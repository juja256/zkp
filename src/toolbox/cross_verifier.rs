use ark_ec::AffineRepr;
use ark_ec::CurveGroup;
use ark_ec::VariableBaseMSM;
use ark_ed25519::EdwardsAffine;
use ark_ff::BigInt;
use ark_ff::PrimeField;
use ark_ff::Zero;
use bulletproofs::BulletproofGens;
use bulletproofs::PedersenGens;
use rand::{thread_rng, Rng};
use std::borrow::BorrowMut;
use std::iter;
use std::marker::PhantomData;

use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::traits::{IsIdentity, VartimeMultiscalarMul};

use crate::toolbox::{SchnorrCS, cross_transcript::TranscriptProtocol};
use crate::CompactCrossProof;
use crate::RangeProof;
use crate::{BatchableProof, CompactProof, ProofError, Transcript};

use super::dalek_ark::ark_to_ristretto255;
use super::Point;
use super::PointVar;
use super::Scalar;
use super::ScalarVar;

macro_rules! cast {
    ($value:expr, $pattern:path) => {
        match $value {
            $pattern(inner) => inner,
            _ => panic!("Failed to cast value to {}", stringify!($pattern)),
        }
    };
}

/// Used to produce verification results.
///
/// To use a [`Verifier`], first construct one using [`Verifier::new()`],
/// supplying a domain separation label, as well as the transcript to
/// operate on.
///
/// Then, allocate secret ([`Verifier::allocate_scalar`]) variables
/// and allocate and assign public ([`Verifier::allocate_point`])
/// variables, and use those variables to define the proof statements.
/// Note that no assignments to secret variables are assigned, since
/// the verifier doesn't know the secrets.
///
/// Finally, use [`Verifier::verify_compact`] or
/// [`Verifier::verify_batchable`] to consume the verifier and produce
/// a verification result.
pub struct CrossVerifier<G1: AffineRepr, G2: AffineRepr, U: TranscriptProtocol<G1, G2>, T: BorrowMut<U>, const B_x: usize, const B_c: usize, const B_f: usize> 
    where BigInt<4>: From<<G1::ScalarField as PrimeField>::BigInt>, 
          BigInt<4>: From<<G2::ScalarField as PrimeField>::BigInt>,
          <G1::ScalarField as PrimeField>::BigInt: From<BigInt<4>>,
          <G2::ScalarField as PrimeField>::BigInt: From<BigInt<4>> {
    phantom_u: PhantomData<U>,

    transcript: T,
    num_scalars: usize,
    points: Vec<Point<G1, G2>>,
    point_labels: Vec<&'static [u8]>,
    constraints: Vec<(PointVar, Vec<(ScalarVar, PointVar)>, Option<()>)>,

}

impl<G1: AffineRepr, G2: AffineRepr, U: TranscriptProtocol<G1, G2>, T: BorrowMut<U>, const B_x: usize, const B_c: usize, const B_f: usize> CrossVerifier<G1, G2, U, T, B_x, B_c, B_f>
    where BigInt<4>: From<<G1::ScalarField as PrimeField>::BigInt>, 
            BigInt<4>: From<<G2::ScalarField as PrimeField>::BigInt>,
            <G1::ScalarField as PrimeField>::BigInt: From<BigInt<4>>,
            <G2::ScalarField as PrimeField>::BigInt: From<BigInt<4>> {
    /// Construct a verifier for the proof statement with the given
    /// `proof_label`, operating on the given `transcript`.
    pub fn new(proof_label: &'static [u8], mut transcript: T) -> Self {
        transcript.borrow_mut().domain_sep(proof_label);
        CrossVerifier {
            transcript,
            num_scalars: 0,
            points: Vec::default(),
            point_labels: Vec::default(),
            constraints: Vec::default(),
            phantom_u: PhantomData,
        }
    }

    /// Allocate a placeholder scalar variable, without an assignment.
    pub fn allocate_scalar(&mut self, label: &'static [u8]) -> ScalarVar {
        self.transcript.borrow_mut().append_scalar_var(label);
        self.num_scalars += 1;
        ScalarVar(self.num_scalars - 1)
    }

    /// Attempt to allocate a point variable, or fail verification if
    /// the assignment is invalid.
    pub fn allocate_point(
        &mut self,
        label: &'static [u8],
        assignment: Point<G1, G2>,
    ) -> Result<PointVar, ProofError> {
        self.transcript.borrow_mut().validate_and_append_point_var(label, &assignment)?;
        self.points.push(assignment);
        self.point_labels.push(label);
        Ok(PointVar(self.points.len() - 1))
    }

    /// Consume the verifier to produce a verification of a [`CompactProof`].
    pub fn verify_compact(mut self, proof: &CompactCrossProof<G1::ScalarField, G2::ScalarField>) -> Result<(), ProofError> {
        // Check that there are as many responses as secret variables
        if proof.responses.len() != self.num_scalars {
            return Err(ProofError::VerificationFailure);
        }

        // Recompute the prover's commitments based on their claimed challenge value:
        for (lhs_var, rhs_lc, _) in &self.constraints {
            let commitment = match self.points[lhs_var.0] {
                Point::G1(_) => {
                    Point::G1(G1::Group::msm(
                        rhs_lc
                            .iter()
                            .map(|(_sc_var, pt_var)| self.points[pt_var.0])
                            .chain(iter::once(self.points[lhs_var.0]))
                            .filter_map(|point| if let Point::G1(g1_point) = point { Some(g1_point) } else { None })
                            .collect::<Vec<G1>>()
                            .as_slice(),
                        rhs_lc
                            .iter()
                            .map(|(sc_var, _pt_var)| match proof.responses[sc_var.0] {
                                Scalar::F1(sc) => Ok(sc),
                                Scalar::F2(sc) => Err(ProofError::VerificationFailure),
                                Scalar::Cross(sc) => Ok(G1::ScalarField::from_bigint(sc.into()).unwrap()),
                            })
                            .chain(iter::once(Ok(-G1::ScalarField::from_bigint(proof.challenge.into()).unwrap())))
                            .collect::<Result<Vec<G1::ScalarField>, ProofError>>()?
                            .as_slice(),
                    ).map_err(|_| ProofError::VerificationFailure)?
                    .into_affine()
                    )
                },
                Point::G2(_) => {
                    Point::G2(G2::Group::msm(
                        rhs_lc
                            .iter()
                            .map(|(_sc_var, pt_var)| self.points[pt_var.0])
                            .chain(iter::once(self.points[lhs_var.0]))
                            .filter_map(|point| if let Point::G2(g1_point) = point { Some(g1_point) } else { None })
                            .collect::<Vec<G2>>()
                            .as_slice(),
                            rhs_lc
                            .iter()
                            .map(|(sc_var, _pt_var)| match proof.responses[sc_var.0] {
                                Scalar::F2(sc) => Ok(sc),
                                Scalar::F1(sc) => Err(ProofError::VerificationFailure),
                                Scalar::Cross(sc) => Ok(G2::ScalarField::from_bigint(sc.into()).unwrap()),
                            })
                            .chain(iter::once(Ok(-G2::ScalarField::from_bigint(proof.challenge.into()).unwrap())))
                            .collect::<Result<Vec<G2::ScalarField>, ProofError>>()?
                            .as_slice()
                    ).map_err(|_| ProofError::VerificationFailure)?
                    .into_affine()
                    )
                },
            };

            self.transcript.borrow_mut().append_blinding_commitment(self.point_labels[lhs_var.0], &commitment);
        }

        // Recompute the challenge and check if it's the claimed one
        let challenge = self.transcript.borrow_mut().get_challenge(b"p-chel", B_c/8);

        if challenge == proof.challenge {
            Ok(())
        } else {
            Err(ProofError::VerificationFailure)
        }
    }

}

#[cfg(feature = "rangeproof")]
impl<G1: AffineRepr, U: TranscriptProtocol<G1, EdwardsAffine>, T: BorrowMut<U>, const B_x: usize, const B_c: usize, const B_f: usize> 
    CrossVerifier<G1, EdwardsAffine, U, T, B_x, B_c, B_f> 
    where BigInt<4>: From<<G1::ScalarField as PrimeField>::BigInt>,
          <G1::ScalarField as PrimeField>::BigInt: From<BigInt<4>> {
    pub fn verify_range_proofs(&mut self, range_proofs: &[RangeProof]) -> Result<(), ProofError> {
        let mut range_proof_iter = range_proofs.iter();
        self.constraints.to_owned().iter().filter_map(|(lhs, rhs_lc, rp)| match rp {
            Some(_) => {
                let (G, H) = (cast!(self.points[rhs_lc[0].1.0], Point::G2), cast!(self.points[rhs_lc[1].1.0], Point::G2));
                let Com = ark_to_ristretto255(cast!(self.points[lhs.0], Point::G2)).unwrap();
                match range_proof_iter.next() {
                    Some(rp) => Some(
                        rp.0.verify_single(
                        &BulletproofGens::new(B_x, 1), 
                        &PedersenGens { B: ark_to_ristretto255(G).unwrap(), B_blinding: ark_to_ristretto255(H).unwrap() },
                        self.transcript.borrow_mut().as_transcript(), 
                        &Com.compress(), 
                        B_x)
                        .map_err(|_| ProofError::VerificationFailure)
                    ),
                    None => Some(Err(ProofError::VerificationFailure))
                }
            },
            None => None,
        }).collect::<Result<(), ProofError>>()
    }

    pub fn verify_cross(mut self, proof: &CompactCrossProof<G1::ScalarField, <EdwardsAffine as AffineRepr>::ScalarField>) -> Result<(), ProofError> {
        self.verify_range_proofs(proof.range_proofs.as_slice())?;
        self.verify_compact(proof)
    }
}

impl<'a, G1: AffineRepr, G2: AffineRepr, U: TranscriptProtocol<G1, G2>, T: BorrowMut<U>, const B_x: usize, const B_c: usize, const B_f: usize> SchnorrCS 
    for CrossVerifier<G1, G2, U, T, B_x, B_c, B_f>
    where BigInt<4>: From<<G1::ScalarField as PrimeField>::BigInt>, 
        BigInt<4>: From<<G2::ScalarField as PrimeField>::BigInt>,
        <G1::ScalarField as PrimeField>::BigInt: From<BigInt<4>>,
        <G2::ScalarField as PrimeField>::BigInt: From<BigInt<4>> {
    type ScalarVar = ScalarVar;
    type PointVar = PointVar;

    fn constrain(&mut self, lhs: PointVar, linear_combination: Vec<(ScalarVar, PointVar)>) -> usize {
        self.constraints.push((lhs, linear_combination, None));
        self.constraints.len() - 1
    }

    #[cfg(feature = "rangeproof")]
    fn require_range_proof(&mut self, constraint: usize) {
        assert!(matches!(self.points[self.constraints[constraint].0.0], Point::G2(_)), "Expected Point::G2, but found a different variant");
        assert!(self.constraints[constraint].1.len() == 2, "Expected 2 linear combinations, but found a different number");
        self.constraints[constraint].2 = Some(());
    }
}