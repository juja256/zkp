
use std::borrow::BorrowMut;
use std::marker::PhantomData;

use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{BigInt, BigInteger, PrimeField, UniformRand};
use ark_ec::VariableBaseMSM;
use ark_serialize::{CanonicalSerialize, CanonicalDeserialize};
use rand::{thread_rng, Rng};
use merlin::{TranscriptRng, TranscriptRngBuilder};

use crate::toolbox::{SchnorrCS, cross_transcript::TranscriptProtocol};
use crate::{BatchableProof, CompactProof, ProofError, Transcript};

use super::{Challenge, Point, PointVar, Scalar, ScalarVar};

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct CompactCrossProof<F1: PrimeField, F2: PrimeField>  
    where F1::BigInt: Into<BigInt<4>>, 
          F2::BigInt: Into<BigInt<4>> {
    /// The Fiat-Shamir challenge.
    pub challenge: Challenge,
    /// The prover's responses, one per secret variable.
    pub responses: Vec<Scalar<F1, F2>>,
}

pub struct CrossProver<G1: AffineRepr, G2: AffineRepr, U: TranscriptProtocol<G1, G2>, T: BorrowMut<U>, const B_x: usize, const B_c: usize, const B_f: usize> 
    where BigInt<4>: From<<G1::ScalarField as PrimeField>::BigInt>, 
          BigInt<4>: From<<G2::ScalarField as PrimeField>::BigInt>,
          <G1::ScalarField as PrimeField>::BigInt: From<BigInt<4>>,
          <G2::ScalarField as PrimeField>::BigInt: From<BigInt<4>> {
    phantom_u: PhantomData<U>,
    transcript: T,

    scalars: Vec<Scalar<G1::ScalarField, G2::ScalarField >>,
    points: Vec<Point<G1, G2>>,

    point_labels: Vec<&'static [u8]>,
    constraints: Vec<(PointVar, Vec<(ScalarVar, PointVar)>)>,
}


impl<G1: AffineRepr, G2: AffineRepr, U: TranscriptProtocol<G1, G2>, T: BorrowMut<U>, const B_x: usize, const B_c: usize, const B_f: usize> 
    CrossProver<G1, G2, U, T, B_x, B_c, B_f> 
    where BigInt<4>: From<<G1::ScalarField as PrimeField>::BigInt>, 
          BigInt<4>: From<<G2::ScalarField as PrimeField>::BigInt>,
          <G1::ScalarField as PrimeField>::BigInt: From<BigInt<4>>,
          <G2::ScalarField as PrimeField>::BigInt: From<BigInt<4>> {
    /// Construct a new prover.  The `proof_label` disambiguates proof
    /// statements.
    pub fn new(proof_label: &'static [u8], mut transcript: T) -> Self {
        // G1 is smaller than G2
        assert!(<G1::ScalarField as PrimeField>::MODULUS_BIT_SIZE < <G2::ScalarField as PrimeField>::MODULUS_BIT_SIZE);
        // B_x + B_c + B_f is smaller than G1::ScalarField::MODULUS_BIT_SIZE
        assert!(B_x + B_c + B_f < <G1::ScalarField as PrimeField>::MODULUS_BIT_SIZE as usize);

        transcript.borrow_mut().domain_sep(proof_label);
        CrossProver {
            phantom_u: PhantomData,
            transcript,
            scalars: Vec::default(),
            points: Vec::default(),
            point_labels: Vec::default(),
            constraints: Vec::default(),
        }
    }

    /// Allocate and assign a secret variable with the given `label`.
    pub fn allocate_scalar(&mut self, label: &'static [u8], assignment: Scalar<G1::ScalarField, G2::ScalarField>) -> Result<ScalarVar, ProofError> {
        if let Scalar::Cross(assignment) = assignment {
            if assignment.num_bits() > B_x as u32 {
                return Err(ProofError::ScalarVarExceedsBound);
            }
        }
        self.transcript.borrow_mut().append_scalar_var(label);
        self.scalars.push(assignment);
        Ok(ScalarVar(self.scalars.len() - 1))
    }

    /// Allocate and assign a public variable with the given `label`.
    ///
    /// The point is compressed to be appended to the transcript, and
    /// the compressed point is returned to allow reusing the result
    /// of that computation; it can be safely discarded.
    pub fn allocate_point(
        &mut self,
        label: &'static [u8],
        assignment: Point<G1, G2>,
    ) -> PointVar {
        self.transcript.borrow_mut().append_point_var(label, &assignment);
        self.points.push(assignment);
        self.point_labels.push(label);
        PointVar(self.points.len() - 1)
    }

    /// The compact and batchable proofs differ only by which data they store.
    fn prove_impl(mut self) -> Result<(Challenge, Vec<Scalar<G1::ScalarField, G2::ScalarField>>, Vec<Point<G1, G2>>), ProofError> {
        // Construct a TranscriptRng
        let mut rng_builder = self.transcript.borrow_mut().build_rng();
        for scalar in &self.scalars {
            rng_builder = rng_builder.rekey_with_witness_bytes(b"", scalar.into_bigint().to_bytes_le().as_slice());
        }
        let mut transcript_rng = rng_builder.finalize(&mut thread_rng());

        // Generate a blinding factor for each secret variable
        let blindings = self
            .scalars
            .iter()
            .map(|s| match s {
                Scalar::F1(scalar) => Scalar::F1(G1::ScalarField::rand(&mut transcript_rng)),
                Scalar::F2(scalar) => Scalar::F2(G2::ScalarField::rand(&mut transcript_rng)),
                Scalar::Cross(scalar) => Scalar::Cross(
                    BigInt::<4>::rand(&mut transcript_rng) >> ((<G1::ScalarField as PrimeField>::MODULUS_BIT_SIZE as u32) - (B_x + B_c + B_f) as u32) // clear the high bits
                ),
            })
            .collect::<Vec<Scalar<G1::ScalarField, G2::ScalarField>>>();

        // Commit to each blinded LHS
        let mut commitments = Vec::with_capacity(self.constraints.len());
        for (lhs_var, rhs_lc) in &self.constraints {
            let commitment = match self.points[lhs_var.0] {
                Point::G1(_) => {
                    Point::G1(
                        G1::Group::msm(
                        rhs_lc.iter().map(|(_sc_var, pt_var)| 
                                match self.points[pt_var.0] {
                                    Point::G1(pt) => Ok(pt),
                                    Point::G2(_) => Err(ProofError::PointVarMismatch),
                                }
                            ).collect::<Result<Vec<_>, ProofError>>()?.as_slice(),
                        rhs_lc.iter().map(|(sc_var, _pt_var)| 
                                match blindings[sc_var.0] {
                                    Scalar::F1(scalar) => Ok(scalar),
                                    Scalar::F2(scalar) => Err(ProofError::PointVarMismatch),
                                    Scalar::Cross(scalar) => Ok(G1::ScalarField::from_bigint(scalar.into()).unwrap()),
                                }
                            ).collect::<Result<Vec<_>, ProofError>>()?.as_slice(),
                        ).map_err(|_| ProofError::PointVarMismatch)?.into_affine()
                    )
                },
                Point::G2(_) => {
                    Point::G2(
                        G2::Group::msm(
                        rhs_lc.iter().map(|(_sc_var, pt_var)| 
                                match self.points[pt_var.0] {
                                    Point::G2(pt) => Ok(pt),
                                    Point::G1(_) => Err(ProofError::PointVarMismatch),
                                }
                            ).collect::<Result<Vec<_>, ProofError>>()?.as_slice(),
                        rhs_lc.iter().map(|(sc_var, _pt_var)| 
                                match blindings[sc_var.0] {
                                    Scalar::F2(scalar) => Ok(scalar),
                                    Scalar::F1(_) => Err(ProofError::PointVarMismatch),
                                    Scalar::Cross(scalar) => Ok(G2::ScalarField::from_bigint(scalar.into()).unwrap()),
                                }
                            ).collect::<Result<Vec<_>, ProofError>>()?.as_slice(),
                        ).map_err(|_| ProofError::PointVarMismatch)?.into_affine()
                    )
                },
            };


            self.transcript.borrow_mut().append_blinding_commitment(self.point_labels[lhs_var.0], &commitment);
            commitments.push(commitment);
        }

        // Obtain a scalar challenge and compute responses
        let challenge = self.transcript.borrow_mut().get_challenge(b"p-chel", B_c/8);

        let responses = Iterator::zip(self.scalars.iter(), blindings.iter())
            .map(|(s, b)| match s {
                Scalar::F1(scalar) => if let Scalar::F1(blinding) = b {
                        Ok(Scalar::F1(*scalar * G1::ScalarField::from_bigint(challenge.into()).unwrap() + *blinding))
                    } else {
                        Err(ProofError::PointVarMismatch)
                    },
                Scalar::F2(scalar) => if let Scalar::F2(blinding) = b {
                        Ok(Scalar::F2(*scalar * G2::ScalarField::from_bigint(challenge.into()).unwrap() + *blinding))
                    } else {
                        Err(ProofError::PointVarMismatch)
                    },
                Scalar::Cross(scalar) => {
                    let (s0, s1) = scalar.mul(&challenge);
                    if !s1.is_zero() {
                        Err(ProofError::ScalarVarExceedsBound)
                    } else if BigInt::<4>::from(s0) > BigInt::<4>::from(G1::ScalarField::MODULUS) {
                        Err(ProofError::ProverAborted)
                    } else {
                        Ok(Scalar::Cross(s0))
                    }
                }
                
            })
            .collect::<Result<Vec<_>, ProofError>>()?;

        Ok((challenge, responses, commitments))
    }

    /// Consume this prover to produce a compact proof.
    pub fn prove_compact(self) -> Result<CompactCrossProof<G1::ScalarField, G2::ScalarField>, ProofError> {
        let (challenge, responses, _) = self.prove_impl()?;

        Ok(CompactCrossProof {
            challenge,
            responses,
        })
    }
}

impl<G1: AffineRepr, G2: AffineRepr, U: TranscriptProtocol<G1, G2>, T: BorrowMut<U>, const B_x: usize, const B_c: usize, const B_f: usize> SchnorrCS for CrossProver<G1, G2, U, T, B_x, B_c, B_f>
    where BigInt<4>: From<<G1::ScalarField as PrimeField>::BigInt>, 
          BigInt<4>: From<<G2::ScalarField as PrimeField>::BigInt>,
          <G1::ScalarField as PrimeField>::BigInt: From<BigInt<4>>,
          <G2::ScalarField as PrimeField>::BigInt: From<BigInt<4>> {
    type ScalarVar = ScalarVar;
    type PointVar = PointVar;

    fn constrain(&mut self, lhs: Self::PointVar, linear_combination: Vec<(Self::ScalarVar, Self::PointVar)>) {
        self.constraints.push((lhs, linear_combination));
    }
}
