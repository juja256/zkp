
use std::borrow::BorrowMut;
use std::cmp::min;
use std::convert::TryInto;
use std::marker::PhantomData;
use std::sync::atomic::AtomicUsize;

use ark_ec::{AffineRepr, CurveGroup};

macro_rules! cast {
    ($value:expr, $pattern:path) => {
        match $value {
            $pattern(inner) => inner,
            _ => panic!("Failed to cast value to {}", stringify!($pattern)),
        }
    };
}
use ark_ed25519::EdwardsAffine;
use ark_ff::{BigInt, BigInteger, PrimeField, UniformRand};
use ark_ec::VariableBaseMSM;
use ark_serialize::{CanonicalSerialize, CanonicalDeserialize};
use bulletproofs::{BulletproofGens, PedersenGens};
use rand::{thread_rng, Rng};
use merlin::{TranscriptRng, TranscriptRngBuilder};

use crate::toolbox::{SchnorrCS, cross_transcript::TranscriptProtocol};
use crate::{BatchableProof, CompactCrossProof, CompactProof, ProofError, RangeProof, Transcript};

use super::dalek_ark::ark_to_ristretto255;
use super::{Challenge, Point, PointVar, Scalar, ScalarVar};

pub struct CrossProver<G1: AffineRepr, G2: AffineRepr, U: TranscriptProtocol<G1, G2>, T: BorrowMut<U>, const B_x: usize, const B_c: usize, const B_f: usize> 
    where BigInt<4>: From<<G1::ScalarField as PrimeField>::BigInt>, 
          BigInt<4>: From<<G2::ScalarField as PrimeField>::BigInt>,
          <G1::ScalarField as PrimeField>::BigInt: From<BigInt<4>>,
          <G2::ScalarField as PrimeField>::BigInt: From<BigInt<4>> {
    g: BigInt<4>,
    g_bits: u32,
    phantom_u: PhantomData<U>,
    transcript: T,

    scalars: Vec<Scalar<G1::ScalarField, G2::ScalarField>>,
    points: Vec<Point<G1, G2>>,

    point_labels: Vec<&'static [u8]>,
    constraints: Vec<(PointVar, Vec<(ScalarVar, PointVar)>, Option<()>)>,
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
        let g_bits = min(<G1::ScalarField as PrimeField>::MODULUS_BIT_SIZE, <G2::ScalarField as PrimeField>::MODULUS_BIT_SIZE);
        let g = min(BigInt::<4>::from(G1::ScalarField::MODULUS), BigInt::<4>::from(G2::ScalarField::MODULUS));
        assert!(B_x + B_c + B_f < g_bits as usize);

        transcript.borrow_mut().domain_sep(proof_label);
        CrossProver {
            g,
            g_bits,
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
                    BigInt::<4>::rand(&mut transcript_rng) >> (self.g_bits - (B_x + B_c + B_f) as u32) // clear the high bits
                ),
            })
            .collect::<Vec<Scalar<G1::ScalarField, G2::ScalarField>>>();

        // Commit to each blinded LHS
        let mut commitments = Vec::with_capacity(self.constraints.len());
        for (lhs_var, rhs_lc, _) in &self.constraints {
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
                    if let Scalar::Cross(blinding) = b {
                        let (mut s0, s1) = scalar.mul(&challenge);
                        if !s1.is_zero() {
                            return Err(ProofError::ScalarVarExceedsBound)
                        } 
                        let carry = s0.add_with_carry(blinding);
                        if carry || (BigInt::<4>::from(s0) > self.g) {
                            Err(ProofError::ProverAborted)
                        } else {
                            Ok(Scalar::Cross(s0))
                        }
                    } else {
                        Err(ProofError::PointVarMismatch)
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
            #[cfg(feature = "rangeproof")]
            range_proofs: vec![],
        })
    }
}

#[cfg(feature = "rangeproof")]
impl<G1: AffineRepr, U: TranscriptProtocol<G1, EdwardsAffine>, T: BorrowMut<U>, const B_x: usize, const B_c: usize, const B_f: usize> 
    CrossProver<G1, EdwardsAffine, U, T, B_x, B_c, B_f> 
    where BigInt<4>: From<<G1::ScalarField as PrimeField>::BigInt>,
          <G1::ScalarField as PrimeField>::BigInt: From<BigInt<4>> {
    
    pub fn get_range_proofs(&mut self) -> Result<Vec<RangeProof>, ProofError> {
        #[cfg(feature = "rangeproof_batchable")]
        {
            let v = self.constraints.to_owned().iter()
                .filter_map(|(_lhc, rhs_lc, range_proof)| match range_proof {
                    Some(_) => {
                        let (G, H) = (cast!(self.points[rhs_lc[0].1.0], Point::G2), cast!(self.points[rhs_lc[1].1.0], Point::G2));
                        let (v, v_blinding) = (cast!(self.scalars[rhs_lc[0].0.0], Scalar::Cross), cast!(self.scalars[rhs_lc[1].0.0], Scalar::F2));
                        Some((G, H, v.0[0], curve25519_dalek::Scalar::from_bytes_mod_order(v_blinding.into_bigint().to_bytes_le()[..].try_into().unwrap())))
                    },
                    None => None,
                }).collect::<Vec<_>>();
            bulletproofs::RangeProof::prove_multiple(
                &BulletproofGens::new(B_x, 16), 
                &PedersenGens { B: ark_to_ristretto255(v[0].0).unwrap(), B_blinding: ark_to_ristretto255(v[0].1).unwrap() },
                self.transcript.borrow_mut().as_transcript(), 
                v.iter().map(|&(_,_,v,_)| v).collect::<Vec<_>>().as_slice(), 
                v.iter().map(|&(_,_,_,v_blinding)| v_blinding).collect::<Vec<_>>().as_slice(),
                B_x
            )
            .map(|(r,_)| vec![RangeProof(r)])
            .map_err(|e| ProofError::RangeProofError(e))
        }
        #[cfg(not(feature = "rangeproof_batchable"))]
        Ok(
            self.constraints.to_owned().iter()
            .filter_map(|(_lhc, rhs_lc, range_proof)| match range_proof {
                Some(_) => {
                    let (G, H) = (cast!(self.points[rhs_lc[0].1.0], Point::G2), cast!(self.points[rhs_lc[1].1.0], Point::G2));
                    let (v, v_blinding) = (cast!(self.scalars[rhs_lc[0].0.0], Scalar::Cross), cast!(self.scalars[rhs_lc[1].0.0], Scalar::F2));
                    Some(bulletproofs::RangeProof::prove_single(
                        &BulletproofGens::new(B_x, 1),
                        &PedersenGens { B: ark_to_ristretto255(G).unwrap(), B_blinding: ark_to_ristretto255(H).unwrap() },
                        self.transcript.borrow_mut().as_transcript(),
                        v.0[0],
                        &curve25519_dalek::Scalar::from_bytes_mod_order(v_blinding.into_bigint().to_bytes_le()[..].try_into().unwrap()),
                        B_x,
                        ).map(|(r,c)| RangeProof(r))
                        .map_err(|e| ProofError::RangeProofError(e))
                    )
                },
                None => None,
            })
            .collect::<Result<Vec<_>, ProofError>>()?
        )
    }

    /// proving equality of two Pedersen commitments to small x in different groups using bulletproofs and https://eprint.iacr.org/2022/1593.pdf
    pub fn prove_cross(mut self) -> Result<CompactCrossProof<G1::ScalarField, <EdwardsAffine as AffineRepr>::ScalarField>, ProofError> {
        let range_proofs = self.get_range_proofs()?;
        let (challenge, responses, _) = self.prove_impl()?;

        Ok(CompactCrossProof {
            challenge,
            responses,
            range_proofs,
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

    fn constrain(&mut self, lhs: Self::PointVar, linear_combination: Vec<(Self::ScalarVar, Self::PointVar)>) -> usize {
        self.constraints.push((lhs, linear_combination, None));
        self.constraints.len() - 1
    }

    #[cfg(feature = "rangeproof")]
    fn require_range_proof(&mut self, constraint: usize) {
        assert!(matches!(self.points[self.constraints[constraint].0.0], Point::G2(_)), "Expected Point::G2, but found a different variant");
        assert!(self.constraints[constraint].1.len() == 2, "Expected 2 linear combinations, but found a different number");
        assert!(matches!(self.scalars[self.constraints[constraint].1[0].0.0], Scalar::Cross(_)), "Expected Scalar::Cross, but found a different variant");
        self.constraints[constraint].2 = Some(());
    }
}