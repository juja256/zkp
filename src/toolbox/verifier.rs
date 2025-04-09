use ark_ec::AffineRepr;
use ark_ec::CurveGroup;
use ark_ec::VariableBaseMSM;
use ark_ff::Zero;
use rand::{thread_rng, Rng};
use std::borrow::BorrowMut;
use std::iter;
use std::marker::PhantomData;

use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use curve25519_dalek::scalar::Scalar;
use curve25519_dalek::traits::{IsIdentity, VartimeMultiscalarMul};

use crate::toolbox::{SchnorrCS, standard_transcript::TranscriptProtocol};
use crate::{BatchableProof, CompactProof, ProofError, Transcript};

use super::PointVar;
use super::ScalarVar;

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
pub struct Verifier<G: AffineRepr, U: TranscriptProtocol<G>, T: BorrowMut<U>> {
    phantom_u: PhantomData<U>,

    transcript: T,
    num_scalars: usize,
    points: Vec<G>,
    point_labels: Vec<&'static [u8]>,
    constraints: Vec<(PointVar, Vec<(ScalarVar, PointVar)>)>,
}

impl<G: AffineRepr, U: TranscriptProtocol<G>, T: BorrowMut<U>> Verifier<G, U, T> {
    /// Construct a verifier for the proof statement with the given
    /// `proof_label`, operating on the given `transcript`.
    pub fn new(proof_label: &'static [u8], mut transcript: T) -> Self {
        //<Transcript as TranscriptProtocol<G>>::domain_sep(transcript.borrow_mut(), proof_label);
        transcript.borrow_mut().domain_sep(proof_label);
        Verifier {
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
        assignment: G,
    ) -> Result<PointVar, ProofError> {
        self.transcript.borrow_mut().validate_and_append_point_var(label, &assignment)?;
        self.points.push(assignment);
        self.point_labels.push(label);
        Ok(PointVar(self.points.len() - 1))
    }

    /// Consume the verifier to produce a verification of a [`CompactProof`].
    pub fn verify_compact(mut self, proof: &CompactProof<G::ScalarField>) -> Result<(), ProofError> {
        // Check that there are as many responses as secret variables
        if proof.responses.len() != self.num_scalars {
            return Err(ProofError::VerificationFailure);
        }

        // Decompress all parameters or fail verification.
        let points = self.points;

        // Recompute the prover's commitments based on their claimed challenge value:
        let minus_c = -proof.challenge;
        for (lhs_var, rhs_lc) in &self.constraints {
            let commitment = G::Group::msm(
                rhs_lc
                    .iter()
                    .map(|(_sc_var, pt_var)| points[pt_var.0])
                    .chain(iter::once(points[lhs_var.0])).collect::<Vec<G>>().as_slice(),
                rhs_lc
                    .iter()
                    .map(|(sc_var, _pt_var)| proof.responses[sc_var.0])
                    .chain(iter::once(minus_c)).collect::<Vec<G::ScalarField>>().as_slice(),
                ).unwrap()
                .into_affine();

            self.transcript.borrow_mut().append_blinding_commitment(self.point_labels[lhs_var.0], &commitment);
        }

        // Recompute the challenge and check if it's the claimed one
        let challenge = self.transcript.borrow_mut().get_challenge(b"chal");

        if challenge == proof.challenge {
            Ok(())
        } else {
            Err(ProofError::VerificationFailure)
        }
    }

    /// Consume the verifier to produce a verification of a [`BatchableProof`].
    pub fn verify_batchable(mut self, proof: &BatchableProof<G>) -> Result<(), ProofError> {
        // Check that there are as many responses as secret variables
        if proof.responses.len() != self.num_scalars {
            return Err(ProofError::VerificationFailure);
        }
        // Check that there are as many commitments as constraints
        if proof.commitments.len() != self.constraints.len() {
            return Err(ProofError::VerificationFailure);
        }

        // Feed the prover's commitments into the transcript:
        for (i, commitment) in proof.commitments.iter().enumerate() {
            let (ref lhs_var, ref _rhs_lc) = self.constraints[i];
            self.transcript.borrow_mut().validate_and_append_blinding_commitment(
                self.point_labels[lhs_var.0],
                &commitment,
            )?;
        }

        let minus_c = -self.transcript.borrow_mut().get_challenge(b"chal");

        let commitments_offset = self.points.len();
        let combined_points = self.points.iter().chain(proof.commitments.iter()).map(|&p| p).collect::<Vec<G>>();

        let mut coeffs = vec![G::ScalarField::zero(); self.points.len() + proof.commitments.len()];
        // For each constraint of the form Q = sum(P_i, x_i),
        // we want to ensure Q_com = sum(P_i, resp_i) - c * Q,
        // so add the check rand*( sum(P_i, resp_i) - c * Q - Q_com ) == 0
        for i in 0..self.constraints.len() {
            let (ref lhs_var, ref rhs_lc) = self.constraints[i];
            let random_factor = G::ScalarField::from(thread_rng().gen::<u128>());

            coeffs[commitments_offset + i] += -random_factor;
            coeffs[lhs_var.0] += random_factor * minus_c;
            for (sc_var, pt_var) in rhs_lc {
                coeffs[pt_var.0] += random_factor * proof.responses[sc_var.0];
            }
        }
        
        let check = G::Group::msm(
            combined_points.as_slice(),
            coeffs.as_slice()
        )
        .map_err(|_| ProofError::VerificationFailure)?;

        if check.is_zero() {
            Ok(())
        } else {
            Err(ProofError::VerificationFailure)
        }
    }
}

impl<'a, G: AffineRepr, U: TranscriptProtocol<G>, T: BorrowMut<U>> SchnorrCS for Verifier<G, U, T> {
    type ScalarVar = ScalarVar;
    type PointVar = PointVar;

    fn constrain(&mut self, lhs: PointVar, linear_combination: Vec<(ScalarVar, PointVar)>) -> usize {
        self.constraints.push((lhs, linear_combination));
        self.constraints.len() - 1
    }

    #[cfg(feature = "rangeproof")]
    fn require_range_proof(&mut self, constraint: usize) {}
}
