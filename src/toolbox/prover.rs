
use std::borrow::BorrowMut;
use std::marker::PhantomData;

use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{BigInteger, PrimeField, UniformRand};
use ark_ec::VariableBaseMSM;
use rand::{thread_rng, Rng};
use merlin::{TranscriptRng, TranscriptRngBuilder};

use crate::toolbox::{SchnorrCS, standard_transcript::TranscriptProtocol};
use crate::{BatchableProof, CompactProof, Transcript};

use super::{PointVar, ScalarVar};

/// Used to create proofs.
///
/// To use a [`Prover`], first construct one using [`Prover::new()`],
/// supplying a domain separation label, as well as the transcript to
/// operate on.
///
/// Then, allocate and assign secret ([`Prover::allocate_scalar`]) and
/// public ([`Prover::allocate_point`]) variables, and use those
/// variables to define the proof statements.
///
/// Finally, use [`Prover::prove_compact`] or
/// [`Prover::prove_batchable`] to consume the prover and produce a
/// proof.
pub struct Prover<G: AffineRepr, U: TranscriptProtocol<G>, T: BorrowMut<U>> {
    phantom_u: PhantomData<U>,
    transcript: T,
    scalars: Vec<G::ScalarField>,
    points: Vec<G>,
    point_labels: Vec<&'static [u8]>,
    constraints: Vec<(PointVar, Vec<(ScalarVar, PointVar)>)>,
}

impl<G: AffineRepr, U: TranscriptProtocol<G>, T: BorrowMut<U>> Prover<G, U, T> {
    /// Construct a new prover.  The `proof_label` disambiguates proof
    /// statements.
    pub fn new(proof_label: &'static [u8], mut transcript: T) -> Self {
        transcript.borrow_mut().domain_sep(proof_label);
        Prover {
            phantom_u: PhantomData,
            transcript,
            scalars: Vec::default(),
            points: Vec::default(),
            point_labels: Vec::default(),
            constraints: Vec::default(),
        }
    }

    /// Allocate and assign a secret variable with the given `label`.
    pub fn allocate_scalar(&mut self, label: &'static [u8], assignment: G::ScalarField) -> ScalarVar {
        self.transcript.borrow_mut().append_scalar_var(label);
        self.scalars.push(assignment);
        ScalarVar(self.scalars.len() - 1)
    }

    /// Allocate and assign a public variable with the given `label`.
    ///
    /// The point is compressed to be appended to the transcript, and
    /// the compressed point is returned to allow reusing the result
    /// of that computation; it can be safely discarded.
    pub fn allocate_point(
        &mut self,
        label: &'static [u8],
        assignment: G,
    ) -> (PointVar, G) {
        self.transcript.borrow_mut().append_point_var(label, &assignment);
        self.points.push(assignment);
        self.point_labels.push(label);
        (PointVar(self.points.len() - 1), assignment)
    }

    /// The compact and batchable proofs differ only by which data they store.
    fn prove_impl(mut self) -> (G::ScalarField, Vec<G::ScalarField>, Vec<G>) {
        // Construct a TranscriptRng
        let mut rng_builder = self.transcript.borrow_mut().build_rng();
        for scalar in &self.scalars {
            rng_builder = rng_builder.rekey_with_witness_bytes(b"", scalar.into_bigint().to_bytes_le().as_slice() );
        }
        let mut transcript_rng = rng_builder.finalize(&mut thread_rng());

        // Generate a blinding factor for each secret variable
        let blindings = self
            .scalars
            .iter()
            .map(|_| G::ScalarField::rand(&mut transcript_rng))
            .collect::<Vec<G::ScalarField>>();

        // Commit to each blinded LHS
        let mut commitments = Vec::with_capacity(self.constraints.len());
        for (lhs_var, rhs_lc) in &self.constraints {
            let commitment = G::Group::msm(
                rhs_lc.iter().map(|(_sc_var, pt_var)| self.points[pt_var.0]).collect::<Vec<G>>().as_slice(),
                rhs_lc.iter().map(|(sc_var, _pt_var)| blindings[sc_var.0]).collect::<Vec<G::ScalarField>>().as_slice(),
            ).unwrap().into_affine();

            self.transcript.borrow_mut().append_blinding_commitment(self.point_labels[lhs_var.0], &commitment);
            commitments.push(commitment);
        }

        // Obtain a scalar challenge and compute responses
        let challenge = self.transcript.borrow_mut().get_challenge(b"chal");
        let responses = Iterator::zip(self.scalars.iter(), blindings.iter())
            .map(|(s, b)| *s * challenge + b)
            .collect::<Vec<G::ScalarField>>();

        (challenge, responses, commitments)
    }

    /// Consume this prover to produce a compact proof.
    pub fn prove_compact(self) -> CompactProof<G::ScalarField> {
        let (challenge, responses, _) = self.prove_impl();

        CompactProof {
            challenge,
            responses,
        }
    }

    /// Consume this prover to produce a batchable proof.
    pub fn prove_batchable(self) -> BatchableProof<G> {
        let (_, responses, commitments) = self.prove_impl();

        BatchableProof {
            commitments,
            responses,
        }
    }
}

impl<G: AffineRepr, U: TranscriptProtocol<G>, T: BorrowMut<U>> SchnorrCS for Prover<G, U, T> {
    type ScalarVar = ScalarVar;
    type PointVar = PointVar;

    fn constrain(&mut self, lhs: PointVar, linear_combination: Vec<(ScalarVar, PointVar)>) -> usize {
        self.constraints.push((lhs, linear_combination));
        self.constraints.len() - 1
    }

    #[cfg(feature = "rangeproof")]
    fn require_range_proof(&mut self, constraint: usize) {}
}
