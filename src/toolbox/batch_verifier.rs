use std::borrow::BorrowMut;
use std::marker::PhantomData;

use rand::{thread_rng, Rng};

use ark_ff::Field;
use ark_ff::Zero;
use ark_ec::VariableBaseMSM;
use ark_ec::AffineRepr;

use crate::toolbox::{SchnorrCS, standard_transcript::TranscriptProtocol};
use crate::util::Matrix;
use crate::{BatchableProof, ProofError, Transcript};

/// Used to produce batch verification results.
///
/// To use a [`BatchVerifier`], first construct one using [`BatchVerifier::new()`],
/// declaring a batch size,
/// supplying a domain separation label for the proof statement, as well as a
/// transcript for each proof to verify.
///
/// Allocate secret variables using [`BatchVerifier::allocate_scalar`].
///
/// To allocate points which have the same assignment for all proofs
/// in the batch, use [`BatchVerifier::allocate_static_point`].  This
/// allows the implementation to overlap coefficients among all proofs
/// in the combined verification check.
///
/// To allocate points which have different asssignments for each
/// proof instance, use [`BatchVerifier::allocate_instance_point`].
///
/// Finally, use [`BatchVerifier::verify_batchable`] to consume the
/// verifier and produce a batch verification result.
pub struct BatchVerifier<G: AffineRepr, U: TranscriptProtocol<G>, T: BorrowMut<U>> {
    phantom_u: PhantomData<U>,

    batch_size: usize,
    transcripts: Vec<T>,

    num_scalars: usize,

    static_points: Vec<G>,
    static_point_labels: Vec<&'static [u8]>,

    instance_points: Vec<Vec<G>>,
    instance_point_labels: Vec<&'static [u8]>,

    constraints: Vec<(PointVar, Vec<(ScalarVar, PointVar)>)>,
}

/// A scalar variable used in batch verification.
#[derive(Copy, Clone)]
pub struct ScalarVar(usize);

/// A point variable used in batch verification.
#[derive(Copy, Clone)]
pub enum PointVar {
    /// A variable whose assignment is common to all proofs in the batch.
    Static(usize),
    /// A variable whose assignment is unique for each proof instance.
    Instance(usize),
}

impl<G: AffineRepr, U: TranscriptProtocol<G>, T: BorrowMut<U>> BatchVerifier<G, U, T> {
    /// Construct a new batch verifier for the statement with the
    /// given `proof_label`.
    ///
    /// The `batch_size` is required as an up-front parameter to help
    /// prevent errors with size mismatches.
    ///
    /// Note that this function requires one transcript borrow per
    /// proof.
    pub fn new(
        proof_label: &'static [u8],
        batch_size: usize,
        mut transcripts: Vec<T>,
    ) -> Result<Self, ProofError> {
        if transcripts.len() != batch_size {
            return Err(ProofError::BatchSizeMismatch);
        }
        for i in 0..transcripts.len() {
            transcripts[i].borrow_mut().domain_sep(proof_label);
        }
        Ok(BatchVerifier {
            phantom_u: PhantomData,
            batch_size,
            transcripts,
            num_scalars: 0,
            static_points: Vec::default(),
            static_point_labels: Vec::default(),
            instance_points: Vec::default(),
            instance_point_labels: Vec::default(),
            constraints: Vec::default(),
        })
    }

    /// Allocate a placeholder scalar variable with the given `label`.
    pub fn allocate_scalar(&mut self, label: &'static [u8]) -> ScalarVar {
        for transcript in self.transcripts.iter_mut() {
            transcript.borrow_mut().append_scalar_var(label);
        }
        self.num_scalars += 1;
        ScalarVar(self.num_scalars - 1)
    }

    /// Allocate a point variable whose assignment is common to all proofs in the batch.
    pub fn allocate_static_point(
        &mut self,
        label: &'static [u8],
        assignment: G,
    ) -> Result<PointVar, ProofError> {
        for transcript in self.transcripts.iter_mut() {
            transcript.borrow_mut().validate_and_append_point_var(label, &assignment)?;
        }
        self.static_points.push(assignment);
        self.static_point_labels.push(label);

        Ok(PointVar::Static(self.static_points.len() - 1))
    }

    /// Allocate a point variable with a different assignment for each proof instance.
    pub fn allocate_instance_point(
        &mut self,
        label: &'static [u8],
        assignments: Vec<G>,
    ) -> Result<PointVar, ProofError> {
        if assignments.len() != self.batch_size {
            return Err(ProofError::BatchSizeMismatch);
        }
        // nll
        {
            let it = Iterator::zip(self.transcripts.iter_mut(), assignments.iter());
            for (transcript, assignment) in it {
                transcript.borrow_mut().validate_and_append_point_var(label, &assignment)?;
            }
        }
        self.instance_points.push(assignments);
        self.instance_point_labels.push(label);

        Ok(PointVar::Instance(self.instance_points.len() - 1))
    }

    /// Consume the verifier to produce a verification result.
    pub fn verify_batchable(mut self, proofs: &[BatchableProof<G>]) -> Result<(), ProofError> {
        if proofs.len() != self.batch_size {
            return Err(ProofError::BatchSizeMismatch);
        }

        for proof in proofs {
            if proof.commitments.len() != self.constraints.len() {
                return Err(ProofError::VerificationFailure);
            }
            if proof.responses.len() != self.num_scalars {
                return Err(ProofError::VerificationFailure);
            }
        }

        // Feed each prover's commitments into their respective transcript
        for j in 0..self.batch_size {
            for (i, com) in proofs[j].commitments.iter().enumerate() {
                let label = match self.constraints[i].0 {
                    PointVar::Static(var_idx) => self.static_point_labels[var_idx],
                    PointVar::Instance(var_idx) => self.instance_point_labels[var_idx],
                };
                self.transcripts[j].borrow_mut().validate_and_append_blinding_commitment(label, &com)?;
            }
        }

        // Compute the challenge value for each proof
        let minus_c = self
            .transcripts
            .iter_mut()
            .map(|trans| -trans.borrow_mut().get_challenge(b"chal"))
            .collect::<Vec<_>>();

        let num_s = self.static_points.len();
        let num_i = self.instance_points.len();
        let num_c = self.constraints.len();

        let mut static_coeffs = vec![G::ScalarField::zero(); num_s];
        let mut instance_coeffs = Matrix::<G::ScalarField>::new(num_i + num_c, self.batch_size);

        for i in 0..num_c {
            let (ref lhs_var, ref rhs_lc) = self.constraints[i];
            for j in 0..self.batch_size {
                let random_factor = G::ScalarField::from(thread_rng().gen::<u128>());

                // rand*( sum(P_i, resp_i) - c * Q - Q_com) == 0

                instance_coeffs[(num_i + i, j)] -= random_factor;

                match lhs_var {
                    PointVar::Static(var_idx) => {
                        static_coeffs[*var_idx] += random_factor * minus_c[j];
                    }
                    PointVar::Instance(var_idx) => {
                        instance_coeffs[(*var_idx, j)] += random_factor * minus_c[j];
                    }
                }

                for (sc_var, pt_var) in rhs_lc {
                    let resp = proofs[j].responses[sc_var.0];
                    match pt_var {
                        PointVar::Static(var_idx) => {
                            static_coeffs[*var_idx] += random_factor * resp;
                        }
                        PointVar::Instance(var_idx) => {
                            instance_coeffs[(*var_idx, j)] += random_factor * resp;
                        }
                    }
                }
            }
        }

        let mut instance_points = self.instance_points.clone();
        for i in 0..num_c {
            let ith_commitments = proofs.iter().map(|proof| proof.commitments[i]);
            instance_points.push(ith_commitments.collect());
        }

        let flat_instance_points = instance_points
            .iter()
            .flat_map(|inner| inner.iter().cloned())
            .collect::<Vec<G>>();

        let scalar_coeffs: Vec<_> = static_coeffs
            .iter()
            .chain(instance_coeffs.row_major_entries())
            .cloned()
            .collect::<Vec<_>>();
        let points: Vec<_> = self.static_points
            .iter()
            .chain(flat_instance_points.iter())
            .cloned()
            .collect::<Vec<_>>();

        let check = G::Group::msm(&points[..], &scalar_coeffs[..])
            .map_err(|_| ProofError::VerificationFailure)?;

        if check.is_zero() {
            Ok(())
        } else {
            Err(ProofError::VerificationFailure)
        }
    }
}

impl<'a, G: AffineRepr, U: TranscriptProtocol<G>, T: BorrowMut<U>> SchnorrCS for BatchVerifier<G, U, T> {
    type ScalarVar = ScalarVar;
    type PointVar = PointVar;

    fn constrain(&mut self, lhs: PointVar, linear_combination: Vec<(ScalarVar, PointVar)>) -> usize {
        self.constraints.push((lhs, linear_combination));
        self.constraints.len() - 1
    }

    fn require_range_proof(&mut self, _constraint: usize) {}
}
