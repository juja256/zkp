use thiserror::Error;
/// An error during proving or verification, such as a verification failure.
#[derive(Debug, Error)]
pub enum ProofError {
    /// Something is wrong with the proof, causing a verification failure.
    #[error("Verification failed.")]
    VerificationFailure,
    /// Occurs during batch verification if the batch parameters are mis-sized.
    #[error("Mismatched parameter sizes for batch verification.")]
    BatchSizeMismatch,

    #[error("Cross scalar variable must not exceed b_x bits")]
    ScalarVarExceedsBound,

    #[error("Point variable assignment mismatch")]
    PointVarMismatch,

    #[error("Prover aborted")]
    ProverAborted,

    #[error("Proof parsing failed")]
    ParsingFailure,
}
