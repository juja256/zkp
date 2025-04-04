use std::io::Cursor;

use bulletproofs::RangeProof;
use ark_ec::AffineRepr;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize};
use ark_ff::{BigInt, PrimeField};
use curve25519_dalek::ristretto::CompressedRistretto;
use crate::toolbox::{Challenge, Scalar};

use crate::ProofError;
/// A Schnorr proof in compact format.
///
/// This performs the standard folklore optimization of sending the
/// challenge in place of the commitments to the prover's randomness.
/// However, this optimization prevents batch verification.
///
/// This proof has `m+1` 32-byte elements, where `m` is the number of
/// secret variables.  This means there is no space savings for a
/// `CompactProof` over a `BatchableProof` when there is only one
/// statement.
#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct CompactProof<F: PrimeField> {
    /// The Fiat-Shamir challenge.
    pub challenge: F,
    /// The prover's responses, one per secret variable.
    pub responses: Vec<F>,
}

impl<F: PrimeField> CompactProof<F> {
    pub fn to_bytes(&self) -> Result<Vec<u8>, ProofError> {
        let mut cursor = Cursor::new(Vec::new());
        self.serialize_compressed(&mut cursor).map_err(|_| ProofError::ParsingFailure)?;
        Ok(cursor.into_inner())
    }

    /// Deserializes the proof from a byte slice.
    ///
    /// Returns an error if the byte slice cannot be parsed into a `R1CSProof`.
    pub fn from_bytes(slice: &[u8]) -> Result<CompactProof<F>, ProofError> {
        let mut cursor = Cursor::new(slice);
        let proof = CompactProof::<F>::deserialize_compressed(&mut cursor);
        if proof.is_ok() {
            Ok(proof.unwrap())
        } else {
            Err(ProofError::ParsingFailure)
        }
    }
}

/// A Schnorr proof in batchable format.
///
/// This proof has `m+n` 32-byte elements, where `m` is the number of
/// secret variables and `n` is the number of statements.
#[derive(Clone, CanonicalDeserialize, CanonicalSerialize)]
pub struct BatchableProof<G: AffineRepr> {
    /// Commitments to the prover's blinding factors.
    pub commitments: Vec<G>,
    /// The prover's responses, one per secret variable.
    pub responses: Vec<G::ScalarField>,
}

impl<G: AffineRepr> BatchableProof<G> {
    pub fn to_bytes(&self) -> Result<Vec<u8>, ProofError> {
        let mut cursor = Cursor::new(Vec::new());
        self.serialize_compressed(&mut cursor).map_err(|_| ProofError::ParsingFailure)?;
        Ok(cursor.into_inner())
    }

    /// Deserializes the proof from a byte slice.
    ///
    /// Returns an error if the byte slice cannot be parsed into a `R1CSProof`.
    pub fn from_bytes(slice: &[u8]) -> Result<BatchableProof<G>, ProofError> {
        let mut cursor = Cursor::new(slice);
        let proof = BatchableProof::<G>::deserialize_compressed(&mut cursor);
        if proof.is_ok() {
            Ok(proof.unwrap())
        } else {
            Err(ProofError::ParsingFailure)
        }
    }
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct CompactCrossProof<F1: PrimeField, F2: PrimeField>  
    where F1::BigInt: Into<BigInt<4>>, 
          F2::BigInt: Into<BigInt<4>> {
    /// The Fiat-Shamir challenge.
    pub challenge: Challenge,
    /// The prover's responses, one per secret variable.
    pub responses: Vec<Scalar<F1, F2>>,

    pub range_proof: (RangeProof, Vec<CompressedRistretto>),
}

impl<F1: PrimeField, F2: PrimeField> CompactCrossProof<F1, F2> 
    where F1::BigInt: Into<BigInt<4>>, 
          F2::BigInt: Into<BigInt<4>> {
    pub fn to_bytes(&self) -> Result<Vec<u8>, ProofError> {
        let mut cursor = Cursor::new(Vec::new());
        self.serialize_compressed(&mut cursor).map_err(|_| ProofError::ParsingFailure)?;
        Ok(cursor.into_inner())
    }

    /// Deserializes the proof from a byte slice.
    ///
    /// Returns an error if the byte slice cannot be parsed into a `R1CSProof`.
    pub fn from_bytes(slice: &[u8]) -> Result<CompactCrossProof<F1, F2>, ProofError> {
        let mut cursor = Cursor::new(slice);
        let proof = CompactCrossProof::<F1, F2>::deserialize_compressed(&mut cursor);
        if proof.is_ok() {
            Ok(proof.unwrap())
        } else {
            Err(ProofError::ParsingFailure)
        }
    }
}