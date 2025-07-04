use std::io::Cursor;

use ark_ec::AffineRepr;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Compress, SerializationError};
use ark_ff::{BigInt, PrimeField};
use curve25519_dalek::ristretto::CompressedRistretto;
use crate::toolbox::{Challenge, FromBytes, Scalar, ToBytes};

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

impl<F: PrimeField> ToBytes for CompactProof<F> {}
impl<F: PrimeField> FromBytes for CompactProof<F> {}

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

impl<G: AffineRepr> ToBytes for BatchableProof<G> {}
impl<G: AffineRepr> FromBytes for BatchableProof<G> {}

#[derive(Clone)]
pub struct RangeProof (
    /// The range proof.
    pub bulletproofs::RangeProof,
);

impl CanonicalSerialize for RangeProof {
    fn serialize_with_mode<W: std::io::Write>(
        &self,
        mut writer: W,
        compress: Compress,
    ) -> Result<(), SerializationError> {
        // Serialize the proof
        let proof_bytes = self.0.to_bytes();
        (proof_bytes.len() as u32).serialize_with_mode(&mut writer, compress)?;
        writer.write_all(&proof_bytes)?;

        Ok(())
    }

    fn serialized_size(&self, _compress: Compress) -> usize {
        let proof_size = self.0.to_bytes().len();
        proof_size + 4
    }
}

impl ark_serialize::Valid for RangeProof {
    fn check(&self) -> Result<(), SerializationError> {
        Ok(())
    }
}

impl CanonicalDeserialize for RangeProof {
    fn deserialize_with_mode<R: std::io::Read>(
        mut reader: R,
        _compress: ark_serialize::Compress,
        _validate: ark_serialize::Validate,
    ) -> Result<Self, ark_serialize::SerializationError> {
        // Deserialize the proof
        let proof_len = u32::deserialize_compressed(&mut reader)? as usize;
        let mut proof_bytes = vec![0u8; proof_len];
        reader.read_exact(&mut proof_bytes)?;
        let proof = bulletproofs::RangeProof::from_bytes(&proof_bytes)
            .map_err(|_| ark_serialize::SerializationError::InvalidData)?;

        Ok(RangeProof ( proof ))
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
    #[cfg(feature = "rangeproof")]
    /// Range proof for the secret variables.
    pub range_proofs: Vec<RangeProof>,
}

impl<F1: PrimeField, F2: PrimeField> ToBytes for CompactCrossProof<F1, F2> 
    where F1::BigInt: Into<BigInt<4>>, 
          F2::BigInt: Into<BigInt<4>> {}

impl<F1: PrimeField, F2: PrimeField> FromBytes for CompactCrossProof<F1, F2> 
    where F1::BigInt: Into<BigInt<4>>, 
          F2::BigInt: Into<BigInt<4>> {}