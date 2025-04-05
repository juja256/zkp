use std::io::Cursor;

use ark_ec::AffineRepr;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Compress, SerializationError};
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

#[derive(Clone)]
pub struct RangeProof {
    /// The range proof.
    pub proof: bulletproofs::RangeProof,
    /// The commitments factor for the range proof.
    pub commitment: CompressedRistretto,
}

impl CanonicalSerialize for RangeProof {
    fn serialize_with_mode<W: std::io::Write>(
        &self,
        mut writer: W,
        compress: Compress,
    ) -> Result<(), SerializationError> {
        // Serialize the proof
        let proof_bytes = self.proof.to_bytes();
        (proof_bytes.len() as u32).serialize_with_mode(&mut writer, compress)?;
        writer.write_all(&proof_bytes)?;
        writer.write_all(self.commitment.as_bytes())?;

        Ok(())
    }

    fn serialized_size(&self, _compress: Compress) -> usize {
        let proof_size = self.proof.to_bytes().len();
        let commitments_size: usize = 32;
        proof_size + commitments_size + 8
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

        
        // Deserialize the commitments
        let mut buf = [0u8; 32];
        reader.read_exact(&mut buf)?;
        let commitment = CompressedRistretto::from_slice(&buf).map_err(|_| {
            ark_serialize::SerializationError::InvalidData
        })?;


        Ok(RangeProof { proof, commitment })
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
    /// Range proof for the secret variable.
    pub range_proofs: Vec<RangeProof>,
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