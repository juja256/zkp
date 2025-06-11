//! Contains lower-level tools that allow programmable specification
//! of proof statements.
//!
//! The higher-level [`define_proof`] macro allows declarative
//! specification of static proof statements, and expands into code
//! that uses this lower-level API.  This lower-level API can also be
//! used directly to perform imperative specification of proof
//! statements, allowing proof statements with runtime parameters
//! (e.g., an anonymous credential with a variable number of
//! attributes).
//!
//! The `SchnorrCS` trait defines the common constraint system API
//! used for specifying proof statements; it is implemented by the
//! `Prover`, `Verifier`, and `BatchVerifier` structs.
//!
//! Roughly speaking, the tools fit together in the following way:
//!
//! * Statements are defined as generic functions which take a
//! `SchnorrCS` implementation and some variables,
//! and add the proof statements to the constraint system;
//!
//! * To create a proof, construct a `Prover`,
//! allocate and assign variables, pass the prover and the variables
//! to the generic statement function, then consume the prover to
//! obtain a proof.
//!
//! * To verify a proof, construct a `Verifier`,
//! allocate and assign variables, pass the verifier and the variables
//! to the generic statement function, then consume the verifier to
//! obtain a verification result.
//!
//! Note that the expansion of the [`define_proof`] macro contains a
//! public `internal` module with the generated proof statement
//! function, making it possible to combine generated and hand-crafted
//! proof statements into the same constraint system.

/// Implements batch verification of batchable proofs.
pub mod batch_verifier;
/// Implements proof creation.
pub mod prover;

pub mod cross_prover;
/// Implements proof verification of compact and batchable proofs.
pub mod verifier;

pub mod cross_verifier;

pub mod cross_dleq;
pub mod dalek_ark;

use std::convert::TryInto;

use ark_ff::{BigInt, Field, PrimeField, UniformRand};
use ark_ec::AffineRepr;
use ark_serialize::{CanonicalDeserialize, CanonicalSerialize, Compress, SerializationError};
use merlin::TranscriptRngBuilder;
use rand::Rng;
use crate::ark_ff::BigInteger;

use crate::{ProofError, Transcript};

#[cfg(feature = "rangeproof")]
macro_rules! cast {
    ($target: expr, $pat: path) => {
        {
            if let $pat(a) = $target { // #1
                a
            } else {
                panic!(
                    "mismatch variant when cast to {}", 
                    stringify!($pat)); // #2
            }
        }
    };
}


/// A secret variable used during proving.
#[derive(Copy, Clone, Debug)]
pub struct ScalarVar(usize);
/// A public variable used during proving.
#[derive(Copy, Clone, Debug)]
pub struct PointVar(usize);

#[derive(Copy, Clone, Debug)]
pub enum Point<G1: AffineRepr, G2: AffineRepr> {
    G1(G1),
    G2(G2)
}

impl<G1: AffineRepr, G2: AffineRepr> Point<G1, G2> {
    pub fn is_zero(&self) -> bool {
        match self {
            Point::G1(point) => point.is_zero(),
            Point::G2(point) => point.is_zero(),
        }
    }
}

impl<G1: AffineRepr, G2: AffineRepr> CanonicalSerialize for Point<G1, G2> {    
    fn serialize_with_mode<W: std::io::Write>(
        &self,
        writer: W,
        compress: Compress,
    ) -> Result<(), SerializationError> {
        match self {
            Point::G1(point) => point.serialize_with_mode(writer, compress),
            Point::G2(point) => point.serialize_with_mode(writer, compress)
        }
    }
    
    fn serialized_size(&self, compress: Compress) -> usize {
        match self {
            Point::G1(point) => point.serialized_size(compress),
            Point::G2(point) => point.serialized_size(compress)
        }
    }
}

#[derive(Clone, Debug)]
pub enum Scalar<F1: PrimeField, F2: PrimeField> 
    where F1::BigInt: Into<BigInt<4>>, 
          F2::BigInt: Into<BigInt<4>>,
 {
    F1(F1),
    F2(F2),
    Cross(BigInt<4>)
}

impl<F1: PrimeField, F2: PrimeField> CanonicalSerialize for Scalar<F1, F2> 
    where F1::BigInt: Into<BigInt<4>>, 
          F2::BigInt: Into<BigInt<4>> {
    fn serialize_with_mode<W: std::io::Write>(
        &self,
        mut writer: W,
        compress: Compress,
    ) -> Result<(), SerializationError> {
        match self {
            Scalar::F1(scalar) => {
                0u8.serialize_with_mode(&mut writer, compress)?;
                scalar.serialize_with_mode(&mut writer, compress)
            },
            Scalar::F2(scalar) => {
                1u8.serialize_with_mode(&mut writer, compress)?;
                scalar.serialize_with_mode(&mut writer, compress)
            },
            Scalar::Cross(bigint) => {
                2u8.serialize_with_mode(&mut writer, compress)?;
                bigint.serialize_with_mode(&mut writer, compress)
            },
        }
    }

    fn serialized_size(&self, compress: Compress) -> usize {
        1 + match self {
            Scalar::F1(scalar) => scalar.serialized_size(compress),
            Scalar::F2(scalar) => scalar.serialized_size(compress),
            Scalar::Cross(bigint) => bigint.serialized_size(compress),
        }
    }
}

impl<F1: PrimeField, F2: PrimeField> ark_serialize::Valid for Scalar<F1, F2> 
    where F1::BigInt: Into<BigInt<4>>, 
          F2::BigInt: Into<BigInt<4>> {
    fn check(&self) -> Result<(), SerializationError> {
        match self {
            Scalar::F1(scalar) => scalar.check(),
            Scalar::F2(scalar) => scalar.check(),
            Scalar::Cross(bigint) => bigint.check(),
        }
    }
}

impl<F1: PrimeField, F2: PrimeField> CanonicalDeserialize for Scalar<F1, F2> 
    where F1::BigInt: Into<BigInt<4>>, 
          F2::BigInt: Into<BigInt<4>> {
    fn deserialize_with_mode<R: std::io::Read>(
        mut reader: R,
        compress: Compress,
        validate: ark_serialize::Validate,
    ) -> Result<Self, SerializationError> {
        let tag: u8 = u8::deserialize_with_mode(&mut reader, compress, validate)?;
        match tag {
            0 => Ok(Scalar::F1(F1::deserialize_with_mode(&mut reader, compress, validate)?)),
            1 => Ok(Scalar::F2(F2::deserialize_with_mode(&mut reader, compress, validate)?)),
            2 => Ok(Scalar::Cross(BigInt::<4>::deserialize_with_mode(&mut reader, compress, validate)?)),
            _ => Err(SerializationError::InvalidData),
        }
    }
}

impl<F1: PrimeField, F2: PrimeField> Scalar<F1, F2> 
    where F1::BigInt: Into<BigInt<4>>, 
          F2::BigInt: Into<BigInt<4>>,
 {
    pub fn into_bigint(&self) -> BigInt<4> {
        match self {
            Scalar::F1(scalar) => scalar.into_bigint().into(),
            Scalar::F2(scalar) => scalar.into_bigint().into(),
            Scalar::Cross(scalar) => scalar.clone(),
        }
    }
}

pub type Challenge = BigInt<4>;

/// An interface for specifying proof statements, common between
/// provers and verifiers.
///
/// The variables for the constraint system are provided as associated
/// types, allowing different implementations to have different point
/// and scalar types.  For instance, the batch verifier has two types
/// of point variables, one for points common to all proofs in the
/// batch, and one for points varying per-proof.
///
/// This is why variable allocation is *not* included in the trait, as
/// different roles may have different behaviour -- for instance, a
/// prover needs to supply assignments to the scalar variables, but
/// a verifier doesn't have access to the prover's secret scalars.
///
/// To specify a proof statement using this trait, write a generic
/// function that takes a constraint system as a parameter and adds
/// the statements.  For instance, to specify an equality of discrete
/// logarithms, one could write
/// ```rust,ignore
/// fn dleq_statement<CS: SchnorrCS>(
///     cs: &mut CS,
///     x: CS::ScalarVar,
///     A: CS::PointVar,
///     G: CS::PointVar,
///     B: CS::PointVar,
///     H: CS::PointVar,
/// ) {
///     cs.constrain(A, vec![(x, B)]);
///     cs.constrain(G, vec![(x, H)]);
/// }
/// ```
///
/// This means that multiple statements can be added to the same
/// proof, independently of the specification of the statement, by
/// constructing a constraint system and then passing it to multiple
/// statement functions.
pub trait SchnorrCS {
    /// A handle for a scalar variable in the constraint system.
    type ScalarVar: Copy;
    /// A handle for a point variable in the constraint system.
    type PointVar: Copy;

    /// Add a constraint of the form `lhs = linear_combination`.
    fn constrain(
        &mut self,
        lhs: Self::PointVar,
        linear_combination: Vec<(Self::ScalarVar, Self::PointVar)>,
    ) -> usize;

    #[cfg(feature = "rangeproof")]
    /// Mark the contraint as a range proof commitment
    fn require_range_proof(&mut self, constraint: usize);
}

pub mod standard_transcript{
    use ark_ec::AffineRepr;
    use ark_ff::{Field};
    use merlin::{Transcript, TranscriptRngBuilder};

    use crate::ProofError;

    /// This trait defines the wire format for how the constraint system
    /// interacts with the proof transcript.
    pub trait TranscriptProtocol<G: AffineRepr> {
        /// Appends `label` to the transcript as a domain separator.
        fn domain_sep(&mut self, label: &'static [u8]);

        /// Append the `label` for a scalar variable to the transcript.
        ///
        /// Note: this does not commit its assignment, which is secret,
        /// and only serves to bind the proof to the variable allocations.
        fn append_scalar_var(&mut self, label: &'static [u8]);

        /// Append a point variable to the transcript, for use by a prover.
        ///
        /// Returns the compressed point encoding to allow reusing the
        /// result of the encoding computation; the return value can be
        /// discarded if it's unused.
        fn append_point_var(
            &mut self,
            label: &'static [u8],
            point: &G,
        );

        /// Check that point variable is not the identity and
        /// append it to the transcript, for use by a verifier.
        ///
        /// Returns `Ok(())` if the point is not the identity point (and
        /// therefore generates the full ristretto255 group).
        ///
        /// Using this function prevents small-subgroup attacks.
        fn validate_and_append_point_var(
            &mut self,
            label: &'static [u8],
            point: &G,
        ) -> Result<(), ProofError>;

        /// Append a blinding factor commitment to the transcript, for use by
        /// a prover.
        ///
        /// Returns the compressed point encoding to allow reusing the
        /// result of the encoding computation; the return value can be
        /// discarded if it's unused.
        fn append_blinding_commitment(
            &mut self,
            label: &'static [u8],
            point: &G,
        );

        /// Check that a blinding factor commitment is not the identity and
        /// commit it to the transcript, for use by a verifier.
        ///
        /// Returns `Ok(())` if the point is not the identity point (and
        /// therefore generates the full ristretto255 group).
        ///
        /// Using this function prevents small-subgroup attacks.
        fn validate_and_append_blinding_commitment(
            &mut self,
            label: &'static [u8],
            point: &G,
        ) -> Result<(), ProofError>;

        fn build_rng(&self) -> TranscriptRngBuilder;

        /// Get a scalar challenge from the transcript.
        fn get_challenge(&mut self, label: &'static [u8]) -> G::ScalarField;
    }

    impl<G: AffineRepr> TranscriptProtocol<G> for Transcript {
        fn domain_sep(&mut self, label: &'static [u8]) {
            self.append_message(b"dom-sep", b"schnorrzkp/1.0/ristretto255");
            self.append_message(b"dom-sep", label);
        }

        fn append_scalar_var(&mut self, label: &'static [u8]) {
            self.append_message(b"scvar", label);
        }

        fn append_point_var(
            &mut self,
            label: &'static [u8],
            point: &G,
        ) {
            let mut bytes = Vec::new();
            point.serialize_uncompressed(&mut bytes).unwrap();
            self.append_message(b"ptvar", label);
            self.append_message(b"val", &bytes);
        }

        fn validate_and_append_point_var(
            &mut self,
            label: &'static [u8],
            point: &G,
        ) -> Result<(), ProofError> {
            if point.is_zero() {
                return Err(ProofError::VerificationFailure);
            }
            let mut bytes = Vec::new();
            point.serialize_uncompressed(&mut bytes).unwrap();
            self.append_message(b"ptvar", label);
            self.append_message(b"val", &bytes);
            Ok(())
        }

        fn append_blinding_commitment(
            &mut self,
            label: &'static [u8],
            point: &G,
        ) {
            let mut bytes = Vec::new();
            point.serialize_uncompressed(&mut bytes).unwrap();
            self.append_message(b"blindcom", label);
            self.append_message(b"val", &bytes);
        }

        fn validate_and_append_blinding_commitment(
            &mut self,
            label: &'static [u8],
            point: &G,
        ) -> Result<(), ProofError> {
            if point.is_zero() {
                return Err(ProofError::VerificationFailure);
            }
            let mut bytes = Vec::new();
            point.serialize_uncompressed(&mut bytes).unwrap();
            self.append_message(b"blindcom", label);
            self.append_message(b"val", &bytes);
            Ok(())
        }

        fn build_rng(&self) -> TranscriptRngBuilder {
            self.build_rng()    
        }

        fn get_challenge(&mut self, label: &'static [u8]) -> G::ScalarField {
            let mut bytes = [0; 64];
            self.challenge_bytes(label, &mut bytes);
            G::ScalarField::from_random_bytes(&bytes).unwrap()
        }
    }

}

pub mod cross_transcript{
    use std::{convert::TryInto, io::Chain};

    use ark_ec::AffineRepr;
    use ark_ff::BigInt;
    use ark_serialize::CanonicalSerialize;
    use merlin::{Transcript, TranscriptRngBuilder};

    use crate::ProofError;

    use super::{Challenge, Point};

    /// This trait defines the wire format for how the constraint system
    /// interacts with the proof transcript.
    pub trait TranscriptProtocol<G1: AffineRepr + CanonicalSerialize, G2: AffineRepr + CanonicalSerialize> {
        /// Appends `label` to the transcript as a domain separator.
        fn domain_sep(&mut self, label: &'static [u8]);

        /// Append the `label` for a scalar variable to the transcript.
        ///
        /// Note: this does not commit its assignment, which is secret,
        /// and only serves to bind the proof to the variable allocations.
        fn append_scalar_var(&mut self, label: &'static [u8]);

        /// Append a point variable to the transcript, for use by a prover.
        ///
        /// Returns the compressed point encoding to allow reusing the
        /// result of the encoding computation; the return value can be
        /// discarded if it's unused.
        fn append_point_var(
            &mut self,
            label: &'static [u8],
            point: &Point<G1, G2>,
        );

        /// Check that point variable is not the identity and
        /// append it to the transcript, for use by a verifier.
        ///
        /// Returns `Ok(())` if the point is not the identity point (and
        /// therefore generates the full ristretto255 group).
        ///
        /// Using this function prevents small-subgroup attacks.
        fn validate_and_append_point_var(
            &mut self,
            label: &'static [u8],
            point: &Point<G1, G2>,
        ) -> Result<(), ProofError>;

        /// Append a blinding factor commitment to the transcript, for use by
        /// a prover.
        ///
        /// Returns the compressed point encoding to allow reusing the
        /// result of the encoding computation; the return value can be
        /// discarded if it's unused.
        fn append_blinding_commitment(
            &mut self,
            label: &'static [u8],
            point: &Point<G1, G2>,
        );

        /// Check that a blinding factor commitment is not the identity and
        /// commit it to the transcript, for use by a verifier.
        ///
        /// Returns `Ok(())` if the point is not the identity point (and
        /// therefore generates the full ristretto255 group).
        ///
        /// Using this function prevents small-subgroup attacks.
        fn validate_and_append_blinding_commitment(
            &mut self,
            label: &'static [u8],
            point: &Point<G1, G2>,
        ) -> Result<(), ProofError>;

        fn build_rng(&self) -> TranscriptRngBuilder;

        /// Get a scalar challenge from the transcript.
        fn get_challenge(&mut self, label: &'static [u8], size: usize) -> Challenge;

        fn as_transcript(&mut self) -> &mut Transcript;
    }

    impl<G1: AffineRepr + CanonicalSerialize, G2: AffineRepr + CanonicalSerialize> TranscriptProtocol<G1, G2> for Transcript {
        fn as_transcript(&mut self) -> &mut Transcript {
            self
        }

        fn domain_sep(&mut self, label: &'static [u8]) {
            self.append_message(b"dom-sep", b"schnorrcrosszkp/1.0/");
            self.append_message(b"dom-sep", label);
        }

        fn append_scalar_var(&mut self, label: &'static [u8]) {
            self.append_message(b"scvar", label);
        }

        fn append_point_var(
            &mut self,
            label: &'static [u8],
            point: &Point<G1, G2>,
        ) {
            let mut bytes = Vec::new();
            point.serialize_uncompressed(&mut bytes).unwrap();
            self.append_message(b"ptvar", label);
            self.append_message(b"val", &bytes);
        }

        fn validate_and_append_point_var(
            &mut self,
            label: &'static [u8],
            point: &Point<G1, G2>,
        ) -> Result<(), ProofError> {
            if point.is_zero() {
                return Err(ProofError::VerificationFailure);
            }
            let mut bytes = Vec::new();
            point.serialize_uncompressed(&mut bytes).unwrap();
            self.append_message(b"ptvar", label);
            self.append_message(b"val", &bytes);
            Ok(())
        }

        fn append_blinding_commitment(
            &mut self,
            label: &'static [u8],
            point: &Point<G1, G2>,
        ) {
            let mut bytes = Vec::new();
            point.serialize_uncompressed(&mut bytes).unwrap();
            self.append_message(b"blindcom", label);
            self.append_message(b"val", &bytes);
        }

        fn validate_and_append_blinding_commitment(
            &mut self,
            label: &'static [u8],
            point: &Point<G1, G2>,
        ) -> Result<(), ProofError> {
            if point.is_zero() {
                return Err(ProofError::VerificationFailure);
            }
            let mut bytes = Vec::new();
            point.serialize_uncompressed(&mut bytes).unwrap();
            self.append_message(b"blindcom", label);
            self.append_message(b"val", &bytes);
            Ok(())
        }

        fn build_rng(&self) -> TranscriptRngBuilder {
            self.build_rng()    
        }

        fn get_challenge(&mut self, label: &'static [u8], size: usize) -> Challenge {
            let mut bytes = [0; 64];
            self.challenge_bytes(label, &mut bytes[..size]);

            BigInt::new([
                u64::from_le_bytes(bytes[0..8].try_into().unwrap()),
                u64::from_le_bytes(bytes[8..16].try_into().unwrap()),
                u64::from_le_bytes(bytes[16..24].try_into().unwrap()),
                u64::from_le_bytes(bytes[24..32].try_into().unwrap()),
            ])
        }
    }

}
