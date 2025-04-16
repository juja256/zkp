// -*- coding: utf-8; mode: rust; -*-
//
// To the extent possible under law, the authors have waived all
// copyright and related or neighboring rights to zkp,
// using the Creative Commons "CC0" public domain dedication.  See
// <http://creativecommons.org/publicdomain/zero/1.0/> for full
// details.
//
// Authors:
// - Henry de Valence <hdevalence@hdevalence.ca>
// - Yevhen Hrubiian <grubian.euhen@gmail.com>

#[doc(hidden)]
#[macro_export]
macro_rules! __compute_formula_constraint {
    // Unbracket a statement
    (($public_vars:ident, $secret_vars:ident) ($($x:tt)*)) => {
        // Add a trailing +
        __compute_formula_constraint!(($public_vars,$secret_vars) $($x)* +)
    };
    // Inner part of the formula: give a list of &Scalars
    // Since there's a trailing +, we can just generate the list as normal...
    (($public_vars:ident, $secret_vars:ident)
     $( $scalar:ident * $point:ident +)+ ) => {
        vec![ $( ($secret_vars.$scalar , $public_vars.$point), )* ]
    };
}

/// Creates a module with code required to produce a non-interactive
/// zero-knowledge proof statement, to serialize it to wire format, to
/// parse from wire format, and to verify the proof or batch-verify
/// multiple proofs.
///
/// The statement is specified in an embedded DSL resembling
/// Camenisch-Stadler notation.  For instance, a proof of knowledge of
/// two equal discrete logarithms ("DLEQ") is specified as:
///
/// ```rust,ignore
/// define_proof! {dleq, "DLEQ Proof", (x), (A, B, H), (G) : A = (x * G), B = (x * H) }
/// ```
///
/// This creates a module `dleq` with code for proving knowledge of a
/// secret `x: Scalar` such that `A = x * G`, `B = x * H` for
/// per-proof public parameters `A, B, H: RistrettoPoint` and common
/// parameters `G: RistrettoPoint`; the UTF-8 string `"DLEQ Proof"` is
/// added to the transcript as a domain separator.
///
/// In general the syntax is
/// ```rust,ignore
/// define_proof!{
///     module_name,   // all generated code for this statement goes here
///     "Proof Label", // a UTF-8 domain separator unique to the statement
///     (x,y,z,...),   // secret variable labels (preferably lower-case)
///     (A,B,C,...),   // public per-proof parameter labels (upper-case)
///     (G,H,...)      // public common parameter labels (upper-case)
///     :
///     LHS = (x * A + y * B + z * C + ... ),  // comma-separated statements
///     ...
/// }
/// ```
///
/// Statements have the form `LHS = (A * x + B * y + C * z + ... )`,
/// where `LHS` is one of the points listed as a public parameter, and
/// the right-hand side is a sum of public points multiplied by secret
/// scalars.
///
/// Points which have the same assignment for all instances of the
/// proof statement (for instance, a basepoint) should be specified as
/// common public parameters, so that the generated implementation of
/// batch verification is more efficient.
///
/// Proof creation is done in constant time.  Proof verification uses
/// variable-time code.
#[macro_export]
macro_rules! define_proof {
    (
        $proof_module_name:ident // Name of the module to create
        ,
        $proof_label_string:expr // A string literal, used as a domain separator
        ,
        ( $($secret_var:ident),+ ) // Secret variables, sep by commas
        ,
        ( $($instance_var:ident),* ) // Public instance variables, separated by commas
        ,
        ( $($common_var:ident),* ) // Public common variables, separated by commas
        :
        // List of statements to prove
        // Format: LHS = ( ... RHS expr ... ),
        $($lhs:ident = $statement:tt),+
    ) => {
        /// An auto-generated Schnorr proof implementation.
        ///
        /// Proofs are created using `prove_compact` or
        /// `prove_batchable`, producing `CompactProof`s or
        /// `BatchableProof`s respectively.  These are verified
        /// using `verify_compact` and `verify_batchable`;
        /// `BatchableProofs` can also be batch-verified using
        /// `batch_verify`, but they have slightly larger proof
        /// sizes compared to `CompactProof`s.
        ///
        /// The internal details of the proof statement are accessible
        /// in the `internals` module.  While this is not necessary
        /// to create and verify proofs, the it can be used with the
        /// lower-level constraint system API to manually combine
        /// statements from different proofs.
        #[allow(non_snake_case)]
        pub mod $proof_module_name {
            use $crate::ark_ec::{AffineRepr, CurveGroup};
            use $crate::ark_ff::{BigInteger, PrimeField, UniformRand};
            use $crate::ark_ec::VariableBaseMSM;

            use $crate::toolbox::prover::Prover;
            use $crate::toolbox::verifier::Verifier;

            pub use $crate::merlin::Transcript;
            pub use $crate::{CompactProof, BatchableProof, ProofError};

            /// The generated [`internal`] module contains lower-level
            /// functions at the level of the Schnorr constraint
            /// system API.
            pub mod internal {
                use $crate::toolbox::SchnorrCS;

                /// The proof label committed to the transcript as a domain separator.
                pub const PROOF_LABEL: &'static str = $proof_label_string;

                /// A container type that holds transcript labels for secret variables.
                pub struct TranscriptLabels {
                    $( pub $secret_var: &'static str, )+
                    $( pub $instance_var: &'static str, )+
                    $( pub $common_var: &'static str, )+
                }

                /// The transcript labels used for each secret variable.
                pub const TRANSCRIPT_LABELS: TranscriptLabels = TranscriptLabels {
                    $( $secret_var: stringify!($secret_var), )+
                    $( $instance_var: stringify!($instance_var), )+
                    $( $common_var: stringify!($common_var), )+
                };

                /// A container type that simulates named parameters for [`proof_statement`].
                #[derive(Copy, Clone)]
                pub struct SecretVars<CS: SchnorrCS> {
                    $( pub $secret_var: CS::ScalarVar, )+
                }

                /// A container type that simulates named parameters for [`proof_statement`].
                #[derive(Copy, Clone)]
                pub struct PublicVars<CS: SchnorrCS> {
                    $( pub $instance_var: CS::PointVar, )+
                    $( pub $common_var: CS::PointVar, )+
                }

                /// The underlying proof statement generated by the macro invocation.
                ///
                /// This function exists separately from the proving
                /// and verification functions to allow composition of
                /// different proof statements with common variable
                /// assignments.
                pub fn proof_statement<CS: SchnorrCS>(
                    cs: &mut CS,
                    secrets: SecretVars<CS>,
                    publics: PublicVars<CS>,
                ) {
                    $(
                        cs.constrain(
                            publics.$lhs,
                            __compute_formula_constraint!( (publics, secrets) $statement ),
                        );
                    )+
                }
            }

            /// Named parameters for [`prove_compact`] and [`prove_batchable`].
            #[derive(Copy, Clone)]
            pub struct ProveAssignments<'a, G: AffineRepr> {
                $(pub $secret_var: &'a G::ScalarField,)+
                $(pub $instance_var: &'a G,)+
                $(pub $common_var: &'a G,)+
            }

            /// Named parameters for [`verify_compact`] and [`verify_batchable`].
            #[derive(Copy, Clone)]
            pub struct VerifyAssignments<'a, G: AffineRepr> {
                $(pub $instance_var: &'a G,)+
                $(pub $common_var: &'a G,)+
            }

            /// Point encodings computed during proving and returned to allow reuse.
            ///
            /// This is used to allow a prover to avoid having to
            /// re-compress points used in the proof that may be
            /// necessary to supply to the verifier.
            #[derive(Copy, Clone)]
            pub struct CompressedPoints<G: AffineRepr> {
                $(pub $instance_var: G,)+
                $(pub $common_var: G,)+
            }

            /// Named parameters for [`batch_verify`].
            #[derive(Clone)]
            pub struct BatchVerifyAssignments<G: AffineRepr> {
                $(pub $instance_var: Vec<G>,)+
                $(pub $common_var: G,)+
            }

            fn build_prover<'a, G: AffineRepr>(
                transcript: &'a mut Transcript,
                assignments: ProveAssignments<G>,
            ) -> (Prover<G, Transcript, &'a mut Transcript>, CompressedPoints<G>) {
                use self::internal::*;
                use $crate::toolbox::prover::*;
                use $crate::toolbox::PointVar;
                
                let mut prover = Prover::new(PROOF_LABEL.as_bytes(), transcript);

                let secret_vars = SecretVars {
                    $(
                        $secret_var: prover.allocate_scalar(
                            TRANSCRIPT_LABELS.$secret_var.as_bytes(),
                            *assignments.$secret_var,
                        ),
                    )+
                };

                

                struct VarPointPairs<G: AffineRepr> {
                    $( pub $instance_var: (PointVar, G), )+
                    $( pub $common_var: (PointVar, G), )+
                }

                let pairs = VarPointPairs {
                    $(
                        $instance_var: prover.allocate_point(
                            TRANSCRIPT_LABELS.$instance_var.as_bytes(),
                            *assignments.$instance_var,
                        ),
                    )+
                    $(
                        $common_var: prover.allocate_point(
                            TRANSCRIPT_LABELS.$common_var.as_bytes(),
                            *assignments.$common_var,
                        ),
                    )+
                };

                // XXX return compressed points
                let public_vars = PublicVars {
                    $($instance_var: pairs.$instance_var.0,)+
                    $($common_var: pairs.$common_var.0,)+
                };

                let compressed = CompressedPoints {
                    $($instance_var: pairs.$instance_var.1,)+
                    $($common_var: pairs.$common_var.1,)+
                };

                proof_statement(&mut prover, secret_vars, public_vars);

                (prover, compressed)
            }

            /// Given a transcript and assignments to secret and public variables, produce a proof in compact format.
            pub fn prove_compact<G: AffineRepr>(
                transcript: &mut Transcript,
                assignments: ProveAssignments<G>,
            ) -> (CompactProof<G::ScalarField>, CompressedPoints<G>) {
                let (prover, compressed) = build_prover(transcript, assignments);

                (prover.prove_compact(), compressed)
            }

            /// Given a transcript and assignments to secret and public variables, produce a proof in batchable format.
            pub fn prove_batchable<G: AffineRepr>(
                transcript: &mut Transcript,
                assignments: ProveAssignments<G>,
            ) -> (BatchableProof<G>, CompressedPoints<G>) {
                let (prover, compressed) = build_prover(transcript, assignments);

                (prover.prove_batchable(), compressed)
            }

            fn build_verifier<'a, G: AffineRepr>(
                transcript: &'a mut Transcript,
                assignments: VerifyAssignments<G>,
            ) -> Result<Verifier<G, Transcript, &'a mut Transcript>, ProofError> {
                use self::internal::*;
                use $crate::toolbox::verifier::*;

                let mut verifier = Verifier::new(PROOF_LABEL.as_bytes(), transcript);

                let secret_vars = SecretVars {
                    $($secret_var: verifier.allocate_scalar(TRANSCRIPT_LABELS.$secret_var.as_bytes()),)+
                };

                let public_vars = PublicVars {
                    $(
                        $instance_var: verifier.allocate_point(
                            TRANSCRIPT_LABELS.$instance_var.as_bytes(),
                            *assignments.$instance_var,
                        )?,
                    )+
                    $(
                        $common_var: verifier.allocate_point(
                            TRANSCRIPT_LABELS.$common_var.as_bytes(),
                            *assignments.$common_var,
                        )?,
                    )+
                };

                proof_statement(&mut verifier, secret_vars, public_vars);

                Ok(verifier)
            }

            /// Given a transcript and assignments to public variables, verify a proof in compact format.
            pub fn verify_compact<G: AffineRepr>(
                proof: &CompactProof<G::ScalarField>,
                transcript: &mut Transcript,
                assignments: VerifyAssignments<G>,
            ) -> Result<(), ProofError> {
                let verifier = build_verifier(transcript, assignments)?;

                verifier.verify_compact(proof)
            }

            /// Given a transcript and assignments to public variables, verify a proof in batchable format.
            pub fn verify_batchable<G: AffineRepr>(
                proof: &BatchableProof<G>,
                transcript: &mut Transcript,
                assignments: VerifyAssignments<G>,
            ) -> Result<(), ProofError> {
                let verifier = build_verifier(transcript, assignments)?;

                verifier.verify_batchable(proof)
            }

            /// Verify a batch of proofs, given a batch of transcripts and a batch of assignments.
            pub fn batch_verify<G: AffineRepr>(
                proofs: &[BatchableProof<G>],
                transcripts: Vec<&mut Transcript>,
                assignments: BatchVerifyAssignments<G>,
            ) -> Result<(), ProofError> {
                use self::internal::*;
                use $crate::toolbox::batch_verifier::*;

                let batch_size = proofs.len();

                let mut verifier: BatchVerifier<G, Transcript, &mut Transcript> = BatchVerifier::new(PROOF_LABEL.as_bytes(), batch_size, transcripts)?;

                let secret_vars = SecretVars {
                    $($secret_var: verifier.allocate_scalar(TRANSCRIPT_LABELS.$secret_var.as_bytes()),)+
                };

                let public_vars = PublicVars {
                    $(
                        $instance_var: verifier.allocate_instance_point(
                            TRANSCRIPT_LABELS.$instance_var.as_bytes(),
                            assignments.$instance_var,
                        )?,
                    )+
                    $(
                        $common_var: verifier.allocate_static_point(
                            TRANSCRIPT_LABELS.$common_var.as_bytes(),
                            assignments.$common_var,
                        )?,
                    )+
                };

                proof_statement(&mut verifier, secret_vars, public_vars);

                verifier.verify_batchable(proofs)
            }
            /* 
            #[cfg(all(feature = "bench", test))]
            mod bench {
                use super::*;
                use $crate::rand::thread_rng;

                extern crate test;
                use self::test::Bencher;

                #[bench]
                fn prove(b: &mut Bencher) {
                    let mut rng = thread_rng();

                    struct RandomAssignments {
                        $(pub $secret_var: Scalar,)+
                        $(pub $instance_var: RistrettoPoint,)+
                        $(pub $common_var: RistrettoPoint,)+
                    }

                    let assignments = RandomAssignments {
                        $($secret_var: Scalar::random(&mut rng),)+
                        $($instance_var: RistrettoPoint::random(&mut rng),)+
                        $($common_var: RistrettoPoint::random(&mut rng),)+
                    };

                    // Proving is constant time, so it shouldn't matter
                    // that the relation is not satisfied by random assignments.
                    b.iter(|| {
                        let mut trans = Transcript::new(b"Benchmark");
                        prove_compact(&mut trans, ProveAssignments {
                            $($secret_var: &assignments.$secret_var,)+
                            $($instance_var: &assignments.$instance_var,)+
                            $($common_var: &assignments.$common_var,)+
                        })
                    });
                }

                #[bench]
                fn verify_compact_proof(b: &mut Bencher) {
                    let mut rng = thread_rng();

                    struct RandomAssignments {
                        $(pub $secret_var: Scalar,)+
                        $(pub $instance_var: RistrettoPoint,)+
                        $(pub $common_var: RistrettoPoint,)+
                    }

                    let assignments = RandomAssignments {
                        $($secret_var: Scalar::random(&mut rng),)+
                        $($instance_var: RistrettoPoint::random(&mut rng),)+
                        $($common_var: RistrettoPoint::random(&mut rng),)+
                    };

                    let mut trans = Transcript::new(b"Benchmark");
                    let (proof, points) = prove_compact(&mut trans, ProveAssignments {
                        $($secret_var: &assignments.$secret_var,)+
                        $($instance_var: &assignments.$instance_var,)+
                        $($common_var: &assignments.$common_var,)+
                    });

                    // The proof is well-formed but invalid, so the
                    // compact verification should fall through to the
                    // final check on the recomputed challenge, and
                    // therefore verification failure should not affect
                    // timing.
                    b.iter(|| {
                        let mut trans = Transcript::new(b"Benchmark");
                        verify_compact(&proof, &mut trans, VerifyAssignments {
                            $($instance_var: &points.$instance_var,)+
                            $($common_var: &points.$common_var,)+
                        })
                    });
                }

                #[bench]
                fn verify_batchable_proof(b: &mut Bencher) {
                    let mut rng = thread_rng();

                    struct RandomAssignments {
                        $(pub $secret_var: Scalar,)+
                        $(pub $instance_var: RistrettoPoint,)+
                        $(pub $common_var: RistrettoPoint,)+
                    }

                    let assignments = RandomAssignments {
                        $($secret_var: Scalar::random(&mut rng),)+
                        $($instance_var: RistrettoPoint::random(&mut rng),)+
                        $($common_var: RistrettoPoint::random(&mut rng),)+
                    };

                    let mut trans = Transcript::new(b"Benchmark");
                    let (proof, points) = prove_batchable(&mut trans, ProveAssignments {
                        $($secret_var: &assignments.$secret_var,)+
                        $($instance_var: &assignments.$instance_var,)+
                        $($common_var: &assignments.$common_var,)+
                    });

                    // The proof is well-formed but invalid, so the
                    // batchable verification should perform the check and
                    // see a non-identity point.  So verification failure
                    // should not affect timing.
                    b.iter(|| {
                        let mut trans = Transcript::new(b"Benchmark");
                        verify_batchable(&proof, &mut trans, VerifyAssignments {
                            $($instance_var: &points.$instance_var,)+
                            $($common_var: &points.$common_var,)+
                        })
                    });
                }
            }
            */
        }
    }
}


/// This macro is similar to [`define_proof!`] but is used for
/// cross-domain proofs. The syntax is similar, but the
/// secret variables are allowed to use different domains.
/// The proof statement is  specified as a list of statements, each of which is
/// a linear combination of public points and secret scalars from both domains.
/// 
/// For example, a proof of knowledge of openings to two Pedersen commitments
/// across two groups is specified as:
/// ```rust,ignore
/// define_cross_proof! {
///     pedersen, "Pedersen Proof", (x), (r), (s), (Com1), (Com2), (G1, H1), (G2, H2): 
///     Com1 = (x * G1 + r * H1), Com2 = (x * G2 + s * H2) 
/// } 
/// ```
/// This creates a module `pedersen` with code for proving knowledge of secret `x`
/// that should be the same acrooss groups G1 and G2 in two Pedersen commitments 
/// `Com1` and `Com2` for per-proof public parameters `Com1`, `Com2`, and common
/// parameters `G1`, `H1`, `G2`, and `H2`. The UTF-8 string `"Pedersen Proof"`
/// is added to the transcript as a domain separator.
/// 
/// In general the syntax is
/// ```rust,ignore
/// define_cross_proof!{
///     module_name,   // all generated code for this statement goes here
///     "Proof Label", // a UTF-8 domain separator unique to the statement
///     (x,y,z,...),   // cross-domain secret variable labels (preferably lower-case)
///     (r,s,t,...),   // secret variable labels in G1 (preferably lower-case)
///     (u,v,w,...),   // secret variable labels in G2 (preferably lower-case)
///     (A,B,C,...),   // public per-proof parameter labels in G1 (preferably upper-case)
///     (D,E,F,...),   // public per-proof parameter labels in G2 (preferably upper-case)
///     (G,H,I,...),   // public common parameter labels in G1 (preferably upper-case)
///     (J,K,L,...),   // public common parameter labels in G2 (preferably upper-case)
///     :
///     LHS = (x * A + y * B + z * C + ... ),  // comma-separated statements
///     ...
/// }
/// ```
/// Statements have the form `LHS = (A * x + B * y + C * z + ... )`,
/// where `LHS` is one of the points listed as a public parameter in G1 or G2, and
/// the right-hand side is a sum of public points from `LHS` point's group multiplied by
/// secret scalars from selected domain or cross-domain secret scalars
/// 
/// This macro generates group-agnostic code using generic types for elliptic curve groups 
/// from ark-works. G1 and G2 must implement `AffineRepr` and their `ScalarFields` must not 
/// exceed 256bits so that both could be converted to `BigInt<4>`. `B_x` generic constant is
/// used to specify bitlength of the cross-domain scalars. In order to provide soundness of the
/// proof, the `B_x` must be less than or equal to 64 (bits), `B_c` - challenge bitlength must 
/// not be less then 128 for corresponding 128bit security. `B_f` controls probability of 
/// prover aborting the proof generation, e.g. `B_f=56` means that the prover will abort 
/// with probability 1/2^56.
/// 
/// If the G2 is specified as a [`ark_ed25519::EdwardsAffine`] and `rangeproof` feature is
/// enabled, the macro will also generate code to support range proofs using dalek's [`bulletproofs`],
/// converting G2 points to RistrettoPoints under the hood. In order to request the range proof 
/// for cross-domain scalar `x` name the `LHS` variable as `Com_x` placing prefix `Com` before the
/// varialbe name, if so the `Com_x` must specify Pedersen commitment for `x` in the G2 group.
/// One can also use `Com_x` for G1 group, but in this case the range proof requirement will be
/// ignored because range proving system completely relies on G2 arithmetic. 
/// 
/// If `rangeproof_batchable` feature is enabled, the macro will also generate code to support 
/// batch compression and verification of range proofs using [`bulletproofs`], additionally
/// one must verify that all `Com_x` commitments uses the same basis.
/// 
/// Proof creation is done in constant time.  Proof verification uses
/// variable-time code.
#[macro_export]
macro_rules! define_cross_proof {
    (
        $proof_module_name:ident // Name of the module to create
        ,
        $proof_label_string:expr // A string literal, used as a domain separator
        ,
        ( $($secret_var:ident),+ ) // Common secret variables, sep by commas
        ,
        ( $($secret_var_1:ident),+ ) // Secret variables in G1, sep by commas
        ,
        ( $($secret_var_2:ident),+ ) // Secret variables in G2, sep by commas
        ,
        ( $($instance_var_1:ident),* ) // Public instance variables in G1, separated by commas
        ,
        ( $($instance_var_2:ident),* ) // Public instance variables in G2, separated by commas
        ,
        ( $($common_var_1:ident),* ) // Public common variables in G1, separated by commas
        ,
        ( $($common_var_2:ident),* ) // Public common variables in G2, separated by commas
        :
        // List of statements to prove
        // Format: LHS = ( ... RHS expr ... ),
        $($lhs:ident = $statement:tt),+
    ) => {
        /// An auto-generated Schnorr proof implementation.
        ///
        /// Proofs are created using `prove_compact` or
        /// `prove_batchable`, producing `CompactProof`s or
        /// `BatchableProof`s respectively.  These are verified
        /// using `verify_compact` and `verify_batchable`;
        /// `BatchableProofs` can also be batch-verified using
        /// `batch_verify`, but they have slightly larger proof
        /// sizes compared to `CompactProof`s.
        ///
        /// The internal details of the proof statement are accessible
        /// in the `internals` module.  While this is not necessary
        /// to create and verify proofs, the it can be used with the
        /// lower-level constraint system API to manually combine
        /// statements from different proofs.
        #[allow(non_snake_case)]
        pub mod $proof_module_name {
            use $crate::ark_ec::{AffineRepr, CurveGroup};
            use $crate::ark_ff::{BigInteger, BigInt, PrimeField, UniformRand};
            use $crate::ark_ec::VariableBaseMSM;

            use $crate::toolbox::cross_prover::CrossProver;
            use $crate::toolbox::cross_verifier::CrossVerifier;
            use $crate::toolbox::{Point, Scalar};
            use ark_ed25519::EdwardsAffine;

            pub use $crate::merlin::Transcript;
            pub use $crate::{CompactCrossProof, ProofError};

            /// The generated [`internal`] module contains lower-level
            /// functions at the level of the Schnorr constraint
            /// system API.
            pub mod internal {
                use $crate::toolbox::SchnorrCS;

                /// The proof label committed to the transcript as a domain separator.
                pub const PROOF_LABEL: &'static str = $proof_label_string;

                /// A container type that holds transcript labels for secret variables.
                pub struct TranscriptLabels {
                    $( pub $secret_var: &'static str, )+
                    $( pub $secret_var_1: &'static str, )+
                    $( pub $secret_var_2: &'static str, )+
                    $( pub $instance_var_1: &'static str, )+
                    $( pub $instance_var_2: &'static str, )+
                    $( pub $common_var_1: &'static str, )+
                    $( pub $common_var_2: &'static str, )+
                }

                /// The transcript labels used for each secret variable.
                pub const TRANSCRIPT_LABELS: TranscriptLabels = TranscriptLabels {
                    $( $secret_var: stringify!($secret_var), )+
                    $( $secret_var_1: stringify!($secret_var_1), )+
                    $( $secret_var_2: stringify!($secret_var_2), )+
                    $( $instance_var_1: stringify!($instance_var_1), )+
                    $( $instance_var_2: stringify!($instance_var_2), )+
                    $( $common_var_1: stringify!($common_var_1), )+
                    $( $common_var_2: stringify!($common_var_2), )+
                };

                /// A container type that simulates named parameters for [`proof_statement`].
                #[derive(Copy, Clone)]
                pub struct SecretVars<CS: SchnorrCS> {
                    $( pub $secret_var: CS::ScalarVar, )+
                    $( pub $secret_var_1: CS::ScalarVar, )+
                    $( pub $secret_var_2: CS::ScalarVar, )+
                }

                /// A container type that simulates named parameters for [`proof_statement`].
                #[derive(Copy, Clone)]
                pub struct PublicVars<CS: SchnorrCS> {
                    $( pub $instance_var_1: CS::PointVar, )+
                    $( pub $instance_var_2: CS::PointVar, )+
                    $( pub $common_var_1: CS::PointVar, )+
                    $( pub $common_var_2: CS::PointVar, )+
                }

                /// The underlying proof statement generated by the macro invocation.
                ///
                /// This function exists separately from the proving
                /// and verification functions to allow composition of
                /// different proof statements with common variable
                /// assignments.
                pub fn proof_statement<CS: SchnorrCS>(
                    cs: &mut CS,
                    secrets: SecretVars<CS>,
                    publics: PublicVars<CS>,
                ) {
                    $(
                        let c = cs.constrain(
                            publics.$lhs,
                            __compute_formula_constraint!( (publics, secrets) $statement ),
                        );
                        if stringify!($lhs).starts_with("Com") {
                            cs.require_range_proof(c);
                        }
                    )+
                }
            }

            /// Named parameters for [`prove_compact`] and [`prove_batchable`].
            #[derive(Copy, Clone)]
            pub struct ProveAssignments<'a, G1: AffineRepr, G2: AffineRepr> {
                $(pub $secret_var: &'a BigInt<4>,)+
                $(pub $secret_var_1: &'a G1::ScalarField,)+
                $(pub $secret_var_2: &'a G2::ScalarField,)+
                $(pub $instance_var_1: &'a G1,)+
                $(pub $instance_var_2: &'a G2,)+
                $(pub $common_var_1: &'a G1,)+
                $(pub $common_var_2: &'a G2,)+
            }

            /// Named parameters for [`verify_compact`] and [`verify_batchable`].
            #[derive(Copy, Clone)]
            pub struct VerifyAssignments<'a, G1: AffineRepr, G2: AffineRepr> {
                $(pub $instance_var_1: &'a G1,)+
                $(pub $instance_var_2: &'a G2,)+
                $(pub $common_var_1: &'a G1,)+
                $(pub $common_var_2: &'a G2,)+
            }

            /// Point encodings computed during proving and returned to allow reuse.
            ///
            /// This is used to allow a prover to avoid having to
            /// re-compress points used in the proof that may be
            /// necessary to supply to the verifier.
            #[derive(Copy, Clone)]
            pub struct CompressedPoints<G1: AffineRepr, G2: AffineRepr> {
                $(pub $instance_var_1: G1,)+
                $(pub $instance_var_2: G2,)+
                $(pub $common_var_1: G1,)+
                $(pub $common_var_2: G2,)+
            }

            /* 
            /// Named parameters for [`batch_verify`].
            #[derive(Clone)]
            pub struct BatchVerifyAssignments<G: AffineRepr> {
                $(pub $instance_var: Vec<G>,)+
                $(pub $common_var: G,)+
            }
            */
            fn build_prover<'a, G1: AffineRepr, G2: AffineRepr, const B_x: usize, const B_c: usize, const B_f: usize> (
                transcript: &'a mut Transcript,
                assignments: ProveAssignments<G1, G2>,
            ) -> Result<(CrossProver<G1, G2, Transcript, &'a mut Transcript, B_x, B_c, B_f>, CompressedPoints<G1, G2>), ProofError>
            where 
                BigInt<4>: From<<G1::ScalarField as PrimeField>::BigInt>, 
                BigInt<4>: From<<G2::ScalarField as PrimeField>::BigInt>,
                <G1::ScalarField as PrimeField>::BigInt: From<BigInt<4>>,
                <G2::ScalarField as PrimeField>::BigInt: From<BigInt<4>>,
            {
                use self::internal::*;
                use $crate::toolbox::cross_prover::*;
                use $crate::toolbox::PointVar;
                
                let mut prover: CrossProver<G1, G2, Transcript, _, B_x, B_c, B_f> 
                    = CrossProver::new(PROOF_LABEL.as_bytes(), transcript);

                let secret_vars = SecretVars {
                    $(
                        $secret_var: prover.allocate_scalar(
                            TRANSCRIPT_LABELS.$secret_var.as_bytes(),
                            Scalar::Cross(*assignments.$secret_var),
                        )?,
                    )+
                    $(
                        $secret_var_1: prover.allocate_scalar(
                            TRANSCRIPT_LABELS.$secret_var_1.as_bytes(),
                            Scalar::F1(*assignments.$secret_var_1),
                        )?,
                    )+
                    $(
                        $secret_var_2: prover.allocate_scalar(
                            TRANSCRIPT_LABELS.$secret_var_2.as_bytes(),
                            Scalar::F2(*assignments.$secret_var_2),
                        )?,
                    )+
                };

                struct VarPointPairs<G1: AffineRepr, G2: AffineRepr> {
                    $( pub $instance_var_1: (PointVar, G1), )+
                    $( pub $instance_var_2: (PointVar, G2), )+
                    $( pub $common_var_1: (PointVar, G1), )+
                    $( pub $common_var_2: (PointVar, G2), )+
                }

                let pairs = VarPointPairs {
                    $(
                        $instance_var_1: (prover.allocate_point(
                            TRANSCRIPT_LABELS.$instance_var_1.as_bytes(),
                            Point::G1(*assignments.$instance_var_1),
                        ), *assignments.$instance_var_1),
                    )+
                    $(
                        $instance_var_2: (prover.allocate_point(
                            TRANSCRIPT_LABELS.$instance_var_2.as_bytes(),
                            Point::G2(*assignments.$instance_var_2),
                        ), *assignments.$instance_var_2),
                    )+
                    $(
                        $common_var_1: (prover.allocate_point(
                            TRANSCRIPT_LABELS.$common_var_1.as_bytes(),
                            Point::G1(*assignments.$common_var_1),
                        ), *assignments.$common_var_1),
                    )+
                    $(
                        $common_var_2: (prover.allocate_point(
                            TRANSCRIPT_LABELS.$common_var_2.as_bytes(),
                            Point::G2(*assignments.$common_var_2),
                        ), *assignments.$common_var_2),  
                    )+
                };

                // XXX return compressed points
                let public_vars = PublicVars {
                    $($instance_var_1: pairs.$instance_var_1.0,)+
                    $($instance_var_2: pairs.$instance_var_2.0,)+
                    $($common_var_1: pairs.$common_var_1.0,)+
                    $($common_var_2: pairs.$common_var_2.0,)+
                };

                let compressed = CompressedPoints {
                    $($instance_var_1: pairs.$instance_var_1.1,)+
                    $($instance_var_2: pairs.$instance_var_2.1,)+
                    $($common_var_1: pairs.$common_var_1.1,)+
                    $($common_var_2: pairs.$common_var_2.1,)+
                };

                proof_statement(&mut prover, secret_vars, public_vars);

                Ok((prover, compressed))
            }

            /// Given a transcript and assignments to secret and public variables, produce a proof in compact format.
            pub fn prove_compact<'a, G1: AffineRepr, G2: AffineRepr, const B_x: usize, const B_c: usize, const B_f: usize>(
                transcript: &mut Transcript,
                assignments: ProveAssignments<G1, G2>,
            ) -> Result<(CompactCrossProof<G1::ScalarField, G2::ScalarField>, CompressedPoints<G1, G2>), ProofError>
                where BigInt<4>: From<<G1::ScalarField as PrimeField>::BigInt>, 
                    BigInt<4>: From<<G2::ScalarField as PrimeField>::BigInt>,
                    <G1::ScalarField as PrimeField>::BigInt: From<BigInt<4>>,
                    <G2::ScalarField as PrimeField>::BigInt: From<BigInt<4>>, {
                let (prover, compressed) = build_prover::<G1, G2, B_x, B_c, B_f>(transcript, assignments)?;

                Ok((prover.prove_compact()?, compressed))
            }

            
            #[cfg(feature = "rangeproof")]
            /// Given a transcript and assignments to secret and public variables, produce a compact cross proof with range proofs
            pub fn prove_cross<'a, G1: AffineRepr, const B_x: usize, const B_c: usize, const B_f: usize>(
                transcript: &mut Transcript,
                assignments: ProveAssignments<G1, EdwardsAffine>,
            ) -> Result<(CompactCrossProof<G1::ScalarField, <EdwardsAffine as AffineRepr>::ScalarField>, CompressedPoints<G1, EdwardsAffine>), ProofError>
                where BigInt<4>: From<<G1::ScalarField as PrimeField>::BigInt>, 
                    <G1::ScalarField as PrimeField>::BigInt: From<BigInt<4>> {
                let (prover, compressed) = build_prover::<G1, EdwardsAffine, B_x, B_c, B_f>(transcript, assignments)?;

                Ok((prover.prove_cross()?, compressed))
            }

            /*
            /// Given a transcript and assignments to secret and public variables, produce a proof in batchable format.
            pub fn prove_batchable<G: AffineRepr>(
                transcript: &mut Transcript,
                assignments: ProveAssignments<G>,
            ) -> (BatchableProof<G>, CompressedPoints<G>) {
                let (prover, compressed) = build_prover(transcript, assignments);

                (prover.prove_batchable(), compressed)
            }
            */
            fn build_verifier<'a, G1: AffineRepr, G2: AffineRepr, const B_x: usize, const B_c: usize, const B_f: usize>(
                transcript: &'a mut Transcript,
                assignments: VerifyAssignments<G1, G2>,
            ) -> Result<CrossVerifier<G1, G2, Transcript, &'a mut Transcript, B_x, B_c, B_f>, ProofError>
                where BigInt<4>: From<<G1::ScalarField as PrimeField>::BigInt>, 
                    BigInt<4>: From<<G2::ScalarField as PrimeField>::BigInt>,
                    <G1::ScalarField as PrimeField>::BigInt: From<BigInt<4>>,
                    <G2::ScalarField as PrimeField>::BigInt: From<BigInt<4>>, {
                use self::internal::*;
                use $crate::toolbox::cross_verifier::*;

                let mut verifier: CrossVerifier<G1, G2, Transcript, _, B_x, B_c, B_f> 
                    = CrossVerifier::new(PROOF_LABEL.as_bytes(), transcript);

                let secret_vars = SecretVars {
                    $($secret_var: verifier.allocate_scalar(TRANSCRIPT_LABELS.$secret_var.as_bytes()),)+
                    $($secret_var_1: verifier.allocate_scalar(TRANSCRIPT_LABELS.$secret_var_1.as_bytes()),)+
                    $($secret_var_2: verifier.allocate_scalar(TRANSCRIPT_LABELS.$secret_var_2.as_bytes()),)+
                };

                let public_vars = PublicVars {
                    $(
                        $instance_var_1: verifier.allocate_point(
                            TRANSCRIPT_LABELS.$instance_var_1.as_bytes(),
                            Point::G1(*assignments.$instance_var_1),
                        )?,
                    )+
                    $(
                        $instance_var_2: verifier.allocate_point(
                            TRANSCRIPT_LABELS.$instance_var_2.as_bytes(),
                            Point::G2(*assignments.$instance_var_2),
                        )?,
                    )+
                    $(
                        $common_var_1: verifier.allocate_point(
                            TRANSCRIPT_LABELS.$common_var_1.as_bytes(),
                            Point::G1(*assignments.$common_var_1),
                        )?,
                    )+
                    $(
                        $common_var_2: verifier.allocate_point(
                            TRANSCRIPT_LABELS.$common_var_2.as_bytes(),
                            Point::G2(*assignments.$common_var_2),
                        )?,
                    )+
                };

                proof_statement(&mut verifier, secret_vars, public_vars);

                Ok(verifier)
            }

            /// Given a transcript and assignments to public variables, verify a proof in compact format.
            pub fn verify_compact<G1: AffineRepr, G2: AffineRepr, const B_x: usize, const B_c: usize, const B_f: usize>(
                proof: &CompactCrossProof<G1::ScalarField, G2::ScalarField>,
                transcript: &mut Transcript,
                assignments: VerifyAssignments<G1, G2>,
            ) -> Result<(), ProofError> 
                where BigInt<4>: From<<G1::ScalarField as PrimeField>::BigInt>, 
                    BigInt<4>: From<<G2::ScalarField as PrimeField>::BigInt>,
                    <G1::ScalarField as PrimeField>::BigInt: From<BigInt<4>>,
                    <G2::ScalarField as PrimeField>::BigInt: From<BigInt<4>>, {
                let verifier = build_verifier::<G1, G2, B_x, B_c, B_f>(transcript, assignments)?;

                verifier.verify_compact(proof)
            }

            #[cfg(feature = "rangeproof")]
            /// Verify a compact cross proof with range proofs
            pub fn verify_cross<G1: AffineRepr, const B_x: usize, const B_c: usize, const B_f: usize>(
                proof: &CompactCrossProof<G1::ScalarField, <EdwardsAffine as AffineRepr>::ScalarField>,
                transcript: &mut Transcript,
                assignments: VerifyAssignments<G1, EdwardsAffine>,
            ) -> Result<(), ProofError> 
                where BigInt<4>: From<<G1::ScalarField as PrimeField>::BigInt>, 
                    <G1::ScalarField as PrimeField>::BigInt: From<BigInt<4>>, {
                let verifier = build_verifier::<G1, EdwardsAffine, B_x, B_c, B_f>(transcript, assignments)?;

                verifier.verify_cross(proof)
            }

            /*
            /// Given a transcript and assignments to public variables, verify a proof in batchable format.
            pub fn verify_batchable<G: AffineRepr>(
                proof: &BatchableProof<G>,
                transcript: &mut Transcript,
                assignments: VerifyAssignments<G>,
            ) -> Result<(), ProofError> {
                let verifier = build_verifier(transcript, assignments)?;

                verifier.verify_batchable(proof)
            }

            /// Verify a batch of proofs, given a batch of transcripts and a batch of assignments.
            pub fn batch_verify<G: AffineRepr>(
                proofs: &[BatchableProof<G>],
                transcripts: Vec<&mut Transcript>,
                assignments: BatchVerifyAssignments<G>,
            ) -> Result<(), ProofError> {
                use self::internal::*;
                use $crate::toolbox::batch_verifier::*;

                let batch_size = proofs.len();

                let mut verifier: BatchVerifier<G, Transcript, &mut Transcript> = BatchVerifier::new(PROOF_LABEL.as_bytes(), batch_size, transcripts)?;

                let secret_vars = SecretVars {
                    $($secret_var: verifier.allocate_scalar(TRANSCRIPT_LABELS.$secret_var.as_bytes()),)+
                };

                let public_vars = PublicVars {
                    $(
                        $instance_var: verifier.allocate_instance_point(
                            TRANSCRIPT_LABELS.$instance_var.as_bytes(),
                            assignments.$instance_var,
                        )?,
                    )+
                    $(
                        $common_var: verifier.allocate_static_point(
                            TRANSCRIPT_LABELS.$common_var.as_bytes(),
                            assignments.$common_var,
                        )?,
                    )+
                };

                proof_statement(&mut verifier, secret_vars, public_vars);

                verifier.verify_batchable(proofs)
            }*/

        }
    }
}
