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
#![allow(non_snake_case)]


#[macro_use]
extern crate zkp;

use std::convert::TryFrom;

use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{Field, UniformRand};
use ark_serialize::CanonicalDeserialize;
use ark_test_curves::secp256k1::{Fr, G1Affine};
use ark_ed25519::EdwardsAffine as ArkEdwardsAffine;
use curve25519_dalek::RistrettoPoint;
use rand::thread_rng;


use zkp::{BatchableProof, CompactProof, Transcript};

fn ristretto_to_ark(point: RistrettoPoint) -> Option<ArkEdwardsAffine> {
    // Step 1: Compress the RistrettoPoint to get its Edwards representation
    let compressed = point.compress();
    let bytes: Vec<u8> = compressed.as_bytes().to_vec();
    ark_ed25519::EdwardsAffine::deserialize_compressed(&mut std::io::Cursor::new(bytes)).ok()
}

define_proof! {dleq, "Com(x, r1), Com(x, r2) Proof", (x, r1, r2), (A, B), (G, H) : A = (x * G + r1 * H), B = (x * G + r2 * H) }

#[test]
fn create_and_verify_compact() {
    let G = G1Affine::generator();
    let H = G1Affine::rand(&mut thread_rng());
    // Prover's scope
    let (proof, points) = {
        let x = Fr::from(rand::random::<u64>());
        let r1 = Fr::from(rand::random::<u64>());
        let r2 = Fr::from(rand::random::<u64>());
        let A = (G * x + H * r1).into_affine();
        let B = (G * x + H * r2).into_affine();

        let mut transcript = Transcript::new(b"DLEQTest");
        dleq::prove_compact(
            &mut transcript,
            dleq::ProveAssignments {
                x: &x,
                r1: &r1,
                r2: &r2,
                A: &A,
                B: &B,
                G: &G,
                H: &H,
            },
        )
    };

    let proof_bytes = proof.to_bytes().unwrap();
    println!("{:?}", proof_bytes);
    let parsed_proof: dleq::CompactProof<_> = CompactProof::from_bytes(&proof_bytes).unwrap();

    // Verifier logic
    let mut transcript = Transcript::new(b"DLEQTest");
    assert!(dleq::verify_compact(
        &parsed_proof,
        &mut transcript,
        dleq::VerifyAssignments {
            A: &points.A,
            B: &points.B,
            G: &G,
            H: &H,
        },
    )
    .is_ok());
}


#[test]
fn create_and_verify_batchable() {
    // identical to above but with batchable proofs
    let G = G1Affine::generator();
    let H = G1Affine::rand(&mut thread_rng());

    // Prover's scope
    let (proof, points) = {
        let x = Fr::from(rand::random::<u64>());
        let r1 = Fr::from(rand::random::<u64>());
        let r2 = Fr::from(rand::random::<u64>());
        let A = (G * x + H * r1).into_affine();
        let B = (G * x + H * r2).into_affine();

        let mut transcript = Transcript::new(b"DLEQTest");
        dleq::prove_batchable(
            &mut transcript,
            dleq::ProveAssignments {
                x: &x,
                r1: &r1,
                r2: &r2,
                A: &A,
                B: &B,
                G: &G,
                H: &H,
            },
        )
    };
    
    let proof_bytes = proof.to_bytes().unwrap();
    println!("{:?}\n{:?}\n{:?}", proof.commitments, proof.responses, proof_bytes);
    let parsed_proof: dleq::BatchableProof<_> = BatchableProof::from_bytes(&proof_bytes).unwrap();

    // Verifier logic
    let mut transcript = Transcript::new(b"DLEQTest");
    assert!(dleq::verify_batchable(
        &parsed_proof,
        &mut transcript,
        dleq::VerifyAssignments {
            A: &points.A,
            B: &points.B,
            G: &G,
            H: &H,
        },
    )
    .is_ok());
}

#[test]
fn create_batch_and_batch_verify() {
    let messages = [
        "One message",
        "Another message",
        "A third message",
        "A fourth message",
    ];

    let G = G1Affine::generator();
    let H = G1Affine::rand(&mut thread_rng());

    // Prover's scope
    let (proofs, pubkeys, vrf_outputs) = {
        let mut proofs = vec![];
        let mut pubkeys = vec![];
        let mut vrf_outputs = vec![];

        for (i, message) in messages.iter().enumerate() {
            
            let x = Fr::from(rand::random::<u64>());
            let r1 = Fr::from(rand::random::<u64>());
            let r2 = Fr::from(rand::random::<u64>());
            let A = (G * x + H * r1).into_affine();
            let B = (G * x + H * r2).into_affine();

            let mut transcript = Transcript::new(b"DLEQTest");
            let (proof, points) = dleq::prove_batchable(
                &mut transcript,
                dleq::ProveAssignments {
                    x: &x,
                    r1: &r1,
                    r2: &r2,
                    A: &A,
                    B: &B,
                    G: &G,
                    H: &H,
                },
            );

            proofs.push(proof);
            pubkeys.push(points.A);
            vrf_outputs.push(points.B);
        }

        (proofs, pubkeys, vrf_outputs)
    };

    // Verifier logic
    let mut transcripts = vec![Transcript::new(b"DLEQTest"); messages.len()];

    assert!(dleq::batch_verify(
        &proofs,
        transcripts.iter_mut().collect(),
        dleq::BatchVerifyAssignments {
            A: pubkeys,
            B: vrf_outputs,
            H: H,
            G: G,
        },
    )
    .is_ok());
}

