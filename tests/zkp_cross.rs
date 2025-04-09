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

use std::{convert::TryFrom, sync::Arc};

use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{BigInt, Field, UniformRand};
use ark_serialize::CanonicalDeserialize;
use ark_test_curves::secp256k1::{Fr as F1, G1Affine};
use ark_ed25519::{EdwardsAffine as G2Affine, Fr as F2};
use curve25519_dalek::RistrettoPoint;
use rand::thread_rng;


use zkp::{BatchableProof, CompactCrossProof, CompactProof, Transcript};

define_cross_proof! {dleq, "Com(x, r1), Com(x, r2) Proof", 
    (x), 
    (r1), 
    (r2), 
    (A), 
    (Com_A), 
    (G_1, H_1), 
    (G_2, H_2) : 
    A = (x * G_1 + r1 * H_1), Com_A = (x * G_2 + r2 * H_2) }

#[test]
fn create_and_verify_compact() {
    let G_1 = G1Affine::generator();
    let H_1 = G1Affine::rand(&mut thread_rng());
    let G_2 = G2Affine::generator();
    let H_2 = G2Affine::rand(&mut thread_rng());
    // Prover's scope
    let (proof, points) = {
        let x = BigInt::from(rand::random::<u64>());
        let r1 = F1::ONE/F1::from(rand::random::<u64>());
        let r2 = F2::ONE/F2::from(rand::random::<u64>());
        let A = (G_1 * F1::from(x) + H_1 * r1).into_affine();
        let Com_A = (G_2 * F2::from(x) + H_2 * r2).into_affine();

        let mut transcript = Transcript::new(b"discrete log equality among groups");
        dleq::prove_cross::<_, 64, 128, 40>(
            &mut transcript,
            dleq::ProveAssignments {
                x: &x,
                r1: &r1,
                r2: &r2,
                A: &A,
                Com_A: &Com_A,
                G_1: &G_1,
                H_1: &H_1,
                G_2: &G_2,
                H_2: &H_2
            },
        ).unwrap()
    };

    let proof_bytes = proof.to_bytes().unwrap();
    println!("{:?}", proof_bytes.len());
    let parsed_proof: dleq::CompactCrossProof<F1, F2> = CompactCrossProof::from_bytes(&proof_bytes).unwrap();

    // Verifier logic
    let mut transcript = Transcript::new(b"discrete log equality among groups");
    assert!(dleq::verify_cross::<_, 64, 128, 40>(
        &parsed_proof,
        &mut transcript,
        dleq::VerifyAssignments {
            A: &points.A,
            Com_A: &points.Com_A,
            G_1: &G_1,
            H_1: &H_1,
            G_2: &G_2,
            H_2: &H_2
        },
    )
    .is_ok());
}

/* 

#[test]
fn create_and_verify_batchable() {
    // identical to above but with batchable proofs
    let G = G1Affine::generator();
    let H = G1Affine::rand(&mut thread_rng());

    // Prover's scope
    let (proof, points) = {
        let x = F1::from(rand::random::<u64>());
        let r1 = F1::from(rand::random::<u64>());
        let r2 = F1::from(rand::random::<u64>());
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
            
            let x = F1::from(rand::random::<u64>());
            let r1 = F1::from(rand::random::<u64>());
            let r2 = F1::from(rand::random::<u64>());
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

*/