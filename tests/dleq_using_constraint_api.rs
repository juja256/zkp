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

extern crate bincode;
extern crate curve25519_dalek;
extern crate serde;
extern crate sha2;
extern crate zkp;

use std::borrow::BorrowMut;

use self::sha2::Sha512;

use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::UniformRand;
use curve25519_dalek::constants as dalek_constants;
use curve25519_dalek::ristretto::RistrettoPoint;
use curve25519_dalek::scalar::Scalar;

use ark_test_curves::secp256k1::{G1Affine, Fr};

use rand::thread_rng;
use zkp::toolbox::standard_transcript::TranscriptProtocol;
use zkp::toolbox::{batch_verifier::BatchVerifier, prover::Prover, verifier::Verifier, SchnorrCS};
use zkp::Transcript;

fn dleq_statement<CS: SchnorrCS>(
    cs: &mut CS,
    x: CS::ScalarVar,
    A: CS::PointVar,
    G: CS::PointVar,
    B: CS::PointVar,
    H: CS::PointVar,
) {
    cs.constrain(A, vec![(x, B)]);
    cs.constrain(G, vec![(x, H)]);
}

#[test]
fn create_and_verify_compact_dleq() {
    let B = G1Affine::generator();
    let H = G1Affine::rand(&mut thread_rng());

    let (proof, cmpr_A, cmpr_G) = {
        let x = Fr::from(89327492234u64);

        let A = (B * x).into_affine();
        let G = (H * x).into_affine();

        let mut transcript = Transcript::new(b"DLEQTest");
        let mut prover: Prover<G1Affine, Transcript, _> = Prover::new(b"DLEQProof", &mut transcript);

        // XXX committing var names to transcript forces ordering (?)
        let var_x = prover.allocate_scalar(b"x", x);
        let (var_B, _) = prover.allocate_point(b"B", B);
        let (var_H, _) = prover.allocate_point(b"H", H);
        let (var_A, cmpr_A) = prover.allocate_point(b"A", A);
        let (var_G, cmpr_G) = prover.allocate_point(b"G", G);

        dleq_statement(&mut prover, var_x, var_A, var_G, var_B, var_H);

        (prover.prove_compact(), cmpr_A, cmpr_G)
    };

    let mut transcript = Transcript::new(b"DLEQTest");
    let mut verifier: Verifier<G1Affine, Transcript, _> = Verifier::new(b"DLEQProof", &mut transcript);

    let var_x = verifier.allocate_scalar(b"x");
    let var_B = verifier.allocate_point(b"B", B).unwrap();
    let var_H = verifier.allocate_point(b"H", H).unwrap();
    let var_A = verifier.allocate_point(b"A", cmpr_A).unwrap();
    let var_G = verifier.allocate_point(b"G", cmpr_G).unwrap();

    dleq_statement(&mut verifier, var_x, var_A, var_G, var_B, var_H);

    assert!(verifier.verify_compact(&proof).is_ok());
}

#[test]
fn create_and_verify_batchable_dleq() {
    let B = G1Affine::generator();
    let H = G1Affine::rand(&mut thread_rng());

    let (proof, cmpr_A, cmpr_G) = {
        let x = Fr::from(89327492234u64);

        let A = (B * x).into_affine();
        let G = (H * x).into_affine();

        let mut transcript = Transcript::new(b"DLEQTest");
        let mut prover: Prover<G1Affine, Transcript, _> = Prover::new(b"DLEQProof", &mut transcript);

        // XXX committing var names to transcript forces ordering (?)
        let var_x = prover.allocate_scalar(b"x", x);
        let (var_B, _) = prover.allocate_point(b"B", B);
        let (var_H, _) = prover.allocate_point(b"H", H);
        let (var_A, cmpr_A) = prover.allocate_point(b"A", A);
        let (var_G, cmpr_G) = prover.allocate_point(b"G", G);

        dleq_statement(&mut prover, var_x, var_A, var_G, var_B, var_H);

        (prover.prove_batchable(), cmpr_A, cmpr_G)
    };

    let mut transcript = Transcript::new(b"DLEQTest");
    let mut verifier: Verifier<G1Affine, Transcript, _> = Verifier::new(b"DLEQProof", &mut transcript);

    let var_x = verifier.allocate_scalar(b"x");
    let var_B = verifier.allocate_point(b"B", B).unwrap();
    let var_H = verifier.allocate_point(b"H", H).unwrap();
    let var_A = verifier.allocate_point(b"A", cmpr_A).unwrap();
    let var_G = verifier.allocate_point(b"G", cmpr_G).unwrap();

    dleq_statement(&mut verifier, var_x, var_A, var_G, var_B, var_H);

    assert!(verifier.verify_batchable(&proof).is_ok());
}


#[test]
fn create_and_batch_verify_batchable_dleq() {
    let B = G1Affine::generator();
    let H = G1Affine::rand(&mut thread_rng());

    let batch_size = 16;

    let mut proofs = Vec::new();
    let mut cmpr_As = Vec::new();
    let mut cmpr_Gs = Vec::new();

    for j in 0..batch_size {
        let (proof, cmpr_A, cmpr_G) = {
            let x = Fr::from(89327492234u64);

            let A = (B * x).into_affine();
            let G = (H * x).into_affine();

            let mut transcript = Transcript::new(b"DLEQBatchTest");
            let mut prover: Prover<G1Affine, Transcript, _> = Prover::new(b"DLEQProof", &mut transcript);

            // XXX committing var names to transcript forces ordering (?)
            let var_x = prover.allocate_scalar(b"x", x);
            let (var_B, _) = prover.allocate_point(b"B", B);
            let (var_H, _) = prover.allocate_point(b"H", H);
            let (var_A, cmpr_A) = prover.allocate_point(b"A", A);
            let (var_G, cmpr_G) = prover.allocate_point(b"G", G);

            dleq_statement(&mut prover, var_x, var_A, var_G, var_B, var_H);

            (prover.prove_batchable(), cmpr_A, cmpr_G)
        };
        proofs.push(proof);
        cmpr_As.push(cmpr_A);
        cmpr_Gs.push(cmpr_G);
    }

    let mut transcripts = vec![Transcript::new(b"DLEQBatchTest"); batch_size];
    let transcript_refs = transcripts.iter_mut().collect();
    let mut verifier: BatchVerifier<G1Affine, Transcript, &mut Transcript> = BatchVerifier::new(b"DLEQProof", batch_size, transcript_refs).unwrap();

    let var_x = verifier.allocate_scalar(b"x");
    let var_B = verifier.allocate_static_point(b"B", B).unwrap();
    let var_H = verifier.allocate_static_point(b"H", H).unwrap();
    let var_A = verifier.allocate_instance_point(b"A", cmpr_As).unwrap();
    let var_G = verifier.allocate_instance_point(b"G", cmpr_Gs).unwrap();

    dleq_statement(&mut verifier, var_x, var_A, var_G, var_B, var_H);

    assert!(verifier.verify_batchable(&proofs).is_ok());
}
    
