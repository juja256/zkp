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
use std::convert::TryInto;

use self::sha2::Sha512;

use ark_ec::twisted_edwards::TECurveConfig;
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{BigInteger, Field, MontConfig, Zero};
use ark_ff::{BigInt, PrimeField, UniformRand, One};
use ark_serialize::CanonicalDeserialize;
use curve25519_dalek::{constants as dalek_constants, edwards};
use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use group::Group;
use zkp::toolbox::dalek_ark::ristretto255_to_ark;
use zkp::toolbox::Scalar;

use ark_ed25519::EdwardsAffine as ArkEdwardsAffine;
use ark_secq256k1::Affine as G2Affine;
use ark_secq256k1::Fr as F2;
//use ark_test_curves::secp256k1::{Fr as F2, G1Affine as G2Affine};

use rand::thread_rng;
use zkp::toolbox::cross_transcript::TranscriptProtocol;
use zkp::toolbox::Point;
use zkp::toolbox::{cross_prover::CrossProver, cross_verifier::CrossVerifier, SchnorrCS};
use zkp::CompactCrossProof;
use zkp::Transcript;
use ark_ed25519::{EdwardsAffine as G1Affine, Fr as F1, Fq, FqConfig, EdwardsConfig};


fn dleq_statement<CS: SchnorrCS>(
    cs: &mut CS,
    x: CS::ScalarVar,
    r1: CS::ScalarVar,
    r2: CS::ScalarVar,
    Com1: CS::PointVar,
    Com2: CS::PointVar,
    G1: CS::PointVar,
    H1: CS::PointVar,
    G2: CS::PointVar,
    H2: CS::PointVar,
) {
    cs.constrain(Com1, vec![(x, G1), (r1, H1)]);
    cs.constrain(Com2, vec![(x, G2), (r2, H2)]);
}

#[test]
fn cross_zkp() {
    let G1 = G1Affine::generator();
    let H1 = G1Affine::rand(&mut thread_rng());
    let G2 = G2Affine::rand(&mut thread_rng());
    let H2 = G2Affine::rand(&mut thread_rng());

    let x = BigInt::<4>::from(1u64 << 63);
    let r1 = F1::rand(&mut thread_rng());
    let r2 = F2::rand(&mut thread_rng());

    let Com1 = Point::G1((G1 * F1::from_bigint(x).unwrap() + H1 * r1).into_affine());
    let Com2 = Point::G2((G2 * F2::from_bigint(x).unwrap() + H2 * r2).into_affine());

    let proof = {
        let mut transcript = Transcript::new(b"DLEQTest");
        let mut prover: CrossProver<G1Affine, G2Affine, Transcript, _, 64, 128, 32> =
            CrossProver::new(b"DLEQProof", &mut transcript);

        // XXX committing var names to transcript forces ordering (?)
        let var_x = prover.allocate_scalar(b"x", Scalar::Cross(x)).unwrap();
        let var_r1 = prover.allocate_scalar(b"r1", Scalar::F1(r1)).unwrap();
        let var_r2 = prover.allocate_scalar(b"r2", Scalar::F2(r2)).unwrap();
        let var_G1 = prover.allocate_point(b"G1", Point::G1(G1));
        let var_G2 = prover.allocate_point(b"G2", Point::G2(G2));
        let var_H1 = prover.allocate_point(b"H1", Point::G1(H1));
        let var_H2 = prover.allocate_point(b"H2", Point::G2(H2));
        let var_Com1 = prover.allocate_point(b"Com1", Com1);
        let var_Com2 = prover.allocate_point(b"Com2", Com2);

        dleq_statement(
            &mut prover,
            var_x,
            var_r1,
            var_r2,
            var_Com1,
            var_Com2,
            var_G1,
            var_H1,
            var_G2,
            var_H2,
        );

        prover.prove_compact().unwrap()
    };
    for (i, response) in proof.responses.iter().enumerate() {
        println!("proof response {}: {:?}", i, response.into_bigint());
    }
    let proof_bytes = proof.to_bytes().unwrap();
    println!("{:?}\n{:?}", proof.responses, proof_bytes);
    let parsed_proof: CompactCrossProof<_, _> =
        CompactCrossProof::<F1, F2>::from_bytes(&proof_bytes).unwrap();

    let mut transcript = Transcript::new(b"DLEQTest");
    let mut verifier: CrossVerifier<G1Affine, G2Affine, Transcript, _, 64, 128, 32> =
        CrossVerifier::new(b"DLEQProof", &mut transcript);
    // println!("A={:?}", A); // Debug trait is not implemented for Point
    let var_x = verifier.allocate_scalar(b"x");
    let var_r1 = verifier.allocate_scalar(b"r1");
    let var_r2 = verifier.allocate_scalar(b"r2");
    let var_G1 = verifier.allocate_point(b"G1", Point::G1(G1)).unwrap();
    let var_G2 = verifier.allocate_point(b"G2", Point::G2(G2)).unwrap();
    let var_H1 = verifier.allocate_point(b"H1", Point::G1(H1)).unwrap();
    let var_H2 = verifier.allocate_point(b"H2", Point::G2(H2)).unwrap();
    let var_Com1 = verifier.allocate_point(b"Com1", Com1).unwrap();
    let var_Com2 = verifier.allocate_point(b"Com2", Com2).unwrap();
    dleq_statement(
        &mut verifier,
        var_x,
        var_r1,
        var_r2,
        var_Com1,
        var_Com2,
        var_G1,
        var_H1,
        var_G2,
        var_H2,
    );


    verifier.verify_compact(&parsed_proof).unwrap();
}
/*
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

*/
