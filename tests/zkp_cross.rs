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

use std::{cmp::min, convert::TryFrom, sync::Arc};

use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{BigInt, BigInteger, Field, PrimeField, UniformRand};
use ark_serialize::CanonicalDeserialize;
use ark_test_curves::secp256k1::{self as G1, Fr as F1, G1Affine};
use ark_ed25519::{self as G2, EdwardsAffine as G2Affine, Fr as F2};
use curve25519_dalek::RistrettoPoint;
use rand::thread_rng;
use group::Group;
use ark_ec::VariableBaseMSM;

use zkp::{toolbox::Scalar, BatchableProof, CompactCrossProof, CompactProof, Transcript};

define_cross_proof! {
    comeq, 
    "{(Q, Com(x), G_1, G_2, H_2); (x, s) | Q = [x]G_1 ∈ G1 & Com(x) = [x]G_2 + [s]H_2 ∈ G2}", 
    (x0, x1, x2, x3), 
    (r0, r1, r2, r3), 
    (s0, s1, s2, s3), 
    (A0, A1, A2, A3, Q), 
    (Com_x0, Com_x1, Com_x2, Com_x3), 
    (G_1, G_1_1, G_1_2, G_1_3, H_1), 
    (G_2, H_2) : 
    A0 = (x0 * G_1 + r0 * H_1), 
    Com_x0 = (x0 * G_2 + s0 * H_2),
    A1 = (x1 * G_1 + r1 * H_1), 
    Com_x1 = (x1 * G_2 + s1 * H_2),
    A2 = (x2 * G_1 + r2 * H_1),
    Com_x2 = (x2 * G_2 + s2 * H_2),
    A3 = (x3 * G_1 + r3 * H_1),
    Com_x3 = (x3 * G_2 + s3 * H_2),
    Q = (x0 * G_1 + x1 * G_1_1 + x2 * G_1_2 + x3 * G_1_3)
}

#[test]
fn create_and_verify_cross_group() {
    let B: Vec<BigInt<4>> = (0..4).map(|x| BigInt::from(1u64) << x*64).collect();

    let G = B.iter().map(|&x| (G1Affine::generator() * F1::from(x)).into_affine() ).collect::<Vec<_>>();

    let H_1 = G1Affine::rand(&mut thread_rng());
    let G_2 = G2Affine::generator();
    let H_2 = G2Affine::rand(&mut thread_rng());
    let min = min(G1::Fr::MODULUS, G2::Fr::MODULUS);

    // Prover's scope
    let (proof, points) = {
        let x: BigInt<4> = BigInt::rand(&mut thread_rng()) >> 2;
        let s: BigInt<4> = BigInt::rand(&mut thread_rng()) >> 2;

        let x0 = x.0[0].into();
        let x1 = x.0[1].into();
        let x2 = x.0[2].into();
        let x3 = x.0[3].into();

        let r0 = F1::rand(&mut thread_rng());
        let r1 = F1::rand(&mut thread_rng());
        let r2 = F1::rand(&mut thread_rng());
        let r3 = F1::rand(&mut thread_rng());

        let s0 = F2::from(BigInt::from(s.0[0]));
        let s1 = F2::from(BigInt::from(s.0[1]));
        let s2 = F2::from(BigInt::from(s.0[2]));
        let s3 = F2::from(BigInt::from(s.0[3]));

        let A0 = (G[0] * F1::from(x0) + H_1 * r0).into_affine();
        let A1 = (G[0] * F1::from(x1) + H_1 * r1).into_affine();
        let A2 = (G[0] * F1::from(x2) + H_1 * r2).into_affine();
        let A3 = (G[0] * F1::from(x3) + H_1 * r3).into_affine();

        let Com_x0 = (G_2 * F2::from(x0) + H_2 * s0).into_affine();
        let Com_x1 = (G_2 * F2::from(x1) + H_2 * s1).into_affine();
        let Com_x2 = (G_2 * F2::from(x2) + H_2 * s2).into_affine();
        let Com_x3 = (G_2 * F2::from(x3) + H_2 * s3).into_affine();

        let Q = <G1Affine as AffineRepr>::Group::msm(
            &G,
            &[F1::from(x0), F1::from(x1), F1::from(x2), F1::from(x3)],
        ).unwrap().into_affine();

        let mut transcript = Transcript::new(b"discrete log equality among groups");
        comeq::prove_cross::<G1Affine, 64, 128, 40>(
            &mut transcript,
            comeq::ProveAssignments {
                x0: &x0,
                x1: &x1,
                x2: &x2,
                x3: &x3,
                r0: &r0,
                r1: &r1,
                r2: &r2,
                r3: &r3,
                s0: &s0,
                s1: &s1,
                s2: &s2,
                s3: &s3,
                A0: &A0,
                A1: &A1,
                A2: &A2,
                A3: &A3,
                Com_x0: &Com_x0,
                Com_x1: &Com_x1,
                Com_x2: &Com_x2,
                Com_x3: &Com_x3,
                Q: &Q,
                G_1: &G[0],
                G_1_1: &G[1],
                G_1_2: &G[2],
                G_1_3: &G[3],
                H_1: &H_1,
                G_2: &G_2,
                H_2: &H_2,
            },
        )
        .unwrap()
    };

    let proof_bytes = proof.to_bytes().unwrap();
    println!("{:?}", proof_bytes.len());
    let parsed_proof: comeq::CompactCrossProof<F1, F2> = CompactCrossProof::from_bytes(&proof_bytes).unwrap();

    // Verifier logic
    let mut transcript = Transcript::new(b"discrete log equality among groups");
    assert!(comeq::verify_cross::<G1Affine, 64, 128, 40>(
        &parsed_proof,
        &mut transcript,
        comeq::VerifyAssignments {
            A0: &points.A0,
            A1: &points.A1,
            A2: &points.A2,
            A3: &points.A3,
            Com_x0: &points.Com_x0,
            Com_x1: &points.Com_x1,
            Com_x2: &points.Com_x2,
            Com_x3: &points.Com_x3,
            Q: &points.Q,
            G_1: &G[0],
            G_1_1: &G[1],
            G_1_2: &G[2],
            G_1_3: &G[3],
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

        let mut transcript = Transcript::new(b"comeqTest");
        comeq::prove_batchable(
            &mut transcript,
            comeq::ProveAssignments {
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
    let parsed_proof: comeq::BatchableProof<_> = BatchableProof::from_bytes(&proof_bytes).unwrap();

    // Verifier logic
    let mut transcript = Transcript::new(b"comeqTest");
    assert!(comeq::verify_batchable(
        &parsed_proof,
        &mut transcript,
        comeq::VerifyAssignments {
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

            let mut transcript = Transcript::new(b"comeqTest");
            let (proof, points) = comeq::prove_batchable(
                &mut transcript,
                comeq::ProveAssignments {
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
    let mut transcripts = vec![Transcript::new(b"comeqTest"); messages.len()];

    assert!(comeq::batch_verify(
        &proofs,
        transcripts.iter_mut().collect(),
        comeq::BatchVerifyAssignments {
            A: pubkeys,
            B: vrf_outputs,
            H: H,
            G: G,
        },
    )
    .is_ok());
}

*/