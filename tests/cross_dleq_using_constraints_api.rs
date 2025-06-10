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
use ark_ff::{BigInteger, Field, MontConfig, QuadExtConfig, Zero};
use ark_ff::{BigInt, PrimeField, UniformRand, One};
use ark_serialize::CanonicalDeserialize;
use curve25519_dalek::{constants as dalek_constants, edwards};
use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
use group::Group;
use zkp::toolbox::dalek_ark::ristretto255_to_ark;
use zkp::toolbox::{prover, PointVar, Scalar, ScalarVar};

use ark_ed25519::EdwardsAffine as ArkEdwardsAffine;
use ark_secq256k1::Affine as G1Affine;
use ark_secq256k1::Fr as F1;

use rand::thread_rng;
use zkp::toolbox::cross_transcript::TranscriptProtocol;
use zkp::toolbox::Point;
use zkp::toolbox::{cross_prover::CrossProver, cross_verifier::CrossVerifier, SchnorrCS};
use zkp::CompactCrossProof;
use zkp::Transcript;
use ark_ed25519::{EdwardsAffine as G2, Fr as F2};

#[derive(Clone)]
struct PedersenBasis<G1: AffineRepr, G2: AffineRepr> {
    G_1: G1,
    H_1: G1,
    G_2: G2,
    H_2: G2,
}

struct PedersenBasisVars {
    G_1: PointVar,
    G_1_1: PointVar,
    G_1_2: PointVar,
    G_1_3: PointVar,
    H_1: PointVar,
    G_2: PointVar,
    H_2: PointVar,
}

struct CrossDleqProver<G1: AffineRepr>
    where BigInt<4>: From<<G1::ScalarField as PrimeField>::BigInt>, 
        <G1::ScalarField as PrimeField>::BigInt: From<BigInt<4>> {

    prover: CrossProver<G1, G2, Transcript, Transcript, 64, 128, 56>,
    basis: PedersenBasis<G1, G2>,
    basis_vars: PedersenBasisVars,
}

impl<G1: AffineRepr> CrossDleqProver<G1> where BigInt<4>: From<<G1::ScalarField as PrimeField>::BigInt>, 
        <G1::ScalarField as PrimeField>::BigInt: From<BigInt<4>> {

    fn new(basis: PedersenBasis<G1, G2>) -> Self {
        let transcript = Transcript::new(b"DLEQTest");
        let mut prover = CrossProver::<G1, G2, _, _, 64, 128, 56>::new(b"DLEQProof", transcript);

        let B: Vec<BigInt<4>> = (0..4).map(|x| BigInt::from(1u64.into()) << x*64).collect();
        let G = B.iter().map(|&x| (basis.G_1 * G1::ScalarField::from_bigint(x.into()).unwrap() ).into_affine() ).collect::<Vec<_>>();

        let var_G1 = prover.allocate_point(b"G_1", Point::G1(basis.G_1));
        let var_G1_1 = prover.allocate_point(b"G_1_1", Point::G1(G[1]));
        let var_G1_2 = prover.allocate_point(b"G_1_2", Point::G1(G[2]));
        let var_G1_3 = prover.allocate_point(b"G_1_3", Point::G1(G[3]));
        let var_G2 = prover.allocate_point(b"G_2", Point::G2(basis.G_2));
        let var_H1 = prover.allocate_point(b"H_1", Point::G1(basis.H_1));
        let var_H2 = prover.allocate_point(b"H_2", Point::G2(basis.H_2));
        
        Self {
            prover,
            basis,
            basis_vars: PedersenBasisVars {
                G_1: var_G1,
                G_1_1: var_G1_1,
                G_1_2: var_G1_2,
                G_1_3: var_G1_3,
                H_1: var_H1,
                G_2: var_G2,
                H_2: var_H2,
            },
        }
    }

    fn dleq_statement_short(
        &mut self,
        x: ScalarVar,
        r: ScalarVar,
        s: ScalarVar,
        Com1: PointVar,
        Com2: PointVar,
        G_1: PointVar,
        H_1: PointVar,
        G_2: PointVar,
        H_2: PointVar,
    ) {
        self.prover.constrain(Com1, vec![(x, G_1), (r, H_1)]);
        let c2 = self.prover.constrain(Com2, vec![(x, G_2), (s, H_2)]);
        self.prover.require_range_proof(c2);
    }

    fn add_dleq_statement(
        &mut self,
        x: BigInt<4>,
    ) -> (G1, G1, G1, G1, G1, G2, G2, G2, G2) {
        let x0 = BigInt::<4>::from(x.0[0].into());
        let x1 = BigInt::<4>::from(x.0[1].into());
        let x2 = BigInt::<4>::from(x.0[2].into());
        let x3 = BigInt::<4>::from(x.0[3].into());

        let r0 = G1::ScalarField::rand(&mut thread_rng());
        let r1 = G1::ScalarField::rand(&mut thread_rng());
        let r2 = G1::ScalarField::rand(&mut thread_rng());
        let r3 = G1::ScalarField::rand(&mut thread_rng());

        let s0 = F2::rand(&mut thread_rng());
        let s1 = F2::rand(&mut thread_rng());
        let s2 = F2::rand(&mut thread_rng());
        let s3 = F2::rand(&mut thread_rng());

        let Q = (self.basis.G_1 * G1::ScalarField::from_bigint(x.into()).unwrap()).into_affine();
        let Q0 = (self.basis.G_1 * G1::ScalarField::from_bigint(x0.into()).unwrap() + self.basis.H_1 * r0).into_affine();
        let Q1 = (self.basis.G_1 * G1::ScalarField::from_bigint(x1.into()).unwrap() + self.basis.H_1 * r1).into_affine();
        let Q2 = (self.basis.G_1 * G1::ScalarField::from_bigint(x2.into()).unwrap() + self.basis.H_1 * r2).into_affine();
        let Q3 = (self.basis.G_1 * G1::ScalarField::from_bigint(x3.into()).unwrap() + self.basis.H_1 * r3).into_affine();

        let Com_x0 = (self.basis.G_2 * F2::from(x0) + self.basis.H_2 * s0).into_affine();
        let Com_x1 = (self.basis.G_2 * F2::from(x1) + self.basis.H_2 * s1).into_affine();
        let Com_x2 = (self.basis.G_2 * F2::from(x2) + self.basis.H_2 * s2).into_affine();
        let Com_x3 = (self.basis.G_2 * F2::from(x3) + self.basis.H_2 * s3).into_affine();

        let var_x0 = self.prover.allocate_scalar(b"x0", Scalar::Cross(x0)).unwrap();
        let var_x1 = self.prover.allocate_scalar(b"x1", Scalar::Cross(x1)).unwrap();
        let var_x2 = self.prover.allocate_scalar(b"x2", Scalar::Cross(x2)).unwrap();
        let var_x3 = self.prover.allocate_scalar(b"x3", Scalar::Cross(x3)).unwrap();
        let var_r0 = self.prover.allocate_scalar(b"r0", Scalar::F1(r0)).unwrap();
        let var_r1 = self.prover.allocate_scalar(b"r1", Scalar::F1(r1)).unwrap();
        let var_r2 = self.prover.allocate_scalar(b"r2", Scalar::F1(r2)).unwrap();
        let var_r3 = self.prover.allocate_scalar(b"r3", Scalar::F1(r3)).unwrap();
        let var_s0 = self.prover.allocate_scalar(b"s0", Scalar::F2(s0)).unwrap();
        let var_s1 = self.prover.allocate_scalar(b"s1", Scalar::F2(s1)).unwrap();
        let var_s2 = self.prover.allocate_scalar(b"s2", Scalar::F2(s2)).unwrap();
        let var_s3 = self.prover.allocate_scalar(b"s3", Scalar::F2(s3)).unwrap();

        let var_Com_x0 = self.prover.allocate_point(b"Com_x0", Point::G2(Com_x0));
        let var_Com_x1 = self.prover.allocate_point(b"Com_x1", Point::G2(Com_x1));
        let var_Com_x2 = self.prover.allocate_point(b"Com_x2", Point::G2(Com_x2));
        let var_Com_x3 = self.prover.allocate_point(b"Com_x3", Point::G2(Com_x3));

        let var_Q = self.prover.allocate_point(b"Q", Point::G1(Q));
        let var_Q0 = self.prover.allocate_point(b"Q0", Point::G1(Q0));
        let var_Q1 = self.prover.allocate_point(b"Q1", Point::G1(Q1));
        let var_Q2 = self.prover.allocate_point(b"Q2", Point::G1(Q2));
        let var_Q3 = self.prover.allocate_point(b"Q3", Point::G1(Q3));

        self.dleq_statement_short(
            var_x0,
            var_r0,
            var_s0,
            var_Q0,
            var_Com_x0,
            self.basis_vars.G_1,
            self.basis_vars.H_1,
            self.basis_vars.G_2,
            self.basis_vars.H_2,
        );
        self.dleq_statement_short(
            var_x1,
            var_r1,
            var_s1,
            var_Q1,
            var_Com_x1,
            self.basis_vars.G_1,
            self.basis_vars.H_1,
            self.basis_vars.G_2,
            self.basis_vars.H_2,
        );
        self.dleq_statement_short(
            var_x2,
            var_r2,
            var_s2,
            var_Q2,
            var_Com_x2,
            self.basis_vars.G_1,
            self.basis_vars.H_1,
            self.basis_vars.G_2,
            self.basis_vars.H_2,
        );
        self.dleq_statement_short(
            var_x3,
            var_r3,
            var_s3,
            var_Q3,
            var_Com_x3,
            self.basis_vars.G_1,
            self.basis_vars.H_1,
            self.basis_vars.G_2,
            self.basis_vars.H_2,
        );
        self.prover.constrain(var_Q, vec![(var_x0, self.basis_vars.G_1), (var_x1, self.basis_vars.G_1_1), (var_x2, self.basis_vars.G_1_2), (var_x3, self.basis_vars.G_1_3)]);
        (Q, Q0, Q1, Q2, Q3, Com_x0, Com_x1, Com_x2, Com_x3)
    }

    fn prove_cross(self) -> Result<CompactCrossProof<G1::ScalarField, F2>, zkp::ProofError> {
        self.prover.prove_cross()
    }
}

struct CrossDleqVerifier<G1: AffineRepr>
    where BigInt<4>: From<<G1::ScalarField as PrimeField>::BigInt>, 
        <G1::ScalarField as PrimeField>::BigInt: From<BigInt<4>> {

    verifier: CrossVerifier<G1, G2, Transcript, Transcript, 64, 128, 56>,
    basis: PedersenBasis<G1, G2>,
    basis_vars: PedersenBasisVars,
}

impl<G1: AffineRepr> CrossDleqVerifier<G1> where BigInt<4>: From<<G1::ScalarField as PrimeField>::BigInt>, 
        <G1::ScalarField as PrimeField>::BigInt: From<BigInt<4>> {

    fn new(basis: PedersenBasis<G1, G2>) -> Self {
        let transcript = Transcript::new(b"DLEQTest");
        let mut verifier = CrossVerifier::<G1, G2, _, _, 64, 128, 56>::new(b"DLEQProof", transcript);

        let B: Vec<BigInt<4>> = (0..4).map(|x| BigInt::from(1u64.into()) << x*64).collect();
        let G = B.iter().map(|&x| (basis.G_1 * G1::ScalarField::from_bigint(x.into()).unwrap() ).into_affine() ).collect::<Vec<_>>();

        let var_G1 = verifier.allocate_point(b"G_1", Point::G1(basis.G_1)).unwrap();
        let var_G1_1 = verifier.allocate_point(b"G_1_1", Point::G1(G[1])).unwrap();
        let var_G1_2 = verifier.allocate_point(b"G_1_2", Point::G1(G[2])).unwrap();
        let var_G1_3 = verifier.allocate_point(b"G_1_3", Point::G1(G[3])).unwrap();
        let var_G2 = verifier.allocate_point(b"G_2", Point::G2(basis.G_2)).unwrap();
        let var_H1 = verifier.allocate_point(b"H_1", Point::G1(basis.H_1)).unwrap();
        let var_H2 = verifier.allocate_point(b"H_2", Point::G2(basis.H_2)).unwrap();

        Self {
            verifier,
            basis,
            basis_vars: PedersenBasisVars {
                G_1: var_G1,
                G_1_1: var_G1_1,
                G_1_2: var_G1_2,
                G_1_3: var_G1_3,
                H_1: var_H1,
                G_2: var_G2,
                H_2: var_H2,
            },
        }
    }

    fn dleq_statement_short(
        &mut self,
        x: ScalarVar,
        r: ScalarVar,
        s: ScalarVar,
        Com1: PointVar,
        Com2: PointVar,
        G_1: PointVar,
        H_1: PointVar,
        G_2: PointVar,
        H_2: PointVar,
    ) {
        self.verifier.constrain(Com1, vec![(x, G_1), (r, H_1)]);
        let c2 = self.verifier.constrain(Com2, vec![(x, G_2), (s, H_2)]);
        self.verifier.require_range_proof(c2);
    }

    fn add_dleq_statement(&mut self, Q: G1, Q0: G1, Q1: G1, Q2: G1, Q3: G1, Com_x0: G2, Com_x1: G2, Com_x2: G2, Com_x3: G2) {
        let var_x0 = self.verifier.allocate_scalar(b"x0");
        let var_x1 = self.verifier.allocate_scalar(b"x1");
        let var_x2 = self.verifier.allocate_scalar(b"x2");
        let var_x3 = self.verifier.allocate_scalar(b"x3");
        let var_r0 = self.verifier.allocate_scalar(b"r0");
        let var_r1 = self.verifier.allocate_scalar(b"r1");
        let var_r2 = self.verifier.allocate_scalar(b"r2");
        let var_r3 = self.verifier.allocate_scalar(b"r3");
        let var_s0 = self.verifier.allocate_scalar(b"s0");
        let var_s1 = self.verifier.allocate_scalar(b"s1");
        let var_s2 = self.verifier.allocate_scalar(b"s2");
        let var_s3 = self.verifier.allocate_scalar(b"s3");

        let var_Com_x0 = self.verifier.allocate_point(b"Com_x0", Point::G2(Com_x0)).unwrap();
        let var_Com_x1 = self.verifier.allocate_point(b"Com_x1", Point::G2(Com_x1)).unwrap();
        let var_Com_x2 = self.verifier.allocate_point(b"Com_x2", Point::G2(Com_x2)).unwrap();
        let var_Com_x3 = self.verifier.allocate_point(b"Com_x3", Point::G2(Com_x3)).unwrap();

        let var_Q =  self.verifier.allocate_point(b"Q", Point::G1(Q)).unwrap();
        let var_Q0 = self.verifier.allocate_point(b"Q0", Point::G1(Q0)).unwrap();
        let var_Q1 = self.verifier.allocate_point(b"Q1", Point::G1(Q1)).unwrap();
        let var_Q2 = self.verifier.allocate_point(b"Q2", Point::G1(Q2)).unwrap();
        let var_Q3 = self.verifier.allocate_point(b"Q3", Point::G1(Q3)).unwrap();

        self.dleq_statement_short(
            var_x0,
            var_r0,
            var_s0,
            var_Q0,
            var_Com_x0,
            
            self.basis_vars.G_1,
            self.basis_vars.H_1,
            self.basis_vars.G_2,
            self.basis_vars.H_2,
        );
        self.dleq_statement_short(
            var_x1,
            var_r1,
            var_s1,
            var_Q1,
            var_Com_x1,
            
            self.basis_vars.G_1,
            self.basis_vars.H_1,
            self.basis_vars.G_2,
            self.basis_vars.H_2,
        );
        self.dleq_statement_short(
            var_x2,
            var_r2,
            var_s2,
            var_Q2,
            var_Com_x2,
            
            self.basis_vars.G_1,
            self.basis_vars.H_1,
            self.basis_vars.G_2,
            self.basis_vars.H_2,
        );
        self.dleq_statement_short(
            var_x3,
            var_r3,
            var_s3,
            var_Q3,
            var_Com_x3,
            
            self.basis_vars.G_1,
            self.basis_vars.H_1,
            self.basis_vars.G_2,
            self.basis_vars.H_2,
        );
        self.verifier.constrain(var_Q, vec![(var_x0, self.basis_vars.G_1), (var_x1, self.basis_vars.G_1_1), (var_x2, self.basis_vars.G_1_2), (var_x3, self.basis_vars.G_1_3)]);
    }

    fn verify_cross(
        self,
        proof: &CompactCrossProof<G1::ScalarField, F2>,
    ) -> Result<(), zkp::ProofError> {
        self.verifier.verify_cross(proof)
    }
}

#[test]
#[cfg(feature="rangeproof")]
fn cross_zkp() {
    let B = G1Affine::generator();
    let H = G1Affine::rand(&mut thread_rng());
    let G_2 = G2::generator();
    let H_2 = G2::rand(&mut thread_rng());

    let basis = PedersenBasis {
        G_1: B,
        H_1: H,
        G_2,
        H_2,
    };

    let mut prover = CrossDleqProver::<G1Affine>::new(basis.clone());
    let mut cc = vec![];
    for i in 0..16 {
        let x: BigInt<4> = BigInt::rand(&mut thread_rng()) >> 3;
        cc.push(prover.add_dleq_statement(x));
    }

    let proof = prover.prove_cross().unwrap();
    println!("{}", proof.to_bytes().unwrap().len());
    let mut verifier = CrossDleqVerifier::<G1Affine>::new(basis);
    for (Q, Q0, Q1, Q2, Q3, Com_x0, Com_x1, Com_x2, Com_x3) in cc {
        verifier.add_dleq_statement(Q, Q0, Q1, Q2, Q3, Com_x0, Com_x1, Com_x2, Com_x3);
    }

    verifier.verify_cross(&proof).unwrap();
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
