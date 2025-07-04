use std::borrow::BorrowMut as _;
use std::io::Cursor;

use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};
use ark_ff::{BigInt, PrimeField, UniformRand};

use ark_serialize::{CanonicalSerialize, CanonicalDeserialize};
use rand::thread_rng;
use crate::toolbox::{cross_prover::CrossProver, cross_verifier::CrossVerifier, SchnorrCS, PointVar, Point, Scalar, ScalarVar};
use crate::{CompactCrossProof, ProofError};
use crate::Transcript;
use ark_ed25519::{EdwardsAffine as G2, Fr as F2};

#[derive(Clone)]
pub struct PedersenBasis<G1: AffineRepr, G2: AffineRepr> {
    pub G_1: G1,
    pub H_1: G1,
    pub G_2: G2,
    pub H_2: G2,
}

impl<G1: AffineRepr, G2: AffineRepr> PedersenBasis<G1, G2> {
    pub fn new(G_1: G1, H_1: G1, G_2: G2, H_2: G2) -> Self {
        Self { G_1, H_1, G_2, H_2 }
    }   
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

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct CrossDLEQCommitments<G1: AffineRepr, G2: AffineRepr> {
    pub Q: G1,
    pub Q0: G1,
    pub Q1: G1,
    pub Q2: G1,
    pub Q3: G1,
    pub Com_x0: G2,
    pub Com_x1: G2,
    pub Com_x2: G2,
    pub Com_x3: G2,
}

#[derive(Clone, CanonicalSerialize, CanonicalDeserialize)]
pub struct CrossDLEQProof<G1: AffineRepr>
    where BigInt<4>: From<<G1::ScalarField as PrimeField>::BigInt>, 
        <G1::ScalarField as PrimeField>::BigInt: From<BigInt<4>> {
    pub proof: CompactCrossProof<G1::ScalarField, F2>,
    pub commitments: Vec<CrossDLEQCommitments<G1, G2>>,
}

impl<G1: AffineRepr> CrossDLEQProof<G1> 
    where BigInt<4>: From<<G1::ScalarField as PrimeField>::BigInt>, 
        <G1::ScalarField as PrimeField>::BigInt: From<BigInt<4>> {
    pub fn to_bytes(&self) -> Result<Vec<u8>, ProofError> {
        let mut cursor = Cursor::new(Vec::new());
        self.serialize_compressed(&mut cursor).map_err(|_| ProofError::ParsingFailure)?;
        Ok(cursor.into_inner())
    }

    /// Deserializes the proof from a byte slice.
    ///
    /// Returns an error if the byte slice cannot be parsed into a `R1CSProof`.
    pub fn from_bytes(slice: &[u8]) -> Result<CrossDLEQProof<G1>, ProofError> {
        let mut cursor = Cursor::new(slice);
        let proof = CrossDLEQProof::<G1>::deserialize_compressed(&mut cursor);
        if proof.is_ok() {
            Ok(proof.unwrap())
        } else {
            Err(ProofError::ParsingFailure)
        }
    }
}

/// CrossDleqProver is a prover builder for cross group DLEQ statements.
pub struct CrossDleqProver<'a, G1: AffineRepr>
    where BigInt<4>: From<<G1::ScalarField as PrimeField>::BigInt>, 
        <G1::ScalarField as PrimeField>::BigInt: From<BigInt<4>> {
    
    commitments: Vec<CrossDLEQCommitments<G1, G2>>,
    prover: CrossProver<G1, G2, Transcript, &'a mut Transcript, 64, 128, 56>,
    basis: PedersenBasis<G1, G2>,
    basis_vars: PedersenBasisVars,
}

impl<'a, G1: AffineRepr> CrossDleqProver<'a, G1> where BigInt<4>: From<<G1::ScalarField as PrimeField>::BigInt>, 
        <G1::ScalarField as PrimeField>::BigInt: From<BigInt<4>> {

    pub fn new(basis: PedersenBasis<G1, G2>, transcript: &'a mut Transcript) -> Self {
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
            commitments: vec![],
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

    /// Adds a discrete log statement R_{DL} = { (Q ∈ 𝔾_1; x) | Q = x * G_1 }
    pub fn add_dl_statement(&mut self, x: G1::ScalarField) -> G1 {
        let var_x = self.prover.allocate_scalar(b"x", Scalar::F1(x)).unwrap();
        let Q = (self.basis.G_1 * x).into_affine();
        let var_Q = self.prover.allocate_point(b"Q", Point::G1(Q));
        self.prover.constrain(var_Q, vec![(var_x, self.basis_vars.G_1)]);
        Q
    }

    /// Adds a cross DLEQ statement R_{DLEQ} = { (Com_x ∈ 𝔾_2, Q ∈ 𝔾_1; x, r) | Com_x = x * G_1 + r * H_1, Q = x * G_2 }
    pub fn add_dleq_statement(
        &mut self,
        x: BigInt<4>,
        s: <G2 as AffineRepr>::ScalarField,
    ) {
        let B: Vec<BigInt<4>> = (0..4).map(|x| BigInt::from(1u64.into()) << x*64).collect();
        let x0 = BigInt::<4>::from(x.0[0].into());
        let x1 = BigInt::<4>::from(x.0[1].into());
        let x2 = BigInt::<4>::from(x.0[2].into());
        let x3 = BigInt::<4>::from(x.0[3].into());

        let r0 = G1::ScalarField::rand(&mut thread_rng());
        let r1 = G1::ScalarField::rand(&mut thread_rng());
        let r2 = G1::ScalarField::rand(&mut thread_rng());
        let r3 = G1::ScalarField::rand(&mut thread_rng());

        let s = s.into_bigint();
        let s0 = F2::from(BigInt::from(s.0[0].into()));
        let s1 = F2::from(BigInt::from(s.0[1].into()));
        let s2 = F2::from(BigInt::from(s.0[2].into()));
        let s3 = F2::from(BigInt::from(s.0[3].into()));

        let Q = (self.basis.G_1 * G1::ScalarField::from_bigint(x.into()).unwrap()).into_affine();
        let Q0 = (self.basis.G_1 * G1::ScalarField::from_bigint(x0.into()).unwrap() + self.basis.H_1 * r0).into_affine();
        let Q1 = (self.basis.G_1 * G1::ScalarField::from_bigint(x1.into()).unwrap() + self.basis.H_1 * r1).into_affine();
        let Q2 = (self.basis.G_1 * G1::ScalarField::from_bigint(x2.into()).unwrap() + self.basis.H_1 * r2).into_affine();
        let Q3 = (self.basis.G_1 * G1::ScalarField::from_bigint(x3.into()).unwrap() + self.basis.H_1 * r3).into_affine();

        let Com_x0 = (self.basis.G_2 * F2::from(x0) + self.basis.H_2 * s0).into_affine();
        let Com_x1 = (self.basis.G_2 * F2::from(x1) + self.basis.H_2 * s1).into_affine();
        let Com_x2 = (self.basis.G_2 * F2::from(x2) + self.basis.H_2 * s2).into_affine();
        let Com_x3 = (self.basis.G_2 * F2::from(x3) + self.basis.H_2 * s3).into_affine();
        let Com_x = <G2 as AffineRepr>::Group::msm(
            &[Com_x0, Com_x1, Com_x2, Com_x3],
            B.iter().map(|&x| F2::from(x)).collect::<Vec<_>>().as_slice(),
        ).unwrap().into_affine();

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
        let c = CrossDLEQCommitments {
            Q,
            Q0,
            Q1,
            Q2,
            Q3,
            Com_x0,
            Com_x1,
            Com_x2,
            Com_x3,
        };
        self.commitments.push(c);
    }

    /// Proves the cross group statements
    pub fn prove_cross(self) -> Result<CrossDLEQProof<G1>, crate::ProofError> {
        let cross_proof = self.prover.prove_cross()?;

        Ok(CrossDLEQProof {
            proof: cross_proof,
            commitments: self.commitments,
        })
    }
}

/// CrossDleqVerifier is a verifier builder for cross group DLEQ statements.
pub struct CrossDleqVerifier<'a, G1: AffineRepr>
    where BigInt<4>: From<<G1::ScalarField as PrimeField>::BigInt>, 
        <G1::ScalarField as PrimeField>::BigInt: From<BigInt<4>> {

    verifier: CrossVerifier<G1, G2, Transcript, &'a mut Transcript, 64, 128, 56>,
    basis_vars: PedersenBasisVars,
}

impl<'a, G1: AffineRepr> CrossDleqVerifier<'a, G1> where BigInt<4>: From<<G1::ScalarField as PrimeField>::BigInt>, 
        <G1::ScalarField as PrimeField>::BigInt: From<BigInt<4>> {

    pub fn new(basis: PedersenBasis<G1, G2>, transcript: &'a mut Transcript) -> Self {
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

    pub fn add_dl_statement(&mut self, Q: G1) {
        let var_x = self.verifier.allocate_scalar(b"x");
        let var_Q = self.verifier.allocate_point(b"Q", Point::G1(Q)).unwrap();
        self.verifier.constrain(var_Q, vec![(var_x, self.basis_vars.G_1)]);
    }

    pub fn add_dleq_statement(&mut self, commitment: CrossDLEQCommitments<G1, G2>) {
        let CrossDLEQCommitments {
            Q,
            Q0,
            Q1,
            Q2,
            Q3,
            Com_x0,
            Com_x1,
            Com_x2,
            Com_x3,
        } = commitment;
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

    pub fn verify_cross(
        self,
        proof: &CompactCrossProof<G1::ScalarField, F2>,
    ) -> Result<(), crate::ProofError> {
        self.verifier.verify_cross(proof)
    }
}