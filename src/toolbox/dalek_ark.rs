use std::convert::TryInto as _;

use ark_ec::twisted_edwards::{TECurveConfig};
use ark_ec::{AffineRepr, CurveGroup};
use ark_ff::{AdditiveGroup as _, BigInteger, Field, MontConfig, Zero};
use ark_ff::{BigInt, PrimeField, UniformRand, One};
use ark_serialize::CanonicalDeserialize;
use curve25519_dalek::{constants as dalek_constants, edwards};
use curve25519_dalek::ristretto::{CompressedRistretto, RistrettoPoint};
//use group::{Group, GroupEncoding};

use ark_ed25519::EdwardsAffine as ArkEdwardsAffine;

use ark_ed25519::{Fq, FqConfig, EdwardsConfig};
use group::{Group as _, GroupEncoding as _};
use rand::thread_rng;

fn is_negative(x: &Fq) -> bool {
    x.into_bigint().to_bytes_le()[0] & 1 == 1
}

pub fn decompress_ristretto255(compressed: &[u8; 32]) -> Option<ArkEdwardsAffine> {
    //CompressedRistretto::decompress(&self)
    // Decode the compressed point into field elements
    let mut bytes = [0u8; 32];
    bytes.copy_from_slice(compressed);
    let s = Fq::from_le_bytes_mod_order(&bytes);

    // Check if the least significant bit of s is 1
    if is_negative(&s) {
        return None;
    }
    let a = EdwardsConfig::COEFF_A;
    let d = EdwardsConfig::COEFF_D;
    
    // y = (1 + a * s²) / (1 - a * s²)
    let y = ( Fq::ONE + a * s.square() ) / ( Fq::ONE - a * s.square() );

    if y.is_zero() {
        return None;
    }
    // x = ((4 * s²) / (a * d * (1 + a * s²)² - (1 - a * s²)²))^(1/2)
    let x = (( Fq::from(4) * s.square() ) / 
        ( a*d* (Fq::ONE + a*s.square()).square() - (Fq::ONE - a*s.square()).square()))
        .sqrt()
        .map(|x| if is_negative(&x) {-x} else {x} );
    
    if x.is_none() || is_negative( &(x.unwrap() * y) ) {
        return None;
    } else {
        let edwards_point = (ArkEdwardsAffine::new_unchecked(x.unwrap(), y) * ark_ed25519::Fr::from(4)).into_affine();
        Some(edwards_point)
    }
}

pub fn ristretto255_to_ark(point: RistrettoPoint) -> Option<ArkEdwardsAffine> {
    // Convert the RistrettoPoint to its Edwards representation
    let edwards_point = point.compress().to_bytes();
    decompress_ristretto255(&edwards_point[0..32].try_into().expect("Slice with incorrect length"))
}

pub fn ark_to_ristretto255(mut point: ArkEdwardsAffine) -> Option<RistrettoPoint> {
    // add 4-torsion if needed
    if is_negative(&(point.x*point.y)) || point.x.is_zero() {
        point = (point + ArkEdwardsAffine::new_unchecked(EdwardsConfig::COEFF_A.sqrt().unwrap(), Fq::ZERO)).into_affine();
    }

    if is_negative(&point.x) || point.y == -Fq::ONE {
        point = ArkEdwardsAffine::new_unchecked(-point.x, -point.y);
    }

    let s = (-EdwardsConfig::COEFF_A * (Fq::ONE - point.y)/(Fq::ONE + point.y))
        .sqrt()
        .map(|x| if is_negative(&x) {-x} else {x} );
    
    match s {
        None => None,
        Some(s) => {
            let mut bytes = [0u8; 32];
            bytes.copy_from_slice(&s.into_bigint().to_bytes_le()[0..32]);
            RistrettoPoint::from_bytes(&bytes).into()
        }
    }   
}

#[test]
fn test_dalek_to_ark() {
    let G = RistrettoPoint::generator();
    let H = RistrettoPoint::random(&mut thread_rng());
    let G_ark = ristretto255_to_ark(G).unwrap();
    let H_ark = ristretto255_to_ark(H).unwrap();
    let R = G + H;
    let R_ark = ristretto255_to_ark(R).unwrap();
    assert!(R_ark - G_ark - H_ark == ArkEdwardsAffine::zero());
}

#[test]
fn test_ark_to_dalek() {
    let G = ArkEdwardsAffine::generator();
    let H = ArkEdwardsAffine::rand(&mut thread_rng());
    let G_dalek = ark_to_ristretto255(G).unwrap();
    let H_dalek = ark_to_ristretto255(H).unwrap();
    let R = (G + H).into_affine();
    let R_dalek = ark_to_ristretto255(R).unwrap();
    assert!(R_dalek - G_dalek - H_dalek == RistrettoPoint::identity());
}