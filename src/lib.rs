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
#![cfg_attr(feature = "bench", feature(test))]
#![cfg_attr(feature = "nightly", feature(external_doc))]
#![cfg_attr(feature = "nightly", doc(include = "../README.md"))]
#![cfg_attr(feature = "nightly", deny(missing_docs))]
#![doc(html_root_url = "https://docs.rs/zkp/")]
//! ## Note
//!
//! Docs will only build on nightly Rust until
//! [RFC 1990 stabilizes](https://github.com/rust-lang/rust/issues/44732).

extern crate serde;

#[doc(hidden)]
#[macro_use]
pub extern crate serde_derive;
#[doc(hidden)]
pub extern crate merlin;
#[doc(hidden)]
pub extern crate rand;

pub extern crate ark_ec;
pub extern crate ark_ff;

pub use merlin::Transcript;

mod errors;
mod proofs;
mod util;

pub use crate::errors::*;
pub use crate::proofs::*;

pub mod toolbox;

#[macro_use]
mod macros;
pub use crate::macros::*;
