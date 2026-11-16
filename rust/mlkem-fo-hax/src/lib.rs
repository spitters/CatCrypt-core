//! The Fujisaki–Okamoto layer of ML-KEM-768 (FIPS 203, Algorithms 16–18).
//!
//! The crate contains the key-encapsulation orchestration of ML-KEM and nothing
//! below it. K-PKE (Algorithms 13–15) and the hash functions H, G and J are the
//! associated functions of the trait [`fo::FoOps`]; the generic functions
//! [`fo::keygen`], [`fo::encaps`] and [`fo::decaps`] are straight-line call
//! sequences over these operations, with byte (de)serialisation of the
//! decapsulation key the only other work.
//!
//! The code is written in the subset of Rust that hax and Aeneas extract:
//! fixed-size byte arrays, `for` loops over `usize` ranges, no slices, iterators,
//! heap allocation, early returns or closures. An extraction yields the three
//! KEM programs over an abstract interface whose fields are the trait's
//! operations, which is the form of an FO transform over an abstract PKE with
//! explicit coins.

pub mod types;
pub mod fo;
