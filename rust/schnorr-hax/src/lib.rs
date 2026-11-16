// Copyright (c) 2026 CatCrypt Contributors. MIT license.
//! Schnorr signatures: Hax-extractable implementation.
//!
//! This crate implements the standard Schnorr signature scheme in a
//! trait-based style suitable for hax extraction to Lean 4. The
//! `SchnorrCrypto` trait abstracts all concrete group and hash operations,
//! allowing the protocol logic to be verified independently of the group.
//!
//! Architecture follows the frost-hax / faest-hax methodology:
//! - `src/` modules are hax-extractable (fixed-size arrays, bounded loops)
//! - The `SchnorrCrypto` trait is axiomatized in the Lean bridge
//! - Lean bridge connects extraction to CatCrypt's Schnorr formalization

pub mod types;
pub mod scheme;

pub use types::*;
pub use scheme::*;
