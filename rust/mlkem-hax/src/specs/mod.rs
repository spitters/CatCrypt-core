//! Pure cryptographic specifications (hash stubs).
//!
//! These are specification stubs for SHA3 and SHAKE. The actual implementations
//! are axiomatized in the Lean bridge. The stubs provide deterministic output
//! for testing, but are NOT cryptographically secure.

pub mod sha3;
