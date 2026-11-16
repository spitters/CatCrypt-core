//! Field arithmetic mod q = 3329 (FIPS 203).
//!
//! All operations work on u16 values in [0, q).
//! Maps to CatCrypt's `ZMod 3329` operations.

use crate::types::Q;

/// Reduce mod q. Input must be < 2*q or u32.
#[inline]
pub fn reduce(x: u32) -> u16 {
    (x % Q) as u16
}

/// Addition mod q.
#[inline]
pub fn add(a: u16, b: u16) -> u16 {
    reduce(a as u32 + b as u32)
}

/// Subtraction mod q.
#[inline]
pub fn sub(a: u16, b: u16) -> u16 {
    reduce(a as u32 + Q - b as u32)
}

/// Multiplication mod q.
#[inline]
pub fn mul(a: u16, b: u16) -> u16 {
    reduce(a as u32 * b as u32)
}

/// Negation mod q.
#[inline]
pub fn neg(a: u16) -> u16 {
    if a == 0 { 0 } else { (Q as u16) - a }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_field_add() {
        assert_eq!(add(3328, 1), 0);
        assert_eq!(add(1000, 2000), 3000);
        assert_eq!(add(2000, 2000), 671); // 4000 mod 3329
    }

    #[test]
    fn test_field_mul() {
        assert_eq!(mul(0, 1234), 0);
        assert_eq!(mul(1, 1234), 1234);
        assert_eq!(mul(17, 17), 289);
    }

    #[test]
    fn test_field_sub() {
        assert_eq!(sub(1000, 1000), 0);
        assert_eq!(sub(0, 1), 3328);
    }
}
