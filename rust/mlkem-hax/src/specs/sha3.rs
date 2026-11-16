//! FIPS-202 (SHA-3 / SHAKE) — real, byte-exact pure-Rust implementation.
//!
//! Keccak-f[1600] permutation + sponge, with zero external dependencies (fixed
//! arrays, bounded loops — hax-extraction friendly). These are the FIPS-203
//! symmetric primitives for ML-KEM:
//! - G(seed)      = SHA3-512(seed)      → (ρ, σ)
//! - H(pk)        = SHA3-256(pk)        → public-key hash
//! - J(z ‖ c)     = SHAKE-256(z ‖ c)    → implicit-rejection key
//! - XOF(ρ, i, j) = SHAKE-128(ρ ‖ i ‖ j) → matrix sampling (incremental squeeze)
//! - PRF_η(s, b)  = SHAKE-256(s ‖ b)    → CBD noise

/// Keccak-f[1600] round constants.
const RC: [u64; 24] = [
    0x0000000000000001, 0x0000000000008082, 0x800000000000808a, 0x8000000080008000,
    0x000000000000808b, 0x0000000080000001, 0x8000000080008081, 0x8000000000008009,
    0x000000000000008a, 0x0000000000000088, 0x0000000080008009, 0x000000008000000a,
    0x000000008000808b, 0x800000000000008b, 0x8000000000008089, 0x8000000000008003,
    0x8000000000008002, 0x8000000000000080, 0x000000000000800a, 0x800000008000000a,
    0x8000000080008081, 0x8000000000008080, 0x0000000080000001, 0x8000000080008008,
];

/// Rotation offsets, in the ρ/π traversal order.
const ROTC: [u32; 24] = [
    1, 3, 6, 10, 15, 21, 28, 36, 45, 55, 2, 14,
    27, 41, 56, 8, 25, 43, 62, 18, 39, 61, 20, 44,
];

/// Lane permutation (π), in the ρ/π traversal order.
const PILN: [usize; 24] = [
    10, 7, 11, 17, 18, 3, 5, 16, 8, 21, 24, 4,
    15, 23, 19, 13, 12, 2, 20, 14, 22, 9, 6, 1,
];

/// The Keccak-f[1600] permutation, in place on 25 lanes of 64 bits.
fn keccakf(st: &mut [u64; 25]) {
    let mut bc = [0u64; 5];
    for round in 0..24 {
        // θ
        for i in 0..5 {
            bc[i] = st[i] ^ st[i + 5] ^ st[i + 10] ^ st[i + 15] ^ st[i + 20];
        }
        for i in 0..5 {
            let t = bc[(i + 4) % 5] ^ bc[(i + 1) % 5].rotate_left(1);
            for jj in 0..5 {
                let j = jj * 5;
                st[j + i] ^= t;
            }
        }
        // ρ and π
        let mut t = st[1];
        for i in 0..24 {
            let j = PILN[i];
            let tmp = st[j];
            st[j] = t.rotate_left(ROTC[i]);
            t = tmp;
        }
        // χ
        for jj in 0..5 {
            let j = jj * 5;
            for i in 0..5 {
                bc[i] = st[j + i];
            }
            for i in 0..5 {
                st[j + i] ^= (!bc[(i + 1) % 5]) & bc[(i + 2) % 5];
            }
        }
        // ι
        st[0] ^= RC[round];
    }
}

/// XOR a `rate`-byte block into the state (little-endian lanes). `rate` must be
/// a multiple of 8.
fn xor_block(st: &mut [u64; 25], block: &[u8], rate: usize) {
    let mut i = 0;
    while i < rate / 8 {
        let b = i * 8;
        let lane = (block[b] as u64)
            | ((block[b + 1] as u64) << 8)
            | ((block[b + 2] as u64) << 16)
            | ((block[b + 3] as u64) << 24)
            | ((block[b + 4] as u64) << 32)
            | ((block[b + 5] as u64) << 40)
            | ((block[b + 6] as u64) << 48)
            | ((block[b + 7] as u64) << 56);
        st[i] ^= lane;
        i += 1;
    }
}

/// Extract `n` bytes from the state (little-endian lanes), `n <= rate`.
fn extract(st: &[u64; 25], out: &mut [u8]) {
    for k in 0..out.len() {
        let lane = st[k / 8];
        out[k] = (lane >> (8 * (k % 8))) as u8;
    }
}

/// Generic sponge: absorb `input`, then squeeze `out.len()` bytes.
/// `rate` in bytes; `delim` is the domain-separation/padding byte.
fn keccak(rate: usize, delim: u8, input: &[u8], out: &mut [u8]) {
    let mut st = [0u64; 25];
    let mut block = [0u8; 168]; // max rate (SHAKE-128)

    // Absorb full blocks.
    let mut pos = 0;
    while input.len() - pos >= rate {
        xor_block(&mut st, &input[pos..pos + rate], rate);
        keccakf(&mut st);
        pos += rate;
    }

    // Final block with pad10*1 padding.
    let rem = input.len() - pos;
    for i in 0..rate {
        block[i] = 0;
    }
    for i in 0..rem {
        block[i] = input[pos + i];
    }
    block[rem] = delim;
    block[rate - 1] |= 0x80;
    xor_block(&mut st, &block[..rate], rate);
    keccakf(&mut st);

    // Squeeze.
    let mut outpos = 0;
    while outpos < out.len() {
        let n = if out.len() - outpos < rate { out.len() - outpos } else { rate };
        extract(&st, &mut out[outpos..outpos + n]);
        outpos += n;
        if outpos < out.len() {
            keccakf(&mut st);
        }
    }
}

/// SHA3-256 (rate 136, delim 0x06). ML-KEM H.
pub fn sha3_256(input: &[u8]) -> [u8; 32] {
    let mut out = [0u8; 32];
    keccak(136, 0x06, input, &mut out);
    out
}

/// SHA3-512 (rate 72, delim 0x06). ML-KEM G.
pub fn sha3_512(input: &[u8]) -> [u8; 64] {
    let mut out = [0u8; 64];
    keccak(72, 0x06, input, &mut out);
    out
}

/// SHAKE-256 (rate 136, delim 0x1f), squeezing 32 bytes. ML-KEM J.
pub fn shake256(input: &[u8], _out_len: usize) -> [u8; 32] {
    let mut out = [0u8; 32];
    keccak(136, 0x1f, input, &mut out);
    out
}

/// PRF_η = SHAKE-256(key ‖ nonce), squeezing 128 bytes (64·η for η=2). ML-KEM PRF.
pub fn prf(key: &[u8; 32], nonce: u8, _out_len: usize) -> [u8; 128] {
    let mut input = [0u8; 33];
    for i in 0..32 {
        input[i] = key[i];
    }
    input[32] = nonce;
    let mut out = [0u8; 128];
    keccak(136, 0x1f, &input, &mut out);
    out
}

// ---------------------------------------------------------------------------
// Incremental SHAKE-128 XOF (rate 168, delim 0x1f) for matrix rejection sampling.
// The absorb input (ρ ‖ i ‖ j = 34 bytes) fits in one block; squeezing is
// block-at-a-time so the FIPS-203 §4.2.2 rejection loop can request more.
// ---------------------------------------------------------------------------

/// SHAKE-128 block size in bytes.
pub const SHAKE128_RATE: usize = 168;

/// Absorb a short seed (≤ 167 bytes) and return the primed Keccak state.
pub fn shake128_init(seed: &[u8]) -> [u64; 25] {
    let mut st = [0u64; 25];
    let mut block = [0u8; SHAKE128_RATE];
    for i in 0..seed.len() {
        block[i] = seed[i];
    }
    block[seed.len()] = 0x1f;
    block[SHAKE128_RATE - 1] |= 0x80;
    xor_block(&mut st, &block, SHAKE128_RATE);
    keccakf(&mut st);
    st
}

/// Squeeze one 168-byte SHAKE-128 block, advancing the state.
pub fn shake128_squeezeblock(st: &mut [u64; 25]) -> [u8; SHAKE128_RATE] {
    let mut out = [0u8; SHAKE128_RATE];
    extract(st, &mut out);
    keccakf(st);
    out
}

#[cfg(test)]
mod tests {
    use super::*;

    // FIPS-202 published empty-string digests.
    #[test]
    fn sha3_256_empty() {
        let h = sha3_256(&[]);
        let expected: [u8; 32] = [
            0xa7, 0xff, 0xc6, 0xf8, 0xbf, 0x1e, 0xd7, 0x66, 0x51, 0xc1, 0x47, 0x56,
            0xa0, 0x61, 0xd6, 0x62, 0xf5, 0x80, 0xff, 0x4d, 0xe4, 0x3b, 0x49, 0xfa,
            0x82, 0xd8, 0x0a, 0x4b, 0x80, 0xf8, 0x43, 0x4a,
        ];
        assert_eq!(h, expected);
    }

    #[test]
    fn sha3_512_empty() {
        let h = sha3_512(&[]);
        let expected: [u8; 64] = [
            0xa6, 0x9f, 0x73, 0xcc, 0xa2, 0x3a, 0x9a, 0xc5, 0xc8, 0xb5, 0x67, 0xdc,
            0x18, 0x5a, 0x75, 0x6e, 0x97, 0xc9, 0x82, 0x16, 0x4f, 0xe2, 0x58, 0x59,
            0xe0, 0xd1, 0xdc, 0xc1, 0x47, 0x5c, 0x80, 0xa6, 0x15, 0xb2, 0x12, 0x3a,
            0xf1, 0xf5, 0xf9, 0x4c, 0x11, 0xe3, 0xe9, 0x40, 0x2c, 0x3a, 0xc5, 0x58,
            0xf5, 0x00, 0x19, 0x9d, 0x95, 0xb6, 0xd3, 0xe3, 0x01, 0x75, 0x85, 0x86,
            0x28, 0x1d, 0xcd, 0x26,
        ];
        assert_eq!(h, expected);
    }

    #[test]
    fn sha3_256_abc() {
        // SHA3-256("abc")
        let h = sha3_256(b"abc");
        let expected: [u8; 32] = [
            0x3a, 0x98, 0x5d, 0xa7, 0x4f, 0xe2, 0x25, 0xb2, 0x04, 0x5c, 0x17, 0x2d,
            0x6b, 0xd3, 0x90, 0xbd, 0x85, 0x5f, 0x08, 0x6e, 0x3e, 0x9d, 0x52, 0x5b,
            0x46, 0xbf, 0xe2, 0x45, 0x11, 0x43, 0x15, 0x32,
        ];
        assert_eq!(h, expected);
    }

    #[test]
    fn shake256_empty_prefix() {
        // SHAKE256("") first 32 bytes.
        let h = shake256(&[], 32);
        let expected: [u8; 32] = [
            0x46, 0xb9, 0xdd, 0x2b, 0x0b, 0xa8, 0x8d, 0x13, 0x23, 0x3b, 0x3f, 0xeb,
            0x74, 0x3e, 0xeb, 0x24, 0x3f, 0xcd, 0x52, 0xea, 0x62, 0xb8, 0x1b, 0x82,
            0xb5, 0x0c, 0x27, 0x64, 0x6e, 0xd5, 0x76, 0x2f,
        ];
        assert_eq!(h, expected);
    }

    #[test]
    fn shake128_empty_prefix() {
        // SHAKE128("") first 168 bytes, checked on the leading 16.
        let mut st = shake128_init(&[]);
        let block = shake128_squeezeblock(&mut st);
        let expected16: [u8; 16] = [
            0x7f, 0x9c, 0x2b, 0xa4, 0xe8, 0x8f, 0x82, 0x7d, 0x61, 0x60, 0x45, 0x50,
            0x76, 0x05, 0x85, 0x3e,
        ];
        assert_eq!(&block[..16], &expected16);
    }

    #[test]
    fn sha3_256_deterministic() {
        let input = [0u8; 32];
        assert_eq!(sha3_256(&input), sha3_256(&input));
    }
}
