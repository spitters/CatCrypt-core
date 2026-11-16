//! Reference cross-check for the Schnorr scheme against BIP-340 (secp256k1).
//!
//! These tests instantiate the crate's generic `SchnorrCrypto` trait with the
//! REAL secp256k1 group and the REAL BIP-340 tagged SHA-256 hashes (via the
//! RustCrypto `k256` and `sha2` crates), then drive the crate's OWN scheme
//! functions and cross-check them against the official BIP-340 published test
//! vectors (bitcoin/bips, `bip-0340/test-vectors.csv`) and against `k256`'s own
//! BIP-340 signer/verifier.
//!
//! ## What is checked, and the trait boundary
//!
//! The `SchnorrCrypto` trait models an abstract prime-order group with a
//! 32-byte element encoding and bare 32-byte scalars. secp256k1 fits the scalar
//! side exactly (the field order n is 256-bit) and fits the point side through
//! BIP-340's x-only encoding, with two consequences that these tests treat
//! precisely rather than paper over:
//!
//!  * `sign` (byte-for-byte KAT — see `crate_sign_matches_bip340_vectors`).
//!    The crate's `sign` uses only `group_mul` (scalar times a known point),
//!    `scalar_mul`, `scalar_add`, and `hash_challenge` — every one of which is
//!    faithfully expressible over secp256k1. BIP-340 negates the secret when
//!    P = d·G has odd y and negates the nonce when R = k·G has odd y (the
//!    abstract group has no even-y notion), so the harness supplies the even-y
//!    canonical representatives d' and k' — the exact scalars BIP-340's own
//!    algorithm signs with — and the crate's `sign` then reproduces the
//!    published 64-byte signature exactly for vectors 0-3.
//!
//!  * `verify` (representational gap — see `crate_verify_group_add_gap`).
//!    Verification needs `group_add(R, e·P)`. On the x-only 32-byte encoding
//!    `group_add` is not a total function: re-encoding the intermediate e·P to
//!    x-only discards its y-parity, and lifting it back (BIP-340 lifts to even
//!    y) recovers e·P only when e·P already has even y, otherwise it recovers
//!    -(e·P) and the sum is R - e·P. So the crate's `verify` agrees with the
//!    BIP-340 reference exactly when e·P has even y. `group_add` on the x-only
//!    encoding is the blocking method for a byte-driven verify KAT; the test
//!    asserts this equivalence deterministically against `k256`.
//!
//! The official vectors are independently pinned in
//! `reference_verifier_pins_vectors` (k256's `VerifyingKey::verify_raw`
//! reproduces every published TRUE/FALSE result, and `SigningKey::sign_raw`
//! reproduces the published signatures for the signing vectors).
//!
//! `tests/kat_vectors.rs` is a toy Z_65521 model of the protocol logic and is
//! NOT this independent reference.

use schnorr_hax::scheme::*;
use schnorr_hax::types::*;

use k256::elliptic_curve::ops::Reduce;
use k256::elliptic_curve::point::{AffineCoordinates, DecompactPoint};
use k256::schnorr::{Signature, SigningKey, VerifyingKey};
use k256::{AffinePoint, FieldBytes, ProjectivePoint, Scalar, U256};
use sha2::{Digest, Sha256};

// ============================================================
// secp256k1 / BIP-340 backend for SchnorrCrypto
// ============================================================

/// Reduce 32 big-endian bytes to a secp256k1 scalar (mod n).
fn sc(b: &[u8; 32]) -> Scalar {
    <Scalar as Reduce<U256>>::reduce_bytes(&FieldBytes::from(*b))
}

/// Serialize a secp256k1 scalar to 32 big-endian bytes.
fn sb(s: &Scalar) -> [u8; 32] {
    s.to_bytes().into()
}

/// BIP-340 lift_x: the curve point with the given x-coordinate and even y.
/// `AffinePoint::decompact` is the SEC1 "compact" decode, which fixes even y —
/// the same lift `k256`'s own `VerifyingKey::from_bytes` uses for a public key.
fn lift_x_even(x: &[u8; 32]) -> Option<ProjectivePoint> {
    let ap: Option<AffinePoint> = AffinePoint::decompact(&FieldBytes::from(*x)).into();
    ap.map(ProjectivePoint::from)
}

/// x-only (BIP-340) encoding of a projective point: its affine x-coordinate.
fn x_only(p: ProjectivePoint) -> [u8; 32] {
    p.to_affine().x().into()
}

/// SHA-256 pre-seeded as BIP-340 `tagged_hash(tag, ..)` = SHA256(H(tag)||H(tag)||..).
fn tagged(tag: &[u8]) -> Sha256 {
    let th = Sha256::digest(tag);
    let mut h = Sha256::new();
    h.update(th);
    h.update(th);
    h
}

#[derive(Copy, Clone)]
struct Secp256k1Bip340;

impl SchnorrCrypto for Secp256k1Bip340 {
    fn scalar_add(a: &SchnorrScalar, b: &SchnorrScalar) -> SchnorrScalar {
        sb(&(sc(a) + sc(b)))
    }

    fn scalar_mul(a: &SchnorrScalar, b: &SchnorrScalar) -> SchnorrScalar {
        sb(&(sc(a) * sc(b)))
    }

    fn scalar_inv(a: &SchnorrScalar) -> SchnorrScalar {
        let inv: Option<Scalar> = sc(a).invert().into();
        sb(&inv.unwrap_or(Scalar::ZERO))
    }

    fn group_mul(s: &SchnorrScalar, p: &SchnorrPoint) -> SchnorrPoint {
        match lift_x_even(p) {
            Some(pt) => x_only(pt * sc(s)),
            None => ZERO_POINT,
        }
    }

    fn group_add(a: &SchnorrPoint, b: &SchnorrPoint) -> SchnorrPoint {
        match (lift_x_even(a), lift_x_even(b)) {
            (Some(pa), Some(pb)) => x_only(pa + pb),
            _ => ZERO_POINT,
        }
    }

    /// BIP-340 challenge e = int(tagged_hash("BIP0340/challenge", R || P || m)) mod n.
    fn hash_challenge(r: &SchnorrPoint, pk: &SchnorrPoint, msg: &[u8; 32]) -> SchnorrScalar {
        let mut h = tagged(b"BIP0340/challenge");
        h.update(r);
        h.update(pk);
        h.update(msg);
        let e = <Scalar as Reduce<U256>>::reduce_bytes(&h.finalize());
        sb(&e)
    }

    fn generator() -> SchnorrPoint {
        x_only(ProjectivePoint::GENERATOR)
    }

    fn identity() -> SchnorrPoint {
        ZERO_POINT
    }
}

// ============================================================
// Hex + official BIP-340 vectors (bitcoin/bips test-vectors.csv)
// ============================================================

fn hv(c: u8) -> u8 {
    match c {
        b'0'..=b'9' => c - b'0',
        b'a'..=b'f' => c - b'a' + 10,
        b'A'..=b'F' => c - b'A' + 10,
        _ => panic!("bad hex digit"),
    }
}

fn hx32(s: &str) -> [u8; 32] {
    let b = s.as_bytes();
    assert_eq!(b.len(), 64, "expected 64 hex chars");
    let mut o = [0u8; 32];
    for i in 0..32 {
        o[i] = (hv(b[2 * i]) << 4) | hv(b[2 * i + 1]);
    }
    o
}

fn hx64(s: &str) -> [u8; 64] {
    let b = s.as_bytes();
    assert_eq!(b.len(), 128, "expected 128 hex chars");
    let mut o = [0u8; 64];
    for i in 0..64 {
        o[i] = (hv(b[2 * i]) << 4) | hv(b[2 * i + 1]);
    }
    o
}

/// Signing vectors 0-3 (secret key present, 32-byte message).
struct SignVector {
    sk: &'static str,
    pk: &'static str,
    aux: &'static str,
    msg: &'static str,
    sig: &'static str,
}

const SIGN_VECTORS: &[SignVector] = &[
    SignVector {
        sk: "0000000000000000000000000000000000000000000000000000000000000003",
        pk: "F9308A019258C31049344F85F89D5229B531C845836F99B08601F113BCE036F9",
        aux: "0000000000000000000000000000000000000000000000000000000000000000",
        msg: "0000000000000000000000000000000000000000000000000000000000000000",
        sig: "E907831F80848D1069A5371B402410364BDF1C5F8307B0084C55F1CE2DCA821525F66A4A85EA8B71E482A74F382D2CE5EBEEE8FDB2172F477DF4900D310536C0",
    },
    SignVector {
        sk: "B7E151628AED2A6ABF7158809CF4F3C762E7160F38B4DA56A784D9045190CFEF",
        pk: "DFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659",
        aux: "0000000000000000000000000000000000000000000000000000000000000001",
        msg: "243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89",
        sig: "6896BD60EEAE296DB48A229FF71DFE071BDE413E6D43F917DC8DCF8C78DE33418906D11AC976ABCCB20B091292BFF4EA897EFCB639EA871CFA95F6DE339E4B0A",
    },
    SignVector {
        sk: "C90FDAA22168C234C4C6628B80DC1CD129024E088A67CC74020BBEA63B14E5C9",
        pk: "DD308AFEC5777E13121FA72B9CC1B7CC0139715309B086C960E18FD969774EB8",
        aux: "C87AA53824B4D7AE2EB035A2B5BBBCCC080E76CDC6D1692C4B0B62D798E6D906",
        msg: "7E2D58D8B3BCDF1ABADEC7829054F90DDA9805AAB56C77333024B9D0A508B75C",
        sig: "5831AAEED7B44BB74E5EAB94BA9D4294C49BCF2A60728D8B4C200F50DD313C1BAB745879A5AD954A72C45A91C3A51D3C7ADEA98D82F8481E0E1E03674A6F3FB7",
    },
    SignVector {
        sk: "0B432B2677937381AEF05BB02A66ECD012773062CF3FA2549E44F58ED2401710",
        pk: "25D1DFF95105F5253C4022F628A996AD3A0D95FBF21D468A1B33F8C160D8F517",
        aux: "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF",
        msg: "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF",
        sig: "7EB0509757E246F19449885651611CB965ECC1A187DD51B64FDA1EDC9637D5EC97582B9CB13DB3933705B32BA982AF5AF25FD78881EBB32771FC5922EFC66EA3",
    },
];

/// Verification vectors 0-14 (all 32-byte messages), with the published result.
struct VerifyVector {
    pk: &'static str,
    msg: &'static str,
    sig: &'static str,
    valid: bool,
}

const VERIFY_VECTORS: &[VerifyVector] = &[
    VerifyVector { pk: "F9308A019258C31049344F85F89D5229B531C845836F99B08601F113BCE036F9", msg: "0000000000000000000000000000000000000000000000000000000000000000", sig: "E907831F80848D1069A5371B402410364BDF1C5F8307B0084C55F1CE2DCA821525F66A4A85EA8B71E482A74F382D2CE5EBEEE8FDB2172F477DF4900D310536C0", valid: true },
    VerifyVector { pk: "DFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659", msg: "243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89", sig: "6896BD60EEAE296DB48A229FF71DFE071BDE413E6D43F917DC8DCF8C78DE33418906D11AC976ABCCB20B091292BFF4EA897EFCB639EA871CFA95F6DE339E4B0A", valid: true },
    VerifyVector { pk: "DD308AFEC5777E13121FA72B9CC1B7CC0139715309B086C960E18FD969774EB8", msg: "7E2D58D8B3BCDF1ABADEC7829054F90DDA9805AAB56C77333024B9D0A508B75C", sig: "5831AAEED7B44BB74E5EAB94BA9D4294C49BCF2A60728D8B4C200F50DD313C1BAB745879A5AD954A72C45A91C3A51D3C7ADEA98D82F8481E0E1E03674A6F3FB7", valid: true },
    VerifyVector { pk: "25D1DFF95105F5253C4022F628A996AD3A0D95FBF21D468A1B33F8C160D8F517", msg: "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFF", sig: "7EB0509757E246F19449885651611CB965ECC1A187DD51B64FDA1EDC9637D5EC97582B9CB13DB3933705B32BA982AF5AF25FD78881EBB32771FC5922EFC66EA3", valid: true },
    VerifyVector { pk: "D69C3509BB99E412E68B0FE8544E72837DFA30746D8BE2AA65975F29D22DC7B9", msg: "4DF3C3F68FCC83B27E9D42C90431A72499F17875C81A599B566C9889B9696703", sig: "00000000000000000000003B78CE563F89A0ED9414F5AA28AD0D96D6795F9C6376AFB1548AF603B3EB45C9F8207DEE1060CB71C04E80F593060B07D28308D7F4", valid: true },
    VerifyVector { pk: "EEFDEA4CDB677750A420FEE807EACF21EB9898AE79B9768766E4FAA04A2D4A34", msg: "243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89", sig: "6CFF5C3BA86C69EA4B7376F31A9BCB4F74C1976089B2D9963DA2E5543E17776969E89B4C5564D00349106B8497785DD7D1D713A8AE82B32FA79D5F7FC407D39B", valid: false },
    VerifyVector { pk: "DFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659", msg: "243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89", sig: "FFF97BD5755EEEA420453A14355235D382F6472F8568A18B2F057A14602975563CC27944640AC607CD107AE10923D9EF7A73C643E166BE5EBEAFA34B1AC553E2", valid: false },
    VerifyVector { pk: "DFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659", msg: "243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89", sig: "1FA62E331EDBC21C394792D2AB1100A7B432B013DF3F6FF4F99FCB33E0E1515F28890B3EDB6E7189B630448B515CE4F8622A954CFE545735AAEA5134FCCDB2BD", valid: false },
    VerifyVector { pk: "DFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659", msg: "243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89", sig: "6CFF5C3BA86C69EA4B7376F31A9BCB4F74C1976089B2D9963DA2E5543E177769961764B3AA9B2FFCB6EF947B6887A226E8D7C93E00C5ED0C1834FF0D0C2E6DA6", valid: false },
    VerifyVector { pk: "DFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659", msg: "243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89", sig: "0000000000000000000000000000000000000000000000000000000000000000123DDA8328AF9C23A94C1FEECFD123BA4FB73476F0D594DCB65C6425BD186051", valid: false },
    VerifyVector { pk: "DFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659", msg: "243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89", sig: "00000000000000000000000000000000000000000000000000000000000000017615FBAF5AE28864013C099742DEADB4DBA87F11AC6754F93780D5A1837CF197", valid: false },
    VerifyVector { pk: "DFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659", msg: "243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89", sig: "4A298DACAE57395A15D0795DDBFD1DCB564DA82B0F269BC70A74F8220429BA1D69E89B4C5564D00349106B8497785DD7D1D713A8AE82B32FA79D5F7FC407D39B", valid: false },
    VerifyVector { pk: "DFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659", msg: "243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89", sig: "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC2F69E89B4C5564D00349106B8497785DD7D1D713A8AE82B32FA79D5F7FC407D39B", valid: false },
    VerifyVector { pk: "DFF1D77F2A671C5F36183726DB2341BE58FEAE1DA2DECED843240F7B502BA659", msg: "243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89", sig: "6CFF5C3BA86C69EA4B7376F31A9BCB4F74C1976089B2D9963DA2E5543E177769FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141", valid: false },
    VerifyVector { pk: "FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEFFFFFC30", msg: "243F6A8885A308D313198A2E03707344A4093822299F31D0082EFA98EC4E6C89", sig: "6CFF5C3BA86C69EA4B7376F31A9BCB4F74C1976089B2D9963DA2E5543E17776969E89B4C5564D00349106B8497785DD7D1D713A8AE82B32FA79D5F7FC407D39B", valid: false },
];

// ============================================================
// Helpers driving the reference and the BIP-340 nonce
// ============================================================

/// Even-y check for a projective point (true iff y is even).
fn even_y(p: &ProjectivePoint) -> bool {
    !bool::from(p.to_affine().y_is_odd())
}

/// BIP-340 effective secret d' (= d or n-d so that d'·G has even y) and the
/// x-only public key P = x(d·G).
fn effective_secret(d0: &[u8; 32]) -> (Scalar, [u8; 32]) {
    let d = sc(d0);
    let point = ProjectivePoint::GENERATOR * d;
    let d_eff = if even_y(&point) { d } else { d.negate() };
    (d_eff, x_only(point))
}

/// BIP-340 signing nonce: derive the effective nonce k' (even-y R) that the
/// crate's `sign` must be given so that R = k'·G matches the vector.
fn effective_nonce(d_eff: &Scalar, px: &[u8; 32], aux: &[u8; 32], msg: &[u8; 32]) -> Scalar {
    let aux_hash: [u8; 32] = tagged(b"BIP0340/aux").chain_update(aux).finalize().into();
    let d_bytes = sb(d_eff);
    let mut t = [0u8; 32];
    for i in 0..32 {
        t[i] = d_bytes[i] ^ aux_hash[i];
    }
    let mut h = tagged(b"BIP0340/nonce");
    h.update(t);
    h.update(px);
    h.update(msg);
    let k0 = <Scalar as Reduce<U256>>::reduce_bytes(&h.finalize());
    assert!(!bool::from(k0.is_zero()), "nonce must be nonzero");
    let r_point = ProjectivePoint::GENERATOR * k0;
    if even_y(&r_point) {
        k0
    } else {
        k0.negate()
    }
}

/// k256's own BIP-340 verifier over a raw (unhashed) 32-byte message.
fn reference_verify(pk: &[u8; 32], msg: &[u8; 32], sig: &[u8; 64]) -> bool {
    let vk = match VerifyingKey::from_bytes(pk) {
        Ok(v) => v,
        Err(_) => return false,
    };
    let s = match Signature::try_from(&sig[..]) {
        Ok(s) => s,
        Err(_) => return false,
    };
    vk.verify_raw(msg, &s).is_ok()
}

// ============================================================
// 1. Byte-for-byte KAT: the crate's OWN sign vs BIP-340 vectors 0-3
// ============================================================

#[test]
fn crate_sign_matches_bip340_vectors() {
    for (i, v) in SIGN_VECTORS.iter().enumerate() {
        let d0 = hx32(v.sk);
        let aux = hx32(v.aux);
        let msg = hx32(v.msg);
        let expected = hx64(v.sig);
        let expected_pk = hx32(v.pk);

        // BIP-340 even-y canonical secret / nonce (the scalars BIP-340 signs
        // with; the abstract group has no even-y notion to derive them itself).
        let (d_eff, px) = effective_secret(&d0);
        assert_eq!(px, expected_pk, "vector {}: x(d*G) == published public key", i);
        let k_eff = effective_nonce(&d_eff, &px, &aux, &msg);

        // Drive the crate's OWN sign over the real secp256k1 backend.
        let sig = sign::<Secp256k1Bip340>(&sb(&d_eff), &sb(&k_eff), &msg);

        let mut got = [0u8; 64];
        got[0..32].copy_from_slice(&sig.r);
        got[32..64].copy_from_slice(&sig.s);
        assert_eq!(got, expected, "vector {}: crate sign == BIP-340 signature", i);
    }
}

// ============================================================
// 2. hash_challenge is the real BIP-340 challenge; curve equation holds
// ============================================================

#[test]
fn crate_hash_challenge_matches_bip340() {
    for (i, v) in SIGN_VECTORS.iter().enumerate() {
        let pk = hx32(v.pk);
        let msg = hx32(v.msg);
        let sig = hx64(v.sig);
        let mut r = [0u8; 32];
        r.copy_from_slice(&sig[0..32]);
        let mut s = [0u8; 32];
        s.copy_from_slice(&sig[32..64]);

        // Crate's own hash_challenge.
        let c = Secp256k1Bip340::hash_challenge(&r, &pk, &msg);

        // Independent recomputation of BIP-340 e.
        let mut h = tagged(b"BIP0340/challenge");
        h.update(r);
        h.update(pk);
        h.update(msg);
        let e_ref: [u8; 32] = <Scalar as Reduce<U256>>::reduce_bytes(&h.finalize())
            .to_bytes()
            .into();
        assert_eq!(c, e_ref, "vector {}: hash_challenge == BIP-340 challenge", i);

        // BIP-340 curve equation with the published values: s*G == R + e*P,
        // using k256 point ops directly (independent of the crate's group_add).
        let big_p = lift_x_even(&pk).expect("P on curve");
        let big_r = lift_x_even(&r).expect("R on curve");
        let lhs = ProjectivePoint::GENERATOR * sc(&s);
        let rhs = big_r + big_p * sc(&c);
        assert_eq!(lhs, rhs, "vector {}: s*G == R + e*P (secp256k1)", i);
    }
}

// ============================================================
// 3. Scalar field ops match k256; group_mul reproduces the public key
// ============================================================

#[test]
fn crate_scalar_and_group_mul_match_secp256k1() {
    // Scalar field agreement on sample values over the real secp256k1 order.
    let samples: [[u8; 32]; 3] = [
        {
            let mut a = [0u8; 32];
            a[31] = 42;
            a
        },
        hx32("B7E151628AED2A6ABF7158809CF4F3C762E7160F38B4DA56A784D9045190CFEF"),
        hx32("C90FDAA22168C234C4C6628B80DC1CD129024E088A67CC74020BBEA63B14E5C9"),
    ];
    for a in &samples {
        for b in &samples {
            assert_eq!(
                Secp256k1Bip340::scalar_add(a, b),
                sb(&(sc(a) + sc(b))),
                "scalar_add == k256"
            );
            assert_eq!(
                Secp256k1Bip340::scalar_mul(a, b),
                sb(&(sc(a) * sc(b))),
                "scalar_mul == k256"
            );
        }
        // a * a^{-1} == 1 in the real field.
        let inv = Secp256k1Bip340::scalar_inv(a);
        assert_eq!(
            Secp256k1Bip340::scalar_mul(a, &inv),
            sb(&Scalar::ONE),
            "scalar_inv is the field inverse"
        );
    }

    // group_mul(sk, G) reproduces the BIP-340 x-only public key.
    for (i, v) in SIGN_VECTORS.iter().enumerate() {
        let sk = hx32(v.sk);
        let g = Secp256k1Bip340::generator();
        let pk = Secp256k1Bip340::group_mul(&sk, &g);
        assert_eq!(pk, hx32(v.pk), "vector {}: sk*G x-only == public key", i);
    }
}

// ============================================================
// 4. Independent reference: k256 reproduces every published result
// ============================================================

#[test]
fn reference_verifier_pins_vectors() {
    // k256's BIP-340 verifier agrees with every published TRUE/FALSE.
    for (i, v) in VERIFY_VECTORS.iter().enumerate() {
        let pk = hx32(v.pk);
        let msg = hx32(v.msg);
        let sig = hx64(v.sig);
        assert_eq!(
            reference_verify(&pk, &msg, &sig),
            v.valid,
            "vector {}: k256 verify == published result",
            i
        );
    }

    // k256's BIP-340 signer reproduces the published signatures (0-3).
    for (i, v) in SIGN_VECTORS.iter().enumerate() {
        let sk = hx32(v.sk);
        let aux = hx32(v.aux);
        let msg = hx32(v.msg);
        let signing = SigningKey::from_bytes(&sk).expect("valid signing key");
        let sig = signing.sign_raw(&msg, &aux).expect("sign");
        assert_eq!(
            sig.to_bytes(),
            hx64(v.sig),
            "vector {}: k256 sign_raw == published signature",
            i
        );
    }
}

// ============================================================
// 5. verify's group_add gap on the x-only encoding, pinned to k256
// ============================================================

#[test]
fn crate_verify_group_add_gap() {
    // The crate's verify computes group_add(R, e*P). On the x-only 32-byte
    // encoding, the intermediate e*P loses its y-parity, so verify agrees with
    // the BIP-340 reference exactly when e*P has even y. This localizes the
    // blocking method (group_add non-closure) and is asserted against k256.
    let valid = &VERIFY_VECTORS[0..5]; // vectors 0-4: all published-valid
    let mut ep_even = 0;
    let mut ep_odd = 0;
    for (i, v) in valid.iter().enumerate() {
        let pk = hx32(v.pk);
        let msg = hx32(v.msg);
        let sig_bytes = hx64(v.sig);
        let mut r = [0u8; 32];
        r.copy_from_slice(&sig_bytes[0..32]);
        let mut s = [0u8; 32];
        s.copy_from_slice(&sig_bytes[32..64]);

        assert!(reference_verify(&pk, &msg, &sig_bytes), "vector {} is valid", i);

        let sig = SchnorrSignature { r, s };
        let crate_ok = verify::<Secp256k1Bip340>(&pk, &msg, &sig);

        // Independent parity of e*P.
        let c = Secp256k1Bip340::hash_challenge(&r, &pk, &msg);
        let big_p = lift_x_even(&pk).expect("P on curve");
        let ep = big_p * sc(&c);
        let ep_is_even = even_y(&ep);
        if ep_is_even {
            ep_even += 1;
        } else {
            ep_odd += 1;
        }

        assert_eq!(
            crate_ok, ep_is_even,
            "vector {}: crate verify accepts iff e*P has even y",
            i
        );
    }
    // The published set exercises both parities of e*P, so the x-only gap is
    // observed rather than assumed.
    assert!(ep_even > 0 && ep_odd > 0, "both e*P parities present in vectors 0-4");
}
