//! Byte sizes and array types of ML-KEM-768 (FIPS 203, parameter set k = 3).

/// Module rank k = 3 (ML-KEM-768).
pub const K: usize = 3;

/// Encapsulation key ek = ByteEncode12(t̂) ‖ ρ: 384·k + 32 = 1184 bytes.
pub const EK_BYTES: usize = 1184;

/// K-PKE decryption key dk_PKE = ByteEncode12(ŝ): 384·k = 1152 bytes.
pub const DK_PKE_BYTES: usize = 1152;

/// Decapsulation key dk = dk_PKE ‖ ek ‖ H(ek) ‖ z: 768·k + 96 = 2400 bytes.
pub const DK_BYTES: usize = 2400;

/// Ciphertext c = (c₁, c₂): 32·(d_u·k + d_v) = 1088 bytes.
pub const CT_BYTES: usize = 1088;

/// Shared secret K: 32 bytes.
pub const SS_BYTES: usize = 32;

/// Seeds d, z, the message m, the coins r and the hash H(ek): 32 bytes each.
pub const SEED_BYTES: usize = 32;

/// Offset of ek in dk.
pub const DK_EK_OFFSET: usize = DK_PKE_BYTES;

/// Offset of H(ek) in dk.
pub const DK_H_OFFSET: usize = DK_PKE_BYTES + EK_BYTES;

/// Offset of z in dk.
pub const DK_Z_OFFSET: usize = DK_PKE_BYTES + EK_BYTES + SEED_BYTES;

/// Encapsulation key (equal to the K-PKE encryption key ek_PKE).
pub type EncapsKey = [u8; EK_BYTES];

/// K-PKE decryption key.
pub type DkPke = [u8; DK_PKE_BYTES];

/// ML-KEM decapsulation key.
pub type DecapsKey = [u8; DK_BYTES];

/// Ciphertext.
pub type Ciphertext = [u8; CT_BYTES];

/// Shared secret.
pub type SharedSecret = [u8; SS_BYTES];

/// A 32-byte string: a seed (d, z), a message m, coins r or the hash H(ek).
pub type Bytes32 = [u8; SEED_BYTES];
