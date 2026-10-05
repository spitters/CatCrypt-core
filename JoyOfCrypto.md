# The Joy of Cryptography in CatCrypt

This document maps Mike Rosulek's free textbook
*[The Joy of Cryptography](https://joyofcryptography.com/)* to the worked schemes in
`CatCryptCore/Examples/`. Rosulek proves security with *interchangeable libraries*: a
proof replaces one library by an indistinguishable one, simplifies the composed code,
and repeats. CatCrypt's state-separating packages are the same device, and the
simplification steps are performed by the tactics `ssprove_code_simpl`,
`ssprove_contract_*`, `ssprove_copy_propagate_*`, `ssprove_crypto` and `adv_game_hop`.

Every module listed here is part of this repository and of its library build. The
library is built with `sorry` reported as an error, so every theorem named below is
proved; the statement column records the hypotheses a theorem carries. The
[blueprint](https://spitters.github.io/CatCrypt-core/blueprint/) states the same
results informally, one chapter or section per module, with links to the declarations.

## How to read the tables

- *Perfect* means an advantage equal to `0` for every adversary. Most perfect results
  instantiate a primitive by a bijection family (for each input, `k ↦ F(k, x)` is a
  bijection from keys to outputs); over a uniform key such a primitive is
  information-theoretically ideal, and the proof is a single bijection coupling.
- *Reduction* means a bound of the form `Adv_scheme(A) ≤ Σ Adv_prim(B_i(A))` with
  each `B_i` an explicit adversary defined in the module.
- *Hop hypotheses* means the composition is proved and the individual game hops
  (typically the soundness of a reduction) are arguments of the theorem.

Chapter numbers follow the online edition of the book.

## Chapters of the book

| Ch. | Topic | Module | Main results | Statement |
|---|---|---|---|---|
| 1–2 | One-time pad, one-time secrecy | `OneTimePad` | `otp_correct`, `otp_perfect_indcpa`, `otp_nompkg_secure`, `otp_uc` | Perfect IND-CPA over `Bool`; the same games as perfectly secure packages and as UC emulation with error 0 |
| 1–2 | (same, by reflection) | `ReflectTacticDemo` | `demo_otp_nompkg_secure`, `demo_otp_uc` | The two package-level OTP results, each by one call of the reflective package tactic |
| 3 | Secret sharing | `SecretSharing` | `shareXor_reconstruct`, `ss_perfect_privacy` | 2-out-of-2 XOR sharing; one share has advantage 0 |
| 3 | Secret sharing | `ShamirSecretSharing` | `shamir_reconstruct`, `shamir_perfect_privacy` | Shamir `t`-out-of-`n` over `ZMod p`: Lagrange reconstruction from `t` shares; any `t − 1` shares have advantage 0 |
| 5 | Pseudorandom generators | `PRG` | `bijPRG_perfect`, `triple_prg_bound_of_assumption` | Perfect security of a bijective generator (length-preserving); triple-from-double bound `2·ε` with hop hypotheses |
| 6 | Pseudorandom functions | `PRF` | `bijPRF_perfect`, `cascade_prf_bound` | Perfect bijection-family PRF; cascade bound `2·ε + q(q−1)/2N` with hop hypotheses |
| 6 | PRG from a PRF | `PRFPRG` | `prg_decomp_security_bound` | Over `Bool`, two counters: sum of two PRF advantages of explicit reductions, for the variant with independent seeds |
| 7 | CPA security | `CPAFromPRF` | `bijCPA_perfect_indcpa`, `cpa_from_prf_bound` | `(r, F(k, r) ⊕ m)`: perfect for a bijection family; `≤ ε` under a PRF assumption with the PRF-swap hop as a hypothesis |
| 7 | Deterministic encryption | `DetCPA` | `det_enc_xor_insecure` | Deterministic XOR encryption: a distinguisher with advantage exactly 1 |
| 7 | IND-CPA games | `INDCPA` | `perfect_indcpa_zero_advantage` | Standalone IND-CPA games; perfect security gives advantage 0 |
| 8 | Block-cipher modes | `CTRMode` | `ctr_perfect_indcpa`, `ctr_indcpa_bound` | Single-block CTR: perfect for a bijection family; `≤ ε` under a PRF assumption, with the PRF-swap hop as a hypothesis |
| 8 | Block-cipher modes | `CBCMode` | `cbc_perfect_indcpa`, `cbc_indcpa_bound` | Single-block CBC: perfect for a family bijective in key and input; `≤ 2·ε` for a real cipher under a PRF assumption, with the two swap hops as hypotheses |
| 9 | Chosen-ciphertext attacks | `Crypto/SecurityDefs` | `INDCCA_Game`, `INDCCA_reduces_to_INDCPA` | IND-CCA game with a decryption oracle; IND-CCA ≤ IND-CPA + two decryption-oracle integrity gaps, for any scheme |
| 10 | MACs | `MAC` | `bijMAC_forgery_prob`, `boolXorMAC_forgery_prob` | Bijection-family MAC: single-query forgery probability exactly `1/\|Tag\|` |
| 10 | MAC from a PRF | `PRFMAC` | `security_based_on_prf` | Over `Bool`: forgery on an unqueried message, two PRF advantages plus a statistical gap of 1/2 |
| 12 | Encrypt-then-MAC | `EncryptThenMAC` | `EtM_correct`, `boolEtM_perfect_indcpa` | Generic EtM combinator preserves correctness; perfect IND-CPA of the XOR instance |
| 12 | Encrypt-then-MAC under CCA | `EtMCCA` | `boolEtM_indcca_reduces` | IND-CCA advantage of the XOR instance equals its MAC-integrity gaps (the IND-CPA term is 0) |
| 12 | Universal hashing | `UniversalHash` | `boolPairwiseHash_is_universal`, `boolPairwiseHash_mac_security` | A 1/2-universal family over `Bool`; one-time forgery advantage ≤ 1/2 |
| 13 | Signatures | `Schnorr` | `schnorr_special_soundness`, `schnorr_forking_bound`, `dlFromForking_correct` | Schnorr: special soundness; fork success ≥ `acc² − acc/p` by the core forking lemma; extraction returns the discrete log |
| 14 | Diffie–Hellman | `DiffieHellman` | `ka_advantage_eq_ddh` | Key-indistinguishability advantage equals the DDH advantage of an explicit reduction |
| 15 | ElGamal | `ElGamal` | `elgamal_indcpa_le_ddh`, `elgamal_indcpa_eq_ddh` | Pairing-group formulation: IND-CPA ≤ two DDH advantages of explicit reductions; the distance from the real encryption of `m₀` to the ideal DDH world equals one DDH advantage |
| 15 | ElGamal | `ElGamalDDH`, `CyclicGroupDDH` | `elgamal_correct`, `elgamal_indcpa_security` | Cyclic group with explicit exponents: IND-CPA ≤ two DDH advantages of explicit reductions |
| 15 | ElGamal as UC | `ElGamalUCConcrete` | `elgamal_uc_concrete` | Concrete UC emulation bounded by the DDH advantages of the reductions |
| 15 | Hashed ElGamal | `HashedElGamal` | `heg_indcpa_le_ddh`, `heg_perfect_hash_security` | Two DDH advantages, under a message-independence hypothesis on the ideal reduction; advantage 0 when the mask is uniform |
| 15 | Hybrid encryption | `KEMDEM` | `pke_security`, `pke_perfect_security`, `xorHybrid_perfect_security` | `Adv_PKE ≤ Adv_KEM + Adv_DEM + Adv_KEM` with three explicit reductions; perfect when both components are |

Chapter 4 (intractable computations) and Chapter 11 (hash functions) have no
dedicated module. The hardness assumptions used above (DDH, CDH, DL, t-SDH, ODH, CR,
OWF, PRP, RSA and others) are defined in `Crypto/Assumptions/`.

### Where the core statement differs from the book

- The block-cipher modes are proved for a single block. Multi-block CTR needs a
  product-of-bijections argument and multi-block CBC a PRP-chaining argument; neither
  is formalized.
- A bijective generator is length-preserving, so `bijPRG_perfect` does not cover a
  length-extending PRG; the length-extending case is the triple-from-double bound.
- Perfect IND-CCA is impossible in this information-theoretic model: a one-time-pad
  decryption oracle leaks the key, and a finite tag space admits guessing. The CCA
  results are therefore reductions to integrity gaps.
- `PRFPRG` and `PRFMAC` work over `Bool`, so their bounds are concrete numbers rather
  than functions of a security parameter.

## Beyond the book

| Topic | Module | Main results | Statement |
|---|---|---|---|
| Basic Hash (RFID protocol) | `BasicHash` | `auth_zero_advantage_xor`, `unlink_real_always_true`, `unlink_ideal_not_always_true` | Perfect authentication for a bijection-family hash; for the XOR hash the two unlinkability games are distinguishable |
| Commitments | `Commitment` | `maskComm_perfect_hiding`, `idComm_perfectly_binding` | A perfectly hiding and a perfectly binding commitment over `Bool` |
| Σ-protocols | `SigmaProtocol` | `simpleSigma_shvzk`, `simpleSigma_special_sound`, `simpleSigma_hiding`, `simpleSigma_binding` | Completeness, perfect SHVZK and special soundness; the derived commitment is hiding and binding |
| Σ-protocols with prover state | `Sigma` | `simpleSigma_shvzk_given`, `simpleSigma_shvzk`, `simpleSigma_special_sound` | The same properties for a stateful prover, with a fixed or a sampled challenge |
| Chaum–Pedersen | `ChaumPedersen`, `GroupParam` | `chaumPedersen_SHVZK_visible`, `chaumPedersen_special_soundness`, `chaumPedersen_uc_secure` | Equality of discrete logarithms: SHVZK, special soundness, UC emulation with error 0 |
| Oblivious transfer | `OT` | `otEnc_message_independent`, `ot_sender_secure`, `receiver_security` | Naor–Pinkas: per-instance sender privacy when `d ≠ ab`; sender privacy of the whole transcript ≤ `1/\|Exp\|` (the probability of `c = ab`); receiver privacy ≤ two DDH advantages |
| Coin tossing | `CoinToss` | `coinToss_eq` | The sum of two uniform elements of `ZMod p` is uniform |
| Pedersen commitments | `Commitments/Pedersen`, `Commitments/CommitmentScheme` | `pedersen_perfect_hiding`, `pedersen_binding_le_dlog`, `pedersen_hiding_uc` | Perfect hiding; binding ≤ DL advantage of an explicit reduction; UC hiding with error 0 |
| KZG commitments | `Commitments/KZG/*`, `Commitments/PolyCommitScheme` | `KZG_knowledge_sound`, `honestAGMOutput_checks` | Knowledge soundness in the algebraic group model: ≤ `(t + 1)` · t-SDH advantage of an explicit reduction |
| Nested hybrids | `PKE/*` | `Adv_MT_CPA_OT`, `Adv_MI_MT_CPA_nested` | Larsen–Schürmann (CSF 2025): many-time ≤ `q·ε`, multi-instance ≤ `n·q·ε`, from per-step hypotheses on the SLIDE adversaries |
| Cryptobox (NaCl `crypto_box`) | `Cryptobox/*` | `pkae_game_hopping`, `cryptobox_security_full` | PKAE ≤ `2·ε_pkey + ε_nike + ε_ae`; the PKEY hops are proved, the NIKE and AE hop bounds are hypotheses |
| Hybrid argument | `DeepHybrid` | `two_instance_advantage_bound`, `three_instance_triangle` | Hybrid ladders of shallow games for XOR encryption |

## Proof-ladders benchmark

The community [proof-ladders](https://github.com/proof-ladders/) benchmark poses a
fixed set of challenges. The modules above cover the following.

| Ladder | Challenge | Module | Statement |
|---|---|---|---|
| Symmetric | PRF cascade | `PRF` | `cascade_prf_bound`: `2·ε + q(q−1)/2N`, all three hop bounds (including the switching hop) as hypotheses |
| Symmetric | PRG triple | `PRG` | `triple_prg_bound_of_assumption`: `2·ε`, hop soundness as hypotheses |
| Symmetric | Encrypt-then-MAC | `EtMCCA` | `boolEtM_indcca_reduces`: IND-CCA reduced to MAC integrity |
| Asymmetric | KEM-DEM | `KEMDEM` | `pke_security`: three explicit reductions, no hypotheses |
| Protocol | Basic Hash | `BasicHash` | Perfect authentication and the unlinkability counterexample |

The other protocol challenges and the implementation ladder are not addressed.

## Attribution

*The Joy of Cryptography* is licensed CC BY-NC-SA. The modules formalize its results,
credit the relevant chapter in their docstrings, and do not reproduce its prose or
figures.
