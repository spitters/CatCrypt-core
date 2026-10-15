/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.CryptoWord
public import CatCryptCore.Crypto.PRPPRFSwitching

/-!
# AEAD (Authenticated Encryption with Associated Data) Security

This file defines security notions for AEAD schemes over a type `W` of keys,
plaintexts and associated data and a ciphertext type `C`.

## Games

* `AEAD_Advantage` — single-sample real-or-random game: the adversary sees one
  ciphertext, either `encrypt key pt ad` under a uniform key or a uniform
  ciphertext. The adversary sees a single sample, so the supremum of this
  advantage over all adversaries is a statistical distance (an
  information-theoretic quantity).
* `AEAD_CCA_Advantage` — adaptive deterministic-authenticated-encryption game
  (Rogaway–Shrimpton 2006). The adversary queries an encryption oracle and a
  decryption oracle. In the real game they are `encrypt key` and
  `decrypt key`. In the ideal game encryption is a lazily sampled random
  function of `(pt, ad)` with values in the ciphertext type, and decryption
  returns the plaintext recorded for `(ct, ad)` in the log of encryption
  answers and `none` otherwise. Consistent answers on repeated queries replace
  the query restrictions of the original definition.
* `AEAD_Keyed_Advantage` — single-sample real-or-random game with key-dependent
  plaintext and associated data.

The ciphertext type `C` is a parameter of `AEADDef` (default `W`). A scheme
with `C = W` whose decryption inverts encryption decrypts every ciphertext to
`some _`, so it has `AEAD_CCA_Advantage` close to `1`: integrity requires a
ciphertext type larger than the plaintext type.

## Main definitions

* `AEADDef` — an AEAD scheme (`encrypt`, and `decrypt` returning `none` on
  rejection)
* `AEAD_Game_Real` / `AEAD_Game_Ideal`, `AEAD_Advantage`
* `aeadRealOracle`, `aeadIdealOracle`, `AEAD_CCA_Advantage`
* `aead_keyed_real` / `aead_keyed_ideal`, `AEAD_Keyed_Advantage`

## Main results

* `AEAD_CPA_le_CCA` — for an adversary `A` given as a probability mass function
  on its guess, `AEAD_Advantage` of `A` is at most `AEAD_CCA_Advantage` of the
  adversary `AEAD_CPA_to_CCA pt ad A`, which asks one encryption query.

## Usage in EDHOC

EDHOC uses AES-CCM-16-64-128 for:
1. Encrypting message 3 (containing initiator's credential + MAC_3)
2. Encrypting message 4 (optional, containing EAD_4)
3. Message 2 uses XOR encryption (KEYSTREAM_2), not AEAD

## References

* Rogaway, *Authenticated-Encryption with Associated-Data*, CCS 2002
* Rogaway & Shrimpton, *A Provable-Security Treatment of the Key-Wrap Problem*,
  EUROCRYPT 2006
* Boneh & Shoup, *A Graduate Course in Applied Cryptography*, §9.5
* RFC 9528 — EDHOC, Section 5.3-5.4
-/

@[expose] public section

namespace CatCrypt.Crypto.Assumptions

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal

variable {W : Type} [SampleableType W] {C : Type} [SampleableType C]

/-! ## AEAD Definition -/

/-- Abstract AEAD scheme with keys, plaintexts and associated data in `W` and
ciphertexts in `C` (default `W`).

- `encrypt key plaintext ad` → ciphertext
- `decrypt key ciphertext ad` → `some plaintext`, or `none` on rejection -/
structure AEADDef (W : Type) [SampleableType W] (C : Type := W) where
  /-- AEAD encryption: (key, plaintext, associated_data) → ciphertext.
  Models `aes_ccm_encrypt_tag_8` in lakers' `Crypto` trait. -/
  encrypt : W → W → W → C
  /-- AEAD decryption: (key, ciphertext, associated_data) → plaintext, or
  `none` when the ciphertext is rejected.
  Models `aes_ccm_decrypt_tag_8` in lakers' `Crypto` trait. -/
  decrypt : W → C → W → Option W

/-! ## Single-sample real-or-random game -/

/-- Type of AEAD adversary: receives a ciphertext and must distinguish
real encryption from random. -/
abbrev AEAD_Adversary (C : Type) := C → SPComp Bool

/-- AEAD real game: sample random key, encrypt the adversary's chosen plaintext. -/
noncomputable def AEAD_Game_Real (D : AEADDef W C) (pt ad : W)
    (A : AEAD_Adversary C) : SPComp Bool := do
  let key ← SPComp.sample W
  let ct := D.encrypt key pt ad
  A ct

/-- AEAD ideal game: adversary receives a random ciphertext. -/
noncomputable def AEAD_Game_Ideal (A : AEAD_Adversary C) : SPComp Bool := do
  let ct ← SPComp.sample C
  A ct

/-- Advantage in distinguishing one encryption of `pt` under a uniform key from
a uniform ciphertext. -/
noncomputable def AEAD_Advantage (D : AEADDef W C) (pt ad : W)
    (A : AEAD_Adversary C) : ℝ≥0∞ :=
  Advantage (AEAD_Game_Real D pt ad A) (AEAD_Game_Ideal A)

/-! ## IsPure Proofs -/

omit [SampleableType C] in
theorem AEAD_Game_Real_isPure (D : AEADDef W C) (pt ad : W)
    (A : AEAD_Adversary C) (hA : ∀ x, SPComp.IsPure (A x)) :
    SPComp.IsPure (AEAD_Game_Real D pt ad A) := by
  unfold AEAD_Game_Real
  apply SPComp.bind_isPure (SPComp.sample_isPure _); intro key
  exact hA _

theorem AEAD_Game_Ideal_isPure (A : AEAD_Adversary C)
    (hA : ∀ x, SPComp.IsPure (A x)) :
    SPComp.IsPure (AEAD_Game_Ideal A) := by
  unfold AEAD_Game_Ideal
  apply SPComp.bind_isPure (SPComp.sample_isPure _); intro ct
  exact hA ct

/-! ## Adaptive authenticated-encryption game

The adversary is an adaptive oracle adversary (`OracleAdv`). A query
`.inl (pt, ad)` asks for an encryption and is answered `.inl ct`; a query
`.inr (ct, ad)` asks for a decryption and is answered `.inr` of a plaintext
option.

The ideal encryption oracle is a lazily sampled random function of `(pt, ad)`;
the ideal decryption oracle answers from the log of encryption answers. A
scheme is secure when no adversary distinguishes `(encrypt key, decrypt key)`
from this pair: encryption hides the plaintext and every ciphertext not
produced by the encryption oracle is rejected (Rogaway–Shrimpton 2006,
deterministic authenticated encryption). -/

/-- Queries of the authenticated-encryption game: `.inl (pt, ad)` asks for an
encryption, `.inr (ct, ad)` for a decryption. -/
abbrev AEAD_CCA_Query (W C : Type) := (W × W) ⊕ (C × W)

/-- Answers of the authenticated-encryption game: `.inl ct` to an encryption
query, `.inr` of a plaintext option to a decryption query. -/
abbrev AEAD_CCA_Answer (W C : Type) := C ⊕ Option W

/-- Adaptive adversary of the authenticated-encryption game. -/
abbrev AEAD_CCA_Adversary (W C : Type) :=
  OracleAdv (AEAD_CCA_Query W C) (AEAD_CCA_Answer W C) Bool

/-- The real oracles under `key`: `encrypt key` and `decrypt key`. -/
noncomputable def aeadRealOracle (D : AEADDef W C) (key : W) :
    Unit → AEAD_CCA_Query W C → PMF (AEAD_CCA_Answer W C × Unit)
  | _, .inl (pt, ad) => PMF.pure (.inl (D.encrypt key pt ad), ())
  | _, .inr (ct, ad) => PMF.pure (.inr (D.decrypt key ct ad), ())

/-- Decryption from the log `((pt, ad), ct)` of encryption answers: the
plaintext of the most recent entry with ciphertext `ct` and associated data
`ad`, and `none` if there is no such entry. -/
def aeadLogDecrypt (log : List ((W × W) × C)) (ct : C) (ad : W) : Option W :=
  (log.find? fun e => decide (e.2 = ct ∧ e.1.2 = ad)).map fun e => e.1.1

/-- The ideal oracles with the log `((pt, ad), ct)` as state. Encryption of a
recorded `(pt, ad)` returns the recorded ciphertext; encryption of a fresh
`(pt, ad)` returns a uniform ciphertext and records it. Decryption answers
with `aeadLogDecrypt`. -/
noncomputable def aeadIdealOracle :
    List ((W × W) × C) → AEAD_CCA_Query W C → PMF (AEAD_CCA_Answer W C × List ((W × W) × C))
  | log, .inl (pt, ad) =>
    match log.lookup (pt, ad) with
    | some ct => PMF.pure (.inl ct, log)
    | none => (PMF.uniformOfFintype C).map fun ct => (.inl ct, ((pt, ad), ct) :: log)
  | log, .inr (ct, ad) => PMF.pure (.inr (aeadLogDecrypt log ct ad), log)

/-- Real authenticated-encryption game: sample a key, run `A` against
`aeadRealOracle D key`. -/
noncomputable def AEAD_CCA_Game_Real (D : AEADDef W C)
    (A : AEAD_CCA_Adversary W C) : SPComp Bool :=
  PRPPRF.pmfGame ((PMF.uniformOfFintype W).bind fun key =>
    (OracleAdv.run (aeadRealOracle D key) A ()).map Prod.fst)

/-- Ideal authenticated-encryption game: run `A` against `aeadIdealOracle`
from the empty log. -/
noncomputable def AEAD_CCA_Game_Ideal (A : AEAD_CCA_Adversary W C) : SPComp Bool :=
  PRPPRF.pmfGame ((OracleAdv.run aeadIdealOracle A []).map Prod.fst)

/-- Advantage of `A` in distinguishing the real encryption and decryption
oracles of `D` from the ideal ones. -/
noncomputable def AEAD_CCA_Advantage (D : AEADDef W C)
    (A : AEAD_CCA_Adversary W C) : ℝ≥0∞ :=
  Advantage (AEAD_CCA_Game_Real D A) (AEAD_CCA_Game_Ideal A)

/-- The adversary of the authenticated-encryption game that asks one
encryption query `(pt, ad)` and runs the single-sample adversary `A` on the
answer. -/
noncomputable def AEAD_CPA_to_CCA (pt ad : W) (A : C → PMF Bool) :
    AEAD_CCA_Adversary W C :=
  .query (.inl (pt, ad)) fun r =>
    match r with
    | .inl ct => .rand (A ct) .ret
    | .inr _ => .ret false

/-- `prTrue` of a heap-independent game is the probability of `true`. -/
theorem prTrue_pmfGame (p : PMF Bool) (h₀ : Heap) : prTrue (PRPPRF.pmfGame p) h₀ = p true := by
  have h := PRPPRF.prTrue_pmfGame_map p id h₀
  rw [PMF.map_id] at h
  rw [h, show {x : Bool | id x = true} = {true} from by ext x; simp,
    PMF.toOuterMeasure_apply_singleton]

/-- `prTrue` of a uniform sample followed by a heap-independent game. -/
theorem prTrue_sample_bind_pmfGame {α : Type} [Fintype α] [Nonempty α]
    (f : α → PMF Bool) (h₀ : Heap) :
    prTrue (SPComp.bind (SPComp.sample α) fun a => PRPPRF.pmfGame (f a)) h₀ =
      ((PMF.uniformOfFintype α).bind f) true := by
  rw [prTrue_bind_sample, PMF.bind_apply, tsum_fintype]
  simp only [prTrue_pmfGame, PMF.uniformOfFintype_apply]

/-- **The single-sample game reduces to the authenticated-encryption game.**
For a single-sample adversary given by the distribution `A ct` of its guess,
the single-sample advantage equals the advantage of `AEAD_CPA_to_CCA pt ad A`
in the authenticated-encryption game. -/
theorem AEAD_CPA_le_CCA (D : AEADDef W C) (pt ad : W) (A : C → PMF Bool) :
    AEAD_Advantage D pt ad (fun ct => PRPPRF.pmfGame (A ct)) ≤
    AEAD_CCA_Advantage D (AEAD_CPA_to_CCA pt ad A) := by
  refine le_of_eq ?_
  have hreal : prTrue (AEAD_Game_Real D pt ad fun ct => PRPPRF.pmfGame (A ct)) Heap.empty =
      prTrue (AEAD_CCA_Game_Real D (AEAD_CPA_to_CCA pt ad A)) Heap.empty := by
    rw [AEAD_CCA_Game_Real, prTrue_pmfGame]
    refine (prTrue_sample_bind_pmfGame (fun key => A (D.encrypt key pt ad)) _).trans ?_
    congr 2
    funext key
    simp [AEAD_CPA_to_CCA, aeadRealOracle, PMF.map_bind, PMF.pure_map, PMF.bind_pure]
  have hideal : prTrue (AEAD_Game_Ideal fun ct => PRPPRF.pmfGame (A ct)) Heap.empty =
      prTrue (AEAD_CCA_Game_Ideal (W := W) (AEAD_CPA_to_CCA pt ad A)) Heap.empty := by
    rw [AEAD_CCA_Game_Ideal, prTrue_pmfGame]
    refine (prTrue_sample_bind_pmfGame A _).trans ?_
    congr 1
    simp only [AEAD_CPA_to_CCA, aeadIdealOracle, OracleAdv.run_query, OracleAdv.run_rand,
      OracleAdv.run_ret, List.lookup_nil, PMF.map_bind, PMF.bind_map, Function.comp_def,
      PMF.pure_map, PMF.bind_pure]
  simp only [AEAD_Advantage, AEAD_CCA_Advantage, Advantage, hreal, hideal]

/-! ## Keyed AEAD game (key-dependent messages)

`AEAD_Keyed_Advantage` is the single-sample real-or-random game in which the
plaintext and associated data depend on the key via `pt ad : W → W`. The
adversary sees the ciphertext only. Standard `AEAD_Advantage` does not imply
`AEAD_Keyed_Advantage`; key-dependent-message security in general needs
additional assumptions (Black–Rogaway–Shrimpton, SAC 2003). -/

/-- AEAD keyed real game: sample a key and output the ciphertext of the
key-dependent plaintext and associated data. -/
noncomputable def aead_keyed_real (D : AEADDef W C)
    (pt ad : W → W) : SPComp C :=
  SPComp.bind (SPComp.sample W) (fun key =>
    SPComp.pure (D.encrypt key (pt key) (ad key)))

/-- AEAD keyed ideal game: a uniform ciphertext. -/
noncomputable def aead_keyed_ideal : SPComp C :=
  SPComp.sample C

/-- Advantage in distinguishing the ciphertext of key-dependent plaintext and
associated data from a uniform ciphertext. -/
noncomputable def AEAD_Keyed_Advantage (D : AEADDef W C) (pt ad : W → W)
    (A : C → SPComp Bool) : ENNReal :=
  AdvantageA (aead_keyed_real D pt ad) aead_keyed_ideal A

omit [SampleableType C] in
theorem aead_keyed_real_isPure (D : AEADDef W C) (pt ad : W → W) :
    SPComp.IsPure (aead_keyed_real D pt ad) := by
  unfold aead_keyed_real
  apply SPComp.bind_isPure (SPComp.sample_isPure _); intro _
  exact SPComp.pure_isPure _

theorem aead_keyed_ideal_isPure : SPComp.IsPure (aead_keyed_ideal (C := C)) :=
  SPComp.sample_isPure _

end CatCrypt.Crypto.Assumptions
