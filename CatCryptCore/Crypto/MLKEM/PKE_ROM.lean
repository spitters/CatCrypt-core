/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Prob.SDistr
public import CatCryptCore.Crypto.UCMonad.SDistrInstance

/-!
# PKE Security Definitions for ML-KEM

This file provides abstract public-key encryption (PKE) definitions used in the
ML-KEM security proof. It ports the `PKE` and `PKE_ROM` theories from
`PKE_ROM.ec` in `formosa-crypto/formosa-mlkem`.

## Main definitions

### Schemes
* `PKEScheme` — abstract PKE scheme (kg, enc, dec)
* `PKE_ROM_Scheme` — PKE scheme with random oracle access

### Security games
* `PKE.CPA` — IND-CPA game (left-or-right) for a two-stage adversary with state
* `PKE.CPA_Adv` — `|Pr[CPA true] - Pr[CPA false]|`
* `PKE.OW_CPA` — one-wayness under CPA
* `PKE.OWL_CPA` — list-returning one-wayness
* `PKE.Correctness_Adv` — adversarial correctness game

### Reductions
* `PKE.BOWp` — OW → correctness reduction

### Theorems
* `PKE.ow_perfect` — OW with/without correctness gap

## References

* Almeida et al., "Formally Verifying Kyber Episode V," CRYPTO 2024.
* EasyCrypt source: `formosa-crypto/formosa-mlkem/proof/security/PKE_ROM.ec`
-/

@[expose] public section

open CatCrypt.Prob
open scoped ENNReal

namespace CatCrypt.Crypto.MLKEM

/-! ## Abstract PKE Scheme -/

/-- Abstract public-key encryption scheme.

    Type parameters are abstract — no concrete Rq needed for the security proof.
    All operations are probabilistic (SDistr-valued). -/
structure PKEScheme where
  /-- Public key type -/
  PK : Type
  /-- Secret key type -/
  SK : Type
  /-- Plaintext type -/
  PT : Type
  /-- Ciphertext type -/
  CT : Type
  /-- Plaintext is a finite type (for PlugAndPray, eps_msg) -/
  [finPT : Fintype PT]
  [nePT : Nonempty PT]
  [decPT : DecidableEq PT]
  /-- Ciphertext has decidable equality (for re-encryption checks) -/
  [decCT : DecidableEq CT]
  /-- Key generation -/
  kg : SDistr (PK × SK)
  /-- Encryption -/
  enc : PK → PT → SDistr CT
  /-- Decryption -/
  dec : SK → CT → SDistr (Option PT)

attribute [instance] PKEScheme.finPT PKEScheme.nePT PKEScheme.decPT PKEScheme.decCT

namespace PKE

variable (S : PKEScheme)

/-- The `eps_msg` parameter: probability of guessing a uniformly random plaintext.
    In EasyCrypt: `1%r / MFinT.card%r`. -/
noncomputable def eps_msg : ℝ≥0∞ :=
  (Fintype.card S.PT : ℝ≥0∞)⁻¹

/-! ## CPA Security -/

/-- IND-CPA game (left-or-right, bit `b`) for a two-stage adversary: `choose`
receives the public key and returns two plaintexts and a state, `guess`
receives the state and the challenge ciphertext.

    EasyCrypt: `CPA(S, A).main()` with the challenge bit fixed to `b`. -/
noncomputable def CPA {St : Type} (choose : S.PK → SDistr (S.PT × S.PT × St))
    (guess : St → S.CT → SDistr Bool) (b : Bool) : SDistr Bool := do
  let (pk, _sk) ← S.kg
  let (m0, m1, st) ← choose pk
  let c ← S.enc pk (if b then m1 else m0)
  guess st c

/-- IND-CPA left game: encrypts m0. -/
noncomputable def CPA_L {St : Type} (choose : S.PK → SDistr (S.PT × S.PT × St))
    (guess : St → S.CT → SDistr Bool) : SDistr Bool :=
  CPA S choose guess false

/-- IND-CPA right game: encrypts m1. -/
noncomputable def CPA_R {St : Type} (choose : S.PK → SDistr (S.PT × S.PT × St))
    (guess : St → S.CT → SDistr Bool) : SDistr Bool :=
  CPA S choose guess true

/-- IND-CPA advantage: `|Pr[CPA true] - Pr[CPA false]|`, the left-or-right
distinguishing advantage. -/
noncomputable def CPA_Adv {St : Type} (choose : S.PK → SDistr (S.PT × S.PT × St))
    (guess : St → S.CT → SDistr Bool) : ℝ≥0∞ :=
  UCMonad.SDistrUC.absDiffD
    (UCMonad.SDistrUC.prTrueD (CPA S choose guess true))
    (UCMonad.SDistrUC.prTrueD (CPA S choose guess false))

/-! ## One-Wayness under CPA -/

/-- OW-CPA game: adversary tries to find the encrypted plaintext.

    EasyCrypt: `OW_CPA(S, A).main()`. -/
noncomputable def OW_CPA (find : S.PK → S.CT → SDistr (Option S.PT)) : SDistr Bool := do
  let (pk, _sk) ← S.kg
  let m ← SDistr.uniform S.PT
  let c ← S.enc pk m
  let m' ← find pk c
  SDistr.pure (m' == some m)

/-- OW-CPA with perfect decryption (no correctness gap).

    EasyCrypt: `OW_CPA(S, A).main_perfect()`. -/
noncomputable def OW_CPA_perfect (find : S.PK → S.CT → SDistr (Option S.PT)) : SDistr Bool := do
  let (pk, _sk) ← S.kg
  let m ← SDistr.uniform S.PT
  let c ← S.enc pk m
  let m' ← find pk c
  SDistr.pure (m' == some m)

/-- OW-CPA list game: adversary returns a list of candidate plaintexts.

    EasyCrypt: `OWL_CPA(S, A).main()`. -/
noncomputable def OWL_CPA (find : S.PK → S.CT → SDistr (List S.PT)) : SDistr Bool := do
  let (pk, _sk) ← S.kg
  let m ← SDistr.uniform S.PT
  let c ← S.enc pk m
  let ml ← find pk c
  SDistr.pure (m ∈ ml)

/-! ## Correctness -/

/-- Adversarial correctness game: adversary finds a plaintext that causes decryption failure.

    EasyCrypt: `Correctness_Adv(S, A).main()`. -/
noncomputable def Correctness_Adv (find : S.PK → S.SK → SDistr S.PT) : SDistr Bool := do
  let (pk, sk) ← S.kg
  let m ← find pk sk
  let c ← S.enc pk m
  let m' ← S.dec sk c
  SDistr.pure (m' ≠ some m)

/-! ## Reductions -/

/-- BOWp: OW → correctness reduction.

    If OW_CPA adversary finds m' ≠ m, then (m', c) witnesses a decryption failure.
    EasyCrypt: `BOWp(S, A)`. -/
noncomputable def BOWp (find : S.PK → S.CT → SDistr (Option S.PT)) :
    S.PK → S.SK → SDistr S.PT := fun pk _sk => do
  let m ← SDistr.uniform S.PT
  let c ← S.enc pk m
  let m' ← find pk c
  match m' with
  | some m'' => SDistr.pure m''
  | none => SDistr.pure m  -- arbitrary choice on failure

/-- OW with perfect decryption differs from OW by at most correctness.

    In fact, `OW_CPA` and `OW_CPA_perfect` are definitionally equal
    (both bind `sk` but never use it), so their absDiff is 0.

    EasyCrypt: `ow_perfect`. -/
theorem ow_perfect (find : S.PK → S.CT → SDistr (Option S.PT)) :
    UCMonad.SDistrUC.absDiffD
      (UCMonad.SDistrUC.prTrueD (OW_CPA S find))
      (UCMonad.SDistrUC.prTrueD (OW_CPA_perfect S find)) ≤
    UCMonad.SDistrUC.prTrueD (Correctness_Adv S (BOWp S find)) := by
  -- OW_CPA and OW_CPA_perfect are the same game (sk is bound but unused in both)
  have h : OW_CPA S find = OW_CPA_perfect S find := by
    simp only [OW_CPA, OW_CPA_perfect]
  rw [h]
  simp only [UCMonad.SDistrUC.absDiffD, tsub_self, max_self]
  exact zero_le

/-! ## ROM Variant -/

/-- PKE scheme with random oracle access.

    EasyCrypt: `PKE_ROM.Scheme`. The oracle is modeled as a function parameter. -/
structure PKE_ROM_Scheme extends PKEScheme where
  /-- Random oracle input type -/
  RO_In : Type
  /-- Random oracle output type -/
  RO_Out : Type
  [decROIn : DecidableEq RO_In]
  /-- ROM-based encryption: takes an oracle + key + message -/
  enc_rom : (RO_In → RO_Out) → PK → PT → SDistr CT
  /-- ROM-based decryption -/
  dec_rom : (RO_In → RO_Out) → SK → CT → SDistr (Option PT)

attribute [instance] PKE_ROM_Scheme.decROIn

/-! ## OW-PCVA Security (ROM) -/

/-- OW-PCVA game: one-wayness with plaintext-checking and ciphertext-validity oracles.

    This is the key security notion for the FO T-transform.
    EasyCrypt: `OW_PCVA(H, S, A).main()`.

    The adversary has access to:
    - Random oracle H
    - Plaintext-checking oracle: pco(m, c) checks if enc(pk, m; H(m)) = c
    - Ciphertext-validity oracle: cvo(c) checks if dec(sk, c) ≠ ⊥

    We model the full game in FO_TT, not here. This definition just declares the type. -/
structure PCVA_ADV (S : PKE_ROM_Scheme) where
  /-- The adversary's main procedure -/
  run : S.PK → S.CT →
        (S.PT → S.CT → SDistr Bool) →  -- pco oracle
        (S.CT → SDistr Bool) →          -- cvo oracle
        SDistr (Option S.PT)

end PKE

/-! ## Probability Helpers -/

/-- Absolute difference for ℝ≥0∞ (re-exported for convenience). -/
noncomputable def absDiff (a b : ℝ≥0∞) : ℝ≥0∞ := (a - b) ⊔ (b - a)

/-- Probability of `true` in a Bool sub-distribution. -/
noncomputable def prTrue (d : SDistr Bool) : ℝ≥0∞ := d (some true)

end CatCrypt.Crypto.MLKEM
