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
* `PKE.BOWp` — the uniform-plaintext correctness adversary of `ow_perfect`

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

/-- OW-CPA with the decryption check: the game returns whether the adversary's
answer equals the decryption of the challenge ciphertext under the secret key.
It differs from `OW_CPA` only when decryption of the challenge fails
(`ow_perfect`).

    EasyCrypt: `OW_CPA(S, A).main_perfect()`. -/
noncomputable def OW_CPA_perfect (find : S.PK → S.CT → SDistr (Option S.PT)) : SDistr Bool := do
  let (pk, sk) ← S.kg
  let m ← SDistr.uniform S.PT
  let c ← S.enc pk m
  let m' ← find pk c
  let md ← S.dec sk c
  SDistr.pure (m' == md)

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

/-- BOWp: the correctness adversary of `ow_perfect`, which returns a uniform
plaintext. `Correctness_Adv S (BOWp S)` is the decryption-failure probability
of an honestly encrypted uniform plaintext.

    EasyCrypt: `BOWp(S, A)`. -/
noncomputable def BOWp : S.PK → S.SK → SDistr S.PT := fun _pk _sk =>
  SDistr.uniform S.PT

/-- `bind` is subadditive in its continuation at a fixed outcome. -/
theorem _root_.CatCrypt.Prob.SDistr.bind_apply_le_add {α β : Type} (d : SDistr α)
    (f g h : α → SDistr β) (o : Option β) (hfgh : ∀ a, f a o ≤ g a o + h a o) :
    (d.bind f) o ≤ (d.bind g) o + (d.bind h) o := by
  simp only [SDistr.bind, PMF.bind_apply]
  rw [← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun oa => ?_
  cases oa with
  | none => exact le_self_add
  | some a => rw [← mul_add]; exact mul_le_mul_right (hfgh a) _

/-- Binding a sub-distribution before a computation that ignores the result
does not increase the probability of a value. -/
theorem _root_.CatCrypt.Prob.SDistr.bind_const_apply_some_le {α β : Type} (d : SDistr α)
    (z : SDistr β) (b : β) :
    (d.bind fun _ => z) (some b) ≤ z (some b) := by
  simp only [SDistr.bind, PMF.bind_apply]
  calc ∑' oa, d oa * (match oa with | some _ => z | none => SDistr.fail) (some b)
      ≤ ∑' oa, d oa * z (some b) := ENNReal.tsum_le_tsum fun oa => by
        cases oa with
        | none => simp [SDistr.fail]
        | some a => exact le_rfl
    _ = z (some b) := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- Binding a lossless sub-distribution before a point mass leaves the point
mass unchanged at every value. -/
theorem _root_.CatCrypt.Prob.SDistr.bind_const_pure_apply_some {α β : Type} (d : SDistr α)
    (hd : d none = 0) (x b : β) :
    (d.bind fun _ => SDistr.pure x) (some b) = SDistr.pure x (some b) := by
  simp only [SDistr.bind, PMF.bind_apply]
  have h1 : ∑' a, d (some a) = 1 := by
    have h := PMF.tsum_coe d
    rwa [SDistr.tsum_option_eq_add, hd, zero_add] at h
  rw [SDistr.tsum_option_eq_add, hd, zero_mul, zero_add]
  dsimp only
  rw [ENNReal.tsum_mul_right, h1, one_mul]

/-- OW with and without the decryption check differ by at most the
decryption-failure probability of an honestly encrypted uniform plaintext,
for a scheme whose decryption never fails to terminate (`S.dec sk c none = 0`).
The two games agree whenever the challenge ciphertext decrypts to the
encrypted plaintext.

    EasyCrypt: `ow_perfect`. -/
theorem ow_perfect (hdec : ∀ sk c, S.dec sk c none = 0)
    (find : S.PK → S.CT → SDistr (Option S.PT)) :
    UCMonad.SDistrUC.absDiffD
      (UCMonad.SDistrUC.prTrueD (OW_CPA S find))
      (UCMonad.SDistrUC.prTrueD (OW_CPA_perfect S find)) ≤
    UCMonad.SDistrUC.prTrueD (Correctness_Adv S (BOWp S)) := by
  -- The three tests at a decryption result `md`.
  have hpt : ∀ (m : S.PT) (m' md : Option S.PT),
      SDistr.pure (m' == some m) (some true) ≤
        SDistr.pure (m' == md) (some true) + SDistr.pure (decide (md ≠ some m)) (some true) ∧
      SDistr.pure (m' == md) (some true) ≤
        SDistr.pure (m' == some m) (some true) + SDistr.pure (decide (md ≠ some m)) (some true) := by
    intro m m' md
    simp only [SDistr.pure_apply_some]
    by_cases h : md = some m
    · subst h; simp
    · simp only [h, ne_eq, not_false_eq_true, decide_true, if_pos]
      constructor <;> exact le_add_left (by split_ifs <;> simp)
  -- The two inequalities after the challenge ciphertext `c` is fixed.
  have hinner : ∀ (pk : S.PK) (sk : S.SK) (m : S.PT) (c : S.CT),
      ((find pk c).bind fun m' => SDistr.pure (m' == some m)) (some true) ≤
        ((find pk c).bind fun m' => (S.dec sk c).bind fun md => SDistr.pure (m' == md))
          (some true) +
        ((S.dec sk c).bind fun md => SDistr.pure (decide (md ≠ some m))) (some true) ∧
      ((find pk c).bind fun m' => (S.dec sk c).bind fun md => SDistr.pure (m' == md))
          (some true) ≤
        ((find pk c).bind fun m' => SDistr.pure (m' == some m)) (some true) +
        ((S.dec sk c).bind fun md => SDistr.pure (decide (md ≠ some m))) (some true) := by
    intro pk sk m c
    have hZ := SDistr.bind_const_apply_some_le (find pk c)
      ((S.dec sk c).bind fun md => SDistr.pure (decide (md ≠ some m))) true
    have hconst := fun x => SDistr.bind_const_pure_apply_some (S.dec sk c) (hdec sk c) x true
    constructor
    · refine (SDistr.bind_apply_le_add _ _ _ _ _ fun m' => ?_).trans (add_le_add le_rfl hZ)
      rw [← hconst]
      exact SDistr.bind_apply_le_add _ _ _ _ _ fun md => (hpt m m' md).1
    · refine (SDistr.bind_apply_le_add _ _ _ _ _ fun m' => ?_).trans (add_le_add le_rfl hZ)
      rw [← hconst]
      exact SDistr.bind_apply_le_add _ _ _ _ _ fun md => (hpt m m' md).2
  unfold UCMonad.SDistrUC.prTrueD UCMonad.SDistrUC.absDiffD OW_CPA OW_CPA_perfect
    Correctness_Adv BOWp
  refine max_le (tsub_le_iff_left.mpr ?_) (tsub_le_iff_left.mpr ?_)
  · refine SDistr.bind_apply_le_add _ _ _ _ _ fun x => ?_
    obtain ⟨pk, sk⟩ := x
    refine SDistr.bind_apply_le_add _ _ _ _ _ fun m => ?_
    refine SDistr.bind_apply_le_add _ _ _ _ _ fun c => ?_
    exact (hinner pk sk m c).1
  · refine SDistr.bind_apply_le_add _ _ _ _ _ fun x => ?_
    obtain ⟨pk, sk⟩ := x
    refine SDistr.bind_apply_le_add _ _ _ _ _ fun m => ?_
    refine SDistr.bind_apply_le_add _ _ _ _ _ fun c => ?_
    exact (hinner pk sk m c).2

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
