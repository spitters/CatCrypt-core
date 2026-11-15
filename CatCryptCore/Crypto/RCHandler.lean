/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.RC
public import CatCryptCore.Relational.Approx

/-!
# Robust compilation over a class of handlers

`RobustCompilationH HC ε π F` is robust compilation `RobustCompilation ε (π h) (F h)` at every
handler `h` of a class `HC`. A compiled program and its source are interpreted under a handler of
the linked functions, and the statement quantifies over the handlers the linked code may realise.

The bound is derived from a coupling. Let a source computation `c₁` and a target computation `c₂`
be related by `rHoare` at equal heaps, with a postcondition under which either the source read-back
`k₁` fails at the source leaf, or the two read-backs agree and the heaps are equal. Then the
read-backs `c₁.bind k₁` and `c₂.bind k₂` are related at equality with grade the failure weight of
the source read-back (`rHoareApprox_bind_of_rHoare_failOr`), and their statistical distance is at
most that weight. Robust compilation follows through `RC_iff_sdist`.

## Main definitions

* `RobustCompilationH`: robust compilation at every handler of a class.

## Main results

* `liftRApprox_bind_of_coupling_failOr`: the distribution-level form of the derivation.
* `rHoareApprox_bind_of_rHoare_failOr`: the graded judgment of the read-backs.
* `sdist_bind_le_of_rHoare_failOr`: the statistical distance of the read-backs.
* `robustCompilationH_iff_sdist`: robust compilation over a class iff the statistical distance
  is bounded at every handler of the class.
* `robustCompilationH_of_rHoare`: robust compilation over a class from couplings at every handler.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto

open CatCrypt.Core CatCrypt.Prob CatCrypt.Relational

open scoped ENNReal

/-! ## Robust compilation over a class of handlers -/

/-- **Robust compilation over a class of handlers**: at every handler `h` satisfying `HC`,
    replacing `F h` by `π h` preserves security in every context and for every distinguisher,
    up to `ε`. -/
def RobustCompilationH {H I O : Type} (HC : H → Prop) (ε : ℝ≥0∞) (π F : H → I → SPComp O) :
    Prop :=
  ∀ h, HC h → RobustCompilation ε (π h) (F h)

/-- Robust compilation over a class iff the statistical distance is at most `ε` at every handler
    of the class. -/
theorem robustCompilationH_iff_sdist {H I O : Type} (HC : H → Prop) (ε : ℝ≥0∞)
    (π F : H → I → SPComp O) :
    RobustCompilationH HC ε π F ↔ ∀ h, HC h → sdist (π h) (F h) ≤ ε :=
  forall_congr' fun h => imp_congr_right fun _ => RC_iff_sdist (π h) (F h) ε

/-! ## The derivation from a coupling -/

section Derivation

variable {A B O : Type}

/-- **Read-backs of coupled distributions.** Let a coupling of `d₁` and `d₂` relate only pairs
    at which the source read-back `K₁` fails or agrees with the target read-back `K₂`. Then the
    read-backs are related at equality with grade the failure weight of the source read-back. -/
theorem liftRApprox_bind_of_coupling_failOr {d₁ : SDistr A} {d₂ : SDistr B}
    (c : Coupling d₁ d₂) (K₁ : A → SDistr O) (K₂ : B → SDistr O)
    (hc : ∀ p q, c.joint (some (p, q)) ≠ 0 → K₁ p = SDistr.fail ∨ K₁ p = K₂ q) :
    liftRApprox ((d₁.bind K₁) none) Eq (d₁.bind K₁) (d₂.bind K₂) := by
  have hD₁ : ∀ y, (d₁.bind K₁) (some y) =
      ∑' p, ∑' q, c.joint (some (p, q)) * K₁ p (some y) := by
    intro y
    rw [SDistr.bind_apply_some]
    refine tsum_congr fun p => ?_
    rw [← c.left_marginal_sum p, ENNReal.tsum_mul_right]
  have hD₂ : ∀ y, (d₂.bind K₂) (some y) =
      ∑' p, ∑' q, c.joint (some (p, q)) * K₂ q (some y) := by
    intro y
    rw [SDistr.bind_apply_some, ENNReal.tsum_comm]
    refine tsum_congr fun q => ?_
    rw [← c.right_marginal_sum q, ENNReal.tsum_mul_right]
  have hle : ∀ p q y, c.joint (some (p, q)) * K₁ p (some y) ≤
      c.joint (some (p, q)) * K₂ q (some y) := by
    intro p q y
    by_cases h0 : c.joint (some (p, q)) = 0
    · simp [h0]
    · rcases hc p q h0 with h | h
      · simp [h, SDistr.fail_apply_some]
      · rw [h]
  have hle₂ : ∀ p q y, c.joint (some (p, q)) * K₂ q (some y) ≤
      c.joint (some (p, q)) * K₁ p (some y) +
        c.joint (some (p, q)) * K₁ p none * K₂ q (some y) := by
    intro p q y
    by_cases h0 : c.joint (some (p, q)) = 0
    · simp [h0]
    · rcases hc p q h0 with h | h
      · simp [h, SDistr.fail_apply_some, SDistr.fail_apply_none]
      · rw [h]
        exact le_self_add
  have hmass : ∀ q, ∑' y, K₂ q (some y) ≤ 1 := by
    intro q
    have hone : K₂ q none + ∑' y, K₂ q (some y) = 1 := by
      rw [← SDistr.tsum_option_eq_add]
      exact (K₂ q).tsum_coe
    exact hone ▸ le_add_self
  refine liftRApprox_eq_of_tv ?_ ?_
  · refine le_of_eq_of_le (ENNReal.tsum_eq_zero.mpr fun y => tsub_eq_zero_of_le ?_) zero_le
    rw [hD₁, hD₂]
    exact ENNReal.tsum_le_tsum fun p => ENNReal.tsum_le_tsum fun q => hle p q y
  · calc tvMargin (d₂.bind K₂) (d₁.bind K₁)
        ≤ ∑' y, ∑' p, ∑' q, c.joint (some (p, q)) * K₁ p none * K₂ q (some y) := by
          refine ENNReal.tsum_le_tsum fun y => tsub_le_iff_left.mpr ?_
          rw [hD₁, hD₂, ← ENNReal.tsum_add]
          refine ENNReal.tsum_le_tsum fun p => ?_
          rw [← ENNReal.tsum_add]
          exact ENNReal.tsum_le_tsum fun q => hle₂ p q y
      _ = ∑' p, ∑' q, c.joint (some (p, q)) * K₁ p none * ∑' y, K₂ q (some y) := by
          rw [ENNReal.tsum_comm]
          refine tsum_congr fun p => ?_
          rw [ENNReal.tsum_comm]
          exact tsum_congr fun q => ENNReal.tsum_mul_left
      _ ≤ ∑' p, ∑' q, c.joint (some (p, q)) * K₁ p none :=
          ENNReal.tsum_le_tsum fun p => ENNReal.tsum_le_tsum fun q =>
            mul_le_of_le_one_right' (hmass q)
      _ = ∑' p, d₁ (some p) * K₁ p none :=
          tsum_congr fun p => by rw [← c.left_marginal_sum p, ENNReal.tsum_mul_right]
      _ ≤ (d₁.bind K₁) none := by
          rw [SDistr.bind_apply_none]
          exact le_add_self

/-- **Graded judgment of the read-backs.** Let `c₁` and `c₂` be related by `rHoare` at equal
    heaps with a postcondition under which the source read-back `k₁` fails, or the read-backs
    agree at equal heaps. The read-backs are related at equality with grade `δ`, a bound of the
    failure weight of the source read-back. -/
theorem rHoareApprox_bind_of_rHoare_failOr {α β : Type} {c₁ : SPComp α} {c₂ : SPComp β}
    {Q : RPost α β} (hc : rHoare eqPre c₁ c₂ Q) (k₁ : α → SPComp O) (k₂ : β → SPComp O)
    (hQ : ∀ a s₁ b s₂, Q a s₁ b s₂ → k₁ a = SPComp.fail ∨ (k₁ a = k₂ b ∧ s₁ = s₂))
    {δ : ℝ≥0∞} (hδ : ∀ s, (c₁.bind k₁) s none ≤ δ) :
    rHoareApprox δ eqPre (c₁.bind k₁) (c₂.bind k₂) eqPost := by
  intro s₀ s heq
  obtain rfl : s₀ = s := heq
  obtain ⟨c, hsat⟩ := hc s₀ s₀ rfl
  refine liftRApprox_mono_rel (fun p₁ p₂ hp => pairPost_of_eq hp)
    (liftRApprox_mono_eps (hδ s₀) ?_)
  refine liftRApprox_bind_of_coupling_failOr c (fun p => k₁ p.1 p.2) (fun q => k₂ q.1 q.2) ?_
  intro p q hpq
  rcases hQ _ _ _ _ (hsat p q hpq) with h | ⟨h, hs⟩
  · left
    rw [h]
    rfl
  · right
    rw [h, hs]

/-- **Statistical distance of the read-backs** of computations coupled as in
    `rHoareApprox_bind_of_rHoare_failOr`: at most a bound `δ` of the failure weight of the source
    read-back. -/
theorem sdist_bind_le_of_rHoare_failOr {α β : Type} {c₁ : SPComp α} {c₂ : SPComp β}
    {Q : RPost α β} (hc : rHoare eqPre c₁ c₂ Q) (k₁ : α → SPComp O) (k₂ : β → SPComp O)
    (hQ : ∀ a s₁ b s₂, Q a s₁ b s₂ → k₁ a = SPComp.fail ∨ (k₁ a = k₂ b ∧ s₁ = s₂))
    {δ : ℝ≥0∞} (hδ : ∀ s, (c₁.bind k₁) s none ≤ δ) :
    sdist (fun _ : Unit => c₁.bind k₁) (fun _ : Unit => c₂.bind k₂) ≤ δ :=
  rHoareApprox_sdist (rHoareApprox_bind_of_rHoare_failOr hc k₁ k₂ hQ hδ)

/-- **Robust compilation over a class of handlers from couplings.** At every handler `h` of the
    class and every input `i`, let the source computation `c₁ h i` and the target computation
    `c₂ h i` be coupled at equal heaps with a postcondition `Q` under which the source read-back
    `k₁` fails, or the read-backs agree at equal heaps, and let `ε` bound the failure weight of the
    source read-back. The read-backs are robustly compiled at `ε` over the class. -/
theorem robustCompilationH_of_rHoare {H I α β : Type} {HC : H → Prop}
    {c₁ : H → I → SPComp α} {c₂ : H → I → SPComp β} {Q : RPost α β}
    (hc : ∀ h, HC h → ∀ i, rHoare eqPre (c₁ h i) (c₂ h i) Q)
    (k₁ : α → SPComp O) (k₂ : β → SPComp O)
    (hQ : ∀ a s₁ b s₂, Q a s₁ b s₂ → k₁ a = SPComp.fail ∨ (k₁ a = k₂ b ∧ s₁ = s₂))
    {ε : ℝ≥0∞} (hε : ∀ h, HC h → ∀ i s, ((c₁ h i).bind k₁) s none ≤ ε) :
    RobustCompilationH HC ε (fun h i => (c₁ h i).bind k₁) (fun h i => (c₂ h i).bind k₂) := by
  refine (robustCompilationH_iff_sdist _ _ _ _).mpr fun h hh => ?_
  refine iSup_le fun D => iSup_le fun i => iSup_le fun s => ?_
  exact rHoareApprox_absDiff_prTrue
    (rHoareApprox_bind_of_rHoare_failOr (hc h hh i) k₁ k₂ hQ (hε h hh i)) D s

end Derivation

end CatCrypt.Crypto
