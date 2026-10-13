/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCAdmClass

/-!
# Trace-Relating Secure Compilation

This file defines a quantitative analogue, ours, of the trace relations of Abate et al.
(ESOP 2020), over the per-distinguisher decomposition `ucDistComp`. Their framework is
non-probabilistic: it has trace relations but no distinguishers and no `ε`.

## Trace-Relating Perspective

Abate et al. define compiler correctness when source and target traces are
connected by a relation `R : Trace_S → Trace_T → Prop` (their Def. 1.2, with robust
variants in Thms. 5.1–5.3). In our analogue:
- Source traces = behaviors of `F` (ideal functionality)
- Target traces = behaviors of `π` (real protocol)
- Relation = connected by simulator: `t_π ≈_ε t_{S∘F}`
- `ucDistComp` = per-distinguisher quantitative bound

The key insight: `ucDistComp f g D ≤ ε` says "f and g are ε-related when
observed through test D". We read this as a quantitative analogue of a trace relation.

## Main definitions

* `TraceRelating` — per-distinguisher ε-equivalence (admissible D only)
* `TraceRelatingL1` — per-distinguisher ε-equivalence (all D)

## Main results

* `ucCdist_eq_sInf_traceRelating` — ucCdist is the least `ε` with `TraceRelating f g ε`
* `traceRelatingL1_iff_ucSdist` — `TraceRelatingL1 f g ε ↔ ucSdist f g ≤ ε`
* `traceRelating_comp_right` — composition preserves trace-relating bounds

## References

* Abate, Blanco, Ciobâcă, Durier, Garg, Hrițcu, Patrignani, Tanter, Thibault,
  "Trace-Relating Compiler Correctness and Secure Compilation", ESOP 2020
* Patrignani, Künnemann, Wahby, Cecchetti, "Universal Composability Is Robust
  Compilation", TOPLAS 46(4), 2024
-/

@[expose] public section

open scoped ENNReal

namespace UCMonad

variable {T : Type → Type} [UCMonadCompDist T]

/-! ## Trace-Relating ε-Equivalence -/

/-- Trace-relating ε-equivalence: for all admissible tests D,
    the per-test distance is bounded by ε. -/
def TraceRelating {α β : Type} (f g : α → T β) (ε : ℝ≥0∞) : Prop :=
  ∀ (D : β → T Bool), adm D → UCMonadCompDist.ucDistComp f g D ≤ ε

/-- Level 1 trace-relating: for ALL tests D (no admissibility restriction). -/
def TraceRelatingL1 {α β : Type} (f g : α → T β) (ε : ℝ≥0∞) : Prop :=
  ∀ (D : β → T Bool), UCMonadCompDist.ucDistComp f g D ≤ ε

/-! ## Relationship to ucCdist and ucSdist -/

/-- `ucCdist ≤ ε → TraceRelating ε`: the distance bound gives per-test bounds. -/
theorem traceRelating_of_ucCdist {α β : Type} {f g : α → T β} {ε : ℝ≥0∞}
    (h : ucCdist f g ≤ ε) : TraceRelating f g ε :=
  fun D hD => le_trans
    (le_iSup₂ (f := fun D _ => UCMonadCompDist.ucDistComp f g D) D hD) h

/-- `TraceRelating ε → ucCdist ≤ ε`: if all per-test distances are bounded,
    the sup (ucCdist) is bounded. -/
theorem ucCdist_of_traceRelating {α β : Type} {f g : α → T β} {ε : ℝ≥0∞}
    (h : TraceRelating f g ε) : ucCdist f g ≤ ε :=
  iSup₂_le h

/-- `TraceRelating f g ε ↔ ucCdist f g ≤ ε`. -/
theorem traceRelating_iff_ucCdist {α β : Type} (f g : α → T β) (ε : ℝ≥0∞) :
    TraceRelating f g ε ↔ ucCdist f g ≤ ε :=
  ⟨ucCdist_of_traceRelating, traceRelating_of_ucCdist⟩

/-- ucCdist is the infimum of trace-relating bounds. -/
theorem ucCdist_eq_sInf_traceRelating {α β : Type} (f g : α → T β) :
    ucCdist f g = sInf {ε | TraceRelating f g ε} := by
  apply le_antisymm
  · -- ucCdist ≤ inf: every trace-relating bound ≥ ucCdist, so ucCdist ≤ inf
    apply le_csInf
    · exact ⟨ucCdist f g, traceRelating_of_ucCdist le_rfl⟩
    · intro ε hε; exact ucCdist_of_traceRelating hε
  · -- inf ≤ ucCdist: ucCdist is itself trace-relating, so inf ≤ ucCdist
    apply csInf_le
    · exact ⟨0, fun _ h => zero_le⟩  -- bdd below by 0
    · exact traceRelating_of_ucCdist le_rfl

/-- `ucSdist ≤ ε → TraceRelatingL1 ε`. -/
theorem traceRelatingL1_of_ucSdist {α β : Type} {f g : α → T β} {ε : ℝ≥0∞}
    (h : UCMonadMetric.ucSdist f g ≤ ε) : TraceRelatingL1 f g ε := by
  intro D
  rw [UCMonadCompDist.ucSdist_eq_iSup_distComp] at h
  exact le_trans (le_iSup _ D) h

/-- `TraceRelatingL1 ε → ucSdist ≤ ε`. -/
theorem ucSdist_of_traceRelatingL1 {α β : Type} {f g : α → T β} {ε : ℝ≥0∞}
    (h : TraceRelatingL1 f g ε) : UCMonadMetric.ucSdist f g ≤ ε := by
  rw [UCMonadCompDist.ucSdist_eq_iSup_distComp]
  exact iSup_le h

/-- `TraceRelatingL1 f g ε ↔ ucSdist f g ≤ ε`. -/
theorem traceRelatingL1_iff_ucSdist {α β : Type} (f g : α → T β) (ε : ℝ≥0∞) :
    TraceRelatingL1 f g ε ↔ UCMonadMetric.ucSdist f g ≤ ε :=
  ⟨ucSdist_of_traceRelatingL1, traceRelatingL1_of_ucSdist⟩

/-! ## Structural Properties -/

/-- L1 trace-relating implies L3 trace-relating (forget non-admissible tests). -/
theorem traceRelating_of_traceRelatingL1 {α β : Type} {f g : α → T β} {ε : ℝ≥0∞}
    (h : TraceRelatingL1 f g ε) : TraceRelating f g ε :=
  fun D _ => h D

/-- Reflexivity: f is 0-related to itself. -/
theorem traceRelating_self {α β : Type} (f : α → T β) :
    TraceRelating f f 0 :=
  fun D _ => by simp [UCMonadCompDist.ucDistComp_self]

/-- Symmetry: trace-relating is symmetric. -/
theorem traceRelating_symm {α β : Type} {f g : α → T β} {ε : ℝ≥0∞}
    (h : TraceRelating f g ε) : TraceRelating g f ε :=
  fun D hD => by rw [UCMonadCompDist.ucDistComp_comm]; exact h D hD

/-- Triangle inequality for trace-relating. -/
theorem traceRelating_triangle {α β : Type} {f g h' : α → T β} {ε₁ ε₂ : ℝ≥0∞}
    (h₁ : TraceRelating f g ε₁) (h₂ : TraceRelating g h' ε₂) :
    TraceRelating f h' (ε₁ + ε₂) :=
  fun D hD => le_trans (UCMonadCompDist.ucDistComp_triangle f g h' D)
    (add_le_add (h₁ D hD) (h₂ D hD))

/-- Right composition preserves trace-relating (requires adm k). -/
theorem traceRelating_comp_right {α β γ : Type}
    {f g : α → T β} {k : β → T γ} {ε : ℝ≥0∞}
    (h : TraceRelating f g ε) (hk : adm k) :
    TraceRelating (fun a => f a >>= k) (fun a => g a >>= k) ε := by
  intro D hD
  rw [UCMonadCompDist.ucDistComp_bind_right]
  exact h _ (adm_bind hk hD)

/-- Left composition preserves trace-relating (no adm needed). -/
theorem traceRelating_comp_left {α β γ : Type}
    {ρ : α → T β} {g₁ g₂ : β → T γ} {ε : ℝ≥0∞}
    (h : TraceRelating g₁ g₂ ε) :
    TraceRelating (fun a => ρ a >>= g₁) (fun a => ρ a >>= g₂) ε :=
  fun D hD => le_trans (UCMonadCompDist.ucDistComp_bind_left ρ g₁ g₂ D) (h D hD)

/-- Monotonicity: smaller ε implies larger ε. -/
theorem traceRelating_mono {α β : Type} {f g : α → T β} {ε₁ ε₂ : ℝ≥0∞}
    (h : TraceRelating f g ε₁) (hle : ε₁ ≤ ε₂) :
    TraceRelating f g ε₂ :=
  fun D hD => le_trans (h D hD) hle

end UCMonad
