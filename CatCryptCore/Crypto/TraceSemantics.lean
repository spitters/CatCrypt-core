/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.TraceEquiv

/-!
# Trace semantics of reactive systems

The trace semantics of a reactive system `S : Sys τ E O` is its function of history
probabilities `Sys.histProb S : IOHist E O → ℝ≥0∞`. This file characterises the image of this
map and shows that systems modulo trace equivalence correspond exactly to consistent history
families, in the spirit of the generic trace semantics of Hasuo, Jacobs and Sokolova (LMCS 3(4),
2007), where finite traces of a Kleisli coalgebra are its map into a final coalgebra of traces.

A *consistent history family* (`ConsistentHist`) is a function `p : IOHist E O → ℝ≥0∞` with
`p [] = 1` such that, for every history `hs` and input `x`, the sum over the outputs `y` of
`p (hs ++ [(x, y)])` is at most `p hs`: the sub-distribution form of the consistency of the
conditional output distributions.

## Main results

* `Sys.histProb_consistent`: the history probabilities of every system form a consistent family;
  `Sys.tsum_histProb_append_eq` gives equality of the sums for a lossless system.
* `histSys p`: the canonical history system of a consistent family `p`. Its state is the history
  so far; on the input `(e, h)` after the history `hs` it answers `(o, h')` and moves to
  `hs ++ [((e, h), (o, h'))]` with probability `p (hs ++ [((e, h), (o, h'))]) / p hs`, and fails
  with the remaining probability. After a history of probability `0` it fails with probability `1`.
* `histProb_histSys`: completeness, `histProb (histSys p) = p`.
* `traceSemantics`: the equivalence between trace-equivalence classes of systems (with a state type
  in `Type`) and consistent history families.
* `Sys.realizes_zero_iff_histProb_eq`: `R` realizes `I` at bound `0` exactly when their history
  probabilities agree.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open scoped ENNReal

variable {τ υ E O : Type}

/-- A sum over `(τ × O) × Heap` as an outer sum over the output and heap and an inner sum over
the state. -/
private theorem tsum_state_out' (f : (τ × O) × Heap → ℝ≥0∞) :
    ∑' p, f p = ∑' (oh : O × Heap) (t : τ), f ((t, oh.1), oh.2) := by
  let e : (O × Heap) × τ ≃ (τ × O) × Heap :=
    { toFun := fun x => ((x.2, x.1.1), x.1.2)
      invFun := fun p => ((p.1.2, p.2), p.1.1)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [← e.tsum_eq]
  exact ENNReal.tsum_prod (f := fun (oh : O × Heap) (t : τ) => f ((t, oh.1), oh.2))

/-! ## Consistency of the history probabilities -/

namespace Sys

/-- Unfolding lemma of `histProb` at the empty history: it has probability `1`. -/
theorem histProb_nil (S : Sys τ E O) : S.histProb [] = 1 := rfl

/-- The successful outcomes of one step have total mass at most `1`. -/
theorem tsum_step_le_one (S : Sys τ E O) (t : τ) (e : E) (h : Heap) :
    ∑' (y : O × Heap) (t' : τ), S.step t e h (some ((t', y.1), y.2)) ≤ 1 := by
  rw [← tsum_state_out' (fun p => S.step t e h (some p))]
  calc ∑' p, S.step t e h (some p) ≤ S.step t e h none + ∑' p, S.step t e h (some p) :=
        le_add_self
    _ = 1 := by rw [← SDistr.tsum_option_eq_add, PMF.tsum_coe]

/-- The successful outcomes of a step that never fails have total mass `1`. -/
theorem tsum_step_eq_one (S : Sys τ E O) (t : τ) (e : E) (h : Heap)
    (hS : SPComp.NoFail (S.step t e)) :
    ∑' (y : O × Heap) (t' : τ), S.step t e h (some ((t', y.1), y.2)) = 1 := by
  rw [← tsum_state_out' (fun p => S.step t e h (some p))]
  have h1 := (S.step t e h).tsum_coe
  rw [SDistr.tsum_option_eq_add, hS h, zero_add] at h1
  exact h1

/-- From every state, extending a history by one input and summing over the outputs gives at most
the probability of the history. -/
theorem tsum_accept_append_le (S : Sys τ E O) (x : E × Heap) :
    ∀ (hs : IOHist E O) (t : τ), ∑' y, S.accept t (hs ++ [(x, y)]) ≤ S.accept t hs := by
  intro hs
  induction hs with
  | nil =>
    intro t
    simp only [List.nil_append, accept_cons, accept, mul_one]
    exact S.tsum_step_le_one t x.1 x.2
  | cons a hs ih =>
    intro t
    obtain ⟨x₀, y₀⟩ := a
    simp only [List.cons_append, accept_cons]
    rw [ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_left]
    exact ENNReal.tsum_le_tsum fun t' => by gcongr; exact ih t'

/-- For a system whose steps never fail, extending a history by one input and summing over the
outputs gives the probability of the history. -/
theorem tsum_accept_append_eq (S : Sys τ E O) (hS : ∀ t e, SPComp.NoFail (S.step t e))
    (x : E × Heap) :
    ∀ (hs : IOHist E O) (t : τ), ∑' y, S.accept t (hs ++ [(x, y)]) = S.accept t hs := by
  intro hs
  induction hs with
  | nil =>
    intro t
    simp only [List.nil_append, accept_cons, accept, mul_one]
    exact S.tsum_step_eq_one t x.1 x.2 (hS t x.1)
  | cons a hs ih =>
    intro t
    obtain ⟨x₀, y₀⟩ := a
    simp only [List.cons_append, accept_cons]
    rw [ENNReal.tsum_comm]
    simp_rw [ENNReal.tsum_mul_left, ih]

/-- Extending a history by one input and summing over the outputs gives at most the probability
of the history. -/
theorem tsum_histProb_append_le (S : Sys τ E O) (hs : IOHist E O) (x : E × Heap) :
    ∑' y, S.histProb (hs ++ [(x, y)]) ≤ S.histProb hs :=
  S.tsum_accept_append_le x hs S.init

/-- For a lossless system, extending a history by one input and summing over the outputs gives
the probability of the history. -/
theorem tsum_histProb_append_eq (S : Sys τ E O) (hS : ∀ t e, SPComp.NoFail (S.step t e))
    (hs : IOHist E O) (x : E × Heap) :
    ∑' y, S.histProb (hs ++ [(x, y)]) = S.histProb hs :=
  S.tsum_accept_append_eq hS x hs S.init

end Sys

/-! ## Consistent history families -/

/-- A consistent history family: the empty history has probability `1`, and for every history
`hs` and input `x` the probabilities of the one-step extensions of `hs` at `x` sum to at most the
probability of `hs`. -/
structure ConsistentHist (p : IOHist E O → ℝ≥0∞) : Prop where
  /-- The empty history has probability `1`. -/
  nil : p [] = 1
  /-- The extensions of a history at one input have total probability at most its own. -/
  append : ∀ (hs : IOHist E O) (x : E × Heap), ∑' y, p (hs ++ [(x, y)]) ≤ p hs

/-- The history probabilities of a system form a consistent family. -/
theorem Sys.histProb_consistent (S : Sys τ E O) : ConsistentHist S.histProb :=
  ⟨S.histProb_nil, S.tsum_histProb_append_le⟩

namespace ConsistentHist

variable {p : IOHist E O → ℝ≥0∞}

/-- A one-step extension has at most the probability of the history it extends. -/
theorem le_snoc (hp : ConsistentHist p) (hs : IOHist E O) (x : E × Heap) (y : O × Heap) :
    p (hs ++ [(x, y)]) ≤ p hs :=
  (ENNReal.le_tsum y).trans (hp.append hs x)

/-- An extension has at most the probability of the history it extends. -/
theorem le_append (hp : ConsistentHist p) (ext : IOHist E O) :
    ∀ hs : IOHist E O, p (hs ++ ext) ≤ p hs := by
  induction ext with
  | nil => intro hs; simp
  | cons a rest ih =>
    intro hs
    obtain ⟨x, y⟩ := a
    calc p (hs ++ (x, y) :: rest) = p ((hs ++ [(x, y)]) ++ rest) := by simp
      _ ≤ p (hs ++ [(x, y)]) := ih _
      _ ≤ p hs := hp.le_snoc hs x y

/-- Every history has probability at most `1`. -/
theorem le_one (hp : ConsistentHist p) (hs : IOHist E O) : p hs ≤ 1 := by
  simpa [hp.nil] using hp.le_append hs []

/-- Every history has finite probability. -/
theorem ne_top (hp : ConsistentHist p) (hs : IOHist E O) : p hs ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (hp.le_one hs)

end ConsistentHist

/-! ## The canonical history system -/

/-- The sub-distribution with weight `q a` on each `a` and the remaining mass on failure. -/
noncomputable def subDistrOfWeights {α : Type} (q : α → ℝ≥0∞) (hq : ∑' a, q a ≤ 1) :
    SDistr α :=
  ⟨fun o => o.elim (1 - ∑' a, q a) q, by
    rw [ENNReal.summable.hasSum_iff, SDistr.tsum_option_eq_add]
    exact tsub_add_cancel_of_le hq⟩

/-- Unfolding lemma of `subDistrOfWeights` at a successful outcome. -/
theorem subDistrOfWeights_some {α : Type} (q : α → ℝ≥0∞) (hq : ∑' a, q a ≤ 1) (a : α) :
    subDistrOfWeights q hq (some a) = q a := rfl

/-- The conditional probability of the output `y` at the input `x` after the history `hs`. -/
noncomputable def histWeight (p : IOHist E O → ℝ≥0∞) (hs : IOHist E O) (x : E × Heap)
    (y : O × Heap) : ℝ≥0∞ :=
  p (hs ++ [(x, y)]) / p hs

/-- The conditional output probabilities of a consistent family have total mass at most `1`. -/
theorem ConsistentHist.tsum_histWeight_le {p : IOHist E O → ℝ≥0∞} (hp : ConsistentHist p)
    (hs : IOHist E O) (x : E × Heap) : ∑' y, histWeight p hs x y ≤ 1 := by
  simp only [histWeight, div_eq_mul_inv, ENNReal.tsum_mul_right]
  calc (∑' y, p (hs ++ [(x, y)])) * (p hs)⁻¹ ≤ p hs * (p hs)⁻¹ := by
        gcongr
        exact hp.append hs x
    _ ≤ 1 := ENNReal.mul_inv_le_one (p hs)

open Classical in
/-- One step of the history system: after the history `hs`, on the input `(e, h)` it answers
`(o, h')` and moves to `hs ++ [((e, h), (o, h'))]` with probability `histWeight p hs (e, h) (o, h')`
and fails with the remaining probability. -/
noncomputable def histStep {p : IOHist E O → ℝ≥0∞} (hp : ConsistentHist p) (hs : IOHist E O)
    (e : E) : SPComp (IOHist E O × O) := fun h =>
  subDistrOfWeights (fun z : (IOHist E O × O) × Heap =>
      if z.1.1 = hs ++ [((e, h), (z.1.2, z.2))] then histWeight p hs (e, h) (z.1.2, z.2) else 0)
    (by
      rw [tsum_state_out' (fun z : (IOHist E O × O) × Heap =>
        if z.1.1 = hs ++ [((e, h), (z.1.2, z.2))] then histWeight p hs (e, h) (z.1.2, z.2)
        else 0)]
      simp only [tsum_ite_eq]
      exact hp.tsum_histWeight_le hs (e, h))

/-- The canonical history system of a consistent family `p`: its state is the history so far and
its step is `histStep`. -/
noncomputable def histSys {p : IOHist E O → ℝ≥0∞} (hp : ConsistentHist p) :
    Sys (IOHist E O) E O where
  init := []
  step := histStep hp

/-- One activation of the history system: the probability of answering `y` at the input `x`
after the history `t`, followed by the probability of `hs` from the extended history. -/
theorem accept_histSys_cons {p : IOHist E O → ℝ≥0∞} (hp : ConsistentHist p) (t : IOHist E O)
    (x : E × Heap) (y : O × Heap) (hs : IOHist E O) :
    (histSys hp).accept t ((x, y) :: hs) =
      histWeight p t x y * (histSys hp).accept (t ++ [(x, y)]) hs := by
  classical
  rw [Sys.accept_cons]
  simp only [histSys, histStep, subDistrOfWeights_some, Prod.mk.eta, ite_mul, zero_mul,
    tsum_ite_eq]

/-- From the history `t`, the history system accepts `hs` with probability
`p (t ++ hs) / p t`, in the form `accept t hs * p t = p (t ++ hs)`. -/
theorem accept_histSys_mul {p : IOHist E O → ℝ≥0∞} (hp : ConsistentHist p) (hs : IOHist E O) :
    ∀ t : IOHist E O, (histSys hp).accept t hs * p t = p (t ++ hs) := by
  induction hs with
  | nil => intro t; simp [Sys.accept]
  | cons a hs ih =>
    intro t
    obtain ⟨x, y⟩ := a
    rw [accept_histSys_cons]
    by_cases h0 : p t = 0
    · have hz : p (t ++ (x, y) :: hs) = 0 :=
        le_antisymm (h0 ▸ hp.le_append ((x, y) :: hs) t) zero_le
      rw [h0, hz, mul_zero]
    · calc histWeight p t x y * (histSys hp).accept (t ++ [(x, y)]) hs * p t
          = (histSys hp).accept (t ++ [(x, y)]) hs * p (t ++ [(x, y)]) := by
            unfold histWeight
            rw [mul_comm, ← mul_assoc, ENNReal.mul_div_cancel h0 (hp.ne_top t), mul_comm]
        _ = p (t ++ [(x, y)] ++ hs) := ih _
        _ = p (t ++ (x, y) :: hs) := by simp

/-- **Completeness of the trace semantics.** The history probabilities of the history system of
a consistent family are that family. -/
theorem histProb_histSys {p : IOHist E O → ℝ≥0∞} (hp : ConsistentHist p) (hs : IOHist E O) :
    (histSys hp).histProb hs = p hs := by
  have h := accept_histSys_mul hp hs []
  rw [hp.nil, mul_one, List.nil_append] at h
  exact h

/-! ## Systems modulo trace equivalence -/

/-- A reactive system with its state type in `Type`, packaged with its state type. -/
abbrev SysSigma (E O : Type) := Σ τ : Type, Sys τ E O

/-- Trace equivalence as a setoid on packaged systems. -/
instance traceSetoid (E O : Type) : Setoid (SysSigma E O) where
  r R I := Sys.TraceEq R.2 I.2
  iseqv := ⟨fun _ _ => rfl, fun h hs => (h hs).symm, fun h₁ h₂ hs => (h₁ hs).trans (h₂ hs)⟩

/-- Trace-equivalence classes of reactive systems. -/
abbrev TraceClass (E O : Type) := Quotient (traceSetoid E O)

/-- **Trace semantics as a bijection** (Hasuo–Jacobs–Sokolova style): trace-equivalence classes
of reactive systems correspond exactly to consistent history families. A class is sent to the
history probabilities of any of its systems, and a family to the class of its history system. -/
noncomputable def traceSemantics :
    TraceClass E O ≃ {p : IOHist E O → ℝ≥0∞ // ConsistentHist p} where
  toFun := Quotient.lift (fun S : SysSigma E O => ⟨S.2.histProb, S.2.histProb_consistent⟩)
    (fun _ _ h => Subtype.ext (funext h))
  invFun p := ⟦⟨IOHist E O, histSys p.2⟩⟧
  left_inv c := by
    induction c using Quotient.inductionOn with
    | h S => exact Quotient.sound fun hs => histProb_histSys S.2.histProb_consistent hs
  right_inv p := Subtype.ext (funext (histProb_histSys p.2))

/-- Unfolding lemma of `traceSemantics`: the trace semantics of the class of a system is its
history probability function. -/
@[simp]
theorem traceSemantics_mk (S : SysSigma E O) :
    (traceSemantics ⟦S⟧ : IOHist E O → ℝ≥0∞) = S.2.histProb := rfl

/-- **Realization at bound `0` is equality of trace semantics.** `R` realizes `I` at bound `0`
exactly when the history probabilities of `R` and `I` agree. -/
theorem Sys.realizes_zero_iff_histProb_eq {R : Sys τ E O} {I : Sys υ E O} :
    Realizes R I (fun _ _ => 0) ↔ R.histProb = I.histProb :=
  Sys.traceEq_iff_realizes_zero.symm.trans funext_iff.symm

end CatCrypt.Crypto.UCTransparent
