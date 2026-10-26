/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QRHLSeq
public import CatCryptCore.XDijkstra.XPredCore

/-!
# qRHL as a reading of the XDijkstra relational layer

The qRHL judgment `qrHoare Φ C₁ C₂ Ψ` of `CatCrypt.Quantum.QRHL` states that every
positive semidefinite bipartite state satisfying `Φ` is taken by the joint evolution,
summed over outcome pairs, to a state satisfying `Ψ`. This file reads the judgment as a
triple of the graded transformer kernel `XCorePT` of `CatCryptCore.XDijkstra.XPredCore`.

The assertion type is the type of predicates on bipartite matrices, ordered pointwise
by implication. A state map `f` gives the transformer `stateMapPT f`, whose weakest
precondition at `Q` is `Q () ∘ f`; it has result type `Unit`, since the judgment keeps
only the outcome-summed state, and trivial grade and exception postcondition. The
transformer of the pair `C₁ ~ C₂` is `qrhlPT C₁ C₂`, the state-map transformer of the
joint post-state `jointPost C₁ C₂`. Positivity is a conjunct of the precondition
(`BipartitePred.psdAnd`), so the transformer itself carries no guard:

* `qrHoare_iff_triple`: the judgment is `XCorePT.Triple (psdAnd Φ) (qrhlPT C₁ C₂) Ψ`.
* The sequencing rules are `XCorePT.seq_triple`, through the equations
  `qrhlPT_qbind` and `qrhlPT_qbind_qpure_right`, which state that the transformer of a
  sequential composite is the sequence `XCorePT.seq` of the transformers.
* The consequence rule is `XCorePT.Triple.conseq`; the skip rule is the triple of
  `XCorePT.ret`, by `qrhlPT_qpure`.
* The two-sided judgment is a relational triple `XCorePT.RelTriple` over the product of
  the left transformer `qrhlPT C₁ (qpure ())` and the right transformer
  `qrhlPT (qpure ()) C₂` (`qrHoare_iff_relTriple`), and `XCorePT.rel_seq` gives the rule
  that composes a left one-sided judgment with a right one-sided judgment
  (`qrhl_left_right`).

## Main results

* `qrHoare_iff_triple`, `qrHoare_iff_relTriple`
* `qrhl_skip_triple`, `qrhl_conseq_triple`, `qrhl_one_sided_left_wp_triple`,
  `qrhl_one_sided_left_triple`, `qrhl_seq_one_sided_left_triple`, `qrhl_seq_triple`,
  `qrhl_unitary_wp_triple`, `qrhl_left_right`
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder
open Matrix

noncomputable section

namespace CatCrypt.XDijkstra.XQRHL

open CatCrypt.Quantum CatCrypt.Quantum.QRHL CatCrypt.Quantum.UnitaryChannel

universe u

variable {d₁ d₂ : ℕ} {α β γ δ : Type}

/-! ## Transformers of state maps -/

/-- The transformer of a state map `f : S → S` over predicates on `S`: the weakest
precondition of `Q` is `Q () ∘ f`, at result type `Unit`, trivial exception
postcondition and trivial grade. -/
def stateMapPT {S : Type u} (f : S → S) : XCorePT (S → Prop) Unit Unit Unit where
  apply Q _ := fun s => Q () (f s)
  grade := ()
  mono h _ := fun s => h () (f s)

@[simp] theorem stateMapPT_apply {S : Type u} (f : S → S) (Q : Unit → S → Prop) (e : Unit) :
    (stateMapPT f).apply Q e = fun s => Q () (f s) := rfl

/-- The sequence of two state-map transformers is the transformer of the composite map. -/
theorem stateMapPT_seq {S : Type u} (f g : S → S) :
    (stateMapPT f).seq (stateMapPT g) = stateMapPT (g ∘ f) :=
  XCorePT.ext (fun _ _ => rfl) rfl

/-- The transformer of the identity map is the return of `()`. -/
theorem stateMapPT_id {S : Type u} : stateMapPT (id : S → S) = XCorePT.ret () :=
  XCorePT.ext (fun _ _ => rfl) rfl

/-! ## The transformer of a pair of programs -/

/-- The predicate `Φ` restricted to positive semidefinite states, as an element of the
assertion type of `qrhlPT` (predicates on bipartite matrices, ordered pointwise). -/
def BipartitePred.psdAnd (Φ : BipartitePred d₁ d₂) :
    Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ → Prop :=
  fun ρ => ρ.PosSemidef ∧ Φ ρ

/-- The transformer of `C₁ ~ C₂`: the state-map transformer of the joint post-state. -/
def qrhlPT (C₁ : QComp d₁ α) (C₂ : QComp d₂ β) :
    XCorePT (Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ → Prop) Unit Unit Unit :=
  stateMapPT (jointPost C₁ C₂)

/-- **The qRHL judgment is a triple of `qrhlPT`** with the precondition restricted to
positive semidefinite states. -/
theorem qrHoare_iff_triple (Φ Ψ : BipartitePred d₁ d₂) (C₁ : QComp d₁ α) (C₂ : QComp d₂ β) :
    qrHoare Φ C₁ C₂ Ψ ↔
      XCorePT.Triple (BipartitePred.psdAnd Φ) (qrhlPT C₁ C₂) (fun _ => Ψ) () :=
  ⟨fun h ρ hρ => h ρ hρ.1 hρ.2, fun h ρ hρ hΦ => h ρ ⟨hρ, hΦ⟩⟩

/-! ## Skip and consequence -/

/-- The transformer of `pure a ~ pure b` is the return of `()`. -/
theorem qrhlPT_qpure (a : α) (b : β) :
    qrhlPT (d₁ := d₁) (d₂ := d₂) (QComp.qpure a) (QComp.qpure b) = XCorePT.ret () := by
  refine XCorePT.ext (fun Q _ => funext fun ρ => ?_) rfl
  change Q () (jointPost _ _ ρ) = Q () ρ
  rw [jointPost, tsum_eq_single (a, b) (fun p hp => jointBranch_qpure_ne
    (fun h => hp (Prod.ext h.1 h.2)) ρ), jointBranch_qpure]

/-- **Skip rule** as the triple of `XCorePT.ret`. -/
theorem qrhl_skip_triple (Φ : BipartitePred d₁ d₂) (a : α) (b : β) :
    qrHoare Φ (QComp.qpure a) (QComp.qpure b) Φ := by
  rw [qrHoare_iff_triple, qrhlPT_qpure]
  exact fun _ h => h.2

/-- **Consequence rule** as `XCorePT.Triple.conseq`. -/
theorem qrhl_conseq_triple {Φ Φ' Ψ Ψ' : BipartitePred d₁ d₂}
    {C₁ : QComp d₁ α} {C₂ : QComp d₂ β}
    (h : qrHoare Φ C₁ C₂ Ψ)
    (hΦ : ∀ ρ, ρ.PosSemidef → Φ' ρ → Φ ρ)
    (hΨ : ∀ ρ, Ψ ρ → Ψ' ρ) :
    qrHoare Φ' C₁ C₂ Ψ' := by
  rw [qrHoare_iff_triple] at h ⊢
  exact XCorePT.Triple.conseq h (fun ρ hρ => ⟨hρ.1, hΦ ρ hρ.1 hρ.2⟩)
    (fun _ ρ => hΨ ρ) le_rfl

/-! ## One-sided rules -/

/-- The transformer of `C₁ ~ pure b` is the state-map transformer of `oneSidedPost C₁ b`. -/
theorem qrhlPT_qpure_right (C₁ : QComp d₁ α) (b : β) :
    qrhlPT (d₂ := d₂) C₁ (QComp.qpure b) = stateMapPT (oneSidedPost C₁ b) := by
  refine XCorePT.ext (fun Q _ => funext fun ρ => ?_) rfl
  change Q () (jointPost _ _ ρ) = Q () (oneSidedPost C₁ b ρ)
  rw [jointPost, tsum_jointBranch_qpure_right]

/-- A left one-sided judgment gives a triple of `qrhlPT C₁ (pure b)` whose postcondition
records positivity, when every branch of `C₁` is completely positive. -/
theorem triple_psdAnd_of_qrHoare_left {Φ Θ : BipartitePred d₁ d₂} (C₁ : QComp d₁ α) (b : β)
    (hcp : ∀ a, IsCPMap (C₁.branch a)) (h : qrHoare Φ C₁ (QComp.qpure b) Θ) :
    XCorePT.Triple (BipartitePred.psdAnd Φ) (qrhlPT C₁ (QComp.qpure b))
      (fun _ => BipartitePred.psdAnd Θ) () := by
  intro ρ hρ
  refine ⟨?_, h ρ hρ.1 hρ.2⟩
  rw [jointPost, tsum_jointBranch_qpure_right]
  exact oneSidedPost_psd C₁ b hcp ρ hρ.1

/-- **One-sided rule, weakest-precondition form**: the weakest precondition of
`qrhlPT C₁ (pure b)` at `Ψ` is `oneSidedPre C₁ b Ψ`. -/
theorem qrhl_one_sided_left_wp_triple (C₁ : QComp d₁ α) (b : β) (Ψ : BipartitePred d₁ d₂) :
    qrHoare (BipartitePred.oneSidedPre C₁ b Ψ) C₁ (QComp.qpure b) Ψ := by
  rw [qrHoare_iff_triple, qrhlPT_qpure_right]
  exact fun _ h => h.2

/-- **One-sided rule** for a product predicate, from the weakest-precondition form by
`XCorePT.Triple.conseq`. -/
theorem qrhl_one_sided_left_triple
    (P₁ : Matrix (Fin d₁) (Fin d₁) ℂ → Prop)
    (P₂ : Matrix (Fin d₂) (Fin d₂) ℂ → Prop)
    (C₁ : QComp d₁ α) (b : β)
    (h₁ : ∀ σ, σ.PosSemidef → P₁ σ → P₁ (∑' a, C₁.branch a σ))
    (htp : ∀ σ : Matrix (Fin d₁) (Fin d₁) ℂ, (∑' a, C₁.branch a σ).trace = σ.trace) :
    qrHoare (BipartitePred.product P₁ P₂) C₁ (QComp.qpure b)
      (BipartitePred.product P₁ P₂) := by
  refine qrhl_conseq_triple (qrhl_one_sided_left_wp_triple C₁ b _) ?_ (fun _ h => h)
  intro ρ hρ ⟨hP₁, hP₂⟩
  refine ⟨?_, ?_⟩
  · rw [partialTrace₂_oneSidedPost]
    exact h₁ _ (PartialTrace.partialTrace₂_psd ρ hρ) hP₁
  · rw [partialTrace₁_oneSidedPost C₁ b htp]
    exact hP₂

/-- The transformer of `(C₁; D₁) ~ pure b'` is the sequence of the transformers of
`C₁ ~ pure b` and `D₁ ~ pure b'`. -/
theorem qrhlPT_qbind_qpure_right (C₁ : QComp d₁ α) (D₁ : QComp d₁ γ) (b : β) (b' : β) :
    qrhlPT (d₂ := d₂) (QComp.qbind C₁ fun _ => D₁) (QComp.qpure b') =
      (qrhlPT C₁ (QComp.qpure b)).seq (qrhlPT D₁ (QComp.qpure b')) := by
  rw [qrhlPT_qpure_right, qrhlPT_qpure_right, qrhlPT_qpure_right, stateMapPT_seq]
  exact congrArg stateMapPT (funext fun ρ => oneSidedPost_qbind C₁ D₁ b b' ρ)

/-- **One-sided sequence rule** as `XCorePT.seq_triple`. -/
theorem qrhl_seq_one_sided_left_triple
    {Φ Θ Ψ : BipartitePred d₁ d₂} (C₁ : QComp d₁ α) (D₁ : QComp d₁ γ) (b b' : β)
    (hcp : ∀ a, IsCPMap (C₁.branch a))
    (h₁ : qrHoare Φ C₁ (QComp.qpure b) Θ)
    (h₂ : qrHoare Θ D₁ (QComp.qpure b') Ψ) :
    qrHoare Φ (QComp.qbind C₁ fun _ => D₁) (QComp.qpure b') Ψ := by
  rw [qrHoare_iff_triple] at h₂ ⊢
  rw [qrhlPT_qbind_qpure_right C₁ D₁ b b']
  exact XCorePT.seq_triple (triple_psdAnd_of_qrHoare_left C₁ b hcp h₁) h₂

/-! ## Two-sided sequencing -/

/-- The transformer of `(C₁; D₁) ~ (C₂; D₂)` is the sequence of the transformers of
`C₁ ~ C₂` and `D₁ ~ D₂`. -/
theorem qrhlPT_qbind (C₁ : QComp d₁ α) (D₁ : QComp d₁ γ) (C₂ : QComp d₂ β)
    (D₂ : QComp d₂ δ) :
    qrhlPT (QComp.qbind C₁ fun _ => D₁) (QComp.qbind C₂ fun _ => D₂) =
      (qrhlPT C₁ C₂).seq (qrhlPT D₁ D₂) := by
  rw [qrhlPT, qrhlPT, qrhlPT, stateMapPT_seq]
  exact congrArg stateMapPT (funext fun ρ => jointPost_qbind C₁ D₁ C₂ D₂ ρ)

/-- **Two-sided sequence rule** as `XCorePT.seq_triple`. -/
theorem qrhl_seq_triple {Φ Θ Ψ : BipartitePred d₁ d₂} (C₁ : QComp d₁ α) (D₁ : QComp d₁ γ)
    (C₂ : QComp d₂ β) (D₂ : QComp d₂ δ)
    (hcp₁ : ∀ a, IsCPMap (C₁.branch a)) (hcp₂ : ∀ b, IsCPMap (C₂.branch b))
    (h₁ : qrHoare Φ C₁ C₂ Θ) (h₂ : qrHoare Θ D₁ D₂ Ψ) :
    qrHoare Φ (QComp.qbind C₁ fun _ => D₁) (QComp.qbind C₂ fun _ => D₂) Ψ := by
  rw [qrHoare_iff_triple] at h₂ ⊢
  rw [qrhlPT_qbind]
  refine XCorePT.seq_triple (R := BipartitePred.psdAnd Θ) (fun ρ hρ => ⟨?_, h₁ ρ hρ.1 hρ.2⟩) h₂
  exact jointPost_psd C₁ C₂ hcp₁ hcp₂ ρ hρ.1

/-! ## Unitary rules -/

/-- **Unitary rule, weakest-precondition form**, through `qrHoare_iff_triple`: the weakest
precondition of `qrhlPT` at `Ψ` is `conjPre U₁ U₂ Ψ`. -/
theorem qrhl_unitary_wp_triple
    (U₁ : Matrix.unitaryGroup (Fin d₁) ℂ) (U₂ : Matrix.unitaryGroup (Fin d₂) ℂ)
    (Ψ : BipartitePred d₁ d₂) :
    XCorePT.Triple (BipartitePred.psdAnd (BipartitePred.conjPre U₁ U₂ Ψ))
      (qrhlPT (unitaryChannel U₁) (unitaryChannel U₂)) (fun _ => Ψ) () := by
  intro ρ hρ
  change Ψ (jointPost _ _ ρ)
  rw [jointPost, tsum_jointBranch_unitaryChannel]
  exact hρ.2

/-! ## The relational triple over the product -/

/-- The total action of `pure x` is the identity. -/
theorem totalMap_qpure {d : ℕ} (x : α) : totalMap (QComp.qpure x : QComp d α) = LinearMap.id := by
  refine LinearMap.ext fun Y => ?_
  rw [totalMap_apply, tsum_eq_single x (fun a ha => by simp [QComp.qpure, ha])]
  simp [QComp.qpure]

/-- The joint post-state of `C₁ ~ C₂` is that of `pure () ~ C₂` after that of
`C₁ ~ pure ()`. -/
theorem jointPost_eq_right_left (C₁ : QComp d₁ α) (C₂ : QComp d₂ β)
    (ρ : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) :
    jointPost C₁ C₂ ρ =
      jointPost (QComp.qpure ()) C₂ (jointPost C₁ (QComp.qpure ()) ρ) := by
  rw [← jointPost_qbind C₁ (QComp.qpure ()) (QComp.qpure ()) C₂, QComp.qpure_qbind]
  simp only [jointPost, tsum_jointBranch_eq_lift, totalMap_qbind, totalMap_qpure,
    LinearMap.id_comp]

/-- **The two-sided judgment is a relational triple** over the product of the left
transformer `qrhlPT C₁ (pure ())` and the right transformer `qrhlPT (pure ()) C₂`. -/
theorem qrHoare_iff_relTriple (Φ Ψ : BipartitePred d₁ d₂) (C₁ : QComp d₁ α)
    (C₂ : QComp d₂ β) :
    qrHoare Φ C₁ C₂ Ψ ↔
      XCorePT.RelTriple (BipartitePred.psdAnd Φ) (qrhlPT C₁ (QComp.qpure ()))
        (qrhlPT (QComp.qpure ()) C₂) (fun _ => Ψ) () := by
  rw [qrHoare_iff_triple]
  unfold XCorePT.RelTriple XCorePT.Triple
  have happ : (qrhlPT C₁ C₂).apply (fun _ => Ψ) () =
      ((qrhlPT C₁ (QComp.qpure ())).prod (qrhlPT (QComp.qpure ()) C₂)).apply
        (fun _ => Ψ) () :=
    funext fun ρ => congrArg Ψ (jointPost_eq_right_left C₁ C₂ ρ)
  rw [happ]

/-- **Left-then-right rule** as `XCorePT.rel_seq`: a judgment `{Φ} C₁ ~ pure () {Θ}` and a
judgment `{Θ} pure () ~ C₂ {Ψ}` give `{Φ} C₁ ~ C₂ {Ψ}` when every branch of `C₁` is
completely positive. -/
theorem qrhl_left_right {Φ Θ Ψ : BipartitePred d₁ d₂} (C₁ : QComp d₁ α) (C₂ : QComp d₂ β)
    (hcp : ∀ a, IsCPMap (C₁.branch a))
    (h₁ : qrHoare Φ C₁ (QComp.qpure ()) Θ) (h₂ : qrHoare Θ (QComp.qpure ()) C₂ Ψ) :
    qrHoare Φ C₁ C₂ Ψ := by
  rw [qrHoare_iff_relTriple]
  rw [qrHoare_iff_triple] at h₂
  exact XCorePT.rel_seq (triple_psdAnd_of_qrHoare_left C₁ () hcp h₁) (fun _ => h₂)

end CatCrypt.XDijkstra.XQRHL
