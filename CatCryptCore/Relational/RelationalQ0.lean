/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Relational.Approx

/-!
# Relational Q₀-monads: the coupling structure for a generic approximate relational logic

The Approxis reconstruction (`ApproxisRelational.lean`) fixes the effect to `SDistr`.
This file abstracts the structure that reconstruction actually consumes — a monad with
a **graded approximate relational lifting** and its four laws (pure, grade-additive
bind, relation- and grade-monotonicity) — into a typeclass `RelQ0Lift`, and extends it
with a heap-indexed denotation and adequacy to the typeclass `RelQ0`. It is the first
step of extending the reconstruction from the classical effect to every
coupling-equipped Q₀-monad: `SDistr` is the classical instance here, `QComp` (quantum
couplings, `Quantum/ApproxRelational.lean`) is the intended second.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt

open scoped ENNReal
open CatCrypt.Prob CatCrypt.Relational

/-- Pairing every outcome of two `ε`-coupled sub-distributions with one heap `h` gives an
`ε`-coupling of the paired sub-distributions supported in `R` on values and equality on
heaps. -/
theorem liftRApprox_bind_pure_heap {α β : Type} {ε : ℝ≥0∞} {R : α → β → Prop}
    {d₁ : SDistr α} {d₂ : SDistr β} (hd : liftRApprox ε R d₁ d₂) (h : CatCrypt.Core.Heap) :
    liftRApprox ε (fun p q => R p.1 q.1 ∧ p.2 = q.2)
      (d₁.bind (fun a => SDistr.pure (a, h))) (d₂.bind (fun b => SDistr.pure (b, h))) := by
  have hb := liftRApprox_bind (ε₂ := 0) (f₁ := fun a => SDistr.pure (a, h))
    (f₂ := fun b => SDistr.pure (b, h)) hd (fun a b hab =>
    liftRApprox_of_liftR (liftR_pure (R := fun (p : α × CatCrypt.Core.Heap)
      (q : β × CatCrypt.Core.Heap) => R p.1 q.1 ∧ p.2 = q.2) ⟨hab, rfl⟩))
  rwa [add_zero] at hb

/-- A **graded relational lifting** on an effect `T`: monad operations `pure'`, `bind'`
and a graded approximate relational lifting `liftR ε R m₁ m₂` satisfying the four
coupling laws (pure at grade `0`, grade-additive bind, relation- and
grade-monotonicity).

The class carries no semantics of `T`: `liftR := fun _ _ _ _ _ => True` satisfies all
four laws, so an instance of `RelQ0Lift` alone says nothing about what programs compute.
Results derived from the lifting laws hold over every instance; statements about the
meaning of programs require `RelQ0`, which adds a denotation and adequacy. -/
class RelQ0Lift (T : Type → Type) where
  pure' : {α : Type} → α → T α
  bind' : {α β : Type} → T α → (α → T β) → T β
  liftR : {α β : Type} → ℝ≥0∞ → (α → β → Prop) → T α → T β → Prop
  liftR_pure : ∀ {α β : Type} {a : α} {b : β} {R : α → β → Prop},
    R a b → liftR 0 R (pure' a) (pure' b)
  liftR_bind : ∀ {α β α' β' : Type} {ε δ : ℝ≥0∞} {R : α → β → Prop} {S : α' → β' → Prop}
    {m₁ : T α} {m₂ : T β} {k₁ : α → T α'} {k₂ : β → T β'},
    liftR ε R m₁ m₂ → (∀ a b, R a b → liftR δ S (k₁ a) (k₂ b)) →
    liftR (ε + δ) S (bind' m₁ k₁) (bind' m₂ k₂)
  liftR_mono_rel : ∀ {α β : Type} {ε : ℝ≥0∞} {R S : α → β → Prop} {m₁ : T α} {m₂ : T β},
    (∀ a b, R a b → S a b) → liftR ε R m₁ m₂ → liftR ε S m₁ m₂
  liftR_mono_eps : ∀ {α β : Type} {ε ε' : ℝ≥0∞} {R : α → β → Prop} {m₁ : T α} {m₂ : T β},
    ε ≤ ε' → liftR ε R m₁ m₂ → liftR ε' R m₁ m₂

/-- A **relational Q₀-monad**: a graded relational lifting (`RelQ0Lift`) together with a
stateful denotation `denote m h` as a sub-distribution over results and final heaps that
sends `pure'` and `bind'` to the state-monad unit and bind over `SDistr`.

The field `liftR_adequate` relates the lifting to the semantics: for every initial heap
`h`, `liftR ε R m₁ m₂` gives an `ε`-approximate sub-coupling of `denote m₁ h` and
`denote m₂ h` supported on pairs whose values are related by `R` and whose final heaps
are equal (`liftRApprox`). A stateless effect denotes by pairing every outcome with the
unchanged initial heap. With `denote_pure` the adequacy field excludes, for example,
`liftR := True` (`RelQ0.not_liftR_zero_pure_empty`). -/
class RelQ0 (T : Type → Type) extends RelQ0Lift T where
  /-- The denotation of a computation from an initial heap, as a sub-distribution over
  results and final heaps. -/
  denote : {α : Type} → T α → CatCrypt.Core.Heap → SDistr (α × CatCrypt.Core.Heap)
  denote_pure : ∀ {α : Type} (a : α) (h : CatCrypt.Core.Heap),
    denote (pure' a) h = SDistr.pure (a, h)
  denote_bind : ∀ {α β : Type} (m : T α) (k : α → T β) (h : CatCrypt.Core.Heap),
    denote (bind' m k) h = (denote m h).bind (fun p => denote (k p.1) p.2)
  /-- Adequacy: from every initial heap, the lifting gives a sub-coupling of the
  denotations supported on `R`-related values with equal final heaps. -/
  liftR_adequate : ∀ {α β : Type} {ε : ℝ≥0∞} {R : α → β → Prop} {m₁ : T α} {m₂ : T β},
    liftR ε R m₁ m₂ → ∀ h : CatCrypt.Core.Heap,
      liftRApprox ε (fun p q => R p.1 q.1 ∧ p.2 = q.2) (denote m₁ h) (denote m₂ h)

/- The lifting operations and laws of `RelQ0Lift` are also reachable under the `RelQ0`
namespace (`RelQ0.liftR` is the constant `RelQ0Lift.liftR`). -/
namespace RelQ0
export RelQ0Lift (pure' bind' liftR liftR_pure liftR_bind liftR_mono_rel liftR_mono_eps)
end RelQ0

/-- The classical instance: `SDistr` with the sub-coupling lifting `liftRApprox`; the
denotation pairs every outcome with the unchanged initial heap. -/
noncomputable instance instRelQ0SDistr : RelQ0 SDistr where
  pure' := SDistr.pure
  bind' := SDistr.bind
  liftR := liftRApprox
  liftR_pure h := liftRApprox_of_liftR (liftR_pure h)
  liftR_bind h hf := liftRApprox_bind h hf
  liftR_mono_rel hRS h := liftRApprox_mono_rel hRS h
  liftR_mono_eps hε h := liftRApprox_mono_eps hε h
  denote m h := m.bind (fun a => SDistr.pure (a, h))
  denote_pure a h := SDistr.pure_bind a _
  denote_bind m k h := by
    simp only [SDistr.bind_assoc, SDistr.pure_bind]
  liftR_adequate hm h := liftRApprox_bind_pure_heap hm h

/-- In every `RelQ0`, two point masses are not related at grade `0` by the empty relation.
In particular `liftR := fun _ _ _ _ _ => True` is not the lifting of any `RelQ0`. -/
theorem RelQ0.not_liftR_zero_pure_empty {T : Type → Type} [RelQ0 T] {α β : Type}
    (a : α) (b : β) :
    ¬ RelQ0.liftR 0 (fun (_ : α) (_ : β) => False) (RelQ0.pure' (T := T) a)
      (RelQ0.pure' (T := T) b) := by
  intro h
  have hA := RelQ0.liftR_adequate h CatCrypt.Core.Heap.empty
  rw [RelQ0.denote_pure, RelQ0.denote_pure] at hA
  obtain ⟨c, hc⟩ := hA
  have hz : ∀ a' b', c.joint (some (a', b')) = 0 := fun a' b' => by
    by_contra hne
    exact (hc a' b' hne).1
  have hdef := c.left_deficit
  simp only [hz, tsum_zero, tsub_zero] at hdef
  have h1 : (∑' a', (SDistr.pure (a, CatCrypt.Core.Heap.empty) :
      SDistr (α × CatCrypt.Core.Heap)) (some a')) = 1 :=
    SDistr.tsum_some_eq_one_of_none_zero (SDistr.pure_apply_none _)
  rw [h1] at hdef
  exact one_ne_zero (le_antisymm hdef zero_le)

/-! ## Higher-order layer: arrow-type relational lifting

The first-order judgment `RelQ0Lift.liftR` relates values. The extension to *function*
types — the arrow-type case the first-order judgment cannot express — is definable
over any `RelQ0Lift` and its compatibility rules are derivable from the four
first-order laws, so it holds for every graded relational lifting at once. -/

/-- Higher-order (arrow-type) relational lifting: Kleisli arrows `f, g` are related
at `R ⇒ S` and grade `ε` when they send `R`-related arguments to `liftR ε S`-related
results. -/
def liftRArr {T : Type → Type} [RelQ0Lift T] {α α' β β' : Type}
    (ε : ℝ≥0∞) (R : α → α' → Prop) (S : β → β' → Prop)
    (f : α → T β) (g : α' → T β') : Prop :=
  ∀ a a', R a a' → RelQ0Lift.liftR ε S (f a) (g a')

/-- Arrow elimination (application): an `R ⇒ S`-related function pair, applied to
`R`-related arguments, yields `liftR ε S`-related results. -/
theorem liftRArr_app {T : Type → Type} [RelQ0Lift T] {α α' β β' : Type}
    {ε : ℝ≥0∞} {R : α → α' → Prop} {S : β → β' → Prop}
    {f : α → T β} {g : α' → T β'} {a : α} {a' : α'}
    (hfg : liftRArr ε R S f g) (ha : R a a') : RelQ0Lift.liftR ε S (f a) (g a') :=
  hfg a a' ha

/-- Kleisli composition of arrow-related pairs, grade-additive — the higher-order
form of the first-order bind rule, over any graded relational lifting. -/
theorem liftRArr_kleisli {T : Type → Type} [RelQ0Lift T] {α α' β β' γ γ' : Type}
    {ε δ : ℝ≥0∞} {R : α → α' → Prop} {S : β → β' → Prop} {U : γ → γ' → Prop}
    {f : α → T β} {g : α' → T β'} {k : β → T γ} {k' : β' → T γ'}
    (hfg : liftRArr ε R S f g) (hkk' : liftRArr δ S U k k') :
    liftRArr (ε + δ) R U (fun a => RelQ0Lift.bind' (f a) k)
      (fun a' => RelQ0Lift.bind' (g a') k') :=
  fun a a' ha => RelQ0Lift.liftR_bind (hfg a a' ha) (fun b b' hb => hkk' b b' hb)

/-- Grade monotonicity lifts to arrows. -/
theorem liftRArr_mono_eps {T : Type → Type} [RelQ0Lift T] {α α' β β' : Type}
    {ε ε' : ℝ≥0∞} {R : α → α' → Prop} {S : β → β' → Prop}
    {f : α → T β} {g : α' → T β'} (hε : ε ≤ ε') (h : liftRArr ε R S f g) :
    liftRArr ε' R S f g :=
  fun a a' ha => RelQ0Lift.liftR_mono_eps hε (h a a' ha)

/- The guarded (step-indexed) higher-order layer lives in `RelationalQ0Guarded.lean`,
built on iris-lean's `SiProp` (the topos of trees) — the same step-indexed
propositions `refines` uses — rather than a hand-rolled copy. -/

end CatCrypt
