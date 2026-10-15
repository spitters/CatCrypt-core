/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.XDijkstra.XCostMonad
public import CatCryptCore.Crypto.MonadCostModel

@[expose] public section
set_option autoImplicit false

/-!
# `XCostMonadModel`: `CostM` as the cost grading of the tick-state monad

`TickM σ α` is the state monad over `σ` that counts ticks: `run s` is the value, the final
state and the number of ticks, as for `CostM σ n α`, but without a bound on the count.
`TickM σ` is a lawful monad and a `UCMonadBase`, and the worst-case tick count over inputs
and initial states is a `MonadCostModel` on it.

Forgetting the bound sends `CostM σ n α` to `TickM σ α`; the map commutes with `pure`,
`bind`, `tick`, `get` and `set`, and sends a Kleisli arrow into `CostM σ n` to an arrow of
cost at most `n` (`costBounded_toTickM`). Conversely every arrow of `TickM σ` of cost at
most `n` is the image of exactly one arrow into `CostM σ n` (`costBoundedEquiv`). The
indexed family `CostM σ n` is therefore the grading `costBounded n` of the Kleisli arrows of
the single monad `TickM σ`.

Katsumata's parametric effect monads ("Parametric effect monads and semantics of effect
systems", POPL 2014) are families `T e` indexed by a preordered monoid of effects;
`CostM σ` is such a family over `(ℕ, ≤, 0, +)`, with `CostM.instGradedMonad` for the unit
and multiplication and `CostM.relax` for the inclusions along `≤`, and
`costBoundedEquiv` identifies its Kleisli arrows at `n` with the arrows of `TickM σ` of cost
at most `n`. Danielsson's `Thunk n` monad ("Lightweight semiformal time complexity analysis
for purely functional data structures", POPL 2008) indexes computations by an exact tick
count in the type; `CostM σ n` indexes by an upper bound on the count of a state program.

## Main definitions

* `TickM σ α`: the tick-counting state monad, with `TickM.tick`, `TickM.get`, `TickM.set`
* `instMonadCostModelTickM`: the cost model `cost f := ⨆ a, ⨆ s, ((f a).run s).2`
* `CostM.toTickM`: forget the bound
* `costBoundedEquiv`: `{f : α → TickM σ β // costBounded n f} ≃ (α → CostM σ n β)`

## Main results

* `TickM` is a `LawfulMonad` and a `UCMonadBase`
* `costBounded_iff_run`: `costBounded n f` iff every run of every `f a` counts at most `n`
* `toTickM_pure`, `toTickM_bind`, `toTickM_tick`, `toTickM_get`, `toTickM_set`
* `costBounded_toTickM`: the image of a Kleisli arrow into `CostM σ n` has cost at most `n`
-/

namespace CatCrypt.XDijkstra

/-- A state program over `σ` with a tick counter and no bound on the count: `run s` is the
returned value, the final state and the number of ticks. -/
@[ext]
structure TickM (σ : Type) (α : Type) where
  /-- The run from an initial state: value and final state, paired with the number of
  ticks. -/
  run : σ → (α × σ) × ℕ

namespace TickM

variable {σ α β γ : Type}

/-- Return a value: the state is unchanged and no tick is counted. -/
protected def pure (a : α) : TickM σ α where
  run s := ((a, s), 0)

/-- Run `x`, then the continuation at its value from its final state; the tick counts add. -/
protected def bind (x : TickM σ α) (f : α → TickM σ β) : TickM σ β where
  run s :=
    (((f (x.run s).1.1).run (x.run s).1.2).1,
      (x.run s).2 + ((f (x.run s).1.1).run (x.run s).1.2).2)

/-- Count `k` ticks. -/
def tick (k : ℕ) : TickM σ Unit where
  run s := (((), s), k)

/-- Return the state. -/
protected def get : TickM σ σ where
  run s := ((s, s), 0)

/-- Replace the state. -/
protected def set (s' : σ) : TickM σ Unit where
  run _ := (((), s'), 0)

instance instMonad : Monad (TickM σ) where
  pure := TickM.pure
  bind := TickM.bind

/-- The run of `pure`. -/
@[simp] theorem run_pure (a : α) (s : σ) : (pure a : TickM σ α).run s = ((a, s), 0) := rfl

/-- The run of `>>=`. -/
@[simp] theorem run_bind (x : TickM σ α) (f : α → TickM σ β) (s : σ) :
    (x >>= f).run s =
      (((f (x.run s).1.1).run (x.run s).1.2).1,
        (x.run s).2 + ((f (x.run s).1.1).run (x.run s).1.2).2) := rfl

/-- The run of `TickM.tick`. -/
@[simp] theorem run_tick (k : ℕ) (s : σ) : (tick k : TickM σ Unit).run s = (((), s), k) := rfl

/-- The run of `TickM.get`. -/
@[simp] theorem run_get (s : σ) : (TickM.get : TickM σ σ).run s = ((s, s), 0) := rfl

/-- The run of `TickM.set`. -/
@[simp] theorem run_set (s' s : σ) : (TickM.set s' : TickM σ Unit).run s = (((), s'), 0) :=
  rfl

instance instLawfulMonad : LawfulMonad (TickM σ) := LawfulMonad.mk'
  (id_map := fun x => TickM.ext <| funext fun s => by simp [Functor.map, TickM.bind, TickM.pure])
  (pure_bind := fun a f => TickM.ext <| funext fun s => by simp)
  (bind_assoc := fun x f g => TickM.ext <| funext fun s => by simp [Nat.add_assoc])

/-- Parallel composition on `Sum`, by case split on the input. -/
def mapSum {α β γ δ : Type} (f : α → TickM σ β) (g : γ → TickM σ δ) :
    α ⊕ γ → TickM σ (β ⊕ δ)
  | .inl a => f a >>= fun b => pure (.inl b)
  | .inr c => g c >>= fun d => pure (.inr d)

instance instUCMonadBase : UCMonad.UCMonadBase (TickM σ) where
  ucMapSum := mapSum
  ucMapSum_inl _ _ _ := rfl
  ucMapSum_inr _ _ _ := rfl
  ucMapSum_pure_pure {_ _} := by
    funext x; cases x <;> exact TickM.ext (funext fun s => by simp [mapSum])
  ucMapSum_pure_kleisli f g := by
    funext x; cases x <;> exact TickM.ext (funext fun s => by simp [mapSum])

/-- The worst-case tick count of a Kleisli arrow, over inputs and initial states. -/
noncomputable instance instMonadCostModelTickM : UCMonad.MonadCostModel (TickM σ) where
  cost f := ⨆ a, ⨆ s, ((((f a).run s).2 : ℕ) : ℕ∞)
  cost_pure {_} := le_antisymm (iSup₂_le fun _ _ => le_rfl) bot_le
  cost_bind {α β γ} {f g} := iSup₂_le fun a s => by
    simp only [run_bind, Nat.cast_add]
    exact add_le_add (α := ℕ∞) (le_iSup₂ (f := fun a s => ((((f a).run s).2 : ℕ) : ℕ∞)) a s)
      (le_iSup₂ (f := fun b s => ((((g b).run s).2 : ℕ) : ℕ∞)) _ _)
  cost_mapSum {α β γ δ} {f g} := iSup₂_le fun x s => by
    cases x with
    | inl a =>
      simp only [UCMonad.UCMonadBase.ucMapSum, mapSum, run_bind, run_pure, Nat.add_zero]
      exact le_max_of_le_left (le_iSup₂ (f := fun a s => ((((f a).run s).2 : ℕ) : ℕ∞)) a s)
    | inr c =>
      simp only [UCMonad.UCMonadBase.ucMapSum, mapSum, run_bind, run_pure, Nat.add_zero]
      exact le_max_of_le_right (le_iSup₂ (f := fun c s => ((((g c).run s).2 : ℕ) : ℕ∞)) c s)
  cost_precomp {α α' β} {g} f :=
    iSup₂_le fun a s => le_iSup₂ (f := fun a s => ((((g a).run s).2 : ℕ) : ℕ∞)) (f a) s

/-- An arrow of `TickM σ` has cost at most `n` iff every run of every `f a` counts at most
`n` ticks. -/
theorem costBounded_iff_run {n : ℕ} (f : α → TickM σ β) :
    UCMonad.costBounded n f ↔ ∀ a s, ((f a).run s).2 ≤ n := by
  show (⨆ a, ⨆ s, ((((f a).run s).2 : ℕ) : ℕ∞)) ≤ n ↔ _
  simp only [iSup_le_iff, Nat.cast_le]

end TickM

namespace CostM

variable {σ α β : Type} {m n : ℕ}

/-- Forget the bound on the tick count. -/
def toTickM (x : CostM σ n α) : TickM σ α where
  run := x.run

/-- The run of `CostM.toTickM`. -/
@[simp] theorem run_toTickM (x : CostM σ n α) : x.toTickM.run = x.run := rfl

/-- `toTickM` sends `CostM.pure` to `pure`. -/
@[simp] theorem toTickM_pure (a : α) : (CostM.pure a : CostM σ 0 α).toTickM = pure a := rfl

/-- `toTickM` sends `CostM.bind` to `>>=`. -/
@[simp] theorem toTickM_bind (x : CostM σ m α) (f : α → CostM σ n β) :
    (x.bind f).toTickM = x.toTickM >>= fun a => (f a).toTickM := rfl

/-- `toTickM` sends `CostM.tick` to `TickM.tick`. -/
@[simp] theorem toTickM_tick (k : ℕ) : (tick k : CostM σ k Unit).toTickM = TickM.tick k := rfl

/-- `toTickM` sends `CostM.get` to `TickM.get`. -/
@[simp] theorem toTickM_get : (CostM.get : CostM σ 0 σ).toTickM = TickM.get := rfl

/-- `toTickM` sends `CostM.set` to `TickM.set`. -/
@[simp] theorem toTickM_set (s' : σ) :
    (CostM.set s' : CostM σ 0 Unit).toTickM = TickM.set s' := rfl

/-- The image of a Kleisli arrow into `CostM σ n` has cost at most `n`. -/
theorem costBounded_toTickM (k : α → CostM σ n β) :
    UCMonad.costBounded n (fun a => (k a).toTickM) :=
  (TickM.costBounded_iff_run _).mpr fun a s => (k a).cost_le s

end CostM

/-- The Kleisli arrows into `CostM σ n` are the arrows of `TickM σ` of cost at most `n`. -/
def costBoundedEquiv {σ α β : Type} {n : ℕ} :
    {f : α → TickM σ β // UCMonad.costBounded n f} ≃ (α → CostM σ n β) where
  toFun f a := ⟨(f.1 a).run, (TickM.costBounded_iff_run f.1).mp f.2 a⟩
  invFun k := ⟨fun a => (k a).toTickM, CostM.costBounded_toTickM k⟩
  left_inv _ := rfl
  right_inv _ := rfl

end CatCrypt.XDijkstra
