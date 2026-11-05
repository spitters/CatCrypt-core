/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Complexity.D.Link

/-!
# The exact cost reading of D terms as costed trees

The evaluator of D (`Tm.eval`) places one `tick` node at every evaluation step, the cost model
of the call-by-value λ-calculus of Forster and Kunze (*A Certifying Extraction with Time
Bounds from Coq to Call-By-Value Lambda Calculus*, ITP 2019). `Tm.timedD t ρ` reads the
evaluation tree back as a step-prefixed costed tree `ℕ × SPTree.Timed (Val τ)`, the form of
the certificates of `derive_timed`: `(t.eval ρ).costTree`.

`CTree.costTree` is a morphism of trees: a `tick` is a step cost `1` in front
(`CTree.costTree_tick`), `n` ticks are a step cost `n` (`CTree.costTree_stepN`), and the
substitution of `CTree` is the costed bind behind the step cost of the tree
(`CTree.costTree_bind`). With the defining clauses of the evaluator this gives one equation
per construct, for example `Tm.timedD_app`, `Tm.timedD_letE`, `Tm.timedD_prim`. The left fold
and the iteration of a function value have the costed forms `foldTimed` and `iterTimed`
(`costTree_foldT`, `costTree_iterT`).

The reading is exact and sound. The time of `t.timedD ρ` is the cost of `t` at `ρ`
(`Tm.stepTime_timedD`); the evaluation tree is simulated by it at factor `1` with no
allowance (`Tm.timedSim_timedD`); at a first-order term over a first-order context whose
evaluation is query-free, its erasure compiles to the denotation (`Tm.compile_erase_timedD`).

## Main definitions

* `Tm.timedD`, `foldTimed`, `iterTimed`

## Main results

* `CTree.costTree_tick`, `CTree.costTree_stepN`, `CTree.costTree_bind`
* `costTree_foldT`, `costTree_iterT`
* `Tm.timedD_app`, `Tm.timedD_letE`, `Tm.timedD_prim`
* `Tm.timedSim_timedD`, `Tm.stepTime_timedD`, `Tm.compile_erase_timedD`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Complexity.D

open CatCrypt.Core

namespace CTree

variable {α β : Type}

/-- The costed tree of a returned value. -/
theorem costTree_ret (a : α) : (ret a : CTree α).costTree = (0, .ret a) := rfl

/-- A tick is a step cost `1` in front of the costed tree. -/
theorem costTree_tick (t : CTree α) :
    (tick t).costTree = SPTree.Timed.delay 1 t.costTree := rfl

/-- `n` ticks are a step cost `n` in front of the costed tree. -/
theorem costTree_stepN (n : ℕ) (t : CTree α) :
    (stepN CTree.tick n t).costTree = SPTree.Timed.delay n t.costTree := by
  induction n with
  | zero => simp [stepN, SPTree.Timed.delay]
  | succ n ih => grind [stepN, costTree_tick, SPTree.Timed.delay]

/-- The substitution of D trees is the costed bind behind the step cost of the tree. -/
theorem costTree_bind (t : CTree α) (g : α → CTree β) :
    (t.bind g).costTree =
      SPTree.Timed.delay t.costTree.1 (t.costTree.2.bind fun a => (g a).costTree) := by
  induction t with
  | ret a => simp [bind, costTree, SPTree.Timed.delay, SPTree.Timed.bind]
  | tick t ih => grind [bind, costTree, SPTree.Timed.delay]
  | sample f k ih => simp [bind, costTree, SPTree.Timed.delay, SPTree.Timed.bind, ih]
  | get n f k ih =>
    simp only [bind, costTree, SPTree.Timed.delay, SPTree.Timed.bind, Nat.zero_add,
      Prod.mk.injEq, SPTree.Timed.get.injEq, true_and]
    exact ⟨heq_of_eq (funext fun x => by rw [ih x]; rfl),
      heq_of_eq (funext fun x => by rw [ih x]; rfl)⟩
  | set n f v k ih => simp [bind, costTree, SPTree.Timed.delay, SPTree.Timed.bind, ih]
  | query d r x k ih => simp [bind, costTree, SPTree.Timed.delay, SPTree.Timed.bind, ih]
  | fail => simp [bind, costTree, SPTree.Timed.delay, SPTree.Timed.bind]

end CTree

/-! ## Folds -/

/-- The costed left fold of a function value: a step cost `1` and the costed tree of the
application per element. -/
noncomputable def foldTimed {a c : Ty} (g : Val (.arr (.prod c a) c)) :
    Val c → List (Val a) → ℕ × SPTree.Timed (Val c)
  | acc, [] => (0, .ret acc)
  | acc, x :: xs => SPTree.Timed.delay (1 + (g (acc, x)).costTree.1)
      ((g (acc, x)).costTree.2.bind fun acc' => foldTimed g acc' xs)

/-- The costed `n`-fold iteration of a function value: a step cost `1` and the costed tree of
the application per iteration. -/
noncomputable def iterTimed {c : Ty} (g : Val (.arr c c)) :
    Val c → ℕ → ℕ × SPTree.Timed (Val c)
  | acc, 0 => (0, .ret acc)
  | acc, n + 1 => SPTree.Timed.delay (1 + (g acc).costTree.1)
      ((g acc).costTree.2.bind fun acc' => iterTimed g acc' n)

/-- The costed tree of the evaluated left fold is the costed left fold. -/
theorem costTree_foldT {a c : Ty} (g : Val (.arr (.prod c a) c)) (acc : Val c)
    (l : List (Val a)) : (foldT CTree.tick g acc l).costTree = foldTimed g acc l := by
  induction l generalizing acc with
  | nil => rfl
  | cons x xs ih =>
    simp [foldT, foldTimed, CTree.costTree_bind, CTree.costTree_tick, SPTree.Timed.delay, ih,
      Nat.add_assoc]

/-- The costed tree of the evaluated iteration is the costed iteration. -/
theorem costTree_iterT {c : Ty} (g : Val (.arr c c)) (acc : Val c) (n : ℕ) :
    (iterT CTree.tick g acc n).costTree = iterTimed g acc n := by
  induction n generalizing acc with
  | zero => rfl
  | succ n ih =>
    simp [iterT, iterTimed, CTree.costTree_bind, CTree.costTree_tick, SPTree.Timed.delay, ih,
      Nat.add_assoc]

namespace Tm

variable {Γ : List Ty} {τ : Ty}

/-- The exact cost reading of a term: its evaluation tree as a step-prefixed costed tree. -/
noncomputable def timedD (t : Tm Γ τ) (ρ : Env Γ) : ℕ × SPTree.Timed (Val τ) :=
  (t.eval ρ).costTree

/-! ## The reading per construct -/

/-- An application: the costed function, the costed argument, a step cost `1` for the
β-step and the costed tree of the call. -/
theorem timedD_app {a b : Ty} (f : Tm Γ (.arr a b)) (x : Tm Γ a) (ρ : Env Γ) :
    (app f x).timedD ρ =
      SPTree.Timed.delay (f.timedD ρ).1 ((f.timedD ρ).2.bind fun g =>
        SPTree.Timed.delay (x.timedD ρ).1 ((x.timedD ρ).2.bind fun v =>
          SPTree.Timed.delay 1 (g v).costTree)) := by
  simp only [timedD, eval_app, CTree.costTree_bind, CTree.costTree_tick]

/-- A `let`: the costed bound term, then a step cost `1` and the costed body. -/
theorem timedD_letE {a b : Ty} (e : Tm Γ a) (body : Tm (a :: Γ) b) (ρ : Env Γ) :
    (letE e body).timedD ρ =
      SPTree.Timed.delay (e.timedD ρ).1 ((e.timedD ρ).2.bind fun v =>
        SPTree.Timed.delay 1 (body.timedD (ρ.cons v))) := by
  simp only [timedD, eval_letE, CTree.costTree_bind, CTree.costTree_tick]

/-- A primitive: the costed argument, then the cost of the primitive in front of its value. -/
theorem timedD_prim {a b : Ty} (p : Prim a b) (x : Tm Γ a) (ρ : Env Γ) :
    (prim p x).timedD ρ =
      SPTree.Timed.delay (x.timedD ρ).1 ((x.timedD ρ).2.bind fun v =>
        (p.cost v, .ret (p.apply v))) := by
  simp [timedD, eval, interp, CTree.costTree_bind, CTree.costTree_stepN,
    CTree.costTree_ret, SPTree.Timed.delay]

/-! ## Soundness -/

/-- The evaluation tree is simulated by its costed reading at factor `1` with no
allowance. -/
theorem timedSim_timedD (t : Tm Γ τ) (ρ : Env Γ) :
    TimedSim (· = ·) 1 0 (t.timedD ρ) (t.eval ρ) :=
  CTree.timedSim_costTree _

/-- The time of the costed reading is the cost of the term. -/
theorem stepTime_timedD (t : Tm Γ τ) (ρ : Env Γ) :
    SPTree.Timed.stepTime (t.timedD ρ) = t.cost ρ := by
  have h1 := CTree.stepTime_costTree_le (t.eval ρ)
  have h2 := (t.timedSim_timedD ρ).cost_le
  simp only [cost, timedD] at h1 h2 ⊢
  omega

/-- At a first-order term over a first-order context whose evaluation is query-free, the
erasure of the costed reading compiles to the denotation. -/
theorem compile_erase_timedD (O : CTree.Oracle) (t : Tm Γ τ) (hτ : τ.FO)
    (hΓ : ∀ σ ∈ Γ, σ.FO) (ρ : Env Γ) (hq : (t.eval ρ).QueryFree) :
    (t.timedD ρ).2.erase.compile = t.denote O ρ := by
  have hrel : (fun (a v : Val τ) => v = id a) = (· = ·) :=
    funext₂ fun _ _ => propext eq_comm
  have h := TimedSim.run (enc := id) (hrel ▸ t.timedSim_timedD ρ) hq O
  rw [← t.run_eval O hτ hΓ ρ, h]
  exact (SPComp.bind_pure _).symm

end Tm

end CatCrypt.Complexity.D
