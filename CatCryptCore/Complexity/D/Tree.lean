/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Core.Code

/-!
# Costed effect trees for the deep language D

`CTree α` is the result type of the evaluator of the deep call-by-value language D
(`CatCryptCore.Complexity.D.Semantics`): a computation tree whose nodes are the effects of D
(`sample`, `get`, `set`, `query`) and a `tick` node for one evaluation step (a β-step, a
branch or a primitive operation). It lives in `Type` (the effect nodes range over the finite
ground types `FTy`), so that a function value of D, a Lean function `Val a → CTree (Val b)`, is
again a value that a tree can return.

## Main definitions

* `FTy`: the finite ground types (unit, booleans, `w`-bit words, residues `Fin (n + 1)`) over
  which the effects range.
* `CTree`: the trees, with a `fail` node of cost `0` meaning `SPComp.fail`, and `CTree.bind`
  (substitution at the leaves).
* `CTree.cost`: worst-case step count: one per `tick` and one per effect node, the maximum over
  the branches of `sample`, `get` and `query` (the convention of `SPTree.queryCost`).
* `CTree.erase`: the tree with its `tick` nodes removed.
* `CTree.run`: the denotation in `SPComp`, given an implementation of the oracle; ticks are
  not observable.
* `CTree.AllRet`: a predicate holds at every leaf.
* `CTree.Rel`: the lifting of a relation on leaves to trees, with `tick` nodes allowed on the
  left only.

## Main results

* `CTree.cost_bind_le`: the cost of a bind is at most the cost of the tree plus a bound on the
  continuation at the leaves (bind adds).
* `CTree.cost_bind_sample`: a sample node followed by a continuation costs one plus the
  maximum over the branches.
* `CTree.Rel.bind`: related trees and related continuations give related binds.
* `CTree.Rel.erase_eq`: trees related by equality agree after erasing the ticks.
* `CTree.run_erase`: erasing ticks does not change the denotation.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Complexity.D

open CatCrypt.Core

/-! ## Finite ground types -/

/-- The finite ground types of D: the types over which `sample`, `get`, `set` and `query`
range. -/
inductive FTy : Type where
  /-- The unit type. -/
  | unit
  /-- The booleans. -/
  | bool
  /-- Words of `w` bits. -/
  | word (w : ℕ)
  /-- The residues modulo `n + 1`, `Fin (n + 1)`, which is `ZMod (n + 1)` by definition. -/
  | fin (n : ℕ)
  deriving DecidableEq

/-- The Lean type of a finite ground type. -/
def FTy.den : FTy → Type
  | .unit => Unit
  | .bool => Bool
  | .word w => BitVec w
  | .fin n => Fin (n + 1)

instance FTy.instFintype : (f : FTy) → Fintype f.den
  | .unit => inferInstanceAs (Fintype Unit)
  | .bool => inferInstanceAs (Fintype Bool)
  | .word w => Fintype.ofEquiv (Fin (2 ^ w))
      ⟨BitVec.ofFin, BitVec.toFin, fun _ => rfl, fun _ => rfl⟩
  | .fin n => inferInstanceAs (Fintype (Fin (n + 1)))

instance FTy.instInhabited : (f : FTy) → Inhabited f.den
  | .unit => inferInstanceAs (Inhabited Unit)
  | .bool => inferInstanceAs (Inhabited Bool)
  | .word w => inferInstanceAs (Inhabited (BitVec w))
  | .fin n => inferInstanceAs (Inhabited (Fin (n + 1)))

instance FTy.instNonempty (f : FTy) : Nonempty f.den := ⟨default⟩

/-- The heap location with identifier `n` holding a value of type `f`. -/
def FTy.loc (f : FTy) (n : ℕ) : Location := { id := n, ty := f.den }

/-! ## Trees -/

/-- Costed effect trees: the effects of D and a `tick` node for one evaluation step. -/
inductive CTree (α : Type) : Type where
  /-- Return a value. -/
  | ret : α → CTree α
  /-- One evaluation step, then continue. -/
  | tick : CTree α → CTree α
  /-- Sample uniformly from `f` and continue with `k`. -/
  | sample (f : FTy) (k : f.den → CTree α) : CTree α
  /-- Read location `n` of type `f` and continue with `k`. -/
  | get (n : ℕ) (f : FTy) (k : f.den → CTree α) : CTree α
  /-- Write `v` to location `n` of type `f` and continue with `k`. -/
  | set (n : ℕ) (f : FTy) (v : f.den) (k : CTree α) : CTree α
  /-- Query the oracle at `x` (input type `d`, output type `r`) and continue with `k`. -/
  | query (d r : FTy) (x : d.den) (k : r.den → CTree α) : CTree α
  /-- Failure: no result, at no cost. -/
  | fail : CTree α

namespace CTree

variable {α β γ : Type}

/-- Substitution at the leaves. -/
def bind : CTree α → (α → CTree β) → CTree β
  | ret a, g => g a
  | tick t, g => tick (t.bind g)
  | sample f k, g => sample f fun x => (k x).bind g
  | get n f k, g => get n f fun x => (k x).bind g
  | set n f v k, g => set n f v (k.bind g)
  | query d r x k, g => query d r x fun y => (k y).bind g
  | fail, _ => fail

/-- Worst-case step count: one per `tick` and per effect node, the maximum over the
branches. -/
def cost : CTree α → ℕ
  | ret _ => 0
  | tick t => 1 + t.cost
  | sample _ k => 1 + Finset.univ.sup fun x => (k x).cost
  | get _ _ k => 1 + Finset.univ.sup fun x => (k x).cost
  | set _ _ _ k => 1 + k.cost
  | query _ _ _ k => 1 + Finset.univ.sup fun y => (k y).cost
  | fail => 0

/-- The tree without its `tick` nodes. -/
def erase : CTree α → CTree α
  | ret a => ret a
  | tick t => t.erase
  | sample f k => sample f fun x => (k x).erase
  | get n f k => get n f fun x => (k x).erase
  | set n f v k => set n f v k.erase
  | query d r x k => query d r x fun y => (k y).erase
  | fail => fail

/-- An implementation of the oracle: a stateful probabilistic computation per input. -/
abbrev Oracle : Type := (d r : FTy) → d.den → SPComp r.den

/-- The denotation of a tree in `SPComp`, the oracle answered by `O`; ticks are skipped. -/
noncomputable def run (O : Oracle) : CTree α → SPComp α
  | ret a => SPComp.pure a
  | tick t => t.run O
  | sample f k => SPComp.bind (SPComp.sample f.den) fun x => (k x).run O
  | get n f k => SPComp.bind (SPComp.get (f.loc n)) fun x => (k x).run O
  | set n f v k => SPComp.bind (SPComp.set (f.loc n) v) fun _ => k.run O
  | query d r x k => SPComp.bind (O d r x) fun y => (k y).run O
  | fail => SPComp.fail

/-- `P` holds at every leaf of the tree. -/
def AllRet (P : α → Prop) : CTree α → Prop
  | ret a => P a
  | tick t => t.AllRet P
  | sample _ k => ∀ x, (k x).AllRet P
  | get _ _ k => ∀ x, (k x).AllRet P
  | set _ _ _ k => k.AllRet P
  | query _ _ _ k => ∀ y, (k y).AllRet P
  | fail => True

@[simp] theorem bind_ret (a : α) (g : α → CTree β) : (ret a).bind g = g a := rfl

@[simp] theorem bind_tick (t : CTree α) (g : α → CTree β) :
    (tick t).bind g = tick (t.bind g) := rfl

@[simp] theorem cost_ret (a : α) : (ret a).cost = 0 := rfl

@[simp] theorem cost_tick (t : CTree α) : (tick t).cost = 1 + t.cost := rfl

@[simp] theorem bind_fail (g : α → CTree β) : (fail : CTree α).bind g = fail := rfl

@[simp] theorem cost_fail : (fail : CTree α).cost = 0 := rfl

@[simp] theorem run_fail (O : Oracle) : (fail : CTree α).run O = SPComp.fail := rfl

/-! ## Monad laws -/

theorem bind_ret_right (t : CTree α) : t.bind ret = t := by
  induction t <;> simp_all [bind]

theorem bind_assoc (t : CTree α) (g : α → CTree β) (h : β → CTree γ) :
    (t.bind g).bind h = t.bind fun a => (g a).bind h := by
  induction t <;> simp_all [bind]

/-! ## Cost of a bind -/

theorem AllRet.mono {P Q : α → Prop} (hPQ : ∀ a, P a → Q a) {t : CTree α}
    (h : t.AllRet P) : t.AllRet Q := by
  induction t <;> simp_all [AllRet]

theorem AllRet.of_forall {P : α → Prop} (hP : ∀ a, P a) (t : CTree α) : t.AllRet P := by
  induction t <;> simp_all [AllRet]

theorem sup_le_sup_add {ι : Type} [Fintype ι] (a b : ι → ℕ) (B : ℕ)
    (h : ∀ x, a x ≤ b x + B) : Finset.univ.sup a ≤ Finset.univ.sup b + B :=
  Finset.sup_le fun x _ =>
    (h x).trans (Nat.add_le_add_right (Finset.le_sup (f := b) (Finset.mem_univ x)) B)

/-- Bind adds: the cost of `t.bind g` is at most the cost of `t` plus a bound on the cost of
`g` at the leaves of `t`. -/
theorem cost_bind_le (t : CTree α) (g : α → CTree β) (B : ℕ)
    (h : t.AllRet fun a => (g a).cost ≤ B) : (t.bind g).cost ≤ t.cost + B := by
  induction t with
  | ret a => simpa [bind, cost, AllRet] using h
  | tick t ih => simp only [bind, cost, AllRet] at h ⊢; have := ih h; omega
  | sample f k ih =>
    simp only [bind, cost, AllRet] at h ⊢
    have := sup_le_sup_add _ _ B fun x => ih x (h x)
    omega
  | get n f k ih =>
    simp only [bind, cost, AllRet] at h ⊢
    have := sup_le_sup_add _ _ B fun x => ih x (h x)
    omega
  | set n f v k ih => simp only [bind, cost, AllRet] at h ⊢; have := ih h; omega
  | query d r x k ih =>
    simp only [bind, cost, AllRet] at h ⊢
    have := sup_le_sup_add _ _ B fun x => ih x (h x)
    omega
  | fail => simp only [bind, cost]; omega

/-- A sample node followed by `g` costs one plus the maximum over the branches. -/
theorem cost_bind_sample (f : FTy) (k : f.den → CTree α) (g : α → CTree β) :
    ((sample f k).bind g).cost = 1 + Finset.univ.sup fun x => ((k x).bind g).cost := rfl

/-- A leaf followed by `g` costs what `g` costs there. -/
theorem cost_bind_ret (a : α) (g : α → CTree β) : ((ret a).bind g).cost = (g a).cost := rfl

/-- A predicate holds at the leaves of a bind if it holds at the leaves of the continuation
at every leaf of the tree. -/
theorem allRet_bind {P : β → Prop} (t : CTree α) (g : α → CTree β)
    (h : t.AllRet fun a => (g a).AllRet P) : (t.bind g).AllRet P := by
  induction t <;> simp_all [AllRet, bind]

/-! ## Erasure and denotation -/

theorem run_erase (O : Oracle) (t : CTree α) : t.erase.run O = t.run O := by
  induction t with
  | ret a => rfl
  | tick t ih => exact ih
  | sample f k ih => simp only [erase, run]; exact congrArg _ (funext ih)
  | get n f k ih => simp only [erase, run]; exact congrArg _ (funext ih)
  | set n f v k ih => simp only [erase, run]; exact congrArg _ (funext fun _ => ih)
  | query d r x k ih => simp only [erase, run]; exact congrArg _ (funext ih)
  | fail => rfl

theorem run_bind (O : Oracle) (t : CTree α) (g : α → CTree β) :
    (t.bind g).run O = SPComp.bind (t.run O) fun a => (g a).run O := by
  induction t with
  | ret a => exact (SPComp.pure_bind a fun a => (g a).run O).symm
  | tick t ih => exact ih
  | sample f k ih =>
    simp only [bind, run]; rw [SPComp.bind_assoc]; exact congrArg _ (funext ih)
  | get n f k ih =>
    simp only [bind, run]; rw [SPComp.bind_assoc]; exact congrArg _ (funext ih)
  | set n f v k ih =>
    simp only [bind, run]; rw [SPComp.bind_assoc]; exact congrArg _ (funext fun _ => ih)
  | query d r x k ih =>
    simp only [bind, run]; rw [SPComp.bind_assoc]; exact congrArg _ (funext ih)
  | fail => exact (SPComp.fail_bind _).symm

/-! ## Relational lifting -/

/-- The lifting of `R` to trees: the effect nodes agree, the leaves are related, and the left
tree may carry `tick` nodes. -/
inductive Rel {α β : Type} (R : α → β → Prop) : CTree α → CTree β → Prop where
  | ret {a : α} {b : β} : R a b → Rel R (ret a) (ret b)
  | tick {t : CTree α} {m : CTree β} : Rel R t m → Rel R (tick t) m
  | sample (f : FTy) {k : f.den → CTree α} {k' : f.den → CTree β} :
      (∀ x, Rel R (k x) (k' x)) → Rel R (sample f k) (sample f k')
  | get (n : ℕ) (f : FTy) {k : f.den → CTree α} {k' : f.den → CTree β} :
      (∀ x, Rel R (k x) (k' x)) → Rel R (get n f k) (get n f k')
  | set (n : ℕ) (f : FTy) (v : f.den) {k : CTree α} {k' : CTree β} :
      Rel R k k' → Rel R (set n f v k) (set n f v k')
  | query (d r : FTy) (x : d.den) {k : r.den → CTree α} {k' : r.den → CTree β} :
      (∀ y, Rel R (k y) (k' y)) → Rel R (query d r x k) (query d r x k')
  | fail : Rel R fail fail

theorem Rel.bind {α' β' : Type} {R : α → β → Prop} {S : α' → β' → Prop}
    {t : CTree α} {m : CTree β} (h : Rel R t m) {g : α → CTree α'} {g' : β → CTree β'}
    (hg : ∀ a b, R a b → Rel S (g a) (g' b)) : Rel S (t.bind g) (m.bind g') := by
  induction h with
  | ret hab => exact hg _ _ hab
  | tick _ ih => exact .tick ih
  | sample f _ ih => exact .sample f ih
  | get n f _ ih => exact .get n f ih
  | set n f v _ ih => exact .set n f v ih
  | query d r x _ ih => exact .query d r x ih
  | fail => exact .fail

theorem Rel.mono {R S : α → β → Prop} (hRS : ∀ a b, R a b → S a b) {t : CTree α}
    {m : CTree β} (h : Rel R t m) : Rel S t m := by
  induction h with
  | ret hab => exact .ret (hRS _ _ hab)
  | tick _ ih => exact .tick ih
  | sample f _ ih => exact .sample f ih
  | get n f _ ih => exact .get n f ih
  | set n f v _ ih => exact .set n f v ih
  | query d r x _ ih => exact .query d r x ih
  | fail => exact .fail

/-- Trees related by equality agree after erasing the ticks of the left one. -/
theorem Rel.erase_eq {t m : CTree α} (h : Rel (· = ·) t m) : t.erase = m := by
  induction h with
  | ret hab => exact congrArg CTree.ret hab
  | tick _ ih => exact ih
  | sample f _ ih => exact congrArg (CTree.sample f) (funext ih)
  | get n f _ ih => exact congrArg (CTree.get n f) (funext ih)
  | set n f v _ ih => exact congrArg (CTree.set n f v) ih
  | query d r x _ ih => exact congrArg (CTree.query d r x) (funext ih)
  | fail => rfl

end CTree

end CatCrypt.Complexity.D
