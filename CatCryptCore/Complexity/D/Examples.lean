/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Complexity.D.Cost
public import Mathlib.Data.Nat.Size

/-!
# Examples of the deep language D

Three D-terms with their denotations and their costs:

* `sumBody`: the sum of a list of naturals by `foldl`; it denotes `List.foldl (· + ·) 0`
  (`sumBody_den`) and costs at most `size (sum l) + 2` steps per element, one β-step and an
  addition charged by the bit lengths of its operands (`sumBody_cost_le`).
* `twice` applied to the successor `succT` and a numeral `n`: it denotes `n + 2`
  (`twice_succ_den`) and costs four β-steps and two additions,
  `6 + max (size n) 1 + max (size (n + 1)) 1` steps (`twice_succ_cost`); applied to the
  successor `succW w` on `w`-bit words it costs six steps (`twice_succW_cost`).
* `xorSample k`: a uniformly sampled byte XOR a constant `k`; it denotes
  `SPComp.bind (SPComp.sample _) fun x => SPComp.pure (x ^^^ k)` (`xorSample_denote`, and
  `xorSample_run_eval` for the evaluator) and costs three steps: the sample, the β-step of the
  `letE` and the XOR (`xorSample_cost`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Complexity.D.Examples

open CatCrypt.Core Tm

/-! ## Sum of a list -/

/-- The addition of a pair, as a function term. -/
def addT {Γ : List Ty} : Tm Γ (.arr (.prod .nat .nat) .nat) := lam (prim .natAdd (var .here))

/-- The sum of the list in the innermost variable. -/
def sumBody : Tm [.list .nat] .nat := foldl addT (natLit 0) (var .here)

/-- The value of `addT` under the step node `tk`: `max (size x) (size y) + 1` step nodes, then
the sum. -/
def addStep (tk : ∀ {α : Type}, CTree α → CTree α) : Val (.arr (.prod .nat .nat) .nat) :=
  fun (p : ℕ × ℕ) => stepN tk (max p.1.size p.2.size + 1) (CTree.ret (p.1 + p.2))

theorem foldT_add_den (l : List ℕ) :
    ∀ acc : ℕ, foldT (fun t => t) (addStep fun t => t) acc l =
        .ret (List.foldl (fun x y : ℕ => x + y) acc l : ℕ) := by
  induction l with
  | nil => intro acc; rfl
  | cons x xs ih =>
    intro acc
    have e : foldT (fun t => t) (addStep fun t => t) acc (x :: xs) =
        foldT (fun t => t) (addStep fun t => t) (acc + x) xs := by
      show (stepN (fun t => t) _ (CTree.ret (acc + x))).bind _ = _
      rw [stepN_id]
      rfl
    exact e.trans (ih (acc + x))

theorem foldT_add_cost_le (l : List ℕ) :
    ∀ acc : ℕ, (foldT CTree.tick (addStep CTree.tick) acc l).cost ≤
      l.length * ((acc + l.sum).size + 2) := by
  induction l with
  | nil => intro acc; exact Nat.zero_le _
  | cons x xs ih =>
    intro acc
    have h := ih (acc + x)
    have e : (foldT CTree.tick (addStep CTree.tick) acc (x :: xs)).cost =
        1 + (max acc.size x.size + 1 +
          (foldT CTree.tick (addStep CTree.tick) (acc + x) xs).cost) := by
      show ((CTree.tick (stepN CTree.tick (max acc.size x.size + 1) (CTree.ret (acc + x)))).bind
        fun acc' => foldT CTree.tick (addStep CTree.tick) acc' xs).cost = _
      rw [CTree.bind_tick, stepN_tick_bind, CTree.cost_tick, cost_stepN_tick]
      rfl
    have hs : acc + x + xs.sum = acc + (x :: xs).sum := by
      rw [List.sum_cons]; omega
    have ha : acc.size ≤ (acc + (x :: xs).sum).size := Nat.size_le_size (Nat.le_add_right _ _)
    have hx : x.size ≤ (acc + (x :: xs).sum).size := by
      apply Nat.size_le_size
      rw [List.sum_cons]
      omega
    rw [hs] at h
    refine (le_of_eq e).trans ?_
    have hm : max acc.size x.size ≤ (acc + (x :: xs).sum).size := max_le ha hx
    simp only [List.length_cons, Nat.succ_mul]
    omega

theorem sumBody_den (l : List ℕ) :
    sumBody.den (Env.nil.cons (τ := .list .nat) l) =
      .ret (List.foldl (fun x y : ℕ => x + y) 0 l : ℕ) :=
  foldT_add_den l 0

/-- The sum costs at most `size (sum l) + 2` steps per element: one β-step and an addition
whose operands are at most the sum. -/
theorem sumBody_cost_le (l : List ℕ) :
    sumBody.cost (Env.nil.cons (τ := .list .nat) l) ≤ l.length * (l.sum.size + 2) := by
  have h := foldT_add_cost_le l 0
  rw [Nat.zero_add] at h
  exact h

/-! ## A function applied twice -/

/-- `λf. λx. f (f x)`. -/
def twice {Γ : List Ty} {a : Ty} : Tm Γ (.arr (.arr a a) (.arr a a)) :=
  lam (lam (app (var (.there .here)) (app (var (.there .here)) (var .here))))

/-- The successor on `ℕ`. -/
def succT {Γ : List Ty} : Tm Γ (.arr .nat .nat) := lam (prim .natAdd (pair (var .here) (natLit 1)))

theorem twice_succ_den (n : ℕ) :
    (app (app twice succT) (natLit n)).den Env.nil = .ret (n + 1 + 1) := by
  dsimp only [Tm.den, Tm.interp, twice, succT]
  simp only [stepN_id, CTree.bind_ret]
  rfl

/-- Four β-steps and two additions of one, at `n` and at `n + 1`. -/
theorem twice_succ_cost (n : ℕ) :
    (app (app twice succT) (natLit n)).cost Env.nil =
      6 + max n.size 1 + max (n + 1).size 1 := by
  let k : ℕ → CTree ℕ := fun v => CTree.tick (stepN CTree.tick (max v.size (1 : ℕ).size + 1)
    (CTree.ret (v + 1)))
  show (CTree.tick (CTree.tick ((CTree.tick (stepN CTree.tick (max n.size (1 : ℕ).size + 1)
    (CTree.ret (n + 1)))).bind k))).cost = _
  rw [CTree.bind_tick, stepN_tick_bind, CTree.bind_ret]
  simp only [k, CTree.cost_tick, cost_stepN_tick, CTree.cost_ret, Nat.size_one]
  omega

/-- The successor on `w`-bit words. -/
def succW {Γ : List Ty} (w : ℕ) : Tm Γ (.arr (.word w) (.word w)) :=
  lam (prim (.wadd w) (pair (var .here) (lit (.word w) (1 : BitVec w))))

/-- On words every primitive costs one step: four β-steps and two additions. -/
theorem twice_succW_cost (w : ℕ) (x : BitVec w) :
    (app (app twice (succW w)) (lit (.word w) x)).cost Env.nil = 6 := rfl

/-! ## An effectful sampler -/

/-- Sample a byte and XOR it with `k`. -/
def xorSample (k : BitVec 8) : Tm [] (.word 8) :=
  letE (sample (.word 8)) (prim (.wxor 8) (pair (var .here) (lit (.word 8) k)))

theorem xorSample_denote (O : CTree.Oracle) (k : BitVec 8) :
    (xorSample k).denote O Env.nil =
      SPComp.bind (SPComp.sample (FTy.word 8).den) fun x : BitVec 8 => SPComp.pure (x ^^^ k) :=
  rfl

theorem xorSample_run_eval (O : CTree.Oracle) (k : BitVec 8) :
    ((xorSample k).eval Env.nil).run O =
      SPComp.bind (SPComp.sample (FTy.word 8).den) fun x : BitVec 8 => SPComp.pure (x ^^^ k) :=
  ((xorSample k).run_eval O trivial (fun _ h => nomatch h) Env.nil).trans
    (xorSample_denote O k)

theorem xorSample_cost (k : BitVec 8) : (xorSample k).cost Env.nil = 3 := by
  rw [xorSample, cost_letE_sample]
  have h : ∀ x : (FTy.word 8).den,
      (prim (.wxor 8) (pair (var .here) (lit (.word 8) k))).cost
        (Env.nil.cons (τ := .word 8) x) = 1 := fun _ => rfl
  simp only [h]
  rw [Finset.sup_const Finset.univ_nonempty]

end CatCrypt.Complexity.D.Examples
