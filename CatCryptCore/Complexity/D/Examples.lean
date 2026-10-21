/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Complexity.D.Cost

/-!
# Examples of the deep language D

Three D-terms with their denotations and their costs:

* `sumBody`: the sum of a list of naturals by `foldl`; it denotes `List.foldl (· + ·) 0`
  (`sumBody_den`) and costs two steps per element, one β-step and one addition
  (`sumBody_cost`).
* `twice` applied to the successor `succT` and a numeral `n`: it denotes `n + 2`
  (`twice_succ_den`) and costs six steps (`twice_succ_cost`).
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

theorem foldT_add_den (l : List ℕ) :
    ∀ acc : ℕ, foldT (fun t => t) (a := .nat) (c := .nat)
      (fun p : ℕ × ℕ => CTree.ret (p.1 + p.2)) acc l =
        .ret (List.foldl (fun x y : ℕ => x + y) acc l : ℕ) := by
  induction l with
  | nil => intro acc; rfl
  | cons x xs ih => intro acc; exact ih (acc + x)

theorem foldT_add_cost (l : List ℕ) :
    ∀ acc : ℕ, (foldT CTree.tick (a := .nat) (c := .nat)
      (fun p : ℕ × ℕ => CTree.tick (CTree.ret (p.1 + p.2))) acc l).cost = 2 * l.length := by
  induction l with
  | nil => intro acc; rfl
  | cons x xs ih =>
    intro acc
    have h := ih (acc + x)
    have e : (foldT CTree.tick (a := .nat) (c := .nat)
        (fun p : ℕ × ℕ => CTree.tick (CTree.ret (p.1 + p.2))) acc (x :: xs)).cost =
        1 + (1 + (foldT CTree.tick (a := .nat) (c := .nat)
          (fun p : ℕ × ℕ => CTree.tick (CTree.ret (p.1 + p.2))) (acc + x) xs).cost) := rfl
    refine e.trans ?_
    simp only [List.length_cons]
    omega

theorem sumBody_den (l : List ℕ) :
    sumBody.den (Env.nil.cons (τ := .list .nat) l) =
      .ret (List.foldl (fun x y : ℕ => x + y) 0 l : ℕ) :=
  foldT_add_den l 0

theorem sumBody_cost (l : List ℕ) :
    sumBody.cost (Env.nil.cons (τ := .list .nat) l) = 2 * l.length :=
  foldT_add_cost l 0

/-! ## A function applied twice -/

/-- `λf. λx. f (f x)`. -/
def twice {Γ : List Ty} {a : Ty} : Tm Γ (.arr (.arr a a) (.arr a a)) :=
  lam (lam (app (var (.there .here)) (app (var (.there .here)) (var .here))))

/-- The successor on `ℕ`. -/
def succT {Γ : List Ty} : Tm Γ (.arr .nat .nat) := lam (prim .natAdd (pair (var .here) (natLit 1)))

theorem twice_succ_den (n : ℕ) :
    (app (app twice succT) (natLit n)).den Env.nil = .ret (n + 1 + 1) := rfl

theorem twice_succ_cost (n : ℕ) : (app (app twice succT) (natLit n)).cost Env.nil = 6 := rfl

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
