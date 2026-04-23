/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Jasmin.PassFramework

/-!
# Constant Folding Pass

Fold constant expressions at compile time. This handles:
- Boolean negation: `!true → false`, `!false → true`
- Boolean binary ops: `true && false → false`, etc.
- Conditional elimination: `if true then e₁ else e₂ → e₁`

## Main definitions

* `constFoldExpr` — The constant folding transformation on expressions
* `constFoldExpr_correct` — Proof that the pass preserves `ExprPassCorrect`

## Proof technique

The correctness proof uses structural induction on `PExpr`. For each folding
case, the key step is: `eval(ret x >>= f) = f(x)` via `SPComp.pure_bind`,
which shows that pre-computing a pure expression yields the same result.
-/

namespace CatCrypt.Crypto.Jasmin

open CatCrypt.Deep (RawCode eval_bind eval_ret)
open CatCrypt.Core (SPComp)

set_option autoImplicit false

/-! ## Folding Helpers

Separate helpers for each folding rule make the equation compiler generate
clean equations and keep the main proof manageable. -/

/-- Fold a unary operation applied to a (possibly constant) expression.
    Currently folds: `Onot (Pbool b) → Pbool (!b)` -/
private def foldApp1 (op : SOp1) (e : PExpr) : PExpr :=
  match op, e with
  | .Onot, .Pbool b => .Pbool (!b)
  | _, _ => .Papp1 op e

/-- Fold a binary operation applied to (possibly constant) expressions.
    Currently folds boolean ops: Oand, Oor, Obeq on Pbool arguments. -/
private def foldApp2 (op : SOp2) (e₁ e₂ : PExpr) : PExpr :=
  match op, e₁, e₂ with
  | .Oand, .Pbool a, .Pbool b => .Pbool (a && b)
  | .Oor,  .Pbool a, .Pbool b => .Pbool (a || b)
  | .Obeq, .Pbool a, .Pbool b => .Pbool (a == b)
  | _, _, _ => .Papp2 op e₁ e₂

/-- Fold a conditional with a (possibly constant) condition.
    `Pbool true → et`, `Pbool false → ef`, otherwise keep. -/
private def foldIf (ty : SType) (cond et ef : PExpr) : PExpr :=
  match cond with
  | .Pbool true  => et
  | .Pbool false => ef
  | _ => .Pif ty cond et ef

/-! ## Main Pass -/

/-- Constant folding on Jasmin expressions. Recursively simplifies
    sub-expressions, then applies folding rules at each node. -/
def constFoldExpr : PExpr → PExpr
  | .Papp1 op e => foldApp1 op (constFoldExpr e)
  | .Papp2 op e₁ e₂ => foldApp2 op (constFoldExpr e₁) (constFoldExpr e₂)
  | .Pif ty cond et ef =>
    foldIf ty (constFoldExpr cond) (constFoldExpr et) (constFoldExpr ef)
  | .Pget aa ws x idx => .Pget aa ws x (constFoldExpr idx)
  | .Psub aa ws len x idx => .Psub aa ws len x (constFoldExpr idx)
  | .Pload ws x off => .Pload ws x (constFoldExpr off)
  | e => e  -- Pconst, Pbool, Parr_init, Pvar, PappN: unchanged

noncomputable section

/-! ## Correctness Proof -/

/-- Key lemma: `foldApp1` preserves eval when the input expression
    has the same eval as some original expression. -/
private theorem foldApp1_spec (op : SOp1) (e e₀ : PExpr) (sid : ScopeId)
    (h : (translatePExpr sid e).eval = (translatePExpr sid e₀).eval) :
    (translatePExpr sid (foldApp1 op e)).eval =
    (translatePExpr sid (.Papp1 op e₀)).eval := by
  unfold foldApp1
  split
  · -- op = .Onot, e = .Pbool b
    rename_i b
    have he₀ : (translatePExpr sid e₀).eval = SPComp.pure ⟨.sbool, b⟩ := by
      rw [← h]; rfl
    simp only [translatePExpr, eval_bind, eval_ret, he₀, SPComp.pure_bind, evalSop1]
  · -- no fold: .Papp1 op e
    simp only [translatePExpr, eval_bind, eval_ret, h]

/-- Key lemma: `foldApp2` preserves eval. -/
private theorem foldApp2_spec (op : SOp2) (e₁ e₂ e₁₀ e₂₀ : PExpr) (sid : ScopeId)
    (h₁ : (translatePExpr sid e₁).eval = (translatePExpr sid e₁₀).eval)
    (h₂ : (translatePExpr sid e₂).eval = (translatePExpr sid e₂₀).eval) :
    (translatePExpr sid (foldApp2 op e₁ e₂)).eval =
    (translatePExpr sid (.Papp2 op e₁₀ e₂₀)).eval := by
  unfold foldApp2
  split
  · -- Oand on two Pbools
    rename_i a b
    have he₁₀ : (translatePExpr sid e₁₀).eval = SPComp.pure ⟨.sbool, a⟩ := by
      rw [← h₁]; rfl
    have he₂₀ : (translatePExpr sid e₂₀).eval = SPComp.pure ⟨.sbool, b⟩ := by
      rw [← h₂]; rfl
    simp only [translatePExpr, eval_bind, eval_ret, he₁₀, he₂₀,
               SPComp.pure_bind, evalSop2]
  · -- Oor on two Pbools
    rename_i a b
    have he₁₀ : (translatePExpr sid e₁₀).eval = SPComp.pure ⟨.sbool, a⟩ := by
      rw [← h₁]; rfl
    have he₂₀ : (translatePExpr sid e₂₀).eval = SPComp.pure ⟨.sbool, b⟩ := by
      rw [← h₂]; rfl
    simp only [translatePExpr, eval_bind, eval_ret, he₁₀, he₂₀,
               SPComp.pure_bind, evalSop2]
  · -- Obeq on two Pbools
    rename_i a b
    have he₁₀ : (translatePExpr sid e₁₀).eval = SPComp.pure ⟨.sbool, a⟩ := by
      rw [← h₁]; rfl
    have he₂₀ : (translatePExpr sid e₂₀).eval = SPComp.pure ⟨.sbool, b⟩ := by
      rw [← h₂]; rfl
    simp only [translatePExpr, eval_bind, eval_ret, he₁₀, he₂₀,
               SPComp.pure_bind, evalSop2]
  · -- no fold: .Papp2 op e₁ e₂
    simp only [translatePExpr, eval_bind, eval_ret, h₁, h₂]

/-- Key lemma: `foldIf` preserves eval. -/
private theorem foldIf_spec (ty : SType) (cond et ef cond₀ et₀ ef₀ : PExpr)
    (sid : ScopeId)
    (hc : (translatePExpr sid cond).eval = (translatePExpr sid cond₀).eval)
    (ht : (translatePExpr sid et).eval = (translatePExpr sid et₀).eval)
    (hf : (translatePExpr sid ef).eval = (translatePExpr sid ef₀).eval) :
    (translatePExpr sid (foldIf ty cond et ef)).eval =
    (translatePExpr sid (.Pif ty cond₀ et₀ ef₀)).eval := by
  unfold foldIf
  split
  · -- cond = .Pbool true
    have hc₀ : (translatePExpr sid cond₀).eval = SPComp.pure ⟨.sbool, true⟩ := by
      rw [← hc]; rfl
    simp only [translatePExpr, eval_bind, eval_ret, hc₀, SPComp.pure_bind]
    exact ht
  · -- cond = .Pbool false
    rename_i _
    have hc₀ : (translatePExpr sid cond₀).eval = SPComp.pure ⟨.sbool, false⟩ := by
      rw [← hc]; rfl
    simp only [translatePExpr, eval_bind, eval_ret, hc₀, SPComp.pure_bind]
    exact hf
  · -- no fold: .Pif ty cond et ef
    show (translatePExpr sid (.Pif ty cond et ef)).eval =
         (translatePExpr sid (.Pif ty cond₀ et₀ ef₀)).eval
    simp only [translatePExpr, eval_bind, hc]
    congr 1
    funext ⟨sty, val⟩
    cases sty with
    | sbool => cases val with
      | false => exact hf
      | true => exact ht
    | sint => exact ht
    | sarr => exact ht
    | sword => exact ht

/-- Constant folding preserves expression semantics.
    Proved by structural recursion on `PExpr`, matching `constFoldExpr`'s pattern. -/
theorem constFoldExpr_correct : ExprPassCorrect constFoldExpr := fun sid e =>
  match e with
  | .Pconst _ | .Pbool _ | .Parr_init _ | .Pvar _ | .PappN _ _ => rfl
  | .Papp1 op e => by
    simp only [constFoldExpr]
    exact foldApp1_spec op _ e sid (constFoldExpr_correct sid e)
  | .Papp2 op e₁ e₂ => by
    simp only [constFoldExpr]
    exact foldApp2_spec op _ _ e₁ e₂ sid
      (constFoldExpr_correct sid e₁) (constFoldExpr_correct sid e₂)
  | .Pif ty cond et ef => by
    simp only [constFoldExpr]
    exact foldIf_spec ty _ _ _ cond et ef sid
      (constFoldExpr_correct sid cond) (constFoldExpr_correct sid et)
      (constFoldExpr_correct sid ef)
  | .Pget _ _ _ idx => by
    simp only [constFoldExpr, translatePExpr, eval_bind,
               constFoldExpr_correct sid idx]
  | .Psub _ _ _ _ idx => by
    simp only [constFoldExpr, translatePExpr, eval_bind]
  | .Pload _ _ off => by
    simp only [constFoldExpr, translatePExpr, eval_bind,
               constFoldExpr_correct sid off]

end

end CatCrypt.Crypto.Jasmin
