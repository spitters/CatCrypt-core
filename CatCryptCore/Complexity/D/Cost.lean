/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Complexity.D.Semantics

/-!
# Cost semantics of the deep language D

The cost of a term `t` in an environment `ρ` is `Tm.cost t ρ`, the worst-case step count
`CTree.cost` of its evaluation `Tm.eval t ρ`: one unit per β-step and branch, `p.cost v` units
for a primitive operation `p` at the argument `v` (logarithmic in the bit lengths on `ℕ`,
`Prim.cost`), and one unit per effect node, the maximum over the branches of `sample`, `get`
and `query`. It is determined by the evaluator, not supplied with the term.

## Main results

* `Tm.cost_app_le`, `Tm.cost_app_lam`: an application costs the function, the argument, one
  β-step and the body.
* `Tm.cost_letE_le`, `Tm.cost_letE_ret`: a `letE` costs its bound term once, one β-step and
  the body; the variable costs nothing at its uses (`Tm.cost_var`).
* `Tm.cost_prim`, `Tm.cost_prim_le`: a primitive operation costs its argument and `Prim.cost`
  of the argument's value.
* `Tm.cost_letE_sample`: a sample followed by a continuation costs one plus the maximum over
  the sampled values.
* `foldT_cost_le`, `iterT_cost_le`: a recursion scheme costs at most the number of iterations
  times one plus the cost of one application.
* `Tm.cost_compose_le`, `Tm.allRet_compose`, `Tm.cost_app_compose_le`: precomposition of
  function terms; the costs add.

Sequencing of effects is `CTree.cost_bind_le` (bind adds) and `CTree.cost_bind_sample` (a
sample takes the maximum over its branches).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Complexity.D

open CTree

/-- `n` ticks cost `n`. -/
@[simp] theorem cost_stepN_tick {α : Type} (n : ℕ) (t : CTree α) :
    (stepN CTree.tick n t).cost = n + t.cost := by
  induction n with
  | zero => simp [stepN]
  | succ n ih => simp only [stepN, CTree.cost_tick, ih]; omega

/-! ## Recursion schemes -/

theorem foldT_cost_le {a c : Ty} (g : Val (.arr (.prod c a) c)) (B : ℕ)
    (hg : ∀ p, (g p).cost ≤ B) (l : List (Val a)) :
    ∀ acc : Val c, (foldT CTree.tick g acc l).cost ≤ l.length * (1 + B) := by
  induction l with
  | nil => intro acc; simp [foldT]
  | cons x xs ih =>
    intro acc
    have h := CTree.cost_bind_le (CTree.tick (g (acc, x)))
      (fun acc' => foldT CTree.tick g acc' xs) _ (CTree.AllRet.of_forall ih _)
    have h2 := hg (acc, x)
    simp only [CTree.cost_tick] at h
    simp only [foldT, List.length_cons, Nat.succ_mul]
    omega

theorem iterT_cost_le {c : Ty} (g : Val (.arr c c)) (B : ℕ) (hg : ∀ p, (g p).cost ≤ B)
    (n : ℕ) : ∀ acc : Val c, (iterT CTree.tick g acc n).cost ≤ n * (1 + B) := by
  induction n with
  | zero => intro acc; simp [iterT]
  | succ n ih =>
    intro acc
    have h := CTree.cost_bind_le (CTree.tick (g acc))
      (fun acc' => iterT CTree.tick g acc' n) _ (CTree.AllRet.of_forall ih _)
    have h2 := hg acc
    simp only [CTree.cost_tick] at h
    simp only [iterT, Nat.succ_mul]
    omega

namespace Tm

variable {Γ : List Ty}

/-- The cost of a term: the worst-case step count of its evaluation. -/
def cost {τ : Ty} (t : Tm Γ τ) (ρ : Env Γ) : ℕ := (t.eval ρ).cost

/-! ## Unfolding lemmas of the evaluator -/

theorem eval_app {a b : Ty} (f : Tm Γ (.arr a b)) (x : Tm Γ a) (ρ : Env Γ) :
    (app f x).eval ρ = (f.eval ρ).bind fun g => (x.eval ρ).bind fun v => .tick (g v) := rfl

theorem eval_lam {a b : Ty} (body : Tm (a :: Γ) b) (ρ : Env Γ) :
    (lam body).eval ρ = .ret fun v => body.eval (ρ.cons v) := rfl

theorem eval_letE {a b : Ty} (e : Tm Γ a) (body : Tm (a :: Γ) b) (ρ : Env Γ) :
    (letE e body).eval ρ = (e.eval ρ).bind fun v => .tick (body.eval (ρ.cons v)) := rfl

/-! ## Cost of the constructs -/

theorem cost_var {τ : Ty} (x : Var Γ τ) (ρ : Env Γ) : (var x).cost ρ = 0 := rfl

theorem cost_lam {a b : Ty} (body : Tm (a :: Γ) b) (ρ : Env Γ) : (lam body).cost ρ = 0 := rfl

/-- An application costs the function, the argument, one β-step and the body. -/
theorem cost_app_le {a b : Ty} (f : Tm Γ (.arr a b)) (x : Tm Γ a) (ρ : Env Γ) (B : ℕ)
    (hf : (f.eval ρ).AllRet fun g => ∀ v, (g v).cost ≤ B) :
    (app f x).cost ρ ≤ f.cost ρ + (x.cost ρ + (1 + B)) := by
  rw [cost, eval_app]
  refine CTree.cost_bind_le _ _ _ (hf.mono fun g hg => ?_)
  refine CTree.cost_bind_le _ _ _ (CTree.AllRet.of_forall (fun v => ?_) _)
  have := hg v
  simp only [CTree.cost_tick]
  omega

/-- A β-redex with a value argument costs one plus the body. -/
theorem cost_app_lam {a b : Ty} (body : Tm (a :: Γ) b) (x : Tm Γ a) (ρ : Env Γ) (v : Val a)
    (hx : x.eval ρ = .ret v) : (app (lam body) x).cost ρ = 1 + body.cost (ρ.cons v) := by
  simp only [cost, eval_app, hx]
  rfl

theorem eval_prim {a b : Ty} (p : Prim a b) (x : Tm Γ a) (ρ : Env Γ) :
    (prim p x).eval ρ =
      (x.eval ρ).bind fun v => stepN CTree.tick (p.cost v) (.ret (p.apply v)) := rfl

/-- A primitive operation at a value costs `Prim.cost` of the value. -/
theorem cost_prim {a b : Ty} (p : Prim a b) (x : Tm Γ a) (ρ : Env Γ) (v : Val a)
    (hx : x.eval ρ = .ret v) : (prim p x).cost ρ = p.cost v := by
  simp only [cost, eval_prim, hx, CTree.bind_ret, cost_stepN_tick, CTree.cost_ret,
    Nat.add_zero]

/-- A primitive operation costs its argument and a bound on `Prim.cost` at its values. -/
theorem cost_prim_le {a b : Ty} (p : Prim a b) (x : Tm Γ a) (ρ : Env Γ) (B : ℕ)
    (h : (x.eval ρ).AllRet fun v => p.cost v ≤ B) : (prim p x).cost ρ ≤ x.cost ρ + B := by
  rw [cost, eval_prim]
  refine CTree.cost_bind_le _ _ _ (h.mono fun v hv => ?_)
  simpa using hv

/-- A `letE` costs its bound term once, one β-step and the body. -/
theorem cost_letE_le {a b : Ty} (e : Tm Γ a) (body : Tm (a :: Γ) b) (ρ : Env Γ) (B : ℕ)
    (h : (e.eval ρ).AllRet fun v => (body.eval (ρ.cons v)).cost ≤ B) :
    (letE e body).cost ρ ≤ e.cost ρ + (1 + B) := by
  rw [cost, eval_letE]
  refine CTree.cost_bind_le _ _ _ (h.mono fun v hv => ?_)
  simp only [CTree.cost_tick]
  omega

/-- A `letE` of a value costs one plus the body. -/
theorem cost_letE_ret {a b : Ty} (e : Tm Γ a) (body : Tm (a :: Γ) b) (ρ : Env Γ) (v : Val a)
    (he : e.eval ρ = .ret v) : (letE e body).cost ρ = 1 + body.cost (ρ.cons v) := by
  simp only [cost, eval_letE, he]
  rfl

/-- A sample followed by a continuation costs one plus the maximum over the samples. -/
theorem cost_letE_sample {b : Ty} (f : FTy) (body : Tm (.base f :: Γ) b) (ρ : Env Γ) :
    (letE (sample f) body).cost ρ =
      1 + Finset.univ.sup fun x : f.den => 1 + body.cost (ρ.cons x) := rfl

/-- Unfolding lemma of `Tm.eval` at `fail`: the failure node. -/
theorem eval_fail {τ : Ty} (ρ : Env Γ) : (Tm.fail : Tm Γ τ).eval ρ = .fail := rfl

/-- Unfolding lemma of `Tm.cost` at `fail`: failure costs nothing. -/
theorem cost_fail {τ : Ty} (ρ : Env Γ) : (Tm.fail : Tm Γ τ).cost ρ = 0 := rfl

/-- Unfolding lemma of `Tm.denote` at `fail`: failure means `SPComp.fail`. -/
theorem denote_fail {τ : Ty} (O : CTree.Oracle) (ρ : Env Γ) :
    (Tm.fail : Tm Γ τ).denote O ρ = CatCrypt.Core.SPComp.fail := rfl

/-- A multiplication of residues at a value costs `size (n + 1) * size (n + 1) + 1`, in the
bit length of the modulus. -/
theorem cost_finMul {n : ℕ} (x : Tm Γ (.prod (.fin n) (.fin n))) (ρ : Env Γ)
    (v : Val (.prod (.fin n) (.fin n))) (hx : x.eval ρ = .ret v) :
    (prim (.finMul n) x).cost ρ = (n + 1).size * (n + 1).size + 1 :=
  cost_prim _ x ρ v hx

/-- A `seq` costs both terms and one step. -/
theorem cost_seq_le {a b : Ty} (e : Tm Γ a) (body : Tm Γ b) (ρ : Env Γ) :
    (seq e body).cost ρ ≤ e.cost ρ + (1 + body.cost ρ) :=
  CTree.cost_bind_le _ _ _ (CTree.AllRet.of_forall (fun _ => le_refl _) _)

/-! ## Precomposition -/

/-- Building a composite costs the two function terms and two β-steps. -/
theorem cost_compose_le {a b c : Ty} (g : Tm Γ (.arr b c)) (f : Tm Γ (.arr a b))
    (ρ : Env Γ) : (compose g f).cost ρ ≤ g.cost ρ + (f.cost ρ + 2) := by
  have h1 : (app (composeT (a := a)) g).cost ρ ≤
      (composeT (a := a)).cost ρ + (g.cost ρ + (1 + 0)) :=
    cost_app_le (composeT (a := a)) g ρ 0 fun _ => Nat.le_refl 0
  have h0 : (composeT (a := a) (b := b) (c := c)).cost ρ = 0 := rfl
  have h2 : ((app (composeT (a := a)) g).eval ρ).AllRet fun c => ∀ fv, (c fv).cost ≤ 0 :=
    CTree.allRet_bind ((composeT (a := a)).eval ρ) _
      (CTree.allRet_bind (g.eval ρ) _ (CTree.AllRet.of_forall (fun _ _ => Nat.le_refl 0) _))
  have h3 := CTree.cost_bind_le ((app (composeT (a := a)) g).eval ρ)
    (fun c => (f.eval ρ).bind fun fv => .tick (c fv)) (f.cost ρ + 1)
    (h2.mono fun c hc => CTree.cost_bind_le _ _ _ (CTree.AllRet.of_forall (fun fv => by
      have := hc fv
      simp only [CTree.cost_tick]
      omega) _))
  have h4 : (compose g f).cost ρ =
      (((app (composeT (a := a)) g).eval ρ).bind fun c =>
        (f.eval ρ).bind fun fv => .tick (c fv)).cost :=
    rfl
  have h5 : (app (composeT (a := a)) g).cost ρ = ((app (composeT (a := a)) g).eval ρ).cost :=
    rfl
  omega

/-- An application of a composite costs the two applications and two β-steps. -/
theorem allRet_compose {a b c : Ty} (g : Tm Γ (.arr b c)) (f : Tm Γ (.arr a b))
    (ρ : Env Γ) (Bg Bf : ℕ) (hg : (g.eval ρ).AllRet fun gv => ∀ v, (gv v).cost ≤ Bg)
    (hf : (f.eval ρ).AllRet fun fv => ∀ v, (fv v).cost ≤ Bf) :
    ((compose g f).eval ρ).AllRet fun h => ∀ v, (h v).cost ≤ Bf + Bg + 2 := by
  refine CTree.allRet_bind ((app composeT g).eval ρ) _ ?_
  refine CTree.allRet_bind (g.eval ρ) _ (hg.mono fun gv hgv => ?_)
  refine CTree.allRet_bind (f.eval ρ) _ (hf.mono fun fv hfv => ?_)
  intro v
  have h := CTree.cost_bind_le (CTree.tick (fv v)) (fun w => CTree.tick (gv w)) (1 + Bg)
    (CTree.AllRet.of_forall (fun w => by
      have := hgv w
      simp only [CTree.cost_tick]
      omega) _)
  have := hfv v
  simp only [CTree.cost_tick] at h
  exact h.trans (by omega)

/-- Precomposition: applying `compose g f` costs the costs of `g`, `f` and the argument, the
costs of the two applications, and five steps. -/
theorem cost_app_compose_le {a b c : Ty} (g : Tm Γ (.arr b c)) (f : Tm Γ (.arr a b))
    (x : Tm Γ a) (ρ : Env Γ) (Bg Bf : ℕ)
    (hg : (g.eval ρ).AllRet fun gv => ∀ v, (gv v).cost ≤ Bg)
    (hf : (f.eval ρ).AllRet fun fv => ∀ v, (fv v).cost ≤ Bf) :
    (app (compose g f) x).cost ρ ≤ g.cost ρ + f.cost ρ + x.cost ρ + (Bf + Bg + 5) := by
  have h1 := cost_app_le (compose g f) x ρ _ (allRet_compose g f ρ Bg Bf hg hf)
  have h2 := cost_compose_le g f ρ
  omega

end Tm

end CatCrypt.Complexity.D
