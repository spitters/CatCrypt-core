/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Complexity.D.Link
public import CatCryptCore.Complexity.D.Reflect
public import CatCryptCore.Complexity.D.Asymptotic
import all CatCryptCore.Core.SPTreeTimed

/-!
# Linking certificates of `derive_reduction` to D

The comparison lemmas between the costed trees of `derive_timed` and the evaluation trees of
reflected D-terms, one per construct of the terms that `reflect_d` produces for a reduction.
Each lemma concludes `TimedSim R K n x (t.eval ρ)` for a construct `t` from the relations of its
parts; the pure parts of a term are given by their exact cost derivations `CEq` of `reflect_d`.
The side conditions are linear inequalities between the step costs of the costed tree and the
step counts of the D evaluation.

* `TimedSim.shift`, `TimedSim.tick`: steps of the D tree in front of a related tree, paid by the
  step cost in front of the costed tree and the allowance.
* `TimedSim.eval_letE_sample`: a `letE` over a sample against a costed sample node.
* `TimedSim.eval_letE_ceq`: a `letE` over a pure part of exact cost.
* `TimedSim.eval_letE_bind`: a `letE` over a computation against a costed bind.
* `TimedSim.eval_app_ceq`: the application of a function value (an adversary or a primitive) to
  a pure argument, the function value related to the costed subtree.
* `TimedSim.eval_ite_ceq`: a conditional on a pure test.
* `TimedSim.monoK`, `TimedSim.costTree`: monotonicity in the factor and the costed tree of an
  adversary call.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Complexity.D

open CatCrypt.Core CatCrypt.Complexity.D.Reflect

namespace TimedSimTree

variable {α β : Type} {R : α → β → Prop}

/-- The relation is monotone in the factor. -/
theorem monoK {K K' n : ℕ} {A : SPTree.Timed α} {t : CTree β} (h : TimedSimTree R K n A t)
    (hK : K ≤ K') : TimedSimTree R K' n A t := by
  induction h with
  | ret hR => exact .ret hR
  | tick _ hm ih => exact .tick ih hm
  | @sample n γ finγ neγ c k f e k' m _ hm ih =>
    refine .sample f e m ih fun b => (hm b).trans ?_
    have := Nat.mul_le_mul_right (c b) hK
    omega
  | @get n i f c k k' m _ hm ih =>
    refine .get i f m ih fun x => (hm x).trans ?_
    have := Nat.mul_le_mul_right (c x) hK
    omega
  | @set n i f v c A t m _ hm ih =>
    refine .set i f v m ih (hm.trans ?_)
    have := Nat.mul_le_mul_right c hK
    omega
  | fail => exact .fail
  | @query n d r x c k k' m _ hm ih =>
    refine .query d r x m ih fun y => (hm y).trans ?_
    have := Nat.mul_le_mul_right (c y) hK
    omega

/-- `j` steps in front of the D tree, paid by the allowance. -/
theorem stepN_tick {K m n : ℕ} {A : SPTree.Timed α} {t : CTree β}
    (h : TimedSimTree R K m A t) (j : ℕ) (hj : m + j ≤ n) :
    TimedSimTree R K n A (stepN CTree.tick j t) := by
  induction j generalizing n with
  | zero => exact h.mono (by omega)
  | succ j ih => exact .tick (ih (n := n - 1) (by omega)) (by omega)

end TimedSimTree

namespace TimedSim

variable {α β γ δ : Type} {R : α → β → Prop} {K n : ℕ}

/-- The relation is monotone in the factor. -/
theorem monoK {K' : ℕ} {x : ℕ × SPTree.Timed α} {t : CTree β} (h : TimedSim R K n x t)
    (hK : K ≤ K') : TimedSim R K' n x t :=
  (TimedSimTree.monoK h hK).mono (by have := Nat.mul_le_mul_right x.1 hK; omega)

/-- `j` steps in front of the D tree, paid by the step cost in front of the costed tree and the
allowance. -/
theorem shift {m c c' : ℕ} {A : SPTree.Timed α} {t : CTree β} (h : TimedSim R K m (c', A) t)
    (j : ℕ) (hle : m + K * c' + j ≤ n + K * c) :
    TimedSim R K n (c, A) (stepN CTree.tick j t) :=
  TimedSimTree.stepN_tick h j hle

/-- One step in front of the D tree. -/
theorem tick {m c c' : ℕ} {A : SPTree.Timed α} {t : CTree β} (h : TimedSim R K m (c', A) t)
    (hle : m + K * c' + 1 ≤ n + K * c) : TimedSim R K n (c, A) (.tick t) :=
  shift h 1 hle

/-- The D tree of an adversary call is simulated by its costed tree at any factor `K ≥ 1`. -/
theorem costTree (hK : 1 ≤ K) (t : CTree β) : TimedSim (· = ·) K 0 t.costTree t :=
  (CTree.timedSim_costTree t).monoK hK

variable {Γ : List Ty} {ρ : Env Γ}

/-- A `letE` over a sample against a costed sample node, the values matched through `e`. -/
theorem eval_letE_sample (hK : 1 ≤ K) {b : Ty} {f : FTy} {body : Tm (.base f :: Γ) b}
    {γ' : Type} {finγ : Fintype γ'} {neγ : Nonempty γ'} {c : γ' → ℕ}
    {k : γ' → SPTree.Timed α} {R : α → Val b → Prop} (e : γ' ≃ f.den)
    (h : ∀ x, TimedSim R K n (c x, k x) (.tick (body.eval (ρ.cons (e x))))) :
    TimedSim R K n (0, .sample γ' finγ neγ c k) ((Tm.letE (.sample f) body).eval ρ) :=
  TimedSim.sample hK f e h

/-- A `letE` over a pure part of exact cost `ce`: the steps of the part and the β-step are paid
by the step cost in front of the costed tree. -/
theorem eval_letE_ceq {a b : Ty} {e : Tm Γ a} {body : Tm (a :: Γ) b} {ce : ℕ} {u : Val a}
    {R : α → Val b → Prop} {m c c' : ℕ} {A : SPTree.Timed α} (he : CEq e ρ ce u)
    (h : TimedSim R K m (c', A) (body.eval (ρ.cons u))) (hle : m + K * c' + (ce + 1) ≤ n + K * c) :
    TimedSim R K n (c, A) ((Tm.letE e body).eval ρ) := by
  rw [Tm.eval_letE, he, stepN_ret_bind, stepN_tick_succ]
  exact shift h (ce + 1) hle

/-- A `letE` over a computation against a costed bind: the bound part related to the step-
prefixed tree `(c₀, A)`, the continuation to the ticked evaluation of the body. The step cost
`c₀` moves into the allowance, since the costed bind of a certificate has no step cost in front
of its tree. -/
theorem eval_letE_bind {a b : Ty} {e : Tm Γ a} {body : Tm (a :: Γ) b} {R : α → Val a → Prop}
    {S : γ → Val b → Prop} {f : α → ℕ × SPTree.Timed γ} {m c₀ : ℕ} {A : SPTree.Timed α}
    (he : TimedSim R K n (c₀, A) (e.eval ρ))
    (hf : ∀ x v, R x v → TimedSim S K m (f x) (.tick (body.eval (ρ.cons v)))) :
    TimedSim S K (n + m + K * c₀) (A.bind f) ((Tm.letE e body).eval ρ) := by
  rw [Tm.eval_letE]
  have := TimedSim.bind he hf
  refine TimedSimTree.mono this ?_
  simp only [SPTree.Timed.delay, Nat.mul_add]
  omega

/-- The application of a function value to a pure argument: the steps of the function term,
of the argument and the β-step are paid by the step cost in front of the costed tree. -/
theorem eval_app_ceq {a b : Ty} {f : Tm Γ (.arr a b)} {x : Tm Γ a} {cf cx : ℕ}
    {F : Val (.arr a b)} {v : Val a} {R : α → Val b → Prop} {m c c' : ℕ} {A : SPTree.Timed α}
    (hf : CEq f ρ cf F) (hx : CEq x ρ cx v) (h : TimedSim R K m (c', A) (F v))
    (hle : m + K * c' + (cf + cx + 1) ≤ n + K * c) :
    TimedSim R K n (c, A) ((Tm.app f x).eval ρ) := by
  rw [Tm.eval_app, hf, stepN_ret_bind, hx, stepN_ret_bind]
  change TimedSim R K n (c, A) (stepN CTree.tick cf (stepN CTree.tick cx (CTree.tick (F v))))
  rw [stepN_tick_succ, stepN_tick_add]
  exact shift h (cf + (cx + 1)) (by omega)

/-- A conditional on a pure test of exact cost `cb` against a conditional of costed trees. -/
theorem eval_ite_ceq {τ : Ty} {bt : Tm Γ .bool} {t u : Tm Γ τ} {cb m : ℕ} {P : Prop}
    [Decidable P] {R : α → Val τ → Prop} {x y : ℕ × SPTree.Timed α}
    (hb : CEq bt ρ cb (decide P)) (hx : TimedSim R K m x (t.eval ρ))
    (hy : TimedSim R K m y (u.eval ρ)) (hle : m + (cb + 1) ≤ n) :
    TimedSim R K n (if P then x else y) ((Tm.ite bt t u).eval ρ) := by
  have key : (Tm.ite bt t u).eval ρ =
      stepN CTree.tick (cb + 1) (bif decide P then t.eval ρ else u.eval ρ) := by
    show ((bt.eval ρ).bind (fun (v : Bool) => CTree.tick (bif v then t.eval ρ else u.eval ρ))) = _
    rw [hb]
    exact (stepN_ret_bind cb (decide P) _).trans (stepN_tick_succ _ _)
  rw [key]
  by_cases hP : P
  · have hc : (bif decide P then t.eval ρ else u.eval ρ) = t.eval ρ := by simp [hP]
    rw [hc, ite_eq_left hP]
    exact TimedSimTree.stepN_tick hx (cb + 1) (by omega)
  · have hc : (bif decide P then t.eval ρ else u.eval ρ) = u.eval ρ := by simp [hP]
    rw [hc, ite_eq_right hP]
    exact TimedSimTree.stepN_tick hy (cb + 1) (by omega)

end TimedSim

/-! ## Closing the primitives of a reflected term -/

/-- The renaming that moves the outermost variable of `Γ ++ [σ]` to the innermost position. -/
def Ren.rot : (Γ : List Ty) → (σ : Ty) → Ren (Γ ++ [σ]) (σ :: Γ)
  | [], _ => fun _ x => x
  | _ :: Γ, σ => fun _ x => match x with
    | .here => .there .here
    | .there y => match Ren.rot Γ σ _ y with
      | .here => .here
      | .there w => .there (.there w)

theorem Env.comp_rot_nil {σ : Ty} (v : Val σ) :
    (Env.nil.cons v).comp (Ren.rot [] σ) = Env.nil.cons v := by
  funext τ x
  cases x with
  | here => rfl
  | there y => nomatch y

theorem Env.comp_rot_cons {Γ : List Ty} {α σ : Ty} (ρ : Env Γ) (a : Val α) (v : Val σ) :
    ((ρ.cons a).cons v).comp (Ren.rot (α :: Γ) σ) = ((ρ.cons v).comp (Ren.rot Γ σ)).cons a := by
  funext τ x
  cases x with
  | here => rfl
  | there y =>
    show ((ρ.cons a).cons v) τ (match Ren.rot Γ σ τ y with
      | .here => .here
      | .there w => .there (.there w)) = (ρ.cons v) τ (Ren.rot Γ σ τ y)
    generalize Ren.rot Γ σ τ y = z
    cases z <;> rfl

/-- The term `t` with its outermost variable bound to the closed term `p`. -/
def Tm.closeOuter {Γ : List Ty} {σ τ : Ty} (p : Tm [] σ) (t : Tm (Γ ++ [σ]) τ) : Tm Γ τ :=
  .letE p.weaken (t.rename (Ren.rot Γ σ))

/-- The evaluation of `t` with its outermost variable bound to `p`: the steps of `p` and the
β-step, then the evaluation of `t` with the value of `p` outermost. -/
theorem Tm.eval_closeOuter {Γ : List Ty} {σ τ : Ty} (p : Tm [] σ) (t : Tm (Γ ++ [σ]) τ)
    (ρ : Env Γ) {e : ℕ} {v : Val σ} (hp : p.EvalsTo e v) :
    (Tm.closeOuter p t).eval ρ =
      stepN CTree.tick (e + 1) (t.eval ((ρ.cons v).comp (Ren.rot Γ σ))) := by
  rw [Tm.closeOuter, Tm.eval_letE, Tm.eval_weaken, hp, stepN_ret_bind, ← stepN_tick_succ]
  congr 2
  exact Tm.interp_rename CTree.tick t _ _

theorem Tm.cost_closeOuter {Γ : List Ty} {σ τ : Ty} (p : Tm [] σ) (t : Tm (Γ ++ [σ]) τ)
    (ρ : Env Γ) {e : ℕ} {v : Val σ} (hp : p.EvalsTo e v) :
    (Tm.closeOuter p t).cost ρ = e + 1 + t.cost ((ρ.cons v).comp (Ren.rot Γ σ)) := by
  rw [Tm.cost, Tm.eval_closeOuter p t ρ hp, cost_stepN_tick]
  rfl

theorem Tm.run_eval_closeOuter {Γ : List Ty} {σ τ : Ty} (O : CTree.Oracle) (p : Tm [] σ)
    (t : Tm (Γ ++ [σ]) τ) (ρ : Env Γ) {e : ℕ} {v : Val σ} (hp : p.EvalsTo e v) :
    ((Tm.closeOuter p t).eval ρ).run O = (t.eval ((ρ.cons v).comp (Ren.rot Γ σ))).run O := by
  rw [Tm.eval_closeOuter p t ρ hp, run_stepN_tick]

/-! ## Evaluation and denotation with function values in the environment -/

/-- A type that is first-order or a function type between first-order types. -/
def Ty.FOArr : Ty → Prop
  | .arr a b => a.FO ∧ b.FO
  | τ => τ.FO

/-- A value with the ticks of its function body erased. -/
def Val.eraseArr : (τ : Ty) → Val τ → Val τ
  | .arr _ _, f => fun v => (f v).erase
  | _, v => v

/-- An environment with the ticks of its function values erased. -/
def Env.eraseArr {Γ : List Ty} (ρ : Env Γ) : Env Γ := fun τ x => Val.eraseArr τ (ρ τ x)

theorem Env.eraseArr_nil : (Env.nil : Env []).eraseArr = Env.nil := by
  funext τ x
  nomatch x

theorem Env.eraseArr_cons {Γ : List Ty} {τ : Ty} (ρ : Env Γ) (v : Val τ) :
    (ρ.cons v).eraseArr = ρ.eraseArr.cons (Val.eraseArr τ v) := by
  funext σ x
  cases x <;> rfl

/-- Unfolding lemma of `Val.eraseArr` at a function type. -/
theorem Val.eraseArr_arr {a b : Ty} (f : Val (.arr a b)) :
    Val.eraseArr (.arr a b) f = fun v => (f v).erase := rfl

/-- Unfolding lemma of `Val.eraseArr` at a base type. -/
theorem Val.eraseArr_base (f : FTy) (v : Val (.base f)) : Val.eraseArr (.base f) v = v := rfl

/-- A tree is related by equality to its erasure. -/
theorem CTree.rel_erase {α : Type} (t : CTree α) : CTree.Rel (· = ·) t t.erase := by
  induction t with
  | ret a => exact .ret rfl
  | tick t ih => exact .tick ih
  | sample f k ih => exact .sample f ih
  | get n f k ih => exact .get n f ih
  | set n f v k ih => exact .set n f v ih
  | query d r x k ih => exact .query d r x ih
  | fail => exact .fail

theorem CTree.erase_stepN_tick {α : Type} (n : ℕ) (t : CTree α) :
    (stepN CTree.tick n t).erase = t.erase := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

theorem valRel_eraseArr : (τ : Ty) → τ.FOArr → (v : Val τ) → ValRel τ v (Val.eraseArr τ v)
  | .arr a b, h, f => fun x y hxy => by
    rw [ValRel.iff_eq_of_FO a h.1] at hxy
    subst hxy
    exact (CTree.rel_erase (f x)).mono fun u w huw => (ValRel.iff_eq_of_FO b h.2 u w).2 huw
  | .base _, _, _ => rfl
  | .nat, _, _ => rfl
  | .prod a b, h, v => (ValRel.iff_eq_of_FO (.prod a b) h v v).2 rfl
  | .sum a b, h, v => (ValRel.iff_eq_of_FO (.sum a b) h v v).2 rfl
  | .list a, h, v => (ValRel.iff_eq_of_FO (.list a) h v v).2 rfl

/-- The meaning of the evaluation of a term at a first-order type, in an environment of
first-order values and function values between first-order types, is its denotation with the
function values erased. -/
theorem Tm.run_eval_eraseArr {Γ : List Ty} {τ : Ty} (O : CTree.Oracle) (t : Tm Γ τ)
    (hτ : τ.FO) (hΓ : ∀ σ ∈ Γ, σ.FOArr) (ρ : Env Γ) :
    (t.eval ρ).run O = t.denote O ρ.eraseArr := by
  have hρ : EnvRel ρ ρ.eraseArr := fun σ x => valRel_eraseArr σ (hΓ σ x.mem) _
  rw [← CTree.run_erase, ((t.interp_rel hρ).mono fun u v huv =>
    (ValRel.iff_eq_of_FO τ hτ u v).1 huv).erase_eq]
  rfl

end CatCrypt.Complexity.D
