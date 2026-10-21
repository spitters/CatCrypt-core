/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Complexity.D.Cost
public import CatCryptCore.Crypto.UCAdmClass.SPCompInstance

/-!
# Time admissibility over the deep language D

A Kleisli arrow `f : Val a → SPComp (Val b)` between the values of first-order D types is
admissible at time `n` (`TimeAdm O n f`) when a closed D-term `t : Tm [] (.arr a b)`
realizes it: `t` evaluates without effects, in `c` steps, to a closure `g`; every call
`g x` costs at most `k` steps; `c + 1 + k ≤ n`; and `g x` means `f x` in `SPComp`, the oracle
answered by `O` (`TimeRealizer`). The bound `c + 1 + k` is the cost of the application
`t x`: evaluating `t`, one β-step and the call (`TimeRealizer.apply_cost_le`).

The realizer is a closed term, not a value of the function type. A function value of D is a
Lean function `Val a → CTree (Val b)`, so quantifying over values would admit closures that
were not produced by evaluating a `lam` and whose trees carry no ticks. Every closure of a
closed term comes from the evaluation of a `lam` and carries the ticks of its body. The
argument and result types are first-order (`Ty.FO`): at a function type an input would itself
be an uncosted Lean function.

## The bound is a constant

The bound `n` is one number for all inputs, not a function of the input size. This is the
convention of concrete security, where the time of an adversary or distinguisher is a number
at fixed parameters, and it is the grading under which the laws below compose: a bound in the
input size would require, for a bind, a bound on the size of the outputs of the first arrow,
which the cost semantics of D does not track. A consequence is that at an unbounded type such
as `ℕ` or a list, an admissible arrow reads only a bounded part of a large input.

## The graded laws

The laws of `UCAdmClass` (`CatCryptCore/Crypto/UCAdmClass.lean`) hold in graded form:

* `timeAdm_pure`: `pure` is admissible at time `1` (the realizer `λx. x`).
* `timeAdm_bind`: Kleisli composition adds the times, plus `3` (`Tm.compose`: two β-steps to
  build the composite and one β-step for the inner call).
* `timeAdm_mapSum`: the coproduct is admissible at the maximum of the times plus `2`. Its
  realizer `Tm.sumMap` is `λx. case x (inl (f x)) (inr (g x))` with the closed function terms
  weakened under the binder (`Tm.weaken`), so a call evaluates only the function term of its
  branch: one step for the case analysis, one β-step, and the application of that term.
* `timeAdm_precomp`: precomposition by a function `φ` that a closed D-term computes at time
  `p` (that is, `pure ∘ φ` admissible at time `p`) gives time `p + n + 3`.

The ungraded law `adm_precomp`, precomposition with every Lean function at no cost, fails.
Let `φ : ℕ → Bool` map `x` to the parity of its bit length `Nat.size x`. An application within
`n` steps applies a primitive operation on `ℕ` only at arguments of bit length below `n`
(`Prim.cost`), iterates `iter` fewer than `n` times, and reads a natural number of larger bit
length only through `wofNat w`, at the finitely many widths `w` that occur in the term. Its
results at `2 ^ m` and at `2 ^ (m + 1)` are therefore the same for `m` large, while their bit
lengths `m + 1` and `m + 2` have different parities. So `pure ∘ φ` is
admissible at no constant time, although `pure` is admissible at time `1`. Precomposition is
charged by the cost of the term that computes the function; `UCAdmClass` is therefore not
instantiated, and the laws are theorems about the graded family `TimeAdm O n`.

## The time-bounded computational distance

`ucCdistTime O t f g` is the supremum of the per-distinguisher distance `spcomp_distComp` over
the distinguishers admissible at time `t`, `ucCdist` restricted to a time class. It is a
pseudometric (`ucCdistTime_self`, `ucCdistTime_sym`, `ucCdistTime_triangle`), bounded by the statistical
distance (`ucCdistTime_le_sdist`) and monotone in `t` (`ucCdistTime_mono`). Pre-composition
does not increase it (`ucCdistTime_comp_left`). Post-composition with an arrow admissible at
time `s` moves the time from `t` to `s + t + 3` (`ucCdistTime_comp_right`), and the coproduct
moves it to `t + 4` (`ucCdistTime_mapSum_le`).

## The range test

Let `G : S → Y` be a generator realized by a closed D-term at time `T_G`, with `S` a finite
ground type. The range test `D y = decide (∃ s, G s = y)` separates `G` applied to a uniform
seed from a uniform `Y` when `|S| < |Y|`. A D-term computing `D` with no other access to `G`
than evaluating it finds a preimage by enumerating seeds: `iter` over the `|S|` seeds, one
evaluation of `G` and one word comparison each, at time about `|S| · T_G`. Below this time a
term decides the range only if it computes some other function with the same values, for
instance an inverse of `G` cheaper than the enumeration. So for `G` a pseudorandom generator,
the range test is not admissible below time about `|S| · T_G`, and `ucCdistTime` at such a
time can be small on the pair (`G` on a uniform seed, uniform `Y`) while the statistical
distance is at least `1 - |S| / |Y|`. The query, size and shape classes on `SPComp` do not
make this separation: the range test is a pure test `pure ∘ p`, which makes no query and is
admissible in each of them, so their computational distance equals the statistical distance
on this pair (`Complexity.md`, item 3). This is an argument, not a formal lower bound: the
time class separates the two distances on the pair only when no cheap term computes the
range test.

## Main definitions

* `Tm.EvalsTo`: a closed term evaluates without effects in `c` steps to a value.
* `TimeRealizer`: a closed D-term realizing an arrow at time `n`.
* `Tm.applyEval`: the application of a closed function term to an input.
* `TimeAdm`: time-`n` admissibility of a Kleisli arrow on `SPComp`.
* `Ren`, `Tm.rename`, `Tm.weaken`: renaming of variables, and a closed term in any context.
* `Tm.sumMap`: the coproduct of two closed function terms.
* `ucCdistTime`: the time-bounded computational distance.

## Main results

* `TimeRealizer.apply_cost_le`, `TimeRealizer.apply_run`, `TimeRealizer.run_den`: the
  application costs at most `n` and means `f`, through the evaluator and through the
  denotation `Tm.den`.
* `Tm.interp_rename`, `Tm.eval_weaken`: the interpreter commutes with renaming; a weakened
  closed term evaluates as the closed term.
* The graded laws and the properties of `ucCdistTime` listed above.

## References

* Y. Forster, F. Kunze. *A certifying extraction with time bounds from Coq to call-by-value
  λ-calculus*. ITP 2019.
* Y. Forster, F. Kunze, M. Roth. *The weak call-by-value λ-calculus is reasonable for both
  time and space*. POPL 2020.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Complexity.D

open CatCrypt.Core CatCrypt.Crypto UCMonad

open scoped ENNReal

/-! ## Steps in front of a tree -/

theorem stepN_add {α : Type} (tk : ∀ {β : Type}, CTree β → CTree β) (m k : ℕ)
    (t : CTree α) : stepN tk (m + k) t = stepN tk m (stepN tk k t) := by
  induction m with
  | zero => rw [Nat.zero_add]; rfl
  | succ m ih => rw [Nat.add_right_comm]; exact congrArg (fun s => tk s) ih

theorem run_stepN_tick {α : Type} (O : CTree.Oracle) (n : ℕ) (t : CTree α) :
    (stepN CTree.tick n t).run O = t.run O := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

/-- A tree related to ticks in front of a leaf is a related leaf. -/
theorem rel_stepN_ret_inv {α β : Type} {R : α → β → Prop} {c : ℕ} {v : α} {m : CTree β}
    (h : CTree.Rel R (stepN CTree.tick c (.ret v)) m) : ∃ w, m = .ret w ∧ R v w := by
  induction c with
  | zero => cases h with | ret h => exact ⟨_, rfl, h⟩
  | succ c ih => cases h with | tick h => exact ih h

/-! ## Realizers -/

/-- The closed term `t` evaluates without effects, in `c` steps, to the value `v`. -/
def Tm.EvalsTo {τ : Ty} (t : Tm [] τ) (c : ℕ) (v : Val τ) : Prop :=
  t.eval Env.nil = stepN CTree.tick c (.ret v)

/-- An application of a closed function term to an input: evaluating the term, one β-step
and the call. -/
def Tm.applyEval {a b : Ty} (t : Tm [] (.arr a b)) (x : Val a) : CTree (Val b) :=
  (t.eval Env.nil).bind fun h => .tick (h x)

/-- A realizer of the arrow `f` at time `n`: a closed D-term evaluating in `evalCost` steps
to a closure whose calls cost at most `callCost` steps and mean `f` in `SPComp`, with
`evalCost + 1 + callCost ≤ n`. -/
structure TimeRealizer (O : CTree.Oracle) {a b : Ty} (n : ℕ)
    (f : Val a → SPComp (Val b)) : Type where
  /-- The closed term. -/
  term : Tm [] (.arr a b)
  /-- The steps of evaluating the term to a closure. -/
  evalCost : ℕ
  /-- A bound on the steps of a call of the closure. -/
  callCost : ℕ
  /-- The closure. -/
  closure : Val (.arr a b)
  evals : term.EvalsTo evalCost closure
  call_le : ∀ v, (closure v).cost ≤ callCost
  time_le : evalCost + 1 + callCost ≤ n
  run_eq : ∀ x, (closure x).run O = f x

/-- Time-`n` admissibility of a Kleisli arrow between the values of first-order D types: a
closed D-term realizes it at time `n`. -/
def TimeAdm (O : CTree.Oracle) {a b : Ty} (n : ℕ) (f : Val a → SPComp (Val b)) : Prop :=
  a.FO ∧ b.FO ∧ Nonempty (TimeRealizer O n f)

namespace TimeRealizer

variable {O : CTree.Oracle} {a b : Ty} {n : ℕ} {f : Val a → SPComp (Val b)}

/-- The application of the realizer to an input costs at most `n` steps. -/
theorem apply_cost_le (r : TimeRealizer O n f) (x : Val a) :
    (r.term.applyEval x).cost ≤ n := by
  rw [Tm.applyEval, show r.term.eval Env.nil = _ from r.evals, stepN_tick_bind, cost_stepN_tick,
    CTree.bind_ret, CTree.cost_tick]
  have := r.call_le x
  have := r.time_le
  omega

/-- The application of the realizer to an input means `f` at that input. -/
theorem apply_run (r : TimeRealizer O n f) (x : Val a) :
    (r.term.applyEval x).run O = f x := by
  rw [Tm.applyEval, show r.term.eval Env.nil = _ from r.evals, stepN_tick_bind, run_stepN_tick,
    CTree.bind_ret]
  exact r.run_eq x

/-- The denotation of the realizer's term, applied to an input, means `f` at that input: the
realizer is a term whose denotation is `f`. -/
theorem run_den (r : TimeRealizer O n f) (ha : a.FO) (hb : b.FO) (x : Val a) :
    ((r.term.den Env.nil).bind fun g => g x).run O = f x := by
  have hrel := r.term.interp_rel (ρ := Env.nil) (δ := Env.nil) (fun _ y => nomatch y)
  rw [show r.term.eval Env.nil = _ from r.evals] at hrel
  obtain ⟨g', hg', hgg⟩ := rel_stepN_ret_inv hrel
  rw [hg', CTree.bind_ret]
  have hx : ValRel a x x := (ValRel.iff_eq_of_FO a ha x x).2 rfl
  have he := ((hgg x x hx).mono fun u v huv => (ValRel.iff_eq_of_FO b hb u v).1 huv).erase_eq
  rw [← he, CTree.run_erase]
  exact r.run_eq x

/-- A realizer at time `n` is one at every larger time. -/
def relax (r : TimeRealizer O n f) {m : ℕ} (h : n ≤ m) : TimeRealizer O m f :=
  { r with time_le := le_trans r.time_le h }

end TimeRealizer

theorem TimeAdm.mono {O : CTree.Oracle} {a b : Ty} {n m : ℕ} {f : Val a → SPComp (Val b)}
    (h : TimeAdm O n f) (hnm : n ≤ m) : TimeAdm O m f :=
  ⟨h.1, h.2.1, h.2.2.elim fun r => ⟨r.relax hnm⟩⟩

/-! ## The identity -/

/-- The realizer `λx. x` of `pure`. -/
def TimeRealizer.pure (O : CTree.Oracle) (a : Ty) :
    TimeRealizer O 1 (fun x : Val a => SPComp.pure x) where
  term := .lam (.var .here)
  evalCost := 0
  callCost := 0
  closure := fun v => .ret v
  evals := rfl
  call_le := fun _ => le_refl _
  time_le := le_refl _
  run_eq := fun _ => rfl

theorem timeAdm_pure (O : CTree.Oracle) {a : Ty} (ha : a.FO) :
    TimeAdm O 1 (fun x : Val a => SPComp.pure x) :=
  ⟨ha, ha, ⟨TimeRealizer.pure O a⟩⟩

/-! ## Kleisli composition -/

section Compose

variable {a b c : Ty}

/-- The closure of `Tm.compose`, given the closures of its two function terms. -/
def composeClosure (gv : Val (.arr b c)) (fv : Val (.arr a b)) : Val (.arr a c) :=
  fun x => (CTree.tick (fv x)).bind fun v => .tick (gv v)

theorem evalsTo_compose {tg : Tm [] (.arr b c)} {tf : Tm [] (.arr a b)} {cg cf : ℕ}
    {gv : Val (.arr b c)} {fv : Val (.arr a b)} (hg : tg.EvalsTo cg gv)
    (hf : tf.EvalsTo cf fv) : (Tm.compose tg tf).EvalsTo (cg + cf + 2) (composeClosure gv fv) := by
  unfold Tm.EvalsTo at *
  rw [Tm.compose, Tm.eval_app, Tm.eval_app, hg, hf]
  simp only [stepN_tick_bind]
  change (stepN CTree.tick cg (CTree.tick _)).bind _ = _
  rw [stepN_tick_bind, show cg + cf + 2 = cg + (1 + (cf + 1)) by omega, stepN_add, stepN_add,
    stepN_add]
  rfl

theorem composeClosure_cost_le {gv : Val (.arr b c)} {fv : Val (.arr a b)} {kg kf : ℕ}
    (hg : ∀ v, (gv v).cost ≤ kg) (hf : ∀ v, (fv v).cost ≤ kf) (x : Val a) :
    (composeClosure gv fv x).cost ≤ kf + kg + 2 := by
  have h := CTree.cost_bind_le (CTree.tick (fv x)) (fun v => CTree.tick (gv v)) (1 + kg)
    (CTree.AllRet.of_forall (fun v => by rw [CTree.cost_tick]; have := hg v; omega) _)
  rw [CTree.cost_tick] at h
  have := hf x
  show ((CTree.tick (fv x)).bind fun v => CTree.tick (gv v)).cost ≤ _
  omega

theorem composeClosure_run (O : CTree.Oracle) (gv : Val (.arr b c)) (fv : Val (.arr a b))
    (x : Val a) : (composeClosure gv fv x).run O =
      SPComp.bind ((fv x).run O) fun v => (gv v).run O := by
  unfold composeClosure
  rw [CTree.run_bind]
  rfl

/-- The realizer `Tm.compose tg tf` of the Kleisli composite. -/
def TimeRealizer.bind {O : CTree.Oracle} {n m : ℕ} {f : Val a → SPComp (Val b)}
    {g : Val b → SPComp (Val c)} (rf : TimeRealizer O n f) (rg : TimeRealizer O m g) :
    TimeRealizer O (n + m + 3) (fun x => f x >>= g) where
  term := Tm.compose rg.term rf.term
  evalCost := rg.evalCost + rf.evalCost + 2
  callCost := rf.callCost + rg.callCost + 2
  closure := composeClosure rg.closure rf.closure
  evals := evalsTo_compose rg.evals rf.evals
  call_le := composeClosure_cost_le rg.call_le rf.call_le
  time_le := by
    have := rf.time_le
    have := rg.time_le
    omega
  run_eq := by
    intro x
    rw [composeClosure_run, rf.run_eq]
    show _ = SPComp.bind (f x) g
    exact congrArg _ (funext rg.run_eq)

theorem timeAdm_bind {O : CTree.Oracle} {n m : ℕ} {f : Val a → SPComp (Val b)}
    {g : Val b → SPComp (Val c)} (hf : TimeAdm O n f) (hg : TimeAdm O m g) :
    TimeAdm O (n + m + 3) (fun x => f x >>= g) :=
  ⟨hf.1, hg.2.1, hf.2.2.elim fun rf => hg.2.2.elim fun rg => ⟨rf.bind rg⟩⟩

/-- Precomposition by a function `φ` that a closed D-term computes at time `p`. -/
theorem timeAdm_precomp {O : CTree.Oracle} {p n : ℕ} {φ : Val a → Val b}
    {g : Val b → SPComp (Val c)} (hφ : TimeAdm O p (fun x => SPComp.pure (φ x)))
    (hg : TimeAdm O n g) : TimeAdm O (p + n + 3) (g ∘ φ) := by
  have e : (fun x => SPComp.pure (φ x) >>= g) = g ∘ φ :=
    funext fun x => SPComp.pure_bind (φ x) g
  exact e ▸ timeAdm_bind hφ hg

end Compose

/-! ## Renaming and weakening -/

/-- Renamings from `Γ` to `Δ`: a variable of `Δ` for every variable of `Γ`. -/
def Ren (Γ Δ : List Ty) : Type := (τ : Ty) → Var Γ τ → Var Δ τ

/-- A renaming under one more binder. -/
def Ren.lift {Γ Δ : List Ty} {σ : Ty} (r : Ren Γ Δ) : Ren (σ :: Γ) (σ :: Δ) :=
  fun _ x => match x with
    | .here => .here
    | .there y => .there (r _ y)

/-- Renaming of the variables of a term. -/
def Tm.rename {Γ Δ : List Ty} {τ : Ty} : Tm Γ τ → Ren Γ Δ → Tm Δ τ
  | .var x, r => .var (r _ x)
  | .lam b, r => .lam (b.rename r.lift)
  | .app f x, r => .app (f.rename r) (x.rename r)
  | .letE e b, r => .letE (e.rename r) (b.rename r.lift)
  | .seq e b, r => .seq (e.rename r) (b.rename r)
  | .natLit n, _ => .natLit n
  | .lit f v, _ => .lit f v
  | .prim p x, r => .prim p (x.rename r)
  | .pair x y, r => .pair (x.rename r) (y.rename r)
  | .fst p, r => .fst (p.rename r)
  | .snd p, r => .snd (p.rename r)
  | .inl x, r => .inl (x.rename r)
  | .inr x, r => .inr (x.rename r)
  | .case s l rt, r => .case (s.rename r) (l.rename r.lift) (rt.rename r.lift)
  | .ite c t e, r => .ite (c.rename r) (t.rename r) (e.rename r)
  | .nil, _ => .nil
  | .cons x xs, r => .cons (x.rename r) (xs.rename r)
  | .lcase xs n c, r => .lcase (xs.rename r) (n.rename r) (c.rename r.lift.lift)
  | .foldl f i xs, r => .foldl (f.rename r) (i.rename r) (xs.rename r)
  | .iter n f i, r => .iter (n.rename r) (f.rename r) (i.rename r)
  | .sample f, _ => .sample f
  | .get n f, _ => .get n f
  | .set n f x, r => .set n f (x.rename r)
  | .query d r' x, r => .query d r' (x.rename r)

/-- A closed term in any context. -/
def Tm.weaken {Γ : List Ty} {τ : Ty} (t : Tm [] τ) : Tm Γ τ :=
  t.rename fun _ x => nomatch x

/-- An environment read through a renaming. -/
def Env.comp {Γ Δ : List Ty} (ρ : Env Δ) (r : Ren Γ Δ) : Env Γ := fun _ x => ρ _ (r _ x)

theorem Env.comp_lift {Γ Δ : List Ty} {σ : Ty} (ρ : Env Δ) (r : Ren Γ Δ) (v : Val σ) :
    (ρ.cons v).comp r.lift = (ρ.comp r).cons v := by
  funext τ x
  cases x <;> rfl

theorem Env.comp_lift_lift {Γ Δ : List Ty} {σ σ' : Ty} (ρ : Env Δ) (r : Ren Γ Δ)
    (u : Val σ') (v : Val σ) : ((ρ.cons u).cons v).comp r.lift.lift = ((ρ.comp r).cons u).cons v := by
  funext τ x
  rcases x with _ | (_ | _) <;> rfl

section Rename

variable (tk : ∀ {α : Type}, CTree α → CTree α)

/-- The interpreter commutes with renaming. -/
theorem Tm.interp_rename {Γ : List Ty} {τ : Ty} (t : Tm Γ τ) :
    ∀ {Δ : List Ty} (r : Ren Γ Δ) (ρ : Env Δ),
      (t.rename r).interp tk ρ = t.interp tk (ρ.comp r) := by
  induction t
  case lcase xs n c ihxs ihn ihc =>
    intro Δ r ρ
    simp only [Tm.rename, Tm.interp, ihxs, ihn, ihc]
    congr 1
    funext l
    congr 2
    funext x l'
    exact congrArg _ (Env.comp_lift_lift (σ' := .list _) ρ r l' x)
  all_goals (intro Δ r ρ; simp only [Tm.rename, Tm.interp, *, Env.comp_lift] <;> rfl)

end Rename

/-- A weakened closed term evaluates as the closed term. -/
theorem Tm.eval_weaken {Γ : List Ty} {τ : Ty} (t : Tm [] τ) (ρ : Env Γ) :
    (t.weaken : Tm Γ τ).eval ρ = t.eval Env.nil := by
  unfold Tm.weaken Tm.eval
  refine (Tm.interp_rename CTree.tick t _ ρ).trans ?_
  congr 1
  funext _ x
  nomatch x

/-! ## Coproducts -/

section Sum

variable {a b c d : Ty}

/-- The body `case x (inl (f x)) (inr (g x))` of `Tm.sumMap`, with the closed function terms
`f` and `g` weakened under the binder of `x`. -/
def sumMapBody (f : Tm [] (.arr a b)) (g : Tm [] (.arr c d)) :
    Tm [.sum a c] (.sum b d) :=
  .case (.var .here) (.inl (.app f.weaken (.var .here))) (.inr (.app g.weaken (.var .here)))

/-- The coproduct `λx. case x (inl (f x)) (inr (g x))` of the closed function terms `f` and
`g`: a call evaluates only the function term of its branch. -/
def Tm.sumMap (f : Tm [] (.arr a b)) (g : Tm [] (.arr c d)) :
    Tm [] (.arr (.sum a c) (.sum b d)) :=
  .lam (sumMapBody f g)

theorem sumMapBody_eval_inl (f : Tm [] (.arr a b)) (g : Tm [] (.arr c d)) (y : Val a) :
    (sumMapBody f g).eval (Env.nil.cons (τ := .sum a c) (Sum.inl y)) =
      .tick ((f.applyEval y).bind fun v => .ret (Sum.inl v : Val b ⊕ Val d)) := by
  show CTree.tick ((((Tm.weaken f : Tm [a, .sum a c] _).eval _).bind fun h =>
    CTree.tick (h y)).bind _) = _
  rw [Tm.eval_weaken]
  rfl

theorem sumMapBody_eval_inr (f : Tm [] (.arr a b)) (g : Tm [] (.arr c d)) (z : Val c) :
    (sumMapBody f g).eval (Env.nil.cons (τ := .sum a c) (Sum.inr z)) =
      .tick ((g.applyEval z).bind fun v => .ret (Sum.inr v : Val b ⊕ Val d)) := by
  show CTree.tick ((((Tm.weaken g : Tm [c, .sum a c] _).eval _).bind fun h =>
    CTree.tick (h z)).bind _) = _
  rw [Tm.eval_weaken]
  rfl

/-- The cost of a bind with a leaf continuation is at most the cost of the tree. -/
theorem cost_bind_ret_le {α β : Type} (t : CTree α) (k : α → β) :
    (t.bind fun v => .ret (k v)).cost ≤ t.cost := by
  simpa using CTree.cost_bind_le t (fun v => .ret (k v)) 0
    (CTree.AllRet.of_forall (fun _ => le_refl _) _)

/-- The realizer `Tm.sumMap tf tg` of the coproduct at the maximum of the two times plus two
steps: the case analysis and the β-step of the call. -/
def TimeRealizer.mapSum {O : CTree.Oracle} {n m : ℕ} {f : Val a → SPComp (Val b)}
    {g : Val c → SPComp (Val d)} (rf : TimeRealizer O n f) (rg : TimeRealizer O m g) :
    TimeRealizer (a := .sum a c) (b := .sum b d) O (max n m + 2) (mapSum f g) where
  term := Tm.sumMap rf.term rg.term
  evalCost := 0
  callCost := max n m + 1
  closure := fun x => (sumMapBody rf.term rg.term).eval (Env.nil.cons x)
  evals := rfl
  call_le := by
    intro x
    change Val a ⊕ Val c at x
    rcases x with y | z
    · rw [sumMapBody_eval_inl, CTree.cost_tick]
      have h2 := rf.apply_cost_le y
      exact le_trans (Nat.add_le_add_left ((cost_bind_ret_le _ _).trans
        (h2.trans (le_max_left n m))) 1) (by omega)
    · rw [sumMapBody_eval_inr, CTree.cost_tick]
      have h2 := rg.apply_cost_le z
      exact le_trans (Nat.add_le_add_left ((cost_bind_ret_le _ _).trans
        (h2.trans (le_max_right n m))) 1) (by omega)
  time_le := by omega
  run_eq := by
    intro x
    change Val a ⊕ Val c at x
    rcases x with y | z
    · show ((sumMapBody rf.term rg.term).eval (Env.nil.cons (Sum.inl y))).run O = _
      rw [sumMapBody_eval_inl]
      show ((rf.term.applyEval y).bind _).run O = _
      rw [CTree.run_bind, mapSum_inl, SPComp.map, rf.apply_run]
      rfl
    · show ((sumMapBody rf.term rg.term).eval (Env.nil.cons (Sum.inr z))).run O = _
      rw [sumMapBody_eval_inr]
      show ((rg.term.applyEval z).bind _).run O = _
      rw [CTree.run_bind, mapSum_inr, SPComp.map, rg.apply_run]
      rfl

theorem timeAdm_mapSum {O : CTree.Oracle} {n m : ℕ} {f : Val a → SPComp (Val b)}
    {g : Val c → SPComp (Val d)} (hf : TimeAdm O n f) (hg : TimeAdm O m g) :
    TimeAdm (a := .sum a c) (b := .sum b d) O (max n m + 2) (mapSum f g) := by
  obtain ⟨ha, hb, ⟨rf⟩⟩ := hf
  obtain ⟨hc, hd, ⟨rg⟩⟩ := hg
  exact ⟨⟨ha, hc⟩, ⟨hb, hd⟩, ⟨rf.mapSum rg⟩⟩

variable (a c) in
/-- The realizer `λx. inl x` of the left injection. -/
def TimeRealizer.inl (O : CTree.Oracle) :
    TimeRealizer (a := a) (b := .sum a c) O 1
      (fun x : Val a => SPComp.pure (Sum.inl x : Val a ⊕ Val c)) where
  term := .lam (.inl (.var .here))
  evalCost := 0
  callCost := 0
  closure := fun v => .ret (Sum.inl v : Val a ⊕ Val c)
  evals := rfl
  call_le := fun _ => le_refl _
  time_le := le_refl _
  run_eq := fun _ => rfl

variable (a c) in
/-- The realizer `λx. inr x` of the right injection. -/
def TimeRealizer.inr (O : CTree.Oracle) :
    TimeRealizer (a := c) (b := .sum a c) O 1
      (fun x : Val c => SPComp.pure (Sum.inr x : Val a ⊕ Val c)) where
  term := .lam (.inr (.var .here))
  evalCost := 0
  callCost := 0
  closure := fun v => .ret (Sum.inr v : Val a ⊕ Val c)
  evals := rfl
  call_le := fun _ => le_refl _
  time_le := le_refl _
  run_eq := fun _ => rfl

/-- The injection `inl` is admissible at time `1`. -/
theorem timeAdm_inl (O : CTree.Oracle) (ha : a.FO) (hc : c.FO) :
    TimeAdm (a := a) (b := .sum a c) O 1
      (fun x : Val a => SPComp.pure (Sum.inl x : Val a ⊕ Val c)) :=
  ⟨ha, ⟨ha, hc⟩, ⟨TimeRealizer.inl a c O⟩⟩

/-- The injection `inr` is admissible at time `1`. -/
theorem timeAdm_inr (O : CTree.Oracle) (ha : a.FO) (hc : c.FO) :
    TimeAdm (a := c) (b := .sum a c) O 1
      (fun x : Val c => SPComp.pure (Sum.inr x : Val a ⊕ Val c)) :=
  ⟨hc, ⟨ha, hc⟩, ⟨TimeRealizer.inr a c O⟩⟩

end Sum

/-! ## The time-bounded computational distance -/

section Distance

variable (O : CTree.Oracle)

/-- The computational distance at time `t`: the supremum of the per-distinguisher distance
over the distinguishers admissible at time `t`. -/
noncomputable def ucCdistTime {α : Type} {b : Ty} (t : ℕ) (f g : α → SPComp (Val b)) :
    ℝ≥0∞ :=
  ⨆ (D : Val b → SPComp Bool) (_ : TimeAdm (b := .bool) O t D), spcomp_distComp f g D

variable {O}

theorem ucCdistTime_le_sdist {α : Type} {b : Ty} (t : ℕ) (f g : α → SPComp (Val b)) :
    ucCdistTime O t f g ≤ sdist f g := by
  rw [spcomp_sdist_eq_iSup]
  exact iSup₂_le fun D _ => le_iSup (spcomp_distComp f g) D

theorem ucCdistTime_self {α : Type} {b : Ty} (t : ℕ) (f : α → SPComp (Val b)) :
    ucCdistTime O t f f = 0 := by
  simp [ucCdistTime, spcomp_distComp_self]

theorem ucCdistTime_sym {α : Type} {b : Ty} (t : ℕ) (f g : α → SPComp (Val b)) :
    ucCdistTime O t f g = ucCdistTime O t g f := by
  simp only [ucCdistTime, spcomp_distComp_comm f g]

theorem ucCdistTime_triangle {α : Type} {b : Ty} (t : ℕ) (f g h : α → SPComp (Val b)) :
    ucCdistTime O t f h ≤ ucCdistTime O t f g + ucCdistTime O t g h := by
  refine iSup₂_le fun D hD => (spcomp_distComp_triangle f g h D).trans (add_le_add ?_ ?_)
  · exact le_iSup₂ (f := fun D (_ : TimeAdm (b := .bool) O t D) => spcomp_distComp f g D) D hD
  · exact le_iSup₂ (f := fun D (_ : TimeAdm (b := .bool) O t D) => spcomp_distComp g h D) D hD

theorem ucCdistTime_mono {α : Type} {b : Ty} {t t' : ℕ} (htt : t ≤ t')
    (f g : α → SPComp (Val b)) : ucCdistTime O t f g ≤ ucCdistTime O t' f g :=
  iSup₂_le fun D hD =>
    le_iSup₂ (f := fun D (_ : TimeAdm (b := .bool) O t' D) => spcomp_distComp f g D) D
      (hD.mono htt)

/-- Post-composition with an arrow admissible at time `s` moves the time to `s + t + 3`. -/
theorem ucCdistTime_comp_right {α : Type} {b c : Ty} {s : ℕ} (t : ℕ)
    (f g : α → SPComp (Val b)) (k : Val b → SPComp (Val c)) (hk : TimeAdm O s k) :
    ucCdistTime O t (fun x => SPComp.bind (f x) k) (fun x => SPComp.bind (g x) k) ≤
      ucCdistTime O (s + t + 3) f g := by
  refine iSup₂_le fun D hD => ?_
  rw [spcomp_distComp_bind_right]
  exact le_iSup₂ (f := fun D (_ : TimeAdm (b := .bool) O (s + t + 3) D) =>
    spcomp_distComp f g D) (fun y => SPComp.bind (k y) D) (timeAdm_bind hk hD)

/-- Pre-composition with any arrow does not increase the distance. -/
theorem ucCdistTime_comp_left {α β : Type} {c : Ty} (t : ℕ) (f : α → SPComp β)
    (g₁ g₂ : β → SPComp (Val c)) :
    ucCdistTime O t (fun x => SPComp.bind (f x) g₁) (fun x => SPComp.bind (f x) g₂) ≤
      ucCdistTime O t g₁ g₂ :=
  iSup₂_le fun D hD => (spcomp_distComp_bind_left f g₁ g₂ D).trans
    (le_iSup₂ (f := fun D (_ : TimeAdm (b := .bool) O t D) => spcomp_distComp g₁ g₂ D) D hD)

/-- Sequential composition of close arrows: the first hop is measured at time `s + t + 3`. -/
theorem ucCdistTime_comp_add {α : Type} {b c : Ty} {s : ℕ} (t : ℕ)
    (f₁ f₂ : α → SPComp (Val b)) (g₁ g₂ : Val b → SPComp (Val c))
    {ε₁ ε₂ : ℝ≥0∞}
    (hf : ucCdistTime O (s + t + 3) f₁ f₂ ≤ ε₁) (hg₁ : TimeAdm O s g₁)
    (hg : ucCdistTime O t g₁ g₂ ≤ ε₂) :
    ucCdistTime O t (fun x => SPComp.bind (f₁ x) g₁) (fun x => SPComp.bind (f₂ x) g₂) ≤
      ε₁ + ε₂ :=
  (ucCdistTime_triangle t _ (fun x => SPComp.bind (f₂ x) g₁) _).trans
    (add_le_add ((ucCdistTime_comp_right t f₁ f₂ g₁ hg₁).trans hf)
      ((ucCdistTime_comp_left t f₂ g₁ g₂).trans hg))

/-- Parallel composition: each component is measured at time `t + 4`. -/
theorem ucCdistTime_mapSum_le {α₁ α₂ : Type} {b₁ b₂ : Ty} (t : ℕ)
    (f₁ f₂ : α₁ → SPComp (Val b₁)) (g₁ g₂ : α₂ → SPComp (Val b₂)) :
    ucCdistTime O (b := .sum b₁ b₂) t (mapSum f₁ g₁) (mapSum f₂ g₂) ≤
      ucCdistTime O (t + 4) f₁ f₂ ⊔ ucCdistTime O (t + 4) g₁ g₂ := by
  refine iSup₂_le fun D hD =>
    (spcomp_distComp_mapSum f₁ f₂ g₁ g₂ D).trans (sup_le_sup ?_ ?_)
  · have h := timeAdm_precomp (timeAdm_inl O hD.1.1 hD.1.2) hD
    exact le_iSup₂ (f := fun D (_ : TimeAdm (b := .bool) O (t + 4) D) =>
      spcomp_distComp f₁ f₂ D) (fun y => D (Sum.inl y)) (h.mono (by omega))
  · have h := timeAdm_precomp (timeAdm_inr O hD.1.1 hD.1.2) hD
    exact le_iSup₂ (f := fun D (_ : TimeAdm (b := .bool) O (t + 4) D) =>
      spcomp_distComp g₁ g₂ D) (fun y => D (Sum.inr y)) (h.mono (by omega))

end Distance

end CatCrypt.Complexity.D
