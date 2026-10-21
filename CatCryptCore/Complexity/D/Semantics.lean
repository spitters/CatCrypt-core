/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Complexity.D.Syntax

/-!
# Evaluator and denotation of the deep language D

`Tm.interp tk` is a big-step, environment-passing interpreter of D (a definitional interpreter
in Reynolds' sense) into costed effect trees `CTree`, parameterised by the node `tk` placed at
each evaluation step. Its two instances are:

* `Tm.eval`, with `tk = CTree.tick`: the evaluator. A tick is placed at every β-step (an
  application of a function value, a `letE`, a `seq`, every iteration of `foldl` and `iter`),
  and at every branch (`case`, `ite`, `lcase`); a primitive operation `p` at the argument `v`
  places `p.cost v` ticks (`stepN`), logarithmic cost on `ℕ` and one tick on `Bool` and
  words; variables, literals, constructors, projections and closures are free. With the unit
  cost of the effect nodes this is the convention of L (Forster–Kunze) and of `derive_timed`,
  with `letE` priced as the β-redex `(λx. b) e`. The cost of a term is therefore determined
  by its evaluation (`CatCryptCore.Complexity.D.Cost`).
* `Tm.den`, with `tk = id`: the denotation, a tick-free tree; `Tm.denote O t ρ`, its meaning
  in `SPComp` with the oracle answered by `O`, is what a term is compared with when it is
  compared with an ordinary Lean definition.

Both are defined by structural recursion on the term: D has only structural recursion
(`foldl`, `iter`), so neither needs fuel.

## Adequacy

Function values of the two instances differ (the evaluator's closures carry ticks), so they
are related by a logical relation `ValRel`: equality at ground types, the lifting `CTree.Rel`
at function types. `Tm.interp_rel` is the fundamental lemma: in related environments the
evaluator and the denotation give related trees. At first-order types `ValRel` is equality,
so the evaluator with its ticks erased is the denotation (`Tm.eval_erase`), and both have the
same meaning in `SPComp` (`Tm.run_eval`).

## Renaming

The interpreter commutes with renaming (`Tm.interp_rename`), and a weakened closed term
evaluates as the closed term (`Tm.eval_weaken`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Complexity.D

open CatCrypt.Core

/-! ## The interpreter -/

section Interp

variable (tk : ∀ {α : Type}, CTree α → CTree α)

/-- Left fold of a function value over a list, one step node per application. -/
def foldT {a c : Ty} (g : Val (.arr (.prod c a) c)) : Val c → List (Val a) → CTree (Val c)
  | acc, [] => .ret acc
  | acc, x :: xs => (tk (g (acc, x))).bind fun acc' => foldT g acc' xs

/-- `n`-fold iteration of a function value, one step node per application. -/
def iterT {c : Ty} (g : Val (.arr c c)) : Val c → ℕ → CTree (Val c)
  | acc, 0 => .ret acc
  | acc, n + 1 => (tk (g acc)).bind fun acc' => iterT g acc' n

/-- `n` step nodes in front of a tree. -/
def stepN {α : Type} : ℕ → CTree α → CTree α
  | 0, t => t
  | n + 1, t => tk (stepN n t)

/-- Case analysis on a list. -/
def listCase {α β : Type} (l : List α) (n : β) (c : α → List α → β) : β :=
  match l with
  | [] => n
  | x :: xs => c x xs

/-- The interpreter of D into costed trees, with `tk` at every evaluation step. -/
def Tm.interp {Γ : List Ty} {τ : Ty} : Tm Γ τ → Env Γ → CTree (Val τ)
  | .var x, ρ => .ret (ρ _ x)
  | .lam b, ρ => .ret fun v => Tm.interp b (ρ.cons v)
  | .app f x, ρ => (Tm.interp f ρ).bind fun g => (Tm.interp x ρ).bind fun v => tk (g v)
  | .letE e b, ρ => (Tm.interp e ρ).bind fun v => tk (Tm.interp b (ρ.cons v))
  | .seq e b, ρ => (Tm.interp e ρ).bind fun _ => tk (Tm.interp b ρ)
  | .natLit n, _ => .ret n
  | .lit _ v, _ => .ret v
  | .prim p x, ρ => (Tm.interp x ρ).bind fun v => stepN tk (p.cost v) (.ret (p.apply v))
  | .pair x y, ρ => (Tm.interp x ρ).bind fun u => (Tm.interp y ρ).bind fun v => .ret (u, v)
  | .fst (a := a) (b := b) p, ρ => (Tm.interp p ρ).bind fun (v : Val a × Val b) => .ret v.1
  | .snd (a := a) (b := b) p, ρ => (Tm.interp p ρ).bind fun (v : Val a × Val b) => .ret v.2
  | .inl (a := a) (b := b) x, ρ =>
    (Tm.interp x ρ).bind fun v => .ret (Sum.inl v : Val a ⊕ Val b)
  | .inr (a := a) (b := b) x, ρ =>
    (Tm.interp x ρ).bind fun v => .ret (Sum.inr v : Val a ⊕ Val b)
  | .case (a := a) (b := b) s l r, ρ =>
    (Tm.interp s ρ).bind fun (v : Val a ⊕ Val b) =>
      tk (Sum.elim (fun x => Tm.interp l (ρ.cons x)) (fun y => Tm.interp r (ρ.cons y)) v)
  | .ite c t e, ρ =>
    (Tm.interp c ρ).bind fun (b : Bool) => tk (bif b then Tm.interp t ρ else Tm.interp e ρ)
  | .nil (a := a), _ => .ret ([] : List (Val a))
  | .cons (a := a) x xs, ρ =>
    (Tm.interp x ρ).bind fun v => (Tm.interp xs ρ).bind fun (l : List (Val a)) => .ret (v :: l)
  | .lcase (a := a) xs n c, ρ =>
    (Tm.interp xs ρ).bind fun (l : List (Val a)) =>
      tk (listCase l (Tm.interp n ρ) fun x l' =>
        Tm.interp c (((ρ.cons (τ := .list a) l').cons x)))
  | .foldl f i xs, ρ =>
    (Tm.interp f ρ).bind fun g => (Tm.interp i ρ).bind fun acc =>
      (Tm.interp xs ρ).bind fun l => foldT tk g acc l
  | .iter n f i, ρ =>
    (Tm.interp n ρ).bind fun (k : ℕ) => (Tm.interp f ρ).bind fun g =>
      (Tm.interp i ρ).bind fun acc => iterT tk g acc k
  | .sample f, _ => .sample f .ret
  | .get n f, _ => .get n f .ret
  | .set n f x, ρ => (Tm.interp x ρ).bind fun v => .set n f v (.ret (() : Unit))
  | .query d r x, ρ => (Tm.interp x ρ).bind fun v => .query d r v .ret

end Interp

namespace Tm

variable {Γ : List Ty} {τ : Ty}

/-- The evaluator: a tick at every evaluation step. -/
def eval (t : Tm Γ τ) (ρ : Env Γ) : CTree (Val τ) := t.interp CTree.tick ρ

/-- The denotation as a tick-free tree. -/
def den (t : Tm Γ τ) (ρ : Env Γ) : CTree (Val τ) := t.interp (fun t => t) ρ

/-- The denotation in `SPComp`, the oracle answered by `O`. -/
noncomputable def denote (O : CTree.Oracle) (t : Tm Γ τ) (ρ : Env Γ) : SPComp (Val τ) :=
  (t.den ρ).run O

end Tm

/-! ## The logical relation -/

/-- The logical relation between the values of the evaluator and of the denotation: equality
at ground types, the lifting `CTree.Rel` at function types. -/
def ValRel : (τ : Ty) → Val τ → Val τ → Prop
  | .base _, u, v => u = v
  | .nat, u, v => u = v
  | .prod a b, u, v => ValRel a u.1 v.1 ∧ ValRel b u.2 v.2
  | .sum a b, u, v => Sum.LiftRel (ValRel a) (ValRel b) u v
  | .arr a b, f, g => ∀ x y, ValRel a x y → CTree.Rel (ValRel b) (f x) (g y)
  | .list a, u, v => List.Forall₂ (ValRel a) u v

/-- Pointwise related environments. -/
def EnvRel {Γ : List Ty} (ρ δ : Env Γ) : Prop := ∀ τ (x : Var Γ τ), ValRel τ (ρ τ x) (δ τ x)

theorem EnvRel.cons {Γ : List Ty} {τ : Ty} {ρ δ : Env Γ} (h : EnvRel ρ δ) {u v : Val τ}
    (huv : ValRel τ u v) : EnvRel (ρ.cons u) (δ.cons v) := by
  intro σ x
  cases x with
  | here => exact huv
  | there y => exact h σ y

/-- At first-order types the logical relation is equality. -/
theorem ValRel.iff_eq_of_FO : (τ : Ty) → τ.FO → ∀ u v : Val τ, ValRel τ u v ↔ u = v
  | .base _, _, _, _ => Iff.rfl
  | .nat, _, _, _ => Iff.rfl
  | .prod a b, h, u, v => by
    have ha := ValRel.iff_eq_of_FO a h.1
    have hb := ValRel.iff_eq_of_FO b h.2
    show ValRel a u.1 v.1 ∧ ValRel b u.2 v.2 ↔ u = v
    rw [ha, hb]
    exact Prod.ext_iff.symm
  | .sum a b, h, u, v => by
    have ha := ValRel.iff_eq_of_FO a h.1
    have hb := ValRel.iff_eq_of_FO b h.2
    change Val a ⊕ Val b at u v
    show Sum.LiftRel (ValRel a) (ValRel b) u v ↔ u = v
    constructor
    · rintro (⟨hx⟩ | ⟨hy⟩)
      · exact congrArg Sum.inl ((ha _ _).1 hx)
      · exact congrArg Sum.inr ((hb _ _).1 hy)
    · rintro rfl
      cases u with
      | inl x => exact .inl ((ha x x).2 rfl)
      | inr y => exact .inr ((hb y y).2 rfl)
  | .arr _ _, h, _, _ => h.elim
  | .list a, h, u, v => by
    have ha := ValRel.iff_eq_of_FO a h
    show List.Forall₂ (ValRel a) u v ↔ u = v
    have hab : ValRel a = (· = ·) := funext fun x => funext fun y => propext (ha x y)
    rw [hab, List.forall₂_eq_eq_eq]
    exact Iff.rfl

theorem Prim.rel {a b : Ty} (p : Prim a b) {u v : Val a} (h : ValRel a u v) :
    ValRel b (p.apply u) (p.apply v) := by
  rw [ValRel.iff_eq_of_FO a p.fo.1] at h
  rw [ValRel.iff_eq_of_FO b p.fo.2, h]

/-- Without step nodes, `stepN` is the identity. -/
theorem stepN_id {α : Type} (n : ℕ) (t : CTree α) : stepN (fun t => t) n t = t := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih

/-- Ticks in front of the left tree preserve the relation. -/
theorem stepN_tick_rel {α β : Type} {R : α → β → Prop} {t : CTree α} {m : CTree β}
    (h : CTree.Rel R t m) (n : ℕ) : CTree.Rel R (stepN CTree.tick n t) m := by
  induction n with
  | zero => exact h
  | succ n ih => exact .tick ih

/-- Ticks in front of a tree commute with a bind. -/
theorem stepN_tick_bind {α β : Type} (n : ℕ) (t : CTree α) (g : α → CTree β) :
    (stepN CTree.tick n t).bind g = stepN CTree.tick n (t.bind g) := by
  induction n with
  | zero => rfl
  | succ n ih => exact congrArg CTree.tick ih

theorem foldT_rel {a c : Ty} {g g' : Val (.arr (.prod c a) c)} (hg : ValRel _ g g')
    {l l' : List (Val a)} (hl : List.Forall₂ (ValRel a) l l') :
    ∀ {acc acc' : Val c}, ValRel c acc acc' →
      CTree.Rel (ValRel c) (foldT CTree.tick g acc l) (foldT (fun t => t) g' acc' l') := by
  induction hl with
  | nil => intro acc acc' h; exact .ret h
  | cons hx _ ih =>
    intro acc acc' h
    exact (CTree.Rel.tick (hg _ _ ⟨h, hx⟩)).bind fun _ _ hc => ih hc

theorem iterT_rel {c : Ty} {g g' : Val (.arr c c)} (hg : ValRel _ g g') (n : ℕ) :
    ∀ {acc acc' : Val c}, ValRel c acc acc' →
      CTree.Rel (ValRel c) (iterT CTree.tick g acc n) (iterT (fun t => t) g' acc' n) := by
  induction n with
  | zero => intro acc acc' h; exact .ret h
  | succ n ih =>
    intro acc acc' h
    exact (CTree.Rel.tick (hg _ _ h)).bind fun _ _ hc => ih hc

theorem sumElim_rel {α β α' β' γ γ' : Type} {R : α → α' → Prop} {S : β → β' → Prop}
    {T : γ → γ' → Prop} {f : α → CTree γ} {f' : α' → CTree γ'} {g : β → CTree γ}
    {g' : β' → CTree γ'} (hf : ∀ x y, R x y → CTree.Rel T (f x) (f' y))
    (hg : ∀ x y, S x y → CTree.Rel T (g x) (g' y)) {u : α ⊕ β} {v : α' ⊕ β'}
    (huv : Sum.LiftRel R S u v) : CTree.Rel T (Sum.elim f g u) (Sum.elim f' g' v) := by
  cases huv with
  | inl h => exact hf _ _ h
  | inr h => exact hg _ _ h

theorem cond_rel {γ γ' : Type} {T : γ → γ' → Prop} {x y : CTree γ} {x' y' : CTree γ'}
    (hx : CTree.Rel T x x') (hy : CTree.Rel T y y') (b : Bool) :
    CTree.Rel T (bif b then x else y) (bif b then x' else y') := by
  cases b
  · exact hy
  · exact hx

theorem listCase_rel {α α' γ γ' : Type} {R : α → α' → Prop} {T : γ → γ' → Prop}
    {n : CTree γ} {n' : CTree γ'} {c : α → List α → CTree γ} {c' : α' → List α' → CTree γ'}
    (hn : CTree.Rel T n n')
    (hc : ∀ x y l l', R x y → List.Forall₂ R l l' → CTree.Rel T (c x l) (c' y l'))
    {l : List α} {l' : List α'} (hl : List.Forall₂ R l l') :
    CTree.Rel T (listCase l n c) (listCase l' n' c') := by
  cases hl with
  | nil => exact hn
  | cons hx hxs => exact hc _ _ _ _ hx hxs

namespace Tm

/-- The fundamental lemma: in related environments the evaluator and the denotation give
related trees. -/
theorem interp_rel {Γ : List Ty} {τ : Ty} (t : Tm Γ τ) :
    ∀ {ρ δ : Env Γ}, EnvRel ρ δ → CTree.Rel (ValRel τ) (t.eval ρ) (t.den δ) := by
  induction t with
  | var x => intro ρ δ h; exact .ret (h _ x)
  | lam b ih => intro ρ δ h; exact .ret fun u v huv => ih (h.cons huv)
  | app f x ihf ihx =>
    intro ρ δ h
    exact (ihf h).bind fun g g' hg => (ihx h).bind fun u v huv => .tick (hg u v huv)
  | letE e b ihe ihb =>
    intro ρ δ h; exact (ihe h).bind fun u v huv => .tick (ihb (h.cons huv))
  | seq e b ihe ihb => intro ρ δ h; exact (ihe h).bind fun _ _ _ => .tick (ihb h)
  | natLit n => intro ρ δ h; exact .ret rfl
  | lit f v => intro ρ δ h; exact .ret rfl
  | prim p x ih =>
    intro ρ δ h
    refine (ih h).bind fun u v huv => ?_
    rw [stepN_id]
    exact stepN_tick_rel (.ret (p.rel huv)) _
  | pair x y ihx ihy =>
    intro ρ δ h
    exact (ihx h).bind fun u u' hu => (ihy h).bind fun v v' hv => .ret ⟨hu, hv⟩
  | fst p ih => intro ρ δ h; exact (ih h).bind fun u v huv => .ret huv.1
  | snd p ih => intro ρ δ h; exact (ih h).bind fun u v huv => .ret huv.2
  | inl x ih => intro ρ δ h; exact (ih h).bind fun u v huv => .ret (Sum.LiftRel.inl huv)
  | inr x ih => intro ρ δ h; exact (ih h).bind fun u v huv => .ret (Sum.LiftRel.inr huv)
  | case s l r ihs ihl ihr =>
    intro ρ δ h
    exact (ihs h).bind fun u v huv =>
      .tick (sumElim_rel (fun _ _ hx => ihl (h.cons hx)) (fun _ _ hy => ihr (h.cons hy)) huv)
  | ite c t e ihc iht ihe =>
    intro ρ δ h
    exact (ihc h).bind fun u v huv => by
      change u = v at huv
      subst huv
      exact .tick (cond_rel (iht h) (ihe h) u)
  | nil => intro ρ δ h; exact .ret List.Forall₂.nil
  | cons x xs ihx ihxs =>
    intro ρ δ h
    exact (ihx h).bind fun u v huv => (ihxs h).bind fun l l' hl => .ret (List.Forall₂.cons huv hl)
  | lcase xs n c ihxs ihn ihc =>
    intro ρ δ h
    exact (ihxs h).bind fun l l' hl =>
      .tick (listCase_rel (ihn h) (fun _ _ _ _ hx hxs => ihc ((h.cons (τ := .list _) hxs).cons hx)) hl)
  | foldl f i xs ihf ihi ihxs =>
    intro ρ δ h
    exact (ihf h).bind fun g g' hg => (ihi h).bind fun a a' ha =>
      (ihxs h).bind fun l l' hl => foldT_rel hg hl ha
  | iter n f i ihn ihf ihi =>
    intro ρ δ h
    exact (ihn h).bind fun k k' hk => by
      change k = k' at hk
      subst hk
      exact (ihf h).bind fun g g' hg => (ihi h).bind fun a a' ha => iterT_rel hg k ha
  | sample f => intro ρ δ h; exact .sample f fun _ => .ret rfl
  | get n f => intro ρ δ h; exact .get n f fun _ => .ret rfl
  | set n f x ih =>
    intro ρ δ h
    exact (ih h).bind fun u v huv => by
      change u = v at huv
      subst huv
      exact .set n f u (.ret rfl)
  | query d r x ih =>
    intro ρ δ h
    exact (ih h).bind fun u v huv => by
      change u = v at huv
      subst huv
      exact .query d r u fun _ => .ret rfl

/-- Adequacy at first-order types: the evaluator with its ticks erased is the denotation. -/
theorem eval_erase {Γ : List Ty} {τ : Ty} (t : Tm Γ τ) (hτ : τ.FO) (hΓ : ∀ σ ∈ Γ, σ.FO)
    (ρ : Env Γ) : (t.eval ρ).erase = t.den ρ := by
  have hρ : EnvRel ρ ρ := fun σ x => (ValRel.iff_eq_of_FO σ (hΓ σ x.mem) _ _).2 rfl
  exact ((t.interp_rel hρ).mono fun u v huv => (ValRel.iff_eq_of_FO τ hτ u v).1 huv).erase_eq

/-- Adequacy in `SPComp`: the evaluator has the meaning of the denotation. -/
theorem run_eval {Γ : List Ty} {τ : Ty} (O : CTree.Oracle) (t : Tm Γ τ) (hτ : τ.FO)
    (hΓ : ∀ σ ∈ Γ, σ.FO) (ρ : Env Γ) : (t.eval ρ).run O = t.denote O ρ := by
  rw [← CTree.run_erase, t.eval_erase hτ hΓ ρ]
  rfl

end Tm

/-! ## Renaming -/

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

end CatCrypt.Complexity.D
