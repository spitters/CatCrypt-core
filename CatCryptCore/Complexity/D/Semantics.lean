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
  at every branch (`case`, `ite`, `lcase`) and at every node that `fold` visits; a primitive
  operation `p` at the argument `v` places `p.cost v` ticks (`stepN`), logarithmic cost on `ℕ` and one tick on `Bool` and
  words, and in the bit length of the modulus on `Fin (n + 1)`; variables, literals,
  constructors, projections, closures and `fail` are free. With the unit
  cost of the effect nodes this is the convention of L (Forster–Kunze) and of `derive_timed`,
  with `letE` priced as the β-redex `(λx. b) e`. The cost of a term is therefore determined
  by its evaluation (`CatCryptCore.Complexity.D.Cost`).
* `Tm.den`, with `tk = id`: the denotation, a tick-free tree; `Tm.denote O t ρ`, its meaning
  in `SPComp` with the oracle answered by `O`, is what a term is compared with when it is
  compared with an ordinary Lean definition.

Both are defined by structural recursion on the term: D has only structural recursion
(`foldl`, `iter`, `fold`), so neither needs fuel.

## Inductive types

`con` costs nothing: the children of a constructor with positions `some f` are a table, a value
of `pi f fun _ => X`, whose components are evaluated where the table is built (`ptab`), so a
constructor is free, as `derive_timed` charges a constructor. `fold g x` places one step node
and applies the step function of the constructor of the root (`stepAt`, `foldW`); the
recursive results it
receives are evaluated when the step applies them, each application a step node, so that a fold
costs one step per node it visits plus the step functions there, as a call of a structural
recursion costs one plus its body, and a child whose result the step does not apply costs
nothing. A case analysis is the `fold` that applies no recursive result: one step plus the
branch.

## Dependent products and sums

`ptab ts` evaluates its components in the order of `tabT` (`tabDep`: each leaf tagged with its
element, then read back as a dependent function), at no cost of its own, as `pair` is free: the
table costs the sum of its components. `papp` and `spair` are free, as projections and
constructors are; `scase` and `fcase` place one step node and continue with the branch, as
`case` does.

## Adequacy

Function values of the two instances differ (the evaluator's closures carry ticks), so they
are related by a logical relation `ValRel`: equality at ground types and at inductive types,
whose fields are first-order, the lifting `CTree.Rel` at function types, componentwise at
dependent products and at the common index of dependent pairs. `Tm.interp_rel` is the fundamental lemma: in related environments the
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

/-- The step of an eliminator of `S` at a node of shape `a`, with its children `kids` and its
recursive results `rec`: the step function of the constructor of `a` applied to the field, and
for a constructor with positions to the children and the results as functions of the
positions. -/
def stepAt {X c : Ty} : (S : Sig) → Val (S.stepsTy X c) → (a : (Sig.den S).1) →
    ((Sig.den S).2 a → Val X) → ((Sig.den S).2 a → CTree (Val c)) → CTree (Val c)
  | .base _, g, x, _, _ => g x
  | .ext S _ _, g, .inl x, kids, rec => stepAt S g.1 x kids rec
  | .ext _ _ none, g, .inr x, _, _ => g.2 x
  | .ext _ a (some f), g, .inr x, kids, rec =>
    let g' : Val (.arr (Sig.altTy a (some f) X c) c) := g.2
    g' ((x, kids, rec) : Val a × ((f.den → Val X) × (f.den → CTree (Val c))))

/-- The eliminator of `mu S` with the step functions `g`: the step at each node, its recursive
results the eliminator at the children, evaluated when the step applies them. -/
def foldW {S : Sig} {c : Ty} (g : Val (S.stepsTy (.mu S) c)) : WType (Sig.den S).2 → CTree (Val c)
  | ⟨a, kids⟩ => stepAt S g a kids fun j => foldW g (kids j)

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

/-- Tabulation over `Fin n`: the trees at `0, 1, …, n - 1` in this order, their leaves
collected into a function. -/
def tabFin {X : Type} : (n : ℕ) → (Fin n → CTree X) → CTree (Fin n → X)
  | 0, _ => .ret Fin.elim0
  | n + 1, g => (g 0).bind fun x => (tabFin n fun i => g i.succ).bind fun h =>
      .ret (Fin.cons x h : Fin (n + 1) → X)

/-- Tabulation over the functions `Fin q → r.den`, from a tabulation `tr` over `r`: by the first
value, then the rest. -/
def tabTab (r : FTy) (tr : ∀ {Y : Type}, (r.den → CTree Y) → CTree (r.den → Y)) {X : Type} :
    (q : ℕ) → ((Fin q → r.den) → CTree X) → CTree ((Fin q → r.den) → X)
  | 0, g => (g Fin.elim0).bind fun x => .ret fun _ => x
  | q + 1, g => (tr fun a => tabTab r tr q fun h => g (Fin.cons a h : Fin (q + 1) → r.den)).bind
      fun T => .ret fun v => T (v 0) (Fin.tail v)

/-- Tabulation over a finite ground type: the trees at every element in a fixed order, their
leaves collected into a function. -/
def tabT : (f : FTy) → {X : Type} → (f.den → CTree X) → CTree (f.den → X)
  | .unit, _, g => (g ()).bind fun x => .ret fun _ => x
  | .bool, _, g => (g false).bind fun x => (g true).bind fun y =>
      .ret fun b => bif b then y else x
  | .word w, _, g => (tabFin (2 ^ w) fun i => g (BitVec.ofFin i)).bind fun h =>
      .ret fun v => h v.toFin
  | .fin n, _, g => tabFin (n + 1) g
  | .tab q r, _, g => tabTab r (fun g' => tabT r g') q g

/-- The value of a dependent pair at the element `j`: its value when its index is `j`, the
default `d j` otherwise. -/
def sigmaAt {I : Type} (dec : DecidableEq I) {X : I → Type} (d : (j : I) → X j)
    (s : (j : I) × X j) (j : I) : X j :=
  @dite _ (s.1 = j) (dec s.1 j) (fun e => e ▸ s.2) fun _ => d j

/-- Dependent tabulation over a finite ground type: the trees at every element in the order of
`tabT`, their leaves collected into a dependent function. Each leaf is tagged with its element,
and the default `d` is the value at an element whose tag differs, which does not occur
(`tabDep_rel`). -/
def tabDep (f : FTy) {X : f.den → Type} (d : (j : f.den) → X j)
    (g : (j : f.den) → CTree (X j)) : CTree ((j : f.den) → X j) :=
  (tabT f fun j => (g j).bind fun x => .ret (⟨j, x⟩ : (j : f.den) × X j)).bind fun h =>
    .ret fun j => sigmaAt (FTy.decEq f) d (h j) j

/-- A constructor of a signature `S` at its argument `v`, the node built by `mk`; the children of
a constructor with positions are the table in its argument. -/
def conAt {X : Ty} : (S : Sig) → ((a : (Sig.den S).1) → ((Sig.den S).2 a → Val X) → Val X) →
    Val (S.conTy X) → Val X
  | .base _, mk, v => mk v fun p => Empty.elim p
  | .ext S _ none, mk, .inl v => conAt S (fun a k => mk (.inl a) k) v
  | .ext _ _ none, mk, .inr v => mk (.inr v) fun p => Empty.elim p
  | .ext S _ (some _), mk, .inl v => conAt S (fun a k => mk (.inl a) k) v
  | .ext _ a (some f), mk, .inr v =>
    let v' : Val a × (f.den → Val X) := v
    mk (.inr v'.1) v'.2

/-- The value of `mu S` that a constructor builds from its argument `v`: the node of the shape and
the children that `v` selects. -/
def Sig.node (S : Sig) (v : Val (S.conTy (.mu S))) : Val (.mu S) :=
  conAt S (fun a k => (WType.mk a k : Val (.mu S))) v

/-- The interpreter of D into costed trees, with `tk` at every evaluation step. -/
def Tm.interp {Γ : List Ty} : {τ : Ty} → Tm Γ τ → Env Γ → CTree (Val τ)
  | _, .var x, ρ => .ret (ρ _ x)
  | _, .lam b, ρ => .ret fun v => Tm.interp b (ρ.cons v)
  | _, .app f x, ρ => (Tm.interp f ρ).bind fun g => (Tm.interp x ρ).bind fun v => tk (g v)
  | _, .letE e b, ρ => (Tm.interp e ρ).bind fun v => tk (Tm.interp b (ρ.cons v))
  | _, .seq e b, ρ => (Tm.interp e ρ).bind fun _ => tk (Tm.interp b ρ)
  | _, .natLit n, _ => .ret n
  | _, .lit _ v, _ => .ret v
  | _, .prim p x, ρ => (Tm.interp x ρ).bind fun v => stepN tk (p.cost v) (.ret (p.apply v))
  | _, .pair x y, ρ => (Tm.interp x ρ).bind fun u => (Tm.interp y ρ).bind fun v => .ret (u, v)
  | _, .fst (a := a) (b := b) p, ρ => (Tm.interp p ρ).bind fun (v : Val a × Val b) => .ret v.1
  | _, .snd (a := a) (b := b) p, ρ => (Tm.interp p ρ).bind fun (v : Val a × Val b) => .ret v.2
  | _, .inl (a := a) (b := b) x, ρ =>
    (Tm.interp x ρ).bind fun v => .ret (Sum.inl v : Val a ⊕ Val b)
  | _, .inr (a := a) (b := b) x, ρ =>
    (Tm.interp x ρ).bind fun v => .ret (Sum.inr v : Val a ⊕ Val b)
  | _, .case (a := a) (b := b) s l r, ρ =>
    (Tm.interp s ρ).bind fun (v : Val a ⊕ Val b) =>
      tk (Sum.elim (fun x => Tm.interp l (ρ.cons x)) (fun y => Tm.interp r (ρ.cons y)) v)
  | _, .ite c t e, ρ =>
    (Tm.interp c ρ).bind fun (b : Bool) => tk (bif b then Tm.interp t ρ else Tm.interp e ρ)
  | _, .nil (a := a), _ => .ret ([] : List (Val a))
  | _, .cons (a := a) x xs, ρ =>
    (Tm.interp x ρ).bind fun v => (Tm.interp xs ρ).bind fun (l : List (Val a)) => .ret (v :: l)
  | _, .lcase (a := a) xs n c, ρ =>
    (Tm.interp xs ρ).bind fun (l : List (Val a)) =>
      tk (listCase l (Tm.interp n ρ) fun x l' =>
        Tm.interp c (((ρ.cons (τ := .list a) l').cons x)))
  | _, .foldl f i xs, ρ =>
    (Tm.interp f ρ).bind fun g => (Tm.interp i ρ).bind fun acc =>
      (Tm.interp xs ρ).bind fun l => foldT tk g acc l
  | _, .iter n f i, ρ =>
    (Tm.interp n ρ).bind fun (k : ℕ) => (Tm.interp f ρ).bind fun g =>
      (Tm.interp i ρ).bind fun acc => iterT tk g acc k
  | _, .sample f, _ => .sample f .ret
  | _, .get n f, _ => .get n f .ret
  | _, .set n f x, ρ => (Tm.interp x ρ).bind fun v => .set n f v (.ret (() : Unit))
  | _, .query d r x, ρ => (Tm.interp x ρ).bind fun v => .query d r v .ret
  | _, .fail, _ => .fail
  | _, .con (S := S) _ x, ρ =>
    (Tm.interp x ρ).bind fun v => .ret (conAt S (fun a k => (WType.mk a k : Val (.mu S))) v)
  | _, .fold _ g x, ρ =>
    (Tm.interp g ρ).bind fun gv => (Tm.interp x ρ).bind fun w => tk (foldW gv w)
  | _, .ptab (f := f) (B := B) ts, ρ =>
    tabDep f (fun j => Val.default (B j)) fun j => Tm.interp (ts j) ρ
  | _, .papp (B := B) t j, ρ =>
    (Tm.interp t ρ).bind fun (v : (j : _) → Val (B j)) => .ret (v j)
  | _, .spair (f := f) (B := B) j x, ρ =>
    (Tm.interp x ρ).bind fun v => .ret (⟨j, v⟩ : (j : f.den) × Val (B j))
  | _, .scase (f := f) (B := B) s ks, ρ =>
    (Tm.interp s ρ).bind fun (v : (j : f.den) × Val (B j)) =>
      tk (Tm.interp (ks v.1) (ρ.cons v.2))
  | _, .fcase (f := f) i ks, ρ => (Tm.interp i ρ).bind fun (j : f.den) => tk (Tm.interp (ks j) ρ)

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
  | .mu _, u, v => u = v
  | .pi _ B, u, v => ∀ j, ValRel (B j) (u j) (v j)
  | .sig _ B, u, v => ∃ e : u.1 = v.1, ValRel (B v.1) (e ▸ u.2) v.2

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
  | .mu _, _, _, _ => Iff.rfl
  | .pi f B, h, u, v => by
    change (j : f.den) → Val (B j) at u v
    show (∀ j, ValRel (B j) (u j) (v j)) ↔ u = v
    rw [funext_iff]
    exact forall_congr' fun j => ValRel.iff_eq_of_FO (B j) (h j) (u j) (v j)
  | .sig f B, h, u, v => by
    change (j : f.den) × Val (B j) at u v
    obtain ⟨i, x⟩ := u
    obtain ⟨j, y⟩ := v
    show (∃ e : i = j, ValRel (B j) (e ▸ x) y) ↔ _
    constructor
    · rintro ⟨rfl, hxy⟩
      rw [(ValRel.iff_eq_of_FO (B i) (h i) x y).1 hxy]
    · intro he
      obtain ⟨rfl, hx⟩ := Sigma.mk.inj_iff.1 he
      cases hx
      exact ⟨rfl, (ValRel.iff_eq_of_FO (B i) (h i) x x).2 rfl⟩

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

theorem tabFin_rel {X Y : Type} : ∀ (n : ℕ) {R : Fin n → X → Y → Prop} {g : Fin n → CTree X}
    {g' : Fin n → CTree Y}, (∀ i, CTree.Rel (R i) (g i) (g' i)) →
      CTree.Rel (fun h h' => ∀ i, R i (h i) (h' i)) (tabFin n g) (tabFin n g')
  | 0, _, _, _, _ => .ret fun i => i.elim0
  | n + 1, R, _, _, hg => (hg 0).bind fun _ _ hx =>
      (tabFin_rel n (R := fun i => R i.succ) fun i => hg i.succ).bind
      fun _ _ hh => .ret fun i => by
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa using hx
        · simpa using hh j

theorem tabTab_rel (r : FTy) (tr : ∀ {Y : Type}, (r.den → CTree Y) → CTree (r.den → Y))
    (htr : ∀ {X Y : Type} {R : r.den → X → Y → Prop} {g : r.den → CTree X}
      {g' : r.den → CTree Y}, (∀ a, CTree.Rel (R a) (g a) (g' a)) →
        CTree.Rel (fun h h' => ∀ a, R a (h a) (h' a)) (tr g) (tr g'))
    {X Y : Type} : ∀ (q : ℕ) {R : (Fin q → r.den) → X → Y → Prop}
      {g : (Fin q → r.den) → CTree X} {g' : (Fin q → r.den) → CTree Y},
      (∀ v, CTree.Rel (R v) (g v) (g' v)) →
      CTree.Rel (fun h h' => ∀ v, R v (h v) (h' v)) (tabTab r tr q g) (tabTab r tr q g')
  | 0, _, _, _, hg => (hg Fin.elim0).bind fun _ _ hx => .ret fun v => by
      have hv : v = Fin.elim0 := funext fun i => i.elim0
      subst hv
      exact hx
  | q + 1, R, _, _, hg =>
    (htr (R := fun a T T' => ∀ h, R (Fin.cons a h) (T h) (T' h)) fun a =>
      tabTab_rel r tr htr q (R := fun h => R (Fin.cons a h)) fun _ => hg _).bind fun _ _ hT =>
      .ret fun v => by
        have hv : R (Fin.cons (v 0) (Fin.tail v)) _ _ := hT (v 0) (Fin.tail v)
        rwa [Fin.cons_self_tail] at hv

/-- Tabulations of related trees are related pointwise, at a relation that may depend on the
element. -/
theorem tabT_rel : ∀ (f : FTy) {X Y : Type} {R : f.den → X → Y → Prop} {g : f.den → CTree X}
    {g' : f.den → CTree Y}, (∀ j, CTree.Rel (R j) (g j) (g' j)) →
      CTree.Rel (fun h h' => ∀ j, R j (h j) (h' j)) (tabT f g) (tabT f g')
  | .unit, _, _, _, _, _, hg => (hg ()).bind fun _ _ hx => .ret fun _ => hx
  | .bool, _, _, _, _, _, hg => (hg false).bind fun _ _ hx => (hg true).bind fun _ _ hy =>
      .ret fun b => by cases b; exact hx; exact hy
  | .word w, _, _, R, _, _, hg =>
    (tabFin_rel (2 ^ w) (R := fun i => R (BitVec.ofFin i)) fun _ => hg _).bind fun _ _ hh =>
      .ret fun v => hh v.toFin
  | .fin n, _, _, _, _, _, hg => tabFin_rel (n + 1) hg
  | .tab q r, _, _, _, _, _, hg => tabTab_rel r (fun g' => tabT r g') (fun h => tabT_rel r h) q hg

theorem sigmaAt_mk {I : Type} (dec : DecidableEq I) {X : I → Type} (d : (j : I) → X j)
    (j : I) (x : X j) : sigmaAt dec d ⟨j, x⟩ j = x := by
  unfold sigmaAt
  cases dec j j with
  | isTrue _ => rfl
  | isFalse h => exact absurd rfl h

/-- Dependent tabulations of related trees are related pointwise. -/
theorem tabDep_rel (f : FTy) {X Y : f.den → Type} {R : (j : f.den) → X j → Y j → Prop}
    {d : (j : f.den) → X j} {d' : (j : f.den) → Y j} {g : (j : f.den) → CTree (X j)}
    {g' : (j : f.den) → CTree (Y j)} (hg : ∀ j, CTree.Rel (R j) (g j) (g' j)) :
    CTree.Rel (fun h h' => ∀ j, R j (h j) (h' j)) (tabDep f d g) (tabDep f d' g') := by
  refine (tabT_rel f (R := fun j s s' => ∃ x y, s = ⟨j, x⟩ ∧ s' = ⟨j, y⟩ ∧ R j x y)
    fun j => (hg j).bind fun x y hxy => .ret ⟨x, y, rfl, rfl, hxy⟩).bind fun h h' hh => ?_
  refine .ret fun j => ?_
  obtain ⟨x, y, hx, hy, hxy⟩ := hh j
  simp only [hx, hy, sigmaAt_mk]
  exact hxy

/-- A tabulation over `Fin n` of leaves is the leaf of their values. -/
theorem tabFin_ret {X : Type} : ∀ (n : ℕ) (w : Fin n → X),
    tabFin n (fun i => .ret (w i)) = .ret w
  | 0, w => congrArg CTree.ret (funext fun i => i.elim0)
  | n + 1, w => by
    rw [tabFin, CTree.bind_ret, tabFin_ret n (fun i => w i.succ), CTree.bind_ret]
    exact congrArg CTree.ret (Fin.cons_self_tail w)

theorem tabTab_ret (r : FTy) (tr : ∀ {Y : Type}, (r.den → CTree Y) → CTree (r.den → Y))
    (htr : ∀ {Y : Type} (w : r.den → Y), tr (fun a => .ret (w a)) = .ret w) {X : Type} :
    ∀ (q : ℕ) (w : (Fin q → r.den) → X), tabTab r tr q (fun v => .ret (w v)) = .ret w
  | 0, w => by
    rw [tabTab, CTree.bind_ret]
    exact congrArg CTree.ret (funext fun v => by rw [show v = Fin.elim0 from funext fun i => i.elim0])
  | q + 1, w => by
    rw [tabTab]
    have hin : ∀ a : r.den, tabTab r tr q
        (fun h => CTree.ret (w (Fin.cons a h : Fin (q + 1) → r.den))) =
        CTree.ret fun h => w (Fin.cons a h : Fin (q + 1) → r.den) := fun a =>
      tabTab_ret r tr htr q _
    simp only [hin]
    rw [htr, CTree.bind_ret]
    exact congrArg CTree.ret (funext fun v => by simp only [Fin.cons_self_tail])

/-- A tabulation of leaves is the leaf of their values. -/
theorem tabT_ret : ∀ (f : FTy) {X : Type} (w : f.den → X), tabT f (fun j => .ret (w j)) = .ret w
  | .unit, _, _ => rfl
  | .bool, _, w => congrArg CTree.ret (funext fun b => by cases b <;> rfl)
  | .word n, _, w => by
    rw [tabT, tabFin_ret (2 ^ n) (fun i => w (BitVec.ofFin i)), CTree.bind_ret]
    rfl
  | .fin n, _, w => tabFin_ret (n + 1) w
  | .tab q r, _, w => tabTab_ret r (fun g' => tabT r g') (fun w' => tabT_ret r w') q w

/-- A dependent tabulation of leaves is the leaf of their values. -/
theorem tabDep_ret (f : FTy) {X : f.den → Type} (d : (j : f.den) → X j) (w : (j : f.den) → X j) :
    tabDep f d (fun j => .ret (w j)) = .ret w := by
  rw [tabDep]
  simp only [CTree.bind_ret]
  rw [tabT_ret f (fun j => (⟨j, w j⟩ : (j : f.den) × X j)), CTree.bind_ret]
  exact congrArg CTree.ret (funext fun j => sigmaAt_mk (FTy.decEq f) d j (w j))

/-- A constructor at related arguments builds equal nodes, the children of a first-order
signature being equal. -/
theorem conAt_rel {X : Ty} (hX : ∀ x y, ValRel X x y → x = y) : ∀ (S : Sig), S.FO →
    ∀ (mk : (a : (Sig.den S).1) → ((Sig.den S).2 a → Val X) → Val X) {u v : Val (S.conTy X)},
      ValRel (S.conTy X) u v → conAt S mk u = conAt S mk v
  | .base a, hS, mk, u, v, huv => by
    have he : u = v := (ValRel.iff_eq_of_FO a hS u v).1 huv
    subst he
    rfl
  | .ext S a none, hS, mk, u, v, huv => by
    have h' : Sum.LiftRel (ValRel (S.conTy X)) (ValRel a) u v := huv
    cases h' with
    | inl h => exact conAt_rel hX S hS.1 _ h
    | inr h =>
      have he := (ValRel.iff_eq_of_FO a hS.2 _ _).1 h
      subst he
      rfl
  | .ext S a (some f), hS, mk, u, v, huv => by
    have h' : Sum.LiftRel (ValRel (S.conTy X)) (ValRel (.prod a (.pi f fun _ => X))) u v := huv
    cases h' with
    | inl h => exact conAt_rel hX S hS.1 _ h
    | @inr x y h =>
      have he : x.1 = y.1 := (ValRel.iff_eq_of_FO a hS.2 _ _).1 h.1
      have hk : x.2 = y.2 := funext fun j => hX _ _ (h.2 j)
      show mk (.inr x.1) x.2 = mk (.inr y.1) y.2
      rw [he, hk]

/-- A step of an eliminator at related step functions and related recursive results gives
related trees, the fields of a first-order signature being related to themselves. -/
theorem stepAt_rel {X c : Ty} (hX : ∀ x : Val X, ValRel X x x) : ∀ (S : Sig), S.FO →
    ∀ {g g' : Val (S.stepsTy X c)}, ValRel _ g g' → ∀ (a : (Sig.den S).1)
      (kids : (Sig.den S).2 a → Val X) {rec rec' : (Sig.den S).2 a → CTree (Val c)},
      (∀ j, CTree.Rel (ValRel c) (rec j) (rec' j)) →
        CTree.Rel (ValRel c) (stepAt S g a kids rec) (stepAt S g' a kids rec')
  | .base a, hS, _, _, hg, x, _, _, _, _ => hg x x ((ValRel.iff_eq_of_FO a hS x x).2 rfl)
  | .ext S _ _, hS, _, _, hg, .inl x, kids, _, _, hr => stepAt_rel hX S hS.1 hg.1 x kids hr
  | .ext _ a none, hS, _, _, hg, .inr x, _, _, _, _ =>
    hg.2 x x ((ValRel.iff_eq_of_FO a hS.2 x x).2 rfl)
  | .ext _ a (some _), hS, _, _, hg, .inr x, kids, _, _, hr =>
    hg.2 _ _ ⟨(ValRel.iff_eq_of_FO a hS.2 x x).2 rfl,
      fun j => hX (kids j), fun j j' hj => by subst hj; exact hr j⟩

/-- The eliminator at related step functions: the evaluator and the denotation give related
trees at every value. -/
theorem foldW_rel {S : Sig} {c : Ty} (hS : S.FO) {g g' : Val (S.stepsTy (.mu S) c)}
    (hg : ValRel _ g g') (w : WType (Sig.den S).2) :
    CTree.Rel (ValRel c) (foldW g w) (foldW g' w) := by
  induction w with
  | mk a kids ih => exact stepAt_rel (X := .mu S) (fun _ => rfl) S hS hg a kids ih

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
  | fail => intro ρ δ h; exact .fail
  | @con _ S hS x ih =>
    intro ρ δ h
    exact (ih h).bind fun u v huv => .ret (conAt_rel (X := .mu S) (fun _ _ e => e) S hS _ huv)
  | @fold _ S c hS g x ihg ihx =>
    intro ρ δ h
    exact (ihg h).bind fun gv gv' hg => (ihx h).bind fun w w' hw => by
      change w = w' at hw
      subst hw
      exact .tick (foldW_rel hS hg w)
  | @ptab _ f B ts ih =>
    intro ρ δ h
    exact tabDep_rel f fun j => ih j h
  | papp t j ih => intro ρ δ h; exact (ih h).bind fun u v huv => .ret (huv j)
  | spair j x ih => intro ρ δ h; exact (ih h).bind fun u v huv => .ret ⟨rfl, huv⟩
  | @scase _ f B c s ks ihs ihks =>
    intro ρ δ h
    refine (ihs h).bind fun u v huv => ?_
    change (j : f.den) × Val (B j) at u v
    obtain ⟨i, x⟩ := u
    obtain ⟨j, y⟩ := v
    change ∃ e : i = j, ValRel (B j) (e ▸ x) y at huv
    obtain ⟨rfl, hxy⟩ := huv
    exact .tick (ihks i (h.cons hxy))
  | fcase i ks ihi ihks =>
    intro ρ δ h
    exact (ihi h).bind fun u v huv => by
      change u = v at huv
      subst huv
      exact .tick (ihks u h)

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
  all_goals (intro Δ r ρ; simp only [Tm.rename, Tm.interp, *, Env.comp_lift]; try rfl)

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
