/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Complexity.D.Semantics
public import CatCryptCore.Container.PolyRGraph

/-!
# D in the reflexive-graph model and its polynomial model

This module interprets the deep language D in the reflexive-graph category with families of
`CatCryptCore.Container.RGraphCwF` (Atkey, Ghani and Johann) and in the polynomial model over it,
`CatCryptCore.Container.PolyRGraph`, and proves the abstraction theorem of Reynolds for D with
cost.

D has no type variables; its parameters are the finite ground types `FTy`. A base relation
(`BRel`) is a relation on the values of each finite ground type. It extends to every type of D
(`Ty.relB`): the base relation at `base f`, equality at `nat`, componentwise at products, sums,
lists and dependent products and sums, the relator `Container.WLift` (`Container.IWLift`) of the
relation of the fields at an inductive type (family), and at a function type the exact lifting
`CTree.Lift` of trees: related arguments go to trees with the same effect nodes and the same
ticks, at related leaves. Related trees have equal cost (`CTree.Lift.cost_eq`). When the base
relation is equality, the relation at every type is equality (`Ty.relB_iff_eq`): this is the
identity extension condition of the reflexive-graph model.

A term respects a base relation (`Tm.RespB`) when its literals are related to themselves, its
primitive operations send related arguments to related results at equal cost (`Prim.RespB`), the
values it branches on (`ite`, `fcase`) and the values it writes or sends as a query are related
only when equal, the values it samples, reads or receives are related to themselves, and the
recursive positions of the signatures it folds over are related only when equal (`Sig.PosEq`).
Every term respects a base relation that is equality (`Tm.respB_of_iff_eq`).

The abstraction theorem (`Tm.eval_lift`) is proved by structural recursion on the term: in
environments related by a base relation that the term respects, the evaluator gives trees related
by the exact lifting, so the values are related and the costs are equal (`Tm.abstraction_cost`).

Over a reflexive graph `G` with a base relation over each edge that is equality over the
reflexive edges (`BaseRG`), a type of D is a type of the reflexive-graph model with the values as
the set at every vertex (`Ty.rg`), an environment of a context is one (`envRG`), and a computation
is one (`Ty.rgC`, the trees with their exact lifting). A term that respects the base relations over
every edge is a term of the computation type in the context extension by the environment
(`Tm.rg`), and the abstraction theorem of the model (`RGraphCwF.Tm.abstraction`) at it is the
abstraction theorem of D with cost (`Tm.rg_abstraction`). Over the walking edge
(`PolyRGraph.walk`), one base relation gives a `BaseRG` (`BaseRG.walk`).

In the polynomial model, a computation of type `τ` (`Ty.polyC`) has the trees as shapes and the
clock ticks of a tree, `Fin t.cost`, as positions, related over an edge when they have the same
index; the context of a D-context (`ctxP`) has the environments as shapes and the clock `ℕ` of the
context as positions. A respecting term is a term of the polynomial model (`Tm.poly`) whose
backward map sends each tick of its tree to the same tick of the clock. Over an edge, related
trees have the same number of ticks and the relation of ticks is the graph of the identity
bijection (`Ty.polyC_pos_rel_iff`).

## Main definitions

* `BRel`, `Ty.relB`, `Sig.fldRelB`, `ISig.fldRelB`, `EnvRelB` — base relations and their
  extension to the types of D;
* `CTree.Lift` — the exact lifting of a relation to trees;
* `Prim.RespB`, `Sig.PosEq`, `Tm.RespB` — respect of a base relation;
* `BaseRG`, `BaseRG.walk`, `Ty.rg`, `envRG`, `Ty.rgC`, `Tm.rg` — the interpretation in the
  reflexive-graph model;
* `ctxP`, `Ty.polyC`, `Tm.poly` — the interpretation in the polynomial model.

## Main results

* `CTree.Lift.cost_eq`, `CTree.Lift.iff_eq` — related trees have equal cost; the lifting of
  equality is equality;
* `Ty.relB_iff_eq` — identity extension;
* `Tm.respB_of_iff_eq` — every term respects equality;
* `Tm.eval_lift`, `Tm.abstraction_cost` — the abstraction theorem of D with cost;
* `Tm.rg_abstraction` — the abstraction theorem of the reflexive-graph model at a term of D;
* `Ty.polyC_pos_rel_iff` — the positions of a computation in the polynomial model are its ticks,
  related over an edge by the identity bijection.

## References

* J. C. Reynolds, *Types, abstraction and parametric polymorphism*, IFIP Congress 1983;
* R. Atkey, N. Ghani, P. Johann, *A relationally parametric model of dependent type theory*,
  POPL 2014;
* S. Moss, T. von Glehn, *Dialectica models of type theory*, LICS 2018.

Search words: abstraction theorem, free theorem, relational parametricity, logical relation,
identity extension, reflexive graph, cost, representation independence, non-interference.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Complexity.D

open CatCrypt.Container

/-! ## The exact lifting of a relation to trees -/

namespace CTree

/-- The exact lifting of `R` to trees: the effect nodes and the ticks agree, the leaves are
related. -/
inductive Lift {α β : Type} (R : α → β → Prop) : CTree α → CTree β → Prop where
  | ret {a : α} {b : β} : R a b → Lift R (ret a) (ret b)
  | tick {t : CTree α} {m : CTree β} : Lift R t m → Lift R (tick t) (tick m)
  | sample (f : FTy) {k : f.den → CTree α} {k' : f.den → CTree β} :
      (∀ x, Lift R (k x) (k' x)) → Lift R (sample f k) (sample f k')
  | get (n : ℕ) (f : FTy) {k : f.den → CTree α} {k' : f.den → CTree β} :
      (∀ x, Lift R (k x) (k' x)) → Lift R (get n f k) (get n f k')
  | set (n : ℕ) (f : FTy) (v : f.den) {k : CTree α} {k' : CTree β} :
      Lift R k k' → Lift R (set n f v k) (set n f v k')
  | query (d r : FTy) (x : d.den) {k : r.den → CTree α} {k' : r.den → CTree β} :
      (∀ y, Lift R (k y) (k' y)) → Lift R (query d r x k) (query d r x k')
  | fail : Lift R fail fail

variable {α β α' β' : Type}

/-- The exact lifting is preserved by `bind` at related continuations. -/
theorem Lift.bind {R : α → β → Prop} {S : α' → β' → Prop} {t : CTree α} {m : CTree β}
    (h : Lift R t m) {g : α → CTree α'} {g' : β → CTree β'}
    (hg : ∀ a b, R a b → Lift S (g a) (g' b)) : Lift S (t.bind g) (m.bind g') := by
  induction h with
  | ret hab => exact hg _ _ hab
  | tick _ ih => exact .tick ih
  | sample f _ ih => exact .sample f ih
  | get n f _ ih => exact .get n f ih
  | set n f v _ ih => exact .set n f v ih
  | query d r x _ ih => exact .query d r x ih
  | fail => exact .fail

/-- Trees related by the exact lifting have equal cost. -/
theorem Lift.cost_eq {R : α → β → Prop} {t : CTree α} {m : CTree β} (h : Lift R t m) :
    t.cost = m.cost := by
  induction h with
  | ret _ => rfl
  | tick _ ih => simp only [cost, ih]
  | sample f _ ih => simp only [cost, ih]
  | get n f _ ih => simp only [cost, ih]
  | set n f v _ ih => simp only [cost, ih]
  | query d r x _ ih => simp only [cost, ih]
  | fail => rfl

/-- The exact lifting of a relation that is equality is equality. -/
theorem Lift.iff_eq {R : α → α → Prop} (hR : ∀ a b, R a b ↔ a = b) (t m : CTree α) :
    Lift R t m ↔ t = m := by
  constructor
  · intro h
    induction h with
    | ret hab => exact congrArg CTree.ret ((hR _ _).1 hab)
    | tick _ ih => exact congrArg CTree.tick ih
    | sample f _ ih => exact congrArg (CTree.sample f) (funext ih)
    | get n f _ ih => exact congrArg (CTree.get n f) (funext ih)
    | set n f v _ ih => exact congrArg (CTree.set n f v) ih
    | query d r x _ ih => exact congrArg (CTree.query d r x) (funext ih)
    | fail => rfl
  · rintro rfl
    induction t with
    | ret a => exact .ret ((hR a a).2 rfl)
    | tick _ ih => exact .tick ih
    | sample f _ ih => exact .sample f ih
    | get n f _ ih => exact .get n f ih
    | set n f v _ ih => exact .set n f v ih
    | query d r x _ ih => exact .query d r x ih
    | fail => exact .fail

end CTree

/-- The same number of ticks in front of trees related by the exact lifting. -/
theorem stepN_lift {α β : Type} {R : α → β → Prop} {t : CTree α} {m : CTree β}
    (h : CTree.Lift R t m) (n : ℕ) :
    CTree.Lift R (stepN CTree.tick n t) (stepN CTree.tick n m) := by
  induction n with
  | zero => exact h
  | succ n ih => exact .tick ih

/-! ## Base relations and their extension to the types of D -/

/-- A base relation: a relation on the values of each finite ground type. -/
abbrev BRel : Type :=(f : FTy) → f.den → f.den → Prop

mutual

/-- The relation of a type of D at a base relation: the base relation at `base f`, equality at
`nat`, componentwise at products, sums, lists, dependent products and sums, the relator of the
fields at inductive types, and the exact lifting `CTree.Lift` at function types. -/
def Ty.relB (R : BRel) : (τ : Ty) → Val τ → Val τ → Prop
  | .base f, u, v => R f u v
  | .nat, u, v => u = v
  | .prod a b, u, v => Ty.relB R a u.1 v.1 ∧ Ty.relB R b u.2 v.2
  | .sum a b, u, v => Sum.LiftRel (Ty.relB R a) (Ty.relB R b) u v
  | .arr a b, f, g => ∀ x y, Ty.relB R a x y → CTree.Lift (Ty.relB R b) (f x) (g y)
  | .list a, u, v => List.Forall₂ (Ty.relB R a) u v
  | .mu S, u, v => Container.WLift (P := S.Pos) (Sig.fldRelB R S) u v
  | .pi _ B, u, v => ∀ j, Ty.relB R (B j) (u j) (v j)
  | .sig _ B, u, v => ∃ e : u.1 = v.1, Ty.relB R (B v.1) (e ▸ u.2) v.2
  | .imu _ S _, u, v => Container.IWLift (C := fun j => (S j).Ctor) (P := fun j c => (S j).Pos c)
      (nx := fun j c p => (S j).nx c p) (fun j c x y => ISig.fldRelB R (S j) c x y) u v

/-- The relation at the fields of the constructors of a signature. -/
def Sig.fldRelB (R : BRel) : (S : Sig) → (c : S.Ctor) → S.Fld c → S.Fld c → Prop
  | .base a, _, x, y => Ty.relB R a x y
  | .ext S _ _, .inl c, x, y => Sig.fldRelB R S c x y
  | .ext _ a _, .inr _, x, y => Ty.relB R a x y

/-- The relation at the fields of the constructors of an indexed signature. -/
def ISig.fldRelB (R : BRel) {f : FTy} : (S : ISig f) → (c : S.Ctor) → S.Fld c → S.Fld c → Prop
  | .base a => fun _ x y => Ty.relB R a x y
  | .ext S a _ _ => fun c => match c with
    | .inl c => ISig.fldRelB R S c
    | .inr _ => fun x y => Ty.relB R a x y

end

/-- Environments related pointwise at a base relation. -/
def EnvRelB (R : BRel) {Γ : List Ty} (ρ δ : Env Γ) : Prop :=
  ∀ τ (x : Var Γ τ), Ty.relB R τ (ρ τ x) (δ τ x)

/-- Related environments extended by related values are related. -/
theorem EnvRelB.cons {R : BRel} {Γ : List Ty} {τ : Ty} {ρ δ : Env Γ} (h : EnvRelB R ρ δ)
    {u v : Val τ} (huv : Ty.relB R τ u v) : EnvRelB R (ρ.cons u) (δ.cons v) := by
  intro σ x
  cases x with
  | here => exact huv
  | there y => exact h σ y

section IdExt

variable {R : BRel}

mutual

/-- Identity extension: at a base relation that is equality, the relation of every type of D is
equality. -/
theorem Ty.relB_iff_eq (hR : ∀ f a b, R f a b ↔ a = b) :
    (τ : Ty) → ∀ u v : Val τ, Ty.relB R τ u v ↔ u = v
  | .base f, u, v => hR f u v
  | .nat, _, _ => Iff.rfl
  | .prod a b, u, v => by
    have ha := Ty.relB_iff_eq hR a
    have hb := Ty.relB_iff_eq hR b
    change Ty.relB R a u.1 v.1 ∧ Ty.relB R b u.2 v.2 ↔ u = v
    rw [ha, hb]
    exact Prod.ext_iff.symm
  | .sum a b, u, v => by
    have ha := Ty.relB_iff_eq hR a
    have hb := Ty.relB_iff_eq hR b
    change Val a ⊕ Val b at u v
    change Sum.LiftRel (Ty.relB R a) (Ty.relB R b) u v ↔ u = v
    constructor
    · rintro (⟨hx⟩ | ⟨hy⟩)
      · exact congrArg Sum.inl ((ha _ _).1 hx)
      · exact congrArg Sum.inr ((hb _ _).1 hy)
    · rintro rfl
      cases u with
      | inl x => exact .inl ((ha x x).2 rfl)
      | inr y => exact .inr ((hb y y).2 rfl)
  | .arr a b, f, g => by
    have ha := Ty.relB_iff_eq hR a
    have hb := Ty.relB_iff_eq hR b
    change (∀ x y, Ty.relB R a x y → CTree.Lift (Ty.relB R b) (f x) (g y)) ↔ f = g
    constructor
    · intro h
      funext x
      exact (CTree.Lift.iff_eq hb _ _).1 (h x x ((ha x x).2 rfl))
    · rintro rfl x y hxy
      obtain rfl := (ha x y).1 hxy
      exact (CTree.Lift.iff_eq hb _ _).2 rfl
  | .list a, u, v => by
    have ha := Ty.relB_iff_eq hR a
    change List.Forall₂ (Ty.relB R a) u v ↔ u = v
    have hab : Ty.relB R a = (· = ·) := funext fun x => funext fun y => propext (ha x y)
    rw [hab, List.forall₂_eq_eq_eq]
    exact Iff.rfl
  | .mu S, u, v => Container.WLift.iff_eq (fun c x y => Sig.fldRelB_iff_eq hR S c x y) u v
  | .imu _ S _, u, v =>
    Container.IWLift.iff_eq (fun j c x y => ISig.fldRelB_iff_eq hR (S j) c x y) u v
  | .pi f B, u, v => by
    change (j : f.den) → Val (B j) at u v
    change (∀ j, Ty.relB R (B j) (u j) (v j)) ↔ u = v
    rw [funext_iff]
    exact forall_congr' fun j => Ty.relB_iff_eq hR (B j) (u j) (v j)
  | .sig f B, u, v => by
    change (j : f.den) × Val (B j) at u v
    obtain ⟨i, x⟩ := u
    obtain ⟨j, y⟩ := v
    change (∃ e : i = j, Ty.relB R (B j) (e ▸ x) y) ↔ _
    constructor
    · rintro ⟨rfl, hxy⟩
      rw [(Ty.relB_iff_eq hR (B i) x y).1 hxy]
    · intro he
      obtain ⟨rfl, hx⟩ := Sigma.mk.inj_iff.1 he
      cases hx
      exact ⟨rfl, (Ty.relB_iff_eq hR (B i) x x).2 rfl⟩

/-- Identity extension at the fields of a signature. -/
theorem Sig.fldRelB_iff_eq (hR : ∀ f a b, R f a b ↔ a = b) :
    (S : Sig) → ∀ (c : S.Ctor) (x y : S.Fld c), Sig.fldRelB R S c x y ↔ x = y
  | .base a, _, x, y => Ty.relB_iff_eq hR a x y
  | .ext S _ _, .inl c, x, y => Sig.fldRelB_iff_eq hR S c x y
  | .ext _ a _, .inr _, x, y => Ty.relB_iff_eq hR a x y

/-- Identity extension at the fields of an indexed signature. -/
theorem ISig.fldRelB_iff_eq (hR : ∀ f a b, R f a b ↔ a = b) {f : FTy} :
    (S : ISig f) → ∀ (c : S.Ctor) (x y : S.Fld c), ISig.fldRelB R S c x y ↔ x = y
  | .base a, _, x, y => Ty.relB_iff_eq hR a x y
  | .ext S a _ _, c, x, y => by
    cases c with
    | inl c => exact ISig.fldRelB_iff_eq hR S c x y
    | inr _ => exact Ty.relB_iff_eq hR a x y

end

end IdExt

/-! ## Respect of a base relation -/

/-- A primitive operation respects a base relation when it sends related arguments to related
results at equal cost. -/
def Prim.RespB (R : BRel) {a b : Ty} (p : Prim a b) : Prop :=
  ∀ u v, Ty.relB R a u v → Ty.relB R b (p.apply u) (p.apply v) ∧ p.cost u = p.cost v

/-- The recursive positions of a signature are discrete at a base relation: at each constructor
with positions `some f`, the base relation at `f` relates only equal elements. -/
def Sig.PosEq (R : BRel) : Sig → Prop
  | .base _ => True
  | .ext S _ none => Sig.PosEq R S
  | .ext S _ (some f) => (∀ j j', R f j j' → j = j') ∧ Sig.PosEq R S

/-- The recursive positions of every signature are discrete at a base relation that is
equality. -/
theorem Sig.posEq_of_iff_eq {R : BRel} (hR : ∀ f a b, R f a b ↔ a = b) : (S : Sig) → S.PosEq R
  | .base _ => trivial
  | .ext S _ none => Sig.posEq_of_iff_eq hR S
  | .ext S _ (some f) => ⟨fun j j' => (hR f j j').1, Sig.posEq_of_iff_eq hR S⟩

/-- A term respects a base relation: its literals are related to themselves, its primitive
operations respect the relation, the values it branches on, writes or sends as a query are related
only when equal, and the values it samples, reads or receives are related to themselves. -/
def Tm.RespB (R : BRel) : {Γ : List Ty} → {τ : Ty} → Tm Γ τ → Prop
  | _, _, .var _ => True
  | _, _, .lam b => b.RespB R
  | _, _, .app f x => f.RespB R ∧ x.RespB R
  | _, _, .letE e b => e.RespB R ∧ b.RespB R
  | _, _, .seq e b => e.RespB R ∧ b.RespB R
  | _, _, .natLit _ => True
  | _, _, .lit f v => R f v v
  | _, _, .prim p x => p.RespB R ∧ x.RespB R
  | _, _, .pair x y => x.RespB R ∧ y.RespB R
  | _, _, .fst p => p.RespB R
  | _, _, .snd p => p.RespB R
  | _, _, .inl x => x.RespB R
  | _, _, .inr x => x.RespB R
  | _, _, .case s l r => s.RespB R ∧ l.RespB R ∧ r.RespB R
  | _, _, .ite c t e => (∀ b b', R .bool b b' → b = b') ∧ c.RespB R ∧ t.RespB R ∧ e.RespB R
  | _, _, .nil => True
  | _, _, .cons x xs => x.RespB R ∧ xs.RespB R
  | _, _, .lcase xs n c => xs.RespB R ∧ n.RespB R ∧ c.RespB R
  | _, _, .foldl f i xs => f.RespB R ∧ i.RespB R ∧ xs.RespB R
  | _, _, .iter n f i => n.RespB R ∧ f.RespB R ∧ i.RespB R
  | _, _, .sample f => ∀ x, R f x x
  | _, _, .get _ f => ∀ x, R f x x
  | _, _, .set _ f x => (∀ v v', R f v v' → v = v') ∧ R .unit () () ∧ x.RespB R
  | _, _, .query d r x => (∀ v v', R d v v' → v = v') ∧ (∀ y, R r y y) ∧ x.RespB R
  | _, _, .fail => True
  | _, _, .con x => x.RespB R
  | _, _, .fold (S := S) g x => S.PosEq R ∧ g.RespB R ∧ x.RespB R
  | _, _, .icon x => x.RespB R
  | _, _, .ifold (c := _) g x => g.RespB R ∧ x.RespB R
  | _, _, .ptab ts => ∀ j, (ts j).RespB R
  | _, _, .papp (B := _) t _ => t.RespB R
  | _, _, .spair _ x => x.RespB R
  | _, _, .scase s ks => s.RespB R ∧ ∀ j, (ks j).RespB R
  | _, _, .fcase (f := f) i ks => (∀ j j', R f j j' → j = j') ∧ i.RespB R ∧ ∀ j, (ks j).RespB R

/-- Every primitive operation respects a base relation that is equality. -/
theorem Prim.respB_of_iff_eq {R : BRel} (hR : ∀ f a b, R f a b ↔ a = b) {a b : Ty}
    (p : Prim a b) : p.RespB R := by
  intro u v huv
  obtain rfl := (Ty.relB_iff_eq hR a u v).1 huv
  exact ⟨(Ty.relB_iff_eq hR b _ _).2 rfl, rfl⟩

/-- Every term respects a base relation that is equality. -/
theorem Tm.respB_of_iff_eq {R : BRel} (hR : ∀ f a b, R f a b ↔ a = b) {Γ : List Ty} {τ : Ty}
    (t : Tm Γ τ) : t.RespB R := by
  have hrefl : ∀ f a, R f a a := fun f a => (hR f a a).2 rfl
  have heq : ∀ f a b, R f a b → a = b := fun f a b => (hR f a b).1
  induction t with
  | prim p x ih => exact ⟨p.respB_of_iff_eq hR, ih⟩
  | lit f v => exact hrefl f v
  | ite c t e ihc iht ihe => exact ⟨heq _, ihc, iht, ihe⟩
  | sample f => exact hrefl f
  | get n f => exact hrefl f
  | set n f x ih => exact ⟨heq f, hrefl _ _, ih⟩
  | query d r x ih => exact ⟨heq d, hrefl r, ih⟩
  | fcase i ks ihi ihks => exact ⟨heq _, ihi, ihks⟩
  | @fold _ S c g x ihg ihx => exact ⟨Sig.posEq_of_iff_eq hR S, ihg, ihx⟩
  | _ => simp_all [Tm.RespB]

/-! ## The abstraction theorem -/

section Fundamental

variable {R : BRel}

/-- A left fold at related step functions, lists and accumulators gives trees related by the
exact lifting. -/
theorem foldT_lift {a c : Ty} {g g' : Val (.arr (.prod c a) c)} (hg : Ty.relB R _ g g')
    {l l' : List (Val a)} (hl : List.Forall₂ (Ty.relB R a) l l') :
    ∀ {acc acc' : Val c}, Ty.relB R c acc acc' →
      CTree.Lift (Ty.relB R c) (foldT CTree.tick g acc l) (foldT CTree.tick g' acc' l') := by
  induction hl with
  | nil => intro acc acc' h; exact .ret h
  | cons hx _ ih =>
    intro acc acc' h
    exact (CTree.Lift.tick (hg _ _ ⟨h, hx⟩)).bind fun _ _ hc => ih hc

/-- An iteration at related step functions and accumulators gives trees related by the exact
lifting. -/
theorem iterT_lift {c : Ty} {g g' : Val (.arr c c)} (hg : Ty.relB R _ g g') (n : ℕ) :
    ∀ {acc acc' : Val c}, Ty.relB R c acc acc' →
      CTree.Lift (Ty.relB R c) (iterT CTree.tick g acc n) (iterT CTree.tick g' acc' n) := by
  induction n with
  | zero => intro acc acc' h; exact .ret h
  | succ n ih =>
    intro acc acc' h
    exact (CTree.Lift.tick (hg _ _ h)).bind fun _ _ hc => ih hc

/-- Tabulations over `Fin n` of related trees are related pointwise. -/
theorem tabFin_lift {X Y : Type} : ∀ (n : ℕ) {Q : Fin n → X → Y → Prop} {g : Fin n → CTree X}
    {g' : Fin n → CTree Y}, (∀ i, CTree.Lift (Q i) (g i) (g' i)) →
      CTree.Lift (fun h h' => ∀ i, Q i (h i) (h' i)) (tabFin n g) (tabFin n g')
  | 0, _, _, _, _ => .ret fun i => i.elim0
  | n + 1, Q, _, _, hg => (hg 0).bind fun _ _ hx =>
      (tabFin_lift n (Q := fun i => Q i.succ) fun i => hg i.succ).bind
      fun _ _ hh => .ret fun i => by
        refine Fin.cases ?_ (fun j => ?_) i
        · simpa using hx
        · simpa using hh j

/-- Tabulations over `Fin q → r.den` of related trees are related pointwise. -/
theorem tabTab_lift (r : FTy) (tr : ∀ {Y : Type}, (r.den → CTree Y) → CTree (r.den → Y))
    (htr : ∀ {X Y : Type} {Q : r.den → X → Y → Prop} {g : r.den → CTree X}
      {g' : r.den → CTree Y}, (∀ a, CTree.Lift (Q a) (g a) (g' a)) →
        CTree.Lift (fun h h' => ∀ a, Q a (h a) (h' a)) (tr g) (tr g'))
    {X Y : Type} : ∀ (q : ℕ) {Q : (Fin q → r.den) → X → Y → Prop}
      {g : (Fin q → r.den) → CTree X} {g' : (Fin q → r.den) → CTree Y},
      (∀ v, CTree.Lift (Q v) (g v) (g' v)) →
      CTree.Lift (fun h h' => ∀ v, Q v (h v) (h' v)) (tabTab r tr q g) (tabTab r tr q g')
  | 0, _, _, _, hg => (hg Fin.elim0).bind fun _ _ hx => .ret fun v => by
      have hv : v = Fin.elim0 := funext fun i => i.elim0
      subst hv
      exact hx
  | q + 1, Q, _, _, hg =>
    (htr (Q := fun a T T' => ∀ h, Q (Fin.cons a h) (T h) (T' h)) fun a =>
      tabTab_lift r tr htr q (Q := fun h => Q (Fin.cons a h)) fun _ => hg _).bind fun _ _ hT =>
      .ret fun v => by
        have hv : Q (Fin.cons (v 0) (Fin.tail v)) _ _ := hT (v 0) (Fin.tail v)
        rwa [Fin.cons_self_tail] at hv

/-- Tabulations of trees related by the exact lifting are related pointwise. -/
theorem tabT_lift : ∀ (f : FTy) {X Y : Type} {Q : f.den → X → Y → Prop} {g : f.den → CTree X}
    {g' : f.den → CTree Y}, (∀ j, CTree.Lift (Q j) (g j) (g' j)) →
      CTree.Lift (fun h h' => ∀ j, Q j (h j) (h' j)) (tabT f g) (tabT f g')
  | .unit, _, _, _, _, _, hg => (hg ()).bind fun _ _ hx => .ret fun _ => hx
  | .bool, _, _, _, _, _, hg => (hg false).bind fun _ _ hx => (hg true).bind fun _ _ hy =>
      .ret fun b => by
        cases b with
        | false => exact hx
        | true => exact hy
  | .word w, _, _, Q, _, _, hg =>
    (tabFin_lift (2 ^ w) (Q := fun i => Q (BitVec.ofFin i)) fun _ => hg _).bind fun _ _ hh =>
      .ret fun v => hh v.toFin
  | .fin n, _, _, _, _, _, hg => tabFin_lift (n + 1) hg
  | .tab q r, _, _, _, _, _, hg =>
    tabTab_lift r (fun g' => tabT r g') (fun h => tabT_lift r h) q hg

/-- Dependent tabulations of trees related by the exact lifting are related pointwise. -/
theorem tabDep_lift (f : FTy) {X Y : f.den → Type} {Q : (j : f.den) → X j → Y j → Prop}
    {d : (j : f.den) → X j} {d' : (j : f.den) → Y j} {g : (j : f.den) → CTree (X j)}
    {g' : (j : f.den) → CTree (Y j)} (hg : ∀ j, CTree.Lift (Q j) (g j) (g' j)) :
    CTree.Lift (fun h h' => ∀ j, Q j (h j) (h' j)) (tabDep f d g) (tabDep f d' g') := by
  refine (tabT_lift f (Q := fun j s s' => ∃ x y, s = ⟨j, x⟩ ∧ s' = ⟨j, y⟩ ∧ Q j x y)
    fun j => (hg j).bind fun x y hxy => .ret ⟨x, y, rfl, rfl, hxy⟩).bind fun h h' hh => ?_
  refine .ret fun j => ?_
  obtain ⟨x, y, hx, hy, hxy⟩ := hh j
  simp only [hx, hy, sigmaAt_mk]
  exact hxy

/-- A constructor at arguments related at a base relation builds related nodes. -/
theorem conAt_relB {X : Ty} {Q : Val X → Val X → Prop} : ∀ (S : Sig)
    (mk mk' : (a : (Sig.den S).A) → ((Sig.den S).B a → Val X) → Val X),
    (∀ (c : S.Ctor) (x y : S.Fld c) (k k' : S.Pos c → Val X), Sig.fldRelB R S c x y →
      (∀ p, Ty.relB R X (k p) (k' p)) → Q (mk ⟨c, x⟩ k) (mk' ⟨c, y⟩ k')) →
    ∀ {u v : Val (S.conTy X)}, Ty.relB R (S.conTy X) u v → Q (conAt S mk u) (conAt S mk' v)
  | .base _, _, _, hmk, _, _, huv => hmk () _ _ _ _ huv fun p => p.elim
  | .ext S a none, mk, mk', hmk, u, v, huv => by
    have h' : Sum.LiftRel (Ty.relB R (S.conTy X)) (Ty.relB R a) u v := huv
    cases h' with
    | inl h =>
      exact conAt_relB S (fun a k => mk ⟨.inl a.1, a.2⟩ k) (fun a k => mk' ⟨.inl a.1, a.2⟩ k)
        (fun c x y k k' hxy hk => hmk (.inl c) x y k k' hxy hk) h
    | inr h => exact hmk (.inr ()) _ _ _ _ h fun p => p.elim
  | .ext S a (some f), mk, mk', hmk, u, v, huv => by
    have h' : Sum.LiftRel (Ty.relB R (S.conTy X)) (Ty.relB R (.prod a (.pi f fun _ => X)))
      u v := huv
    cases h' with
    | inl h =>
      exact conAt_relB S (fun a k => mk ⟨.inl a.1, a.2⟩ k) (fun a k => mk' ⟨.inl a.1, a.2⟩ k)
        (fun c x y k k' hxy hk => hmk (.inl c) x y k k' hxy hk) h
    | inr h => exact hmk (.inr ()) _ _ _ _ h.1 h.2

/-- A step of an eliminator at related step functions, fields, children and recursive results
gives trees related by the exact lifting. -/
theorem stepAt_lift {X c : Ty} : ∀ (S : Sig), S.PosEq R → ∀ {g g' : Val (S.stepsTy X c)},
    Ty.relB R _ g g' → ∀ {c₀ : S.Ctor} {x y : S.Fld c₀}, Sig.fldRelB R S c₀ x y →
    ∀ {kids kids' : S.Pos c₀ → Val X}, (∀ p, Ty.relB R X (kids p) (kids' p)) →
    ∀ {rec rec' : S.Pos c₀ → CTree (Val c)}, (∀ j, CTree.Lift (Ty.relB R c) (rec j) (rec' j)) →
      CTree.Lift (Ty.relB R c) (stepAt S g ⟨c₀, x⟩ kids rec) (stepAt S g' ⟨c₀, y⟩ kids' rec')
  | .base _, _, _, _, hg, _, _, _, hxy, _, _, _, _, _, _ => hg _ _ hxy
  | .ext S _ none, hS, _, _, hg, .inl _, _, _, hxy, _, _, hk, _, _, hr =>
    stepAt_lift S hS hg.1 (c₀ := _) hxy hk hr
  | .ext S _ (some _), hS, _, _, hg, .inl _, _, _, hxy, _, _, hk, _, _, hr =>
    stepAt_lift S hS.2 hg.1 (c₀ := _) hxy hk hr
  | .ext _ _ none, _, _, _, hg, .inr _, _, _, hxy, _, _, _, _, _, _ => hg.2 _ _ hxy
  | .ext _ _ (some _), hS, _, _, hg, .inr _, _, _, hxy, _, _, hk, _, _, hr =>
    hg.2 _ _ ⟨hxy, hk, fun j j' hj => by obtain rfl := hS.1 j j' hj; exact hr j⟩

/-- The eliminator of `mu S` at related step functions and values gives trees related by the
exact lifting, when the recursive positions of `S` are discrete. -/
theorem foldW_lift {S : Sig} (hS : S.PosEq R) {c : Ty} {g g' : Val (S.stepsTy (.mu S) c)}
    (hg : Ty.relB R _ g g') {w w' : Val (.mu S)} (hw : Ty.relB R (.mu S) w w') :
    CTree.Lift (Ty.relB R c) (foldW g w) (foldW g' w') := by
  change Container.WLift (P := S.Pos) (Sig.fldRelB R S) w w' at hw
  induction hw with
  | mk hxy hk ih => exact stepAt_lift (X := .mu S) S hS hg hxy hk ih

/-- A constructor of an indexed signature at related arguments builds related nodes. -/
theorem conAtI_relB {f : FTy} {X : f.den → Ty} {T : Type} {Q : T → T → Prop} : ∀ (S : ISig f)
    (mk mk' : (a : (c : S.Ctor) × S.Fld c) → ((p : S.Pos a.1) → Val (X (S.nx a.1 p))) → T),
    (∀ (c : S.Ctor) (x y : S.Fld c) (k k' : (p : S.Pos c) → Val (X (S.nx c p))),
      ISig.fldRelB R S c x y → (∀ p, Ty.relB R _ (k p) (k' p)) →
        Q (mk ⟨c, x⟩ k) (mk' ⟨c, y⟩ k')) →
    ∀ {u v : Val (S.conTy X)}, Ty.relB R (S.conTy X) u v → Q (conAtI S mk u) (conAtI S mk' v)
  | .base _, _, _, hmk, _, _, huv => hmk () _ _ _ _ huv fun p => p.elim
  | .ext S a none nx, mk, mk', hmk, u, v, huv => by
    have h' : Sum.LiftRel (Ty.relB R (S.conTy X)) (Ty.relB R a) u v := huv
    cases h' with
    | inl h =>
      exact conAtI_relB S (fun a k => mk ⟨.inl a.1, a.2⟩ k) (fun a k => mk' ⟨.inl a.1, a.2⟩ k)
        (fun c x y k k' hxy hk => hmk (.inl c) x y k k' hxy hk) h
    | inr h => exact hmk (.inr ()) _ _ _ _ h fun p => p.elim
  | .ext S a (some g) nx, mk, mk', hmk, u, v, huv => by
    have h' : Sum.LiftRel (Ty.relB R (S.conTy X))
        (Ty.relB R (.prod a (.pi g fun p => X (nx p)))) u v := huv
    cases h' with
    | inl h =>
      exact conAtI_relB S (fun a k => mk ⟨.inl a.1, a.2⟩ k) (fun a k => mk' ⟨.inl a.1, a.2⟩ k)
        (fun c x y k k' hxy hk => hmk (.inl c) x y k k' hxy hk) h
    | inr h => exact hmk (.inr ()) _ _ _ _ h.1 h.2

/-- A step of an eliminator of an indexed family at related step functions, fields, children
and recursive results gives trees related by the exact lifting. -/
theorem stepAtI_lift {f : FTy} {X c : f.den → Ty} {r : Ty} : ∀ (S : ISig f)
    {g g' : Val (S.stepsTy X c r)}, Ty.relB R _ g g' →
    ∀ {c₀ : S.Ctor} {x y : S.Fld c₀}, ISig.fldRelB R S c₀ x y →
    ∀ {kids kids' : (p : S.Pos c₀) → Val (X (S.nx c₀ p))},
      (∀ p, Ty.relB R _ (kids p) (kids' p)) →
    ∀ {rec rec' : (p : S.Pos c₀) → CTree (Val (c (S.nx c₀ p)))},
      (∀ p, CTree.Lift (Ty.relB R _) (rec p) (rec' p)) →
      CTree.Lift (Ty.relB R r) (stepAtI S g ⟨c₀, x⟩ kids rec) (stepAtI S g' ⟨c₀, y⟩ kids' rec')
  | .base _, _, _, hg, _, _, _, hxy, _, _, _, _, _, _ => hg _ _ hxy
  | .ext S _ none _, _, _, hg, c₀, _, _, hxy, _, _, hk, _, _, hr => by
    cases c₀ with
    | inl c₀ => exact stepAtI_lift S hg.1 (c₀ := c₀) hxy hk hr
    | inr _ => exact hg.2 _ _ hxy
  | .ext S _ (some _) _, _, _, hg, c₀, _, _, hxy, _, _, hk, _, _, hr => by
    cases c₀ with
    | inl c₀ => exact stepAtI_lift S hg.1 (c₀ := c₀) hxy hk hr
    | inr _ => exact hg.2 _ _ ⟨hxy, hk, fun p _ _ _ => hr p⟩

/-- The eliminator of an indexed family at related step functions and values gives trees related
by the exact lifting. -/
theorem foldIW_lift {f : FTy} {S : f.den → ISig f} {c : f.den → Ty}
    {g g' : (j : f.den) → Val ((S j).stepsTy (fun j' => .imu f S j') c (c j))}
    (hg : Ty.relB R (.pi f fun j => (S j).stepsTy (fun j' => .imu f S j') c (c j)) g g')
    {i : f.den} {w w' : Val (.imu f S i)} (hw : Ty.relB R (.imu f S i) w w') :
    CTree.Lift (Ty.relB R (c i)) (foldIW g w) (foldIW g' w') := by
  change Container.IWLift (C := fun j => (S j).Ctor) (P := fun j c => (S j).Pos c)
    (nx := fun j c p => (S j).nx c p) (fun j c x y => ISig.fldRelB R (S j) c x y) w w' at hw
  induction hw with
  | mk hxy hk ih => exact stepAtI_lift (S _) (hg _) hxy hk ih

/-- The abstraction theorem of D: in environments related at a base relation that the term
respects, the evaluator gives trees related by the exact lifting of the relation of the type. -/
theorem Tm.eval_lift {Γ : List Ty} {τ : Ty} (t : Tm Γ τ) :
    t.RespB R → ∀ {ρ δ : Env Γ}, EnvRelB R ρ δ →
      CTree.Lift (Ty.relB R τ) (t.eval ρ) (t.eval δ) := by
  induction t with
  | var x => intro _ ρ δ h; exact .ret (h _ x)
  | lam b ih => intro ht ρ δ h; exact .ret fun u v huv => ih ht (h.cons huv)
  | app f x ihf ihx =>
    intro ht ρ δ h
    exact (ihf ht.1 h).bind fun g g' hg => (ihx ht.2 h).bind fun u v huv => .tick (hg u v huv)
  | letE e b ihe ihb =>
    intro ht ρ δ h; exact (ihe ht.1 h).bind fun u v huv => .tick (ihb ht.2 (h.cons huv))
  | seq e b ihe ihb => intro ht ρ δ h; exact (ihe ht.1 h).bind fun _ _ _ => .tick (ihb ht.2 h)
  | natLit n => intro _ ρ δ h; exact .ret rfl
  | lit f v => intro ht ρ δ h; exact .ret ht
  | prim p x ih =>
    intro ht ρ δ h
    refine (ih ht.2 h).bind fun u v huv => ?_
    obtain ⟨hr, hc⟩ := ht.1 u v huv
    change CTree.Lift _ (stepN CTree.tick (p.cost u) (.ret (p.apply u)))
      (stepN CTree.tick (p.cost v) (.ret (p.apply v)))
    rw [hc]
    exact stepN_lift (.ret hr) _
  | pair x y ihx ihy =>
    intro ht ρ δ h
    exact (ihx ht.1 h).bind fun u u' hu => (ihy ht.2 h).bind fun v v' hv => .ret ⟨hu, hv⟩
  | fst p ih => intro ht ρ δ h; exact (ih ht h).bind fun u v huv => .ret huv.1
  | snd p ih => intro ht ρ δ h; exact (ih ht h).bind fun u v huv => .ret huv.2
  | inl x ih => intro ht ρ δ h; exact (ih ht h).bind fun u v huv => .ret (Sum.LiftRel.inl huv)
  | inr x ih => intro ht ρ δ h; exact (ih ht h).bind fun u v huv => .ret (Sum.LiftRel.inr huv)
  | case s l r ihs ihl ihr =>
    intro ht ρ δ h
    refine (ihs ht.1 h).bind fun u v huv => .tick ?_
    cases huv with
    | inl hx => exact ihl ht.2.1 (h.cons hx)
    | inr hy => exact ihr ht.2.2 (h.cons hy)
  | ite c t e ihc iht ihe =>
    intro ht ρ δ h
    refine (ihc ht.2.1 h).bind fun u v huv => ?_
    obtain rfl := ht.1 u v huv
    cases u
    · exact .tick (ihe ht.2.2.2 h)
    · exact .tick (iht ht.2.2.1 h)
  | nil => intro _ ρ δ h; exact .ret List.Forall₂.nil
  | cons x xs ihx ihxs =>
    intro ht ρ δ h
    exact (ihx ht.1 h).bind fun u v huv =>
      (ihxs ht.2 h).bind fun l l' hl => .ret (List.Forall₂.cons huv hl)
  | lcase xs n c ihxs ihn ihc =>
    intro ht ρ δ h
    refine (ihxs ht.1 h).bind fun l l' hl => .tick ?_
    cases hl with
    | nil => exact ihn ht.2.1 h
    | cons hx hxs => exact ihc ht.2.2 ((h.cons (τ := .list _) hxs).cons hx)
  | foldl f i xs ihf ihi ihxs =>
    intro ht ρ δ h
    exact (ihf ht.1 h).bind fun g g' hg => (ihi ht.2.1 h).bind fun a a' ha =>
      (ihxs ht.2.2 h).bind fun l l' hl => foldT_lift hg hl ha
  | iter n f i ihn ihf ihi =>
    intro ht ρ δ h
    refine (ihn ht.1 h).bind fun k k' hk => ?_
    change k = k' at hk
    subst hk
    exact (ihf ht.2.1 h).bind fun g g' hg => (ihi ht.2.2 h).bind fun a a' ha => iterT_lift hg k ha
  | sample f => intro ht ρ δ h; exact .sample f fun x => .ret (ht x)
  | get n f => intro ht ρ δ h; exact .get n f fun x => .ret (ht x)
  | set n f x ih =>
    intro ht ρ δ h
    refine (ih ht.2.2 h).bind fun u v huv => ?_
    obtain rfl := ht.1 u v huv
    exact .set n f u (.ret ht.2.1)
  | query d r x ih =>
    intro ht ρ δ h
    refine (ih ht.2.2 h).bind fun u v huv => ?_
    obtain rfl := ht.1 u v huv
    exact .query d r u fun y => .ret (ht.2.1 y)
  | fail => intro _ ρ δ h; exact .fail
  | @con _ S x ih =>
    intro ht ρ δ h
    exact (ih ht h).bind fun u v huv => .ret (conAt_relB (Q := Ty.relB R (.mu S)) S _ _
      (fun _ _ _ _ _ hxy hk => Container.WLift.mk hxy hk) huv)
  | @fold _ S c g x ihg ihx =>
    intro ht ρ δ h
    exact (ihg ht.2.1 h).bind fun gv gv' hg => (ihx ht.2.2 h).bind fun w w' hw =>
      .tick (foldW_lift ht.1 hg hw)
  | @icon _ f S i x ih =>
    intro ht ρ δ h
    exact (ih ht h).bind fun u v huv => .ret (conAtI_relB (X := fun j => .imu f S j)
      (Q := Ty.relB R (.imu f S i)) (S i)
      (fun a k => (Container.IPW.mk i a k : Val (.imu f S i)))
      (fun a k => (Container.IPW.mk i a k : Val (.imu f S i)))
      (fun _ _ _ _ _ hxy hk => Container.IWLift.mk (C := fun j => (S j).Ctor)
        (P := fun j c => (S j).Pos c) (nx := fun j c p => (S j).nx c p)
        (R := fun j c x y => ISig.fldRelB R (S j) c x y) hxy hk)
      huv)
  | @ifold _ f S c i g x ihg ihx =>
    intro ht ρ δ h
    exact (ihg ht.1 h).bind fun gv gv' hg => (ihx ht.2 h).bind fun w w' hw =>
      .tick (foldIW_lift hg hw)
  | @ptab _ f B ts ih =>
    intro ht ρ δ h
    exact tabDep_lift f fun j => ih j (ht j) h
  | papp t j ih => intro ht ρ δ h; exact (ih ht h).bind fun u v huv => .ret (huv j)
  | spair j x ih => intro ht ρ δ h; exact (ih ht h).bind fun u v huv => .ret ⟨rfl, huv⟩
  | @scase _ f B c s ks ihs ihks =>
    intro ht ρ δ h
    refine (ihs ht.1 h).bind fun u v huv => ?_
    change (j : f.den) × Val (B j) at u v
    obtain ⟨i, x⟩ := u
    obtain ⟨j, y⟩ := v
    change ∃ e : i = j, Ty.relB R (B j) (e ▸ x) y at huv
    obtain ⟨rfl, hxy⟩ := huv
    exact .tick (ihks i (ht.2 i) (h.cons hxy))
  | fcase i ks ihi ihks =>
    intro ht ρ δ h
    refine (ihi ht.2.1 h).bind fun u v huv => ?_
    obtain rfl := ht.1 u v huv
    exact .tick (ihks u (ht.2.2 u) h)

/-- The abstraction theorem of D with cost: in environments related at a base relation that the
term respects, the values are related and the costs are equal. -/
theorem Tm.abstraction_cost {Γ : List Ty} {τ : Ty} (t : Tm Γ τ) (ht : t.RespB R)
    {ρ δ : Env Γ} (h : EnvRelB R ρ δ) :
    CTree.Lift (Ty.relB R τ) (t.eval ρ) (t.eval δ) ∧ (t.eval ρ).cost = (t.eval δ).cost :=
  ⟨t.eval_lift ht h, (t.eval_lift ht h).cost_eq⟩

end Fundamental

/-! ## The interpretation in the reflexive-graph model -/

section RGraph

/-- Base relations over the edges of a reflexive graph, equality over the reflexive edges. -/
structure BaseRG (G : RGraphCwF.Ctx.{0}) where
  /-- The base relation over an edge. -/
  R : ∀ {γ γ' : G.V}, G.E γ γ' → BRel
  /-- Over a reflexive edge the base relation is equality. -/
  refl_iff : ∀ γ f a b, R (G.refl γ) f a b ↔ a = b

variable {G : RGraphCwF.Ctx.{0}}

/-- A type of D as a type of the reflexive-graph model: its values at every vertex, related
over an edge by the relation of the type at the base relation of the edge. -/
def Ty.rg (B : BaseRG G) (τ : Ty) : RGraphCwF.Ty G where
  V := fun _ => Val τ
  E := fun e => Ty.relB (B.R e) τ
  refl_iff := fun γ => Ty.relB_iff_eq (B.refl_iff γ) τ

/-- The environments of a context of D as a type of the reflexive-graph model. -/
def envRG (B : BaseRG G) (Γ : List Ty) : RGraphCwF.Ty G where
  V := fun _ => Env Γ
  E := fun e ρ δ => EnvRelB (B.R e) ρ δ
  refl_iff := fun γ ρ δ => by
    constructor
    · intro h
      funext τ x
      exact (Ty.relB_iff_eq (B.refl_iff γ) τ _ _).1 (h τ x)
    · rintro rfl τ x
      exact (Ty.relB_iff_eq (B.refl_iff γ) τ _ _).2 rfl

/-- The computations of a type of D as a type of the reflexive-graph model: the trees, related
over an edge by the exact lifting of the relation of the type. -/
def Ty.rgC (B : BaseRG G) (τ : Ty) : RGraphCwF.Ty G where
  V := fun _ => CTree (Val τ)
  E := fun e => CTree.Lift (Ty.relB (B.R e) τ)
  refl_iff := fun γ => CTree.Lift.iff_eq (Ty.relB_iff_eq (B.refl_iff γ) τ)

/-- A term of D that respects the base relation over every edge as a term of the computation
type in the extension of the graph by the environments. -/
def Tm.rg (B : BaseRG G) {Γ : List Ty} {τ : Ty} (t : Tm Γ τ)
    (ht : ∀ {γ γ' : G.V} (e : G.E γ γ'), t.RespB (B.R e)) :
    RGraphCwF.Tm (RGraphCwF.ext G (envRG B Γ)) ((Ty.rgC B τ).sub (RGraphCwF.wk _)) where
  V := fun p => t.eval p.2
  E := fun e => t.eval_lift (ht e.1) e.2

/-- The abstraction theorem of the reflexive-graph model at a term of D: over an edge of the
extended graph, the trees are related by the exact lifting and have equal cost. -/
theorem Tm.rg_abstraction (B : BaseRG G) {Γ : List Ty} {τ : Ty} (t : Tm Γ τ)
    (ht : ∀ {γ γ' : G.V} (e : G.E γ γ'), t.RespB (B.R e))
    {p q : (RGraphCwF.ext G (envRG B Γ)).V} (e : (RGraphCwF.ext G (envRG B Γ)).E p q) :
    CTree.Lift (Ty.relB (B.R e.1) τ) (t.eval p.2) (t.eval q.2) ∧
      (t.eval p.2).cost = (t.eval q.2).cost :=
  ⟨(Tm.rg B t ht).abstraction e, ((Tm.rg B t ht).abstraction e).cost_eq⟩

/-- The base relations over the walking edge given by one base relation: equality over the
reflexive edges and `R` over the edge. -/
def BaseRG.walkR (R : BRel) : ∀ {x y : PolyRGraph.WalkV.{0}}, PolyRGraph.WalkE x y → BRel
  | _, _, .refl _ => fun _ a b => a = b
  | _, _, .edge => R

/-- The walking edge with one base relation over its edge. -/
def BaseRG.walk (R : BRel) : BaseRG PolyRGraph.walk.{0} where
  R := BaseRG.walkR R
  refl_iff := fun _ _ _ _ => Iff.rfl

end RGraph

/-! ## The interpretation in the polynomial model -/

section Poly

variable {G : RGraphCwF.Ctx.{0}}

/-- The context of the polynomial model of a context of D: the environments as shapes, the clock
`ℕ` of the context as positions. -/
def ctxP (B : BaseRG G) (Γ : List Ty) : PolyRGraph.Ctx.{0} :=
  ⟨RGraphCwF.ext G (envRG B Γ), RGraphCwF.Ty.disc _ ℕ⟩

/-- The computations of a type of D in the polynomial model: the trees as shapes, the clock ticks
`Fin t.cost` of a tree `t` as positions, related over an edge when they have the same index. -/
def Ty.polyC (B : BaseRG G) (Γ : List Ty) (τ : Ty) : PolyRGraph.Ty (ctxP B Γ) where
  S := (Ty.rgC B τ).sub (RGraphCwF.wk _)
  P :=
    { V := fun p => Fin (p.2 : CTree (Val τ)).cost
      E := fun _ i j => i.val = j.val
      refl_iff := fun _ _ _ => Fin.val_inj }

/-- Over an edge, trees related by the exact lifting have the same number of ticks, and the
relation of their ticks is the graph of the identity bijection. -/
theorem Ty.polyC_pos_rel_iff (B : BaseRG G) (Γ : List Ty) (τ : Ty)
    {p q : (RGraphCwF.ext (ctxP B Γ).A (Ty.polyC B Γ τ).S).V}
    (e : (RGraphCwF.ext (ctxP B Γ).A (Ty.polyC B Γ τ).S).E p q) :
    ∃ h : (p.2 : CTree (Val τ)).cost = (q.2 : CTree (Val τ)).cost,
      ∀ i j, (Ty.polyC B Γ τ).P.E e i j ↔ Fin.cast h i = j :=
  ⟨e.2.cost_eq, fun i j => by
    change i.val = j.val ↔ _
    exact ⟨fun hij => Fin.ext hij, fun hij => by subst hij; rfl⟩⟩

/-- A term of D that respects the base relation over every edge as a term of the polynomial
model: its trees as shapes, and the backward map that sends each tick of its tree to the same tick
of the clock of the context. -/
def Tm.poly (B : BaseRG G) {Γ : List Ty} {τ : Ty} (t : Tm Γ τ)
    (ht : ∀ {γ γ' : G.V} (e : G.E γ γ'), t.RespB (B.R e)) :
    PolyRGraph.Tm (ctxP B Γ) (Ty.polyC B Γ τ) where
  S := Tm.rg B t ht
  P :=
    { V := fun p => (p.2 : Fin (t.eval p.1.2).cost).val
      E := fun e => e.2 }

end Poly

end CatCrypt.Complexity.D
