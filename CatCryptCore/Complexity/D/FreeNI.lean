/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Complexity.D.RGraphInterp

/-!
# Non-interference with timing as a free theorem of D

A set of secret finite ground types `Sec : FTy → Prop` gives the base relation `BRel.secret Sec`:
the total relation at a secret type and equality at every other finite ground type. The secret is
then an abstract type: two secrets are always related, and a term that respects the relation
(`Tm.RespB`) inspects a secret only through primitive operations that send related arguments to
related results at equal cost, that is, primitives whose result and cost do not depend on the
secret. A branch, a write, a query or a fold over a recursive position at a secret type is
excluded by `Tm.RespB`, since the relation there is not discrete.

The public types (`Ty.Pub Sec`) are built from the non-secret finite ground types and `ℕ` by
products, sums, lists, and dependent products and sums. At a public type the relation is equality
(`Ty.Pub.relB_iff`), the identity extension condition restricted to the public part. The
abstraction theorem with cost (`Tm.abstraction_cost`) then gives, for a respecting term in two
environments that agree on the public variables:

* equal cost whatever the type of the result (`Tm.cost_eq_of_secret`): timing non-interference in
  the sense of Agat, with the cost of D as the clock;
* equal trees when the result type is public (`Tm.eval_eq_of_pub`): the effect nodes, the ticks and
  the leaves agree, so the public output, its distribution and its cost are independent of the
  secret.

`Tm.free_noninterference` states both for a term with one secret variable in front of a public
context.

## Comparison with dependency soundness

The dependency-soundness route (`DepSound`, `noninterference_hFreeRel`,
`exists_depSound_of_noninterference` and the probabilistic forms of `DepSoundProb`, in the
development's `Bridges/Transfer`) works with a lens into the trees of the free monad of a
container, whose backward map lists the input positions each output path demands; non-interference
holds when no backward image contains a secret position. The two routes conclude the same kind of
statement, a relation between the runs on two inputs differing only in the secret (`CTree.Lift`
here, `HFreeRel` there), and they differ in where the evidence sits.

* Here the evidence is the type: the relation is fixed by the secret types, and `Tm.RespB` is a
  structural condition on the term; there is no backward map. The condition is sufficient, not
  necessary: a term that compares a secret with itself through a primitive does not respect the
  relation although its output is constant. Dependency soundness is a characterization: every
  non-interfering family has a dependency-sound lens.
* Here the ticks are nodes of the tree, so the same relation gives equal cost; on the
  dependency-soundness side cost is visible only when it is an operation of the container.
* Here a sampling node is related to itself by the identity coupling (the relation is reflexive at
  sampled types), as with `ViewRel` at the classical effect. A sample that masks a secret, as in a
  one-time pad, needs a coupling along a bijection, which `couplingCodeRel` and `PFlow.sample_push`
  provide and `Tm.RespB` does not.
* Here secrecy is a property of a finite ground type, so a secret and a public value of the same
  finite ground type cannot be told apart; the dependency-soundness route marks secret positions
  of an input individually.

The two meet at deterministic non-interference of a tree family; a theorem stating this needs an
embedding of the trees of D (`CTree`) into the trees of the free monad of a container, which is not
part of this module.

## Main definitions

* `BRel.secret` — the base relation of a set of secret types;
* `Ty.Pub` — the public types.

## Main results

* `CTree.Lift.mono` — monotonicity of the exact lifting;
* `Ty.Pub.relB_iff` — identity extension at the public types;
* `EnvRelB.refl_of_pub` — a public environment is related to itself;
* `Prim.respB_of_pub` — a primitive between public types respects the relation;
* `Tm.cost_eq_of_secret`, `Tm.eval_eq_of_pub`, `Tm.free_noninterference` — non-interference with
  timing.

## References

* J. C. Reynolds, *Types, abstraction and parametric polymorphism*, IFIP Congress 1983;
* D. Volpano, G. Smith, C. Irvine, *A sound type system for secure flow analysis*, Journal of
  Computer Security 4, 1996;
* A. Sabelfeld, A. C. Myers, *Language-based information-flow security*, IEEE JSAC 21, 2003;
* J. Agat, *Transforming out timing leaks*, POPL 2000.

Search words: non-interference, noninterference, information flow, timing channel, constant time,
free theorem, parametricity, abstract type, secret.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Complexity.D

/-- The exact lifting is monotone in the relation of the leaves. -/
theorem CTree.Lift.mono {α β : Type} {R S : α → β → Prop} (hRS : ∀ a b, R a b → S a b)
    {t : CTree α} {m : CTree β} (h : CTree.Lift R t m) : CTree.Lift S t m := by
  induction h with
  | ret hab => exact .ret (hRS _ _ hab)
  | tick _ ih => exact .tick ih
  | sample f _ ih => exact .sample f ih
  | get n f _ ih => exact .get n f ih
  | set n f v _ ih => exact .set n f v ih
  | query d r x _ ih => exact .query d r x ih
  | fail => exact .fail

/-- The base relation of a set of secret finite ground types: total at a secret type, equality at
every other finite ground type. -/
def BRel.secret (Sec : FTy → Prop) : BRel := fun f a b => Sec f ∨ a = b

/-- At a finite ground type that is not secret, the relation of the secret types is equality. -/
theorem BRel.secret_eq {Sec : FTy → Prop} {f : FTy} (hf : ¬ Sec f) {a b : f.den}
    (h : BRel.secret Sec f a b) : a = b :=
  h.resolve_left hf

/-- The public types: built from the finite ground types that are not secret and `ℕ` by products,
sums, lists, and dependent products and sums. -/
inductive Ty.Pub (Sec : FTy → Prop) : Ty → Prop where
  | base {f : FTy} : ¬ Sec f → Ty.Pub Sec (.base f)
  | nat : Ty.Pub Sec .nat
  | prod {a b : Ty} : Ty.Pub Sec a → Ty.Pub Sec b → Ty.Pub Sec (.prod a b)
  | sum {a b : Ty} : Ty.Pub Sec a → Ty.Pub Sec b → Ty.Pub Sec (.sum a b)
  | list {a : Ty} : Ty.Pub Sec a → Ty.Pub Sec (.list a)
  | pi {f : FTy} {B : f.den → Ty} : (∀ j, Ty.Pub Sec (B j)) → Ty.Pub Sec (.pi f B)
  | sig {f : FTy} {B : f.den → Ty} : (∀ j, Ty.Pub Sec (B j)) → Ty.Pub Sec (.sig f B)

/-- Identity extension at the public types: the relation of the secret types is equality. -/
theorem Ty.Pub.relB_iff {Sec : FTy → Prop} {τ : Ty} (hτ : τ.Pub Sec) :
    ∀ u v : Val τ, Ty.relB (BRel.secret Sec) τ u v ↔ u = v := by
  induction hτ with
  | base hf =>
    intro u v
    exact ⟨BRel.secret_eq hf, fun h => Or.inr h⟩
  | nat => intro u v; exact Iff.rfl
  | prod _ _ iha ihb =>
    intro u v
    change Ty.relB _ _ u.1 v.1 ∧ Ty.relB _ _ u.2 v.2 ↔ u = v
    rw [iha, ihb]
    exact Prod.ext_iff.symm
  | @sum a b _ _ iha ihb =>
    intro u v
    change Val a ⊕ Val b at u v
    change Sum.LiftRel (Ty.relB _ a) (Ty.relB _ b) u v ↔ u = v
    constructor
    · rintro (⟨hx⟩ | ⟨hy⟩)
      · exact congrArg Sum.inl ((iha _ _).1 hx)
      · exact congrArg Sum.inr ((ihb _ _).1 hy)
    · rintro rfl
      cases u with
      | inl x => exact .inl ((iha x x).2 rfl)
      | inr y => exact .inr ((ihb y y).2 rfl)
  | @list a _ iha =>
    intro u v
    change List.Forall₂ (Ty.relB _ a) u v ↔ u = v
    have hab : Ty.relB (BRel.secret Sec) a = (· = ·) :=
      funext fun x => funext fun y => propext (iha x y)
    rw [hab, List.forall₂_eq_eq_eq]
    exact Iff.rfl
  | @pi f B _ ih =>
    intro u v
    change (j : f.den) → Val (B j) at u v
    change (∀ j, Ty.relB _ (B j) (u j) (v j)) ↔ u = v
    rw [funext_iff]
    exact forall_congr' fun j => ih j (u j) (v j)
  | @sig f B _ ih =>
    intro u v
    change (j : f.den) × Val (B j) at u v
    obtain ⟨i, x⟩ := u
    obtain ⟨j, y⟩ := v
    change (∃ e : i = j, Ty.relB _ (B j) (e ▸ x) y) ↔ _
    constructor
    · rintro ⟨rfl, hxy⟩
      rw [(ih i x y).1 hxy]
    · intro he
      obtain ⟨rfl, hx⟩ := Sigma.mk.inj_iff.1 he
      cases hx
      exact ⟨rfl, (ih i x x).2 rfl⟩

/-- An environment of a public context is related to itself at the relation of the secret
types. -/
theorem EnvRelB.refl_of_pub {Sec : FTy → Prop} {Γ : List Ty} (hΓ : ∀ σ ∈ Γ, σ.Pub Sec)
    (ρ : Env Γ) : EnvRelB (BRel.secret Sec) ρ ρ :=
  fun σ x => ((hΓ σ x.mem).relB_iff _ _).2 rfl

/-- A primitive operation between public types respects the relation of the secret types. -/
theorem Prim.respB_of_pub {Sec : FTy → Prop} {a b : Ty} (ha : a.Pub Sec) (hb : b.Pub Sec)
    (p : Prim a b) : p.RespB (BRel.secret Sec) := by
  intro u v huv
  obtain rfl := (ha.relB_iff u v).1 huv
  exact ⟨(hb.relB_iff _ _).2 rfl, rfl⟩

/-- Timing non-interference: a term that respects the relation of the secret types has equal cost
in two environments related by it, whatever the type of its result. -/
theorem Tm.cost_eq_of_secret {Sec : FTy → Prop} {Γ : List Ty} {τ : Ty} (t : Tm Γ τ)
    (ht : t.RespB (BRel.secret Sec)) {ρ δ : Env Γ} (h : EnvRelB (BRel.secret Sec) ρ δ) :
    (t.eval ρ).cost = (t.eval δ).cost :=
  (t.abstraction_cost ht h).2

/-- Non-interference at a public result type: a term that respects the relation of the secret
types gives the same tree in two environments related by it, so its public output, the
distribution of that output and its cost do not depend on the secret. -/
theorem Tm.eval_eq_of_pub {Sec : FTy → Prop} {Γ : List Ty} {τ : Ty} (hτ : τ.Pub Sec)
    (t : Tm Γ τ) (ht : t.RespB (BRel.secret Sec)) {ρ δ : Env Γ}
    (h : EnvRelB (BRel.secret Sec) ρ δ) : t.eval ρ = t.eval δ :=
  (CTree.Lift.iff_eq (fun _ _ => Iff.rfl) _ _).1
    ((t.eval_lift ht h).mono fun u v huv => (hτ.relB_iff u v).1 huv)

/-- Non-interference with timing as a free theorem: for a term with a variable of a secret type in
front of a public context that respects the relation of the secret types, any two secrets give
runs of equal cost, and of equal trees when the result type is public. -/
theorem Tm.free_noninterference {Sec : FTy → Prop} {s : FTy} (hs : Sec s) {Γ : List Ty}
    {τ : Ty} (t : Tm (.base s :: Γ) τ) (ht : t.RespB (BRel.secret Sec))
    (hΓ : ∀ σ ∈ Γ, σ.Pub Sec) (ρ : Env Γ) (k k' : s.den) :
    (t.eval (ρ.cons (τ := .base s) k)).cost = (t.eval (ρ.cons (τ := .base s) k')).cost ∧
      (τ.Pub Sec →
        t.eval (ρ.cons (τ := .base s) k) = t.eval (ρ.cons (τ := .base s) k')) := by
  have h : EnvRelB (BRel.secret Sec) (ρ.cons (τ := .base s) k) (ρ.cons (τ := .base s) k') :=
    (EnvRelB.refl_of_pub hΓ ρ).cons (Or.inl hs)
  exact ⟨t.cost_eq_of_secret ht h, fun hτ => t.eval_eq_of_pub hτ ht h⟩

end CatCrypt.Complexity.D
