/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Container.CwF
public import CatCryptCore.Container.DillerNahm
public import Mathlib.CategoryTheory.Category.Basic

/-!
# Dependent products of containers, and the Diller–Nahm predicate over pairs of runs

This module continues `CatCryptCore.Container.CwF`, the polynomial model over `Type`.

Dependent products. A shape of `Ty.pi A B` is a `PiShape`: a forward map `fwd` on shapes, and a
backward map `back` that sends an argument `a` and a position of the result to `none` or to a
position `some d` of the argument (Proposition 3.12 of Cavallo and Höfer). A position of the
function type is an argument with a result position on which `back` is `none`. The bijection between
terms of `B` over `Γ.A` and terms of `Π A B` (`Tm.lamEquiv`) is the isomorphism
`(Z + Y)^X ≃ Σ f : X → 1 + Y, ({x // f x = none} → Z)` at each shape of `Γ`, where a backward map
into `Γ.B γ ⊕ A.P γ a` is split into the part into `A.P γ a`, which is shape data, and the part into
`Γ.B γ`, which remains position data. The base `Type` has extensive coproducts by `Sum.elim`; its
coproducts have η only propositionally, so `Tm.app_lam`, `Tm.lam_app` and `Tm.lam_sub` are
propositional, where the paper has strict isomorphisms. `Ty.pi_sub` is strict.

Function extensionality. The function type records the backward component in its shape, and a path
compares shapes (`nonempty_tm_eq_iff`). A path between `f` and `g` is therefore equal forward maps
and equal backward maps (`nonempty_tm_eq_pi_iff`), and a family of paths between the applications
`Tm.app f` and `Tm.app g` is equal forward maps only (`nonempty_tm_eq_app_iff`). Two functions with
equal values at each argument and different backward components are thus pointwise equal without a
path between them, so function extensionality fails in the model; this is the failure in the title
of Cavallo and Höfer.

The predicate layer. Equation (9) of Moss and von Glehn (§8) reads
`∀ u y, (∀ x ∈ F(u,y), A(u;x)) → B(f u; y)`; it is `DNSound` on a `DNLens` with predicates `Pred`
on the positions. An agreement `Agree P` is a predicate on the positions of the first of two runs,
and it is exactly a `Pred` on the container `runPair P` of pairs of runs (`Agree.toPred`). The lift
`runPairLens g` of a Diller–Nahm morphism runs `g` on both shapes and evaluates its backward map at
the first. Equation (9) at this lift is agreement soundness (`dnSound_runPair_iff`), so that
"non-interference is Diller–Nahm over pairs of runs" is the statement of that theorem. Objects with
an agreement and sound morphisms form a category (`RunObj`, `RunHom`) over the Diller–Nahm category.

A term as a lens. A term `a` of type `A` is a lens `Tm.toLens a` from `Γ` to the total container
`Ty.total A`, whose backward map is that of `a`. A backward map is unconstrained: soundness for
agreement (`TermSound`) is a predicate added on the term. It is stable under substitution
(`TermSound.sub`), and a sound term gives a morphism of `RunObj` (`RunHom.ofTerm`).

## Main definitions

* `PiShape`, `PiShape.Pos`, `Ty.pi`, `Tm.lam`, `Tm.app`, `Tm.appAt` — dependent products;
* `Pred`, `DNSound` — the Diller–Nahm predicate, equation (9) of Moss and von Glehn;
* `Agree`, `runPair`, `Agree.toPred`, `runPairLens`, `AgreeSound`, `DepSound` — pairs of runs;
* `RunObj`, `RunHom` — the category over pairs of runs;
* `Ty.total`, `Tm.toLens`, `TermSound` — a term as a lens, with soundness as an added predicate.

## Main results

* `Tm.lamEquiv`, `Tm.app_lam`, `Tm.lam_app`, `Tm.lam_sub`, `Tm.app_sub`, `Ty.pi_sub` — Π;
* `PiShape.ext_iff_cast`, `nonempty_tm_eq_pi_iff`, `nonempty_tm_eq_app_iff` — the shape of a
  function type is its forward and backward data;
* `DNSound.id`, `DNSound.comp`, `AgreeSound.id`, `AgreeSound.comp`, `DepSound.id`, `DepSound.comp`,
  `agreeSound_ofLens_iff`;
* `dnSound_runPair_iff`, `runPairLens_id`, `runPairLens_comp` — agreement soundness is equation (9)
  over pairs of runs;
* `RunHom.id_comp`, `RunHom.comp_id`, `RunHom.comp_assoc`, and the `Category` instance on `RunObj`;
* `Tm.toLens_sub`, `TermSound.sub`, `dnSound_ofLens_toLens_iff`.

## References

* T. von Glehn, *Polynomials and models of type theory*, PhD thesis, Cambridge, 2015;
* S. Moss, T. von Glehn, *Dialectica models of type theory*, LICS 2018, §8;
* E. Cavallo, T. Höfer, *Univalence without function extensionality*, arXiv:2605.00812, §3;
* T. Altenkirch, A. Kaposi, *Type theory in type theory using quotient inductive types*, POPL 2016.

Search words: dependent product, Π type, polynomial model, function extensionality, partial backward
map, Dialectica, Diller–Nahm, non-interference, noninterference, dependency soundness, agreement,
pair of runs, category with families.
-/

set_option autoImplicit false

@[expose] public section

universe u

namespace CatCrypt.Container.CwF

open PFunctor

/-! ## Shapes of the function type -/

/-- A shape of a function type at a fixed shape of the context: the forward map on shapes, and the
partial backward map from a position of the result to a position of the argument. The value `none`
means that the position of the result depends on the context and not on the argument. -/
structure PiShape {I : Type u} (AP BS : I → Type u) (BP : ∀ i, BS i → Type u) : Type u where
  /-- The forward map on shapes. -/
  fwd : ∀ i, BS i
  /-- The partial backward map, to a position of the argument. -/
  back : ∀ i, BP i (fwd i) → Option (AP i)

section Point

variable {I : Type u} {AP BS : I → Type u} {BP : ∀ i, BS i → Type u} {Z Z' : Type u}

/-- **The shape of a function type is its forward and backward data.** Two shapes are equal exactly
when their forward maps are equal and their backward maps are equal over that equality. -/
theorem PiShape.ext_iff_cast {s s' : PiShape AP BS BP} :
    s = s' ↔ ∃ h : s.fwd = s'.fwd, ∀ i b, s.back i b = s'.back i (congrFun h i ▸ b) := by
  constructor
  · rintro rfl
    exact ⟨rfl, fun _ _ => rfl⟩
  · obtain ⟨f, k⟩ := s
    obtain ⟨f', k'⟩ := s'
    rintro ⟨h, hb⟩
    obtain rfl : f = f' := h
    exact congrArg (PiShape.mk f) (funext fun i => funext fun b => hb i b)

/-- The positions of a function type at a shape: the argument and result position pairs on which the
backward map is `none`. -/
abbrev PiShape.Pos (s : PiShape AP BS BP) : Type u :=
  {x : Σ i, BP i (s.fwd i) // s.back x.1 x.2 = none}

/-- The abstraction at a shape of the context: a backward map into a sum is split into the partial
backward map, and a backward map from the positions where that map is `none`. -/
def lamPoint (f : ∀ i, BS i) (t : ∀ i, BP i (f i) → Z ⊕ AP i) :
    Σ s : PiShape AP BS BP, (s.Pos → Z) :=
  ⟨⟨f, fun i b => (t i b).getRight?⟩,
    fun x => (t x.1.1 x.1.2).getLeft (Sum.getRight?_eq_none_iff.1 x.2)⟩

/-- The application at a shape of the context: the two parts of a backward map are recombined. -/
def appPoint (s : PiShape AP BS BP) (K : s.Pos → Z) (i : I) (b : BP i (s.fwd i)) : Z ⊕ AP i :=
  match h : s.back i b with
  | none => .inl (K ⟨⟨i, b⟩, h⟩)
  | some d => .inr d

/-- `appPoint` where the backward map is `none`. -/
theorem appPoint_of_none (s : PiShape AP BS BP) (K : s.Pos → Z) {i : I} {b : BP i (s.fwd i)}
    (h : s.back i b = none) : appPoint s K i b = .inl (K ⟨⟨i, b⟩, h⟩) := by
  unfold appPoint
  split <;> simp_all

/-- `appPoint` where the backward map is `some d`. -/
theorem appPoint_of_some (s : PiShape AP BS BP) (K : s.Pos → Z) {i : I} {b : BP i (s.fwd i)}
    {d : AP i} (h : s.back i b = some d) : appPoint s K i b = .inr d := by
  unfold appPoint
  split <;> simp_all

/-- Application after abstraction, at a shape of the context. -/
theorem appPoint_lamPoint (f : ∀ i, BS i) (t : ∀ i, BP i (f i) → Z ⊕ AP i) (i : I)
    (b : BP i (f i)) : appPoint (lamPoint f t).1 (lamPoint f t).2 i b = t i b := by
  rcases ht : t i b with z | d
  · have h : (lamPoint f t).1.back i b = none := by simp [lamPoint, ht]
    refine (appPoint_of_none _ _ h).trans (congrArg Sum.inl ?_)
    exact (Sum.getLeft_eq_iff _).2 ht
  · exact appPoint_of_some _ _ (by simp [lamPoint, ht])

/-- Pairs of a shape and a backward map, with the same forward map, are equal when the partial
backward maps and the backward maps are pointwise equal. -/
theorem piPoint_ext {f : ∀ i, BS i} {k k' : ∀ i, BP i (f i) → Option (AP i)}
    {K : (PiShape.mk f k).Pos → Z} {K' : (PiShape.mk f k').Pos → Z}
    (hb : ∀ i b, k i b = k' i b)
    (hK : ∀ i b (h : k i b = none), K ⟨⟨i, b⟩, h⟩ = K' ⟨⟨i, b⟩, (hb i b).symm.trans h⟩) :
    (⟨⟨f, k⟩, K⟩ : Σ s : PiShape AP BS BP, (s.Pos → Z)) = ⟨⟨f, k'⟩, K'⟩ := by
  obtain rfl : k = k' := funext fun i => funext (hb i)
  exact congrArg (Sigma.mk _) (funext fun ⟨⟨i, b⟩, h⟩ => hK i b h)

/-- Abstraction after application, at a shape of the context. -/
theorem lamPoint_appPoint (s : PiShape AP BS BP) (K : s.Pos → Z) :
    lamPoint s.fwd (appPoint s K) = ⟨s, K⟩ := by
  obtain ⟨f, k⟩ := s
  have hb : ∀ i b, (appPoint ⟨f, k⟩ K i b).getRight? = k i b := fun i b => by
    rcases h : k i b with _ | d
    · rw [appPoint_of_none _ K h]
      rfl
    · rw [appPoint_of_some _ K h]
      rfl
  refine piPoint_ext hb fun i b h => ?_
  exact (Sum.getLeft_eq_iff _).2 (appPoint_of_none _ K _)

/-- The left value of a sum after a map of the left component. -/
theorem getLeft_elim_map (m : Z → Z') {Y : Type u} (z : Z ⊕ Y)
    (h : (Sum.elim (fun w => Sum.inl (m w)) Sum.inr z : Z' ⊕ Y).isLeft) (h' : z.isLeft) :
    (Sum.elim (fun w => Sum.inl (m w)) Sum.inr z : Z' ⊕ Y).getLeft h = m (z.getLeft h') := by
  cases z with
  | inl w => rfl
  | inr y => simp at h'

/-- The abstraction is natural in the target of the backward map. -/
theorem lamPoint_map (m : Z → Z') (f : ∀ i, BS i) (t : ∀ i, BP i (f i) → Z ⊕ AP i) :
    lamPoint f (fun i b => Sum.elim (fun w => Sum.inl (m w)) Sum.inr (t i b)) =
      ⟨(lamPoint f t).1, fun x => m ((lamPoint f t).2 x)⟩ := by
  have hb : ∀ i b, (Sum.elim (fun w => Sum.inl (m w)) Sum.inr (t i b) : Z' ⊕ AP i).getRight? =
      (t i b).getRight? := fun i b => by
    cases t i b <;> rfl
  exact piPoint_ext hb fun i b h =>
    getLeft_elim_map m (t i b) _ (Sum.getRight?_eq_none_iff.1 ((hb i b).symm.trans h))

end Point

/-! ## Dependent products -/

section Pi

variable {Γ Δ : Ctx.{u}} {A : Ty Γ} {B : Ty (ext Γ A)}

/-- The dependent product (Proposition 3.12): a shape is a `PiShape`, and a position is an argument
and a result position on which the backward map is `none`. -/
def Ty.pi (A : Ty Γ) (B : Ty (ext Γ A)) : Ty Γ where
  S γ := PiShape (A.P γ) (fun a => B.S ⟨γ, a⟩) (fun a => B.P ⟨γ, a⟩)
  P _ s := s.Pos

/-- The dependent product is stable under substitution, strictly. -/
theorem Ty.pi_sub (A : Ty Γ) (B : Ty (ext Γ A)) (σ : Lens Δ Γ) :
    (Ty.pi A B).sub σ = Ty.pi (A.sub σ) (B.sub (lift σ A)) := rfl

/-- Abstraction. -/
def Tm.lam (t : Tm (ext Γ A) B) : Tm Γ (Ty.pi A B) :=
  Tm.ofSection fun γ => lamPoint (fun a => t.S ⟨γ, a⟩) (fun a => t.P ⟨γ, a⟩)

/-- Application to the last variable. -/
def Tm.app (f : Tm Γ (Ty.pi A B)) : Tm (ext Γ A) B where
  S x := (f.S x.1).fwd x.2
  P x := appPoint (f.S x.1) (f.P x.1) x.2

/-- Application to a term. -/
abbrev Tm.appAt (f : Tm Γ (Ty.pi A B)) (a : Tm Γ A) : Tm Γ (B.sub (inst a)) :=
  (Tm.app f).sub (inst a)

/-- The partial backward map of an abstraction reads the part of the backward map of the body into
the argument. -/
theorem Tm.lam_back (t : Tm (ext Γ A) B) (γ : Γ.A) (a : A.S γ) (b : B.P ⟨γ, a⟩ (t.S ⟨γ, a⟩)) :
    ((Tm.lam t).S γ).back a b = (t.P ⟨γ, a⟩ b).getRight? := rfl

/-- The forward map of a function is its application. -/
theorem Tm.app_S (f : Tm Γ (Ty.pi A B)) (γ : Γ.A) (a : A.S γ) :
    (Tm.app f).S ⟨γ, a⟩ = (f.S γ).fwd a := rfl

/-- The β law of Π. -/
theorem Tm.app_lam (t : Tm (ext Γ A) B) : Tm.app (Tm.lam t) = t :=
  Tm.congr_P fun x b =>
    appPoint_lamPoint (AP := A.P x.1) (BS := fun a => B.S ⟨x.1, a⟩)
      (BP := fun a => B.P ⟨x.1, a⟩) (Z := Γ.B x.1) (fun a => t.S ⟨x.1, a⟩)
      (fun a => t.P ⟨x.1, a⟩) x.2 b

/-- The η law of Π. -/
theorem Tm.lam_app (f : Tm Γ (Ty.pi A B)) : Tm.lam (Tm.app f) = f :=
  Tm.ext_section fun γ => lamPoint_appPoint (f.S γ) (f.P γ)

/-- **The bijection of abstraction and application** (Proposition 3.12). -/
def Tm.lamEquiv : Tm (ext Γ A) B ≃ Tm Γ (Ty.pi A B) where
  toFun := Tm.lam
  invFun := Tm.app
  left_inv := Tm.app_lam
  right_inv := Tm.lam_app

/-- The β law of Π at a term. -/
theorem Tm.appAt_lam (t : Tm (ext Γ A) B) (a : Tm Γ A) :
    Tm.appAt (Tm.lam t) a = t.sub (inst a) :=
  congrArg (fun x : Tm (ext Γ A) B => x.sub (inst a)) (Tm.app_lam t)

/-- Abstraction is natural in the context. -/
theorem Tm.lam_sub (t : Tm (ext Γ A) B) (σ : Lens Δ Γ) :
    (Tm.lam t).sub σ = Tm.lam (A := A.sub σ) (B := B.sub (lift σ A)) (t.sub (lift σ A)) :=
  Tm.ext_section fun d =>
    (lamPoint_map (σ.toFunB d) (fun a => t.S ⟨σ.toFunA d, a⟩)
      (fun a => t.P ⟨σ.toFunA d, a⟩)).symm

/-- Application is natural in the context. -/
theorem Tm.app_sub (f : Tm Γ (Ty.pi A B)) (σ : Lens Δ Γ) :
    (Tm.app f).sub (lift σ A) = Tm.app (A := A.sub σ) (B := B.sub (lift σ A)) (f.sub σ) := by
  have h : f.sub σ = Tm.lam (A := A.sub σ) (B := B.sub (lift σ A)) ((Tm.app f).sub (lift σ A)) :=
    (congrArg (fun g : Tm Γ (Ty.pi A B) => g.sub σ) (Tm.lam_app f)).symm.trans (Tm.lam_sub _ σ)
  exact (Tm.app_lam (A := A.sub σ) (B := B.sub (lift σ A)) _).symm.trans
    (congrArg (Tm.app (A := A.sub σ) (B := B.sub (lift σ A))) h.symm)

/-- **Paths between functions.** The type `f = g` of a function type has a term exactly when the
forward maps are equal and the partial backward maps are equal over that equality. -/
theorem nonempty_tm_eq_pi_iff {f g : Tm Γ (Ty.pi A B)} :
    Nonempty (Tm Γ (Ty.eq f g)) ↔
      ∀ γ, ∃ h : (f.S γ).fwd = (g.S γ).fwd,
        ∀ a b, (f.S γ).back a b = (g.S γ).back a (congrFun h a ▸ b) :=
  nonempty_tm_eq_iff.trans (forall_congr' fun _ => PiShape.ext_iff_cast)

/-- **Paths between applications.** The family of paths between the applications of `f` and `g`
exists exactly when the forward maps are equal; the backward maps play no part. -/
theorem nonempty_tm_eq_app_iff {f g : Tm Γ (Ty.pi A B)} :
    Nonempty (Tm (ext Γ A) (Ty.eq (Tm.app f) (Tm.app g))) ↔ ∀ γ, (f.S γ).fwd = (g.S γ).fwd :=
  nonempty_tm_eq_iff.trans
    ⟨fun h γ => funext fun a => h ⟨γ, a⟩, fun h x => congrFun (h x.1) x.2⟩

end Pi

/-! ## The Diller–Nahm predicate -/

section Predicate

variable {P Q R S : PFunctor.{u, u}}

/-- A predicate on the positions of a container. -/
abbrev Pred (P : PFunctor.{u, u}) : Type u := ∀ a, P.B a → Prop

/-- **Equation (9) of Moss and von Glehn.** `∀ u y, (∀ x ∈ F(u,y), A(u;x)) → B(f u; y)`. -/
def DNSound (A : Pred P) (B : Pred Q) (g : DNLens P Q) : Prop :=
  ∀ u y, (∀ x ∈ g.toFunB u y, A u x) → B (g.toFunA u) y

/-- The identity satisfies equation (9). -/
theorem DNSound.id (A : Pred P) : DNSound A A (DNLens.id P) :=
  fun _ y h => h y (Multiset.mem_singleton_self y)

/-- Equation (9) is closed under composition. -/
theorem DNSound.comp {A : Pred P} {B : Pred Q} {C : Pred R} {f : DNLens P Q} {g : DNLens Q R}
    (hf : DNSound A B f) (hg : DNSound B C g) : DNSound A C (DNLens.comp g f) :=
  fun u z h => hg _ z fun y hy => hf u y fun x hx =>
    h x (Multiset.mem_bind.2 ⟨y, hy, hx⟩)

/-- An agreement on the container `P`: for two shapes and a position of the first, the proposition
that the two runs agree at that position. -/
abbrev Agree (P : PFunctor.{u, u}) : Type u := ∀ a (_ : P.A), P.B a → Prop

/-- The container of pairs of runs: a shape is a pair of shapes, and a position is a position of the
first run. -/
abbrev runPair (P : PFunctor.{u, u}) : PFunctor.{u, u} := ⟨P.A × P.A, fun x => P.B x.1⟩

/-- An agreement as a predicate on the positions of the container of pairs of runs. -/
def Agree.toPred (R : Agree P) : Pred (runPair P) := fun x d => R x.1 x.2 d

/-- The lift of a Diller–Nahm morphism to pairs of runs: the forward map runs on both shapes, and
the backward map is evaluated at the first. -/
def runPairLens (g : DNLens P Q) : DNLens (runPair P) (runPair Q) where
  toFunA x := (g.toFunA x.1, g.toFunA x.2)
  toFunB x := g.toFunB x.1

/-- The lift to pairs of runs preserves the identity, strictly. -/
theorem runPairLens_id : runPairLens (DNLens.id P) = DNLens.id (runPair P) := rfl

/-- The lift to pairs of runs preserves composition, strictly. -/
theorem runPairLens_comp (g : DNLens Q R) (f : DNLens P Q) :
    runPairLens (DNLens.comp g f) = DNLens.comp (runPairLens g) (runPairLens f) := rfl

/-- **Soundness for agreement of a Diller–Nahm morphism.** Two runs that agree at each position
demanded by `y` at the first run have outputs that agree at `y`. -/
def AgreeSound (RP : Agree P) (RQ : Agree Q) (g : DNLens P Q) : Prop :=
  ∀ a a' y, (∀ d ∈ g.toFunB a y, RP a a' d) → RQ (g.toFunA a) (g.toFunA a') y

/-- **Dependency soundness of a lens.** Two runs that agree at the position demanded by `y` at the
first run have outputs that agree at `y`. -/
def DepSound (RP : Agree P) (RQ : Agree Q) (l : Lens P Q) : Prop :=
  ∀ a a' y, RP a a' (l.toFunB a y) → RQ (l.toFunA a) (l.toFunA a') y

/-- **Non-interference is Diller–Nahm over pairs of runs.** Equation (9) at the lift of `g` to the
container of pairs of runs is soundness of `g` for agreement. -/
theorem dnSound_runPair_iff {RP : Agree P} {RQ : Agree Q} {g : DNLens P Q} :
    DNSound RP.toPred RQ.toPred (runPairLens g) ↔ AgreeSound RP RQ g :=
  ⟨fun h a a' y hy => h (a, a') y hy, fun h x y hy => h x.1 x.2 y hy⟩

/-- The identity is sound for agreement. -/
theorem AgreeSound.id (RP : Agree P) : AgreeSound RP RP (DNLens.id P) :=
  fun _ _ y h => h y (Multiset.mem_singleton_self y)

/-- Soundness for agreement is closed under composition. -/
theorem AgreeSound.comp {RP : Agree P} {RQ : Agree Q} {RR : Agree R} {f : DNLens P Q}
    {g : DNLens Q R} (hf : AgreeSound RP RQ f) (hg : AgreeSound RQ RR g) :
    AgreeSound RP RR (DNLens.comp g f) :=
  fun a a' z h => hg _ _ z fun y hy => hf a a' y fun d hd =>
    h d (Multiset.mem_bind.2 ⟨y, hy, hd⟩)

/-- The identity lens is dependency sound. -/
theorem DepSound.id (RP : Agree P) : DepSound RP RP (Lens.id P) :=
  fun _ _ _ h => h

/-- Dependency soundness is closed under composition. -/
theorem DepSound.comp {RP : Agree P} {RQ : Agree Q} {RR : Agree R} {f : Lens P Q} {g : Lens Q R}
    (hf : DepSound RP RQ f) (hg : DepSound RQ RR g) : DepSound RP RR (Lens.comp g f) :=
  fun a a' z h => hg _ _ z (hf a a' _ h)

/-- A lens is dependency sound exactly when its Diller–Nahm morphism is sound for agreement. -/
theorem agreeSound_ofLens_iff {RP : Agree P} {RQ : Agree Q} {l : Lens P Q} :
    AgreeSound RP RQ (DNLens.ofLens l) ↔ DepSound RP RQ l :=
  ⟨fun h a a' y hy => h a a' y fun d hd => by
      rw [show d = l.toFunB a y from Multiset.mem_singleton.1 hd]
      exact hy,
    fun h a a' y hy => h a a' y (hy _ (Multiset.mem_singleton_self _))⟩

end Predicate

/-! ## The category over pairs of runs -/

/-- An object over pairs of runs: a container with an agreement. -/
structure RunObj : Type (u + 1) where
  /-- The container. -/
  cont : PFunctor.{u, u}
  /-- The agreement of two runs at a position. -/
  agree : Agree cont

/-- A morphism over pairs of runs: a Diller–Nahm morphism with its soundness for agreement. -/
@[ext] structure RunHom (X Y : RunObj.{u}) : Type u where
  /-- The underlying Diller–Nahm morphism. -/
  lens : DNLens X.cont Y.cont
  /-- Soundness for agreement. -/
  sound : AgreeSound X.agree Y.agree lens

namespace RunHom

variable {W X Y Z : RunObj.{u}}

/-- The identity over pairs of runs. -/
protected def id (X : RunObj.{u}) : RunHom X X := ⟨DNLens.id X.cont, AgreeSound.id X.agree⟩

/-- The composite over pairs of runs. -/
def comp (g : RunHom Y Z) (f : RunHom X Y) : RunHom X Z :=
  ⟨DNLens.comp g.lens f.lens, f.sound.comp g.sound⟩

/-- The identity is a left unit. -/
theorem id_comp (f : RunHom X Y) : comp (RunHom.id Y) f = f :=
  RunHom.ext (DNLens.id_comp f.lens)

/-- The identity is a right unit. -/
theorem comp_id (f : RunHom X Y) : comp f (RunHom.id X) = f :=
  RunHom.ext (DNLens.comp_id f.lens)

/-- Composition is associative. -/
theorem comp_assoc (h : RunHom Y Z) (g : RunHom X Y) (f : RunHom W X) :
    comp (comp h g) f = comp h (comp g f) :=
  RunHom.ext (DNLens.comp_assoc h.lens g.lens f.lens)

end RunHom

/-- **The category over pairs of runs.** Objects are containers with agreements, and morphisms are
Diller–Nahm morphisms sound for agreement. -/
instance : CategoryTheory.Category RunObj.{u} where
  Hom := RunHom
  id := RunHom.id
  comp f g := RunHom.comp g f
  id_comp := RunHom.comp_id
  comp_id := RunHom.id_comp
  assoc f g h := (RunHom.comp_assoc h g f).symm

/-! ## A term as a lens -/

section Term

variable {Γ Δ : Ctx.{u}} {A : Ty Γ}

/-- The total container of a type: shapes are pairs, and positions are the positions of the type. -/
abbrev Ty.total (A : Ty Γ) : PFunctor.{u, u} := ⟨Σ γ, A.S γ, fun x => A.P x.1 x.2⟩

/-- A term as a lens into the total container of its type. Its backward map is that of the term. -/
def Tm.toLens (a : Tm Γ A) : Lens Γ (Ty.total A) where
  toFunA γ := ⟨γ, a.S γ⟩
  toFunB := a.P

/-- The map from a context extension to the total container: positions of the type are positions of
the context extension. -/
def totalOfExt (A : Ty Γ) : Lens (ext Γ A) (Ty.total A) where
  toFunA x := x
  toFunB _ y := Sum.inr y

/-- The lens of a term is its section into the context extension, followed by the map to the total
container. -/
theorem Tm.toLens_eq (a : Tm Γ A) : Lens.comp (totalOfExt A) (inst a) = a.toLens := rfl

/-- The map of total containers over a substitution. -/
def totalMap (A : Ty Γ) (σ : Lens Δ Γ) : Lens (Ty.total (A.sub σ)) (Ty.total A) where
  toFunA x := ⟨σ.toFunA x.1, x.2⟩
  toFunB _ y := y

/-- The lens of a substituted term, strictly. -/
theorem Tm.toLens_sub (a : Tm Γ A) (σ : Lens Δ Γ) :
    Lens.comp (totalMap A σ) (a.sub σ).toLens = Lens.comp a.toLens σ := rfl

/-- The agreement on the total container of a substituted type: the agreement of the images. -/
def Agree.pullTotal (σ : Lens Δ Γ) (RA : Agree (Ty.total A)) : Agree (Ty.total (A.sub σ)) :=
  fun x x' d => RA ⟨σ.toFunA x.1, x.2⟩ ⟨σ.toFunA x'.1, x'.2⟩ d

/-- **Soundness of a term for agreement.** The backward map of a term is unconstrained by the model;
this condition is a predicate added on the term. -/
def TermSound (RΓ : Agree Γ) (RA : Agree (Ty.total A)) (a : Tm Γ A) : Prop :=
  DepSound RΓ RA a.toLens

/-- Soundness of a term is stable under a dependency-sound substitution. -/
theorem TermSound.sub {RΓ : Agree Γ} {RΔ : Agree Δ} {RA : Agree (Ty.total A)} {a : Tm Γ A}
    {σ : Lens Δ Γ} (ha : TermSound RΓ RA a) (hσ : DepSound RΔ RΓ σ) :
    TermSound RΔ (Agree.pullTotal σ RA) (a.sub σ) :=
  fun d d' y h => ha _ _ y (hσ d d' _ h)

/-- A sound term as a morphism over pairs of runs. -/
def RunHom.ofTerm {RΓ : Agree Γ} {RA : Agree (Ty.total A)} (a : Tm Γ A)
    (h : TermSound RΓ RA a) : RunHom ⟨Γ, RΓ⟩ ⟨Ty.total A, RA⟩ :=
  ⟨DNLens.ofLens a.toLens, agreeSound_ofLens_iff.2 h⟩

/-- Equation (9) at the lens of a term: the predicate on the position demanded by `y` gives the
predicate at `y`. -/
theorem dnSound_ofLens_toLens_iff {RΓ : Pred Γ} {RA : Pred (Ty.total A)} {a : Tm Γ A} :
    DNSound RΓ RA (DNLens.ofLens a.toLens) ↔ ∀ γ y, RΓ γ (a.P γ y) → RA ⟨γ, a.S γ⟩ y :=
  ⟨fun h γ y hy => h γ y fun d hd => by
      rw [show d = a.P γ y from Multiset.mem_singleton.1 hd]
      exact hy,
    fun h γ y hy => h γ y (hy _ (Multiset.mem_singleton_self _))⟩

end Term

end CatCrypt.Container.CwF
