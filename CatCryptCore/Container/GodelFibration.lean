/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Container.CwFPi
public import Mathlib.CategoryTheory.Iso
public import CatCryptCore.ForMathlib.MultisetSum

/-!
# The Gödel fibration of the Diller–Nahm category

The base is `Type u`. The fibre over an index set `I` has the Dialectica predicates on `I`
(`DPred I`): a family of witness types `W i`, a family of counter-witness types `C i w`, and a
matrix of propositions `mat i w c`, read as `∃ w, ∀ c, mat i w c`. An entailment `φ ⟶ ψ` in the
fibre is a Diller–Nahm morphism over `I`: a forward map on witnesses and a backward map sending a
counter-witness of `ψ` to a finite multiset of counter-witnesses of `φ`, subject to equation (9)
of Moss and von Glehn (`DPred.Hom.toDNLens`, `DPred.Hom.dnSound`).

Reindexing along `h : J → I` is precomposition. The quantifiers over a family `K : I → Type u`
are `DPred.sigma` and `DPred.pi`, adjoint to reindexing along `Sigma.fst` on the left and on the
right, and both satisfy the Beck–Chevalley condition strictly. The fibre has conjunction and
implication, and implication is right adjoint to conjunction: in the Diller–Nahm form (multisets
of counter-witnesses) this holds without decidability of the matrices.

The fibration validates, as morphisms of a fibre, the principles of the Dialectica
interpretation: every predicate is isomorphic to its prenex form `∃ w ∀ c` of a quantifier-free
predicate (the characterisation of Gödel fibrations by Trotta, Spadetto and de Paiva), choice
(`∀ k ∃ l ↔ ∃ f ∀ k`), independence of premise for a universal premise, the Diller–Nahm form of
Markov's principle (finitely many candidates), contraction and weakening.

## Main definitions

* `DPred`, `DPred.holds`, `DPred.Hom` and the `Category` instance on the fibre;
* `DPred.reindex`, `DPred.reindexFunctor` — reindexing;
* `DPred.ofProp`, `DPred.top`, `DPred.and`, `DPred.imp`, `DPred.sigma`, `DPred.pi`,
  `DPred.sigmaFun`, `DPred.prenexForm`;
* `DPred.sigmaAdj`, `DPred.piAdj`, `DPred.impAdj` — `∃ ⊣ reindex ⊣ ∀`, `∧ ⊣ →`;
* `DPred.reindexSigmaIso`, `DPred.reindexPiIso` — Beck–Chevalley;
* `DPred.prenex`, `DPred.choice`, `DPred.ip`, `DPred.markovDN`, `DPred.contr`, `DPred.weak` —
  the validated principles;
* `DPred.equivTy` — a predicate on `I` is a type over the discrete context `disc I` of the
  polynomial model with a predicate on its total container.

## Main results

* `DPred.Hom.holds` — an entailment preserves the meaning;
* `DPred.Hom.dnSound` — an entailment is a Diller–Nahm morphism satisfying equation (9);
* `DPred.holds_ofProp`, `DPred.holds_sigma`, `DPred.holds_pi`, `DPred.holds_and`,
  `DPred.holds_imp` — the meaning of the connectives.

## References

* J. M. E. Hyland, *Proof theory in the abstract*, Annals of Pure and Applied Logic 114 (2002).
* D. Trotta, M. Spadetto, V. de Paiva, *Dialectica logical principles*, LFCS 2022, and
  *Gödel fibrations: a categorical characterisation of the Dialectica interpretation*.
* J. Diller, W. Nahm, *Eine Variante zur Dialectica-Interpretation der Heyting-Arithmetik
  endlicher Typen*, Archiv für mathematische Logik 16 (1974).
* P. Hofstra, *The dialectica monad and its cousins*, in Models, Logics, and Higher-Dimensional
  Categories, CRM Proceedings 53 (2011).
* S. Moss, T. von Glehn, *Dialectica models of type theory*, LICS 2018.

Search words: Gödel fibration, Dialectica predicate, Diller–Nahm, fibration, reindexing,
Beck–Chevalley, quantifier adjunction, independence of premise, Markov principle, choice,
Skolemisation, prenex form, contraction.
-/

set_option autoImplicit false

@[expose] public section

universe u

namespace CatCrypt.Container

open CategoryTheory

/-- A Dialectica predicate on `I`: witnesses, counter-witnesses, and a matrix of propositions. -/
structure DPred (I : Type u) : Type (u + 1) where
  /-- The witnesses at an index. -/
  W : I → Type u
  /-- The counter-witnesses of a witness. -/
  C : ∀ i, W i → Type u
  /-- The matrix: whether a witness withstands a counter-witness. -/
  mat : ∀ i (w : W i), C i w → Prop

namespace DPred

variable {I J : Type u}

/-- The meaning of a Dialectica predicate, `∃ w, ∀ c, mat i w c`. -/
def holds (φ : DPred I) (i : I) : Prop := ∃ w, ∀ c, φ.mat i w c

/-- Entailment in the fibre over `I`, in Diller–Nahm form: a forward map on witnesses, and a
backward map from a counter-witness of the conclusion to a finite multiset of counter-witnesses of
the premise, such that a witness withstanding all of them gives a witness withstanding the
counter-witness of the conclusion. -/
structure Hom (φ ψ : DPred I) : Type u where
  /-- The forward map on witnesses. -/
  fwd : ∀ i, φ.W i → ψ.W i
  /-- The backward map on counter-witnesses. -/
  back : ∀ i w, ψ.C i (fwd i w) → Multiset (φ.C i w)
  /-- Equation (9) of Moss and von Glehn. -/
  sound : ∀ i w c, (∀ x ∈ back i w c, φ.mat i w x) → ψ.mat i (fwd i w) c

namespace Hom

variable {φ ψ χ : DPred I}

/-- Entailments with equal forward maps and backward maps equal over them are equal. -/
theorem ext {f g : φ.Hom ψ} (hA : ∀ i w, f.fwd i w = g.fwd i w)
    (hB : ∀ i w c, f.back i w c = g.back i w (hA i w ▸ c)) : f = g := by
  obtain ⟨fA, fB, fS⟩ := f
  obtain ⟨gA, gB, gS⟩ := g
  obtain rfl : fA = gA := funext fun i => funext (hA i)
  obtain rfl : fB = gB := funext fun i => funext fun w => funext (hB i w)
  rfl

/-- The identity entailment: a counter-witness demands itself once. -/
protected def id (φ : DPred I) : φ.Hom φ where
  fwd _ w := w
  back _ _ c := {c}
  sound _ _ c h := h c (Multiset.mem_singleton_self c)

/-- The composite of entailments: the backward maps compose by the bind of multisets. -/
def comp (f : φ.Hom ψ) (g : ψ.Hom χ) : φ.Hom χ where
  fwd i w := g.fwd i (f.fwd i w)
  back i w c := (g.back i (f.fwd i w) c).bind (f.back i w)
  sound i w c h := g.sound i _ c fun y hy =>
    f.sound i w y fun x hx => h x (Multiset.mem_bind.2 ⟨y, hy, hx⟩)

/-- An entailment preserves the meaning. -/
theorem holds (f : φ.Hom ψ) (i : I) : φ.holds i → ψ.holds i := fun ⟨w, hw⟩ =>
  ⟨f.fwd i w, fun c => f.sound i w c fun x _ => hw x⟩

end Hom

/-- The fibre over `I`. -/
instance : Category (DPred I) where
  Hom := Hom
  id := Hom.id
  comp := Hom.comp
  id_comp f := Hom.ext (fun _ _ => rfl) fun _ _ _ =>
    (Multiset.bind_singleton _ (fun y => y)).trans (Multiset.map_id' _)
  comp_id f := Hom.ext (fun _ _ => rfl) fun _ _ _ => Multiset.singleton_bind _ _
  assoc f g h := Hom.ext (fun _ _ => rfl) fun _ _ _ => by simp [Hom.comp, Multiset.bind_assoc]

/-- Unfolding lemma of the `Category` instance: composition in the fibre is `Hom.comp`. -/
theorem comp_eq {φ ψ χ : DPred I} (f : φ ⟶ ψ) (g : ψ ⟶ χ) : f ≫ g = Hom.comp f g := rfl

/-- Unfolding lemma of the `Category` instance: the identity in the fibre is `Hom.id`. -/
theorem id_eq (φ : DPred I) : 𝟙 φ = Hom.id φ := rfl

/-! ## The polynomial model and the Diller–Nahm category -/

/-- A Dialectica predicate on `I` is a type over the discrete context `disc I` of the polynomial
model with a predicate on the positions of its total container. -/
def equivTy : DPred I ≃ Σ A : CwF.Ty (CwF.disc I), CwF.Pred (CwF.Ty.total A) where
  toFun φ := ⟨⟨φ.W, φ.C⟩, fun x c => φ.mat x.1 x.2 c⟩
  invFun A := ⟨A.1.S, A.1.P, fun i w c => A.2 ⟨i, w⟩ c⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The total container of a predicate: shapes are pairs of an index and a witness. -/
abbrev total (φ : DPred I) : PFunctor.{u, u} := CwF.Ty.total (equivTy φ).1

/-- The matrix of a predicate as a predicate on its total container. -/
abbrev pred (φ : DPred I) : CwF.Pred φ.total := (equivTy φ).2

/-- An entailment as a morphism of the Diller–Nahm category of the total containers. -/
def Hom.toDNLens {φ ψ : DPred I} (f : φ.Hom ψ) : DNLens φ.total ψ.total where
  toFunA x := ⟨x.1, f.fwd x.1 x.2⟩
  toFunB x c := f.back x.1 x.2 c

/-- An entailment satisfies equation (9) of Moss and von Glehn on the total containers. -/
theorem Hom.dnSound {φ ψ : DPred I} (f : φ.Hom ψ) : CwF.DNSound φ.pred ψ.pred f.toDNLens :=
  fun x c h => f.sound x.1 x.2 c h

/-! ## Reindexing -/

/-- Reindexing along `h : J → I`. -/
def reindex (h : J → I) (φ : DPred I) : DPred J where
  W j := φ.W (h j)
  C j w := φ.C (h j) w
  mat j w c := φ.mat (h j) w c

/-- Reindexing of an entailment. -/
def Hom.reindex (h : J → I) {φ ψ : DPred I} (f : φ.Hom ψ) :
    (φ.reindex h).Hom (ψ.reindex h) where
  fwd j w := f.fwd (h j) w
  back j w c := f.back (h j) w c
  sound j w c hc := f.sound (h j) w c hc

/-- Reindexing as a functor between fibres. -/
def reindexFunctor (h : J → I) : DPred I ⥤ DPred J where
  obj := reindex h
  map f := Hom.reindex h f
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Unfolding lemma of `reindex`: the meaning of a reindexed predicate. -/
theorem holds_reindex (h : J → I) (φ : DPred I) (j : J) :
    (φ.reindex h).holds j ↔ φ.holds (h j) := Iff.rfl

/-! ## Connectives -/

/-- A proposition on `I` as a predicate with trivial witnesses and counter-witnesses. -/
def ofProp (p : I → Prop) : DPred I where
  W _ := PUnit
  C _ _ := PUnit
  mat i _ _ := p i

/-- The meaning of `ofProp p` is `p`. -/
theorem holds_ofProp (p : I → Prop) (i : I) : (ofProp p).holds i ↔ p i :=
  ⟨fun ⟨_, h⟩ => h PUnit.unit, fun h => ⟨PUnit.unit, fun _ => h⟩⟩

/-- The true predicate. -/
def top : DPred I := ofProp fun _ => True

/-- Conjunction: pairs of witnesses, and a counter-witness of either component. -/
def and (φ ψ : DPred I) : DPred I where
  W i := φ.W i × ψ.W i
  C i w := φ.C i w.1 ⊕ ψ.C i w.2
  mat i w := Sum.elim (φ.mat i w.1) (ψ.mat i w.2)

/-- The meaning of a conjunction. -/
theorem holds_and (φ ψ : DPred I) (i : I) :
    (DPred.and φ ψ).holds i ↔ φ.holds i ∧ ψ.holds i := by
  constructor
  · rintro ⟨⟨w, v⟩, h⟩
    exact ⟨⟨w, fun c => h (.inl c)⟩, ⟨v, fun c => h (.inr c)⟩⟩
  · rintro ⟨⟨w, hw⟩, ⟨v, hv⟩⟩
    exact ⟨⟨w, v⟩, fun c => c.casesOn hw hv⟩

/-- Implication, Diller–Nahm form: a witness is a morphism of the fibres at `i`, a forward map
and a backward map into finite multisets; a counter-witness is a witness of the premise and a
counter-witness of the conclusion at its image. -/
def imp (φ ψ : DPred I) : DPred I where
  W i := Σ f : φ.W i → ψ.W i, ∀ w, ψ.C i (f w) → Multiset (φ.C i w)
  C i F := Σ w : φ.W i, ψ.C i (F.1 w)
  mat i F c := (∀ x ∈ F.2 c.1 c.2, φ.mat i c.1 x) → ψ.mat i (F.1 c.1) c.2

/-- A witness of an implication sends the meaning of the premise to that of the conclusion. -/
theorem holds_imp (φ ψ : DPred I) (i : I) (h : (imp φ ψ).holds i) (hφ : φ.holds i) :
    ψ.holds i := by
  obtain ⟨F, hF⟩ := h
  obtain ⟨w, hw⟩ := hφ
  exact ⟨F.1 w, fun c => hF ⟨w, c⟩ fun x _ => hw x⟩

section Quantifiers

variable {K : I → Type u}

/-- The existential quantifier over a family `K`. -/
def sigma (φ : DPred (Σ i, K i)) : DPred I where
  W i := Σ k : K i, φ.W ⟨i, k⟩
  C i w := φ.C ⟨i, w.1⟩ w.2
  mat i w c := φ.mat ⟨i, w.1⟩ w.2 c

/-- The universal quantifier over a family `K`: a witness for each `k`, and a counter-witness at
one `k`. -/
def pi (φ : DPred (Σ i, K i)) : DPred I where
  W i := ∀ k : K i, φ.W ⟨i, k⟩
  C i w := Σ k : K i, φ.C ⟨i, k⟩ (w k)
  mat i w c := φ.mat ⟨i, c.1⟩ (w c.1) c.2

/-- The meaning of an existential quantifier. -/
theorem holds_sigma (φ : DPred (Σ i, K i)) (i : I) :
    (sigma φ).holds i ↔ ∃ k, φ.holds ⟨i, k⟩ := by
  constructor
  · rintro ⟨⟨k, w⟩, h⟩
    exact ⟨k, w, h⟩
  · rintro ⟨k, w, h⟩
    exact ⟨⟨k, w⟩, h⟩

/-- The meaning of a universal quantifier. -/
theorem holds_pi (φ : DPred (Σ i, K i)) (i : I) :
    (pi φ).holds i ↔ ∀ k, φ.holds ⟨i, k⟩ := by
  constructor
  · rintro ⟨w, h⟩ k
    exact ⟨w k, fun c => h ⟨k, c⟩⟩
  · intro h
    choose w hw using h
    exact ⟨w, fun c => hw c.1 c.2⟩

/-- `∃ ⊣ reindex`: entailments out of `sigma φ` are entailments out of `φ` into the reindexing
along `Sigma.fst`. -/
def sigmaAdj (φ : DPred (Σ i, K i)) (ψ : DPred I) :
    (sigma φ).Hom ψ ≃ φ.Hom (ψ.reindex Sigma.fst) where
  toFun f :=
    { fwd x w := f.fwd x.1 ⟨x.2, w⟩
      back x w c := f.back x.1 ⟨x.2, w⟩ c
      sound x w c h := f.sound x.1 ⟨x.2, w⟩ c h }
  invFun g :=
    { fwd i w := g.fwd ⟨i, w.1⟩ w.2
      back i w c := g.back ⟨i, w.1⟩ w.2 c
      sound i w c h := g.sound ⟨i, w.1⟩ w.2 c h }
  left_inv _ := rfl
  right_inv _ := rfl

/-- `reindex ⊣ ∀`: entailments into `pi φ` are entailments from the reindexing along
`Sigma.fst` into `φ`. -/
def piAdj (ψ : DPred I) (φ : DPred (Σ i, K i)) :
    ψ.Hom (pi φ) ≃ (ψ.reindex Sigma.fst).Hom φ where
  toFun f :=
    { fwd x w := f.fwd x.1 w x.2
      back x w c := f.back x.1 w ⟨x.2, c⟩
      sound x w c h := f.sound x.1 w ⟨x.2, c⟩ h }
  invFun g :=
    { fwd i w k := g.fwd ⟨i, k⟩ w
      back i w c := g.back ⟨i, c.1⟩ w c.2
      sound i w c h := g.sound ⟨i, c.1⟩ w c.2 h }
  left_inv _ := rfl
  right_inv _ := rfl

/-- Beck–Chevalley for `∃`: reindexing commutes with the existential quantifier, strictly. -/
def reindexSigmaIso (h : J → I) (φ : DPred (Σ i, K i)) :
    (sigma φ).reindex h ≅ sigma (K := fun j => K (h j)) (φ.reindex fun x => ⟨h x.1, x.2⟩) :=
  Iso.refl _

/-- Beck–Chevalley for `∀`: reindexing commutes with the universal quantifier, strictly. -/
def reindexPiIso (h : J → I) (φ : DPred (Σ i, K i)) :
    (pi φ).reindex h ≅ pi (K := fun j => K (h j)) (φ.reindex fun x => ⟨h x.1, x.2⟩) :=
  Iso.refl _

end Quantifiers

/-! ## Implication is right adjoint to conjunction -/

/-- `∧ ⊣ →`: the fibre is cartesian closed. The backward map of an entailment out of a
conjunction is split into its left and right parts; no decision on the matrices is needed. -/
def impAdj (χ φ ψ : DPred I) : (DPred.and χ φ).Hom ψ ≃ χ.Hom (imp φ ψ) where
  toFun h :=
    { fwd i x := ⟨fun w => h.fwd i (x, w), fun w c => (h.back i (x, w) c).filterMap Sum.getRight?⟩
      back i x c := (h.back i (x, c.1) c.2).filterMap Sum.getLeft?
      sound i x c hx hz := h.sound i (x, c.1) c.2 fun y hy => by
        cases y with
        | inl a => exact hx a ((Multiset.mem_filterMap _ _).2 ⟨.inl a, hy, rfl⟩)
        | inr b => exact hz b ((Multiset.mem_filterMap _ _).2 ⟨.inr b, hy, rfl⟩) }
  invFun g :=
    { fwd i w := (g.fwd i w.1).1 w.2
      back i w c := (g.back i w.1 ⟨w.2, c⟩).map Sum.inl + ((g.fwd i w.1).2 w.2 c).map Sum.inr
      sound i w c hy := g.sound i w.1 ⟨w.2, c⟩
        (fun a ha => hy (.inl a) (Multiset.mem_add.2 (.inl (Multiset.mem_map_of_mem _ ha))))
        (fun b hb => hy (.inr b) (Multiset.mem_add.2 (.inr (Multiset.mem_map_of_mem _ hb)))) }
  left_inv h := Hom.ext (fun _ _ => rfl) fun _ _ _ =>
    Multiset.map_filterMap_getLeft_add_getRight _
  right_inv g := by
    refine Hom.ext (fun i x => Sigma.ext rfl (heq_of_eq (funext fun w => funext fun c =>
      Multiset.filterMap_getRight_map_add _ _))) fun i x c => ?_
    refine (Multiset.filterMap_getLeft_map_add _ _).trans ?_
    congr 1
    change c = _
    grind

/-! ## The validated principles -/

section Principles

variable {K : I → Type u}

/-- The prenex form `∃ w ∀ c, mat i w c` of a predicate, built from `ofProp` on the total sort of
counter-witnesses by `sigma` and `pi`. -/
def prenexForm (φ : DPred I) : DPred I :=
  sigma (K := φ.W) (pi (K := fun x : Σ i, φ.W i => φ.C x.1 x.2)
    (ofProp fun y => φ.mat y.1.1 y.1.2 y.2))

/-- Every predicate is isomorphic to the `∃ ∀` of a quantifier-free predicate. -/
def prenex (φ : DPred I) : φ ≅ prenexForm φ where
  hom :=
    { fwd _ w := ⟨w, fun _ => PUnit.unit⟩
      back _ _ c := {c.1}
      sound _ _ c h := h c.1 (Multiset.mem_singleton_self _) }
  inv :=
    { fwd _ w := w.1
      back _ _ c := {⟨c, PUnit.unit⟩}
      sound _ _ c h := h ⟨c, PUnit.unit⟩ (Multiset.mem_singleton_self _) }
  hom_inv_id := Hom.ext (fun _ _ => rfl) fun _ _ _ => rfl
  inv_hom_id := Hom.ext (fun _ _ => rfl) fun _ _ _ => rfl

/-- The choice form `∃ f ∀ k, φ (k, f k)`: the existential quantifier ranges over choice
functions `f : ∀ k : K i, L ⟨i, k⟩`. -/
def sigmaFun {L : (Σ i, K i) → Type u} (φ : DPred (Σ x : Σ i, K i, L x)) : DPred I :=
  sigma (K := fun i => ∀ k : K i, L ⟨i, k⟩)
    (pi (K := fun p => K p.1) (φ.reindex fun y => ⟨⟨y.1.1, y.2⟩, y.1.2 y.2⟩))

/-- Choice (Skolemisation): `∀ k ∃ l, φ` is isomorphic to `∃ f ∀ k, φ (k, f k)`. -/
def choice {L : (Σ i, K i) → Type u} (φ : DPred (Σ x : Σ i, K i, L x)) :
    pi (sigma φ) ≅ sigmaFun φ where
  hom :=
    { fwd _ w := ⟨fun k => (w k).1, fun k => (w k).2⟩
      back _ _ c := {c}
      sound _ _ c h := h c (Multiset.mem_singleton_self _) }
  inv :=
    { fwd _ w k := ⟨w.1 k, w.2 k⟩
      back _ _ c := {c}
      sound _ _ c h := h c (Multiset.mem_singleton_self _) }
  hom_inv_id := Hom.ext (fun _ _ => rfl) fun _ _ _ => Multiset.singleton_bind _ _
  inv_hom_id := Hom.ext (fun _ _ => rfl) fun _ _ _ => Multiset.singleton_bind _ _

/-- The canonical witness of a universally quantified proposition. -/
abbrev unitW (K : I → Type u) (i : I) : ∀ _ : K i, PUnit.{u + 1} := fun _ => PUnit.unit

/-- Independence of premise for a universal premise: from `(∀ k, p) → ∃ l, ψ` follows
`∃ l, (∀ k, p) → ψ`. -/
def ip {L : I → Type u} (p : (Σ i, K i) → Prop) (ψ : DPred (Σ i, L i)) :
    imp (pi (ofProp p)) (sigma ψ) ⟶
      sigma (imp ((pi (ofProp p)).reindex Sigma.fst) ψ) where
  fwd i F := ⟨(F.1 (unitW K i)).1, fun _ => (F.1 (unitW K i)).2, fun _ c => F.2 (unitW K i) c⟩
  back i _ c := {⟨unitW K i, c.2⟩}
  sound _ _ _ h hx := h _ (Multiset.mem_singleton_self _) hx

/-- Markov's principle, Diller–Nahm form: from `(∀ k, p k) → q` follows the existence of a finite
multiset `m` of candidates with `(∀ k ∈ m, p k) → q`. -/
def markovDN (p : (Σ i, K i) → Prop) (q : I → Prop) :
    imp (pi (ofProp p)) (ofProp q) ⟶
      sigma (K := fun i => Multiset (K i)) (ofProp fun x => (∀ k ∈ x.2, p ⟨x.1, k⟩) → q x.1) where
  fwd i F := ⟨(F.2 (unitW K i) PUnit.unit).map Sigma.fst, PUnit.unit⟩
  back i _ _ := {⟨unitW K i, PUnit.unit⟩}
  sound _ _ _ h hk := h _ (Multiset.mem_singleton_self _) fun _ hx =>
    hk _ (Multiset.mem_map_of_mem _ hx)

/-- Contraction: a counter-witness of either copy demands itself once. No decision on the matrix
is needed. -/
def contr (φ : DPred I) : φ ⟶ DPred.and φ φ where
  fwd _ w := (w, w)
  back _ _ c := Sum.elim (fun x => {x}) (fun x => {x}) c
  sound _ _ c h := by
    cases c with
    | inl x => exact h x (Multiset.mem_singleton_self _)
    | inr x => exact h x (Multiset.mem_singleton_self _)

/-- Weakening: the true predicate demands nothing. -/
def weak (φ : DPred I) : φ ⟶ top where
  fwd _ _ := PUnit.unit
  back _ _ _ := 0
  sound _ _ _ _ := trivial

end Principles

end DPred

end CatCrypt.Container
