/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Complexity.D.DillerNahm
public import CatCryptCore.Container.PolyNaturalModel

/-!
# The types of D in the polynomial model

The codes `Ty` of D with their values `Val` form a universe in the sense of Awodey's natural
models (`PFunctor.NaturalModel.univPoly Val`), and so do the codes with their translated values
`Ty.hat`, the shapes of the Diller–Nahm interpretation of `CatCrypt.Complexity.D.DillerNahm`.
The type formers of D are the structures of the polynomial model on these universes:

* `Ty.pi f B` and `Ty.sig f B` (D2) are the Π- and Σ-codes of the model at the finite ground
  codes `base f`: cartesian maps from the polynomials of families over a finite ground index into
  the universe polynomial (`piStr`, `sigStr`, `piStrHat`, `sigStrHat`), whose fibre equivalences
  are identities, so that Awodey's pullback square holds (`CartLens.pullbackEquiv`). The domain of
  a code of D ranges over a type defined before `Ty` (`FTy.den`): codes over arbitrary codes would
  make `Ty` and `Val` inductive-recursive.
* `Ty.mu S` (D1) and `Ty.imu f S i` (D3) are W-codes: the values of `mu S` are Mathlib's `WType`
  of the container `Sig.den S` and those of `imu f S i` the indexed W-type `Container.IPW` of the
  indexed container `ISig.cont S` (`wStr`, `iwStr`).
* A function type translates to the costed function `Container.Costed` of the Diller–Nahm model
  (`Ty.hat (.arr a b) = Costed a.hat b.hat`), whose morphism is `Costed.toDN`.

The logical relation `Sim` of the translation is the relation of the model at each former: the
dependent product of the relations at `pi` (`Sim.pi_iff`), their dependent sum over equal indices
at `sig` (`Sim.sig_iff`), the relator `Container.WLift` of the W-type at `mu` (by definition), and
at a function type the bound of the evaluation by the demand of the Diller–Nahm morphism of the
costed function (`Sim.arr_iff_demand`): at related arguments, a leaf after at most the clock
ticks that a data token of the output demands, at a value related to the forward map.

## Main definitions

* `finPiPoly`, `finSigPoly`: the polynomials of families of codes over a finite ground index
* `piStr`, `sigStr`, `piStrHat`, `sigStrHat`: the Π- and Σ-structures of D
* `ISig.cont`: the indexed container of an indexed signature
* `wPoly`, `iwPoly`, `wStr`, `iwStr`: the W-codes of D

## Main results

* `Sim.pi_iff`, `Sim.sig_iff`, `Sim.arr_iff_demand`

## References

* S. Awodey, *Natural models of homotopy type theory*, MSCS 28 (2018);
* T. von Glehn, *Polynomials and models of type theory*, PhD thesis, Cambridge, 2015;
* S. Moss, T. von Glehn, *Dialectica models of type theory*, LICS 2018, §8.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Complexity.D

open PFunctor PFunctor.NaturalModel CatCrypt.Container

/-! ## Π and Σ at the finite ground codes -/

/-- The polynomial of the families of codes over a finite ground index, with the dependent
functions into an interpretation `El` of the codes as directions: the part of Awodey's
`piPoly El` at the codes `base f`. -/
def finPiPoly (El : Ty → Type) : PFunctor.{0, 0} :=
  ⟨Σ f : FTy, f.den → Ty, fun c => ∀ x : c.1.den, El (c.2 x)⟩

/-- The polynomial of the families of codes over a finite ground index, with the dependent pairs
of an interpretation `El` of the codes as directions: the part of `univPoly El ◃ univPoly El` at
the codes `base f`. -/
def finSigPoly (El : Ty → Type) : PFunctor.{0, 0} :=
  ⟨Σ f : FTy, f.den → Ty, fun c => Σ x : c.1.den, El (c.2 x)⟩

/-- The Π-structure of the values of D at the finite ground codes: the code `pi f B`, whose values
are the dependent functions. -/
def piStr : CartLens (finPiPoly Val) (univPoly Val) :=
  ⟨fun c => .pi c.1 c.2, fun _ => Equiv.refl _⟩

/-- The Σ-structure of the values of D at the finite ground codes: the code `sig f B`, whose
values are the dependent pairs. -/
def sigStr : CartLens (finSigPoly Val) (univPoly Val) :=
  ⟨fun c => .sig c.1 c.2, fun _ => Equiv.refl _⟩

/-- The Π-structure of the translated values: a table of translated components. -/
def piStrHat : CartLens (finPiPoly Ty.hat) (univPoly Ty.hat) :=
  ⟨fun c => .pi c.1 c.2, fun _ => Equiv.refl _⟩

/-- The Σ-structure of the translated values: a dependent pair of an index and a translated
value. -/
def sigStrHat : CartLens (finSigPoly Ty.hat) (univPoly Ty.hat) :=
  ⟨fun c => .sig c.1 c.2, fun _ => Equiv.refl _⟩

/-! ## W-codes -/

/-- The indexed container of a family of indexed signatures: at an index, a constructor with its
field; positions those of the constructor; the child at a position at the index it names. -/
def ISig.cont {f : FTy} (S : f.den → ISig f) : IPFunctor.{0, 0, 0, 0} f.den f.den :=
  ⟨fun j => (c : (S j).Ctor) × (S j).Fld c, fun j a => (S j).Pos a.1, fun j a p => (S j).nx a.1 p⟩

/-- The polynomial of the W-codes: a signature, with the values of the W-type of its container as
directions. -/
def wPoly : PFunctor.{0, 0} := ⟨Sig, fun S => (Sig.den S).W⟩

/-- The polynomial of the indexed W-codes: a family of indexed signatures over a finite ground
index and an index, with the values of the indexed W-type of its container as directions. -/
def iwPoly : PFunctor.{0, 0} :=
  ⟨Σ f : FTy, (f.den → ISig f) × f.den, fun c => IPW (ISig.cont c.2.1) c.2.2⟩

/-- The W-codes of D: the values of `mu S` are the W-type of the container of `S`. -/
def wStr : CartLens wPoly (univPoly Val) :=
  ⟨fun S => .mu S, fun _ => Equiv.refl _⟩

/-- The indexed W-codes of D: the values of `imu f S i` are the indexed W-type of the indexed
container of `S` at `i`. -/
def iwStr : CartLens iwPoly (univPoly Val) :=
  ⟨fun c => .imu c.1 c.2.1 c.2.2, fun _ => Equiv.refl _⟩

/-! ## The logical relation -/

/-- `Sim` at a dependent product is the dependent product of the relations. -/
theorem Sim.pi_iff {f : FTy} {B : f.den → Ty} {u : Ty.hat (.pi f B)} {v : Val (.pi f B)} :
    Sim (.pi f B) u v ↔ ∀ j, Sim (B j) (u j) (v j) :=
  Iff.rfl

/-- `Sim` at a dependent sum is the relation at a common index. -/
theorem Sim.sig_iff {f : FTy} {B : f.den → Ty} {u : Ty.hat (.sig f B)} {v : Val (.sig f B)} :
    Sim (.sig f B) u v ↔ ∃ e : u.1 = v.1, Sim (B v.1) (e ▸ u.2) v.2 :=
  Iff.rfl

/-- `Sim` at a function type is the bound of the evaluation by the Diller–Nahm morphism of the
costed function: at related arguments, the D function is a leaf after at most the clock ticks that
a data token of the output demands, at a value related to the forward map. -/
theorem Sim.arr_iff_demand {a b : Ty} {p : Ty.hat (.arr a b)} {g : Val (.arr a b)} :
    Sim (.arr a b) p g ↔ ∀ u v, Sim a u v → ∃ m w, g v = stepN CTree.tick m (.ret w) ∧
      m ≤ ((Costed.toDN p).toFunB u false).count true ∧ Sim b ((Costed.toDN p).toFunA u) w := by
  have hc : ∀ u, ((Costed.toDN p).toFunB u false).count true = p.2 u :=
    fun u => Clocked.count_true_toDN (Costed.toClocked p) u
  constructor
  · intro h u v huv
    obtain ⟨m, w, h1, h2, h3⟩ := h u v huv
    exact ⟨m, w, h1, (hc u).symm ▸ h2, h3⟩
  · intro h u v huv
    obtain ⟨m, w, h1, h2, h3⟩ := h u v huv
    exact ⟨m, w, h1, hc u ▸ h2, h3⟩

end CatCrypt.Complexity.D
