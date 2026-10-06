/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.SetTheory.Cardinal.Finite
public import CatCryptCore.Category.ProtBicat
public import CatCryptCore.Crypto.UCMonad.LeakageExceptT
public import CatCryptCore.XDijkstra.GradedWP

@[expose] public section

set_option autoImplicit false

/-!
# coPara leakage ↔ graded-`ExceptT`: the construction-level correspondence

A leaky protocol 1-cell has two presentations:

* the **coPara leakage** presentation (`ProtBicat`): a 1-cell `a ⟶ b` is a
  `ProtObj T a b`, i.e. an interface type `I := iface` together with a map
  `prot : a → T (b ⊕ I)`. The leakage/interface coparameter `I` **accumulates
  under horizontal composition**: `(P.hcomp Q).iface = P.iface ⊕ Q.iface`
  (`ProtObj.hcomp`, Capucci–Gavranović coPara over the cocartesian Kleisli
  category);
* the **graded-`ExceptT`** presentation: the leakage output is the
  exception branch — `T (b ⊕ I) ≃ ExceptT I T b` pointwise (`leakEquiv`) — and
  composition is graded, the grade **adding** monoidally (`GradedWP.gbind`
  produces grade `g₁ + g₂`).

The pointwise 1-cell iso `leakEquiv` is defined in `LeakageExceptT`. This module
adds two *construction-level* correspondence facts and states what remains open.

## What is proved here

1. **1-cell correspondence.** A coPara-shaped underlying map `π : a → T (b ⊕ I)`
   transports to its graded-`ExceptT` image `a → ExceptT I T b` by applying
   `leakEquiv` on outputs (`coParaToExceptT`); this transport is an *equivalence*
   of the two 1-cell function types (`coParaExceptTEquiv`, via
   `Equiv.arrowCongr` on `leakEquiv`). At the `ProtObj` level this is
   `ProtObj.toExceptTCell`. All of this is definitional over `leakEquiv`.

2. **Composition accumulation.** The coPara composite's interface is the
   coproduct of the components' interfaces — `hcomp_iface`:
   `(P.hcomp Q).iface = P.iface ⊕ Q.iface`, definitionally. This is the
   interface *accumulation* under composition, stated at the **monoidal / `Sum`
   level**.

3. **The `ℕ`-size grade bridge to `gbind`.** The monoidal coproduct
   accumulation maps onto `GradedWP.gbind`'s additive grade through the
   **interface-size functor** `Nat.card`: for finite interfaces,
   `ifaceGrade (P.hcomp Q) = ifaceGrade P + ifaceGrade Q` (`ifaceGrade_hcomp`,
   from `Nat.card_sum`). This is the `(ℕ, +, 0)` — i.e. `AddCommMonoid` —
   identity, matching `gbind`'s grade addition `g₁ + g₂` exactly: the composite
   size-grade is definitionally the grade of the `gbind` of the two component
   size-graded transformers (`hcompGradedTransport`).

So: coPara ≅ graded-`ExceptT` **at the 1-cell level** (via `leakEquiv`), and
**at the composition level** the interface accumulates — *monoidally* by `⊕`
(`hcomp_iface`) and, after applying the `Nat.card` size functor, *additively* in
`(ℕ, +, 0)` matching `gbind` (`ifaceGrade_hcomp` / `hcompGradedTransport`).

## What is not proved here

The interface grade in its native form is `(Type, ⊕, Empty)` — a **symmetric
monoidal** structure (coproduct, unit `Empty`, associativity/commutativity/
unitality only *up to iso*), **not** a strict `AddCommMonoid`. `GradedWP` is
graded over `[AddCommMonoid G] [Preorder G]`, so the interface coproduct cannot
be plugged in *as* the grade directly; it must be pushed through a monoid-valued
functor — here `Nat.card`, landing in `(ℕ, +, 0)`. Consequently:

* the additive `gbind` bridge is available only for the **size** grade (or, more
  generally, any monoidal functor `Type → G` into an `AddCommMonoid`), **not**
  for the raw type-level interface; and
* the full **biequivalence** `ProtBicat T ≃ Kleisli(graded-ExceptT)` — carrying
  the 2-cells (`ProtMor` simulators) and the coherence data across, and the
  question of whether the type-level `⊕` interface can itself be organised as an
  `AddCommMonoid`-graded structure without collapsing to a size — is **not**
  established here.

## Main results

* `coParaExceptTEquiv`, `coParaToExceptT_eq`: a 1-cell `a → T (b ⊕ I)` is a Kleisli arrow
  of `ExceptT I T`.
* `hcomp_iface`, `ifaceGrade_hcomp`: the interface size is additive under horizontal
  composition.
* `coPara_gradedExceptT_correspondence`: the correspondence of 1-cells with graded
  `ExceptT` arrows, with composition and grade.
-/

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open UCMonad

variable {T : Type → Type} [UCMonadBase T]

/-! ## 1. The 1-cell correspondence

A coPara-shaped underlying map `a → T (b ⊕ I)` transports, pointwise on its
outputs, to a graded-`ExceptT` map `a → ExceptT I T b` via `leakEquiv`. Since
`leakEquiv T b I` is an `Equiv`, the transport is itself an equivalence of the
two 1-cell function types. `UCMonadBase T` supplies the `Monad`/`LawfulMonad`
instances `leakEquiv` requires. -/

/-- **1-cell transport.** The graded-`ExceptT` image of a coPara-shaped underlying
    map `π : a → T (b ⊕ I)`: apply the leakage↔exception iso `leakEquiv` on each
    output. A normal result stays a success value; a leaked value becomes the
    exception. -/
def coParaToExceptT {a b I : Type} (π : a → T (b ⊕ I)) : a → ExceptT I T b :=
  fun x => leakEquiv T b I (π x)

/-- **The 1-cell correspondence is an equivalence.** The two presentations of a
    leaky 1-cell — coPara `a → T (b ⊕ I)` and graded-`ExceptT`
    `a → ExceptT I T b` — are isomorphic, pointwise via `leakEquiv`. -/
def coParaExceptTEquiv (a b I : Type) :
    (a → T (b ⊕ I)) ≃ (a → ExceptT I T b) :=
  Equiv.arrowCongr (Equiv.refl a) (leakEquiv T b I)

/-- `coParaToExceptT` is the forward direction of the equivalence
    `coParaExceptTEquiv`. -/
theorem coParaToExceptT_eq {a b I : Type} (π : a → T (b ⊕ I)) :
    coParaToExceptT π = coParaExceptTEquiv (T := T) a b I π := rfl

/-- **1-cell correspondence at the `ProtObj` level.** A protocol 1-cell
    `P : ProtObj T a b`, whose interface coparameter is `P.iface`, has
    graded-`ExceptT` image `a → ExceptT P.iface T b` — its underlying map
    transported by `leakEquiv`. -/
def ProtObj.toExceptTCell {a b : Type} (P : ProtObj T a b) :
    a → ExceptT P.iface T b :=
  coParaToExceptT P.prot

/-! ## 2. Composition accumulation, at the monoidal (`Sum`) level

Horizontal composition of coPara 1-cells accumulates their interfaces via the
coproduct. This is definitional in `ProtObj.hcomp`. -/

/-- **Interface accumulation (monoidal level).** The coPara composite's interface
    coparameter is the coproduct of the components' — the interface *accumulates*
    under horizontal composition. This is the `Sum`/monoidal-level accumulation
    statement; it holds definitionally. -/
theorem hcomp_iface {a b c : Type} (P : ProtObj T a b) (Q : ProtObj T b c) :
    (P.hcomp Q).iface = (P.iface ⊕ Q.iface) := rfl

/-! ## 3. The `ℕ`-size grade bridge to `GradedWP.gbind`

The type-level `⊕` accumulation maps onto `gbind`'s **additive** grade through
the interface-size functor `Nat.card : Type → ℕ`. For finite interfaces this is
`Nat.card_sum`, an `AddCommMonoid ℕ` identity. -/

/-- **The interface-size grade** of a coPara 1-cell: the number of leakage
    components (`Nat.card` of its interface). This is the monoid-valued image of
    the type-level interface — the grade that plugs into `GradedWP`
    (`AddCommMonoid ℕ`). -/
noncomputable def ifaceGrade {a b : Type} (P : ProtObj T a b) : ℕ :=
  Nat.card P.iface

/-- **Interface size adds under composition.** The `Nat.card` image of the
    `⊕`-accumulation `(P.hcomp Q).iface = P.iface ⊕ Q.iface` is the additive
    identity `ifaceGrade (P.hcomp Q) = ifaceGrade P + ifaceGrade Q` in
    `(ℕ, +, 0)`. This is the `AddCommMonoid` correspondent of the monoidal
    coproduct accumulation, and it matches `gbind`'s grade addition `g₁ + g₂`. -/
theorem ifaceGrade_hcomp {a b c : Type} (P : ProtObj T a b) (Q : ProtObj T b c)
    [Finite P.iface] [Finite Q.iface] :
    ifaceGrade (P.hcomp Q) = ifaceGrade P + ifaceGrade Q := by
  show Nat.card ((P.hcomp Q).iface) = Nat.card P.iface + Nat.card Q.iface
  rw [hcomp_iface P Q]
  exact Nat.card_sum

/-- **The composite size-grade is `gbind`'s grade.** A transformer graded by the
    composite's interface size `ifaceGrade (P.hcomp Q)` is obtained by
    `GradedWP.gbind` of two component transformers graded by `ifaceGrade P` and
    `ifaceGrade Q` — `gbind` produces grade `ifaceGrade P + ifaceGrade Q`, which
    by `ifaceGrade_hcomp` is exactly `ifaceGrade (P.hcomp Q)`. This exhibits the
    monoidal `⊕`-accumulation of interfaces as `gbind`'s additive grade under the
    `Nat.card` size functor.

    (The transformer *contents* are immaterial — the point is the grade
    bookkeeping — so the two stages are built from `gpure` reindexed up to the
    component grade via `gweaken`.) -/
noncomputable def hcompGradedTransport {a b c : Type}
    (P : ProtObj T a b) (Q : ProtObj T b c)
    [Finite P.iface] [Finite Q.iface]
    {α β : Type} (a₀ : α) (b₀ : β) :
    GradedWP.GPredTrans (ifaceGrade (P.hcomp Q)) β :=
  ifaceGrade_hcomp P Q ▸
    GradedWP.gbind
      (GradedWP.gweaken (Nat.zero_le (ifaceGrade P)) (GradedWP.gpure a₀) :
        GradedWP.GPredTrans (ifaceGrade P) α)
      (fun _ => (GradedWP.gweaken (Nat.zero_le (ifaceGrade Q)) (GradedWP.gpure b₀) :
        GradedWP.GPredTrans (ifaceGrade Q) β))

/-! ## 4. Summary

The two presentations agree **at the 1-cell level** (an `Equiv`,
`coParaExceptTEquiv`), and **at the composition level** the interface
accumulates — monoidally by `⊕` (`hcomp_iface`) and additively in `(ℕ, +, 0)`
after `Nat.card` (`ifaceGrade_hcomp`), matching `gbind`. The open statements (raw
type-level `⊕` as an `AddCommMonoid` grade without a size collapse; the full
biequivalence carrying 2-cells) are recorded in the module docstring. -/

/-- **Summary of the construction-level correspondence.** Packages the two facts
    that hold: the 1-cell function types are equivalent (`coParaExceptTEquiv`,
    the pointwise `leakEquiv` iso), and interface size adds under composition
    (`ifaceGrade_hcomp`, the `Nat.card` image of the `⊕`-accumulation, matching
    `gbind`'s grade addition). -/
theorem coPara_gradedExceptT_correspondence
    {a b c : Type} (P : ProtObj T a b) (Q : ProtObj T b c)
    [Finite P.iface] [Finite Q.iface] :
    (Nonempty ((a → T (b ⊕ P.iface)) ≃ (a → ExceptT P.iface T b)))
      ∧ ifaceGrade (P.hcomp Q) = ifaceGrade P + ifaceGrade Q :=
  ⟨⟨coParaExceptTEquiv (T := T) a b P.iface⟩, ifaceGrade_hcomp P Q⟩

end CatCrypt.Crypto.SecureCompilation.Ascent
