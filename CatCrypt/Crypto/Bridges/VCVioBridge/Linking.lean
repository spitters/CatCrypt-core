/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Bridges.VCVioBridge.State

/-!
# VCVio Bridge — Package Linking ≡ simulateQ (Phase 3)

Realizes the SSP "package algebra" as the Kleisli bicategory of VCVio's free-monad
adjunction on polynomial functors.

## Background

An SSP package with imports `I` and exports `E` is (categorically) a natural
transformation `P_E ⇒ FreeP_I`, equivalently a family

    (e : E.Domain) → OracleComp I (E.Range e)

which is definitionally VCVio's `QueryImpl E (OracleComp I)`. Package linking is
composition in the Kleisli bicategory of the free-monad adjunction, and via the
universal property `MonadHom(FreeP, M) ≅ Nat(P, M)` it is literally `simulateQ`.

Upstream VCVio's `QueryImpl.compose` (notation `∘ₛ`) fixes the middle spec's
index to `Type 0`; since CatCrypt's `heapStateSpec` is indexed by `HeapOp : Type 1`,
we define a universe-polymorphic `link` directly on top of `simulateQ`.

## Main definitions

* `PkgImpl I E` — alias for `QueryImpl E (OracleComp I)`: an SSP-style package
* `PkgImpl.id'` — identity package
* `PkgImpl.link` — sequential linking via `simulateQ` (universe-polymorphic)
* `PkgImpl.toSPComp` — lower a package with heap-state imports to `SPComp`

## Main results

* `PkgImpl.link_id_left`, `PkgImpl.link_id_right` — unit laws
* `PkgImpl.link_assoc` — associativity (from monad-morphism composition)
* `PkgImpl.toSPComp_link` — linking commutes with `SPComp` lowering

These are the SSP package-algebra laws, derived from the free-monad UMP rather
than postulated.

## Note on CatCrypt's `RawPackage.link`

The shallow-embedding `CatCrypt.Package.RawPackage.link` is a stub (it returns
`P₁` unchanged, as documented at `CatCrypt/Package/RawPackage.lean:141`). The
genuine linking infrastructure lives in the deep embedding
(`CatCrypt.Deep.Package`). This file stands alongside both, providing the VCVio
presentation of the package algebra. A future identification `DeepPackage.link`
↔ `PkgImpl.link` would close the circle but is out of scope here.
-/

namespace CatCrypt.Crypto.VCVioBridge

open CatCrypt.Core CatCrypt.Prob OracleComp

universe u

/-! ## Packages as query implementations into an imports free monad -/

/-- An SSP-style package with imports `I` and exports `E`: for each export
    query, a computation in the free monad over imports. Categorically this is
    a natural transformation `P_E ⇒ FreeP_I`; definitionally equal to
    `QueryImpl E (OracleComp I)`. -/
@[reducible] def PkgImpl {ιI ιE : Type u}
    (I : OracleSpec.{u, 0} ιI) (E : OracleSpec.{u, 0} ιE) :
    Type u := QueryImpl E (OracleComp I)

namespace PkgImpl

variable {ιI ιM ιE ιF : Type u}
  {I : OracleSpec.{u, 0} ιI} {M : OracleSpec.{u, 0} ιM}
  {E : OracleSpec.{u, 0} ιE} {F : OracleSpec.{u, 0} ιF}

/-- Identity package on an interface: each export forwards to the same query.
    Delegates to upstream `QueryImpl.id'`. -/
@[reducible] noncomputable def id' (spec : OracleSpec.{u, 0} ιE) : PkgImpl spec spec :=
  QueryImpl.id' spec

/-- Sequential linking of packages. `link p q` has the exports of `q` compiled
    against the implementations `p` provides; each `q` export is run with `p`
    substituted for its queries via `simulateQ`. This is `p ∘ q` in SSP
    notation. Defined directly on `simulateQ` (not `QueryImpl.compose`) to avoid
    upstream's universe-0 restriction on the middle spec. -/
noncomputable def link (p : PkgImpl I M) (q : PkgImpl M E) : PkgImpl I E :=
  fun t => simulateQ p (q t)

@[simp] theorem link_apply (p : PkgImpl I M) (q : PkgImpl M E) (t : ιE) :
    link p q t = simulateQ p (q t) := rfl

/-! ### SSP algebraic laws, derived from the monad-morphism UMP -/

/-- Left-unit: linking with the identity on the middle interface is a no-op.
    This follows from upstream's `simulateQ_id'`. -/
@[simp] theorem link_id_left (q : PkgImpl M E) : link (id' M) q = q := by
  funext t
  show simulateQ (QueryImpl.id' M) (q t) = q t
  simp

/-- Right-unit: post-composing with the identity on the exports is a no-op.
    The identity package forwards every query, so `simulateQ p` on it is `p`. -/
@[simp] theorem link_id_right (p : PkgImpl I M) : link p (id' M) = p := by
  funext t
  show simulateQ p (QueryImpl.id' M t) = p t
  simp

/-- Core lemma: `simulateQ` commutes with composition of handlers. Concretely,
    interpreting via `q` and then via `p` is the same as interpreting via the
    composed handler `link p q`. This is the functoriality of the free monad.

    The return type `α` lives at `Type 0` because range types of our specs do,
    which is the universe that `simulateQ`'s handler composes against. -/
theorem simulateQ_simulateQ (p : PkgImpl I M) (q : PkgImpl M E)
    {α : Type} (x : OracleComp E α) :
    simulateQ p (simulateQ q x) = simulateQ (link p q) x := by
  induction x using OracleComp.inductionOn with
  | pure a => simp
  | query_bind s mx ih =>
    simp only [simulateQ_query_bind]
    rw [simulateQ_bind]
    -- Both sides reduce to binds whose continuations are pointwise equal
    -- after using the induction hypothesis.
    congr 1
    funext u
    exact ih u

/-- Associativity of package linking. This is the content of the free-monad UMP:
    `simulateQ` is a monad morphism, so composition commutes appropriately. -/
theorem link_assoc (p : PkgImpl I M) (q : PkgImpl M E) (r : PkgImpl E F) :
    link p (link q r) = link (link p q) r := by
  funext t
  exact simulateQ_simulateQ p q (r t)

end PkgImpl

/-! ### Lowering to `SPComp` via the heap state oracle -/

namespace PkgImpl

/-- If a package imports from `heapStateSpec`, lower each export to `SPComp`.
    Specialized to universe 1 (the universe of `HeapOp`). -/
noncomputable def toSPComp
    {ιE : Type 1} {E : OracleSpec.{1, 0} ιE}
    (p : PkgImpl heapStateSpec E) (t : ιE) : SPComp (E t) :=
  runState (p t)

/-- Linking commutes with `SPComp` lowering: running the linked package at any
    export is the same as `simulateQ`-composing the implementations and then
    running the combined computation. -/
theorem toSPComp_link
    {ιE : Type 1} {E : OracleSpec.{1, 0} ιE}
    (p : PkgImpl heapStateSpec heapStateSpec)
    (q : PkgImpl heapStateSpec E) (t : ιE) :
    toSPComp (link p q) t = runState (simulateQ p (q t)) := rfl

end PkgImpl

end CatCrypt.Crypto.VCVioBridge
