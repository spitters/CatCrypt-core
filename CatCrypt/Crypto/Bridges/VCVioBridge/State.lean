/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Bridges.VCVioBridge.Monad

/-!
# VCVio Bridge — State layer (Phase 2)

Encoding of CatCrypt's typed heap as an oracle polynomial.

We realize `SPComp`'s state layer as a handler for the polynomial functor
associated to a "heap oracle" spec. This lets us view a stateful CatCrypt
computation as a VCVio `OracleComp heapStateSpec`, and package linking as
`simulateQ`.

## Main definitions

* `HeapOp` — sum of typed heap operations (`getL l`, `putL l v`)
* `heapStateSpec` — the oracle spec: each op maps to its response type
* `heapHandler` — canonical interpretation in `StateT Heap SDistr`
* `runState` — monad morphism `OracleComp heapStateSpec ⇒ SPComp`

## Main results

* `runState_pure`, `runState_bind` — monad-morphism laws
-/

namespace CatCrypt.Crypto.VCVioBridge

open CatCrypt.Core CatCrypt.Prob
open scoped ENNReal

/-! ## Heap operations as a polynomial functor -/

/-- Sum of typed heap operations. Each constructor records the operation's
    "position"; the corresponding response type is given by `heapStateSpec`.
    Universe level is inferred — `HeapOp` lives at whichever universe `Location`
    forces, not necessarily `Type 0`. -/
inductive HeapOp where
  | getL (l : Location)
  | putL (l : Location) (v : l.ty)

/-- Heap-as-oracle spec: each operation maps to its response type. Reading a
    location of type `l.ty` returns `l.ty`; writing returns `Unit`. -/
def heapStateSpec : OracleSpec HeapOp
  | .getL l => l.ty
  | .putL _ _ => Unit

/-! ## Canonical heap handler -/

/-- Canonical interpretation of heap ops in `StateT Heap SDistr`. Reading a
    location returns `h.get l` without changing the heap; writing sets it. -/
noncomputable def heapHandler : QueryImpl heapStateSpec (StateT Heap SDistr)
  | .getL l => StateT.mk fun h => SDistr.pure (h.get l, h)
  | .putL l v => StateT.mk fun h => SDistr.pure ((), h.set l v)

/-! ## runState: OracleComp heapStateSpec ⇒ SPComp -/

/-- Run a heap-oracle computation against a concrete heap, producing an `SPComp`.
    This is `simulateQ` followed by `StateT.run`, producing a `Heap → SDistr (α × Heap)`
    which is exactly `SPComp α`. -/
noncomputable def runState {α : Type} (oc : OracleComp heapStateSpec α) : SPComp α :=
  fun h => (simulateQ heapHandler oc).run h

/-- `runState` preserves `pure`. -/
theorem runState_pure {α : Type} (a : α) :
    runState (pure a : OracleComp heapStateSpec α) = SPComp.pure a := by
  funext h
  simp [runState, SPComp.pure]
  rfl

/-- `runState` preserves `bind`. -/
theorem runState_bind {α β : Type}
    (mx : OracleComp heapStateSpec α) (f : α → OracleComp heapStateSpec β) :
    runState (mx >>= f) = SPComp.bind (runState mx) (fun a => runState (f a)) := by
  funext h
  simp only [runState, simulateQ_bind]
  -- Goal after simp: (simulateQ heapHandler mx >>= fun a => simulateQ heapHandler (f a)).run h
  --               = SPComp.bind (fun h => (simulateQ heapHandler mx).run h) ... h
  unfold SPComp.bind
  simp only [StateT.run_bind]
  rfl

end CatCrypt.Crypto.VCVioBridge
