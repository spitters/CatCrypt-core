/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.XDijkstra.XPostShape
public import CatCryptCore.XDijkstra.XMvcgen
public import CatCryptCore.XDijkstra.XRelatorPMF
public import CatCryptCore.XDijkstra.XHeapSoundness

/-!
# XDijkstra — the extended-PostShape Dijkstra-monad framework (import aggregator)

A single weakest-precondition framework that fuses four axes the stock `Std.Do` WP keeps
apart: a **grade** (a monoid budget / cost), **separation logic** (assertions in a bunched
carrier, with a frame rule), **relational** reasoning (relating two programs), and
**monad-morphism transfer**. It is a local fork of `Std.Do`'s WP — `Std.Do.PostShape` lives
in the Lean toolchain and cannot be extended in place, so `XPostShape` mirrors it and adds the
grade layer. Forcing this module builds the whole framework so a change to one axis cannot
silently rot the others.

* `XPostShape` — the fused core. `XPostShape` (`pure | arg | except | graded G`),
  `XPredTrans` over an assertion carrier `Ω` (with a value grade), `xpure`/`xbind`/`xseq`,
  `XWP`, `XTriple`, and the four axis-laws: `xwp_graded_bind` (grades add), `xframe` (frame
  rule over `class XBI Ω`), `xprod`/`xrel_seq` (deterministic relational), `xwp_morphism`
  (transfer). Value-grade and `LawfulMonad` are jointly unsatisfiable, so the monad laws hold
  at the semantic `apply` level and grades thread through `xseq`.
* `XMvcgen` — the `xmvcgen` VC generator: a simp-set-driven normalizer (`@[xspec]` + an
  explicit reduction bundle) that threads all four axes on a fused goal and leaves the residual
  VCs (the assertion entailment and `grade ≤ budget`). Fused demos (graded+frame,
  relational+graded).
* `XRelatorPMF` — the `T̂` relator: probabilistic coupling at `PMF`. `IsCoupling` /
  `Couples` (the relational lifting), `Couples_pure`, `Couples_bind` (the coupling `bind` —
  the pRHL composition rule), `Couples_same` (the `x = y` diagonal), and the probabilistic
  relational triple. The deterministic `xprod` is the trivial (independent) coupling.
* `XHeapSoundness` — soundness against a state machine and separation logic. An `XBI (HProp V)`
  with disjoint-heap `∗`, so `xframe` is the frame rule over disjoint heaps, and a
  soundness `XWP (StateM σ)` instance for which `XTriple` is the ordinary state Hoare
  triple (`stateWP_triple_iff`, definitional).

Stock `mvcgen` cannot fuse these axes over one extended `PostShape`: its `PredTrans ps`
codomain has no grade slot (see `GradedMvcgenProbe`). Lineage: *The Next 700 Relational
Program Logics* (relational), graded Dijkstra monads (graded), *Dijkstra Monads for All*
(morphism), and the `MVCGenToSL` chain (SL).
-/

@[expose] public section
