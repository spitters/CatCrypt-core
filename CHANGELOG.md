# Changelog

## Unreleased

- New directory `XDijkstra/`: a graded Dijkstra-monad kernel (`XCorePT`,
  `XPostShape`, `XPredTrans`, `XTriple`, the `xmvcgen` tactics and the `xspec`
  simp set), with a guide for users of `mvcgen` (`XDijkstra/README.md`) and a
  tutorial module (`XDijkstra/Demo.lean`).
- `XDijkstra/XCostMonad.lean`: the cost-counting state monad `CostM σ n`, a
  graded monad indexed by a bound on the tick count, with an `XWP` instance at
  the shape `.graded ℕ (.arg σ .pure)` (`instXWPCostM`), the soundness theorem
  `CostM.sound` against the run, and reduction lemmas in the `xspec` set. The
  tutorial has a section on a graded triple about a `CostM` program.
- `XDijkstra/XPredCore.lean`: the observation of a monad without a shape
  (`XCoreWP`, `XCoreWP.Triple`, `LawfulXCoreWP` with `XCoreWP.bind_triple`) and
  morphisms of observations with a joint map on the pair of postconditions
  (`XCoreWPHom`, `XCoreWPHom.triple`). `XWP` and `XWPMorphism` convert to them
  (`XWP.toCoreWP`, `xtriple_iff_core`, `XWPMorphism.toCoreWPHom`).
- `XDijkstra/Rel/`: graded relational coupling over `RelQ0` monads
  (`XRelTripleQ0`), the coupling specification monad `RelPT` with the tactics
  `relmvcgen` and `relmvcgen_ctl`, and `XDijkstra/XAdvantageHybrid.lean` with the
  tactic `advmvcgen` for advantage bounds over a chain of games.

## v0.2.0 — 2026-06-10

- Toolchain: Lean 4.29.1, Mathlib `v4.29.1`, VCVio `v4.29.0`, Duper `v4.29.0`,
  lean-auto `v4.29.0-hammer` (was Lean 4.28.0 across the board).
- The Rust → Jasmin compiler pipeline (`Crypto/Jasmin/`,
  `Crypto/SecureCompilation/`) moved out of the minimal basis into a separate
  project. With it go the per-ISA compiler-correctness axioms and all
  `native_decide` uses.
- Removed the unused `PRP_PRF_Switching` axiom: its statement did not express
  the switching lemma. The birthday-term bound definition remains.
- Fixed the `Crypto.NomAdvantage` build failure on Lean 4.29 (explicit
  universe annotations on the universe-monomorphic `NomPackage`).
- New modules: `Tactics/{SumCases, SPNormalize, Remember, Triangle,
  CryptoAuto}` and `Deep/Reflect` (an `SPComp` → `RawCode` reifier).
- Added `CITATION.cff`, `CHANGELOG.md`, `CONTRIBUTING.md`, and a CI workflow
  with sorry/axiom guards.
- Dropped the unused Duper, lean-auto, and lean-smt dependencies (no module
  imported them); the dependency set is now Mathlib + VCVio + hammer-free.

## v0.1.0 — 2026-04-23

- Initial minimal-basis release (Lean 4.28.0).
