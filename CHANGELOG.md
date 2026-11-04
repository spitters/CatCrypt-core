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
- `XDijkstra/GradedDo.lean`: the classes `GradedMonad` and `LawfulGradedMonad`
  for families of type constructors indexed by a grade of an additive monoid,
  and the block notation `gdo`, which expands to `GradedMonad.gbind`. `CostM σ`
  is an instance (`CostM.instGradedMonad`, `CostM.instLawfulGradedMonad`), and
  the tutorial states its cost example in the notation.
- `XDijkstra/XErrMonad.lean`: `ErrM ε`, the sub-distributions that fail with
  weight at most `ε`, a graded monad over `(ℝ≥0∞, +, 0)` by the union bound
  `sdistr_bind_none_le`, with an `XWP` instance at the shape
  `.graded ℝ≥0∞ .pure` (`instXWPErrM`) and the soundness theorems `ErrM.sound`
  and `ErrM.prob_post_ge` against the sub-distribution.
- `XDijkstra/XPredCore.lean`: the observation of a monad without a shape
  (`XCoreWP`, `XCoreWP.Triple`, `LawfulXCoreWP` with `XCoreWP.bind_triple`) and
  morphisms of observations with a joint map on the pair of postconditions
  (`XCoreWPHom`, `XCoreWPHom.triple`). `XWP` and `XWPMorphism` convert to them
  (`XWP.toCoreWP`, `xtriple_iff_core`, `XWPMorphism.toCoreWPHom`).
- `XDijkstra/Rel/`: graded relational coupling over `RelQ0` monads
  (`XRelTripleQ0`), the coupling specification monad `RelPT` with the tactics
  `relmvcgen` and `relmvcgen_ctl`, and `XDijkstra/XAdvantageHybrid.lean` with the
  tactic `advmvcgen` for advantage bounds over a chain of games.
- `native_decide` is accepted in core, as in the development repository; the
  CI step that rejected it is removed. A proof that uses it depends on the
  axiom `Lean.ofReduceBool`, which `#print axioms` lists. The first users are the
  Pocklington primality certificates of `Crypto/Ristretto255/FinGroup.lean`.
- `Crypto/UCPullback.lean`: environment pullbacks (`EnvPullback`), a map on
  systems with a map on environments in the opposite direction and an advantage
  equation, and the pullback law `EnvPullback.realizes_map`: a realization with
  bound `b` maps to one with bound `b ∘ pull`. Pullbacks compose; the
  composition theorem for two holes is `EnvPullback.realizes_twoHole`. Open
  systems, hybrids, multi-call hybrids, either side of the cascade and
  adversary absorption are instances.
- `Crypto/UCPullbackSemantics.lean`: advantage theories and pullbacks between
  them (`AdvTheory`, `AdvPullback`, `AdvPullback.realizes_rel`), with step
  equivalence and the compilation of party diagrams (`compilePullback_rel`) and
  the oracle-game semantics (`OProt.toAdvPullback`) as instances; adversary
  absorption as an action on environments up to advantage, with the forwarding
  adversary `AdvSys.dummy` acting as the identity (`AdvSys.adv_absorb_absorb`,
  `AdvSys.adv_absorb_dummy`).
- `Crypto/UCPullbackTimed.lean`, `Crypto/UCPullbackCost.lean`: time
  certificates of the environment reductions of hybrids, multi-call hybrids and
  adversary absorption (`Hybrid.Timed.reduce_timeBound`,
  `Strat.absorb_timeBound`), the time of an environment over its whole run
  (`EnvTimeBound.sysEnvTree_time`), and costed pullbacks (`CostedPullback`),
  whose reduced environments have the time of the environment plus constants of
  the pullback (`CostedPullback.pull_envTimeBound`); the costed pullback law, the
  two-hole law and the cascade composition theorem with these times
  (`CostedPullback.realizes_map`, `CostedPullback.realizes_twoHole`,
  `realizes_seq_timed`).
- `Crypto/UCCascadeEnrichedPar.lean`: parallel composition and bounded
  feedback of classes of lossless systems; both preserve realization at
  statistical bounds and are non-expansive for the realization distance on
  classes idle at given events (`Cell1.dist_par_le`, `Cell1.dist_loopback_le`).
- `Crypto/Party/RelatorRelational.lean`: the relational judgment of party
  programs is the relation lifting of programs at exact couplings
  (`Prog.relTriple_iff_relProg`).
- `Category/ProtBicatPullback.lean`: rounds-graded pullbacks
  (`AdvPullbackRounds`, `AdvPullbackRounds.realizes_rel`) and the protocol
  bicategory in systems as one, from the advantage theory of one-shot protocols,
  whose supremum is `sdist` (`oneShotTheory_iSup_adv`), with horizontal
  composition and identities carried by the relation
  (`UCMonad.statelessPullback_rel_hcomp`, `UCMonad.statelessPullback_rel_hid`).
- `Quantum/QPullback.lean`: quantum realization with environment-dependent
  bounds (`QRealizesB`, `QRealizesSimB`, `QRealizesSimQB`), the constant bound as
  an instance (`QRealizes_iff_const`), quantum environment pullbacks with the
  pullback law and the two-hole law (`QEnvPullback.realizes_map`,
  `QEnvPullback.realizes_twoHole`), and simulator absorption as a pullback
  (`QSim.qview_attach`, `QRealizesSimB_iff_attach`).
- `Quantum/QPullbackCascade.lean`: register transfer of simulators with a
  private register (`QSimQ.qviewQ_attachQ`), pullbacks over environments with
  quantum memory (`QEnvPullbackQ`), the quantum cascade with private registers
  as composition in `QSysCat` (`QSys.cascade_toQRSys`) and its composition
  theorem (`QRealizesQB.cascade`).
- `Quantum/QPullbackPar.lean`, `Quantum/QPullbackFeedback.lean`: quantum
  parallel composition and bounded loopback with private registers as pullbacks
  over environments with memory, for components idle at a given event, with the
  composition theorems `QRealizesQB.par` and `QRealizesQB.loopback`.
- `Quantum/QPullbackAdversary.lean`: quantum adversary systems (`QAdvSys`),
  attachment as a pullback (`QRealizesQB.attachAdv`), concurrent quantum UC
  emulation with environment-dependent bounds (`QUCEmulatesSysB`) and the
  quantum dummy-adversary theorem (`qucEmulatesSysB_of_realizes`,
  `QUCEmulatesSysB.realizes_dummy`, `qucEmulatesSysB_iff_realizes_of_le`).
- `Quantum/ClassicalLiftPullback.lean`: the classical lift as a pullback of
  advantage theories (`ClassicalLiftSys.liftPullback`), with the advantage
  equation `ClassicalLiftSys.cpDist_qview_liftQSys` and reflection of
  realizations along a pullback whose pull of tests has a section
  (`AdvPullback.realizes_of_rel`).

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
