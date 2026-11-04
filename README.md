# CatCrypt Core

> 🚧 **Under active development.** CatCrypt is still evolving rapidly — APIs,
> module organization, and dependencies may change between releases.

The core of CatCrypt: machine-checked foundations for game-based
cryptographic security proofs in Lean 4 — sub-distributions, a
stateful-probabilistic program monad, probabilistic relational Hoare
logic, state-separated packages, proof automation, forking lemmas, and
Montgomery-curve mathematics.

📖 **Documentation:** [hosted API reference](https://spitters.github.io/CatCrypt-core/) ·
[blueprint](https://spitters.github.io/CatCrypt-core/blueprint/) ([dependency graph](https://spitters.github.io/CatCrypt-core/blueprint/dep_graph_document.html)) ·
[design & influences](DESIGN.md) · [The Joy of Cryptography in CatCrypt](JoyOfCrypto.md)

This is the **minimal-basis release**. The universal-composability theory,
concurrent UC, quantum verification, the verified compilation pipeline, and
the full catalogue of concrete protocols live in separate, larger
distributions.

Module names live under the `CatCryptCore.*` root (single entry point:
`import CatCryptCore`), so the library coexists with any package that has its
own `CatCrypt.*` module tree. Declared *namespaces* are `CatCrypt.*`:
`open CatCrypt.Core`, `CatCrypt.Core.SPComp`, etc. Paths in the table below
are relative to `CatCryptCore/`.

## Contents

| Layer | Modules |
|---|---|
| Probability | `Prob/*` — sub-distributions, couplings, support, birthday bound, Schwartz–Zippel |
| Core | `Core/*` — typed heap (finite- and countable-typed locations), `SPComp` stateful-probabilistic monad, `SPTree` syntactic trees |
| Relational | `Relational/*` — pRHL judgment, sync/frame/reorder rules |
| Non-uniform | `NonUniform/*` — sampling from an arbitrary sub-distribution, conditioning, products, the unbounded `while` loop and its pHL / pRHL rules |
| Package | `Package/*` — interface-based package algebra |
| Category | `Category/*` — Kleisli of SPComp, family bicategory, cocartesian / affine structure |
| Graded WP kernel | `XDijkstra/*` — graded predicate transformers extending `Std.Do` with a grade, a frame rule, relational triples and transfer along monad morphisms; the `xmvcgen` tactics ([guide](CatCryptCore/XDijkstra/README.md)) |
| Deep embedding | `Deep/*` — syntactic package calculus with semantic evaluation, `SPComp` → `RawCode` reflection |
| Bridge | `Bridge/*` — deep-to-shallow semantic bridge |
| Tactics | `Tactics/*` — pRHL automation (sync, invariant, WP/SP, ProofFrog, lazy sampling, remember/forget, triangle chaining, …) |
| Crypto foundation | `Crypto/{Game,Advantage,SDist,SecurityDefs,Encryption,HybridArgument,NomAdvantage}.lean` |
| Forking | `Crypto/ForkingLemma.lean`, `Crypto/GeneralForkingLemma.lean` — Pointcheval–Stern and Bellare–Neven |
| Up-to-bad | `Crypto/BadEvent.lean` — identical-until-bad / fundamental lemma of game-playing, bad-event union bounds, hybrid + up-to-bad, and lazy/eager sampling (`Tactics/UpToBad.lean` drives it) |
| Complexity | `Crypto/{UCAdmClass,MonadCostModel,QueryBoundedUC,SizeBoundedUC,CTAdmClass,UCLevels,DummyAdversary,CompUCEquivalence,ConcreteReductions,RCL3,TraceRelating}.lean`, `Unary/ExpectedCost.lean` — admissibility classes from query cost, total size and constant-time shape; the computational distance over admissible distinguishers and three levels of UC emulation; the dummy-adversary and constructive-cryptography equivalences at a bounded class; negligible functions; expected cost with the geometric-retry bound ([guide](CatCryptCore/Crypto/Complexity.md)) |
| Query counts and provenance | `Crypto/{OracleQueryVec,OracleProfile}.lean`, `Tactics/{QueryBound,QueryFold}.lean` — a query bound as a bound on the cost fold of the adversary's tree at a charge, with per-oracle counts, total counts and provenance as charges (`isQueryBoundBy_iff_cost_le`, `MayOnlyCall`, `IsQueryProfile`); the query profile, the set of pairs (multiset of queries, result) over the paths of an adversary, of which these notions are evaluations at nonempty answer types (`isQueryBoundBy_iff_profile`, `mayOnlyCall_iff_profile`, `cost_eq_iSup_profile`); the laws of the profile under simulation and substitution, stated on traces (`mem_profile_simulate_iff`, `mem_profile_subst_iff`), with the Diller–Nahm composite when each program asks a fixed multiset of queries for each answer (`profile_subst_of_demand`, `demandLens_comp`); the budget-passing fold `Within`, with an equation at every constructor and at `bind` (`within_bind`, `isQueryBoundBy_iff_within`); the tactics `query_bound` and `query_fold` ([registry](CatCryptCore/Tactics/AGENTS.md)) |
| Time of UC reductions | `Crypto/{UCConcreteTimed,UCSimulatorCostMono}.lean` — costed forms of the joint run and of the view of a strategy against a reactive system, and of the environment reductions `envReduction` and `sysEnvTree`, whose time is the time of the environment, the graded step bounds of the strategy and the system over its activations (`StratRunBound`, `SysRunBound`), the reset to the environment's heap and a constant per activation (`envReduction.tree.timeBound_timed`, `sysEnvTree.timeBound_timed`); a costed simulator at other views, with its erasure and time bounds (`Simulator.Timed.mono`, `Simulator.mono.erase_timed`, `Simulator.mono.timeBound_timed`) ([guide](CatCryptCore/Crypto/ConcreteSecurity.md)) |
| Containers and type theory | `Container/{DillerNahm,CwF,CwFPi}.lean` — the Diller–Nahm category of containers (Moss and von Glehn), in which a first-order costed function is a linear morphism (`Costed.equivIsLinear`), costs with use counts compose as `c₂ + n₂ * c₁` (`Clocked.toDN_comp`) and query counts add (`VecCosted.toDN_comp`); the polynomial model of type theory over `Type` as a category with families (Cavallo and Höfer, §3), with dependent sums, dependent products (`Tm.lamEquiv`), identity types with empty positions (`nonempty_tm_eq_iff`), coproducts and the reflective modality (`Tm.modalEquiv`); the Diller–Nahm predicate (`DNSound`), which over pairs of runs is agreement soundness (`dnSound_runPair_iff`), and the category of objects with an agreement and sound morphisms (`RunObj`, `RunHom`) |
| Assumptions | `Crypto/Assumptions/*` — DDH, CDH, GapDH, DL, t-SDH, q-SDH, CoCDH, ODH, CR, OWF, PRP, RSA, AEAD, MAC |
| Curve math | `Crypto/KeyAgreement/{MontgomeryLadder,MontgomeryAsWeierstrass,MontgomeryXOnly,Curve25519}.lean` |
| Fujisaki–Okamoto | `Crypto/PKE/{Games,FOTransformT}.lean`, `Crypto/KEM/{Games,FOTransformU,FOTransform,FIPS203KEM,FIPS203Security}.lean` — PKE and KEM games, the T and U transforms with their classical reductions, the FIPS 203 KEM |
| Quantum foundations | `Quantum/{Instrument,TraceNorm,UnitaryChannel,CPMap,Measurement,TensorProduct,KroneckerPSD,ChoiKraus,PartialTrace,Stinespring}.lean` — instruments and channels on finite matrices, trace norm, completely positive maps, measurements, tensor products, positivity of Kronecker products, the Choi characterisation and Kraus form of completely positive maps, partial trace, Stinespring dilation and purification |
| Quantum distances | `Crypto/UCMonad/{QuantumUC,DiamondNorm,DiamondNormStates,DiamondDominates,DiamondTensorStable,DiamondEmulation,LocalOpFunctorial,QIndistDiamond}.lean`, `Quantum/{ClassicalEmbed,ClassicalLift,ClassicalDiamondLift,QRHL}.lean` — the `UCMonad` instance of quantum instruments with the distinguishing distance `qdist`, the diamond norm `qdistDiamond` (a metric, above `qdist` and the CP-distinguisher distance, stable under local operations); diamond-distance emulation `QUCEmulatesDiamond` is a preorder with additive error, preserved by sequential composition on either side and by tensoring with a fixed instrument, and gives `UCEmulates` with the adversary as simulator; the embedding of classical subdistributions with equality of the classical and quantum distances, and quantum relational Hoare logic |
| Quantum systems and quantum UC | `Quantum/{SubInstrumentOrder,QSysCat,QSysCatTensor,QSysCatPrivate,QSysCatOpenTheory,ClassicalLiftSys,ClassicalLiftFunctor,QRealizes,QRealizesMem,QOTPReactive,QOTPInsecure}.lean`, `Crypto/{OpenTheoryObs,UCTransport}.lean` — Selinger's order on subinstruments, an ω-complete partial order in which sequencing is ω-continuous; the traced symmetric monoidal category of quantum reactive systems (`⊕` traced by the ω-supremum of the feedback runs, `⊗` of registers by framing), its variant with registers private to morphisms, and its Int construction as an open theory with quantum emulation closed under composition; the classical lift of reactive systems as a traced braided monoidal functor, with statistical transport of realization bounds; transport of realization along observation-preserving maps; realization of quantum reactive systems with simulators holding quantum registers, and the quantum one-time pad realizing the secure quantum channel and, over an insecure channel, the confidential channel with Pauli tampering ([guide](CatCryptCore/Quantum/README.md)) |
| Composition law | `Crypto/{UCPullback,UCPullbackSemantics,UCPullbackTimed,UCPullbackCost,UCCascadeEnrichedPar}.lean`, `Category/ProtBicatPullback.lean`, `Quantum/{QPullback,QPullbackCascade,QPullbackPar,QPullbackFeedback,QPullbackAdversary,ClassicalLiftPullback}.lean` — realization is preserved along environment pullbacks: a pullback is a map on systems with a map on environments in the opposite direction such that the advantage of an environment against the images equals the advantage of its reduced environment against the sources, and it maps a realization with bound `b` to a realization of the images with bound `b ∘ pull`; a context with two holes is two pullbacks and transitivity ([`EnvPullback.realizes_map`, `EnvPullback.realizes_twoHole`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/UCPullback.lean)). Contexts are instances: open systems (among them feedback), hybrids, multi-call hybrids (among them parallel composition) and either side of the cascade ([`Open.toEnvPullback`, `Hybrid.toEnvPullback`, `MultiHybrid.toEnvPullback`, `EnvPullback.seqLeft`, `EnvPullback.seqRight`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/UCPullback.lean)). Adversary absorption is a pullback ([`AdvSys.toEnvPullback`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/UCPullback.lean)) and an action on environments up to advantage, under which the forwarding adversary acts as the identity ([`AdvSys.adv_absorb_absorb`, `AdvSys.adv_absorb_dummy`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/UCPullbackSemantics.lean)). A change of semantics is a pullback between advantage theories ([`AdvPullback.realizes_rel`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/UCPullbackSemantics.lean)): step equivalence, with the compilation of party diagrams as an instance, and the oracle-game semantics of a protocol ([`stepEqPullback`, `compilePullback_rel`, `OProt.toAdvPullback`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/UCPullbackSemantics.lean)); the protocol bicategory in systems, as a rounds-graded pullback whose bound is the number of rounds times the one-shot statistical distance and whose relation carries horizontal composition and identities ([`AdvPullbackRounds.realizes_rel`, `UCMonad.statelessPullback_rel_hcomp`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Category/ProtBicatPullback.lean)); and the classical lift into quantum systems, which also reflects realization ([`ClassicalLiftSys.liftPullback`, `AdvPullback.realizes_of_rel`, `ClassicalLiftSys.cpDist_qview_liftQSys`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/ClassicalLiftPullback.lean)). Costed pullbacks carry time certificates of the reduced environments over whole runs: an environment with given per-activation costs, activation count and distinguisher cost reduces to one whose costs grow by constants of the pullback, with the hybrid, absorption and cascade contexts as instances ([`CostedPullback.pull_envTimeBound`, `CostedPullback.realizes_twoHole`, `realizes_seq_timed`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/UCPullbackCost.lean); [`Hybrid.Timed.reduce_timeBound`, `Strat.absorb_timeBound`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/UCPullbackTimed.lean)). The realization distance is non-expansive for parallel composition and feedback of classes idle at given events ([`Cell1.dist_par_le`, `Cell1.dist_loopback_le`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/UCCascadeEnrichedPar.lean)). The quantum analogue, with diamond distances bounded by functions of the environment ([`QRealizesB`, `QEnvPullback.realizes_map`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/QPullback.lean)), covers the cascade with private registers ([`QRealizesQB.cascade`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/QPullbackCascade.lean)), parallel composition ([`QRealizesQB.par`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/QPullbackPar.lean)), feedback ([`QRealizesQB.loopback`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/QPullbackFeedback.lean)), simulator absorption ([`QRealizesSimB_iff_attach`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/QPullback.lean)) and quantum adversary systems with the dummy-adversary theorem ([`qucEmulatesSysB_of_realizes`, `QUCEmulatesSysB.realizes_dummy`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/QPullbackAdversary.lean)) ([guide](CatCryptCore/Quantum/README.md#composition-law-for-quantum-realization)) |
| Party language | `Crypto/Party/*` — classical and quantum party programs in `do` notation, denoted as reactive systems; parallel composition and loops agree with the Int construction on systems; the category of wiring diagrams with a faithful traced monoidal denotation functor; subroutine calls as multi-call hybrids; qubit ports with linear ownership; port typing, opacity, a relational program logic whose judgment is the relator of programs at exact couplings ([`Prog.relTriple_iff_relProg`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Party/RelatorRelational.lean)), refinement, time certificates and quantum weakest preconditions derived from programs (`party_derive`); F_AKE, X3DH and PQXDH as programs ([guide](CatCryptCore/Crypto/Party/README.md)) |
| Quantum random oracles | `Quantum/QROM/*` — semi-classical one-way to hiding for every mixed initial state (`O2HTheorem.o2h_semiclassical_mixed`) and for multi-round adversaries whose local operations are arbitrary completely positive trace-preserving maps (`O2HGeneral.o2h_semiclassical_gen`, through a unitary dilation that keeps the acceptance probability), completely positive instruments (`Quantum/CPInstrument`), measure-and-reprogram for a single reprogrammed point (`MeasureReprogram.measure_reprogram`), Zhandry's compressed oracle with equality of output probabilities against the standard oracle and at most `q` database entries after `q` queries (`CompressedOracle.prOut_compressed_eq`, `CompressedOracleLocal.runCmp_database_le`), the search bound, quantum KEM games with classical decapsulation queries, normal form of adversaries, and the game hops of the Fujisaki–Okamoto proof with implicit rejection |
| ML-KEM | `Crypto/MLKEM/*` — the FIPS 203 specification over `Z/3329Z` with its NTT (`Spec/`, `Crypto/Lattice/*`), the module-LWE PKE, and IND-CCA security of ML-KEM-512 against quantum adversaries in the QROM, every term a proved number or a quantum module-LWE advantage of an explicit reduction ([proof structure](CatCryptCore/Crypto/MLKEM/QROM.md)) |

## Time certificates

A concrete security theorem bounds the advantage of every adversary `A` by advantages of
explicit reductions `B A`; it says something about efficient adversaries only if `B A` runs in
time close to that of `A`. Every reduction and every simulator therefore carries a time
certificate, in the form of the cost judgment of EasyCrypt (Barbosa et al., CCS 2021):

- a costed form `B.timed`, a program in which each node also carries the cost of computing the
  next one;
- an erasure theorem `B.erase_timed`, checked by the kernel, stating that removing the costs
  gives `B`;
- a time theorem bounding the time of the costed form by the time of the costed adversary plus
  a constant, or, for a simulator whose state grows, plus `a + b·i` at activation `i` or
  `b·|e|` in the size of the event `e`.

The certificates rest on four ideas.

1. Costs on the syntax of programs. Programs are trees of registered kinds: sampling programs
   (`SPTree`), oracle adversaries and oracle programs, and quantum instruments
   ([`register_tree_kind`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Tactics/DeriveTimed.lean),
   [`qInstrKind`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/QTreeKind.lean)).
   The costed form is obtained by translating the term node by node, and primitive operations
   are priced by `timed_cost` registrations. An operation without a price, or a field whose
   type is a computation of no registered kind, is refused, never priced at zero
   ([`ComputationType`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Tactics/ComputationType.lean)).
2. Unknown code behind a costed witness. A time theorem quantifies over costed adversaries
   whose erasure is the adversary and whose time is bounded, so the bound of a reduction is
   relative to the adversary's time; running an adversary against an oracle implementation
   costs its time plus its queries times the cost of one answer
   ([`OracleAdv.Timed.timeBound_simulate`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/OracleAdversaryTimed.lean)).
3. Derivation by tactics. `derive_timed` and `derive_reduction` derive the costed form, its
   erasure theorem and a time bound of a program, inlining the costed forms of its callees;
   [`derive_timed_structure`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Tactics/DeriveTimedStructure.lean)
   gives a structure of programs (a reactive system, a strategy, a simulator) its costed
   mirror; [`derive_hybrid_time`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Tactics/DeriveSimulator.lean)
   assembles the time theorem of a simulator from the bounds of its steps. Two ratchets keep
   the number of uncertified reductions and of hand-written costed forms from rising.
4. Composition. Costed environment pullbacks carry bounds over whole runs (activations, rounds
   and the distinguisher) through every context of the composition law, classical and quantum
   ([`CostedPullback.pull_envTimeBound`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/UCPullbackCost.lean),
   [`QRealizesQB.cascade_timed`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Quantum/QPullbackCost.lean)).

The derived costs are related to an operational cost model: `D` is a deep call-by-value
language with the cost model of the weak call-by-value λ-calculus L of Forster and Kunze (ITP
2019), which Forster, Kunze and Roth showed reasonable for time (POPL 2020). A reduction is
reflected into `D` by a certifying extraction in the style of Forster and Kunze, and
[`link_timed`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Tactics/LinkTimed.lean)
proves that the costed form simulates the reflected term and that the cost of the term in `D`
is at most the time of the costed form plus a constant
([D](CatCryptCore/Complexity/D/README.md)). The conventions, the laws of the costed trees and
the comparison with other cost analyses are in the
[guide](CatCryptCore/Crypto/ConcreteSecurity.md).

## Build

See [BUILDING.md](BUILDING.md) for building the library and the documentation.

## Dependencies

Pinned in `lakefile.lean` and `lake-manifest.json`; the toolchain is in `lean-toolchain`:

- [Mathlib](https://github.com/leanprover-community/mathlib4)
- [nominal-lean](https://github.com/spitters/nominal-lean) — the nominal-sets layer (`Nominal/`)

## Documentation

- **API reference:** [doc-gen4](https://spitters.github.io/CatCrypt-core/)
- **Blueprint:** [hosted blueprint](https://spitters.github.io/CatCrypt-core/blueprint/) and its
  [dependency graph](https://spitters.github.io/CatCrypt-core/blueprint/dep_graph_document.html) (leanblueprint; sources in
  [`blueprint/src/`](blueprint/src/)). It states the foundation layers and every worked
  scheme in `CatCryptCore/Examples/`, each statement linked to its Lean declaration in
  the API reference.
- **The Joy of Cryptography:** [JoyOfCrypto.md](JoyOfCrypto.md) maps the chapters of
  Rosulek's textbook to the worked schemes in `CatCryptCore/Examples/`.
- **Graded weakest preconditions:** [CatCryptCore/XDijkstra/README.md](CatCryptCore/XDijkstra/README.md)
  relates the kernel to `Std.Do` and `mvcgen`;
  [`Demo.lean`](CatCryptCore/XDijkstra/Demo.lean) is the tutorial.
- **Proof automation:** [CatCryptCore/Tactics/README.md](CatCryptCore/Tactics/README.md)
  documents `catcrypt_auto` and `catcrypt_auto?`, their goal shapes and arms, and how a
  library registers shapes and arms for its own goals, with the VCVio registrations as
  the worked example.
- **Design and influences:** [DESIGN.md](DESIGN.md) ·
  **Changelog:** [CHANGELOG.md](CHANGELOG.md) ·
  **Contributing:** [CONTRIBUTING.md](CONTRIBUTING.md)

To build the manual, the API reference or the blueprint locally, see [BUILDING.md](BUILDING.md).

## Relation to SSProve

The program logic, package algebra, and the `ssprove_*` tactic family port
the design of [SSProve](https://github.com/SSProve/ssprove), the Coq/Rocq
framework for modular cryptographic proofs:

> P. G. Haselwarter, E. Rivas, A. Van Muylder, T. Winterhalter, C. Abate,
> N. Sidorenco, C. Hriţcu, K. Maillard, B. Spitters.
> *SSProve: A Foundational Framework for Modular Cryptographic Proofs in Coq.*
> ACM Transactions on Programming Languages and Systems 45(3), 2023.
> [doi:10.1145/3594735](https://doi.org/10.1145/3594735)

## Related projects

- [hax-lean](https://github.com/spitters/hax-lean) — a partially verified version
  of [hax](https://github.com/hacspec/hax), a tool for high-assurance translation of
  a large subset of Rust into formal languages.

## Citing

See `CITATION.cff`. The accompanying paper:

> B. Spitters. *CatCrypt: From Rust to Cryptographic Security in Lean.*
> Cryptology ePrint Archive, Paper 2026/604.
> <https://eprint.iacr.org/2026/604.pdf>

## License

MIT. See `LICENSE`.
