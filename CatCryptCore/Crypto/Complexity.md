# Complexity measures and computational UC

UC emulation compares two protocols by the advantage of a distinguisher. The statistical
distance `ucSdist` takes the supremum over all distinguishers; the computational distance
`ucCdist` takes it over an *admissibility class* of programs. These modules make the class a
parameter, instantiate it with complexity measures, and prove the UC equivalences at a
bounded class.

## Contributions

1. **Computational distance as a definition.** `ucCdist` is the supremum of per-distinguisher
   distances over a class closed under `pure`, composition and coproducts. It is a
   pseudometric bounded by `ucSdist`, non-expansive under pre-composition and under
   post-composition with admissible arrows, and bounded under parallel composition
   ([`UCAdmClass`](UCAdmClass.lean)).
2. **Classes from complexity measures.** A cost on Kleisli arrows, zero on `pure` and
   subadditive under bind, yields a class and a graded family of arrows of cost at most `n`
   ([`MonadCostModel`](MonadCostModel.lean)). Instances: oracle-query cost on syntax trees
   (`spTreeQueryAdm`); total size, which is multiplicative under bind and can be exponential
   in query cost ([`SizeBoundedUC`](SizeBoundedUC.lean)); one operation shape for every
   input ([`CTAdmClass`](CTAdmClass.lean)).
3. **Separation results.** At query cost and at size, a distinguisher that tests the output
   is admissible, so the computational and statistical distances coincide on the canonical
   separating pair ([`QueryBoundedUC`](QueryBoundedUC.lean), [`SizeBoundedUC`](SizeBoundedUC.lean)).
   If every admissible distinguisher has advantage at most `ε` and an inadmissible one
   reaches `c > ε`, then `ucCdist ≤ ε < c ≤ ucSdist` (`ucCdist_lt_ucSdist_of_bounded`).
4. **Three levels of emulation** ([`UCLevels`](UCLevels.lean)): the statistical distance;
   `ucCdist` with any simulator; `ucCdist` with an admissible simulator. Each is transitive
   and monotone in `ε`, and levels 1 and 3 each imply level 2.
5. **Equivalences at a bounded class.** Dummy-adversary completeness and the equivalence of
   per-adversary and uniform simulators, over `ucSdist` ([`DummyAdversary`](DummyAdversary.lean))
   and over `ucCdist` with admissible adversaries; the equivalence of a construction (a
   converter relating the two protocols within `ε`) with UC emulation
   ([`CompUCEquivalence`](CompUCEquivalence.lean)); both instantiated at query cost and size.
6. **Robust compilation at level 3** ([`RCL3`](RCL3.lean)): equivalent to a bound on `ucCdist`;
   for a fixed simulator construction, level-3 emulation is equivalent to a preservation
   property. A per-distinguisher notion of trace relation has `ucCdist` as its least bound
   ([`TraceRelating`](TraceRelating.lean)).
7. **Expected cost** ([`ExpectedCost`](../Unary/ExpectedCost.lean)): a cost counter averaged by
   the expectation algebra of [`ExpectationWP`](../Unary/ExpectationWP.lean). The bind law
   holds as an inequality, and as an equality for lossless continuations; worst-case query
   cost bounds expected cost; a loop that retries an attempt of expected cost `C` and
   success probability `p` has expected cost at most `C / p`.
8. **Security parameter** ([`ConcreteReductions`](ConcreteReductions.lean)): negligible
   functions and emulation with a negligible bound, transitive and stable under
   polynomially many hybrids.

## Relation to the literature

- Level 1 at `ε = 0` is the perfect UC of Patrignani, Künnemann, Wahby and Cecchetti
  (TOPLAS 2024, Def. 2), for `ε > 0` the statistical UC of Künnemann, Patrignani and
  Cecchetti (CSF 2024, §IV-A). Levels 2 and 3 are instances of the predicate-parametrised
  robust compilation of the CSF paper (Def. 7); its computational UC (Def. 3) also bounds the
  adversary. The level-3 equivalences of item 6 correspond to their UC ⟺ RHP theorems
  (TOPLAS Thm. 4, CSF Thms. 2–3) for a fixed simulator.
- Item 5 follows Canetti's dummy-adversary completeness and black-box simulation
  (ePrint 2000/067, Claims 11 and 13), stated here for distances. The notion of
  construction is Maurer's (TOSCA 2011, Def. 3, security condition); its equivalence with UC
  emulation is ours.
- The trace relations of item 6 are a quantitative analogue of those of Abate et al.
  (ESOP 2020, Def. 1.2), whose setting has no probabilities.
- The constant-time class is the observational constant-time condition of Barthe et al.
  (POPL 2020, Def. 3.1) with every input secret.
- The expectation algebra is Hasuo's (TCS 2015, Def. 2.4). The bind law of item 7
  corresponds to the sequential rule of the ert calculus (Kaminski et al., J. ACM 2018,
  Table 1 and Thm. 8.1), and the retry bound to the extractor construction of Bellare and
  Goldreich (CRYPTO 1992, §6).

## References

- Marco Patrignani, Robert Künnemann, Riad S. Wahby, Ethan Cecchetti. Universal Composability
  Is Robust Compilation. ACM TOPLAS 46(4), 2024.
- Robert Künnemann, Marco Patrignani, Ethan Cecchetti. Computationally Bounded Robust
  Compilation and Universally Composable Security. CSF 2024.
- Ran Canetti. Universally Composable Security: A New Paradigm for Cryptographic Protocols.
  FOCS 2001; IACR ePrint 2000/067, version of 2020-02-11.
- Ueli Maurer. Constructive Cryptography — A New Paradigm for Security Definitions and
  Proofs. TOSCA 2011.
- Carmine Abate, Roberto Blanco, Ștefan Ciobâcă, Adrien Durier, Deepak Garg, Cătălin Hrițcu,
  Marco Patrignani, Éric Tanter, Jérémy Thibault. Trace-Relating Compiler Correctness and
  Secure Compilation. ESOP 2020.
- Gilles Barthe, Sandrine Blazy, Benjamin Grégoire, Rémi Hutin, Vincent Laporte, David
  Pichardie, Alix Trieu. Formal Verification of a Constant-Time Preserving C Compiler. POPL 2020.
- Ichiro Hasuo. Generic Weakest Precondition Semantics from Monads Enriched with Order.
  Theoretical Computer Science 604, 2015.
- Benjamin Lucien Kaminski, Joost-Pieter Katoen, Christoph Matheja, Federico Olmedo. Weakest
  Precondition Reasoning for Expected Runtimes of Randomized Algorithms. J. ACM 65(5), 2018.
- Mihir Bellare, Oded Goldreich. On Defining Proofs of Knowledge. CRYPTO 1992.
