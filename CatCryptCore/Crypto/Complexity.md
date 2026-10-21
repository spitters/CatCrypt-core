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
   ([`MonadCostModel`](MonadCostModel.lean)). Query cost on `SPComp` is an instance: the cost
   of an arrow is the least worst-case oracle-query cost of a syntax tree compiling to it, and
   the class of arrows with a tree of bounded query cost (`spTreeQueryAdm`) is the class this
   instance induces (`spTreeQueryAdm_eq_costModel`). A second class consists of arrows with
   a tree of bounded total size, which is multiplicative under bind and can be exponential in
   query cost ([`SizeBoundedUC`](SizeBoundedUC.lean)). An abstract constant-time predicate closed
   under `pure`, composition and coproducts yields a class; the concrete predicate "one
   operation shape for every input" is closed under `pure` and composition, is contained in
   the query class, and is closed under coproducts only when the two branches have the same
   shape ([`CTAdmClass`](CTAdmClass.lean)).
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
   and over `ucCdist` with admissible adversaries ([`CompUCEquivalence`](CompUCEquivalence.lean)),
   instantiated at query cost and size.
6. **Robust compilation at level 3** ([`RCL3`](RCL3.lean)): equivalent to a bound on `ucCdist`;
   for a fixed simulator construction, level-3 emulation is equivalent to a preservation
   property. A per-distinguisher notion of trace relation has `ucCdist` as its least bound
   ([`TraceRelating`](TraceRelating.lean)).
7. **Expected cost** ([`ExpectedCost`](../Unary/ExpectedCost.lean)): a cost counter averaged by
   the expectation algebra of [`ExpectationWP`](../Unary/ExpectationWP.lean), where ordered
   monad algebras are proved to be exactly the order-congruent Eilenberg–Moore algebras
   (`orderedMonadAlgebra_laws_iff`). The bind law
   holds as an inequality, and as an equality for lossless continuations; worst-case query
   cost bounds expected cost; a loop that retries an attempt of expected cost `C` and
   success probability `p` has expected cost at most `C / p`.
8. **Security parameter** ([`ConcreteReductions`](ConcreteReductions.lean)): negligible
   functions and emulation with a negligible bound, transitive and stable under
   polynomially many hybrids.

## Step time as a grading

[`XTimedMonad`](../XDijkstra/XTimedMonad.lean) connects the step-time trees of `derive_timed`
and `derive_reduction` (`SPTree.Timed`, `SPTree.Timed.stepTime`) to the graded program logic and
to the cost classes above.

- `TimedM n α` is the type of step-prefixed trees `(c, t) : ℕ × SPTree.Timed α` with
  `stepTime (c, t) ≤ n`. It is a lawful graded monad over `(ℕ, +, 0)` (`GradedMonad`,
  `LawfulGradedMonad`): return is the leaf at index `0`, bind is the costed bind
  `SPTree.Timed.bind` at the sum of the indices, and `TimedM.relax` moves along `≤`. Programs are
  written as `gdo` blocks.
- The observation `timeWP` at the shape `.graded ℕ .pure` has grade `n` and weakest precondition
  "the postcondition holds at every leaf". Its lemmas are in the `xspec` set, so `xmvcgen!`
  reduces the time bound of a `gdo` block to an inequality between numbers; `TimedM.sound` turns
  a triple and a grade bound into a bound on `stepTime`. `XTimedMonadTest` proves the time bound
  of the costed distinguisher `ckaPubRedOf.tree.timed` (`KEMCKA`) this way.
- `TimedM` is graded as `CostM σ n` is (`XCostMonad`): `CostM` bounds the tick count of a
  deterministic state program on every run, `TimedM` the worst-case time of a tree over its
  branches. `TickM` (`XCostMonadModel`) is a monad on `Type → Type`; the step-prefixed trees live
  in `Type 1`, so their unbounded counterpart is not a `MonadCostModel` instance.
- The step-time cost of an `SPComp` arrow, `spTreeTimeCost`, is the least time of a step-prefixed
  tree family whose erasure compiles to the arrow, and `spTreeTimeCost_le_iff` identifies the
  arrows of cost at most `n` with the erasures of the arrows into `TimedM n`. The infimum may take
  zero step costs, and the query cost of an erased tree is at most its time, so
  `spTreeTimeCost = spTreeQueryCost`. The cost model `timeCostModel` is the query-cost instance
  (`timeCostModel_eq`) and satisfies all four laws: zero on `pure`, subadditive under bind,
  coproduct at most the maximum, and `cost_precomp`. Precomposition with a Lean function is not
  charged, whatever the cost of computing the function; a time class that charges it carries the
  step cost of the function in the index of `TimedM`, as `SPTree.Timed.map f fc` does.

## Time over the deep language D

[`Complexity/D/TimeAdm`](../Complexity/D/TimeAdm.lean) defines a time class in which the pure
computation of an arrow is charged. Time is the step count of the deep call-by-value language D
([`Complexity/D`](../Complexity/D/README.md)), whose cost model is that of the weak call-by-value
λ-calculus L of Forster and Kunze (ITP 2019; with Roth, POPL 2020).

- `TimeAdm O n f` holds when a closed D-term `t : Tm [] (a ⇒ b)`, `a` and `b` first-order,
  evaluates without effects to a closure whose application to every input costs at most `n`
  steps and means `f` in `SPComp` (`TimeRealizer`; `TimeRealizer.run_den` relates it to the
  denotation `Tm.den`). The realizer is a closed term: a function value of D is a Lean
  function, and quantifying over values would admit functions of cost zero. The bound is a
  constant, the convention of concrete security, so that the laws compose without bounds on
  output sizes.
- The laws of `UCAdmClass` hold in graded form: `pure` at time `1` (`timeAdm_pure`), bind at
  the sum of the times plus `3` (`timeAdm_bind`, through `Tm.compose`), the coproduct at the
  maximum plus `2` (`timeAdm_mapSum`), and precomposition by a function that a closed D-term
  computes at time `p` at `p + n + 3` (`timeAdm_precomp`). Precomposition by an arbitrary Lean
  function is not admissible at any constant time; the module docstring gives the argument
  for the parity of the bit length on `ℕ`. The class is therefore a graded family of
  predicates and not a `UCAdmClass` instance.
- `ucCdistTime O t` is `ucCdist` over the distinguishers admissible at time `t`: a pseudometric
  bounded by `sdist` and monotone in `t`; pre-composition does not increase it, and
  post-composition with an arrow admissible at time `s` and the coproduct move the time to
  `s + t + 3` and `t + 4` (`ucCdistTime_comp_right`, `ucCdistTime_mapSum_le`).
- The query, size and shape classes admit every pure test `pure ∘ p`, and the step-time cost
  of `XTimedMonad` equals query cost (`spTreeTimeCost_eq_spTreeQueryCost`), since the pure
  computation of a tree carries no cost of its own. In the D class the range test of a
  generator `G : S → Y` is charged: a term computing it from `G` enumerates the seeds at time
  about `|S| · cost(G)`, so below that time it is admissible only through a cheaper inverse of
  `G`. This is the separation that item 3 lacks for the other classes; the module docstring
  states it as an argument, not as a formal lower bound.

## Relation to the literature

- Security definitions parametrised by an admissibility predicate with an additive cost model
  are due to Petcher and Morrisett (FCF, POST 2015, §3.7). Barbosa, Barthe, Grégoire, Koutsos
  and Strub (CCS 2021) prove costs in a Hoare logic and UC transitivity, composition and
  dummy-adversary completeness under cost-restricted simulators and environments. The
  distance as a supremum over a distinguisher class closed under converters is Maurer's
  (TOSCA 2011, §4.5). New in items 1–2 are the cost-model axioms on the Kleisli arrows of an
  arbitrary monad and the query, size and shape classes on `SPComp` syntax trees; item 3
  states two elementary facts for these classes.
- VCVio already instruments oracle computations with an additive cost, defines expected cost
  through its weakest precondition and bounds it by worst-case query bounds; eHL (Avanzini et
  al., OOPSLA 2024) proves expected-cost bounds in EasyCrypt. New in item 7 are the bind
  inequality on the stateful monad `SPComp` and the retry bound for a generic round.
- Level 1 at `ε = 0` is the perfect UC of Patrignani, Künnemann, Wahby and Cecchetti
  (TOPLAS 2024, Def. 2), for `ε > 0` the statistical UC of Künnemann, Patrignani and
  Cecchetti (CSF 2024, §IV-A). Levels 2 and 3 are instances of the predicate-parametrised
  robust compilation of the CSF paper (Def. 7); its computational UC (Def. 3) also bounds the
  adversary. The level-3 equivalences of item 6 correspond to their UC ⟺ RHP theorems
  (TOPLAS Thm. 4, CSF Thms. 2–3) for a fixed simulator.
- Item 5 follows Canetti's dummy-adversary completeness and black-box simulation
  (ePrint 2000/067, Claims 11 and 13), stated here for distances and for single-shot
  systems, in which the adversary receives one leak and sends nothing.
- The trace relations of item 6 are a quantitative analogue of those of Abate et al.
  (ESOP 2020, Def. 1.2), whose setting has no probabilities.
- The concrete constant-time predicate is the observational constant-time condition of
  Barthe et al. (POPL 2020, Def. 3.1) with every input secret.
- The ordered monad algebras of Loom (Gladshtein et al., POPL 2026, Def. 3.2) are, by
  `orderedMonadAlgebra_laws_iff`, the order-congruent Eilenberg–Moore algebras of Hasuo
  (TCS 2015, Def. 3.3 and Prop. 3.4) and the Pos-relative algebras of Hino, Kobayashi,
  Hasuo and Jacobs (LICS 2016, Def. 4.2 and Prop. 4.12); Maillard et al. (ICFP 2019, §4.4)
  relate such algebras to effect observations. Loom cites Maillard et al. but not Hasuo or
  Hino et al.; the Lean theorem makes the identification explicit. The bind law of item 7
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
- Vladimir Gladshtein, George Pîrlea, Qiyuan Zhao, Vitaly Kurin, Ilya Sergey. Foundational
  Multi-Modal Program Verifiers. POPL 2026.
- Wataru Hino, Hiroki Kobayashi, Ichiro Hasuo, Bart Jacobs. Healthiness from Duality.
  LICS 2016.
- Kenji Maillard, Danel Ahman, Robert Atkey, Guido Martínez, Cătălin Hriţcu, Exequiel Rivas,
  Éric Tanter. Dijkstra Monads for All. ICFP 2019.
- Adam Petcher, Greg Morrisett. The Foundational Cryptography Framework. POST 2015.
- Manuel Barbosa, Gilles Barthe, Benjamin Grégoire, Adrien Koutsos, Pierre-Yves Strub.
  Mechanized Proofs of Adversarial Complexity and Application to Universal Composability.
  CCS 2021.
- Martin Avanzini, Gilles Barthe, Benjamin Grégoire, Georg Moser, Gabriele Vanoni. Hopping
  Proofs of Expectation-Based Properties. OOPSLA 2024.
