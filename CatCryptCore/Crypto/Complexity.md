# Complexity measures and computational UC

The modules listed here make the distinguishers of a UC statement range over a class of
programs instead of all Kleisli arrows. The statistical distance `ucSdist` is a supremum over
all distinguishers; the computational distance `ucCdist` is the same supremum restricted to
the *admissible* ones. A complexity measure enters by fixing which arrows are admissible.

## The interface

[`UCAdmClass`](UCAdmClass.lean) is a predicate `adm` on Kleisli arrows `α → T β`, closed under
`pure`, composition and the coproduct `mapSum`. [`UCMonadCompDist`](UCAdmClass.lean) splits
`ucSdist` into one component per distinguisher, and `ucCdist` is the supremum of the components
over admissible distinguishers. From this definition the file proves that `ucCdist` is a
pseudometric (`ucCdist_self`, `ucCdist_sym`, `ucCdist_triangle`), that it is bounded by the
statistical distance (`ucCdist_le_ucSdist`), that post-composition with an admissible arrow
does not increase it (`ucCdist_comp_right`), and that it is bounded under parallel composition
(`ucCdist_mapSum_le`).

[`MonadCostModel`](MonadCostModel.lean) assigns a cost in `ℕ∞` to each Kleisli arrow, zero
on `pure` and subadditive under bind; [`UCAdmClass_of_costModel`](MonadCostModel.lean) makes
the arrows of finite cost admissible, and `costBounded n` is the graded family of arrows of
cost at most `n`.

## The measures

| Measure | Admissibility class | What is proved |
|---|---|---|
| Query cost: oracle calls on the worst path of an `SPTree` | [`spTreeQueryAdm`](MonadCostModel.lean) | an admissibility class obtained from a cost model; some arrows are outside it. Pure output tests have query cost zero, so on the separating pair `Example.π` / `Example.F` the query-bounded distance equals the statistical distance, both `1` ([`ex_queryBounded_no_separation`](QueryBoundedUC.lean)) |
| Total size: all nodes of an `SPTree`, summed over branches | [`spTreeSizeAdm`](SizeBoundedUC.lean) | size can be exponential in query cost ([`wideTree_queryCost`](SizeBoundedUC.lean), [`wideTree_size_ge`](SizeBoundedUC.lean)); size is multiplicative under bind ([`size_bind_mul`](SizeBoundedUC.lean)), so it is not a cost model and the class is built directly. If every admissible distinguisher has advantage at most `ε` and an inadmissible one reaches `c > ε`, then `ucCdist < ucSdist` ([`ucCdist_lt_ucSdist_of_bounded`](SizeBoundedUC.lean), [`ucCdist_lt_ucSdist_strict`](SizeBoundedUC.lean)) |
| Constant-time shape: the `SPTree` with return values erased | [`UCAdmClass_of_CTClass`](CTAdmClass.lean), [`ct_spComp`](CTAdmClass.lean) | arrows given by syntax trees with one operation shape for every input (the observational constant-time condition of Barthe et al., with every input secret) form an admissibility class, contained in the query-bounded class (`ct_spComp_implies_queryAdm`) |
| Expected cost: a cost counter threaded through an `SPComp`, averaged by the expectation algebra | [`ecost`](../Unary/ExpectedCost.lean) | the bind law ([`ecost_bind_le`](../Unary/ExpectedCost.lean), exact for lossless continuations: `ecost_bind`); worst-case query cost bounds expected cost ([`ecost_compileCharged_le_queryCost`](../Unary/ExpectedCost.lean), [`ecost_of_spTreeQueryAdm`](../Unary/ExpectedCost.lean)); counting does not change the program ([`compileCharged_erase`](../Unary/ExpectedCost.lean)); a retry loop with per-round cost `C` and success probability `p` has expected cost at most `C / p` ([`ecost_retryN_le_div`](../Unary/ExpectedCost.lean)) |
| Oracle-query count in a pHL judgment | [`Unary/QueryBound`](../Unary/QueryBound.lean) | after `q` queries the probability of a bad event is at most `q * ε` (`prBad_induction`, `advantage_le_query_bound_derived`) |
| Ticks in a graded state monad | [`CostM σ n`](../XDijkstra/XCostMonad.lean) | every run of a `CostM σ n` program counts at most `n` ticks (`CostM.cost_le`); the family is a lawful graded monad over `(ℕ, +, 0)` with a weakest-precondition instance whose grade is `n` |

The trivial classes, every arrow admissible, are the instances for `SPComp`
([`UCAdmClass/SPCompInstance`](UCAdmClass/SPCompInstance.lean)), `SDistr`
([`UCAdmClass/SDistrInstance`](UCAdmClass/SDistrInstance.lean)) and the round-indexed monad
`RoundM n` ([`UCMonad/RoundMCompDist`](UCMonad/RoundMCompDist.lean)); for them `ucCdist`
equals the statistical distance (`ucCdist_eq_sdistRoundM` for `RoundM n`).

## Security levels and equivalences

[`UCLevels`](UCLevels.lean) defines three levels of UC emulation: level 1 with the
statistical distance, level 2 with `ucCdist` (`UCEmulatesL2`), level 3 with `ucCdist` and a
simulator construction that preserves admissibility (`UCEmulatesL3`, `UCEmulatesAlgL3`). Level 1
implies level 2 (`UCEmulatesL2_of_L1`) and level 3 implies level 2 (`UCEmulatesL3_implies_L2`);
each level is transitive and monotone in `ε`, and reflexive (level 3 for admissible
adversaries). Level 1 is statistical UC; at `ε = 0` it is the perfect UC of Patrignani,
Künnemann, Wahby and Cecchetti (Def. 2), and for `ε > 0` the statistical UC of Künnemann,
Patrignani and Cecchetti (§IV-A). Levels 2 and 3 are instances, not named in that paper, of
its predicate-parametrised robust compilation (Def. 7); its computational UC (Def. 3) also
bounds the adversary. The numbering of the levels is ours, and the bounds are concrete in
`ε`.

[`DummyAdversary`](DummyAdversary.lean) proves, over the statistical distance, that emulation
against the dummy adversary implies emulation against every adversary (`dummy_completeness`;
Canetti, Claim 11) and that per-adversary simulators yield a uniform simulator construction
(`specialized_iff_general`; cf. Canetti's black-box simulation, Claim 13).
[`CompUCEquivalence`](CompUCEquivalence.lean) proves the same at `ucCdist` with admissible
adversaries (`ucEmulatesCdist_iff_dummy`), and that a construction in the sense of Maurer
(TOSCA 2011, Def. 3, security condition only) is equivalent to UC emulation
(`ccConstructsCdist_iff_ucEmulatesCdist`). That equivalence is ours; Maurer and Renner remark
on the relation between the two frameworks without stating it as a theorem.
[`QueryBoundedUC`](QueryBoundedUC.lean) and [`SizeBoundedUC`](SizeBoundedUC.lean) instantiate
both equivalences at the query-bounded and size-bounded classes.

[`ConcreteReductions`](ConcreteReductions.lean) adds the security parameter: negligible
functions (`IsNegligible`, closed under sums and under multiplication by a polynomial,
`isNegligible_add`, `isNegligible_poly_mul`) and UC emulation with a negligible bound
(`UCEmulatesNegl`), transitive (`UCEmulatesNegl_trans`) and stable under polynomially many
hybrids (`UCEmulatesNegl_hybrid_bound`).

## Secure compilation at level 3

[`RCL3`](RCL3.lean) states robust compilation at level 3, as closure under contexts and
admissible distinguishers, and proves it equivalent to a bound on `ucCdist`
(`RC_L3_iff_ucCdist`), and level-3 UC emulation with a fixed simulator construction
equivalent to a level-3 preservation property (`UCEmulatesAlgL3_iff_RHPL3`). These are
analogues of the equivalences of UC with robust hyperproperty preservation in the TOPLAS
(Thm. 4) and CSF (Thms. 2 and 3) papers, whose RHP quantifies "for every target attacker
there is a source attacker"; [`RCL3SPComp`](RCL3SPComp.lean) proves the parallel-composition
bound for `SPComp`. [`TraceRelating`](TraceRelating.lean) defines a quantitative analogue, ours, of
the trace relations of Abate et al., who work without probabilities, and proves that
`ucCdist` is the least bound over admissible distinguishers (`ucCdist_eq_sInf_traceRelating`), and that a bound `ε` over all distinguishers holds exactly
when `ucSdist ≤ ε` (`traceRelatingL1_iff_ucSdist`).

## References

- Marco Patrignani, Robert Künnemann, Riad S. Wahby, Ethan Cecchetti. Universal Composability
  Is Robust Compilation. ACM TOPLAS 46(4), 2024.
- Robert Künnemann, Marco Patrignani, Ethan Cecchetti. Computationally Bounded Robust
  Compilation and Universally Composable Security. CSF 2024.
- Ran Canetti. Universally Composable Security: A New Paradigm for Cryptographic Protocols.
  FOCS 2001; IACR ePrint 2000/067, version of 2020-02-11 (Claims 11 and 13).
- Ueli Maurer. Constructive Cryptography — A New Paradigm for Security Definitions and
  Proofs. TOSCA 2011.
- Ueli Maurer, Renato Renner. Abstract Cryptography. ICS 2011.
- Carmine Abate, Roberto Blanco, Ștefan Ciobâcă, Adrien Durier, Deepak Garg, Cătălin Hrițcu,
  Marco Patrignani, Éric Tanter, Jérémy Thibault. Trace-Relating Compiler Correctness and
  Secure Compilation. ESOP 2020.
- Gilles Barthe, Sandrine Blazy, Benjamin Grégoire, Rémi Hutin, Vincent Laporte, David
  Pichardie, Alix Trieu. Formal Verification of a Constant-Time Preserving C Compiler. POPL 2020.
- Benjamin Lucien Kaminski, Joost-Pieter Katoen, Christoph Matheja, Federico Olmedo. Weakest
  Precondition Reasoning for Expected Runtimes of Randomized Algorithms. J. ACM 65(5), 2018.
- Philipp G. Haselwarter, Kwing Hei Li, Markus de Medeiros, Simon Oddershede Gregersen,
  Alejandro Aguirre, Joseph Tassarotti, Lars Birkedal. Tachis: Higher-Order Separation Logic
  with Credits for Expected Costs. OOPSLA 2024.
- Oded Goldreich. Foundations of Cryptography, Vol. 1, Def. 4.7.2. Cambridge University
  Press, 2001.
- Mihir Bellare, Oded Goldreich. On Defining Proofs of Knowledge. CRYPTO 1992, §6.
