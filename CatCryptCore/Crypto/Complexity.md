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
| Constant-time shape: the `SPTree` with return values erased | [`UCAdmClass_of_CTClass`](CTAdmClass.lean), [`ct_spComp`](CTAdmClass.lean) | arrows given by syntax trees with one operation shape for every input form an admissibility class, contained in the query-bounded class (`ct_spComp_implies_queryAdm`) |
| Expected cost: credits threaded through an `SPComp`, averaged by the expectation algebra | [`ecost`](../Unary/ExpectedCost.lean) | the bind law ([`ecost_bind_le`](../Unary/ExpectedCost.lean), exact for lossless continuations: `ecost_bind`); worst-case query cost bounds expected cost ([`ecost_compileCharged_le_queryCost`](../Unary/ExpectedCost.lean), [`ecost_of_spTreeQueryAdm`](../Unary/ExpectedCost.lean)); counting does not change the program ([`compileCharged_erase`](../Unary/ExpectedCost.lean)); a retry loop with per-round cost `C` and success probability `p` has expected cost at most `C / p` ([`ecost_retryN_le_div`](../Unary/ExpectedCost.lean)) |
| Oracle-query count in a pHL judgment | [`Unary/QueryBound`](../Unary/QueryBound.lean) | after `q` queries the probability of a bad event is at most `q * ε` (`prBad_induction`, `advantage_le_query_bound_derived`) |
| Ticks in a graded state monad | [`CostM σ n`](../XDijkstra/XCostMonad.lean) | every run of a `CostM σ n` program counts at most `n` ticks (`CostM.cost_le`); the family is a lawful graded monad over `(ℕ, +, 0)` with a weakest-precondition instance whose grade is `n` |

The trivial classes, every arrow admissible, are the instances for `SPComp`
([`UCAdmClass/SPCompInstance`](UCAdmClass/SPCompInstance.lean)), `SDistr`
([`UCAdmClass/SDistrInstance`](UCAdmClass/SDistrInstance.lean)) and the round-indexed monad
`RoundM n` ([`UCMonad/RoundMCompDist`](UCMonad/RoundMCompDist.lean)); for them `ucCdist`
equals the statistical distance (`ucCdist_eq_sdistRoundM` for `RoundM n`).

## Security levels and equivalences

[`UCLevels`](UCLevels.lean) defines Patrignani's three levels of UC emulation: level 1 with the
statistical distance, level 2 with `ucCdist` (`UCEmulatesL2`), level 3 with `ucCdist` and a
simulator construction that preserves admissibility (`UCEmulatesL3`, `UCEmulatesAlgL3`). Level 1
implies level 2 (`UCEmulatesL2_of_L1`) and level 3 implies level 2 (`UCEmulatesL3_implies_L2`);
each level is reflexive, transitive and monotone in `ε`.

[`DummyAdversary`](DummyAdversary.lean) proves that emulation against the dummy adversary
implies emulation against every adversary (`dummy_completeness`) and that a specialised
simulator yields a uniform construction (`specialized_iff_general`).
[`CompUCEquivalence`](CompUCEquivalence.lean) proves the same at `ucCdist` with admissible
adversaries (`ucEmulatesCdist_iff_dummy`), and the equivalence of constructive-cryptography
construction with UC emulation (`ccConstructsCdist_iff_ucEmulatesCdist`).
[`QueryBoundedUC`](QueryBoundedUC.lean) and [`SizeBoundedUC`](SizeBoundedUC.lean) instantiate
both equivalences at the query-bounded and size-bounded classes.

[`ConcreteReductions`](ConcreteReductions.lean) adds the security parameter: negligible
functions (`IsNegligible`, closed under sums and under multiplication by a polynomial,
`isNegligible_add`, `isNegligible_poly_mul`) and UC emulation with a negligible bound
(`UCEmulatesNegl`), transitive (`UCEmulatesNegl_trans`) and stable under polynomially many
hybrids (`UCEmulatesNegl_hybrid_bound`).

## Secure compilation at level 3

[`RCL3`](RCL3.lean) states robust compilation at level 3 and proves it equivalent to a bound
on `ucCdist` (`RC_L3_iff_ucCdist`) and to robust hyperproperty preservation at level 3
(`UCEmulatesAlgL3_iff_RHPL3`); [`RCL3SPComp`](RCL3SPComp.lean) proves the parallel-composition
bound for `SPComp`. [`TraceRelating`](TraceRelating.lean) proves that `ucCdist` is the least
bound of a trace-relating compiler over admissible distinguishers
(`ucCdist_eq_sInf_traceRelating`), and that a bound `ε` over all distinguishers holds exactly
when `ucSdist ≤ ε` (`traceRelatingL1_iff_ucSdist`).
