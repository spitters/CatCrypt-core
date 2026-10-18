# Concrete security and the cost of reductions

CatCrypt states security concretely: a theorem bounds the advantage of every adversary by the
advantages of explicit reductions plus a statistical term, and the efficiency of each reduction
is a separate statement about its running time. The complexity measures of the library serve
the purposes of §3; their results and relation to the literature are in [Complexity.md](Complexity.md).

## 1. The convention

A computational security theorem has the form

```
for every adversary A,   Adv_protocol(A) ≤ Σᵢ Adv_primᵢ(Bᵢ A) + ε_stat
```

where each reduction `Bᵢ` is a definition in the same file, `Adv_primᵢ` is the advantage in the
game of a primitive, and `ε_stat` is an information-theoretic term, a number or a function of
the query bounds of `A`. This is the form of the code-based game proofs of CertiCrypt and
EasyCrypt [BGZ09, BGHZ11] and of concrete security after Bellare and Rogaway [BR06]. For
example, `cascade_prf_bound` ([Examples/PRF.lean](../Examples/PRF.lean)) bounds the PRF
advantage of the cascade against an oracle adversary `A` with `A.IsQueryBound q` by the PRF
advantages of `cascadeRedInner F A` and `cascadeRedOuter A` plus `q(q−1)/2 / |D|`.

A Lean adversary is an arbitrary function, and the theorem holds for every one. Its content for
an efficient `A` comes from two further facts: `Bᵢ A` is efficient when `A` is (§2), and the
assumption on the primitive bounds `Adv_primᵢ` at efficient adversaries. The assumption stays
outside the theorem. Two forms are excluded. A hypothesis `∀ A, Adv_prim(A) ≤ ε` on a
computational game, under any name (a class, a structure field, an assumed reduction `∃ B`),
fails for every primitive when `A` ranges over unbounded functions, since exhaustive search
breaks it. A bound `⨆ A, Adv_prim(B A)` replaces the adversary at hand by the strongest one.

UC statements are made for each adversary and environment. `UCEmulatesCSim spec π F sim bound`
([UCConcrete.lean](UCConcrete.lean)) states that for every adversary `A` and environment `Z`
(an input, an initial heap and a distinguisher) the gap between the real run with `A` and the
ideal run with the simulator `sim A` is at most `bound A Z`, for instance `DDH_Advantage (B A Z)`
for an explicit reduction `B`. Transitivity, subroutine and parallel composition are
`UCEmulatesCSim.trans`, `UCEmulatesCSim_compile` and `UCEmulatesCSim_par`; `UCFromGameC` turns
a concrete game bound into concrete UC emulation. The numeric `UCEmulates ε` ([UC.lean](UC.lean))
bounds the statistical distance over all distinguishers and serves information-theoretic
protocols; `UCEmulatesC_const_iff` identifies it with `UCEmulatesC` at a constant bound.
Asymptotic statements (`IsNegligible`, `UCEmulatesNegl`, `isNegligible_poly_mul`) are
in [ConcreteReductions.lean](ConcreteReductions.lean).

## 2. Efficiency of reductions

For each reduction the statement to certify is

```
time(Bᵢ A) ≤ k · time(A) + q · t + c
```

where `q` is the number of oracle queries of `A`, `t` the cost of answering one, `k` the number
of runs of `A` inside `Bᵢ` (one for a black-box reduction, more under rewinding) and `c` the
remaining work of `Bᵢ`. EasyCrypt proves statements of this form in the cost logic of
[BBGKS21], with the adversary an abstract module whose cost is a parameter. CatCrypt certifies
them by the following construction, applied reduction by reduction, starting with the
reductions written as oracle trees.

1. Costed mirrors. The oracle trees `OracleAdv` ([OracleAdversary.lean](OracleAdversary.lean))
   and the syntax trees `SPTree` ([SPTree.lean](../Core/SPTree.lean)) have mirrors
   `OracleAdv.Timed` ([OracleAdversaryTimed.lean](OracleAdversaryTimed.lean)) and `SPTree.Timed`
   ([SPTreeTimed.lean](../Core/SPTreeTimed.lean)) with the same constructors, in which each
   sampling and query node also carries the cost of computing the next node. `erase` sends a
   mirror to the plain tree; `TimeBound` sums node and step costs along every path. Its laws
   are the time analogues of `isQueryBound_bind` and `isQueryBound_simulate`
   ([OracleSimulation.lean](OracleSimulation.lean)): `timeBound_bind`, and `timeBound_simulate`,
   by which `OracleAdv.simulate impl A` has time at most `T_A + q_A · t_impl`. `compileTimed`
   sends a costed syntax tree to `CostComp` with expected cost at most its time
   (`ecost_compileTimed_le_time`).
2. The adversary as a costed witness. A time theorem quantifies over costed adversaries whose
   erasure is `A` and whose time is at most `T`, as §1 quantifies over `A` with
   `A.IsQueryBound q`.
3. The reduction instrumented. Each reduction `B` has a costed version with two kernel-checked
   theorems: the erasure equation (the costed `B` applied to a costed `A` erases to `B A`) and
   the time theorem `k · T + q · t + c`.
4. Derived costs. The step costs are derived from the reduction's code by the rules of
   call-by-value evaluation: a call costs one plus the callee's cost at its arguments; `if` and
   `match` cost one plus the branch taken; constructors, literals, projections and variables
   are free. Isabelle's `time_fun` [HOL] and Hopwood's `assert_efficient` for Lean [Hop26]
   derive costs in this way; the latter prices a function-typed parameter such as the
   adversary through a cost argument of its own. Primitives take registered costs: word and
   field operations, table lookups, and one unit per sampling node, as in `SPTree.queryCost`.

The kernel checks the erasure equation, so an error in a derived cost can misstate a running
time but cannot change the reduction whose advantage §1 bounds. The trusted base of a time
theorem is the rule set and the registered primitive costs, listed with the theorem. For a
family of reductions indexed by the security parameter, polynomial time theorems supply the
running-time conjunct of the asymptotic statements of §1, which bound advantages.

## 3. What the complexity measures are for

Query bounds of adversaries. `OracleAdv.IsQueryBound A q` states that every path of `A` asks at
most `q` queries; `IsQueryBoundBy cost` weights each query; `QueryCostLe` states the same for
`OracleProg` trees ([Signatures/EUFCMA.lean](Signatures/EUFCMA.lean)). These are the hypotheses of
the statistical terms of §1, such as `q(q−1)/2 / |D|` above or `q / |T|` for guessing a tag in
`T`, and `isQueryBound_simulate` carries them through a reduction.

Expected cost of extractors. `CostComp` and `ecost` ([ExpectedCost.lean](../Unary/ExpectedCost.lean))
give the expected value of the charges a program accumulates; `ecost_bind_le` is the tower
law, and `ecost_retryN_le_div` bounds a loop retrying an attempt of expected cost `C` and
success probability `p` by `C / p`. A rewinding extractor is bounded with these two quantities, and the per-attempt cost is a
parameter; a time theorem of §2 for the prover makes it a function of the prover's running time.

Admissibility classes and computational UC. `UCAdmClass` ([UCAdmClass.lean](UCAdmClass.lean))
is a predicate on Kleisli arrows closed under `pure`, composition, coproducts and precomposition
with functions (`adm_pure`, `adm_bind`, `adm_mapSum`, `adm_precomp`); `ucCdist` is the distance
over admissible distinguishers. A `MonadCostModel` ([MonadCostModel.lean](MonadCostModel.lean)),
a cost on Kleisli arrows zero on `pure` and subadditive under composition, induces a class. On
`SPComp` the instances are the query class `spTreeQueryAdm`, the size class `spTreeSizeAdm`
([SizeBoundedUC.lean](SizeBoundedUC.lean)) and the shape class of `ct_spComp`
([CTAdmClass.lean](CTAdmClass.lean)). Over them are stated the levels `UCEmulatesL2` and
`UCEmulatesL3` ([UCLevels.lean](UCLevels.lean)) and `UCEmulatesCdist`
([CompUCEquivalence.lean](CompUCEquivalence.lean)), with transitivity, the implications between
levels and dummy-adversary completeness ([QueryBoundedUC.lean](QueryBoundedUC.lean)).

These classes bound the operations of a syntax-tree witness: the query class the `sample`,
`get` and `set` nodes on the worst path (`SPTree.queryCost`), the size class all nodes summed
over branches (`SPTree.size`), the shape class the sequence of operations, the same for every
input. The value in a `ret` node, a value written by `set` and the computation inside a
continuation carry no charge (`queryCost (ret a) = 0`, `size (ret a) = 1`). Every class
therefore contains every pure test `pure ∘ p`, by `adm_pure` and `adm_precomp`
(`adm_pure_predicate`, `adm_pure_predicate_size`). For a generator `G : S → Y` with
`|S| < |Y|`, the range test `p y = decide (∃ s, G s = y)` distinguishes `G` on a uniform seed
from the uniform distribution on `Y` with advantage at least `1 − |S|/|Y|`, so `ucCdist` of this
pair is at least that much in every class on `SPComp`. Computational indistinguishability is
carried by the convention of §1; the classes serve statements about queries, size and shape and
the structure of computational UC.

## 4. Relation to implicit computational complexity

The derived costs of §2 are an automatic cost analysis: a cost function computed from the text
of a program under call-by-value evaluation, as `time_fun` derives a time function from a
function's equations and Forster and Kunze [FK19] certify time bounds of extracted
call-by-value λ-terms. The cost is derived program by program; a bound on it is a theorem.

Implicit computational complexity in the type-theoretic sense characterises a complexity class
by a restriction of the language: safe recursion [BC92], bounded linear logic [GSS92], light
linear and light affine logic [Gir98, AR02] and soft linear logic [Laf04] capture the
polynomial-time functions, and their typable programs are closed under composition; Atkey
[Atk24] surveys these characterisations and extends them to dependent types. The `UCAdmClass`
laws take this closure under composition as their model: the admissible arrows form a wide
subcategory of the Kleisli category. Through `adm_precomp`, which admits precomposition with
every function, the laws also admit every pure test, so a class satisfying them bounds the
effectful operations of an arrow and leaves its pure computation free. The running time of that
pure computation in a reduction is what the derived costs of §2 certify.

## References

- [AR02] A. Asperti, L. Roversi. Intuitionistic light affine logic. ACM TOCL 3(1), 2002.
- [Atk24] R. Atkey. Polynomial time and dependent types. POPL 2024.
- [BBGKS21] M. Barbosa, G. Barthe, B. Grégoire, A. Koutsos, P.-Y. Strub. Mechanized proofs of adversarial complexity and application to universal composability. CCS 2021.
- [BC92] S. Bellantoni, S. Cook. A new recursion-theoretic characterization of the polytime functions. Computational Complexity 2, 1992.
- [BGHZ11] G. Barthe, B. Grégoire, S. Heraud, S. Zanella-Béguelin. Computer-aided security proofs for the working cryptographer. CRYPTO 2011.
- [BGZ09] G. Barthe, B. Grégoire, S. Zanella-Béguelin. Formal certification of code-based cryptographic proofs. POPL 2009.
- [BR06] M. Bellare, P. Rogaway. The security of triple encryption and a framework for code-based game-playing proofs. EUROCRYPT 2006.
- [FK19] Y. Forster, F. Kunze. A certifying extraction with time bounds from Coq to call-by-value lambda calculus. ITP 2019.
- [Gir98] J.-Y. Girard. Light linear logic. Information and Computation 143(2), 1998.
- [GSS92] J.-Y. Girard, A. Scedrov, P. J. Scott. Bounded linear logic: a modular approach to polynomial-time computability. Theoretical Computer Science 97(1), 1992.
- [HOL] Isabelle/HOL, HOL-Library: the `time_fun` command.
- [Hop26] D.-E. Hopwood. Are the reductions efficient? An `efficient` keyword for Lean. Talk, October 2026; implementation in the zcash/ironwood repository.
- [Laf04] Y. Lafont. Soft linear logic and polynomial time. Theoretical Computer Science 318, 2004.
