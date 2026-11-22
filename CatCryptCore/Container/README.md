# Containers, the Diller–Nahm category and the cost of programs

A costed program is a morphism of the Diller–Nahm category of containers (Moss and von Glehn,
LICS 2018, §8): a forward map on shapes and a backward map sending a position of the output to a
finite multiset of positions of the input, its demand. Composition is the bind of the multiset
monad, so use counts multiply and costs compose as `c₂ + n₂ · c₁` (`Clocked.toDN_comp`). A logic
interpreted in this category turns derivations into programs whose demand is bounded by the use
counts of their hypotheses; extractors are realizers of derivations, and their cost is a use
count. Replacing multisets by finitely supported measures gives expected demands, and so the
expected cost of rewinding.

## The category

- [`DillerNahm`](DillerNahm.lean): a first-order costed function is a linear morphism
  (`Costed.equivIsLinear`), and costed functions with use counts compose in the category.
- [`DNBang`](DNBang.lean), [`DNGraded`](DNGraded.lean), [`DialecticaCat`](DialecticaCat.lean):
  the category is the co-Kleisli category of the multiset comonad `bang` on lenses
  (`dnCokleisliEquiv`); the graded exponential of bounded linear logic, under which the
  composition laws of use and query counts are products of count matrices; de Paiva's Dialectica
  category, symmetric monoidal closed.
- [`DNCert`](DNCert.lean): a use bound of a program tree is a Diller–Nahm morphism, and
  interpreting calls through a handler composes use bounds by the multiset bind
  (`demandLens_comp`).
- [`Amortized`](Amortized.lean): a step whose demand depends on a potential of the state; the
  `q`-fold composite has Tarjan's amortized bound (`Clocked.iter_potential_cost_le`).
- [`ExpectedDN`](ExpectedDN.lean): demands as finitely supported measures; the price of a
  composite is the composite of prices, which is linearity of expectation (`EDNLens.price_comp`).

## Logic and extraction

- [`GodelFibration`](GodelFibration.lean): Dialectica predicates over the category, with the
  quantifier and implication adjunctions, choice, independence of premise and the Diller–Nahm
  form of Markov's principle.
- [`DNLogic`](DNLogic.lean): natural deduction for positive many-sorted logic, sound for truth
  and for the Diller–Nahm meaning; a derivation has a realizer (`Deriv.realize`) whose demand on
  a hypothesis is bounded by its use count (`Deriv.card_back_le`).
- [`DNLogicSigma`](DNLogicSigma.lean), [`DNLogicShares`](DNLogicShares.lean),
  [`SchnorrDN`](SchnorrDN.lean): special soundness as a derivation using the prover twice, so
  the extractor of a Σ-protocol is its realizer; threshold reconstruction; the Schnorr
  extraction followed through derivation, morphism, composition and price.

## Expected cost and rewinding

- [`GodelFibrationW`](GodelFibrationW.lean), [`GodelFibrationWIter`](GodelFibrationWIter.lean):
  derivations with expected use counts bounding the expected demand; iteration as powers of
  affine count matrices, and the retry rule with expected count `c + k/p`
  (`wuseCount_retryCollect`).
- [`ExpectedDNOp`](ExpectedDNOp.lean), [`DNLogicForking`](DNLogicForking.lean): the operational
  retry loop and threshold extractor; the rewinding Fiat–Shamir extractor, sound, with expected
  cost at most its certified time per fork plus the price of the witness check, divided by the
  forking bound (`forkExtractor_timed`).

## Classical logic and proof mining

- [`DNLogicNeg`](DNLogicNeg.lean): the Gödel–Gentzen translation into the logic; from a
  classical derivation of a `Π⁰₂` statement, a function satisfying it (`CDeriv.extract_spec`).
- [`DNLogicMono`](DNLogicMono.lean), [`DNLogicMonoClassical`](DNLogicMonoClassical.lean): the
  monotone interpretation (Howard, Kohlenbach); bound extraction as a cost majorant, with a
  witness of size at most `M (size x)` (`Deriv.exists_le_pi2Bound`), also from classical
  derivations.
- [`DNLogicMetastable`](DNLogicMetastable.lean): for `∀∃∀` statements, the finite form of
  Kreisel's no-counterexample interpretation, which gives metastability bounds. The
  `DNLogicTest*` modules apply the extraction to Euclid's theorem, monotone convergence and the
  hybrid lemma.
- [`DNLogicTestPrimes`](DNLogicTestPrimes.lean): Euclid's theorem that every `n` has a prime
  `p > n`, as a classical derivation `CDeriv` from two hypotheses, with extraction and bound.
- [`DNLogicTestMonotone`](DNLogicTestMonotone.lean): the combinatorial core of the metastability
  of a nondecreasing sequence in `[0, 1]`, as a realized axiom (`gapHyp a`) of the Diller–Nahm
  logic.
- [`DNLogicTestHybrid`](DNLogicTestHybrid.lean): the averaging step of a hybrid argument: if
  `ε ≤ |a q - a 0|` then some `j < q` has `ε / q ≤ |a (j + 1) - a j|`, mined from its classical
  proof.

## Type theory and parametricity

- [`CwF`](CwF.lean), [`CwFPi`](CwFPi.lean), [`PolyNaturalModel`](PolyNaturalModel.lean),
  [`PolyPiSigma`](PolyPiSigma.lean), [`WTypes`](WTypes.lean): the polynomial model of type
  theory over `Type`, with dependent sums and products, identity types and W-types.
- [`Code`](Code.lean), [`CodeCost`](CodeCost.lean), [`CodeRel`](CodeRel.lean),
  [`QuotientFree`](QuotientFree.lean): codes for signatures of program trees, whose cost is
  PolyFun's charge fold and whose relational lifts relate programs over two signatures.
- [`DNRel`](DNRel.lean), [`PolyRel`](PolyRel.lean): squares of Diller–Nahm morphisms over
  relations of signatures; related prices give equal prices of related demands
  (`SigRel.DNSquare.price_eq`).
- [`RGraphCwF`](RGraphCwF.lean), [`RGraphUniverse`](RGraphUniverse.lean),
  [`PolyRGraph`](PolyRGraph.lean), [`PolyRGraphUniverse`](PolyRGraphUniverse.lean): the
  reflexive-graph model of Atkey, Ghani and Johann, in which every term preserves relations and
  the polymorphic identity is unique (`Tm.polyId_eq`); the polynomial model over it, where every
  relation of signatures arises from a type.

The cost model these morphisms interpret is that of the time certificates
([`Tactics/README.md`](../Tactics/README.md#time-certificates)) and of the deep language D
([`Complexity/D/README.md`](../Complexity/D/README.md)).
