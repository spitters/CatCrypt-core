# XDijkstra: a graded Dijkstra-monad kernel

`CatCryptCore/XDijkstra/` is a weakest-precondition kernel in the style of Lean's
`Std.Do`. A program is observed as a monotone predicate transformer, and a Hoare
triple states that a precondition entails the weakest precondition of a
postcondition. The kernel adds four things that a `Std.Do` triple does not state:

- a grade: a value of an additive monoid (a cost, an error bound) stored in the
  transformer and added under sequencing;
- a separating product on assertions, with a frame rule;
- relational triples: a triple over the product of two transformers, and a
  coupling relation for probability distributions;
- transfer of triples along a monad morphism whose source and target have
  different effect shapes.

All declarations are in the namespace `CatCrypt.XDijkstra`, except those of
`GradedWP.lean`. A tutorial with one short example per feature is in
[`Demo.lean`](Demo.lean).

## For users of `mvcgen`

| `Std.Do` | XDijkstra | Difference |
|---|---|---|
| `PostShape` (`pure`, `arg σ`, `except ε`) | `XPostShape` (`pure`, `arg σ`, `except ε`, `graded G`) | one added constructor for a grade layer; `XPostShape.Grade` is the product of the grade types |
| `Assertion ps` | `XAssertion ps Ω` | assertions take values in a preordered carrier `Ω`; `Ω := Prop` gives plain propositions |
| `ExceptConds ps`, `PostCond α ps` | `XExceptConds ps Ω`, `XPostCond α ps Ω` | a postcondition is a pair `(success, exceptions)`; there is no `⇓` notation |
| `PredTrans ps α` | `XPredTrans ps Ω α`; without a shape, `XCorePT Pred EPred G α` | fields `apply`, `grade`, `mono` |
| `WP m ps`, `wp⟦x⟧` | `XWP m ps Ω`, `XWP.xwp x`; without a shape, `XCoreWP m Pred EPred G`, `XCoreWP.wp x` | no bracket notation is declared; `xwp⟦x⟧` appears in docstrings only. `ps` and `Ω` are not output parameters, so statements name them: `(m := …) (ps := …) (Ω := …)`. Of the parameters of `XCoreWP` only the grade type `G` is an output parameter |
| `Triple x P Q`, `⦃P⦄ x ⦃Q⦄` | `XTriple P x Q` for a program, `XPT P t Q` for a transformer | no bracket notation; the precondition comes first |
| `Q ⊢ₚ Q'` | `Q ⊢ₓ Q'` (`XPostCond.le`, scoped notation) | |
| `@[spec]` | `@[xspec]` | `xspec` is a simp attribute for equations `(op …).apply Q = …` and `(op …).grade.1 = …`; it does not hold Hoare triples |
| `mvcgen` | `xmvcgen`, `xmvcgen_ctl`, `xmvcgen!` | each is a `simp only` call; see "Tactics" |
| `do` blocks of a `Monad` | `gdo` blocks of a `GradedMonad` | the grade of a block is the sum of the grades of its steps; `let x ← e`, `let x := v`, a step, and a final expression or `return v`; no `mut`, loops or early `return` |

Stay with `mvcgen` when the goal is a triple about one program, has no grade and
no separating conjunct. `mvcgen` looks up triple specifications, splits the goal
into named verification conditions and handles loop invariants; the tactics of
this kernel do none of these. Use the kernel when the statement itself needs a
grade bound next to the triple, a frame, a second program, or a change of effect
shape.

## Modules

| Module | Content |
|---|---|
| `XPredCore` | `XCorePT`, a graded transformer over an arbitrary ordered assertion type; `ret`, `bind`, `seq`, `prod`; the sequencing, frame, relational and transfer rules; `XCoreHom`; the observation classes `XCoreWP` and `LawfulXCoreWP`; `XCoreWPHom`, a morphism of observations |
| `XPostShape` | `XPostShape`, `XAssertion`, `XPostCond`, `XPredTrans`, `XWP`, `XPT`, `XTriple`, `XBI`, `XRelTriple`, `XWPMorphism`; the rules of the four features as instances of the core rules; `XPredTrans.equivCore`; `XWP.toCoreWP` and `XWPMorphism.toCoreWPHom` |
| `XMvcgen` | the simp attribute `xspec` and the tactic `xmvcgen` |
| `XMvcgenControl` | `xite`, `xphi`, `xfor` with their reduction lemmas and triple rules; the tactic `xmvcgen_ctl` |
| `XMvcgenReg` | the core reductions added to `xspec`; the tactic `xmvcgen!` |
| `XMorphismInstance` | `thetaX` and `instXWPMorphismBaseChange`: transfer from a state shape to the same shape with an exception layer |
| `XHeapSoundness` | `instXWPStateM` and `stateWP_triple_iff` for `StateM σ`; the heap carrier `HProp V` with `instXBIHProp` |
| `XRelatorPMF` | `IsCoupling`, `Couples`, `XRelTriplePMF` for Mathlib's `PMF` |
| `XQuantaleGradeCore` | the join of grades over `GradeQuantale`; the combinator `xpar` |
| `GradedWP` | an earlier, self-contained transformer with the grade as a type index (`GPredTrans`, `gbind`), in the namespace `CatCrypt.Crypto.SecureCompilation.Ascent.GradedWP` |
| `GradedDo` | the classes `GradedMonad` (`gpure` at grade `0`, `gbind` adding the grades) and `LawfulGradedMonad`; `GradedMonad.gseq`; the block notation `gdo` |
| `XCostMonad` | `CostM σ n`, a state monad with a tick counter, indexed by a bound `n` on the count; `instXWPCostM` at the shape `psCost σ`, which is `.graded ℕ (.arg σ .pure)`; `costWP_triple_iff` and `CostM.sound` against the run; `costWP_seq`, `costWP_bind_grade_fst`; `CostM.instGradedMonad`, `CostM.instLawfulGradedMonad` |
| `XErrMonad` | `ErrM ε`, the sub-distributions that fail with weight at most `ε`; the union bound `sdistr_bind_none_le`; `ErrM.instGradedMonad`, `ErrM.instLawfulGradedMonad`; `instXWPErrM` at the shape `psErr`, which is `.graded ℝ≥0∞ .pure`; `errWP_triple_iff`, `ErrM.sound` and `ErrM.prob_post_ge` against the sub-distribution; `errWP_seq`, `errWP_bind_grade_fst` |
| `XAdvantageHybrid` | `advChain_triangle`, `advChain_uniform`: the triangle inequality over a chain of games; the tactics `advmvcgen`, `advmvcgen_dep` |
| `XDijkstraAll` | imports `XPostShape`, `XMvcgen`, `XRelatorPMF`, `XHeapSoundness` |
| `Demo` | the tutorial |

The directory `Rel/` holds the graded relational layer over the relational monads
`RelQ0` (`PMF` and the sub-distribution monad `SDistr`).

| Module | Content |
|---|---|
| `Rel/XRelQ0` | `XRelTripleQ0 ε R m₁ m₂`, a coupling of two computations up to error `ε`; `xrelQ0_pure`, `xrelQ0_seq` (errors add); `couples_iff_xrelQ0_zero` relates it to `Couples` on `PMF` |
| `Rel/XSDistrSoundness` | `instXWPSDistr` and `sdistrWP_triple_iff`: the support-level observation of `SDistr`; `couplingPT`, a transformer whose grade is a coupling error |
| `Rel/XRelSpecMonad` | `RelPT`, the specification monad on pairs of computations with the error as index; `relPure`, `relBind`, `relBind_spec`, `relSpec_seq` |
| `Rel/XRelMvcgen` | the tactic `relmvcgen`, which applies `relBind_spec` and `relSpec_seq` along a chain of binds |
| `Rel/XRelMvcgenControl` | `relSpec_ite`, `relForN`, `relSpec_forN`: a coupled conditional and a coupled bounded loop; the tactic `relmvcgen_ctl` |
| `Rel/XHybridExample` | a hybrid argument over `SDistr` with the per-hop couplings as hypotheses: `hybrid3_bound`, `hybridN_bound` |
| `Rel/XLargeReduction` | reductions with five hops and with `n` hops: `relSpec5_auto`, `largeN_reduction_uniform`, `largeN_reduction_varying` |
| `Rel/XCombinedAutomation` | the tactics `advmvcgen!`, `advmvcgen_dep!` and `relmvcgen!`, which also discharge the arithmetic side conditions |
| `Rel/XCoreProtocolReduction` | the multi-query PRF reduction as a coupling: `prf_multi_query_coupling` |
| `Rel/XProbUCBaseline` | `sdistr_uc_iff_tvMargin`, `sdistr_uc_le_advantage`, `pmf_uc_zero_iff_eq`: the coupling at equality as a statistical-distance bound on `SDistr` and as equality on `PMF` |

`Category/XCategoricalModel.lean` reads the kernel categorically
(`GradedDijkstraObservation`, `self_gradedDijkstraObservation`,
`grade_axis_is_lawvere_quantale`), `Category/XCategoricalModelRel.lean` does the
same for `RelPT` (`relational_axis_is_monad`, `relational_grade_adds`), and
`Category/CoParaGradedBridge.lean` relates the grade addition of
`GradedWP.gbind` to the size of a protocol interface (`ifaceGrade_hcomp`).

## The four features and their theorems

| Feature | At a shape (`XPostShape`) | Over an arbitrary assertion type (`XPredCore`) |
|---|---|---|
| Grade | `xseq_triple`, `xwp_graded_bind`, `xtriple_grade_le` | `XCorePT.seq_triple`, `XCorePT.seq_grade`, `XCorePT.seq_grade_le` |
| Frame | `xframe`, `xpure_local` | `XCorePT.frame`, `XCorePT.ret_local`, `XCorePT.bind_local`, `XCorePT.seq_local` |
| Relational | `xrel_seq`; for `PMF`: `Couples_bind`, `XRelTriplePMF_seq` | `XCorePT.rel_seq` |
| Morphism | `xwp_morphism` | `XCorePT.Triple.transfer`, `XCoreHom.map_triple`, `XCoreWPHom.triple` |

The grade is a field of the transformer. `xseq x y` has grade
`x.grade + y.grade`. `xbind x f` has the grade of `x`, because the grade of `f a`
depends on the value `a`; the `Monad` instance `instMonad` uses `xbind`, so a
`do` block over `XPredTrans` does not add grades. The monad laws are proved for
the field `apply` (`xbind_pure_apply`, `xpure_bind_apply`, `xbind_assoc_apply`).

A program monad that adds grades under `bind` is therefore a family indexed by
the grade. `CostM σ n α` in `XCostMonad` is such a family: `CostM.bind` takes a
head of index `m` and continuations of a common index `n` to index `m + n`, each
`CostM σ n` has an `XWP` instance whose grade is `n`, and `costWP_seq` identifies
the observation of `CostM.seq` with `xseq` of the observations. `CostM.sound`
states what a triple with a grade bound means for the run: the result satisfies
the postcondition and the number of ticks is at most the bound.

Such a family is an instance of the class `GradedMonad` of `GradedDo`: a return
`gpure` at grade `0` and a bind `gbind` that takes grades `g` and `h` to `g + h`
(graded monads in the sense of Katsumata and of Orchard and Petricek).
`LawfulGradedMonad` states the three monad laws as heterogeneous equalities,
since their sides have the grades `0 + g` and `g`, `g + 0` and `g`,
`(g + h) + k` and `g + (h + k)`. Lean's `do` notation elaborates to `Bind.bind`
at one type constructor and does not apply to a family; the block notation `gdo`
expands to `GradedMonad.gbind` instead, as a rebindable `do` does in Haskell.

```lean
def bumpDo : CostM ℕ (1 + (0 + 2)) Unit := gdo
  CostM.tick 1
  CostM.modify (· + 1)
  CostM.tick 2
```

The expansion nests to the right, so a block with steps of grades `g₁, …, gₙ`
has the grade `g₁ + (g₂ + (… + gₙ))`, with last summand `0` when it ends in
`return`. The grade is not normalised: the type of the block names this sum
(`bumpDo`), or the block is cast by a weakening of the family (`readThenTick`
with `CostM.relax`).

`ErrM ε α` in `XErrMonad` is a second instance, over the sub-distribution type
`SDistr α`, which is `PMF (Option α)`. Its index bounds the failure weight
`d none`, which is `1 - SDistr.mass d` (`one_sub_mass`). The failure weight of a
bind is `d none + ∑' a, d (some a) * f a none` (`sdistr_bind_none_eq`), so bounds
`ε₁` on the head and `ε₂` on every continuation give the bound `ε₁ + ε₂`
(`sdistr_bind_none_le`, the union bound). The observation `errWP` has the
weakest precondition of `sdistrWP`, the support-level observation of `SDistr`,
and the index as grade. `ErrM.sound` states that under a triple with
postcondition `Q` and a grade bound `b` every value of nonzero weight satisfies
`Q` and the failure weight is at most `b`; `ErrM.prob_post_ge` states that the
values satisfying `Q` have total weight at least `1 - b`.

`ErrM` is the unary counterpart of the graded couplings of `Rel/XRelQ0`. There
`XRelTripleQ0 ε R m₁ m₂` relates two computations up to an error `ε`, and
`xrelQ0_seq` adds the errors of a head and of its continuations; in the
specification monad `RelPT` of `Rel/XRelSpecMonad` the error is likewise an index
that `relBind` adds. In both layers the grade is an element of `(ℝ≥0∞, +, 0)`
that bounds a probability and is added under bind. The unary grade bounds the
weight of failure of one computation and its triples speak about the support;
the relational grade bounds the weight on which two computations are not coupled
in the relation. No theorem of this package derives one from the other.

## Tactics

`xmvcgen`, `xmvcgen_ctl` and `xmvcgen!` each expand to one `simp only` call that
unfolds `XTriple` and `XPT` (and `XRelTriple`, except in `xmvcgen_ctl`), rewrites
`apply` and `grade` of the combinators, and unfolds `XAssertion.le`. The goal that
remains is an entailment
in the carrier, or an inequality between grades. Each accepts extra simp
arguments in brackets, usually the definitions of the steps of the program.

- `xmvcgen` uses a fixed list of lemmas.
- `xmvcgen_ctl` uses the fixed list and the `xspec` set.
- `xmvcgen!` uses the `xspec` set only, so a reduction lemma tagged `@[xspec]`
  in a later module is used without a change to the tactic.

## Adding a monad or an operation

1. Choose the shape `ps` and the carrier `Ω`, and write the instance
   `XWP m ps Ω`: a function `xwp : m α → XPredTrans ps Ω α`, giving `apply`,
   `grade` and a proof of `mono`. `instXWPStateM` with `stateWP` is the model
   without a grade, `instXWPCostM` with `costWP` the model with one.
2. State what a triple means for the monad, as `stateWP_triple_iff` does for
   `StateM`, and what the grade means for the run, as `CostM.sound` does. The class `XWP` has no laws; `GradedDijkstraObservation` in
   `Category/XCategoricalModel.lean` states that the observation commutes with
   `pure` and `bind`.
3. For each operation, state the reductions `(op …).apply Q = …` and
   `(op …).grade.1 = …` and tag them `@[simp, xspec]`, as `xite_apply`,
   `xite_grade_fst` and `xboost_grade_fst` are. The module must import `XMvcgen`;
   the attribute cannot be used in the module that registers it.
4. For a separation carrier, write `XBI Ω` (`instXBIHProp`). For a change of
   monad, write `XWPMorphism θ` (`instXWPMorphismBaseChange`).

## `XPostShape` and `XCorePT`

`XCorePT Pred EPred G α` takes the assertion type, the type of exception
postconditions and the grade type as parameters and asks only for `≤` on the
first two. A shape `ps` and a carrier `Ω` compute these parameters:
`XAssertion ps Ω`, `XExceptConds ps Ω` and `ps.Grade`. `XPredTrans.toCore` and
`XPredTrans.ofCore` convert in both directions, `XPredTrans.equivCore` states the
equivalence, and `xpure_toCore`, `xbind_toCore`, `xseq_toCore`, `xprod_toCore`,
`xpt_iff_core` and `xlocal_iff_core` identify the operations, the triple and
locality. A rule that does not mention the shape is proved at `XCorePT` and
instantiated; `xseq_local` in `Demo.lean` is an example.

The observation of a monad is also stated without a shape. `XCoreWP m Pred EPred G`
gives `wp : m α → XCorePT Pred EPred G α`, `XCoreWP.Triple` is the triple of a
program, and `LawfulXCoreWP` states that the observation commutes with `pure` and
`bind`, from which `XCoreWP.bind_triple` follows. The assertion types are
ordinary parameters, since one monad is observed at several of them (`StateM ℕ`
at `Set ℕ` and at `XAssertion (psState ℕ) Prop` in `Demo.lean`); the grade type
is an output parameter, since no argument of a triple mentions it. `XCoreWPHom`
is a morphism between two observations with one map on the pair of
postconditions, as `XWPMorphism` has; `XCoreHom.toWPHom` is the case where the
map acts on each component. `XWP.toCoreWP` turns an `XWP` instance into an
`XCoreWP` observation and `XWPMorphism.toCoreWPHom` a morphism into a core
morphism; both are definitions, used as local instances, because the order on
`XAssertion ps Ω` is a local instance. `xtriple_iff_core` identifies `XTriple`
with `XCoreWP.Triple`.

| Notion | At `XCorePT` | Depends on the shape |
|---|---|---|
| Transformer, triple, rules of the four features | `XCorePT`, `XCorePT.Triple`, `XCorePT.seq_triple`, `XCorePT.frame`, `XCorePT.rel_seq` | `XPredTrans`, `XPT` take a postcondition as a pair `XPostCond α ps Ω` |
| Observation of a monad | `XCoreWP`, `XCoreWP.Triple`, `LawfulXCoreWP` | `XWP`, `XTriple`; converted by `XWP.toCoreWP` |
| Morphism of observations | `XCoreWPHom`, `XCoreWPHom.triple` | `XWPMorphism`, `xwp_morphism`; converted by `XWPMorphism.toCoreWPHom` |
| Assertion types and their order | parameters `Pred`, `EPred` with `≤` | `XAssertion`, `XExceptConds`, `XAssertion.le`, computed by recursion on the shape |
| Separation | `XCoreSep` on the assertion type | `XBI` on the carrier `Ω`, lifted by `XAssertion.sep` |
| Reduction lemmas and tactics | none | the `xspec` set, `xmvcgen`, `xmvcgen_ctl`, `xmvcgen!` |
| Control combinators | none | `xite`, `xphi`, `xfor`, `xpar` |
| Relational layer of `Rel/` | none | `instXWPSDistr`, `couplingPT` and the statements that write a postcondition as a pair |

`xphi`, `xfor` and `tick` are defined at the single shape `.graded ℕ .pure` over
`Prop`.

The Lean 4.33.1 toolchain contains, beside `Std.Do`, a library `Std.Internal.Do`
whose `PredTrans Pred EPred α` is parameterised by an assertion type and an
exception-postcondition type instead of a `PostShape`. `XCorePT` has these two
parameters and the grade.
