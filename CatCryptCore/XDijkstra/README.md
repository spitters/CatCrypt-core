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
| `WP m ps`, `wp⟦x⟧` | `XWP m ps Ω`, `XWP.xwp x` | no bracket notation is declared; `xwp⟦x⟧` appears in docstrings only. `ps` and `Ω` are not output parameters, so statements name them: `(m := …) (ps := …) (Ω := …)` |
| `Triple x P Q`, `⦃P⦄ x ⦃Q⦄` | `XTriple P x Q` for a program, `XPT P t Q` for a transformer | no bracket notation; the precondition comes first |
| `Q ⊢ₚ Q'` | `Q ⊢ₓ Q'` (`XPostCond.le`, scoped notation) | |
| `@[spec]` | `@[xspec]` | `xspec` is a simp attribute for equations `(op …).apply Q = …` and `(op …).grade.1 = …`; it does not hold Hoare triples |
| `mvcgen` | `xmvcgen`, `xmvcgen_ctl`, `xmvcgen!` | each is a `simp only` call; see "Tactics" |

Stay with `mvcgen` when the goal is a triple about one program, has no grade and
no separating conjunct. `mvcgen` looks up triple specifications, splits the goal
into named verification conditions and handles loop invariants; the tactics of
this kernel do none of these. Use the kernel when the statement itself needs a
grade bound next to the triple, a frame, a second program, or a change of effect
shape.

## Modules

| Module | Content |
|---|---|
| `XPredCore` | `XCorePT`, a graded transformer over an arbitrary ordered assertion type; `ret`, `bind`, `seq`, `prod`; the sequencing, frame, relational and transfer rules; `XCoreHom` |
| `XPostShape` | `XPostShape`, `XAssertion`, `XPostCond`, `XPredTrans`, `XWP`, `XPT`, `XTriple`, `XBI`, `XRelTriple`, `XWPMorphism`; the rules of the four features as instances of the core rules; `XPredTrans.equivCore` |
| `XMvcgen` | the simp attribute `xspec` and the tactic `xmvcgen` |
| `XMvcgenControl` | `xite`, `xphi`, `xfor` with their reduction lemmas and triple rules; the tactic `xmvcgen_ctl` |
| `XMvcgenReg` | the core reductions added to `xspec`; the tactic `xmvcgen!` |
| `XMorphismInstance` | `thetaX` and `instXWPMorphismBaseChange`: transfer from a state shape to the same shape with an exception layer |
| `XHeapSoundness` | `instXWPStateM` and `stateWP_triple_iff` for `StateM σ`; the heap carrier `HProp V` with `instXBIHProp` |
| `XRelatorPMF` | `IsCoupling`, `Couples`, `XRelTriplePMF` for Mathlib's `PMF` |
| `XQuantaleGradeCore` | the join of grades over `GradeQuantale`; the combinator `xpar` |
| `GradedWP` | an earlier, self-contained transformer with the grade as a type index (`GPredTrans`, `gbind`), in the namespace `CatCrypt.Crypto.SecureCompilation.Ascent.GradedWP` |
| `XDijkstraAll` | imports `XPostShape`, `XMvcgen`, `XRelatorPMF`, `XHeapSoundness` |
| `Demo` | the tutorial |

`Category/XCategoricalModel.lean` reads the kernel categorically
(`GradedDijkstraObservation`, `self_gradedDijkstraObservation`,
`grade_axis_is_lawvere_quantale`), and `Category/CoParaGradedBridge.lean` relates
the grade addition of `GradedWP.gbind` to the size of a protocol interface
(`ifaceGrade_hcomp`).

## The four features and their theorems

| Feature | At a shape (`XPostShape`) | Over an arbitrary assertion type (`XPredCore`) |
|---|---|---|
| Grade | `xseq_triple`, `xwp_graded_bind`, `xtriple_grade_le` | `XCorePT.seq_triple`, `XCorePT.seq_grade`, `XCorePT.seq_grade_le` |
| Frame | `xframe`, `xpure_local` | `XCorePT.frame`, `XCorePT.ret_local`, `XCorePT.bind_local`, `XCorePT.seq_local` |
| Relational | `xrel_seq`; for `PMF`: `Couples_bind`, `XRelTriplePMF_seq` | `XCorePT.rel_seq` |
| Morphism | `xwp_morphism` | `XCorePT.Triple.transfer`, `XCoreHom.map_triple` |

The grade is a field of the transformer. `xseq x y` has grade
`x.grade + y.grade`. `xbind x f` has the grade of `x`, because the grade of `f a`
depends on the value `a`; the `Monad` instance `instMonad` uses `xbind`, so a
`do` block over `XPredTrans` does not add grades. The monad laws are proved for
the field `apply` (`xbind_pure_apply`, `xpure_bind_apply`, `xbind_assoc_apply`).

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
   `grade` and a proof of `mono`. `instXWPStateM` with `stateWP` is the model.
2. State what a triple means for the monad, as `stateWP_triple_iff` does for
   `StateM`. The class `XWP` has no laws; `GradedDijkstraObservation` in
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

The following are stated with a shape and have no counterpart at `XCorePT`: the
classes `XWP`, `XBI` and `XWPMorphism`, the program-level `XTriple`, the three
tactics and the `xspec` lemmas, and the combinators `xite`, `xphi`, `xfor` and
`xpar`. `xphi`, `xfor` and `tick` are defined at the single shape
`.graded ℕ .pure` over `Prop`.

The Lean 4.33.1 toolchain contains, beside `Std.Do`, a library `Std.Internal.Do`
whose `PredTrans Pred EPred α` is parameterised by an assertion type and an
exception-postcondition type instead of a `PostShape`. `XCorePT` has these two
parameters and the grade.

## Limitations

- The tactics are `simp only` macros. They do not look up triples, split a goal
  into named conditions, case on a `bif` (`demo_branch` uses `cases b`) or find
  loop invariants (`xfor_triple` is applied by hand).
- At a shape with a state layer and a postcondition written as a `fun`, the
  lemmas `xseq_apply` and `stateWP_apply` were observed not to rewrite; the
  definitions (`xseq`, `stateWP`, `XWP.xwp`) are passed to the tactic instead.
  `addTwo_x` and `stepT_seq_budget` in `Demo.lean` show the calls.
- This package has two `XWP` instances: `instXWPSelf` (a transformer observes
  itself) and `instXWPStateM`, whose shape has no grade layer. Every graded
  example is a transformer written by hand (`stepCost1`, `costStep`, `tick`,
  `xboost`, `stepT`); no program monad is observed at a graded shape here.
- Locality is proved for `xpure` only (`xpure_local`). The framed examples
  `demo_frame` and `heap_framed_triple` frame around `xpure`. Over `Prop` with a
  state layer the product is pointwise conjunction, and a step that changes the
  state is not local (`stepT_not_local` in `Demo.lean`).
- The two `XWPMorphism` instances, `instXWPMorphismId` and
  `instXWPMorphismBaseChange`, relate transformers to transformers, and their
  transfer law holds by `rfl`.
- `xprod` runs its two arguments one after the other on the same shape. The
  coupling relation `Couples` on `PMF` is a separate definition: there is no
  `XWP` instance for `PMF`, and `XRelTriplePMF` is not an `XRelTriple`.
- That `XPredTrans ps Ω` is not a lawful monad is argued in the module docstring
  of `XPostShape`; it is not a Lean theorem.
- `GradedWP` is not related to `XPredTrans` by a theorem.
- `XDijkstraAll` does not import `XMvcgenControl`, `XMvcgenReg`,
  `XMorphismInstance`, `XQuantaleGradeCore`, `GradedWP` or `Demo`; the root
  module `CatCryptCore` imports them.
