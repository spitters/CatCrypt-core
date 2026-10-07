# XDijkstra: notes for proof work

Read [`README.md`](README.md) for the vocabulary and the module map, and
[`Demo.lean`](Demo.lean) for one example per feature. Declarations are in the
namespace `CatCrypt.XDijkstra`.

## Anti-patterns

- Using the kernel for a goal that `mvcgen` closes. A triple about one program
  with no grade, frame, second program or change of shape belongs in `Std.Do`.
- Unfolding by hand (`unfold XTriple XPT`, `show … ≤ …`) where `xmvcgen`,
  `xmvcgen_ctl` or `xmvcgen!` computes the weakest precondition.
- Proving at a shape a rule that does not mention the shape. Prove it for
  `XCorePT` in `XPredCore.lean` and instantiate it through `XPredTrans.toCore`.
- Expecting `do` notation over `XPredTrans` to add grades. `instMonad` uses
  `xbind`, whose grade is that of its first argument; only `xseq` adds.
- Writing a `Monad` instance for a cost-counting monad and expecting a grade.
  A grade that adds under `bind` is an index of the type: follow `CostM σ n` in
  `XCostMonad.lean` or `ErrM ε` in `XErrMonad.lean`, give the family a
  `GradedMonad` instance and write programs as `gdo` blocks.
- Writing chains of `.bind` and `.seq` for a family that has a `GradedMonad`
  instance. Use a `gdo` block; use the operations of the family directly only for
  a single application or inside a lemma about the operation.
- Adding a lemma to the fixed list inside the `xmvcgen` macro. Tag it
  `@[simp, xspec]` in its own module and use `xmvcgen!`.

## Pitfalls

- `xwp_graded_bind` carries `@[defeq]`, which is checked when the theorem is
  declared. The equation must stay definitional: a change to the grade of `xseq`
  or to the `Add` instance on `(XPostShape.graded G ps).Grade` has to keep it so.
- `xseq_grade` is not in `xspec`. It rewrites the same term as `xwp_graded_bind`
  and leaves `((a, u) + (b, v)).1`, which `simp only` does not reduce.
- `XAssertion.preorder`, `XExceptConds.preorder` and `XAssertion.coreSep` are
  definitions, local instances of `XPostShape.lean` only. A file that applies an
  `XCorePT` rule at a shape repeats the `attribute [local instance]` line.
- `register_simp_attr xspec` is in `XMvcgen.lean`, where the attribute can be
  neither applied nor referenced. `XMvcgenControl` tags the control-flow lemmas;
  `XMvcgenReg` adds the core reductions. `simp only [xspec]` in a module that
  does not import `XMvcgenReg` lacks `xpure_apply`, `xbind_apply`, `xseq_apply`,
  `xprod_apply` and `xwp_graded_bind`.
- `xmvcgen_ctl` does not unfold `XRelTriple`.
- The assertion types of `XCoreWP` are not output parameters; only the grade
  type is. Where an argument such as `⟨⟩` does not determine a type, write
  `XCoreWP.Triple (EPred := …)`. A function `θ` with an implicit result type is
  passed to `XWPMorphism.toCoreWPHom` as `@θ`, with `(m := …) (n := …)`.
- The parameters `ps` and `Ω` of `XWP` are not output parameters. Write
  `XTriple (m := …) (ps := …) (Ω := …)` and `XPT (ps := …)` in statements.
- `XPostCond` is reducible and has to stay so. A reduction lemma quantifies over
  `Q : XPostCond α ps Ω`, while a postcondition written as a pair `(fun a => …, e)`
  has the product type; `simp` and `rw` compare the two types with reducible
  definitions unfolded only, and with a non-reducible `XPostCond` no `_apply`
  lemma rewrites such a goal (`demo_state_seq_reg` is the regression example).
- For a program of `StateM`, pass `xwp_stateM` and `stateWP_apply` to the tactic;
  they are not in `xspec`. A new `XWP` instance needs the corresponding pair of
  lemmas: `simp only` does not unfold the class projection `XWP.xwp`. For
  `CostM` the pair is `xwp_costM` and `costWP_apply`; they and the `CostM.run_*`
  lemmas are in `xspec`, because `XCostMonad` imports `XMvcgenReg`.
- The index of a `CostM` program is a sum such as `1 + (0 + 2)`. State the type
  of the program and the `(m := CostM σ …)` argument of `XTriple` with the same
  expression; `xmvcgen!` leaves the sum in the grade goal and `omega` closes it.
- `CostM.sound` takes the grade bound in the form
  `(XWP.xwp (ps := psCost σ) (Ω := Prop) x).grade.1 ≤ b`; `ErrM.sound` and
  `ErrM.prob_post_ge` take it at `psErr`.
- The index of a `gdo` block is the right-nested sum of the indices of its
  steps, with last summand `0` after `return`: three steps of indices `0`, `1`
  and a `return` give `0 + (1 + 0)`. State the type of the block with that
  expression, or apply the weakening of the family to the block and give the
  source index explicitly, as `CostM.relax (m := 0 + (1 + 0)) (by omega) <| gdo …`
  in `readThenTick`.
- A new `GradedMonad` instance needs the equations `gpure_eq`, `gbind_eq` and
  `gseq_eq` that rewrite the class operations to those of the family, tagged
  `@[simp, xspec]`, as for `CostM` and `ErrM`: `simp only` does not unfold the
  class projections, and the reduction lemmas are stated for the operations of
  the family.
- In a quotation pattern of a macro over a syntax category of block elements, an
  antiquotation after a term needs its category (`$r:gdoElem $rs:gdoElem*`).
  Without it the term parser reads the following antiquotations as arguments of
  an application.
- An element parser `term` of a block category is preceded by
  `notFollowedBy("let")`. Otherwise `let x := v` followed by a line is parsed as
  a term-level `let` whose body is that line, and `x` is not in scope in the rest
  of the block.
- `gdo` and `gdo_elems%` are tokens in every module that imports `GradedDo`; an
  identifier `gdo` does not parse there.
- `errWP_apply` has low simp priority in the `xspec` set. It applies to a step
  that is a variable or an opaque constant; for `ErrM.pure`, `ErrM.bind`,
  `ErrM.seq` and `ErrM.relax` the equations `errWP_apply_pure`,
  `errWP_apply_bind`, `errWP_apply_seq` and `errWP_apply_relax` apply first. They
  are equalities of propositions proved by `propext`, not by `rfl`: the support
  of a bind is characterised by `SDistr.bind_apply_some_ne_zero_iff`.
- A hypothesis `h : XTriple (m := ErrM ε) (ps := psErr) (Ω := Prop) P x (Q, PUnit.unit)`
  is applied as a function, `h hP a ha`, or rewritten by `errWP_triple_iff`.
- A transformer over `Prop` with a state layer is in general not `XLocal`
  (`stepT_not_local`); `xframe` then does not apply.
- `xphi`, `xfor`, `tick`, `xfor_triple` are fixed at `.graded ℕ .pure` over `Prop`.

## Proof patterns

A graded specification is a conjunction; each part is one tactic call followed by
arithmetic or an entailment.

```lean
  refine ⟨?_, ?_⟩
  · xmvcgen [stepT]
    omega
  · xmvcgen [stepT]
    rintro s rfl; rfl
```

A triple about a program of a monad with an `XWP` instance:

```lean
  xmvcgen! [xwp_stateM, stateWP_apply]
  rintro s rfl; rfl
```

A graded triple about a `CostM` program `bump`, and its consequence for the run
(`bump_budget`, `bump_run` in `Demo.lean`):

```lean
  refine ⟨?_, ?_⟩
  · xmvcgen!
    omega
  · xmvcgen! [bump]
    rintro s rfl; rfl
…
  CostM.sound bump (bump_budget n b hb).2 (bump_budget n b hb).1 n rfl
```

The same proof applies to a `gdo` block (`bumpDo_budget`). A graded triple about
a `gdo` block of `ErrM` from the triples `hc`, `hd` of its steps
(`addSamples_budget` in `Demo.lean`):

```lean
  refine ⟨?_, ?_⟩
  · xmvcgen!
    rw [add_zero]
  · xmvcgen! [addSamples]
    intro _ x hx y hy
    exact ⟨x, y, hc trivial x hx, hd x (hc trivial x hx) y hy, rfl⟩
```

The frame rule for a local transformer, and a core rule at a shape:

```lean
  xframe (xpure_local a) (XAssertion.le_refl .pure P)

attribute [local instance] XAssertion.preorder XExceptConds.preorder XAssertion.coreSep
…
  (xlocal_iff_core _).2 <|
    XCorePT.seq_local ((xlocal_iff_core x).1 hx) ((xlocal_iff_core y).1 hy)
```

## Where a new lemma goes

- A rule that holds for every ordered assertion type, including a rule about an
  observation `XCoreWP` or a morphism `XCoreWPHom`: `XPredCore.lean`. A new rule
  about programs is stated for `XCoreWP` first and reaches `XWP` through
  `XWP.toCoreWP` and `xtriple_iff_core`.
- Its instance at a shape, or a fact about `XAssertion`, `XPostCond`, `XWP`,
  `XBI`, `XWPMorphism`: `XPostShape.lean`.
- An `XCoreWP` observation at assertion types that no shape computes: the module
  of the monad, as a global instance. `XWP.toCoreWP` stays a definition; a module
  that needs it writes `attribute [local instance] XWP.toCoreWP` after the line
  for `XAssertion.preorder` and `XExceptConds.preorder`.
- The reduction lemmas of a new combinator: the module that defines the
  combinator, tagged `@[simp, xspec]`; that module imports `XMvcgen`.
- An `XWP`, `XBI` or `XWPMorphism` instance for a concrete monad or carrier: its
  own module, as `XHeapSoundness`, `XCostMonad`, `XErrMonad` and
  `XMorphismInstance` are. A `GradedMonad` instance goes in the module of the
  family.
- A coupling rule or a relational tactic: the directory `Rel/`.
- A lemma about Mathlib notions only: `CatCryptCore/ForMathlib/`.
- A short example: `Demo.lean`. Register a new module in `CatCryptCore.lean`.
