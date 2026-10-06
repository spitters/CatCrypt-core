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
- The parameters `ps` and `Ω` of `XWP` are not output parameters. Write
  `XTriple (m := …) (ps := …) (Ω := …)` and `XPT (ps := …)` in statements.
- `XPostCond` is reducible and has to stay so. A reduction lemma quantifies over
  `Q : XPostCond α ps Ω`, while a postcondition written as a pair `(fun a => …, e)`
  has the product type; `simp` and `rw` compare the two types with reducible
  definitions unfolded only, and with a non-reducible `XPostCond` no `_apply`
  lemma rewrites such a goal (`demo_state_seq_reg` is the regression example).
- For a program of `StateM`, pass `xwp_stateM` and `stateWP_apply` to the tactic;
  they are not in `xspec`. A new `XWP` instance needs the corresponding pair of
  lemmas: `simp only` does not unfold the class projection `XWP.xwp`.
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

The frame rule for a local transformer, and a core rule at a shape:

```lean
  xframe (xpure_local a) (XAssertion.le_refl .pure P)

attribute [local instance] XAssertion.preorder XExceptConds.preorder XAssertion.coreSep
…
  (xlocal_iff_core _).2 <|
    XCorePT.seq_local ((xlocal_iff_core x).1 hx) ((xlocal_iff_core y).1 hy)
```

## Where a new lemma goes

- A rule that holds for every ordered assertion type: `XPredCore.lean`.
- Its instance at a shape, or a fact about `XAssertion`, `XPostCond`, `XWP`,
  `XBI`, `XWPMorphism`: `XPostShape.lean`.
- The reduction lemmas of a new combinator: the module that defines the
  combinator, tagged `@[simp, xspec]`; that module imports `XMvcgen`.
- An `XWP`, `XBI` or `XWPMorphism` instance for a concrete monad or carrier: its
  own module, as `XHeapSoundness` and `XMorphismInstance` are.
- A lemma about Mathlib notions only: `CatCryptCore/ForMathlib/`.
- A short example: `Demo.lean`. Register a new module in `CatCryptCore.lean`.
