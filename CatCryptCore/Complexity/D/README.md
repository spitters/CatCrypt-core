# D: a deep call-by-value language with intrinsic cost

D is a typed call-by-value λ-calculus embedded in Lean, whose terms carry their own cost.
A Lean function carries no cost of its own, so a time measure on `SPComp` arrows collapses to
query cost (`spTreeTimeCost_eq_spTreeQueryCost` in `XDijkstra/XTimedMonad.lean`). In D the
cost of a program is the number of evaluation steps of its term.

The cost model follows the weak call-by-value λ-calculus L of Forster and Kunze:

* Y. Forster, F. Kunze. *A certifying extraction with time bounds from Coq to call-by-value
  λ-calculus*. ITP 2019, LIPIcs 141. doi:10.4230/LIPIcs.ITP.2019.17
* Y. Forster, F. Kunze, M. Roth. *The weak call-by-value λ-calculus is reasonable for both
  time and space*. POPL 2020, PACMPL 4. doi:10.1145/3371095

In L, time is the number of β-steps, and the second paper shows that this measure is
polynomially related to Turing-machine time. D counts β-steps in the same way and adds three
kinds of unit-cost step: primitive operations on `ℕ`, `Bool` and fixed-width words (the
word-RAM convention), branches, and effect nodes (`sample`, `get`, `set`, `query`, as in
`SPTree.queryCost`).

## Modules

| Module | Content |
| --- | --- |
| `Tree` | `FTy` (finite ground types), `CTree` (effect trees with a `tick` node), `CTree.cost` (worst case over the branches), `CTree.run` (meaning in `SPComp`), `CTree.Rel` (relational lifting) |
| `Syntax` | `Ty`, `Val`, de Bruijn `Var`, `Env`, `Prim`, the intrinsically typed terms `Tm Γ τ`, `Tm.compose`; the module docstring maps each construct of hax-lean's `TExpr` to D |
| `Semantics` | the interpreter `Tm.interp`, the evaluator `Tm.eval` (a tick at every step), the denotation `Tm.den` / `Tm.denote`, the logical relation `ValRel` and the adequacy theorems |
| `Cost` | `Tm.cost` and its compositionality lemmas |
| `Examples` | a list sum by `foldl`, a function applied twice, a sampler |

## What is proved

* The evaluator and the denotation give related trees in related environments
  (`Tm.interp_rel`, the fundamental lemma of the logical relation `ValRel`). At first-order
  types the evaluator with its ticks erased is the denotation (`Tm.eval_erase`), and both have
  the same meaning in `SPComp` (`Tm.run_eval`).
* The cost of a bind is at most the cost of the tree plus a bound on the continuation at its
  leaves (`CTree.cost_bind_le`); a sample costs one plus the maximum over its branches
  (`CTree.cost_bind_sample`, `Tm.cost_letE_sample`).
* An application costs the function, the argument, one β-step and the body
  (`Tm.cost_app_le`, `Tm.cost_app_lam`); a `letE` costs its bound term once
  (`Tm.cost_letE_le`, `Tm.cost_letE_ret`); variables cost nothing (`Tm.cost_var`).
* `foldl` and `iter` cost at most the number of iterations times one plus the cost of one
  application (`foldT_cost_le`, `iterT_cost_le`).
* Precomposition of function terms adds the costs (`Tm.cost_compose_le`,
  `Tm.allRet_compose`, `Tm.cost_app_compose_le`).

## Design

Terms are intrinsically typed and scoped (`Tm : List Ty → Ty → Type`). A function value is a
Lean function `Val a → CTree (Val b)` into costed trees, so the evaluator is a definitional
interpreter: it is defined by structural recursion on the term, and a closure is produced
only by evaluating a `lam`.

Recursion is structural: `foldl` over lists, `iter` over `ℕ`, and the constructor match
`lcase`. There is no general fixed point, so every term denotes a total function and neither
the evaluator nor the denotation needs fuel. A Lean definition by structural recursion on a
list or a natural number is reflected through these schemes; a definition by well-founded
recursion needs a bound on its recursion depth, which becomes the count of an `iter`.

Unlike L, which encodes data by Scott encodings and counts their β-steps, D has native
products, sums, lists and primitive operations; a constructor or a projection costs nothing
and a branch costs one step, the convention of `derive_timed`.
