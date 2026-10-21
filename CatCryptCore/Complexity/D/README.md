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
polynomially related to Turing-machine time. D counts β-steps in the same way and adds
branches and effect nodes (`sample`, `get`, `set`, `query`, as in `SPTree.queryCost`) at one
step each, and primitive operations at the cost `Prim.cost`.

## Cost of primitive operations

Operations on `Bool` and on fixed-width words cost one step (the word-RAM convention for a
fixed word width). Operations on `ℕ` are charged by the bit length `Nat.size` of their
arguments (logarithmic cost):

| Operation | Cost |
| --- | --- |
| `natAdd`, `natSub`, `natEq`, `natLt` | `max (size x) (size y) + 1` |
| `natMul`, `natDiv`, `natMod` | `size x * size y + 1` (schoolbook) |
| `Bool` and word operations | `1` |

The shifts `wshl` and `wshr` take a natural-number amount and cost one step: an amount of at
least the word width gives the zero word, so only amounts below the word width are
meaningful. The evaluator places `p.cost v` ticks for a primitive operation `p` at the
argument `v`, so `CTree.cost` remains the number of ticks and effect nodes.

Unit cost on unbounded integers is too strong a model. A unit-cost RAM with multiplication
decides in polynomial time every problem in PSPACE:

* J. Hartmanis, J. Simon. *On the power of multiplication in random access machines*. 15th
  Annual Symposium on Switching and Automata Theory (SWAT 1974), IEEE, 13–23.

Under the logarithmic cost criterion, where an operation costs the bit lengths of its
operands, RAM time and Turing-machine time are polynomially related:

* S. A. Cook, R. A. Reckhow. *Time bounded random access machines*. JCSS 7(4), 1973, 354–375.

D charges `ℕ` operations under this criterion. That a primitive step of D is simulated in L by
a number of β-steps polynomial in its cost, which would place D's cost among the reasonable
time measures of Forster, Kunze and Roth, is not proved here.

## Modules

| Module | Content |
| --- | --- |
| `Tree` | `FTy` (finite ground types), `CTree` (effect trees with a `tick` node), `CTree.cost` (worst case over the branches), `CTree.run` (meaning in `SPComp`), `CTree.Rel` (relational lifting) |
| `Syntax` | `Ty`, `Val`, de Bruijn `Var`, `Env`, `Prim`, the intrinsically typed terms `Tm Γ τ`, `Tm.compose`; the module docstring maps each construct of hax-lean's `TExpr` to D |
| `Semantics` | the interpreter `Tm.interp`, the evaluator `Tm.eval` (a tick at every step), the denotation `Tm.den` / `Tm.denote`, the logical relation `ValRel` and the adequacy theorems |
| `Cost` | `Tm.cost` and its compositionality lemmas |
| `Examples` | a list sum by `foldl`, a function applied twice, a sampler |
| `TimeAdm` | time admissibility of `SPComp` arrows by closed D-terms, its graded laws, the time-bounded distance `ucCdistTime` |

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
  (`Tm.cost_letE_le`, `Tm.cost_letE_ret`); variables cost nothing (`Tm.cost_var`); a
  primitive operation costs its argument and `Prim.cost` at the argument's value
  (`Tm.cost_prim`, `Tm.cost_prim_le`).
* The sum of a list `l` by `foldl` costs at most `length l * (size (sum l) + 2)`
  (`Examples.sumBody_cost_le`); on words, a function applied twice to the successor costs
  exactly six steps (`Examples.twice_succW_cost`).
* `foldl` and `iter` cost at most the number of iterations times one plus the cost of one
  application (`foldT_cost_le`, `iterT_cost_le`).
* Precomposition of function terms adds the costs (`Tm.cost_compose_le`,
  `Tm.allRet_compose`, `Tm.cost_app_compose_le`).

## Time admissibility

The module `TimeAdm` charges the time of a distinguisher in the cost model of Forster and
Kunze cited above. A Kleisli arrow `f : Val a → SPComp (Val b)` on first-order types is
admissible at time `n` (`TimeAdm`) when a closed D-term evaluates to a closure whose
application to every input costs at most `n` steps and means `f`. The laws of `UCAdmClass`
hold in graded form: `pure` at time 1, bind at the sum of the times plus 3, the coproduct at
the maximum of the times plus 2, and precomposition only by a function that a closed D-term
computes, at the sum of the two times plus 3; precomposition by an arbitrary Lean function is
not admissible at any constant time. `ucCdistTime` is the computational distance over the
distinguishers admissible at time `t`, a pseudometric with the composition bounds that these
laws give. In the query, size and shape classes a pure test is free, and step time on `SPComp`
equals query cost; the time class charges the range test of a generator at about the number of
seeds times the cost of the generator. The module also defines renaming and weakening of terms
(`Tm.rename`, `Tm.weaken`, `Tm.interp_rename`). Its relation to the other classes is in
`CatCryptCore/Crypto/Complexity.md`, section "Time over the deep language D".

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
