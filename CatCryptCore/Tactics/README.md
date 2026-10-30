# `catcrypt_auto`: goal-shape dispatch for leaf goals

`catcrypt_auto` closes the main goal by reading its shape and running, in order, the
tactics registered for that shape. `catcrypt_auto?` does the same and reports the tactic
that closed the goal as a suggestion to paste in its place. The shapes and tactics live in
a registry that any library extends from its own modules, without changing CatCrypt; the
registrations for VCVio are in
[catcrypt-vcvio](https://github.com/spitters/catcrypt-vcvio/blob/lean-upgrade-4.35/CatCryptVCVio/AutoVCVio.lean).

This guide covers using the tactic and registering shapes for new goal forms. The
registry of every game-proof tactic in this directory, with its internal rules, is
[AGENTS.md](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Tactics/AGENTS.md).

## Contents

1. [What the tactic does](#what-the-tactic-does)
2. [Built-in shapes and arms](#built-in-shapes-and-arms)
3. [Which module to import](#which-module-to-import)
4. [Registering shapes, arms and normalisation steps](#registering-shapes-arms-and-normalisation-steps)
5. [Worked example: the VCVio registrations](#worked-example-the-vcvio-registrations)
6. [Testing registrations](#testing-registrations)
7. [Options](#options)

## What the tactic does

A *shape* is a predicate on the goal type, built from head constants given by name; an
*arm* is a tactic text attached to a shape with an order. The dispatcher
([`AutoDispatchCore.lean`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Tactics/AutoDispatchCore.lean))
runs five stages and stops at the first arm that closes the goal.

1. **Direct stage.** Among the shapes registered as `direct`, the one of highest priority
   that matches the goal as stated runs its arms.
2. **Normalisation.** The registered normalisation steps whose trigger matches the goal
   run in registration order; a step is kept when it changes the goal. While the goal
   then matches no shape and its head is a non-recursive definition of regular
   reducibility from outside Lean, Mathlib, Batteries, Aesop and Qq, that definition is
   unfolded (at most four times), each unfolding followed by the normalisation steps.
3. **Normalised stage.** The shape is read from the goal with its `set`/`let` variables
   replaced by their values and, failing a match, from its `whnfR`; a goal that no shape
   matches has the shape `other`. The arms of the shape `*` run once for each non-proof
   term argument, then the arms of the shape.
4. **Unfolding pass.** When every arm fails, the definitions found at the heads of the
   goal's explicit arguments (to depth 3) and the definitions passed as arguments that
   occur in the goal are unfolded, the normalisation steps run again, and the arms of the
   new shape run.
5. **Premise stage.** On the goal of stage 3, the arms of the shape `premises` run with
   premises ranked for the goal from the theorems of the current file and the fields of
   local hypotheses
   ([`AutoPremises.lean`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Tactics/AutoPremises.lean));
   when they fail, the first premises are applied in several forms (`exact p _ … _`,
   `apply p <;> assumption`, `rw [p]`, `simp only [p]`, then `catcrypt_grind` with the
   premises and with their instances read off the goal).

Shapes and arm texts name constants by `Name` and are parsed where `catcrypt_auto` is
called, so a module registers them without importing the theory they refer to. An arm
whose `needs` constant is absent from the environment, or whose text does not parse
there, is skipped and named as skipped in the error.

An arm closes the goal only when it leaves no goal open, logs no error, assigns a proof
term without `sorry`, and the kernel accepts that term. Each arm runs under its own
heartbeat and wall-clock budget, and the whole run under a total wall-clock budget
([Options](#options)). An arm that fails or exceeds a budget is undone, with its
messages, and the next arm runs.

### Arguments

`catcrypt_auto [t₁, …, tₙ]` passes terms to the arms. Each term is elaborated once and
sent by its kind:

- a local hypothesis goes to `simp_all` and `aesop` (not to `grind`, which already uses
  the local context and rejects it as a parameter);
- a definition goes to `grind`, `catcrypt_grind`, `simp_all`, `gcongr_unfold` and the
  unfolding pass;
- a term with a hole `_` or `?x`, a term whose type is not a proposition, and a term
  that does not elaborate without an expected type go to the `*` arms (`exact t`, then
  `apply t`), which run before the arms of the shape;
- any other proof goes to `grind`, `catcrypt_grind` and `simp_all` as a lemma, to `aesop`
  as an unsafe rule, and, when its statement is not `∀`-quantified, to `hop_chain` as a
  hop fact.

### `catcrypt_auto?`

`catcrypt_auto?` behaves as `catcrypt_auto` and adds a "Try this" suggestion: the
closing arm with its arguments substituted, preceded by the normalisation and `unfold`
steps that changed the goal, as one parenthesised tactic sequence. Pasting the
suggestion replaces the search by the one tactic that succeeded.

```lean
example (a : Bool) :
    RelTriple (pure a : ProbComp Bool) (pure a : ProbComp Bool) (EqRel Bool) := by
  catcrypt_auto?   -- Try this: rvcgen
```

### Failure

When every arm fails, the tactic fails with the goal unchanged. The error names the
shape of the normalised stage and lists each arm with the first line of its error (or the
reason it was skipped), then the failures after the unfolding pass, in the premise stage
and in the direct stage, and states when the total budget was spent:

```text
catcrypt_auto: goal shape distance inequality; every arm failed (budget 20000 heartbeats and 5000 ms each):
  hop_chain: …
  …
```

The shape in the error tells which family of tactics was tried; a goal reported as
`other` matched no registered shape.

## Built-in shapes and arms

The tables list the registrations of this package, with the module that registers each
arm. Arms of a shape run in increasing order. `simp_all` arms run after `clear` of the
equations introduced by `set … with h` and of equations whose right side contains their
left side.

### Direct stage

| Shape (priority) | Goal | Arms, in order | Module |
|---|---|---|---|
| time bound (120) | `TimeBound`, `StepTimeBound`, or `≤` mentioning `SPTree.Timed.stepTime` or `time` | [`time_bound`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Tactics/AutoTime.lean) | `AutoTime` |
| coupling (100) | `XRelTripleQ0 …`, `RelSpecTriple …` | `relmvcgen!?` | `AutoDispatchExt` |
| hybrid advantage (90) | `AdvantageA _ _ _ ≤ _` | `advmvcgen!?`; `advmvcgen_dep` with a leaf closer | `AutoDispatchExt` |
| zero advantage (80) | `AdvantageA _ _ _ = 0`, possibly under `∀ A` | `prob_to_rHoare`; [`advantage_zero_of_rHoare`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Advantage.lean) with `catcrypt_auto` on the `rHoare` premise | `AutoDispatchExt` |
| extended triple (70) | mentions `XTriple`, `XPT` or `XRelTriple` | `xmvcgen!`, then `omega`, `le_rfl`, `assumption`, `simp_all` or `grind` on each residual | `AutoDispatchExt` |

The tactics `relmvcgen!?`, `advmvcgen!?` and `advmvcgen_dep` are the generators of
[`XCombinedAutomation.lean`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/XDijkstra/Rel/XCombinedAutomation.lean).
When the arms of the direct stage fail, the normalised stage runs.

### Normalised stage

Normalisation step
([`AutoBase.lean`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Tactics/AutoBase.lean)):
a goal mentioning `>>=` is rewritten by `simp only [SPComp.monad_bind_eq]`.

| Shape (priority) | Goal | Arms, in order (order numbers) |
|---|---|---|
| `IsPure/NoFail side condition` (100) | `SPComp.IsPure _`, `SPComp.NoFail _` | `aesop` over the rule set `CatCryptRel` (10); `solve_by_elim` over the `IsPure` combinators of `pure`, `sample`, `fail`, `bind` (90); the same over the `NoFail` combinators (91); `grind +suggestions` with `CatCryptGrind` (95) |
| `relational rHoare judgment` (100) | `rHoare _ _ _ _` | `aesop` over `CatCryptRel` (10); `ssprove_crypto` (20); `ssprove_crypto_grind` (30) |
| `distance inequality` (90) | `a ≤ b` over `ℝ≥0∞` or `ℝ` where `a` is a distance registered with `@[hop_metric]` or a sum with one as summand, or a side mentions a registered distance, `prTrue` or `prEvent` | [`hop_chain`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Tactics/AutoArms.lean) (10); `hop_chain!` (11); `sum_atoms_le` (20); [`le_of_eq_nf`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Tactics/BindSwap.lean) (25); `gcongr <;> catcrypt_grind` (30); `catcrypt_grind` (40); `ord_residual` and `grind +suggestions` (45); `bound`, with a quarter of the budget and skipped when a `∀`-quantified inequality is in context (50) |
| `advantage equality` (85) | `_ = _` with a side an application of `AdvantageA` or `Advantage` | [`advantage_eq_nf`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Tactics/BindSwap.lean) (5); `grind +suggestions` (90) |
| `monotonicity inequality` (80) | `f a₁ … aₙ ≤ f b₁ … bₙ` or `<`; `Monotone f`, `Antitone f`, `StrictMono f`, `StrictAnti f` | [`gcongr_unfold`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Tactics/AutoArms.lean) (10); `gcongr` (20); `gcongr <;> catcrypt_grind` (30); `sum_atoms_le` on `≤` (40); `ord_residual` (45); `simp_all` (50); `grind` (60); `grind +suggestions` (65) |
| `heap read after write` (70, 50) | `Heap.get (Heap.set _ _ _) _ = _`; `=`, `≠` or `¬ _ = _` mentioning `Heap.set` | `grind [Heap.get_set_same, Heap.get_set_other]` (10); `hyp_unfold`, then `grind` or `simp_all` (30) |
| `SPComp equality` (60) | `_ = _` over `SPComp _` | [`bind_swap_nf`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Tactics/BindSwap.lean) (5); `catcrypt_grind` (10); `funext_unfold`, then `rfl`, `grind` or `simp_all`, and `grind +suggestions` (15); [`bind_vcgen`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Tactics/BindVcgen.lean) (20); `bij_cov` (21); `spec_inline` (22); `bool_cases`, then `rfl`, `decide` or `simp_all` (25); `hyp_unfold`, then `grind` or `simp_all` (30) |
| `other` | no shape matches | `sum_atoms_le` on `≤` (10); `ord_residual` (15); `simp_all` (20); `bool_cases`, then `rfl`, `decide` or `simp_all` (25); `grind` (30); `hyp_unfold`, then `grind` or `simp_all` (35); `funext_unfold`, then `rfl`, `grind` or `simp_all` (36); [`eqn_unfold`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Tactics/AutoEqnUnfold.lean), then `rfl`, `grind` or `simp_all` (37); `grind +suggestions` (40) |
| `*` | each non-proof term argument `t` | `exact t` (10); `apply t <;> (first \| assumption \| catcrypt_grind)` (20) |
| `premises` | premise stage | `solve_by_elim [p₁, …]` (10), then the premise forms of stage 5 |

What the arm tactics do:

- `hop_chain [facts]` proves `d x y ≤ e` for a registered distance `d`: it collects hop
  facts `d u v ≤ b` from the context and the arguments, finds a path from `x` to `y`
  (both directions when a symmetry lemma is registered), composes the triangle lemma
  along it and closes the residual by `sum_atoms_le`. `hop_chain!` identifies endpoints
  up to definitional equality and unfolds the bound's head definitions when the residual
  stays open.
- `sum_atoms_le` decides inequalities between ℕ-weighted sums of atoms in an ordered
  commutative semiring of nonnegative elements (`ℝ≥0∞`), using hypotheses `a ≤ b`
  between atoms.
- `ord_residual` proves `a ≤ b` over a semiring with a partial order by a depth-bounded
  search over `assumption`, `le_rfl`, `positivity`, factor bounds (`c * a ≤ a` from
  `c ≤ 1`, and the like) and `gcongr`.
- `gcongr_unfold [defs]` introduces the binders of a goal such as `Monotone f`, unfolds
  the given definitions and runs `gcongr`.
- `bool_cases` splits on Boolean variables and on the conditions of `decide` and `if`;
  `hyp_unfold` unfolds predicate definitions in the hypotheses; `funext_unfold` proves an
  equality of functions into a program type registered with `catcrypt_funext_type`;
  `eqn_unfold` rewrites applications of definitions by pattern matching to constructors
  by their equation lemmas.
- `bind_swap_nf` closes an `SPComp` equality whose sides differ in the order of
  independent `IsPure` binds; `advantage_eq_nf` reduces an equality of advantages to game
  equalities closed by `bind_swap_nf`, and `le_of_eq_nf` uses it for `≤`; `bind_vcgen`
  peels matching binds; `bij_cov` changes variables through a bijection at a uniform
  sample; `spec_inline` inlines specifications of abstract operations given as
  hypotheses.
- `catcrypt_grind` is `grind` with the scoped lemma set `CatCryptGrind` active
  ([`AutoBase.lean`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Tactics/AutoBase.lean));
  the `grind +suggestions` arms add the premises of Lean's library-suggestion selector
  ([`AutoSets.lean`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Tactics/AutoSets.lean)).

## Which module to import

None of these modules is imported by the aggregate module `CatCryptCore.Tactics`; a file
that uses them imports them itself. Registrations are active wherever the registering
module is in the import closure.

| Module | Adds | Imports |
|---|---|---|
| [`AutoDispatchCore`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Tactics/AutoDispatchCore.lean) | the tactics `catcrypt_auto`, `catcrypt_auto?`; the commands `catcrypt_auto_shape`, `catcrypt_auto_arm`, `catcrypt_auto_norm`, `catcrypt_funext_type`, `#import_closure_roots`; the options; no shape | `Lean`, `AutoHopRegistry`, `AutoPremises` (all three Lean-only) |
| [`AutoHopRegistry`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Tactics/AutoHopRegistry.lean) | the attribute `@[hop_metric]` | `Lean` |
| [`AutoBase`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Tactics/AutoBase.lean) | the shapes of the normalised stage, the arms that use only Lean tactics, `catcrypt_grind`, the `>>=` normalisation step | `AutoDispatchCore` and a Lean-only module |
| [`AutoArms`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Tactics/AutoArms.lean) | `hop_chain`, `sum_atoms_le`, `ord_residual`, `gcongr_unfold`, `bool_cases`, `hyp_unfold`, `funext_unfold` and their arms | `AutoDispatchCore`, `AutoEqnUnfold`, Mathlib tactic modules |
| [`AutoSets`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Tactics/AutoSets.lean) | the sets `CatCryptRel` and `CatCryptGrind`, the `ssprove_crypto` and `grind +suggestions` arms | Aesop, Mathlib tactic modules, the relational and unary program logic |
| [`AutoMetrics`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Tactics/AutoMetrics.lean) | the three distances of game proofs for `hop_chain`: `sdist`, `Advantage`, `AdvantageA` at a fixed adversary | `AutoArms`, `SDist`, `Advantage`, `Triangle` |
| [`AutoDispatch`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Tactics/AutoDispatch.lean) | every arm of the normalised stage above | `AutoBase`, `AutoSets`, `BindVcgen`, `BindSwap`, `Triangle`, `SDist` |
| [`AutoDispatchExt`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Tactics/AutoDispatchExt.lean) | the direct shapes for the XDijkstra judgments and zero advantage | `AutoDispatch`, the XDijkstra automation |
| [`AutoTime`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Tactics/AutoTime.lean) | the direct shape `time bound` | the costed trees and timed adversaries |

A game proof over CatCrypt's own `SPComp` imports `CatCryptCore.Tactics.AutoDispatchExt`
and has every arm above except `time bound`. A library that registers shapes for its own
goal forms depends only on `CatCryptCore.Tactics.AutoDispatchCore`, whose closure is
Lean and two Lean-only modules; its users import the library's registering module.

With `AutoDispatchCore` alone in scope, `catcrypt_auto` has only the shapes and arms of
the modules that the file imports, and the premise forms of stage 5. The shapes of
`AutoBase` name CatCrypt constants, so on a goal over another library they do not match,
and such a goal reaches the arms of `other`.

## Registering shapes, arms and normalisation steps

### Commands

```lean
catcrypt_auto_shape "name" [direct] priority p := matcher
catcrypt_auto_arm "shape" order k [le_only] [skip_forall_ineq] [budget_div n]
    [needs [c₁, …]] := "tactic text"
catcrypt_auto_norm [needs [c₁, …]] when matcher := "tactic text"
catcrypt_funext_type T
```

- A shape is read in the direct stage when `direct` is given, and in the normalised
  stage otherwise. Among the matching shapes of a stage, the one of highest `priority`
  runs; equal priorities are taken in registration order.
- An arm belongs to the shape of the given name; registering an arm for a shape of
  another module, or for `other`, `*` or `premises`, adds to that shape. Arms run in
  increasing `order`.
  - `needs [c₁, …]`: the arm is skipped when one of the constants is absent.
  - `le_only`: the arm runs only on goals whose `whnfR` is `_ ≤ _`.
  - `skip_forall_ineq`: the arm is skipped when a local hypothesis is a `∀`-quantified
    inequality.
  - `budget_div n`: the arm's heartbeat budget is the per-arm budget divided by `n`.
- A normalisation step runs, before the normalised shape is read, on goals its matcher
  accepts, and is kept when it changes the goal.
- `catcrypt_funext_type T` registers `T` as a program type of `funext_unfold`.

Constant names in matchers and in `needs` are taken as written and not resolved: write
them fully qualified. Arm texts are parsed and elaborated in the scope of the call site,
so constants in them are also best written fully qualified. The registering modules of
this package and of catcrypt-vcvio are `module` files with their registrations in a
`public section`.

### Matchers

| Matcher | Holds on the goal type `t` when |
|---|---|
| `app c` | `t` is an application of `c` |
| `app c/k` | `t` is an application of `c` to exactly `k` arguments |
| `arg c/k at i [whnf] (m)` | `t` is `c` applied to `k` arguments and argument `i` (from 0, implicit and instance arguments included) satisfies `m`, after `whnfR` when `whnf` is given |
| `mentions [c₁, …]` | `t` contains one of the constants |
| `under_forall (m)` | `t` is a `∀` whose body satisfies `m` |
| `any [m₁, …]`, `all [m₁, …]` | one, or all, of the matchers hold |
| `same_head_sides r` | `t` is `r _ _ a b` with `a` and `b` applications of the same function to the same number of arguments |
| `distance [T₁, …] mentioning [c₁, …]` | `t` is `a ≤ b` over a type whose `whnfR` is one of the `Tᵢ`, and `a` is a `@[hop_metric]` distance or a sum with one as summand, or a side mentions one of the `cᵢ` or a registered distance |

For example, `arg Eq/3 at 1 (app f)` matches an equation whose left side is an
application of `f`, since `@Eq α a b` has the type as argument 0.

### Placeholders in arm texts

| Placeholder | Replaced by |
|---|---|
| `%GRIND` | ` [g₁, …]`, the lemma and definition arguments for `grind`, or nothing |
| `%GRIND_TAIL` | `, g₁, …`, the same arguments, to extend a list the arm already has, or nothing |
| `%AESOP_ADD` | ` (add unsafe a₁, …)` or nothing |
| `%HOP` | ` [h₁, …]`, the unquantified proof arguments, or nothing |
| `%DEFS` | ` [d₁, …]`, the definition arguments, or nothing |
| `%SIMP_ALL` | the `simp_all` arm with the arguments for `simp_all`, after the `clear` described above |
| `%TERM` | the term argument (arms of `*` only) |
| `%PREMISES` | ` [p₁, …]`, the premises of the premise stage; an arm with it is left out when there are none |

### A minimal example

```lean
import CatCryptCore.Tactics.AutoDispatchCore

def MyLib.Small (n : Nat) : Prop := n < 100

catcrypt_auto_shape "MyLib small" direct priority 100 := app MyLib.Small
catcrypt_auto_arm "MyLib small" order 10 := "(unfold MyLib.Small; omega)"
catcrypt_auto_arm "MyLib small" order 20 := "(simp only [MyLib.Small]; grind%GRIND)"

example (n : Nat) (h : n < 50) : MyLib.Small n := by catcrypt_auto?
```

A normalisation step, for a library with a definition `MyLib.wrap` and its unfolding
lemma `MyLib.wrap_eq`, run before the normalised shape is read:

```lean
catcrypt_auto_norm needs [MyLib.wrap_eq] when mentions [MyLib.wrap] :=
  "simp only [MyLib.wrap_eq]"
```

### Distances for `hop_chain`

`@[hop_metric]`
([`AutoHopRegistry.lean`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Tactics/AutoHopRegistry.lean))
makes a distance available to `hop_chain`, `sum_atoms_le` and the `distance inequality`
shape. It accepts four kinds of declaration:

- a triangle lemma `d … x z ≤ d … x y + d … y z` (the endpoint positions are read off
  the statement; the other arguments are the context of the distance);
- a symmetry lemma `d … x y = d … y x`;
- a definition whose unfolding is a distance term, or an equation `D … = d …` whose
  right side is one;
- a dominance lemma `d₁ … ≤ d₂ …`, by which a hop fact over `d₂` is read as one over `d₁`.

The registrations of `sdist`, `Advantage` and `AdvantageA` stand beside their triangle
lemmas, in
[`SDist.lean`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/SDist.lean),
[`Advantage.lean`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Crypto/Advantage.lean)
and
[`Triangle.lean`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCore/Tactics/Triangle.lean):

```lean
attribute [hop_metric] CatCrypt.Crypto.sdist_triangle CatCrypt.Crypto.sdist_sym
```

## Worked example: the VCVio registrations

[`CatCryptVCVio/AutoVCVio.lean`](https://github.com/spitters/catcrypt-vcvio/blob/lean-upgrade-4.35/CatCryptVCVio/AutoVCVio.lean)
registers `catcrypt_auto` shapes for goals about VCVio's `OracleComp`. Of CatCrypt it
imports only `CatCryptCore.Tactics.AutoDispatchCore`; the rest of its imports are
VCVio's program-logic tactics and query bounds. All five shapes are direct.

| Shape (priority) | Goal | Arms, in order |
|---|---|---|
| VCVio relational triple (100) | `RelTriple`, `RelWP`, `_ =ᵈ _` | `rvcgen`; `by_equiv <;> rvcgen` |
| VCVio unary triple (100) | `Triple _ _ _` | `vcgen`; `vcgen` then `grind` or `simp` |
| VCVio query bound (95) | `IsQueryBound`, `IsTotalQueryBound`, `IsQueryBoundP`, `IsPerIndexQueryBound`, `PFunctor.FreeM.IsRollBound` | `simp`; unfolding to `IsRollBound` and `simp` with PolyFun's roll-bound lemmas; `grind` with `isTotalQueryBound_query_bind_iff`; `simp` then `decide` |
| VCVio simulateQ equation (90) | an equation with a side `simulateQ _ _` or `(simulateQ _ _).run _` | `simp`; `grind`; `handler_step` then `simp` |
| VCVio probability (80) | `=`, `≠`, `≤` or `<` mentioning `evalDist`, `prEvent` or `prFail` | `simp`; `grind`; `simp only [prEvent_norm]` then `simp`; `simp [Pi.single_apply, eq_comm]`; `vcgen`; `by_equiv <;> rvcgen` |

The registrations show the elements of this guide in use:

```lean
catcrypt_auto_shape "VCVio simulateQ equation" direct priority 90 :=
  any [arg Eq/3 at 1 (app simulateQ), arg Eq/3 at 2 (app simulateQ),
    arg Eq/3 at 1 (arg StateT.run/5 at 3 (app simulateQ)),
    arg Eq/3 at 2 (arg StateT.run/5 at 3 (app simulateQ))]

catcrypt_auto_arm "VCVio simulateQ equation" order 10 := "simp%GRIND"
catcrypt_auto_arm "VCVio simulateQ equation" order 20 := "grind%GRIND"
catcrypt_auto_arm "VCVio simulateQ equation" order 30 := "(handler_step; simp%GRIND)"

catcrypt_auto_arm "VCVio query bound" order 30
    needs [OracleComp.isTotalQueryBound_query_bind_iff] :=
  "grind [OracleComp.IsTotalQueryBound, OracleComp.IsQueryBoundP, \
    OracleComp.isTotalQueryBound_query_bind_iff%GRIND_TAIL]"
```

The `needs` clause skips the arm against a VCVio version without the lemma, and
`%GRIND_TAIL` appends the user's arguments to the arm's own lemma list. When every VCVio
arm fails, the normalised stage runs on the same goal with whatever shapes are in scope.

## Testing registrations

Each registration is tested by a goal of its shape closed by `catcrypt_auto`, and the arm
that closes it is pinned with `#guard_msgs` on the output of `catcrypt_auto?`, as in the
tests of `AutoVCVio.lean`:

```lean
/--
info: Try this:
  [apply] rvcgen
-/
#guard_msgs in
example (a : Bool) :
    RelTriple (pure a : ProbComp Bool) (pure a : ProbComp Bool) (EqRel Bool) := by
  catcrypt_auto?
```

A change in the registry that makes an earlier arm close the goal, or makes the expected
arm fail, changes the message and fails the test. `#guard_msgs (substring := true)`
compares a part of the message, which suits long suggestions and failure messages; the
tests of this package
([`AutoDispatchTest.lean`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCoreTest/Tactics/AutoDispatchTest.lean))
also pin failures, here on a distance that is not registered with `@[hop_metric]`:

```lean
noncomputable def unregDist {X : Type} (δ : X → X → ℝ≥0∞) (x y : X) : ℝ≥0∞ := δ x y

/--
error: catcrypt_auto: goal shape other; every arm failed
-/
#guard_msgs (substring := true) in
example {X : Type} (δ : X → X → ℝ≥0∞) (a b c : X) (e₁ e₂ : ℝ≥0∞)
    (h₁ : unregDist δ a b ≤ e₁) (h₂ : unregDist δ b c ≤ e₂) :
    unregDist δ a c ≤ e₁ + e₂ := by
  catcrypt_auto
```

`#import_closure_roots M` prints the root packages of the import closure of an imported
module `M` and its modules outside `Init`, `Std` and `Lean`; a test with it checks that a
registering module keeps a small closure
([`AutoBaseTest.lean`](https://github.com/spitters/CatCrypt-core/blob/main/CatCryptCoreTest/Tactics/AutoBaseTest.lean)).
`catcrypt_premises?` prints the ranked premises of the premise stage for the main goal.

## Options

| Option | Default | Meaning |
|---|---|---|
| `catcrypt_auto.maxHeartbeats` | 20000 | heartbeats of each arm, in the unit of `maxHeartbeats` |
| `catcrypt_auto.maxMillis` | 5000 | milliseconds of each arm (0: none) |
| `catcrypt_auto.totalMillis` | 30000 | milliseconds of the whole run (0: none) |
| `catcrypt_premises.max` | 16 | premises ranked for the premise stage |
| `catcrypt_premises.fieldDepth` | 2 | depth of structure fields of hypotheses read as premises |
| `catcrypt_premise_forms.premises` | 3 | premises applied in several forms |
| `catcrypt_premise_forms.instances` | 2 | instances per premise read off the goal |
| `catcrypt_premise_forms.maxHeartbeats` | 5000 | heartbeats of each premise form |
| `catcrypt_premise_forms.maxMillis` | 1000 | milliseconds of each premise form |
| `catcrypt_premise_forms.totalHeartbeats` | 20000 | heartbeats after which no further premise form starts |

The steps between arms (matching, normalisation, unfolding, premise ranking) run under
the heartbeat budget of one arm and the time left of the total budget. Before the first
arm of a run whose text contains `+suggestions`, Lean's library-suggestion selector runs
once on the goal outside the arm budgets, so that its index of the imported theorems is
built there; the time it takes extends the total budget.
