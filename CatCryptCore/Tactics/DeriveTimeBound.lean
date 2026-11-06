/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.AutoTime
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.TimeFoldRegistry
public import CatCryptCore.Core.SPTreeTimedFree
public import CatCryptCore.Crypto.OracleAdversaryFree

/-!
# The time theorem of a costed computation tree

`derive_time_bound R.tree` states and proves the time theorem `R.tree.timeBound_timed` of the
costed tree `R.tree.timed` that `derive_timed` (or `derive_reduction R`) defined:

* every binder `A : X₁ → … → SPTree.Timed β` (an adversary or a sub-computation in tree
  form) gets a bound `T_A` and the hypothesis `∀ x, (A x).time ≤ T_A`;
* every binder `k : SPTree.Timed β` (a key generation) gets a bound `G_k` and the hypothesis
  `k.time ≤ G_k`;
* every cost companion `fCost : X₁ → … → ℕ` gets its own bound `t_fCost` and the hypothesis
  `∀ x, fCost x ≤ t_fCost`;
* the bound of the theorem is the cost of the tree with every atom replaced by its bound:
  the step costs and node units along the tree, a bind charged with the bound of its first
  tree plus the bound of its continuation, a branch `if` charged with the maximum of its
  branches, a `sample` or `sampleDist` node charged with one plus the bound of its step cost
  and continuation at a fresh sample, normalised to a sum of atoms with natural coefficients.

A bound that mentions a value bound inside the tree (a sampled value, a value read from the
heap, the result of a bind, a matched value) is admitted when the value occurs only inside
registered costs `f.timedCost a` whose closed form does not mention it: each such cost is
replaced by the right side of `f.timedCost_eq` at `a`, or by the bound of `f.timedCost_le` at
`a` (premises closed from the hypotheses of the theorem), whichever exists and is free of the
value (`rewriteCosts`). When neither is, the cost is replaced by its bound free of the value
(`AutoTime.boundFree?`): a premise `∀ x y, fCost x y ≤ ?k` of the `_le` lemma is closed by the
bound of the companion at fresh arguments, each cost companion by its bound variable, each
value `↑i` of `i : Fin n` by `n`, each length of a list built by `List.ofFn`, `map` or `zip` by
its equation, each length of a length invariant by its bound. Since every operation of a bound
is monotone, the replaced bound bounds the original one, and `time_bound` uses the same lemmas
at its arithmetic leaves (`AutoTime.addCostFacts`).

The continuation of a bind `A.bind f` whose bound mentions the bound value `b` only through
lengths `(π b).length` (a fold over a list returned by a callee) is bounded at the values of
the length invariants of `A`: for each local hypothesis or theorem `N.allRet_length` of a callee
`N.timed` concluding `AllRet (fun a => (π a).length ≤ n) A` (`AutoTime.lengthInvs`), each
`(π b).length` in the bound, and in the closed forms of the registered costs, is replaced by
`n` (`withFreshLen`). This is tried only when the bound at every value fails, so a bound found
without it is unchanged. `time_bound` assumes the same invariants at the bind
(`st_bind_inv`). When both fail, they are tried again in the strict mode (`withStrict`), in
which the closed form of every registered cost is free of all the values bound inside the
continuation, so that the bound of a cost at an inner value (a sampled coefficient) does not
keep an outer value (the board returned by a callee) outside a registered cost.

A `match` in a step cost whose alternatives have bounds that mention their pattern variables
is bounded by the same `match` on the same discriminants, each alternative replaced by its
bound (`matchBound`). When no bound of an alternative mentions its pattern variables, the
bound of the `match` is the maximum of the bounds of its alternatives. The bound of a match by
cases is monotone in each alternative, and `time_bound` proves it by splitting the arithmetic
leaf on the discriminants of the match. A step or a tree dispatched by a `match` (the
hoisted match of a reduction on its input, a dispatch on a sum, a match on two discriminants
or on nested patterns) is bounded in the same way, each alternative by the bound of its step
or tree, which includes the cost of the dispatch charged in that alternative (`boundMatch`).
A case analysis `T.casesOn` or `T.rec` of a non-recursive inductive type in a step cost (the
cost of `Sum.map f g` on a bound value) is bounded by the maximum of the bounds of its minor
premises when none mentions a field (`casesBound?`).

A costed tree whose body is a pure step `(e, t)` with `t` a `ret` leaf (a reduction that
computes its result without sampling, state or calls) has its theorem proved by the recursion
that computes the bound (`mirrorTimeBound`). The body is first put in projection-normal form
(`reduceProjCtor`: each projection of a constructor application, of a pair or of a structure,
replaced by the field). The bound `B₀` of the step cost `e` is computed clause by clause as
above, and each clause yields its monotonicity proof:

* a sum, product or maximum: `Nat.add_le_add`, `Nat.mul_le_mul`, `max_le_max`;
* an `if`: `ite_le_max_of`;
* a cost companion `f a`: the hypothesis `h_f a`;
* a `match` whose alternative bounds do not mention their pattern variables: the splitter of
  its matcher with the motive `fun ds => m[ds] ≤ B` and the maximum `B` of the alternative
  bounds, each alternative bound lifted to `B` by `le_max_left` and `le_max_right`;
* a `match` whose alternative bounds mention their pattern variables: the splitter with the
  motive `fun ds => m[ds] ≤ mB[ds]`, `mB` the same match of the alternative bounds;
* at each alternative of a splitter, the equation lemma of the matcher reduces the match at
  the pattern of the alternative (under its overlap hypotheses, for a wildcard alternative)
  to the body of the alternative;
* a registered cost that mentions a pattern variable: its closed form, with the proof from
  `f.timedCost_eq` or `f.timedCost_le`;
* any other term: itself, by `Nat.le_refl`.

The pair is read as `boundStep` reads it, and the step cost is put in projection-normal form
before the recursion. The stated bound is the bound `B` of the other procedure, so the
statement does not depend on the procedure that proves it; `B₀ ≤ B` is closed by `omega`. The
proof is linear in the size of the step cost, where `time_bound` unfolds the step cost against
the bound as a whole.

Every other tree, and a pure step with a clause outside this fragment (the step cost `y.1` of
a subtree) or with `B₀ ≤ B` outside `omega` (a cost that the projection-normal form or the
closed forms of registered costs change), has its theorem proved by `time_bound`, under its
own heartbeat budget
(`proofHeartbeats`). A pair or tree that no clause reads (a call of a recursive definition
`C.timed`, which does not unfold) is bounded by the time theorem of the callee
(`calleeBound?`): a theorem `C.timeBound_timed` found by name as `time_bound` finds it
(`envSources`), its conclusion unified at the call and its premises (`∀ x, p x ≤ tp` on a cost
argument) closed from the bound hypotheses of the caller (`closeByContext`); the bound is the
right side of its conclusion, and `time_bound` uses the same theorem at the call. When the
bound cannot be computed (a cost that depends on a bound value through a term other than a
companion with such a closed form, a callee without such a theorem) or `time_bound` does not
close the goal, nothing is declared and the command fails with the
reason. The command is written once per reduction, in place of a hand-stated theorem of the
same name.

## The fold rule

**Rule.** The time theorem of a costed tree of any kind registered by `register_time_fold`
(`TimeFoldRegistry.lean`) is proved by one structural recursion over the image of the costed
term in a free monad (`foldBound`): the goal is the bound
`wpFold (OpSpec.chargeUnder (fun a => ↑(c a)) allows) x (fun _ => 0) ≤ ↑B` of the charge fold
of a program `x : FreeM P α`, read from the time-bound predicate of the kind through its
registered equivalence (`FoldKind.stepTimeBoundIff`, `FoldKind.timeBoundIff`; a reading
`OpSpec.charge c` is `OpSpec.chargeUnder c (fun _ _ => True)`). The bound `B` is a term of `ℕ`
computed with its proof, clause by clause, each clause one lemma of
`ForMathlib/PFunctorChargeUnder.lean`:

* a leaf `FreeM.pure a`: `0` (`wpFold_chargeUnder_pure_le`);
* an operation node `FreeM.liftBind a r`: the bound of its charge `c a` (reduced by
  `reduceCharge`, so that `tickCost (.inr n)` reads as `n`) plus the bound of `r b` at a fresh
  answer `b` under the hypothesis `allows a b`, the latter free of `b`
  (`wpFold_chargeUnder_liftBind_le`); at a sampling node the hypothesis is `b ∈ μ.support`, and
  an `if` or `if h :` decided by a hypothesis of the context is its branch, so that a costly
  branch outside the support is not charged (the probabilistic case of the rule);
* a tick whose charge has a summand `y.1` and whose continuation is the image of `y.2`: the
  rest of the charge plus the bound of the step-prefixed image of `y` (`splitWith?`, through
  `FoldKind.stepFold`); a step-prefixed image `stepToFreeMT y`: the bound of `y.1` plus the
  bound of the image of `y.2` (`foldStep`, `FoldKind.stepFold`);
* a bind `x.bind f`: the bound of `x` plus the bound of `f a` at a fresh return `a`, free of
  `a`, under the leaf invariant of `x` when its bound carries one
  (`wpFold_chargeUnder_bind_le_add`, the bind clause `wpFold_chargeUnder_bind_le`); the bind of
  the kind under the step-prefixed image is first rewritten by the fold equation of a costed
  bind (`FoldKind.bindFold`: `wpFold_stepToFreeMT_bind` of `SPTreeTimedFree.lean`,
  `OracleAdversaryFree.lean`, `OracleProgTimedFree.lean`, `QTreeKindFree.lean`); a bind whose
  first program is a node is reassociated;
* an `if`, an `if h :` and a `match`: the maximum of the bounds of the branches
  (`wpFold_ite_le_max_enat`, `wpFold_dite_le_max_enat`, `Split.splitMatch`), each free of the
  hypothesis or of the pattern variables of its branch; an `if` of trees is pushed through the
  image (`apply_ite`, `apply_dite`);
* a binder tree: the time-bound hypothesis of the binder, read as a fold bound by the
  registered equivalence (`toFoldFact?`); a hypothesis of the context that bounds a charge fold
  is read as it stands;
* a callee: the conclusion of its time theorem `C.timeBound_timed` (found as `time_bound` finds
  it, `AutoTime.envSources`), read by the registered equivalences, its premises closed by
  `closePremises`, and its leaf invariant `AllRet Q t` read as a demonic fold
  (`FoldKind.allRetFold`);
* a combinator with a registered law (`FoldKind.laws`: `QInstrT.placeLeft`, `QInstrT.placeRight`
  and the oracle absorption `QAdvT.absorb`): the law, its premises proved by the rule;
* the time `t.time` of a costed tree charged by a node of another kind (the computation node of
  an oracle program): the rule on the image of `t` (`FoldKind.timeLe`);
* any other tree: its head definition unfolded (a non-recursive definition, the step of a
  recursive definition at a constructor), then the node equations of the image.

The charges are bounded free of the cost companions and of the values bound in the program by
`bfree?`, the clauses of `AutoTime.boundFree?` with a dependent `if` bounded by the maximum of
its branches (`dite_le_max_of`) and the premise of a registered cost lemma `f.timedCost_le`
closed by the same procedure; the final comparison with a stated bound, and the normalised form
of a derived bound (`normalizeSum`), are closed by `omega` after the facts of
`AutoTime.addCostFacts` and `AutoTime.addLengthFacts` (`arithLe`).

**Fragment.** The rule decides the programs built from these clauses whose charges `bfree?`
bounds free of the bound values: every bound is a sum, product or maximum of numerals, bound
variables of binders and companions, and closed forms of registered costs. It refuses, naming
the program or the charge, a charge that depends on a bound value through a function that no
clause reads, a `match` whose alternative bounds mention their pattern variables, and a tree
that no clause reads after unfolding. The bound it computes is the cost of the program with
every atom replaced by its bound and every branching by a maximum (over the allowed answers at
a node); for `SPTree` with every answer allowed this bounds `stepTime`
(`SPTree.Timed.stepTime_le_of_wpFold_le`).

**Kinds.** A costed tree of a registered kind other than `SPTree` gets the theorem stated by the
left side of `FoldKind.stepTimeBoundIff` (`StepTimeBound (c xs) B` for oracle adversaries,
oracle programs, costed instruments and circuits), every binder tree its time-bound hypothesis
(the left side of `FoldKind.timeBoundIff`), every cost companion its bound (`withBounds`),
proved by the rule alone (`emitFoldTimeBound`). A costed `SPTree` keeps its statement
`stepTime (c xs) ≤ B` with the bound `B` of `boundStep`: the rule runs first
(`foldSPTreeTimeBound`) and `mirrorTimeBound` and `emitTimeBound` (`time_bound`) remain the
fallback. A binder tree of an `SPTree` has the hypothesis `(A x).time ≤ T`, which bounds no
charge fold (the time of a sampling node with an unbounded family of continuation times is
`0`), so a tree with a binder tree goes to the fallback. Setting the environment variable
`CATCRYPT_FOLD_REPORT` to a file appends a line per theorem proved by the fallback, with the
reason of the rule (`reportFallback`). Kind detection is the lookup of the head of the codomain
in the registry (`kindOfType?`, `foldKindOfTimed?`).

**Vector charges.** A kind registered with a vector charge (`FoldKind.useCharge`; the charge
`useCharge cost` of oracle programs at `{query, tick}`, `OracleProgUseBound.lean`) is read by the
same rule, one component at a time. A binder of the kind gets two bound variables, its query
count `q_A` and its time `T_A`, and one hypothesis, its use bound
`∀ ys, UseBound (useCharge 1) _ (img (A ys)) (budget q_A T_A)` (queries counted at unit cost,
`useHypAt`); it is read as one fold fact per component (`toFoldFacts`, through the readings
`wpFold_queryCharge_le_of_useBound`, `wpFold_tickCost_le_of_useBound` among
`FoldKind.hypIffs`). The use bound of the step-prefixed image of the costed term is the join
`FoldKind.useJoin` (`useBound_of_wpFold_le`) of its component folds, each bounded by the fold
rule at its own charge, and the theorem is read back by `FoldKind.useStepIff`
(`useBound_step_iff`): `StepTimeBound x T ∧ QueryCostLe (fun _ => 1) x.2.erase q`
(`emitUseTimeBound`). The clauses at the query component are the clauses above at the charge
`queryCharge`: a computation node and a tick charge no query, a query its cost; the step and bind
equations at that charge are `FoldKind.stepFolds`, `FoldKind.bindFolds`. A bind, a delay, a
computation node and an `if` are thus bounded componentwise, an `if` by the pointwise maximum.
The components meet at the handler combinators, whose component laws (`FoldKind.laws`) bound one
component of the composite from several components of their arguments: the tick fold of
`bindQueries h p` is `T + q * t` from the tick fold `T` and the query fold `q` of `p` and the
tick fold `t` of the handler, its query fold `q * q'`; `collectLog` adds `2 * ℓ + 1` per query
for records of length at most `ℓ` and gives the leaf invariant `al.2.length ≤ q * ℓ` of its
result, read as the leaf invariant of the bind that follows it (a law is tried at the first
program of a bind, `foldBind`). A law applies only at an application of its combinator.

The premise `∀ x, AllRet (fun rl => rl.2.length ≤ ?ℓ) (h x).2` of a law is proved by the
**leaf-length rule** (`closeLeafLen`): the leaf invariant is unfolded at each node of the tree
(an introduced answer), the tree `y.2` of a pair is read through its head, a bind of the kind
through `FoldKind.allRetBind`, an `if` and a `match` are split, and at each leaf the value is
bounded free of the bound variables (a numeral when it reduces to one, else `bfree?`); `?ℓ` is
the maximum of the leaf bounds. A vector theorem is stated with `derive_time_bound +queries`, and
without it whenever the scalar rule fails on a kind with a vector charge (a composite whose time
depends on the query count of a binder).

**Standalone tactic.** `time_fold` runs the rule on a goal
`wpFold (OpSpec.chargeUnder c allows) x (fun _ => 0) ≤ B` or
`wpFold (OpSpec.charge c) x (fun _ => 0) ≤ B` over any program `x` of a free monad, programs
written directly in `FreeM` included, and on the time-bound goals of the registered kinds
(`readGoal`); the hypotheses of the context are its fold facts and its functions bounded by
hypotheses `∀ ys, f ys ≤ t` its cost companions.

## Main definitions

* `rewriteCosts` — the registered costs that mention a bound value, replaced by closed forms
* `withFreshLen` — the bound of a continuation at the values of the length invariants of a tree
* `withStrict` — the strict mode of `rewriteCosts`, free of every value bound by the tree
* `matchBound` — the bound of a `match` by cases
* `calleeBound?` — the bound of a call from the time theorem of the callee
* `emitTimeBound` — the procedure by `time_bound`; it returns the reason when the theorem is
  not proved
* `mirrorCost` — the bound of a step cost with its proof
* `mirrorTimeBound` — the procedure for a pure step, along the bound
* `closePremises` — the premises of the time theorem of a callee, bound families by maxima
* `foldBound` — the fold rule: the bound of a charge fold with its proof
* `closeLeafLen` — the leaf-length rule
* `useHypAt`, `emitUseTimeBound` — the use bound of a binder and the theorem with query count
* `emitFoldTimeBound` — the procedure for a costed tree of a registered kind
* `foldSPTreeTimeBound` — the procedure for a costed `SPTree` by the fold rule
* `time_fold` — the fold rule as a tactic
* `derive_time_bound R.tree` — the command
-/

public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveTimeBound

/-! ## Rule lemmas -/

/-- A `dite` over `ℕ` is at most the maximum of the bounds of its branches. -/
theorem dite_le_max_of {c : Prop} [Decidable c] {t : c → ℕ} {f : ¬c → ℕ} {a b : ℕ}
    (ht : ∀ h, t h ≤ a) (hf : ∀ h, f h ≤ b) : dite c t f ≤ max a b := by
  by_cases h : c
  · rw [dite_eq_left h]
    exact le_max_of_le_left (ht h)
  · rw [dite_eq_right h]
    exact le_max_of_le_right (hf h)

open Lean Meta Elab Term Command CatCrypt.Core CatCrypt.Tactics.TimeFold

meta section

/-- The role of a binder of a costed tree in its time theorem. -/
inductive Role where
  /-- A function into costed trees: its time is bounded pointwise. -/
  | tree
  /-- A costed tree: its time is bounded. -/
  | key
  /-- A cost companion: bounded pointwise. -/
  | cost
  /-- A function into costed trees of a kind registered by `register_time_fold` other than
  `SPTree`, or a value of one: its time bound (the left side of `FoldKind.timeBoundIff`, or of
  `FoldKind.stepTimeBoundIff` for a step-prefixed tree) holds pointwise. -/
  | kind

/-- The left side of the registered equivalence `L` at the tree `x` and the bound `n` (the last
two explicit arguments of `L`), with the proof of the left side from a bound on the charge fold
of its right side, and the right side. -/
def iffAt (L : Name) (x n : Expr) : MetaM (Expr × Expr × (Expr → MetaM Expr)) := do
  let cL ← mkConstWithFreshMVarLevels L
  let (ls, bis, lt) ← forallMetaTelescopeReducing (← inferType cL)
  let ex := (Array.range ls.size).filter fun i => bis[i]! == .default
  unless ex.size ≥ 2 && lt.isAppOfArity ``Iff 2 do
    throwError "`{L}` is not an equivalence of a tree and a bound"
  unless ← isDefEq ls[ex[ex.size - 2]!]! x do
    throwError "`{L}` does not apply to{indentExpr x}"
  unless ← isDefEq ls[ex[ex.size - 1]!]! n do throwError "`{L}`: the bound"
  let pL ← instantiateMVars (mkAppN cL ls)
  let lt ← instantiateMVars lt
  return (lt.getArg! 0, lt.getArg! 1, fun pf => mkAppM ``Iff.mpr #[pL, pf])

/-- The kind registered for the costed tree type `ty` (under its binders, a pair `ℕ × T` read as
the step-prefixed tree `T`), with whether it is step-prefixed. -/
def kindOfType? (ty : Expr) : MetaM (Option (FoldKind × Bool)) := do
  forallTelescopeReducing ty fun _ b => do
    let b ← whnfR b
    let (b, step) := if b.isAppOfArity ``Prod 2 then (b.getArg! 1, true) else (b, false)
    let b ← whnfR b
    let some n := b.getAppFn.constName? | return none
    if n == ``SPTree.Timed then return none
    return (← foldKindOf? n).map (·, step)

/-- The role of a binder of type `t`; with `oadv`, a function into (or a value of) costed trees
of a kind registered by `register_time_fold` other than `SPTree` is bounded as well. -/
def roleOf (t : Expr) (oadv : Bool := false) : MetaM (Option Role) := do
  if oadv then
    if (← kindOfType? t).isSome then return some .kind
  forallTelescopeReducing t fun ys b => do
    let b ← whnfR b
    if b.isAppOf ``SPTree.Timed then
      return some (if ys.isEmpty then .key else .tree)
    if b.isConstOf ``Nat && !ys.isEmpty then return some .cost
    return none

/-- The bounds: each bounded binder with its bound variable and role. -/
abbrev Bounds := Array (FVarId × Expr × Role)

/-- `ℕ`. -/
def natE : Expr := Lean.mkConst ``Nat

/-- `a + b` over `ℕ`. -/
def mkAddN (a b : Expr) : Expr :=
  mkApp6 (Lean.mkConst ``HAdd.hAdd [0, 0, 0]) natE natE natE
    (mkApp2 (Lean.mkConst ``instHAdd [0]) natE (Lean.mkConst ``instAddNat)) a b

/-- `a * b` over `ℕ`. -/
def mkMulN (a b : Expr) : Expr :=
  mkApp6 (Lean.mkConst ``HMul.hMul [0, 0, 0]) natE natE natE
    (mkApp2 (Lean.mkConst ``instHMul [0]) natE (Lean.mkConst ``instMulNat)) a b

/-- `max a b` over `ℕ`. -/
def mkMaxN (a b : Expr) : MetaM Expr := mkAppM ``Max.max #[a, b]

/-- The closed form of the registered cost `s = f.timedCost a` that does not mention `b`: the
right side of `f.timedCost_eq` at `a`, or the bound of `f.timedCost_le` at `a`, with the
propositional premises closed from the context by `closeByContext`, and `subst` applied to the
result before it is checked to be free of `b`. -/
def costClosedForm? (b : FVarId) (s : Expr) (subst : Expr → MetaM Expr := pure) :
    MetaM (Option Expr) := do
  let some n := s.getAppFn.constName? | return none
  for c in ← CatCrypt.Tactics.AutoTime.costLemmas n do
    let st ← saveState
    let (ms, _, body) ← forallMetaTelescopeReducing (← inferType c)
    let side? := if body.isAppOfArity ``Eq 3 then some (body.getArg! 1, body.getArg! 2)
      else CatCrypt.Tactics.AutoTime.natLe? body
    let some (l, r) := side? | st.restore; continue
    if ← isDefEq l s then
      let ok ← ms.allM fun m => do
        let mid := m.mvarId!
        if ← mid.isAssigned then return true
        unless ← isProp (← mid.getType) do return true
        CatCrypt.Tactics.AutoTime.closeByContext mid
      let r ← subst (← instantiateMVars r)
      if ok && !r.hasExprMVar && !r.containsFVar b then return some r
    st.restore
  return none

/-- The user name of the local that marks the strict mode of `rewriteCosts`. -/
def strictName : Name := `_derive_time_bound_strict

/-- `k` in the strict mode of `rewriteCosts`: the variables bound inside `k` (the values bound
by the tree) are eliminated from the closed form of every registered cost. -/
def withStrict {γ : Type} (k : MetaM γ) : MetaM γ :=
  withLocalDecl strictName .default (mkConst ``Unit) (fun _ => k) (kind := .implDetail)

/-- In the strict mode, `b` and the variables of `s` bound after the marker of `withStrict`. -/
def strictAvoid? (b : FVarId) (s : Expr) : MetaM (Option (Array FVarId)) := do
  let lctx ← getLCtx
  let some sd := lctx.findFromUserName? strictName | return none
  let fs := (collectFVars {} s).fvarIds.filter fun f =>
    match lctx.find? f with
    | some d => d.index > sd.index
    | none => false
  return some (if fs.contains b then fs else fs.push b)

/-- `e` with every registered cost `f.timedCost a` that mentions `b` replaced by its closed
form free of `b` after `subst` (`costClosedForm?`), where one exists, and otherwise by its bound
free of `b` (`AutoTime.boundFree?`: a premise `∀ x y, fCost x y ≤ ?k` closed by the bound of the
companion at fresh arguments, a value of `Fin n` by `n`, the length of a list built by
`List.ofFn`, `map` or `zip` by its equation, a length by a local invariant). In the strict mode
(`withStrict`) the bound is free of every value bound by the tree, so that a cost of an inner
value does not keep an outer one. -/
def rewriteCosts (b : FVarId) (e : Expr) (subst : Expr → MetaM Expr := pure) : MetaM Expr :=
  Meta.transform e (pre := fun s => do
    unless s.containsFVar b do return .done s
    let some n := s.getAppFn.constName? | return .continue
    unless n.lastComponentAsString == "timedCost" do return .continue
    if let some avoid ← strictAvoid? b s then
      let some (r, _) ← CatCrypt.Tactics.AutoTime.boundFree? avoid s 64 | return .continue
      let r ← subst r
      if avoid.any r.containsFVar then return .continue
      return .done r
    match ← costClosedForm? b s subst with
    | some r => return .done r
    | none =>
      let some (r, _) ← CatCrypt.Tactics.AutoTime.boundFree? #[b] s 64 | return .continue
      let r ← subst r
      if r.containsFVar b then return .continue
      return .done r)

/-- `e` with every length `l.length` that mentions `b` and is not inside a registered cost
replaced by its bound free of `b` (`AutoTime.boundFree?`: the equation of a list function or a
theorem tagged `@[length_bound]`), where one exists. A length that a closed form of a registered
cost leaves in a bound (the number of iterations of a fold over a list built from a matched
value) is bounded in this way. -/
def rewriteLengths (b : FVarId) (e : Expr) : MetaM Expr :=
  Meta.transform e (pre := fun s => do
    unless s.containsFVar b do return .done s
    if let some n := s.getAppFn.constName? then
      if n.lastComponentAsString == "timedCost" then return .done s
    unless s.isAppOfArity ``List.length 2 do return .continue
    let some (r, _) ← CatCrypt.Tactics.AutoTime.boundFree? #[b] s 64 | return .done s
    if r.containsFVar b then return .done s
    return .done r)

/-- The fresh variable `b : γ` in `k`, which must not occur in the result after the registered
costs that mention it are replaced by their closed forms (`rewriteCosts`). -/
def withFresh (γ : Expr) (k : Expr → MetaM Expr) : MetaM Expr :=
  withLocalDeclD `b γ fun b => do
    let r ← k b
    let r ← instantiateMVars r
    let r ← if r.containsFVar b.fvarId! then rewriteCosts b.fvarId! r else pure r
    if r.containsFVar b.fvarId! then
      throwError "the bound depends on a bound value{indentExpr r}"
    return r

/-- `k` under the local hypotheses `(π b).length ≤ n` of the length invariants `invs`. -/
def withLenHyps {γ : Type} (b : Expr) (invs : List (Expr × Expr × Expr)) (k : MetaM γ) :
    MetaM γ :=
  match invs with
  | [] => k
  | (_, len, n) :: rest => do
    let l ← instantiateMVars (len.beta #[b]).headBeta
    withLocalDeclD `hlen (CatCrypt.Tactics.AutoTime.mkNatLe l n) fun _ => withLenHyps b rest k

/-- The bound `k b` of the continuation of a bind `A.bind f` at a fresh `b : γ`, the registered
costs that mention `b` replaced by their closed forms (`rewriteCosts`) and each length
`(π b).length` of a length invariant `AllRet (fun a => (π a).length ≤ n) A` of the tree `A`
(`AutoTime.lengthInvs`) replaced by its bound `n`, the invariants also local hypotheses for
`AutoTime.boundFree?`; `none` when `A` has no length invariant or the result mentions `b`. -/
def withFreshLen (A γ : Expr) (k : Expr → MetaM Expr) : MetaM (Option Expr) := do
  let invs ← CatCrypt.Tactics.AutoTime.lengthInvs A
  if invs.isEmpty then return none
  withLocalDeclD `b γ fun b => withLenHyps b invs.toList do
    let subst (r : Expr) : MetaM Expr := do
      let mut r := r
      for (_, len, n) in invs do
        let l ← instantiateMVars (len.beta #[b]).headBeta
        r := (← kabstract r l).instantiate1 n
      return r
    let r ← instantiateMVars (← k b)
    let r ← subst (← rewriteCosts b.fvarId! r (subst := subst))
    if r.containsFVar b.fvarId! then return none
    return some r

/-- The head-reduced form of a tree or pair: `whnfR`, then the unfolding of a non-recursive
head definition, at most eight times. -/
def reduceHead (e : Expr) : MetaM Expr := do
  let mut e ← CatCrypt.Tactics.AutoTime.whnfC e
  for _ in [0:8] do
    match ← CatCrypt.Tactics.AutoTime.unfoldTree? e with
    | some e' => e := e'
    | none => break
  return e

/-- The `match` `m` with result type `ℕ` and the alternatives `alts` (each a function of the
pattern variables of its alternative), on the discriminants of `m`. `none` when `m` has
arguments after its alternatives or its motive has no universe parameter. -/
def matchBound (m : MatcherApp) (alts : Array Expr) : MetaM (Option Expr) := do
  unless m.remaining.isEmpty do return none
  let some pos := m.uElimPos? | return none
  let motive ← forallBoundedTelescope (← inferType m.motive) m.discrs.size fun xs _ =>
    mkLambdaFVars xs natE
  let r := { m with matcherLevels := m.matcherLevels.set! pos Level.one, motive, alts }.toExpr
  try
    check r
    return some r
  catch _ => return none

/-- The bound of the `match` `m` whose alternatives are bounded by `k` (a step cost, a pair or
a tree): the maximum of the bounds of its alternatives, or, when a bound mentions a pattern
variable after the registered costs are replaced by closed forms (`rewriteCosts`) and the
lengths by their bounds (`rewriteLengths`), the `match` of the bounds of
its alternatives (`matchBound`). The bounds of the alternatives include the cost of the
dispatch that the costed form charges in each alternative. -/
def boundMatch (m : MatcherApp) (k : Expr → MetaM Expr) : MetaM Expr := do
  let mut acc : Option Expr := none
  let mut lams : Array Expr := #[]
  let mut dep := false
  for alt in m.alts, n in m.altNumParams do
    let (b, lam, d) ← lambdaBoundedTelescope alt n fun ys body => do
      let r ← instantiateMVars (← k body)
      let r ← ys.foldlM (init := r) fun r y => rewriteCosts y.fvarId! r
      let r ← ys.foldlM (init := r) fun r y => rewriteLengths y.fvarId! r
      let d := ys.any fun y => r.containsFVar y.fvarId!
      return (r, ← mkLambdaFVars ys r, d)
    lams := lams.push lam
    dep := dep || d
    unless d do
      acc ← match acc with
        | none => pure (some b)
        | some a => if a == b then pure (some a) else some <$> mkMaxN a b
  if dep then
    match ← matchBound m lams with
    | some r => return r
    | none => throwError "the bound depends on a matched value{indentExpr m.toExpr}"
  match acc with
  | some r => return r
  | none => throwError "a match without alternatives{indentExpr m.toExpr}"

/-- The bound of a case analysis `T.casesOn ps m x a₁ … aₖ` or `T.rec ps m a₁ … aₖ x` of a
non-recursive inductive type `T` with one motive and no argument after its major premise, whose
minor premises `aᵢ` (functions of the fields of constructor `i`) are bounded by `k`: the maximum
of the bounds of the minor premises (a cost of `Sum.map f g` on a bound value). `none` when `e`
is not such a case analysis or a bound of a minor premise mentions a field. -/
def casesBound? (e : Expr) (k : Expr → MetaM Expr) : MetaM (Option Expr) := do
  let some c := e.getAppFn.constName? | return none
  let env ← getEnv
  let args := e.getAppArgs
  let some (iv, start) ← (do
      if isCasesOnRecursor env c then
        let some (.inductInfo iv) := env.find? c.getPrefix | return none
        return some (iv, iv.numParams + 1 + iv.numIndices + 1)
      let some (.recInfo rv) := env.find? c | return none
      unless rv.numMotives == 1 do return none
      let some (.inductInfo iv) := env.find? rv.getMajorInduct | return none
      return some (iv, rv.numParams + 1) : MetaM (Option (InductiveVal × Nat)))
    | return none
  if iv.isRec then return none
  let nCtors := iv.ctors.length
  unless args.size == iv.numParams + 1 + iv.numIndices + 1 + nCtors do return none
  let mut acc : Option Expr := none
  for ctor in iv.ctors, i in [0:nCtors] do
    let some (.ctorInfo cv) := env.find? ctor | return none
    let some minor := args[start + i]? | return none
    let b? ← lambdaBoundedTelescope minor cv.numFields fun ys body => do
      if ys.size != cv.numFields then return none
      let r ← instantiateMVars (← k body)
      let r ← ys.foldlM (init := r) fun r y => rewriteCosts y.fvarId! r
      let r ← ys.foldlM (init := r) fun r y => rewriteLengths y.fvarId! r
      if ys.any fun y => r.containsFVar y.fvarId! then return none
      return some r
    let some b := b? | return none
    acc ← match acc with
      | none => pure (some b)
      | some a => if a == b then pure (some a) else some <$> mkMaxN a b
  return acc

/-- The bound of the time theorem of a callee at `x`: a theorem of `envSources` (the theorem
`C.timeBound_timed` of a costed tree `C.timed`) whose conclusion `stepTime x ≤ B` (or
`x.time ≤ B` when `step` is false) unifies at `x`, with its propositional premises closed from
the context by `closeByContext` (the bound hypotheses of the caller); its right side `B`. -/
def calleeBound? (x : Expr) (step : Bool) : MetaM (Option Expr) := do
  let lhs ← if step then mkAppM ``SPTree.Timed.stepTime #[x]
    else mkAppM ``SPTree.Timed.time #[x]
  for c in ← CatCrypt.Tactics.AutoTime.envSources x do
    let st ← saveState
    let (ms, _, body) ← forallMetaTelescopeReducing (← inferType c)
    let some (l, r) := CatCrypt.Tactics.AutoTime.natLe? body | st.restore; continue
    if ← isDefEq l lhs then
      let ok ← ms.allM fun m => do
        let mid := m.mvarId!
        if ← mid.isAssigned then return true
        unless ← isProp (← mid.getType) do return true
        CatCrypt.Tactics.AutoTime.closeByContext mid
      let r ← instantiateMVars r
      if ok && !r.hasExprMVar then return some r
    st.restore
  return none

mutual

/-- The bound of a step cost `e : ℕ`. -/
partial def boundCost (bs : Bounds) (e : Expr) : MetaM Expr := do
  let e := e.headBeta
  match e with
  | .letE _ _ v b _ => boundCost bs (b.instantiate1 v)
  | .mdata _ b => boundCost bs b
  | _ =>
  if e.isAppOfArity ``HAdd.hAdd 6 then
    return mkAddN (← boundCost bs (e.getArg! 4)) (← boundCost bs (e.getArg! 5))
  if e.isAppOfArity ``HMul.hMul 6 then
    return mkMulN (← boundCost bs (e.getArg! 4)) (← boundCost bs (e.getArg! 5))
  if e.isAppOfArity ``Max.max 4 then
    return ← mkMaxN (← boundCost bs (e.getArg! 2)) (← boundCost bs (e.getArg! 3))
  if e.isAppOfArity ``ite 5 then
    return ← mkMaxN (← boundCost bs (e.getArg! 3)) (← boundCost bs (e.getArg! 4))
  if let some y := CatCrypt.Tactics.AutoTime.fstOf? e then
    -- the step cost of a pair is at most its time
    return ← boundStep bs y
  if let .fvar f := e.getAppFn then
    if let some (_, v, .cost) := bs.find? (·.1 == f) then return v
  -- a `match` in a cost: the maximum of the bounds of its alternatives, or, when a bound
  -- mentions a pattern variable, the `match` of the bounds of its alternatives
  if let some m ← matchMatcherApp? e then
    if !m.alts.isEmpty then return ← boundMatch m (boundCost bs)
  if let some r ← casesBound? e (boundCost bs) then return r
  if let some _ := e.nat? then return e
  if e.isRawNatLit then return e
  return e

/-- The bound of `stepTime x` for a pair `x : ℕ × SPTree.Timed α`. -/
partial def boundStep (bs : Bounds) (x : Expr) : MetaM Expr := do
  let x ← reduceHead x
  if x.isAppOfArity ``Prod.mk 4 then
    let e := x.getArg! 2
    let t := x.getArg! 3
    -- `(c + y.1, y.2)`: the pair `y` after `c`
    if let some y := CatCrypt.Tactics.AutoTime.sndOf? t then
      let fsts := (CatCrypt.Tactics.AutoTime.appsOf e #[]).filter fun o =>
        match CatCrypt.Tactics.AutoTime.fstOf? o with
        | some y' => y' == y
        | none => false
      if let some o := fsts[0]? then
        let c := e.replace fun s => if s == o then some (mkNatLit 0) else none
        return mkAddN (← boundCost bs c) (← boundStep bs y)
    return mkAddN (← boundCost bs e) (← boundTree bs t)
  if x.isAppOfArity ``SPTree.Timed.delay 3 then
    let e := x.getArg! 1
    let z := x.getArg! 2
    -- `delay (c + y.1) (y.2.bind f)`: the pair `y` (a call of a costed callee) followed by `f`,
    -- bounded by one bound of `y`, so that its step cost and its tree are not bounded apart
    if z.isAppOfArity ``SPTree.Timed.bind 4 then
      if let some y := CatCrypt.Tactics.AutoTime.sndOf? (z.getArg! 2) then
        let fsts := (CatCrypt.Tactics.AutoTime.appsOf e #[]).filter fun o =>
          match CatCrypt.Tactics.AutoTime.fstOf? o with
          | some y' => y' == y
          | none => false
        if let some o := fsts[0]? then
          let c := e.replace fun s => if s == o then some (mkNatLit 0) else none
          let f := z.getArg! 3
          let α := z.getArg! 0
          let k ← withFresh α fun v => boundStep bs (f.beta #[v])
          return mkAddN (← boundCost bs c) (mkAddN (← boundStep bs y) k)
    return mkAddN (← boundCost bs e) (← boundStep bs z)
  if x.isAppOfArity ``SPTree.Timed.map 5 then
    let a := x.getArg! 4
    let fc := x.getArg! 3
    let α := x.getArg! 0
    return mkAddN (← boundTree bs a) (← withFresh α fun v => boundCost bs (fc.beta #[v]))
  if x.isAppOfArity ``SPTree.Timed.bind 4 then
    let a := x.getArg! 2
    let f := x.getArg! 3
    let α := x.getArg! 0
    let ta ← boundTree bs a
    -- the continuation at every value, else at the values of the length invariants of `a`,
    -- else both again in the strict mode of `rewriteCosts`
    let k ← try withFresh α fun v => boundStep bs (f.beta #[v])
      catch e => do
        let r? ← try withFreshLen a α fun v => boundStep bs (f.beta #[v])
          catch _ => pure none
        match r? with
        | some r => pure r
        | none =>
          let r? ← try withStrict (withFreshLen a α fun v => boundStep bs (f.beta #[v]))
            catch _ => pure none
          match r? with
          | some r => pure r
          | none =>
            try withStrict (withFresh α fun v => boundStep bs (f.beta #[v]))
            catch _ => throw e
    return mkAddN ta k
  if x.isAppOfArity ``ite 5 then
    return ← mkMaxN (← boundStep bs (x.getArg! 3)) (← boundStep bs (x.getArg! 4))
  if x.isAppOfArity ``dite 5 then
    let c := x.getArg! 1
    let l ← withFresh c fun h => boundStep bs ((x.getArg! 3).beta #[h])
    let r ← withFresh (mkNot c) fun h => boundStep bs ((x.getArg! 4).beta #[h])
    return ← mkMaxN l r
  -- a step dispatched by a `match`: the bounds of its alternatives (`boundMatch`)
  if let some m ← matchMatcherApp? x then
    if !m.alts.isEmpty then return ← boundMatch m (boundStep bs)
  -- a callee that does not unfold (a recursive definition): the bound of its time theorem
  if let some b ← calleeBound? x true then return b
  throwError "no bound for the pair{indentExpr x}"

/-- The bound of `t.time` for a tree `t : SPTree.Timed α`. -/
partial def boundTree (bs : Bounds) (t : Expr) : MetaM Expr := do
  if let .fvar f := t.getAppFn then
    if let some (_, v, r) := bs.find? (·.1 == f) then
      match r with
      | .tree | .key => return v
      | .cost | .kind => pure ()
  let t ← reduceHead t
  if let .fvar f := t.getAppFn then
    if let some (_, v, r) := bs.find? (·.1 == f) then
      match r with
      | .tree | .key => return v
      | .cost | .kind => pure ()
  if t.isAppOf ``SPTree.Timed.ret then return mkNatLit 0
  if t.isAppOf ``SPTree.Timed.fail then return mkNatLit 0
  if t.isAppOfArity ``SPTree.Timed.sample 6 then
    let γ := t.getArg! 1
    let c := t.getArg! 4
    let k := t.getArg! 5
    let b ← withFresh γ fun v => do
      return mkAddN (← boundCost bs (c.beta #[v])) (← boundTree bs (k.beta #[v]))
    return mkAddN (mkNatLit 1) b
  if t.isAppOfArity ``SPTree.Timed.sampleDist 5 then
    let γ := t.getArg! 1
    let c := t.getArg! 3
    let k := t.getArg! 4
    let b ← withFresh γ fun v => do
      return mkAddN (← boundCost bs (c.beta #[v])) (← boundTree bs (k.beta #[v]))
    return mkAddN (mkNatLit 1) b
  if t.isAppOfArity ``SPTree.Timed.get 4 then
    let l := t.getArg! 1
    let c := t.getArg! 2
    let k := t.getArg! 3
    let b ← withFresh (mkApp (Lean.mkConst ``Location.ty) l) fun v => do
      return mkAddN (← boundCost bs (c.beta #[v])) (← boundTree bs (k.beta #[v]))
    return mkAddN (mkNatLit 1) b
  if t.isAppOfArity ``SPTree.Timed.set 5 then
    return mkAddN (mkNatLit 1)
      (mkAddN (← boundCost bs (t.getArg! 3)) (← boundTree bs (t.getArg! 4)))
  if let some y := CatCrypt.Tactics.AutoTime.sndOf? t then
    return ← boundStep bs y
  if t.isAppOfArity ``ite 5 then
    return ← mkMaxN (← boundTree bs (t.getArg! 3)) (← boundTree bs (t.getArg! 4))
  -- a tree dispatched by a `match`: the bounds of its alternatives (`boundMatch`)
  if let some m ← matchMatcherApp? t then
    if !m.alts.isEmpty then return ← boundMatch m (boundTree bs)
  -- a callee tree that does not unfold: the bound of its time theorem
  if let some b ← calleeBound? t false then return b
  throwError "no bound for the tree{indentExpr t}"

end

/-- The summands of a sum over `ℕ`, a numeral contributing its value. -/
partial def summands (e : Expr) : Array Expr × Nat :=
  if e.isAppOfArity ``HAdd.hAdd 6 then
    let (a, m) := summands (e.getArg! 4)
    let (b, n) := summands (e.getArg! 5)
    (a ++ b, m + n)
  else match e.nat? with
    | some n => (#[], n)
    | none => match e.rawNatLit? with
      | some n => (#[], n)
      | none => (#[e], 0)

/-- The sum `e` normalised: equal summands collected with a coefficient, numerals summed last,
operands of `max` and products normalised. -/
partial def normalizeSum (e : Expr) : MetaM Expr := do
  let (ts, k) := summands e
  let ts ← ts.mapM fun t => do
    if t.isAppOfArity ``Max.max 4 then
      mkMaxN (← normalizeSum (t.getArg! 2)) (← normalizeSum (t.getArg! 3))
    else if t.isAppOfArity ``HMul.hMul 6 then
      return mkMulN (← normalizeSum (t.getArg! 4)) (← normalizeSum (t.getArg! 5))
    else return t
  let groups : Array (Expr × Nat) := ts.foldl (init := #[]) fun acc t =>
    match acc.findIdx? (·.1 == t) with
    | some i => acc.modify i fun (u, n) => (u, n + 1)
    | none => acc.push (t, 1)
  let terms := groups.map fun (t, n) => if n == 1 then t else mkMulN (mkNatLit n) t
  let body := terms.foldl (init := none) fun acc t =>
    match acc with
    | none => some t
    | some s => some (mkAddN s t)
  return match body with
    | none => mkNatLit k
    | some s => if k == 0 then s else mkAddN s (mkNatLit k)

/-- The instance of the join `J` of a vector charge (`FoldKind.useJoin`) at the program `x`: its
metavariables, with every function into `ℕ` among them (the cost of a query) assigned the
constant `1`, so that the use bound counts queries, and its conclusion. -/
def useJoinAt (J : Name) (x : Expr) : MetaM (Array Expr × Expr × Expr) := do
  let cJ ← mkConstWithFreshMVarLevels J
  let (ms, _, concl) ← forallMetaTelescope (← inferType cJ)
  unless concl.getAppNumArgs ≥ 2 do throwError "`{J}` does not conclude a use bound"
  unless ← isDefEq concl.appFn!.appArg! x do throwError "`{J}` does not apply to{indentExpr x}"
  for m in ms do
    let mid := m.mvarId!
    if ← mid.isAssigned then continue
    let ty ← whnfR (← instantiateMVars (← mid.getType))
    if let .forallE n d b _ := ty then
      if !b.hasLooseBVars && (← whnfR b).isConstOf ``Nat then
        mid.assign (.lam n d (mkNatLit 1) .default)
  return (ms, cJ, concl)

/-- The use bound `UseBound (C 1) allows x (budget q T)` of the program `x` at the vector charge
of `k`, counting queries (`useJoinAt`), with `q` and `T` the two bound arguments of the
conclusion of the join. -/
def useHypAt (k : FoldKind) (x q T : Expr) : MetaM Expr := do
  let some J := k.useJoin | throwError "the kind `{k.timed}` has no vector charge"
  let (ms, _, concl) ← useJoinAt J x
  let bnds ← ms.filterM fun m => do
    if ← m.mvarId!.isAssigned then return false
    return (← whnfR (← instantiateMVars (← inferType m))).isConstOf ``Nat
  unless bnds.size == 2 do throwError "`{J}`: the two bounds of the use bound"
  unless (← isDefEq bnds[0]! q) && (← isDefEq bnds[1]! T) do throwError "`{J}`: the bounds"
  let r ← instantiateMVars concl
  if r.hasExprMVar then throwError "`{J}` is not determined by its program"
  return r

/-- The bound variables and hypotheses of the bounded binders `xs`, in order, passed to `k`
with the bounds. With `vec`, a binder of a kind with a vector charge (`FoldKind.useJoin`) has
two bound variables, its query count `q_A` and its time `T_A`, and the hypothesis
`∀ ys, UseBound (C 1) allows (img (A ys)) (budget q_A T_A)` on the image of its tree
(`useHypAt`). -/
partial def withBounds {γ : Type} (xs : Array Expr) (i : Nat) (bs : Bounds)
    (vars hyps : Array Expr) (k : Bounds → Array Expr → Array Expr → TermElabM γ)
    (oadv : Bool := false) (vec : Bool := false) : TermElabM γ := do
  if h : i < xs.size then
    let x := xs[i]
    let t ← inferType x
    match ← roleOf t oadv with
    | none => withBounds xs (i + 1) bs vars hyps k oadv vec
    | some r =>
      let n := (← x.fvarId!.getUserName).eraseMacroScopes
      if let .kind := r then
        if vec then
          if let some (kd, step) ← kindOfType? t then
            if kd.useJoin.isSome then
              return ← withLocalDecl (Name.mkSimple ("q_" ++ n.toString)) .implicit natE
                fun q => withLocalDecl (Name.mkSimple ("T_" ++ n.toString)) .implicit natE
                fun v => do
                let hTy ← forallTelescopeReducing t fun ys _ => do
                  let img ← mkAppM (if step then kd.stepToFreeMT else kd.toFreeMT)
                    #[mkAppN x ys]
                  mkForallFVars ys (← useHypAt kd img q v)
                withLocalDeclD (Name.mkSimple ("h_" ++ n.toString)) hTy fun hx =>
                  withBounds xs (i + 1) (bs.push (x.fvarId!, v, r)) (vars.push q |>.push v)
                    (hyps.push hx) k oadv vec
      let vName := match r with
        | .tree | .kind => Name.mkSimple ("T_" ++ n.toString)
        | .key => Name.mkSimple ("G_" ++ n.toString)
        | .cost => Name.mkSimple ("t_" ++ n.toString)
      withLocalDecl vName .implicit natE fun v => do
        let hTy ← forallTelescopeReducing t fun ys _ => do
          let concl ← match r with
            | .cost => mkAppM ``LE.le #[mkAppN x ys, v]
            | .kind => do
              let some (k, step) ← kindOfType? t | throwError "withBounds: kind"
              let L := if step then k.stepTimeBoundIff else k.timeBoundIff
              let (lhs, _, _) ← iffAt L (mkAppN x ys) v
              pure lhs
            | _ => do mkAppM ``LE.le #[← mkAppM ``SPTree.Timed.time #[mkAppN x ys], v]
          mkForallFVars ys concl
        withLocalDeclD (Name.mkSimple ("h_" ++ n.toString)) hTy fun hx =>
          withBounds xs (i + 1) (bs.push (x.fvarId!, v, r)) (vars.push v) (hyps.push hx) k
            oadv vec
  else k bs vars hyps

/-- The heartbeat budget, in thousands, of the proof of one time theorem by `time_bound`. -/
def proofHeartbeats : Nat := 400000

/-- State and prove `name`: the time theorem of the costed tree `c` (a definition returning
`ℕ × SPTree.Timed α`). Returns `none` with the reason when the bound is not computed or
`time_bound` does not prove it. -/
def emitTimeBound (c name : Name) : TermElabM (Option MessageData) := do
  let info ← getConstInfo c
  let lvls := info.levelParams.map mkLevelParam
  forallTelescope info.type fun xs body => do
    unless (← whnfR body).isAppOfArity ``Prod 2 do
      return some m!"`{c}` is not a step-prefixed tree"
    withBounds xs 0 #[] #[] #[] fun bs vars hyps => do
      let x := mkAppN (Lean.mkConst c lvls) xs
      let bound ← try
          normalizeSum (← instantiateMVars (← boundStep bs x))
        catch e => return some m!"no bound: {e.toMessageData}"
      let goal ← mkAppM ``LE.le #[← mkAppM ``SPTree.Timed.stepTime #[x], bound]
      let mv ← mkFreshExprSyntheticOpaqueMVar goal
      let s ← saveState
      let tac ← `(tactic| time_bound)
      let cap (c : Core.Context) : Core.Context :=
        { c with maxHeartbeats := proofHeartbeats * 1000 }
      let r ← tryCatchRuntimeEx
        (withCurrHeartbeats <| withTheReader Core.Context cap do
          let gs ← Tactic.run mv.mvarId! (Tactic.evalTactic tac)
          return if gs.isEmpty then none else some m!"`time_bound` left goals")
        fun e => do
          if e.isInterrupt then throw e
          return some m!"`time_bound` failed: {e.toMessageData}"
      if let some why := r then
        s.restore
        return some why
      let pf ← instantiateMVars mv
      if pf.hasSorry || pf.hasExprMVar then return some m!"the proof is incomplete"
      let ty ← mkForallFVars (xs ++ vars ++ hyps) goal
      let val ← mkLambdaFVars (xs ++ vars ++ hyps) pf
      addDecl (Declaration.thmDecl
        { name, levelParams := info.levelParams, type := ty, value := val })
      return none

/-- The bounds with the hypothesis of each bounded binder. -/
abbrev HBounds := Array (FVarId × Expr × Role × Expr)

/-- `a ≤ b` over `ℕ`. -/
def mkNatLe (a b : Expr) : Expr :=
  mkApp4 (mkConst ``LE.le [Level.zero]) natE (mkConst ``instLENat) a b

/-- The maximum of the bounds `bs` folded from the left, with a proof of `bᵢ ≤ max` for each:
`max (… (max b₀ b₁) …) bₙ`. Equal neighbours are kept once, as in `boundCost`. -/
def maxChain (bs : Array Expr) : MetaM (Expr × Array Expr) := do
  let some b0 := bs[0]? | throwError "maxChain: no bound"
  let mut acc := b0
  let mut pfs : Array Expr := #[mkApp (mkConst ``Nat.le_refl) b0]
  for b in bs[1:] do
    if b == acc then
      pfs := pfs.push (mkApp (mkConst ``Nat.le_refl) b)
      continue
    let acc' ← mkMaxN acc b
    -- the earlier proofs lifted by `le_max_left`, the new bound by `le_max_right`
    let l ← mkAppM ``le_max_left #[acc, b]
    pfs ← pfs.mapM fun p => mkAppM ``le_trans #[p, l]
    pfs := pfs.push (← mkAppM ``le_max_right #[acc, b])
    acc := acc'
  return (acc, pfs)

/-- The equation `eqn` of a matcher at the application `l` of that matcher to the patterns of
its alternative, the overlap hypotheses taken from `ys`: the arguments of the alternative in
the right side, and the proof of `l = alt args`. -/
def eqnAt (eqn : Name) (l : Expr) (ys : Array Expr) : MetaM (Array Expr × Expr) := do
  let c ← mkConstWithFreshMVarLevels eqn
  let (ms, _, ty) ← forallMetaTelescopeReducing (← inferType c)
  unless ty.isAppOfArity ``Eq 3 do throwError "mirror: equation {eqn}"
  -- argument by argument: on a constructor pattern `isDefEq` would first reduce both matcher
  -- applications by iota, leaving `?h ()` against the body of the alternative
  let lhs := ty.getArg! 1
  let .const n₁ us₁ := lhs.getAppFn | throwError "mirror: equation {eqn}"
  let .const n₂ us₂ := l.getAppFn | throwError "mirror: equation {eqn} does not apply"
  unless n₁ == n₂ && us₁.length == us₂.length &&
      lhs.getAppNumArgs == l.getAppNumArgs do
    throwError "mirror: equation {eqn} does not apply"
  for u₁ in us₁, u₂ in us₂ do
    unless ← isLevelDefEq u₁ u₂ do throwError "mirror: equation {eqn}: universe"
  for a in lhs.getAppArgs, b in l.getAppArgs do
    unless ← isDefEq a b do throwError "mirror: equation {eqn} does not apply"
  for mv in ms do
    let mid := mv.mvarId!
    if ← mid.isAssigned then continue
    let t ← instantiateMVars (← mid.getType)
    let some y ← ys.findM? fun y => do isDefEq (← inferType y) t
      | throwError "mirror: overlap hypothesis of {eqn}"
    mid.assign y
  let args ← (ty.getArg! 2).getAppArgs.mapM instantiateMVars
  return (args, ← instantiateMVars (mkAppN c ms))

/-- A proof of `m[ds] ≤ rhs ds` by the splitter of the matcher of `m` with the motive
`fun ds => m[ds] ≤ rhs ds`: at alternative `i`, the equation `i` of the matcher reduces
`m[pat]` to the body of the alternative at its arguments, which `altPfs[i]` (a function of
the pattern variables of the alternative) bounds by `rhs`; when `rhsMatch`, `rhs` is a match
of the same matcher, reduced by the same equation. -/
def splitProof (m : MatcherApp) (rhs : Array Expr → Expr) (altPfs : Array Expr)
    (rhsMatch : Bool) : MetaM Expr := do
  let some pos := m.uElimPos? | throwError "mirror: match without a motive universe"
  let eqns ← Match.getEquationsFor m.matcherName
  let motive ← forallBoundedTelescope (← inferType m.motive) m.discrs.size fun xs _ =>
    mkLambdaFVars xs (mkNatLe { m with discrs := xs }.toExpr (rhs xs))
  let lvls := m.matcherLevels.set! pos Level.zero
  let f := mkAppN (mkConst eqns.splitterName lvls.toList) (m.params ++ #[motive] ++ m.discrs)
  let mut fty ← inferType f
  let mut alts : Array Expr := #[]
  for i in [0:m.alts.size] do
    let .forallE _ d b _ ← whnfD fty | throwError "mirror: splitter type"
    let pf ← forallTelescopeReducing d fun ys tgt => do
      let some (l, r) := CatCrypt.Tactics.AutoTime.natLe? tgt.headBeta
        | throwError "mirror: splitter alternative"
      let (args, eq₁) ← eqnAt eqns.eqnNames[i]! l ys
      let mut pf ← mkAppM ``le_trans #[← mkAppM ``Nat.le_of_eq #[eq₁], altPfs[i]!.beta args]
      if rhsMatch then
        let (_, eq₂) ← eqnAt eqns.eqnNames[i]! r ys
        pf ← mkAppM ``le_trans #[pf, ← mkAppM ``Nat.le_of_eq #[← mkEqSymm eq₂]]
      mkLambdaFVars ys pf
    alts := alts.push pf
    fty := b.instantiate1 pf
  return mkAppN f alts

/-- The closed form `r` of the registered cost `s = f.timedCost a` free of the variable `b`,
with a proof of `s ≤ r`: from `f.timedCost_eq` at `a` by `Nat.le_of_eq`, or from
`f.timedCost_le` at `a`, the propositional premises closed from the context
(`costClosedForm?` with its proof). -/
def costClosedFormPf? (b : FVarId) (s : Expr) : MetaM (Option (Expr × Expr)) := do
  let some n := s.getAppFn.constName? | return none
  for c in ← CatCrypt.Tactics.AutoTime.costLemmas n do
    let st ← saveState
    let (ms, _, body) ← forallMetaTelescopeReducing (← inferType c)
    let isEq := body.isAppOfArity ``Eq 3
    let side? := if isEq then some (body.getArg! 1, body.getArg! 2)
      else CatCrypt.Tactics.AutoTime.natLe? body
    let some (l, r) := side? | st.restore; continue
    if ← isDefEq l s then
      let ok ← ms.allM fun m => do
        let mid := m.mvarId!
        if ← mid.isAssigned then return true
        unless ← isProp (← mid.getType) do return true
        CatCrypt.Tactics.AutoTime.closeByContext mid
      let r ← instantiateMVars r
      let pf ← instantiateMVars (mkAppN c ms)
      if ok && !r.hasExprMVar && !pf.hasExprMVar && !r.containsFVar b then
        let pf ← if isEq then mkAppM ``Nat.le_of_eq #[pf] else pure pf
        return some (r, pf)
    st.restore
  return none

/-- The registered cost `s` with a proof of `s ≤ r`, `r` its replacement in the bound of
`boundCost`: for the pattern variables `pvs` of the enclosing matches, grouped by match from the
outermost, the innermost group first and each group in order, a registered cost that mentions
the variable is replaced by its closed form free of it, as `rewriteCosts` does at each
alternative. -/
def rewriteCostPf (pvs : Array (Array FVarId)) (s : Expr) : MetaM (Expr × Expr) := do
  let mut cur := s
  let mut pf := mkApp (mkConst ``Nat.le_refl) s
  for ys in pvs.reverse do
    for y in ys do
      let some n := cur.getAppFn.constName? | return (cur, pf)
      unless n.lastComponentAsString == "timedCost" && cur.containsFVar y do continue
      if let some (r, p) ← costClosedFormPf? y cur then
        pf ← mkAppM ``le_trans #[pf, p]
        cur := r
  return (cur, pf)

/-- The bound of a step cost `e : ℕ` with a proof of `e ≤ bound`, by the clauses of
`boundCost`; throws outside them. `pvs` are the pattern variables of the enclosing matches,
one group per match from the outermost (`rewriteCostPf`). -/
partial def mirrorCost (hs : HBounds) (pvs : Array (Array FVarId)) (e : Expr) :
    MetaM (Expr × Expr) := do
  let go := fun e => mirrorCost hs pvs e
  let e := e.headBeta
  match e with
  | .letE _ _ v b _ => go (b.instantiate1 v)
  | .mdata _ b => go b
  | _ =>
  if e.isAppOfArity ``HAdd.hAdd 6 then
    let (a, pa) ← go (e.getArg! 4)
    let (b, pb) ← go (e.getArg! 5)
    return (mkAddN a b, ← mkAppM ``Nat.add_le_add #[pa, pb])
  if e.isAppOfArity ``HMul.hMul 6 then
    let (a, pa) ← go (e.getArg! 4)
    let (b, pb) ← go (e.getArg! 5)
    return (mkMulN a b, ← mkAppM ``Nat.mul_le_mul #[pa, pb])
  if e.isAppOfArity ``Max.max 4 then
    let (a, pa) ← go (e.getArg! 2)
    let (b, pb) ← go (e.getArg! 3)
    return (← mkMaxN a b, ← mkAppM ``max_le_max #[pa, pb])
  if e.isAppOfArity ``ite 5 then
    let (a, pa) ← go (e.getArg! 3)
    let (b, pb) ← go (e.getArg! 4)
    let pf := mkAppN (mkConst ``CatCrypt.Tactics.AutoTime.ite_le_max_of)
      #[e.getArg! 1, e.getArg! 2, e.getArg! 3, e.getArg! 4, a, b, pa, pb]
    return (← mkMaxN a b, pf)
  if (CatCrypt.Tactics.AutoTime.fstOf? e).isSome then
    throwError "mirror: the step cost of a subtree"
  if let .fvar f := e.getAppFn then
    if let some (_, v, .cost, h) := hs.find? (·.1 == f) then
      return (v, mkAppN h e.getAppArgs)
  if let some m ← matchMatcherApp? e then
    let mut bnds : Array Expr := #[]
    let mut pfs : Array Expr := #[]
    let mut lams : Array Expr := #[]
    let mut dep := false
    for alt in m.alts, n in m.altNumParams do
      let (b, pf, lam, d) ← lambdaBoundedTelescope alt n fun ys body => do
        let (r, p) ← mirrorCost hs (pvs.push (ys.map (·.fvarId!))) body
        let r ← instantiateMVars r
        let d := ys.any fun y => r.containsFVar y.fvarId!
        return (r, ← mkLambdaFVars ys p, ← mkLambdaFVars ys r, d)
      bnds := bnds.push b
      pfs := pfs.push pf
      lams := lams.push lam
      dep := dep || d
    if dep then
      let some mB ← matchBound m lams | throwError "mirror: no match of the bounds"
      let some mBm ← matchMatcherApp? mB | throwError "mirror: the match of the bounds"
      let pf ← splitProof m (fun xs => { mBm with discrs := xs }.toExpr) pfs true
      return (mB, pf)
    let (B, ups) ← maxChain bnds
    -- each alternative proof lifted to the maximum
    let mut pfs' : Array Expr := #[]
    for alt in m.alts, n in m.altNumParams, pf in pfs, up in ups do
      pfs' := pfs'.push (← lambdaBoundedTelescope alt n fun ys _ => do
        mkLambdaFVars ys (← mkAppM ``le_trans #[pf.beta ys, up]))
    return (B, ← splitProof m (fun _ => B) pfs' false)
  if let some n := e.getAppFn.constName? then
    if n.lastComponentAsString == "timedCost" && pvs.any (·.any e.containsFVar) then
      return ← rewriteCostPf pvs e
  return (e, mkApp (mkConst ``Nat.le_refl) e)

/-- The outcome of `mirrorTimeBound`. -/
inductive MirrorResult where
  /-- The theorem is declared. -/
  | proved
  /-- The tree is not a pure step. -/
  | outside
  /-- The tree is a pure step and the procedure stops for the reason `why`. -/
  | refused (why : MessageData)

/-- The time theorem of the costed tree `c` with a pure step body, proved along its bound. The
theorem states the bound `B` of `emitTimeBound` (`boundStep`), so the statement does not depend
on the procedure that proves it; `B₀ ≤ B` is proved by `omega` against `B` in projection-normal
form, which is definitionally `B`. -/
def mirrorTimeBound (c name : Name) : TermElabM MirrorResult := do
  let info ← getConstInfo c
  let lvls := info.levelParams.map mkLevelParam
  forallTelescope info.type fun xs _ => do
    withBounds xs 0 #[] #[] #[] fun bs vars hyps => do
      let hs : HBounds := (bs.zip hyps).map fun ((f, v, r), h) => (f, v, r, h)
      let x := mkAppN (Lean.mkConst c lvls) xs
      -- the pair as `boundStep` reads it
      let body ← reduceHead x
      unless body.isAppOfArity ``Prod.mk 4 do return .outside
      let t ← reduceHead (body.getArg! 3)
      unless t.isAppOfArity ``SPTree.Timed.ret 2 do return .outside
      let bound? : Except MessageData Expr ← try
          pure (.ok (← normalizeSum (← instantiateMVars (← boundStep bs x))))
        catch ex => pure (.error ex.toMessageData)
      let bound ← match bound? with
        | .ok b => pure b
        | .error why => return .refused m!"no bound: {why}"
      let e := body.getArg! 2
      let eP ← CatCrypt.Tactics.DeriveReduction.reduceProjCtor e
      let r : Except MessageData (Expr × Expr) ← try
          pure (.ok (← mirrorCost hs #[] eP))
        catch ex => pure (.error ex.toMessageData)
      let (b0, pe) ← match r with
        | .ok p => pure p
        | .error why => return .refused why
      let b0 ← instantiateMVars b0
      -- `B₀ ≤ B` by `omega`, `B` the bound of `boundStep` in projection-normal form
      let boundP ← CatCrypt.Tactics.DeriveReduction.reduceProjCtor bound
      let mv ← mkFreshExprSyntheticOpaqueMVar (mkNatLe b0 boundP)
      let gs ← try Tactic.run mv.mvarId! (Tactic.evalTactic (← `(tactic| omega)))
        catch _ => pure [mv.mvarId!]
      unless gs.isEmpty do
        return .refused m!"`omega` does not prove{indentExpr (mkNatLe b0 boundP)}"
      -- `stepTime x ≤ B` from `e ≤ B₀ ≤ B` by `st_start`, `st_pair` and `time_ret`, the body
      -- `(e, ret a)` of `x` read by the kernel through the definition of `x`
      let goal ← mkAppM ``LE.le #[← mkAppM ``SPTree.Timed.stepTime #[x], bound]
      let α := t.getArg! 0
      let h1 ← mkAppM ``Nat.le_trans #[pe, ← instantiateMVars mv]
      let h2 ← mkAppM ``Nat.le_trans #[← mkAppM ``Nat.le_of_eq #[← mkAppM ``Nat.zero_add #[e]], h1]
      let h3 := mkAppN (mkConst ``CatCrypt.Tactics.AutoTime.time_ret)
        #[α, mkAddN (mkNatLit 0) e, bound, t.getArg! 1, h2]
      let h4 ← mkAppM ``CatCrypt.Tactics.AutoTime.st_pair #[h3]
      let pf := mkAppN (mkConst ``CatCrypt.Tactics.AutoTime.st_start) #[α, bound, x, h4]
      let ty ← mkForallFVars (xs ++ vars ++ hyps) goal
      let v ← mkLambdaFVars (xs ++ vars ++ hyps) pf
      addDecl (Declaration.thmDecl
        { name, levelParams := info.levelParams, type := ty, value := v })
      return .proved

/-! ## The bound of a costed oracle adversary -/

/-- A proof of `l = r` over `ℕ` by `omega`, with the hypotheses of the context cleared. -/
def omegaEq (l r : Expr) : TermElabM Expr := do
  let mv ← mkFreshExprSyntheticOpaqueMVar (← mkEq l r)
  let mut hs : Array FVarId := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    if ← isProp d.type then hs := hs.push d.fvarId
  let g ← mv.mvarId!.tryClearMany hs
  let gs ← Tactic.run g (Tactic.evalTactic (← `(tactic| omega)))
  unless gs.isEmpty do throwError "the step cost is not{indentExpr r}"
  instantiateMVars mv

mutual

/-- A bound of `e : ℕ` free of the variables `xs`, with a proof of `e ≤ bound`: the clauses of
`AutoTime.boundFree?`, with a dependent `if` bounded by the maximum of the bounds of its
branches (`dite_le_max_of`), and the premise `∀ y, fCost y ≤ ?k` of the lemma `f.timedCost_le`
of a registered cost closed by the bound of `fCost y` free of `y` and of `xs`
(`closeBound`). -/
partial def bfree? (xs : Array FVarId) (e : Expr) (fuel : Nat := 64) :
    MetaM (Option (Expr × Expr)) := do
  if fuel == 0 then return none
  let e := (← instantiateMVars e).headBeta
  match e with
  | .letE _ _ v b _ => return ← bfree? xs (b.instantiate1 v) (fuel - 1)
  | .mdata _ b => return ← bfree? xs b (fuel - 1)
  | _ => pure ()
  unless xs.any e.containsFVar do return some (e, ← mkAppM ``Nat.le_refl #[e])
  if e.isAppOfArity ``HAdd.hAdd 6 || e.isAppOfArity ``HMul.hMul 6 ||
      e.isAppOfArity ``Max.max 4 then
    let n := e.getAppNumArgs
    let some (a, pa) ← bfree? xs (e.getArg! (n - 2)) (fuel - 1) | return none
    let some (b, pb) ← bfree? xs (e.getArg! (n - 1)) (fuel - 1) | return none
    if e.isAppOfArity ``HAdd.hAdd 6 then
      return some (mkAddN a b, ← mkAppM ``Nat.add_le_add #[pa, pb])
    if e.isAppOfArity ``HMul.hMul 6 then
      return some (mkMulN a b, ← mkAppM ``Nat.mul_le_mul #[pa, pb])
    return some (← mkMaxN a b, ← mkAppM ``max_le_max #[pa, pb])
  if e.isAppOfArity ``ite 5 then
    let some (a, pa) ← bfree? xs (e.getArg! 3) (fuel - 1) | return none
    let some (b, pb) ← bfree? xs (e.getArg! 4) (fuel - 1) | return none
    let pf := mkAppN (mkConst ``CatCrypt.Tactics.AutoTime.ite_le_max_of)
      #[e.getArg! 1, e.getArg! 2, e.getArg! 3, e.getArg! 4, a, b, pa, pb]
    return some (← mkMaxN a b, pf)
  if e.isAppOfArity ``dite 5 then
    let c := e.getArg! 1
    let branch (ty br : Expr) : MetaM (Option (Expr × Expr)) :=
      withLocalDeclD `h ty fun h => do
        let some (a, pa) ← bfree? (xs.push h.fvarId!) (br.beta #[h]) (fuel - 1)
          | return none
        return some (a, ← mkLambdaFVars #[h] pa)
    let some (a, pa) ← branch c (e.getArg! 3) | return none
    let some (b, pb) ← branch (mkNot c) (e.getArg! 4) | return none
    let pf := mkAppN (mkConst ``dite_le_max_of)
      #[c, e.getArg! 2, e.getArg! 3, e.getArg! 4, a, b, pa, pb]
    return some (← mkMaxN a b, pf)
  if let some n := e.getAppFn.constName? then
    if n.lastComponentAsString == "timedCost" then
      for c in ← CatCrypt.Tactics.AutoTime.costLemmas n do
        let st ← saveState
        let (ms, _, body) ← forallMetaTelescopeReducing (← inferType c)
        let isEq := body.isAppOfArity ``Eq 3
        let side? := if isEq then some (body.getArg! 1, body.getArg! 2)
          else CatCrypt.Tactics.AutoTime.natLe? body
        let some (l, r) := side? | st.restore; continue
        if ← isDefEq l e then
          let ok ← ms.allM fun m => do
            let mid := m.mvarId!
            if ← mid.isAssigned then return true
            unless ← isProp (← mid.getType) do return true
            closeBound xs mid (fuel - 1)
          let r ← instantiateMVars r
          let pf ← instantiateMVars (mkAppN c ms)
          if ok && !r.hasExprMVar && !pf.hasExprMVar then
            let pf ← if isEq then mkAppM ``Nat.le_of_eq #[pf] else pure pf
            if let some (b, pb) ← bfree? xs r (fuel - 1) then
              return some (b, ← mkAppM ``Nat.le_trans #[pf, pb])
        st.restore
  CatCrypt.Tactics.AutoTime.boundFree? xs e fuel

/-- Close the premise `mid`: `∀ ys, l ≤ ?r` with `?r` unassigned by `?r` the bound of `l` free
of `ys` and `xs` (`bfree?`), any other premise by `AutoTime.closeByContext`. -/
partial def closeBound (xs : Array FVarId) (mid : MVarId) (fuel : Nat) : MetaM Bool :=
  mid.withContext do
    let ty ← instantiateMVars (← mid.getType)
    let s ← saveState
    let ok ← try
        forallTelescopeReducing ty fun ys body => do
          let some (l, r) := CatCrypt.Tactics.AutoTime.natLe? body | return false
          unless (← instantiateMVars r).getAppFn.isMVar do return false
          let some (b, pf) ← bfree? (xs ++ ys.map (·.fvarId!)) l fuel | return false
          unless ← isDefEq r b do return false
          mid.assign (← mkLambdaFVars ys pf)
          return true
      catch _ => pure false
    if ok then return true
    s.restore
    CatCrypt.Tactics.AutoTime.closeByContext mid fuel

end

/-- Whether `ty` (under its binders) is an inequality over `ℕ`. -/
def isNatLeLeaf (ty : Expr) : MetaM Bool :=
  forallTelescopeReducing ty fun _ body =>
    pure (CatCrypt.Tactics.AutoTime.natLe? body).isSome

/-- The proposition `ty` one step unfolded: `whnfCore`, else the unfolding of its head
definition; `none` when neither changes it. -/
def unfoldProp? (ty : Expr) : MetaM (Option Expr) := do
  let ty' ← whnfCore ty
  if ty' != ty then return some ty'
  return (← unfoldDefinition? ty).map (·.headBeta)

/-- The leaves of a premise `ty`: its conjuncts, each head definition unfolded, down to
inequalities `∀ ys, l ≤ r` over `ℕ`; `none` when a conjunct is not one. -/
partial def premLeaves (ty : Expr) (fuel : Nat := 8) : MetaM (Option (Array Expr)) := do
  let ty ← instantiateMVars ty
  if ← isNatLeLeaf ty then return some #[ty]
  if ty.isAppOfArity ``And 2 then
    let some a ← premLeaves (ty.getArg! 0) fuel | return none
    let some b ← premLeaves (ty.getArg! 1) fuel | return none
    return some (a ++ b)
  if fuel == 0 then return none
  let some ty' ← unfoldProp? ty | return none
  premLeaves ty' (fuel - 1)

/-- The proof of the premise `ty` from the proofs `pfs` of its leaves from index `k`, along the
traversal of `premLeaves`, with the index after its last leaf. -/
partial def premProof (ty : Expr) (pfs : Array Expr) (k : Nat) (fuel : Nat := 8) :
    MetaM (Expr × Nat) := do
  let ty ← instantiateMVars ty
  if ← isNatLeLeaf ty then return (pfs[k]!, k + 1)
  if ty.isAppOfArity ``And 2 then
    let (a, k) ← premProof (ty.getArg! 0) pfs k fuel
    let (b, k) ← premProof (ty.getArg! 1) pfs k fuel
    return (← mkAppM ``And.intro #[a, b], k)
  if fuel == 0 then throwError "premProof: premise{indentExpr ty}"
  let some ty' ← unfoldProp? ty | throwError "premProof: premise{indentExpr ty}"
  premProof ty' pfs k (fuel - 1)

/-- The bound of a leaf `∀ ys, l ≤ ?M` whose right side is an unassigned metavariable: `?M`, the
bound of `l` free of `ys` and `xs` (its projections of constructors reduced), and the proof of
`∀ ys, l ≤ bound` as a function of `ys`. -/
def leafBound? (xs : Array FVarId) (leaf : Expr) : MetaM (Option (MVarId × Expr × Expr)) :=
  forallTelescopeReducing leaf fun ys body => do
    let some (l, r) := CatCrypt.Tactics.AutoTime.natLe? body | return none
    let r ← instantiateMVars r
    let .mvar m := r | return none
    if ← m.isAssigned then return none
    let l ← CatCrypt.Tactics.DeriveReduction.reduceProjCtor (← instantiateMVars l)
    let some (b, pf) ← bfree? (xs ++ ys.map (·.fvarId!)) l | return none
    if ys.any fun y => b.containsFVar y.fvarId! then return none
    return some (m, b, ← mkLambdaFVars ys pf)

/-- Whether the numeral `e` is zero. -/
def isZeroNat (e : Expr) : Bool :=
  e.nat? == some 0 || e.rawNatLit? == some 0

/-- Close the premises `ms` of the time theorem of a callee. A premise whose leaves
(`premLeaves`: its conjuncts, head definitions unfolded) are all bounds `∀ ys, l ≤ ?M` at an
unassigned `?M` (a cost bound shared by several companions, the bound of the cost companions of
a state passed to the callee) is a family: each `?M` is assigned the maximum of the bounds of
its leaves free of `ys` and `xs` (`leafBound?`), zero bounds left out, and each leaf is proved
through `le_max_left` and `le_max_right` (`maxChain`). The other premises are closed by
`AutoTime.closeByContext`. -/
def closePremises (xs : Array FVarId) (ms : Array Expr) : MetaM Bool := do
  let mut fam : Array (MVarId × Array Expr) := #[]
  for m in ms do
    let mid := m.mvarId!
    if ← mid.isAssigned then continue
    unless ← isProp (← mid.getType) do continue
    let some ls ← premLeaves (← mid.getType) | continue
    let isFam ← ls.allM fun l => forallTelescopeReducing l fun _ body => do
      let some (_, r) := CatCrypt.Tactics.AutoTime.natLe? body | return false
      match ← instantiateMVars r with
      | .mvar m => return !(← m.isAssigned)
      | _ => return false
    if isFam && !ls.isEmpty then fam := fam.push (mid, ls)
  let mut data : Array (MVarId × Expr × Expr) := #[]
  for (_, ls) in fam do
    for l in ls do
      let some d ← leafBound? xs l | return false
      data := data.push d
  -- each `?M` is assigned the maximum of the bounds of its leaves
  let mut ups : Array Expr := Array.replicate data.size (default : Expr)
  let mut done : Array MVarId := #[]
  for (mv, _, _) in data do
    if done.contains mv then continue
    done := done.push mv
    let idx := (List.range data.size).filter fun i => data[i]!.1 == mv
    let mut uniq : Array Expr := #[]
    for i in idx do
      let b := data[i]!.2.1
      unless isZeroNat b || uniq.contains b do uniq := uniq.push b
    let (M, pfs) ← if uniq.isEmpty then pure (mkNatLit 0, #[]) else maxChain uniq
    unless ← isDefEq (mkMVar mv) M do return false
    for i in idx do
      let b := data[i]!.2.1
      let up ← match uniq.idxOf? b with
        | some j => pure pfs[j]!
        | none => mkAppM ``Nat.zero_le #[M]
      ups := ups.set! i up
  -- the proofs of the leaves, then of the premises
  let mut leafPfs : Array Expr := #[]
  let mut i := 0
  for (_, ls) in fam do
    for l in ls do
      let pf := data[i]!.2.2
      let up := ups[i]!
      leafPfs := leafPfs.push (← forallTelescopeReducing (← instantiateMVars l) fun ys _ => do
        mkLambdaFVars ys (← mkAppM ``Nat.le_trans #[pf.beta ys, up]))
      i := i + 1
  let mut k := 0
  for (mid, _) in fam do
    let (p, k') ← premProof (← mid.getType) leafPfs k
    mid.assign p
    k := k'
  for m in ms do
    let mid := m.mvarId!
    if ← mid.isAssigned then continue
    unless ← isProp (← mid.getType) do continue
    unless ← CatCrypt.Tactics.AutoTime.closeByContext mid do return false
  return true

/-- `k` under let-bound local hypotheses for the parts of the hypothesis `h : ty`: its
conjuncts, each head definition unfolded, so that their bounds `∀ a, π a ≤ c` are local
hypotheses of `bfree?`; `k` receives the let-bound variables in the order of the context. -/
partial def withInvHyps {γ : Type} (h ty : Expr) (k : Array Expr → TermElabM γ)
    (fuel : Nat := 8) : TermElabM γ := do
  let ty ← instantiateMVars ty
  if ty.isAppOfArity ``And 2 then
    let a := ty.getArg! 0
    let b := ty.getArg! 1
    let pa ← mkAppM ``And.left #[h]
    let pb ← mkAppM ``And.right #[h]
    withLetDecl `hl a pa fun h₁ =>
      withLetDecl `hr b pb fun h₂ =>
        withInvHyps h₁ a (fuel := fuel) fun l₁ =>
          withInvHyps h₂ b (fuel := fuel) fun l₂ => k (#[h₁, h₂] ++ l₁ ++ l₂)
  else if fuel == 0 || (← isNatLeLeaf ty) then k #[]
  else
    match ← unfoldProp? ty with
    | some ty' => withLetDecl `hu ty' h fun h' =>
        withInvHyps h' ty' (fuel := fuel - 1) fun l => k (#[h'] ++ l)
    | none => k #[]

/-- The first projection `y.1` among the subterms of `e`. -/
def findFst (e y : Expr) : Option Expr :=
  (CatCrypt.Tactics.AutoTime.appsOf e #[]).find? fun o =>
    match CatCrypt.Tactics.AutoTime.fstOf? o with
    | some y' => y' == y
    | none => false

/-! ## The fold rule -/


/-- A bound of the charge fold of a program with its proof
`wpFold Φ x (fun _ => 0) ≤ ↑bound` and, when the leaves of `x` are known to satisfy a
predicate `Q` (from the time theorem of a callee), `Q` with the proof of the demonic fold
`wpFold (OpSpec.demonicUnder allows) x Q`. -/
structure FoldB where
  /-- The bound, a natural number. -/
  bound : Expr
  /-- The proof of the bound. -/
  proof : Expr
  /-- The leaf invariant and its demonic fold. -/
  inv : Option (Expr × Expr) := none

/-- The context of the fold rule: the fold facts (`∀ ys, wpFold Φ x (fun _ => 0) ≤ ↑n`, the
time-bound hypotheses of binder trees read through the registered equivalences, and the fold
bounds of the local context), and the variables that no bound may mention. -/
structure FoldCx where
  /-- The proofs of the fold facts. -/
  facts : Array Expr := #[]
  /-- The variables eliminated from every bound. -/
  avoid : Array FVarId := #[]

/-- `ℕ∞`. -/
def enatE : Expr := mkConst ``ENat

/-- `(n : ℕ∞)`. -/
def enatCast (n : Expr) : MetaM Expr :=
  mkAppOptM ``Nat.cast #[some enatE, none, some n]

/-- The parts `(Φ, x, post, r)` of `wpFold Φ x post ≤ r`. -/
def foldLe? (e : Expr) : Option (Expr × Expr × Expr × Expr) := do
  guard (e.isAppOfArity ``LE.le 4)
  let w := e.getArg! 2
  guard (w.isAppOfArity ``PFunctor.FreeM.wpFold 6)
  return (w.getArg! 3, w.getArg! 4, w.getArg! 5, e.getArg! 3)

/-- The natural number `n` of the cast `(n : ℕ∞)`. -/
def natOfCast? (e : Expr) : Option Expr :=
  if e.isAppOfArity ``Nat.cast 3 then some (e.getArg! 2) else none

/-- The charge `c : P.A → ℕ` and the answer relation of `OpSpec.chargeUnder (fun a => ↑(c a))
allows`; `OpSpec.charge` reads as every answer allowed. -/
def chargeOf? (Φ : Expr) : MetaM (Option (Expr × Expr × Bool)) := do
  let Φ ← instantiateMVars Φ
  let fn := Φ.getAppFn
  let args := Φ.getAppArgs
  let (cf, allows?, under) ← match fn.constName? with
    | some ``PFunctor.OpSpec.chargeUnder =>
      if args.size == 6 then pure (args[4]!, some args[5]!, true) else return none
    | some ``PFunctor.OpSpec.charge =>
      if args.size == 5 then pure (args[4]!, none, false) else return none
    | _ => return none
  let P := args[0]!
  let c ← match cf.eta with
    | .lam n ty b bi =>
      if let some m := natOfCast? b then pure (Expr.lam n ty m bi)
      else return none
    | _ => return none
  let allows ← match allows? with
    | some a => pure a
    | none => do
      let pa ← mkAppM ``PFunctor.A #[P]
      withLocalDeclD `a pa fun a => do
        let pb ← mkAppM ``PFunctor.B #[P, a]
        withLocalDeclD `b pb fun b => mkLambdaFVars #[a, b] (mkConst ``True)
  return some (c, allows, under)

/-- `fun a => ((c a : ℕ) : ℕ∞)`. -/
def chargeFn (c : Expr) : MetaM Expr := do
  let .lam n ty b bi := c | throwError "chargeFn: {c}"
  withLocalDecl n bi ty fun a => do
    mkLambdaFVars #[a] (← enatCast (b.instantiate1 a))

/-- The charge reading `Φ` over the allowed answers: `OpSpec.charge c` read as
`OpSpec.chargeUnder c (fun _ _ => True)`. -/
def normSpec (Φ : Expr) : MetaM Expr := do
  unless Φ.isAppOfArity ``PFunctor.OpSpec.charge 5 do return Φ
  let some (c, allows, _) ← chargeOf? Φ | return Φ
  mkAppOptM ``PFunctor.OpSpec.chargeUnder
    #[none, none, none, none, some (← chargeFn c), some allows]

/-- The proof `pf : wpFold Φ x post ≤ r` restated over `OpSpec.chargeUnder c (fun _ _ => True)`
when `Φ` is `OpSpec.charge c`. -/
def normFold (pf : Expr) : MetaM Expr := do
  let ty ← whnfR (← instantiateMVars (← inferType pf))
  let some (Φ, x, post, _) := foldLe? ty | return pf
  unless Φ.isAppOfArity ``PFunctor.OpSpec.charge 5 do return pf
  let eq ← mkAppM ``PFunctor.FreeM.wpFold_charge_eq_chargeUnder_true #[Φ.getArg! 4, x, post]
  mkAppM ``Eq.trans_le #[← mkEqSymm eq, pf]

/-- The proof `pf` over `OpSpec.chargeUnder c (fun _ _ => True)` restated over `Φ`, when `Φ` is
`OpSpec.charge c`. -/
def denormFold (Φ pf : Expr) : MetaM Expr := do
  unless Φ.isAppOfArity ``PFunctor.OpSpec.charge 5 do return pf
  let ty ← instantiateMVars (← inferType pf)
  let some (_, x, post, _) := foldLe? ty | return pf
  let eq ← mkAppM ``PFunctor.FreeM.wpFold_charge_eq_chargeUnder_true #[Φ.getArg! 4, x, post]
  mkAppM ``Eq.trans_le #[eq, pf]

/-- The statement `wpFold Φ x (fun _ => 0) ≤ ↑n`. -/
def foldGoal (Φ x n : Expr) : MetaM Expr := do
  let xt ← whnfR (← inferType x)
  let α := xt.appArg!
  let z ← mkNumeral enatE 0
  let post ← withLocalDeclD `a α fun a => mkLambdaFVars #[a] z
  mkAppM ``LE.le #[← mkAppM ``PFunctor.FreeM.wpFold #[Φ, x, post], ← enatCast n]

/-- The proof of `B₀ ≤ B` over `ℕ` by `omega`, after the facts of `AutoTime.addCostFacts` and
`AutoTime.addLengthFacts`, and else by `omega` after `ring_nf`. -/
def arithLe (l r : Expr) : TermElabM Expr := do
  let mv ← mkFreshExprSyntheticOpaqueMVar (mkNatLe l r)
  let g ← CatCrypt.Tactics.AutoTime.addCostFacts mv.mvarId!
  let g ← CatCrypt.Tactics.AutoTime.addLengthFacts g
  let gs ← Tactic.run g (Tactic.evalTactic
    (← `(tactic| first | omega | (ring_nf <;> omega) | (simp only [Nat.cast_id] at * <;> omega))))
  unless gs.isEmpty do throwError "arithLe"
  instantiateMVars mv

/-- `e` with its head definition unfolded and its matchers reduced while the head is applied to a
constructor (the charge `tickCost (.inr n)` of a position read as `n`) and is not an arithmetic
operation, a numeral, a registered cost or a proposition former, at most `fuel` times. -/
partial def reduceCharge (e : Expr) (fuel : Nat := 8) : MetaM Expr := do
  let e ← whnfR e.headBeta
  if fuel == 0 then return e
  let stop := [``HAdd.hAdd, ``HMul.hMul, ``HSub.hSub, ``Max.max, ``ite, ``dite, ``OfNat.ofNat,
    ``Nat.succ, ``List.length, ``CatCrypt.Core.SPTree.Timed.time, ``Membership.mem, ``Eq, ``Ne,
    ``Not, ``LT.lt, ``LE.le]
  match e.getAppFn with
  | .const n _ =>
    if stop.contains n || n.lastComponentAsString == "timedCost" then return e
    let onCtor ← e.getAppArgs.anyM fun a => do
      let a ← whnfR a
      match a.getAppFn.constName? with
      | some c => return (← getEnv).isConstructor c
      | none => return false
    unless onCtor do return e
    let some e' ← withDefault (unfoldDefinition? e) | return e
    let e'' ← whnfCore e'.headBeta
    if e'' == e then return e
    reduceCharge e'' (fuel - 1)
  | _ => return e

/-- `e` with each projection `y.1` or `y.2` of a pair `y` whose head reduces (`reduceHead`, the
unfolding of a non-recursive definition such as `delay` or a bind returning a pair) to a pair
replaced by the field, and each projection of a constructor reduced. -/
def reduceProjs (e : Expr) : MetaM Expr := do
  let e ← CatCrypt.Tactics.DeriveReduction.reduceProjCtor e
  Meta.transform e (post := fun s => do
    let (y?, i) := match CatCrypt.Tactics.AutoTime.fstOf? s,
        CatCrypt.Tactics.AutoTime.sndOf? s with
      | some y, _ => (some y, 0)
      | _, some y => (some y, 1)
      | _, _ => (none, 0)
    let some y := y? | return .continue
    if y.hasLooseBVars then return .continue
    let y' ← reduceHead y
    if y'.isAppOfArity ``Prod.mk 4 then
      return .visit (if i == 0 then y'.getArg! 2 else y'.getArg! 3)
    return .continue)

/-- The proposition `allows a b` reduced; `none` when it reduces to `True`. -/
def reduceAllows (p : Expr) : MetaM (Option Expr) := do
  let p' ← reduceCharge p
  if p'.isConstOf ``True then return none
  return some p'

/-- A proof of `p` or of `¬p` in the local context. -/
def decided? (p : Expr) : MetaM (Option (Bool × Expr)) := do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    unless ← isProp d.type do continue
    if ← withNewMCtxDepth (isDefEq d.type p) then return some (true, d.toExpr)
    if ← withNewMCtxDepth (isDefEq d.type (mkNot p)) then return some (false, d.toExpr)
  return none

/-- The instance of the lemma `L` at fresh metavariables read as an implication `A → B`: an
equivalence `A ↔ B` from left to right (`rev`: from right to left), or an implication whose
last premise is `A`, read forwards only; with the metavariables and the map from a proof of `A`
to a proof of `B`. -/
def lemmaImp (L : Name) (rev : Bool) :
    MetaM (Option (Array Expr × Expr × Expr × (Expr → MetaM Expr))) := do
  let cL ← mkConstWithFreshMVarLevels L
  let (ls, _, lt) ← forallMetaTelescopeReducing (← inferType cL)
  if lt.isAppOfArity ``Iff 2 then
    let pL := mkAppN cL ls
    if rev then
      return some (ls, lt.getArg! 1, lt.getArg! 0, fun p => mkAppM ``Iff.mpr #[pL, p])
    return some (ls, lt.getArg! 0, lt.getArg! 1, fun p => mkAppM ``Iff.mp #[pL, p])
  if rev || ls.isEmpty then return none
  let A ← instantiateMVars (← inferType ls.back!)
  let pL := mkAppN cL ls.pop
  return some (ls.pop, A, lt, fun p => pure (mkApp pL p))

/-- The fold facts of `h : ty` read under the binders of `ty` (`reducing`: of its weak head normal
form); see `toFoldFacts`. -/
def toFoldFactsWith (h ty : Expr) (reducing : Bool) : MetaM (Array Expr) := do
  let tele : (Array Expr → Expr → MetaM (Array Expr)) → MetaM (Array Expr) :=
    if reducing then forallTelescopeReducing ty else forallTelescope ty
  tele fun ys body => do
    let hb := mkAppN h ys
    if (foldLe? body).isSome then
      let some (Φ, _, _, r) := foldLe? body | return #[]
      unless (natOfCast? r).isSome do return #[]
      unless (← chargeOf? Φ).isSome do return #[]
      return #[← mkLambdaFVars ys (← normFold hb)]
    let mut out := #[]
    for k in ← foldKinds do
      for L in #[k.timeBoundIff, k.stepTimeBoundIff] ++ k.hypIffs do
        let st ← saveState
        try
          if let some (_, lhs, rhs, mk) ← lemmaImp L false then
            if (foldLe? rhs).isSome then
              if ← isDefEq lhs body then
                let pf ← instantiateMVars (← mk hb)
                let pty ← instantiateMVars (← inferType pf)
                if !pf.hasExprMVar && (foldLe? pty).isSome then
                  let f ← instantiateMVars (← mkLambdaFVars ys (← normFold pf))
                  st.restore
                  out := out.push f
                  continue
        catch _ => pure ()
        st.restore
    return out

/-- The fold facts of the proof `h : ∀ ys, body`: `body` a bound on a charge fold, or the left
side of a registered equivalence or implication from a time-bound predicate to a bound on a
charge fold (`FoldKind.timeBoundIff`, `FoldKind.stepTimeBoundIff`, `FoldKind.hypIffs`). A use
bound at a vector charge gives one fact per component (its readings among `hypIffs`); its
binders are read without unfolding the use bound, whose order on vectors is pointwise. -/
def toFoldFacts (h : Expr) : MetaM (Array Expr) := do
  let ty ← instantiateMVars (← inferType h)
  let r ← toFoldFactsWith h ty false
  if !r.isEmpty then return r
  toFoldFactsWith h ty true

/-- The first fold fact of the proof `h` (`toFoldFacts`). -/
def toFoldFact? (h : Expr) : MetaM (Option Expr) :=
  return (← toFoldFacts h)[0]?

/-- The bound of the program `x` from a fold fact of `cx` whose program unifies with `x`. -/
def factAt? (cx : FoldCx) (Φ x : Expr) : MetaM (Option FoldB) := do
  for f in cx.facts do
    let st ← saveState
    let (ms, _, body) ← forallMetaTelescopeReducing (← inferType f)
    let some (Φf, xf, _, r) := foldLe? body | st.restore; continue
    if (← isDefEq xf x) && (← isDefEq Φf Φ) then
      let pf ← instantiateMVars (mkAppN f ms)
      let some n := natOfCast? (← instantiateMVars r) | st.restore; continue
      let n ← instantiateMVars n
      unless pf.hasExprMVar || n.hasExprMVar do return some { bound := n, proof := pf }
    st.restore
  return none

/-- The record, the image (`false`: `toFreeMT`, `true`: `stepToFreeMT`) and the tree of the
image `x` of a costed tree of a registered kind. -/
def imageOf? (x : Expr) : MetaM (Option (FoldKind × Bool × Expr)) := do
  let some n := x.getAppFn.constName? | return none
  if x.getAppNumArgs == 0 then return none
  for k in ← foldKinds do
    if n == k.toFreeMT then return some (k, false, x.appArg!)
    if n == k.stepToFreeMT then return some (k, true, x.appArg!)
  return none

/-- The equation `n` (`FoldKind.stepFold`, `FoldKind.bindFold`) at its instance whose left side
is `lhs`, its instances synthesized and its remaining premises closed as in `appTrivial`. -/
def eqAt (n : Name) (lhs : Expr) : MetaM Expr := do
  let c ← mkConstWithFreshMVarLevels n
  let (ms, bis, body) ← forallMetaTelescopeReducing (← inferType c)
  unless body.isAppOfArity ``Eq 3 do throwError "eqAt: `{n}` is not an equation"
  unless ← isDefEq (body.getArg! 1) lhs do
    throwError "eqAt: `{n}` does not apply to{indentExpr lhs}"
  for i in [0:ms.size] do
    if bis[i]! == .instImplicit then
      let m := ms[i]!.mvarId!
      unless ← m.isAssigned do
        m.assign (← synthInstance (← instantiateMVars (← m.getType)))
  for m in ms do
    let mid := m.mvarId!
    if ← mid.isAssigned then continue
    let ty ← instantiateMVars (← mid.getType)
    unless ← isProp ty do continue
    let pf ← forallTelescopeReducing ty fun ys b => do
      let b' ← reduceCharge b
      unless b'.isConstOf ``True do throwError "eqAt: the premise{indentExpr ty}"
      mkLambdaFVars ys (mkConst ``True.intro)
    mid.assign pf
  let e ← instantiateMVars (mkAppN c ms)
  if e.hasExprMVar then throwError "eqAt: `{n}` is not determined by its left side"
  return e

/-- The first of the equations `ns` that applies at `lhs` (`eqAt`): the equation of a kind at
its charge, then its equations at the further component charges of a vector charge. -/
def eqAtAny (ns : Array Name) (lhs : Expr) : MetaM Expr := do
  let mut err : MessageData := m!"eqAtAny: no equation"
  for n in ns do
    let st ← saveState
    try
      return ← eqAt n lhs
    catch e =>
      st.restore
      err := e.toMessageData
  throwError err

/-- The charge fold `wpFold Φ x post`. -/
def foldOf (Φ x post : Expr) : MetaM Expr :=
  mkAppM ``PFunctor.FreeM.wpFold #[Φ, x, post]

/-- The constant `post = fun _ => 0` of the charge folds of programs `x`. -/
def zeroPost (x : Expr) : MetaM Expr := do
  let xt ← whnfR (← inferType x)
  let z ← mkNumeral enatE 0
  withLocalDeclD `a xt.appArg! fun a => mkLambdaFVars #[a] z

/-- The bound of the program `x` from the bound `r` of the program `x'` and a proof
`eq : x = x'`. -/
def transportFold (Φ x eq : Expr) (r : FoldB) : MetaM FoldB := do
  let post ← zeroPost x
  let xt ← inferType x
  let f ← withLocalDeclD `z xt fun z => do
    mkLambdaFVars #[z] (← mkAppM ``PFunctor.FreeM.wpFold #[Φ, z, post])
  let feq ← mkCongrArg f eq
  return { bound := r.bound, proof := ← mkAppM ``Eq.trans_le #[feq, r.proof] }

/-- The leaf invariant `Q` and the proof of `wpFold (OpSpec.demonicUnder allows) x Q` from the
proof `q : AllRet Q t` of the leaf invariant of the tree `t` of the image `x`, by
`FoldKind.allRetFold`; for a step-prefixed image, lifted over its first tick. -/
def invFold? (k : FoldKind) (step : Bool) (allows x q : Expr) :
    MetaM (Option (Expr × Expr)) := do
  let some arf := k.allRetFold | return none
  let st ← saveState
  try
    let qty ← instantiateMVars (← inferType q)
    let cF ← mkConstWithFreshMVarLevels arf
    let (fs, _, ft) ← forallMetaTelescopeReducing (← inferType cF)
    let (fl, isIff) :=
      if ft.isAppOfArity ``Iff 2 then (ft.getArg! 0, true) else (ft.bindingDomain!, false)
    unless ← isDefEq fl qty do st.restore; return none
    let pF := mkAppN cF fs
    let d ← if isIff then mkAppM ``Iff.mp #[pF, q] else pure (mkApp pF q)
    let d ← instantiateMVars d
    let dty ← whnfR (← instantiateMVars (← inferType d))
    unless dty.isAppOfArity ``PFunctor.FreeM.wpFold 6 do st.restore; return none
    let Q := dty.getArg! 5
    if !step then return some (Q, d)
    let x' ← whnfD x
    unless x'.isAppOfArity ``PFunctor.FreeM.liftBind 4 do st.restore; return none
    let d' ← mkAppM ``PFunctor.FreeM.wpFold_demonicUnder_liftBind_const
      #[allows, x'.getArg! 2, d]
    return some (Q, d')
  catch _ =>
    st.restore
    return none

/-- The bound of the image `x` of the tree `t` from the time theorem of a callee
(`AutoTime.envSources` of `t`): a conclusion, or the left conjunct of a conclusion, read as a
bound on the charge fold of `x` by the registered equivalences of the kind `k`, its premises
closed by `closePremises`; a right conjunct `AllRet Q t'` (`FoldKind.allRet`) is the leaf
invariant (`invFold?`). -/
def calleeFold? (cx : FoldCx) (k : FoldKind) (step : Bool) (Φ allows x t : Expr) :
    MetaM (Option FoldB) := do
  for c in ← CatCrypt.Tactics.AutoTime.envSources t do
    let st ← saveState
    try
      let (ms, _, body) ← forallMetaTelescopeReducing (← inferType c)
      let isAnd := body.isAppOfArity ``And 2
      let core := if isAnd then body.getArg! 0 else body
      let pc0 := mkAppN c ms
      let pcore ← if isAnd then mkAppM ``And.left #[pc0] else pure pc0
      let mut found : Option (Expr × Expr) := none
      for L in #[if step then k.stepTimeBoundIff else k.timeBoundIff] ++ k.hypIffs do
        let st' ← saveState
        if let some (_, lhs, rhs, mk) ← lemmaImp L false then
          if let some (_, xr, _, r) := foldLe? rhs then
            if (← isDefEq lhs core) && (← isDefEq xr x) then
              found := some (← mk pcore, r)
              break
        st'.restore
      let some (pf, r) := found | st.restore; continue
      unless ← closePremises cx.avoid ms do st.restore; continue
      let pf ← normFold (← instantiateMVars pf)
      let some (Φp, _, _, _) := foldLe? (← whnfR (← instantiateMVars (← inferType pf)))
        | st.restore; continue
      unless ← isDefEq Φp Φ do st.restore; continue
      let some n := natOfCast? (← instantiateMVars r) | st.restore; continue
      let n ← instantiateMVars n
      if pf.hasExprMVar || n.hasExprMVar then st.restore; continue
      let mut inv : Option (Expr × Expr) := none
      if isAnd then
        let i ← instantiateMVars (body.getArg! 1)
        if let some ar := k.allRet then
          if i.getAppFn.isConstOf ar then
            inv ← invFold? k step allows x (← mkAppM ``And.right #[pc0])
      return some { bound := n, proof := pf, inv }
    catch _ => st.restore
  return none

/-- A bound of the charge `e`, free of the variables to avoid: the time `t.time` of a costed
tree of a kind with `FoldKind.timeLe`, by the fold rule on its image; else by `bfree?`. -/
def costBoundWith (foldOf : FoldCx → Expr → Expr → TermElabM FoldB) (cx : FoldCx) (e : Expr) :
    TermElabM (Expr × Expr) := do
  for k in ← foldKinds do
    let some L := k.timeLe | continue
    let st ← saveState
    try
      let cL ← mkConstWithFreshMVarLevels L
      let (ls, _, lt) ← forallMetaTelescopeReducing (← inferType cL)
      unless lt.isAppOfArity ``LE.le 4 do st.restore; continue
      let lhs := lt.getArg! 2
      if let some a := natOfCast? lhs then
        if ← isDefEq a e then
          let w := lt.getArg! 3
          if w.isAppOfArity ``PFunctor.FreeM.wpFold 6 then
            let pL ← instantiateMVars (mkAppN cL ls)
            let Φc := w.getArg! 3
            let some (c, allows, _) ← chargeOf? Φc | throwError "timeLe"
            let Φn ← mkAppOptM ``PFunctor.OpSpec.chargeUnder
              #[none, none, none, none, some (← chargeFn c), some allows]
            let r ← foldOf cx Φn (← instantiateMVars (w.getArg! 4))
            let pr ← denormFold Φc r.proof
            let pf ← mkAppM ``PFunctor.FreeM.natCast_le_of_le_trans #[pL, pr]
            return (r.bound, pf)
    catch _ => pure ()
    st.restore
  match ← bfree? cx.avoid e with
  | some r => return r
  | none => throwError "no bound of the charge{indentExpr e}\nfree of the values bound in the \
      program"


/-- The tick tree of the image `x` of a costed tree unfolded one step, when this exposes a node of
the free monad (`FreeM.pure` or `FreeM.liftBind`): the node equations of the image. -/
def unfoldImage? (x : Expr) : MetaM (Option Expr) := do
  let x' ← whnfD x
  if x'.isAppOfArity ``PFunctor.FreeM.pure 3 || x'.isAppOfArity ``PFunctor.FreeM.liftBind 4 then
    return some x'
  return none

/-- The tree `t` in weak head normal form when this exposes a constructor (a pair, or a node of
the tree type): the step of a recursive definition at a constructor of its argument. A bind of
the kind, a combinator with a law, an `if` and a `match` are kept. -/
def exposeTree (k : FoldKind) (t : Expr) : MetaM Expr := do
  if t.isAppOfArity ``ite 5 || t.isAppOfArity ``dite 5 then return t
  if (← matchMatcherApp? t).isSome then return t
  if let some n := t.getAppFn.constName? then
    if k.bind == some n then return t
    if (← getEnv).isConstructor n then return t
  let t' ← whnfD t
  if let some n := t'.getAppFn.constName? then
    if (← getEnv).isConstructor n then return t'
  return t

/-- The variables of the local context `l` that are not in `l₀`. -/
def newFVars (l₀ l : LocalContext) : Array FVarId :=
  l.foldl (init := #[]) fun acc d =>
    if l₀.contains d.fvarId || d.isImplementationDetail then acc else acc.push d.fvarId

/-! ## The leaf-length rule -/

/-- The bound of the value `l : ℕ` at a leaf, free of the variables `avoid`, with the proof of
`l ≤ b`: a numeral when `l` reduces to one (the length of a list literal), else `bfree?`. -/
def leafValueBound (avoid : Array FVarId) (l : Expr) : MetaM (Expr × Expr) := do
  let r ← withTransparency .default <| Meta.reduce l
  if let some n := r.nat? <|> r.rawNatLit? then
    let b := mkNatLit n
    return (b, ← mkExpectedTypeHint (mkApp (mkConst ``Nat.le_refl) b) (mkNatLe l b))
  match ← bfree? avoid l with
  | some r => return r
  | none => throwError "no bound of the leaf value{indentExpr l}\nfree of the values bound in \
      the program"

/-- The leaf invariant `ty = AllRet Q t` unfolded at a constructor of `t`: the definition of the
invariant applied once and its match reduced (`Q a` at a leaf, `∀ o, AllRet Q (k o)` at a node);
`none` when `t` exposes no constructor. -/
def unfoldAllRet? (ty : Expr) : MetaM (Option Expr) := do
  let some ty' ← withDefault (unfoldDefinition? ty) | return none
  let ty' ← whnfCore ty'.headBeta
  if ty'.isForall || (CatCrypt.Tactics.AutoTime.natLe? ty').isSome then return some ty'
  return none

/-- **The leaf-length rule.** A goal `AllRet (fun v => e v ≤ ?ℓ) t` of a kind `k` (its leaf
invariant `FoldKind.allRet`), proved by recursion over `t`: at a leaf `pure a` the bound of
`e a` (`leafValueBound`) is recorded with a delayed goal `b ≤ ?ℓ` in `leaves`; a node is the
invariant at every answer (an introduced variable); the tree `y.2` of a pair is the tree of the
pair `y` after its head is unfolded; a bind of the kind is the invariant of every continuation
(`FoldKind.allRetBind`); an `if`, an `if h :`
and a `match` (of trees or of pairs) are split; any other tree has its head unfolded. The bounds
avoid every variable introduced below `l₀`. -/
partial def leafLenGoal (k : FoldKind) (avoid : Array FVarId) (l₀ : LocalContext) (g : MVarId)
    (leaves : IO.Ref (Array (MVarId × Expr))) (fuel : Nat := 64) : TermElabM Unit := do
  if fuel == 0 then throwError "the leaf-length rule exhausted its depth"
  g.withContext do
  let ty ← whnfR (← instantiateMVars (← g.getType))
  if ty.isForall then
    let (_, g') ← g.intro1
    return ← leafLenGoal k avoid l₀ g' leaves (fuel - 1)
  if let some (l, r) := CatCrypt.Tactics.AutoTime.natLe? ty then
    let av := avoid ++ newFVars l₀ (← getLCtx)
    let (b, pf) ← leafValueBound av l
    if av.any b.containsFVar then
      throwError "the bound of the leaf value{indentExpr l}\nmentions a bound value"
    let d ← mkFreshExprSyntheticOpaqueMVar (mkNatLe b r)
    g.assign (← mkAppM ``Nat.le_trans #[pf, d])
    leaves.modify (·.push (d.mvarId!, b))
    return
  let some ar := k.allRet | throwError "the kind `{k.timed}` has no leaf invariant"
  unless ty.isAppOf ar && ty.getAppNumArgs ≥ 2 do
    throwError "the leaf-length rule reads no clause at{indentExpr ty}"
  if let some ty' ← unfoldAllRet? ty then
    return ← leafLenGoal k avoid l₀ (← g.replaceTargetDefEq ty') leaves (fuel - 1)
  let t := ty.appArg!
  let retarget (t' : Expr) : TermElabM Unit := do
    leafLenGoal k avoid l₀ (← g.replaceTargetDefEq (mkApp ty.appFn! t')) leaves (fuel - 1)
  let split (e : Expr) : TermElabM Bool := do
    if e.isAppOfArity ``ite 5 || e.isAppOfArity ``dite 5 then
      let some (s₁, s₂) ← splitIfTarget? g | return false
      for gi in [s₁.mvarId, s₂.mvarId] do leafLenGoal k avoid l₀ gi leaves (fuel - 1)
      return true
    if (← matchMatcherApp? e).isSome then
      for gi in ← Split.splitMatch g e do leafLenGoal k avoid l₀ gi leaves (fuel - 1)
      return true
    return false
  if ← split t then return
  if let some y := CatCrypt.Tactics.AutoTime.sndOf? t then
    let y' ← reduceHead y
    if y'.isAppOfArity ``Prod.mk 4 then return ← retarget (y'.getArg! 3)
    if let (some bnd, some ab) := (k.bind, k.allRetBind) then
      if y'.getAppFn.isConstOf bnd then
        let gs ← (← g.replaceTargetDefEq (mkApp ty.appFn! (← mkAppM ``Prod.snd #[y']))).apply
          (← mkConstWithFreshMVarLevels ab)
        for gi in gs do
          unless ← gi.isAssigned do leafLenGoal k avoid l₀ gi leaves (fuel - 1)
        return
    if ← split y' then return
    if y' != y then return ← retarget (← mkAppM ``Prod.snd #[y'])
  let t' ← exposeTree k (← reduceHead t)
  if t' != t then return ← retarget t'
  throwError "the leaf-length rule reads no clause at the tree{indentExpr t}"

/-- Whether `ty` is a leaf-length premise `∀ ys, AllRet (fun v => e v ≤ ?ℓ) t` of the kind `k`,
with `?ℓ` an unassigned metavariable; the metavariable. -/
def leafLenPremise? (k : FoldKind) (ty : Expr) : MetaM (Option MVarId) := do
  let some ar := k.allRet | return none
  forallTelescopeReducing ty fun _ body => do
    unless body.isAppOf ar && body.getAppNumArgs ≥ 2 do return none
    let Q := body.appFn!.appArg!
    let .lam _ _ qb _ := Q | return none
    let some (_, r) := CatCrypt.Tactics.AutoTime.natLe? qb | return none
    match ← instantiateMVars r with
    | .mvar m => return if ← m.isAssigned then none else some m
    | _ => return none

/-- The leaf-length rule at the premise `mid` (`leafLenPremise?`): `?ℓ` is the maximum of the
bounds of the leaves, each delayed goal closed by `maxChain`. -/
def closeLeafLen (k : FoldKind) (avoid : Array FVarId) (mid : MVarId) (ℓ : MVarId) :
    TermElabM Unit := do
  let leaves ← IO.mkRef #[]
  leafLenGoal k avoid (← mid.getDecl).lctx mid leaves
  let ls ← leaves.get
  let mut uniq : Array Expr := #[]
  for (_, b) in ls do
    unless uniq.contains b do uniq := uniq.push b
  let (M, ups) ← if uniq.isEmpty then pure (mkNatLit 0, #[]) else maxChain uniq
  unless ← isDefEq (mkMVar ℓ) M do throwError "the leaf-length rule: the bound"
  for (d, b) in ls do
    let some j := uniq.idxOf? b | throwError "the leaf-length rule: a leaf"
    d.assign ups[j]!

mutual

/-- **The fold rule.** The bound of the charge fold `wpFold Φ x (fun _ => 0)` of the program `x`,
`Φ = OpSpec.chargeUnder (fun a => ↑(c a)) allows`, by structural recursion over `x`; see the
module docstring for the clauses and the fragment they decide. -/
partial def foldBound (cx : FoldCx) (Φ x : Expr) (fuel : Nat := 256) : TermElabM FoldB := do
  if fuel == 0 then throwError "the fold rule exhausted its depth at{indentExpr x}"
  let mut x := (← instantiateMVars x).headBeta
  -- a composite `(f ∘ g) a` (the continuation of `FreeM.bind A (stepToFreeMT ∘ f)`) is `f (g a)`
  if x.isAppOfArity ``Function.comp 6 then
    x := mkApp (x.getArg! 3) (mkApp (x.getArg! 4) (x.getArg! 5)).headBeta
  if let some r ← factAt? cx Φ x then return r
  let some (c, allows, _) ← chargeOf? Φ
    | throwError "not a charge fold over the natural numbers{indentExpr Φ}"
  if let some (k, step, t) ← imageOf? x then
    return ← foldImage cx Φ c allows k step x t fuel
  let x' ← whnfR x
  if x' != x then
    if let some r ← factAt? cx Φ x' then return r
    if let some (k, step, t) ← imageOf? x' then
      return ← foldImage cx Φ c allows k step x' t.headBeta fuel
  if x'.isAppOfArity ``PFunctor.FreeM.pure 3 then
    let pf ← mkAppM ``PFunctor.FreeM.wpFold_chargeUnder_pure_le
      #[c, allows, x'.getArg! 2, mkNatLit 0]
    return { bound := mkNatLit 0, proof := pf }
  if x'.isAppOfArity ``PFunctor.FreeM.liftBind 4 then
    return ← foldNode cx Φ c allows (x'.getArg! 2) (x'.getArg! 3) fuel
  if x'.isAppOfArity ``PFunctor.FreeM.bind 5 then
    return ← foldBind cx Φ c allows x' fuel
  if x'.isAppOfArity ``ite 5 || x'.isAppOfArity ``dite 5 then
    return ← foldIf cx Φ x' fuel
  if (← matchMatcherApp? x').isSome then
    return ← foldMatch cx Φ x' x' fuel
  let x'' ← reduceHead x'
  if x'' != x' then return ← foldBound cx Φ x'' (fuel - 1)
  throwError "the fold rule reads no clause at the program{indentExpr x'}"

/-- The call clause: a call at `a` with continuation `r`. The charge `c a` is reduced
(`reduceCharge`) and bounded free of the values bound in the program (`costBound`); the
continuation is bounded at a fresh answer `b` under `allows a b` (dropped when it reduces to
`True`), and its bound must not mention `b`. A tick whose charge has a summand `y.1` and whose
continuation is the image of `y.2` is read as the image of the step-prefixed tree `y`
(`splitTick?`). -/
partial def foldNode (cx : FoldCx) (Φ c allows a r : Expr) (fuel : Nat) : TermElabM FoldB := do
  let ca ← reduceProjs (← reduceCharge (c.beta #[a]))
  if let some res ← splitTick? cx Φ c allows a r ca fuel then return res
  let (m, pc) ← costBoundWith (fun cx Φ x => foldBound cx Φ x (fuel - 1)) cx ca
  let rty ← whnf (← inferType r)
  let .forallE bn dom _ _ := rty | throwError "foldNode: continuation{indentExpr r}"
  withLocalDeclD bn (← whnf dom) fun b => do
    let al := (allows.beta #[a, b]).headBeta
    let red ← reduceAllows al
    let hty := red.getD al
    withLocalDeclD `hb hty fun hb => do
      let avoid := cx.avoid.push b.fvarId! |>.push hb.fvarId!
      let res ← foldBound { cx with avoid } Φ (r.beta #[b]).headBeta (fuel - 1)
      let n ← instantiateMVars res.bound
      if n.containsFVar b.fvarId! || n.containsFVar hb.fvarId! then
        throwError "the bound of the continuation of the call{indentExpr a}\nmentions its \
          answer:{indentExpr n}"
      let hr ← mkLambdaFVars #[b, hb] res.proof
      let pf ← mkAppM ``PFunctor.FreeM.wpFold_chargeUnder_liftBind_le
        #[c, allows, a, r, m, n, pc, hr]
      return { bound := mkAddN m n, proof := pf }

/-- The tick split at a call `a` whose continuation `r` ignores its answer: the equation
`hX : F (liftBind a r) = ↑(c a) + F body` (`wpFold_chargeUnder_liftBind_const` at an inhabitant
of the answers of `a`, allowed), then `splitWith?`. -/
partial def splitTick? (cx : FoldCx) (Φ c allows a r ca : Expr) (fuel : Nat) :
    TermElabM (Option FoldB) := do
  let .lam _ _ body _ := r | return none
  if body.hasLooseBVars then return none
  let some (k, false, _) ← imageOf? body | return none
  let st ← saveState
  try
    let rty ← whnf (← inferType r)
    let .forallE _ dom _ _ := rty | return none
    let dom ← whnf dom
    let some b0 ← (try some <$> mkDefault dom catch _ => pure none) | return none
    let p ← reduceCharge (allows.beta #[a, b0])
    unless p.isConstOf ``True do return none
    let fm ← whnfR (← inferType body)
    let (P, α) := (fm.getArg! 0, fm.getArg! 1)
    let post ← zeroPost body
    let hX ← mkAppOptM ``PFunctor.FreeM.wpFold_chargeUnder_liftBind_const
      #[some P, some α, none, none, none, some (← chargeFn c), some allows, some a, some b0,
        some (Lean.mkConst ``True.intro), some body, some post]
    splitWith? cx Φ k hX ca body fuel
  catch ex =>
    if ex.isInterrupt || ex.isRuntime then throw ex
    st.restore
    return none

/-- The tick split: from `hX : F X = ↑ca + F body` with `body` the image `toFreeMT y.2` of the
tree of a step-prefixed tree `y` and `ca = e + y.1`, the bound of `e` plus the bound of
`stepToFreeMT y` (`FoldKind.stepFold`). When moreover `y` is `A.bind f` with `A = S.2` and
`e = e₀ + S.1`, the bound of `e₀` plus the bound of `(stepToFreeMT S).bind (stepToFreeMT ∘ f)`
(`FoldKind.bindFold`), so that the step cost `S.1` of a callee and its tree are bounded together
by its time theorem. With the whole charge `y.1`, the split is made only when `y` is read
without unfolding its image (an `if`, a `match`, a bind of the kind or a pair). -/
partial def splitWith? (cx : FoldCx) (Φ : Expr) (k : FoldKind) (hX ca body : Expr)
    (fuel : Nat) : TermElabM (Option FoldB) := do
  let some (k', false, t) ← imageOf? body | return none
  unless k'.timed == k.timed do return none
  let some sf := k.stepFold | return none
  let t' ← reduceHead t
  let some y := CatCrypt.Tactics.AutoTime.sndOf? t' | return none
  -- the charge is in the normal form of `reduceProjs`, so `y` is matched in that form
  let some o := findFst ca (← reduceProjs y) | return none
  if ca == o then
    let y' ← reduceHead y
    let readable := y'.isAppOfArity ``ite 5 || y'.isAppOfArity ``dite 5 ||
      y'.isAppOfArity ``Prod.mk 4 || (← matchMatcherApp? y').isSome ||
      (k.bind.any fun b => y'.getAppFn.isConstOf b)
    unless readable do return none
  let e := ca.replace fun s => if s == o then some (mkNatLit 0) else none
  let post ← zeroPost body
  let st ← saveState
  try
    let hs ← eqAtAny (#[sf] ++ k.stepFolds)
      (← foldOf Φ (← mkAppM k.stepToFreeMT #[y]) post)
    if let (some bnd, some bf) := (k.bind, k.bindFold) then
      let y' ← reduceHead y
      if y'.getAppFn.isConstOf bnd && y'.getAppNumArgs ≥ 2 then
        let A := y'.getArg! (y'.getAppNumArgs - 2)
        if let some S := CatCrypt.Tactics.AutoTime.sndOf? (← reduceHead A) then
          if let some oS := findFst e (← reduceProjs S) then
            let e₀ := e.replace fun s => if s == oS then some (mkNatLit 0) else none
            let hc ← omegaEq ca (mkAddN (mkAddN e₀ oS) o)
            let (m, pe) ← costBoundWith (fun cx Φ x => foldBound cx Φ x (fuel - 1)) cx e₀
            let hsu ← eqAtAny (#[bf] ++ k.bindFolds)
              (← foldOf Φ (← mkAppM k.stepToFreeMT #[y']) post)
            let hsuTy ← instantiateMVars (← inferType hsu)
            let bindProg := (hsuTy.getArg! 2).getArg! 4
            let tS := bindProg.getArg! 3
            let g := bindProg.getArg! 4
            let stepS ← mkAppM k.stepToFreeMT #[S]
            let v ← mkAppM ``PFunctor.FreeM.bind #[stepS, g]
            let rv ← foldBound cx Φ v (fuel - 1)
            -- `F ((stepToFreeMT S).bind g) = ↑S.1 + F ((toFreeMT S.2).bind g)`
            let gFold ← withLocalDeclD `a (← inferType g).bindingDomain! fun a => do
              mkLambdaFVars #[a] (← foldOf Φ (g.beta #[a]) post)
            let e1 ← mkAppM ``PFunctor.FreeM.wpFold_bind' #[Φ, stepS, g, post]
            let e2 ← eqAtAny (#[sf] ++ k.stepFolds) (← foldOf Φ stepS gFold)
            let e3 ← mkEqSymm (← mkAppM ``PFunctor.FreeM.wpFold_bind' #[Φ, tS, g, post])
            let e2ty ← instantiateMVars (← inferType e2)
            let castS := (e2ty.getArg! 2).getArg! 4
            let hv ← mkEqTrans e1 (← mkEqTrans e2 (← mkCongrArg
              (← withLocalDeclD `z enatE fun z => do mkLambdaFVars #[z] (← mkAdd castS z)) e3))
            let pf ← mkAppM ``PFunctor.FreeM.enat_split₂_le #[hX, hs, hsu, hv, hc, pe, rv.proof]
            return some { bound := mkAddN m rv.bound, proof := pf }
    let hc ← omegaEq ca (mkAddN e o)
    let (m, pe) ← costBoundWith (fun cx Φ x => foldBound cx Φ x (fuel - 1)) cx e
    let ry ← foldBound cx Φ (← mkAppM k.stepToFreeMT #[y]) (fuel - 1)
    let pf ← mkAppM ``PFunctor.FreeM.enat_split_le #[hX, hs, hc, pe, ry.proof]
    return some { bound := mkAddN m ry.bound, proof := pf, inv := ry.inv }
  catch ex =>
    if ex.isInterrupt || ex.isRuntime then throw ex
    st.restore
    return none

/-- The step clause: the image `x = stepToFreeMT y` of a step-prefixed tree is bounded through
`FoldKind.stepFold`, `F x = ↑y.1 + F (toFreeMT y.2)`: by `splitWith?`, else by the bound of the
charge `y.1` plus the bound of `toFreeMT y.2`. -/
partial def foldStep (cx : FoldCx) (Φ : Expr) (k : FoldKind) (sf : Name) (x : Expr)
    (fuel : Nat) : TermElabM FoldB := do
  let post ← zeroPost x
  let hX ← eqAtAny (#[sf] ++ k.stepFolds) (← foldOf Φ x post)
  let hty ← instantiateMVars (← inferType hX)
  let rhs := hty.getArg! 2
  let some ca0 := natOfCast? (rhs.getArg! 4) | throwError "foldStep: {rhs}"
  let body := (rhs.getArg! 5).getArg! 4
  let ca ← reduceProjs (← reduceCharge ca0)
  if let some r ← splitWith? cx Φ k hX ca body fuel then return r
  let (m, pc) ← costBoundWith (fun cx Φ x => foldBound cx Φ x (fuel - 1)) cx ca
  let r ← foldBound cx Φ body (fuel - 1)
  let pf ← mkAppM ``PFunctor.FreeM.enat_eq_add_le #[hX, pc, r.proof]
  return { bound := mkAddN m r.bound, proof := pf }

/-- The bind clause: `x.bind f` is bounded by the bound of `x` plus the bound of `f a` at a fresh
return `a`, under the leaf invariant `Q a` of `x` when its bound carries one (taken apart by
`withInvHyps`); the bound of `f a` must not mention `a`. A bind whose first program is a node is
first reassociated (`FreeM.bind` on `pure` and `liftBind`). -/
partial def foldBind (cx : FoldCx) (Φ c allows x : Expr) (fuel : Nat) : TermElabM FoldB := do
  let x0 := x.getArg! 3
  let f := x.getArg! 4
  let leaf? : Option FoldB ← do
    if let some r ← factAt? cx Φ x0 then pure (some r)
    else match ← imageOf? x0 with
      | some (k, step, t) => do
        match ← calleeFold? cx k step Φ allows x0 t with
        | some r => pure (some r)
        | none => k.laws.findSomeM? fun L => lawFold? cx Φ x0 L fuel
      | none => pure none
  if leaf?.isNone then
    let mut x0' ← whnfR x0
    if (← imageOf? x0').isSome then
      if let some u ← unfoldImage? x0' then x0' := u
    if x0'.isAppOfArity ``PFunctor.FreeM.pure 3 then
      return ← foldBound cx Φ (f.beta #[x0'.getArg! 2]).headBeta (fuel - 1)
    if x0'.isAppOfArity ``PFunctor.FreeM.liftBind 4 then
      let x' ← whnfCore (← mkAppM ``PFunctor.FreeM.bind #[x0', f])
      return ← foldBound cx Φ x' (fuel - 1)
  let r0 ← match leaf? with
    | some r => pure r
    | none => foldBound cx Φ x0 (fuel - 1)
  let fty ← whnf (← inferType f)
  let .forallE an α _ _ := fty | throwError "foldBind: continuation{indentExpr f}"
  let (Q, hI) ← match r0.inv with
    | some p => pure p
    | none => do
      let Q ← withLocalDeclD an α fun a => mkLambdaFVars #[a] (mkConst ``True)
      pure (Q, ← mkAppM ``PFunctor.FreeM.wpFold_demonicUnder_true #[allows, x0])
  withLocalDeclD an α fun a => do
    let qa := (Q.beta #[a]).headBeta
    withLocalDeclD `ha qa fun ha => do
      withInvHyps ha qa fun lets => do
        let avoid := cx.avoid ++ #[a.fvarId!, ha.fvarId!] ++ lets.map (·.fvarId!)
        let r ← foldBound { cx with avoid } Φ (f.beta #[a]).headBeta (fuel - 1)
        let n ← instantiateMVars r.bound
        if n.containsFVar a.fvarId! || n.containsFVar ha.fvarId! ||
            lets.any fun l => n.containsFVar l.fvarId! then
          throwError "the bound of the continuation of a bind mentions the bound \
            value{indentExpr n}"
        let hf ← mkLambdaFVars (#[a, ha] ++ lets) r.proof
        let pf ← mkAppM ``PFunctor.FreeM.wpFold_chargeUnder_bind_le_add
          #[c, allows, x0, f, Q, r0.bound, n, r0.proof, hf, hI]
        return { bound := mkAddN r0.bound n, proof := pf }

/-- The `if` clause: an `if` or `if h :` decided by a hypothesis of the context (the answer
relation at a sampling node, `b ∈ μ.support`) is its branch; else the maximum of the bounds of
its branches, a branch of `if h :` bounded under its hypothesis and free of it. -/
partial def foldIf (cx : FoldCx) (Φ x : Expr) (fuel : Nat) : TermElabM FoldB := do
  let isD := x.isAppOfArity ``dite 5
  let (α, p, inst, t, e) := (x.getArg! 0, x.getArg! 1, x.getArg! 2, x.getArg! 3, x.getArg! 4)
  let post ← zeroPost x
  if let some (pos, h) ← decided? p then
    let lem := if isD then (if pos then ``dif_pos else ``dif_neg)
      else (if pos then ``if_pos else ``if_neg)
    let eq ← mkAppOptM lem #[some p, some inst, some h, some α, some t, some e]
    let x' := (← instantiateMVars (← inferType eq)).getArg! 2
    let r ← foldBound cx Φ x'.headBeta (fuel - 1)
    return ← transportFold Φ x eq r
  if !isD then
    let r1 ← foldBound cx Φ t (fuel - 1)
    let r2 ← foldBound cx Φ e (fuel - 1)
    let pf ← mkAppOptM ``PFunctor.FreeM.wpFold_ite_le_max_enat
      #[none, none, some Φ, some p, some inst, some t, some e, some post, none, none,
        some r1.proof, some r2.proof]
    return { bound := ← mkMaxN r1.bound r2.bound, proof := pf }
  let branch (ty br : Expr) : TermElabM (Expr × Expr) :=
    withLocalDeclD `h ty fun h => do
      let r ← foldBound { cx with avoid := cx.avoid.push h.fvarId! } Φ (br.beta #[h]).headBeta
        (fuel - 1)
      let b ← instantiateMVars r.bound
      if b.containsFVar h.fvarId! then throwError "the bound of a branch mentions its proof"
      return (b, ← mkLambdaFVars #[h] r.proof)
  let (m, pt) ← branch p t
  let (n, pe) ← branch (mkNot p) e
  let pf ← mkAppOptM ``PFunctor.FreeM.wpFold_dite_le_max_enat
    #[none, none, some Φ, some p, some inst, some t, some e, some post, none, none, some pt,
      some pe]
  return { bound := ← mkMaxN m n, proof := pf }

/-- The `match` clause: the goal `wpFold Φ x (fun _ => 0) ≤ ↑?B` is split on the match `me`
(`Split.splitMatch`); each alternative is bounded under its pattern variables, free of them, and
`?B` is the maximum of the bounds of the alternatives. -/
partial def foldMatch (cx : FoldCx) (Φ x me : Expr) (fuel : Nat) : TermElabM FoldB := do
  let B ← mkFreshExprMVar natE
  let g ← mkFreshExprSyntheticOpaqueMVar (← foldGoal Φ x B)
  let l₀ ← getLCtx
  let gs ← Split.splitMatch g.mvarId! me
  let mut rs : Array (MVarId × FoldB) := #[]
  for gi in gs do
    let r ← gi.withContext do
      let ty ← instantiateMVars (← gi.getType)
      let some (Φi, xi, _, _) := foldLe? ty | throwError "foldMatch: alternative{indentExpr ty}"
      let nv := newFVars l₀ (← getLCtx)
      let r ← foldBound { cx with avoid := cx.avoid ++ nv } Φi xi (fuel - 1)
      let n ← instantiateMVars r.bound
      if nv.any n.containsFVar then
        throwError "the bound of an alternative of a match mentions its pattern \
          variables{indentExpr n}"
      pure r
    rs := rs.push (gi, r)
  let (M, ups) ← maxChain (← rs.mapM fun (_, r) => instantiateMVars r.bound)
  unless ← isDefEq B M do throwError "foldMatch: bound"
  for h : i in [0:rs.size] do
    let (gi, r) := rs[i]'h.2.1
    gi.withContext do
      gi.assign (← mkAppM ``PFunctor.FreeM.wpFold_le_natCast_of_le #[r.proof, ups[i]!])
  return { bound := M, proof := ← instantiateMVars g }

/-- The clauses of an image `x` of a costed tree `t` of the kind `k` (`step`: the step-prefixed
image): the time theorem of a callee (`calleeFold?`); an `if` or `if h :` of trees, the image
pushed into its branches; a `match` of trees; a bind of the kind under the step-prefixed image,
by `FoldKind.bindFold`; a registered combinator law (`FoldKind.laws`); else the node equations
of the image. -/
partial def foldImage (cx : FoldCx) (Φ c allows : Expr) (k : FoldKind) (step : Bool)
    (x t : Expr) (fuel : Nat) : TermElabM FoldB := do
  let _ := c
  if let some r ← calleeFold? cx k step Φ allows x t then return r
  -- the tree reduced one step at a time (`whnfR`, else the unfolding of a non-recursive head
  -- definition), each form read by the clauses before the next is taken
  let mut t' := t
  for _ in [0:9] do
    let x' := mkApp x.appFn! t'
    if t' != t then
      if let some r ← factAt? cx Φ x' then return r
      if let some r ← calleeFold? cx k step Φ allows x' t' then return r
    if let some r ← imageClause? cx Φ k step x' t' fuel then return r
    let t1 ← CatCrypt.Tactics.AutoTime.whnfC t'
    let t2 ← if t1 != t' then pure t1 else
      pure ((← CatCrypt.Tactics.AutoTime.unfoldTree? t').getD t')
    if t2 == t' then break
    t' := t2
  let x' := mkApp x.appFn! t'
  let t'' ← exposeTree k t'
  if t'' != t' then return ← foldBound cx Φ (mkApp x.appFn! t'') (fuel - 1)
  if step then
    if let some sf := k.stepFold then return ← foldStep cx Φ k sf x' fuel
  if let some x'' ← unfoldImage? x' then return ← foldBound cx Φ x'' (fuel - 1)
  throwError "the fold rule reads no clause at the costed tree{indentExpr t'}"

/-- The clauses of the image `x` of the tree `t` in its present form: an `if` or `if h :` of
trees, the image pushed into its branches; a `match` of trees; the tree `y.2` of a
step-prefixed tree, below the bound of `stepToFreeMT y`; a bind of the kind under the
step-prefixed image (`FoldKind.bindFold`); a combinator law (`FoldKind.laws`). -/
partial def imageClause? (cx : FoldCx) (Φ : Expr) (k : FoldKind) (step : Bool) (x t : Expr)
    (fuel : Nat) : TermElabM (Option FoldB) := do
  if t.isAppOfArity ``ite 5 || t.isAppOfArity ``dite 5 then
    let lem := if t.isAppOfArity ``ite 5 then ``apply_ite else ``apply_dite
    let eq ← mkAppOptM lem #[none, none, some x.appFn!, some (t.getArg! 1), some (t.getArg! 2),
      some (t.getArg! 3), some (t.getArg! 4)]
    let x'' := (← instantiateMVars (← inferType eq)).getArg! 2
    let r ← foldBound cx Φ x'' (fuel - 1)
    return some (← transportFold Φ x eq r)
  if (← matchMatcherApp? t).isSome then
    return some (← foldMatch cx Φ x t fuel)
  if !step then
    if let (some y, some sf) := (CatCrypt.Tactics.AutoTime.sndOf? t, k.stepFold) then
      -- the projection of a pair (a literal, or a definition unfolding to one) is its field
      let isBind := k.bind.any fun b => y.getAppFn.isConstOf b
      let y' ← if isBind then pure y else exposeTree k (← reduceHead y)
      if y'.isAppOfArity ``Prod.mk 4 then
        return some (← foldBound cx Φ (mkApp x.appFn! (y'.getArg! 3)) (fuel - 1))
      let post ← zeroPost x
      let sy ← mkAppM k.stepToFreeMT #[y]
      let hs ← eqAtAny (#[sf] ++ k.stepFolds) (← foldOf Φ sy post)
      let r ← foldBound cx Φ sy (fuel - 1)
      let pf ← mkAppM ``PFunctor.FreeM.enat_le_of_add_eq #[hs, r.proof]
      return some { bound := r.bound, proof := pf }
  if step then
    if let (some bnd, some bf) := (k.bind, k.bindFold) then
      if t.getAppFn.isConstOf bnd && t.getAppNumArgs ≥ 2 then
        let post ← zeroPost x
        let eq ← eqAtAny (#[bf] ++ k.bindFolds) (← foldOf Φ x post)
        let eqTy ← instantiateMVars (← inferType eq)
        let r ← foldBound cx Φ ((eqTy.getArg! 2).getArg! 4) (fuel - 1)
        return some { bound := r.bound, proof := ← mkAppM ``Eq.trans_le #[eq, r.proof] }
  for L in k.laws do
    if let some r ← lawFold? cx Φ x L fuel then return some r
  return none

/-- A combinator law `L`: a theorem concluding `wpFold Φ' x' (fun _ => 0) ≤ ↑B`, or that bound
and a leaf invariant `AllRet Q t` (`FoldKind.allRet`, the leaf invariant of the result), whose
program unifies with `x`; each premise that bounds a charge fold (under binders) is proved by the
fold rule at its own charge (a component law of a vector charge bounds one component from
others), its bound assigned to the metavariable of the premise; a leaf-length premise
`∀ ys, AllRet (fun v => e v ≤ ?ℓ) t` is proved by the leaf-length rule (`closeLeafLen`); the
other premises are closed by `closePremises`. -/
partial def lawFold? (cx : FoldCx) (Φ x : Expr) (L : Name) (fuel : Nat) :
    TermElabM (Option FoldB) := do
  let st ← saveState
  try
    let cL ← mkConstWithFreshMVarLevels L
    let (ms, _, concl) ← forallMetaTelescopeReducing (← inferType cL)
    let concl ← whnfR concl
    let isAnd := concl.isAppOfArity ``And 2
    let core := if isAnd then concl.getArg! 0 else concl
    let some (Φl, xl, _, r) := foldLe? core | st.restore; return none
    -- a law of a combinator applies only at an application of that combinator
    if xl.getAppNumArgs > 0 && x.getAppNumArgs > 0 then
      if let (some cl, some cx') := (xl.appArg!.getAppFn.constName?,
          (← whnfR x.appArg!).getAppFn.constName?) then
        if cl != cx' && !(← getEnv).isConstructor cl then st.restore; return none
    unless ← isDefEq xl x do st.restore; return none
    unless ← isDefEq (← normSpec Φl) Φ do st.restore; return none
    for m in ms do
      let mid := m.mvarId!
      if ← mid.isAssigned then continue
      let ty ← instantiateMVars (← mid.getType)
      unless ← isProp ty do continue
      forallTelescopeReducing ty fun ys body => do
        let some (Φp, xp, _, rp) := foldLe? body | return
        let some np := natOfCast? rp | return
        let rr ← foldBound { cx with avoid := cx.avoid ++ ys.map (·.fvarId!) } (← normSpec Φp)
          xp (fuel - 1)
        unless ← isDefEq np rr.bound do
          throwError "the bound of an argument of a combinator mentions its binders"
        mid.assign (← mkLambdaFVars ys (← denormFold Φp rr.proof))
    let img? ← imageOf? x
    if let some (k, _, _) := img? then
      for m in ms do
        let mid := m.mvarId!
        if ← mid.isAssigned then continue
        let ty ← instantiateMVars (← mid.getType)
        unless ← isProp ty do continue
        if let some ℓ ← leafLenPremise? k ty then closeLeafLen k cx.avoid mid ℓ
    unless ← closePremises cx.avoid ms do st.restore; return none
    let pc ← instantiateMVars (mkAppN cL ms)
    let pf ← normFold (← if isAnd then mkAppM ``And.left #[pc] else pure pc)
    let some n := natOfCast? (← instantiateMVars r) | st.restore; return none
    let n ← instantiateMVars n
    if pf.hasExprMVar || n.hasExprMVar then st.restore; return none
    let mut inv : Option (Expr × Expr) := none
    if isAnd then
      if let (some (k, step, _), some (_, allows, _)) := (img?, ← chargeOf? Φ) then
        let i ← instantiateMVars (concl.getArg! 1)
        if let some ar := k.allRet then
          if i.getAppFn.isConstOf ar then
            inv ← invFold? k step allows x (← mkAppM ``And.right #[pc])
    return some { bound := n, proof := pf, inv }
  catch ex =>
    if ex.isInterrupt || ex.isRuntime then throw ex
    st.restore
    return none

end

/-- The fold facts of the local context: its propositions read by `toFoldFact?`. -/
def contextFacts : MetaM (Array Expr) := do
  let mut out := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    unless ← isProp d.type do continue
    out := out ++ (← toFoldFacts d.toExpr)
  return out

/-- The functions of the local context bounded by a hypothesis `∀ ys, f ys ≤ t` over `ℕ`: the
cost companions of a goal, eliminated from the bounds of the fold rule. -/
def boundedFns : MetaM (Array FVarId) := do
  let mut out := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    unless ← isProp d.type do continue
    let f? ← forallTelescopeReducing d.type fun ys body => do
      let some (l, _) := CatCrypt.Tactics.AutoTime.natLe? body | return none
      if ys.isEmpty then return none
      let .fvar f := l.getAppFn | return none
      return some f
    if let some f := f? then
      unless out.contains f do out := out.push f
  return out

/-- A goal read as a bound on a charge fold: the program `x`, the reading `Φ` (normalised by
`normSpec`), the bound `B : ℕ∞` of the goal, and the map from a proof of
`wpFold Φ x (fun _ => 0) ≤ B` to a proof of the goal. The goal is a bound on a charge fold, or
the left side of a registered equivalence (`FoldKind.timeBoundIff`, `FoldKind.stepTimeBoundIff`)
or the conclusion of a registered implication (`FoldKind.hypIffs`) from such a bound. -/
structure FoldGoal where
  /-- The reading. -/
  spec : Expr
  /-- The program. -/
  prog : Expr
  /-- The bound of the goal, in `ℕ∞`. -/
  rhs : Expr
  /-- The proof of the goal from a proof of the bound. -/
  close : Expr → MetaM Expr

/-- The goal `tgt` read as a bound on a charge fold; see `FoldGoal`. -/
def readGoal (tgt : Expr) : MetaM (Option FoldGoal) := do
  let tgt ← instantiateMVars tgt
  if let some (Φ, x, _, r) := foldLe? (← whnfR tgt) then
    if (← chargeOf? Φ).isSome then
      return some { spec := ← normSpec Φ, prog := x, rhs := r, close := denormFold Φ }
  for k in ← foldKinds do
    for L in #[k.timeBoundIff, k.stepTimeBoundIff] ++ k.concls do
      let st ← saveState
      try
        let isConcl := k.concls.contains L
        if let some (_, prem, concl, mk) ← lemmaImp L (rev := !isConcl) then
          if let some (Φ, x, _, r) := foldLe? prem then
            if (← chargeOf? Φ).isSome then
              if ← isDefEq concl tgt then
                let x ← instantiateMVars x
                let r ← instantiateMVars r
                let Φ ← instantiateMVars Φ
                unless x.hasExprMVar || r.hasExprMVar do
                  let close (pf : Expr) : MetaM Expr := do mk (← denormFold Φ pf)
                  return some { spec := ← normSpec Φ, prog := x, rhs := r, close }
      catch _ => pure ()
      st.restore
  return none

/-- The proof of `wpFold Φ x (fun _ => 0) ≤ rhs` from the bound `r` of the fold rule: through
`B₀ ≤ n` (`arithLe`) when `rhs` is the cast of `n`, else by `norm_cast` and `omega`. -/
def closeRhs (r : FoldB) (rhs : Expr) : TermElabM Expr := do
  let B₀ ← instantiateMVars r.bound
  if let some n := natOfCast? rhs then
    let le ← try arithLe B₀ n
      catch _ => throwError "the computed bound{indentExpr B₀}\nis not below the stated \
        bound{indentExpr n}"
    return ← mkAppM ``PFunctor.FreeM.wpFold_le_natCast_of_le #[r.proof, le]
  let mv ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``LE.le #[← enatCast B₀, rhs])
  let gs ← try Tactic.run mv.mvarId! (Tactic.evalTactic
      (← `(tactic| first | (norm_cast; omega) | (norm_num) | (simp; omega))))
    catch _ => pure [mv.mvarId!]
  unless gs.isEmpty do
    throwError "the computed bound{indentExpr B₀}\nis not below the stated bound{indentExpr rhs}"
  mkAppM ``le_trans #[r.proof, ← instantiateMVars mv]

/-- `time_fold` proves a goal `wpFold Φ x (fun _ => 0) ≤ B` with
`Φ = OpSpec.chargeUnder (fun a => ↑(c a)) allows` or `Φ = OpSpec.charge (fun a => ↑(c a))` over a
program `x` of a free monad (written in `FreeM` or the image of a costed tree), or a time-bound
goal of a registered kind (`register_time_fold`), by the fold rule (`foldBound`): the bound
`B₀` computed clause by clause from the structure of `x`, the hypotheses of the context read as
fold bounds and the time theorems of callees, followed by `B₀ ≤ B` over `ℕ`. -/
syntax (name := timeFoldStx) "time_fold" : tactic

@[tactic timeFoldStx] def evalTimeFold : Tactic.Tactic := fun _ => do
  let g ← Tactic.getMainGoal
  let rest := (← Tactic.getGoals).tail
  g.withContext do
    let some fg ← readGoal (← g.getType)
      | throwError "time_fold: the goal is neither a bound on a charge fold nor a registered \
          time bound{indentExpr (← g.getType)}"
    let cx : FoldCx := { facts := ← contextFacts, avoid := ← boundedFns }
    let r ← foldBound cx fg.spec fg.prog
    let pf ← fg.close (← closeRhs r fg.rhs)
    let pf ← instantiateMVars pf
    if pf.hasSyntheticSorry then throwError "time_fold: the proof is incomplete"
    g.assign pf
  Tactic.setGoals rest

/-- The record of the costed tree `c` (a definition returning `ℕ × T` with `T` of a registered
kind other than `SPTree.Timed`). -/
def foldKindOfTimed? (c : Name) : MetaM (Option FoldKind) := do
  match ← kindOfType? (← getConstInfo c).type with
  | some (k, true) => return some k
  | _ => return none

/-- The file named by the environment variable `CATCRYPT_FOLD_REPORT`, to which
`derive_time_bound` appends a line for each time theorem of a costed `SPTree` proved by the
fallback (`emitTimeBound` or `mirrorTimeBound`) with the reason of the fold rule. -/
def reportFallback (name : Name) (why : MessageData) : TermElabM Unit := do
  let some path ← IO.getEnv "CATCRYPT_FOLD_REPORT" | return
  let w ← why.toString
  let line := s!"{name}\t{(w.replace "\n" " ").take 300}\n"
  let h ← IO.FS.Handle.mk path .append
  h.putStr line

/-- State and prove `name`, the time theorem of the costed tree `c` of the registered kind `k`:
the left side of `k.stepTimeBoundIff` at `c xs` and the bound `B` computed by the fold rule
(`foldBound`) on the step-prefixed image of `c xs`, every binder tree of a registered kind with
its time-bound hypothesis read as a fold fact (`toFoldFact?`) and every cost companion with its
bound (`withBounds`); `B` is normalised (`normalizeSum`) when `arithLe` proves the normalised
bound above the computed one. Returns the reason when the bound is not computed or the proof is
not accepted. -/
def emitFoldTimeBound (k : FoldKind) (c name : Name) : TermElabM (Option MessageData) := do
  let info ← getConstInfo c
  let lvls := info.levelParams.map mkLevelParam
  forallTelescope info.type fun xs _ => do
    withBounds xs 0 #[] #[] #[] (oadv := true) fun bs vars hyps => do
      let mut facts := #[]
      for h in hyps do
        facts := facts ++ (← toFoldFacts h)
      let avoid := bs.filterMap fun (f, _, r) => match r with
        | .cost => some f
        | _ => none
      let x := mkAppN (Lean.mkConst c lvls) xs
      let Bm ← mkFreshExprMVar natE
      let (goal, rhs, close) ← try iffAt k.stepTimeBoundIff x Bm
        catch e => return some e.toMessageData
      let some (Φ, xr, _, _) := foldLe? rhs | return some m!"`{k.stepTimeBoundIff}`: the fold"
      let r ← try foldBound { facts, avoid } (← normSpec Φ) xr
        catch e => return some m!"no bound: {e.toMessageData}"
      let B ← instantiateMVars r.bound
      let Bn ← normalizeSum B
      let mut bound := B
      let mut pf0 := r.proof
      if Bn != B then
        try
          let le ← arithLe B Bn
          pf0 ← mkAppM ``PFunctor.FreeM.wpFold_le_natCast_of_le #[pf0, le]
          bound := Bn
        catch _ => pure ()
      unless ← isDefEq Bm bound do return some m!"the bound"
      let pf ← instantiateMVars (← close (← denormFold Φ pf0))
      if pf.hasSorry || pf.hasExprMVar then return some m!"the proof is incomplete"
      let goal ← instantiateMVars goal
      let ty ← mkForallFVars (xs ++ vars ++ hyps) goal
      let val ← mkLambdaFVars (xs ++ vars ++ hyps) pf
      try
        addDecl (Declaration.thmDecl
          { name, levelParams := info.levelParams, type := ty, value := val })
      catch e => return some m!"the proof is not accepted: {e.toMessageData}"
      return none

/-- The bound `B` of the fold rule on the program `x` at the charge reading `Φ`, normalised
(`normalizeSum`) when `arithLe` proves the normalised bound above it, with the proof of
`wpFold Φ x (fun _ => 0) ≤ ↑B` over `Φ` itself. -/
def foldNormalized (cx : FoldCx) (Φ x : Expr) : TermElabM (Expr × Expr) := do
  let r ← foldBound cx (← normSpec Φ) x
  let B ← instantiateMVars r.bound
  let Bn ← normalizeSum B
  let mut bound := B
  let mut pf := r.proof
  if Bn != B then
    try
      let le ← arithLe B Bn
      pf ← mkAppM ``PFunctor.FreeM.wpFold_le_natCast_of_le #[pf, le]
      bound := Bn
    catch _ => pure ()
  return (bound, ← denormFold Φ pf)

/-- State and prove `name`, the time theorem with query count of the costed tree `c` of the kind
`k` with a vector charge: every binder tree of a kind with a vector charge has a use bound
(`withBounds` with `vec`), read as one fold fact per component (`toFoldFacts`); the use bound
of the step-prefixed image of `c xs` is the join `FoldKind.useJoin` of its component folds, each
bounded by the fold rule at its own charge, and the theorem is the right side of
`FoldKind.useStepIff` at the joined bounds (the time bound and the query count of an oracle
program). Returns the reason when the theorem is not proved. -/
def emitUseTimeBound (k : FoldKind) (c name : Name) : TermElabM (Option MessageData) := do
  let (some J, some U) := (k.useJoin, k.useStepIff)
    | return some m!"the kind `{k.timed}` has no vector charge"
  let info ← getConstInfo c
  let lvls := info.levelParams.map mkLevelParam
  forallTelescope info.type fun xs _ => do
    withBounds xs 0 #[] #[] #[] (oadv := true) (vec := true) fun bs vars hyps => do
      let mut facts := #[]
      for h in hyps do
        facts := facts ++ (← toFoldFacts h)
      let avoid := bs.filterMap fun (f, _, r) => match r with
        | .cost => some f
        | _ => none
      let x := mkAppN (Lean.mkConst c lvls) xs
      let img ← mkAppM k.stepToFreeMT #[x]
      let (ms, cJ, _) ← try useJoinAt J img catch e => return some e.toMessageData
      for m in ms do
        let mid := m.mvarId!
        if ← mid.isAssigned then continue
        let ty ← instantiateMVars (← mid.getType)
        unless ← isProp ty do continue
        let some (Φp, xp, _, rp) := foldLe? ty | return some m!"`{J}`: the premise{indentExpr ty}"
        let some np := natOfCast? rp | return some m!"`{J}`: the bound of{indentExpr ty}"
        let (b, pf) ← try foldNormalized { facts, avoid } Φp xp
          catch e => return some m!"no bound of the component{indentExpr Φp}\n{e.toMessageData}"
        unless ← isDefEq np b do return some m!"the bound of a component"
        mid.assign pf
      let pj ← instantiateMVars (mkAppN cJ ms)
      if pj.hasExprMVar then return some m!"the use bound is not determined"
      let cU ← mkConstWithFreshMVarLevels U
      let (us, _, ut) ← forallMetaTelescope (← inferType cU)
      unless ut.isAppOfArity ``Iff 2 do return some m!"`{U}` is not an equivalence"
      unless ← isDefEq (ut.getArg! 0) (← inferType pj) do
        return some m!"`{U}` does not read the use bound{indentExpr (← inferType pj)}"
      let goal ← instantiateMVars (ut.getArg! 1)
      let pf ← instantiateMVars (← mkAppM ``Iff.mp #[mkAppN cU us, pj])
      if pf.hasSorry || pf.hasExprMVar || goal.hasExprMVar then
        return some m!"the proof is incomplete"
      let ty ← mkForallFVars (xs ++ vars ++ hyps) goal
      let val ← mkLambdaFVars (xs ++ vars ++ hyps) pf
      try
        addDecl (Declaration.thmDecl
          { name, levelParams := info.levelParams, type := ty, value := val })
      catch e => return some m!"the proof is not accepted: {e.toMessageData}"
      return none

/-- State and prove `name`, the time theorem `stepTime (c xs) ≤ B` of a costed `SPTree`, by the
fold rule: `B` is the bound of `boundStep` (the statement of `emitTimeBound`), and the bound of
the fold rule on the charge fold of `stepToFreeMT (c xs)` with every answer allowed is proved
below it by `arithLe`; `SPTree.Timed.stepTime_le_of_wpFold_le` concludes. A binder tree has the
hypothesis `(A x).time ≤ T_A`, which bounds no charge fold (a sampling node with an unbounded
family of continuation times has time `0`), so a tree with a binder tree is refused. Returns
the reason when the theorem is not proved. -/
def foldSPTreeTimeBound (c name : Name) : TermElabM (Option MessageData) := do
  let info ← getConstInfo c
  let lvls := info.levelParams.map mkLevelParam
  forallTelescope info.type fun xs body => do
    unless (← whnfR body).isAppOfArity ``Prod 2 do
      return some m!"`{c}` is not a step-prefixed tree"
    withBounds xs 0 #[] #[] #[] fun bs vars hyps => do
      if bs.any fun (_, _, r) => match r with | .tree | .key => true | _ => false then
        return some m!"a binder tree has the hypothesis `time ≤ T`, which bounds no charge fold"
      let avoid := bs.filterMap fun (f, _, r) => match r with
        | .cost => some f
        | _ => none
      let x := mkAppN (Lean.mkConst c lvls) xs
      let bound ← try normalizeSum (← instantiateMVars (← boundStep bs x))
        catch e => return some m!"no bound: {e.toMessageData}"
      let img ← mkAppM ``SPTree.Timed.stepToFreeMT #[x]
      let Φ ← mkAppM ``PFunctor.OpSpec.charge
        #[← chargeFn (← withLocalDeclD `a (← mkAppM ``PFunctor.A
          #[mkConst ``SPTree.SPSigT]) fun a => do
            mkLambdaFVars #[a] (← mkAppM ``SPTree.tickCost #[a]))]
      let r ← try foldBound { avoid } (← normSpec Φ) img
        catch e => return some m!"{e.toMessageData}"
      let le ← try arithLe (← instantiateMVars r.bound) bound
        catch _ => return some m!"the bound of the fold rule{indentExpr r.bound}\nis not \
          below{indentExpr bound}"
      let pf ← mkAppM ``PFunctor.FreeM.wpFold_le_natCast_of_le #[r.proof, le]
      let pf ← mkAppM ``SPTree.Timed.stepTime_le_of_wpFold_le #[x, bound, ← denormFold Φ pf]
      let pf ← instantiateMVars pf
      if pf.hasSorry || pf.hasExprMVar then return some m!"the proof is incomplete"
      let goal ← mkAppM ``LE.le #[← mkAppM ``SPTree.Timed.stepTime #[x], bound]
      let ty ← mkForallFVars (xs ++ vars ++ hyps) goal
      let val ← mkLambdaFVars (xs ++ vars ++ hyps) pf
      try
        addDecl (Declaration.thmDecl
          { name, levelParams := info.levelParams, type := ty, value := val })
      catch e => return some m!"the proof is not accepted: {e.toMessageData}"
      return none

/-- Whether the costed tree `c` returns a step-prefixed costed oracle adversary: the record of
its codomain (`foldKindOfTimed?`) is that of `OracleAdv.Timed`. -/
def isOracleTimed (c : Name) : MetaM Bool := do
  return (← foldKindOfTimed? c).any (·.timed == ``CatCrypt.Crypto.OracleAdv.Timed)

/-- `derive_time_bound R.tree` states and proves `R.tree.timeBound_timed`, the time theorem of
`R.tree.timed` (see the module docstring): by the fold rule for a costed tree of a registered
kind (`emitFoldTimeBound`), and for a kind with a vector charge, when that fails or with
`+queries`, with the query count beside the time (`emitUseTimeBound`); for a costed `SPTree`
by the fold rule first (`foldSPTreeTimeBound`), else along its bound for a pure step body (`mirrorTimeBound`), else by
`time_bound` (`emitTimeBound`); it fails with the reasons when the theorem is not proved. -/
syntax (name := deriveTimeBoundCmd) "derive_time_bound " ("+queries ")? ident : command

@[command_elab deriveTimeBoundCmd]
def elabDeriveTimeBound : CommandElab := fun stx => do
  liftTermElabM do
    let queries := !stx[1].isNone
    let t ← realizeGlobalConstNoOverloadWithInfo stx[2]
    let name := t ++ `timeBound_timed
    if let some k ← foldKindOfTimed? (t ++ `timed) then
      if queries then
        if let some why ← emitUseTimeBound k (t ++ `timed) name then
          throwError "`{name}` is not proved: {why}"
        return
      let s ← saveState
      let some why ← emitFoldTimeBound k (t ++ `timed) name | return
      if k.useJoin.isSome then
        s.restore
        let some whyU ← emitUseTimeBound k (t ++ `timed) name | return
        throwError "`{name}` is not proved: {why}\nwith the query counts: {whyU}"
      throwError "`{name}` is not proved: {why}"
    let s ← saveState
    let whyF? ← try foldSPTreeTimeBound (t ++ `timed) name
      catch e => do
        if e.isInterrupt then throw e
        pure (some e.toMessageData)
    let some whyF := whyF? | return
    s.restore
    let r ← mirrorTimeBound (t ++ `timed) name
    if let .proved := r then
      reportFallback name whyF
      return
    if let some why ← emitTimeBound (t ++ `timed) name then
      if let .refused w := r then
        throwError "`{name}` is not proved: {why}\nalong the bound of the pure step: {w}\n\
          by the fold rule: {whyF}"
      throwError "`{name}` is not proved: {why}\nby the fold rule: {whyF}"
    reportFallback name whyF

end

end CatCrypt.Tactics.DeriveTimeBound
