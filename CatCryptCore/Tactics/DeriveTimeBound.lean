/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.AutoTime
public import CatCryptCore.Tactics.DeriveReduction

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

## Costed oracle adversaries

A costed tree `R.tree.timed` returning a step-prefixed costed oracle adversary
`ℕ × OracleAdv.Timed D R α` gets the theorem `StepTimeBound (R.tree.timed xs) B`, stated and
proved together by a recursion over the structure of the adversary (`oaStep`, `oaTree`); every
binder into costed oracle adversaries `A : X → OracleAdv.Timed D R β` gets a bound `T_A` and the
hypothesis `∀ x, (A x).TimeBound T_A`, and every cost companion its bound as above. Each node
yields its bound and the proof by one rule lemma (`oa_*`):

* a pair `(c, t)`: the bound of `c` plus the bound of `t` (`oa_stb_pair`); a pair
  `(c + y.1, y.2)` or `delay c y`: the bound of `c` plus the bound of `y` (`oa_stb_pair_snd`,
  `oa_stb_delay`);
* a `rand` or `query` node: one plus the bound of its step-prefixed continuation at a fresh
  value (`oa_tb_rand`, `oa_tb_query`); a leaf: zero; a bounded binder: its bound;
* a bind `A.bind f`: the bound of `A` plus the bound of `f` at a fresh value (`oa_stb_bind`,
  `OracleAdv.Timed.timeBound_bind_of_allRet`); a pair `(c + S.1 + (S.2.bind f).1,
  (S.2.bind f).2)`, the adversary `S` followed by `f`, by the bound of `c`, of `S` and of `f`
  (`oa_stb_pair_bind`), each step cost read once. When the bound of `A` (or `S`) comes from a
  time theorem whose conclusion carries a leaf invariant `AllRet Q`, the continuation is bounded
  under `Q a`, its conjuncts and the bounds of its unfolded definitions local hypotheses
  (`withInvHyps`): the cost companions of a state returned by a fold are bounded by the
  invariant of the fold;
* an `if` or `if h :`: the maximum of the bounds of its branches (`oa_stb_ite`, `oa_stb_dite`,
  `oa_tb_ite`);
* a call that no rule reads (a recursive callee, a fold): the bound of the time theorem of the
  callee (`oaCallee?`), `StepTimeBound x B`, `x.TimeBound B`, or either in conjunction with a
  leaf invariant. Its premises are closed by `closePremises`: a premise whose leaves (its
  conjuncts, definitions unfolded) are bounds `∀ ys, l ≤ ?M` at a free `?M` (a bound shared by
  several cost companions, the bound of the cost companions of a state passed to the callee)
  has `?M` assigned the maximum of the bounds of its leaves; any other premise is closed from
  the context.

A step cost is bounded free of the cost companions and of the values bound inside the
adversary by `bfree?`, the clauses of `AutoTime.boundFree?` with a dependent `if` bounded by the
maximum of its branches (`dite_le_max_of`) and the premise of a registered cost lemma
`f.timedCost_le` (the step cost of a loop) closed by the same procedure. The bound is
normalised by `normalizeSum` when `omega`, alone or after `ring_nf`, proves the normalised bound
above it.

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
* `oaStep`, `oaTree` — the bound of a costed oracle adversary with its proof
* `closePremises` — the premises of the time theorem of a callee, bound families by maxima
* `emitOracleTimeBound` — the procedure for a costed oracle adversary
* `derive_time_bound R.tree` — the command
-/

public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveTimeBound

/-! ## Rule lemmas of the bound of a costed oracle adversary -/

section OracleRules

open CatCrypt.Crypto.OracleAdv.Timed

variable {D R α β : Type}

/-- A `dite` over `ℕ` is at most the maximum of the bounds of its branches. -/
theorem dite_le_max_of {c : Prop} [Decidable c] {t : c → ℕ} {f : ¬c → ℕ} {a b : ℕ}
    (ht : ∀ h, t h ≤ a) (hf : ∀ h, f h ≤ b) : dite c t f ≤ max a b := by
  by_cases h : c
  · rw [dite_eq_left h]
    exact le_max_of_le_left (ht h)
  · rw [dite_eq_right h]
    exact le_max_of_le_right (hf h)

/-- Every leaf of a costed oracle adversary satisfies the trivial predicate. -/
theorem oa_allRet_true (A : CatCrypt.Crypto.OracleAdv.Timed D R α) :
    AllRet (fun _ => True) A := by
  induction A with
  | ret a => trivial
  | rand p c k ih => exact ih
  | query d c k ih => exact ih

/-- A leaf takes no time. -/
theorem oa_tb_ret (a : α) (n : ℕ) :
    (CatCrypt.Crypto.OracleAdv.Timed.ret a : CatCrypt.Crypto.OracleAdv.Timed D R α).TimeBound n :=
  trivial

/-- A sample node costs one unit and the bound of its step-prefixed continuations. -/
theorem oa_tb_rand {γ : Type} {p : PMF γ} {c : γ → ℕ}
    {k : γ → CatCrypt.Crypto.OracleAdv.Timed D R α} {n : ℕ}
    (h : ∀ b, StepTimeBound (c b, k b) n) :
    (CatCrypt.Crypto.OracleAdv.Timed.rand p c k).TimeBound (1 + n) :=
  (timeBound_rand_iff p c k (1 + n)).2 ⟨by omega, fun b => by
    rw [Nat.add_sub_cancel_left]
    exact h b⟩

/-- A query node costs one unit and the bound of its step-prefixed continuations. -/
theorem oa_tb_query {d : D} {c : R → ℕ} {k : R → CatCrypt.Crypto.OracleAdv.Timed D R α}
    {n : ℕ} (h : ∀ r, StepTimeBound (c r, k r) n) :
    (CatCrypt.Crypto.OracleAdv.Timed.query d c k).TimeBound (1 + n) :=
  (timeBound_query_iff d c k (1 + n)).2 ⟨by omega, fun r => by
    rw [Nat.add_sub_cancel_left]
    exact h r⟩

/-- A pair `(c, t)` is bounded by a bound of `c` plus a bound of `t`. -/
theorem oa_stb_pair {c m n : ℕ} {t : CatCrypt.Crypto.OracleAdv.Timed D R α} (hc : c ≤ m)
    (ht : t.TimeBound n) : StepTimeBound (c, t) (m + n) :=
  ⟨by omega, ht.mono (by omega)⟩

/-- A pair `(c + y.1, y.2)`, the step-prefixed tree `y` after `c`. -/
theorem oa_stb_pair_snd {e c m n : ℕ} {y : ℕ × CatCrypt.Crypto.OracleAdv.Timed D R α}
    (he : e = c + y.1) (hc : c ≤ m) (hy : StepTimeBound y n) :
    StepTimeBound (e, y.2) (m + n) := by
  obtain ⟨h1, h2⟩ := hy
  subst he
  exact ⟨by omega, h2.mono (by omega)⟩

/-- A pair `(c + S.1 + (S.2.bind f).1, (S.2.bind f).2)`: the step-prefixed tree `S` followed
by `f`, after `c`, with `f` bounded at the leaves of `S.2` that satisfy `Q`. -/
theorem oa_stb_pair_bind {e c k m n : ℕ} {S : ℕ × CatCrypt.Crypto.OracleAdv.Timed D R α}
    {f : α → ℕ × CatCrypt.Crypto.OracleAdv.Timed D R β} {Q : α → Prop}
    (he : e = c + S.1 + (S.2.bind f).1) (hc : c ≤ k) (hS : StepTimeBound S m)
    (hQ : AllRet Q S.2) (hf : ∀ a, Q a → StepTimeBound (f a) n) :
    StepTimeBound (e, (S.2.bind f).2) (k + (m + n)) := by
  obtain ⟨h1, h2⟩ := timeBound_bind_of_allRet hS.2 hQ hf
  have := hS.1
  subst he
  exact ⟨by omega, h2.mono (by omega)⟩

/-- A bind is bounded by the bound of its tree plus the bound of its continuation at the leaves
of the tree that satisfy `Q`. -/
theorem oa_stb_bind {m n : ℕ} {A : CatCrypt.Crypto.OracleAdv.Timed D R α}
    {f : α → ℕ × CatCrypt.Crypto.OracleAdv.Timed D R β} {Q : α → Prop} (hA : A.TimeBound m)
    (hQ : AllRet Q A) (hf : ∀ a, Q a → StepTimeBound (f a) n) :
    StepTimeBound (A.bind f) (m + n) :=
  timeBound_bind_of_allRet hA hQ hf

/-- The tree of a step-prefixed tree is bounded by the bound of the pair. -/
theorem oa_tb_snd {n : ℕ} {y : ℕ × CatCrypt.Crypto.OracleAdv.Timed D R α}
    (h : StepTimeBound y n) : y.2.TimeBound n :=
  h.2.mono (Nat.sub_le _ _)

/-- A pair is bounded by the time bound of its tree after its step cost. -/
theorem oa_stb_delay {c m n : ℕ} {y : ℕ × CatCrypt.Crypto.OracleAdv.Timed D R α} (hc : c ≤ m)
    (hy : StepTimeBound y n) : StepTimeBound (delay c y) (m + n) :=
  (stepTimeBound_delay hy).mono (by omega)

/-- An `if` of step-prefixed trees is bounded by the maximum of the bounds of its branches. -/
theorem oa_stb_ite {c : Prop} [Decidable c] {m n : ℕ}
    {x y : ℕ × CatCrypt.Crypto.OracleAdv.Timed D R α} (hx : StepTimeBound x m)
    (hy : StepTimeBound y n) : StepTimeBound (if c then x else y) (max m n) := by
  split
  · exact hx.mono (le_max_left _ _)
  · exact hy.mono (le_max_right _ _)

/-- A dependent `if` of step-prefixed trees is bounded by the maximum of the bounds of its
branches. -/
theorem oa_stb_dite {c : Prop} [Decidable c] {m n : ℕ}
    {x : c → ℕ × CatCrypt.Crypto.OracleAdv.Timed D R α}
    {y : ¬c → ℕ × CatCrypt.Crypto.OracleAdv.Timed D R α} (hx : ∀ h, StepTimeBound (x h) m)
    (hy : ∀ h, StepTimeBound (y h) n) : StepTimeBound (dite c x y) (max m n) := by
  by_cases h : c
  · rw [dite_eq_left h]
    exact (hx h).mono (le_max_left _ _)
  · rw [dite_eq_right h]
    exact (hy h).mono (le_max_right _ _)

/-- An `if` of trees is bounded by the maximum of the bounds of its branches. -/
theorem oa_tb_ite {c : Prop} [Decidable c] {m n : ℕ}
    {x y : CatCrypt.Crypto.OracleAdv.Timed D R α} (hx : x.TimeBound m)
    (hy : y.TimeBound n) : (if c then x else y).TimeBound (max m n) := by
  split
  · exact hx.mono (le_max_left _ _)
  · exact hy.mono (le_max_right _ _)

end OracleRules

open Lean Meta Elab Term Command CatCrypt.Core

meta section

/-- The role of a binder of a costed tree in its time theorem. -/
inductive Role where
  /-- A function into costed trees: its time is bounded pointwise. -/
  | tree
  /-- A costed tree: its time is bounded. -/
  | key
  /-- A cost companion: bounded pointwise. -/
  | cost
  /-- A function into costed oracle adversaries: its time bound holds pointwise. -/
  | oadv

/-- The role of a binder of type `t`; with `oadv`, a function into (or a value of) costed
oracle adversaries `OracleAdv.Timed D R β` is bounded as well. -/
def roleOf (t : Expr) (oadv : Bool := false) : MetaM (Option Role) := do
  forallTelescopeReducing t fun ys b => do
    let b ← whnfR b
    if oadv && b.isAppOf ``CatCrypt.Crypto.OracleAdv.Timed then return some .oadv
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
variable after the registered costs are replaced by closed forms, the `match` of the bounds of
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
    return mkAddN (← boundCost bs (x.getArg! 1)) (← boundStep bs (x.getArg! 2))
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
      | .cost | .oadv => pure ()
  let t ← reduceHead t
  if let .fvar f := t.getAppFn then
    if let some (_, v, r) := bs.find? (·.1 == f) then
      match r with
      | .tree | .key => return v
      | .cost | .oadv => pure ()
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

/-- The bound variables and hypotheses of the bounded binders `xs`, in order, passed to `k`
with the bounds. -/
partial def withBounds {γ : Type} (xs : Array Expr) (i : Nat) (bs : Bounds)
    (vars hyps : Array Expr) (k : Bounds → Array Expr → Array Expr → TermElabM γ)
    (oadv : Bool := false) : TermElabM γ := do
  if h : i < xs.size then
    let x := xs[i]
    let t ← inferType x
    match ← roleOf t oadv with
    | none => withBounds xs (i + 1) bs vars hyps k oadv
    | some r =>
      let n := (← x.fvarId!.getUserName).eraseMacroScopes
      let vName := match r with
        | .tree | .oadv => Name.mkSimple ("T_" ++ n.toString)
        | .key => Name.mkSimple ("G_" ++ n.toString)
        | .cost => Name.mkSimple ("t_" ++ n.toString)
      withLocalDecl vName .implicit natE fun v => do
        let hTy ← forallTelescopeReducing t fun ys _ => do
          let concl ← match r with
            | .cost => mkAppM ``LE.le #[mkAppN x ys, v]
            | .oadv => mkAppM ``CatCrypt.Crypto.OracleAdv.Timed.TimeBound #[mkAppN x ys, v]
            | _ => do mkAppM ``LE.le #[← mkAppM ``SPTree.Timed.time #[mkAppN x ys], v]
          mkForallFVars ys concl
        withLocalDeclD (Name.mkSimple ("h_" ++ n.toString)) hTy fun hx =>
          withBounds xs (i + 1) (bs.push (x.fvarId!, v, r)) (vars.push v) (hyps.push hx) k
            oadv
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

/-- A bound of a costed oracle adversary or of a step-prefixed one, its proof, and, when the
leaves of the tree are known to satisfy a predicate `Q` (from the time theorem of a callee),
`Q` with the proof of `AllRet Q t`. -/
structure OABound where
  /-- The bound. -/
  bound : Expr
  /-- The proof of `t.TimeBound bound` or of `StepTimeBound x bound`. -/
  proof : Expr
  /-- The leaf invariant `Q` of the tree and the proof of `AllRet Q t`. -/
  inv : Option (Expr × Expr) := none

/-- The context of the bound of a costed oracle adversary: the bounded binders with their
hypotheses, and the variables that no bound may mention (the cost companions and the values
bound inside the tree). -/
structure OACtx where
  /-- The bounded binders, with their bound variables, roles and hypotheses. -/
  hs : HBounds
  /-- The variables eliminated from every bound. -/
  avoid : Array FVarId

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

/-- The bound of a call `x` (`step`: a step-prefixed adversary, else an adversary) from the time
theorem of the callee (`AutoTime.envSources`): its conclusion `StepTimeBound x B` (or
`x.TimeBound B`), or the conjunction of it with a leaf invariant `AllRet Q x.2` (`AllRet Q x`),
unified at `x`, its premises closed by `closePremises`. -/
def oaCallee? (xs : Array FVarId) (x : Expr) (step : Bool) : MetaM (Option OABound) := do
  let head := if step then ``CatCrypt.Crypto.OracleAdv.Timed.StepTimeBound
    else ``CatCrypt.Crypto.OracleAdv.Timed.TimeBound
  for c in ← CatCrypt.Tactics.AutoTime.envSources x do
    let st ← saveState
    try
      let (ms, _, body) ← forallMetaTelescopeReducing (← inferType c)
      let isAnd := body.isAppOfArity ``And 2
      let core := if isAnd then body.getArg! 0 else body
      unless core.isAppOfArity head 5 do st.restore; continue
      unless ← isDefEq (core.getArg! 3) x do st.restore; continue
      unless ← closePremises xs ms do st.restore; continue
      let pf ← instantiateMVars (mkAppN c ms)
      let B ← instantiateMVars (core.getArg! 4)
      if pf.hasExprMVar || B.hasExprMVar then st.restore; continue
      unless isAnd do return some { bound := B, proof := pf }
      let inv ← instantiateMVars (body.getArg! 1)
      let p ← mkAppM ``And.left #[pf]
      if inv.isAppOfArity ``CatCrypt.Crypto.OracleAdv.Timed.AllRet 5 then
        let q ← mkAppM ``And.right #[pf]
        return some { bound := B, proof := p, inv := some (inv.getArg! 3, q) }
      return some { bound := B, proof := p }
    catch _ => st.restore
  return none

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

/-- The type arguments `D`, `R`, `α` of `ℕ × OracleAdv.Timed D R α` (`pair`) or of
`OracleAdv.Timed D R α`. -/
def oaArgs (x : Expr) (pair : Bool) : MetaM (Expr × Expr × Expr) := do
  let mut t ← whnfR (← inferType x)
  if pair then t ← whnfR (t.getArg! 1)
  unless t.isAppOfArity ``CatCrypt.Crypto.OracleAdv.Timed 3 do
    throwError "not a costed oracle adversary{indentExpr x}"
  return (t.getArg! 0, t.getArg! 1, t.getArg! 2)

/-- The bound of a step cost, free of the variables to avoid. -/
def oaCost (cx : OACtx) (e : Expr) : MetaM (Expr × Expr) := do
  let some r ← bfree? cx.avoid e | throwError "no bound for the step cost{indentExpr e}"
  return r

mutual

/-- The bound of the step-prefixed adversary `x : ℕ × OracleAdv.Timed D R α`: a pair, a `delay`,
a bind, an `if` or `if h :` of pairs, or a call bounded by the time theorem of the callee. -/
partial def oaStep (cx : OACtx) (x : Expr) : TermElabM OABound := do
  let x' ← reduceHead x
  if x'.isAppOfArity ``Prod.mk 4 then return ← oaPair cx (x'.getArg! 2) (x'.getArg! 3)
  if x'.isAppOfArity ``CatCrypt.Crypto.OracleAdv.Timed.delay 5 then
    let (bc, pc) ← oaCost cx (x'.getArg! 3)
    let r ← oaStep cx (x'.getArg! 4)
    return { bound := mkAddN bc r.bound, proof := ← mkAppM ``oa_stb_delay #[pc, r.proof],
             inv := r.inv }
  if x'.isAppOfArity ``CatCrypt.Crypto.OracleAdv.Timed.bind 6 then
    let A := x'.getArg! 4
    let rA ← oaTree cx A
    let (_, hQ, n, hf) ← oaCont cx (x'.getArg! 2) rA.inv A (x'.getArg! 5)
    return { bound := mkAddN rA.bound n, proof := ← mkAppM ``oa_stb_bind #[rA.proof, hQ, hf] }
  if x'.isAppOfArity ``ite 5 || x'.isAppOfArity ``dite 5 then
    let (D, R, α) ← oaArgs x' true
    let c := x'.getArg! 1
    if x'.isAppOfArity ``ite 5 then
      let a ← oaStep cx (x'.getArg! 3)
      let b ← oaStep cx (x'.getArg! 4)
      return { bound := ← mkMaxN a.bound b.bound,
               proof := mkAppN (mkConst ``oa_stb_ite) #[D, R, α, c, x'.getArg! 2, a.bound,
                 b.bound, x'.getArg! 3, x'.getArg! 4, a.proof, b.proof] }
    let branch (ty br : Expr) : TermElabM (Expr × Expr) :=
      withLocalDeclD `h ty fun h => do
        let r ← oaStep { cx with avoid := cx.avoid.push h.fvarId! } (br.beta #[h])
        let b ← instantiateMVars r.bound
        if b.containsFVar h.fvarId! then throwError "the bound of a branch mentions its proof"
        return (b, ← mkLambdaFVars #[h] r.proof)
    let (a, pa) ← branch c (x'.getArg! 3)
    let (b, pb) ← branch (mkNot c) (x'.getArg! 4)
    return { bound := ← mkMaxN a b,
             proof := mkAppN (mkConst ``oa_stb_dite) #[D, R, α, c, x'.getArg! 2, a, b,
               x'.getArg! 3, x'.getArg! 4, pa, pb] }
  if let some r ← oaCallee? cx.avoid x true then return r
  if let some r ← oaCallee? cx.avoid x' true then return r
  throwError "no bound for the step-prefixed adversary{indentExpr x'}"

/-- The bound of the pair `(e, t)`: the tree `y` after `c` when `t = y.2` and `e = c + y.1`; with
`y = S.2.bind f` and `c = c₀ + S.1`, the step-prefixed adversary `S` followed by `f` after `c₀`,
`f` bounded at the leaves of `S.2` under the leaf invariant of `S` (`oa_stb_pair_bind`); else
the bound of `e` plus the bound of `t`. -/
partial def oaPair (cx : OACtx) (e t : Expr) : TermElabM OABound := do
  let t' ← reduceHead t
  if let some y := CatCrypt.Tactics.AutoTime.sndOf? t' then
    if let some o := findFst e y then
      let c := e.replace fun s => if s == o then some (mkNatLit 0) else none
      if y.isAppOfArity ``CatCrypt.Crypto.OracleAdv.Timed.bind 6 then
        if let some S := CatCrypt.Tactics.AutoTime.sndOf? (y.getArg! 4) then
          if let some oS := findFst c S then
            let c₀ := c.replace fun s => if s == oS then some (mkNatLit 0) else none
            let he ← omegaEq e (mkAddN (mkAddN c₀ oS) o)
            let (bc, pc) ← oaCost cx c₀
            let rS ← oaStep cx S
            let (_, hQ, n, hf) ← oaCont cx (y.getArg! 2) rS.inv (y.getArg! 4) (y.getArg! 5)
            return { bound := mkAddN bc (mkAddN rS.bound n),
                     proof := ← mkAppM ``oa_stb_pair_bind #[he, pc, rS.proof, hQ, hf] }
      let he ← omegaEq e (mkAddN c o)
      let (bc, pc) ← oaCost cx c
      let ry ← oaStep cx y
      return { bound := mkAddN bc ry.bound,
               proof := ← mkAppM ``oa_stb_pair_snd #[he, pc, ry.proof], inv := ry.inv }
  let (bc, pc) ← oaCost cx e
  let rt ← oaTree cx t
  return { bound := mkAddN bc rt.bound, proof := ← mkAppM ``oa_stb_pair #[pc, rt.proof],
           inv := rt.inv }

/-- The bound `n` of the continuation `f` of a bind of the tree `A` at a fresh value `a`, under
the leaf invariant `Q a` of `A` (`fun _ => True` without one) taken apart by `withInvHyps`: the
invariant `Q`, the proof of `AllRet Q A`, `n`, and the proof of
`∀ a, Q a → StepTimeBound (f a) n`. -/
partial def oaCont (cx : OACtx) (α : Expr) (inv : Option (Expr × Expr)) (A f : Expr) :
    TermElabM (Expr × Expr × Expr × Expr) := do
  let (Q, hQ) ← match inv with
    | some p => pure p
    | none => do
      pure (Expr.lam `a α (mkConst ``True) .default, ← mkAppM ``oa_allRet_true #[A])
  withLocalDeclD `a α fun a => do
    let qa := (Q.beta #[a]).headBeta
    withLocalDeclD `ha qa fun ha => do
      withInvHyps ha qa fun lets => do
        let r ← oaStep { cx with avoid := cx.avoid.push a.fvarId! } (f.beta #[a])
        let n ← instantiateMVars r.bound
        if n.containsFVar a.fvarId! || n.containsFVar ha.fvarId! ||
            lets.any fun l => n.containsFVar l.fvarId! then
          throwError "the bound of the continuation depends on the bound value{indentExpr n}"
        return (Q, hQ, n, ← mkLambdaFVars (#[a, ha] ++ lets) r.proof)

/-- The bound of the costed oracle adversary `t`: a bounded binder, a leaf, a `rand` or `query`
node (one unit, then the bound of its step-prefixed continuations at a fresh value), the tree
`y.2` of a step-prefixed adversary, an `if`, or a call bounded by the time theorem of the
callee. -/
partial def oaTree (cx : OACtx) (t : Expr) : TermElabM OABound := do
  let binder? (t : Expr) : Option OABound := do
    let .fvar f := t.getAppFn | none
    let (_, v, r, h) ← cx.hs.find? (·.1 == f)
    match r with
    | .oadv => some { bound := v, proof := mkAppN h t.getAppArgs }
    | _ => none
  if let some r := binder? t then return r
  let t' ← reduceHead t
  if let some r := binder? t' then return r
  if t'.isAppOfArity ``CatCrypt.Crypto.OracleAdv.Timed.ret 4 then
    return { bound := mkNatLit 0,
             proof := mkAppN (mkConst ``oa_tb_ret)
               #[t'.getArg! 0, t'.getArg! 1, t'.getArg! 2, t'.getArg! 3, mkNatLit 0] }
  let node (rand : Bool) : TermElabM OABound := do
    let (D, R, α) := (t'.getArg! 0, t'.getArg! 1, t'.getArg! 2)
    let (γ, c, k) := if rand then (t'.getArg! 3, t'.getArg! 5, t'.getArg! 6)
      else (R, t'.getArg! 4, t'.getArg! 5)
    withLocalDeclD `b γ fun b => do
      let r ← oaPair { cx with avoid := cx.avoid.push b.fvarId! } (c.beta #[b]) (k.beta #[b])
      let n ← instantiateMVars r.bound
      if n.containsFVar b.fvarId! then
        throwError "the bound of a node depends on its value{indentExpr n}"
      let h ← mkLambdaFVars #[b] r.proof
      let pf := if rand then
          mkAppN (mkConst ``oa_tb_rand) #[D, R, α, γ, t'.getArg! 4, c, k, n, h]
        else mkAppN (mkConst ``oa_tb_query) #[D, R, α, t'.getArg! 3, c, k, n, h]
      return { bound := mkAddN (mkNatLit 1) n, proof := pf }
  if t'.isAppOfArity ``CatCrypt.Crypto.OracleAdv.Timed.rand 7 then return ← node true
  if t'.isAppOfArity ``CatCrypt.Crypto.OracleAdv.Timed.query 6 then return ← node false
  if let some y := CatCrypt.Tactics.AutoTime.sndOf? t' then
    let r ← oaStep cx y
    return { bound := r.bound, proof := ← mkAppM ``oa_tb_snd #[r.proof], inv := r.inv }
  if t'.isAppOfArity ``ite 5 then
    let (D, R, α) ← oaArgs t' false
    let a ← oaTree cx (t'.getArg! 3)
    let b ← oaTree cx (t'.getArg! 4)
    return { bound := ← mkMaxN a.bound b.bound,
             proof := mkAppN (mkConst ``oa_tb_ite) #[D, R, α, t'.getArg! 1, t'.getArg! 2,
               a.bound, b.bound, t'.getArg! 3, t'.getArg! 4, a.proof, b.proof] }
  if let some r ← oaCallee? cx.avoid t false then return r
  if let some r ← oaCallee? cx.avoid t' false then return r
  throwError "no bound for the costed oracle adversary{indentExpr t'}"

end

/-- Whether the costed tree `c` returns a step-prefixed costed oracle adversary. -/
def isOracleTimed (c : Name) : MetaM Bool := do
  forallTelescope (← getConstInfo c).type fun _ body => do
    let body ← whnfR body
    unless body.isAppOfArity ``Prod 2 do return false
    return (← whnfR (body.getArg! 1)).isAppOf ``CatCrypt.Crypto.OracleAdv.Timed

/-- State and prove `name`, the time theorem `StepTimeBound (c xs) B` of the costed oracle
adversary `c`, along its bound (`oaStep`): every binder into costed oracle adversaries and
every cost companion gets a bound and its hypothesis (`withBounds`); the bound is normalised
(`normalizeSum`) when `omega`, alone or after `ring_nf`, proves the normalised bound above the
computed one. Returns the
reason when the bound is not computed or the proof is not accepted. -/
def emitOracleTimeBound (c name : Name) : TermElabM (Option MessageData) := do
  let info ← getConstInfo c
  let lvls := info.levelParams.map mkLevelParam
  forallTelescope info.type fun xs _ => do
    withBounds xs 0 #[] #[] #[] (oadv := true) fun bs vars hyps => do
      let hs : HBounds := (bs.zip hyps).map fun ((f, v, r), h) => (f, v, r, h)
      let avoid := bs.filterMap fun (f, _, r) => match r with
        | .cost => some f
        | _ => none
      let x := mkAppN (Lean.mkConst c lvls) xs
      let r ← try oaStep { hs, avoid } x
        catch e => return some m!"no bound: {e.toMessageData}"
      let B ← instantiateMVars r.bound
      let Bn ← normalizeSum B
      let mut bound := B
      let mut pf ← instantiateMVars r.proof
      if Bn != B then
        try
          let le ← omegaLe B Bn
          pf ← mkAppM ``CatCrypt.Crypto.OracleAdv.Timed.StepTimeBound.mono #[pf, le]
          bound := Bn
        catch _ => pure ()
      if pf.hasSorry || pf.hasExprMVar then return some m!"the proof is incomplete"
      let goal ← mkAppM ``CatCrypt.Crypto.OracleAdv.Timed.StepTimeBound #[x, bound]
      let ty ← mkForallFVars (xs ++ vars ++ hyps) goal
      let val ← mkLambdaFVars (xs ++ vars ++ hyps) pf
      try
        addDecl (Declaration.thmDecl
          { name, levelParams := info.levelParams, type := ty, value := val })
      catch e => return some m!"the proof is not accepted: {e.toMessageData}"
      return none
where
  /-- A proof of `l ≤ r` over `ℕ` by `omega`, else by `omega` after `ring_nf` (products of
  sums, whose factors `normalizeSum` normalises, are atoms of `omega`), with the hypotheses of
  the context cleared. -/
  omegaLe (l r : Expr) : TermElabM Expr := do
    let mv ← mkFreshExprSyntheticOpaqueMVar (mkNatLe l r)
    let mut hs : Array FVarId := #[]
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      if ← isProp d.type then hs := hs.push d.fvarId
    let g ← mv.mvarId!.tryClearMany hs
    let gs ← Tactic.run g (Tactic.evalTactic (← `(tactic| first | omega | (ring_nf <;> omega))))
    unless gs.isEmpty do throwError "omegaLe"
    instantiateMVars mv

/-- `derive_time_bound R.tree` states and proves `R.tree.timeBound_timed`, the time theorem of
`R.tree.timed` (see the module docstring): along its bound for a pure step body
(`mirrorTimeBound`), else by `time_bound` (`emitTimeBound`); it fails with the reason when the
theorem is not proved, for a pure step with the reasons of both procedures. -/
syntax (name := deriveTimeBoundCmd) "derive_time_bound " ident : command

@[command_elab deriveTimeBoundCmd]
def elabDeriveTimeBound : CommandElab := fun stx => do
  liftTermElabM do
    let t ← realizeGlobalConstNoOverloadWithInfo stx[1]
    let name := t ++ `timeBound_timed
    if ← isOracleTimed (t ++ `timed) then
      if let some why ← emitOracleTimeBound (t ++ `timed) name then
        throwError "`{name}` is not proved: {why}"
      return
    let r ← mirrorTimeBound (t ++ `timed) name
    if let .proved := r then return
    if let some why ← emitTimeBound (t ++ `timed) name then
      if let .refused w := r then
        throwError "`{name}` is not proved: {why}\nalong the bound of the pure step: {w}"
      throwError "`{name}` is not proved: {why}"

end

end CatCrypt.Tactics.DeriveTimeBound
