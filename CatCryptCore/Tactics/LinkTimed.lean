/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveTimed
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Complexity.D.Reflect
public import CatCryptCore.Complexity.D.TimedLink
public import CatCryptCore.Complexity.D.LinkDt

/-!
# `link_timed`: the costed tree of a reduction simulates its reflected D-term

For a tree `T` with its costed form `T.timed` of `derive_timed` and its D-term `T.d` of
`reflect_d`, the command `link_timed x` proves

* `T.d_timedSim`: `TimedSim (fun a w => a = w) 1 n (T.timed …) ((T.d …).eval ρ)` for a numeral
  allowance `n` computed by the derivation, and
* `T.d_cost_le`: `(T.d …).cost ρ ≤ n + 1 * SPTree.Timed.stepTime (T.timed …)`, by
  `TSim.cost_le`.

The argument `x` names the tree (`resolveTree`): `T = x.tree` for a reduction `x` of
`derive_reduction`, for a field `x = R.f` of a structure-valued reduction (its tree `R.f.tree`)
and for a step `x = S.start` of a multi-call simulator (`S.start.tree`, or `S.start.treeHat` on
costed states); `T = x` for a definition `x` with the costed form `x.timed` of `derive_timed`.

## The telescope

The binders are read off `T.d_den`, whose environment `ρ` is the environment of the
statement, and aligned with the binders of `T.timed`:

* a type parameter is the finite ground type of `reflect_d` (`MF : FTy` at `MF.den`);
* a record that `reflect_d` unbundles is the constructor applied to its fields, and the fields
  that are not types are binders kept in place;
* a data binder, a proof binder and an unused binder are kept, an unused function binder with
  its companion of `derive_timed`; an unused binder whose costed form has another type (a tree
  function `O' → SPTree.Timed O`) is the binder of the costed form;
* a data function `f` is kept with its companion `fCost` of `derive_timed`, its D value `gf`, a
  cost function `fDCost`, the step equation `hf : ∀ v, gf v = stepN CTree.tick (fDCost v)
  (.ret (f …))` and the bound `hfCost : ∀ v, fDCost v ≤ fCost …`;
* a tree function `A` with arguments is replaced by the costed tree `A`, its companion `ACost`,
  its D value `gA` and `hA : ∀ v, TimedSim (fun a w => a = w) 1 0 (ACost …, A …) (gA v)`,
  which `CTree.timedSim_costTree` discharges for the costed tree of a D value;
* a tree `p` without arguments is replaced by the costed tree `p`, its D value `gp` and
  `hp : TimedSim (fun a w => a = w) 1 0 (0, p) (gp ())`;
* a class method of `reflect_d` (the D value `gm` of a method `m` of a local instance, after
  the binders of the source) gets a cost function `mDCost`, the step equation `hm` and the
  bound `hmCost : ∀ v, mDCost v ≤ 0`: the method costs the unit step of its application, as
  `derive_timed` charges a method of a local instance; a method value that is a projection or
  re-pairing of its argument (`v.1`, `v.2`, `(v.1, v.2)`), which `derive_timed` charges nothing
  for, has the step of its application paid by the allowance (`DSim.appFree`).

## The route through the soundness theorem

For a D-term `t` in the fragment `Tm.InDtFrag` at a first-order type, `link_timed` first builds
the translated environment `η` of the telescope (`EnvHat.consE` of the cast of a data value,
`dataEntry` of a data function value and its cost companion, `treeEntry` of a costed tree
function value) and proves `CostLeA (fun a b => cast _ a = b) e d (t.dtC cc η) (T.timed …)`:
the costed form of `derive_timed` is above the charges of `Tm.dtC` stated on D's syntax, up to
deficits `e` in front and `d` in the tree that the allowance pays (`Tm.timedSim_of_costLeA`).

The charge of a call. The class: terms whose calls of function variables are at arguments of
any type of D, the finite ground types `base MF` of type parameters `MF` included. `cc` is
`callCost` (`Tm.dt`, `Tm.allow`) when `t.allow` reduces to a numeral; otherwise, when a call is
at an argument of type `base MF` with `MF` a variable, where `callCost (base MF)` is undecided,
every call is charged `1` (`cc = fun _ => 1`, `Tm.dtC_timedSim`), whose allowance
`t.allowC cc` does not depend on the argument types and reduces to a numeral. A call on `unit`,
which `derive_timed` charges nothing for, is then a deficit of one.

The deficit. The class: terms with calls of free function values (a projection or re-pairing
`v.1`, `v.2`, `(v.1, v.2)` of a matched argument, `Kind.freeFn`), which `derive_timed` charges
nothing for while `Tm.dtC` charges the unit call. As the walk pays that step from the allowance
(`DSim.appFree`), the comparison closes a step-cost side goal `c ≤ c' + e` at the least deficit
`e` up to the slack: the number of calls of free function values in `t`, at the charge `1` of
every call plus the number of calls on `unit`. The deficits add along a path (`TreeLeA`) and the
allowance of the statement is `t.allowC cc + (e + d)`. With no such call the slack is `0` and
the comparison is `CostLe`, without deficit.

The comparison is one rule over both costed trees after reduction to head normal form:

* equal constructors (`ret`, `sample`, `get`, `set`, `fail`) compare their leaves by definitional
  equality and their step costs as side goals, a child's step cost and subtree at one variable;
  the deficit of the node is the deficit of its step cost plus that of its subtrees;
* binds stuck at their first tree compare the first trees with equal leaves and the
  continuations pointwise (`CostLeA.bind`), and record the inequality of their step costs as a
  fact for the side goals;
* the leaf map at zero cost. The class: a costed bind `B.bind k` whose continuation is
  `k y = (0, ret (g y))` for a function `g` of the bound value, on either side of the comparison.
  Such a bind is the costed tree `B` with its leaves mapped by `g` at the same step costs, its
  own step cost `0` (`SPTree.Timed.bind_ret_fst`, recorded as a fact for the side goals). It is
  compared as `B` with the leaf relation composed with `g`, `S a (g b)` on the upper side
  (`TreeLeA.map_right`) and `S (g a) b` on the lower side (`TreeLeA.map_left`), at the same
  deficits. When both sides are stuck binds, `CostLeA.bind` is tried first and the leaf map is
  read when it fails (first trees with different leaves, such as a call on the term side against
  a costed call followed by a sample and a table on the costed side, then projected);
* a tree, a leaf or a step cost whose reduction is stuck at a variable of type `Bool`, a sum,
  `Option`, a list or a pair is split on that variable, both sides at once, at the largest
  deficit of the cases (`TreeLeA.mono`, `CostLeA.mono`);
* definitionally equal trees are equal (`TreeLeA.refl`);
* a side goal is closed by `omega` on the step costs with the first components of costed pairs,
  `callCost` and decided conditionals reduced, definitionally equal atoms identified, the facts
  of its context, `callCost_le_one`, and for two registered costs of the same left fold the
  monotonicity in the step cost (`foldl_timedCost_mono`) when the step costs compare.

`Tm.timedSim_of_costLeA` then gives `T.d_timedSim` from `Tm.dtC_timedSim`, `T.d_cost_le` follows
as below, and `TimedSim.run_eq` gives `T.d_run`: at a query-free evaluation, `T.d` means the
compiled erasure of `T.timed`. The statements are those of the walk, and the docstring of
`T.d_timedSim` names the charge and the deficit. When the route does not apply (constructs
outside the fragment, costed trees of another shape), the walk below proves the theorems and the docstring of `T.d_timedSim` records why the route did not
apply; when the walk also fails, the error reports both reasons.

## The walk

The proof is a walk over the D-term, one rule of `CatCryptCore.Complexity.D.TimedLink` per
construct, against the unfolded value of `T.timed`: `letE` of a sample, get or set, of a
data term (`TSim.letE`) or of a computation (`TSim.bind`), a call of a tree function value with
arguments (`TSim.call`) or on `unit` (`TSim.call0`), `ite`, `fail`, and a data leaf
(`TSim.ret`); data terms by `DSim.var`, `lit`, `natLit`, `pair`, `fst`, `snd`, `inl`, `inr`,
`letE`, `prim` (and `decide` for the atom of a condition), `app` of a data function value and
`appFree` of a projection or re-pairing value, a data conditional (`DSim.iteIf`, charged the
branch it takes, and `DSim.decBool` for the condition `if b` of a Boolean).

Calls of certified callees. The class: a call that `reflect_d` reflects as the closure of the
D-term `c.d` of a callee with a certificate `c.d_timedSim` (`Reflect.Impl.certCall?`,
`certClosure?`), on the last argument after the `let` of the others. The rule is `TSim.call` with
the closure (`Reflect.CEq.lam`) and, at the value of the arguments, the certificate of the callee
(`TSim.certCall`): the callee is linked at the call by its certificate, as a function variable
of the substitution theorem `Tm.dtC_subst` is by its entry, and its body is not walked again. At
a function parameter of the callee the argument is a data function value of the caller passed
through, whose step equation and cost bound are the premises of the certificate there
(`certArgs`). The
call is charged the unit of a call of `derive_timed` and the step cost of the costed form of the
callee; the allowance adds the allowance of the certificate. Its costed tree is read in head
normal form, and a bind whose first tree is such a call is unified with the projections of its
split pair reduced (`applyRuleProj`), so that its step cost is not taken from the costed form of
the callee. The route through the soundness theorem does not apply to such a term (the closure
of an effectful callee is outside `Tm.InDtFrag`).

The eliminator of a structural recursion. The class: a `fold` that `reflect_d` marks with its
source (a structural recursion `f` over a Lean inductive type `T` whose other arguments are
fixed variables of the D-term), the call charged by the companion `f.timedCost` of
`derive_timed`, defined by the same recursion. The rule is `DSim.foldEnc` at `C := f.timedCost`:
the scrutinee is walked first, its value the encoding `T.dEnc t`; the other arguments are read
from the environment; the induction over `T` (`T.rec`) takes at each constructor the walk of its
step at the node of its fields, its children and its recursive results, where a recursive call
on a child is `DSim.appRec` with the induction hypothesis at the child (its step count chosen by
`Exists.choose`), and the node condition, the allowance and the charge of the step within the
companion at the constructor, is closed by the equations of the companion and `omega`
(`DSim.node`). A case analysis on a value of `T` (charged inline by `derive_timed`), an
eliminator at a function motive (a recursion with an accumulator) and a constructor (the table
`ptab` of its children) are refused with messages naming them. A costed bind whose
continuation returns a
projection or re-pairing of its argument at zero cost (the projection of a costed table onto its
plain value) is removed by `TSim.bindRet`, the leaves then related through that map. The two
branches of an `ite` are derived each
at its own allowance and lifted to the larger one by `TSim.mono`.

At each tree node the costed tree of the goal is replaced by its tree under a fresh step cost
(`TSim.conv`); the step-cost inequalities are collected and closed once the walk has assigned the
costed trees, innermost first: an undetermined step cost is set to the other side or to `0`, the
others are closed by `omega`, with atoms that are definitionally equal identified first.
Any other construct is refused with a message naming it, as are operations on `ℕ` and leaves
whose type differs from their D representation (`Option`).

## Main definitions

* `link_timed x`: the command.
* `certClosure?`, `envPeel`, `certArgs`, `applyRuleProj`: the call of a certified callee.
* `DtState`, `DtM`, `provePair`, `proveTree`, `closeSideD`, `sideD`, `splitIdx`, `leafMap?`,
  `leafMapGoal`, `countFree`, `dtRoute`: the comparison of the
  route through the soundness theorem.

## Main results

* `TimedLink.TSim.conv`: the costed tree of a goal against its tree under a smaller step cost.
* `TimedLink.TSim.bindRet`: a costed bind with a zero-cost returning continuation against the
  D term of its tree.
* `TimedLink.DSim.appFree`: an application that the costed form charges nothing for, paid by the
  allowance.
* `TimedLink.DSim.inl`, `TimedLink.DSim.inr`: the injections into a sum.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Complexity.D.TimedLink

open CatCrypt.Core

variable {Γ : List Ty} {ρ : Env Γ} {α γ : Type} {τ : Ty} {K : ℕ}

/-- A costed tree `X` simulates whatever its tree simulates under a step cost at most that of
`X`. -/
theorem TSim.conv {E : α → Val τ → Prop} {n c : ℕ} {X : ℕ × SPTree.Timed α} {t : Tm Γ τ}
    (h : TSim E K n (c, X.2) t ρ) (hc : c ≤ X.1) : TSim E K n X t ρ :=
  TSim.le_fst hc h

/-- A data function value that `derive_timed` charges nothing for (a projection or re-pairing of
its argument) applied: the β-step and its `m ≤ d` steps are paid by the allowance. -/
theorem DSim.appFree {a b : Ty} {F : Tm Γ (.arr a b)} {x : Tm Γ a} {g : Val (.arr a b)}
    {v : Val a} {w : Val b} {n c d m : ℕ} (hF : Reflect.CEq F ρ 0 g) (hx : DSim K n c x ρ v)
    (hg : g v = stepN CTree.tick m (.ret w)) (hm : m ≤ d) :
    DSim K (n + (1 + d)) c (.app F x) ρ w := by
  obtain ⟨mx, hmx, l⟩ := hx
  exact ⟨0 + mx + (m + 1), Reflect.CEq.app hF hmx hg, by omega⟩

/-- A costed bind whose continuation returns `h y` at zero cost relates to what its tree relates
to, the leaves related through `h`. -/
theorem timedSimTree_bindRet {β : Type} {E : α → β → Prop} {h : γ → α} {n : ℕ}
    {A : SPTree.Timed γ} {t : CTree β} (hA : TimedSimTree (fun a w => E (h a) w) K n A t) :
    TimedSimTree E K n (A.bind fun y => (0, .ret (h y))).2 t := by
  induction hA with
  | ret hR => exact .ret hR
  | tick _ hm ih => exact .tick ih hm
  | sample f e mb _ hmb ih =>
    refine .sample f e mb ih fun b => ?_
    simp only [SPTree.Timed.bind_ret_fst, Nat.add_zero]
    exact hmb b
  | get i f mb _ hmb ih =>
    refine .get i f mb ih fun x => ?_
    simp only [SPTree.Timed.bind_ret_fst, Nat.add_zero]
    exact hmb x
  | set i f v mb _ hmb ih =>
    refine .set i f v mb ih ?_
    simp only [SPTree.Timed.bind_ret_fst, Nat.add_zero]
    exact hmb
  | fail => exact .fail
  | query d r x mb _ hmb ih =>
    refine .query d r x mb ih fun y => ?_
    simp only [SPTree.Timed.bind_ret_fst, Nat.add_zero]
    exact hmb y

/-- A costed bind whose continuation returns `h y` at zero cost (the projection of a costed value
of `derive_timed` onto its plain value) against the D term of its tree, the leaves related
through `h`. -/
theorem TSim.bindRet {E : α → Val τ → Prop} {h : γ → α} {x : ℕ × SPTree.Timed γ} {t : Tm Γ τ}
    {n : ℕ} (hx : TSim (fun a w => E (h a) w) K n x t ρ) :
    TSim E K n (SPTree.Timed.delay x.1 (x.2.bind fun y => (0, .ret (h y)))) t ρ := by
  unfold TSim TimedSim
  simp only [SPTree.Timed.delay, SPTree.Timed.bind_ret_fst, Nat.add_zero]
  exact timedSimTree_bindRet hx

/-- The left injection of a data term into a sum costs nothing beyond the term. -/
theorem DSim.inl {a b : Ty} {x : Tm Γ a} {v : Val a} {n c : ℕ} (h : DSim K n c x ρ v) :
    DSim K n c (.inl x : Tm Γ (.sum a b)) ρ (Sum.inl v : Val a ⊕ Val b) := by
  obtain ⟨m, hm, l⟩ := h
  refine ⟨m, ?_, l⟩
  change ((x.eval ρ).bind fun v => .ret (Sum.inl v : Val a ⊕ Val b)) = _
  rw [hm]
  exact Reflect.stepN_ret_bind m v _

/-- The right injection of a data term into a sum costs nothing beyond the term. -/
theorem DSim.inr {a b : Ty} {x : Tm Γ b} {v : Val b} {n c : ℕ} (h : DSim K n c x ρ v) :
    DSim K n c (.inr x : Tm Γ (.sum a b)) ρ (Sum.inr v : Val a ⊕ Val b) := by
  obtain ⟨m, hm, l⟩ := h
  refine ⟨m, ?_, l⟩
  change ((x.eval ρ).bind fun v => .ret (Sum.inr v : Val a ⊕ Val b)) = _
  rw [hm]
  exact Reflect.stepN_ret_bind m v _

end CatCrypt.Complexity.D.TimedLink

meta section

namespace CatCrypt.Complexity.D.LinkTimed

open Lean Elab Meta Term Command CatCrypt.Core CatCrypt.Complexity.D TimedLink

/-- The hypothesis attached to a D function value of the environment. -/
inductive Kind where
  /-- A data function value: its step equation `hg` and the bound `hFC` of its cost. -/
  | dataFn (hg hFC : Expr)
  /-- A data function value that `derive_timed` charges nothing for (a projection or re-pairing
  of its argument): its step equation `hg` and the bound `hFC` of its cost. -/
  | freeFn (hg hFC : Expr)
  /-- A tree function value with arguments, simulated by the costed tree (`hA`). -/
  | treeFn (hA : Expr)
  /-- A tree function value on `unit`, simulated by the costed tree (`hp`). -/
  | tree0 (hp : Expr)
  /-- The recursive results of a step of an eliminator: the induction hypotheses at the children
  (`ihs`, at the positions `poss`), or at a function of children (`fnIh`). -/
  | recFn (poss ihs : Array Expr) (fnIh : Option Expr)
  deriving Inhabited

/-- The walk monad: the kinds of the D function values; the state holds the step-cost side
goals. -/
abbrev LinkM := ReaderT (Std.HashMap FVarId Kind) (StateRefT (Array MVarId) TermElabM)

/-- A refusal of the walk. -/
def failL {α : Type} (msg : MessageData) : LinkM α := throwError m!"link_timed: {msg}"

/-- The rule `c` with a metavariable for every binder, the binders by name, and its
conclusion. -/
def instRule (c : Name) : MetaM (Expr × Std.HashMap Name Expr × Expr) := do
  let e ← mkConstWithFreshMVarLevels c
  let mut ty ← inferType e
  let mut args : Array Expr := #[]
  let mut m : Std.HashMap Name Expr := {}
  repeat
    match ty with
    | .forallE n d b _ =>
      let mv ← mkFreshExprMVar d (userName := n)
      args := args.push mv
      m := m.insert n mv
      ty := b.instantiate1 mv
    | _ => break
  return (mkAppN e args, m, ty)

/-- The metavariable of the binder `n` of a rule. -/
def arg (m : Std.HashMap Name Expr) (n : Name) : MetaM Expr := do
  let some e := m[n]? | throwError "link_timed: the rule has no binder `{n}`"
  return e

/-- Close the goal `mv` by `pf`. -/
def closeWith (mv pf : Expr) : MetaM Unit := do
  let mv ← instantiateMVars mv
  unless mv.isMVar do
    unless ← isDefEq mv pf do throwError "link_timed: `{pf}` does not close `{mv}`"
    return
  let pty ← inferType pf
  unless ← isDefEq (← inferType mv) pty do
    throwError "link_timed: the type{indentExpr pty}\ndoes not match{indentExpr (← inferType mv)}"
  mv.mvarId!.assign pf

/-- Apply the rule `c` to the goal `g` after `pre` has fixed some of its binders: unify its
conclusion and return its binders. -/
def applyRule (g : MVarId) (c : Name)
    (pre : Std.HashMap Name Expr → MetaM Unit := fun _ => pure ()) :
    LinkM (Std.HashMap Name Expr) := do
  let (pf, m, concl) ← instRule c
  pre m
  let gty ← g.getType
  unless ← isDefEq concl gty do
    failL m!"the rule `{c}` does not apply to{indentExpr (← instantiateMVars gty)}"
  g.assign pf
  return m

/-- `applyRule` with the projections of pairs in the conclusion reduced after `pre`: a step-prefixed
tree split into fresh metavariables by `pre` enters the unification through its components, so
that a component is not assigned by unifying the pair with the costed form of a callee whose
projection the goal holds. -/
def applyRuleProj (g : MVarId) (c : Name)
    (pre : Std.HashMap Name Expr → MetaM Unit := fun _ => pure ()) :
    LinkM (Std.HashMap Name Expr) := do
  let (pf, m, concl) ← instRule c
  pre m
  let concl ← Meta.transform (← instantiateMVars concl) (post := fun e => do
    if (e.isAppOfArity ``Prod.fst 3 || e.isAppOfArity ``Prod.snd 3) &&
        (e.getArg! 2).isAppOfArity ``Prod.mk 4 then
      return .done ((e.getArg! 2).getArg! (if e.isAppOfArity ``Prod.fst 3 then 2 else 3))
    return .continue)
  let gty ← g.getType
  unless ← isDefEq concl gty do
    failL m!"the rule `{c}` does not apply to{indentExpr (← instantiateMVars gty)}"
  g.assign pf
  return m

/-- The `i`-th value of the syntactic environment `ρ` (a chain of `Env.cons`). -/
partial def envNth (ρ : Expr) (i : Nat) : MetaM Expr := do
  let ρ ← instantiateMVars ρ
  unless ρ.isAppOfArity ``Env.cons 4 do
    throwError "link_timed: the environment `{ρ}` is not a chain of `Env.cons`"
  if i == 0 then return ρ.getArg! 2 else envNth (ρ.getArg! 3) (i - 1)

/-- The de Bruijn index of a variable `Var.here.there…`. -/
partial def varIdx (x : Expr) : MetaM Nat := do
  let x ← whnfR (← instantiateMVars x)
  if x.isAppOfArity ``Var.here 2 then return 0
  if x.isAppOfArity ``Var.there 4 then return (← varIdx (x.getArg! 3)) + 1
  throwError "link_timed: the variable `{x}` is not a de Bruijn index"

/-- The kind of the D value of the variable term `F` in `ρ`, if `F` is a variable bound to a
function value of the telescope. -/
def kindOfVar (ρ F : Expr) : LinkM (Option Kind) := do
  let F ← instantiateMVars F
  unless F.isAppOfArity ``Tm.var 3 do return none
  let v ← whnf (← envNth ρ (← varIdx (F.getArg! 2)))
  let .fvar fv := v | return none
  return (← read)[fv]?

/-- The callee `c` and its parameter context `Δ` when `F` is the closure of a certified callee
that `reflect_d` built at a call (`Reflect.Impl.certCall?`): `Tm.lam` of `c.d` renamed by
`Ren.liftN Δ`, with the certificate `c.d_timedSim` in the environment. -/
def certClosure? (F : Expr) : MetaM (Option (Name × Expr)) := do
  let F ← instantiateMVars F
  unless F.isAppOfArity ``Tm.lam 4 do return none
  let body := F.getArg! 3
  unless body.isAppOfArity ``Tm.rename 5 do return none
  unless (body.getArg! 4).isAppOfArity ``Ren.liftN 2 do return none
  let .const cd _ := body.getArg! 3 | return none
  let .str c "d" := cd | return none
  unless (← getEnv).contains (c ++ `d_timedSim) do return none
  return some (c, body.getArg! 0)

/-- The first `k` values of the syntactic environment `ρ` (a chain of `Env.cons`), innermost
first, and the environment below them. -/
partial def envPeel (ρ : Expr) : Nat → MetaM (Array Expr × Expr)
  | 0 => return (#[], ρ)
  | k + 1 => do
    let ρ ← instantiateMVars ρ
    unless ρ.isAppOfArity ``Env.cons 4 do
      throwError "link_timed: the environment `{ρ}` is not a chain of `Env.cons`"
    let (vs, ρ0) ← envPeel (ρ.getArg! 3) k
    return (#[ρ.getArg! 2] ++ vs, ρ0)

/-- The certificate `c.d_timedSim` at the D values `vs` of the parameters of `c`, outermost
first. A data parameter takes its value. A function parameter, whose binders in the certificate
are the function, its companion, its D value, the D cost, the step equation and the bound of the
D cost by the companion, is filled from a data function value of the caller passed through (a
variable of kind `dataFn` or `freeFn`): its D value, and its step equation and bound, from which
the function, the companion and the D cost are read by unification. -/
def certArgs (c : Name) (vs : Array Expr) : LinkM Expr := do
  let cert := Lean.mkConst (c ++ `d_timedSim)
  let (ms, _, _) ← forallMetaTelescopeReducing (← inferType cert)
  let mut k := 0
  let mut i := 0
  while k < ms.size && i < vs.size do
    let grp ← if k + 5 < ms.size then do
        let T ← whnfR (← inferType ms[k + 2]!)
        pure (T.isAppOfArity ``Val 1 && T.appArg!.isAppOfArity ``Ty.arr 2)
      else pure false
    if grp then
      let v ← whnf (← instantiateMVars vs[i]!)
      let some (hg, hFC) ← (do
          let .fvar fv := v | pure none
          match (← read)[fv]? with
          | some (.dataFn hg hFC) | some (.freeFn hg hFC) => pure (some (hg, hFC))
          | _ => pure none) |
        failL m!"the argument `{vs[i]!}` of the function parameter of `{c}` is not a data \
          function value of the caller"
      unless ← isDefEq ms[k + 2]! v do failL m!"the D value `{v}` at the call of `{c}`"
      unless ← isDefEq (← inferType ms[k + 4]!) (← inferType hg) do
        failL m!"the step equation of `{v}` at the call of `{c}`"
      ms[k + 4]!.mvarId!.assign hg
      unless ← isDefEq (← inferType ms[k + 5]!) (← inferType hFC) do
        failL m!"the cost bound of `{v}` at the call of `{c}`"
      ms[k + 5]!.mvarId!.assign hFC
      k := k + 6
    else
      unless ← isDefEq ms[k]! vs[i]! do failL m!"the argument `{vs[i]!}` of `{c}`"
      k := k + 1
    i := i + 1
  let pf ← instantiateMVars (mkAppN cert (ms.extract 0 k))
  if pf.hasExprMVar then failL m!"the certificate of `{c}` at the call is not determined"
  return pf

/-- Record a step-cost side goal. -/
def side (mv : Expr) : LinkM Unit := modify (·.push mv.mvarId!)

/-- The arguments of a `TSim` goal. -/
def tsimArgs (ty : Expr) : MetaM (Array Expr) := do
  let ty ← instantiateMVars ty
  unless ty.isAppOfArity ``TSim 9 do throwError "link_timed: not a `TSim` goal{indentExpr ty}"
  return ty.getAppArgs

/-- The arguments of a `DSim` goal. -/
def dsimArgs (ty : Expr) : MetaM (Array Expr) := do
  let ty ← instantiateMVars ty
  unless ty.isAppOfArity ``DSim 8 do throwError "link_timed: not a `DSim` goal{indentExpr ty}"
  return ty.getAppArgs

/-- Whether the D-term `e` is a data term: no effect, every application one of a data function
value. `loc` counts the binders of `e` above the environment `ρ`. -/
partial def isData (ρ : Expr) (loc : Nat) (e : Expr) : LinkM Bool := do
  let e ← instantiateMVars e
  if let .mdata _ e' := e then return ← isData ρ loc e'
  match e.getAppFn.constName?, e.getAppNumArgs with
  | some ``Tm.fold, 5 => isData ρ loc (e.getArg! 4)
  | some ``Tm.var, 3 => return true
  | some ``Tm.lit, 3 => return true
  | some ``Tm.natLit, 2 => return true
  | some ``Tm.pair, 5 => return (← isData ρ loc (e.getArg! 3)) && (← isData ρ loc (e.getArg! 4))
  | some ``Tm.fst, 4 => isData ρ loc (e.getArg! 3)
  | some ``Tm.snd, 4 => isData ρ loc (e.getArg! 3)
  | some ``Tm.inl, 4 => isData ρ loc (e.getArg! 3)
  | some ``Tm.inr, 4 => isData ρ loc (e.getArg! 3)
  | some ``Tm.prim, 5 => isData ρ loc (e.getArg! 4)
  | some ``Tm.letE, 5 =>
    return (← isData ρ loc (e.getArg! 3)) && (← isData ρ (loc + 1) (e.getArg! 4))
  | some ``Tm.app, 5 =>
    let F := e.getArg! 3
    unless F.isAppOfArity ``Tm.var 3 do return false
    let i ← varIdx (F.getArg! 2)
    if i < loc then return false
    let v ← whnf (← envNth ρ (i - loc))
    let .fvar fv := v | return false
    match (← read)[fv]? with
    | some (.dataFn ..) | some (.freeFn ..) => isData ρ loc (e.getArg! 4)
    | _ => return false
  | _, _ => return false

/-- Assign the value of a `DSim` goal, when still open, to `v`; a sampled value enters the
environment through the equivalence `Equiv.refl` of `TSim.sample` and is read through it. -/
def setVal (g : MVarId) (v : Expr) : MetaM Unit := do
  let as ← dsimArgs (← g.getType)
  let vm ← instantiateMVars as[7]!
  if vm.isMVar then
    unless ← vm.mvarId!.isAssigned do
      let v ← instantiateMVars v
      vm.mvarId!.assign (← if v.isAppOf ``DFunLike.coe then whnf v else pure v)

/-- The cost of a primitive operation of a `DSim.prim` or `DSim.decide` instance, as a numeral;
operations on `ℕ` are refused. -/
def primCost (t hp : Expr) : LinkM Nat := do
  if (t.getArg! 1).containsConst (· == ``Ty.nat) || (t.getArg! 2).containsConst (· == ``Ty.nat)
  then failL m!"the operation on `ℕ`{indentExpr t}\nis outside the fragment of link_timed"
  let some (_, _, lhs, _) := (← instantiateMVars (← inferType hp)).app4? ``LE.le |
    failL m!"the cost bound of `{t}`"
  let some k ← (evalNat (← whnf lhs)).run |
    failL m!"the cost{indentExpr lhs}\nof the primitive operation is not a numeral"
  return k

mutual

/-- Derive the `DSim` goal `g` construct by construct. -/
partial def solveD (g : MVarId) : LinkM Unit := g.withContext do
  let as ← dsimArgs (← g.getType)
  let t ← instantiateMVars as[5]!
  let ρ := as[6]!
  if let .mdata kv t' := t then
    if kv.contains `dFold.fn then return ← solveFold g kv t'
    return ← solveD g
  if let some (x, kd) ← recCall? ρ t then return ← solveRecCall g x kd
  match t.getAppFn.constName?, t.getAppNumArgs with
  | some ``Tm.var, 3 =>
    setVal g (← envNth ρ (← varIdx (t.getArg! 2)))
    discard <| applyRule g ``DSim.var
  | some ``Tm.lit, 3 => discard <| applyRule g ``DSim.lit
  | some ``Tm.natLit, 2 => discard <| applyRule g ``DSim.natLit
  | some ``Tm.pair, 5 =>
    let m ← applyRule g ``DSim.pair
    solveD (← arg m `hx).mvarId!
    solveD (← arg m `hy).mvarId!
  | some ``Tm.fst, 4 =>
    let m ← applyRule g ``DSim.fst
    solveD (← arg m `h).mvarId!
  | some ``Tm.snd, 4 =>
    let m ← applyRule g ``DSim.snd
    solveD (← arg m `h).mvarId!
  | some ``Tm.inl, 4 =>
    let m ← applyRule g ``DSim.inl
    solveD (← arg m `h).mvarId!
  | some ``Tm.inr, 4 =>
    let m ← applyRule g ``DSim.inr
    solveD (← arg m `h).mvarId!
  | some ``Tm.letE, 5 =>
    let m ← applyRule g ``DSim.letE
    solveD (← arg m `he).mvarId!
    solveD (← arg m `hb).mvarId!
  | some ``Tm.ite, 5 =>
    let m ← applyRule g ``DSim.iteIf
    closeWith (← arg m `hK) (← mkAppM ``Nat.le_refl #[as[2]!])
    solveCond (← arg m `hb).mvarId!
    solveD (← arg m `ht).mvarId!
    solveD (← arg m `he).mvarId!
  | some ``Tm.prim, 5 =>
    let m ← applyRule g ``DSim.prim
    solveD (← arg m `hx).mvarId!
    let hp ← arg m `hp
    let k ← primCost t hp
    let some K ← (evalNat as[2]!).run |
      failL m!"the factor{indentExpr as[2]!}\nis not a numeral"
    closeWith (← arg m `n₀) (mkNatLit (k - K))
    closeWith hp (← mkDecideProof (← instantiateMVars (← inferType hp)))
  | some ``Tm.app, 5 =>
    match ← kindOfVar ρ (t.getArg! 3) with
    | some (.dataFn hg hFC) =>
      let m ← applyRule g ``DSim.app
      closeWith (← arg m `hK) (← mkAppM ``Nat.le_refl #[as[2]!])
      let F := t.getArg! 3
      closeWith (← arg m `hF) (← mkAppM ``Reflect.CEq.var #[F.getArg! 2, ρ])
      solveD (← arg m `hx).mvarId!
      let v ← instantiateMVars (← arg m `v)
      closeWith (← arg m `hg) (mkApp hg v)
      closeWith (← arg m `hm) (mkApp hFC v)
    | some (.freeFn hg hFC) =>
      let m ← applyRule g ``DSim.appFree
      let F := t.getArg! 3
      closeWith (← arg m `hF) (← mkAppM ``Reflect.CEq.var #[F.getArg! 2, ρ])
      solveD (← arg m `hx).mvarId!
      let v ← instantiateMVars (← arg m `v)
      closeWith (← arg m `hg) (mkApp hg v)
      closeWith (← arg m `hm) (mkApp hFC v)
    | _ => failL m!"the application `{t}` is not a call of a data function value (an eliminator \
        at a function motive, the reflection of a recursion with an accumulator, is not linked)"
  | some ``Tm.fold, 5 =>
    failL m!"the eliminator{indentExpr t}\nis not the fold of a structural recursion with fixed \
      other arguments (a case analysis on a value of an inductive type, which `derive_timed` \
      charges inline, is not linked)"
  | some ``Tm.con, 3 =>
    failL m!"the constructor{indentExpr t}\nof an inductive type: the table of its children \
      (`ptab`) is outside the fragment of link_timed"
  | _, _ => failL m!"the data construct `{t.getAppFn}` is outside the fragment of link_timed"

/-- A recursive call in a step of an eliminator: the application of the recursive results at a
position (`DSim.appRec`), its cost the induction hypothesis at the child (`Exists.choose`). -/
partial def solveRecCall (g : MVarId) (x : Expr) (kd : Kind) : LinkM Unit := g.withContext do
  let as ← dsimArgs (← g.getType)
  let ρ := as[6]!
  let .recFn poss ihs fnIh := kd | failL m!"internal: a recursive call"
  let m ← applyRule g ``DSim.appRec
  closeWith (← arg m `hK) (← mkAppM ``Nat.le_refl #[as[2]!])
  closeWith (← arg m `hF) (← mkAppM ``Reflect.CEq.snd #[← mkAppM ``Reflect.CEq.snd
    #[← mkAppM ``Reflect.CEq.var #[x, ρ]]])
  solveD (← arg m `hx).mvarId!
  let v ← instantiateMVars (← arg m `v)
  let ih ← match fnIh with
    | some h => pure (mkApp h v)
    | none => do
      let mut found := none
      for p in poss, h in ihs do
        if found.isNone && (← isDefEq p v) then found := some h
      let some h := found | failL m!"the recursive call at the position `{v}`, which is not a \
        literal of a child"
      pure h
  let spec ← mkAppM ``Exists.choose_spec #[ih]
  closeWith (← arg m `hg) (← mkAppM ``And.left #[spec])
  closeWith (← arg m `hm) (← mkAppM ``And.right #[spec])

/-- The eliminator of a structural recursion `f` over a Lean inductive type (a fold that
`reflect_d` marks with its source): `DSim.foldEnc` with the cost companion `f.timedCost` of
`derive_timed`, its induction over the type built from the walk of each step at the node of its
constructor, whose node condition is the equation of the companion at the constructor. -/
partial def solveFold (g : MVarId) (kv : KVMap) (t : Expr) : LinkM Unit := g.withContext do
  let as ← dsimArgs (← g.getType)
  let K := as[2]!
  let ρ := as[6]!
  let f := kv.getName `dFold.fn
  let pos := kv.getNat `dFold.pos
  let fixed := (kv.getString `dFold.fixed).splitOn ","
  let ta := t.getAppArgs
  unless t.isAppOfArity ``Tm.fold 5 do failL m!"internal: the fold{indentExpr t}"
  let (Γ, S, cTy, gtm, x) := (ta[0]!, ta[1]!, ta[2]!, ta[3]!, ta[4]!)
  let comp := f ++ `timedCost
  unless (← getEnv).contains comp do
    failL m!"the structural recursion `{f}` has no cost companion `{comp}` (derive_timed \
      derives it for a callee)"
  -- The scrutinee, its value the encoding of a source value.
  let nx ← mkFreshExprMVar (mkConst ``Nat)
  let cx ← mkFreshExprMVar (mkConst ``Nat)
  let w ← mkFreshExprMVar (mkApp (mkConst ``Val) (mkApp (mkConst ``Ty.mu) S))
  let hx ← mkFreshExprMVar
    (mkAppN (mkConst ``DSim) #[Γ, mkApp (mkConst ``Ty.mu) S, K, nx, cx, x, ρ, w])
  solveD hx.mvarId!
  let w ← whnfR (← instantiateMVars w)
  let .const encN _ := w.getAppFn | failL m!"the scrutinee of the fold of `{f}` has the value \
    {w}, which is not the encoding of a source value"
  unless encN matches .str _ "dEnc" do
    failL m!"the scrutinee of the fold of `{f}` has the value {w}, which is not the encoding of \
      a source value"
  let t0 := w.appArg!
  let enc := w.appFn!
  let T ← inferType t0
  let some r ← Reflect.Impl.indRep? T | failL m!"the type `{T}` of the scrutinee of `{f}`"
  -- The other arguments of the recursion, read from the environment.
  let decode (v : Expr) : MetaM Expr := do
    let v ← whnfR v
    match v.getAppFn with
    | .const n _ => if n == ``Reflect.optEnc || n matches .str _ "dEnc" then return v.appArg!
                    else return v
    | _ => return v
  let mut args : Array Expr := #[]
  for i in [0:fixed.length] do
    let k := fixed[i]!
    if i == pos then args := args.push t0
    else match k.toNat? with
      | some k => args := args.push (← decode (← envNth ρ k))
      | none => failL m!"the argument {i} of the structural recursion `{f}` is not a variable of \
          the D-term"
  let srcAt (t' : Expr) : Expr := mkAppN (mkConst f) (args.set! pos t')
  let resTy ← inferType (srcAt t0)
  let E ← match ← Reflect.Impl.encoder? resTy with
    | some e => pure e
    | none => withLocalDeclD `v resTy fun v => mkLambdaFVars #[v] v
  let compTy ← inferType (mkConst comp)
  let compArity ← forallTelescope compTy fun ys _ => pure ys.size
  unless compArity == args.size do
    failL m!"the cost companion `{comp}` takes {compArity} arguments, `{f}` {args.size}"
  let Fl ← withLocalDeclD `t T fun t' => do mkLambdaFVars #[t'] (mkApp E (srcAt t')).headBeta
  let Cl ← withLocalDeclD `t T fun t' => do
    mkLambdaFVars #[t'] (mkAppN (mkConst comp) (args.set! pos t'))
  -- The steps: a tuple of closures, at no cost.
  let rec ceqSteps (e : Expr) : MetaM Expr := do
    let e ← instantiateMVars e
    if e.isAppOfArity ``Tm.pair 5 then
      return ← mkAppM ``Reflect.CEq.pair #[← ceqSteps (e.getArg! 3), ← ceqSteps (e.getArg! 4)]
    if e.isAppOfArity ``Tm.lam 4 then return ← mkAppM ``Reflect.CEq.lam #[e.getArg! 3, ρ]
    throwError "link_timed: the steps of the fold of `{f}` are not a tuple of λ-terms{indentExpr e}"
  let hg ← ceqSteps gtm
  let gv := (← instantiateMVars (← inferType hg)).appArg!
  let rec lams (e : Expr) : Array Expr :=
    if e.isAppOfArity ``Tm.pair 5 then lams (e.getArg! 3) ++ #[e.getArg! 4] else #[e]
  let stepLams := lams gtm
  unless stepLams.size == r.ctors.size do failL m!"internal: the steps of the fold of `{f}`"
  let X := mkApp (mkConst ``Ty.mu) S
  let stmt (t' : Expr) : MetaM Expr := do
    withLocalDeclD `m (mkConst ``Nat) fun mv => do
      let lhs := mkAppN (mkConst ``foldW) #[S, cTy, gv, mkApp enc t']
      let rhs ← mkAppM ``stepN #[mkConst ``CTree.tick, mv,
        mkApp2 (mkConst ``CTree.ret) (mkApp (mkConst ``Val) cTy) (mkApp Fl t').headBeta]
      let body := mkAnd (← mkEq lhs rhs) (← mkAppM ``LE.le #[mv, ← mkAppM ``HMul.hMul
        #[K, (mkApp Cl t').headBeta]])
      mkAppM ``Exists #[← mkLambdaFVars #[mv] body]
  let motive ← withLocalDeclD `t T fun t' => do mkLambdaFVars #[t'] (← stmt t')
  let ind ← getConstInfoInduct r.ind
  let eqns ← match ← getEqnsFor? comp with
    | some es => pure es
    | none => failL m!"the cost companion `{comp}` has no equations"
  let mut minors := Array.replicate ind.numCtors (default : Expr)
  for c in r.ctors, lamE in stepLams do
    let lamE ← instantiateMVars lamE
    let aTy := lamE.getArg! 1
    let body := lamE.getArg! 3
    let ctorTy ← instantiateForall (← getConstInfoCtor c.name).type r.params
    let mn ← forallTelescope ctorTy fun xs _ => do
      let ihTys ← c.recs.mapM fun i => do
        let xi := xs[i]!
        match ← whnf (← inferType xi) with
        | .forallE n R _ bi => withLocalDecl n bi R fun a => do
            mkForallFVars #[a] (mkApp motive (mkApp xi a)).headBeta
        | _ => pure (mkApp motive xi).headBeta
      withLocalDeclsDND (ihTys.mapIdx fun i T => (Name.mkSimple s!"ih{i}", T)) fun ihs => do
        let fvals := (c.fields.zip c.fieldEnc).map fun (i, en) => match en with
          | some e => mkApp e xs[i]!
          | none => xs[i]!
        let fv := Reflect.Impl.fieldTupleVal fvals.toList c.fieldTys.toList
        let val := fun τ => mkApp (mkConst ``Val) τ
        let finish (vv : Expr) (kd? : Option (Expr × Kind)) : LinkM Expr := do
          let ρ' := mkAppN (mkConst ``Env.cons) #[Γ, aTy, vv, ρ]
          let nb ← mkFreshExprMVar (mkConst ``Nat)
          let cb ← mkFreshExprMVar (mkConst ``Nat)
          let wb ← mkFreshExprMVar (val cTy)
          let hb ← mkFreshExprMVar (mkAppN (mkConst ``DSim) #[mkApp3 (mkConst ``List.cons [0])
            (mkConst ``Ty) aTy Γ, cTy, K, nb, cb, body, ρ', wb])
          match kd? with
          | some (fvr, kd) => withReader (·.insert fvr.fvarId! kd) (solveD hb.mvarId!)
          | none => solveD hb.mvarId!
          let goalB ← mkAppM ``LE.le #[← mkAppM ``HAdd.hAdd #[nb, ← mkAppM ``HMul.hMul #[K, cb]],
            ← mkAppM ``HMul.hMul
              #[K, (mkApp Cl (mkAppN (mkConst c.name) (r.params ++ xs))).headBeta]]
          let hB ← mkFreshExprMVar (← instantiateMVars goalB)
          let ids : Array (TSyntax `Lean.Parser.Tactic.simpLemma) ← eqns.mapM fun n =>
            `(Lean.Parser.Tactic.simpLemma| $(mkIdent n):ident)
          let rest ← try
              Tactic.run hB.mvarId! (Tactic.evalTactic
                (← `(tactic| (simp only [$ids,*]; (try split_ifs) <;> omega))))
            catch ex =>
              failL m!"the node condition of the constructor `{c.name}` of the fold of `{f}`, \
                the step against the equation of `{comp}`,{indentExpr (← instantiateMVars goalB)}\
                \nis not closed: {ex.toMessageData}"
          unless rest.isEmpty do
            failL m!"the node condition{indentExpr (← instantiateMVars goalB)}\nis not closed"
          let pf ← mkAppM ``DSim.node #[← instantiateMVars hb, ← instantiateMVars hB]
          let goal := (mkApp motive (mkAppN (mkConst c.name) (r.params ++ xs))).headBeta
          mkExpectedTypeHint pf goal
        let pf ← match c.shape.fty? with
          | none => finish fv none
          | some fy => do
            let encKids ← match c.shape with
              | .fn _ => withLocalDeclD `a (mkApp (mkConst ``FTy.den) fy) fun a =>
                  mkLambdaFVars #[a] (mkApp enc (mkApp xs[c.recs[0]!]! a))
              | _ => Reflect.Impl.kidTable c.shape (val X) (c.recs.map fun i => mkApp enc xs[i]!)
            let recV ← withLocalDeclD `j (mkApp (mkConst ``FTy.den) fy) fun j =>
              mkLambdaFVars #[j]
                (mkAppN (mkConst ``foldW) #[S, cTy, gv, (mkApp encKids j).headBeta])
            let piTy :=
              mkApp2 (mkConst ``Ty.pi) fy (.lam `_ (mkApp (mkConst ``FTy.den) fy) X .default)
            let arrTy := mkApp2 (mkConst ``Ty.arr) (mkApp (mkConst ``Ty.base) fy) cTy
            withLetDecl `rec (val arrTy) recV fun recF => do
              let inner := mkApp4 (mkConst ``Prod.mk [0, 0]) (val piTy) (val arrTy) encKids recF
              let vv := mkApp4 (mkConst ``Prod.mk [0, 0]) (val c.fieldTy)
                (val (mkApp2 (mkConst ``Ty.prod) piTy arrTy)) fv inner
              let poss ← (List.range c.recs.size).toArray.mapM fun i => do
                match c.shape with
                | .fn _ => pure default
                | _ => Reflect.Impl.posLit c.shape i
              let fnIh := match c.shape with | .fn _ => some ihs[0]! | _ => none
              let pf ← finish vv (some (recF, .recFn poss ihs fnIh))
              mkLetFVars #[recF] pf
        mkLambdaFVars (xs ++ ihs) pf
    minors := minors.set! c.declIdx mn
  let hF ← withLocalDeclD `t T fun t' => do
    mkLambdaFVars #[t'] (mkAppN (mkConst (r.ind ++ `rec) [Level.zero])
      (r.params ++ #[motive] ++ minors ++ #[t']))
  let m ← applyRule g ``DSim.foldEnc fun m => do
    for (n, v) in [(`S, S), (`c, cTy), (`g, gtm), (`x, x), (`gv, gv), (`T, T), (`enc, enc),
        (`F, Fl), (`C, Cl), (`t, t0)] do
      closeWith (← arg m n) v
  closeWith (← arg m `hK) (← mkAppM ``Nat.le_refl #[K])
  closeWith (← arg m `hg) hg
  closeWith (← arg m `hx) (← instantiateMVars hx)
  closeWith (← arg m `hF) hF

/-- The recursive results of a step of an eliminator applied, `app (snd (snd (var x))) a`: the
variable and the kind of its recursive results. -/
partial def recCall? (ρ t : Expr) : LinkM (Option (Expr × Kind)) := do
  unless t.isAppOfArity ``Tm.app 5 do return none
  let F ← instantiateMVars (t.getArg! 3)
  unless F.isAppOfArity ``Tm.snd 4 do return none
  let F' ← instantiateMVars (F.getArg! 3)
  unless F'.isAppOfArity ``Tm.snd 4 do return none
  let V ← instantiateMVars (F'.getArg! 3)
  unless V.isAppOfArity ``Tm.var 3 do return none
  let x := V.getArg! 2
  let v ← instantiateMVars (← envNth ρ (← varIdx x))
  unless v.isAppOfArity ``Prod.mk 4 do return none
  let v2 := v.getArg! 3
  unless v2.isAppOfArity ``Prod.mk 4 do return none
  let .fvar fv := v2.getArg! 3 | return none
  match (← read)[fv]? with
  | some kd@(.recFn ..) => return some (x, kd)
  | _ => return none

/-- Derive the `DSim` goal `g` of the condition of a conditional: an operation at its head is a
decision atom (`DSim.decide`). -/
partial def solveCond (g : MVarId) : LinkM Unit := g.withContext do
  let as ← dsimArgs (← g.getType)
  let t ← instantiateMVars as[5]!
  unless t.isAppOfArity ``Tm.prim 5 do
    -- A Boolean term read as the decision of its truth (`if b`), or a decision computed so.
    let s ← (Term.saveState : TermElabM Term.SavedState)
    try
      let m ← applyRule g ``DSim.decBool
      return ← solveD (← arg m `h).mvarId!
    catch _ =>
      (s.restore : TermElabM Unit)
      return ← solveD g
  let m ← applyRule g ``DSim.decide
  solveD (← arg m `hx).mvarId!
  let hp ← arg m `hp
  closeWith (← arg m `n₀) (mkNatLit (← primCost t hp))
  closeWith hp (← mkDecideProof (← instantiateMVars (← inferType hp)))

end

/-- The step cost and tree of a costed expression `X`. -/
def costedParts (X : Expr) : MetaM (Expr × Expr) := do
  let X ← instantiateMVars X
  let X := X.headBeta
  if X.isAppOfArity ``Prod.mk 4 then return (X.getArg! 2, X.getArg! 3)
  let X' ← whnfR X
  if X'.isAppOfArity ``Prod.mk 4 then return (X'.getArg! 2, X'.getArg! 3)
  return (← mkAppM ``Prod.fst #[X], ← mkAppM ``Prod.snd #[X])

/-- Replace the costed tree of the goal by its tree under a fresh step cost, bounded by the step
cost of the goal (a side goal), unless that step cost is still to be determined. -/
def conv (g : MVarId) : LinkM MVarId := do
  let as ← tsimArgs (← g.getType)
  let (c, A) ← costedParts as[6]!
  let c ← instantiateMVars c
  if c.isMVar then return g
  let (pf, m, concl) ← instRule ``TSim.conv
  unless ← isDefEq concl (← g.getType) do
    failL m!"the conversion does not apply to{indentExpr (← g.getType)}"
  g.assign pf
  side (← arg m `hc)
  let h ← arg m `h
  let hty ← tsimArgs (← inferType h)
  let x := hty[6]!
  unless x.isAppOfArity ``Prod.mk 4 do failL m!"the conversion has no pair"
  let g' ← mkFreshExprMVar (mkAppN (mkConst ``TSim) (hty.set! 6 (x.setArg 3 A)))
  closeWith h g'
  return g'.mvarId!

/-- A pair of fresh metavariables for the binder `n` of type `ℕ × SPTree.Timed γ`. -/
def splitPair (m : Std.HashMap Name Expr) (n : Name) : MetaM Unit := do
  let x ← arg m n
  let ty ← whnfR (← inferType x)
  unless ty.isAppOfArity ``Prod 2 do throwError "link_timed: `{n}` is not a pair"
  let p ← mkAppM ``Prod.mk #[← mkFreshExprMVar (ty.getArg! 0), ← mkFreshExprMVar (ty.getArg! 1)]
  unless ← isDefEq x p do throwError "link_timed: `{n}` does not split"

/-- The goal of a branch `h : TSim E K n x t ρ` of a conditional at a fresh allowance, and that
allowance: the branches are derived each at its own allowance. -/
def freshBranch (h : Expr) : MetaM (Expr × Expr) := do
  let as ← tsimArgs (← inferType h)
  let nB ← mkFreshExprMVar (mkConst ``Nat)
  return (← mkFreshExprMVar (mkAppN (mkConst ``TSim) (as.set! 5 nB)), nB)

/-- Close the branches `(h, g, nB)` of a conditional from their derivations `g` at the
allowances `nB` by `TSim.mono`, at the common allowance `n`: the largest `nB`, or the value of `n`
when it is already a numeral. -/
def joinBranches (n : Expr) (bs : Array (Expr × Expr × Expr)) : LinkM Unit := do
  let mut k := 0
  for (_, _, nB) in bs do
    let nB ← instantiateMVars nB
    let some kB ← (evalNat nB).run |
      failL m!"the allowance{indentExpr nB}\nof a branch is not a numeral"
    k := max k kB
  let nv ← instantiateMVars n
  if nv.isMVar then closeWith nv (mkNatLit k)
  else
    let some kn ← (evalNat nv).run | failL m!"the allowance{indentExpr nv}\nis not a numeral"
    k := kn
  for (h, g, nB) in bs do
    let hn ← mkDecideProof (← mkAppM ``LE.le #[← instantiateMVars nB, mkNatLit k])
    closeWith h (← mkAppM ``TSim.mono #[hn, g])

/-- Whether `e` is built from the variable `v` by `Prod.fst`, `Prod.snd` and `Prod.mk` alone: a
projection or re-pairing of a pair argument, which `derive_timed` charges nothing for. -/
partial def isPairMap (v e : Expr) : MetaM Bool := do
  let e := (← instantiateMVars e).headBeta
  if e == v then return true
  if e.isAppOfArity ``Prod.fst 3 || e.isAppOfArity ``Prod.snd 3 then
    return ← isPairMap v e.appArg!
  if e.isAppOfArity ``Prod.mk 4 then
    return (← isPairMap v (e.getArg! 2)) && (← isPairMap v (e.getArg! 3))
  return false

/-- Whether the costed tree `X` is `delay x.1 (x.2.bind fun y => (0, ret (h y)))` for a
projection or re-pairing `h` (`isPairMap`): the projection of the costed values of `x` onto their
plain values, which `TSim.bindRet` removes. -/
def isBindRet (X : Expr) : MetaM Bool := do
  let X := (← instantiateMVars X).headBeta
  unless X.isAppOfArity ``SPTree.Timed.delay 3 do return false
  let x := X.getArg! 2
  unless x.isAppOfArity ``SPTree.Timed.bind 4 do return false
  let .lam n T body _ := x.getArg! 3 | return false
  withLocalDeclD n T fun y => do
    let b := (body.instantiate1 y).headBeta
    unless b.isAppOfArity ``Prod.mk 4 do return false
    let r := b.getArg! 3
    unless r.isAppOfArity ``SPTree.Timed.ret 2 do return false
    isPairMap y r.appArg!

/-- Derive the `TSim` goal `g` construct by construct. -/
partial def solveT (g : MVarId) : LinkM Unit := g.withContext do
  let as ← tsimArgs (← g.getType)
  let K := as[4]!
  let t ← instantiateMVars as[7]!
  let ρ := as[8]!
  let one ← mkAppM ``Nat.le_refl #[K]
  let ret (g : MVarId) : LinkM Unit := do
    let m ← applyRule (← conv g) ``TSim.ret
    solveD (← arg m `ht).mvarId!
    let hE ← arg m `hE
    let some (_, l, _) := (← whnfR (← instantiateMVars (← inferType hE))).eq? |
      failL m!"the leaf relation{indentExpr (← inferType hE)}\nis not an equation"
    closeWith hE (← mkEqRefl l)
  if ← isBindRet as[6]! then
    let m ← applyRule g ``TSim.bindRet
    return ← solveT (← arg m `hx).mvarId!
  match t.getAppFn.constName?, t.getAppNumArgs with
  | some ``Tm.letE, 5 =>
    let e ← instantiateMVars (t.getArg! 3)
    match e.getAppFn.constName?, e.getAppNumArgs with
    | some ``Tm.sample, 2 =>
      let m ← applyRule (← conv g) ``TSim.sample
      closeWith (← arg m `hK) one
      closeWith (← arg m `e) (← mkAppM ``Equiv.refl #[← arg m `β])
      let (_, g') ← (← arg m `hk).mvarId!.intro1
      solveT g'
    | some ``Tm.get, 3 =>
      let m ← applyRule (← conv g) ``TSim.get
      closeWith (← arg m `hK) one
      let (_, g') ← (← arg m `hk).mvarId!.intro1
      solveT g'
    | some ``Tm.set, 4 =>
      let m ← applyRule (← conv g) ``TSim.set
      closeWith (← arg m `hK) one
      solveD (← arg m `hx).mvarId!
      solveT (← arg m `hk).mvarId!
      side (← arg m `hc)
    | _, _ =>
      if ← isData ρ 0 e then
        let m ← applyRule (← conv g) ``TSim.letE (splitPair · `x)
        solveD (← arg m `he).mvarId!
        solveT (← arg m `hb).mvarId!
        side (← arg m `hc)
      else
        let m ← if (← certClosure? (e.getArg! 3)).isSome && e.isAppOfArity ``Tm.app 5 then
            applyRuleProj (← conv g) ``TSim.bind (splitPair · `x)
          else applyRule (← conv g) ``TSim.bind (splitPair · `x)
        solveT (← arg m `hs).mvarId!
        let (_, g1) ← (← arg m `hk).mvarId!.intro1
        let (_, g2) ← g1.intro1
        let (h, g3) ← g2.intro1
        solveT (← Lean.Meta.subst g3 h)
  | some ``Tm.app, 5 =>
    if let some (c, Δ) ← certClosure? (t.getArg! 3) then
      -- A call of a certified callee: its certificate at the arguments of the call.
      let some (_, tys) := (← instantiateMVars Δ).listLit? |
        failL m!"the parameter context `{Δ}` of `{c}` is not a list"
      -- The costed tree of the call in head normal form, so that its tree is read off the
      -- costed form of the callee and not off a projection of the caller's.
      let gty ← instantiateMVars (← g.getType)
      let g0 ← g.replaceTargetDefEq
        (mkAppN gty.getAppFn (gty.getAppArgs.set! 6 (← whnf (gty.getArg! 6))))
      let g' ← conv g0
      let (_, A) ← costedParts (← tsimArgs (← g'.getType))[6]!
      let m ← applyRule g' ``TSim.call fun m => do
        let y ← arg m `y
        let p ← mkAppM ``Prod.mk #[← mkFreshExprMVar (mkConst ``Nat), A]
        unless ← isDefEq y p do throwError "link_timed: the call does not split"
      closeWith (← arg m `hK) one
      let F := t.getArg! 3
      closeWith (← arg m `hF) (← mkAppM ``Reflect.CEq.lam #[F.getArg! 3, ρ])
      solveD (← arg m `hx).mvarId!
      let u ← instantiateMVars (← arg m `u)
      let (inner, ρ0) ← envPeel ρ (tys.length - 1)
      let vs := inner.reverse.push u
      let h ← mkAppM ``TSim.certCall #[← certArgs c vs, ρ0]
      closeWith (← arg m `hg) h
      side (← arg m `hc)
      return
    match ← kindOfVar ρ (t.getArg! 3) with
    | some (.treeFn hA) =>
      let m ← applyRule (← conv g) ``TSim.call (splitPair · `y)
      closeWith (← arg m `hK) one
      let F := t.getArg! 3
      closeWith (← arg m `hF) (← mkAppM ``Reflect.CEq.var #[F.getArg! 2, ρ])
      solveD (← arg m `hx).mvarId!
      closeWith (← arg m `hg) (mkApp hA (← instantiateMVars (← arg m `u)))
      side (← arg m `hc)
    | some (.tree0 hp) =>
      let m ← applyRule g ``TSim.call0
      let F := t.getArg! 3
      closeWith (← arg m `hF) (← mkAppM ``Reflect.CEq.var #[F.getArg! 2, ρ])
      closeWith (← arg m `hg) hp
    | _ =>
      if ← isData ρ 0 t then ret g
      else failL m!"the application `{t}` is not a call of a function value of the telescope"
  | some ``Tm.fail, 2 => discard <| applyRule (← conv g) ``TSim.fail
  | some ``Tm.ite, 5 =>
    let m ← applyRule (← conv g) ``TSim.ite
    closeWith (← arg m `hK) one
    solveCond (← arg m `hb).mvarId!
    let ht ← arg m `ht
    let he ← arg m `he
    let (gt, nt) ← freshBranch ht
    solveT gt.mvarId!
    let (ge, ne) ← freshBranch he
    solveT ge.mvarId!
    joinBranches (← arg m `n₂) #[(ht, gt, nt), (he, ge, ne)]
    side (← arg m `hc)
  | _, _ =>
    if ← isData ρ 0 t then ret g
    else failL m!"the tree construct `{t.getAppFn}` is outside the fragment of link_timed"

/-- The `ℕ`-expression `e` with every maximal subterm other than `+`, `*` and a numeral replaced by
the first atom of the state that it is definitionally equal to (added to the state when there is
none), so that `omega` sees atoms that differ only in implicit arguments as one. -/
partial def canonAtoms (e : Expr) : StateT (Array Expr) MetaM Expr := do
  let e ← instantiateMVars e
  if e.isAppOfArity ``HAdd.hAdd 6 || e.isAppOfArity ``HMul.hMul 6 then
    return mkApp2 e.appFn!.appFn! (← canonAtoms (e.getArg! 4)) (← canonAtoms (e.getArg! 5))
  if e.isAppOf ``OfNat.ofNat || e.isRawNatLit then return e
  for a in ← get do
    if ← isDefEq a e then return a
  modify (·.push e)
  return e

/-- Close a step-cost side goal `a ≤ b`: a side that is an undetermined step cost is set to the
other side; a step cost that no construct determines is the least, `0`; the rest is `omega`
after β-, projection-, `delay`-, `Val`-, `Prim.apply`- and `Equiv.refl`-normalisation. -/
def solveSide (g : MVarId) : TermElabM Unit := g.withContext do
  if ← g.isAssigned then return
  let ty ← instantiateMVars (← g.getType)
  let some (_, _, a, b) := ty.app4? ``LE.le
    | throwError "link_timed: the side goal{indentExpr ty}\nis not an inequality"
  let a := a.headBeta
  let b := b.headBeta
  if b.isMVar then
    unless ← b.mvarId!.isAssigned do
      b.mvarId!.assign a
      g.assign (← mkAppM ``Nat.le_refl #[a])
      return
  if a.isMVar then
    unless ← a.mvarId!.isAssigned do
      a.mvarId!.assign b
      g.assign (← mkAppM ``Nat.le_refl #[b])
      return
  for m in (ty.collectMVars {}).result do
    unless ← m.isAssigned do
      if ← isDefEq (← m.getType) (mkConst ``Nat) then m.assign (mkNatLit 0)
  let gs ← try
      Tactic.run g do
        Tactic.evalTactic (← `(tactic| first
          | omega
          | (try dsimp only [SPTree.Timed.delay, Val, Prim.apply, Equiv.refl_apply])))
    catch ex =>
      throwError "link_timed: the step-cost inequality{indentExpr ty}\nis not closed: \
        {ex.toMessageData}"
  for g' in gs do
    let g'' ← g'.withContext do
      let ty' ← instantiateMVars (← g'.getType)
      let some (_, _, a', b') := ty'.app4? ``LE.le | pure g'
      let ((a'', b''), _) ← (do pure (← canonAtoms a', ← canonAtoms b')).run #[]
      g'.replaceTargetDefEq (mkApp2 ty'.appFn!.appFn! a'' b'')
    let rest ← try Tactic.run g'' (Tactic.evalTactic (← `(tactic| omega)))
      catch ex =>
        throwError "link_timed: the step-cost inequality{indentExpr ty}\nis not closed: \
          {ex.toMessageData}"
    unless rest.isEmpty do
      throwError "link_timed: the step-cost inequality{indentExpr ty}\nis not closed"

/-! ## The route through the soundness theorem of `Tm.dt` -/

/-- The state of a comparison of two costed trees: the facts `x.1 ≤ y.1` of the stuck binds
compared so far. -/
structure DtState where
  /-- Proofs of inequalities between step costs, each with the variables of its context. -/
  facts : Array (Expr × Array FVarId) := #[]
  /-- The largest deficit of a step-cost side goal: the number of calls of free function values
  (`Kind.freeFn`) in the term. -/
  slack : Nat := 0

/-- The comparison monad. -/
abbrev DtM := StateRefT DtState TermElabM

/-- A refusal of the comparison. -/
def failD {α : Type} (msg : MessageData) : DtM α := throwError m!"{msg}"

/-- Record a fact between step costs. -/
def factD (pf : Expr) : DtM Unit := do
  let fvs := (← getLCtx).getFVarIds
  modify fun s => { s with facts := s.facts.push (pf, fvs) }

/-- Apply the rule `c` to the goal `g`: unify its conclusion and return its binders. -/
def applyRuleD (g : MVarId) (c : Name) : MetaM (Std.HashMap Name Expr) := do
  let (pf, m, concl) ← instRule c
  unless ← isDefEq concl (← g.getType) do
    throwError m!"the rule `{c}` does not apply to{indentExpr (← instantiateMVars (← g.getType))}"
  g.assign pf
  return m

/-- Whether a variable of type `T` is split as a discriminant: `Bool`, a sum, `Option` and a
list. -/
def splittable (T : Expr) : MetaM Bool := do
  let T ← whnfD T
  return T.isConstOf ``Bool || T.isAppOfArity ``Sum 2 || T.isAppOfArity ``Option 1 ||
    T.isAppOfArity ``List 1 || T.isAppOfArity ``Prod 2

/-- The variable on which the reduction of `e` is stuck, if `e` is an elimination (a matcher, a
recursor, a projection) of a splittable variable (`splittable`), through eliminations of
eliminations. -/
partial def stuckVar? (e : Expr) : MetaM (Option FVarId) := do
  let discr (d : Expr) : MetaM (Option FVarId) := do
    let d ← whnfD d
    if let .fvar fv := d then
      if (← fv.getDecl).isLet then return none
      return if ← splittable (← fv.getType) then some fv else none
    stuckVar? d
  let e ← whnfD e
  match e with
  | .proj _ _ s => discr s
  | _ =>
    let .const n _ := e.getAppFn | return none
    let args := e.getAppArgs
    if let some info ← getMatcherInfo? n then
      for i in [info.numParams + 1 : info.numParams + 1 + info.numDiscrs] do
        if h : i < args.size then
          if let some fv ← discr args[i] then return some fv
      return none
    if let some (.recInfo rv) := (← getEnv).find? n then
      if h : rv.getMajorIdx < args.size then return ← discr args[rv.getMajorIdx]
    return none

/-- The first variable on which one of `es` is stuck. -/
def firstStuck? (es : Array Expr) : MetaM (Option FVarId) := do
  for e in es do
    if let some fv ← stuckVar? e then return some fv
  return none

/-- The goals of a case split of `g` on the variable `fv`. -/
def splitOn (g : MVarId) (fv : FVarId) : MetaM (Array MVarId) := do
  return (← g.cases fv).map (·.mvarId)

/-- The step-cost expression `e` with `+`, `*` and numerals kept, the first component of a
costed pair reduced to the component, `callCost` of a type reduced to its value or kept with
the fact `callCost_le_one`, a subterm that reduces to a numeral (a decided conditional) that
numeral, and any other subterm an atom. -/
partial def normCost (e : Expr) : StateRefT (Array Expr) MetaM Expr := do
  let e := (← instantiateMVars e).headBeta
  if e.isAppOfArity ``HAdd.hAdd 6 || e.isAppOfArity ``HMul.hMul 6 then
    return mkApp2 e.appFn!.appFn! (← normCost (e.getArg! 4)) (← normCost (e.getArg! 5))
  if e.isAppOf ``OfNat.ofNat || e.isRawNatLit then return e
  if e.isLet || e.isMData then return ← normCost (← whnfCore e)
  -- A projection of a costed pair or of a costed closure, applied to further arguments.
  let pr? : Option (Nat × Expr × Array Expr) :=
    let f := e.getAppFn
    let as := e.getAppArgs
    if (f.isConstOf ``Prod.fst || f.isConstOf ``Prod.snd) && as.size ≥ 3 then
      some (if f.isConstOf ``Prod.fst then 0 else 1, as[2]!, as.extract 3 as.size)
    else match f with
      | .proj ``Prod i s => some (i, s, as)
      | _ => none
  if let some (i, P, extra) := pr? then
    let P' ← whnfD P
    if P'.isAppOfArity ``Prod.mk 4 then
      return ← normCost (mkAppN (P'.getArg! (2 + i)) extra).headBeta
    if i == 0 && extra.isEmpty then return ← mkAppM ``Prod.fst #[P']
    return e
  if e.isAppOfArity ``Tm.allow 3 || e.isAppOfArity ``Tm.allowC 4 then
    if let some k ← (evalNat (← reduce e)).run then return mkNatLit k
    return e
  if e.isAppOfArity ``callCost 1 then
    if let some k ← (evalNat (← whnfD e)).run then return mkNatLit k
    modify (·.push (mkApp (mkConst ``callCost_le_one) e.appArg!))
    return e
  if let some k ← (evalNat (← whnfD e)).run then return mkNatLit k
  return e

/-- Close the step-cost side goal `g` by `omega`, after `normCost` and the identification of
definitionally equal atoms (`canonAtoms`), with the facts whose variables are in its context;
when `omega` fails, split on a variable on which an atom is stuck and close each case. -/
partial def closeSideD (facts : Array (Expr × Array FVarId)) (fuel : Nat) (g : MVarId) :
    TermElabM Unit :=
  g.withContext do
  if ← g.isAssigned then return
  let ty ← instantiateMVars (← g.getType)
  let some (_, _, a, b) := ty.app4? ``LE.le |
    throwError "the side goal{indentExpr ty}\nis not an inequality"
  let lctx ← getLCtx
  let mut hs : Array (Expr × Expr × Expr) := #[]
  let mut extra : Array Expr := #[]
  let ((a', b'), ex) ← (do pure (← normCost a, ← normCost b)).run #[]
  extra := extra ++ ex
  for (f, fvs) in facts do
    unless fvs.all lctx.contains do continue
    let some (_, _, x, y) := (← instantiateMVars (← inferType f)).app4? ``LE.le | continue
    let ((x', y'), ex) ← (do pure (← normCost x, ← normCost y)).run #[]
    extra := extra ++ ex
    hs := hs.push (x', y', f)
  for f in extra do
    let some (_, _, x, y) := (← inferType f).app4? ``LE.le | continue
    hs := hs.push (x, y, f)
  let ((tgt, hyps), atoms) ← (do
      let t ← mkAppM ``LE.le #[← canonAtoms a', ← canonAtoms b']
      let hyps ← hs.mapM fun (x, y, f) => do
        let t ← mkAppM ``LE.le #[← canonAtoms x, ← canonAtoms y]
        pure ({ userName := `hf, type := t, value := f } : Hypothesis)
      pure (t, hyps)).run #[]
  -- Registered fold costs of the same fold: the monotonicity in the step cost, when the step
  -- costs compare (`foldl_timedCost_mono`).
  let mut hyps := hyps
  if fuel > 0 then
    let folds := atoms.filter (·.isAppOfArity ``List.foldl.timedCost 6)
    for x in folds do
      for y in folds do
        if x == y then continue
        let (xa, ya) := (x.getAppArgs, y.getAppArgs)
        unless ← isDefEq xa[2]! ya[2]! <&&> isDefEq xa[4]! ya[4]! <&&> isDefEq xa[5]! ya[5]! do
          continue
        let st ← saveState
        try
          let hT ← withLocalDeclD `a xa[0]! fun a => withLocalDeclD `b xa[1]! fun b => do
            mkForallFVars #[a, b] (← mkAppM ``LE.le #[(mkApp2 xa[3]! a b).headBeta,
              (mkApp2 ya[3]! a b).headBeta])
          let h ← mkFreshExprMVar hT
          let (_, gh) ← h.mvarId!.introN 2
          closeSideD facts (fuel - 1) gh
          let pf ← mkAppM ``foldl_timedCost_mono #[xa[2]!, ← instantiateMVars h, xa[4]!, xa[5]!]
          hyps := hyps.push { userName := `hf, type := ← mkAppM ``LE.le #[x, y], value := pf }
        catch _ => st.restore
  let st ← saveState
  let ok ← try
      let g' ← g.replaceTargetDefEq tgt
      let (_, g') ← g'.assertHypotheses hyps
      let rest ← Tactic.run g' (Tactic.evalTactic (← `(tactic| omega)))
      pure rest.isEmpty
    catch _ => pure false
  if ok then return
  st.restore
  if fuel > 0 then
    if let some fv ← firstStuck? atoms then
      for g'' in ← splitOn g fv do closeSideD facts (fuel - 1) g''
      return
  throwError "the step-cost inequality{indentExpr tgt}\nis not closed by `omega` with the \
    facts{indentD (MessageData.joinSep (hyps.toList.map (m!"{·.type}")) ", ")}"

/-- The value of a numeral expression, after instantiation and, if needed, reduction. -/
def numeralD (e : Expr) : MetaM Nat := do
  let e ← instantiateMVars e
  if let some k ← (evalNat e).run then return k
  if let some k ← (evalNat (← reduce e)).run then return k
  throwError "the deficit{indentExpr e}\nis not a numeral"

/-- Close a step-cost side goal `c ≤ c' + e` of the comparison with the facts recorded so far:
for an undetermined deficit `e`, with the least `e` at most the slack (`DtState.slack`) for which
the goal closes. -/
def sideD (g : MVarId) : DtM Unit := do
  let st ← get
  let ty ← instantiateMVars (← g.getType)
  let some (_, _, _, rhs) := ty.app4? ``LE.le | closeSideD st.facts 8 g
  unless rhs.isAppOfArity ``HAdd.hAdd 6 && (rhs.getArg! 5).getAppFn.isMVar do
    closeSideD st.facts 8 g
    return
  let ev := rhs.getArg! 5
  let attempt (j : Nat) : TermElabM Bool := do
    let s ← saveState
    try
      unless ← isDefEq ev (mkNatLit j) do throwError "the deficit{indentExpr ev}\nis not set"
      closeSideD st.facts 8 g
      return true
    catch ex =>
      s.restore
      if j == st.slack then throw ex
      return false
  for j in [0:st.slack + 1] do
    if ← attempt j then return

/-- Prove the goal `g` with indices of deficit at the argument positions `idx` after a case
split on `fv`: each case is proved by `prove` at fresh indices, lifted by `mono` to the indices of
`g`, which are then the largest of the cases. -/
def splitIdx (g : MVarId) (fv : FVarId) (idx : List Nat) (mono : Name)
    (prove : MVarId → DtM Unit) : DtM Unit := do
  let ty ← instantiateMVars (← g.getType)
  let mut les : Array (Nat × Expr × Expr) := #[]
  for g' in ← splitOn g fv do
    let ls ← g'.withContext do
      let ty' ← instantiateMVars (← g'.getType)
      let mut args := ty'.getAppArgs
      let mut us : Array Expr := #[]
      for i in idx do
        let u ← mkFreshExprMVar (mkConst ``Nat)
        us := us.push u
        args := args.set! i u
      let h ← mkFreshExprMVar (mkAppN ty'.getAppFn args)
      let mut hs : Array Expr := #[]
      let mut ls : Array (Nat × Expr × Expr) := #[]
      for i in idx, u in us do
        let hle ← mkFreshExprMVar (← mkAppM ``LE.le #[u, ty'.getArg! i])
        hs := hs.push hle
        ls := ls.push (i, u, hle)
      g'.assign (← mkAppM mono (#[h] ++ hs))
      prove h.mvarId!
      pure ls
    les := les ++ ls
  for i in idx do
    let mut m := 0
    for (j, u, _) in les do
      if j == i then m := max m (← numeralD u)
    -- An undetermined index, possibly abstracted over the variables a split reverted.
    let D ← instantiateMVars (ty.getArg! i)
    if D.getAppFn.isMVar then
      unless ← isDefEq D (mkNatLit m) do throwError "the deficit{indentExpr D}\nis not set"
  for (_, u, hle) in les do
    let uE ← instantiateMVars u
    let DE ← instantiateMVars (← inferType hle)
    let some (_, _, _, D) := DE.app4? ``LE.le | throwError "not an inequality{indentExpr DE}"
    let pf := mkApp3 (mkConst ``Nat.le_of_ble_eq_true) uE D (← mkEqRefl (mkConst ``Bool.true))
    unless ← isDefEq (← inferType hle) (← inferType pf) do
      throwError "the deficit{indentExpr uE}\nof a case exceeds{indentExpr D}"
    hle.mvarId!.assign pf

/-- The bind whose tree the costed tree `T` is, when `T` is the tree of a costed bind stuck at
its first tree. -/
def bindView? (T : Expr) : MetaM (Option Expr) := do
  let P? : Option Expr :=
    if T.isAppOfArity ``Prod.snd 3 then some T.appArg!
    else match T with
      | .proj ``Prod 1 s => some s
      | _ => none
  let some P := P? | return none
  let P ← whnfD P
  return if P.isAppOfArity ``SPTree.Timed.bind 4 then some P else none

/-- The tree `B` and the leaf map `g` when the costed pair `P` is `B.bind fun y => (0, ret (g y))`:
a costed bind whose continuation returns a function of the bound value at zero cost. -/
def leafMap? (P : Expr) : MetaM (Option (Expr × Expr)) := do
  let P ← instantiateMVars P
  unless P.isAppOfArity ``SPTree.Timed.bind 4 do return none
  let .lam n T body _ := (← instantiateMVars (P.getArg! 3)) | return none
  withLocalDeclD n T fun y => do
    let b ← whnfD (body.instantiate1 y)
    unless b.isAppOfArity ``Prod.mk 4 do return none
    unless (← (evalNat (← instantiateMVars (b.getArg! 2))).run) == some 0 do return none
    let r ← whnfD (b.getArg! 3)
    unless r.isAppOfArity ``SPTree.Timed.ret 2 do return none
    return some (P.getArg! 2, ← mkLambdaFVars #[y] r.appArg!)

/-- Read the goal `g : TreeLeA S D A B` with `A` (`left`) or `B` the tree of the costed bind
`A₀.bind fun y => (0, ret (g' y))` (`leafMap?`) as the goal on `A₀` with the leaf relation
composed with `g'` (`TreeLeA.map_left`, `TreeLeA.map_right`), and return that goal. The step cost
`0` of the bind (`SPTree.Timed.bind_ret_fst`) becomes a fact for the side goals. -/
def leafMapGoal (g : MVarId) (left : Bool) (A₀ g' : Expr) : DtM MVarId := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  let (α, β, S', D, A, B) :=
    (ty.getArg! 0, ty.getArg! 1, ty.getArg! 2, ty.getArg! 3, ty.getArg! 4, ty.getArg! 5)
  let δ := (← whnfD (← inferType g')).bindingDomain!
  let (a₀, b₀) := if left then (δ, β) else (α, δ)
  let S ← withLocalDeclD `a a₀ fun a => withLocalDeclD `b b₀ fun b => do
    let r := if left then mkApp2 S' (mkApp g' a).headBeta b else mkApp2 S' a (mkApp g' b).headBeta
    mkLambdaFVars #[a, b] r.headBeta
  let hS ← withLocalDeclD `a a₀ fun a => withLocalDeclD `b b₀ fun b => do
    withLocalDeclD `h (mkApp2 S a b).headBeta fun h => mkLambdaFVars #[a, b, h] h
  let h ← mkFreshExprMVar (mkAppN (mkConst ``TreeLeA) #[a₀, b₀, S, D, (if left then A₀ else A),
    (if left then B else A₀)])
  let pf := if left then mkAppN (mkConst ``TreeLeA.map_left) #[δ, β, α, S, S', g', D, A₀, B, h, hS]
    else mkAppN (mkConst ``TreeLeA.map_right) #[α, δ, β, S, S', g', D, A, A₀, h, hS]
  unless ← isDefEq (← inferType pf) ty do
    failD m!"the leaf map{indentExpr g'}\ndoes not match{indentExpr ty}"
  g.assign pf
  factD (← mkAppM ``Nat.le_of_eq #[← mkAppM ``SPTree.Timed.bind_ret_fst #[A₀, g']])
  return h.mvarId!

/-- Close the goal `S a b` of two leaves: `S` applied is an equation between definitionally
equal sides, after a split on a variable on which a side is stuck. -/
partial def proveLeaf (g : MVarId) : DtM Unit := g.withContext do
  let ty := (← instantiateMVars (← g.getType)).headBeta
  let some (_, l, r) := ty.eq? | failD m!"the leaf relation{indentExpr ty}\nis not an equation"
  if ← isDefEq l r then
    g.assign (← mkEqRefl r)
    return
  if let some fv ← firstStuck? #[l, r] then
    for g' in ← splitOn g fv do proveLeaf g'
    return
  failD m!"the leaves{indentExpr l}\nand{indentExpr r}\ndiffer"

/-- Close the goal `h : ∀ x, P x` by `prove` at a fresh variable, the proof abstracted once it is
complete. -/
def underBinder (h : Expr) (prove : MVarId → DtM Unit) : DtM Unit := do
  let hT ← instantiateMVars (← inferType h)
  let .forallE n T _ _ := hT | throwError "the goal{indentExpr hT}\nis not universal"
  withLocalDeclD n T fun x => do
    let g ← mkFreshExprMVar (hT.bindingBody!.instantiate1 x)
    prove g.mvarId!
    h.mvarId!.assign (← mkLambdaFVars #[x] (← instantiateMVars g))

mutual

/-- Prove the goal `TreeLeA S D A B` node by node, its deficit `D` determined by the proof: equal
constructors (deficit of the step cost plus deficit of the subtrees), binds stuck at their first
tree (`CostLeA.bind`, whose step-cost inequality becomes a fact), a split on a variable on which
both reductions are stuck (the largest deficit of the cases, `TreeLeA.mono`), or definitionally
equal trees (`TreeLeA.refl`). -/
partial def proveTree (g : MVarId) : DtM Unit := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  unless ty.isAppOfArity ``TreeLeA 6 do failD m!"not a `TreeLeA` goal{indentExpr ty}"
  let A ← whnfD (ty.getArg! 4)
  let B ← whnfD (ty.getArg! 5)
  let g ← g.replaceTargetDefEq (mkAppN ty.getAppFn ((ty.getAppArgs.set! 4 A).set! 5 B))
  let node (c : Name) (single : Bool) : DtM Unit := do
    let m ← applyRuleD g c
    let hc ← arg m `hc
    let hk ← arg m `hk
    if single then
      proveTree hk.mvarId!
      sideD hc.mvarId!
    else
      -- The step cost and the subtree of a child are compared at the same variable.
      let hcT ← instantiateMVars (← inferType hc)
      let hkT ← instantiateMVars (← inferType hk)
      let .forallE n T _ _ := hcT | failD m!"the node rule `{c}` has no child binder"
      withLocalDeclD n T fun x => do
        let gc ← mkFreshExprMVar (hcT.bindingBody!.instantiate1 x)
        let gk ← mkFreshExprMVar (hkT.bindingBody!.instantiate1 x)
        proveTree gk.mvarId!
        sideD gc.mvarId!
        hc.mvarId!.assign (← mkLambdaFVars #[x] (← instantiateMVars gc))
        hk.mvarId!.assign (← mkLambdaFVars #[x] (← instantiateMVars gk))
  match A.getAppFn.constName?, B.getAppFn.constName? with
  | some ``SPTree.Timed.ret, some ``SPTree.Timed.ret =>
    let m ← applyRuleD g ``TreeLeA.ret0
    proveLeaf (← arg m `h).mvarId!
  | some ``SPTree.Timed.sample, some ``SPTree.Timed.sample => node ``TreeLeA.sample' false
  | some ``SPTree.Timed.sampleDist, some ``SPTree.Timed.sampleDist =>
    node ``TreeLeA.sampleDist' false
  | some ``SPTree.Timed.get, some ``SPTree.Timed.get => node ``TreeLeA.get' false
  | some ``SPTree.Timed.set, some ``SPTree.Timed.set => node ``TreeLeA.set' true
  | some ``SPTree.Timed.load, some ``SPTree.Timed.load => node ``TreeLeA.load' true
  | some ``SPTree.Timed.fail, some ``SPTree.Timed.fail => discard <| applyRuleD g ``TreeLeA.fail0
  | _, _ =>
    let vA ← bindView? A
    let vB ← bindView? B
    let lA ← match vA with | some P => leafMap? P | none => pure none
    let lB ← match vB with | some P => leafMap? P | none => pure none
    let stuckBinds (P P' : Expr) : DtM Unit := do
      let h ← mkFreshExprMVar (mkAppN (mkConst ``CostLeA) #[ty.getArg! 0, ty.getArg! 1,
        ty.getArg! 2, ← mkFreshExprMVar (mkConst ``Nat), ← mkFreshExprMVar (mkConst ``Nat), P, P'])
      let m ← applyRuleD h.mvarId! ``CostLeA.bind
      proveTree (← arg m `hA).mvarId!
      underBinder (← arg m `hk) provePair
      factD (← mkAppM ``CostLeA.fst_le #[h])
      let pf ← mkAppM ``CostLeA.tree #[h]
      unless ← isDefEq (← inferType pf) (← g.getType) do
        failD m!"the stuck binds{indentExpr P}\nand{indentExpr P'}\ndo not match"
      g.assign pf
    if let (some P, some P') := (vA, vB) then
      if lA.isNone && lB.isNone then
        stuckBinds P P'
        return
      -- A leaf map at zero cost on a side: the stuck binds first, else the leaf map.
      let s ← (saveState : TermElabM _)
      let st ← get
      try
        stuckBinds P P'
        return
      catch _ =>
        s.restore
        set st
    if let some (B₀, g') := lB then
      proveTree (← leafMapGoal g false B₀ g')
      return
    if let some (A₀, g') := lA then
      proveTree (← leafMapGoal g true A₀ g')
      return
    if let some fv ← firstStuck? #[A, B] then
      splitIdx g fv [3] ``TreeLeA.mono proveTree
      return
    if ← isDefEq A B then
      let m ← applyRuleD g ``TreeLeA.refl
      underBinder (← arg m `hS) proveLeaf
      return
    failD m!"the costed trees{indentExpr A}\nand{indentExpr B}\ndiffer in shape"

/-- Prove the goal `CostLeA S e d X Y`, its deficits determined by the proof: a split on a
variable on which a tree is stuck (the largest deficits of the cases), else the trees by
`proveTree` and the step-cost inequality as a side goal. -/
partial def provePair (g : MVarId) : DtM Unit := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  unless ty.isAppOfArity ``CostLeA 7 do failD m!"not a `CostLeA` goal{indentExpr ty}"
  let tr (X : Expr) : MetaM Expr := do
    let X ← whnfD X
    return if X.isAppOfArity ``Prod.mk 4 then X.getArg! 3 else mkProj ``Prod 1 X
  let A ← whnfD (← tr (ty.getArg! 5))
  let B ← whnfD (← tr (ty.getArg! 6))
  if (← bindView? A).isNone || (← bindView? B).isNone then
    if let some fv ← firstStuck? #[A, B] then
      splitIdx g fv [3, 4] ``CostLeA.mono provePair
      return
  let m ← applyRuleD g ``CostLeA.mk
  proveTree (← arg m `h).mvarId!
  sideD (← arg m `hc).mvarId!

end

/-- Prove a proposition that reduces to `True`, conjunctions, disjunctions and equations
between definitionally equal sides. -/
partial def proveRed (p : Expr) : MetaM Expr := do
  let p' ← whnfD p
  if p'.isConstOf ``True then return mkConst ``True.intro
  if p'.isAppOfArity ``And 2 then
    return mkApp4 (mkConst ``And.intro) p'.appFn!.appArg! p'.appArg!
      (← proveRed p'.appFn!.appArg!) (← proveRed p'.appArg!)
  if p'.isAppOfArity ``Or 2 then
    let a := p'.appFn!.appArg!
    let b := p'.appArg!
    try return mkApp3 (mkConst ``Or.inl) a b (← proveRed a)
    catch _ => return mkApp3 (mkConst ``Or.inr) a b (← proveRed b)
  if let some (_, l, r) := p'.eq? then
    if ← isDefEq l r then return ← mkEqRefl l
  throwError "the condition{indentExpr p}\ndoes not reduce to a true statement"

/-- The translated environment of the syntactic environment `ρ` of a telescope and the proof
that it is related to `ρ`: a data value `v` of a first-order type `σ` is the entry of its cast
(`Sim.cast_self`), a data function value the entry `dataEntry` of its value and cost
(`SimE.dataEntry`), a tree function value the entry `treeEntry` of its costed tree
(`SimE.treeEntry`). -/
partial def envHat (kinds : Std.HashMap FVarId Kind) (ρ : Expr) : MetaM (Expr × Expr) := do
  let ρ ← instantiateMVars ρ
  if ρ.isConstOf ``Env.nil then return (mkConst ``EnvHat.nil, mkConst ``SimEnv.nil)
  unless ρ.isAppOfArity ``Env.cons 4 do
    throwError "the environment `{ρ}` is not a chain of `Env.cons`"
  let σ := ρ.getArg! 1
  let v := ρ.getArg! 2
  let (η', h') ← envHat kinds (ρ.getArg! 3)
  let arrTys : MetaM (Expr × Expr × Expr × Expr) := do
    let σ' ← whnfD σ
    unless σ'.isAppOfArity ``Ty.arr 2 do throwError "the value `{v}` is not a function value"
    let a := σ'.getArg! 0
    let b := σ'.getArg! 1
    return (a, b, ← proveRed (mkApp (mkConst ``Ty.FO) a), ← proveRed (mkApp (mkConst ``Ty.FO) b))
  let kind? := match v with
    | .fvar fv => kinds[fv]?
    | _ => none
  let (e, he) ← match kind? with
    | some (.dataFn hg hFC) | some (.freeFn hg hFC) => do
      let (a, b, ha, hb) ← arrTys
      let (f, C) ← forallTelescope (← inferType hg) fun vs eq => do
        let some (_, _, r) := eq.eq? | throwError "the step equation `{hg}`"
        let as := r.getAppArgs
        let ret := as[as.size - 1]!
        pure (← mkLambdaFVars vs ret.appArg!, ← mkLambdaFVars vs as[as.size - 2]!)
      let fc ← forallTelescope (← inferType hFC) fun vs le => do
        let some (_, _, _, r) := le.app4? ``LE.le | throwError "the cost bound `{hFC}`"
        mkLambdaFVars vs r
      pure (← mkAppOptM ``dataEntry (#[a, b, ha, hb, f, fc].map some),
        ← mkAppOptM ``SimE.dataEntry (#[a, b, ha, hb, f, fc, C, v, hg, hFC].map some))
    | some (.treeFn hA) => do
      let (a, b, ha, hb) ← arrTys
      let F ← forallTelescope (← inferType hA) fun vs ts => do
        let ts ← instantiateMVars ts
        unless ts.isAppOfArity ``TimedSim 7 do throwError "the hypothesis `{hA}`"
        mkLambdaFVars vs (ts.getArg! 5)
      pure (← mkAppOptM ``treeEntry (#[a, b, ha, hb, F].map some),
        ← mkAppOptM ``SimE.treeEntry (#[a, b, ha, hb, F, v, hA].map some))
    | some (.tree0 hp) => do
      let (a, b, ha, hb) ← arrTys
      let ts ← instantiateMVars (← inferType hp)
      unless ts.isAppOfArity ``TimedSim 7 do throwError "the hypothesis `{hp}`"
      let (F, hA) ← withLocalDeclD `v (mkApp (mkConst ``Val) a) fun x => do
        pure (← mkLambdaFVars #[x] (ts.getArg! 5), ← mkLambdaFVars #[x] hp)
      pure (← mkAppOptM ``treeEntry (#[a, b, ha, hb, F].map some),
        ← mkAppOptM ``SimE.treeEntry (#[a, b, ha, hb, F, v, hA].map some))
    | some (.recFn ..) => throwError "the recursive results of a step are not in the environment"
    | none => do
      let hσ ← proveRed (mkApp (mkConst ``Ty.FO) σ)
      let p ← mkAppM ``Eq.symm #[← mkAppM ``Ty.hat_eq_val #[σ, hσ]]
      let u ← mkAppM ``cast #[p, v]
      pure (← mkAppM ``Ty.ofHat #[σ, u],
        ← mkAppM ``SimE.ofHat #[σ, ← mkAppM ``Sim.cast_self #[σ, hσ, v]])
  return (← mkAppM ``EnvHat.consE #[e, η'], ← mkAppM ``SimEnv.consE #[h', he])

/-- The number of calls in the D-term `e` (reduced to constructors, under `depth` binders of its
own) of a variable of the environment `ρ` that is a free function value (`Kind.freeFn`), and with
`unit` set also the calls of function variables on `unit`. -/
partial def countFree (kinds : Std.HashMap FVarId Kind) (ρ : Expr) (unit : Bool) (depth : Nat)
    (e : Expr) : MetaM Nat := do
  let .const n _ := e.getAppFn | return 0
  unless n.getPrefix == ``Tm do return 0
  let args := e.getAppArgs
  let sub (i : Nat) (extra : Nat) : MetaM Nat :=
    if h : i < args.size then countFree kinds ρ unit (depth + extra) args[i] else pure 0
  let here : MetaM Nat := do
    unless n == ``Tm.app && args.size == 5 do return 0
    let f := args[3]!
    unless f.isAppOfArity ``Tm.var 3 do return 0
    if unit then
      let a ← whnf args[1]!
      if a.isAppOfArity ``Ty.base 1 && (← whnf a.appArg!).isConstOf ``FTy.unit then return 1
    try
      let i ← varIdx (f.getArg! 2)
      if i < depth then return 0
      let v ← whnf (← envNth ρ (i - depth))
      let .fvar fv := v | return 0
      return match kinds[fv]? with
        | some (.freeFn ..) => 1
        | _ => 0
    catch _ => return 0
  let h ← here
  let rest ← match n with
    | ``Tm.lam => sub 3 1
    | ``Tm.letE => return (← sub 3 0) + (← sub 4 1)
    | ``Tm.case => return (← sub 4 0) + (← sub 5 1) + (← sub 6 1)
    | ``Tm.lcase => return (← sub 3 0) + (← sub 4 0) + (← sub 5 2)
    | _ => args.foldlM (fun acc a => return acc + (← countFree kinds ρ unit depth a)) 0
  return h + rest

/-- The route through the soundness theorem: for the D-term `t : Tm Γ τ` in the fragment
`Tm.InDtFrag` at a first-order type, the translated environment `η` of the telescope (`envHat`),
and the costed form `X`, prove `CostLeA (fun a b => cast _ a = b) e d (t.dtC cc η) X` by
`provePair` with the side goals closed by `closeSideD` up to the slack, and return
`Tm.timedSim_of_costLeA cc … : TimedSim (· = ·) 1 (t.allowC cc + (e + d)) X (t.eval ρ)` with the
allowance evaluated to a numeral and a note on the route. The charge `cc` of a call is
`callCost` when `t.allow` reduces to a numeral (`Tm.dt`, `Tm.allow`), else the charge `1` of every
call, whose allowance does not depend on the argument types. The slack is the number of calls of
free function values in `t`, at the charge `1` plus the number of calls on `unit`. -/
def dtRoute (kinds : Std.HashMap FVarId Kind) (t τ ρ X : Expr) :
    TermElabM (Expr × Nat × String) := do
  let hfrag ← proveRed (← mkAppM ``Tm.InDtFrag #[t])
  let hτ ← proveRed (mkApp (Lean.mkConst ``Ty.FO) τ)
  let allowE ← mkAppM ``Tm.allow #[t]
  let tyT := Lean.mkConst ``Ty
  let (cc, hcc, k, unit, noteK) ← match ← (evalNat (← reduce allowE)).run with
    | some k => pure (Lean.mkConst ``callCost, Lean.mkConst ``callCost_le_one, k, false, "")
    | none =>
      let cc := mkLambda `a .default tyT (mkNatLit 1)
      let hcc := mkLambda `a .default tyT (mkApp (Lean.mkConst ``Nat.le_refl) (mkNatLit 1))
      let allowCE ← mkAppM ``Tm.allowC #[cc, t]
      let some k ← (evalNat (← reduce allowCE)).run |
        throwError "neither the allowance{indentExpr allowE}\nnor the allowance at the charge \
          `1` of every call reduces to a numeral"
      pure (cc, hcc, k, true, "; `callCost` undecided, every call charged `1` (`Tm.dtC`)")
  let tR ← reduce t
  let slack ← countFree kinds ρ unit 0 tR
  let (η, hρ) ← envHat kinds ρ
  let p ← mkAppM ``Ty.hat_eq_val #[τ, hτ]
  let hatτ := mkApp (mkConst ``Ty.hat) τ
  let valτ := mkApp (mkConst ``Val) τ
  let S ← withLocalDeclD `a hatτ fun a => withLocalDeclD `b valτ fun b => do
    mkLambdaFVars #[a, b] (← mkEq (← mkAppM ``cast #[p, a]) b)
  let eM ← mkFreshExprMVar (mkConst ``Nat)
  let dM ← mkFreshExprMVar (mkConst ``Nat)
  let hX ← mkFreshExprMVar (mkAppN (mkConst ``CostLeA) #[hatτ, valτ, S, eM, dM,
    ← mkAppM ``Tm.dtC #[cc, t, η], X])
  let ((), _) ← (provePair hX.mvarId!).run { slack }
  let hX ← instantiateMVars hX
  if hX.hasMVar then
    let ms ← (← getMVars hX).mapM fun m => do pure m!"{← instantiateMVars (← m.getType)}"
    throwError "the comparison has unassigned parts of types{indentD (MessageData.joinSep
      ms.toList ", ")}"
  let e ← numeralD eM
  let d ← numeralD dM
  let noteD := if e + d == 0 then "" else
    s!"; the deficit {e + d} of the calls the costed form charges nothing for paid by the \
      allowance"
  return (← mkAppM ``Tm.timedSim_of_costLeA #[cc, hcc, t, hfrag, hτ, hρ, hX], k + (e + d),
    noteK ++ noteD)

/-- The leaf relation `fun a w => a = w` between the leaves `γ` of a costed tree and the values
`vτ` of their D type; the two types agree (an `Option` leaf, represented by `optEnc`, is
refused). -/
def eqRel (γ vτ : Expr) : MetaM Expr := do
  unless ← isDefEq γ vτ do
    throwError "link_timed: the leaves `{γ}` are not the values `{vτ}` of their D type"
  withLocalDeclD `a γ fun a => withLocalDeclD `w vτ fun w => do
    mkLambdaFVars #[a, w] (mkApp3 (mkConst ``Eq [1]) vτ a w)

/-- The leaf type `γ` of a type `… → SPTree γ` or `… → SPTree.Timed γ`. -/
def leafTy (T : Expr) : MetaM Expr :=
  forallTelescope T fun _ c => return c.appArg!

/-- The tree `T` that `link_timed x` links, a constant with the costed form `T.timed`, the D-term
`T.d` and its denotation theorem `T.d_den`: `x.tree` when it has the three (a reduction of
`derive_reduction`, a field `R.f` of a structure-valued reduction with its tree `R.f.tree`, a
step `S.start` of a multi-call simulator with its tree `S.start.tree`), else `x` (a definition
with the costed form `x.timed` of `derive_timed`, or a tree named in full). The name `x` need not
be a constant; both candidates are resolved in the current namespaces. -/
def resolveTree (x : Name) : CoreM Name := do
  let env ← getEnv
  let parts (t : Name) : List Name := [t ++ `timed, t ++ `d, t ++ `d_den]
  let cands := [x ++ `tree, x ++ `treeHat, x]
  let mut found : Array Name := #[]
  for c in cands do
    for (t, fs) in ← resolveGlobalName c do
      if fs.isEmpty && env.contains t then
        if (parts t).all env.contains then return t
        found := found.push t
  match found[0]? with
  | some t =>
    let missing := (parts t).filter (!env.contains ·)
    throwError "link_timed: `{t}` lacks {missing}; `derive_timed` gives `{t ++ `timed}` and \
      `reflect_d {t}` gives `{t ++ `d}` and `{t ++ `d_den}`"
  | none => throwError "link_timed: neither `{x ++ `tree}` nor `{x}` is a constant"

/-- Build the theorems `T.d_timedSim` and `T.d_cost_le` for the tree `T` (`resolveTree`). -/
partial def linkTimed (tree : Name) : TermElabM Unit := do
  let timedN := tree ++ `timed
  let dN := tree ++ `d
  let denN := tree ++ `d_den
  for n in [tree, timedN, dN, denN] do
    unless (← getEnv).contains n do throwError "link_timed: `{n}` does not exist"
  let nStat ← forallTelescope (← getConstInfo dN).type fun xs _ => pure xs.size
  forallTelescope (← getConstInfo denN).type fun xs stmt => do
    let statics := xs.extract 0 nStat
    let dBs := xs.extract (nStat + 1) xs.size
    let some (_, lhs, rhs) := stmt.eq? | throwError "link_timed: `{denN}` is not an equation"
    let la := lhs.getAppArgs
    let τ := la[1]!
    let rho := la[4]!
    let targs := rhs.appArg!.getAppArgs
    let rec go (j i : Nat) (tty : Expr) (tArgs binders : Array Expr)
        (kinds : Std.HashMap FVarId Kind) : TermElabM Unit := do
      if h : j < targs.size then
        let a := targs[j]
        -- A field of a record that `reflect_d` unbundles is a binder inside the argument.
        if i < dBs.size && !dBs.contains a && a.containsFVar dBs[i]!.fvarId! then
          return ← go j (i + 1) tty tArgs (binders.push dBs[i]!) kinds
        let some i' := dBs.findIdx? (· == a) |
          go (j + 1) i (tty.bindingBody!.instantiate1 a) (tArgs.push a) binders kinds
        unless i' == i do throwError "link_timed: the binders of `{denN}` are out of order"
        let .forallE tn T tb _ := tty | throwError "link_timed: `{timedN}` has too few binders"
        let xT ← inferType a
        let xn ← a.fvarId!.getUserName
        let triple ← if i + 2 < dBs.size then do
            let gT ← whnfR (← inferType dBs[i+1]!)
            pure (gT.isAppOf ``Val && (← inferType dBs[i+2]!).containsFVar a.fvarId!)
          else pure false
        if !triple then
          -- A binder that the D-term does not read (outside `ρ`), as a tree function whose
          -- costed form has another type, is the binder of the costed form.
          if !(← isDefEq T xT) && !(← instantiateMVars rho).containsFVar a.fvarId! then
            return ← withLocalDeclD tn T fun a' => do
              let tb := tb.instantiate1 a'
              if let .forallE cn cT cb _ := tb then
                if cn == tn.appendAfter "Cost" then
                  return ← withLocalDeclD cn cT fun fc =>
                    go (j + 1) (i + 1) (cb.instantiate1 fc) (tArgs ++ #[a', fc])
                      (binders ++ #[a', fc]) kinds
              go (j + 1) (i + 1) tb (tArgs.push a') (binders.push a') kinds
          unless ← isDefEq T xT do
            throwError "link_timed: the binder `{tn}` of `{timedN}` does not match `{xn}`"
          let tb := tb.instantiate1 a
          -- An unused function binder keeps its companion of `derive_timed` as a binder.
          if let .forallE cn cT cb _ := tb then
            if cn == tn.appendAfter "Cost" then
              return ← withLocalDeclD cn cT fun fc =>
                go (j + 1) (i + 1) (cb.instantiate1 fc) (tArgs ++ #[a, fc])
                  (binders ++ #[a, fc]) kinds
          go (j + 1) (i + 1) tb (tArgs.push a) (binders.push a) kinds
        else
          let lctx := (← getLCtx).setUserName dBs[i+1]!.fvarId! (xn.appendBefore "g")
          let insts ← getLocalInstances
          withLCtx lctx insts do
          let g := dBs[i+1]!
          let hden := dBs[i+2]!
          let gT ← inferType g
          let some (aτ, bτ) := (do
              let τg := gT.appArg!
              guard (τg.isAppOfArity ``Ty.arr 2)
              pure (τg.getArg! 0, τg.getArg! 1)) |
            throwError "link_timed: the D value of `{xn}` is not a function"
          let cod ← forallTelescope xT fun _ c => pure c
          if cod.isAppOf ``SPTree then
            let ds ← forallTelescope xT fun ys _ => pure ys.size
            withLocalDeclD tn T fun A' => do
            let tb := tb.instantiate1 A'
            let E ← eqRel (← leafTy T) (mkApp (mkConst ``Val) bτ)
            if ds == 0 then
              let hpT ← mkAppM ``TimedSim #[E, mkNatLit 1, mkNatLit 0,
                ← mkAppM ``Prod.mk #[mkNatLit 0, A'], mkApp g (mkConst ``Unit.unit)]
              withLocalDeclD (xn.appendBefore "h") hpT fun hp =>
                go (j + 1) (i + 3) tb (tArgs.push A') (binders ++ #[A', g, hp])
                  (kinds.insert g.fvarId! (.tree0 hp))
            else
              let .forallE cn cT cb _ := tb |
                throwError "link_timed: `{timedN}` has no companion for `{xn}`"
              withLocalDeclD cn cT fun AC => do
              let hT ← forallTelescope (← inferType hden) fun vs eq => do
                let some (_, _, r) := eq.eq? | throwError "link_timed: `{hden}`"
                let ps := r.appArg!.getAppArgs
                mkForallFVars vs (← mkAppM ``TimedSim #[E, mkNatLit 1, mkNatLit 0,
                  ← mkAppM ``Prod.mk #[mkAppN AC ps, mkAppN A' ps], mkApp g vs[0]!])
              withLocalDeclD (xn.appendBefore "h") hT fun hA =>
                go (j + 1) (i + 3) (cb.instantiate1 AC) (tArgs ++ #[A', AC])
                  (binders ++ #[A', AC, g, hA]) (kinds.insert g.fvarId! (.treeFn hA))
          else
            unless ← isDefEq T xT do
              throwError "link_timed: the binder `{tn}` of `{timedN}` does not match `{xn}`"
            let tb := tb.instantiate1 a
            let .forallE cn cT cb _ := tb |
              throwError "link_timed: `{timedN}` has no companion for `{xn}`"
            withLocalDeclD cn cT fun fc => do
            let FCT ← mkArrow (mkApp (mkConst ``Val) aτ) (mkConst ``Nat)
            withLocalDeclD (xn.appendAfter "DCost") FCT fun FC => do
            let (hgT, hFCT) ← forallTelescope (← inferType hden) fun vs eq => do
              let some (_, _, r) := eq.eq? | throwError "link_timed: `{hden}`"
              let v := vs[0]!
              let e1 ← mkEq (mkApp g v)
                (← mkAppM ``stepN #[mkConst ``CTree.tick, mkApp FC v, r])
              let e2 ← mkAppM ``LE.le #[mkApp FC v, mkAppN fc r.appArg!.getAppArgs]
              return (← mkForallFVars vs e1, ← mkForallFVars vs e2)
            withLocalDeclD (xn.appendBefore "h") hgT fun hg =>
            withLocalDeclD ((xn.appendAfter "Cost").appendBefore "h") hFCT fun hFC =>
              go (j + 1) (i + 3) (cb.instantiate1 fc) (tArgs ++ #[a, fc])
                (binders ++ #[a, fc, g, FC, hg, hFC]) (kinds.insert g.fvarId! (.dataFn hg hFC))
      else if i + 1 < dBs.size then
        -- A class method of `reflect_d`: a data function value `g` without a source binder,
        -- priced at the unit step of its application (cost `0` beyond it).
        let g := dBs[i]!
        let hden := dBs[i+1]!
        let gT ← whnfR (← inferType g)
        let τg := gT.appArg!
        unless gT.isAppOf ``Val && τg.isAppOfArity ``Ty.arr 2 do
          throwError "link_timed: the binder `{g}` of `{denN}` is not a method value"
        let aτ := τg.getArg! 0
        let (hgT, hFCT, mn) ← withLocalDeclD `FC
            (← mkArrow (mkApp (mkConst ``Val) aτ) (mkConst ``Nat)) fun FC => do
          forallTelescope (← inferType hden) fun vs eq => do
            let some (_, _, r) := eq.eq? | throwError "link_timed: `{hden}`"
            unless r.isAppOf ``CTree.ret do
              throwError "link_timed: the method value `{g}` of `{denN}` is a program of a \
                record{indentExpr r}"
            let v := vs[0]!
            let e1 ← mkEq (mkApp g v) (← mkAppM ``stepN #[mkConst ``CTree.tick, mkApp FC v, r])
            let e2 ← mkAppM ``LE.le #[mkApp FC v, mkNatLit 0]
            let mn := match r.appArg!.getAppFn.constName? with
              | some (.str _ s) => Name.mkSimple s
              | _ => `method
            return (← mkLambdaFVars #[FC] (← mkForallFVars vs e1),
              ← mkLambdaFVars #[FC] (← mkForallFVars vs e2), mn)
        let free ← forallTelescope (← inferType hden) fun vs eq => do
          let some (_, _, r) := eq.eq? | return false
          isPairMap vs[0]! r.appArg!
        let lctx := (← getLCtx).setUserName g.fvarId! (mn.appendBefore "g")
        withLCtx lctx (← getLocalInstances) do
        withLocalDeclD (mn.appendAfter "DCost")
            (← mkArrow (mkApp (mkConst ``Val) aτ) (mkConst ``Nat)) fun FC =>
        withLocalDeclD (mn.appendBefore "h") (hgT.beta #[FC]) fun hg =>
        withLocalDeclD ((mn.appendAfter "Cost").appendBefore "h") (hFCT.beta #[FC]) fun hFC =>
          go j (i + 2) tty tArgs (binders ++ #[g, FC, hg, hFC])
            (kinds.insert g.fvarId! (if free then .freeFn hg hFC else .dataFn hg hFC))
      else
        let timedApp := mkAppN (mkConst timedN) tArgs
        let dC := mkAppN (mkConst dN) statics
        let γ := (← whnfR (← inferType timedApp)).appArg!.appArg!
        let E ← eqRel γ (mkApp (mkConst ``Val) τ)
        let one := mkNatLit 1
        let some Xunf ← unfoldDefinition? timedApp |
          throwError "link_timed: `{timedN}` does not unfold"
        let some tunf ← unfoldDefinition? dC | throwError "link_timed: `{dN}` does not unfold"
        let s ← saveState
        let viaDt : Except MessageData (Expr × Nat × String) ← try
            pure (.ok (← dtRoute kinds dC τ rho timedApp))
          catch ex => do
            s.restore
            pure (.error ex.toMessageData)
        let dtWhy : MessageData := match viaDt with
          | .error m => m
          | .ok _ => m!""
        let (pf, k, route) ← match viaDt.toOption with
          | some (pf, k, note) =>
            pure (pf, k, s!"through the soundness theorem `Tm.dt_timedSim`{note}")
          | none => do
            try
              let n ← mkFreshExprMVar (mkConst ``Nat)
              let main ← mkFreshExprMVar
                (← mkAppM ``TSim #[E, one, n, Xunf.headBeta, tunf.headBeta, rho])
              let ((), sides) ← ((solveT main.mvarId!).run kinds).run #[]
              for sg in sides.reverse do solveSide sg
              let nv ← instantiateMVars n
              let some k ← (evalNat nv).run |
                throwError "link_timed: the allowance{indentExpr nv}\nis not a numeral"
              let pf ← instantiateMVars main
              if pf.hasMVar then
                throwError "link_timed: the derivation has unassigned parts{indentExpr pf}"
              let why := ((← dtWhy.toString).replace "\n" " ").take 300
              pure (pf, k, s!"by the walk; the soundness theorem does not apply: {why}")
            catch ex =>
              throwError "{ex.toMessageData}\nlink_timed: the route through the soundness \
                theorem `Tm.dt_timedSim` does not apply either: {dtWhy}"
        let stmtT ← mkAppM ``TimedSim
          #[E, one, mkNatLit k, timedApp, ← mkAppM ``Tm.eval #[dC, rho]]
        let allB := statics ++ binders
        let type ← instantiateMVars (← mkForallFVars allB stmtT)
        let value ← instantiateMVars (← mkLambdaFVars allB (← mkExpectedTypeHint pf stmtT))
        let thm := tree ++ `d_timedSim
        addDecl <| .thmDecl { name := thm, levelParams := [], type, value }
        addDocStringCore thm s!"The costed tree `{timedN}` simulates the evaluation of `{dN}` \
          at factor `1` and allowance `{k}`, proved by `link_timed` {route}."
        let costT ← mkAppM ``LE.le #[← mkAppM ``Tm.cost #[dC, rho],
          ← mkAppM ``HAdd.hAdd #[mkNatLit k, ← mkAppM ``HMul.hMul #[one,
            ← mkAppM ``SPTree.Timed.stepTime #[timedApp]]]]
        let cpf ← mkAppM ``TSim.cost_le #[mkAppN (mkConst thm) allB]
        let ctype ← instantiateMVars (← mkForallFVars allB costT)
        let cvalue ← instantiateMVars (← mkLambdaFVars allB (← mkExpectedTypeHint cpf costT))
        let cthm := tree ++ `d_cost_le
        addDecl <| .thmDecl { name := cthm, levelParams := [], type := ctype, value := cvalue }
        addDocStringCore cthm s!"The cost of `{dN}`: the allowance `{k}` plus the time of \
          `{timedN}`, proved by `link_timed`."
        if viaDt.toOption.isSome then
          let qf ← mkAppM ``CTree.QueryFree #[← mkAppM ``Tm.eval #[dC, rho]]
          withLocalDeclD `O (mkConst ``CTree.Oracle) fun O =>
          withLocalDeclD `hq qf fun hq => do
            let rpf ← mkAppM ``TimedSim.run_eq #[mkAppN (mkConst thm) allB, hq, O]
            let rT ← instantiateMVars (← inferType rpf)
            let rB := allB ++ #[O, hq]
            let rthm := tree ++ `d_run
            let rType ← instantiateMVars (← mkForallFVars rB rT)
            let rValue ← instantiateMVars (← mkLambdaFVars rB rpf)
            addDecl <| .thmDecl { name := rthm, levelParams := [], type := rType, value := rValue }
            addDocStringCore rthm s!"At a query-free evaluation, `{dN}` means the compiled \
              erasure of `{timedN}`, proved by `link_timed` through the soundness theorem \
              `Tm.dt_timedSim`."
    go 0 0 (← inferType (mkConst timedN)) #[] #[] {}

/-- `link_timed x` proves `T.d_timedSim`, the simulation of the evaluation of the D-term `T.d` of
`reflect_d` by the costed tree `T.timed`, and `T.d_cost_le`, the cost of `T.d` by the time of
`T.timed`, for the tree `T` that `x` names: `x.tree` for a reduction `x` of `derive_reduction`, a
field `x = R.f` of a structure-valued reduction or a step `x = S.start` of a multi-call
simulator, and `x` for a definition with the costed form `x.timed` of `derive_timed`. -/
syntax (name := linkTimedCmd) "link_timed " ident : command

@[command_elab linkTimedCmd, inherit_doc linkTimedCmd]
def elabLinkTimed : CommandElab := fun stx => do
  let T ← liftCoreM <| resolveTree stx[1].getId
  liftTermElabM (linkTimed T)

end CatCrypt.Complexity.D.LinkTimed

end

end
