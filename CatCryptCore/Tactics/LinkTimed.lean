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

/-!
# `link_timed`: the costed tree of a reduction simulates its reflected D-term

For a reduction `R` with the tree `R.tree` of `derive_reduction`, its costed form `R.tree.timed`
of `derive_timed` and its D-term `R.tree.d` of `reflect_d`, the command `link_timed R` proves

* `R.tree.d_timedSim`: `TimedSim (fun a w => a = w) 1 n (R.tree.timed …) ((R.tree.d …).eval ρ)`
  for a numeral allowance `n` computed by the derivation, and
* `R.tree.d_cost_le`: `(R.tree.d …).cost ρ ≤ n + 1 * SPTree.Timed.stepTime (R.tree.timed …)`,
  by `TSim.cost_le`.

## The telescope

The binders are read off `R.tree.d_den`, whose environment `ρ` is the environment of the
statement, and aligned with the binders of `R.tree.timed`:

* a type parameter is the finite ground type of `reflect_d` (`MF : FTy` at `MF.den`);
* a data binder and an unused binder are kept;
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
  `derive_timed` charges a method of a local instance.

## The walk

The proof is a walk over the D-term, one rule of `CatCryptCore.Complexity.D.TimedLink` per
construct, against the unfolded value of `R.tree.timed`: `letE` of a sample, get or set, of a
data term (`TSim.letE`) or of a computation (`TSim.bind`), a call of a tree function value with
arguments (`TSim.call`) or on `unit` (`TSim.call0`), `ite`, `fail`, and a data leaf
(`TSim.ret`); data terms by `DSim.var`, `lit`, `natLit`, `pair`, `fst`, `snd`, `letE`, `prim`
(and `decide` for the atom of a condition) and `app` of a data function value. At each tree node
the costed tree of the goal is replaced by its tree under a fresh step cost (`TSim.conv`); the
step-cost inequalities are collected and closed once the walk has assigned the costed trees,
innermost first: an undetermined step cost is set to the other side or to `0`, the others are
closed by `omega`. Any other construct is refused with a message naming it, as are operations on
`ℕ` and leaves whose type differs from their D representation (`Option`).

## Main definitions

* `link_timed R`: the command.

## Main results

* `TimedLink.TSim.conv`: the costed tree of a goal against its tree under a smaller step cost.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Complexity.D.TimedLink

open CatCrypt.Core

variable {Γ : List Ty} {ρ : Env Γ} {α : Type} {τ : Ty} {K : ℕ}

/-- A costed tree `X` simulates whatever its tree simulates under a step cost at most that of
`X`. -/
theorem TSim.conv {E : α → Val τ → Prop} {n c : ℕ} {X : ℕ × SPTree.Timed α} {t : Tm Γ τ}
    (h : TSim E K n (c, X.2) t ρ) (hc : c ≤ X.1) : TSim E K n X t ρ :=
  TSim.le_fst hc h

end CatCrypt.Complexity.D.TimedLink

meta section

namespace CatCrypt.Complexity.D.LinkTimed

open Lean Elab Meta Term Command CatCrypt.Core CatCrypt.Complexity.D TimedLink

/-- The hypothesis attached to a D function value of the environment. -/
inductive Kind where
  /-- A data function value: its step equation `hg` and the bound `hFC` of its cost. -/
  | dataFn (hg hFC : Expr)
  /-- A tree function value with arguments, simulated by the costed tree (`hA`). -/
  | treeFn (hA : Expr)
  /-- A tree function value on `unit`, simulated by the costed tree (`hp`). -/
  | tree0 (hp : Expr)
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
  match e.getAppFn.constName?, e.getAppNumArgs with
  | some ``Tm.var, 3 => return true
  | some ``Tm.lit, 3 => return true
  | some ``Tm.natLit, 2 => return true
  | some ``Tm.pair, 5 => return (← isData ρ loc (e.getArg! 3)) && (← isData ρ loc (e.getArg! 4))
  | some ``Tm.fst, 4 => isData ρ loc (e.getArg! 3)
  | some ``Tm.snd, 4 => isData ρ loc (e.getArg! 3)
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
    | some (.dataFn ..) => isData ρ loc (e.getArg! 4)
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
  | some ``Tm.letE, 5 =>
    let m ← applyRule g ``DSim.letE
    solveD (← arg m `he).mvarId!
    solveD (← arg m `hb).mvarId!
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
    | _ => failL m!"the application `{t}` is not a call of a data function value"
  | _, _ => failL m!"the data construct `{t.getAppFn}` is outside the fragment of link_timed"

/-- Derive the `DSim` goal `g` of the condition of a conditional: an operation at its head is a
decision atom (`DSim.decide`). -/
partial def solveCond (g : MVarId) : LinkM Unit := g.withContext do
  let as ← dsimArgs (← g.getType)
  let t ← instantiateMVars as[5]!
  unless t.isAppOfArity ``Tm.prim 5 do return ← solveD g
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
    closeWith (← arg m `hE) (← mkEqRefl (← instantiateMVars (← arg m `a)))
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
        let m ← applyRule (← conv g) ``TSim.bind (splitPair · `x)
        solveT (← arg m `hs).mvarId!
        let (_, g1) ← (← arg m `hk).mvarId!.intro1
        let (_, g2) ← g1.intro1
        let (h, g3) ← g2.intro1
        solveT (← Lean.Meta.subst g3 h)
  | some ``Tm.app, 5 =>
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
    solveT (← arg m `ht).mvarId!
    solveT (← arg m `he).mvarId!
    side (← arg m `hc)
  | _, _ =>
    if ← isData ρ 0 t then ret g
    else failL m!"the tree construct `{t.getAppFn}` is outside the fragment of link_timed"

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
  let gs ← Tactic.run g do
    Tactic.evalTactic (← `(tactic| first
      | omega
      | (dsimp only [SPTree.Timed.delay, Val, Prim.apply, Equiv.refl_apply]; omega)))
  unless gs.isEmpty do
    throwError "link_timed: the step-cost inequality{indentExpr ty}\nis not closed"

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

/-- Build the theorems `R.tree.d_timedSim` and `R.tree.d_cost_le`. -/
def linkTimed (R : Name) : TermElabM Unit := do
  let tree := R ++ `tree
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
          unless ← isDefEq T xT do
            throwError "link_timed: the binder `{tn}` of `{timedN}` does not match `{xn}`"
          go (j + 1) (i + 1) (tb.instantiate1 a) (tArgs.push a) (binders.push a) kinds
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
            let v := vs[0]!
            let e1 ← mkEq (mkApp g v) (← mkAppM ``stepN #[mkConst ``CTree.tick, mkApp FC v, r])
            let e2 ← mkAppM ``LE.le #[mkApp FC v, mkNatLit 0]
            let mn := match r.appArg!.getAppFn.constName? with
              | some (.str _ s) => Name.mkSimple s
              | _ => `method
            return (← mkLambdaFVars #[FC] (← mkForallFVars vs e1),
              ← mkLambdaFVars #[FC] (← mkForallFVars vs e2), mn)
        let lctx := (← getLCtx).setUserName g.fvarId! (mn.appendBefore "g")
        withLCtx lctx (← getLocalInstances) do
        withLocalDeclD (mn.appendAfter "DCost")
            (← mkArrow (mkApp (mkConst ``Val) aτ) (mkConst ``Nat)) fun FC =>
        withLocalDeclD (mn.appendBefore "h") (hgT.beta #[FC]) fun hg =>
        withLocalDeclD ((mn.appendAfter "Cost").appendBefore "h") (hFCT.beta #[FC]) fun hFC =>
          go j (i + 2) tty tArgs (binders ++ #[g, FC, hg, hFC])
            (kinds.insert g.fvarId! (.dataFn hg hFC))
      else
        let timedApp := mkAppN (mkConst timedN) tArgs
        let dC := mkAppN (mkConst dN) statics
        let γ := (← whnfR (← inferType timedApp)).appArg!.appArg!
        let E ← eqRel γ (mkApp (mkConst ``Val) τ)
        let one := mkNatLit 1
        let some Xunf ← unfoldDefinition? timedApp |
          throwError "link_timed: `{timedN}` does not unfold"
        let some tunf ← unfoldDefinition? dC | throwError "link_timed: `{dN}` does not unfold"
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
        let stmtT ← mkAppM ``TimedSim
          #[E, one, mkNatLit k, timedApp, ← mkAppM ``Tm.eval #[dC, rho]]
        let allB := statics ++ binders
        let type ← instantiateMVars (← mkForallFVars allB stmtT)
        let value ← instantiateMVars (← mkLambdaFVars allB (← mkExpectedTypeHint pf stmtT))
        let thm := tree ++ `d_timedSim
        addDecl <| .thmDecl { name := thm, levelParams := [], type, value }
        addDocStringCore thm s!"The costed tree `{timedN}` simulates the evaluation of `{dN}` \
          at factor `1` and allowance `{k}`, proved by `link_timed`."
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
    go 0 0 (← inferType (mkConst timedN)) #[] #[] {}

/-- `link_timed R` proves `R.tree.d_timedSim`, the simulation of the evaluation of the D-term
`R.tree.d` of `reflect_d` by the costed tree `R.tree.timed` of `derive_reduction`, and
`R.tree.d_cost_le`, the cost of `R.tree.d` by the time of `R.tree.timed`. -/
syntax (name := linkTimedCmd) "link_timed " ident : command

@[command_elab linkTimedCmd, inherit_doc linkTimedCmd]
def elabLinkTimed : CommandElab := fun stx => do
  let R ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo stx[1]
  liftTermElabM (linkTimed R)

end CatCrypt.Complexity.D.LinkTimed

end

end
