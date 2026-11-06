/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCSimulatorCostPotComp
public import CatCryptCore.Tactics.DeriveTimeBound

/-!
# Potentials of costed states and potential time bounds of costed multi-call simulators

The class `StatePotential σ` gives a size measure `pot : σ → ℕ` and an invariant `inv : σ → Prop`
on a type of states or messages. It is defined by structure recursion over the types of the costed
states that `derive_reduction` produces:

| type | `pot` | `inv` |
|---|---|---|
| `ℕ` | its value (a declared price) | `True` |
| `Unit`, `Bool` | `0` | `True` |
| `α × β` | `pot a + pot b` | both |
| `α ⊕ β`, `Option α` | the potential of the present part (`0` for `none`) | of the present part |
| `List α` | the length plus the potentials of the elements | of every element |
| `K → α` | `⨆ x, pot (f x)`, a companion's largest value | `pot ∘ f` bounded, every value |

A user instance overrides the derived one for a type the recursion does not cover (a structure
state on plain states). The import measures of the messages are read from the same class: a
message `x` received carries the import `κ + pot x`, a message passed on the import `pot x` or `0`.
The class `PotLeSize X` (`pot x + 1 ≤ ImportSize.size x`, derived for the same types) makes the
import measures linear in the size (`ImportLinear`).

## The rule of `derive_hybrid_time (potential) R`

For the costed form `R.timed : … → MultiHybrid.Timed σ E O EG OG` of a multi-call simulator whose
step theorems `R.st.tree.timeBound_timed` (or `R.st.treeHat.timeBound_timed`) exist, with
instances `StatePotential` on `σ`, `E`, `O`, `EG`, `OG`, the command defines

`R.potentialBound_timed : … → (R.timed …).PotentialBound gE gO hEG hO a b`

with the invariant `inv` and the potential `pot` of `σ`, the imports `gE e = κE + pot e`,
`gO o = κO + pot o` received, and the imports `hEG`, `hO` passed on, each `pot` or `0`. Its class
of simulators: the step bounds, as the step theorems state them, are sums of constants, terms not
depending on the state or the input, and terms depending on them, each with a numeral coefficient,
after the equations and bounds of the registered costs (`AutoTime.addCostFacts`) and the length
equations (`AutoTime.addLengthFacts`); every term depending on the state or the input is a
summand of the potential of the state or the input, or a value at a point of a function component
of the state; and each step changes the state so that, after the simplification by the equations
of `pot` and `inv`, of `Function.update`, of lists and of `if`, the potential clause is a linear
inequality over these summands and suprema of function components that are updated pointwise
(`cons`, `append` of the input or of state data, `Function.update` with a cost companion, the
assignment of a number read from the input).

* The constants: `a` is the largest constant part of the three step bounds (their sum when one of
  them is not a numeral), `b` the largest sum of their coefficients. The step bound
  `B s x ≤ a + b * (pot s + g x)` is proved by `omega` from the cost and length facts and the
  facts `G t ≤ ⨆ G` for the function components `G` of the state.
* The potential clause `AllRet (fun y => inv y.1 ∧ pot y.1 + h y.2 ≤ pot s + g x)` of each step
  is proved by unfolding the costed tree, splitting its matches, and closing every leaf by the
  closer `potClose`: a supremum of a new function component is bounded by `⨆ x, F x ≤ U`, `U` the
  pointwise bound of `F x` in which every value `G x` of a function component of the state is
  replaced by its supremum and an `if` by the maximum of its branches; then `omega`.
* `κE` is the least number up to `κMax` (`16`) for which the clause of `start` closes, `κO` that
  for `resume` and `finish` (the clause is monotone in `κ`, so the search is a bisection); the
  measures passed on are `pot` on both inner events and outer outputs when the clauses close with
  them, else `0` on the outer outputs, else `0` on the inner events, else `0` on both.

A step whose clause does not close for `κ = κMax` under the four choices is refused, with an
error that names the step, the potential clause and the leaf goal left open; a step bound with a
term not bounded by the potential is refused with the step and the bound.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core

/-- A size measure `pot` and an invariant `inv` on the states or messages of type `σ`: the
potential of a costed state and the import of a message. -/
class StatePotential (σ : Type) where
  /-- The potential of a state, the import of a message. -/
  pot : σ → ℕ
  /-- The invariant under which the potential bounds the size of the state. -/
  inv : σ → Prop

namespace StatePotential

/-- A number has the potential of its value: a declared price is counted in unary. -/
instance instNat : StatePotential ℕ := ⟨fun n => n, fun _ => True⟩

/-- The unit has the potential `0`. -/
instance instUnit : StatePotential Unit := ⟨fun _ => 0, fun _ => True⟩

/-- A boolean has the potential `0`. -/
instance instBool : StatePotential Bool := ⟨fun _ => 0, fun _ => True⟩

/-- A pair has the sum of the potentials of its components. -/
instance instProd {α β : Type} [StatePotential α] [StatePotential β] :
    StatePotential (α × β) :=
  ⟨fun p => pot p.1 + pot p.2, fun p => inv p.1 ∧ inv p.2⟩

/-- A sum has the potential of its present part. -/
instance instSum {α β : Type} [StatePotential α] [StatePotential β] :
    StatePotential (α ⊕ β) :=
  ⟨Sum.elim pot pot, Sum.elim inv inv⟩

/-- An option has the potential of its present part, `0` for `none`. -/
instance instOption {α : Type} [StatePotential α] : StatePotential (Option α) :=
  ⟨fun o => o.elim 0 pot, fun o => ∀ a, o = some a → inv a⟩

/-- A list has its length plus the potentials of its elements. -/
instance instList {α : Type} [StatePotential α] : StatePotential (List α) :=
  ⟨fun l => l.length + (l.map pot).sum, fun l => ∀ a ∈ l, inv a⟩

/-- A function has the supremum of the potentials of its values, under the invariant that they
are bounded above: a cost companion `K → ℕ` has the supremum of its values. -/
noncomputable instance instFun {K α : Type} [StatePotential α] : StatePotential (K → α) :=
  ⟨fun f => ⨆ x, pot (f x), fun f => BddAbove (Set.range fun x => pot (f x)) ∧ ∀ x, inv (f x)⟩

variable {α β K : Type} [StatePotential α] [StatePotential β]

@[simp] theorem pot_nat (n : ℕ) : pot n = n := rfl
@[simp] theorem pot_nat_fun : (pot : ℕ → ℕ) = fun n => n := rfl
@[simp] theorem inv_nat (n : ℕ) : inv n ↔ True := Iff.rfl
@[simp] theorem pot_unit (u : Unit) : pot u = 0 := rfl
@[simp] theorem inv_unit (u : Unit) : inv u ↔ True := Iff.rfl
@[simp] theorem pot_bool (b : Bool) : pot b = 0 := rfl
@[simp] theorem inv_bool (b : Bool) : inv b ↔ True := Iff.rfl
@[simp] theorem pot_prod (p : α × β) : pot p = pot p.1 + pot p.2 := rfl
@[simp] theorem inv_prod (p : α × β) : inv p ↔ inv p.1 ∧ inv p.2 := Iff.rfl
@[simp] theorem pot_inl (a : α) : pot (Sum.inl a : α ⊕ β) = pot a := rfl
@[simp] theorem pot_inr (b : β) : pot (Sum.inr b : α ⊕ β) = pot b := rfl
@[simp] theorem inv_inl (a : α) : inv (Sum.inl a : α ⊕ β) ↔ inv a := Iff.rfl
@[simp] theorem inv_inr (b : β) : inv (Sum.inr b : α ⊕ β) ↔ inv b := Iff.rfl
@[simp] theorem pot_some (a : α) : pot (some a) = pot a := rfl
@[simp] theorem pot_none : pot (none : Option α) = 0 := rfl
@[simp] theorem inv_some (a : α) : inv (some a) ↔ inv a := by
  simp only [inv, Option.some.injEq, forall_eq']
@[simp] theorem inv_none : inv (none : Option α) ↔ True := by
  simp only [inv, reduceCtorEq, false_implies, implies_true]
@[simp] theorem pot_list (l : List α) : pot l = l.length + (l.map pot).sum := rfl
@[simp] theorem inv_list (l : List α) : inv l ↔ ∀ a ∈ l, inv a := Iff.rfl
@[simp] theorem pot_fun (f : K → α) : pot f = ⨆ x, pot (f x) := rfl
@[simp] theorem inv_fun (f : K → α) :
    inv f ↔ BddAbove (Set.range fun x => pot (f x)) ∧ ∀ x, inv (f x) := Iff.rfl

/-- The sum of the potentials passed on with an output of a step is the potential of the sum. -/
@[simp] theorem sum_elim_pot (z : α ⊕ β) : Sum.elim pot pot z = pot z := rfl

/-- A family of numbers bounded pointwise by `U` is bounded above. -/
theorem bddAbove_range_of_le {ι : Type} {F : ι → ℕ} (U : ℕ) (h : ∀ x, F x ≤ U) :
    BddAbove (Set.range F) :=
  ⟨U, by rintro _ ⟨x, rfl⟩; exact h x⟩

/-- A supremum of numbers bounded pointwise by `U` is at most `U`. -/
theorem iSup_le_of_le {ι : Type} {F : ι → ℕ} (U : ℕ) (h : ∀ x, F x ≤ U) : (⨆ x, F x) ≤ U :=
  ciSup_le' h

/-- A value of a family bounded above is at most its supremum. -/
theorem le_iSup_of_bdd {ι : Type} {F : ι → ℕ} (h : BddAbove (Set.range F)) (x : ι) :
    F x ≤ ⨆ i, F i :=
  le_ciSup h x

end StatePotential

/-- The potential of a message is less than its size: the import measures `κ + pot` are linear
in the size of the message (`ImportLinear`). -/
class PotLeSize (X : Type) [StatePotential X] [ImportSize X] : Prop where
  /-- The potential of a message is less than its size. -/
  pot_lt : ∀ x : X, StatePotential.pot x + 1 ≤ ImportSize.size x

namespace PotLeSize

open StatePotential ImportSize

instance instNat : PotLeSize ℕ := ⟨fun n => by simp [size]⟩
instance instUnit : PotLeSize Unit := ⟨fun _ => le_rfl⟩
instance instBool : PotLeSize Bool := ⟨fun _ => le_rfl⟩

instance instProd {α β : Type} [StatePotential α] [StatePotential β] [ImportSize α]
    [ImportSize β] [PotLeSize α] [PotLeSize β] : PotLeSize (α × β) :=
  ⟨fun p => by
    have := pot_lt p.1
    have := pot_lt p.2
    simp only [pot_prod, size]
    omega⟩

instance instSum {α β : Type} [StatePotential α] [StatePotential β] [ImportSize α]
    [ImportSize β] [PotLeSize α] [PotLeSize β] : PotLeSize (α ⊕ β) :=
  ⟨fun z => by
    rcases z with a | b
    · have := pot_lt a
      simp only [pot_inl, size, Sum.elim_inl]
      omega
    · have := pot_lt b
      simp only [pot_inr, size, Sum.elim_inr]
      omega⟩

instance instOption {α : Type} [StatePotential α] [ImportSize α] [PotLeSize α] :
    PotLeSize (Option α) :=
  ⟨fun o => by
    rcases o with _ | a
    · simp [size]
    · have := pot_lt a
      simp only [pot_some, size, Option.elim_some]
      omega⟩

instance instList {α : Type} [StatePotential α] [ImportSize α] [PotLeSize α] :
    PotLeSize (List α) :=
  ⟨fun l => by
    induction l with
    | nil => simp [size]
    | cons a l ih =>
      have := pot_lt a
      simp only [pot_list, size, List.length_cons, List.map_cons, List.sum_cons] at ih ⊢
      omega⟩

end PotLeSize

/-- Import measures at most `k` plus the potential of the message are linear in the size, with
the constant `k + 1`. -/
theorem ImportLinear.of_le_pot {E OG : Type} [StatePotential E] [StatePotential OG]
    [ImportSize E] [ImportSize OG] [PotLeSize E] [PotLeSize OG] {gE : E → ℕ} {gO : OG → ℕ}
    (k : ℕ) (hE : ∀ e, gE e ≤ k + StatePotential.pot e)
    (hO : ∀ o, gO o ≤ k + StatePotential.pot o) : ImportLinear gE gO (k + 1) := by
  refine ⟨fun e => ?_, fun o => ?_⟩
  · have := PotLeSize.pot_lt e
    have := hE e
    have := ImportSize.one_le e
    have : k ≤ k * ImportSize.size e := Nat.le_mul_of_pos_right k this
    rw [Nat.add_mul, Nat.one_mul]
    omega
  · have := PotLeSize.pot_lt o
    have := hO o
    have := ImportSize.one_le o
    have : k ≤ k * ImportSize.size o := Nat.le_mul_of_pos_right k this
    rw [Nat.add_mul, Nat.one_mul]
    omega

end CatCrypt.Crypto.UCTransparent

public section

namespace CatCrypt.Tactics.StatePotential

open Lean Meta Elab Term Tactic
open CatCrypt.Crypto.UCTransparent

meta section

/-- The largest import created per message that the search of `κ` tries. -/
def κMax : Nat := 16

/-- The simplification lemmas of the potential clause: the equations of `pot` and `inv`, of
`Function.update`, of lists, of `if` and of the leaves of costed trees. -/
def potSimpLemmas : Array Name :=
  #[``StatePotential.pot_nat, ``StatePotential.pot_nat_fun, ``StatePotential.inv_nat,
    ``StatePotential.pot_unit, ``StatePotential.inv_unit, ``StatePotential.pot_bool,
    ``StatePotential.inv_bool, ``StatePotential.pot_prod, ``StatePotential.inv_prod,
    ``StatePotential.pot_inl, ``StatePotential.pot_inr, ``StatePotential.inv_inl,
    ``StatePotential.inv_inr, ``StatePotential.pot_some, ``StatePotential.pot_none,
    ``StatePotential.inv_some, ``StatePotential.inv_none, ``StatePotential.pot_list,
    ``StatePotential.inv_list, ``StatePotential.pot_fun, ``StatePotential.inv_fun,
    ``StatePotential.sum_elim_pot, ``Sum.elim_inl, ``Sum.elim_inr, ``Function.update_apply,
    ``apply_ite, ``List.length_append, ``List.length_cons, ``List.length_nil, ``List.map_append,
    ``List.map_cons, ``List.map_nil, ``List.sum_append, ``List.sum_cons, ``List.sum_nil,
    ``List.map_id', ``List.mem_append, ``List.mem_cons, ``CatCrypt.Core.SPTree.Timed.AllRet,
    ``CatCrypt.Core.SPTree.Timed.delay, ``CatCrypt.Core.SPTree.Timed.bind, ``Prod.fst, ``Prod.snd,
    ``and_true, ``true_and,
    ``implies_true, ``forall_const, ``Nat.add_zero, ``Nat.zero_add, ``ite_true, ``ite_false,
    ``Pi.zero_apply, ``Pi.one_apply, ``Nat.zero_max, ``Nat.max_zero, ``ite_self, ``dite_eq_ite]

/-- The subterms of `e` with no loose bound variable. -/
partial def closedSubterms (e : Expr) : Array Expr :=
  go #[e] #[]
where
  /-- Visit the terms of `todo`. -/
  go (todo acc : Array Expr) : Array Expr :=
    if h : todo.size > 0 then
      let t := todo.back
      let todo := todo.pop
      let acc := if t.hasLooseBVars then acc else acc.push t
      match t with
      | .app f a => go (todo.push f |>.push a) acc
      | .lam _ d b _ => go (todo.push d |>.push b) acc
      | .forallE _ d b _ => go (todo.push d |>.push b) acc
      | .mdata _ b => go (todo.push b) acc
      | .letE _ t v b _ => go (todo.push t |>.push v |>.push b) acc
      | .proj _ _ b => go (todo.push b) acc
      | _ => go todo acc
    else acc

/-- The applications `G t` in `e`, with no loose bound variable, of the functions `G` of the
hypotheses `BddAbove (Set.range G)` of the context, each with the fact `G t ≤ ⨆ i, G i`. -/
def supFacts (bdds : Array (Expr × Expr)) (e : Expr) : MetaM (Array Expr) := do
  let mut out := #[]
  let mut seen : Array Expr := #[]
  for t in closedSubterms e do
    unless t.isApp do continue
    if seen.contains t then continue
    unless (← inferType t).isConstOf ``Nat do continue
    for (G, hB) in bdds do
      let dom := (← inferType G).bindingDomain!
      let x ← mkFreshExprMVar dom
      let s ← saveState
      if ← withReducible (isDefEq (G.beta #[x]) t) then
        let x ← instantiateMVars x
        if !x.hasExprMVar then
          out := out.push (← mkAppM ``StatePotential.le_iSup_of_bdd #[hB, x])
          seen := seen.push t
          break
      s.restore
  return out

/-- The hypotheses `BddAbove (Set.range G)` of the local context, each with its function `G`. -/
def bddHyps : MetaM (Array (Expr × Expr)) := do
  let mut out := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOfArity ``BddAbove 3 then
      let r := ty.appArg!
      if r.isAppOfArity ``Set.range 3 then out := out.push (r.appArg!, d.toExpr)
  return out

/-- The pointwise bound of the value `e` at the point `x` of a new function component: `e` when
it does not mention `x`, the sum of the bounds for a sum, a multiple by a numeral, the maximum of
the bounds of the branches of an `if` and of a `max`, and the supremum `⨆ i, G i` for a value `G x`
of a function component `G` of the state (a hypothesis `BddAbove (Set.range G)`). -/
partial def supAbstract (bdds : Array (Expr × Expr)) (x e : Expr) : MetaM Expr := do
  let e := e.headBeta
  if !e.containsFVar x.fvarId! then return e
  if e.isAppOfArity ``HAdd.hAdd 6 then
    return ← mkAppM ``HAdd.hAdd #[← supAbstract bdds x (e.getArg! 4),
      ← supAbstract bdds x (e.getArg! 5)]
  if e.isAppOfArity ``HMul.hMul 6 && !(e.getArg! 4).containsFVar x.fvarId! then
    return ← mkAppM ``HMul.hMul #[e.getArg! 4, ← supAbstract bdds x (e.getArg! 5)]
  if e.isAppOfArity ``ite 5 then
    return ← mkAppM ``Max.max #[← supAbstract bdds x (e.getArg! 3),
      ← supAbstract bdds x (e.getArg! 4)]
  if e.isAppOfArity ``dite 5 then
    let c := e.getArg! 1
    let br (b : Expr) : MetaM Expr := withLocalDeclD `h c fun h => do
      let v ← supAbstract bdds x (b.beta #[h])
      if v.containsFVar h.fvarId! then throwError "the branch uses its condition"
      return v
    let notC ← mkAppM ``Not #[c]
    let brF (b : Expr) : MetaM Expr := withLocalDeclD `h notC fun h => do
      let v ← supAbstract bdds x (b.beta #[h])
      if v.containsFVar h.fvarId! then throwError "the branch uses its condition"
      return v
    return ← mkAppM ``Max.max #[← br (e.getArg! 3), ← brF (e.getArg! 4)]
  if e.isAppOfArity ``Max.max 4 then
    return ← mkAppM ``Max.max #[← supAbstract bdds x (e.getArg! 2),
      ← supAbstract bdds x (e.getArg! 3)]
  for (G, _) in bdds do
    let s ← saveState
    if ← withReducible (isDefEq (G.beta #[x]) e) then
      return ← mkAppM ``iSup #[G]
    s.restore
  throwError "the value{indentExpr e}\nof a new function component is not bounded by a value \
    of a function component of the state"

/-- Close a goal over `ℕ` by `omega` after splitting its `if`s, with the facts `G t ≤ ⨆ G`. -/
def omegaWithFacts (g : MVarId) : TermElabM Unit := g.withContext do
  let facts ← supFacts (← bddHyps) (← instantiateMVars (← g.getType))
  let mut g := g
  for f in facts do
    let (_, g') ← (← g.assert `hsup (← inferType f) f).intro1P
    g := g'
  let ty ← instantiateMVars (← g.getType)
  let gs ← try Tactic.run g (Tactic.evalTactic (← `(tactic|
      first | omega | (split_ifs <;> omega) | (split <;> omega))))
    catch _ => throwError "`omega` does not prove{indentExpr ty}"
  unless gs.isEmpty do throwError "`omega` does not prove{indentExpr ty}"

/-- The suprema `⨆ x, F x` of `e` whose function `F` is not that of a hypothesis
`BddAbove (Set.range F)`: the suprema of new function components. -/
def newSups (bdds : Array (Expr × Expr)) (e : Expr) : MetaM (Array Expr) := do
  let mut out := #[]
  let sups := (closedSubterms e).filter (·.isAppOfArity ``iSup 4)
  for S in sups do
    if out.contains S then continue
    let F := S.appArg!
    let mut known := false
    for (G, _) in bdds do
      if ← withReducible (isDefEq F G) then known := true; break
    unless known do out := out.push S
  return out

/-- The bound `⨆ x, F x ≤ U` of a supremum of a new function component, with `U` its pointwise
bound (`supAbstract`), proved pointwise by `omegaWithFacts`. -/
def boundSup (S : Expr) : TermElabM Expr := do
  let F := S.appArg!
  let dom := (← inferType F).bindingDomain!
  let bdds ← bddHyps
  let U ← withLocalDeclD `x dom fun x => do
    let U ← supAbstract bdds x (F.beta #[x])
    if U.containsFVar x.fvarId! then throwError "the bound mentions the point"
    return U
  let pw ← mkFreshExprSyntheticOpaqueMVar (← withLocalDeclD `x dom fun x => do
    mkForallFVars #[x] (← mkAppM ``LE.le #[F.beta #[x], U]))
  let (_, g) ← pw.mvarId!.intro1
  omegaWithFacts g
  mkAppM ``StatePotential.iSup_le_of_le #[U, ← instantiateMVars pw]

/-- Close an inequality over `ℕ` between potentials: each supremum of a new function component
is bounded by its pointwise bound, then `omegaWithFacts`. -/
def leClose (g : MVarId) : TermElabM Unit := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  let sups ← newSups (← bddHyps) ty
  let mut g := g
  for S in sups do
    let pf ← boundSup S
    let (_, g') ← (← g.assert `hsupb (← inferType pf) pf).intro1P
    g := g'
  omegaWithFacts g

/-- Close `BddAbove (Set.range F)`: by a hypothesis, or by the pointwise bound of `F`. -/
def bddClose (g : MVarId) : TermElabM Unit := g.withContext do
  let ty ← instantiateMVars (← g.getType)
  let F := ty.appArg!.appArg!
  let bdds ← bddHyps
  for (G, h) in bdds do
    if ← withReducible (isDefEq F G) then g.assign h; return
  let dom := (← inferType F).bindingDomain!
  let U ← withLocalDeclD `x dom fun x => do
    let U ← supAbstract bdds x (F.beta #[x])
    if U.containsFVar x.fvarId! then throwError "the bound mentions the point"
    return U
  let pw ← mkFreshExprSyntheticOpaqueMVar (← withLocalDeclD `x dom fun x => do
    mkForallFVars #[x] (← mkAppM ``LE.le #[F.beta #[x], U]))
  let (_, g') ← pw.mvarId!.intro1
  omegaWithFacts g'
  g.assign (← mkAppM ``StatePotential.bddAbove_range_of_le #[U, ← instantiateMVars pw])

/-- Split the conjunctions of the hypotheses of the context. -/
def splitHyps (g : MVarId) : TermElabM MVarId := do
  let gs ← try Tactic.run g (Tactic.evalTactic (← `(tactic| casesm* _ ∧ _)))
    catch _ => return g
  match gs with
  | [g'] => return g'
  | _ => return g

/-- Close a leaf goal of a potential clause: a conjunction part by part, a `∀` or an implication
after introducing it, `True`, `BddAbove (Set.range F)` by `bddClose`, an inequality over `ℕ` by
`leClose`, any other goal by a hypothesis or `simp_all`. -/
partial def potClose (g : MVarId) : TermElabM Unit := do
  let g ← splitHyps g
  g.withContext do
  let ty ← whnfR (← instantiateMVars (← g.getType))
  if ty.isAppOfArity ``And 2 then
    let gs ← g.apply (mkConst ``And.intro)
    for g' in gs do potClose g'
    return
  if ty.isConstOf ``True then g.assign (mkConst ``True.intro); return
  if ty.isForall then
    let (_, g') ← g.intro1
    potClose g'
    return
  if ty.isAppOfArity ``BddAbove 3 then bddClose g; return
  if ty.isAppOfArity ``LE.le 4 && (ty.getArg! 0).isConstOf ``Nat then leClose g; return
  if ty.isAppOfArity ``ite 5 then
    let gs ← Tactic.run g (Tactic.evalTactic (← `(tactic| split_ifs)))
    for g' in gs do potClose g'
    return
  let gs ← Tactic.run g (Tactic.evalTactic (← `(tactic| first | assumption | simp_all)))
  unless gs.isEmpty do throwError "the goal{indentExpr ty}\nis not closed"

/-- The definitions `R.….timed` of the costed trees of `R`, which the potential clause unfolds. -/
def treeDefs (R : Name) : MetaM (Array Name) := do
  let mut out := #[]
  for (n, ci) in (← getEnv).constants.toList do
    if R.isPrefixOf n && n != R && n.getString! == "timed" && ci.isDefinition then
      out := out.push n
  return out

/-- Simplify the goal and the hypotheses by `potSimpLemmas` and the definitions `defs`: the goal,
or `none` when it is closed. -/
def simpAll (defs : Array Name) (g : MVarId) : TermElabM (Option MVarId) := do
  let ids : Array Ident := (potSimpLemmas ++ defs).map mkCIdent
  let args : Array (TSyntax ``Parser.Tactic.simpLemma) ←
    ids.mapM fun i => `(Parser.Tactic.simpLemma| $i:ident)
  let gs ← try Tactic.run g (Tactic.evalTactic (← `(tactic| simp only [$args,*] at *)))
    catch _ => return some g
  return gs.head?

/-- Prove the potential clause `g` of a step, `AllRet Q (A.st s x)` under `inv s`: unfold the
costed tree by the definitions `ctx`, split its matches, and close every leaf by `potClose`. -/
partial def clauseClose (ctx : Array Name) (g : MVarId) (fuel : Nat := 6) :
    TermElabM Unit := do
  let some g ← simpAll ctx g | return
  let g ← splitHyps g
  let s ← saveState
  try
    potClose g
  catch e =>
    s.restore
    if fuel == 0 then throw e
    let gs ← try Tactic.run g (Tactic.evalTactic (← `(tactic| split)))
      catch _ => throw e
    if gs.isEmpty then return
    for g' in gs do clauseClose ctx g' (fuel - 1)

end

/-- `pot_close` proves a potential clause `AllRet (fun y => inv y.1 ∧ …) t` or a leaf of one
under hypotheses `inv s`: it simplifies by the equations of `pot` and `inv`, splits the matches of
the tree and closes every leaf by `potClose`. -/
syntax (name := potCloseTac) "pot_close" : tactic

/-- Elaborate `pot_close`. -/
@[tactic potCloseTac]
meta def evalPotClose : Tactic := fun _ => do
  clauseClose #[] (← getMainGoal)
  replaceMainGoal []

end CatCrypt.Tactics.StatePotential
