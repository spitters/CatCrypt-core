/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.GCongr
public import Mathlib.Tactic.Positivity
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring
public import CatCryptCore.Tactics.AutoHopRegistry
public meta import CatCryptCore.Tactics.AutoHopRegistry
public import CatCryptCore.Tactics.AutoDispatchCore
public meta import CatCryptCore.Tactics.AutoDispatchCore

/-!
# Hop chains over registered pseudometrics, sums of atoms, and monotonicity

This module provides eight procedures.

* `hop_chain [facts]` proves `d x y ≤ e` for a distance `d` registered with the
  attribute `@[hop_metric]`. It collects hop facts `d u v ≤ b` (and `d u v = b`) from the
  local context and from its arguments, searches the graph whose vertices are endpoints
  and whose edges are hop facts (both directions when a symmetry lemma is registered) for
  a path from `x` to `y`, composes the triangle lemma along the path, and closes the
  residual inequality between the sum of the hop bounds and `e` with `sum_atoms_le`.
  A fact over a distance `d₂` that dominates `d` by a lemma `d … x y ≤ d₂ … x y`
  registered with `@[hop_metric]` is read as a hop fact over `d` (two rounds, so that
  `d ≤ d₂ ≤ d₃` composes).
* `sum_atoms_le` decides inequalities between ℕ-weighted sums of atoms in an ordered
  commutative semiring whose elements are nonnegative (`ℝ≥0∞` in practice), using in
  addition hypotheses `a ≤ b` between atoms; a goal outside the fragment is read again
  after expanding sums over `Finset.range (n + 1)` and reducing conditionals on Boolean
  literal equations.
* `gcongr_unfold [defs]` introduces the binders of a goal that unfolds to a universally
  quantified relation (for example `Monotone f`), unfolds the listed definitions, and runs
  `gcongr` with a fixed discharger.
* `hop_chain! [facts]` is `hop_chain` with hop endpoints identified up to definitional
  equality at default transparency and the head definitions of the bound unfolded when
  the residual inequality is not closed.
* `bool_cases` splits the goal, in at most three rounds, by `cases` on local Boolean
  variables and `by_cases` on the propositions of `decide` and `if` subterms.
* `hyp_unfold` unfolds, in the local hypotheses, the predicate definitions found at the
  head of a hypothesis or under `¬`, `∧`, `∨`, `↔` and non-dependent `→` (to depth 4):
  definitions that `AutoDispatch.isUnfoldable` accepts. Two rounds, so that a definition
  exposed by the first unfolding is unfolded too. The hypotheses are changed by delta
  reduction (`replaceLocalDeclDefEq`). It fails when no hypothesis has such a definition.
* `funext_unfold` proves an equality `f = g` at a function type whose codomain is a
  program type registered with `catcrypt_funext_type`, or at a registered program type
  that unfolds to a function type, by applying `funext` once for each argument up to and
  including the arguments of the program type, and then unfolding in the goal each
  definition from the workspace that is applied to more arguments than its declared
  binders (an operation on the representation of the program type, such as
  `SPComp.bind c f h`).
* `ord_residual` proves a goal `a ≤ b` over a type with `Semiring` and `PartialOrder`
  instances (`ℝ≥0∞`, `ℝ`, `ℕ`, …) by a depth-bounded monotonicity search. At each goal it
  tries, in order: the leaf closers `assumption`, `exact le_rfl`, `assumption_mod_cast`
  and, on a goal `0 ≤ x`, `positivity`; the factor bounds `c * a ≤ a`, `a * c ≤ a` from
  `c ≤ 1` (`mul_le_of_le_one_left`, `mul_le_of_le_one_right`), `a ≤ c * a`, `a ≤ a * c`
  from `1 ≤ c` (`le_mul_of_one_le_left`, `le_mul_of_one_le_right`), `a * c ≤ 1` from
  `a ≤ 1` and `c ≤ 1` (`mul_le_one₀`), and `a ≤ b + c`, `a ≤ c + b` from `a ≤ b` and
  `0 ≤ c` (`le_add_of_le_of_nonneg`, `le_add_of_nonneg_of_le`), each applied at instance
  transparency with every new goal solved recursively; then `gcongr`, its side goals
  discharged by its own discharger, each main goal it leaves solved recursively. The
  search has depth `n` for `ord_residual n` and 3 for `ord_residual`. A goal that is not
  `_ ≤ _` over a type with both instances fails at once, before any tactic runs. A factor
  lemma absent from the environment is skipped.

The attribute `@[hop_metric]` and the distance views are in
`CatCryptCore.Tactics.AutoHopRegistry`. No distance is built into the procedures; the
registrations of `Advantage`, `sdist` and `AdvantageA` are beside their triangle lemmas,
in `CatCryptCore.Crypto.Advantage`, `CatCryptCore.Crypto.SDist` and
`CatCryptCore.Tactics.Triangle`.

The module registers with `catcrypt_auto` (`CatCryptCore.Tactics.AutoDispatchCore`) these
arms:

| Shape | Arm | Order |
|---|---|---|
| `distance inequality` | `hop_chain`; `hop_chain!`; `sum_atoms_le` | 10; 11; 20 |
| `monotonicity inequality` | `gcongr_unfold`; `gcongr`; `sum_atoms_le` | 10; 20; 40 |
| `other` | `sum_atoms_le` | 10 |
| `other` | `bool_cases`, then `rfl`, `decide` or `simp_all` on each case | 25 |
| `SPComp equality` | `bool_cases` when it splits, then `rfl`, `decide` or `simp_all` | 25 |
| `SPComp equality`, `heap read after write` | `hyp_unfold`, then `grind` or `simp_all` | 30 |
| `other` | `hyp_unfold`, then `grind` or `simp_all` | 35 |
| `SPComp equality`; `other` | `funext_unfold`, then `rfl`, `grind` or `simp_all` | 15; 36 |
| `distance inequality`; `monotonicity inequality` | `ord_residual` | 45; 45 |
| `other` | `ord_residual` | 15 |
-/

@[expose] public section

meta section

namespace CatCrypt.Tactics.AutoArms

open Lean Meta Elab Tactic

/-! ## Hop facts and path search -/

/-- A hop fact `d … x y ≤ bound` over the distance of the goal. -/
structure Hop where
  /-- Left endpoint. -/
  src : Expr
  /-- Right endpoint. -/
  dst : Expr
  /-- The distance term `d … src dst`. -/
  lhs : Expr
  /-- A proof of `lhs ≤ bound`. -/
  pf : Expr
  deriving Inhabited

/-- Read a proof `h` of `t ≤ b` or `t = b`, with `t` a distance over the goal's metric and
context arguments, as a hop. -/
def hopOf? (goal : DView) (h : Expr) : MetaM (Option Hop) := do
  let ty ← whnfR (← instantiateMVars (← inferType h))
  let (lhs, rhs, pfLe) ← match leSides? ty, eqSides? ty with
    | some (l, r), _ => pure (l, r, h)
    | none, some (l, r) =>
      if (← inferType l).isProp then return none
      pure (l, r, ← mkAppM ``le_of_eq #[h])
    | none, none => return none
  let some v ← distView? lhs | return none
  unless v.entry.decl == goal.entry.decl do return none
  let .triangle i j := v.entry.kind | return none
  for k in [0:v.args.size] do
    if k != i && k != j then
      unless ← isDefEq v.args[k]! goal.args[k]! do return none
  let pf ← match v.pf with
    | some p => mkAppM ``Eq.trans_le #[← mkEqSymm p, pfLe]
    | none => mkExpectedTypeHint pfLe (← mkAppM ``LE.le #[v.term, rhs])
  return some { src := v.args[i]!, dst := v.args[j]!, lhs := v.term, pf }

/-- The reversed hop `d … y x ≤ b` from `d … x y ≤ b` by a registered symmetry lemma. -/
def reverseHop? (goal : DView) (hop : Hop) : MetaM (Option Hop) := do
  let .triangle i j := goal.entry.kind | return none
  let some (_, args) := appParts? hop.lhs | return none
  let lhsRev := mkAppN hop.lhs.getAppFn ((args.set! i hop.dst).set! j hop.src)
  for x in ← hopEntries do
    unless x.kind == .symm && x.head == goal.entry.head do continue
    let (p, ty) ← instThm x.decl
    let some (l, r) := eqSides? ty | continue
    if (← isDefEq l lhsRev) && (← isDefEq r hop.lhs) then
      let p ← instantiateMVars p
      return some { src := hop.dst, dst := hop.src, lhs := lhsRev,
                    pf := ← mkAppM ``Eq.trans_le #[p, hop.pf] }
  return none

/-- The index of `e` among `nodes` up to reducible definitional equality; when `deep` is
set and there is none, the index of the first node definitionally equal to `e` at
default transparency. -/
def nodeIdx (nodes : Array Expr) (e : Expr) (deep : Bool := false) : MetaM (Option Nat) := do
  for k in [0:nodes.size] do
    if ← withReducible (isDefEq nodes[k]! e) then return some k
  if deep then
    for k in [0:nodes.size] do
      if ← isDefEq nodes[k]! e then return some k
  return none

/-- Breadth-first search for a path of hops from `src` to `dst`; endpoints are identified
by `nodeIdx` with `deep`. -/
def findPath (hops : Array Hop) (src dst : Expr) (deep : Bool := false) :
    MetaM (Option (Array Hop)) := do
  let mut nodes : Array Expr := #[src, dst]
  let mut edges : Array (Nat × Nat × Hop) := #[]
  for hop in hops do
    let a ← match ← nodeIdx nodes hop.src deep with
      | some a => pure a
      | none => do nodes := nodes.push hop.src; pure (nodes.size - 1)
    let b ← match ← nodeIdx nodes hop.dst deep with
      | some b => pure b
      | none => do nodes := nodes.push hop.dst; pure (nodes.size - 1)
    edges := edges.push (a, b, hop)
  let mut prev : Array (Option (Nat × Hop)) := Array.replicate nodes.size none
  let mut seen : Array Bool := (Array.replicate nodes.size false).set! 0 true
  let mut queue : Array Nat := #[0]
  let mut qi := 0
  while qi < queue.size do
    let u := queue[qi]!
    qi := qi + 1
    for (a, b, hop) in edges do
      if a == u && !seen[b]! then
        seen := seen.set! b true
        prev := prev.set! b (some (u, hop))
        queue := queue.push b
  if !seen[1]! then return none
  let mut path : Array Hop := #[]
  let mut v := 1
  let mut fuel := nodes.size
  while v != 0 && fuel > 0 do
    fuel := fuel - 1
    let some (u, hop) := prev[v]! | break
    path := path.push hop
    v := u
  return some path.reverse

/-! ## Sums of atoms -/

/-- The value of a natural-number literal `OfNat.ofNat n` or a raw literal. -/
def natLit? (e : Expr) : Option Nat :=
  if e.isAppOfArity ``OfNat.ofNat 3 then
    match e.appFn!.appArg! with
    | .lit (.natVal n) => some n
    | _ => none
  else match e with
    | .lit (.natVal n) => some n
    | _ => none

/-- The ℕ-weighted atoms of a sum: `a + b`, `0`, `n * a`, `a * n` and `n • a` with `n` a
literal are read structurally; every other term is an atom of weight `1`. -/
partial def weightedAtoms (e : Expr) : MetaM (Array (Nat × Expr)) := do
  let e := (← instantiateMVars e).cleanupAnnotations
  if let some (a, b) := addSides? e then
    return (← weightedAtoms a) ++ (← weightedAtoms b)
  if natLit? e == some 0 || e.isAppOfArity ``Zero.zero 2 then return #[]
  if e.isAppOfArity ``HMul.hMul 6 || e.isAppOfArity ``HSMul.hSMul 6 then
    let a := e.appFn!.appArg!
    let b := e.appArg!
    if let some n := natLit? a then
      return (← weightedAtoms b).map fun (c, t) => (n * c, t)
    if e.isAppOfArity ``HMul.hMul 6 then
      if let some n := natLit? b then
        return (← weightedAtoms a).map fun (c, t) => (n * c, t)
  return #[(1, e)]

/-- Run a tactic on a fresh goal of type `ty` and return the proof, or fail. -/
def proveWith (ty : Expr) (tac : TSyntax `tactic) : TacticM Expr := do
  let m ← mkFreshExprSyntheticOpaqueMVar ty
  let gs ← Tactic.run m.mvarId! (evalTactic tac)
  unless gs.isEmpty do throwError "goals remain after `{tac}`"
  instantiateMVars m

/-- Left-associated sum of a nonempty array of terms. -/
def mkSum (ts : Array Expr) : MetaM Expr := do
  let mut acc := ts[0]!
  for t in ts[1:] do
    acc ← mkAppM ``HAdd.hAdd #[acc, t]
  return acc

/-- Maximal number of atom occurrences on either side handled by `sum_atoms_le`. -/
def maxUnits : Nat := 64

/-- Augmenting-path step of bipartite matching from left unit `u`. -/
partial def augment (adj : Array (Array Nat)) (u : Nat) (visited : Array Bool)
    (matchR : Array (Option Nat)) : Bool × Array Bool × Array (Option Nat) := Id.run do
  let mut visited := visited
  let mut matchR := matchR
  for r in adj[u]! do
    if visited[r]! then continue
    visited := visited.set! r true
    match matchR[r]! with
    | none => return (true, visited, matchR.set! r (some u))
    | some u' =>
      let (ok, vis', mr') := augment adj u' visited matchR
      visited := vis'
      matchR := mr'
      if ok then return (true, visited, matchR.set! r (some u))
  return (false, visited, matchR)

/-- Prove `S ≤ E` for the goal `g` by the procedure documented at `sum_atoms_le`. -/
def sumAtomsLe (g : MVarId) : TacticM Unit := g.withContext do
  let ty ← whnfR (← instantiateMVars (← g.getType))
  let some (lhs, rhs) := leSides? ty |
    throwError "sum_atoms_le: the goal is not `_ ≤ _`:{indentExpr ty}"
  let α ← inferType lhs
  let wl ← weightedAtoms lhs
  let wr ← weightedAtoms rhs
  let nl := wl.foldl (fun s (c, _) => s + c) 0
  let nr := wr.foldl (fun s (c, _) => s + c) 0
  if nl > maxUnits || nr > maxUnits then
    throwError "sum_atoms_le: more than {maxUnits} atom occurrences on one side"
  let lUnits : Array Expr := wl.foldl (fun acc (c, t) => acc ++ Array.replicate c t) #[]
  let rUnits : Array Expr := wr.foldl (fun acc (c, t) => acc ++ Array.replicate c t) #[]
  -- hypotheses `a ≤ b` of the local context
  let mut hyps : Array (Expr × Expr × Expr) := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t ← whnfR (← instantiateMVars d.type)
    if let some (a, b) := leSides? t then
      if ← isDefEq (← inferType a) α then hyps := hyps.push (a, b, d.toExpr)
  -- the edge proofs `lUnits[u] ≤ rUnits[r]`
  let mut adj : Array (Array Nat) := #[]
  let mut proofs : Std.HashMap (Nat × Nat) Expr := {}
  for u in [0:lUnits.size] do
    let mut row := #[]
    for r in [0:rUnits.size] do
      if ← withReducible (isDefEq lUnits[u]! rUnits[r]!) then
        row := row.push r
        proofs := proofs.insert (u, r) (← mkAppM ``le_refl #[lUnits[u]!])
      else
        for (a, b, p) in hyps do
          if (← withReducible (isDefEq a lUnits[u]!)) &&
              (← withReducible (isDefEq b rUnits[r]!)) then
            row := row.push r
            proofs := proofs.insert (u, r) p
            break
    adj := adj.push row
  let mut matchR : Array (Option Nat) := Array.replicate rUnits.size none
  for u in [0:lUnits.size] do
    let (ok, _, mr) := augment adj u (Array.replicate rUnits.size false) matchR
    unless ok do
      throwError "sum_atoms_le: the atom{indentExpr lUnits[u]!}\noccurs more often on the \
        left than it is bounded on the right (by itself or by a hypothesis `a ≤ b`) \
        in{indentExpr ty}"
    matchR := mr
  let mut matchL : Array Nat := Array.replicate lUnits.size 0
  for r in [0:rUnits.size] do
    if let some u := matchR[r]! then matchL := matchL.set! u r
  let rest := (List.range rUnits.size).toArray.filter fun r => matchR[r]!.isNone
  let zero ← mkAppOptM ``OfNat.ofNat #[α, mkRawNatLit 0, none]
  let restSum? ← if rest.isEmpty then pure none
    else some <$> mkSum (rest.map fun r => rUnits[r]!)
  let pf ← if lUnits.isEmpty then do
      let hS ← proveWith (← mkEq lhs zero) (← `(tactic| ring1))
      let hz ← proveWith (← mkAppM ``LE.le #[zero, rhs])
        (← `(tactic| first | exact zero_le _ | positivity))
      mkAppM ``Eq.trans_le #[hS, hz]
    else do
      let mut hmid ← pure (proofs[(0, matchL[0]!)]!)
      for u in [1:lUnits.size] do
        hmid ← mkAppM ``add_le_add #[hmid, proofs[(u, matchL[u]!)]!]
      let some (aSum, bSum) := leSides? (← whnfR (← inferType hmid)) |
        throwError "sum_atoms_le: internal error"
      let hS ← proveWith (← mkEq lhs aSum) (← `(tactic| ring1))
      let (top, hpad) ← match restSum? with
        | none => pure (bSum, ← mkAppM ``le_refl #[bSum])
        | some rs => do
          let top ← mkAppM ``HAdd.hAdd #[bSum, rs]
          let hpad ← proveWith (← mkAppM ``LE.le #[bSum, top])
            (← `(tactic| first | exact le_self_add | exact le_add_of_nonneg_right (by positivity)))
          pure (top, hpad)
      let hE ← proveWith (← mkEq rhs top) (← `(tactic| ring1))
      let h1 ← mkAppM ``le_trans #[hmid, hpad]
      let h2 ← mkAppM ``le_of_le_of_eq #[h1, ← mkEqSymm hE]
      mkAppM ``Eq.trans_le #[hS, h2]
  unless ← isDefEq (← inferType pf) (← g.getType) do
    throwError "sum_atoms_le: internal error: proof type mismatch"
  g.assign pf

/-- The units of `ts` with one occurrence of each unit of `sub` removed (reducible
definitional equality), or `none` when some unit of `sub` does not occur. -/
def removeUnits (ts sub : Array Expr) : MetaM (Option (Array Expr)) := do
  let mut rest := ts
  for s in sub do
    let mut idx : Option Nat := none
    for i in [0:rest.size] do
      if ← withReducible (isDefEq rest[i]! s) then
        idx := some i
        break
    let some i := idx | return none
    rest := rest.eraseIdxIfInBounds i
  return some rest

/-- The units of a weighted atom list: each atom repeated by its weight. -/
def unitsOf (w : Array (Nat × Expr)) : Array Expr :=
  w.foldl (fun acc (c, t) => acc ++ Array.replicate c t) #[]

/-- Maximal number of hypotheses between sums applied in sequence by `sum_atoms_le`. -/
def maxSumHypSteps : Nat := 3

/-- Prove `S ≤ E` for the goal `g` by `sumAtomsLe`; when that fails, by a hypothesis
`A ≤ B` of the local context whose sides are not both single atoms and whose atoms of `A`
occur among those of `S`: with `S = A + R` (`ring1`) and `A + R ≤ B + R` (`add_le_add`),
the goal `B + R ≤ E` is proved in the same way, using at most `steps` such hypotheses. -/
partial def sumAtomsLeHyps (g : MVarId) (steps : Nat) : TacticM Unit := g.withContext do
  try sumAtomsLe g
  catch e =>
    if steps == 0 then throw e
    let ty ← whnfR (← instantiateMVars (← g.getType))
    let some (lhs, rhs) := leSides? ty | throw e
    let α ← inferType lhs
    let lUnits := unitsOf (← weightedAtoms lhs)
    for d in ← getLCtx do
      if d.isImplementationDetail then continue
      let t ← whnfR (← instantiateMVars d.type)
      let some (a, b) := leSides? t | continue
      unless ← isDefEq (← inferType a) α do continue
      let aUnits := unitsOf (← weightedAtoms a)
      let bUnits := unitsOf (← weightedAtoms b)
      if aUnits.size ≤ 1 && bUnits.size ≤ 1 then continue
      if aUnits.isEmpty || aUnits.size > maxUnits || bUnits.size > maxUnits then continue
      let some rest ← removeUnits lUnits aUnits | continue
      let s ← saveState
      try
        let (aR, bR, hStep) ← if rest.isEmpty then
            pure (a, b, d.toExpr)
          else do
            let R ← mkSum rest
            let aR ← mkAppM ``HAdd.hAdd #[a, R]
            let bR ← mkAppM ``HAdd.hAdd #[b, R]
            pure (aR, bR, ← mkAppM ``add_le_add #[d.toExpr, ← mkAppM ``le_refl #[R]])
        let hS ← proveWith (← mkEq lhs aR) (← `(tactic| ring1))
        let m ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``LE.le #[bR, rhs])
        sumAtomsLeHyps m.mvarId! (steps - 1)
        let pf ← mkAppM ``Eq.trans_le #[hS, ← mkAppM ``le_trans #[hStep, m]]
        unless ← isDefEq (← inferType pf) (← g.getType) do
          throwError "sum_atoms_le: internal error: proof type mismatch"
        g.assign pf
        return
      catch _ =>
        s.restore
    throw e

set_option hygiene false in
/-- The normalisation that `sum_atoms_le` applies before its second reading of a goal:
finite sums over `Finset.range (n + 1)` and `Finset.range 0` are expanded, and
conditionals on the Boolean literal equations `false = true` and `true = false` are
reduced. -/
def sumAtomsNorm : TacticM (TSyntax `tactic) :=
  `(tactic| simp only [Finset.sum_range_succ, Finset.sum_range_zero, Bool.false_eq_true,
    Bool.true_eq_false, ↓reduceIte])

/-- Prove `S ≤ E` for the goal `g` by `sumAtomsLeHyps`; when that fails, normalise the
goal by `sumAtomsNorm` and read it again. The error of the first reading is reported when
the normalisation does not change the goal. -/
def sumAtomsLeNorm (g : MVarId) : TacticM Unit := do
  try sumAtomsLeHyps g maxSumHypSteps
  catch e =>
    let gs ← try Tactic.run g (evalTactic (← sumAtomsNorm)) catch _ => throw e
    match gs with
    | [] => pure ()
    | [g'] => sumAtomsLeHyps g' maxSumHypSteps
    | _ => throw e

/-- `sum_atoms_le` proves `S ≤ E` where `S` and `E` are sums of atoms with natural-number
literal weights (`a + b`, `0`, `n * a`, `a * n`, `n • a`; any other term is an atom),
in an ordered commutative semiring with `0 ≤ x` for all `x` (`ℝ≥0∞` in practice).
When the goal is not in this fragment as stated, it is read a second time after
`simp only [Finset.sum_range_succ, Finset.sum_range_zero, Bool.false_eq_true,
Bool.true_eq_false, ↓reduceIte]`: a sum over `Finset.range (n + 1)` is a sum of atoms
once expanded, and `if false = true then a else b` is the atom `b`.

Reading each atom as an independent variable, the inequality holds in every such
semiring if and only if the weight of each atom on the left is at most its weight on the
right; the tactic decides this fragment. It also uses hypotheses `a ≤ b` of the local
context between atoms: each left occurrence is matched (bipartite matching) to a distinct
right occurrence of the same atom or of an atom bounding it by a hypothesis. Hypotheses
between atoms are used as single steps, not chained transitively. A hypothesis `A ≤ B`
whose sides are sums is applied to the left side when the atoms of `A` occur in `S`
(with multiplicity, in any order and grouping): `S = A + R ≤ B + R`, and `B + R ≤ E` is
read again; at most three such hypotheses are applied in sequence.

The proof is `S = Σ aₖ` (`ring1`), `Σ aₖ ≤ Σ bₖ` (`add_le_add` of the matched steps),
`Σ bₖ ≤ Σ bₖ + R` (`le_self_add`), `E = Σ bₖ + R` (`ring1`). Both sides are compared as
multisets of atoms, so the order and grouping of the summands do not matter. It fails,
naming the unmatched atom, when no matching exists. -/
syntax (name := sumAtomsLeStx) "sum_atoms_le" : tactic

@[tactic sumAtomsLeStx] def evalSumAtomsLe : Tactic := fun _ => do
  let g ← getMainGoal
  sumAtomsLeNorm g
  replaceMainGoal []

/-! ## Hop chains -/

/-- `n` is a definition that `unfoldBoundHead?` unfolds: a definition with a value, not
recursive, not an instance, a projection or a matcher, not a `@[hop_metric]` head, and
not from the Lean core, Mathlib, Batteries, Aesop or Qq. -/
def unfoldsBound (n : Name) : MetaM Bool := do
  let env ← getEnv
  let some (.defnInfo _) := env.find? n | return false
  if isInstanceCore env n || env.isProjectionFn n || isMatcherCore env n then return false
  if ← isRecursiveDefinition n then return false
  if (← hopEntries).any (·.head == n) then return false
  if let some idx := env.getModuleIdxFor? n then
    let root := (env.header.moduleNames[idx.toNat]!).getRoot
    if [`Init, `Std, `Lean, `Lake, `Mathlib, `Batteries, `Aesop, `Qq].contains root then
      return false
  return true

/-- `e` with its head definition unfolded, at most four times, while the head is a
definition that `unfoldsBound` accepts; `none` when no unfolding applies. -/
def unfoldBoundHead? (e : Expr) : MetaM (Option Expr) := do
  let mut cur := e
  let mut changed := false
  for _ in [0:4] do
    let some n := cur.getAppFn.constName? | break
    unless ← unfoldsBound n do break
    let some e' ← unfoldDefinition? cur | break
    cur := e'.headBeta
    changed := true
  return if changed then some cur else none

/-- The proof `h` of `t ≤ b` or `t = b` as a proof of `t ≤ b`, with `t`. -/
def leFact? (h : Expr) : MetaM (Option (Expr × Expr)) := do
  let ty ← whnfR (← instantiateMVars (← inferType h))
  if let some (l, _) := leSides? ty then return some (l, h)
  if let some (l, _) := eqSides? ty then
    if (← inferType l).isProp then return none
    return some (l, ← mkAppM ``le_of_eq #[h])
  return none

/-- The facts over dominated distances obtained from the facts `cands` by the dominance
lemmas registered with `@[hop_metric]`, in `rounds` rounds: for a lemma
`d₁ … x y ≤ d₂ … x y` and a fact `d₂ … u v ≤ b` (or `= b`), the fact `d₁ … u v ≤ b`. -/
def liftDominated (cands : Array Expr) (rounds : Nat := 2) : MetaM (Array Expr) := do
  let doms := (← hopEntries).filterMap fun x => match x.kind with
    | .dominance r => some (x.decl, r)
    | _ => none
  if doms.isEmpty then return #[]
  let mut out : Array Expr := #[]
  let mut frontier := cands
  for _ in [0:rounds] do
    let mut next : Array Expr := #[]
    for c in frontier do
      let some (t, pf) ← leFact? c | continue
      let some (h, _) := appParts? t | continue
      for (decl, rhsHead) in doms do
        unless rhsHead == h do continue
        let (p, ty) ← instThm decl
        let some (l, r) := leSides? ty | continue
        unless ← isDefEq r t do continue
        let l ← instantiateMVars l
        if l.hasExprMVar then continue
        let p ← instantiateMVars p
        next := next.push (← mkAppM ``le_trans #[p, pf])
    if next.isEmpty then break
    out := out ++ next
    frontier := next
  return out

/-- The core of `hop_chain` and `hop_chain!`: prove the main goal from the elaborated
argument proofs `extra` and the hypotheses of the local context. With `deep`
(`hop_chain!`), hop endpoints are identified up to definitional equality at default
transparency, and a residual inequality that `sum_atoms_le` does not close is read again
with the head definitions of its right side unfolded (`unfoldBoundHead?`). -/
def hopChainCore (extra : Array Expr) (deep : Bool := false) : TacticM Unit := do
  let g ← getMainGoal
  g.withContext do
  let ty ← whnfR (← instantiateMVars (← g.getType))
  let some (lhs, rhs) := leSides? ty |
    throwError "hop_chain: the goal is not `d x y ≤ e`:{indentExpr ty}"
  let some gv ← distView? lhs |
    throwError "hop_chain: the left side is not a distance registered with \
      `@[hop_metric]`:{indentExpr lhs}"
  let .triangle i j := gv.entry.kind | throwError "hop_chain: internal error"
  let src := gv.args[i]!
  let dst := gv.args[j]!
  let mut cands : Array Expr := extra
  for d in ← getLCtx do
    unless d.isImplementationDetail do cands := cands.push d.toExpr
  cands := cands ++ (← liftDominated cands)
  let mut hops : Array Hop := #[]
  for c in cands do
    if let some hop ← hopOf? gv c then
      hops := hops.push hop
      if let some rev ← reverseHop? gv hop then hops := hops.push rev
  let some path ← findPath hops src dst deep |
    throwError "hop_chain: no chain of hop facts over `{gv.entry.head}` connects{indentExpr src}\
      \nto{indentExpr dst}\nhop facts found: {← hops.mapM fun h => inferType h.pf}"
  if path.isEmpty then
    throwError "hop_chain: the two endpoints of the goal coincide"
  -- compose the triangle lemma along the path, from the right
  let last := path[path.size - 1]!
  let mut acc := last.pf
  for k' in [0:path.size - 1] do
    let k := path.size - 2 - k'
    let hop := path[k]!
    let tgt := mkAppN gv.term.getAppFn ((gv.args.set! i hop.src).set! j dst)
    let (tri, triTy) ← instThm gv.entry.decl
    let some (l, r) := leSides? triTy | throwError "hop_chain: internal error"
    let some (r₁, _) := addSides? r | throwError "hop_chain: internal error"
    unless (← isDefEq l tgt) && (← isDefEq r₁ hop.lhs) do
      throwError "hop_chain: the triangle lemma `{gv.entry.decl}` does not apply at{indentExpr tgt}"
    let tri ← instantiateMVars tri
    acc ← mkAppM ``le_trans #[tri, ← mkAppM ``add_le_add #[hop.pf, acc]]
  let some (_, bound) := leSides? (← whnfR (← inferType acc)) |
    throwError "hop_chain: internal error"
  let res ← mkFreshExprSyntheticOpaqueMVar (← mkAppM ``LE.le #[bound, rhs])
  let core ← mkAppM ``le_trans #[acc, res]
  let pf ← match gv.pf with
    | some p => mkAppM ``Eq.trans_le #[p, core]
    | none => pure core
  unless ← isDefEq (← inferType pf) (← g.getType) do
    throwError "hop_chain: internal error: proof type mismatch"
  g.assign pf
  let residualError (e : Exception) : TacticM Unit :=
    throwError "hop_chain: the hops compose to{indentExpr bound}\nbut the residual \
      inequality is not closed: {e.toMessageData}"
  let saved ← saveState
  try sumAtomsLeNorm res.mvarId!
  catch e =>
    unless deep do residualError e
    let some rhs' ← unfoldBoundHead? rhs | residualError e
    saved.restore
    let res' ← res.mvarId!.replaceTargetDefEq (← mkAppM ``LE.le #[bound, rhs'])
    try sumAtomsLeNorm res'
    catch e' => residualError e'
  replaceMainGoal []

/-- `hop_chain [h₁, …, hₙ]` proves `d x y ≤ e` for a distance `d` registered with
`@[hop_metric]`.

Hop facts are proofs of `d … u v ≤ b` or `d … u v = b` whose context arguments agree
with the goal's: the arguments `hᵢ` and the hypotheses of the local context. A
universally quantified hypothesis is never a hop fact; pass its instances as arguments.
Terms headed by a registered definition or equation are unfolded to the distance first,
and a fact over a distance that dominates `d` by a registered dominance lemma is read as a
fact over `d` (`liftDominated`).
The procedure searches breadth first for a path of hop facts from `x` to `y` (using
each fact in both directions when a symmetry lemma for `d` is registered), composes the
registered triangle lemma along the path to `d x y ≤ b₁ + (b₂ + …)`, and closes the
residual `b₁ + (b₂ + …) ≤ e` with `sum_atoms_le`. It fails when no path exists or the
residual is not closed. -/
syntax (name := hopChainStx) "hop_chain" (" [" term,* "]")? : tactic

@[tactic hopChainStx] def evalHopChain : Tactic := fun stx => do
  let ts : Array Term := stx[1][1].getSepArgs.map (⟨·⟩)
  let extra ← withMainContext <| ts.mapM fun (t : Term) => do
    let e ← Term.withoutErrToSorry (elabTerm t none)
    if (← whnfR (← inferType e)).isForall then
      throwError "hop_chain: the argument `{t}` is quantified; pass an instance of it"
    return e
  hopChainCore extra

/-- `hop_chain! [h₁, …, hₙ]` is `hop_chain [h₁, …, hₙ]` with two unfoldings: a hop
endpoint is identified with another endpoint, or with an endpoint of the goal, when the
two are definitionally equal at default transparency (game definitions that agree after
unfolding), and when the residual `b₁ + (b₂ + …) ≤ e` is not closed, `e` is read again
with its head definitions unfolded (a bound defined as a sum of the hop bounds). -/
syntax (name := hopChainBangStx) "hop_chain!" (" [" term,* "]")? : tactic

@[tactic hopChainBangStx] def evalHopChainBang : Tactic := fun stx => do
  let ts : Array Term := stx[1][1].getSepArgs.map (⟨·⟩)
  let extra ← withMainContext <| ts.mapM fun (t : Term) => do
    let e ← Term.withoutErrToSorry (elabTerm t none)
    if (← whnfR (← inferType e)).isForall then
      throwError "hop_chain!: the argument `{t}` is quantified; pass an instance of it"
    return e
  hopChainCore extra (deep := true)

/-! ## Monotonicity -/

/-- Whether `e` is an order or set relation that `gcongr` treats directly. -/
def isRelation (e : Expr) : Bool :=
  e.isAppOfArity ``LE.le 4 || e.isAppOfArity ``LT.lt 4 || e.isAppOfArity ``GE.ge 4 ||
    e.isAppOfArity ``GT.gt 4 || e.isAppOfArity ``HasSubset.Subset 4 ||
    e.isAppOfArity ``HasSSubset.SSubset 4

/-- `gcongr_unfold [d₁, …, dₙ]` proves a monotonicity goal.

It introduces binders while the goal is not a relation and unfolds (by `whnf`) to a
universal quantification, so `Monotone f`, `Antitone f` and similar definitions become
`f a ≤ f b` under the hypothesis `a ≤ b`; then it unfolds `d₁, …, dₙ` with `simp only`,
runs `gcongr`, and closes every remaining goal by `assumption`, `assumption_mod_cast`,
`positivity` or `norm_num`. It fails, naming the step, when a listed definition does
not occur, when `gcongr` does not apply, or when a goal remains. -/
syntax (name := gcongrUnfoldStx) "gcongr_unfold" (" [" ident,* "]")? : tactic

@[tactic gcongrUnfoldStx] def evalGcongrUnfold : Tactic := fun stx => focus do
  let ds : Array Ident := stx[1][1].getSepArgs.map (⟨·⟩)
  for _ in [0:16] do
    let g ← getMainGoal
    let ty ← instantiateMVars (← g.getType)
    if isRelation ty then break
    if ty.isForall then
      let (_, g') ← g.intro1
      replaceMainGoal [g']
      continue
    let ty' ← g.withContext (whnf ty)
    unless ty'.isForall do
      throwError "gcongr_unfold: the goal is not a relation and does not unfold to a \
        quantified one:{indentExpr ty}"
    let (_, g') ← (← g.replaceTargetDefEq ty').intro1
    replaceMainGoal [g']
  unless ds.isEmpty do
    let lemmas ← ds.mapM fun d => `(Parser.Tactic.simpLemma| $d:ident)
    try evalTactic (← `(tactic| simp only [$lemmas,*]))
    catch e => throwError "gcongr_unfold: unfolding {ds} fails: {e.toMessageData}"
  if (← getUnsolvedGoals).isEmpty then return
  try evalTactic (← `(tactic| gcongr))
  catch e => throwError "gcongr_unfold: `gcongr` does not apply: {e.toMessageData}"
  evalTactic (← `(tactic|
    all_goals try (first | assumption | assumption_mod_cast | positivity | (norm_num; done))))
  let gs ← getUnsolvedGoals
  unless gs.isEmpty do
    throwError "gcongr_unfold: goals remain after `gcongr`: {gs.map (·.name)}\
      {← gs.mapM fun g => do return indentExpr (← g.getType)}"

/-! ## Boolean case splits -/

/-- A case split of `bool_cases`. -/
inductive BoolSplit where
  /-- `cases` on the local Boolean variable. -/
  | var (x : FVarId)
  /-- `by_cases` on the proposition. -/
  | prop (p : Expr)

/-- The propositions `p` of the subterms `decide p` and of the conditions of `if` and
dependent `if` in `e` that have no loose bound variables and no metavariables. -/
def splitProps (e : Expr) : Array Expr :=
  let rec go (e : Expr) (acc : Array Expr) : Array Expr :=
    let acc := match e.getAppFn.constName?, e.getAppNumArgs with
      | some ``Decidable.decide, 2 => acc.push (e.getArg! 0)
      | some ``ite, 5 => acc.push (e.getArg! 1)
      | some ``dite, 5 => acc.push (e.getArg! 1)
      | _, _ => acc
    match e with
    | .app f a => go a (go f acc)
    | .lam _ t b _ | .forallE _ t b _ => go b (go t acc)
    | .letE _ t v b _ => go b (go v (go t acc))
    | .mdata _ b | .proj _ _ b => go b acc
    | _ => acc
  (go e #[]).filter fun p => !p.hasLooseBVars && !p.hasMVar

/-- The first case split of `bool_cases` on the goal `g`: a local Boolean variable that
occurs in the goal, then one that occurs in a hypothesis, then a proposition of
`splitProps` of the goal of which neither it nor its negation is a hypothesis. -/
def boolSplit? (g : MVarId) : MetaM (Option BoolSplit) := g.withContext do
  let t ← instantiateMVars (← g.getType)
  let mut vars : Array LocalDecl := #[]
  for d in ← getLCtx do
    if d.isImplementationDetail || d.isLet then continue
    if (← whnfR (← instantiateMVars d.type)).isConstOf ``Bool then vars := vars.push d
  for d in vars do
    if t.containsFVar d.fvarId then return some (.var d.fvarId)
  for d in vars do
    for h in ← getLCtx do
      if h.isImplementationDetail then continue
      if (← instantiateMVars h.type).containsFVar d.fvarId then return some (.var d.fvarId)
  for p in splitProps t do
    let known ← (← getLCtx).anyM fun h => do
      if h.isImplementationDetail then return false
      let ty ← instantiateMVars h.type
      return ty == p || ty == mkNot p
    unless known do return some (.prop p)
  return none

/-- Split the goal `g` once by `boolSplit?`; `none` when there is no split. -/
def boolSplitOnce (g : MVarId) : MetaM (Option (List MVarId)) := do
  match ← boolSplit? g with
  | none => return none
  | some (.var x) => return some ((← g.cases x).toList.map (·.mvarId))
  | some (.prop p) =>
    let (a, b) ← g.byCases p
    return some [a.mvarId, b.mvarId]

/-- The number of rounds of `bool_cases`: it leaves at most `2 ^ maxBoolSplits`
goals. -/
def maxBoolSplits : Nat := 3

/-- `bool_cases` splits the main goal in at most three rounds; in each round every goal
is split once by `boolSplit?`: by `cases` on a local Boolean variable that occurs in
the goal or in a hypothesis, or else by `by_cases` on the proposition `p` of a subterm
`decide p` or of the condition of an `if` of the goal. It leaves at most eight goals,
and fails when the main goal has no such split. -/
syntax (name := boolCasesStx) "bool_cases" : tactic

@[tactic boolCasesStx] def evalBoolCases : Tactic := fun _ => do
  let g ← getMainGoal
  let some first ← boolSplitOnce g |
    throwError "bool_cases: the goal has no Boolean variable, `decide` or `if` to split on"
  let mut goals := first
  for _ in [1:maxBoolSplits] do
    let mut next : List MVarId := []
    for h in goals do
      next := next ++ ((← boolSplitOnce h).getD [h])
    goals := next
  replaceMainGoal goals

/-! ## Definitions in hypotheses -/

/-- The predicate definitions of the proposition `e` that `hyp_unfold` unfolds, added to
`acc`: the head of `e`, read through `¬`, `∧`, `∨`, `↔` and non-dependent `→` between
propositions to depth `depth`, when it is a definition that `isUnfoldable` accepts. -/
partial def predDefHeads (e : Expr) (depth : Nat) (acc : Array Name) :
    MetaM (Array Name) := do
  let e := e.cleanupAnnotations
  if depth == 0 then return acc
  if e.isAppOfArity ``Not 1 then return ← predDefHeads e.appArg! (depth - 1) acc
  if e.isAppOfArity ``And 2 || e.isAppOfArity ``Or 2 || e.isAppOfArity ``Iff 2 then
    let acc ← predDefHeads e.appFn!.appArg! (depth - 1) acc
    return ← predDefHeads e.appArg! (depth - 1) acc
  if let .forallE _ d b _ := e then
    if b.hasLooseBVars || !(← isProp d) then return acc
    let acc ← predDefHeads d (depth - 1) acc
    return ← predDefHeads b (depth - 1) acc
  let some n := e.getAppFn.constName? | return acc
  if acc.contains n then return acc
  if ← AutoDispatch.isUnfoldable n then return acc.push n
  return acc

/-- One round of `hyp_unfold` on `g`: the goal with its hypotheses changed, and whether
a hypothesis changed. -/
def hypUnfoldRound (g : MVarId) : MetaM (MVarId × Bool) := g.withContext do
  let mut g := g
  let mut changed := false
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    unless ← isProp ty do continue
    let ns ← predDefHeads ty 4 #[]
    if ns.isEmpty then continue
    let ty' ← deltaExpand ty ns.contains
    if ty' == ty then continue
    g ← g.replaceLocalDeclDefEq d.fvarId ty'
    changed := true
  return (g, changed)

/-- `hyp_unfold` unfolds the predicate definitions at the heads of the local hypotheses
(see the module docstring); it fails when there is none. -/
syntax (name := hypUnfoldStx) "hyp_unfold" : tactic

/-- The elaborator of `hyp_unfold`. -/
@[tactic hypUnfoldStx] def evalHypUnfold : Tactic := fun _ => do
  let g ← getMainGoal
  let (g, changed) ← hypUnfoldRound g
  unless changed do
    throwError "hyp_unfold: no hypothesis has a predicate definition at its head"
  let (g, _) ← hypUnfoldRound g
  replaceMainGoal [g]

/-! ## Extensionality over program types -/

/-- The number of `funext` steps that `funext_unfold` takes on an equality at the type
`T`: the binders of `T` (read with `whnfR`) up to a type registered with
`catcrypt_funext_type`, plus the leading binders of that type's unfolding; `none` when no
registered type is reached within `fuel` binders. -/
partial def funextArity? (T : Expr) (fuel : Nat := 8) : MetaM (Option Nat) := do
  if fuel == 0 then return none
  let T ← whnfR T
  if let some n := T.getAppFn.constName? then
    if (AutoDispatch.funextTypeExt.getState (← getEnv)).contains n then
      let some T' ← unfoldDefinition? T | return none
      let T' ← whnfR T'
      let k := T'.getForallArity
      return if k == 0 then none else some k
  if let .forallE nm d b bi := T then
    return ← withLocalDecl nm bi d fun x => do
      let some k ← funextArity? (b.instantiate1 x) (fuel - 1) | return none
      return some (k + 1)
  return none

/-- The bound on the unfoldings of one call of `unfoldOverApplied`. -/
def maxOverAppliedUnfolds : Nat := 64

/-- `e` with its beta-redexes reduced and each application of a definition that
`unfoldsBound` accepts to more arguments than its declared binders unfolded and
beta-reduced, at most `maxOverAppliedUnfolds` times. -/
def unfoldOverApplied (e : Expr) : MetaM Expr := do
  let count ← IO.mkRef 0
  transform e (post := fun t => do
    if t.isApp && t.getAppFn.isLambda then return .visit t.headBeta
    let some n := t.getAppFn.constName? | return .continue
    if (← count.get) ≥ maxOverAppliedUnfolds then return .continue
    unless ← unfoldsBound n do return .continue
    let some (.defnInfo d) := (← getEnv).find? n | return .continue
    unless t.getAppNumArgs > d.type.getForallArity do return .continue
    let some t' ← unfoldDefinition? t | return .continue
    count.modify (· + 1)
    return .visit t'.headBeta)

/-- `funext_unfold` applies `funext` to an equality of functions into a registered
program type and unfolds the over-applied definitions of the goal (see the module
docstring). It fails when the goal is not such an equality. -/
syntax (name := funextUnfoldStx) "funext_unfold" : tactic

/-- The elaborator of `funext_unfold`. -/
@[tactic funextUnfoldStx] def evalFunextUnfold : Tactic := fun _ => do
  let g ← getMainGoal
  let g ← g.withContext do
    let ty ← whnfR (← instantiateMVars (← g.getType))
    let some (T, _, _) := ty.eq? |
      throwError "funext_unfold: the goal is not an equality"
    let some k ← funextArity? T |
      throwError "funext_unfold: the goal is not an equality at a function type into a \
        registered program type:{indentExpr T}"
    let mut g := g
    for _ in [0:k] do
      let [g'] ← g.apply (← mkConstWithFreshMVarLevels ``funext) |
        throwError "funext_unfold: `funext` does not apply"
      let (_, g'') ← g'.intro1
      g := g''
    g.withContext do
      let t ← instantiateMVars (← g.getType)
      let t' ← unfoldOverApplied t
      if t' == t then return g
      g.replaceTargetDefEq t'
  replaceMainGoal [g]

/-! ## Ordered-semiring residuals -/

/-- The search depth of `ord_residual` without a depth argument. -/
def ordResidualDepth : Nat := 3

/-- The factor and summand bounds that `ord_residual` applies, in order. -/
def factorLemmas : List Name :=
  [``mul_le_of_le_one_left, ``mul_le_of_le_one_right, ``le_mul_of_one_le_left,
    ``le_mul_of_one_le_right, ``mul_le_one₀, ``le_add_of_le_of_nonneg,
    ``le_add_of_nonneg_of_le]

/-- The type `α` of a goal `a ≤ b` (read after `whnfR`) when `α` has `Semiring` and
`PartialOrder` instances. -/
def orderedType? (t : Expr) : MetaM (Option Expr) := do
  let t ← whnfR (← instantiateMVars t)
  unless t.isAppOfArity ``LE.le 4 do return none
  let α := t.getArg! 0
  let u ← getLevel α
  let some u' := u.dec | return none
  let some _ ← synthInstance? (mkApp (mkConst ``Semiring [u']) α) | return none
  let some _ ← synthInstance? (mkApp (mkConst ``PartialOrder [u']) α) | return none
  return some α

/-- `e` is the numeral `0`, `OfNat.ofNat _ 0 _`, or `Zero.zero`. -/
def isZeroLit (e : Expr) : Bool :=
  (e.isAppOfArity ``OfNat.ofNat 3 && (e.getArg! 1).rawNatLit? == some 0) ||
    e.isAppOfArity ``Zero.zero 2

/-- `g` is closed by one of the leaf closers of `ord_residual`. -/
def closeLeaf (g : MVarId) : TacticM Bool := do
  let t ← whnfR (← instantiateMVars (← g.getType))
  let nonneg := t.isAppOfArity ``LE.le 4 && isZeroLit (t.getArg! 2)
  let pos ← `(tactic| positivity)
  let tacs : List (TSyntax `tactic) :=
    [← `(tactic| assumption), ← `(tactic| exact le_rfl), ← `(tactic| assumption_mod_cast)] ++
      (if nonneg then [pos] else [])
  for tac in tacs do
    let s ← saveState
    try
      setGoals [g]
      evalTactic tac
      if (← getUnsolvedGoals).isEmpty then return true
      s.restore
    catch _ => s.restore
  return false

mutual

/-- Solve `g` by the search of `ord_residual` at depth `fuel`, or throw. -/
partial def solve (fuel : Nat) (g : MVarId) : TacticM Unit := do
  if ← g.isAssigned then return
  if ← closeLeaf g then return
  if fuel == 0 then throwError "ord_residual: depth exhausted"
  let env ← getEnv
  for n in factorLemmas do
    unless env.contains n do continue
    let s ← saveState
    try
      let gs ← withTransparency .instances <|
        g.apply (← mkConstWithFreshMVarLevels n) { synthAssignedInstances := false }
      solveAll (fuel - 1) gs
      return
    catch _ => s.restore
  let s ← saveState
  try
    setGoals [g]
    evalTactic (← `(tactic| gcongr))
    let gs ← getUnsolvedGoals
    solveAll (fuel - 1) gs
    return
  catch _ => s.restore
  throwError "ord_residual: no step closes{indentExpr (← g.getType)}"

/-- Solve each of `gs` by `solve fuel`, or throw. -/
partial def solveAll (fuel : Nat) (gs : List MVarId) : TacticM Unit := do
  for g' in gs do solve fuel g'

end

/-- `ord_residual` proves `a ≤ b` over an ordered semiring by the monotonicity search
described in the module docstring, to depth `n` (`ord_residual n`) or 3. It fails at once
on a goal that is not `_ ≤ _` over a type with `Semiring` and `PartialOrder` instances. -/
syntax (name := ordResidualStx) "ord_residual" (ppSpace num)? : tactic

/-- The elaborator of `ord_residual`. -/
@[tactic ordResidualStx] def evalOrdResidual : Tactic := fun stx => do
  let depth := match stx[1].getOptional? with
    | some n => n.isNatLit?.getD ordResidualDepth
    | none => ordResidualDepth
  let g ← getMainGoal
  let rest := (← getGoals).drop 1
  g.withContext do
    if (← orderedType? (← g.getType)).isNone then
      throwError "ord_residual: the goal is not `_ ≤ _` over an ordered semiring"
    solve depth g
  setGoals rest

end CatCrypt.Tactics.AutoArms

end

/-! ## Arms of `catcrypt_auto` -/

catcrypt_auto_arm "distance inequality" order 10 := "hop_chain%HOP"
catcrypt_auto_arm "distance inequality" order 11 := "hop_chain!%HOP"
catcrypt_auto_arm "distance inequality" order 20 := "sum_atoms_le"
catcrypt_auto_arm "monotonicity inequality" order 10 := "gcongr_unfold%DEFS"
catcrypt_auto_arm "monotonicity inequality" order 20 := "gcongr"
catcrypt_auto_arm "monotonicity inequality" order 40 le_only := "sum_atoms_le"
catcrypt_auto_arm "other" order 10 le_only := "sum_atoms_le"
catcrypt_auto_arm "other" order 25 := "(bool_cases <;> first | rfl | decide | %SIMP_ALL)"
catcrypt_auto_arm "SPComp equality" order 25 :=
  "((first | bool_cases | skip) <;> first | rfl | decide | %SIMP_ALL)"

catcrypt_auto_arm "other" order 35 := "(hyp_unfold; first | grind%GRIND | %SIMP_ALL)"
catcrypt_auto_arm "heap read after write" order 30 :=
  "(hyp_unfold; first | grind%GRIND | %SIMP_ALL)"
catcrypt_auto_arm "SPComp equality" order 30 := "(hyp_unfold; first | grind%GRIND | %SIMP_ALL)"

catcrypt_auto_arm "SPComp equality" order 15 :=
  "(funext_unfold; first | rfl | grind%GRIND | %SIMP_ALL)"
catcrypt_auto_arm "other" order 36 := "(funext_unfold; first | rfl | grind%GRIND | %SIMP_ALL)"
catcrypt_auto_arm "distance inequality" order 45 := "ord_residual"
catcrypt_auto_arm "monotonicity inequality" order 45 := "ord_residual"
catcrypt_auto_arm "other" order 15 := "ord_residual"
