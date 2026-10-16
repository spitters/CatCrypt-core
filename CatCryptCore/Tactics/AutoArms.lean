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
public import CatCryptCore.Tactics.Triangle
public import CatCryptCore.Tactics.AutoHopRegistry
public meta import CatCryptCore.Tactics.AutoHopRegistry
public import CatCryptCore.Tactics.AutoDispatchCore

/-!
# Hop chains over registered pseudometrics, sums of atoms, and monotonicity

This module provides three procedures.

* `hop_chain [facts]` proves `d x y ≤ e` for a distance `d` registered with the
  attribute `@[hop_metric]`. It collects hop facts `d u v ≤ b` (and `d u v = b`) from the
  local context and from its arguments, searches the graph whose vertices are endpoints
  and whose edges are hop facts (both directions when a symmetry lemma is registered) for
  a path from `x` to `y`, composes the triangle lemma along the path, and closes the
  residual inequality between the sum of the hop bounds and `e` with `sum_atoms_le`.
* `sum_atoms_le` decides inequalities between ℕ-weighted sums of atoms in an ordered
  commutative semiring whose elements are nonnegative (`ℝ≥0∞` in practice), using in
  addition hypotheses `a ≤ b` between atoms; a goal outside the fragment is read again
  after expanding sums over `Finset.range (n + 1)` and reducing conditionals on Boolean
  literal equations.
* `gcongr_unfold [defs]` introduces the binders of a goal that unfolds to a universally
  quantified relation (for example `Monotone f`), unfolds the listed definitions, and runs
  `gcongr` with a fixed discharger.

The attribute `@[hop_metric]` and the distance views are in
`CatCryptCore.Tactics.AutoHopRegistry`. No distance is built into the procedures; the
registrations of `Advantage`, `AdvantageA` and `sdist` are in
`CatCryptCore.Tactics.AutoMetrics`.

The module registers with `catcrypt_auto` (`CatCryptCore.Tactics.AutoDispatchCore`) the
arms `hop_chain` and `sum_atoms_le` of the distance shape, `gcongr_unfold`, `gcongr` and
`sum_atoms_le` of the monotonicity shape, and `sum_atoms_le` of the shape `other`.
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

/-- The index of `e` among `nodes` up to reducible definitional equality. -/
def nodeIdx (nodes : Array Expr) (e : Expr) : MetaM (Option Nat) := do
  for k in [0:nodes.size] do
    if ← withReducible (isDefEq nodes[k]! e) then return some k
  return none

/-- Breadth-first search for a path of hops from `src` to `dst`. -/
def findPath (hops : Array Hop) (src dst : Expr) : MetaM (Option (Array Hop)) := do
  let mut nodes : Array Expr := #[src, dst]
  let mut edges : Array (Nat × Nat × Hop) := #[]
  for hop in hops do
    let a ← match ← nodeIdx nodes hop.src with
      | some a => pure a
      | none => do nodes := nodes.push hop.src; pure (nodes.size - 1)
    let b ← match ← nodeIdx nodes hop.dst with
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
        left than it is bounded on the right (by itself or by a hypothesis `a ≤ b`) in{indentExpr ty}"
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

/-- The core of `hop_chain`: prove the main goal from the elaborated argument proofs
`extra` and the hypotheses of the local context. -/
def hopChainCore (extra : Array Expr) : TacticM Unit := do
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
  let mut hops : Array Hop := #[]
  for c in cands do
    if let some hop ← hopOf? gv c then
      hops := hops.push hop
      if let some rev ← reverseHop? gv hop then hops := hops.push rev
  let some path ← findPath hops src dst |
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
  try sumAtomsLeNorm res.mvarId!
  catch e =>
    throwError "hop_chain: the hops compose to{indentExpr bound}\nbut the residual \
      inequality is not closed: {e.toMessageData}"
  replaceMainGoal []

/-- `hop_chain [h₁, …, hₙ]` proves `d x y ≤ e` for a distance `d` registered with
`@[hop_metric]`.

Hop facts are proofs of `d … u v ≤ b` or `d … u v = b` whose context arguments agree
with the goal's: the arguments `hᵢ` and the hypotheses of the local context. A
universally quantified hypothesis is never a hop fact; pass its instances as arguments.
Terms headed by a registered definition or equation are unfolded to the distance first.
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

end CatCrypt.Tactics.AutoArms

end

/-! ## Arms of `catcrypt_auto` -/

catcrypt_auto_arm "distance inequality" order 10 := "hop_chain%HOP"
catcrypt_auto_arm "distance inequality" order 20 := "sum_atoms_le"
catcrypt_auto_arm "monotonicity inequality" order 10 := "gcongr_unfold%DEFS"
catcrypt_auto_arm "monotonicity inequality" order 20 := "gcongr"
catcrypt_auto_arm "monotonicity inequality" order 40 le_only := "sum_atoms_le"
catcrypt_auto_arm "other" order 10 le_only := "sum_atoms_le"
