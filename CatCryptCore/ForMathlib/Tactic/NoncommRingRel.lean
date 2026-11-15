/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Tactic.NoncommRing
public import Mathlib.Tactic.Module
public import Mathlib.Tactic.LinearCombination
public import Mathlib.Algebra.Star.Basic
public meta import Lean.Elab.Tactic

/-!
# The `noncomm_ring_rel` tactic: ring identities modulo word relations

`noncomm_ring_rel [h₁, …, hₙ]` proves an equation `p = q` in a not necessarily commutative ring
`R` from hypotheses `hᵢ : ∀ xs, uᵢ = vᵢ` in `R`, where `uᵢ` is typically a product of atoms
(a word): idempotents `P * P = P`, involutions `X * X = 1`, isometries `star U * U = 1`, partial
isometries `W * star W * W = W`, orthogonality `P * Q = 0`, commutation `Y * X = X * Y`,
self-adjointness `star F = F`.

## Procedure

1. Orientation. Each relation is used from the side of larger degree (number of atoms in a
   product, the maximum over the summands of a sum) to the side of smaller degree; on equal
   degree it is used from left to right as given, so a commutation hypothesis `Y * X = X * Y`
   fixes the order of `X` and `Y`.
2. Star closure. When `R` has a `star` and the goal or a relation mentions `star`, the relation
   `star u = star v` is added for each relation, normalised by `star_mul`, `star_star` and the
   relations of degree one (`star F = F`).
3. Right-associated forms. For a relation `u₁ * ⋯ * uₖ = v` with `k ≥ 2` the tactic adds
   `∀ Z, u₁ * (u₂ * ⋯ * (uₖ * Z)) = v * Z` (right-associated), the analogue for monoids of the
   `@[reassoc]` lemmas of category theory, so that the relation applies inside the
   right-associated normal form of a longer product.
4. Normalisation. `simp only` with the lemmas of `noncomm_ring` (distributivity, `mul_assoc`,
   numerals as `nsmul`, scalars pulled to the front) together with the relations and their
   right-associated forms; then `abel1`, else `match_scalars` with each scalar goal closed by
   `ring1` or by `linear_combination h` for a hypothesis `h` of the list whose type is an
   equation outside `R` (a relation between scalars).

When the oriented relations are confluent, the normal form of step 4 is the normal form of
Bergman's diamond lemma in the free algebra modulo the relations, and the tactic decides the
identity. `noncomm_ring_rel? [h₁, …]` runs the same procedure and reports the oriented relations
and the critical pairs (overlaps `u₁ = a b`, `u₂ = b c` and inclusions `u₁ = a u₂ b`, with the
atoms unified) whose two reducts the procedure does not join; such a pair is a derived relation
that can be proved separately and added to the list. A failing `noncomm_ring_rel` reports the
unresolved critical pairs in its error.

## Main declarations

* the tactics `noncomm_ring_rel [h₁, …]` and `noncomm_ring_rel? [h₁, …]`.
-/

public meta section

set_option autoImplicit false

namespace CatCryptCore.Tactic.NoncommRingRel

open Lean Meta Elab Tactic

/-- The factors of a product, read through every `HMul.hMul`. -/
partial def wordOf (e : Expr) : List Expr :=
  match e.getAppFnArgs with
  | (``HMul.hMul, #[_, _, _, _, a, b]) => wordOf a ++ wordOf b
  | _ => [e]

/-- The degree of a ring expression: the number of atoms of a product, the maximum over the
summands of a sum, zero for a numeral. -/
partial def degree (e : Expr) : Nat :=
  match e.getAppFnArgs with
  | (``HMul.hMul, #[_, _, _, _, a, b]) => degree a + degree b
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => max (degree a) (degree b)
  | (``HSub.hSub, #[_, _, _, _, a, b]) => max (degree a) (degree b)
  | (``Neg.neg, #[_, _, a]) => degree a
  | (``HSMul.hSMul, #[_, _, _, _, _, a]) => degree a
  | (``HPow.hPow, #[_, _, _, _, a, n]) => degree a * (n.nat?.getD 1)
  | (``OfNat.ofNat, _) => 0
  | (``Zero.zero, _) => 0
  | (``One.one, _) => 0
  | _ => 1

/-- A relation: a proof of `∀ xs, lhs = rhs` in the ring. -/
structure Rule where
  /-- The proof of the relation. -/
  proof : Expr
  /-- Its type `∀ xs, lhs = rhs`. -/
  type : Expr
deriving Inhabited

/-- The proof `fun xs => (h xs).symm` of the reversed relation. -/
def Rule.symm (r : Rule) : MetaM Rule := do
  forallTelescope r.type fun xs body => do
    let some (_, _, _) := body.eq? | throwError "noncomm_ring_rel: not an equation{indentExpr body}"
    let p ← mkEqSymm (mkAppN r.proof xs)
    let p ← mkLambdaFVars xs p
    return { proof := p, type := ← inferType p }

/-- `simp only [names]` applied to the type of a proof: the proof of the simplified statement,
or `none` when the statement simplifies to `True`. -/
def simpProof (names : List Name) (extra : Array Expr) (p : Expr) : MetaM (Option Expr) := do
  let mut thms : SimpTheorems := {}
  for n in names do
    if (← getEnv).contains n then
      thms ← thms.addConst n
  for e in extra do
    thms ← thms.add (.stx (← mkFreshId) (mkNullNode)) #[] e
  let ctx ← Simp.mkContext (simpTheorems := #[thms]) (congrTheorems := ← getSimpCongrTheorems)
  let ty ← inferType p
  let (r, _) ← simp ty ctx
  if r.expr.isTrue then return none
  match r.proof? with
  | none => return some (← mkExpectedTypeHint p r.expr)
  | some h => return some (← mkEqMP h p)

/-- The simp lemmas that right-associate a product and remove units. -/
def assocNames : List Name :=
  [``mul_assoc, ``one_mul, ``mul_one, ``zero_mul, ``mul_zero]

/-- The simp lemmas that turn `star` of a square matrix into `Mᴴ` and push `ᴴ` through products,
sums and units; they are used when the environment contains them. -/
def matrixStarNames : List Name :=
  [`Matrix.star_eq_conjTranspose, `Matrix.conjTranspose_mul, `Matrix.conjTranspose_conjTranspose,
    `Matrix.conjTranspose_one, `Matrix.conjTranspose_zero, `Matrix.conjTranspose_add,
    `Matrix.conjTranspose_sub, `Matrix.conjTranspose_neg]

/-- The simp lemmas that push `star` through products, sums and units. -/
def starNames : List Name :=
  [``star_mul, ``star_star, ``star_one, ``star_zero, ``star_add, ``star_sub, ``star_neg,
    ``mul_assoc, ``one_mul, ``mul_one, ``zero_mul, ``mul_zero] ++ matrixStarNames

/-- Orients a relation from its side of larger degree to its side of smaller degree. -/
def orient (r : Rule) : MetaM Rule := do
  let flip ← forallTelescope r.type fun _ body => do
    let some (_, l, rhs) := body.eq? |
      throwError "noncomm_ring_rel: not an equation{indentExpr body}"
    return decide (degree l < degree rhs)
  if flip then r.symm else return r

/-- The right-associated form `∀ xs Z, u₁ * (⋯ * (uₖ * Z)) = v * Z` of a relation whose
left side is a product, or `none` for a relation whose left side is a single atom. -/
def reassoc (r : Rule) : MetaM (Option Rule) := do
  forallTelescope r.type fun xs body => do
    let some (ty, l, rhs) := body.eq? | return none
    if (wordOf l).length < 2 then return none
    unless l.isAppOfArity ``HMul.hMul 6 do return none
    let mulFn := l.appFn!.appFn!
    withLocalDeclD `Z ty fun z => do
      let lz := mkApp2 mulFn l z
      let rz := mkApp2 mulFn rhs z
      let p ← mkCongrArg (← withLocalDeclD `y ty fun y => mkLambdaFVars #[y] (mkApp2 mulFn y z))
        (mkAppN r.proof xs)
      let p ← mkExpectedTypeHint p (← mkEq lz rz)
      let some p ← simpProof assocNames #[] p | return none
      let p ← mkLambdaFVars (xs.push z) p
      return some { proof := p, type := ← inferType p }

/-- The relation `∀ xs, star lhs = star rhs` normalised by `starNames` and the relations `deg1`
(relations whose left side is a single atom, such as `star F = F`). -/
def starRule (r : Rule) (deg1 : Array Expr) : MetaM (Option Rule) := do
  forallTelescope r.type fun xs body => do
    let some (ty, _, _) := body.eq? | return none
    let starFn ← mkAppOptM ``Star.star #[ty, none]
    let p ← mkCongrArg starFn (mkAppN r.proof xs)
    let some p ← simpProof starNames deg1 p | return none
    let p ← mkLambdaFVars xs p
    return some { proof := p, type := ← inferType p }

/-- Whether an expression mentions `star` or the conjugate transpose of a matrix. -/
def mentionsStar (e : Expr) : Bool :=
  (e.find? fun f => f.isConstOf ``Star.star || f.isConstOf `Matrix.conjTranspose).isSome

/-- The relations and scalar hypotheses of a call. -/
structure Setup where
  /-- The oriented relations. -/
  rules : Array Rule
  /-- The right-associated forms of the relations. -/
  reassocs : Array Rule
  /-- Hypotheses that are equations outside the ring. -/
  scalars : Array Expr

/-- Elaborates the hypotheses and builds the oriented relations, their star closure and their
right-associated forms, for a goal that is an equation in `ty`. -/
def setup (ty goal : Expr) (hs : Array Term) : TacticM Setup := do
  let mut rules : Array Rule := #[]
  let mut scalars : Array Expr := #[]
  for h in hs do
    let p ← elabTerm h none
    let p ← instantiateMVars p
    let t ← instantiateMVars (← inferType p)
    let inR ← forallTelescope t fun _ body => do
      match body.eq? with
      | some (α, _, _) => isDefEq α ty
      | none => return false
    if inR then
      rules := rules.push (← orient { proof := p, type := t })
    else
      scalars := scalars.push p
  let hasStar := mentionsStar goal || rules.any (mentionsStar ·.type)
  if hasStar && (← synthInstance? (← mkAppM ``Star #[ty])).isSome then
    let deg1 ← rules.filterM fun r => forallTelescope r.type fun _ body => do
      match body.eq? with
      | some (_, l, _) => return (wordOf l).length == 1
      | none => return false
    let mut extra : Array Rule := #[]
    for r in rules do
      if let some s ← starRule r (deg1.map (·.proof)) then
        let s ← orient s
        let dup ← (rules ++ extra).anyM fun q => isDefEq q.type s.type
        unless dup do extra := extra.push s
    rules := rules ++ extra
  let mut reassocs : Array Rule := #[]
  for r in rules do
    if let some s ← reassoc r then reassocs := reassocs.push s
  return { rules, reassocs, scalars }

/-- The normalising tactic of step 4 with the given relations and scalar hypotheses. -/
def mainTac (rules : Array Term) (scalars : Array Term) (useStar : Bool) :
    TacticM (TSyntax `tactic) := do
  let env ← getEnv
  let starLemmas : Array Term := if useStar then
      ((starNames.filter env.contains).map fun n => (mkCIdent n : Term)).toArray
    else #[]
  let lemmas ← (starLemmas ++ rules).mapM fun t => `(Parser.Tactic.simpLemma| $t:term)
  let mut scalarTac ← `(tactic| ring1)
  for s in scalars.reverse do
    scalarTac ← `(tactic| first | linear_combination $s:term | $scalarTac:tactic)
  scalarTac ← `(tactic| first | ring1 | $scalarTac:tactic)
  `(tactic| (
    (try simp only [add_mul, mul_add, sub_eq_add_neg, mul_assoc, pow_one, pow_zero, pow_succ,
      one_mul, mul_one, zero_mul, mul_zero, Mathlib.Tactic.NoncommRing.nat_lit_mul_eq_nsmul,
      Mathlib.Tactic.NoncommRing.mul_nat_lit_eq_nsmul, mul_smul_comm, smul_mul_assoc, neg_mul,
      mul_neg, smul_add, smul_neg, smul_zero, $lemmas,*]) <;>
    first
      | abel1
      | (match_scalars <;> $scalarTac:tactic)))

/-- Whether `tac` closes `g`; the state is restored afterwards. -/
def closes (tac : TSyntax `tactic) (g : MVarId) : TacticM Bool := do
  let s ← saveState
  try
    let gs ← Term.withoutErrToSorry <| Tactic.run g (withoutRecover (evalTactic tac))
    let ok := gs.isEmpty
    s.restore
    return ok
  catch _ =>
    s.restore
    return false

/-- The right-associated product of a nonempty list of factors, with the multiplication
`mulFn`. -/
def mkWord (mulFn : Expr) : List Expr → Option Expr
  | [] => none
  | [a] => some a
  | a :: as => (mkWord mulFn as).map (mkApp2 mulFn a)

/-- `a * x * b` with the empty factors left out. -/
def wrap (mulFn : Expr) (a : List Expr) (x : Expr) (b : List Expr) : Expr :=
  let xb := match mkWord mulFn b with
    | some w => mkApp2 mulFn x w
    | none => x
  a.foldr (fun f acc => mkApp2 mulFn f acc) xb

/-- The left side as a word, the right side and the multiplication of a relation with its
bound variables instantiated by fresh metavariables. -/
def instRule (r : Rule) : MetaM (Option (List Expr × Expr × Expr)) := do
  let (_, _, body) ← forallMetaTelescope r.type
  let some (_, l, rhs) := body.eq? | return none
  unless l.isAppOfArity ``HMul.hMul 6 do return none
  return some (wordOf l, rhs, l.appFn!.appFn!)

/-- The critical pairs of two relations: for each overlap of a suffix of the left side of `r₁`
with a prefix of the left side of `r₂`, and for each occurrence of the left side of `r₂`
inside the left side of `r₁`, the equation between the two reducts, with the unassigned
variables abstracted. -/
def criticalPairs (r₁ r₂ : Rule) (same : Bool) : MetaM (Array Expr) := do
  let some (l₁, _, _) ← withNewMCtxDepth (instRule r₁) | return #[]
  let some (l₂, _, _) ← withNewMCtxDepth (instRule r₂) | return #[]
  let n₁ := l₁.length
  let n₂ := l₂.length
  let mut out : Array Expr := #[]
  -- overlaps: suffix of length k of l₁ with prefix of length k of l₂
  for k in List.range' 1 (min n₁ n₂ - 1) do
    let res ← withNewMCtxDepth do
      let some (a₁, v₁, mul) ← instRule r₁ | return none
      let some (a₂, v₂, _) ← instRule r₂ | return none
      let ok ← (List.zip (a₁.drop (n₁ - k)) (a₂.take k)).allM fun (x, y) => isDefEq x y
      if !ok then return none
      let lhs := wrap mul [] v₁ (a₂.drop k)
      let rhs := wrap mul (a₁.take (n₁ - k)) v₂ []
      let eq ← instantiateMVars (← mkEq lhs rhs)
      return some (← abstractMVars eq).expr
    if let some e := res then out := out.push e
  -- inclusions: l₂ inside l₁ at position i
  if !same && n₂ < n₁ then
    for i in List.range (n₁ - n₂ + 1) do
      let res ← withNewMCtxDepth do
        let some (a₁, v₁, mul) ← instRule r₁ | return none
        let some (a₂, v₂, _) ← instRule r₂ | return none
        let ok ← (List.zip ((a₁.drop i).take n₂) a₂).allM fun (x, y) => isDefEq x y
        if !ok then return none
        let rhs := wrap mul (a₁.take i) v₂ (a₁.drop (i + n₂))
        let eq ← instantiateMVars (← mkEq v₁ rhs)
        return some (← abstractMVars eq).expr
      if let some e := res then out := out.push e
  return out

/-- The critical pairs of the relations that `tac` does not close. -/
def unresolved (rules : Array Rule) (tac : TSyntax `tactic) : TacticM (Array Expr) := do
  let mut out : Array Expr := #[]
  for i in List.range rules.size do
    for j in List.range rules.size do
      for e in ← criticalPairs rules[i]! rules[j]! (i == j) do
        let ok ← lambdaTelescope e fun _ eq => do
          let g ← mkFreshExprMVar eq
          closes tac g.mvarId!
        unless ok do
          out := out.push (← lambdaTelescope e fun xs eq => mkForallFVars xs eq)
  return out

/-- `noncomm_ring_rel [h₁, …, hₙ]` proves an equation in a not necessarily commutative ring
modulo the word relations `hᵢ : ∀ xs, u = v` (idempotents, involutions, isometries, partial
isometries, orthogonality, commutation, self-adjointness). Each relation is oriented by degree,
closed under `star` when the goal mentions `star`, and used with its right-associated form
`∀ Z, u₁ * (⋯ * (uₖ * Z)) = v * Z` in the `simp only` normalisation of `noncomm_ring`; the goal
is then closed by `abel1` or `match_scalars` with `ring1`. A hypothesis that is an equation
outside the ring is used as `linear_combination h` on the scalar goals. -/
syntax (name := noncommRingRel) "noncomm_ring_rel" (" [" term,* "]")? : tactic

/-- `noncomm_ring_rel? [h₁, …, hₙ]` runs `noncomm_ring_rel [h₁, …, hₙ]` and reports the oriented
relations and the critical pairs of the relations that its normalisation does not join. -/
syntax (name := noncommRingRelQ) "noncomm_ring_rel?" (" [" term,* "]")? : tactic

/-- The procedure shared by `noncomm_ring_rel` and `noncomm_ring_rel?`. -/
def run (hs : Array Term) (report : Bool) : TacticM Unit := withMainContext do
  let goal ← instantiateMVars (← getMainTarget)
  let some (ty, _, _) := goal.eq? | throwError "noncomm_ring_rel: the goal is not an equation"
  let s ← setup ty goal hs
  let useStar := mentionsStar goal || s.rules.any (mentionsStar ·.type)
  let ruleStx ← (s.rules ++ s.reassocs).mapM fun r => Term.exprToSyntax r.proof
  let scalarStx ← s.scalars.mapM fun e => Term.exprToSyntax e
  let tac ← mainTac ruleStx scalarStx useStar
  if report then
    let pairs ← unresolved s.rules tac
    let ruleMsgs := s.rules.map fun r => m!"{r.type}"
    let pairMsgs := pairs.map fun e => m!"{e}"
    logInfo m!"noncomm_ring_rel: oriented relations:{indentD (MessageData.joinSep ruleMsgs.toList
      Format.line)}\n{if pairs.isEmpty then m!"all critical pairs resolve" else
        m!"unresolved critical pairs:{indentD (MessageData.joinSep pairMsgs.toList
          Format.line)}"}"
  let s0 ← saveState
  try
    Term.withoutErrToSorry <| withoutRecover <| evalTactic tac
  catch ex =>
    let pairs ← unresolved s.rules tac
    s0.restore
    if pairs.isEmpty then
      throwError "noncomm_ring_rel failed: {ex.toMessageData}"
    else
      throwError "noncomm_ring_rel failed: {ex.toMessageData}\nunresolved critical pairs:{
        indentD (MessageData.joinSep (pairs.map (m!"{·}")).toList Format.line)}"

elab_rules : tactic
  | `(tactic| noncomm_ring_rel $[[$hs,*]]?) => run (hs.map (·.getElems) |>.getD #[]) false
  | `(tactic| noncomm_ring_rel? $[[$hs,*]]?) => run (hs.map (·.getElems) |>.getD #[]) true

end CatCryptCore.Tactic.NoncommRingRel
