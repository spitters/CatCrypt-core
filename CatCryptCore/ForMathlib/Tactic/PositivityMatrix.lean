/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.ForMathlib.Tactic.PositivityStar
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Data.Matrix.Block
public meta import Lean.Elab.Tactic

/-!
# `positivity` extensions for matrices and the tactic `psd`

Over an `RCLike` field `𝕜`, the positive semidefinite matrices form the positive cone of the
Loewner order `A ≤ B ↔ (B - A).PosSemidef` (scoped to `MatrixOrder`). This cone contains `0`,
`1`, the Gram matrices `cᴴ * c` and `c * cᴴ` for rectangular `c`, the rank-one matrices
`vecMulVec v (star v)` and the diagonal matrices with nonnegative entries, and it is closed under
sums, finite sums, nonnegative scalars, congruences `cᴴ * a * c` and `c * a * cᴴ` for rectangular
`c`, Kronecker products, compressions `a.submatrix e e`, reindexing `reindex e e a` and block
diagonal sums `blockDiagonal`.

The extensions below make `positivity` prove `0 ≤ X` for `X : Matrix n n 𝕜` built by these rules
from atoms with a hypothesis `0 ≤ a`, `a.PosSemidef`, `a.PosDef`, `a ≤ b` (for `b - a`),
`IsStarProjection a`, or a universally quantified form `∀ i, (a i).PosSemidef`,
`∀ i, 0 ≤ a i`. Together with the extensions of `PositivityStar` (star squares, star
projections, the continuous functional calculus) they reach `CFC.sqrt a`, `cfc f a` and `1 - p`
at matrix type.

## Tactics

* `psd` proves `0 ≤ X`, `X.PosSemidef` and `A ≤ B` (Loewner) by these rules, with the scopes
  `MatrixOrder` and `ComplexOrder` open.
* `psd?` runs `psd`; when it fails it names the subterm that no rule proves nonnegative.

## Main results

* `Matrix.PosSemidef.blockDiagonal`: a block diagonal matrix with positive semidefinite blocks is
  positive semidefinite.
* `Matrix.PosSemidef.reindex`: reindexing by one equivalence on both sides keeps positive
  semidefiniteness.
-/

@[expose] public section

set_option autoImplicit false

namespace Matrix

open scoped ComplexOrder Kronecker

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The congruence `Bᴴ * (A * B)` of a positive semidefinite matrix is positive semidefinite. -/
theorem PosSemidef.conjTranspose_mul_mul_same_assoc {m n : Type*} [Fintype n] [Finite m]
    {A : Matrix n n 𝕜} (hA : A.PosSemidef) (B : Matrix n m 𝕜) :
    (Bᴴ * (A * B)).PosSemidef := by
  have := Fintype.ofFinite m
  simpa only [Matrix.mul_assoc] using hA.conjTranspose_mul_mul_same B

/-- The congruence `B * (A * Bᴴ)` of a positive semidefinite matrix is positive semidefinite. -/
theorem PosSemidef.mul_mul_conjTranspose_same_assoc {m n : Type*} [Fintype n] [Finite m]
    {A : Matrix n n 𝕜} (hA : A.PosSemidef) (B : Matrix m n 𝕜) :
    (B * (A * Bᴴ)).PosSemidef := by
  have := Fintype.ofFinite m
  simpa only [Matrix.mul_assoc] using hA.mul_mul_conjTranspose_same B

/-- Reindexing a positive semidefinite matrix by one equivalence on rows and columns keeps it
positive semidefinite. -/
theorem PosSemidef.reindex {m n : Type*} {A : Matrix n n 𝕜} (hA : A.PosSemidef) (e : n ≃ m) :
    (Matrix.reindex e e A).PosSemidef := by
  simpa only [reindex_apply] using hA.submatrix e.symm

/-- A diagonal matrix whose entries are nonnegative is positive semidefinite. -/
theorem posSemidef_diagonal_of_forall_nonneg {n : Type*} [DecidableEq n] {d : n → 𝕜}
    (h : ∀ i, 0 ≤ d i) : (diagonal d).PosSemidef :=
  PosSemidef.diagonal (Pi.le_def.mpr h)

/-- A block diagonal matrix whose blocks are positive semidefinite is positive semidefinite. -/
theorem PosSemidef.blockDiagonal {m o : Type*} [Finite m] [Finite o] [DecidableEq o]
    {M : o → Matrix m m 𝕜} (hM : ∀ k, (M k).PosSemidef) :
    (Matrix.blockDiagonal M).PosSemidef := by
  have := Fintype.ofFinite o
  have h : Matrix.blockDiagonal M =
      ∑ k, M k ⊗ₖ vecMulVec (Pi.single k 1) (star (Pi.single k 1)) := by
    ext ⟨i, t⟩ ⟨j, t'⟩
    simp [blockDiagonal_apply, Matrix.sum_apply, kroneckerMap_apply, vecMulVec_apply,
      Pi.single_apply]
    grind
  rw [h]
  exact posSemidef_sum _ fun k _ => (hM k).kronecker (posSemidef_vecMulVec_self_star _)

end Matrix

end

public meta section

namespace CatCryptCore.Tactic.PositivityMatrix

open Lean Meta Elab Tactic Qq Mathlib.Meta.Positivity
open CatCryptCore.Tactic.PositivityStar

/-- `(n, 𝕜)` when `α` is `Matrix n n 𝕜` with `RCLike 𝕜`. -/
def matSquare? (α : Expr) : MetaM (Option (Expr × Expr)) := do
  let α := (← instantiateMVars α).consumeMData
  unless α.isAppOfArity ``Matrix 3 do return none
  let #[m, n, k] := α.getAppArgs | return none
  unless ← withReducible <| isDefEq m n do return none
  match ← trySynthInstance (← mkAppM ``RCLike #[k]) with
  | .some _ => return some (n, k)
  | _ => return none

/-- A proof of `0 ≤ e` by the core of `positivity`, with the Loewner order at a square matrix
type over an `RCLike` field and the synthesized order elsewhere. -/
def nonnegProof (e : Expr) : MetaM (Option Expr) := do
  try
    let ⟨u, α, e⟩ ← inferTypeQ' e
    let zα ← synthInstanceQ q(Zero $α)
    let pα : Q(PartialOrder $α) ← match ← matSquare? α with
      | some (n, k) => mkAppOptM ``Matrix.instPartialOrder #[k, n, none]
      | none => synthInstanceQ q(PartialOrder $α)
    coreNonneg (u := u) zα pα e
  catch _ => return none

/-- A hypothesis `∀ xs, P` of the local context whose instance at some `xs` is `goal`, applied to
those `xs`. Only hypotheses whose conclusion has the head `head` are tried. -/
def forallHyp (goal : Expr) (head : Name) : MetaM (Option Expr) := do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t ← instantiateMVars d.type
    unless t.isForall && t.getForallBody.isAppOf head do continue
    let r ← withoutModifyingState do
      let (xs, _, body) ← forallMetaTelescopeReducing t
      if ← withTransparency .instances <| isDefEq body goal then
        let pf ← instantiateMVars (mkAppN d.toExpr xs)
        if pf.hasExprMVar then return none
        return some pf
      return none
    if r.isSome then return r
  return none

/-- A proof of `X.PosSemidef` from a hypothesis: `X.PosSemidef`, `X.PosDef`, `a ≤ b` for
`X = b - a`, or a universally quantified `∀ xs, (Y xs).PosSemidef`. -/
def psdHyp (x : Expr) : MetaM (Option Expr) := do
  let target ← mkAppM ``Matrix.PosSemidef #[x]
  let xc := x.consumeMData
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let t := (← instantiateMVars d.type).consumeMData
    if t.isAppOf ``Matrix.PosSemidef then
      if ← isSame t.appArg! x then return some d.toExpr
    if t.isAppOf ``Matrix.PosDef then
      if ← isSame t.appArg! x then return some (← mkAppM ``Matrix.PosDef.posSemidef #[d.toExpr])
    if t.isAppOfArity ``LE.le 4 && xc.isAppOfArity ``HSub.hSub 6 then
      if (← isSame t.appArg! xc.appFn!.appArg!) && (← isSame t.appFn!.appArg! xc.appArg!) then
        if ← isDefEq (← inferType d.toExpr) target then
          return some (← mkExpectedTypeHint d.toExpr target)
  forallHyp target ``Matrix.PosSemidef

/-- A proof of `x.PosSemidef` for a square matrix `x`: a hypothesis, or `0 ≤ x` by the core of
`positivity`. -/
def psdOf (x : Expr) : MetaM (Option Expr) := do
  if let some h ← psdHyp x then return some h
  let some p ← nonnegProof x | return none
  return some (← mkAppM ``Matrix.LE.le.posSemidef #[p])

/-- The result `0 ≤ e` from a proof `h` of `e.PosSemidef`. -/
def ofPSD {u : Level} {α : Q(Type u)} (zα : Q(Zero $α)) (pα : Q(PartialOrder $α))
    (e : Q($α)) (h : Expr) : MetaM (Strictness zα e (some pα)) := do
  nonnegOf zα pα e (← mkAppM ``Matrix.PosSemidef.nonneg #[h])

/-- Whether `x` is `cᴴ` (or `star c`) up to unfolding of instances. -/
def isConjTransposeOf (x c : Expr) : MetaM Bool := do
  try
    let ct ← mkAppM ``Matrix.conjTranspose #[c]
    withTransparency .instances <| isDefEq x ct
  catch _ => pure false

/-- The factors `(x, y)` when `e` is `x * y`. -/
def mul? (e : Expr) : Option (Expr × Expr) :=
  let e := e.consumeMData
  if e.isAppOfArity ``HMul.hMul 6 then some (e.appFn!.appArg!, e.appArg!) else none

/-- A proof of `(x * y).PosSemidef` when the product is a Gram matrix `cᴴ * c`, `c * cᴴ` or a
congruence `cᴴ * a * c`, `c * a * cᴴ` (in either association) of a positive semidefinite `a`. -/
def psdMul (x y : Expr) : MetaM (Option Expr) := do
  if ← isConjTransposeOf x y then
    return some (← mkAppM ``Matrix.posSemidef_conjTranspose_mul_self #[y])
  if ← isConjTransposeOf y x then
    return some (← mkAppM ``Matrix.posSemidef_self_mul_conjTranspose #[x])
  if let some (c, a) := mul? x then
    if ← isConjTransposeOf c y then
      if let some ha ← psdOf a then
        return some (← mkAppM ``Matrix.PosSemidef.conjTranspose_mul_mul_same #[ha, y])
    if ← isConjTransposeOf y c then
      if let some ha ← psdOf a then
        return some (← mkAppM ``Matrix.PosSemidef.mul_mul_conjTranspose_same #[ha, c])
  if let some (a, c) := mul? y then
    if ← isConjTransposeOf x c then
      if let some ha ← psdOf a then
        return some (← mkAppM ``Matrix.PosSemidef.conjTranspose_mul_mul_same_assoc #[ha, c])
    if ← isConjTransposeOf c x then
      if let some ha ← psdOf a then
        return some (← mkAppM ``Matrix.PosSemidef.mul_mul_conjTranspose_same_assoc #[ha, x])
  return none

/-- The middle factors `a` of `e = x * y` read as a congruence `cᴴ * a * c` or `c * a * cᴴ`. -/
def congruenceMiddles (x y : Expr) : MetaM (List Expr) := do
  let mut r := []
  if let some (c, a) := mul? x then
    if (← isConjTransposeOf c y) || (← isConjTransposeOf y c) then r := r ++ [a]
  if let some (a, c) := mul? y then
    if (← isConjTransposeOf x c) || (← isConjTransposeOf c x) then r := r ++ [a]
  return r

/-- The `positivity` extension for products of matrices: Gram matrices `cᴴ * c`, `c * cᴴ` and
congruences `cᴴ * a * c`, `c * a * cᴴ` for rectangular `c`. -/
@[positivity _ * _]
def evalMatMul : PositivityExt where eval {_u α} zα pα? e :=
  match pα? with
  | none => pure .none
  | some pα => do
    let some _ ← matSquare? α | return .none
    let some (x, y) := mul? e | return .none
    let some h ← psdMul x y | return .none
    ofPSD zα pα e h

/-- The `positivity` extension for sums of matrices. -/
@[positivity _ + _]
def evalMatAdd : PositivityExt where eval {_u α} zα pα? e :=
  match pα? with
  | none => pure .none
  | some pα => do
    let some _ ← matSquare? α | return .none
    let e' := e.consumeMData
    unless e'.isAppOfArity ``HAdd.hAdd 6 do return .none
    let some ha ← psdOf e'.appFn!.appArg! | return .none
    let some hb ← psdOf e'.appArg! | return .none
    ofPSD zα pα e (← mkAppM ``Matrix.PosSemidef.add #[ha, hb])

/-- The `positivity` extension for nonnegative scalar multiples `r • a` of matrices. -/
@[positivity _ • _]
def evalMatSMul : PositivityExt where eval {_u α} zα pα? e :=
  match pα? with
  | none => pure .none
  | some pα => do
    let some _ ← matSquare? α | return .none
    let e' := e.consumeMData
    unless e'.isAppOfArity ``HSMul.hSMul 6 do return .none
    let some hr ← nonnegProof e'.appFn!.appArg! | return .none
    let some ha ← psdOf e'.appArg! | return .none
    ofPSD zα pα e (← mkAppM ``Matrix.PosSemidef.smul #[ha, hr])

/-- The `positivity` extension for finite sums `∑ i ∈ s, a i` of matrices. -/
@[positivity Finset.sum _ _]
def evalMatSum : PositivityExt where eval {_u α} zα pα? e :=
  match pα? with
  | none => pure .none
  | some pα => do
    let some _ ← matSquare? α | return .none
    let e' := e.consumeMData
    unless e'.isAppOfArity ``Finset.sum 5 do return .none
    let args := e'.getAppArgs
    let s := args[3]!
    let f := args[4]!
    let h? ← withLocalDeclD `i args[0]! fun i => do
      let mem ← mkAppOptM ``Membership.mem #[none, none, none, s, i]
      withLocalDeclD `hi mem fun hi => do
        let some h ← psdOf (f.beta #[i]) | return none
        return some (← mkLambdaFVars #[i, hi] h)
    let some h := h? | return .none
    ofPSD zα pα e (← mkAppM ``Matrix.posSemidef_sum #[s, h])

/-- The `positivity` extension for Kronecker products `a ⊗ₖ b`. -/
@[positivity Matrix.kroneckerMap _ _ _]
def evalKronecker : PositivityExt where eval {_u α} zα pα? e :=
  match pα? with
  | none => pure .none
  | some pα => do
    let some _ ← matSquare? α | return .none
    let e' := e.consumeMData
    unless e'.isAppOfArity ``Matrix.kroneckerMap 10 do return .none
    let some ha ← psdOf e'.appFn!.appArg! | return .none
    let some hb ← psdOf e'.appArg! | return .none
    ofPSD zα pα e (← mkAppM ``Matrix.PosSemidef.kronecker #[ha, hb])

/-- The `positivity` extension for compressions `a.submatrix f f`. -/
@[positivity Matrix.submatrix _ _ _]
def evalSubmatrix : PositivityExt where eval {_u α} zα pα? e :=
  match pα? with
  | none => pure .none
  | some pα => do
    let some _ ← matSquare? α | return .none
    let e' := e.consumeMData
    unless e'.isAppOfArity ``Matrix.submatrix 8 do return .none
    let args := e'.getAppArgs
    unless ← isSame args[6]! args[7]! do return .none
    let some ha ← psdOf args[5]! | return .none
    ofPSD zα pα e (← mkAppM ``Matrix.PosSemidef.submatrix #[ha, args[6]!])

/-- The `positivity` extension for reindexing `reindex f f a`. -/
@[positivity DFunLike.coe (Matrix.reindex _ _) _]
def evalReindex : PositivityExt where eval {_u α} zα pα? e :=
  match pα? with
  | none => pure .none
  | some pα => do
    let some _ ← matSquare? α | return .none
    let e' := e.consumeMData
    unless e'.isAppOfArity ``DFunLike.coe 6 do return .none
    let r := e'.appFn!.appArg!.consumeMData
    unless r.isAppOfArity ``Matrix.reindex 7 do return .none
    let rargs := r.getAppArgs
    unless ← isSame rargs[5]! rargs[6]! do return .none
    let some ha ← psdOf e'.appArg! | return .none
    ofPSD zα pα e (← mkAppM ``Matrix.PosSemidef.reindex #[ha, rargs[5]!])

/-- The `positivity` extension for diagonal matrices `diagonal d` with `0 ≤ d i`. -/
@[positivity Matrix.diagonal _]
def evalDiagonal : PositivityExt where eval {_u α} zα pα? e :=
  match pα? with
  | none => pure .none
  | some pα => do
    let some (n, _) ← matSquare? α | return .none
    let e' := e.consumeMData
    unless e'.isAppOfArity ``Matrix.diagonal 5 do return .none
    let d := e'.appArg!
    let h? ← withLocalDeclD `i n fun i => do
      let some h ← nonnegProof (d.beta #[i]) | return none
      return some (← mkLambdaFVars #[i] h)
    let some h := h? | return .none
    ofPSD zα pα e (← mkAppM ``Matrix.posSemidef_diagonal_of_forall_nonneg #[h])

/-- The `positivity` extension for the rank-one matrices `vecMulVec v (star v)` and
`vecMulVec (star v) v`. -/
@[positivity Matrix.vecMulVec _ _]
def evalVecMulVec : PositivityExt where eval {_u α} zα pα? e :=
  match pα? with
  | none => pure .none
  | some pα => do
    let some _ ← matSquare? α | return .none
    let e' := e.consumeMData
    unless e'.isAppOfArity ``Matrix.vecMulVec 6 do return .none
    let w := e'.appFn!.appArg!
    let v := e'.appArg!
    try
      ofPSD zα pα e (← mkAppM ``Matrix.posSemidef_vecMulVec_self_star #[w])
    catch _ =>
      ofPSD zα pα e (← mkAppM ``Matrix.posSemidef_vecMulVec_star_self #[v])

/-- The `positivity` extension for block diagonal matrices with positive semidefinite blocks. -/
@[positivity Matrix.blockDiagonal _]
def evalBlockDiagonal : PositivityExt where eval {_u α} zα pα? e :=
  match pα? with
  | none => pure .none
  | some pα => do
    let some _ ← matSquare? α | return .none
    let e' := e.consumeMData
    unless e'.isAppOfArity ``Matrix.blockDiagonal 7 do return .none
    let args := e'.getAppArgs
    let m := args[6]!
    let h? ← withLocalDeclD `k args[2]! fun k => do
      let some h ← psdOf (m.beta #[k]) | return none
      return some (← mkLambdaFVars #[k] h)
    let some h := h? | return .none
    ofPSD zα pα e (← mkAppM ``Matrix.PosSemidef.blockDiagonal #[h])

/-- Whether `e` is the numeral `k`. -/
def isNumeral (e : Expr) (k : Nat) : Bool :=
  let e := e.consumeMData
  e.isAppOfArity ``OfNat.ofNat 3 && e.appFn!.appArg!.rawNatLit? == some k

/-- A proof of `target` by the lemma `thm`: its conclusion is unified with `target`, its explicit
hypotheses are the proofs `hyps` in order and its instance arguments are synthesized. -/
def applyLemmaTo (target : Expr) (thm : Name) (hyps : List Expr) : MetaM Expr := do
  let c ← mkConstWithFreshMVarLevels thm
  let (xs, bis, ty) ← forallMetaTelescopeReducing (← inferType c)
  unless ← isDefEq ty target do throwError "{thm} does not prove{indentExpr target}"
  let mut hyps := hyps
  for y in xs, bi in bis do
    if bi.isExplicit then
      if let h :: rest := hyps then
        unless ← isDefEq y h do throwError "{thm}: hypothesis{indentExpr h}\ndoes not apply"
        hyps := rest
  for y in xs, bi in bis do
    if bi.isInstImplicit && !(← y.mvarId!.isAssigned) then
      y.mvarId!.assign (← synthInstance (← instantiateMVars (← inferType y)))
  let pf ← instantiateMVars (mkAppN c xs)
  if pf.hasExprMVar then throwError "{thm}: arguments not determined"
  return pf

/-- A proof of `x.PosSemidef` by the lemma `thm` without explicit arguments, whose conclusion is
unified with `x.PosSemidef` and whose instance arguments are synthesized. -/
def applyPSDLemma (x : Expr) (thm : Name) : MetaM Expr := do
  applyLemmaTo (← mkAppM ``Matrix.PosSemidef #[x]) thm []

/-- The `positivity` extension for matrix atoms: `0`, `1`, a hypothesis `a.PosSemidef`,
`a.PosDef`, `a ≤ b` for `b - a`, or `∀ xs, (a xs).PosSemidef`; and, at every type, a hypothesis
`∀ xs, 0 ≤ a xs`. -/
@[positivity _]
def evalMatrixAtom : PositivityExt where eval {_u α} zα pα? e :=
  match pα? with
  | none => pure .none
  | some pα => do
    if let some p ← forallHyp q(0 ≤ $e) ``LE.le then
      return ← nonnegOf zα pα e p
    let some _ ← matSquare? α | return .none
    if isNumeral e 0 then return ← ofPSD zα pα e (← applyPSDLemma e ``Matrix.PosSemidef.zero)
    if isNumeral e 1 then return ← ofPSD zα pα e (← applyPSDLemma e ``Matrix.PosSemidef.one)
    let some h ← psdHyp e | return .none
    ofPSD zα pα e h

/-- The subterm of `e` that no rule proves nonnegative: `e` itself when the rule for its head
constructor has all its premises, otherwise the first failing premise, searched recursively. -/
partial def blame (e : Expr) : MetaM MessageData := do
  let fails (c : Expr) : MetaM Bool := return (← nonnegProof c).isNone
  let descend (cs : List Expr) : MetaM MessageData := do
    for c in cs do
      if ← fails c then return ← blame c
    return m!"{e}"
  let under (dom : Expr) (body : Expr → MetaM Expr) : MetaM MessageData :=
    withLocalDeclD `i dom fun i => do
      let b ← body i
      if ← fails b then blame b else return m!"{e}"
  let e' := e.consumeMData
  let args := e'.getAppArgs
  if e'.isAppOfArity ``HAdd.hAdd 6 || e'.isAppOfArity ``HSMul.hSMul 6 then
    descend [args[4]!, args[5]!]
  else if e'.isAppOfArity ``HMul.hMul 6 then
    descend (← congruenceMiddles args[4]! args[5]!)
  else if e'.isAppOfArity ``Matrix.kroneckerMap 10 then
    descend [args[8]!, args[9]!]
  else if e'.isAppOfArity ``Matrix.submatrix 8 then
    descend [args[5]!]
  else if e'.isAppOfArity ``DFunLike.coe 6 then
    descend [args[5]!]
  else if e'.isAppOfArity ``Finset.sum 5 then
    under args[0]! fun i => pure (args[4]!.beta #[i])
  else if e'.isAppOfArity ``Matrix.diagonal 5 then
    under (← inferType args[4]!).bindingDomain! fun i => pure (args[4]!.beta #[i])
  else if e'.isAppOfArity ``Matrix.blockDiagonal 7 then
    under args[2]! fun k => pure (args[6]!.beta #[k])
  else
    return m!"{e}"

/-- The error of `psd` when no rule proves `0 ≤ x`. -/
def failure {β : Type} (x : Expr) (report : Bool) : MetaM β := do
  if report then
    throwError "psd? failed: no rule of the positive cone proves `0 ≤ _` for the subterm{
      indentD (← blame x)}\nof{indentExpr x}"
  else
    throwError "psd failed to prove{indentExpr x}\npositive semidefinite; `psd?` names the \
      subterm outside the grammar"

/-- A proof of the goal `t`, of the form `0 ≤ x`, `x.PosSemidef` or `a ≤ b`. -/
def prove (t : Expr) (report : Bool) : MetaM Expr := do
  let t := (← instantiateMVars t).consumeMData
  if t.isAppOfArity ``LE.le 4 then
    let a := t.appFn!.appArg!
    let b := t.appArg!
    if isNumeral a 0 || a.consumeMData.isAppOf ``Zero.zero then
      let some p ← nonnegProof b | failure b report
      unless ← isDefEq (← inferType p) t do failure b report
      return p
    let bc := b.consumeMData
    if bc.isAppOfArity ``HAdd.hAdd 6 then
      if ← isSame bc.appFn!.appArg! a then
        if let some p ← nonnegProof bc.appArg! then
          return ← applyLemmaTo t ``le_add_of_nonneg_right [p]
      if ← isSame bc.appArg! a then
        if let some p ← nonnegProof bc.appFn!.appArg! then
          return ← applyLemmaTo t ``le_add_of_nonneg_left [p]
    let d ← mkAppM ``HSub.hSub #[b, a]
    if (← matSquare? (← inferType b)).isSome then
      let some h ← psdOf d | failure d report
      unless ← isDefEq (← inferType h) t do failure d report
      return ← mkExpectedTypeHint h t
    let some p ← nonnegProof d | failure d report
    return ← mkAppM ``le_of_sub_nonneg #[p]
  if t.isAppOf ``Matrix.PosSemidef then
    let x := t.appArg!
    let some h ← psdOf x | failure x report
    return h
  throwError "psd: the goal is not `0 ≤ x`, `x.PosSemidef` or `a ≤ b`:{indentExpr t}"

/-- The procedure shared by `psd` and `psd?`. -/
def run (report : Bool) : TacticM Unit := liftMetaFinishingTactic fun g => do
  let p ← prove (← g.getType) report
  g.assign p
  if report then logInfo "psd? closes the goal; `psd` does the same"

/-- `psd_core` is the procedure of `psd` without the scopes `MatrixOrder` and `ComplexOrder`. -/
syntax (name := psdCore) "psd_core" : tactic

/-- `psd_core?` is the procedure of `psd?` without the scopes `MatrixOrder` and
`ComplexOrder`. -/
syntax (name := psdCoreQ) "psd_core?" : tactic

elab_rules : tactic
  | `(tactic| psd_core) => run false
  | `(tactic| psd_core?) => run true

/-- `psd` proves `0 ≤ X`, `X.PosSemidef` and the Loewner inequality `A ≤ B` for matrices over an
`RCLike` field, and `0 ≤ x` and `a ≤ b` in any star-ordered ring, when `X` (or `B - A`) is built
from atoms with a hypothesis `0 ≤ a`, `a.PosSemidef`, `IsStarProjection a` or `a ≤ b` by star
squares, Gram matrices `cᴴ * c`, congruences `cᴴ * a * c`, sums, finite sums, nonnegative
scalars, `⊗ₖ`, `submatrix e e`, `reindex e e`, `diagonal`, `blockDiagonal`,
`vecMulVec v (star v)`, `0`, `1`, `CFC.sqrt`, `cfc f` with `f ≥ 0` and `1 - p`. It opens the
scopes `MatrixOrder` and `ComplexOrder` and runs the `positivity` extensions of this file and of
`PositivityStar`. -/
macro (name := psd) "psd" : tactic =>
  `(tactic| open scoped $(Lean.mkIdent `MatrixOrder) $(Lean.mkIdent `ComplexOrder) in psd_core)

/-- `psd?` runs `psd`; when it fails it names the subterm that no rule proves nonnegative. -/
macro (name := psdQ) "psd?" : tactic =>
  `(tactic| open scoped $(Lean.mkIdent `MatrixOrder) $(Lean.mkIdent `ComplexOrder) in psd_core?)

end CatCryptCore.Tactic.PositivityMatrix

end
