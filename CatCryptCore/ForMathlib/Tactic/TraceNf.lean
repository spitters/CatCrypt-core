/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.Tactic.Ring.RingNF
public import CatCryptCore.ForMathlib.Matrix.ProjectorRewinding
public import CatCryptCore.ForMathlib.Tactic.TraceNfAttr
public meta import Lean.Elab.Tactic

/-!
# The `trace_nf` tactic: traces of matrix words up to rotation

`trace_nf` normalises traces of polynomials in matrices. A trace of a product is a trace of a
word in its atoms; two words have equal traces in all dimensions when they are rotations of each
other (cyclic equivalence), and the necklaces (words up to rotation) are a basis of the free
algebra modulo commutators (Klep–Schweighofer 2008). The tactic

1. distributes `Matrix.trace` over sums, differences, negations, scalar multiples and finite
   sums, and matrix products over sums;
2. rewrites each `Matrix.trace w` with `w` a product to the trace of the least rotation of the
   right-associated word of `w` in the order `Lean.Expr.lt` on atoms (simproc `traceNecklace`,
   proved by `Matrix.mul_assoc` and `Matrix.trace_mul_comm`); rectangular factors are allowed,
   since every rotation of a closed word is well typed;
3. rewrites `re (trace w)` (`RCLike.re` or `Complex.re`), when every atom of `w` is Hermitian by a
   hypothesis `Matrix.IsHermitian A` of the local context, to the least of the rotations of `w`
   and of its reversal (simprocs `traceReverseRCLikeRe`, `traceReverseComplexRe`), since
   `re (trace w) = re (trace wᴴ)`;
4. rewrites the vector forms `star x ⬝ᵥ (M *ᵥ y)`, `(x ᵥ* M) ⬝ᵥ y` and `‖WithLp.toLp 2 v‖ ^ 2` to
   `star x ⬝ᵥ (W *ᵥ y)` with `W` a right-associated product;
5. closes or normalises the remaining scalar equation with `ring_nf`.
-/

set_option autoImplicit false

public section

namespace Matrix

variable {n : Type*} [Fintype n]

/-- The real part of a trace is invariant under the conjugate transpose. -/
theorem re_trace_conjTranspose {𝕜 : Type*} [RCLike 𝕜] (A : Matrix n n 𝕜) :
    RCLike.re Aᴴ.trace = RCLike.re A.trace := by
  rw [Matrix.trace_conjTranspose, RCLike.star_def, RCLike.conj_re]

/-- Two matrices related by the conjugate transpose have traces with equal real parts. -/
theorem re_trace_eq_of_conjTranspose_eq {𝕜 : Type*} [RCLike 𝕜] {A B : Matrix n n 𝕜}
    (h : Aᴴ = B) : RCLike.re A.trace = RCLike.re B.trace := by
  rw [← h, re_trace_conjTranspose]

/-- Two complex matrices related by the conjugate transpose have traces with equal real
parts. -/
theorem complex_re_trace_eq_of_conjTranspose_eq {A B : Matrix n n ℂ} (h : Aᴴ = B) :
    A.trace.re = B.trace.re := by
  rw [← h, Matrix.trace_conjTranspose, Complex.star_def, Complex.conj_re]

end Matrix

attribute [trace_nf] Matrix.trace_add Matrix.trace_sub Matrix.trace_neg Matrix.trace_smul
  Matrix.trace_sum Matrix.trace_zero smul_eq_mul Matrix.mul_add Matrix.add_mul Matrix.mul_sub
  Matrix.sub_mul Matrix.mul_neg Matrix.neg_mul Matrix.smul_mul Matrix.mul_smul Matrix.mul_zero
  Matrix.zero_mul Matrix.sum_mul Matrix.mul_sum

attribute [inner_nf] Matrix.star_mulVec Matrix.mulVec_mulVec Matrix.vecMul_vecMul
  Matrix.conjTranspose_mul Matrix.conjTranspose_conjTranspose Matrix.mul_assoc
  Matrix.norm_toLp_sq_eq_re_star_dotProduct

attribute [inner_nf ←] Matrix.dotProduct_mulVec

end

public meta section

namespace CatCryptCore.Tactic.TraceNf

open Lean Meta

/-- Whether `e` has a type `Matrix m n α`. -/
def isMatrix (e : Expr) : MetaM Bool := do
  return (← instantiateMVars (← whnfR (← inferType e))).isAppOfArity ``Matrix 3

/-- The multiplication head and the two factors of a matrix product `a * b`. -/
def mulArgs? (e : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  match e.getAppFnArgs with
  | (``HMul.hMul, #[_, _, _, _, a, b]) =>
    if (← isMatrix e) then return some (e.appFn!.appFn!, a, b) else return none
  | _ => return none

/-- The matrix product `a * b`. -/
def mkMul (a b : Expr) : MetaM Expr := mkAppM ``HMul.hMul #[a, b]

/-- For right-associated `x` and `y`, the right-associated form `r` of `x * y` and a proof of
`x * y = r`. -/
partial def append (x y : Expr) : MetaM (Expr × Expr) := do
  match ← mulArgs? x with
  | some (_, x1, x2) =>
    let (r, p) ← append x2 y
    let h1 ← mkAppM ``Matrix.mul_assoc #[x1, x2, y]
    let f ← withLocalDeclD `z (← inferType r) fun z => do mkLambdaFVars #[z] (← mkMul x1 z)
    let h2 ← mkCongrArg f p
    return (← mkMul x1 r, ← mkEqTrans h1 h2)
  | none =>
    let r ← mkMul x y
    return (r, ← mkEqRefl r)

/-- The right-associated form `r` of a product `e` and a proof of `e = r`. -/
partial def rassoc (e : Expr) : MetaM (Expr × Expr) := do
  match ← mulArgs? e with
  | some (f, a, b) =>
    let (a', pa) ← rassoc a
    let (b', pb) ← rassoc b
    let (r, pr) ← append a' b'
    let p1 ← mkCongr (← mkCongrArg f pa) pb
    return (r, ← mkEqTrans p1 pr)
  | none => return (e, ← mkEqRefl e)

/-- The atoms of a product, from left to right. -/
partial def atoms (e : Expr) : MetaM (List Expr) := do
  match ← mulArgs? e with
  | some (_, a, b) => return (← atoms a) ++ (← atoms b)
  | none => return [e]

/-- The right-associated product of a nonempty list of atoms. -/
def build : List Expr → MetaM Expr
  | [] => throwError "trace_nf: empty word"
  | [a] => pure a
  | a :: as => do mkMul a (← build as)

/-- The lexicographic order on words induced by `Lean.Expr.lt` on atoms. -/
def lexLt : List Expr → List Expr → Bool
  | [], [] => false
  | [], _ => true
  | _, [] => false
  | a :: as, b :: bs => if a == b then lexLt as bs else a.lt b

/-- The rotation of `xs` by `r` places. -/
def rotate (xs : List Expr) (r : Nat) : List Expr := xs.drop r ++ xs.take r

/-- The first index of a least rotation of `xs`. -/
def leastRotation (xs : List Expr) : Nat := Id.run do
  let mut best := 0
  for r in [1:xs.length] do
    if lexLt (rotate xs r) (rotate xs best) then best := r
  return best

/-- For a right-associated product `nf` with atoms `xs`, the right-associated rotation `t` of
`nf` by `r` places and a proof of `trace nf = trace t`. -/
def rotateTrace (nf : Expr) (xs : List Expr) (r : Nat) : MetaM (Expr × Expr) := do
  if r == 0 then return (nf, ← mkEqRefl (← mkAppM ``Matrix.trace #[nf]))
  let L ← build (xs.take r)
  let R ← build (xs.drop r)
  let (lr, pLR) ← append L R
  let (t, pRL) ← append R L
  let pc ← mkAppM ``Matrix.trace_mul_comm #[L, R]
  let trLR := (← mkAppM ``Matrix.trace #[lr]).appFn!
  let trRL := (← mkAppM ``Matrix.trace #[t]).appFn!
  let p ← mkEqTrans (← mkEqTrans (← mkCongrArg trLR (← mkEqSymm pLR)) pc)
    (← mkCongrArg trRL pRL)
  return (t, p)

/-- The simproc `traceNecklace`: `trace w` for a product `w` to the trace of the least rotation
of the right-associated word of `w`. -/
def necklaceProc (e : Expr) : Simp.SimpM Simp.Step := do
  let_expr Matrix.trace _ _ _ _ m := e | return .continue
  let some _ ← mulArgs? m | return .continue
  try
    let tr := e.appFn!
    let (nf, pnf) ← rassoc m
    let xs ← atoms nf
    let r := leastRotation xs
    if r == 0 && nf == m then return .continue
    let (t, pt) ← rotateTrace nf xs r
    let p ← mkEqTrans (← mkCongrArg tr pnf) pt
    return .visit { expr := ← mkAppM ``Matrix.trace #[t], proof? := p }
  catch _ => return .continue

/-- A proof of `Aᴴ = A` from a hypothesis `Matrix.IsHermitian A` of the local context. -/
def hermitian? (a : Expr) : MetaM (Option Expr) := do
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ty ← instantiateMVars d.type
    if ty.isAppOf ``Matrix.IsHermitian && ty.appArg! == a then
      return some (← mkAppM ``Matrix.IsHermitian.eq #[d.toExpr])
  return none

/-- For a right-associated product `w` of Hermitian atoms, the right-associated reversal `r` of
`w` and a proof of `wᴴ = r`. -/
partial def adjRev (w : Expr) : MetaM (Expr × Expr) := do
  match ← mulArgs? w with
  | some (_, a, rest) =>
    let some pa ← hermitian? a | throwError "trace_nf: atom not Hermitian"
    let (r', pr) ← adjRev rest
    let h1 ← mkAppM ``Matrix.conjTranspose_mul #[a, rest]
    let some (_, rhs) := (← inferType h1).eq?.map (fun (_, l, r) => (l, r))
      | throwError "trace_nf: conjTranspose_mul"
    let some (f, _, _) ← mulArgs? rhs | throwError "trace_nf: conjTranspose_mul"
    let h2 ← mkCongr (← mkCongrArg f pr) pa
    let (r, p3) ← append r' a
    return (r, ← mkEqTrans (← mkEqTrans h1 h2) p3)
  | none =>
    let some pa ← hermitian? w | throwError "trace_nf: atom not Hermitian"
    return (w, pa)

/-- The simprocs `traceReverseRCLikeRe` and `traceReverseComplexRe`: `re (trace w)`, for a
product `w` of atoms Hermitian by local hypotheses, to `re (trace t)` with `t` the least of the
rotations of `w` and of its reversal. `lem` is `Matrix.re_trace_eq_of_conjTranspose_eq` or
`Matrix.complex_re_trace_eq_of_conjTranspose_eq`. -/
def reverseProc (lem : Name) (e : Expr) : Simp.SimpM Simp.Step := do
  let tre := e.appArg!
  let_expr Matrix.trace _ _ _ _ m := tre | return .continue
  let some _ ← mulArgs? m | return .continue
  try
    let re := e.appFn!
    let tr := tre.appFn!
    let (nf, pnf) ← rassoc m
    let xs ← atoms nf
    let (rv, prv) ← adjRev nf
    let ys ← atoms rv
    let rx := leastRotation xs
    let ry := leastRotation ys
    unless lexLt (rotate ys ry) (rotate xs rx) do return .continue
    let (t, pt) ← rotateTrace rv ys ry
    let p1 ← mkCongrArg re (← mkCongrArg tr pnf)
    let p2 ← mkAppM lem #[prv]
    let p3 ← mkCongrArg re pt
    let p ← mkEqTrans (← mkEqTrans p1 p2) p3
    return .visit { expr := mkApp re (← mkAppM ``Matrix.trace #[t]), proof? := p }
  catch _ => return .continue

end CatCryptCore.Tactic.TraceNf

open CatCryptCore.Tactic.TraceNf

/-- `trace w` for a matrix product `w` to the trace of the least rotation (in the order
`Lean.Expr.lt` on atoms) of the right-associated word of `w`. -/
simproc_decl traceNecklace (Matrix.trace _) := necklaceProc

/-- `RCLike.re (trace w)` for a product `w` of atoms Hermitian by local hypotheses to the least
of the rotations of `w` and of its reversal. -/
simproc_decl traceReverseRCLikeRe (RCLike.re (Matrix.trace _)) :=
  reverseProc ``Matrix.re_trace_eq_of_conjTranspose_eq

/-- `Complex.re (trace w)` for a product `w` of complex atoms Hermitian by local hypotheses to the
least of the rotations of `w` and of its reversal. -/
simproc_decl traceReverseComplexRe (Complex.re (Matrix.trace _)) :=
  reverseProc ``Matrix.complex_re_trace_eq_of_conjTranspose_eq

end

/-- `trace_nf` normalises traces of matrix polynomials to combinations of traces of words in least
rotation, real parts of traces of Hermitian words also up to reversal, and the vector forms
`star x ⬝ᵥ (M *ᵥ y)` and `‖WithLp.toLp 2 v‖ ^ 2` to `star x ⬝ᵥ (W *ᵥ y)` with `W`
right-associated; it ends with `ring_nf`. -/
syntax (name := traceNf) "trace_nf" (Lean.Parser.Tactic.location)? : tactic

macro_rules
  | `(tactic| trace_nf $[$loc]?) => `(tactic|
      (simp only [trace_nf, inner_nf, traceNecklace, traceReverseRCLikeRe,
          traceReverseComplexRe] $[$loc]?
       try ring_nf $[$loc]?))
