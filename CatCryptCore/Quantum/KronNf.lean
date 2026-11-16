/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.KronNfAttr
public import CatCryptCore.Quantum.PartialTrace
public import CatCryptCore.ForMathlib.Matrix.KroneckerReindex
public meta import Lean.Elab.Tactic

/-!
# Kronecker normal form: `kron_nf`, `kron_index`, `kron_ext`

The rewrite system of the simp set `kron_nf` moves products, adjoints, scalars, sums, traces and
partial traces through Kronecker products, for Mathlib's type-indexed `⊗ₖ` on
`Matrix (m × n)`, for its reindexing along `finProdFinEquiv`, and for the product
`CatCrypt.Quantum.TensorProduct.kronecker` on `Matrix (Fin (d₁ * d₂))`. The oriented rules
`(A ⊗ B) (C ⊗ D) → AC ⊗ BD`, `(A ⊗ B)ᴴ → Aᴴ ⊗ Bᴴ`, `(c A) ⊗ B → c (A ⊗ B)`,
`A ⊗ (c B) → c (A ⊗ B)`, `(A + A') ⊗ B → A ⊗ B + A' ⊗ B` (both sides, and for finite sums),
`1 ⊗ 1 → 1`, `0 ⊗ B → 0`, `tr (A ⊗ B) → tr A · tr B`, `tr₂ (A ⊗ B) → tr B • A`,
`tr₁ (A ⊗ B) → tr A • B` decrease the number of products above a `⊗` node. Normal forms are sums
of scalar multiples of single Kronecker products.

## Tactics

* `kron_nf`: `kron_index`, then `simp only` with the set `kron_nf` and the ring laws of matrices
  (unit, zero, distributivity, scalars, left-associated products) and the additivity of `ᴴ`,
  `trace` and linear maps.
* `kron_index`: in the goal, replaces each type index `Fin k` by `Fin (d₁ * d₂)` when
  `Fin (d₁ * d₂)`, a Kronecker product at `d₁, d₂` or `finProdEquiv d₁ d₂` occurs in the goal and
  `k` and `d₁ * d₂` are definitionally equal (`4`, `2 ^ 2`, `2 * 2`), and closes the change by
  definitional equality. Lemmas whose index is `Fin (?d₁ * ?d₂)` then apply by `apply` and
  `refine`, which do not unify `4` with `?d₁ * ?d₂`.
* `kron_ext [i₁ i₂ j₁ j₂]`: reduces an equation of matrices indexed by `Fin (d₁ * d₂)` to the
  entries at the points `finProdEquiv (i₁, i₂)`, `finProdEquiv (j₁, j₂)` and evaluates Kronecker
  products there; `kron_ext at h` gives the entry equations of a hypothesis `h : M = N`.

## Main results

* `TensorProduct.kronecker_eq_reindex`: the `Fin` product is the reindexed `⊗ₖ`
* `TensorProduct.kronecker_apply_finProdEquiv`: entries at product points
* `TensorProduct.kronecker_mulVec_kronVec`: the action on product vectors
* `Matrix.finset_sum_kronecker`, `Matrix.kronecker_finset_sum`: finite sums for `⊗ₖ`
-/

@[expose] public section

set_option autoImplicit false

open Matrix

namespace Matrix

variable {ι R l m n p : Type*}

/-- The Kronecker product distributes over a finite sum on the left. -/
theorem finset_sum_kronecker [NonUnitalNonAssocSemiring R] (s : Finset ι)
    (A : ι → Matrix l m R) (B : Matrix n p R) :
    kroneckerMap (· * ·) (∑ i ∈ s, A i) B = ∑ i ∈ s, kroneckerMap (· * ·) (A i) B := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp [kroneckerMap_apply, Matrix.sum_apply, Finset.sum_mul]

/-- The Kronecker product distributes over a finite sum on the right. -/
theorem kronecker_finset_sum [NonUnitalNonAssocSemiring R] (s : Finset ι)
    (A : Matrix l m R) (B : ι → Matrix n p R) :
    kroneckerMap (· * ·) A (∑ i ∈ s, B i) = ∑ i ∈ s, kroneckerMap (· * ·) A (B i) := by
  ext ⟨a, b⟩ ⟨c, d⟩
  simp [kroneckerMap_apply, Matrix.sum_apply, Finset.mul_sum]

end Matrix

namespace CatCrypt.Quantum.TensorProduct

variable {d₁ d₂ e₁ e₂ : ℕ}

/-- The Kronecker product on `Fin (d₁ * d₂)` is Mathlib's `⊗ₖ` reindexed along
`finProdFinEquiv`. -/
theorem kronecker_eq_reindex (A : Matrix (Fin d₁) (Fin d₁) ℂ) (B : Matrix (Fin d₂) (Fin d₂) ℂ) :
    kronecker A B = reindex finProdFinEquiv finProdFinEquiv (kroneckerMap (· * ·) A B) := by
  ext i j
  rw [reindex_kronecker_apply_symm, kronecker_apply]
  rfl

/-- Entry of the Kronecker product at the images of two index pairs. -/
theorem kronecker_apply_finProdEquiv (A : Matrix (Fin d₁) (Fin d₁) ℂ)
    (B : Matrix (Fin d₂) (Fin d₂) ℂ) (i₁ j₁ : Fin d₁) (i₂ j₂ : Fin d₂) :
    kronecker A B (finProdEquiv d₁ d₂ (i₁, i₂)) (finProdEquiv d₁ d₂ (j₁, j₂)) =
      A i₁ j₁ * B i₂ j₂ := by
  simp [kronecker_apply]

/-- Entry of the identity at the images of two index pairs. -/
theorem one_apply_finProdEquiv (i₁ j₁ : Fin d₁) (i₂ j₂ : Fin d₂) :
    (1 : Matrix (Fin (d₁ * d₂)) (Fin (d₁ * d₂)) ℂ) (finProdEquiv d₁ d₂ (i₁, i₂))
        (finProdEquiv d₁ d₂ (j₁, j₂)) =
      (1 : Matrix (Fin d₁) (Fin d₁) ℂ) i₁ j₁ * (1 : Matrix (Fin d₂) (Fin d₂) ℂ) i₂ j₂ := by
  rw [← kronecker_one_one, kronecker_apply_finProdEquiv]

/-- The Kronecker product is additive in its second argument. -/
theorem kronecker_add_right (A : Matrix (Fin d₁) (Fin d₁) ℂ)
    (B C : Matrix (Fin d₂) (Fin d₂) ℂ) :
    kronecker A (B + C) = kronecker A B + kronecker A C := by
  ext i j
  simp [kronecker_apply, mul_add]

/-- The Kronecker product is subtractive in its second argument. -/
theorem kronecker_sub_right (A : Matrix (Fin d₁) (Fin d₁) ℂ)
    (B C : Matrix (Fin d₂) (Fin d₂) ℂ) :
    kronecker A (B - C) = kronecker A B - kronecker A C := by
  ext i j
  simp [kronecker_apply, mul_sub]

/-- A negation in the first argument moves out of the Kronecker product. -/
theorem kronecker_neg_left (A : Matrix (Fin d₁) (Fin d₁) ℂ) (B : Matrix (Fin d₂) (Fin d₂) ℂ) :
    kronecker (-A) B = -kronecker A B := by
  ext i j
  simp [kronecker_apply]

/-- A negation in the second argument moves out of the Kronecker product. -/
theorem kronecker_neg_right (A : Matrix (Fin d₁) (Fin d₁) ℂ) (B : Matrix (Fin d₂) (Fin d₂) ℂ) :
    kronecker A (-B) = -kronecker A B := by
  ext i j
  simp [kronecker_apply]

/-- A scalar in the first argument moves out of the Kronecker product. -/
theorem kronecker_smul_left (c : ℂ) (A : Matrix (Fin d₁) (Fin d₁) ℂ)
    (B : Matrix (Fin d₂) (Fin d₂) ℂ) : kronecker (c • A) B = c • kronecker A B := by
  ext i j
  simp [kronecker_apply, mul_assoc]

/-- A scalar in the second argument moves out of the Kronecker product. -/
theorem kronecker_smul_right (c : ℂ) (A : Matrix (Fin d₁) (Fin d₁) ℂ)
    (B : Matrix (Fin d₂) (Fin d₂) ℂ) : kronecker A (c • B) = c • kronecker A B := by
  ext i j
  simp only [kronecker_apply, Matrix.smul_apply, smul_eq_mul]
  ring

/-- The Kronecker product with the zero matrix on the left is zero. -/
theorem kronecker_zero_left (B : Matrix (Fin d₂) (Fin d₂) ℂ) :
    kronecker (0 : Matrix (Fin d₁) (Fin d₁) ℂ) B = 0 := by
  ext i j
  simp [kronecker_apply]

/-- The Kronecker product with the zero matrix on the right is zero. -/
theorem kronecker_zero_right (A : Matrix (Fin d₁) (Fin d₁) ℂ) :
    kronecker A (0 : Matrix (Fin d₂) (Fin d₂) ℂ) = 0 := by
  ext i j
  simp [kronecker_apply]

/-- The Kronecker product distributes over a finite sum on the left. -/
theorem finset_sum_kronecker {ι : Type*} (s : Finset ι) (A : ι → Matrix (Fin d₁) (Fin d₁) ℂ)
    (B : Matrix (Fin d₂) (Fin d₂) ℂ) :
    kronecker (∑ i ∈ s, A i) B = ∑ i ∈ s, kronecker (A i) B := by
  ext p q
  simp only [kronecker_apply, Matrix.sum_apply, Finset.sum_mul]

/-- The Kronecker product distributes over a finite sum on the right. -/
theorem kronecker_finset_sum {ι : Type*} (s : Finset ι) (A : Matrix (Fin d₁) (Fin d₁) ℂ)
    (B : ι → Matrix (Fin d₂) (Fin d₂) ℂ) :
    kronecker A (∑ i ∈ s, B i) = ∑ i ∈ s, kronecker A (B i) := by
  ext p q
  simp only [kronecker_apply, Matrix.sum_apply, Finset.mul_sum]

/-- Kronecker product of vectors on `Fin (d₁ * d₂)`:
`(kronVec u v) (finProdEquiv (i₁, i₂)) = u i₁ * v i₂`. -/
noncomputable def kronVec (u : Fin d₁ → ℂ) (v : Fin d₂ → ℂ) : Fin (d₁ * d₂) → ℂ :=
  fun i => u ((finProdEquiv d₁ d₂).symm i).1 * v ((finProdEquiv d₁ d₂).symm i).2

/-- Entry of the Kronecker product of vectors at the image of an index pair. -/
theorem kronVec_apply_finProdEquiv (u : Fin d₁ → ℂ) (v : Fin d₂ → ℂ) (i₁ : Fin d₁)
    (i₂ : Fin d₂) : kronVec u v (finProdEquiv d₁ d₂ (i₁, i₂)) = u i₁ * v i₂ := by
  simp [kronVec]

/-- A Kronecker product of matrices acts factorwise on a Kronecker product of vectors. -/
theorem kronecker_mulVec_kronVec (A : Matrix (Fin d₁) (Fin d₁) ℂ)
    (B : Matrix (Fin d₂) (Fin d₂) ℂ) (u : Fin d₁ → ℂ) (v : Fin d₂ → ℂ) :
    kronecker A B *ᵥ kronVec u v = kronVec (A *ᵥ u) (B *ᵥ v) := by
  ext i
  obtain ⟨⟨i₁, i₂⟩, rfl⟩ := (finProdEquiv d₁ d₂).surjective i
  simp only [mulVec, dotProduct, kronVec_apply_finProdEquiv]
  rw [← (finProdEquiv d₁ d₂).sum_comp, Fintype.sum_prod_type, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun j₁ _ => Finset.sum_congr rfl fun j₂ _ => ?_
  rw [kronecker_apply_finProdEquiv, kronVec_apply_finProdEquiv]
  ring

/-- Two matrices indexed by `Fin (d₁ * d₂)` and `Fin (e₁ * e₂)` are equal when their entries at
the images of index pairs are equal. -/
theorem eq_of_kronecker_entries {R : Type*} {M N : Matrix (Fin (d₁ * d₂)) (Fin (e₁ * e₂)) R}
    (h : ∀ i₁ i₂ j₁ j₂, M (finProdEquiv d₁ d₂ (i₁, i₂)) (finProdEquiv e₁ e₂ (j₁, j₂)) =
      N (finProdEquiv d₁ d₂ (i₁, i₂)) (finProdEquiv e₁ e₂ (j₁, j₂))) :
    M = N := by
  ext i j
  obtain ⟨⟨i₁, i₂⟩, rfl⟩ := (finProdEquiv d₁ d₂).surjective i
  obtain ⟨⟨j₁, j₂⟩, rfl⟩ := (finProdEquiv e₁ e₂).surjective j
  exact h i₁ i₂ j₁ j₂

/-- The entry equations at the images of index pairs of an equation of matrices indexed by
`Fin (d₁ * d₂)` and `Fin (e₁ * e₂)`. -/
theorem kronecker_entries_of_eq {R : Type*} {M N : Matrix (Fin (d₁ * d₂)) (Fin (e₁ * e₂)) R}
    (h : M = N) (i₁ : Fin d₁) (i₂ : Fin d₂) (j₁ : Fin e₁) (j₂ : Fin e₂) :
    M (finProdEquiv d₁ d₂ (i₁, i₂)) (finProdEquiv e₁ e₂ (j₁, j₂)) =
      N (finProdEquiv d₁ d₂ (i₁, i₂)) (finProdEquiv e₁ e₂ (j₁, j₂)) := by
  rw [h]

end CatCrypt.Quantum.TensorProduct

end

public meta section

namespace CatCryptCore.Tactic.KronIndex

open Lean Meta Elab Tactic

/-- The products `a * b` of `e`'s occurrences of `Fin (a * b)`, of `TensorProduct.kronecker` at
`a` and `b`, and of `finProdEquiv a b`, without repetition, accumulated onto `acc`. -/
partial def productIndices (e : Expr) (acc : Array Expr := #[]) : Array Expr :=
  let push (acc : Array Expr) (p : Expr) : Array Expr :=
    if acc.contains p then acc else acc.push p
  match e with
  | .app f a =>
    let acc := if f.isConstOf ``Fin && a.isAppOfArity ``HMul.hMul 6 then push acc a else acc
    let acc :=
      if e.isAppOf ``CatCrypt.Quantum.TensorProduct.kronecker ||
          e.isAppOf ``CatCrypt.Quantum.TensorProduct.finProdEquiv then
        let args := e.getAppArgs
        if h : 2 ≤ args.size then push acc (mkNatMul args[0] args[1]) else acc
      else acc
    productIndices a (productIndices f acc)
  | .lam _ t b _ | .forallE _ t b _ => productIndices b (productIndices t acc)
  | .letE _ t v b _ => productIndices b (productIndices v (productIndices t acc))
  | .mdata _ b | .proj _ _ b => productIndices b acc
  | _ => acc

/-- Replaces each `Fin k` in `e` by `Fin p` for the first `p` of `ps` with `k` and `p`
definitionally equal at default transparency and `k` not syntactically a product. -/
def reindexFin (ps : Array Expr) (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun x => do
    if let .app f k := x then
      if f.isConstOf ``Fin && !k.isAppOfArity ``HMul.hMul 6 && !k.hasLooseBVars then
        for p in ps do
          if ← withDefault (withNewMCtxDepth (isDefEq k p)) then
            return .done (mkApp f p)
    return .continue)

/-- `kron_index` replaces the type index `Fin k` of every term in the goal by `Fin (d₁ * d₂)`
when `Fin (d₁ * d₂)` occurs in the goal and `k` is definitionally equal to `d₁ * d₂` (`4`,
`2 ^ 2`, `2 * 2`), and checks the change by definitional equality. It succeeds without change
when no index is replaced. -/
elab "kron_index" : tactic => withMainContext do
  let g ← getMainGoal
  let t ← instantiateMVars (← g.getType)
  let ps := productIndices t
  if ps.isEmpty then return
  let t' ← reindexFin ps t
  if t' == t then return
  unless ← withDefault (isDefEq t t') do
    throwError "kron_index: the reindexed goal is not definitionally equal to the goal"
  replaceMainGoal [← g.replaceTargetDefEq t']

/-- The factors `a`, `b` of an index type `Fin (a * b)`. -/
def finProdFactors? (m : Expr) : Option (Expr × Expr) :=
  if m.isAppOfArity ``Fin 1 then
    let k := m.appArg!
    if k.isAppOfArity ``HMul.hMul 6 then some (k.getArg! 4, k.getArg! 5) else none
  else none

/-- The arguments `#[a, b, c, e, R, M, N]` of an equation `M = N` between matrices over `R`
indexed by `Fin (a * b)` and `Fin (c * e)`. -/
def matrixEqArgs (t : Expr) : MetaM (Array (Option Expr)) := do
  let some (ty, M, N) := t.eq? | throwError "kron_ext: {t} is not an equation"
  let ty ← instantiateMVars ty
  if ty.isAppOfArity ``Matrix 3 then
    if let (some (a, b), some (c, e)) :=
        (finProdFactors? (ty.getArg! 0), finProdFactors? (ty.getArg! 1)) then
      return #[a, b, c, e, ty.getArg! 2, M, N]
  throwError "kron_ext: {ty} is not a type of matrices indexed by `Fin (_ * _)`"

/-- `kron_ext_apply` applies `TensorProduct.eq_of_kronecker_entries` to a goal `M = N` between
matrices indexed by `Fin (a * b)` and `Fin (c * e)`, with the factors read from the goal. -/
elab "kron_ext_apply" : tactic => withMainContext do
  let g ← getMainGoal
  let args ← matrixEqArgs (← instantiateMVars (← g.getType))
  let lem ← mkAppOptM ``CatCrypt.Quantum.TensorProduct.eq_of_kronecker_entries args
  replaceMainGoal (← g.apply lem)

/-- `kron_ext_hyp h` replaces `h : M = N` between matrices indexed by `Fin (a * b)` and
`Fin (c * e)` (after the reindexing of `kron_index`) by its entry equations
`TensorProduct.kronecker_entries_of_eq h`. -/
elab "kron_ext_hyp " h:ident : tactic => withMainContext do
  let g ← getMainGoal
  let fv ← getFVarId h
  let t ← instantiateMVars (← fv.getType)
  let ps := productIndices t
  let t' ← if ps.isEmpty then pure t else reindexFin ps t
  let g ← if t' == t then pure g else g.replaceLocalDeclDefEq fv t'
  g.withContext do
    let args ← matrixEqArgs t'
    let pf ← mkAppOptM ``CatCrypt.Quantum.TensorProduct.kronecker_entries_of_eq
      (args.push (mkFVar fv))
    let r ← g.replace fv pf
    replaceMainGoal [r.mvarId]

end CatCryptCore.Tactic.KronIndex

end

public section

open CatCrypt.Quantum.TensorProduct CatCrypt.Quantum.PartialTrace in
attribute [kron_nf] Matrix.conjTranspose_kronecker Matrix.one_kronecker_one Matrix.smul_kronecker
  Matrix.kronecker_smul Matrix.add_kronecker Matrix.kronecker_add Matrix.zero_kronecker
  Matrix.kronecker_zero Matrix.trace_kronecker Matrix.finset_sum_kronecker
  Matrix.kronecker_finset_sum Matrix.reindex_kronecker_mul_reindex_kronecker
  Matrix.conjTranspose_reindex_kronecker Matrix.reindex_one_kronecker_one
  Matrix.trace_reindex_kronecker Matrix.reindex_kronecker_apply
  CatCrypt.Quantum.TensorProduct.kronecker_mul_kronecker
  CatCrypt.Quantum.TensorProduct.conjTranspose_kronecker
  CatCrypt.Quantum.TensorProduct.kronecker_one_one CatCrypt.Quantum.TensorProduct.trace_kronecker
  kronecker_add_left kronecker_add_right kronecker_sub_left kronecker_sub_right kronecker_neg_left
  kronecker_neg_right kronecker_smul_left kronecker_smul_right kronecker_zero_left
  kronecker_zero_right CatCrypt.Quantum.TensorProduct.finset_sum_kronecker
  CatCrypt.Quantum.TensorProduct.kronecker_finset_sum kronecker_apply_finProdEquiv
  kronVec_apply_finProdEquiv kronecker_mulVec_kronVec partialTrace₁_kronecker
  partialTrace₂_kronecker

attribute [kron_nf ←] Matrix.mul_kronecker_mul

/-- `kron_nf` normalises Kronecker expressions: `kron_index`, then `simp only` with the simp set
`kron_nf`, the unit, zero, distributivity and scalar laws of matrix products, left-associated
products, and the additivity of `ᴴ`, `trace` and linear maps (partial traces). The result is a sum
of scalar multiples of single Kronecker products. -/
macro "kron_nf" : tactic =>
  `(tactic| (kron_index; simp only [$(Lean.mkIdent `kron_nf):ident, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_zero, Matrix.zero_mul, Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul,
    Matrix.mul_sub, Matrix.neg_mul, Matrix.mul_neg, Matrix.smul_mul, Matrix.mul_smul,
    Finset.sum_mul, Finset.mul_sum, smul_smul, smul_add, smul_sub, smul_zero, ← Matrix.mul_assoc,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_add, Matrix.conjTranspose_sub,
    Matrix.conjTranspose_neg, Matrix.conjTranspose_smul, Matrix.conjTranspose_sum,
    Matrix.conjTranspose_one, Matrix.conjTranspose_zero, Matrix.conjTranspose_conjTranspose,
    Matrix.trace_add, Matrix.trace_sub, Matrix.trace_neg, Matrix.trace_smul, Matrix.trace_sum,
    Matrix.trace_zero, map_add, map_sub, map_neg, map_smul, map_sum, map_zero, add_zero,
    zero_add]))

/-- `kron_ext` reduces an equation of matrices indexed by `Fin (d₁ * d₂)` to the entries at the
points `finProdEquiv (i₁, i₂)`, `finProdEquiv (j₁, j₂)` (after `kron_index`) and evaluates
Kronecker products, identities, sums and scalars there. `kron_ext i₁ i₂ j₁ j₂` names the four
indices. -/
syntax (name := kronExt) "kron_ext" (ppSpace colGt ident)* : tactic

/-- `kron_ext at h` replaces `h : M = N` between matrices indexed by `Fin (d₁ * d₂)` by its entry
equations at the images of index pairs, with Kronecker products evaluated there. -/
syntax (name := kronExtAt) "kron_ext" " at " ident : tactic

macro_rules
  | `(tactic| kron_ext) => `(tactic| kron_ext _i₁ _i₂ _j₁ _j₂)
  | `(tactic| kron_ext $i₁:ident $i₂:ident $j₁:ident $j₂:ident) =>
    `(tactic| (kron_index;
                kron_ext_apply;
                intro $i₁:ident $i₂:ident $j₁:ident $j₂:ident;
                try simp only [CatCrypt.Quantum.TensorProduct.kronecker_apply_finProdEquiv,
                  CatCrypt.Quantum.TensorProduct.one_apply_finProdEquiv,
                  CatCrypt.Quantum.TensorProduct.kronVec_apply_finProdEquiv,
                  Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply,
                  Matrix.zero_apply, Matrix.conjTranspose_apply, Matrix.sum_apply,
                  smul_eq_mul]))

macro_rules
  | `(tactic| kron_ext at $h:ident) =>
    `(tactic| (kron_ext_hyp $h:ident;
                try simp only [CatCrypt.Quantum.TensorProduct.kronecker_apply_finProdEquiv,
                  CatCrypt.Quantum.TensorProduct.one_apply_finProdEquiv,
                  CatCrypt.Quantum.TensorProduct.kronVec_apply_finProdEquiv,
                  Matrix.add_apply, Matrix.sub_apply, Matrix.neg_apply, Matrix.smul_apply,
                  Matrix.zero_apply, Matrix.conjTranspose_apply, Matrix.sum_apply,
                  smul_eq_mul] at $h:ident))

end
