/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Mathlib.Data.Fintype.Card

/-!
# Abstract Cyclic-Group Parameters

`GroupParam` axiomatizes a finite cyclic group of prime order together with its
scalar field, packaged as a single structure so protocol definitions can quantify
over an arbitrary such group. The carrier `G` is the group; `Scalar` is the field
`ℤ/qℤ` where `q = |g|`; `exp x = gᣞ` is generator exponentiation and `groupExp h x`
is exponentiation of an arbitrary element. The structure records the group and
scalar-field axioms as fields, so a concrete instantiation discharges them once and
every downstream proof reasons purely equationally.

This is the abstract group interface used by the UC examples over discrete-log
groups (Pedersen commitment, dual-mode oblivious transfer).
-/

set_option autoImplicit false

namespace CatCrypt.Examples

/-- Parameters for a finite cyclic group of prime order together with its scalar
    field `ℤ/qℤ`. The carrier `G` is the group with generator `generator`; `Scalar`
    is the field of exponents; `exp` is generator exponentiation and `groupExp` is
    exponentiation of an arbitrary group element. The remaining fields record the
    group and field axioms needed for equational reasoning. -/
structure GroupParam where
  /-- The group carrier. -/
  G : Type
  /-- The scalar field `ℤ/qℤ`, where `q` is the order of the generator. -/
  Scalar : Type
  /-- `G` is finite. -/
  [finG : Fintype G]
  /-- `G` is nonempty. -/
  [neG : Nonempty G]
  /-- `G` has decidable equality. -/
  [decG : DecidableEq G]
  /-- `Scalar` is finite. -/
  [finScalar : Fintype Scalar]
  /-- `Scalar` is nonempty. -/
  [neScalar : Nonempty Scalar]
  /-- `Scalar` has decidable equality. -/
  [decScalar : DecidableEq Scalar]
  /-- The generator `g`. -/
  generator : G
  /-- The group identity element. -/
  identity : G
  /-- Generator exponentiation `g ^ x`. -/
  exp : Scalar → G
  /-- Exponentiation of an arbitrary element `h ^ x`. -/
  groupExp : G → Scalar → G
  /-- Scalar addition. -/
  scalarAdd : Scalar → Scalar → Scalar
  /-- Scalar multiplication. -/
  scalarMul : Scalar → Scalar → Scalar
  /-- Scalar subtraction. -/
  scalarSub : Scalar → Scalar → Scalar
  /-- Scalar division (well-defined by primality of the order). -/
  scalarDiv : Scalar → Scalar → Scalar
  /-- Scalar negation. -/
  scalarNeg : Scalar → Scalar
  /-- The additive identity scalar. -/
  scalarZero : Scalar
  /-- Group multiplication. -/
  groupMul : G → G → G
  /-- Group inverse. -/
  groupInv : G → G
  /-- The multiplicative identity scalar. -/
  scalarOne : Scalar
  /-- Generator exponentiation is a homomorphism: `g ^ (x + y) = gᣞ · gᣩ`. -/
  exp_add : ∀ x y, exp (scalarAdd x y) = groupMul (exp x) (exp y)
  /-- `g ^ 0 = 1`. -/
  exp_zero : exp scalarZero = identity
  /-- Division is a right inverse to multiplication: `(x / y) · y = x` for `y ≠ 0`. -/
  div_mul_cancel : ∀ x y, y ≠ scalarZero → scalarMul (scalarDiv x y) y = x
  /-- Generator exponentiation is a special case of general exponentiation. -/
  groupExp_generator : ∀ x, exp x = groupExp generator x
  /-- Exponentiation of a power: `(g ^ w) ^ e = g ^ (w · e)`. -/
  groupExp_exp : ∀ w e, groupExp (exp w) e = exp (scalarMul w e)
  /-- `h ^ 1 = h`. -/
  groupExp_one : ∀ h, groupExp h scalarOne = h
  /-- General exponentiation is additive in the exponent. -/
  groupExp_add : ∀ h a b, groupExp h (scalarAdd a b) = groupMul (groupExp h a) (groupExp h b)
  /-- Distinct scalars have nonzero difference. -/
  scalarSub_ne_zero : ∀ a b, a ≠ b → scalarSub a b ≠ scalarZero
  /-- Right identity for group multiplication. -/
  groupMul_identity : ∀ a, groupMul a identity = a
  /-- Left identity for group multiplication. -/
  identity_groupMul : ∀ a, groupMul identity a = a
  /-- Right inverse for group multiplication. -/
  groupMul_inv : ∀ a, groupMul a (groupInv a) = identity
  /-- Left inverse for group multiplication. -/
  inv_groupMul : ∀ a, groupMul (groupInv a) a = identity
  /-- Group multiplication is associative. -/
  groupMul_assoc : ∀ a b c, groupMul (groupMul a b) c = groupMul a (groupMul b c)
  /-- `h ^ 0 = 1`. -/
  groupExp_zero : ∀ h, groupExp h scalarZero = identity
  /-- `a · 1 = a`. -/
  scalarMul_one : ∀ a, scalarMul a scalarOne = a
  /-- Inverse of a power: `(h ^ e)⁻¹ = h ^ (-e)`. -/
  groupInv_groupExp : ∀ h e, groupInv (groupExp h e) = groupExp h (scalarNeg e)
  /-- Subtraction as addition of the negation. -/
  scalarSub_eq : ∀ a b, scalarSub a b = scalarAdd a (scalarNeg b)
  /-- Right negation cancels: `a + (-a) = 0`. -/
  scalarAdd_neg : ∀ a, scalarAdd a (scalarNeg a) = scalarZero
  /-- Generator exponentiation is surjective. -/
  exp_surj : ∀ h, ∃ x, exp x = h
  /-- Generator exponentiation is injective (prime order). -/
  exp_inj : ∀ x y, exp x = exp y → x = y
  /-- Scalar addition is commutative. -/
  scalarAdd_comm : ∀ a b, scalarAdd a b = scalarAdd b a
  /-- Scalar addition is associative. -/
  scalarAdd_assoc : ∀ a b c, scalarAdd (scalarAdd a b) c = scalarAdd a (scalarAdd b c)
  /-- Scalar multiplication distributes over addition on the left. -/
  scalarMul_add : ∀ a b c, scalarMul a (scalarAdd b c) = scalarAdd (scalarMul a b) (scalarMul a c)
  /-- Scalar multiplication distributes over addition on the right. -/
  scalarAdd_mul : ∀ a b c, scalarMul (scalarAdd a b) c = scalarAdd (scalarMul a c) (scalarMul b c)
  /-- Scalar multiplication is commutative. -/
  scalarMul_comm : ∀ a b, scalarMul a b = scalarMul b a
  /-- Right additive identity: `a + 0 = a`. -/
  scalarAdd_zero : ∀ a, scalarAdd a scalarZero = a
  /-- Left additive identity: `0 + a = a`. -/
  scalarZero_add : ∀ a, scalarAdd scalarZero a = a
  /-- Left negation cancels: `(-a) + a = 0`. -/
  scalarNeg_add : ∀ a, scalarAdd (scalarNeg a) a = scalarZero
  /-- Negation of zero is zero. -/
  scalarNeg_zero : scalarNeg scalarZero = scalarZero
  /-- Negation distributes over addition. -/
  scalarNeg_add_distrib : ∀ a b, scalarNeg (scalarAdd a b) = scalarAdd (scalarNeg a) (scalarNeg b)
  /-- `a · 0 = 0`. -/
  scalarMul_zero : ∀ a, scalarMul a scalarZero = scalarZero
  /-- `0 · a = 0`. -/
  scalarZero_mul : ∀ a, scalarMul scalarZero a = scalarZero
  /-- Division cancels multiplication: `(a · b) / b = a` for `b ≠ 0`. -/
  mul_div_cancel : ∀ a b, b ≠ scalarZero → scalarDiv (scalarMul a b) b = a
  /-- Scalar multiplication is associative. -/
  scalarMul_assoc : ∀ a b c, scalarMul (scalarMul a b) c = scalarMul a (scalarMul b c)

attribute [instance] GroupParam.finG GroupParam.neG GroupParam.decG GroupParam.finScalar
  GroupParam.neScalar GroupParam.decScalar

/-! ## Derived scalar-field lemmas -/

/-- Multiplication distributes over negation: `a · (-b) = -(a · b)`. -/
lemma scalarMul_neg (gp : GroupParam) (a b : gp.Scalar) :
    gp.scalarMul a (gp.scalarNeg b) = gp.scalarNeg (gp.scalarMul a b) := by
  have h : gp.scalarAdd (gp.scalarMul a b) (gp.scalarMul a (gp.scalarNeg b)) = gp.scalarZero := by
    rw [← gp.scalarMul_add, gp.scalarAdd_neg, gp.scalarMul_zero]
  calc gp.scalarMul a (gp.scalarNeg b)
      = gp.scalarAdd gp.scalarZero (gp.scalarMul a (gp.scalarNeg b)) := by rw [gp.scalarZero_add]
    _ = gp.scalarAdd (gp.scalarAdd (gp.scalarNeg (gp.scalarMul a b)) (gp.scalarMul a b))
          (gp.scalarMul a (gp.scalarNeg b)) := by rw [gp.scalarNeg_add]
    _ = gp.scalarAdd (gp.scalarNeg (gp.scalarMul a b))
          (gp.scalarAdd (gp.scalarMul a b) (gp.scalarMul a (gp.scalarNeg b))) := by
          rw [gp.scalarAdd_assoc]
    _ = gp.scalarAdd (gp.scalarNeg (gp.scalarMul a b)) gp.scalarZero := by rw [h]
    _ = gp.scalarNeg (gp.scalarMul a b) := by rw [gp.scalarAdd_zero]

/-- Multiplication distributes over negation on the left: `(-a) · b = -(a · b)`. -/
lemma scalarNeg_mul (gp : GroupParam) (a b : gp.Scalar) :
    gp.scalarMul (gp.scalarNeg a) b = gp.scalarNeg (gp.scalarMul a b) := by
  rw [gp.scalarMul_comm, scalarMul_neg, gp.scalarMul_comm]

end CatCrypt.Examples
