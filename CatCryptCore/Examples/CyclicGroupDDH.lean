/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Crypto.Advantage

/-!
# Cyclic Group Abstraction and the DDH Games

An abstract cyclic-group interface `CyclicGroup G` with explicit exponents, together
with the group-theoretic Decisional Diffie–Hellman games `DDH_real` / `DDH_ideal` and
the advantage `DDH_Advantage`.

This is the exponent-level DDH formulation used by discrete-log encryption schemes
(e.g. Hashed ElGamal). It is distinct from the `PairingGroup` / `DDHDef` formulation
in `CatCryptCore.Examples.ElGamal` and `CatCryptCore.Crypto.Assumptions.DDH`: here the
group is presented abstractly with a bijective exponentiation `pow : Exp → G`, and the
shared-secret operation `elemPow` is defined through the discrete logarithm.

## Cyclic group interface

- `G` is a finite, nonempty type of group elements.
- `Exp` is a finite, nonempty type of exponents (`Z_q` where `q = |G|`).
- `pow : Exp → G` is exponentiation of the generator, assumed bijective.
- `mul` / `inv` / `one` give the group operation, inverse, and identity.
- `expMul` multiplies exponents; `pow_comm` records exponent commutativity.

## DDH games

- `DDH_real`: sample `a, b`, output `(g^a, g^b, g^(a·b))`.
- `DDH_ideal`: sample `a, b, c`, output `(g^a, g^b, g^c)`.
- `DDH_Advantage`: the distinguishing advantage between the two.

## References

* [Boneh & Shoup, *A Graduate Course in Applied Cryptography*, Chapter 11]
* [SSProve: theories/Crypt/examples/PKE/ElGamal.v]
-/

set_option autoImplicit false

namespace CatCryptCore.Examples.CyclicGroupDDH

open CatCrypt.Core
open CatCrypt.Crypto
open CatCrypt.Prob
open scoped ENNReal

/-! ## Cyclic Group Abstraction -/

/-- A cyclic group structure with explicit exponents.

An abstract interface capturing the algebraic structure of a prime-order cyclic
group: a bijective exponentiation `pow : Exp → G`, a commutative group operation,
and exponent multiplication. -/
class CyclicGroup (G : Type) where
  /-- The type of exponents (`Z_q` where `q` is the group order). -/
  Exp : Type
  /-- `G` is finite. -/
  finG : Fintype G
  /-- `G` is nonempty. -/
  neG : Nonempty G
  /-- Exponents are finite. -/
  finExp : Fintype Exp
  /-- Exponents are nonempty. -/
  neExp : Nonempty Exp
  /-- The generator. -/
  gen : G
  /-- Exponentiation: `g^a`. -/
  pow : Exp → G
  /-- Group multiplication. -/
  mul : G → G → G
  /-- Group inverse. -/
  inv : G → G
  /-- Exponent multiplication (in `Z_q`). -/
  expMul : Exp → Exp → Exp
  /-- Exponent negation (in `Z_q`). -/
  expNeg : Exp → Exp
  /-- Identity element. -/
  one : G
  /-- Exponent commutativity for `pow`. -/
  pow_comm : ∀ a b, pow (expMul a b) = pow (expMul b a)
  /-- Multiplication is associative. -/
  mul_assoc : ∀ x y z, mul (mul x y) z = mul x (mul y z)
  /-- Multiplication is commutative (in a cyclic group). -/
  mul_comm : ∀ x y, mul x y = mul y x
  /-- Right inverse: `x * x⁻¹ = 1`. -/
  mul_inv : ∀ x, mul x (inv x) = one
  /-- Right identity: `x * 1 = x`. -/
  mul_one : ∀ x, mul x one = x
  /-- Exponentiation is a bijection from `Exp` to `G`. -/
  pow_bij : Function.Bijective pow

attribute [reducible, instance] CyclicGroup.finG CyclicGroup.finExp
attribute [instance] CyclicGroup.neG CyclicGroup.neExp

namespace CyclicGroup

variable {G : Type} [CG : CyclicGroup G]

/-- Notation for group multiplication. -/
instance : Mul G := ⟨CG.mul⟩

/-- Notation for group inverse. -/
instance : Inv G := ⟨CG.inv⟩

/-- Notation for identity. -/
instance : One G := ⟨CG.one⟩

/-- `g^a` via coercion. -/
abbrev gPow (a : CG.Exp) : G := CG.pow a

/-- `x^a` for `x : G` using the discrete log and then exponentiating.
Since `pow` is bijective, there is a unique exponent `e` with `pow e = x`; then
`x^a = pow (expMul e a)`. -/
noncomputable def elemPow (x : G) (a : CG.Exp) : G :=
  let e := (CG.pow_bij.2 x).choose
  CG.pow (CG.expMul e a)

/-- The inverse operation on exponents: `g^(-a) = (g^a)⁻¹`. -/
def powNeg (a : CG.Exp) : G := CG.inv (CG.pow a)

/-- `elemPow (pow e) a = pow (expMul e a)`: exponentiating `g^e` by `a` gives
`g^(e·a)`, from the definition of `elemPow` and the bijectivity of `pow`. -/
theorem elemPow_pow (e a : CG.Exp) : elemPow (CG.pow e) a = CG.pow (CG.expMul e a) := by
  unfold elemPow
  have he' : CG.pow (CG.pow_bij.2 (CG.pow e)).choose = CG.pow e :=
    (CG.pow_bij.2 (CG.pow e)).choose_spec
  have hinj : (CG.pow_bij.2 (CG.pow e)).choose = e := CG.pow_bij.1 he'
  rw [hinj]

end CyclicGroup

/-! ## Decisional Diffie–Hellman (DDH) Games

The DDH assumption states that it is hard to distinguish `(g^a, g^b, g^(ab))` for
random `a, b` from `(g^a, g^b, g^c)` for random `a, b, c`. -/

/-- DDH triple type: `(g^a, g^b, z)` where `z` is either `g^(ab)` or `g^c`. -/
abbrev DDHTriple (G : Type) := G × G × G

/-- Real DDH game: sample `a, b` and return `(g^a, g^b, g^(ab))`. -/
noncomputable def DDH_real (G : Type) [CG : CyclicGroup G] : SPComp (DDHTriple G) := do
  let a ← SPComp.sample CG.Exp
  let b ← SPComp.sample CG.Exp
  let ga := CG.pow a
  let gb := CG.pow b
  let gab := CG.pow (CG.expMul a b)
  return (ga, gb, gab)

/-- Ideal DDH game: sample `a, b, c` and return `(g^a, g^b, g^c)`. -/
noncomputable def DDH_ideal (G : Type) [CG : CyclicGroup G] : SPComp (DDHTriple G) := do
  let a ← SPComp.sample CG.Exp
  let b ← SPComp.sample CG.Exp
  let c ← SPComp.sample CG.Exp
  let ga := CG.pow a
  let gb := CG.pow b
  let gc := CG.pow c
  return (ga, gb, gc)

/-- DDH advantage: the distinguishing advantage between real and ideal DDH games. -/
noncomputable def DDH_Advantage (G : Type) [CG : CyclicGroup G]
    (A : DDHTriple G → SPComp Bool) : ℝ≥0∞ :=
  AdvantageA (DDH_real G) (DDH_ideal G) A

end CatCryptCore.Examples.CyclicGroupDDH
