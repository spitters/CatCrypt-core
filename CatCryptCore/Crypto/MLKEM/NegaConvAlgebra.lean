/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.MLKEM.MLKEMRankInstance
public import CatCryptCore.Crypto.MLKEM.Spec.Ntt

/-!
# The ring algebra of the ML-KEM module and the decryption noise

The signed negacyclic convolution `signedNegaConv` over a commutative ring is
commutative and additive in each argument. At the ML-KEM ring it is multiplication in
`(Z/3329Z)[X]/(X^256+1)` (`Spec.Ntt.coeffsToRqKem_polyMulKem`), which gives
associativity through the injective map `Spec.Coeffs.coeffsToRqKem`. At every module
rank `k`, the transpose is the adjoint of matrix-vector multiplication for the dot
product, and the decryption input of an honest ciphertext under an honest key is the
encoded message plus the noise `e · r + e₂ − s · e₁`.

## Main results

* `signedNegaConv_comm`, `signedNegaConv_add_left`, `signedNegaConv_add_right`,
  `signedNegaConv_smul_left` — commutativity and bilinearity of the convolution
* `ringMul_comm`, `ringMul_assoc`, `ringMul_add_left`, `ringMul_add_right` — the ring
  laws of `MLKEM512Instance.ringMul`
* `vecDot_matVecMul` — `(A s) · r = s · (Aᵀ r)`
* `decrypt_noise_eq` — `v − s · u = encode m + (e · r + e₂ − s · e₁)`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Lattice.SignedNegacyclicConv

variable {R : Type*} [CommRing R] {n : ℕ} [NeZero n]

/-- The signed negacyclic convolution is additive in its first argument. -/
theorem signedNegaConv_add_left (x y z : Fin n → R) :
    signedNegaConv (x + y) z = signedNegaConv x z + signedNegaConv y z := by
  funext k
  simp only [signedNegaConv, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> ring

/-- The signed negacyclic convolution is additive in its second argument. -/
theorem signedNegaConv_add_right (x y z : Fin n → R) :
    signedNegaConv x (y + z) = signedNegaConv x y + signedNegaConv x z := by
  funext k
  simp only [signedNegaConv, Pi.add_apply, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> ring

/-- The signed negacyclic convolution commutes with scaling of its first argument. -/
theorem signedNegaConv_smul_left (c : R) (x y : Fin n → R) :
    signedNegaConv (c • x) y = c • signedNegaConv x y := by
  funext k
  simp only [signedNegaConv, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> ring

/-- The signed negacyclic convolution is commutative: the substitution `i ↦ k - i`
of the summation index keeps the wrap condition `i ≤ k`. -/
theorem signedNegaConv_comm (x y : Fin n → R) :
    signedNegaConv x y = signedNegaConv y x := by
  funext k
  simp only [signedNegaConv]
  refine Fintype.sum_equiv (Equiv.subLeft k) _ _ fun i => ?_
  simp only [Equiv.subLeft_apply, sub_sub_cancel]
  have hiff : (k - i).val ≤ k.val ↔ i.val ≤ k.val := by
    by_cases h : i ≤ k
    · rw [Fin.coe_sub_iff_le.mpr h]
      exact iff_of_true (by omega) (Fin.le_def.mp h)
    · have h' : k < i := lt_of_not_ge h
      rw [Fin.coe_sub_iff_lt.mpr h']
      have := Fin.lt_def.mp h'
      have := k.isLt
      exact iff_of_false (by omega) (by omega)
  rw [mul_comm (y _)]
  exact if_congr hiff.symm rfl rfl

end CatCrypt.Crypto.Lattice.SignedNegacyclicConv

namespace CatCrypt.Crypto.MLKEM.MLKEMRankInstance

open MLKEM512Instance (Rq ringMul ringAdd ringSub Msg msgEncode)
open CatCrypt.Crypto.Lattice.SignedNegacyclicConv (signedNegaConv_comm signedNegaConv_add_left
  signedNegaConv_add_right)
open CatCrypt.Crypto.MLKEM.Spec.Coeffs (coeffsToRqKem coeffsToRqKem_injective coeffsToRqKem_add)
open CatCrypt.Crypto.MLKEM.Spec.Ntt (coeffsToRqKem_polyMulKem)

/-- `coeffsToRqKem` carries `ringMul` to multiplication in the quotient ring. -/
theorem coeffsToRqKem_ringMul (a b : Rq) :
    coeffsToRqKem (ringMul a b) = coeffsToRqKem a * coeffsToRqKem b :=
  coeffsToRqKem_polyMulKem a b

/-- `coeffsToRqKem` carries a finite sum to the sum of the images. -/
theorem coeffsToRqKem_sum {ι : Type*} (s : Finset ι) (f : ι → Rq) :
    coeffsToRqKem (∑ i ∈ s, f i) = ∑ i ∈ s, coeffsToRqKem (f i) :=
  map_sum (AddMonoidHom.mk' coeffsToRqKem coeffsToRqKem_add) f s

/-- `ringMul` is commutative. -/
theorem ringMul_comm (a b : Rq) : ringMul a b = ringMul b a :=
  signedNegaConv_comm a b

/-- `ringMul` is associative. -/
theorem ringMul_assoc (a b c : Rq) : ringMul (ringMul a b) c = ringMul a (ringMul b c) := by
  apply coeffsToRqKem_injective
  simp only [coeffsToRqKem_ringMul, mul_assoc]

/-- `ringMul` distributes over addition on the left. -/
theorem ringMul_add_left (a b c : Rq) : ringMul (a + b) c = ringMul a c + ringMul b c :=
  signedNegaConv_add_left a b c

/-- `ringMul` distributes over addition on the right. -/
theorem ringMul_add_right (a b c : Rq) : ringMul a (b + c) = ringMul a b + ringMul a c :=
  signedNegaConv_add_right a b c

/-- The dot product distributes over vector addition on the left. -/
theorem vecDot_add_left {k : ℕ} (u v w : Vec k) :
    vecDot (vecAdd u v) w = vecDot u w + vecDot v w := by
  simp only [vecDot, vecAdd, Pi.add_apply, ringMul_add_left, Finset.sum_add_distrib]

/-- The dot product distributes over vector addition on the right. -/
theorem vecDot_add_right {k : ℕ} (u v w : Vec k) :
    vecDot u (vecAdd v w) = vecDot u v + vecDot u w := by
  simp only [vecDot, vecAdd, Pi.add_apply, ringMul_add_right, Finset.sum_add_distrib]

/-- The dot product is symmetric. -/
theorem vecDot_comm {k : ℕ} (u v : Vec k) : vecDot u v = vecDot v u := by
  simp only [vecDot, ringMul_comm]

/-- The transpose is the adjoint of matrix-vector multiplication for the dot product:
`(A s) · r = s · (Aᵀ r)`. -/
theorem vecDot_matVecMul {k : ℕ} (A : Mat k) (s r : Vec k) :
    vecDot (matVecMul A s) r = vecDot s (matVecMul (matTranspose A) r) := by
  apply coeffsToRqKem_injective
  simp only [vecDot, matVecMul, matTranspose, coeffsToRqKem_sum, coeffsToRqKem_ringMul,
    Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  ring

/-- **The decryption noise.** For an honest key `t = A s + e` and an honest ciphertext
`u = Aᵀ r + e₁`, `v = t · r + e₂ + encode m`, the decryption input `v − s · u` is the
encoded message plus the noise `e · r + e₂ − s · e₁`. -/
theorem decrypt_noise_eq {k : ℕ} (A : Mat k) (s e r e1 : Vec k) (e2 : Rq) (m : Msg) :
    ringSub
        (ringAdd (ringAdd (vecDot (vecAdd (matVecMul A s) e) r) e2) (msgEncode m))
        (vecDot s (vecAdd (matVecMul (matTranspose A) r) e1)) =
      msgEncode m + (vecDot e r + e2 - vecDot s e1) := by
  simp only [ringSub, ringAdd, vecDot_add_left, vecDot_add_right, vecDot_matVecMul]
  abel

end CatCrypt.Crypto.MLKEM.MLKEMRankInstance
