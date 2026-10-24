/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.KWiseOracle
public import CatCryptCore.Quantum.QROM.QMLWEAux
public import CatCryptCore.Crypto.MLKEM.FIPS203QROMQuantumMLWE
public import Mathlib.FieldTheory.Finite.GaloisField
public import Mathlib.LinearAlgebra.Lagrange

/-!
# Polynomial oracles and quantum module-LWE without oracle access

A uniform polynomial `p` of degree `< k` over a finite field `F`, read through an
injection `ι : D → F` and a balanced map `π : F → R`, gives a `k`-wise independent
table `x ↦ π (p (ι x))` (`polyOracle_kWise`). By `prOut_avg_eq_of_kWise`
(Zhandry, CRYPTO 2012, Theorem 6.1) such tables can replace the uniform
auxiliary tables `G`, `J`, `Hq`, `T` of `qMLWEAux` and `qMLWEExtAux`: a
reduction that draws the polynomial coefficients itself and computes every
oracle answer, decapsulation answer and key from the polynomials is a quantum
distinguisher without oracle access with the same acceptance probability.

The tables are replaced one at a time. For fixed values of the other tables,
one run of the distinguisher, as a function of the replaced table, is a finite
sum of functions each reading at most `auxDeg q k` points: every value of the
merged oracle `auxOracle` and of the decapsulation function `decapsHq` reads
one point of each table (`ReadsOne`), every unitary of the flattened
multi-round adversary reads at most `k` points (`flatten_family_dependsOn`), and
the key `Hq p` reads one.

## Main definitions

* `pushWeight Φ` — the weight on tables of `Φ ω` at a uniform seed `ω`
* `polyTable ι π k cf`, `polyOracle ι π k`, `Balanced π` — the polynomial table
  and its weight
* `KWiseInvariant k g` — every `k`-wise independent weight gives `g` its
  uniform average
* `ReadsOne Φ` — every value of `Φ H` is determined by `H` at one point
* `auxDeg q k` — the independence degree `2 (q' + (q' + 1) k) + 1`,
  `q' = flatQ q k q`
* `QStdDist`, `qStdAcc`, `qMLWE`, `qMLWEExt` — quantum distinguishers without
  oracle access and their module-LWE and extended module-LWE advantages
* `qRedSamp`, `qRedPoly` — the reductions that sample their own oracles
* `PolyData D R` — a field, an injection of `D` and a balanced map onto `R`
* `qMLWEStdBound` — `qMLWEBound` with standard module-LWE terms

## Main results

* `polyOracle_kWise` — a uniform polynomial of degree `< k` is `k`-wise
  independent
* `KWiseInvariant.of_dependsOn`, `KWiseInvariant.push` — functions depending on
  at most `k` points keep their average under `k`-wise independent families
* `chainOp_family_dependsOn`, `flatten_family_dependsOn`,
  `prOutC_family_dependsOn` — locality of chains whose unitaries read the table
* `kWiseInvariant_qAuxRun_G`, `_J`, `_Hq`, `_T` — one run of a distinguisher,
  table by table
* `qMLWEAux_eq_qMLWE_qRedPoly`, `qMLWEExtAux_eq_qMLWEExt_qRedPoly` — module-LWE
  with oracle access equals standard quantum module-LWE of `qRedPoly`
* `PolyData.nonempty_galois` — polynomial data over `GaloisField p N` for a
  range of size `p ^ M`, `M ≤ N`, and a domain of size at most `p ^ N`
* `mlkem512_qindcca_qmlwe_std` — the ML-KEM-512 QROM bound under quantum
  module-LWE and extended module-LWE, with no auxiliary oracles

## The reduction and the assumption

The added cost of `qRedPoly` over the distinguisher is drawing `auxDeg q k`
field elements per table and evaluating a polynomial of degree `< auxDeg q k`
per oracle entry, decapsulation answer and key. The assumption is module-LWE
and extended module-LWE against quantum distinguishers without oracle access.
The key type `K` and the oracle range `Fin n`, `n = |K × Seed|`, are parameters
of `mlkem512_qindcca_qmlwe_std`; its polynomial data exist by
`PolyData.nonempty_galois` when `|K|` and `n` are powers of one prime.

## References

* [Zhandry — Secure Identity-Based Encryption in the Quantum Random Oracle
  Model, CRYPTO 2012], Theorem 6.1
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal NNReal

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## Weights pushed forward from a uniform seed -/

section Push

variable {α β Ω : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype Ω]

/-- The weight on tables of the table `Φ ω` at a uniform seed `ω`. -/
def pushWeight (Φ : Ω → α → β) (H : α → β) : ℝ≥0 :=
  ∑ ω, if Φ ω = H then ((Fintype.card Ω : ℝ≥0))⁻¹ else 0

/-- The cylinder of `H₀` on `S` as a product of finsets. -/
theorem cyl_eq_piFinset (S : Finset α) (H₀ : α → β) :
    cyl S H₀ = Fintype.piFinset fun x => if x ∈ S then {H₀ x} else Finset.univ := by
  ext H
  simp only [cyl, Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset]
  refine ⟨fun h x => ?_, fun h x hx => ?_⟩
  · split_ifs with hx
    · exact Finset.mem_singleton.mpr (h x hx)
    · exact Finset.mem_univ _
  · simpa [hx] using h x

theorem card_cyl_mul (S : Finset α) (H₀ : α → β) :
    (cyl S H₀).card * Fintype.card β ^ S.card = Fintype.card β ^ Fintype.card α := by
  rw [cyl_eq_piFinset, Fintype.card_piFinset]
  have h1 : ∏ x, (if x ∈ S then ({H₀ x} : Finset β) else Finset.univ).card =
      ∏ x, if x ∈ S then 1 else Fintype.card β :=
    Finset.prod_congr rfl fun x _ => by split_ifs <;> simp
  rw [h1, Finset.prod_ite, Finset.prod_const_one, one_mul, Finset.prod_const, ← pow_add]
  congr 1
  have h2 : (Finset.univ.filter fun x => x ∉ S) = Sᶜ := by ext; simp
  rw [h2, Finset.card_compl]
  have := Finset.card_le_univ S
  omega

/-- A seeded family whose tables at any `≤ k` points take each value vector on
`|Ω| / |β|^j` seeds is `k`-wise independent. -/
theorem kWiseIndep_pushWeight [Nonempty Ω] [Nonempty β] {k : ℕ} (Φ : Ω → α → β)
    (hΦ : ∀ S : Finset α, S.card ≤ k → ∀ H₀ : α → β,
      (Finset.univ.filter fun ω => ∀ x ∈ S, Φ ω x = H₀ x).card * Fintype.card β ^ S.card =
        Fintype.card Ω) :
    KWiseIndep k (pushWeight Φ) := by
  intro S hS H₀
  have hL : ∑ H ∈ cyl S H₀, pushWeight Φ H =
      ((Finset.univ.filter fun ω => ∀ x ∈ S, Φ ω x = H₀ x).card : ℝ≥0) *
        ((Fintype.card Ω : ℝ≥0))⁻¹ := by
    simp only [pushWeight]
    rw [Finset.sum_comm, Finset.card_filter, Nat.cast_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun ω _ => ?_
    rw [Finset.sum_ite_eq]
    split_ifs with h1 h2 h2 <;> simp_all [cyl]
  rw [hL, Finset.sum_const, nsmul_eq_mul, Fintype.card_fun, Nat.cast_pow]
  have h1' : ((Finset.univ.filter fun ω => ∀ x ∈ S, Φ ω x = H₀ x).card : ℝ≥0) *
      (Fintype.card β : ℝ≥0) ^ S.card = Fintype.card Ω := by exact_mod_cast hΦ S hS H₀
  have h2' : ((cyl S H₀).card : ℝ≥0) * (Fintype.card β : ℝ≥0) ^ S.card =
      (Fintype.card β : ℝ≥0) ^ Fintype.card α := by exact_mod_cast card_cyl_mul S H₀
  have hΩ : (Fintype.card Ω : ℝ≥0) ≠ 0 := by simp
  have hβ : (Fintype.card β : ℝ≥0) ^ S.card ≠ 0 := by simp
  have hc1 : ((Finset.univ.filter fun ω => ∀ x ∈ S, Φ ω x = H₀ x).card : ℝ≥0) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1'
    exact hΩ h1'.symm
  have hc2 : ((cyl S H₀).card : ℝ≥0) ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h2'
    exact pow_ne_zero _ (by simp) h2'.symm
  rw [← h1', ← h2', mul_inv, mul_inv, ← mul_assoc, ← mul_assoc, mul_inv_cancel₀ hc1,
    mul_inv_cancel₀ hc2]

end Push

/-! ## Counting through a surjective additive map -/

section Count

variable {G M : Type} [AddGroup G] [AddGroup M] [Fintype G] [Fintype M] [DecidableEq M]

/-- Under a surjective additive map `E`, the preimage of `A` has `|A| |G| / |M|`
elements. -/
theorem card_preimage_mul_of_surjective (E : G →+ M) (hE : Function.Surjective E)
    (A : Finset M) :
    (Finset.univ.filter fun g => E g ∈ A).card * Fintype.card M =
      Fintype.card G * A.card := by
  have hfib : ∀ b : M, (Finset.univ.filter fun g => E g = b).card =
      (Finset.univ.filter fun g => E g = 0).card := fun b =>
    AddMonoidHom.card_fiber_eq_of_mem_range E (hE b) (hE 0)
  have hA : (Finset.univ.filter fun g => E g ∈ A).card =
      ∑ b ∈ A, (Finset.univ.filter fun g => E g = b).card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := E) (t := A) fun g hg => by simpa using hg]
    refine Finset.sum_congr rfl fun b hb => ?_
    congr 1
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨h ▸ hb, h⟩⟩
  have hG : Fintype.card G = ∑ b : M, (Finset.univ.filter fun g => E g = b).card := by
    rw [← Finset.card_univ, Finset.card_eq_sum_card_fiberwise (f := E) (t := Finset.univ)
      fun _ _ => Finset.mem_coe.mpr (Finset.mem_univ _)]
  rw [hA, hG]
  simp only [hfib, Finset.sum_const, smul_eq_mul, Finset.card_univ]
  ring

end Count

/-! ## Polynomials of degree `< k` -/

section Poly

variable {F : Type} [Field F] [Fintype F] [DecidableEq F]

/-- The value at `y` of the polynomial with coefficient vector `cf`. -/
def polyEval {k : ℕ} (cf : Fin k → F) (y : F) : F :=
  ∑ i, cf i * y ^ (i : ℕ)

variable {D : Type} [Fintype D] [DecidableEq D]

omit [Fintype F] [Fintype D] in
/-- Interpolation: at `≤ k` distinct points any values are taken by a
polynomial of degree `< k`. -/
theorem exists_polyEval (k : ℕ) (ι : D → F) (hι : Function.Injective ι) (S : Finset D)
    (hS : S.card ≤ k) (r : D → F) : ∃ cf : Fin k → F, ∀ x ∈ S, polyEval cf (ι x) = r x := by
  set p := Lagrange.interpolate S ι r
  have hdeg : p.natDegree < k ∨ k = 0 := by
    by_cases hp : p = 0
    · rcases Nat.eq_zero_or_pos k with h | h
      · exact Or.inr h
      · exact Or.inl (by rw [hp, Polynomial.natDegree_zero]; exact h)
    · left
      rw [Polynomial.natDegree_lt_iff_degree_lt hp]
      exact (Lagrange.degree_interpolate_lt (r := r) hι.injOn).trans_le (by exact_mod_cast hS)
  rcases hdeg with hdeg | hk
  · refine ⟨fun i => p.coeff i, fun x hx => ?_⟩
    rw [polyEval, Fin.sum_univ_eq_sum_range (fun i => p.coeff i * ι x ^ i),
      ← Polynomial.eval_eq_sum_range' hdeg, Lagrange.eval_interpolate_at_node _ hι.injOn hx]
  · subst hk
    refine ⟨fun i => i.elim0, fun x hx => ?_⟩
    have := Finset.card_pos.mpr ⟨x, hx⟩
    omega

/-- Evaluation at the points of `S`, as an additive map on coefficient vectors. -/
def evalOn (k : ℕ) (ι : D → F) (S : Finset D) : (Fin k → F) →+ (S → F) where
  toFun cf x := polyEval cf (ι x)
  map_zero' := by funext x; simp [polyEval]
  map_add' a b := by funext x; simp [polyEval, add_mul, Finset.sum_add_distrib]

omit [Fintype F] [Fintype D] in
theorem evalOn_surjective (k : ℕ) (ι : D → F) (hι : Function.Injective ι) (S : Finset D)
    (hS : S.card ≤ k) : Function.Surjective (evalOn k ι S) := by
  intro v
  obtain ⟨cf, hcf⟩ := exists_polyEval k ι hι S hS fun x => if hx : x ∈ S then v ⟨x, hx⟩ else 0
  refine ⟨cf, funext fun x => ?_⟩
  show polyEval cf (ι x) = v x
  rw [hcf x x.2, dite_eq_left x.2]

variable {R : Type} [Fintype R] [DecidableEq R]

/-- The table `x ↦ π (p (ι x))` of the polynomial `p` with coefficient vector
`cf`, of degree `< k`. -/
def polyTable (ι : D → F) (π : F → R) (k : ℕ) (cf : Fin k → F) : D → R :=
  fun x => π (polyEval cf (ι x))

/-- The weight on tables `D → R` of `polyTable ι π k cf` at a uniform
coefficient vector `cf`. -/
def polyOracle (ι : D → F) (π : F → R) (k : ℕ) : (D → R) → ℝ≥0 :=
  pushWeight (polyTable ι π k)

/-- `π` is balanced: each of its fibres has `|F| / |R|` elements. -/
def Balanced (π : F → R) : Prop :=
  ∀ r, (Finset.univ.filter fun y => π y = r).card * Fintype.card R = Fintype.card F

/-- **A uniform polynomial of degree `< k` is a `k`-wise independent oracle.**
For an injection `ι : D → F` and a balanced `π : F → R`, the table
`x ↦ π (p (ι x))` of a uniform `p` of degree `< k` is `k`-wise independent. -/
theorem polyOracle_kWise (k : ℕ) (ι : D → F) (hι : Function.Injective ι) (π : F → R)
    (hπ : Balanced π) : KWiseIndep k (polyOracle ι π k) := by
  have : Nonempty R := Nonempty.intro (π 0)
  refine kWiseIndep_pushWeight _ fun S hS H₀ => ?_
  set A : Finset (S → F) := Fintype.piFinset fun x => Finset.univ.filter fun y => π y = H₀ x
  have hpre : (Finset.univ.filter fun cf : Fin k → F => ∀ x ∈ S, polyTable ι π k cf x = H₀ x) =
      Finset.univ.filter fun cf => evalOn k ι S cf ∈ A := by
    refine Finset.filter_congr fun cf _ => ?_
    simp only [A, Fintype.mem_piFinset, Finset.mem_filter, Finset.mem_univ, true_and,
      polyTable]
    exact ⟨fun h x => h x x.2, fun h x hx => h ⟨x, hx⟩⟩
  have hcount := card_preimage_mul_of_surjective (evalOn k ι S) (evalOn_surjective k ι hι S hS) A
  have hA : A.card * Fintype.card R ^ S.card = Fintype.card F ^ S.card := by
    rw [Fintype.card_piFinset, ← Fintype.card_coe S, ← Finset.card_univ (α := S),
      Finset.prod_mul_pow_card, ← Finset.prod_const]
    exact Finset.prod_congr rfl fun x _ => hπ (H₀ x)
  rw [hpre]
  rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_coe, Fintype.card_fin] at hcount
  have hF : 0 < Fintype.card F ^ S.card := pow_pos Fintype.card_pos _
  refine Nat.eq_of_mul_eq_mul_right hF ?_
  calc _ = (Finset.univ.filter fun cf => evalOn k ι S cf ∈ A).card *
        Fintype.card F ^ S.card * Fintype.card R ^ S.card := by ring
    _ = Fintype.card F ^ k * (A.card * Fintype.card R ^ S.card) := by rw [hcount]; ring
    _ = _ := by rw [hA, Fintype.card_fun, Fintype.card_fin]

end Poly

/-! ## Averages that every `k`-wise independent weight preserves -/

section Invariant

variable {α β : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]

/-- Every `k`-wise independent weight gives `g` its uniform average. -/
def KWiseInvariant (k : ℕ) (g : (α → β) → ℝ≥0∞) : Prop :=
  ∀ μ : (α → β) → ℝ≥0, KWiseIndep k μ →
    ∑ H, (μ H : ℝ≥0∞) * g H = ∑ H, (Fintype.card (α → β) : ℝ≥0∞)⁻¹ * g H

namespace KWiseInvariant

theorem sum {k : ℕ} {κ : Type} (s : Finset κ) (g : κ → (α → β) → ℝ≥0∞)
    (hg : ∀ j ∈ s, KWiseInvariant k (g j)) : KWiseInvariant k (fun H => ∑ j ∈ s, g j H) := by
  intro μ hμ
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j hj => hg j hj μ hμ

theorem const_mul {k : ℕ} {g : (α → β) → ℝ≥0∞} (hg : KWiseInvariant k g) (c : ℝ≥0∞) :
    KWiseInvariant k (fun H => c * g H) := by
  intro μ hμ
  calc ∑ H, (μ H : ℝ≥0∞) * (c * g H) = c * ∑ H, (μ H : ℝ≥0∞) * g H := by
        rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun H _ => mul_left_comm _ _ _
    _ = c * ∑ H, (Fintype.card (α → β) : ℝ≥0∞)⁻¹ * g H := by rw [hg μ hμ]
    _ = _ := by rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun H _ => mul_left_comm _ _ _

theorem mono {k l : ℕ} {g : (α → β) → ℝ≥0∞} (hg : KWiseInvariant k g) (hkl : k ≤ l) :
    KWiseInvariant l g :=
  fun μ hμ => hg μ fun S hS H₀ => hμ S (hS.trans hkl) H₀

/-- A uniform average over a finite index of invariant functions is invariant. -/
theorem avg {k : ℕ} {Y : Type} [Fintype Y] (g : Y → (α → β) → ℝ≥0∞)
    (hg : ∀ y, KWiseInvariant k (g y)) :
    KWiseInvariant k (fun H => ∑ y, (Fintype.card Y : ℝ≥0∞)⁻¹ * g y H) :=
  sum Finset.univ (fun y H => (Fintype.card Y : ℝ≥0∞)⁻¹ * g y H) fun y _ => (hg y).const_mul _

/-- The value `ofReal (re (F H))` of a function `F` depending on at most `k`
points, with non-negative real part, is invariant. -/
theorem of_dependsOn [Nonempty β] {k : ℕ} {F : (α → β) → ℂ} (hF : DependsOnAtMost k F)
    (hre : ∀ H, 0 ≤ (F H).re) : KWiseInvariant k (fun H => ENNReal.ofReal (F H).re) := by
  intro μ hμ
  have key : ∀ ν : (α → β) → ℝ≥0, ∑ H, (ν H : ℝ≥0∞) * ENNReal.ofReal (F H).re =
      ENNReal.ofReal (∑ H, ((ν H : ℝ) : ℂ) * F H).re := by
    intro ν
    rw [Complex.re_sum, ENNReal.ofReal_sum_of_nonneg fun H _ => by
      rw [Complex.re_ofReal_mul]; exact mul_nonneg (ν H).2 (hre H)]
    refine Finset.sum_congr rfl fun H _ => ?_
    rw [Complex.re_ofReal_mul, ENNReal.ofReal_mul (ν H).coe_nonneg, ENNReal.ofReal_coe_nnreal]
  set u : ℝ≥0 := ((Fintype.card (α → β) : ℝ≥0))⁻¹ with hu
  have hc : (Fintype.card (α → β) : ℝ≥0∞)⁻¹ = (u : ℝ≥0∞) := by
    rw [hu, ENNReal.coe_inv (by simp), ENNReal.coe_natCast]
  have hcyl : CylinderAgree k (fun H => ((μ H : ℝ) : ℂ)) (fun _ => ((u : ℝ) : ℂ)) :=
    fun S hS H₀ => by
      have h2 := congrArg (fun r : ℝ≥0 => ((r : ℝ) : ℂ)) (hμ S hS H₀)
      simpa only [NNReal.coe_sum, Complex.ofReal_sum] using h2
  rw [hc, key μ, key (fun _ => u), sum_mul_eq_of_cylinderAgree hcyl hF]

end KWiseInvariant

variable {Ω : Type} [Fintype Ω]

/-- The average of `g` over a `k`-wise independent seeded family is its uniform
average. -/
theorem KWiseInvariant.push [Nonempty Ω] {k : ℕ} {g : (α → β) → ℝ≥0∞}
    (hg : KWiseInvariant k g) (Φ : Ω → α → β) (hΦ : KWiseIndep k (pushWeight Φ)) :
    ∑ ω, (Fintype.card Ω : ℝ≥0∞)⁻¹ * g (Φ ω) =
      ∑ H, (Fintype.card (α → β) : ℝ≥0∞)⁻¹ * g H := by
  rw [← hg _ hΦ]
  simp only [pushWeight, ENNReal.ofNNReal_finsetSum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [Finset.sum_eq_single (Φ ω)]
  · rw [ite_eq_left rfl, ENNReal.coe_inv (by simp), ENNReal.coe_natCast]
  · intro H _ hH
    rw [ite_eq_right (Ne.symm hH), ENNReal.coe_zero, zero_mul]
  · intro h
    exact absurd (Finset.mem_univ _) h

end Invariant

/-! ## Functions of a table read through a map that reads one point -/

section Reads

variable {α β γ δ : Type}

/-- Every value of `Φ H` is determined by `H` at one point at most. -/
def ReadsOne (Φ : (α → β) → γ → δ) : Prop :=
  ∀ y, ∃ S : Finset α, S.card ≤ 1 ∧ ∀ H H' : α → β, (∀ x ∈ S, H x = H' x) → Φ H y = Φ H' y

theorem DependsOnAtMost.comp_readsOne {k : ℕ} {F : (γ → δ) → ℂ} (hF : DependsOnAtMost k F)
    {Φ : (α → β) → γ → δ} (hΦ : ReadsOne Φ) : DependsOnAtMost k (fun H => F (Φ H)) := by
  classical
  choose T hT hTΦ using hΦ
  obtain ⟨ι, _, S, g, hg, hF⟩ := hF
  refine ⟨ι, inferInstance, fun i => (S i).biUnion T, fun i H => g i (Φ H),
    fun i => ⟨?_, ?_⟩, fun H => hF (Φ H)⟩
  · exact (Finset.card_biUnion_le_card_mul _ _ 1 fun y _ => hT y).trans (by simpa using (hg i).1)
  · intro H H' hH
    exact (hg i).2 _ _ fun y hy => hTΦ y H H' fun x hx => hH x (Finset.mem_biUnion.mpr ⟨y, hy, hx⟩)

theorem EntriesDependOnAtMost.comp_readsOne {d k : ℕ}
    {M : (γ → δ) → Matrix (Fin d) (Fin d) ℂ} (hM : EntriesDependOnAtMost k M)
    {Φ : (α → β) → γ → δ} (hΦ : ReadsOne Φ) : EntriesDependOnAtMost k (fun H => M (Φ H)) :=
  fun i j => (hM i j).comp_readsOne hΦ

end Reads

/-! ## Adversaries whose unitaries read the table -/

section Family

open Matrix CatCrypt.Quantum CatCrypt.Quantum.TensorProduct

variable {α β : Type}

theorem EntriesDependOnAtMost.mono {d k l : ℕ} {M : (α → β) → Matrix (Fin d) (Fin d) ℂ}
    (hM : EntriesDependOnAtMost k M) (hkl : k ≤ l) : EntriesDependOnAtMost l M :=
  fun i j => (hM i j).mono hkl

/-- A chain with `q` calls to an oracle whose entries read one point and
unitaries whose entries read `r` points has entries reading `q + (q + 1) r`
points. -/
theorem chainOp_family_dependsOn {d : ℕ} (O : (α → β) → Matrix (Fin d) (Fin d) ℂ)
    (hO : EntriesDependOnAtMost 1 O) (r : ℕ) :
    ∀ (q : ℕ) (U : (α → β) → Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ),
      (∀ i, EntriesDependOnAtMost r (fun H => (U H i : Matrix (Fin d) (Fin d) ℂ))) →
      EntriesDependOnAtMost (q + (q + 1) * r) (fun H => chainOp (O H) q (U H))
  | 0, U, hU => (hU 0).mono (by omega)
  | q + 1, U, hU =>
    ((chainOp_family_dependsOn O hO r q (fun H => Fin.tail (U H)) fun i => hU i.succ).mul hO
      le_rfl).mul (hU 0) (le_of_eq (by ring))

theorem kr_family_dependsOn {d c d' r : ℕ} (e : Fin (d * c) ≃ Fin d')
    {A : (α → β) → Matrix (Fin d) (Fin d) ℂ} (hA : EntriesDependOnAtMost r A)
    (B : Matrix (Fin c) (Fin c) ℂ) : EntriesDependOnAtMost r (fun H => kr e (A H) B) := by
  intro i j
  simp only [kr, Matrix.submatrix_apply, kronecker_apply]
  exact (hA _ _).mul (DependsOnAtMost.const 0 _) (by omega)

/-- The deferred round answering with a table-read function has entries
reading one point. -/
theorem roundV_family_dependsOn {d c a d' : ℕ} [NeZero c] (e : Fin (d * c) ≃ Fin d')
    (R : ClassicalRound d c a) (f : (α → β) → Fin c → Fin a) (hf : ReadsOne f) :
    EntriesDependOnAtMost 1 (fun H => (roundV e R (f H) : Matrix (Fin d') (Fin d') ℂ)) := by
  have hC : EntriesDependOnAtMost 1 (fun H => roundC e R (f H)) := by
    intro i j
    simp only [roundC, Matrix.sum_apply]
    refine DependsOnAtMost.sum_apply Finset.univ _ fun z _ => ?_
    obtain ⟨S, hS, hSf⟩ := hf z
    exact DependsOnAtMost.of_localOn hS fun H H' h => by simp only [hSf H H' h]
  exact hC.mul (EntriesDependOnAtMost.const 0 _) le_rfl

theorem liftU_family_dependsOn {d c d' r : ℕ} (e : Fin (d * c) ≃ Fin d')
    {U : (α → β) → Matrix.unitaryGroup (Fin d) ℂ}
    (hU : EntriesDependOnAtMost r (fun H => (U H : Matrix (Fin d) (Fin d) ℂ))) :
    EntriesDependOnAtMost r (fun H => (liftU e (U H) : Matrix (Fin d') (Fin d') ℂ)) :=
  kr_family_dependsOn e hU 1

/-- Merging a unitary reading one point between a chain whose unitaries read `r`
points and a constant chain gives unitaries reading `r + 1` points. -/
theorem mergeChain_family_dependsOn {d q r : ℕ} (V : (α → β) → Matrix.unitaryGroup (Fin d) ℂ)
    (B : (α → β) → Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ)
    (hV : EntriesDependOnAtMost 1 (fun H => (V H : Matrix (Fin d) (Fin d) ℂ)))
    (hB : ∀ i, EntriesDependOnAtMost 0 (fun H => (B H i : Matrix (Fin d) (Fin d) ℂ))) :
    ∀ (q₀ : ℕ) (A : (α → β) → Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ),
      (∀ i, EntriesDependOnAtMost r (fun H => (A H i : Matrix (Fin d) (Fin d) ℂ))) →
      ∀ i, EntriesDependOnAtMost (r + 1)
        (fun H => (mergeChain (V H) (B H) q₀ (A H) i : Matrix (Fin d) (Fin d) ℂ))
  | 0, A, hA, i => by
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [mergeChain, Fin.cons_zero, Submonoid.coe_mul]
      exact ((hB 0).mul hV le_rfl).mul (hA 0) (by omega)
    · simp only [mergeChain, Fin.cons_succ, Fin.tail]
      exact (hB i.succ).mono (by omega)
  | q₀ + 1, A, hA, i => by
    refine Fin.cases ?_ (fun i => ?_) i
    · simp only [mergeChain, Fin.cons_zero]
      exact (hA 0).mono (by omega)
    · simp only [mergeChain, Fin.cons_succ]
      exact mergeChain_family_dependsOn V B hV hB q₀ (fun H => Fin.tail (A H))
        (fun i => hA i.succ) i

variable {m n q c a : ℕ}

/-- Flattening `k` rounds that answer with a table-read function adds `k` read
points to each unitary. -/
theorem flatten_family_dependsOn [NeZero c] (f : (α → β) → Fin c → Fin a) (hf : ReadsOne f) :
    ∀ (k : ℕ) {w q₀ : ℕ} (A : (α → β) → MRH m n w q q₀ k c a)
      (R : Fin k → ClassicalRound (m * n * w) c a) (r : ℕ), (∀ H, (A H).rounds = R) →
      (∀ i, EntriesDependOnAtMost r
        (fun H => ((A H).head i : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ))) →
      (∀ j i, EntriesDependOnAtMost 0
        (fun H => ((A H).tail j i : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ))) →
      ∀ i, EntriesDependOnAtMost (r + k) (fun H => ((flatten (f H) k (A H)).U i :
        Matrix (Fin (m * n * ancW c k w)) (Fin (m * n * ancW c k w)) ℂ))
  | 0, _, _, _, _, _, _, hhead, _, i => hhead i
  | k + 1, w, q₀, A, R, r, hR, hhead, htail, i => by
    have h := flatten_family_dependsOn f hf k (fun H => peel (f H) (A H))
      (liftR (ancE m n w c) ∘ Fin.tail R) (r + 1) (fun H => by simp only [peel, hR H])
      (fun i => by
        simp only [peel, hR]
        exact mergeChain_family_dependsOn _ _ (roundV_family_dependsOn _ (R 0) f hf)
          (fun i => liftU_family_dependsOn _ (htail 0 i)) q₀ _
          (fun i => liftU_family_dependsOn _ (hhead i)) i)
      (fun j i => by
        simp only [peel, Function.comp_apply]
        exact liftU_family_dependsOn _ (htail j.succ i)) i
    exact h.mono (by omega)

/-- The initial state of the flattened adversary does not depend on the round
answers or on the head. -/
theorem flatten_init_eq [NeZero c] (f f' : Fin c → Fin a) :
    ∀ (k : ℕ) {w q₀ : ℕ} (A A' : MRH m n w q q₀ k c a), A.init = A'.init →
      (flatten f k A).init = (flatten f' k A').init
  | 0, _, _, _, _, h => h
  | k + 1, _, _, A, A', h => flatten_init_eq f f' k (peel f A) (peel f' A') (by
      simp only [peel, h])

variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] {w j : ℕ} [NeZero n]

omit [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] in
/-- The acceptance probability of a family of adversaries whose unitaries read
`r` points, against an oracle each of whose values reads one point, depends on
at most `2 (j + (j + 1) r)` points. -/
theorem prOutC_family_dependsOn (A : (α → β) → QAdv m n w j) (O : (α → β) → Fin m → Fin n)
    (hO : ReadsOne O) (r : ℕ)
    (hU : ∀ i, EntriesDependOnAtMost r
      (fun H => ((A H).U i : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ)))
    (ρ P : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ) (hinit : ∀ H, (A H).init.val = ρ)
    (hfin : ∀ H, (A H).final = P) :
    DependsOnAtMost (2 * (j + (j + 1) * r)) (fun H => prOutC (A H) (O H)) := by
  have hOr : EntriesDependOnAtMost 1
      (fun H => (oracleU m n w (O H) : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ)) :=
    (oracleU_entries_dependsOn m n w).comp_readsOne hO
  have hX : EntriesDependOnAtMost (j + (j + 1) * r)
      (fun H => P * chainOp (oracleU m n w (O H) : Matrix _ _ ℂ) j (A H).U) :=
    (EntriesDependOnAtMost.const 0 P).mul
      (chainOp_family_dependsOn _ hOr r j (fun H => (A H).U) hU) (by omega)
  have heq : (fun H => prOutC (A H) (O H)) = fun H =>
      ((P * chainOp (oracleU m n w (O H) : Matrix _ _ ℂ) j (A H).U) * ρ *
        (P * chainOp (oracleU m n w (O H) : Matrix _ _ ℂ) j (A H).U)ᴴ).trace :=
    funext fun H => by simp only [prOutC, runOp, hinit H, hfin H]
  rw [heq]
  exact ((hX.mul (EntriesDependOnAtMost.const 0 ρ) (r := j + (j + 1) * r) (by omega)).mul
    hX.conjTranspose (by omega)).trace

/-- The acceptance probability of such a family is invariant under every
`K`-wise independent weight, for `K ≥ 2 (j + (j + 1) r)`. -/
theorem kWiseInvariant_prOut_family [Nonempty β] (A : (α → β) → QAdv m n w j)
    (O : (α → β) → Fin m → Fin n) (hO : ReadsOne O) (r : ℕ)
    (hU : ∀ i, EntriesDependOnAtMost r
      (fun H => ((A H).U i : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ)))
    (ρ P : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ) (hinit : ∀ H, (A H).init.val = ρ)
    (hfin : ∀ H, (A H).final = P) {K : ℕ} (hK : 2 * (j + (j + 1) * r) ≤ K) :
    KWiseInvariant K (fun H => prOut (A H) (O H)) := by
  have e : (fun H => prOut (A H) (O H)) = fun H => ENNReal.ofReal (prOutC (A H) (O H)).re :=
    funext fun H => prOut_eq_ofReal_re _ _
  rw [e]
  exact (KWiseInvariant.of_dependsOn (prOutC_family_dependsOn A O hO r hU ρ P hinit hfin)
    fun H => prOutC_re_nonneg _ _).mono hK

end Family

/-! ## The oracles of the auxiliary games read one point of each table -/

section AuxReads

open CatCrypt.Crypto.PKE.Games (Scheme)

variable {m₁ m₂ n c a : ℕ} {PK SK M C R K Hash Z : Type} [DecidableEq Z]
  (P : Scheme PK SK M C R) (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁)
  (eJ : (Z × C) ≃ Fin m₂) (eKR : (K × R) ≃ Fin n) (eC : C ≃ Fin c) (eKa : K ≃ Fin a)
  [DecidableEq Hash]

theorem readsOne_auxOracle_G (pk : PK) (Hq : C → K) (J : Fin m₂ → Fin n) (T : C → Fin n)
    (z : Z) : ReadsOne fun G => auxOracle P hpk eG eJ eKR pk Hq G J T z := by
  intro y
  induction y using Fin.addCases with
  | left x =>
    refine ⟨{x}, by simp, fun G G' h => ?_⟩
    simp only [auxOracle, mergeOracle, Fin.addCases_left, keyHop, coinCt,
      h x (Finset.mem_singleton_self x)]
  | right x =>
    exact ⟨∅, by simp, fun G G' _ => by simp only [auxOracle, mergeOracle, Fin.addCases_right]⟩

theorem readsOne_auxOracle_J (pk : PK) (Hq : C → K) (G : Fin m₁ → Fin n) (T : C → Fin n)
    (z : Z) : ReadsOne fun J => auxOracle P hpk eG eJ eKR pk Hq G J T z := by
  intro y
  induction y using Fin.addCases with
  | left x =>
    exact ⟨∅, by simp, fun J J' _ => by simp only [auxOracle, mergeOracle, Fin.addCases_left]⟩
  | right x =>
    refine ⟨{x}, by simp, fun J J' h => ?_⟩
    simp only [auxOracle, mergeOracle, Fin.addCases_right, prefixUpdate,
      h x (Finset.mem_singleton_self x)]

theorem readsOne_auxOracle_T (pk : PK) (Hq : C → K) (G : Fin m₁ → Fin n) (J : Fin m₂ → Fin n)
    (z : Z) : ReadsOne fun T => auxOracle P hpk eG eJ eKR pk Hq G J T z := by
  intro y
  induction y using Fin.addCases with
  | left x =>
    exact ⟨∅, by simp, fun T T' _ => by simp only [auxOracle, mergeOracle, Fin.addCases_left]⟩
  | right x =>
    refine ⟨{(eJ.symm x).2}, by simp, fun T T' h => ?_⟩
    simp only [auxOracle, mergeOracle, Fin.addCases_right, prefixUpdate,
      h _ (Finset.mem_singleton_self _)]

theorem readsOne_auxOracle_Hq (pk : PK) (G : Fin m₁ → Fin n) (J : Fin m₂ → Fin n)
    (T : C → Fin n) (z : Z) : ReadsOne fun Hq => auxOracle P hpk eG eJ eKR pk Hq G J T z := by
  intro y
  induction y using Fin.addCases with
  | left x =>
    refine ⟨{coinCt (kemEncAt P eG pk) eKR.symm G x}, by simp, fun Hq Hq' h => ?_⟩
    simp only [auxOracle, mergeOracle, Fin.addCases_left, keyHop,
      h _ (Finset.mem_singleton_self _)]
  | right x =>
    exact ⟨∅, by simp, fun Hq Hq' _ => by simp only [auxOracle, mergeOracle, Fin.addCases_right]⟩

omit [DecidableEq Z] [DecidableEq Hash] in
theorem readsOne_decapsHq [Nonempty K] [DecidableEq C] (p : C) :
    ReadsOne fun Hq : C → K => decapsHq eC eKa Hq p := by
  intro y
  refine ⟨{eC.symm y}, by simp, fun Hq Hq' h => ?_⟩
  simp only [decapsHq, h _ (Finset.mem_singleton_self _)]

end AuxReads

/-! ## One run of a distinguisher with oracle access, table by table -/

/-- The number of table points on which one run of a distinguisher with `k`
rounds and `q` queries per segment depends: `2 (q' + (q' + 1) k) + 1` with
`q' = flatQ q k q`. -/
def auxDeg (q k : ℕ) : ℕ := 2 * (flatQ q k q + (flatQ q k q + 1) * k) + 1

theorem le_auxDeg {q k j r : ℕ} (hj : j ≤ flatQ q k q) (hr : r ≤ k) :
    1 + 2 * (j + (j + 1) * r) ≤ auxDeg q k := by
  unfold auxDeg
  rw [Nat.add_comm 1]
  exact Nat.succ_le_succ
    (Nat.mul_le_mul_left 2 (Nat.add_le_add hj (Nat.mul_le_mul (Nat.succ_le_succ hj) hr)))

section AuxBase

open CatCrypt.Crypto.PKE.Games (Scheme)

variable {m₁ m₂ n W q k c a : ℕ} {PK SK M C R K Hash Z ι X : Type} [Fintype PK] [Fintype SK]
  [Fintype M] [DecidableEq M] [Nonempty M] [Fintype Z] [DecidableEq Z] [Fintype K] [Nonempty K]
  [DecidableEq K] [Fintype R] [Fintype C] [DecidableEq C] [DecidableEq Hash] [Fintype ι]
  (S : Scheme PK SK M C R) (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁) (eJ : (Z × C) ≃ Fin m₂)
  (eKR : (K × R) ≃ Fin n) (eC : C ≃ Fin c) (eKa : K ≃ Fin a) [NeZero n] [NeZero c]
  (key : X → PK) (E : QAuxDist ι X (m₁ + m₂) n W q k c a C K) (x : X)

/-- The adversary run by `E` on input `x` with coins `i` when it receives the
key `h`, with decapsulation answers from the table `Hq`. -/
def auxRunAdv (h : K) (Hq : C → K) (i : ι) :
    QAdv (m₁ + m₂) n (ancW c k W) (E.stop x h i) :=
  truncAdv (toQAdv (E.prog x h i) (decapsHq eC eKa Hq (E.point x i))) (E.stop x h i)
    (E.final x h i) (E.final_conjTranspose x h i) (E.final_mul_self x h i)

omit [Fintype C] [DecidableEq K] [Fintype K] [Fintype ι] [NeZero n] in
theorem auxRunAdv_U_dependsOn (h : K) (i : ι) (j : Fin (E.stop x h i + 1)) :
    EntriesDependOnAtMost k (fun Hq => ((auxRunAdv eC eKa E x h Hq i).U j :
      Matrix (Fin ((m₁ + m₂) * n * ancW c k W)) (Fin ((m₁ + m₂) * n * ancW c k W)) ℂ)) :=
  (flatten_family_dependsOn (fun Hq => decapsHq eC eKa Hq (E.point x i))
    (readsOne_decapsHq eC eKa (E.point x i)) k (fun _ => (E.prog x h i).toMRH)
    (E.prog x h i).rounds 0 (fun _ => rfl) (fun _ => EntriesDependOnAtMost.const 0 _)
    (fun _ _ => EntriesDependOnAtMost.const 0 _) _).mono (by omega)

omit [Fintype C] [DecidableEq K] [Fintype K] [Fintype ι] [NeZero n] in
theorem auxRunAdv_init (h : K) (Hq Hq' : C → K) (i : ι) :
    (auxRunAdv eC eKa E x h Hq i).init = (auxRunAdv eC eKa E x h Hq' i).init :=
  flatten_init_eq _ _ k _ _ rfl

omit [DecidableEq K] [Fintype PK] [Fintype SK] [Fintype M] [DecidableEq M] [Nonempty M]
  [Fintype Z] [Fintype K] [Fintype R] [Fintype C] [Fintype ι] in
theorem kWiseInvariant_qAuxRun_G (Hq : C → K) (J : Fin m₂ → Fin n) (T : C → Fin n) (z : Z)
    (i : ι) : KWiseInvariant (auxDeg q k)
      (fun G => qAuxRun S hpk eG eJ eKR eC eKa key E x Hq G J T z i) :=
  kWiseInvariant_prOut_family (fun _ => auxRunAdv eC eKa E x (Hq (E.point x i)) Hq i)
    (fun G => auxOracle S hpk eG eJ eKR (key x) Hq G J T z)
    (readsOne_auxOracle_G S hpk eG eJ eKR (key x) Hq J T z) 0
    (fun _ => EntriesDependOnAtMost.const 0 _) _ _ (fun _ => rfl) (fun _ => rfl)
    ((Nat.le_add_left _ 1).trans (le_auxDeg (E.stop x _ i).isLt.le (Nat.zero_le k)))

omit [DecidableEq K] [Fintype PK] [Fintype SK] [Fintype M] [DecidableEq M] [Nonempty M]
  [Fintype Z] [Fintype K] [Fintype R] [Fintype C] [Fintype ι] in
theorem kWiseInvariant_qAuxRun_J (Hq : C → K) (G : Fin m₁ → Fin n) (T : C → Fin n) (z : Z)
    (i : ι) : KWiseInvariant (auxDeg q k)
      (fun J => qAuxRun S hpk eG eJ eKR eC eKa key E x Hq G J T z i) :=
  kWiseInvariant_prOut_family (fun _ => auxRunAdv eC eKa E x (Hq (E.point x i)) Hq i)
    (fun J => auxOracle S hpk eG eJ eKR (key x) Hq G J T z)
    (readsOne_auxOracle_J S hpk eG eJ eKR (key x) Hq G T z) 0
    (fun _ => EntriesDependOnAtMost.const 0 _) _ _ (fun _ => rfl) (fun _ => rfl)
    ((Nat.le_add_left _ 1).trans (le_auxDeg (E.stop x _ i).isLt.le (Nat.zero_le k)))

omit [DecidableEq K] [Fintype PK] [Fintype SK] [Fintype M] [DecidableEq M] [Nonempty M]
  [Fintype Z] [Fintype K] [Fintype R] [Fintype ι] in
theorem kWiseInvariant_qAuxRun_T (Hq : C → K) (G : Fin m₁ → Fin n) (J : Fin m₂ → Fin n) (z : Z)
    (i : ι) : KWiseInvariant (auxDeg q k)
      (fun T => qAuxRun S hpk eG eJ eKR eC eKa key E x Hq G J T z i) :=
  kWiseInvariant_prOut_family (fun _ => auxRunAdv eC eKa E x (Hq (E.point x i)) Hq i)
    (fun T => auxOracle S hpk eG eJ eKR (key x) Hq G J T z)
    (readsOne_auxOracle_T S hpk eG eJ eKR (key x) Hq G J z) 0
    (fun _ => EntriesDependOnAtMost.const 0 _) _ _ (fun _ => rfl) (fun _ => rfl)
    ((Nat.le_add_left _ 1).trans (le_auxDeg (E.stop x _ i).isLt.le (Nat.zero_le k)))

omit [Fintype PK] [Fintype SK] [Fintype M] [DecidableEq M] [Nonempty M] [Fintype Z]
  [Fintype R] [Fintype ι] in
theorem kWiseInvariant_qAuxRun_Hq (G : Fin m₁ → Fin n) (J : Fin m₂ → Fin n) (T : C → Fin n)
    (z : Z) (i : ι) : KWiseInvariant (auxDeg q k)
      (fun Hq => qAuxRun S hpk eG eJ eKR eC eKa key E x Hq G J T z i) := by
  set p := E.point x i
  have e : (fun Hq => qAuxRun S hpk eG eJ eKR eC eKa key E x Hq G J T z i) = fun Hq =>
      ∑ h : K, ENNReal.ofReal (((if Hq p = h then (1 : ℂ) else 0) *
        prOutC (auxRunAdv eC eKa E x h Hq i)
          (auxOracle S hpk eG eJ eKR (key x) Hq G J T z))).re := by
    funext Hq
    rw [Finset.sum_eq_single (Hq p)]
    · rw [ite_eq_left rfl, one_mul, ← prOut_eq_ofReal_re]
      rfl
    · intro h _ hh
      rw [ite_eq_right (Ne.symm hh), zero_mul, Complex.zero_re, ENNReal.ofReal_zero]
    · intro hn
      exact absurd (Finset.mem_univ _) hn
  rw [e]
  refine KWiseInvariant.sum Finset.univ _ fun h _ => ?_
  have hind : DependsOnAtMost 1 (fun Hq : C → K => if Hq p = h then (1 : ℂ) else 0) :=
    DependsOnAtMost.of_localOn (S := {p}) (by simp) fun H H' hH => by
      simp only [hH p (Finset.mem_singleton_self p)]
  have hrun := prOutC_family_dependsOn (fun Hq => auxRunAdv eC eKa E x h Hq i)
    (fun Hq => auxOracle S hpk eG eJ eKR (key x) Hq G J T z)
    (readsOne_auxOracle_Hq S hpk eG eJ eKR (key x) G J T z) k
    (auxRunAdv_U_dependsOn eC eKa E x h i) (auxRunAdv eC eKa E x h (fun _ => h) i).init.val
    (E.final x h i) (fun Hq => congrArg (fun D => D.val) (auxRunAdv_init eC eKa E x h _ _ i))
    (fun _ => rfl)
  refine (KWiseInvariant.of_dependsOn (hind.mul hrun le_rfl) fun Hq => ?_).mono
    (le_auxDeg (E.stop x h i).isLt.le le_rfl)
  split_ifs
  · rw [one_mul]; exact prOutC_re_nonneg _ _
  · simp

variable {ΩG ΩJ ΩH ΩT : Type} [Fintype ΩG] [Nonempty ΩG] [Fintype ΩJ] [Nonempty ΩJ]
  [Fintype ΩH] [Nonempty ΩH] [Fintype ΩT] [Nonempty ΩT]
  (ΦG : ΩG → Fin m₁ → Fin n) (ΦJ : ΩJ → Fin m₂ → Fin n) (ΦH : ΩH → C → K)
  (ΦT : ΩT → C → Fin n)

omit [Fintype PK] [Fintype SK] [Fintype M] [DecidableEq M] [Nonempty M] [Fintype R]
  [Fintype ι] in
/-- The uniform average over the tables `G`, `J`, `Hq`, `T` of one run of a
distinguisher equals its average over seeded families that are
`auxDeg q k`-wise independent. -/
theorem tabAvg5_qAuxRun_eq_push (hG : KWiseIndep (auxDeg q k) (pushWeight ΦG))
    (hJ : KWiseIndep (auxDeg q k) (pushWeight ΦJ)) (hH : KWiseIndep (auxDeg q k) (pushWeight ΦH))
    (hT : KWiseIndep (auxDeg q k) (pushWeight ΦT)) (i : ι) :
    tabAvg5 (fun z G J Hq T => qAuxRun S hpk eG eJ eKR eC eKa key E x Hq G J T z i) =
      ∑ z : Z, (Fintype.card Z : ℝ≥0∞)⁻¹ *
        ∑ ωG, (Fintype.card ΩG : ℝ≥0∞)⁻¹ * ∑ ωJ, (Fintype.card ΩJ : ℝ≥0∞)⁻¹ *
          ∑ ωH, (Fintype.card ΩH : ℝ≥0∞)⁻¹ * ∑ ωT, (Fintype.card ΩT : ℝ≥0∞)⁻¹ *
            qAuxRun S hpk eG eJ eKR eC eKa key E x (ΦH ωH) (ΦG ωG) (ΦJ ωJ) (ΦT ωT) z i := by
  unfold tabAvg5
  refine Finset.sum_congr rfl fun z _ => congrArg _ ?_
  refine (KWiseInvariant.push ?_ ΦG hG).symm.trans ?_
  · exact KWiseInvariant.avg _ fun J => KWiseInvariant.avg _ fun Hq => KWiseInvariant.avg _
      fun T => kWiseInvariant_qAuxRun_G S hpk eG eJ eKR eC eKa key E x Hq J T z i
  refine Finset.sum_congr rfl fun ωG _ => congrArg _ ?_
  refine (KWiseInvariant.push ?_ ΦJ hJ).symm.trans ?_
  · exact KWiseInvariant.avg _ fun Hq => KWiseInvariant.avg _
      fun T => kWiseInvariant_qAuxRun_J S hpk eG eJ eKR eC eKa key E x Hq (ΦG ωG) T z i
  refine Finset.sum_congr rfl fun ωJ _ => congrArg _ ?_
  refine (KWiseInvariant.push ?_ ΦH hH).symm.trans ?_
  · exact KWiseInvariant.avg _
      fun T => kWiseInvariant_qAuxRun_Hq S hpk eG eJ eKR eC eKa key E x (ΦG ωG) (ΦJ ωJ) T z i
  refine Finset.sum_congr rfl fun ωH _ => congrArg _ ?_
  exact (KWiseInvariant.push
    (kWiseInvariant_qAuxRun_T S hpk eG eJ eKR eC eKa key E x (ΦH ωH) (ΦG ωG) (ΦJ ωJ) z i)
    ΦT hT).symm

end AuxBase

/-! ## Module-LWE against quantum distinguishers without oracle access -/

section Std

/-- A uniform average over a product is the nested uniform average. -/
theorem sum_prod_uniform {α β : Type} [Fintype α] [Fintype β] (f : α × β → ℝ≥0∞) :
    ∑ p, (Fintype.card (α × β) : ℝ≥0∞)⁻¹ * f p =
      ∑ a, (Fintype.card α : ℝ≥0∞)⁻¹ * ∑ b, (Fintype.card β : ℝ≥0∞)⁻¹ * f (a, b) := by
  rw [Fintype.sum_prod_type, Fintype.card_prod, Nat.cast_mul,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun b _ => mul_assoc _ _ _

variable {m n w : ℕ} [NeZero n]

/-- A quantum distinguisher on a classical input in `X` with coins in `ι` and
no oracle access: from the input and its coins, an adversary that makes no
oracle call. -/
abbrev QStdDist (ι X : Type) (m n w : ℕ) : Type := X → ι → QAdv m n w 0

/-- The acceptance probability of an adversary that makes no oracle call,
evaluated at the constant table, which it does not read (`prOut_absorbOracle`). -/
def prOut0 (A : QAdv m n w 0) : ℝ≥0∞ := prOut A fun _ => 0

/-- The probability that `E` outputs `1` on input `x`, its coins uniform. -/
def qStdAcc {ι X : Type} [Fintype ι] (E : QStdDist ι X m n w) (x : X) : ℝ≥0∞ :=
  ∑ i : ι, (Fintype.card ι : ℝ≥0∞)⁻¹ * prOut0 (E x i)

variable (B : CatCrypt.Crypto.MLKEM.MLWE_PKE_Basic.Params)

/-- The module-LWE advantage of a quantum distinguisher without oracle access:
`|Pr[1 | real] - Pr[1 | uniform]|` on the sample `(A, t)` of `mlweSample`. -/
def qMLWE {ι : Type} [Fintype ι]
    (E : QStdDist ι (CatCrypt.Crypto.MLKEM.MLWE_PKE_Basic.PK B) m n w) : ℝ≥0∞ :=
  absDiff (sdExp (mlweSample B false) (qStdAcc E)) (sdExp (mlweSample B true) (qStdAcc E))

/-- The extended module-LWE advantage of a quantum distinguisher without oracle
access, on the sample `(A, t, u, v)` of `extSample`. -/
def qMLWEExt {ι : Type} [Fintype ι] (E : QStdDist ι (B.Mat × B.Vec × B.Vec × B.R) m n w) :
    ℝ≥0∞ :=
  absDiff (sdExp (extSample B false) (qStdAcc E)) (sdExp (extSample B true) (qStdAcc E))

end Std

section Red

open CatCrypt.Crypto.PKE.Games (Scheme)

variable {m₁ m₂ n W q k c a : ℕ} {PK SK M C R K Hash Z ι X : Type}
  [DecidableEq Z] [Nonempty K] [DecidableEq C] [DecidableEq Hash]
  (S : Scheme PK SK M C R) (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁) (eJ : (Z × C) ≃ Fin m₂)
  (eKR : (K × R) ≃ Fin n) (eC : C ≃ Fin c) (eKa : K ≃ Fin a) [NeZero n] [NeZero c]
  (key : X → PK)
  {ΩG ΩJ ΩH ΩT : Type} (ΦG : ΩG → Fin m₁ → Fin n) (ΦJ : ΩJ → Fin m₂ → Fin n)
  (ΦH : ΩH → C → K) (ΦT : ΩT → C → Fin n)

/-- The reduction that samples its own oracles: with coins
`(i, z, ωG, ωJ, ωH, ωT)` it forms the tables `G = ΦG ωG`, `J = ΦJ ωJ`,
`Hq = ΦH ωH`, `T = ΦT ωT`, and runs `E` with coins `i` on input `x`, answering
its oracle calls by `auxOracle` at the public key `key x`, its decapsulation
queries by `decapsHq Hq` and its key query by `Hq`, all computed from the
tables. -/
def qRedSamp (E : QAuxDist ι X (m₁ + m₂) n W q k c a C K) :
    QStdDist (ι × Z × ΩG × ΩJ × ΩH × ΩT) X (m₁ + m₂) n (ancW c k W) :=
  fun x s => absorbOracle
    (auxRunAdv eC eKa E x (ΦH s.2.2.2.2.1 (E.point x s.1)) (ΦH s.2.2.2.2.1) s.1)
    (auxOracle S hpk eG eJ eKR (key x) (ΦH s.2.2.2.2.1) (ΦG s.2.2.1) (ΦJ s.2.2.2.1)
      (ΦT s.2.2.2.2.2) s.2.1)

/-- One run of the self-sampling reduction is one run of the distinguisher
against the sampled tables. -/
theorem prOut0_qRedSamp (E : QAuxDist ι X (m₁ + m₂) n W q k c a C K) (x : X) (i : ι) (z : Z)
    (ωG : ΩG) (ωJ : ΩJ) (ωH : ΩH) (ωT : ΩT) :
    prOut0 (qRedSamp S hpk eG eJ eKR eC eKa key ΦG ΦJ ΦH ΦT E x (i, z, ωG, ωJ, ωH, ωT)) =
      qAuxRun S hpk eG eJ eKR eC eKa key E x (ΦH ωH) (ΦG ωG) (ΦJ ωJ) (ΦT ωT) z i :=
  prOut_absorbOracle _ _ _

variable [Fintype ι] [Fintype Z] [Fintype C] [Fintype K] [DecidableEq K]
  [Fintype ΩG] [Nonempty ΩG] [Fintype ΩJ] [Nonempty ΩJ]
  [Fintype ΩH] [Nonempty ΩH] [Fintype ΩT] [Nonempty ΩT]

/-- The acceptance probability of the self-sampling reduction is that of the
distinguisher with oracle access, when each family is `auxDeg q k`-wise
independent. -/
theorem qStdAcc_qRedSamp (E : QAuxDist ι X (m₁ + m₂) n W q k c a C K)
    (hG : KWiseIndep (auxDeg q k) (pushWeight ΦG)) (hJ : KWiseIndep (auxDeg q k) (pushWeight ΦJ))
    (hH : KWiseIndep (auxDeg q k) (pushWeight ΦH)) (hT : KWiseIndep (auxDeg q k) (pushWeight ΦT))
    (x : X) :
    qStdAcc (qRedSamp S hpk eG eJ eKR eC eKa key ΦG ΦJ ΦH ΦT E) x =
      qAuxAcc S hpk eG eJ eKR eC eKa key E x := by
  unfold qStdAcc qAuxAcc
  simp only [sum_prod_uniform]
  refine Finset.sum_congr rfl fun i _ => congrArg _ ?_
  rw [tabAvg5_qAuxRun_eq_push S hpk eG eJ eKR eC eKa key E x ΦG ΦJ ΦH ΦT hG hJ hH hT i]
  simp only [prOut0_qRedSamp]

end Red

section RedMLWE

open CatCrypt.Crypto.PKE.Games (Scheme)
open CatCrypt.Crypto.MLKEM

variable {m₁ m₂ n W q k c a : ℕ} {SK C R K Hash Z ι : Type}
  [Fintype Z] [DecidableEq Z] [Fintype K] [Nonempty K] [DecidableEq K] [Fintype C]
  [DecidableEq C] [DecidableEq Hash] [Fintype ι]
  (B : MLWE_PKE_Basic.Params) (S : Scheme (MLWE_PKE_Basic.PK B) SK B.PT C R)
  (hpk : MLWE_PKE_Basic.PK B → Hash) (eG : (B.PT × Hash) ≃ Fin m₁)
  (eJ : (Z × C) ≃ Fin m₂) (eKR : (K × R) ≃ Fin n) (eC : C ≃ Fin c) (eKa : K ≃ Fin a)
  [NeZero n] [NeZero c]
  {ΩG ΩJ ΩH ΩT : Type} [Fintype ΩG] [Nonempty ΩG] [Fintype ΩJ] [Nonempty ΩJ]
  [Fintype ΩH] [Nonempty ΩH] [Fintype ΩT] [Nonempty ΩT]
  (ΦG : ΩG → Fin m₁ → Fin n) (ΦJ : ΩJ → Fin m₂ → Fin n) (ΦH : ΩH → C → K)
  (ΦT : ΩT → C → Fin n)

/-- Module-LWE with oracle access is standard module-LWE against the reduction
that samples its oracles from `auxDeg q k`-wise independent families. -/
theorem qMLWEAux_eq_qMLWE (E : QAuxDist ι (MLWE_PKE_Basic.PK B) (m₁ + m₂) n W q k c a C K)
    (hG : KWiseIndep (auxDeg q k) (pushWeight ΦG)) (hJ : KWiseIndep (auxDeg q k) (pushWeight ΦJ))
    (hH : KWiseIndep (auxDeg q k) (pushWeight ΦH)) (hT : KWiseIndep (auxDeg q k) (pushWeight ΦT)) :
    qMLWEAux B S hpk eG eJ eKR eC eKa E =
      qMLWE B (qRedSamp S hpk eG eJ eKR eC eKa id ΦG ΦJ ΦH ΦT E) := by
  unfold qMLWEAux qMLWE
  rw [funext (qStdAcc_qRedSamp S hpk eG eJ eKR eC eKa id ΦG ΦJ ΦH ΦT E hG hJ hH hT)]

/-- Extended module-LWE with oracle access is standard extended module-LWE
against the reduction that samples its oracles from `auxDeg q k`-wise
independent families. -/
theorem qMLWEExtAux_eq_qMLWEExt
    (E : QAuxDist ι (B.Mat × B.Vec × B.Vec × B.R) (m₁ + m₂) n W q k c a C K)
    (hG : KWiseIndep (auxDeg q k) (pushWeight ΦG)) (hJ : KWiseIndep (auxDeg q k) (pushWeight ΦJ))
    (hH : KWiseIndep (auxDeg q k) (pushWeight ΦH)) (hT : KWiseIndep (auxDeg q k) (pushWeight ΦT)) :
    qMLWEExtAux B S hpk eG eJ eKR eC eKa E =
      qMLWEExt B (qRedSamp S hpk eG eJ eKR eC eKa (fun x => (x.1, x.2.1)) ΦG ΦJ ΦH ΦT E) := by
  unfold qMLWEExtAux qMLWEExt
  rw [funext (qStdAcc_qRedSamp S hpk eG eJ eKR eC eKa (fun x => (x.1, x.2.1)) ΦG ΦJ ΦH ΦT E
    hG hJ hH hT)]

end RedMLWE

/-! ## Polynomial oracles for the auxiliary tables -/

/-- A polynomial oracle on tables `D → R`: a finite field `F`, an injection
`ι : D → F` and a balanced `π : F → R`. -/
structure PolyData (D R : Type) [Fintype R] [DecidableEq R] where
  /-- The field of the coefficients. -/
  F : Type
  [field : Field F]
  [fintype : Fintype F]
  [decEq : DecidableEq F]
  /-- The encoding of the domain in the field. -/
  ι : D → F
  ι_injective : Function.Injective ι
  /-- The map from the field onto the range. -/
  π : F → R
  π_balanced : Balanced π

attribute [instance] PolyData.field PolyData.fintype PolyData.decEq

namespace PolyData

variable {D R : Type} [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R]

/-- The table of the polynomial with coefficient vector `cf` of length `k`. -/
def table (P : PolyData D R) (k : ℕ) : (Fin k → P.F) → D → R := polyTable P.ι P.π k

theorem kWise (P : PolyData D R) (k : ℕ) : KWiseIndep k (pushWeight (P.table k)) :=
  polyOracle_kWise k P.ι P.ι_injective P.π P.π_balanced

omit [Fintype D] [DecidableEq D] in
/-- The first component of an equivalence `F ≃ R × T` is balanced. -/
theorem balanced_of_equiv {F T : Type} [Fintype F] [Fintype T] (e : F ≃ R × T) :
    Balanced fun y => (e y).1 := by
  intro r
  have h1 : (Finset.univ.filter fun y => (e y).1 = r).card = Fintype.card T := by
    rw [← Finset.card_map e.toEmbedding]
    have : (Finset.univ.filter fun y => (e y).1 = r).map e.toEmbedding =
        (Finset.univ : Finset T).map ⟨fun t => (r, t), fun _ _ h => (Prod.mk.inj h).2⟩ := by
      ext ⟨r', t⟩
      simp only [Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and,
        Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨y, hy, he⟩
        exact ⟨t, by rw [← hy, he]; rfl⟩
      · rintro ⟨t', ht'⟩
        exact ⟨e.symm (r', t),
          by simp only [Equiv.apply_symm_apply]; exact (Prod.mk.inj ht').1.symm, by simp⟩
    rw [this, Finset.card_map, Finset.card_univ]
  rw [h1, Fintype.card_congr e, Fintype.card_prod, Nat.mul_comm]

omit [DecidableEq D] in
/-- A polynomial oracle over the Galois field of order `p ^ N`: it exists when
the domain has at most `p ^ N` elements and the range has `p ^ M` elements
with `M ≤ N`. -/
theorem nonempty_galois (p N M : ℕ) [Fact p.Prime] (hN : N ≠ 0) (hD : Fintype.card D ≤ p ^ N)
    (hR : Fintype.card R = p ^ M) (hMN : M ≤ N) : Nonempty (PolyData D R) := by
  classical
  let _ : Fintype (GaloisField p N) := Fintype.ofFinite _
  have hF : Fintype.card (GaloisField p N) = p ^ N := by
    rw [← Nat.card_eq_fintype_card, GaloisField.card p N hN]
  obtain ⟨f⟩ : Nonempty (D ↪ GaloisField p N) :=
    Function.Embedding.nonempty_of_card_le (hD.trans hF.ge)
  have hc : Fintype.card (GaloisField p N) = Fintype.card (R × Fin (p ^ (N - M))) := by
    rw [hF, Fintype.card_prod, hR, Fintype.card_fin, ← pow_add, Nat.add_sub_cancel' hMN]
  let e := Fintype.equivOfCardEq hc
  exact Nonempty.intro (PolyData.mk (F := GaloisField p N) f f.injective (fun y => (e y).1)
    (balanced_of_equiv e))

end PolyData

section RedPoly

open CatCrypt.Crypto.PKE.Games (Scheme)
open CatCrypt.Crypto.MLKEM

variable {m₁ m₂ n W q k c a : ℕ} {SK C R K Hash Z ι : Type}
  [Fintype Z] [DecidableEq Z] [Fintype K] [Nonempty K] [DecidableEq K] [Fintype C]
  [DecidableEq C] [DecidableEq Hash] [Fintype ι]
  (B : MLWE_PKE_Basic.Params) (S : Scheme (MLWE_PKE_Basic.PK B) SK B.PT C R)
  (hpk : MLWE_PKE_Basic.PK B → Hash) (eG : (B.PT × Hash) ≃ Fin m₁)
  (eJ : (Z × C) ≃ Fin m₂) (eKR : (K × R) ≃ Fin n) (eC : C ≃ Fin c) (eKa : K ≃ Fin a)
  [NeZero n] [NeZero c]
  (PG : PolyData (Fin m₁) (Fin n)) (PJ : PolyData (Fin m₂) (Fin n)) (PH : PolyData C K)
  (PT : PolyData C (Fin n))

/-- The reduction with polynomial oracles: it draws `auxDeg q k` coefficients in
the field of each table, evaluates the four polynomials to answer the oracle,
decapsulation and key queries of `E`, and runs `E`. -/
def qRedPoly {X : Type} (key : X → MLWE_PKE_Basic.PK B)
    (E : QAuxDist ι X (m₁ + m₂) n W q k c a C K) :=
  qRedSamp S hpk eG eJ eKR eC eKa key (PG.table (auxDeg q k)) (PJ.table (auxDeg q k))
    (PH.table (auxDeg q k)) (PT.table (auxDeg q k)) E

/-- **Module-LWE with oracle access is standard quantum module-LWE.** The
advantage of a distinguisher with the auxiliary oracles equals the standard
advantage of the reduction that evaluates polynomials of degree
`< auxDeg q k` in place of the oracles.

References: Zhandry, "Secure identity-based encryption in the quantum random
oracle model", CRYPTO 2012, ePrint 2012/076, Theorem 6.1 (a quantum random
oracle queried `q` times is simulated exactly by a `2q`-wise independent
function). -/
theorem qMLWEAux_eq_qMLWE_qRedPoly
    (E : QAuxDist ι (MLWE_PKE_Basic.PK B) (m₁ + m₂) n W q k c a C K) :
    qMLWEAux B S hpk eG eJ eKR eC eKa E =
      qMLWE B (qRedPoly B S hpk eG eJ eKR eC eKa PG PJ PH PT id E) :=
  qMLWEAux_eq_qMLWE B S hpk eG eJ eKR eC eKa _ _ _ _ E (PG.kWise _) (PJ.kWise _) (PH.kWise _)
    (PT.kWise _)

/-- **Extended module-LWE with oracle access is standard extended quantum
module-LWE**, against the reduction with polynomial oracles. -/
theorem qMLWEExtAux_eq_qMLWEExt_qRedPoly
    (E : QAuxDist ι (B.Mat × B.Vec × B.Vec × B.R) (m₁ + m₂) n W q k c a C K) :
    qMLWEExtAux B S hpk eG eJ eKR eC eKa E =
      qMLWEExt B (qRedPoly B S hpk eG eJ eKR eC eKa PG PJ PH PT (fun x => (x.1, x.2.1)) E) :=
  qMLWEExtAux_eq_qMLWEExt B S hpk eG eJ eKR eC eKa _ _ _ _ E (PG.kWise _) (PJ.kWise _)
    (PH.kWise _) (PT.kWise _)

end RedPoly

/-! ## ML-KEM-512 under quantum module-LWE and extended module-LWE without oracle access -/

section MLKEM512

open CatCrypt.Crypto.MLKEM CatCrypt.Crypto.MLKEM.FIPS203QROMQuantumMLWE
open MLKEM512Instance (mlkem512Params)
open CompressedPKE (MLKEM512CT mlkem512Compress mlkem512CompressedScheme)
open MLWE_PKE_Basic (PK)

variable {m₁ m₂ n w q k c a : ℕ} {K Hash Z : Type} [Fintype Z] [Nonempty Z] [DecidableEq Z]
  [Fintype K] [Nonempty K] [DecidableEq Hash]
  (hpk : PK mlkem512Params.toBasic → Hash) (eG : (mlkem512Params.PT × Hash) ≃ Fin m₁)
  (eJ : (Z × MLKEM512CT) ≃ Fin m₂) (eKR : (K × mlkem512Params.Seed) ≃ Fin n)
  (eC : MLKEM512CT ≃ Fin c) (eKa : K ≃ Fin a) [NeZero n] [NeZero c]

open scoped Classical in
/-- `qMLWEBound` with each module-LWE advantage with oracle access replaced by
the standard quantum module-LWE advantage of the reduction `qRedPoly` with
polynomial oracles `PG`, `PJ`, `PH`, `PT`. -/
def qMLWEStdBound (PG : PolyData (Fin m₁) (Fin n)) (PJ : PolyData (Fin m₂) (Fin n))
    (PH : PolyData MLKEM512CT K) (PT : PolyData MLKEM512CT (Fin n))
    (A : KEMQAdv m₁ m₂ n w q k c a (PK mlkem512Params.toBasic) MLKEM512CT K) (b : Bool) :
    ℝ≥0∞ :=
  qMLWE mlkem512Params.toBasic (qRedPoly mlkem512Params.toBasic mlkem512CompressedScheme hpk eG
      eJ eKR eC eKa PG PJ PH PT id
      (qRedEnc mlkem512CompressedScheme (indRed eG (owRedQuery A b)) true)) +
    qMLWEExt mlkem512Params.toBasic (qRedPoly mlkem512Params.toBasic mlkem512CompressedScheme
      hpk eG eJ eKR eC eKa PG PJ PH PT (fun x => (x.1, x.2.1))
      (qRedExt mlkem512Params.toBasic mlkem512Compress (indRed eG (owRedQuery A b)) true)) +
    qMLWEExt mlkem512Params.toBasic (qRedPoly mlkem512Params.toBasic mlkem512CompressedScheme
      hpk eG eJ eKR eC eKa PG PJ PH PT (fun x => (x.1, x.2.1))
      (qRedExt mlkem512Params.toBasic mlkem512Compress (indRed eG (owRedQuery A b)) false)) +
    qMLWE mlkem512Params.toBasic (qRedPoly mlkem512Params.toBasic mlkem512CompressedScheme hpk eG
      eJ eKR eC eKa PG PJ PH PT id
      (qRedEnc mlkem512CompressedScheme (indRed eG (owRedQuery A b)) false)) +
    (Fintype.card mlkem512Params.PT : ℝ≥0∞)⁻¹ + corrErr mlkem512CompressedScheme

omit [Nonempty Z] in
open scoped Classical in
theorem qMLWEBound_eq_qMLWEStdBound (PG : PolyData (Fin m₁) (Fin n))
    (PJ : PolyData (Fin m₂) (Fin n)) (PH : PolyData MLKEM512CT K)
    (PT : PolyData MLKEM512CT (Fin n))
    (A : KEMQAdv m₁ m₂ n w q k c a (PK mlkem512Params.toBasic) MLKEM512CT K) (b : Bool) :
    qMLWEBound hpk eG eJ eKR eC eKa A b = qMLWEStdBound hpk eG eJ eKR eC eKa PG PJ PH PT A b := by
  unfold qMLWEBound qMLWEStdBound
  rw [qMLWEAux_eq_qMLWE_qRedPoly, qMLWEAux_eq_qMLWE_qRedPoly, qMLWEExtAux_eq_qMLWEExt_qRedPoly,
    qMLWEExtAux_eq_qMLWEExt_qRedPoly]

variable [NeZero a] [NeZero (flatQ q k q)] [NeZero (m₁ + m₂)]

open scoped Classical in
/-- **The FIPS 203 Fujisaki–Okamoto KEM over the idealised ML-KEM-512 K-PKE against
every quantum adversary with `k` decapsulation rounds, under quantum module-LWE and
extended module-LWE without oracle access.** The bound of
`mlkem512_qindcca_qmlwe_coll` with each one-wayness term `qMLWEStdBound`:
module-LWE and extended module-LWE advantages, without oracle access, of the
reductions `qRedPoly` that answer the auxiliary oracles by polynomials drawn from
`PG`, `PJ`, `PH`, `PT` (`PolyData.nonempty_galois` supplies these over a Galois
field when each range has prime-power size and each domain fits in the field);
`ε` bounds the coin-collision weight of the scheme. -/
theorem mlkem512_qindcca_qmlwe_std (PG : PolyData (Fin m₁) (Fin n))
    (PJ : PolyData (Fin m₂) (Fin n)) (PH : PolyData MLKEM512CT K)
    (PT : PolyData MLKEM512CT (Fin n))
    (A : KEMQAdv m₁ m₂ n w q k c a (PK mlkem512Params.toBasic) MLKEM512CT K)
    (ε : ℝ≥0∞) (hcoll : collWeight mlkem512CompressedScheme ≤ ε)
    (hcoin : ∀ pk sk, mlkem512CompressedScheme.keygen (pk, sk) ≠ 0 → ∀ m, ∃ ρ,
      mlkem512CompressedScheme.dec sk (mlkem512CompressedScheme.enc pk m ρ) = some m)
    (lam : PK mlkem512Params.toBasic × MLWE_PKE_Basic.SK mlkem512Params.toBasic → ℝ≥0∞)
    (hlam : ∀ pk sk, mlkem512CompressedScheme.keygen (pk, sk) ≠ 0 → ∀ x,
      ((badVals (kemBad mlkem512CompressedScheme hpk eG eKR pk sk) x).card : ℝ≥0∞) /
        (n : ℝ≥0∞) ≤ lam (pk, sk)) :
    qINDCCAAdvantage mlkem512CompressedScheme hpk eG eJ eKR eC eKa A ≤
      (4 * ((flatQ q k q : ℝ≥0∞) * (4 * (flatQ q k q : ℝ≥0∞) *
          (qMLWEStdBound hpk eG eJ eKR eC eKa PG PJ PH PT (nfKEM A) true +
            ∑ i : KEMInput (PK mlkem512Params.toBasic) (MLWE_PKE_Basic.SK mlkem512Params.toBasic)
              Z mlkem512Params.PT K m₁ m₂ n, kemSample mlkem512CompressedScheme i * lam i.1))) ^
            (1 / 2 : ℝ) +
        (8 * (flatQ q k q : ℝ≥0∞) *
            (∑ i : KEMInput (PK mlkem512Params.toBasic) (MLWE_PKE_Basic.SK mlkem512Params.toBasic)
              Z mlkem512Params.PT K m₁ m₂ n, kemSample mlkem512CompressedScheme i * lam i.1) ^
              (1 / 2 : ℝ) +
          (∑ i : KEMInput (PK mlkem512Params.toBasic) (MLWE_PKE_Basic.SK mlkem512Params.toBasic)
              Z mlkem512Params.PT K m₁ m₂ n, kemSample mlkem512CompressedScheme i * lam i.1 +
            ε) +
          8 * (flatQ q k q : ℝ≥0∞) *
            (∑ i : KEMInput (PK mlkem512Params.toBasic) (MLWE_PKE_Basic.SK mlkem512Params.toBasic)
              Z mlkem512Params.PT K m₁ m₂ n, kemSample mlkem512CompressedScheme i * lam i.1) ^
              (1 / 2 : ℝ)) +
        4 * ((flatQ q k q : ℝ≥0∞) * (4 * (flatQ q k q : ℝ≥0∞) *
          (qMLWEStdBound hpk eG eJ eKR eC eKa PG PJ PH PT (nfKEM A) false +
            ∑ i : KEMInput (PK mlkem512Params.toBasic) (MLWE_PKE_Basic.SK mlkem512Params.toBasic)
              Z mlkem512Params.PT K m₁ m₂ n, kemSample mlkem512CompressedScheme i * lam i.1))) ^
            (1 / 2 : ℝ)) +
      2 * (8 * (flatQ q k q : ℝ≥0∞) * ((Fintype.card Z : ℝ≥0∞)⁻¹) ^ (1 / 2 : ℝ) +
        (8 * (flatQ (q + 4) k q : ℝ≥0∞) *
            (∑ i : KEMInput (PK mlkem512Params.toBasic) (MLWE_PKE_Basic.SK mlkem512Params.toBasic)
              Z mlkem512Params.PT K m₁ m₂ n, kemSample mlkem512CompressedScheme i * lam i.1) ^
              (1 / 2 : ℝ) +
          ∑ i : KEMInput (PK mlkem512Params.toBasic) (MLWE_PKE_Basic.SK mlkem512Params.toBasic)
              Z mlkem512Params.PT K m₁ m₂ n, kemSample mlkem512CompressedScheme i * lam i.1 +
          8 * (flatQ q k q : ℝ≥0∞) *
            (∑ i : KEMInput (PK mlkem512Params.toBasic) (MLWE_PKE_Basic.SK mlkem512Params.toBasic)
              Z mlkem512Params.PT K m₁ m₂ n, kemSample mlkem512CompressedScheme i * lam i.1) ^
              (1 / 2 : ℝ))) := by
  have h := mlkem512_qindcca_qmlwe_coll hpk eG eJ eKR eC eKa A ε hcoll hcoin lam hlam
  simp only [qMLWEBound_eq_qMLWEStdBound hpk eG eJ eKR eC eKa PG PJ PH PT] at h
  exact h

end MLKEM512

end CatCrypt.Quantum.QROM
