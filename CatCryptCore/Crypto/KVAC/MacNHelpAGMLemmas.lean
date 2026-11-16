/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Assumptions.KDL
public import CatCryptCore.ForMathlib.PMFUniform
public import CatCryptCore.Crypto.SPCompPMF
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.Algebra.MvPolynomial.Supported

/-!
# `MAC_n` in the algebraic group model: the algebraic lemma, the degree bound and `B_z`

The first part of the security proof of `MAC_n` with the helper oracle for algebraic adversaries
(`CatCrypt.Crypto.KVAC.MacNHelpAGM`), after Orrù 2024, Lemma 5.4.

## The algebraic lemma

The formal variables are the key `w, w', x0, x1, y_1, …, y_n` and the logarithms `u_k` of the
`U` components of the MAC answers (`Formal.Var`). Over a commutative ring `R` (the exponent
ring), with the logarithms `γ` of the parameters as numbers (`Formal.ParLog`), every element
the adversary receives has a polynomial: the generator `1`, a parameter its `γ`,
`C_W = γ_w w + γ_{w'} w'`, `I = γ_V - γ_0 x0 - γ_1 x1 - Σ γ_{y_i} y_i`, and for the `k`-th MAC
answer `U_k = u_k` and `V_k = γ_w w + u_k (x0 + t_k x1) + Σ y_i M_{k,i}`, where the attribute
`M_{k,i}` has the polynomial of its representation over the elements received before
(`Formal.basis`, `Formal.vPoly`, `Formal.mPoly`).

`Formal.forgery_poly_identity_not_fresh`: if the forgery `(M*, (t*, U*, V*))` satisfies the
verification equation `V* = γ_w w + U* (x0 + t* x1) + Σ y_i M*_i` as an identity of
polynomials, the `t_k` are pairwise distinct, `γ_w, γ_{w'}, γ_0 ≠ 0` and `γ_0 t* ≠ γ_1`, then the
forgery is the `j`-th MAC answer for some `j`: `t* = t_j` and `U*`, `V*`, `M*` have the
polynomials of `U_j`, `V_j`, `M_j`. The proof (`Formal.peel`) removes the largest index
`k` with a coefficient on `u_k`: the partial derivative in `u_k` of the identity, evaluated at
substitutions into `R[X]`, gives the coefficients (`Formal.peel_coeffs`), and the base elements
`1, C_W, I` are settled by `Formal.base_coeffs`.

## The degree bound

`simO_run_length`: against the oracle `simO` of `reductionAlg`, an adversary with at most
`q_m` MAC queries (`OracleAdv.IsQueryBoundBy macCost`) leaves a state whose polynomials in `χ`
have degree at most `q_m + 1` when the start state has degree at most `1`;
`forgeryPoly_length_le` bounds the forgery polynomial by degree `q_m + 2`.

## The reduction `B_z`

`reductionZ_bound`: the probability that an adversary wins suf-cmva-Help with
`t* = log_{G_{x0}} G_{x1}` (`zEventGame`) is at most the DL advantage of `reductionZ`, for a
generator `g ≠ 1`.

## References

* G. Fuchsbauer, E. Kiltz, J. Loss, *The Algebraic Group Model and its Applications*,
  CRYPTO 2018. <https://eprint.iacr.org/2017/620>
* M. Orrù, *Revisiting Keyed-Verification Anonymous Credentials*, 2024, Lemma 5.4.
  <https://eprint.iacr.org/2024/1552>
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.KVAC.MacNHelpAGM

/-! ## The algebraic lemma -/

namespace Formal

open MvPolynomial

/-- The formal variables: the key `w, w', x0, x1, (y_i)` and the logarithms `u_k` of the `U`
components of the MAC answers. -/
inductive Var (n : ℕ) where
  /-- `w`. -/
  | w
  /-- `w'`. -/
  | w'
  /-- `x0`. -/
  | x0
  /-- `x1`. -/
  | x1
  /-- `y_i`. -/
  | y (i : Fin n)
  /-- `u_k`. -/
  | u (k : ℕ)
  deriving DecidableEq

/-- The logarithms of the parameters `(G_w, G_{w'}, G_{x0}, G_{x1}, G_V, (G_{y_i}), (G_{m_i}))`. -/
structure ParLog (R : Type) (n : ℕ) where
  /-- `γ_w`. -/
  gw : R
  /-- `γ_{w'}`. -/
  gw' : R
  /-- `γ_0`. -/
  g0 : R
  /-- `γ_1`. -/
  g1 : R
  /-- `γ_V`. -/
  gV : R
  /-- `γ_{y_i}`. -/
  gy : Fin n → R
  /-- `γ_{m_i}`. -/
  gm : Fin n → R

variable {R : Type} [CommRing R] {n : ℕ}

/-- `x0 + s x1`. -/
noncomputable def lin (s : R) : MvPolynomial (Var n) R := X .x0 + C s * X .x1

/-- The polynomial of a representation `c` over the polynomials `B` of the received elements. -/
noncomputable def rep (B : List (MvPolynomial (Var n) R)) (c : List R) : MvPolynomial (Var n) R :=
  (List.zipWith (fun a b => C a * b) c B).sum

variable (γ : ParLog R n) (t : ℕ → R) (M : ℕ → Fin n → List R)

/-- `C_W = γ_w w + γ_{w'} w'`. -/
noncomputable def cwPoly : MvPolynomial (Var n) R := C γ.gw * X .w + C γ.gw' * X .w'

/-- `I = γ_V - γ_0 x0 - γ_1 x1 - Σ γ_{y_i} y_i`. -/
noncomputable def iPoly : MvPolynomial (Var n) R :=
  C γ.gV - C γ.g0 * X .x0 - C γ.g1 * X .x1 - ∑ i, C (γ.gy i) * X (.y i)

/-- The polynomials of the starting basis: the generator, the parameters, `C_W` and `I`. -/
noncomputable def basis0 : List (MvPolynomial (Var n) R) :=
  [1, C γ.gw, C γ.gw', C γ.g0, C γ.g1, C γ.gV] ++ List.ofFn (fun i => C (γ.gy i)) ++
    List.ofFn (fun i => C (γ.gm i)) ++ [cwPoly γ, iPoly γ]

/-- The polynomials of the elements received before the `k`-th MAC answer, for the MAC log
`(t_j, M_j)`: each answer appends `U_j = u_j` and `V_j`. -/
noncomputable def basis : ℕ → List (MvPolynomial (Var n) R)
  | 0 => basis0 γ
  | k + 1 => basis k ++ [X (.u k), C γ.gw * X .w + X (.u k) * lin (t k) +
      ∑ i, X (.y i) * rep (basis k) (M k i)]

/-- The polynomial of the attribute `M_{k,i}` of the `k`-th MAC query. -/
noncomputable def mPoly (k : ℕ) (i : Fin n) : MvPolynomial (Var n) R :=
  rep (basis γ t M k) (M k i)

/-- The polynomial `γ_w w + u_k (x0 + t_k x1) + Σ y_i M_{k,i}` of `V_k`. -/
noncomputable def vPoly (k : ℕ) : MvPolynomial (Var n) R :=
  C γ.gw * X .w + X (.u k) * lin (t k) + ∑ i, X (.y i) * mPoly γ t M k i

/-- Unfolding lemma of `basis` at a successor: the answer `k` appends `U_k` and `V_k`. -/
theorem basis_succ (k : ℕ) :
    basis γ t M (k + 1) = basis γ t M k ++ [X (.u k), vPoly γ t M k] := rfl

/-- The span of the polynomials received before the `k`-th MAC answer. -/
noncomputable def spanAt (k : ℕ) : Submodule R (MvPolynomial (Var n) R) :=
  Submodule.span R {p | p ∈ basis γ t M k}

/-- The variables other than the `u_j` with `j ≥ k`. -/
def early (k : ℕ) : Set (Var n) := {v | ∀ j, v = .u j → j < k}

variable {γ t M}

/-- The polynomial of a representation lies in the span of the basis. -/
theorem rep_mem (B : List (MvPolynomial (Var n) R)) (c : List R) :
    rep B c ∈ Submodule.span R {p | p ∈ B} := by
  induction B generalizing c with
  | nil => cases c <;> simp [rep]
  | cons b B ih =>
    cases c with
    | nil => simp [rep]
    | cons a c =>
      simp only [rep, List.zipWith_cons_cons, List.sum_cons]
      refine Submodule.add_mem _ ?_ ?_
      · rw [C_mul']
        exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
      · exact Submodule.span_mono (fun p hp => by simp_all) (ih c)

/-- A constant lies in every `supported` subalgebra. -/
theorem C_mem_supported (s : Set (Var n)) (a : R) : C a ∈ supported R s :=
  (supported R s).algebraMap_mem a

/-- A variable of `s` lies in `supported R s` (over any commutative ring). -/
theorem X_mem_supported_of_mem {s : Set (Var n)} {v : Var n} (hv : v ∈ s) :
    (X v : MvPolynomial (Var n) R) ∈ supported R s :=
  Algebra.subset_adjoin ⟨v, hv, rfl⟩

/-- The starting polynomials contain no `u_j`. -/
theorem basis0_mem (p : MvPolynomial (Var n) R) (hp : p ∈ basis0 γ) :
    p ∈ supported R (early 0) := by
  have hX : ∀ v : Var n, (∀ j, v ≠ .u j) → X v ∈ supported R (early 0) := fun v hv =>
    X_mem_supported_of_mem fun j hj => absurd hj (hv j)
  simp only [basis0, List.mem_append, List.mem_cons, List.mem_ofFn, List.not_mem_nil,
    or_false] at hp
  rcases hp with (((rfl | rfl | rfl | rfl | rfl | rfl) | ⟨i, rfl⟩) | ⟨i, rfl⟩) | rfl | rfl
  all_goals try first
    | exact Subalgebra.one_mem _
    | exact C_mem_supported _ _
  · exact Subalgebra.add_mem _ (Subalgebra.mul_mem _ (C_mem_supported _ _) (hX _ (by simp)))
      (Subalgebra.mul_mem _ (C_mem_supported _ _) (hX _ (by simp)))
  · refine Subalgebra.sub_mem _ (Subalgebra.sub_mem _ (Subalgebra.sub_mem _ (C_mem_supported _ _)
      (Subalgebra.mul_mem _ (C_mem_supported _ _) (hX _ (by simp))))
      (Subalgebra.mul_mem _ (C_mem_supported _ _) (hX _ (by simp)))) ?_
    exact Subalgebra.sum_mem _ fun i _ =>
      Subalgebra.mul_mem _ (C_mem_supported _ _) (hX _ (by simp))

/-- The polynomials received before the `k`-th MAC answer contain no `u_j` with `j ≥ k`. -/
theorem spanAt_le (k : ℕ) :
    spanAt γ t M k ≤ Subalgebra.toSubmodule (supported R (early k)) := by
  rw [spanAt, Submodule.span_le]
  induction k with
  | zero => exact fun p hp => basis0_mem p hp
  | succ k ih =>
    intro p hp
    rw [Set.mem_ofPred_eq, basis_succ] at hp
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
    have hmono : supported R (early (n := n) k) ≤ supported R (early (k + 1)) :=
      supported_mono fun v hv j hj => Nat.lt_succ_of_lt (hv j hj)
    have hk : ∀ i, mPoly γ t M k i ∈ supported R (early k) := fun i =>
      (Submodule.span_le.mpr ih) (rep_mem _ _)
    have hX : ∀ v : Var n, (∀ j, v ≠ .u j) → X v ∈ supported R (early (k + 1)) := fun v hv =>
      X_mem_supported_of_mem fun j hj => absurd hj (hv j)
    have hu : X (.u k) ∈ supported R (early (n := n) (k + 1)) :=
      X_mem_supported_of_mem fun j hj => by cases hj; omega
    rcases hp with hp | rfl | rfl
    · exact hmono (ih hp)
    · exact hu
    · refine Subalgebra.add_mem _ (Subalgebra.add_mem _
        (Subalgebra.mul_mem _ (C_mem_supported _ _) (hX _ (by simp)))
        (Subalgebra.mul_mem _ hu (Subalgebra.add_mem _ (hX _ (by simp))
          (Subalgebra.mul_mem _ (C_mem_supported _ _) (hX _ (by simp)))))) ?_
      exact Subalgebra.sum_mem _ fun i _ => Subalgebra.mul_mem _ (hX _ (by simp)) (hmono (hk i))

/-- A polynomial received before the `k`-th MAC answer does not depend on `u_k`. -/
theorem pderiv_eq_zero_of_mem {k : ℕ} {p : MvPolynomial (Var n) R} (hp : p ∈ spanAt γ t M k) :
    pderiv (Var.u k) p = 0 := by
  apply pderiv_eq_zero_of_notMem_vars
  intro h
  have := (mem_supported.mp (spanAt_le k hp)) h
  simp [early] at this

/-- `x0 + s x1` does not depend on `u_k`. -/
theorem pderiv_lin (k : ℕ) (s : R) : pderiv (Var.u k) (lin (n := n) s) = 0 := by
  simp [lin, pderiv_X]

/-- The partial derivative of `V_k` in `u_k` is `x0 + t_k x1`. -/
theorem pderiv_vPoly (k : ℕ) : pderiv (Var.u k) (vPoly γ t M k) = lin (t k) := by
  have hm : ∀ i, pderiv (Var.u k) (mPoly γ t M k i) = 0 := fun i =>
    pderiv_eq_zero_of_mem (rep_mem _ _)
  simp [vPoly, pderiv_lin, hm, pderiv_X]

/-- An element of the span after the `k`-th MAC answer is an element of the span before it
plus multiples of `U_k` and `V_k`. -/
theorem mem_spanAt_succ {k : ℕ} {p : MvPolynomial (Var n) R} (hp : p ∈ spanAt γ t M (k + 1)) :
    ∃ p' ∈ spanAt γ t M k, ∃ a b : R, p = p' + C a * X (.u k) + C b * vPoly γ t M k := by
  have hset : {q | q ∈ basis γ t M (k + 1)} =
      {q | q ∈ basis γ t M k} ∪ {X (.u k), vPoly γ t M k} := by
    ext q
    simp only [basis_succ, Set.mem_ofPred_eq, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, Set.mem_union, Set.mem_insert_iff, Set.mem_singleton_iff]
  rw [spanAt, hset, Submodule.span_union, Submodule.mem_sup] at hp
  obtain ⟨p', hp', z, hz, rfl⟩ := hp
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hz
  exact ⟨p', hp', a, b, by rw [C_mul', C_mul', add_assoc]⟩

/-- An element of the starting span is `a + c C_W + d I`. -/
theorem mem_spanAt_zero {p : MvPolynomial (Var n) R} (hp : p ∈ spanAt γ t M 0) :
    ∃ a c d : R, p = C a + C c * cwPoly γ + C d * iPoly γ := by
  induction hp using Submodule.span_induction with
  | mem x hx =>
    simp only [Set.mem_ofPred_eq, basis, basis0, List.mem_append, List.mem_cons, List.mem_ofFn,
      List.not_mem_nil, or_false] at hx
    rcases hx with (((rfl | rfl | rfl | rfl | rfl | rfl) | ⟨i, rfl⟩) | ⟨i, rfl⟩) | rfl | rfl
    · exact ⟨1, 0, 0, by simp⟩
    · exact ⟨γ.gw, 0, 0, by simp⟩
    · exact ⟨γ.gw', 0, 0, by simp⟩
    · exact ⟨γ.g0, 0, 0, by simp⟩
    · exact ⟨γ.g1, 0, 0, by simp⟩
    · exact ⟨γ.gV, 0, 0, by simp⟩
    · exact ⟨γ.gy i, 0, 0, by simp⟩
    · exact ⟨γ.gm i, 0, 0, by simp⟩
    · exact ⟨0, 1, 0, by simp⟩
    · exact ⟨0, 0, 1, by simp⟩
  | zero => exact ⟨0, 0, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, c, d, rfl⟩ := hx
    obtain ⟨a', c', d', rfl⟩ := hy
    exact ⟨a + a', c + c', d + d', by simp only [map_add]; ring⟩
  | smul r x _ hx =>
    obtain ⟨a, c, d, rfl⟩ := hx
    exact ⟨r * a, r * c, d * r, by simp only [smul_eq_C_mul, map_mul]; ring⟩

/-- Evaluate a polynomial identity at a substitution into `R[X]` and compare it with the goal. -/
local macro "eval_at " s:term " using " h:term : tactic => `(tactic| (
  have hh := congrArg (aeval $s) $h
  simp only [cwPoly, iPoly, lin, map_add, map_sub, map_mul, aeval_X, aeval_C,
    Polynomial.algebraMap_apply, Algebra.algebraMap_self, RingHom.id_apply, map_neg, map_sum,
    zero_mul, mul_zero, add_zero, zero_add, sub_zero, map_zero, Finset.sum_const_zero, ite_mul,
    mul_ite, Finset.sum_ite_eq', Finset.mem_univ, ite_true, mul_one] at hh ⊢
  linear_combination hh))

/-- Equal polynomials of degree at most `2` have equal coefficients. -/
theorem quad_eq {a b c a' b' c' : R}
    (h : Polynomial.C a + Polynomial.C b * Polynomial.X + Polynomial.C c * Polynomial.X ^ 2 =
      Polynomial.C a' + Polynomial.C b' * Polynomial.X + Polynomial.C c' * Polynomial.X ^ 2) :
    a = a' ∧ b = b' ∧ c = c' := by
  have h0 := congrArg (Polynomial.coeff · 0) h
  have h1 := congrArg (Polynomial.coeff · 1) h
  have h2 := congrArg (Polynomial.coeff · 2) h
  simp only [Polynomial.coeff_add, Polynomial.coeff_C_mul, Polynomial.coeff_C,
    Polynomial.coeff_X, Polynomial.coeff_X_pow] at h0 h1 h2
  simp_all

/-- **Coefficients of the peeled index.** The partial derivative in `u_k` of the verification
identity, compared at four substitutions into `R[X]`. -/
theorem peel_coeffs {tk ts aU aV bU bV : R} {mU mV : Fin n → R}
    (hD : C bU + C bV * lin tk =
      (C aU + C aV * lin tk) * lin ts + ∑ i, X (.y i) * (C (mU i) + C (mV i) * lin tk)) :
    bU = 0 ∧ bV = aU ∧ aV = 0 ∧ bV * tk = aU * ts ∧ (∀ i, mU i = 0) ∧ ∀ i, mV i = 0 := by
  have h1 := quad_eq (R := R) (a := bU) (b := bV) (c := 0) (a' := 0) (b' := aU) (c' := aV) (by
    eval_at (fun v : Var n => match v with | .x0 => (Polynomial.X : Polynomial R) | _ => 0)
      using hD)
  have h2 := quad_eq (R := R) (a := bU) (b := bV * tk) (c := 0) (a' := 0) (b' := aU * ts)
    (c' := aV * tk * ts) (by
      eval_at (fun v : Var n => match v with | .x1 => (Polynomial.X : Polynomial R) | _ => 0)
        using hD)
  have h3 : ∀ i, mU i = 0 ∧ mU i + mV i = 0 := fun i => by
    have h3 := quad_eq (R := R) (a := bU) (b := 0) (c := 0) (a' := 0) (b' := mU i) (c' := 0) (by
      eval_at (fun v : Var n => match v with
        | .y j => if j = i then (Polynomial.X : Polynomial R) else 0 | _ => 0) using hD)
    have h4 := quad_eq (R := R) (a := bU + bV) (b := 0) (c := 0) (a' := aU + aV)
      (b' := mU i + mV i) (c' := 0) (by
      eval_at (fun v : Var n => match v with
        | .x0 => 1 | .y j => if j = i then (Polynomial.X : Polynomial R) else 0 | _ => 0)
        using hD)
    exact ⟨h3.2.1.symm, h4.2.1.symm⟩
  refine ⟨h1.1, h1.2.1.trans ?_, h1.2.2.symm, h2.2.1, fun i => (h3 i).1, fun i => ?_⟩
  · simp
  · have := h3 i
    grind

/-- **The base elements.** A verification identity over `1, C_W, I` holds only with all
coefficients zero. -/
theorem base_coeffs [IsDomain R] {ts : R} (hγw : γ.gw ≠ 0) (hγw' : γ.gw' ≠ 0) (hγ0 : γ.g0 ≠ 0)
    (hz : γ.g0 * ts ≠ γ.g1) {c a b cU cV dU dV : R} {e ci di : Fin n → R}
    (h : C b + C cV * cwPoly γ + C dV * iPoly γ =
      C c * (C γ.gw * X .w) + (C a + C cU * cwPoly γ + C dU * iPoly γ) * lin ts +
        ∑ i, X (.y i) * (C (e i) + C (ci i) * cwPoly γ + C (di i) * iPoly γ)) :
    c = 0 ∧ a = 0 ∧ b = 0 ∧ cU = 0 ∧ cV = 0 ∧ dU = 0 ∧ dV = 0 ∧
      ∀ i, e i = 0 ∧ ci i = 0 ∧ di i = 0 := by
  have mz : ∀ {x y : R}, x * y = 0 → y ≠ 0 → x = 0 := fun h hy =>
    (mul_eq_zero.mp h).resolve_right hy
  have s1 := quad_eq (R := R) (a := b + dV * γ.gV) (b := cV * γ.gw) (c := 0) (a' := 0)
    (b' := c * γ.gw) (c' := 0) (by
      eval_at (fun v : Var n => match v with | .w => (Polynomial.X : Polynomial R) | _ => 0)
        using h)
  have s2 := quad_eq (R := R) (a := b + dV * γ.gV) (b := cV * γ.gw') (c := 0) (a' := 0)
    (b' := 0) (c' := 0) (by
      eval_at (fun v : Var n => match v with | .w' => (Polynomial.X : Polynomial R) | _ => 0)
        using h)
  have s3 := quad_eq (R := R) (a := b + dV * γ.gV) (b := -dV * γ.g0) (c := 0) (a' := 0)
    (b' := a + dU * γ.gV) (c' := -dU * γ.g0) (by
      eval_at (fun v : Var n => match v with | .x0 => (Polynomial.X : Polynomial R) | _ => 0)
        using h)
  have s4 := quad_eq (R := R) (a := b + dV * γ.gV) (b := -dV * γ.g1) (c := 0) (a' := 0)
    (b' := (a + dU * γ.gV) * ts) (c' := -dU * γ.g1 * ts) (by
      eval_at (fun v : Var n => match v with | .x1 => (Polynomial.X : Polynomial R) | _ => 0)
        using h)
  have s5 := quad_eq (R := R) (a := b + dV * γ.gV) (b := cV * γ.gw - dV * γ.g0) (c := 0)
    (a' := 0) (b' := c * γ.gw + a + dU * γ.gV) (c' := cU * γ.gw - dU * γ.g0) (by
      eval_at (fun v : Var n => match v with
        | .w => (Polynomial.X : Polynomial R) | .x0 => Polynomial.X | _ => 0) using h)
  have hcV : cV = 0 := mz (by linear_combination s2.2.1) hγw'
  have hc : c = 0 := mz (by linear_combination -s1.2.1 + γ.gw * hcV) hγw
  have hdU : dU = 0 := mz (by linear_combination s3.2.2) hγ0
  have hdV : dV = 0 := by
    refine mz (y := γ.g0 * ts - γ.g1) ?_ (sub_ne_zero.mpr hz)
    linear_combination s4.2.1 - ts * s3.2.1
  have ha : a = 0 := by linear_combination -s3.2.1 - γ.g0 * hdV - γ.gV * hdU
  have hb : b = 0 := by linear_combination s2.1 - γ.gV * hdV
  have hcU : cU = 0 := mz (by linear_combination -s5.2.2 + γ.g0 * hdU) hγw
  refine ⟨hc, ha, hb, hcU, hcV, hdU, hdV, fun i => ?_⟩
  have s6 := quad_eq (R := R) (a := b + dV * γ.gV) (b := -dV * γ.gy i) (c := 0) (a' := 0)
    (b' := e i + di i * γ.gV) (c' := -di i * γ.gy i) (by
      eval_at (fun v : Var n => match v with
        | .y j => if j = i then (Polynomial.X : Polynomial R) else 0 | _ => 0) using h)
  have s7 := quad_eq (R := R) (a := b + dV * (γ.gV - γ.g0)) (b := -dV * γ.gy i) (c := 0)
    (a' := a + dU * (γ.gV - γ.g0))
    (b' := -dU * γ.gy i + e i + di i * (γ.gV - γ.g0)) (c' := -di i * γ.gy i) (by
      eval_at (fun v : Var n => match v with
        | .x0 => 1 | .y j => if j = i then (Polynomial.X : Polynomial R) else 0 | _ => 0)
        using h)
  have s8 := quad_eq (R := R) (a := b + cV * γ.gw + dV * γ.gV) (b := -dV * γ.gy i) (c := 0)
    (a' := c * γ.gw) (b' := e i + ci i * γ.gw + di i * γ.gV) (c' := -di i * γ.gy i) (by
      eval_at (fun v : Var n => match v with
        | .w => 1 | .y j => if j = i then (Polynomial.X : Polynomial R) else 0 | _ => 0)
        using h)
  have hdi : di i = 0 :=
    mz (by linear_combination s7.2.1 - s6.2.1 - γ.gy i * hdU) hγ0
  have hei : e i = 0 := by linear_combination -s6.2.1 - γ.gy i * hdV - γ.gV * hdi
  exact ⟨hei, mz (by linear_combination -s8.2.1 - hei - γ.gV * hdi - γ.gy i * hdV) hγw, hdi⟩

omit [CommRing R] in
/-- A sum over `range (k + 1)` of a sequence that is `a` at `k` and `l` below. -/
theorem sum_range_succ_ite {β : Type} [AddCommMonoid β] (k : ℕ) (a : R) (l : ℕ → R)
    (f : R → ℕ → β) :
    ∑ j ∈ Finset.range (k + 1), f (if j = k then a else l j) j =
      ∑ j ∈ Finset.range k, f (l j) j + f a k := by
  rw [Finset.sum_range_succ]
  simp only [↓reduceIte]
  congr 1
  exact Finset.sum_congr rfl fun j hj => by
    have : j ≠ k := by simp only [Finset.mem_range] at hj; omega
    simp only [this, ↓reduceIte]

/-- **Peeling.** An identity `V = c γ_w w + U (x0 + t* x1) + Σ y_i M_i` over the elements
received before the `k`-th MAC answer makes `(U, V, M)` a combination `Σ_j l_j (U_j, V_j, M_j)`
with `Σ_j l_j = c` and `l_j = 0` unless `t_j = t*`. -/
theorem peel [IsDomain R] {ts : R} (hγw : γ.gw ≠ 0) (hγw' : γ.gw' ≠ 0) (hγ0 : γ.g0 ≠ 0)
    (hz : γ.g0 * ts ≠ γ.g1) (k : ℕ) :
    ∀ (c : R) (U V : MvPolynomial (Var n) R) (Mf : Fin n → MvPolynomial (Var n) R),
      U ∈ spanAt γ t M k → V ∈ spanAt γ t M k → (∀ i, Mf i ∈ spanAt γ t M k) →
      V = C c * (C γ.gw * X .w) + U * lin ts + ∑ i, X (.y i) * Mf i →
      ∃ l : ℕ → R, (∀ j < k, l j * (t j - ts) = 0) ∧ ∑ j ∈ Finset.range k, l j = c ∧
        U = ∑ j ∈ Finset.range k, C (l j) * X (.u j) ∧
        V = ∑ j ∈ Finset.range k, C (l j) * vPoly γ t M j ∧
        ∀ i, Mf i = ∑ j ∈ Finset.range k, C (l j) * mPoly γ t M j i := by
  induction k with
  | zero =>
    intro c U V Mf hU hV hM h
    obtain ⟨a, cU, dU, rfl⟩ := mem_spanAt_zero hU
    obtain ⟨b, cV, dV, rfl⟩ := mem_spanAt_zero hV
    choose e ci di hMf using fun i => mem_spanAt_zero (hM i)
    obtain rfl : Mf = fun i => C (e i) + C (ci i) * cwPoly γ + C (di i) * iPoly γ := funext hMf
    obtain ⟨hc, ha, hb, hcU, hcV, hdU, hdV, hi⟩ := base_coeffs hγw hγw' hγ0 hz h
    refine ⟨fun _ => 0, by simp, by simp [hc], by simp [ha, hcU, hdU], by simp [hb, hcV, hdV],
      fun i => by simp [(hi i).1, (hi i).2.1, (hi i).2.2]⟩
  | succ k ih =>
    intro c U V Mf hU hV hM h
    obtain ⟨U', hU', aU, aV, rfl⟩ := mem_spanAt_succ hU
    obtain ⟨V', hV', bU, bV, rfl⟩ := mem_spanAt_succ hV
    choose M' hM' mU mV hMf using fun i => mem_spanAt_succ (hM i)
    have hMf' := funext hMf
    subst hMf'
    have hM0 : ∀ i, pderiv (Var.u k) (M' i) = 0 := fun i => pderiv_eq_zero_of_mem (hM' i)
    have hy : ∀ i, pderiv (Var.u k) (X (Var.y i) : MvPolynomial (Var n) R) = 0 := fun i =>
      pderiv_X_of_ne (by simp)
    have hD : C bU + C bV * lin (t k) = (C aU + C aV * lin (t k)) * lin ts +
        ∑ i, X (.y i) * (C (mU i) + C (mV i) * lin (t k)) := by
      have := congrArg (pderiv (Var.u k)) h
      simp only [map_add, map_sum, pderiv_mul, pderiv_C, pderiv_X_self,
        pderiv_eq_zero_of_mem hU', pderiv_eq_zero_of_mem hV', hM0, pderiv_vPoly, pderiv_lin,
        pderiv_X_of_ne (show Var.w ≠ Var.u k by simp), hy, zero_mul, mul_zero, zero_add,
        add_zero, mul_one] at this
      linear_combination this
    obtain ⟨hbU, hbV, haV, ht, hmU, hmV⟩ := peel_coeffs hD
    subst hbU haV
    subst bV
    have hmU' : mU = 0 := funext hmU
    have hmV' : mV = 0 := funext hmV
    subst hmU' hmV'
    have hM'' : ∀ i, M' i - C aU * mPoly γ t M k i ∈ spanAt γ t M k := fun i => by
      refine Submodule.sub_mem _ (hM' i) ?_
      rw [C_mul']
      exact Submodule.smul_mem _ _ (rep_mem _ _)
    have hid : V' = C (c - aU) * (C γ.gw * X .w) + U' * lin ts +
        ∑ i, X (.y i) * (M' i - C aU * mPoly γ t M k i) := by
      have hC : C aU * C (t k) = (C aU * C ts : MvPolynomial (Var n) R) := by
        rw [← map_mul, ← map_mul, ht]
      have hs : ∑ i, X (.y i) * (M' i - C aU * mPoly γ t M k i) =
          ∑ i, X (.y i) * M' i - C aU * ∑ i, X (.y i) * mPoly γ t M k i := by
        rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun i _ => by ring
      simp only [Pi.zero_apply, map_zero, zero_mul, add_zero] at h
      rw [hs, map_sub]
      simp only [vPoly, lin] at h ⊢
      linear_combination h - (X (.u k) * X .x1) * hC
    obtain ⟨l, hl, hsum, hUl, hVl, hMl⟩ := ih (c - aU) U' V'
      (fun i => M' i - C aU * mPoly γ t M k i) hU' hV' hM'' hid
    refine ⟨fun j => if j = k then aU else l j, fun j hj => ?_, ?_, ?_, ?_, fun i => ?_⟩
    · by_cases hjk : j = k
      · subst hjk
        simp only [↓reduceIte]
        linear_combination ht
      · simp only [hjk, ↓reduceIte]
        exact hl j (by omega)
    · beta_reduce
      rw [sum_range_succ_ite k aU l fun x _ => x, hsum]
      ring
    · beta_reduce
      rw [sum_range_succ_ite k aU l fun x j => (C x * X (Var.u j) : MvPolynomial (Var n) R),
        ← hUl]
      simp
    · beta_reduce
      rw [sum_range_succ_ite k aU l fun x j => C x * vPoly γ t M j, ← hVl]
      simp
    · beta_reduce
      rw [sum_range_succ_ite k aU l fun x j => C x * mPoly γ t M j i, ← hMl i]
      simp

/-- **The algebraic lemma (Orrù 2024, Lemma 5.4, for `MAC_n` with group attributes).** After
`q` MAC answers with pairwise distinct `t_j`, a forgery `(μ, (t*, α, β))` given by
representations over the received elements whose verification equation
`V* = γ_w w + U* (x0 + t* x1) + Σ y_i M*_i` holds as a polynomial identity is the `j`-th MAC
answer for some `j < q`: `t* = t_j`, and `U*`, `V*`, `M*` have the polynomials of `U_j`,
`V_j`, `M_j`. The hypotheses are `γ_w, γ_{w'}, γ_0 ≠ 0` and `γ_0 t* ≠ γ_1`
(`t* ≠ log_{G_{x0}} G_{x1}`). -/
theorem forgery_poly_identity_not_fresh [IsDomain R] {q : ℕ} {ts : R} {α β : List R}
    {μ : Fin n → List R} (hγw : γ.gw ≠ 0) (hγw' : γ.gw' ≠ 0) (hγ0 : γ.g0 ≠ 0)
    (hz : γ.g0 * ts ≠ γ.g1) (ht : ∀ j < q, ∀ j' < q, t j = t j' → j = j')
    (hφ : rep (basis γ t M q) β = C γ.gw * X .w + rep (basis γ t M q) α * lin ts +
      ∑ i, X (.y i) * rep (basis γ t M q) (μ i)) :
    ∃ j < q, ts = t j ∧ rep (basis γ t M q) α = X (.u j) ∧
      rep (basis γ t M q) β = vPoly γ t M j ∧ ∀ i, rep (basis γ t M q) (μ i) = mPoly γ t M j i := by
  obtain ⟨l, hl, hsum, hU, hV, hM⟩ := peel hγw hγw' hγ0 hz q 1 _ _ _ (rep_mem _ _) (rep_mem _ _)
    (fun i => rep_mem _ _) (by rw [map_one, one_mul]; exact hφ)
  obtain ⟨j, hj, hlj⟩ := Finset.exists_ne_zero_of_sum_ne_zero (s := Finset.range q) (f := l)
    (by rw [hsum]; exact one_ne_zero)
  have hjq : j < q := Finset.mem_range.mp hj
  have htj : t j = ts := by
    have := hl j hjq
    rw [mul_eq_zero, sub_eq_zero] at this
    exact this.resolve_left hlj
  have hzero : ∀ j' ∈ Finset.range q, j' ≠ j → l j' = 0 := fun j' hj' hne => by
    have := hl j' (Finset.mem_range.mp hj')
    rw [mul_eq_zero, sub_eq_zero] at this
    exact this.resolve_right fun h => hne (ht j' (Finset.mem_range.mp hj') j hjq (h.trans htj.symm))
  have hsingle : ∀ f : ℕ → MvPolynomial (Var n) R,
      ∑ j' ∈ Finset.range q, C (l j') * f j' = C (l j) * f j := fun f =>
    Finset.sum_eq_single j (fun j' hj' hne => by rw [hzero j' hj' hne, map_zero, zero_mul])
      (fun h => absurd hj h)
  have hl1 : l j = 1 := by
    rw [← hsum]
    exact (Finset.sum_eq_single j (fun j' hj' hne => hzero j' hj' hne)
      (fun h => absurd hj h)).symm
  refine ⟨j, hjq, htj.symm, ?_, ?_, fun i => ?_⟩
  · rw [hU, hsingle fun j' => X (.u j'), hl1, map_one, one_mul]
  · rw [hV, hsingle fun j' => vPoly γ t M j', hl1, map_one, one_mul]
  · rw [hM i, hsingle fun j' => mPoly γ t M j' i, hl1, map_one, one_mul]

end Formal

/-! ## The degree bound -/

section Degree

open CatCryptCore.Examples.CyclicGroupDDH CatCrypt.Examples.OT AlgMac AlgMac.MacN

variable {G : Type} [CGR : CyclicGroupRing G]

/-- The sum of list polynomials has the length of the longer summand. -/
theorem length_padd (p q : Poly G) : (padd p q).length = max p.length q.length := by
  induction p generalizing q with
  | nil => simp [padd]
  | cons a p ih =>
    cases q with
    | nil => simp [padd]
    | cons b q =>
      simp only [padd, List.length_cons, ih]
      omega

/-- A scalar multiple has the length of the polynomial. -/
theorem length_pscale (c : CGR.Exp) (p : Poly G) : (pscale c p).length = p.length := by
  simp [pscale]

/-- The negation has the length of the polynomial. -/
theorem length_pneg (p : Poly G) : (pneg p).length = p.length := by
  simp [pneg]

/-- The product of polynomials of degrees at most `a` and `b` has degree at most `a + b`. -/
theorem length_pmul_le (q : Poly G) (b : ℕ) (hq : q.length ≤ b + 1) :
    ∀ (p : Poly G) (a : ℕ), p.length ≤ a + 1 → (pmul p q).length ≤ a + b + 1
  | [], _, _ => by simp [pmul]
  | x :: p, a, hp => by
    have ih := length_pmul_le q b hq p (a - 1) (by simp only [List.length_cons] at hp; omega)
    simp only [pmul, length_padd, length_pscale, List.length_cons]
    simp only [List.length_cons] at hp
    rcases p with _ | ⟨y, p⟩
    · simp only [pmul, List.length_nil]
      omega
    · simp only [List.length_cons] at hp
      omega

/-- A sum of polynomials of length at most `d` has length at most `d`. -/
theorem length_psum_le (l : List (Poly G)) (d : ℕ) (h : ∀ p ∈ l, p.length ≤ d) :
    (psum l).length ≤ d := by
  induction l with
  | nil => simp [psum]
  | cons p l ih =>
    have := ih fun q hq => h q (List.mem_cons_of_mem _ hq)
    simp only [psum, List.foldr_cons] at this ⊢
    rw [length_padd]
    exact max_le (h p List.mem_cons_self) this

/-- The polynomial of a representation over polynomials of length at most `d` has length at
most `d`. -/
theorem length_polyRep_le (P : List (Poly G)) (c : Rep G) (d : ℕ)
    (h : ∀ p ∈ P, p.length ≤ d) : (polyRep P c).length ≤ d := by
  induction P generalizing c with
  | nil => cases c <;> simp [polyRep, psum]
  | cons p P ih =>
    cases c with
    | nil => simp [polyRep, psum]
    | cons a c =>
      have := ih c fun q hq => h q (List.mem_cons_of_mem _ hq)
      simp only [polyRep, psum, List.zipWith_cons_cons, List.foldr_cons] at this ⊢
      rw [length_padd, length_pscale]
      exact max_le (h p List.mem_cons_self) this

/-- Key polynomials of degree at most `1`. -/
def KeyPolys.Lin {n : ℕ} (kp : KeyPolys G n) : Prop :=
  kp.w.length ≤ 2 ∧ kp.w'.length ≤ 2 ∧ kp.x0.length ≤ 2 ∧ kp.x1.length ≤ 2 ∧
    ∀ i, (kp.y i).length ≤ 2

/-- The key polynomials `a_v + b_v χ` have degree at most `1`. -/
theorem keyPolys_lin {n : ℕ} (a b : MacN.Key G n) : (keyPolys a b).Lin := by
  simp [KeyPolys.Lin, keyPolys]

/-- `macPoly` raises the degree of its arguments by at most one. -/
theorem length_macPoly_le {n : ℕ} (γw : CGR.Exp) (kp : KeyPolys G n) (hkp : kp.Lin)
    (pA0 pA1 : Poly G) (pA : Fin n → Poly G) (d : ℕ) (h0 : pA0.length ≤ d + 1)
    (h1 : pA1.length ≤ d + 1) (hA : ∀ i, (pA i).length ≤ d + 1) :
    (macPoly γw kp pA0 pA1 pA).length ≤ d + 2 := by
  obtain ⟨hw, -, hx0, hx1, hy⟩ := hkp
  have e0 := length_pmul_le pA0 d h0 kp.x0 1 hx0
  have e1 := length_pmul_le pA1 d h1 kp.x1 1 hx1
  have e2 := length_psum_le (List.ofFn fun i => pmul (kp.y i) (pA i)) (d + 2) (by
    intro p hp
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
    have := length_pmul_le (pA i) d (hA i) (kp.y i) 1 (hy i)
    omega)
  simp only [macPoly, length_padd, length_pscale]
  omega

/-- The forgery polynomial over a state of degree at most `d` has degree at most `d + 1`. -/
theorem forgeryPoly_length_le {n : ℕ} (γw : CGR.Exp) (kp : KeyPolys G n) (hkp : kp.Lin)
    (P : List (Poly G)) (d : ℕ) (hP : ∀ p ∈ P, p.length ≤ d + 1) (o : SymOut G n) :
    (forgeryPoly γw kp P o).length ≤ d + 2 := by
  have h1 := length_polyRep_le P o.2.2.2 (d + 1) hP
  have h2 := length_macPoly_le γw kp hkp (polyRep P o.2.2.1)
    (pscale o.2.1 (polyRep P o.2.2.1)) (fun i => polyRep P (o.1 i)) d
    (length_polyRep_le P _ _ hP) (by rw [length_pscale]; exact length_polyRep_le P _ _ hP)
    (fun i => length_polyRep_le P _ _ hP)
  simp only [forgeryPoly, length_padd, length_pneg]
  omega

/-- **Degree bound of `simO`.** Against `simO`, an adversary with at most `m` MAC queries
leaves a state whose polynomials have degree at most `e + m + 1` when the start state has degree
at most `e + 1`. -/
theorem simO_run_length [DecidableEq G] {n : ℕ} {α : Type} (ch : List G) (γw : CGR.Exp)
    (kp : KeyPolys G n) (hkp : kp.Lin) (A : OracleAdv (SymQ G n) (Ans G) α) :
    ∀ (m e : ℕ) (P : List (Poly G)), A.IsQueryBoundBy macCost m →
      (∀ p ∈ P, p.length ≤ e + 2) →
      ∀ y ∈ (OracleAdv.run (simO ch γw kp) A P).support, ∀ p ∈ y.2, p.length ≤ e + m + 2 := by
  induction A with
  | ret a =>
    intro m e P _ hP y hy p hp
    simp only [OracleAdv.run_ret, PMF.support_pure, Set.mem_singleton_iff] at hy
    subst hy
    have := hP p hp
    omega
  | rand p k ih =>
    intro m e P hA hP y hy
    rw [OracleAdv.run_rand, PMF.mem_support_bind_iff] at hy
    obtain ⟨b, -, hy⟩ := hy
    exact ih b m e P (hA b) hP y hy
  | query d k ih =>
    intro m e P hA hP y hy
    rw [OracleAdv.run_query, PMF.mem_support_bind_iff] at hy
    obtain ⟨x, hx, hy⟩ := hy
    obtain ⟨hc, hk⟩ := hA
    rcases d with Msym | q | q
    · simp only [simO, PMF.support_map, Set.mem_image] at hx
      obtain ⟨r, -, rfl⟩ := hx
      have hm : 1 ≤ m := hc
      have hP' : ∀ p ∈ P ++ [[r.2.1, r.2.2], macPoly γw kp [r.2.1, r.2.2]
          (pscale r.1 [r.2.1, r.2.2]) fun i => polyRep P (Msym i)], p.length ≤ (e + 1) + 2 := by
        intro p hp
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with hp | rfl | rfl
        · have := hP p hp
          omega
        · simp
        · exact length_macPoly_le γw kp hkp _ _ _ (e + 1) (by simp)
            (by rw [length_pscale]; simp) fun i => length_polyRep_le P _ _ hP
      intro p hp
      have := ih _ (m - 1) (e + 1) _ (hk _) hP' y hy p hp
      omega
    · simp only [simO, PMF.support_pure, Set.mem_singleton_iff] at hx
      subst hx
      exact ih _ m e P (by simpa only [macCost, Nat.sub_zero] using hk _) hP y hy
    · simp only [simO, PMF.support_pure, Set.mem_singleton_iff] at hx
      subst hx
      exact ih _ m e P (by simpa only [macCost, Nat.sub_zero] using hk _) hP y hy

/-- The starting polynomials of `reductionAlg` have degree at most `1`. -/
theorem basisPolys0_length {n : ℕ} (one : CGR.Exp) (γ : ParExp G n) (a b : MacN.Key G n) :
    ∀ p ∈ basisPolys0 one γ (keyPolys a b), p.length ≤ 2 := by
  intro p hp
  simp only [basisPolys0, List.mem_append, List.mem_cons, List.mem_ofFn, List.not_mem_nil,
    or_false] at hp
  rcases hp with (((rfl | rfl | rfl | rfl | rfl | rfl) | ⟨i, rfl⟩) | ⟨i, rfl⟩) | rfl | rfl
  all_goals try simp
  · simp [keyPolys, length_padd, length_pscale]
  · have := length_psum_le (List.ofFn fun i => pscale (γ.2.2.2.2.2.1 i) ((keyPolys a b).y i)) 2
      (by
        intro p hp
        obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hp
        simp [keyPolys, length_pscale])
    simp only [length_padd, length_pneg, length_pscale, keyPolys, List.length_cons,
      List.length_nil] at this ⊢
    omega

/-- **The degree bound of `reductionAlg`.** For an algebraic adversary with at most `q_m` MAC
queries, every polynomial of the final state of `simO` has degree at most `q_m + 1`, and the
forgery polynomial `ψ*` has degree at most `q_m + 2`. -/
theorem reductionAlg_degree [DecidableEq G] {n : ℕ} (one : CGR.Exp) (ch : List G)
    (γ : ParExp G n) (a b : MacN.Key G n) (A : OracleAdv (SymQ G n) (Ans G) (SymOut G n))
    (qm : ℕ) (hA : A.IsQueryBoundBy macCost qm)
    (y : SymOut G n × List (Poly G))
    (hy : y ∈ (OracleAdv.run (simO ch γ.1 (keyPolys a b)) A
      (basisPolys0 one γ (keyPolys a b))).support) :
    (∀ p ∈ y.2, p.length ≤ qm + 2) ∧
      (forgeryPoly γ.1 (keyPolys a b) y.2 y.1).length ≤ qm + 3 := by
  have h := simO_run_length ch γ.1 _ (keyPolys_lin a b) A qm 0 _ hA
    (fun p hp => basisPolys0_length one γ a b p hp) y hy
  refine ⟨fun p hp => by have := h p hp; omega, ?_⟩
  exact forgeryPoly_length_le γ.1 _ (keyPolys_lin a b) y.2 (qm + 1) (fun p hp => by
    have := h p hp; omega) y.1

end Degree

/-! ## The reduction `B_z` -/

section ReductionZ

open CatCryptCore.Examples.CyclicGroupDDH CatCrypt.Examples.OT AlgMac AlgMac.MacN
open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto.Assumptions.KDL

variable {G : Type} [CGR : CyclicGroupRing G]

/-- For a generator `g ≠ 1`, `a ↦ g^a` is a bijection. -/
theorem elemPow_gen_bijective (hgen : CGR.gen ≠ CGR.one) :
    Function.Bijective (CyclicGroup.elemPow (G := G) CGR.gen) := by
  have hd : (CGR.pow_bij.2 CGR.gen).choose ≠ CGR.expZero := by
    intro h
    apply hgen
    rw [← (CGR.pow_bij.2 CGR.gen).choose_spec, h, CGR.pow_zero]
  exact CGR.pow_bij.comp (CGR.expMul_bij _ hd)

/-- A bind is monotone in its continuation, outcome by outcome. -/
theorem pmf_bind_apply_mono {α β : Type} (μ : PMF α) (f g : α → PMF β) (b : β)
    (h : ∀ x, f x b ≤ g x b) : (μ.bind f) b ≤ (μ.bind g) b := by
  rw [PMF.bind_apply, PMF.bind_apply]
  exact ENNReal.tsum_le_tsum fun x => by gcongr; exact h x

/-- The probability of `true` under a map grows with the event. -/
theorem pmf_map_true_mono {α : Type} (p : PMF α) (d e : α → Bool)
    (h : ∀ a, d a = true → e a = true) : (p.map d) true ≤ (p.map e) true := by
  rw [PMF.map_apply, PMF.map_apply]
  refine ENNReal.tsum_le_tsum fun a => ?_
  by_cases hd : d a = true
  · simp [hd, h a hd]
  · split_ifs <;> simp_all

variable {n : ℕ}

/-- The parameters of `reductionZ`: those of `p` with `G_{x0} = g^{γ0}` and `G_{x1} = g^χ`. -/
noncomputable def zPar (χ : CGR.Exp) (p : MacN.Par G n) (γ0 : CGR.Exp) : MacN.Par G n :=
  (gw p, gw' p, CyclicGroup.elemPow CGR.gen γ0, CyclicGroup.elemPow CGR.gen χ, gV p, gy p, gm p)

/-- Uniform `χ`, `p`, `γ0` give uniform parameters `zPar χ p γ0`. -/
theorem uniform_zPar {β : Type} (hgen : CGR.gen ≠ CGR.one) (K : MacN.Par G n → PMF β) :
    (PMF.uniformFintype CGR.Exp).bind (fun χ => (PMF.uniformFintype (MacN.Par G n)).bind
      fun p => (PMF.uniformFintype CGR.Exp).bind fun γ0 => K (zPar χ p γ0)) =
      (PMF.uniformFintype (MacN.Par G n)).bind K := by
  let e : CGR.Exp ≃ G := Equiv.ofBijective _ (elemPow_gen_bijective hgen)
  let E : CGR.Exp × MacN.Par G n × CGR.Exp ≃ MacN.Par G n × (G × G) :=
    { toFun := fun z => (zPar z.1 z.2.1 z.2.2, (gx0 z.2.1, gx1 z.2.1))
      invFun := fun w => (e.symm (gx1 w.1), (gw w.1, gw' w.1, w.2.1, w.2.2, gV w.1, gy w.1, gm w.1),
        e.symm (gx0 w.1))
      left_inv := fun z => by
        obtain ⟨χ, ⟨a, b, c, d, v, y, m⟩, γ0⟩ := z
        simp [zPar, e]
      right_inv := fun w => by
        obtain ⟨⟨a, b, c, d, v, y, m⟩, x0, x1⟩ := w
        simp [zPar, e, Equiv.ofBijective_apply_symm_apply] }
  have hmap : (PMF.uniformFintype (CGR.Exp × MacN.Par G n × CGR.Exp)).map
      (fun z => zPar z.1 z.2.1 z.2.2) = PMF.uniformFintype (MacN.Par G n) := by
    rw [show (fun z : CGR.Exp × MacN.Par G n × CGR.Exp => zPar z.1 z.2.1 z.2.2) =
      Prod.fst ∘ E from rfl, ← PMF.map_comp, PMF.uniformFintype_map_equiv, PMF.map_uniform_fst]
  conv_rhs => rw [← hmap, PMF.bind_map, PMF.uniform_prod_eq_bind, PMF.uniform_prod_eq_bind]
  simp only [PMF.bind_bind, PMF.map_bind, PMF.bind_map, Function.comp_def]

variable [DecidableEq G] [DecidableEq CGR.Exp]

/-- **The event of `B_z`.** The suf-cmva-Help game of `macN` that accepts a forgery only when
`t* = log_{G_{x0}} G_{x1}`, that is `G_{x0}^{t*} = G_{x1}`. -/
noncomputable def zEventGame
    (A : MacN.Par G n → G × G →
      OracleAdv (macN G n).HelpQry (macN G n).HelpAns ((macN G n).Msg × (macN G n).Tag)) :
    SPComp Bool :=
  liftPMF ((macN G n).setup.bind fun x =>
    (OracleAdv.run ((macN G n).helpOracle x.1 x.2) (A x.1 (iparams x.1 x.2)) []).map fun y =>
      ((macN G n).verify x.1 x.2 y.1.1 y.1.2 && (macN G n).strongFresh y.1 y.2) &&
        decide (CyclicGroup.elemPow (gx0 (x.1 : MacN.Par G n)) (y.1.2 : CGR.Exp × G × G).1 =
          gx1 (x.1 : MacN.Par G n)))

/-- The probability of `G_{x0}^{t*} = G_{x1}` at fixed parameters `p`. -/
noncomputable def zAt
    (A : MacN.Par G n → G × G →
      OracleAdv (macN G n).HelpQry (macN G n).HelpAns ((macN G n).Msg × (macN G n).Tag))
    (p : MacN.Par G n) : PMF Bool :=
  (PMF.uniformFintype (MacN.Key G n)).bind fun k =>
    (OracleAdv.run ((macN G n).helpOracle p k) (A p (iparams p k)) []).map fun y =>
      decide (CyclicGroup.elemPow (gx0 p) (y.1.2 : CGR.Exp × G × G).1 = gx1 p)

/-- **The reduction `B_z` to DL.** The probability that `A` wins suf-cmva-Help with
`t* = log_{G_{x0}} G_{x1}` is at most the DL advantage of `reductionZ A`, for a generator
`g ≠ 1`. -/
theorem reductionZ_bound (hgen : CGR.gen ≠ CGR.one)
    (A : MacN.Par G n → G × G →
      OracleAdv (macN G n).HelpQry (macN G n).HelpAns ((macN G n).Msg × (macN G n).Tag)) :
    prTrue (zEventGame A) Heap.empty ≤ DL_Advantage (reductionZ A) := by
  rw [zEventGame, prTrue_liftPMF, DL_Advantage, DL_Game_eq, prTrue_liftPMF]
  calc _ ≤ ((PMF.uniformFintype (MacN.Par G n)).bind (zAt A)) true := by
        rw [AlgMac.setup, PMF.bind_bind]
        refine pmf_bind_apply_mono _ _ _ _ fun p => ?_
        rw [PMF.bind_map]
        refine pmf_bind_apply_mono _ _ _ _ fun k => pmf_map_true_mono _ _ _ fun y hy => ?_
        simp only [Bool.and_eq_true] at hy
        exact hy.2
    _ = ((PMF.uniformFintype CGR.Exp).bind fun χ => (PMF.uniformFintype (MacN.Par G n)).bind
          fun p => (PMF.uniformFintype CGR.Exp).bind fun γ0 => zAt A (zPar χ p γ0)) true := by
        rw [uniform_zPar hgen]
    _ ≤ _ := by
        refine pmf_bind_apply_mono _ _ _ _ fun χ => ?_
        simp only [reductionZ, PMF.map_bind]
        refine pmf_bind_apply_mono _ _ _ _ fun p => ?_
        refine pmf_bind_apply_mono _ _ _ _ fun γ0 => ?_
        refine pmf_bind_apply_mono _ _ _ _ fun k => ?_
        rw [PMF.map_comp]
        refine pmf_map_true_mono _ _ _ fun y hy => ?_
        simp only [decide_eq_true_eq, Function.comp_apply] at hy ⊢
        apply (elemPow_gen_bijective hgen).1
        rw [CyclicGroupRing.elemPow_mul]
        exact hy

end ReductionZ

end CatCrypt.Crypto.KVAC.MacNHelpAGM
