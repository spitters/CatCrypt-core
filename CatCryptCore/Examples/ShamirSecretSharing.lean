/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Crypto.SecurityDefs
import CatCryptCore.Relational.Rules
import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic
import CatCryptCore.Tactics
import CatCryptCore.Deep.ReflectUCHelpers

/-!
# Shamir `t`-out-of-`n` Secret Sharing: Reconstruction and Perfect Privacy

Shamir's secret-sharing scheme over the finite field `ZMod p` (`p` prime): a
secret `s` is shared by sampling a uniformly random polynomial `f` of degree
`< t` with `f(0) = s`, and handing party `i` the point `f(xᵢ)` at a distinct,
nonzero evaluation point `xᵢ`. Reconstruction from any `t` shares is Lagrange
interpolation; **perfect privacy** says any `t-1` shares are jointly uniform and
independent of `s`.

We model a degree-`< t` polynomial by its constant coefficient `s` (the secret)
together with `d := t-1` *free* coefficients `a : Fin d → ZMod p` (the
coefficients of `X¹, …, X^d`). Sharing at a point `q` is then
`shareVal s a q = s + ∑ᵢ aᵢ · q^{i+1}`, which is exactly the evaluation of the
polynomial `build s a = C s + ∑ᵢ C aᵢ · X^{i+1}` at `q` (`shareVal_eq_eval`).

## Main definitions

* `shareVal` / `build` — the field-level share and the underlying polynomial.
* `PrivGame` / `PrivAdv` — the `(t-1)`-share privacy game and its advantage.

## Main results

* `shamir_reconstruct` — **reconstruction**: for any `t = d+1` distinct
  evaluation points, Lagrange interpolation through the shares recovers the
  secret `f(0) = s`. General `t`-out-of-`n`.
* `shamir_perfect_privacy` — **perfect privacy**: for any `t-1` nonzero
  evaluation points, any two secrets `s₀, s₁`, and any adversary `A`, the
  `(t-1)`-share privacy advantage is exactly `0`. General `t`-out-of-`n`.

The privacy coupling avoids inverting a Vandermonde matrix: the difference of the
two secrets is absorbed by translating the free-coefficient vector by the free
coefficients of `(s₁ - s₀) · L`, where `L` is the degree-`< t` polynomial that is
`1` at `0` and `0` at every revealed point (`vanishPoly`). Since translation is a
bijection of the sampling space, `advantage_zero_of_rHoare` collapses the
advantage to `0`. This mirrors the `poly_bij` construction of the SSProve-Rocq
proof, adapted to a coefficient-vector coupling.

## References

* [Rosulek, The Joy of Cryptography, §3.13 (Shamir secret sharing)]
* [Shamir, How to Share a Secret, CACM 1979]
-/

namespace CatCrypt.Examples.ShamirSecretSharing

open CatCrypt.Core CatCrypt.Prob CatCrypt.Relational CatCrypt.Crypto
open Polynomial
open scoped ENNReal

variable {p : ℕ} [Fact p.Prime] {d : ℕ}

/-! ## The scheme -/

/-- The share of a degree-`< d+1` polynomial with constant term `s` and free
    coefficients `a` (the coefficients of `X¹, …, X^d`), evaluated at `q`. -/
def shareVal (s : ZMod p) (a : Fin d → ZMod p) (q : ZMod p) : ZMod p :=
  s + ∑ i : Fin d, a i * q ^ ((i : ℕ) + 1)

/-- The underlying polynomial `C s + ∑ᵢ C aᵢ · X^{i+1}`. -/
noncomputable def build (s : ZMod p) (a : Fin d → ZMod p) : (ZMod p)[X] :=
  C s + ∑ i : Fin d, C (a i) * X ^ ((i : ℕ) + 1)

/-- `shareVal` is the evaluation of `build`. -/
theorem shareVal_eq_eval (s : ZMod p) (a : Fin d → ZMod p) (q : ZMod p) :
    (build s a).eval q = shareVal s a q := by
  simp only [build, shareVal, eval_add, eval_C, eval_finsetSum, eval_mul, eval_pow, eval_X]

/-- The polynomial has degree at most `d` (i.e. `< t = d+1`). -/
theorem build_natDegree_le (s : ZMod p) (a : Fin d → ZMod p) :
    (build s a).natDegree ≤ d := by
  refine (natDegree_add_le _ _).trans (max_le (by simp)
    ((natDegree_sum_le _ _).trans (Finset.sup_le fun i _ =>
      (natDegree_C_mul_le _ _).trans (by simp))))

/-- The constant term is the secret: `shareVal s a 0 = s`. -/
theorem shareVal_zero (s : ZMod p) (a : Fin d → ZMod p) : shareVal s a 0 = s := by
  simp [shareVal]

/-! ## Reconstruction (general `t`-out-of-`n`) -/

/-- **Reconstruction.** For any `t = d+1` distinct evaluation points `x`, Lagrange
    interpolation through the shares `shareVal s a (x j)` recovers the secret
    `s = f(0)`. This is the correctness of Shamir reconstruction from any `t`
    shares. -/
theorem shamir_reconstruct (x : Fin (d + 1) → ZMod p) (hx : Function.Injective x)
    (s : ZMod p) (a : Fin d → ZMod p) :
    (Lagrange.interpolate Finset.univ x (fun j => shareVal s a (x j))).eval 0 = s := by
  have hdeg : (build s a).degree < (Finset.univ : Finset (Fin (d + 1))).card := by
    rw [Finset.card_univ, Fintype.card_fin]
    exact lt_of_le_of_lt (degree_le_natDegree) (by exact_mod_cast Nat.lt_succ_of_le (build_natDegree_le s a))
  have hinterp := Lagrange.eq_interpolate (v := x) hx.injOn hdeg
  simp_rw [← shareVal_eq_eval] at *
  rw [← hinterp, shareVal_eq_eval, shareVal_zero]

/-! ## The vanishing polynomial for the privacy coupling -/

/-- `L`: the degree-`< t` polynomial equal to `1` at `0` and `0` at every revealed
    point `rp j`. Built as `(∏ⱼ (0 - rp j))⁻¹ · ∏ⱼ (X - rp j)`. -/
noncomputable def vanishPoly (rp : Fin d → ZMod p) : (ZMod p)[X] :=
  C ((∏ j, (0 - rp j))⁻¹) * ∏ j, (X - C (rp j))

theorem vanishPoly_eval (rp : Fin d → ZMod p) (q : ZMod p) :
    (vanishPoly rp).eval q = (∏ j, (0 - rp j))⁻¹ * ∏ j, (q - rp j) := by
  simp only [vanishPoly, eval_mul, eval_C, eval_prod, eval_sub, eval_X]

theorem prod_zero_sub_ne (rp : Fin d → ZMod p) (hrp : ∀ j, rp j ≠ 0) :
    (∏ j, (0 - rp j)) ≠ 0 := by
  simp [Finset.prod_ne_zero_iff, hrp]

theorem vanishPoly_eval_zero (rp : Fin d → ZMod p) (hrp : ∀ j, rp j ≠ 0) :
    (vanishPoly rp).eval 0 = 1 :=
  (vanishPoly_eval rp 0).trans (inv_mul_cancel₀ (prod_zero_sub_ne rp hrp))

theorem vanishPoly_coeff_zero (rp : Fin d → ZMod p) (hrp : ∀ j, rp j ≠ 0) :
    (vanishPoly rp).coeff 0 = 1 := by
  simp [coeff_zero_eq_eval_zero, vanishPoly_eval_zero rp hrp]

theorem vanishPoly_eval_pt (rp : Fin d → ZMod p) (k : Fin d) :
    (vanishPoly rp).eval (rp k) = 0 := by
  simp [vanishPoly_eval, Finset.prod_eq_zero (Finset.mem_univ k)]

theorem vanishPoly_natDegree_le (rp : Fin d → ZMod p) :
    (vanishPoly rp).natDegree ≤ d := by
  refine (natDegree_C_mul_le _ _).trans ?_
  refine (natDegree_prod_le _ _).trans
    (le_trans (Finset.sum_le_sum (fun j _ => natDegree_X_sub_C_le (rp j))) (by simp))

/-! ## The free-coefficient sum identity -/

/-- For a polynomial of degree `≤ d`, the "free-coefficient sum"
    `∑ᵢ f.coeff (i+1) · q^{i+1}` equals `f(q) - f.coeff 0`. -/
theorem freeSum (f : (ZMod p)[X]) (hf : f.natDegree ≤ d) (q : ZMod p) :
    ∑ i : Fin d, f.coeff ((i : ℕ) + 1) * q ^ ((i : ℕ) + 1) = f.eval q - f.coeff 0 := by
  rw [eval_eq_sum_range' (Nat.lt_succ_of_le hf) q, Finset.sum_range_succ',
    Fin.sum_univ_eq_sum_range (fun k => f.coeff (k + 1) * q ^ (k + 1)) d]; simp

/-! ## The translation vector and the share-equality identity -/

/-- The free-coefficient translation absorbing the secret difference `s₁ - s₀`. -/
noncomputable def transVec (rp : Fin d → ZMod p) (s0 s1 : ZMod p) : Fin d → ZMod p :=
  fun i => (s1 - s0) * (vanishPoly rp).coeff ((i : ℕ) + 1)

/-- **Share-equality under translation.** Sharing `s₁` with the translated free
    coefficients `a + transVec` produces the *same* revealed shares as sharing
    `s₀` with `a`. This is the information-theoretic core of privacy. -/
theorem shareVal_translate (rp : Fin d → ZMod p) (hrp : ∀ j, rp j ≠ 0)
    (s0 s1 : ZMod p) (a : Fin d → ZMod p) (j : Fin d) :
    shareVal s1 (a + transVec rp s0 s1) (rp j) = shareVal s0 a (rp j) := by
  have hkey : ∑ i : Fin d, transVec rp s0 s1 i * (rp j) ^ ((i : ℕ) + 1) = s0 - s1 := by
    simp only [transVec, mul_assoc]
    rw [← Finset.mul_sum, freeSum (vanishPoly rp) (vanishPoly_natDegree_le rp) (rp j),
      vanishPoly_eval_pt rp j, vanishPoly_coeff_zero rp hrp]; ring
  simp only [shareVal, Pi.add_apply, add_mul, Finset.sum_add_distrib, hkey]
  ring

/-! ## The privacy game -/

/-- The `(t-1)`-share privacy game. The corrupted parties hold their shares at the
    `d = t-1` revealed points `rp` of one of two secrets:
    `PrivGame rp s₀ s₁ true` shares `s₀`, `PrivGame rp s₀ s₁ false` shares `s₁`. -/
noncomputable def PrivGame (rp : Fin d → ZMod p) (s0 s1 : ZMod p) (b : Bool) :
    SPComp (Fin d → ZMod p) := do
  let a ← SPComp.sample (Fin d → ZMod p)
  SPComp.pure (fun j => shareVal (if b then s0 else s1) a (rp j))

/-- Privacy advantage: the corrupted parties' distinguishing probability between
    `(t-1)` shares of `s₀` and of `s₁`. -/
noncomputable def PrivAdv (rp : Fin d → ZMod p) (s0 s1 : ZMod p)
    (A : (Fin d → ZMod p) → SPComp Bool) : ℝ≥0∞ :=
  AdvantageA (PrivGame rp s0 s1 true) (PrivGame rp s0 s1 false) A

/-- Coupling: for any `t-1` nonzero revealed points, the two privacy games are
    equidistributed. Translating the uniformly sampled free-coefficient vector by
    `transVec` (a bijection of the sampling space) keeps every revealed share
    fixed while switching the secret from `s₀` to `s₁`. -/
theorem priv_coupling (rp : Fin d → ZMod p) (hrp : ∀ j, rp j ≠ 0) (s0 s1 : ZMod p) :
    rHoare eqPre (PrivGame rp s0 s1 true) (PrivGame rp s0 s1 false) eqPost := by
  simp only [PrivGame, Bool.false_eq_true, if_true, if_false]
  apply rHoare_bij_step (Equiv.addRight (transVec rp s0 s1))
  intro a
  apply rHoare_ret
  intro h₁ h₂ hpre
  exact ⟨funext fun j => (shareVal_translate rp hrp s0 s1 a j).symm, hpre⟩

/-- **Shamir `(t-1)`-share perfect privacy.** For any `t-1` nonzero evaluation
    points, any two secrets `s₀, s₁`, and any adversary `A`, the privacy advantage
    is exactly `0`: any `t-1` shares are uniform and independent of the secret. -/
theorem shamir_perfect_privacy (rp : Fin d → ZMod p) (hrp : ∀ j, rp j ≠ 0)
    (s0 s1 : ZMod p) (A : (Fin d → ZMod p) → SPComp Bool) :
    PrivAdv rp s0 s1 A = 0 :=
  advantage_zero_of_rHoare _ _ (priv_coupling rp hrp s0 s1) A

/-- A share at a nonzero evaluation point varies with the secret: with the free
    coefficients fixed to zero, two distinct secrets give distinct shares at the
    point `1 ≠ 0`. Privacy therefore relies on the random free coefficients (and
    the `rp j ≠ 0` hypothesis that keeps the revealed points off the constant
    term), not on the share function discarding the secret. -/
theorem shamir_share_depends_on_secret :
    ∃ (s₀ s₁ : ZMod p) (coeffs : Fin d → ZMod p) (x : ZMod p),
      s₀ ≠ s₁ ∧ x ≠ 0 ∧ shareVal s₀ coeffs x ≠ shareVal s₁ coeffs x :=
  ⟨0, 1, 0, 1, zero_ne_one, one_ne_zero, by simp [shareVal]⟩

/-! ## Reflection into the Package / UC Stack

The shallow `shamir_perfect_privacy` bounds a single distinguisher applied to the
two privacy-game bodies. This section lifts it to a composable statement about deep
nominal packages linked with an arbitrary adversary package, following the stack
`shallow game → rawCode% → NomPackage.ofOracle → DeepNomAdvantage → sdist → UC`
via the shared `CatCryptCore.Deep.ReflectUCHelpers` combinators. The privacy game
samples a free-coefficient vector then returns the revealed shares (heap-independent),
so the shallow coupling `priv_coupling` (for nonzero revealed points `hrp`) upgrades
to a full `SPComp` equality of the two reflected bodies
(`spcomp_eq_of_isPure_coupling`), and the whole stack follows with no purity bridge
on the adversary. -/

open CatCrypt.Deep

/-- The reflected `(t-1)`-share privacy-game body for bit `b`: sample a uniform
    free-coefficient vector `a` and reveal the shares at the corrupted points. -/
noncomputable def shamirGameRaw (rp : Fin d → ZMod p) (s0 s1 : ZMod p) (b : Bool) :
    RawCode (Fin d → ZMod p) :=
  rawCode% (SPComp.bind (SPComp.sample (Fin d → ZMod p))
    (fun a => SPComp.pure (fun j => shareVal (if b then s0 else s1) a (rp j))))

instance instValidShamirGameRaw (rp : Fin d → ZMod p) (s0 s1 : ZMod p) (b : Bool) :
    IsValid (∅ : LocSet) (shamirGameRaw rp s0 s1 b) := by unfold shamirGameRaw; infer_instance

/-- The reflected body evaluates back to the shallow privacy game. -/
theorem shamirGameRaw_eval_shallow (rp : Fin d → ZMod p) (s0 s1 : ZMod p) (b : Bool) :
    (shamirGameRaw rp s0 s1 b).eval = PrivGame rp s0 s1 b := by
  simp only [shamirGameRaw, RawCode.eval]; rfl

/-- The privacy game is heap-independent (a uniform coefficient sample then pure
    share reveals). -/
theorem shamir_game_isPure (rp : Fin d → ZMod p) (s0 s1 : ZMod p) (b : Bool) :
    SPComp.IsPure (PrivGame rp s0 s1 b) := by
  unfold PrivGame
  exact SPComp.bind_isPure (SPComp.sample_isPure _) (fun _ => SPComp.pure_isPure _)

/-- The two reflected bodies (shares of `s0` vs. `s1`) have equal evaluations: for
    nonzero revealed points the coupling `priv_coupling` upgrades to `SPComp`
    equality. -/
theorem shamirGameRaw_eval_eq (rp : Fin d → ZMod p) (hrp : ∀ j, rp j ≠ 0) (s0 s1 : ZMod p) :
    (shamirGameRaw rp s0 s1 true).eval = (shamirGameRaw rp s0 s1 false).eval := by
  rw [shamirGameRaw_eval_shallow, shamirGameRaw_eval_shallow]
  exact spcomp_eq_of_isPure_coupling (shamir_game_isPure rp s0 s1 true)
    (shamir_game_isPure rp s0 s1 false) (priv_coupling rp hrp s0 s1)

/-- Real privacy game as an oracle-exporting nominal package (shares `s0`). -/
noncomputable def shamirGameTrue (rp : Fin d → ZMod p) (s0 s1 : ZMod p) : NomPackage :=
  NomPackage.ofOracle 1 Unit (Fin d → ZMod p) (fun _ => shamirGameRaw rp s0 s1 true)

/-- Ideal privacy game as an oracle-exporting nominal package (shares `s1`). -/
noncomputable def shamirGameFalse (rp : Fin d → ZMod p) (s0 s1 : ZMod p) : NomPackage :=
  NomPackage.ofOracle 1 Unit (Fin d → ZMod p) (fun _ => shamirGameRaw rp s0 s1 false)

/-- **Zero deep-nominal advantage against every adversary package** (nonzero points). -/
theorem shamir_deepnom_zero (rp : Fin d → ZMod p) (hrp : ∀ j, rp j ≠ 0)
    (s0 s1 : ZMod p) (A : NomPackage) :
    DeepNomAdvantage (shamirGameTrue rp s0 s1) (shamirGameFalse rp s0 s1) A = 0 :=
  deepNomAdvantage_ofOracle_zero _ _ (fun _ => shamirGameRaw_eval_eq rp hrp s0 s1) A

/-- **Statistical distance zero** between the two linked-game families. -/
theorem shamir_sdist_zero (rp : Fin d → ZMod p) (hrp : ∀ j, rp j ≠ 0) (s0 s1 : ZMod p) :
    sdist (fun A : NomPackage => runPkg (DeepPackage.link A.pkg (shamirGameTrue rp s0 s1).pkg))
          (fun A : NomPackage => runPkg (DeepPackage.link A.pkg (shamirGameFalse rp s0 s1).pkg)) = 0 :=
  sdist_ofOracle_zero _ _ (fun _ => shamirGameRaw_eval_eq rp hrp s0 s1)

/-- **Package-level perfect privacy** (`NomPkgSecure`). -/
theorem shamir_nompkg_secure (rp : Fin d → ZMod p) (hrp : ∀ j, rp j ≠ 0) (s0 s1 : ZMod p) :
    NomPkgSecure (shamirGameTrue rp s0 s1) (shamirGameFalse rp s0 s1) (fun _ => 0) :=
  nomPkgSecure_ofOracle _ _ (fun _ => shamirGameRaw_eval_eq rp hrp s0 s1)

/-- **Perfect UC emulation** of the linked-game families over the trivial-leak
    interface (`out = Bool`, `leak = Empty`) with the identity simulator
    (composition plumbing). -/
theorem shamir_uc (rp : Fin d → ZMod p) (hrp : ∀ j, rp j ≠ 0) (s0 s1 : ZMod p) :
    UCEmulates 0 ⟨NomPackage, Bool, Empty, Empty, Bool⟩
      (fun A => SPComp.map (Sum.inl : Bool → Bool ⊕ Empty)
        (runPkg (DeepPackage.link A.pkg (shamirGameTrue rp s0 s1).pkg)))
      (fun A => SPComp.map (Sum.inl : Bool → Bool ⊕ Empty)
        (runPkg (DeepPackage.link A.pkg (shamirGameFalse rp s0 s1).pkg))) :=
  uc_ofOracle _ _ (fun _ => shamirGameRaw_eval_eq rp hrp s0 s1)

end CatCrypt.Examples.ShamirSecretSharing
