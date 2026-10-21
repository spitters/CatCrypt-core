/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.FiatShamirROM.Reduction
public import CatCryptCore.Crypto.Assumptions.DLGroupParam
public import CatCryptCore.Crypto.FiatShamirROM.LinearRelation

/-!
# Schnorr signatures as an instance of the generic Fiat–Shamir theorem

The Schnorr Σ-protocol over a `GroupParam` as a `FiatShamirROM.Sigma`: statements
are public keys `g^w`, commitments `g^r`, responses `r + e·w`, the simulator
answers `(g^z · pk^(−e), z)`, and the extractor is `(z₁ − z₂)/(e₁ − e₂)`. It is
special sound, perfect HVZK, and each commitment has probability `1/|Scalar|`.
Its relation game is the discrete-logarithm game over the group.

## Main definitions

* `schnorrSigma gp` — the Schnorr Σ-protocol
* `dlOfWitness gp B` — a witness-finding adversary as a discrete-logarithm adversary

## Main results

* `schnorrSigma_verify_eq` — the Schnorr verifier is the verifier of the linear
  Σ-protocol `dlogSigma gp` on constant vectors
* `schnorrSigma_specialSound`, `schnorrSigma_complete`, `schnorrSigma_uniqueResp` —
  from the properties of `dlogSigma gp`
* `schnorrSigma_perfectHVZK`, `schnorrSigma_commitBound`
* `relAdvantage_schnorrSigma` — the relation game of `schnorrSigma gp` is the
  discrete-logarithm game
* `schnorr_fs_rom_eufcma` — for every adversary against the Fiat–Shamir game over
  `schnorrSigma gp` with at most `qH` hash and `qS` signing queries,
  `ε'·(ε'/(qH + 1) − 1/|Scalar|) ≤ DL_Advantage (dlOfWitness (extractReduction A))`
  with `ε' = eufcmaAdvantage A − qS·(qH + 1 + qS)/|Scalar|`

## References

* C. P. Schnorr, *Efficient signature generation by smart cards*, J. Cryptology
  4(3), 1991.
* D. Pointcheval, J. Stern, *Security arguments for digital signatures and blind
  signatures*, J. Cryptology 13(3), 2000.
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal

namespace CatCrypt.Examples.GroupParam

variable (gp : GroupParam)

/-- Cancellation of a common left summand under subtraction:
`(s + a) − (s + b) = a − b`. -/
theorem scalarSub_add_left (s a b : gp.Scalar) :
    gp.scalarSub (gp.scalarAdd s a) (gp.scalarAdd s b) = gp.scalarSub a b := by
  simp only [gp.scalarSub_eq, gp.scalarNeg_add_distrib]
  rw [gp.scalarAdd_assoc, ← gp.scalarAdd_assoc a, gp.scalarAdd_comm a (gp.scalarNeg s),
    gp.scalarAdd_assoc (gp.scalarNeg s), ← gp.scalarAdd_assoc s, gp.scalarAdd_neg,
    gp.scalarZero_add]

/-- Two accepting Schnorr transcripts `g^zᵢ = a · pk^eᵢ` with the same commitment
and distinct challenges determine the discrete logarithm of `pk` as
`(z₁ − z₂)/(e₁ − e₂)`. -/
theorem exp_extract_eq (pk a : gp.G) (e₁ e₂ z₁ z₂ : gp.Scalar)
    (hv₁ : gp.exp z₁ = gp.groupMul a (gp.groupExp pk e₁))
    (hv₂ : gp.exp z₂ = gp.groupMul a (gp.groupExp pk e₂)) (hne : e₁ ≠ e₂) :
    gp.exp (gp.scalarDiv (gp.scalarSub z₁ z₂) (gp.scalarSub e₁ e₂)) = pk := by
  obtain ⟨k, hk⟩ := gp.exp_surj pk
  obtain ⟨s, hs⟩ := gp.exp_surj a
  have hge : ∀ e, gp.groupExp pk e = gp.exp (gp.scalarMul k e) := by
    intro e; rw [← hk, gp.groupExp_exp]
  have hz₁ : z₁ = gp.scalarAdd s (gp.scalarMul k e₁) := gp.exp_inj _ _ (by
    rw [hv₁, ← hs, hge, ← gp.exp_add])
  have hz₂ : z₂ = gp.scalarAdd s (gp.scalarMul k e₂) := gp.exp_inj _ _ (by
    rw [hv₂, ← hs, hge, ← gp.exp_add])
  have hz_diff : gp.scalarSub z₁ z₂ = gp.scalarMul k (gp.scalarSub e₁ e₂) := by
    rw [hz₁, hz₂, scalarSub_add_left]
    simp only [gp.scalarSub_eq]
    rw [← scalarMul_neg gp, ← gp.scalarMul_add]
  have he_ne : gp.scalarSub e₁ e₂ ≠ gp.scalarZero := gp.scalarSub_ne_zero e₁ e₂ hne
  rw [← hk, hz_diff, gp.mul_div_cancel _ _ he_ne]

/-- The simulated commitment `g^z · (g^sk)^(−e)` for the response `z = r + e·sk`
is `g^r`. -/
theorem sim_commit_eq (sk r e : gp.Scalar) :
    gp.groupMul (gp.exp (gp.scalarAdd r (gp.scalarMul e sk)))
      (gp.groupInv (gp.groupExp (gp.exp sk) e)) = gp.exp r := by
  rw [gp.groupExp_exp, ← gp.groupExp_exp, gp.groupInv_groupExp, gp.groupExp_exp, ← gp.exp_add,
    scalarMul_neg, gp.scalarMul_comm sk e, gp.scalarAdd_assoc, gp.scalarAdd_neg,
    gp.scalarAdd_zero]

/-- Translation by a scalar as an equivalence. -/
def addEquiv (c : gp.Scalar) : gp.Scalar ≃ gp.Scalar where
  toFun r := gp.scalarAdd r c
  invFun z := gp.scalarAdd z (gp.scalarNeg c)
  left_inv r := by simp only [gp.scalarAdd_assoc, gp.scalarAdd_neg, gp.scalarAdd_zero]
  right_inv z := by simp only [gp.scalarAdd_assoc, gp.scalarNeg_add, gp.scalarAdd_zero]

end CatCrypt.Examples.GroupParam

namespace CatCrypt.Crypto.FiatShamirROM

open CatCrypt.Crypto CatCrypt.Examples

variable (gp : GroupParam)

/-- The Schnorr Σ-protocol for the discrete-logarithm relation `g^w = pk`, with
uniform key generation. -/
noncomputable def schnorrSigma : Sigma where
  Stmt := gp.G
  Wit := gp.Scalar
  Com := gp.G
  Ch := gp.Scalar
  Resp := gp.Scalar
  Rand := gp.Scalar
  SimRand := gp.Scalar
  inhWit := ⟨gp.scalarZero⟩
  rel x w := gp.exp w = x
  gen := (PMF.uniformOfFintype gp.Scalar).map fun w => (gp.exp w, w)
  commit _ _ r := gp.exp r
  respond _ w r e := gp.scalarAdd r (gp.scalarMul e w)
  verify x a e z := gp.exp z == gp.groupMul a (gp.groupExp x e)
  simulate x e z := (gp.groupMul (gp.exp z) (gp.groupInv (gp.groupExp x e)), z)
  extract _ _ e z e' z' := gp.scalarDiv (gp.scalarSub z z') (gp.scalarSub e e')

/-- The Schnorr verifier is the verifier of the linear Σ-protocol `dlogSigma gp` on
constant vectors. -/
theorem schnorrSigma_verify_eq (pk a : gp.G) (e z : gp.Scalar) :
    (schnorrSigma gp).verify pk a e z = (dlogSigma gp).verify pk (fun _ => a) e (fun _ => z) := by
  rw [Bool.eq_iff_iff, dlogSigma_verify_iff]
  exact beq_iff_eq

theorem schnorrSigma_specialSound : (schnorrSigma gp).SpecialSound := by
  intro (pk : gp.G) (a : gp.G) (e₁ : gp.Scalar) (z₁ : gp.Scalar) (e₂ : gp.Scalar)
    (z₂ : gp.Scalar) hv₁ hv₂ hne
  rw [schnorrSigma_verify_eq] at hv₁ hv₂
  exact (dlogRelation_holds_iff _ _).mp (dlogSigma_specialSound gp pk _ e₁ _ e₂ _ hv₁ hv₂ hne)

/-- The honest Schnorr transcript `(g^r, e, r + e·w)` for `g^w = pk` verifies. -/
theorem schnorrSigma_complete : (schnorrSigma gp).Complete := by
  intro (pk : gp.G) (w : gp.Scalar) hw (r : gp.Scalar) (e : gp.Scalar)
  change (schnorrSigma gp).verify pk (gp.exp r) e (gp.scalarAdd r (gp.scalarMul e w)) = true
  rw [schnorrSigma_verify_eq, ← dlogRelation_map pk (fun _ => r)]
  exact dlogSigma_complete gp pk (fun _ => w) ((dlogRelation_holds_iff _ _).mpr hw) (fun _ => r) e

/-- Two accepted Schnorr responses `g^z = g^z' = a · pk^e` are equal. -/
theorem schnorrSigma_uniqueResp : (schnorrSigma gp).UniqueResp := by
  intro (pk : gp.G) (a : gp.G) (e : gp.Scalar) (z : gp.Scalar) (z' : gp.Scalar) h h'
  rw [schnorrSigma_verify_eq] at h h'
  exact congrFun (dlogSigma_uniqueResp gp pk _ e _ _ h h') 0

omit gp in
theorem map_uniformOfFintype_equiv' {α : Type} [Fintype α] [Nonempty α] (c : α ≃ α) :
    (PMF.uniformOfFintype α).map c = PMF.uniformOfFintype α := by
  classical
  ext z
  rw [PMF.map_apply, tsum_eq_single (c.symm z)]
  · simp
  · intro r hr
    rw [if_neg]
    intro h
    exact hr (by rw [h, Equiv.symm_apply_apply])

theorem schnorrSigma_perfectHVZK : (schnorrSigma gp).PerfectHVZK := by
  intro x w hxw e
  simp only [schnorrSigma, PMF.support_map] at hxw
  obtain ⟨w', _, hw⟩ := hxw
  obtain ⟨hx, hw'⟩ := Prod.mk.inj hw
  subst hx
  subst hw'
  change (PMF.uniformOfFintype gp.Scalar).map
      (fun r => (gp.exp r, gp.scalarAdd r (gp.scalarMul e w'))) =
    (PMF.uniformOfFintype gp.Scalar).map
      (fun z => (gp.groupMul (gp.exp z) (gp.groupInv (gp.groupExp (gp.exp w') e)), z))
  conv_rhs => rw [← map_uniformOfFintype_equiv' (gp.addEquiv (gp.scalarMul e w')),
    PMF.map_comp]
  congr 1
  funext r
  simp only [Function.comp_apply, GroupParam.addEquiv, Equiv.coe_fn_mk]
  rw [gp.sim_commit_eq w' r e]

theorem schnorrSigma_commitBound :
    (schnorrSigma gp).CommitBound (1 / Fintype.card gp.Scalar) := by
  classical
  intro x w _ a
  change (PMF.uniformOfFintype gp.Scalar).toOuterMeasure {r | gp.exp r = a} ≤ _
  rw [PMF.toOuterMeasure_uniformOfFintype_apply, one_div, ENNReal.div_eq_inv_mul]
  refine mul_le_of_le_one_right (by positivity) ?_
  exact Nat.cast_le_one.mpr (Fintype.card_le_one_iff.mpr fun r s =>
    Subtype.ext (gp.exp_inj _ _ ((show gp.exp r.1 = a from r.2).trans
      (show gp.exp s.1 = a from s.2).symm)))

/-- A witness-finding adversary for `schnorrSigma gp` as a discrete-logarithm
adversary. -/
noncomputable def dlOfWitness (B : gp.G → PMF gp.Scalar) : gp.G → SPComp gp.Scalar :=
  fun pk h => (B pk).map fun w => some (w, h)

/-- The relation game of `schnorrSigma gp` is the discrete-logarithm game. -/
theorem relAdvantage_schnorrSigma (B : gp.G → PMF gp.Scalar) :
    (schnorrSigma gp).relAdvantage B = gp.DL_Advantage (dlOfWitness gp B) := by
  have hgame : gp.dlGame (dlOfWitness gp B) = liftPMF
      ((PMF.uniformOfFintype gp.Scalar).bind fun w =>
        (B (gp.exp w)).map fun w' => gp.exp w' == gp.exp w) := by
    funext h
    simp only [GroupParam.dlGame, liftPMF, SPComp.monad_bind_eq, SPComp.bind,
      SPComp.sample, SPComp.pure, dlOfWitness, SDistr.bind, SDistr.uniform, SDistr.pure]
    simp only [PMF.bind_bind, Function.comp_def, PMF.pure_bind, ← PMF.bind_pure_comp]
  unfold Sigma.relAdvantage Sigma.relGame GroupParam.DL_Advantage
  rw [hgame, OracleForking.prTrue_pmfGame, OracleForking.prTrue_pmfGame]
  simp only [schnorrSigma, PMF.bind_map, Function.comp_def, PMF.toOuterMeasure_bind_apply,
    PMF.toOuterMeasure_map_apply]
  refine tsum_congr fun w => ?_
  congr 2

variable {gp} {M : Type} [DecidableEq M] {qH qS : ℕ}

/-- **The generic Fiat–Shamir theorem for Schnorr.** For every adversary against
the Fiat–Shamir game over `schnorrSigma gp` with at most `qH` hash and `qS`
signing queries,
`ε'·(ε'/(qH + 1) − 1/|Scalar|) ≤ DL_Advantage (dlOfWitness (extractReduction A))`
with `ε' = eufcmaAdvantage A − qS·(qH + 1 + qS)/|Scalar|`. The discrete-logarithm
adversary runs `A` at most twice and computes `(z₁ − z₂)/(e₁ − e₂)`. -/
theorem schnorr_fs_rom_eufcma (A : Adversary (schnorrSigma gp) M qH qS) :
    (eufcmaAdvantage A - ((qS * (qH + 1 + qS) : ℕ) : ℝ≥0∞) / Fintype.card gp.Scalar) *
        ((eufcmaAdvantage A - ((qS * (qH + 1 + qS) : ℕ) : ℝ≥0∞) / Fintype.card gp.Scalar) /
            ((qH + 1 : ℕ) : ℝ≥0∞) - 1 / Fintype.card gp.Scalar) ≤
      gp.DL_Advantage (dlOfWitness gp (extractReduction A)) := by
  have h := fiatShamir_rom_eufcma (schnorrSigma_specialSound gp) (schnorrSigma_perfectHVZK gp)
    (schnorrSigma_commitBound gp) A
  rw [← div_eq_mul_one_div] at h
  exact (relAdvantage_schnorrSigma gp (extractReduction A)) ▸ h

end CatCrypt.Crypto.FiatShamirROM
