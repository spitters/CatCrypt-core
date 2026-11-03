/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.X3DHSquareHops
public import CatCryptCore.Crypto.Assumptions.GapDH

/-!
# The bad event of the X3DH square under the gap Diffie–Hellman assumption

`X3DHSquareHops.x3dh_advantage_le_badGame` bounds the advantage of an oracle adversary `B`
between the real and the simulated X3DH game by the probability `badGame G B true` of the bad
event `DH1Hit`: the key-derivation table of the simulated world comes to hold an input whose
initiator `a` and responder `b` are uncorrupt and whose `DH1` is `g^{ik_a · spk_b}`. This module
bounds that probability by gap Diffie–Hellman advantages of explicit reductions, and composes the
bound into the UC statement of X3DH against `F_AKE`.

**The problem.** `gapDHDef G` is the gap Diffie–Hellman problem of the group `G : DHGroup S W`
as an instance of `Assumptions.GapDHDef`: `cdh X Y = Y^{dlog X}`, key generation of a uniform
exponent, and the decision oracle `ddhOracle (gapDHDef G)`, which accepts `(g^x, Y, Z)` when
`Z = Y^x`.

**The finite-party predicate.** `NamesIn P B`: on every path, the oracle adversary `B` starts
sessions only between parties of the finite set `P` and queries the key derivation only at inputs
whose initiator and responder are in `P`. Party identifiers are natural numbers and a public key
may be read before the party is corrupted, so the reduction guesses the pair `(a, b)`; the bound
is a sum over the pairs of `P`.

**The reduction.** `gdhRed G a b B`, on the challenge `(X, Y)` with the decision oracle `O`, runs
`B` against the world of the reduction (`stepR`), a copy of the simulated world in which
* the long-term secrets of every party are drawn as in the simulator, and the identity key of `a`
  is `IK_a = X · g^u` and the signed prekey of `b` is `SPK_b = Y · g^v` for the drawn `u`, `v`;
* the Diffie–Hellman values that need `ik_a = x + u` or `spk_b = y + v` are symbolic: in an input
  `Inp (W ⊕ W)`, `inr E` stands for `E^{ik_a}` in `DH1` and `DH2` and for `E^{spk_b}` in `DH3`;
* the lookups in the key-derivation table and the comparisons with the partner's recorded input
  are decided with `O` (`symEq`: `w = E^k` is the triple `(g^k, E, w)` and `E^k = E'^k` the
  triple `(g^k, E · E'^{-1}, 1)`);
* `F_AKE` runs as in the simulated world.
At the end it outputs `w · (X^v Y^u g^{uv})^{-1}` for the first `DH1 = w` of an input with
initiator `a` and responder `b` that `O` accepts for `(IK_a, SPK_b)` (`extractR`).

**The proof.**
1. *Shifted draws.* The simulated world whose draws of `ik_a` and `spk_b` are shifted by `x` and
   `y` is the simulated world, since a shift is a bijection of the draws
   (`simGame_oracle_eq_trans`).
2. *Coupling.* On the same draw, the shifted simulated world and the world of the reduction give
   the same answer and reach states of the relation `Rel`, unless the step corrupts `a` or `b`
   (`rel_start`, `step_rel`). Corruption is never undone, and `DH1HitAB` requires `a` and `b`
   uncorrupt.
3. *Bad flags under the coupling* (`flag_le_of_coupling`): the flag of `DH1HitAB` in the simulated
   world is set at most as often as the flag of `Bad2`, the same input in the symbolic table with
   a known `DH1`, in the world of the reduction (`pairBad_le_red`).
4. *Extraction.* `Bad2` persists along the steps (`Mono`), and on `Bad2` the extraction outputs
   `g^{xy}` (`extractR_of_bad2`); averaging over `x`, `y` gives the advantage of `gdhRed`
   (`pairBad_le_gapDH`).
5. *Union bound* over the pairs of `P`, under the invariant `InvP` that the table and the records
   name parties of `P` (`badGame_le_gapDH`).

## Main definitions

* `gapDHDef`: the gap Diffie–Hellman problem of a `DHGroup`.
* `symEq`, `inpEq`, `slookup`, `sroDet`: symbolic values and their equality by the decision
  oracle.
* `startR`, `stepR`, `oracleR`, `extractR`: the world of the reduction.
* `redTree`, `redPMF`, `gdhRed`: the reduction as a program, its output, and the GDH adversary.
* `NamesIn`: the finite-party predicate.
* `gdhBound`: the bound of the square.

## Main results

* `symEq_ddh`, `inpEq_ddh`, `slookup_ddh`, `sroDet_ddh`: correctness of the symbolic equality.
* `simGame_oracle_eq_trans`: the shifted simulated world is the simulated world.
* `rel_start`, `step_rel`: the coupling of a step.
* `flag_le_of_coupling`, `run_flag_le_final`, `run_flag_union_le`, `run_flag_le_of_inv_on`:
  bad flags under a coupling, at the final state, over a finite union, and along an invariant on a
  class of queries.
* `pairBad_le_gapDH`: the bad event of a pair is at most the GDH advantage of `gdhRed`.
* `badGame_le_gapDH`: `badGame G B true ≤ ∑ a ∈ P, ∑ b ∈ P, GapDH_Advantage (gapDHDef G)
  (gdhRed G a b B)` for `B` naming only parties of `P`.
* `x3dh_realizesSim_gapDH`: X3DH realizes `F_AKE` behind `x3dhSim` with the bound `gdhBound`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.AKE.X3DHSquareGDH

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Relational
open CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.PAKE.DHExtract CatCrypt.Crypto.Assumptions
open CatCrypt.Crypto.AKE.X3DHSquare CatCrypt.Crypto.AKE.X3DHSquareHops
open CatCrypt.Crypto.OracleGameUpToBad
open scoped ENNReal

/-! ## The gap Diffie–Hellman problem of a group -/

section GDH

variable {S W : Type} [Field S] [Fintype S] [SampleableType W] (G : DHGroup S W)

/-- **The gap Diffie–Hellman problem of the group `G`** as an instance of `GapDHDef`: the
Diffie–Hellman function `cdh X Y = Y^{dlog X}`, the key agreement `dh x Y = Y^{dlog x}` on a
private key stored as its public value, and the key generation of a uniform exponent `s` with
the pair `(g^s, g^s)`. The game samples two exponents and wins when the adversary, with the
decision oracle of `cdh`, outputs `g^{xy}` on `(g^x, g^y)`. -/
noncomputable def gapDHDef : GapDHDef W where
  dh x Y := G.exp Y (G.dlog x)
  cdh X Y := G.exp Y (G.dlog X)
  keygen := liftPMF ((PMF.uniformFintype S).map fun s => (G.pub s, G.pub s))
  keygen_isPure := liftPMF_isPure _

/-- The decision oracle of `gapDHDef G` on public values: `(g^x, Y, Z)` is accepted when
`Z = Y^x`. -/
theorem ddhOracle_pub (x : S) (Y Z : W) :
    ddhOracle (gapDHDef G) (G.pub x) Y Z = decide (Z = G.exp Y x) := by
  simp only [ddhOracle, gapDHDef, DHGroup.dlog_pub]

/-- The Diffie–Hellman value of two public values. -/
theorem cdh_pub (x y : S) : (gapDHDef G).cdh (G.pub x) (G.pub y) = G.pub (x * y) := by
  simp only [gapDHDef, DHGroup.dlog_pub, G.exp_pub, mul_comm]

end GDH

/-! ## Oracle adversaries whose queries lie in a class -/

/-- `AllQ Q A`: every query of `A`, on every path, satisfies `Q`. -/
def AllQ {D R α : Type} (Q : D → Prop) : OracleAdv D R α → Prop
  | .ret _ => True
  | .rand _ k => ∀ c, AllQ Q (k c)
  | .query d k => Q d ∧ ∀ r, AllQ Q (k r)

/-! ## Bad flags under a coupling of draws -/

section FlagCoupling

variable {σ σ₁ σ₂ D R α Ω : Type} [Fintype Ω] [Nonempty Ω]

theorem toOuterMeasure_le_one {β : Type} (p : PMF β) (T : Set β) : p.toOuterMeasure T ≤ 1 :=
  (p.toOuterMeasure.mono (Set.subset_univ T)).trans_eq
    ((PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr (Set.subset_univ _))

/-- A flagged oracle that is the image of a uniform draw. -/
theorem flagWhen_uniform_map (f : σ → D → Ω → R × σ) (bad : σ → Prop) [DecidablePred bad]
    (s : σ) (b : Bool) (d : D) :
    OracleAdv.flagWhen (fun _ _ x => bad x.2) (fun s d => (PMF.uniformFintype Ω).map (f s d))
        (s, b) d =
      (PMF.uniformFintype Ω).map fun r => ((f s d r).1, ((f s d r).2, b || decide (bad (f s d r).2))) := by
  simp only [OracleAdv.flagWhen, PMF.map_comp]
  rfl

/-- A run from a set flag keeps it. -/
theorem run_flag_true_one (O : σ → D → PMF (R × σ)) (bad : σ → D → R × σ → Prop)
    [∀ s d x, Decidable (bad s d x)] (A : OracleAdv D R α) (s : σ) :
    (OracleAdv.run (OracleAdv.flagWhen bad O) A (s, true)).toOuterMeasure {y | y.2.2 = true} = 1 := by
  induction A generalizing s with
  | ret a =>
    rw [OracleAdv.run_ret, PMF.toOuterMeasure_apply_eq_one_iff]
    intro y hy
    rw [PMF.support_pure, Set.mem_singleton_iff] at hy
    subst hy
    rfl
  | rand p k ih =>
    rw [OracleAdv.run_rand, PMF.toOuterMeasure_bind_apply]
    simp only [ih, mul_one, PMF.tsum_coe]
  | query d k ih =>
    rw [OracleAdv.run_query, PMF.toOuterMeasure_bind_apply]
    have h : ∀ x ∈ (OracleAdv.flagWhen bad O (s, true) d).support, x.2.2 = true := by
      intro x hx
      simp only [OracleAdv.flagWhen, PMF.support_map, Set.mem_image] at hx
      obtain ⟨z, -, rfl⟩ := hx
      simp
    calc _ = ∑' x, (OracleAdv.flagWhen bad O (s, true) d) x * 1 := by
          refine tsum_congr fun x => ?_
          by_cases hx : x ∈ (OracleAdv.flagWhen bad O (s, true) d).support
          · obtain ⟨u, v, w⟩ := x
            have hw : w = true := h _ hx
            subst hw
            rw [ih]
          · rw [PMF.apply_eq_zero_iff _ _ |>.mpr hx, zero_mul, zero_mul]
      _ = 1 := by simp only [mul_one, PMF.tsum_coe]

/-- A run from a dead state never sets the flag. -/
theorem run_flag_dead_zero (f₁ : σ₁ → D → Ω → R × σ₁) (Dead bad₁ : σ₁ → Prop)
    [DecidablePred bad₁] (hdead : ∀ s d r, Dead s → Dead (f₁ s d r).2)
    (hdb : ∀ s, Dead s → ¬ bad₁ s) (A : OracleAdv D R α) (s : σ₁) (hs : Dead s) :
    (OracleAdv.run (OracleAdv.flagWhen (fun _ _ x => bad₁ x.2)
      (fun s d => (PMF.uniformFintype Ω).map (f₁ s d))) A (s, false)).toOuterMeasure
        {y | y.2.2 = true} = 0 := by
  induction A generalizing s with
  | ret a =>
    rw [OracleAdv.run_ret, PMF.toOuterMeasure_pure_apply]
    simp
  | rand p k ih =>
    rw [OracleAdv.run_rand, PMF.toOuterMeasure_bind_apply]
    simp only [fun b => ih b s hs, mul_zero, tsum_zero]
  | query d k ih =>
    rw [OracleAdv.run_query, flagWhen_uniform_map, PMF.bind_map, PMF.toOuterMeasure_bind_apply]
    refine ENNReal.tsum_eq_zero.mpr fun r => ?_
    simp only [Function.comp_apply, Bool.false_or, decide_eq_false (hdb _ (hdead s d r hs))]
    rw [ih _ _ (hdead s d r hs), mul_zero]

/-- **A bad flag under a coupling of draws.** Let two oracles be images of the same uniform draw,
and let every step from related states either reach a dead state of the first oracle, from which
its bad event never occurs, or give the same answer and reach related states. When the bad event
of the first oracle on related states implies the bad event of the second, the first run sets its
flag with at most the probability with which the second does. -/
theorem flag_le_of_coupling (f₁ : σ₁ → D → Ω → R × σ₁) (f₂ : σ₂ → D → Ω → R × σ₂)
    (Rel : σ₁ → σ₂ → Prop) (Dead bad₁ : σ₁ → Prop) (bad₂ : σ₂ → Prop) [DecidablePred bad₁]
    [DecidablePred bad₂] (hdead : ∀ s d r, Dead s → Dead (f₁ s d r).2)
    (hdb : ∀ s, Dead s → ¬ bad₁ s) (hbad : ∀ s₁ s₂, Rel s₁ s₂ → bad₁ s₁ → bad₂ s₂)
    (hstep : ∀ s₁ s₂ d r, Rel s₁ s₂ → Dead (f₁ s₁ d r).2 ∨
      ((f₁ s₁ d r).1 = (f₂ s₂ d r).1 ∧ Rel (f₁ s₁ d r).2 (f₂ s₂ d r).2))
    (A : OracleAdv D R α) (s₁ : σ₁) (s₂ : σ₂) (h : Rel s₁ s₂) :
    (OracleAdv.run (OracleAdv.flagWhen (fun _ _ x => bad₁ x.2)
      (fun s d => (PMF.uniformFintype Ω).map (f₁ s d))) A (s₁, false)).toOuterMeasure
        {y | y.2.2 = true} ≤
    (OracleAdv.run (OracleAdv.flagWhen (fun _ _ x => bad₂ x.2)
      (fun s d => (PMF.uniformFintype Ω).map (f₂ s d))) A (s₂, false)).toOuterMeasure
        {y | y.2.2 = true} := by
  induction A generalizing s₁ s₂ with
  | ret a =>
    rw [OracleAdv.run_ret, PMF.toOuterMeasure_pure_apply]
    simp
  | rand p k ih =>
    rw [OracleAdv.run_rand, OracleAdv.run_rand, PMF.toOuterMeasure_bind_apply,
      PMF.toOuterMeasure_bind_apply]
    refine ENNReal.tsum_le_tsum fun b => ?_
    gcongr
    exact ih b s₁ s₂ h
  | query d k ih =>
    rw [OracleAdv.run_query, OracleAdv.run_query, flagWhen_uniform_map, flagWhen_uniform_map,
      PMF.bind_map, PMF.bind_map, PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
    refine ENNReal.tsum_le_tsum fun r => ?_
    gcongr
    simp only [Function.comp_apply, Bool.false_or]
    by_cases hb : bad₁ (f₁ s₁ d r).2
    · rcases hstep s₁ s₂ d r h with hd | ⟨-, hr⟩
      · exact absurd hb (hdb _ hd)
      · rw [decide_eq_true hb, decide_eq_true (hbad _ _ hr hb), run_flag_true_one,
          run_flag_true_one]
    · rw [decide_eq_false hb]
      rcases hstep s₁ s₂ d r h with hd | ⟨ho, hr⟩
      · rw [run_flag_dead_zero f₁ Dead bad₁ hdead hdb _ _ hd]
        exact zero_le
      · by_cases hb₂ : bad₂ (f₂ s₂ d r).2
        · rw [decide_eq_true hb₂, run_flag_true_one]
          exact toOuterMeasure_le_one _ _
        · rw [decide_eq_false hb₂, ho]
          exact ih _ _ _ hr

/-- The support of a run flagged by an event that the oracle keeps: a set flag means that the
event holds at the final state. -/
theorem run_flag_support (O : σ → D → PMF (R × σ)) (P : σ → Prop) [DecidablePred P]
    (hmono : ∀ s d, P s → ∀ x ∈ (O s d).support, P x.2) (A : OracleAdv D R α) (s : σ) (b : Bool)
    (hb : b = true → P s) :
    ∀ z ∈ (OracleAdv.run (OracleAdv.flagWhen (fun _ _ x => P x.2) O) A (s, b)).support,
      z.2.2 = true → P z.2.1 := by
  induction A generalizing s b with
  | ret a =>
    intro z hz hf
    rw [OracleAdv.run_ret, PMF.support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact hb hf
  | rand p k ih =>
    intro z hz
    rw [OracleAdv.run_rand, PMF.mem_support_bind_iff] at hz
    obtain ⟨c, -, hc⟩ := hz
    exact ih c s b hb z hc
  | query d k ih =>
    intro z hz
    rw [OracleAdv.run_query, PMF.mem_support_bind_iff] at hz
    obtain ⟨x, hx, hz⟩ := hz
    simp only [OracleAdv.flagWhen, PMF.support_map, Set.mem_image] at hx
    obtain ⟨w, hw, rfl⟩ := hx
    refine ih w.1 w.2 _ ?_ z hz
    intro h
    rcases Bool.or_eq_true_iff.mp h with h | h
    · exact hmono s d (hb h) w hw
    · exact of_decide_eq_true h

/-- **A flag of an event that the oracle keeps** is set at most with the probability of the event
at the final state. -/
theorem run_flag_le_final (O : σ → D → PMF (R × σ)) (P : σ → Prop) [DecidablePred P]
    (hmono : ∀ s d, P s → ∀ x ∈ (O s d).support, P x.2) (A : OracleAdv D R α) (s : σ) :
    (OracleAdv.run (OracleAdv.flagWhen (fun _ _ x => P x.2) O) A (s, false)).toOuterMeasure
        {y | y.2.2 = true} ≤ (OracleAdv.run O A s).toOuterMeasure {y | P y.2} := by
  rw [← OracleAdv.run_flagWhen_map (fun _ _ x => P x.2) O A s false,
    PMF.toOuterMeasure_map_apply]
  refine PMF.toOuterMeasure_mono _ fun z hz => ?_
  exact run_flag_support O P hmono A s false (fun h => by cases h) z hz.2 hz.1

open Classical in
/-- **The union bound over a finite family of bad events.** -/
theorem run_flag_union_le {ι : Type} (O : σ → D → PMF (R × σ)) (bad : ι → σ → Prop)
    (T : Finset ι) (A : OracleAdv D R α) (s : σ) :
    (OracleAdv.run (OracleAdv.flagWhen (fun _ _ x => ∃ i ∈ T, bad i x.2) O) A
        (s, false)).toOuterMeasure {y | y.2.2 = true} ≤
      ∑ i ∈ T, (OracleAdv.run (OracleAdv.flagWhen (fun _ _ x => bad i x.2) O) A
        (s, false)).toOuterMeasure {y | y.2.2 = true} := by
  induction T using Finset.induction_on with
  | empty =>
    rw [Finset.sum_empty]
    refine ((OracleAdv.run_flagWhen_mono O _ (fun _ _ _ => False)
      (fun _ _ _ h => by simp at h) A s).trans
        (run_flag_le_final O (fun _ => False) (fun _ _ h => h.elim) A s)).trans_eq ?_
    simp
  | insert j T hj ih =>
    rw [Finset.sum_insert hj]
    refine (OracleAdv.run_flagWhen_mono O _ (fun _ _ x => bad j x.2 ∨ ∃ i ∈ T, bad i x.2)
      (fun _ _ _ h => by simpa using h) A s).trans ?_
    refine (OracleAdv.run_flagWhen_or_le O _ _ A s).trans ?_
    gcongr

/-- **A bad flag implied by another along an invariant of the queries of a class.** -/
theorem run_flag_le_of_inv_on (O : σ → D → PMF (R × σ)) (Q : D → Prop) (I bad₁ bad₂ : σ → Prop)
    [DecidablePred bad₁] [DecidablePred bad₂]
    (hI : ∀ s d, I s → Q d → ∀ x ∈ (O s d).support, I x.2) (hb : ∀ s, I s → bad₁ s → bad₂ s)
    (A : OracleAdv D R α) (hA : AllQ Q A) (s : σ) (hs : I s) :
    (OracleAdv.run (OracleAdv.flagWhen (fun _ _ x => bad₁ x.2) O) A (s, false)).toOuterMeasure
        {y | y.2.2 = true} ≤
      (OracleAdv.run (OracleAdv.flagWhen (fun _ _ x => bad₂ x.2) O) A (s, false)).toOuterMeasure
        {y | y.2.2 = true} := by
  induction A generalizing s with
  | ret a =>
    rw [OracleAdv.run_ret, PMF.toOuterMeasure_pure_apply]
    simp
  | rand p k ih =>
    rw [OracleAdv.run_rand, OracleAdv.run_rand, PMF.toOuterMeasure_bind_apply,
      PMF.toOuterMeasure_bind_apply]
    exact ENNReal.tsum_le_tsum fun c => mul_le_mul_right (ih c (hA c) s hs) _
  | query d k ih =>
    rw [OracleAdv.run_query, OracleAdv.run_query]
    simp only [OracleAdv.flagWhen, PMF.bind_map, PMF.toOuterMeasure_bind_apply]
    refine ENNReal.tsum_le_tsum fun x => ?_
    by_cases hx : x ∈ (O s d).support
    · refine mul_le_mul_right ?_ _
      simp only [Function.comp_apply, Bool.false_or]
      have hIx := hI s d hs hA.1 x hx
      by_cases h₁ : bad₁ x.2
      · rw [decide_eq_true h₁, decide_eq_true (hb _ hIx h₁), run_flag_true_one, run_flag_true_one]
      · rw [decide_eq_false h₁]
        by_cases h₂ : bad₂ x.2
        · rw [decide_eq_true h₂, run_flag_true_one]
          exact toOuterMeasure_le_one _ _
        · rw [decide_eq_false h₂]
          exact ih x.1 (hA.2 x.1) x.2 hIx
    · rw [(PMF.apply_eq_zero_iff _ _).mpr hx, zero_mul, zero_mul]

end FlagCoupling

/-! ## Symbolic Diffie–Hellman values -/

section Sym

variable {S W K : Type} [Field S] [Fintype S] [SampleableType W] (G : DHGroup S W)

/-- The value of a symbolic Diffie–Hellman value at the secret exponent `k` of its position:
`inl w` is the known value `w`, `inr E` is `E^k`. -/
def ev (k : S) : W ⊕ W → W
  | .inl w => w
  | .inr E => G.exp E k

/-- The value of the fourth position of a symbolic input, which is always known. -/
def val4 : W ⊕ W → W
  | .inl w => w
  | .inr E => E

/-- The value of a symbolic input at the identity secret `ik` (positions `DH1` and `DH2`) and the
signed-prekey secret `spk` (position `DH3`). -/
def interp (ik spk : S) (i : Inp (W ⊕ W)) : Inp W :=
  ⟨i.sid, i.ini, i.res, ev G ik i.dh1, ev G ik i.dh2, ev G spk i.dh3, val4 i.dh4⟩

/-- A symbolic input as a table entry with its value. -/
def interpE (ik spk : S) (p : Inp (W ⊕ W) × K) : Inp W × K := (interp G ik spk p.1, p.2)

variable (O : W → W → W → Bool)

/-- **The equality of two symbolic values** of a position with public key `Z`, decided with the
decision oracle `O`: `w = E^z` is the triple `(Z, E, w)`, and `E^z = E'^z` is the triple
`(Z, E · E'^{-1}, 1)`. -/
def symEq (Z : W) : W ⊕ W → W ⊕ W → Bool
  | .inl w, .inl w' => decide (w = w')
  | .inl w, .inr E => O Z E w
  | .inr E, .inl w => O Z E w
  | .inr E, .inr E' => O Z (G.mul E (G.exp E' (-1))) (G.pub 0)

/-- The equality of two symbolic inputs, with the public identity key `ZA` and the public signed
prekey `ZB` of the positions. -/
def inpEq (ZA ZB : W) (i j : Inp (W ⊕ W)) : Bool :=
  decide (i.sid = j.sid) && decide (i.ini = j.ini) && decide (i.res = j.res) &&
    symEq G O ZA i.dh1 j.dh1 && symEq G O ZA i.dh2 j.dh2 && symEq G O ZB i.dh3 j.dh3 &&
    decide (val4 i.dh4 = val4 j.dh4)

/-- The lookup of a symbolic input in a symbolic table. -/
def slookup (ZA ZB : W) (j : Inp (W ⊕ W)) : List (Inp (W ⊕ W) × K) → Option K
  | [] => none
  | p :: tb => if inpEq G O ZA ZB j p.1 then some p.2 else slookup ZA ZB j tb

/-- The lazily sampled key derivation on a symbolic table, with the fresh value `k`. -/
def sroDet (ZA ZB : W) (tb : List (Inp (W ⊕ W) × K)) (j : Inp (W ⊕ W)) (k : K) :
    K × List (Inp (W ⊕ W) × K) :=
  match slookup G O ZA ZB j tb with
  | some v => (v, tb)
  | none => (k, (j, k) :: tb)

/-- **Correctness of the symbolic equality** with the decision oracle of `gapDHDef G`. -/
theorem symEq_ddh (k : S) (s t : W ⊕ W) :
    symEq G (ddhOracle (gapDHDef G)) (G.pub k) s t = decide (ev G k s = ev G k t) := by
  rcases s with w | E <;> rcases t with w' | E'
  · rfl
  · simp only [symEq, ddhOracle_pub, ev]
    exact decide_eq_decide.mpr Iff.rfl
  · simp only [symEq, ddhOracle_pub, ev]
    exact decide_eq_decide.mpr eq_comm
  · simp only [symEq, ddhOracle_pub, ev]
    refine decide_eq_decide.mpr ?_
    simp only [G.exp_eq, G.mul_eq, DHGroup.dlog_pub, G.pub.injective.eq_iff]
    constructor <;> intro h <;> linear_combination -h

/-- **Correctness of the symbolic equality of inputs.** -/
theorem inpEq_ddh (ik spk : S) (i j : Inp (W ⊕ W)) :
    inpEq G (ddhOracle (gapDHDef G)) (G.pub ik) (G.pub spk) i j =
      decide (interp G ik spk i = interp G ik spk j) := by
  simp only [inpEq, symEq_ddh, interp, Inp.mk.injEq, Bool.decide_and, Bool.and_assoc]

/-- **Correctness of the symbolic lookup.** -/
theorem slookup_ddh (ik spk : S) (j : Inp (W ⊕ W)) (tb : List (Inp (W ⊕ W) × K)) :
    slookup G (ddhOracle (gapDHDef G)) (G.pub ik) (G.pub spk) j tb =
      (tb.map (interpE G ik spk)).lookup (interp G ik spk j) := by
  induction tb with
  | nil => rfl
  | cons p tb ih =>
    rw [slookup, inpEq_ddh, List.map_cons, lookup_cons, ih]
    simp only [interpE, decide_eq_true_eq]
    exact if_congr Iff.rfl rfl rfl

/-- **Correctness of the symbolic key derivation.** -/
theorem sroDet_ddh (ik spk : S) (tb : List (Inp (W ⊕ W) × K)) (j : Inp (W ⊕ W)) (k : K) :
    roDet (tb.map (interpE G ik spk)) (interp G ik spk j) k =
      ((sroDet G (ddhOracle (gapDHDef G)) (G.pub ik) (G.pub spk) tb j k).1,
        (sroDet G (ddhOracle (gapDHDef G)) (G.pub ik) (G.pub spk) tb j k).2.map
          (interpE G ik spk)) := by
  unfold sroDet
  rw [slookup_ddh]
  cases h : (tb.map (interpE G ik spk)).lookup (interp G ik spk j) with
  | some v => simp only [roDet, h]
  | none => simp only [roDet, h, List.map_cons, interpE]

end Sym

/-! ## The world of the reduction -/

/-- The state of the simulator in the world of the reduction: its copy of the real state with a
table of symbolic inputs and the draws of the long-term secrets, its symbolic recorded inputs,
and its phase. -/
abbrev RSim (S W K : Type) := RSt S (W ⊕ W) K × (Inst → Option (Inp (W ⊕ W))) × Phase S W K

section Red

variable {S W K : Type} [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K]
  [Inhabited K] (G : DHGroup S W) (a b : PartyId) (O : W → W → W → Bool) (X Y : W)

/-- The draw of the identity secret of `a`, the offset of `ik_a` from the challenge exponent. -/
def off1 (rs : RSt S (W ⊕ W) K) : S := ((rs.lt a).map Prod.fst).getD 0

/-- The draw of the signed-prekey secret of `b`, the offset of `spk_b` from the challenge
exponent. -/
def off2 (rs : RSt S (W ⊕ W) K) : S := ((rs.lt b).map Prod.snd).getD 0

/-- The public identity key of `a`: `X · g^u` for the draw `u`. -/
def keyA (rs : RSt S (W ⊕ W) K) : W := G.mul X (G.pub (off1 a rs))

/-- The public signed prekey of `b`: `Y · g^v` for the draw `v`. -/
def keyB (rs : RSt S (W ⊕ W) K) : W := G.mul Y (G.pub (off2 b rs))

/-- The public identity key of the party `p` with the drawn pair `l`. -/
def pubIK (p : PartyId) (l : S × S) : W := if p = a then G.mul X (G.pub l.1) else G.pub l.1

/-- The public signed prekey of the party `p` with the drawn pair `l`. -/
def pubSPK (p : PartyId) (l : S × S) : W := if p = b then G.mul Y (G.pub l.2) else G.pub l.2

/-- The symbolic input of the initiator `p` with the drawn pair `la` and ephemeral secret `ek`,
for the responder `q` with the drawn pair `lb` and one-time prekey `opk`: `DH1 = SPK_q^{ik_p}`
is symbolic when `p` is `a`. -/
def aliceS (sid : SessionId) (p q : PartyId) (la lb : S × S) (ek opk : S) : Inp (W ⊕ W) :=
  ⟨sid, p, q,
    if p = a then .inr (pubSPK G b Y q lb) else .inl (G.exp (pubSPK G b Y q lb) la.1),
    .inl (G.exp (pubIK G a X q lb) ek), .inl (G.exp (pubSPK G b Y q lb) ek),
    .inl (G.exp (G.pub opk) ek)⟩

/-- The symbolic input of the responder `q` with the drawn pair `lq` and one-time prekey `opk`,
for the initiator `p` with the drawn pair `lp`, on the ephemeral public key `E`: `DH1` is
symbolic for the pair `(a, b)`, `DH2 = E^{ik_q}` when `q` is `a`, `DH3 = E^{spk_q}` when `q` is
`b`. -/
def bobS (sid : SessionId) (p q : PartyId) (E : W) (lq lp : S × S) (opk : S) : Inp (W ⊕ W) :=
  ⟨sid, p, q,
    if q = b then (if p = a then .inr (pubSPK G b Y q lq) else .inl (G.exp (pubSPK G b Y q lq) lp.1))
      else .inl (G.exp (pubIK G a X p lp) lq.2),
    if q = a then .inr E else .inl (G.exp E lq.1),
    if q = b then .inr E else .inl (G.exp E lq.2),
    .inl (G.exp E opk)⟩

/-- The delivery of `deliverD` on the symbolic copy: the lookup in the table and the comparison
with the partner's input are symbolic. -/
def deliverR (rs : RSt S (W ⊕ W) K) (inp : Inst → Option (Inp (W ⊕ W))) (x : Inst) (r : Rec K)
    (ip : Inp (W ⊕ W)) (k : K) : RSim S W K × Dec S W K :=
  if Exposed rs.st x r then
    ((keyed rs x r (sroDet G O (keyA G a X rs) (keyB G b Y rs) rs.ro ip k).1
        (sroDet G O (keyA G a X rs) (keyB G b Y rs) rs.ro ip k).2,
        Function.update inp x (some ip), .out .ack),
      .inl (.inr (.newKey x.1 x.2 (sroDet G O (keyA G a X rs) (keyB G b Y rs) rs.ro ip k).1)))
  else
    ((keyed rs x r default rs.ro, Function.update inp x (some ip), .out .ack),
      .inl (.inr (if (inp (x.1, r.peer)).all (fun j => inpEq G O (keyA G a X rs) (keyB G b Y rs) j ip)
        then .newKey x.1 x.2 default else .newKeyUnlinked x.1 x.2 default)))

/-- `complete` in the world of the reduction. -/
def completeR (s : RSim S W K) (x : Inst) (r : Draw S K) : RSim S W K × Dec S W K :=
  match s.1.st.recs x, s.1.eph x with
  | some rc, some ek =>
    match opkOf s.1 x.1 rc.peer with
    | some opk =>
      if rc.role = .initiator ∧ rc.key.isNone then
        deliverR G a b O X Y (ltD (ltD s.1 x.2 r.2.1).2 rc.peer r.2.2.1).2 s.2.1 x rc
          (aliceS G a b X Y x.1 x.2 rc.peer (ltD s.1 x.2 r.2.1).1
            (ltD (ltD s.1 x.2 r.2.1).2 rc.peer r.2.2.1).1 ek opk) r.2.2.2
      else ((s.1, s.2.1, .fwd), .inr (.inr .ack))
    | none => ((s.1, s.2.1, .fwd), .inr (.inr .ack))
  | _, _ => ((s.1, s.2.1, .fwd), .inr (.inr .ack))

/-- `send` in the world of the reduction. -/
def sendR (s : RSim S W K) (x : Inst) (e : W) (r : Draw S K) : RSim S W K × Dec S W K :=
  match s.1.st.recs x, s.1.eph x with
  | some rc, some opk =>
    if rc.role = .responder ∧ rc.key.isNone then
      deliverR G a b O X Y (ltD (ltD s.1 x.2 r.2.1).2 rc.peer r.2.2.1).2 s.2.1 x rc
        (bobS G a b X Y x.1 rc.peer x.2 e (ltD s.1 x.2 r.2.1).1
          (ltD (ltD s.1 x.2 r.2.1).2 rc.peer r.2.2.1).1 opk) r.2.2.2
    else ((s.1, s.2.1, .fwd), .inr (.inr .ack))
  | _, _ => ((s.1, s.2.1, .fwd), .inr (.inr .ack))

/-- A symbolic input with known values. -/
def ofInp (x : Inp W) : Inp (W ⊕ W) := ⟨x.sid, x.ini, x.res, .inl x.dh1, .inl x.dh2, .inl x.dh3,
  .inl x.dh4⟩

/-- **The start of the simulator in the world of the reduction**, with the draw `r`: the start
`simStartD` of the simulator, with the identity key of `a` and the signed prekey of `b` read
from the challenge and the draws, and the inputs of the key derivation symbolic. -/
def startR (s : RSim S W K) (e : OEv W) (r : Draw S K) : RSim S W K × Dec S W K :=
  match e with
  | .inl (.newSession sid pid peer role) =>
    if (s.1.st.recs (sid, pid)).isNone then
      (({ s.1 with st := addSession s.1.st (sid, pid) peer role,
                   eph := Function.update s.1.eph (sid, pid) (some r.1) }, s.2.1, .fwd),
        .inl (.inl (.newSession sid pid peer role)))
    else ((s.1, s.2.1, .fwd), .inl (.inl (.newSession sid pid peer role)))
  | .inl (.getKey sid pid) => ((s.1, s.2.1, .fwd), .inl (.inl (.getKey sid pid)))
  | .inr .idle => ((s.1, s.2.1, .fwd), .inr (.inr .ack))
  | .inr .poll => (({ s.1 with st := (pollStep s.1.st).1 }, s.2.1, .fwd),
      .inr (.inr (.notice (pollStep s.1.st).2)))
  | .inr (.pub pid) =>
    (((ltD s.1 pid r.2.1).2, s.2.1, .fwd),
      .inr (.inr (.pub (pubIK G a X pid (ltD s.1 pid r.2.1).1)
        (pubSPK G b Y pid (ltD s.1 pid r.2.1).1))))
  | .inr (.ephPub sid pid) =>
    ((s.1, s.2.1, .fwd), .inr (.inr (.eph ((s.1.eph (sid, pid)).map G.pub))))
  | .inr (.corrupt pid) =>
    if Named s.1.st pid then ((s.1, s.2.1, .fwd), .inr (.inr (.secret none))) else
      (({ (ltD s.1 pid r.2.1).2 with st := corruptStep (ltD s.1 pid r.2.1).2.st pid }, s.2.1,
          .out (.secret (some (ltD s.1 pid r.2.1).1))), .inl (.inr (.corrupt pid)))
  | .inr (.complete sid pid) => completeR G a b O X Y s (sid, pid) r
  | .inr (.send sid pid e) => sendR G a b O X Y s (sid, pid) e r
  | .inr (.kdf x) =>
    (({ s.1 with ro := (sroDet G O (keyA G a X s.1) (keyB G b Y s.1) s.1.ro (ofInp x)
        r.2.2.2).2 }, s.2.1, .fwd),
      .inr (.inr (.hash (sroDet G O (keyA G a X s.1) (keyB G b Y s.1) s.1.ro (ofInp x)
        r.2.2.2).1)))

/-- The finish of the simulator in the world of the reduction. -/
def finR (s : RSim S W K) (o : FOut K) : RSim S W K × OOut S W K :=
  ((s.1, s.2.1, .fwd), simOut s.2.2 o)

/-- **A step of the world of the reduction** with the draw `r = (r₀, kf)`: the start reads
`r₀` and `F_AKE` reads `kf`, as in `simWorldD`. -/
def stepR (t : RSim S W K × St K) (e : OEv W) (r : Draw S K × K) :
    (RSim S W K × St K) × OOut S W K :=
  (((drive0D fStepD finR (startR G a b O X Y t.1 e r.1).1 (startR G a b O X Y t.1 e r.1).2
      t.2 r.2).1,
    (drive0D fStepD finR (startR G a b O X Y t.1 e r.1).1 (startR G a b O X Y t.1 e r.1).2
      t.2 r.2).2.1),
    (drive0D fStepD finR (startR G a b O X Y t.1 e r.1).1 (startR G a b O X Y t.1 e r.1).2
      t.2 r.2).2.2)

/-- The oracle of the world of the reduction. -/
noncomputable def oracleR (t : RSim S W K × St K) (e : OEv W) :
    PMF (OOut S W K × (RSim S W K × St K)) :=
  (PMF.uniformFintype (Draw S K × K)).map fun r => (stepR G a b O X Y t e r).swap

/-- The first `DH1` of an input of the table with initiator `a` and responder `b` that the
decision oracle accepts as the Diffie–Hellman value of the keys of `a` and `b`. -/
def hitR (rs : RSt S (W ⊕ W) K) : Option W :=
  rs.ro.findSome? fun p =>
    if p.1.ini = a ∧ p.1.res = b then
      match p.1.dh1 with
      | .inl w => if O (keyA G a X rs) (keyB G b Y rs) w then some w else none
      | .inr _ => none
    else none

/-- **The output of the reduction** on its final state: an accepted `DH1 = g^{(x+u)(y+v)}`,
divided by `X^v · Y^u · g^{uv}`, or the unit when there is none. -/
def extractR (rs : RSt S (W ⊕ W) K) : W :=
  match hitR G a b O X Y rs with
  | some w => G.mul w (G.exp (G.mul (G.mul (G.exp X (off2 b rs)) (G.exp Y (off1 a rs)))
      (G.pub (off1 a rs * off2 b rs))) (-1))
  | none => G.pub 0

/-- The initial state of the world of the reduction. -/
def rInitR : RSim S W K × St K :=
  ((⟨initSt, fun _ => none, fun _ => none, []⟩, fun _ => none, .fwd), initSt)

/-- The answer of the world of the reduction to the query `e` as a program: one draw. -/
noncomputable def implR (t : RSim S W K × St K) (e : OEv W) :
    OracleAdv Empty Empty (OOut S W K × (RSim S W K × St K)) :=
  .rand (PMF.uniformFintype (Draw S K × K)) fun r =>
    .ret ((stepR G a b O X Y t e r).2, (stepR G a b O X Y t e r).1)

/-- **The reduction as a program**: the oracle adversary `B` run against the world of the
reduction, followed by the extraction from the final state. -/
noncomputable def redTree (B : OracleAdv (OEv W) (OOut S W K) Bool) : OracleAdv Empty Empty W :=
  (OracleAdv.simulate (implR G a b O X Y) B rInitR).bind fun p => .ret (extractR G a b O X Y p.2.1.1)

/-- The output distribution of the reduction. -/
noncomputable def redPMF (B : OracleAdv (OEv W) (OOut S W K) Bool) : PMF W :=
  (OracleAdv.run (fun (_ : Unit) (q : Empty) => q.elim) (redTree G a b O X Y B) ()).map Prod.fst

end Red

/-- **The gap Diffie–Hellman reduction** for the pair `(a, b)`: on the challenge `(X, Y)` with
the decision oracle `O`, it runs the oracle adversary `B` against the world of the reduction and
outputs `extractR`. -/
noncomputable def gdhRed {S W K : Type} [Field S] [Fintype S] [SampleableType W] [Fintype K]
    [Nonempty K] [Inhabited K] (G : DHGroup S W) (a b : PartyId)
    (B : OracleAdv (OEv W) (OOut S W K) Bool) : GapDH_Adversary W :=
  fun O X Y => liftPMF (redPMF G a b O X Y B)

/-! ## The simulated world with shifted draws -/

section Shift

variable {S W K : Type} [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K]
  [Inhabited K] (G : DHGroup S W) (a b : PartyId) (x y : S)

/-- The long-term secrets of the party `p` from the drawn pair `l`: the identity secret of `a` is
shifted by `x` and the signed-prekey secret of `b` by `y`. -/
def sh (p : PartyId) (l : S × S) : S × S :=
  (if p = a then x + l.1 else l.1, if p = b then y + l.2 else l.2)

/-- `sh` as a bijection of the pairs. -/
def shEquiv (p : PartyId) : (S × S) ≃ (S × S) where
  toFun := sh a b x y p
  invFun := sh a b (-x) (-y) p
  left_inv l := by
    simp only [sh]
    ext <;> split_ifs <;> simp
  right_inv l := by
    simp only [sh]
    ext <;> split_ifs <;> simp

/-- The shift of an optional party: the identity without a party. -/
def shO : Option PartyId → (S × S) ≃ (S × S)
  | none => Equiv.refl _
  | some p => shEquiv a b x y p

/-- The party whose long-term secrets an event draws first: the party of `pub`, `corrupt`,
`complete` and `send`. -/
def ev1 : OEv W → Option PartyId
  | .inr (.pub p) | .inr (.corrupt p) | .inr (.complete _ p) | .inr (.send _ p _) => some p
  | _ => none

/-- The party whose long-term secrets an event draws second: the peer of the session of
`complete` and `send`. -/
def ev2 (s : SimSt S W K) : OEv W → Option PartyId
  | .inr (.complete sid p) | .inr (.send sid p _) => (s.1.st.recs (sid, p)).map Rec.peer
  | _ => none

/-- The shifted draw of a step from the state `s` on the event `e`. -/
def transD (s : SimSt S W K) (e : OEv W) : Draw S K ≃ Draw S K :=
  Equiv.prodCongr (Equiv.refl S) (Equiv.prodCongr (shO a b x y (ev1 e))
    (Equiv.prodCongr (shO a b x y (ev2 s e)) (Equiv.refl K)))

/-- The shifted draw of a step of the simulated world. -/
def transW (t : SimSt S W K × St K) (e : OEv W) : (Draw S K × K) ≃ (Draw S K × K) :=
  Equiv.prodCongr (transD a b x y t.1 e) (Equiv.refl K)

/-- **The simulated world with shifted draws is the simulated world**: the oracle of `simGame G`
is the image of a uniform draw under `simWorldD` at the shifted draw. -/
theorem simGame_oracle_eq_trans (t : SimSt S W K × St K) (e : OEv W) :
    (simGame G).oracle () t e = (PMF.uniformFintype (Draw S K × K)).map
      fun r => (simWorldD G t e (transW a b x y t e r)).swap := by
  rw [simGame_oracle_eq]
  conv_lhs => rw [← PMF.uniformFintype_map_equiv (transW a b x y t e), PMF.map_comp]
  rfl

end Shift

/-! ## The coupling of the simulated world and the world of the reduction -/

section Coupling

variable {S W K : Type} [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K]
  [Inhabited K] (G : DHGroup S W) (a b : PartyId) (x y : S)

/-- The symbols of a symbolic input name only drawn secrets: `DH1` and `DH2` are known while `a`
has no long-term secrets, and `DH3` while `b` has none. -/
def SymOk (lt : PartyId → Option (S × S)) (i : Inp (W ⊕ W)) : Prop :=
  (lt a = none → i.dh1.isLeft = true ∧ i.dh2.isLeft = true) ∧ (lt b = none → i.dh3.isLeft = true)

/-- **The coupling relation** between a state `s₁` of the simulator with shifted draws and a
state `s₂` of the simulator in the world of the reduction: equal records, corruptions, notices,
session secrets and phases; the long-term secrets of `s₁` are the shifted draws of `s₂`; the
tables and the recorded inputs of `s₁` are the values of the symbolic ones of `s₂` at
`ik_a = x + u` and `spk_b = y + v`; the symbols name drawn secrets; the inputs of the table with
initiator `a` and responder `b` have a known `DH1`; the records are fresh; `a` and `b` are
uncorrupt. -/
structure RelC (rs₁ : RSt S W K) (inp₁ : Inst → Option (Inp W)) (ph₁ : Phase S W K)
    (rs₂ : RSt S (W ⊕ W) K) (inp₂ : Inst → Option (Inp (W ⊕ W))) (ph₂ : Phase S W K) : Prop where
  st : rs₁.st = rs₂.st
  eph : rs₁.eph = rs₂.eph
  lt : ∀ q, rs₁.lt q = (rs₂.lt q).map (sh a b x y q)
  ro : rs₁.ro = rs₂.ro.map (interpE G (x + off1 a rs₂) (y + off2 b rs₂))
  inp : ∀ z, inp₁ z = (inp₂ z).map (interp G (x + off1 a rs₂) (y + off2 b rs₂))
  ph : ph₁ = ph₂
  symRo : ∀ p ∈ rs₂.ro, SymOk a b rs₂.lt p.1
  symInp : ∀ z i, inp₂ z = some i → SymOk a b rs₂.lt i
  abL : ∀ p ∈ rs₂.ro, p.1.ini = a → p.1.res = b → p.1.dh1.isLeft = true
  fresh : ∀ z r, rs₂.st.recs z = some r → r.status = .fresh
  uncA : rs₂.st.corrupt a = false
  uncB : rs₂.st.corrupt b = false

/-- The coupling relation on the states of the simulators. -/
def Rel (s₁ : SimSt S W K) (s₂ : RSim S W K) : Prop :=
  RelC G a b x y s₁.1 s₁.2.1 s₁.2.2 s₂.1 s₂.2.1 s₂.2.2

/-- The parties `a` and `b`: one of them is corrupt in the simulator's copy. -/
def Stop (s : SimSt S W K) : Prop := s.1.st.corrupt a = true ∨ s.1.st.corrupt b = true

omit [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- The public identity key of the reduction is the public value of the shifted secret. -/
theorem pubIK_pub (p : PartyId) (l : S × S) :
    pubIK G a (G.pub x) p l = G.pub (sh a b x y p l).1 := by
  unfold pubIK sh
  split_ifs <;> simp [G.mul_pub]

omit [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- The public signed prekey of the reduction is the public value of the shifted secret. -/
theorem pubSPK_pub (p : PartyId) (l : S × S) :
    pubSPK G b (G.pub y) p l = G.pub (sh a b x y p l).2 := by
  unfold pubSPK sh
  split_ifs <;> simp [G.mul_pub]

omit [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
theorem keyA_pub (rs : RSt S (W ⊕ W) K) : keyA G a (G.pub x) rs = G.pub (x + off1 a rs) := by
  simp only [keyA, G.mul_pub]

omit [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
theorem keyB_pub (rs : RSt S (W ⊕ W) K) : keyB G b (G.pub y) rs = G.pub (y + off2 b rs) := by
  simp only [keyB, G.mul_pub]

omit [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- A known value does not depend on the exponent. -/
theorem ev_of_isLeft {s : W ⊕ W} (h : s.isLeft = true) (k k' : S) : ev G k s = ev G k' s := by
  rcases s with w | E
  · rfl
  · cases h

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- `SymOk` holds for larger sets of drawn secrets. -/
theorem SymOk.mono {lt lt' : PartyId → Option (S × S)} {i : Inp (W ⊕ W)}
    (h : ∀ q v, lt q = some v → lt' q = some v) (hs : SymOk a b lt i) : SymOk a b lt' i := by
  refine ⟨fun ha => hs.1 ?_, fun hb => hs.2 ?_⟩
  · cases hq : lt a with
    | none => rfl
    | some v => rw [h a v hq] at ha; cases ha
  · cases hq : lt b with
    | none => rfl
    | some v => rw [h b v hq] at hb; cases hb

omit [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- The value of a symbolic input whose symbols name drawn secrets does not change when more
secrets are drawn. -/
theorem interp_stable {rs rs' : RSt S (W ⊕ W) K} (h : ∀ q v, rs.lt q = some v → rs'.lt q = some v)
    {i : Inp (W ⊕ W)} (hs : SymOk a b rs.lt i) :
    interp G (x + off1 a rs') (y + off2 b rs') i = interp G (x + off1 a rs) (y + off2 b rs) i := by
  have h1 : ev G (x + off1 a rs') i.dh1 = ev G (x + off1 a rs) i.dh1 ∧
      ev G (x + off1 a rs') i.dh2 = ev G (x + off1 a rs) i.dh2 := by
    cases hq : rs.lt a with
    | none => exact ⟨ev_of_isLeft G (hs.1 hq).1 _ _, ev_of_isLeft G (hs.1 hq).2 _ _⟩
    | some v => simp only [off1, hq, h a v hq, and_self]
  have h2 : ev G (y + off2 b rs') i.dh3 = ev G (y + off2 b rs) i.dh3 := by
    cases hq : rs.lt b with
    | none => exact ev_of_isLeft G (hs.2 hq) _ _
    | some v => simp only [off2, hq, h b v hq]
  simp only [interp, h1, h2]

omit [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- The table of values of a symbolic table whose symbols name drawn secrets does not change when
more secrets are drawn. -/
theorem map_interpE_stable {rs rs' : RSt S (W ⊕ W) K}
    (h : ∀ q v, rs.lt q = some v → rs'.lt q = some v) {tb : List (Inp (W ⊕ W) × K)}
    (hs : ∀ p ∈ tb, SymOk a b rs.lt p.1) :
    tb.map (interpE G (x + off1 a rs') (y + off2 b rs')) =
      tb.map (interpE G (x + off1 a rs) (y + off2 b rs)) :=
  List.map_congr_left fun p hp => by
    simp only [interpE, interp_stable G a b x y h (hs p hp)]

omit [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- **Drawing long-term secrets** on both sides: the simulator with the shifted draw obtains the
shifted secrets, and the relation is kept. -/
theorem rel_ltD {rs₁ : RSt S W K} {inp₁ : Inst → Option (Inp W)} {ph₁ : Phase S W K}
    {rs₂ : RSt S (W ⊕ W) K} {inp₂ : Inst → Option (Inp (W ⊕ W))} {ph₂ : Phase S W K}
    (h : RelC G a b x y rs₁ inp₁ ph₁ rs₂ inp₂ ph₂) (p : PartyId) (l : S × S) :
    (ltD rs₁ p (sh a b x y p l)).1 = sh a b x y p (ltD rs₂ p l).1 ∧
      RelC G a b x y (ltD rs₁ p (sh a b x y p l)).2 inp₁ ph₁ (ltD rs₂ p l).2 inp₂ ph₂ := by
  have hl : rs₁.lt p = (rs₂.lt p).map (sh a b x y p) := h.lt p
  cases hq : rs₂.lt p with
  | some l' =>
    rw [hq] at hl
    simp only [ltD, hq, hl, Option.map_some, true_and]
    exact h
  | none =>
    rw [hq] at hl
    have hext : ∀ q v, rs₂.lt q = some v → (Function.update rs₂.lt p (some l)) q = some v := by
      intro q v hv
      have hne : q ≠ p := fun hc => by subst hc; rw [hq] at hv; cases hv
      rw [Function.update_of_ne hne, hv]
    have hext' : ∀ q v, rs₂.lt q = some v →
        ({ rs₂ with lt := Function.update rs₂.lt p (some l) } : RSt S (W ⊕ W) K).lt q = some v :=
      hext
    simp only [ltD, hq, hl, Option.map_none, true_and]
    refine ⟨h.st, h.eph, fun q => ?_, ?_, fun z => ?_, h.ph, fun e he =>
      (h.symRo e he).mono a b hext, fun z i hi => (h.symInp z i hi).mono a b hext, h.abL, h.fresh,
      h.uncA, h.uncB⟩
    · by_cases hqp : q = p
      · subst hqp; simp only [Function.update_self, Option.map_some]
      · simp only [Function.update_of_ne hqp]; exact h.lt q
    · exact h.ro.trans (map_interpE_stable G a b x y hext' h.symRo).symm
    · rw [h.inp z]
      cases hz : inp₂ z with
      | none => rfl
      | some i =>
        simp only [Option.map_some]
        exact congrArg some (interp_stable G a b x y hext' (h.symInp z i hz)).symm

omit [Fintype S] [Fintype K] [Nonempty K] [Inhabited K] in
/-- The symbolic key derivation keeps its table or adds the new input. -/
theorem sroDet_snd (O : W → W → W → Bool) (ZA ZB : W) (tb : List (Inp (W ⊕ W) × K))
    (j : Inp (W ⊕ W)) (k : K) :
    (sroDet G O ZA ZB tb j k).2 = tb ∨ (sroDet G O ZA ZB tb j k).2 = (j, k) :: tb := by
  unfold sroDet
  split
  · exact Or.inl rfl
  · exact Or.inr rfl

omit [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- **A key on both sides**: the relation holds after the same record update, related tables and
the same recorded input. -/
theorem RelC.keyedR {rs₁ : RSt S W K} {inp₁ : Inst → Option (Inp W)} {ph₁ : Phase S W K}
    {rs₂ : RSt S (W ⊕ W) K} {inp₂ : Inst → Option (Inp (W ⊕ W))} {ph₂ : Phase S W K}
    (h : RelC G a b x y rs₁ inp₁ ph₁ rs₂ inp₂ ph₂) {z : Inst} {rc : Rec K}
    (hrc : rs₂.st.recs z = some rc) (v : K) {ro₁ : List (Inp W × K)}
    {ro₂ : List (Inp (W ⊕ W) × K)}
    (hro : ro₁ = ro₂.map (interpE G (x + off1 a rs₂) (y + off2 b rs₂)))
    (hsym : ∀ p ∈ ro₂, SymOk a b rs₂.lt p.1)
    (hab : ∀ p ∈ ro₂, p.1.ini = a → p.1.res = b → p.1.dh1.isLeft = true)
    {ip : Inp (W ⊕ W)} (hs : SymOk a b rs₂.lt ip) (ph : Phase S W K) :
    RelC G a b x y (keyed rs₁ z rc v ro₁)
      (Function.update inp₁ z (some (interp G (x + off1 a rs₂) (y + off2 b rs₂) ip))) ph
      (keyed rs₂ z rc v ro₂) (Function.update inp₂ z (some ip)) ph := by
  refine ⟨by simp only [X3DHSquare.keyed]; rw [h.st], h.eph, h.lt, hro, fun z' => ?_, rfl, hsym, fun z' i hi => ?_,
    hab, fun z' r hr => ?_, h.uncA, h.uncB⟩
  · by_cases hz : z' = z
    · subst hz; simp only [Function.update_self, Option.map_some]; rfl
    · simp only [Function.update_of_ne hz]; exact h.inp z'
  · by_cases hz : z' = z
    · subst hz; simp only [Function.update_self, Option.some.injEq] at hi; subst hi; exact hs
    · simp only [Function.update_of_ne hz] at hi; exact h.symInp z' i hi
  · simp only [X3DHSquare.keyed, setRec] at hr
    by_cases hz : z' = z
    · subst hz
      simp only [Function.update_self, Option.some.injEq] at hr
      subst hr
      exact h.fresh _ rc hrc
    · simp only [Function.update_of_ne hz] at hr; exact h.fresh z' r hr

omit [Fintype K] [Nonempty K] in
/-- **The delivery of a key** on both sides gives the same decision and keeps the relation. -/
theorem rel_deliver {rs₁ : RSt S W K} {inp₁ : Inst → Option (Inp W)} {ph₁ : Phase S W K}
    {rs₂ : RSt S (W ⊕ W) K} {inp₂ : Inst → Option (Inp (W ⊕ W))} {ph₂ : Phase S W K}
    (h : RelC G a b x y rs₁ inp₁ ph₁ rs₂ inp₂ ph₂) {z : Inst} {rc : Rec K}
    (hrc : rs₂.st.recs z = some rc) {ip : Inp (W ⊕ W)} (hs : SymOk a b rs₂.lt ip)
    (hsh : (ip.ini = z.2 ∧ ip.res = rc.peer) ∨ (ip.ini = rc.peer ∧ ip.res = z.2)) (k : K) :
    (deliverD rs₁ inp₁ z rc (interp G (x + off1 a rs₂) (y + off2 b rs₂) ip) k).2 =
        (deliverR G a b (ddhOracle (gapDHDef G)) (G.pub x) (G.pub y) rs₂ inp₂ z rc ip k).2 ∧
      Rel G a b x y (deliverD rs₁ inp₁ z rc (interp G (x + off1 a rs₂) (y + off2 b rs₂) ip) k).1
        (deliverR G a b (ddhOracle (gapDHDef G)) (G.pub x) (G.pub y) rs₂ inp₂ z rc ip k).1 := by
  have hE1 : Exposed rs₁.st z rc ↔ Exposed rs₂.st z rc := by rw [h.st]
  unfold deliverD deliverR
  rw [keyA_pub, keyB_pub]
  by_cases hE : Exposed rs₂.st z rc
  · simp only [hE, hE1, ↓reduceIte]
    rw [h.ro, sroDet_ddh]
    refine ⟨rfl, h.keyedR G a b x y hrc _ rfl ?_ ?_ hs _⟩
    · rcases sroDet_snd G (ddhOracle (gapDHDef G)) (G.pub (x + off1 a rs₂)) (G.pub (y + off2 b rs₂))
        rs₂.ro ip k with he | he <;> rw [he]
      · exact h.symRo
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact hs
        · exact h.symRo p hp
    · rcases sroDet_snd G (ddhOracle (gapDHDef G)) (G.pub (x + off1 a rs₂)) (G.pub (y + off2 b rs₂))
        rs₂.ro ip k with he | he <;> rw [he]
      · exact h.abL
      · intro p hp hpa hpb
        rcases List.mem_cons.mp hp with rfl | hp
        · exfalso
          have hf := h.fresh z rc hrc
          have ha := h.uncA
          have hb := h.uncB
          simp only [Exposed] at hE
          rcases hsh with ⟨h1, h2⟩ | ⟨h1, h2⟩ <;> grind
        · exact h.abL p hp hpa hpb
  · simp only [hE, hE1, ↓reduceIte]
    refine ⟨?_, h.keyedR G a b x y hrc _ h.ro h.symRo h.abL hs _⟩
    rw [h.inp]
    cases inp₂ (z.1, rc.peer) with
    | none => rfl
    | some j => simp only [Option.map_some, Option.all_some, inpEq_ddh]

omit [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- The relation does not depend on the phases beyond their equality. -/
theorem RelC.setPh {rs₁ : RSt S W K} {inp₁ : Inst → Option (Inp W)} {ph₁ : Phase S W K}
    {rs₂ : RSt S (W ⊕ W) K} {inp₂ : Inst → Option (Inp (W ⊕ W))} {ph₂ : Phase S W K}
    (h : RelC G a b x y rs₁ inp₁ ph₁ rs₂ inp₂ ph₂) (ph : Phase S W K) :
    RelC G a b x y rs₁ inp₁ ph rs₂ inp₂ ph :=
  ⟨h.st, h.eph, h.lt, h.ro, h.inp, rfl, h.symRo, h.symInp, h.abL, h.fresh, h.uncA, h.uncB⟩

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- `opkOf` reads the records and the session secrets. -/
theorem opkOf_congr {W' : Type} {rs₁ : RSt S W K} {rs₂ : RSt S W' K} (hst : rs₁.st = rs₂.st)
    (heph : rs₁.eph = rs₂.eph) (sid : SessionId) (q : PartyId) :
    opkOf rs₁ sid q = opkOf rs₂ sid q := by
  simp only [opkOf, hst, heph]

omit [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
@[simp] theorem transD_apply (s : SimSt S W K) (e : OEv W) (r : Draw S K) :
    transD a b x y s e r = (r.1, shO a b x y (ev1 e) r.2.1, shO a b x y (ev2 s e) r.2.2.1,
      r.2.2.2) := rfl

omit [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- The value of the symbolic input of an initiator is its input in the simulator. -/
theorem aliceS_interp {rs : RSt S (W ⊕ W) K} {sid : SessionId} {p q : PartyId} {la lb : S × S}
    (hp : rs.lt p = some la) (ek opk : S) :
    interp G (x + off1 a rs) (y + off2 b rs) (aliceS G a b (G.pub x) (G.pub y) sid p q la lb ek opk) =
      aliceInp G sid p q (sh a b x y p la).1 ek (G.pub (sh a b x y q lb).1)
        (G.pub (sh a b x y q lb).2) (G.pub opk) := by
  unfold aliceS
  by_cases hpa : p = a
  · subst hpa
    simp only [interp, aliceInp, ev, pubIK_pub G p b x y, pubSPK_pub G p b x y, off1, hp, sh,
      ↓reduceIte, Option.map_some, Option.getD_some, val4]
  · simp only [interp, aliceInp, ev, pubIK_pub G a b x y, pubSPK_pub G a b x y, sh, hpa,
      ↓reduceIte, val4]

omit [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- The value of the symbolic input of a responder is its input in the simulator. -/
theorem bobS_interp {rs : RSt S (W ⊕ W) K} {sid : SessionId} {p q : PartyId} {lq lp : S × S}
    (hq : rs.lt q = some lq) (hp : rs.lt p = some lp) (E : W) (opk : S) :
    interp G (x + off1 a rs) (y + off2 b rs) (bobS G a b (G.pub x) (G.pub y) sid p q E lq lp opk) =
      bobInp G sid p q (G.pub (sh a b x y p lp).1) E (sh a b x y q lq).1 (sh a b x y q lq).2 opk := by
  unfold bobS
  simp only [interp, bobInp, Inp.mk.injEq, true_and]
  refine ⟨?_, ?_, ?_, rfl⟩
  · by_cases hqb : q = b
    · subst hqb
      by_cases hpa : p = a
      · subst hpa
        simp only [ev, pubSPK_pub G p q x y, off1, hp, sh, ↓reduceIte, Option.map_some,
          Option.getD_some, G.exp_pub, mul_comm]
      · simp only [ev, pubSPK_pub G a q x y, sh, hpa, ↓reduceIte, G.exp_pub, mul_comm]
    · simp only [ev, pubIK_pub G a b x y, sh, hqb, ↓reduceIte, G.exp_pub]
  · by_cases hqa : q = a
    · subst hqa; simp only [ev, off1, hq, sh, ↓reduceIte, Option.map_some, Option.getD_some]
    · simp only [ev, sh, hqa, ↓reduceIte]
  · by_cases hqb : q = b
    · subst hqb; simp only [ev, off2, hq, sh, ↓reduceIte, Option.map_some, Option.getD_some]
    · simp only [ev, sh, hqb, ↓reduceIte]

omit [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
theorem aliceS_symOk {lt : PartyId → Option (S × S)} {sid : SessionId} {p q : PartyId}
    {la lb : S × S} (hp : lt p = some la) (ek opk : S) :
    SymOk a b lt (aliceS G a b (G.pub x) (G.pub y) sid p q la lb ek opk) := by
  refine ⟨fun ha => ⟨?_, rfl⟩, fun _ => rfl⟩
  have hpa : p ≠ a := fun hc => by subst hc; rw [hp] at ha; cases ha
  simp only [aliceS, hpa, ↓reduceIte, Sum.isLeft_inl]

omit [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
theorem bobS_symOk {lt : PartyId → Option (S × S)} {sid : SessionId} {p q : PartyId}
    {lq lp : S × S} (hq : lt q = some lq) (hp : lt p = some lp) (E : W) (opk : S) :
    SymOk a b lt (bobS G a b (G.pub x) (G.pub y) sid p q E lq lp opk) := by
  refine ⟨fun ha => ⟨?_, ?_⟩, fun hb => ?_⟩
  · have hpa : p ≠ a := fun hc => by subst hc; rw [hp] at ha; cases ha
    simp only [bobS, hpa, ↓reduceIte]
    split_ifs <;> rfl
  · have hqa : q ≠ a := fun hc => by subst hc; rw [hq] at ha; cases ha
    simp only [bobS, hqa, ↓reduceIte, Sum.isLeft_inl]
  · have hqb : q ≠ b := fun hc => by subst hc; rw [hq] at hb; cases hb
    simp only [bobS, hqb, ↓reduceIte, Sum.isLeft_inl]

omit [Fintype K] [Nonempty K] in
/-- **`complete` on both sides** gives the same decision and keeps the relation. -/
theorem rel_complete {s₁ : SimSt S W K} {s₂ : RSim S W K} (h : Rel G a b x y s₁ s₂)
    (sid : SessionId) (pid : PartyId) (r : Draw S K) :
    (simCompleteD G s₁ (sid, pid) (transD a b x y s₁ (.inr (.complete sid pid)) r)).2 =
        (completeR G a b (ddhOracle (gapDHDef G)) (G.pub x) (G.pub y) s₂ (sid, pid) r).2 ∧
      Rel G a b x y (simCompleteD G s₁ (sid, pid) (transD a b x y s₁ (.inr (.complete sid pid)) r)).1
        (completeR G a b (ddhOracle (gapDHDef G)) (G.pub x) (G.pub y) s₂ (sid, pid) r).1 := by
  obtain ⟨rs₁, inp₁, ph₁⟩ := s₁
  obtain ⟨rs₂, inp₂, ph₂⟩ := s₂
  have h' : RelC G a b x y rs₁ inp₁ ph₁ rs₂ inp₂ ph₂ := h
  simp only [simCompleteD, completeR, transD_apply, ev1, ev2]
  rw [h'.st, h'.eph]
  simp only [opkOf_congr h'.st h'.eph]
  cases hr : rs₂.st.recs (sid, pid) with
  | none => dsimp only; exact ⟨rfl, h'.setPh G a b x y _⟩
  | some rc =>
    cases he : rs₂.eph (sid, pid) with
    | none => dsimp only; exact ⟨rfl, h'.setPh G a b x y _⟩
    | some ek =>
      cases ho : opkOf rs₂ sid rc.peer with
      | none => dsimp only; rw [ho]; exact ⟨rfl, h'.setPh G a b x y _⟩
      | some opk =>
        dsimp only
        rw [ho]
        by_cases hc : rc.role = .initiator ∧ rc.key.isNone
        · simp only [hc, and_self, ↓reduceIte, Option.map_some, shO, shEquiv, Equiv.coe_fn_mk]
          obtain ⟨e₁, h₁⟩ := rel_ltD G a b x y h' pid r.2.1
          obtain ⟨e₂, h₂⟩ := rel_ltD G a b x y h₁ rc.peer r.2.2.1
          rw [e₁, e₂]
          have hp : (ltD (ltD rs₂ pid r.2.1).2 rc.peer r.2.2.1).2.lt pid =
              some (ltD rs₂ pid r.2.1).1 :=
            ltD_lt_mono _ _ _ _ _ (ltD_lt_self rs₂ pid r.2.1)
          rw [← aliceS_interp G a b x y hp]
          refine rel_deliver G a b x y h₂ ?_ (aliceS_symOk G a b x y hp ek opk) (Or.inl ⟨rfl, rfl⟩) _
          simp only [ltD_st, hr]
        · simp only [hc, ↓reduceIte, true_and]
          exact h'.setPh G a b x y _

omit [Fintype K] [Nonempty K] in
/-- **`send` on both sides** gives the same decision and keeps the relation. -/
theorem rel_send {s₁ : SimSt S W K} {s₂ : RSim S W K} (h : Rel G a b x y s₁ s₂)
    (sid : SessionId) (pid : PartyId) (e : W) (r : Draw S K) :
    (simSendD G s₁ (sid, pid) e (transD a b x y s₁ (.inr (.send sid pid e)) r)).2 =
        (sendR G a b (ddhOracle (gapDHDef G)) (G.pub x) (G.pub y) s₂ (sid, pid) e r).2 ∧
      Rel G a b x y (simSendD G s₁ (sid, pid) e (transD a b x y s₁ (.inr (.send sid pid e)) r)).1
        (sendR G a b (ddhOracle (gapDHDef G)) (G.pub x) (G.pub y) s₂ (sid, pid) e r).1 := by
  obtain ⟨rs₁, inp₁, ph₁⟩ := s₁
  obtain ⟨rs₂, inp₂, ph₂⟩ := s₂
  have h' : RelC G a b x y rs₁ inp₁ ph₁ rs₂ inp₂ ph₂ := h
  simp only [simSendD, sendR, transD_apply, ev1, ev2]
  rw [h'.st, h'.eph]
  cases hr : rs₂.st.recs (sid, pid) with
  | none => dsimp only; exact ⟨rfl, h'.setPh G a b x y _⟩
  | some rc =>
    cases he : rs₂.eph (sid, pid) with
    | none => dsimp only; exact ⟨rfl, h'.setPh G a b x y _⟩
    | some opk =>
      dsimp only
      by_cases hc : rc.role = .responder ∧ rc.key.isNone
      · simp only [hc, and_self, ↓reduceIte, Option.map_some, shO, shEquiv, Equiv.coe_fn_mk]
        obtain ⟨e₁, h₁⟩ := rel_ltD G a b x y h' pid r.2.1
        obtain ⟨e₂, h₂⟩ := rel_ltD G a b x y h₁ rc.peer r.2.2.1
        rw [e₁, e₂]
        have hq : (ltD (ltD rs₂ pid r.2.1).2 rc.peer r.2.2.1).2.lt pid =
            some (ltD rs₂ pid r.2.1).1 :=
          ltD_lt_mono _ _ _ _ _ (ltD_lt_self rs₂ pid r.2.1)
        have hp : (ltD (ltD rs₂ pid r.2.1).2 rc.peer r.2.2.1).2.lt rc.peer =
            some (ltD (ltD rs₂ pid r.2.1).2 rc.peer r.2.2.1).1 := ltD_lt_self _ _ _
        rw [← bobS_interp G a b x y hq hp]
        refine rel_deliver G a b x y h₂ ?_ (bobS_symOk G a b x y hq hp e opk)
          (Or.inr ⟨rfl, rfl⟩) _
        simp only [ltD_st, hr]
      · simp only [hc, ↓reduceIte, true_and]
        exact h'.setPh G a b x y _

omit [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- The relation after the same update of the records, corruptions, notices and session secrets
on both sides, with fresh records and `a`, `b` uncorrupt. -/
theorem RelC.upd {rs₁ : RSt S W K} {inp₁ : Inst → Option (Inp W)} {ph₁ : Phase S W K}
    {rs₂ : RSt S (W ⊕ W) K} {inp₂ : Inst → Option (Inp (W ⊕ W))} {ph₂ : Phase S W K}
    (h : RelC G a b x y rs₁ inp₁ ph₁ rs₂ inp₂ ph₂) {t₁ t₂ : St K} (ht : t₁ = t₂)
    {eph₁ eph₂ : Inst → Option S} (he : eph₁ = eph₂)
    (hf : ∀ z r, t₂.recs z = some r → r.status = .fresh) (ha : t₂.corrupt a = false)
    (hb : t₂.corrupt b = false) (ph : Phase S W K) :
    RelC G a b x y { rs₁ with st := t₁, eph := eph₁ } inp₁ ph { rs₂ with st := t₂, eph := eph₂ }
      inp₂ ph :=
  ⟨ht, he, h.lt, h.ro, h.inp, rfl, h.symRo, h.symInp, h.abL, hf, ha, hb⟩

omit [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- The relation after a new entry of the tables. -/
theorem RelC.roUpd {rs₁ : RSt S W K} {inp₁ : Inst → Option (Inp W)} {ph₁ : Phase S W K}
    {rs₂ : RSt S (W ⊕ W) K} {inp₂ : Inst → Option (Inp (W ⊕ W))} {ph₂ : Phase S W K}
    (h : RelC G a b x y rs₁ inp₁ ph₁ rs₂ inp₂ ph₂) {ro₁ : List (Inp W × K)}
    {ro₂ : List (Inp (W ⊕ W) × K)}
    (hro : ro₁ = ro₂.map (interpE G (x + off1 a rs₂) (y + off2 b rs₂)))
    (hsym : ∀ p ∈ ro₂, SymOk a b rs₂.lt p.1)
    (hab : ∀ p ∈ ro₂, p.1.ini = a → p.1.res = b → p.1.dh1.isLeft = true) (ph : Phase S W K) :
    RelC G a b x y { rs₁ with ro := ro₁ } inp₁ ph { rs₂ with ro := ro₂ } inp₂ ph :=
  ⟨h.st, h.eph, h.lt, hro, h.inp, rfl, hsym, h.symInp, hab, h.fresh, h.uncA, h.uncB⟩

omit [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
theorem interp_ofInp (ik spk : S) (q : Inp W) : interp G ik spk (ofInp q) = q := by
  cases q; rfl

omit [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
theorem sh_of_ne {p : PartyId} (ha : p ≠ a) (hb : p ≠ b) (l : S × S) : sh a b x y p l = l := by
  simp only [sh, ha, hb, ↓reduceIte]

omit [Fintype K] [Nonempty K] in
/-- **The coupling of a start of the simulator**: from related states, the simulator with the
shifted draw and the simulator of the reduction make the same decision and reach related
states, unless the step corrupts `a` or `b`. -/
theorem rel_start {s₁ : SimSt S W K} {s₂ : RSim S W K} (h : Rel G a b x y s₁ s₂) (e : OEv W)
    (r : Draw S K) :
    Stop a b (simStartD G s₁ e (transD a b x y s₁ e r)).1 ∨
      ((simStartD G s₁ e (transD a b x y s₁ e r)).2 =
          (startR G a b (ddhOracle (gapDHDef G)) (G.pub x) (G.pub y) s₂ e r).2 ∧
        Rel G a b x y (simStartD G s₁ e (transD a b x y s₁ e r)).1
          (startR G a b (ddhOracle (gapDHDef G)) (G.pub x) (G.pub y) s₂ e r).1) := by
  obtain ⟨rs₁, inp₁, ph₁⟩ := s₁
  obtain ⟨rs₂, inp₂, ph₂⟩ := s₂
  have h' : RelC G a b x y rs₁ inp₁ ph₁ rs₂ inp₂ ph₂ := h
  rcases e with (⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) | (_ | _ | pid | ⟨sid, pid⟩ | pid |
    ⟨sid, pid⟩ | ⟨sid, pid, e⟩ | q)
  · right
    have hn : (rs₁.st.recs (sid, pid)).isNone = (rs₂.st.recs (sid, pid)).isNone := by rw [h'.st]
    dsimp only [simStartD, startR, transD_apply]
    by_cases hc : (rs₂.st.recs (sid, pid)).isNone = true
    · rw [ite_eq_left (hn.trans hc), ite_eq_left hc]
      refine ⟨rfl, h'.upd G a b x y (by rw [h'.st]) (by rw [h'.eph]) ?_ ?_ ?_ _⟩
      · intro z rz hz
        unfold addSession at hz
        split at hz
        · exact h'.fresh z rz hz
        · by_cases hzx : z = (sid, pid)
          · subst hzx; simp only [Function.update_self, Option.some.injEq] at hz; rw [← hz]
          · simp only [Function.update_of_ne hzx] at hz; exact h'.fresh z rz hz
      · unfold addSession; split <;> exact h'.uncA
      · unfold addSession; split <;> exact h'.uncB
    · rw [ite_eq_right (hn ▸ hc), ite_eq_right hc]
      exact ⟨rfl, h'.setPh G a b x y _⟩
  · exact Or.inr ⟨rfl, h'.setPh G a b x y _⟩
  · exact Or.inr ⟨rfl, h'.setPh G a b x y _⟩
  · right
    dsimp only [simStartD, startR]
    rw [h'.st]
    refine ⟨rfl, h'.upd G a b x y rfl h'.eph ?_ ?_ ?_ _⟩
    · rw [(pollStep_fst _).1]; exact h'.fresh
    · rw [(pollStep_fst _).2.1]; exact h'.uncA
    · rw [(pollStep_fst _).2.1]; exact h'.uncB
  · right
    obtain ⟨e₁, h₁⟩ := rel_ltD G a b x y h' pid r.2.1
    dsimp only [simStartD, startR, transD_apply, ev1, shO, shEquiv, Equiv.coe_fn_mk]
    rw [e₁, pubIK_pub G a b x y, pubSPK_pub G a b x y]
    exact ⟨rfl, h₁.setPh G a b x y _⟩
  · right
    dsimp only [simStartD, startR, ephPubOf]
    rw [h'.eph]
    exact ⟨rfl, h'.setPh G a b x y _⟩
  · have hn : Named rs₁.st pid = Named rs₂.st pid := by rw [h'.st]
    dsimp only [simStartD, startR, transD_apply, ev1, shO, shEquiv, Equiv.coe_fn_mk]
    by_cases hc : Named rs₂.st pid = true
    · rw [ite_eq_left (hn.trans hc), ite_eq_left hc]
      exact Or.inr ⟨rfl, h'.setPh G a b x y _⟩
    · rw [ite_eq_right (hn ▸ hc), ite_eq_right hc]
      obtain ⟨e₁, h₁⟩ := rel_ltD G a b x y h' pid r.2.1
      by_cases hab : pid = a ∨ pid = b
      · left
        simp only [Stop, corruptStep, ltD_st]
        rcases hab with rfl | rfl <;> simp
      · right
        have hpa : pid ≠ a := fun hc => hab (Or.inl hc)
        have hpb : pid ≠ b := fun hc => hab (Or.inr hc)
        simp only [sh_of_ne a b x y hpa hpb] at e₁ h₁
        rw [sh_of_ne a b x y hpa hpb, e₁]
        refine ⟨rfl, h₁.upd G a b x y (t₁ := corruptStep (ltD rs₁ pid r.2.1).2.st pid)
          (t₂ := corruptStep (ltD rs₂ pid r.2.1).2.st pid) (by rw [h₁.st]) h₁.eph h₁.fresh ?_ ?_ _⟩
        · simp only [corruptStep, Function.update_of_ne hpa.symm]; exact h₁.uncA
        · simp only [corruptStep, Function.update_of_ne hpb.symm]; exact h₁.uncB
  · exact Or.inr (rel_complete G a b x y h sid pid r)
  · exact Or.inr (rel_send G a b x y h sid pid e r)
  · right
    dsimp only [simStartD, startR, transD_apply]
    rw [h'.ro, keyA_pub, keyB_pub, ← interp_ofInp G (x + off1 a rs₂) (y + off2 b rs₂) q,
      sroDet_ddh]
    refine ⟨rfl, h'.roUpd G a b x y rfl ?_ ?_ _⟩
    · rcases sroDet_snd G (ddhOracle (gapDHDef G)) (G.pub (x + off1 a rs₂))
        (G.pub (y + off2 b rs₂)) rs₂.ro (ofInp q) r.2.2.2 with he | he <;> rw [he]
      · exact h'.symRo
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact ⟨fun _ => ⟨rfl, rfl⟩, fun _ => rfl⟩
        · exact h'.symRo p hp
    · rcases sroDet_snd G (ddhOracle (gapDHDef G)) (G.pub (x + off1 a rs₂))
        (G.pub (y + off2 b rs₂)) rs₂.ro (ofInp q) r.2.2.2 with he | he <;> rw [he]
      · exact h'.abL
      · intro p hp
        rcases List.mem_cons.mp hp with rfl | hp
        · exact fun _ _ => rfl
        · exact h'.abL p hp

end Coupling

/-! ## The coupling of the worlds -/

section World

variable {S W K : Type} [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K]
  [Inhabited K] (G : DHGroup S W) (a b : PartyId) (x y : S)

/-- The coupling relation on the states of the worlds: related simulators and the same state of
`F_AKE`. -/
def RelW (t₁ : SimSt S W K × St K) (t₂ : RSim S W K × St K) : Prop :=
  Rel G a b x y t₁.1 t₂.1 ∧ t₁.2 = t₂.2

/-- The bad event for the pair `(a, b)`: the table of the simulated world holds an input with
initiator `a` and responder `b`, both uncorrupt, whose `DH1` is `g^{ik_a · spk_b}`. -/
def DH1HitAB (s : SimSt S W K) : Prop :=
  ∃ ip v ikA spkA ikB spkB, s.1.ro.lookup ip = some v ∧ ip.ini = a ∧ ip.res = b ∧
    s.1.st.corrupt a = false ∧ s.1.st.corrupt b = false ∧ s.1.lt a = some (ikA, spkA) ∧
    s.1.lt b = some (ikB, spkB) ∧ ip.dh1 = G.pub (ikA * spkB)

/-- The event of the world of the reduction that answers `DH1HitAB`: the symbolic table holds an
input with initiator `a` and responder `b` whose `DH1` is the known value
`g^{(x + u)(y + v)}`, with the long-term secrets of `a` and `b` drawn. -/
def Bad2 (t : RSim S W K × St K) : Prop :=
  ∃ p ∈ t.1.1.ro, p.1.ini = a ∧ p.1.res = b ∧ (t.1.1.lt a).isSome = true ∧
    (t.1.1.lt b).isSome = true ∧
    p.1.dh1 = .inl (G.pub ((x + off1 a t.1.1) * (y + off2 b t.1.1)))

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
theorem stop_drive0D {α β τ EG OG Rf O' : Type} (stepD : τ → EG → Rf → τ × OG)
    (fin : α × β → OG → (α × β) × O') (hfin : ∀ s o, (fin s o).1.1 = s.1)
    (s : α × β) (d : EG ⊕ O') (t : τ) (k : Rf) :
    (drive0D stepD fin s d t k).1.1 = s.1 := by
  unfold drive0D
  split
  · rfl
  · exact hfin _ _

omit [Fintype K] [Nonempty K] in
/-- **The coupling of a step of the worlds**: from related states, the simulated world with the
shifted draw and the world of the reduction give the same answer and reach related states,
unless the step corrupts `a` or `b`. -/
theorem step_rel {t₁ : SimSt S W K × St K} {t₂ : RSim S W K × St K} (h : RelW G a b x y t₁ t₂)
    (e : OEv W) (r : Draw S K × K) :
    Stop a b (simWorldD G t₁ e (transW a b x y t₁ e r)).1.1 ∨
      ((simWorldD G t₁ e (transW a b x y t₁ e r)).2 =
          (stepR G a b (ddhOracle (gapDHDef G)) (G.pub x) (G.pub y) t₂ e r).2 ∧
        RelW G a b x y (simWorldD G t₁ e (transW a b x y t₁ e r)).1
          (stepR G a b (ddhOracle (gapDHDef G)) (G.pub x) (G.pub y) t₂ e r).1) := by
  have htr : transW a b x y t₁ e r = (transD a b x y t₁.1 e r.1, r.2) := rfl
  rw [htr]
  rcases rel_start G a b x y h.1 e r.1 with hs | ⟨hd, hr⟩
  · left
    simp only [Stop, simWorldD] at hs ⊢
    rw [stop_drive0D _ _ (fun _ _ => rfl)]
    exact hs
  · right
    simp only [simWorldD, stepR]
    rw [hd, h.2]
    generalize (simStartD G t₁.1 e (transD a b x y t₁.1 e r.1)).1 = s₁ at hr
    generalize (startR G a b (ddhOracle (gapDHDef G)) (G.pub x) (G.pub y) t₂.1 e r.1).1 = s₂ at hr
    obtain ⟨rs₁, inp₁, ph₁⟩ := s₁
    obtain ⟨rs₂, inp₂, ph₂⟩ := s₂
    have hr' : RelC G a b x y rs₁ inp₁ ph₁ rs₂ inp₂ ph₂ := hr
    cases (startR G a b (ddhOracle (gapDHDef G)) (G.pub x) (G.pub y) t₂.1 e r.1).2 with
    | inr o => exact ⟨rfl, hr, rfl⟩
    | inl g =>
      simp only [drive0D, finV, finR]
      rw [hr'.ph]
      exact ⟨rfl, hr'.setPh G a b x y _, rfl⟩

omit [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
theorem lookup_mem {α β : Type} [DecidableEq α] {u : α} {v : β} :
    ∀ {l : List (α × β)}, l.lookup u = some v → (u, v) ∈ l
  | [], h => by simp at h
  | (u', v') :: l, h => by
    rw [lookup_cons] at h
    by_cases hu : u = u'
    · subst hu
      simp only [↓reduceIte, Option.some.injEq] at h
      subst h
      exact List.mem_cons_self
    · simp only [hu, ↓reduceIte] at h
      exact List.mem_cons_of_mem _ (lookup_mem h)

omit [Fintype S] [Fintype K] [Nonempty K] [Inhabited K] in
/-- **The bad event of the pair, on related states,** is the event `Bad2` of the world of the
reduction. -/
theorem bad2_of_rel {t₁ : SimSt S W K × St K} {t₂ : RSim S W K × St K}
    (h : RelW G a b x y t₁ t₂) (hb : DH1HitAB G a b t₁.1) : Bad2 G a b x y t₂ := by
  obtain ⟨ip, v, ikA, spkA, ikB, spkB, hl, hia, hrb, -, -, hla, hlb, hd⟩ := hb
  have hR : RelC G a b x y t₁.1.1 t₁.1.2.1 t₁.1.2.2 t₂.1.1 t₂.1.2.1 t₂.1.2.2 := h.1
  have hm := lookup_mem hl
  rw [hR.ro, List.mem_map] at hm
  obtain ⟨p, hp, hpe⟩ := hm
  simp only [interpE, Prod.mk.injEq] at hpe
  obtain ⟨hpi, -⟩ := hpe
  have hpa : p.1.ini = a := by rw [← hia, ← hpi]; rfl
  have hpb : p.1.res = b := by rw [← hrb, ← hpi]; rfl
  have hlA := hR.lt a
  have hlB := hR.lt b
  rw [hla] at hlA
  rw [hlb] at hlB
  cases hA : t₂.1.1.lt a with
  | none => rw [hA] at hlA; cases hlA
  | some la =>
    cases hB : t₂.1.1.lt b with
    | none => rw [hB] at hlB; cases hlB
    | some lb =>
      rw [hA, Option.map_some, Option.some.injEq] at hlA
      rw [hB, Option.map_some, Option.some.injEq] at hlB
      have hik : ikA = x + off1 a t₂.1.1 := by
        simp only [off1, hA, Option.map_some, Option.getD_some]
        have := congrArg Prod.fst hlA
        simp only [sh, ↓reduceIte] at this
        exact this
      have hspk : spkB = y + off2 b t₂.1.1 := by
        simp only [off2, hB, Option.map_some, Option.getD_some]
        have := congrArg Prod.snd hlB
        simp only [sh, ↓reduceIte] at this
        exact this
      refine ⟨p, hp, hpa, hpb, by rw [hA]; rfl, by rw [hB]; rfl, ?_⟩
      have hL := hR.abL p hp hpa hpb
      rcases hq : p.1.dh1 with w | E
      · have h1 : ip.dh1 = w := by rw [← hpi]; simp only [interp, hq, ev]
        rw [← h1, hd, hik, hspk]
      · rw [hq] at hL; cases hL

omit [Field S] [Fintype S] [Fintype K] [Nonempty K] in
theorem deliverD_corrupt (rs : RSt S W K) (inp : Inst → Option (Inp W)) (z : Inst) (rc : Rec K)
    (ip : Inp W) (k : K) : (deliverD rs inp z rc ip k).1.1.st.corrupt = rs.st.corrupt := by
  unfold deliverD
  split <;> rfl

omit [Fintype K] [Nonempty K] [Inhabited K] in
theorem addSession_corrupt (t : St K) (z : Inst) (peer : PartyId) (role : Role) :
    (addSession t z peer role).corrupt = t.corrupt := by
  unfold addSession
  split <;> rfl

omit [Fintype S] [Fintype K] [Nonempty K] in
/-- The start of the simulator never clears a corruption. -/
theorem simStartD_corrupt (s : SimSt S W K) (e : OEv W) (r : Draw S K) (p : PartyId)
    (h : s.1.st.corrupt p = true) : (simStartD G s e r).1.1.st.corrupt p = true := by
  rcases e with (⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) | (_ | _ | pid | ⟨sid, pid⟩ | pid |
    ⟨sid, pid⟩ | ⟨sid, pid, e⟩ | q)
  all_goals simp only [simStartD, simCompleteD, simSendD]
  all_goals repeat' split
  all_goals simp_all [deliverD_corrupt, addSession_corrupt, (pollStep_fst _).2.1, corruptStep,
    ltD_st, Function.update_apply]

omit [Fintype S] [Fintype K] [Nonempty K] in
/-- A step of the simulated world never clears a corruption of `a` or `b`. -/
theorem stop_simWorldD (t : SimSt S W K × St K) (e : OEv W) (r : Draw S K × K)
    (h : Stop a b t.1) : Stop a b (simWorldD G t e r).1.1 := by
  simp only [Stop, simWorldD]
  rw [stop_drive0D _ _ (fun _ _ => rfl)]
  rcases h with h | h
  · exact Or.inl (simStartD_corrupt G _ _ _ _ h)
  · exact Or.inr (simStartD_corrupt G _ _ _ _ h)

/-- The tables of the world of the reduction grow and its long-term secrets stay. -/
def Mono (rs rs' : RSt S (W ⊕ W) K) : Prop :=
  (∀ p ∈ rs.ro, p ∈ rs'.ro) ∧ (∀ q v, rs.lt q = some v → rs'.lt q = some v)

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
theorem Mono.trans {rs rs' rs'' : RSt S (W ⊕ W) K} (h : Mono rs rs') (h' : Mono rs' rs'') :
    Mono rs rs'' :=
  ⟨fun p hp => h'.1 p (h.1 p hp), fun q v hq => h'.2 q v (h.2 q v hq)⟩

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
theorem mono_refl (rs : RSt S (W ⊕ W) K) : Mono rs rs := ⟨fun _ h => h, fun _ _ h => h⟩

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
theorem mono_ltD (rs : RSt S (W ⊕ W) K) (p : PartyId) (l : S × S) : Mono rs (ltD rs p l).2 :=
  ⟨fun q hq => by rw [ltD_ro]; exact hq, ltD_lt_mono rs p l⟩

omit [Fintype S] [Fintype K] [Nonempty K] in
theorem mono_deliverR (O : W → W → W → Bool) (X Y : W) (rs : RSt S (W ⊕ W) K)
    (inp : Inst → Option (Inp (W ⊕ W))) (z : Inst) (rc : Rec K) (ip : Inp (W ⊕ W)) (k : K) :
    Mono rs (deliverR G a b O X Y rs inp z rc ip k).1.1 := by
  unfold deliverR
  split
  · refine ⟨fun q hq => ?_, fun _ _ h => h⟩
    rcases sroDet_snd G O (keyA G a X rs) (keyB G b Y rs) rs.ro ip k with he | he <;>
      simp only [X3DHSquare.keyed, he]
    · exact hq
    · exact List.mem_cons_of_mem _ hq
  · exact mono_refl _

omit [Fintype S] [Fintype K] [Nonempty K] in
/-- **The start of the simulator of the reduction** keeps the entries of the table and the drawn
secrets. -/
theorem mono_startR (O : W → W → W → Bool) (X Y : W) (s : RSim S W K) (e : OEv W)
    (r : Draw S K) : Mono s.1 (startR G a b O X Y s e r).1.1 := by
  rcases e with (⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) | (_ | _ | pid | ⟨sid, pid⟩ | pid |
    ⟨sid, pid⟩ | ⟨sid, pid, e⟩ | q)
  · simp only [startR]
    split
    · exact mono_refl _
    · exact mono_refl _
  · exact mono_refl _
  · exact mono_refl _
  · exact mono_refl _
  · exact mono_ltD _ _ _
  · exact mono_refl _
  · simp only [startR]
    split
    · exact mono_refl _
    · exact mono_ltD _ _ _
  · simp only [startR, completeR]
    repeat' split
    all_goals first
      | exact mono_refl _
      | exact ((mono_ltD _ _ _).trans (mono_ltD _ _ _)).trans (mono_deliverR G a b O X Y _ _ _ _ _ _)
  · simp only [startR, sendR]
    repeat' split
    all_goals first
      | exact mono_refl _
      | exact ((mono_ltD _ _ _).trans (mono_ltD _ _ _)).trans (mono_deliverR G a b O X Y _ _ _ _ _ _)
  · simp only [startR]
    refine ⟨fun p hp => ?_, fun _ _ h => h⟩
    rcases sroDet_snd G O (keyA G a X s.1) (keyB G b Y s.1) s.1.ro (ofInp q) r.2.2.2 with he | he <;>
      simp only [he]
    · exact hp
    · exact List.mem_cons_of_mem _ hp

omit [Fintype S] [Fintype K] [Nonempty K] in
theorem mono_stepR (O : W → W → W → Bool) (X Y : W) (t : RSim S W K × St K) (e : OEv W)
    (r : Draw S K × K) : Mono t.1.1 (stepR G a b O X Y t e r).1.1.1 := by
  simp only [stepR]
  rw [stop_drive0D _ _ (fun _ _ => rfl)]
  exact mono_startR G a b O X Y t.1 e r.1

omit [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
theorem Bad2.mono {t t' : RSim S W K × St K} (h : Mono t.1.1 t'.1.1) (hb : Bad2 G a b x y t) :
    Bad2 G a b x y t' := by
  obtain ⟨p, hp, h1, h2, ha, hb', hd⟩ := hb
  obtain ⟨la, hla⟩ := Option.isSome_iff_exists.mp ha
  obtain ⟨lb, hlb⟩ := Option.isSome_iff_exists.mp hb'
  have hoff1 : off1 a t'.1.1 = off1 a t.1.1 := by simp only [off1, hla, h.2 a la hla]
  have hoff2 : off2 b t'.1.1 = off2 b t.1.1 := by simp only [off2, hlb, h.2 b lb hlb]
  refine ⟨p, h.1 p hp, h1, h2, by rw [h.2 a la hla]; rfl, by rw [h.2 b lb hlb]; rfl, ?_⟩
  rw [hoff1, hoff2]
  exact hd

omit [Fintype K] [Nonempty K] [Inhabited K] in
/-- **The extraction on the event `Bad2`** outputs the Diffie–Hellman value of the challenge. -/
theorem extractR_of_bad2 {t : RSim S W K × St K} (h : Bad2 G a b x y t) :
    extractR G a b (ddhOracle (gapDHDef G)) (G.pub x) (G.pub y) t.1.1 = G.pub (x * y) := by
  obtain ⟨p, hp, h1, h2, -, -, hd⟩ := h
  unfold extractR hitR
  rw [keyA_pub, keyB_pub]
  set f : Inp (W ⊕ W) × K → Option W := fun p =>
    if p.1.ini = a ∧ p.1.res = b then
      match p.1.dh1 with
      | .inl w => if ddhOracle (gapDHDef G) (G.pub (x + off1 a t.1.1)) (G.pub (y + off2 b t.1.1)) w
          then some w else none
      | .inr _ => none
    else none with hf
  have hacc : ∀ q w, f q = some w → w = G.pub ((x + off1 a t.1.1) * (y + off2 b t.1.1)) := by
    intro q w hq
    simp only [hf] at hq
    split_ifs at hq with hq1
    split at hq
    · split_ifs at hq with hq2
      simp only [Option.some.injEq] at hq
      subst hq
      rw [ddhOracle_pub, decide_eq_true_eq, G.exp_pub] at hq2
      rw [hq2, mul_comm]
    · cases hq
  have hpf : f p = some (G.pub ((x + off1 a t.1.1) * (y + off2 b t.1.1))) := by
    simp only [hf, h1, h2, and_self, ↓reduceIte, hd, ddhOracle_pub, G.exp_pub, mul_comm,
      decide_true]
  cases hs : t.1.1.ro.findSome? f with
  | none =>
    rw [List.findSome?_eq_none_iff] at hs
    rw [hs p hp] at hpf
    cases hpf
  | some w =>
    obtain ⟨q, -, hq⟩ := List.exists_of_findSome?_eq_some hs
    rw [hacc q w hq]
    simp only [G.exp_pub, G.mul_pub]
    congr 1
    ring

end World

/-! ## The output of the reduction -/

section Output

variable {S W K : Type} [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K]
  [Inhabited K] (G : DHGroup S W) (a b : PartyId)

/-- **The output distribution of the reduction** is the extraction from the final state of a run
of `B` against the world of the reduction. -/
theorem redPMF_eq (O : W → W → W → Bool) (X Y : W) (B : OracleAdv (OEv W) (OOut S W K) Bool) :
    redPMF G a b O X Y B =
      (OracleAdv.run (oracleR G a b O X Y) B rInitR).map fun z => extractR G a b O X Y z.2.1.1 := by
  have hO : ∀ (t : RSim S W K × St K) (e : OEv W),
      (oracleR G a b O X Y t e).map (Prod.map id fun t => (t, ())) =
        OracleAdv.simOracle (implR G a b O X Y) (fun (_ : Unit) (q : Empty) => q.elim) (t, ()) e := by
    intro t e
    simp only [OracleAdv.simOracle, implR, oracleR, OracleAdv.run_rand, OracleAdv.run_ret,
      PMF.map_comp, PMF.map_bind, PMF.pure_map]
    exact (PMF.bind_pure_comp _ _).symm
  unfold redPMF redTree
  rw [OracleAdv.run_bind, OracleAdv.run_simulate,
    ← OracleAdv.run_map_state _ _ (fun t => (t, ())) hO]
  simp only [PMF.map_comp, PMF.bind_map, OracleAdv.run_ret, PMF.map_bind, Function.comp_def,
    PMF.pure_map]
  exact PMF.bind_pure_comp _ _

/-- **The advantage of the reduction** as a probability over the challenge exponents. -/
theorem gapDH_advantage_gdhRed (B : OracleAdv (OEv W) (OOut S W K) Bool) :
    GapDH_Advantage (gapDHDef G) (gdhRed G a b B) =
      ((PMF.uniformFintype S).bind fun x => (PMF.uniformFintype S).bind fun y =>
        (redPMF G a b (ddhOracle (gapDHDef G)) (G.pub x) (G.pub y) B).map
          fun c => decide (c = G.pub (x * y))) true := by
  unfold GapDH_Advantage
  rw [← prTrue_liftPMF _ Heap.empty]
  congr 1
  funext h
  unfold GapDH_Game
  have hk : (gapDHDef G).keygen = liftPMF ((PMF.uniformFintype S).map fun s => (G.pub s, G.pub s)) :=
    rfl
  simp only [SPComp.monad_bind_eq, gdhRed, hk]
  rw [liftPMF_bind_apply, PMF.bind_map]
  conv_rhs => unfold liftPMF
  rw [PMF.map_bind]
  refine congrArg _ (funext fun x => ?_)
  simp only [Function.comp_apply]
  rw [liftPMF_bind_apply, PMF.bind_map, PMF.map_bind]
  refine congrArg _ (funext fun y => ?_)
  simp only [Function.comp_apply]
  rw [liftPMF_bind_apply, PMF.map_comp, cdh_pub]
  exact PMF.bind_pure_comp _ _

end Output

/-! ## The bad event of a pair under the gap Diffie–Hellman assumption -/

section Pair

variable {S W K : Type} [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K]
  [Inhabited K] (G : DHGroup S W) (a b : PartyId)

/-- The initial state of the simulated world. -/
def simInit : SimSt S W K × St K := ((rInit, fun _ => none, .fwd), initSt)

/-- The oracle of the simulated game on the states of the simulated world. -/
noncomputable def simO (t : SimSt S W K × St K) (e : OEv W) :
    PMF (OOut S W K × (SimSt S W K × St K)) :=
  (simGame G).oracle () t e

open Classical in
/-- **The bad event of the pair `(a, b)` in the simulated world**: the probability that the
table of the simulated world comes to hold an input with initiator `a` and responder `b`, both
uncorrupt, whose `DH1` is `g^{ik_a · spk_b}`. -/
noncomputable def pairBad (B : OracleAdv (OEv W) (OOut S W K) Bool) : ℝ≥0∞ :=
  (OracleAdv.run (OracleAdv.flagWhen (fun _ _ z => DH1HitAB G a b z.2.1) (simO G)) B
    (simInit, false)).toOuterMeasure {y | y.2.2 = true}

omit [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
theorem relW_init (x y : S) : RelW G a b x y (simInit (K := K)) rInitR :=
  ⟨⟨rfl, rfl, fun _ => rfl, rfl, fun _ => rfl, rfl, (fun _ h => by cases h),
    (fun _ _ h => by cases h), (fun _ h => by cases h), (fun _ _ h => by cases h), rfl, rfl⟩, rfl⟩

open Classical in
/-- **The bad event of a pair at fixed challenge exponents** is at most the probability that the
reduction outputs the Diffie–Hellman value. -/
theorem pairBad_le_red (B : OracleAdv (OEv W) (OOut S W K) Bool) (x y : S) :
    pairBad G a b B ≤ ((redPMF G a b (ddhOracle (gapDHDef G)) (G.pub x) (G.pub y) B).map
      fun c => decide (c = G.pub (x * y))) true := by
  have hO : simO G = fun t e => (PMF.uniformFintype (Draw S K × K)).map
      fun r => (simWorldD G t e (transW a b x y t e r)).swap :=
    funext fun t => funext fun e => simGame_oracle_eq_trans G a b x y t e
  have h₁ := flag_le_of_coupling
    (fun t e r => (simWorldD G t e (transW a b x y t e r)).swap)
    (fun t e r => (stepR G a b (ddhOracle (gapDHDef G)) (G.pub x) (G.pub y) t e r).swap)
    (RelW G a b x y) (fun t => Stop a b t.1) (fun t => DH1HitAB G a b t.1) (Bad2 G a b x y)
    (fun t e r h => stop_simWorldD G a b t e _ h)
    (fun t h hb => by
      obtain ⟨_, _, _, _, _, _, _, _, _, ha, hb', _⟩ := hb
      rcases h with h | h <;> simp_all)
    (fun t₁ t₂ h hb => bad2_of_rel G a b x y h hb)
    (fun t₁ t₂ e r h => step_rel G a b x y h e r) B simInit rInitR (relW_init G a b x y)
  have h₂ := run_flag_le_final (oracleR G a b (ddhOracle (gapDHDef G)) (G.pub x) (G.pub y))
    (Bad2 G a b x y) (fun t e hb z hz => by
      simp only [oracleR, PMF.support_map, Set.mem_image] at hz
      obtain ⟨r, -, rfl⟩ := hz
      exact hb.mono G a b x y (mono_stepR G a b _ _ _ t e r)) B rInitR
  unfold pairBad
  rw [hO]
  refine h₁.trans (h₂.trans ?_)
  rw [redPMF_eq, PMF.map_comp, ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  refine PMF.toOuterMeasure_mono _ fun z hz => ?_
  simp only [Set.mem_preimage, Function.comp_apply, Set.mem_singleton_iff, decide_eq_true_eq]
  exact extractR_of_bad2 G a b x y hz.1

/-- **The bad event of a pair is a gap Diffie–Hellman problem**: its probability is at most the
advantage of the reduction `gdhRed G a b B`. -/
theorem pairBad_le_gapDH (B : OracleAdv (OEv W) (OOut S W K) Bool) :
    pairBad G a b B ≤ GapDH_Advantage (gapDHDef G) (gdhRed G a b B) := by
  rw [gapDH_advantage_gdhRed, PMF.bind_apply]
  calc pairBad G a b B = ∑' x : S, PMF.uniformFintype S x *
        ∑' y : S, PMF.uniformFintype S y * pairBad G a b B := by
        simp only [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    _ ≤ _ := by
      refine ENNReal.tsum_le_tsum fun x => ?_
      gcongr
      rw [PMF.bind_apply]
      refine ENNReal.tsum_le_tsum fun y => ?_
      gcongr
      exact pairBad_le_red G a b B x y

end Pair

/-! ## Finitely many parties -/

section Names

variable {S W K : Type} [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K]
  [Inhabited K] (G : DHGroup S W)

/-- An event names parties of `P` where it names parties of a session or of a key-derivation
input: the party and the peer of a new session, the initiator and the responder of a query of the
key derivation. The other events are unconstrained. -/
def EvIn (P : Finset PartyId) : OEv W → Prop
  | .inl (.newSession _ pid peer _) => pid ∈ P ∧ peer ∈ P
  | .inr (.kdf q) => q.ini ∈ P ∧ q.res ∈ P
  | _ => True

/-- **The finite-party predicate**: on every path, the oracle adversary `B` starts sessions only
between parties of `P` and queries the key derivation only at inputs whose initiator and
responder are in `P`. -/
def NamesIn {α : Type} (P : Finset PartyId) (B : OracleAdv (OEv W) (OOut S W K) α) : Prop :=
  AllQ (EvIn P) B

/-- The invariant of the parties: the inputs of the table of the simulator's copy and the
sessions of its records name parties of `P`. -/
def InvP (P : Finset PartyId) (rs : RSt S W K) : Prop :=
  (∀ e ∈ rs.ro, e.1.ini ∈ P ∧ e.1.res ∈ P) ∧
    ∀ z r, rs.st.recs z = some r → z.2 ∈ P ∧ r.peer ∈ P

omit [Fintype K] [Nonempty K] [Inhabited K] in
theorem roDet_mem {D : Type} [DecidableEq D] (tb : List (D × K)) (q : D) (k : K) :
    ∀ e ∈ (roDet tb q k).2, e ∈ tb ∨ e = (q, k) := by
  intro e he
  unfold roDet at he
  split at he
  · exact Or.inl he
  · rcases List.mem_cons.mp he with h | h
    · exact Or.inr h
    · exact Or.inl h

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
theorem InvP.ltD {P : Finset PartyId} {rs : RSt S W K} (h : InvP P rs) (p : PartyId)
    (l : S × S) : InvP P (X3DHSquareHops.ltD rs p l).2 := by
  simp only [InvP, ltD_ro, ltD_st]
  exact h

omit [Field S] [Fintype S] [Fintype K] [Nonempty K] in
theorem InvP.deliverD {P : Finset PartyId} {rs : RSt S W K} (h : InvP P rs)
    (inp : Inst → Option (Inp W)) {z : Inst} {rc : Rec K} (hz : rs.st.recs z = some rc)
    {ip : Inp W} (hip : ip.ini ∈ P ∧ ip.res ∈ P) (k : K) :
    InvP P (X3DHSquareHops.deliverD rs inp z rc ip k).1.1 := by
  have hrecs' : ∀ (v : K) z' r, (setRec rs.st z { rc with key := some v }).recs z' = some r →
      z'.2 ∈ P ∧ r.peer ∈ P := fun v z' r hr => by
    simp only [setRec] at hr
    by_cases hz' : z' = z
    · subst hz'
      simp only [Function.update_self, Option.some.injEq] at hr
      subst hr
      exact h.2 _ rc hz
    · simp only [Function.update_of_ne hz'] at hr
      exact h.2 z' r hr
  unfold X3DHSquareHops.deliverD
  split
  · refine ⟨fun e he => ?_, hrecs' _⟩
    rcases roDet_mem rs.ro ip k e he with he | rfl
    · exact h.1 e he
    · exact hip
  · exact ⟨h.1, hrecs' _⟩

omit [Fintype S] [Fintype K] [Nonempty K] in
/-- **The start of the simulator keeps the invariant of the parties** on the events that name
parties of `P`. -/
theorem invP_simStartD {P : Finset PartyId} (s : SimSt S W K) (e : OEv W) (r : Draw S K)
    (h : InvP P s.1) (he : EvIn P e) : InvP P (simStartD G s e r).1.1 := by
  rcases e with (⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) | (_ | _ | pid | ⟨sid, pid⟩ | pid |
    ⟨sid, pid⟩ | ⟨sid, pid, e⟩ | q)
  · simp only [simStartD]
    split
    · refine ⟨h.1, fun z rz hz => ?_⟩
      simp only [addSession] at hz
      split at hz
      · exact h.2 z rz hz
      · by_cases hzx : z = (sid, pid)
        · subst hzx
          simp only [Function.update_self, Option.some.injEq] at hz
          subst hz
          exact he
        · simp only [Function.update_of_ne hzx] at hz
          exact h.2 z rz hz
    · exact h
  · exact h
  · exact h
  · exact ⟨h.1, fun z rz hz => h.2 z rz (by rw [← (pollStep_fst _).1]; exact hz)⟩
  · exact h.ltD _ _
  · exact h
  · simp only [simStartD]
    split
    · exact h
    · have h' := h.ltD pid r.2.1
      exact ⟨h'.1, fun z rz hz => h'.2 z rz hz⟩
  · simp only [simStartD, simCompleteD]
    split
    · split
      · split
        · exact ((h.ltD _ _).ltD _ _).deliverD _ (by simp only [ltD_st]; assumption)
            (h.2 _ _ (by assumption)) _
        · exact h
      · exact h
    · exact h
  · simp only [simStartD, simSendD]
    split
    · split
      · exact ((h.ltD _ _).ltD _ _).deliverD _ (by simp only [ltD_st]; assumption)
          ⟨(h.2 _ _ (by assumption)).2, (h.2 _ _ (by assumption)).1⟩ _
      · exact h
    · exact h
  · simp only [simStartD]
    refine ⟨fun e' he' => ?_, h.2⟩
    rcases roDet_mem s.1.ro q r.2.2.2 e' he' with he' | rfl
    · exact h.1 e' he'
    · exact he

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
theorem invP_init (P : Finset PartyId) : InvP P (simInit (S := S) (W := W) (K := K)).1.1 :=
  ⟨(fun _ h => by cases h), (fun _ _ h => by cases h)⟩

omit [Fintype S] [Fintype K] [Nonempty K] [Inhabited K] in
/-- On the invariant of the parties, the bad event is the bad event of a pair of `P`. -/
theorem dh1Hit_pair {P : Finset PartyId} {s : SimSt S W K} (h : InvP P s.1) (hd : DH1Hit G s) :
    ∃ ab ∈ P ×ˢ P, DH1HitAB G ab.1 ab.2 s := by
  obtain ⟨ip, v, ikA, spkA, ikB, spkB, hl, hi, hr, hla, hlb, hd⟩ := hd
  have hm := h.1 _ (lookup_mem hl)
  exact ⟨(ip.ini, ip.res), Finset.mem_product.mpr hm, ip, v, ikA, spkA, ikB, spkB, hl, rfl, rfl,
    hi, hr, hla, hlb, hd⟩

open Classical in
/-- The bad-event experiment of `X3DHSquareHops` is the flag of `DH1Hit` in the simulated world. -/
theorem badGame_eq_sim (B : OracleAdv (OEv W) (OOut S W K) Bool) :
    badGame G B true =
      (OracleAdv.run (OracleAdv.flagWhen (fun _ _ z => DH1Hit G z.2.1) (simO G))
        B (simInit, false)).toOuterMeasure {y | y.2.2 = true} := by
  have hJ : ∀ (s : JSt S W K) (e : OEv W),
      (jointSim G s e).map (Prod.map id fun s' => s'.1.1) = simO G s.1.1 e := jointSim_map G
  have hO : ∀ (st : JSt S W K × Bool) (d : OEv W),
      (OracleAdv.flagWhen (fun _ _ x => DH1Hit G x.2.1.1.1) (jointSim G) st d).map
          (Prod.map id fun st => (st.1.1.1, st.2)) =
        OracleAdv.flagWhen (fun _ _ z => DH1Hit G z.2.1) (simO G) (st.1.1.1, st.2) d := by
    intro st d
    simp only [OracleAdv.flagWhen]
    rw [← hJ st.1 d, PMF.map_comp, PMF.map_comp]
    rfl
  unfold badGame
  rw [map_flag_apply]
  have h := congrArg (fun p => PMF.toOuterMeasure p {y | y.2.2 = true})
    (OracleAdv.run_map_state _ _ _ hO B (jointInit, false))
  simp only [PMF.toOuterMeasure_map_apply] at h
  exact h

open Classical in
/-- **The bad event of the X3DH square under the gap Diffie–Hellman assumption.** For an oracle
adversary `B` that names only parties of the finite set `P`, the probability of the bad event
`DH1Hit` is at most the sum over the pairs `(a, b)` of `P` of the gap Diffie–Hellman advantages of
the reductions `gdhRed G a b B`. -/
theorem badGame_le_gapDH (P : Finset PartyId) (B : OracleAdv (OEv W) (OOut S W K) Bool)
    (hB : NamesIn P B) :
    badGame G B true ≤ ∑ a ∈ P, ∑ b ∈ P, GapDH_Advantage (gapDHDef G) (gdhRed G a b B) := by
  rw [badGame_eq_sim]
  have hI : ∀ (t : SimSt S W K × St K) (e : OEv W), InvP P t.1.1 → EvIn P e →
      ∀ x ∈ (simO G t e).support, InvP P x.2.1.1 := by
    intro t e ht he x hx
    rw [simO, simGame_oracle_eq] at hx
    obtain ⟨r, -, hr⟩ := (PMF.mem_support_map_iff _ _ _).mp hx
    rw [← hr]
    simp only [Prod.snd_swap, simWorldD]
    rw [stop_drive0D _ _ (fun _ _ => rfl)]
    exact invP_simStartD G t.1 e r.1 ht he
  have h₁ := run_flag_le_of_inv_on (simO G) (EvIn P) (fun t => InvP P t.1.1)
    (fun t => DH1Hit G t.1) (fun t => ∃ ab ∈ P ×ˢ P, DH1HitAB G ab.1 ab.2 t.1) hI
    (fun t ht hd => dh1Hit_pair G ht hd) B hB simInit (invP_init P)
  have h₂ := run_flag_union_le (simO G) (fun ab t => DH1HitAB G ab.1 ab.2 t.1) (P ×ˢ P) B simInit
  have h₃ : ∑ ab ∈ P ×ˢ P, pairBad G ab.1 ab.2 B ≤
      ∑ ab ∈ P ×ˢ P, GapDH_Advantage (gapDHDef G) (gdhRed G ab.1 ab.2 B) :=
    Finset.sum_le_sum fun ab _ => pairBad_le_gapDH G ab.1 ab.2 B
  exact (h₁.trans (h₂.trans h₃)).trans_eq (Finset.sum_product _ _ _)

open Classical in
/-- The bound of the X3DH square at the oracle adversary `B` and the finite set of parties `P`:
the sum over the pairs of `P` of the gap Diffie–Hellman advantages of `gdhRed`, when `B` names
only parties of `P`, and `⊤` otherwise. -/
noncomputable def gdhBound (P : Finset PartyId) (B : OracleAdv (OEv W) (OOut S W K) Bool) :
    ℝ≥0∞ :=
  if NamesIn P B then ∑ a ∈ P, ∑ b ∈ P, GapDH_Advantage (gapDHDef G) (gdhRed G a b B) else ⊤

/-- **X3DH realizes `F_AKE` behind `x3dhSim` under the gap Diffie–Hellman assumption.** For
every finite set of parties `P` and every environment `Z` whose oracle reduction
`OProt.oracle.reduction Z` names only parties of `P`, the distance between the real X3DH protocol
and the simulator running with `F_AKE` is at most the sum over the pairs `(a, b)` of `P` of the
gap Diffie–Hellman advantages of the reductions `gdhRed G a b (OProt.oracle.reduction Z)`; the
bound is `⊤` for the other environments. -/
theorem x3dh_realizesSim_gapDH (P : Finset PartyId) :
    RealizesSim (x3dhReal (K := K) G) (F_AKE (SPComp.sample K) true) (x3dhSim G)
      (fun _ Z => gdhBound G P ((OProt.oracle (Q := OEv W) (A := OOut S W K)).reduction Z)) :=
  fun ζ Z => (x3dh_realizesSim_oracleGame G ζ Z).trans (by
    by_cases hN : NamesIn P ((OProt.oracle (Q := OEv W) (A := OOut S W K)).reduction Z)
    · simp only [gdhBound, hN, ↓reduceIte]
      exact (x3dh_advantage_le_badGame G _).trans (badGame_le_gapDH G P _ hN)
    · simp only [gdhBound, hN, ↓reduceIte]
      exact le_top)

end Names

end CatCrypt.Crypto.AKE.X3DHSquareGDH
