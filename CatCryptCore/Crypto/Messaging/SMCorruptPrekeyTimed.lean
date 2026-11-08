/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.SMCorruptPrekey
public import CatCryptCore.Crypto.Messaging.SMCorruptTimed

/-!
# Running time of the first-epoch PRF-PRNG reduction

Time certificate of the reduction `smcRootRedFirst` of
`CatCryptCore.Crypto.Messaging.SMCorruptPrekey`.

The reduction is the oracle tree `smRootTreeFirst` with the challenge-epoch distribution and the
interaction of the adversary as parameters; its costed form is derived by `derive_timed`. The
costed simulator `smRootImplFirst.timed` answers the `i`-th query in time at most
`smQueryTime s v r g e (1 + 3 i)` under the companion invariant `smCostInv (1 + 3 i)`
(`smRootImplFirst.timed_bound`), the bound of the simulator `smRootImplOf` of
`CatCryptCore.Crypto.Messaging.SMCorruptTimed`. For an adversary of time `T` with at most `q`
queries and call cost at most `a`, the reduction tree has time at most
`T + ∑_{j < q} smQueryTime s v r g e (1 + 3 j) + a + 8`, a polynomial of degree two in `q`.

No module imports this file.

## Main results

* `smRootImplFirst.timed_bound` — the time of a simulated query
* `smcRootRedFirst.timeBound_timed` — the time of the derived costed tree of `smRootTreeFirst`
* `smcRootRedFirst.tree`, `smcRootRedFirst.compile_tree`,
  `smcRootRedFirst.tree.timeBound_timed` — the reduction is the erasure of the derived costed
  tree, of time at most the bound above plus one
-/

set_option autoImplicit false

@[expose] public section

namespace CatCrypt.Crypto.Messaging

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Assumptions

derive_timed smRootTreeFirst

variable {Sc Msg Key Rand RK Sa W Ct : Type} [Fintype Rand] [Nonempty Rand] [SampleableType W]
  [SampleableType Ct]

/-- **Time of a query of the first-epoch PRF-PRNG simulator.** From a costed state with
companions at most `1 + 3 i`, the costed simulator `smRootImplFirst` answers in time at most
`smQueryTime s v r g e (1 + 3 i)` and returns states with companions at most `1 + 3 (i + 1)`. -/
theorem smRootImplFirst.timed_bound (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t : ℕ) (ideal : Bool) (σ : SMSt Sc Msg RK Sa) (q : SMQuery W)
    (sCost : Sc → Rand → ℕ) (rCost : RK × Key → ℕ) (vCost : Sc → Msg → ℕ)
    (eCost : W → W → W → ℕ) (gCost : Sa → ℕ) {s v r g e : ℕ} (hs : ∀ x c, sCost x c ≤ s)
    (hv : ∀ x m, vCost x m ≤ v) (hr : ∀ x, rCost x ≤ r) (he : ∀ k m a, eCost k m a ≤ e)
    (hg : ∀ x, gCost x ≤ g) (i : ℕ) (loc ck) (hinv : smCostInv (1 + 3 * i) ck loc) :
    OracleAdv.Timed.StepTimeBound (OracleAdv.Timed.delay 1
        (smRootImplFirst.timed C R G D ΔFS ΔPCS t ideal σ q sCost loc rCost ck vCost eCost gCost))
        (smQueryTime s v r g e (1 + 3 * i)) ∧
      OracleAdv.Timed.AllRet (fun y => smCostInv (1 + 3 * (i + 1)) y.2.1 y.2.2)
        (smRootImplFirst.timed C R G D ΔFS ΔPCS t ideal σ q sCost loc rCost ck vCost eCost
          gCost).2 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hinv
  unfold smCostInv smQueryTime
  cases q with
  | ratchet p =>
    simp only [smRootImplFirst.timed, smRootRatchetFirst.timed, OracleAdv.Timed.delay,
      OracleAdv.Timed.StepTimeBound]
    split
    · sm_cost_steps
    · simp only [smRootRatchet.timed, OracleAdv.Timed.delay]
      sm_cost_steps
  | _ =>
    simp only [smRootImplFirst.timed, smRootRecv.timed, smFullSend.timed, smFullChall.timed,
      smFullCorr.timed, OracleAdv.Timed.delay, OracleAdv.Timed.StepTimeBound]
    sm_cost_steps

variable [Fintype RK] [Nonempty RK]

/-- The oracle tree of the reduction `smcRootRedFirst`: the tree `smRootTreeFirst` with the
challenge-epoch distribution and the interaction of the adversary as parameters. -/
noncomputable def smcRootRedFirst.tree (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS : ℕ) (ideal : Bool) (i : Msg × Sc × Sc) (tStar : PMF ℕ)
    (play : ℕ → Msg → OracleAdv (SMQuery W) (SMAns Sc Msg RK Sa Ct) Bool) :
    OracleAdv (PPQuery RK Key) (RK × Sa) Bool :=
  smRootTreeFirst C R G D ΔFS ΔPCS ideal i tStar play

derive_timed smcRootRedFirst.tree

/-- The derived costed tree of `smcRootRedFirst`, at the challenge-epoch distribution of `A` and
a costed interaction `play` that erases to the interaction of `A`, erases to the reduction. -/
theorem smcRootRedFirst.compile_tree (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS : ℕ) (ideal : Bool) (i : Msg × Sc × Sc) (A : SMCorruptAdv Sc Msg RK Sa W Ct)
    (play : ℕ → Msg → OracleAdv.Timed (SMQuery W) (SMAns Sc Msg RK Sa Ct) Bool)
    (playCost : ℕ → Msg → ℕ) (hplay : ∀ t g, (play t g).erase = A.play t g)
    (sCost : Sc → Rand → ℕ) (rCost : RK × Key → ℕ) (vCost : Sc → Msg → ℕ)
    (eCost : W → W → W → ℕ) (gCost : Sa → ℕ) :
    (smcRootRedFirst.tree.timed C R G D ΔFS ΔPCS ideal i A.tStar play playCost sCost rCost vCost
      eCost gCost).2.erase = smcRootRedFirst C R G D ΔFS ΔPCS ideal i A := by
  rw [smcRootRedFirst.tree.erase_timed]
  have h : (fun t g => (play t g).erase) = A.play := funext fun t => funext (hplay t)
  rw [h]
  rfl

/-- **Time of the first-epoch PRF-PRNG reduction.** For a costed interaction of time at most
`T`, at most `q` queries and call cost at most `a`, CKA sends of cost at most `s`, CKA receives
of cost at most `v`, root steps of cost at most `r`, chain steps of cost at most `g` and
encryptions of cost at most `e`, the derived costed tree of `smcRootRedFirst` has time at most
`T + ∑_{j < q} smQueryTime s v r g e (1 + 3 j) + a + 8`. -/
theorem smcRootRedFirst.timeBound_timed (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS : ℕ) (ideal : Bool) (i : Msg × Sc × Sc) (tStar : PMF ℕ)
    (play : ℕ → Msg → OracleAdv.Timed (SMQuery W) (SMAns Sc Msg RK Sa Ct) Bool)
    (playCost : ℕ → Msg → ℕ) (sCost : Sc → Rand → ℕ) (rCost : RK × Key → ℕ)
    (vCost : Sc → Msg → ℕ) (eCost : W → W → W → ℕ) (gCost : Sa → ℕ) {T q a s v r g e : ℕ}
    (hA : ∀ t g, (play t g).TimeBound T) (hq : ∀ t g, (play t g).erase.IsQueryBound q)
    (ha : ∀ t g, playCost t g ≤ a) (hs : ∀ x c, sCost x c ≤ s) (hv : ∀ x m, vCost x m ≤ v)
    (hr : ∀ x, rCost x ≤ r) (he : ∀ k m a, eCost k m a ≤ e) (hg : ∀ x, gCost x ≤ g) :
    OracleAdv.Timed.StepTimeBound
      (smRootTreeFirst.timed C R G D ΔFS ΔPCS ideal i tStar play playCost sCost rCost vCost
        eCost gCost)
      (T + ∑ j ∈ Finset.range q, smQueryTime s v r g e (1 + 3 * j) + a + 8) := by
  unfold smRootTreeFirst.timed
  refine (timeBound_rand_zero _ _ fun t => timeBound_rand_cost_bind_fst (K := 4 + a)
    (B := T + ∑ j ∈ Finset.range q, smQueryTime s v r g e (1 + 3 * j)) _ _ _
    (fun _ => by have := ha t i.1; omega) fun rk => ?_).mono (by omega)
  refine (OracleAdv.Timed.timeBound_simulateHat_inv _ _ _
    (fun i ŝ => smCostInv (1 + 3 * i) ŝ.1 ŝ.2) (fun i => smQueryTime s v r g e (1 + 3 * i))
    (fun i ŝ d h => smRootImplFirst.timed_bound C R G D ΔFS ΔPCS t ideal _ d sCost rCost vCost
      eCost gCost hs hv hr he hg i _ _ h)
    (hA t i.1) (hq t i.1) 0 _ ?_).mono ?_
  · refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_⟩ <;>
      dsimp only <;> omega
  · simp only [Nat.zero_add, le_refl]

/-- **Time of `smcRootRedFirst`.** The derived costed tree `smcRootRedFirst.tree.timed` has the
time bound of `smcRootRedFirst.timeBound_timed` plus one step:
`T + ∑_{j < q} smQueryTime s v r g e (1 + 3 j) + a + 9`. -/
theorem smcRootRedFirst.tree.timeBound_timed (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS : ℕ) (ideal : Bool) (i : Msg × Sc × Sc) (tStar : PMF ℕ)
    (play : ℕ → Msg → OracleAdv.Timed (SMQuery W) (SMAns Sc Msg RK Sa Ct) Bool)
    (playCost : ℕ → Msg → ℕ) (sCost : Sc → Rand → ℕ) (rCost : RK × Key → ℕ)
    (vCost : Sc → Msg → ℕ) (eCost : W → W → W → ℕ) (gCost : Sa → ℕ) {T q a s v r g e : ℕ}
    (hA : ∀ t g, (play t g).TimeBound T) (hq : ∀ t g, (play t g).erase.IsQueryBound q)
    (ha : ∀ t g, playCost t g ≤ a) (hs : ∀ x c, sCost x c ≤ s) (hv : ∀ x m, vCost x m ≤ v)
    (hr : ∀ x, rCost x ≤ r) (he : ∀ k m a, eCost k m a ≤ e) (hg : ∀ x, gCost x ≤ g) :
    OracleAdv.Timed.StepTimeBound
      (smcRootRedFirst.tree.timed C R G D ΔFS ΔPCS ideal i tStar play playCost sCost rCost vCost
        eCost gCost)
      (T + ∑ j ∈ Finset.range q, smQueryTime s v r g e (1 + 3 * j) + a + 9) := by
  unfold smcRootRedFirst.tree.timed
  exact (OracleAdv.Timed.stepTimeBound_delay (smcRootRedFirst.timeBound_timed C R G D ΔFS ΔPCS
    ideal i tStar play playCost sCost rCost vCost eCost gCost hA hq ha hs hv hr he hg)).mono
    (by omega)

end CatCrypt.Crypto.Messaging
