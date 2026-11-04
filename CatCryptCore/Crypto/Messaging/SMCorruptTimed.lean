/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.SMCorrupt

/-!
# Running time of the reductions of secure messaging with state corruption

DOC

No module imports this file.
-/

set_option autoImplicit false

@[expose] public section

namespace CatCrypt.Crypto.Messaging

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Assumptions

/-! ## The dual-PRF reductions of the PRF-PRNG game -/

section PRFPRNGTime

variable {RK Key Out : Type}

/-- The time of a tree that draws `x` from `μ` and then runs a step-prefixed tree `S x` of time
at most `B`, returning the first component of its output. -/
theorem timeBound_rand_bind_fst {D R X Ŝ : Type} (μ : PMF X)
    (S : X → ℕ × OracleAdv.Timed D R (Bool × Ŝ)) {B : ℕ}
    (hS : ∀ x, OracleAdv.Timed.StepTimeBound (S x) B) :
    OracleAdv.Timed.StepTimeBound (0, OracleAdv.Timed.rand μ
      (fun x => (S x).1 + ((S x).2.bind fun r => (0, OracleAdv.Timed.ret r.1)).1)
      fun x => ((S x).2.bind fun r => (0, OracleAdv.Timed.ret r.1)).2) (B + 1) := by
  refine ⟨Nat.zero_le _, by dsimp only; omega, fun x => ?_⟩
  obtain ⟨h1, h2⟩ := hS x
  obtain ⟨h3, h4⟩ := OracleAdv.Timed.timeBound_bind (n := 0) h2
    (f := fun r => (0, OracleAdv.Timed.ret r.1)) fun _ => ⟨le_refl _, trivial⟩
  refine ⟨by dsimp only; omega, h4.mono ?_⟩
  dsimp only; omega

variable [Fintype RK] [Nonempty RK]

/-- **Time of `ppRedR`.** For a costed adversary of time at most `T` and at most `q` queries,
and a root step `F` of cost at most `c`, the costed right dual-PRF reduction has time at most
`T + q (c + 3) + 1`: one simulated query costs the root step on the drawn root state, or the
forwarded query. -/
theorem ppRedR.timeBound_timed (F : RK → Key → Out) (FCost : RK → Key → ℕ)
    (A : OracleAdv.Timed (PPQuery RK Key) Out Bool) {T q c : ℕ} (hA : A.TimeBound T)
    (hq : A.erase.IsQueryBound q) (hF : ∀ rk I, FCost rk I ≤ c) :
    OracleAdv.Timed.StepTimeBound (ppRedR.timed F FCost A) (T + q * (c + 3) + 1) := by
  unfold ppRedR.timed
  refine timeBound_rand_bind_fst _ _ fun rk => ?_
  refine OracleAdv.Timed.timeBound_simulate _ (fun u d => ?_) hA hq ()
  cases d with
  | prng I =>
    have := hF rk I
    refine ⟨?_, trivial⟩
    simp only [OracleAdv.Timed.delay, ppImplR.timed]; omega
  | prf r =>
    refine ⟨by simp only [OracleAdv.Timed.delay, ppImplR.timed]; omega, ?_⟩
    simp only [OracleAdv.Timed.delay, ppImplR.timed]
    exact ⟨by omega, fun _ => ⟨by dsimp only; omega, trivial⟩⟩

variable [Fintype Out] [Nonempty Out] [DecidableEq RK]

/-- The time of the `i`-th simulated query of `ppRedL`: the search of the table of the random
function, of at most `i` entries. -/
def ppQueryTimeL (i : ℕ) : ℕ := 5 * i + 6

omit [Fintype RK] [Nonempty RK] in
/-- **Time of `ppRedL`.** For a costed adversary of time at most `T` and at most `q` queries,
the costed left dual-PRF reduction has time at most `T + ∑_{j < q} (5 j + 6)`: the table of the
lazily sampled random function grows by at most one entry per query. -/
theorem ppRedL.timeBound_timed (A : OracleAdv.Timed (PPQuery RK Key) Out Bool) {T q : ℕ}
    (hA : A.TimeBound T) (hq : A.erase.IsQueryBound q) :
    OracleAdv.Timed.StepTimeBound (ppRedL.timed A)
      (T + ∑ j ∈ Finset.range q, ppQueryTimeL j) := by
  unfold ppRedL.timed
  have hS := OracleAdv.Timed.timeBound_simulateHat_inv (fun σ => σ) (fun σ => σ)
    (fun σ d => OracleAdv.Timed.delay 1 (ppImplL.timed (Key := Key) σ d))
    (fun i (σ : List (RK × Out)) => σ.length ≤ i) ppQueryTimeL
    (fun i σ d hσ => by
      have hl := fun r => List.lookup.timedCost_le r σ
      cases d with
      | prng I =>
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · simp only [OracleAdv.Timed.delay, ppImplL.timed, ppQueryTimeL]; omega
        · simp only [OracleAdv.Timed.delay, ppImplL.timed, ppQueryTimeL]
          exact ⟨by omega, fun _ => ⟨by dsimp only; omega, trivial⟩⟩
        · simp only [OracleAdv.Timed.delay, ppImplL.timed, OracleAdv.Timed.AllRet]
          intro _; omega
      | prf r =>
        have := hl r
        simp only [OracleAdv.Timed.delay, ppImplL.timed, ppQueryTimeL]
        split
        · exact ⟨⟨by omega, trivial⟩, by simp only [OracleAdv.Timed.AllRet]; omega⟩
        · refine ⟨⟨by dsimp only; omega, by dsimp only; omega,
            fun _ => ⟨by dsimp only; omega, trivial⟩⟩, ?_⟩
          simp only [OracleAdv.Timed.AllRet, List.length_cons]; intro _; omega)
    hA hq 0 [] (Nat.le_refl _)
  unfold OracleAdv.Timed.simulateHat at hS
  simp only [Nat.zero_add] at hS
  obtain ⟨h1, h2⟩ := hS
  obtain ⟨h3, h4⟩ := OracleAdv.Timed.timeBound_bind (n := 0) h2
    (f := fun r => (0, OracleAdv.Timed.ret r.1)) fun _ => ⟨le_refl _, trivial⟩
  exact (OracleAdv.Timed.stepTimeBound_delay ⟨h3, h4⟩).mono (by omega)

end PRFPRNGTime

/-! ## The CKA reduction -/

section CKATime

variable {Sc Msg Key Rand RK Sa W Ct : Type} [SampleableType W] [SampleableType Ct]

/-- The bound `B` on the cost companions of a costed state of the CKA simulator: the companions
of the root keys, the sending and receiving chains, the CKA shadow states and the counters. -/
def smCKACostInv (B : ℕ)
    (fh : ((CKAParty → RK) × (CKAParty → ℕ)) × ((CKAParty → Option Sa) × (CKAParty → ℕ)) ×
      ((CKAParty → Option Sa) × (CKAParty → ℕ)) × Option (RK × Sa) × Bool)
    (sh : ((CKAParty → Unit) × (CKAParty → ℕ)) × ((CKAParty → ℕ) × (CKAParty → ℕ)) × Unit) :
    Prop :=
  (∀ p, fh.1.2 p ≤ B) ∧ (∀ p, fh.2.1.2 p ≤ B) ∧ (∀ p, fh.2.2.1.2 p ≤ B) ∧
    (∀ p, sh.1.2 p ≤ B) ∧ ∀ p, sh.2.1.2 p ≤ B

/-- The time of a simulated query of the CKA reduction from a state with companions at most
`B`, with root steps of cost at most `r`, chain steps of cost at most `g` and encryptions of
cost at most `e`. -/
def smCKAQueryTime (r g e B : ℕ) : ℕ := r + 2 * g + e + 6 * B + 50

theorem smCKAImplOf.timed_bound (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa))
    (D : AEADDef W Ct) (t : ℕ) (ideal : Bool) (σ : SMLoc RK Sa × CKAGameSt Unit Unit)
    (q : SMQuery W) (rCost : RK × Key → ℕ) (eCost : W → W → W → ℕ) (gCost : Sa → ℕ)
    {r g e : ℕ} (hr : ∀ x, rCost x ≤ r) (he : ∀ k m a, eCost k m a ≤ e) (hg : ∀ s, gCost s ≤ g)
    (i : ℕ) (fh sh) (hinv : smCKACostInv (1 + 3 * i) fh sh) :
    OracleAdv.Timed.StepTimeBound (OracleAdv.Timed.delay 1
        (smCKAImplOf.timed (Sc := Sc) (Msg := Msg) (Rand := Rand) R G D t ideal σ q rCost fh sh
          eCost gCost)) (smCKAQueryTime r g e (1 + 3 * i)) ∧
      OracleAdv.Timed.AllRet (fun y => smCKACostInv (1 + 3 * (i + 1)) y.2.1 y.2.2)
        (smCKAImplOf.timed (Sc := Sc) (Msg := Msg) (Rand := Rand) R G D t ideal σ q rCost fh sh
          eCost gCost).2 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hinv
  unfold smCKACostInv smCKAQueryTime
  cases q <;>
    simp only [smCKAImplOf.timed, smCKARatchet.timed, smCKARecvT.timed, smCKASendT.timed,
      smCKAChallT.timed, smCKACorrT.timed, OracleAdv.Timed.delay,
      OracleAdv.Timed.StepTimeBound, OracleAdv.Timed.TimeBound, OracleAdv.Timed.AllRet] <;>
    repeat' (first | trivial | apply And.intro | intro _ | split |
      dsimp only [OracleAdv.Timed.StepTimeBound, OracleAdv.Timed.TimeBound,
        OracleAdv.Timed.AllRet] | grind)

variable [Fintype RK] [Nonempty RK]

/-- The oracle tree of the CKA reduction `smcCKARed` at the challenge epoch `t` and the public
value `pub`, for the interaction `play` of the secure-messaging adversary. -/
noncomputable def smcCKARed.tree (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa))
    (D : AEADDef W Ct) (ideal : Bool)
    (play : ℕ → Msg → OracleAdv (SMQuery W) (SMAns Sc Msg RK Sa Ct) Bool) (t : ℕ) (pub : Msg) :
    OracleAdv CKAQuery (CKAAns Sc Msg Key Rand) Bool :=
  smCKATreeOf R G D ideal play t pub

derive_timed smcCKARed.tree

/-- The derived costed tree of `smcCKARed`, at a costed interaction `play` that erases to the
interaction of `A`, erases to the interaction of the CKA reduction. -/
theorem smcCKARed.compile_tree [Fintype Rand] [Nonempty Rand] (R : PRGDef (RK × Key) (RK × Sa))
    (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (ideal : Bool) (A : SMCorruptAdv Sc Msg RK Sa W Ct)
    (play : ℕ → Msg → OracleAdv.Timed (SMQuery W) (SMAns Sc Msg RK Sa Ct) Bool)
    (playCost : ℕ → Msg → ℕ) (hplay : ∀ t g, (play t g).erase = A.play t g) (t : ℕ) (pub : Msg)
    (rCost : RK × Key → ℕ) (eCost : W → W → W → ℕ) (gCost : Sa → ℕ) :
    (smcCKARed.tree.timed R G D ideal play playCost t pub rCost eCost gCost).2.erase =
      (smcCKARed (Rand := Rand) (Key := Key) R G D ideal A).play t pub := by
  rw [smcCKARed.tree.erase_timed]
  have h : (fun t g => (play t g).erase) = A.play := funext fun t => funext (hplay t)
  rw [h]
  rfl

/-- The time of a tree that draws `x` from `μ` at the step cost `c x` and then runs a
step-prefixed tree `S x` of time at most `B`, returning the first component of its output. -/
theorem timeBound_rand_cost_bind_fst {D R X Ŝ : Type} (μ : PMF X) (c : X → ℕ)
    (S : X → ℕ × OracleAdv.Timed D R (Bool × Ŝ)) {K B : ℕ} (hc : ∀ x, c x ≤ K)
    (hS : ∀ x, OracleAdv.Timed.StepTimeBound (S x) B) :
    OracleAdv.Timed.StepTimeBound (0, OracleAdv.Timed.rand μ
      (fun x => c x + (S x).1 + ((S x).2.bind fun r => (0, OracleAdv.Timed.ret r.1)).1)
      fun x => ((S x).2.bind fun r => (0, OracleAdv.Timed.ret r.1)).2) (K + B + 1) := by
  refine ⟨Nat.zero_le _, by dsimp only; omega, fun x => ?_⟩
  obtain ⟨h1, h2⟩ := hS x
  obtain ⟨h3, h4⟩ := OracleAdv.Timed.timeBound_bind (n := 0) h2
    (f := fun r => (0, OracleAdv.Timed.ret r.1)) fun _ => ⟨le_refl _, trivial⟩
  have := hc x
  refine ⟨by dsimp only; omega, h4.mono ?_⟩
  dsimp only; omega

/-- **Time of the CKA reduction.** For a costed interaction of time at most `T`, at most `q`
queries and call cost at most `a`, root steps of cost at most `r`, chain steps of cost at most
`g` and encryptions of cost at most `e`, the derived costed tree of `smcCKARed` has time at most
`T + ∑_{j < q} (r + 2 g + e + 6 (1 + 3 j) + 50) + a + 5`: one simulated query per query,
whose cost grows with the cost companions of the simulator state. -/
theorem smcCKARed.timeBound_timed (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa))
    (D : AEADDef W Ct) (ideal : Bool)
    (play : ℕ → Msg → OracleAdv.Timed (SMQuery W) (SMAns Sc Msg RK Sa Ct) Bool)
    (playCost : ℕ → Msg → ℕ) (t : ℕ) (pub : Msg) (rCost : RK × Key → ℕ)
    (eCost : W → W → W → ℕ) (gCost : Sa → ℕ) {T q a r g e : ℕ}
    (hA : ∀ t g, (play t g).TimeBound T) (hq : ∀ t g, (play t g).erase.IsQueryBound q)
    (ha : ∀ t g, playCost t g ≤ a) (hr : ∀ x, rCost x ≤ r) (he : ∀ k m a, eCost k m a ≤ e)
    (hg : ∀ s, gCost s ≤ g) :
    OracleAdv.Timed.StepTimeBound
      (smcCKARed.tree.timed (Key := Key) (Rand := Rand) R G D ideal play playCost t pub rCost
        eCost gCost)
      (T + ∑ j ∈ Finset.range q, smCKAQueryTime r g e (1 + 3 * j) + a + 5) := by
  unfold smcCKARed.tree.timed smCKATreeOf.timed
  refine (OracleAdv.Timed.stepTimeBound_delay (timeBound_rand_cost_bind_fst (K := 3 + a)
    (B := T + ∑ j ∈ Finset.range q, smCKAQueryTime r g e (1 + 3 * j)) _ _ _
    (fun _ => by have := ha t pub; omega) fun rk => ?_)).mono (by omega)
  refine (OracleAdv.Timed.timeBound_simulateHat_inv _ _ _
    (fun i ŝ => smCKACostInv (1 + 3 * i) ŝ.1 ŝ.2) (fun i => smCKAQueryTime r g e (1 + 3 * i))
    (fun i ŝ d h => smCKAImplOf.timed_bound R G D t ideal _ d rCost eCost gCost hr he hg i _ _ h)
    (hA t pub) (hq t pub) 0 _ ?_).mono ?_
  · refine ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => ?_⟩ <;>
      dsimp only <;> omega
  · simp only [Nat.zero_add, le_refl]

end CKATime

end CatCrypt.Crypto.Messaging
