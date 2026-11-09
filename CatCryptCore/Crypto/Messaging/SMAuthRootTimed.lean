/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.SMAuthRoot
public import CatCryptCore.Crypto.Messaging.SMAuthTimed
import CatCryptCore.Tactics.DeriveTimed

/-!
# Running time of the PRF-PRNG reduction of the forgery event

The time certificate of the reduction `smAuthRootRed` of
`CatCryptCore.Crypto.Messaging.SMAuthRoot`. The reduction is the oracle tree
`smAuthRootRed.tree` with the challenge-epoch distribution and the interaction of the adversary
as parameters; its costed form is derived by `derive_timed`, and `smAuthRootRed.compile_tree`
states that the erased costed tree is the reduction at a costed interaction erasing to the
adversary's.

The simulator `smAuthRootImpl` keeps the full state of the secure-messaging game, the log of the
honest ciphertexts and the list of the answered corruptions. The potential is
`smAuthRootCostInv i`: the cost companions of the secure-messaging state are at most `1 + 3 i`
(`smCostInv`), and the log and the list of corruptions have at most `i` entries. A delivery at
the position `j` walks the receiving chain `j` steps twice, so its step handles data of the size
of the event: the `i`-th query costs at most
`2 (g + 4) j + smAuthRootQueryTime s v r g e dd i` (`smAuthRootImpl.timed_bound`). For an
adversary of time `T` with at most `q` queries whose delivery positions sum to at most `J`, the
reduction has time at most
`T + 2 (g + 4) J + ∑_{j < q} smAuthRootQueryTime s v r g e dd j + a + 9`
(`smAuthRootRed.timeBound_timed`), a polynomial of degree two in `q`.

No module imports this file.

## Main results

* `smAuthRootRed.tree`, `smAuthRootRed.compile_tree` — the reduction as an oracle tree and the
  erasure of its costed form
* `smRootImplAt.timed_bound` — the time of a query of the simulator of the root step at the
  epoch `k`
* `smAuthRootImpl.timed_bound` — the time of a simulated query under the potential, with the
  walk of the receiving chain charged to the delivery position `smAuthDeliverIdx`
* `smAuthRootRed.timeBound_timed` — the time of the reduction
-/

set_option autoImplicit false

@[expose] public section

namespace CatCrypt.Crypto.Messaging

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Assumptions

section RootTime

variable {Sc Msg Key Rand RK Sa W Ct : Type} [Fintype Rand] [Nonempty Rand] [SampleableType W]
  [SampleableType Ct] [DecidableEq W] [DecidableEq Ct] [Fintype RK] [Nonempty RK]

/-- The oracle tree of the PRF-PRNG reduction `smAuthRootRed` at the epoch `k`, for the
distribution `tStar` of the challenge epoch and the interaction `play` of the authenticity
adversary. -/
noncomputable def smAuthRootRed.tree (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS k : ℕ) (initP : PMF (Msg × Sc × Sc)) (tStar : PMF ℕ)
    (play : ℕ → Msg → OracleAdv (SMAuthQuery W Ct) (SMAuthAns Msg Ct (SMPartySt Sc RK Sa) W) Bool) :
    OracleAdv (PPQuery RK Key) (RK × Sa) Bool :=
  smAuthRootTree C R G D ΔFS ΔPCS k initP tStar play

derive_timed smAuthRootRed.tree

/-- The derived costed tree of `smAuthRootRed`, at the challenge-epoch distribution of `A` and a
costed interaction `play` that erases to the interaction of `A`, erases to the PRF-PRNG
reduction. -/
theorem smAuthRootRed.compile_tree (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS k : ℕ) (initP : PMF (Msg × Sc × Sc)) (A : SMAuthAdv Msg W Ct (SMPartySt Sc RK Sa))
    (play : ℕ → Msg → OracleAdv.Timed (SMAuthQuery W Ct) (SMAuthAns Msg Ct (SMPartySt Sc RK Sa) W)
      Bool)
    (playCost : ℕ → Msg → ℕ) (hplay : ∀ t g, (play t g).erase = A.play t g)
    (sCost : Sc → Rand → ℕ) (rCost : RK × Key → ℕ) (vCost : Sc → Msg → ℕ)
    (eCost : W → W → W → ℕ) (gCost : Sa → ℕ) (dCost : W → Ct → W → ℕ) :
    (smAuthRootRed.tree.timed C R G D ΔFS ΔPCS k initP A.tStar play playCost sCost rCost vCost
      eCost gCost dCost).2.erase = smAuthRootRed C R G D ΔFS ΔPCS k initP A := by
  rw [smAuthRootRed.tree.erase_timed]
  have h : (fun t g => (play t g).erase) = A.play := funext fun t => funext (hplay t)
  rw [h]
  rfl

/-- `List.all` with a test of cost at most `k` costs at most `k + 5` per element and one
more. -/
private theorem all_timedCost_le' {α : Type} (l : List α) (p : α → Bool) (pCost : α → ℕ)
    {k : ℕ} (hp : ∀ a, pCost a ≤ k) : List.all.timedCost l p pCost ≤ (k + 5) * l.length + 1 := by
  induction l with
  | nil => simp [List.all.timedCost.eq_1]
  | cons a l ih =>
    rw [List.all.timedCost.eq_2, List.length_cons, Nat.mul_succ]
    have := hp a
    omega

/-- `j` iterations of a function of cost at most `c` cost at most `(c + 3) j + 1`. -/
private theorem iterate_timedCost_le' {α : Type} (f : α → α) (fCost : α → ℕ) {c : ℕ}
    (hf : ∀ a, fCost a ≤ c) (j : ℕ) :
    ∀ s, Nat.iterate.timedCost f fCost j s ≤ (c + 3) * j + 1 := by
  induction j with
  | zero => intro s; simp [Nat.iterate.timedCost]
  | succ j ih =>
    intro s
    have := ih (f s); have := hf s
    simp only [Nat.iterate.timedCost]
    rw [Nat.mul_succ]; omega

omit [DecidableEq W] [DecidableEq Ct] [Fintype RK] [Nonempty RK] in
/-- **Time of a query of `smRootImplAt`.** From a costed state with companions at most
`1 + 3 i`, the costed simulator answers in time at most `smQueryTime s v r g e (1 + 3 i)` and
returns states with companions at most `1 + 3 (i + 1)`. -/
theorem smRootImplAt.timed_bound (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t k : ℕ) (σ : SMSt Sc Msg RK Sa) (q : SMQuery W)
    (sCost : Sc → Rand → ℕ) (rCost : RK × Key → ℕ) (vCost : Sc → Msg → ℕ)
    (eCost : W → W → W → ℕ) (gCost : Sa → ℕ) {s v r g e : ℕ} (hs : ∀ x c, sCost x c ≤ s)
    (hv : ∀ x m, vCost x m ≤ v) (hr : ∀ x, rCost x ≤ r) (he : ∀ k m a, eCost k m a ≤ e)
    (hg : ∀ x, gCost x ≤ g) (i : ℕ) (loc ck) (hinv : smCostInv (1 + 3 * i) ck loc) :
    OracleAdv.Timed.StepTimeBound
        (smRootImplAt.timed C R G D ΔFS ΔPCS t k σ q sCost rCost loc ck vCost eCost gCost)
        (smQueryTime s v r g e (1 + 3 * i)) ∧
      OracleAdv.Timed.AllRet (fun y => smCostInv (1 + 3 * (i + 1)) y.2.1 y.2.2)
        (smRootImplAt.timed C R G D ΔFS ΔPCS t k σ q sCost rCost loc ck vCost eCost gCost).2 := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := hinv
  unfold smCostInv smQueryTime
  cases q <;>
    simp only [smRootImplAt.timed, smRootRatchet.timed, smRootRecv.timed, smFullSend.timed,
      smFullChall.timed, smFullCorr.timed, OracleAdv.Timed.delay,
      OracleAdv.Timed.StepTimeBound] <;>
    repeat' (first | trivial | apply And.intro | intro _ | split |
      dsimp only [OracleAdv.Timed.StepTimeBound, OracleAdv.Timed.TimeBound,
        OracleAdv.Timed.AllRet] | grind)

/-- The bound on a costed state of the simulator `smAuthRootImpl` after at most `i` queries: the
cost companions of the secure-messaging state are at most `1 + 3 i` (`smCostInv`), and the log
and the list of corruptions have at most `i` entries. -/
def smAuthRootCostInv (i : ℕ)
    (ŝ : (((((CKAParty → Sc) × (CKAParty → ℕ)) × ((CKAParty → ℕ) × (CKAParty → ℕ)) × Msg) ×
      ((CKAParty → RK) × (CKAParty → ℕ)) × ((CKAParty → Option Sa) × (CKAParty → ℕ)) ×
      ((CKAParty → Option Sa) × (CKAParty → ℕ)) × Option (RK × Sa) × Bool) × SMAuthAux W Ct) ×
      Bool) : Prop :=
  smCostInv (1 + 3 * i) ŝ.1.1.1 ŝ.1.1.2 ∧ ŝ.1.2.log.length ≤ i ∧ ŝ.1.2.corrs.length ≤ i

/-- The time of the `i`-th simulated query of `smAuthRootRed` apart from the walk of the
receiving chain: a query of the secure-messaging simulator, the search of the log and the tests
of the corruptions, with decryptions of cost at most `d`. -/
def smAuthRootQueryTime (s v r g e d i : ℕ) : ℕ :=
  smQueryTime s v r g e (1 + 3 * i) + 150 * i + 2 * g + 2 * d + 300

omit [Fintype RK] [Nonempty RK] in
/-- **Time of a query of the simulator of `smAuthRootRed`.** From a costed state with
companions at most `1 + 3 i`, a log and a list of corruptions of at most `i` entries, the costed
simulator `smAuthRootImpl` answers the query `d` in time at most
`2 (g + 4) · smAuthDeliverIdx d + smAuthRootQueryTime s v r g e dd i` and returns states
satisfying `smAuthRootCostInv (i + 1)`. -/
theorem smAuthRootImpl.timed_bound (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t k : ℕ) (σ : (SMSt Sc Msg RK Sa × SMAuthAux W Ct) × Bool) (d : SMAuthQuery W Ct)
    (sCost : Sc → Rand → ℕ) (rCost : RK × Key → ℕ) (vCost : Sc → Msg → ℕ)
    (eCost : W → W → W → ℕ) (gCost : Sa → ℕ) (dCost : W → Ct → W → ℕ) {s v r g e dd : ℕ}
    (hs : ∀ x c, sCost x c ≤ s) (hv : ∀ x m, vCost x m ≤ v) (hr : ∀ x, rCost x ≤ r)
    (he : ∀ k m a, eCost k m a ≤ e) (hg : ∀ x, gCost x ≤ g) (hd : ∀ k c a, dCost k c a ≤ dd)
    (i : ℕ) (loc ck) (x : SMAuthAux W Ct) (hinv : smCostInv (1 + 3 * i) ck loc)
    (hl : σ.1.2.log.length ≤ i) (hc : σ.1.2.corrs.length ≤ i) :
    OracleAdv.Timed.StepTimeBound (OracleAdv.Timed.delay 1
        (smAuthRootImpl.timed C R G D ΔFS ΔPCS t k σ d sCost rCost loc ck vCost eCost gCost dCost
          ((ck, loc), x)))
        (2 * (g + 4) * smAuthDeliverIdx d + smAuthRootQueryTime s v r g e dd i) ∧
      OracleAdv.Timed.AllRet (fun y => smAuthRootCostInv (i + 1) y.2)
        (smAuthRootImpl.timed C R G D ΔFS ΔPCS t k σ d sCost rCost loc ck vCost eCost gCost dCost
          ((ck, loc), x)).2 := by
  have hall := all_timedCost_le' σ.1.2.corrs (fun c => ckaAllowCorr ΔFS ΔPCS k c.2 c.1)
    (fun _ => 11) (k := 11) (fun _ => le_rfl)
  have hin := fun q => smRootImplAt.timed_bound C R G D ΔFS ΔPCS t k σ.1.1 q sCost rCost vCost
    eCost gCost hs hv hr he hg i loc ck hinv
  obtain ⟨h1, h2, h3, h4, h5⟩ := hinv
  unfold smAuthRootImpl.timed
  split
  · cases d with
    | sm q =>
      simp only [smAuthRootStep.timed]
      have hcp := fun pr : SMLogEntry W Ct → Bool => List.countP.timedCost_le pr
        (fun _ => 1) (k := 1) (fun _ => le_rfl) σ.1.2.log
      have hu := fun a => SMAuthAux.upd_length (Pub := Msg) (Leak := SMPartySt Sc RK Sa) σ.1.2
        (ckaShadow σ.1.1.ck) q a
      have hallu := fun a : SMSchemeAns Msg Ct (SMPartySt Sc RK Sa) =>
        all_timedCost_le' (σ.1.2.upd (ckaShadow σ.1.1.ck) q a).corrs
        (fun c => ckaAllowCorr ΔFS ΔPCS k c.2 c.1) (fun _ => 11) (k := 11) (fun _ => le_rfl)
      refine ⟨(OracleAdv.Timed.stepTimeBound_delay (OracleAdv.Timed.stepTimeBound_delay
        (OracleAdv.Timed.stepTimeBound_delay (OracleAdv.Timed.stepTimeBound_delay
          (OracleAdv.Timed.stepTimeBound_delay_add_bind (c := 1) (n := 40 * i + 60) (hin q).1
            fun y => ?_))))).mono ?_, OracleAdv.Timed.allRet_bind (hin q).2 fun y hy => ?_⟩
      · have := hallu y.1.toScheme
        have := hu y.1.toScheme
        simp only [OracleAdv.Timed.delay, OracleAdv.Timed.StepTimeBound]
        repeat' (first | trivial | apply And.intro | split | grind)
      · simp only [smAuthDeliverIdx, smAuthRootQueryTime]
        omega
      · have := hu y.1.toScheme
        simp only [OracleAdv.Timed.delay]
        split <;> exact ⟨hy, by dsimp only; omega, by dsimp only; omega⟩
    | deliver p j ad c =>
      simp only [smAuthRootStep.timed]
      have hall' := all_timedCost_le' σ.1.2.corrs
        (fun c => ckaAllowCorr ΔFS ΔPCS ((ckaShadow σ.1.1.ck).t p) c.2 c.1) (fun _ => 11)
        (k := 11) (fun _ => le_rfl)
      have hfind := List.find?.timedCost_le
        (fun l : SMLogEntry W Ct => decide (l.e = (ckaShadow σ.1.1.ck).t p ∧ l.j = j ∧
          l.ad = ad ∧ l.ct = c)) (fun _ => 1) (k := 1) (fun _ => le_rfl) σ.1.2.log
      have hit := iterate_timedCost_le' (fun s => (G.stretch s).2) (fun s => 1 + gCost s)
        (c := g + 1) (fun s => by have := hg s; omega) j
      have hp2 := h2 p
      have hp5 := h5 p
      simp only [OracleAdv.Timed.delay, OracleAdv.Timed.StepTimeBound,
        OracleAdv.Timed.TimeBound, OracleAdv.Timed.AllRet, smAuthDeliverIdx,
        smAuthRootQueryTime, smQueryTime]
      refine ⟨⟨?_, trivial⟩, ?_⟩
      · have hM : 2 * (g + 4) * j = 2 * ((g + 4) * j) := Nat.mul_assoc _ _ _
        rw [hM]
        rcases hrcv : σ.1.1.loc.rcv p with _ | a
        · simp only
          repeat' split
          all_goals omega
        · have := hit a
          have := hg ((fun s => (G.stretch s).2)^[j] a)
          have := hd (chainKey G a j) c ad
          simp only
          rw [show g + 1 + 3 = g + 4 by omega] at *
          generalize (g + 4) * j = M at *
          repeat' split
          all_goals omega
      · exact ⟨⟨fun q => by grind, fun q => by grind, fun q => by grind, fun q => by grind,
          fun q => by grind⟩, by grind, by grind⟩
  · simp only [OracleAdv.Timed.delay, OracleAdv.Timed.StepTimeBound,
      OracleAdv.Timed.TimeBound, OracleAdv.Timed.AllRet, smAuthRootCostInv, smCostInv]
    grind [smAuthRootQueryTime]

omit [SampleableType W] [SampleableType Ct] [DecidableEq W] [DecidableEq Ct] [Fintype RK]
  [Nonempty RK] in
/-- The time of a tree that draws `x` from `μ` at the step cost `c x` and then runs a
step-prefixed tree `S x` of time at most `B`, returning a function `f` of its output. -/
private theorem timeBound_rand_cost_bind_ret' {D R X β γ : Type} (μ : PMF X) (c : X → ℕ)
    (S : X → ℕ × OracleAdv.Timed D R β) (f : β → γ) {K B : ℕ} (hc : ∀ x, c x ≤ K)
    (hS : ∀ x, OracleAdv.Timed.StepTimeBound (S x) B) :
    OracleAdv.Timed.StepTimeBound (0, OracleAdv.Timed.rand μ
      (fun x => c x + (S x).1 + ((S x).2.bind fun r => (0, OracleAdv.Timed.ret (f r))).1)
      fun x => ((S x).2.bind fun r => (0, OracleAdv.Timed.ret (f r))).2) (K + B + 1) := by
  refine ⟨Nat.zero_le _, by dsimp only; omega, fun x => ?_⟩
  obtain ⟨h1, h2⟩ := hS x
  obtain ⟨h3, h4⟩ := OracleAdv.Timed.timeBound_bind (n := 0) h2
    (f := fun r => (0, OracleAdv.Timed.ret (f r))) fun _ => ⟨le_refl _, trivial⟩
  have := hc x
  refine ⟨by dsimp only; omega, h4.mono ?_⟩
  dsimp only; omega

/-- **Time of `smAuthRootRed`.** For a costed interaction of time at most `T`, at most `q`
queries, deliveries whose positions in the receiving chain sum to at most `J` on every path, and
call cost at most `a`, CKA sends of cost at most `s`, CKA receives of cost at most `v`, root
steps of cost at most `r`, chain steps of cost at most `g`, encryptions of cost at most `e` and
decryptions of cost at most `dd`, the derived costed tree of `smAuthRootRed` has time at most
`T + 2 (g + 4) J + ∑_{j < q} smAuthRootQueryTime s v r g e dd j + a + 9`. -/
theorem smAuthRootRed.timeBound_timed (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS k : ℕ) (initP : PMF (Msg × Sc × Sc)) (tStar : PMF ℕ)
    (play : ℕ → Msg → OracleAdv.Timed (SMAuthQuery W Ct) (SMAuthAns Msg Ct (SMPartySt Sc RK Sa) W)
      Bool)
    (playCost : ℕ → Msg → ℕ) (sCost : Sc → Rand → ℕ) (rCost : RK × Key → ℕ)
    (vCost : Sc → Msg → ℕ) (eCost : W → W → W → ℕ) (gCost : Sa → ℕ) (dCost : W → Ct → W → ℕ)
    {T q J a s v r g e dd : ℕ}
    (hA : ∀ t g, (play t g).TimeBound T) (hq : ∀ t g, (play t g).erase.IsQueryBound q)
    (hJ : ∀ t g, (play t g).erase.IsQueryBoundBy smAuthDeliverIdx J)
    (ha : ∀ t g, playCost t g ≤ a) (hs : ∀ x c, sCost x c ≤ s) (hv : ∀ x m, vCost x m ≤ v)
    (hr : ∀ x, rCost x ≤ r) (he : ∀ k m a, eCost k m a ≤ e) (hg : ∀ x, gCost x ≤ g)
    (hd : ∀ k c a, dCost k c a ≤ dd) :
    OracleAdv.Timed.StepTimeBound
      (smAuthRootRed.tree.timed C R G D ΔFS ΔPCS k initP tStar play playCost sCost rCost vCost
        eCost gCost dCost)
      (T + 2 * (g + 4) * J + ∑ j ∈ Finset.range q, smAuthRootQueryTime s v r g e dd j + a + 9) := by
  unfold smAuthRootRed.tree.timed smAuthRootTree.timed
  refine (OracleAdv.Timed.stepTimeBound_delay (timeBound_rand_zero _ _ fun t =>
    timeBound_rand_zero _ _ fun i => timeBound_rand_cost_bind_ret' (K := 5 + a)
      (B := T + 2 * (g + 4) * J + ∑ j ∈ Finset.range q, smAuthRootQueryTime s v r g e dd j)
      _ _ _ _ (fun _ => by have := ha t i.1; omega) fun rk => ?_)).mono (by omega)
  unfold OracleAdv.Timed.simulateHat
  refine (OracleAdv.Timed.timeBound_simulate_inv_of_isQueryBoundBy _
    (fun d => 2 * (g + 4) * smAuthDeliverIdx d) (smAuthRootQueryTime s v r g e dd)
    (fun i ŝ => smAuthRootCostInv i ŝ)
    (fun i ŝ d h => smAuthRootImpl.timed_bound C R G D ΔFS ΔPCS t k _ d sCost rCost vCost eCost
      gCost dCost hs hv hr he hg hd i ŝ.1.1.2 ŝ.1.1.1 ŝ.1.2 h.1 h.2.1 h.2.2)
    (hA t i.1) ((hJ t i.1).mul_left _) (hq t i.1) 0 _ ?_).mono ?_
  · simp [smAuthRootCostInv, smCostInv, SMAuthAux.init]
  · simp only [Nat.zero_add, le_refl]

end RootTime

end CatCrypt.Crypto.Messaging
