/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.HybridArgument
import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveReduction.Basic
import CatCryptCore.Tactics.AutoTime
public import CatCryptCore.Tactics.AutoTime.Basic
public import CatCryptCore.Tactics.StdCosts

/-!
# Running time of the sampler-hybrid reductions

The reductions `pairFstRed` and `pairSndRed` of `HybridArgument` map a two-stage
distinguisher `FamilyDistinguisher` against a pair of samplers to a two-stage distinguisher
against one of them. Their costed forms come from `derive_reduction`, field by field over the
costed mirror `FamilyDistinguisher.Timed` of `derive_timed_structure`; the theorems below bound
the time of each stage.

## Cost model

The cost rules of `CatCryptCore.Tactics.DeriveTimed`: one unit per call. The sampler `d` (or
`c`) is a costed computation with its cost companion; the stages `pre` and `guess` of the
distinguisher `B` are costed computations that compile to `B.pre` and `B.guess`, and `guess`
has a cost companion.

## Main results

* `pairFstRed.timeBound_timed` — first stage of time `pre.time`, second stage of time at most
  `ad + Td + a + T + 2`
* `pairSndRed.timeBound_timed` — first stage of time at most `pre.time + ac + Tc + 1`, second
  stage of time at most `a + T + 1`
* `epochFold.tree.timeBound_timed`, `idealPrefix.tree.timeBound_timed` — `n` epochs with
  samplers and state maps of time at most `T` and companions at most `c` run in time at most
  `n (4 T + 4 c + co + 4 n + 9) + 1`
* `secHybRed.timeBound_timed`, `stretchHybRed.timeBound_timed` — the hop reductions of the
  epoch hybrid: a first stage of time linear in the heap size of `h₀` plus the idealized prefix
  of `i` epochs, a second stage of the remaining epochs plus the time and call cost of `D`
* `epochFold.tree.allRet_length`, `idealPrefix.tree.allRet_length` — the fold over `bs` returns at
  most `bs.length` entries, the idealized prefix of `j` epochs at most `j`
* `secHybRed.timeBound_timed_len`, `stretchHybRed.timeBound_timed_len` — on the views of at most
  `i` entries that the first stage returns, with append of cost `aa * u.length + ba` and `D`
  bounded on the lengths it receives: a second stage with append cost `aa * i + ba`

The hop reductions take the costed samplers `getRoot`, `post`, `sec`, `s`, `secI`, `sI` with
cost companions, the map `out` and the list append `hAppend` as primitives with cost
companions, and the distinguisher `D` with its cost companion.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.HybridArgument

open CatCrypt.Core

derive_timed_structure FamilyDistinguisher

derive_reduction pairFstRed

derive_reduction pairSndRed

derive_reduction secHybRed

derive_reduction stretchHybRed

/-- **Time of the epoch fold.** With samplers and state maps of time at most `T`, the cost
companions of the costed calls at most `c` and the cost of `out` at most `co`, the fold over
`n` epochs runs in time at most `n (4 T + 4 c + co + 4 n + 9) + 1`. The companions of the
recursive call are one more than those of the caller, whence the term `4 n`. -/
theorem epochFold.tree.timeBound_timed {W ρ Z : Type} (getRoot : ρ → SPTree.Timed W)
    (post : W → SPTree.Timed ρ) (out : W → W) (outCost : W → ℕ) (sec : Unit → SPTree.Timed Z)
    (s : W × Z → SPTree.Timed W) {T co : ℕ} (hg : ∀ x, (getRoot x).time ≤ T)
    (hp : ∀ w, (post w).time ≤ T) (hsec : ∀ u, (sec u).time ≤ T) (hs : ∀ p, (s p).time ≤ T)
    (hoc : ∀ w, outCost w ≤ co) (bs : List Bool) :
    ∀ (getRootCost : ρ → ℕ) (postCost : W → ℕ) (secCost : Unit → ℕ) (sCost : W × Z → ℕ)
      (c : ℕ), (∀ x, getRootCost x ≤ c) → (∀ w, postCost w ≤ c) → (∀ u, secCost u ≤ c) →
      (∀ p, sCost p ≤ c) → ∀ x,
      SPTree.Timed.stepTime (epochFold.tree.timed getRoot getRootCost post postCost out outCost
        sec secCost s sCost bs x) ≤ bs.length * (4 * T + 4 * c + co + 4 * bs.length + 9) + 1 := by
  induction bs with
  | nil =>
    intro _ _ _ _ _ _ _ _ _ x
    simp [epochFold.tree.timed, SPTree.Timed.stepTime, SPTree.Timed.delay,
      SPTree.Timed.time_ret]
  | cons b bs ih =>
    intro getRootCost postCost secCost sCost c hgc hpc hsecc hsc x
    have ih' := ih (fun a => 1 + getRootCost a) (fun a => 1 + postCost a)
      (fun a => 1 + secCost a) (fun a => 1 + sCost a) (c + 1) (fun a => by grind)
      (fun a => by grind) (fun a => by grind) (fun a => by grind)
    have hlen : bs.length * (4 * T + 4 * (c + 1) + co + 4 * bs.length + 9) + 1 +
        (4 * T + 4 * c + co + 9) ≤
        (b :: bs).length * (4 * T + 4 * c + co + 4 * (b :: bs).length + 9) + 1 := by
      simp only [List.length_cons]; nlinarith
    refine le_trans ?_ hlen
    generalize bs.length * (4 * T + 4 * (c + 1) + co + 4 * bs.length + 9) = K at ih' ⊢
    rw [epochFold.tree.timed.eq_2]
    time_bound

/-- **Time of the idealized prefix.** With samplers and state maps of time at most `T`, the
cost companions of the costed calls at most `c` and the cost of `out` at most `co`, the first
`j` idealized epochs run in time at most `j (4 T + 4 c + co + 4 j + 9) + 1`. -/
theorem idealPrefix.tree.timeBound_timed {W ρ Z : Type} (getRoot : ρ → SPTree.Timed W)
    (post : W → SPTree.Timed ρ) (out : W → W) (outCost : W → ℕ) (secI : Unit → SPTree.Timed Z)
    (sI : W × Z → SPTree.Timed W) {T co : ℕ} (hg : ∀ x, (getRoot x).time ≤ T)
    (hp : ∀ w, (post w).time ≤ T) (hsec : ∀ u, (secI u).time ≤ T) (hs : ∀ p, (sI p).time ≤ T)
    (hoc : ∀ w, outCost w ≤ co) (j : ℕ) :
    ∀ (getRootCost : ρ → ℕ) (postCost : W → ℕ) (secICost : Unit → ℕ) (sICost : W × Z → ℕ)
      (c : ℕ), (∀ x, getRootCost x ≤ c) → (∀ w, postCost w ≤ c) → (∀ u, secICost u ≤ c) →
      (∀ p, sICost p ≤ c) → ∀ bs x,
      SPTree.Timed.stepTime (idealPrefix.tree.timed getRoot getRootCost post postCost out outCost
        secI secICost sI sICost j bs x) ≤ j * (4 * T + 4 * c + co + 4 * j + 9) + 1 := by
  induction j with
  | zero =>
    intro _ _ _ _ _ _ _ _ _ bs x
    simp [idealPrefix.tree.timed, SPTree.Timed.stepTime, SPTree.Timed.delay,
      SPTree.Timed.time_ret]
  | succ j ih =>
    intro getRootCost postCost secICost sICost c hgc hpc hsecc hsc bs x
    have ih' := ih (fun a => 1 + getRootCost a) (fun a => 1 + postCost a)
      (fun a => 1 + secICost a) (fun a => 1 + sICost a) (c + 1) (fun a => by grind)
      (fun a => by grind) (fun a => by grind) (fun a => by grind)
    have hlen : j * (4 * T + 4 * (c + 1) + co + 4 * j + 9) + 1 + (4 * T + 4 * c + co + 9) ≤
        (j + 1) * (4 * T + 4 * c + co + 4 * (j + 1) + 9) + 1 := by
      nlinarith
    refine le_trans ?_ hlen
    generalize j * (4 * T + 4 * (c + 1) + co + 4 * j + 9) = K at ih' ⊢
    cases bs with
    | nil =>
      rw [idealPrefix.tree.timed.eq_2]
      simp [SPTree.Timed.stepTime, SPTree.Timed.delay, SPTree.Timed.time_ret]
      omega
    | cons b bs =>
      rw [idealPrefix.tree.timed.eq_3]
      time_bound

/-- The costed epoch fold over `bs` returns views of at most `bs.length` entries. -/
theorem epochFold.tree.allRet_length {W ρ Z : Type} (getRoot : ρ → SPTree.Timed W)
    (getRootCost : ρ → ℕ) (post : W → SPTree.Timed ρ) (postCost : W → ℕ) (out : W → W)
    (outCost : W → ℕ) (sec : Unit → SPTree.Timed Z) (secCost : Unit → ℕ)
    (s : W × Z → SPTree.Timed W) (sCost : W × Z → ℕ) (bs : List Bool) (x : ρ) :
    SPTree.Timed.AllRet (fun l : List W => l.length ≤ bs.length)
      (epochFold.tree.timed getRoot getRootCost post postCost out outCost sec secCost s sCost
        bs x).2 := by
  induction bs generalizing getRootCost postCost secCost sCost x with
  | nil =>
    simp only [epochFold.tree.timed, SPTree.Timed.delay]
    exact Nat.le_refl 0
  | cons b bs ih =>
    rw [epochFold.tree.timed.eq_2]
    simp only [SPTree.Timed.delay]
    refine SPTree.Timed.allRet_bind_of (SPTree.Timed.allRet_of_forall (fun _ => ?_) _)
    refine SPTree.Timed.allRet_bind_of (SPTree.Timed.allRet_of_forall (fun _ => ?_) _)
    refine SPTree.Timed.allRet_bind_of (SPTree.Timed.allRet_of_forall (fun _ => ?_) _)
    refine SPTree.Timed.allRet_bind_of (SPTree.Timed.allRet_of_forall (fun _ => ?_) _)
    exact SPTree.Timed.allRet_bind_of (SPTree.Timed.allRet_mono
      (fun l (h : l.length ≤ bs.length) => by
        simp only [SPTree.Timed.AllRet, List.length_cons]; omega) _ (ih _ _ _ _ _))

/-- The costed idealized prefix of `j` epochs returns views of at most `j` entries. -/
theorem idealPrefix.tree.allRet_length {W ρ Z : Type} (getRoot : ρ → SPTree.Timed W)
    (getRootCost : ρ → ℕ) (post : W → SPTree.Timed ρ) (postCost : W → ℕ) (out : W → W)
    (outCost : W → ℕ) (secI : Unit → SPTree.Timed Z) (secICost : Unit → ℕ)
    (sI : W × Z → SPTree.Timed W) (sICost : W × Z → ℕ) (j : ℕ) (bs : List Bool) (x : ρ) :
    SPTree.Timed.AllRet (fun p : List W × ρ => p.1.length ≤ j)
      (idealPrefix.tree.timed getRoot getRootCost post postCost out outCost secI secICost sI
        sICost j bs x).2 := by
  induction j generalizing getRootCost postCost secICost sICost bs x with
  | zero =>
    simp only [idealPrefix.tree.timed, SPTree.Timed.delay]
    exact Nat.le_refl 0
  | succ j ih =>
    cases bs with
    | nil =>
      rw [idealPrefix.tree.timed.eq_2]
      simp only [SPTree.Timed.delay]
      exact Nat.zero_le _
    | cons b bs =>
      rw [idealPrefix.tree.timed.eq_3]
      simp only [SPTree.Timed.delay]
      refine SPTree.Timed.allRet_bind_of (SPTree.Timed.allRet_of_forall (fun _ => ?_) _)
      refine SPTree.Timed.allRet_bind_of (SPTree.Timed.allRet_of_forall (fun _ => ?_) _)
      refine SPTree.Timed.allRet_bind_of (SPTree.Timed.allRet_of_forall (fun _ => ?_) _)
      refine SPTree.Timed.allRet_bind_of (SPTree.Timed.allRet_of_forall (fun _ => ?_) _)
      exact SPTree.Timed.allRet_bind_of (SPTree.Timed.allRet_mono
        (fun p (h : p.1.length ≤ j) => by
          simp only [SPTree.Timed.AllRet, List.length_cons]; omega) _ (ih _ _ _ _ _ _))

/-- **Time of `pairFstRed`**: its first stage is the first stage of `B`; its second stage
draws from `d` (time at most `Td`, call cost at most `ad`) and calls the second stage of `B`
(time at most `T`, call cost at most `a`). -/
theorem pairFstRed.timeBound_timed {σ β γ : Type} (d : Unit → SPTree.Timed γ)
    (dCost : Unit → ℕ) (B : FamilyDistinguisher σ Unit (β × γ)) (pre : SPTree.Timed (σ × Unit))
    (guess : σ → β × γ → SPTree.Timed Bool) (guessCost : σ → β × γ → ℕ) {Td ad T a : ℕ}
    (hd : (d ()).time ≤ Td) (hdc : dCost () ≤ ad) (hg : ∀ s y, (guess s y).time ≤ T)
    (hgc : ∀ s y, guessCost s y ≤ a) :
    (pairFstRed.timed d dCost B pre guess guessCost).TimeBound pre.time
      (ad + Td + a + T + 2) := by
  refine ⟨?_, fun st r => ?_⟩
  · simp [pairFstRed.timed, pairFstRed.pre.tree.timed, SPTree.Timed.stepTime]
  · change SPTree.Timed.stepTime (pairFstRed.guess.tree.timed d dCost B pre guess guessCost st r) ≤
      ad + Td + a + T + 2
    simp only [pairFstRed.guess.tree.timed, SPTree.Timed.stepTime_delay]
    have := SPTree.Timed.stepTime_bind_le (d ())
      (fun x => (1 + guessCost st (r, x), guess st (r, x))) (a + T + 1) fun x => by
        simp only [SPTree.Timed.stepTime]; have := hg st (r, x); have := hgc st (r, x); omega
    omega

/-- **Time of `pairSndRed`**: its first stage runs the first stage of `B` and draws from `c`
(time at most `Tc`, call cost at most `ac`); its second stage calls the second stage of `B`
(time at most `T`, call cost at most `a`). -/
theorem pairSndRed.timeBound_timed {σ β γ : Type} (c : Unit → SPTree.Timed β)
    (cCost : Unit → ℕ) (B : FamilyDistinguisher σ Unit (β × γ)) (pre : SPTree.Timed (σ × Unit))
    (guess : σ → β × γ → SPTree.Timed Bool) (guessCost : σ → β × γ → ℕ) {Tc ac T a : ℕ}
    (hc : (c ()).time ≤ Tc) (hcc : cCost () ≤ ac) (hg : ∀ s y, (guess s y).time ≤ T)
    (hgc : ∀ s y, guessCost s y ≤ a) :
    (pairSndRed.timed c cCost B pre guess guessCost).TimeBound (pre.time + ac + Tc + 1)
      (a + T + 1) := by
  refine ⟨?_, fun st q => ?_⟩
  · change SPTree.Timed.stepTime (pairSndRed.pre.tree.timed c cCost B pre guess guessCost) ≤
      pre.time + ac + Tc + 1
    simp only [pairSndRed.pre.tree.timed]
    have := SPTree.Timed.stepTime_bind_le pre
      (fun x => SPTree.Timed.delay (1 + cCost ())
        ((c ()).bind fun r => (0, SPTree.Timed.ret ((x.1, r), ())))) (ac + Tc + 1) fun x => by
        rw [SPTree.Timed.stepTime_delay]
        have := SPTree.Timed.stepTime_bind_le (c ())
          (fun r => (0, SPTree.Timed.ret ((x.1, r), ()))) 0 fun r => by
            simp [SPTree.Timed.stepTime, SPTree.Timed.time_ret]
        omega
    omega
  · change SPTree.Timed.stepTime (pairSndRed.guess.tree.timed c cCost B pre guess guessCost st q) ≤
      a + T + 1
    simp only [pairSndRed.guess.tree.timed, SPTree.Timed.stepTime]
    have := hg st.1 (st.2, q); have := hgc st.1 (st.2, q); omega

section HybridHops

variable {W ρ Z : Type} (getRoot : ρ → SPTree.Timed W) (getRootCost : ρ → ℕ)
  (post : W → SPTree.Timed ρ) (postCost : W → ℕ) (out : W → W) (outCost : W → ℕ)
  (sec : Unit → SPTree.Timed Z) (secCost : Unit → ℕ) (s : W × Z → SPTree.Timed W)
  (sCost : W × Z → ℕ) (secI : Unit → SPTree.Timed Z) (secICost : Unit → ℕ)
  (sI : W × Z → SPTree.Timed W) (sICost : W × Z → ℕ) (i : ℕ) (bs : List Bool) (x : ρ)
  (h₀ : Heap) (D : List W → SPTree.Timed Bool) (DCost : List W → ℕ)
  (hAppend : List W → List W → List W) (hAppendCost : List W → List W → ℕ)
  {T c co TD aD ah : ℕ} (hg : ∀ x, (getRoot x).time ≤ T) (hp : ∀ w, (post w).time ≤ T)
  (hsec : ∀ u, (sec u).time ≤ T) (hs : ∀ p, (s p).time ≤ T) (hsecI : ∀ u, (secI u).time ≤ T)
  (hsI : ∀ p, (sI p).time ≤ T) (hgc : ∀ x, getRootCost x ≤ c) (hpc : ∀ w, postCost w ≤ c)
  (hsecc : ∀ u, secCost u ≤ c) (hsc : ∀ p, sCost p ≤ c) (hsecIc : ∀ u, secICost u ≤ c)
  (hsIc : ∀ p, sICost p ≤ c) (hoc : ∀ w, outCost w ≤ co) (hD : ∀ v, (D v).time ≤ TD)
  (hDc : ∀ v, DCost v ≤ aD) (hac : ∀ u v, hAppendCost u v ≤ ah)

include hg hp hsec hs hgc hpc hsecc hsc hoc hD hDc hac in
/-- The second stage of both hop reductions, after the challenge state `k`: one call of `post`,
the computational epochs after epoch `i` and one call of `D`. -/
private theorem hybGuess_stepTime_le (k : W) (ks₀ : List W) (C : ℕ) :
    SPTree.Timed.stepTime (SPTree.Timed.delay (C + postCost k)
      ((post k).bind fun x =>
        SPTree.Timed.delay (2 + (List.drop.timedCost (i + 1) bs + 1) +
          (epochFold.tree.timed (fun a => getRoot a) (fun a => 1 + getRootCost a)
            (fun a => post a) (fun a => 1 + postCost a) out outCost (fun a => sec a)
            (fun a => 1 + secCost a) (fun a => s a) (fun a => 1 + sCost a)
            (List.drop (i + 1) bs) x).1)
        ((epochFold.tree.timed (fun a => getRoot a) (fun a => 1 + getRootCost a)
            (fun a => post a) (fun a => 1 + postCost a) out outCost (fun a => sec a)
            (fun a => 1 + secCost a) (fun a => s a) (fun a => 1 + sCost a)
            (List.drop (i + 1) bs) x).2.bind fun x_2 =>
          (1 + (DCost (hAppend ks₀ ((bif bs.getD i false then k else out k) :: x_2)) +
            (1 + (hAppendCost ks₀ ((bif bs.getD i false then k else out k) :: x_2) +
              (1 + (1 + List.getD.timedCost bs i false + (1 + outCost k + 1)))))),
            D (hAppend ks₀ ((bif bs.getD i false then k else out k) :: x_2)))))) ≤
      C + bs.length * (4 * T + 4 * c + co + 4 * bs.length + 17) + T + c + co + TD + aD + ah +
        16 := by
  have hE := epochFold.tree.timeBound_timed getRoot post out outCost sec s hg hp hsec hs hoc
    (bs.drop (i + 1)) (fun a => 1 + getRootCost a) (fun a => 1 + postCost a)
    (fun a => 1 + secCost a) (fun a => 1 + sCost a) (c + 1) (fun a => by grind)
    (fun a => by grind) (fun a => by grind) (fun a => by grind)
  have hdl : (bs.drop (i + 1)).length ≤ bs.length := by simp
  have hm : (bs.drop (i + 1)).length * (4 * T + 4 * (c + 1) + co +
      4 * (bs.drop (i + 1)).length + 9) + 4 * bs.length ≤
      bs.length * (4 * T + 4 * c + co + 4 * bs.length + 17) := by
    have := Nat.mul_le_mul hdl (show 4 * T + 4 * (c + 1) + co + 4 * (bs.drop (i + 1)).length + 9
      ≤ 4 * T + 4 * c + co + 4 * bs.length + 13 by omega)
    nlinarith
  have hd := List.drop.timedCost_le (i + 1) bs
  have hgd := List.getD.timedCost_le bs i false
  generalize bs.length * (4 * T + 4 * c + co + 4 * bs.length + 17) = K at hm ⊢
  generalize (bs.drop (i + 1)).length * (4 * T + 4 * (c + 1) + co +
      4 * (bs.drop (i + 1)).length + 9) = M at hm hE
  simp only [SPTree.Timed.stepTime] at hE
  rw [SPTree.Timed.stepTime_delay]
  refine (Nat.add_le_add_left (SPTree.Timed.stepTime_bind_le _ _
    (K + co + TD + aD + ah + 15) fun y => ?_) _).trans ?_
  · rw [SPTree.Timed.stepTime_delay]
    refine (Nat.add_le_add_left (SPTree.Timed.stepTime_bind_le _ _
      (TD + aD + ah + co + 2 * bs.length + 10) fun z => ?_) _).trans ?_
    · simp only [SPTree.Timed.stepTime]
      have := hD (hAppend ks₀ ((bif bs.getD i false then k else out k) :: z))
      have := hDc (hAppend ks₀ ((bif bs.getD i false then k else out k) :: z))
      have := hac ks₀ ((bif bs.getD i false then k else out k) :: z)
      have := hoc k
      omega
    · have := hE y
      grind
  · have := hp k; have := hpc k; omega

include hg hp hsec hs hsecI hsI hgc hpc hsecc hsc hsecIc hsIc hoc hD hDc hac in
/-- **Time of `secHybRed`**: its first stage resets the heap to `h₀`, runs the first `i`
idealized epochs and reads the root; its second stage calls the stretch `s`, then runs the
computational epochs after epoch `i` and calls `D`. -/
theorem secHybRed.timeBound_timed :
    (secHybRed.timed getRoot getRootCost post postCost out outCost sec secCost s sCost secI
      secICost sI sICost i bs x h₀ D DCost hAppend hAppendCost).TimeBound
      (h₀.data.keys.card + i * (4 * T + 4 * c + co + 4 * i + 13) + T + c + 4)
      (bs.length * (4 * T + 4 * c + co + 4 * bs.length + 17) + 2 * T + 2 * c + co + TD + aD +
        ah + 18) := by
  refine ⟨?_, fun st r => ?_⟩
  · have hI := idealPrefix.tree.timeBound_timed (fun a => getRoot a) (fun a => post a) out
      outCost (fun a => secI a) (fun a => sI a) hg hp hsecI hsI hoc i (fun a => 1 + getRootCost a)
      (fun a => 1 + postCost a) (fun a => 1 + secICost a) (fun a => 1 + sICost a) (c + 1)
      (fun a => by grind) (fun a => by grind) (fun a => by grind) (fun a => by grind) bs x
    have hm : i * (4 * T + 4 * (c + 1) + co + 4 * i + 9) ≤
        i * (4 * T + 4 * c + co + 4 * i + 13) := Nat.mul_le_mul_left _ (by omega)
    generalize i * (4 * T + 4 * c + co + 4 * i + 13) = K at hm ⊢
    generalize i * (4 * T + 4 * (c + 1) + co + 4 * i + 9) = L at hm hI
    simp only [secHybRed.timed, secHybRed.pre.tree.timed, SPTree.Timed.stepTime,
      SPTree.Timed.time_load]
    refine le_trans (Nat.add_le_add_left (Nat.add_le_add_left
      (SPTree.Timed.prefix_bind_le _ _ _ (1 + c + T) fun y => ?_) _) _) ?_
    · rw [SPTree.Timed.stepTime_delay]
      refine (Nat.add_le_add_left (SPTree.Timed.stepTime_bind_le _ _ 0 fun z => ?_) _).trans ?_
      · simp [SPTree.Timed.stepTime, SPTree.Timed.time_ret]
      · have := hg y.2; have := hgc y.2; omega
    · simp only [SPTree.Timed.stepTime] at hI
      omega
  · simp only [secHybRed.timed, secHybRed.guess.tree.timed, Prod.mk.eta]
    rw [SPTree.Timed.stepTime_delay]
    refine (Nat.add_le_add_left (SPTree.Timed.stepTime_bind_le _ _ _ fun k =>
      hybGuess_stepTime_le getRoot getRootCost post postCost out outCost sec secCost s sCost i
        bs D DCost hAppend hAppendCost hg hp hsec hs hgc hpc hsecc hsc hoc hD hDc hac k st.1 1)
      _).trans ?_
    have := hs (st.2, r); have := hsc (st.2, r); omega

include hg hp hsec hs hsecI hsI hgc hpc hsecc hsc hsecIc hsIc hoc hD hDc hac in
/-- **Time of `stretchHybRed`**: its first stage resets the heap to `h₀`, runs the first `i`
idealized epochs, reads the root and draws the idealized secret; its second stage runs the
computational epochs after epoch `i` and calls `D`. -/
theorem stretchHybRed.timeBound_timed :
    (stretchHybRed.timed getRoot getRootCost post postCost out outCost sec secCost s sCost secI
      secICost sI sICost i bs x h₀ D DCost hAppend hAppendCost).TimeBound
      (h₀.data.keys.card + i * (4 * T + 4 * c + co + 4 * i + 13) + 2 * T + 2 * c + 5)
      (bs.length * (4 * T + 4 * c + co + 4 * bs.length + 17) + T + c + co + TD + aD + ah +
        17) := by
  refine ⟨?_, fun ks₀ k => ?_⟩
  · have hI := idealPrefix.tree.timeBound_timed (fun a => getRoot a) (fun a => post a) out
      outCost (fun a => secI a) (fun a => sI a) hg hp hsecI hsI hoc i (fun a => 1 + getRootCost a)
      (fun a => 1 + postCost a) (fun a => 1 + secICost a) (fun a => 1 + sICost a) (c + 1)
      (fun a => by grind) (fun a => by grind) (fun a => by grind) (fun a => by grind) bs x
    have hm : i * (4 * T + 4 * (c + 1) + co + 4 * i + 9) ≤
        i * (4 * T + 4 * c + co + 4 * i + 13) := Nat.mul_le_mul_left _ (by omega)
    generalize i * (4 * T + 4 * c + co + 4 * i + 13) = K at hm ⊢
    generalize i * (4 * T + 4 * (c + 1) + co + 4 * i + 9) = L at hm hI
    simp only [stretchHybRed.timed, stretchHybRed.pre.tree.timed, SPTree.Timed.stepTime,
      SPTree.Timed.time_load]
    refine le_trans (Nat.add_le_add_left (Nat.add_le_add_left
      (SPTree.Timed.prefix_bind_le _ _ _ (2 + 2 * c + 2 * T) fun y => ?_) _) _) ?_
    · rw [SPTree.Timed.stepTime_delay]
      refine (Nat.add_le_add_left (SPTree.Timed.stepTime_bind_le _ _ (1 + c + T)
        fun z => ?_) _).trans ?_
      · rw [SPTree.Timed.stepTime_delay]
        refine (Nat.add_le_add_left (SPTree.Timed.stepTime_bind_le _ _ 0
          fun w => ?_) _).trans ?_
        · simp [SPTree.Timed.stepTime, SPTree.Timed.time_ret]
        · have := hsecI (); have := hsecIc (); omega
      · have := hg y.2; have := hgc y.2; omega
    · simp only [SPTree.Timed.stepTime] at hI
      omega
  · simp only [stretchHybRed.timed, stretchHybRed.guess.tree.timed, Prod.mk.eta]
    have := hybGuess_stepTime_le getRoot getRootCost post postCost out outCost sec secCost s
      sCost i bs D DCost hAppend hAppendCost hg hp hsec hs hgc hpc hsecc hsc hoc hD hDc hac k ks₀ 1
    omega

/-! ### Bounds at the lengths the hop reductions reach

The second stage of a hop reduction appends once, to the view `ks₀` of the first stage, and runs
`D` on the result. An append of cost linear in the length of its first argument has no bound over
all states, so the theorems below bound the second stage on the states of the first stage: the
view has at most `i` entries (`idealPrefix.tree.allRet_length`), the append costs at most
`aa * i + ba`, and `D` receives at most `i + 1 + (bs.length - (i + 1))` entries. -/

include hg hp hsec hs hgc hpc hsecc hsc hoc in
/-- The second stage of both hop reductions, after the challenge state `k`, on a view `ks₀` of at
most `i` entries, with append of cost linear in the length of its first argument and `D` bounded
on the lengths of the views that reach it. -/
private theorem hybGuess_stepTime_le_len {aa ba : ℕ}
    (hlen : ∀ u v, (hAppend u v).length ≤ u.length + v.length)
    (hDl : ∀ v, v.length ≤ i + 1 + (bs.length - (i + 1)) → (D v).time ≤ TD)
    (hDcl : ∀ v, v.length ≤ i + 1 + (bs.length - (i + 1)) → DCost v ≤ aD)
    (hacl : ∀ u v, hAppendCost u v ≤ aa * u.length + ba)
    (k : W) (ks₀ : List W) (hks : ks₀.length ≤ i) (C : ℕ) :
    SPTree.Timed.stepTime (SPTree.Timed.delay (C + postCost k)
      ((post k).bind fun x =>
        SPTree.Timed.delay (2 + (List.drop.timedCost (i + 1) bs + 1) +
          (epochFold.tree.timed (fun a => getRoot a) (fun a => 1 + getRootCost a)
            (fun a => post a) (fun a => 1 + postCost a) out outCost (fun a => sec a)
            (fun a => 1 + secCost a) (fun a => s a) (fun a => 1 + sCost a)
            (List.drop (i + 1) bs) x).1)
        ((epochFold.tree.timed (fun a => getRoot a) (fun a => 1 + getRootCost a)
            (fun a => post a) (fun a => 1 + postCost a) out outCost (fun a => sec a)
            (fun a => 1 + secCost a) (fun a => s a) (fun a => 1 + sCost a)
            (List.drop (i + 1) bs) x).2.bind fun x_2 =>
          (1 + (DCost (hAppend ks₀ ((bif bs.getD i false then k else out k) :: x_2)) +
            (1 + (hAppendCost ks₀ ((bif bs.getD i false then k else out k) :: x_2) +
              (1 + (1 + List.getD.timedCost bs i false + (1 + outCost k + 1)))))),
            D (hAppend ks₀ ((bif bs.getD i false then k else out k) :: x_2)))))) ≤
      C + bs.length * (4 * T + 4 * c + co + 4 * bs.length + 17) + T + c + co + TD + aD +
        (aa * i + ba) + 16 := by
  have hE := epochFold.tree.timeBound_timed getRoot post out outCost sec s hg hp hsec hs hoc
    (bs.drop (i + 1)) (fun a => 1 + getRootCost a) (fun a => 1 + postCost a)
    (fun a => 1 + secCost a) (fun a => 1 + sCost a) (c + 1) (fun a => by grind)
    (fun a => by grind) (fun a => by grind) (fun a => by grind)
  have hdl : (bs.drop (i + 1)).length ≤ bs.length := by simp
  have hm : (bs.drop (i + 1)).length * (4 * T + 4 * (c + 1) + co +
      4 * (bs.drop (i + 1)).length + 9) + 4 * bs.length ≤
      bs.length * (4 * T + 4 * c + co + 4 * bs.length + 17) := by
    have := Nat.mul_le_mul hdl (show 4 * T + 4 * (c + 1) + co + 4 * (bs.drop (i + 1)).length + 9
      ≤ 4 * T + 4 * c + co + 4 * bs.length + 13 by omega)
    nlinarith
  have hd := List.drop.timedCost_le (i + 1) bs
  have hgd := List.getD.timedCost_le bs i false
  have hap := Nat.mul_le_mul_left aa hks
  generalize bs.length * (4 * T + 4 * c + co + 4 * bs.length + 17) = K at hm ⊢
  generalize (bs.drop (i + 1)).length * (4 * T + 4 * (c + 1) + co +
      4 * (bs.drop (i + 1)).length + 9) = M at hm hE
  simp only [SPTree.Timed.stepTime] at hE
  rw [SPTree.Timed.stepTime_delay]
  refine (Nat.add_le_add_left (SPTree.Timed.stepTime_bind_le _ _
    (K + co + TD + aD + (aa * i + ba) + 15) fun y => ?_) _).trans ?_
  · rw [SPTree.Timed.stepTime_delay]
    refine (Nat.add_le_add_left (SPTree.Timed.stepTime_bind_le_of_allRet _ _
      (TD + aD + (aa * i + ba) + co + 2 * bs.length + 10)
      (epochFold.tree.allRet_length _ _ _ _ out outCost _ _ _ _ (bs.drop (i + 1)) y)
      fun z hz => ?_) _).trans ?_
    · have hl : (hAppend ks₀ ((bif bs.getD i false then k else out k) :: z)).length ≤
          i + 1 + (bs.length - (i + 1)) := by
        have := hlen ks₀ ((bif bs.getD i false then k else out k) :: z)
        simp only [List.length_cons, List.length_drop] at this hz
        omega
      simp only [SPTree.Timed.stepTime]
      have := hDl _ hl
      have := hDcl _ hl
      have := hacl ks₀ ((bif bs.getD i false then k else out k) :: z)
      have := hoc k
      omega
    · have := hE y
      grind
  · have := hp k; have := hpc k; omega

include hg hp hsec hs hsecI hsI hgc hpc hsecc hsc hsecIc hsIc hoc in
/-- **Time of `secHybRed` on the states of its first stage.** The first stage has the bound of
`secHybRed.timeBound_timed` and returns a view of at most `i` entries. On such a state, with
append of cost at most `aa * u.length + ba` and `D` bounded on the views of length at most
`i + 1 + (bs.length - (i + 1))`, the second stage takes the bound of
`secHybRed.timeBound_timed` at the append cost `aa * i + ba`. -/
theorem secHybRed.timeBound_timed_len {aa ba : ℕ}
    (hlen : ∀ u v, (hAppend u v).length ≤ u.length + v.length)
    (hDl : ∀ v, v.length ≤ i + 1 + (bs.length - (i + 1)) → (D v).time ≤ TD)
    (hDcl : ∀ v, v.length ≤ i + 1 + (bs.length - (i + 1)) → DCost v ≤ aD)
    (hacl : ∀ u v, hAppendCost u v ≤ aa * u.length + ba) :
    let R := secHybRed.timed getRoot getRootCost post postCost out outCost sec secCost s sCost
      secI secICost sI sICost i bs x h₀ D DCost hAppend hAppendCost
    SPTree.Timed.stepTime (R.preCost, R.pre) ≤
        h₀.data.keys.card + i * (4 * T + 4 * c + co + 4 * i + 13) + T + c + 4 ∧
      SPTree.Timed.AllRet (fun p => p.1.1.length ≤ i) R.pre ∧
      ∀ st r, st.1.length ≤ i → SPTree.Timed.stepTime (R.guessCost st r, R.guess st r) ≤
        bs.length * (4 * T + 4 * c + co + 4 * bs.length + 17) + 2 * T + 2 * c + co + TD + aD +
          (aa * i + ba) + 18 := by
  intro R
  refine ⟨(secHybRed.timeBound_timed getRoot getRootCost post postCost out outCost sec secCost s
    sCost secI secICost sI sICost i bs x h₀ (fun _ => SPTree.Timed.ret true) (fun _ => 0) hAppend
    (fun _ _ => 0) (TD := 0) (aD := 0) (ah := 0) hg hp hsec hs hsecI hsI hgc hpc hsecc hsc hsecIc
    hsIc hoc (fun _ => by simp [SPTree.Timed.time_ret]) (fun _ => le_rfl)
    (fun _ _ => le_rfl)).1, ?_, fun st r hst => ?_⟩
  · simp only [R, secHybRed.timed, secHybRed.pre.tree.timed, SPTree.Timed.AllRet]
    refine SPTree.Timed.allRet_bind_of (SPTree.Timed.allRet_mono (fun p hp => ?_) _
      (idealPrefix.tree.allRet_length _ _ _ _ out outCost _ _ _ _ i bs x))
    refine SPTree.Timed.allRet_bind_of (SPTree.Timed.allRet_of_forall (fun _ => hp) _)
  · simp only [R, secHybRed.timed, secHybRed.guess.tree.timed, Prod.mk.eta]
    rw [SPTree.Timed.stepTime_delay]
    refine (Nat.add_le_add_left (SPTree.Timed.stepTime_bind_le _ _ _ fun k =>
      hybGuess_stepTime_le_len getRoot getRootCost post postCost out outCost sec secCost s sCost i
        bs D DCost hAppend hAppendCost hg hp hsec hs hgc hpc hsecc hsc hoc hlen hDl hDcl hacl k st.1
        hst 1) _).trans ?_
    have := hs (st.2, r); have := hsc (st.2, r); omega

include hg hp hsec hs hsecI hsI hgc hpc hsecc hsc hsecIc hsIc hoc in
/-- **Time of `stretchHybRed` on the states of its first stage.** The first stage has the bound
of `stretchHybRed.timeBound_timed` and returns a view of at most `i` entries. On such a state,
with append of cost at most `aa * u.length + ba` and `D` bounded on the views of length at most
`i + 1 + (bs.length - (i + 1))`, the second stage takes the bound of
`stretchHybRed.timeBound_timed` at the append cost `aa * i + ba`. -/
theorem stretchHybRed.timeBound_timed_len {aa ba : ℕ}
    (hlen : ∀ u v, (hAppend u v).length ≤ u.length + v.length)
    (hDl : ∀ v, v.length ≤ i + 1 + (bs.length - (i + 1)) → (D v).time ≤ TD)
    (hDcl : ∀ v, v.length ≤ i + 1 + (bs.length - (i + 1)) → DCost v ≤ aD)
    (hacl : ∀ u v, hAppendCost u v ≤ aa * u.length + ba) :
    let R := stretchHybRed.timed getRoot getRootCost post postCost out outCost sec secCost s
      sCost secI secICost sI sICost i bs x h₀ D DCost hAppend hAppendCost
    SPTree.Timed.stepTime (R.preCost, R.pre) ≤
        h₀.data.keys.card + i * (4 * T + 4 * c + co + 4 * i + 13) + 2 * T + 2 * c + 5 ∧
      SPTree.Timed.AllRet (fun p => p.1.length ≤ i) R.pre ∧
      ∀ ks₀ k, ks₀.length ≤ i → SPTree.Timed.stepTime (R.guessCost ks₀ k, R.guess ks₀ k) ≤
        bs.length * (4 * T + 4 * c + co + 4 * bs.length + 17) + T + c + co + TD + aD +
          (aa * i + ba) + 17 := by
  intro R
  refine ⟨(stretchHybRed.timeBound_timed getRoot getRootCost post postCost out outCost sec secCost
    s sCost secI secICost sI sICost i bs x h₀ (fun _ => SPTree.Timed.ret true) (fun _ => 0) hAppend
    (fun _ _ => 0) (TD := 0) (aD := 0) (ah := 0) hg hp hsec hs hsecI hsI hgc hpc hsecc hsc hsecIc
    hsIc hoc (fun _ => by simp [SPTree.Timed.time_ret]) (fun _ => le_rfl)
    (fun _ _ => le_rfl)).1, ?_, fun ks₀ k hst => ?_⟩
  · simp only [R, stretchHybRed.timed, stretchHybRed.pre.tree.timed, SPTree.Timed.AllRet]
    refine SPTree.Timed.allRet_bind_of (SPTree.Timed.allRet_mono (fun p hp => ?_) _
      (idealPrefix.tree.allRet_length _ _ _ _ out outCost _ _ _ _ i bs x))
    refine SPTree.Timed.allRet_bind_of (SPTree.Timed.allRet_of_forall (fun _ => ?_) _)
    exact SPTree.Timed.allRet_bind_of (SPTree.Timed.allRet_of_forall (fun _ => hp) _)
  · simp only [R, stretchHybRed.timed, stretchHybRed.guess.tree.timed, Prod.mk.eta]
    have := hybGuess_stepTime_le_len getRoot getRootCost post postCost out outCost sec secCost s
      sCost i bs D DCost hAppend hAppendCost hg hp hsec hs hgc hpc hsecc hsc hoc hlen hDl hDcl hacl
      k ks₀ hst 1
    omega

end HybridHops

end CatCrypt.Crypto.HybridArgument
