/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCFeedbackLaws
public import CatCryptCore.Crypto.UCFuelPad
public import CatCryptCore.Crypto.UCSquare

/-!
# Feedback through a simulator, and the truncation of feedback

**The slide lemma.** Let `π` be a multi-call simulator from `(EG, OG)` to `(E, O)` and `Y` a
system on `(EG ⊕ X, OG ⊕ X)`. The simulator `π` extended by forwarding on the wire `X`, running
with `Y`, and then fed back along `X`, agrees with `π` running with the loopback of `Y`
(`Sys.loopback_slide`). In the first system an activation of `π` is split across the
activations of the tensor that the feedback hybrid makes, so `π` enters the tensor in its
counted form `π.counted N`, which counts its calls across those activations. The fuels differ:
the outer loopback counts the wire passes of a whole activation, the inner loopback those of
one call of `π`; the two systems agree when every call of `π` to the loopback of `Y` ends within
`k` wire passes (`Sys.ExitsWithin Y Inv k`), the inner fuel is at least `k` and the outer fuel
is at least `k * (π.fuel + 1)`.

With it, realization behind a simulator and squares pass through feedback with a wire on both
edges (`RealizesSim.loopback_wire`, `Square.loopback`).

**Truncation.** Two loopbacks of a lossless system with different fuels `n` and `m` realize each
other with bound the probability that some activation produces more than `min n m` wire values
(`Sys.loopback_truncation`). The flagged loopback `Sys.loopbackFlag S n j cut` is the loopback
with fuel `n` whose state records whether an activation has produced more than `j` wire values.

## Main definitions

* `Sys.fbNext`: the continuation of an activation of the loopback after a wire value.
* `Sys.fbRunCount`: the activation of the loopback with the number of wire values produced.
* `Sys.loopbackFlag`: the loopback that flags an activation with more than `j` wire values.

## Main results

* `Sys.loopback_slide`: the slide lemma, at distance `0`.
* `Realizes.loopback_slide`: realization of `π` extended by forwarding passes to the loopback.
* `RealizesSim.loopback_wire`: realization behind a simulator under feedback, wire on both
  edges.
* `Square.loopback`: a square with the extended simulator on the right gives the square of the
  feedback composites with `π` on the right.
* `Sys.loopback_truncation`: the truncation tail.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open scoped ENNReal

namespace Sys

variable {τ E O X : Type}

/-- The continuation of an activation of the loopback of `S` after the wire value `x` in the
state `t`, with `n` further calls allowed: the activation from the event `inr x`, or the output
`cut x` when no call is left. -/
noncomputable def fbNext (S : Sys τ (E ⊕ X) (O ⊕ X)) (cut : X → O) : ℕ → X → τ → SPComp (τ × O)
  | 0, x, t => SPComp.pure (t, cut x)
  | n + 1, x, t => fbRun S cut n (.inr x) t

/-- Unfolding lemma of `fbRun`: one step of `S`, then the output or `fbNext`. -/
theorem fbRun_eq_bind (S : Sys τ (E ⊕ X) (O ⊕ X)) (cut : X → O) (n : ℕ) (g : E ⊕ X) (t : τ) :
    fbRun S cut n g t = SPComp.bind (S.step t g) fun q =>
      Sum.elim (fun o => SPComp.pure (q.1, o)) (fun x => fbNext S cut n x q.1) q.2 := by
  cases n <;> rfl

/-! ## The slide lemma -/

section Slide

variable {σ υ EG OG : Type} (π : MultiHybrid σ E O EG OG) (N : ℕ)
  (Y : Sys υ (EG ⊕ X) (OG ⊕ X))

/-- The counted form of `π` extended by forwarding on the wire `X`. -/
noncomputable abbrev slideHybrid :
    MultiHybrid ((σ × ℕ) × Unit) (E ⊕ X) (O ⊕ X) (EG ⊕ X) (OG ⊕ X) :=
  (π.counted N).tensor (MultiHybrid.idSim X X)

/-- The rest of an activation of the tensor after the answer `og` to a call of `π`, with `K`
further calls of the tensor allowed. -/
private noncomputable def ansL (K : ℕ) (sc : σ × ℕ) (og : OG) (u : υ) :
    SPComp (((σ × ℕ) × Unit) × υ × (O ⊕ X)) :=
  match K with
  | 0 => SPComp.map (fun r => ((r.1, ()), u, Sum.inl r.2)) ((π.counted N).finish sc og)
  | K + 1 => SPComp.bind ((π.counted N).resume sc og) fun r =>
      (slideHybrid π N).drive Y K (r.1, ()) (Sum.map Sum.inl Sum.inl r.2) u

/-- The continuation of the outer loopback after an activation of the tensor with result `p`,
with `j` further calls allowed. -/
private noncomputable def contL (cut : X → O) (j : ℕ) (p : ((σ × ℕ) × Unit) × υ × (O ⊕ X)) :
    SPComp ((((σ × ℕ) × Unit) × υ) × O) :=
  Sum.elim (fun o => SPComp.pure ((p.1, p.2.1), o))
    (fun x => fbNext ((slideHybrid π N).withSub Y) cut j x (p.1, p.2.1)) p.2.2

/-- The rest of an activation of `π` over the loopback of `Y` after the answer `og`, with `r`
further calls allowed. -/
private noncomputable def ansR (cY : X → OG) (m r : ℕ) (s : σ) (og : OG) (u : υ) :
    SPComp (σ × (Unit × υ) × O) :=
  match r with
  | 0 => SPComp.bind (π.finish s og) fun r => SPComp.pure (r.1, ((), u), r.2)
  | r + 1 => SPComp.bind (π.resume s og) fun r' =>
      π.drive (Y.loopback m cY) r r'.1 r'.2 ((), u)

/-- The state map of the slide lemma on results. -/
private def slideΦ (p : (((σ × ℕ) × Unit) × υ) × O) : (σ × (Unit × υ)) × O :=
  ((p.1.1.1.1, ((), p.1.2)), p.2)

/-- The reshaping of a result of `drive` on the right. -/
private def slideρ (p : σ × (Unit × υ) × O) : (σ × (Unit × υ)) × O :=
  ((p.1, p.2.1), p.2.2)

/-- The rest of an activation of the tensor from a call `g` on the subroutine. -/
private theorem slide_drive_call (K : ℕ) (sc : σ × ℕ) (g : EG ⊕ X) (u : υ) :
    (slideHybrid π N).drive Y K (sc, ()) (.inl g) u =
      SPComp.bind (Y.step u g) fun q =>
        Sum.elim (fun og => ansL π N Y K sc og q.1)
          (fun x => SPComp.pure ((sc, ()), q.1, Sum.inr x)) q.2 := by
  cases K <;>
  · simp only [MultiHybrid.drive]
    congr 1; funext q; rcases q with ⟨u', og | x⟩ <;>
      simp [ansL, MultiHybrid.idSim, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind,
        MultiHybrid.drive]

/-- The rest of an activation of `π` over the loopback of `Y` from a call `g`. -/
private theorem slide_drive_right (cY : X → OG) (m r : ℕ) (s : σ) (g : EG) (u : υ) :
    π.drive (Y.loopback m cY) r s (.inl g) ((), u) =
      SPComp.bind (fbRun Y cY m (.inl g) u) fun q => ansR π Y cY m r s q.2 q.1 := by
  cases r <;>
  · simp only [MultiHybrid.drive, loopback_step, ansR, SPComp.map, SPComp.bind_assoc,
      SPComp.pure_bind]

/-- The outer loopback from a wire value. -/
private theorem slide_fbRun_inr (cut : X → O) (j : ℕ) (sc : σ × ℕ) (x : X) (u : υ) :
    fbRun ((slideHybrid π N).withSub Y) cut j (.inr x) ((sc, ()), u) =
      SPComp.bind ((slideHybrid π N).drive Y (slideHybrid (X := X) π N).fuel (sc, ())
        (.inl (.inr x)) u) (contL π N Y cut j) := by
  rw [fbRun_eq_bind]
  simp [MultiHybrid.withSub, MultiHybrid.idSim, SPComp.map, SPComp.bind_assoc,
    SPComp.pure_bind]
  rfl

/-- The outer loopback from an outer event. -/
private theorem slide_fbRun_inl (cut : X → O) (j : ℕ) (s : σ) (c : ℕ) (e : E) (u : υ) :
    fbRun ((slideHybrid π N).withSub Y) cut j (.inl e) (((s, c), ()), u) =
      SPComp.bind (π.start s e) fun r =>
        SPComp.bind ((slideHybrid π N).drive Y (slideHybrid (X := X) π N).fuel ((r.1, 0), ())
          (Sum.map Sum.inl Sum.inl r.2) u) (contL π N Y cut j) := by
  rw [fbRun_eq_bind]
  simp [MultiHybrid.withSub, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  rfl

variable (cut : X → O) (cY : X → OG) (m : ℕ) (Inv : υ → Prop) (k : ℕ)

/-- The claim of the slide lemma after an answer to a call of `π` with `r` further calls of `π`
allowed. -/
private def SlideAns (r : ℕ) : Prop :=
  ∀ (c : ℕ) (s : σ) (og : OG) (u : υ) (K j : ℕ), c + r = π.fuel → r ≤ K → Inv u →
    k * r ≤ j →
    SPComp.bind (SPComp.bind (ansL π N Y K (s, c) og u) (contL π N Y cut j))
        (fun p => SPComp.pure (slideΦ p)) =
      SPComp.bind (ansR π Y cY m r s og u) (fun p => SPComp.pure (slideρ p))

/-- The claim of the slide lemma during a call of `π`: the loopback of `Y` from `g`. -/
private theorem slide_wire (hN : π.fuel ≤ N) (r : ℕ) (hA : SlideAns π N Y cut cY m Inv k r) :
    ∀ (i : ℕ) (g : EG ⊕ X) (u : υ) (s : σ) (c K j : ℕ), Y.ExitsBy Inv i g u →
      c + r = π.fuel → r ≤ K → i + k * r ≤ j →
      SPComp.bind (SPComp.bind ((slideHybrid π N).drive Y K ((s, c), ()) (.inl g) u)
          (contL π N Y cut j)) (fun p => SPComp.pure (slideΦ p)) =
        SPComp.bind (SPComp.bind (fbRun Y cY i g u) fun q => ansR π Y cY m r s q.2 q.1)
          (fun p => SPComp.pure (slideρ p)) := by
  intro i
  induction i with
  | zero =>
    intro g u s c K j hex hc hK hj
    rw [slide_drive_call, fbRun_eq_bind]
    simp only [SPComp.bind_assoc]
    refine bind_congr_isOutcome fun q hq => ?_
    have h0 := hex q hq
    rcases q with ⟨u', og | x⟩
    · have h1 := hA c s og u' K j hc hK h0 (by omega)
      simpa only [Sum.elim_inl, SPComp.pure_bind, SPComp.bind_assoc] using h1
    · exact (h0 : False).elim
  | succ i ih =>
    intro g u s c K j hex hc hK hj
    rw [slide_drive_call, fbRun_eq_bind]
    simp only [SPComp.bind_assoc]
    refine bind_congr_isOutcome fun q hq => ?_
    have h0 := hex q hq
    rcases q with ⟨u', og | x⟩
    · have h1 := hA c s og u' K j hc hK h0 (by omega)
      simpa only [Sum.elim_inl, SPComp.pure_bind, SPComp.bind_assoc] using h1
    · obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
      have h1 := ih (.inr x) u' s c (slideHybrid (X := X) π N).fuel j' h0 hc
        (show r ≤ max N 0 by omega) (by omega)
      simp only [Sum.elim_inr, SPComp.pure_bind, contL, fbNext]
      rw [slide_fbRun_inr]
      simpa only [SPComp.bind_assoc] using h1

/-- The claim of the slide lemma at a decision of `π`. -/
private theorem slide_decision (hN : π.fuel ≤ N) (hkm : k ≤ m) (hex : Y.ExitsWithin Inv k)
    (r : ℕ) (hA : SlideAns π N Y cut cY m Inv k r) :
    ∀ (c : ℕ) (s : σ) (d : EG ⊕ O) (u : υ) (K j : ℕ), c + r = π.fuel → r ≤ K → Inv u →
      k * r + k ≤ j →
      SPComp.bind (SPComp.bind ((slideHybrid π N).drive Y K ((s, c), ())
          (Sum.map Sum.inl Sum.inl d) u) (contL π N Y cut j))
          (fun p => SPComp.pure (slideΦ p)) =
        SPComp.bind (π.drive (Y.loopback m cY) r s d ((), u))
          (fun p => SPComp.pure (slideρ p)) := by
  intro c s d u K j hc hK hu hj
  rcases d with g | o
  · rw [Sum.map_inl, slide_drive_right, fbRun_eq_of_exitsBy cY cY k (hex u hu g) hkm]
    exact slide_wire π N Y cut cY m Inv k hN r hA k (.inl g) u s c K j (hex u hu g) hc hK
      (by omega)
  · simp [MultiHybrid.drive, contL, slideΦ, slideρ]

/-- The claim of the slide lemma after an answer, for every number of further calls. -/
private theorem slide_ans (hN : π.fuel ≤ N) (hkm : k ≤ m) (hex : Y.ExitsWithin Inv k) :
    ∀ r, SlideAns π N Y cut cY m Inv k r := by
  intro r
  induction r with
  | zero =>
    intro c s og u K j hc hK hu hj
    rcases K with _ | K
    · simp [ansL, ansR, contL, slideΦ, slideρ, SPComp.map, SPComp.bind_assoc,
        SPComp.pure_bind]
    · simp [ansL, ansR, contL, slideΦ, slideρ, SPComp.map, SPComp.bind_assoc,
        SPComp.pure_bind, MultiHybrid.drive,
        MultiHybrid.counted_resume_of_le π N s c og (by omega : π.fuel ≤ c)]
  | succ r ih =>
    intro c s og u K j hc hK hu hj
    obtain ⟨K, rfl⟩ : ∃ K', K = K' + 1 := ⟨K - 1, by omega⟩
    have hM := slide_decision π N Y cut cY m Inv k hN hkm hex r ih
    simp only [ansL, ansR, MultiHybrid.counted_resume_of_lt π N s c og (by omega : c < π.fuel),
      SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
    congr 1; funext r'
    have h1 := hM (c + 1) r'.1 r'.2 u K j (by omega) (by omega) hu
      (by rw [Nat.mul_add, Nat.mul_one] at hj; exact hj)
    simpa only [SPComp.bind_assoc] using h1

/-- The possible outcomes of an activation of `ρ` against `Xs` are at subroutine states
satisfying `P`, when `P` holds initially and every step of `Xs` preserves it. -/
private theorem drive_isOutcome_inv {σ' τ' E' O' EG' OG' : Type}
    (ρ : MultiHybrid σ' E' O' EG' OG') (Xs : Sys τ' EG' OG') (P : τ' → Prop)
    (hX : ∀ t g q, P t → IsOutcome (Xs.step t g) q → P q.1) :
    ∀ n s d t, P t → ∀ p, IsOutcome (ρ.drive Xs n s d t) p → P p.2.1 := by
  intro n
  induction n with
  | zero =>
    rintro s (g | o) t ht p hp
    · simp only [MultiHybrid.drive] at hp
      obtain ⟨q, hq, hp⟩ := isOutcome_bind hp
      obtain ⟨r, -, hp⟩ := isOutcome_bind hp
      obtain rfl := isOutcome_pure hp
      exact hX t g q ht hq
    · simp only [MultiHybrid.drive] at hp
      obtain rfl := isOutcome_pure hp
      exact ht
  | succ n ih =>
    rintro s (g | o) t ht p hp
    · simp only [MultiHybrid.drive] at hp
      obtain ⟨q, hq, hp⟩ := isOutcome_bind hp
      obtain ⟨r, -, hp⟩ := isOutcome_bind hp
      exact ih _ _ _ (hX t g q ht hq) p hp
    · simp only [MultiHybrid.drive] at hp
      obtain rfl := isOutcome_pure hp
      exact ht

/-- The possible outcomes of a step of `π` over the loopback of `Y` from a state satisfying
`Inv` are at states satisfying `Inv`. -/
private theorem slide_right_isOutcome (hkm : k ≤ m) (hex : Y.ExitsWithin Inv k) (s : σ) (u : υ)
    (e : E) (hu : Inv u) (p : (σ × (Unit × υ)) × O)
    (hp : IsOutcome ((π.withSub (Y.loopback m cY)).step (s, ((), u)) e) p) : Inv p.1.2.2 := by
  have hY : ∀ (w : Unit × υ) (g : EG) q, Inv w.2 →
      IsOutcome ((Y.loopback m cY).step w g) q → Inv q.1.2 := by
    intro w g q hw hq
    rw [loopback_step, fbRun_eq_of_exitsBy cY cY k (hex w.2 hw g) hkm] at hq
    obtain ⟨a, ha, hqa⟩ := isOutcome_bind hq
    obtain rfl := isOutcome_pure hqa
    exact fbRun_isOutcome_of_exitsBy cY k (hex w.2 hw g) a ha
  simp only [MultiHybrid.withSub] at hp
  obtain ⟨r, -, hp⟩ := isOutcome_bind hp
  obtain ⟨p', hp', hpp⟩ := isOutcome_bind hp
  obtain rfl := isOutcome_pure hpp
  exact drive_isOutcome_inv π (Y.loopback m cY) (fun w => Inv w.2) hY _ _ _ _ hu p' hp'

/-- **The slide lemma.** When every call of `π` to the loopback of `Y` ends within `k` wire
passes on an invariant `Inv` of `Y` that holds initially, the counted form of `π` extended by
forwarding on the wire, running with `Y` and fed back with fuel `n ≥ k * (π.fuel + 1)`, and `π`
running with the loopback of `Y` with fuel `m ≥ k`, realize each other at distance `0`, whatever
the cut-off maps. -/
theorem loopback_slide (hN : π.fuel ≤ N) {n : ℕ} (hkm : k ≤ m) (hkn : k * (π.fuel + 1) ≤ n)
    (hinit : Inv Y.init) (hex : Y.ExitsWithin Inv k) :
    Realizes (((slideHybrid π N).withSub Y).loopback n cut) (π.withSub (Y.loopback m cY))
      (fun _ _ => 0) ∧
    Realizes (π.withSub (Y.loopback m cY)) (((slideHybrid π N).withSub Y).loopback n cut)
      (fun _ _ => 0) := by
  have hstep : ∀ (w : Unit × (((σ × ℕ) × Unit) × υ)) (e : E), Inv w.2.2 →
      SPComp.map (fun p => ((p.1.2.1.1.1, ((), p.1.2.2)), p.2))
          ((((slideHybrid π N).withSub Y).loopback n cut).step w e) =
        (π.withSub (Y.loopback m cY)).step (w.2.1.1.1, ((), w.2.2)) e := by
    rintro ⟨⟨⟩, ⟨⟨s, c⟩, ⟨⟩⟩, u⟩ e hu
    rw [loopback_step, slide_fbRun_inl]
    simp only [MultiHybrid.withSub, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
    congr 1; funext r
    have h1 := slide_decision π N Y cut cY m Inv k hN hkm hex π.fuel
      (slide_ans π N Y cut cY m Inv k hN hkm hex π.fuel) 0 r.1 r.2 u
      (slideHybrid (X := X) π N).fuel n (by omega) (show π.fuel ≤ max N 0 by omega) hu
      (by rw [Nat.mul_add, Nat.mul_one] at hkn; exact hkn)
    simpa only [slideΦ, slideρ, SPComp.bind_assoc, SPComp.pure_bind] using h1
  have h : Realizes (((slideHybrid π N).withSub Y).loopback n cut)
      (π.withSub (Y.loopback m cY)) (fun _ _ => 0) := by
    refine realizes_zero_of_stepMap_on _ _ (fun w => Inv w.2.2)
      (fun w => (w.2.1.1.1, ((), w.2.2))) hinit rfl (fun w e hw => ?_) hstep
    refine exists_bind_pure_of_isOutcome _
      (fun p : (Unit × (((σ × ℕ) × Unit) × υ)) × O => Inv p.1.2.2) fun p hp => ?_
    have h1 := isOutcome_map (fun p => ((p.1.2.1.1.1, ((), p.1.2.2)), p.2)) hp
    rw [hstep w e hw] at h1
    exact slide_right_isOutcome π Y cY m Inv k hkm hex _ _ e hw _ h1
  exact ⟨h, fun ζ => (h ζ).symm⟩

end Slide

/-! ## Truncation -/

/-- The activation of the loopback of `S` from the event `g` in the state `t`, with `n` further
calls allowed, together with the number of wire values that `S` outputs during it. -/
noncomputable def fbRunCount (S : Sys τ (E ⊕ X) (O ⊕ X)) (cut : X → O) :
    ℕ → E ⊕ X → τ → SPComp (τ × O × ℕ)
  | 0, g, t => SPComp.bind (S.step t g) fun q =>
      Sum.elim (fun o => SPComp.pure (q.1, o, 0)) (fun x => SPComp.pure (q.1, cut x, 1)) q.2
  | n + 1, g, t => SPComp.bind (S.step t g) fun q =>
      Sum.elim (fun o => SPComp.pure (q.1, o, 0))
        (fun x => SPComp.map (fun p => (p.1, p.2.1, p.2.2 + 1)) (fbRunCount S cut n (.inr x) q.1))
        q.2

/-- Forgetting the count, `fbRunCount` is `fbRun`. -/
theorem map_fbRunCount (S : Sys τ (E ⊕ X) (O ⊕ X)) (cut : X → O) :
    ∀ (n : ℕ) (g : E ⊕ X) (t : τ),
      SPComp.map (fun p => (p.1, p.2.1)) (fbRunCount S cut n g t) = fbRun S cut n g t := by
  intro n
  induction n with
  | zero =>
    intro g t
    simp only [fbRunCount, fbRun, SPComp.map, SPComp.bind_assoc]
    congr 1; funext q; rcases q with ⟨t', o | x⟩ <;> simp [SPComp.pure_bind]
  | succ n ih =>
    intro g t
    simp only [fbRunCount, fbRun, SPComp.map, SPComp.bind_assoc]
    congr 1; funext q; rcases q with ⟨t', o | x⟩
    · simp [SPComp.pure_bind]
    · dsimp only [Sum.elim_inr]
      rw [← ih]
      simp [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]

/-- `fbRunCount` never fails when the steps of `S` never fail. -/
theorem fbRunCount_noFail (S : Sys τ (E ⊕ X) (O ⊕ X)) (cut : X → O)
    (hS : ∀ t g, SPComp.NoFail (S.step t g)) :
    ∀ (n : ℕ) (g : E ⊕ X) (t : τ), SPComp.NoFail (fbRunCount S cut n g t) := by
  intro n
  induction n with
  | zero =>
    intro g t
    exact Assumptions.SPComp.bind_noFail (hS t g) fun q => by
      rcases q with ⟨t', o | x⟩ <;> exact SPComp.pure_noFail _
  | succ n ih =>
    intro g t
    exact Assumptions.SPComp.bind_noFail (hS t g) fun q => by
      rcases q with ⟨t', o | x⟩
      · exact SPComp.pure_noFail _
      · dsimp only [Sum.elim_inr, SPComp.map]
        exact Assumptions.SPComp.bind_noFail (ih _ _) fun _ => SPComp.pure_noFail _

/-- The activations with fuels `n` and `m` agree on the outcomes with at most `j` wire values,
for `j ≤ n` and `j ≤ m`, whatever the cut-off maps. -/
theorem fbRunCount_agree (S : Sys τ (E ⊕ X) (O ⊕ X)) (cut cut' : X → O) {β : Type}
    (κ : τ × O → SPComp β) :
    ∀ (j : ℕ) {n m : ℕ} (g : E ⊕ X) (t : τ), j ≤ n → j ≤ m →
      SPComp.bind (fbRunCount S cut n g t)
          (fun p => if j < p.2.2 then SPComp.fail else κ (p.1, p.2.1)) =
        SPComp.bind (fbRunCount S cut' m g t)
          (fun p => if j < p.2.2 then SPComp.fail else κ (p.1, p.2.1)) := by
  intro j
  induction j with
  | zero =>
    intro n m g t _ _
    have h : ∀ (c : X → O) (n' : ℕ),
        SPComp.bind (fbRunCount S c n' g t)
            (fun p => if 0 < p.2.2 then SPComp.fail else κ (p.1, p.2.1)) =
          SPComp.bind (S.step t g)
            (fun q => Sum.elim (fun o => κ (q.1, o)) (fun _ => SPComp.fail) q.2) := by
      intro c n'
      cases n' <;>
      · simp only [fbRunCount, SPComp.bind_assoc]
        congr 1; funext q; rcases q with ⟨t', o | x⟩ <;>
          simp [SPComp.pure_bind, SPComp.map, SPComp.bind_assoc, bind_fail_right]
    rw [h cut n, h cut' m]
  | succ j ih =>
    intro n m g t hn hm
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [fbRunCount, SPComp.bind_assoc]
    congr 1; funext q; rcases q with ⟨t', o | x⟩
    · simp [SPComp.pure_bind]
    · simp only [Sum.elim_inr, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind,
        Nat.add_lt_add_iff_right]
      exact ih _ _ (by omega) (by omega)

/-- The loopback of `S` with fuel `n` whose state records whether an activation has produced
more than `j` wire values. -/
noncomputable def loopbackFlag (S : Sys τ (E ⊕ X) (O ⊕ X)) (n j : ℕ) (cut : X → O) :
    Sys (τ × Bool) E O where
  init := (S.init, false)
  step t e := SPComp.map (fun p => ((p.1, t.2 || decide (j < p.2.2)), p.2.1))
    (fbRunCount S cut n (.inl e) t.1)

/-- The flagged loopback realizes the loopback at distance `0`. -/
theorem realizes_loopbackFlag (S : Sys τ (E ⊕ X) (O ⊕ X)) (n j : ℕ) (cut : X → O) :
    Realizes (S.loopbackFlag n j cut) (S.loopback n cut) (fun _ _ => 0) :=
  realizes_zero_of_stepMap _ _ (fun w => ((), w.1)) rfl fun w e => by
    rw [loopback_step, ← map_fbRunCount]
    simp [loopbackFlag, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]

/-- **The truncation tail.** For a system `S` whose steps never fail, the loopbacks with fuels
`n` and `m` realize each other with bound the probability that, in the run against the loopback
with fuel `n`, some activation produces more than `min n m` wire values. -/
theorem loopback_truncation (S : Sys τ (E ⊕ X) (O ⊕ X))
    (hS : ∀ t g, SPComp.NoFail (S.step t g)) (n m : ℕ) (cut cut' : X → O) :
    Realizes (S.loopback n cut) (S.loopback m cut')
      (fun _ Z => prBad (S.loopbackFlag n (min n m) cut) Prod.snd Z) := by
  have h1 := realizes_loopbackFlag S n (min n m) cut
  have h3 := realizes_loopbackFlag S m (min n m) cut'
  have hnf : ∀ (n' : ℕ) (c : X → O) (t : τ × Bool) (e : E),
      SPComp.NoFail ((S.loopbackFlag n' (min n m) c).step t e) := fun n' c t e => by
    dsimp only [loopbackFlag, SPComp.map]
    exact Assumptions.SPComp.bind_noFail (fbRunCount_noFail S c hS _ _ _) fun _ =>
      SPComp.pure_noFail _
  have hk : ∀ (c : X → O) (n' : ℕ) (t : τ) (e : E),
      SPComp.bind ((S.loopbackFlag n' (min n m) c).step (t, false) e) (goodK Prod.snd) =
        SPComp.bind (fbRunCount S c n' (.inl e) t) (fun p =>
          if min n m < p.2.2 then SPComp.fail else SPComp.pure ((p.1, false), p.2.1)) := by
    intro c n' t e
    simp only [loopbackFlag, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
    congr 1; funext p
    by_cases hp : min n m < p.2.2 <;> simp [goodK, hp]
  have h2 : Realizes (S.loopbackFlag n (min n m) cut) (S.loopbackFlag m (min n m) cut')
      (fun _ Z => prBad (S.loopbackFlag n (min n m) cut) Prod.snd Z) := by
    intro ζ Z
    refine adv_le_prBad (S.loopbackFlag n (min n m) cut) (S.loopbackFlag m (min n m) cut')
      Prod.snd rfl (hnf n cut) (hnf m cut') ?_ Z
    rintro ⟨t, b⟩ e hb
    obtain rfl : b = false := hb
    rw [hk cut n t e, hk cut' m t e]
    exact fbRunCount_agree S cut cut' (fun q => SPComp.pure ((q.1, false), q.2)) (min n m)
      (.inl e) t (min_le_left n m) (min_le_right n m)
  have h1' : Realizes (S.loopback n cut) (S.loopbackFlag n (min n m) cut) (fun _ _ => 0) :=
    fun ζ => (h1 ζ).symm
  exact fun ζ => (((h1'.trans h2).trans h3) ζ).mono fun Z => by simp

end Sys

/-! ## Realization and squares under feedback through a simulator -/

/-- **Feedback through a simulator** (composition plumbing). If `R` realizes the counted form of
`π` extended by forwarding on the wire, running with `Y`, with bound `b`, both idle at `idle`,
and every call of `π` to the loopback of `Y` ends within `k` wire passes on an invariant of `Y`
that holds initially, then the loopback of `R` with fuel `n ≥ k * (π.fuel + 1)` realizes `π`
running with the loopback of `Y` with fuel `m ≥ k`, with bound `b` at the reduced environment of
the feedback hybrid. -/
theorem Realizes.loopback_slide {τ σ υ E O EG OG X : Type} {R : Sys τ (E ⊕ X) (O ⊕ X)}
    {π : MultiHybrid σ E O EG OG} {N : ℕ} {Y : Sys υ (EG ⊕ X) (OG ⊕ X)}
    {b : (ζ : Type) → Env (Strat ζ (E ⊕ X) (O ⊕ X)) ζ → ℝ≥0∞}
    (h : Realizes R ((Sys.slideHybrid π N).withSub Y) b) (hN : π.fuel ≤ N)
    (idle : E ⊕ X) (oR oY : O ⊕ X) (hR : MultiHybrid.IdleAt R idle oR)
    (hY : MultiHybrid.IdleAt ((Sys.slideHybrid π N).withSub Y) idle oY)
    (Inv : υ → Prop) {k m n : ℕ} (hkm : k ≤ m) (hkn : k * (π.fuel + 1) ≤ n)
    (hinit : Inv Y.init) (hex : Y.ExitsWithin Inv k) (cut : X → O) (cY : X → OG) :
    Realizes (R.loopback n cut) (π.withSub (Y.loopback m cY))
      (fun ζ Z => b (MultiHybrid.RState Unit ζ (E ⊕ X) O)
        ((MultiHybrid.fbHybrid n cut).reduceEnv idle Z)) := by
  have h1 := Realizes.loopback idle oR oY hR hY h n cut
  have h2 := (Sys.loopback_slide π N Y cut cY m Inv k hN hkm hkn hinit hex).1
  exact fun ζ => ((h1.trans h2) ζ).mono fun Z => by simp

/-- **Realization behind a simulator under feedback, wire on both edges** (composition
plumbing). If `R` realizes `I` behind the counted form of `π` extended by forwarding on the
wire, with bound `b`, `R` and the simulator running with `I` are idle at `idle`, and every call
of `π` to the loopback of `I` ends within `k` wire passes on an invariant of `I` that holds
initially, then the loopback of `R` with fuel `n ≥ k * (π.fuel + 1)` realizes the loopback of
`I` with fuel `m ≥ k` behind `π`, with bound `b` at the reduced environment of the feedback
hybrid. -/
theorem RealizesSim.loopback_wire {τ σ υ E O EG OG X : Type} {V : PubView E O}
    {W : PubView EG OG} {VX : PubView X X} {R : Sys τ (E ⊕ X) (O ⊕ X)}
    {I : Sys υ (EG ⊕ X) (OG ⊕ X)} {π : MultiHybrid σ E O EG OG} (hπ : π.Opaque V W) {N : ℕ}
    (hN : π.fuel ≤ N) {b : (ζ : Type) → Env (Strat ζ (E ⊕ X) (O ⊕ X)) ζ → ℝ≥0∞}
    (h : RealizesSim R I (Simulator.tensor (π.counted N) (MultiHybrid.idSim X X)
      (hπ.counted N) (MultiHybrid.idSim_opaque VX)) b)
    (idle : E ⊕ X) (oR oI : O ⊕ X) (hR : MultiHybrid.IdleAt R idle oR)
    (hI : MultiHybrid.IdleAt ((Sys.slideHybrid π N).withSub I) idle oI)
    (Inv : υ → Prop) {k m n : ℕ} (hkm : k ≤ m) (hkn : k * (π.fuel + 1) ≤ n)
    (hinit : Inv I.init) (hex : I.ExitsWithin Inv k) (cut : X → O) (cY : X → OG) :
    RealizesSim (R.loopback n cut) (I.loopback m cY) (Simulator.ofMultiHybrid π hπ)
      (fun ζ Z => b (MultiHybrid.RState Unit ζ (E ⊕ X) O)
        ((MultiHybrid.fbHybrid n cut).reduceEnv idle Z)) :=
  Realizes.loopback_slide h hN idle oR oI hR hI Inv hkm hkn hinit hex cut cY

/-- **Feedback of a square, wire on both edges.** A square whose right simulator is the counted
form of `π` extended by forwarding on the wire `X` gives the square of the feedback composites,
with fuels `n` on top and `m` at the bottom, and `π` on the right. A subroutine `K` is
admissible when it is admissible for the given square, the two systems that the feedback runs
with are idle at `idle`, and every call of `π` to the loopback of the bottom over `K` ends within
`k` wire passes on an invariant that holds initially; the fuels satisfy `m ≥ k` and
`n ≥ k * (π.fuel + 1)`. The bound is that of the given square at the reduced environment of the
feedback hybrid. -/
theorem Square.loopback {σ E O E' O' X EG OG EG' OG' : Type} {V : PubView E O}
    {V' : PubView E' O'} {VX : PubView X X} {VG : PubView EG OG} {VG' : PubView EG' OG'}
    {π₁ : Open (E ⊕ X) (O ⊕ X) EG OG} {π₂ : Open (E' ⊕ X) (O' ⊕ X) EG' OG'}
    {SG : Simulator EG OG EG' OG' VG VG'} {ρ : MultiHybrid σ E O E' O'} (hρ : ρ.Opaque V V')
    {N : ℕ} (hN : ρ.fuel ≤ N) {A : {τ : Type} → Sys τ EG' OG' → Prop}
    {b : {τ : Type} → Sys τ EG' OG' → (ζ : Type) → Env (Strat ζ (E ⊕ X) (O ⊕ X)) ζ → ℝ≥0∞}
    (α : Square π₁ π₂ SG (Simulator.tensor (ρ.counted N) (MultiHybrid.idSim X X)
      (hρ.counted N) (MultiHybrid.idSim_opaque VX)) A b)
    {k m n : ℕ} (hkm : k ≤ m) (hkn : k * (ρ.fuel + 1) ≤ n) (cut : X → O) (cY : X → O')
    (idle : E ⊕ X) (idle' : E' ⊕ X) :
    Square ((Open.feedback n cut idle).comp π₁) ((Open.feedback m cY idle').comp π₂) SG
      (Simulator.ofMultiHybrid ρ hρ)
      (fun K => A K ∧ (∃ o, MultiHybrid.IdleAt (π₁.withSub (SG.withSub K)) idle o) ∧
        (∃ o, MultiHybrid.IdleAt ((Sys.slideHybrid ρ N).withSub (π₂.withSub K)) idle o) ∧
        ∃ Inv : _ → Prop, Inv (π₂.withSub K).init ∧ (π₂.withSub K).ExitsWithin Inv k)
      (fun K ζ Z => b K (MultiHybrid.RState Unit ζ (E ⊕ X) O)
        ((MultiHybrid.fbHybrid n cut).reduceEnv idle Z)) := by
  refine ⟨fun K hK => ?_⟩
  obtain ⟨hA, ⟨oR, hR⟩, ⟨oI, hI⟩, Inv, hinit, hex⟩ := hK
  exact Realizes.loopback_slide (α.realizes K hA) hN idle oR oI hR hI Inv hkm hkn hinit hex
    cut cY

end CatCrypt.Crypto.UCTransparent
