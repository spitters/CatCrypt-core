/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.X3DHSquareJoint
public import CatCryptCore.Crypto.AKE.X3DHSquareGDH

/-!
# The long-term secrets of a party drawn before the run

In the worlds of X3DH with a joint identity and signing key (`jointOWith`, its instances `jointO`
and `simSignO`, and the filtered world `filtJO`) the long-term secrets `lt p = (ik_p, spk_p)` of a
party `p` are drawn at their first use (`ltAt`). A run from a state without `lt p` is the average
over a uniform pair of the runs from the state with `lt p` preset to that pair, for the output
and for the probability of a bad flag that does not read `lt p`.

The draw of `p` may happen at a step only on some outcomes of the step: an injection whose peer is
not `p` draws `p` as the initiator only when the delivered signature verifies on a fresh value of
the random oracle. The proof therefore uses the commutation of the step with the draw (the draw
before the step equals the step followed by the draw; `OracleAdv.run_bind_draw_comm`), which holds
at every step, in place of a trigger predicate on the state and the event.

For the world of the gap Diffie–Hellman reduction (`stepR` of `X3DHSquareGDH`), `relW_preset`
states the coupling relation at the initial states with `lt p` preset, the reduction side at the
pair `(0, s)`; at `p = a` the public identity key of `a` in the reduction is then the challenge
`X` (`keyA_preset`).

## Main results

* `OracleAdv.run_bind_draw_comm`, `OracleAdv.run_map_obs_eq_bind_draw`,
  `OracleAdv.run_flag_eq_bind_draw` — a run against an oracle that commutes with a draw kernel
* `drawComm_ltAt`, `realStep_drawComm`, `completeSig_drawComm`, `filtJO_drawComm`,
  `jointOWith_drawComm` — the steps commute with the draw of `lt p`
* `run_map_obs_eq_bind_ltSet`, `run_flag_eq_tsum_ltSet` — a run of an oracle on layered states
  that commutes with the draw, from a state without `lt p`
* `jointOWith_run_eager`, `jointOWith_flag_eager` and their instances at `jointO`, `simSignO`,
  `filtJO` — the long-term secrets of `p` preset
* `relW_preset`, `keyA_preset`, `pubIK_zero` — the coupling of the reduction at the preset
  states
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.OracleAdv

open scoped ENNReal

section DrawComm

variable {σ D R α β X : Type}

/-- **A run commutes with a draw kernel.** Let `Dr` draw a value and place it in the state, let a
second draw be the first (`hidem`), let a step from a state after the draw keep the drawn value
(`hpers`), and let every step of the oracle `O` commute with the draw (`hcomm`): the draw before
the step equals the step followed by the draw. Then the draw before a run of an oracle adversary
equals the run followed by the draw, together with the drawn value. -/
theorem run_bind_draw_comm (Dr : σ → PMF (X × σ)) (O : σ → D → PMF (R × σ))
    (hidem : ∀ s, ∀ l ∈ (Dr s).support, Dr l.2 = PMF.pure l)
    (hpers : ∀ s, ∀ l ∈ (Dr s).support, ∀ d, ∀ y ∈ (O l.2 d).support,
      Dr y.2 = PMF.pure (l.1, y.2))
    (hcomm : ∀ s d, (Dr s).bind (fun l => O l.2 d) =
      (O s d).bind fun y => (Dr y.2).map fun l => (y.1, l.2))
    (A : OracleAdv D R α) (s : σ) :
    (Dr s).bind (fun l => (OracleAdv.run O A l.2).map fun y => (l.1, y)) =
      (OracleAdv.run O A s).bind fun z => (Dr z.2).map fun l => (l.1, (z.1, l.2)) := by
  induction A generalizing s with
  | ret a =>
    simp only [OracleAdv.run_ret, PMF.pure_map, PMF.pure_bind]
    rfl
  | rand p f ih =>
    simp only [OracleAdv.run_rand, PMF.map_bind, PMF.bind_bind]
    rw [PMF.bind_comm]
    exact congrArg _ (funext fun b => ih b s)
  | query d f ih =>
    simp only [OracleAdv.run_query]
    have step₁ : ∀ l ∈ (Dr s).support,
        ((O l.2 d).bind fun y => OracleAdv.run O (f y.1) y.2).map (fun y => (l.1, y)) =
          (O l.2 d).bind fun y => (OracleAdv.run O (f y.1) y.2).bind
            fun z => (Dr z.2).map fun l => (l.1, (z.1, l.2)) := by
      intro l hl
      rw [PMF.map_bind]
      refine PMF.bind_congr_support _ _ _ fun y hy => ?_
      rw [← ih y.1 y.2, hpers s l hl d y hy, PMF.pure_bind]
    rw [PMF.bind_congr_support _ _ _ step₁, ← PMF.bind_bind, hcomm, PMF.bind_bind,
      PMF.bind_bind]
    refine congrArg _ (funext fun y => ?_)
    rw [PMF.bind_map, ← ih y.1 y.2]
    refine PMF.bind_congr_support _ _ _ fun l hl => ?_
    simp only [Function.comp_apply]
    rw [← ih y.1 l.2, hidem y.2 l hl, PMF.pure_bind]

/-- **The output and an observable of the final state of a run against an oracle that commutes
with a draw kernel** are those of the run from the state after the draw, for an observable that
the draw keeps. -/
theorem run_map_obs_eq_bind_draw (Dr : σ → PMF (X × σ)) (O : σ → D → PMF (R × σ)) (g : σ → β)
    (hg : ∀ s, ∀ l ∈ (Dr s).support, g l.2 = g s)
    (hidem : ∀ s, ∀ l ∈ (Dr s).support, Dr l.2 = PMF.pure l)
    (hpers : ∀ s, ∀ l ∈ (Dr s).support, ∀ d, ∀ y ∈ (O l.2 d).support,
      Dr y.2 = PMF.pure (l.1, y.2))
    (hcomm : ∀ s d, (Dr s).bind (fun l => O l.2 d) =
      (O s d).bind fun y => (Dr y.2).map fun l => (y.1, l.2))
    (A : OracleAdv D R α) (s : σ) :
    (OracleAdv.run O A s).map (fun y => (y.1, g y.2)) =
      (Dr s).bind fun l => (OracleAdv.run O A l.2).map fun y => (y.1, g y.2) := by
  have h := congrArg (PMF.map fun w : X × α × σ => (w.2.1, g w.2.2))
    (run_bind_draw_comm Dr O hidem hpers hcomm A s)
  simp only [PMF.map_bind, PMF.map_comp, Function.comp_def] at h
  rw [h, ← PMF.bind_pure_comp]
  refine congrArg _ (funext fun a => ?_)
  calc PMF.pure (a.1, g a.2) = (Dr a.2).bind fun _ => PMF.pure (a.1, g a.2) :=
        (PMF.bind_const _ _).symm
    _ = _ := by
      rw [← PMF.bind_pure_comp]
      exact PMF.bind_congr_support _ _ _ fun x hx => by simp [hg a.2 x hx]

/-- The draw kernel on flagged states: the draw on the state, the flag kept. -/
noncomputable def drawF (Dr : σ → PMF (X × σ)) (t : σ × Bool) : PMF (X × (σ × Bool)) :=
  (Dr t.1).map fun l => (l.1, (l.2, t.2))

/-- **A flagged oracle commutes with a draw kernel** when the oracle does and the bad event does
not see the draw, neither in the state before the step nor in the state after it. -/
theorem flagWhen_draw_comm (Dr : σ → PMF (X × σ)) (O : σ → D → PMF (R × σ))
    (bad : σ → D → R × σ → Prop) [∀ s d y, Decidable (bad s d y)]
    (hbad₁ : ∀ s d y, ∀ l ∈ (Dr s).support, bad l.2 d y ↔ bad s d y)
    (hbad₂ : ∀ s d y, ∀ l ∈ (Dr y.2).support, bad s d (y.1, l.2) ↔ bad s d y)
    (hcomm : ∀ s d, (Dr s).bind (fun l => O l.2 d) =
      (O s d).bind fun y => (Dr y.2).map fun l => (y.1, l.2))
    (t : σ × Bool) (d : D) :
    (drawF Dr t).bind (fun l => OracleAdv.flagWhen bad O l.2 d) =
      (OracleAdv.flagWhen bad O t d).bind fun y => (drawF Dr y.2).map fun l => (y.1, l.2) := by
  obtain ⟨s, b⟩ := t
  have h₁ : ∀ l ∈ (Dr s).support,
      (O l.2 d).map (fun x => (x.1, (x.2, b || decide (bad l.2 d x)))) =
        (O l.2 d).map (fun x => (x.1, (x.2, b || decide (bad s d x)))) := by
    intro l hl
    simp only [hbad₁ s d _ l hl]
  simp only [drawF, OracleAdv.flagWhen, PMF.bind_map, PMF.map_comp, Function.comp_def]
  rw [PMF.bind_congr_support _ _ _ h₁, ← PMF.map_bind, hcomm, PMF.map_bind]
  refine congrArg _ (funext fun y => ?_)
  rw [PMF.map_comp, ← PMF.bind_pure_comp, ← PMF.bind_pure_comp]
  exact PMF.bind_congr_support _ _ _ fun l hl => by simp [hbad₂ s d y l hl]

/-- **The probability of a bad flag of a run against an oracle that commutes with a draw
kernel** is the average over the draw of that probability from the state after the draw, for a
bad event that does not see the draw. -/
theorem run_flag_eq_bind_draw (Dr : σ → PMF (X × σ)) (O : σ → D → PMF (R × σ))
    (bad : σ → D → R × σ → Prop) [∀ s d y, Decidable (bad s d y)]
    (hbad₁ : ∀ s d y, ∀ l ∈ (Dr s).support, bad l.2 d y ↔ bad s d y)
    (hbad₂ : ∀ s d y, ∀ l ∈ (Dr y.2).support, bad s d (y.1, l.2) ↔ bad s d y)
    (hidem : ∀ s, ∀ l ∈ (Dr s).support, Dr l.2 = PMF.pure l)
    (hpers : ∀ s, ∀ l ∈ (Dr s).support, ∀ d, ∀ y ∈ (O l.2 d).support,
      Dr y.2 = PMF.pure (l.1, y.2))
    (hcomm : ∀ s d, (Dr s).bind (fun l => O l.2 d) =
      (O s d).bind fun y => (Dr y.2).map fun l => (y.1, l.2))
    (A : OracleAdv D R α) (s : σ) (b : Bool) :
    (OracleAdv.run (OracleAdv.flagWhen bad O) A (s, b)).toOuterMeasure {y | y.2.2 = true} =
      ∑' l, Dr s l * (OracleAdv.run (OracleAdv.flagWhen bad O) A (l.2, b)).toOuterMeasure
        {y | y.2.2 = true} := by
  have hsupp : ∀ (t : σ × Bool) (l : X × (σ × Bool)), l ∈ (drawF Dr t).support →
      ∃ l₀ ∈ (Dr t.1).support, l = (l₀.1, (l₀.2, t.2)) := by
    intro t l hl
    simp only [drawF, PMF.support_map, Set.mem_image] at hl
    obtain ⟨l₀, hl₀, rfl⟩ := hl
    exact ⟨l₀, hl₀, rfl⟩
  have h := run_map_obs_eq_bind_draw (drawF Dr) (OracleAdv.flagWhen bad O) Prod.snd
    (fun t l hl => by obtain ⟨l₀, -, rfl⟩ := hsupp t l hl; rfl)
    (fun t l hl => by
      obtain ⟨l₀, hl₀, rfl⟩ := hsupp t l hl
      simp only [drawF, hidem t.1 l₀ hl₀, PMF.pure_map])
    (fun t l hl d y hy => by
      obtain ⟨l₀, hl₀, rfl⟩ := hsupp t l hl
      simp only [OracleAdv.flagWhen, PMF.support_map, Set.mem_image] at hy
      obtain ⟨y₀, hy₀, rfl⟩ := hy
      simp only [drawF, hpers t.1 l₀ hl₀ d y₀ hy₀, PMF.pure_map])
    (flagWhen_draw_comm Dr O bad hbad₁ hbad₂ hcomm) A (s, b)
  have hm : ∀ t, (OracleAdv.run (OracleAdv.flagWhen bad O) A t).toOuterMeasure
      {y | y.2.2 = true} = ((OracleAdv.run (OracleAdv.flagWhen bad O) A t).map
        fun y => (y.1, y.2.2)).toOuterMeasure {z | z.2 = true} := fun t => by
    rw [PMF.toOuterMeasure_map_apply]
    rfl
  rw [hm, h, drawF, PMF.bind_map, PMF.toOuterMeasure_bind_apply]
  exact tsum_congr fun l => by rw [hm]; rfl

end DrawComm

end CatCrypt.Crypto.OracleAdv

namespace CatCrypt.Crypto.AKE.X3DHSquare

open CatCrypt.Core CatCrypt.Crypto CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.AKE.X3DHSquareSigned (realStep completeSig ltAt_of_some realStep_pub)
open CatCrypt.Crypto.PAKE.CPaceSquare (roAt)

/-! ## The draw of the long-term secrets of a party commutes with the steps -/

section DrawLt

variable {S K T : Type} [Fintype S] [Nonempty S]

/-- The state `s` with the long-term secrets of `p` set to `v`. -/
def ltSet (p : PartyId) (v : Option (S × S)) (s : RStT S K T) : RStT S K T :=
  { s with lt := Function.update s.lt p v }

/-- **A step commutes with the draw of `lt p` at `s`**: the draw of the long-term secrets of `p`
before the step `f` equals the step followed by the draw. -/
def DrawComm {γ : Type} (p : PartyId) (f : RStT S K T → PMF (γ × RStT S K T))
    (s : RStT S K T) : Prop :=
  (ltAt s p).bind (fun l => f l.2) = (f s).bind fun y => (ltAt y.2 p).map fun l => (y.1, l.2)

/-- After the draw of `lt p`, the state is the state with `lt p` set to the drawn pair. -/
theorem ltAt_support_eq (s : RStT S K T) (p : PartyId) :
    ∀ l ∈ (ltAt s p).support, l.2 = ltSet p (some l.1) s := by
  intro l hl
  unfold ltAt at hl
  split at hl
  · rename_i v hv
    simp only [PMF.support_pure, Set.mem_singleton_iff] at hl
    subst hl
    simp only [ltSet, ← hv, Function.update_eq_self]
  · simp only [PMF.support_map, Set.mem_image] at hl
    obtain ⟨v, -, rfl⟩ := hl
    rfl

/-- The draw of `lt p` from a state where it is unset. -/
theorem ltAt_of_none (s : RStT S K T) (p : PartyId) (h : s.lt p = none) :
    ltAt s p = (PMF.uniformFintype (S × S)).map fun l => (l, ltSet p (some l) s) := by
  simp only [ltAt, h]
  rfl

/-- The draw of `lt p` from a state where it is set to `v`. -/
theorem ltAt_ltSet_some (s : RStT S K T) (p : PartyId) (v : S × S) :
    ltAt (ltSet p (some v) s) p = PMF.pure (v, ltSet p (some v) s) :=
  ltAt_of_some _ _ _ (by simp [ltSet])

/-- **A step that neither reads nor writes `lt p` commutes with its draw.** -/
theorem drawComm_of_free {γ : Type} (p : PartyId) (f : RStT S K T → PMF (γ × RStT S K T))
    (s : RStT S K T) (hf : ∀ v, f (ltSet p v s) = (f s).map fun y => (y.1, ltSet p v y.2))
    (hlt : ∀ y ∈ (f s).support, y.2.lt p = s.lt p) : DrawComm p f s := by
  unfold DrawComm
  cases h : s.lt p with
  | none =>
    rw [ltAt_of_none s p h, PMF.bind_map]
    simp only [Function.comp_def, hf]
    rw [PMF.bind_congr_support (f s) _ (fun y => (PMF.uniformFintype (S × S)).map
      fun l => (y.1, ltSet p (some l) y.2)) fun y hy => by
        rw [ltAt_of_none y.2 p ((hlt y hy).trans h), PMF.map_comp]; rfl]
    simp only [← PMF.bind_pure_comp]
    exact PMF.bind_comm _ _ _
  | some v =>
    rw [ltAt_of_some s p v h, PMF.pure_bind]
    conv_lhs => rw [← PMF.bind_pure (f s)]
    exact PMF.bind_congr_support _ _ _ fun y hy => by
      rw [ltAt_of_some y.2 p v ((hlt y hy).trans h), PMF.pure_map]

/-- **Composition**: a step followed by a step commutes with the draw. -/
theorem drawComm_bind {γ δ : Type} (p : PartyId) (F : RStT S K T → PMF (δ × RStT S K T))
    (f : RStT S K T → PMF (γ × RStT S K T))
    (g : γ → RStT S K T → PMF (δ × RStT S K T)) (s : RStT S K T)
    (hF : ∀ s, F s = (f s).bind fun y => g y.1 y.2) (hf : DrawComm p f s)
    (hg : ∀ y ∈ (f s).support, DrawComm p (g y.1) y.2) : DrawComm p F s := by
  unfold DrawComm at *
  simp only [hF]
  rw [← PMF.bind_bind, hf, PMF.bind_bind, PMF.bind_bind]
  refine PMF.bind_congr_support _ _ _ fun y hy => ?_
  rw [PMF.bind_map]
  exact hg y hy

/-- A step that agrees with a step that commutes with the draw, at `s` and at the states after
the draw, commutes with the draw. -/
theorem drawComm_congr {γ : Type} (p : PartyId) (f f' : RStT S K T → PMF (γ × RStT S K T))
    (s : RStT S K T) (h₀ : f s = f' s) (h₁ : ∀ v, f (ltSet p (some v) s) = f' (ltSet p (some v) s))
    (h : DrawComm p f' s) : DrawComm p f s := by
  unfold DrawComm at *
  rw [h₀, ← h]
  exact PMF.bind_congr_support _ _ _ fun l hl => by rw [ltAt_support_eq s p l hl, h₁]

/-- The draw of `lt q` commutes with the draw of `lt p`. -/
theorem drawComm_ltAt (p q : PartyId) (s : RStT S K T) : DrawComm p (fun s => ltAt s q) s := by
  by_cases hq : q = p
  · subst hq
    unfold DrawComm
    refine PMF.bind_congr_support _ _ _ fun l hl => ?_
    dsimp only
    rw [ltAt_support_eq s q l hl, ltAt_ltSet_some, PMF.pure_map]
  · refine drawComm_of_free p _ s (fun v => ?_) (fun y hy => ?_)
    · have h' : (ltSet p v s).lt q = s.lt q := by simp [ltSet, Function.update_of_ne hq]
      cases h : s.lt q with
      | some l => rw [ltAt_of_some _ _ l (h'.trans h), ltAt_of_some _ _ l h, PMF.pure_map]
      | none =>
        rw [ltAt_of_none _ _ (h'.trans h), ltAt_of_none _ _ h, PMF.map_comp]
        congr 1
        funext l
        simp only [Function.comp_apply, ltSet, Function.update_comm (Ne.symm hq)]
    · rw [ltAt_support_eq s q y hy]
      simp [ltSet, Function.update_of_ne (Ne.symm hq)]

/-- A step that keeps the state commutes with the draw. -/
theorem drawComm_pure {γ : Type} (p : PartyId) (o : γ) (s : RStT S K T) :
    DrawComm p (fun s => PMF.pure (o, s)) s :=
  drawComm_of_free p _ s (fun v => by rw [PMF.pure_map]) (fun y hy => by
    rw [PMF.mem_support_pure_iff] at hy
    rw [hy])

/-- A step followed by a map of its answer commutes with the draw. -/
theorem drawComm_map {γ δ : Type} (p : PartyId) (F : RStT S K T → PMF (δ × RStT S K T))
    (f : RStT S K T → PMF (γ × RStT S K T)) (φ : γ → δ) (s : RStT S K T)
    (hF : ∀ s, F s = (f s).map fun y => (φ y.1, y.2)) (hf : DrawComm p f s) :
    DrawComm p F s := by
  unfold DrawComm at *
  simp only [hF]
  rw [← PMF.map_bind, hf, PMF.map_bind, PMF.bind_map]
  refine congrArg _ (funext fun y => ?_)
  simp only [Function.comp_apply, PMF.map_comp, Function.comp_def]

omit [Fintype S] [Nonempty S] in
/-- Unfolding lemma of `ltSet`: the session records are kept. -/
@[simp] theorem ltSet_st (p : PartyId) (v : Option (S × S)) (s : RStT S K T) :
    (ltSet p v s).st = s.st := rfl

omit [Fintype S] [Nonempty S] in
/-- Unfolding lemma of `ltSet`: the session secrets are kept. -/
@[simp] theorem ltSet_eph (p : PartyId) (v : Option (S × S)) (s : RStT S K T) :
    (ltSet p v s).eph = s.eph := rfl

omit [Fintype S] [Nonempty S] in
/-- Unfolding lemma of `ltSet`: the key-derivation state is kept. -/
@[simp] theorem ltSet_ro (p : PartyId) (v : Option (S × S)) (s : RStT S K T) :
    (ltSet p v s).ro = s.ro := rfl

omit [Fintype S] [Nonempty S] in
/-- Unfolding lemma of `ltSet` under `opkOf`: the one-time prekeys are kept. -/
@[simp] theorem opkOf_ltSet (p : PartyId) (v : Option (S × S)) (s : RStT S K T)
    (sid : SessionId) (b : PartyId) : opkOf (ltSet p v s) sid b = opkOf s sid b := rfl

end DrawLt

section Steps

variable {S W K : Type} [Fintype S] [Nonempty S] [DecidableEq W] [Fintype K] [Nonempty K]

/-- The key derivation of a session, keyed into the state, commutes with the draw of `lt p`. -/
theorem drawComm_roKeyed (p : PartyId) (i : Inp W) (o : ROut S W K) (x : Inst) (r : Rec K)
    (s : RSt S W K) :
    DrawComm p (fun s => (roAt s.ro i).map fun q => (o, keyed s x r q.1 q.2)) s := by
  refine drawComm_of_free p _ s (fun v => ?_) (fun y hy => ?_)
  · rw [PMF.map_comp]
    congr 1
  · simp only [PMF.support_map, Set.mem_image] at hy
    obtain ⟨q, -, rfl⟩ := hy
    rfl

/-- **The key derivation of a session after the draws of two parties** commutes with the draw of
`lt p`: the shape of the completions of an initiator and of a responder. -/
theorem drawComm_twoDraws (p a b : PartyId) (I : S × S → S × S → Inp W) (o : ROut S W K)
    (x : Inst) (r : Rec K) (s : RSt S W K) :
    DrawComm p (fun s => (ltAt s a).bind fun la => (ltAt la.2 b).bind fun lb =>
      (roAt lb.2.ro (I la.1 lb.1)).map fun q => (o, keyed lb.2 x r q.1 q.2)) s := by
  refine drawComm_bind p _ (fun s => ltAt s a) (fun la s => (ltAt s b).bind fun lb =>
    (roAt lb.2.ro (I la lb.1)).map fun q => (o, keyed lb.2 x r q.1 q.2)) s ?_
    (drawComm_ltAt p a s) ?_
  · intro _
    rfl
  intro la _
  refine drawComm_bind p _ (fun s => ltAt s b) (fun lb s =>
    (roAt s.ro (I la.1 lb)).map fun q => (o, keyed s x r q.1 q.2)) la.2 ?_
    (drawComm_ltAt p b la.2) ?_
  · intro _
    rfl
  intro lb _
  exact drawComm_roKeyed p _ o x r lb.2

/-- The completion with a delivered prekey commutes with the draw of `lt p`. -/
theorem completeSig_drawComm (A : AKEAlg S W) (p : PartyId) (x : Inst) (spk : W)
    (s : RSt S W K) : DrawComm p (fun s => completeSig A s x spk) s := by
  rcases hr : s.st.recs x with _ | r
  · exact drawComm_congr p _ _ s (by simp [completeSig, hr]) (fun v => by simp [completeSig, hr])
      (drawComm_pure p .ack s)
  rcases he : s.eph x with _ | ek
  · exact drawComm_congr p _ _ s (by simp [completeSig, hr, he])
      (fun v => by simp [completeSig, hr, he]) (drawComm_pure p .ack s)
  rcases ho : opkOf s x.1 r.peer with _ | opk
  · exact drawComm_congr p _ _ s (by simp [completeSig, hr, he, ho])
      (fun v => by simp [completeSig, hr, he, ho]) (drawComm_pure p .ack s)
  by_cases hc : r.role = .initiator ∧ r.key.isNone
  · exact drawComm_congr p _ _ s (by simp only [completeSig, hr, he, ho, hc, and_self,
        ↓reduceIte])
      (fun v => by simp only [completeSig, ltSet_st, ltSet_eph, opkOf_ltSet, hr, he, ho, hc,
        and_self, ↓reduceIte])
      (drawComm_twoDraws p x.2 r.peer
        (fun la lb => A.initInp x.1 x.2 r.peer la.1 ek (A.pub lb.1) spk (A.pub opk)) .ack x r s)
  · exact drawComm_congr p _ _ s (by simp only [completeSig, hr, he, ho, hc, ↓reduceIte])
      (fun v => by simp only [completeSig, ltSet_st, ltSet_eph, opkOf_ltSet, hr, he, ho, hc,
        ↓reduceIte]) (drawComm_pure p .ack s)

/-- The completion of an initiator commutes with the draw of `lt p`. -/
theorem completeStep_drawComm (A : AKEAlg S W) (p : PartyId) (x : Inst) (s : RSt S W K) :
    DrawComm p (fun s => completeStepK lazyKDF A s x) s := by
  rcases hr : s.st.recs x with _ | r
  · exact drawComm_congr p _ _ s (by simp [completeStepK, hr])
      (fun v => by simp [completeStepK, hr]) (drawComm_pure p .ack s)
  rcases he : s.eph x with _ | ek
  · exact drawComm_congr p _ _ s (by simp [completeStepK, hr, he])
      (fun v => by simp [completeStepK, hr, he]) (drawComm_pure p .ack s)
  rcases ho : opkOf s x.1 r.peer with _ | opk
  · exact drawComm_congr p _ _ s (by simp [completeStepK, hr, he, ho])
      (fun v => by simp [completeStepK, hr, he, ho]) (drawComm_pure p .ack s)
  by_cases hc : r.role = .initiator ∧ r.key.isNone
  · exact drawComm_congr p _ _ s (by simp only [completeStepK, lazyKDF, hr, he, ho, hc,
        and_self, ↓reduceIte])
      (fun v => by simp only [completeStepK, lazyKDF, ltSet_st, ltSet_eph, opkOf_ltSet, hr, he,
        ho, hc, and_self, ↓reduceIte])
      (drawComm_twoDraws p x.2 r.peer
        (fun la lb => A.initInp x.1 x.2 r.peer la.1 ek (A.pub lb.1) (A.pub lb.2) (A.pub opk))
        .ack x r s)
  · exact drawComm_congr p _ _ s (by simp only [completeStepK, hr, he, ho, hc, ↓reduceIte])
      (fun v => by simp only [completeStepK, ltSet_st, ltSet_eph, opkOf_ltSet, hr, he, ho, hc,
        ↓reduceIte]) (drawComm_pure p .ack s)

/-- The completion of a responder commutes with the draw of `lt p`. -/
theorem sendStep_drawComm (A : AKEAlg S W) (p : PartyId) (x : Inst) (e : W) (s : RSt S W K) :
    DrawComm p (fun s => sendStepK lazyKDF A s x e) s := by
  rcases hr : s.st.recs x with _ | r
  · exact drawComm_congr p _ _ s (by simp [sendStepK, hr])
      (fun v => by simp [sendStepK, hr]) (drawComm_pure p .ack s)
  rcases he : s.eph x with _ | opk
  · exact drawComm_congr p _ _ s (by simp [sendStepK, hr, he])
      (fun v => by simp [sendStepK, hr, he]) (drawComm_pure p .ack s)
  by_cases hc : r.role = .responder ∧ r.key.isNone
  · exact drawComm_congr p _ _ s (by simp only [sendStepK, lazyKDF, hr, he, hc,
        and_self, ↓reduceIte])
      (fun v => by simp only [sendStepK, lazyKDF, ltSet_st, ltSet_eph, hr, he, hc, and_self,
        ↓reduceIte])
      (drawComm_twoDraws p x.2 r.peer
        (fun lb la => A.respInp x.1 r.peer x.2 (A.pub la.1) e lb.1 lb.2 opk) .ack x r s)
  · exact drawComm_congr p _ _ s (by simp only [sendStepK, hr, he, hc, ↓reduceIte])
      (fun v => by simp only [sendStepK, ltSet_st, ltSet_eph, hr, he, hc, ↓reduceIte])
      (drawComm_pure p .ack s)

omit [DecidableEq W] [Fintype K] [Nonempty K] in
/-- The corruption of a party commutes with the draw of `lt p`. -/
theorem corruptRStep_drawComm (p pid : PartyId) (s : RSt S W K) :
    DrawComm p (fun s => (corruptRStep s pid : PMF (ROut S W K × RSt S W K))) s := by
  by_cases hn : Named s.st pid = true
  · exact drawComm_congr p _ _ s (by simp [corruptRStep, hn])
      (fun v => by simp [corruptRStep, hn]) (drawComm_pure p (.secret none) s)
  · refine drawComm_congr p _ _ s (by simp only [corruptRStep, hn]; rfl)
      (fun v => by simp only [corruptRStep, ltSet_st, hn]) ?_
    refine drawComm_bind p _ (fun s => ltAt s pid) (fun l s =>
      PMF.pure ((ROut.secret (some l) : ROut S W K), { s with st := corruptStep s.st pid }))
      s ?_ (drawComm_ltAt p pid s) ?_
    · intro s'
      rw [← PMF.bind_pure_comp]
      rfl
    · intro l _
      refine drawComm_of_free p _ l.2 (fun v => ?_) (fun y hy => ?_)
      · rw [PMF.pure_map]
        rfl
      · rw [PMF.mem_support_pure_iff] at hy
        rw [hy]

/-- **A step of the real X3DH state machine commutes with the draw of `lt p`.** -/
theorem realStep_drawComm (A : AKEAlg S W) (p : PartyId) (g : OEv W) (s : RSt S W K) :
    DrawComm p (fun s => realStep A s g) s := by
  rcases g with ((⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) |
    (_ | _ | pid | ⟨sid, pid⟩ | pid | ⟨sid, pid⟩ | ⟨sid, pid, e⟩ | x))
  · refine drawComm_of_free p _ s (fun v => ?_) (fun y hy => ?_)
    · simp only [realStep, realGame, realGameK, realHonK, lazyKDF, ltSet_st]
      by_cases h : (s.st.recs (sid, pid)).isNone = true
      · simp only [h, ↓reduceIte, PMF.map_bind, PMF.pure_map]
        rfl
      · simp only [h, Bool.false_eq_true, ↓reduceIte, PMF.pure_map]
    · simp only [realStep, realGame, realGameK, realHonK, lazyKDF] at hy
      split_ifs at hy
      · simp only [PMF.map_bind, PMF.pure_map, PMF.support_bind, PMF.support_pure,
          Set.mem_iUnion, Set.mem_singleton_iff] at hy
        obtain ⟨_, -, rfl⟩ := hy
        rfl
      · simp only [PMF.pure_map, PMF.support_pure, Set.mem_singleton_iff] at hy
        rw [hy]
  · refine drawComm_of_free p _ s (fun v => ?_) (fun y hy => ?_)
    · simp only [realStep, realGame, realGameK, realHonK, PMF.pure_map]
      rfl
    · simp only [realStep, realGame, realGameK, realHonK, PMF.pure_map, PMF.support_pure,
        Set.mem_singleton_iff] at hy
      rw [hy]
  · refine drawComm_of_free p _ s (fun v => ?_) (fun y hy => ?_)
    · simp only [realStep, realGame, realGameK, realAdvK, PMF.pure_map]
    · simp only [realStep, realGame, realGameK, realAdvK, PMF.pure_map, PMF.support_pure,
        Set.mem_singleton_iff] at hy
      rw [hy]
  · refine drawComm_of_free p _ s (fun v => ?_) (fun y hy => ?_)
    · simp only [realStep, realGame, realGameK, realAdvK, PMF.pure_map]
      rfl
    · simp only [realStep, realGame, realGameK, realAdvK, PMF.pure_map, PMF.support_pure,
        Set.mem_singleton_iff] at hy
      rw [hy]
  · refine drawComm_map p _ (fun s => ltAt s pid)
      (fun l => (Sum.inr (ROut.pub (A.pub l.1) (A.pub l.2)) : OOut S W K)) s ?_
      (drawComm_ltAt p pid s)
    intro s'
    rw [realStep_pub]
  · refine drawComm_of_free p _ s (fun v => ?_) (fun y hy => ?_)
    · simp only [realStep, realGame, realGameK, realAdvK, PMF.pure_map]
      rfl
    · simp only [realStep, realGame, realGameK, realAdvK, PMF.pure_map, PMF.support_pure,
        Set.mem_singleton_iff] at hy
      rw [hy]
  · refine drawComm_map p _ (fun s => corruptRStep s pid) (fun o => (Sum.inr o : OOut S W K))
      s ?_ (corruptRStep_drawComm p pid s)
    intro s'
    rfl
  · refine drawComm_map p _ (fun s => completeStepK lazyKDF A s (sid, pid))
      (fun o => (Sum.inr o : OOut S W K)) s ?_ (completeStep_drawComm A p (sid, pid) s)
    intro s'
    rfl
  · refine drawComm_map p _ (fun s => sendStepK lazyKDF A s (sid, pid) e)
      (fun o => (Sum.inr o : OOut S W K)) s ?_ (sendStep_drawComm A p (sid, pid) e s)
    intro s'
    rfl
  · refine drawComm_of_free p _ s (fun v => ?_) (fun y hy => ?_)
    · simp only [realStep, realGame, realGameK, realAdvK, lazyKDF, PMF.map_comp]
      rfl
    · simp only [realStep, realGame, realGameK, realAdvK, lazyKDF, PMF.map_comp,
        PMF.support_map, Set.mem_image] at hy
      obtain ⟨_, -, rfl⟩ := hy
      rfl

end Steps

/-! ## The draw on the states of a layer over the real state machine -/

section Pair

variable {S K T L : Type} [Fintype S] [Nonempty S]

/-- **The draw of `lt p` on the states of a layer over the real state machine**: the draw on
the state machine, the state of the layer kept. -/
noncomputable def drawP (p : PartyId) (t : L × RStT S K T) : PMF ((S × S) × (L × RStT S K T)) :=
  (ltAt t.2 p).map fun l => (l.1, (t.1, l.2))

/-- **A layered step commutes with the draw of `lt p`.** The step is a draw `M` of the layer, a
step `f a` of the state machine, a draw `N` of the layer, a second step `g` of the state
machine, and a new layer state; when both steps of the state machine commute with the draw, the
layered step does. -/
theorem drawP_comm {α γ ρ δ ο : Type} (p : PartyId)
    (F : L × RStT S K T → PMF (ο × (L × RStT S K T))) (t : L × RStT S K T) (M : PMF α)
    (f : α → RStT S K T → PMF (γ × RStT S K T)) (N : α → γ → PMF ρ)
    (g : α → γ → ρ → RStT S K T → PMF (δ × RStT S K T)) (o : α → γ → ρ → δ → ο)
    (j : α → γ → ρ → L)
    (hF : ∀ s, F (t.1, s) = M.bind fun a => (f a s).bind fun y => (N a y.1).bind fun r =>
      (g a y.1 r y.2).map fun c => (o a y.1 r c.1, (j a y.1 r, c.2)))
    (hf : ∀ a ∈ M.support, DrawComm p (f a) t.2)
    (hg : ∀ a ∈ M.support, ∀ y ∈ (f a t.2).support, ∀ r, DrawComm p (g a y.1 r) y.2) :
    (drawP p t).bind (fun l => F l.2) =
      (F t).bind fun y => (drawP p y.2).map fun l => (y.1, l.2) := by
  obtain ⟨t₁, t₂⟩ := t
  simp only [drawP, PMF.bind_map, Function.comp_def, hF]
  rw [PMF.bind_comm]
  simp only [PMF.bind_bind]
  refine PMF.bind_congr_support _ _ _ fun a ha => ?_
  have hfa := hf a ha
  unfold DrawComm at hfa
  rw [← PMF.bind_bind, hfa, PMF.bind_bind]
  refine PMF.bind_congr_support _ _ _ fun y hy => ?_
  rw [PMF.bind_map]
  simp only [Function.comp_def]
  rw [PMF.bind_comm]
  refine congrArg _ (funext fun r => ?_)
  have hgr := hg a ha y hy r
  unfold DrawComm at hgr
  calc _ = PMF.map (fun c => (o a y.1 r c.1, (j a y.1 r, c.2)))
        ((ltAt y.2 p).bind fun l => g a y.1 r l.2) := (PMF.map_bind _ _ _).symm
    _ = _ := by
      rw [hgr, PMF.map_bind, PMF.bind_map]
      refine congrArg _ (funext fun c => ?_)
      simp only [Function.comp_apply, PMF.map_comp, Function.comp_def]

omit [Fintype S] [Nonempty S] in
/-- `ltSet` at the value already in place is the identity. -/
theorem ltSet_self (p : PartyId) (s : RStT S K T) : ltSet p (s.lt p) s = s := by
  simp [ltSet]

/-- After the draw on the states of a layer, the state is the state with `lt p` set. -/
theorem drawP_support_eq (p : PartyId) (t : L × RStT S K T) :
    ∀ l ∈ (drawP p t).support, l.2 = (t.1, ltSet p (some l.1) t.2) := by
  intro l hl
  simp only [drawP, PMF.support_map, Set.mem_image] at hl
  obtain ⟨l₀, hl₀, rfl⟩ := hl
  rw [ltAt_support_eq t.2 p l₀ hl₀]

/-- The draw on a state whose `lt p` is set to `v` is the point mass. -/
theorem drawP_of_some (p : PartyId) (t : L × RStT S K T) (v : S × S) (h : t.2.lt p = some v) :
    drawP p t = PMF.pure (v, t) := by
  simp only [drawP, ltAt_of_some t.2 p v h, PMF.pure_map]

/-- The draw on a state whose `lt p` is unset. -/
theorem drawP_of_none (p : PartyId) (t : L × RStT S K T) (h : t.2.lt p = none) :
    drawP p t = (PMF.uniformFintype (S × S)).map fun x => (x, (t.1, ltSet p (some x) t.2)) := by
  simp only [drawP, ltAt_of_none t.2 p h, PMF.map_comp]
  rfl

variable {E R α β : Type}

/-- **The long-term secrets of `p` drawn before the run, for the output and an observable.**
For an oracle on the states of a layer over the real state machine that commutes with the draw
of `lt p` and keeps a drawn `lt p`, a run from a state without `lt p` has the output, with an
observable of the final state that does not read `lt p`, of the run from the state with `lt p`
preset to a uniform pair. -/
theorem run_map_obs_eq_bind_ltSet (p : PartyId)
    (O : L × RStT S K T → E → PMF (R × (L × RStT S K T))) (g : L × RStT S K T → β)
    (hg : ∀ t v, g (t.1, ltSet p v t.2) = g t)
    (hcomm : ∀ t e, (drawP p t).bind (fun l => O l.2 e) =
      (O t e).bind fun y => (drawP p y.2).map fun l => (y.1, l.2))
    (hmono : ∀ t e, ∀ y ∈ (O t e).support, ∀ v, t.2.lt p = some v → y.2.2.lt p = some v)
    (B : OracleAdv E R α) (t : L × RStT S K T) (ht : t.2.lt p = none) :
    (OracleAdv.run O B t).map (fun y => (y.1, g y.2)) =
      (PMF.uniformFintype (S × S)).bind fun x =>
        (OracleAdv.run O B (t.1, ltSet p (some x) t.2)).map fun y => (y.1, g y.2) := by
  rw [OracleAdv.run_map_obs_eq_bind_draw (drawP p) O g ?_ ?_ ?_ hcomm B t, drawP_of_none p t ht,
    PMF.bind_map]
  · rfl
  · intro s l hl
    rw [drawP_support_eq p s l hl]
    exact hg s _
  · intro s l hl
    have h₁ : l.2.2.lt p = some l.1 := by rw [drawP_support_eq p s l hl]; simp [ltSet]
    exact drawP_of_some p _ l.1 h₁
  · intro s l hl d y hy
    have h₁ : l.2.2.lt p = some l.1 := by rw [drawP_support_eq p s l hl]; simp [ltSet]
    exact drawP_of_some p _ l.1 (hmono _ d y hy _ h₁)

/-- **The long-term secrets of `p` drawn before the run, for a bad flag.** The form of
`run_map_obs_eq_bind_ltSet` for the probability of a bad flag that does not read `lt p`. -/
theorem run_flag_eq_tsum_ltSet (p : PartyId)
    (O : L × RStT S K T → E → PMF (R × (L × RStT S K T)))
    (bad : L × RStT S K T → E → R × (L × RStT S K T) → Prop) [∀ s d y, Decidable (bad s d y)]
    (hbad : ∀ t e y v w, bad (t.1, ltSet p v t.2) e (y.1, (y.2.1, ltSet p w y.2.2)) ↔ bad t e y)
    (hcomm : ∀ t e, (drawP p t).bind (fun l => O l.2 e) =
      (O t e).bind fun y => (drawP p y.2).map fun l => (y.1, l.2))
    (hmono : ∀ t e, ∀ y ∈ (O t e).support, ∀ v, t.2.lt p = some v → y.2.2.lt p = some v)
    (B : OracleAdv E R α) (t : L × RStT S K T) (b : Bool) (ht : t.2.lt p = none) :
    (OracleAdv.run (OracleAdv.flagWhen bad O) B (t, b)).toOuterMeasure {y | y.2.2 = true} =
      ∑' x, PMF.uniformFintype (S × S) x *
        (OracleAdv.run (OracleAdv.flagWhen bad O) B ((t.1, ltSet p (some x) t.2), b)).toOuterMeasure
          {y | y.2.2 = true} := by
  rw [OracleAdv.run_flag_eq_bind_draw (drawP p) O bad ?_ ?_ ?_ ?_ hcomm B t b,
    ← PMF.toOuterMeasure_bind_apply, ← PMF.toOuterMeasure_bind_apply, drawP_of_none p t ht,
    PMF.bind_map]
  · rfl
  · intro s d y l hl
    rw [drawP_support_eq p s l hl]
    have h := hbad s d y (some l.1) (y.2.2.lt p)
    rwa [ltSet_self] at h
  · intro s d y l hl
    rw [drawP_support_eq p y.2 l hl]
    have h := hbad s d y (s.2.lt p) (some l.1)
    rwa [ltSet_self] at h
  · intro s l hl
    have h₁ : l.2.2.lt p = some l.1 := by rw [drawP_support_eq p s l hl]; simp [ltSet]
    exact drawP_of_some p _ l.1 h₁
  · intro s l hl d y hy
    have h₁ : l.2.2.lt p = some l.1 := by rw [drawP_support_eq p s l hl]; simp [ltSet]
    exact drawP_of_some p _ l.1 (hmono _ d y hy _ h₁)

end Pair

/-! ## The worlds of the joint-key model -/

section Joint

variable (P : FiatShamirROM.Sigma) [DecidableEq P.Stmt] [Fintype P.Wit] [Nonempty P.Wit]
  {K : Type} [Fintype K] [Nonempty K]

/-- The completion with a delivered prekey keeps the drawn long-term secrets. -/
theorem completeSig_lt_mono (A : AKEAlg P.Wit P.Stmt) (s : RSt P.Wit P.Stmt K) (x : Inst)
    (spk : P.Stmt) : ∀ y ∈ (completeSig A s x spk).support, ∀ q v, s.lt q = some v →
      y.2.lt q = some v := by
  intro y hy q v h
  unfold completeSig at hy
  repeat' split at hy
  all_goals first
    | (simp only [PMF.support_pure, Set.mem_singleton_iff] at hy; rw [hy]; exact h)
    | (simp only [PMF.support_bind, PMF.support_map, Set.mem_iUnion, Set.mem_image] at hy
       obtain ⟨la, hla, lb, hlb, k', -, rfl⟩ := hy
       exact (X3DHSquareSigned.ltAt_support _ _ lb hlb).2.2.2.2 _ _
         ((X3DHSquareSigned.ltAt_support _ _ la hla).2.2.2.2 _ _ h))

/-- A step of the filtered world keeps the drawn long-term secrets. -/
theorem filtJO_lt_mono (A : AKEAlg P.Wit P.Stmt) (t : JSt P × RSt P.Wit P.Stmt K) (e : JEv P) :
    ∀ y ∈ (filtJO P A t e).support, ∀ q v, t.2.lt q = some v → y.2.2.lt q = some v := by
  intro y hy q v h
  simp only [filtJO, X3DHSquareSigned.layO, PMF.support_bind, PMF.support_map, Set.mem_iUnion,
    Set.mem_image] at hy
  obtain ⟨a, -, z, hz, r, -, rfl⟩ := hy
  exact (X3DHSquareSigned.realO_support A t.2 a.2 z hz).2 q v h

/-- A step of the real protocol with the signature oracles `O` keeps the drawn long-term
secrets. -/
theorem jointOWith_lt_mono (O : SigOracles P) (A : AKEAlg P.Wit P.Stmt)
    (t : JSt P × RSt P.Wit P.Stmt K) (e : JEv P) :
    ∀ y ∈ (jointOWith P O A t e).support, ∀ q v, t.2.lt q = some v → y.2.2.lt q = some v := by
  intro y hy q v h
  rcases e with h' | a | (q' | ⟨q', k⟩ | ⟨sid, pid, spk, σ⟩)
  · rw [jointOWith_inl] at hy
    exact filtJO_lt_mono P A t _ y hy q v h
  · rw [jointOWith_inr_inl] at hy
    exact filtJO_lt_mono P A t _ y hy q v h
  · simp only [jointOWith, PMF.support_bind, PMF.support_map, Set.mem_iUnion,
      Set.mem_image] at hy
    obtain ⟨l, hl, r, -, rfl⟩ := hy
    exact (X3DHSquareSigned.ltAt_support _ _ l hl).2.2.2.2 _ _ h
  · simp only [jointOWith, PMF.support_bind, PMF.support_map, Set.mem_iUnion,
      Set.mem_image] at hy
    obtain ⟨l, hl, r, -, rfl⟩ := hy
    exact (X3DHSquareSigned.ltAt_support _ _ l hl).2.2.2.2 _ _ h
  · simp only [jointOWith] at hy
    split at hy
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at hy
      rw [hy]
      exact h
    · simp only [PMF.support_bind, Set.mem_iUnion] at hy
      obtain ⟨l, hl, r, -, hy⟩ := hy
      have hl' := (X3DHSquareSigned.ltAt_support _ _ l hl).2.2.2.2 _ _ h
      split at hy
      · simp only [PMF.support_map, Set.mem_image] at hy
        obtain ⟨c, hc, rfl⟩ := hy
        exact completeSig_lt_mono P A l.2 _ spk c hc q v hl'
      · simp only [PMF.support_pure, Set.mem_singleton_iff] at hy
        rw [hy]
        exact hl'

/-- **A step of the filtered world commutes with the draw of `lt p`.** -/
theorem filtJO_drawComm (A : AKEAlg P.Wit P.Stmt) (p : PartyId)
    (t : JSt P × RSt P.Wit P.Stmt K) (e : JEv P) :
    (drawP p t).bind (fun l => filtJO P A l.2 e) =
      (filtJO P A t e).bind fun y => (drawP p y.2).map fun l => (y.1, l.2) := by
  refine drawP_comm p (fun t => filtJO P A t e) t (jPre P t.1 e) (fun a s => realStep A s a.2)
    (fun a q => jPost P a.1 q) (fun _ _ _ s => PMF.pure ((), s)) (fun _ _ r _ => r.2)
    (fun _ _ r => r.1) ?_ (fun a _ => realStep_drawComm A p a.2 t.2)
    (fun _ _ y _ _ => drawComm_pure p () y.2)
  intro s
  simp only [filtJO, X3DHSquareSigned.layO, PMF.pure_map]
  rfl

/-- **A step of the real protocol with the signature oracles `O` commutes with the draw of
`lt p`.** -/
theorem jointOWith_drawComm (O : SigOracles P) (A : AKEAlg P.Wit P.Stmt) (p : PartyId)
    (t : JSt P × RSt P.Wit P.Stmt K) (e : JEv P) :
    (drawP p t).bind (fun l => jointOWith P O A l.2 e) =
      (jointOWith P O A t e).bind fun y => (drawP p y.2).map fun l => (y.1, l.2) := by
  rcases e with h' | a | (q | ⟨q, k⟩ | ⟨sid, pid, spk, σ⟩)
  · simp only [jointOWith_inl]
    exact filtJO_drawComm P A p t _
  · simp only [jointOWith_inr_inl]
    exact filtJO_drawComm P A p t _
  · refine drawP_comm p (fun t => jointOWith P O A t (.inr (.inr (.sigPub q)))) t (PMF.pure ())
      (fun _ s => ltAt s q)
      (fun _ lt => signAt P (O (A.pub lt.1, lt.1)) { t.1 with ph := .sign q } q (A.pub lt.1)
        (A.pub lt.2))
      (fun _ _ _ s => PMF.pure ((), s)) (fun _ _ r _ => (.inr (.inr r.2) : JOut P K))
      (fun _ _ r => r.1) ?_ (fun _ _ => drawComm_ltAt p q t.2)
      (fun _ _ y _ _ => drawComm_pure p () y.2)
    intro s
    simp only [jointOWith, PMF.pure_bind, PMF.pure_map]
    rfl
  · refine drawP_comm p (fun t => jointOWith P O A t (.inr (.inr (.sigHash q k)))) t
      (PMF.pure ()) (fun _ s => ltAt s q)
      (fun _ lt => hashAt P (fun s k => O (A.pub lt.1, lt.1) s (.inl k))
        { t.1 with ph := .hash q k } q k)
      (fun _ _ _ s => PMF.pure ((), s)) (fun _ _ r _ => (.inr (.inr (hashOut P r.1)) : JOut P K))
      (fun _ _ r => r.2) ?_ (fun _ _ => drawComm_ltAt p q t.2)
      (fun _ _ y _ _ => drawComm_pure p () y.2)
    intro s
    simp only [jointOWith, PMF.pure_bind, PMF.pure_map]
    rfl
  · rcases hq : t.1.peers (sid, pid) with _ | q
    · refine drawP_comm p (fun t => jointOWith P O A t (.inr (.inr (.inject sid pid spk σ)))) t
        (PMF.pure ()) (fun _ s => PMF.pure ((), s)) (fun _ _ => PMF.pure ())
        (fun _ _ _ s => PMF.pure ((), s)) (fun _ _ _ _ => (.inr (.inr .ack) : JOut P K))
        (fun _ _ _ => { t.1 with ph := .inj }) ?_ (fun _ _ => drawComm_pure p () t.2)
        (fun _ _ y _ _ => drawComm_pure p () y.2)
      intro s
      simp only [jointOWith, hq, PMF.pure_bind, PMF.pure_map]
    · refine drawP_comm p (fun t => jointOWith P O A t (.inr (.inr (.inject sid pid spk σ)))) t
        (PMF.pure ()) (fun _ s => ltAt s q)
        (fun _ lt => hashAt P (fun s k => O (A.pub lt.1, lt.1) s (.inl k)) { t.1 with ph := .inj }
          q (σ.1, spk))
        (fun _ lt r s => if verAns P (A.pub lt.1) σ r.1 then completeSig A s (sid, pid) spk
          else PMF.pure (.ack, s))
        (fun _ _ _ _ => (.inr (.inr .ack) : JOut P K)) (fun _ _ r => r.2) ?_
        (fun _ _ => drawComm_ltAt p q t.2) ?_
      · intro s
        simp only [jointOWith, hq, PMF.pure_bind]
        refine congrArg _ (funext fun lt => congrArg _ (funext fun r => ?_))
        split_ifs
        · rfl
        · rw [PMF.pure_map]
      · intro _ _ y _ r
        by_cases hv : verAns P (A.pub y.1.1) σ r.1 = true
        · exact drawComm_congr p _ _ y.2 (by simp only [hv, ↓reduceIte])
            (fun _ => by simp only [hv, ↓reduceIte])
            (completeSig_drawComm A p (sid, pid) spk y.2)
        · exact drawComm_congr p _ _ y.2 (by simp only [hv, Bool.false_eq_true, ↓reduceIte])
            (fun _ => by simp only [hv, Bool.false_eq_true, ↓reduceIte])
            (drawComm_pure p .ack y.2)

/-! ### The long-term secrets of a party preset -/

variable {α : Type}

/-- **The long-term secrets of `p` drawn before a run of the real protocol with the signature
oracles `O`.** From a state without `lt p`, the output of a run is the average over a uniform
pair of the output of the run from the state with `lt p` preset to the pair. -/
theorem jointOWith_run_eager (O : SigOracles P) (A : AKEAlg P.Wit P.Stmt) (p : PartyId)
    (B : OracleAdv (JEv P) (JOut P K) α) (t : JSt P × RSt P.Wit P.Stmt K)
    (ht : t.2.lt p = none) :
    (OracleAdv.run (jointOWith P O A) B t).map Prod.fst =
      (PMF.uniformFintype (P.Wit × P.Wit)).bind fun x =>
        (OracleAdv.run (jointOWith P O A) B (t.1, ltSet p (some x) t.2)).map Prod.fst := by
  have h := congrArg (PMF.map Prod.fst) (run_map_obs_eq_bind_ltSet p (jointOWith P O A)
    (fun _ => ()) (fun _ _ => rfl) (jointOWith_drawComm P O A p)
    (fun t e y hy v => jointOWith_lt_mono P O A t e y hy p v) B t ht)
  simpa only [PMF.map_comp, PMF.map_bind, Function.comp_def] using h

open Classical in
/-- **The long-term secrets of `p` drawn before a run of the real protocol with the signature
oracles `O`, for a bad flag.** From a state without `lt p`, the probability that the run sets
the flag of a bad event that does not read `lt p` is the average over a uniform pair of that
probability from the state with `lt p` preset to the pair. -/
theorem jointOWith_flag_eager (O : SigOracles P) (A : AKEAlg P.Wit P.Stmt) (p : PartyId)
    (bad : JSt P × RSt P.Wit P.Stmt K → JEv P → JOut P K × (JSt P × RSt P.Wit P.Stmt K) → Prop)
    (hbad : ∀ t e y v w, bad (t.1, ltSet p v t.2) e (y.1, (y.2.1, ltSet p w y.2.2)) ↔ bad t e y)
    (B : OracleAdv (JEv P) (JOut P K) α) (t : JSt P × RSt P.Wit P.Stmt K) (b : Bool)
    (ht : t.2.lt p = none) :
    (OracleAdv.run (OracleAdv.flagWhen bad (jointOWith P O A)) B (t, b)).toOuterMeasure
        {y | y.2.2 = true} =
      ∑' x, PMF.uniformFintype (P.Wit × P.Wit) x *
        (OracleAdv.run (OracleAdv.flagWhen bad (jointOWith P O A)) B
          ((t.1, ltSet p (some x) t.2), b)).toOuterMeasure {y | y.2.2 = true} :=
  run_flag_eq_tsum_ltSet p (jointOWith P O A) bad hbad (jointOWith_drawComm P O A p)
    (fun t e y hy v => jointOWith_lt_mono P O A t e y hy p v) B t b ht

/-- `jointOWith_run_eager` for the real protocol `jointO`. -/
theorem jointO_run_eager (A : AKEAlg P.Wit P.Stmt) (p : PartyId)
    (B : OracleAdv (JEv P) (JOut P K) α) (t : JSt P × RSt P.Wit P.Stmt K)
    (ht : t.2.lt p = none) :
    (OracleAdv.run (jointO P A) B t).map Prod.fst =
      (PMF.uniformFintype (P.Wit × P.Wit)).bind fun x =>
        (OracleAdv.run (jointO P A) B (t.1, ltSet p (some x) t.2)).map Prod.fst :=
  jointOWith_run_eager P _ A p B t ht

open Classical in
/-- `jointOWith_flag_eager` for the real protocol `jointO`. -/
theorem jointO_flag_eager (A : AKEAlg P.Wit P.Stmt) (p : PartyId)
    (bad : JSt P × RSt P.Wit P.Stmt K → JEv P → JOut P K × (JSt P × RSt P.Wit P.Stmt K) → Prop)
    (hbad : ∀ t e y v w, bad (t.1, ltSet p v t.2) e (y.1, (y.2.1, ltSet p w y.2.2)) ↔ bad t e y)
    (B : OracleAdv (JEv P) (JOut P K) α) (t : JSt P × RSt P.Wit P.Stmt K) (b : Bool)
    (ht : t.2.lt p = none) :
    (OracleAdv.run (OracleAdv.flagWhen bad (jointO P A)) B (t, b)).toOuterMeasure
        {y | y.2.2 = true} =
      ∑' x, PMF.uniformFintype (P.Wit × P.Wit) x *
        (OracleAdv.run (OracleAdv.flagWhen bad (jointO P A)) B
          ((t.1, ltSet p (some x) t.2), b)).toOuterMeasure {y | y.2.2 = true} :=
  jointOWith_flag_eager P _ A p bad hbad B t b ht

/-- `jointOWith_run_eager` for the real protocol with simulated signatures `simSignO`. -/
theorem simSignO_run_eager (A : AKEAlg P.Wit P.Stmt) (p : PartyId)
    (B : OracleAdv (JEv P) (JOut P K) α) (t : JSt P × RSt P.Wit P.Stmt K)
    (ht : t.2.lt p = none) :
    (OracleAdv.run (simSignO P A) B t).map Prod.fst =
      (PMF.uniformFintype (P.Wit × P.Wit)).bind fun x =>
        (OracleAdv.run (simSignO P A) B (t.1, ltSet p (some x) t.2)).map Prod.fst :=
  jointOWith_run_eager P _ A p B t ht

open Classical in
/-- `jointOWith_flag_eager` for the real protocol with simulated signatures `simSignO`. -/
theorem simSignO_flag_eager (A : AKEAlg P.Wit P.Stmt) (p : PartyId)
    (bad : JSt P × RSt P.Wit P.Stmt K → JEv P → JOut P K × (JSt P × RSt P.Wit P.Stmt K) → Prop)
    (hbad : ∀ t e y v w, bad (t.1, ltSet p v t.2) e (y.1, (y.2.1, ltSet p w y.2.2)) ↔ bad t e y)
    (B : OracleAdv (JEv P) (JOut P K) α) (t : JSt P × RSt P.Wit P.Stmt K) (b : Bool)
    (ht : t.2.lt p = none) :
    (OracleAdv.run (OracleAdv.flagWhen bad (simSignO P A)) B (t, b)).toOuterMeasure
        {y | y.2.2 = true} =
      ∑' x, PMF.uniformFintype (P.Wit × P.Wit) x *
        (OracleAdv.run (OracleAdv.flagWhen bad (simSignO P A)) B
          ((t.1, ltSet p (some x) t.2), b)).toOuterMeasure {y | y.2.2 = true} :=
  jointOWith_flag_eager P _ A p bad hbad B t b ht

/-- **The long-term secrets of `p` drawn before a run of the filtered world.** -/
theorem filtJO_run_eager (A : AKEAlg P.Wit P.Stmt) (p : PartyId)
    (B : OracleAdv (JEv P) (JOut P K) α) (t : JSt P × RSt P.Wit P.Stmt K)
    (ht : t.2.lt p = none) :
    (OracleAdv.run (filtJO P A) B t).map Prod.fst =
      (PMF.uniformFintype (P.Wit × P.Wit)).bind fun x =>
        (OracleAdv.run (filtJO P A) B (t.1, ltSet p (some x) t.2)).map Prod.fst := by
  have h := congrArg (PMF.map Prod.fst) (run_map_obs_eq_bind_ltSet p (filtJO P A)
    (fun _ => ()) (fun _ _ => rfl) (filtJO_drawComm P A p)
    (fun t e y hy v => filtJO_lt_mono P A t e y hy p v) B t ht)
  simpa only [PMF.map_comp, PMF.map_bind, Function.comp_def] using h

open Classical in
/-- **The long-term secrets of `p` drawn before a run of the filtered world, for a bad
flag.** -/
theorem filtJO_flag_eager (A : AKEAlg P.Wit P.Stmt) (p : PartyId)
    (bad : JSt P × RSt P.Wit P.Stmt K → JEv P → JOut P K × (JSt P × RSt P.Wit P.Stmt K) → Prop)
    (hbad : ∀ t e y v w, bad (t.1, ltSet p v t.2) e (y.1, (y.2.1, ltSet p w y.2.2)) ↔ bad t e y)
    (B : OracleAdv (JEv P) (JOut P K) α) (t : JSt P × RSt P.Wit P.Stmt K) (b : Bool)
    (ht : t.2.lt p = none) :
    (OracleAdv.run (OracleAdv.flagWhen bad (filtJO P A)) B (t, b)).toOuterMeasure
        {y | y.2.2 = true} =
      ∑' x, PMF.uniformFintype (P.Wit × P.Wit) x *
        (OracleAdv.run (OracleAdv.flagWhen bad (filtJO P A)) B
          ((t.1, ltSet p (some x) t.2), b)).toOuterMeasure {y | y.2.2 = true} :=
  run_flag_eq_tsum_ltSet p (filtJO P A) bad hbad (filtJO_drawComm P A p)
    (fun t e y hy v => filtJO_lt_mono P A t e y hy p v) B t b ht

end Joint

end CatCrypt.Crypto.AKE.X3DHSquare

/-! ## The world of the gap Diffie–Hellman reduction at preset long-term secrets -/

namespace CatCrypt.Crypto.AKE.X3DHSquareGDH

open CatCrypt.Core CatCrypt.Crypto CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.PAKE.DHExtract
open CatCrypt.Crypto.AKE.X3DHSquare

variable {S W K : Type} [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K]
  [Inhabited K] (G : DHGroup S W) (a b : PartyId) (x y : S)

omit [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- **The coupling of the worlds at the initial states with `lt p` preset**: the world of the
reduction with `lt p = (0, s)` and the simulated world with `lt p` the shifted pair
`sh a b x y p (0, s)`. -/
theorem relW_preset (p : PartyId) (s : S) :
    RelW G a b x y
      ((ltSet p (some (sh a b x y p (0, s))) (rInit : RSt S W K), fun _ => none, .fwd), initSt)
      ((ltSet p (some (0, s)) (rInitR (S := S) (W := W) (K := K)).1.1, fun _ => none, .fwd),
        initSt) := by
  refine ⟨⟨rfl, rfl, fun q => ?_, rfl, fun _ => rfl, rfl, (fun _ h => by cases h),
    (fun _ _ h => by cases h), (fun _ h => by cases h), (fun _ _ h => by cases h), rfl, rfl⟩, rfl⟩
  by_cases hq : q = p
  · subst hq
    simp [ltSet]
  · simp [ltSet, Function.update_of_ne hq, rInit, rInitR]

omit [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- **The identity key of `a` in the reduction at `lt a = (0, s)` is the challenge `X`.** -/
theorem keyA_preset (X : W) (s : S) (rs : RSt S (W ⊕ W) K) :
    keyA G a X (ltSet a (some (0, s)) rs) = X := by
  simp [keyA, off1, ltSet]

omit [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- The public identity key of `a` in the reduction at the pair `(0, s)` is the challenge
`X`. -/
theorem pubIK_zero (X : W) (s : S) : pubIK G a X a (0, s) = X := by
  simp [pubIK]

end CatCrypt.Crypto.AKE.X3DHSquareGDH
