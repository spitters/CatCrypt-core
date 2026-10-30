/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCLoopbackTrace
public import CatCryptCore.Prob.SDistrChain

/-!
# The unbounded loopback

The activation `Sys.fbRunFail S n g t` of the loopback of `S` with fuel `n` is `Sys.fbRun` with
failure in place of the cut-off map: a wire value answered to the last allowed call ends the
activation with `SPComp.fail`. The runs are monotone in the fuel in the order of `SPComp`
(`Sys.fbRunFail_mono`), and their supremum is the unbounded activation `Sys.fbRunω S g t`. The
unbounded loopback `Sys.loopbackω S` is the system on the outer ports whose step is `fbRunω` from
the outer event; an activation that never exits loses its mass.

## Main definitions

* `Sys.fbRunFail S n g t`: the activation with fuel `n`, failing when the fuel is exhausted.
* `Sys.fbRunω S g t`: the supremum over the fuel of `fbRunFail`.
* `Sys.loopbackω S`: the unbounded loopback of `S` along its wire.

## Main results

* `Sys.fbRunFail_mono`: `fbRunFail` is monotone in the fuel.
* `Sys.fbRunω_eq`: one step of `S` followed by `fbRunω` on a wire value (unfolding equation).
* `Sys.loopbackω_stepMap_on`: a step map on an invariant gives a step map of the unbounded
  loopbacks.
* `Sys.loopback_stepMap_loopbackω`: when the fuel `k` is adequate on an invariant, the loopback
  with fuel `n ≥ k` and any cut-off map is step-equivalent to the unbounded loopback.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Core.SPComp

open CatCrypt.Prob

/-- The failed computation is the least element of `SPComp α`. -/
theorem fail_le {α : Type} (c : SPComp α) : SPComp.fail ≤ c := fun h a => by
  simp [SPComp.fail, SDistr.fail_apply_some]

end CatCrypt.Core.SPComp

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open OmegaCompletePartialOrder
open scoped ENNReal

/-- A possible outcome of the supremum of a chain is a possible outcome of one of its
elements. -/
theorem exists_isOutcome_of_isOutcome_ωSup {α : Type} {c : Chain (SPComp α)} {a : α}
    (h : IsOutcome (ωSup c) a) : ∃ n, IsOutcome (c n) a := by
  obtain ⟨hp, hp', h⟩ := h
  rw [SPComp.ωSup_apply, SDistr.ωSup_apply_some] at h
  by_contra hn
  push Not at hn
  exact h (ENNReal.iSup_eq_zero.mpr fun n => by
    have := hn n
    simp only [IsOutcome, not_exists, not_not] at this
    exact this hp hp')

namespace Sys

variable {τ υ E O X : Type}

/-! ## Activations failing on exhausted fuel -/

/-- The activation of the loopback of `S` from the event `g` in the state `t` with `n` further
calls allowed, failing when a wire value is answered to the last allowed call. -/
noncomputable def fbRunFail (S : Sys τ (E ⊕ X) (O ⊕ X)) : ℕ → E ⊕ X → τ → SPComp (τ × O)
  | 0, g, t => SPComp.bind (S.step t g) fun q =>
      Sum.elim (fun o => SPComp.pure (q.1, o)) (fun _ => SPComp.fail) q.2
  | n + 1, g, t => SPComp.bind (S.step t g) fun q =>
      Sum.elim (fun o => SPComp.pure (q.1, o)) (fun x => fbRunFail S n (.inr x) q.1) q.2

/-- `fbRunFail` grows with one more call allowed. -/
theorem fbRunFail_le_succ (S : Sys τ (E ⊕ X) (O ⊕ X)) :
    ∀ (n : ℕ) (g : E ⊕ X) (t : τ), S.fbRunFail n g t ≤ S.fbRunFail (n + 1) g t := by
  intro n
  induction n with
  | zero =>
    intro g t
    refine SPComp.bind_mono_right _ fun q => ?_
    rcases q with ⟨t', o | x⟩
    · exact le_rfl
    · exact SPComp.fail_le _
  | succ n ih =>
    intro g t
    refine SPComp.bind_mono_right _ fun q => ?_
    rcases q with ⟨t', o | x⟩
    · exact le_rfl
    · exact ih _ _

/-- `fbRunFail` is monotone in the fuel. -/
theorem fbRunFail_mono (S : Sys τ (E ⊕ X) (O ⊕ X)) (g : E ⊕ X) (t : τ) :
    Monotone fun n => S.fbRunFail n g t :=
  monotone_nat_of_le_succ fun n => S.fbRunFail_le_succ n g t

/-- The chain of activations failing on exhausted fuel. -/
noncomputable def fbChain (S : Sys τ (E ⊕ X) (O ⊕ X)) (g : E ⊕ X) (t : τ) :
    Chain (SPComp (τ × O)) :=
  ⟨fun n => S.fbRunFail n g t, S.fbRunFail_mono g t⟩

/-- The unbounded activation of the loopback of `S` from the event `g` in the state `t`: the
supremum over the fuel of `fbRunFail`. -/
noncomputable def fbRunω (S : Sys τ (E ⊕ X) (O ⊕ X)) (g : E ⊕ X) (t : τ) : SPComp (τ × O) :=
  ωSup (S.fbChain g t)

/-- The unbounded loopback of `S` along its wire `X`: an outer event `e` runs `fbRunω` from the
event `inl e`. -/
noncomputable def loopbackω (S : Sys τ (E ⊕ X) (O ⊕ X)) : Sys τ E O where
  init := S.init
  step t e := S.fbRunω (.inl e) t

/-- Unfolding lemma of `loopbackω`: a step. -/
theorem loopbackω_step (S : Sys τ (E ⊕ X) (O ⊕ X)) (t : τ) (e : E) :
    S.loopbackω.step t e = S.fbRunω (.inl e) t :=
  rfl

/-! ## The unfolding equation -/

/-- **Unfolding equation.** The unbounded activation is one step of `S`, followed on an output
`inl o` by the end of the activation and on an output `inr x` by the unbounded activation from
the event `inr x`. -/
theorem fbRunω_eq (S : Sys τ (E ⊕ X) (O ⊕ X)) (g : E ⊕ X) (t : τ) :
    S.fbRunω g t = SPComp.bind (S.step t g) fun q =>
      Sum.elim (fun o => SPComp.pure (q.1, o)) (fun x => S.fbRunω (.inr x) q.1) q.2 := by
  -- the chain of continuations whose binds are the activations with one more call
  let K : Chain (τ × (O ⊕ X) → SPComp (τ × O)) :=
    ⟨fun n q => Sum.elim (fun o => SPComp.pure (q.1, o))
      (fun x => S.fbRunFail n (.inr x) q.1) q.2, fun m n hmn q => by
        rcases q with ⟨t', o | x⟩
        · exact le_rfl
        · exact S.fbRunFail_mono _ _ hmn⟩
  have hK : (fun q : τ × (O ⊕ X) => Sum.elim (fun o => SPComp.pure (q.1, o))
      (fun x => S.fbRunω (.inr x) q.1) q.2) = ωSup K := by
    funext q
    rw [(ωScottContinuous.apply (β := fun _ => SPComp (τ × O)) q).map_ωSup K]
    rcases q with ⟨t', o | x⟩
    · exact le_antisymm (le_ωSup_of_le 0 le_rfl) (ωSup_le _ _ fun _ => le_rfl)
    · rfl
  apply le_antisymm
  · refine ωSup_le _ _ fun n => ?_
    cases n with
    | zero =>
      change S.fbRunFail 0 g t ≤ _
      rw [fbRunFail]
      refine SPComp.bind_mono_right _ fun q => ?_
      rcases q with ⟨t', o | x⟩
      · exact le_rfl
      · exact SPComp.fail_le _
    | succ n =>
      change S.fbRunFail (n + 1) g t ≤ _
      rw [fbRunFail]
      refine SPComp.bind_mono_right _ fun q => ?_
      rcases q with ⟨t', o | x⟩
      · exact le_rfl
      · exact le_ωSup (S.fbChain (.inr x) t') n
  · rw [hK, (SPComp.ωScottContinuous_bind_right (S.step t g)).map_ωSup K]
    exact ωSup_le _ _ fun n => le_ωSup (S.fbChain g t) (n + 1)

/-! ## Step maps -/

/-- A step map on an invariant commutes with the activation failing on exhausted fuel, and the
invariant holds at its possible outcomes. -/
theorem fbRunFail_stepMap_on {S : Sys τ (E ⊕ X) (O ⊕ X)} {S' : Sys υ (E ⊕ X) (O ⊕ X)}
    {Inv : τ → Prop} {f : τ → υ} (h : StepMapOn S S' Inv f) :
    ∀ (m : ℕ) (g : E ⊕ X) (t : τ), Inv t →
      (∀ p, IsOutcome (S.fbRunFail m g t) p → Inv p.1) ∧
      SPComp.map (fun p => (f p.1, p.2)) (S.fbRunFail m g t) = S'.fbRunFail m g (f t) := by
  intro m
  induction m with
  | zero =>
    intro g t ht
    refine ⟨fun p hp => ?_, ?_⟩
    · simp only [fbRunFail] at hp
      obtain ⟨q, hq, hpq⟩ := isOutcome_bind hp
      have hq' := h.pres t g ht q hq
      rcases q with ⟨t', o | x⟩
      · obtain rfl := isOutcome_pure hpq
        exact hq'
      · obtain ⟨_, _, hpq⟩ := hpq
        exact absurd (SDistr.fail_apply_some _) hpq
    · simp only [fbRunFail, ← h.step t g ht, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
      congr 1; funext q; rcases q with ⟨t', o | x⟩ <;> simp
  | succ m ih =>
    intro g t ht
    refine ⟨fun p hp => ?_, ?_⟩
    · simp only [fbRunFail] at hp
      obtain ⟨q, hq, hpq⟩ := isOutcome_bind hp
      have hq' := h.pres t g ht q hq
      rcases q with ⟨t', o | x⟩
      · obtain rfl := isOutcome_pure hpq
        exact hq'
      · exact (ih (.inr x) t' hq').1 p hpq
    · simp only [fbRunFail, ← h.step t g ht, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
      refine bind_congr_isOutcome fun q hq => ?_
      have hq' := h.pres t g ht q hq
      rcases q with ⟨t', o | x⟩
      · simp
      · simpa [SPComp.map] using (ih (.inr x) t' hq').2

/-- A step map on an invariant commutes with the unbounded activation, and the invariant holds
at its possible outcomes. -/
theorem fbRunω_stepMap_on {S : Sys τ (E ⊕ X) (O ⊕ X)} {S' : Sys υ (E ⊕ X) (O ⊕ X)}
    {Inv : τ → Prop} {f : τ → υ} (h : StepMapOn S S' Inv f) (g : E ⊕ X) (t : τ) (ht : Inv t) :
    (∀ p, IsOutcome (S.fbRunω g t) p → Inv p.1) ∧
      SPComp.map (fun p => (f p.1, p.2)) (S.fbRunω g t) = S'.fbRunω g (f t) := by
  refine ⟨fun p hp => ?_, ?_⟩
  · obtain ⟨n, hn⟩ := exists_isOutcome_of_isOutcome_ωSup hp
    exact (fbRunFail_stepMap_on h n g t ht).1 p hn
  · change SPComp.bind (ωSup (S.fbChain g t)) (fun p => SPComp.pure (f p.1, p.2)) = _
    rw [(SPComp.ωScottContinuous_bind_left _).map_ωSup]
    exact le_antisymm
      (ωSup_le _ _ fun n => (fbRunFail_stepMap_on h n g t ht).2.le.trans
        (le_ωSup (S'.fbChain g (f t)) n))
      (ωSup_le _ _ fun n => le_ωSup_of_le n (fbRunFail_stepMap_on h n g t ht).2.ge)

/-- **Step maps under unbounded feedback.** A step map `f` from `S` to `S'` on `Inv` is a step
map from the unbounded loopback of `S` to that of `S'` on `Inv`. -/
theorem loopbackω_stepMap_on {S : Sys τ (E ⊕ X) (O ⊕ X)} {S' : Sys υ (E ⊕ X) (O ⊕ X)}
    {Inv : τ → Prop} {f : τ → υ} (h : StepMapOn S S' Inv f) :
    StepMapOn S.loopbackω S'.loopbackω Inv f where
  init_inv := h.init_inv
  init_map := h.init_map
  pres t e ht q hq := (fbRunω_stepMap_on h (.inl e) t ht).1 q hq
  step t e ht := (fbRunω_stepMap_on h (.inl e) t ht).2

/-! ## Adequate fuel -/

/-- With adequate fuel `k`, the activation failing on exhausted fuel `n ≥ k` is the activation
with fuel `k` and any cut-off map. -/
theorem fbRunFail_eq_of_exitsBy {S : Sys τ (E ⊕ X) (O ⊕ X)} {P : τ → Prop} (cut : X → O) :
    ∀ (k : ℕ) {n : ℕ} {g : E ⊕ X} {t : τ}, S.ExitsBy P k g t → k ≤ n →
      S.fbRunFail n g t = fbRun S cut k g t := by
  intro k
  induction k with
  | zero =>
    intro n g t h _
    cases n <;>
    · simp only [fbRunFail, fbRun]
      refine bind_congr_isOutcome fun q hq => ?_
      have hq' := h q hq
      rcases q with ⟨t', o | x⟩
      · rfl
      · exact False.elim hq'
  | succ k ih =>
    intro n g t h hkn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [fbRunFail, fbRun]
    refine bind_congr_isOutcome fun q hq => ?_
    have hq' := h q hq
    rcases q with ⟨t', o | x⟩
    · rfl
    · exact ih hq' (by omega)

/-- With adequate fuel `k`, the unbounded activation is the activation with fuel `k` and any
cut-off map. -/
theorem fbRunω_eq_of_exitsBy {S : Sys τ (E ⊕ X) (O ⊕ X)} {P : τ → Prop} (cut : X → O) (k : ℕ)
    {g : E ⊕ X} {t : τ} (h : S.ExitsBy P k g t) : S.fbRunω g t = fbRun S cut k g t := by
  apply le_antisymm
  · refine ωSup_le _ _ fun n => ?_
    calc S.fbRunFail n g t ≤ S.fbRunFail (max n k) g t := S.fbRunFail_mono g t (le_max_left _ _)
      _ = fbRun S cut k g t := fbRunFail_eq_of_exitsBy cut k h (le_max_right _ _)
  · rw [← fbRunFail_eq_of_exitsBy cut k h le_rfl]
    exact le_ωSup (S.fbChain g t) k

/-- **Adequate fuel.** When fuel `k` is adequate for `S` on an invariant that holds initially,
the projection to the state of `S` is a step map from the loopback with fuel `n ≥ k` and any
cut-off map to the unbounded loopback. -/
theorem loopback_stepMap_loopbackω (S : Sys τ (E ⊕ X) (O ⊕ X)) (Inv : τ → Prop) {k n : ℕ}
    (hkn : k ≤ n) (cut : X → O) (hinit : Inv S.init) (hex : S.ExitsWithin Inv k) :
    StepMapOn (S.loopback n cut) S.loopbackω (fun u => Inv u.2) Prod.snd where
  init_inv := hinit
  init_map := rfl
  pres u e hu q hq := by
    rw [loopback_step, fbRun_eq_of_exitsBy cut cut k (hex u.2 hu e) hkn] at hq
    obtain ⟨p, hp, rfl⟩ := exists_of_isOutcome_map hq
    exact fbRun_isOutcome_of_exitsBy cut k (hex u.2 hu e) p hp
  step u e hu := by
    rw [loopback_step, loopbackω_step, fbRunω_eq_of_exitsBy cut k (hex u.2 hu e),
      fbRun_eq_of_exitsBy cut cut k (hex u.2 hu e) hkn]
    simp only [SPComp.map_comp, Function.comp_def]
    exact SPComp.map_id _

/-- **Adequate fuel**, as step equivalence: the loopback with fuel `n ≥ k` and any cut-off map is
step-equivalent to the unbounded loopback. -/
theorem loopback_stepEq_loopbackω (S : Sys τ (E ⊕ X) (O ⊕ X)) (Inv : τ → Prop) {k n : ℕ}
    (hkn : k ≤ n) (cut : X → O) (hinit : Inv S.init) (hex : S.ExitsWithin Inv k) :
    StepEq ⟨Unit × τ, S.loopback n cut⟩ ⟨τ, S.loopbackω⟩ :=
  (loopback_stepMap_loopbackω S Inv hkn cut hinit hex).stepEq

end Sys

end CatCrypt.Crypto.UCTransparent
