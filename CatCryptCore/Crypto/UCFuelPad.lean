/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCParallel

/-!
# Padding the fuel of a multi-call hybrid

The counted form `π.counted n` of a multi-call hybrid `π` has fuel `n` and the state of `π`
together with the number of answers received in the current activation. It runs `π`, and on the
answer to call number `π.fuel + 1` it calls `π.finish` and ends the activation, so for
`π.fuel ≤ n` it makes the calls of `π` whatever the larger fuel. Over every subroutine, `π` and
`π.counted n` realize each other at distance `0` (`realizes_counted`, `realizes_counted_symm`),
and opacity carries over with the counters required equal (`Opaque.counted`).

Padding both components of a tensor to the larger fuel removes the hypothesis of equal fuels
from `realizes_tensor_withSub_par` and `RealizesSim.par`
(`realizes_tensor_withSub_par_padded`, `RealizesSim.par_padded`).

## Main definitions

* `MultiHybrid.counted`: the multi-call hybrid with a call counter and a given fuel.
* `MultiHybrid.padFuel`: the larger fuel of two multi-call hybrids.

## Main results

* `MultiHybrid.drive_counted`: the rest of an activation of `π.counted n` is the rest of the
  activation of `π`, up to the counter.
* `MultiHybrid.realizes_counted`, `MultiHybrid.realizes_counted_symm`: distance `0`.
* `MultiHybrid.Opaque.counted`: opacity of the counted form.
* `MultiHybrid.realizes_tensor_withSub_par_padded`, `RealizesSim.par_padded`: the tensor over a
  parallel composition, for multi-call hybrids of arbitrary fuels.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open CatCrypt.Relational
open scoped ENNReal

/-- A coupling of `c₁` and `c₂` gives a coupling of their images under `f₁` and `f₂`. -/
private theorem rHoare_map' {α β γ δ : Type} {Φ : RPre} {c₁ : SPComp α} {c₂ : SPComp β}
    {f₁ : α → γ} {f₂ : β → δ} {Ψ : RPost α β} {Θ : RPost γ δ} (h : rHoare Φ c₁ c₂ Ψ)
    (hf : ∀ a h₁ b h₂, Ψ a h₁ b h₂ → Θ (f₁ a) h₁ (f₂ b) h₂) :
    rHoare Φ (SPComp.map f₁ c₁) (SPComp.map f₂ c₂) Θ :=
  rHoare_bind h fun a b => rHoare_ret fun h₁ h₂ hΨ => hf a h₁ b h₂ hΨ

namespace MultiHybrid

variable {σ σ' τ υ E O E' O' EG OG EG' OG' : Type}

/-- The counted form of `π` with fuel `n`: the state of `π` with the number of answers received
in the current activation. `start` sets the counter to `0`; on an answer, `resume` of `π` runs
while the counter is below `π.fuel` and increments it, and `finish` of `π` ends the activation
when the counter has reached `π.fuel`. -/
noncomputable def counted (π : MultiHybrid σ E O EG OG) (n : ℕ) :
    MultiHybrid (σ × ℕ) E O EG OG where
  init := (π.init, 0)
  fuel := n
  start s e := SPComp.map (fun r => ((r.1, 0), r.2)) (π.start s.1 e)
  resume s o :=
    if s.2 < π.fuel then SPComp.map (fun r => ((r.1, s.2 + 1), r.2)) (π.resume s.1 o)
    else SPComp.map (fun r => ((r.1, 0), Sum.inr r.2)) (π.finish s.1 o)
  finish s o := SPComp.map (fun r => ((r.1, 0), r.2)) (π.finish s.1 o)
  start_noFail s e :=
    Assumptions.SPComp.bind_noFail (π.start_noFail _ _) fun _ => SPComp.pure_noFail _
  resume_noFail s o := by
    split
    · exact Assumptions.SPComp.bind_noFail (π.resume_noFail _ _) fun _ => SPComp.pure_noFail _
    · exact Assumptions.SPComp.bind_noFail (π.finish_noFail _ _) fun _ => SPComp.pure_noFail _
  finish_noFail s o :=
    Assumptions.SPComp.bind_noFail (π.finish_noFail _ _) fun _ => SPComp.pure_noFail _

/-- The larger of the fuels of `π` and `π'`, the fuel to which both are padded. -/
def padFuel (π : MultiHybrid σ E O EG OG) (π' : MultiHybrid σ' E' O' EG' OG') : ℕ :=
  max π.fuel π'.fuel

/-- The fuel of `π` is at most the padded fuel. -/
theorem le_padFuel_left (π : MultiHybrid σ E O EG OG) (π' : MultiHybrid σ' E' O' EG' OG') :
    π.fuel ≤ padFuel π π' :=
  le_max_left _ _

/-- The fuel of `π'` is at most the padded fuel. -/
theorem le_padFuel_right (π : MultiHybrid σ E O EG OG) (π' : MultiHybrid σ' E' O' EG' OG') :
    π'.fuel ≤ padFuel π π' :=
  le_max_right _ _

section CountedUnfold

variable (π : MultiHybrid σ E O EG OG) (n : ℕ) (s : σ) (k : ℕ)

/-- Unfolding lemma of `counted`: `start`. -/
@[simp] theorem counted_start (e : E) : (π.counted n).start (s, k) e =
    SPComp.map (fun r => ((r.1, 0), r.2)) (π.start s e) := rfl

/-- Unfolding lemma of `counted`: `resume` with the counter below the fuel of `π`. -/
theorem counted_resume_of_lt (o : OG) (hk : k < π.fuel) : (π.counted n).resume (s, k) o =
    SPComp.map (fun r => ((r.1, k + 1), r.2)) (π.resume s o) := by
  simp only [counted, hk, ↓reduceIte]

/-- Unfolding lemma of `counted`: `resume` with the counter at the fuel of `π` or above. -/
theorem counted_resume_of_le (o : OG) (hk : π.fuel ≤ k) : (π.counted n).resume (s, k) o =
    SPComp.map (fun r => ((r.1, 0), Sum.inr r.2)) (π.finish s o) := by
  simp only [counted, Nat.not_lt.mpr hk, ↓reduceIte]

/-- Unfolding lemma of `counted`: `finish`. -/
@[simp] theorem counted_finish (o : OG) : (π.counted n).finish (s, k) o =
    SPComp.map (fun r => ((r.1, 0), r.2)) (π.finish s o) := rfl

end CountedUnfold

/-- The rest of an activation of `π.counted n` with counter `k` and `n'` calls left after the
next one is the rest of the activation of `π` with `m` calls left, up to the counter, when
`k + m = π.fuel` and `m ≤ n'`. -/
theorem drive_counted (π : MultiHybrid σ E O EG OG) (n : ℕ) (X : Sys τ EG OG) :
    ∀ m k n', k + m = π.fuel → m ≤ n' → ∀ s d t,
      SPComp.map (fun p => (p.1.1, p.2)) ((π.counted n).drive X n' (s, k) d t) =
        π.drive X m s d t := by
  intro m
  induction m with
  | zero =>
    intro k n' hk _ s d t
    rcases d with g | o
    · rcases n' with _ | n'
      · simp [drive, counted, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
      · simp [drive, counted, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind, ← hk]
    · simp [drive, SPComp.map, SPComp.pure_bind]
  | succ m ih =>
    intro k n' hk hm s d t
    obtain ⟨n', rfl⟩ : ∃ n'', n' = n'' + 1 := ⟨n' - 1, by omega⟩
    rcases d with g | o
    · have hlt : k < π.fuel := by omega
      have ih' := fun s d t => ih (k + 1) n' (by omega) (by omega) s d t
      simp only [drive, counted_resume_of_lt π n s k _ hlt, SPComp.map, SPComp.bind_assoc,
        SPComp.pure_bind] at ih' ⊢
      congr 1; funext q; congr 1; funext r
      exact ih' _ _ _
    · simp [drive, SPComp.map, SPComp.pure_bind]

/-- A step of `(π.counted n).withSub X` is a step of `π.withSub X`, up to the counter, when
`π.fuel ≤ n`. -/
theorem counted_withSub_step (π : MultiHybrid σ E O EG OG) {n : ℕ} (hn : π.fuel ≤ n)
    (X : Sys τ EG OG) (p : (σ × ℕ) × τ) (e : E) :
    SPComp.map (fun q => ((q.1.1.1, q.1.2), q.2)) (((π.counted n).withSub X).step p e) =
      (π.withSub X).step (p.1.1, p.2) e := by
  have h := fun s d t => drive_counted π n X π.fuel 0 n (by omega) hn s d t
  simp only [withSub, counted, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind] at h ⊢
  congr 1; funext r
  rw [← h]
  simp only [SPComp.bind_assoc, SPComp.pure_bind]

/-- **Fuel padding**: `(π.counted n).withSub X` realizes `π.withSub X` at distance `0`, for
`π.fuel ≤ n`. -/
theorem realizes_counted (π : MultiHybrid σ E O EG OG) {n : ℕ} (hn : π.fuel ≤ n)
    (X : Sys τ EG OG) :
    Realizes ((π.counted n).withSub X) (π.withSub X) (fun _ _ => 0) :=
  realizes_zero_of_stepMap _ _ (fun p => (p.1.1, p.2)) rfl fun p e =>
    counted_withSub_step π hn X p e

/-- **Fuel padding**: `π.withSub X` realizes `(π.counted n).withSub X` at distance `0`, for
`π.fuel ≤ n`. -/
theorem realizes_counted_symm (π : MultiHybrid σ E O EG OG) {n : ℕ} (hn : π.fuel ≤ n)
    (X : Sys τ EG OG) :
    Realizes (π.withSub X) ((π.counted n).withSub X) (fun _ _ => 0) :=
  fun ζ => (realizes_counted π hn X ζ).symm

/-- An unwinding relation `R` of `π` gives the unwinding relation `R × (=)` of its counted
form. -/
theorem Unwinding.counted {π : MultiHybrid σ E O EG OG} {V : PubView E O} {W : PubView EG OG}
    {R : σ → σ → Prop} (h : π.Unwinding V W R) (n : ℕ) :
    (π.counted n).Unwinding V W (fun s t => R s.1 t.1 ∧ s.2 = t.2) where
  init := ⟨h.init, rfl⟩
  start := by
    rintro ⟨s, k⟩ ⟨s', k'⟩ e e' ⟨hs, -⟩ he
    rw [counted_start, counted_start]
    exact rHoare_map' (h.start _ _ _ _ hs he) fun _ _ _ _ hp => ⟨hp.1, ⟨hp.2.1, rfl⟩, hp.2.2⟩
  resume := by
    rintro ⟨s, k⟩ ⟨s', k'⟩ o o' ⟨hs, rfl⟩ ho
    by_cases hk : k < π.fuel
    · rw [counted_resume_of_lt _ _ _ _ _ hk, counted_resume_of_lt _ _ _ _ _ hk]
      exact rHoare_map' (h.resume _ _ _ _ hs ho) fun _ _ _ _ hp =>
        ⟨hp.1, ⟨hp.2.1, rfl⟩, hp.2.2⟩
    · rw [counted_resume_of_le _ _ _ _ _ (Nat.not_lt.mp hk),
        counted_resume_of_le _ _ _ _ _ (Nat.not_lt.mp hk)]
      exact rHoare_map' (h.finish _ _ _ _ hs ho) fun _ _ _ _ hp =>
        ⟨hp.1, ⟨hp.2.1, rfl⟩, hp.2.2⟩
  finish := by
    rintro ⟨s, k⟩ ⟨s', k'⟩ o o' ⟨hs, -⟩ ho
    rw [counted_finish, counted_finish]
    exact rHoare_map' (h.finish _ _ _ _ hs ho) fun _ _ _ _ hp => ⟨hp.1, ⟨hp.2.1, rfl⟩, hp.2.2⟩

/-- **Opacity of the counted form**: the counted form of a simulator opaque from `W` to `V` is
opaque from `W` to `V`. -/
theorem Opaque.counted {π : MultiHybrid σ E O EG OG} {V : PubView E O} {W : PubView EG OG}
    (h : π.Opaque V W) (n : ℕ) : (π.counted n).Opaque V W := by
  obtain ⟨R, hR⟩ := h
  exact ⟨_, hR.counted n⟩

/-- **Tensor and parallel composition, unequal fuels.** For multi-call hybrids `π` and `π'`,
the tensor of their counted forms at the larger fuel over the parallel composition of `X` and
`Y` and the parallel composition of `π` over `X` and `π'` over `Y` realize each other at
distance `0`. -/
theorem realizes_tensor_withSub_par_padded (π : MultiHybrid σ E O EG OG)
    (π' : MultiHybrid σ' E' O' EG' OG') (X : Sys τ EG OG) (Y : Sys υ EG' OG') :
    Realizes (((π.counted (padFuel π π')).tensor (π'.counted (padFuel π π'))).withSub (X.par Y))
      ((π.withSub X).par (π'.withSub Y)) (fun _ _ => 0) := by
  have h₁ := realizes_tensor_withSub_par (π.counted (padFuel π π'))
    (π'.counted (padFuel π π')) rfl X Y
  have h₂ : Realizes (((π.counted (padFuel π π')).withSub X).par
      ((π'.counted (padFuel π π')).withSub Y)) ((π.withSub X).par (π'.withSub Y))
      (fun _ _ => 0) := by
    refine realizes_zero_of_stepMap _ _
      (fun p => ((p.1.1.1, p.1.2), (p.2.1.1, p.2.2))) rfl ?_
    rintro ⟨a, b⟩ (e | e)
    · rw [Sys.par_step_inl, Sys.par_step_inl,
        ← counted_withSub_step π (le_padFuel_left π π') X a e]
      simp [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
    · rw [Sys.par_step_inr, Sys.par_step_inr,
        ← counted_withSub_step π' (le_padFuel_right π π') Y b e]
      simp [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  exact fun ζ => ((h₁ ζ).triangle (h₂ ζ)).mono fun _ => by simp

end MultiHybrid

open MultiHybrid in
/-- **Parallel composition behind the tensor of simulators, unequal fuels.** If `X` realizes `I`
behind the opaque multi-call simulator `S` with bound `bX`, and `Y` realizes `J` behind `S'` with
bound `bY`, then `X.par Y` realizes `I.par J` behind the tensor of the counted forms of `S` and
`S'` at the larger fuel, with the bound of `realizes_par`. -/
theorem RealizesSim.par_padded {σ σ' τ τ' υ υ' E O E' O' EG OG EG' OG' : Type}
    {V : PubView E O} {W : PubView EG OG} {V' : PubView E' O'} {W' : PubView EG' OG'}
    {X : Sys τ E O} {I : Sys τ' EG OG} {Y : Sys υ E' O'} {J : Sys υ' EG' OG'}
    (S : MultiHybrid σ E O EG OG) (S' : MultiHybrid σ' E' O' EG' OG')
    (hS : S.Opaque V W) (hS' : S'.Opaque V' W')
    (hY : ∀ u e, SPComp.NoFail (Y.step u e))
    (hSI : ∀ t e, SPComp.NoFail ((S.withSub I).step t e))
    (idleL : E) (idleR : E') {oX oSI : O} {oY oSJ : O'}
    (hXi : IdleAt X idleL oX) (hSIi : IdleAt (S.withSub I) idleL oSI)
    (hYi : IdleAt Y idleR oY) (hSJi : IdleAt (S'.withSub J) idleR oSJ)
    {bX : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞}
    {bY : (ζ : Type) → Env (Strat ζ E' O') ζ → ℝ≥0∞}
    (hX : RealizesSim X I (Simulator.ofMultiHybrid S hS) bX)
    (hYr : RealizesSim Y J (Simulator.ofMultiHybrid S' hS') bY) :
    RealizesSim (X.par Y) (I.par J)
      (Simulator.tensor (S.counted (padFuel S S')) (S'.counted (padFuel S S'))
        (hS.counted _) (hS'.counted _))
      (fun ζ Z => bX (RState υ ζ E (O ⊕ O')) ((parCtxL Y hY).reduceEnv idleL Z) +
        bY (RState (σ × τ') ζ E' (O ⊕ O')) ((parCtxR (S.withSub I) hSI).reduceEnv idleR Z)) := by
  have h₁ := realizes_par hY hSI idleL idleR hXi hSIi hYi hSJi hX hYr
  have h₂ := realizes_tensor_withSub_par_padded S S' I J
  exact fun ζ => ((h₁ ζ).triangle (h₂ ζ).symm).mono fun _ => by simp

end CatCrypt.Crypto.UCTransparent
