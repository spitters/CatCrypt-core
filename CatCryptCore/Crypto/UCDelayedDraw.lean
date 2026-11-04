/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCTransparentMulti
public import CatCryptCore.Crypto.UCFeedbackLaws
public import CatCryptCore.NonUniform.Sample
public import CatCryptCore.Unary.Lossless

/-!
# Delayed draws of a key in a reactive system

A reactive system may draw a key later than the start of the run, at the first activation that
reads it, while its specification draws the key at the start. This file states such delayed
draws and moves the draw to the start of the run at distance `0`.

## Model

* `Sys.DelayedDraw L W μ Inv D` — the system `L` draws a key of distribution `μ`, or parts of
  it, later than the systems `W k` with the key `k` drawn at the start; `D s` is the conditional
  distribution of the key and of the state of `W` given the state `s` of `L`. A draw at the first
  use, several keys drawn at their own first uses, and a draw through a bijection chosen at the
  state of the draw are delayed draws.
* `KeyedSys K τ E O` — a system whose steps read a key of type `K`: `step k` for the
  activations that read the key, `step₀` for those that do not, and `uses t e` saying which.
  `KeyedSys.withKey S k` is the system with the key fixed to `k`; `KeyedSys.lazy S μ` is the
  system that samples the key from `μ` at the first activation that reads it.

## Main results

* `Sys.DelayedDraw.view_eq` (delayed draw) — the view of `L` is the average over `k ← μ` of the
  views of `W k`.
* `Sys.delayedDraw_ofSlot` — a key drawn into a slot of the state at its first use is a
  delayed draw; `KeyedSys.delayedDraw_lazy` — so is the lazily keyed system.
* `Sys.DelayedDraw.withSub` — a delayed draw of the subroutine of a multi-call hybrid is a
  delayed draw of the hybrid.
* `KeyedSys.view_lazy` (lazy to eager sampling) — when the activations that do not read the
  key step as `step₀`, the view of the lazily keyed system is the average over `k ← μ` of the
  views of the system with key `k`: the sample moves to the start of the run at distance 0.
* `KeyedSys.ofPorts`, `KeyedSys.lazy_ofPorts` — the keyed system on two ports, and lazy sampling
  commutes with it.
* `KeyedSys.lazy_pres` — invariants of a lazily keyed system, from each kind of activation;
  `KeyedSys.lazy_pres_det` — the same for deterministic steps, as a draw followed by a point
  mass into the invariant.
* `isOutcome_bind_sampleFrom_iff` — the possible outcomes of a bind with a draw.

Trace equivalence of delayed draws against the same eager systems (`Sys.DelayedDraw.traceEq`,
`KeyedSys.traceEq_lazy`) is in `CatCryptCore.Crypto.TraceEqLaws`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.NonUniform CatCrypt.Crypto.UCConcrete
open scoped ENNReal

/-- The possible outcomes of a bind with a draw from `d`: the possible outcomes of the
continuation at the values in the support of `d`. -/
theorem isOutcome_bind_sampleFrom_iff {α β : Type} {d : SDistr α} {f : α → SPComp β} {b : β} :
    IsOutcome (SPComp.bind (sampleFrom d) f) b ↔ ∃ a, d (some a) ≠ 0 ∧ IsOutcome (f a) b := by
  rw [isOutcome_bind_iff_of_isPure (sampleFrom_isPure d)]
  refine exists_congr fun a => and_congr_left fun _ => ⟨fun ⟨hp, hp', h⟩ => ?_, fun h => ?_⟩
  · obtain ⟨a', ha', hp⟩ := SDistr.bind_support_witness h
    obtain ⟨rfl, -⟩ := Prod.mk.inj ((SDistr.mem_support_pure_iff _ _).mp hp)
    exact ha'
  · refine ⟨Heap.empty, Heap.empty, ?_⟩
    rw [sampleFrom_apply]
    unfold SDistr.bind
    rw [PMF.bind_apply, ne_eq, ENNReal.tsum_eq_zero]
    push Not
    exact ⟨some a, mul_ne_zero h ((SDistr.mem_support_pure_iff _ _).mpr rfl)⟩

/-! ## Delayed draws -/

namespace Sys

variable {K σ τ E O ζ : Type}

/-- **A delayed draw.** The system `L` draws a key of distribution `μ`, or a part of it, later
than the start of the run, and `W k` is the system with the key `k` drawn at the start. `D s` is
the distribution of the key and of the state of `W` given the state `s` of `L`: the conditional
distribution of what `L` has not drawn yet at `s`, the state of `W` being determined by `s` and
the key. On the states of the invariant `Inv`, drawing from `D` after a step of `L` gives the
key, the next state of `W` and the output with the distribution of a step of `W` after drawing
from `D`. A draw at the first use of a key, several keys each drawn at its own first use, and a
draw through a bijection that depends on the state at the draw are delayed draws. -/
structure DelayedDraw (L : Sys σ E O) (W : K → Sys τ E O) (μ : PMF K) (Inv : σ → Prop)
    (D : σ → SDistr (K × τ)) : Prop where
  /-- The invariant holds initially. -/
  init_inv : Inv L.init
  /-- Initially nothing is drawn: the key has distribution `μ`, and `W k` is at its start. -/
  init : D L.init = (ofPMF μ).bind fun k => SDistr.pure (k, (W k).init)
  /-- The conditional distributions are total. -/
  mass : ∀ s, SDistr.mass (D s) = 1
  /-- The invariant holds at the possible outcomes of every step from a state satisfying it. -/
  pres : ∀ s e, Inv s → ∀ q, IsOutcome (L.step s e) q → Inv q.1
  /-- A step of `L` followed by the draw from `D` is the draw from `D` followed by a step of
  `W`. -/
  step : ∀ s e, Inv s →
    SPComp.bind (L.step s e) (fun q => SPComp.map (fun kt => (kt, q.2)) (sampleFrom (D q.1))) =
      SPComp.bind (sampleFrom (D s)) fun kt =>
        SPComp.map (fun p => ((kt.1, p.1), p.2)) ((W kt.1).step kt.2 e)

/-- **A delayed draw on loops.** From a state of the invariant, the run of `L` followed by the
draw from `D` at its last state is the draw from `D` followed by the run of `W` with the key
drawn. -/
theorem DelayedDraw.loop {L : Sys σ E O} {W : K → Sys τ E O} {μ : PMF K} {Inv : σ → Prop}
    {D : σ → SDistr (K × τ)} (h : DelayedDraw L W μ Inv D) (Z : Strat ζ E O) :
    ∀ (n : ℕ) (z : ζ) (s : σ) (b : Bool), Inv s →
      SPComp.bind (loop L (fun _ => false) Z n (z, s, b))
          (fun c => SPComp.map (fun kt => (kt.1, c.1, kt.2, c.2.2)) (sampleFrom (D c.2.1))) =
        SPComp.bind (sampleFrom (D s)) fun kt =>
          SPComp.map (fun c => (kt.1, c)) (loop (W kt.1) (fun _ => false) Z n (z, kt.2, b)) := by
  have hc : ∀ s, SPComp.IsPure (sampleFrom (D s)) := fun s => sampleFrom_isPure _
  intro n
  induction n with
  | zero =>
    intro z s b _
    simp only [UCTransparent.loop, SPComp.pure_bind, SPComp.map]
  | succ n ih =>
    intro z s b hs
    have key : ∀ a : ζ × E,
        SPComp.bind (L.step s a.2) (fun p => SPComp.bind (Z.obs a.1 p.2) fun z' =>
          SPComp.bind (UCTransparent.loop L (fun _ => false) Z n (z', p.1, b || false))
            fun c => SPComp.map (fun kt => (kt.1, c.1, kt.2, c.2.2)) (sampleFrom (D c.2.1))) =
        SPComp.bind (sampleFrom (D s)) fun kt =>
          SPComp.bind ((W kt.1).step kt.2 a.2) fun p => SPComp.bind (Z.obs a.1 p.2) fun z' =>
            SPComp.map (fun c => (kt.1, c))
              (UCTransparent.loop (W kt.1) (fun _ => false) Z n (z', p.1, b || false)) := by
      intro a
      calc _ = SPComp.bind (L.step s a.2) (fun p => SPComp.bind (sampleFrom (D p.1)) fun kt =>
              SPComp.bind (Z.obs a.1 p.2) fun z' => SPComp.map (fun c => (kt.1, c))
                (UCTransparent.loop (W kt.1) (fun _ => false) Z n (z', kt.2, b || false))) := by
            refine bind_congr_isOutcome fun p hp => ?_
            simp only [ih _ _ _ (h.pres s a.2 hs p hp)]
            exact (SPComp.isPure_bind_comm_left _ _ _ (hc _)).symm
        _ = SPComp.bind (SPComp.bind (L.step s a.2) fun q =>
              SPComp.map (fun kt => (kt, q.2)) (sampleFrom (D q.1))) fun x =>
                SPComp.bind (Z.obs a.1 x.2) fun z' => SPComp.map (fun c => (x.1.1, c))
                  (UCTransparent.loop (W x.1.1) (fun _ => false) Z n (z', x.1.2, b || false)) := by
            simp only [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
        _ = _ := by
            rw [h.step s a.2 hs]
            simp only [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
    simp only [UCTransparent.loop, SPComp.bind_assoc, key]
    refine (SPComp.isPure_bind_comm_left _ _ _ (hc _)).symm.trans ?_
    simp only [SPComp.map, SPComp.bind_assoc]

/-- **Delayed draw.** The view of a system with a delayed draw of a key of distribution `μ` is
the average over `k ← μ` of the views of the system with the key `k` drawn at the start. -/
theorem DelayedDraw.view_eq {L : Sys σ E O} {W : K → Sys τ E O} {μ : PMF K} {Inv : σ → Prop}
    {D : σ → SDistr (K × τ)} (h : DelayedDraw L W μ Inv D) (Z : Strat ζ E O) :
    view L Z = SPComp.bind (sampleFrom (ofPMF μ)) fun k => view (W k) Z := by
  have hl := congrArg (SPComp.map fun x => x.2.1)
    (h.loop Z Z.rounds Z.init L.init false h.init_inv)
  simp only [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind, dead_sampleFrom (h.mass _), h.init,
    ← sampleFrom_bind_sampleFrom, sampleFrom_pure] at hl
  simp only [view, run, SPComp.map, hl]

/-- The conditional distribution of the key and the state given a state with an optional key
slot: the key in the slot, or a draw from `μ` with an empty slot. -/
noncomputable def slotCond (μ : PMF K) (slot : σ → Option K) (s : σ) : SDistr (K × σ) :=
  match slot s with
  | some k => SDistr.pure (k, s)
  | none => (ofPMF μ).bind fun k => SDistr.pure (k, s)

/-- **A key drawn into the state is a delayed draw.** The system `L` holds its key in the slot
`slot` of its state, `W k` is `L` with the key `k` given in place of each draw. With the key `k`
in the slot, `L` steps as `W k` and keeps `k`; with an empty slot, an activation either draws
the key from `μ` and steps as `W k` with the key `k` put in the slot, or steps as every `W k`
and leaves the slot empty. -/
theorem delayedDraw_ofSlot (L : Sys σ E O) (W : K → Sys σ E O) (μ : PMF K)
    (slot : σ → Option K) (hinit : ∀ k, (W k).init = L.init)
    (hsome : ∀ s k e, slot s = some k → L.step s e = (W k).step s e)
    (hkeep : ∀ s k e, slot s = some k → ∀ q, IsOutcome ((W k).step s e) q → slot q.1 = some k)
    (hnone : ∀ s e, slot s = none →
      (L.step s e = SPComp.bind (sampleFrom (ofPMF μ)) (fun k => (W k).step s e) ∧
        ∀ k q, IsOutcome ((W k).step s e) q → slot q.1 = some k) ∨
      ((∀ k, L.step s e = (W k).step s e) ∧
        ∀ q, IsOutcome (L.step s e) q → slot q.1 = none)) (h₀ : slot L.init = none) :
    DelayedDraw L W μ (fun _ => True) (slotCond μ slot) where
  init_inv := trivial
  init := by simp only [slotCond, h₀, hinit]
  mass s := by
    unfold slotCond
    split
    · exact SDistr.mass_pure _
    · rw [← isLossless_sampleFrom_iff, ← sampleFrom_bind_sampleFrom]
      exact Unary.lossless_bind (isLossless_sampleFrom_ofPMF μ) fun _ =>
        (isLossless_sampleFrom_iff _).mpr (SDistr.mass_pure _)
  pres _ _ _ _ _ := trivial
  step s e _ := by
    rcases hs : slot s with _ | k
    · rcases hnone s e hs with ⟨hL, hk⟩ | ⟨hL, hk⟩
      · rw [hL, SPComp.bind_assoc]
        simp only [slotCond, hs, ← sampleFrom_bind_sampleFrom, sampleFrom_pure, SPComp.map,
          SPComp.bind_assoc, SPComp.pure_bind]
        congr 1; funext k
        exact bind_congr_isOutcome fun q hq => by simp only [hk k q hq, sampleFrom_pure,
          SPComp.pure_bind]
      · rw [bind_congr_isOutcome (g := fun q => SPComp.bind (sampleFrom (ofPMF μ)) fun k =>
            SPComp.pure ((k, q.1), q.2)) fun q hq => by
          simp only [slotCond, hk q hq, ← sampleFrom_bind_sampleFrom, sampleFrom_pure,
            SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]]
        simp only [slotCond, hs, ← sampleFrom_bind_sampleFrom, sampleFrom_pure, SPComp.map,
          SPComp.bind_assoc, SPComp.pure_bind, ← hL]
        exact (SPComp.isPure_bind_comm_left _ _ _ (sampleFrom_isPure _)).symm
    · rw [hsome s k e hs, bind_congr_isOutcome (g := fun q => SPComp.pure ((k, q.1), q.2))
        fun q hq => by simp only [slotCond, hkeep s k e hs q hq, sampleFrom_pure, SPComp.map,
          SPComp.pure_bind]]
      simp only [slotCond, hs, sampleFrom_pure, SPComp.map, SPComp.pure_bind]

/-! ### Delayed draws under a multi-call hybrid -/

section Hybrid

variable {υ EG OG : Type}

/-- The invariant of a delayed draw holds at the possible outcomes of the rest of an activation
of a multi-call hybrid over the drawing subroutine. -/
theorem DelayedDraw.drive_pres {X : Sys τ EG OG} {W : K → Sys υ EG OG} {μ : PMF K}
    {Inv : τ → Prop} {D : τ → SDistr (K × υ)} (h : DelayedDraw X W μ Inv D)
    (π : MultiHybrid σ E O EG OG) :
    ∀ n s d x, Inv x → ∀ p, IsOutcome (π.drive X n s d x) p → Inv p.2.1 := by
  intro n
  induction n with
  | zero =>
    rintro s (g | o) x hx p hp
    · obtain ⟨q, hq, hp⟩ := isOutcome_bind hp
      obtain ⟨r, -, hp⟩ := isOutcome_bind hp
      rw [← isOutcome_pure hp]
      exact h.pres x g hx q hq
    · rw [← isOutcome_pure hp]
      exact hx
  | succ n ih =>
    rintro s (g | o) x hx p hp
    · obtain ⟨q, hq, hp⟩ := isOutcome_bind hp
      obtain ⟨r, -, hp⟩ := isOutcome_bind hp
      exact ih _ _ _ (h.pres x g hx q hq) p hp
    · rw [← isOutcome_pure hp]
      exact hx

/-- **A delayed draw under a multi-call hybrid, on the rest of an activation.** -/
theorem DelayedDraw.drive {X : Sys τ EG OG} {W : K → Sys υ EG OG} {μ : PMF K}
    {Inv : τ → Prop} {D : τ → SDistr (K × υ)} (h : DelayedDraw X W μ Inv D)
    (π : MultiHybrid σ E O EG OG) :
    ∀ n s d x, Inv x →
      SPComp.bind (π.drive X n s d x)
          (fun p => SPComp.map (fun kt => (kt.1, p.1, kt.2, p.2.2)) (sampleFrom (D p.2.1))) =
        SPComp.bind (sampleFrom (D x)) fun kt =>
          SPComp.map (fun p => (kt.1, p)) (π.drive (W kt.1) n s d kt.2) := by
  have hc : ∀ x, SPComp.IsPure (sampleFrom (D x)) := fun _ => sampleFrom_isPure _
  have hX : ∀ x g, Inv x → ∀ (F : (K × υ) × OG → SPComp (K × σ × υ × O)),
      SPComp.bind (X.step x g) (fun q => SPComp.bind (sampleFrom (D q.1)) fun kt =>
        F (kt, q.2)) =
      SPComp.bind (sampleFrom (D x)) fun kt =>
        SPComp.bind ((W kt.1).step kt.2 g) fun p => F ((kt.1, p.1), p.2) := by
    intro x g hx F
    have := congrArg (fun c => SPComp.bind c F) (h.step x g hx)
    simpa only [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind] using this
  intro n
  induction n with
  | zero =>
    rintro s (g | o) x hx
    · refine Eq.trans ?_ ((hX x g hx fun y => SPComp.bind (π.finish s y.2) fun r =>
          SPComp.pure (y.1.1, r.1, y.1.2, r.2)).trans ?_)
      · simp only [MultiHybrid.drive, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
        congr 1; funext q
        exact (SPComp.isPure_bind_comm_left _ _ _ (hc _)).symm
      · simp only [MultiHybrid.drive, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
    · simp only [MultiHybrid.drive, SPComp.map, SPComp.pure_bind]
  | succ n ih =>
    rintro s (g | o) x hx
    · refine Eq.trans ?_ ((hX x g hx fun y => SPComp.bind (π.resume s y.2) fun r =>
          SPComp.map (fun p => (y.1.1, p)) (π.drive (W y.1.1) n r.1 r.2 y.1.2)).trans ?_)
      · simp only [MultiHybrid.drive, SPComp.bind_assoc]
        refine bind_congr_isOutcome fun q hq => ?_
        simp only [ih _ _ _ (h.pres x g hx q hq)]
        exact (SPComp.isPure_bind_comm_left _ _ _ (hc _)).symm
      · simp only [MultiHybrid.drive, SPComp.map, SPComp.bind_assoc]
    · simp only [MultiHybrid.drive, SPComp.map, SPComp.pure_bind]

/-- **A delayed draw under a multi-call hybrid.** A hybrid over a subroutine that delays the
draw of a key delays it against the hybrid over the subroutines with the key drawn at the
start. -/
theorem DelayedDraw.withSub {X : Sys τ EG OG} {W : K → Sys υ EG OG} {μ : PMF K}
    {Inv : τ → Prop} {D : τ → SDistr (K × υ)} (h : DelayedDraw X W μ Inv D)
    (π : MultiHybrid σ E O EG OG) :
    DelayedDraw (π.withSub X) (fun k => π.withSub (W k)) μ (fun t => Inv t.2)
      (fun t => (D t.2).bind fun kt => SDistr.pure (kt.1, (t.1, kt.2))) where
  init_inv := h.init_inv
  init := by
    simp only [MultiHybrid.withSub, h.init, SDistr.bind_assoc, SDistr.pure_bind]
  mass t := by
    rw [← isLossless_sampleFrom_iff, ← sampleFrom_bind_sampleFrom]
    exact Unary.lossless_bind ((isLossless_sampleFrom_iff _).mpr (h.mass _)) fun _ =>
      (isLossless_sampleFrom_iff _).mpr (SDistr.mass_pure _)
  pres t e ht q hq := by
    simp only [MultiHybrid.withSub] at hq
    obtain ⟨r, -, hq⟩ := isOutcome_bind hq
    obtain ⟨p, hp, hq⟩ := isOutcome_bind hq
    rw [← isOutcome_pure hq]
    exact h.drive_pres π _ _ _ _ ht p hp
  step t e ht := by
    have hd := fun r : σ × (EG ⊕ O) => congrArg
      (fun c => SPComp.bind c fun x => SPComp.pure ((x.1, (x.2.1, x.2.2.1)), x.2.2.2))
      (h.drive π π.fuel r.1 r.2 t.2 ht)
    simp only [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind] at hd
    simp only [MultiHybrid.withSub, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind,
      ← sampleFrom_bind_sampleFrom, sampleFrom_pure, hd]
    exact SPComp.isPure_bind_comm_left _ _ _ (sampleFrom_isPure _) |>.symm

end Hybrid

end Sys

/-! ## Lazy and eager sampling of a key in a system run -/

/-- A system whose steps read a key of type `K`: initial state `init`, step `step k` with the
key `k` for the activations that read it, step `step₀` for the activations that do not, and
`uses t e` saying whether the activation of the event `e` at the state `t` reads the key. -/
structure KeyedSys (K τ E O : Type) where
  /-- Initial state. -/
  init : τ
  /-- One activation with the key. -/
  step : K → τ → E → SPComp (τ × O)
  /-- One activation that does not read the key. -/
  step₀ : τ → E → SPComp (τ × O)
  /-- Whether the activation reads the key. -/
  uses : τ → E → Bool

namespace KeyedSys

variable {K τ E O ζ : Type}

/-- The system with the key fixed to `k`. -/
def withKey (S : KeyedSys K τ E O) (k : K) : Sys τ E O where
  init := S.init
  step := S.step k

/-- The step of the lazily keyed system: a state with key `k` steps with `k`; a state without
key samples the key from `μ` when the activation reads it, and steps with `step₀` otherwise. -/
noncomputable def lazyStep (S : KeyedSys K τ E O) (μ : PMF K) :
    Option K × τ → E → SPComp ((Option K × τ) × O)
  | (some k, t), e => SPComp.bind (S.step k t e) fun p => SPComp.pure ((some k, p.1), p.2)
  | (none, t), e =>
    if S.uses t e then
      SPComp.bind (sampleFrom (ofPMF μ)) fun k =>
        SPComp.bind (S.step k t e) fun p => SPComp.pure ((some k, p.1), p.2)
    else SPComp.bind (S.step₀ t e) fun p => SPComp.pure ((none, p.1), p.2)

/-- The system that samples its key from `μ` at the first activation that reads it. -/
noncomputable def lazy (S : KeyedSys K τ E O) (μ : PMF K) : Sys (Option K × τ) E O where
  init := (none, S.init)
  step := S.lazyStep μ

/-- The step of the system with key `k` (unfolding lemma of `withKey`). -/
@[simp] theorem withKey_step (S : KeyedSys K τ E O) (k : K) : (S.withKey k).step = S.step k :=
  rfl

/-- The lazily keyed system samples the key at an activation without key that reads it. -/
theorem lazy_step_none_of_uses (S : KeyedSys K τ E O) (μ : PMF K) {t : τ} {e : E}
    (hu : S.uses t e = true) :
    (S.lazy μ).step (none, t) e = SPComp.bind (sampleFrom (ofPMF μ)) fun k =>
      SPComp.bind (S.step k t e) fun p => SPComp.pure ((some k, p.1), p.2) := by
  simp [lazy, lazyStep, hu]

/-- The lazily keyed system steps with `step₀` at an activation without key that does not
read it. -/
theorem lazy_step_none_of_not_uses (S : KeyedSys K τ E O) (μ : PMF K) {t : τ} {e : E}
    (hu : S.uses t e = false) :
    (S.lazy μ).step (none, t) e =
      SPComp.bind (S.step₀ t e) fun p => SPComp.pure ((none, p.1), p.2) := by
  simp [lazy, lazyStep, hu]

/-- The conditional distribution of the key and the state given a state of the lazily keyed
system: the key held, or a draw from `μ` without key. -/
noncomputable def lazyCond (μ : PMF K) : Option K × τ → SDistr (K × τ)
  | (some k, t) => SDistr.pure (k, t)
  | (none, t) => (ofPMF μ).bind fun k => SDistr.pure (k, t)

/-- **The draw at the first use is a delayed draw**, when the activations that do not read the
key step as `step₀`. -/
theorem delayedDraw_lazy (S : KeyedSys K τ E O) (μ : PMF K)
    (hind : ∀ k t e, S.uses t e = false → S.step k t e = S.step₀ t e) :
    Sys.DelayedDraw (S.lazy μ) S.withKey μ (fun _ => True) (lazyCond μ) where
  init_inv := trivial
  init := rfl
  mass := by
    rintro ⟨_ | k, t⟩
    · rw [lazyCond, ← isLossless_sampleFrom_iff, ← sampleFrom_bind_sampleFrom]
      exact Unary.lossless_bind (isLossless_sampleFrom_ofPMF μ) fun _ =>
        (isLossless_sampleFrom_iff _).mpr (SDistr.mass_pure _)
    · simp [lazyCond]
  pres _ _ _ _ _ := trivial
  step := by
    rintro ⟨_ | k, t⟩ e -
    · simp only [lazyCond, ← sampleFrom_bind_sampleFrom, sampleFrom_pure, SPComp.map,
        SPComp.bind_assoc, SPComp.pure_bind, withKey_step]
      cases hu : S.uses t e
      · rw [lazy_step_none_of_not_uses S μ hu]
        simp only [hind _ _ _ hu, SPComp.bind_assoc, SPComp.pure_bind,
          ← sampleFrom_bind_sampleFrom, sampleFrom_pure]
        exact (SPComp.isPure_bind_comm_left _ _ _ (sampleFrom_isPure _)).symm
      · rw [lazy_step_none_of_uses S μ hu]
        simp only [SPComp.bind_assoc, SPComp.pure_bind, sampleFrom_pure]
    · simp [lazy, lazyStep, lazyCond, SPComp.map]

/-- **Lazy to eager sampling.** When the activations that do not read the key step as `step₀`,
the view of the system that samples its key from `μ` at the first activation that reads it is
the average over `k ← μ` of the views of the system with key `k`. -/
theorem view_lazy (S : KeyedSys K τ E O) (μ : PMF K)
    (hind : ∀ k t e, S.uses t e = false → S.step k t e = S.step₀ t e) (Z : Strat ζ E O) :
    view (S.lazy μ) Z = SPComp.bind (sampleFrom (ofPMF μ)) fun k => view (S.withKey k) Z :=
  (delayedDraw_lazy S μ hind).view_eq Z

/-! ### Keyed systems on two ports -/

/-- The keyed system with the state of `SL` and `SR`, which steps as `SL` on a left event and as
`SR` on a right event, the output on the port of the event. -/
noncomputable def ofPorts {E' O' : Type} (SL : KeyedSys K τ E O) (SR : KeyedSys K τ E' O') :
    KeyedSys K τ (E ⊕ E') (O ⊕ O') where
  init := SL.init
  step k t := Sum.elim (fun e => SPComp.map (fun q => (q.1, .inl q.2)) (SL.step k t e))
    (fun e => SPComp.map (fun q => (q.1, .inr q.2)) (SR.step k t e))
  step₀ t := Sum.elim (fun e => SPComp.map (fun q => (q.1, .inl q.2)) (SL.step₀ t e))
    (fun e => SPComp.map (fun q => (q.1, .inr q.2)) (SR.step₀ t e))
  uses t := Sum.elim (SL.uses t) (SR.uses t)

/-- Sampling the key lazily commutes with the composition on two ports. -/
theorem lazy_ofPorts {E' O' : Type} (SL : KeyedSys K τ E O) (SR : KeyedSys K τ E' O')
    (μ : PMF K) : (ofPorts SL SR).lazy μ = Sys.ofPorts (SL.lazy μ) (SR.lazy μ) := by
  simp only [KeyedSys.lazy, Sys.ofPorts, ofPorts, Sys.mk.injEq, true_and]
  funext ⟨ko, t⟩ e
  rcases ko with _ | k <;> rcases e with e | e
  all_goals first
    | (simp [KeyedSys.lazyStep, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]; done)
    | (cases hu : SL.uses t e <;>
        simp [KeyedSys.lazyStep, hu, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind])
    | (cases hu : SR.uses t e <;>
        simp [KeyedSys.lazyStep, hu, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind])

/-- **Invariants of a lazily keyed system.** An invariant `Inv` of the states with an optional
key holds at every possible outcome of a step of `S.lazy μ` from a state satisfying it when it
does so with the key, at every key for an activation without the key that reads it, and without
the key for an activation that does not read it. -/
theorem lazy_pres (S : KeyedSys K τ E O) (μ : PMF K) (Inv : Option K × τ → Prop)
    (hsome : ∀ k t e, Inv (some k, t) → ∀ q, IsOutcome (S.step k t e) q → Inv (some k, q.1))
    (huses : ∀ t e, Inv (none, t) → S.uses t e = true →
      ∀ k q, IsOutcome (S.step k t e) q → Inv (some k, q.1))
    (hnone : ∀ t e, Inv (none, t) → S.uses t e = false →
      ∀ q, IsOutcome (S.step₀ t e) q → Inv (none, q.1)) :
    ∀ t e, Inv t → ∀ q, IsOutcome ((S.lazy μ).step t e) q → Inv q.1 := by
  rintro ⟨_ | k, t⟩ e hI q hq
  · cases hu : S.uses t e
    · rw [lazy_step_none_of_not_uses S μ hu, isOutcome_bind_pure_iff] at hq
      obtain ⟨p, hp, rfl⟩ := hq
      exact hnone t e hI hu p hp
    · rw [lazy_step_none_of_uses S μ hu] at hq
      obtain ⟨k, -, hq⟩ := isOutcome_bind hq
      obtain ⟨p, hp, rfl⟩ := isOutcome_bind_pure_iff.mp hq
      exact huses t e hI hu k p hp
  · simp only [lazy, lazyStep, isOutcome_bind_pure_iff] at hq
    obtain ⟨p, hp, rfl⟩ := hq
    exact hsome k t e hI p hp

/-- A lazily keyed system with deterministic steps `D` preserves an invariant `Inv` when each
activation does: with the key, at every key when the key is drawn, and without the key
otherwise. The step is then a draw followed by a point mass into `Inv`. -/
theorem lazy_pres_det (S : KeyedSys K τ E O) (μ : PMF K) (D : Option K → τ → E → τ × O)
    (hS : ∀ k t e, S.step k t e = SPComp.pure (D (some k) t e))
    (hS₀ : ∀ t e, S.step₀ t e = SPComp.pure (D none t e)) (Inv : Option K × τ → Prop)
    (hsome : ∀ k t e, Inv (some k, t) → Inv (some k, (D (some k) t e).1))
    (huses : ∀ t e, Inv (none, t) → S.uses t e = true → ∀ k, Inv (some k, (D (some k) t e).1))
    (hnone : ∀ t e, Inv (none, t) → S.uses t e = false → Inv (none, (D none t e).1))
    (t : Option K × τ) (e : E) (hI : Inv t) :
    ∃ (α : Type) (c : SPComp α) (g : α → (Option K × τ) × O),
      (S.lazy μ).step t e = SPComp.bind c (fun a => SPComp.pure (g a)) ∧ ∀ a, Inv (g a).1 :=
  exists_bind_pure_of_isOutcome _ (fun q : (Option K × τ) × O => Inv q.1) <| lazy_pres S μ Inv
    (fun k t e hI q hq => by
      rw [hS, isOutcome_pure_iff] at hq
      exact hq ▸ hsome k t e hI)
    (fun t e hI hu k q hq => by
      rw [hS, isOutcome_pure_iff] at hq
      exact hq ▸ huses t e hI hu k)
    (fun t e hI hu q hq => by
      rw [hS₀, isOutcome_pure_iff] at hq
      exact hq ▸ hnone t e hI hu)
    t e hI

end KeyedSys

end CatCrypt.Crypto.UCTransparent
