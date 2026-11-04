/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCTransparent
public import CatCryptCore.Crypto.UCChannel
public import CatCryptCore.Crypto.UCFeedbackLaws
public import CatCryptCore.Crypto.OracleSimulation
public import CatCryptCore.Crypto.Assumptions.AEAD
public import CatCryptCore.NonUniform.UnaryRules
public import CatCryptCore.Tactics.AutoDispatchExt

/-!
# Systems over oracle games and their reductions

A protocol that uses a cryptographic primitive only through its oracle interface is a
system of `CatCryptCore.Crypto.UCTransparent` built over an oracle game: every activation runs
an oracle program against the game's stateful oracle, whose key is sampled once. This file
compiles every environment of such a system into an oracle adversary of the game, and proves
that the distance between the system over the real game and the system over the ideal game is,
at every environment `Z`, the game advantage of the compiled adversary of `Z`.

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
* `OProt τ E O Q A` — a protocol whose activations are oracle programs with queries `Q` and
  answers `A` (`OracleAdv Q A (τ × O)`). `OProt.plug P orc s₀` is the system of `P` against
  the stateful oracle `orc` from state `s₀`; `OProt.oracle` is the protocol that forwards each
  event to the oracle as a query.
* `OProt.reduce P Z dist`, `OProt.reduction P Z` — the environment `Z` with the distinguisher
  `dist`, run against `P`, as an oracle adversary: it samples the steps of `Z` from its heap,
  runs the program of `P` for each event, and outputs the bit of the distinguisher.
* `KeyedGame Q A` — an oracle game: a key distribution, a keyed stateful oracle and an initial
  oracle state. `KeyedGame.accept G B` is the probability that the adversary `B` outputs `true`
  in `G`, and `KeyedGame.advantage G₀ G₁ B` the distance of the two acceptance probabilities.
* `OProt.sys P G` — the system of `P` over the game `G`: the key is sampled at the first
  activation and the oracle of `G` with that key answers the programs of `P`.

## Main results

* `Sys.DelayedDraw.view_eq` (delayed draw) — the view of `L` is the average over `k ← μ` of the
  views of `W k`.
* `Sys.delayedDraw_ofSlot` — a key drawn into a slot of the state at its first use is a
  delayed draw; `KeyedSys.delayedDraw_lazy` — so is the lazily keyed system.
* `KeyedSys.view_lazy` (lazy to eager sampling) — when the activations that do not read the
  key step as `step₀`, the view of the lazily keyed system is the average over `k ← μ` of the
  views of the system with key `k`: the sample moves to the start of the run at distance 0.
* `KeyedSys.ofPorts`, `KeyedSys.lazy_ofPorts` — the keyed system on two ports, and lazy sampling
  commutes with it; `KeyedSys.lazy_pres_det` — invariants of a lazily keyed system with
  deterministic steps.
* `OProt.prTrue_view_plug` — the acceptance probability of `Z` against `P.plug orc s₀` is the
  probability that `P.reduction Z` outputs `true` against `orc`.
* `OProt.prTrue_view_sys` — the acceptance probability of `Z` against `P.sys G` is
  `G.accept (P.reduction Z)`.
* `OProt.adv_sys`, `Realizes.ofOracleGame` — the advantage of `Z` between `P.sys G₀` and
  `P.sys G₁` is `KeyedGame.advantage G₀ G₁ (P.reduction Z)`, so `P.sys G₀` realizes
  `P.sys G₁`
  with that bound.
* `Realizes.ofAEAD` — for the authenticated-encryption games of
  `CatCryptCore.Crypto.Assumptions.AEAD`, the bound is `AEAD_CCA_Advantage D (P.reduction Z)`.
* `prTrue_bind_le_pmf_bind`, `prTrue_bind_le_runRand` — a run that samples from its heap is
  bounded by an oracle adversary that samples the same distribution, step by step.
* `prTrue_bind_liftPMF` — a bind after a lifted distribution accepts with the average of its
  continuations.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.NonUniform CatCrypt.Crypto.UCConcrete
open scoped ENNReal

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
      (S.lazy μ).step t e = SPComp.bind c (fun a => SPComp.pure (g a)) ∧ ∀ a, Inv (g a).1 := by
  obtain ⟨ko, t⟩ := t
  rcases ko with _ | k
  · cases hu : S.uses t e
    · exact ⟨Unit, SPComp.pure (), fun _ => ((none, (D none t e).1), (D none t e).2),
        by simp [KeyedSys.lazy, KeyedSys.lazyStep, hu, hS₀, SPComp.pure_bind],
        fun _ => hnone t e hI hu⟩
    · exact ⟨K, sampleFrom (ofPMF μ), fun k => ((some k, (D (some k) t e).1), (D (some k) t e).2),
        by simp [KeyedSys.lazy, KeyedSys.lazyStep, hu, hS, SPComp.pure_bind],
        fun k => huses t e hI hu k⟩
  · exact ⟨Unit, SPComp.pure (), fun _ => ((some k, (D (some k) t e).1), (D (some k) t e).2),
      by simp [KeyedSys.lazy, KeyedSys.lazyStep, hS, SPComp.pure_bind],
      fun _ => hsome k t e hI⟩

end KeyedSys

/-! ## Protocols over an oracle and their reductions -/

/-- A protocol over an oracle with queries `Q` and answers `A`: initial state `init`, and for
each state and event an oracle program `step t e` returning the new state and the output. -/
structure OProt (τ E O Q A : Type) where
  /-- Initial state. -/
  init : τ
  /-- One activation as an oracle program. -/
  step : τ → E → OracleAdv Q A (τ × O)

namespace OProt

variable {τ E O Q A S ζ : Type}

/-- The protocol that forwards each event to the oracle as a query and outputs the answer. -/
def oracle : OProt Unit Q A Q A where
  init := ()
  step _ q := .query q fun a => .ret ((), a)

/-- One activation of `P` against the stateful oracle `orc`: the program of `P` runs against
`orc` from the oracle state of `t`. -/
noncomputable def plugStep (P : OProt τ E O Q A) (orc : S → Q → PMF (A × S)) (t : τ × S)
    (e : E) : SPComp ((τ × S) × O) :=
  SPComp.bind (sampleFrom (ofPMF (OracleAdv.run orc (P.step t.1 e) t.2))) fun x =>
    SPComp.pure ((x.1.1, x.2), x.1.2)

/-- The system of `P` against the stateful oracle `orc` from the oracle state `s₀`. -/
noncomputable def plug (P : OProt τ E O Q A) (orc : S → Q → PMF (A × S)) (s₀ : S) :
    Sys (τ × S) E O where
  init := (P.init, s₀)
  step := P.plugStep orc

/-- The step of `P.plug orc s₀` (unfolding lemma of `plug`). -/
@[simp] theorem plug_step (P : OProt τ E O Q A) (orc : S → Q → PMF (A × S)) (s₀ : S) :
    (P.plug orc s₀).step = P.plugStep orc :=
  rfl

/-- The environment `Z` with the distinguisher `dist`, run against `P`, as an oracle adversary:
each of the `n` remaining activations samples the next event of `Z` from its heap, runs the
program of `P` on it from the protocol state `t`, and gives the output to `Z`; the output is
the bit of `dist`, and `false` when a step of `Z` or `dist` fails. -/
noncomputable def reduce (P : OProt τ E O Q A) (Z : Strat ζ E O) (dist : ζ → SPComp Bool) :
    ℕ → ζ → τ → Heap → OracleAdv Q A Bool
  | 0, z, _, h => .rand (dist z h) fun o => match o with
    | none => .ret false
    | some (b, _) => .ret b
  | n + 1, z, t, h => .rand (Z.next z h) fun o => match o with
    | none => .ret false
    | some ((z₁, e), h₁) => (P.step t e).bind fun p =>
      .rand (Z.obs z₁ p.2 h₁) fun o' => match o' with
        | none => .ret false
        | some (z₂, h₂) => reduce P Z dist n z₂ p.1 h₂

/-- The reduction of the environment `Z` against `P`: `reduce` from the initial states of `Z`
and `P` and the initial heap of `Z`, with the distinguisher of `Z`. -/
noncomputable def reduction (P : OProt τ E O Q A) (Z : Env (Strat ζ E O) ζ) :
    OracleAdv Q A Bool :=
  P.reduce Z.input Z.dist Z.input.rounds Z.input.init P.init Z.heap

/-- The acceptance probability of a run of `Z` against `P.plug orc s₀` is the probability that
`reduce` outputs `true` against `orc`. -/
theorem prTrue_loop_plug (P : OProt τ E O Q A) (orc : S → Q → PMF (A × S)) (s₀ : S)
    (Z : Strat ζ E O) (dist : ζ → SPComp Bool) :
    ∀ (n : ℕ) (z : ζ) (t : τ) (s : S) (b : Bool) (h : Heap),
      prTrue (SPComp.bind (SPComp.map Prod.fst
          (loop (P.plug orc s₀) (fun _ => false) Z n (z, (t, s), b))) dist) h =
        ((OracleAdv.run orc (P.reduce Z dist n z t h) s).map Prod.fst) true := by
  intro n
  induction n with
  | zero =>
    intro z t s b h
    simp only [loop, SPComp.map, SPComp.pure_bind]
    have hw := prTrue_bind_eq_weighted (dist z) SPComp.pure h
    rw [SPComp.bind_pure] at hw
    rw [hw, reduce, OracleAdv.run_rand, PMF.map_bind, PMF.bind_apply]
    refine tsum_congr fun o => ?_
    congr 1
    rcases o with _ | ⟨b', h'⟩
    · simp [-PMF.map_apply, PMF.pure_map]
    · cases b' <;> simp [prTrue_pure, -PMF.map_apply, PMF.pure_map]
  | succ n ih =>
    intro z t s b h
    simp only [loop, SPComp.map, SPComp.bind_assoc]
    rw [reduce, OracleAdv.run_rand, PMF.map_bind, PMF.bind_apply, prTrue_bind_eq_weighted]
    refine tsum_congr fun o => ?_
    congr 1
    rcases o with _ | ⟨⟨z₁, e⟩, h₁⟩
    · simp [-PMF.map_apply, PMF.pure_map]
    · dsimp only
      simp only [plug_step, plugStep, SPComp.bind_assoc, SPComp.pure_bind]
      rw [prTrue_bind_sampleFrom, OracleAdv.run_bind, PMF.map_bind, PMF.bind_apply]
      refine tsum_congr fun x => ?_
      rw [ofPMF_apply_some]
      congr 1
      rw [OracleAdv.run_rand, PMF.map_bind, PMF.bind_apply, prTrue_bind_eq_weighted]
      refine tsum_congr fun o' => ?_
      congr 1
      rcases o' with _ | ⟨z₂, h₂⟩
      · simp [-PMF.map_apply, PMF.pure_map]
      · simpa only [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind] using
          ih z₂ x.1.1 x.2 (b || false) h₂

/-- **The environment as an oracle adversary.** The acceptance probability of `Z` against
`P.plug orc s₀` is the probability that `P.reduction Z` outputs `true` against `orc` from
`s₀`. -/
theorem prTrue_view_plug (P : OProt τ E O Q A) (orc : S → Q → PMF (A × S)) (s₀ : S)
    (Z : Env (Strat ζ E O) ζ) :
    prTrue (SPComp.bind (view (P.plug orc s₀) Z.input) Z.dist) Z.heap =
      ((OracleAdv.run orc (P.reduction Z) s₀).map Prod.fst) true :=
  prTrue_loop_plug P orc s₀ Z.input Z.dist _ _ _ _ _ _

end OProt

/-! ## Oracle games -/

/-- An oracle game with queries `Q` and answers `A`: the key is sampled from `keyDist`, and the
adversary queries the stateful oracle `oracle k` from the state `init`. -/
structure KeyedGame (Q A : Type) where
  /-- Keys. -/
  Key : Type
  /-- Oracle states. -/
  State : Type
  /-- Key distribution. -/
  keyDist : PMF Key
  /-- The stateful oracle with a key. -/
  oracle : Key → State → Q → PMF (A × State)
  /-- Initial oracle state. -/
  init : State

namespace KeyedGame

variable {Q A : Type}

/-- The probability that the adversary `B` outputs `true` in the game `G`. -/
noncomputable def accept (G : KeyedGame Q A) (B : OracleAdv Q A Bool) : ℝ≥0∞ :=
  (G.keyDist.bind fun k => (OracleAdv.run (G.oracle k) B G.init).map Prod.fst) true

/-- The advantage of the adversary `B` between the games `G₀` and `G₁`. -/
noncomputable def advantage (G₀ G₁ : KeyedGame Q A) (B : OracleAdv Q A Bool) : ℝ≥0∞ :=
  absDiff (G₀.accept B) (G₁.accept B)

end KeyedGame

namespace OProt

variable {τ E O Q A ζ : Type}

/-- The protocol `P` over the game `G` as a keyed system: with key `k` each program of `P` runs
against the oracle of `G` with key `k`; every activation reads the key. -/
noncomputable def keyed (P : OProt τ E O Q A) (G : KeyedGame Q A) :
    KeyedSys G.Key (τ × G.State) E O where
  init := (P.init, G.init)
  step k := P.plugStep (G.oracle k)
  step₀ _ _ := SPComp.fail
  uses _ _ := true

/-- The system of `P` over the game `G`: the key is sampled from the key distribution of `G` at
the first activation, and the oracle of `G` with that key answers the programs of `P`. -/
noncomputable def sys (P : OProt τ E O Q A) (G : KeyedGame Q A) :
    Sys (Option G.Key × (τ × G.State)) E O :=
  (P.keyed G).lazy G.keyDist

/-- The acceptance probability of `Z` against the system of `P` over `G` is the probability
that `P.reduction Z` outputs `true` in `G`. -/
theorem prTrue_view_sys (P : OProt τ E O Q A) (G : KeyedGame Q A) (Z : Env (Strat ζ E O) ζ) :
    prTrue (SPComp.bind (view (P.sys G) Z.input) Z.dist) Z.heap = G.accept (P.reduction Z) := by
  rw [sys, KeyedSys.view_lazy _ _ (fun _ _ _ h => by simp [keyed] at h), SPComp.bind_assoc,
    prTrue_bind_sampleFrom, KeyedGame.accept, PMF.bind_apply]
  refine tsum_congr fun k => ?_
  rw [ofPMF_apply_some]
  congr 1
  exact P.prTrue_view_plug (G.oracle k) G.init Z

/-- The advantage of `Z` between the systems of `P` over `G₀` and over `G₁` is the advantage of
`P.reduction Z` between `G₀` and `G₁`. -/
theorem adv_sys (P : OProt τ E O Q A) (G₀ G₁ : KeyedGame Q A) (Z : Env (Strat ζ E O) ζ) :
    adv (P.sys G₀) (P.sys G₁) Z = KeyedGame.advantage G₀ G₁ (P.reduction Z) := by
  rw [adv_eq, prTrue_view_sys, prTrue_view_sys]
  rfl

end OProt

/-- **Realization over an oracle game.** The system of `P` over `G₀` realizes the system of `P`
over `G₁` with bound, at the environment `Z`, the advantage of the reduction `P.reduction Z`
between `G₀` and `G₁`. -/
theorem Realizes.ofOracleGame {τ E O Q A : Type} (P : OProt τ E O Q A)
    (G₀ G₁ : KeyedGame Q A) :
    Realizes (P.sys G₀) (P.sys G₁) fun _ Z => KeyedGame.advantage G₀ G₁ (P.reduction Z) :=
  fun _ Z => le_of_eq (P.adv_sys G₀ G₁ Z)

/-! ## Authenticated encryption -/

section AEAD

open CatCrypt.Crypto.Assumptions

variable {W : Type} [SampleableType W] {C : Type} [SampleableType C]

/-- The real authenticated-encryption game of `D`: a uniform key and the oracle
`aeadRealOracle D`. -/
noncomputable def aeadRealGame (D : AEADDef W C) :
    KeyedGame (AEAD_CCA_Query W C) (AEAD_CCA_Answer W C) where
  Key := W
  State := Unit
  keyDist := PMF.uniformFintype W
  oracle := aeadRealOracle D
  init := ()

/-- The ideal authenticated-encryption game: no key, and the oracle `aeadIdealOracle` from the
empty log. -/
noncomputable def aeadIdealGame : KeyedGame (AEAD_CCA_Query W C) (AEAD_CCA_Answer W C) where
  Key := Unit
  State := List ((W × W) × C)
  keyDist := PMF.pure ()
  oracle _ := aeadIdealOracle
  init := []

/-- The advantage between the real and the ideal authenticated-encryption games is
`AEAD_CCA_Advantage`. -/
theorem advantage_aeadGame (D : AEADDef W C) (B : AEAD_CCA_Adversary W C) :
    KeyedGame.advantage (aeadRealGame D) aeadIdealGame B = AEAD_CCA_Advantage D B := by
  simp only [KeyedGame.advantage, KeyedGame.accept, AEAD_CCA_Advantage, Advantage,
    AEAD_CCA_Game_Real, AEAD_CCA_Game_Ideal, prTrue_liftPMF, aeadRealGame, aeadIdealGame,
    PMF.pure_bind, absDiff]

/-- **Realization over authenticated encryption.** A protocol `P` over the authenticated
encryption oracles, run over the real oracles of `D` with a key sampled at the first
activation, realizes `P` over the ideal oracles with bound, at the environment `Z`, the
authenticated-encryption advantage of the reduction `P.reduction Z`. -/
theorem Realizes.ofAEAD {τ E O : Type}
    (P : OProt τ E O (AEAD_CCA_Query W C) (AEAD_CCA_Answer W C)) (D : AEADDef W C) :
    Realizes (P.sys (aeadRealGame D)) (P.sys aeadIdealGame) fun _ Z =>
      AEAD_CCA_Advantage D (P.reduction Z) :=
  fun _ Z => (le_of_eq (P.adv_sys _ _ Z)).trans_eq (advantage_aeadGame D _)

end AEAD

/-! ## Bounding a run by an oracle adversary -/

/-- A bind after `c` accepts from the heap `h` with at most the probability of `true` in the
distribution that samples `o` from `c h` and continues with `F o`, when every continuation of
the bind is dominated by the corresponding continuation `F`. -/
theorem prTrue_bind_le_pmf_bind {α : Type} (c : SPComp α) (f : α → SPComp Bool) (h : Heap)
    (F : Option (α × Heap) → PMF Bool)
    (hF : ∀ a h', prTrue (f a) h' ≤ F (some (a, h')) true) :
    prTrue (SPComp.bind c f) h ≤ (PMF.bind (c h) F) true := by
  rw [prTrue_bind_eq_weighted, PMF.bind_apply]
  refine ENNReal.tsum_le_tsum fun o => ?_
  rcases o with _ | ⟨a, h'⟩
  · simp
  · gcongr
    exact hF a h'

/-- A bind after `c` accepts from the heap `h` with at most the probability that an oracle
adversary that samples from `c h` produces an output accepted by `w`, when every continuation
of the bind is dominated by the corresponding continuation of the adversary. -/
theorem prTrue_bind_le_runRand {α Q A β S : Type} (c : SPComp α) (f : α → SPComp Bool)
    (h : Heap) (orc : S → Q → PMF (A × S)) (k : Option (α × Heap) → OracleAdv Q A β) (s : S)
    (w : β × S → Bool)
    (hk : ∀ a h', prTrue (f a) h' ≤ ((OracleAdv.run orc (k (some (a, h'))) s).map w) true) :
    prTrue (SPComp.bind c f) h ≤ ((OracleAdv.run orc (.rand (c h) k) s).map w) true := by
  rw [OracleAdv.run_rand, PMF.map_bind]
  exact prTrue_bind_le_pmf_bind c f h _ hk

/-- A bind after a lifted distribution `p` accepts with the `p`-average of the acceptance
probabilities of its continuations. -/
theorem prTrue_bind_liftPMF {α : Type} (p : PMF α) (f : α → SPComp Bool) (h : Heap) :
    prTrue (SPComp.bind (liftPMF p) f) h = ∑' a, p a * prTrue (f a) h := by
  simp only [prTrue, liftPMF_bind_apply, PMF.bind_apply]
  rw [ENNReal.tsum_comm]
  simp_rw [ENNReal.tsum_mul_left]

end CatCrypt.Crypto.UCTransparent
