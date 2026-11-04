/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCFeedback
public import CatCryptCore.Crypto.UCGlobal
public import CatCryptCore.Prob.Support

/-!
# The trace laws of bounded feedback

The loopback `Sys.loopback S n cut` of a system on `(E ⊕ X, O ⊕ X)` satisfies the axioms of a
trace (Joyal–Street–Verity) at distance `0`, each as a pair of realizations at bound `0`.
For every fuel `n`:

* vanishing for the empty wire (`loopback_empty`),
* superposing with a parallel component, up to the reassociation of the sum interfaces
  `parWireEv`, `parWireOut` (`loopback_par`),
* naturality in the outer ports for relabellings by pure maps (`loopback_mapPorts`),
* dinaturality in the wire for a pure map on the wire (`loopback_dinat`).

The remaining laws hold when the fuel suffices for every activation. The predicate
`Sys.ExitsBy S P n g t` states that the activation of the loopback from the event `g` of `S`
in the state `t` ends with an output of `S` on the outer port within `n + 1` calls on every
possible outcome, at a state satisfying `P`; `Sys.ExitsWithin S Inv k` states this for every
outer event from every state satisfying `Inv`. Under it:

* fuel independence: `S.loopback n cut` and `S.loopback k cut'` agree for `k ≤ n`
  (`loopback_fuel_indep`),
* yanking: the loopback of the swap of the two copies of `X` with fuel at least `1` is the
  identity of `X` (`loopback_yank`),
* vanishing for a sum of wires: two nested loopbacks agree with one loopback along the sum of
  the wires, when the flat loopback exits within `p` and both nested fuels are at least `p`
  (`loopback_loopback`).

The activation of the loopback is the recursion `Sys.fbRun` over the steps of `S`
(`Sys.loopback_step`).

These laws and the invariants of reactive systems are stated over the possible outcomes
`IsOutcome c a` of a computation. The possible outcomes of a point mass, a map and a bind with a
pure head are computed by `isOutcome_pure_iff`, `isOutcome_map_iff`, `isOutcome_bind_pure_iff`
and `isOutcome_bind_iff_of_isPure` (a uniform draw: `isOutcome_bind_sample_iff`), and the
universal statements over them by `forall_isOutcome_pure`, `forall_isOutcome_map` and
`forall_isOutcome_bind_of_forall`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open scoped ENNReal

/-! ## Possible outcomes of a computation -/

/-- The value `a` is a possible outcome of `c`: from some initial heap, `c` returns `a` with
some final heap with nonzero probability. -/
def IsOutcome {α : Type} (c : SPComp α) (a : α) : Prop :=
  ∃ hp hp', c hp (some (a, hp')) ≠ 0

section Outcome

variable {α β : Type}

/-- The possible outcomes of a pure computation. -/
theorem isOutcome_pure {a b : α} (h : IsOutcome (SPComp.pure a) b) : a = b := by
  obtain ⟨hp, hp', h⟩ := h
  have := (SDistr.mem_support_pure_iff _ _).mp h
  grind

/-- A possible outcome of a bind is a possible outcome of the continuation at a possible
outcome of the head. -/
@[grind →] theorem isOutcome_bind {c : SPComp α} {f : α → SPComp β} {b : β}
    (h : IsOutcome (SPComp.bind c f) b) : ∃ a, IsOutcome c a ∧ IsOutcome (f a) b := by
  obtain ⟨hp, hp', h⟩ := h
  obtain ⟨⟨a, h₁⟩, ha, hb⟩ := SDistr.bind_support_witness h
  exact ⟨a, ⟨hp, h₁, ha⟩, ⟨h₁, hp', hb⟩⟩

/-- The image of a possible outcome is a possible outcome of the map. -/
theorem isOutcome_map {c : SPComp α} {a : α} (f : α → β) (h : IsOutcome c a) :
    IsOutcome (SPComp.map f c) (f a) := by
  obtain ⟨hp, hp', h⟩ := h
  refine ⟨hp, hp', fun h0 => h ?_⟩
  simp only [SPComp.map, SPComp.bind_def, SPComp.pure_def, SDistr.bind, PMF.bind_apply,
    ENNReal.tsum_eq_zero] at h0
  have := h0 (some (a, hp'))
  classical
  simpa using this

/-- Two continuations that agree at the possible outcomes of `c` give equal binds. -/
theorem bind_congr_isOutcome {c : SPComp α} {f g : α → SPComp β}
    (h : ∀ a, IsOutcome c a → f a = g a) : SPComp.bind c f = SPComp.bind c g := by
  funext hp
  refine SDistr.bind_congr_support fun p hp₂ => ?_
  obtain ⟨a, h₁⟩ := p
  dsimp only
  rw [h a ⟨hp, h₁, hp₂⟩]

/-- A computation whose possible outcomes satisfy `P` factors through the subtype of `P`. -/
theorem exists_bind_pure_of_isOutcome (c : SPComp α) (P : α → Prop)
    (h : ∀ a, IsOutcome c a → P a) :
    ∃ (γ : Type) (c' : SPComp γ) (g : γ → α),
      c = SPComp.bind c' (fun b => SPComp.pure (g b)) ∧ ∀ b, P (g b) := by
  classical
  refine ⟨{a // P a}, fun hp => (c hp).bind fun p =>
    if hP : P p.1 then SDistr.pure (⟨p.1, hP⟩, p.2) else SDistr.fail, Subtype.val, ?_,
    fun b => b.2⟩
  funext hp
  change c hp = (((c hp).bind fun p => if hP : P p.1 then
    SDistr.pure ((⟨p.1, hP⟩ : {a // P a}), p.2) else SDistr.fail).bind fun q =>
      SDistr.pure ((q.1 : α), q.2))
  rw [SDistr.bind_assoc]
  refine (SDistr.bind_pure (c hp)).symm.trans (SDistr.bind_congr_support fun p hp₂ => ?_)
  obtain ⟨a, h₁⟩ := p
  have ha : P a := h a ⟨hp, h₁, hp₂⟩
  grind

/-- The possible outcomes of a point mass: its value. -/
@[simp, grind =] theorem isOutcome_pure_iff {a b : α} : IsOutcome (SPComp.pure a) b ↔ a = b := by
  refine ⟨isOutcome_pure, fun h => ⟨Heap.empty, Heap.empty, ?_⟩⟩
  subst h
  simp [SPComp.pure_def, SDistr.pure, PMF.pure_apply]

/-- The possible outcomes of a map: the images of the possible outcomes. -/
@[simp, grind =] theorem isOutcome_map_iff {c : SPComp α} {f : α → β} {b : β} :
    IsOutcome (SPComp.map f c) b ↔ ∃ a, IsOutcome c a ∧ f a = b := by
  refine ⟨fun h => ?_, fun ⟨a, ha, hb⟩ => hb ▸ isOutcome_map f ha⟩
  obtain ⟨a, ha, hb⟩ := isOutcome_bind h
  exact ⟨a, ha, isOutcome_pure hb⟩

/-- A possible outcome of a map is the image of a possible outcome. -/
@[deprecated isOutcome_map_iff +typeChanged (since := "2026-11-04")]
theorem exists_of_isOutcome_map {c : SPComp α} {h : α → β} {b : β}
    (hb : IsOutcome (SPComp.map h c) b) : ∃ a, IsOutcome c a ∧ h a = b :=
  isOutcome_map_iff.mp hb

/-- The possible outcomes of a bind with a point-mass continuation. -/
@[simp] theorem isOutcome_bind_pure_iff {c : SPComp α} {f : α → β} {b : β} :
    IsOutcome (SPComp.bind c fun a => SPComp.pure (f a)) b ↔ ∃ a, IsOutcome c a ∧ f a = b :=
  isOutcome_map_iff

/-- **The possible outcomes of a bind with a pure head**: the possible outcomes of the
continuation at the possible outcomes of the head. A pure head returns each of its values from
every heap, so the continuation runs from every heap. -/
theorem isOutcome_bind_iff_of_isPure {c : SPComp α} {f : α → SPComp β} {b : β}
    (hc : SPComp.IsPure c) :
    IsOutcome (SPComp.bind c f) b ↔ ∃ a, IsOutcome c a ∧ IsOutcome (f a) b := by
  refine ⟨isOutcome_bind, fun ⟨a, ⟨h₀, h₀', ha⟩, ⟨h₁, h₁', hb⟩⟩ => ⟨h₁, h₁', ?_⟩⟩
  obtain ⟨d, hd⟩ := hc
  have hne : ∀ {γ δ : Type} {e : SDistr γ} {g : γ → SDistr δ} {x : γ} {y : δ},
      e (some x) ≠ 0 → g x (some y) ≠ 0 → (e.bind g) (some y) ≠ 0 := by
    intro γ δ e g x y hx hy
    unfold SDistr.bind
    rw [PMF.bind_apply, ne_eq, ENNReal.tsum_eq_zero]
    push Not
    exact ⟨some x, mul_ne_zero hx hy⟩
  rw [hd] at ha
  obtain ⟨a', hda, hp⟩ := SDistr.bind_support_witness ha
  obtain ⟨rfl, -⟩ := Prod.mk.inj ((SDistr.mem_support_pure_iff _ _).mp hp)
  have hc₁ : c h₁ (some (a', h₁)) ≠ 0 := by
    rw [hd]
    exact hne hda ((SDistr.mem_support_pure_iff _ _).mpr rfl)
  exact hne (g := fun p : α × Heap => f p.1 p.2) hc₁ hb

/-- The possible outcomes of a bind with a uniform draw: the possible outcomes of the
continuation at any value. -/
theorem isOutcome_bind_sample_iff {γ : Type} [Fintype γ] [Nonempty γ] {f : γ → SPComp β}
    {b : β} : IsOutcome (SPComp.bind (SPComp.sample γ) f) b ↔ ∃ a, IsOutcome (f a) b := by
  rw [isOutcome_bind_iff_of_isPure (SPComp.sample_isPure γ)]
  refine ⟨fun ⟨a, _, h⟩ => ⟨a, h⟩, fun ⟨a, h⟩ => ⟨a, ⟨Heap.empty, Heap.empty, ?_⟩, h⟩⟩
  simp only [SPComp.sample, SDistr.uniform]
  unfold SDistr.bind
  rw [PMF.bind_apply, ne_eq, ENNReal.tsum_eq_zero]
  push Not
  refine ⟨some a, mul_ne_zero ?_ ((SDistr.mem_support_pure_iff _ _).mpr rfl)⟩
  simp [PMF.map_apply]

/-- A property of every possible outcome of a point mass is a property of its value. -/
theorem forall_isOutcome_pure {P : α → Prop} {a : α} :
    (∀ b, IsOutcome (SPComp.pure a) b → P b) ↔ P a := by
  simp

/-- A property of every possible outcome of a map is a property of the image of every possible
outcome. -/
theorem forall_isOutcome_map {P : β → Prop} {c : SPComp α} {f : α → β} :
    (∀ b, IsOutcome (SPComp.map f c) b → P b) ↔ ∀ a, IsOutcome c a → P (f a) := by
  simp

/-- A property of the possible outcomes of every continuation is a property of the possible
outcomes of the bind. The converse fails: a continuation may run from a heap the head never
reaches. -/
theorem forall_isOutcome_bind_of_forall {P : β → Prop} {c : SPComp α} {f : α → SPComp β}
    (h : ∀ a, IsOutcome c a → ∀ b, IsOutcome (f a) b → P b) :
    ∀ b, IsOutcome (SPComp.bind c f) b → P b := fun _ hb => by
  obtain ⟨a, ha, hab⟩ := isOutcome_bind hb
  exact h a ha _ hab

@[deprecated (since := "2026-11-04")] alias forall_isOutcome_bind := forall_isOutcome_bind_of_forall

end Outcome

namespace Sys

variable {τ υ E O E' O' EG OG X Y : Type}

/-- Unfolding lemma of `Sys.mapPorts`: a step on the event `e`. -/
theorem mapPorts_step (S : Sys τ EG OG) (fe : E → EG) (fo : OG → O) (t : τ) (e : E) :
    (S.mapPorts fe fo).step t e = SPComp.map (fun q => (q.1, fo q.2)) (S.step t (fe e)) :=
  rfl

/-! ## The activation of the loopback -/

/-- The rest of an activation of the loopback of `S` from the event `g` of `S` in the state `t`,
with `n` further calls allowed: an output `inl o` of `S` ends the activation with `o`; an output
`inr x` is the next event `inr x`, or ends the activation with `cut x` when no call is left. -/
noncomputable def fbRun (S : Sys τ (E ⊕ X) (O ⊕ X)) (cut : X → O) :
    ℕ → E ⊕ X → τ → SPComp (τ × O)
  | 0, g, t => SPComp.bind (S.step t g) fun q =>
      Sum.elim (fun o => SPComp.pure (q.1, o)) (fun x => SPComp.pure (q.1, cut x)) q.2
  | n + 1, g, t => SPComp.bind (S.step t g) fun q =>
      Sum.elim (fun o => SPComp.pure (q.1, o)) (fun x => fbRun S cut n (.inr x) q.1) q.2

/-- The drive of the feedback hybrid from a subroutine event is `fbRun`. -/
theorem drive_fbHybrid (S : Sys τ (E ⊕ X) (O ⊕ X)) (cut : X → O) (k : ℕ) :
    ∀ (n : ℕ) (g : E ⊕ X) (t : τ),
      (MultiHybrid.fbHybrid k cut).drive S n () (.inl g) t =
        SPComp.map (fun p => ((), p.1, p.2)) (fbRun S cut n g t) := by
  intro n
  induction n with
  | zero =>
    intro g t
    simp only [MultiHybrid.drive, fbRun, SPComp.map, SPComp.bind_assoc]
    congr 1; funext q; rcases q with ⟨t', o | x⟩ <;> simp [MultiHybrid.fbHybrid]
  | succ n ih =>
    intro g t
    simp only [MultiHybrid.drive, fbRun, SPComp.map, SPComp.bind_assoc]
    congr 1; funext q; rcases q with ⟨t', o | x⟩
    · simp [MultiHybrid.fbHybrid, MultiHybrid.drive]
    · rw [show (MultiHybrid.fbHybrid k cut).resume () (.inr x) =
        SPComp.pure ((), .inl (.inr x)) from rfl, SPComp.pure_bind, ih]
      rfl

/-- A step of the loopback is the activation `fbRun` from the outer event. -/
theorem loopback_step (S : Sys τ (E ⊕ X) (O ⊕ X)) (n : ℕ) (cut : X → O) (u : Unit × τ)
    (e : E) : (S.loopback n cut).step u e =
      SPComp.map (fun p => (((), p.1), p.2)) (fbRun S cut n (.inl e) u.2) := by
  change SPComp.bind (SPComp.pure ((), Sum.inl (Sum.inl e))) (fun r => SPComp.bind
    ((MultiHybrid.fbHybrid n cut).drive S n r.1 r.2 u.2) fun p =>
      SPComp.pure ((p.1, p.2.1), p.2.2)) = _
  rw [SPComp.pure_bind, drive_fbHybrid]
  simp [SPComp.map]

/-! ## Laws for every fuel -/

/-- **Vanishing for the empty wire.** The loopback along the empty wire is the system on the
outer ports. -/
theorem loopback_empty (S : Sys τ (E ⊕ Empty) (O ⊕ Empty)) (n : ℕ) (cut : Empty → O) :
    Realizes (S.loopback n cut) (S.mapPorts Sum.inl (Sum.elim id Empty.elim)) (fun _ _ => 0) ∧
    Realizes (S.mapPorts Sum.inl (Sum.elim id Empty.elim)) (S.loopback n cut)
      (fun _ _ => 0) := by
  have hrun : ∀ e t, fbRun S cut n (.inl e) t =
      SPComp.map (fun q => (q.1, Sum.elim id Empty.elim q.2)) (S.step t (.inl e)) := by
    intro e t
    cases n <;>
      (simp only [fbRun, SPComp.map]; congr 1; funext q; rcases q with ⟨t', o | x⟩; rfl
       exact x.elim)
  have h : Realizes (S.loopback n cut) (S.mapPorts Sum.inl (Sum.elim id Empty.elim))
      (fun _ _ => 0) :=
    realizes_zero_of_stepMap _ _ Prod.snd rfl fun u e => by
      simp only [loopback_step, hrun, Sys.mapPorts, Sys.relabel, SPComp.map_comp]
      rfl
  exact ⟨h, fun ζ => (h ζ).symm⟩

/-- The events of `(E ⊕ E') ⊕ X` as events of `(E ⊕ X) ⊕ E'`. -/
def parWireEv : (E ⊕ E') ⊕ X → (E ⊕ X) ⊕ E'
  | .inl (.inl e) => .inl (.inl e)
  | .inl (.inr e) => .inr e
  | .inr x => .inl (.inr x)

/-- The outputs of `(O ⊕ X) ⊕ O'` as outputs of `(O ⊕ O') ⊕ X`. -/
def parWireOut : (O ⊕ X) ⊕ O' → (O ⊕ O') ⊕ X
  | .inl (.inl o) => .inl (.inl o)
  | .inl (.inr x) => .inr x
  | .inr o => .inl (.inr o)

/-- **Superposing.** The loopback of a parallel composition along the wire of its left
component is the parallel composition of the loopback of the left component with the right
component. -/
theorem loopback_par (S : Sys τ (E ⊕ X) (O ⊕ X)) (T : Sys υ E' O') (n : ℕ) (cut : X → O) :
    Realizes (((S.par T).mapPorts parWireEv parWireOut).loopback n (Sum.inl ∘ cut))
      ((S.loopback n cut).par T) (fun _ _ => 0) ∧
    Realizes ((S.loopback n cut).par T)
      (((S.par T).mapPorts parWireEv parWireOut).loopback n (Sum.inl ∘ cut))
      (fun _ _ => 0) := by
  have hrun : ∀ (m : ℕ) (g : E ⊕ X) (t : τ) (v : υ),
      fbRun ((S.par T).mapPorts parWireEv parWireOut) (Sum.inl ∘ cut) m (Sum.map Sum.inl id g)
        (t, v) = SPComp.map (fun p => ((p.1, v), Sum.inl p.2)) (fbRun S cut m g t) := by
    have hstep : ∀ (g : E ⊕ X) (t : τ) (v : υ),
        ((S.par T).mapPorts parWireEv parWireOut).step (t, v) (Sum.map Sum.inl id g) =
          SPComp.map (fun q => ((q.1, v), Sum.map Sum.inl id q.2)) (S.step t g) := by
      intro g t v
      have hg : parWireEv (Sum.map Sum.inl id g : (E ⊕ E') ⊕ X) = Sum.inl g := by
        rcases g with e | x <;> rfl
      simp only [Sys.mapPorts, Sys.relabel, hg, Sys.par_step_inl, SPComp.map_comp]
      congr 1; funext q; rcases q with ⟨t', o | x⟩ <;> rfl
    intro m
    induction m with
    | zero =>
      intro g t v
      simp only [fbRun, hstep, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
      congr 1; funext q; rcases q with ⟨t', o | x⟩ <;> simp
    | succ m ih =>
      intro g t v
      simp only [fbRun, hstep, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
      congr 1; funext q; rcases q with ⟨t', o | x⟩
      · simp
      · have := ih (.inr x) t' v
        simp only [Sum.map_inr, id] at this
        simp only [Sum.map_inr, id, Sum.elim_inr, this, SPComp.map]
  have hrunR : ∀ (m : ℕ) (e : E') (t : τ) (v : υ),
      fbRun ((S.par T).mapPorts parWireEv parWireOut) (Sum.inl ∘ cut) m (.inl (.inr e))
        (t, v) = SPComp.map (fun q => ((t, q.1), Sum.inr q.2)) (T.step v e) := by
    intro m e t v
    cases m <;> simp [fbRun, Sys.mapPorts, Sys.relabel, parWireEv, parWireOut, SPComp.map]
  have h : Realizes (((S.par T).mapPorts parWireEv parWireOut).loopback n (Sum.inl ∘ cut))
      ((S.loopback n cut).par T) (fun _ _ => 0) := by
    refine realizes_zero_of_stepMap _ _ (fun s => ((s.1, s.2.1), s.2.2)) rfl ?_
    rintro ⟨u, t, v⟩ (e | e)
    · have := hrun n (.inl e) t v
      simp only [Sum.map_inl] at this
      rw [loopback_step, Sys.par_step_inl, loopback_step, this]
      simp only [SPComp.map_comp]
      rfl
    · rw [loopback_step, Sys.par_step_inr, hrunR, SPComp.map_comp, SPComp.map_comp]
      rfl
  exact ⟨h, fun ζ => (h ζ).symm⟩

/-- **Naturality.** The loopback commutes with relabelling the outer ports by pure maps. -/
theorem loopback_mapPorts (S : Sys τ (EG ⊕ X) (OG ⊕ X)) (f : E → EG) (g : OG → O) (n : ℕ)
    (cut : X → OG) :
    Realizes ((S.mapPorts (Sum.map f id) (Sum.map g id)).loopback n (g ∘ cut))
      ((S.loopback n cut).mapPorts f g) (fun _ _ => 0) ∧
    Realizes ((S.loopback n cut).mapPorts f g)
      ((S.mapPorts (Sum.map f id) (Sum.map g id)).loopback n (g ∘ cut)) (fun _ _ => 0) := by
  have hrun : ∀ (m : ℕ) (ev : E ⊕ X) (t : τ),
      fbRun (S.mapPorts (Sum.map f id) (Sum.map g id)) (g ∘ cut) m ev t =
        SPComp.map (fun p => (p.1, g p.2)) (fbRun S cut m (Sum.map f id ev) t) := by
    intro m
    induction m with
    | zero =>
      intro ev t
      simp only [fbRun, mapPorts_step, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
      congr 1; funext q; rcases q with ⟨t', o | x⟩ <;> simp
    | succ m ih =>
      intro ev t
      simp only [fbRun, mapPorts_step, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
      congr 1; funext q; rcases q with ⟨t', o | x⟩ <;> simp [ih, SPComp.map]
  refine realizes_zero_of_step_eq _ _ rfl fun u e => ?_
  have := hrun n (.inl e) u.2
  simp only [Sum.map_inl] at this
  rw [loopback_step, this]
  simp only [Sys.mapPorts, Sys.relabel, loopback_step, SPComp.map_comp]
  rfl

/-- **Dinaturality.** For a pure map `h` on the wire, applying `h` to the wire output of `S`
before the loopback along `X` is applying it to the wire event before the loopback along
`Y`. -/
theorem loopback_dinat (S : Sys τ (E ⊕ X) (O ⊕ Y)) (h : Y → X) (n : ℕ) (cut : X → O) :
    Realizes ((S.mapPorts id (Sum.map id h)).loopback n cut)
      ((S.mapPorts (Sum.map id h) id).loopback n (cut ∘ h)) (fun _ _ => 0) ∧
    Realizes ((S.mapPorts (Sum.map id h) id).loopback n (cut ∘ h))
      ((S.mapPorts id (Sum.map id h)).loopback n cut) (fun _ _ => 0) := by
  have hrun : ∀ (m : ℕ) (ev : E ⊕ Y) (t : τ),
      fbRun (S.mapPorts id (Sum.map id h)) cut m (Sum.map id h ev) t =
        fbRun (S.mapPorts (Sum.map id h) id) (cut ∘ h) m ev t := by
    intro m
    induction m with
    | zero =>
      intro ev t
      simp only [fbRun, mapPorts_step, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
      congr 1; funext q; rcases q with ⟨t', o | x⟩ <;> simp
    | succ m ih =>
      intro ev t
      simp only [fbRun, mapPorts_step, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
      congr 1; funext q; rcases q with ⟨t', o | x⟩ <;> simp [← ih]
  refine realizes_zero_of_step_eq _ _ rfl fun u e => ?_
  have := hrun n (.inl e) u.2
  simp only [Sum.map_inl, id_eq] at this
  rw [loopback_step, loopback_step, this]

/-! ## Adequate fuel -/

/-- The activation of the loopback of `S` from the event `g` in the state `t` ends within
`n + 1` calls of `S` on every possible outcome, with an output on the outer port at a state
satisfying `P`. -/
def ExitsBy (S : Sys τ (E ⊕ X) (O ⊕ X)) (P : τ → Prop) : ℕ → E ⊕ X → τ → Prop
  | 0, g, t => ∀ q, IsOutcome (S.step t g) q → Sum.elim (fun _ => P q.1) (fun _ => False) q.2
  | n + 1, g, t => ∀ q, IsOutcome (S.step t g) q →
      Sum.elim (fun _ => P q.1) (fun x => ExitsBy S P n (.inr x) q.1) q.2

/-- Fuel `k` is adequate for `S` on the invariant `Inv`: from every state satisfying `Inv`, every
activation of the loopback ends within `k + 1` calls of `S` at a state satisfying `Inv`. -/
def ExitsWithin (S : Sys τ (E ⊕ X) (O ⊕ X)) (Inv : τ → Prop) (k : ℕ) : Prop :=
  ∀ t, Inv t → ∀ e, ExitsBy S Inv k (.inl e) t

/-- `ExitsBy` is monotone in the fuel. -/
theorem ExitsBy.mono {S : Sys τ (E ⊕ X) (O ⊕ X)} {P : τ → Prop} {k n : ℕ} (hkn : k ≤ n)
    {g : E ⊕ X} {t : τ} (h : S.ExitsBy P k g t) : S.ExitsBy P n g t := by
  have hsucc : ∀ (k : ℕ) (g : E ⊕ X) (t : τ), S.ExitsBy P k g t → S.ExitsBy P (k + 1) g t := by
    intro k
    induction k with
    | zero =>
      intro g t h q hq
      have hq' := h q hq
      rcases q with ⟨t', o | x⟩
      · exact hq'
      · exact False.elim hq'
    | succ k ih =>
      intro g t h q hq
      have hq' := h q hq
      rcases q with ⟨t', o | x⟩
      · exact hq'
      · exact ih _ _ hq'
  induction hkn with
  | refl => exact h
  | step _ ih => exact hsucc _ _ _ ih

/-- With adequate fuel `k`, the activation does not depend on a larger fuel or on the cut-off
map. -/
theorem fbRun_eq_of_exitsBy {S : Sys τ (E ⊕ X) (O ⊕ X)} {P : τ → Prop} (cut cut' : X → O) :
    ∀ (k : ℕ) {n : ℕ} {g : E ⊕ X} {t : τ}, S.ExitsBy P k g t → k ≤ n →
      fbRun S cut n g t = fbRun S cut' k g t := by
  intro k
  induction k with
  | zero =>
    intro n g t h _
    cases n <;>
    · simp only [fbRun]
      refine bind_congr_isOutcome fun q hq => ?_
      have hq' := h q hq
      rcases q with ⟨t', o | x⟩
      · rfl
      · exact False.elim hq'
  | succ k ih =>
    intro n g t h hkn
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    simp only [fbRun]
    refine bind_congr_isOutcome fun q hq => ?_
    have hq' := h q hq
    rcases q with ⟨t', o | x⟩
    · rfl
    · exact ih hq' (by omega)

/-- With adequate fuel `k`, every possible outcome of the activation is at a state satisfying
`P`. -/
theorem fbRun_isOutcome_of_exitsBy {S : Sys τ (E ⊕ X) (O ⊕ X)} {P : τ → Prop} (cut : X → O) :
    ∀ (k : ℕ) {g : E ⊕ X} {t : τ}, S.ExitsBy P k g t →
      ∀ p, IsOutcome (fbRun S cut k g t) p → P p.1 := by
  intro k
  induction k with
  | zero =>
    intro g t h p hp
    simp only [fbRun] at hp
    obtain ⟨q, hq, hpq⟩ := isOutcome_bind hp
    have hq' := h q hq
    rcases q with ⟨t', o | x⟩
    · obtain rfl := isOutcome_pure hpq
      exact hq'
    · exact False.elim hq'
  | succ k ih =>
    intro g t h p hp
    simp only [fbRun] at hp
    obtain ⟨q, hq, hpq⟩ := isOutcome_bind hp
    have hq' := h q hq
    rcases q with ⟨t', o | x⟩
    · obtain rfl := isOutcome_pure hpq
      exact hq'
    · exact ih hq' p hpq

/-- The possible outcomes of a loopback step are at states whose second component satisfies
`P` when the activation exits with adequate fuel. -/
theorem exists_loopback_step_factor {S : Sys τ (E ⊕ X) (O ⊕ X)} {Inv : τ → Prop} {k n : ℕ}
    (cut : X → O) (hkn : k ≤ n) (hex : S.ExitsWithin Inv k) (u : Unit × τ) (e : E)
    (hu : Inv u.2) :
    ∃ (α : Type) (c : SPComp α) (g : α → (Unit × τ) × O),
      (S.loopback n cut).step u e = SPComp.bind c (fun a => SPComp.pure (g a)) ∧
        ∀ a, Inv (g a).1.2 := by
  refine exists_bind_pure_of_isOutcome _ (fun p : (Unit × τ) × O => Inv p.1.2) fun p hp => ?_
  rw [loopback_step, fbRun_eq_of_exitsBy cut cut k (hex u.2 hu e) hkn] at hp
  obtain ⟨a, ha, hpa⟩ := isOutcome_bind hp
  have := isOutcome_pure hpa
  subst this
  exact fbRun_isOutcome_of_exitsBy cut k (hex u.2 hu e) a ha

/-- **Fuel independence.** When fuel `k` is adequate on an invariant that holds initially, the
loopbacks with fuel `n ≥ k` and with fuel `k` agree, whatever their cut-off maps. -/
theorem loopback_fuel_indep (S : Sys τ (E ⊕ X) (O ⊕ X)) (Inv : τ → Prop) {k n : ℕ}
    (hkn : k ≤ n) (cut cut' : X → O) (hinit : Inv S.init) (hex : S.ExitsWithin Inv k) :
    Realizes (S.loopback n cut) (S.loopback k cut') (fun _ _ => 0) ∧
    Realizes (S.loopback k cut') (S.loopback n cut) (fun _ _ => 0) := by
  have h : Realizes (S.loopback n cut) (S.loopback k cut') (fun _ _ => 0) := by
    refine realizes_zero_of_stepMap_on _ _ (fun u => Inv u.2) _root_.id hinit rfl
      (fun u e hu => exists_loopback_step_factor cut hkn hex u e hu) fun u e hu => ?_
    rw [loopback_step, loopback_step, fbRun_eq_of_exitsBy cut cut' k (hex u.2 hu e) hkn]
    simp [SPComp.map_comp, Function.comp_def]
  exact ⟨h, fun ζ => (h ζ).symm⟩

/-- The stateless system that answers the event `e` with `f e`. -/
noncomputable def ofFun (f : E → O) : Sys Unit E O where
  init := ()
  step t e := SPComp.pure (t, f e)

/-- **Yanking.** With fuel at least `1`, the loopback of the swap of the two copies of `X` is the
identity of `X`. -/
theorem loopback_yank (n : ℕ) (cut : X → X) :
    Realizes ((ofFun (Sum.swap : X ⊕ X → X ⊕ X)).loopback (n + 1) cut) (ofFun id)
      (fun _ _ => 0) ∧
    Realizes (ofFun id) ((ofFun (Sum.swap : X ⊕ X → X ⊕ X)).loopback (n + 1) cut)
      (fun _ _ => 0) := by
  have h : Realizes ((ofFun (Sum.swap : X ⊕ X → X ⊕ X)).loopback (n + 1) cut) (ofFun id)
      (fun _ _ => 0) :=
    realizes_zero_of_stepMap _ _ (fun _ => ()) rfl fun u e => by
      rw [loopback_step]
      cases n <;> simp [fbRun, ofFun]
  exact ⟨h, fun ζ => (h ζ).symm⟩

/-! ## Vanishing for a sum of wires -/

section Vanishing

variable (S : Sys τ ((E ⊕ X) ⊕ Y) ((O ⊕ X) ⊕ Y))

/-- The system `S` with the two wires `X` and `Y` taken as one wire `X ⊕ Y`. -/
noncomputable def sumWire : Sys τ (E ⊕ (X ⊕ Y)) (O ⊕ (X ⊕ Y)) :=
  S.mapPorts (Equiv.sumAssoc E X Y).symm (Equiv.sumAssoc O X Y)

/-- A step of `S.sumWire` on a reassociated event is a step of `S`. -/
theorem sumWire_step (t : τ) (ev : (E ⊕ X) ⊕ Y) :
    S.sumWire.step t (Equiv.sumAssoc E X Y ev) =
      SPComp.map (fun q => (q.1, Equiv.sumAssoc O X Y q.2)) (S.step t ev) := by
  simp [sumWire, Sys.mapPorts, Sys.relabel]

variable {S}

/-- The possible outcomes of the inner loopback along `Y` from a state where the flat loopback
exits within `j`: an outer output at a state satisfying `P`, or a wire value `x` at a state from
which the flat loopback, continued on `x`, exits within `j - 1`, with `j ≥ 1`. -/
theorem fbRun_inner_isOutcome {P : τ → Prop} (cY : Y → O ⊕ X) :
    ∀ (j : ℕ) {m : ℕ} {ev : (E ⊕ X) ⊕ Y} {t : τ},
      S.sumWire.ExitsBy P j (Equiv.sumAssoc E X Y ev) t → j ≤ m →
      ∀ q, IsOutcome (fbRun S cY m ev t) q →
        Sum.elim (fun _ => P q.1)
          (fun x => 1 ≤ j ∧ S.sumWire.ExitsBy P (j - 1) (.inr (.inl x)) q.1) q.2 := by
  have hS : ∀ {t : τ} {ev : (E ⊕ X) ⊕ Y} {q0 : τ × ((O ⊕ X) ⊕ Y)}, IsOutcome (S.step t ev) q0 →
      IsOutcome (S.sumWire.step t (Equiv.sumAssoc E X Y ev))
        (q0.1, Equiv.sumAssoc O X Y q0.2) := by
    intro t ev q0 hq0
    rw [sumWire_step]
    exact isOutcome_map (fun q => (q.1, Equiv.sumAssoc O X Y q.2)) hq0
  intro j
  induction j with
  | zero =>
    intro m ev t hj _ q hq
    cases m <;>
    · simp only [fbRun] at hq
      obtain ⟨⟨t', (o | x) | y⟩, hq0, hqq0⟩ := isOutcome_bind hq
      · have h0 := hj _ (hS hq0)
        obtain rfl := isOutcome_pure hqq0
        simpa using h0
      · exact False.elim (hj _ (hS hq0))
      · exact False.elim (hj _ (hS hq0))
  | succ j ih =>
    intro m ev t hj hjm q hq
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [fbRun] at hq
    obtain ⟨⟨t', (o | x) | y⟩, hq0, hqq0⟩ := isOutcome_bind hq
    · have h0 := hj _ (hS hq0)
      obtain rfl := isOutcome_pure hqq0
      simpa using h0
    · have h0 := hj _ (hS hq0)
      obtain rfl := isOutcome_pure hqq0
      exact ⟨by omega, h0⟩
    · have h0 := hj _ (hS hq0)
      have h1 := ih (ev := .inr y) h0 (by omega) q hqq0
      rcases q with ⟨t'', o | x⟩
      · exact h1
      · exact ⟨by omega, ExitsBy.mono (by omega) h1.2⟩

/-- With adequate fuel, the flat loopback from a reassociated event runs the inner loopback
along `Y` and then continues on its wire output `x` as the flat loopback from `inr (inl x)`. -/
theorem fbRun_sumWire_split {P : τ → Prop} (c : X ⊕ Y → O) (cY : Y → O ⊕ X) :
    ∀ (j : ℕ) {m N N₂ : ℕ} {ev : (E ⊕ X) ⊕ Y} {t : τ},
      S.sumWire.ExitsBy P j (Equiv.sumAssoc E X Y ev) t → j ≤ m → j ≤ N → j ≤ N₂ →
      fbRun S.sumWire c N (Equiv.sumAssoc E X Y ev) t =
        SPComp.bind (fbRun S cY m ev t) fun q =>
          Sum.elim (fun o => SPComp.pure (q.1, o))
            (fun x => fbRun S.sumWire c N₂ (.inr (.inl x)) q.1) q.2 := by
  have hS : ∀ {t : τ} {ev : (E ⊕ X) ⊕ Y} {q0 : τ × ((O ⊕ X) ⊕ Y)}, IsOutcome (S.step t ev) q0 →
      IsOutcome (S.sumWire.step t (Equiv.sumAssoc E X Y ev))
        (q0.1, Equiv.sumAssoc O X Y q0.2) := by
    intro t ev q0 hq0
    rw [sumWire_step]
    exact isOutcome_map (fun q => (q.1, Equiv.sumAssoc O X Y q.2)) hq0
  intro j
  induction j with
  | zero =>
    intro m N N₂ ev t hj _ _ _
    cases N <;> cases m <;>
    · simp only [fbRun, sumWire_step, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
      refine bind_congr_isOutcome ?_
      rintro ⟨t', (o | x) | y⟩ hq0
      · simp
      · exact False.elim (hj _ (hS hq0))
      · exact False.elim (hj _ (hS hq0))
  | succ j ih =>
    intro m N N₂ ev t hj hjm hjN hjN₂
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    obtain ⟨N, rfl⟩ : ∃ N', N = N' + 1 := ⟨N - 1, by omega⟩
    simp only [fbRun, sumWire_step, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
    refine bind_congr_isOutcome ?_
    rintro ⟨t', (o | x) | y⟩ hq0
    · simp
    · have h0 := hj _ (hS hq0)
      simp only [Equiv.sumAssoc_apply_inl_inr, Sum.elim_inr, Sum.elim_inl,
        SPComp.pure_bind] at h0 ⊢
      exact (fbRun_eq_of_exitsBy c c j h0 (by omega)).trans
        (fbRun_eq_of_exitsBy c c j h0 (by omega)).symm
    · have h0 := hj _ (hS hq0)
      simp only [Equiv.sumAssoc_apply_inr, Sum.elim_inr] at h0 ⊢
      exact ih (ev := .inr y) h0 (by omega) (by omega) (by omega)

/-- With adequate fuel, the outer loopback along `X` of the inner loopback along `Y` runs as the
flat loopback along `X ⊕ Y`. -/
theorem fbRun_loopback_sumWire {P : τ → Prop} (c : X ⊕ Y → O) (cX : X → O)
    (cY : Y → O ⊕ X) :
    ∀ (j : ℕ) {m n N : ℕ} {g : E ⊕ X} {t : τ},
      S.sumWire.ExitsBy P j (Equiv.sumAssoc E X Y (.inl g)) t → j ≤ m → j ≤ n → j ≤ N →
      fbRun (S.loopback m cY) cX n g ((), t) =
        SPComp.map (fun p => (((), p.1), p.2))
          (fbRun S.sumWire c N (Equiv.sumAssoc E X Y (.inl g)) t) := by
  intro j
  induction j with
  | zero =>
    intro m n N g t hj hjm _ hjN
    rw [fbRun_sumWire_split c cY 0 hj hjm hjN hjN]
    cases n <;>
    · simp only [fbRun, loopback_step, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
      refine bind_congr_isOutcome ?_
      rintro ⟨t', o | x⟩ hq
      · simp
      · have hE := fbRun_inner_isOutcome cY 0 hj hjm _ hq
        simp at hE
  | succ j ih =>
    intro m n N g t hj hjm hjn hjN
    rw [fbRun_sumWire_split c cY (j + 1) hj hjm hjN hjN]
    obtain ⟨n, rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    simp only [fbRun, loopback_step, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
    refine bind_congr_isOutcome ?_
    rintro ⟨t', o | x⟩ hq
    · simp
    · have hE := fbRun_inner_isOutcome cY (j + 1) hj hjm _ hq
      simp only [Sum.elim_inr, Nat.add_sub_cancel] at hE ⊢
      rw [ih (g := .inr x) (N := N) hE.2 (by omega) (by omega) (by omega)]
      rfl

/-- **Vanishing for a sum of wires.** When fuel `p` is adequate for the loopback along `X ⊕ Y`
on an invariant that holds initially, the loopback along `X` of the loopback along `Y` with
fuels at least `p` agrees with the loopback along `X ⊕ Y` with fuel `p`, whatever the cut-off
maps. -/
theorem loopback_loopback (Inv : τ → Prop) {p m n : ℕ} (hm : p ≤ m) (hn : p ≤ n)
    (c : X ⊕ Y → O) (cX : X → O) (cY : Y → O ⊕ X) (hinit : Inv S.init)
    (hex : S.sumWire.ExitsWithin Inv p) :
    Realizes ((S.loopback m cY).loopback n cX) (S.sumWire.loopback p c) (fun _ _ => 0) ∧
    Realizes (S.sumWire.loopback p c) ((S.loopback m cY).loopback n cX) (fun _ _ => 0) := by
  have hrun : ∀ (t : τ), Inv t → ∀ e : E,
      fbRun (S.loopback m cY) cX n (.inl e) ((), t) =
        SPComp.map (fun q => (((), q.1), q.2)) (fbRun S.sumWire c p (.inl e) t) :=
    fun t ht e => fbRun_loopback_sumWire c cX cY p (hex t ht e) hm hn le_rfl
  have h : Realizes ((S.loopback m cY).loopback n cX) (S.sumWire.loopback p c)
      (fun _ _ => 0) := by
    refine realizes_zero_of_stepMap_on _ _ (fun s => Inv s.2.2) (fun s => ((), s.2.2)) hinit rfl
      ?_ ?_
    · rintro ⟨u, u', t⟩ e ht
      refine exists_bind_pure_of_isOutcome _ (fun q : (Unit × Unit × τ) × O => Inv q.1.2.2)
        fun q hq => ?_
      rw [loopback_step, hrun t ht e] at hq
      obtain ⟨a, ha, hqa⟩ := isOutcome_bind hq
      obtain ⟨b, hb, hab⟩ := isOutcome_bind ha
      have h1 := isOutcome_pure hqa
      have h2 := isOutcome_pure hab
      subst h1 h2
      exact fbRun_isOutcome_of_exitsBy c p (hex t ht e) b hb
    · rintro ⟨u, u', t⟩ e ht
      rw [loopback_step, loopback_step, hrun t ht e]
      simp [SPComp.map_comp, Function.comp_def]
  exact ⟨h, fun ζ => (h ζ).symm⟩

end Vanishing

end Sys

end CatCrypt.Crypto.UCTransparent
