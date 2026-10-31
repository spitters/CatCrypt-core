/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCLoopbackOmega
public import CatCryptCore.Crypto.UCLoopbackMonoidal
public import CatCryptCore.ForMathlib.CategoryTheory.Monoidal.Traced

/-!
# The trace of the category of port types

The unbounded loopback `Sys.loopbackω` is a trace on the symmetric monoidal category `SysCat`:
the class of `f : X ⊗ U ⟶ Y ⊗ U` is sent to the class of the unbounded loopback of `f` along
`U`. Each axiom of Joyal, Street and Verity is a step equivalence. The laws that move a system
across the loopback (tightening, sliding, superposing) hold for the activations failing on
exhausted fuel at every fuel, and pass to the supremum by continuity of `SPComp.bind`. The
vanishing law for a tensor product of wires compares two suprema in both directions, each by an
induction on the fuel of one side against the unfolding equation of the other. The vanishing
law for the unit and yanking follow from the unfolding equation `Sys.fbRunω_eq`.

## Main definitions

* `SysObj.loopbackω`: the unbounded loopback of a bundled system.
* `SysCat.trace`: the class of the unbounded loopback.
* `SysCat.tracedCategory`: `SysCat` is a traced symmetric monoidal category.

## Main results

* `Sys.loopbackω_seq_left`, `Sys.loopbackω_seq_right`: naturality in the outer ports, for
  stateful systems.
* `Sys.loopbackω_slide`: dinaturality in the wire, for a stateful system on the wire.
* `Sys.loopbackω_empty`: vanishing for the empty wire.
* `Sys.fbRunω_loopbackω_sumAssoc`, `Sys.loopbackω_loopbackω`: vanishing for a sum of wires.
* `Sys.loopbackω_par_left`: superposing on the left.
* `Sys.loopbackω_swap`: yanking.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open OmegaCompletePartialOrder

namespace Sys

variable {τ γ ρ E O E' O' X Y U V W : Type}

/-- Unfolding lemma of `ofFun`: a step. -/
theorem ofFun_step (f : E → O) (t : Unit) (e : E) : (ofFun f).step t e = SPComp.pure (t, f e) :=
  rfl

/-! ## Passing to the supremum -/

/-- When the activations failing on exhausted fuel of `S'` are those of `S` followed by `k` at
every fuel, the unbounded activation of `S'` is that of `S` followed by `k`. -/
theorem fbRunω_eq_bind_of_fbRunFail {υ E₁ O₁ X₁ : Type} {S : Sys τ (E ⊕ X) (O ⊕ X)}
    {S' : Sys υ (E₁ ⊕ X₁) (O₁ ⊕ X₁)} {g : E ⊕ X} {t : τ} {g' : E₁ ⊕ X₁} {t' : υ}
    (k : τ × O → SPComp (υ × O₁))
    (h : ∀ n, S'.fbRunFail n g' t' = SPComp.bind (S.fbRunFail n g t) k) :
    S'.fbRunω g' t' = SPComp.bind (S.fbRunω g t) k := by
  change ωSup (S'.fbChain g' t') = SPComp.bind (ωSup (S.fbChain g t)) k
  rw [(SPComp.ωScottContinuous_bind_left k).map_ωSup]
  exact le_antisymm (ωSup_le _ _ fun n => le_ωSup_of_le n (h n).le)
    (ωSup_le _ _ fun n => le_ωSup_of_le n (h n).ge)

/-! ## Naturality in the outer ports -/

/-- **Tightening on the event side.** A stateful system `g` on the outer events, beside the
forwarding of the wire and cascaded into `S`, commutes with the unbounded loopback. -/
theorem loopbackω_seq_left (g : Sys γ E' E) (S : Sys τ (E ⊕ X) (O ⊕ X)) :
    StepMapOn ((g.par (ofFun (id : X → X))).seq S).loopbackω (g.seq S.loopbackω)
      (fun _ => True) (fun u => (u.1.1, u.2)) := by
  set L := (g.par (ofFun (id : X → X))).seq S with hL
  have hstepR : ∀ (x : X) (c : γ) (v : Unit) (t : τ),
      L.step ((c, v), t) (.inr x) =
        SPComp.bind (S.step t (.inr x)) fun r => SPComp.pure (((c, v), r.1), r.2) := by
    intro x c v t
    simp [hL, seq_step, ofFun, SPComp.map]
  have hstepL : ∀ (e : E') (c : γ) (v : Unit) (t : τ),
      L.step ((c, v), t) (.inl e) = SPComp.bind (g.step c e) fun q =>
        SPComp.bind (S.step t (.inl q.2)) fun r => SPComp.pure (((q.1, v), r.1), r.2) := by
    intro e c v t
    simp [hL, seq_step, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  have hrunR : ∀ (n : ℕ) (x : X) (c : γ) (v : Unit) (t : τ),
      L.fbRunFail n (.inr x) ((c, v), t) =
        SPComp.bind (S.fbRunFail n (.inr x) t) fun p => SPComp.pure (((c, v), p.1), p.2) := by
    intro n
    induction n with
    | zero =>
      intro x c v t
      simp only [fbRunFail, hstepR, SPComp.bind_assoc, SPComp.pure_bind]
      congr 1; funext q; rcases q with ⟨t', o | x'⟩ <;> simp [SPComp.fail_bind]
    | succ n ih =>
      intro x c v t
      simp only [fbRunFail, hstepR, SPComp.bind_assoc, SPComp.pure_bind]
      congr 1; funext q; rcases q with ⟨t', o | x'⟩
      · simp
      · simpa using ih x' c v t'
  have hrunRω : ∀ (x : X) (c : γ) (v : Unit) (t : τ),
      L.fbRunω (.inr x) ((c, v), t) =
        SPComp.bind (S.fbRunω (.inr x) t) fun p => SPComp.pure (((c, v), p.1), p.2) :=
    fun x c v t => fbRunω_eq_bind_of_fbRunFail _ fun n => hrunR n x c v t
  refine StepMapOn.of_step _ rfl fun u e => ?_
  obtain ⟨⟨c, v⟩, t⟩ := u
  rw [loopbackω_step, fbRunω_eq, hstepL, seq_step]
  simp only [loopbackω_step, fbRunω_eq S (.inl _), SPComp.map, SPComp.bind_assoc,
    SPComp.pure_bind]
  congr 1; funext q; congr 1; funext r; rcases r with ⟨t', o | x'⟩
  · simp
  · simp [hrunRω, SPComp.bind_assoc]

/-- The activation failing on exhausted fuel of `S` cascaded into `h` beside the forwarding of
the wire is the activation of `S` followed by a step of `h`, at every fuel. -/
theorem fbRunFail_seq_right (S : Sys τ (E ⊕ X) (O ⊕ X)) (h : Sys ρ O O') :
    ∀ (n : ℕ) (ev : E ⊕ X) (t : τ) (c : ρ) (v : Unit),
      (S.seq (h.par (ofFun (id : X → X)))).fbRunFail n ev (t, (c, v)) =
        SPComp.bind (S.fbRunFail n ev t) fun p =>
          SPComp.map (fun r => ((p.1, (r.1, v)), r.2)) (h.step c p.2) := by
  intro n
  induction n with
  | zero =>
    intro ev t c v
    simp only [fbRunFail, seq_step, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
    congr 1; funext q; rcases q with ⟨t', o | x⟩
    · simp [SPComp.map, SPComp.bind_assoc]
    · simp [ofFun, SPComp.fail_bind]
  | succ n ih =>
    intro ev t c v
    simp only [fbRunFail, seq_step, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
    congr 1; funext q; rcases q with ⟨t', o | x⟩
    · simp [SPComp.map, SPComp.bind_assoc]
    · simpa [ofFun, SPComp.map] using ih (.inr x) t' c v

/-- **Tightening on the output side.** The unbounded loopback of `S` cascaded into a stateful
system `h` beside the forwarding of the wire is the unbounded loopback of `S` cascaded
into `h`. -/
theorem loopbackω_seq_right (S : Sys τ (E ⊕ X) (O ⊕ X)) (h : Sys ρ O O') :
    StepMapOn (S.seq (h.par (ofFun (id : X → X)))).loopbackω (S.loopbackω.seq h)
      (fun _ => True) (fun u => (u.1, u.2.1)) := by
  refine StepMapOn.of_step _ rfl fun u e => ?_
  obtain ⟨t, c, v⟩ := u
  rw [loopbackω_step, fbRunω_eq_bind_of_fbRunFail _ fun n => fbRunFail_seq_right S h n _ t c v,
    seq_step, loopbackω_step]
  simp [SPComp.map, SPComp.bind_assoc]

/-! ## Dinaturality in the wire -/

section Slide

variable (S : Sys τ (E ⊕ X) (O ⊕ Y)) (g : Sys γ Y X)

/-- The activations of the loopback along `Y` of `g` placed before `S` are those of the
loopback along `X` of `g` placed after `S` with the states exchanged, at every fuel: a wire
event `y` of the first is a step of `g` on `y` followed by the second from the event `g`
answers. -/
theorem fbRunFail_seq_slide :
    ∀ (n : ℕ) (y : Y) (c : γ) (w : Unit) (t : τ),
      (((ofFun (id : E → E)).par g).seq S).fbRunFail n (.inr y) ((w, c), t) =
        SPComp.bind (g.step c y) fun q2 =>
          SPComp.bind ((S.seq ((ofFun (id : O → O)).par g)).fbRunFail n (.inr q2.2)
            (t, (w, q2.1))) fun p => SPComp.pure (p.1.swap, p.2) := by
  intro n
  induction n with
  | zero =>
    intro y c w t
    simp only [fbRunFail, seq_step, par_step_inr, SPComp.map, SPComp.bind_assoc,
      SPComp.pure_bind]
    congr 1; funext q2; congr 1; funext r; rcases r with ⟨t', o | y'⟩
    · simp [ofFun, SPComp.map]
    · simp [SPComp.map, SPComp.fail_bind, bind_fail_right]
  | succ n ih =>
    intro y c w t
    simp only [fbRunFail, seq_step, par_step_inr, SPComp.map, SPComp.bind_assoc,
      SPComp.pure_bind]
    congr 1; funext q2; congr 1; funext r; rcases r with ⟨t', o | y'⟩
    · simp [ofFun, SPComp.map]
    · simpa [SPComp.map, SPComp.bind_assoc] using ih y' q2.1 w t'

/-- The activation of the loopback along `Y` of `g` placed before `S` from an outer event is
that of the loopback along `X` of `g` placed after `S`, with the states exchanged, at every
fuel. -/
theorem fbRunFail_seq_slide_inl (n : ℕ) (e : E) (w : Unit) (c : γ) (t : τ) :
    (((ofFun (id : E → E)).par g).seq S).fbRunFail n (.inl e) ((w, c), t) =
      SPComp.bind ((S.seq ((ofFun (id : O → O)).par g)).fbRunFail n (.inl e) (t, (w, c)))
        fun p => SPComp.pure (p.1.swap, p.2) := by
  cases n with
  | zero =>
    simp only [fbRunFail, seq_step, par_step_inl, ofFun_step, id_eq, SPComp.map,
      SPComp.bind_assoc,
      SPComp.pure_bind]
    congr 1; funext r; rcases r with ⟨t', o | y'⟩
    · simp [ofFun, SPComp.map]
    · simp [SPComp.map, SPComp.fail_bind, bind_fail_right]
  | succ n =>
    simp only [fbRunFail, seq_step, par_step_inl, ofFun_step, id_eq, SPComp.map,
      SPComp.bind_assoc,
      SPComp.pure_bind]
    congr 1; funext r; rcases r with ⟨t', o | y'⟩
    · simp [ofFun, SPComp.map]
    · simpa [SPComp.map, SPComp.bind_assoc] using fbRunFail_seq_slide S g n y' c w t'

/-- **Sliding a stateful system along the wire.** For `S` on `(E ⊕ X, O ⊕ Y)` and a system `g`
from `Y` to `X`, exchanging the states is a step map from the unbounded loopback along `X` of
`g` placed after `S` to the unbounded loopback along `Y` of `g` placed before `S`. -/
theorem loopbackω_slide :
    StepMapOn (S.seq ((ofFun (id : O → O)).par g)).loopbackω
      (((ofFun (id : E → E)).par g).seq S).loopbackω (fun _ => True) Prod.swap := by
  refine StepMapOn.of_step _ rfl fun u e => ?_
  obtain ⟨t, w, c⟩ := u
  exact (fbRunω_eq_bind_of_fbRunFail _ fun n => fbRunFail_seq_slide_inl S g n e w c t).symm

end Slide

/-! ## Vanishing for the empty wire and yanking -/

/-- **Vanishing for the empty wire.** The unbounded loopback along `Empty` is the system
between the unitors. -/
theorem loopbackω_empty (S : Sys τ (E ⊕ Empty) (O ⊕ Empty)) :
    StepMapOn S.loopbackω
      ((ofFun (Equiv.sumEmpty E Empty).symm).seq (S.seq (ofFun (Equiv.sumEmpty O Empty))))
      (fun _ => True) (fun t => ((), (t, ()))) := by
  refine StepMapOn.of_step _ rfl fun t e => ?_
  rw [loopbackω_step, fbRunω_eq]
  simp only [seq_step, ofFun, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  congr 1; funext q; rcases q with ⟨t', o | x⟩
  · simp
  · exact x.elim

/-- **Yanking.** The unbounded loopback of the swap of the two copies of `X` is the forwarding
system. -/
theorem loopbackω_swap :
    StepMapOn (ofFun (Equiv.sumComm X X)).loopbackω (ofFun id) (fun _ => True) id := by
  refine StepMapOn.of_step _ rfl fun t e => ?_
  rw [loopbackω_step, fbRunω_eq]
  simp only [ofFun, Equiv.sumComm_apply, Sum.swap_inl, SPComp.pure_bind, Sum.elim_inr]
  rw [fbRunω_eq]
  simp [SPComp.map]

/-! ## Structure maps around a system -/

/-- A system between two stateless systems is the system on relabelled ports; the state map
keeps the state of the middle system. -/
theorem StepMapOn.ofFun_seq_seq_ofFun {EG OG : Type} (a : E → EG) (S : Sys τ EG OG)
    (b : OG → O) :
    StepMapOn ((ofFun a).seq (S.seq (ofFun b))) (S.mapPorts a b) (fun _ => True)
      (fun s => s.2.1) :=
  StepMapOn.of_step _ rfl fun s e => by
    simp [seq_step, ofFun_step, mapPorts_step, SPComp.map, SPComp.bind_assoc]

/-! ## Vanishing for a sum of wires -/

section Vanishing

variable (S : Sys τ (E ⊕ (X ⊕ Y)) (O ⊕ (X ⊕ Y)))

/-- **Vanishing for a sum of wires.** The unbounded activation of the loopback along `X` of the
unbounded loopback along `Y` of `S` (on reassociated ports) from an outer event is the unbounded
activation of `S` along `X ⊕ Y`. -/
theorem fbRunω_loopbackω_sumAssoc (e : E) (t : τ) :
    (S.mapPorts (Equiv.sumAssoc E X Y) (Equiv.sumAssoc O X Y).symm).loopbackω.fbRunω (.inl e) t =
      S.fbRunω (.inl e) t := by
  set G := S.mapPorts (Equiv.sumAssoc E X Y) (Equiv.sumAssoc O X Y).symm with hGdef
  set R := G.loopbackω with hRdef
  have hG : ∀ (t : τ) (ev : (E ⊕ X) ⊕ Y), G.step t ev =
      SPComp.bind (S.step t (Equiv.sumAssoc E X Y ev)) fun q =>
        SPComp.pure (q.1, (Equiv.sumAssoc O X Y).symm q.2) := fun _ _ => rfl
  -- the unbounded activation of the outer loopback, continued from an inner event
  let Bext : (E ⊕ X) ⊕ Y → τ → SPComp (τ × O) := fun ev t =>
    SPComp.bind (G.fbRunω ev t) fun q =>
      Sum.elim (fun o => SPComp.pure (q.1, o)) (fun x => R.fbRunω (.inr x) q.1) q.2
  have hR : ∀ (g : E ⊕ X) (t : τ), R.fbRunω g t = Bext (.inl g) t :=
    fun g t => fbRunω_eq R g t
  have hB : ∀ (ev : E ⊕ (X ⊕ Y)) (t : τ), Bext ((Equiv.sumAssoc E X Y).symm ev) t =
      SPComp.bind (S.step t ev) fun q => Sum.elim (fun o => SPComp.pure (q.1, o))
        (fun w => Bext ((Equiv.sumAssoc E X Y).symm (.inr w)) q.1) q.2 := by
    intro ev t
    simp only [Bext]
    rw [fbRunω_eq G, hG]
    simp only [Equiv.apply_symm_apply, SPComp.bind_assoc, SPComp.pure_bind]
    congr 1; funext q; rcases q with ⟨t', o | x | y⟩
    · simp
    · simp only [Equiv.sumAssoc_symm_apply_inr_inl, Sum.elim_inl, Sum.elim_inr,
        SPComp.pure_bind]
      exact hR (.inr x) t'
    · simp
  -- the activations of `S` are below the outer loopback
  have hle₁ : ∀ (n : ℕ) (ev : E ⊕ (X ⊕ Y)) (t : τ),
      S.fbRunFail n ev t ≤ Bext ((Equiv.sumAssoc E X Y).symm ev) t := by
    intro n
    induction n with
    | zero =>
      intro ev t
      rw [hB, fbRunFail]
      refine SPComp.bind_mono_right _ fun q => ?_
      rcases q with ⟨t', o | w⟩
      · exact le_rfl
      · exact SPComp.fail_le _
    | succ n ih =>
      intro ev t
      rw [hB, fbRunFail]
      refine SPComp.bind_mono_right _ fun q => ?_
      rcases q with ⟨t', o | w⟩
      · exact le_rfl
      · exact ih (.inr w) t'
  -- the inner loopback followed by `S` on the outer wire is below `S`
  let K : τ × (O ⊕ X) → SPComp (τ × O) := fun q =>
    Sum.elim (fun o => SPComp.pure (q.1, o)) (fun x => S.fbRunω (.inr (.inl x)) q.1) q.2
  have hQ : ∀ (k : ℕ) (ev : (E ⊕ X) ⊕ Y) (t : τ),
      SPComp.bind (G.fbRunFail k ev t) K ≤ S.fbRunω (Equiv.sumAssoc E X Y ev) t := by
    intro k
    induction k with
    | zero =>
      intro ev t
      rw [fbRunω_eq S]
      simp only [fbRunFail, hG, SPComp.bind_assoc, SPComp.pure_bind]
      refine SPComp.bind_mono_right _ fun q => ?_
      rcases q with ⟨t', o | x | y⟩
      · simp [K]
      · simp [K]
      · simp [SPComp.fail_bind, SPComp.fail_le]
    | succ k ih =>
      intro ev t
      rw [fbRunω_eq S]
      simp only [fbRunFail, hG, SPComp.bind_assoc, SPComp.pure_bind]
      refine SPComp.bind_mono_right _ fun q => ?_
      rcases q with ⟨t', o | x | y⟩
      · simp [K]
      · simp [K]
      · simpa using ih (.inr y) t'
  have hQω : ∀ (ev : (E ⊕ X) ⊕ Y) (t : τ),
      SPComp.bind (G.fbRunω ev t) K ≤ S.fbRunω (Equiv.sumAssoc E X Y ev) t := by
    intro ev t
    change SPComp.bind (ωSup (G.fbChain ev t)) K ≤ _
    rw [(SPComp.ωScottContinuous_bind_left K).map_ωSup]
    exact ωSup_le _ _ fun k => hQ k ev t
  have hle₂ : ∀ (m : ℕ) (g : E ⊕ X) (t : τ),
      R.fbRunFail m g t ≤ S.fbRunω (Equiv.sumAssoc E X Y (.inl g)) t := by
    intro m
    induction m with
    | zero =>
      intro g t
      refine le_trans ?_ (hQω (.inl g) t)
      refine SPComp.bind_mono_right _ fun q => ?_
      rcases q with ⟨t', o | x⟩
      · exact le_rfl
      · exact SPComp.fail_le _
    | succ m ih =>
      intro g t
      refine le_trans ?_ (hQω (.inl g) t)
      refine SPComp.bind_mono_right _ fun q => ?_
      rcases q with ⟨t', o | x⟩
      · exact le_rfl
      · exact ih (.inr x) t'
  apply le_antisymm
  · exact ωSup_le _ _ fun m => hle₂ m (.inl e) t
  · refine ωSup_le _ _ fun n => (hle₁ n (.inl e) t).trans ?_
    rw [hR]
    rfl

/-- **Vanishing for a sum of wires**, as a step map: the identity of the states is a step map
from the loopback along `X` of the loopback along `Y` of `S` (on reassociated ports) to the
loopback of `S` along `X ⊕ Y`. -/
theorem loopbackω_loopbackω :
    StepMapOn (S.mapPorts (Equiv.sumAssoc E X Y) (Equiv.sumAssoc O X Y).symm).loopbackω.loopbackω
      S.loopbackω (fun _ => True) id :=
  StepMapOn.of_step _ rfl fun t e => by
    rw [loopbackω_step, loopbackω_step, fbRunω_loopbackω_sumAssoc]
    simp [SPComp.map, SPComp.bind_pure]

end Vanishing

/-! ## Superposing -/

section Superposing

variable (S : Sys τ (E ⊕ X) (O ⊕ X))

/-- The system `S` beside the forwarding of `W` on the left, with its wire reassociated to the
outside. -/
noncomputable abbrev parLeftWire (W : Type) : Sys (Unit × τ) ((W ⊕ E) ⊕ X) ((W ⊕ O) ⊕ X) :=
  ((ofFun (id : W → W)).par S).mapPorts (Equiv.sumAssoc W E X) (Equiv.sumAssoc W O X).symm

/-- The activations of `S` beside the forwarding of `W` are those of `S`, at every fuel. -/
theorem fbRunFail_parLeftWire :
    ∀ (n : ℕ) (ev : E ⊕ X) (u : Unit) (t : τ),
      (S.parLeftWire W).fbRunFail n (Sum.map Sum.inr id ev) (u, t) =
        SPComp.bind (S.fbRunFail n ev t) fun p => SPComp.pure ((u, p.1), Sum.inr p.2) := by
  have hstep : ∀ (ev : E ⊕ X) (u : Unit) (t : τ),
      (S.parLeftWire W).step (u, t) (Sum.map Sum.inr id ev) =
        SPComp.bind (S.step t ev) fun q => SPComp.pure ((u, q.1), Sum.map Sum.inr id q.2) := by
    intro ev u t
    have hev : Equiv.sumAssoc W E X (Sum.map Sum.inr id ev) = Sum.inr ev := by
      rcases ev with e | x <;> rfl
    simp only [parLeftWire, mapPorts_step, hev, par_step_inr, SPComp.map, SPComp.bind_assoc,
      SPComp.pure_bind]
    congr 1
  intro n
  induction n with
  | zero =>
    intro ev u t
    simp only [fbRunFail, hstep, SPComp.bind_assoc, SPComp.pure_bind]
    congr 1; funext q; rcases q with ⟨t', o | x⟩ <;> simp [SPComp.fail_bind]
  | succ n ih =>
    intro ev u t
    simp only [fbRunFail, hstep, SPComp.bind_assoc, SPComp.pure_bind]
    congr 1; funext q; rcases q with ⟨t', o | x⟩
    · simp
    · simpa using ih (.inr x) u t'

/-- **Superposing on the left.** The forwarding of `W` beside the unbounded loopback of `S` is
the unbounded loopback of `S` beside the forwarding of `W`. -/
theorem loopbackω_par_left :
    StepMapOn ((ofFun (id : W → W)).par S.loopbackω) (S.parLeftWire W).loopbackω
      (fun _ => True) id := by
  refine StepMapOn.of_step _ rfl fun s e => ?_
  obtain ⟨u, t⟩ := s
  rcases e with w | e
  · rw [par_step_inl, loopbackω_step, fbRunω_eq]
    simp [parLeftWire, mapPorts_step, ofFun_step, SPComp.map]
  · have h := fbRunω_eq_bind_of_fbRunFail _ fun n =>
      fbRunFail_parLeftWire (W := W) S n (.inl e) u t
    simp only [Sum.map_inl] at h
    rw [par_step_inr, loopbackω_step, loopbackω_step, id, h]
    simp [SPComp.map]

end Superposing

end Sys

namespace SysObj

/-- The unbounded loopback of a bundled system. -/
noncomputable def loopbackω {E O X : Type} (A : SysObj (E ⊕ X) (O ⊕ X)) : SysObj E O :=
  ⟨A.St, A.sys.loopbackω⟩

end SysObj

/-- Step equivalence is a congruence for the unbounded loopback. -/
theorem Sys.StepEq.loopbackω {E O X : Type} {A A' : SysObj (E ⊕ X) (O ⊕ X)}
    (h : Sys.StepEq A A') : Sys.StepEq A.loopbackω A'.loopbackω :=
  Sys.StepEq.map (fun A => A.loopbackω)
    (fun _ _ ⟨_, _, h⟩ => ⟨_, _, Sys.loopbackω_stepMap_on h⟩) h

namespace SysCat

open CategoryTheory MonoidalCategory

/-- The trace of `f : X ⊗ U ⟶ Y ⊗ U`: the class of the unbounded loopback along `U`. -/
noncomputable def trace (U : SysCat) {X Y : SysCat} (f : X ⊗ U ⟶ Y ⊗ U) : X ⟶ Y :=
  Quotient.map (SysObj.loopbackω (E := X.P) (O := Y.P) (X := U.P))
    (fun _ _ h => Sys.StepEq.loopbackω h) f

/-- `SysCat` is a traced symmetric monoidal category; the trace is the unbounded loopback. -/
noncomputable instance tracedCategory : TracedCategory SysCat where
  trace := trace
  trace_whiskerRight_comp U _ _ _ g f := by
    induction g using Quotient.inductionOn
    induction f using Quotient.inductionOn
    exact Quotient.sound (Sys.loopbackω_seq_left _ _).stepEq
  trace_comp_whiskerRight U _ _ _ f h := by
    induction f using Quotient.inductionOn
    induction h using Quotient.inductionOn
    exact Quotient.sound (Sys.loopbackω_seq_right _ _).stepEq
  trace_whiskerLeft_comp g f := by
    induction g using Quotient.inductionOn
    induction f using Quotient.inductionOn
    exact Quotient.sound (Relation.EqvGen.symm _ _ (Sys.loopbackω_slide _ _).stepEq)
  trace_tensorUnit f := by
    induction f using Quotient.inductionOn
    exact Quotient.sound (Sys.loopbackω_empty _).stepEq
  trace_tensor U V _ _ f := by
    induction f using Quotient.inductionOn with
    | h A =>
      refine Quotient.sound (Relation.EqvGen.trans _ _ _
        (Relation.EqvGen.symm _ _ (Sys.loopbackω_loopbackω A.sys).stepEq)
        (Relation.EqvGen.symm _ _ (Sys.StepEq.loopbackω (Sys.StepEq.loopbackω
          (Sys.StepMapOn.ofFun_seq_seq_ofFun _ A.sys _).stepEq))))
  whiskerLeft_trace W U _ _ f := by
    induction f using Quotient.inductionOn with
    | h A =>
      refine Quotient.sound (Relation.EqvGen.trans _ _ _
        (Sys.loopbackω_par_left (W := W.P) A.sys).stepEq
        (Relation.EqvGen.symm _ _ (Sys.StepEq.loopbackω
          (Sys.StepMapOn.ofFun_seq_seq_ofFun _ ((Sys.ofFun id).par A.sys) _).stepEq)))
  trace_braiding U := Quotient.sound (Sys.loopbackω_swap (X := U.P)).stepEq

end SysCat

end CatCrypt.Crypto.UCTransparent
