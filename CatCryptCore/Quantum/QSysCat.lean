/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QRealizes
public import CatCryptCore.Quantum.SubInstrumentOrder
public import CatCryptCore.ForMathlib.CategoryTheory.Monoidal.Traced

/-!
# The traced symmetric monoidal category of quantum reactive systems

A quantum reactive system `QRSys R τ E O` on the register `R` has a classical state `τ`; an
activation on the event `e` is a subinstrument on `R` whose outcome is the new state and the
output. The register is shared with the environment and with the other systems of a
composition; a private register is a factor of `R`, and the systems on the factors of `M × N`
are placed side by side by `QRSys.frameR` and `QRSys.frameL` (core `SubInstrument.frame` and
`OpenSystem.frameLeft`). The core `ReactiveUC.QSys` on `Fin d × H` is such a system
(`ReactiveUC.QSys.toQRSys`).

The development follows the classical one (`UCLoopbackTrace`, `UCLoopbackMonoidal`,
`UCLoopbackOmega`, `UCLoopbackTraced`) with sub-distributions replaced by subinstruments and the
ω-complete order of `SDistr` by Selinger's order (`SubInstrumentOrder`):

* a step map `QRSys.StepMap S T f` sends the initial state of `S` to that of `T` and commutes
  with the steps; step equivalence `QRSys.StepEq` is the equivalence relation it generates;
* the category `QSysCat R` has types of ports as objects and systems modulo step equivalence as
  morphisms; composition is the cascade `QRSys.seq` (the output of the first system is the event
  of the second);
* the tensor product of port types is their sum, the tensor product of morphisms is the
  parallel composition `QRSys.par`, and the unit is `Empty`;
* the activation of the feedback loop of `S` on `E ⊕ U → O ⊕ U` with fuel `n` fails when a wire
  value is answered to the last allowed call (`QRSys.fbRunFail`); the runs increase with the
  fuel, and the unbounded activation `QRSys.fbRunω` is their supremum. The unbounded loopback
  `QRSys.loopbackω` is the trace.

## Main definitions

* `QRSys R τ E O`, `QRSys.seq`, `QRSys.par`, `QRSys.ofFun`, `QRSys.mapPorts`.
* `QRSys.frameR`, `QRSys.frameL`, `QRSys.parFramed`: systems on the factors of a register.
* `QRSys.StepMap`, `QRSys.StepEq`.
* `QSysCat R`, with `Category`, `MonoidalCategory`, `SymmetricCategory` instances.
* `QRSys.fbRunFail`, `QRSys.fbRunω`, `QRSys.loopbackω`.
* `QSysCat.trace`, `QSysCat.tracedCategory`.

## Main results

* `QRSys.fbRunω_eq`: the unfolding equation of the unbounded activation.
* `QRSys.StepEq.loopbackω`: step equivalence is a congruence for the unbounded loopback.
* `QRSys.loopbackω_seq_left`, `QRSys.loopbackω_seq_right`: naturality.
* `QRSys.loopbackω_slide`: dinaturality.
* `QRSys.loopbackω_empty`, `QRSys.loopbackω_loopbackω`: vanishing.
* `QRSys.loopbackω_par_left`: superposing.
* `QRSys.loopbackω_swap`: yanking.
* `Party.QProg.qloop_stepMap`, `Party.QProg.qview_eq_of_stepMap`: a step map between core
  quantum systems with the same initial private basis state keeps their views.
-/

@[expose] public section

set_option autoImplicit false

/-- The failing subinstrument is the least element of Selinger's order. -/
theorem Quantum.SubInstrument.fail_le {A B α : Type} [Fintype A] [Fintype B]
    (c : SubInstrument A B α) : (SubInstrument.fail : SubInstrument A B α) ≤ c := fun a => by
  simpa using c.isCP_branch a

namespace CatCrypt.Quantum.ReactiveUC

open _root_.Quantum OmegaCompletePartialOrder

attribute [local simp] SubInstrument.bind_assoc SubInstrument.pure_bind SubInstrument.fail_bind
  SubInstrument.bind_fail

/-- A quantum reactive system on the register `R` with classical state `τ`, events `E` and
outputs `O`. -/
structure QRSys (R : Type) [Fintype R] (τ E O : Type) where
  /-- Initial classical state. -/
  init : τ
  /-- One activation: a subinstrument on the register with the new state and the output as
  outcome. -/
  step : τ → E → SubInstrument R R (τ × O)

/-- The core quantum reactive system on the register `Fin d × H`, its initial basis state
forgotten. -/
def QSys.toQRSys {H : Type} [Fintype H] {τ E O : Type} {d : ℕ} (S : QSys H τ E O d) :
    QRSys (Fin d × H) τ E O :=
  ⟨S.init, S.step⟩

namespace QRSys

variable {R : Type} [Fintype R]
variable {τ υ ρ γ τ' υ' E O P Q E' O' P' E'' EG OG X Y U : Type}

/-! ## Operations -/

/-- The cascade of `S` and `T`: the output of a step of `S` is the event of a step of `T`. -/
noncomputable def seq (S : QRSys R τ E O) (T : QRSys R υ O P) : QRSys R (τ × υ) E P where
  init := (S.init, T.init)
  step s e := (S.step s.1 e).bind fun q =>
    (T.step s.2 q.2).bind fun r => SubInstrument.pure ((q.1, r.1), r.2)

/-- Unfolding lemma of `seq`: a step. -/
theorem seq_step (S : QRSys R τ E O) (T : QRSys R υ O P) (s : τ × υ) (e : E) :
    (S.seq T).step s e = (S.step s.1 e).bind fun q =>
      (T.step s.2 q.2).bind fun r => SubInstrument.pure ((q.1, r.1), r.2) :=
  rfl

/-- The parallel composition of `S` and `T`: an event `inl e` activates `S`, an event `inr e`
activates `T`, and the output carries the tag of the event. -/
noncomputable def par (S : QRSys R τ E O) (T : QRSys R υ E' O') :
    QRSys R (τ × υ) (E ⊕ E') (O ⊕ O') where
  init := (S.init, T.init)
  step s := Sum.elim
    (fun e => (S.step s.1 e).bind fun q => SubInstrument.pure ((q.1, s.2), Sum.inl q.2))
    (fun e => (T.step s.2 e).bind fun q => SubInstrument.pure ((s.1, q.1), Sum.inr q.2))

/-- Unfolding lemma of `par`: a step on a left event. -/
@[simp] theorem par_step_inl (S : QRSys R τ E O) (T : QRSys R υ E' O') (s : τ × υ) (e : E) :
    (S.par T).step s (.inl e) =
      (S.step s.1 e).bind fun q => SubInstrument.pure ((q.1, s.2), Sum.inl q.2) :=
  rfl

/-- Unfolding lemma of `par`: a step on a right event. -/
@[simp] theorem par_step_inr (S : QRSys R τ E O) (T : QRSys R υ E' O') (s : τ × υ) (e : E') :
    (S.par T).step s (.inr e) =
      (T.step s.2 e).bind fun q => SubInstrument.pure ((s.1, q.1), Sum.inr q.2) :=
  rfl

/-- The stateless system that answers the event `e` with `f e` and leaves the register
unchanged. -/
noncomputable def ofFun (f : E → O) : QRSys R Unit E O where
  init := ()
  step t e := SubInstrument.pure (t, f e)

/-- Unfolding lemma of `ofFun`: a step. -/
@[simp] theorem ofFun_step (f : E → O) (t : Unit) (e : E) :
    (ofFun f : QRSys R Unit E O).step t e = SubInstrument.pure (t, f e) :=
  rfl

/-- The system `S` on ports relabelled by `fe` on events and `fo` on outputs. -/
noncomputable def mapPorts (S : QRSys R τ EG OG) (fe : E → EG) (fo : OG → O) : QRSys R τ E O where
  init := S.init
  step t e := (S.step t (fe e)).bind fun q => SubInstrument.pure (q.1, fo q.2)

/-- Unfolding lemma of `mapPorts`: a step. -/
theorem mapPorts_step (S : QRSys R τ EG OG) (fe : E → EG) (fo : OG → O) (t : τ) (e : E) :
    (S.mapPorts fe fo).step t e =
      (S.step t (fe e)).bind fun q => SubInstrument.pure (q.1, fo q.2) :=
  rfl

/-! ## Registers framed together -/

section Frame

variable {M N : Type} [Fintype M] [Fintype N]

/-- The system `S` on the left factor of the register `M × N`. -/
noncomputable def frameR (S : QRSys M τ E O) (N : Type) [Fintype N] : QRSys (M × N) τ E O where
  init := S.init
  step t e := (S.step t e).frame N

/-- The system `S` on the right factor of the register `M × N`. -/
noncomputable def frameL (S : QRSys N τ E O) (M : Type) [Fintype M] : QRSys (M × N) τ E O where
  init := S.init
  step t e := OpenSystem.frameLeft (S.step t e) M

/-- The parallel composition of `S` on the register `M` and `T` on the register `N`, on the
register `M × N`. -/
noncomputable def parFramed (S : QRSys M τ E O) (T : QRSys N υ E' O') :
    QRSys (M × N) (τ × υ) (E ⊕ E') (O ⊕ O') :=
  (S.frameR N).par (T.frameL M)

/-- Framing on the right commutes with the cascade. -/
theorem frameR_seq (S : QRSys M τ E O) (T : QRSys M υ O P) :
    (S.seq T).frameR N = (S.frameR N).seq (T.frameR N) := by
  simp only [frameR, seq, SubInstrument.frame_bind, SubInstrument.frame_pure]

/-- Framing on the left commutes with the cascade. -/
theorem frameL_seq (S : QRSys N τ E O) (T : QRSys N υ O P) :
    (S.seq T).frameL M = (S.frameL M).seq (T.frameL M) := by
  simp only [frameL, seq, OpenSystem.frameLeft_bind, OpenSystem.frameLeft_pure]

end Frame

/-! ## Step maps -/

/-- The state map `f` is a step map from `S` to `T`: it sends the initial state of `S` to that
of `T` and commutes with the steps. -/
structure StepMap (S : QRSys R τ E O) (T : QRSys R υ E O) (f : τ → υ) : Prop where
  /-- The initial state is mapped to the initial state. -/
  init_map : f S.init = T.init
  /-- The map commutes with the steps. -/
  step : ∀ t e,
    (S.step t e).bind (fun p => SubInstrument.pure (f p.1, p.2)) = T.step (f t) e

namespace StepMap

/-- The identity is a step map from a system to itself. -/
theorem refl (S : QRSys R τ E O) : StepMap S S id :=
  ⟨rfl, fun t e => by simp⟩

/-- Step maps of the two components give a step map of the cascade. -/
theorem seq {S : QRSys R τ E O} {S' : QRSys R τ' E O} {T : QRSys R υ O P}
    {T' : QRSys R υ' O P} {f : τ → τ'} {g : υ → υ'} (hS : StepMap S S' f)
    (hT : StepMap T T' g) : StepMap (S.seq T) (S'.seq T') (Prod.map f g) where
  init_map := by
    change (f S.init, g T.init) = (S'.init, T'.init)
    rw [hS.init_map, hT.init_map]
  step s e := by
    simp only [seq_step, ← hS.step, ← hT.step,
      SubInstrument.bind_assoc, SubInstrument.pure_bind, Prod.map]

/-- Step maps of the two components give a step map of their parallel composition. -/
theorem par {S : QRSys R τ E O} {S' : QRSys R τ' E O} {T : QRSys R υ E' O'}
    {T' : QRSys R υ' E' O'} {f : τ → τ'} {g : υ → υ'} (hS : StepMap S S' f)
    (hT : StepMap T T' g) : StepMap (S.par T) (S'.par T') (Prod.map f g) where
  init_map := by
    change (f S.init, g T.init) = (S'.init, T'.init)
    rw [hS.init_map, hT.init_map]
  step s e := by
    rcases e with e | e
    · simp only [par_step_inl, ← hS.step,
        SubInstrument.bind_assoc, SubInstrument.pure_bind, Prod.map]
    · simp only [par_step_inr, ← hT.step,
        SubInstrument.bind_assoc, SubInstrument.pure_bind, Prod.map]

/-- A step map gives a step map of the systems on relabelled ports. -/
theorem mapPorts {S : QRSys R τ EG OG} {S' : QRSys R τ' EG OG} {f : τ → τ'}
    (h : StepMap S S' f) (fe : E → EG) (fo : OG → O) :
    StepMap (S.mapPorts fe fo) (S'.mapPorts fe fo) f where
  init_map := h.init_map
  step t e := by
    simp only [mapPorts_step, ← h.step, SubInstrument.bind_assoc, SubInstrument.pure_bind]

/-- A step map gives a step map of the systems framed on the right. -/
theorem frameR {M N : Type} [Fintype M] [Fintype N] {S : QRSys M τ E O}
    {S' : QRSys M τ' E O} {f : τ → τ'} (h : StepMap S S' f) :
    StepMap (S.frameR N) (S'.frameR N) f where
  init_map := h.init_map
  step t e := by
    simp only [QRSys.frameR, ← h.step, SubInstrument.frame_bind, SubInstrument.frame_pure]

/-- A step map gives a step map of the systems framed on the left. -/
theorem frameL {M N : Type} [Fintype M] [Fintype N] {S : QRSys N τ E O}
    {S' : QRSys N τ' E O} {f : τ → τ'} (h : StepMap S S' f) :
    StepMap (S.frameL M) (S'.frameL M) f where
  init_map := h.init_map
  step t e := by
    simp only [QRSys.frameL, ← h.step, OpenSystem.frameLeft_bind, OpenSystem.frameLeft_pure]

end StepMap

/-! ## Step equivalence -/

/-- A quantum reactive system on the register `R` with events `E` and outputs `O`, its state
type bundled. -/
structure Obj (R : Type) [Fintype R] (E O : Type) : Type 1 where
  /-- The state type. -/
  St : Type
  /-- The system. -/
  sys : QRSys R St E O

/-- `A` and `B` are related by a step map. -/
def StepRel (A B : Obj R E O) : Prop :=
  ∃ f : A.St → B.St, StepMap A.sys B.sys f

/-- Step equivalence: the equivalence relation generated by step maps. -/
def StepEq : Obj R E O → Obj R E O → Prop :=
  Relation.EqvGen StepRel

/-- A step map gives step equivalence. -/
theorem StepMap.stepEq {S : QRSys R τ E O} {T : QRSys R υ E O} {f : τ → υ}
    (h : StepMap S T f) : StepEq (⟨τ, S⟩ : Obj R E O) ⟨υ, T⟩ :=
  Relation.EqvGen.rel _ _ ⟨f, h⟩

/-- A map of bundled systems that sends step maps to step maps preserves step equivalence. -/
theorem StepEq.map {R₂ : Type} [Fintype R₂] {E₁ O₁ E₂ O₂ : Type}
    (F : Obj R E₁ O₁ → Obj R₂ E₂ O₂)
    (hF : ∀ A B, StepRel A B → StepRel (F A) (F B)) {A B : Obj R E₁ O₁} (h : StepEq A B) :
    StepEq (F A) (F B) := by
  induction h with
  | rel A B h => exact Relation.EqvGen.rel _ _ (hF A B h)
  | refl A => exact Relation.EqvGen.refl _
  | symm A B _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans A B C _ _ ih₁ ih₂ => exact Relation.EqvGen.trans _ _ _ ih₁ ih₂

namespace Obj

/-- The cascade of bundled systems. -/
noncomputable def seq (A : Obj R E O) (B : Obj R O P) : Obj R E P :=
  ⟨A.St × B.St, A.sys.seq B.sys⟩

/-- The parallel composition of bundled systems. -/
noncomputable def par (A : Obj R E O) (B : Obj R E' O') : Obj R (E ⊕ E') (O ⊕ O') :=
  ⟨A.St × B.St, A.sys.par B.sys⟩

/-- A bundled system on relabelled ports. -/
noncomputable def mapPorts (A : Obj R EG OG) (fe : E → EG) (fo : OG → O) : Obj R E O :=
  ⟨A.St, A.sys.mapPorts fe fo⟩

/-- The stateless forwarding system. -/
noncomputable def idSys (R : Type) [Fintype R] (E : Type) : Obj R E E :=
  ⟨Unit, ofFun id⟩

end Obj

/-- Step equivalence is a congruence for the cascade. -/
theorem StepEq.seq {A A' : Obj R E O} {B B' : Obj R O P} (hA : StepEq A A')
    (hB : StepEq B B') : StepEq (A.seq B) (A'.seq B') := by
  refine Relation.EqvGen.trans _ (A'.seq B) _ ?_ ?_
  · exact StepEq.map (fun A => A.seq B)
      (fun _ _ ⟨_, h⟩ => ⟨_, h.seq (StepMap.refl B.sys)⟩) hA
  · exact StepEq.map (fun B => A'.seq B)
      (fun _ _ ⟨_, h⟩ => ⟨_, (StepMap.refl A'.sys).seq h⟩) hB

/-- Step equivalence is a congruence for the parallel composition. -/
theorem StepEq.par {A A' : Obj R E O} {B B' : Obj R E' O'} (hA : StepEq A A')
    (hB : StepEq B B') : StepEq (A.par B) (A'.par B') := by
  refine Relation.EqvGen.trans _ (A'.par B) _ ?_ ?_
  · exact StepEq.map (fun A => A.par B)
      (fun _ _ ⟨_, h⟩ => ⟨_, h.par (StepMap.refl B.sys)⟩) hA
  · exact StepEq.map (fun B => A'.par B)
      (fun _ _ ⟨_, h⟩ => ⟨_, (StepMap.refl A'.sys).par h⟩) hB

/-- Step equivalence is a congruence for relabelling the ports. -/
theorem StepEq.mapPorts {A A' : Obj R EG OG} (h : StepEq A A') (fe : E → EG) (fo : OG → O) :
    StepEq (A.mapPorts fe fo) (A'.mapPorts fe fo) :=
  StepEq.map (fun A => A.mapPorts fe fo) (fun _ _ ⟨_, h⟩ => ⟨_, h.mapPorts fe fo⟩) h

/-! ## Unit and associativity laws of the cascade -/

/-- The forwarding system cascaded before `S`: `Prod.snd` is a step map to `S`. -/
theorem StepMap.id_seq (S : QRSys R τ E O) : StepMap ((ofFun id).seq S) S Prod.snd :=
  ⟨rfl, fun s e => by simp [seq_step]⟩

/-- The forwarding system cascaded after `S`: `Prod.fst` is a step map to `S`. -/
theorem StepMap.seq_id (S : QRSys R τ E O) : StepMap (S.seq (ofFun id)) S Prod.fst :=
  ⟨rfl, fun s e => by simp [seq_step]⟩

/-- Reassociation of the states is a step map between the two cascades of three systems. -/
theorem StepMap.seq_assoc (S : QRSys R τ E O) (T : QRSys R υ O P) (V : QRSys R ρ P Q) :
    StepMap ((S.seq T).seq V) (S.seq (T.seq V)) (fun s => (s.1.1, (s.1.2, s.2))) :=
  ⟨rfl, fun s e => by simp [seq_step]⟩

/-- The forwarding system cascaded before `A` is step equivalent to `A`. -/
theorem StepEq.id_seq (A : Obj R E O) : StepEq ((Obj.idSys R E).seq A) A :=
  (StepMap.id_seq A.sys).stepEq

/-- The forwarding system cascaded after `A` is step equivalent to `A`. -/
theorem StepEq.seq_id (A : Obj R E O) : StepEq (A.seq (Obj.idSys R O)) A :=
  (StepMap.seq_id A.sys).stepEq

/-- The cascade is associative up to step equivalence. -/
theorem StepEq.seq_assoc (A : Obj R E O) (B : Obj R O P) (C : Obj R P Q) :
    StepEq ((A.seq B).seq C) (A.seq (B.seq C)) :=
  (StepMap.seq_assoc A.sys B.sys C.sys).stepEq

/-! ## Laws of the parallel composition -/

/-- The cascade of two stateless systems is the stateless system of the composite. -/
theorem StepMap.ofFun_seq (f : E → O) (g : O → P) :
    StepMap ((ofFun f : QRSys R Unit E O).seq (ofFun g)) (ofFun (g ∘ f)) (fun _ => ()) :=
  ⟨rfl, fun _ _ => by simp [seq_step]⟩

/-- The parallel composition of two stateless systems is the stateless system of the sum of
the functions. -/
theorem StepMap.ofFun_par (f : E → O) (g : E' → O') :
    StepMap ((ofFun f : QRSys R Unit E O).par (ofFun g)) (ofFun (Sum.map f g)) (fun _ => ()) :=
  ⟨rfl, fun _ e => by rcases e with e | e <;> simp⟩

/-- **Interchange.** The parallel composition of two cascades is the cascade of the parallel
compositions; the state map exchanges the middle components. -/
theorem StepMap.seq_par (S : QRSys R τ E O) (T : QRSys R υ O P) (S' : QRSys R τ' E' O')
    (T' : QRSys R υ' O' P') :
    StepMap ((S.seq T).par (S'.seq T')) ((S.par S').seq (T.par T'))
      (fun s => ((s.1.1, s.2.1), (s.1.2, s.2.2))) :=
  ⟨rfl, fun s e => by rcases e with e | e <;> simp [seq_step]⟩

/-- **Naturality of the associator.** -/
theorem StepMap.par_assoc_seq (S : QRSys R τ E O) (T : QRSys R υ E' O')
    (V : QRSys R ρ E'' P) :
    StepMap (((S.par T).par V).seq (ofFun (Equiv.sumAssoc O O' P)))
      ((ofFun (Equiv.sumAssoc E E' E'')).seq (S.par (T.par V)))
      (fun s => ((), (s.1.1.1, (s.1.1.2, s.1.2)))) :=
  ⟨rfl, fun s e => by rcases e with (e | e) | e <;> simp [seq_step]⟩

/-- **Naturality of the symmetry.** -/
theorem StepMap.par_swap_seq (S : QRSys R τ E O) (T : QRSys R υ E' O') :
    StepMap ((S.par T).seq (ofFun (Equiv.sumComm O O')))
      ((ofFun (Equiv.sumComm E E')).seq (T.par S)) (fun s => ((), (s.1.2, s.1.1))) :=
  ⟨rfl, fun s e => by rcases e with e | e <;> simp [seq_step]⟩

/-- **Naturality of the left unitor.** -/
theorem StepMap.empty_par_seq (S : QRSys R τ E O) :
    StepMap (((ofFun (id : Empty → Empty)).par S).seq (ofFun (Equiv.emptySum Empty O)))
      ((ofFun (Equiv.emptySum Empty E)).seq S) (fun s => ((), s.1.2)) :=
  ⟨rfl, fun s e => by
    rcases e with e | e
    · exact e.elim
    · simp [seq_step]⟩

/-- **Naturality of the right unitor.** -/
theorem StepMap.par_empty_seq (S : QRSys R τ E O) :
    StepMap ((S.par (ofFun (id : Empty → Empty))).seq (ofFun (Equiv.sumEmpty O Empty)))
      ((ofFun (Equiv.sumEmpty E Empty)).seq S) (fun s => ((), s.1.1)) :=
  ⟨rfl, fun s e => by
    rcases e with e | e
    · simp [seq_step]
    · exact e.elim⟩

end QRSys

/-! ## The category of port types -/

/-- Step equivalence as a setoid on bundled systems. -/
instance QRSys.Obj.stepSetoid (R : Type) [Fintype R] (E O : Type) : Setoid (QRSys.Obj R E O) :=
  ⟨QRSys.StepEq, Relation.EqvGen.is_equivalence _⟩

/-- A type of ports of quantum reactive systems on the register `R`. -/
structure QSysCat (R : Type) [Fintype R] : Type 1 where
  /-- The ports. -/
  P : Type

namespace QSysCat

open CategoryTheory MonoidalCategory

variable {R : Type} [Fintype R]

/-- The category of port types: a morphism from `X` to `Y` is a quantum reactive system on `R`
with events `X.P` and outputs `Y.P` modulo step equivalence; composition is the cascade and the
identity is the forwarding system. -/
noncomputable instance category : Category.{1} (QSysCat R) where
  Hom X Y := Quotient (QRSys.Obj.stepSetoid R X.P Y.P)
  id X := ⟦QRSys.Obj.idSys R X.P⟧
  comp := Quotient.map₂ QRSys.Obj.seq fun _ _ h₁ _ _ h₂ => QRSys.StepEq.seq h₁ h₂
  id_comp := by
    rintro X Y ⟨A⟩
    exact Quotient.sound (QRSys.StepEq.id_seq A)
  comp_id := by
    rintro X Y ⟨A⟩
    exact Quotient.sound (QRSys.StepEq.seq_id A)
  assoc := by
    rintro W X Y Z ⟨A⟩ ⟨B⟩ ⟨C⟩
    exact Quotient.sound (QRSys.StepEq.seq_assoc A B C)

/-- The morphism given by a function of ports: the class of the stateless system
`QRSys.ofFun f`. -/
noncomputable def homOfFun {X Y : QSysCat R} (f : X.P → Y.P) : X ⟶ Y :=
  ⟦⟨Unit, QRSys.ofFun f⟩⟧

/-- Composition of morphisms given by functions is composition of the functions. -/
theorem homOfFun_comp {X Y Z : QSysCat R} (f : X.P → Y.P) (g : Y.P → Z.P) :
    homOfFun f ≫ homOfFun g = homOfFun (g ∘ f) :=
  Quotient.sound (QRSys.StepMap.ofFun_seq f g).stepEq

/-- The isomorphism of port types given by an equivalence of the ports. -/
noncomputable def isoOfEquiv {X Y : QSysCat R} (e : X.P ≃ Y.P) : X ≅ Y where
  hom := homOfFun e
  inv := homOfFun e.symm
  hom_inv_id := by
    rw [homOfFun_comp, e.symm_comp_self]
    rfl
  inv_hom_id := by
    rw [homOfFun_comp, e.self_comp_symm]
    rfl

/-- Unfolding lemma of `isoOfEquiv`: the forward morphism. -/
theorem isoOfEquiv_hom {X Y : QSysCat R} (e : X.P ≃ Y.P) : (isoOfEquiv e).hom = homOfFun e :=
  rfl

/-- Unfolding lemma of `isoOfEquiv`: the backward morphism. -/
theorem isoOfEquiv_inv {X Y : QSysCat R} (e : X.P ≃ Y.P) :
    (isoOfEquiv e).inv = homOfFun e.symm :=
  rfl

/-- The tensor product of morphisms: the parallel composition. -/
noncomputable def tensorHom {X₁ Y₁ X₂ Y₂ : QSysCat R} (f : X₁ ⟶ Y₁) (g : X₂ ⟶ Y₂) :
    (⟨X₁.P ⊕ X₂.P⟩ : QSysCat R) ⟶ ⟨Y₁.P ⊕ Y₂.P⟩ :=
  Quotient.map₂ QRSys.Obj.par (fun _ _ h₁ _ _ h₂ => QRSys.StepEq.par h₁ h₂) f g

/-- **Interchange.** The tensor product of morphisms commutes with composition. -/
theorem tensorHom_comp {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : QSysCat R} (f₁ : X₁ ⟶ Y₁) (f₂ : X₂ ⟶ Y₂)
    (g₁ : Y₁ ⟶ Z₁) (g₂ : Y₂ ⟶ Z₂) :
    tensorHom f₁ f₂ ≫ tensorHom g₁ g₂ = tensorHom (f₁ ≫ g₁) (f₂ ≫ g₂) := by
  induction f₁ using Quotient.inductionOn
  induction f₂ using Quotient.inductionOn
  induction g₁ using Quotient.inductionOn
  induction g₂ using Quotient.inductionOn
  exact (Quotient.sound (QRSys.StepMap.seq_par _ _ _ _).stepEq).symm

/-- The tensor product of morphisms given by functions is given by the sum of the functions. -/
theorem homOfFun_tensorHom {X₁ Y₁ X₂ Y₂ : QSysCat R} (f : X₁.P → Y₁.P) (g : X₂.P → Y₂.P) :
    tensorHom (homOfFun f) (homOfFun g) =
      homOfFun (X := ⟨X₁.P ⊕ X₂.P⟩) (Y := ⟨Y₁.P ⊕ Y₂.P⟩) (Sum.map f g) :=
  Quotient.sound (QRSys.StepMap.ofFun_par f g).stepEq

/-- The monoidal data: sums of ports, the parallel composition, the unit `Empty`, and the
structure isomorphisms of the sum equivalences. -/
noncomputable instance monoidalCategoryStruct : MonoidalCategoryStruct (QSysCat R) where
  tensorObj X Y := ⟨X.P ⊕ Y.P⟩
  tensorHom := tensorHom
  whiskerLeft X _ _ g := tensorHom (𝟙 X) g
  whiskerRight f Y := tensorHom f (𝟙 Y)
  tensorUnit := ⟨Empty⟩
  associator X Y Z := isoOfEquiv (Equiv.sumAssoc X.P Y.P Z.P)
  leftUnitor X := isoOfEquiv (Equiv.emptySum Empty X.P)
  rightUnitor X := isoOfEquiv (Equiv.sumEmpty X.P Empty)

/-- Unfolding lemma of the identity: the morphism of the identity function. -/
theorem id_eq_homOfFun (X : QSysCat R) : 𝟙 X = homOfFun id :=
  rfl

/-- Unfolding lemma of the associator. -/
theorem associator_def (X Y Z : QSysCat R) :
    α_ X Y Z = isoOfEquiv (X := (X ⊗ Y) ⊗ Z) (Y := X ⊗ (Y ⊗ Z)) (Equiv.sumAssoc X.P Y.P Z.P) :=
  rfl

/-- Unfolding lemma of the left unitor. -/
theorem leftUnitor_def (X : QSysCat R) :
    λ_ X = isoOfEquiv (X := 𝟙_ (QSysCat R) ⊗ X) (Y := X) (Equiv.emptySum Empty X.P) :=
  rfl

/-- Unfolding lemma of the right unitor. -/
theorem rightUnitor_def (X : QSysCat R) :
    ρ_ X = isoOfEquiv (X := X ⊗ 𝟙_ (QSysCat R)) (Y := X) (Equiv.sumEmpty X.P Empty) :=
  rfl

/-- Whiskering a morphism given by a function on the left. -/
theorem whiskerLeft_homOfFun (X : QSysCat R) {Y Z : QSysCat R} (g : Y.P → Z.P) :
    X ◁ homOfFun g = homOfFun (X := X ⊗ Y) (Y := X ⊗ Z) (Sum.map id g) :=
  homOfFun_tensorHom id g

/-- Whiskering a morphism given by a function on the right. -/
theorem whiskerRight_homOfFun {X Y : QSysCat R} (f : X.P → Y.P) (Z : QSysCat R) :
    homOfFun f ▷ Z = homOfFun (X := X ⊗ Z) (Y := Y ⊗ Z) (Sum.map f id) :=
  homOfFun_tensorHom f id

/-- `QSysCat R` is a monoidal category under the parallel composition. -/
noncomputable instance monoidalCategory : MonoidalCategory (QSysCat R) where
  toMonoidalCategoryStruct := monoidalCategoryStruct
  tensorHom_def f g := by
    change tensorHom f g = tensorHom f (𝟙 _) ≫ tensorHom (𝟙 _) g
    rw [tensorHom_comp, Category.comp_id, Category.id_comp]
  id_tensorHom_id _ _ := by
    change tensorHom (homOfFun id) (homOfFun id) = homOfFun id
    rw [homOfFun_tensorHom, Sum.map_id_id]
  tensorHom_comp_tensorHom := tensorHom_comp
  whiskerLeft_id _ _ := by
    change tensorHom (homOfFun id) (homOfFun id) = homOfFun id
    rw [homOfFun_tensorHom, Sum.map_id_id]
  id_whiskerRight _ _ := by
    change tensorHom (homOfFun id) (homOfFun id) = homOfFun id
    rw [homOfFun_tensorHom, Sum.map_id_id]
  associator_naturality := by
    rintro _ _ _ _ _ _ ⟨A⟩ ⟨B⟩ ⟨C⟩
    exact Quotient.sound (QRSys.StepMap.par_assoc_seq A.sys B.sys C.sys).stepEq
  leftUnitor_naturality := by
    rintro _ _ ⟨A⟩
    exact Quotient.sound (QRSys.StepMap.empty_par_seq A.sys).stepEq
  rightUnitor_naturality := by
    rintro _ _ ⟨A⟩
    exact Quotient.sound (QRSys.StepMap.par_empty_seq A.sys).stepEq
  pentagon _ _ _ _ := by
    simp only [associator_def, isoOfEquiv_hom, whiskerLeft_homOfFun, whiskerRight_homOfFun,
      homOfFun_comp]
    congr 1
    funext e
    rcases e with ((e | e) | e) | e <;> rfl
  triangle _ _ := by
    simp only [associator_def, leftUnitor_def, rightUnitor_def, isoOfEquiv_hom,
      whiskerLeft_homOfFun, whiskerRight_homOfFun, homOfFun_comp]
    congr 1
    funext e
    rcases e with (e | e) | e
    · rfl
    · exact e.elim
    · rfl

/-- `QSysCat R` is a symmetric monoidal category; the symmetry swaps the summands. -/
noncomputable instance symmetricCategory : SymmetricCategory (QSysCat R) where
  braiding X Y := isoOfEquiv (X := ⟨X.P ⊕ Y.P⟩) (Y := ⟨Y.P ⊕ X.P⟩) (Equiv.sumComm X.P Y.P)
  braiding_naturality_right := by
    rintro _ _ _ ⟨A⟩
    exact Quotient.sound (QRSys.StepMap.par_swap_seq (QRSys.ofFun id) A.sys).stepEq
  braiding_naturality_left := by
    rintro _ _ ⟨A⟩ _
    exact Quotient.sound (QRSys.StepMap.par_swap_seq A.sys (QRSys.ofFun id)).stepEq
  hexagon_forward _ _ _ := by
    simp only [associator_def, isoOfEquiv_hom, whiskerLeft_homOfFun, whiskerRight_homOfFun,
      homOfFun_comp]
    congr 1
    funext e
    rcases e with (e | e) | e <;> rfl
  hexagon_reverse _ _ _ := by
    simp only [associator_def, isoOfEquiv_hom, isoOfEquiv_inv, whiskerLeft_homOfFun,
      whiskerRight_homOfFun, homOfFun_comp]
    congr 1
    funext e
    rcases e with e | e | e <;> rfl
  symmetry _ _ := by
    simp only [isoOfEquiv_hom, homOfFun_comp, id_eq_homOfFun]
    congr 1
    funext e
    rcases e with e | e <;> rfl

end QSysCat

/-! ## The unbounded feedback loop -/

namespace QRSys

variable {R : Type} [Fintype R]
variable {τ υ ρ γ E O E' O' X Y W : Type}

/-- The activation of the loopback of `S` from the event `g` in the state `t` with `n` further
calls allowed, failing when a wire value is answered to the last allowed call. -/
noncomputable def fbRunFail (S : QRSys R τ (E ⊕ X) (O ⊕ X)) :
    ℕ → E ⊕ X → τ → SubInstrument R R (τ × O)
  | 0, g, t => (S.step t g).bind fun q =>
      Sum.elim (fun o => SubInstrument.pure (q.1, o)) (fun _ => SubInstrument.fail) q.2
  | n + 1, g, t => (S.step t g).bind fun q =>
      Sum.elim (fun o => SubInstrument.pure (q.1, o)) (fun x => fbRunFail S n (.inr x) q.1) q.2

/-- `fbRunFail` grows with one more call allowed. -/
theorem fbRunFail_le_succ (S : QRSys R τ (E ⊕ X) (O ⊕ X)) :
    ∀ (n : ℕ) (g : E ⊕ X) (t : τ), S.fbRunFail n g t ≤ S.fbRunFail (n + 1) g t := by
  intro n
  induction n with
  | zero =>
    intro g t
    refine SubInstrument.bind_mono_right _ fun q => ?_
    rcases q with ⟨t', o | x⟩
    · exact le_rfl
    · exact SubInstrument.fail_le _
  | succ n ih =>
    intro g t
    refine SubInstrument.bind_mono_right _ fun q => ?_
    rcases q with ⟨t', o | x⟩
    · exact le_rfl
    · exact ih _ _

/-- `fbRunFail` is monotone in the fuel. -/
theorem fbRunFail_mono (S : QRSys R τ (E ⊕ X) (O ⊕ X)) (g : E ⊕ X) (t : τ) :
    Monotone fun n => S.fbRunFail n g t :=
  monotone_nat_of_le_succ fun n => S.fbRunFail_le_succ n g t

/-- The chain of activations failing on exhausted fuel. -/
noncomputable def fbChain (S : QRSys R τ (E ⊕ X) (O ⊕ X)) (g : E ⊕ X) (t : τ) :
    Chain (SubInstrument R R (τ × O)) :=
  ⟨fun n => S.fbRunFail n g t, S.fbRunFail_mono g t⟩

/-- The unbounded activation of the loopback of `S`: the supremum over the fuel of
`fbRunFail` in Selinger's order. -/
noncomputable def fbRunω (S : QRSys R τ (E ⊕ X) (O ⊕ X)) (g : E ⊕ X) (t : τ) :
    SubInstrument R R (τ × O) :=
  ωSup (S.fbChain g t)

/-- The unbounded loopback of `S` along its wire `X`: an outer event `e` runs `fbRunω` from the
event `inl e`. -/
noncomputable def loopbackω (S : QRSys R τ (E ⊕ X) (O ⊕ X)) : QRSys R τ E O where
  init := S.init
  step t e := S.fbRunω (.inl e) t

/-- Unfolding lemma of `loopbackω`: a step. -/
theorem loopbackω_step (S : QRSys R τ (E ⊕ X) (O ⊕ X)) (t : τ) (e : E) :
    S.loopbackω.step t e = S.fbRunω (.inl e) t :=
  rfl

/-- **Unfolding equation.** The unbounded activation is one step of `S`, followed on an output
`inl o` by the end of the activation and on an output `inr x` by the unbounded activation from
the event `inr x`. -/
theorem fbRunω_eq (S : QRSys R τ (E ⊕ X) (O ⊕ X)) (g : E ⊕ X) (t : τ) :
    S.fbRunω g t = (S.step t g).bind fun q =>
      Sum.elim (fun o => SubInstrument.pure (q.1, o)) (fun x => S.fbRunω (.inr x) q.1) q.2 := by
  let K : Chain (τ × (O ⊕ X) → SubInstrument R R (τ × O)) :=
    ⟨fun n q => Sum.elim (fun o => SubInstrument.pure (q.1, o))
      (fun x => S.fbRunFail n (.inr x) q.1) q.2, fun m n hmn q => by
        rcases q with ⟨t', o | x⟩
        · exact le_rfl
        · exact S.fbRunFail_mono _ _ hmn⟩
  have hK : (fun q : τ × (O ⊕ X) => Sum.elim (fun o => SubInstrument.pure (q.1, o))
      (fun x => S.fbRunω (.inr x) q.1) q.2) = ωSup K := by
    funext q
    rw [(ωScottContinuous.apply (β := fun _ => SubInstrument R R (τ × O)) q).map_ωSup K]
    rcases q with ⟨t', o | x⟩
    · exact le_antisymm (le_ωSup_of_le 0 le_rfl) (ωSup_le _ _ fun _ => le_rfl)
    · rfl
  apply le_antisymm
  · refine ωSup_le _ _ fun n => ?_
    cases n with
    | zero =>
      change S.fbRunFail 0 g t ≤ _
      rw [fbRunFail]
      refine SubInstrument.bind_mono_right _ fun q => ?_
      rcases q with ⟨t', o | x⟩
      · exact le_rfl
      · exact SubInstrument.fail_le _
    | succ n =>
      change S.fbRunFail (n + 1) g t ≤ _
      rw [fbRunFail]
      refine SubInstrument.bind_mono_right _ fun q => ?_
      rcases q with ⟨t', o | x⟩
      · exact le_rfl
      · exact le_ωSup (S.fbChain (.inr x) t') n
  · rw [hK, SubInstrument.bind_ωSup]
    exact ωSup_le _ _ fun n => le_ωSup (S.fbChain g t) (n + 1)

/-- When the activations failing on exhausted fuel of `S'` are those of `S` followed by `k` at
every fuel, the unbounded activation of `S'` is that of `S` followed by `k`. -/
theorem fbRunω_eq_bind_of_fbRunFail {υ E₁ O₁ X₁ : Type} {S : QRSys R τ (E ⊕ X) (O ⊕ X)}
    {S' : QRSys R υ (E₁ ⊕ X₁) (O₁ ⊕ X₁)} {g : E ⊕ X} {t : τ} {g' : E₁ ⊕ X₁} {t' : υ}
    (k : τ × O → SubInstrument R R (υ × O₁))
    (h : ∀ n, S'.fbRunFail n g' t' = (S.fbRunFail n g t).bind k) :
    S'.fbRunω g' t' = (S.fbRunω g t).bind k := by
  change ωSup (S'.fbChain g' t') = (ωSup (S.fbChain g t)).bind k
  rw [SubInstrument.ωSup_bind]
  exact le_antisymm (ωSup_le _ _ fun n => le_ωSup_of_le n (h n).le)
    (ωSup_le _ _ fun n => le_ωSup_of_le n (h n).ge)

/-! ## Step maps under the unbounded loopback -/

/-- A step map commutes with the activation failing on exhausted fuel. -/
theorem fbRunFail_stepMap {S : QRSys R τ (E ⊕ X) (O ⊕ X)} {S' : QRSys R υ (E ⊕ X) (O ⊕ X)}
    {f : τ → υ} (h : StepMap S S' f) :
    ∀ (m : ℕ) (g : E ⊕ X) (t : τ),
      (S.fbRunFail m g t).bind (fun p => SubInstrument.pure (f p.1, p.2)) =
        S'.fbRunFail m g (f t) := by
  intro m
  induction m with
  | zero =>
    intro g t
    simp only [fbRunFail, ← h.step t g, SubInstrument.bind_assoc, SubInstrument.pure_bind]
    congr 1; funext q; rcases q with ⟨t', o | x⟩ <;> simp
  | succ m ih =>
    intro g t
    simp only [fbRunFail, ← h.step t g, SubInstrument.bind_assoc, SubInstrument.pure_bind]
    congr 1; funext q; rcases q with ⟨t', o | x⟩
    · simp
    · simpa using ih (.inr x) t'

/-- **Step maps under unbounded feedback.** A step map from `S` to `S'` is a step map from the
unbounded loopback of `S` to that of `S'`. -/
theorem loopbackω_stepMap {S : QRSys R τ (E ⊕ X) (O ⊕ X)} {S' : QRSys R υ (E ⊕ X) (O ⊕ X)}
    {f : τ → υ} (h : StepMap S S' f) : StepMap S.loopbackω S'.loopbackω f where
  init_map := h.init_map
  step t e := (fbRunω_eq_bind_of_fbRunFail (S := S) (S' := S') _
    fun n => (fbRunFail_stepMap h n (.inl e) t).symm).symm

/-! ## Naturality in the outer ports -/

/-- **Tightening on the event side.** A system `g` on the outer events, beside the forwarding
of the wire and cascaded into `S`, commutes with the unbounded loopback. -/
theorem loopbackω_seq_left (g : QRSys R γ E' E) (S : QRSys R τ (E ⊕ X) (O ⊕ X)) :
    StepMap ((g.par (ofFun (id : X → X))).seq S).loopbackω (g.seq S.loopbackω)
      (fun u => (u.1.1, u.2)) := by
  set L := (g.par (ofFun (id : X → X))).seq S with hL
  have hstepR : ∀ (x : X) (c : γ) (v : Unit) (t : τ),
      L.step ((c, v), t) (.inr x) =
        (S.step t (.inr x)).bind fun r => SubInstrument.pure (((c, v), r.1), r.2) := by
    intro x c v t
    simp [hL, seq_step]
  have hstepL : ∀ (e : E') (c : γ) (v : Unit) (t : τ),
      L.step ((c, v), t) (.inl e) = (g.step c e).bind fun q =>
        (S.step t (.inl q.2)).bind fun r => SubInstrument.pure (((q.1, v), r.1), r.2) := by
    intro e c v t
    simp [hL, seq_step]
  have hrunR : ∀ (n : ℕ) (x : X) (c : γ) (v : Unit) (t : τ),
      L.fbRunFail n (.inr x) ((c, v), t) =
        (S.fbRunFail n (.inr x) t).bind fun p => SubInstrument.pure (((c, v), p.1), p.2) := by
    intro n
    induction n with
    | zero =>
      intro x c v t
      simp only [fbRunFail, hstepR, SubInstrument.bind_assoc, SubInstrument.pure_bind]
      congr 1; funext q; rcases q with ⟨t', o | x'⟩ <;> simp
    | succ n ih =>
      intro x c v t
      simp only [fbRunFail, hstepR, SubInstrument.bind_assoc, SubInstrument.pure_bind]
      congr 1; funext q; rcases q with ⟨t', o | x'⟩
      · simp
      · simpa using ih x' c v t'
  have hrunRω : ∀ (x : X) (c : γ) (v : Unit) (t : τ),
      L.fbRunω (.inr x) ((c, v), t) =
        (S.fbRunω (.inr x) t).bind fun p => SubInstrument.pure (((c, v), p.1), p.2) :=
    fun x c v t => fbRunω_eq_bind_of_fbRunFail _ fun n => hrunR n x c v t
  refine ⟨rfl, fun u e => ?_⟩
  obtain ⟨⟨c, v⟩, t⟩ := u
  rw [loopbackω_step, fbRunω_eq, hstepL, seq_step]
  simp only [loopbackω_step, fbRunω_eq S (.inl _), SubInstrument.bind_assoc,
    SubInstrument.pure_bind]
  congr 1; funext q; congr 1; funext r; rcases r with ⟨t', o | x'⟩
  · simp
  · simp [hrunRω]

/-- The activation failing on exhausted fuel of `S` cascaded into `h` beside the forwarding of
the wire is the activation of `S` followed by a step of `h`, at every fuel. -/
theorem fbRunFail_seq_right (S : QRSys R τ (E ⊕ X) (O ⊕ X)) (h : QRSys R ρ O O') :
    ∀ (n : ℕ) (ev : E ⊕ X) (t : τ) (c : ρ) (v : Unit),
      (S.seq (h.par (ofFun (id : X → X)))).fbRunFail n ev (t, (c, v)) =
        (S.fbRunFail n ev t).bind fun p =>
          (h.step c p.2).bind fun r => SubInstrument.pure ((p.1, (r.1, v)), r.2) := by
  intro n
  induction n with
  | zero =>
    intro ev t c v
    simp only [fbRunFail, seq_step, SubInstrument.bind_assoc, SubInstrument.pure_bind]
    congr 1; funext q; rcases q with ⟨t', o | x⟩ <;> simp
  | succ n ih =>
    intro ev t c v
    simp only [fbRunFail, seq_step, SubInstrument.bind_assoc, SubInstrument.pure_bind]
    congr 1; funext q; rcases q with ⟨t', o | x⟩
    · simp
    · simpa using ih (.inr x) t' c v

/-- **Tightening on the output side.** The unbounded loopback of `S` cascaded into `h` beside
the forwarding of the wire is the unbounded loopback of `S` cascaded into `h`. -/
theorem loopbackω_seq_right (S : QRSys R τ (E ⊕ X) (O ⊕ X)) (h : QRSys R ρ O O') :
    StepMap (S.seq (h.par (ofFun (id : X → X)))).loopbackω (S.loopbackω.seq h)
      (fun u => (u.1, u.2.1)) := by
  refine ⟨rfl, fun u e => ?_⟩
  obtain ⟨t, c, v⟩ := u
  rw [loopbackω_step, fbRunω_eq_bind_of_fbRunFail _ fun n => fbRunFail_seq_right S h n _ t c v,
    seq_step, loopbackω_step]
  simp

/-! ## Dinaturality in the wire -/

section Slide

variable (S : QRSys R τ (E ⊕ X) (O ⊕ Y)) (g : QRSys R γ Y X)

/-- The activations of the loopback along `Y` of `g` placed before `S` are those of the loopback
along `X` of `g` placed after `S` with the states exchanged, at every fuel. -/
theorem fbRunFail_seq_slide :
    ∀ (n : ℕ) (y : Y) (c : γ) (w : Unit) (t : τ),
      (((ofFun (id : E → E)).par g).seq S).fbRunFail n (.inr y) ((w, c), t) =
        (g.step c y).bind fun q2 =>
          ((S.seq ((ofFun (id : O → O)).par g)).fbRunFail n (.inr q2.2) (t, (w, q2.1))).bind
            fun p => SubInstrument.pure (p.1.swap, p.2) := by
  intro n
  induction n with
  | zero =>
    intro y c w t
    simp only [fbRunFail, seq_step, par_step_inr, SubInstrument.bind_assoc,
      SubInstrument.pure_bind]
    congr 1; funext q2; congr 1; funext r; rcases r with ⟨t', o | y'⟩ <;> simp
  | succ n ih =>
    intro y c w t
    simp only [fbRunFail, seq_step, par_step_inr, SubInstrument.bind_assoc,
      SubInstrument.pure_bind]
    congr 1; funext q2; congr 1; funext r; rcases r with ⟨t', o | y'⟩
    · simp
    · simpa using ih y' q2.1 w t'

/-- The activation of the loopback along `Y` of `g` placed before `S` from an outer event is
that of the loopback along `X` of `g` placed after `S`, with the states exchanged. -/
theorem fbRunFail_seq_slide_inl (n : ℕ) (e : E) (w : Unit) (c : γ) (t : τ) :
    (((ofFun (id : E → E)).par g).seq S).fbRunFail n (.inl e) ((w, c), t) =
      ((S.seq ((ofFun (id : O → O)).par g)).fbRunFail n (.inl e) (t, (w, c))).bind
        fun p => SubInstrument.pure (p.1.swap, p.2) := by
  cases n with
  | zero =>
    simp only [fbRunFail, seq_step, par_step_inl, ofFun_step, id_eq, SubInstrument.bind_assoc,
      SubInstrument.pure_bind]
    congr 1; funext r; rcases r with ⟨t', o | y'⟩ <;> simp
  | succ n =>
    simp only [fbRunFail, seq_step, par_step_inl, ofFun_step, id_eq, SubInstrument.bind_assoc,
      SubInstrument.pure_bind]
    congr 1; funext r; rcases r with ⟨t', o | y'⟩
    · simp
    · simpa using fbRunFail_seq_slide S g n y' c w t'

/-- **Sliding a system along the wire.** Exchanging the states is a step map from the unbounded
loopback along `X` of `g` placed after `S` to the unbounded loopback along `Y` of `g` placed
before `S`. -/
theorem loopbackω_slide :
    StepMap (S.seq ((ofFun (id : O → O)).par g)).loopbackω
      (((ofFun (id : E → E)).par g).seq S).loopbackω Prod.swap := by
  refine ⟨rfl, fun u e => ?_⟩
  obtain ⟨t, w, c⟩ := u
  exact (fbRunω_eq_bind_of_fbRunFail _ fun n => fbRunFail_seq_slide_inl S g n e w c t).symm

end Slide

/-! ## Vanishing for the empty wire and yanking -/

/-- **Vanishing for the empty wire.** The unbounded loopback along `Empty` is the system
between the unitors. -/
theorem loopbackω_empty (S : QRSys R τ (E ⊕ Empty) (O ⊕ Empty)) :
    StepMap S.loopbackω
      ((ofFun (Equiv.sumEmpty E Empty).symm).seq (S.seq (ofFun (Equiv.sumEmpty O Empty))))
      (fun t => ((), (t, ()))) := by
  refine ⟨rfl, fun t e => ?_⟩
  rw [loopbackω_step, fbRunω_eq]
  simp only [seq_step, ofFun_step, SubInstrument.bind_assoc, SubInstrument.pure_bind]
  congr 1; funext q; rcases q with ⟨t', o | x⟩
  · simp
  · exact x.elim

/-- **Yanking.** The unbounded loopback of the swap of the two copies of `X` is the forwarding
system. -/
theorem loopbackω_swap :
    StepMap (ofFun (Equiv.sumComm X X) : QRSys R Unit (X ⊕ X) (X ⊕ X)).loopbackω (ofFun id)
      id := by
  refine ⟨rfl, fun t e => ?_⟩
  rw [loopbackω_step, fbRunω_eq]
  simp only [ofFun_step, Equiv.sumComm_apply, Sum.swap_inl, SubInstrument.pure_bind,
    Sum.elim_inr]
  rw [fbRunω_eq]
  simp

/-- A system between two stateless systems is the system on relabelled ports. -/
theorem StepMap.ofFun_seq_seq_ofFun {EG OG : Type} (a : E → EG) (S : QRSys R τ EG OG)
    (b : OG → O) :
    StepMap ((ofFun a).seq (S.seq (ofFun b))) (S.mapPorts a b) (fun s => s.2.1) :=
  ⟨rfl, fun s e => by simp [seq_step, mapPorts_step]⟩

/-! ## Vanishing for a sum of wires -/

section Vanishing

variable (S : QRSys R τ (E ⊕ (X ⊕ Y)) (O ⊕ (X ⊕ Y)))

/-- **Vanishing for a sum of wires.** The unbounded activation of the loopback along `X` of the
unbounded loopback along `Y` of `S` (on reassociated ports) from an outer event is the unbounded
activation of `S` along `X ⊕ Y`. -/
theorem fbRunω_loopbackω_sumAssoc (e : E) (t : τ) :
    (S.mapPorts (Equiv.sumAssoc E X Y) (Equiv.sumAssoc O X Y).symm).loopbackω.fbRunω (.inl e) t =
      S.fbRunω (.inl e) t := by
  set G := S.mapPorts (Equiv.sumAssoc E X Y) (Equiv.sumAssoc O X Y).symm with hGdef
  set L := G.loopbackω with hLdef
  have hG : ∀ (t : τ) (ev : (E ⊕ X) ⊕ Y), G.step t ev =
      (S.step t (Equiv.sumAssoc E X Y ev)).bind fun q =>
        SubInstrument.pure (q.1, (Equiv.sumAssoc O X Y).symm q.2) := fun _ _ => rfl
  let Bext : (E ⊕ X) ⊕ Y → τ → SubInstrument R R (τ × O) := fun ev t =>
    (G.fbRunω ev t).bind fun q =>
      Sum.elim (fun o => SubInstrument.pure (q.1, o)) (fun x => L.fbRunω (.inr x) q.1) q.2
  have hL : ∀ (g : E ⊕ X) (t : τ), L.fbRunω g t = Bext (.inl g) t :=
    fun g t => fbRunω_eq L g t
  have hB : ∀ (ev : E ⊕ (X ⊕ Y)) (t : τ), Bext ((Equiv.sumAssoc E X Y).symm ev) t =
      (S.step t ev).bind fun q => Sum.elim (fun o => SubInstrument.pure (q.1, o))
        (fun w => Bext ((Equiv.sumAssoc E X Y).symm (.inr w)) q.1) q.2 := by
    intro ev t
    simp only [Bext]
    rw [fbRunω_eq G, hG]
    simp only [Equiv.apply_symm_apply, SubInstrument.bind_assoc, SubInstrument.pure_bind]
    congr 1; funext q; rcases q with ⟨t', o | x | y⟩
    · simp
    · simp only [Equiv.sumAssoc_symm_apply_inr_inl, Sum.elim_inl, Sum.elim_inr,
        SubInstrument.pure_bind]
      exact hL (.inr x) t'
    · simp
  have hle₁ : ∀ (n : ℕ) (ev : E ⊕ (X ⊕ Y)) (t : τ),
      S.fbRunFail n ev t ≤ Bext ((Equiv.sumAssoc E X Y).symm ev) t := by
    intro n
    induction n with
    | zero =>
      intro ev t
      rw [hB, fbRunFail]
      refine SubInstrument.bind_mono_right _ fun q => ?_
      rcases q with ⟨t', o | w⟩
      · exact le_rfl
      · exact SubInstrument.fail_le _
    | succ n ih =>
      intro ev t
      rw [hB, fbRunFail]
      refine SubInstrument.bind_mono_right _ fun q => ?_
      rcases q with ⟨t', o | w⟩
      · exact le_rfl
      · exact ih (.inr w) t'
  let K : τ × (O ⊕ X) → SubInstrument R R (τ × O) := fun q =>
    Sum.elim (fun o => SubInstrument.pure (q.1, o)) (fun x => S.fbRunω (.inr (.inl x)) q.1) q.2
  have hQ : ∀ (k : ℕ) (ev : (E ⊕ X) ⊕ Y) (t : τ),
      (G.fbRunFail k ev t).bind K ≤ S.fbRunω (Equiv.sumAssoc E X Y ev) t := by
    intro k
    induction k with
    | zero =>
      intro ev t
      rw [fbRunω_eq S]
      simp only [fbRunFail, hG, SubInstrument.bind_assoc, SubInstrument.pure_bind]
      refine SubInstrument.bind_mono_right _ fun q => ?_
      rcases q with ⟨t', o | x | y⟩
      · simp [K]
      · simp [K]
      · simpa using SubInstrument.fail_le _
    | succ k ih =>
      intro ev t
      rw [fbRunω_eq S]
      simp only [fbRunFail, hG, SubInstrument.bind_assoc, SubInstrument.pure_bind]
      refine SubInstrument.bind_mono_right _ fun q => ?_
      rcases q with ⟨t', o | x | y⟩
      · simp [K]
      · simp [K]
      · simpa using ih (.inr y) t'
  have hQω : ∀ (ev : (E ⊕ X) ⊕ Y) (t : τ),
      (G.fbRunω ev t).bind K ≤ S.fbRunω (Equiv.sumAssoc E X Y ev) t := by
    intro ev t
    change (ωSup (G.fbChain ev t)).bind K ≤ _
    rw [SubInstrument.ωSup_bind]
    exact ωSup_le _ _ fun k => hQ k ev t
  have hle₂ : ∀ (m : ℕ) (g : E ⊕ X) (t : τ),
      L.fbRunFail m g t ≤ S.fbRunω (Equiv.sumAssoc E X Y (.inl g)) t := by
    intro m
    induction m with
    | zero =>
      intro g t
      refine le_trans ?_ (hQω (.inl g) t)
      refine SubInstrument.bind_mono_right _ fun q => ?_
      rcases q with ⟨t', o | x⟩
      · exact le_rfl
      · exact SubInstrument.fail_le _
    | succ m ih =>
      intro g t
      refine le_trans ?_ (hQω (.inl g) t)
      refine SubInstrument.bind_mono_right _ fun q => ?_
      rcases q with ⟨t', o | x⟩
      · exact le_rfl
      · exact ih (.inr x) t'
  apply le_antisymm
  · exact ωSup_le _ _ fun m => hle₂ m (.inl e) t
  · refine ωSup_le _ _ fun n => (hle₁ n (.inl e) t).trans ?_
    rw [hL]
    rfl

/-- **Vanishing for a sum of wires**, as a step map: the identity of the states is a step map
from the loopback along `X` of the loopback along `Y` of `S` (on reassociated ports) to the
loopback of `S` along `X ⊕ Y`. -/
theorem loopbackω_loopbackω :
    StepMap (S.mapPorts (Equiv.sumAssoc E X Y) (Equiv.sumAssoc O X Y).symm).loopbackω.loopbackω
      S.loopbackω id :=
  ⟨rfl, fun t e => by
    rw [loopbackω_step, loopbackω_step, fbRunω_loopbackω_sumAssoc]
    simp⟩

end Vanishing

/-! ## Superposing -/

section Superposing

variable (S : QRSys R τ (E ⊕ X) (O ⊕ X))

/-- The system `S` beside the forwarding of `W` on the left, with its wire reassociated to the
outside. -/
noncomputable abbrev parLeftWire (W : Type) : QRSys R (Unit × τ) ((W ⊕ E) ⊕ X) ((W ⊕ O) ⊕ X) :=
  ((ofFun (id : W → W)).par S).mapPorts (Equiv.sumAssoc W E X) (Equiv.sumAssoc W O X).symm

/-- The activations of `S` beside the forwarding of `W` are those of `S`, at every fuel. -/
theorem fbRunFail_parLeftWire :
    ∀ (n : ℕ) (ev : E ⊕ X) (u : Unit) (t : τ),
      (S.parLeftWire W).fbRunFail n (Sum.map Sum.inr id ev) (u, t) =
        (S.fbRunFail n ev t).bind fun p => SubInstrument.pure ((u, p.1), Sum.inr p.2) := by
  have hstep : ∀ (ev : E ⊕ X) (u : Unit) (t : τ),
      (S.parLeftWire W).step (u, t) (Sum.map Sum.inr id ev) =
        (S.step t ev).bind fun q =>
          SubInstrument.pure ((u, q.1), Sum.map Sum.inr id q.2) := by
    intro ev u t
    have hev : Equiv.sumAssoc W E X (Sum.map Sum.inr id ev) = Sum.inr ev := by
      rcases ev with e | x <;> rfl
    simp only [parLeftWire, mapPorts_step, hev, par_step_inr, SubInstrument.bind_assoc,
      SubInstrument.pure_bind]
    congr 1
  intro n
  induction n with
  | zero =>
    intro ev u t
    simp only [fbRunFail, hstep, SubInstrument.bind_assoc, SubInstrument.pure_bind]
    congr 1; funext q; rcases q with ⟨t', o | x⟩ <;> simp
  | succ n ih =>
    intro ev u t
    simp only [fbRunFail, hstep, SubInstrument.bind_assoc, SubInstrument.pure_bind]
    congr 1; funext q; rcases q with ⟨t', o | x⟩
    · simp
    · simpa using ih (.inr x) u t'

/-- **Superposing on the left.** The forwarding of `W` beside the unbounded loopback of `S` is
the unbounded loopback of `S` beside the forwarding of `W`. -/
theorem loopbackω_par_left :
    StepMap ((ofFun (id : W → W)).par S.loopbackω) (S.parLeftWire W).loopbackω id := by
  refine ⟨rfl, fun s e => ?_⟩
  obtain ⟨u, t⟩ := s
  rcases e with w | e
  · rw [par_step_inl, loopbackω_step, fbRunω_eq]
    simp [parLeftWire, mapPorts_step]
  · have h := fbRunω_eq_bind_of_fbRunFail _ fun n =>
      fbRunFail_parLeftWire (W := W) S n (.inl e) u t
    simp only [Sum.map_inl] at h
    rw [par_step_inr, loopbackω_step, loopbackω_step, id, h]
    simp

end Superposing

/-- The unbounded loopback of a bundled system. -/
noncomputable def Obj.loopbackω {E O X : Type} (A : Obj R (E ⊕ X) (O ⊕ X)) : Obj R E O :=
  ⟨A.St, A.sys.loopbackω⟩

/-- Step equivalence is a congruence for the unbounded loopback. -/
theorem StepEq.loopbackω {E O X : Type} {A A' : Obj R (E ⊕ X) (O ⊕ X)}
    (h : StepEq A A') : StepEq A.loopbackω A'.loopbackω :=
  StepEq.map (fun A => A.loopbackω) (fun _ _ ⟨_, h⟩ => ⟨_, loopbackω_stepMap h⟩) h

end QRSys

namespace QSysCat

open CategoryTheory MonoidalCategory

variable {R : Type} [Fintype R]

/-- The trace of `f : X ⊗ U ⟶ Y ⊗ U`: the class of the unbounded loopback along `U`. -/
noncomputable def trace (U : QSysCat R) {X Y : QSysCat R} (f : X ⊗ U ⟶ Y ⊗ U) : X ⟶ Y :=
  Quotient.map (QRSys.Obj.loopbackω (E := X.P) (O := Y.P) (X := U.P))
    (fun _ _ h => QRSys.StepEq.loopbackω h) f

/-- `QSysCat R` is a traced symmetric monoidal category; the trace is the unbounded loopback,
the least fixed point of the feedback in Selinger's order. -/
noncomputable instance tracedCategory : TracedCategory (QSysCat R) where
  trace := trace
  trace_whiskerRight_comp U _ _ _ g f := by
    induction g using Quotient.inductionOn
    induction f using Quotient.inductionOn
    exact Quotient.sound (QRSys.loopbackω_seq_left _ _).stepEq
  trace_comp_whiskerRight U _ _ _ f h := by
    induction f using Quotient.inductionOn
    induction h using Quotient.inductionOn
    exact Quotient.sound (QRSys.loopbackω_seq_right _ _).stepEq
  trace_whiskerLeft_comp g f := by
    induction g using Quotient.inductionOn
    induction f using Quotient.inductionOn
    exact Quotient.sound (Relation.EqvGen.symm _ _ (QRSys.loopbackω_slide _ _).stepEq)
  trace_tensorUnit f := by
    induction f using Quotient.inductionOn
    exact Quotient.sound (QRSys.loopbackω_empty _).stepEq
  trace_tensor U V _ _ f := by
    induction f using Quotient.inductionOn with
    | h A =>
      refine Quotient.sound (Relation.EqvGen.trans _ _ _
        (Relation.EqvGen.symm _ _ (QRSys.loopbackω_loopbackω A.sys).stepEq)
        (Relation.EqvGen.symm _ _ (QRSys.StepEq.loopbackω (QRSys.StepEq.loopbackω
          (QRSys.StepMap.ofFun_seq_seq_ofFun _ A.sys _).stepEq))))
  whiskerLeft_trace W U _ _ f := by
    induction f using Quotient.inductionOn with
    | h A =>
      refine Quotient.sound (Relation.EqvGen.trans _ _ _
        (QRSys.loopbackω_par_left (W := W.P) A.sys).stepEq
        (Relation.EqvGen.symm _ _ (QRSys.StepEq.loopbackω
          (QRSys.StepMap.ofFun_seq_seq_ofFun _ ((QRSys.ofFun id).par A.sys) _).stepEq)))
  trace_braiding U := Quotient.sound (QRSys.loopbackω_swap (X := U.P)).stepEq

end QSysCat

end CatCrypt.Quantum.ReactiveUC

/-! ## Views under step maps -/

namespace CatCrypt.Crypto.Party.QProg

open _root_.Quantum CatCrypt.Quantum.ReactiveUC

variable {H : Type} [Fintype H] {τ υ ζ E O : Type} {d : ℕ}

/-- A state map that commutes with the steps of two systems commutes with their joint runs
against an environment. -/
theorem qloop_stepMap {S₁ : QSys H τ E O d} {S₂ : QSys H υ E O d} {f : τ → υ}
    (hf : ∀ t e, (S₁.step t e).bind (fun p => SubInstrument.pure (f p.1, p.2)) = S₂.step (f t) e)
    (Z : QStrat ζ E O d) (n : ℕ) (z : ζ) (t : τ) :
    (qloop S₁ Z n (z, t)).bind (fun c => SubInstrument.pure (c.1, f c.2)) =
      qloop S₂ Z n (z, f t) := by
  induction n generalizing z t with
  | zero => exact SubInstrument.pure_bind _ _
  | succ n ih =>
    simp only [qloop, ← hf, SubInstrument.bind_assoc, SubInstrument.pure_bind, ih]

/-- **Views are invariant under step maps.** A step map between two systems with the same
initial private basis state keeps the view of every environment. -/
theorem qview_eq_of_stepMap [DecidableEq H] {S₁ : QSys H τ E O d} {S₂ : QSys H υ E O d}
    {f : τ → υ} (hr : S₁.initReg = S₂.initReg) (hf : QRSys.StepMap S₁.toQRSys S₂.toQRSys f)
    (Z : QStrat ζ E O d) : qview S₁ Z = qview S₂ Z := by
  have hi : S₂.init = f S₁.init := hf.init_map.symm
  simp only [qview, hr, hi, ← qloop_stepMap hf.step, SubInstrument.bind_assoc,
    SubInstrument.pure_bind]

end CatCrypt.Crypto.Party.QProg
