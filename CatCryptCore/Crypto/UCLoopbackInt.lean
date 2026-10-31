/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCLoopbackTraced
public import CatCryptCore.ForMathlib.CategoryTheory.Monoidal.IntConstructionMonoidal
public import CatCryptCore.Crypto.UCParallel

/-!
# The Int construction on systems and composition with a subroutine

`IntConstruction SysCat` is the Int construction on the traced symmetric monoidal category
`SysCat` of port types and systems modulo step equivalence; it is compact closed
(`IntConstruction.instRigidCategory`). The object `SysCat.iface E O` is the interface `(E, O)`:
`E` the events a system receives, `O` the outputs it returns.

* A system on `(E, O)` is a morphism `SysCat.iface E O ⟶ 𝟙_`, the class of the system on
  `E ⊕ Empty` and `Empty ⊕ O` (`SysCat.sysHom`).
* A multi-call hybrid `π` with outer interface `(E, O)` and subroutine interface `(EG, OG)` is
  the system `π.toSys` on `E ⊕ OG` and `EG ⊕ O`: it receives outer events and subroutine
  answers and emits subroutine calls and outer outputs, counting the calls of the current
  activation in its state. Its class is a morphism `SysCat.iface E O ⟶ SysCat.iface EG OG`
  (`SysCat.openHom`).

Composition in the Int construction is the trace over the shared negative component. The
composite of `SysCat.openHom π` with the system `S` is the unbounded loopback of the system
`π.loopSys S`, which runs one step of `π.toSys` followed by the call of `S` it makes. Every
activation of that loopback exits within `π.fuel + 1` further calls, so the bridge
`Sys.loopback_stepEq_loopbackω` identifies it with the bounded loopback, and the bounded loopback
is step-equivalent to `π.withSub S` (`SysCat.openHom_comp_sysHom`).

## Main definitions

* `MultiHybrid.toSys`: a multi-call hybrid as a system with a call counter.
* `MultiHybrid.loopSys`: one step of `π.toSys` followed by the call of `S`.
* `SysCat.iface`, `SysCat.sysHom`, `SysCat.openHom`: interfaces, systems and multi-call hybrids
  in `IntConstruction SysCat`.

## Main results

* `MultiHybrid.exitsWithin_loopSys`: the loopback of `π.loopSys S` exits within `π.fuel + 1`.
* `MultiHybrid.loopback_loopSys_stepMap`: the bounded loopback of `π.loopSys S` is `π.withSub S`
  up to a step map.
* `SysCat.openHom_comp_sysHom`: the Int composite of `SysCat.openHom π` with the system `S` is
  `π.withSub S`.
* `SysCat.openHom_comp_sysHom_ofMultiHybrid`: the same for the open system
  `Open.ofMultiHybrid π idle`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open CategoryTheory MonoidalCategory BraidedCategory

namespace MultiHybrid

variable {σ τ E O EG OG : Type}

/-- One step of `π.toSys` from the hybrid state `s` with `c` calls left: an outer event starts
an activation with `π.fuel` calls left after the first; a subroutine answer with no call left
finishes it, and otherwise resumes it with one call less. -/
noncomputable def toSysStep (π : MultiHybrid σ E O EG OG) :
    σ × ℕ → E ⊕ OG → SPComp ((σ × ℕ) × (EG ⊕ O))
  | (s, _), .inl e => SPComp.map (fun r => ((r.1, π.fuel), r.2)) (π.start s e)
  | (s, 0), .inr o => SPComp.map (fun r => ((r.1, π.fuel), .inr r.2)) (π.finish s o)
  | (s, k + 1), .inr o => SPComp.map (fun r => ((r.1, k), r.2)) (π.resume s o)

/-- The multi-call hybrid `π` as a system on `E ⊕ OG` and `EG ⊕ O`: it receives outer events and
subroutine answers and emits subroutine calls and outer outputs; the state holds the hybrid state
and the number of calls left in the current activation. -/
noncomputable def toSys (π : MultiHybrid σ E O EG OG) : Sys (σ × ℕ) (E ⊕ OG) (EG ⊕ O) where
  init := (π.init, π.fuel)
  step := π.toSysStep

/-- The rest of a step of `π.loopSys S` after the decision `d` of the hybrid, in hybrid state `s`
with `c` calls left and subroutine state `t`: a call is answered by `S` on the wire, and an outer
output is returned. -/
noncomputable def loopAfter (S : Sys τ EG OG) (s : σ) (c : ℕ) (t : τ) :
    EG ⊕ O → SPComp (((σ × ℕ) × τ) × ((Empty ⊕ O) ⊕ OG))
  | .inl g => SPComp.map (fun q => (((s, c), q.1), .inr q.2)) (S.step t g)
  | .inr o => SPComp.pure (((s, c), t), .inl (.inr o))

/-- One step of `π.loopSys S`. -/
noncomputable def loopStep (π : MultiHybrid σ E O EG OG) (S : Sys τ EG OG) :
    (σ × ℕ) × τ → (E ⊕ Empty) ⊕ OG → SPComp (((σ × ℕ) × τ) × ((Empty ⊕ O) ⊕ OG))
  | ((s, _), t), .inl (.inl e) =>
    SPComp.bind (π.start s e) fun r => loopAfter S r.1 π.fuel t r.2
  | _, .inl (.inr x) => x.elim
  | ((s, 0), t), .inr o =>
    SPComp.map (fun r => (((r.1, π.fuel), t), .inl (.inr r.2))) (π.finish s o)
  | ((s, k + 1), t), .inr o =>
    SPComp.bind (π.resume s o) fun r => loopAfter S r.1 k t r.2

/-- The system traced in the Int composite of `π.toSys` with `S`: one step of `π.toSys` followed
by the call of `S` it makes, whose answer is fed back on the wire `OG`. -/
noncomputable def loopSys (π : MultiHybrid σ E O EG OG) (S : Sys τ EG OG) :
    Sys ((σ × ℕ) × τ) ((E ⊕ Empty) ⊕ OG) ((Empty ⊕ O) ⊕ OG) where
  init := ((π.init, π.fuel), S.init)
  step := π.loopStep S

/-- Unfolding lemma of `loopSys`: a step is `loopStep`. -/
theorem loopSys_step (π : MultiHybrid σ E O EG OG) (S : Sys τ EG OG) :
    (π.loopSys S).step = π.loopStep S :=
  rfl

/-- The rest of an activation of `π.withSub S` after the subroutine answer `o`, in hybrid state
`s` with `c` calls left and subroutine state `t`. -/
noncomputable def answer (π : MultiHybrid σ E O EG OG) (S : Sys τ EG OG) :
    ℕ → σ → OG → τ → SPComp (σ × τ × O)
  | 0, s, o, t => SPComp.map (fun r => (r.1, t, r.2)) (π.finish s o)
  | k + 1, s, o, t => SPComp.bind (π.resume s o) fun r => π.drive S k r.1 r.2 t

/-- The drive from a call is the call followed by `answer`. -/
theorem drive_inl (π : MultiHybrid σ E O EG OG) (S : Sys τ EG OG) (k : ℕ) (s : σ) (g : EG)
    (t : τ) :
    π.drive S k s (.inl g) t = SPComp.bind (S.step t g) fun q => π.answer S k s q.2 q.1 := by
  cases k <;> rfl

/-- The activation of the loopback of `π.loopSys S` from a subroutine answer, with at least as
much fuel as calls left, is `answer`. -/
theorem fbRun_loopSys (π : MultiHybrid σ E O EG OG) (S : Sys τ EG OG) (cut : OG → Empty ⊕ O) :
    ∀ (c m : ℕ), c ≤ m → ∀ (s : σ) (o : OG) (t : τ),
      SPComp.map (fun p => ((p.1.1.1, p.1.2), p.2))
          (Sys.fbRun (π.loopSys S) cut m (.inr o) ((s, c), t)) =
        SPComp.map (fun x => ((x.1, x.2.1), (Sum.inr x.2.2 : Empty ⊕ O))) (π.answer S c s o t) := by
  intro c
  induction c with
  | zero =>
    intro m _ s o t
    cases m <;> simp [Sys.fbRun, loopSys, loopStep, answer, SPComp.map, SPComp.bind_assoc]
  | succ k ih =>
    intro m hm s o t
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    simp only [Sys.fbRun, loopSys_step, loopStep, answer, SPComp.map, SPComp.bind_assoc]
    congr 1
    funext r
    rcases r with ⟨s', g | o'⟩
    · have h := fun q : τ × OG => ih m (by omega) s' q.2 q.1
      simp only [SPComp.map] at h
      simp only [loopAfter, drive_inl, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind,
        Sum.elim_inr]
      congr 1
      funext q
      exact h q
    · simp [loopAfter, drive]

/-- From a subroutine answer with `c ≤ m` calls left, the loopback of `π.loopSys S` exits
within `m` further calls. -/
theorem exitsBy_loopSys (π : MultiHybrid σ E O EG OG) (S : Sys τ EG OG) :
    ∀ (c m : ℕ), c ≤ m → ∀ (s : σ) (o : OG) (t : τ),
      (π.loopSys S).ExitsBy (fun _ => True) m (.inr o) ((s, c), t) := by
  intro c
  induction c with
  | zero =>
    intro m _ s o t
    cases m <;>
    · intro q hq
      simp only [loopSys_step, loopStep] at hq
      obtain ⟨r, -, rfl⟩ := exists_of_isOutcome_map hq
      trivial
  | succ k ih =>
    intro m hm s o t
    obtain ⟨m, rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    intro q hq
    simp only [loopSys_step, loopStep] at hq
    obtain ⟨r, -, hr⟩ := isOutcome_bind hq
    rcases r with ⟨s', g | o'⟩
    · obtain ⟨q', -, rfl⟩ := exists_of_isOutcome_map hr
      exact ih m (by omega) s' q'.2 q'.1
    · obtain rfl := isOutcome_pure hr
      trivial

/-- **Adequate fuel.** Every activation of the loopback of `π.loopSys S` exits within
`π.fuel + 1` further calls. -/
theorem exitsWithin_loopSys (π : MultiHybrid σ E O EG OG) (S : Sys τ EG OG) :
    (π.loopSys S).ExitsWithin (fun _ => True) (π.fuel + 1) := by
  rintro ⟨⟨s, c⟩, t⟩ - (e | x)
  · intro q hq
    simp only [loopSys_step, loopStep] at hq
    obtain ⟨r, -, hr⟩ := isOutcome_bind hq
    rcases r with ⟨s', g | o'⟩
    · obtain ⟨q', -, rfl⟩ := exists_of_isOutcome_map hr
      exact exitsBy_loopSys π S _ _ le_rfl s' q'.2 q'.1
    · obtain rfl := isOutcome_pure hr
      trivial
  · exact x.elim

/-- The loopback of `π.loopSys S` with fuel `π.fuel + 1` is `π.withSub S` on the relabelled
ports, up to the step map forgetting the call counter. -/
theorem loopback_loopSys_stepMap (π : MultiHybrid σ E O EG OG) (S : Sys τ EG OG)
    (cut : OG → Empty ⊕ O) :
    Sys.StepMapOn ((π.loopSys S).loopback (π.fuel + 1) cut)
      ((π.withSub S).mapPorts (Sum.elim id Empty.elim) Sum.inr) (fun _ => True)
      (fun u => (u.2.1.1, u.2.2)) :=
  Sys.StepMapOn.of_step _ rfl fun u e => by
    obtain ⟨⟨⟩, ⟨s, c⟩, t⟩ := u
    rcases e with e | x
    · rw [Sys.loopback_step, Sys.mapPorts_step]
      simp only [Sys.fbRun, loopSys_step, loopStep, withSub, SPComp.map, SPComp.bind_assoc,
        SPComp.pure_bind]
      congr 1
      funext r
      rcases r with ⟨s', g | o⟩
      · have h := fun q : τ × OG => fbRun_loopSys π S cut π.fuel π.fuel le_rfl s' q.2 q.1
        simp only [SPComp.map] at h
        simp only [loopAfter, drive_inl, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind,
          Sum.elim_inr]
        congr 1
        funext q
        exact h q
      · simp [loopAfter, drive]
    · exact x.elim

end MultiHybrid

namespace SysCat

variable {σ τ E O EG OG : Type}

/-- The map of ports of `swapRight`, exchanging the last two summands. -/
def swapFun {A B C : Type} : (A ⊕ B) ⊕ C → (A ⊕ C) ⊕ B
  | .inl (.inl a) => .inl (.inl a)
  | .inl (.inr b) => .inr b
  | .inr c => .inl (.inr c)

/-- `swapRight X U V` is the morphism of the map of ports `swapFun`. -/
theorem swapRight_eq_homOfFun (X U V : SysCat) :
    swapRight X U V = homOfFun (X := (X ⊗ U) ⊗ V) (Y := (X ⊗ V) ⊗ U) swapFun := by
  change homOfFun _ ≫ X ◁ homOfFun _ ≫ homOfFun _ = _
  simp only [whiskerLeft_homOfFun, homOfFun_comp]
  congr 1
  funext p
  rcases p with (x | u) | v <;> rfl

/-- The interface `(E, O)` as an object of the Int construction on `SysCat`. -/
abbrev iface (E O : Type) : IntConstruction SysCat :=
  ⟨⟨E⟩, ⟨O⟩⟩

/-- A system on `(E, O)` as a morphism `(E, O) ⟶ 𝟙` of the Int construction: the class of the
system on `E ⊕ Empty` and `Empty ⊕ O`. -/
noncomputable def sysHom (A : SysObj E O) : iface E O ⟶ 𝟙_ (IntConstruction SysCat) :=
  ⟨(⟦A.mapPorts (Sum.elim id Empty.elim) Sum.inr⟧ : (⟨E ⊕ Empty⟩ : SysCat) ⟶ ⟨Empty ⊕ O⟩)⟩

/-- A multi-call hybrid with outer interface `(E, O)` and subroutine interface `(EG, OG)` as a
morphism `(E, O) ⟶ (EG, OG)` of the Int construction: the class of `π.toSys`. -/
noncomputable def openHom (π : MultiHybrid σ E O EG OG) : iface E O ⟶ iface EG OG :=
  ⟨(⟦⟨σ × ℕ, π.toSys⟩⟧ : (⟨E ⊕ OG⟩ : SysCat) ⟶ ⟨EG ⊕ O⟩)⟩

/-- The morphism traced in the Int composite of `openHom π` with `sysHom S` is the class of
`π.loopSys S`. -/
theorem compKernel_openHom_sysHom (π : MultiHybrid σ E O EG OG) (S : Sys τ EG OG) :
    IntConstruction.compKernel (openHom π) (sysHom ⟨τ, S⟩) =
      (⟦⟨(σ × ℕ) × τ, π.loopSys S⟩⟧ : (⟨(E ⊕ Empty) ⊕ OG⟩ : SysCat) ⟶ ⟨(Empty ⊕ O) ⊕ OG⟩) := by
  simp only [IntConstruction.compKernel, swapRight_eq_homOfFun]
  refine Quotient.sound (Sys.StepMapOn.of_step (fun s => (s.2.1.1, s.2.2.2.1.1)) rfl
    fun u e => ?_).stepEq
  obtain ⟨⟨⟩, ⟨⟨s, c⟩, ⟨⟩⟩, ⟨⟩, ⟨t, ⟨⟩⟩, ⟨⟩⟩ := u
  change τ at t
  rcases e with (e | x) | o
  · simp only [Sys.seq_step, Sys.ofFun_step, MultiHybrid.toSys, MultiHybrid.toSysStep,
      MultiHybrid.loopSys, MultiHybrid.loopStep, SysObj.seq, SysObj.par, SysObj.mapPorts,
      SysObj.idSys, swapFun, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind, Sys.par_step_inl,
      IntConstruction.tensorUnit_pos, IntConstruction.tensorUnit_neg]
    congr 1
    funext r
    rcases r with ⟨s', g | o⟩ <;>
      simp [MultiHybrid.loopAfter, Sys.ofFun_step, Sys.mapPorts_step, SPComp.map,
        SPComp.bind_assoc]
  · exact x.elim
  · rcases c with _ | k
    · simp [Sys.seq_step, Sys.ofFun_step, MultiHybrid.toSys, MultiHybrid.toSysStep,
        MultiHybrid.loopSys, MultiHybrid.loopStep, SysObj.seq, SysObj.par, SysObj.mapPorts,
        SysObj.idSys, swapFun, SPComp.map, SPComp.bind_assoc]
    · simp only [Sys.seq_step, Sys.ofFun_step, MultiHybrid.toSys, MultiHybrid.toSysStep,
        MultiHybrid.loopSys, MultiHybrid.loopStep, SysObj.seq, SysObj.par, SysObj.mapPorts,
        SysObj.idSys, swapFun, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind,
        Sys.par_step_inl, IntConstruction.tensorUnit_pos,
        IntConstruction.tensorUnit_neg]
      congr 1
      funext r
      rcases r with ⟨s', g | o⟩ <;>
        simp [MultiHybrid.loopAfter, Sys.ofFun_step, Sys.mapPorts_step, SPComp.map,
          SPComp.bind_assoc]

/-- **Composition with a subroutine.** The Int composite of the multi-call hybrid `π` with the
system `S` is the system `π.withSub S`, up to step equivalence. -/
theorem openHom_comp_sysHom [Nonempty O] (π : MultiHybrid σ E O EG OG) (S : Sys τ EG OG) :
    openHom π ≫ sysHom ⟨τ, S⟩ = sysHom ⟨σ × τ, π.withSub S⟩ := by
  obtain ⟨o₀⟩ := ‹Nonempty O›
  apply IntConstruction.hom_ext
  rw [IntConstruction.comp_hom, compKernel_openHom_sysHom]
  exact Quotient.sound (Relation.EqvGen.trans _ _ _
    (Relation.EqvGen.symm _ _ (Sys.loopback_stepEq_loopbackω (π.loopSys S) (fun _ => True)
      le_rfl (fun _ => .inr o₀) trivial (π.exitsWithin_loopSys S)))
    (π.loopback_loopSys_stepMap S _).stepEq)

/-- **Composition with a subroutine**, for the open system of a multi-call hybrid: the Int
composite of `openHom π` with `S` is the system `(Open.ofMultiHybrid π idle).withSub S`. -/
theorem openHom_comp_sysHom_ofMultiHybrid [Nonempty O] (π : MultiHybrid σ E O EG OG)
    (idle : EG) (S : Sys τ EG OG) :
    openHom π ≫ sysHom ⟨τ, S⟩ = sysHom ⟨_, (Open.ofMultiHybrid π idle).withSub S⟩ :=
  openHom_comp_sysHom π S

end SysCat

end CatCrypt.Crypto.UCTransparent
