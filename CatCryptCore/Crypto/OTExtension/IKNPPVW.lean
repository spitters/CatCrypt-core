/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OTExtension.IKNPWakeShape
public import CatCryptCore.Crypto.OT.PVWPull
public import CatCryptCore.Crypto.UCIndexed
public import CatCryptCore.Crypto.UCChannelLift
public import CatCryptCore.Crypto.UCWake

/-!
# IKNP over PVW base OTs

**Ideal functionality.** `FOTSched otChoose` (both parties honest) and
`FOTSchedSH otChoose leak` (a semi-honest corrupt party): the scheduled transfer of `m` message
pairs of `OT/FOTSched.lean`.

**Real protocol.** The IKNP parties of `OTExtension/IKNPWake.lean`, with their randomness drawn
in their own state (`IKNPWake.partyLazy`), over `κ` copies of the pull-form PVW oblivious transfer
of one column pair (`pvwBase`) beside the secure channel for the masked messages, closed by the
wake closure in which the delivery of the PVW channel `i` wakes the sender for the base OT `i` and
the delivery of the IKNP channel wakes the receiver (`iknpPVW`). A column of `m` bits is sent
through PVW as a group element (`bitsCode`, `bitsDecode`).

**Simulator.** The wake closure of the composite simulator of modular composition: the forwarding
of the parties' port beside the indexed copies `simKeep` of the PVW simulator `simP` (one per base
OT) and the forwarding of the channel's adversary port, over the IKNP simulator `simW` with its
corruption port moved by a relabelling.

**Bound.** The bound of the IKNP realization over the ideal base OTs at the environment reduced
through the wake closure, the relabellings and the extended simulator: `0` with both parties
honest and against a corrupt sender, and `CRHash_Advantage H (iknpWakeCRRed H Z')` against a
corrupt receiver. The `κ` PVW realizations contribute bound `0`.

**Proof.** One PVW instance on tuples of one realizes `FOTSched baseOut` after relabelling its
honest port (`RealizesSim.mapHon`, `FOTSched.one_stepMap`). The `κ` copies realize `κ` copies of
`FOTSched baseOut` with the honest and adversary ports split by copy (`RealizesSim.indexedSplit`),
which is `FOTSchedPar` (`pvwBase_realizesSim`). Modular composition with the channel
(`RealizesSim.modular_withChan`) substitutes the PVW copies for the ideal base OTs in the IKNP
realization, and `RealizesSim.wakeClose` closes the wakes.

## Main definitions

* `splitIdx`: the indexed events of a sum interface, split by port.
* `MultiHybrid.indexedKeep`: indexed copies of a simulator that keep the active copy on an
  activation answered without a call.
* `pvwBase`: `κ` copies of the pull-form PVW OT of one column pair.
* `iknpPVW`: IKNP over the PVW base OTs, closed by the wakes.

## Main results

* `RealizesSim.mapHon`: realization behind `idSim ⊗ S` with the honest port relabelled.
* `RealizesSim.indexedSplit`: realization of indexed copies behind `idSim ⊗ S.indexedKeep`, on
  the interface split by port.
* `pvwBase_realizesSim`: the PVW copies realize the `κ` scheduled base OTs at distance `0`.
* `iknpPVW_realizesSim`: the composition theorem for a realization of IKNP behind `simW`.
* `iknpPVW_H_realizesSim`, `iknpPVW_S_realizesSim`, `iknpPVW_R_realizesSim`: the three cases.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete CatCrypt.Relational
open scoped ENNReal

/-! ## Losslessness of a simulator over a lossless subroutine -/

namespace MultiHybrid

variable {ι σ τ E O EG OG : Type}

/-- The rest of an activation of a multi-call hybrid over a lossless subroutine never fails. -/
theorem drive_noFail (π : MultiHybrid σ E O EG OG) (X : Sys τ EG OG)
    (hX : ∀ t g, SPComp.NoFail (X.step t g)) :
    ∀ n s d t, SPComp.NoFail (π.drive X n s d t) := by
  intro n
  induction n with
  | zero =>
    rintro s (g | o) t
    · exact Assumptions.SPComp.bind_noFail (hX _ _) fun _ =>
        Assumptions.SPComp.bind_noFail (π.finish_noFail _ _) fun _ => SPComp.pure_noFail _
    · exact SPComp.pure_noFail _
  | succ n ih =>
    rintro s (g | o) t
    · exact Assumptions.SPComp.bind_noFail (hX _ _) fun _ =>
        Assumptions.SPComp.bind_noFail (π.resume_noFail _ _) fun _ => ih _ _ _
    · exact SPComp.pure_noFail _

/-- Single steps of a multi-call hybrid over a lossless subroutine never fail. -/
theorem withSub_noFail (π : MultiHybrid σ E O EG OG) (X : Sys τ EG OG)
    (hX : ∀ t g, SPComp.NoFail (X.step t g)) :
    ∀ t e, SPComp.NoFail ((π.withSub X).step t e) := by
  intro t e
  simp only [MultiHybrid.withSub]
  exact Assumptions.SPComp.bind_noFail (π.start_noFail _ _) fun _ =>
    Assumptions.SPComp.bind_noFail (drive_noFail π X hX _ _ _ _) fun _ => SPComp.pure_noFail _

/-! ## Indexed copies keeping the active copy -/

variable [DecidableEq ι] [Inhabited ι]

/-- **Indexed copies keeping the active copy.** The indexed copies of `π` of
`MultiHybrid.indexed`, except that a start of the copy `i` that answers without a call leaves the
recorded active copy unchanged; a start that calls records `i`. -/
noncomputable def indexedKeep (π : MultiHybrid σ E O EG OG) :
    MultiHybrid ((ι → σ) × ι) (ι × E) O (ι × EG) OG where
  init := (fun _ => π.init, default)
  fuel := π.fuel
  start s e := SPComp.map
    (fun r => ((Function.update s.1 e.1 r.1, Sum.elim (fun _ => e.1) (fun _ => s.2) r.2),
      Sum.map (Prod.mk e.1) id r.2))
    (π.start (s.1 e.1) e.2)
  resume s o := SPComp.map
    (fun r => ((Function.update s.1 s.2 r.1, s.2), Sum.map (Prod.mk s.2) id r.2))
    (π.resume (s.1 s.2) o)
  finish s o := SPComp.map (fun r => ((Function.update s.1 s.2 r.1, s.2), r.2))
    (π.finish (s.1 s.2) o)
  start_noFail _ _ :=
    Assumptions.SPComp.bind_noFail (π.start_noFail _ _) fun _ => SPComp.pure_noFail _
  resume_noFail _ _ :=
    Assumptions.SPComp.bind_noFail (π.resume_noFail _ _) fun _ => SPComp.pure_noFail _
  finish_noFail _ _ :=
    Assumptions.SPComp.bind_noFail (π.finish_noFail _ _) fun _ => SPComp.pure_noFail _

/-- Unfolding lemma of `indexedKeep`: the start of the copy `e.1`. -/
theorem indexedKeep_start (π : MultiHybrid σ E O EG OG) (s : (ι → σ) × ι) (e : ι × E) :
    (π.indexedKeep (ι := ι)).start s e = SPComp.map
      (fun r => ((Function.update s.1 e.1 r.1, Sum.elim (fun _ => e.1) (fun _ => s.2) r.2),
        Sum.map (Prod.mk e.1) id r.2))
      (π.start (s.1 e.1) e.2) := rfl

/-- The rest of an activation of `indexedKeep` is that of `indexed`. -/
theorem indexedKeep_drive (π : MultiHybrid σ E O EG OG) (X : Sys τ (ι × EG) OG) :
    ∀ n s d t, (π.indexedKeep (ι := ι)).drive X n s d t = (π.indexed (ι := ι)).drive X n s d t := by
  intro n
  induction n with
  | zero => rintro s (g | o) t <;> rfl
  | succ n ih =>
    rintro s (g | o) t
    · simp only [drive, ih]
      rfl
    · rfl

variable {V : PubView E O} {W : PubView EG OG} {π : MultiHybrid σ E O EG OG}

/-- The unwinding relation of `indexedKeep`: the same active copy, and the copies pointwise
related. -/
theorem Unwinding.indexedKeep {R : σ → σ → Prop} (hR : Unwinding π V W R) :
    Unwinding (π.indexedKeep (ι := ι)) (V.indexed ι) (W.indexed ι)
      (fun s s' => s.2 = s'.2 ∧ ∀ i, R (s.1 i) (s'.1 i)) where
  init := ⟨rfl, fun _ => hR.init⟩
  start := by
    rintro ⟨ss, a⟩ ⟨ss', a'⟩ ⟨i, e⟩ ⟨i', e'⟩ ⟨ha, hs⟩ ⟨hi, he⟩
    dsimp only at ha hi
    subst ha hi
    rw [indexedKeep_start, indexedKeep_start]
    simp only [SPComp.map]
    refine rHoare_bind (hR.start _ _ _ _ (hs i) he) fun r r' =>
      rHoare_ret fun _ _ hp => ⟨hp.1, ⟨?_, fun k => ?_⟩, ?_⟩
    · rcases r with ⟨_, g | o⟩ <;> rcases r' with ⟨_, g' | o'⟩
      all_goals first | rfl | exact hp.2.2.elim
    · rcases eq_or_ne k i with rfl | hk
      · simpa using hp.2.1
      · simpa [hk] using hs k
    · exact PubView.stepRel_indexed i hp.2.2
  resume := (hR.indexed (ι := ι)).resume
  finish := (hR.indexed (ι := ι)).finish

/-- **Opacity of `indexedKeep`** for the indexed views. -/
theorem Opaque.indexedKeep (h : π.Opaque V W) :
    (π.indexedKeep (ι := ι)).Opaque (V.indexed ι) (W.indexed ι) := by
  obtain ⟨_, hR⟩ := h
  exact ⟨_, hR.indexedKeep⟩

omit [Inhabited ι] in
/-- An activation of `indexedKeep` over indexed copies of `X` on the copy `i`, with the active
copy forgotten, is the activation of the copy `i` over the copy `i` of `X`. -/
theorem indexedKeep_stepFuel [Inhabited ι] (π : MultiHybrid σ E O EG OG) (X : Sys τ EG OG)
    (n : ℕ) (ss : ι → σ) (j i : ι) (ts : ι → τ) (e : E) :
    SPComp.map (fun p => ((p.1.1.1, p.1.2), p.2))
        ((π.indexedKeep (ι := ι)).stepFuel (X.indexed (ι := ι)) n ((ss, j), ts) (i, e)) =
      SPComp.map (fun p => ((Function.update ss i p.1.1, Function.update ts i p.1.2), p.2))
        (π.stepFuel X n (ss i, ts i) e) := by
  simp only [stepFuel, indexedKeep_start, indexedKeep_drive, SPComp.map, SPComp.bind_assoc,
    SPComp.pure_bind]
  congr 1
  funext r
  rcases r with ⟨s', g | o⟩
  · simp only [Sum.elim_inl]
    rw [drive_indexed]
    simp [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  · cases n <;> simp [drive, SPComp.pure_bind]

end MultiHybrid

/-! ## Splitting the indexed interface by port -/

/-- The indexed events of a sum interface, split by port: an indexed honest event or an indexed
adversary event as an event of the copy. -/
def splitIdx {ι EH EA : Type} : (ι × EH) ⊕ (ι × EA) → ι × (EH ⊕ EA)
  | .inl (i, h) => (i, .inl h)
  | .inr (i, a) => (i, .inr a)

namespace Sys

variable {ι τ υ EH EA OH OA EH' OH' : Type}

/-- Indexed copies of a port-typed system, split by port, answer each event on its port. -/
theorem PortTyped.indexedSplit [DecidableEq ι] {I : Sys υ (EH ⊕ EA) (OH ⊕ OA)}
    (hI : I.PortTyped) : ((I.indexed (ι := ι)).mapPorts splitIdx id).PortTyped := by
  obtain ⟨IL, IR, hL, hR⟩ := hI
  refine ⟨IL.indexed, IR.indexed, ?_, ?_⟩
  · rintro t ⟨i, h⟩
    simp [mapPorts, relabel, splitIdx, hL, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  · rintro t ⟨i, a⟩
    simp [mapPorts, relabel, splitIdx, hR, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]

/-- A port-typed system with its honest port relabelled answers each event on its port. -/
theorem PortTyped.mapHon {I : Sys υ (EH ⊕ EA) (OH ⊕ OA)} (hI : I.PortTyped) (a : EH' → EH)
    (c : OH → OH') : (I.mapPorts (Sum.map a id) (Sum.map c id)).PortTyped := by
  obtain ⟨IL, IR, hL, hR⟩ := hI
  refine ⟨IL.mapPorts a c, IR, ?_, ?_⟩
  · intro t h
    simp [mapPorts, relabel, hL, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  · intro t e
    simp [mapPorts, relabel, hR, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]

end Sys

namespace MultiHybrid

variable {ι σ υ EH OH EA OA EA' OA' EH' OH' : Type}

/-- **The forwarding simulator with a relabelled honest port.** For a port-typed `I`, the
forwarding of the honest port beside `S` over `I`, relabelled on the honest port, has the steps
of the forwarding of the relabelled honest port beside `S` over the relabelled `I`. -/
theorem realizes_tensor_mapHon (S : MultiHybrid σ EA OA EA' OA')
    (I : Sys υ (EH ⊕ EA') (OH ⊕ OA')) (hI : I.PortTyped) (a : EH' → EH) (c : OH → OH') :
    Realizes ((((idSim EH OH).tensor S).withSub I).mapPorts (Sum.map a id) (Sum.map c id))
      (((idSim EH' OH').tensor S).withSub (I.mapPorts (Sum.map a id) (Sum.map c id)))
      (fun _ _ => 0) := by
  obtain ⟨IL, IR, hL, hR⟩ := hI
  have hJL : ∀ t g, (I.mapPorts (Sum.map a id) (Sum.map c id)).step t (.inl g) =
      SPComp.map (fun q => (q.1, .inl q.2)) ((IL.mapPorts a c).step t g) := by
    intro t g
    simp [Sys.mapPorts, Sys.relabel, hL, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  have hJR : ∀ t g, (I.mapPorts (Sum.map a id) (Sum.map c id)).step t (.inr g) =
      SPComp.map (fun q => (q.1, .inr q.2)) (IR.step t g) := by
    intro t g
    simp [Sys.mapPorts, Sys.relabel, hR, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  refine realizes_zero_of_stepMap _ _ id rfl ?_
  rintro ⟨⟨⟨⟩, s⟩, u⟩ (h | e)
  · rw [id, tensor_withSub_step_inl _ _ _ _ hJL, idSim_stepFuel]
    simp only [Sys.mapPorts, Sys.relabel, Sum.map_inl, id]
    rw [tensor_withSub_step_inl _ _ I IL hL, idSim_stepFuel]
    simp [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  · rw [id, tensor_withSub_step_inr _ _ _ _ hJR]
    simp only [Sys.mapPorts, Sys.relabel, Sum.map_inr, id]
    rw [tensor_withSub_step_inr _ _ I IR hR]
    simp only [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
    rfl

variable [DecidableEq ι] [Inhabited ι]

/-- **Indexed copies split by port.** For a port-typed `I`, the forwarding of the indexed honest
port beside `S.indexedKeep` over the copies of `I` split by port has, up to the active copy, the
steps of the copies of `idSim ⊗ S` over `I`, split by port. -/
theorem realizes_tensor_indexedSplit (S : MultiHybrid σ EA OA EA' OA')
    (I : Sys υ (EH ⊕ EA') (OH ⊕ OA')) (hI : I.PortTyped) :
    Realizes (((idSim (ι × EH) OH).tensor (S.indexedKeep (ι := ι))).withSub
        ((I.indexed (ι := ι)).mapPorts splitIdx id))
      (((((idSim EH OH).tensor S).withSub I).indexed (ι := ι)).mapPorts splitIdx id)
      (fun _ _ => 0) := by
  obtain ⟨IL, IR, hL, hR⟩ := hI
  have hJL : ∀ t g, ((I.indexed (ι := ι)).mapPorts splitIdx id).step t (.inl g) =
      SPComp.map (fun q => (q.1, .inl q.2)) ((IL.indexed (ι := ι)).step t g) := by
    rintro t ⟨i, h⟩
    simp [Sys.mapPorts, Sys.relabel, splitIdx, hL, SPComp.map, SPComp.bind_assoc,
      SPComp.pure_bind]
  have hJR : ∀ t g, ((I.indexed (ι := ι)).mapPorts splitIdx id).step t (.inr g) =
      SPComp.map (fun q => (q.1, .inr q.2)) ((IR.indexed (ι := ι)).step t g) := by
    rintro t ⟨i, a⟩
    simp [Sys.mapPorts, Sys.relabel, splitIdx, hR, SPComp.map, SPComp.bind_assoc,
      SPComp.pure_bind]
  have hu : ∀ (ss : ι → σ) (us : ι → υ) (i : ι) (x : σ) (y : υ),
      Function.update (fun k => (((), ss k), us k)) i (((), x), y) =
        fun k => (((), Function.update ss i x k), Function.update us i y k) := by
    intro ss us i x y
    funext k
    rcases eq_or_ne k i with rfl | hk <;> simp [*]
  refine realizes_zero_of_stepMap _ _ (fun s i => (((), s.1.2.1 i), s.2 i)) rfl ?_
  rintro ⟨⟨⟨⟩, ss, j⟩, us⟩ (⟨i, h⟩ | ⟨i, e⟩)
  · rw [tensor_withSub_step_inl _ _ _ _ hJL, idSim_stepFuel]
    simp only [Sys.mapPorts, Sys.relabel, splitIdx, Sys.indexed_step]
    rw [tensor_withSub_step_inl _ _ I IL hL, idSim_stepFuel]
    simp only [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind, hu, Function.update_eq_self]
    rfl
  · rw [tensor_withSub_step_inr _ _ _ _ hJR]
    simp only [Sys.mapPorts, Sys.relabel, splitIdx, Sys.indexed_step]
    rw [tensor_withSub_step_inr _ _ I IR hR]
    have hk := congrArg (SPComp.map fun q : ((ι → σ) × (ι → υ)) × OA =>
      (fun k => (((), q.1.1 k), q.1.2 k), (Sum.inr q.2 : OH ⊕ OA)))
      (indexedKeep_stepFuel S IR (max (idSim (ι × EH) OH).fuel (S.indexedKeep (ι := ι)).fuel)
        ss j i us e)
    simp only [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind, hu] at hk ⊢
    exact hk

end MultiHybrid

/-! ## Realizations behind the forwarding of the honest port -/

namespace RealizesSim

open MultiHybrid

variable {τ υ σ EH OH EA OA EA' OA' EH' OH' : Type} {VH : PubView EH OH}
  {VH' : PubView EH' OH'} {VA : PubView EA OA} {WA : PubView EA' OA'}

/-- **Realization with a relabelled honest port.** If `R` realizes the port-typed `I` behind the
forwarding of the honest port beside `S`, then `R` and `I` with their honest ports relabelled by
`a` on events and `c` on outputs realize each other behind the forwarding of the relabelled
honest port beside `S`, with the bound at the environment reduced through the relabelling. -/
theorem mapHon {R : Sys τ (EH ⊕ EA) (OH ⊕ OA)} {I : Sys υ (EH ⊕ EA') (OH ⊕ OA')}
    {S : MultiHybrid σ EA OA EA' OA'} {hS : S.Opaque VA WA}
    {b : (ζ : Type) → Env (Strat ζ (EH ⊕ EA) (OH ⊕ OA)) ζ → ℝ≥0∞} (hI : I.PortTyped)
    (a : EH' → EH) (c : OH → OH') (ha : ∀ e e', VH'.ev e e' → VH.ev (a e) (a e'))
    (hc : ∀ o o', VH.out o o' → VH'.out (c o) (c o'))
    (h : RealizesSim R I (Simulator.tensor (idSim EH OH) S (idSim_opaque VH) hS) b) :
    RealizesSim (R.mapPorts (Sum.map a id) (Sum.map c id))
      (I.mapPorts (Sum.map a id) (Sum.map c id))
      (Simulator.tensor (idSim EH' OH') S (idSim_opaque VH') hS)
      (fun ζ Z => b (ζ × Unit) ((Open.mapPorts (Sum.map a id) (Sum.map c id)).reduceEnv Z)) := by
  have hf : ∀ e e', (VH'.sum VA).ev e e' →
      (VH.sum VA).ev (Sum.map a id e) (Sum.map a id e') := by
    intro e e' he
    cases he with
    | inl h => exact Sum.LiftRel.inl (ha _ _ h)
    | inr h => exact Sum.LiftRel.inr h
  have hg : ∀ o o', (VH.sum VA).out o o' →
      (VH'.sum VA).out (Sum.map c id o) (Sum.map c id o') := by
    intro o o' ho
    cases ho with
    | inl h => exact Sum.LiftRel.inl (hc _ _ h)
    | inr h => exact Sum.LiftRel.inr h
  have h₁ := RealizesSim.mapPorts (Sum.map a id) (Sum.map c id) hf hg h
  have h₂ := realizes_tensor_mapHon S I hI a c
  exact fun ζ Z => le_of_le_of_eq ((Realizes.trans h₁ h₂) ζ Z) (add_zero _)

/-- **Indexed copies split by port.** If `R` realizes the port-typed, lossless `I` behind the
forwarding of the honest port beside `S`, then the `κ` copies of `R` realize the `κ` copies of
`I`, both with the indexed events split by port, behind the forwarding of the indexed honest port
beside `S.indexedKeep`. The bound is the bound of `realizes_indexed` at the environment reduced
through the splitting. -/
theorem indexedSplit {κ : ℕ} [NeZero κ] {R : Sys τ (EH ⊕ EA) (OH ⊕ OA)}
    {I : Sys υ (EH ⊕ EA') (OH ⊕ OA')} {S : MultiHybrid σ EA OA EA' OA'} {hS : S.Opaque VA WA}
    {b : (ζ : Type) → Env (Strat ζ (EH ⊕ EA) (OH ⊕ OA)) ζ → ℝ≥0∞} (hI : I.PortTyped)
    (hRf : ∀ t e, SPComp.NoFail (R.step t e)) (hIf : ∀ t e, SPComp.NoFail (I.step t e))
    (idle : EH ⊕ EA) {oR oI : OH ⊕ OA} (hRi : IdleAt R idle oR)
    (hIi : IdleAt (((idSim EH OH).tensor S).withSub I) idle oI)
    (h : RealizesSim R I (Simulator.tensor (idSim EH OH) S (idSim_opaque VH) hS) b) :
    RealizesSim ((R.indexed (ι := Fin κ)).mapPorts splitIdx id)
      ((I.indexed (ι := Fin κ)).mapPorts splitIdx id)
      (Simulator.tensor (idSim (Fin κ × EH) OH) (S.indexedKeep (ι := Fin κ))
        (idSim_opaque (VH.indexed (Fin κ))) hS.indexedKeep)
      (fun ζ Z => ∑ j : Fin κ,
        b (RState ((Fin κ → (Unit × σ) × υ) × (Fin κ → τ)) (ζ × Unit) (EH ⊕ EA) (OH ⊕ OA))
          ((indexedCtx (((idSim EH OH).tensor S).withSub I) R (fun i : Fin κ => i.val < j.val)
            (withSub_noFail _ I hIf) hRf j).reduceEnv idle
            ((Open.mapPorts splitIdx id).reduceEnv Z))) := by
  have h₁ := realizes_indexed (κ := κ) (withSub_noFail _ I hIf) hRf idle hRi hIi h
  have h₂ := Open.realizes_relabel () (fun e => ((), splitIdx e)) (fun _ => id) h₁
  have h₃ := realizes_tensor_indexedSplit (ι := Fin κ) S I hI
  exact fun ζ => ((h₂ ζ).triangle (h₃ ζ).symm).mono fun _ => by
    simp only [add_zero]
    exact le_rfl

end RealizesSim

end CatCrypt.Crypto.UCTransparent

/-! ## The PVW base OTs -/

namespace CatCrypt.Crypto.OT.IKNPPVW

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.OT.IKNPWake CatCrypt.Crypto.OT.PVW
open CatCrypt.Crypto.OT.IKNPSquare CatCrypt.Examples
open scoped ENNReal

variable {gp : GroupParam} {κ m : ℕ}

/-- The honest events of one base OT as events of PVW on tuples of one. -/
def tupEv : BPair m ⊕ Bool → PVWHonest.InEv 1 (Fin m → Bool)
  | .inl p => .inl fun _ => p
  | .inr b => .inr fun _ => b

/-- The honest outputs of PVW on tuples of one as outputs of one base OT. -/
def untupOut : PVWHonest.InOut 1 (Fin m → Bool) → HOut m
  | .inl b => .inl b
  | .inr y => .inr (y.map (· 0))

/-- The tuple of one of a base-OT event, read at the index `0`, is that event. -/
theorem oneEv_tupEv (e : (BPair m ⊕ Bool) ⊕ SchedEv) :
    FOTSched.oneEv (Sum.map tupEv id e) = e := by
  rcases e with (p | b) | a <;> rfl

/-- The output of one base OT read through the tuple of one is that output. -/
theorem untupOut_oneOut (o : HOut m ⊕ SchedOut) :
    Sum.map untupOut id (FOTSched.oneOut o) = o := by
  rcases o with (b | y) | a
  · rfl
  · cases y <;> rfl
  · rfl

/-- **One PVW base OT**: the pull-form PVW oblivious transfer of one column pair with the CRS
`crs`, the columns sent as group elements through the embedding `emb`, on the honest port of one
base OT. -/
noncomputable def pvwOne (crs : CRS gp) (emb : (Fin m → Bool) ↪ gp.Scalar) :=
  (PVWPull.pvwPull (m := 1) crs (bitsCode gp emb) (bitsDecode gp emb)).mapPorts
    (Sum.map tupEv id) (Sum.map untupOut id)

/-- **One PVW base OT realizes `FOTSched baseOut`** behind the forwarding of the honest port
beside `simP`, at distance `0`. -/
theorem pvwOne_realizesSim (crs : CRS gp) (emb : (Fin m → Bool) ↪ gp.Scalar) :
    RealizesSim (pvwOne crs emb) (FOTSched (baseOut (m := m)))
      (Simulator.tensor (MultiHybrid.idSim (BPair m ⊕ Bool) (HOut m)) (PVWPull.simP gp 1)
        (MultiHybrid.idSim_opaque hidView) (MultiHybrid.opaque_eqView _)) (fun _ _ => 0) := by
  have h₀ := PVWPull.pvwPull_realizesSim (m := 1) (VH := hidView) crs (bitsCode gp emb)
    (bitsDecode gp emb) (bitsDecode_bitsCode gp emb)
  have h₁ := RealizesSim.mapHon (VH' := hidView) (FOTSched_portTyped _) tupEv untupOut
    (fun _ _ _ => trivial) (fun _ _ _ => trivial) h₀
  refine RealizesSim.subst_stepMap FOTSched.oneSt FOTSched.oneSt_init (fun t e => ?_) h₁
  have h := congrArg (fun c => SPComp.map (fun p => (p.1, Sum.map untupOut id p.2)) c)
    (FOTSched.one_stepMap (baseOut (m := m)) t (Sum.map tupEv id e))
  simp only [Sys.mapPorts, Sys.relabel, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind,
    oneEv_tupEv, untupOut_oneOut, Prod.mk.eta, SPComp.bind_pure] at h ⊢
  exact h

/-- The scheduled transfer never fails. -/
theorem fotSched_noFail {X C Y : Type} (out : X → C → Y) (t : SchedSt X C Y)
    (e : (X ⊕ C) ⊕ SchedEv) : SPComp.NoFail ((FOTSched out).step t e) := by
  rcases e with (x | c) | a <;>
    simp only [FOTSched, Sys.ofPorts_step_inl, Sys.ofPorts_step_inr, FOTSched.sendSys,
      FOTSched.recvSys, FOTSched.schedSys, SPComp.map, SPComp.pure_bind] <;>
    exact SPComp.pure_noFail _

/-- One PVW base OT never fails. -/
theorem pvwOne_noFail (crs : CRS gp) (emb : (Fin m → Bool) ↪ gp.Scalar) :
    ∀ t e, SPComp.NoFail ((pvwOne crs emb).step t e) := by
  have hR : ∀ t e, SPComp.NoFail
      ((PVWPull.realP (m := 1) crs (bitsCode gp emb) (bitsDecode gp emb)).step t e) :=
    MultiHybrid.withSub_noFail _ _ (FChan_noFail _ _)
  intro t e
  simp only [pvwOne, Sys.mapPorts, Sys.relabel, SPComp.map]
  refine Assumptions.SPComp.bind_noFail ?_ fun _ => SPComp.pure_noFail _
  rcases e with h | a
  · exact hR _ _
  · simp only [Sum.map_inr, id, PVWPull.pvwPull, Sys.wakeCloseSilent]
    split
    · exact hR _ _
    · exact Assumptions.SPComp.bind_noFail (hR _ _) fun _ =>
        Assumptions.SPComp.bind_noFail (hR _ _) fun _ => SPComp.pure_noFail _

/-- One PVW base OT is idle at the channel's `idle`. -/
theorem pvwOne_idleAt (crs : CRS gp) (emb : (Fin m → Bool) ↪ gp.Scalar) :
    MultiHybrid.IdleAt (pvwOne crs emb) (.inr .idle) (.inr .ack) := by
  intro t
  simp only [pvwOne, Sys.mapPorts, Sys.relabel, Sum.map_inr, id,
    PVWPull.pvwPull_idleAt crs _ _ t, SPComp.map, SPComp.pure_bind]

/-- The simulated base OT is idle at the channel's `idle`. -/
theorem simOne_idleAt :
    MultiHybrid.IdleAt (((MultiHybrid.idSim (BPair m ⊕ Bool) (HOut m)).tensor
      (PVWPull.simP gp 1)).withSub (FOTSched (baseOut (m := m)))) (.inr .idle) (.inr .ack) := by
  rintro ⟨⟨⟨⟩, s⟩, u⟩
  rw [MultiHybrid.tensor_withSub_step_inr _ _ _ (FOTSched.schedSys _) (fun _ _ => rfl)]
  simp [MultiHybrid.stepFuel, PVWPull.simP, PVWPull.simPStart, MultiHybrid.drive, SPComp.map,
    SPComp.pure_bind]

variable (κ) in
/-- **The `κ` PVW base OTs**: `κ` copies of `pvwOne`, with the indexed events split by port on
the honest port of `FOTSchedPar` and on the indexed channel events. -/
noncomputable def pvwBase (crs : CRS gp) (emb : (Fin m → Bool) ↪ gp.Scalar) :=
  (((pvwOne crs emb).indexed (ι := Fin κ)).mapPorts splitIdx id).mapPorts (Sum.map splitIdx id) id

/-- The view of the honest port of the base OTs: equal events, all outputs related. -/
def baseHV (κ m : ℕ) : PubView (HEv κ m) (HOut m) where
  ev := Eq
  out _ _ := True

/-- **The PVW base OTs realize the `κ` scheduled base OTs** `baseG κ m = FOTSchedPar (Fin κ)
baseOut` behind the forwarding of the honest port beside `simP.indexedKeep`, at distance `0`.
-/
theorem pvwBase_realizesSim [NeZero κ] (crs : CRS gp) (emb : (Fin m → Bool) ↪ gp.Scalar) :
    RealizesSim (pvwBase κ crs emb) (baseG κ m)
      (Simulator.tensor (MultiHybrid.idSim (HEv κ m) (HOut m))
        ((PVWPull.simP gp 1).indexedKeep (ι := Fin κ))
        (MultiHybrid.idSim_opaque (baseHV κ m)) (MultiHybrid.opaque_eqView _).indexedKeep)
      (fun _ _ => 0) := by
  have h₁ := RealizesSim.indexedSplit (κ := κ) (FOTSched_portTyped _) (pvwOne_noFail crs emb)
    (fotSched_noFail _) (.inr .idle) (pvwOne_idleAt crs emb) simOne_idleAt
    (pvwOne_realizesSim crs emb)
  have h₂ := RealizesSim.mapHon (VH' := baseHV κ m)
    (Sys.PortTyped.indexedSplit (FOTSched_portTyped _)) splitIdx id
    (fun e e' he => by subst he; exact ⟨rfl, trivial⟩) (fun _ _ _ => trivial) h₁
  simp only [Sum.map_id_id] at h₂
  have h₃ := RealizesSim.subst_stepMap (Y := baseG κ m)
    (X := (((FOTSched (baseOut (m := m))).indexed (ι := Fin κ)).mapPorts splitIdx id).mapPorts
      (Sum.map splitIdx id) id)
    (π := (MultiHybrid.idSim (HEv κ m) (HOut m)).tensor
      ((PVWPull.simP gp 1).indexedKeep (ι := Fin κ)))
    (hπ := (MultiHybrid.idSim_opaque (baseHV κ m)).tensor
      (MultiHybrid.opaque_eqView _).indexedKeep) id rfl (fun t e => ?_) h₂
  · exact fun ζ Z => le_of_le_of_eq (h₃ ζ Z) Finset.sum_const_zero
  · rcases e with (⟨i, p⟩ | ⟨i, b⟩) | ⟨i, a⟩ <;>
      simp [baseG, FOTSchedPar, FOTSched, Sys.mapPorts, Sys.relabel, splitIdx, SPComp.map,
        SPComp.bind_assoc, SPComp.pure_bind]

/-! ## Idle events through forwarding -/

/-- A hybrid beside the forwarding of a port, over a subroutine idle at `inr e`, is idle at
`inr e`. -/
theorem idleAt_tensor_fwd {σ τ E O EG OG E' O' : Type} (π : MultiHybrid σ E O EG OG)
    (X : Sys τ (EG ⊕ E') (OG ⊕ O')) (e : E') (o : O')
    (hX : ∀ t, X.step t (.inr e) = SPComp.pure (t, .inr o)) :
    MultiHybrid.IdleAt ((π.tensor (MultiHybrid.idSim E' O')).withSub X) (.inr e) (.inr o) := by
  rintro ⟨⟨s, ⟨⟩⟩, t⟩
  simp only [MultiHybrid.withSub]
  generalize (π.tensor (MultiHybrid.idSim E' O')).fuel = n
  cases n <;> simp [MultiHybrid.drive, MultiHybrid.tensor, MultiHybrid.idSim, hX, SPComp.map,
    SPComp.pure_bind]

/-- A hybrid beside a simulator beside the forwarding of a port, over a subroutine idle at
`inr (inr e)`, is idle at `inr (inr e)`. -/
theorem idleAt_tensor_tensor_fwd {σ σ₂ τ E O EG OG E₂ O₂ EG₂ OG₂ E' O' : Type}
    (π : MultiHybrid σ E O EG OG) (π₂ : MultiHybrid σ₂ E₂ O₂ EG₂ OG₂)
    (X : Sys τ (EG ⊕ (EG₂ ⊕ E')) (OG ⊕ (OG₂ ⊕ O'))) (e : E') (o : O')
    (hX : ∀ t, X.step t (.inr (.inr e)) = SPComp.pure (t, .inr (.inr o))) :
    MultiHybrid.IdleAt ((π.tensor (π₂.tensor (MultiHybrid.idSim E' O'))).withSub X)
      (.inr (.inr e)) (.inr (.inr o)) := by
  rintro ⟨⟨s, s₂, ⟨⟩⟩, t⟩
  simp only [MultiHybrid.withSub]
  generalize (π.tensor (π₂.tensor (MultiHybrid.idSim E' O'))).fuel = n
  cases n <;> simp [MultiHybrid.drive, MultiHybrid.tensor, MultiHybrid.idSim, hX, SPComp.map,
    SPComp.pure_bind]

/-- A system beside the IKNP channel is idle at the channel's `idle`. -/
theorem withChan_idle {τ EH EA OH OA : Type} {M : Type} (X : Sys τ (EH ⊕ EA) (OH ⊕ OA))
    (t : τ × ChanSt (Msg m M)) :
    (X.withChan (chanC m M)).step t (.inr (.inr .idle)) = SPComp.pure (t, .inr (.inr .ack)) := by
  obtain ⟨t, u⟩ := t
  simp [Sys.withChan, Sys.mapPorts, Sys.relabel, chanEv, chanOut, chanC, FChan, FChan.advSys,
    FChan.advStep, SPComp.map, SPComp.pure_bind]

/-! ## The corruption port moved -/

/-- The relabelling that moves the corruption events from the adversary port to the parties'
port. -/
def unpeekEv {EP P A : Type} : (EP ⊕ P) ⊕ A → EP ⊕ (A ⊕ P)
  | .inl (.inl e) => .inl e
  | .inl (.inr p) => .inr (.inr p)
  | .inr a => .inr (.inl a)

/-- The relabelling that moves the answers of corruption events to the parties' port. -/
def unpeekOut {OP L AO : Type} : OP ⊕ (AO ⊕ L) → (OP ⊕ L) ⊕ AO
  | .inl o => .inl (.inl o)
  | .inr (.inl a) => .inr a
  | .inr (.inr l) => .inl (.inr l)

/-- The relabelling that moves the corruption events from the parties' port to the adversary
port. -/
def peekG {EP P A : Type} : EP ⊕ (A ⊕ P) → (EP ⊕ P) ⊕ A
  | .inl e => .inl (.inl e)
  | .inr (.inl a) => .inr a
  | .inr (.inr p) => .inl (.inr p)

/-- The relabelling that moves the answers of corruption events to the adversary port. -/
def peekOutG {OP L AO : Type} : (OP ⊕ L) ⊕ AO → OP ⊕ (AO ⊕ L)
  | .inl (.inl o) => .inl o
  | .inl (.inr l) => .inr (.inr l)
  | .inr a => .inr (.inl a)

/-- `peekEv` inverts `unpeekEv`. -/
theorem peekEv_unpeekEv {M P : Type} (e : ((InEv m M ⊕ WakeEv κ) ⊕ P) ⊕ AEv κ m M) :
    peekEv (unpeekEv e) = e := by
  rcases e with (e | p) | a <;> rfl

/-- `unpeekOut` inverts `peekOut`. -/
theorem unpeekOut_peekOut {M L : Type} (o : (InOut m M ⊕ L) ⊕ AOut m M) :
    unpeekOut (peekOut o) = o := by
  rcases o with (o | l) | a <;> rfl

/-- The view of the parties' port: inputs and outputs hidden, wakes and corruption events
public. -/
abbrev vF (κ m : ℕ) (M P L : Type) : PubView ((InEv m M ⊕ WakeEv κ) ⊕ P) (InOut m M ⊕ L) :=
  ((hidView : PubView (InEv m M) (InOut m M)).wake (WakeEv κ)).sum PubView.eqView

/-- The view of the interface of the protocol over the ideal base OTs and the channel, with the
corruption events on the parties' port. -/
abbrev vU (κ m : ℕ) (M P L : Type) :
    PubView (((InEv m M ⊕ WakeEv κ) ⊕ P) ⊕ AEv κ m M) ((InOut m M ⊕ L) ⊕ AOut m M) :=
  (vF κ m M P L).sum (((PubView.eqView : PubView SchedEv SchedOut).indexed (Fin κ)).sum
    PubView.eqView)

/-- `unpeekEv` sends events related by `vU` to events related by `outerV`. -/
theorem unpeekEv_rel {M P L : Type} (e e' : ((InEv m M ⊕ WakeEv κ) ⊕ P) ⊕ AEv κ m M)
    (h : (vU κ m M P L).ev e e') : (outerV κ m M P L).ev (unpeekEv e) (unpeekEv e') := by
  rcases e with (e | p) | (⟨i, a⟩ | d) <;> rcases e' with (e' | p') | (⟨i', a'⟩ | d') <;>
    simp_all [PubView.sum, PubView.eqView, PubView.indexed, PubView.wake, unpeekEv]

/-- `unpeekOut` sends outputs related by `outerV` to outputs related by `vU`. -/
theorem unpeekOut_rel {M P L : Type} (o o' : InOut m M ⊕ (AOut m M ⊕ L))
    (h : (outerV κ m M P L).out o o') : (vU κ m M P L).out (unpeekOut o) (unpeekOut o') := by
  rcases o with o | (a | l) <;> rcases o' with o' | (a' | l') <;>
    simp_all [PubView.sum, PubView.eqView, PubView.indexed, PubView.wake, unpeekOut, hidView,
      Sum.LiftRel.refl]

/-! ## The composition -/

/-- The adversary events of the PVW base OTs beside the IKNP channel. -/
abbrev AEvP (κ : ℕ) (gp : GroupParam) (m : ℕ) (M : Type) :=
  (Fin κ × ChanAEv (PVWHonest.V gp 1)) ⊕ ChanAEv (Msg m M)

/-- The adversary outputs of the PVW base OTs beside the IKNP channel. -/
abbrev AOutP (gp : GroupParam) (m : ℕ) (M : Type) :=
  ChanAOut (PVWHonest.V gp 1) Unit ⊕ ChanAOut (Msg m M) Unit

variable {M : Type}

/-- The deliveries: the delivery of the PVW channel `i` wakes the sender for the base OT `i`, the
delivery of the IKNP channel wakes the receiver. -/
def dlvP {P : Type} : AEvP κ gp m M ⊕ P → Option (WakeEv κ)
  | .inl (.inl (i, .deliver)) => some (.wakeS i)
  | .inl (.inr .deliver) => some .wakeR
  | _ => none

/-- The answer to a wake that would need a second pass. -/
def cutP {L : Type} (_ : WakeEv κ) : InOut m M ⊕ (AOutP gp m M ⊕ L) := .inl (.inl false)

/-- The idle event: the IKNP channel's `idle`. -/
def idleP {P : Type} : (InEv m M ⊕ (AEvP κ gp m M ⊕ P)) ⊕ WakeEv κ :=
  .inl (.inr (.inl (.inr .idle)))

/-- The simulator of the PVW base OTs: the indexed copies of `simP` keeping the active copy. -/
noncomputable abbrev simKeep (κ : ℕ) (gp : GroupParam) [NeZero κ] :=
  (PVWPull.simP gp 1).indexedKeep (ι := Fin κ)

/-- The view of the interface of IKNP over the PVW base OTs with the corruption events on the
parties' port. -/
abbrev vC (κ : ℕ) (gp : GroupParam) (m : ℕ) (M P L : Type) :=
  (vF κ m M P L).sum
    (((PubView.eqView :
        PubView (ChanAEv (PVWHonest.V gp 1)) (ChanAOut (PVWHonest.V gp 1) Unit)).indexed
      (Fin κ)).sum (PubView.eqView : PubView (ChanAEv (Msg m M)) (ChanAOut (Msg m M) Unit)))

/-- The view of the interface of IKNP over the PVW base OTs: inputs and outputs hidden, wakes,
adversary and corruption events public. -/
abbrev vW (κ : ℕ) (gp : GroupParam) (m : ℕ) (M P L : Type) :=
  ((hidView : PubView (InEv m M) (InOut m M)).wake (WakeEv κ)).sum
    (PubView.eqView : PubView (AEvP κ gp m M ⊕ P) (AOutP gp m M ⊕ L))

/-- `peekG` sends events related by `vW` to events related by `vC`. -/
theorem peekG_rel {P L : Type} (e e' : (InEv m M ⊕ WakeEv κ) ⊕ (AEvP κ gp m M ⊕ P))
    (h : (vW κ gp m M P L).ev e e') : (vC κ gp m M P L).ev (peekG e) (peekG e') := by
  rcases h with ⟨h⟩ | ⟨h⟩
  · exact Sum.LiftRel.inl (Sum.LiftRel.inl h)
  · obtain rfl := h
    rename_i x
    rcases x with (⟨i, a⟩ | d) | p
    · exact Sum.LiftRel.inr (Sum.LiftRel.inl ⟨rfl, rfl⟩)
    · exact Sum.LiftRel.inr (Sum.LiftRel.inr rfl)
    · exact Sum.LiftRel.inl (Sum.LiftRel.inr rfl)

/-- `peekOutG` sends outputs related by `vC` to outputs related by `vW`. -/
theorem peekOutG_rel {P L : Type} (o o' : (InOut m M ⊕ L) ⊕ AOutP gp m M)
    (h : (vC κ gp m M P L).out o o') : (vW κ gp m M P L).out (peekOutG o) (peekOutG o') := by
  rcases h with ⟨⟨h⟩ | ⟨h⟩⟩ | ⟨⟨h⟩ | ⟨h⟩⟩
  · exact Sum.LiftRel.inl trivial
  · obtain rfl : _ = _ := h
    exact Sum.LiftRel.inr rfl
  · obtain rfl : _ = _ := h
    exact Sum.LiftRel.inr rfl
  · obtain rfl : _ = _ := h
    exact Sum.LiftRel.inr rfl

section Compose

variable [AddCommGroup M] (H : Fin m → (Fin κ → Bool) → M) {P L LS LR EGA OGA : Type}
  (φS : IKNPSenderView κ m Unit → LS) (φR : IKNPReceiverView κ m M Unit × (Fin m → M) → LR)
  (ans : Option LS → Option LR → P → L) [NeZero κ]
  (sch : SchedEv → EGA) (stat : OGA → Bool × Bool) (pkEv : EGA)
  (simS : OGA → SPComp LS) (simR : OGA → SPComp LR)
  (hSf : ∀ a, SPComp.NoFail (simS a)) (hRf : ∀ a, SPComp.NoFail (simR a))
  (crs : CRS gp) (emb : (Fin m → Bool) ↪ gp.Scalar)

/-- **IKNP over the PVW base OTs, before the wake closure**: the parties with their own draw over
the `κ` PVW base OTs beside the IKNP channel, the adversary ports forwarded. -/
noncomputable def iknpPVWOpen :=
  ((partyLazy H φS φR ans).tensor (MultiHybrid.idSim (AEvP κ gp m M) (AOutP gp m M))).withSub
    ((pvwBase κ crs emb).withChan (chanC m M))

/-- **IKNP over the PVW base OTs**: `iknpPVWOpen` with the corruption events on the adversary
port, closed by the wakes `dlvP`. -/
noncomputable def iknpPVW :=
  ((iknpPVWOpen H φS φR ans crs emb).mapPorts peekG peekOutG).wakeClose dlvP cutP

/-- The IKNP simulator `simW` with the corruption port moved to the parties' port. -/
noncomputable def simU :
    Simulator (((InEv m M ⊕ WakeEv κ) ⊕ P) ⊕ AEv κ m M) ((InOut m M ⊕ L) ⊕ AOut m M)
      (InEv m M ⊕ EGA) (InOut m M ⊕ OGA) (vU κ m M P L) (innerV m M EGA OGA) :=
  (Simulator.ofMultiHybrid (simW ans sch stat pkEv simS simR hSf hRf (κ := κ))
    (simW_opaque ans sch stat pkEv simS simR hSf hRf)).mapPorts unpeekEv unpeekOut
    unpeekEv_rel unpeekOut_rel

variable (gp) in
/-- The composite simulator before the wake closure: the forwarding of the parties' port beside
`simKeep` and the forwarding of the IKNP channel's adversary port, over `simU`, with the
corruption events on the adversary port. -/
noncomputable def simC :
    Simulator ((InEv m M ⊕ WakeEv κ) ⊕ (AEvP κ gp m M ⊕ P)) (InOut m M ⊕ (AOutP gp m M ⊕ L))
      (InEv m M ⊕ EGA) (InOut m M ⊕ OGA) (vW κ gp m M P L) (innerV m M EGA OGA) :=
  ((Simulator.ofMultiHybrid
      (MultiHybrid.extendFwd ((InEv m M ⊕ WakeEv κ) ⊕ P) (InOut m M ⊕ L)
        ((simKeep κ gp).tensor (MultiHybrid.idSim (ChanAEv (Msg m M)) (ChanAOut (Msg m M) Unit))))
      (MultiHybrid.Opaque.extendFwd (vF κ m M P L)
        (((MultiHybrid.opaque_eqView (PVWPull.simP gp 1)).indexedKeep (ι := Fin κ)).tensor
          (MultiHybrid.idSim_opaque PubView.eqView)))).comp
      (simU ans sch stat pkEv simS simR hSf hRf)).mapPorts peekG peekOutG peekG_rel peekOutG_rel

variable (gp) in
/-- **The simulator of IKNP over the PVW base OTs**: the wake closure of `simC`. -/
noncomputable def simPVW :
    Simulator (InEv m M ⊕ (AEvP κ gp m M ⊕ P)) (InOut m M ⊕ (AOutP gp m M ⊕ L))
      (InEv m M ⊕ EGA) (InOut m M ⊕ OGA)
      ((hidView : PubView (InEv m M) (InOut m M)).sum PubView.eqView) (innerV m M EGA OGA) :=
  (simC gp ans sch stat pkEv simS simR hSf hRf).wakeClose dlvP (fun _ _ h => congrArg dlvP h)
    cutP (fun _ => Sum.LiftRel.inl trivial)

/-- **IKNP over the ideal base OTs, with the draw in the parties.** A realization of `I` by
`iknpW` behind `simW` is a realization by the parties with their own draw over the base OTs
beside the channel behind `simU`. -/
theorem iknpLazy_realizesSim {υ : Type} {I : Sys υ (InEv m M ⊕ EGA) (InOut m M ⊕ OGA)}
    {b : (ζ : Type) → Env (Strat ζ ((InEv m M ⊕ WakeEv κ) ⊕ (AEv κ m M ⊕ P))
      (InOut m M ⊕ (AOut m M ⊕ L))) ζ → ℝ≥0∞}
    (h : RealizesSim (iknpW H φS φR ans) I
      (Simulator.ofMultiHybrid (simW ans sch stat pkEv simS simR hSf hRf)
        (simW_opaque ans sch stat pkEv simS simR hSf hRf)) b) :
    RealizesSim (((partyLazy H φS φR ans).tensor (MultiHybrid.idSim (AEv κ m M) (AOut m M))).withSub
        ((baseG κ m).withChan (chanC m M))) I (simU ans sch stat pkEv simS simR hSf hRf)
      (fun ζ Z => b (ζ × Unit) ((Open.mapPorts unpeekEv unpeekOut).reduceEnv Z)) := by
  have h₁ : Realizes (realLazyW H φS φR ans) _ b :=
    realizes_of_view_eq (fun ζ Z => (view_iknpW_eq_lazy H φS φR ans Z).symm) h
  have h₂ := RealizesSim.mapPorts (V := vU κ m M P L)
    (S := Simulator.ofMultiHybrid (simW ans sch stat pkEv simS simR hSf hRf)
      (simW_opaque ans sch stat pkEv simS simR hSf hRf)) unpeekEv unpeekOut unpeekEv_rel
    unpeekOut_rel h₁
  refine realizes_of_view_eq (A := (realLazyW H φS φR ans).mapPorts unpeekEv unpeekOut)
    (fun ζ Z => view_eq_of_stepMap (((partyLazy H φS φR ans).tensor
      (MultiHybrid.idSim (AEv κ m M) (AOut m M))).withSub ((baseG κ m).withChan (chanC m M)))
      ((realLazyW H φS φR ans).mapPorts unpeekEv unpeekOut) id rfl (fun t e => ?_) Z) h₂
  simp only [realLazyW, Sys.mapPorts, Sys.relabel, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind,
    peekEv_unpeekEv, unpeekOut_peekOut, id, Prod.mk.eta, SPComp.bind_pure]

/-- **IKNP over the PVW base OTs** (composition plumbing). A realization of `I` by `iknpW` behind
`simW` with bound `b` gives a realization of `I` by IKNP over `κ` PVW base OTs, closed by the
wakes, behind `simPVW`, with bound `b` at the environment reduced through the wake closure, the
relabellings and the extended simulator; the PVW base OTs contribute `0`. -/
theorem iknpPVW_realizesSim {υ : Type} {I : Sys υ (InEv m M ⊕ EGA) (InOut m M ⊕ OGA)}
    {b : (ζ : Type) → Env (Strat ζ ((InEv m M ⊕ WakeEv κ) ⊕ (AEv κ m M ⊕ P))
      (InOut m M ⊕ (AOut m M ⊕ L))) ζ → ℝ≥0∞}
    (h : RealizesSim (iknpW H φS φR ans) I
      (Simulator.ofMultiHybrid (simW ans sch stat pkEv simS simR hSf hRf)
        (simW_opaque ans sch stat pkEv simS simR hSf hRf)) b) :
    RealizesSim (iknpPVW H φS φR ans crs emb) I (simPVW gp ans sch stat pkEv simS simR hSf hRf)
      (fun _ Z => b _ ((Open.mapPorts unpeekEv unpeekOut).reduceEnv
        ((MultiHybrid.extendFwd ((InEv m M ⊕ WakeEv κ) ⊕ P) (InOut m M ⊕ L)
          ((simKeep κ gp).tensor
            (MultiHybrid.idSim (ChanAEv (Msg m M)) (ChanAOut (Msg m M) Unit)))).reduceEnv
          (.inr (.inr .idle))
          ((Open.mapPorts peekG peekOutG).reduceEnv
            ((Open.relabel none (wakeEv dlvP) wakeOut).reduceEnv
              ((MultiHybrid.fbHybrid 1 cutP).reduceEnv idleP Z)))))) := by
  have hF := iknpLazy_realizesSim H φS φR ans sch stat pkEv simS simR hSf hRf h
  have hρ := pvwBase_realizesSim (κ := κ) crs emb
  have hρI₀ : MultiHybrid.IdleAt (pvwBase κ crs emb) (.inr (default, .idle)) (.inr .ack) := by
    intro t
    simp only [pvwBase, Sys.mapPorts, Sys.relabel, Sum.map_inr, splitIdx, id, SPComp.map,
      Sys.indexed_step, SPComp.bind_assoc, SPComp.pure_bind]
    rw [pvwOne_idleAt crs emb]
    simp [SPComp.pure_bind]
  have hGI₀ : MultiHybrid.IdleAt (((MultiHybrid.idSim (HEv κ m) (HOut m)).tensor
      (simKeep κ gp)).withSub (baseG κ m)) (.inr (default, .idle)) (.inr .ack) := by
    rintro ⟨⟨⟨⟩, ss, j⟩, u⟩
    rw [MultiHybrid.tensor_withSub_step_inr _ _ _
      ((FOTSched.schedSys (baseOut (m := m))).indexed (ι := Fin κ)) (fun _ _ => rfl)]
    simp [MultiHybrid.stepFuel, MultiHybrid.indexedKeep_start, PVWPull.simP,
      PVWPull.simPStart, MultiHybrid.drive, SPComp.map, SPComp.pure_bind]
  have hFI : MultiHybrid.IdleAt ((simU ans sch stat pkEv simS simR hSf hRf (κ := κ)).withSub I)
      (.inr (.inr .idle)) (.inr (.inr .ack)) := by
    intro t
    have := simW_idleAt ans sch stat pkEv simS simR hSf hRf I t
    simp only [wakeEv, dlvW, idleW] at this
    simp [simU, Simulator.mapPorts, Simulator.ofMultiHybrid, Sys.mapPorts, Sys.relabel,
      unpeekEv, unpeekOut, this, SPComp.map, SPComp.pure_bind]
  have hmod := RealizesSim.modular_withChan (VF := vF κ m M P L) (VC := PubView.eqView)
    (VD := PubView.eqView) (partyLazy H φS φR ans) (simKeep κ gp)
    ((MultiHybrid.opaque_eqView _).indexedKeep) (pvwBase κ crs emb) (baseG κ m)
    (FOTSchedPar_portTyped _) (chanC m M) (FChan_portTyped _ _) (FChan_noFail _ _) I
    (simU ans sch stat pkEv simS simR hSf hRf) (.inr (default, .idle)) (.inr (.inr .idle))
    (.inr (.inr .idle)) (.inr (.inr .idle)) ⟨_, hρI₀⟩ ⟨_, hGI₀⟩
    ⟨_, fun t => withChan_idle _ t⟩
    ⟨_, idleAt_tensor_tensor_fwd _ _ _ _ _ fun t => withChan_idle _ t⟩
    ⟨_, idleAt_tensor_fwd _ _ _ _ fun t => withChan_idle _ t⟩ ⟨_, hFI⟩ hρ hF
  have h₂ := RealizesSim.mapPorts (V := vW κ gp m M P L) peekG peekOutG peekG_rel
    peekOutG_rel hmod
  have hRI : MultiHybrid.IdleAt ((iknpPVWOpen H φS φR ans crs emb).mapPorts peekG peekOutG)
      (wakeEv dlvP (idleP (P := P))).2 (.inr (.inl (.inr .ack))) := by
    intro t
    have := idleAt_tensor_fwd (partyLazy H φS φR ans) _ _ _
      (fun t => withChan_idle (pvwBase κ crs emb) t) t
    simp [iknpPVWOpen, Sys.mapPorts, Sys.relabel, wakeEv, dlvP, idleP, peekG, peekOutG, this,
      SPComp.map, SPComp.pure_bind]
  have hSI : MultiHybrid.IdleAt
      ((simC gp ans sch stat pkEv simS simR hSf hRf (κ := κ)).withSub I)
      (wakeEv dlvP (idleP (P := P))).2 (.inr (.inl (.inr .ack))) := by
    intro t
    have := idleAt_tensor_tensor_fwd (MultiHybrid.idSim ((InEv m M ⊕ WakeEv κ) ⊕ P)
      (InOut m M ⊕ L)) (simKeep κ gp) _ _ _ hFI t
    simp [simC, Simulator.mapPorts, Simulator.comp, Simulator.ofMultiHybrid,
      MultiHybrid.extendFwd, Sys.mapPorts, Sys.relabel, wakeEv, dlvP, idleP, peekG, peekOutG,
      this, SPComp.map, SPComp.pure_bind]
  have h₃ := RealizesSim.wakeClose dlvP (fun _ _ h => congrArg dlvP h) cutP
    (fun _ => Sum.LiftRel.inl trivial) idleP _ _ hRI hSI h₂
  exact fun ζ Z => le_of_le_of_eq (h₃ ζ Z) (zero_add _)

end Compose

/-! ## The three cases -/

section Cases

variable [AddCommGroup M] (H : Fin m → (Fin κ → Bool) → M) [NeZero κ] (crs : CRS gp)
  (emb : (Fin m → Bool) ↪ gp.Scalar)

/-- **IKNP over PVW base OTs, both parties honest.** Ideal functionality: `FOTSched otChoose`,
the scheduled transfer of `m` message pairs. Real protocol: the IKNP parties over `κ` copies of
the pull-form PVW OT of one column pair beside the secure channel, closed by the wakes. Simulator:
`simPVW` over the honest IKNP simulator; inputs hidden, wakes public. Distance `0`. -/
theorem iknpPVW_H_realizesSim :
    RealizesSim (iknpPVW H (fun _ : IKNPSenderView κ m Unit => ())
        (fun _ : IKNPReceiverView κ m M Unit × (Fin m → M) => ()) ansH crs emb)
      (FOTSched otChoose)
      (simPVW gp ansH id statSched .poll (fun _ => SPComp.pure ()) (fun _ => SPComp.pure ())
        (fun _ => SPComp.pure_noFail _) (fun _ => SPComp.pure_noFail _)) (fun _ _ => 0) :=
  iknpPVW_realizesSim H _ _ ansH id statSched .poll _ _ _ _ crs emb (iknpH_realizesSim H)

/-- **IKNP over PVW base OTs against a semi-honest corrupt sender.** Ideal functionality:
`FOTSchedSH otChoose leakSend`. Real protocol: the IKNP parties over `κ` PVW base OTs beside the
secure channel, closed by the wakes, the corruption event showing the sender's secret and
columns once it has sent. Simulator: `simPVW` over the corrupt-sender IKNP simulator, which draws
the sender's view by `iknpSimS`. Distance `0`. -/
theorem iknpPVW_S_realizesSim :
    RealizesSim (iknpPVW H (fun v : IKNPSenderView κ m Unit => v)
        (fun _ : IKNPReceiverView κ m M Unit × (Fin m → M) => ()) ansS crs emb)
      (FOTSchedSH otChoose leakSend)
      (simPVW gp ansS .inl statSH (.inr ())
        (fun _ => iknpSimS (fun _ _ => SPComp.pure ()) (fun _ => ((0 : M), (0 : M))))
        (fun _ => SPComp.pure ()) (fun _ => iknpSimS_noFail _) (fun _ => SPComp.pure_noFail _))
      (fun _ _ => 0) :=
  iknpPVW_realizesSim H (fun v : IKNPSenderView κ m Unit => v)
    (fun _ : IKNPReceiverView κ m M Unit × (Fin m → M) => ()) ansS
    (Sum.inl : SchedEv → SchedEv ⊕ Unit) statSH (.inr ())
    (fun _ => iknpSimS (fun _ _ => SPComp.pure ()) (fun _ => ((0 : M), (0 : M))))
    (fun _ => SPComp.pure ()) (fun _ => iknpSimS_noFail _) (fun _ => SPComp.pure_noFail _) crs
    emb (iknpS_realizesSim H)

/-- **IKNP over PVW base OTs against a semi-honest corrupt receiver.** Ideal functionality:
`FOTSchedSH otChoose (leakRecv otChoose)`. Real protocol: the IKNP parties over `κ` PVW base OTs
beside the secure channel, closed by the wakes, the corruption event showing the receiver's view
once it has received the message. Simulator: `simPVW` over the corrupt-receiver IKNP simulator,
which completes the receiver's view by `iknpSimR`. Bound: the correlation-robust hash advantage of
`iknpWakeCRRed H` at the environment reduced through the wake closure, the relabellings and the
extended simulator. -/
theorem iknpPVW_R_realizesSim [Fintype M] [Nonempty M] :
    RealizesSim (iknpPVW H (fun _ : IKNPSenderView κ m Unit => ()) (fun v : RView κ m M => v)
        ansR crs emb)
      (FOTSchedSH otChoose (leakRecv otChoose))
      (simPVW gp ansR .inl statSH (.inr ()) (fun _ => SPComp.pure ()) (simRR H)
        (fun _ => SPComp.pure_noFail _) (simRR_noFail H))
      (fun _ Z => CRHash_Advantage H (iknpWakeCRRed H
        ((Open.mapPorts unpeekEv unpeekOut).reduceEnv
          ((MultiHybrid.extendFwd ((InEv m M ⊕ WakeEv κ) ⊕ Unit) (InOut m M ⊕ Option (RView κ m M))
            ((simKeep κ gp).tensor
              (MultiHybrid.idSim (ChanAEv (Msg m M)) (ChanAOut (Msg m M) Unit)))).reduceEnv
            (.inr (.inr .idle))
            ((Open.mapPorts peekG peekOutG).reduceEnv
              ((Open.relabel none (wakeEv dlvP) wakeOut).reduceEnv
                ((MultiHybrid.fbHybrid 1 cutP).reduceEnv idleP Z))))))) :=
  iknpPVW_realizesSim H (fun _ : IKNPSenderView κ m Unit => ()) (fun v : RView κ m M => v) ansR
    (Sum.inl : SchedEv → SchedEv ⊕ Unit) statSH (.inr ()) (fun _ => SPComp.pure ()) (simRR H)
    (fun _ => SPComp.pure_noFail _) (simRR_noFail H) crs emb (iknpR_realizesSim H)

end Cases

end CatCrypt.Crypto.OT.IKNPPVW
