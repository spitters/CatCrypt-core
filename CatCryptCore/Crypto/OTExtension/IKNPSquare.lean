/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OTExtension.IKNP
public import CatCryptCore.Crypto.UCOracleGame
public import CatCryptCore.Crypto.UCChannel
public import CatCryptCore.Crypto.UCParallel

/-!
# The IKNP OT extension over ideal base OTs as squares against `F_OT^m`

**Ideal functionality.** `F_OT^m` (`fotSendSys`, `fotRecvSys`) carries `m` parallel
1-out-of-2 oblivious transfers of messages in `M`. Its state holds the sender's message pairs,
once given, and whether the receiver has obtained its output. A sender activation keeps the first
message pairs and tells the sender whether the receiver has obtained its output. A receiver
activation with choices `r`, the first after the message pairs are given, outputs the chosen
messages `otChoose x r`; every other receiver activation outputs nothing. Each corruption case
places the corrupt party on the adversary port: `FOTr` (corrupt receiver) has the sender on the
honest port and the receiver on the adversary port, `FOTs` (corrupt sender) the receiver on the
honest port and the sender on the adversary port. Both are port-typed (`Sys.ofPorts`).

**Real protocol.** IKNP (`CatCryptCore.Crypto.OTExtension.IKNP`) over ideal base OTs: the base
OTs give the sender the columns of `T + r · s` for the receiver's matrix `T` and the sender's
secret `s`. The randomness `(T, s)` is drawn at the first activation that runs the protocol
(`KeyedSys.lazy`). Against a corrupt receiver (`realR`), the receiver activation that completes
the inputs outputs the receiver's view (its matrix and the masked message pairs) and its output.
Against a corrupt sender (`realS`), the receiver activation that completes the inputs outputs the
receiver's output to the honest port, and the next sender activation outputs the sender's view
(its secret and its columns).

**Simulators.** Each simulator forwards the honest port and acts on the adversary port only
(`postSim`), so it never reads an honest input or output. `iknpSimRecv` (corrupt receiver)
completes the chosen messages from `F_OT^m` into a receiver view by `iknpSimR`; `iknpSimSend`
(corrupt sender) samples a sender view by `iknpSimS` at the first sender activation after
`F_OT^m` reports delivery. Both are opaque for the view that relates all honest values and
compares adversary values (`hidView.sum eqView`).

**Proof.** Against a corrupt receiver, the hop from IKNP to the system with uniform pads at the
unchosen positions (`crR`) is the correlation-robust hash game of `iknp_sendPriv_le`: the run
depends on `(T, s)` only through `T` and the hashes `H j (T j + s)` (`iknpRView_eq`), the
lazy draw moves to the start of the run (`KeyedSys.view_lazy`), and the bound is the advantage
of the explicit reduction `iknpEnvCRRed H Z`. The uniform pads couple with the simulator at the
activation that draws them (`iknpSenderMsg_otChoose`, a shift of the uniform pads). Against a
corrupt sender, the receiver's output is `otChoose x r` (`iknpRecvOut_otChoose`), the draw of
`(T, s)` moves to the sender activation that reveals the view, and the columns of `T + r · s`
are uniform: distance `0`, the receiver-privacy hop of `iknp_recvPriv_eq` with ideal base OTs.

## Main definitions

* `fotSendSys`, `fotRecvSys`, `FOTr`, `FOTs` — the ideal functionality `F_OT^m`.
* `realR`, `realS` — IKNP over ideal base OTs, corrupt receiver and corrupt sender.
* `postSim`, `iknpSimRecv`, `iknpSimSend` — the simulators.
* `iknpEnvCRRed` — the reduction of an environment to the correlation-robust hash game.

## Main results

* `FOTr_portTyped`, `FOTs_portTyped` — `F_OT^m` answers each event on the port of the event.
* `iknp_realizesSim_corruptReceiver` — against a corrupt receiver, IKNP realizes `FOTr` behind
  `iknpSimRecv` with bound `CRHash_Advantage H (iknpEnvCRRed H Z)`.
* `iknp_realizesSim_corruptSender` — against a corrupt sender, IKNP realizes `FOTs` behind
  `iknpSimSend` at distance `0`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.OT.IKNPSquare

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open CatCrypt.Crypto.UCTransparent CatCrypt.NonUniform CatCrypt.Relational
open scoped ENNReal

variable {κ m : ℕ} {M : Type}

/-! ## The ideal functionality `F_OT^m` -/

/-- The state of `F_OT^m`: the sender's message pairs once given, and whether the receiver has
obtained its output. -/
abbrev FOTState (m : ℕ) (M : Type) := Option (Fin m → M × M) × Bool

/-- A receiver activation: at the first one after the message pairs `x` are given, the output
`v x` and the receiver marked served; otherwise no output. -/
def recvStep {V : Type} (t : FOTState m M) (v : (Fin m → M × M) → V) :
    FOTState m M × Option V :=
  match t with
  | (some x, false) => ((some x, true), some (v x))
  | _ => (t, none)

/-- The sender activation of `F_OT^m`: the first message pairs are kept, and the sender learns
whether the receiver has obtained its output. -/
def fotSend (t : FOTState m M) (x : Fin m → M × M) : FOTState m M × Bool :=
  ((some (t.1.getD x), t.2), t.2)

/-- The sender port of `F_OT^m`. -/
noncomputable def fotSendSys : Sys (FOTState m M) (Fin m → M × M) Bool where
  init := (none, false)
  step t x := SPComp.pure (fotSend t x)

/-- The receiver port of `F_OT^m`: the receiver with choices `r` obtains `otChoose x r`. -/
noncomputable def fotRecvSys : Sys (FOTState m M) (Fin m → Bool) (Option (Fin m → M)) where
  init := (none, false)
  step t r := SPComp.pure (recvStep t fun x => otChoose x r)

/-- **`F_OT^m` against a corrupt receiver**: the sender on the honest port, the receiver on the
adversary port. -/
noncomputable def FOTr :
    Sys (FOTState m M) ((Fin m → M × M) ⊕ (Fin m → Bool)) (Bool ⊕ Option (Fin m → M)) :=
  Sys.ofPorts fotSendSys fotRecvSys

/-- **`F_OT^m` against a corrupt sender**: the receiver on the honest port, the sender on the
adversary port. -/
noncomputable def FOTs :
    Sys (FOTState m M) ((Fin m → Bool) ⊕ (Fin m → M × M)) (Option (Fin m → M) ⊕ Bool) :=
  Sys.ofPorts fotRecvSys fotSendSys

/-- `FOTr` answers each event on the port of the event. -/
theorem FOTr_portTyped : (FOTr (m := m) (M := M)).PortTyped :=
  Sys.ofPorts_portTyped _ _

/-- `FOTs` answers each event on the port of the event. -/
theorem FOTs_portTyped : (FOTs (m := m) (M := M)).PortTyped :=
  Sys.ofPorts_portTyped _ _

/-! ## Simulators on the adversary port -/

/-- The view that relates all events and all outputs: the view of a port that carries honest
values only. -/
def hidView {E O : Type} : PubView E O where
  ev _ _ := True
  out _ _ := True

/-- The simulator on an adversary port: it forwards the event to its subroutine, keeping the
event for the answer, and maps the answer with `post` from its persistent state and the event. -/
noncomputable def postSim {σ E O OG : Type} (s₀ : σ) (post : σ → Option E → OG → SPComp (σ × O))
    (hpost : ∀ s e o, SPComp.NoFail (post s e o)) : MultiHybrid (σ × Option E) E O E OG where
  init := (s₀, none)
  fuel := 0
  start s e := SPComp.pure ((s.1, some e), .inl e)
  resume s o := SPComp.map (fun p => ((p.1, none), .inr p.2)) (post s.1 s.2 o)
  finish s o := SPComp.map (fun p => ((p.1, none), p.2)) (post s.1 s.2 o)
  start_noFail _ _ := SPComp.pure_noFail _
  resume_noFail _ _ := Assumptions.SPComp.bind_noFail (hpost _ _ _) fun _ => SPComp.pure_noFail _
  finish_noFail _ _ := Assumptions.SPComp.bind_noFail (hpost _ _ _) fun _ => SPComp.pure_noFail _

/-- `postSim` is opaque for the equality views. -/
theorem postSim_opaque {σ E O OG : Type} (s₀ : σ) (post : σ → Option E → OG → SPComp (σ × O))
    (hpost : ∀ s e o, SPComp.NoFail (post s e o)) :
    (postSim s₀ post hpost).Opaque PubView.eqView PubView.eqView := by
  refine ⟨Eq, rfl, ?_, ?_, ?_⟩
  · rintro s _ e _ rfl rfl
    exact rHoare_ret fun _ _ h => ⟨h, rfl, PubView.stepRel_eqView _⟩
  · rintro s _ o _ rfl rfl
    exact rHoare_conseq (fun _ _ hh => hh) (fun _ _ _ _ hh => by
      obtain ⟨rfl, rfl⟩ := hh; exact ⟨rfl, rfl, PubView.stepRel_eqView _⟩) (rHoare_refl _)
  · rintro s _ o _ rfl rfl
    exact rHoare_conseq (fun _ _ hh => hh) (fun _ _ _ _ hh => by
      obtain ⟨rfl, rfl⟩ := hh; exact ⟨rfl, rfl, rfl⟩) (rHoare_refl _)

/-- One activation of `postSim` against `X`: one step of `X` on the event, then `post`. -/
theorem postSim_stepFuel {σ E O OG τ : Type} (s₀ : σ)
    (post : σ → Option E → OG → SPComp (σ × O)) (hpost : ∀ s e o, SPComp.NoFail (post s e o))
    (X : Sys τ E OG) (s : σ × Option E) (t : τ) (e : E) :
    (postSim s₀ post hpost).stepFuel X 0 (s, t) e =
      SPComp.bind (X.step t e) fun q =>
        SPComp.map (fun p => (((p.1, none), q.1), p.2)) (post s.1 (some e) q.2) := by
  simp [MultiHybrid.stepFuel, postSim, MultiHybrid.drive, SPComp.map, SPComp.bind_assoc,
    SPComp.pure_bind]

/-- Running `D` after a heap-independent `G` from the heap `h₀` is running `fixHeap h₀ D` after
`G` from the empty heap. -/
theorem prTrue_bind_fixHeap {α : Type} {G : SPComp α} (hG : SPComp.IsPure G)
    (D : α → SPComp Bool) (h₀ : Heap) :
    prTrue (SPComp.bind G D) h₀ = prTrue (SPComp.bind G (fixHeap h₀ D)) Heap.empty := by
  obtain ⟨d, hd⟩ := hG
  unfold prTrue; congr 1; funext h; congr 1
  rw [isPure_bind_expand hd D h₀, isPure_bind_expand hd _ Heap.empty]; rfl

/-! ## Against a corrupt receiver -/

section CorruptReceiver

/-- The randomness of an IKNP execution: the receiver's matrix and the sender's secret. -/
abbrev IKNPKey (κ m : ℕ) := (Fin m → Fin κ → Bool) × (Fin κ → Bool)

/-- The keyed system with the ports of `FOTr` whose receiver activation with choices `r` that
completes the inputs outputs `out k x r` for the key `k` and the message pairs `x`. -/
noncomputable def trigR {K V : Type} (out : K → (Fin m → M × M) → (Fin m → Bool) → V) :
    KeyedSys K (FOTState m M) ((Fin m → M × M) ⊕ (Fin m → Bool)) (Bool ⊕ Option V) where
  init := (none, false)
  step k t := Sum.elim (fun x => SPComp.pure ((fotSend t x).1, .inl (fotSend t x).2))
    fun r => SPComp.pure ((recvStep t (out k · r)).1, .inr (recvStep t (out k · r)).2)
  step₀ t := Sum.elim (fun x => SPComp.pure ((fotSend t x).1, .inl (fotSend t x).2))
    fun _ => match t with
      | (some _, false) => SPComp.fail
      | _ => SPComp.pure (t, .inr none)
  uses t e := e.isRight && t.1.isSome && !t.2

/-- An activation of `trigR out` that does not complete the inputs does not read the key. -/
theorem trigR_hind {K V : Type} (out : K → (Fin m → M × M) → (Fin m → Bool) → V) (k : K)
    (t : FOTState m M) (e : (Fin m → M × M) ⊕ (Fin m → Bool)) (hu : (trigR out).uses t e = false) :
    (trigR out).step k t e = (trigR out).step₀ t e := by
  rcases e with x | r
  · rfl
  · rcases t with ⟨_ | x, _ | _⟩ <;> simp_all [trigR, recvStep]

/-- Every activation of the lazily keyed `trigR out` ends in a state that holds a key only once
the receiver is served. -/
theorem trigR_lazy_pres {K V : Type} (out : K → (Fin m → M × M) → (Fin m → Bool) → V)
    (μ : PMF K) (t : Option K × FOTState m M) (e : (Fin m → M × M) ⊕ (Fin m → Bool))
    (hI : t.1.isSome → t.2.2 = true) :
    ∃ (α : Type) (c : SPComp α) (g : α → (Option K × FOTState m M) × (Bool ⊕ Option V)),
      ((trigR out).lazy μ).step t e = SPComp.bind c (fun a => SPComp.pure (g a)) ∧
        ∀ a, (g a).1.1.isSome → (g a).1.2.2 = true := by
  obtain ⟨ko, t⟩ := t
  rcases e with x | r
  · refine ⟨Unit, SPComp.pure (), fun _ => ((ko, (fotSend t x).1), .inl (fotSend t x).2),
      ?_, fun _ h => hI h⟩
    cases ko <;> simp [KeyedSys.lazy, KeyedSys.lazyStep, trigR, SPComp.pure_bind]
  · rcases t with ⟨_ | x, _ | _⟩ <;> rcases ko with _ | k
    · exact ⟨Unit, SPComp.pure (), fun _ => ((none, (none, false)), .inr none),
        by simp [KeyedSys.lazy, KeyedSys.lazyStep, trigR, SPComp.pure_bind], by simp⟩
    · simp at hI
    · exact ⟨Unit, SPComp.pure (), fun _ => ((none, (none, true)), .inr none),
        by simp [KeyedSys.lazy, KeyedSys.lazyStep, trigR, SPComp.pure_bind], by simp⟩
    · exact ⟨Unit, SPComp.pure (), fun _ => ((some k, (none, true)), .inr none),
        by simp [KeyedSys.lazy, KeyedSys.lazyStep, trigR, recvStep, SPComp.pure_bind], by simp⟩
    · exact ⟨K, sampleFrom (ofPMF μ),
        fun k => ((some k, (some x, true)), .inr (some (out k x r))),
        by simp [KeyedSys.lazy, KeyedSys.lazyStep, trigR, recvStep, SPComp.pure_bind], by simp⟩
    · simp at hI
    · exact ⟨Unit, SPComp.pure (), fun _ => ((none, (some x, true)), .inr none),
        by simp [KeyedSys.lazy, KeyedSys.lazyStep, trigR, SPComp.pure_bind], by simp⟩
    · exact ⟨Unit, SPComp.pure (), fun _ => ((some k, (some x, true)), .inr none),
        by simp [KeyedSys.lazy, KeyedSys.lazyStep, trigR, recvStep, SPComp.pure_bind], by simp⟩

variable [AddCommGroup M]

/-- The view and output of a corrupt receiver in IKNP over ideal base OTs with randomness
`k = (T, s)`: the base OTs give the sender the columns of `T + r · s`, the receiver sees `T` and
the masked message pairs, and outputs its unmasked messages. -/
def iknpRView (H : Fin m → (Fin κ → Bool) → M) (k : IKNPKey κ m) (x : Fin m → M × M)
    (r : Fin m → Bool) : IKNPReceiverView κ m M Unit × (Fin m → M) :=
  ((k.1, (), iknpSenderMsg H x k.2 (otChoose (iknpBaseIn k.1 r) k.2)),
    iknpRecvOut H r k.1 (iknpSenderMsg H x k.2 (otChoose (iknpBaseIn k.1 r) k.2)))

/-- The view of `iknpCRView` with the challenge `th = (T, h)`: the masked message pairs carry
`H j (T j)` at the choice and `h j` at the other position; the output is `otChoose x r`. -/
def crRView (H : Fin m → (Fin κ → Bool) → M) (th : (Fin m → Fin κ → Bool) × (Fin m → M))
    (x : Fin m → M × M) (r : Fin m → Bool) : IKNPReceiverView κ m M Unit × (Fin m → M) :=
  iknpCRView H (x, r, ()) th ()

/-- The corrupt receiver's view in IKNP over ideal base OTs depends on `(T, s)` through `T` and
the hashes `H j (T j + s)`. -/
theorem iknpRView_eq (H : Fin m → (Fin κ → Bool) → M) (T : Fin m → Fin κ → Bool)
    (s : Fin κ → Bool) (x : Fin m → M × M) (r : Fin m → Bool) :
    iknpRView H (T, s) x r = crRView H (T, fun j => H j (T j + s)) x r := by
  simp only [iknpRView, crRView, iknpCRView]
  rw [iknpRecvOut_otChoose, iknpSenderMsg_otChoose]

/-- **IKNP over ideal base OTs against a corrupt receiver.** The randomness `(T, s)` is drawn at
the receiver activation that completes the inputs, which outputs the receiver's view and
output. -/
noncomputable def realR (H : Fin m → (Fin κ → Bool) → M) :
    Sys (Option (IKNPKey κ m) × FOTState m M) ((Fin m → M × M) ⊕ (Fin m → Bool))
      (Bool ⊕ Option (IKNPReceiverView κ m M Unit × (Fin m → M))) :=
  (trigR (iknpRView H)).lazy (PMF.uniformFintype _)

variable [Fintype M] [Nonempty M]

/-- The system with uniform pads at the unchosen positions: `trigR` of `crRView`, with the
challenge drawn uniformly at the receiver activation that completes the inputs. -/
noncomputable def crR (H : Fin m → (Fin κ → Bool) → M) :
    Sys (Option ((Fin m → Fin κ → Bool) × (Fin m → M)) × FOTState m M)
      ((Fin m → M × M) ⊕ (Fin m → Bool))
      (Bool ⊕ Option (IKNPReceiverView κ m M Unit × (Fin m → M))) :=
  (trigR (crRView H)).lazy (PMF.uniformFintype _)

/-- The adversary-port answer of the simulator against a corrupt receiver: the chosen messages
`z` from `F_OT^m`, completed by `iknpSimR` into a receiver view on the choices `r`. -/
noncomputable def simRPost (H : Fin m → (Fin κ → Bool) → M) :
    Unit → Option (Fin m → Bool) → Option (Fin m → M) →
      SPComp (Unit × Option (IKNPReceiverView κ m M Unit × (Fin m → M)))
  | _, some r, some z =>
    SPComp.map (fun v => ((), some (v, z))) (iknpSimR (fun _ => SPComp.pure ()) H r z)
  | _, _, _ => SPComp.pure ((), none)

/-- `simRPost` never fails. -/
theorem simRPost_noFail (H : Fin m → (Fin κ → Bool) → M) (s : Unit) (r : Option (Fin m → Bool))
    (o : Option (Fin m → M)) : SPComp.NoFail (simRPost H s r o) := by
  rcases r with _ | r <;> rcases o with _ | z <;> simp only [simRPost] <;>
    first
    | exact SPComp.pure_noFail _
    | (unfold iknpSimR SPComp.map
       aesop (rule_sets := [CatCryptRel]) (config := { terminal := true }))

/-- The simulator against a corrupt receiver as a multi-call simulator: forwarding on the
sender's port, `simRPost` on the receiver's port. -/
noncomputable def simProtR (H : Fin m → (Fin κ → Bool) → M) :=
  (MultiHybrid.idSim (Fin m → M × M) Bool).tensor (postSim () (simRPost H) (simRPost_noFail H))

/-- **The simulator against a corrupt receiver.** It forwards the honest sender's events and
outputs, and completes the receiver's chosen messages from `F_OT^m` into a receiver view by
`iknpSimR`; it reads no honest value. Opaque for `hidView.sum eqView`. -/
noncomputable def iknpSimRecv (H : Fin m → (Fin κ → Bool) → M) :
    Simulator ((Fin m → M × M) ⊕ (Fin m → Bool))
      (Bool ⊕ Option (IKNPReceiverView κ m M Unit × (Fin m → M)))
      ((Fin m → M × M) ⊕ (Fin m → Bool)) (Bool ⊕ Option (Fin m → M))
      (hidView.sum PubView.eqView) (hidView.sum PubView.eqView) :=
  Simulator.ofMultiHybrid (simProtR H)
    (MultiHybrid.Opaque.tensor (MultiHybrid.idSim_opaque _) (postSim_opaque _ _ _))

/-- **Reduction to correlation-robust hashing.** On a challenge `th`, run the environment `Z`,
from its initial heap, against `trigR (crRView H)` with the key `th`, and output the bit of its
distinguisher. -/
noncomputable def iknpEnvCRRed (H : Fin m → (Fin κ → Bool) → M) {ζ : Type}
    (Z : Env (Strat ζ ((Fin m → M × M) ⊕ (Fin m → Bool))
      (Bool ⊕ Option (IKNPReceiverView κ m M Unit × (Fin m → M)))) ζ) :
    (Fin m → Fin κ → Bool) × (Fin m → M) → SPComp Bool :=
  fixHeap Z.heap fun th => SPComp.bind (view ((trigR (crRView H)).withKey th) Z.input) Z.dist

/-- The draw of the uniform pads in `crRView` is the draw of `iknpSimR` on the chosen
messages. -/
theorem crRView_sample {β : Type} (H : Fin m → (Fin κ → Bool) → M) (x : Fin m → M × M)
    (r : Fin m → Bool) (G : IKNPReceiverView κ m M Unit × (Fin m → M) → β) :
    SPComp.bind (SPComp.sample ((Fin m → Fin κ → Bool) × (Fin m → M)))
        (fun th => SPComp.pure (G (crRView H th x r))) =
      SPComp.bind (iknpSimR (fun _ => SPComp.pure ()) H r (otChoose x r))
        (fun v => SPComp.pure (G (v, otChoose x r))) := by
  rw [SPComp.sample_prod_eq]
  simp only [iknpSimR, SPComp.bind_assoc, SPComp.pure_bind]
  congr 1; funext T
  rw [← SPComp.sample_bind_equiv (Equiv.addLeft fun j => -if r j then (x j).1 else (x j).2)]
  congr 1; funext h
  congr 2
  simp only [crRView, iknpCRView, Equiv.coe_addLeft, Pi.add_apply, Prod.mk.injEq, true_and]
  refine ⟨funext fun j => ?_, trivial⟩
  by_cases hr : r j <;> simp [hr, otChoose]

/-- Hop 1: IKNP against a corrupt receiver realizes `crR`, with bound the correlation-robust
hash advantage of `iknpEnvCRRed H Z`. -/
theorem realR_realizes_crR (H : Fin m → (Fin κ → Bool) → M) :
    Realizes (realR H) (crR H) fun _ Z => CRHash_Advantage H (iknpEnvCRRed H Z) := by
  intro ζ Z
  have hk : ∀ T s, (trigR (iknpRView H)).withKey (T, s) =
      (trigR (crRView H)).withKey (T, fun j => H j (T j + s)) := by
    intro T s
    simp only [KeyedSys.withKey, trigR, iknpRView_eq]
  have hr : ∀ Zs : Strat ζ _ _, view (realR H) Zs =
      SPComp.bind (crHashReal H) fun th => view ((trigR (crRView H)).withKey th) Zs := by
    intro Zs
    rw [realR, KeyedSys.view_lazy _ _ (trigR_hind _) Zs, ofPMF_uniformFintype, sampleFrom_uniform,
      SPComp.sample_prod_eq]
    simp only [crHashReal, SPComp.bind_assoc, SPComp.pure_bind, hk]
  have hi : ∀ Zs : Strat ζ _ _, view (crR H) Zs =
      SPComp.bind crHashIdeal fun th => view ((trigR (crRView H)).withKey th) Zs := by
    intro Zs
    rw [crR, KeyedSys.view_lazy _ _ (trigR_hind _) Zs, ofPMF_uniformFintype, sampleFrom_uniform,
      SPComp.sample_prod_eq]
    simp only [crHashIdeal, SPComp.bind_assoc, SPComp.pure_bind]
  change absDiff _ _ ≤ _
  rw [hr, hi, SPComp.bind_assoc, SPComp.bind_assoc,
    prTrue_bind_fixHeap (G := crHashReal H) (by
      unfold crHashReal; aesop (rule_sets := [CatCryptRel]) (config := { terminal := true }))
      _ Z.heap,
    prTrue_bind_fixHeap (G := crHashIdeal) (by
      unfold crHashIdeal; aesop (rule_sets := [CatCryptRel]) (config := { terminal := true }))
      _ Z.heap]
  exact le_rfl

/-- Hop 2: `crR` realizes the simulator against a corrupt receiver over `FOTr` at distance `0`:
the uniform pads couple with the draw of `iknpSimR` at the activation that draws them. -/
theorem crR_realizes_sim (H : Fin m → (Fin κ → Bool) → M) :
    Realizes (crR H) ((simProtR H).withSub FOTr) fun _ _ => 0 := by
  refine realizes_zero_of_stepMap_on _ _ (fun t => t.1.isSome → t.2.2 = true)
    (fun t => (((), ((), none)), t.2)) (by simp [crR, KeyedSys.lazy, trigR]) rfl
    (fun t e hI => trigR_lazy_pres _ _ t e hI) ?_
  rintro ⟨ko, t⟩ (x | r) hI
  · rw [simProtR, MultiHybrid.tensor_withSub_step_inl _ _ FOTr fotSendSys (fun _ _ => rfl),
      MultiHybrid.idSim_stepFuel]
    cases ko <;> simp [crR, KeyedSys.lazy, KeyedSys.lazyStep, trigR, fotSendSys, SPComp.map,
      SPComp.pure_bind]
  · rw [simProtR, MultiHybrid.tensor_withSub_step_inr _ _ FOTr fotRecvSys (fun _ _ => rfl)]
    change SPComp.map _ _ = SPComp.map _ ((postSim () (simRPost H) _).stepFuel _ 0 _ _)
    rw [postSim_stepFuel]
    rcases t with ⟨_ | x, _ | _⟩ <;> rcases ko with _ | k
    case some.false.none =>
      simp only [crR, KeyedSys.lazy, KeyedSys.lazyStep, trigR, fotRecvSys, recvStep, simRPost,
        SPComp.map, SPComp.bind_assoc, SPComp.pure_bind, Sum.isRight_inr, Option.isSome_some,
        Bool.not_false, Bool.and_self, ite_true, Sum.elim_inr, ofPMF_uniformFintype,
        sampleFrom_uniform]
      exact crRView_sample H x r fun w => ((((), (), none), some x, true), Sum.inr (some w))
    all_goals first
      | (simp at hI; done)
      | simp [crR, KeyedSys.lazy, KeyedSys.lazyStep, trigR, fotRecvSys, recvStep, simRPost,
          SPComp.map, SPComp.pure_bind]

/-- **IKNP against a corrupt receiver as a square.** Ideal functionality: `FOTr`, `F_OT^m` with
the sender on the honest port and the receiver on the adversary port. Real protocol: `realR H`,
IKNP over ideal base OTs, which reveals the receiver's view (its matrix and the masked message
pairs) and output. Simulator: `iknpSimRecv H`, which completes the chosen messages into a
receiver view by `iknpSimR` and reads no honest value. Bound: the correlation-robust hash
advantage of the explicit reduction `iknpEnvCRRed H Z` of the environment. Corrupt receiver,
one transfer of `m` message pairs. -/
theorem iknp_realizesSim_corruptReceiver (H : Fin m → (Fin κ → Bool) → M) :
    RealizesSim (realR H) FOTr (iknpSimRecv H) fun _ Z => CRHash_Advantage H (iknpEnvCRRed H Z) :=
  fun ζ Z =>
    le_of_le_of_eq ((Realizes.trans (realR_realizes_crR H) (crR_realizes_sim H)) ζ Z)
      (add_zero _)

end CorruptReceiver

/-! ## Against a corrupt sender -/

section CorruptSender

variable [AddCommGroup M]

/-- The state of IKNP against a corrupt sender: the sender's message pairs once given, the
receiver's choices once the receiver is served, and whether the sender's view is revealed. -/
abbrev SState (m : ℕ) (M : Type) :=
  Option (Fin m → M × M) × Option (Fin m → Bool) × Bool

/-- The honest receiver's activation with choices `r`: at the first one after the message pairs
`x` are given, the choices are kept and the receiver outputs `z x`; otherwise no output. -/
def sRecv (t : SState m M) (r : Fin m → Bool) (z : (Fin m → M × M) → Fin m → M) :
    SState m M × Option (Fin m → M) :=
  match t with
  | (some x, none, d) => ((some x, some r, d), some (z x))
  | _ => (t, none)

/-- The corrupt sender's activation with message pairs `x`: the first message pairs are kept;
at the first activation after the receiver is served, the view `v r` is revealed. -/
def sSend {V : Type} (t : SState m M) (x : Fin m → M × M) (v : (Fin m → Bool) → V) :
    SState m M × Option V :=
  match t with
  | (xo, some r, false) => ((some (xo.getD x), some r, true), some (v r))
  | (xo, ro, d) => ((some (xo.getD x), ro, d), none)

/-- The view of a corrupt sender in IKNP over ideal base OTs with randomness `k = (T, s)` and the
receiver's choices `r`: its secret `s` and the columns of `T + r · s` from the base OTs. -/
def iknpSView (k : IKNPKey κ m) (r : Fin m → Bool) : IKNPSenderView κ m Unit :=
  (k.2, (), otChoose (iknpBaseIn k.1 r) k.2)

/-- The output of the receiver in IKNP over ideal base OTs with randomness `k = (T, s)`. -/
def iknpROut (H : Fin m → (Fin κ → Bool) → M) (k : IKNPKey κ m) (x : Fin m → M × M)
    (r : Fin m → Bool) : Fin m → M :=
  iknpRecvOut H r k.1 (iknpSenderMsg H x k.2 (otChoose (iknpBaseIn k.1 r) k.2))

/-- The receiver's output in IKNP over ideal base OTs is the chosen messages. -/
theorem iknpROut_eq (H : Fin m → (Fin κ → Bool) → M) (k : IKNPKey κ m) (x : Fin m → M × M)
    (r : Fin m → Bool) : iknpROut H k x r = otChoose x r :=
  iknpRecvOut_otChoose H x k.1 r k.2

/-- IKNP against a corrupt sender as a keyed system with the ports of `FOTs`, with the key
`k = (T, s)`. The key is drawn at the receiver activation that completes the inputs when
`early` holds, and at the sender activation that reveals the view otherwise. -/
noncomputable def trigS (H : Fin m → (Fin κ → Bool) → M) (early : Bool) :
    KeyedSys (IKNPKey κ m) (SState m M) ((Fin m → Bool) ⊕ (Fin m → M × M))
      (Option (Fin m → M) ⊕ Option (IKNPSenderView κ m Unit)) where
  init := (none, none, false)
  step k t := Sum.elim
    (fun r => SPComp.pure ((sRecv t r (iknpROut H k · r)).1, .inl (sRecv t r (iknpROut H k · r)).2))
    fun x => SPComp.pure ((sSend t x (iknpSView k)).1, .inr (sSend t x (iknpSView k)).2)
  step₀ t := Sum.elim
    (fun r => SPComp.pure ((sRecv t r (otChoose · r)).1, .inl (sRecv t r (otChoose · r)).2))
    fun x => match t with
      | (_, some _, false) => SPComp.fail
      | (xo, ro, d) => SPComp.pure ((some (xo.getD x), ro, d), .inr none)
  uses t e := Sum.elim (fun _ => early && t.1.isSome && t.2.1.isNone)
    (fun _ => t.2.1.isSome && !t.2.2) e

/-- An activation of `trigS H early` that does not reveal the sender's view does not depend on
the key. -/
theorem trigS_hind (H : Fin m → (Fin κ → Bool) → M) (early : Bool) (k : IKNPKey κ m)
    (t : SState m M) (e : (Fin m → Bool) ⊕ (Fin m → M × M))
    (hu : (trigS H early).uses t e = false) :
    (trigS H early).step k t e = (trigS H early).step₀ t e := by
  rcases e with r | x
  · simp only [trigS, Sum.elim_inl, iknpROut_eq]
  · rcases t with ⟨xo, _ | r, _ | _⟩ <;> simp_all [trigS, sSend]

/-- **IKNP over ideal base OTs against a corrupt sender.** The randomness `(T, s)` is drawn at
the receiver activation that completes the inputs, which outputs the receiver's output to the
honest port; the next sender activation reveals the sender's view. -/
noncomputable def realS (H : Fin m → (Fin κ → Bool) → M) :
    Sys (Option (IKNPKey κ m) × SState m M) ((Fin m → Bool) ⊕ (Fin m → M × M))
      (Option (Fin m → M) ⊕ Option (IKNPSenderView κ m Unit)) :=
  (trigS H true).lazy (PMF.uniformFintype _)

/-- Every activation of the lazily keyed `trigS H false` ends in a state that holds a key only
once the sender's view is revealed. -/
theorem trigS_lazy_pres (H : Fin m → (Fin κ → Bool) → M) (t : Option (IKNPKey κ m) × SState m M)
    (e : (Fin m → Bool) ⊕ (Fin m → M × M)) (hI : t.1.isSome → t.2.2.2 = true) :
    ∃ (α : Type) (c : SPComp α)
      (g : α → (Option (IKNPKey κ m) × SState m M) ×
        (Option (Fin m → M) ⊕ Option (IKNPSenderView κ m Unit))),
      ((trigS H false).lazy (PMF.uniformFintype _)).step t e =
          SPComp.bind c (fun a => SPComp.pure (g a)) ∧
        ∀ a, (g a).1.1.isSome → (g a).1.2.2.2 = true := by
  obtain ⟨ko, t⟩ := t
  rcases e with r | x
  · refine ⟨Unit, SPComp.pure (), fun _ =>
      ((ko, (sRecv t r (otChoose · r)).1), .inl (sRecv t r (otChoose · r)).2), ?_, fun _ h => ?_⟩
    · cases ko <;> simp [KeyedSys.lazy, KeyedSys.lazyStep, trigS, iknpROut_eq, SPComp.pure_bind]
    · rcases t with ⟨_ | _, _ | _, _⟩ <;> exact hI h
  · rcases t with ⟨xo, _ | r, _ | _⟩
    · rcases ko with _ | k
      · exact ⟨Unit, SPComp.pure (), fun _ => ((none, (some (xo.getD x), none, false)), .inr none),
          by simp [KeyedSys.lazy, KeyedSys.lazyStep, trigS, SPComp.pure_bind], by simp⟩
      · simp at hI
    · exact ⟨Unit, SPComp.pure (), fun _ => ((ko, (some (xo.getD x), none, true)), .inr none),
        by cases ko <;> simp [KeyedSys.lazy, KeyedSys.lazyStep, trigS, sSend, SPComp.pure_bind],
        by simp⟩
    · rcases ko with _ | k
      · exact ⟨_, sampleFrom (ofPMF (PMF.uniformFintype (IKNPKey κ m))),
          fun k => ((some k, (some (xo.getD x), some r, true)), .inr (some (iknpSView k r))),
          by simp [KeyedSys.lazy, KeyedSys.lazyStep, trigS, sSend, SPComp.pure_bind], by simp⟩
      · simp at hI
    · exact ⟨Unit, SPComp.pure (), fun _ => ((ko, (some (xo.getD x), some r, true)), .inr none),
        by cases ko <;> simp [KeyedSys.lazy, KeyedSys.lazyStep, trigS, sSend, SPComp.pure_bind],
        by simp⟩

/-- Hop 1: drawing `(T, s)` at the receiver activation and at the sender activation that reveals
the view give the same views: the receiver's output does not depend on `(T, s)`
(`iknpROut_eq`). -/
theorem realS_realizes_late (H : Fin m → (Fin κ → Bool) → M) :
    Realizes (realS H) ((trigS H false).lazy (PMF.uniformFintype _)) fun _ _ => 0 := by
  intro ζ Z
  have hv : view (realS H) Z.input =
      view ((trigS H false).lazy (PMF.uniformFintype _)) Z.input := by
    rw [realS, KeyedSys.view_lazy _ _ (trigS_hind H true),
      KeyedSys.view_lazy _ _ (trigS_hind H false)]
    rfl
  simp [Env.gap, hv]

/-- The adversary-port answer of the simulator against a corrupt sender: at the first sender
activation after `F_OT^m` reports that the receiver is served, a sender view by `iknpSimS`;
otherwise nothing. The persistent state records whether the view is revealed. -/
noncomputable def simSPost :
    Bool → Option (Fin m → M × M) → Bool →
      SPComp (Bool × Option (IKNPSenderView κ m Unit))
  | false, some x, true =>
    SPComp.map (fun v => (true, some v)) (iknpSimS (fun _ _ => SPComp.pure ()) x)
  | d, _, _ => SPComp.pure (d, none)

omit [AddCommGroup M] in
/-- `simSPost` never fails. -/
theorem simSPost_noFail (d : Bool) (x : Option (Fin m → M × M)) (b : Bool) :
    SPComp.NoFail (simSPost (κ := κ) d x b) := by
  rcases d with _ | _ <;> rcases x with _ | x <;> rcases b with _ | _ <;> simp only [simSPost] <;>
    first
    | exact SPComp.pure_noFail _
    | (unfold iknpSimS SPComp.map
       aesop (rule_sets := [CatCryptRel]) (config := { terminal := true }))

/-- The simulator against a corrupt sender as a multi-call simulator: forwarding on the
receiver's port, `simSPost` on the sender's port. -/
noncomputable def simProtS :
    MultiHybrid (Unit × (Bool × Option (Fin m → M × M))) ((Fin m → Bool) ⊕ (Fin m → M × M))
      (Option (Fin m → M) ⊕ Option (IKNPSenderView κ m Unit))
      ((Fin m → Bool) ⊕ (Fin m → M × M)) (Option (Fin m → M) ⊕ Bool) :=
  (MultiHybrid.idSim (Fin m → Bool) (Option (Fin m → M))).tensor
    (postSim false (simSPost (κ := κ) (m := m) (M := M)) simSPost_noFail)

omit [AddCommGroup M] in
/-- `simProtS` is opaque for the view that relates honest values and compares adversary
values. -/
theorem simProtS_opaque :
    (simProtS (κ := κ) (m := m) (M := M)).Opaque (hidView.sum PubView.eqView)
      (hidView.sum PubView.eqView) :=
  MultiHybrid.Opaque.tensor (MultiHybrid.idSim_opaque _) (postSim_opaque _ _ _)

/-- **The simulator against a corrupt sender.** It forwards the honest receiver's events and
outputs, and at the first sender activation after `F_OT^m` reports that the receiver is served
it reveals a sender view drawn by `iknpSimS`; it reads no honest value. Opaque for
`hidView.sum eqView`. -/
noncomputable def iknpSimSend :
    Simulator ((Fin m → Bool) ⊕ (Fin m → M × M))
      (Option (Fin m → M) ⊕ Option (IKNPSenderView κ m Unit))
      ((Fin m → Bool) ⊕ (Fin m → M × M)) (Option (Fin m → M) ⊕ Bool)
      (hidView.sum PubView.eqView) (hidView.sum PubView.eqView) :=
  Simulator.ofMultiHybrid simProtS simProtS_opaque

omit [AddCommGroup M] in
/-- The draw of `(T, s)` in the corrupt sender's view is the draw of `iknpSimS`: the columns of
`T + r · s` are uniform. -/
theorem iknpSView_sample {β : Type} (x : Fin m → M × M) (r : Fin m → Bool)
    (G : IKNPSenderView κ m Unit → β) :
    SPComp.bind (SPComp.sample (IKNPKey κ m)) (fun k => SPComp.pure (G (iknpSView k r))) =
      SPComp.bind (iknpSimS (fun _ _ => SPComp.pure ()) x) (fun v => SPComp.pure (G v)) := by
  rw [SPComp.sample_prod_eq]
  simp only [iknpSimS, iknpSView, SPComp.bind_assoc, SPComp.pure_bind, otChoose_iknpBaseIn]
  rw [SPComp.isPure_bind_comm (SPComp.sample (Fin m → Fin κ → Bool))
    (SPComp.sample (Fin κ → Bool)) _ (SPComp.sample_isPure _) (SPComp.sample_isPure _)]
  congr 1; funext s
  exact SPComp.sample_bind_equiv (Equiv.addRight (iknpShift r s))
    fun T => SPComp.pure (G (s, (), fun i j => T j i))

/-- Hop 2: IKNP with `(T, s)` drawn at the sender activation that reveals the view realizes the
simulator against a corrupt sender over `FOTs` at distance `0`: the receiver's output is
`otChoose x r`, and the revealed view couples with the draw of `iknpSimS`. -/
theorem late_realizes_sim (H : Fin m → (Fin κ → Bool) → M) :
    Realizes ((trigS H false).lazy (PMF.uniformFintype _)) (simProtS.withSub FOTs)
      fun _ _ => 0 := by
  refine realizes_zero_of_stepMap_on _ _ (fun t => t.1.isSome → t.2.2.2 = true)
    (fun t => (((), (t.2.2.2, none)), (t.2.1, t.2.2.1.isSome)))
    (by simp [KeyedSys.lazy, trigS]) rfl (fun t e hI => trigS_lazy_pres H t e hI) ?_
  rintro ⟨ko, t⟩ (r | x) hI
  · rw [simProtS, MultiHybrid.tensor_withSub_step_inl _ _ FOTs fotRecvSys (fun _ _ => rfl),
      MultiHybrid.idSim_stepFuel]
    rcases t with ⟨_ | x, _ | r₀, _ | _⟩ <;> rcases ko with _ | k <;>
      simp [KeyedSys.lazy, KeyedSys.lazyStep, trigS, sRecv, fotRecvSys, recvStep, iknpROut_eq,
        SPComp.map, SPComp.pure_bind]
  · rw [simProtS, MultiHybrid.tensor_withSub_step_inr _ _ FOTs fotSendSys (fun _ _ => rfl)]
    change SPComp.map _ _ = SPComp.map _ ((postSim false simSPost _).stepFuel _ 0 _ _)
    rw [postSim_stepFuel]
    rcases t with ⟨xo, _ | r, _ | _⟩ <;> rcases ko with _ | k
    case some.false.none =>
      simp only [KeyedSys.lazy, KeyedSys.lazyStep, trigS, sSend, fotSendSys, fotSend,
        simSPost, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind, Sum.elim_inr,
        Option.isSome_some, Bool.not_false, Bool.and_self, ite_true, ofPMF_uniformFintype,
        sampleFrom_uniform]
      exact iknpSView_sample x r fun v =>
        ((((), true, none), some (xo.getD x), true), Sum.inr (some v))
    all_goals first
      | (simp at hI; done)
      | simp [KeyedSys.lazy, KeyedSys.lazyStep, trigS, sSend, fotSendSys, fotSend, simSPost,
          SPComp.map, SPComp.pure_bind]

/-- **IKNP against a corrupt sender as a square.** Ideal functionality: `FOTs`, `F_OT^m` with
the receiver on the honest port and the sender on the adversary port. Real protocol:
`realS H`, IKNP over ideal base OTs, which gives the receiver its output and reveals the
sender's view (its secret and its columns from the base OTs) at the next sender activation.
Simulator: `iknpSimSend`, which draws a sender view by `iknpSimS` once `F_OT^m` reports that the
receiver is served, and reads no honest value. Distance `0`. Corrupt sender, one transfer of
`m` message pairs. -/
theorem iknp_realizesSim_corruptSender (H : Fin m → (Fin κ → Bool) → M) :
    RealizesSim (realS H) FOTs iknpSimSend fun _ _ => 0 :=
  fun ζ Z =>
    le_of_le_of_eq ((Realizes.trans (realS_realizes_late H) (late_realizes_sim H)) ζ Z)
      (add_zero _)

end CorruptSender

end CatCrypt.Crypto.OT.IKNPSquare
