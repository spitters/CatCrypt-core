/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCParallel
public import CatCryptCore.Crypto.ChannelCap

/-!
# The ideal channel with a capability

The system `Sys.ofPorts KL KR` has one state shared by two sub-systems, `KL` on the left port
and `KR` on the right port; it answers every event on the port of the event
(`Sys.ofPorts_portTyped`), and it is opaque for the sum of two views when both sub-systems have
unwinding conditions for the same relation of states (`Sys.Opaque.ofPorts`).

The equality view `PubView.eqView` relates equal events and equal outputs. Every multi-call
simulator is opaque for it (`MultiHybrid.opaque_eqView`): a simulator that sees only the
adversary port leaks nothing about honest values, because honest values never reach it.

The ideal channel `FChan cap ℓ` with the capability `cap` and the leakage `ℓ` is a system of
this form. On the honest port, `send v` appends `v` to the queue of messages in transit and
`recv` takes the first delivered message from the inbox. On the adversary port, `poll` returns
the observation `cap.wireLeak ℓ m` of the next message `m` the adversary has not yet been shown
and advances a cursor; `deliver` moves the head of the queue to the inbox; `drop` removes it
and `tamper v` replaces it by `v` in the inbox, each only when `cap` grants the power and
otherwise without effect; `idle` changes nothing (`FChan_idleAt`). The adversary pulls each
observation with `poll`, which makes the channel answer every event on its port and gives the
idle event; the alternative is to push the observation as the output of `send`, which places
adversary-directed output on the honest port.

Honest sends with the same observation are related by the honest view `honView cap ℓ`, and the
channel is opaque for `(honView cap ℓ).sum eqView` (`FChan_opaque`): the adversary port shows
exactly what the capability lets the adversary read.

The capability order gives cells: for `c₁ ≤ c₂` the channel `FChan c₁ ℓ` realizes
`FChan c₂ ℓ` at distance `0` behind the tensor of the forwarding simulator on the honest port
with `capSim c₁ ℓ` on the adversary port (`FChan_realizes_of_le`). The simulator `capSim c₁ ℓ`
replaces a `drop` or `tamper` that `c₁` does not grant by `idle`, and turns a plaintext
observation into its leakage when `c₁` does not grant reading.

## Main definitions

* `Sys.ofPorts`: one shared state, one sub-system per port.
* `PubView.eqView`: the equality view.
* `ChanHEv`, `ChanHOut`, `ChanAEv`, `ChanAOut`, `ChanSt`: the ports and the state of the
  channel.
* `FChan cap ℓ`: the ideal channel.
* `honView cap ℓ`: the view of the honest port.
* `capSim c₁ ℓ`: the simulator of the capability order.

## Main results

* `Sys.ofPorts_portTyped`, `Sys.Opaque.ofPorts`.
* `MultiHybrid.opaque_eqView`, `Sys.opaque_eqView`.
* `FChan_portTyped`, `FChan_idleAt`, `FChan_opaque`.
* `FChan_realizes_of_le`: the cell of the capability order.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open CatCrypt.Relational
open CatCrypt.Crypto.Choreography (ChannelCap)
open scoped ENNReal

/-! ## One shared state, one sub-system per port -/

namespace Sys

variable {τ E O E' O' : Type}

/-- The system with the state of `KL` and `KR`, which steps as `KL` on a left event and as `KR`
on a right event, the output on the port of the event. The initial state is that of `KL`. -/
noncomputable def ofPorts (KL : Sys τ E O) (KR : Sys τ E' O') : Sys τ (E ⊕ E') (O ⊕ O') where
  init := KL.init
  step t := Sum.elim (fun e => SPComp.map (fun q => (q.1, .inl q.2)) (KL.step t e))
    (fun e => SPComp.map (fun q => (q.1, .inr q.2)) (KR.step t e))

/-- Unfolding lemma of `Sys.ofPorts`: a step on a left event. -/
@[simp] theorem ofPorts_step_inl (KL : Sys τ E O) (KR : Sys τ E' O') (t : τ) (e : E) :
    (ofPorts KL KR).step t (.inl e) = SPComp.map (fun q => (q.1, .inl q.2)) (KL.step t e) :=
  rfl

/-- Unfolding lemma of `Sys.ofPorts`: a step on a right event. -/
@[simp] theorem ofPorts_step_inr (KL : Sys τ E O) (KR : Sys τ E' O') (t : τ) (e : E') :
    (ofPorts KL KR).step t (.inr e) = SPComp.map (fun q => (q.1, .inr q.2)) (KR.step t e) :=
  rfl

/-- The system of two sub-systems answers every event on the port of the event. -/
theorem ofPorts_portTyped (KL : Sys τ E O) (KR : Sys τ E' O') : (ofPorts KL KR).PortTyped :=
  ⟨KL, KR, fun _ _ => rfl, fun _ _ => rfl⟩

/-- Unwinding conditions of the two sub-systems for one relation of states give the unwinding
condition of the system of the two sub-systems for the sum of the views. -/
theorem Unwinding.ofPorts {KL : Sys τ E O} {KR : Sys τ E' O'} {VL : PubView E O}
    {VR : PubView E' O'} {T : τ → τ → Prop} (hL : KL.Unwinding VL T) (hR : KR.Unwinding VR T) :
    (ofPorts KL KR).Unwinding (VL.sum VR) T := by
  refine ⟨hL.init, fun t t' e e' ht he => ?_⟩
  cases he with
  | inl he =>
    rw [ofPorts_step_inl, ofPorts_step_inl]
    exact rHoare_bind (hL.step t t' _ _ ht he) fun _ _ =>
      rHoare_ret fun _ _ hp => ⟨hp.1, hp.2.1, Sum.LiftRel.inl hp.2.2⟩
  | inr he =>
    rw [ofPorts_step_inr, ofPorts_step_inr]
    exact rHoare_bind (hR.step t t' _ _ ht he) fun _ _ =>
      rHoare_ret fun _ _ hp => ⟨hp.1, hp.2.1, Sum.LiftRel.inr hp.2.2⟩

/-- **Opacity of a system of two sub-systems**: unwinding conditions of the two sub-systems for
one relation of states give opacity for the sum of the views. -/
theorem Opaque.ofPorts {KL : Sys τ E O} {KR : Sys τ E' O'} {VL : PubView E O}
    {VR : PubView E' O'} {T : τ → τ → Prop} (hL : KL.Unwinding VL T)
    (hR : KR.Unwinding VR T) : (ofPorts KL KR).Opaque (VL.sum VR) :=
  ⟨T, hL.ofPorts hR⟩

end Sys

/-! ## The equality view -/

namespace PubView

variable {E O EG OG : Type}

/-- The equality view: equal events and equal outputs. -/
def eqView : PubView E O where
  ev := Eq
  out := Eq

/-- Equal decisions are related for the equality views. -/
theorem stepRel_eqView (d : EG ⊕ O) :
    StepRel (eqView : PubView E O) (eqView : PubView EG OG) d d := by
  cases d <;> rfl

end PubView

open PubView (eqView)

/-- Every system is opaque for the equality view. -/
theorem Sys.opaque_eqView {τ E O : Type} (X : Sys τ E O) : X.Opaque eqView := by
  refine ⟨Eq, rfl, ?_⟩
  rintro t _ e _ rfl rfl
  exact rHoare_conseq (fun _ _ h => h)
    (fun _ _ _ _ hp => by obtain ⟨rfl, rfl⟩ := hp; exact ⟨rfl, rfl, rfl⟩) (rHoare_refl _)

/-- **Every multi-call simulator is opaque for the equality views**, with the equality of
states as unwinding relation. -/
theorem MultiHybrid.opaque_eqView {σ E O EG OG : Type} (π : MultiHybrid σ E O EG OG) :
    π.Opaque eqView eqView := by
  refine ⟨Eq, rfl, ?_, ?_, ?_⟩
  · rintro s _ e _ rfl rfl
    exact rHoare_conseq (fun _ _ h => h) (fun _ _ _ _ hp => by
      obtain ⟨rfl, rfl⟩ := hp; exact ⟨rfl, rfl, PubView.stepRel_eqView _⟩) (rHoare_refl _)
  · rintro s _ o _ rfl rfl
    exact rHoare_conseq (fun _ _ h => h) (fun _ _ _ _ hp => by
      obtain ⟨rfl, rfl⟩ := hp; exact ⟨rfl, rfl, PubView.stepRel_eqView _⟩) (rHoare_refl _)
  · rintro s _ o _ rfl rfl
    exact rHoare_conseq (fun _ _ h => h)
      (fun _ _ _ _ hp => by obtain ⟨rfl, rfl⟩ := hp; exact ⟨rfl, rfl, rfl⟩) (rHoare_refl _)

/-! ## The ports and the state of the channel -/

/-- Events of the honest port of the channel. -/
inductive ChanHEv (V : Type) where
  /-- Send the value `v`. -/
  | send (v : V)
  /-- Receive the first delivered message. -/
  | recv

/-- Outputs of the honest port of the channel. -/
inductive ChanHOut (V : Type) where
  /-- A send is accepted. -/
  | ok
  /-- The first delivered message, if any. -/
  | got (o : Option V)

/-- Events of the adversary port of the channel. -/
inductive ChanAEv (V : Type) where
  /-- No action. -/
  | idle
  /-- Observe the next message not yet shown. -/
  | poll
  /-- Deliver the head of the queue. -/
  | deliver
  /-- Drop the head of the queue. -/
  | drop
  /-- Replace the head of the queue by `v` and deliver `v`. -/
  | tamper (v : V)

/-- Outputs of the adversary port of the channel. -/
inductive ChanAOut (V Leak : Type) where
  /-- Acknowledgement. -/
  | ack
  /-- The observation of the next message not yet shown, if any. -/
  | leak (o : Option (V ⊕ Leak))

/-- The state of the channel. -/
structure ChanSt (V : Type) where
  /-- The messages in transit, oldest first. -/
  queue : List V
  /-- The number of messages at the front of the queue already shown to the adversary. -/
  cursor : ℕ
  /-- The delivered messages not yet received, oldest first. -/
  inbox : List V

/-! ## The channel -/

namespace FChan

variable {V Leak : Type}

/-- The initial state: no message in transit, none shown, none delivered. -/
def initSt : ChanSt V := ⟨[], 0, []⟩

/-- The state after the head of the queue leaves it, with `l` appended to the inbox. -/
def popTo (t : ChanSt V) (l : List V) : ChanSt V := ⟨t.queue.tail, t.cursor - 1, t.inbox ++ l⟩

/-- A step of the honest port. -/
def honStep (t : ChanSt V) : ChanHEv V → ChanSt V × ChanHOut V
  | .send v => (⟨t.queue ++ [v], t.cursor, t.inbox⟩, .ok)
  | .recv => (⟨t.queue, t.cursor, t.inbox.tail⟩, .got t.inbox.head?)

/-- The observation of the next message not yet shown, under `cap`. -/
def pollLeak (cap : ChannelCap) (ℓ : V → Leak) (t : ChanSt V) : Option (V ⊕ Leak) :=
  ((t.queue.map (cap.wireLeak ℓ)).drop t.cursor).head?

/-- A step of the adversary port under `cap`. -/
def advStep (cap : ChannelCap) (ℓ : V → Leak) (t : ChanSt V) :
    ChanAEv V → ChanSt V × ChanAOut V Leak
  | .idle => (t, .ack)
  | .poll => (⟨t.queue, min (t.cursor + 1) t.queue.length, t.inbox⟩, .leak (pollLeak cap ℓ t))
  | .deliver => (popTo t t.queue.head?.toList, .ack)
  | .drop => (bif cap.drop then popTo t [] else t, .ack)
  | .tamper v => (bif cap.tamper then popTo t [v] else t, .ack)

/-- The honest port of the channel as a system. -/
noncomputable def honSys : Sys (ChanSt V) (ChanHEv V) (ChanHOut V) where
  init := initSt
  step t e := SPComp.pure (honStep t e)

/-- The adversary port of the channel under `cap` as a system. -/
noncomputable def advSys (cap : ChannelCap) (ℓ : V → Leak) :
    Sys (ChanSt V) (ChanAEv V) (ChanAOut V Leak) where
  init := initSt
  step t e := SPComp.pure (advStep cap ℓ t e)

/-- The relation of states with the same observations of the queue and the same cursor. -/
def Rel (cap : ChannelCap) (ℓ : V → Leak) (t t' : ChanSt V) : Prop :=
  t.queue.map (cap.wireLeak ℓ) = t'.queue.map (cap.wireLeak ℓ) ∧ t.cursor = t'.cursor

/-- Removing the head of the queue preserves `Rel`. -/
theorem rel_popTo {cap : ChannelCap} {ℓ : V → Leak} {t t' : ChanSt V} (h : Rel cap ℓ t t')
    (l l' : List V) : Rel cap ℓ (popTo t l) (popTo t' l') := by
  grind [Rel, popTo, List.map_tail]

end FChan

open FChan in
/-- **The ideal channel** with the capability `cap` and the leakage `ℓ`: the honest port on the
left, the adversary port on the right, one shared state. -/
noncomputable def FChan {V Leak : Type} (cap : ChannelCap) (ℓ : V → Leak) :
    Sys (ChanSt V) (ChanHEv V ⊕ ChanAEv V) (ChanHOut V ⊕ ChanAOut V Leak) :=
  Sys.ofPorts honSys (advSys cap ℓ)

/-- The view of the honest port of the channel: two sends with the same observation under
`cap` are related, and so are two receives; honest outputs carry no public part. -/
def honView {V Leak : Type} (cap : ChannelCap) (ℓ : V → Leak) :
    PubView (ChanHEv V) (ChanHOut V) where
  ev
    | .send v, .send v' => cap.wireLeak ℓ v = cap.wireLeak ℓ v'
    | .recv, .recv => True
    | _, _ => False
  out _ _ := True

namespace FChan

variable {V Leak : Type}

/-- The unwinding condition of the honest port for `honView cap ℓ` and `Rel cap ℓ`. -/
theorem honSys_unwinding (cap : ChannelCap) (ℓ : V → Leak) :
    honSys.Unwinding (honView cap ℓ) (Rel cap ℓ) := by
  refine ⟨⟨rfl, rfl⟩, fun t t' e e' ht he => ?_⟩
  cases e <;> cases e' <;> simp only [honView] at he
  · exact rHoare_ret fun _ _ h => ⟨h, by grind [Rel, honStep], trivial⟩
  · exact rHoare_ret fun _ _ h => ⟨h, by grind [Rel, honStep], trivial⟩

/-- The unwinding condition of the adversary port for the equality view and `Rel cap ℓ`. -/
theorem advSys_unwinding (cap : ChannelCap) (ℓ : V → Leak) :
    (advSys cap ℓ).Unwinding eqView (Rel cap ℓ) := by
  refine ⟨⟨rfl, rfl⟩, fun t t' e e' ht he => ?_⟩
  cases he
  cases e
  · exact rHoare_ret fun _ _ h => ⟨h, ht, rfl⟩
  · have hlen : t.queue.length = t'.queue.length := by
      simpa using congrArg List.length ht.1
    exact rHoare_ret fun _ _ h => ⟨h, ⟨ht.1, by simp [advStep, hlen, ht.2]⟩,
      by simp only [advStep, pollLeak, ht.1, ht.2]; rfl⟩
  · exact rHoare_ret fun _ _ h => ⟨h, rel_popTo ht _ _, rfl⟩
  · exact rHoare_ret fun _ _ h => ⟨h, by cases cap.drop <;> grind [advStep, rel_popTo], rfl⟩
  · exact rHoare_ret fun _ _ h => ⟨h, by cases cap.tamper <;> grind [advStep, rel_popTo], rfl⟩

end FChan

section Channel

variable {V Leak : Type}

/-- The channel answers every event on the port of the event. -/
theorem FChan_portTyped (cap : ChannelCap) (ℓ : V → Leak) : (FChan cap ℓ).PortTyped :=
  Sys.ofPorts_portTyped _ _

/-- The channel is idle at the adversary event `idle`. -/
theorem FChan_idleAt (cap : ChannelCap) (ℓ : V → Leak) :
    MultiHybrid.IdleAt (FChan cap ℓ) (.inr .idle) (.inr .ack) := fun t => by
  simp [FChan, FChan.advSys, FChan.advStep]

/-- **Opacity of the channel**: the adversary port shows exactly what the capability lets the
adversary read; two runs whose honest sends have the same observations under `cap` give the
adversary the same outputs. -/
theorem FChan_opaque (cap : ChannelCap) (ℓ : V → Leak) :
    (FChan cap ℓ).Opaque ((honView cap ℓ).sum eqView) :=
  Sys.Opaque.ofPorts (FChan.honSys_unwinding cap ℓ) (FChan.advSys_unwinding cap ℓ)

end Channel

/-! ## The capability order -/

namespace FChan

variable {V Leak : Type}

/-- The adversary event of `FChan c₂` that the simulator issues for an adversary event of
`FChan c₁`: `drop` and `tamper` that `c₁` does not grant become `idle`. -/
def capEv (c₁ : ChannelCap) : ChanAEv V → ChanAEv V
  | .idle => .idle
  | .poll => .poll
  | .deliver => .deliver
  | .drop => bif c₁.drop then .drop else .idle
  | .tamper v => bif c₁.tamper then .tamper v else .idle

/-- The observation under `c₁` of an observation under a capability that reads at least as
much: a plaintext becomes its leakage when `c₁` does not grant reading. -/
def capLeak (c₁ : ChannelCap) (ℓ : V → Leak) : V ⊕ Leak → V ⊕ Leak
  | .inl m => bif c₁.read then .inl m else .inr (ℓ m)
  | .inr l => .inr l

/-- The adversary output of `FChan c₁` that the simulator returns for an adversary output of
`FChan c₂`. -/
def capOut (c₁ : ChannelCap) (ℓ : V → Leak) : ChanAOut V Leak → ChanAOut V Leak
  | .ack => .ack
  | .leak o => .leak (o.map (capLeak c₁ ℓ))

/-- For `c₁ ≤ c₂`, `capLeak c₁ ℓ` sends the observation under `c₂` to the observation under
`c₁`. -/
theorem capLeak_wireLeak {c₁ c₂ : ChannelCap} (hle : c₁ ≤ c₂) (ℓ : V → Leak) (m : V) :
    capLeak c₁ ℓ (c₂.wireLeak ℓ m) = c₁.wireLeak ℓ m := by
  obtain ⟨hr, -, -⟩ := hle
  rcases c₁ with ⟨r₁, d₁, t₁⟩
  rcases c₂ with ⟨r₂, d₂, t₂⟩
  cases r₁ <;> cases r₂ <;> simp_all [capLeak, ChannelCap.wireLeak]

/-- For `c₁ ≤ c₂`, the poll observation under `c₂` mapped by `capLeak c₁ ℓ` is the poll
observation under `c₁`. -/
theorem pollLeak_capLeak {c₁ c₂ : ChannelCap} (hle : c₁ ≤ c₂) (ℓ : V → Leak) (t : ChanSt V) :
    (pollLeak c₂ ℓ t).map (capLeak c₁ ℓ) = pollLeak c₁ ℓ t := by
  simp only [pollLeak, ← List.head?_map, ← List.map_drop, List.map_map]
  congr 3
  funext m
  exact capLeak_wireLeak hle ℓ m

end FChan

open FChan in
/-- The simulator of the capability order on the adversary port: it issues `capEv c₁` of each
event to the channel and returns `capOut c₁ ℓ` of the answer, in one call per activation. -/
noncomputable def capSim {V Leak : Type} (c₁ : ChannelCap) (ℓ : V → Leak) :
    MultiHybrid Unit (ChanAEv V) (ChanAOut V Leak) (ChanAEv V) (ChanAOut V Leak) where
  init := ()
  fuel := 0
  start _ e := SPComp.pure ((), .inl (capEv c₁ e))
  resume _ o := SPComp.pure ((), .inr (capOut c₁ ℓ o))
  finish _ o := SPComp.pure ((), capOut c₁ ℓ o)
  start_noFail _ _ := SPComp.pure_noFail _
  resume_noFail _ _ := SPComp.pure_noFail _
  finish_noFail _ _ := SPComp.pure_noFail _

/-- **The cell of the capability order**: for `c₁ ≤ c₂`, the channel `FChan c₁ ℓ` realizes
`FChan c₂ ℓ` at distance `0` behind the forwarding simulator on the honest port tensored with
`capSim c₁ ℓ` on the adversary port. -/
theorem FChan_realizes_of_le {V Leak : Type} {c₁ c₂ : ChannelCap} (hle : c₁ ≤ c₂)
    (ℓ : V → Leak) :
    RealizesSim (FChan c₁ ℓ) (FChan c₂ ℓ)
      (Simulator.tensor (MultiHybrid.idSim (ChanHEv V) (ChanHOut V)) (capSim c₁ ℓ)
        (MultiHybrid.idSim_opaque (honView c₁ ℓ)) (capSim c₁ ℓ).opaque_eqView)
      (fun _ _ => 0) := by
  change Realizes (FChan c₁ ℓ)
    (((MultiHybrid.idSim (ChanHEv V) (ChanHOut V)).tensor (capSim c₁ ℓ)).withSub (FChan c₂ ℓ))
    (fun _ _ => 0)
  refine realizes_zero_of_stepMap _ _ (fun t => (((), ()), t)) rfl fun t e => ?_
  rcases e with e | e
  · rw [MultiHybrid.tensor_withSub_step_inl _ _ (FChan c₂ ℓ) FChan.honSys (fun _ _ => rfl),
      MultiHybrid.idSim_stepFuel]
    simp [FChan, SPComp.map]
  · rw [MultiHybrid.tensor_withSub_step_inr _ _ (FChan c₂ ℓ) (FChan.advSys c₂ ℓ)
      (fun _ _ => rfl)]
    have hpoll := FChan.pollLeak_capLeak hle ℓ t
    obtain ⟨-, hd, ht⟩ := hle
    cases e with
    | drop =>
      cases h1 : c₁.drop <;>
        simp [FChan, capSim, MultiHybrid.idSim, MultiHybrid.stepFuel, MultiHybrid.drive,
          FChan.advSys, FChan.advStep, FChan.capEv, FChan.capOut, SPComp.map, h1, hd]
    | tamper v =>
      cases h1 : c₁.tamper <;>
        simp [FChan, capSim, MultiHybrid.idSim, MultiHybrid.stepFuel, MultiHybrid.drive,
          FChan.advSys, FChan.advStep, FChan.capEv, FChan.capOut, SPComp.map, h1, ht]
    | _ =>
      simp [FChan, capSim, MultiHybrid.idSim, MultiHybrid.stepFuel, MultiHybrid.drive,
        FChan.advSys, FChan.advStep, FChan.capEv, FChan.capOut, SPComp.map, hpoll]

end CatCrypt.Crypto.UCTransparent
