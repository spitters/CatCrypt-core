/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Party.Prog
public import CatCryptCore.Crypto.AKE.FAKESys
public import CatCryptCore.Crypto.UCSimulator

/-!
# The authenticated key-exchange functionality in the party language

**Ideal functionality.** `F_AKE keySample unlinked` of `CatCryptCore.Crypto.AKE.FAKESys`: the
multi-session authenticated key exchange of Canetti and Krawczyk with adversarial key delivery,
corruption of parties and keys drawn from `keySample`; with `unlinked`, the
delivery `newKeyUnlinked` gives a session a key independent of its partner's.

**Program.** `FAKEProg.body keySample unlinked t` is one activation of `F_AKE` as a program of
the party language (`Party.Prog`) over the state `t` of the functionality: it receives an event,
answers an honest event by `honStep`, an adversary event by the step of the adversary port, and
samples a fresh key from `keySample` on `newKey` and `newKeyUnlinked`. Its loop `FAKEProg.sys`
from `initSt` is step-equivalent to `F_AKE` (`FAKEProg.sys_stepEq`). A multi-call simulator
running with the program is at distance `0` from the simulator running with `F_AKE`
(`FAKEProg.withSub_realizes`), so a UC statement of a protocol against `F_AKE` behind a
multi-call simulator holds against the program (`FAKEProg.realizesSim_sys`). The functionality
is the shared ideal functionality of the X3DH and PQXDH protocols written in the party language
(`Party.Protocols.X3DH`, `Party.Protocols.PQXDH`).

Search words: party language, F_AKE, authenticated key exchange, ideal functionality, UC, X3DH,
PQXDH.

## Main definitions

* `FAKEProg.body`: an activation of `F_AKE` as a program.
* `FAKEProg.sys`: the loop of `body`, the functionality as a program.

## Main results

* `FAKEProg.act_body`: the activation of the program is the step of `F_AKE`.
* `FAKEProg.sys_stepEq`: the program is step-equivalent to `F_AKE`.
* `FAKEProg.sys_opaque`: opacity of the program for the view of the key-exchange interface.
* `FAKEProg.withSub_realizes`: a multi-call simulator running with `F_AKE` realizes the simulator
  running with the program at distance `0`.
* `FAKEProg.realizesSim_sys`: realization behind a multi-call simulator transfers from `F_AKE`
  to the program.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Party.FAKEProg

open CatCrypt.Core CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.UCConcrete Prog
open PubView (eqView)
open scoped ENNReal

variable {K : Type} [Countable K]

/-- **An activation of `F_AKE` as a program**: receive an event, answer it as the port of the
event does on the state `t`, and return the new state; `newKey` and `newKeyUnlinked` sample a
fresh key from `keySample`. -/
noncomputable def body (keySample : SPComp K) (unlinked : Bool) (t : St K) :
    Prog (HEv ⊕ AEv K) (HOut K ⊕ AOut) (St K) := do
  match ← recvE with
  | .inl h =>
    sendE (.inl (honStep t h).2)
    pure (honStep t h).1
  | .inr .idle =>
    sendE (.inr .ack)
    pure t
  | .inr .poll =>
    sendE (.inr (.notice (pollStep t).2))
    pure (pollStep t).1
  | .inr (.corrupt pid) =>
    sendE (.inr .ack)
    pure (corruptStep t pid)
  | .inr (.impersonate _ _) =>
    sendE (.inr .ack)
    pure t
  | .inr (.newKey sid pid k) =>
    let kf ← sampleE keySample
    sendE (.inr .ack)
    pure (newKeyStep t (sid, pid) k kf)
  | .inr (.newKeyUnlinked sid pid k) =>
    let kf ← sampleE keySample
    sendE (.inr .ack)
    pure ((if unlinked then newKeyFreshStep else newKeyStep) t (sid, pid) k kf)

/-- **`F_AKE` as a program**: the loop of `body` from the empty state. -/
noncomputable def sys (keySample : SPComp K) (unlinked : Bool) :
    Sys (Prog (HEv ⊕ AEv K) (HOut K ⊕ AOut) (St K)) (HEv ⊕ AEv K) (HOut K ⊕ AOut) :=
  loopSys (body keySample unlinked) initSt

/-- The activation of `body` is the step of `F_AKE` followed by a return. -/
theorem act_body (keySample : SPComp K) (unlinked : Bool) (t : St K) (e : HEv ⊕ AEv K) :
    act (body keySample unlinked t) e =
      SPComp.map (fun q => (Prog.ret q.1, q.2)) ((F_AKE keySample unlinked).step t e) := by
  rcases e with h | (_ | _ | pid | ⟨sid, pid⟩ | ⟨sid, pid, k⟩ | ⟨sid, pid, k⟩)
  all_goals simp [body, act_def, stepWith_def, ProgE.recvE, sampleE, ProgE.sendE, ProgE.bind,
    emitK_bind, emitK_sample, F_AKE, honSys, advSys, SPComp.map, SPComp.bind_assoc]

/-- **The program is step-equivalent to `F_AKE`.** -/
theorem sys_stepEq (keySample : SPComp K) (unlinked : Bool) :
    Sys.StepEq ⟨_, sys keySample unlinked⟩ ⟨St K, F_AKE keySample unlinked⟩ :=
  loopSys_stepEq _ _ _ (act_body keySample unlinked)

/-- **Opacity of the program** for the view of the key-exchange interface. -/
theorem sys_opaque (keySample : SPComp K) (unlinked : Bool) :
    (sys keySample unlinked).Opaque (keHonView.sum eqView) :=
  opaque_keView _

variable {σ E O : Type}

/-- **A multi-call simulator running with `F_AKE` realizes the simulator running with the
program** at distance `0`: the return of the state of `F_AKE` is a step map. -/
theorem withSub_realizes (π : MultiHybrid σ E O (HEv ⊕ AEv K) (HOut K ⊕ AOut))
    (keySample : SPComp K) (unlinked : Bool) :
    Realizes (π.withSub (F_AKE keySample unlinked)) (π.withSub (sys keySample unlinked))
      (fun _ _ => 0) :=
  realizes_zero_of_stepMap _ _ (fun p => (p.1, Prog.ret p.2)) rfl fun p e =>
    MultiHybrid.withSub_stepMap π Prog.ret (fun t g => (act_body keySample unlinked t g).symm) p e

/-- **Realization behind a multi-call simulator transfers from `F_AKE` to the program.** -/
theorem realizesSim_sys {τ : Type} {V : PubView E O}
    {W : PubView (HEv ⊕ AEv K) (HOut K ⊕ AOut)} {R : Sys τ E O}
    {π : MultiHybrid σ E O (HEv ⊕ AEv K) (HOut K ⊕ AOut)} {h : π.Opaque V W}
    {keySample : SPComp K} {unlinked : Bool} {bound : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞}
    (hR : RealizesSim R (F_AKE keySample unlinked) (Simulator.ofMultiHybrid π h) bound) :
    RealizesSim R (sys keySample unlinked) (Simulator.ofMultiHybrid π h) bound :=
  fun ζ Z => le_of_le_of_eq ((Realizes.trans hR (withSub_realizes π keySample unlinked)) ζ Z)
    (add_zero _)

end CatCrypt.Crypto.Party.FAKEProg
