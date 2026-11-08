/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.SignalStackUC
public import CatCryptCore.Crypto.AKE.PQXDHSquareGDH
import CatCryptCore.Tactics.AutoDispatchExt

/-!
# The PQXDH Signal stack realizes the ideal secure channel

The PQXDH key exchange `pqxdhReal P G` followed by the key layer `keyLayer realV` realizes the
ideal secure channel `F_SC realV idealV` of `SignalStackUC.lean`. The proof is the instance of the
KE-then-channel composition `stack_realizes_FSC_of` at the PQXDH square
`pqxdh_realizesSim_gapDH` of `PQXDHSquareGDH.lean`: the PQXDH simulator `simProt P G` is a
forwarding simulator for the data `pqFwd`, and the simulator over `F_SC` is
`chanSim (simProt P G) pqFwd`.

The time certificate of the simulator is in `SignalStackPQXDHTimed.lean`.

## Main results

* `pqPhase`, `pqFwd`: the forwarding data of the PQXDH simulator.
* `pqSimStart_noHon`: the `start` step of the PQXDH simulator outputs nothing on the honest port.
* `simProt_isFwd`: the PQXDH simulator is a forwarding simulator for `pqFwd`.
* `pqxdhStackBound`, `pqxdh_stack_realizes_FSC`: the bound and the realization of `F_SC`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Messaging.SignalStackPQXDH

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Messaging
open CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.Messaging.SignalStackUC
open CatCrypt.Crypto.AKE.PQXDHSquare
open CatCrypt.Crypto.AKE.PQXDHSquareGDH (gdhBoundP pqxdh_realizesSim_gapDH)
open CatCrypt.Crypto.KEM.Games (Scheme)
open CatCrypt.Crypto.PAKE.DHExtract (DHGroup)
open PubView (eqView)
open scoped ENNReal

section Fwd

variable {S W K PK SK SS C : Type}

/-- The stored adversary output of a phase of the PQXDH simulator: none in the phase `fwd`. -/
def pqPhase : Phase S W K PK C → Option (POut S W K PK C)
  | .fwd => none
  | .out r => some r

/-- **The forwarding data of the PQXDH simulator**: the phase `fwd` after an answer of `F_AKE`,
the output stored in the phase, and the acknowledgement `.inl .ack`. -/
def pqFwd : FwdData (SimSt S W K PK SK SS C) (POut S W K PK C) where
  reset s := (s.1, s.2.1, .fwd)
  phase s := pqPhase s.2.2
  ack := .inl .ack

/-- A decision of the PQXDH simulator that is not an honest output. -/
def PNoHon (d : Dec S W K PK C) : Prop := ∀ h, d ≠ .inr (.inl h)

end Fwd

section Sim

variable {S W K PK SK SS C : Type} [Field S] [Fintype S] [DecidableEq W] [Fintype K]
  [Nonempty K] [Inhabited K] [DecidableEq SS] (O : KemOps PK SK SS C) (G : DHGroup S W)

omit [Field S] [Fintype S] in
/-- The delivery of a key calls `F_AKE`. -/
theorem pqDeliver_noHon (s : PSt S W K PK SK SS C) (inp : Inst → Option (PInp W SS)) (x : Inst)
    (r : Rec K) (ip : PInp W SS) {q : SimSt S W K PK SK SS C × Dec S W K PK C}
    (hq : IsOutcome (deliver s inp x r ip) q) : PNoHon q.2 := by
  unfold deliver at hq
  split at hq
  · obtain ⟨a, _, rfl⟩ := isOutcome_map_iff.mp hq
    intro h hh
    simp at hh
  · rw [← isOutcome_pure hq]
    intro h hh
    simp at hh

/-- **The PQXDH simulator outputs nothing on the honest port by itself**: every honest output of
the simulated world is an answer of the functionality. -/
theorem pqSimStart_noHon (s : SimSt S W K PK SK SS C) (e : OEv W SS C)
    {q : SimSt S W K PK SK SS C × Dec S W K PK C} (hq : IsOutcome (simStart O G s e) q) :
    PNoHon q.2 := by
  rcases e with (⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) |
    (_ | _ | pid | ⟨sid, pid⟩ | ⟨sid, pid⟩ | pid | ⟨sid, pid⟩ | ⟨sid, pid, e, c⟩ | x)
  all_goals simp only [simStart, simCorrupt, simComplete, simSend] at hq
  case inl.newSession =>
    split at hq
    · obtain ⟨y, _, hq⟩ := isOutcome_bind hq
      split at hq
      · obtain ⟨a, _, rfl⟩ := isOutcome_map_iff.mp hq; intro h hh; simp at hh
      · rw [← isOutcome_pure hq]; intro h hh; simp at hh
    · rw [← isOutcome_pure hq]; intro h hh; simp at hh
  all_goals repeat' split at hq
  all_goals first
    | (rw [← isOutcome_pure hq]; intro h hh; simp at hh)
    | (obtain ⟨a, _, rfl⟩ := isOutcome_map_iff.mp hq; intro h hh; simp at hh)
    | (obtain ⟨_, _, hq⟩ := isOutcome_bind hq; obtain ⟨_, _, hq⟩ := isOutcome_bind hq
       obtain ⟨_, _, hq⟩ := isOutcome_bind hq; exact pqDeliver_noHon _ _ _ _ _ hq)
    | (obtain ⟨_, _, hq⟩ := isOutcome_bind hq; obtain ⟨_, _, hq⟩ := isOutcome_bind hq
       exact pqDeliver_noHon _ _ _ _ _ hq)

/-- **The PQXDH simulator is a forwarding simulator** for the data `pqFwd`. -/
theorem simProt_isFwd (P : Scheme PK SK SS C) : IsFwd (simProt (K := K) P G) pqFwd where
  fuel_eq := rfl
  finish_eq s o := by
    rcases s with ⟨a, b, ph⟩
    cases ph <;> rcases o with o | o <;> rfl
  start_noHon s e _ hq := pqSimStart_noHon (kemOps P) G s e hq

end Sim

section Stack

variable {S W K PK SK SS C V : Type} [Field S] [Fintype S] [SampleableType W] [Fintype K]
  [Nonempty K] [Inhabited K] [DecidableEq SS] (P : Scheme PK SK SS C) (G : DHGroup S W)

/-- The bound of the PQXDH Signal stack at an environment `Z`: the gap Diffie–Hellman bound of
the PQXDH square at the environment reduced through the key layer, and `scBound` at the
environment reduced through the simulator. -/
noncomputable def pqxdhStackBound (N : Finset PartyId) (realV : K → SPComp V) (idealV : SPComp V)
    (hR : ∀ k, SPComp.IsPure (realV k) ∧ SPComp.NoFail (realV k)) (ζ : Type)
    (Z : Env (Strat ζ (OEv W SS C) (HOut V ⊕ POut S W K PK C)) ζ) : ℝ≥0∞ :=
  gdhBoundP P G N ((OProt.oracle (Q := OEv W SS C) (A := OOut S W K PK C)).reduction
      ((Hybrid.seqCtxR (E := OEv W SS C) (keyLayer realV)
        (keyLayer_noFail fun k => (hR k).2)).reduceEnv Z)) +
    scBound realV idealV ((simSCOver (simProt (K := K) P G) pqFwd).reduceEnv (.inr .idle) Z)

/-- **The PQXDH Signal stack realizes the ideal secure channel** (genuine UC).

*Ideal functionality.* `F_SC realV idealV`: the multi-session secure channel over `F_AKE` with
unlinked delivery, whose honest port outputs on `getKey` the ideal view `idealV` for a completed
session, the real view `realV k` under the adversary key `k` for a session exposed by corruption,
and nothing for a session without a key.

*Real world.* The real PQXDH protocol `pqxdhReal P G` followed by the key layer
`keyLayer realV`, which keys the view `realV` with the session key of every `getKey` answer.

*Simulator.* `chanSim (simProt P G) pqFwd`: the PQXDH simulator with its decisions read over
`F_SC`. It keeps a copy of the real state, draws the long-term, session and KEM secrets, forwards
the honest events, answers the adversary events on its copy, corrupts under the static rule, and
delivers keys through `newKey` or `newKeyUnlinked`; in the phase `fwd` it passes the answers of
`F_SC` on the honest port unchanged.

*Bound.* For views that neither touch the heap nor fail, for every finite set of parties `N` and
every environment `Z`, the distance is at most `pqxdhStackBound`: the gap Diffie–Hellman bound
`gdhBoundP` of the PQXDH square at the environment reduced through the key layer, plus
`scBound realV idealV` at the environment reduced through the simulator. -/
theorem pqxdh_stack_realizes_FSC (N : Finset PartyId) (realV : K → SPComp V) (idealV : SPComp V)
    (hR : ∀ k, SPComp.IsPure (realV k) ∧ SPComp.NoFail (realV k))
    (hI : SPComp.IsPure idealV ∧ SPComp.NoFail idealV) :
    RealizesSim ((pqxdhReal (K := K) P G).seq (keyLayer realV)) (F_SC realV idealV)
      (chanSim (simProt P G) pqFwd) (pqxdhStackBound P G N realV idealV hR) :=
  stack_realizes_FSC_of (pqxdhReal (K := K) P G) (simProt P G) (simProt_opaque P G) pqFwd
    (simProt_isFwd G P) (pqxdh_realizesSim_gapDH P G N) realV idealV hR hI

end Stack

end CatCrypt.Crypto.Messaging.SignalStackPQXDH
