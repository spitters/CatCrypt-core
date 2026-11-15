/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCTransparentMulti
public import CatCryptCore.Crypto.UCPullbackMetric

/-!
# CryptoVerif games as transition systems

A CryptoVerif game is an oracle process: replicated oracles `O[ĩ]`, each instance callable once
when it is available, whose body ends with `return(M)`, `yield` or `event_abort e` and executes
events on the way. A game here is written with combinators: an interface (oracles, replication
indices, arguments, results, events) and a state machine with an availability predicate and a
probabilistic call. Its system `CvGame.sys` is a `Sys` whose state keeps, beside the game state,
the instances already called, the log of executed events and the abort flag, and whose output
on a call is the result (or a refusal) together with the events the call executed. The
environment of `Realizes` is CryptoVerif's context and distinguisher; it chooses every call,
its indices and its arguments.

## Main results

* `CvIface`, `CvRet`, `CvCall`, `CvOut` — the interface, the ways a call ends, the calls and the
  outputs of a game.
* `CvGame`, `CvConf`, `CvGame.sys` — a game, the configuration of its system, and the system.
* `CvConf.calls`, `CvConf.calls_le_card`, `CvGame.calls_next_some`, `CvGame.kernel_blocked` —
  the number of answered calls of an oracle, its bound by the number of replication indices, its
  increment at an answered call, and the refusal of a call at a used or unavailable instance.
* `CvBound` — bounds as functions of the environment. Indistinguishability `G ≈_ε G'` is
  `Realizes G.sys G'.sys ε`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.CryptoVerifLogic

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open CatCrypt.Crypto.UCTransparent
open scoped ENNReal

/-- The interface of a CryptoVerif game: oracle names, the replication indices of each oracle
(a finite type), argument and result types, and the type of events. -/
structure CvIface where
  /-- Oracle names. -/
  Orc : Type
  /-- The replication indices `ĩ` of an oracle `O[ĩ]`. -/
  Idx : Orc → Type
  /-- Replication indices range over a finite type. -/
  fin : ∀ o, Fintype (Idx o)
  /-- Oracle names have decidable equality. -/
  decOrc : DecidableEq Orc
  /-- Replication indices have decidable equality. -/
  decIdx : ∀ o, DecidableEq (Idx o)
  /-- Argument types. -/
  Arg : Orc → Type
  /-- Result types. -/
  Res : Orc → Type
  /-- Events, with their arguments. -/
  Ev : Type
  /-- Events have decidable equality. -/
  decEv : DecidableEq Ev

attribute [instance] CvIface.fin CvIface.decOrc CvIface.decIdx CvIface.decEv

/-- The end of an oracle call: `return(M)`, `yield`, or `event_abort`, which ends the game. -/
inductive CvRet (α : Type) where
  /-- `return(M)`. -/
  | ret (a : α)
  /-- `yield`: the call ends without a result. -/
  | yield
  /-- `event_abort e`: the game ends. -/
  | abort

/-- Whether a call ended with `event_abort`. -/
def CvRet.isAbort {α : Type} : CvRet α → Bool
  | .abort => true
  | _ => false

variable {I : CvIface}

/-- A call of the environment: an oracle, the replication indices of its instance and its
arguments. -/
abbrev CvCall (I : CvIface) := (o : I.Orc) × I.Idx o × I.Arg o

/-- The output of a call: `none` when the call is refused, otherwise the oracle and its end;
beside it, the events the call executed. -/
abbrev CvOut (I : CvIface) := Option ((o : I.Orc) × CvRet (I.Res o)) × List I.Ev

/-- A CryptoVerif game over the interface `I`: a state (the arrays of the process, as partial
maps from indices, and its tables), the instances available at a state (those whose enclosing
`return` has run), and the body of an instance on its arguments, which gives the next state, the
end of the call and the events executed. -/
structure CvGame (I : CvIface) where
  /-- Game states. -/
  State : Type
  /-- The initial state. -/
  init : State
  /-- The instances available at a state. -/
  avail : State → (o : I.Orc) → I.Idx o → Bool
  /-- The body of an oracle instance. -/
  call : State → (o : I.Orc) → I.Idx o → I.Arg o → SPComp (State × CvRet (I.Res o) × List I.Ev)

/-- The configuration of the system of a game: the game state, the instances already called,
the log of executed events, and whether the game has aborted. -/
structure CvConf (G : CvGame I) where
  /-- The game state. -/
  st : G.State
  /-- The instances already called. -/
  used : (o : I.Orc) → I.Idx o → Bool
  /-- The executed events, oldest first. -/
  log : List I.Ev
  /-- Whether an `event_abort` has run. -/
  stopped : Bool

/-- The number of answered calls of the oracle `o`: the number of its used instances. -/
def CvConf.calls {G : CvGame I} (c : CvConf G) (o : I.Orc) : ℕ :=
  (Finset.univ.filter fun i => c.used o i = true).card

/-- Each instance answers at most once, so an oracle has at most as many answered calls as
replication indices. -/
theorem CvConf.calls_le_card {G : CvGame I} (c : CvConf G) (o : I.Orc) :
    c.calls o ≤ Fintype.card (I.Idx o) :=
  Finset.card_filter_le _ _

namespace CvGame

variable (G : CvGame I)

/-- The result of the kernel of a step: `none` for a refused call, otherwise the next game
state, the oracle and the end of its call, and the events executed. -/
abbrev KRes := Option (G.State × ((o : I.Orc) × CvRet (I.Res o)) × List I.Ev)

/-- A call is refused after an abort, at a used instance, and at an unavailable instance. -/
def blocked (c : CvConf G) (a : CvCall I) : Bool :=
  c.stopped || c.used a.1 a.2.1 || !G.avail c.st a.1 a.2.1

/-- The probabilistic part of a step: refusal, or the body of the called instance. -/
noncomputable def kernel (c : CvConf G) (a : CvCall I) : SPComp G.KRes :=
  if G.blocked c a then SPComp.pure none
  else SPComp.map (fun r => some (r.1, ⟨a.1, r.2.1⟩, r.2.2)) (G.call c.st a.1 a.2.1 a.2.2)

/-- The configuration after a step: a refused call leaves it; an answered call moves the game
state, marks the instance used, appends the executed events and records an abort. -/
def next (c : CvConf G) (a : CvCall I) : G.KRes → CvConf G
  | none => c
  | some r =>
    { st := r.1
      used := Function.update c.used a.1 (Function.update (c.used a.1) a.2.1 true)
      log := c.log ++ r.2.2
      stopped := c.stopped || r.2.1.2.isAbort }

/-- The output of a step. -/
def out : G.KRes → CvOut I
  | none => (none, [])
  | some r => (some r.2.1, r.2.2)

/-- The system of a game. -/
noncomputable def sys : Sys (CvConf G) (CvCall I) (CvOut I) where
  init := ⟨G.init, fun _ _ => false, [], false⟩
  step c a := SPComp.map (fun r => (G.next c a r, G.out r)) (G.kernel c a)

/-- A refused call returns `none`. -/
theorem kernel_blocked (c : CvConf G) (a : CvCall I) (h : G.blocked c a = true) :
    G.kernel c a = SPComp.pure none := by
  simp [kernel, h]

/-- The log after a step is the log before it followed by the events of the output. -/
theorem log_next (c : CvConf G) (a : CvCall I) (r : G.KRes) :
    (G.next c a r).log = c.log ++ (G.out r).2 := by
  cases r <;> simp [next, out]

/-- An answered call at an unused instance adds one answered call of its oracle. -/
theorem calls_next_some (c : CvConf G) (a : CvCall I)
    (r : G.State × ((o : I.Orc) × CvRet (I.Res o)) × List I.Ev) (h : c.used a.1 a.2.1 = false) :
    (G.next c a (some r)).calls a.1 = c.calls a.1 + 1 := by
  simp only [next, CvConf.calls, Function.update_self]
  rw [← Finset.card_insert_of_notMem (s := Finset.univ.filter fun i => c.used a.1 i = true)
    (a := a.2.1) (by simp [h])]
  congr 1
  ext j
  by_cases hj : j = a.2.1 <;> simp [Function.update_apply, hj]

end CvGame

/-- A bound of indistinguishability: a function of the environment state type and the
environment. -/
abbrev CvBound (I : CvIface) := (ζ : Type) → Env (Strat ζ (CvCall I) (CvOut I)) ζ → ℝ≥0∞

end CatCrypt.Crypto.CryptoVerifLogic
