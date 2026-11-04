/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QPullbackPar

/-!
# Quantum feedback with private registers as a context over environments with memory

The **quantum loopback** `QSys.loopback S n cut` of a system `S` with private register `H` on
the interface `(E ⊕ X, O ⊕ X)` along the wire `X` is a system on `(E, O)` with the same private
register: an outer event `e` activates `S` on `inl e`; an output `inr x` of `S` is fed back to
`S` as the event `inr x`, at most `n` times; the first output `inl o` ends the activation with
the outer output `o`, and a wire value `x` answered to the last allowed call ends it with the
output `cut x` (`QSys.fbRun`). It is the bounded loopback with a cut-off, the quantum analogue
of the classical `Sys.loopback`. It differs from the unbounded loopback `QRSys.loopbackω` of
`QSysCat`, the trace of that category, which fails on exhausted fuel and takes the supremum over
the fuel.

The feedback context `- ↺` is a quantum pullback over environments with memory
(`QSys.loopbackCtx`). The pulled environment `QSys.fbEnv Z n cut idle` keeps the memory register
of `Z`, runs `Z.rounds * (n + 1)` rounds against `S`, and carries a phase (`QSys.FbPhase`):
at the start of an outer round it lets `Z` choose an event, during a call it feeds wire values
back, and after the outer output it pads the round with activations on the idle event `idle`.
When `S` is idle at `idle` (`QSys.IdleAt`), the padding collapses to `pure`
(`QSys.qloopQ_fbEnv_rest`), each block of `n + 1` rounds is one round against the loopback
(`QSys.qloopQ_fbEnv`), and the views agree (`QSys.qviewQ_loopback`). The runs split along the
sum of the round numbers (`qloopQ_add`).

The **composition theorem** for the quantum loopback (`QRealizesQB.loopback`): if `R` realizes
`I` against environments with quantum memory with bound `b`, both idle at `idle`, then the
loopback of `R` realizes the loopback of `I` with the bound `b` at the pulled environment. It is
the quantum analogue of the classical `Realizes.loopback`.

Search words: quantum feedback, bounded loopback, private register, quantum context, pullback,
composition theorem, idle event, environment with quantum memory, fuel, cut-off.

## Main definitions

* `QSys.fbRun`, `QSys.loopback`, `QSys.FbPhase`, `QSys.fbEnv`, `QSys.loopbackCtx`

## Main results

* `qloopQ_add` — joint runs split along the sum of the round numbers
* `QSys.qloopQ_fbEnv`, `QSys.qviewQ_loopback`
* `QRealizesQB.loopback`
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace CatCrypt.Quantum.ReactiveUC

open _root_.Quantum
open CatCrypt.Crypto.UCTransport (QSysObj)
open scoped ENNReal

/-! ## Splitting joint runs -/

section Split

variable {H K : Type} [Fintype H] [Fintype K]
variable {τ ζ E O : Type} {d : ℕ}

/-- **Joint runs split along the sum of the round numbers**: `m + k` rounds are `m` rounds
followed by `k` rounds from the configuration reached. -/
theorem qloopQ_add (S : QSys H τ E O d) (Z : QStratQ K ζ E O d) :
    ∀ (m k : ℕ) (c : ζ × τ),
      qloopQ S Z (m + k) c = (qloopQ S Z m c).bind (qloopQ S Z k) := by
  intro m
  induction m with
  | zero => intro k c; simp only [Nat.zero_add, qloopQ, SubInstrument.pure_bind]
  | succ m ih =>
    intro k c
    rw [Nat.succ_add]
    simp only [qloopQ, SubInstrument.bind_assoc, ih]

end Split

/-! ## The quantum loopback -/

namespace QSys

variable {H K : Type} [Fintype H] [Fintype K]
variable {τ ζ E O X : Type} {d : ℕ}

/-- The feedback run of `S` with fuel `k` from the event `ev`: `S` is activated on `ev`; an
output `inl o` ends the run with `o`, an output `inr x` is fed back as the event `inr x` with
fuel `k - 1`, and at fuel `0` a wire value `x` ends the run with `cut x`. -/
def fbRun (S : QSys H τ (E ⊕ X) (O ⊕ X) d) (cut : X → O) :
    ℕ → τ → E ⊕ X → SubInstrument (Fin d × H) (Fin d × H) (τ × O)
  | 0, t, ev => (S.step t ev).bind fun p => SubInstrument.pure (p.1, p.2.elim id cut)
  | k + 1, t, ev => (S.step t ev).bind fun p =>
      p.2.elim (fun o => SubInstrument.pure (p.1, o)) fun x => fbRun S cut k p.1 (.inr x)

/-- The quantum loopback of `S` along its wire `X` with fuel `n` and cut-off map `cut`: an
outer event `e` starts the feedback run of `S` from `inl e` with fuel `n`. -/
def loopback (S : QSys H τ (E ⊕ X) (O ⊕ X) d) (n : ℕ) (cut : X → O) : QSys H τ E O d where
  init := S.init
  initReg := S.initReg
  step t e := S.fbRun cut n t (.inl e)

/-- The phase of the environment pulled back along the loopback: at the start of an outer
round, in a call with remaining fuel `k`, feeding the wire value `x` back with fuel `k`, or
padding the round with `j + 1` idle activations. -/
inductive FbPhase (X : Type) where
  /-- The start of an outer round. -/
  | start
  /-- A call with remaining fuel `k`. -/
  | call (k : ℕ)
  /-- Feeding the wire value `x` back with remaining fuel `k`. -/
  | feed (x : X) (k : ℕ)
  /-- Padding with `j + 1` idle activations left. -/
  | pad (j : ℕ)

/-- The phase with `j` padding activations left: the start of an outer round when `j = 0`. -/
def FbPhase.rest {X : Type} : ℕ → FbPhase X
  | 0 => .start
  | j + 1 => .pad j

/-- The event choice of the environment pulled back along the loopback. -/
def fbNext (Z : QStratQ K ζ E O d) (n : ℕ) (idle : E ⊕ X) :
    ζ → FbPhase X → SubInstrument (Fin d × K) (Fin d × K) ((ζ × FbPhase X) × (E ⊕ X))
  | z, .start => (Z.next z).bind fun a => SubInstrument.pure ((a.1, .call n), .inl a.2)
  | z, .call k => SubInstrument.pure ((z, .call k), idle)
  | z, .feed x k => SubInstrument.pure ((z, .call k), .inr x)
  | z, .pad j => SubInstrument.pure ((z, .pad j), idle)

/-- The observation of the environment pulled back along the loopback. -/
def fbObs (Z : QStratQ K ζ E O d) (cut : X → O) :
    ζ → FbPhase X → O ⊕ X → SubInstrument (Fin d × K) (Fin d × K) (ζ × FbPhase X)
  | z, .call k, .inl o => (Z.obs z o).bind fun z' => SubInstrument.pure (z', FbPhase.rest k)
  | z, .call 0, .inr x => (Z.obs z (cut x)).bind fun z' => SubInstrument.pure (z', .start)
  | z, .call (k + 1), .inr x => SubInstrument.pure (z, .feed x k)
  | z, .pad j, _ => SubInstrument.pure (z, FbPhase.rest j)
  | z, .start, _ => SubInstrument.pure (z, .start)
  | z, .feed _ _, _ => SubInstrument.pure (z, .start)

/-- The environment `Z` pulled back along the loopback with fuel `n`, cut-off map `cut` and
idle event `idle`: it keeps the memory register of `Z` and runs `n + 1` rounds per round of
`Z`, the first on the outer event of `Z`, then the wire values fed back, then idle padding. -/
def fbEnv (Z : QStratQ K ζ E O d) (n : ℕ) (cut : X → O) (idle : E ⊕ X) :
    QStratQ K (ζ × FbPhase X) (E ⊕ X) (O ⊕ X) d where
  rounds := Z.rounds * (n + 1)
  init := (Z.init, .start)
  initReg := Z.initReg
  next c := fbNext Z n idle c.1 c.2
  obs c o := fbObs Z cut c.1 c.2 o

/-- Unfolding lemma of `fbEnv`: its event choice. -/
theorem fbEnv_next (Z : QStratQ K ζ E O d) (n : ℕ) (cut : X → O) (idle : E ⊕ X)
    (c : ζ × FbPhase X) : (fbEnv Z n cut idle).next c = fbNext Z n idle c.1 c.2 :=
  rfl

/-- Unfolding lemma of `fbEnv`: its observation. -/
theorem fbEnv_obs (Z : QStratQ K ζ E O d) (n : ℕ) (cut : X → O) (idle : E ⊕ X)
    (c : ζ × FbPhase X) (o : O ⊕ X) : (fbEnv Z n cut idle).obs c o = fbObs Z cut c.1 c.2 o :=
  rfl

variable {S : QSys H τ (E ⊕ X) (O ⊕ X) d} {idle : E ⊕ X} {oS : O ⊕ X}

/-- The idle padding of the pulled environment collapses to `pure` on a system idle at the
idle event. -/
theorem qloopQ_fbEnv_rest (hS : S.IdleAt idle oS) (Z : QStratQ K ζ E O d) (n : ℕ)
    (cut : X → O) : ∀ (j : ℕ) (z : ζ) (t : τ),
      qloopQ S (fbEnv Z n cut idle) j ((z, FbPhase.rest j), t) =
        SubInstrument.pure ((z, .start), t) := by
  intro j
  induction j with
  | zero => intro z t; rfl
  | succ j ih =>
    intro z t
    simp only [qloopQ, FbPhase.rest.eq_2, fbEnv_next, fbEnv_obs, fbNext, fbObs, hS t,
      envPlace, SubInstrument.frame_pure, relabel_pure, SubInstrument.pure_bind, ih]

/-- A call with fuel `k` of the pulled environment, followed by its remaining `k` rounds, is
the feedback run with fuel `k` followed by the observation of `Z`. -/
theorem qloopQ_fbEnv_call (hS : S.IdleAt idle oS) (Z : QStratQ K ζ E O d) (n : ℕ)
    (cut : X → O) : ∀ (k : ℕ) (z : ζ) (t : τ) (ev : E ⊕ X),
      ((S.step t ev).frame K).bind (fun p =>
          (envPlace H ((fbEnv Z n cut idle).obs (z, .call k) p.2)).bind fun c =>
            qloopQ S (fbEnv Z n cut idle) k (c, p.1)) =
        ((S.fbRun cut k t ev).frame K).bind fun p =>
          (envPlace H (Z.obs z p.2)).bind fun z' => SubInstrument.pure ((z', .start), p.1) := by
  intro k
  induction k with
  | zero =>
    intro z t ev
    simp only [fbRun, SubInstrument.frame_bind, SubInstrument.bind_assoc]
    congr 1
    funext p
    rcases p with ⟨t', o | x⟩ <;>
      simp only [fbEnv_obs, fbObs, FbPhase.rest, qloopQ, envPlace, SubInstrument.frame_bind,
        SubInstrument.frame_pure, relabel_bind, relabel_pure, SubInstrument.bind_assoc,
        SubInstrument.pure_bind, Sum.elim_inl, Sum.elim_inr, id]
  | succ k ih =>
    intro z t ev
    simp only [fbRun, SubInstrument.frame_bind, SubInstrument.bind_assoc]
    congr 1
    funext p
    rcases p with ⟨t', o | x⟩
    · simp only [fbEnv_obs, fbObs, envPlace, SubInstrument.frame_bind, SubInstrument.frame_pure,
        relabel_bind, relabel_pure, SubInstrument.bind_assoc, SubInstrument.pure_bind,
        Sum.elim_inl]
      simp only [qloopQ_fbEnv_rest hS]
    · simp only [envPlace, fbEnv_obs, fbObs] at ih
      simp only [fbEnv_obs, fbObs, Sum.elim_inr, envPlace, SubInstrument.frame_pure,
        relabel_pure, SubInstrument.pure_bind, qloopQ, fbEnv_next, fbNext]
      exact ih z t' (.inr x)

/-- One outer round of the pulled environment, `n + 1` rounds against `S`, is one round
against the loopback of `S`. -/
theorem qloopQ_fbEnv_round (hS : S.IdleAt idle oS) (Z : QStratQ K ζ E O d) (n : ℕ)
    (cut : X → O) (z : ζ) (t : τ) :
    qloopQ S (fbEnv Z n cut idle) (n + 1) ((z, .start), t) =
      (qloopQ (S.loopback n cut) Z 1 (z, t)).bind
        fun c => SubInstrument.pure ((c.1, .start), c.2) := by
  have hc := qloopQ_fbEnv_call hS Z n cut n
  simp only [envPlace] at hc
  simp only [qloopQ, fbEnv_next, fbNext, loopback, envPlace, SubInstrument.frame_bind,
    SubInstrument.frame_pure, relabel_bind, relabel_pure, SubInstrument.bind_assoc,
    SubInstrument.pure_bind, hc]

/-- **Blocks of the pulled environment.** `m * (n + 1)` rounds of the pulled environment
against `S` from the start of an outer round are `m` rounds of `Z` against the loopback of
`S`. -/
theorem qloopQ_fbEnv (hS : S.IdleAt idle oS) (Z : QStratQ K ζ E O d) (n : ℕ)
    (cut : X → O) : ∀ (m : ℕ) (z : ζ) (t : τ),
      qloopQ S (fbEnv Z n cut idle) (m * (n + 1)) ((z, .start), t) =
        (qloopQ (S.loopback n cut) Z m (z, t)).bind
          fun c => SubInstrument.pure ((c.1, .start), c.2) := by
  intro m
  induction m with
  | zero => intro z t; simp only [Nat.zero_mul, qloopQ, SubInstrument.pure_bind]
  | succ m ih =>
    intro z t
    rw [Nat.succ_mul, Nat.add_comm, qloopQ_add, qloopQ_fbEnv_round hS, Nat.add_comm m 1,
      qloopQ_add, SubInstrument.bind_assoc, SubInstrument.bind_assoc]
    simp only [SubInstrument.pure_bind, ih]

/-- **View under the loopback.** The view of `Z` against the loopback of a system idle at
`idle` is the view of the pulled environment against the system, projected to the state of
`Z`. -/
theorem qviewQ_loopback [DecidableEq H] [DecidableEq K] (hS : S.IdleAt idle oS)
    (Z : QStratQ K ζ E O d) (n : ℕ) (cut : X → O) :
    qviewQ (S.loopback n cut) Z =
      (qviewQ S (fbEnv Z n cut idle)).bind fun c => SubInstrument.pure c.1 := by
  have hr : (fbEnv Z n cut idle).rounds = Z.rounds * (n + 1) := rfl
  have hi : (fbEnv Z n cut idle).init = (Z.init, .start) := rfl
  have hk : (fbEnv Z n cut idle).initReg = Z.initReg := rfl
  have hl : (S.loopback n cut).initReg = S.initReg := rfl
  have hl' : (S.loopback n cut).init = S.init := rfl
  simp only [qviewQ, hr, hi, hk, hl, hl', qloopQ_fbEnv hS, SubInstrument.bind_assoc,
    SubInstrument.pure_bind]

/-- The feedback context `- ↺` with fuel `n`, cut-off map `cut` and idle event `idle` as a
pullback over environments with memory: the memory register is kept, the pulled environment is
`fbEnv`, and the admissible systems are those idle at `idle`. -/
def loopbackCtx (n : ℕ) (cut : X → O) (idle : E ⊕ X) :
    QEnvPullbackQ (E ⊕ X) (O ⊕ X) E O d where
  map Y := { H := Y.H, τ := Y.τ, sys := Y.sys.loopback n cut }
  Mem K := K
  memFin _ inst _ := inst
  memDec _ _ inst := inst
  Ctx ζ := ζ × FbPhase X
  pull Z := fbEnv Z n cut idle
  out c := c.1
  Adm Y := ∃ o, Y.sys.IdleAt idle o
  view_map := by
    rintro Y ⟨o, hY⟩ K _ _ ζ Z
    exact qviewQ_loopback hY Z n cut

end QSys

/-! ## The composition theorem for the quantum loopback -/

namespace QRealizesQB

variable {H H₁ : Type} [Fintype H] [DecidableEq H] [Fintype H₁] [DecidableEq H₁]
variable {τ τ₁ E O X : Type} {d : ℕ}

/-- **Composition theorem for the quantum loopback.** If `R` realizes `I` against environments
with memory with bound `b`, and `R` and `I` are idle at `idle`, then the loopback of `R`
realizes the loopback of `I` with bound `b` at the pulled environment, which runs `n + 1`
rounds of the system per round of the outer environment and keeps its memory register. -/
theorem loopback {R : QSys H τ (E ⊕ X) (O ⊕ X) d} {I : QSys H₁ τ₁ (E ⊕ X) (O ⊕ X) d}
    (idle : E ⊕ X) {oR oI : O ⊕ X} (hR : R.IdleAt idle oR) (hI : I.IdleAt idle oI)
    {b : (K : Type) → [Fintype K] → [DecidableEq K] → (ζ : Type) →
      QStratQ K ζ (E ⊕ X) (O ⊕ X) d → ℝ≥0∞}
    (h : QRealizesQB R I b) (n : ℕ) (cut : X → O) :
    QRealizesQB (R.loopback n cut) (I.loopback n cut)
      fun K _ _ ζ Z => b K (ζ × QSys.FbPhase X) (QSys.fbEnv Z n cut idle) :=
  (QSys.loopbackCtx n cut idle).realizes_map (X := { H := H, τ := τ, sys := R })
    (Y := { H := H₁, τ := τ₁, sys := I }) ⟨oR, hR⟩ ⟨oI, hI⟩ h

end QRealizesQB

end CatCrypt.Quantum.ReactiveUC
