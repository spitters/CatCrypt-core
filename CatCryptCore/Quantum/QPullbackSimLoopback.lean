/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QPullbackFeedback
public import CatCryptCore.Quantum.QPullbackCascade

/-!
# Quantum feedback behind a simulator with a private register

Realization behind a simulator with a private register is preserved by the quantum loopback.
For a simulator `S` with private register `M` between the real interface `(E ⊕ X, O ⊕ X)` and
the ideal interface `(EG, OG)`, the **loopback simulator** `QSimQ.loopbackPullback S n cut idle`
is the pullback over environments with quantum memory that first pulls an outer environment
`Z` back along the feedback context (`QSys.fbEnv Z n cut idle`, which runs `n + 1` rounds per
round of `Z`) and then absorbs `S` into it. On systems it sends the ideal system `I` to the
loopback of `S.attachQ I`. A single-call simulator answers one ideal activation per real event,
while the loopback calls the system up to `n + 1` times per outer event; the loopback simulator
is therefore the simulator `S` run behind the pulled feedback environment, with memory register
`K × M` and state `(ζ × FbPhase X) × σ`.

The **composition theorem** (`QRealizesSimQB.loopback`): if `R` realizes `I` behind `S` with
bound `b`, and `R` and `S.attachQ I` are idle at the shared event `idle`, then for every
environment `Z` of the outer interface, the view of `Z` against the loopback of `R` is within
`b` at `QSys.fbEnv Z n cut idle` of the view of `I` behind `S` against the pulled feedback
environment, projected to the state of `Z`. It is the quantum analogue of the classical
`RealizesSim.loopback`, and it reduces to the system form `QRealizesQB.loopback` through
`QRealizesSimQB_iff_attachQ`.

Search words: quantum feedback, loopback, simulator, private register, composition theorem,
environment with quantum memory, pullback, idle event, cut-off.

## Main definitions

* `QSimQ.loopbackPullback`

## Main results

* `QSimQ.qviewQ_loopback_attachQ` — the view against the loopback of the attached system
* `QRealizesSimQB.loopback_attachQ` — the system form
* `QRealizesSimQB.loopback` — the simulator form
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace CatCrypt.Quantum.ReactiveUC

open _root_.Quantum
open CatCrypt.Crypto.UCTransport (QSysObj)
open scoped ENNReal

namespace QSimQ

variable {H M : Type} [Fintype H] [DecidableEq H] [Fintype M] [DecidableEq M]
variable {υ σ E O X EG OG : Type} {d : ℕ}

/-- The loopback simulator of `S` with fuel `n`, cut-off map `cut` and idle event `idle`, as a
pullback over environments with memory: on systems the loopback of the system behind `S`, on
environments `S` absorbed into the feedback environment `QSys.fbEnv Z n cut idle`. -/
def loopbackPullback (S : QSimQ M σ (E ⊕ X) (O ⊕ X) EG OG d) (n : ℕ) (cut : X → O)
    (idle : E ⊕ X) : QEnvPullbackQ EG OG E O d :=
  S.toQEnvPullbackQ.comp (QSys.loopbackCtx n cut idle)

/-- **View under the loopback behind a simulator.** If `S.attachQ I` is idle at `idle`, the view
of `Z` against its loopback is the view of `I` behind `S` against the feedback environment
pulled back from `Z`, projected to the state of `Z`. -/
theorem qviewQ_loopback_attachQ {K ζ : Type} [Fintype K] [DecidableEq K]
    (S : QSimQ M σ (E ⊕ X) (O ⊕ X) EG OG d) (I : QSys H υ EG OG d) {idle : E ⊕ X}
    {oI : O ⊕ X} (hI : (S.attachQ I).IdleAt idle oI) (n : ℕ) (cut : X → O)
    (Z : QStratQ K ζ E O d) :
    qviewQ ((S.attachQ I).loopback n cut) Z =
      (simViewQ I S (QSys.fbEnv Z n cut idle)).bind fun c => SubInstrument.pure c.1 := by
  refine ((S.loopbackPullback n cut idle).view_map (X := { H := H, τ := υ, sys := I })
    ⟨trivial, oI, hI⟩ Z).trans ?_
  simp only [simViewQ, SubInstrument.bind_assoc, SubInstrument.pure_bind]
  rfl

end QSimQ

namespace QRealizesSimQB

variable {H H' M : Type} [Fintype H] [DecidableEq H] [Fintype H'] [DecidableEq H'] [Fintype M]
  [DecidableEq M]
variable {τ υ σ E O X EG OG : Type} {d : ℕ}

/-- **Loopback behind a simulator, system form.** If `R` realizes `I` behind `S` with bound `b`,
and `R` and `S.attachQ I` are idle at `idle`, then the loopback of `R` realizes the loopback of
`S.attachQ I` with bound `b` at the pulled feedback environment. -/
theorem loopback_attachQ {R : QSys H τ (E ⊕ X) (O ⊕ X) d} {I : QSys H' υ EG OG d}
    {S : QSimQ M σ (E ⊕ X) (O ⊕ X) EG OG d} (idle : E ⊕ X) {oR oI : O ⊕ X}
    (hR : R.IdleAt idle oR) (hI : (S.attachQ I).IdleAt idle oI)
    {b : (K : Type) → [Fintype K] → [DecidableEq K] → (ζ : Type) →
      QStratQ K ζ (E ⊕ X) (O ⊕ X) d → ℝ≥0∞}
    (h : QRealizesSimQB R I S b) (n : ℕ) (cut : X → O) :
    QRealizesQB (R.loopback n cut) ((S.attachQ I).loopback n cut)
      fun K _ _ ζ Z => b K (ζ × QSys.FbPhase X) (QSys.fbEnv Z n cut idle) :=
  QRealizesQB.loopback idle hR hI ((QRealizesSimQB_iff_attachQ R I S b).1 h) n cut

/-- **Composition theorem for the quantum loopback behind a simulator.** If `R` realizes `I`
behind the simulator `S` with bound `b`, and `R` and `S.attachQ I` are idle at `idle`, then the
loopback of `R` realizes `I` behind the loopback simulator `S.loopbackPullback n cut idle`: for
every environment `Z`, the view of `Z` against `R.loopback n cut` is within `b` at the pulled
feedback environment of the view of `I` behind `S` against that environment, projected to the
state of `Z`. -/
theorem loopback {R : QSys H τ (E ⊕ X) (O ⊕ X) d} {I : QSys H' υ EG OG d}
    {S : QSimQ M σ (E ⊕ X) (O ⊕ X) EG OG d} (idle : E ⊕ X) {oR oI : O ⊕ X}
    (hR : R.IdleAt idle oR) (hI : (S.attachQ I).IdleAt idle oI)
    {b : (K : Type) → [Fintype K] → [DecidableEq K] → (ζ : Type) →
      QStratQ K ζ (E ⊕ X) (O ⊕ X) d → ℝ≥0∞}
    (h : QRealizesSimQB R I S b) (n : ℕ) (cut : X → O)
    (K : Type) [Fintype K] [DecidableEq K] (ζ : Type) (Z : QStratQ K ζ E O d) :
    cpDist (qviewQ (R.loopback n cut) Z)
        ((simViewQ I S (QSys.fbEnv Z n cut idle)).bind fun c => SubInstrument.pure c.1) ≤
      b K (ζ × QSys.FbPhase X) (QSys.fbEnv Z n cut idle) := by
  rw [← S.qviewQ_loopback_attachQ I hI n cut Z]
  exact loopback_attachQ idle hR hI h n cut K ζ Z

end QRealizesSimQB

end CatCrypt.Quantum.ReactiveUC
