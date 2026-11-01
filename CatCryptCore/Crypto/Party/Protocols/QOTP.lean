/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Party.QProg
public import CatCryptCore.Crypto.Party.QProgWP
public import CatCryptCore.Crypto.Party.Category
public import CatCryptCore.Quantum.QOTPReactive
public import CatCryptCore.Quantum.QOTPInsecure

/-!
# The quantum one-time pad in the party language

The two quantum UC statements on the quantum one-time pad, with the real world, the ideal
functionality and the simulator written as quantum party programs (`Party.QProg`), loops of one
activation per iteration.

**Reactive quantum one-time pad** (`CatCryptCore.Quantum.QOTPReactive`).
*Ideal functionality*: the secure quantum channel `F_qsc n` on `n` qubits, the program
`Reactive.idealBody n`: on `send` it swaps the interface register into its buffer and leaks
the length `n`; on `deliver` it swaps the buffer back; on `drop` it aborts.
*Real protocol*: the key functionality, Alice, the authenticated quantum channel and Bob,
the program `QProg.qotpRealBody n`: on `send` Alice swaps the message into the buffer, a key
`k` is sampled and the buffer is encrypted by the Pauli operator `P_k`; on `deliver` Bob
decrypts and swaps the buffer out; on `steal` the adversary takes the ciphertext.
*Simulator*: the program `Reactive.simBody n` on the environment's register: it translates
`steal` to `drop`, the leak to `sent`, and on `aborted` applies the Pauli twirl to the
interface register.

**Insecure channel** (`CatCryptCore.Quantum.QOTPInsecure`).
*Ideal functionality*: the confidential quantum channel with Pauli tampering, the program
`Insecure.confBody n`: on `send` it swaps the message into its buffer and leaks the length;
on `deliver j` it applies `P_j` to the buffer and swaps it out.
*Real protocol*: the program `Insecure.realBody n`: on `send` a key `k` is sampled and the
interface register is encrypted by `P_k` (the insecure channel hands the ciphertext to the
adversary); on `deliver` Bob decrypts.
*Simulator*: the program `Insecure.simBody n` on the environment's register and `n` halves
of EPR pairs: on the leak it prepares the maximally entangled state, on `deliver` it measures in
the Bell basis and forwards the Pauli index.

Each program is related to the hand-written system by a step map at the embedding of states as
returned programs (`QProg.loopQSys_stepMap`, `QProg.simView_loopQSim`,
`QProg.simViewQ_loopQSimQ`); views are invariant under step maps (`QProg.qview_eq_of_stepMap`,
`QProg.qviewQ_eq_of_stepMap`), so the realizations transfer to the program forms. The loops
denote the hand-written systems in the category of quantum party programs `QPartyCat`.

Search words: party language, quantum one-time pad, quantum UC, quantum party program,
simulator, secure quantum channel, EPR simulator, step map.

## Main definitions

* `QProg.loopQSysP`, `QProg.loopQSim`, `QProg.loopQSimQ`: a loop of a quantum party program as
  a quantum system with a private register, and as a simulator without and with one.
* `QOTP.Reactive.idealBody`, `QOTP.Reactive.simBody`, and the systems `QOTP.Reactive.realP`,
  `QOTP.Reactive.idealP`, `QOTP.Reactive.simP`.
* `QOTP.Insecure.realBody`, `QOTP.Insecure.confBody`, `QOTP.Insecure.simBody`, and the systems
  `QOTP.Insecure.realP`, `QOTP.Insecure.confP`, `QOTP.Insecure.simP`.

## Main results

* `QProg.qview_eq_of_stepMap`, `QProg.qviewQ_eq_of_stepMap`: a step map with the same initial
  private basis state keeps the view of every environment.
* `QProg.simView_loopQSim`, `QProg.simViewQ_loopQSimQ`: a simulator program whose activations
  are the steps of a hand-written simulator gives the same simulated view.
* `QOTP.Reactive.ofLoop_realBody`, `QOTP.Reactive.ofLoop_idealBody`,
  `QOTP.Insecure.ofLoop_realBody`, `QOTP.Insecure.ofLoop_confBody`: the loops denote the
  hand-written worlds in `QPartyCat`.
* `QOTP.Reactive.qotpProg_realizesSim`: `QRealizesSim (realP n) (idealP n) (simP n) 0`.
* `QOTP.Insecure.qotpInsecureProg_realizesSimQ`:
  `QRealizesSimQ (realP n) (confP n) (simP n) 0`.
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace CatCrypt.Crypto.Party

open CatCrypt.Core _root_.Quantum CatCrypt.Quantum.ReactiveUC

namespace QProg

/-! ## Loops as systems and simulators, and the transfer of views -/

section Transfer

variable {R H M : Type} [Fintype R] [Fintype H] [DecidableEq H] [Fintype M] [DecidableEq M]
  {τ υ σ ζ E O EG OG : Type} {d : ℕ}

/-- **Loops of one activation as step maps.** When the activation of `body s` on every event
is the step `step s e` followed by a return, the embedding of states as returned programs is a
step map from the system with step `step` to the loop of `body`. -/
theorem loopQSys_stepMap (body : σ → QProg R E O σ) (s₀ : σ)
    (step : σ → E → SubInstrument R R (σ × O))
    (h : ∀ s e, act (body s) e =
      (step s e).bind fun q => SubInstrument.pure (ProgE.ret q.1, q.2)) :
    QRSys.StepMap ⟨s₀, step⟩ (loopQSys body s₀) ProgE.ret :=
  ⟨rfl, fun s e => by rw [loopQSys_step_ret, h]⟩

/-- The loop of `body` from `s₀` as a quantum system with interface register `Fin d` and
private register `H` started in the basis state `h₀`. -/
def loopQSysP (body : σ → QProg (Fin d × H) E O σ) (s₀ : σ) (h₀ : H) :
    QSys H (QProg (Fin d × H) E O σ) E O d where
  init := .ret s₀
  initReg := h₀
  step := (loopQSys body s₀).step

omit [DecidableEq H] in
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
theorem qview_eq_of_stepMap {S₁ : QSys H τ E O d} {S₂ : QSys H υ E O d} {f : τ → υ}
    (hr : S₁.initReg = S₂.initReg) (hf : QRSys.StepMap S₁.toQRSys S₂.toQRSys f)
    (Z : QStrat ζ E O d) : qview S₁ Z = qview S₂ Z := by
  have hi : S₂.init = f S₁.init := hf.init_map.symm
  simp only [qview, hr, hi, ← qloop_stepMap hf.step, SubInstrument.bind_assoc,
    SubInstrument.pure_bind]

omit [DecidableEq H] in
/-- A state map that commutes with the steps of two systems commutes with their joint runs
against an environment with memory. -/
theorem qloopQ_stepMap {K : Type} [Fintype K] {S₁ : QSys H τ E O d} {S₂ : QSys H υ E O d}
    {f : τ → υ}
    (hf : ∀ t e, (S₁.step t e).bind (fun p => SubInstrument.pure (f p.1, p.2)) = S₂.step (f t) e)
    (Z : QStratQ K ζ E O d) (n : ℕ) (z : ζ) (t : τ) :
    (qloopQ S₁ Z n (z, t)).bind (fun c => SubInstrument.pure (c.1, f c.2)) =
      qloopQ S₂ Z n (z, f t) := by
  induction n generalizing z t with
  | zero => exact SubInstrument.pure_bind _ _
  | succ n ih =>
    simp only [qloopQ, ← hf, SubInstrument.frame_bind, SubInstrument.frame_pure,
      SubInstrument.bind_assoc, SubInstrument.pure_bind, ih]

/-- **Views with memory are invariant under step maps.** -/
theorem qviewQ_eq_of_stepMap {K : Type} [Fintype K] [DecidableEq K] {S₁ : QSys H τ E O d}
    {S₂ : QSys H υ E O d} {f : τ → υ}
    (hr : S₁.initReg = S₂.initReg) (hf : QRSys.StepMap S₁.toQRSys S₂.toQRSys f)
    (Z : QStratQ K ζ E O d) : qviewQ S₁ Z = qviewQ S₂ Z := by
  have hi : S₂.init = f S₁.init := hf.init_map.symm
  simp only [qviewQ, hr, hi, ← qloopQ_stepMap hf.step, SubInstrument.bind_assoc,
    SubInstrument.pure_bind]

/-- **Simulated views are invariant under step maps of simulators.** -/
theorem simView_eq_of_simMap {σ₁ σ₂ : Type} {S₁ : QSim σ₁ E O EG OG d}
    {S₂ : QSim σ₂ E O EG OG d} (f : σ₁ → σ₂) (hi : f S₁.init = S₂.init)
    (hpre : ∀ s e, (S₁.pre s e).bind (fun b => SubInstrument.pure (f b.1, b.2)) =
      S₂.pre (f s) e)
    (hpost : ∀ s o, (S₁.post s o).bind (fun b => SubInstrument.pure (f b.1, b.2)) =
      S₂.post (f s) o)
    (I : QSys H υ EG OG d) (Z : QStrat ζ E O d) :
    simView I S₁ Z = simView I S₂ Z := by
  have h := qview_hom I (S₁.absorb Z) (S₂.absorb Z) (fun c => (c.1, f c.2)) rfl
    (by simp only [QSim.absorb, hi])
    (fun c => by
      simp only [QSim.absorb, ← hpre, SubInstrument.bind_assoc, SubInstrument.pure_bind])
    (fun c o => by
      simp only [QSim.absorb, ← hpost, SubInstrument.bind_assoc, SubInstrument.pure_bind])
  rw [simView, simView, ← h, SubInstrument.bind_assoc]
  simp only [SubInstrument.pure_bind]

/-- **Simulated views with memory are invariant under step maps of simulators.** -/
theorem simViewQ_eq_of_simMap {K : Type} [Fintype K] [DecidableEq K] {σ₁ σ₂ : Type}
    {S₁ : QSimQ M σ₁ E O EG OG d} {S₂ : QSimQ M σ₂ E O EG OG d} (f : σ₁ → σ₂)
    (hi : f S₁.init = S₂.init) (hr : S₁.initReg = S₂.initReg)
    (hpre : ∀ s e, (S₁.pre s e).bind (fun b => SubInstrument.pure (f b.1, b.2)) =
      S₂.pre (f s) e)
    (hpost : ∀ s o, (S₁.post s o).bind (fun b => SubInstrument.pure (f b.1, b.2)) =
      S₂.post (f s) o)
    (I : QSys H υ EG OG d) (Z : QStratQ K ζ E O d) :
    simViewQ I S₁ Z = simViewQ I S₂ Z := by
  have he : (Equiv.refl (Fin d)).prodCongr (Equiv.refl (K × M)) = Equiv.refl _ :=
    Equiv.ext fun _ => rfl
  have h := qviewQ_iso I (S₁.absorb Z) (S₂.absorb Z) (Equiv.refl _) (fun c => (c.1, f c.2)) rfl
    (by simp only [QSimQ.absorb, hi]) (by simp only [QSimQ.absorb, hr, Equiv.refl_apply])
    (fun c => by
      simp only [he, relabel_refl, QSimQ.absorb, placeRight, ← hpre,
        relabel_bind, relabel_pure, SubInstrument.frame_bind, SubInstrument.frame_pure,
        SubInstrument.bind_assoc, SubInstrument.pure_bind])
    (fun c o => by
      simp only [he, relabel_refl, QSimQ.absorb, placeRight, ← hpost,
        relabel_bind, relabel_pure, SubInstrument.frame_bind, SubInstrument.frame_pure,
        SubInstrument.bind_assoc, SubInstrument.pure_bind])
  rw [simViewQ, simViewQ, ← h, SubInstrument.bind_assoc]
  simp only [SubInstrument.pure_bind]

/-- The simulator of the loop of a quantum party program on the environment's register: an
activation on a real event `inl e` emits an ideal event `inl g`, an activation on an ideal
output `inr o` emits a real output `inr o'`; any other output fails. -/
def loopQSim (body : σ → QProg (Fin d) (E ⊕ OG) (EG ⊕ O) σ) (s₀ : σ) :
    QSim (QProg (Fin d) (E ⊕ OG) (EG ⊕ O) σ) E O EG OG d where
  init := .ret s₀
  pre t e := ((loopQSys body s₀).step t (.inl e)).bind fun x =>
    Sum.elim (fun g => SubInstrument.pure (x.1, g)) (fun _ => SubInstrument.fail) x.2
  post t o := ((loopQSys body s₀).step t (.inr o)).bind fun x =>
    Sum.elim (fun _ => SubInstrument.fail) (fun o' => SubInstrument.pure (x.1, o')) x.2

/-- The simulator of the loop of a quantum party program on the environment's register and a
private register `M` started in the basis state `m₀`. -/
def loopQSimQ (body : σ → QProg (Fin d × M) (E ⊕ OG) (EG ⊕ O) σ) (s₀ : σ) (m₀ : M) :
    QSimQ M (QProg (Fin d × M) (E ⊕ OG) (EG ⊕ O) σ) E O EG OG d where
  init := .ret s₀
  initReg := m₀
  pre t e := ((loopQSys body s₀).step t (.inl e)).bind fun x =>
    Sum.elim (fun g => SubInstrument.pure (x.1, g)) (fun _ => SubInstrument.fail) x.2
  post t o := ((loopQSys body s₀).step t (.inr o)).bind fun x =>
    Sum.elim (fun _ => SubInstrument.fail) (fun o' => SubInstrument.pure (x.1, o')) x.2

/-- **Simulator programs.** When every activation of `body s` is the step of the simulator
`S` followed by a return, the loop of `body` gives the same simulated view as `S`. -/
theorem simView_loopQSim (S : QSim σ E O EG OG d) (body : σ → QProg (Fin d) (E ⊕ OG) (EG ⊕ O) σ)
    (hpre : ∀ s e, act (body s) (.inl e) =
      (S.pre s e).bind fun b => SubInstrument.pure (ProgE.ret b.1, .inl b.2))
    (hpost : ∀ s o, act (body s) (.inr o) =
      (S.post s o).bind fun b => SubInstrument.pure (ProgE.ret b.1, .inr b.2))
    (I : QSys H υ EG OG d) (Z : QStrat ζ E O d) :
    simView I S Z = simView I (loopQSim body S.init) Z :=
  simView_eq_of_simMap ProgE.ret rfl
    (fun s e => by
      simp only [loopQSim, loopQSys_step_ret, hpre, SubInstrument.bind_assoc,
        SubInstrument.pure_bind, Sum.elim_inl])
    (fun s o => by
      simp only [loopQSim, loopQSys_step_ret, hpost, SubInstrument.bind_assoc,
        SubInstrument.pure_bind, Sum.elim_inr]) I Z

/-- **Simulator programs with a private register.** -/
theorem simViewQ_loopQSimQ {K : Type} [Fintype K] [DecidableEq K] (S : QSimQ M σ E O EG OG d)
    (body : σ → QProg (Fin d × M) (E ⊕ OG) (EG ⊕ O) σ)
    (hpre : ∀ s e, act (body s) (.inl e) =
      (S.pre s e).bind fun b => SubInstrument.pure (ProgE.ret b.1, .inl b.2))
    (hpost : ∀ s o, act (body s) (.inr o) =
      (S.post s o).bind fun b => SubInstrument.pure (ProgE.ret b.1, .inr b.2))
    (I : QSys H υ EG OG d) (Z : QStratQ K ζ E O d) :
    simViewQ I S Z = simViewQ I (loopQSimQ body S.init S.initReg) Z :=
  simViewQ_eq_of_simMap ProgE.ret rfl rfl
    (fun s e => by
      simp only [loopQSimQ, loopQSys_step_ret, hpre, SubInstrument.bind_assoc,
        SubInstrument.pure_bind, Sum.elim_inl])
    (fun s o => by
      simp only [loopQSimQ, loopQSys_step_ret, hpost, SubInstrument.bind_assoc,
        SubInstrument.pure_bind, Sum.elim_inr]) I Z

/-- A system is the loop system of a program with one activation per iteration, up to views. -/
theorem qview_loopQSysP (S : QSys H τ E O d) (body : τ → QProg (Fin d × H) E O τ)
    (h : ∀ s e, act (body s) e =
      (S.step s e).bind fun q => SubInstrument.pure (ProgE.ret q.1, q.2))
    (Z : QStrat ζ E O d) : qview S Z = qview (loopQSysP body S.init S.initReg) Z :=
  qview_eq_of_stepMap (S₁ := S) (S₂ := loopQSysP body S.init S.initReg) rfl
    (loopQSys_stepMap body S.init S.step h) Z

/-- A system is the loop system of a program with one activation per iteration, up to views
with memory. -/
theorem qviewQ_loopQSysP {K : Type} [Fintype K] [DecidableEq K] (S : QSys H τ E O d)
    (body : τ → QProg (Fin d × H) E O τ)
    (h : ∀ s e, act (body s) e =
      (S.step s e).bind fun q => SubInstrument.pure (ProgE.ret q.1, q.2))
    (Z : QStratQ K ζ E O d) : qviewQ S Z = qviewQ (loopQSysP body S.init S.initReg) Z :=
  qviewQ_eq_of_stepMap (S₁ := S) (S₂ := loopQSysP body S.init S.initReg) rfl
    (loopQSys_stepMap body S.init S.step h) Z

end Transfer

end QProg

namespace Protocols.QOTP

/-! ## The reactive quantum one-time pad -/

namespace Reactive

open CatCrypt.Quantum.QOTPReactive (Reg Key swapOp twirlOp Phase IPhase Event Out IEvent IOut
  realStep idealStep simEvent simPost qotpReal qotpIdeal qotpSim qotp_realizesSim)

variable {n : ℕ}

/-- The secure quantum channel `F_qsc n` as a loop body over its phase. -/
def idealBody (n : ℕ) : IPhase → QProg (Reg n × Reg n) IEvent IOut IPhase
  | .idle => do
    match ← ProgE.recvE with
    | .send =>
      QProg.opE (swapOp (Reg n))
      ProgE.sendE (.leak n)
      pure .sent
    | .deliver | .drop =>
      ProgE.sendE .ignored
      pure .idle
  | .sent => do
    match ← ProgE.recvE with
    | .send =>
      ProgE.sendE .ignored
      pure .sent
    | .deliver =>
      QProg.opE (swapOp (Reg n))
      ProgE.sendE .received
      pure .done
    | .drop =>
      ProgE.sendE .aborted
      pure .done
  | .done => do
    let _ ← ProgE.recvE
    ProgE.sendE .ignored
    pure .done

/-- The simulator of the reactive quantum one-time pad as a loop body on the environment's
register: real events are translated to ideal events, and on `aborted` the interface register
is twirled. -/
def simBody (n : ℕ) : Unit → QProg (Reg n) (Event ⊕ IOut) (IEvent ⊕ Out) Unit
  | () => do
    match ← ProgE.recvE with
    | .inl e => ProgE.sendE (.inl (simEvent e))
    | .inr (.leak _) => ProgE.sendE (.inr .sent)
    | .inr .received => ProgE.sendE (.inr .received)
    | .inr .aborted =>
      QProg.opE (twirlOp n)
      ProgE.sendE (.inr .aborted)
    | .inr .ignored => ProgE.sendE (.inr .ignored)

/-- An activation of the real-world program is the hand-written step. -/
theorem act_realBody (s : Phase n) (e : Event) :
    QProg.act (QProg.qotpRealBody n s) e =
      (realStep n s e).bind fun q => SubInstrument.pure (ProgE.ret q.1, q.2) := by
  cases s <;> cases e <;>
    simp [QProg.qotpRealBody, realStep, QProg.act_def, QProg.stepWith_def, ProgE.recvE,
      ProgE.sendE, QProg.opE, ProgE.bind, QProg.emitK_bind, QProg.emitK_op,
      SubInstrument.bind_assoc]

/-- An activation of the ideal-world program is the hand-written step. -/
theorem act_idealBody (s : IPhase) (e : IEvent) :
    QProg.act (idealBody n s) e =
      (idealStep n s e).bind fun q => SubInstrument.pure (ProgE.ret q.1, q.2) := by
  cases s <;> cases e <;>
    simp [idealBody, idealStep, QProg.act_def, QProg.stepWith_def, ProgE.recvE,
      ProgE.sendE, QProg.opE, ProgE.bind, QProg.emitK_bind, QProg.emitK_op,
      SubInstrument.bind_assoc]

/-- An activation of the simulator program on a real event is the hand-written translation. -/
theorem act_simBody_inl (s : Unit) (e : Event) :
    QProg.act (simBody n s) (.inl e) =
      ((qotpSim n).pre s e).bind fun b => SubInstrument.pure (ProgE.ret b.1, .inl b.2) := by
  simp [simBody, qotpSim, QProg.act_def, QProg.stepWith_def, ProgE.recvE, ProgE.sendE,
    ProgE.bind]

/-- An activation of the simulator program on an ideal output is the hand-written
translation. -/
theorem act_simBody_inr (s : Unit) (o : IOut) :
    QProg.act (simBody n s) (.inr o) =
      ((qotpSim n).post s o).bind fun b => SubInstrument.pure (ProgE.ret b.1, .inr b.2) := by
  cases o <;>
    simp [simBody, qotpSim, simPost, QProg.act_def, QProg.stepWith_def, ProgE.recvE,
      ProgE.sendE, QProg.opE, ProgE.bind, QProg.emitK_bind, QProg.emitK_op,
      SubInstrument.bind_assoc]

/-- The real world of the reactive quantum one-time pad as a party program. -/
abbrev realP (n : ℕ) := QProg.loopQSysP (QProg.qotpRealBody n) .idle (qotpReal n).initReg

/-- The secure quantum channel as a party program. -/
abbrev idealP (n : ℕ) := QProg.loopQSysP (idealBody n) .idle (qotpIdeal n).initReg

/-- The simulator of the reactive quantum one-time pad as a party program. -/
abbrev simP (n : ℕ) := QProg.loopQSim (simBody n) ()

/-- The loop of the real-world program denotes the hand-written real world in the category
of quantum party programs. -/
theorem ofLoop_realBody :
    (QPartyCat.toQRSys (Reg n × Reg n)).map (QPartyCat.ofLoop (QProg.qotpRealBody n) .idle) =
      ⟦⟨_, (qotpReal n).toQRSys⟩⟧ :=
  QPartyCat.toQRSys_map_ofLoop_of_act _ _ _ act_realBody

/-- The loop of the ideal-world program denotes the secure quantum channel in the category of
quantum party programs. -/
theorem ofLoop_idealBody :
    (QPartyCat.toQRSys (Reg n × Reg n)).map (QPartyCat.ofLoop (idealBody n) .idle) =
      ⟦⟨_, (qotpIdeal n).toQRSys⟩⟧ :=
  QPartyCat.toQRSys_map_ofLoop_of_act _ _ _ act_idealBody

/-- **The reactive quantum one-time pad in the party language.** The real-world program
realizes the secure quantum channel program behind the simulator program at distance `0`. -/
theorem qotpProg_realizesSim : QRealizesSim (realP n) (idealP n) (simP n) 0 := fun ζ =>
  quc_congr _ _ (qotp_realizesSim ζ)
    (funext fun Z => by rw [QProg.qview_loopQSysP (qotpReal n) _ act_realBody Z]; rfl)
    (funext fun Z => by
      rw [QProg.simView_loopQSim (qotpSim n) (simBody n) act_simBody_inl act_simBody_inr,
        simView, simView, QProg.qview_loopQSysP (qotpIdeal n) _ act_idealBody]
      rfl)

end Reactive

/-! ## The quantum one-time pad over an insecure channel -/

namespace Insecure

open CatCrypt.Quantum.QOTPReactive (Reg Key keyOp swapOp)
open CatCrypt.Quantum.QOTPInsecure (Phase IPhase Event Out IEvent IOut encI decI errQ eprOp bellOp
  noKey realStep confStep simPre simPost insReal confIdeal eprSim qotpInsecure_realizesSimQ)

variable {n : ℕ}

/-- The real world of the quantum one-time pad over an insecure channel as a loop body over
its phase. -/
def realBody (n : ℕ) : Phase n → QProg (Reg n × Reg n) Event Out (Phase n)
  | .idle => do
    match ← ProgE.recvE with
    | .send =>
      let k ← QProg.opE (keyOp n)
      QProg.opE (encI k)
      ProgE.sendE .sent
      pure (.sent k)
    | .deliver =>
      ProgE.sendE .ignored
      pure .idle
  | .sent k => do
    match ← ProgE.recvE with
    | .send =>
      ProgE.sendE .ignored
      pure (.sent k)
    | .deliver =>
      QProg.opE (decI k)
      ProgE.sendE .received
      pure .done
  | .done => do
    let _ ← ProgE.recvE
    ProgE.sendE .ignored
    pure .done

/-- The confidential quantum channel with Pauli tampering as a loop body over its phase. -/
def confBody (n : ℕ) : IPhase → QProg (Reg n × Reg n) (IEvent n) IOut IPhase
  | .idle => do
    match ← ProgE.recvE with
    | .send =>
      QProg.opE (swapOp (Reg n))
      ProgE.sendE (.leak n)
      pure .sent
    | .deliver _ =>
      ProgE.sendE .ignored
      pure .idle
  | .sent => do
    match ← ProgE.recvE with
    | .send =>
      ProgE.sendE .ignored
      pure .sent
    | .deliver j =>
      QProg.opE (errQ j)
      QProg.opE (swapOp (Reg n))
      ProgE.sendE .received
      pure .done
  | .done => do
    let _ ← ProgE.recvE
    ProgE.sendE .ignored
    pure .done

/-- The EPR simulator as a loop body on the environment's register and the simulator's
register: on the leak it prepares `n` EPR pairs, on `deliver` after the leak it measures in the
Bell basis and forwards the Pauli index. -/
def simBody (n : ℕ) :
    IPhase → QProg (Reg n × Reg n) (Event ⊕ IOut) (IEvent n ⊕ Out) IPhase
  | s => do
    match ← ProgE.recvE with
    | .inl .send =>
      ProgE.sendE (.inl .send)
      pure s
    | .inl .deliver =>
      match s with
      | .sent =>
        let j ← QProg.opE (bellOp n)
        ProgE.sendE (.inl (.deliver j))
        pure .done
      | .idle =>
        ProgE.sendE (.inl (.deliver (noKey n)))
        pure .idle
      | .done =>
        ProgE.sendE (.inl (.deliver (noKey n)))
        pure .done
    | .inr (.leak _) =>
      QProg.opE (eprOp n)
      ProgE.sendE (.inr .sent)
      pure .sent
    | .inr .received =>
      ProgE.sendE (.inr .received)
      pure s
    | .inr .ignored =>
      ProgE.sendE (.inr .ignored)
      pure s

/-- An activation of the real-world program is the hand-written step. -/
theorem act_realBody (s : Phase n) (e : Event) :
    QProg.act (realBody n s) e =
      (realStep n s e).bind fun q => SubInstrument.pure (ProgE.ret q.1, q.2) := by
  cases s <;> cases e <;>
    simp [realBody, realStep, QProg.act_def, QProg.stepWith_def, ProgE.recvE,
      ProgE.sendE, QProg.opE, ProgE.bind, QProg.emitK_bind, QProg.emitK_op,
      SubInstrument.bind_assoc]

/-- An activation of the ideal-world program is the hand-written step. -/
theorem act_confBody (s : IPhase) (e : IEvent n) :
    QProg.act (confBody n s) e =
      (confStep n s e).bind fun q => SubInstrument.pure (ProgE.ret q.1, q.2) := by
  cases s <;> cases e <;>
    simp [confBody, confStep, QProg.act_def, QProg.stepWith_def, ProgE.recvE,
      ProgE.sendE, QProg.opE, ProgE.bind, QProg.emitK_bind, QProg.emitK_op,
      SubInstrument.bind_assoc]

/-- An activation of the simulator program on a real event is the hand-written translation. -/
theorem act_simBody_inl (s : IPhase) (e : Event) :
    QProg.act (simBody n s) (.inl e) =
      ((eprSim n).pre s e).bind fun b => SubInstrument.pure (ProgE.ret b.1, .inl b.2) := by
  cases s <;> cases e <;>
    simp [simBody, eprSim, simPre, QProg.act_def, QProg.stepWith_def, ProgE.recvE,
      ProgE.sendE, QProg.opE, ProgE.bind, QProg.emitK_bind, QProg.emitK_op,
      SubInstrument.bind_assoc]

/-- An activation of the simulator program on an ideal output is the hand-written
translation. -/
theorem act_simBody_inr (s : IPhase) (o : IOut) :
    QProg.act (simBody n s) (.inr o) =
      ((eprSim n).post s o).bind fun b => SubInstrument.pure (ProgE.ret b.1, .inr b.2) := by
  cases s <;> cases o <;>
    simp [simBody, eprSim, simPost, QProg.act_def, QProg.stepWith_def, ProgE.recvE,
      ProgE.sendE, QProg.opE, ProgE.bind, QProg.emitK_bind, QProg.emitK_op,
      SubInstrument.bind_assoc]

/-- The real world over the insecure channel as a party program. -/
abbrev realP (n : ℕ) := QProg.loopQSysP (realBody n) .idle (insReal n).initReg

/-- The confidential quantum channel with Pauli tampering as a party program. -/
abbrev confP (n : ℕ) := QProg.loopQSysP (confBody n) .idle (confIdeal n).initReg

/-- The EPR simulator as a party program. -/
abbrev simP (n : ℕ) := QProg.loopQSimQ (simBody n) .idle (eprSim n).initReg

/-- The loop of the real-world program denotes the hand-written real world in the category
of quantum party programs. -/
theorem ofLoop_realBody :
    (QPartyCat.toQRSys (Reg n × Reg n)).map (QPartyCat.ofLoop (realBody n) .idle) =
      ⟦⟨_, (insReal n).toQRSys⟩⟧ :=
  QPartyCat.toQRSys_map_ofLoop_of_act _ _ _ act_realBody

/-- The loop of the ideal-world program denotes the confidential quantum channel in the
category of quantum party programs. -/
theorem ofLoop_confBody :
    (QPartyCat.toQRSys (Reg n × Reg n)).map (QPartyCat.ofLoop (confBody n) .idle) =
      ⟦⟨_, (confIdeal n).toQRSys⟩⟧ :=
  QPartyCat.toQRSys_map_ofLoop_of_act _ _ _ act_confBody

/-- **The quantum one-time pad over an insecure channel in the party language.** The
real-world program realizes the program of the confidential quantum channel with Pauli
tampering behind the EPR simulator program at distance `0`. -/
theorem qotpInsecureProg_realizesSimQ : QRealizesSimQ (realP n) (confP n) (simP n) 0 :=
  fun K _ _ ζ => quc_congr _ _ (qotpInsecure_realizesSimQ K ζ)
    (funext fun Z => by rw [QProg.qviewQ_loopQSysP (insReal n) _ act_realBody Z]; rfl)
    (funext fun Z => by
      rw [QProg.simViewQ_loopQSimQ (eprSim n) (simBody n) act_simBody_inl act_simBody_inr,
        simViewQ, simViewQ, QProg.qviewQ_loopQSysP (confIdeal n) _ act_confBody]
      rfl)

end Insecure

end Protocols.QOTP

end CatCrypt.Crypto.Party
