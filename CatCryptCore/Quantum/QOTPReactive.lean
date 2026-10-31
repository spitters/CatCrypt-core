/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QRealizes
public import CatCryptCore.Quantum.PauliTwirl

/-!
# The reactive quantum one-time pad

The quantum one-time pad realizes the ideal secure quantum channel at distance `0`, as a
square of quantum reactive systems (`ReactiveUC.QRealizesSim`).

A message is an `n`-qubit register. The environment holds the interface register
`I = Fin (2 ^ n)`; the private register of each world is a buffer `Q = Fin (2 ^ n)`.

Real world `qotpReal n`. Its classical state holds the protocol phase and, after the first
`send`, the key `k ∈ (Fin 2 × Fin 2)ⁿ` (the key functionality samples it uniformly).
* `send`: Alice swaps `I ↔ Q`, so the buffer takes the environment's message, the key is
  sampled, and Alice applies the Pauli operator `P_k` to `Q`. Output `sent`.
* `deliver` (the authenticated channel passes `Q` to Bob): Bob applies `P_kᴴ` to `Q` and swaps
  `Q ↔ I`. Output `received`.
* `steal` (the adversary takes `Q` off the channel): swap `Q ↔ I`. Output `aborted`.

Ideal world `qotpIdeal n`, the secure quantum channel `F_qsc n`.
* `send`: swap `I ↔ Q` and leak the length `n`.
* `deliver`: swap `Q ↔ I`. Output `received`.
* `drop`: output `aborted`; the buffer is not touched.

Simulator `qotpSim n`. It translates `steal` to `drop`, the leak to `sent`, and on `aborted`
applies a uniformly random Pauli operator to `I`, which is the replacement channel onto the
maximally mixed state (`twirlOp_branch`).

The proof runs the two worlds in lockstep. In the phase after `send`, the real buffer is the
ideal buffer conjugated by `P_k`; averaged over the key, every later step agrees
(`keyRun_sent`): on `deliver` decryption inverts encryption, and on `steal` the stolen
ciphertext is the twirl of the buffer, while the content that the swap leaves in the buffer is
discarded at the end of the run (`swap_discard_twirl`).

## Main definitions

* `QOTPReactive.qotpReal n`, `QOTPReactive.qotpIdeal n`, `QOTPReactive.qotpSim n`

## Main results

* `QOTPReactive.qview_qotpReal` — the view of every environment is the same in both worlds
* `QOTPReactive.qotp_realizesSim` — `QRealizesSim (qotpReal n) (qotpIdeal n) (qotpSim n) 0`
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace CatCrypt.Quantum.QOTPReactive

open _root_.Quantum
open Matrix
open CatCrypt.Quantum.OpenSystem (frameLeft frameLeft_branch frameLeft_bind frameLeft_pure
  frame_bind_frameLeft_comm)
open CatCrypt.Quantum.ReactiveUC
open CatCrypt.Quantum.PauliTwirl (pauliFin conjTranspose_mul_pauliFin pauliFin_mul_conjTranspose
  pauliFin_twirl)
open scoped Kronecker

/-! ## Operations on a register -/

section Ops

variable {A N : Type} [Fintype A] [DecidableEq A] [Fintype N] [DecidableEq N]

omit [DecidableEq A] [DecidableEq N] in
/-- Operations on the two factors commute, with a continuation of both outcomes. -/
theorem frame_frameLeft_bind_comm {α β γ C : Type} [Fintype C] (p : SubInstrument A A α)
    (q : SubInstrument N N β) (f : α → β → SubInstrument (A × N) C γ) :
    (p.frame N).bind (fun a => (frameLeft q A).bind fun b => f a b) =
      (frameLeft q A).bind (fun b => (p.frame N).bind fun a => f a b) := by
  have h := congrArg (fun X => SubInstrument.bind X (fun ab => f ab.1 ab.2))
    (frame_bind_frameLeft_comm p q)
  simpa only [SubInstrument.bind_assoc, SubInstrument.pure_bind] using h

/-- The unitary channel `ρ ↦ U ρ Uᴴ` as a subinstrument with one outcome. -/
def unitaryOp (U : Matrix A A ℂ) (hU : Uᴴ * U = 1) : SubInstrument A A Unit :=
  SubInstrument.ofKraus (fun _ => U) (by simpa using hU)

/-- A unitary channel followed by its inverse is the identity. -/
theorem unitaryOp_bind_conjTranspose (U : Matrix A A ℂ) (hU : Uᴴ * U = 1)
    (hU' : Uᴴᴴ * Uᴴ = 1) :
    (unitaryOp U hU).bind (fun _ => unitaryOp Uᴴ hU') = SubInstrument.pure () := by
  refine DSubInstrument.ext <| funext fun u => LinearMap.ext fun ρ => ?_
  rw [SubInstrument.bind, DSubInstrument.branch_bind_apply_univ]
  simp [unitaryOp, Matrix.mul_assoc, ← Matrix.mul_assoc Uᴴ U, hU]

omit [DecidableEq A] in
/-- A unitary on the right factor followed by its inverse is the identity. -/
theorem frameLeft_unitaryOp_bind_inv {β C : Type} [Fintype C] (U : Matrix N N ℂ)
    (hU : Uᴴ * U = 1) (hU' : Uᴴᴴ * Uᴴ = 1) (f : Unit → SubInstrument (A × N) C β) :
    (frameLeft (unitaryOp U hU) A).bind
        (fun _ => (frameLeft (unitaryOp Uᴴ hU') A).bind f) = f () := by
  rw [← SubInstrument.bind_assoc, ← frameLeft_bind, unitaryOp_bind_conjTranspose, frameLeft_pure,
    SubInstrument.pure_bind]

/-- Discarding the right factor `N` of `A × N`, as a subinstrument with one outcome. -/
def discardOp : SubInstrument (A × N) A Unit :=
  (discardRight (A := A) (H := N)).bind fun _ => SubInstrument.pure ()

/-- The branch of `discardOp` is the partial trace over the right factor. -/
theorem discardOp_branch :
    (discardOp : SubInstrument (A × N) A Unit).branch () = MatrixMap.traceRight A N := by
  refine LinearMap.ext fun ρ => ?_
  rw [discardOp, SubInstrument.bind, DSubInstrument.branch_bind_apply_univ]
  ext a a'
  simp [discardRight, discardKraus, Matrix.mul_apply, Matrix.sum_apply]

/-- A continuation after `discardOp` acts on the partial trace. -/
theorem discardOp_bind_branch {β C : Type} [Fintype C] (f : Unit → SubInstrument A C β) (c : β)
    (ρ : Matrix (A × N) (A × N) ℂ) :
    ((discardOp : SubInstrument (A × N) A Unit).bind f).branch c ρ =
      (f ()).branch c (MatrixMap.traceRight A N ρ) := by
  rw [SubInstrument.bind, DSubInstrument.branch_bind_apply_univ]
  simp [discardOp_branch]

/-- An operation on the left factor followed by discarding the right factor is discarding the
right factor followed by the operation. -/
theorem frame_bind_discardOp {α β C : Type} [Fintype C] (W : SubInstrument A A α)
    (K : α → SubInstrument A C β) :
    (W.frame N).bind (fun a => discardOp.bind fun _ => K a) =
      discardOp.bind fun _ => W.bind K := by
  refine DSubInstrument.ext <| funext fun c => LinearMap.ext fun ρ => ?_
  have hL : ((W.frame N).bind fun a => discardOp.bind fun _ => K a).branch c ρ =
      ∑' a, (K a).branch c (W.branch a (MatrixMap.traceRight A N ρ)) := by
    rw [SubInstrument.bind, DSubInstrument.branch_bind_apply]
    refine tsum_congr fun a => ?_
    rw [discardOp_bind_branch, DSubInstrument.branch_frame_apply]
    exact congrArg _ (LinearMap.congr_fun (MatrixMap.traceRight_comp_amplify (W.branch a)) ρ)
  rw [hL, discardOp_bind_branch, SubInstrument.bind, DSubInstrument.branch_bind_apply]

/-- A unitary on the right factor is lost when the right factor is discarded. -/
theorem frameLeft_unitaryOp_bind_discardOp {β C : Type} [Fintype C] (U : Matrix N N ℂ)
    (hU : Uᴴ * U = 1) (f : Unit → SubInstrument A C β) :
    (frameLeft (unitaryOp U hU) A).bind (fun _ => discardOp.bind f) = discardOp.bind f := by
  refine DSubInstrument.ext <| funext fun c => LinearMap.ext fun ρ => ?_
  rw [SubInstrument.bind, DSubInstrument.branch_bind_apply_univ]
  simp only [Finset.univ_unique, Finset.sum_singleton, LinearMap.comp_apply,
    discardOp_bind_branch, frameLeft_branch, unitaryOp, DSubInstrument.branch_ofKraus_apply]
  exact congrArg _ (LinearMap.congr_fun
    (MatrixMap.traceRight_comp_amplifyLeft (MatrixMap.isTP_conj hU)) ρ)

/-- The permutation matrix of the swap of the two factors of `A × A`. -/
def swapMat (A : Type) [DecidableEq A] : Matrix (A × A) (A × A) ℂ :=
  Matrix.of fun x y => if y = x.swap then 1 else 0

/-- The swap of the two factors is unitary. -/
theorem swapMat_unitary : (swapMat A)ᴴ * swapMat A = 1 := by
  ext x y
  simp only [swapMat, conjTranspose_apply, of_apply, Matrix.mul_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single y.swap]
  · simp
  · intro b _ hb
    simp [show y ≠ b.swap from fun h => hb (by simp [h])]
  · simp

/-- The swap carries an operator on the right factor to the same operator on the left factor. -/
theorem swapMat_mul_one_kronecker (U : Matrix A A ℂ) :
    swapMat A * ((1 : Matrix A A ℂ) ⊗ₖ U) = (U ⊗ₖ (1 : Matrix A A ℂ)) * swapMat A := by
  ext ⟨a, b⟩ ⟨c, e⟩
  simp only [swapMat, Matrix.mul_apply, of_apply, Prod.swap_prod_mk, kroneckerMap_apply,
    Matrix.one_apply, ite_mul, one_mul, zero_mul, mul_ite, mul_zero, Fintype.sum_prod_type,
    Prod.mk.injEq, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq',
    Finset.mem_univ, ↓reduceIte, mul_one, ite_and]
  by_cases h : c = b <;> subst_vars <;> simp [Finset.sum_ite_eq, eq_comm]

/-- The swap of the two factors of `A × A`. -/
def swapOp (A : Type) [Fintype A] [DecidableEq A] : SubInstrument (A × A) (A × A) Unit :=
  unitaryOp (swapMat A) swapMat_unitary

end Ops

/-! ## The key, encryption and the twirl -/

section Key

variable (n : ℕ)

/-- A key of the `n`-qubit one-time pad: a pair of bits per qubit. -/
abbrev Key := Fin n → Fin 2 × Fin 2

/-- The weight of a key, `2⁻ⁿ`, as the amplitude of the uniform key. -/
abbrev amp : ℂ := (2 : ℂ)⁻¹ ^ n

/-- The squared amplitudes of the uniform key sum to `1`. -/
theorem card_key_mul_amp : (Fintype.card (Key n) : ℂ) * (amp n * amp n) = 1 := by
  simp only [Key, amp, Fintype.card_fun, Fintype.card_prod, Fintype.card_fin]
  rw [← mul_pow, Nat.cast_pow, ← mul_pow]
  norm_num

/-- `4ⁿ (2ⁿ)⁻¹ (2ⁿ)⁻¹ = 1`. -/
theorem four_pow_mul_inv : (4 : ℂ) ^ n * (((2 : ℂ) ^ n)⁻¹ * ((2 : ℂ) ^ n)⁻¹) = 1 := by
  rw [← mul_inv, ← mul_pow]
  norm_num

/-- The squared amplitudes of the uniform key sum to `1`, with the conjugate amplitude. -/
theorem card_key_amp_star : (Fintype.card (Key n) : ℂ) * (amp n * star (amp n)) = 1 := by
  rw [show star (amp n) = amp n by simp [amp], card_key_mul_amp]

/-- The register of an `n`-qubit message. -/
abbrev Reg := Fin (2 ^ n)

variable {n}

/-- Sampling the key uniformly, on the buffer register: the Kraus operators `2⁻ⁿ • 1`. -/
def keyH : SubInstrument (Reg n) (Reg n) (Key n) :=
  SubInstrument.ofKraus (fun _ => amp n • (1 : Matrix (Reg n) (Reg n) ℂ)) (by
    simp only [conjTranspose_smul, conjTranspose_one, Matrix.smul_mul, Matrix.mul_smul,
      Matrix.one_mul, smul_smul, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ]
    rw [card_key_amp_star, one_smul])

/-- Sampling the key and forgetting it is the identity. -/
theorem keyH_bind_pure : keyH.bind (fun _ => SubInstrument.pure ()) =
    (SubInstrument.pure () : SubInstrument (Reg n) (Reg n) Unit) := by
  refine DSubInstrument.ext <| funext fun u => LinearMap.ext fun ρ => ?_
  rw [SubInstrument.bind, DSubInstrument.branch_bind_apply_univ]
  cases u
  simp only [SubInstrument.branch_pure_self, LinearMap.id_comp, keyH,
    DSubInstrument.branch_ofKraus_apply, LinearMap.id_apply, Finset.sum_const,
    Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ]
  simp only [LinearMap.smul_apply, MatrixMap.conj_apply, conjTranspose_smul, conjTranspose_one,
    Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one, smul_smul]
  grind [card_key_amp_star, one_smul]

/-- Sampling the key, placed on the buffer of the world register. -/
abbrev keyOp (n : ℕ) : SubInstrument (Reg n × Reg n) (Reg n × Reg n) (Key n) :=
  frameLeft keyH (Reg n)

/-- Sampling the key and not using it is the identity. -/
theorem keyOp_bind_const {β C : Type} [Fintype C] (X : SubInstrument (Reg n × Reg n) C β) :
    (keyOp n).bind (fun _ => X) = X := by
  calc (keyOp n).bind (fun _ => X)
      = ((keyOp n).bind fun _ => frameLeft (SubInstrument.pure ()) (Reg n)).bind fun _ => X := by
        simp only [frameLeft_pure, SubInstrument.bind_assoc, SubInstrument.pure_bind]
    _ = X := by
        rw [keyOp, ← frameLeft_bind, keyH_bind_pure, frameLeft_pure, SubInstrument.pure_bind]

/-- Encryption under the key `k`: the Pauli operator `P_k` on the buffer. -/
abbrev encOp (k : Key n) : SubInstrument (Reg n × Reg n) (Reg n × Reg n) Unit :=
  frameLeft (unitaryOp (pauliFin k) (conjTranspose_mul_pauliFin k)) (Reg n)

/-- Decryption under the key `k`: the operator `P_kᴴ` on the buffer. -/
abbrev decOp (k : Key n) : SubInstrument (Reg n × Reg n) (Reg n × Reg n) Unit :=
  frameLeft (unitaryOp (pauliFin k)ᴴ (by simpa using pauliFin_mul_conjTranspose k)) (Reg n)

/-- The Pauli twirl on the register: a uniformly random Pauli operator, the outcome forgotten. -/
def twirlOp (n : ℕ) : SubInstrument (Reg n) (Reg n) Unit :=
  (SubInstrument.ofKraus (fun k : Key n => amp n • pauliFin k) (by
    simp only [conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
      conjTranspose_mul_pauliFin, Finset.sum_const, Finset.card_univ,
      ← Nat.cast_smul_eq_nsmul ℂ]
    rw [card_key_amp_star, one_smul])).bind fun _ => SubInstrument.pure ()

/-- The Pauli twirl is the replacement channel onto the maximally mixed state:
`σ ↦ 2⁻ⁿ tr σ • 1`. -/
theorem twirlOp_branch (σ : Matrix (Reg n) (Reg n) ℂ) :
    (twirlOp n).branch () σ = ((2 : ℂ)⁻¹ ^ n * σ.trace) • (1 : Matrix (Reg n) (Reg n) ℂ) := by
  rw [twirlOp, SubInstrument.bind, DSubInstrument.branch_bind_apply_univ]
  rw [← pauliFin_twirl σ]
  have h4 : ((2 : ℂ) ^ n)⁻¹ * ((2 : ℂ) ^ n)⁻¹ = ((4 : ℂ) ^ n)⁻¹ := by
    rw [← mul_inv, ← mul_pow]
    norm_num
  simp [smul_smul, Finset.smul_sum, h4]

/-- Key sampling, encryption of the buffer and the swap of the buffer into the interface is
the swap followed by the twirl of the interface. -/
theorem key_enc_swap {β C : Type} [Fintype C] (Y : SubInstrument (Reg n × Reg n) C β) :
    (keyOp n).bind (fun k => (encOp k).bind fun _ => (swapOp (Reg n)).bind fun _ => Y) =
      (swapOp (Reg n)).bind fun _ => ((twirlOp n).frame (Reg n)).bind fun _ => Y := by
  refine DSubInstrument.ext <| funext fun c => LinearMap.ext fun ρ => ?_
  simp only [twirlOp, SubInstrument.frame_bind, SubInstrument.frame_pure,
    SubInstrument.bind_assoc, SubInstrument.pure_bind]
  simp only [SubInstrument.bind, DSubInstrument.branch_bind_apply_univ, LinearMap.sum_apply,
    LinearMap.comp_apply, Finset.univ_unique, Finset.sum_singleton, keyOp, encOp, swapOp,
    unitaryOp, keyH, frameLeft_branch, DSubInstrument.branch_frame_apply,
    DSubInstrument.branch_ofKraus_apply, MatrixMap.amplifyLeft_conj, MatrixMap.amplify_conj]
  refine Finset.sum_congr rfl fun k _ => congrArg _ ?_
  have hK : swapMat (Reg n) *
      kroneckerMap (· * ·) (1 : Matrix (Reg n) (Reg n) ℂ) (pauliFin k) *
      kroneckerMap (· * ·) (1 : Matrix (Reg n) (Reg n) ℂ) (amp n • 1) =
      kroneckerMap (· * ·) (amp n • pauliFin k) (1 : Matrix (Reg n) (Reg n) ℂ) *
        swapMat (Reg n) := by
    rw [swapMat_mul_one_kronecker, Matrix.kronecker_smul, Matrix.smul_kronecker,
      Matrix.one_kronecker_one, Matrix.mul_smul, Matrix.mul_one, Matrix.smul_mul]
  simp only [MatrixMap.conj_apply, Matrix.mul_assoc]
  have h := congrArg (fun K => K * ρ * Kᴴ) hK
  simpa only [conjTranspose_mul, Matrix.mul_assoc] using h

/-- After the swap and the partial trace over the buffer, the twirl of the interface depends
only on the trace of the state, which the swap keeps. -/
theorem swap_discard_twirl {β C : Type} [Fintype C] (f : Unit → SubInstrument (Reg n) C β) :
    (swapOp (Reg n)).bind (fun _ => discardOp.bind fun _ => (twirlOp n).bind f) =
      discardOp.bind fun _ => (twirlOp n).bind f := by
  refine DSubInstrument.ext <| funext fun c => LinearMap.ext fun ρ => ?_
  rw [SubInstrument.bind, DSubInstrument.branch_bind_apply_univ]
  simp only [Finset.univ_unique, Finset.sum_singleton, LinearMap.comp_apply,
    discardOp_bind_branch]
  simp only [PUnit.default_eq_unit, swapOp, unitaryOp, DSubInstrument.branch_ofKraus_apply]
  rw [SubInstrument.bind, DSubInstrument.branch_bind_apply_univ]
  simp only [Finset.univ_unique, Finset.sum_singleton, LinearMap.comp_apply,
    PUnit.default_eq_unit, twirlOp_branch, MatrixMap.trace_traceRight,
    MatrixMap.trace_conj_apply, swapMat_unitary, Matrix.one_mul]

end Key

/-! ## The two worlds and the simulator -/

/-- Events of the real interface. -/
inductive Event
  /-- Alice sends the message in the interface register. -/
  | send
  /-- The adversary lets the channel deliver. -/
  | deliver
  /-- The adversary takes the buffer off the channel. -/
  | steal
  deriving DecidableEq

/-- Outputs of the real interface. -/
inductive Out
  /-- A message was sent. -/
  | sent
  /-- Bob received the message into the interface register. -/
  | received
  /-- Bob aborted. -/
  | aborted
  /-- The event had no effect. -/
  | ignored
  deriving DecidableEq

/-- Events of the ideal interface. -/
inductive IEvent
  /-- The sender inputs the message in the interface register. -/
  | send
  /-- The adversary lets the functionality deliver. -/
  | deliver
  /-- The adversary drops the message. -/
  | drop
  deriving DecidableEq

/-- Outputs of the ideal interface. -/
inductive IOut
  /-- The length of the message, leaked to the adversary. -/
  | leak (len : ℕ)
  /-- The receiver obtained the message into the interface register. -/
  | received
  /-- The receiver aborted. -/
  | aborted
  /-- The event had no effect. -/
  | ignored
  deriving DecidableEq

/-- Phases of the real world; after `send` the phase holds the key. -/
inductive Phase (n : ℕ)
  /-- Nothing sent. -/
  | idle
  /-- The encrypted message is in the buffer. -/
  | sent (k : Key n)
  /-- Delivered or stolen. -/
  | done

/-- Phases of the ideal world. -/
inductive IPhase
  /-- Nothing sent. -/
  | idle
  /-- The message is in the buffer. -/
  | sent
  /-- Delivered or dropped. -/
  | done

variable {n : ℕ}

/-- One activation of the real world. -/
def realStep (n : ℕ) :
    Phase n → Event → SubInstrument (Reg n × Reg n) (Reg n × Reg n) (Phase n × Out)
  | .idle, .send => (swapOp (Reg n)).bind fun _ => (keyOp n).bind fun k =>
      (encOp k).bind fun _ => SubInstrument.pure (.sent k, .sent)
  | .idle, .deliver => SubInstrument.pure (.idle, .ignored)
  | .idle, .steal => SubInstrument.pure (.idle, .ignored)
  | .sent k, .send => SubInstrument.pure (.sent k, .ignored)
  | .sent k, .deliver => (decOp k).bind fun _ => (swapOp (Reg n)).bind fun _ =>
      SubInstrument.pure (.done, .received)
  | .sent _, .steal => (swapOp (Reg n)).bind fun _ => SubInstrument.pure (.done, .aborted)
  | .done, .send => SubInstrument.pure (.done, .ignored)
  | .done, .deliver => SubInstrument.pure (.done, .ignored)
  | .done, .steal => SubInstrument.pure (.done, .ignored)

/-- The real world: the key functionality, Alice, the authenticated quantum channel with
`deliver` and `steal`, and Bob, with the channel buffer as private register. -/
def qotpReal (n : ℕ) : QSys (Reg n) (Phase n) Event Out (2 ^ n) where
  init := .idle
  initReg := ⟨0, Nat.two_pow_pos n⟩
  step := realStep n

/-- One activation of the ideal secure quantum channel. -/
def idealStep (n : ℕ) :
    IPhase → IEvent → SubInstrument (Reg n × Reg n) (Reg n × Reg n) (IPhase × IOut)
  | .idle, .send => (swapOp (Reg n)).bind fun _ => SubInstrument.pure (.sent, .leak n)
  | .idle, .deliver => SubInstrument.pure (.idle, .ignored)
  | .idle, .drop => SubInstrument.pure (.idle, .ignored)
  | .sent, .send => SubInstrument.pure (.sent, .ignored)
  | .sent, .deliver => (swapOp (Reg n)).bind fun _ => SubInstrument.pure (.done, .received)
  | .sent, .drop => SubInstrument.pure (.done, .aborted)
  | .done, .send => SubInstrument.pure (.done, .ignored)
  | .done, .deliver => SubInstrument.pure (.done, .ignored)
  | .done, .drop => SubInstrument.pure (.done, .ignored)

/-- The ideal secure quantum channel `F_qsc n`, with the buffer as private register. -/
def qotpIdeal (n : ℕ) : QSys (Reg n) IPhase IEvent IOut (2 ^ n) where
  init := .idle
  initReg := ⟨0, Nat.two_pow_pos n⟩
  step := idealStep n

/-- The simulator's translation of a real event. -/
def simEvent : Event → IEvent
  | .send => .send
  | .deliver => .deliver
  | .steal => .drop

/-- The simulator's translation of an ideal output: on `aborted` it twirls the interface
register. -/
def simPost (n : ℕ) : IOut → CPComp (2 ^ n) (Unit × Out)
  | .leak _ => SubInstrument.pure ((), .sent)
  | .received => SubInstrument.pure ((), .received)
  | .aborted => (twirlOp n).bind fun _ => SubInstrument.pure ((), .aborted)
  | .ignored => SubInstrument.pure ((), .ignored)

/-- The simulator of the quantum one-time pad. -/
def qotpSim (n : ℕ) : QSim Unit Event Out IEvent IOut (2 ^ n) where
  init := ()
  pre _ e := SubInstrument.pure ((), simEvent e)
  post _ o := simPost n o

/-- Unfolding lemma: the step of the real world. -/
theorem qotpReal_step : (qotpReal n).step = realStep n := rfl

/-- Unfolding lemma: the step of the ideal world. -/
theorem qotpIdeal_step : (qotpIdeal n).step = idealStep n := rfl

/-- Unfolding lemma: the simulator translates events without acting on the register. -/
theorem qotpSim_pre (s : Unit) (e : Event) :
    (qotpSim n).pre s e = SubInstrument.pure ((), simEvent e) := rfl

/-- Unfolding lemma: the simulator's translation of outputs. -/
theorem qotpSim_post (s : Unit) (o : IOut) : (qotpSim n).post s o = simPost n o := rfl

/-- Unfolding lemma: an event choice of the environment with the simulator absorbed. -/
theorem absorb_next {ζ : Type} (Z : QStrat ζ Event Out (2 ^ n)) (c : ζ × Unit) :
    ((qotpSim n).absorb Z).next c = (Z.next c.1).bind fun a =>
      ((qotpSim n).pre c.2 a.2).bind fun b => SubInstrument.pure ((a.1, b.1), b.2) := rfl

/-- Unfolding lemma: an observation of the environment with the simulator absorbed. -/
theorem absorb_obs {ζ : Type} (Z : QStrat ζ Event Out (2 ^ n)) (c : ζ × Unit) (og : IOut) :
    ((qotpSim n).absorb Z).obs c og = ((qotpSim n).post c.2 og).bind fun b =>
      (Z.obs c.1 b.2).bind fun z => SubInstrument.pure (z, b.1) := rfl

/-- After delivery or theft the real world ignores every event. -/
theorem realStep_done (e : Event) : realStep n .done e = SubInstrument.pure (.done, .ignored) := by
  cases e <;> rfl

/-- After delivery or a drop the ideal world ignores every event. -/
theorem idealStep_done (e : IEvent) :
    idealStep n .done e = SubInstrument.pure (.done, .ignored) := by
  cases e <;> rfl

/-! ## The runs of the two worlds -/

variable {ζ : Type} (Z : QStrat ζ Event Out (2 ^ n))

/-- The run of `Z` against the real world from a configuration, with the buffer discarded. -/
def realRun (m : ℕ) (c : ζ × Phase n) : SubInstrument (Reg n × Reg n) (Reg n) ζ :=
  (qloop (qotpReal n) Z m c).bind fun c' => discardOp.bind fun _ => SubInstrument.pure c'.1

/-- The run of `Z` behind the simulator against the ideal world, with the buffer discarded. -/
def idealRun (m : ℕ) (c : (ζ × Unit) × IPhase) : SubInstrument (Reg n × Reg n) (Reg n) ζ :=
  (qloop (qotpIdeal n) ((qotpSim n).absorb Z) m c).bind fun c' =>
    discardOp.bind fun _ => SubInstrument.pure c'.1.1

/-- The run of `Z` against a world that ignores every event. -/
def envLoop : ℕ → ζ → CPComp (2 ^ n) ζ
  | 0, z => SubInstrument.pure z
  | m + 1, z => (Z.next z).bind fun a => (Z.obs a.1 .ignored).bind fun z' => envLoop m z'

/-- After delivery or theft the real world ignores every event. -/
theorem realRun_done (m : ℕ) (z : ζ) :
    realRun Z m (z, .done) = discardOp.bind fun _ => envLoop Z m z := by
  induction m generalizing z with
  | zero => simp only [realRun, qloop, SubInstrument.pure_bind, envLoop]
  | succ m ih =>
    simp only [realRun] at ih ⊢
    simp only [qloop, qotpReal_step, realStep_done, SubInstrument.bind_assoc,
      SubInstrument.pure_bind, ih, frame_bind_discardOp, envLoop]

/-- After delivery or a drop the ideal world behind the simulator ignores every event. -/
theorem idealRun_done (m : ℕ) (z : ζ) :
    idealRun Z m ((z, ()), .done) = discardOp.bind fun _ => envLoop Z m z := by
  induction m generalizing z with
  | zero => simp only [idealRun, qloop, SubInstrument.pure_bind, envLoop]
  | succ m ih =>
    simp only [idealRun] at ih ⊢
    simp only [qloop, qotpIdeal_step, absorb_next, absorb_obs, qotpSim_pre, qotpSim_post,
      idealStep_done, simPost, SubInstrument.frame_bind, SubInstrument.frame_pure,
      SubInstrument.bind_assoc, SubInstrument.pure_bind, ih, frame_bind_discardOp, envLoop]

/-- After `send`, the real run averaged over the key, with the buffer encrypted, is the ideal
run behind the simulator. -/
theorem keyRun_sent (m : ℕ) (z : ζ) :
    (keyOp n).bind (fun k => (encOp k).bind fun _ => realRun Z m (z, .sent k)) =
      idealRun Z m ((z, ()), .sent) := by
  induction m generalizing z with
  | zero =>
    simp only [realRun, idealRun, qloop, SubInstrument.pure_bind, encOp,
      frameLeft_unitaryOp_bind_discardOp, keyOp_bind_const]
  | succ m ih =>
    simp only [realRun, idealRun] at ih ⊢
    simp only [qloop, qotpReal_step, qotpIdeal_step, absorb_next, absorb_obs, qotpSim_pre,
      qotpSim_post, SubInstrument.frame_bind, SubInstrument.frame_pure, SubInstrument.bind_assoc,
      SubInstrument.pure_bind, ← frame_frameLeft_bind_comm]
    refine congrArg _ (funext fun a => ?_)
    obtain ⟨z', e⟩ := a
    have hR := fun z => realRun_done Z m z
    have hI := fun z => idealRun_done Z m z
    simp only [realRun, idealRun] at hR hI
    cases e
    · simp only [realStep, idealStep, simEvent, simPost, SubInstrument.pure_bind,
        SubInstrument.frame_pure, ← frame_frameLeft_bind_comm, ih]
    · simp only [realStep, idealStep, simEvent, simPost, SubInstrument.pure_bind,
        SubInstrument.bind_assoc, SubInstrument.frame_pure, frameLeft_unitaryOp_bind_inv,
        keyOp_bind_const, hR, hI]
    · simp only [realStep, idealStep, simEvent, simPost, SubInstrument.pure_bind,
        SubInstrument.bind_assoc, SubInstrument.frame_bind, SubInstrument.frame_pure,
        key_enc_swap, hR, hI, frame_bind_discardOp, swap_discard_twirl]

/-- Before `send`, the real run is the ideal run behind the simulator. -/
theorem realRun_idle (m : ℕ) (z : ζ) :
    realRun Z m (z, .idle) = idealRun Z m ((z, ()), .idle) := by
  induction m generalizing z with
  | zero => simp only [realRun, idealRun, qloop, SubInstrument.pure_bind]
  | succ m ih =>
    have hS := fun z => keyRun_sent Z m z
    simp only [realRun, idealRun] at ih hS ⊢
    simp only [qloop, qotpReal_step, qotpIdeal_step, absorb_next, absorb_obs, qotpSim_pre,
      qotpSim_post, SubInstrument.frame_bind, SubInstrument.frame_pure, SubInstrument.bind_assoc,
      SubInstrument.pure_bind]
    refine congrArg _ (funext fun a => ?_)
    obtain ⟨z', e⟩ := a
    cases e
    · simp only [realStep, idealStep, simEvent, simPost, SubInstrument.pure_bind,
        SubInstrument.bind_assoc, SubInstrument.frame_pure, ← frame_frameLeft_bind_comm, hS]
    · simp only [realStep, idealStep, simEvent, simPost, SubInstrument.pure_bind,
        SubInstrument.frame_pure, ih]
    · simp only [realStep, idealStep, simEvent, simPost, SubInstrument.pure_bind,
        SubInstrument.frame_pure, ih]

/-- **The reactive quantum one-time pad.** The view of every environment against the real
world equals its view against the ideal secure channel behind the simulator. -/
theorem qview_qotpReal : qview (qotpReal n) Z = simView (qotpIdeal n) (qotpSim n) Z := by
  have h := realRun_idle Z Z.rounds Z.init
  simp only [realRun, idealRun, discardOp, SubInstrument.bind_assoc,
    SubInstrument.pure_bind] at h
  simp only [simView, qview, SubInstrument.bind_assoc, SubInstrument.pure_bind]
  exact congrArg _ (funext fun _ => h)

/-- The quantum one-time pad over the authenticated quantum channel realizes the ideal secure
quantum channel `F_qsc n` behind the simulator `qotpSim n` at distance `0`. -/
theorem qotp_realizesSim : QRealizesSim (qotpReal n) (qotpIdeal n) (qotpSim n) 0 := fun ζ =>
  quc_congr _ _ (QRealizes.refl (qotpReal n) ζ) rfl
    (funext fun Z => by rw [qview_qotpReal])

end CatCrypt.Quantum.QOTPReactive
