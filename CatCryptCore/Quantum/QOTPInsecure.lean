/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QRealizesMem
public import CatCryptCore.Quantum.QOTPReactive
public import CatCryptCore.Quantum.PauliTwirl

/-!
# The quantum one-time pad over an insecure channel

Over an insecure quantum channel the quantum one-time pad realizes a confidential quantum
channel with Pauli tampering at distance `0`, behind a simulator that holds `n` halves of EPR
pairs in its private register (`ReactiveUC.QRealizesSimQ`).

A message is an `n`-qubit register. The environment holds the interface register
`I = Fin (2 ^ n)`; the private register of each world is a buffer `Q = Fin (2 ^ n)`, and the
simulator's register is `B = Fin (2 ^ n)`.

Real world `insReal n`.
* `send`: the key `k ∈ (Fin 2 × Fin 2)ⁿ` is sampled uniformly and Alice applies the Pauli
  operator `P_k` to the message register. The insecure channel hands the ciphertext to the
  adversary: the ciphertext stays in the interface register. Output `sent`.
* `deliver`: the adversary delivers the interface register to Bob, who applies `P_kᴴ`.
  Output `received`.

Ideal world `confIdeal n`, the confidential quantum channel with Pauli tampering.
* `send`: swap `I ↔ Q` and leak the length `n`.
* `deliver j` (`j` a Pauli index chosen by the adversary): apply `P_j` to `Q` and swap
  `Q ↔ I`. Output `received`.

Simulator `eprSim n`. On the leak it prepares the maximally entangled state on `I × B`, so the
adversary holds one half of `n` EPR pairs in place of the ciphertext. On `deliver` it measures
`I × B` in the Bell basis `|Φ_j⟩ = (P_j ⊗ 1) |Φ⁺⟩` and forwards `deliver j`.

The proof compares the two worlds with the environment's memory `K` and the simulator register
`B` on the same register `(I × Q) × (K × B)` (`qviewQ_padMem` pads the real world's
environment). After `send`, every operation of the environment between `send` and `deliver`
is a linear map `V` on `I × K`; the two worlds agree after the partial trace over `Q × B` for
every such `V` (`twirl_epr_trace`, `deliver_trace`). The identity behind `deliver_trace` is
the four-point identity of the Pauli operators (`pauliFin_four_point`).

## Main definitions

* `QOTPInsecure.insReal n`, `QOTPInsecure.confIdeal n`, `QOTPInsecure.eprSim n`
* `QOTPInsecure.eprOp n`, `QOTPInsecure.bellOp n`

## Main results

* `QOTPInsecure.pauliFin_four_point`
* `QOTPInsecure.qotpInsecure_realizesSimQ` —
  `QRealizesSimQ (insReal n) (confIdeal n) (eprSim n) 0`
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace CatCrypt.Quantum.QOTPInsecure

open _root_.Quantum
open Matrix
open CatCrypt.Quantum.OpenSystem (frameLeft frameLeft_branch frameLeft_bind frameLeft_pure)
open CatCrypt.Quantum.ReactiveUC
open CatCrypt.Quantum.QOTPReactive (Key amp Reg keyH keyOp unitaryOp swapOp swapMat
  swapMat_unitary)
open CatCrypt.Quantum.PauliTwirl (pauli pauliN piOp piOp_apply pauliFin
  conjTranspose_mul_pauliFin pauliFin_mul_conjTranspose isTwirlFamily_pauliFin)

/-! ## The four-point identity of the Pauli operators -/

section FourPoint

/-- The entries of the one-qubit Pauli operator `X^a Z^b` as integers. -/
def pauliZ (a b i j : Fin 2) : ℤ :=
  if i = j + a then (-1) ^ (b.val * j.val) else 0

/-- The entries of `pauli a b` are the integers `pauliZ a b`. -/
theorem pauli_eq_cast (a b i j : Fin 2) : pauli a b i j = (pauliZ a b i j : ℂ) := by
  unfold pauli pauliZ
  by_cases h : i = j + a <;> simp [h]

/-- The one-qubit four-point identity of the Pauli operators. -/
theorem pauliZ_four_point (x x' i i' j j' u u' : Fin 2) :
    ∑ c : Fin 2 × Fin 2, pauliZ c.1 c.2 x i * pauliZ c.1 c.2 x' i' * pauliZ c.1 c.2 j u *
        pauliZ c.1 c.2 j' u' =
      ∑ c : Fin 2 × Fin 2, pauliZ c.1 c.2 i u * pauliZ c.1 c.2 i' u' * pauliZ c.1 c.2 x j *
        pauliZ c.1 c.2 x' j' := by
  simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
  revert x x' i i' j j' u u'
  decide

/-- The `n`-qubit four-point identity of the Pauli operators:
`∑ k, P_k x i P_k x' i' P_k j u P_k j' u' = ∑ k, P_k i u P_k i' u' P_k x j P_k x' j'`. -/
theorem pauliN_four_point {n : ℕ} (x x' i i' j j' u u' : Fin n → Fin 2) :
    ∑ k : Fin n → Fin 2 × Fin 2, pauliN k x i * pauliN k x' i' * pauliN k j u * pauliN k j' u' =
      ∑ k : Fin n → Fin 2 × Fin 2,
        pauliN k i u * pauliN k i' u' * pauliN k x j * pauliN k x' j' := by
  simp only [pauliN, piOp_apply, ← Finset.prod_mul_distrib]
  rw [← Fintype.prod_sum (fun l (c : Fin 2 × Fin 2) => pauli c.1 c.2 (x l) (i l) *
      pauli c.1 c.2 (x' l) (i' l) * pauli c.1 c.2 (j l) (u l) * pauli c.1 c.2 (j' l) (u' l)),
    ← Fintype.prod_sum (fun l (c : Fin 2 × Fin 2) => pauli c.1 c.2 (i l) (u l) *
      pauli c.1 c.2 (i' l) (u' l) * pauli c.1 c.2 (x l) (j l) * pauli c.1 c.2 (x' l) (j' l))]
  refine Finset.prod_congr rfl fun l _ => ?_
  simp only [pauli_eq_cast]
  exact_mod_cast pauliZ_four_point (x l) (x' l) (i l) (i' l) (j l) (j' l) (u l) (u' l)

/-- The four-point identity for the Pauli operators on `Fin (2 ^ n)`. -/
theorem pauliFin_four_point {n : ℕ} (x x' i i' j j' u u' : Fin (2 ^ n)) :
    ∑ k : Key n, pauliFin k x i * pauliFin k x' i' * pauliFin k j u * pauliFin k j' u' =
      ∑ k : Key n, pauliFin k i u * pauliFin k i' u' * pauliFin k x j * pauliFin k x' j' := by
  simp only [pauliFin, submatrix_apply]
  exact pauliN_four_point _ _ _ _ _ _ _ _

/-- The entries of the Pauli operators are real. -/
theorem star_pauliFin {n : ℕ} (k : Key n) (a b : Fin (2 ^ n)) :
    star (pauliFin k a b) = pauliFin k a b := by
  simp [pauliFin, pauliN, piOp_apply, pauli_eq_cast]

end FourPoint

/-! ## EPR pairs and the Bell measurement -/

section Bell

variable {n : ℕ}

/-- The amplitude `2^(-n/2)` of the maximally entangled state on `n` pairs of qubits. -/
def eprAmp (n : ℕ) : ℝ := (Real.sqrt (2 ^ n))⁻¹

/-- `eprAmp n ^ 2 = 2⁻ⁿ`. -/
theorem eprAmp_mul_self : (eprAmp n : ℂ) * (eprAmp n : ℂ) = ((2 : ℂ) ^ n)⁻¹ := by
  rw [← Complex.ofReal_mul, eprAmp, ← mul_inv, Real.mul_self_sqrt (by positivity)]
  push_cast
  rfl

/-- The Kraus operator `|Φ⁺⟩⟨c|` of the preparation of the maximally entangled state. -/
def eprKraus (c : Reg n × Reg n) : Matrix (Reg n × Reg n) (Reg n × Reg n) ℂ :=
  Matrix.of fun x y => if y = c ∧ x.1 = x.2 then (eprAmp n : ℂ) else 0

/-- The operators `eprKraus c` satisfy the completeness relation. -/
theorem eprKraus_complete :
    ∑ c : Reg n × Reg n, (eprKraus c)ᴴ * eprKraus c = 1 := by
  have hs : ∑ x : Reg n × Reg n, (if x.1 = x.2 then (eprAmp n : ℂ) * (eprAmp n : ℂ) else 0) =
      1 := by
    rw [Fintype.sum_prod_type]
    simp [eprAmp_mul_self]
  ext y y'
  simp only [Matrix.sum_apply, mul_apply, conjTranspose_apply, eprKraus, of_apply, one_apply]
  rw [Finset.sum_comm]
  by_cases h : y = y'
  · subst h
    simp only [↓reduceIte]
    rw [← hs]
    refine Finset.sum_congr rfl fun x _ => ?_
    by_cases hx : x.1 = x.2 <;> simp [hx, Complex.conj_ofReal]
  · simp [h, apply_ite (star : ℂ → ℂ), ite_and]

/-- Preparing the maximally entangled state `|Φ⁺⟩ = 2^(-n/2) ∑ x |x, x⟩` on two `n`-qubit
registers, replacing their content. -/
def eprOp (n : ℕ) : SubInstrument (Reg n × Reg n) (Reg n × Reg n) Unit :=
  (SubInstrument.ofKraus eprKraus eprKraus_complete).bind fun _ => SubInstrument.pure ()

/-- The projector `|Φ_j⟩⟨Φ_j|` onto the Bell state `|Φ_j⟩ = (P_j ⊗ 1) |Φ⁺⟩`. -/
def bellProj (j : Key n) : Matrix (Reg n × Reg n) (Reg n × Reg n) ℂ :=
  Matrix.of fun x y => ((2 : ℂ) ^ n)⁻¹ * (pauliFin j x.1 x.2 * star (pauliFin j y.1 y.2))

/-- The Bell projectors are self-adjoint. -/
theorem conjTranspose_bellProj (j : Key n) : (bellProj j)ᴴ = bellProj j := by
  ext x y
  simp [bellProj, conjTranspose_apply, mul_comm]

/-- The Bell projectors are idempotent. -/
theorem bellProj_mul_self (j : Key n) : bellProj j * bellProj j = bellProj j := by
  have htr : ∑ z : Reg n × Reg n, star (pauliFin j z.1 z.2) * pauliFin j z.1 z.2 =
      (2 : ℂ) ^ n := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    have h1 : ∀ b : Reg n, ∑ a : Reg n, star (pauliFin j a b) * pauliFin j a b = 1 := by
      intro b
      have := congrFun (congrFun (conjTranspose_mul_pauliFin j) b) b
      simpa [mul_apply, conjTranspose_apply] using this
    rw [Finset.sum_congr rfl fun b _ => h1 b]
    simp
  ext x y
  simp only [bellProj, mul_apply, of_apply]
  have : ∀ z : Reg n × Reg n,
      ((2 : ℂ) ^ n)⁻¹ * (pauliFin j x.1 x.2 * star (pauliFin j z.1 z.2)) *
        (((2 : ℂ) ^ n)⁻¹ * (pauliFin j z.1 z.2 * star (pauliFin j y.1 y.2))) =
      ((2 : ℂ) ^ n)⁻¹ * ((2 : ℂ) ^ n)⁻¹ * (pauliFin j x.1 x.2 * star (pauliFin j y.1 y.2)) *
        (star (pauliFin j z.1 z.2) * pauliFin j z.1 z.2) := fun z => by ring
  simp only [this, ← Finset.mul_sum, htr]
  field_simp

/-- The Bell projectors sum to the identity. -/
theorem sum_bellProj : ∑ j : Key n, bellProj j = 1 := by
  ext x y
  have h := isTwirlFamily_pauliFin n x.1 x.2 y.1 y.2
  simp only [Matrix.sum_apply, bellProj, of_apply, ← Finset.mul_sum, h, one_apply, Prod.ext_iff]
  split_ifs <;> simp

/-- The Bell projectors satisfy the completeness relation. -/
theorem bellProj_complete : ∑ j : Key n, (bellProj j)ᴴ * bellProj j = 1 := by
  simp only [conjTranspose_bellProj, bellProj_mul_self, sum_bellProj]

/-- The Bell measurement on two `n`-qubit registers, with outcome the Pauli index `j` of the
Bell state `|Φ_j⟩`. -/
def bellOp (n : ℕ) : SubInstrument (Reg n × Reg n) (Reg n × Reg n) (Key n) :=
  SubInstrument.ofKraus bellProj bellProj_complete

end Bell

/-! ## The two worlds and the simulator -/

/-- Events of the real interface. -/
inductive Event
  /-- Alice sends the message in the interface register. -/
  | send
  /-- The adversary delivers the interface register to Bob. -/
  | deliver
  deriving DecidableEq

/-- Outputs of the real interface. -/
inductive Out
  /-- A message was sent. -/
  | sent
  /-- Bob received the message into the interface register. -/
  | received
  /-- The event had no effect. -/
  | ignored
  deriving DecidableEq

/-- Events of the ideal interface. -/
inductive IEvent (n : ℕ)
  /-- The sender inputs the message in the interface register. -/
  | send
  /-- The adversary lets the functionality deliver the message with the Pauli error `P_j`. -/
  | deliver (j : Key n)

/-- Outputs of the ideal interface. -/
inductive IOut
  /-- The length of the message, leaked to the adversary. -/
  | leak (len : ℕ)
  /-- The receiver obtained the message into the interface register. -/
  | received
  /-- The event had no effect. -/
  | ignored

/-- Phases of the real world; after `send` the phase holds the key. -/
inductive Phase (n : ℕ)
  /-- Nothing sent. -/
  | idle
  /-- The ciphertext is with the adversary. -/
  | sent (k : Key n)
  /-- Delivered. -/
  | done

/-- Phases of the ideal world and of the simulator. -/
inductive IPhase
  /-- Nothing sent. -/
  | idle
  /-- The message is in the buffer. -/
  | sent
  /-- Delivered. -/
  | done

variable {n : ℕ}

/-- Encryption under the key `k`: the Pauli operator `P_k` on the interface register. -/
abbrev encI (k : Key n) : SubInstrument (Reg n × Reg n) (Reg n × Reg n) Unit :=
  (unitaryOp (pauliFin k) (conjTranspose_mul_pauliFin k)).frame (Reg n)

/-- Decryption under the key `k`: the operator `P_kᴴ` on the interface register. -/
abbrev decI (k : Key n) : SubInstrument (Reg n × Reg n) (Reg n × Reg n) Unit :=
  (unitaryOp (pauliFin k)ᴴ (by simpa using pauliFin_mul_conjTranspose k)).frame (Reg n)

/-- The Pauli error `P_j` on the buffer. -/
abbrev errQ (j : Key n) : SubInstrument (Reg n × Reg n) (Reg n × Reg n) Unit :=
  frameLeft (unitaryOp (pauliFin j) (conjTranspose_mul_pauliFin j)) (Reg n)

/-- One activation of the real world. -/
def realStep (n : ℕ) :
    Phase n → Event → SubInstrument (Reg n × Reg n) (Reg n × Reg n) (Phase n × Out)
  | .idle, .send => (keyOp n).bind fun k => (encI k).bind fun _ =>
      SubInstrument.pure (.sent k, .sent)
  | .idle, .deliver => SubInstrument.pure (.idle, .ignored)
  | .sent k, .send => SubInstrument.pure (.sent k, .ignored)
  | .sent k, .deliver => (decI k).bind fun _ => SubInstrument.pure (.done, .received)
  | .done, _ => SubInstrument.pure (.done, .ignored)

/-- The real world: the key functionality, Alice, the insecure quantum channel and Bob. The
buffer is the private register; the insecure channel hands the ciphertext to the adversary,
whose register is the interface register. -/
def insReal (n : ℕ) : QSys (Reg n) (Phase n) Event Out (2 ^ n) where
  init := .idle
  initReg := ⟨0, Nat.two_pow_pos n⟩
  step := realStep n

/-- One activation of the confidential quantum channel with Pauli tampering. -/
def confStep (n : ℕ) :
    IPhase → IEvent n → SubInstrument (Reg n × Reg n) (Reg n × Reg n) (IPhase × IOut)
  | .idle, .send => (swapOp (Reg n)).bind fun _ => SubInstrument.pure (.sent, .leak n)
  | .idle, .deliver _ => SubInstrument.pure (.idle, .ignored)
  | .sent, .send => SubInstrument.pure (.sent, .ignored)
  | .sent, .deliver j => (errQ j).bind fun _ => (swapOp (Reg n)).bind fun _ =>
      SubInstrument.pure (.done, .received)
  | .done, _ => SubInstrument.pure (.done, .ignored)

/-- The confidential quantum channel with Pauli tampering, with the buffer as private
register. -/
def confIdeal (n : ℕ) : QSys (Reg n) IPhase (IEvent n) IOut (2 ^ n) where
  init := .idle
  initReg := ⟨0, Nat.two_pow_pos n⟩
  step := confStep n

/-- The Pauli index forwarded with an event that the ideal world ignores. -/
def noKey (n : ℕ) : Key n := fun _ => (0, 0)

/-- The simulator's translation of a real event: after the leak, `deliver` is answered by the
Bell measurement of the interface register and the simulator register. -/
def simPre (n : ℕ) :
    IPhase → Event → SubInstrument (Reg n × Reg n) (Reg n × Reg n) (IPhase × IEvent n)
  | s, .send => SubInstrument.pure (s, .send)
  | .sent, .deliver => (bellOp n).bind fun j => SubInstrument.pure (.done, .deliver j)
  | .idle, .deliver => SubInstrument.pure (.idle, .deliver (noKey n))
  | .done, .deliver => SubInstrument.pure (.done, .deliver (noKey n))

/-- The simulator's translation of an ideal output: on the leak it prepares the maximally
entangled state on the interface register and the simulator register. -/
def simPost (n : ℕ) :
    IPhase → IOut → SubInstrument (Reg n × Reg n) (Reg n × Reg n) (IPhase × Out)
  | _, .leak _ => (eprOp n).bind fun _ => SubInstrument.pure (.sent, .sent)
  | s, .received => SubInstrument.pure (s, .received)
  | s, .ignored => SubInstrument.pure (s, .ignored)

/-- The simulator with `n` halves of EPR pairs in its private register. -/
def eprSim (n : ℕ) : QSimQ (Reg n) IPhase Event Out (IEvent n) IOut (2 ^ n) where
  init := .idle
  initReg := ⟨0, Nat.two_pow_pos n⟩
  pre := simPre n
  post := simPost n

/-! ## Padding the environment's memory with an unused register -/

section PadMem

variable {H K B : Type} [Fintype H] [DecidableEq H] [Fintype K] [DecidableEq K] [Fintype B]
  [DecidableEq B] {τ ζ E O : Type} {d : ℕ}

/-- The environment `Z` with its memory extended by a register `B` that it does not touch,
prepared in the basis state `b₀`. -/
def padMem (Z : QStratQ K ζ E O d) (B : Type) [Fintype B] (b₀ : B) : QStratQ (K × B) ζ E O d where
  rounds := Z.rounds
  init := Z.init
  initReg := (Z.initReg, b₀)
  next z := placeLeft K B (Z.next z)
  obs z o := placeLeft K B (Z.obs z o)

omit [DecidableEq H] [DecidableEq K] [DecidableEq B] in
/-- The run against the padded environment is the run against `Z`, beside the unused
register. -/
theorem qloopQ_padMem (S : QSys H τ E O d) (Z : QStratQ K ζ E O d) (b₀ : B) (m : ℕ)
    (c : ζ × τ) :
    qloopQ S (padMem Z B b₀) m c =
      relabel (Equiv.prodAssoc (Fin d × H) K B) ((qloopQ S Z m c).frame B) := by
  have hE : ∀ {α : Type} (w : SubInstrument (Fin d × K) (Fin d × K) α),
      envPlace H (placeLeft K B w) =
        relabel (Equiv.prodAssoc (Fin d × H) K B) ((envPlace H w).frame B) := by
    intro α w
    simp only [envPlace, placeLeft, frame_relabel, frame_frame, relabel_relabel]
    rfl
  have hW : ∀ {α : Type} (x : SubInstrument (Fin d × H) (Fin d × H) α),
      x.frame (K × B) = relabel (Equiv.prodAssoc (Fin d × H) K B) ((x.frame K).frame B) := by
    intro α x
    rw [frame_frame, relabel_relabel, relabel_of_forall_eq _ fun _ => rfl]
  have hn : ∀ z, (padMem Z B b₀).next z = placeLeft K B (Z.next z) := fun _ => rfl
  have ho : ∀ z o, (padMem Z B b₀).obs z o = placeLeft K B (Z.obs z o) := fun _ _ => rfl
  induction m generalizing c with
  | zero => simp only [qloopQ, SubInstrument.frame_pure, relabel_pure]
  | succ m ih =>
    simp only [qloopQ, hn, ho, hE, hW, ih, SubInstrument.frame_bind, relabel_bind]

omit [DecidableEq H] in
/-- Preparing a pair of basis states, running a subinstrument beside the second register and
discarding both registers is preparing the first basis state, running the subinstrument and
discarding the first register. -/
theorem appendBasis_pair_discard {A C : Type} [Fintype A] [DecidableEq A] [Fintype C]
    {γ β : Type} (k₀ : K) (b₀ : B) (X : SubInstrument (A × K) (A × K) γ)
    (g : γ → SubInstrument A C β) :
    (appendBasis (k₀, b₀)).bind (fun _ => (relabel (Equiv.prodAssoc A K B) (X.frame B)).bind
      fun c => discardRight.bind fun _ => g c) =
    (appendBasis k₀).bind (fun _ => X.bind fun c => discardRight.bind fun _ => g c) := by
  refine DSubInstrument.ext <| funext fun b => LinearMap.ext fun ρ => ?_
  have hY : ∀ b' : B, (((appendBasis (k₀, b₀)).branch () ρ).submatrix
      (Equiv.prodAssoc A K B) (Equiv.prodAssoc A K B)).submatrix (·, b') (·, b') =
      if b' = b₀ then (appendBasis k₀).branch () ρ else 0 := by
    intro b'
    ext x y
    by_cases hb : b' = b₀
    · subst hb
      simp [appendBasis_branch_apply]
    · simp [appendBasis_branch_apply, hb]
  rw [DSubInstrument.branch_bind_apply, DSubInstrument.branch_bind_apply]
  refine tsum_congr fun u => ?_
  cases u
  rw [DSubInstrument.branch_bind_apply, DSubInstrument.branch_bind_apply]
  refine tsum_congr fun c => ?_
  rw [DSubInstrument.branch_bind_apply, DSubInstrument.branch_bind_apply, tsum_fintype,
    tsum_fintype, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun k _ => ?_
  have hblk : ∀ b' : B, (discardRight (A := A)).branch (k, b')
      ((relabel (Equiv.prodAssoc A K B) (X.frame B)).branch c
        ((appendBasis (k₀, b₀)).branch () ρ)) =
      if b' = b₀ then (discardRight (A := A)).branch k (X.branch c ((appendBasis k₀).branch () ρ))
      else 0 := by
    intro b'
    rw [discardRight_branch_apply, discardRight_branch_apply]
    have h := hY b'
    by_cases hb : b' = b₀
    · subst hb
      simp only [↓reduceIte] at h
      ext a a'
      simp only [submatrix_apply, relabel_branch, reindexMap_apply,
        DSubInstrument.branch_frame_apply, MatrixMap.amplify_apply, ↓reduceIte]
      rw [← h]
      rfl
    · simp only [hb, ↓reduceIte] at h
      ext a a'
      simp only [submatrix_apply, relabel_branch, reindexMap_apply,
        DSubInstrument.branch_frame_apply, MatrixMap.amplify_apply, hb, ↓reduceIte]
      simp_all
  simp only [hblk, apply_ite, map_zero, Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]

/-- Padding the environment's memory with an unused register does not change its view. -/
theorem qviewQ_padMem (S : QSys H τ E O d) (Z : QStratQ K ζ E O d) (b₀ : B) :
    qviewQ S (padMem Z B b₀) = qviewQ S Z := by
  simp only [qviewQ, qloopQ_padMem]
  exact congrArg _ (funext fun _ => appendBasis_pair_discard _ _ _ _)

end PadMem

/-! ## Operations on the joint register

The joint register is `(I × Q) × (K × B)`: the interface register `I`, the buffer `Q`, the
environment's memory `K` and the simulator register `B`. -/

section Joint

variable {K : Type} [Fintype K] {α : Type}

/-- The joint register `(I × Q) × (K × B)`. -/
abbrev Joint (n : ℕ) (K : Type) := (Reg n × Reg n) × (K × Reg n)

/-- An operation of the environment on `I × K`, placed on the joint register. -/
abbrev envOp (w : SubInstrument (Reg n × K) (Reg n × K) α) :
    SubInstrument (Joint n K) (Joint n K) α :=
  envPlace (Reg n) (placeLeft K (Reg n) w)

/-- An operation of the simulator on `I × B`, placed on the joint register. -/
abbrev simOp (s : SubInstrument (Reg n × Reg n) (Reg n × Reg n) α) :
    SubInstrument (Joint n K) (Joint n K) α :=
  envPlace (Reg n) (placeRight K (Reg n) s)

/-- An operation of a world on `I × Q`, placed on the joint register. -/
abbrev worldOp (x : SubInstrument (Reg n × Reg n) (Reg n × Reg n) α) :
    SubInstrument (Joint n K) (Joint n K) α :=
  x.frame (K × Reg n)

/-- The block of a joint operator seen by the environment at `(q, b)`, `(q', b')`. -/
def envBlock (q b q' : Reg n) (b' : Reg n) (ρ : Matrix (Joint n K) (Joint n K) ℂ) :
    Matrix (Reg n × K) (Reg n × K) ℂ :=
  Matrix.of fun x y => ρ ((x.1, q), (x.2, b)) ((y.1, q'), (y.2, b'))

/-- The block of a joint operator seen by the simulator at `(q, κ)`, `(q', κ')`. -/
def simBlock (q : Reg n) (κ : K) (q' : Reg n) (κ' : K) (ρ : Matrix (Joint n K) (Joint n K) ℂ) :
    Matrix (Reg n × Reg n) (Reg n × Reg n) ℂ :=
  Matrix.of fun x y => ρ ((x.1, q), (κ, x.2)) ((y.1, q'), (κ', y.2))

/-- The block of a joint operator seen by a world at `r`, `r'`. -/
def worldBlock (r r' : K × Reg n) (ρ : Matrix (Joint n K) (Joint n K) ℂ) :
    Matrix (Reg n × Reg n) (Reg n × Reg n) ℂ :=
  Matrix.of fun x y => ρ (x, r) (y, r')

/-- Entries of a placed environment operation. -/
theorem envOp_branch_apply (w : SubInstrument (Reg n × K) (Reg n × K) α) (a : α)
    (ρ : Matrix (Joint n K) (Joint n K) ℂ) (i q : Reg n) (κ : K) (b i' q' : Reg n) (κ' : K)
    (b' : Reg n) :
    (envOp w).branch a ρ ((i, q), (κ, b)) ((i', q'), (κ', b')) =
      w.branch a (envBlock q b q' b' ρ) (i, κ) (i', κ') :=
  rfl

/-- Entries of a placed simulator operation. -/
theorem simOp_branch_apply (s : SubInstrument (Reg n × Reg n) (Reg n × Reg n) α) (a : α)
    (ρ : Matrix (Joint n K) (Joint n K) ℂ) (i q : Reg n) (κ : K) (b i' q' : Reg n) (κ' : K)
    (b' : Reg n) :
    (simOp s).branch a ρ ((i, q), (κ, b)) ((i', q'), (κ', b')) =
      s.branch a (simBlock q κ q' κ' ρ) (i, b) (i', b') :=
  rfl

/-- Entries of a placed world operation. -/
theorem worldOp_branch_apply (x : SubInstrument (Reg n × Reg n) (Reg n × Reg n) α) (a : α)
    (ρ : Matrix (Joint n K) (Joint n K) ℂ) (u : Reg n × Reg n) (r : K × Reg n)
    (u' : Reg n × Reg n) (r' : K × Reg n) :
    (worldOp x).branch a ρ (u, r) (u', r') = x.branch a (worldBlock r r' ρ) u u' :=
  rfl

variable [DecidableEq K]

/-- The Kraus operator `⟨q, b|` on the buffer and the simulator register. -/
def trKraus (c : Reg n × Reg n) : Matrix (Reg n × K) (Joint n K) ℂ :=
  Matrix.of fun x y => if y = ((x.1, c.1), (x.2, c.2)) then 1 else 0

/-- The operators `trKraus c` satisfy the completeness relation. -/
theorem trKraus_complete :
    ∑ c : Reg n × Reg n, (trKraus (K := K) c)ᴴ * trKraus c = 1 := by
  ext ⟨⟨i, q⟩, ⟨κ, b⟩⟩ ⟨⟨i', q'⟩, ⟨κ', b'⟩⟩
  simp only [trKraus, Matrix.mul_apply, Matrix.one_apply, Matrix.sum_apply, conjTranspose_apply,
    of_apply, Fintype.sum_prod_type, Prod.ext_iff]
  by_cases hi : i = i' <;> by_cases hq : q = q' <;> by_cases hk : κ = κ' <;>
    by_cases hb : b = b' <;> simp [hi, hq, hk, hb, ite_and, apply_ite (starRingEnd ℂ),
      Finset.sum_ite_eq]

/-- Discarding the buffer and the simulator register. -/
def trQB : SubInstrument (Joint n K) (Reg n × K) Unit :=
  (SubInstrument.ofKraus trKraus trKraus_complete).bind fun _ => SubInstrument.pure ()

/-- The branch of `trQB` is the partial trace over `Q × B`. -/
theorem trQB_branch_apply (ρ : Matrix (Joint n K) (Joint n K) ℂ) (x y : Reg n × K) :
    (trQB (n := n)).branch () ρ x y =
      ∑ c : Reg n × Reg n, ρ ((x.1, c.1), (x.2, c.2)) ((y.1, c.1), (y.2, c.2)) := by
  rw [trQB, SubInstrument.bind, DSubInstrument.branch_bind_apply_univ]
  simp only [SubInstrument.branch_pure_self, LinearMap.id_comp, LinearMap.sum_apply,
    DSubInstrument.branch_ofKraus_apply, MatrixMap.conj_apply, Matrix.sum_apply]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp [trKraus, mul_apply, conjTranspose_apply, apply_ite (starRingEnd ℂ)]

/-- A continuation after `trQB` acts on the partial trace. -/
theorem trQB_bind_branch {β C : Type} [Fintype C] (f : Unit → SubInstrument (Reg n × K) C β)
    (c : β) (ρ : Matrix (Joint n K) (Joint n K) ℂ) :
    ((trQB (n := n)).bind f).branch c ρ = (f ()).branch c ((trQB (n := n)).branch () ρ) := by
  rw [SubInstrument.bind, DSubInstrument.branch_bind_apply_univ]
  simp

/-- The partial trace over `Q × B` after a placed environment operation is the operation after
the partial trace. -/
theorem trQB_envOp (w : SubInstrument (Reg n × K) (Reg n × K) α) (a : α)
    (ρ : Matrix (Joint n K) (Joint n K) ℂ) :
    (trQB (n := n)).branch () ((envOp w).branch a ρ) =
      w.branch a ((trQB (n := n)).branch () ρ) := by
  have h : (trQB (n := n)).branch () ρ = ∑ c : Reg n × Reg n, envBlock c.1 c.2 c.1 c.2 ρ := by
    ext x y
    rw [trQB_branch_apply, Matrix.sum_apply]
    rfl
  ext x y
  rw [trQB_branch_apply, h, map_sum, Matrix.sum_apply]
  rfl

/-- A placed environment operation followed by the partial trace over `Q × B` is the partial
trace followed by the operation. -/
theorem envOp_bind_trQB {β C : Type} [Fintype C] (w : SubInstrument (Reg n × K) (Reg n × K) α)
    (f : α → SubInstrument (Reg n × K) C β) :
    (envOp w).bind (fun a => (trQB (n := n)).bind fun _ => f a) =
      (trQB (n := n)).bind fun _ => w.bind f := by
  refine DSubInstrument.ext <| funext fun c => LinearMap.ext fun ρ => ?_
  rw [SubInstrument.bind, DSubInstrument.branch_bind_apply, trQB_bind_branch, SubInstrument.bind,
    DSubInstrument.branch_bind_apply]
  refine tsum_congr fun a => ?_
  rw [trQB_bind_branch, trQB_envOp]

end Joint

/-! ## Entries of the operations of the worlds and of the simulator -/

section Entries

/-- The branch of the key sampling scales by `2⁻²ⁿ`. -/
theorem keyOp_branch_apply (k : Key n) (X : Matrix (Reg n × Reg n) (Reg n × Reg n) ℂ) :
    (keyOp n).branch k X = (amp n * amp n) • X := by
  ext x y
  simp [keyH, frameLeft_branch, MatrixMap.amplifyLeft_apply, DSubInstrument.branch_ofKraus_apply,
    MatrixMap.conj_apply, amp]
  ring

/-- Entries of a unitary on the interface register. -/
theorem frame_unitaryOp_apply (U : Matrix (Reg n) (Reg n) ℂ) (hU : Uᴴ * U = 1)
    (X : Matrix (Reg n × Reg n) (Reg n × Reg n) ℂ) (x y : Reg n × Reg n) :
    ((unitaryOp U hU).frame (Reg n)).branch () X x y =
      ∑ u, ∑ u', U x.1 u * X (u, x.2) (u', y.2) * star (U y.1 u') := by
  simp only [unitaryOp, DSubInstrument.branch_frame_apply, MatrixMap.amplify_apply,
    DSubInstrument.branch_ofKraus_apply, MatrixMap.conj_apply, mul_apply, Finset.sum_mul,
    conjTranspose_apply, submatrix_apply]
  exact Finset.sum_comm

/-- Entries of a unitary on the buffer. -/
theorem frameLeft_unitaryOp_apply (U : Matrix (Reg n) (Reg n) ℂ) (hU : Uᴴ * U = 1)
    (X : Matrix (Reg n × Reg n) (Reg n × Reg n) ℂ) (x y : Reg n × Reg n) :
    (frameLeft (unitaryOp U hU) (Reg n)).branch () X x y =
      ∑ u, ∑ u', U x.2 u * X (x.1, u) (y.1, u') * star (U y.2 u') := by
  simp only [unitaryOp, frameLeft_branch, MatrixMap.amplifyLeft_apply,
    DSubInstrument.branch_ofKraus_apply, MatrixMap.conj_apply, mul_apply, Finset.sum_mul,
    conjTranspose_apply, submatrix_apply]
  exact Finset.sum_comm

/-- Entries of the swap. -/
theorem swapOp_apply (X : Matrix (Reg n × Reg n) (Reg n × Reg n) ℂ) (x y : Reg n × Reg n) :
    (swapOp (Reg n)).branch () X x y = X x.swap y.swap := by
  simp [swapOp, unitaryOp, swapMat, DSubInstrument.branch_ofKraus_apply, MatrixMap.conj_apply,
    mul_apply]

/-- Entries of the preparation of the maximally entangled state:
`X ↦ tr X • |Φ⁺⟩⟨Φ⁺|`. -/
theorem eprOp_apply (X : Matrix (Reg n × Reg n) (Reg n × Reg n) ℂ) (x y : Reg n × Reg n) :
    (eprOp n).branch () X x y =
      if x.1 = x.2 ∧ y.1 = y.2 then ((2 : ℂ) ^ n)⁻¹ * X.trace else 0 := by
  rw [eprOp, SubInstrument.bind, DSubInstrument.branch_bind_apply_univ]
  simp only [SubInstrument.branch_pure_self, LinearMap.id_comp, LinearMap.sum_apply,
    DSubInstrument.branch_ofKraus_apply, MatrixMap.conj_apply, Matrix.sum_apply]
  have h : ∀ c : Reg n × Reg n, (eprKraus c * X * (eprKraus c)ᴴ) x y =
      if x.1 = x.2 ∧ y.1 = y.2 then ((2 : ℂ) ^ n)⁻¹ * X c c else 0 := by
    intro c
    by_cases hx : x.1 = x.2 <;> by_cases hy : y.1 = y.2 <;>
      simp [eprKraus, mul_apply, conjTranspose_apply, hx, hy, ← eprAmp_mul_self,
        apply_ite (starRingEnd ℂ), Complex.conj_ofReal, mul_ite, Finset.sum_ite_eq']
    ring
  rw [Finset.sum_congr rfl fun c _ => h c]
  split_ifs <;> simp [Matrix.trace, Finset.mul_sum]

/-- Entries of the Bell measurement: `X ↦ Π_j X Π_j`. -/
theorem bellOp_apply (j : Key n) (X : Matrix (Reg n × Reg n) (Reg n × Reg n) ℂ) :
    (bellOp n).branch j X = bellProj j * X * bellProj j := by
  rw [bellOp, DSubInstrument.branch_ofKraus_apply, MatrixMap.conj_apply, conjTranspose_bellProj]

end Entries

/-! ## The two identities after `send` -/

section Identities

variable {K : Type} [Fintype K] [DecidableEq K]

/-- `2⁻²ⁿ ⬝ 2ⁿ = 2⁻ⁿ`. -/
theorem amp_mul_amp_mul_two_pow : amp n * amp n * (2 : ℂ) ^ n = ((2 : ℂ) ^ n)⁻¹ := by
  simp only [amp, inv_pow]
  field_simp

/-- After the partial trace over `Q × B`, the key sampling and the encryption of the interface
register give the state that the swap into the buffer and the preparation of the maximally
entangled state on `I × B` give. -/
theorem twirl_epr_trace (ρ : Matrix (Joint n K) (Joint n K) ℂ) :
    ∑ k : Key n, (trQB (n := n)).branch ()
        ((worldOp (encI k)).branch () ((worldOp (keyOp n)).branch k ρ)) =
      (trQB (n := n)).branch ()
        ((simOp (eprOp n)).branch () ((worldOp (swapOp (Reg n))).branch () ρ)) := by
  ext ⟨i, κ⟩ ⟨i', κ'⟩
  have hL : (∑ k : Key n, (trQB (n := n)).branch ()
        ((worldOp (encI k)).branch () ((worldOp (keyOp n)).branch k ρ))) (i, κ) (i', κ') =
      if i = i' then ((2 : ℂ) ^ n)⁻¹ *
        ∑ c : Reg n × Reg n, ∑ u : Reg n, ρ ((u, c.1), (κ, c.2)) ((u, c.1), (κ', c.2))
      else 0 := by
    simp only [Matrix.sum_apply, trQB_branch_apply, worldOp_branch_apply, frame_unitaryOp_apply,
      worldBlock, of_apply, keyOp_branch_apply, Matrix.smul_apply, smul_eq_mul]
    have hk : ∀ (c : Reg n × Reg n) (u u' : Reg n), ∑ k : Key n, pauliFin k i u *
        (amp n * amp n * ρ ((u, c.1), (κ, c.2)) ((u', c.1), (κ', c.2))) * star (pauliFin k i' u') =
        amp n * amp n * ρ ((u, c.1), (κ, c.2)) ((u', c.1), (κ', c.2)) *
          (if i = i' ∧ u = u' then (2 : ℂ) ^ n else 0) := by
      intro c u u'
      rw [← isTwirlFamily_pauliFin n i u i' u', Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by ring
    have hswap : ∀ c : Reg n × Reg n, (∑ k : Key n, ∑ u : Reg n, ∑ u' : Reg n, pauliFin k i u *
        (amp n * amp n * ρ ((u, c.1), (κ, c.2)) ((u', c.1), (κ', c.2))) *
          star (pauliFin k i' u')) =
        ∑ u : Reg n, ∑ u' : Reg n, ∑ k : Key n, pauliFin k i u *
          (amp n * amp n * ρ ((u, c.1), (κ, c.2)) ((u', c.1), (κ', c.2))) *
            star (pauliFin k i' u') := fun c => by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun u _ => Finset.sum_comm
    rw [Finset.sum_comm, Finset.sum_congr rfl fun c _ => hswap c]
    simp only [hk]
    by_cases h : i = i'
    · subst h
      simp only [true_and, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
        ite_true, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun u _ => ?_
      rw [mul_right_comm, amp_mul_amp_mul_two_pow]
    · simp only [h, false_and, ↓reduceIte, mul_zero, Finset.sum_const_zero]
  have hR : ((trQB (n := n)).branch ()
        ((simOp (eprOp n)).branch () ((worldOp (swapOp (Reg n))).branch () ρ))) (i, κ) (i', κ') =
      if i = i' then ((2 : ℂ) ^ n)⁻¹ *
        ∑ c : Reg n × Reg n, ∑ u : Reg n, ρ ((u, c.1), (κ, c.2)) ((u, c.1), (κ', c.2))
      else 0 := by
    simp only [trQB_branch_apply, simOp_branch_apply, eprOp_apply, Matrix.trace, diag_apply,
      simBlock, of_apply, worldOp_branch_apply, swapOp_apply, worldBlock, Prod.swap]
    rw [Fintype.sum_prod_type]
    by_cases h : i = i'
    · subst h
      simp only [and_self, Finset.sum_ite_eq, Finset.mem_univ, ite_true, ← Finset.mul_sum]
      rw [Finset.sum_comm]
    · simp only [h, ↓reduceIte]
      refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun y _ => ?_
      rw [ite_eq_right_iff]
      rintro ⟨rfl, rfl⟩
      exact absurd rfl h
  rw [hL, hR]

/-- Exchange of two pairs of finite sums. -/
theorem sum_comm4 {A B C D : Type} [Fintype A] [Fintype B] [Fintype C] [Fintype D]
    (f : A → B → C → D → ℂ) :
    ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := by
  calc ∑ a, ∑ b, ∑ c, ∑ d, f a b c d = ∑ a, ∑ c, ∑ d, ∑ b, f a b c d :=
        Finset.sum_congr rfl fun a _ => by
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun c _ => Finset.sum_comm
    _ = ∑ c, ∑ a, ∑ d, ∑ b, f a b c d := Finset.sum_comm
    _ = ∑ c, ∑ d, ∑ a, ∑ b, f a b c d := Finset.sum_congr rfl fun c _ => Finset.sum_comm

/-- A double sum of a double indicator is the value at the indicated pair. -/
theorem sum_sum_ite_eq {A B M : Type} [Fintype A] [Fintype B] [DecidableEq A] [DecidableEq B]
    [AddCommMonoid M] (a : A) (b : B) (f : A → B → M) :
    ∑ x, ∑ y, (if a = x then (if b = y then f x y else 0) else 0) = f a b := by
  rw [Finset.sum_eq_single a]
  · simp
  · intro x _ hx
    simp [Ne.symm hx]
  · simp

/-- An entry of a linear map at a linear combination. -/
theorem map_sum_smul_apply {X ι : Type} [Fintype ι] (V : MatrixMap X X)
    (c : ι → ℂ) (M : ι → Matrix X X ℂ) (x y : X) :
    V (∑ i, c i • M i) x y = ∑ i, c i * V (M i) x y := by
  simp [map_sum, map_smul, Matrix.sum_apply]

/-- The partial trace over `Q × B` as the sum of the diagonal blocks. -/
theorem trQB_eq_sum (ρ : Matrix (Joint n K) (Joint n K) ℂ) :
    (trQB (n := n)).branch () ρ = ∑ c : Reg n × Reg n, envBlock c.1 c.2 c.1 c.2 ρ := by
  ext x y
  rw [trQB_branch_apply, Matrix.sum_apply]
  rfl

/-- The partial trace over the measured pair of a Bell projection on both sides. -/
theorem sum_bellProj_conj (j : Key n) (G : Reg n × Reg n → Reg n × Reg n → ℂ) :
    ∑ c : Reg n × Reg n, (∑ z' : Reg n × Reg n,
        (∑ z : Reg n × Reg n, bellProj j c z * G z z') * bellProj j z' c) =
      ∑ z : Reg n × Reg n, ∑ z' : Reg n × Reg n, bellProj j z' z * G z z' := by
  have hP : ∀ z z' : Reg n × Reg n, ∑ c, bellProj j z' c * bellProj j c z = bellProj j z' z :=
    fun z z' => by
      have := congrFun (congrFun (bellProj_mul_self j) z') z
      rwa [mul_apply] at this
  simp only [Finset.sum_mul]
  rw [Finset.sum_comm]
  conv_lhs => enter [2, z']; rw [Finset.sum_comm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun z' _ => ?_
  rw [← hP z z', Finset.sum_mul]
  exact Finset.sum_congr rfl fun c _ => by ring

/-- After the partial trace over `Q × B`, decryption after an operation `V` of the adversary on
the ciphertext, averaged over the key, is the Bell measurement of the adversary's register
against the simulator's EPR halves followed by the Pauli correction `P_j` of the message. -/
theorem deliver_trace {α : Type} (w : SubInstrument (Reg n × K) (Reg n × K) α) (a : α)
    (ρ : Matrix (Joint n K) (Joint n K) ℂ) :
    ∑ k : Key n, (trQB (n := n)).branch () ((worldOp (decI k)).branch ()
        ((envOp w).branch a ((worldOp (encI k)).branch () ((worldOp (keyOp n)).branch k ρ)))) =
      ∑ j : Key n, (trQB (n := n)).branch () ((worldOp (swapOp (Reg n))).branch ()
        ((worldOp (errQ j)).branch () ((simOp (bellOp n)).branch j ((envOp w).branch a
          ((simOp (eprOp n)).branch () ((worldOp (swapOp (Reg n))).branch () ρ)))))) := by
  set N : Key n → Matrix (Joint n K) (Joint n K) ℂ := fun k =>
    (worldOp (encI k)).branch () ((worldOp (keyOp n)).branch k ρ) with hN
  set N' : Matrix (Joint n K) (Joint n K) ℂ :=
    (simOp (eprOp n)).branch () ((worldOp (swapOp (Reg n))).branch () ρ) with hN'
  ext ⟨i, κ⟩ ⟨i', κ'⟩
  set L : Reg n → Reg n → Matrix (Reg n × K) (Reg n × K) ℂ := fun y y' =>
    ∑ k : Key n, (star (pauliFin k y i) * pauliFin k y' i') • (trQB (n := n)).branch () (N k)
    with hL
  set R : Reg n → Reg n → Matrix (Reg n × K) (Reg n × K) ℂ := fun x x' =>
    ∑ j : Key n, ∑ p : Reg n, ∑ p' : Reg n, ∑ β : Reg n, ∑ β' : Reg n,
      (pauliFin j i p * star (pauliFin j i' p') * bellProj j (x', β') (x, β)) •
        envBlock p β p' β' N' with hR
  have hLR : ∀ y y', L y y' = R y y' := by
    intro y y'
    ext ⟨j0, l⟩ ⟨j0', l'⟩
    have hC : ∀ u u' : Reg n, amp n * amp n * ∑ k : Key n, star (pauliFin k y i) *
        pauliFin k y' i' * pauliFin k j0 u * star (pauliFin k j0' u') =
        ((2 : ℂ) ^ n)⁻¹ * ((2 : ℂ) ^ n)⁻¹ * ∑ k : Key n, pauliFin k i u *
          star (pauliFin k i' u') * pauliFin k y' j0' * star (pauliFin k y j0) := by
      intro u u'
      simp only [star_pauliFin]
      rw [pauliFin_four_point y y' i i' j0 j0' u u']
      simp only [amp, inv_pow]
      congr 1
      exact Finset.sum_congr rfl fun k _ => by ring
    have hLe : L y y' (j0, l) (j0', l') = ∑ u : Reg n, ∑ u' : Reg n,
        ∑ k : Key n, ∑ c : Reg n × Reg n, amp n * amp n * (star (pauliFin k y i) *
          pauliFin k y' i' * pauliFin k j0 u * star (pauliFin k j0' u')) *
          ρ ((u, c.1), (l, c.2)) ((u', c.1), (l', c.2)) := by
      simp only [hL, hN, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, trQB_branch_apply,
        worldOp_branch_apply, frame_unitaryOp_apply, worldBlock, of_apply, keyOp_branch_apply,
        Finset.mul_sum]
      rw [sum_comm4]
      refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun u' _ =>
        Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun c _ => ?_
      ring
    have hRe : R y y' (j0, l) (j0', l') = ∑ u : Reg n, ∑ u' : Reg n,
        ∑ k : Key n, ∑ c : Reg n × Reg n, ((2 : ℂ) ^ n)⁻¹ * ((2 : ℂ) ^ n)⁻¹ *
          (pauliFin k i u * star (pauliFin k i' u') * pauliFin k y' j0' *
            star (pauliFin k y j0)) * ρ ((u, c.1), (l, c.2)) ((u', c.1), (l', c.2)) := by
      simp only [hR, hN', Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, envBlock, of_apply,
        simOp_branch_apply, eprOp_apply, Matrix.trace, diag_apply, simBlock,
        worldOp_branch_apply, swapOp_apply, worldBlock, Prod.swap, bellProj, mul_ite, mul_zero,
        ite_and, Finset.mul_sum]
      simp only [sum_sum_ite_eq]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun u _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun u' _ => Finset.sum_congr rfl fun k _ =>
        Finset.sum_congr rfl fun c _ => ?_
      ring
    rw [hLe, hRe]
    refine Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun u' _ => ?_
    rw [Finset.sum_comm, Finset.sum_comm (s := (Finset.univ : Finset (Key n)))]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum, ← Finset.mul_sum, hC]
  have hl : (∑ k : Key n, (trQB (n := n)).branch () ((worldOp (decI k)).branch ()
        ((envOp w).branch a (N k)))) (i, κ) (i', κ') =
      ∑ y : Reg n, ∑ y' : Reg n, w.branch a (L y y') (y, κ) (y', κ') := by
    simp only [hL, map_sum_smul_apply, ← trQB_envOp, trQB_branch_apply, Matrix.sum_apply,
      worldOp_branch_apply, frame_unitaryOp_apply, worldBlock, of_apply, conjTranspose_apply,
      star_star, Finset.mul_sum]
    rw [sum_comm4]
    refine Finset.sum_congr rfl fun y _ => Finset.sum_congr rfl fun y' _ =>
      Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun c _ => ?_
    ring
  have hr : (∑ j : Key n, (trQB (n := n)).branch () ((worldOp (swapOp (Reg n))).branch ()
        ((worldOp (errQ j)).branch () ((simOp (bellOp n)).branch j
          ((envOp w).branch a N'))))) (i, κ) (i', κ') =
      ∑ x : Reg n, ∑ x' : Reg n, w.branch a (R x x') (x, κ) (x', κ') := by
    simp only [hR, map_sum, map_smul, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul,
      trQB_branch_apply, worldOp_branch_apply, swapOp_apply, worldBlock, of_apply, Prod.swap,
      frameLeft_unitaryOp_apply, simOp_branch_apply, bellOp_apply, simBlock, mul_apply]
    conv_lhs => enter [2, j]; rw [Finset.sum_comm]; enter [2, p]; rw [Finset.sum_comm]
    conv_lhs => enter [2, j, 2, p, 2, p']; rw [← Finset.sum_mul, ← Finset.mul_sum,
      sum_bellProj_conj]
    simp only [envOp_branch_apply, Fintype.sum_prod_type, Finset.mul_sum, Finset.sum_mul]
    conv_lhs => enter [2, j, 2, p, 2, p', 2, x]; rw [Finset.sum_comm]
    conv_rhs => rw [sum_comm4]
    conv_rhs => enter [2, j, 2, p, 2, x]; rw [Finset.sum_comm]
    conv_rhs => enter [2, j, 2, p]; rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun p _ =>
      Finset.sum_congr rfl fun p' _ => Finset.sum_congr rfl fun x _ =>
      Finset.sum_congr rfl fun x' _ => Finset.sum_congr rfl fun β _ =>
      Finset.sum_congr rfl fun β' _ => ?_
    ring
  rw [hl, hr]
  simp only [hLR]

/-- A continuation after an operation with one outcome acts on its branch. -/
theorem bind_unit_branch {A B C : Type} [Fintype A] [Fintype B] [Fintype C] {β : Type}
    (p : SubInstrument A B Unit) (k : Unit → SubInstrument B C β) (c : β)
    (ρ : Matrix A A ℂ) : (p.bind k).branch c ρ = (k ()).branch c (p.branch () ρ) := by
  rw [SubInstrument.bind, DSubInstrument.branch_bind_apply_univ]
  simp

/-- The branch of a sequencing after an operation with finitely many outcomes. -/
theorem bind_fin_branch {A B C : Type} [Fintype A] [Fintype B] [Fintype C] {α β : Type}
    [Fintype α] (p : SubInstrument A B α) (k : α → SubInstrument B C β) (c : β)
    (ρ : Matrix A A ℂ) : (p.bind k).branch c ρ = ∑ a, (k a).branch c (p.branch a ρ) := by
  rw [SubInstrument.bind, DSubInstrument.branch_bind_apply_univ, LinearMap.sum_apply]
  rfl

/-- The continuations of the real world after `send`: an outcome `inl` of the environment
discards `Q × B`; an outcome `inr` lets Bob decrypt first. -/
def kontR {γ δ C β : Type} [Fintype C] (g : γ → SubInstrument (Reg n × K) C β)
    (h : δ → SubInstrument (Reg n × K) C β) (k : Key n) :
    γ ⊕ δ → SubInstrument (Joint n K) C β :=
  Sum.elim (fun x => (trQB (n := n)).bind fun _ => g x)
    (fun y => (worldOp (decI k)).bind fun _ => (trQB (n := n)).bind fun _ => h y)

/-- The continuations of the ideal world behind the simulator after `send`: an outcome `inr`
of the environment is answered by the Bell measurement, the Pauli error and the delivery. -/
def kontI {γ δ C β : Type} [Fintype C] (g : γ → SubInstrument (Reg n × K) C β)
    (h : δ → SubInstrument (Reg n × K) C β) :
    γ ⊕ δ → SubInstrument (Joint n K) C β :=
  Sum.elim (fun x => (trQB (n := n)).bind fun _ => g x)
    (fun y => (simOp (bellOp n)).bind fun j => (worldOp (errQ j)).bind fun _ =>
      (worldOp (swapOp (Reg n))).bind fun _ => (trQB (n := n)).bind fun _ => h y)

/-- **The step after `send`.** For every operation `W` of the environment on `I × K` and
every split of its outcomes into those after which the message is delivered and the others,
the key sampling and the encryption of the real world give the same subinstrument as the swap
into the buffer and the simulator's EPR pairs. -/
theorem send_core {α γ δ C β : Type} [Fintype C] (W : SubInstrument (Reg n × K) (Reg n × K) α)
    (f : α → γ ⊕ δ) (g : γ → SubInstrument (Reg n × K) C β)
    (h : δ → SubInstrument (Reg n × K) C β) :
    (worldOp (keyOp n)).bind (fun k => (worldOp (encI k)).bind fun _ =>
      (envOp W).bind fun a => kontR g h k (f a)) =
    (worldOp (swapOp (Reg n))).bind (fun _ => (simOp (eprOp n)).bind fun _ =>
      (envOp W).bind fun a => kontI g h (f a)) := by
  refine DSubInstrument.ext <| funext fun c => LinearMap.ext fun ρ => ?_
  have hsum : ∀ (k : Key n) (X : Matrix (Joint n K) (Joint n K) ℂ),
      Summable fun a => (kontR g h k (f a)).branch c ((envOp W).branch a X) := fun k X =>
    ((envOp W).isCPTNIFamily.comp_eval
      (fun a => (kontR g h k (f a)).isCPTNIFamily) c).summable_apply X
  have hL : ((worldOp (K := K) (keyOp n)).bind (fun k => (worldOp (encI k)).bind fun _ =>
      (envOp W).bind fun a => kontR g h k (f a))).branch c ρ =
      ∑' a, ∑ k : Key n, (kontR g h k (f a)).branch c ((envOp W).branch a
        ((worldOp (encI k)).branch () ((worldOp (keyOp n)).branch k ρ))) := by
    rw [bind_fin_branch, Summable.tsum_finsetSum fun k _ => hsum k _]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [bind_unit_branch, SubInstrument.bind, DSubInstrument.branch_bind_apply]
  have hR : ((worldOp (K := K) (swapOp (Reg n))).bind (fun _ => (simOp (eprOp n)).bind fun _ =>
      (envOp W).bind fun a => kontI g h (f a))).branch c ρ =
      ∑' a, (kontI g h (f a)).branch c ((envOp W).branch a
        ((simOp (eprOp n)).branch () ((worldOp (swapOp (Reg n))).branch () ρ))) := by
    rw [bind_unit_branch, bind_unit_branch, SubInstrument.bind, DSubInstrument.branch_bind_apply]
  rw [hL, hR]
  refine tsum_congr fun a => ?_
  cases f a with
  | inl x =>
    simp only [kontR, kontI, Sum.elim_inl, trQB_bind_branch, trQB_envOp]
    rw [← map_sum, ← map_sum, twirl_epr_trace]
  | inr y =>
    simp only [kontR, kontI, Sum.elim_inr, bind_unit_branch]
    rw [bind_fin_branch]
    simp only [bind_unit_branch]
    rw [← map_sum ((h y).branch c), deliver_trace, map_sum]

end Identities

/-! ## The runs of the two worlds -/

section Runs

variable {K ζ : Type} [Fintype K] [DecidableEq K]

/-- The basis state in which the buffer and the simulator register are prepared. -/
abbrev reg₀ (n : ℕ) : Reg n := ⟨0, Nat.two_pow_pos n⟩

variable (Z : QStratQ K ζ Event Out (2 ^ n))

/-- The run of `Z`, with its memory padded by the simulator register, against the real world
from a configuration, with the registers other than `I` discarded. -/
def realRun (m : ℕ) (c : ζ × Phase n) : SubInstrument (Joint n K) (Reg n) ζ :=
  (qloopQ (insReal n) (padMem Z (Reg n) (reg₀ n)) m c).bind fun c' =>
    discardRight.bind fun _ => discardRight.bind fun _ => SubInstrument.pure c'.1

/-- The run of `Z` behind the simulator against the ideal world from a configuration, with the
registers other than `I` discarded. -/
def idealRun (m : ℕ) (c : (ζ × IPhase) × IPhase) : SubInstrument (Joint n K) (Reg n) ζ :=
  (qloopQ (confIdeal n) ((eprSim n).absorb Z) m c).bind fun c' =>
    discardRight.bind fun _ => discardRight.bind fun _ => SubInstrument.pure c'.1.1

/-- The run of `Z` against a world that ignores every event. -/
def envLoopK : ℕ → ζ → SubInstrument (Reg n × K) (Reg n × K) ζ
  | 0, z => SubInstrument.pure z
  | m + 1, z => (Z.next z).bind fun a => (Z.obs a.1 .ignored).bind fun z' => envLoopK m z'

/-- The run of `Z` against a world that ignores every event, with its memory discarded. -/
def envRunK (m : ℕ) (z : ζ) : SubInstrument (Reg n × K) (Reg n) ζ :=
  (envLoopK Z m z).bind fun z' => discardRight.bind fun _ => SubInstrument.pure z'

omit [DecidableEq K] in
/-- A placed environment operation of `pure` is `pure`. -/
theorem envOp_pure {α : Type} (a : α) :
    envOp (n := n) (K := K) (SubInstrument.pure a) = SubInstrument.pure a := by
  simp only [envPlace, placeLeft, SubInstrument.frame_pure, relabel_pure]

omit [DecidableEq K] in
/-- A placed simulator operation of `pure` is `pure`. -/
theorem simOp_pure {α : Type} (a : α) :
    simOp (n := n) (K := K) (SubInstrument.pure a) = SubInstrument.pure a := by
  simp only [envPlace, placeRight, SubInstrument.frame_pure, relabel_pure]

omit [DecidableEq K] in
/-- A placed environment operation of a sequencing is the sequencing of the placed parts. -/
theorem envOp_bind {α β : Type} (p : SubInstrument (Reg n × K) (Reg n × K) α)
    (k : α → SubInstrument (Reg n × K) (Reg n × K) β) :
    envOp (p.bind k) = (envOp p).bind fun a => envOp (k a) := by
  simp only [envPlace, placeLeft, SubInstrument.frame_bind, relabel_bind]

/-- One activation of the run against a world that ignores every event. -/
theorem envRunK_succ (m : ℕ) (z : ζ) :
    envRunK Z (m + 1) z =
      (Z.next z).bind fun a => (Z.obs a.1 .ignored).bind fun z' => envRunK Z m z' := by
  simp only [envRunK, envLoopK, SubInstrument.bind_assoc]

/-- One activation of the real run. -/
theorem realRun_succ (m : ℕ) (z : ζ) (ph : Phase n) :
    realRun Z (m + 1) (z, ph) = (envOp (Z.next z)).bind fun b =>
      (worldOp (realStep n ph b.2)).bind fun p =>
        (envOp (Z.obs b.1 p.2)).bind fun z' => realRun Z m (z', p.1) := by
  simp only [realRun, qloopQ, SubInstrument.bind_assoc]
  rfl

/-- One activation of the ideal run behind the simulator. -/
theorem idealRun_succ (m : ℕ) (z : ζ) (s ph : IPhase) :
    idealRun Z (m + 1) ((z, s), ph) = (envOp (Z.next z)).bind fun a =>
      (simOp (simPre n s a.2)).bind fun b =>
        (worldOp (confStep n ph b.2)).bind fun p =>
          (simOp (simPost n b.1 p.2)).bind fun q =>
            (envOp (Z.obs a.1 q.2)).bind fun z' => idealRun Z m ((z', q.1), p.1) := by
  simp only [idealRun, qloopQ, QSimQ.absorb, envPlace_bind, envPlace_pure,
    SubInstrument.bind_assoc, SubInstrument.pure_bind]
  rfl

/-- Discarding `K × B` and then `Q` is discarding `Q × B` and then `K`. -/
theorem discards_eq_trQB {C β : Type} [Fintype C] (f : SubInstrument (Reg n) C β) :
    (discardRight : SubInstrument (Joint n K) (Reg n × Reg n) (K × Reg n)).bind
      (fun _ => (discardRight : SubInstrument (Reg n × Reg n) (Reg n) (Reg n)).bind fun _ => f) =
    (trQB (n := n)).bind fun _ =>
      (discardRight : SubInstrument (Reg n × K) (Reg n) K).bind fun _ => f := by
  refine DSubInstrument.ext <| funext fun b => LinearMap.ext fun ρ => ?_
  rw [trQB_bind_branch]
  simp only [SubInstrument.bind, DSubInstrument.branch_bind_apply_univ, LinearMap.sum_apply,
    LinearMap.comp_apply, discardRight_branch_apply]
  rw [trQB_eq_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun κ _ => ?_
  simp only [← map_sum]
  congr 1
  ext a a'
  simp only [Matrix.sum_apply, submatrix_apply, envBlock, of_apply, Fintype.sum_prod_type]
  exact Finset.sum_comm

/-- After `deliver` the real world ignores every event. -/
theorem realStep_done (e : Event) :
    realStep n .done e = SubInstrument.pure (.done, .ignored) := by
  cases e <;> rfl

/-- After `deliver` the real run is the run against a world that ignores every event. -/
theorem realRun_done (m : ℕ) (z : ζ) :
    realRun Z m (z, .done) = (trQB (n := n)).bind fun _ => envRunK Z m z := by
  induction m generalizing z with
  | zero =>
    simp only [realRun, qloopQ, SubInstrument.pure_bind, discards_eq_trQB, envRunK, envLoopK]
  | succ m ih =>
    simp only [realRun_succ, realStep_done, SubInstrument.frame_pure, SubInstrument.pure_bind,
      ih, envOp_bind_trQB, envRunK_succ]

/-- After `deliver` the ideal run behind the simulator is the run against a world that ignores
every event. -/
theorem idealRun_done (m : ℕ) (z : ζ) :
    idealRun Z m ((z, .done), .done) = (trQB (n := n)).bind fun _ => envRunK Z m z := by
  induction m generalizing z with
  | zero =>
    simp only [idealRun, qloopQ, SubInstrument.pure_bind, discards_eq_trQB, envRunK, envLoopK]
  | succ m ih =>
    rw [idealRun_succ]
    have h : ∀ a : ζ × Event, (simOp (K := K) (simPre n .done a.2)).bind (fun b =>
        (worldOp (confStep n .done b.2)).bind fun p =>
          (simOp (simPost n b.1 p.2)).bind fun q =>
            (envOp (Z.obs a.1 q.2)).bind fun z' => idealRun Z m ((z', q.1), p.1)) =
        (envOp (Z.obs a.1 .ignored)).bind fun z' => idealRun Z m ((z', .done), .done) := by
      rintro ⟨_, e⟩
      cases e <;> simp only [simPre, confStep, simPost, SubInstrument.frame_pure, simOp_pure,
        SubInstrument.pure_bind]
    simp only [h, ih, envOp_bind_trQB, envRunK_succ]

omit [DecidableEq K] in
/-- A placed simulator operation of a sequencing is the sequencing of the placed parts. -/
theorem simOp_bind {α β : Type} (p : SubInstrument (Reg n × Reg n) (Reg n × Reg n) α)
    (k : α → SubInstrument (Reg n × Reg n) (Reg n × Reg n) β) :
    simOp (K := K) (p.bind k) = (simOp p).bind fun a => simOp (k a) := by
  simp only [envPlace, placeRight, SubInstrument.frame_bind, relabel_bind]

/-! ### Between `send` and `deliver` -/

/-- After `deliver`: the environment observes `received` and runs `p.2` further activations
against a world that ignores every event. -/
def afterDeliver (p : ζ × ℕ) : SubInstrument (Reg n × K) (Reg n) ζ :=
  (Z.obs p.1 .received).bind fun z' => envRunK Z p.2 z'

/-- The real run after `send` under the key `k`, from an environment state (`inl`) or from a
pending delivery (`inr`). -/
def contR (m : ℕ) (k : Key n) : ζ ⊕ (ζ × ℕ) → SubInstrument (Joint n K) (Reg n) ζ :=
  Sum.elim (fun z => realRun Z m (z, .sent k))
    (fun p => (worldOp (decI k)).bind fun _ => (trQB (n := n)).bind fun _ => afterDeliver Z p)

/-- The ideal run behind the simulator after `send`, from an environment state (`inl`) or
from a pending delivery (`inr`). -/
def contI (m : ℕ) : ζ ⊕ (ζ × ℕ) → SubInstrument (Joint n K) (Reg n) ζ :=
  Sum.elim (fun z => idealRun Z m ((z, .sent), .sent))
    (fun p => (simOp (bellOp n)).bind fun j => (worldOp (errQ j)).bind fun _ =>
      (worldOp (swapOp (Reg n))).bind fun _ => (trQB (n := n)).bind fun _ => afterDeliver Z p)

/-- One activation of the environment after `send`: an event `send` is observed as ignored,
an event `deliver` becomes a pending delivery with `m` further activations. -/
def stepS (m : ℕ) : ζ ⊕ (ζ × ℕ) → SubInstrument (Reg n × K) (Reg n × K) (ζ ⊕ (ζ × ℕ)) :=
  Sum.elim
    (fun z => (Z.next z).bind fun b => match b.2 with
      | .send => (Z.obs b.1 .ignored).bind fun z' => SubInstrument.pure (Sum.inl z')
      | .deliver => SubInstrument.pure (Sum.inr (b.1, m)))
    (fun p => SubInstrument.pure (Sum.inr p))

/-- One activation of the real run after `send`. -/
theorem contR_succ (m : ℕ) (k : Key n) (s : ζ ⊕ (ζ × ℕ)) :
    contR Z (m + 1) k s = (envOp (stepS Z m s)).bind (contR Z m k) := by
  cases s with
  | inl z =>
    simp only [contR, stepS, Sum.elim_inl, realRun_succ, envOp_bind, SubInstrument.bind_assoc]
    refine congrArg _ (funext fun b => ?_)
    obtain ⟨z₁, e⟩ := b
    cases e
    · simp only [realStep, SubInstrument.frame_pure, SubInstrument.pure_bind, envOp_bind,
        envOp_pure, SubInstrument.bind_assoc, Sum.elim_inl]
    · simp only [realStep, SubInstrument.frame_bind, SubInstrument.frame_pure,
        SubInstrument.bind_assoc, SubInstrument.pure_bind, envOp_pure, Sum.elim_inr,
        realRun_done, envOp_bind_trQB, afterDeliver]
  | inr p =>
    simp only [contR, stepS, Sum.elim_inr, envOp_pure, SubInstrument.pure_bind]

/-- One activation of the ideal run behind the simulator after `send`. -/
theorem contI_succ (m : ℕ) (s : ζ ⊕ (ζ × ℕ)) :
    contI Z (m + 1) s = (envOp (stepS Z m s)).bind (contI Z m) := by
  cases s with
  | inl z =>
    simp only [contI, stepS, Sum.elim_inl, idealRun_succ, envOp_bind, SubInstrument.bind_assoc]
    refine congrArg _ (funext fun b => ?_)
    obtain ⟨z₁, e⟩ := b
    cases e
    · simp only [simPre, confStep, simPost, SubInstrument.frame_pure, simOp_pure,
        SubInstrument.pure_bind, envOp_bind, envOp_pure, SubInstrument.bind_assoc, Sum.elim_inl]
    · simp only [simPre, confStep, simPost, simOp_bind, simOp_pure, SubInstrument.frame_bind,
        SubInstrument.frame_pure, SubInstrument.bind_assoc, SubInstrument.pure_bind, envOp_pure,
        Sum.elim_inr, idealRun_done, envOp_bind_trQB, afterDeliver]
  | inr p =>
    simp only [contI, stepS, Sum.elim_inr, envOp_pure, SubInstrument.pure_bind]

/-- **After `send`.** For every operation `W` of the environment and every continuation, the
real run under a uniformly random key equals the ideal run behind the simulator. -/
theorem sent_runs (m : ℕ) {α : Type} (W : SubInstrument (Reg n × K) (Reg n × K) α)
    (f : α → ζ ⊕ (ζ × ℕ)) :
    (worldOp (keyOp n)).bind (fun k => (worldOp (encI k)).bind fun _ =>
      (envOp W).bind fun a => contR Z m k (f a)) =
    (worldOp (swapOp (Reg n))).bind (fun _ => (simOp (eprOp n)).bind fun _ =>
      (envOp W).bind fun a => contI Z m (f a)) := by
  induction m generalizing α with
  | zero =>
    have hR : ∀ k, contR Z 0 k = kontR (fun z => discardRight.bind fun _ => SubInstrument.pure z)
        (afterDeliver Z) k := fun k => funext fun s => by
      cases s with
      | inl z =>
        simp only [contR, kontR, Sum.elim_inl, realRun, qloopQ, SubInstrument.pure_bind,
          discards_eq_trQB]
      | inr p => rfl
    have hI : contI Z 0 = kontI (fun z => discardRight.bind fun _ => SubInstrument.pure z)
        (afterDeliver Z) := funext fun s => by
      cases s with
      | inl z =>
        simp only [contI, kontI, Sum.elim_inl, idealRun, qloopQ, SubInstrument.pure_bind,
          discards_eq_trQB]
      | inr p => rfl
    simp only [hR, hI]
    exact send_core W f _ _
  | succ m ih =>
    have h := ih (W.bind fun a => stepS Z m (f a)) id
    simp only [envOp_bind, SubInstrument.bind_assoc, id] at h
    simp only [contR_succ, contI_succ]
    exact h

/-- Before `send`, the real run is the ideal run behind the simulator. -/
theorem realRun_idle (m : ℕ) (z : ζ) :
    realRun Z m (z, .idle) = idealRun Z m ((z, .idle), .idle) := by
  induction m generalizing z with
  | zero => simp only [realRun, idealRun, qloopQ, SubInstrument.pure_bind]
  | succ m ih =>
    rw [realRun_succ, idealRun_succ]
    refine congrArg _ (funext fun b => ?_)
    obtain ⟨z₁, e⟩ := b
    cases e
    · have h := sent_runs Z m (Z.obs z₁ .sent) Sum.inl
      simp only [contR, contI, Sum.elim_inl] at h
      simp only [realStep, simPre, confStep, simPost, SubInstrument.frame_bind,
        SubInstrument.frame_pure, simOp_bind, simOp_pure, SubInstrument.bind_assoc,
        SubInstrument.pure_bind]
      exact h
    · simp only [realStep, simPre, confStep, simPost, SubInstrument.frame_pure, simOp_pure,
        SubInstrument.pure_bind, ih]

end Runs

/-! ## The realization -/

section Realization

open CatCrypt.Crypto.UCMonad.DiamondNorm UCMonad.QuantumUC

variable {K ζ : Type} [Fintype K] [DecidableEq K]

/-- **The quantum one-time pad over an insecure channel.** The view of every environment
with every memory register against the real world equals its view against the confidential
quantum channel with Pauli tampering behind the EPR simulator. -/
theorem qviewQ_insReal (Z : QStratQ K ζ Event Out (2 ^ n)) :
    qviewQ (insReal n) Z = simViewQ (confIdeal n) (eprSim n) Z := by
  rw [← qviewQ_padMem (insReal n) Z (reg₀ n)]
  have h := realRun_idle Z Z.rounds Z.init
  simp only [realRun, idealRun] at h
  simp only [simViewQ, qviewQ, SubInstrument.bind_assoc, SubInstrument.pure_bind]
  exact congrArg _ (funext fun _ => congrArg _ (funext fun _ => h))

/-- The quantum one-time pad over an insecure quantum channel realizes the confidential
quantum channel with Pauli tampering `confIdeal n` behind the simulator `eprSim n`, which holds
`n` halves of EPR pairs, at distance `0`. -/
theorem qotpInsecure_realizesSimQ : QRealizesSimQ (insReal n) (confIdeal n) (eprSim n) 0 :=
  fun _ _ _ _ => quc_congr _ _
    (QUCEmulatesDiamond.refl 0 _ fun Z => CPComp.branch_cp (qviewQ (insReal n) Z)) rfl
    (funext fun Z => by rw [qviewQ_insReal])

end Realization

end CatCrypt.Quantum.QOTPInsecure
