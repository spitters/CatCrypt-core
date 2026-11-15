/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.MultiRound
public import CatCryptCore.Quantum.QROM.FiatShamirSigma
public import CatCryptCore.Quantum.QROM.PermUnitaryCore
public import CatCryptCore.Crypto.Signatures.Scheme

/-!
# The EUF-CMA game of a signature scheme in the quantum random-oracle model

A `QROMSig` is a signature scheme whose signer and verifier use a hash `H : X → Y`, with
verification reading `H` at the single point `point pk μ σ`. At a fixed hash it is a core
`SigScheme` (`QROMSig.toSigScheme`), so the classical game `eufcmaAdvantage` and the quantum
game below share their scheme.

A quantum EUF-CMA adversary `QSigAdv` is, per public key, a multi-round adversary `QAdvMR`
with superposition access to the hash and `k` classical signing rounds. A round's outcome is a
message and a tag `τ : Fin T`; the signature of the pair `(μ, τ)` uses the coins `R (μ, τ)` of
a uniform coin table `R`, so repeating a pair returns the same signature and distinct tags give
independent coins. The forgery is read by the adversary from the basis states of the flattened
register (`toQAdv`). The round outcomes are read by the game from the same basis states: the
flattened register carries one ancilla per round, and `roundOutcomes` decodes its digits
(`ancDigits`), digit `j` being the outcome of round `j`. The adversary wins when the forgery
verifies and its message differs from the message of every round outcome.

The conversion `prForge_eq_sum_prOutAt` writes the winning probability in the shape of
`fiatShamir_random_oracle`: the flattened adversary, followed by a permutation unitary that
moves its query register into a new ancilla and writes the verification point into it, run
against `H` with the verifier `QVerifier.ofPred` of the winning predicate at the point `x` and
the challenge `H x`, summed over `x`.

## Main definitions

* `QROMSig` — a signature scheme with a hash read at one point by verification
* `QROMSig.verifyH`, `QROMSig.toSigScheme` — verification and the scheme at a fixed hash
* `QVerifier.ofPred acc` — the verifier projecting onto the basis states with `acc x θ`
* `QAdv.withFinalB A g` — the adversary `A` with the final projector onto `g`
* `postU`, `moveAdv F p`, `moveAcc p g` — the appended permutation unitary, the adversary
  that writes the point `p` into its query register, and the predicate it is tested with
* `ancSplit`, `ancDigits`, `roundOutcomes` — the split of a basis index of the flattened
  register into the register before flattening and the round-outcome ancilla digits
* `QSigAdv` — a quantum EUF-CMA adversary
* `signTab` — the signing table of a key pair, a hash and a coin table
* `prForge`, `qEUFCMAAdvantage` — the winning probability and the advantage

## Main results

* `prOut_withFinalB_eq_sum_prOutAt` — a final test `g k (H (p k))` that reads the oracle at
  the point `p k` is the sum over `x` of `prOutAt` of `moveAdv F p` with verifier
  `QVerifier.ofPred (moveAcc p g)` at `(x, H x)`
* `prForge_eq_sum_prOutAt` — its instance at the forgery test
* `prForge_le_one` — the winning probability is at most one
* `roundOutcomes_ancDigits_symm`, `roundOutcomes_succ` — the outcome of round `j` is the
  `j`-th ancilla digit
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Matrix CatCrypt.Quantum CatCrypt.Quantum.TensorProduct CatCrypt.Core CatCrypt.Prob
  CatCrypt.Crypto.Signatures

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## Signature schemes with a hash -/

/-- A signature scheme whose signer and verifier use a hash `H : X → Y`; verification reads
    `H` at the single point `point pk μ σ` and tests the value with `check`. The signer's
    randomness is a uniform element of `Coins`; a signature `none` is a signing failure. -/
structure QROMSig (Msg PK SK Sig X Y : Type) where
  /-- The signer's coins. -/
  Coins : Type
  [finCoins : Fintype Coins]
  [neCoins : Nonempty Coins]
  /-- The key distribution. -/
  keygen : PMF (PK × SK)
  /-- Signing with the hash, the secret key, the message and the coins. -/
  sign : (X → Y) → SK → Msg → Coins → Option Sig
  /-- The point at which verification reads the hash. -/
  point : PK → Msg → Sig → X
  /-- The verification test of the hash value at `point pk μ σ`. -/
  check : PK → Msg → Sig → Y → Bool

attribute [instance] QROMSig.finCoins QROMSig.neCoins

namespace QROMSig

variable {Msg PK SK Sig X Y : Type}

/-- Verification at the hash `H`: `check` of the value of `H` at `point pk μ σ`. -/
def verifyH (S : QROMSig Msg PK SK Sig X Y) (H : X → Y) (pk : PK) (μ : Msg) (σ : Sig) : Bool :=
  S.check pk μ σ (H (S.point pk μ σ))

/-- The scheme at a fixed hash `H` as a core `SigScheme`: keys from `keygen`, signing with
    uniform coins, and verification `verifyH H`, rejecting the signature `none`. -/
def toSigScheme (S : QROMSig Msg PK SK Sig X Y) (H : X → Y) :
    SigScheme Msg PK SK (Option Sig) where
  keygen := fun h => S.keygen.map fun ks => some (ks, h)
  sign sk μ := SPComp.bind (SPComp.sample S.Coins) fun r => SPComp.pure (S.sign H sk μ r)
  verify pk μ σ := σ.elim false (S.verifyH H pk μ)

end QROMSig

/-! ## Verifiers of classical predicates and final projectors -/

section Pred

variable {m n w q : ℕ}

/-- The verifier of a predicate on the basis states: `V(x, θ)` is the diagonal projector onto
    the basis states `k` with `acc x θ k`. -/
def QVerifier.ofPred (acc : Fin m → Fin n → Fin (m * n * w) → Bool) : QVerifier m n w where
  proj x θ := diagB (acc x θ)
  proj_conjTranspose _ _ := diagB_conjTranspose _
  proj_mul_self _ _ := diagB_mul_self _

/-- The adversary `A` with its final projector replaced by the diagonal projector onto the
    basis states on which `g` holds. -/
def QAdv.withFinalB (A : QAdv m n w q) (g : Fin (m * n * w) → Bool) : QAdv m n w q where
  U := A.U
  init := A.init
  final := diagB g
  final_conjTranspose := diagB_conjTranspose g
  final_mul_self := diagB_mul_self g

/-- The product of two diagonal projectors is the projector of the conjunction. -/
theorem diagB_mul_diagB {d : ℕ} (f g : Fin d → Bool) :
    diagB f * diagB g = diagB (fun k => f k && g k) := by
  rw [diagB, diagB, diagB, Matrix.diagonal_mul_diagonal]
  congr 1; funext k
  cases f k <;> cases g k <;> simp

/-- The trace of a matrix conjugated by a diagonal projector is the sum of its diagonal
    entries on the basis states of the projector. -/
theorem trace_diagB_conj {d : ℕ} (f : Fin d → Bool) (M : Matrix (Fin d) (Fin d) ℂ) :
    (diagB f * M * (diagB f)ᴴ).trace = ∑ k, if f k then M k k else 0 := by
  rw [diagB_conjTranspose]
  simp only [diagB, Matrix.trace, Matrix.diag, Matrix.diagonal_mul, Matrix.mul_diagonal]
  refine Finset.sum_congr rfl fun k _ => ?_
  cases f k <;> simp

/-- The diagonal entries of a positive semidefinite matrix have nonnegative real part. -/
theorem re_diag_nonneg {d : ℕ} {M : Matrix (Fin d) (Fin d) ℂ} (hM : M.PosSemidef) (k : Fin d) :
    0 ≤ (M k k).re :=
  (Complex.nonneg_iff.mp (hM.diag_nonneg (i := k))).1

end Pred

/-! ## Appending a unitary and lifting a chain -/

section Chain

variable {d : ℕ}

/-- The unitaries `U` with `P` applied after the last one. -/
def postU {q : ℕ} (P : Matrix.unitaryGroup (Fin d) ℂ)
    (U : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) :
    Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ :=
  fun i => if i = Fin.last q then P * U i else U i

/-- Applying `P` after the last unitary multiplies the chain operator by `P` on the left. -/
theorem chainOp_postU (O : Matrix (Fin d) (Fin d) ℂ) (P : Matrix.unitaryGroup (Fin d) ℂ) :
    ∀ (q : ℕ) (U : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ),
      chainOp O q (postU P U) = (P : Matrix (Fin d) (Fin d) ℂ) * chainOp O q U
  | 0, U => by simp [chainOp, postU]
  | q + 1, U => by
    have ht : Fin.tail (postU P U) = postU P (Fin.tail U) := by
      funext i
      simp [Fin.tail, postU]
    have h0 : postU P U 0 = U 0 := by
      simp [postU]
    simp only [chainOp, ht, h0, chainOp_postU O P q, Matrix.mul_assoc]

/-- The chain operator of lifted unitaries and a lifted oracle is the lift of the chain
    operator. -/
theorem chainOp_liftU {c d' : ℕ} (e : Fin (d * c) ≃ Fin d') (O : Matrix (Fin d) (Fin d) ℂ) :
    ∀ (q : ℕ) (U : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ),
      chainOp (kr e O 1) q (liftU e ∘ U) = kr e (chainOp O q U) 1
  | 0, U => rfl
  | q + 1, U => by
    have ih := chainOp_liftU e O q (Fin.tail U)
    simp only [chainOp]
    rw [show Fin.tail (liftU e ∘ U) = liftU e ∘ Fin.tail U from rfl, ih]
    simp [kr_mul]

end Chain

/-! ## Writing the point of the final test into the query register -/

section Move

variable {m n w q : ℕ}

/-- The index of `((x, y), z)` and the new ancilla value `a` on the register with the ancilla
    `Fin m` appended to the work register. -/
def regIdx (m n w : ℕ) : ((Fin m × Fin n) × Fin w) × Fin m ≃ Fin (m * n * (w * m)) :=
  ((oracleIndex m n w).prodCongr (Equiv.refl _)).trans
    ((finProdEquiv (m * n * w) m).trans (ancE m n w m))

/-- The predicate of the verifier of `moveAdv F p` at the point `x` and the challenge `θ`: the
    basis state of `F` recovered from the moved registers has the point `x` and passes the
    test `g` at `θ`. -/
def moveAcc (p : Fin (m * n * w) → Fin m) (g : Fin (m * n * w) → Fin n → Bool)
    (x : Fin m) (θ : Fin n) (j : Fin (m * n * (w * m))) : Bool :=
  let u := (regIdx m n w).symm j
  let k := oracleIndex m n w ((u.2, u.1.1.2), u.1.2)
  decide (x = p k) && g k θ

/-- The entries of `kr` at the register indices are products of entries. -/
theorem kr_regIdx_apply (A : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ)
    (B : Matrix (Fin m) (Fin m) ℂ) (t t' : (Fin m × Fin n) × Fin w) (z z' : Fin m) :
    kr (ancE m n w m) A B (regIdx m n w (t, z)) (regIdx m n w (t', z')) =
      A (oracleIndex m n w t) (oracleIndex m n w t') * B z z' := by
  simp [kr, regIdx, kronecker_apply]

/-- The query register of the index of `((x, y), z)` is `x`. -/
theorem xPart_oracleIndex (t : (Fin m × Fin n) × Fin w) :
    xPart m n w (oracleIndex m n w t) = t.1.1 := by
  simp [xPart, oracleIndex]

/-- The query register of the moved register is the query register of the original one. -/
theorem xPart_regIdx (t : (Fin m × Fin n) × Fin w) (z : Fin m) :
    xPart m n (w * m) (regIdx m n w (t, z)) = t.1.1 := by
  have h := congrFun (congrFun (projS_lift (m := m) (n := n) (w := w) (c := m) {t.1.1})
    (regIdx m n w (t, z))) (regIdx m n w (t, z))
  rw [kr_regIdx_apply, projS_eq_diagonal, projS_eq_diagonal] at h
  simpa [indS, Matrix.diagonal_apply, xPart_oracleIndex] using h

/-- The projector onto the query value `x` is the diagonal projector of `xPart = x`. -/
theorem projS_singleton_eq_diagB (x : Fin m) :
    projS m n w {x} = diagB fun j => decide (xPart m n w j = x) := by
  rw [projS_eq_diagonal, diagB]
  congr 1; funext j
  simp [indS]

variable [NeZero m]

/-- The permutation `((x, y), z), a ↦ ((a + p (x, y, z), y), z), x` of the coordinates: the
    query register moves into the ancilla and the point `p` is added into the query register. -/
def movePermAux (p : Fin (m * n * w) → Fin m) : Equiv.Perm (((Fin m × Fin n) × Fin w) × Fin m) where
  toFun u := (((u.2 + p (oracleIndex m n w u.1), u.1.1.2), u.1.2), u.1.1.1)
  invFun v := (((v.2, v.1.1.2), v.1.2), v.1.1.1 - p (oracleIndex m n w ((v.2, v.1.1.2), v.1.2)))
  left_inv u := by simp
  right_inv v := by simp

/-- `movePermAux p` on the register indices. -/
def movePerm (p : Fin (m * n * w) → Fin m) : Equiv.Perm (Fin (m * n * (w * m))) :=
  (regIdx m n w).permCongr (movePermAux p)

/-- `movePerm p` acts on the register indices as `movePermAux p` on the coordinates. -/
theorem movePerm_regIdx (p : Fin (m * n * w) → Fin m) (u : ((Fin m × Fin n) × Fin w) × Fin m) :
    movePerm p (regIdx m n w u) = regIdx m n w (movePermAux p u) := by
  simp [movePerm, Equiv.permCongr_apply]

/-- The adversary `F` on the register with the ancilla `Fin m` started in `|0⟩`, followed by the
    permutation unitary of `movePerm p`: at the end its query register holds the point `p` of
    the final state of `F` and the ancilla holds the query register of `F`. Its query count is
    the one of `F`. -/
def moveAdv (F : QAdv m n w q) (p : Fin (m * n * w) → Fin m) : QAdv m n (w * m) q where
  U := postU (permUnitary (movePerm p)) (liftU (ancE m n w m) ∘ F.U)
  init := liftInit F.init
  final := kr (ancE m n w m) F.final 1
  final_conjTranspose := by rw [kr_conjTranspose, F.final_conjTranspose, conjTranspose_one]
  final_mul_self := by rw [kr_mul, F.final_mul_self, one_mul]

variable [NeZero n]

/-- The run operator of `moveAdv F p` is the permutation unitary after the lifted run
    operator of `F`. -/
theorem runOp_moveAdv (F : QAdv m n w q) (p : Fin (m * n * w) → Fin m) (H : Fin m → Fin n) :
    runOp (moveAdv F p) H =
      (permUnitary (movePerm p) : Matrix _ _ ℂ) * kr (ancE m n w m) (runOp F H) 1 := by
  unfold runOp moveAdv
  simp only
  rw [chainOp_postU, oracleU_lift, chainOp_liftU]

/-- A final test `g k (H (p k))` that reads the oracle at the point `p k` of the final basis
    state: its acceptance probability is the sum over `x` of the probability that `moveAdv F p`
    outputs `x` and is accepted by the verifier of `moveAcc p g` at `(x, H x)`. -/
theorem prOut_withFinalB_eq_sum_prOutAt (F : QAdv m n w q) (p : Fin (m * n * w) → Fin m)
    (g : Fin (m * n * w) → Fin n → Bool) (H : Fin m → Fin n) :
    prOut (F.withFinalB fun k => g k (H (p k))) H =
      ∑ x, prOutAt ((moveAdv F p).withVerifier (QVerifier.ofPred (moveAcc p g)) x (H x)) H x := by
  set N := runOp F H * F.init.val * (runOp F H)ᴴ with hN
  set M := runOp (moveAdv F p) H * (moveAdv F p).init.val * (runOp (moveAdv F p) H)ᴴ with hMdef
  have hMpsd : M.PosSemidef := (moveAdv F p).init.psd.mul_mul_conjTranspose_same _
  have hL : prOut (F.withFinalB fun k => g k (H (p k))) H =
      ENNReal.ofReal (∑ k, if g k (H (p k)) then (N k k).re else 0) := by
    unfold prOut prTrue_Q
    rw [run_branch_true]
    have hc : (F.withFinalB fun k => g k (H (p k))).final *
        runOp (F.withFinalB fun k => g k (H (p k))) H *
        (F.withFinalB fun k => g k (H (p k))).init.val *
        ((F.withFinalB fun k => g k (H (p k))).final *
          runOp (F.withFinalB fun k => g k (H (p k))) H)ᴴ =
        diagB (fun k => g k (H (p k))) * N * (diagB fun k => g k (H (p k)))ᴴ := by
      simp only [hN, QAdv.withFinalB, runOp, conjTranspose_mul, Matrix.mul_assoc]
    rw [hc, trace_diagB_conj, Complex.re_sum]
    refine congrArg _ (Finset.sum_congr rfl fun k _ => ?_)
    split_ifs <;> simp
  have hR : ∀ x, prOutAt ((moveAdv F p).withVerifier (QVerifier.ofPred (moveAcc p g)) x (H x))
      H x = ENNReal.ofReal
        (∑ j, if (moveAcc p g x (H x) j && decide (xPart m n (w * m) j = x)) then (M j j).re
          else 0) := by
    intro x
    unfold prOutAt prTrue_Q
    rw [qbind_decide_eq_branch_true, outRun_branch]
    simp only [QAdv.withVerifier, QVerifier.ofPred]
    rw [projS_singleton_eq_diagB, diagB_mul_diagB]
    have hc : ∀ (D R ρ : Matrix (Fin (m * n * (w * m))) (Fin (m * n * (w * m))) ℂ),
        D * R * ρ * (D * R)ᴴ = D * (R * ρ * Rᴴ) * Dᴴ := fun D R ρ => by
      simp only [conjTranspose_mul, Matrix.mul_assoc]
    rw [hc, trace_diagB_conj, Complex.re_sum]
    refine congrArg _ (Finset.sum_congr rfl fun k _ => ?_)
    split_ifs <;> simp [hMdef, runOp]
  have hM : ∀ j, M j j =
      kr (ancE m n w m) N (ancProj 0) ((movePerm p).symm j) ((movePerm p).symm j) := by
    have hkr : kr (ancE m n w m) (runOp F H) 1 * kr (ancE m n w m) F.init.val (ancProj 0) *
        (kr (ancE m n w m) (runOp F H) 1)ᴴ = kr (ancE m n w m) N (ancProj 0) := by
      rw [kr_conjTranspose, conjTranspose_one, kr_mul, kr_mul, one_mul, mul_one]
    have hMe : M = (kr (ancE m n w m) N (ancProj 0)).submatrix (movePerm p).symm
        (movePerm p).symm := by
      rw [hMdef, runOp_moveAdv, ← permUnitary_conj, ← hkr]
      change _ * kr (ancE m n w m) F.init.val (ancProj 0) * _ = _
      simp only [conjTranspose_mul, Matrix.mul_assoc]
    intro j
    rw [hMe, Matrix.submatrix_apply]
  have hsum : ∀ j, (∑ x : Fin m,
      if (moveAcc p g x (H x) j && decide (xPart m n (w * m) j = x)) then (M j j).re else 0) =
      if moveAcc p g (xPart m n (w * m) j) (H (xPart m n (w * m) j)) j then (M j j).re
        else 0 := by
    intro j
    rw [Finset.sum_eq_single (xPart m n (w * m) j)]
    · simp
    · intro b _ hb
      simp [Ne.symm hb]
    · simp
  rw [hL, Finset.sum_congr rfl fun x _ => hR x, ← ENNReal.ofReal_sum_of_nonneg]
  · congr 1
    rw [Finset.sum_comm]
    simp_rw [hsum, hM]
    rw [← Equiv.sum_comp (movePerm p)]
    simp only [Equiv.symm_apply_apply]
    rw [← (regIdx m n w).sum_comp, Fintype.sum_prod_type, ← (oracleIndex m n w).sum_comp]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [Finset.sum_eq_single 0]
    · simp [movePerm_regIdx, kr_regIdx_apply, movePermAux, xPart_regIdx, moveAcc, ancProj]
    · intro z _ hz
      simp [kr_regIdx_apply, ancProj, hz]
    · simp
  · intro x _
    refine Finset.sum_nonneg fun j _ => ?_
    split_ifs
    · exact re_diag_nonneg hMpsd j
    · exact le_rfl

end Move

/-! ## The round outcomes in the flattened register -/

section Outcomes

/-- An index of the register with one more ancilla, split into an index of the register and the
    ancilla digit; its inverse is the index map of `kr (ancE m n w c)`. -/
def ancSplit (m n w c : ℕ) : Fin (m * n * (w * c)) ≃ Fin (m * n * w) × Fin c :=
  (ancE m n w c).symm.trans (finProdEquiv (m * n * w) c).symm

/-- An index of the flattened register with `k` ancillas, split into an index of the register
    before flattening and the `k` ancilla digits; digit `j` is the ancilla that `peel` adds for
    round `j`. -/
def ancDigits (m n c : ℕ) : (k : ℕ) → {w : ℕ} →
    Fin (m * n * ancW c k w) ≃ Fin (m * n * w) × (Fin k → Fin c)
  | 0, _ => (Equiv.prodUnique _ _).symm
  | k + 1, w =>
    (ancDigits m n c k (w := w * c)).trans <|
      ((ancSplit m n w c).prodCongr (Equiv.refl _)).trans <|
        (Equiv.prodAssoc _ _ _).trans <|
          (Equiv.refl _).prodCongr (Fin.consEquiv fun _ : Fin (k + 1) => Fin c)

/-- The round outcomes of a basis state of the flattened register: its `k` ancilla digits. -/
def roundOutcomes (m n c : ℕ) {k w : ℕ} (i : Fin (m * n * ancW c k w)) : Fin k → Fin c :=
  (ancDigits m n c k i).2

variable {m n w c k : ℕ}

/-- The basis state with register index `b` and ancilla digits `y` has round outcomes `y`: the
    outcome of round `j` is the `j`-th ancilla digit. -/
theorem roundOutcomes_ancDigits_symm (b : Fin (m * n * w)) (y : Fin k → Fin c) :
    roundOutcomes m n c ((ancDigits m n c k).symm (b, y)) = y := by
  simp [roundOutcomes]

/-- The outcome of round `0` is the digit of the ancilla that `peel` adds first, and the outcome
    of round `j + 1` is the outcome of round `j` of the register that contains this ancilla. -/
theorem roundOutcomes_succ (i : Fin (m * n * ancW c (k + 1) w)) :
    roundOutcomes m n c i = Fin.cons (ancSplit m n w c (ancDigits m n c k (w := w * c) i).1).2
      (roundOutcomes m n c (k := k) (w := w * c) i) :=
  rfl

end Outcomes

/-! ## The quantum EUF-CMA game -/

section Game

variable {m n w q k c a T : ℕ} {Msg PK SK Sig X Y : Type}

/-- A quantum EUF-CMA adversary: per public key a multi-round adversary with superposition
    access to the hash and `k` classical signing rounds, started in a pure state, and the
    forgery read from a basis state of its flattened register. The round outcomes are not
    chosen by the adversary: the game reads them from the round-outcome ancillas of the basis
    state (`roundOutcomes`). -/
structure QSigAdv (m n w q k c a T : ℕ) (Msg PK Sig : Type) where
  /-- The multi-round adversary at a public key. -/
  run : PK → QAdvMR m n w q k c a
  /-- The initial state is pure. -/
  pure : ∀ pk, ∃ ψ : Fin (m * n * w) → ℂ, (run pk).init.val = Matrix.vecMulVec ψ (star ψ)
  /-- The forgery read from a basis state of the flattened register. -/
  forge : Fin (m * n * ancW c k w) → Msg × Sig

/-- The signing table of the secret key `sk`, the hash `H` and the coin table `R`: the round
    outcome `eQ (μ, τ)` is answered by the encoding `eA` of the signature of `μ` with the coins
    `R (μ, τ)`. -/
def signTab (S : QROMSig Msg PK SK Sig X Y) (eQ : Msg × Fin T ≃ Fin c) (eA : Option Sig ≃ Fin a)
    (sk : SK) (H : X → Y) (R : Msg × Fin T → S.Coins) : Fin c → Fin a :=
  fun i => eA (S.sign H sk (eQ.symm i).1 (R (eQ.symm i)))

/-- The hash `X → Y` of an oracle table `Fin m → Fin n` through the encodings `eX`, `eY`. -/
def hashOf (eX : X ≃ Fin m) (eY : Y ≃ Fin n) (H : Fin m → Fin n) : X → Y :=
  fun x => eY.symm (H (eX x))

/-- The verification point of the forgery of a basis state, encoded in `Fin m`. -/
def forgePoint (S : QROMSig Msg PK SK Sig X Y) (eX : X ≃ Fin m)
    (A : QSigAdv m n w q k c a T Msg PK Sig) (pk : PK) : Fin (m * n * ancW c k w) → Fin m :=
  fun i => eX (S.point pk (A.forge i).1 (A.forge i).2)

/-- The winning test of a basis state given the encoded hash value `θ` at its verification
    point: the forgery passes `check` and its message differs from the message, decoded by
    `eQ`, of the outcome of every round, read from the round-outcome ancillas of the basis
    state by `roundOutcomes`. -/
def forgeTest [DecidableEq Msg] (S : QROMSig Msg PK SK Sig X Y) (eY : Y ≃ Fin n)
    (eQ : Msg × Fin T ≃ Fin c) (A : QSigAdv m n w q k c a T Msg PK Sig) (pk : PK) :
    Fin (m * n * ancW c k w) → Fin n → Bool :=
  fun i θ => S.check pk (A.forge i).1 (A.forge i).2 (eY.symm θ) &&
    decide (∀ j, (eQ.symm (roundOutcomes m n c i j)).1 ≠ (A.forge i).1)

/-- The probability that `A` wins at the key pair `ks`, the oracle table `H` and the coin table
    `R`: the flattened run of `A` against `H` with the signing table `signTab`, followed by the
    projector onto the basis states whose forgery verifies under `hashOf eX eY H` (the test
    `forgeTest` at the value of `H` at `forgePoint`, which is `verifyH (hashOf eX eY H)`) and
    whose message is not among the round outcomes. -/
def prForge [DecidableEq Msg] [NeZero n] [NeZero c] (S : QROMSig Msg PK SK Sig X Y)
    (eX : X ≃ Fin m) (eY : Y ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c) (eA : Option Sig ≃ Fin a)
    (A : QSigAdv m n w q k c a T Msg PK Sig) (ks : PK × SK) (H : Fin m → Fin n)
    (R : Msg × Fin T → S.Coins) : ℝ≥0∞ :=
  prOut ((toQAdv (A.run ks.1) (signTab S eQ eA ks.2 (hashOf eX eY H) R)).withFinalB fun i =>
    forgeTest S eY eQ A ks.1 i (H (forgePoint S eX A ks.1 i))) H

/-- The quantum EUF-CMA advantage: the winning probability averaged over the key pair, a
    uniform coin table and a uniform oracle table. -/
def qEUFCMAAdvantage [DecidableEq Msg] [Fintype Msg] [Fintype PK] [Fintype SK] [NeZero n]
    [NeZero c] (S : QROMSig Msg PK SK Sig X Y) (eX : X ≃ Fin m) (eY : Y ≃ Fin n)
    (eQ : Msg × Fin T ≃ Fin c) (eA : Option Sig ≃ Fin a) (A : QSigAdv m n w q k c a T Msg PK Sig) :
    ℝ≥0∞ :=
  ∑ ks, S.keygen ks * ∑ R, (Fintype.card (Msg × Fin T → S.Coins) : ℝ≥0∞)⁻¹ *
    ∑ H, (Fintype.card (Fin m → Fin n) : ℝ≥0∞)⁻¹ * prForge S eX eY eQ eA A ks H R

/-- The winning probability in the shape of `fiatShamir_random_oracle`: the flattened
    adversary followed by the unitary that moves its query register into an ancilla and writes
    the verification point of its forgery into it, tested at `(x, H x)` by the verifier of the
    winning predicate and summed over `x`. -/
theorem prForge_eq_sum_prOutAt [DecidableEq Msg] [NeZero m] [NeZero n] [NeZero c]
    (S : QROMSig Msg PK SK Sig X Y) (eX : X ≃ Fin m) (eY : Y ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c)
    (eA : Option Sig ≃ Fin a) (A : QSigAdv m n w q k c a T Msg PK Sig) (ks : PK × SK)
    (H : Fin m → Fin n) (R : Msg × Fin T → S.Coins) :
    prForge S eX eY eQ eA A ks H R =
      ∑ x, prOutAt ((moveAdv (toQAdv (A.run ks.1) (signTab S eQ eA ks.2 (hashOf eX eY H) R))
          (forgePoint S eX A ks.1)).withVerifier
        (QVerifier.ofPred (moveAcc (forgePoint S eX A ks.1) (forgeTest S eY eQ A ks.1)))
        x (H x)) H x :=
  prOut_withFinalB_eq_sum_prOutAt _ (forgePoint S eX A ks.1) (forgeTest S eY eQ A ks.1) H

/-- The winning probability is at most one. -/
theorem prForge_le_one [DecidableEq Msg] [NeZero n] [NeZero c] (S : QROMSig Msg PK SK Sig X Y)
    (eX : X ≃ Fin m) (eY : Y ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c) (eA : Option Sig ≃ Fin a)
    (A : QSigAdv m n w q k c a T Msg PK Sig) (ks : PK × SK) (H : Fin m → Fin n)
    (R : Msg × Fin T → S.Coins) : prForge S eX eY eQ eA A ks H R ≤ 1 := by
  suffices h : ∀ B : QAdv m n (ancW c k w) (flatQ q k q), prOut B H ≤ 1 from h _
  intro B
  unfold prOut prTrue_Q
  have h : ((run B H).branch true B.init.val).trace.re ≤ B.init.val.trace.re :=
    calc ((run B H).branch true B.init.val).trace.re
        ≤ ∑' b, ((run B H).branch b B.init.val).trace.re :=
          (trace_re_summable ((run B H).branch_summable _)).le_tsum true
            (fun b _ => trace_re_nonneg_of_psd ((run B H).branch_psd b _ B.init.psd))
      _ = (∑' b, ((run B H).branch b B.init.val).trace).re :=
          (Complex.re_tsum (trace_summable ((run B H).branch_summable _))).symm
      _ ≤ B.init.val.trace.re := (run B H).branch_stp _ B.init.psd
  rw [B.init.tr_one, Complex.one_re] at h
  exact ENNReal.ofReal_le_one.mpr h

end Game

end CatCrypt.Quantum.QROM
