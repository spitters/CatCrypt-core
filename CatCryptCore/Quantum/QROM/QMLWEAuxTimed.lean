/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.AdversariesTimed
import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveReduction.Basic
public import CatCryptCore.Tactics.StdCosts

/-!
# Time certificates of the module-LWE reductions of `QMLWEAux`

The costed forms `qRedEnc.timed` and `qRedExt.timed` of the two hops from an IND-CPA adversary
with oracle access to module-LWE distinguishers with oracle access, derived by
`derive_reduction`, with their erasure theorems. Each runs the multi-round circuit of the
adversary unchanged after computing the challenge ciphertext, so its time is that of the
adversary plus the cost of the encryption (for `qRedExt`, of the compression, the ring addition
and the message encoding), of the message choice, and a constant.

## Main results

* `qRedEnc.timeBound`, `qRedExt.timeBound` — the time of each hop
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Quantum.QROM

derive_reduction qRedEnc

derive_reduction qRedExt

/-- **Time of `qRedEnc`.** If every circuit of the costed adversary runs within `T`, the
encryption costs at most `E` and the message choice at most `Ms`, then every circuit of the
reduction runs within `T + E + Ms + 5`. -/
theorem qRedEnc.timeBound {m n W q k c a : ℕ} {PK SK M C R K ι : Type}
    (S : CatCrypt.Crypto.PKE.Games.Scheme PK SK M C R) (D : QIndAuxAdv ι m n W q k c a PK C K M)
    (b : Bool) (prog : PK → C → K → ι → QAdvMRT m n W q k c a)
    (progCost : PK → C → K → ι → ℕ) (encCost : PK → M → R → ℕ) (msgsCost : PK → ι → ℕ)
    (T E Ms : ℕ)
    (hT : ∀ pk cst h i, QAdvMRT.StepTimeBound (progCost pk cst h i, prog pk cst h i) T)
    (hE : ∀ pk x r, encCost pk x r ≤ E) (hM : ∀ pk i, msgsCost pk i ≤ Ms) :
    (qRedEnc.timed S D b prog progCost encCost msgsCost).TimeBound (T + E + Ms + 5) := by
  intro pk h x
  have := hT pk (encPoint S D b pk x) h x.1
  have := hE pk (if b = true then (D.msgs pk x.1).2 else (D.msgs pk x.1).1) x.2
  have := hM pk x.1
  simp only [QAdvMRT.StepTimeBound, qRedEnc.timed, qRedEnc.prog.tree.timed] at *
  omega

/-- **Time of `qRedExt`.** If every circuit of the costed adversary runs within `T`, and the
compression, the ring addition, the message encoding and the message choice cost at most `F`,
`Ad`, `En` and `Ms`, then every circuit of the reduction runs within
`T + F + Ad + En + Ms + 7`. -/
theorem qRedExt.timeBound {m n W q k c a : ℕ} {C K ι : Type}
    (B : CatCrypt.Crypto.MLKEM.MLWE_PKE_Basic.Params)
    (f : CatCrypt.Crypto.MLKEM.MLWE_PKE_Basic.CT B → C)
    (fCost : CatCrypt.Crypto.MLKEM.MLWE_PKE_Basic.CT B → ℕ)
    (D : QIndAuxAdv ι m n W q k c a (CatCrypt.Crypto.MLKEM.MLWE_PKE_Basic.PK B) C K B.PT)
    (b : Bool) (prog : CatCrypt.Crypto.MLKEM.MLWE_PKE_Basic.PK B → C → K → ι →
      QAdvMRT m n W q k c a)
    (progCost : CatCrypt.Crypto.MLKEM.MLWE_PKE_Basic.PK B → C → K → ι → ℕ)
    (ring_addCost : B.R → B.R → ℕ) (m_encodeCost : B.PT → ℕ)
    (msgsCost : CatCrypt.Crypto.MLKEM.MLWE_PKE_Basic.PK B → ι → ℕ) (T F Ad En Ms : ℕ)
    (hT : ∀ pk cst h i, QAdvMRT.StepTimeBound (progCost pk cst h i, prog pk cst h i) T)
    (hF : ∀ u, fCost u ≤ F) (hA : ∀ x y, ring_addCost x y ≤ Ad) (hEn : ∀ x, m_encodeCost x ≤ En)
    (hM : ∀ pk i, msgsCost pk i ≤ Ms) :
    (qRedExt.timed B f fCost D b prog progCost ring_addCost m_encodeCost msgsCost).TimeBound
      (T + F + Ad + En + Ms + 7) := by
  intro x h i
  have := hT (x.1, x.2.1) (extPoint B f D b x i) h i
  have := hF (x.2.2.1, B.ring_add x.2.2.2
    (B.m_encode (if b = true then (D.msgs (x.1, x.2.1) i).2 else (D.msgs (x.1, x.2.1) i).1)))
  have := hA x.2.2.2
    (B.m_encode (if b = true then (D.msgs (x.1, x.2.1) i).2 else (D.msgs (x.1, x.2.1) i).1))
  have := hEn (if b = true then (D.msgs (x.1, x.2.1) i).2 else (D.msgs (x.1, x.2.1) i).1)
  have := hM (x.1, x.2.1) i
  simp only [QAdvMRT.StepTimeBound, qRedExt.timed, qRedExt.prog.tree.timed] at *
  omega

end CatCrypt.Quantum.QROM
