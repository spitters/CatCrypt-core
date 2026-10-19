/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Assumptions.LWE
public import CatCryptCore.Tactics.DeriveReduction

/-!
# IND-CPA security of LWE-style public-key encryption

The public-key encryption of Regev and Lyubashevsky–Peikert–Regev over an abstract
interface. Key generation samples an LWE instance: the public key is `(a, b)` with
`b = a·s + e`. Encryption of `m` under `(a, b)` samples coins `r` and noise `n` and outputs
`(u, addMsg m v)`, where `(u, v) = encMulAdd (a, b) r n` is `(a·r + e₁, b·r + e₂)` and
`addMsg m` adds the encoding of `m`, a bijection of the second component.

The scheme `LWEPKE` carries the key LWE instance `keyLWE`; the encryption map forms the
second LWE instance `encLWE`, whose matrix is a uniform public key `(a, u)`, whose secret is
the coins and whose error is the noise. Ring-LWE takes every type to be the ring `R_q`
(`encMulAdd (a, b) r (e₁, e₂) = (a·r + e₁, b·r + e₂)`), Module-LWE takes `a` a matrix, `s`,
`e`, `b`, `r`, `e₁`, `u` vectors and `e₂`, `v` ring elements
(`encMulAdd (a, b) r (e₁, e₂) = (aᵀ·r + e₁, bᵀ·r + e₂)`).

The proof has two hops for each message: the public key is pseudorandom (`keyRed`, a
distinguisher for `keyLWE`), then, under the uniform public key, the pair `(u, v)` is
pseudorandom (`ctRed`, a distinguisher for `encLWE`). In the last game the ciphertext is
uniform and the encoding of the message is absorbed by the bijection `addMsg m`.

## Main definitions

* `LWEPKE` — the abstract scheme; `LWEPKE.encLWE` — the encryption map as an LWE instance
* `LWEPKE.keyGen`, `LWEPKE.encrypt`
* `LWEPKE.INDCPA_Game`, `LWEPKE.INDCPA_Advantage` — the public key and the encryption of a
  fixed message, and the advantage of distinguishing the encryptions of `m₀` and `m₁`
* `LWEPKE.Hyb1`, `LWEPKE.Hyb2` — the games with a uniform public key, and with a uniform
  public key and a uniform ciphertext
* `LWEPKE.keyRed`, `LWEPKE.ctRed` — the two reductions to decision LWE
* `keyRed.tree`, `ctRed.tree` and their costed forms (`derive_reduction`)

## Main results

* `LWEPKE.INDCPA_real_le` — the distance from the encryption of `m` to the uniform game is
  at most `LWE_Advantage keyLWE (keyRed m A) + LWE_Advantage encLWE (ctRed m A)`
* `LWEPKE.INDCPA_Advantage_le` — the IND-CPA advantage is at most the sum of these two
  advantages for `m₀` and for `m₁`
* `keyRed.tree.timeBound_timed`, `ctRed.tree.timeBound_timed` — the costed reductions run in
  the time of the adversary plus the costs of the primitives plus a constant
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Assumptions

/-- The product of two sampleable types is sampleable. -/
instance instSampleableTypeProdLWE {α β : Type} [SampleableType α] [SampleableType β] :
    SampleableType (α × β) where

end CatCrypt.Crypto.Assumptions

namespace CatCrypt.Crypto.PKE

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Assumptions
open scoped ENNReal

/-- LWE-style public-key encryption. The key instance `keyLWE` gives the public key
`(a, a·s + e)`; encryption samples coins `r : R` and noise `n : N`, computes
`(u, v) = encMulAdd (a, b) r n`, and outputs `(u, addMsg m v)`. -/
structure LWEPKE (M S E B R N U V Msg : Type) [SampleableType B] [SampleableType U]
    [SampleableType V] where
  /-- The LWE instance of key generation. -/
  keyLWE : LWEDef M S E B
  /-- Sample the encryption coins `r`. -/
  sampleRnd : SPComp R
  /-- Sample the encryption noise `n = (e₁, e₂)`. -/
  sampleNoise : SPComp N
  /-- The encryption map `((a, b), r, n) ↦ (a·r + e₁, b·r + e₂)`. -/
  encMulAdd : M × B → R → N → U × V
  /-- Add the encoding of a message to the second ciphertext component. -/
  addMsg : Msg → V → V
  /-- Adding the encoding of a message is a bijection. -/
  addMsg_bijective : ∀ m, Function.Bijective (addMsg m)
  /-- Sampling the coins is heap-independent. -/
  sampleRnd_isPure : SPComp.IsPure sampleRnd
  /-- Sampling the noise is heap-independent. -/
  sampleNoise_isPure : SPComp.IsPure sampleNoise

namespace LWEPKE

variable {M S E B R N U V Msg : Type} [SampleableType B] [SampleableType U] [SampleableType V]
variable (P : LWEPKE M S E B R N U V Msg)

/-- The encryption map as an LWE instance: the matrix is a uniform public key `(a, u)`, the
secret the coins and the error the noise. -/
noncomputable def encLWE : LWEDef (M × B) R N (U × V) where
  sampleA := do
    let a ← P.keyLWE.sampleA
    let u ← SPComp.sample B
    return (a, u)
  sampleSecret := P.sampleRnd
  sampleError := P.sampleNoise
  mulAddErr := P.encMulAdd
  sampleA_isPure := by
    simp only [SPComp.monad_bind_eq, SPComp.monad_pure_eq]
    exact SPComp.bind_isPure P.keyLWE.sampleA_isPure fun _ =>
      SPComp.bind_isPure (SPComp.sample_isPure B) fun _ => SPComp.pure_isPure _
  sampleSecret_isPure := P.sampleRnd_isPure
  sampleError_isPure := P.sampleNoise_isPure

/-- Key generation: the public key `(a, a·s + e)` and the secret `s`. -/
noncomputable def keyGen : SPComp ((M × B) × S) := do
  let a ← P.keyLWE.sampleA
  let s ← P.keyLWE.sampleSecret
  let e ← P.keyLWE.sampleError
  return ((a, P.keyLWE.mulAddErr a s e), s)

/-- Encryption of `m` under the public key `pk`. -/
noncomputable def encrypt (pk : M × B) (m : Msg) : SPComp (U × V) := do
  let r ← P.sampleRnd
  let n ← P.sampleNoise
  let c := P.encMulAdd pk r n
  return (c.1, P.addMsg m c.2)

/-- The IND-CPA game of the message `m`: the public key and an encryption of `m`. -/
noncomputable def INDCPA_Game (m : Msg) : SPComp ((M × B) × (U × V)) := do
  let k ← P.keyGen
  let c ← P.encrypt k.1 m
  return (k.1, c)

/-- The IND-CPA advantage of `A` on the messages `m₀` and `m₁`. -/
noncomputable def INDCPA_Advantage (m₀ m₁ : Msg) (A : (M × B) × (U × V) → SPComp Bool) :
    ℝ≥0∞ :=
  AdvantageA (P.INDCPA_Game m₀) (P.INDCPA_Game m₁) A

/-- The first hybrid: a uniform public key `(a, u)` and an encryption of `m` under it. -/
noncomputable def Hyb1 (m : Msg) : SPComp ((M × B) × (U × V)) := do
  let a ← P.keyLWE.sampleA
  let u ← SPComp.sample B
  let c ← P.encrypt (a, u) m
  return ((a, u), c)

/-- The second hybrid: a uniform public key and a uniform ciphertext. -/
noncomputable def Hyb2 : SPComp ((M × B) × (U × V)) := do
  let a ← P.keyLWE.sampleA
  let u ← SPComp.sample B
  let c ← SPComp.sample (U × V)
  return ((a, u), c)

/-- The reduction to the key LWE instance: on `(a, b)`, encrypt `m` under the public key
`(a, b)` and run `A`. -/
noncomputable def keyRed (m : Msg) (A : (M × B) × (U × V) → SPComp Bool) (a : M) (b : B) :
    SPComp Bool := do
  let r ← P.sampleRnd
  let n ← P.sampleNoise
  let c := P.encMulAdd (a, b) r n
  A ((a, b), (c.1, P.addMsg m c.2))

/-- The reduction to the encryption LWE instance: on the public key `pk` and the pair
`c = (u, v)`, run `A` on `pk` and `(u, addMsg m v)`. -/
noncomputable def ctRed (m : Msg) (A : (M × B) × (U × V) → SPComp Bool) (pk : M × B)
    (c : U × V) : SPComp Bool :=
  A (pk, (c.1, P.addMsg m c.2))

/-! ## Game hops -/

theorem INDCPA_Game_bind_eq (m : Msg) (A : (M × B) × (U × V) → SPComp Bool) :
    (P.INDCPA_Game m).bind A = LWE_Game_Real P.keyLWE (P.keyRed m A) := by
  simp [INDCPA_Game, keyGen, encrypt, LWE_Game_Real, keyRed, SPComp.bind_assoc]

theorem Hyb1_bind_eq_keyIdeal (m : Msg) (A : (M × B) × (U × V) → SPComp Bool) :
    (P.Hyb1 m).bind A = LWE_Game_Ideal P.keyLWE (P.keyRed m A) := by
  simp [Hyb1, encrypt, LWE_Game_Ideal, keyRed, SPComp.bind_assoc]

theorem Hyb1_bind_eq_ctReal (m : Msg) (A : (M × B) × (U × V) → SPComp Bool) :
    (P.Hyb1 m).bind A = LWE_Game_Real P.encLWE (P.ctRed m A) := by
  simp [Hyb1, encrypt, LWE_Game_Real, encLWE, ctRed, SPComp.bind_assoc]

/-- In the second hybrid the encoding of the message is absorbed by the uniform `v`. -/
theorem Hyb2_bind_eq_ctIdeal (m : Msg) (A : (M × B) × (U × V) → SPComp Bool) :
    P.Hyb2.bind A = LWE_Game_Ideal P.encLWE (P.ctRed m A) := by
  have h : ∀ k : V → SPComp Bool,
      (SPComp.sample V).bind (fun v => k (P.addMsg m v)) = (SPComp.sample V).bind k :=
    fun k => SPComp.sample_bind_equiv (Equiv.ofBijective _ (P.addMsg_bijective m)) k
  simp only [Hyb2, LWE_Game_Ideal, encLWE, ctRed, SPComp.monad_bind_eq, SPComp.monad_pure_eq,
    SPComp.bind_assoc, SPComp.pure_bind, SPComp.sample_prod_eq]
  congr 1; funext a; congr 1; funext b; congr 1; funext u
  exact (h fun v => A ((a, b), u, v)).symm

/-! ## Security -/

/-- The encryption of `m` is at distance at most the two LWE advantages from the uniform
game `Hyb2`. -/
theorem INDCPA_real_le (m : Msg) (A : (M × B) × (U × V) → SPComp Bool) :
    AdvantageA (P.INDCPA_Game m) P.Hyb2 A ≤
      LWE_Advantage P.keyLWE (P.keyRed m A) + LWE_Advantage P.encLWE (P.ctRed m A) := by
  unfold AdvantageA LWE_Advantage
  rw [P.INDCPA_Game_bind_eq m A, P.Hyb2_bind_eq_ctIdeal m A, ← P.Hyb1_bind_eq_keyIdeal m A,
    ← P.Hyb1_bind_eq_ctReal m A]
  exact advantage_triangle _ _ _

/-- **IND-CPA security from decision LWE.** For every adversary `A` and messages `m₀`,
`m₁`, the IND-CPA advantage is at most the decision-LWE advantages of the key reduction
`keyRed` and the ciphertext reduction `ctRed`, for `m₀` and for `m₁`. -/
theorem INDCPA_Advantage_le (m₀ m₁ : Msg) (A : (M × B) × (U × V) → SPComp Bool) :
    P.INDCPA_Advantage m₀ m₁ A ≤
      (LWE_Advantage P.keyLWE (P.keyRed m₀ A) + LWE_Advantage P.encLWE (P.ctRed m₀ A)) +
      (LWE_Advantage P.keyLWE (P.keyRed m₁ A) + LWE_Advantage P.encLWE (P.ctRed m₁ A)) := by
  have h₀ := P.INDCPA_real_le m₀ A
  have h₁ := P.INDCPA_real_le m₁ A
  unfold INDCPA_Advantage
  unfold AdvantageA at *
  have hsymm : Advantage (P.Hyb2.bind A) ((P.INDCPA_Game m₁).bind A) =
      Advantage ((P.INDCPA_Game m₁).bind A) (P.Hyb2.bind A) := by
    simp only [Advantage]; exact max_comm _ _
  calc _ ≤ _ := advantage_triangle _ (P.Hyb2.bind A) _
    _ ≤ _ := by rw [hsymm]; exact add_le_add h₀ h₁

end LWEPKE

/-! ## Costed reductions -/

derive_reduction LWEPKE.keyRed (adv := A)

derive_reduction LWEPKE.ctRed (adv := A)

namespace LWEPKE

variable {M S E B R N U V Msg : Type} [SampleableType B] [SampleableType U] [SampleableType V]

/-- **Time of the key reduction.** With the costed adversary `A` of time at most `T` and call
cost at most `a`, the encryption map of cost at most `te`, the message encoding of cost at most
`tm`, and the samplers of the coins and the noise of time at most `tR` and `tN`, the costed
reduction has time at most `tR + tN + T + a + 2 te + tm + 4`: the two samplers, one adversary
call, the encryption map at each of the two ciphertext components, one encoding and four
steps. -/
theorem keyRed.tree.timeBound_timed (P : LWEPKE M S E B R N U V Msg) (m : Msg)
    (A : (M × B) × (U × V) → SPTree.Timed Bool) (ACost : (M × B) × (U × V) → ℕ)
    (encMulAdd : M × B → R → N → U × V) (encMulAddCost : M × B → R → N → ℕ)
    (addMsg : Msg → V → V) (addMsgCost : Msg → V → ℕ)
    (sampleRnd : SPTree.Timed R) (sampleNoise : SPTree.Timed N)
    {T a te tm tR tN : ℕ} (hA : ∀ x, (A x).time ≤ T) (hAc : ∀ x, ACost x ≤ a)
    (he : ∀ pk r n, encMulAddCost pk r n ≤ te) (hm : ∀ m v, addMsgCost m v ≤ tm)
    (hR : sampleRnd.time ≤ tR) (hN : sampleNoise.time ≤ tN) (x : M) (y : B) :
    SPTree.Timed.stepTime (keyRed.tree.timed P m A ACost x y encMulAdd encMulAddCost addMsg
        addMsgCost sampleRnd sampleNoise) ≤ tR + tN + T + a + 2 * te + tm + 4 := by
  unfold keyRed.tree.timed
  refine (SPTree.Timed.stepTime_bind_le _ _ (tN + (T + a + 2 * te + tm + 4))
    fun r => ?_).trans (by omega)
  refine (SPTree.Timed.stepTime_bind_le _ _ (T + a + 2 * te + tm + 4)
    fun n => ?_).trans (by omega)
  simp only [SPTree.Timed.stepTime]; grind

/-- **Time of the ciphertext reduction.** With the costed adversary `A` of time at most `T`
and call cost at most `a`, and the message encoding of cost at most `tm`, the costed reduction
has time at most `T + a + tm + 2`: one adversary call, one encoding and two steps. -/
theorem ctRed.tree.timeBound_timed (P : LWEPKE M S E B R N U V Msg) (m : Msg)
    (A : (M × B) × (U × V) → SPTree.Timed Bool) (ACost : (M × B) × (U × V) → ℕ)
    (addMsg : Msg → V → V) (addMsgCost : Msg → V → ℕ)
    {T a tm : ℕ} (hA : ∀ x, (A x).time ≤ T) (hAc : ∀ x, ACost x ≤ a)
    (hm : ∀ m v, addMsgCost m v ≤ tm) (pk : M × B) (c : U × V) :
    SPTree.Timed.stepTime (ctRed.tree.timed P m A ACost pk c addMsg addMsgCost) ≤
      T + a + tm + 2 := by
  simp only [SPTree.Timed.stepTime, ctRed.tree.timed]; grind

end LWEPKE

end CatCrypt.Crypto.PKE
