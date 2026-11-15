/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.MLKEM.NegaConvAlgebra
public import CatCryptCore.Crypto.MLKEM.Compress

/-!
# The decode lemma of the ML-KEM message coding

`Compress₁` recovers a bit `b` from `Decompress₁ b + n` whenever the noise `n` has
centred absolute value `Compress.centeredAbs n ≤ 831`. Hence the decryption failure
event of the MLWE public-key encryption scheme at every module rank is contained in
the event that some coefficient of the noise `e · r + e₂ − s · e₁` has centred
absolute value at least `832`.

## Main results

* `compress1_decompress1_add` — the decode lemma for one coefficient
* `msgDecode_msgEncode_add` — the decode lemma for 256 coefficients
* `exists_large_of_msgDecode_ne` — a decoding failure has a coefficient of centred
  absolute value at least `832`
* `exists_large_noise_of_decrypt_ne` — the same for honest decryption of an honest
  encryption, at the noise of `decrypt_noise_eq`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.MLKEM.MLKEMRankInstance

open CatCrypt.Util
open MLKEM512Instance (Rq Msg compress1 decompress1 msgEncode msgDecode)
open CatCrypt.Crypto.MLKEM.Compress (centeredAbs)

/-- **The decode lemma for one coefficient.** `Compress₁` recovers the bit `b` from
`Decompress₁ b + n` whenever the centred noise `n` has absolute value at most `831`. -/
theorem compress1_decompress1_add (b : Bool) (n : Zq3329) (hn : centeredAbs n ≤ 831) :
    compress1 (decompress1 b + n) = b := by
  have hv := n.val_lt
  simp only [centeredAbs, Compress.q] at hn
  cases b
  · simp only [compress1, decompress1, Bool.false_eq_true, ↓reduceIte, zero_add,
      decide_eq_false_iff_not]
    omega
  · have h1665 : (1665 : Zq3329).val = 1665 := rfl
    simp only [compress1, decompress1, ↓reduceIte, ZMod.val_add, h1665, decide_eq_true_eq]
    omega

/-- **The decode lemma.** Decoding the encoded message plus a noise polynomial whose
centred coefficients all have absolute value at most `831` returns the message. -/
theorem msgDecode_msgEncode_add (m : Msg) (n : Rq) (hn : ∀ i, centeredAbs (n i) ≤ 831) :
    msgDecode (msgEncode m + n) = m := by
  funext i
  exact compress1_decompress1_add (m i) (n i) (hn i)

/-- The decoding failure event is contained in the event that some centred noise
coefficient has absolute value at least `832`. -/
theorem exists_large_of_msgDecode_ne (m : Msg) (n : Rq) (h : msgDecode (msgEncode m + n) ≠ m) :
    ∃ i, 832 ≤ centeredAbs (n i) := by
  by_contra hc
  push Not at hc
  exact h (msgDecode_msgEncode_add m n fun i => Nat.le_of_lt_succ (hc i))

/-- **The decryption failure event.** If honest decryption of an honest encryption of
`m` does not return `m`, some coefficient of the noise `e · r + e₂ − s · e₁` has centred
absolute value at least `832`. -/
theorem exists_large_noise_of_decrypt_ne {k : ℕ} (A : Mat k) (s e r e1 : Vec k) (e2 : Rq)
    (m : Msg)
    (h : msgDecode (MLKEM512Instance.ringSub
        (MLKEM512Instance.ringAdd
          (MLKEM512Instance.ringAdd (vecDot (vecAdd (matVecMul A s) e) r) e2) (msgEncode m))
        (vecDot s (vecAdd (matVecMul (matTranspose A) r) e1))) ≠ m) :
    ∃ i, 832 ≤ centeredAbs ((vecDot e r + e2 - vecDot s e1) i) := by
  rw [decrypt_noise_eq] at h
  exact exists_large_of_msgDecode_ne m _ h

end CatCrypt.Crypto.MLKEM.MLKEMRankInstance
