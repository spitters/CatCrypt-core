/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Examples.OneTimePad
import CatCryptCore.Deep.ReflectTactic

set_option autoImplicit false

/-!
# Demo: the reflective SSP tactic on the real one-time-pad games

`Examples/OneTimePad.lean` closes its perfect-security stack with a ~40-line
hand-written "Reflection into the Package / UC Stack" section: `otpGameRaw`, the
`IsValid` instance, `otpGameRaw_eval`, `otpGameRaw_eval_eq`, `otpGameTrue`,
`otpGameFalse`, `otp_eval_eq`, and then the four package theorems
(`otp_deepnom_zero`, `otp_nompkg_secure`, `otp_sdist_zero`, `otp_uc`).

This file reproduces the two headline package results — `otp_nompkg_secure` and
`otp_uc` — on the **same** one-time-pad games, each in a **single**
`reflect_ofOracle_*` invocation, given only the shallow game family and the one
shallow coupling reused from `OneTimePad`.
-/

namespace CatCrypt.Examples.ReflectTacticDemo

open CatCrypt.Core CatCrypt.Crypto CatCrypt.Deep
open CatCrypt.Examples.OTP

/-- The shallow one-time-pad oracle body (the `SPComp` game the package reflects):
    sample a uniform key and return the ciphertext `k ⊕ m`. -/
noncomputable def otpBody (m : Bool) : SPComp Bool :=
  SPComp.bind (SPComp.sample Bool) (fun k => SPComp.pure (xor k m))

/-- The single shallow coupling the tactic consumes, reused from `OneTimePad`:
    the two one-time-pad game bodies coincide as `SPComp` computations (each is
    the uniform sample). Obtained from `OneTimePad`'s reflected coupling
    `otp_eval_eq` via the round-trip `otpGameRaw_eval`. -/
theorem otpBody_eq (m₀ m₁ : Bool) : otpBody m₀ = otpBody m₁ := by
  unfold otpBody
  rw [← otpGameRaw_eval m₀, ← otpGameRaw_eval m₁]
  exact otp_eval_eq m₀ m₁

/-- **`otp_nompkg_secure` reproduced in one invocation.** Package-level perfect
    security of the reflected OTP games, from the shallow body + shallow coupling. -/
theorem demo_otp_nompkg_secure (m₀ m₁ : Bool) :
    NomPkgSecure (otpGameTrue m₀) (otpGameFalse m₁) (fun _ => 0) :=
  reflect_ofOracle_nompkg_secure 1 (fun _ => otpBody m₀) (fun _ => otpBody m₁)
    (fun _ => otpBody_eq m₀ m₁)

/-- **`otp_uc` reproduced in one invocation.** Perfect UC emulation of the linked
    OTP game families over the trivial-leak interface, from the shallow body +
    shallow coupling. -/
theorem demo_otp_uc (m₀ m₁ : Bool) :
    UCEmulates 0 ⟨NomPackage, Bool, Empty, Empty, Bool⟩
      (fun A => SPComp.map (Sum.inl : Bool → Bool ⊕ Empty)
        (runPkg (DeepPackage.link A.pkg (otpGameTrue m₀).pkg)))
      (fun A => SPComp.map (Sum.inl : Bool → Bool ⊕ Empty)
        (runPkg (DeepPackage.link A.pkg (otpGameFalse m₁).pkg))) :=
  reflect_ofOracle_uc 1 (fun _ => otpBody m₀) (fun _ => otpBody m₁)
    (fun _ => otpBody_eq m₀ m₁)

end CatCrypt.Examples.ReflectTacticDemo
