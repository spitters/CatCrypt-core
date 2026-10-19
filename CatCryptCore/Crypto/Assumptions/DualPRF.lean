/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.PRPPRFSwitching

/-!
# Dual pseudorandom functions

A function `F : K₁ → K₂ → Out` is a dual PRF when it is a PRF keyed by either argument:
under a uniform first argument it is indistinguishable from a random function of the second
argument, and under a uniform second argument it is indistinguishable from a random function
of the first argument (Bellare, *New Proofs for NMAC and HMAC*, CRYPTO 2006; Bindel,
Brendel, Fischlin, Goncalves, Stebila, *Hybrid Key Exchange in TLS 1.3*, J. Cryptology 2023).
The adversary chooses the other argument adaptively: it is an oracle adversary
(`OracleAdv`) whose queries are values of the other argument.

Each direction is the adaptive PRF advantage `PRPPRF.PRF_q_Advantage` of the core PRF game:
the real game samples the key once and answers each query `x` by `F k x`, the ideal game
answers with a lazily sampled random function. The advantage is stated for each adversary;
there is no uniform bound.

## Main definitions

* `DualPRF_Left_Advantage F A` — the advantage of `A` against `F` keyed by its first argument
* `DualPRF_Right_Advantage F A` — the advantage of `A` against `F` keyed by its second
  argument, the PRF advantage of `Function.swap F`

## Main results

* `DualPRF_Right_Advantage_eq_left_swap` — the right advantage of `F` is the left advantage
  of `Function.swap F`
* `DualPRF_Left_Advantage_of_isQueryBound_zero`, `DualPRF_Right_Advantage_of_isQueryBound_zero`
  — an adversary without queries has advantage zero
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Assumptions

open CatCrypt.Crypto CatCrypt.Crypto.PRPPRF
open scoped ENNReal

variable {K₁ K₂ Out : Type} [Fintype K₁] [Nonempty K₁] [Fintype K₂] [Nonempty K₂]
  [DecidableEq K₁] [DecidableEq K₂] [DecidableEq Out] [Fintype Out] [Nonempty Out]

/-- The advantage of `A` against `F` keyed by a uniform first argument: `A` queries values
of the second argument and receives `F k x` in the real game, a lazily sampled random
function in the ideal game. -/
noncomputable def DualPRF_Left_Advantage (F : K₁ → K₂ → Out) (A : OracleAdv K₂ Out Bool) :
    ℝ≥0∞ :=
  PRF_q_Advantage F A

/-- The advantage of `A` against `F` keyed by a uniform second argument: `A` queries values
of the first argument and receives `F x k` in the real game, a lazily sampled random
function in the ideal game. -/
noncomputable def DualPRF_Right_Advantage (F : K₁ → K₂ → Out) (A : OracleAdv K₁ Out Bool) :
    ℝ≥0∞ :=
  PRF_q_Advantage (Function.swap F) A

omit [Fintype K₁] [Nonempty K₁] [DecidableEq K₂] [DecidableEq Out] in
/-- The right advantage of `F` is the left advantage of `Function.swap F`. -/
theorem DualPRF_Right_Advantage_eq_left_swap (F : K₁ → K₂ → Out) (A : OracleAdv K₁ Out Bool) :
    DualPRF_Right_Advantage F A = DualPRF_Left_Advantage (Function.swap F) A :=
  rfl

omit [Fintype K₂] [Nonempty K₂] [DecidableEq K₁] [DecidableEq Out] in
/-- An adversary without queries has left advantage zero. -/
theorem DualPRF_Left_Advantage_of_isQueryBound_zero (F : K₁ → K₂ → Out)
    {A : OracleAdv K₂ Out Bool} (hA : A.IsQueryBound 0) : DualPRF_Left_Advantage F A = 0 :=
  PRF_q_Advantage_of_isQueryBound_zero F hA

omit [Fintype K₁] [Nonempty K₁] [DecidableEq K₂] [DecidableEq Out] in
/-- An adversary without queries has right advantage zero. -/
theorem DualPRF_Right_Advantage_of_isQueryBound_zero (F : K₁ → K₂ → Out)
    {A : OracleAdv K₁ Out Bool} (hA : A.IsQueryBound 0) : DualPRF_Right_Advantage F A = 0 :=
  PRF_q_Advantage_of_isQueryBound_zero _ hA

end CatCrypt.Crypto.Assumptions
