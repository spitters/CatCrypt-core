/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCMonad.ConcurrentSys
public import CatCryptCore.Crypto.UCPullback

/-!
# The dummy-adversary theorem for environment-dependent bounds

Emulation against every adversary system (`UCEmulatesSys R F b`) with an environment-dependent
bound `b` is compared with realization behind a simulator (`Realizes R (F.attach S) b`).

* `UCEmulatesSys.realizes_dummy`: emulation against every adversary gives a realization behind
  a simulator with the bound `b` at the environment pulled back through the forwarding (dummy)
  adversary, `(AdvSys.dummy AP Lk).toEnvPullback.pull Z`, which is `Z` with the dummy adversary
  absorbed.
* `ucEmulatesSys_iff_realizes_of_le`: when absorbing the dummy adversary does not increase the
  bound, emulation against every adversary with bound `b` holds iff `R` realizes `F.attach S`
  with bound `b` for some simulator `S`. At a constant bound the hypothesis holds by reflexivity,
  and the statement is `ucEmulatesSys_iff_realizes`.
-/

@[expose] public section

set_option autoImplicit false

namespace UCMonad.ConcurrentSys

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCTransparent
open scoped ENNReal

variable {φ τ AP AF Lk LF P Oh : Type}

/-- **Dummy-adversary direction.** Emulation against every adversary with bound `b` gives a
simulator `S` such that `R` realizes `F.attach S` with bound `b` at the environment pulled back
through the forwarding adversary. -/
theorem UCEmulatesSys.realizes_dummy {R : Sys τ (Event P AP) (Oh × Lk)}
    {F : Sys φ (Event P AF) (Oh × LF)}
    {b : (ζ : Type) → Env (Strat ζ (Event P AP) (Oh × Lk)) ζ → ℝ≥0∞}
    (h : UCEmulatesSys R F b) :
    ∃ (σ : Type) (S : AdvSys σ AP AF LF Lk), Realizes R (F.attach S)
      (fun ζ Z => b ((AdvSys.dummy AP Lk).toEnvPullback.Ctx ζ)
        ((AdvSys.dummy AP Lk).toEnvPullback.pull Z)) :=
  (ucEmulatesSysAgainst_dummy_iff R F _).1 (h Unit AP Lk (AdvSys.dummy AP Lk))

/-- **Dummy-adversary theorem for environment-dependent bounds.** If absorbing the forwarding
adversary does not increase the bound `b`, emulation against every adversary with bound `b` holds
iff `R` realizes `F.attach S` with bound `b` for some simulator `S`. -/
theorem ucEmulatesSys_iff_realizes_of_le (R : Sys τ (Event P AP) (Oh × Lk))
    (F : Sys φ (Event P AF) (Oh × LF))
    (b : (ζ : Type) → Env (Strat ζ (Event P AP) (Oh × Lk)) ζ → ℝ≥0∞)
    (hb : ∀ (ζ : Type) (Z : Env (Strat ζ (Event P AP) (Oh × Lk)) ζ),
      b ((AdvSys.dummy AP Lk).toEnvPullback.Ctx ζ) ((AdvSys.dummy AP Lk).toEnvPullback.pull Z) ≤
        b ζ Z) :
    UCEmulatesSys R F b ↔
      ∃ (σ : Type) (S : AdvSys σ AP AF LF Lk), Realizes R (F.attach S) b := by
  constructor
  · intro h
    obtain ⟨σ, S, hS⟩ := h.realizes_dummy
    exact ⟨σ, S, fun ζ => (hS ζ).mono (hb ζ)⟩
  · rintro ⟨_, S, hS⟩
    exact ucEmulatesSys_of_realizes S hS

/-- `ucEmulatesSys_iff_realizes` is the instance at a constant bound. -/
example (R : Sys τ (Event P AP) (Oh × Lk)) (F : Sys φ (Event P AF) (Oh × LF)) (ε : ℝ≥0∞) :
    UCEmulatesSys R F (fun _ _ => ε) ↔
      ∃ (σ : Type) (S : AdvSys σ AP AF LF Lk), Realizes R (F.attach S) (fun _ _ => ε) :=
  ucEmulatesSys_iff_realizes_of_le R F _ fun _ _ => le_rfl

end UCMonad.ConcurrentSys
