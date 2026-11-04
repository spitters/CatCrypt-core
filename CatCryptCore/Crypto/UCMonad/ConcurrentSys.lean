/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCPullbackSemantics
public import CatCryptCore.Crypto.UCParallel

/-!
# Concurrent UC emulation with the adversary and the simulator as systems

A protocol is a reactive system `R : Sys τ (Event P AP) (Oh × Lk)`: its events are honest
inputs `P` and adversary events `AP`, and each activation returns an honest output `Oh` with a
leakage `Lk`. A functionality `F : Sys φ (Event P AF) (Oh × LF)` has its own adversary interface
(`AF`, `LF`). An adversary is an adversary system `A : AdvSys α AI AP Lk Lk'` of
`UCTransparentAdv`: a reactive system with state `α` between the adversary interface of the
environment (`AI`, `Lk'`) and that of the protocol. A simulator is an adversary system
`Sim : AdvSys σ AI AF LF Lk'` on the leakage interface of the functionality. The real world is
`R.attach A`, the ideal world `F.attach Sim`; both are systems on the interface
`Event P AI`/`Oh × Lk'` of the environment, and the environment is quantified by `Realizes`.

The forwarding adversary `AdvSys.dummy`, the composite `AdvSys.comp` and their views
(`AdvSys.view_attach_dummy`, `AdvSys.view_attach_comp`) are those of `UCPullbackSemantics`.

## Main definitions

* `UCEmulatesSysAgainst R F A bound`: some simulator `Sim` makes `R.attach A` realize
  `F.attach Sim` with `bound`.
* `UCEmulatesSys R F b`: emulation against every adversary system `A`, with the bound `b` at the
  environment that absorbs `A`.

## Main results

* `realizes_attach_dummy_iff`: attaching the forwarding adversary does not change realization.
* `ucEmulatesSys_of_realizes` (dummy-adversary theorem): a realization `Realizes R (F.attach S) b`
  gives emulation against every adversary `A`, with simulator `S.comp A` and the bound `b` at the
  environment that absorbs `A`.
* `ucEmulatesSysAgainst_dummy_iff`: emulation against the forwarding adversary is a realization
  `Realizes R (F.attach S) b` for some `S`.
* `ucEmulatesSys_iff_realizes`: with a constant bound `ε`, emulation against every adversary holds
  iff `R` realizes `F.attach S` with bound `ε` for some `S`.
-/

@[expose] public section

set_option autoImplicit false

namespace UCMonad.ConcurrentSys

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCTransparent
open scoped ENNReal

variable {α σ φ τ AI AM AP AF Lk LM LF Lk' P Oh : Type}

/-! ## Views -/

/-- Realization depends on the second system only through its views. -/
theorem realizes_of_view_eq_right {τ υ υ' E O : Type} {R : Sys τ E O} {I : Sys υ E O}
    {I' : Sys υ' E O} {b : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞}
    (hv : ∀ (ζ : Type) (Z : Strat ζ E O), view I Z = view I' Z) (h : Realizes R I b) :
    Realizes R I' b := by
  intro ζ
  have e : (view I : Strat ζ E O → SPComp ζ) = view I' := funext (hv ζ)
  rw [← e]
  exact h ζ

/-- Realization depends on the first system only through its views. -/
theorem realizes_of_view_eq_left {τ τ' υ E O : Type} {R : Sys τ E O} {R' : Sys τ' E O}
    {I : Sys υ E O} {b : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞}
    (hv : ∀ (ζ : Type) (Z : Strat ζ E O), view R Z = view R' Z) (h : Realizes R I b) :
    Realizes R' I b := by
  intro ζ
  have e : (view R : Strat ζ E O → SPComp ζ) = view R' := funext (hv ζ)
  rw [← e]
  exact h ζ

/-- Realization is unchanged by attaching the forwarding adversary to the first system. -/
theorem realizes_attach_dummy_iff {υ : Type} (R : Sys τ (Event P AP) (Oh × Lk))
    (I : Sys υ (Event P AP) (Oh × Lk))
    (b : (ζ : Type) → Env (Strat ζ (Event P AP) (Oh × Lk)) ζ → ℝ≥0∞) :
    Realizes (R.attach (AdvSys.dummy AP Lk)) I b ↔ Realizes R I b :=
  ⟨realizes_of_view_eq_left fun _ Z => AdvSys.view_attach_dummy R Z,
    realizes_of_view_eq_left fun _ Z => (AdvSys.view_attach_dummy R Z).symm⟩

/-! ## Emulation -/

/-- Emulation against the adversary system `A`: for some simulator `Sim` on the leakage
interface of `F`, the real world `R.attach A` realizes the ideal world `F.attach Sim` with
`bound`, against every environment. -/
def UCEmulatesSysAgainst (R : Sys τ (Event P AP) (Oh × Lk)) (F : Sys φ (Event P AF) (Oh × LF))
    (A : AdvSys α AI AP Lk Lk')
    (bound : (ζ : Type) → Env (Strat ζ (Event P AI) (Oh × Lk')) ζ → ℝ≥0∞) : Prop :=
  ∃ (σ : Type) (Sim : AdvSys σ AI AF LF Lk'), Realizes (R.attach A) (F.attach Sim) bound

/-- Concurrent UC emulation with the adversary and the simulator as reactive systems: for every
adversary system `A`, emulation against `A` with the bound `b` at the environment that runs `A`
itself (`Env.absorb`). -/
def UCEmulatesSys (R : Sys τ (Event P AP) (Oh × Lk)) (F : Sys φ (Event P AF) (Oh × LF))
    (b : (ζ : Type) → Env (Strat ζ (Event P AP) (Oh × Lk)) ζ → ℝ≥0∞) : Prop :=
  ∀ (α AI Lk' : Type) (A : AdvSys α AI AP Lk Lk'),
    UCEmulatesSysAgainst R F A (fun ζ Z => b (ζ × α) (Z.absorb A))

/-- **Dummy-adversary theorem.** If `R` realizes `F.attach S` with bound `b`, then for every
adversary `A` the real world `R.attach A` realizes `F.attach (S.comp A)` with `b` at the
environment that absorbs `A`. -/
theorem ucEmulatesSys_of_realizes {R : Sys τ (Event P AP) (Oh × Lk)}
    {F : Sys φ (Event P AF) (Oh × LF)}
    {b : (ζ : Type) → Env (Strat ζ (Event P AP) (Oh × Lk)) ζ → ℝ≥0∞}
    (S : AdvSys σ AP AF LF Lk) (h : Realizes R (F.attach S) b) : UCEmulatesSys R F b :=
  fun _ _ _ A => ⟨_, S.comp A,
    realizes_of_view_eq_right (fun _ Z => AdvSys.view_attach_comp F S A Z) (h.attach A)⟩

/-- Emulation against the forwarding adversary is a realization of `F.attach S` by `R` for
some simulator `S`. -/
theorem ucEmulatesSysAgainst_dummy_iff (R : Sys τ (Event P AP) (Oh × Lk))
    (F : Sys φ (Event P AF) (Oh × LF))
    (b : (ζ : Type) → Env (Strat ζ (Event P AP) (Oh × Lk)) ζ → ℝ≥0∞) :
    UCEmulatesSysAgainst R F (AdvSys.dummy AP Lk) b ↔
      ∃ (σ : Type) (S : AdvSys σ AP AF LF Lk), Realizes R (F.attach S) b := by
  unfold UCEmulatesSysAgainst
  simp only [realizes_attach_dummy_iff]

/-- Emulation against the forwarding adversary gives emulation against every adversary. -/
theorem ucEmulatesSys_of_dummy {R : Sys τ (Event P AP) (Oh × Lk)}
    {F : Sys φ (Event P AF) (Oh × LF)}
    {b : (ζ : Type) → Env (Strat ζ (Event P AP) (Oh × Lk)) ζ → ℝ≥0∞}
    (h : UCEmulatesSysAgainst R F (AdvSys.dummy AP Lk) b) : UCEmulatesSys R F b := by
  obtain ⟨_, S, hS⟩ := (ucEmulatesSysAgainst_dummy_iff R F b).1 h
  exact ucEmulatesSys_of_realizes S hS

/-- **Emulation through the dummy adversary.** With a constant bound `ε`, emulation against every
adversary holds iff `R` realizes `F.attach S` with bound `ε` for some simulator `S`. -/
theorem ucEmulatesSys_iff_realizes (R : Sys τ (Event P AP) (Oh × Lk))
    (F : Sys φ (Event P AF) (Oh × LF)) (ε : ℝ≥0∞) :
    UCEmulatesSys R F (fun _ _ => ε) ↔
      ∃ (σ : Type) (S : AdvSys σ AP AF LF Lk), Realizes R (F.attach S) (fun _ _ => ε) := by
  constructor
  · intro h
    exact (ucEmulatesSysAgainst_dummy_iff R F _).1 (h Unit AP Lk (AdvSys.dummy AP Lk))
  · rintro ⟨_, S, hS⟩
    exact ucEmulatesSys_of_realizes S hS

end UCMonad.ConcurrentSys
