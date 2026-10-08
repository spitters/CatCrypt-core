/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Refinement.RRel

/-!
# Abstract programs and machine transformers for relational refinement

The judgments of the ascent are stated as `RRelPT` (`CatCryptCore/Refinement/RRel.lean`)
between the weakest precondition of an abstract `EStateM` program and a predicate
transformer of the concrete side. This module holds the abstract programs, the
concrete transformers of step relations, and their weakest-precondition lemmas.

* `optProg f : EStateM PUnit A B` runs a partial state transformer
  `f : A → Option (B × A)`: it returns `b` in state `a'` when `f a = some (b, a')` and
  raises `()` when `f a = none`.
* `guardProg G f : EStateM (Option ε) (S ⊕ S) α` runs a guarded function
  `f : S → Except ε α` over the tagged state space `S ⊕ S`, where `.inl σ` is the
  state before the run and `.inr σ` the state after it.
* `entryExitRel P Q` relates a state to `.inl σ` by `P` and to `.inr σ` by `Q`.
* `wpRel T` and `wpRelP T` are the weakest and the weakest liberal preconditions of a
  step relation `T : σ → α → σ → Prop` carrying a value.

## Main definitions

* `optProg`, `guardProg`: the abstract programs.
* `entryExitRel`: one relation to `S ⊕ S` from an entry and an exit relation to `S`.
* `wpRel`, `wpRelP`: the concrete transformers of a step relation.

## Main results

* `wp_eStateM_apply`, `wp_optProg_apply`, `wp_guardProg_iff`: the weakest
  preconditions of the abstract programs.
* `rrelPT_optProg_wpRel_iff`, `rrelPT_optProg_wpRelP_iff`: `RRelPT` between `optProg f`
  and `wpRel T` (resp. `wpRelP T`), at the assertion map of a state relation `SR` and
  with the abstract exception postcondition fixed to false, is the forward simulation
  of `f` by `T` (resp. its partial form).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Refinement

open Std.Do

/-! ## Weakest preconditions of `EStateM` programs -/

/-- The weakest precondition of an `EStateM` program is the postcondition of its
    result. -/
theorem wp_eStateM_apply {ε σ α : Type} (x : EStateM ε σ α)
    (Q : PostCond α (.except ε (.arg σ .pure))) (s : σ) :
    wp⟦x⟧ Q s = match x.run s with
      | .ok a s' => Q.1 a s'
      | .error e s' => Q.2.1 e s' := by
  cases h : x.run s <;> simp only [WP.wp, PredTrans.apply, h]

/-! ## The program of a partial state transformer -/

section OptProg

variable {A B : Type}

/-- The abstract program of a partial state transformer `f`: it returns `b` in state
    `a'` when `f a = some (b, a')` and raises `()` in state `a` when `f a = none`. -/
def optProg (f : A → Option (B × A)) : EStateM PUnit A B := fun a =>
  match f a with
  | some p => .ok p.1 p.2
  | none => .error () a

/-- The weakest precondition of `optProg f` is the postcondition at the result of `f`
    and the exception postcondition at a failure of `f`. -/
theorem wp_optProg_apply (f : A → Option (B × A))
    (Q : PostCond B (.except PUnit (.arg A .pure))) (a : A) :
    wp⟦optProg f⟧ Q a = match f a with
      | some p => Q.1 p.1 p.2
      | none => Q.2.1 () a := by
  rw [wp_eStateM_apply]
  cases h : f a <;> simp only [EStateM.run, optProg, h]

end OptProg

/-! ## The program of a guarded function over entry and exit states -/

section GuardProg

variable {S : Type}

/-- The relation of a state `s` to `S ⊕ S`: `.inl σ` by the entry relation `P` and
    `.inr σ` by the exit relation `Q`. -/
def entryExitRel {σ : Type} (P Q : σ → S → Prop) (s : σ) : S ⊕ S → Prop :=
  Sum.elim (P s) (Q s)

/-- The abstract program of a guarded function `f`: from `.inl σ` with `G σ` it returns
    `b` in `.inr σ` when `f σ = .ok b` and raises `some r` in `.inr σ` when
    `f σ = .error r`; otherwise it raises `none`. -/
noncomputable def guardProg {ε α : Type} (G : S → Prop) (f : S → Except ε α) :
    EStateM (Option ε) (S ⊕ S) α := fun x =>
  open Classical in
  match x with
  | .inl σ =>
    if G σ then
      (match f σ with
        | .ok b => .ok b (.inr σ)
        | .error r => .error (some r) (.inr σ))
    else .error none x
  | .inr _ => .error none x

/-- The weakest precondition of `guardProg G f`, when the exception `none` has the
    false postcondition: the start is `.inl σ` with `G σ`, and the result of `f σ`
    meets the normal postcondition at `.ok b` and the postcondition of `some r` at
    `.error r`. -/
theorem wp_guardProg_iff {ε α : Type} {G : S → Prop} {f : S → Except ε α}
    {Q : PostCond α (.except (Option ε) (.arg (S ⊕ S) .pure))} {x : S ⊕ S}
    (hnone : ∀ y, ¬ (Q.2.1 none y).down) :
    (wp⟦guardProg G f⟧ Q x).down ↔ ∃ σ, x = .inl σ ∧ G σ ∧
      ((∃ b, f σ = .ok b ∧ (Q.1 b (.inr σ)).down) ∨
        (∃ r, f σ = .error r ∧ (Q.2.1 (some r) (.inr σ)).down)) := by
  rw [wp_eStateM_apply]
  rcases x with σ | σ
  · by_cases hG : G σ
    · cases hf : f σ with
      | ok b =>
        simp only [EStateM.run, guardProg, if_pos hG, hf]
        refine ⟨fun h => ⟨σ, rfl, hG, Or.inl ⟨b, hf, h⟩⟩, fun ⟨_, h, _, hp⟩ => ?_⟩
        cases h
        rw [hf] at hp
        rcases hp with ⟨_, hb, hp⟩ | ⟨_, hr, _⟩
        · cases hb
          exact hp
        · cases hr
      | error r =>
        simp only [EStateM.run, guardProg, if_pos hG, hf]
        refine ⟨fun h => ⟨σ, rfl, hG, Or.inr ⟨r, hf, h⟩⟩, fun ⟨_, h, _, hp⟩ => ?_⟩
        cases h
        rw [hf] at hp
        rcases hp with ⟨_, hb, _⟩ | ⟨_, hr, hp⟩
        · cases hb
        · cases hr
          exact hp
    · simp only [EStateM.run, guardProg, if_neg hG]
      exact ⟨fun h => (hnone _ h).elim, fun ⟨_, h, hG', _⟩ => by cases h; exact (hG hG').elim⟩
  · simp only [EStateM.run, guardProg]
    exact ⟨fun h => (hnone _ h).elim, fun ⟨_, h, _⟩ => nomatch h⟩

end GuardProg

/-! ## The transformers of a step relation -/

section StepRel

variable {σ α : Type}

/-- The weakest precondition of a step relation `T`: a state `s` satisfies it when
    some `T`-successor `(b, s')` of `s` satisfies the postcondition at `b` and `s'`. -/
def wpRel (T : σ → α → σ → Prop) (Φ : α → Assertion (.arg σ .pure)) (_ : Unit) :
    Assertion (.arg σ .pure) :=
  fun s => ⌜∃ b s', T s b s' ∧ (Φ b s').down⌝

/-- The weakest liberal precondition of a step relation `T`: a state `s` satisfies it
    when every `T`-successor `(b, s')` of `s` satisfies the postcondition at `b` and
    `s'`. -/
def wpRelP (T : σ → α → σ → Prop) (Φ : α → Assertion (.arg σ .pure)) (_ : Unit) :
    Assertion (.arg σ .pure) :=
  fun s => ⌜∀ b s', T s b s' → (Φ b s').down⌝

end StepRel

/-! ## `optProg` refined by a step relation -/

section Sim

variable {σ A B α : Type}

/-- **`RRelPT` of `optProg` by `wpRel` is a forward simulation.** The refinement of
    `optProg f` by `wpRel T` at the assertion map of `SR`, with the abstract exception
    postcondition fixed to false and the value relation `Rv`, holds exactly when from
    every `SR`-related state at which `f` returns `(b, a')` some `T`-successor
    `(v, s')` has `Rv b v` and `SR s' a'`. -/
theorem rrelPT_optProg_wpRel_iff {SR : σ → A → Prop} {Rv : B → α → Prop}
    {f : A → Option (B × A)} {T : σ → α → σ → Prop} :
    RRelPT (AssnRel.ofStateRel (ε := PUnit) SR) (fun E (_ : Unit) => E = ExceptConds.false)
        Rv (fun Φ E => wp⟦optProg f⟧ (Φ, E)) (wpRel T) ↔
      ∀ s a p, SR s a → f a = some p → ∃ v s', T s v s' ∧ Rv p.1 v ∧ SR s' p.2 := by
  constructor
  · intro h s a p hs hf
    obtain ⟨v, s', hT, hR, hs'⟩ := @h (fun b a' => ⌜b = p.1 ∧ a' = p.2⌝)
      (fun v s' => ⌜Rv p.1 v ∧ SR s' p.2⌝)
      (fun b v hR s' ⟨_, hs', hb, ha⟩ => by subst hb ha; exact ⟨hR, hs'⟩)
      ExceptConds.false () rfl s
      ⟨a, hs, by beta_reduce; rw [wp_optProg_apply, hf]; exact ⟨rfl, rfl⟩⟩
    exact ⟨v, s', hT, hR, hs'⟩
  · rintro h Φ Φ' hΦ E _ rfl s ⟨a, hs, hwp⟩
    beta_reduce at hwp
    rw [wp_optProg_apply] at hwp
    cases hf : f a with
    | none =>
      rw [hf] at hwp
      exact hwp.elim
    | some p =>
      rw [hf] at hwp
      obtain ⟨v, s', hT, hR, hs'⟩ := h s a p hs hf
      exact ⟨v, s', hT, @hΦ p.1 v hR s' ⟨p.2, hs', hwp⟩⟩

/-- **`RRelPT` of `optProg` by `wpRelP` is a partial forward simulation.** The
    refinement of `optProg f` by `wpRelP T`, at the data of `rrelPT_optProg_wpRel_iff`,
    holds exactly when from every `SR`-related state at which `f` returns `(b, a')`
    every `T`-successor `(v, s')` has `Rv b v` and `SR s' a'`. -/
theorem rrelPT_optProg_wpRelP_iff {SR : σ → A → Prop} {Rv : B → α → Prop}
    {f : A → Option (B × A)} {T : σ → α → σ → Prop} :
    RRelPT (AssnRel.ofStateRel (ε := PUnit) SR) (fun E (_ : Unit) => E = ExceptConds.false)
        Rv (fun Φ E => wp⟦optProg f⟧ (Φ, E)) (wpRelP T) ↔
      ∀ s a p, SR s a → f a = some p → ∀ v s', T s v s' → Rv p.1 v ∧ SR s' p.2 := by
  constructor
  · intro h s a p hs hf
    exact @h (fun b a' => ⌜b = p.1 ∧ a' = p.2⌝)
      (fun v s' => ⌜Rv p.1 v ∧ SR s' p.2⌝)
      (fun b v hR s' ⟨_, hs', hb, ha⟩ => by subst hb ha; exact ⟨hR, hs'⟩)
      ExceptConds.false () rfl s
      ⟨a, hs, by beta_reduce; rw [wp_optProg_apply, hf]; exact ⟨rfl, rfl⟩⟩
  · rintro h Φ Φ' hΦ E _ rfl s ⟨a, hs, hwp⟩
    beta_reduce at hwp
    rw [wp_optProg_apply] at hwp
    cases hf : f a with
    | none =>
      rw [hf] at hwp
      exact hwp.elim
    | some p =>
      rw [hf] at hwp
      intro v s' hT
      obtain ⟨hR, hs'⟩ := h s a p hs hf v s' hT
      exact @hΦ p.1 v hR s' ⟨p.2, hs', hwp⟩

end Sim

end CatCrypt.Refinement

end
