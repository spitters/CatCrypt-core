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
* `GuardRE`: the relation of the second postconditions for `guardProg`.
* `wpRel`, `wpRelP`: the concrete transformers of a step relation.
* `stepComp`: the relational composite of two step relations.
* `GuardedRRelPT`: the refinement of a guarded update by a concrete transformer.

## Main results

* `wp_eStateM_apply`, `wp_optProg_apply`, `wp_guardProg_iff`: the weakest
  preconditions of the abstract programs.
* `guardProg_rrelPT_iff`: `RRelPT` between `guardProg G f` and a monotone transformer
  is a triple from the entry states to the exit states.
* `rrelPT_optProg_wpRel_iff`, `rrelPT_optProg_wpRelP_iff`: `RRelPT` between `optProg f`
  and `wpRel T` (resp. `wpRelP T`), at the assertion map of a state relation `SR` and
  with the abstract exception postcondition fixed to false, is the forward simulation
  of `f` by `T` (resp. its partial form).
* `wpRel_comp`: `wpRel` of a composite step relation is the composite of the `wpRel`.
* `corresRel_iff_rrelPT`, `corresRelP_iff_rrelPT`, `corresFun_iff_rrelPT`: the total,
  partial and deterministic total forward simulations are `GuardedRRelPT`.
* `GuardedRRelPT.weaken`, `GuardedRRelPT.seq`, `guardedRRelPT_trans`: consequence,
  sequencing, and composition with a refinement at `AssnRel.ofRel R`.
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

/-- The relation of the second postconditions for `guardProg` against a transformer
    whose second argument is a postcondition `Ψ` of raised values: the abstract
    exception `none` has the false postcondition, and the abstract postcondition of
    `some r`, mapped by `ofStateRel SR`, entails `Ψ` at the encoding `encE r`. -/
def GuardRE {σ ε V : Type} (SR : σ → S ⊕ S → Prop) (encE : ε → V)
    (E : ExceptConds (.except (Option ε) (.arg (S ⊕ S) .pure)))
    (Ψ : V → Assertion (.arg σ .pure)) : Prop :=
  (∀ y, ¬ (E.1 none y).down) ∧
    ∀ r, (AssnRel.ofStateRel (ε := Option ε) SR).γ (E.1 (some r)) ⊢ₛ Ψ (encE r)

/-- **`RRelPT` from a guarded function, closed form.** For a transformer `wc` monotone
    in both postconditions, the refinement of `guardProg G f` by `wc` at the assertion
    map of `SR`, the value relation `Rv` and `GuardRE SR encE` holds exactly when, under
    the guard, every state related to `.inl a` satisfies `wc` at two postconditions:
    the state is related to `.inr a` and the value is `Rv`-related to `b` where
    `f a = .ok b`; the state is related to `.inr a` and the value is `encE r` where
    `f a = .error r`. -/
theorem guardProg_rrelPT_iff {σ ε α V : Type} {SR : σ → S ⊕ S → Prop} {G : S → Prop}
    {f : S → Except ε α} {Rv : α → V → Prop} {encE : ε → V}
    {wc : (V → Assertion (.arg σ .pure)) → (V → Assertion (.arg σ .pure)) →
      Assertion (.arg σ .pure)}
    (hmono : ∀ Φ₁ Ψ₁ Φ₂ Ψ₂ : V → Assertion (.arg σ .pure),
      (∀ v, Φ₁ v ⊢ₛ Φ₂ v) → (∀ v, Ψ₁ v ⊢ₛ Ψ₂ v) → wc Φ₁ Ψ₁ ⊢ₛ wc Φ₂ Ψ₂) :
    RRelPT (AssnRel.ofStateRel SR) (GuardRE SR encE) Rv
        (fun Φ E => wp⟦guardProg G f⟧ (Φ, E)) wc ↔
      ∀ a, G a → ∀ s, SR s (.inl a) →
        (wc (fun v s' => ⌜SR s' (.inr a) ∧ ∃ b, f a = .ok b ∧ Rv b v⌝)
          (fun v s' => ⌜SR s' (.inr a) ∧ ∃ r, f a = .error r ∧ v = encE r⌝) s).down := by
  constructor
  · intro h a hG s hs
    let E : ExceptConds (.except (Option ε) (.arg (S ⊕ S) .pure)) :=
      (fun o y => ⌜∃ r, o = some r ∧ f a = .error r ∧ y = .inr a⌝, ())
    have hnone : ∀ y, ¬ (E.1 none y).down := fun _ ⟨_, h, _⟩ => nomatch h
    exact @h (fun b y => ⌜f a = .ok b ∧ y = .inr a⌝)
      (fun v s' => ⌜SR s' (.inr a) ∧ ∃ b, f a = .ok b ∧ Rv b v⌝)
      (fun b v hv s' ⟨_, hx, h₁, h₂⟩ => by subst h₂; exact ⟨hx, b, h₁, hv⟩)
      E (fun v s' => ⌜SR s' (.inr a) ∧ ∃ r, f a = .error r ∧ v = encE r⌝)
      ⟨hnone, fun r s' ⟨_, hx, _, h₀, h₁, h₂⟩ => by
        cases h₀; subst h₂; exact ⟨hx, _, h₁, rfl⟩⟩ s
      ⟨.inl a, hs, (wp_guardProg_iff hnone).mpr ⟨a, rfl, hG, by
        cases hf : f a with
        | ok b => exact Or.inl ⟨b, rfl, rfl, rfl⟩
        | error r => exact Or.inr ⟨r, rfl, r, rfl, hf, rfl⟩⟩⟩
  · rintro h Φ Φ' hΦ E E' ⟨hnone, hE⟩ s ⟨x, hx, hwp⟩
    obtain ⟨a, rfl, hG, hp⟩ := (wp_guardProg_iff hnone).mp hwp
    refine hmono _ _ Φ' E' ?_ ?_ s (h a hG s hx)
    · rintro v s' ⟨hQ, b, hb, hR⟩
      rcases hp with ⟨b', hb', hp⟩ | ⟨r, hr, _⟩
      · rw [hb] at hb'
        cases hb'
        exact @hΦ b v hR s' ⟨.inr a, hQ, hp⟩
      · rw [hb] at hr
        cases hr
    · rintro v s' ⟨hQ, r, hr, rfl⟩
      rcases hp with ⟨b, hb, _⟩ | ⟨r', hr', hp⟩
      · rw [hr] at hb
        cases hb
      · rw [hr] at hr'
        cases hr'
        exact hE r s' ⟨.inr a, hQ, hp⟩

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

/-! ## Composite step relations -/

section Comp

variable {σ α : Type}

/-- The relational composite of a `Unit`-valued step relation `T₁` and a step relation
    `T₂`: a `T₁`-step followed by a `T₂`-step. -/
def stepComp (T₁ : σ → Unit → σ → Prop) (T₂ : σ → α → σ → Prop) : σ → α → σ → Prop :=
  fun s b s'' => ∃ s', T₁ s () s' ∧ T₂ s' b s''

/-- The weakest precondition of a composite step relation is the composite of the
    weakest preconditions. -/
theorem wpRel_comp (T₁ : σ → Unit → σ → Prop) (T₂ : σ → α → σ → Prop)
    (Φ : α → Assertion (.arg σ .pure)) :
    wpRel (stepComp T₁ T₂) Φ () = wpRel T₁ (fun _ => wpRel T₂ Φ ()) () := by
  funext s
  exact congrArg ULift.up (propext
    ⟨fun ⟨b, s'', ⟨s', h₁, h₂⟩, hΦ⟩ => ⟨(), s', h₁, b, s'', h₂, hΦ⟩,
     fun ⟨_, s', h₁, b, s'', h₂, hΦ⟩ => ⟨b, s'', ⟨s', h₁, h₂⟩, hΦ⟩⟩)

end Comp

/-! ## Refinement of a guarded update -/

section Guarded

variable {σ A : Type}

/-- The refinement of the guarded update by a concrete transformer `wc`: the abstract
    program `optProg` of the partial transformer that returns `()` in state `fa a` when
    `P a` holds and fails otherwise, refined by `wc` at the assertion map
    `AssnRel.ofStateRel SR`, with the abstract exception postcondition fixed to
    `ExceptConds.false` and the trivial relation on `Unit` values. -/
abbrev GuardedRRelPT {ε' : Type} (SR : σ → A → Prop) (P : A → Prop) (fa : A → A)
    (wc : (Unit → Assertion (.arg σ .pure)) → ε' → Assertion (.arg σ .pure)) : Prop :=
  RRelPT (AssnRel.ofStateRel (ε := PUnit) SR) (fun E (_ : ε') => E = ExceptConds.false)
    (fun (_ : Unit) (_ : Unit) => True)
    (fun Q E => wp⟦open Classical in
      optProg (fun a => if P a then some ((), fa a) else none)⟧ (Q, E)) wc

/-- **The total forward simulation is `GuardedRRelPT`.** From every `SR`-related state
    with `P` some `T`-successor is related to `fa a` exactly when the guarded update is
    refined by `wpRel T`; an instance of `rrelPT_optProg_wpRel_iff`. -/
theorem corresRel_iff_rrelPT (SR : σ → A → Prop) (P : A → Prop) (fa : A → A)
    (T : σ → σ → Prop) :
    (∀ s a, SR s a → P a → ∃ s', T s s' ∧ SR s' (fa a)) ↔
      GuardedRRelPT SR P fa (wpRel fun s (_ : Unit) s' => T s s') := by
  refine Iff.trans ⟨fun h s a p hs hf => ?_, fun h s a hs hP => ?_⟩ rrelPT_optProg_wpRel_iff.symm
  · split at hf
    · cases hf
      obtain ⟨s', hT, hs'⟩ := h s a hs ‹_›
      exact ⟨(), s', hT, trivial, hs'⟩
    · cases hf
  · obtain ⟨_, s', hT, -, hs'⟩ := h s a ((), fa a) hs (if_pos hP)
    exact ⟨s', hT, hs'⟩

/-- **The partial forward simulation is `GuardedRRelPT`.** From every `SR`-related
    state with `P` every `T`-successor is related to `fa a` exactly when the guarded
    update is refined by `wpRelP T`; an instance of `rrelPT_optProg_wpRelP_iff`. -/
theorem corresRelP_iff_rrelPT (SR : σ → A → Prop) (P : A → Prop) (fa : A → A)
    (T : σ → σ → Prop) :
    (∀ s a, SR s a → P a → ∀ s', T s s' → SR s' (fa a)) ↔
      GuardedRRelPT SR P fa (wpRelP fun s (_ : Unit) s' => T s s') := by
  refine Iff.trans ⟨fun h s a p hs hf v s' hT => ?_, fun h s a hs hP s' hT => ?_⟩
    rrelPT_optProg_wpRelP_iff.symm
  · split at hf
    · cases hf
      exact ⟨trivial, h s a hs ‹_› s' hT⟩
    · cases hf
  · exact (h s a ((), fa a) hs (if_pos hP) () s' hT).2

/-- **The deterministic total forward simulation is `GuardedRRelPT`**, at the step
    relation `s' = run s` of a total function `run`. -/
theorem corresFun_iff_rrelPT (SR : σ → A → Prop) (P : A → Prop) (fa : A → A)
    (run : σ → σ) :
    (∀ s a, SR s a → P a → SR (run s) (fa a)) ↔
      GuardedRRelPT SR P fa (wpRel fun s (_ : Unit) s' => s' = run s) :=
  Iff.trans ⟨fun h s a hs hP => ⟨run s, rfl, h s a hs hP⟩,
    fun h s a hs hP => by obtain ⟨_, rfl, h'⟩ := h s a hs hP; exact h'⟩
    (corresRel_iff_rrelPT SR P fa _)

/-- **Consequence.** `GuardedRRelPT` is contravariant in the guard: a refinement under
    `P` is a refinement under every `P'` that implies `P`. -/
theorem GuardedRRelPT.weaken {ε' : Type} {SR : σ → A → Prop} {P P' : A → Prop}
    {fa : A → A} {wc : (Unit → Assertion (.arg σ .pure)) → ε' → Assertion (.arg σ .pure)}
    (h : GuardedRRelPT SR P fa wc) (himp : ∀ a, P' a → P a) :
    GuardedRRelPT SR P' fa wc := by
  rintro Q Q' hQ E E' hE s ⟨a, hs, hwp⟩
  refine @h Q Q' hQ E E' hE s ⟨a, hs, ?_⟩
  subst hE
  beta_reduce at hwp ⊢
  rw [wp_optProg_apply] at hwp ⊢
  by_cases hP' : P' a
  · rw [if_pos hP'] at hwp
    rwa [if_pos (himp a hP')]
  · rw [if_neg hP'] at hwp
    exact hwp.elim

/-- **Sequencing.** Refinements of two guarded updates by `wpRel T₁` and `wpRel T₂`
    compose to a refinement of the composite update by `wpRel` of the composite step
    relation, when the first update establishes the second guard. -/
theorem GuardedRRelPT.seq {SR : σ → A → Prop} {P Q : A → Prop} {fa ga : A → A}
    {T₁ T₂ : σ → Unit → σ → Prop}
    (h₁ : GuardedRRelPT SR P fa (wpRel T₁)) (h₂ : GuardedRRelPT SR Q ga (wpRel T₂))
    (hpre : ∀ a, P a → Q (fa a)) :
    GuardedRRelPT SR P (fun a => ga (fa a)) (wpRel (stepComp T₁ T₂)) := by
  have e : ∀ T : σ → Unit → σ → Prop, (wpRel fun s (_ : Unit) s' => T s () s') = wpRel T :=
    fun _ => rfl
  rw [← e] at h₁ h₂ ⊢
  rw [← corresRel_iff_rrelPT] at h₁ h₂ ⊢
  intro s a hs hP
  obtain ⟨s₁, hT₁, hs₁⟩ := h₁ s a hs hP
  obtain ⟨s₂, hT₂, hs₂⟩ := h₂ s₁ (fa a) hs₁ (hpre a hP)
  exact ⟨s₂, ⟨s₁, hT₁, hT₂⟩, hs₂⟩

/-- **Composition by `RRelPT.trans`.** A refinement `GuardedRRelPT SR P fa wb` and a
    refinement of `wb` by `wc` at the assertion map `AssnRel.ofRel R` give the
    refinement by `wc` at the composite relation `fun s₂ a => ∃ s₁, R s₂ s₁ ∧ SR s₁ a`.
    The element `E₁` witnesses the composite relation of the second arguments. -/
theorem guardedRRelPT_trans {σ₂ ε₁ : Type} {SR : σ → A → Prop} {R : σ₂ → σ → Prop}
    {P : A → Prop} {fa : A → A}
    {wb : (Unit → Assertion (.arg σ .pure)) → ε₁ → Assertion (.arg σ .pure)}
    {wc : (Unit → Assertion (.arg σ₂ .pure)) → Unit → Assertion (.arg σ₂ .pure)}
    (E₁ : ε₁) (h₁ : GuardedRRelPT SR P fa wb)
    (h₂ : RRelPT (AssnRel.ofRel R) (fun (_ : ε₁) (_ : Unit) => True)
      (fun (_ : Unit) (_ : Unit) => True) wb wc) :
    GuardedRRelPT (fun s₂ a => ∃ s₁, R s₂ s₁ ∧ SR s₁ a) P fa wc := by
  have h := RRelPT.trans h₁ h₂
  intro Q Q' hQ E E' hE
  have hc := @h Q Q'
    (fun _ _ _ => by rw [AssnRel.Rel, AssnRel.ofRel_comp_ofStateRel_γ]; exact @hQ () () trivial)
    E E' ⟨E₁, hE, trivial⟩
  rw [AssnRel.Rel] at hc ⊢
  rwa [AssnRel.ofRel_comp_ofStateRel_γ] at hc

end Guarded

end CatCrypt.Refinement

end
