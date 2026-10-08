/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Refinement.RRel

/-!
# Loop rules and strongest postconditions for `RRel`

Loop rules for the relational refinement `RRel` with a relational invariant on the
loop states, and strongest postconditions of an abstract predicate transformer with
the reduction of a refinement to a single check at the strongest postcondition.

The loop forms are those for which `Std.Do` has specifications: `forIn` over lists
and ranges (`Spec.forIn_list`, `Spec.forIn_range`), and `repeatM`, through which
`Lean.Loop.forIn` (the `repeat`/`while` loop of `do` notation) is defined, for
monads with `Lean.Order.MonadTail` (`Spec.repeatM`). The rule for `repeatM` asks for
a variant that decreases along related iterations; it is the relational form of
S. Graf's `refines_whileLoop` (`sgraf812/ascent`, `Ascent/Corres/Loop.lean`), with an
arbitrary assertion map, arbitrary pre- and postconditions, and a value relation on
the results. The strongest postcondition follows `Ascent/Corres/SP.lean` of the
same development, for transformers into `Std.Do` assertions.

## Main definitions

* `ForInStepLift Y D`: the lift of a relation `Y` on yielded states and a relation
  `D` on finished states to `ForInStep`.
* `sp wa P E`: the strongest postcondition of the transformer `wa` for the
  precondition `P` and second argument `E`, the pointwise meet of the
  postconditions `Q` with `P ⊢ₛ wa Q E`.
* `InfConjunctive wa`: `wa` preserves nonempty meets of postconditions.

## Main results

* `RRel.forIn_list_inv`, `RRel.forIn_range_inv`, `RRel.forIn_rco_inv`: `forIn`
  over lists of equal length and over ranges, with an invariant indexed by the
  iteration count.
* `RRel.repeatM`, `RRel.loop`: `repeatM` and `forIn` over `Lean.Loop`, with a
  relational invariant and a variant on pairs of related states.
* `sp_le`, `le_sp`, `le_wp_sp`: `sp wa P E` is below every valid postcondition,
  above every lower bound of them, and valid for `P` when `wa` is
  `InfConjunctive` and `P` entails `wa` at the true postcondition.
* `RRelPT.of_sp`, `RRelPT.iff_sp`, `RRel.of_sp`: a refinement follows from the
  check at the strongest postcondition of the abstract side, and for an
  `InfConjunctive` monotone abstract side is equivalent to it.
* `infConjunctive_wp_id`, `infConjunctive_wp_stateM`: the `wp` of `Id` and of
  `StateM σ` computations is `InfConjunctive`.
-/

@[expose] public section

set_option autoImplicit false

universe u v w x y z u₁ u₂

namespace CatCrypt.Refinement

open Std.Do Relator

/-- The lift of a relation `Y` on yielded states and a relation `D` on finished
    states to `ForInStep`: `yield` is related only to `yield` by `Y`, `done` only to
    `done` by `D`. -/
def ForInStepLift {β : Type u₁} {β' : Type u₂} (Y D : β → β' → Prop) :
    ForInStep β → ForInStep β' → Prop
  | .yield b, .yield b' => Y b b'
  | .done b,  .done b'  => D b b'
  | _,        _         => False

/-! ## Loop rules -/

section Loops

variable {M : Type u → Type v} {N : Type u → Type w} {ps ps' : PostShape.{u}}
  {α α' β β' : Type u}

/-- `forIn` over two lists of equal length, with an invariant `I i` on the states
    after `i` iterations. The body at position `i` maps `I i`-related states to
    steps that yield `I (i + 1)`-related states or finish with `S`-related states;
    `I` at the length of the lists implies `S`. -/
theorem RRel.forIn_list_inv [Monad M] [WPMonad M ps] [Monad N] [WPMonad N ps']
    {γ : AssnRel ps ps'} {RE : ExceptConds ps → ExceptConds ps' → Prop}
    {A : Type y} {A' : Type z} (I : Nat → β → β' → Prop) (S : β → β' → Prop)
    (body : A → β → M (ForInStep β)) (body' : A' → β' → N (ForInStep β'))
    {l : List A} {l' : List A'} (hlen : l.length = l'.length)
    (hbody : ∀ (i : Nat) (hi : i < l.length) (hi' : i < l'.length) b b', I i b b' →
      RRel γ RE (ForInStepLift (I (i + 1)) S) (body l[i] b) (body' l'[i] b'))
    (hS : ∀ b b', I l.length b b' → S b b')
    {init : β} {init' : β'} (hinit : I 0 init init') :
    RRel γ RE S (forIn l init body) (forIn l' init' body') := by
  induction l generalizing l' I init init' with
  | nil =>
    cases l' with
    | nil =>
      simpa only [List.forIn_nil] using
        RRel.pure (M := M) (N := N) (γ := γ) RE S (hS _ _ hinit)
    | cons _ _ => simp at hlen
  | cons a t ih =>
    cases l' with
    | nil => simp at hlen
    | cons a' t' =>
      simp only [List.forIn_cons]
      refine RRel.bind (hbody 0 (Nat.succ_pos _) (Nat.succ_pos _) _ _ hinit)
        (fun s s' hs => ?_)
      match s, s', hs with
      | .yield b, .yield b', hb =>
        exact ih (I := fun n => I (n + 1)) (Nat.succ_inj.mp hlen)
          (fun i hi hi' b b' h =>
            hbody (i + 1) (Nat.succ_lt_succ hi) (Nat.succ_lt_succ hi') b b' h)
          hS hb
      | .done b,  .done b',  hb => exact RRel.pure RE S hb

/-- `forIn` over a range `[start:stop:step]` (`Std.Legacy.Range`) iterated on both
    sides, with an invariant `I i` on the states after `i` iterations; the body at
    iteration `i` receives the index `start + step * i`. -/
theorem RRel.forIn_range_inv [Monad M] [WPMonad M ps] [Monad N] [WPMonad N ps']
    {γ : AssnRel ps ps'} {RE : ExceptConds ps → ExceptConds ps' → Prop}
    (I : Nat → β → β' → Prop) (S : β → β' → Prop) (r : Std.Legacy.Range)
    (body : Nat → β → M (ForInStep β)) (body' : Nat → β' → N (ForInStep β'))
    (hbody : ∀ i, i < r.size → ∀ b b', I i b b' →
      RRel γ RE (ForInStepLift (I (i + 1)) S) (body (r.start + r.step * i) b)
        (body' (r.start + r.step * i) b'))
    (hS : ∀ b b', I r.size b b' → S b b')
    {init : β} {init' : β'} (hinit : I 0 init init') :
    RRel γ RE S (forIn r init body) (forIn r init' body') := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.forIn_eq_forIn_range']
  refine RRel.forIn_list_inv I S body body' rfl (fun i hi _ b b' h => ?_)
    (by simpa only [List.length_range'] using hS) hinit
  rw [List.length_range'] at hi
  simpa only [List.getElem_range'] using hbody i hi b b' h

/-- `repeatM f a` and `repeatM f' a'` are related for `I`-related initial states
    when each step maps `I`-related states either to `I`-related states on which
    the variant `μ` decreases, or to `S`-related results. -/
theorem RRel.repeatM [Monad M] [Lean.Order.MonadTail M] [WPMonad M ps]
    [Monad N] [Lean.Order.MonadTail N] [WPMonad N ps'] {γ : AssnRel ps ps'}
    {RE : ExceptConds ps → ExceptConds ps' → Prop} [Nonempty β] [Nonempty β']
    (I : α → α' → Prop) (S : β → β' → Prop) (μ : α → α' → Nat)
    {f : α → M (α ⊕ β)} {f' : α' → N (α' ⊕ β')}
    (hf : ∀ a a', I a a' →
      RRel γ RE (Sum.LiftRel (fun x x' => I x x' ∧ μ x x' < μ a a') S) (f a) (f' a'))
    {a : α} {a' : α'} (h : I a a') :
    RRel γ RE S (_root_.repeatM f a) (_root_.repeatM f' a') := by
  suffices H : ∀ n a a', μ a a' = n → I a a' →
      RRel γ RE S (_root_.repeatM f a) (_root_.repeatM f' a') from H _ a a' rfl h
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro a a' hn h
    rw [repeatM_eq_of_monadTail, repeatM_eq_of_monadTail (f := f')]
    refine RRel.bind (hf a a' h) (fun s s' hs => ?_)
    cases hs with
    | inl hx => exact ih _ (hn ▸ hx.2) _ _ rfl hx.1
    | inr hy => exact RRel.pure RE S hy

/-- `forIn` over `Lean.Loop` (the `repeat` and `while` loops of `do` notation): for
    `I`-related initial states, a body that yields `I`-related states on which the
    variant `μ` decreases, or finishes with `S`-related states, gives `S`-related
    loops. -/
theorem RRel.loop [Monad M] [Lean.Order.MonadTail M] [WPMonad M ps]
    [Monad N] [Lean.Order.MonadTail N] [WPMonad N ps'] {γ : AssnRel ps ps'}
    {RE : ExceptConds ps → ExceptConds ps' → Prop} [Nonempty β] [Nonempty β']
    (I : β → β' → Prop) (S : β → β' → Prop) (μ : β → β' → Nat)
    {f : Unit → β → M (ForInStep β)} {f' : Unit → β' → N (ForInStep β')}
    (hf : ∀ b b', I b b' →
      RRel γ RE (ForInStepLift (fun x x' => I x x' ∧ μ x x' < μ b b') S) (f () b)
        (f' () b'))
    {init : β} {init' : β'} (h : I init init') :
    RRel γ RE S (forIn Lean.Loop.mk init f) (forIn Lean.Loop.mk init' f') := by
  refine RRel.repeatM I S μ
    (fun b b' hb => RRel.bind (hf b b' hb) (fun s s' hs => ?_)) h
  match s, s', hs with
  | .yield x, .yield x', hx => exact RRel.pure RE _ (Sum.LiftRel.inl hx)
  | .done x, .done x', hx => exact RRel.pure RE _ (Sum.LiftRel.inr hx)

end Loops

/-- `forIn` over a half-open range `a...b` (`Std.Rco Nat`) iterated on both sides,
    with an invariant `I i` on the states after `i` iterations; the body at
    iteration `i` receives the `i`-th element of the range. The range's `ForIn`
    instance places the states in `Type`. -/
theorem RRel.forIn_rco_inv {M N : Type → Type} {ps ps' : PostShape.{0}}
    [Monad M] [WPMonad M ps] [Monad N] [WPMonad N ps'] {β β' : Type}
    {γ : AssnRel ps ps'} {RE : ExceptConds ps → ExceptConds ps' → Prop}
    (I : Nat → β → β' → Prop) (S : β → β' → Prop) (r : Std.Rco Nat)
    (body : Nat → β → M (ForInStep β)) (body' : Nat → β' → N (ForInStep β'))
    (hbody : ∀ (i : Nat) (hi : i < r.toList.length) b b', I i b b' →
      RRel γ RE (ForInStepLift (I (i + 1)) S) (body r.toList[i] b) (body' r.toList[i] b'))
    (hS : ∀ b b', I r.toList.length b b' → S b b')
    {init : β} {init' : β'} (hinit : I 0 init init') :
    RRel γ RE S (forIn r init body) (forIn r init' body') := by
  simp only [forIn, Std.Rco.forIn'_eq_forIn'_toList]
  exact RRel.forIn_list_inv I S body body' rfl (fun i hi _ => hbody i hi) hS hinit

/-! ## Strongest postconditions -/

section SP

variable {ps ps' : PostShape.{u}} {ε : Type x} {ε' : Type y} {α α' : Type u₁}

/-- The strongest postcondition of the transformer `wa` for the precondition `P`
    and second argument `E`: at each value, the meet of all postconditions `Q`
    with `P ⊢ₛ wa Q E`. -/
def sp (wa : (α → Assertion ps) → ε → Assertion ps) (P : Assertion ps) (E : ε) :
    α → Assertion ps :=
  fun a => SPred.forall fun Q : {Q : α → Assertion ps // P ⊢ₛ wa Q E} => Q.1 a

/-- The transformer `wa` preserves nonempty meets of postconditions: the meet of
    the images entails the image of the pointwise meet. -/
def InfConjunctive (wa : (α → Assertion ps) → ε → Assertion ps) : Prop :=
  ∀ {ι : Type (max u₁ u)} [Nonempty ι] (Q : ι → α → Assertion ps) (E : ε),
    spred(∀ i, wa (Q i) E) ⊢ₛ wa (fun a => spred(∀ i, Q i a)) E

/-- The strongest postcondition is below every postcondition valid for `P`. -/
theorem sp_le {wa : (α → Assertion ps) → ε → Assertion ps} {P : Assertion ps} {E : ε}
    {Q : α → Assertion ps} (h : P ⊢ₛ wa Q E) (a : α) : sp wa P E a ⊢ₛ Q a :=
  SPred.forall_elim (Ψ := fun Q : {Q : α → Assertion ps // P ⊢ₛ wa Q E} => Q.1 a) ⟨Q, h⟩

/-- A postcondition below every postcondition valid for `P` is below the strongest
    postcondition. -/
theorem le_sp {wa : (α → Assertion ps) → ε → Assertion ps} {P : Assertion ps} {E : ε}
    {R : α → Assertion ps} (h : ∀ Q, (P ⊢ₛ wa Q E) → ∀ a, R a ⊢ₛ Q a) (a : α) :
    R a ⊢ₛ sp wa P E a :=
  SPred.forall_intro (Ψ := fun Q : {Q : α → Assertion ps // P ⊢ₛ wa Q E} => Q.1 a)
    fun Q => h Q.1 Q.2 a

/-- For an `InfConjunctive` transformer and a precondition that entails `wa` at the
    true postcondition, the strongest postcondition is valid for `P`. -/
theorem le_wp_sp {wa : (α → Assertion ps) → ε → Assertion ps} (hc : InfConjunctive wa)
    {P : Assertion ps} {E : ε} (hdef : P ⊢ₛ wa (fun _ => ⌜True⌝) E) :
    P ⊢ₛ wa (sp wa P E) E :=
  haveI : Nonempty {Q : α → Assertion ps // P ⊢ₛ wa Q E} := ⟨⟨_, hdef⟩⟩
  (SPred.forall_intro (Ψ := fun Q : {Q : α → Assertion ps // P ⊢ₛ wa Q E} => wa Q.1 E)
    fun Q => Q.2).trans (hc (fun Q : {Q : α → Assertion ps // P ⊢ₛ wa Q E} => Q.1) E)

/-- For a monotone target transformer `wc`, `RRelPT` follows from the check at the
    strongest postcondition of the abstract side: for every precondition `P`, the
    image `γ P` entails `wc` at the postcondition related by `R` to `sp wa P E`. -/
theorem RRelPT.of_sp {γ : AssnRel ps ps'} {RE : ε → ε' → Prop} {R : α → α' → Prop}
    {wa : (α → Assertion ps) → ε → Assertion ps}
    {wc : (α' → Assertion ps') → ε' → Assertion ps'}
    (hmono : ∀ (Q₁ Q₂ : α' → Assertion ps') (E' : ε'),
      (∀ a', Q₁ a' ⊢ₛ Q₂ a') → wc Q₁ E' ⊢ₛ wc Q₂ E')
    (hsp : ∀ (P : Assertion ps) (E : ε) (E' : ε'), RE E E' →
      γ.γ P ⊢ₛ wc (fun a' => spred(∃ a, ⌜R a a'⌝ ∧ γ.γ (sp wa P E a))) E') :
    RRelPT γ RE R wa wc := by
  intro Q Q' hQ E E' hE
  exact (hsp _ E E' hE).trans (hmono _ _ E' fun a' => SPred.exists_elim fun a =>
    SPred.pure_elim_l fun hr => (γ.mono (sp_le .rfl a)).trans (hQ hr))

/-- For an `InfConjunctive` monotone abstract transformer and a monotone target
    transformer, `RRelPT` is equivalent to the check at the strongest postcondition
    for every precondition that entails `wa` at the true postcondition. -/
theorem RRelPT.iff_sp {γ : AssnRel ps ps'} {RE : ε → ε' → Prop} {R : α → α' → Prop}
    {wa : (α → Assertion ps) → ε → Assertion ps}
    {wc : (α' → Assertion ps') → ε' → Assertion ps'} (hc : InfConjunctive wa)
    (hmonoa : ∀ (Q₁ Q₂ : α → Assertion ps) (E : ε),
      (∀ a, Q₁ a ⊢ₛ Q₂ a) → wa Q₁ E ⊢ₛ wa Q₂ E)
    (hmono : ∀ (Q₁ Q₂ : α' → Assertion ps') (E' : ε'),
      (∀ a', Q₁ a' ⊢ₛ Q₂ a') → wc Q₁ E' ⊢ₛ wc Q₂ E') :
    RRelPT γ RE R wa wc ↔ ∀ (P : Assertion ps) (E : ε) (E' : ε'), RE E E' →
      (P ⊢ₛ wa (fun _ => ⌜True⌝) E) →
      γ.γ P ⊢ₛ wc (fun a' => spred(∃ a, ⌜R a a'⌝ ∧ γ.γ (sp wa P E a))) E' := by
  constructor
  · intro h P E E' hE hdef
    exact (γ.mono (le_wp_sp hc hdef)).trans (@h _ _
      (fun a _ hr => SPred.exists_intro' a (SPred.and_intro (SPred.pure_intro hr) .rfl))
      E E' hE)
  · intro hsp Q Q' hQ E E' hE
    refine (hsp _ E E' hE (hmonoa _ _ E fun _ => SPred.pure_intro trivial)).trans
      (hmono _ _ E' fun a' => SPred.exists_elim fun a =>
        SPred.pure_elim_l fun hr => (γ.mono (sp_le .rfl a)).trans (hQ hr))

end SP

/-- `RRel` follows from the check at the strongest postcondition of the `wp` of the
    abstract computation (`RRelPT.of_sp`). -/
theorem RRel.of_sp {M : Type u → Type v} {N : Type u → Type w} {ps ps' : PostShape.{u}}
    {α α' : Type u} [WP M ps] [WP N ps'] {γ : AssnRel ps ps'}
    {RE : ExceptConds ps → ExceptConds ps' → Prop} {R : α → α' → Prop}
    {c : M α} {c' : N α'}
    (hsp : ∀ (P : Assertion ps) (E : ExceptConds ps) (E' : ExceptConds ps'), RE E E' →
      γ.γ P ⊢ₛ wp⟦c'⟧ (fun a' => spred(∃ a, ⌜R a a'⌝ ∧
        γ.γ (sp (fun Q E => wp⟦c⟧ (Q, E)) P E a)), E')) :
    RRel γ RE R c c' :=
  RRelPT.of_sp (fun _ _ E' hQ => (wp c').mono _ _ ⟨hQ, ExceptConds.entails.refl E'⟩) hsp

/-- The `wp` of an `Id` computation preserves nonempty meets. -/
theorem infConjunctive_wp_id {α : Type u} (x : Id α) :
    InfConjunctive (ps := .pure) (ε := ExceptConds .pure)
      (fun (Q : α → Assertion .pure) E => wp⟦x⟧ (Q, E)) := by
  intro ι _ Q E
  exact .rfl

/-- The `wp` of a `StateM σ` computation preserves nonempty meets. -/
theorem infConjunctive_wp_stateM {σ α : Type u} (x : StateM σ α) :
    InfConjunctive (ps := .arg σ .pure) (ε := ExceptConds (.arg σ .pure))
      (fun (Q : α → Assertion (.arg σ .pure)) E => wp⟦x⟧ (Q, E)) := by
  intro ι _ Q E
  exact .rfl

end CatCrypt.Refinement

end
