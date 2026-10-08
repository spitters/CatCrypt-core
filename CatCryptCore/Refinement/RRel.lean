/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Std.Do
public import Mathlib.Logic.Relator
public import Mathlib.Data.List.Forall2

/-!
# Relational refinement of predicate transformers

`RRelPT γ RE R wa wc` relates two predicate transformers `wa` and `wc`, each taking
a postcondition on values and a second argument (an exception postcondition for a
`WP` instance, a control-flow postcondition for a deep embedding). It is the arrow
relation `((R ⇒ γ.Rel) ⇒ (RE ⇒ γ.Rel)) wa wc` of Mathlib's `Relator.LiftFun`, where
`γ.Rel P P'` is the entailment `γ P ⊢ₛ P'` along a map of assertions `γ`.

`RRel γ RE R c c'` is `RRelPT` at the weakest preconditions of `c : M α` and
`c' : N α'`, in possibly different monads and postcondition shapes. It is the
refinement weakest precondition `rwp` of S. Graf's `sgraf812/ascent`, at the top
element; `RRel.closed_form` states it with upstream's postcondition
`fun a' => ∃ a, ⌜R a a'⌝ ∧ γ (Q a)`.

## Main definitions

* `AssnRel ps ps'`: a monotone map of assertions that preserves existentials.
* `AssnRel.id`, `AssnRel.comp`, `AssnRel.purify`: the identity, composition, and
  the embedding of `.pure` assertions by `⌜·⌝`.
* `AssnRel.ofStateRel`, `AssnRel.ofRel`: the assertion maps of a relation between
  states and abstract states, and between two state spaces.
* `AssnRel.Rel γ P P'`: the entailment `γ P ⊢ₛ P'`.
* `RRelPT γ RE R wa wc`: the relational refinement of two predicate transformers.
* `RRel γ RE R c c'`: `RRelPT` at the two `wp` transformers.
* `ForInStepRel`: the constructor-wise lift of a value relation to `ForInStep`.

## Main results

* `RRelPT.transport`, `RRel.transport`: an entailment into `wa`, or a triple for
  `c`, transports to one into `wc`, or a triple for `c'`.
* `RRelPT.trans`, `RRel.trans`: composition along relational composition of value
  relations and of the second arguments, with the composite assertion map.
* `RRelPT.closed_form`, `RRel.closed_form`: the relation at the strongest related
  postcondition.
* `RRel.pure`, `RRel.bind`, `RRel.ite`, `RRel.forIn_list`, `RRel.map_left`,
  `RRel.map_right`: the rules for the monad operations.
-/

@[expose] public section

set_option autoImplicit false

universe u v w x y z u₁ u₂

namespace CatCrypt.Refinement

open Std.Do Relator

/-- A map of assertions from shape `ps` to shape `ps'` that is monotone for
    entailment and maps an existential over a `Type u` index into the existential
    of the images. -/
structure AssnRel (ps ps' : PostShape.{u}) where
  /-- The map of assertions. -/
  γ : Assertion ps → Assertion ps'
  /-- `γ` is monotone for entailment. -/
  mono : ∀ {P Q : Assertion ps}, (P ⊢ₛ Q) → γ P ⊢ₛ γ Q
  /-- `γ` maps an existential into the existential of the images. -/
  exists_le : ∀ {ι : Type u} (P : ι → Assertion ps),
    γ spred(∃ i, P i) ⊢ₛ spred(∃ i, γ (P i))

namespace AssnRel

/-- The identity map of assertions. -/
def id (ps : PostShape.{u}) : AssnRel ps ps where
  γ P := P
  mono h := h
  exists_le _ := .rfl

/-- The composite `γ₂ ∘ γ₁` of two assertion maps. -/
def comp {ps ps' ps'' : PostShape.{u}} (γ₂ : AssnRel ps' ps'') (γ₁ : AssnRel ps ps') :
    AssnRel ps ps'' where
  γ P := γ₂.γ (γ₁.γ P)
  mono h := γ₂.mono (γ₁.mono h)
  exists_le P := (γ₂.mono (γ₁.exists_le P)).trans (γ₂.exists_le _)

/-- The embedding of an assertion of shape `.pure` (a proposition) into shape `ps`
    as the pure assertion `⌜·⌝`. -/
def purify (ps : PostShape.{u}) : AssnRel .pure ps where
  γ P := ⌜P.down⌝
  mono h := SPred.pure_mono h
  exists_le _ := SPred.pure_elim' fun ⟨i, hi⟩ =>
    SPred.exists_intro' i (SPred.pure_intro hi)

/-- The relation of an assertion `P` of shape `ps` to an assertion `P'` of shape
    `ps'` along `γ`: the image `γ P` entails `P'`. -/
def Rel {ps ps' : PostShape.{u}} (γ : AssnRel ps ps') (P : Assertion ps)
    (P' : Assertion ps') : Prop :=
  γ.γ P ⊢ₛ P'

/-- The assertion map of a relation `SR` between states `σ` and abstract states `A`:
    an abstract assertion `Q` goes to `fun s => ⌜∃ a, SR s a ∧ Q a⌝`. The abstract
    shape carries one exception of type `ε`. -/
def ofStateRel {ε σ A : Type} (SR : σ → A → Prop) :
    AssnRel (.except ε (.arg A .pure)) (.arg σ .pure) where
  γ Q := fun s => ⌜∃ a, SR s a ∧ (Q a).down⌝
  mono h := fun _ ⟨a, hs, hq⟩ => ⟨a, hs, h a hq⟩
  exists_le _ := fun _ ⟨a, hs, ⟨i, hi⟩⟩ => ⟨i, a, hs, hi⟩

/-- The assertion map of a relation `R` between states `σ'` and states `σ`: an
    assertion `Q` on `σ` goes to `fun s' => ⌜∃ s, R s' s ∧ Q s⌝`. -/
def ofRel {σ σ' : Type} (R : σ' → σ → Prop) :
    AssnRel (.arg σ .pure) (.arg σ' .pure) where
  γ Q := fun s' => ⌜∃ s, R s' s ∧ (Q s).down⌝
  mono h := fun _ ⟨s, hs, hq⟩ => ⟨s, hs, h s hq⟩
  exists_le _ := fun _ ⟨s, hs, ⟨i, hi⟩⟩ => ⟨i, s, hs, hi⟩

/-- The composite of `ofRel R` after `ofStateRel SR` is `ofStateRel` of the
    relational composite of `R` and `SR`. -/
theorem ofRel_comp_ofStateRel_γ {ε σ σ' A : Type} (R : σ' → σ → Prop)
    (SR : σ → A → Prop) (Q : Assertion (.except ε (.arg A .pure))) :
    ((ofRel R).comp (ofStateRel (ε := ε) SR)).γ Q =
      (ofStateRel (ε := ε) (fun s' a => ∃ s, R s' s ∧ SR s a)).γ Q := by
  funext s'
  exact congrArg ULift.up (propext
    ⟨fun ⟨s, hR, a, hs, hq⟩ => ⟨a, ⟨s, hR, hs⟩, hq⟩,
     fun ⟨a, ⟨s, hR, hs⟩, hq⟩ => ⟨s, hR, a, hs, hq⟩⟩)

end AssnRel

/-- The relational refinement of two predicate transformers `wa` and `wc`: the arrow
    relation `((R ⇒ γ.Rel) ⇒ (RE ⇒ γ.Rel))`. For all postconditions `Q`, `Q'` with
    `γ (Q a) ⊢ₛ Q' a'` whenever `R a a'`, and all second arguments `E`, `E'` with
    `RE E E'`, the image under `γ` of `wa Q E` entails `wc Q' E'`. -/
def RRelPT {ps ps' : PostShape.{u}} {ε : Type x} {ε' : Type y} (γ : AssnRel ps ps')
    (RE : ε → ε' → Prop) {α : Type u₁} {α' : Type u₂} (R : α → α' → Prop)
    (wa : (α → Assertion ps) → ε → Assertion ps)
    (wc : (α' → Assertion ps') → ε' → Assertion ps') : Prop :=
  ((R ⇒ γ.Rel) ⇒ (RE ⇒ γ.Rel)) wa wc

/-- The relational refinement of the weakest preconditions of `c : M α` and
    `c' : N α'`: `RRelPT` at the two `wp` transformers. -/
abbrev RRel {M : Type u → Type v} {N : Type u → Type w} {ps ps' : PostShape.{u}}
    [WP M ps] [WP N ps'] (γ : AssnRel ps ps')
    (RE : ExceptConds ps → ExceptConds ps' → Prop)
    {α α' : Type u} (R : α → α' → Prop) (c : M α) (c' : N α') : Prop :=
  RRelPT γ RE R (fun Q E => wp⟦c⟧ (Q, E)) (fun Q' E' => wp⟦c'⟧ (Q', E'))

/-- The constructor-wise lift of a value relation to `ForInStep`: `yield` and `done`
    are related only to the same constructor, carrying the value relation. -/
def ForInStepRel {β : Type u₁} {β' : Type u₂} (Rβ : β → β' → Prop) :
    ForInStep β → ForInStep β' → Prop
  | .yield b, .yield b' => Rβ b b'
  | .done b,  .done b'  => Rβ b b'
  | _,        _         => False

/-! ## Transport, composition and closed form of `RRelPT` -/

section RRelPT

variable {ps ps' ps'' : PostShape.{u}} {ε : Type x} {ε' : Type y} {ε'' : Type z}
  {α α' α'' : Type u}

/-- An entailment `P ⊢ₛ wa Q E` transports along `RRelPT γ RE R wa wc` to the
    entailment `γ P ⊢ₛ wc Q' E'`, for postconditions related by `R` up to `γ` and
    second arguments related by `RE`. -/
theorem RRelPT.transport {γ : AssnRel ps ps'} {RE : ε → ε' → Prop} {R : α → α' → Prop}
    {wa : (α → Assertion ps) → ε → Assertion ps}
    {wc : (α' → Assertion ps') → ε' → Assertion ps'} (h : RRelPT γ RE R wa wc)
    {P : Assertion ps} {Q : α → Assertion ps} {E : ε} {Q' : α' → Assertion ps'} {E' : ε'}
    (hQ : (R ⇒ γ.Rel) Q Q') (hE : RE E E') (ht : P ⊢ₛ wa Q E) :
    γ.γ P ⊢ₛ wc Q' E' :=
  (γ.mono ht).trans (h hQ hE)

/-- `RRelPT` composes: from `RRelPT γ₁ RE₁ R₁ wa wb` and `RRelPT γ₂ RE₂ R₂ wb wc`
    follows `RRelPT (γ₂ ∘ γ₁) (RE₁ ; RE₂) (R₁ ; R₂) wa wc`, where `;` is relational
    composition through an intermediate value or second argument. The value
    relations are arbitrary relations. -/
theorem RRelPT.trans {γ₁ : AssnRel ps ps'} {γ₂ : AssnRel ps' ps''}
    {RE₁ : ε → ε' → Prop} {RE₂ : ε' → ε'' → Prop}
    {R₁ : α → α' → Prop} {R₂ : α' → α'' → Prop}
    {wa : (α → Assertion ps) → ε → Assertion ps}
    {wb : (α' → Assertion ps') → ε' → Assertion ps'}
    {wc : (α'' → Assertion ps'') → ε'' → Assertion ps''}
    (h₁ : RRelPT γ₁ RE₁ R₁ wa wb) (h₂ : RRelPT γ₂ RE₂ R₂ wb wc) :
    RRelPT (γ₂.comp γ₁) (fun E E'' => ∃ E', RE₁ E E' ∧ RE₂ E' E'')
      (fun a a'' => ∃ a', R₁ a a' ∧ R₂ a' a'') wa wc := by
  rintro Q Q'' hQ E E'' ⟨E', hE₁, hE₂⟩
  refine (γ₂.mono (@h₁ Q (fun b => spred(∃ p : {a // R₁ a b}, γ₁.γ (Q p.1)))
    (fun a b hab => SPred.exists_intro' ⟨a, hab⟩ .rfl) E E' hE₁)).trans
    (@h₂ _ Q'' (fun b a'' hb => ?_) E' E'' hE₂)
  exact (γ₂.exists_le _).trans (SPred.exists_elim fun p => @hQ p.1 a'' ⟨b, p.2, hb⟩)

/-- For a target transformer `wc` monotone in its postcondition, `RRelPT` holds
    exactly when it holds at the strongest postcondition related to `Q`, namely
    `fun a' => ∃ a, ⌜R a a'⌝ ∧ γ (Q a)`. -/
theorem RRelPT.closed_form {γ : AssnRel ps ps'} {RE : ε → ε' → Prop} {R : α → α' → Prop}
    {wa : (α → Assertion ps) → ε → Assertion ps}
    {wc : (α' → Assertion ps') → ε' → Assertion ps'}
    (hmono : ∀ (Q₁ Q₂ : α' → Assertion ps') (E' : ε'),
      (∀ a', Q₁ a' ⊢ₛ Q₂ a') → wc Q₁ E' ⊢ₛ wc Q₂ E') :
    RRelPT γ RE R wa wc ↔
      ∀ (Q : α → Assertion ps) (E : ε) (E' : ε'), RE E E' →
        γ.γ (wa Q E) ⊢ₛ wc (fun a' => spred(∃ a, ⌜R a a'⌝ ∧ γ.γ (Q a))) E' := by
  constructor
  · intro h Q E E' hE
    exact @h Q (fun a' => spred(∃ a, ⌜R a a'⌝ ∧ γ.γ (Q a)))
      (fun a _ hr => SPred.exists_intro' a (SPred.and_intro (SPred.pure_intro hr) .rfl)) E E' hE
  · intro h Q Q' hQ E E' hE
    exact (h Q E E' hE).trans (hmono _ _ E'
      fun a' => SPred.exists_elim fun a => SPred.pure_elim_l fun hr => hQ hr)

end RRelPT

/-! ## `RRel` -/

section RRel

variable {M : Type u → Type v} {N : Type u → Type w} {K : Type u → Type x}
  {ps ps' ps'' : PostShape.{u}} {α α' α'' β β' : Type u}

/-- A triple `⦃P⦄ c ⦃(Q, E)⦄` transports along `RRel γ RE R c c'` to the triple
    `⦃γ P⦄ c' ⦃(Q', E')⦄`, for postconditions related by `R` up to `γ` and
    exception postconditions related by `RE`. -/
theorem RRel.transport [WP M ps] [WP N ps'] {γ : AssnRel ps ps'}
    {RE : ExceptConds ps → ExceptConds ps' → Prop} {R : α → α' → Prop}
    {c : M α} {c' : N α'} (h : RRel γ RE R c c')
    {P : Assertion ps} {Q : α → Assertion ps} {E : ExceptConds ps}
    {Q' : α' → Assertion ps'} {E' : ExceptConds ps'}
    (hQ : (R ⇒ γ.Rel) Q Q') (hE : RE E E') (ht : ⦃P⦄ c ⦃(Q, E)⦄) : ⦃γ.γ P⦄ c' ⦃(Q', E')⦄ :=
  Triple.iff.mpr (RRelPT.transport h hQ hE (Triple.iff.mp ht))

/-- `RRel` composes along relational composition of value relations and of
    exception relations, with the composite assertion map (`RRelPT.trans`). -/
theorem RRel.trans [WP M ps] [WP N ps'] [WP K ps''] {γ₁ : AssnRel ps ps'}
    {γ₂ : AssnRel ps' ps''}
    {RE₁ : ExceptConds ps → ExceptConds ps' → Prop}
    {RE₂ : ExceptConds ps' → ExceptConds ps'' → Prop}
    {R₁ : α → α' → Prop} {R₂ : α' → α'' → Prop}
    {c : M α} {c' : N α'} {c'' : K α''}
    (h₁ : RRel γ₁ RE₁ R₁ c c') (h₂ : RRel γ₂ RE₂ R₂ c' c'') :
    RRel (γ₂.comp γ₁) (fun E E'' => ∃ E', RE₁ E E' ∧ RE₂ E' E'')
      (fun a a'' => ∃ a', R₁ a a' ∧ R₂ a' a'') c c'' :=
  RRelPT.trans h₁ h₂

/-- `RRel` holds exactly when it holds at the strongest postcondition of `c'`
    related to `Q`, namely `fun a' => ∃ a, ⌜R a a'⌝ ∧ γ (Q a)`. This is the
    refinement weakest precondition `rwp` of S. Graf's `sgraf812/ascent`, at the
    top element. -/
theorem RRel.closed_form [WP M ps] [WP N ps'] {γ : AssnRel ps ps'}
    {RE : ExceptConds ps → ExceptConds ps' → Prop} {R : α → α' → Prop}
    {c : M α} {c' : N α'} :
    RRel γ RE R c c' ↔
      ∀ (Q : α → Assertion ps) (E : ExceptConds ps) (E' : ExceptConds ps'),
        RE E E' → γ.γ (wp⟦c⟧ (Q, E)) ⊢ₛ
          wp⟦c'⟧ (fun a' => spred(∃ a, ⌜R a a'⌝ ∧ γ.γ (Q a)), E') :=
  RRelPT.closed_form fun _ _ E' hQ => (wp c').mono _ _ ⟨hQ, ExceptConds.entails.refl E'⟩

/-- Related values give `RRel`-related `pure` computations. -/
theorem RRel.pure [Monad M] [WPMonad M ps] [Monad N] [WPMonad N ps'] {γ : AssnRel ps ps'}
    (RE : ExceptConds ps → ExceptConds ps' → Prop) (R : α → α' → Prop)
    {a : α} {a' : α'} (h : R a a') :
    RRel (M := M) (N := N) γ RE R (Pure.pure a) (Pure.pure a') := by
  intro Q Q' hQ E E' _
  simp only [WPMonad.wp_pure, PredTrans.apply_Pure_pure]
  exact hQ h

/-- Related heads and pointwise related continuations give related sequential
    compositions. -/
theorem RRel.bind [Monad M] [WPMonad M ps] [Monad N] [WPMonad N ps'] {γ : AssnRel ps ps'}
    {RE : ExceptConds ps → ExceptConds ps' → Prop} {Rα : α → α' → Prop}
    {Rβ : β → β' → Prop}
    {c : M α} {c' : N α'} {f : α → M β} {f' : α' → N β'}
    (hc : RRel γ RE Rα c c') (hf : ∀ a a', Rα a a' → RRel γ RE Rβ (f a) (f' a')) :
    RRel γ RE Rβ (c >>= f) (c' >>= f') := by
  intro Q Q' hQ E E' hE
  simp only [WPMonad.wp_bind, PredTrans.apply_Bind_bind]
  exact @hc (fun a => wp⟦f a⟧ (Q, E)) (fun a' => wp⟦f' a'⟧ (Q', E'))
    (fun a a' h => hf a a' h hQ hE) E E' hE

/-- Conditionals with equivalent conditions and branchwise related arms are
    related. -/
theorem RRel.ite [WP M ps] [WP N ps'] {γ : AssnRel ps ps'}
    {RE : ExceptConds ps → ExceptConds ps' → Prop} {R : α → α' → Prop}
    {b b' : Prop} [Decidable b] [Decidable b'] (hb : b ↔ b')
    {t e : M α} {t' e' : N α'} (ht : RRel γ RE R t t') (he : RRel γ RE R e e') :
    RRel γ RE R (if b then t else e) (if b' then t' else e') := by
  by_cases h : b
  · rw [if_pos h, if_pos (hb.mp h)]; exact ht
  · rw [if_neg h, if_neg (mt hb.mpr h)]; exact he

/-- `forIn` over `List.Forall₂`-related lists, with a body that maps related
    elements and related accumulators to `ForInStepRel`-related steps. -/
theorem RRel.forIn_list [Monad M] [WPMonad M ps] [Monad N] [WPMonad N ps']
    {γ : AssnRel ps ps'} {RE : ExceptConds ps → ExceptConds ps' → Prop}
    {A : Type y} {A' : Type z} (RA : A → A' → Prop) (Rβ : β → β' → Prop)
    (body : A → β → M (ForInStep β)) (body' : A' → β' → N (ForInStep β'))
    (hbody : ∀ a a' b b', RA a a' → Rβ b b' →
      RRel γ RE (ForInStepRel Rβ) (body a b) (body' a' b'))
    {l : List A} {l' : List A'} (hl : List.Forall₂ RA l l')
    {init : β} {init' : β'} (hinit : Rβ init init') :
    RRel γ RE Rβ (forIn l init body) (forIn l' init' body') := by
  induction hl generalizing init init' with
  | nil => simpa only [List.forIn_nil] using RRel.pure (M := M) (N := N) (γ := γ) RE Rβ hinit
  | cons hx _ ih =>
    simp only [List.forIn_cons]
    refine RRel.bind (hbody _ _ _ _ hx hinit) (fun s s' hs => ?_)
    match s, s', hs with
    | .yield b, .yield b', hb => exact ih hb
    | .done b,  .done b',  hb => exact RRel.pure RE Rβ hb

/-- `RRel` is preserved by `Functor.map` on the target side, along a map of the
    value relation. -/
theorem RRel.map_right [WP M ps] [Monad N] [WPMonad N ps'] {γ : AssnRel ps ps'}
    {RE : ExceptConds ps → ExceptConds ps' → Prop} {R : α → α' → Prop}
    {S : α → β' → Prop} {c : M α} {c' : N α'} (h : RRel γ RE R c c') (f : α' → β')
    (hf : ∀ a a', R a a' → S a (f a')) : RRel γ RE S c (f <$> c') := by
  intro Q Q' hQ E E' hE
  rw [WPMonad.wp_map]
  exact @h Q (fun a' => Q' (f a')) (fun a a' hr => hQ (hf a a' hr)) E E' hE

/-- `RRel` is preserved by `Functor.map` on the source side, along a map of the
    value relation. -/
theorem RRel.map_left [Monad M] [WPMonad M ps] [WP N ps'] {γ : AssnRel ps ps'}
    {RE : ExceptConds ps → ExceptConds ps' → Prop} {R : α → α' → Prop}
    {S : β → α' → Prop} {c : M α} {c' : N α'} (h : RRel γ RE R c c') (g : α → β)
    (hg : ∀ a a', R a a' → S (g a) a') : RRel γ RE S (g <$> c) c' := by
  intro Q Q' hQ E E' hE
  rw [WPMonad.wp_map]
  exact @h (fun a => Q (g a)) Q' (fun a a' hr => hQ (hg a a' hr)) E E' hE

end RRel

end CatCrypt.Refinement

end
