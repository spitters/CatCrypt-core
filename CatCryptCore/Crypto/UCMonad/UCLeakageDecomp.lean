/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCMonad
public import CatCryptCore.Crypto.UCMonad.LeakageExceptT


@[expose] public section
set_option autoImplicit false

/-!
# UC decomposes as `∃ simulator, relational-Hoare over the `ExceptT` leakage branch`

This module machine-checks the decomposition

> `UC  ⟺  ∃ sim, <relational judgment relating `real` and `ideal ∘ sim`>`,

where the leakage/interface component lives **inside** the relational logic as the
`ExceptT` / `.except` branch (per `LeakageExceptT.leakEquiv`), while the
**simulator existential `∃ sim` is the UC-specific quantifier** —
orthogonal to the leakage-inside-vs-outside question. Leakage internalization
(claim of `LeakageExceptT`) settles *where the interface lives*; it does **not**
supply the `∃ sim`, which is what separates universal composability from a plain
relational Hoare judgment.

## The shape

A protocol / functionality with an observable interface is a leakage channel
`hon → T (out ⊕ i)`: on each honest input it returns a normal output (`.inl`) or
a value on the environment-observable interface (`.inr`). Composing with an
environment fragment `A : leak → T view` yields the post-environment object
`fun a => π a >>= ucMapSum pure A : hon → T (out ⊕ view)`, whose `.inr view`
component is exactly the internalized leakage — the `ExceptT view T out` exception
barrel under `leakEquiv T out view`.

`UCviaRel π F` (`∀ A, ∃ sim, real ≡ ideal∘sim` at the `ExceptT`-transported
relational judgment `RelLeakExact`) is the decomposed reading. The relational
judgment `RelLeakExact r i` compares `r` and `i` *after transporting both into
`ExceptT view T out`* via `leakEquiv`, so the leakage (`.inr`/`.except`) branch is
constrained by the same relation as the success (`.inl`) branch — this is the
exact/perfect specialization of the relational Hoare judgment `RelTriple`, transported through the leakage↔`ExceptT`
iso.

## What is proved

* `RelLeakExact` — relational judgment: real ≡ ideal after `leakEquiv` transport.
* `relLeakExact_iff_eq` — it is exactly pointwise Kleisli equality (`leakEquiv`
  is an `Equiv`, hence injective).
* `UCviaRel`, `UCviaRelAlg` — the decomposed forms; the second makes the
  simulator existential outermost (`∃ Sim, ∀ A`, the algebraic
  simulator-construction), the first per-environment (`∀ A, ∃ sim`).
* `UCviaRel_iff_ExactUCEmulates` — **the decomposition, in general** (no metric):
  the `∃sim`-relational reading is literally `UCMonad.ExactUCEmulates`.
* `UCviaRel_implies_UCEmulatesPerfect` — bridge to the metric `ucSdist` notion:
  exact ⇒ perfect (`ε = 0`), unconditional.
* `UCEmulatesPerfect_implies_UCviaRel` — the converse, **gated on the explicit
  separation hypothesis** `ucSdist f g = 0 → f = g`. This localizes the wall:
  `ucSdist` is only a *pseudo*metric (`UCMonadMetric` ships `ucSdist_self` but no
  separation), so `UCEmulatesPerfect ⇒ UCviaRel` is unprovable in general —
  distance `0` need not be equality.
* `UCviaRel_iff_UCEmulatesPerfect_of_sep` — combining the two: under separation,
  the perfect metric UC and the `∃sim`-relational reading coincide.
* `UCviaRelAlg_implies_UCviaRel` — the algebraic (`∃Sim ∀A`) simulator construction
  yields the semantic (`∀A ∃sim`) one; the `∃ sim` is the UC quantifier.
* `identityRel_implies_UCviaRel` — **orthogonality witness**: identity-simulator
  relational agreement (`real ≡ ideal` directly, `sim = A`) implies UC. The
  converse fails (see the closing remark): UC for Pedersen or dual OT needs a
  *non-trivial* equivocating/extracting simulator, so dropping `∃ sim` is a
  strictly stronger requirement — the `∃ sim` is essential and UC is not the plain
  relational judgment.
-/

namespace CatCrypt.Crypto.SecureCompilation.Ascent

open scoped ENNReal
open UCMonad

universe uT

variable {T : Type → Type}

/-! ## 1. The relational judgment over the `ExceptT` leakage branch

`RelLeakExact r i` relates two post-environment leakage channels
`hon → T (out ⊕ view)` by transporting both into `ExceptT view T out` (via
`leakEquiv`) and demanding they agree there. Because `leakEquiv` is a lawful
functor image of the pointwise leak↔exception iso, this constrains the `.inr`
(leakage / `.except`) branch by the same relation as the `.inl` (success) branch:
leakage is reasoned about *inside* the relational judgment. -/

/-- **Relational judgment, exact level.** The real object `r` and the ideal object
    `i` (each a leakage channel `hon → T (out ⊕ view)`) agree after both are
    transported into the `ExceptT view T out` reading of `LeakageExceptT.leakEquiv`.
    This is the exact/perfect specialization of a relational Hoare judgment
    (`RelTriple`) carried through the leakage↔`ExceptT` iso: the environment-visible
    `.inr`/`.except` component is constrained alongside the `.inl` success value. -/
def RelLeakExact [UCMonadBase T] {hon out view : Type}
    (r i : hon → T (out ⊕ view)) : Prop :=
  ∀ a, leakEquiv T out view (r a) = leakEquiv T out view (i a)

/-- The relational judgment is exactly pointwise Kleisli equality: `leakEquiv` is
    an `Equiv`, hence injective, so agreement in the `ExceptT` reading is agreement
    of the underlying leakage channels. -/
theorem relLeakExact_iff_eq [UCMonadBase T] {hon out view : Type}
    (r i : hon → T (out ⊕ view)) :
    RelLeakExact r i ↔ r = i := by
  constructor
  · intro h; funext a; exact (leakEquiv T out view).injective (h a)
  · rintro rfl a; rfl

/-! ## 2. The decomposed forms of UC -/

/-- **UC, decomposed (per-environment simulator).** For every environment fragment
    `A`, there **exists a simulator** `sim` translating the ideal interface so that
    the real object relates to the ideal-composed-with-`sim` object at the
    relational judgment `RelLeakExact`. The `∃ sim` is explicit; the leakage lives
    inside `RelLeakExact` (the `.except` branch). -/
def UCviaRel [UCMonadBase T] {hon out leak sim_if view : Type}
    (π : hon → T (out ⊕ leak))
    (F : hon → T (out ⊕ sim_if)) : Prop :=
  ∀ (A : leak → T view), ∃ (sim : sim_if → T view),
    RelLeakExact (view := view)
      (fun a => π a >>= UCMonadBase.ucMapSum pure A)
      (fun a => F a >>= UCMonadBase.ucMapSum pure sim)

/-- **UC, decomposed (algebraic: outermost simulator construction).** A single
    simulator construction `Sim : (leak → T view) → (sim_if → T view)` works for
    every environment. This is the `∃ Sim, ∀ A` shape — the UC quantifier
    `∃ Sim` sits *outside* the environment quantifier. -/
def UCviaRelAlg [UCMonadBase T] {hon out leak sim_if view : Type}
    (π : hon → T (out ⊕ leak))
    (F : hon → T (out ⊕ sim_if)) : Prop :=
  ∃ (Sim : SimConstruction T leak sim_if view),
    ∀ (A : leak → T view),
      RelLeakExact (view := view)
        (fun a => π a >>= UCMonadBase.ucMapSum pure A)
        (fun a => F a >>= UCMonadBase.ucMapSum pure (Sim A))

/-! ## 3. The decomposition equivalence (general, no metric) -/

/-- **The decomposition, in general.** The `∃sim`-over-relational-`ExceptT` reading
    of UC is *literally* the exact UC notion `UCMonad.ExactUCEmulates`: the
    relational judgment `RelLeakExact` unfolds (via `relLeakExact_iff_eq`) to the
    Kleisli equality that `ExactUCEmulates` demands. This is the content of
    "UC = ∃sim. relational-Hoare-over-`ExceptT`-leakage" at the exact level —
    no probabilistic coupling required. -/
theorem UCviaRel_iff_ExactUCEmulates [UCMonadBase T]
    {hon out leak sim_if view : Type}
    (π : hon → T (out ⊕ leak))
    (F : hon → T (out ⊕ sim_if)) :
    UCviaRel (view := view) π F ↔ ExactUCEmulates (T := T) (view := view) π F := by
  refine forall_congr' fun A => ?_
  exact exists_congr fun sim => relLeakExact_iff_eq _ _

/-! ## 4. Bridge to the metric (`ucSdist`) UC notion -/

/-- **Exact ⇒ perfect (`ε = 0`), unconditional.** The `∃sim`-relational reading
    implies the metric UC notion at bound `0`: equality of the post-environment
    objects forces `ucSdist ≤ 0`. -/
theorem UCviaRel_implies_UCEmulatesPerfect [UCMonadMetric T]
    {hon out leak sim_if view : Type}
    {π : hon → T (out ⊕ leak)}
    {F : hon → T (out ⊕ sim_if)}
    (h : UCviaRel (view := view) π F) :
    UCEmulatesPerfect (T := T) view π F :=
  UCEmulates_of_ExactUCEmulates
    ((UCviaRel_iff_ExactUCEmulates π F).mp h)

/-- **Perfect ⇒ exact, gated on separation.** The converse to
    `UCviaRel_implies_UCEmulatesPerfect` needs `ucSdist` to *separate points*
    (`ucSdist f g = 0 → f = g`), which `UCMonadMetric` does **not** provide —
    `ucSdist` is a pseudometric (only `ucSdist_self`). With the separation
    hypothesis supplied explicitly, the metric perfect notion collapses back to the
    relational reading. This isolates the precise obstacle: distance `0` need not be
    equality. -/
theorem UCEmulatesPerfect_implies_UCviaRel [UCMonadMetric T]
    {hon out leak sim_if view : Type}
    {π : hon → T (out ⊕ leak)}
    {F : hon → T (out ⊕ sim_if)}
    (hsep : ∀ {α β : Type} (f g : α → T β),
      UCMonadMetric.ucSdist f g = 0 → f = g)
    (h : UCEmulatesPerfect (T := T) view π F) :
    UCviaRel (view := view) π F := by
  rw [UCviaRel_iff_ExactUCEmulates]
  intro A
  obtain ⟨S, hS⟩ := h A
  refine ⟨S, hsep _ _ (le_antisymm hS bot_le)⟩

/-- **Perfect metric UC ⟺ `∃sim`-relational reading, under separation.**
    Combines the two bridge directions: when `ucSdist` separates points, the
    decomposition is an equivalence with the metric `ε = 0` UC notion. -/
theorem UCviaRel_iff_UCEmulatesPerfect_of_sep [UCMonadMetric T]
    {hon out leak sim_if view : Type}
    (π : hon → T (out ⊕ leak))
    (F : hon → T (out ⊕ sim_if))
    (hsep : ∀ {α β : Type} (f g : α → T β),
      UCMonadMetric.ucSdist f g = 0 → f = g) :
    UCviaRel (view := view) π F ↔ UCEmulatesPerfect (T := T) view π F :=
  ⟨UCviaRel_implies_UCEmulatesPerfect,
   UCEmulatesPerfect_implies_UCviaRel hsep⟩

/-! ## 5. The simulator existential is essential -/

/-- **Algebraic ⇒ semantic.** A single outermost simulator construction
    (`∃ Sim, ∀ A`) yields the per-environment existential (`∀ A, ∃ sim`): the `∃ sim`
    quantifier of UC is witnessed uniformly by `Sim`. This is the `∃∀ → ∀∃`
    direction; the converse would require choice *and* uniformity of the witness. -/
theorem UCviaRelAlg_implies_UCviaRel [UCMonadBase T]
    {hon out leak sim_if view : Type}
    {π : hon → T (out ⊕ leak)}
    {F : hon → T (out ⊕ sim_if)}
    (h : UCviaRelAlg (view := view) π F) :
    UCviaRel (view := view) π F := by
  obtain ⟨Sim, hSim⟩ := h
  exact fun A => ⟨Sim A, hSim A⟩

/-! ## 6. Orthogonality witness: `∃ sim` is essential

The following shows one side of the non-collapse. If the **identity** simulator
already relates real and ideal (same interface, `sim = A`), UC holds. The converse
— UC forcing identity agreement — is **false**: UC results
(`pedersen_uc_secure`, `dualOT_uc_secure`, `sigma_uc_zk_secure`) hold precisely via
a *non-trivial* equivocating / extracting / RO-programming simulator with `S ≠ A`,
where `real ≠ ideal` as leakage channels. Hence forcing `sim = id` is a strictly
stronger requirement than UC, and the `∃ sim` quantifier cannot be dropped: UC is
**not** the plain relational Hoare judgment `real ≡ ideal`. -/

/-- **Orthogonality (provable direction).** If the identity simulator makes the real
    and ideal objects relationally equal for every environment (same interface
    `leak = sim_if`, `sim := A`), then UC holds. The `∃ sim` is satisfied by the
    trivial witness. The converse fails on any protocol whose UC proof needs a
    non-trivial simulator (Pedersen, dual-OT), so this implication is strict — the
    non-collapse of UC and plain relational agreement. -/
theorem identityRel_implies_UCviaRel [UCMonadBase T]
    {hon out leak view : Type}
    {π F : hon → T (out ⊕ leak)}
    (h : ∀ A : leak → T view,
      (fun a => π a >>= UCMonadBase.ucMapSum pure A)
        = (fun a => F a >>= UCMonadBase.ucMapSum pure A)) :
    UCviaRel (view := view) π F :=
  fun A => ⟨A, (relLeakExact_iff_eq _ _).mpr (h A)⟩

end CatCrypt.Crypto.SecureCompilation.Ascent
