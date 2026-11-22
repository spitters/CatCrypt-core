/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.CompUCEquivalence

/-!
# Specialized simulators and the universal environment

This file proves a variant of Claim 14 of Canetti (ePrint 2000/067, revision 2020, §4.3.3) for
the single-shot systems of `CompUCEquivalence.lean`: emulation with specialized simulators,
where the simulator may depend on the environment, is equivalent to emulation over `ucCdist`
(`UCEmulatesCdist`), where one simulator serves every admissible distinguisher. It makes four
choices:

* the advice of an environment is a value of an arbitrary type `Z : Type`;
* the universal environment is an arrow on pairs of a code and a view; at `SPComp` the codes
  are the tests and a code is evaluated by application (`admUniversal`);
* the simulator ranges over all arrows `sim_if → T view`, with unbounded cost;
* the cost of an environment enters through the class `adm`; `SpecializedSimulatorSPComp.lean`
  takes query cost and tree size at a fixed bound.

An environment with advice is a type `Z` of advice values, an input map `inp : Z → hon` and an
arrow `E : Z × (out ⊕ view) → T Bool` on the post-adversary view, admissible as one arrow;
the simulator of `UCEmulatesSpecCdist` depends on `E` and `inp` and is uniform over
`z : Z`, which plays Canetti's external input. A standard distinguisher is the case `Z = Unit`.

The hypothesis of the equivalence is a universal environment (`UniversalEnv`): a type of codes
with an evaluation arrow `run`, admissible, whose sections cover every admissible
distinguisher. It is an argument of the theorem, and `admUniversal` is one for the `SPComp`
instance, whose admissibility is trivial. The distance must also decompose over honest inputs
(`UCDistCompPointwise`), which holds for the `SPComp` instance.

The proof follows Canetti's: the direction from `UCEmulatesCdist` restricts the global
simulator to each environment (the section `E (z, ·)` is admissible and constant inputs do not
increase the distance); the converse instantiates the hypothesis at the universal environment
with advice `(code, input)`, obtains its simulator, and transfers the bound to each admissible
distinguisher through its code.

## Main definitions

* `UCEmulatesSpecCdist ε π F` — emulation with specialized simulators
* `UniversalEnv Cov` — a code type with an evaluation arrow covering the tests of `Cov`
* `UCDistCompPointwise T` — the distance is the supremum of its constant-input components
* `admUniversal V` — the universal environment of the admissible tests of `SPComp`

## Main results

* `exists_sim_of_universal` — a simulator defeating the universal environment at every code
  and input defeats every covered test
* `ucEmulatesSpecCdist_iff` — the variant of Claim 14: with an admissible universal environment,
  `UCEmulatesSpecCdist ε π F ↔ UCEmulatesCdist ε π F`
* `ucEmulatesSpecCdist_iff_spcomp` — the equivalence at `SPComp` with trivial admissibility

## References

* Canetti, "Universally Composable Security: A New Paradigm for Cryptographic Protocols",
  ePrint 2000/067, revision 2020-02-11, §4.3.3, Claim 14
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SpecializedSimulator

open UCMonad
open CatCrypt.Crypto.CompUCEquivalence
open scoped ENNReal

/-- A universal environment for the class of tests `Cov`: a type of codes with an evaluation
arrow `run` whose section at some code is each test of `Cov`. -/
structure UniversalEnv {T : Type → Type} {view : Type} (Cov : (view → T Bool) → Prop) where
  /-- The codes of the tests. -/
  Code : Type
  /-- Evaluation of a code on a view. -/
  run : Code × view → T Bool
  /-- Every test of `Cov` is the section of `run` at some code. -/
  cover : ∀ D, Cov D → ∃ c, (fun b => run (c, b)) = D

variable {T : Type → Type} [UCMonadCompDist T]

/-- Canetti's specialized simulators (§4.3.3): for every admissible adversary `A` and every
admissible environment with advice (`Z`, `inp`, `E`) there is a simulator `S`, depending on the
environment but not on the advice `z`, that keeps the real and ideal views within `ε` for the
test `E (z, ·)` at the honest input `inp z`. -/
def UCEmulatesSpecCdist (ε : ℝ≥0∞) {hon out leak sim_if view : Type}
    (π : hon → T (out ⊕ leak)) (F : hon → T (out ⊕ sim_if)) : Prop :=
  ∀ A : leak → T view, adm A →
  ∀ (Z : Type) (inp : Z → hon) (E : Z × (out ⊕ view) → T Bool), adm E →
  ∃ S : sim_if → T view, ∀ z : Z,
    UCMonadCompDist.ucDistComp
      (fun _ : Unit => π (inp z) >>= UCMonadBase.ucMapSum pure A)
      (fun _ : Unit => F (inp z) >>= UCMonadBase.ucMapSum pure S) (fun b => E (z, b)) ≤ ε

/-- The per-distinguisher distance is the supremum over inputs of its constant-input
components. A mixin over `UCMonadCompDist`. -/
class UCDistCompPointwise (T : Type → Type) [UCMonadCompDist T] : Prop where
  /-- Decomposition of `ucDistComp` over the inputs. -/
  ucDistComp_eq_iSup {α β : Type} (f g : α → T β) (D : β → T Bool) :
    UCMonadCompDist.ucDistComp f g D =
      ⨆ a, UCMonadCompDist.ucDistComp (fun _ : Unit => f a) (fun _ : Unit => g a) D

/-- The `SPComp` distance decomposes over inputs. -/
instance : UCDistCompPointwise CatCrypt.Core.SPComp where
  ucDistComp_eq_iSup f g D := by
    simp [UCMonadCompDist.ucDistComp, spcomp_distComp]

/-- A variant of Claim 14, per adversary: a simulator that keeps the real and ideal views within
`ε` for the universal environment at every code and honest input does so for every test covered
by it. -/
theorem exists_sim_of_universal [UCDistCompPointwise T] {ε : ℝ≥0∞}
    {hon out leak sim_if view : Type}
    (π : hon → T (out ⊕ leak)) (F : hon → T (out ⊕ sim_if)) (A : leak → T view)
    {Cov : (out ⊕ view → T Bool) → Prop} (U : UniversalEnv Cov)
    (h : ∃ S : sim_if → T view, ∀ (c : U.Code) (a : hon),
      UCMonadCompDist.ucDistComp (fun _ : Unit => π a >>= UCMonadBase.ucMapSum pure A)
        (fun _ : Unit => F a >>= UCMonadBase.ucMapSum pure S) (fun b => U.run (c, b)) ≤ ε) :
    ∃ S : sim_if → T view, ∀ D, Cov D →
      UCMonadCompDist.ucDistComp (fun a => π a >>= UCMonadBase.ucMapSum pure A)
        (fun a => F a >>= UCMonadBase.ucMapSum pure S) D ≤ ε := by
  obtain ⟨S, hS⟩ := h
  refine ⟨S, fun D hD => ?_⟩
  obtain ⟨c, rfl⟩ := U.cover D hD
  rw [UCDistCompPointwise.ucDistComp_eq_iSup]
  exact iSup_le fun a => hS c a

/-- A variant of Claim 14 (Canetti 2020, §4.3.3): for an admissibility class with an admissible
universal environment, emulation with specialized simulators is equivalent to `UCEmulatesCdist`. -/
theorem ucEmulatesSpecCdist_iff [UCDistCompPointwise T] {ε : ℝ≥0∞}
    {hon out leak sim_if view : Type}
    (π : hon → T (out ⊕ leak)) (F : hon → T (out ⊕ sim_if))
    (U : UniversalEnv (T := T) (view := out ⊕ view) (fun D => adm D)) (hU : adm U.run) :
    UCEmulatesSpecCdist (view := view) ε π F ↔ UCEmulatesCdist (view := view) ε π F := by
  constructor
  · intro h A hA
    obtain ⟨S, hS⟩ := h A hA (U.Code × hon) Prod.snd (fun p => U.run (p.1.1, p.2))
      (adm_precomp (fun p : (U.Code × hon) × (out ⊕ view) => (p.1.1, p.2)) hU)
    obtain ⟨S', hS'⟩ := exists_sim_of_universal π F A U ⟨S, fun c a => hS (c, a)⟩
    exact ⟨S', iSup₂_le hS'⟩
  · intro h A hA Z inp E hE
    obtain ⟨S, hS⟩ := h A hA
    refine ⟨S, fun z => le_trans ?_ (le_trans
      (le_iSup₂ (f := fun D (_ : adm D) => UCMonadCompDist.ucDistComp
        (fun a => π a >>= UCMonadBase.ucMapSum pure A)
        (fun a => F a >>= UCMonadBase.ucMapSum pure S) D)
        (fun b => E (z, b)) (adm_precomp (fun b : out ⊕ view => (z, b)) hE)) hS)⟩
    have key := UCMonadCompDist.ucDistComp_bind_left (fun _ : Unit => pure (inp z))
      (fun a => π a >>= UCMonadBase.ucMapSum pure A)
      (fun a => F a >>= UCMonadBase.ucMapSum pure S) (fun b => E (z, b))
    simpa only [pure_bind] using key

/-- The universal environment of the admissible tests of `SPComp`: codes are the tests, evaluated
by application. Admissibility is trivial at this instance (`adm = fun _ => True`), so the codes
are all tests and the environment is admissible. -/
noncomputable def admUniversal (V : Type) :
    UniversalEnv (T := CatCrypt.Core.SPComp) (view := V) (fun D => adm D) where
  Code := V → CatCrypt.Core.SPComp Bool
  run p := p.1 p.2
  cover D _ := ⟨D, rfl⟩

/-- `ucEmulatesSpecCdist_iff` at `SPComp`, with the universal environment `admUniversal`.
Admissibility is trivial at this instance (`adm = fun _ => True`): the adversaries, environments
and distinguishers of both sides range over all arrows. -/
theorem ucEmulatesSpecCdist_iff_spcomp {ε : ℝ≥0∞} {hon out leak sim_if view : Type}
    (π : hon → CatCrypt.Core.SPComp (out ⊕ leak))
    (F : hon → CatCrypt.Core.SPComp (out ⊕ sim_if)) :
    UCEmulatesSpecCdist (view := view) ε π F ↔ UCEmulatesCdist (view := view) ε π F :=
  ucEmulatesSpecCdist_iff π F (admUniversal _) (by simp [adm])

end CatCrypt.Crypto.SpecializedSimulator
