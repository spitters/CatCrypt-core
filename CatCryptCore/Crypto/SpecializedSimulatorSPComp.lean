/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.SpecializedSimulator
public import CatCryptCore.Crypto.MonadCostModel
public import CatCryptCore.Crypto.SizeBoundedUC

/-!
# A variant of Claim 14 for the graded classes of `SPComp`

This file proves a variant of Canetti's Claim 14 (ePrint 2000/067, revision 2020, §4.3.3)
for `SPComp`, with four choices:

* the advice of an environment is a value of an arbitrary type `Z : Type`;
* the universal environment has the tests of the class as codes and evaluates a code by
  application;
* the simulator ranges over all arrows `sim_if → SPComp view`, with unbounded cost;
* the cost of an environment is its query cost or its tree size, at a fixed bound `n`.

The last choice gives two graded classes of tests:

* query cost at most `n` (`costBounded n`, with the `MonadCostModel SPComp` instance whose
  cost is `spTreeQueryCost`);
* syntax-tree size at most `n`: arrows compiled from an `SPTree` family of finite branching
  with every tree of size at most `n` (`SizeBounded n`).

For each class and each adversary, emulation with specialized simulators against environments
of the class is equivalent to emulation by one simulator against all tests of the class, at the
same bound `n`. The proof instantiates `exists_sim_of_universal` at the universal environment
whose codes are the tests of the class, evaluated by application; choosing a tree family per
code shows that the universal environment lies in the class at the same bound, since
evaluating a code adds no query and no node.

## Main definitions

* `SizeBounded n f` — `f` is compiled from a finite-branching `SPTree` family of size at most
  `n` at every input

## Main results

* `exists_sim_iff_of_universal` — the variant of Claim 14 per adversary for a class closed
  under pure precomposition that contains a universal environment covering it
* `exists_sim_iff_costBounded` — the variant at query cost `n`
* `exists_sim_iff_sizeBounded` — the variant at size `n`

## References

* Canetti, "Universally Composable Security: A New Paradigm for Cryptographic Protocols",
  ePrint 2000/067, revision 2020-02-11, §4.3.3, Claim 14
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SpecializedSimulator

open UCMonad
open CatCrypt.Core
open scoped ENNReal

section Generic

variable {T : Type → Type} [UCMonadCompDist T]

/-- A variant of Claim 14, per adversary, for a class `P` of tests closed under pure
precomposition, with a universal environment in `P` covering `P`: a simulator for each
environment of `P` (uniform over its advice) exists iff one simulator serves every test of `P`. -/
theorem exists_sim_iff_of_universal [UCDistCompPointwise T] {ε : ℝ≥0∞}
    {hon out leak sim_if view : Type}
    (P : {γ : Type} → (γ → T Bool) → Prop)
    (hP : ∀ {γ γ' : Type} (f : γ' → γ) {g : γ → T Bool}, P g → P (g ∘ f))
    (π : hon → T (out ⊕ leak)) (F : hon → T (out ⊕ sim_if)) (A : leak → T view)
    (U : UniversalEnv (T := T) (view := out ⊕ view) (fun D => P D)) (hU : P U.run) :
    (∀ (Z : Type) (inp : Z → hon) (E : Z × (out ⊕ view) → T Bool), P E →
      ∃ S : sim_if → T view, ∀ z : Z,
        UCMonadCompDist.ucDistComp
          (fun _ : Unit => π (inp z) >>= UCMonadBase.ucMapSum pure A)
          (fun _ : Unit => F (inp z) >>= UCMonadBase.ucMapSum pure S) (fun b => E (z, b)) ≤ ε)
    ↔ ∃ S : sim_if → T view, ∀ D : out ⊕ view → T Bool, P D →
      UCMonadCompDist.ucDistComp (fun a => π a >>= UCMonadBase.ucMapSum pure A)
        (fun a => F a >>= UCMonadBase.ucMapSum pure S) D ≤ ε := by
  constructor
  · intro h
    obtain ⟨S, hS⟩ := h (U.Code × hon) Prod.snd (fun p => U.run (p.1.1, p.2))
      (hP (fun p : (U.Code × hon) × (out ⊕ view) => (p.1.1, p.2)) hU)
    exact exists_sim_of_universal π F A U ⟨S, fun c a => hS (c, a)⟩
  · intro h Z inp E hE
    obtain ⟨S, hS⟩ := h
    refine ⟨S, fun z => le_trans ?_ (hS (fun b => E (z, b))
      (hP (fun b : out ⊕ view => (z, b)) hE))⟩
    have key := UCMonadCompDist.ucDistComp_bind_left (fun _ : Unit => pure (inp z))
      (fun a => π a >>= UCMonadBase.ucMapSum pure A)
      (fun a => F a >>= UCMonadBase.ucMapSum pure S) (fun b => E (z, b))
    simpa only [pure_bind] using key

end Generic

/-! ## Query cost at bound `n` -/

/-- The universal environment of the tests of query cost at most `n`: codes are the tests,
evaluated by application. -/
noncomputable def costBoundedUniversal (n : ℕ) (V : Type) :
    UniversalEnv (T := SPComp) (view := V) (fun D => costBounded n D) where
  Code := {D : V → SPComp Bool // costBounded n D}
  run p := p.1.1 p.2
  cover D hD := ⟨⟨D, hD⟩, rfl⟩

/-- The universal environment of query cost `n` has query cost at most `n`. -/
theorem costBounded_costBoundedUniversal_run (n : ℕ) (V : Type) :
    costBounded n (costBoundedUniversal n V).run := by
  have h : ∀ c : (costBoundedUniversal n V).Code, ∃ s : V → SPTree Bool,
      (∀ a, (s a).compile = c.1 a) ∧ (∀ a, (s a).QueryBdd) ∧ ∀ a, (s a).queryCost ≤ n :=
    fun c => (spTreeQueryCost_le_iff n).mp c.2
  choose s hs hb hc using h
  exact (spTreeQueryCost_le_iff n).mpr
    ⟨fun p => s p.1 p.2, fun p => hs p.1 p.2, fun p => hb p.1 p.2, fun p => hc p.1 p.2⟩

/-- A variant of Claim 14 at query cost `n`, per adversary: a specialized simulator for each
environment of query cost at most `n` exists iff one simulator serves every test of query cost
at most `n`. -/
theorem exists_sim_iff_costBounded {ε : ℝ≥0∞} {hon out leak sim_if view : Type} (n : ℕ)
    (π : hon → SPComp (out ⊕ leak)) (F : hon → SPComp (out ⊕ sim_if))
    (A : leak → SPComp view) :
    (∀ (Z : Type) (inp : Z → hon) (E : Z × (out ⊕ view) → SPComp Bool), costBounded n E →
      ∃ S : sim_if → SPComp view, ∀ z : Z,
        UCMonadCompDist.ucDistComp
          (fun _ : Unit => π (inp z) >>= UCMonadBase.ucMapSum pure A)
          (fun _ : Unit => F (inp z) >>= UCMonadBase.ucMapSum pure S) (fun b => E (z, b)) ≤ ε)
    ↔ ∃ S : sim_if → SPComp view, ∀ D : out ⊕ view → SPComp Bool, costBounded n D →
      UCMonadCompDist.ucDistComp (fun a => π a >>= UCMonadBase.ucMapSum pure A)
        (fun a => F a >>= UCMonadBase.ucMapSum pure S) D ≤ ε :=
  exists_sim_iff_of_universal (fun D => costBounded n D)
    (fun f _ hg => le_trans (cost_precomp f) hg) π F A
    (costBoundedUniversal n _) (costBounded_costBoundedUniversal_run n _)

/-! ## Size at bound `n` -/

/-- An arrow is compiled from a finite-branching `SPTree` family whose trees have size at
most `n`. -/
def SizeBounded (n : ℕ) {α β : Type} (f : α → SPComp β) : Prop :=
  ∃ s : α → SPTree β, (∀ a, (s a).compile = f a) ∧ (∀ a, (s a).FinBranch) ∧
    ∀ a, (s a).size ≤ n

/-- `SizeBounded n` is closed under pure precomposition. -/
theorem SizeBounded.precomp {n : ℕ} {α α' β : Type} (f : α' → α) {g : α → SPComp β}
    (hg : SizeBounded n g) : SizeBounded n (g ∘ f) := by
  obtain ⟨s, hs, hb, hc⟩ := hg
  exact ⟨s ∘ f, fun a => hs (f a), fun a => hb (f a), fun a => hc (f a)⟩

/-- The universal environment of the tests of size at most `n`: codes are the tests,
evaluated by application. -/
noncomputable def sizeBoundedUniversal (n : ℕ) (V : Type) :
    UniversalEnv (T := SPComp) (view := V) (fun D => SizeBounded n D) where
  Code := {D : V → SPComp Bool // SizeBounded n D}
  run p := p.1.1 p.2
  cover D hD := ⟨⟨D, hD⟩, rfl⟩

/-- The universal environment of size `n` has size at most `n`. -/
theorem sizeBounded_sizeBoundedUniversal_run (n : ℕ) (V : Type) :
    SizeBounded n (sizeBoundedUniversal n V).run := by
  have h : ∀ c : (sizeBoundedUniversal n V).Code, ∃ s : V → SPTree Bool,
      (∀ a, (s a).compile = c.1 a) ∧ (∀ a, (s a).FinBranch) ∧ ∀ a, (s a).size ≤ n :=
    fun c => c.2
  choose s hs hb hc using h
  exact ⟨fun p => s p.1 p.2, fun p => hs p.1 p.2, fun p => hb p.1 p.2, fun p => hc p.1 p.2⟩

/-- A variant of Claim 14 at size `n`, per adversary: a specialized simulator for each
environment of size at most `n` exists iff one simulator serves every test of size at most `n`. -/
theorem exists_sim_iff_sizeBounded {ε : ℝ≥0∞} {hon out leak sim_if view : Type} (n : ℕ)
    (π : hon → SPComp (out ⊕ leak)) (F : hon → SPComp (out ⊕ sim_if))
    (A : leak → SPComp view) :
    (∀ (Z : Type) (inp : Z → hon) (E : Z × (out ⊕ view) → SPComp Bool), SizeBounded n E →
      ∃ S : sim_if → SPComp view, ∀ z : Z,
        UCMonadCompDist.ucDistComp
          (fun _ : Unit => π (inp z) >>= UCMonadBase.ucMapSum pure A)
          (fun _ : Unit => F (inp z) >>= UCMonadBase.ucMapSum pure S) (fun b => E (z, b)) ≤ ε)
    ↔ ∃ S : sim_if → SPComp view, ∀ D : out ⊕ view → SPComp Bool, SizeBounded n D →
      UCMonadCompDist.ucDistComp (fun a => π a >>= UCMonadBase.ucMapSum pure A)
        (fun a => F a >>= UCMonadBase.ucMapSum pure S) D ≤ ε :=
  exists_sim_iff_of_universal (fun D => SizeBounded n D)
    (fun f _ hg => SizeBounded.precomp f hg) π F A
    (sizeBoundedUniversal n _) (sizeBounded_sizeBoundedUniversal_run n _)

end CatCrypt.Crypto.SpecializedSimulator
