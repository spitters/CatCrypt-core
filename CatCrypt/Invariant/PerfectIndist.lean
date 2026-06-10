/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Invariant.SemiInvariant
import CatCrypt.Relational.Judgment
import CatCrypt.Package.ValidPackage

/-!
# Perfect Indistinguishability

This file defines perfect indistinguishability between packages and provides
the main lemma `eq_rel_perf_ind` for proving it using invariants.

## Main definitions

* `PerfectIndist` - Two packages are perfectly indistinguishable
* `eq_up_to_inv` - Packages are equal up to an invariant on each operation

## Main results

* `eq_rel_perf_ind` - If packages are equal up to an invariant, they are
  perfectly indistinguishable

## Notation

* `G₀ ≈₀ G₁` - Perfect indistinguishability

## References

* [Benton et al., *Nominal SSProve*](https://eprint.iacr.org/2025/598)
* SSProve: theories/Crypt/package/pkg_rhl.v
-/

namespace CatCrypt.Invariant

open CatCrypt.Core
open CatCrypt.Relational
open CatCrypt.Package
open CatCrypt.Prob

/-! ## Perfect Indistinguishability -/

/-- Two packages are perfectly indistinguishable if for all adversaries with
    disjoint state, the advantage is 0.

    `G₀ ≈₀ G₁` means that no adversary can distinguish between G₀ and G₁.

    **WARNING: This is a placeholder defined as `True`.**
    The shallow package layer (`RawPackage`) does not support linking
    (see `RawPackage.link`), so a meaningful quantification over adversaries
    is not possible here. All theorems about `PerfectIndist` are therefore
    vacuously true.

    **For real security proofs, use the deep embedding layer:**
    - `DeepNomAdvantage` in `CatCrypt.Crypto.NomAdvantage` for advantage bounds
    - `DeepPackage.link` in `CatCrypt.Deep.Package` for package composition
    - `runPkg_link_congr` for proving game equivalences -/
def PerfectIndist {L₀ L₁ : Locations} {I E : Interface}
    (P₀ : RawPackage) (P₁ : RawPackage)
    (_ : ValidPackage L₀ I E P₀) (_ : ValidPackage L₁ I E P₁) : Prop :=
  True

-- Notation
notation:50 "(" G₀ " ≈₀ " G₁ ")" => PerfectIndist G₀ G₁

/-! ## Equality Up To Invariant -/

/-- Two packages are equal up to an invariant if each procedure,
    when run from states satisfying the invariant, produces
    coupled outputs that also satisfy the invariant. -/
def eq_up_to_inv {L₀ L₁ : Locations} {I E : Interface}
    (inv : RPre) (P₀ P₁ : RawPackage)
    (_ : ValidPackage L₀ I E P₀) (_ : ValidPackage L₁ I E P₁) : Prop :=
  ∀ id S T, E.has id S T → ∀ x : S,
    ∀ h₀ h₁, inv h₀ h₁ →
      -- There exists a coupling where results are equal and invariant preserved
      liftR (fun (p₀ : T × Heap) (p₁ : T × Heap) =>
        p₀.1 = p₁.1 ∧ inv p₀.2 p₁.2)
        (RawPackage.resolve P₀ id (x : S) h₀)
        (RawPackage.resolve P₁ id (x : S) h₁)

/-! ## Main Lemma -/

/-- If packages are equal up to an invariant, they are perfectly indistinguishable.

    This is the main tool for proving perfect indistinguishability:
    1. Choose an invariant (often `heapEq` for simple cases)
    2. Prove the invariant is valid for L₀ and L₁
    3. Prove `eq_up_to_inv` for each procedure

    The proof idea: since results are equal and invariant is preserved,
    an adversary making queries cannot observe any difference. -/
theorem eq_rel_perf_ind {L₀ L₁ : Locations} {I E : Interface}
    (P₀ P₁ : RawPackage)
    (hP₀ : ValidPackage L₀ I E P₀) (hP₁ : ValidPackage L₁ I E P₁)
    (inv : RPre) [IsInvariant L₀ L₁ inv]
    (_hinv_eq : eq_up_to_inv inv P₀ P₁ hP₀ hP₁) :
    PerfectIndist P₀ P₁ hP₀ hP₁ := by
  -- The proof requires showing that linked games produce equal distributions
  -- This follows from the coupling argument: if all procedures are coupled,
  -- the full game execution is coupled with equal results
  trivial

/-! ## Simplified Version: Equality Invariant -/

/-- Corollary: if packages are equal up to heap equality, they are indistinguishable.
    This is simpler than the general invariant case. -/
theorem eq_rel_perf_ind_eq {L₀ L₁ : Locations} {I E : Interface}
    (P₀ P₁ : RawPackage)
    (hP₀ : ValidPackage L₀ I E P₀) (hP₁ : ValidPackage L₁ I E P₁)
    (_heq : eq_up_to_inv (fun h₀ h₁ => h₀ = h₁) P₀ P₁ hP₀ hP₁) :
    PerfectIndist P₀ P₁ hP₀ hP₁ := by
  -- Apply eq_rel_perf_ind with equality invariant
  trivial

/-! ## Tactics Support -/

/-- Simplify the goal for eq_up_to_inv proofs.
    Called by `simplify_eq_rel` tactic.

    Note: This theorem provides the bridge between the eq_up_to_inv definition
    (which uses liftR directly) and the rHoare judgment. The types are:
    - RawPackage.resolve P id x : SPComp T = Heap → SProb (T × Heap)
    - rHoare expects SPComp α and SPComp β -/
theorem simplify_eq_rel_intro {L₀ L₁ : Locations} {I E : Interface}
    (inv : RPre) (P₀ P₁ : RawPackage)
    (hP₀ : ValidPackage L₀ I E P₀) (hP₁ : ValidPackage L₁ I E P₁)
    (h : ∀ id S T, E.has id S T → ∀ x : S,
      rHoare (α := T) (β := T) inv
        (RawPackage.resolve P₀ id x)
        (RawPackage.resolve P₁ id x)
        (fun v₀ h₀ v₁ h₁ => v₀ = v₁ ∧ inv h₀ h₁)) :
    eq_up_to_inv inv P₀ P₁ hP₀ hP₁ := h

end CatCrypt.Invariant
