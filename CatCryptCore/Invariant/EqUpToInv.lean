/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Invariant.SemiInvariant
import CatCryptCore.Relational.Judgment
import CatCryptCore.Package.ValidPackage

/-!
# Equality up to an invariant

`eq_up_to_inv` relates two shallow packages that agree on every operation up to a
heap invariant, with the bridge `simplify_eq_rel_intro` from the relational
judgment `rHoare`.

A security bound — a zero or bounded `Advantage` — is proved through the deep
embedding: `DeepNomAdvantage` and `NomPkgSecure` in `CatCrypt.Crypto.NomAdvantage`,
over `DeepPackage.link`.

## References

* [Larsen and Schürmann, *Nominal State-Separating Proofs*](https://eprint.iacr.org/2025/598)
* SSProve: theories/Crypt/package/pkg_rhl.v
-/

namespace CatCrypt.Invariant

open CatCrypt.Core
open CatCrypt.Relational
open CatCrypt.Package
open CatCrypt.Prob

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

/-! ## Bridge from the relational judgment -/

/-- Package equality up to an invariant follows from a per-operation `rHoare`
    judgment relating the two resolutions.

    The types line up as:
    - `RawPackage.resolve P id x : SPComp T = Heap → SDistr (T × Heap)`
    - `rHoare` expects `SPComp α` and `SPComp β`. -/
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
