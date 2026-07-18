/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Deep.Reflect
import CatCryptCore.Deep.Package
import CatCryptCore.Deep.Bridge
import CatCryptCore.Crypto.NomAdvantage

set_option autoImplicit false

/-!
# Single-Export Game Packages from Reflected Code

A `RawCode Bool` is packaged as a `DeepPackage` (respectively `NomPackage`)
whose sole export is the main procedure `(0, Unit, Bool)` — the entry point that
`runPkg` / `runDeep` evaluate. Composed with `rawCode%` (reflection of a shallow
`SPComp α` into a syntactic `RawCode α`), these constructors realize the round
trip from a shallow game to a package and back: `runDeep (NomPackage.ofCode
(rawCode% g))` equals the original shallow program `g`.

## Main definitions

* `DeepPackage.ofCode` — the `DeepPackage` exporting `(0, Unit, Bool)` and
  implementing it with a given valid code.
* `NomPackage.ofCode` — the stateless (`∅`-location) nominal wrapper.

## Main results

* `runPkg_ofCode` — `runPkg (DeepPackage.ofCode c) = c.eval`.
* `runDeep_ofCode` — `runDeep (NomPackage.ofCode c) = c.eval`.
* `runDeep_ofCode_reflect` — the end-to-end reflection round trip on a
  coin-flip game.
-/

namespace CatCrypt.Deep

open CatCrypt.Core

universe u

/-- The single-export `DeepPackage` whose main procedure `(0, Unit, Bool)` is
    implemented by `c`. It has locations `L`, no imports, and exactly one export;
    the codomain of that export is `Bool`, into which `c`'s bundle is cast from
    the singleton-membership equality. -/
noncomputable def DeepPackage.ofCode {L : LocSet} (c : RawCode Bool) [IsValid L c] :
    DeepPackage where
  locs := L
  imports := ∅
  exports := ⟨[(0, Unit, Bool)]⟩
  impl := fun _ _ codom h _ =>
    have hc : codom = Bool := by
      have hh := List.mem_singleton.mp h
      simp only [Prod.mk.injEq] at hh
      exact hh.2.2
    hc ▸ ValidCodeBundle.auto c

/-- Evaluating the main export of `DeepPackage.ofCode c` yields `c.eval`. -/
theorem runPkg_ofCode {L : LocSet} (c : RawCode Bool) [IsValid L c] :
    CatCrypt.Crypto.runPkg (DeepPackage.ofCode (L := L) c) = c.eval := by
  have hmem : (0, Unit, Bool) ∈ (DeepPackage.ofCode (L := L) c).exports.ops :=
    List.mem_singleton.mpr rfl
  simp only [CatCrypt.Crypto.runPkg, dif_pos hmem]
  rfl

/-- The stateless nominal package whose main procedure is implemented by `c`.
    Its underlying `DeepPackage` uses no locations, so its atom set is empty and
    the location invariant reduces to `∅ = ∅.image _`. -/
noncomputable def NomPackage.ofCode (c : RawCode Bool) [IsValid (∅ : LocSet) c] :
    NomPackage where
  pkg := DeepPackage.ofCode (L := ∅) c
  locs_eq := by simp [DeepPackage.ofCode]

/-- Evaluating the nominal wrapper yields `c.eval`. -/
theorem runDeep_ofCode (c : RawCode Bool) [IsValid (∅ : LocSet) c] :
    CatCrypt.Crypto.runDeep (NomPackage.ofCode c) = c.eval := by
  rw [CatCrypt.Crypto.runDeep]
  exact runPkg_ofCode c

/-- End-to-end reflection round trip: a shallow coin-flip game reflects into deep
    code via `rawCode%`, wraps into a nominal package via `NomPackage.ofCode`, and
    `runDeep` recovers the original shallow program. -/
theorem runDeep_ofCode_reflect :
    CatCrypt.Crypto.runDeep (NomPackage.ofCode
      (rawCode% (SPComp.bind (SPComp.sample Bool) (fun b => SPComp.pure b))))
    = SPComp.bind (SPComp.sample Bool) (fun b => SPComp.pure b) := by
  rw [runDeep_ofCode]
  simp [RawCode.eval]

end CatCrypt.Deep
