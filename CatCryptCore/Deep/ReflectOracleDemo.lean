/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Deep.Reflect
import CatCryptCore.Deep.Package

/-!
# Reflecting games that call abstract primitives / opaque oracles

`rawCode%` (see `Deep/Reflect.lean`) reifies a shallow `SPComp` program into a
syntactic `RawCode`. Beyond the six canonical constructors, it also reflects an
`SPComp`-typed subterm whose head is *abstract* — a call to a primitive the game
does not implement (`f a : SPComp β`), a locally-bound oracle, or an opaque
constant — as an `embed` leaf. Because `RawCode.eval (embed c) = c` holds
definitionally, the reified program round-trips, and `IsValid.embed`
(`Deep/Package.lean`) supplies the validity proof. This is what makes reflective
state-separating proofs expressible for compositional cryptography, where games
routinely call an abstract adversary or primitive.

The `embed` route is the reifier default because it *round-trips*. The structured
`RawCode.oracleCall` image is also available (constructor, `IsValid.oracleCall`,
and `substOracle` are all wired) and is the right choice when the opaque head is
meant to be *linked* later — but its `eval` is `SPComp.fail`, so it does not
round-trip on its own. The final section demonstrates that path.
-/

namespace CatCrypt.Deep.ReflectOracleDemo

open CatCrypt.Core CatCrypt.Deep

/-! ## An abstract primitive

`f : Bool → SPComp Bool` models a call to a primitive (or oracle, or adversary)
the game does not implement. -/

variable (f : Bool → SPComp Bool)

/-- A game calling the abstract primitive `f` reflects to a `RawCode` rather than
    raising "unsupported head": `f true` becomes an `embed` leaf, the trailing
    `SPComp.pure` a `ret`. -/
noncomputable def deepAbstract : RawCode Bool :=
  rawCode% (SPComp.bind (f true) (fun b => SPComp.pure b))

/-- The reflected abstract-primitive game evaluates back to the original shallow
    program. Definitional: `eval (embed (f true)) = f true`,
    `eval (ret b) = SPComp.pure b`, and η collapses `fun b => SPComp.pure b` to
    `SPComp.pure`. -/
theorem deepAbstract_reflect :
    (deepAbstract f).eval = SPComp.bind (f true) SPComp.pure := rfl

/-! ## Concrete and opaque heads coexist

`sample Bool` reflects to the canonical `RawCode.sample`; the following abstract
`f b` reflects to an `embed` leaf. Concrete constructor handling is unchanged. -/

/-- Sample a bit, then feed it to the abstract primitive `f`. -/
noncomputable def deepMixed : RawCode Bool :=
  rawCode% (SPComp.bind (SPComp.sample Bool) (fun b => f b))

/-- The mixed game round-trips: both the `sample` and the embedded `f b` evaluate
    back to their shallow images. -/
theorem deepMixed_reflect :
    (deepMixed f).eval = SPComp.bind (SPComp.sample Bool) (fun b => f b) := rfl

/-! ## The `oracleCall` route (structured, link-oriented)

`RawCode.oracleCall` reflects an opaque head as a *named* operation call to be
resolved later by `substOracle` / `DeepPackage.link`. It is `IsValid` for any
location set (no location access), and unlinked it evaluates to `SPComp.fail`;
after substitution it takes on the linked implementation's behaviour. -/

/-- A standalone oracle call to operation `0 : ℕ`, domain and codomain `Bool`. -/
def oracleLeaf : RawCode Bool := RawCode.oracleCall 0 Bool Bool true

/-- `oracleCall` is valid for every location set (synthesized automatically once
    the `oracleLeaf` abbreviation is unfolded to its `oracleCall` head). -/
example (L : LocSet) : IsValid L oracleLeaf := by unfold oracleLeaf; infer_instance

/-- Unlinked, an oracle call evaluates to failure. -/
theorem oracleLeaf_eval : oracleLeaf.eval = SPComp.fail := rfl

/-- `substOracle` resolves the oracle call using the supplied environment; here a
    trivial environment sends it to `fail`, but any linked implementation is
    substituted the same way. -/
theorem oracleLeaf_subst :
    oracleLeaf.substOracle (fun _ _ _ _ => RawCode.fail) = RawCode.fail := rfl

end CatCrypt.Deep.ReflectOracleDemo
