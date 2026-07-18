import CatCryptCore.Nominal.Atom
import CatCryptCore.Nominal.FinPerm
import CatCryptCore.Nominal.Nominal
import CatCryptCore.Nominal.Fresh
import CatCryptCore.Nominal.NameAbstraction
import CatCryptCore.Nominal.Support
import CatCryptCore.Nominal.NomPackage

/-!
# Nominal Sets

This module provides the nominal sets infrastructure for CatCrypt.
Nominal sets are mathematical structures for reasoning about names and binding.

## Main submodules

* `CatCrypt.Nominal.Atom` - Atoms (abstract names) and permutations
* `CatCrypt.Nominal.FinPerm` - Finite permutations (group structure)
* `CatCrypt.Nominal.Nominal` - Nominal sets typeclass and action
* `CatCrypt.Nominal.Fresh` - Freshness and move operation
* `CatCrypt.Nominal.NameAbstraction` - Name abstraction `[𝔸]α` (Pitts Ch. 4)
* `CatCrypt.Nominal.Support` - Support class and predicates
* `CatCrypt.Nominal.NomPackage` - Nominal packages with separated composition

## References

* [Pitts, *Nominal Sets*]
* [Larsen and Schürmann, *Nominal State-Separating Proofs*](https://eprint.iacr.org/2025/598)
-/
