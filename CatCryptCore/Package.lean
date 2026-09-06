module

public import CatCryptCore.Package.Interface
public import CatCryptCore.Package.Locations
public import CatCryptCore.Package.RawPackage
public import CatCryptCore.Package.ValidPackage

/-!
# Package System

This module provides the package system infrastructure for CatCrypt.
Packages are composable cryptographic components with interfaces.

## Main submodules

* `CatCrypt.Package.Interface` - Operation signatures and interfaces
* `CatCrypt.Package.Locations` - Memory location tracking
* `CatCrypt.Package.RawPackage` - Raw packages (unvalidated)
* `CatCrypt.Package.ValidPackage` - Valid packages with proofs

## References

* [Larsen and Schürmann, *Nominal State-Separating Proofs*](https://eprint.iacr.org/2025/598)
-/

@[expose] public section
