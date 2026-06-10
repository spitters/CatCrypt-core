import CatCrypt.Package.Interface
import CatCrypt.Package.Locations
import CatCrypt.Package.RawPackage
import CatCrypt.Package.ValidPackage

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

* [Benton et al., *Nominal SSProve*](https://eprint.iacr.org/2025/598)
-/
