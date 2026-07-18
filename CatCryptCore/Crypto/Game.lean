/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Core.Code

/-!
# Cryptographic Games

This file defines cryptographic games for security proofs.
-/

namespace CatCrypt.Crypto

open CatCrypt.Core

/-- A cryptographic game parameterized by a boolean (real vs ideal) -/
structure Game where
  run : Bool → SPComp Bool

end CatCrypt.Crypto
