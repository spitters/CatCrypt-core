/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCrypt.Crypto.Bridges.VCVioBridge.Monad
import CatCrypt.Crypto.Bridges.VCVioBridge.State
import CatCrypt.Crypto.Bridges.VCVioBridge.Linking
import CatCrypt.Crypto.Bridges.VCVioBridge.Relational
import CatCrypt.Crypto.Bridges.VCVioBridge.Examples.Coin
import CatCrypt.Crypto.Bridges.VCVioBridge.Examples.OneTimePad
import CatCrypt.Crypto.Bridges.VCVioBridge.Examples.AdvantageTransfer

/-!
# VCVio Bridge — Umbrella

Re-exports the public core of the VCVio↔CatCrypt bridge. New work goes into
submodules under `CatCrypt/Crypto/Bridges/VCVioBridge/`. This umbrella preserves
the namespace `CatCrypt.Crypto.VCVioBridge` for downstream importers.

## Layers

* `Monad` — probability-level bridge and the `probCompLift` monad morphism
* `State` — heap-as-oracle encoding and the `runState` morphism
* `Linking` — identification of CatCrypt package linking with VCVio `simulateQ`
* `Relational` — `probCompLift` probability preservation and advantage transfer
* `Examples/*` — bridge usage patterns (Coin, OneTimePad, AdvantageTransfer)

## Private extensions (not re-exported here)

* `UCLift` — `UCMonadMorphism` wrapping and `UCEmulates` transfer theorems.
  Depends on the `UCMonad` typeclass; import explicitly if needed.
* `Forking` — re-exports of VCVio's upstream forking lemma. Import explicitly
  if needed; the native CatCrypt forking lemma in
  `CatCrypt/Crypto/ForkingLemma.lean` is the default.
-/
