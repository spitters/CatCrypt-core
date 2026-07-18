/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Unary.Judgment
import CatCryptCore.Unary.Lossless
import CatCryptCore.Unary.Rules
import CatCryptCore.Unary.Event
import CatCryptCore.Unary.Bridge
import CatCryptCore.Unary.FailureEvent
import CatCryptCore.Unary.QueryBound

/-!
# Unary Probabilistic Hoare Logic (pHL)

This module provides a unary probabilistic Hoare logic for CatCrypt,
inspired by EasyCrypt's pHL and CertiCrypt's unary reasoning.

## Submodules

* `Judgment` - `pHoare P c Q` definition and basic properties
* `Lossless` - `isLossless` predicate and losslessness of basic operations
* `Rules` - Proof rules: ret, fail, sample, get, set, bind, assert, frame
* `Event` - Event probability `prEvent` and bounds (union, complement, monotone)
* `Bridge` - Connections between pHL, pRHL, and probability (FEL, byphoare)
* `FailureEvent` - Enhanced failure event lemma variants for game hopping
* `QueryBound` - Query-bounded adversary infrastructure

## What's Novel

This entire unary logic layer is **new to CatCrypt** - the Rocq version
(CatCrypt/Coq) has only a relational logic (pRHL). The unary logic enables:

1. **Probability bounds**: Direct computation of `Pr[G:E]` from pHL judgments
2. **Failure Event Lemma**: Up-to-bad reasoning (`|Pr[G₀:A] - Pr[G₁:A]| ≤ Pr[G₀:bad]`)
3. **Losslessness reasoning**: Proving computations never fail
4. **Query counting**: Bounding adversary queries for concrete security bounds

## References

* EasyCrypt: `phoare`, `byphoare`, `fel` tactics
* CertiCrypt (Barthe et al.): unary reasoning in Coq
* SSProve (Rocq): only has pRHL (this layer is an extension)
-/

namespace CatCrypt.Unary

-- All definitions and theorems are available via the imports above.

end CatCrypt.Unary
