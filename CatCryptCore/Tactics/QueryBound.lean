/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OracleProfile
public import CatCryptCore.Tactics.QueryFold

/-!
# The import of the tactic `query_bound`

This module provides the tactic `query_bound` of `CatCryptCore.Tactics.QueryFold` together with the
theory of the budget-passing fold in `CatCryptCore.Crypto.OracleProfile` that it names. A module that
only carries the attribute `@[query_fold]` imports `CatCryptCore.Tactics.QueryFold`.

Search words: query bound, cost bound, query count, per-oracle count, provenance, tactic.
-/
