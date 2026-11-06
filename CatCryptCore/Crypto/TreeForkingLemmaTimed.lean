/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.TreeForkingLemma
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.StdCosts

/-!
# Time of the tree extractor of the tree-forking lemma

The derived cost `extract.timedCost` of the rewinding extractor `extract` of
`CatCryptCore.Crypto.TreeForkingLemma` (`derive_cost`), the costed form of the tree extractor
`treeExtractor` (`derive_reduction`), and the time theorem of each.

## Cost model

The rules of `CatCryptCore.Tactics.DeriveTimed`. A strategy is a value of the type computed by
recursion `Strategy Y rs`; its continuation `s.2 c` at a challenge `c` is a table read at one
unit (rule (l)), so the cost counts each rewinding of the prover at one unit, and the verifier
`V` at its cost companion `VCost`. The enumeration `FinEnum.toList r.C` of the challenges costs
one unit per challenge (`CatCryptCore.Tactics.StdCosts`). At a node of round `r` the extractor
runs the sub-extraction once for each of the `|r.C|` challenges: the recursive cost occurs once,
in the cost companion of the function that `List.filterMap` maps over the enumeration, which
`List.filterMap.timedCost` charges once per challenge. The cost is therefore that of the
exhaustive extractor, with `∏ᵢ |Cᵢ|` runs of the verifier; an extractor that stops a node after
`kᵢ` successes is another program. The children `fun j => L.get (Fin.castLE h j)` of an
extracted node, a closure over `Fin r.k` placed in a transcript tree, are tabulated where they
are built (rule (m)), at the cost of the `r.k` reads of the list `L` of kept pairs.

## Main definitions

* `extractBound rs v` — a bound on the cost of `extract rs` for a verifier of cost at most `v`

## Main results

* `extract.timedCost_le` — the derived cost of `extract rs` is at most `extractBound rs v`
* `treeExtractor.tree.timeBound_timed` — on a costed prover of time `T`, the costed tree
  extractor runs in time at most `T + 1 + extractBound rs v`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.TreeForking

open CatCrypt.Core

variable {Y : Type}

-- The cost of the rewinding extractor: at a node, one sub-extraction per challenge of the
-- enumeration, the strategy's continuation read as a table, the kept children tabulated.
derive_cost extract

-- The costed tree extractor: the costed prover, then the extractor at its derived cost.
derive_reduction treeExtractor

/-- A bound on the derived cost of `extract rs` for a verifier whose cost companion is at most
`v`: `v + 3` at a leaf, and at a node of round `r` with `n = |r.C|` challenges
`n * (extractBound rs (v + 1) + 12) + r.k * (5 * n + 5) + 7`: one sub-extraction per challenge,
whose verifier costs one unit more, and the `r.k` reads of the list of kept pairs. -/
def extractBound : List Round → ℕ → ℕ
  | [], v => v + 3
  | r :: rs, v =>
    FinEnum.card r.C * (extractBound rs (v + 1) + 12) + r.k * (5 * FinEnum.card r.C + 5) + 7

/-- The derived cost of the rewinding extractor is at most `extractBound rs v` for a verifier
whose cost companion is at most `v`. -/
theorem extract.timedCost_le : ∀ (rs : List Round) (V : Transcript rs → Y → Bool)
    (VCost : Transcript rs → Y → ℕ) (v : ℕ), (∀ t y, VCost t y ≤ v) →
    ∀ s : Strategy Y rs, extract.timedCost rs V VCost s ≤ extractBound rs v
  | [], V, VCost, v, hV, s => by
    rw [extract.timedCost.eq_1, extractBound]
    have := hV () s
    omega
  | r :: rs, V, VCost, v, hV, s => by
    rw [extract.timedCost.eq_2, extractBound]
    have hE : ∀ c, extract.timedCost rs (fun t y => V (s.1, c, t) y)
        (fun t y => 1 + VCost (s.1, c, t) y) (s.2 c) ≤ extractBound rs (v + 1) := fun c =>
      extract.timedCost_le rs _ _ (v + 1) (fun t y => by have := hV (s.1, c, t) y; omega) (s.2 c)
    have hFM := List.filterMap.timedCost_le
      (fun c => Option.map (fun T => (c, T)) (extract rs (fun t y => V (s.1, c, t) y) (s.2 c)))
      (fun c => 1 + (1 + (extract.timedCost rs (fun t y => V (s.1, c, t) y)
        (fun t y => 1 + VCost (s.1, c, t) y) (s.2 c) + 1) + 1))
      (k := extractBound rs (v + 1) + 4) (fun c => by have := hE c; omega) (FinEnum.toList r.C)
    have hlen : (FinEnum.toList r.C).length = FinEnum.card r.C := by simp [FinEnum.toList]
    have hL := List.length_filterMap_le
      (fun c => Option.map (fun T => (c, T)) (extract rs (fun t y => V (s.1, c, t) y) (s.2 c)))
      (FinEnum.toList r.C)
    rw [hlen] at hFM hL
    generalize List.filterMap
      (fun c => Option.map (fun T => (c, T)) (extract rs (fun t y => V (s.1, c, t) y) (s.2 c)))
      (FinEnum.toList r.C) = L at hL ⊢
    have hD : (if h : r.k ≤ L.length then
        ∑ a : Fin r.k, (1 + (List.get.timedCost L (Fin.castLE h a) +
          (2 + List.length.timedCost L))) else 0) ≤ r.k * (5 * FinEnum.card r.C + 5) := by
      split
      · refine (Finset.sum_le_card_nsmul _ _ (5 * FinEnum.card r.C + 5) fun a _ => ?_).trans ?_
        · have := List.get.timedCost_le L (Fin.castLE ‹_› a)
          rw [List.length.timedCost_eq]
          omega
        · simp
      · exact Nat.zero_le _
    simp only [FinEnum.toList.timedCost, List.length.timedCost_eq] at hFM hD ⊢
    have := Nat.mul_le_mul_left (extractBound rs (v + 1) + 8) hL
    nlinarith

/-- The time of the costed tree extractor: a costed prover of time `T` and a verifier whose cost
companion is at most `v` give the time `T + 1 + extractBound rs v`. -/
theorem treeExtractor.tree.timeBound_timed (rs : List Round) (P : SPTree.Timed (Strategy Y rs))
    (V : Transcript rs → Y → Bool) (VCost : Transcript rs → Y → ℕ) {T v : ℕ}
    (hP : P.time ≤ T) (hV : ∀ t y, VCost t y ≤ v) :
    SPTree.Timed.stepTime (treeExtractor.tree.timed rs P V VCost) ≤
      T + (1 + extractBound rs v) := by
  rw [treeExtractor.tree.timed]
  refine (SPTree.Timed.stepTime_bind_le P _ (1 + extractBound rs v) fun s => ?_).trans
    (Nat.add_le_add_right hP _)
  have := extract.timedCost_le rs V VCost v hV s
  simp only [SPTree.Timed.stepTime, SPTree.Timed.time_ret]
  omega

end CatCrypt.Crypto.TreeForking
