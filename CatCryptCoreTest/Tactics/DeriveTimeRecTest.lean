/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveTimeRec
public import CatCryptCore.Tactics.DeriveCost
public import CatCryptCore.Tactics.StdCosts

/-!
# Tests for `derive_time_rec`

* `fold`: a fold over `ℕ` that runs a node computation per level; `sampleFold`: a fold that
  samples a bit per level, with its bound given by a recursive function `sampleFoldTime`.
* `view`: a recursion over `ℕ` with a convoy `r : Fin L → ℕ` whose cost companion grows at the
  recursive call, which runs the fold `fold` of `r 0` nodes per level (bounded by the time
  theorem of `fold`).
* `run`: a recursion over a list whose recursive call is under a bind, at the bound value; the
  cost companion of the step grows by one per level.
* `halve`: a recursion by well-founded recursion on `n / 2`, with the bound `halveTime`
  defined by the same recursion.
* `blocksL`: a recursive data function whose cost is quadratic; its bound `blocksL.timedCost_le`
  is used by `derive_time_bound` for the reduction `useBlocks`.
* `ask`: a costed oracle adversary that queries once per level.
* A bound too small for `sampleFold`, and a cost of a mutual block, are refused.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveTimeRecTest

open CatCrypt.Core

/-- `n` runs of `node`, collected into a function on `Fin n`. -/
noncomputable def fold {X : Type} (node : SPComp X) : (n : ℕ) → SPComp (Fin n → X)
  | 0 => SPComp.pure (fun i => i.elim0)
  | n + 1 => node.bind fun w0 => (fold node n).bind fun rest => SPComp.pure (Fin.cons w0 rest)

derive_reduction fold

derive_time_rec fold.tree using fun n G_node => n * (G_node + 3) + 1

/-- The time theorem of `fold`: `n` runs of `node` and three units per level. -/
example {X : Type} (node : SPTree.Timed X) (n : ℕ) {G : ℕ} (h : node.time ≤ G) :
    SPTree.Timed.stepTime (fold.tree.timed node n) ≤ n * (G + 3) + 1 :=
  fold.tree.timeBound_timed node n h

/-- The number of `true` bits among `n` uniform bits. -/
noncomputable def sampleFold : ℕ → SPComp ℕ
  | 0 => SPComp.pure 0
  | n + 1 => (SPComp.sample Bool).bind fun b =>
      (sampleFold n).bind fun k => SPComp.pure (if b then k + 1 else k)

derive_reduction sampleFold

/-- error: `CatCrypt.Tactics.DeriveTimeRecTest.sampleFold.tree.timeBound_timed` is not proved: -/
#guard_msgs (substring := true) in
derive_time_rec sampleFold.tree using fun n => 4 * n + 1

/-- The time bound of `sampleFold`, by the same recursion. -/
def sampleFoldTime : ℕ → ℕ
  | 0 => 1
  | n + 1 => sampleFoldTime n + 5

derive_time_rec sampleFold.tree using sampleFoldTime

/-- A recursion with a convoy `r` that runs the fold of `r 0` nodes per level. -/
noncomputable def view {X : Type} (node : SPComp X) :
    (L : ℕ) → (r : Fin L → ℕ) → SPComp ℕ
  | 0, _ => SPComp.pure 0
  | L + 1, r => (view node L (fun i => r i.succ)).bind fun k =>
      (fold node (r 0)).bind fun _ => SPComp.pure (k + 1)

derive_reduction view

derive_time_rec view.tree using fun L G_node t_r t_rCost =>
  L * (t_r * (G_node + 3) + t_rCost + 4 * L + 10) + 1

/-- The binders `r`, `rCost` of the costed form are named after the source. -/
example {X : Type} (node : SPTree.Timed X) (L : ℕ) (r rCost : Fin L → ℕ) {G R c : ℕ}
    (hn : node.time ≤ G) (hr : ∀ i, r i ≤ R) (hc : ∀ i, rCost i ≤ c) :
    SPTree.Timed.stepTime (view.tree.timed node L r rCost) ≤
      L * (R * (G + 3) + c + 4 * L + 10) + 1 :=
  view.tree.timeBound_timed node L r rCost hn hr hc

/-- A run of `step` over a list, threading a state. -/
noncomputable def run {S Y : Type} (step : S → ℕ → SPComp (S × Y)) :
    S → List ℕ → SPComp (S × List Y)
  | s, [] => SPComp.pure (s, [])
  | s, l :: ls => (step s l).bind fun p =>
      (run step p.1 ls).bind fun q => SPComp.pure (q.1, p.2 :: q.2)

derive_reduction run

derive_time_rec run.tree using fun (ls : List ℕ) T_step t_stepCost =>
  (T_step + t_stepCost + 4 + ls.length) * ls.length + 1

/-- One bit per halving of `n`. -/
noncomputable def halve (node : SPComp Bool) (n : ℕ) : SPComp ℕ :=
  if n ≤ 1 then SPComp.pure 0 else
    node.bind fun _ => (halve node (n / 2)).bind fun k => SPComp.pure (k + 1)
termination_by n
decreasing_by omega

derive_reduction halve

/-- The time bound of `halve`, by the same recursion. -/
def halveTime (G n : ℕ) : ℕ := if n ≤ 1 then 1 else G + 4 + halveTime G (n / 2)
termination_by n
decreasing_by omega

derive_time_rec halve.tree using fun n G_node => halveTime G_node n

/-- The list `acc ++ [k - 1, …, 0]`, by appending at the end. -/
def blocksL : ℕ → List ℕ → List ℕ
  | 0, acc => acc
  | k + 1, acc => blocksL k (acc ++ [k])

derive_cost blocksL

derive_time_rec blocksL.timedCost using fun k (acc : List ℕ) => k * (2 * acc.length + k + 5) + 1
  with [List.length_append, List.length_singleton]

/-- Sample a bit and pass the blocks from it to the adversary. -/
noncomputable def useBlocks (k : ℕ) (A : List ℕ → SPComp Bool) : SPComp Bool := do
  let i ← SPComp.sample (Fin 4)
  A (blocksL k [i.val])

derive_reduction useBlocks

derive_time_bound useBlocks.tree

/-- The time theorem of `useBlocks` bounds the cost of `blocksL` by `blocksL.timedCost_le`. -/
example (k : ℕ) (A : List ℕ → SPTree.Timed Bool) (ACost : List ℕ → ℕ) {T c : ℕ}
    (hA : ∀ x, (A x).time ≤ T) (hc : ∀ x, ACost x ≤ c) :
    SPTree.Timed.stepTime (useBlocks.tree.timed k A ACost) ≤ c + k * (k + 7) + T + 4 := by
  have h := useBlocks.tree.timeBound_timed k A ACost hA hc
  simp only [List.length_nil, Nat.zero_add, Nat.mul_one] at h
  grind

open CatCrypt.Crypto in
/-- An oracle adversary that queries `n` times. -/
noncomputable def ask : ℕ → OracleAdv ℕ Bool ℕ
  | 0 => .ret 0
  | n + 1 => .query n fun _ => ask n

derive_timed ask

/-- The time bound of `ask`, by the same recursion. -/
def askTime : ℕ → ℕ
  | 0 => 1
  | n + 1 => 2 * askTime n + 4

derive_time_rec ask using askTime

/-- The time theorem of a costed oracle adversary is a `StepTimeBound`. -/
example (n : ℕ) : CatCrypt.Crypto.OracleAdv.Timed.StepTimeBound (ask.timed n) (askTime n) :=
  ask.timeBound_timed n


mutual
/-- A size of a natural number, even part. -/
def evenSize : ℕ → ℕ
  | 0 => 0
  | n + 1 => oddSize n + 1
/-- A size of a natural number, odd part. -/
def oddSize : ℕ → ℕ
  | 0 => 1
  | n + 1 => evenSize n + 2
end

derive_cost evenSize

/-- is defined by mutual recursion -/
#guard_msgs (substring := true) in
derive_time_rec evenSize.timedCost using fun n => 3 * n + 1

end CatCrypt.Tactics.DeriveTimeRecTest
