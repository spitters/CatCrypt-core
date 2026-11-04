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
* `blocksG`: blocks from a function with a cost companion; the bound of its cost is a closed
  form, the product of the block count and the length of the blocks.
* `useNested`: the length of a list built by `blocksL` from a sampled value, bounded free of the
  value by the `@[length_bound]` theorem `blocksL_length`.
* `usePair`: a fold over the positions of a list built from a sampled value, its length bounded
  by the `@[length_bound]` theorem `pairL_length_le` when the bound is stated and at the
  arithmetic leaves; `usePairOn`: the same over `pairL o` of a value `o` matched from the
  argument `q`, with a bound free of `q`.
* `ask`: a costed oracle adversary that queries once per level.
* `pathView`: a recursion behind a structure binder whose levels fold a compound node
  `nodeIdeal deps`; `pathChain`: the same with the fold first, of a node below a `have`, whose
  step cost the caller charges. The induction is on the recursion argument only.
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

/-- `k` blocks from position `n`: block `i` is `f i (n + B * i)`, appended at the end. -/
def blocksG (B : ℕ) (f : ℕ → ℕ → List ℕ) (n : ℕ) : ℕ → List ℕ
  | 0 => []
  | k + 1 => blocksG B f n k ++ f k (n + B * k)

derive_cost blocksG

/-- `k + 1` blocks have the elements of the first `k` blocks and of block `k`. -/
theorem blocksG_length_succ (B : ℕ) (f : ℕ → ℕ → List ℕ) (n k : ℕ) :
    (blocksG B f n (k + 1)).length = (blocksG B f n k).length + (f k (n + B * k)).length := by
  rw [blocksG, List.length_append]

-- a closed form, product of the block count and the length of the blocks
derive_time_rec blocksG.timedCost using fun k t_fCost (f : ℕ → ℕ → List ℕ) B n =>
  k * (t_fCost + 2 * (blocksG B f n k).length + 7) + 1
  with [blocksG_length_succ]

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

/-- `blocksL k acc` has the elements of `acc` and `k` more. -/
@[length_bound] theorem blocksL_length (k : ℕ) (acc : List ℕ) :
    (blocksL k acc).length = acc.length + k := by
  induction k generalizing acc with
  | zero => simp [blocksL]
  | succ k ih =>
    simp only [blocksL, ih, List.length_append, List.length_singleton] <;> omega

/-- Sample a number below 4, build that many blocks, and pass `k` blocks more from them to the
adversary. -/
noncomputable def useNested (k : ℕ) (A : List ℕ → SPComp Bool) : SPComp Bool := do
  let i ← SPComp.sample (Fin 4)
  A (blocksL k (blocksL i.val []))

derive_reduction useNested

-- the cost of the outer `blocksL` mentions the length of the inner list, which mentions the
-- sampled value; `@[length_bound]` on `blocksL_length` bounds it free of that value
derive_time_bound useNested.tree

/-- The time theorem of `useNested` bounds its step time free of the sampled value. -/
example (k : ℕ) (A : List ℕ → SPTree.Timed Bool) (ACost : List ℕ → ℕ) {T c : ℕ}
    (hA : ∀ x, (A x).time ≤ T) (hc : ∀ x, ACost x ≤ c) :
    ∃ E, SPTree.Timed.stepTime (useNested.tree.timed k A ACost) ≤ E :=
  ⟨_, useNested.tree.timeBound_timed k A ACost hA hc⟩

/-- One or two copies of `i`. -/
def pairL (i : ℕ) : List ℕ := if i < 2 then [i] else [i, i]

derive_cost pairL

/-- Building `pairL i` costs at most one unit. -/
theorem pairL.timedCost_le (i : ℕ) : pairL.timedCost i ≤ 1 := by
  unfold pairL.timedCost; grind

/-- `pairL i` has at most two elements. -/
@[length_bound] theorem pairL_length_le (i : ℕ) : (pairL i).length ≤ 2 := by
  unfold pairL; split <;> simp

/-- Sample a number below 4 and pass to the adversary the sum of the positions of `pairL` of
it, folded over those positions from its length. -/
noncomputable def usePair (A : ℕ → SPComp Bool) : SPComp Bool := do
  let i ← SPComp.sample (Fin 4)
  let l := pairL i.val
  A (Fin.foldr l.length (fun j acc => acc + j.val) l.length)

derive_reduction usePair

-- the fold runs over the positions of `pairL` of the sampled value; `@[length_bound]` on
-- `pairL_length_le` states the bound free of that value and closes its arithmetic leaves
derive_time_bound usePair.tree

/-- The time theorem of `usePair` bounds its step time free of the sampled value. -/
example (A : ℕ → SPTree.Timed Bool) (ACost : ℕ → ℕ) {T c : ℕ}
    (hA : ∀ x, (A x).time ≤ T) (hc : ∀ x, ACost x ≤ c) :
    ∃ E, SPTree.Timed.stepTime (usePair.tree.timed A ACost) ≤ E :=
  ⟨_, usePair.tree.timeBound_timed A ACost hA hc⟩

/-- On an answer `some o`, pass to the adversary the sum of the positions of `pairL o`, folded
over those positions from its length; on `none`, pass `0`. -/
noncomputable def usePairOn (q : Option ℕ) (A : ℕ → SPComp Bool) : SPComp Bool :=
  match q with
  | none => A 0
  | some o =>
    let l := pairL o
    A (Fin.foldr l.length (fun j acc => acc + j.val) l.length)

derive_reduction usePairOn

-- the fold runs over the positions of `pairL` of the matched answer; `@[length_bound]` on
-- `pairL_length_le` states the bound free of the answer and closes its arithmetic leaves
derive_time_bound usePairOn.tree

/-- The time theorem of `usePairOn` bounds its step time by one bound for every answer. -/
example (A : ℕ → SPTree.Timed Bool) (ACost : ℕ → ℕ) {T c : ℕ}
    (hA : ∀ x, (A x).time ≤ T) (hc : ∀ x, ACost x ≤ c) :
    ∃ E, ∀ q, SPTree.Timed.stepTime (usePairOn.tree.timed q A ACost) ≤ E :=
  ⟨_, fun q => usePairOn.tree.timeBound_timed q A ACost hA hc⟩

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

/-- A record of computations: a key generation. -/
structure Deps where
  /-- The key generation. -/
  keygen : SPComp (ℕ × ℕ)

/-- One ideal node: a key generation and two bits. -/
noncomputable def nodeIdeal (deps : Deps) : SPComp (ℕ × ℕ × ℕ) :=
  SPComp.bind deps.keygen fun r => SPComp.bind (SPComp.sample Bool) fun e =>
    SPComp.bind (SPComp.sample Bool) fun c => SPComp.pure (r.2, e.toNat, c.toNat)

/-- A path of `L` levels, level `i` holding a key and `r i` nodes. -/
def PathView : (L : ℕ) → (Fin L → ℕ) → Type
  | 0, _ => Unit
  | L + 1, r => (ℕ × (Fin (r 0) → ℕ × ℕ × ℕ)) × PathView L (fun i => r i.succ)

/-- The path of no level. -/
def pathNil (r : Fin 0 → ℕ) : PathView 0 r := ()

/-- The path of a level below a path. -/
def pathCons {L : ℕ} {r : Fin (L + 1) → ℕ} (k : ℕ) (cts : Fin (r 0) → ℕ × ℕ × ℕ)
    (rest : PathView L (fun i => r i.succ)) : PathView (L + 1) r :=
  ((k, cts), rest)

/-- A recursion on `L` behind a structure binder `deps`, with the recursive call first in the
bind and the fold `fold` of a compound node `nodeIdeal deps` per level. -/
noncomputable def pathView (deps : Deps) (nodeKey : Bool → ℕ) :
    (L : ℕ) → (r : Fin L → ℕ) → SPComp (PathView L r)
  | 0, r => SPComp.pure (pathNil r)
  | L + 1, r => (pathView deps nodeKey L (fun i => r i.succ)).bind fun rest =>
      (fold (nodeIdeal deps) (r 0)).bind fun cts =>
        (SPComp.sample Bool).bind fun ns =>
          SPComp.pure (pathCons (nodeKey ns) cts rest)

derive_reduction pathView

-- the time premise of `fold.tree.timeBound_timed` at the compound node is bounded in `G_keygen`
derive_time_rec pathView.tree using fun L G_keygen t_r t_rCost t_nodeKeyCost =>
  L * (t_r * (G_keygen + 11) + G_keygen + t_nodeKeyCost + 10 + t_rCost + 4 * L) + 2

/-- A record of functions: an expansion. -/
structure Kdf where
  /-- The expansion. -/
  expand : ℕ → ℕ → ℕ

/-- One real node: two key generations and an encryption under `js`. -/
noncomputable def nodeReal (deps : Deps) (aead : ℕ → ℕ → ℕ) (js : ℕ) : SPComp (ℕ × ℕ × ℕ) :=
  SPComp.bind deps.keygen fun x => SPComp.bind deps.keygen fun y =>
    SPComp.pure (x.2, y.2, aead (x.1 + y.1) js)

/-- The path and secret of a level below a path and secret. -/
def chainCons {L : ℕ} {r : Fin (L + 1) → ℕ} (k : ℕ) (cts : Fin (r 0) → ℕ × ℕ × ℕ)
    (rest : PathView L (fun i => r i.succ) × ℕ) : PathView (L + 1) r × ℕ :=
  (((k, cts), rest.1), rest.2)

/-- A recursion on `L` with the fold of the node `nodeReal deps aead (H.expand ps lbl)` first:
the costed node is a pair whose step cost the caller charges, below a `have` of the value
`H.expand ps lbl`. -/
noncomputable def pathChain (deps : Deps) (H : Kdf) (lbl : ℕ) (aead : ℕ → ℕ → ℕ)
    (nodeKey : ℕ → ℕ) : (L : ℕ) → (r : Fin L → ℕ) → ℕ → SPComp (PathView L r × ℕ)
  | 0, r, ps => SPComp.pure (pathNil r, H.expand ps lbl)
  | L + 1, r, ps =>
      (fold (nodeReal deps aead (H.expand ps lbl)) (r 0)).bind fun cts =>
        (pathChain deps H lbl aead nodeKey L (fun i => r i.succ) (H.expand ps lbl)).bind
          fun rest => SPComp.pure (chainCons (nodeKey (H.expand ps 0)) cts rest)

derive_reduction pathChain

-- the strategies are the functional induction and the induction on the recursion argument `L`
-- (`x7`), the structure binders `deps` (`x0`) and `H` (`x1`) generalized
/-- * induction x7 generalizing x0 x1 x2 x3 x4 x5 x6 x10 -/
#guard_msgs (substring := true) in
derive_time_rec pathChain.tree using fun L => L + 1

-- the step cost of the costed node, a pair below a `have`, is bounded with its tree
derive_time_rec pathChain.tree using fun L G_keygen t_r t_rCost t_nodeKeyCost t_aeadCost
    t_expandCost =>
  L * (t_r * (2 * G_keygen + t_aeadCost + 10) + 2 * G_keygen + t_aeadCost + 3 * t_expandCost +
    t_nodeKeyCost + 10 + t_rCost + 4 * L) + t_expandCost + 3

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
