/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveTimed
import CatCryptCore.Core.SPTree

/-!
# Tests for `derive_timed`

Reductions over the oracle-tree combinators of `CatCryptCore.Crypto.OracleSimulation`, in
the shapes of the hand-instrumented reductions of CTR$ (a recursion over the message blocks,
a uniform IV, a simulation), FF1 (a recursion over the rounds with a continuation) and
RSA-KEM (a renaming of queries, a simulation by a lazily sampled table). For each, the command
defines the costed form and proves the erasure theorem, whose statement is pinned by an
`example`. `blocks.timeBound_timed` bounds the time of the derived costed form of the block
recursion by `ms.length * (a + s + 7) + t + 2`, the shape `ms.length * (1 + c)` of the
hand-instrumented bound. The computation-tree tests derive costed forms of `SPTree`-valued
definitions over the `sample`, `get` and `set` nodes, `SPTree.map` and `SPTree.bind`, a
recursion over `ℕ`, and a tree argument with a continuation, whose derived time is bounded by
`runThen.stepTime_timed_le`. The last test pins the refusal of a recursive data function without a
registered cost.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveTimedTest

open CatCrypt.Crypto

/-! ## A recursion over a list with a continuation -/

/-- Query `c i, c (i + 1), …` once per block of `ms`, combine each answer with its block by
`step`, and return `g` of the combined blocks. -/
def blocks {D B X : Type} (c : ℕ → D) (step : B → B → B) (g : List B → X) :
    ℕ → List B → OracleAdv D B X
  | _, [] => .ret (g [])
  | i, m :: ms => .query (c i) fun u => blocks c step (fun cs => g (step m u :: cs)) (i + 1) ms

derive_timed blocks

example {D B X : Type} (c : ℕ → D) (cCost : ℕ → ℕ) (step : B → B → B) (stepCost : B → B → ℕ)
    (g : List B → X) (gCost : List B → ℕ) (i : ℕ) (ms : List B) :
    (blocks.timed c cCost step stepCost g gCost i ms).2.erase = blocks c step g i ms :=
  blocks.erase_timed c cCost step stepCost g gCost i ms

/-- With the costs of `c`, `step` and `g` bounded by `a`, `s` and `t`, the derived costed form
of `blocks` has time at most `ms.length * (a + s + 7) + t + 2`. -/
theorem blocks.timeBound_timed {D B X : Type} (c : ℕ → D) (cCost : ℕ → ℕ) (step : B → B → B)
    (stepCost : B → B → ℕ) {a s : ℕ} (hc : ∀ i, cCost i ≤ a) (hs : ∀ m u, stepCost m u ≤ s)
    (ms : List B) : ∀ (g : List B → X) (gCost : List B → ℕ) (t i : ℕ), (∀ cs, gCost cs ≤ t) →
      OracleAdv.Timed.StepTimeBound (blocks.timed c cCost step stepCost g gCost i ms)
        (ms.length * (a + s + 7) + t + 2) := by
  induction ms with
  | nil =>
    intro g gCost t i hg
    have := hg []
    exact ⟨by simp only [blocks.timed, OracleAdv.Timed.delay]; omega, trivial⟩
  | cons m ms ih =>
    intro g gCost t i hg
    have hci := hc i
    have hrec := fun u => ih (fun cs => g (step m u :: cs))
      (fun cs => 1 + (gCost (step m u :: cs) + (1 + stepCost m u))) (t + s + 2) (i + 1)
      (fun cs => by have := hg (step m u :: cs); have := hs m u; omega)
    have e : (ms.length + 1) * (a + s + 7) = ms.length * (a + s + 7) + (a + s + 7) :=
      Nat.succ_mul _ _
    simp only [blocks.timed, OracleAdv.Timed.delay, OracleAdv.Timed.StepTimeBound,
      OracleAdv.Timed.timeBound_query_iff, List.length_cons, e] at hrec ⊢
    refine ⟨by omega, by omega, fun u => ⟨by have := (hrec u).1; omega, ?_⟩⟩
    exact (hrec u).2.mono (by have := (hrec u).1; omega)

/-! ## A recursion over `ℕ` with a continuation argument -/

/-- `n` Feistel rounds from round `j` on the state `st`, one query per round, then the
continuation `k` on the final state. -/
def feistel {W α : Type} (step : W → W → W) :
    ℕ → ℕ → W × W → (W × W → OracleAdv (ℕ × W) W α) → OracleAdv (ℕ × W) W α
  | _, 0, st, k => k st
  | j, n + 1, st, k => .query (j, st.2) fun y => feistel step (j + 1) n (st.2, step st.1 y) k

derive_timed feistel

example {W α : Type} (step : W → W → W) (stepCost : W → W → ℕ) (j n : ℕ) (st : W × W)
    (k : W × W → OracleAdv.Timed (ℕ × W) W α) (kCost : W × W → ℕ) :
    (feistel.timed step stepCost j n st k kCost).2.erase =
      feistel step j n st fun s => (k s).erase :=
  feistel.erase_timed step stepCost j n st k kCost

/-- The rounds followed by a sample of the output bit `Dist` of the final state. -/
noncomputable def feistelRed {W : Type} (step : W → W → W) (n : ℕ) (x : W × W)
    (Dist : W × W → PMF Bool) : OracleAdv (ℕ × W) W Bool :=
  feistel step 0 n x fun st => .rand (Dist st) .ret

derive_timed feistelRed

example {W : Type} (step : W → W → W) (stepCost : W → W → ℕ) (n : ℕ) (x : W × W)
    (Dist : W × W → PMF Bool) (DistCost : W × W → ℕ) :
    (feistelRed.timed step stepCost n x Dist DistCost).2.erase = feistelRed step n x Dist :=
  feistelRed.erase_timed step stepCost n x Dist DistCost

/-! ## Sampling, simulation, sequencing and renaming -/

/-- A uniform IV `s`, then the blocks of `M` against the counters `ctr s`. -/
noncomputable def ivBlocks {D B N : Type} [Fintype N] [Nonempty N] (step : B → B → B)
    (ctr : N → ℕ → D) (M : List B) : OracleAdv D B (N × List B) :=
  .rand (PMF.uniformOfFintype N) fun s => blocks (ctr s) step (fun cs => (s, cs)) 0 M

derive_timed ivBlocks

/-- The adversary `A` with each query `M` answered by `ivBlocks step ctr M`. -/
noncomputable def ivRed {D B N : Type} [Fintype N] [Nonempty N] (step : B → B → B)
    (ctr : N → ℕ → D) (A : OracleAdv (List B) (N × List B) Bool) :
    OracleAdv D B (Bool × Unit) :=
  OracleAdv.simulate (fun _ M => (ivBlocks step ctr M).bind fun r => .ret (r, ())) A ()

derive_timed ivRed

example {D B N : Type} [Fintype N] [Nonempty N] (step : B → B → B) (stepCost : B → B → ℕ)
    (ctr : N → ℕ → D) (ctrCost : N → ℕ → ℕ) (A : OracleAdv.Timed (List B) (N × List B) Bool) :
    (ivRed.timed step stepCost ctr ctrCost A).2.erase = ivRed step ctr A.erase :=
  ivRed.erase_timed step stepCost ctr ctrCost A

/-- The adversary `A` with each query `d` asked as `Sum.inl (f d)`. -/
def liftRed {D R α : Type} (f : D → D × D) (A : OracleAdv D R α) :
    OracleAdv (D × D ⊕ D) R α :=
  OracleAdv.mapQuery (fun d => Sum.inl (f d)) A

derive_timed liftRed

example {D R α : Type} (f : D → D × D) (fCost : D → ℕ) (A : OracleAdv.Timed D R α) :
    (liftRed.timed f fCost A).2.erase = liftRed f A.erase :=
  liftRed.erase_timed f fCost A

/-! ## Matches, conditions and registered primitives -/

/-- The value at the key `q` of an association list. -/
def lookup {K : Type} : List (ℕ × K) → ℕ → Option K
  | [], _ => none
  | (a, k) :: t, q => if a = q then some k else lookup t q

timed_cost lookup := fun {K : Type} (l : List (ℕ × K)) (_ : ℕ) => l.length

/-- Answer `q` from the table, querying the oracle and recording the answer on a miss. -/
noncomputable def lazyAnswer {K : Type} [Nonempty K] (tbl : List (ℕ × K)) (q : ℕ) :
    OracleAdv ℕ K (K × List (ℕ × K)) :=
  match lookup tbl q with
  | some k => .ret (k, tbl)
  | none =>
    if q = 0 then .ret (Classical.arbitrary K, tbl)
    else .query q fun k => .ret (k, (q, k) :: tbl)

derive_timed lazyAnswer

example {K : Type} [Nonempty K] (tbl : List (ℕ × K)) (q : ℕ) :
    (lazyAnswer.timed tbl q).2.erase = lazyAnswer tbl q :=
  lazyAnswer.erase_timed tbl q

/-- The adversary `A` with its queries answered by the table, from the empty table. -/
noncomputable def lazyRed {K : Type} [Nonempty K] (A : OracleAdv ℕ K Bool) :
    OracleAdv ℕ K (Bool × List (ℕ × K)) :=
  OracleAdv.simulate lazyAnswer A []

derive_timed lazyRed

example {K : Type} [Nonempty K] (A : OracleAdv.Timed ℕ K Bool) :
    (lazyRed.timed A).2.erase = lazyRed A.erase :=
  lazyRed.erase_timed A

/-! ## Computation trees -/

open CatCrypt.Core

/-- One uniform sample over `Fin (2 ^ n)`, then `true`. -/
noncomputable def wideSample (n : ℕ) : SPTree Bool :=
  .sample (Fin (2 ^ n)) inferInstance ⟨⟨0, Nat.two_pow_pos n⟩⟩ fun _ => .ret true

derive_timed wideSample

example (n : ℕ) : (wideSample.timed n).2.erase = wideSample n := wideSample.erase_timed n

/-- Read the location `l`, write `upd` of the value back, and return the old value. -/
def readUpdate (l : Location) (upd : l.ty → l.ty) : SPTree l.ty :=
  .get l fun v => .set l (upd v) (.ret v)

derive_timed readUpdate

example (l : Location) (upd : l.ty → l.ty) (updCost : l.ty → ℕ) :
    (readUpdate.timed l upd updCost).2.erase = readUpdate l upd :=
  readUpdate.erase_timed l upd updCost

/-- A uniform sample of `β`, mapped by `f` and continued with `k`. -/
noncomputable def sampleMapBind {β γ δ : Type} [Fintype β] [Nonempty β] (f : β → γ)
    (k : γ → SPTree δ) : SPTree δ :=
  ((SPTree.sample β inferInstance inferInstance fun b => .ret b).map f).bind k

derive_timed sampleMapBind

example {β γ δ : Type} [Fintype β] [Nonempty β] (f : β → γ) (fCost : β → ℕ)
    (k : γ → SPTree.Timed δ) (kCost : γ → ℕ) :
    (sampleMapBind.timed f fCost k kCost).2.erase =
      sampleMapBind f fun c => (k c).erase :=
  sampleMapBind.erase_timed f fCost k kCost

/-- `n` uniform samples of `β`, as a list. -/
noncomputable def samples (β : Type) [Fintype β] [Nonempty β] : ℕ → SPTree (List β)
  | 0 => .ret []
  | n + 1 => .sample β inferInstance inferInstance fun b => (samples β n).map (b :: ·)

derive_timed samples

example (β : Type) [Fintype β] [Nonempty β] (n : ℕ) :
    (samples.timed β n).2.erase = samples β n :=
  samples.erase_timed β n

/-- The tree `A` followed by `k` on its result. -/
def runThen {α β : Type} (A : SPTree α) (k : α → SPTree β) : SPTree β := A.bind k

derive_timed runThen

example {α β : Type} (A : SPTree.Timed α) (k : α → SPTree.Timed β) (kCost : α → ℕ) :
    (runThen.timed A k kCost).2.erase = runThen A.erase fun a => (k a).erase :=
  runThen.erase_timed A k kCost

/-- With the costs of computing `k a` bounded by `c` and the times of the trees `k a` by `t`,
the derived costed form of `runThen` has time at most the time of `A` plus `1 + c + t`. -/
theorem runThen.stepTime_timed_le {α β : Type} (A : SPTree.Timed α) (k : α → SPTree.Timed β)
    (kCost : α → ℕ) {c t : ℕ} (hc : ∀ a, kCost a ≤ c) (hk : ∀ a, (k a).time ≤ t) :
    SPTree.Timed.stepTime (runThen.timed A k kCost) ≤ A.time + (1 + c + t) := by
  refine SPTree.Timed.stepTime_bind_le A _ _ fun a => ?_
  have := hc a
  have := hk a
  simp only [SPTree.Timed.stepTime]
  omega

/-! ## A refusal -/

/-- `lazyAnswer` over the library function `List.lookup`, which has no registered cost. -/
def lazyAnswerList {K : Type} (tbl : List (ℕ × K)) (q : ℕ) : OracleAdv ℕ K (K × List (ℕ × K)) :=
  match tbl.lookup q with
  | some k => .ret (k, tbl)
  | none => .query q fun k => .ret (k, (q, k) :: tbl)

/--
error: derive_timed: needs a registered primitive: `List.lookup` is recursive and has no
registered cost `List.lookup.timedCost`
-/
#guard_msgs (whitespace := lax) in
derive_timed lazyAnswerList

end CatCrypt.Tactics.DeriveTimedTest
