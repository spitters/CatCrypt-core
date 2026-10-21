/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveTimed
public import CatCryptCore.Tactics.StdCosts
public import CatCryptCore.Tactics.DeriveTimedStructure
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
`runThen.stepTime_timed_le`. Further tests pin a point-free reduction whose binders come from
a named function type, a `let` and a discarded argument priced once, a recursive data callee
whose cost is derived on demand, a nested field reached through a helper, and a sum over
`Fin n`, a derived cost that takes the cost companion of a field and its call from a
reduction, two projections of one call priced once, and the costed mirrors of a two-stage
adversary structure (a type field, a proof field, two tree fields) and of a structure with
computation fields. The last tests pin the refusals of a recursive callee whose cost needs a class method
on a local instance priced and of an opaque constant.
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

/-! ## A point-free reduction of a named function type -/

/-- An adversary type under a name. -/
abbrev Adv2 (D R : Type) := ℕ → ℕ → OracleAdv D R Bool

/-- One query at `c (i + j)`. -/
def pfBase {D R : Type} (c : ℕ → D) : Adv2 D R := fun i j => .query (c (i + j)) fun _ => .ret true

/-- `pfBase`, point-free: its binders `i j` come from the type `Adv2 D R`. -/
def pfRed {D R : Type} (c : ℕ → D) : Adv2 D R := pfBase c

derive_timed pfRed

example {D R : Type} (c : ℕ → D) (cCost : ℕ → ℕ) (i j : ℕ) :
    (pfRed.timed (R := R) c cCost i j).2.erase = pfRed c i j :=
  pfRed.erase_timed c cCost i j

/-! ## Sharing: a `let` and an argument are priced once -/

/-- `f x` bound once and used three times. -/
def letRed {D R : Type} (f : ℕ → ℕ) (c : ℕ → D) (x : ℕ) : OracleAdv D R ℕ :=
  let y := f x
  .query (c (y + y)) fun _ => .ret y

derive_timed letRed

example {D R : Type} (f : ℕ → ℕ) (fCost : ℕ → ℕ) (c : ℕ → D) (cCost : ℕ → ℕ) (x : ℕ) :
    (letRed.timed (R := R) f fCost c cCost x).1 = 1 + fCost x + (1 + (cCost (f x + f x) + 1)) :=
  rfl

/-- The first argument; the second is discarded. -/
def discard (a _b : ℕ) : ℕ := a

/-- A call whose discarded argument `f x` is still evaluated. -/
def discRed {D R : Type} (f : ℕ → ℕ) (x : ℕ) : OracleAdv D R ℕ := .ret (discard x (f x))

derive_timed discRed

example {D R : Type} (f : ℕ → ℕ) (fCost : ℕ → ℕ) (x : ℕ) :
    (discRed.timed (D := D) (R := R) f fCost x).1 = 2 + fCost x :=
  rfl

/-! ## A recursive data callee without a registered cost -/

/-- A recursion over `ℕ`. -/
def countDown : ℕ → ℕ
  | 0 => 0
  | n + 1 => countDown n

/-- A call of `countDown`, whose cost `countDown.timedCost` is derived on demand. -/
def recRed {D R : Type} (n : ℕ) : OracleAdv D R ℕ := .ret (countDown n)

derive_timed recRed

example {D R : Type} (n : ℕ) :
    (recRed.timed (D := D) (R := R) n).1 = 1 + countDown.timedCost n :=
  rfl

/-! ## Field paths -/

/-- A structure with one primitive. -/
structure Inner where
  f : ℕ → ℕ

/-- A kit holding an `Inner`. -/
structure Kit where
  inner : Inner

/-- The nested field `k.inner.f`, reached through a helper. -/
def useKit (k : Kit) (x : ℕ) : ℕ := k.inner.f x

/-- A call of the helper. -/
def kitRed {D R : Type} (k : Kit) (x : ℕ) : OracleAdv D R ℕ := .ret (useKit k x)

derive_timed kitRed

example {D R : Type} (k : Kit) (x : ℕ) (fCost : ℕ → ℕ) :
    (kitRed.timed (D := D) (R := R) k x fCost).2.erase = kitRed k x :=
  kitRed.erase_timed k x fCost

/-! ## A sum over `Fin n` -/

/-- `∑ i : Fin n, f i` as the answer. -/
def sumRed {D R : Type} (n : ℕ) (f : Fin n → ℕ) : OracleAdv D R ℕ :=
  .ret (∑ i : Fin n, f i)

derive_timed sumRed

example {D R : Type} (n : ℕ) (f : Fin n → ℕ) (fCost : Fin n → ℕ) :
    (sumRed.timed (D := D) (R := R) n f fCost).2.erase = sumRed n f :=
  sumRed.erase_timed n f fCost

/-! ## Field companions of a derived cost; shared projections -/

/-- A kit with a hash and a constant. -/
structure HKit (W : Type) where
  hash : W → W → W
  zero : W

/-- Hash a list with the field `kit.hash`. -/
def hashList {W : Type} (kit : HKit W) : List W → W
  | [] => kit.zero
  | x :: xs => kit.hash x (hashList kit xs)

derive_cost hashList

/-- The derived cost takes the cost companion of the field `kit.hash` after the arguments. -/
noncomputable example {W : Type} (kit : HKit W) (xs : List W) (hashCost : W → W → ℕ) : ℕ :=
  hashList.timedCost kit xs hashCost

/-- A reduction that calls the adversary on the hash of a concatenation: the call of
`hashList` passes the companion `hashCost` of the reduction. -/
noncomputable def hashRed {W : Type} (kit : HKit W) (A : W → SPTree Bool) (xs : List W) :
    SPTree Bool := A (hashList kit (xs ++ xs))

derive_timed hashRed

example {W : Type} (kit : HKit W) (A : W → SPTree.Timed Bool) (ACost : W → ℕ) (xs : List W)
    (hashCost : W → W → ℕ) :
    hashRed.timed kit A ACost xs hashCost =
      (1 + (ACost (hashList kit (xs ++ xs)) +
        (1 + (hashList.timedCost kit (xs ++ xs) hashCost + (1 + List.append.timedCost xs xs)))),
        A (hashList kit (xs ++ xs))) := rfl

/-- A pair computed with the hash. -/
def pairOf {W : Type} (kit : HKit W) (x : W) : W × W := (kit.hash x x, kit.zero)

/-- The first of two values. -/
def firstOf {W : Type} (a _b : W) : W := a

/-- The projections of `pairOf kit x` share one evaluation: `hashCost x x` is charged once. -/
noncomputable def pairRed {W : Type} (kit : HKit W) (A : W → SPTree Bool) (x : W) :
    SPTree Bool := A (firstOf (pairOf kit x).1 (pairOf kit x).2)

derive_timed pairRed

example {W : Type} (kit : HKit W) (A : W → SPTree.Timed Bool) (ACost : W → ℕ) (x : W)
    (hashCost : W → W → ℕ) :
    (pairRed.timed kit A ACost x hashCost).1 =
      1 + (ACost (firstOf (pairOf kit x).1 (pairOf kit x).2) + (3 + hashCost x x)) := rfl

/-! ## Costed mirrors of structures -/

/-- A two-stage adversary: a state type, a proof field and two tree fields. -/
structure TwoStage (W : Type) where
  St : Type
  inh : Nonempty St
  choose : W → SPTree (St × W)
  guess : St → W → SPTree Bool

derive_timed_structure TwoStage

example {W : Type} (A' : TwoStage.Timed W) (A : TwoStage W) :
    A'.Erases A ↔ ∃ inh : Nonempty A'.St, A = ⟨A'.St, inh, fun w => (A'.choose w).erase,
      fun s w => (A'.guess s w).erase⟩ := Iff.rfl

example {W : Type} (A' : TwoStage.Timed W) (T a T' a' : ℕ) :
    A'.TimeBound T a T' a' ↔ (∀ w, (A'.choose w).time ≤ T) ∧ (∀ w, A'.chooseCost w ≤ a) ∧
      (∀ s w, (A'.guess s w).time ≤ T') ∧ ∀ s w, A'.guessCost s w ≤ a' := Iff.rfl

/-- An adversary with computation fields. -/
structure CompAdv (W : Type) where
  run : W → SPComp Bool
  init : SPComp W

derive_timed_structure CompAdv

example {W : Type} (A' : CompAdv.Timed W) (A : CompAdv W) :
    A'.Erases A ↔ A = ⟨fun w => (A'.run w).erase.compile, A'.init.erase.compile⟩ := Iff.rfl

/-! ## Class methods on a local instance -/

/-- Membership by `BEq.beq` on a local instance. -/
def memB {α : Type} [BEq α] (a : α) : List α → Bool
  | [] => false
  | b :: l => a == b || memB a l

/-- A call of `memB`: `BEq.beq` on the local instance is priced by the companion `beqCost`. -/
def memRed {D R α : Type} [BEq α] (a : α) (l : List α) : OracleAdv D R Bool := .ret (memB a l)

derive_timed memRed

example {D R α : Type} [BEq α] (a : α) (l : List α) (beqCost : α → α → ℕ) :
    (memRed.timed (D := D) (R := R) a l beqCost).2.erase = memRed a l :=
  memRed.erase_timed a l beqCost

example {D R α : Type} [BEq α] (a : α) (l : List α) (beqCost : α → α → ℕ) :
    (memRed.timed (D := D) (R := R) a l beqCost).1 = 1 + memB.timedCost a l beqCost := by
  simp only [memRed.timed]

/-! ## Refusals -/

/-- An opaque constant. -/
opaque opq : ℕ → ℕ

/-- A call of the opaque constant. -/
def opqRed {D R : Type} (n : ℕ) : OracleAdv D R ℕ := .ret (opq n)

/--
error: derive_timed: needs a registered primitive: `CatCrypt.Tactics.DeriveTimedTest.opq` has
no definition to price and no registered cost `CatCrypt.Tactics.DeriveTimedTest.opq.timedCost`
-/
#guard_msgs (whitespace := lax) in
derive_timed opqRed

end CatCrypt.Tactics.DeriveTimedTest
