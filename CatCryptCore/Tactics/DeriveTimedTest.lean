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
reduction, two projections of one call priced once, the costed mirrors of a two-stage
adversary structure (a type field, a proof field, two tree fields), of a structure with
computation fields (one without arguments, whose cost companion is a number) and of a
two-stage oracle adversary whose proof field bounds a tree field, and a field of a computed
structure `(kit.aead iv).enc` priced by a companion indexed by the nonce. A recursion over the
adversary (`logRed`, the shape of the PRF-to-MAC reduction) is derived as a recursion over its
costed tree, and `logRed.timeBound_timed` bounds its time through
`OracleAdv.Timed.timeBound_fold`. The last tests pin
the pricing of a class method on a local instance by a companion (and of an algebraic
operation on a local instance at one unit) and the refusal of an
opaque constant. The costed-closure tests derive a state table updated by `Function.update`
and its simulation, closures in results, a closure result consumed by a continuation, the
shape of the multi-key PRF hybrid reduction and a closure in a computation-tree result.
The final tests pin lets priced once (a `let` under the first binder, a `have` of a
constructor, a let-bound structure value, a let of a field path), a well-founded recursion
through `if`, and the refusal of an operation on a quotient without a registered cost.
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
  .rand (PMF.uniformFintype N) fun s => blocks (ctr s) step (fun cs => (s, cs)) 0 M

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

example {W : Type} (A' : TwoStage.Timed W) (T T' : ℕ) :
    A'.TimeBound T T' ↔ (∀ w, SPTree.Timed.stepTime (A'.chooseCost w, A'.choose w) ≤ T) ∧
      ∀ s w, SPTree.Timed.stepTime (A'.guessCost s w, A'.guess s w) ≤ T' := Iff.rfl

/-- An adversary with computation fields. -/
structure CompAdv (W : Type) where
  run : W → SPComp Bool
  init : SPComp W

derive_timed_structure CompAdv

example {W : Type} (A' : CompAdv.Timed W) (A : CompAdv W) :
    A'.Erases A ↔ A = ⟨fun w => (A'.run w).erase.compile, A'.init.erase.compile⟩ := Iff.rfl

/-- A computation field without arguments has a cost companion that is a number. -/
example {W : Type} (A' : CompAdv.Timed W) (T T' : ℕ) :
    A'.TimeBound T T' ↔ (∀ w, SPTree.Timed.stepTime (A'.runCost w, A'.run w) ≤ T) ∧
      SPTree.Timed.stepTime (A'.initCost, A'.init) ≤ T' := Iff.rfl

/-- A two-stage oracle adversary whose proof field bounds a tree field. -/
structure BoundedStage (W : Type) : Type 1 where
  St : Type
  choose : W → OracleAdv W W (W × St)
  guess : St → W → OracleAdv W W Bool
  bound : ∀ w, (choose w).IsQueryBoundBy (fun _ => 1) 1

derive_timed_structure BoundedStage

example {W : Type} (A' : BoundedStage.Timed W) (A : BoundedStage W) :
    A'.Erases A ↔ ∃ bound : ∀ w, (A'.choose w).erase.IsQueryBoundBy (fun _ => 1) 1,
      A = ⟨A'.St, fun w => (A'.choose w).erase, fun s w => (A'.guess s w).erase, bound⟩ :=
  Iff.rfl

/-! ## Fields of a computed structure -/

/-- An AEAD: encryption under a key. -/
structure AeadT (W : Type) where
  enc : W → W → W

/-- A kit computing an AEAD from a nonce. -/
structure AeadKit (W : Type) where
  aead : W → AeadT W

/-- A field of the computed structure `kit.aead iv`. -/
def aeadRed {D R W : Type} (kit : AeadKit W) (iv k m : W) : OracleAdv D R W :=
  .ret ((kit.aead iv).enc k m)

derive_timed aeadRed

/-- The field `enc` of `kit.aead iv` is priced by a companion indexed by the nonce, the key and
the message; computing `kit.aead iv` is priced by the companion of `aead`. -/
example {D R W : Type} (kit : AeadKit W) (iv k m : W) (aeadCost : W → ℕ)
    (aead_encCost : W → W → W → ℕ) :
    (aeadRed.timed (D := D) (R := R) kit iv k m aeadCost aead_encCost).1 =
      1 + (aead_encCost iv k m + (1 + aeadCost iv)) := rfl

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

/-- Methods of an abstract group (a local instance): one unit each. -/
noncomputable def o6Grp {G : Type} [AddCommGroup G] (g h : G) (n : ℕ) : OracleAdv ℕ ℕ G :=
  .ret (g + h - n • g)

derive_timed o6Grp

example {G : Type} [AddCommGroup G] (g h : G) (n : ℕ) : (o6Grp.timed g h n).1 = 3 := rfl

/-- A primitive interface of a protocol, given as a class (the `Dependencies` classes). -/
class O6Deps (W : Type) where
  /-- An encryption primitive. -/
  aead_enc : W → W → W

/-- A primitive of the interface keeps its cost companion; the group operation costs one
unit. -/
noncomputable def o6DepsRed {W : Type} [O6Deps W] [AddCommGroup W] (k m : W) :
    OracleAdv ℕ ℕ W :=
  .ret (O6Deps.aead_enc k m + k)

derive_timed o6DepsRed

example {W : Type} [O6Deps W] [AddCommGroup W] (k m : W) (aead_encCost : W → W → ℕ) :
    (o6DepsRed.timed k m aead_encCost).1 = 2 + aead_encCost k m := rfl

/-! ## A recursion over the adversary -/

/-- The shape of the PRF-to-MAC reduction: run a forger, forward its queries and record them in
`log`, then check its forgery `(m, t)` by one query when `m` is not in `log`. -/
def logRed {D T : Type} [DecidableEq D] [BEq T] :
    OracleAdv D T (D × T) → List D → OracleAdv D T Bool
  | .ret r, log => if r.1 ∈ log then .ret false else .query r.1 fun t' => .ret (r.2 == t')
  | .rand p k, log => .rand p fun b => logRed (k b) log
  | .query d k, log => .query d fun t' => logRed (k t') (d :: log)

derive_timed logRed

example {D T : Type} [DecidableEq D] [BEq T] (A : OracleAdv.Timed D T (D × T)) (log : List D)
    (beqCost : T → T → ℕ) : (logRed.timed A log beqCost).2.erase = logRed A.erase log :=
  logRed.erase_timed A log beqCost

/-- The derived costed form of a recursion over the adversary is a handler of its nodes: a
forger of time `n` gives time `4 * n + 4 + e` when a comparison of tags costs at most `e`. -/
theorem logRed.timeBound_timed {D T : Type} [DecidableEq D] [BEq T] (beqCost : T → T → ℕ)
    {e : ℕ} (he : ∀ x y, beqCost x y ≤ e) {A : OracleAdv.Timed D T (D × T)} {n : ℕ}
    (hA : A.TimeBound n) (log : List D) :
    OracleAdv.Timed.StepTimeBound (logRed.timed A log beqCost) ((1 + 3) * n + (4 + e)) := by
  refine OracleAdv.Timed.timeBound_fold (fun A s => logRed.timed A s beqCost) ?_ ?_ ?_ hA log
  · intro a s
    simp only [logRed.timed, OracleAdv.Timed.delay]
    split <;> simp_all [OracleAdv.Timed.StepTimeBound, OracleAdv.Timed.TimeBound]
    · omega
    · exact ⟨by omega, by omega, fun y => by have := he a.2 y; omega⟩
  · intro γ p c k s M hM0 hM hk
    rw [logRed.timed]
    simp only [OracleAdv.Timed.StepTimeBound, OracleAdv.Timed.TimeBound]
    refine ⟨by omega, by omega, fun b => ?_⟩
    have h1 := hM b
    have h2 := hk b s
    exact ⟨by have := h2.1; omega, h2.2.mono (by omega)⟩
  · intro d c k s M hM0 hM hk
    rw [logRed.timed]
    simp only [OracleAdv.Timed.StepTimeBound, OracleAdv.Timed.TimeBound]
    refine ⟨by omega, by omega, fun b => ?_⟩
    have h1 := hM b
    have h2 := hk b (d :: s)
    exact ⟨by have := h2.1; omega, h2.2.mono (by omega)⟩

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

/-! ## Costed closures

A state holding a function, updated by `Function.update` (`o6Impl`), its simulation
(`o6Red`, through `OracleAdv.Timed.simulateHat`), closures in a result built from a function
binder, a sampled function and an `if` (`o6Clo`), a closure result consumed by a continuation
(`o6Use`, through `o6Clo.erase_timed_bind`), the shape of `MultiKeyPRF.hybImpl` and
`mkHybRed` (tables and keys stored as functions of a rank, `o6Hyb`, `o6HybRed`), and a closure
in the result of a computation tree (`o6Sp`). -/

/-- A query answered from a table stored as a function, which it updates. -/
noncomputable def o6Impl (s : List ℕ × (ℕ → ℕ)) (q : ℕ) :
    OracleAdv ℕ ℕ (ℕ × (List ℕ × (ℕ → ℕ))) :=
  .ret (s.2 q, (q :: s.1, Function.update s.2 q (s.2 q + 1)))

derive_timed o6Impl

example (s : List ℕ × (ℕ → ℕ) × (ℕ → ℕ)) (q : ℕ) :
    (((o6Impl.timed s q).2.erase.bind fun y => OracleAdv.ret (y.1, y.2.1, y.2.2.1)) =
      o6Impl (s.1, s.2.1) q) := o6Impl.erase_timed s q

/-- The simulation of `o6Impl` from an all-zero table. -/
noncomputable def o6Red (A : OracleAdv ℕ ℕ Bool) : OracleAdv ℕ ℕ Bool :=
  (OracleAdv.simulate o6Impl A ([], fun _ => 0)).bind fun x => .ret x.1

derive_timed o6Red

example (A : OracleAdv.Timed ℕ ℕ Bool) : (o6Red.timed A).2.erase = o6Red A.erase :=
  o6Red.erase_timed A

/-- The time of the simulation of `o6Impl` by the state invariant that the table's companion
is at most `3 i` after `i` queries: query `i` costs at most `4 + 6 i`
(`OracleAdv.Timed.timeBound_simulateHat_inv`). -/
example {A : OracleAdv.Timed ℕ ℕ Bool} {T q : ℕ} (hA : A.TimeBound T)
    (hq : A.erase.IsQueryBound q) :
    OracleAdv.Timed.StepTimeBound
      (OracleAdv.Timed.simulateHat (fun y : List ℕ × (ℕ → ℕ) × (ℕ → ℕ) => (y.1, y.2.1))
        (fun y : List ℕ × (ℕ → ℕ) => (y.1, y.2, fun _ => 0))
        (fun s q => OracleAdv.Timed.delay 1 (o6Impl.timed s q)) A ([], fun _ => 0, fun _ => 0))
      (T + ∑ j ∈ Finset.range q, (4 + 6 * (0 + j))) := by
  refine OracleAdv.Timed.timeBound_simulateHat_inv _ _ _
    (fun i s => ∀ x, s.2.2 x ≤ 3 * i) (fun i => 4 + 6 * i) (fun i s d hs => ?_) hA hq 0 _
    (fun _ => Nat.zero_le _)
  have h := hs d
  refine ⟨⟨?_, trivial⟩, fun x => ?_⟩
  · simp only [o6Impl.timed, OracleAdv.Timed.delay]; omega
  · dsimp only
    split
    · omega
    · have := hs x; omega

/-- Closures in a result: one built from a function binder and a sampled function, one whose
values are an `if` between a pair holding a closure and a pair holding the binder. -/
noncomputable def o6Clo (ctxs : Fin 4 → ℕ) (h : Fin 4) :
    OracleAdv ℕ ℕ ((Fin 4 → ℕ) × (Fin 4 → ℕ × (Fin 4 → ℕ))) :=
  .rand (PMF.uniformFintype (Fin 4 → Fin 3)) fun f =>
    .ret (fun i => ctxs i + (f i : ℕ),
      fun i => if i = h then (ctxs i, fun j => (f j : ℕ)) else (0, ctxs))

derive_timed o6Clo

example (ctxs ctxsCost : Fin 4 → ℕ) (h : Fin 4) :
    ((o6Clo.timed ctxs ctxsCost h).2.erase.bind fun y =>
      OracleAdv.ret (y.1.1, fun a => ((y.2.1 a).1, (y.2.1 a).2.1))) = o6Clo ctxs h :=
  o6Clo.erase_timed ctxs ctxsCost h

/-- A closure result applied by the continuation. -/
noncomputable def o6Use (ctxs : Fin 4 → ℕ) (h : Fin 4) : OracleAdv ℕ ℕ ℕ :=
  (o6Clo ctxs h).bind fun r => .ret (r.1 h + (r.2 h).1)

derive_timed o6Use

example (ctxs ctxsCost : Fin 4 → ℕ) (h : Fin 4) :
    (o6Use.timed ctxs ctxsCost h).2.erase = o6Use ctxs h := o6Use.erase_timed ctxs ctxsCost h

/-- The shape of `MultiKeyPRF.hybImpl`: tables and keys stored as functions of a rank. -/
noncomputable def o6Hyb (F : ℕ → ℕ → Fin 3) (j : ℕ)
    (s : List ℕ × (ℕ → List (ℕ × Fin 3)) × (ℕ → Option ℕ)) (q : ℕ × ℕ) :
    OracleAdv ℕ (Fin 3) (Fin 3 × (List ℕ × (ℕ → List (ℕ × Fin 3)) × (ℕ → Option ℕ))) :=
  if s.1.length < j then
    match List.lookup q.2 (s.2.1 q.1) with
    | some v => .ret (v, (q.1 :: s.1, s.2.1, s.2.2))
    | none => .rand (PMF.uniformFintype (Fin 3)) fun v =>
        .ret (v, (q.1 :: s.1, Function.update s.2.1 q.1 ((q.2, v) :: s.2.1 q.1), s.2.2))
  else if s.1.length = j then
    .query q.2 fun v => .ret (v, (q.1 :: s.1, s.2.1, s.2.2))
  else
    match s.2.2 q.1 with
    | some k => .ret (F k q.2, (q.1 :: s.1, s.2.1, s.2.2))
    | none => .rand (PMF.uniformFintype (Fin 3)) fun k =>
        .ret (F k q.2, (q.1 :: s.1, s.2.1, Function.update s.2.2 q.1 (some (k : ℕ))))

/-- The shape of `MultiKeyPRF.mkHybRed`. -/
noncomputable def o6HybRed (F : ℕ → ℕ → Fin 3) (A : OracleAdv (ℕ × ℕ) (Fin 3) Bool)
    (j : ℕ) : OracleAdv ℕ (Fin 3) Bool :=
  (OracleAdv.simulate (o6Hyb F j) A ([], fun _ => [], fun _ => none)).bind fun x => .ret x.1

derive_timed o6HybRed

example (F : ℕ → ℕ → Fin 3) (FCost : ℕ → ℕ → ℕ) (A : OracleAdv.Timed (ℕ × ℕ) (Fin 3) Bool)
    (j : ℕ) : (o6HybRed.timed F FCost A j).2.erase = o6HybRed F A.erase j :=
  o6HybRed.erase_timed F FCost A j

open CatCrypt.Core in
/-- A closure in the result of a computation tree. -/
noncomputable def o6Sp (h : Fin 4) : SPTree ((Fin 4 → ℕ) × ℕ) :=
  .ret (fun i => if i = h then 1 else 0, 3)

derive_timed o6Sp

example (h : Fin 4) :
    ((o6Sp.timed h).2.erase.bind fun y => CatCrypt.Core.SPTree.ret (y.1.1, y.2)) = o6Sp h :=
  o6Sp.erase_timed h

/-! A tree binder whose results hold functions (the shapes of `copeRedChoose`,
`iknpCRRedOf`): its results are lifted to costed closures of companion zero, and a tree
argument holding costed closures is erased for a callee whose binder takes the plain type. -/

open CatCrypt.Core in
/-- A tree binder holding a function, whose result is passed on in a closure. -/
noncomputable def o6Cope (c : SPTree ((Fin 2 → Bool) × ℕ)) :
    SPTree ((Fin 2 → Fin 3 × Bool) × (Fin 2 → Bool)) :=
  c.bind fun i => .sample (Fin 2 → Fin 3) inferInstance inferInstance fun t =>
    .ret (fun j => (t j, i.1 j), i.1)

derive_timed o6Cope

example (c : CatCrypt.Core.SPTree.Timed ((Fin 2 → Bool) × ℕ)) :
    ((o6Cope.timed c).2.erase.bind fun y => CatCrypt.Core.SPTree.ret (y.1.1, y.2.1)) =
      o6Cope c.erase := o6Cope.erase_timed c

open CatCrypt.Core in
/-- A tree binder holding a function, applied by the continuation. -/
noncomputable def o6Iknp (c : SPTree ((Fin 2 → Bool) × ℕ)) (g : Bool → SPTree Bool) :
    SPTree Bool :=
  c.bind fun i => g (i.1 0)

derive_timed o6Iknp

open CatCrypt.Core in
/-- A call of `o6Iknp` on a tree whose results hold a closure. -/
noncomputable def o6Pass (c : SPTree ((Fin 2 → Bool) × ℕ)) : SPTree Bool :=
  o6Iknp (c.bind fun i => .ret (fun j => !i.1 j, i.2)) fun b => .ret b

derive_timed o6Pass

open CatCrypt.Core in
/-- A partial application of a function parameter whose results hold functions (the shape of
`iknpRedChooseOf`): a closure priced by the parameter's companion, its results tables. -/
noncomputable def o6Bin
    (bIn : (Fin 2 → Bool) → Bool → Fin 2 → (Fin 2 → Bool) × (Fin 2 → Bool))
    (c : SPTree ((Fin 2 → Bool) × Bool)) :
    SPTree ((Fin 2 → (Fin 2 → Bool) × (Fin 2 → Bool)) × Bool) :=
  c.bind fun i => .ret (bIn i.1 i.2, i.2)

derive_timed o6Bin

open CatCrypt.Core in
/-- Addition of an abstract group inside a closure (the shape of `copeRedChoose`): one unit,
as a call of the abstract interface. -/
noncomputable def o6Loc {G : Type} [AddCommGroup G] (g : G) (c : SPTree (Fin 2 → G)) :
    SPTree (Fin 2 → G) :=
  c.bind fun f => .ret (fun j => f j + g)

derive_timed o6Loc

open CatCrypt.Core in
/-- Arithmetic modulo `p` inside a closure: one unit per operation. -/
noncomputable def o6Zm (p : ℕ) (a : ZMod p) : SPTree (Fin 2 → ZMod p) :=
  .ret (fun _ => a * a + a)

derive_timed o6Zm

/-- The closure of `o6Zm` has companion `2`: a multiplication and an addition. -/
example (p : ℕ) (a : ZMod p) :
    o6Zm.timed p a = (0, CatCrypt.Core.SPTree.Timed.ret (fun _ => a * a + a, fun _ => 2)) :=
  rfl

/-- A constant without arguments (the shape of the EDHOC labels `Label.mac_2`), priced by
unfolding. -/
def o6Lbl : ℕ := 3

open CatCrypt.Core in
/-- A call with a constant argument: derived without a panic of the unit-operation tests. -/
noncomputable def o6Nullary (A : ℕ → SPTree Bool) : SPTree Bool := A (o6Lbl + 1)

derive_timed o6Nullary

example (A : ℕ → CatCrypt.Core.SPTree.Timed Bool) (ACost : ℕ → ℕ) :
    o6Nullary.timed A ACost = (1 + (ACost (o6Lbl + 1) + 2), A (o6Lbl + 1)) := rfl

/-- A two-stage adversary whose stages exchange a function (the shape of the base-OT
adversaries of IKNP). -/
structure O6Adv (S : Type) where
  /-- The first stage. -/
  choose : CatCrypt.Core.SPTree ((Fin 2 → Bool) × S)
  /-- The second stage, on the state of the first. -/
  guess : (Fin 2 → Bool) × S → CatCrypt.Core.SPTree Bool

/-- A structure-valued reduction, whose field trees below have the plain interface that the
costed mirror of `O6Adv` takes. -/
noncomputable def o6SRed (A : O6Adv ℕ) : O6Adv ℕ := A

open CatCrypt.Core in
/-- The tree of the first field: a result holding a function, erased to the plain type. -/
noncomputable def o6SRed.choose.tree (c : SPTree ((Fin 2 → Bool) × ℕ)) :
    SPTree ((Fin 2 → Bool) × ℕ) :=
  c.bind fun i => .ret (fun j => !i.1 j, i.2)

open CatCrypt.Core in
/-- The tree of the second field: a binder holding a function, taken plain. -/
noncomputable def o6SRed.guess.tree (g : (Fin 2 → Bool) × ℕ → SPTree Bool)
    (st : (Fin 2 → Bool) × ℕ) : SPTree Bool :=
  g (fun j => st.1 j, st.2)

derive_timed o6SRed.choose.tree

derive_timed o6SRed.guess.tree

example (c : CatCrypt.Core.SPTree.Timed ((Fin 2 → Bool) × ℕ)) :
    (o6SRed.choose.tree.timed c).2.erase = o6SRed.choose.tree c.erase :=
  o6SRed.choose.tree.erase_timed c

example (g : (Fin 2 → Bool) × ℕ → CatCrypt.Core.SPTree.Timed Bool)
    (gCost : (Fin 2 → Bool) × ℕ → ℕ) (st : (Fin 2 → Bool) × ℕ) :
    (o6SRed.guess.tree.timed g gCost st).2.erase = o6SRed.guess.tree (fun a => (g a).erase) st :=
  o6SRed.guess.tree.erase_timed g gCost st

/-! ## Function discriminants, applied lets, tree-valued fields, distributions, words -/

/-- A function passed to a match (`Option.bind` matches on its function argument): the field
that binds it is priced by the function's companion (the shape of the HPKE `redProg`). -/
noncomputable def o6Bind (q : ℕ) (a : Bool ⊕ Option ℕ) : OracleAdv ℕ ℕ (Option ℕ) :=
  .ret (Sum.elim (fun _ => none) (fun ko => ko.bind fun k => some (k + q)) a)

derive_timed o6Bind

/-- A `let`-bound function applied as an oracle tree (the shape of `kemReduction`), zeta- and
beta-reduced before its translation. -/
noncomputable def o6LetApp (x : Bool) : OracleAdv ℕ ℕ ℕ :=
  (have chal := (none : Option ℕ); fun y => match y with
    | true => .ret (chal.getD 0)
    | false => .ret 1) x

derive_timed o6LetApp

example (x : Bool) : (o6LetApp.timed x).2.erase = o6LetApp x := o6LetApp.erase_timed x

/-- A scheme with oracle-tree programs. -/
structure O6RS where
  /-- Encapsulation. -/
  encaps : ℕ → OracleAdv ℕ ℕ ℕ
  /-- Decapsulation. -/
  decaps : ℕ → ℕ → OracleAdv ℕ ℕ (Option ℕ)

/-- A structure holding the scheme. -/
structure O6Outer where
  /-- The scheme. -/
  kem : O6RS

/-- Tree-valued fields of a field path (the shape of the HPKE `ctxtReduction` on
`S.kem.encaps`): primitives priced by their cost companions, their trees at unit cost per
node. -/
noncomputable def o6TreeField (S : O6Outer) (pk : ℕ) : OracleAdv ℕ ℕ (Option ℕ) :=
  (S.kem.encaps pk).bind fun k => S.kem.decaps pk k

derive_timed o6TreeField

example (S : O6Outer) (pk : ℕ) (encapsCost : ℕ → ℕ) (decapsCost : ℕ → ℕ → ℕ) :
    o6TreeField.timed S pk encapsCost decapsCost =
      OracleAdv.Timed.delay (1 + encapsCost pk)
        ((OracleAdv.Timed.ofAdv (S.kem.encaps pk)).bind fun k =>
          (1 + decapsCost pk k, OracleAdv.Timed.ofAdv (S.kem.decaps pk k))) := rfl

/-- A distribution (the shape of `schedReduction`): refused, without a cost structure. -/
noncomputable def o6Pmf (n : ℕ) : PMF ℕ := PMF.pure n

/--
error: derive_timed: no cost structure: `CatCrypt.Tactics.DeriveTimedTest.o6Pmf` is valued in
`PMF`, a distribution without a program; write it as an oracle tree or a computation tree
(`SPComp`) to derive its time
-/
#guard_msgs (whitespace := lax) in
derive_timed o6Pmf

/-- Word operations on `UInt64`, `BitVec 8` and `Fin 5` and a comparison, one unit each. -/
noncomputable def o6Words (a b : UInt64) (x : BitVec 8) (i j : Fin 5) :
    OracleAdv ℕ ℕ (UInt64 × BitVec 8 × Fin 5 × Bool) :=
  .ret (a + (b ^^^ a), x &&& x, i + j, decide (i < j))

derive_timed o6Words

example (a b : UInt64) (x : BitVec 8) (i j : Fin 5) :
    (o6Words.timed a b x i j).1 = 5 := rfl

/-- A scheme with a data field. -/
structure O6Kit where
  /-- A decryption function. -/
  dec : ℕ → ℕ

/-- A program whose costed form takes the cost companion of the field `S.dec`. -/
noncomputable def o6Prog (S : O6Kit) (d : ℕ) : OracleAdv ℕ ℕ ℕ := .ret (S.dec d)

/-- A partial application of `o6Prog` as a handler (the shape of the HPKE `redRun` with
`redProg`): the call passes the caller's companion for `S.dec` (`o6Prog.timed.fieldPaths`). -/
noncomputable def o6Run (S : O6Kit) (A : OracleAdv ℕ ℕ ℕ) : OracleAdv ℕ ℕ ℕ := A.bind (o6Prog S)

derive_timed o6Run

example (S : O6Kit) (A : OracleAdv.Timed ℕ ℕ ℕ) (decCost : ℕ → ℕ) :
    o6Run.timed S A decCost =
      A.bind fun d => OracleAdv.Timed.delay 1 (o6Prog.timed S d decCost) := rfl

/-! ## Recursive callees with dependent results -/

section RecursiveCallee

open CatCrypt.Core

/-- `n` runs of `node`, assembled coordinate by coordinate: a recursion over `ℕ` whose result
type depends on the counter. -/
noncomputable def foldT {X : Type} (node : SPTree X) : (n : ℕ) → SPTree (Fin n → X)
  | 0 => .ret fun i => i.elim0
  | n + 1 => node.bind fun w => (foldT node n).bind fun rest => .ret (Fin.cons w rest)

/-- Three runs of `node`, then `A` on the results. -/
noncomputable def foldUser {X : Type} (node : SPTree X) (A : (Fin 3 → X) → SPTree Bool) :
    SPTree Bool :=
  (foldT node 3).bind A

derive_timed foldUser

example {X : Type} (node : SPTree.Timed X) (n : ℕ) :
    ((foldT.timed node n).2.erase.bind fun y => SPTree.ret y.1) = foldT node.erase n :=
  foldT.erase_timed node n

/-- The empty tuple: a tree without binders whose result holds a function. -/
noncomputable def emptyTuple : SPTree (Fin 0 → Bool) := .ret fun i => i.elim0

derive_timed emptyTuple

/-- `step` on each element of a list: a recursion over `List`. -/
noncomputable def mapLoopT {W : Type} (step : W → SPTree W) : List W → SPTree (List W)
  | [] => .ret []
  | x :: xs => (step x).bind fun y => (mapLoopT step xs).bind fun ys => .ret (y :: ys)

/-- `mapLoopT` on `xs`, then `A`. -/
noncomputable def mapUser {W : Type} (step : W → SPTree W) (A : List W → SPTree Bool)
    (xs : List W) : SPTree Bool :=
  (mapLoopT step xs).bind A

derive_timed mapUser

end RecursiveCallee

/-! ## A field of a structure that reduces to a constructor, applied in a closure -/

section FieldInClosure

open CatCrypt.Core

/-- A structure with one function field. -/
structure EncD (W : Type) where
  /-- Encryption. -/
  enc : W → W → W

/-- An instance of `EncD` built from a class method. -/
def xorE (W : Type) [Add W] : EncD W where
  enc k m := k + m

/-- The field of a `let`-bound structure applied inside `List.zipWith`. -/
noncomputable def epochRed {W : Type} [Add W] (msgs : List W) (A : List W × W → SPTree Bool)
    (km : List W × W) : SPTree Bool :=
  let E := xorE W
  (SPTree.ret (List.zipWith (fun k m => E.enc k m) km.1 msgs, km.2)).bind A

derive_timed epochRed

/-- An instance of `EncD` that returns the key. -/
def keyE (W : Type) : EncD W where
  enc k _ := k

/-- The field of a `let`-bound structure and of a constant structure applied in closures. -/
noncomputable def encRed {W : Type} (A : W → SPTree Bool) (t : SPTree W) (x : W) :
    SPTree Bool :=
  let E := keyE W
  ((t.map fun k => E.enc k x).map fun k => (keyE W).enc k k).bind A

derive_timed encRed

end FieldInClosure

/-! ## The costed mirror of a structure with an anonymous instance parameter -/

section AnonymousInstance

open CatCrypt.Core

variable {W : Type} [Inhabited W]

/-- A structure with an anonymous instance parameter from a `variable` command: the shape of
the key-indistinguishability adversary of X3DH. -/
structure KIAdv (P : {w : W // w = default}) where
  /-- The guess. -/
  run : W → W → SPComp Bool
  /-- A proof field. -/
  run_ok : ∀ k t, run k t = run k t

derive_timed_structure KIAdv

example (P : {w : W // w = default}) (A : KIAdv P) (A' : KIAdv.Timed P) : Prop :=
  KIAdv.Timed.Erases A' A

end AnonymousInstance

/-! ## Lets priced once -/

section LetPricedOnce

open CatCrypt.Core

/-- A `let` under the first binder: the definition applied to both binders is a `let` applied
to an argument. -/
noncomputable def tLetFn (g : ℕ → ℕ) : ℕ → SPTree ℕ :=
  let y := g 0
  fun n => SPTree.ret (y + y + n)

derive_timed tLetFn

/-- The `let` is priced once: `g 0` costs `1 + gCost 0`, the two additions two units. -/
example (g gCost : ℕ → ℕ) (n : ℕ) : (tLetFn.timed g gCost n).1 = 1 + gCost 0 + 2 := rfl

/-- A `have` of a constructor under the first binder (the shape of a reduction that fixes an
absent challenge). -/
noncomputable def tHaveNone (g : Option ℕ → ℕ) : ℕ → SPTree ℕ :=
  have chal : Option ℕ := none
  fun x => SPTree.ret (g chal + x)

derive_timed tHaveNone

example (g gCost : Option ℕ → ℕ) (n : ℕ) : (tHaveNone.timed g gCost n).1 = 2 + gCost none :=
  rfl

/-- A structure of two functions. -/
structure TKit where
  f : ℕ → ℕ
  g : ℕ → ℕ

/-- A `let` of a structure value whose two fields are applied. -/
noncomputable def tKitUse (h : ℕ → ℕ) (n : ℕ) : SPTree ℕ :=
  let k : TKit := ⟨fun x => h (x + n), fun x => h x⟩
  SPTree.ret (k.f 1 + k.g 2)

derive_timed tKitUse

/-- The structure is built once; each field applied costs a call of its value. -/
example (h hCost : ℕ → ℕ) (n : ℕ) :
    (tKitUse.timed h hCost n).1 = 1 + (1 + (hCost (1 + n) + 1) + (1 + hCost 2)) := rfl

/-- A structure holding a structure of two functions. -/
structure TOuter where
  inner : TKit

/-- A `let` of a field path of a binder, whose fields are applied: the path is substituted,
and each field is priced by its cost companion. -/
noncomputable def tPathLet (o : TOuter) (n : ℕ) : SPTree ℕ :=
  let k := o.inner
  SPTree.ret (k.f n + k.g n)

derive_timed tPathLet

example (o : TOuter) (n : ℕ) (fCost gCost : ℕ → ℕ) :
    (tPathLet.timed o n fCost gCost).1 = 1 + (1 + fCost n + (1 + gCost n)) := rfl

end LetPricedOnce

/-! ## Well-founded recursion -/

section WellFounded

open CatCrypt.Core

/-- A recursion by well-founded recursion through `if`. -/
noncomputable def tHalveT (step : ℕ → SPTree Unit) (n : ℕ) : SPTree Unit :=
  if h : n = 0 then SPTree.ret () else SPTree.bind (step n) fun _ => tHalveT step (n / 2)
termination_by n
decreasing_by omega

derive_timed tHalveT

end WellFounded

/-! ## Quotient operations without a registered cost -/

section QuotientRefusal

open CatCrypt.Core

/-- The cardinality of a finite set, an operation on a quotient without a registered cost. -/
noncomputable def tCardT (s : Finset ℕ) : SPTree ℕ :=
  SPTree.ret s.card

/--
error: derive_timed: needs a registered primitive: `Finset.card` is an operation on a quotient
type (`Finset`, `Multiset`) without a registered cost `Finset.card.timedCost`; the costs of
`Finset.sum`, `Finset.prod`, `Finset.univ`, `Finset.range` and `Finset.erase` are registered in
`CatCryptCore.Tactics.StdCosts`, which the module must import
-/
#guard_msgs (whitespace := lax) in
derive_timed tCardT

end QuotientRefusal

end CatCrypt.Tactics.DeriveTimedTest
