/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveReduction

/-!
# Tests for `derive_reduction`

Reductions written in `do`-notation over `SPComp`, with adversaries as function binders. For
each, the command defines the computation tree `B.tree`, proves `B.compile_tree` and runs
`derive_timed B.tree`; the statements of the compile equation and of the erasure theorem are
pinned by `example`s. The shapes are a DDH-style reduction (a uniform sample, group
operations given as a binder, one adversary call), a reduction with two adversary calls and a
second adversary, a reduction with `match` and `if`, a reduction reading and writing a
location, and a reduction that calls a top-level `def` written in `do`-notation, with the
adversary named explicitly. Two tests have primitives: fields of a structure binder and a
method of a local instance, as computation primitives and as data functions. Three tests have
structure-valued results: two reductions between two-stage distinguishers with computation
fields (the shapes of the pair-hybrid reductions of the Signal ratchet chain), with their erasure
theorem pinned and the time of each stage bounded, and a reduction between two-stage oracle
adversaries with a type field, two tree fields and a proof field (the shape of the ECH
reduction). The last test pins the refusal of an unpriced computation, a field of a structure
bound in the body.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveReductionTest

open CatCrypt.Core

/-! ## A DDH-style reduction -/

/-- On a DDH triple `(gx, gy, gz)`, mask the message `m` with `gz` and a fresh uniform `r`,
call the adversary on the public key and the ciphertext, and return the negation of its
guess. The group operation is the binder `mul`. -/
noncomputable def ddhRed {G : Type} [Fintype G] [Nonempty G] (mul : G → G → G) (m : G)
    (A : G × G × G → SPComp Bool) (gx gy gz : G) : SPComp Bool := do
  let r ← SPComp.sample G
  let b ← A (gx, gy, mul m (mul gz r))
  return !b

derive_reduction ddhRed

example {G : Type} [Fintype G] [Nonempty G] (mul : G → G → G) (m : G)
    (A : G × G × G → SPTree Bool) (gx gy gz : G) :
    (ddhRed.tree mul m A gx gy gz).compile = ddhRed mul m (fun x => (A x).compile) gx gy gz :=
  ddhRed.compile_tree mul m A gx gy gz

example {G : Type} [Fintype G] [Nonempty G] (mul : G → G → G) (mulCost : G → G → ℕ) (m : G)
    (A : G × G × G → SPTree.Timed Bool) (ACost : G × G × G → ℕ) (gx gy gz : G) :
    (ddhRed.tree.timed mul mulCost m A ACost gx gy gz).2.erase =
      ddhRed.tree mul m (fun x => (A x).erase) gx gy gz :=
  ddhRed.tree.erase_timed mul mulCost m A ACost gx gy gz

/-! ## Two adversary calls and a second adversary -/

/-- Call `A` twice, the second time on the first answer, and pass the conjunction of the
answers to `B`. -/
noncomputable def twoCall (A : Bool → SPComp Bool) (B : Bool → ℕ → SPComp ℕ) : SPComp ℕ := do
  let x ← A true
  let y ← A x
  B (x && y) 3

derive_reduction twoCall

example (A : Bool → SPTree Bool) (B : Bool → ℕ → SPTree ℕ) :
    (twoCall.tree A B).compile = twoCall (fun x => (A x).compile) (fun x n => (B x n).compile) :=
  twoCall.compile_tree A B

/-! ## `match` and `if` -/

/-- Call the adversary on `n`; on an answer `some k` return `k` when `k < n` and fail
otherwise, on `none` return `0`. -/
noncomputable def branchRed (A : ℕ → SPComp (Option ℕ)) (n : ℕ) : SPComp ℕ := do
  let o ← A n
  match o with
  | some k => if k < n then return k else SPComp.fail
  | none => return 0

derive_reduction branchRed

example (A : ℕ → SPTree (Option ℕ)) (n : ℕ) :
    (branchRed.tree A n).compile = branchRed (fun x => (A x).compile) n :=
  branchRed.compile_tree A n

example (A : ℕ → SPTree.Timed (Option ℕ)) (ACost : ℕ → ℕ) (n : ℕ) :
    (branchRed.tree.timed A ACost n).2.erase = branchRed.tree (fun x => (A x).erase) n :=
  branchRed.tree.erase_timed A ACost n

/-! ## `get` and `set` -/

/-- Read the location `l`, write `upd` of the value back, and call the adversary on the old
value. -/
noncomputable def stateRed (l : Location) (upd : l.ty → l.ty) (A : l.ty → SPComp Bool) :
    SPComp Bool := do
  let v ← SPComp.get l
  SPComp.set l (upd v)
  A v

derive_reduction stateRed

example (l : Location) (upd : l.ty → l.ty) (A : l.ty → SPTree Bool) :
    (stateRed.tree l upd A).compile = stateRed l upd (fun x => (A x).compile) :=
  stateRed.compile_tree l upd A

/-! ## A called definition and an explicit adversary -/

/-- Mask `b` with a uniform bit and call the adversary. -/
noncomputable def maskThen (A : Bool → SPComp Bool) (b : Bool) : SPComp Bool := do
  let c ← SPComp.sample Bool
  A (xor b c)

/-- Post-process `w` with `post` and continue with `maskThen A`. Both `post` and `A` are
functions into `SPComp`, so both are adversaries. -/
noncomputable def postRed (post : Bool → SPComp Bool) (A : Bool → SPComp Bool) :
    Bool → SPComp Bool :=
  fun w => (post w).bind (maskThen A)

derive_reduction postRed (adv := post A)

example (post A : Bool → SPTree Bool) (w : Bool) :
    (postRed.tree post A w).compile =
      postRed (fun x => (post x).compile) (fun x => (A x).compile) w :=
  postRed.compile_tree post A w

/-! ## Primitives: fields of a structure and methods of a local instance -/

/-- Primitives given as a structure: a key generation, a data function and a tagging
computation. -/
structure Deps (K M C : Type) where
  keygen : SPComp K
  enc : K → M → C
  mac : K → C → SPComp Bool

/-- A class with a data method. -/
class Wrap (K C : Type) where
  wrap : K → C → C

/-- Generate a key, encrypt and wrap `m`, call the adversary on the ciphertext, and tag it;
the fields `D.keygen` and `D.mac` are computation primitives, `D.enc` and the method `Wrap.wrap`
are data functions. -/
noncomputable def depRed {K M C : Type} [Wrap K C] (D : Deps K M C) (m : M)
    (A : C → SPComp Bool) : SPComp Bool := do
  let k ← D.keygen
  let c := Wrap.wrap k (D.enc k m)
  let b ← A c
  if b then D.mac k c else
    match b with
    | true => D.mac k (D.enc k m)
    | false => return false

derive_reduction depRed

example {K M C : Type} [Wrap K C] (D : Deps K M C) (m : M) (A : C → SPTree Bool)
    (keygen : SPTree K) (mac : K → C → SPTree Bool) (h_keygen : keygen.compile = D.keygen)
    (h_mac : ∀ k c, (mac k c).compile = D.mac k c) :
    (depRed.tree D m A Wrap.wrap D.enc keygen mac).compile =
      depRed D m (fun x => (A x).compile) :=
  depRed.compile_tree D m A keygen mac h_keygen h_mac

example {K M C : Type} [Wrap K C] (D : Deps K M C) (m : M) (A : C → SPTree.Timed Bool)
    (ACost : C → ℕ) (wrap : K → C → C) (wrapCost : K → C → ℕ) (enc : K → M → C)
    (encCost : K → M → ℕ) (keygen : SPTree.Timed K) (mac : K → C → SPTree.Timed Bool)
    (macCost : K → C → ℕ) :
    (depRed.tree.timed D m A ACost wrap wrapCost enc encCost keygen mac macCost).2.erase =
      depRed.tree D m (fun x => (A x).erase) wrap enc keygen.erase
        (fun k c => (mac k c).erase) :=
  depRed.tree.erase_timed D m A ACost wrap wrapCost enc encCost keygen mac macCost

/-- An adversary given as a structure. -/
structure GuessAdv where
  guess : Bool → SPComp Bool

/-- A reduction calling a field of a structure binder: the field is a computation primitive. -/
noncomputable def fieldRed (A : GuessAdv) (b : Bool) : SPComp Bool := A.guess b

derive_reduction fieldRed

example (A : GuessAdv) (b : Bool) (guess : Bool → SPTree Bool)
    (h : ∀ a, (guess a).compile = A.guess a) :
    (fieldRed.tree A b guess).compile = fieldRed A b :=
  fieldRed.compile_tree A b guess h

/-! ## Primitives used directly and through helpers; arguments of helpers priced once -/

/-- A kit with a key generation, a data function and a pair-valued data function. -/
structure Kit (W : Type) where
  keygen : SPComp W
  f : W → W → W
  pair : W → W × W

/-- A data helper that applies `kit.f`. -/
noncomputable def helperF {W : Type} (kit : Kit W) (x : W) : W := kit.f x x

/-- `kit.f` applied directly and inside `helperF`: one binder `f` with one cost companion. -/
noncomputable def oneComp {W : Type} (kit : Kit W) (A : W → SPComp Bool) : SPComp Bool := do
  let k ← kit.keygen
  A (kit.f k (helperF kit k))

derive_reduction oneComp (adv := A)

example {W : Type} (kit : Kit W) (A : W → SPTree.Timed Bool) (ACost : W → ℕ) (f : W → W → W)
    (fCost : W → W → ℕ) (keygen : SPTree.Timed W) :
    (oneComp.tree.timed kit A ACost f fCost keygen).2.erase =
      oneComp.tree kit (fun x => (A x).erase) f keygen.erase :=
  oneComp.tree.erase_timed kit A ACost f fCost keygen

/-- A computation helper that uses its argument `x` twice. -/
noncomputable def twice {W : Type} (A : W → SPComp Bool) (x : W) : SPComp Bool :=
  SPComp.bind (A x) fun _ => A x

/-- The argument `kit.f k k` of `twice` is priced once. -/
noncomputable def letArg {W : Type} (kit : Kit W) (A : W → SPComp Bool) : SPComp Bool := do
  let k ← kit.keygen
  twice A (kit.f k k)

derive_reduction letArg (adv := A)

example {W : Type} (kit : Kit W) (A : W → SPTree.Timed Bool) (ACost : W → ℕ) (f : W → W → W)
    (fCost : W → W → ℕ) (keygen : SPTree.Timed W) :
    letArg.tree.timed kit A ACost f fCost keygen =
      keygen.bind fun x =>
        (1 + fCost x x + (1 + ACost (f x x) +
          ((A (f x x)).bind fun _ => (1 + ACost (f x x), A (f x x))).1),
          have y := f x x
          ((A y).bind fun _ => (1 + ACost y, A y)).2) := rfl

/-- A computation helper that uses its first data argument. -/
noncomputable def usePair {W : Type} (A : W → SPComp Bool) (a _b : W) : SPComp Bool := A a

/-- The projections `(kit.pair k).1` and `(kit.pair k).2` share one evaluation of
`kit.pair k`. -/
noncomputable def pairArg {W : Type} (kit : Kit W) (A : W → SPComp Bool) : SPComp Bool := do
  let k ← kit.keygen
  usePair A (kit.pair k).1 (kit.pair k).2

derive_reduction pairArg (adv := A)

example {W : Type} (kit : Kit W) (A : W → SPTree.Timed Bool) (ACost : W → ℕ)
    (pair : W → W × W) (pairCost : W → ℕ) (keygen : SPTree.Timed W) :
    pairArg.tree.timed kit A ACost pair pairCost keygen =
      keygen.bind fun x =>
        (1 + pairCost x + (1 + ACost (pair x).1),
          have p := pair x
          A p.1) := rfl

/-- A function binder `B` that the body does not use is not a binder of the tree. -/
noncomputable def unusedB {W : Type} (_B : W → SPComp W) (A : W → SPComp Bool) (x : W) :
    SPComp Bool := A x

derive_reduction unusedB (adv := A)

example {W : Type} (B : W → SPComp W) (A : W → SPTree Bool) (x : W) :
    (unusedB.tree A x).compile = unusedB B (fun y => (A y).compile) x :=
  unusedB.compile_tree B A x

/-! ## Structure-valued reductions -/

/-- A two-stage distinguisher: a first stage drawing a state and an input, a second stage
guessing from the state and an output. -/
structure TwoStageDist (σ α β : Type) where
  pre : SPComp (σ × α)
  guess : σ → β → SPComp Bool

derive_timed_structure TwoStageDist

/-- The distinguisher against the first of two samplers: its second stage draws the second
component with `d`. -/
noncomputable def fstRed {σ β γ : Type} (d : Unit → SPComp γ)
    (B : TwoStageDist σ Unit (β × γ)) : TwoStageDist σ Unit β where
  pre := B.pre
  guess := fun st r => SPComp.bind (d ()) fun q => B.guess st (r, q)

derive_reduction fstRed

/-- The distinguisher against the second of two samplers: its first stage draws the first
component with `c` and keeps it in the state. -/
noncomputable def sndRed {σ β γ : Type} (c : Unit → SPComp β)
    (B : TwoStageDist σ Unit (β × γ)) : TwoStageDist (σ × β) Unit γ where
  pre := SPComp.bind B.pre fun p => SPComp.bind (c ()) fun r => SPComp.pure ((p.1, r), ())
  guess := fun st q => B.guess st.1 (st.2, q)

derive_reduction sndRed

example {σ β γ : Type} (B : TwoStageDist σ Unit (β × γ)) (d : Unit → SPTree.Timed γ)
    (dCost : Unit → ℕ) (pre : SPTree.Timed (σ × Unit)) (guess : σ → β × γ → SPTree.Timed Bool)
    (guessCost : σ → β × γ → ℕ) (hp : pre.erase.compile = B.pre)
    (hg : ∀ s y, (guess s y).erase.compile = B.guess s y) :
    (fstRed.timed d dCost B pre guess guessCost).Erases (fstRed (fun u => (d u).erase.compile) B) :=
  fstRed.erase_timed B d dCost pre guess guessCost hp hg

/-- The second stage of `fstRed`: one call of `d`, then one call of the second stage of `B`. -/
theorem fstRed.timeBound_timed {σ β γ : Type} (d : Unit → SPTree.Timed γ) (dCost : Unit → ℕ)
    (B : TwoStageDist σ Unit (β × γ)) (pre : SPTree.Timed (σ × Unit))
    (guess : σ → β × γ → SPTree.Timed Bool) (guessCost : σ → β × γ → ℕ) {Td ad T a : ℕ}
    (hd : (d ()).time ≤ Td) (hdc : dCost () ≤ ad) (hg : ∀ s y, (guess s y).time ≤ T)
    (hgc : ∀ s y, guessCost s y ≤ a) :
    (fstRed.timed d dCost B pre guess guessCost).TimeBound pre.time (ad + Td + a + T + 2) := by
  refine ⟨?_, fun st r => ?_⟩
  · simp [fstRed.timed, fstRed.pre.tree.timed, SPTree.Timed.stepTime]
  · show SPTree.Timed.stepTime (fstRed.guess.tree.timed d dCost B pre guess guessCost st r) ≤
      ad + Td + a + T + 2
    simp only [fstRed.guess.tree.timed, SPTree.Timed.stepTime_delay]
    have := SPTree.Timed.stepTime_bind_le (d ())
      (fun x => (1 + guessCost st (r, x), guess st (r, x))) (a + T + 1) fun x => by
        simp only [SPTree.Timed.stepTime]; have := hg st (r, x); have := hgc st (r, x); omega
    omega

/-- The first stage of `sndRed`: the first stage of `B`, then one call of `c`. -/
theorem sndRed.timeBound_timed {σ β γ : Type} (c : Unit → SPTree.Timed β) (cCost : Unit → ℕ)
    (B : TwoStageDist σ Unit (β × γ)) (pre : SPTree.Timed (σ × Unit))
    (guess : σ → β × γ → SPTree.Timed Bool) (guessCost : σ → β × γ → ℕ) {Tc ac T a : ℕ}
    (hc : (c ()).time ≤ Tc) (hcc : cCost () ≤ ac) (hg : ∀ s y, (guess s y).time ≤ T)
    (hgc : ∀ s y, guessCost s y ≤ a) :
    (sndRed.timed c cCost B pre guess guessCost).TimeBound (pre.time + ac + Tc + 1)
      (a + T + 1) := by
  refine ⟨?_, fun st q => ?_⟩
  · show SPTree.Timed.stepTime (sndRed.pre.tree.timed c cCost B pre guess guessCost) ≤
      pre.time + ac + Tc + 1
    simp only [sndRed.pre.tree.timed]
    have := SPTree.Timed.stepTime_bind_le pre
      (fun x => SPTree.Timed.delay (1 + cCost ())
        ((c ()).bind fun r => (0, SPTree.Timed.ret ((x.1, r), ())))) (ac + Tc + 1) fun x => by
        rw [SPTree.Timed.stepTime_delay]
        have := SPTree.Timed.stepTime_bind_le (c ())
          (fun r => (0, SPTree.Timed.ret ((x.1, r), ()))) 0 fun r => by
            simp [SPTree.Timed.stepTime, SPTree.Timed.time_ret]
        omega
    omega
  · show SPTree.Timed.stepTime (sndRed.guess.tree.timed c cCost B pre guess guessCost st q) ≤
      a + T + 1
    simp only [sndRed.guess.tree.timed, SPTree.Timed.stepTime]
    have := hg st.1 (st.2, q); have := hgc st.1 (st.2, q); omega

/-- A two-stage oracle adversary: a state type, two tree fields and a proof field about the
first stage. -/
structure OracleTwoStage (W : Type) : Type 1 where
  St : Type
  choose : W → CatCrypt.Crypto.OracleAdv W W (W × St)
  guess : St → W → CatCrypt.Crypto.OracleAdv W W Bool
  bound : ∀ w, choose w = choose w

derive_timed_structure OracleTwoStage

/-- The first stage of `encRed`: run `choose` and encode the first component. -/
def chooseEnc {W St : Type} (enc : W → W) (choose : W → CatCrypt.Crypto.OracleAdv W W (W × St))
    (w : W) : CatCrypt.Crypto.OracleAdv W W (W × St) :=
  (choose w).bind fun x => .ret (enc x.1, x.2)

/-- A reduction between two-stage oracle adversaries, in the shape of the ECH reduction: the
same state type, the first stage followed by an encoding, and the same second stage. -/
def encRed {W : Type} (enc : W → W) (A : OracleTwoStage W) : OracleTwoStage W where
  St := A.St
  choose := chooseEnc enc A.choose
  guess := A.guess
  bound _ := rfl

derive_reduction encRed

example {W : Type} (enc : W → W) (A : OracleTwoStage W) (encCost : W → ℕ)
    (choose : W → CatCrypt.Crypto.OracleAdv.Timed W W (W × A.St)) (chooseCost : W → ℕ)
    (guess : A.St → W → CatCrypt.Crypto.OracleAdv.Timed W W Bool) (guessCost : A.St → W → ℕ)
    (hc : ∀ w, (choose w).erase = A.choose w) (hg : ∀ s w, (guess s w).erase = A.guess s w) :
    (encRed.timed enc encCost A choose chooseCost guess guessCost).Erases (encRed enc A) :=
  encRed.erase_timed enc A encCost choose chooseCost guess guessCost hc hg

/-! ## Refusal of an unpriced computation -/

/-- A reduction calling a field of a structure returned by the adversary. -/
noncomputable def boundFieldRed (A : Bool → SPComp GuessAdv) : SPComp Bool := do
  let g ← A true
  g.guess false

/--
error: derive_reduction: unpriced computation: the subterm
  x.guess false
unfolds to
  x.1 false
which is not built from `pure`, `bind`, `sample`, `get`, `set`, `fail`, `if`, `match`, a call of an adversary or a call of a primitive
-/
#guard_msgs in
derive_reduction boundFieldRed

end CatCrypt.Tactics.DeriveReductionTest
