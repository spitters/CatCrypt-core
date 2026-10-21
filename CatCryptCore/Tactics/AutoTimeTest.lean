/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.AutoTime
import all CatCryptCore.Crypto.Anon.Signalling

/-!
# Tests of `time_bound`

Goals of both tree kinds: a costed computation tree with a bind after an abstract key
generation, a uniform sample and an adversary bounded by a hypothesis; a costed oracle
adversary sequenced after an adversary of known time; a definition by `match` that is
unfolded and split; the time theorem of an inner definition used as a source; the dispatcher
`catcrypt_auto` on a time goal; and the statements of two time theorems of the library,
`crRedTree.timeBound_timed` and `OracleAdv.Timed.timeBound_bind`, closed by `time_bound`
alone.

## Measurement on a sample of time theorems

A uniform sample of 24 time theorems of the workspace, each stated as
`example : type_of% @thm := by time_bound` in a file outside the module system, where the
bodies of the costed definitions are visible; in a module they are visible through
`import all` (as for `Signalling` here) or `@[expose]`. Twenty were measurable; four lie in files that
were under edit (`iknpSenderRed`, `authDDHRed`, and two of `HPKE/Timed`). Closed: 7 of 20 by
the first version of the procedure, 10 of 20 after the first revision (pairs `(c + y.1, y.2)`,
case analysis on the variable of a recursor, step costs `x.1` reduced or bounded by a source,
subtype invariants, `whnfR`), 10 of 20 after the second revision. Closed:
`crRedTree`, `OracleAdv.Timed.timeBound_bind`, `ctrEncAdv`, `edhoc_m2_ddh_red_0_1.tree`,
`postStage`, `bavcGuess`, `splitRed₁.tree`, `nkRed7.tree`, `contRed.tree`,
`kdfReduction.tree`. Open, by the residual goal:

* outside the domain of the procedure: `timeBound_query_iff` (an `↔`), `lazyRF` (a definition
  by recursion on the adversary, proved by induction);
* a combinator whose time theorem has premises that are not time bounds (query bounds of the
  erased adversary): `ksExtractor` (`forkRun.timedK`), `recReduction` (`runOracle`), `liftP`
  (`mapQueryAnswer`);
* a pair `(c + (y.1), (y.2))` whose component `y` is itself a pair, read as two separate
  components, so that the leaf `P + (e, s).2.time ≤ B` counts the step cost of `y` twice:
  `edhoc_ddh_red_0_1.tree`, `GDH_Red_Step4.tree`, `wgKsReduction1.tree`;
* a step cost `(R.timed …).1` of a staged composition whose budget is carried in the state of
  the stages: `rootChoose`, `h3Hop`.

A second uniform sample of 24 time theorems, measured after the second revision without
further change: 21 measurable (two modules with out-of-date imports, one module under
repair), 10 closed (`prfMacRed` and nine reductions of `Noise/Handshake/Timed`). Open: the
four stages of `FAEST/Timed` (`h3Choose`, `hopPre.timeBound_stepBind`, `cvChoose`,
`leafChoose`: step costs `(A.bind f).1` of a staged composition), four reductions of
`Noise/Handshake/Timed` (`cycRed1`, `cycRed2`, `cycRed3`, `nkRed1`: a leaf
`P + (A.bind f).1 + (A.bind f).2.time ≤ B` after a pair `(y.1, y.2)` whose continuation was
not bounded), `tagRed` (`OracleAdv.Timed.simulate`, a step cost not reduced), `ff1Reduction`
and `emImpl` (recursive costed definitions, `feistelAdv.timed`, `Sponge.walk.timed`).
-/

set_option autoImplicit false

namespace CatCrypt.Tactics.AutoTimeTest

open CatCrypt.Core CatCrypt.Crypto

/-- A bind after an abstract tree, a sample node and a bounded adversary. -/
example {W : Type} [Fintype W] [Nonempty W] (keygen : SPTree.Timed W)
    (A : W → SPTree.Timed Bool) (ACost : W → ℕ) (f : W → W → ℕ) {T a t : ℕ}
    (hA : ∀ o, (A o).time ≤ T) (hAc : ∀ o, ACost o ≤ a) (hf : ∀ x y, f x y ≤ t) :
    SPTree.Timed.stepTime (keygen.bind fun k => (f k k,
      SPTree.Timed.sample W inferInstance inferInstance (fun b => f b k + ACost b) fun b => A b)) ≤
      keygen.time + (T + a + 2 * t + 1) := by
  time_bound

/-- A bind after an oracle adversary with a time bound in the context. -/
example {D R : Type} (A : OracleAdv.Timed D R Bool) {T : ℕ} (hA : A.TimeBound T) (c : ℕ)
    (hc : c ≤ 3) : OracleAdv.Timed.StepTimeBound (A.bind fun b => (c, .ret b)) (T + 3) := by
  time_bound

/-- A costed tree defined by `match`. -/
noncomputable def matchTree {K L : Type} (kg : PMF K) (kc : K → ℕ) (f : K → PMF L)
    (fc : K → L → ℕ) (r : Bool ⊕ K) : ℕ × OracleAdv.Timed Empty Empty (K × L) :=
  match r with
  | .inl _ => (0, .rand kg kc fun k => .rand (f k) (fc k) fun l => .ret (k, l))
  | .inr k => (2, .rand (f k) (fc k) fun l => .ret (k, l))

/-- The definition is unfolded and its `match` split. -/
example {K L : Type} (kg : PMF K) (kc : K → ℕ) (f : K → PMF L) (fc : K → L → ℕ) {a b : ℕ}
    (hk : ∀ k, kc k ≤ a) (hf : ∀ k l, fc k l ≤ b) (r : Bool ⊕ K) :
    OracleAdv.Timed.StepTimeBound (matchTree kg kc f fc r) (3 + a + 2 * b) := by
  time_bound

/-- The time theorem of `matchTree`, used below a definition that calls it. -/
theorem matchTree.timeBound {K L : Type} (kg : PMF K) (kc : K → ℕ) (f : K → PMF L)
    (fc : K → L → ℕ) {a b : ℕ} (hk : ∀ k, kc k ≤ a) (hf : ∀ k l, fc k l ≤ b) (r : Bool ⊕ K) :
    OracleAdv.Timed.StepTimeBound (matchTree kg kc f fc r) (3 + a + 2 * b) := by
  time_bound

/-- A definition that sequences `matchTree` before one step. -/
noncomputable def afterMatch {K L : Type} (kg : PMF K) (kc : K → ℕ) (f : K → PMF L)
    (fc : K → L → ℕ) (r : Bool ⊕ K) : ℕ × OracleAdv.Timed Empty Empty (K × L) :=
  OracleAdv.Timed.delay 1 (matchTree kg kc f fc r)

/-- The bound of the inner definition comes from its time theorem. -/
example {K L : Type} (kg : PMF K) (kc : K → ℕ) (f : K → PMF L) (fc : K → L → ℕ) {a b : ℕ}
    (hk : ∀ k, kc k ≤ a) (hf : ∀ k l, fc k l ≤ b) (r : Bool ⊕ K) :
    OracleAdv.Timed.StepTimeBound (afterMatch kg kc f fc r) (4 + a + 2 * b) := by
  time_bound

/-- The dispatcher reads the shape `time bound`. -/
example {W : Type} (keygen : SPTree.Timed W) (A : W → SPTree.Timed Bool) {T : ℕ}
    (hA : ∀ o, (A o).time ≤ T) :
    SPTree.Timed.stepTime (keygen.bind fun k => (1, A k)) ≤ keygen.time + T + 1 := by
  catcrypt_auto

/-- The statement of `crRedTree.timeBound_timed`: a costed tree of `rand` nodes over key
generation, signing, the root, the group choice, the forger and the extractor. -/
example : type_of% @CatCrypt.Crypto.Anon.Signalling.crRedTree.timeBound_timed := by
  time_bound

/-- The statement of `OracleAdv.Timed.timeBound_bind`. -/
example : type_of% @CatCrypt.Crypto.OracleAdv.Timed.timeBound_bind := by
  time_bound

end CatCrypt.Tactics.AutoTimeTest
