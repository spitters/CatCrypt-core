/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DerivePMF
public import CatCryptCore.Tactics.StdCosts
public import CatCryptCore.Crypto.SPCompPMF

/-!
# Tests for the costed forms of distribution-valued reductions

The rule of `CatCryptCore.Tactics.DerivePMF`, over fresh definitions:

* a uniform sample followed by an output map;
* a lazily sampled oracle on a list table (a lookup, and on a miss a uniform sample inserted),
  derived on its own, and a reduction that runs a fresh adversary against it from the empty
  table and maps the output: every query of the adversary is answered by the costed program of
  the oracle's step;
* an adversary given as a structure with a tree-valued field, run against the oracle: the field
  is a costed tree binder of the costed form, and the erasure theorem takes the hypothesis that
  its erased costed tree is the field;
* a computation `liftPMF p` of a distribution: its costed form is the costed tree of `p`;
* the refusal of a distribution given as a parameter.

The erasure theorems and the closed forms of the costs are pinned by `example`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DerivePMFTest

open CatCrypt.Crypto CatCrypt.Core

/-! ## A sample followed by an output map -/

/-- A uniform index, shifted by `n`. -/
noncomputable def sampleShift (n : ℕ) : PMF ℕ :=
  (PMF.uniformFintype (Fin 8)).map fun i => i.val + n

derive_timed sampleShift

/-- The costed form: one `rand` node, and the output map priced at the leaf. -/
example (n : ℕ) : sampleShift.timed n =
    OracleAdv.Timed.delay 0 ((OracleAdv.Timed.rand (PMF.uniformFintype (Fin 8)) (fun _ => 0)
      OracleAdv.Timed.ret).bind fun i => (1, OracleAdv.Timed.ret (i.val + n))) := rfl

/-- The erasure theorem: the distribution of the erased costed tree. -/
example (n : ℕ) : (sampleShift.timed n).2.erase.dist = sampleShift n :=
  sampleShift.erase_timed n

/-- Its time: the sample and the addition. -/
example (n : ℕ) : OracleAdv.Timed.StepTimeBound (sampleShift.timed n) 2 := by
  refine ⟨Nat.zero_le _, ?_⟩
  simp only [sampleShift.timed, sampleShift.pmfTree.timed, OracleAdv.Timed.bind]
  exact ⟨by omega, fun _ => ⟨by simp, trivial⟩⟩

/-! ## A lazily sampled oracle on a list table, and a run against it -/

/-- The lazily sampled oracle: a recorded point returns its value, a fresh point samples a bit
and records it at the head of the table. -/
noncomputable def lazyStep (t : List (ℕ × Bool)) (d : ℕ) : PMF (Bool × List (ℕ × Bool)) :=
  match t.lookup d with
  | some b => PMF.pure (b, t)
  | none => (PMF.uniformFintype Bool).map fun b => (b, (d, b) :: t)

derive_timed lazyStep

/-- The costed step: the lookup at the cost registered in `StdCosts` and the match in front;
on a miss one `rand` node for the fresh bit, and the insertion at the leaf. -/
example (t : List (ℕ × Bool)) (d : ℕ) : lazyStep.timed t d =
    OracleAdv.Timed.delay (2 + List.lookup.timedCost d t)
      (match List.lookup d t with
      | some b => (0, OracleAdv.Timed.ret (b, t))
      | none => (OracleAdv.Timed.rand (PMF.uniformFintype Bool) (fun _ => 0)
          OracleAdv.Timed.ret).bind fun x => (0, OracleAdv.Timed.ret (x, (d, x) :: t))) := rfl

example (t : List (ℕ × Bool)) (d : ℕ) : (lazyStep.timed t d).2.erase.dist = lazyStep t d :=
  lazyStep.erase_timed t d

/-- A reduction that runs the adversary `A` against the lazily sampled oracle from the empty
table and returns the negation of its output bit. -/
noncomputable def runLazy (A : OracleAdv ℕ Bool Bool) : PMF Bool :=
  (OracleAdv.run lazyStep A []).map fun z => !z.1

derive_timed runLazy

/-- The oracle's step is the definition `runLazy.pmfStep`, the tree of `lazyStep`; its costed
form has the cost of the step of `lazyStep.timed`. -/
example (t : List (ℕ × Bool)) (d : ℕ) : runLazy.pmfStep.timed t d =
    OracleAdv.Timed.delay (2 + List.lookup.timedCost d t)
      (match List.lookup d t with
      | some b => (0, OracleAdv.Timed.ret (b, t))
      | none => (OracleAdv.Timed.rand (PMF.uniformFintype Bool) (fun _ => 0)
          OracleAdv.Timed.ret).bind fun x => (0, OracleAdv.Timed.ret (x, (d, x) :: t))) := rfl

/-- The costed form: the costed adversary `A` simulated by the costed step of the oracle, each
query answered by `runLazy.pmfStep.timed` at that query, one unit for its call, then the output
map at the leaves. -/
example (A : OracleAdv.Timed ℕ Bool Bool) : runLazy.timed A =
    OracleAdv.Timed.delay (OracleAdv.Timed.simulate (fun t d =>
        (1 + (runLazy.pmfStep.timed t d).1, (runLazy.pmfStep.timed t d).2)) A []).1
      ((OracleAdv.Timed.simulate (fun t d =>
        (1 + (runLazy.pmfStep.timed t d).1, (runLazy.pmfStep.timed t d).2)) A []).2.bind
        fun z => (2, OracleAdv.Timed.ret !z.1)) := rfl

/-- The erasure theorem: the erased costed reduction has the distribution of the run of the
erased adversary. -/
example (A : OracleAdv.Timed ℕ Bool Bool) : (runLazy.timed A).2.erase.dist = runLazy A.erase :=
  runLazy.erase_timed A

/-- Under any oracle, the run of the erased costed tree has that distribution. -/
example (A : OracleAdv.Timed ℕ Bool Bool) {U : Type} (O : U → Empty → PMF (Empty × U)) (u : U) :
    (OracleAdv.run O (runLazy.timed A).2.erase u).map Prod.fst = runLazy A.erase := by
  rw [OracleAdv.run_map_fst_eq_dist, runLazy.erase_timed]

/-! ## An adversary given as a structure -/

/-- An adversary as a structure: a run on an input and a query bound. -/
structure LazyAdv where
  /-- The run of the adversary on an input. -/
  run : ℕ → OracleAdv ℕ Bool Bool
  /-- At most four queries on every path. -/
  bound : ∀ x, (run x).IsQueryBound 4

/-- The adversary's run on `x` against the lazily sampled oracle from a table recording `x`. -/
noncomputable def runAdv (B : LazyAdv) (x : ℕ) : PMF Bool :=
  (OracleAdv.run lazyStep (B.run x) [(x, true)]).map Prod.fst

derive_timed runAdv

/-- The field `B.run` run against the oracle is a costed tree binder `B_run` of the costed form,
with its cost companion `B_runCost`, the cost of computing the tree from the input. -/
example (B : LazyAdv) (x : ℕ) (B_run : ℕ → OracleAdv.Timed ℕ Bool Bool) (B_runCost : ℕ → ℕ) :
    runAdv.timed B x B_run B_runCost =
      OracleAdv.Timed.delay (1 + B_runCost x +
          (OracleAdv.Timed.simulate (fun t d =>
            (1 + (runAdv.pmfStep.timed t d).1, (runAdv.pmfStep.timed t d).2)) (B_run x)
            [(x, true)]).1)
        ((OracleAdv.Timed.simulate (fun t d =>
            (1 + (runAdv.pmfStep.timed t d).1, (runAdv.pmfStep.timed t d).2)) (B_run x)
            [(x, true)]).2.bind fun z => (0, OracleAdv.Timed.ret z.1)) := rfl

/-- The erasure theorem takes the hypothesis that the erased costed tree is the field. -/
example (B : LazyAdv) (x : ℕ) (B_run : ℕ → OracleAdv.Timed ℕ Bool Bool) (B_runCost : ℕ → ℕ)
    (h : ∀ y, (B_run y).erase = B.run y) :
    (runAdv.timed B x B_run B_runCost).2.erase.dist = runAdv B x :=
  runAdv.erase_timed B x B_run B_runCost h

/-! ## A computation `liftPMF p` -/

/-- The lift of the shifted sample to a computation. -/
noncomputable def liftShift (n : ℕ) : SPComp ℕ := liftPMF (sampleShift n)

derive_timed liftShift

/-- Its costed form is the costed tree of the distribution, with its sample node and its leaf,
not one sampling node. -/
example (n : ℕ) : liftShift.timed n =
    OracleAdv.Timed.delay 0 ((OracleAdv.Timed.rand (PMF.uniformFintype (Fin 8)) (fun _ => 0)
      OracleAdv.Timed.ret).bind fun i => (1, OracleAdv.Timed.ret (i.val + n))) := rfl

example (n : ℕ) : liftPMF (liftShift.timed n).2.erase.dist = liftShift n :=
  liftShift.erase_timed n

/-! ## Refusal -/

/-- A distribution given as a parameter has no sampling program. -/
noncomputable def paramShift (μ : PMF ℕ) : PMF ℕ := μ.map (· + 1)

/--
error: derive_timed: a distribution given as a parameter: `μ` is a binder of type `PMF ℕ`, which
has no sampling program from which its time is derived
-/
#guard_msgs (whitespace := lax) in
derive_timed paramShift

end CatCrypt.Tactics.DerivePMFTest
