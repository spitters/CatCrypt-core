/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCLoopbackObservation
public import CatCryptCore.Crypto.UCSimulator

/-!
# Testing equivalence and realization by environments

A system `R : Sys τ E O` is the open system `sysObj R` on the boundary `ioBoundary E O`, whose
input packets are the events `E` and whose output packets are the outputs `O`. An environment
`Z : Strat ζ E O` with a distinguisher `D : ζ → SPComp Bool` is the test `stratTest Z D`: on the
start packet it drives the system for `Z.rounds` activations through the wire and returns the bit
of `D` on its final state. Inside the composite of the Int construction the wire is traced by the
unbounded loopback, so the whole run happens within the first activation, and its observation is
the run of `Z` against `R` followed by `D` (`obsBit_sysObj_comp_stratHom`).

* `EmulatesΩ.realizes`: testing equivalence of `sysObj R` and `sysObj I` gives `Realizes R I 0`.
* `realizes_zero_iff`: `Realizes R I 0` holds exactly when every environment test observes the
  same bit distribution on `sysObj R` and on `sysObj I`.
* `EmulatesΩε`: the quantitative form, a bound `ε` on the bias of every test at every initial
  heap, with its triangle inequality, its composition theorems and its agreement with the bound
  of `Realizes` (`EmulatesΩε.realizes`).
-/

set_option autoImplicit false

@[expose] public section

namespace CatCrypt.Crypto.UCLoopbackObservation

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open CategoryTheory MonoidalCategory
open CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.SysCat
open CatCrypt.Crypto.UCTransparent.IntSys CatCrypt.Crypto.UCLoopbackOpenTheory
open Interaction Interaction.Open
open scoped ENNReal

variable {τ υ ζ E O : Type}

/-! ## Systems as open systems -/

/-- The boundary of a system with events `E` and outputs `O`: one input port carrying `E` and
one output port carrying `O`. -/
abbrev ioBoundary (E O : Type) : PortBoundary :=
  ⟨⟨Unit, fun _ => E⟩, ⟨Unit, fun _ => O⟩⟩

/-- The system `R` as an open system on `ioBoundary E O`. -/
noncomputable def sysObj (R : Sys τ E O) : loopOpenTheory.Obj (ioBoundary E O) :=
  ⟨⟦⟨τ, R.mapPorts (Sum.elim Empty.elim Sigma.snd) (fun o => Sum.inl ⟨(), o⟩)⟩⟧⟩

/-! ## Environments as tests -/

/-- The packet of the test after its environment state `z` with `k` rounds left: with no round
left the bit of `D`, otherwise the next event of `Z`. -/
noncomputable def stratEmit (Z : Strat ζ E O) (D : ζ → SPComp Bool) :
    ζ → ℕ → SPComp ((ζ × ℕ) ×
      (Interface.Packet bitBoundary.Out ⊕ Interface.Packet (ioBoundary E O).In))
  | z, 0 => SPComp.bind (D z) fun b => SPComp.pure ((z, 0), .inl ⟨(), b⟩)
  | z, k + 1 => SPComp.bind (Z.next z) fun a => SPComp.pure ((a.1, k), .inr ⟨(), a.2⟩)

/-- One step of the test of `Z` and `D`: an output of the system is observed by `Z` before the
next packet, and the start packet starts the emission. -/
noncomputable def stratStep (Z : Strat ζ E O) (D : ζ → SPComp Bool) :
    ζ × ℕ → Interface.Packet (ioBoundary E O).Out ⊕ Interface.Packet bitBoundary.In →
      SPComp ((ζ × ℕ) ×
        (Interface.Packet bitBoundary.Out ⊕ Interface.Packet (ioBoundary E O).In))
  | (z, k), .inl o => SPComp.bind (Z.obs z o.2) fun z' => stratEmit Z D z' k
  | (z, k), .inr _ => stratEmit Z D z k

/-- The test of `Z` and `D` as a system: state the environment state and the rounds left. -/
noncomputable def stratSys (Z : Strat ζ E O) (D : ζ → SPComp Bool) :
    Sys (ζ × ℕ) (Interface.Packet (ioBoundary E O).Out ⊕ Interface.Packet bitBoundary.In)
      (Interface.Packet bitBoundary.Out ⊕ Interface.Packet (ioBoundary E O).In) where
  init := (Z.init, Z.rounds)
  step := stratStep Z D

/-- The test of `Z` and `D` as a morphism `bObj (ioBoundary E O) ⟶ bObj bitBoundary`. -/
noncomputable def stratHom (Z : Strat ζ E O) (D : ζ → SPComp Bool) :
    bObj (ioBoundary E O) ⟶ bObj bitBoundary :=
  ⟨⟦⟨ζ × ℕ, stratSys Z D⟩⟧⟩

/-- The test of `Z` and `D`: the open system on `(ioBoundary E O).swap ⊗ bitBoundary` named by
`stratHom Z D`. -/
noncomputable def stratTest (Z : Strat ζ E O) (D : ζ → SPComp Bool) :
    loopOpenTheory.Obj ((ioBoundary E O).swap.tensor bitBoundary) :=
  nameEquiv (bObj (ioBoundary E O)) (bObj bitBoundary) (stratHom Z D) ≫
    (bMu (ioBoundary E O).swap bitBoundary).hom

/-- The run against the test of `Z` and `D` is composition with `stratHom Z D`. -/
theorem runTest_stratTest (W : loopOpenTheory.Obj (ioBoundary E O)) (Z : Strat ζ E O)
    (D : ζ → SPComp Bool) : runTest W (stratTest Z D) = W ≫ stratHom Z D := by
  rw [runTest_eq]
  simp [testHom, stratTest]

/-! ## The run of an environment inside the composite -/

/-- The relabelling of a packet of the test as an output of the traced kernel. -/
def kernelOut :
    Interface.Packet bitBoundary.Out ⊕ Interface.Packet (ioBoundary E O).In →
      (Interface.Packet bitBoundary.Out ⊕ Empty) ⊕ Interface.Packet (ioBoundary E O).In :=
  Sum.elim (fun b => .inl (.inl b)) Sum.inr

/-- One step of the system traced in the composite of `sysObj R` with `stratHom Z D`: the start
packet goes to the test, and an event on the wire goes to `R`, whose output goes to the test. -/
noncomputable def stratLoopStep (R : Sys τ E O) (Z : Strat ζ E O) (D : ζ → SPComp Bool) :
    τ × (ζ × ℕ) → (Empty ⊕ Interface.Packet bitBoundary.In) ⊕
      Interface.Packet (ioBoundary E O).In →
      SPComp ((τ × (ζ × ℕ)) ×
        ((Interface.Packet bitBoundary.Out ⊕ Empty) ⊕ Interface.Packet (ioBoundary E O).In))
  | _, .inl (.inl x) => x.elim
  | (t, s), .inl (.inr p) =>
    SPComp.map (fun r => ((t, r.1), kernelOut r.2)) (stratStep Z D s (.inr p))
  | (t, s), .inr e =>
    SPComp.bind (R.step t e.2) fun q =>
      SPComp.map (fun r => ((q.1, r.1), kernelOut r.2)) (stratStep Z D s (.inl ⟨(), q.2⟩))

/-- The system traced in the composite of `sysObj R` with `stratHom Z D`. -/
noncomputable def stratLoopSys (R : Sys τ E O) (Z : Strat ζ E O) (D : ζ → SPComp Bool) :
    Sys (τ × (ζ × ℕ)) ((Empty ⊕ Interface.Packet bitBoundary.In) ⊕
      Interface.Packet (ioBoundary E O).In)
      ((Interface.Packet bitBoundary.Out ⊕ Empty) ⊕ Interface.Packet (ioBoundary E O).In) where
  init := (R.init, (Z.init, Z.rounds))
  step := stratLoopStep R Z D

/-- The morphism traced in the composite of `sysObj R` with `stratHom Z D` is the class of
`stratLoopSys R Z D`. -/
theorem compKernel_sysObj_stratHom (R : Sys τ E O) (Z : Strat ζ E O) (D : ζ → SPComp Bool) :
    IntConstruction.compKernel (sysObj R) (stratHom Z D) =
      (⟦⟨τ × (ζ × ℕ), stratLoopSys R Z D⟩⟧ : (⟨(Empty ⊕ Interface.Packet bitBoundary.In) ⊕
        Interface.Packet (ioBoundary E O).In⟩ : SysCat) ⟶
        ⟨(Interface.Packet bitBoundary.Out ⊕ Empty) ⊕ Interface.Packet (ioBoundary E O).In⟩) := by
  simp only [IntConstruction.compKernel, swapRight_eq_homOfFun]
  refine Quotient.sound (Sys.StepMapOn.of_step (fun s => (s.2.1.1, s.2.2.2.1.1)) rfl
    fun u e => ?_).stepEq
  obtain ⟨⟨⟩, ⟨t, ⟨⟩⟩, ⟨⟩, ⟨⟨z, k⟩, ⟨⟩⟩, ⟨⟩⟩ := u
  rcases e with (x | p) | e
  · exact x.elim
  · simp only [IntConstruction.tensorUnit_neg, SPComp.map, IntConstruction.tensorUnit_pos,
      SysObj.idSys, SysObj.par, stratSys, SysObj.seq, Sys.seq_step, Sys.ofFun_step, swapFun,
      SPComp.pure_bind, SPComp.bind_assoc, Sys.par_step_inr, id_eq, Sys.par_step_inl,
      stratStep, stratLoopSys, stratLoopStep]
    congr 1
    funext a
    rcases a with ⟨_, _ | _⟩ <;> rfl
  · simp only [IntConstruction.tensorUnit_neg, SPComp.map, IntConstruction.tensorUnit_pos,
      SysObj.idSys, SysObj.par, stratSys, SysObj.seq, Sys.seq_step, Sys.ofFun_step, swapFun,
      SPComp.pure_bind, SPComp.bind_assoc, Sys.par_step_inl, Sys.mapPorts_step, stratStep,
      stratLoopSys, stratLoopStep]
    congr 1
    funext q
    congr 1
    funext z'
    congr 1
    funext a
    rcases a with ⟨_, _ | _⟩ <;> rfl

/-- Unfolding lemma of `stratLoopSys`: a step on the start packet is the emission of the test. -/
theorem stratLoopSys_step_start (R : Sys τ E O) (Z : Strat ζ E O) (D : ζ → SPComp Bool) (t : τ)
    (z : ζ) (k : ℕ) (p : Interface.Packet bitBoundary.In) :
    (stratLoopSys R Z D).step (t, (z, k)) (.inl (.inr p)) =
      SPComp.map (fun r => ((t, r.1), kernelOut r.2)) (stratEmit Z D z k) :=
  rfl

/-- A step of `stratLoopSys R Z D` on an event of the wire is a step of `R`, the observation of
its output by `Z`, and the step of the test on the start packet. -/
theorem stratLoopSys_step_wire (R : Sys τ E O) (Z : Strat ζ E O) (D : ζ → SPComp Bool) (t : τ)
    (z : ζ) (k : ℕ) (e : Interface.Packet (ioBoundary E O).In) :
    (stratLoopSys R Z D).step (t, (z, k)) (.inr e) =
      SPComp.bind (R.step t e.2) fun q => SPComp.bind (Z.obs z q.2) fun z' =>
        (stratLoopSys R Z D).step (q.1, (z', k)) (.inl (.inr startPkt)) := by
  simp only [stratLoopSys, stratLoopStep, stratStep, SPComp.map, SPComp.bind_assoc]

/-- The unbounded activation of `stratLoopSys R Z D` from an event of the wire. -/
theorem fbRunω_stratLoopSys_wire (R : Sys τ E O) (Z : Strat ζ E O) (D : ζ → SPComp Bool)
    (t : τ) (z : ζ) (k : ℕ) (e : Interface.Packet (ioBoundary E O).In) :
    (stratLoopSys R Z D).fbRunω (.inr e) (t, (z, k)) =
      SPComp.bind (R.step t e.2) fun q => SPComp.bind (Z.obs z q.2) fun z' =>
        (stratLoopSys R Z D).fbRunω (.inl (.inr startPkt)) (q.1, (z', k)) := by
  rw [Sys.fbRunω_eq, stratLoopSys_step_wire]
  simp only [SPComp.bind_assoc]
  congr 1
  funext q
  congr 1
  funext z'
  rw [Sys.fbRunω_eq]

/-- **The run of an environment in the composite.** The first activation of the composite of
`stratLoopSys R Z D` from the environment state `z` with `k` rounds left returns the bit of `D`
on the final state of the run of `Z` against `R` for `k` activations. -/
theorem fbRunω_stratLoopSys_start (R : Sys τ E O) (Z : Strat ζ E O) (D : ζ → SPComp Bool) :
    ∀ (k : ℕ) (z : ζ) (t : τ),
      SPComp.map (fun p => bitOf p.2)
          ((stratLoopSys R Z D).fbRunω (.inl (.inr startPkt)) (t, (z, k))) =
        SPComp.bind (loop R (fun _ => false) Z k (z, t, false)) fun c => D c.1 := by
  intro k
  induction k with
  | zero =>
    intro z t
    rw [Sys.fbRunω_eq, stratLoopSys_step_start]
    simp only [stratEmit, loop, kernelOut, bitOf, SPComp.map, SPComp.bind_assoc,
      SPComp.pure_bind]
    simp only [Sum.elim, SPComp.pure_bind]
    exact SPComp.bind_pure _
  | succ k ih =>
    intro z t
    simp only [SPComp.map] at ih
    rw [Sys.fbRunω_eq, stratLoopSys_step_start]
    simp only [stratEmit, loop, kernelOut, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
    simp only [Sum.elim]
    congr 1
    funext a
    rw [fbRunω_stratLoopSys_wire R Z D t a.1 k ⟨(), a.2⟩]
    simp only [SPComp.bind_assoc, Bool.or_false]
    congr 1
    funext q
    congr 1
    funext z'
    exact ih z' q.1

/-- **The observation of an environment test.** The bit observed by the test of `Z` and `D` on
the system `R` is the view of `Z` against `R` followed by `D`. -/
theorem obsBit_sysObj_comp_stratHom (R : Sys τ E O) (Z : Strat ζ E O) (D : ζ → SPComp Bool) :
    obsBit (sysObj R ≫ stratHom Z D) = SPComp.bind (view R Z) D := by
  have h : sysObj R ≫ stratHom Z D = ⟨⟦⟨_, (stratLoopSys R Z D).loopbackω⟩⟧⟩ :=
    IntConstruction.hom_ext (by rw [IntConstruction.comp_hom, compKernel_sysObj_stratHom]; rfl)
  rw [h]
  have hrun := fbRunω_stratLoopSys_start R Z D Z.rounds Z.init R.init
  simp only [obsBit, firstOut, SPComp.map_comp]
  simp only [view, run, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind] at hrun ⊢
  exact hrun

/-! ## Realization as testing equivalence -/

/-- **Testing equivalence gives realization.** If every test observes the same bit on `sysObj R`
and on `sysObj I`, then `R` realizes `I` with bound `0`. -/
theorem EmulatesΩ.realizes {R : Sys τ E O} {I : Sys υ E O}
    (h : EmulatesΩ (sysObj R) (sysObj I)) : Realizes R I (fun _ _ => 0) := by
  intro ζ Z
  have hZ := h (stratTest Z.input Z.dist)
  rw [runTest_stratTest, runTest_stratTest, obsBit_sysObj_comp_stratHom,
    obsBit_sysObj_comp_stratHom] at hZ
  simp [Env.gap, hZ]

/-- The distinguisher that returns whether the result and the heap are `x`. -/
noncomputable def pointTest {α : Type} (x : α × Heap) : α → SPComp Bool :=
  open Classical in fun a h => SDistr.pure (decide ((a, h) = x), h)

/-- The probability that `pointTest x` accepts after `c` is the mass of `c` at `x`. -/
theorem prTrue_bind_pointTest {α : Type} (c : SPComp α) (x : α × Heap) (h₀ : Heap) :
    prTrue (SPComp.bind c (pointTest x)) h₀ = c h₀ (some x) := by
  unfold prTrue
  simp only [SPComp.bind, pointTest, SDistr.bind, PMF.bind_apply]
  rw [ENNReal.tsum_comm, SDistr.tsum_option_eq_add]
  simp only [SDistr.fail, SDistr.pure, PMF.pure_apply, Option.some.injEq, Prod.mk.injEq,
    reduceCtorEq, ite_false, mul_zero, tsum_zero, zero_add]
  rw [tsum_eq_single x]
  · simp
  · intro a ha
    simp [ha]

/-- Two computations that every distinguisher accepts with the same probability, from every
initial heap, are equal. -/
theorem SPComp.eq_of_prTrue_bind {α : Type} {c c' : SPComp α}
    (h : ∀ (D : α → SPComp Bool) (h₀ : Heap),
      prTrue (SPComp.bind c D) h₀ = prTrue (SPComp.bind c' D) h₀) : c = c' := by
  funext h₀
  refine SDistr.eq_of_some_eq fun x => ?_
  rw [← prTrue_bind_pointTest c x h₀, ← prTrue_bind_pointTest c' x h₀]
  exact h _ _

/-- **Realization with bound `0` is equality of views.** -/
theorem realizes_zero_iff_view_eq {R : Sys τ E O} {I : Sys υ E O} :
    Realizes R I (fun _ _ => 0) ↔ ∀ (ζ : Type) (Z : Strat ζ E O), view R Z = view I Z := by
  constructor
  · intro h ζ Z
    refine SPComp.eq_of_prTrue_bind fun D h₀ => ?_
    have hZ : Env.gap (view R) (view I) ⟨Z, h₀, D⟩ ≤ 0 := h ζ ⟨Z, h₀, D⟩
    exact le_antisymm (tsub_eq_zero_iff_le.mp (nonpos_iff_eq_zero.mp (le_sup_left.trans hZ)))
      (tsub_eq_zero_iff_le.mp (nonpos_iff_eq_zero.mp (le_sup_right.trans hZ)))
  · intro h ζ Z
    simp [Env.gap, h ζ Z.input]

/-- **Realization with bound `0` is testing equivalence against environments.** `R` realizes
`I` with bound `0` exactly when every environment test observes the same bit on `sysObj R` and
on `sysObj I`. -/
theorem realizes_zero_iff {R : Sys τ E O} {I : Sys υ E O} :
    Realizes R I (fun _ _ => 0) ↔ ∀ (ζ : Type) (Z : Strat ζ E O) (D : ζ → SPComp Bool),
      obsBit (runTest (sysObj R) (stratTest Z D)) =
        obsBit (runTest (sysObj I) (stratTest Z D)) := by
  rw [realizes_zero_iff_view_eq]
  constructor
  · intro h ζ Z D
    rw [runTest_stratTest, runTest_stratTest, obsBit_sysObj_comp_stratHom,
      obsBit_sysObj_comp_stratHom, h]
  · intro h ζ Z
    refine SPComp.eq_of_prTrue_bind fun D h₀ => ?_
    have hZD := h ζ Z D
    rw [runTest_stratTest, runTest_stratTest, obsBit_sysObj_comp_stratHom,
      obsBit_sysObj_comp_stratHom] at hZD
    rw [hZD]

/-- **Realization behind a simulator from testing equivalence.** -/
theorem EmulatesΩ.realizesSim {τ υ E O EG OG : Type} {V : PubView E O} {W : PubView EG OG}
    {R : Sys τ E O} {I : Sys υ EG OG} {S : Simulator E O EG OG V W}
    (h : EmulatesΩ (sysObj R) (sysObj (S.withSub I))) : RealizesSim R I S (fun _ _ => 0) :=
  h.realizes

/-! ## Multi-call hybrids as morphisms -/

section Hybrid

variable {σ EG OG : Type}

/-- The multi-call hybrid `π` as a morphism `bObj (ioBoundary EG OG) ⟶ bObj (ioBoundary E O)`:
the class of `π.toSys` on the relabelled ports. -/
noncomputable def simHom (π : MultiHybrid σ E O EG OG) :
    bObj (ioBoundary EG OG) ⟶ bObj (ioBoundary E O) :=
  ⟨⟦⟨σ × ℕ, π.toSys.mapPorts (Sum.elim (fun o => Sum.inr o.2) (fun e => Sum.inl e.2))
    (Sum.elim (fun g => Sum.inr ⟨(), g⟩) (fun o => Sum.inl ⟨(), o⟩))⟩⟧⟩

/-- The relabelling of a decision of `π` as an output of the traced kernel. -/
def hybOut : EG ⊕ O →
    (Interface.Packet (ioBoundary E O).Out ⊕ Empty) ⊕ Interface.Packet (ioBoundary EG OG).In :=
  Sum.elim (fun g => .inr ⟨(), g⟩) (fun o => .inl (.inl ⟨(), o⟩))

/-- One step of the system traced in the composite of `sysObj I` with `simHom π`: an outer event
goes to `π`, and a call on the wire goes to `I`, whose answer goes to `π`. -/
noncomputable def hybLoopStep (π : MultiHybrid σ E O EG OG) (I : Sys υ EG OG) :
    υ × (σ × ℕ) → (Empty ⊕ Interface.Packet (ioBoundary E O).In) ⊕
      Interface.Packet (ioBoundary EG OG).In →
      SPComp ((υ × (σ × ℕ)) ×
        ((Interface.Packet (ioBoundary E O).Out ⊕ Empty) ⊕ Interface.Packet (ioBoundary EG OG).In))
  | _, .inl (.inl x) => x.elim
  | (t, s), .inl (.inr e) => SPComp.map (fun r => ((t, r.1), hybOut r.2)) (π.toSysStep s (.inl e.2))
  | (t, s), .inr g =>
    SPComp.bind (I.step t g.2) fun q =>
      SPComp.map (fun r => ((q.1, r.1), hybOut r.2)) (π.toSysStep s (.inr q.2))

/-- The system traced in the composite of `sysObj I` with `simHom π`. -/
noncomputable def hybLoopSys (π : MultiHybrid σ E O EG OG) (I : Sys υ EG OG) :
    Sys (υ × (σ × ℕ)) ((Empty ⊕ Interface.Packet (ioBoundary E O).In) ⊕
      Interface.Packet (ioBoundary EG OG).In)
      ((Interface.Packet (ioBoundary E O).Out ⊕ Empty) ⊕
        Interface.Packet (ioBoundary EG OG).In) where
  init := (I.init, (π.init, π.fuel))
  step := hybLoopStep π I

/-- The morphism traced in the composite of `sysObj I` with `simHom π` is the class of
`hybLoopSys π I`. -/
theorem compKernel_sysObj_simHom (π : MultiHybrid σ E O EG OG) (I : Sys υ EG OG) :
    IntConstruction.compKernel (sysObj I) (simHom π) =
      (⟦⟨υ × (σ × ℕ), hybLoopSys π I⟩⟧ : (⟨(Empty ⊕ Interface.Packet (ioBoundary E O).In) ⊕
        Interface.Packet (ioBoundary EG OG).In⟩ : SysCat) ⟶
        ⟨(Interface.Packet (ioBoundary E O).Out ⊕ Empty) ⊕
          Interface.Packet (ioBoundary EG OG).In⟩) := by
  simp only [IntConstruction.compKernel, swapRight_eq_homOfFun]
  refine Quotient.sound (Sys.StepMapOn.of_step (fun s => (s.2.1.1, s.2.2.2.1.1)) rfl
    fun u e => ?_).stepEq
  obtain ⟨⟨⟩, ⟨t, ⟨⟩⟩, ⟨⟩, ⟨⟨s, c⟩, ⟨⟩⟩, ⟨⟩⟩ := u
  rcases e with (x | p) | e
  · exact x.elim
  · simp only [IntConstruction.tensorUnit_neg, SPComp.map, IntConstruction.tensorUnit_pos,
      SysObj.idSys, SysObj.par, MultiHybrid.toSys, SysObj.seq, Sys.seq_step, Sys.ofFun_step,
      swapFun, SPComp.pure_bind, SPComp.bind_assoc, Sys.par_step_inr, id_eq, Sys.par_step_inl,
      Sys.mapPorts_step, MultiHybrid.toSysStep, Sum.elim_inr, hybLoopSys, hybLoopStep]
    congr 1
    funext a
    rcases a with ⟨_, _ | _⟩ <;> rfl
  · rcases c with _ | k
    · simp only [IntConstruction.tensorUnit_neg, SPComp.map, IntConstruction.tensorUnit_pos,
        SysObj.idSys, SysObj.par, MultiHybrid.toSys, SysObj.seq, Sys.seq_step, Sys.ofFun_step,
        swapFun, SPComp.pure_bind, SPComp.bind_assoc, Sys.par_step_inl, Sys.mapPorts_step,
        Sum.elim, MultiHybrid.toSysStep, hybLoopSys, hybLoopStep, hybOut]
    · simp only [IntConstruction.tensorUnit_neg, SPComp.map, IntConstruction.tensorUnit_pos,
        SysObj.idSys, SysObj.par, MultiHybrid.toSys, SysObj.seq, Sys.seq_step, Sys.ofFun_step,
        swapFun, SPComp.pure_bind, SPComp.bind_assoc, Sys.par_step_inl, Sys.mapPorts_step,
        Sum.elim, MultiHybrid.toSysStep, hybLoopSys, hybLoopStep]
      congr 1
      funext q
      congr 1
      funext a
      rcases a with ⟨_, _ | _⟩ <;> rfl

/-- Unfolding lemma of `hybLoopSys`: a step is `hybLoopStep`. -/
theorem hybLoopSys_step (π : MultiHybrid σ E O EG OG) (I : Sys υ EG OG) :
    (hybLoopSys π I).step = hybLoopStep π I :=
  rfl

/-- The unbounded activation of `hybLoopSys π I` from a call `g` on the wire, with `c` calls left,
is the drive of `π` against `I` from the call `g`. -/
theorem fbRunω_hybLoopSys_wire (π : MultiHybrid σ E O EG OG) (I : Sys υ EG OG) :
    ∀ (c : ℕ) (s : σ) (g : EG) (t : υ),
      SPComp.map (fun p => ((p.1.2.1, p.1.1), p.2))
          ((hybLoopSys π I).fbRunω (.inr ⟨(), g⟩) (t, (s, c))) =
        SPComp.map (fun p => ((p.1, p.2.1),
            (Sum.inl ⟨(), p.2.2⟩ : Interface.Packet (ioBoundary E O).Out ⊕ Empty)))
          (π.drive I c s (.inl g) t) := by
  intro c
  induction c with
  | zero =>
    intro s g t
    rw [Sys.fbRunω_eq]
    simp only [hybLoopSys_step, hybLoopStep, MultiHybrid.toSysStep, MultiHybrid.drive,
      SPComp.map, SPComp.bind_assoc, SPComp.pure_bind, hybOut, Sum.elim]
  | succ k ih =>
    intro s g t
    rw [Sys.fbRunω_eq]
    simp only [hybLoopSys_step, hybLoopStep, MultiHybrid.toSysStep, MultiHybrid.drive,
      SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
    congr 1
    funext q
    congr 1
    funext r
    rcases r with ⟨s', g' | o⟩
    · have h := ih s' g' q.1
      simp only [SPComp.map] at h
      simp only [hybOut, Sum.elim]
      exact h
    · simp [hybOut, MultiHybrid.drive, SPComp.pure_bind]

/-- **Composition with a subroutine.** The Int composite of the system `I` with the multi-call
hybrid `π` is the system `π.withSub I`. -/
theorem sysObj_comp_simHom (π : MultiHybrid σ E O EG OG) (I : Sys υ EG OG) :
    sysObj I ≫ simHom π = sysObj (π.withSub I) := by
  apply IntConstruction.hom_ext
  rw [IntConstruction.comp_hom, compKernel_sysObj_simHom]
  refine Quotient.sound (Sys.StepMapOn.of_step (fun u => (u.2.1, u.1)) rfl fun u e => ?_).stepEq
  obtain ⟨t, s, c⟩ := u
  rcases e with x | e
  · exact x.elim
  · rw [Sys.loopbackω_step, Sys.fbRunω_eq, Sys.mapPorts_step]
    simp only [hybLoopSys_step, hybLoopStep, MultiHybrid.toSysStep, MultiHybrid.withSub,
      SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
    congr 1
    funext r
    rcases r with ⟨s', g | o⟩
    · have h := fbRunω_hybLoopSys_wire π I π.fuel s' g t
      simp only [SPComp.map] at h
      simp only [hybOut, Sum.elim]
      exact h
    · simp [hybOut, MultiHybrid.drive, SPComp.pure_bind]

/-- **Realization behind a multi-call hybrid from testing equivalence in the Int construction.**
If `sysObj R` and the Int composite of `sysObj I` with `simHom π` are testing equivalent, then
`R` realizes `π.withSub I` with bound `0`. -/
theorem EmulatesΩ.realizes_withSub {R : Sys τ E O} {π : MultiHybrid σ E O EG OG}
    {I : Sys υ EG OG} (h : EmulatesΩ (sysObj R) (sysObj I ≫ simHom π)) :
    Realizes R (π.withSub I) (fun _ _ => 0) := by
  rw [sysObj_comp_simHom] at h
  exact h.realizes

end Hybrid

/-! ## The quantitative form -/

/-- `real` emulates `ideal` up to `ε`: from every initial heap, every test accepts on `real` and
on `ideal` with probabilities at distance at most `ε`. -/
def EmulatesΩε {Δ : PortBoundary} (ε : ℝ≥0∞) (real ideal : loopOpenTheory.Obj Δ) : Prop :=
  ∀ (K : loopOpenTheory.Obj (Δ.swap.tensor bitBoundary)) (h₀ : Heap),
    absDiff (prTrue (obsBit (runTest real K)) h₀) (prTrue (obsBit (runTest ideal K)) h₀) ≤ ε

/-- Emulation up to `ε` is the bound `ε` after every morphism into `bObj bitBoundary`. -/
theorem emulatesΩε_iff {Δ : PortBoundary} {ε : ℝ≥0∞} {real ideal : loopOpenTheory.Obj Δ} :
    EmulatesΩε ε real ideal ↔ ∀ (h : bObj Δ ⟶ bObj bitBoundary) (h₀ : Heap),
      absDiff (prTrue (obsBit (real ≫ h)) h₀) (prTrue (obsBit (ideal ≫ h)) h₀) ≤ ε := by
  constructor
  · intro H h h₀
    have hK : testHom (nameEquiv (bObj Δ) (bObj bitBoundary) h ≫
        (bMu Δ.swap bitBoundary).hom) = h := by
      simp [testHom]
    have := H (nameEquiv (bObj Δ) (bObj bitBoundary) h ≫ (bMu Δ.swap bitBoundary).hom) h₀
    rwa [runTest_eq, runTest_eq, hK] at this
  · intro H K h₀
    rw [runTest_eq, runTest_eq]
    exact H _ h₀

/-- Testing equivalence is emulation up to `0`. -/
theorem EmulatesΩ.emulatesΩε {Δ : PortBoundary} {real ideal : loopOpenTheory.Obj Δ}
    (h : EmulatesΩ real ideal) : EmulatesΩε 0 real ideal := fun K h₀ => by
  rw [h K, absDiff_self]

namespace EmulatesΩε

variable {Δ : PortBoundary}

/-- Every open system emulates itself up to `0`. -/
theorem refl (W : loopOpenTheory.Obj Δ) : EmulatesΩε 0 W W :=
  (EmulatesΩ.refl W).emulatesΩε

/-- Emulation up to `ε` is symmetric. -/
theorem symm {ε : ℝ≥0∞} {W₁ W₂ : loopOpenTheory.Obj Δ} (h : EmulatesΩε ε W₁ W₂) :
    EmulatesΩε ε W₂ W₁ := fun K h₀ => by
  rw [absDiff_comm]
  exact h K h₀

/-- Emulation up to `ε` is monotone in `ε`. -/
theorem mono {ε ε' : ℝ≥0∞} {W₁ W₂ : loopOpenTheory.Obj Δ} (h : EmulatesΩε ε W₁ W₂)
    (hε : ε ≤ ε') : EmulatesΩε ε' W₁ W₂ :=
  fun K h₀ => (h K h₀).trans hε

/-- **Triangle inequality.** -/
theorem trans {ε₁ ε₂ : ℝ≥0∞} {W₁ W₂ W₃ : loopOpenTheory.Obj Δ} (h₁₂ : EmulatesΩε ε₁ W₁ W₂)
    (h₂₃ : EmulatesΩε ε₂ W₂ W₃) : EmulatesΩε (ε₁ + ε₂) W₁ W₃ := fun K h₀ =>
  (absDiff_triangle _ _ _).trans (add_le_add (h₁₂ K h₀) (h₂₃ K h₀))

/-- Emulation up to `ε` is preserved by composition with a morphism of the Int construction. -/
theorem comp {Δ' : PortBoundary} {ε : ℝ≥0∞} {real ideal : loopOpenTheory.Obj Δ}
    (h : EmulatesΩε ε real ideal) (g : bObj Δ ⟶ bObj Δ') :
    EmulatesΩε ε (real ≫ g) (ideal ≫ g) := by
  rw [emulatesΩε_iff] at h ⊢
  intro k h₀
  simpa only [Category.assoc] using h (g ≫ k) h₀

/-- Emulation up to `ε` is invariant under `map`. -/
theorem map {Δ' : PortBoundary} {ε : ℝ≥0∞} (f : PortBoundary.Hom Δ Δ')
    {real ideal : loopOpenTheory.Obj Δ} (h : EmulatesΩε ε real ideal) :
    EmulatesΩε ε (loopOpenTheory.map f real) (loopOpenTheory.map f ideal) :=
  h.comp (bMap f)

/-- Wiring a context `C` on the right preserves emulation up to `ε`. -/
theorem wire_left {Δ₁ Γ Δ₂ : PortBoundary} {ε : ℝ≥0∞}
    {real ideal : loopOpenTheory.Obj (Δ₁.tensor Γ)} (h : EmulatesΩε ε real ideal)
    (C : loopOpenTheory.Obj (Γ.swap.tensor Δ₂)) :
    EmulatesΩε ε (loopOpenTheory.wire real C) (loopOpenTheory.wire ideal C) := by
  have hw : ∀ W : loopOpenTheory.Obj (Δ₁.tensor Γ), loopOpenTheory.wire W C =
      W ≫ ((bMu Δ₁ Γ).inv ≫ bObj Δ₁ ◁ (nameEquiv (bObj Γ) (bObj Δ₂)).symm
        (C ≫ (bMu Γ.swap Δ₂).inv) ≫ (bMu Δ₁ Δ₂).hom) := fun W => by
    simp only [wireHom, Category.assoc]
  rw [hw, hw]
  exact h.comp _

/-- Wiring a context `C` on the left preserves emulation up to `ε`. -/
theorem wire_right {Δ₁ Γ Δ₂ : PortBoundary} {ε : ℝ≥0∞} (C : loopOpenTheory.Obj (Δ₁.tensor Γ))
    {real ideal : loopOpenTheory.Obj (Γ.swap.tensor Δ₂)} (h : EmulatesΩε ε real ideal) :
    EmulatesΩε ε (loopOpenTheory.wire C real) (loopOpenTheory.wire C ideal) := by
  rw [wire_comm' C real, wire_comm' C ideal]
  exact ((h.map _).wire_left _).map _

/-- Putting a context `C` in parallel on the right preserves emulation up to `ε`. -/
theorem par_left {Δ₁ Δ₂ : PortBoundary} {ε : ℝ≥0∞} {real ideal : loopOpenTheory.Obj Δ₁}
    (h : EmulatesΩε ε real ideal) (C : loopOpenTheory.Obj Δ₂) :
    EmulatesΩε ε (loopOpenTheory.par real C) (loopOpenTheory.par ideal C) := by
  have hp : ∀ W : loopOpenTheory.Obj Δ₁, loopOpenTheory.par W C =
      W ≫ ((ρ_ (bObj Δ₁)).inv ≫ bObj Δ₁ ◁ C ≫ (bMu Δ₁ Δ₂).hom) := fun W => by
    change (λ_ _).inv ≫ (W ⊗ₘ C) ≫ (bMu Δ₁ Δ₂).hom = _
    rw [MonoidalCategory.tensorHom_def, unitors_inv_equal, Category.assoc,
      ← rightUnitor_inv_naturality_assoc]
  rw [hp, hp]
  exact h.comp _

/-- Putting a context `C` in parallel on the left preserves emulation up to `ε`. -/
theorem par_right {Δ₁ Δ₂ : PortBoundary} {ε : ℝ≥0∞} (C : loopOpenTheory.Obj Δ₁)
    {real ideal : loopOpenTheory.Obj Δ₂} (h : EmulatesΩε ε real ideal) :
    EmulatesΩε ε (loopOpenTheory.par C real) (loopOpenTheory.par C ideal) := by
  rw [← par_comm' real C, ← par_comm' ideal C]
  exact (h.par_left C).map _

/-- **Composition theorem for `wire`**, with the sum of the bounds. -/
theorem wire_compose {Δ₁ Γ Δ₂ : PortBoundary} {ε₁ ε₂ : ℝ≥0∞}
    {real₁ ideal₁ : loopOpenTheory.Obj (Δ₁.tensor Γ)}
    {real₂ ideal₂ : loopOpenTheory.Obj (Γ.swap.tensor Δ₂)} (h₁ : EmulatesΩε ε₁ real₁ ideal₁)
    (h₂ : EmulatesΩε ε₂ real₂ ideal₂) :
    EmulatesΩε (ε₁ + ε₂) (loopOpenTheory.wire real₁ real₂)
      (loopOpenTheory.wire ideal₁ ideal₂) :=
  (h₁.wire_left real₂).trans (wire_right ideal₁ h₂)

/-- **Composition theorem for `par`**, with the sum of the bounds. -/
theorem par_compose {Δ₁ Δ₂ : PortBoundary} {ε₁ ε₂ : ℝ≥0∞} {real₁ ideal₁ : loopOpenTheory.Obj Δ₁}
    {real₂ ideal₂ : loopOpenTheory.Obj Δ₂} (h₁ : EmulatesΩε ε₁ real₁ ideal₁)
    (h₂ : EmulatesΩε ε₂ real₂ ideal₂) :
    EmulatesΩε (ε₁ + ε₂) (loopOpenTheory.par real₁ real₂) (loopOpenTheory.par ideal₁ ideal₂) :=
  (h₁.par_left real₂).trans (par_right ideal₁ h₂)

/-- **Emulation up to `ε` gives realization at the bound `ε`.** -/
theorem realizes {ε : ℝ≥0∞} {R : Sys τ E O} {I : Sys υ E O}
    (h : EmulatesΩε ε (sysObj R) (sysObj I)) : Realizes R I (fun _ _ => ε) := by
  intro ζ Z
  have hZ := h (stratTest Z.input Z.dist) Z.heap
  rw [runTest_stratTest, runTest_stratTest, obsBit_sysObj_comp_stratHom,
    obsBit_sysObj_comp_stratHom] at hZ
  exact hZ

end EmulatesΩε

/-- **Realization at a constant bound is emulation against environment tests.** `R` realizes `I`
with the constant bound `ε` exactly when every environment test, from every initial heap,
accepts on `sysObj R` and on `sysObj I` with probabilities at distance at most `ε`. -/
theorem realizes_const_iff {ε : ℝ≥0∞} {R : Sys τ E O} {I : Sys υ E O} :
    Realizes R I (fun _ _ => ε) ↔ ∀ (ζ : Type) (Z : Strat ζ E O) (D : ζ → SPComp Bool)
      (h₀ : Heap), absDiff (prTrue (obsBit (runTest (sysObj R) (stratTest Z D))) h₀)
        (prTrue (obsBit (runTest (sysObj I) (stratTest Z D))) h₀) ≤ ε := by
  simp only [runTest_stratTest, obsBit_sysObj_comp_stratHom]
  exact ⟨fun h ζ Z D h₀ => h ζ ⟨Z, h₀, D⟩, fun h ζ Z => h ζ Z.input Z.dist Z.heap⟩

end CatCrypt.Crypto.UCLoopbackObservation
