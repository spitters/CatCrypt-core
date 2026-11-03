/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.ClassicalLiftFunctor

/-!
# The classical lift reflects realizations

The diamond distance of the classical embeddings of two families of sub-distributions equals
their statistical distance (`ClassicalDiamondLift.qdistDiamond_classicalEmbed_eq`): the bound
`qdistDiamond_classicalEmbed_le` holds with equality, since the reference register of
dimension `1` already attains the statistical distance.

For heap-independent classical systems `S` and `I`, the diamond-distance bound `ε` between the
quantum views of the lifts `liftQSys S` and `liftQSys I`, against every environment
`liftStrat Z` with `Z` a classical strategy with heap-independent activations (`StratPure Z`),
holds exactly when every classical environment whose strategy has heap-independent activations
distinguishes `S` from `I` with advantage at most `ε`; the initial heap and the distinguisher
of the classical environment are arbitrary (`ClassicalLiftSys.quc_liftQSys_iff`).

The strategies are restricted to heap-independent ones on both sides. The lifted environment
`liftStrat Z` runs each activation of `Z` from the empty heap and discards the final heap, so
for a strategy that keeps state on the heap between activations it is a different
environment. Such a strategy is reduced to a heap-independent one on the state type
`ζ × Heap` that carries its heap in its state (`carryStrat`); against heap-independent systems
the carried environment has the same advantage (`adv_carryEnv`). Hence the quantum bound for
every state type gives the classical realization `Realizes S I fun _ _ => ε` against every
classical environment (`quc_liftQSys_iff_realizes`).

Search words: classical lift, reflection, converse, quantum UC, diamond norm, statistical
distance, carried heap.

## Main results

* `ClassicalDiamondLift.qdistDiamond_classicalEmbed_eq`: diamond distance of diagonal
  embeddings equals the statistical distance.
* `ClassicalLiftSys.view_isPure`: the view of a heap-independent strategy against a
  heap-independent system is heap-independent.
* `ClassicalLiftSys.adv_le_of_quc_liftQSys`: the converse of `quc_liftQSys_of_realizes_le`.
* `ClassicalLiftSys.quc_liftQSys_iff`: both directions.
* `ClassicalLiftSys.loop_carryStrat`, `ClassicalLiftSys.adv_carryEnv`: the carried-heap
  simulation of a heap-using strategy.
* `ClassicalLiftSys.quc_liftQSys_iff_realizes`: both directions, for all classical
  environments.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Quantum.ClassicalDiamondLift

open CatCrypt.Prob CatCrypt.Quantum CatCrypt.Quantum.TensorProduct
open CatCrypt.Crypto.UCMonad.DiamondNorm UCMonad.QuantumUC UCMonad.SDistrUC
open scoped ENNReal Matrix ComplexOrder

variable {d : ℕ} {α β : Type}

/-- The statistical distance of two families of sub-distributions is at most the diamond
distance of their classical embeddings: the reference register of dimension `1` attains it. -/
theorem sdistD_le_qdistDiamond_classicalEmbed [NeZero d] (f g : α → SDistr β) :
    sdistD f g ≤ qdistDiamond (fun a => classicalEmbed (d := d) (f a))
        (fun a => classicalEmbed (d := d) (g a))
        (classicalEmbed_isCPChannel f) (classicalEmbed_isCPChannel g) := by
  unfold qdistDiamond
  refine le_iSup_of_le 1 ?_
  rw [withRef_classicalEmbed f, withRef_classicalEmbed g]
  have : NeZero (d * 1) := ⟨by simpa using NeZero.ne d⟩
  exact le_of_eq (classicalEmbed_sdist_eq f g)

/-- **Diamond distance of diagonal channels.** The diamond distance of the classical embeddings
of two families of sub-distributions is their statistical distance. -/
theorem qdistDiamond_classicalEmbed_eq [NeZero d] (f g : α → SDistr β) :
    qdistDiamond (fun a => classicalEmbed (d := d) (f a))
        (fun a => classicalEmbed (d := d) (g a))
        (classicalEmbed_isCPChannel f) (classicalEmbed_isCPChannel g) = sdistD f g :=
  le_antisymm (qdistDiamond_classicalEmbed_le f g) (sdistD_le_qdistDiamond_classicalEmbed f g)

end CatCrypt.Quantum.ClassicalDiamondLift

namespace CatCrypt.Quantum.ClassicalLiftSys

open CatCrypt.Core CatCrypt.Prob
open CatCrypt.Crypto.UCTransparent CatCrypt.Quantum.ReactiveUC
open CatCrypt.Crypto.UCMonad.DiamondNorm UCMonad.SDistrUC
open CatCrypt.Crypto.SDistrLift
open CatCrypt.Crypto.UCConcrete (Env)
open CatCrypt.Crypto (prTrue)
open scoped ENNReal

variable {τ υ E O ζ α : Type} {d : ℕ}

/-- The acceptance probability from the heap `h₀` is the weight of `true` in the results of the
run from `h₀`, the final heap discarded. -/
theorem prTrue_eq_bind_fst (G : SPComp Bool) (h₀ : Heap) :
    prTrue G h₀ = ((G h₀).bind fun p => SDistr.pure p.1) (some true) := by
  rw [prTrue, SDistr.bind_apply_some']
  have key : ∀ g : SDistr (Bool × Heap),
      ∑' h, g (some (true, h)) = ∑' p, g (some p) * SDistr.pure p.1 (some true) := by
    intro g
    rw [ENNReal.tsum_prod', tsum_bool]
    simp [SDistr.pure_apply_some]
  exact key (G h₀)

/-- After a heap-independent computation sampling `μ`, the acceptance probability of a
distinguisher `D` from the heap `h₀` is that of the sub-distribution `μ` followed by the runs of
`D` from `h₀`. -/
theorem prTrue_bind_of_isPure {c : SPComp α} {μ : SDistr α}
    (hμ : ∀ h, c h = μ.bind fun a => SDistr.pure (a, h)) (D : α → SPComp Bool) (h₀ : Heap) :
    prTrue (c.bind D) h₀ =
      prTrueD (μ.bind fun a => (D a h₀).bind fun p => SDistr.pure p.1) := by
  rw [prTrue_eq_bind_fst, SPComp.bind_def, hμ, prTrueD]
  simp only [SDistr.bind_assoc, SDistr.pure_bind]

/-- The joint run of a heap-independent strategy and a heap-independent system is
heap-independent. -/
theorem loop_isPure {S : Sys τ E O} (hS : S.HeapPure) {Z : Strat ζ E O} (hZ : StratPure Z)
    (bad : τ → Bool) (n : ℕ) : ∀ c, SPComp.IsPure (loop S bad Z n c) := by
  induction n with
  | zero => intro c; exact SPComp.pure_isPure c
  | succ n ih =>
    intro c
    exact SPComp.bind_isPure (hZ.1 _) fun a => SPComp.bind_isPure (hS _ _) fun p =>
      SPComp.bind_isPure (hZ.2 _ _) fun z => ih _

/-- The view of a heap-independent strategy against a heap-independent system is
heap-independent. -/
theorem view_isPure {S : Sys τ E O} (hS : S.HeapPure) {Z : Strat ζ E O} (hZ : StratPure Z) :
    SPComp.IsPure (view S Z) :=
  SPComp.bind_isPure (loop_isPure hS hZ _ _ _) fun _ => SPComp.pure_isPure _

/-- The advantage of a classical environment whose strategy is heap-independent, from any
initial heap and with any distinguisher, is at most the statistical distance of the views from
the empty heap over all heap-independent strategies. -/
theorem adv_le_sdistD_heapFree_view {S : Sys τ E O} {I : Sys υ E O} (hS : S.HeapPure)
    (hI : I.HeapPure) (Z : Env (Strat ζ E O) ζ) (hZ : StratPure Z.input) :
    adv S I Z ≤ sdistD (fun Z : {Z : Strat ζ E O // StratPure Z} => heapFree (view S Z.1))
      (fun Z => heapFree (view I Z.1)) := by
  obtain ⟨μS, hμS⟩ := view_isPure hS hZ
  obtain ⟨μI, hμI⟩ := view_isPure hI hZ
  have eS : heapFree (view S Z.input) = μS := heapFree_eq_of_forall hμS
  have eI : heapFree (view I Z.input) = μI := heapFree_eq_of_forall hμI
  rw [adv_eq, prTrue_bind_of_isPure hμS, prTrue_bind_of_isPure hμI]
  refine le_iSup_of_le (fun z => (Z.dist z Z.heap).bind fun p => SDistr.pure p.1)
    (le_iSup_of_le ⟨Z.input, hZ⟩ ?_)
  simp only [eS, eI]
  exact le_of_eq (by simp [CatCrypt.Crypto.absDiff, absDiffD])

/-- **The lift reflects realizations.** If the quantum views of the lifts of heap-independent
systems are within diamond distance `ε` against every environment `liftStrat Z` with `Z` a
heap-independent strategy on the state type `ζ`, then every classical environment on `ζ` whose
strategy is heap-independent, from any initial heap and with any distinguisher, has advantage
at most `ε`. -/
theorem adv_le_of_quc_liftQSys [NeZero d] {S : Sys τ E O} {I : Sys υ E O}
    (hS : S.HeapPure) (hI : I.HeapPure) {ε : ℝ≥0∞}
    (h : QUCEmulatesDiamond ε
      (fun Z : {Z : Strat ζ E O // StratPure Z} =>
        (qview (liftQSys (d := d) S) (liftStrat Z.1)).toQComp)
      (fun Z => (qview (liftQSys I) (liftStrat Z.1)).toQComp)
      (fun Z => CPComp.branch_cp (qview (liftQSys S) (liftStrat Z.1)))
      (fun Z => CPComp.branch_cp (qview (liftQSys I) (liftStrat Z.1))))
    (Z : Env (Strat ζ E O) ζ) (hZ : StratPure Z.input) : adv S I Z ≤ ε := by
  have h' : QUCEmulatesDiamond ε
      (fun Z : {Z : Strat ζ E O // StratPure Z} => classicalEmbed (d := d) (heapFree (view S Z.1)))
      (fun Z => classicalEmbed (heapFree (view I Z.1)))
      (ClassicalDiamondLift.classicalEmbed_isCPChannel _)
      (ClassicalDiamondLift.classicalEmbed_isCPChannel _) :=
    quc_congr _ _ h (funext fun Z => qview_liftQSys_toQComp hS Z)
      (funext fun Z => qview_liftQSys_toQComp hI Z)
  exact (adv_le_sdistD_heapFree_view hS hI Z hZ).trans
    ((ClassicalDiamondLift.sdistD_le_qdistDiamond_classicalEmbed _ _).trans h')

/-- **Classical and quantum realization agree on the lifts.** For heap-independent systems,
every classical environment with a heap-independent strategy (any initial heap, any
distinguisher) has advantage at most `ε` exactly when, for every state type `ζ`, the quantum
views of the lifts are within diamond distance `ε` against the environments `liftStrat Z` of
the heap-independent strategies `Z` on `ζ`. -/
theorem quc_liftQSys_iff [NeZero d] {S : Sys τ E O} {I : Sys υ E O}
    (hS : S.HeapPure) (hI : I.HeapPure) {ε : ℝ≥0∞} :
    (∀ (ζ : Type) (Z : Env (Strat ζ E O) ζ), StratPure Z.input → adv S I Z ≤ ε) ↔
      ∀ ζ : Type, QUCEmulatesDiamond ε
        (fun Z : {Z : Strat ζ E O // StratPure Z} =>
          (qview (liftQSys (d := d) S) (liftStrat Z.1)).toQComp)
        (fun Z => (qview (liftQSys I) (liftStrat Z.1)).toQComp)
        (fun Z => CPComp.branch_cp (qview (liftQSys S) (liftStrat Z.1)))
        (fun Z => CPComp.branch_cp (qview (liftQSys I) (liftStrat Z.1))) := by
  constructor
  · intro h ζ
    have hsd : sdistD (fun Z : {Z : Strat ζ E O // StratPure Z} => heapFree (view S Z.1))
        (fun Z => heapFree (view I Z.1)) ≤ ε := by
      refine iSup₂_le fun D a => ?_
      have hg := h ζ ⟨a.1, Heap.empty, fun z => sdistrToSPComp (D z)⟩ a.2
      simp only [adv_eq, prTrue_eq_heapFree, heapFree_bind_sdistrToSPComp] at hg
      exact hg
    exact quc_congr _ _ (ClassicalDiamondLift.classical_to_quantum_diamond_lift _ _ hsd)
      (funext fun Z => (qview_liftQSys_toQComp hS Z).symm)
      (funext fun Z => (qview_liftQSys_toQComp hI Z).symm)
  · intro h ζ Z hZ
    exact adv_le_of_quc_liftQSys hS hI (h ζ) Z hZ

/-! ## Environments that keep state on the heap -/

/-- The strategy `Z` with its heap carried in its own state: from the state `(z, h)`, each
activation runs the activation of `Z` at `z` from the heap `h`, stores the final heap in the new
state, and leaves the actual heap unchanged. The initial carried heap is `h₀`. -/
noncomputable def carryStrat (Z : Strat ζ E O) (h₀ : Heap) : Strat (ζ × Heap) E O where
  rounds := Z.rounds
  init := (Z.init, h₀)
  next zh h' := (Z.next zh.1 zh.2).bind fun p => SDistr.pure (((p.1.1, p.2), p.1.2), h')
  obs zh o h' := (Z.obs zh.1 o zh.2).bind fun p => SDistr.pure (p, h')
  next_noFail zh h' :=
    CatCrypt.Crypto.Assumptions.SPComp.bind_noFail
      (f := fun (p : ζ × E) (hf : Heap) => SDistr.pure (((p.1, hf), p.2), h'))
      (Z.next_noFail zh.1)
      (fun p hf => CatCrypt.Crypto.SPComp.pure_noFail ((p.1, hf), p.2) h') zh.2
  obs_noFail zh o h' :=
    CatCrypt.Crypto.Assumptions.SPComp.bind_noFail
      (f := fun (p : ζ) (hf : Heap) => SDistr.pure ((p, hf), h')) (Z.obs_noFail zh.1 o)
      (fun p hf => CatCrypt.Crypto.SPComp.pure_noFail (p, hf) h') zh.2

/-- The activations of a strategy with carried heap are heap-independent. -/
theorem carryStrat_stratPure (Z : Strat ζ E O) (h₀ : Heap) : StratPure (carryStrat Z h₀) :=
  ⟨fun zh => ⟨(Z.next zh.1 zh.2).bind fun p => SDistr.pure ((p.1.1, p.2), p.1.2),
      fun h' => by simp [carryStrat, SDistr.bind_assoc, SDistr.pure_bind]⟩,
    fun zh o => ⟨Z.obs zh.1 o zh.2,
      fun h' => by simp [carryStrat]⟩⟩

/-- Against a heap-independent system, the joint run of the strategy with carried heap is the
joint run of the original strategy from the carried heap, its final heap moved into the state
and the actual heap left unchanged. -/
theorem loop_carryStrat {S : Sys τ E O} (hS : S.HeapPure) (Z : Strat ζ E O) (h₀ : Heap)
    (bad : τ → Bool) (n : ℕ) : ∀ (zh : ζ × Heap) (t : τ) (b : Bool) (h' : Heap),
      loop S bad (carryStrat Z h₀) n (zh, t, b) h' =
        (loop S bad Z n (zh.1, t, b) zh.2).bind
          fun q => SDistr.pure (((q.1.1, q.2), q.1.2.1, q.1.2.2), h') := by
  choose μ hstep using hS
  induction n with
  | zero =>
    intro zh t b h'
    simp [loop, SPComp.pure_def, SDistr.pure_bind]
  | succ n ih =>
    intro zh t b h'
    simp only [loop, SPComp.bind, ih]
    simp only [carryStrat, hstep, SDistr.bind_assoc, SDistr.pure_bind]

/-- The environment `Z` with its heap carried in the state of its strategy: the strategy
`carryStrat Z.input Z.heap`, the empty initial heap, and the distinguisher that runs `Z.dist`
from the carried heap. -/
noncomputable def carryEnv (Z : Env (Strat ζ E O) ζ) : Env (Strat (ζ × Heap) E O) (ζ × Heap) :=
  ⟨carryStrat Z.input Z.heap, Heap.empty, fun zh _ => Z.dist zh.1 zh.2⟩

/-- Against a heap-independent system, the run of the view followed by the distinguisher of the
carried environment is that of the original environment from its initial heap. -/
theorem view_bind_carryEnv {S : Sys τ E O} (hS : S.HeapPure) (Z : Env (Strat ζ E O) ζ) :
    SPComp.bind (view S (carryEnv Z).input) (carryEnv Z).dist Heap.empty =
      SPComp.bind (view S Z.input) Z.dist Z.heap := by
  simp only [carryEnv, view, run, SPComp.map, SPComp.bind, SPComp.pure]
  rw [loop_carryStrat hS]
  simp only [carryStrat, SDistr.bind_assoc, SDistr.pure_bind]

/-- For heap-independent systems, the carried environment has the advantage of the original
one. -/
theorem adv_carryEnv {S : Sys τ E O} {I : Sys υ E O} (hS : S.HeapPure) (hI : I.HeapPure)
    (Z : Env (Strat ζ E O) ζ) : adv S I (carryEnv Z) = adv S I Z := by
  have e : ∀ {σ : Type} (T : Sys σ E O), T.HeapPure →
      prTrue (SPComp.bind (view T (carryEnv Z).input) (carryEnv Z).dist) (carryEnv Z).heap =
        prTrue (SPComp.bind (view T Z.input) Z.dist) Z.heap := fun T hT => by
    unfold prTrue
    exact congrArg (fun μ => ∑' h, μ (some (true, h))) (view_bind_carryEnv hT Z)
  rw [adv_eq, adv_eq, e S hS, e I hI]

/-- **The lift reflects realizations, for every environment.** If the quantum views of the
lifts of heap-independent systems are within diamond distance `ε` against every environment
`liftStrat Z` with `Z` a heap-independent strategy, for every state type, then every classical
environment, including one whose strategy keeps state on the heap, has advantage at most `ε`. -/
theorem realizes_of_quc_liftQSys [NeZero d] {S : Sys τ E O} {I : Sys υ E O}
    (hS : S.HeapPure) (hI : I.HeapPure) {ε : ℝ≥0∞}
    (h : ∀ ζ : Type, QUCEmulatesDiamond ε
      (fun Z : {Z : Strat ζ E O // StratPure Z} =>
        (qview (liftQSys (d := d) S) (liftStrat Z.1)).toQComp)
      (fun Z => (qview (liftQSys I) (liftStrat Z.1)).toQComp)
      (fun Z => CPComp.branch_cp (qview (liftQSys S) (liftStrat Z.1)))
      (fun Z => CPComp.branch_cp (qview (liftQSys I) (liftStrat Z.1)))) :
    Realizes S I fun _ _ => ε := fun ζ Z =>
  (adv_carryEnv hS hI Z).symm.le.trans
    (adv_le_of_quc_liftQSys hS hI (h (ζ × Heap)) (carryEnv Z) (carryStrat_stratPure _ _))

/-- **Classical and quantum realization agree on the lifts, for all environments.** For
heap-independent systems, `S` realizes `I` at the constant bound `ε` against every classical
environment exactly when, for every state type, the quantum views of the lifts are within
diamond distance `ε` against the environments `liftStrat Z` of the heap-independent
strategies `Z`. -/
theorem quc_liftQSys_iff_realizes [NeZero d] {S : Sys τ E O} {I : Sys υ E O}
    (hS : S.HeapPure) (hI : I.HeapPure) {ε : ℝ≥0∞} :
    Realizes S I (fun _ _ => ε) ↔
      ∀ ζ : Type, QUCEmulatesDiamond ε
        (fun Z : {Z : Strat ζ E O // StratPure Z} =>
          (qview (liftQSys (d := d) S) (liftStrat Z.1)).toQComp)
        (fun Z => (qview (liftQSys I) (liftStrat Z.1)).toQComp)
        (fun Z => CPComp.branch_cp (qview (liftQSys S) (liftStrat Z.1)))
        (fun Z => CPComp.branch_cp (qview (liftQSys I) (liftStrat Z.1))) :=
  ⟨fun h => (quc_liftQSys_iff hS hI).1 fun ζ Z _ => h ζ Z, realizes_of_quc_liftQSys hS hI⟩

end CatCrypt.Quantum.ClassicalLiftSys
