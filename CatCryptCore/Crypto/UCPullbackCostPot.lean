/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCSimulatorCostPotComp
public import CatCryptCore.Crypto.UCPullbackCost
public import CatCryptCore.Crypto.UCConcreteTimed
public import CatCryptCore.Crypto.UCParallelTimed

/-!
# Costed pullbacks through simulators with potential time bounds

The time of an environment reduced by a simulator whose steps cost at most `a + b * (Φ s + g x)`
(`MultiHybrid.Timed.PotentialBound`, `UCSimulatorCostPot.lean`) depends on the potential `Φ` of
the simulator's state, which grows with the import the simulator receives. The import of the
environment enters its time bound as a fifth number `M`.

A *potential bound* of a costed strategy (`Strat.Timed.PotBound ZT hE gO n o β δ`) is an
invariant and a potential `Ψ` on its states (with `Ψm` on the states between a `next` and an
`obs` step): a `next` step from `z` costs at most `n + β * Ψ z` and passes on an event `e` with
`Ψm z' + hE e ≤ Ψ z + δ`; an `obs` step on the answer `g` costs at most `o + β * (Ψm z + gO g)`
and returns states with `Ψ z' ≤ Ψm z + gO g + δ`. The number `δ` is the potential created per
activation. An environment of import `M` (`EnvImportBound`) is one whose costed strategy has a
potential bound with `hE` the size of the event, `gO = 0`, `β = δ = 0` and initial potential at
most `M`: its potential is the import it may still pass on.

The costed reduction of a strategy by a costed multi-call simulator with a potential time bound
(`MultiHybrid.Timed.reducePot`) has a potential bound whose potential is the sum of the
potential of the strategy and of the simulator, and of the import of the message pending
between them. The interface between the strategy and the simulator conserves import up to `κ`
per message, and the potential created per activation of the reduced strategy is
`δ + κ + hEG idle`. The reduction applies to a reduced strategy again, which gives the pullback
through a composite simulator (`MultiHybrid.Timed.reduce_reduce_runBound_import`): the
potentials of the two factors add, the constants `β` add, and the import `κ` created at the
middle interface accumulates over the activations of the run of the twice reduced strategy, so
that it enters the step bound multiplied by `b₁ + b₂` and by the number of activations.

A potential bound gives a graded time bound `StratRunBound` with the answers of import at most
`A` (`Strat.Timed.PotBound.stratRunBound`), whose bound is uniform over the first `q`
activations; this is the environment bound `EnvTimeBoundInv Z ZT ZE Out n o q tD`, the form of
`EnvTimeBound` over a graded strategy bound. A *costed import pullback*
(`ImportPullback E O E' O'`) is an environment pullback with costed reductions that send an
environment of time `(n, o, q, tD)` and import `M` to an environment of time
`(n + nextC q M, o + obsC q M, roundsMul * q, tD + distC)` whose answers have the interface
predicate `Out`. The time-graded pullback law with import (`ImportPullback.realizesTime_map`)
maps realization against the environments of the reduced time (`RealizesTimeInv`) to
realization against the environments of time `(n, o, q, tD)` and import `M`
(`RealizesTimeImport`). The costed reduction of a strategy of import `M` by a multi-call
simulator with a potential time bound whose import of the outer events is at most `c` times
their size has the graded time bound of such a pullback
(`MultiHybrid.Timed.reduce_runBound_import`), and the multi-call simulator is a costed import
pullback (`MultiHybrid.toImportPullback`). The potential certificate of a composite
(`Simulator.Timed.PotCert`, with the import `d` created per activation) gives the time bound of
the twice reduced strategy (`MultiHybrid.Timed.potCert_comp_runBound_import`).

Search words: potential, import, Canetti polynomial time, costed pullback, environment
reduction, activation time, time certificate, simulator, composition.

## Main definitions

* `Strat.Timed.PotBound`: the potential bound of a costed strategy.
* `EnvTimeBoundInv`, `EnvImportBound`: the graded time of an environment, and the time and
  import of an environment.
* `RealizesTimeInv`, `RealizesTimeImport`: realization against those environments.
* `ImportPullback`: costed import pullbacks.
* `MultiHybrid.Timed.reducePot`: the potential bound of the costed multi-call reduction.
* `MultiHybrid.toImportPullback`: a multi-call simulator with a potential time bound as a costed
  import pullback.

## Main results

* `Strat.Timed.PotBound.stratRunBound`, `Strat.Timed.PotBound.runBound`,
  `Strat.Timed.PotBound.envTimeBoundInv`: the graded time bound of a strategy with a potential
  bound.
* `EnvTimeBound.envTimeBoundInv`, `RealizesTimeInv.realizesTime`: the uniform bound is a graded
  bound.
* `ImportPullback.realizesTime_map`: the time-graded pullback law with import.
* `MultiHybrid.Timed.reduce_runBound_import`: the time of a strategy of import `M` reduced by a
  multi-call simulator with a potential time bound.
* `MultiHybrid.Timed.reduce_reduce_runBound_import`: the same for two multi-call simulators in
  sequence.
* `MultiHybrid.Timed.potCert_comp_runBound_import`: the same from the potential certificate of
  their composite.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open scoped ENNReal

/-- The potential bound of a costed strategy with the import `hE` of the events it passes on,
the import `gO` of the answers it receives, the constants `n`, `o`, `β` and the potential `δ`
created per activation: an invariant `Inv` with a potential `Ψ` on the states before a `next`
step, and an invariant `Mid` with a potential `Ψm` on the states before an `obs` step. A `next`
step from `z` costs at most `n + β * Ψ z` and returns states `z'` of `Mid` with events `e`
where `Ψm z' + hE e ≤ Ψ z + δ`; an `obs` step from `z` on `g` costs at most
`o + β * (Ψm z + gO g)` and returns states `z'` of `Inv` with `Ψ z' ≤ Ψm z + gO g + δ`. -/
structure Strat.Timed.PotBound {ζ E O : Type} (ZT : Strat.Timed ζ E O) (hE : E → ℕ)
    (gO : O → ℕ) (n o β δ : ℕ) where
  /-- The invariant before a `next` step. -/
  Inv : ζ → Prop
  /-- The invariant before an `obs` step. -/
  Mid : ζ → Prop
  /-- The potential before a `next` step. -/
  Ψ : ζ → ℕ
  /-- The potential before an `obs` step. -/
  Ψm : ζ → ℕ
  /-- The initial state satisfies the invariant. -/
  init : Inv ZT.init
  /-- The time and the potential clause of a `next` step. -/
  next : ∀ z, Inv z →
    SPTree.Timed.stepTime (ZT.nextCost z, ZT.next z) ≤ n + β * Ψ z ∧
    SPTree.Timed.AllRet (fun r => Mid r.1 ∧ Ψm r.1 + hE r.2 ≤ Ψ z + δ) (ZT.next z)
  /-- The time and the potential clause of an `obs` step. -/
  obs : ∀ z g, Mid z →
    SPTree.Timed.stepTime (ZT.obsCost z g, ZT.obs z g) ≤ o + β * (Ψm z + gO g) ∧
    SPTree.Timed.AllRet (fun z' => Inv z' ∧ Ψ z' ≤ Ψm z + gO g + δ) (ZT.obs z g)

namespace Strat.Timed.PotBound

variable {ζ E O : Type} {ZT : Strat.Timed ζ E O} {hE : E → ℕ} {gO : O → ℕ} {n o β δ : ℕ}

/-- The bound `Ψ₀ + i * (2 * δ + A)` on the potential after `i` activations whose answers have
import at most `A`, with `Ψ₀` the initial potential. -/
def bnd (P : ZT.PotBound hE gO n o β δ) (A i : ℕ) : ℕ := P.Ψ ZT.init + i * (2 * δ + A)

/-- **Graded time of a strategy with a potential bound.** Against answers of import at most
`A`, activation `i` costs at most `n + β * bnd i` in `next` and `o + β * (bnd i + δ + A)` in
`obs`, on the states of potential at most `bnd i`. -/
theorem stratRunBound (P : ZT.PotBound hE gO n o β δ) (A : ℕ) :
    StratRunBound ZT.next ZT.nextCost ZT.obs ZT.obsCost
      (fun i z => P.Inv z ∧ P.Ψ z ≤ P.bnd A i) (fun i z => P.Mid z ∧ P.Ψm z ≤ P.bnd A i + δ)
      (fun _ _ => True) (fun _ g => gO g ≤ A)
      (fun i => n + β * P.bnd A i) (fun i => o + β * (P.bnd A i + δ + A)) where
  next_time i z h := (P.next z h.1).1.trans (by gcongr; exact h.2)
  next_ret i z h := SPTree.Timed.allRet_mono (fun r hr => ⟨⟨hr.1, by omega⟩, trivial⟩) _
    (P.next z h.1).2
  obs_time i z g h hg := (P.obs z g h.1).1.trans (by gcongr; omega)
  obs_ret i z g h hg := SPTree.Timed.allRet_mono (fun z' hz => ⟨hz.1, by
    simp only [bnd, add_mul, one_mul] at h hz ⊢
    omega⟩) _ (P.obs z g h.1).2

/-- **Uniform time of the first `q` activations.** If `Ψ₀ + q * (2 * δ + A) ≤ B` for the initial
potential `Ψ₀`, the strategy has a graded time bound against the answers of import at most `A`
from its initial state, at most `n + β * B` in `next` and `o + β * (B + δ + A)` in `obs` for the
first `q` activations. -/
theorem runBound (P : ZT.PotBound hE gO n o β δ) (A : ℕ) {q B : ℕ}
    (hB : P.Ψ ZT.init + q * (2 * δ + A) ≤ B) :
    ∃ (Inv Mid : ℕ → ζ → Prop) (tN tO : ℕ → ℕ),
      StratRunBound ZT.next ZT.nextCost ZT.obs ZT.obsCost Inv Mid (fun _ _ => True)
        (fun _ g => gO g ≤ A) tN tO ∧
      Inv 0 ZT.init ∧ ∀ i < q, tN i ≤ n + β * B ∧ tO i ≤ o + β * (B + δ + A) :=
  ⟨_, _, _, _, P.stratRunBound A, ⟨P.init, by simp [bnd]⟩, fun i hi => by
    have h1 : i * (2 * δ + A) ≤ q * (2 * δ + A) := Nat.mul_le_mul_right _ hi.le
    have h2 : P.bnd A i ≤ B := by
      simp only [bnd]
      omega
    exact ⟨by gcongr, by gcongr⟩⟩

/-- A potential bound with `β = 0` scaled by `c`: the imports, the potentials and `δ` are
multiplied by `c`. -/
def scale (P : ZT.PotBound hE gO n o 0 δ) (c : ℕ) :
    ZT.PotBound (fun e => c * hE e) (fun g => c * gO g) n o 0 (c * δ) where
  Inv := P.Inv
  Mid := P.Mid
  Ψ z := c * P.Ψ z
  Ψm z := c * P.Ψm z
  init := P.init
  next z h := ⟨by simpa using (P.next z h).1, SPTree.Timed.allRet_mono (fun r hr => ⟨hr.1, by
    have := Nat.mul_le_mul_left c hr.2
    rw [Nat.mul_add, Nat.mul_add] at this
    exact this⟩) _ (P.next z h).2⟩
  obs z g h := ⟨by simpa using (P.obs z g h).1, SPTree.Timed.allRet_mono (fun z' hz => ⟨hz.1, by
    have := Nat.mul_le_mul_left c hz.2
    rw [Nat.mul_add, Nat.mul_add] at this
    exact this⟩) _ (P.obs z g h).2⟩

end Strat.Timed.PotBound

/-! ## Environments of graded time and of bounded import -/

/-- The environment `Z` has time `(n, o, q, tD)` against answers in `Out`: the costed strategy
`ZT` erases to the strategy of `Z` and the costed environment `ZE` erases to `Z`; the costed
strategy has a graded time bound `tN`, `tO` (`StratRunBound`) over the answers in `Out`, from
its initial state, with `tN i ≤ n` and `tO i ≤ o` for the first `q` activations; the strategy
makes at most `q` activations; and the distinguisher costs at most `tD` on every state. -/
structure EnvTimeBoundInv {ζ E O : Type} (Z : Env (Strat ζ E O) ζ) (ZT : Strat.Timed ζ E O)
    (ZE : Env.Timed (Strat ζ E O) ζ) (Out : ℕ → O → Prop) (n o q tD : ℕ) : Prop where
  /-- The costed strategy erases to the strategy of `Z`. -/
  strat_erases : ZT.Erases Z.input
  /-- The costed environment erases to `Z`. -/
  env_erases : ZE.Erases Z
  /-- The graded time of the activations. -/
  runBound : ∃ (Inv Mid : ℕ → ζ → Prop) (tN tO : ℕ → ℕ),
    StratRunBound ZT.next ZT.nextCost ZT.obs ZT.obsCost Inv Mid (fun _ _ => True) Out tN tO ∧
      Inv 0 ZT.init ∧ ∀ i < q, tN i ≤ n ∧ tO i ≤ o
  /-- The number of activations. -/
  rounds_le : Z.input.rounds ≤ q
  /-- The time of the distinguisher. -/
  dist_le : ∀ z, SPTree.Timed.stepTime (ZE.distCost z, ZE.dist z) ≤ tD

/-- An environment of time `(n, o, q, tD)` has time `(n, o, q, tD)` against every answer. -/
theorem EnvTimeBound.envTimeBoundInv {ζ E O : Type} {Z : Env (Strat ζ E O) ζ}
    {ZT : Strat.Timed ζ E O} {ZE : Env.Timed (Strat ζ E O) ζ} {n o q tD : ℕ}
    (h : EnvTimeBound Z ZT ZE n o q tD) :
    EnvTimeBoundInv Z ZT ZE (fun _ _ => True) n o q tD where
  strat_erases := h.strat_erases
  env_erases := h.env_erases
  runBound := ⟨fun _ _ => True, fun _ _ => True, fun _ => n, fun _ => o,
    ⟨fun _ z _ => h.timeBound.1 z,
      fun _ _ _ => SPTree.Timed.allRet_of_forall (fun _ => ⟨trivial, trivial⟩) _,
      fun _ z g _ _ => h.timeBound.2 z g,
      fun _ _ _ _ _ => SPTree.Timed.allRet_of_forall (fun _ => trivial) _⟩,
    trivial, fun _ _ => ⟨le_rfl, le_rfl⟩⟩
  rounds_le := h.rounds_le
  dist_le := h.dist_le

/-- **Graded time of an environment with a potential bound.** If the costed strategy of `Z` has
a potential bound and `Ψ₀ + q * (2 * δ + A) ≤ B` for its initial potential `Ψ₀`, then `Z` has
time `(n + β * B, o + β * (B + δ + A), q, tD)` against the answers of import at most `A`. -/
theorem Strat.Timed.PotBound.envTimeBoundInv {ζ E O : Type} {Z : Env (Strat ζ E O) ζ}
    {ZT : Strat.Timed ζ E O} {ZE : Env.Timed (Strat ζ E O) ζ} {hE : E → ℕ} {gO : O → ℕ}
    {n o β δ q tD : ℕ} (P : ZT.PotBound hE gO n o β δ) (hs : ZT.Erases Z.input)
    (he : ZE.Erases Z) (hq : Z.input.rounds ≤ q)
    (hd : ∀ z, SPTree.Timed.stepTime (ZE.distCost z, ZE.dist z) ≤ tD) (A B : ℕ)
    (hB : P.Ψ ZT.init + q * (2 * δ + A) ≤ B) :
    EnvTimeBoundInv Z ZT ZE (fun _ g => gO g ≤ A) (n + β * B) (o + β * (B + δ + A)) q tD where
  strat_erases := hs
  env_erases := he
  runBound := P.runBound A hB
  rounds_le := hq
  dist_le := hd

/-- The environment `Z` has time `(n, o, q, tD)` and import `M`: the costed strategy `ZT` erases
to the strategy of `Z` and the costed environment `ZE` erases to `Z`; the costed strategy has a
potential bound with the size of the events as their import, no import of the answers, the
constants `n`, `o`, `β = 0` and no potential created, and initial potential at most `M`, so that
the sizes of the events of a run add up to at most `M`; the strategy makes at most `q`
activations; and the distinguisher costs at most `tD` on every state. -/
structure EnvImportBound {ζ E O : Type} [ImportSize E] (Z : Env (Strat ζ E O) ζ)
    (ZT : Strat.Timed ζ E O) (ZE : Env.Timed (Strat ζ E O) ζ) (n o q tD M : ℕ) : Prop where
  /-- The costed strategy erases to the strategy of `Z`. -/
  strat_erases : ZT.Erases Z.input
  /-- The costed environment erases to `Z`. -/
  env_erases : ZE.Erases Z
  /-- The potential bound, with initial potential at most `M`. -/
  pot : ∃ P : ZT.PotBound ImportSize.size (fun _ => 0) n o 0 0, P.Ψ ZT.init ≤ M
  /-- The number of activations. -/
  rounds_le : Z.input.rounds ≤ q
  /-- The time of the distinguisher. -/
  dist_le : ∀ z, SPTree.Timed.stepTime (ZE.distCost z, ZE.dist z) ≤ tD

/-- An environment of time `(n, o, q, tD)` and import `M` has time `(n, o, q, tD)` against
every answer. -/
theorem EnvImportBound.envTimeBoundInv {ζ E O : Type} [ImportSize E]
    {Z : Env (Strat ζ E O) ζ} {ZT : Strat.Timed ζ E O} {ZE : Env.Timed (Strat ζ E O) ζ}
    {n o q tD M : ℕ} (h : EnvImportBound Z ZT ZE n o q tD M) :
    EnvTimeBoundInv Z ZT ZE (fun _ _ => True) n o q tD := by
  obtain ⟨P, -⟩ := h.pot
  obtain ⟨_, _, ⟨Inv, Mid, tN, tO, hR, h0, hb⟩, _, _⟩ :=
    P.envTimeBoundInv h.strat_erases h.env_erases h.rounds_le h.dist_le 0 _ le_rfl
  refine ⟨h.strat_erases, h.env_erases, ⟨Inv, Mid, tN, tO, ?_, h0, ?_⟩, h.rounds_le,
    h.dist_le⟩
  · exact ⟨hR.next_time, hR.next_ret, fun i z g hz _ => hR.obs_time i z g hz le_rfl,
      fun i z g hz _ => hR.obs_ret i z g hz le_rfl⟩
  · intro i hi
    have := hb i hi
    simpa using this

/-! ## Realization against environments of graded time and of bounded import -/

/-- `X` realizes `Y` with bound `b` against every environment of time `(n, o, q, tD)` against
the answers in `Out`. -/
def RealizesTimeInv {τ υ E O : Type} (X : Sys τ E O) (Y : Sys υ E O) (Out : ℕ → O → Prop)
    (n o q tD : ℕ) (b : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞) : Prop :=
  ∀ (ζ : Type) (Z : Env (Strat ζ E O) ζ) (ZT : Strat.Timed ζ E O)
    (ZE : Env.Timed (Strat ζ E O) ζ), EnvTimeBoundInv Z ZT ZE Out n o q tD → adv X Y Z ≤ b ζ Z

/-- `X` realizes `Y` with bound `b` against every environment of time `(n, o, q, tD)` and
import `M`. -/
def RealizesTimeImport {τ υ E O : Type} [ImportSize E] (X : Sys τ E O) (Y : Sys υ E O)
    (n o q tD M : ℕ) (b : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞) : Prop :=
  ∀ (ζ : Type) (Z : Env (Strat ζ E O) ζ) (ZT : Strat.Timed ζ E O)
    (ZE : Env.Timed (Strat ζ E O) ζ), EnvImportBound Z ZT ZE n o q tD M → adv X Y Z ≤ b ζ Z

/-- Realization against the environments of graded time against every answer is realization
against the environments of time `(n, o, q, tD)`. -/
theorem RealizesTimeInv.realizesTime {τ υ E O : Type} {X : Sys τ E O} {Y : Sys υ E O}
    {n o q tD : ℕ} {b : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞}
    (h : RealizesTimeInv X Y (fun _ _ => True) n o q tD b) : RealizesTime X Y n o q tD b :=
  fun ζ Z ZT ZE hT => h ζ Z ZT ZE hT.envTimeBoundInv

/-- A realization is a realization against the environments of every graded time. -/
theorem Realizes.realizesTimeInv {τ υ E O : Type} {X : Sys τ E O} {Y : Sys υ E O}
    {b : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞} (h : Realizes X Y b) (Out : ℕ → O → Prop)
    (n o q tD : ℕ) : RealizesTimeInv X Y Out n o q tD b :=
  fun ζ Z _ _ _ => h ζ Z

/-- A costed import pullback: an environment pullback with costed forms `pullT` and `pullE` of
its environment reduction, which erase to the reduced environment, such that the reduced
environment of an environment of time `(n, o, q, tD)` and import `M` has time
`(n + nextC q M, o + obsC q M, roundsMul * q, tD + distC)` against the answers in `Out`. -/
structure ImportPullback (E O E' O' : Type) [ImportSize E'] extends EnvPullback E O E' O' where
  /-- The costed environment reduction, on the costed strategy of an environment. -/
  pullT : {ζ : Type} → Env (Strat ζ E' O') ζ → Strat.Timed ζ E' O' → Strat.Timed (Ctx ζ) E O
  /-- The costed environment reduction, on the costed environment (its distinguisher). -/
  pullE : {ζ : Type} → Env (Strat ζ E' O') ζ → Env.Timed (Strat ζ E' O') ζ →
    Env.Timed (Strat (Ctx ζ) E O) (Ctx ζ)
  /-- The answers against which the reduced environment is bounded. -/
  Out : ℕ → O → Prop
  /-- The time added to a `next` activation, as a function of `q` and `M`. -/
  nextC : ℕ → ℕ → ℕ
  /-- The time added to an `obs` activation, as a function of `q` and `M`. -/
  obsC : ℕ → ℕ → ℕ
  /-- The time added to the distinguisher. -/
  distC : ℕ
  /-- The factor of the activation count. -/
  roundsMul : ℕ
  /-- **Time of the reduced environment.** -/
  pull_import : ∀ {ζ : Type} (Z : Env (Strat ζ E' O') ζ) (ZT : Strat.Timed ζ E' O')
    (ZE : Env.Timed (Strat ζ E' O') ζ) {n o q tD M : ℕ}, EnvImportBound Z ZT ZE n o q tD M →
      EnvTimeBoundInv (pull Z) (pullT Z ZT) (pullE Z ZE) Out (n + nextC q M) (o + obsC q M)
        (roundsMul * q) (tD + distC)

/-- **Time-graded pullback law with import.** If `X` realizes `Y` with bound `b` against the
environments of time `(n + F.nextC q M, o + F.obsC q M, F.roundsMul * q, tD + F.distC)` against
the answers in `F.Out`, then `F.map X` realizes `F.map Y` with bound `b` at the pulled-back
environment against the environments of time `(n, o, q, tD)` and import `M`. -/
theorem ImportPullback.realizesTime_map {τ υ E O E' O' : Type} [ImportSize E']
    (F : ImportPullback E O E' O') {X : Sys τ E O} {Y : Sys υ E O} (hX : F.Adm X)
    (hY : F.Adm Y) {n o q tD M : ℕ} {b : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞}
    (h : RealizesTimeInv X Y F.Out (n + F.nextC q M) (o + F.obsC q M) (F.roundsMul * q)
      (tD + F.distC) b) :
    RealizesTimeImport (F.map X) (F.map Y) n o q tD M (fun ζ Z => b (F.Ctx ζ) (F.pull Z)) :=
  fun _ Z _ _ hT => (F.adv_map hX hY Z).trans_le (h _ _ _ _ (F.pull_import Z _ _ hT))

/-! ## The costed multi-call reduction -/

namespace MultiHybrid.Timed

variable {σ ζ E O EG OG : Type}

set_option linter.auxLemma false in
/-- **Potential bound of the costed multi-call reduction.** If the costed simulator `πT` has a
potential time bound `P` and the costed strategy `ZT` a potential bound `PZ`, and the interface
between them conserves import up to `κ` per message (`gE e ≤ hE e + κ` for the events of the
strategy, `gZ x ≤ hO x + κ` for the outputs of the simulator), then the costed reduction has a
potential bound with the import `hEG` of its events and `gO` of its answers, the constants
`n + a + 6 + b * (δ + κ)`, `o + a + 4 + β * κ`, `β + b`, and the potential
`δ + κ + hEG idle` created per activation. Its potential is the sum of the potentials of the
strategy and of the simulator and of the import of the pending message. -/
noncomputable def reducePot (π : MultiHybrid σ E O EG OG) (idle : EG) (Z : Strat ζ E O)
    {πT : MultiHybrid.Timed σ E O EG OG} {ZT : Strat.Timed ζ E O} (hT : πT.Erases π)
    (hZ : ZT.Erases Z) {gE : E → ℕ} {gO : OG → ℕ} {hEG : EG → ℕ} {hO : O → ℕ} {a b : ℕ}
    {hE : E → ℕ} {gZ : O → ℕ} {n o β δ κ : ℕ} (P : πT.PotentialBound gE gO hEG hO a b)
    (PZ : ZT.PotBound hE gZ n o β δ) (hκE : ∀ e, gE e ≤ hE e + κ)
    (hκO : ∀ x, gZ x ≤ hO x + κ) :
    (MultiHybrid.reduce.timed π idle Z ZT.next ZT.nextCost πT.start πT.startCost πT.finish
      πT.finishCost ZT.obs ZT.obsCost πT.resume πT.resumeCost).PotBound hEG gO
      (n + a + 6 + b * (δ + κ)) (o + a + 4 + β * κ) (β + b) (δ + κ + hEG idle) where
  Inv
    | (z, s, none) => PZ.Inv z ∧ P.Inv s
    | (z, s, some _) => PZ.Mid z ∧ P.Inv s
  Mid
    | (_, _, none) => False
    | (z, s, some _) => PZ.Mid z ∧ P.Inv s
  Ψ
    | (z, s, none) => PZ.Ψ z + P.Φ s
    | (z, s, some (d, _)) => PZ.Ψm z + P.Φ s + Sum.elim hEG hO d
  Ψm
    | (z, s, none) => PZ.Ψ z + P.Φ s
    | (z, s, some (d, _)) => PZ.Ψm z + P.Φ s + Sum.elim (fun _ => 0) hO d
  init := by
    simp only [MultiHybrid.reduce.timed]
    obtain ⟨_, _, _, rfl⟩ := hT
    obtain ⟨_, _, rfl⟩ := hZ
    exact ⟨PZ.init, P.init⟩
  next zs h := by
    rcases zs with ⟨z, s, _ | ⟨d, k⟩⟩
    · simp only [MultiHybrid.reduce.timed, MultiHybrid.reduce.next.tree.timed,
        MultiHybrid.reduce.next.tree.match_1.timed] at h ⊢
      have hN := PZ.next z h.1
      constructor
      · have := SPTree.Timed.stepTime_bind_bind_le 1 1 (ZT.nextCost z, ZT.next z)
          (fun x => (πT.startCost s x.2, πT.start s x.2))
          (fun x y => (2, SPTree.Timed.ret ((x.1, y.1, some (y.2, π.fuel)), evOf idle y.2)))
          (TB := a + b * (P.Φ s + (PZ.Ψ z + δ + κ))) hN.1 hN.2
          (fun x hx => (P.start s x.2 h.2).1.trans (by
            have := hκE x.2
            gcongr
            omega))
          (fun x _ => (P.start s x.2 h.2).2) (TF := 2)
          (fun _ _ _ _ => by simp [SPTree.Timed.stepTime, SPTree.Timed.time_ret])
        simp only [SPTree.Timed.stepTime, SPTree.Timed.delay] at this ⊢
        simp only [Nat.mul_add, Nat.add_mul] at this ⊢
        omega
      · simp only [SPTree.Timed.delay, SPTree.Timed.allRet_bind]
        refine SPTree.Timed.allRet_mono (fun x hx => ?_) _ hN.2
        refine SPTree.Timed.allRet_mono (fun y hy => ?_) _ (P.start s x.2 h.2).2
        have := hκE x.2
        rcases y with ⟨s', _ | x'⟩
        · simp only [SPTree.Timed.AllRet, evOf, Sum.elim_inl] at hy ⊢
          exact ⟨⟨hx.1, hy.1⟩, by omega⟩
        · simp only [SPTree.Timed.AllRet, evOf, Sum.elim_inr] at hy ⊢
          exact ⟨⟨hx.1, hy.1⟩, by omega⟩
    · simp only [MultiHybrid.reduce.timed, MultiHybrid.reduce.next.tree.timed,
        MultiHybrid.reduce.next.tree.match_1.timed] at h ⊢
      constructor
      · simp only [SPTree.Timed.stepTime, SPTree.Timed.delay, SPTree.Timed.time_ret]
        omega
      · rcases d with g | x
        · simp only [SPTree.Timed.delay, SPTree.Timed.AllRet, evOf, Sum.elim_inl]
          exact ⟨h, by omega⟩
        · simp only [SPTree.Timed.delay, SPTree.Timed.AllRet, evOf, Sum.elim_inr]
          exact ⟨h, by omega⟩
  obs zs g h := by
    rcases zs with ⟨z, s, _ | ⟨_ | x, _ | k⟩⟩
    · exact h.elim
    all_goals simp only [MultiHybrid.reduce.timed, MultiHybrid.reduce.obs.tree.timed,
        MultiHybrid.reduce.obs.tree.match_1.timed] at h ⊢
    · have hF := P.finish s g h.2
      constructor
      · have := SPTree.Timed.stepTime_bind_bind_le 1 1 (πT.finishCost s g, πT.finish s g)
          (fun x => (ZT.obsCost z x.2, ZT.obs z x.2))
          (fun x y => (0, SPTree.Timed.ret (y, x.1, (none : Option ((EG ⊕ O) × ℕ)))))
          (TB := o + β * (PZ.Ψm z + (P.Φ s + gO g + κ))) hF.1 hF.2
          (fun x hx => (PZ.obs z x.2 h.1).1.trans (by
            have := hκO x.2
            gcongr
            omega))
          (fun x _ => (PZ.obs z x.2 h.1).2) (TF := 0)
          (fun _ _ _ _ => by simp [SPTree.Timed.stepTime, SPTree.Timed.time_ret])
        simp only [SPTree.Timed.stepTime, SPTree.Timed.delay, Sum.elim_inl] at this ⊢
        simp only [Nat.mul_add, Nat.add_mul, Nat.add_zero] at this ⊢
        omega
      · simp only [SPTree.Timed.delay, SPTree.Timed.allRet_bind]
        refine SPTree.Timed.allRet_mono (fun x hx => ?_) _ hF.2
        refine SPTree.Timed.allRet_mono (fun y hy => ?_) _ (PZ.obs z x.2 h.1).2
        have := hκO x.2
        simp only [SPTree.Timed.AllRet, Sum.elim_inl]
        exact ⟨⟨hy.1, hx.1⟩, by omega⟩
    · have hR := P.resume s g h.2
      constructor
      · have := SPTree.Timed.stepTime_bind_le (πT.resume s g)
          (fun x => (0, SPTree.Timed.ret (z, x.1, some (x.2, k)))) 0
          (fun _ => by simp [SPTree.Timed.stepTime, SPTree.Timed.time_ret])
        have h2 := hR.1
        simp only [SPTree.Timed.stepTime, SPTree.Timed.delay, Sum.elim_inl] at this h2 ⊢
        simp only [Nat.mul_add, Nat.add_mul, Nat.add_zero] at h2 ⊢
        omega
      · simp only [SPTree.Timed.delay, SPTree.Timed.allRet_bind]
        refine SPTree.Timed.allRet_mono (fun x hx => ?_) _ hR.2
        simp only [SPTree.Timed.AllRet, Sum.elim_inl]
        exact ⟨⟨h.1, hx.1⟩, by omega⟩
    · have hZo := PZ.obs z x h.1
      have hκ := hκO x
      constructor
      · have := SPTree.Timed.stepTime_bind_le (ZT.obs z x)
          (fun y => (0, SPTree.Timed.ret (y, s, (none : Option ((EG ⊕ O) × ℕ))))) 0
          (fun _ => by simp [SPTree.Timed.stepTime, SPTree.Timed.time_ret])
        have h2 := hZo.1
        have h3 := Nat.mul_le_mul_left β hκ
        simp only [SPTree.Timed.stepTime, SPTree.Timed.delay, Sum.elim_inr] at this h2 ⊢
        simp only [Nat.mul_add, Nat.add_mul] at h2 h3 ⊢
        omega
      · simp only [SPTree.Timed.delay, SPTree.Timed.allRet_bind]
        refine SPTree.Timed.allRet_mono (fun y hy => ?_) _ hZo.2
        simp only [SPTree.Timed.AllRet, Sum.elim_inr]
        exact ⟨⟨hy.1, h.2⟩, by omega⟩
    · constructor
      · simp only [SPTree.Timed.stepTime, SPTree.Timed.delay, SPTree.Timed.time_ret]
        omega
      · simp only [SPTree.Timed.delay, SPTree.Timed.AllRet, Sum.elim_inr]
        exact ⟨h, by omega⟩

/-- **Time of a strategy of import `M` reduced by a multi-call simulator with a potential time
bound.** If the costed strategy `ZT` has the potential bound of an environment of import `M`
(`EnvImportBound`) and the costed simulator `πT` a potential time bound whose import of an outer
event is at most `c` times its size, then the costed reduction has a graded time bound against
the answers of import at most `A`, at most `n + a + 6 + b * B` in `next` and
`o + a + 4 + b * (B + hEG idle + A)` in `obs` for the first `q` activations, with
`B = c * M + Φ₀ + q * (2 * hEG idle + A)` and `Φ₀` the initial potential of the simulator. -/
theorem reduce_runBound_import [ImportSize E] (π : MultiHybrid σ E O EG OG) (idle : EG)
    (Z : Strat ζ E O) {πT : MultiHybrid.Timed σ E O EG OG} {ZT : Strat.Timed ζ E O}
    (hT : πT.Erases π) (hZ : ZT.Erases Z) {gE : E → ℕ} {gO : OG → ℕ} {hEG : EG → ℕ}
    {hO : O → ℕ} {a b c n o M : ℕ} (P : πT.PotentialBound gE gO hEG hO a b)
    (hlin : ∀ e, gE e ≤ c * ImportSize.size e)
    (PZ : ZT.PotBound ImportSize.size (fun _ => 0) n o 0 0) (hM : PZ.Ψ ZT.init ≤ M)
    (q A : ℕ) :
    ∃ (Inv Mid : ℕ → RState σ ζ EG O → Prop) (tN tO : ℕ → ℕ),
      StratRunBound
        (MultiHybrid.reduce.timed π idle Z ZT.next ZT.nextCost πT.start πT.startCost
          πT.finish πT.finishCost ZT.obs ZT.obsCost πT.resume πT.resumeCost).next
        (MultiHybrid.reduce.timed π idle Z ZT.next ZT.nextCost πT.start πT.startCost
          πT.finish πT.finishCost ZT.obs ZT.obsCost πT.resume πT.resumeCost).nextCost
        (MultiHybrid.reduce.timed π idle Z ZT.next ZT.nextCost πT.start πT.startCost
          πT.finish πT.finishCost ZT.obs ZT.obsCost πT.resume πT.resumeCost).obs
        (MultiHybrid.reduce.timed π idle Z ZT.next ZT.nextCost πT.start πT.startCost
          πT.finish πT.finishCost ZT.obs ZT.obsCost πT.resume πT.resumeCost).obsCost
        Inv Mid (fun _ _ => True) (fun _ g => gO g ≤ A) tN tO ∧
      Inv 0 (MultiHybrid.reduce.timed π idle Z ZT.next ZT.nextCost πT.start πT.startCost
          πT.finish πT.finishCost ZT.obs ZT.obsCost πT.resume πT.resumeCost).init ∧
      ∀ i < q, tN i ≤ n + a + 6 + b * (c * M + P.Φ πT.init + q * (2 * hEG idle + A)) ∧
        tO i ≤ o + a + 4 +
          b * (c * M + P.Φ πT.init + q * (2 * hEG idle + A) + hEG idle + A) := by
  let R := reducePot π idle Z hT hZ P (PZ.scale c) (κ := 0) (fun e => by simpa using hlin e)
    (fun _ => by simp)
  have hΨ : R.Ψ (MultiHybrid.reduce.timed π idle Z ZT.next ZT.nextCost πT.start πT.startCost
      πT.finish πT.finishCost ZT.obs ZT.obsCost πT.resume πT.resumeCost).init ≤
      c * M + P.Φ πT.init := by
    obtain ⟨_, _, _, rfl⟩ := hT
    obtain ⟨_, _, rfl⟩ := hZ
    exact Nat.add_le_add_right (Nat.mul_le_mul_left c hM) _
  obtain ⟨Inv, Mid, tN, tO, h1, h2, h3⟩ := R.runBound A (q := q) (B := c * M + P.Φ πT.init +
    q * (2 * hEG idle + A)) (by simpa using hΨ)
  exact ⟨Inv, Mid, tN, tO, h1, h2, fun i hi => by simpa using h3 i hi⟩

/-- **Time of a strategy of import `M` reduced by two multi-call simulators in sequence**, the
pullback through the composite of `π₁` and `π₂`. The costed simulators have potential time
bounds `P₁` (outer events `E`, middle events `EM` passed on, middle answers `OM` received) and
`P₂` (middle events received, middle answers passed on), and the middle interface conserves
import up to `κ` per message (`gEM ≤ hEM + κ`, `gM ≤ hM + κ`). Then the twice reduced strategy
has a graded time bound against the answers of import at most `A`, at most
`n + a₁ + 6 + a₂ + 6 + b₂ * (hEM idle₁ + κ) + (b₁ + b₂) * B` in `next` and
`o + a₁ + 4 + a₂ + 4 + b₁ * κ + (b₁ + b₂) * (B + δ + A)` in `obs` for the first `q`
activations, with `δ = hEM idle₁ + κ + hEG idle₂` and
`B = c * M + Φ₁ + Φ₂ + q * (2 * δ + A)`: the potentials of the two simulators add, and the
import `κ` created at the middle interface accumulates over the `q` activations of the twice
reduced strategy. -/
theorem reduce_reduce_runBound_import [ImportSize E] {σ₁ σ₂ EM OM : Type}
    (π₁ : MultiHybrid σ₁ E O EM OM) (idle₁ : EM) (π₂ : MultiHybrid σ₂ EM OM EG OG)
    (idle₂ : EG) (Z : Strat ζ E O) {π₁T : MultiHybrid.Timed σ₁ E O EM OM}
    {π₂T : MultiHybrid.Timed σ₂ EM OM EG OG} {ZT : Strat.Timed ζ E O} (hT₁ : π₁T.Erases π₁)
    (hT₂ : π₂T.Erases π₂) (hZ : ZT.Erases Z) {gE : E → ℕ} {gM hM : OM → ℕ}
    {gEM hEM : EM → ℕ} {hO : O → ℕ} {gO : OG → ℕ} {hEG : EG → ℕ} {a₁ b₁ a₂ b₂ κ c n o M : ℕ}
    (P₁ : π₁T.PotentialBound gE gM hEM hO a₁ b₁)
    (P₂ : π₂T.PotentialBound gEM gO hEG hM a₂ b₂) (hlin : ∀ e, gE e ≤ c * ImportSize.size e)
    (hκE : ∀ m, gEM m ≤ hEM m + κ) (hκO : ∀ x, gM x ≤ hM x + κ)
    (PZ : ZT.PotBound ImportSize.size (fun _ => 0) n o 0 0) (hM : PZ.Ψ ZT.init ≤ M)
    (q A : ℕ) :
    let RT₁ := MultiHybrid.reduce.timed π₁ idle₁ Z ZT.next ZT.nextCost π₁T.start
      π₁T.startCost π₁T.finish π₁T.finishCost ZT.obs ZT.obsCost π₁T.resume π₁T.resumeCost
    let RT₂ := MultiHybrid.reduce.timed π₂ idle₂ (π₁.reduce idle₁ Z) RT₁.next RT₁.nextCost
      π₂T.start π₂T.startCost π₂T.finish π₂T.finishCost RT₁.obs RT₁.obsCost π₂T.resume
      π₂T.resumeCost
    ∃ (Inv Mid : ℕ → RState σ₂ (RState σ₁ ζ EM O) EG OM → Prop) (tN tO : ℕ → ℕ),
      StratRunBound RT₂.next RT₂.nextCost RT₂.obs RT₂.obsCost Inv Mid (fun _ _ => True)
        (fun _ g => gO g ≤ A) tN tO ∧
      Inv 0 RT₂.init ∧
      ∀ i < q, tN i ≤ n + a₁ + 6 + a₂ + 6 + b₂ * (hEM idle₁ + κ) + (b₁ + b₂) *
          (c * M + P₁.Φ π₁T.init + P₂.Φ π₂T.init + q * (2 * (hEM idle₁ + κ + hEG idle₂) + A)) ∧
        tO i ≤ o + a₁ + 4 + a₂ + 4 + b₁ * κ + (b₁ + b₂) *
          (c * M + P₁.Φ π₁T.init + P₂.Φ π₂T.init + q * (2 * (hEM idle₁ + κ + hEG idle₂) + A) +
            (hEM idle₁ + κ + hEG idle₂) + A) := by
  intro RT₁ RT₂
  have hZ₁ : RT₁.Erases (π₁.reduce idle₁ Z) := by
    obtain ⟨_, _, _, rfl⟩ := hT₁
    obtain ⟨_, _, rfl⟩ := hZ
    exact MultiHybrid.reduce.erase_timed _ _ _ _ _ _ _ _ _ _ _ _ _ (fun _ => rfl)
      (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
  let R₁ := reducePot π₁ idle₁ Z hT₁ hZ P₁ (PZ.scale c) (κ := 0)
    (fun e => by simpa using hlin e) (fun _ => by simp)
  let R₂ := reducePot π₂ idle₂ (π₁.reduce idle₁ Z) hT₂ hZ₁ P₂ R₁ hκE hκO
  have hΨ : R₂.Ψ RT₂.init ≤ c * M + P₁.Φ π₁T.init + P₂.Φ π₂T.init := by
    obtain ⟨_, _, _, rfl⟩ := hT₁
    obtain ⟨_, _, _, rfl⟩ := hT₂
    obtain ⟨_, _, rfl⟩ := hZ
    exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.mul_le_mul_left c hM) _) _
  obtain ⟨Inv, Mid, tN, tO, h1, h2, h3⟩ := R₂.runBound A (q := q)
    (B := c * M + P₁.Φ π₁T.init + P₂.Φ π₂T.init + q * (2 * (hEM idle₁ + κ + hEG idle₂) + A))
    (by simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero]; grind)
  refine ⟨Inv, Mid, tN, tO, h1, h2, fun i hi => ?_⟩
  obtain ⟨h4, h5⟩ := h3 i hi
  exact ⟨h4.trans (le_of_eq (by ring)), h5.trans (le_of_eq (by ring))⟩

/-- **Run bound of a composite from its potential certificate.** If the composite of two costed
multi-call simulators, erasing to `π₁` and `π₂`, has the potential certificate `a`, `b`, `c`,
`d`, then the strategy of import `M` reduced by `π₁` and then by `π₂` has a graded time bound
against the answers of size at most `A / c`, at most `n + a + 12 + b * (ι + d) + b * B` in
`next` and `o + a + 8 + b * d + b * (B + ι + d + A)` in `obs` for the first `q` activations,
with `B = c * M + Φ₀ + q * (2 * (ι + d) + A)`, for the initial potential `Φ₀` of the two
simulators and the import `ι` of the idle middle event. -/
theorem potCert_comp_runBound_import {σ₁ σ₂ ζ E O EM OM EG OG : Type} [ImportSize E]
    [ImportSize OG] {V : PubView E O} {U : PubView EM OM} {W : PubView EG OG}
    (π₁ : MultiHybrid σ₁ E O EM OM) (idle₁ : EM) (π₂ : MultiHybrid σ₂ EM OM EG OG)
    (idle₂ : EG) (Z : Strat ζ E O) {π₁T : MultiHybrid.Timed σ₁ E O EM OM}
    {π₂T : MultiHybrid.Timed σ₂ EM OM EG OG} {ZT : Strat.Timed ζ E O} (hT₁ : π₁T.Erases π₁)
    (hT₂ : π₂T.Erases π₂) (hZ : ZT.Erases Z) {a b c d n o M : ℕ}
    (h : ((Simulator.Timed.ofMultiHybrid π₁T : Simulator.Timed E O EM OM V U).comp
      (Simulator.Timed.ofMultiHybrid π₂T : Simulator.Timed EM OM EG OG U W)).PotCert a b c d)
    (PZ : ZT.PotBound ImportSize.size (fun _ => 0) n o 0 0) (hM : PZ.Ψ ZT.init ≤ M)
    (q A : ℕ) :
    let RT₁ := MultiHybrid.reduce.timed π₁ idle₁ Z ZT.next ZT.nextCost π₁T.start
      π₁T.startCost π₁T.finish π₁T.finishCost ZT.obs ZT.obsCost π₁T.resume π₁T.resumeCost
    let RT₂ := MultiHybrid.reduce.timed π₂ idle₂ (π₁.reduce idle₁ Z) RT₁.next RT₁.nextCost
      π₂T.start π₂T.startCost π₂T.finish π₂T.finishCost RT₁.obs RT₁.obsCost π₂T.resume
      π₂T.resumeCost
    ∃ (Φ₀ ι : ℕ) (Inv Mid : ℕ → RState σ₂ (RState σ₁ ζ EM O) EG OM → Prop) (tN tO : ℕ → ℕ),
      StratRunBound RT₂.next RT₂.nextCost RT₂.obs RT₂.obsCost Inv Mid (fun _ _ => True)
        (fun _ g => c * ImportSize.size g ≤ A) tN tO ∧
      Inv 0 RT₂.init ∧
      ∀ i < q, tN i ≤ n + a + 12 + b * (ι + d) + b * (c * M + Φ₀ + q * (2 * (ι + d) + A)) ∧
        tO i ≤ o + a + 8 + b * d + b * (c * M + Φ₀ + q * (2 * (ι + d) + A) + (ι + d) + A) := by
  intro RT₁ RT₂
  obtain ⟨gE, gO, ⟨κ, gM, hM', gEM, hEM, a₁, b₁, d₁, a₂, b₂, d₂, ⟨P₁⟩, ⟨P₂⟩, hκE, hκO, ha, hb,
    hd⟩, hlinE, hlinO⟩ := h
  have hR := reduce_reduce_runBound_import π₁ idle₁ π₂ idle₂ Z hT₁ hT₂ hZ P₁ P₂ hlinE hκE hκO
    PZ hM q A
  obtain ⟨Inv, Mid, tN, tO, h1, h2, h3⟩ := hR
  refine ⟨P₁.Φ π₁T.init + P₂.Φ π₂T.init, hEM idle₁, Inv, Mid, tN, tO,
    ⟨h1.next_time, h1.next_ret, fun i z g hz hg => h1.obs_time i z g hz ((hlinO g).trans hg),
      fun i z g hz hg => h1.obs_ret i z g hz ((hlinO g).trans hg)⟩, h2, fun i hi => ?_⟩
  obtain ⟨h4, h5⟩ := h3 i hi
  simp only [Pi.zero_apply, Nat.add_zero] at h4 h5
  have hq : q * (2 * (hEM idle₁ + κ) + A) ≤ q * (2 * (hEM idle₁ + d) + A) :=
    Nat.mul_le_mul_left q (by omega)
  have k1 : b₂ * (hEM idle₁ + κ) ≤ b * (hEM idle₁ + d) := Nat.mul_le_mul (by omega) (by omega)
  have k2 : (b₁ + b₂) * (c * M + P₁.Φ π₁T.init + P₂.Φ π₂T.init +
      q * (2 * (hEM idle₁ + κ) + A)) ≤
      b * (c * M + (P₁.Φ π₁T.init + P₂.Φ π₂T.init) + q * (2 * (hEM idle₁ + d) + A)) :=
    Nat.mul_le_mul hb (by omega)
  have k3 : b₁ * κ ≤ b * d := Nat.mul_le_mul (by omega) (by omega)
  have k4 : (b₁ + b₂) * (c * M + P₁.Φ π₁T.init + P₂.Φ π₂T.init +
      q * (2 * (hEM idle₁ + κ) + A) + (hEM idle₁ + κ) + A) ≤
      b * (c * M + (P₁.Φ π₁T.init + P₂.Φ π₂T.init) + q * (2 * (hEM idle₁ + d) + A) +
        (hEM idle₁ + d) + A) :=
    Nat.mul_le_mul hb (by omega)
  exact ⟨by omega, by omega⟩

end MultiHybrid.Timed

/-- A multi-call simulator `π` with a costed machine `πT` erasing to it that has a potential
time bound whose import of an outer event is at most `c` times its size, as a costed import
pullback against the answers of import at most `A`: the costed reductions are
`MultiHybrid.Timed.reduce` and `MultiHybrid.reduceEnv.timed`, the activation count is
multiplied by `π.fuel + 1`, and the constants are `a + 6 + b * B` and
`a + 4 + b * (B + hEG idle + A)` with `B = c * M + Φ₀ + (π.fuel + 1) * q * (2 * hEG idle + A)`
and `1`. -/
noncomputable def MultiHybrid.toImportPullback {σ E O EG OG : Type} [ImportSize E]
    (π : MultiHybrid σ E O EG OG) (idle : EG) {πT : MultiHybrid.Timed σ E O EG OG}
    (hE : πT.Erases π) {gE : E → ℕ} {gO : OG → ℕ} {hEG : EG → ℕ} {hO : O → ℕ} {a b c : ℕ}
    (P : πT.PotentialBound gE gO hEG hO a b) (hlin : ∀ e, gE e ≤ c * ImportSize.size e)
    (A : ℕ) : ImportPullback EG OG E O where
  toEnvPullback := π.toEnvPullback idle
  pullT Z ZT := MultiHybrid.Timed.reduce π idle Z.input πT ZT
  pullE Z ZE := MultiHybrid.reduceEnv.timed π idle Z ZE.dist ZE.distCost
  Out _ g := gO g ≤ A
  nextC q M := a + 6 + b * (c * M + P.Φ πT.init + (π.fuel + 1) * q * (2 * hEG idle + A))
  obsC q M := a + 4 +
    b * (c * M + P.Φ πT.init + (π.fuel + 1) * q * (2 * hEG idle + A) + hEG idle + A)
  distC := 1
  roundsMul := π.fuel + 1
  pull_import Z ZT ZE n o q tD M h := by
    obtain ⟨PZ, hM⟩ := h.pot
    obtain ⟨Inv, Mid, tN, tO, h1, h2, h3⟩ := MultiHybrid.Timed.reduce_runBound_import π idle
      Z.input hE h.strat_erases P hlin PZ hM ((π.fuel + 1) * q) A
    rw [MultiHybrid.toEnvPullback_pull]
    refine ⟨MultiHybrid.Timed.reduce_erases hE h.strat_erases,
      MultiHybrid.reduceEnv.erase_timed π idle Z _ _ fun _ => by rw [h.env_erases],
      ⟨Inv, Mid, tN, tO, h1, h2, fun i hi => ⟨(h3 i hi).1.trans (by omega),
        (h3 i hi).2.trans (by omega)⟩⟩, ?_, fun w => ?_⟩
    · have := Nat.mul_le_mul_left (π.fuel + 1) h.rounds_le
      simp only [MultiHybrid.reduceEnv, MultiHybrid.reduce, MultiHybrid.calls]
      linarith
    · have := h.dist_le w.1
      simp only [MultiHybrid.reduceEnv.timed, MultiHybrid.reduceEnv.dist.tree.timed,
        SPTree.Timed.stepTime] at this ⊢
      omega

end CatCrypt.Crypto.UCTransparent
