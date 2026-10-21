/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCConcrete
public import CatCryptCore.Crypto.OracleSubst
public import CatCryptCore.Crypto.PRPPRFSwitching
public import CatCryptCore.Crypto.SPCompPMF

/-!
# Concrete UC emulation with oracle-querying distinguishers

The class route of `UCConcrete` (`GameAdvBoundC`, `UCFromGameC`) for games in the random
oracle model, where the distinguisher, the adversary and the environment query a random
oracle that the game also queries.

A game `g : ROGame hon leak Q R` runs, on input `x`, the program `g.prog x` against a
lazily sampled random function `rfOracle` on the domain `g.dom x` with answers in `g.ans`,
started from the empty table. A distinguisher `D : leak → OracleAdv Q R Bool` asks queries
`q : Q`; each is answered by the program `g.iface x q` against the same lazily sampled
function. The real and the ideal game of a pair each carry their own backing domain: the
ideal game may extend the domain the distinguisher reads by points private to the
simulator, which the distinguisher cannot query.

## Main definitions

* `ROGame` — a game whose program and distinguisher-oracle interface query one lazily
  sampled random function; `ROGame.exp` — the experiment with a distinguisher.
* `ROGame.post`, `ROGame.ofGame` — post-composition with an oracle program, and the
  UC wrapping with the honest output `Unit`.
* `ROEnv`, `DistRO` — environments whose distinguisher queries the oracle, and the
  concrete distance between two games.
* `UCEmulatesROSim` — concrete UC emulation with adversaries and environments that query
  the oracle, the simulator given by a map of adversaries (the form of `UCEmulatesCSim`).
* `ROGameAdvBoundC`, `roEnvReduction`, `roGameUCBound`, `UCFromROGameC` — the route from a
  concrete per-distinguisher game bound to concrete UC emulation.

## Main results

* `ROGame.exp_post`, `ROGame.exp_ofGame` — the experiment of a post-composed and of a
  wrapped game.
* `UCEmulatesROSim_of_advantage` — a per-distinguisher game bound gives concrete UC
  emulation with simulator `S = A`, the bound evaluated at `roEnvReduction A Z`.
* `ucFromROGameC_of_adv` — the instance `UCFromROGameC` from `ROGameAdvBoundC`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto

namespace UCConcreteOracle

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.PRPPRF
open CatCrypt.Crypto.UCDSL CatCrypt.Crypto.UCConcrete
open scoped ENNReal

/-! ## Games in the random oracle model -/

/-- A game in the random oracle model with output `leak` and distinguisher oracle
`Q → R`: on input `x`, the program `prog x` queries a random function on `dom x` with
answers in `ans`, and a distinguisher's query `q` is answered by the program `iface x q`
against the same random function. -/
structure ROGame (hon leak Q R : Type) where
  /-- The domain of the backing random function on input `x`. -/
  dom : hon → Type
  /-- The answers of the backing random function. -/
  ans : Type
  [decEqDom : ∀ x, DecidableEq (dom x)]
  [fintypeAns : Fintype ans]
  [nonemptyAns : Nonempty ans]
  /-- The game's program on input `x`. -/
  prog : (x : hon) → OracleAdv (dom x) ans leak
  /-- The program answering the distinguisher's query `q` on input `x`. -/
  iface : (x : hon) → Q → OracleAdv (dom x) ans R

attribute [instance] ROGame.decEqDom ROGame.fintypeAns ROGame.nonemptyAns

variable {hon leak Q R β γ : Type}

/-- The experiment of `g` on input `x` with distinguisher `D`: the program and then `D` on
its output, every query answered from one lazily sampled random function started from the
empty table. -/
noncomputable def ROGame.exp (g : ROGame hon leak Q R) (x : hon)
    (D : leak → OracleAdv Q R Bool) : SPComp Bool :=
  liftPMF ((OracleAdv.run rfOracle
    ((g.prog x).bind fun l => OracleAdv.subst (g.iface x) (D l)) []).map Prod.fst)

/-- The experiment does not read the initial heap. -/
theorem ROGame.prTrue_exp (g : ROGame hon leak Q R) (x : hon)
    (D : leak → OracleAdv Q R Bool) (h₀ : Heap) :
    prTrue (g.exp x D) h₀ = prTrue (g.exp x D) Heap.empty := by
  simp only [ROGame.exp, prTrue_liftPMF]

/-- The game `g` followed by the oracle program `k`, whose queries are answered through
the interface of `g`. -/
def ROGame.post (g : ROGame hon β Q R) (k : β → OracleAdv Q R γ) : ROGame hon γ Q R where
  dom := g.dom
  ans := g.ans
  prog x := (g.prog x).bind fun b => OracleAdv.subst (g.iface x) (k b)
  iface := g.iface

/-- The experiment of `g.post k` with `D` is the experiment of `g` with `k` followed
by `D`. -/
theorem ROGame.exp_post (g : ROGame hon β Q R) (k : β → OracleAdv Q R γ) (x : hon)
    (D : γ → OracleAdv Q R Bool) :
    (g.post k).exp x D = g.exp x fun b => (k b).bind D := by
  simp only [ROGame.exp, ROGame.post, OracleAdv.bind_assoc, OracleAdv.subst_bind]
  rfl

/-- The game `g` as a UC protocol: no honest output, the output of `g` on the
adversary channel. -/
def ROGame.ofGame (g : ROGame hon leak Q R) : ROGame hon (Unit ⊕ leak) Q R where
  dom := g.dom
  ans := g.ans
  prog x := (g.prog x).bind fun l => .ret (.inr l)
  iface := g.iface

/-- The experiment of `g.ofGame` with `D` is the experiment of `g` with `D` on the
adversary channel. -/
theorem ROGame.exp_ofGame (g : ROGame hon leak Q R) (x : hon)
    (D : Unit ⊕ leak → OracleAdv Q R Bool) :
    g.ofGame.exp x D = g.exp x fun l => D (.inr l) := by
  simp only [ROGame.exp, ROGame.ofGame, OracleAdv.bind_assoc, OracleAdv.bind_ret]
  rfl

/-! ## Environments with oracle access and concrete UC emulation -/

/-- An environment whose distinguisher queries the oracle `Q → R`: an input, an initial
heap and a distinguisher. -/
structure ROEnv (α Q R β : Type) where
  /-- Input fed to the game. -/
  input : α
  /-- Initial heap. -/
  heap : Heap
  /-- Distinguisher run on the output, with oracle access. -/
  dist : β → OracleAdv Q R Bool

/-- Distinguishing gap of the environment `Z` between the games `f` and `g`. -/
noncomputable def ROEnv.gap {α Q R β : Type} (f g : ROGame α β Q R) (Z : ROEnv α Q R β) :
    ℝ≥0∞ :=
  absDiff (prTrue (f.exp Z.input Z.dist) Z.heap) (prTrue (g.exp Z.input Z.dist) Z.heap)

/-- Concrete distance: every environment `Z` with oracle access distinguishes `f` from `g`
with gap at most `bound Z`. -/
def DistRO {α Q R β : Type} (f g : ROGame α β Q R) (bound : ROEnv α Q R β → ℝ≥0∞) : Prop :=
  ∀ Z, ROEnv.gap f g Z ≤ bound Z

/-- Parallel post-processing of the two channels: the honest output is passed on, the
adversary `A` (with oracle access) runs on the leakage. -/
def mapSumRO {out leak V : Type} (A : leak → OracleAdv Q R V) :
    out ⊕ leak → OracleAdv Q R (out ⊕ V)
  | .inl o => .ret (.inl o)
  | .inr l => (A l).bind fun v => .ret (.inr v)

/-- Concrete UC emulation in the random oracle model, with the simulator given by the map
`sim`: for every adversary `A` with oracle access, every environment `Z` with oracle access
distinguishes the real run of `π` with `A` from the ideal run of `F` with `sim A` with gap
at most `bound A Z`. The adversary, the simulator and the environment query the backing
random function of the run through the interface of the game. -/
def UCEmulatesROSim (spec : UCSpec.{0, 0, 0, 0, 0})
    (π : ROGame spec.hon (spec.out ⊕ spec.leak) Q R)
    (F : ROGame spec.hon (spec.out ⊕ spec.sim_if) Q R)
    (sim : (spec.leak → OracleAdv Q R spec.view) → (spec.sim_if → OracleAdv Q R spec.view))
    (bound : (spec.leak → OracleAdv Q R spec.view) →
      ROEnv spec.hon Q R (spec.out ⊕ spec.view) → ℝ≥0∞) : Prop :=
  ∀ (A : spec.leak → OracleAdv Q R spec.view),
    DistRO (π.post (mapSumRO A)) (F.post (mapSumRO (sim A))) (bound A)

/-! ## Class route -/

/-- Concrete game bound in the random oracle model: the advantage of every distinguisher
`D` with oracle access on input `x` is at most `bound x D`, typically the advantage of an
explicit reduction built from `D`. -/
class ROGameAdvBoundC (G_real G_ideal : ROGame hon leak Q R)
    (bound : hon → (leak → OracleAdv Q R Bool) → ℝ≥0∞) : Prop where
  bound_le : ∀ x (D : leak → OracleAdv Q R Bool),
    Advantage (G_real.exp x D) (G_ideal.exp x D) ≤ bound x D

/-- The distinguisher that the game bound receives from adversary `A` and environment `Z`:
`A` on the game output, then `Z.dist` on the adversary channel. -/
def roEnvReduction {V : Type} (A : leak → OracleAdv Q R V)
    (Z : ROEnv hon Q R (Unit ⊕ V)) : leak → OracleAdv Q R Bool :=
  fun l => (A l).bind fun v => Z.dist (.inr v)

/-- UC bound induced by a game bound: the game bound at the environment's input and at
`roEnvReduction A Z`. -/
noncomputable def roGameUCBound {V : Type}
    (bound : hon → (leak → OracleAdv Q R Bool) → ℝ≥0∞) :
    (leak → OracleAdv Q R V) → ROEnv hon Q R (Unit ⊕ V) → ℝ≥0∞ :=
  fun A Z => bound Z.input (roEnvReduction A Z)

/-- The wrapped game followed by the adversary `A`, run with `D`, is the game run with
`A` followed by `D` on the adversary channel. -/
theorem ROGame.exp_ofGame_post {V : Type} (g : ROGame hon leak Q R)
    (A : leak → OracleAdv Q R V) (x : hon) (D : Unit ⊕ V → OracleAdv Q R Bool) :
    (g.ofGame.post (mapSumRO A)).exp x D = g.exp x fun l => (A l).bind fun v => D (.inr v) := by
  rw [ROGame.exp_post, ROGame.exp_ofGame]
  simp only [mapSumRO, OracleAdv.bind_assoc, OracleAdv.bind_ret]

/-- A per-distinguisher game bound gives concrete UC emulation in the random oracle model,
with simulator `S = A` and the bound evaluated at `roEnvReduction A Z`. -/
theorem UCEmulatesROSim_of_advantage {V : Type} {G_real G_ideal : ROGame hon leak Q R}
    {bound : hon → (leak → OracleAdv Q R Bool) → ℝ≥0∞}
    (hAdv : ∀ x D, Advantage (G_real.exp x D) (G_ideal.exp x D) ≤ bound x D) :
    UCEmulatesROSim (UCSpec.ofGame hon leak V) G_real.ofGame G_ideal.ofGame id
      (roGameUCBound bound) := by
  intro A Z
  simp only [ROEnv.gap, ROGame.exp_ofGame_post, id]
  rw [ROGame.prTrue_exp G_real, ROGame.prTrue_exp G_ideal]
  exact hAdv Z.input (roEnvReduction A Z)

/-- Concrete UC emulation in the random oracle model of `G_real.ofGame` by
`G_ideal.ofGame` with view type `V`, simulator `S = A`, and the bound induced by the game
bound `bound`. -/
class UCFromROGameC (G_real G_ideal : ROGame hon leak Q R) (V : Type)
    (bound : hon → (leak → OracleAdv Q R Bool) → ℝ≥0∞) : Prop where
  uc : UCEmulatesROSim (UCSpec.ofGame hon leak V) G_real.ofGame G_ideal.ofGame id
    (roGameUCBound bound)

/-- A concrete game bound in the random oracle model gives concrete UC emulation. -/
instance ucFromROGameC_of_adv {V : Type} {G_real G_ideal : ROGame hon leak Q R}
    {bound : hon → (leak → OracleAdv Q R Bool) → ℝ≥0∞}
    [ROGameAdvBoundC G_real G_ideal bound] : UCFromROGameC G_real G_ideal V bound :=
  ⟨UCEmulatesROSim_of_advantage ROGameAdvBoundC.bound_le⟩

end UCConcreteOracle

end CatCrypt.Crypto
