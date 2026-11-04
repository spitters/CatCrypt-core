/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Category.ProtBicatSys
public import CatCryptCore.Crypto.UCPullbackSemantics

/-!
# The protocol bicategory in systems as a change of semantics

The map `ProtObj.toSys` from the 1-cells of the protocol bicategory `ProtBicat SPComp` (one-shot
protocols) to reactive systems is a change of semantics in the sense of `UCPullbackSemantics`:
a pullback from an advantage theory of one-shot protocols to the environment theory of systems.

The *advantage theory of one-shot protocols* `oneShotTheory hon α` has the Kleisli maps
`hon → SPComp α` as systems; a test is a one-shot distinguisher (a Boolean continuation, an input
and an initial heap), and the advantage is its distinguishing gap. Its supremum over all tests is
the statistical distance `sdist` that the 2-cells `ProtMorε` bound (`oneShotTheory_iSup_adv`).

An environment `Z` of the stateless system activates it `Z.input.rounds` times, each time on an
input it chooses adaptively; the advantage of `Z` is bounded by the number of rounds times the
one-shot distance, and is not the advantage of a single one-shot test. The single-pull shape of
`AdvPullback` does not fit; this file states the generalisation that does:

* A *rounds-graded pullback* (`AdvPullbackRounds T T'`) has a relation `Rel`, a round count
  `rounds t` of each test `t` of `T'`, and a family `pull t i` of tests of `T`, with the law
  `adv' x' y' t ≤ rounds t * ⨆ i, adv x y (pull t i)` on related pairs. Its pullback law
  (`AdvPullbackRounds.realizes_rel`) sends a realization with bound `b` to one with bound
  `rounds t * ⨆ i, b (pull t i)`. Every `AdvPullback` is one with one round
  (`AdvPullback.toRounds`), and a rounds-graded pullback precomposes with an `AdvPullback`
  (`AdvPullbackRounds.precomp`).
* The stateless semantics `statelessPullback hon α` relates a Kleisli map `π` to every system step
  equivalent to `Sys.stateless π`; its round count is `Z.input.rounds`, and it pulls `Z` back to
  the family of all one-shot tests, since `Z` chooses input and continuation of each round.

`realizes_stateless_of_sdist` and `ProtMorε.realizesSim_toSys` (with bound
`Z.input.rounds * ε`) are instances of the law. Horizontal composition and identities are carried
by the relation (`statelessPullback_rel_hcomp`, `statelessPullback_rel_hid`): this is the
functoriality of the relation, from `ProtObj.toSys_hcomp_stepEq` and `ProtObj.toSys_hid_stepEq`.

## Main definitions

* `AdvPullbackRounds`, `AdvPullback.toRounds`, `AdvPullbackRounds.precomp`
* `oneShotTheory`, `statelessPullback`

## Main results

* `AdvPullbackRounds.realizes_rel` — the rounds-graded pullback law.
* `oneShotTheory_iSup_adv`, `oneShotTheory_realizes_iff` — the one-shot theory measures `sdist`.
* `UCMonad.statelessPullback_rel_toSys`, `UCMonad.statelessPullback_rel_hcomp`,
  `UCMonad.statelessPullback_rel_hid` — 1-cells, horizontal composition and identities.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open scoped ENNReal

universe u v u' v' u'' v'' w

/-! ## Rounds-graded pullbacks -/

/-- A rounds-graded pullback from the advantage theory `T` to `T'`: a relation `Rel` from systems
of `T` to systems of `T'`, a round count of each test of `T'`, and a family of tests of `T`
pulled back from each test of `T'`, such that the advantage of a test between related images is
at most its round count times the supremum of the advantages of the pulled-back tests. -/
structure AdvPullbackRounds (T : AdvTheory.{u, v}) (T' : AdvTheory.{u', v'}) where
  /-- The relation from source systems to image systems. -/
  Rel : T.System → T'.System → Prop
  /-- The round count of a test. -/
  rounds : T'.Test → ℕ
  /-- The index type of the tests pulled back from a test. -/
  Pulls : T'.Test → Type w
  /-- The family of tests pulled back from a test. -/
  pull : (t : T'.Test) → Pulls t → T.Test
  /-- The advantage of `t` between related images is at most `rounds t` times the supremum of
  the advantages of the pulled-back tests. -/
  adv_rel : ∀ {x x' y y'}, Rel x x' → Rel y y' → ∀ t,
    T'.adv x' y' t ≤ rounds t * ⨆ i, T.adv x y (pull t i)

namespace AdvPullbackRounds

variable {T : AdvTheory.{u, v}} {T' : AdvTheory.{u', v'}} {T'' : AdvTheory.{u'', v''}}

/-- **Rounds-graded pullback law.** A realization with bound `b` gives a realization of the
related images with bound `rounds t` times the supremum of `b` over the pulled-back tests. -/
theorem realizes_rel (F : AdvPullbackRounds.{u, v, u', v', w} T T') {x y : T.System}
    {x' y' : T'.System} (hx : F.Rel x x') (hy : F.Rel y y') {b : T.Test → ℝ≥0∞}
    (h : T.Realizes x y b) :
    T'.Realizes x' y' (fun t => F.rounds t * ⨆ i, b (F.pull t i)) := fun t =>
  (F.adv_rel hx hy t).trans (mul_le_mul' le_rfl (iSup_mono fun _ => h _))

/-- **Constant bounds.** A realization with the constant bound `ε` gives a realization of the
related images with bound `rounds t * ε`. -/
theorem realizes_rel_const (F : AdvPullbackRounds.{u, v, u', v', w} T T') {x y : T.System}
    {x' y' : T'.System} (hx : F.Rel x x') (hy : F.Rel y y') {ε : ℝ≥0∞}
    (h : T.Realizes x y fun _ => ε) :
    T'.Realizes x' y' (fun t => F.rounds t * ε) := fun t =>
  (F.realizes_rel hx hy h t).trans (mul_le_mul' le_rfl (iSup_le fun _ => le_rfl))

/-- The precomposite of a rounds-graded pullback `G` with a pullback `F`: the relational
composite on systems, `F.pull` after the family of `G` on tests, the round count of `G`. -/
def precomp (F : AdvPullback T T') (G : AdvPullbackRounds.{u', v', u'', v'', w} T' T'') :
    AdvPullbackRounds.{u, v, u'', v'', w} T T'' where
  Rel x z := ∃ y, F.Rel x y ∧ G.Rel y z
  rounds := G.rounds
  Pulls := G.Pulls
  pull t i := F.pull (G.pull t i)
  adv_rel := by
    rintro _ _ _ _ ⟨_, hx, hx'⟩ ⟨_, hy, hy'⟩ t
    refine (G.adv_rel hx' hy' t).trans (le_of_eq ?_)
    simp only [F.adv_rel hx hy]

end AdvPullbackRounds

/-- A pullback as a rounds-graded pullback with one round and one pulled-back test. -/
def AdvPullback.toRounds {T : AdvTheory.{u, v}} {T' : AdvTheory.{u', v'}} (F : AdvPullback T T') :
    AdvPullbackRounds.{u, v, u', v', 0} T T' where
  Rel := F.Rel
  rounds _ := 1
  Pulls _ := Unit
  pull t _ := F.pull t
  adv_rel := by
    intro _ _ _ _ hx hy t
    simp [F.adv_rel hx hy t]

/-! ## The advantage theory of one-shot protocols -/

/-- The advantage theory of one-shot protocols `hon → SPComp α`: a test is a one-shot
distinguisher (a Boolean continuation, an input and an initial heap), and its advantage is the
distinguishing gap. -/
noncomputable def oneShotTheory (hon α : Type) : AdvTheory.{0, 0} where
  System := hon → SPComp α
  Test := (α → SPComp Bool) × hon × Heap
  adv π₁ π₂ t := absDiff (prTrue (SPComp.bind (π₁ t.2.1) t.1) t.2.2)
    (prTrue (SPComp.bind (π₂ t.2.1) t.1) t.2.2)

/-- The supremum of the advantages of all one-shot tests is the statistical distance. -/
theorem oneShotTheory_iSup_adv {hon α : Type} (π₁ π₂ : hon → SPComp α) :
    ⨆ t, (oneShotTheory hon α).adv π₁ π₂ t = sdist π₁ π₂ := by
  simp only [oneShotTheory, sdist, iSup_prod]

/-- Realization in the one-shot theory with a constant bound is a bound on `sdist`. -/
theorem oneShotTheory_realizes_iff {hon α : Type} {π₁ π₂ : hon → SPComp α} {ε : ℝ≥0∞} :
    (oneShotTheory hon α).Realizes π₁ π₂ (fun _ => ε) ↔ sdist π₁ π₂ ≤ ε := by
  simpa only [← oneShotTheory_iSup_adv] using ⟨iSup_le, fun h t => (le_iSup _ t).trans h⟩

/-! ## The stateless semantics -/

open CatCrypt.Relational CatCrypt.Crypto.UCCoupling in
/-- The advantage of an environment `Z` between stateless systems is at most `Z.input.rounds`
times the supremum of the advantages of the one-shot tests: each round is coupled up to the
one-shot distance (`realizes_of_couplingApprox`). -/
theorem adv_stateless_le_rounds_iSup {hon α ζ : Type} (π₁ π₂ : hon → SPComp α)
    (Z : Env (Strat ζ hon (Option α)) ζ) :
    adv (Sys.stateless π₁) (Sys.stateless π₂) Z ≤
      Z.input.rounds * ⨆ t, (oneShotTheory hon α).adv π₁ π₂ t := by
  rw [oneShotTheory_iSup_adv]
  refine realizes_of_couplingApprox (Sys.stateless π₁) (Sys.stateless π₂) (fun _ _ => True)
    (sdist π₁ π₂) trivial (fun t u x _ => ?_) ζ Z
  have hx : sdist (fun _ : Unit => π₁ x) (fun _ : Unit => π₂ x) ≤ sdist π₁ π₂ := by
    unfold sdist
    exact iSup_mono fun D => iSup_le fun _ => le_iSup_of_le x le_rfl
  rw [Sys.stateless_step, Sys.stateless_step]
  unfold SPComp.map
  refine rHoareApprox_mono_eps (le_of_eq (add_zero _)) (rHoareApprox_bind
    (rHoareApprox_of_sdist hx) fun r r' => rHoareApprox_of_rHoare ?_)
  exact rHoare_ret fun _ _ hh => ⟨hh.2, trivial, by rw [hh.1]⟩

/-- The stateless semantics of one-shot protocols as a rounds-graded pullback into the
environment theory: `π` is related to every system step equivalent to `Sys.stateless π`; an
environment `Z` has `Z.input.rounds` rounds and pulls back to the family of all one-shot tests. -/
noncomputable def statelessPullback (hon α : Type) :
    AdvPullbackRounds.{0, 0, 1, 1, 0} (oneShotTheory hon α) (envTheory hon (Option α)) where
  Rel π X := Sys.StepEq ⟨Unit, Sys.stateless π⟩ ⟨X.1, X.2⟩
  rounds Z := Z.2.input.rounds
  Pulls _ := (oneShotTheory hon α).Test
  pull _ s := s
  adv_rel := by
    rintro π₁ ⟨_, X⟩ π₂ ⟨_, Y⟩ hX hY ⟨ζ, Z⟩
    exact ((stepEqPullback hon (Option α)).adv_rel (x := ⟨Unit, Sys.stateless π₁⟩)
      (y := ⟨Unit, Sys.stateless π₂⟩) hX hY ⟨ζ, Z⟩).trans_le
      (adv_stateless_le_rounds_iSup π₁ π₂ Z)

/-- `realizes_stateless_of_sdist` is the constant-bound law of `statelessPullback`. -/
example {hon α : Type} {π₁ π₂ : hon → SPComp α} {ε : ℝ≥0∞} (h : sdist π₁ π₂ ≤ ε) :
    Realizes (Sys.stateless π₁) (Sys.stateless π₂) (fun _ Z => Z.input.rounds * ε) :=
  envTheory_realizes_iff.1 ((statelessPullback hon α).realizes_rel_const
    (x' := ⟨Unit, Sys.stateless π₁⟩) (y' := ⟨Unit, Sys.stateless π₂⟩)
    (Relation.EqvGen.refl _) (Relation.EqvGen.refl _) (oneShotTheory_realizes_iff.2 h))

end CatCrypt.Crypto.UCTransparent

namespace UCMonad

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open CatCrypt.Crypto.UCTransparent
open scoped ENNReal

variable {a b c hon out : Type}

/-- **1-cells.** The protocol of a 1-cell `P` is related to its system `P.toSys`. -/
theorem statelessPullback_rel_toSys (P : ProtObj SPComp a b) :
    (statelessPullback a (b ⊕ P.iface)).Rel P.prot ⟨Unit, P.toSys⟩ :=
  Relation.EqvGen.refl _

/-- **Horizontal composition is carried by the relation.** If `P.prot` is related to `X` and
`Q.prot` to `Y`, then `(P.hcomp Q).prot` is related to the cascade of `X` with the router of `Y`
beside the forwarding of the leakage of `P`. -/
theorem statelessPullback_rel_hcomp (P : ProtObj SPComp a b) (Q : ProtObj SPComp b c)
    {X : Σ τ : Type, Sys τ a (Option (b ⊕ P.iface))}
    {Y : Σ τ : Type, Sys τ b (Option (c ⊕ Q.iface))}
    (hX : (statelessPullback a (b ⊕ P.iface)).Rel P.prot X)
    (hY : (statelessPullback b (c ⊕ Q.iface)).Rel Q.prot Y) :
    (statelessPullback a (c ⊕ (P.iface ⊕ Q.iface))).Rel (P.hcomp Q).prot
      ⟨_, X.2.seq ((Y.2.par (Sys.ofFun (id : Option P.iface → Option P.iface))).mapPorts
        hcompRouteEv hcompRouteOut)⟩ :=
  Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (ProtObj.toSys_hcomp_stepEq P Q))
    (Sys.StepEq.seq hX (Sys.StepEq.mapPorts
      (Sys.StepEq.par hY (Relation.EqvGen.refl (SysObj.idSys (Option P.iface))))
      hcompRouteEv hcompRouteOut))

/-- **Identities are carried by the relation.** The protocol of `hid α` is related to the
forwarding system on `α` with its outputs in the honest summand. -/
theorem statelessPullback_rel_hid (α : Type) :
    (statelessPullback α (α ⊕ (ProtObj.hid (T := SPComp) α).iface)).Rel
      (ProtObj.hid (T := SPComp) α).prot
      ⟨_, ((SysObj.idSys α).mapPorts id fun x => some (Sum.inl x)).sys⟩ :=
  ProtObj.toSys_hid_stepEq α

/-- `ProtMorε.realizesSim_toSys` is an instance of the law of `statelessPullback`: the 2-cell
bounds the one-shot distance by `ε`, the law gives `Z.input.rounds * ε`, and the simulator is
absorbed at distance `0` by `realizes_stateless_simWrap`. -/
example {P Q : ProtObj SPComp hon out} {ε : ℝ≥0∞} (f : ProtMorε P Q ε)
    (hsim : ∀ l, SPComp.NoFail (f.sim l)) (ev : hon → hon → Prop) :
    RealizesSim Q.toSys P.toSys (simWrapSim ev f.sim hsim)
      (fun _ Z => Z.input.rounds * ε) := by
  have hd : (oneShotTheory hon (out ⊕ Q.iface)).Realizes Q.prot
      (fun a => SPComp.bind (P.prot a) (mapSum SPComp.pure f.sim)) (fun _ => ε) :=
    oneShotTheory_realizes_iff.2 ((sdist_sym _ _).trans_le f.dist)
  have h₁ := (envTheory_realizes_iff (b := fun _ Z => Z.input.rounds * ε)).1
    ((statelessPullback hon (out ⊕ Q.iface)).realizes_rel_const
    (x' := ⟨Unit, Q.toSys⟩) (y' := ⟨Unit, Sys.stateless _⟩) (statelessPullback_rel_toSys Q)
    (Relation.EqvGen.refl _) hd)
  have h := Realizes.trans h₁ (realizes_stateless_simWrap P.prot f.sim hsim)
  exact fun ζ => (h ζ).mono fun Z => by simp

end UCMonad
