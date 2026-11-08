/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.X3DHSquareGDH
public import CatCryptCore.Crypto.Messaging.DoubleRatchet
public import CatCryptCore.Crypto.UCCascade
public import CatCryptCore.Crypto.UCConcreteTimed
import CatCryptCore.Tactics.DeriveTimed

/-!
# The Signal stack: X3DH, then the double ratchet keyed by the X3DH session key

The Signal protocol runs the X3DH key agreement and keys the root key of the double ratchet with
the session key that X3DH outputs. This module states the stack over the core results:
* the X3DH square `X3DHSquareGDH.x3dh_realizesSim_gapDH`: the real protocol `x3dhReal G`
  realizes the ideal key exchange `F_AKE` behind the simulator `x3dhSim G`, with the gap
  Diffie–Hellman bound `gdhBound`;
* the secure-messaging game of `DoubleRatchet`: `sm_real` (a uniform root key) against `sm_ideal`
  (uniform ciphertexts), with the advantage `SM_Advantage`.

**The keyed ratchet.** `smRealAt C R G D msgs rk` is `sm_real` with the root key `rk` given:
`sm_real` is the uniform root key followed by `smRealAt` (`sm_real_eq_bind_smRealAt`).

**The stack as a system.** `smLayer sm` is the ratchet as a layer above a key exchange: on the
output `key (some k)` of the honest port it outputs the view `sm k` of the ratchet keyed by `k`,
and every other output passes. The real Signal stack is `(x3dhReal G).seq (smLayer sm)`, and
`signal_stack_realizes` states that it realizes the stack over `F_AKE`,
`(x3dhIdeal G).seq (smLayer sm)`, by the cascade `UCCascade.realizes_seq_left`.

**The stack as a game.** An environment `Z` runs against a world `X` (a key exchange: `x3dhReal G`
or `x3dhIdeal G`) and ends in the state `z`; the ratchet then runs on the key `sel z` and the
distinguisher `A` sees `z` and the view of the ratchet (`stackGame`). The real Signal stack keys
`smRealAt` with `sel z` against the real protocol; the ideal Signal stack runs `sm_ideal` against
`F_AKE` behind the simulator. `signal_stack_advantage_le` bounds their distance, for every
environment, selection and distinguisher, by three explicit terms (the hybrids of the proof):
1. the gap Diffie–Hellman bound of the X3DH square at the environment `stackEnv`, the environment
   `Z` whose distinguisher runs the keyed ratchet on `sel z` and then `A`;
2. `keyRORAdv`: the real-or-random advantage of the key `sel z` in the world of `F_AKE`, at the
   distinguisher `stackRORDist` that runs the keyed ratchet on the key it receives;
3. the secure-messaging advantage of the reduction `stackSMRed`, which runs `Z` against the world
   of `F_AKE` and calls `A` on its final state and the challenge view.

The second term is information-theoretic: it compares two games over the ideal functionality and
the simulator, with no computational assumption. It is the composition gap of the stack, see the
section *The composition gap*; `SignalStackSealed.signal_stack_advantage_le_sealed` is the stack
theorem without it, for a sealed environment.

**Time.** `stackSMRed` and the distinguisher `stackDist` of `stackEnv` have costed trees
(`stackSMRed.tree`, `stackDist.tree`), compile theorems, costed forms derived by `derive_timed`
and time theorems: the time of `stackSMRed` is the time of `Z` over its activations, the time of
the steps of the world, `8` per activation and the time of `A` (`stackSMRed.tree.timeBound_timed`);
the time of `stackDist` is the time of the keyed ratchet and of `A`
(`stackDist.tree.timeBound_timed`), the distinguisher cost of the environment reduction of
`UCOracleGameTimed.reduction.timeBound_timed`, whose oracle adversary is the argument of `gdhRed`
priced by `X3DHSquareGDHTimed.gdhOut_timeBound`.

## The composition gap

The ideal stack of a Signal session is `F_AKE` followed by the ratchet keyed by a uniform key
independent of the view of the environment. The step from the key of `F_AKE` to such a key is
`keyRORAdv (x3dhIdeal G) Z sel (stackRORDist f A)`. For a selection `sel` from the final state of
the environment, which the distinguisher sees, the term is not `0` in general: a distinguisher
that compares the key with `sel z` tells the two games apart. The module
`CatCryptCore.Crypto.Messaging.SignalStackSealed` proves the precise statement.
* `x3dhIdeal_key_secrecy`: for an environment `Z` that never chooses `getKey sid₀ pid` for the
  protocol session `sid₀` of the selected session `x₀` (`Sealed sid₀ Z`, a condition on the
  possible outcomes of every choice of `Z`, with the decidable event predicate `SealedEv`), the
  final state of `Z` and the key of `x₀` when `F_AKE` completed it have the law of the final
  state of `Z` and a fresh uniform key. The proof is a coupling: every permutation of the keys,
  applied to the completed keys of `sid₀`, commutes with the steps of `F_AKE` behind `x3dhSim`
  at the events of a sealed environment.
* `keyRORAdv_readKey_eq_zero`: for the environment `readKey Z x₀`, which runs a sealed `Z` and
  then reads the key of `x₀` on the honest port, the selection of the key it reads, and a
  distinguisher that sees the final state of `Z` and the key, `keyRORAdv` is `0` when every run
  of `Z` against the world of `F_AKE` completes `x₀` (`CompletesAt G x₀ Z`: `x₀` received a key
  chosen by `F_AKE`, not exposed at delivery).
* `signal_stack_advantage_le_sealed` (with `_primitives` and `_dh`): the stack theorem for
  `readKey Z x₀` under these two conditions, with the gap Diffie–Hellman term and the
  secure-messaging term only.

## Main definitions

* `smRealAt`: the secure-messaging real game with a given root key.
* `CKAPureNF`: a CKA whose initialisation and sending neither touch the heap nor fail.
* `smLayer`: the ratchet as a layer above the honest port of a key exchange.
* `x3dhIdeal`: `F_AKE` with uniform keys behind the X3DH simulator.
* `stackGame`, `stackDist`, `stackEnv`, `stackSMRed`, `stackRORDist`, `keyRORAdv`: the stack
  game, the environment of the X3DH step, the secure-messaging reduction, and the real-or-random
  term of the key.

## Main results

* `sm_real_eq_bind_smRealAt`: `sm_real` is a uniform root key followed by `smRealAt`.
* `signal_stack_realizes`: the Signal stack over X3DH realizes the stack over `F_AKE` behind the
  simulator, with the gap Diffie–Hellman bound at the environment reduced through the ratchet.
* `stack_advantage_le`: the hybrid argument of the stack game over any two worlds.
* `signal_stack_advantage_le`: **the Signal stack theorem**.
* `signal_stack_advantage_le_primitives`, `signal_stack_advantage_le_dh`: the stack theorem
  with the secure-messaging term expanded to the CKA (or DDH), root-KDF PRG and FS-AEAD
  advantages of the reductions of `DoubleRatchet` at `stackSMRed`.
* `dhCKA_pureNF`: the Diffie–Hellman CKA satisfies `CKAPureNF`.
* `stackSMRed.tree.timeBound_timed`, `stackDist.tree.timeBound_timed`: the time certificates.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Messaging.SignalStack

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Messaging
open CatCrypt.Crypto.Assumptions CatCryptCore.Examples.CyclicGroupDDH
open CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.PAKE.DHExtract CatCrypt.Crypto.PAKE.CPaceSquare
open CatCrypt.Crypto.AKE.X3DHSquare CatCrypt.Crypto.AKE.X3DHSquareGDH
open scoped ENNReal

/-! ## The keyed ratchet -/

section Keyed

variable {Sc Msg Key RK Sa M Ct : Type} [SampleableType M] [SampleableType Ct]

/-- **The secure-messaging real game with the root key `rk`**: the CKA run of one epoch per
entry of `msgs` and the ciphertexts of the epochs from the root key `rk`. -/
noncomputable def smRealAt (C : CKADef Sc Msg Key) (R : PRGDef (RK × Key) (RK × Sa))
    (G : PRGDef Sa (M × Sa)) (D : AEADDef M Ct) (msgs : List (List (M × M))) (rk : RK) :
    SPComp (SMView Msg Ct) :=
  SPComp.bind C.init fun i =>
    SPComp.bind (ckaRun C msgs.length i.2.1 i.2.2) fun p =>
      SPComp.pure ((i.1, p.1.map Prod.fst), smCts G D (rootRun R rk (p.1.map Prod.snd)) msgs)

/-- A CKA whose initialisation and sending neither touch the heap nor fail. -/
def CKAPureNF (C : CKADef Sc Msg Key) : Prop :=
  PureNF C.init ∧ ∀ s, PureNF (C.send s)

/-- The epochs of a CKA of `CKAPureNF` neither touch the heap nor fail. -/
theorem ckaRun_pureNF {C : CKADef Sc Msg Key} (hC : CKAPureNF C) :
    ∀ (n : ℕ) (s r : Sc), PureNF (ckaRun C n s r)
  | 0, _, _ => pureNF_pure _
  | n + 1, s, _ =>
    (hC.2 s).bind fun _ => (ckaRun_pureNF hC n _ _).bind fun _ => pureNF_pure _

omit [SampleableType Ct] in
/-- The keyed real game of a CKA of `CKAPureNF` neither touches the heap nor fails. -/
theorem smRealAt_pureNF {C : CKADef Sc Msg Key} (hC : CKAPureNF C)
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (M × Sa)) (D : AEADDef M Ct)
    (msgs : List (List (M × M))) (rk : RK) : PureNF (smRealAt C R G D msgs rk) := by
  unfold smRealAt
  exact hC.1.bind fun _ => (ckaRun_pureNF hC _ _ _).bind fun _ => pureNF_pure _

variable [Fintype Key] [Nonempty Key] [Fintype RK] [Nonempty RK] [Fintype Sa] [Nonempty Sa]

omit [SampleableType Ct] [Fintype Key] [Nonempty Key] [Fintype Sa] [Nonempty Sa] in
/-- **`sm_real` is a uniform root key followed by the keyed game.** -/
theorem sm_real_eq_bind_smRealAt (C : CKADef Sc Msg Key) (R : PRGDef (RK × Key) (RK × Sa))
    (G : PRGDef Sa (M × Sa)) (D : AEADDef M Ct) (msgs : List (List (M × M))) :
    sm_real C R G D msgs = SPComp.bind (SPComp.sample RK) (smRealAt C R G D msgs) := by
  unfold sm_real smRealAt
  have h : ∀ i : Msg × Sc × Sc,
      SPComp.bind (ckaRun C msgs.length i.2.1 i.2.2) (fun p =>
        SPComp.bind (SPComp.sample RK) fun rk =>
          SPComp.pure ((i.1, p.1.map Prod.fst), smCts G D (rootRun R rk (p.1.map Prod.snd)) msgs)) =
      SPComp.bind (SPComp.sample RK) fun rk =>
        SPComp.bind (ckaRun C msgs.length i.2.1 i.2.2) fun p =>
          SPComp.pure ((i.1, p.1.map Prod.fst), smCts G D (rootRun R rk (p.1.map Prod.snd)) msgs) :=
    fun i => SPComp.isPure_bind_comm_right _ _ _ (SPComp.sample_isPure RK)
  simp only [h]
  exact SPComp.isPure_bind_comm_right _ _ _ (SPComp.sample_isPure RK)

end Keyed

/-! ## The stack game over a world -/

section Game

variable {τ υ ζ E O V Kk : Type}

/-- **The stack game**: the environment `Z` runs against the world `X` and ends in the state `z`,
then the ratchet `sm z` runs; the result is `z` and the view of the ratchet. -/
noncomputable def stackGame (X : Sys τ E O) (Z : Strat ζ E O) (sm : ζ → SPComp V) :
    SPComp (ζ × V) :=
  SPComp.bind (view X Z) fun z => SPComp.map (fun v => (z, v)) (sm z)

/-- The distinguisher of the environment of the key-exchange step: on the final state `z`, the
ratchet `sm z`, then `A`. -/
noncomputable def stackDist (sm : ζ → SPComp V) (A : ζ × V → SPComp Bool) (z : ζ) :
    SPComp Bool :=
  SPComp.bind (sm z) fun v => A (z, v)

/-- **The environment of the key-exchange step**: the strategy `Z` from the empty heap, with the
distinguisher `stackDist sm A`. -/
noncomputable def stackEnv (Z : Strat ζ E O) (sm : ζ → SPComp V) (A : ζ × V → SPComp Bool) :
    Env (Strat ζ E O) ζ :=
  ⟨Z, Heap.empty, stackDist sm A⟩

/-- **The secure-messaging reduction**: on the challenge view `v`, it runs `Z` against the world
`X` and calls `A` on the final state and `v`. -/
noncomputable def stackSMRed (X : Sys τ E O) (Z : Strat ζ E O) (A : ζ × V → SPComp Bool)
    (v : V) :
    SPComp Bool :=
  SPComp.bind (view X Z) fun z => A (z, v)

/-- The distinguisher of the key: on the state `z` and the key `k`, the ratchet `f k` keyed by
`k`, then `A`. -/
noncomputable def stackRORDist (f : Kk → SPComp V) (A : ζ × V → SPComp Bool) (p : ζ × Kk) :
    SPComp Bool :=
  SPComp.bind (f p.2) fun v => A (p.1, v)

/-- **The real-or-random advantage of the key `sel z`** in the world `X`: the stack game whose
ratchet returns `sel z` against the stack game whose ratchet returns a uniform key. -/
noncomputable def keyRORAdv [Fintype Kk] [Nonempty Kk] (X : Sys τ E O) (Z : Strat ζ E O)
    (sel : ζ → Kk) (A : ζ × Kk → SPComp Bool) : ℝ≥0∞ :=
  AdvantageA (stackGame X Z fun z => SPComp.pure (sel z)) (stackGame X Z fun _ => SPComp.sample Kk)
    A

/-- The stack game followed by `A` is the view followed by `stackDist`. -/
theorem stackGame_bind (X : Sys τ E O) (Z : Strat ζ E O) (sm : ζ → SPComp V)
    (A : ζ × V → SPComp Bool) :
    SPComp.bind (stackGame X Z sm) A = SPComp.bind (view X Z) (stackDist sm A) := by
  simp only [stackGame, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  rfl

/-- The stack game over a ratchet `c z` followed by `f` is the stack game over `c` followed by
`f` and `A`. -/
theorem stackGame_bind_comp (X : Sys τ E O) (Z : Strat ζ E O) (c : ζ → SPComp Kk)
    (f : Kk → SPComp V) (A : ζ × V → SPComp Bool) :
    SPComp.bind (stackGame X Z fun z => SPComp.bind (c z) f) A =
      SPComp.bind (stackGame X Z c) (stackRORDist f A) := by
  simp only [stackGame, stackRORDist, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]

/-- With a ratchet `c` that does not touch the heap, the stack game followed by `A` is `c`
followed by the secure-messaging reduction. -/
theorem stackGame_bind_isPure (X : Sys τ E O) (Z : Strat ζ E O) {c : SPComp V}
    (hc : SPComp.IsPure c) (A : ζ × V → SPComp Bool) :
    SPComp.bind (stackGame X Z fun _ => c) A = SPComp.bind c (stackSMRed X Z A) := by
  rw [stackGame_bind]
  exact SPComp.isPure_bind_comm_right (view X Z) c (fun z v => A (z, v)) hc

/-- The advantage of the stack games over two worlds is the gap of `stackEnv` between the views
of the worlds. -/
theorem advantageA_stackGame (X : Sys τ E O) (Y : Sys υ E O) (Z : Strat ζ E O)
    (sm : ζ → SPComp V) (A : ζ × V → SPComp Bool) :
    AdvantageA (stackGame X Z sm) (stackGame Y Z sm) A =
      Env.gap (view X) (view Y) (stackEnv Z sm A) := by
  simp only [AdvantageA, Advantage, Env.gap, absDiff, stackGame_bind, stackEnv]

/-- **The hybrid argument of the stack.** For the world `X` of the protocol and the world `Y` of
the functionality, a keyed ratchet `f` whose game at a uniform key is `c₁`, and an ideal ratchet
`c₀`, both not touching the heap, the distance between the ratchet keyed by `sel z` over `X` and
the ideal ratchet over `Y` is at most the gap of `stackEnv` between the worlds, the real-or-random
advantage of the key over `Y` and the advantage of `stackSMRed` between `c₁` and `c₀`. -/
theorem stack_advantage_le [Fintype Kk] [Nonempty Kk] (X : Sys τ E O) (Y : Sys υ E O)
    (Z : Strat ζ E O) (sel : ζ → Kk) (f : Kk → SPComp V) {c₁ c₀ : SPComp V}
    (hc : c₁ = SPComp.bind (SPComp.sample Kk) f) (h₁ : SPComp.IsPure c₁)
    (h₀ : SPComp.IsPure c₀) (A : ζ × V → SPComp Bool) :
    AdvantageA (stackGame X Z fun z => f (sel z)) (stackGame Y Z fun _ => c₀) A ≤
      Env.gap (view X) (view Y) (stackEnv Z (fun z => f (sel z)) A) +
        keyRORAdv Y Z sel (stackRORDist f A) + AdvantageA c₁ c₀ (stackSMRed Y Z A) := by
  have e₁ : AdvantageA (stackGame X Z fun z => f (sel z)) (stackGame Y Z fun z => f (sel z)) A =
      Env.gap (view X) (view Y) (stackEnv Z (fun z => f (sel z)) A) :=
    advantageA_stackGame X Y Z _ A
  have e₂ : AdvantageA (stackGame Y Z fun z => f (sel z)) (stackGame Y Z fun _ => c₁) A =
      keyRORAdv Y Z sel (stackRORDist f A) := by
    have ha : (fun z : ζ => f (sel z)) = fun z => SPComp.bind (SPComp.pure (sel z)) f := by
      funext z; rw [SPComp.pure_bind]
    have hb : (fun _ : ζ => c₁) = fun _ => SPComp.bind (SPComp.sample Kk) f := by
      funext _; exact hc
    simp only [keyRORAdv, AdvantageA]
    rw [ha, hb, stackGame_bind_comp, stackGame_bind_comp]
  have e₃ : AdvantageA (stackGame Y Z fun _ => c₁) (stackGame Y Z fun _ => c₀) A =
      AdvantageA c₁ c₀ (stackSMRed Y Z A) := by
    simp only [AdvantageA]
    rw [stackGame_bind_isPure Y Z h₁, stackGame_bind_isPure Y Z h₀]
  unfold AdvantageA at e₁ e₂ e₃ ⊢
  calc Advantage (SPComp.bind (stackGame X Z fun z => f (sel z)) A)
        (SPComp.bind (stackGame Y Z fun _ => c₀) A)
      ≤ Advantage (SPComp.bind (stackGame X Z fun z => f (sel z)) A)
          (SPComp.bind (stackGame Y Z fun z => f (sel z)) A) +
        Advantage (SPComp.bind (stackGame Y Z fun z => f (sel z)) A)
          (SPComp.bind (stackGame Y Z fun _ => c₀) A) := advantage_triangle _ _ _
    _ ≤ Advantage (SPComp.bind (stackGame X Z fun z => f (sel z)) A)
          (SPComp.bind (stackGame Y Z fun z => f (sel z)) A) +
        (Advantage (SPComp.bind (stackGame Y Z fun z => f (sel z)) A)
          (SPComp.bind (stackGame Y Z fun _ => c₁) A) +
        Advantage (SPComp.bind (stackGame Y Z fun _ => c₁) A)
          (SPComp.bind (stackGame Y Z fun _ => c₀) A)) :=
        add_le_add le_rfl (advantage_triangle _ _ _)
    _ = _ := by rw [e₁, e₂, e₃, add_assoc]

end Game

/-! ## The ratchet as a layer above a key exchange -/

section Layer

variable {S W K V : Type}

/-- **The ratchet layer**: on the output `key (some k)` of the honest port, the view `sm k` of the
ratchet keyed by `k`; every other output passes. -/
noncomputable def smLayer (sm : K → SPComp V) :
    Sys Unit (OOut S W K) (HOut V ⊕ ROut S W K) where
  init := ()
  step _ o := match o with
    | .inl .ok => SPComp.pure ((), .inl .ok)
    | .inl (.key none) => SPComp.pure ((), .inl (.key none))
    | .inl (.key (some k)) => SPComp.map (fun v => ((), .inl (.key (some v)))) (sm k)
    | .inr r => SPComp.pure ((), .inr r)

/-- The layer of a ratchet that never fails never fails. -/
theorem smLayer_noFail {sm : K → SPComp V} (hsm : ∀ k, SPComp.NoFail (sm k)) (u : Unit)
    (o : OOut S W K) : SPComp.NoFail ((smLayer (S := S) (W := W) sm).step u o) := by
  rcases o with (_ | (_ | k)) | r
  · exact SPComp.pure_noFail _
  · exact SPComp.pure_noFail _
  · simp only [smLayer, SPComp.map]
    exact Assumptions.SPComp.bind_noFail (hsm k) fun _ => SPComp.pure_noFail _
  · exact SPComp.pure_noFail _

end Layer

/-! ## The Signal stack -/

section Stack

variable {S W K : Type} [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K]
  [Inhabited K] (G : DHGroup S W)

/-- **The world of `F_AKE`**: the ideal key exchange with uniform keys, without key
confirmation, behind the X3DH simulator. -/
noncomputable abbrev x3dhIdeal :=
  (x3dhSim (K := K) G).withSub (F_AKE (SPComp.sample K) true)

/-- **The Signal stack as a system** (composition plumbing). For every finite set of parties `P`
and every ratchet `sm` that never fails, the stack of the real X3DH protocol and the ratchet
layer realizes the stack of `F_AKE` behind the X3DH simulator and the same layer: for every
environment `Z`, the distance is at most the gap Diffie–Hellman bound of the X3DH square at the
environment reduced through the layer. -/
theorem signal_stack_realizes {V : Type} (P : Finset PartyId) (sm : K → SPComp V)
    (hsm : ∀ k, SPComp.NoFail (sm k)) :
    Realizes ((x3dhReal (K := K) G).seq (smLayer sm)) ((x3dhIdeal G).seq (smLayer sm))
      (fun _ Z => gdhBound G P ((OProt.oracle (Q := OEv W) (A := OOut S W K)).reduction
        ((Hybrid.seqCtxR (E := OEv W) (smLayer sm) (smLayer_noFail hsm)).reduceEnv Z))) :=
  realizes_seq_left _ (smLayer_noFail hsm) (x3dh_realizesSim_gapDH G P)

variable {Sc Msg Key Sa M Ct : Type} [SampleableType M] [SampleableType Ct] [Fintype Key]
  [Nonempty Key] [Fintype Sa] [Nonempty Sa]

omit [Fintype Key] [Nonempty Key] [Fintype Sa] [Nonempty Sa] in
/-- **The Signal stack theorem.** Let the CKA `C` neither touch the heap nor fail. For every
finite set of parties `P`, every environment `Z` of the X3DH protocol, every selection `sel` of
the session key from the final state of `Z` and every distinguisher `A` of the final state and
the view of the ratchet, the distance between
* the real stack: `Z` against the real X3DH protocol, then the double ratchet `smRealAt` with the
  root key `sel z`, and
* the ideal stack: `Z` against `F_AKE` behind the X3DH simulator, then `sm_ideal`,

is at most the gap Diffie–Hellman bound of the X3DH square at the environment `stackEnv`, the
real-or-random advantage of the key `sel z` in the world of `F_AKE` (the composition gap, an
information-theoretic term of the ideal functionality), and the secure-messaging advantage of the
reduction `stackSMRed`, which runs `Z` against the world of `F_AKE`. For an environment that reads
the key of the selected session only at the end and a selection of that key,
`SignalStackSealed.signal_stack_advantage_le_sealed` removes the second term. -/
theorem signal_stack_advantage_le (P : Finset PartyId) {C : CKADef Sc Msg Key}
    (hC : CKAPureNF C) (R : PRGDef (K × Key) (K × Sa)) (Gp : PRGDef Sa (M × Sa))
    (D : AEADDef M Ct) (msgs : List (List (M × M))) {ζ : Type}
    (Z : Strat ζ (OEv W) (OOut S W K)) (sel : ζ → K)
    (A : ζ × SMView Msg Ct → SPComp Bool) :
    AdvantageA (stackGame (x3dhReal (K := K) G) Z fun z => smRealAt C R Gp D msgs (sel z))
        (stackGame (x3dhIdeal G) Z fun _ => sm_ideal C msgs) A ≤
      gdhBound G P ((OProt.oracle (Q := OEv W) (A := OOut S W K)).reduction
          (stackEnv Z (fun z => smRealAt C R Gp D msgs (sel z)) A)) +
        keyRORAdv (x3dhIdeal G) Z sel (stackRORDist (smRealAt C R Gp D msgs) A) +
        SM_Advantage C R Gp D msgs (stackSMRed (x3dhIdeal G) Z A) := by
  refine (stack_advantage_le _ _ Z sel (smRealAt C R Gp D msgs)
    (sm_real_eq_bind_smRealAt C R Gp D msgs)
    (sm_real_isPure C hC.1.1 (fun s => (hC.2 s).1) R Gp D msgs)
    (sm_ideal_isPure C hC.1.1 (fun s => (hC.2 s).1) msgs) A).trans ?_
  gcongr
  · exact x3dh_realizesSim_gapDH G P ζ _
  · exact le_of_eq rfl

/-- **The Signal stack theorem at the primitives.** The bound of `signal_stack_advantage_le`
with the secure-messaging advantage of `stackSMRed` expanded by `sm_advantage_le`: over the
epochs `t`, the CKA advantages of `smCKARed`, the PRG advantages of the root KDF at
`smRootRed` and the FS-AEAD advantages of `smAEADRed`, each at the reduction `stackSMRed`. -/
theorem signal_stack_advantage_le_primitives (P : Finset PartyId) {C : CKADef Sc Msg Key}
    (hC : CKAPureNF C) (R : PRGDef (K × Key) (K × Sa)) (Gp : PRGDef Sa (M × Sa))
    (D : AEADDef M Ct) (msgs : List (List (M × M))) {ζ : Type}
    (Z : Strat ζ (OEv W) (OOut S W K)) (sel : ζ → K)
    (A : ζ × SMView Msg Ct → SPComp Bool) :
    AdvantageA (stackGame (x3dhReal (K := K) G) Z fun z => smRealAt C R Gp D msgs (sel z))
        (stackGame (x3dhIdeal G) Z fun _ => sm_ideal C msgs) A ≤
      gdhBound G P ((OProt.oracle (Q := OEv W) (A := OOut S W K)).reduction
          (stackEnv Z (fun z => smRealAt C R Gp D msgs (sel z)) A)) +
        keyRORAdv (x3dhIdeal G) Z sel (stackRORDist (smRealAt C R Gp D msgs) A) +
        (∑ t ∈ Finset.range msgs.length,
            CKA_Advantage C t (msgs.length - (t + 1))
              (smCKARed R Gp D msgs t (stackSMRed (x3dhIdeal G) Z A)) +
          ∑ t ∈ Finset.range msgs.length,
            PRG_Advantage R
              (smRootRed C R Gp D msgs t (msgs.length - (t + 1)) (stackSMRed (x3dhIdeal G) Z A)) +
          ∑ t ∈ Finset.range msgs.length,
            FSAEAD_Advantage Gp D (msgs.getD t [])
              (smAEADRed C Gp D msgs t (msgs.length - (t + 1))
                (stackSMRed (x3dhIdeal G) Z A))) :=
  (signal_stack_advantage_le G P hC R Gp D msgs Z sel A).trans
    (add_le_add le_rfl (sm_advantage_le C R Gp D msgs _))

omit [Fintype Key] [Nonempty Key] in
/-- The Diffie–Hellman CKA neither touches the heap nor fails. -/
theorem dhCKA_pureNF (Gc : Type) [CyclicGroup Gc] : CKAPureNF (dhCKA Gc) := by
  refine ⟨?_, fun _ => ?_⟩ <;> simp only [dhCKA] <;>
    exact (pureNF_sample _).bind fun _ => pureNF_pure _

omit [Fintype Key] [Nonempty Key] in
/-- **The Signal stack theorem with the Diffie–Hellman CKA.** With the CKA `dhCKA Gc` over
the cyclic group `Gc`, the CKA terms of `signal_stack_advantage_le_primitives` are the DDH
advantages of `ckaDDHRed` at `smCKARed` (`sm_dh_advantage_le`). -/
theorem signal_stack_advantage_le_dh (P : Finset PartyId) (Gc : Type) [CyclicGroup Gc]
    (R : PRGDef (K × Gc) (K × Sa)) (Gp : PRGDef Sa (M × Sa)) (D : AEADDef M Ct)
    (msgs : List (List (M × M))) {ζ : Type} (Z : Strat ζ (OEv W) (OOut S W K)) (sel : ζ → K)
    (A : ζ × SMView Gc Ct → SPComp Bool) :
    AdvantageA
        (stackGame (x3dhReal (K := K) G) Z fun z => smRealAt (dhCKA Gc) R Gp D msgs (sel z))
        (stackGame (x3dhIdeal G) Z fun _ => sm_ideal (dhCKA Gc) msgs) A ≤
      gdhBound G P ((OProt.oracle (Q := OEv W) (A := OOut S W K)).reduction
          (stackEnv Z (fun z => smRealAt (dhCKA Gc) R Gp D msgs (sel z)) A)) +
        keyRORAdv (x3dhIdeal G) Z sel (stackRORDist (smRealAt (dhCKA Gc) R Gp D msgs) A) +
        (∑ t ∈ Finset.range msgs.length,
            DDH_Advantage Gc (ckaDDHRed t (msgs.length - (t + 1))
              (smCKARed R Gp D msgs t (stackSMRed (x3dhIdeal G) Z A))) +
          ∑ t ∈ Finset.range msgs.length,
            PRG_Advantage R (smRootRed (dhCKA Gc) R Gp D msgs t (msgs.length - (t + 1))
              (stackSMRed (x3dhIdeal G) Z A)) +
          ∑ t ∈ Finset.range msgs.length,
            FSAEAD_Advantage Gp D (msgs.getD t [])
              (smAEADRed (dhCKA Gc) Gp D msgs t (msgs.length - (t + 1))
                (stackSMRed (x3dhIdeal G) Z A))) :=
  (signal_stack_advantage_le G P (dhCKA_pureNF Gc) R Gp D msgs Z sel A).trans
    (add_le_add le_rfl (sm_dh_advantage_le Gc R Gp D msgs _))

end Stack

/-! ## Time certificates -/

section Time

variable {τ ζ E O V : Type}

/-- The computation tree of `stackSMRed`: the view of the strategy against the world, then the
distinguisher on the final state and the challenge. -/
noncomputable def stackSMRed.tree (X : Sys τ E O) (Z : Strat ζ E O)
    (next : ζ → SPTree (ζ × E)) (step : τ → E → SPTree (τ × O))
    (obs : ζ → O → SPTree ζ)
    (dist : ζ × V → SPTree Bool) (v : V) : SPTree Bool :=
  (view.tree X Z next step obs).bind fun z => dist (z, v)

/-- The tree of `stackSMRed` compiles to `stackSMRed`. -/
theorem stackSMRed.compile_tree (X : Sys τ E O) (Z : Strat ζ E O)
    {next : ζ → SPTree (ζ × E)} {step : τ → E → SPTree (τ × O)}
    {obs : ζ → O → SPTree ζ}
    {dist : ζ × V → SPTree Bool} {A : ζ × V → SPComp Bool}
    (hn : ∀ z, (next z).compile = Z.next z) (hs : ∀ t e, (step t e).compile = X.step t e)
    (ho : ∀ z o, (obs z o).compile = Z.obs z o) (hd : ∀ p, (dist p).compile = A p) (v : V) :
    (stackSMRed.tree X Z next step obs dist v).compile = stackSMRed X Z A v := by
  simp only [stackSMRed.tree, stackSMRed, SPTree.compile_bind, hd,
    view.compile_tree X Z next step obs hn hs ho]

derive_timed stackSMRed.tree

/-- **Time of the secure-messaging reduction.** On the challenge `v`, for a costed strategy and a
costed step of the world over the same interface, from initial states of their invariants, and a
distinguisher of time at most `tD` on the final states, `stackSMRed` costs at most the time of the
strategy over its `q = Z.rounds` activations, the time of `q` steps of the world, `8` per
activation, `tD` and `4`: the time of the adversary `(Z, A)` plus the steps of the world. -/
theorem stackSMRed.tree.timeBound_timed (X : Sys τ E O) (Z : Strat ζ E O)
    {next : ζ → SPTree.Timed (ζ × E)} {nextCost : ζ → ℕ}
    {step : τ → E → SPTree.Timed (τ × O)} {stepCost : τ → E → ℕ}
    {obs : ζ → O → SPTree.Timed ζ} {obsCost : ζ → O → ℕ}
    {dist : ζ × V → SPTree.Timed Bool} {distCost : ζ × V → ℕ} (v : V)
    {InvZ MidZ : ℕ → ζ → Prop} {InvS : ℕ → τ → Prop} {Ev : ℕ → E → Prop}
    {Out : ℕ → O → Prop}
    {tN tS tO : ℕ → ℕ} {tD : ℕ}
    (hZ : StratRunBound next nextCost obs obsCost InvZ MidZ Ev Out tN tO)
    (hS : SysRunBound step stepCost InvS Ev Out tS)
    (hz : InvZ 0 Z.init) (ht : InvS 0 X.init)
    (hd : ∀ z, InvZ Z.rounds z → SPTree.Timed.stepTime (distCost (z, v), dist (z, v)) ≤ tD) :
    SPTree.Timed.stepTime
        (stackSMRed.tree.timed X Z next nextCost step stepCost obs obsCost dist distCost v) ≤
      (∑ i ∈ Finset.range Z.rounds, (tN i + tO i)) + (∑ i ∈ Finset.range Z.rounds, tS i) +
        8 * Z.rounds + tD + 4 := by
  obtain ⟨hV, hA⟩ := view.tree.timeBound_timed X Z hZ hS hz ht
  have hB := SPTree.Timed.stepTime_bind_le_of_allRet _
    (fun z => (1 + distCost (z, v), dist (z, v))) (1 + tD) hA fun z hz' => by
      have := hd z hz'
      simp only [SPTree.Timed.stepTime] at this ⊢
      omega
  simp only [stackSMRed.tree.timed, SPTree.Timed.stepTime_delay] at hV hB ⊢
  simp only [SPTree.Timed.stepTime] at hV hB ⊢
  omega

/-- The computation tree of `stackDist`: the ratchet on the final state, then the
distinguisher. -/
noncomputable def stackDist.tree (sm : ζ → SPTree V) (dist : ζ × V → SPTree Bool) (z : ζ) :
    SPTree Bool :=
  (sm z).bind fun v => dist (z, v)

/-- The tree of `stackDist` compiles to `stackDist`. -/
theorem stackDist.compile_tree {sm : ζ → SPTree V} {dist : ζ × V → SPTree Bool}
    {smC : ζ → SPComp V} {A : ζ × V → SPComp Bool} (hs : ∀ z, (sm z).compile = smC z)
    (hd : ∀ p, (dist p).compile = A p) (z : ζ) :
    (stackDist.tree sm dist z).compile = stackDist smC A z := by
  simp only [stackDist.tree, stackDist, SPTree.compile_bind, hs, hd]

derive_timed stackDist.tree

/-- **Time of the distinguisher of the key-exchange step.** On the final state `z`, for a costed
ratchet of time at most `TS` at `z` whose results lie in `Q` and a distinguisher of time at most
`TD` at the results of `Q`, `stackDist` costs at most `TS + TD + 2`. This is the distinguisher
cost of the environment reduction of `stackEnv` (`OProt.reduction.timeBound_timed`). -/
theorem stackDist.tree.timeBound_timed (sm : ζ → SPTree.Timed V) (smCost : ζ → ℕ)
    (dist : ζ × V → SPTree.Timed Bool) (distCost : ζ × V → ℕ) (z : ζ) {Q : V → Prop}
    {TS TD : ℕ} (hs : SPTree.Timed.stepTime (smCost z, sm z) ≤ TS)
    (hQ : SPTree.Timed.AllRet Q (sm z))
    (hd : ∀ v, Q v → SPTree.Timed.stepTime (distCost (z, v), dist (z, v)) ≤ TD) :
    SPTree.Timed.stepTime (stackDist.tree.timed sm smCost dist distCost z) ≤ TS + TD + 2 := by
  have hB := SPTree.Timed.stepTime_bind_le_of_allRet (sm z)
    (fun v => (1 + distCost (z, v), dist (z, v))) (TD + 1) hQ fun v hv => by
      have := hd v hv
      simp only [SPTree.Timed.stepTime] at this ⊢
      omega
  simp only [stackDist.tree.timed, SPTree.Timed.stepTime_delay] at hB hs ⊢
  simp only [SPTree.Timed.stepTime] at hB hs ⊢
  omega

end Time

end CatCrypt.Crypto.Messaging.SignalStack
