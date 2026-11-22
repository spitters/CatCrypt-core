/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.TripleRatchetCorrupt
public import CatCryptCore.Crypto.Messaging.SignalStackPQXDH

/-!
# PQXDH followed by the triple ratchet realizes secure messaging with corruption

The ratchet of this module is the root-mixed product ratchet (the Diffie–Hellman and KEM CKAs
combined in one root step through a dual PRF), called the triple ratchet below. The Triple
Ratchet of Dodis, Jost, Katsumata, Prest and Schmidt (ePrint 2025/078) and deployed Signal
(Double Ratchet plus SPQR) keep two root chains and mix the two message keys per message
(`mk = KDF_HYBRID(ec_mk, pq_mk)`), so the theorems here are about the root-mixed variant and
not about the deployed protocol.

The post-quantum Signal stack runs the PQXDH key exchange and keys the triple ratchet
`acdSM (prodCKA (dhCKA Gc) (kemCKA KEM)) R Ch D` with the session key of PQXDH as the first root
key. This module proves that the stack realizes the secure-messaging functionality `F_SM` of
`CatCryptCore.Crypto.Messaging.SignalStackSM` over the triple ratchet, behind the PQXDH channel
simulator `chanSim (simProt P G) pqFwd`.

**The composition over a forwarding simulator.** `stack_realizes_FSM_of` is the
secure-messaging form of `stack_realizes_FSC_of`: a key exchange `X` that realizes `F_AKE`
behind a forwarding simulator `π` with the bound `ε`, followed by the ratchet layer
`smCorruptLayer M ini Sch t n ΔFS ΔPCS`, realizes `F_SM M ini Sch t n ΔFS ΔPCS` behind
`chanSim π F` with the bound `fsmBoundOf ε π F`: `ε` at the environment reduced through the
ratchet layer, and per key of the run the corruption advantages of the reductions `smHopRed` and
the probability that the key is read twice. The last term is `1` when both partners of an
unexposed session always read their key, and the bound is then at least `1`: each `getKey` runs
a session of its own, and the partners share no channel.

**The PQXDH instance.** `pqxdh_realizes_FSM` is that composition at the PQXDH square
`pqxdh_realizesSim_gapDH` with the forwarding data `pqFwd` of `SignalStackPQXDH`, and
`pqxdh_tripleRatchet_realizes_FSM` is its instance at the triple ratchet.

## Main definitions

* `fsmBoundOf`: the bound of a key exchange followed by the ratchet layer.
* `pqxdhFsmBound`: that bound at the PQXDH square.

## Main results

* `stack_realizes_FSM_of`: a key exchange behind a forwarding simulator followed by the ratchet
  layer realizes `F_SM`.
* `pqxdh_realizes_FSM`: PQXDH followed by the ratchet layer realizes `F_SM`.
* `pqxdh_tripleRatchet_realizes_FSM`: PQXDH followed by the triple ratchet realizes `F_SM`.

## References

* E. Kret, R. Schmidt, *The PQXDH Key Agreement Protocol*, Signal specification, 2023
* Y. Dodis, D. Jost, S. Katsumata, T. Prest, R. Schmidt, *Triple Ratchet: A Bandwidth
  Efficient Hybrid-Secure Signal Protocol*, ePrint 2025/078
* R. Canetti, P. Jain, M. Swanberg, M. Varia, *Universally composable end-to-end secure
  messaging*, CRYPTO 2022
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Messaging

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Assumptions
  CatCrypt.Crypto.PRPPRF CatCryptCore.Examples.CyclicGroupDDH CatCrypt.Examples.KEMDEM
open CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.Messaging.SignalStackUC CatCrypt.Crypto.Messaging.SignalStackSM
  CatCrypt.Crypto.Messaging.SignalStack
open CatCrypt.Crypto.Messaging.SignalStackPQXDH (pqFwd)
open CatCrypt.Crypto.AKE.X3DHSquare (FEv FOut subView)
open CatCrypt.Crypto.AKE.PQXDHSquare (pqxdhReal simProt simProt_opaque OEv POut)
open CatCrypt.Crypto.AKE.PQXDHSquareGDH (gdhBoundP pqxdh_realizesSim_gapDH)
open CatCrypt.Crypto.KEM.Games (Scheme)
open CatCrypt.Crypto.PAKE.CPaceSquare (PureNF)
open CatCrypt.Crypto.PAKE.DHExtract (DHGroup)
open PubView (eqView)
open scoped ENNReal

/-! ## The composition over a forwarding simulator -/

section Of

variable {K Sst Pub Rand Wd Ct Leak V τ σ AE R : Type} [Fintype Rand] [Nonempty Rand]
  [Fintype K] [Nonempty K] [Inhabited K]

/-- **The bound of a key exchange followed by the ratchet layer** at an environment `Z`: the
bound `ε` of the key exchange at the environment reduced through the ratchet layer, and, at the
environment `Z'` reduced through the channel simulator `simSCOver π F`, over the keys `i` below
the number of activations of `Z'`, the corruption advantages of the reductions
`smHopRed i j Z'` over the `n` challenges `j` and the probability that the key `i` is read
twice. -/
noncomputable def fsmBoundOf (ε : (ζ : Type) → Env (Strat ζ (HEv ⊕ AE) (HOut K ⊕ R)) ζ → ℝ≥0∞)
    (π : MultiHybrid σ (HEv ⊕ AE) (HOut K ⊕ R) (FEv K) (FOut K)) (F : FwdData σ R)
    (M : SMScheme Sst Pub Rand Wd Ct Leak) (ini : K → SPComp (Pub × Sst × Sst))
    (hini : ∀ k, PureNF (ini k))
    (Sch : Pub → OracleAdv (SMQuery Wd) (SMSchemeAns Pub Ct Leak) V) (t n ΔFS ΔPCS : ℕ)
    (ζ : Type) (Z : Env (Strat ζ (HEv ⊕ AE) (HOut V ⊕ R)) ζ) : ℝ≥0∞ :=
  ε (ζ × Unit) ((Hybrid.seqCtxR (E := HEv ⊕ AE) (smCorruptLayer M ini Sch t n ΔFS ΔPCS)
      (keyLayer_noFail fun k => (smSessView_pureNF hini Sch t n ΔFS ΔPCS _ k).2)).reduceEnv Z) +
    ∑ i ∈ Finset.range ((simSCOver (V := V) π F).reduceEnv (.inr .idle) Z).input.rounds,
      ((∑ j ∈ Finset.range n, M.corruptAdvantage ΔFS ΔPCS
          (smHopRed M ini Sch t n ΔFS ΔPCS i j ((simSCOver π F).reduceEnv (.inr .idle) Z))) +
        prBad (hyb (smRealView M ini Sch t n ΔFS ΔPCS) (smIdealView M ini Sch t n ΔFS ΔPCS) i)
          (reuse i) ((simSCOver π F).reduceEnv (.inr .idle) Z))

/-- **A key exchange followed by the ratchet layer realizes secure messaging with corruption**
(genuine UC).

*Ideal functionality.* `F_SM M ini Sch t n ΔFS ΔPCS`: the multi-session functionality over
`F_AKE` with unlinked delivery whose completed sessions have the ideal view of the schedule
`Sch` and whose exposed sessions have the real view under the adversary key.

*Real world.* A key exchange `X` followed by the ratchet layer
`smCorruptLayer M ini Sch t n ΔFS ΔPCS`, which runs the schedule against the oracles of `M`
keyed by the session key of every `getKey` answer.

*Simulator.* `chanSim π F`: the simulator `π` of the key exchange, a forwarding simulator for
the data `F`, with its decisions read over `F_SC`.

*Bound.* For a key exchange that realizes `F_AKE` behind `π` with the bound `ε`, and a scheme
whose initialisation is `ini` at a uniform key with `ini k` neither touching the heap nor
failing, the distance is at most `fsmBoundOf ε π F`: `ε` at the environment reduced through the
ratchet layer, and per key of the run the corruption advantages of the explicit reductions
`smHopRed i j` over the challenges `j < n` and the probability that the key is read twice. -/
theorem stack_realizes_FSM_of (X : Sys τ (HEv ⊕ AE) (HOut K ⊕ R))
    (π : MultiHybrid σ (HEv ⊕ AE) (HOut K ⊕ R) (FEv K) (FOut K))
    (hπ : π.Opaque ((keHonView (K := K)).sum (eqView (E := AE) (O := R))) subView)
    (F : FwdData σ R) (hF : IsFwd π F)
    {ε : (ζ : Type) → Env (Strat ζ (HEv ⊕ AE) (HOut K ⊕ R)) ζ → ℝ≥0∞}
    (hX : RealizesSim X (F_AKE (SPComp.sample K) true) (Simulator.ofMultiHybrid π hπ) ε)
    (M : SMScheme Sst Pub Rand Wd Ct Leak)
    (ini : K → SPComp (Pub × Sst × Sst)) (hM : M.init = SPComp.bind (SPComp.sample K) ini)
    (hini : ∀ k, PureNF (ini k))
    (Sch : Pub → OracleAdv (SMQuery Wd) (SMSchemeAns Pub Ct Leak) V) (t n ΔFS ΔPCS : ℕ) :
    RealizesSim (X.seq (smCorruptLayer M ini Sch t n ΔFS ΔPCS)) (F_SM M ini Sch t n ΔFS ΔPCS)
      (chanSim π F) (fsmBoundOf ε π F M ini hini Sch t n ΔFS ΔPCS) := by
  have hR : ∀ k, SPComp.IsPure (smRealView M ini Sch t n ΔFS ΔPCS k) ∧
      SPComp.NoFail (smRealView M ini Sch t n ΔFS ΔPCS k) := fun k =>
    smSessView_pureNF hini Sch t n ΔFS ΔPCS _ k
  have h := stack_realizes_FSC_of X π hπ F hF hX (smRealView M ini Sch t n ΔFS ΔPCS)
    (smIdealView M ini Sch t n ΔFS ΔPCS) hR (smIdealView_pureNF hini Sch t n ΔFS ΔPCS)
  intro ζ Z
  refine (h ζ Z).trans ?_
  simp only [fsmBoundOf, scBound]
  exact add_le_add le_rfl (Finset.sum_le_sum fun i _ =>
    add_le_add_left (advantageA_hopRed_le M ini hM Sch t n ΔFS ΔPCS i _) _)

end Of

/-! ## The PQXDH stack -/

section PQXDH

variable {S W RK PKp SKp SSp Cp Sst Pub Rand Wd Ct Leak V : Type} [Field S] [Fintype S]
  [SampleableType W] [Fintype RK] [Nonempty RK] [Inhabited RK] [DecidableEq SSp]
  [Fintype Rand] [Nonempty Rand]

/-- **The bound of PQXDH followed by the ratchet layer**: `fsmBoundOf` at the gap
Diffie–Hellman bound `gdhBoundP` of the PQXDH square and the PQXDH simulator with the
forwarding data `pqFwd`. -/
noncomputable def pqxdhFsmBound (KP : Scheme PKp SKp SSp Cp) (G : DHGroup S W)
    (N : Finset PartyId) (M : SMScheme Sst Pub Rand Wd Ct Leak)
    (ini : RK → SPComp (Pub × Sst × Sst)) (hini : ∀ k, PureNF (ini k))
    (Sch : Pub → OracleAdv (SMQuery Wd) (SMSchemeAns Pub Ct Leak) V) (t n ΔFS ΔPCS : ℕ)
    (ζ : Type) (Z : Env (Strat ζ (OEv W SSp Cp) (HOut V ⊕ POut S W RK PKp Cp)) ζ) : ℝ≥0∞ :=
  fsmBoundOf (fun _ Z => gdhBoundP KP G N (OProt.oracle.reduction Z))
    (simProt (K := RK) KP G) pqFwd M ini hini Sch t n ΔFS ΔPCS ζ Z

/-- **PQXDH followed by the ratchet layer realizes secure messaging with corruption** (genuine
UC).

*Ideal functionality.* `F_SM M ini Sch t n ΔFS ΔPCS`, as in `signal_stack_realizes_FSM`.

*Real world.* The real PQXDH protocol `pqxdhReal KP G` followed by the ratchet layer
`smCorruptLayer M ini Sch t n ΔFS ΔPCS`.

*Simulator.* `chanSim (simProt KP G) pqFwd`, the PQXDH simulator over `F_SC`: it keeps a copy
of the real state, draws the long-term, session and KEM secrets, forwards the honest events,
corrupts under the static rule and delivers keys through `newKey` or `newKeyUnlinked`.

*Bound.* For a scheme whose initialisation is `ini` at a uniform key with `ini k` neither
touching the heap nor failing, for every finite set of parties `N` and every environment `Z`,
the distance is at most `pqxdhFsmBound`: the gap Diffie–Hellman bound of the PQXDH square, and
per key of the run the corruption advantages of the explicit reductions `smHopRed i j` over the
challenges `j < n` and the probability that the key is read twice. -/
theorem pqxdh_realizes_FSM (KP : Scheme PKp SKp SSp Cp) (G : DHGroup S W)
    (N : Finset PartyId) (M : SMScheme Sst Pub Rand Wd Ct Leak)
    (ini : RK → SPComp (Pub × Sst × Sst)) (hM : M.init = SPComp.bind (SPComp.sample RK) ini)
    (hini : ∀ k, PureNF (ini k))
    (Sch : Pub → OracleAdv (SMQuery Wd) (SMSchemeAns Pub Ct Leak) V) (t n ΔFS ΔPCS : ℕ) :
    RealizesSim ((pqxdhReal (K := RK) KP G).seq (smCorruptLayer M ini Sch t n ΔFS ΔPCS))
      (F_SM M ini Sch t n ΔFS ΔPCS) (chanSim (simProt KP G) pqFwd)
      (pqxdhFsmBound KP G N M ini hini Sch t n ΔFS ΔPCS) :=
  stack_realizes_FSM_of (pqxdhReal (K := RK) KP G) (simProt KP G) (simProt_opaque KP G) pqFwd
    (SignalStackPQXDH.simProt_isFwd G KP) (pqxdh_realizesSim_gapDH KP G N) M ini hM hini Sch t n
    ΔFS ΔPCS

end PQXDH

/-! ## PQXDH followed by the triple ratchet -/

section Triple

variable {S W : Type} [Field S] [Fintype S] [SampleableType W] (G : DHGroup S W)
  (Gc : Type) [CyclicGroup Gc] {PKp SKp SSp Cp PK SK K E Rk RK Sa Wd Ct V : Type}
  [DecidableEq SSp] [Inhabited K] [Fintype Rk] [Nonempty Rk] [SampleableType Wd]
  [SampleableType Ct] [Fintype RK] [Nonempty RK] [Inhabited RK]

/-- **PQXDH followed by the triple ratchet realizes secure messaging with corruption** (genuine
UC): `pqxdh_realizes_FSM` at the triple ratchet `acdSM (prodCKA (dhCKA Gc) (kemCKA KEM)) R Ch D`
keyed through `acdIni`, for a ratchet KEM whose key generation and encapsulation neither touch
the heap nor fail.

*Ideal functionality.* `F_SM` over `acdSM (prodCKA (dhCKA Gc) (kemCKA KEM)) R Ch D` keyed
through `acdIni (prodCKA (dhCKA Gc) (kemCKA KEM))`.

*Real world.* The real PQXDH protocol `pqxdhReal KP G` followed by the ratchet layer over the
triple ratchet, with the PQXDH session key as the first root key.

*Simulator.* `chanSim (simProt KP G) pqFwd`, the PQXDH channel simulator.

*Bound.* `pqxdhFsmBound` over the triple ratchet: the gap Diffie–Hellman bound of the PQXDH
square and the corruption advantages of the triple ratchet at the reductions `smHopRed i j`
(bounded by `tripleRatchet_corruptAdvantage_le`), plus the probability that a key is read
twice. -/
theorem pqxdh_tripleRatchet_realizes_FSM (KP : Scheme PKp SKp SSp Cp) (N : Finset PartyId)
    (KEM : KEMScheme PK SK K E) [CKACoins (kemCKA KEM) Rk] (hk : PureNF KEM.kgen)
    (he : ∀ pk, PureNF (KEM.encap pk))
    (R : PRGDef (RK × (Gc × K)) (RK × Sa)) (Ch : PRGDef Sa (Wd × Sa)) (D : AEADDef Wd Ct)
    (Sch : (Gc × (Option E × PK)) → OracleAdv (SMQuery Wd)
      (SMSchemeAns (Gc × (Option E × PK)) Ct
        (SMPartySt ((Gc × CyclicGroup.Exp Gc) × (PK × SK)) RK Sa)) V)
    (t n ΔFS ΔPCS : ℕ) :
    RealizesSim ((pqxdhReal (K := RK) KP G).seq
        (smCorruptLayer (acdSM (prodCKA (dhCKA Gc) (kemCKA KEM)) R Ch D)
          (acdIni (prodCKA (dhCKA Gc) (kemCKA KEM))) Sch t n ΔFS ΔPCS))
      (F_SM (acdSM (prodCKA (dhCKA Gc) (kemCKA KEM)) R Ch D)
        (acdIni (prodCKA (dhCKA Gc) (kemCKA KEM))) Sch t n ΔFS ΔPCS)
      (chanSim (simProt KP G) pqFwd)
      (pqxdhFsmBound KP G N (acdSM (prodCKA (dhCKA Gc) (kemCKA KEM)) R Ch D)
        (acdIni (prodCKA (dhCKA Gc) (kemCKA KEM)))
        (acdIni_pureNF (prodCKA_pureNF (dhCKA_pureNF Gc) (kemCKA_pureNF KEM hk he)).1) Sch t n
        ΔFS ΔPCS) :=
  pqxdh_realizes_FSM KP G N (acdSM (prodCKA (dhCKA Gc) (kemCKA KEM)) R Ch D)
    (acdIni (prodCKA (dhCKA Gc) (kemCKA KEM)))
    (acdSM_init_eq _ R Ch D (prodCKA_pureNF (dhCKA_pureNF Gc) (kemCKA_pureNF KEM hk he)).1.1)
    (acdIni_pureNF (prodCKA_pureNF (dhCKA_pureNF Gc) (kemCKA_pureNF KEM hk he)).1) Sch t n
    ΔFS ΔPCS

end Triple

end CatCrypt.Crypto.Messaging
