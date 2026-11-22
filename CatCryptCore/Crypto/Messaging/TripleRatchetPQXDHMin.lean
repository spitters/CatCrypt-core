/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.TripleRatchetPQXDH
public import CatCryptCore.Crypto.AKE.PQXDHSquareKEM

/-!
# The PQXDH Signal stack with the KEM route at matched sessions

The triple ratchet of this module is the root-mixed product ratchet (the Diffie–Hellman and KEM
CKAs combined in one root step through a dual PRF). The Triple Ratchet of Dodis, Jost,
Katsumata, Prest and Schmidt (ePrint 2025/078) and deployed Signal (Double Ratchet plus SPQR)
keep two root chains and mix the two message keys per message
(`mk = KDF_HYBRID(ec_mk, pq_mk)`), so the theorems here are about the root-mixed variant and
not about the deployed protocol.

The PQXDH Signal stack and PQXDH followed by the triple ratchet realize `F_SC` and `F_SM`
(`pqxdh_stack_realizes_FSC`, `pqxdh_tripleRatchet_realizes_FSM`) at the gap Diffie–Hellman bound
of the PQXDH square. This module proves the same statements at the bound `minBoundP` of
`pqxdh_realizesSim_min`: the gap Diffie–Hellman sum plus the minimum of the gap Diffie–Hellman
sum and the KEM bound `kemBound`. The bad event at matched sessions, whose encapsulation comes
from the partner, is bounded by the IND-CCA advantage of explicit reductions, the correctness
error of the KEM and the number of queries over the number of shared secrets, without any
Diffie–Hellman assumption; the bad event at unmatched sessions stays on the gap Diffie–Hellman
route. Because the gap Diffie–Hellman sum is outside the minimum, `minBoundP` is at least the
bound `gdhBoundP` of the gap Diffie–Hellman statements, and the theorems of this module need the
gap Diffie–Hellman assumption. The bounds also contain the probability that a key is read twice,
which is `1` when both partners of an unexposed session always read their key. The compositions
are `stack_realizes_FSC_of` and `stack_realizes_FSM_of` at `pqxdh_realizesSim_min`.

## Main definitions

* `pqxdhStackBoundMin`: the bound of the PQXDH Signal stack at `minBoundP`.
* `pqxdhFsmBoundMin`: `fsmBoundOf` at the bound `minBoundP`.

## Main results

* `pqxdh_stack_realizes_FSC_min`: the PQXDH Signal stack realizes `F_SC` at
  `pqxdhStackBoundMin`.
* `pqxdh_realizes_FSM_min`: PQXDH followed by the ratchet layer realizes `F_SM` at
  `pqxdhFsmBoundMin`.
* `pqxdh_tripleRatchet_realizes_FSM_min`: PQXDH followed by the triple ratchet realizes `F_SM`
  at `pqxdhFsmBoundMin`.

## References

* E. Kret, R. Schmidt, *The PQXDH Key Agreement Protocol*, Signal specification, 2023
* Y. Dodis, D. Jost, S. Katsumata, T. Prest, R. Schmidt, *Triple Ratchet: A Bandwidth
  Efficient Hybrid-Secure Signal Protocol*, ePrint 2025/078
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Messaging

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Assumptions
  CatCrypt.Crypto.PRPPRF CatCryptCore.Examples.CyclicGroupDDH CatCrypt.Examples.KEMDEM
open CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.Messaging.SignalStackUC CatCrypt.Crypto.Messaging.SignalStackSM
  CatCrypt.Crypto.Messaging.SignalStack
open CatCrypt.Crypto.Messaging.SignalStackPQXDH (pqFwd simProt_isFwd)
open CatCrypt.Crypto.AKE.PQXDHSquare (pqxdhReal simProt simProt_opaque OEv OOut POut)
open CatCrypt.Crypto.AKE.PQXDHSquareKEM (minBoundP pqxdh_realizesSim_min)
open CatCrypt.Crypto.KEM.Games (Scheme)
open CatCrypt.Crypto.PAKE.CPaceSquare (PureNF)
open CatCrypt.Crypto.PAKE.DHExtract (DHGroup)
open scoped ENNReal

/-! ## The secure channel -/

section Stack

variable {S W K PK SK SS C V : Type} [Field S] [Fintype S] [SampleableType W] [Fintype K]
  [Nonempty K] [Inhabited K] [DecidableEq SS] [Fintype SS] [Nonempty SS] [DecidableEq C]
  [DecidableEq PK] (P : Scheme PK SK SS C) (G : DHGroup S W)

/-- The bound of the PQXDH Signal stack with the KEM route at matched sessions at an environment
`Z`: the bound `minBoundP` of the PQXDH square at the environment reduced through the key layer,
and `scBound` at the environment reduced through the simulator. -/
noncomputable def pqxdhStackBoundMin (I : Finset SessionId) (N : Finset PartyId) (q : ℕ)
    (realV : K → SPComp V) (idealV : SPComp V)
    (hR : ∀ k, SPComp.IsPure (realV k) ∧ SPComp.NoFail (realV k)) (ζ : Type)
    (Z : Env (Strat ζ (OEv W SS C) (HOut V ⊕ POut S W K PK C)) ζ) : ℝ≥0∞ :=
  minBoundP P G I N q ((OProt.oracle (Q := OEv W SS C) (A := OOut S W K PK C)).reduction
      ((Hybrid.seqCtxR (E := OEv W SS C) (keyLayer realV)
        (keyLayer_noFail fun k => (hR k).2)).reduceEnv Z)) +
    scBound realV idealV ((simSCOver (simProt (K := K) P G) pqFwd).reduceEnv (.inr .idle) Z)

/-- **The PQXDH Signal stack realizes `F_SC`, with gap Diffie–Hellman plus the minimum of gap
Diffie–Hellman and the KEM route** (genuine UC).

*Ideal functionality.* `F_SC realV idealV`, as in `pqxdh_stack_realizes_FSC`.

*Real world.* The real PQXDH protocol `pqxdhReal P G` followed by the key layer
`keyLayer realV`.

*Simulator.* `chanSim (simProt P G) pqFwd`, the PQXDH simulator with its decisions read over
`F_SC`.

*Bound.* For views that neither touch the heap nor fail, for every finite set of session
identifiers `I`, finite set of parties `N` and query bound `q`, and every environment `Z`, the
distance is at most `pqxdhStackBoundMin`: at the environment reduced through the key layer, the
gap Diffie–Hellman sum plus the minimum of the gap Diffie–Hellman sum and the KEM bound
`kemBound` (`⊤` when the oracle reduction names a party outside `N`, a session outside `I` or
asks more than `q` queries), plus `scBound realV idealV` at the environment reduced through the
simulator. -/
theorem pqxdh_stack_realizes_FSC_min (I : Finset SessionId) (N : Finset PartyId) (q : ℕ)
    (realV : K → SPComp V) (idealV : SPComp V)
    (hR : ∀ k, SPComp.IsPure (realV k) ∧ SPComp.NoFail (realV k))
    (hI : SPComp.IsPure idealV ∧ SPComp.NoFail idealV) :
    RealizesSim ((pqxdhReal (K := K) P G).seq (keyLayer realV)) (F_SC realV idealV)
      (chanSim (simProt P G) pqFwd) (pqxdhStackBoundMin P G I N q realV idealV hR) :=
  stack_realizes_FSC_of (pqxdhReal (K := K) P G) (simProt P G) (simProt_opaque P G) pqFwd
    (simProt_isFwd G P) (pqxdh_realizesSim_min P G I N q) realV idealV hR hI

end Stack

/-! ## Secure messaging with corruption -/

section PQXDH

variable {S W RK PKp SKp SSp Cp Sst Pub Rand Wd Ct Leak V : Type} [Field S] [Fintype S]
  [SampleableType W] [Fintype RK] [Nonempty RK] [Inhabited RK] [DecidableEq SSp]
  [Fintype SSp] [Nonempty SSp] [DecidableEq Cp] [DecidableEq PKp] [Fintype Rand] [Nonempty Rand]

/-- **The bound of PQXDH followed by the ratchet layer with the KEM route at matched sessions**:
`fsmBoundOf` at the bound `minBoundP` of the PQXDH square and the PQXDH simulator with the
forwarding data `pqFwd`. -/
noncomputable def pqxdhFsmBoundMin (KP : Scheme PKp SKp SSp Cp) (G : DHGroup S W)
    (I : Finset SessionId) (N : Finset PartyId) (q : ℕ) (M : SMScheme Sst Pub Rand Wd Ct Leak)
    (ini : RK → SPComp (Pub × Sst × Sst)) (hini : ∀ k, PureNF (ini k))
    (Sch : Pub → OracleAdv (SMQuery Wd) (SMSchemeAns Pub Ct Leak) V) (t n ΔFS ΔPCS : ℕ)
    (ζ : Type) (Z : Env (Strat ζ (OEv W SSp Cp) (HOut V ⊕ POut S W RK PKp Cp)) ζ) : ℝ≥0∞ :=
  fsmBoundOf (fun _ Z => minBoundP KP G I N q (OProt.oracle.reduction Z))
    (simProt (K := RK) KP G) pqFwd M ini hini Sch t n ΔFS ΔPCS ζ Z

/-- **PQXDH followed by the ratchet layer realizes `F_SM`, with gap Diffie–Hellman plus the
minimum of gap Diffie–Hellman and the KEM route** (genuine UC).

*Ideal functionality.* `F_SM M ini Sch t n ΔFS ΔPCS`, as in `pqxdh_realizes_FSM`.

*Real world.* The real PQXDH protocol `pqxdhReal KP G` followed by the ratchet layer
`smCorruptLayer M ini Sch t n ΔFS ΔPCS`.

*Simulator.* `chanSim (simProt KP G) pqFwd`, the PQXDH simulator over `F_SC`.

*Bound.* For a scheme whose initialisation is `ini` at a uniform key with `ini k` neither
touching the heap nor failing, for every finite set of session identifiers `I`, finite set of
parties `N` and query bound `q`, and every environment `Z`, the distance is at most
`pqxdhFsmBoundMin`: the bound `minBoundP` of the PQXDH square (the gap Diffie–Hellman sum plus
the minimum of the gap Diffie–Hellman sum and the KEM bound), and per key of the run the
corruption advantages of the explicit reductions `smHopRed i j` over the challenges `j < n` and
the probability that the key is read twice. -/
theorem pqxdh_realizes_FSM_min (KP : Scheme PKp SKp SSp Cp) (G : DHGroup S W)
    (I : Finset SessionId) (N : Finset PartyId) (q : ℕ) (M : SMScheme Sst Pub Rand Wd Ct Leak)
    (ini : RK → SPComp (Pub × Sst × Sst)) (hM : M.init = SPComp.bind (SPComp.sample RK) ini)
    (hini : ∀ k, PureNF (ini k))
    (Sch : Pub → OracleAdv (SMQuery Wd) (SMSchemeAns Pub Ct Leak) V) (t n ΔFS ΔPCS : ℕ) :
    RealizesSim ((pqxdhReal (K := RK) KP G).seq (smCorruptLayer M ini Sch t n ΔFS ΔPCS))
      (F_SM M ini Sch t n ΔFS ΔPCS) (chanSim (simProt KP G) pqFwd)
      (pqxdhFsmBoundMin KP G I N q M ini hini Sch t n ΔFS ΔPCS) :=
  stack_realizes_FSM_of (pqxdhReal (K := RK) KP G) (simProt KP G) (simProt_opaque KP G) pqFwd
    (simProt_isFwd G KP) (pqxdh_realizesSim_min KP G I N q) M ini hM hini Sch t n ΔFS ΔPCS

end PQXDH

/-! ## PQXDH followed by the triple ratchet -/

section Triple

variable {S W : Type} [Field S] [Fintype S] [SampleableType W] (G : DHGroup S W)
  (Gc : Type) [CyclicGroup Gc] {PKp SKp SSp Cp PK SK K E Rk RK Sa Wd Ct V : Type}
  [DecidableEq SSp] [Fintype SSp] [Nonempty SSp] [DecidableEq Cp] [DecidableEq PKp]
  [Inhabited K] [Fintype Rk] [Nonempty Rk] [SampleableType Wd]
  [SampleableType Ct] [Fintype RK] [Nonempty RK] [Inhabited RK]

/-- **PQXDH followed by the triple ratchet realizes `F_SM`, with gap Diffie–Hellman plus the
minimum of gap Diffie–Hellman and the KEM route** (genuine UC): `pqxdh_realizes_FSM_min` at the
triple ratchet
`acdSM (prodCKA (dhCKA Gc) (kemCKA KEM)) R Ch D` keyed through `acdIni`, for a ratchet KEM whose
key generation and encapsulation neither touch the heap nor fail.

*Ideal functionality.* `F_SM` over `acdSM (prodCKA (dhCKA Gc) (kemCKA KEM)) R Ch D` keyed
through `acdIni (prodCKA (dhCKA Gc) (kemCKA KEM))`.

*Real world.* The real PQXDH protocol `pqxdhReal KP G` followed by the ratchet layer over the
triple ratchet, with the PQXDH session key as the first root key.

*Simulator.* `chanSim (simProt KP G) pqFwd`, the PQXDH channel simulator.

*Bound.* `pqxdhFsmBoundMin` over the triple ratchet: the bound `minBoundP` of the PQXDH square,
which is the gap Diffie–Hellman sum for the unmatched sessions plus, for the matched sessions,
the minimum of that sum and the KEM bound of `KP`, and the corruption advantages of the triple
ratchet at the reductions `smHopRed i j`, plus the probability that a key is read twice. -/
theorem pqxdh_tripleRatchet_realizes_FSM_min (KP : Scheme PKp SKp SSp Cp) (I : Finset SessionId)
    (N : Finset PartyId) (q : ℕ)
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
      (pqxdhFsmBoundMin KP G I N q (acdSM (prodCKA (dhCKA Gc) (kemCKA KEM)) R Ch D)
        (acdIni (prodCKA (dhCKA Gc) (kemCKA KEM)))
        (acdIni_pureNF (prodCKA_pureNF (dhCKA_pureNF Gc) (kemCKA_pureNF KEM hk he)).1) Sch t n
        ΔFS ΔPCS) :=
  pqxdh_realizes_FSM_min KP G I N q (acdSM (prodCKA (dhCKA Gc) (kemCKA KEM)) R Ch D)
    (acdIni (prodCKA (dhCKA Gc) (kemCKA KEM)))
    (acdSM_init_eq _ R Ch D (prodCKA_pureNF (dhCKA_pureNF Gc) (kemCKA_pureNF KEM hk he)).1.1)
    (acdIni_pureNF (prodCKA_pureNF (dhCKA_pureNF Gc) (kemCKA_pureNF KEM hk he)).1) Sch t n
    ΔFS ΔPCS

end Triple

end CatCrypt.Crypto.Messaging
