/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.TripleRatchetDeployed
public import CatCryptCore.Crypto.Messaging.TripleRatchetPQXDH

/-!
# PQXDH followed by the deployed Triple Ratchet realizes secure messaging with corruption

The post-quantum Signal stack runs the PQXDH key exchange and keys the deployed Triple Ratchet
`tripleRatchetDeployed` (`TripleRatchetDeployed.lean`) with the session key of PQXDH as the
first root key. `pqxdh_tripleRatchetDeployed_realizes_FSM` is `pqxdh_realizes_FSM`
(`TripleRatchetPQXDH.lean`) at the in-order scheme `toSMScheme` of the deployed Triple Ratchet,
keyed through `tripleRatchetDeployedIni`. Its bound is `pqxdhFsmBound`, which carries the
corruption advantages of the in-order game of the deployed scheme at the reductions `smHopRed`.

## Main definitions

* `tripleRatchetDeployedIni`: the keyed initialisation of the deployed Triple Ratchet.

## Main results

* `tripleRatchetDeployed_init_eq`: the initialisation is the keyed initialisation at a uniform
  root key.
* `pqxdh_tripleRatchetDeployed_realizes_FSM`: PQXDH followed by the deployed Triple Ratchet
  realizes `F_SM`.

## References

* E. Kret, R. Schmidt, *The PQXDH Key Agreement Protocol*, Signal specification, 2023.
* Y. Dodis, D. Jost, S. Katsumata, T. Prest, R. Schmidt, *Triple Ratchet: A Bandwidth Efficient
  Hybrid-Secure Signal Protocol*, ePrint 2025/078.
-/

set_option autoImplicit false

@[expose] public section

namespace CatCrypt.Crypto.Messaging

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Assumptions
open CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.Messaging.SignalStackUC CatCrypt.Crypto.Messaging.SignalStackSM
open CatCrypt.Crypto.Messaging.SignalStackPQXDH (pqFwd)
open CatCrypt.Crypto.AKE.PQXDHSquare (pqxdhReal simProt)
open CatCrypt.Crypto.KEM.Games (Scheme)
open CatCrypt.Crypto.PAKE.CPaceSquare (PureNF pureNF_pure)
open CatCrypt.Crypto.PAKE.DHExtract (DHGroup)
open scoped ENNReal

variable {Sc Msg Key Rand RK Sa W Ct PSt PHdr S : Type} [Inhabited Msg]

/-- **The keyed initialisation of the deployed Triple Ratchet**: the keyed initialisation
`acdIni C rk` of the ACD construction, with the parties embedded into the construction with
headers and the initial states of the sidecar `P` attached. -/
noncomputable def tripleRatchetDeployedIni (C : CKADef Sc Msg Key) (P : SidecarDef PSt PHdr S)
    (rk : RK) :
    SPComp ((Msg × ℕ) × (ACDIDSt Sc RK Sa Msg W × PSt) × (ACDIDSt Sc RK Sa Msg W × PSt)) :=
  SPComp.bind (acdIni (Sa := Sa) C rk) fun i =>
    SPComp.pure ((i.1, 0), (ACDIDSt.embed i.2.1, P.init.1), (ACDIDSt.embed i.2.2, P.init.2))

/-- The keyed initialisation of the deployed Triple Ratchet neither touches the heap nor fails
for a CKA initialisation that neither touches the heap nor fails. -/
theorem tripleRatchetDeployedIni_pureNF {C : CKADef Sc Msg Key} (hC : PureNF C.init)
    (P : SidecarDef PSt PHdr S) (rk : RK) :
    PureNF (tripleRatchetDeployedIni (Sa := Sa) (W := W) C P rk) :=
  (acdIni_pureNF hC rk).bind fun _ => pureNF_pure _

variable [Fintype Rand] [Nonempty Rand] [SampleableType W] [SampleableType Ct] [Fintype RK]
  [Nonempty RK] [DecidableEq Msg]

omit [Fintype Rand] [Nonempty Rand] in
/-- The initialisation of the deployed Triple Ratchet is its keyed initialisation at a uniform
root key, for a CKA initialisation that does not touch the heap. -/
theorem tripleRatchetDeployed_init_eq (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa))
    (D₀ : AEADDef W Ct ((PHdr × W) × ACDHdr Msg)) (F : W → S → W)
    (dec : W → W × ACDHdr Msg) (enc : ACDHdr Msg → W → W) (maxSkip maxStored : ℕ)
    (P : SidecarDef PSt PHdr S) (E : SidecarPack PHdr S W) (hC : SPComp.IsPure C.init) :
    (tripleRatchetDeployed C R G D₀ F dec enc maxSkip maxStored P E).init =
      SPComp.bind (SPComp.sample RK) (tripleRatchetDeployedIni (Sa := Sa) (W := W) C P) := by
  simp only [tripleRatchetDeployed, smidSidecar, acdIDSM, acdIDHdrSM, acdIDHdrBase,
    aeadEncComapAD, acdSMAD, SPComp.bind_assoc, SPComp.pure_bind]
  refine (SPComp.isPure_bind_comm_left _ _ _ hC).trans (congrArg _ (funext fun rk => ?_))
  simp only [tripleRatchetDeployedIni, acdIni, ACDIDSt.embed, SPComp.bind_assoc,
    SPComp.pure_bind]

variable {Sf Wg PKp SKp SSp Cp V : Type} [Field Sf] [Fintype Sf] [SampleableType Wg]
  [Inhabited RK] [DecidableEq SSp]

/-- **PQXDH followed by the deployed Triple Ratchet realizes secure messaging with corruption**
(genuine UC): `pqxdh_realizes_FSM` at the in-order scheme of `tripleRatchetDeployed` keyed
through `tripleRatchetDeployedIni`, for a CKA whose initialisation neither touches the heap nor
fails.

*Ideal functionality.* `F_SM` over the in-order scheme of `tripleRatchetDeployed` keyed through
`tripleRatchetDeployedIni C P`.

*Real world.* The real PQXDH protocol `pqxdhReal KP Gd` followed by the ratchet layer over the
deployed Triple Ratchet, with the PQXDH session key as the first root key.

*Simulator.* `chanSim (simProt KP Gd) pqFwd`, the PQXDH channel simulator.

*Bound.* `pqxdhFsmBound` at the deployed Triple Ratchet: the gap Diffie–Hellman bound of the
PQXDH square, and per key of the run the corruption advantages of the in-order scheme of
`tripleRatchetDeployed` at the reductions `smHopRed i j` and the probability that the key is
read twice. The injective packing `SidecarPack` into a finite word type forces a single salt
and a single sidecar header, so the statement applies only to runs with a constant salt. -/
theorem pqxdh_tripleRatchetDeployed_realizes_FSM (KP : Scheme PKp SKp SSp Cp)
    (Gd : DHGroup Sf Wg) (N : Finset PartyId) (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (hC : PureNF C.init) (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa))
    (D₀ : AEADDef W Ct ((PHdr × W) × ACDHdr Msg)) (F : W → S → W)
    (dec : W → W × ACDHdr Msg) (enc : ACDHdr Msg → W → W) (maxSkip maxStored : ℕ)
    (P : SidecarDef PSt PHdr S) (E : SidecarPack PHdr S W)
    (Sch : (Msg × ℕ) → OracleAdv (SMQuery W)
      (SMSchemeAns (Msg × ℕ) Ct (ACDIDLeak Sc RK Sa Msg W × PSt)) V)
    (t n ΔFS ΔPCS : ℕ) :
    RealizesSim ((pqxdhReal (K := RK) KP Gd).seq
        (smCorruptLayer
          (tripleRatchetDeployed C R G D₀ F dec enc maxSkip maxStored P E).toSMScheme
          (tripleRatchetDeployedIni (Sa := Sa) (W := W) C P) Sch t n ΔFS ΔPCS))
      (F_SM (tripleRatchetDeployed C R G D₀ F dec enc maxSkip maxStored P E).toSMScheme
        (tripleRatchetDeployedIni (Sa := Sa) (W := W) C P) Sch t n ΔFS ΔPCS)
      (chanSim (simProt KP Gd) pqFwd)
      (pqxdhFsmBound KP Gd N
        (tripleRatchetDeployed C R G D₀ F dec enc maxSkip maxStored P E).toSMScheme
        (tripleRatchetDeployedIni (Sa := Sa) (W := W) C P)
        (tripleRatchetDeployedIni_pureNF hC P) Sch t n ΔFS ΔPCS) :=
  pqxdh_realizes_FSM KP Gd N _ _
    (tripleRatchetDeployed_init_eq C R G D₀ F dec enc maxSkip maxStored P E hC.1)
    (tripleRatchetDeployedIni_pureNF hC P) Sch t n ΔFS ΔPCS

end CatCrypt.Crypto.Messaging
