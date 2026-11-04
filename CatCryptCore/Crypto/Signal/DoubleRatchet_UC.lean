/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Signal.DoubleRatchet_CKA
public import CatCryptCore.Crypto.UCConcrete

/-!
# UC Security of the Signal Double Ratchet

The Signal double ratchet is the secure-messaging game of the core double ratchet
(`CatCrypt.Crypto.Messaging.sm_real`/`sm_ideal`) with the Diffie–Hellman CKA `dhCKA G`, the HKDF
root step `hkdfRoot kdf` and the Signal symmetric ratchet of an `FSAEADConfig`
(`DoubleRatchet_CKA`). The adversary sees the public value of the CKA initialisation, the CKA
messages of all epochs and the ciphertexts. `dr_uc_secure` lifts the bound
`signal_dr_confidentiality` (DDH advantages, PRG advantages of the root step and FS-AEAD
advantages of explicit reductions, summed over the epochs) to `UCEmulatesCSim` through
`UCFromGameC`, from the `PureGame` instances of the two games and the `GameAdvBoundC` instance
`instSignalDRGameAdvBoundC`. `signal_dr_distC` is the concrete distance of the games wrapped by
`UCProtocol.ofGame`, the form in which compositions consume them.

## Main definitions

* `signalDRReal`, `signalDRIdeal` — the game families of the Signal double ratchet

## Main results

* `dr_uc_secure` — `UCEmulatesCSim` of the Signal double ratchet games `sm_real`/`sm_ideal`
  at `signalDRBound` of `envReduction A Z`
* `signal_dr_distC` — concrete distance of the wrapped games at `signalDRBound` of
  `envReduction SPComp.pure Z`

## References

* J. Alwen, S. Coretti, Y. Dodis, *The Double Ratchet: Security Notions, Proofs, and
  Modularization for the Signal Protocol*, EUROCRYPT 2019
* Canetti et al., "Universally Composable Double Ratchet", ePrint 2022/376
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Signal.DoubleRatchet_UC

open CatCrypt.Core CatCrypt.Crypto CatCrypt.Prob CatCrypt.Crypto.UCConcrete
open CatCrypt.Crypto.Messaging CatCrypt.Crypto.Signal.DoubleRatchet_CKA
  CatCryptCore.Examples.CyclicGroupDDH CatCrypt.Crypto.UCDSL
open scoped ENNReal

variable (G : Type) [CyclicGroup G] {RK W : Type} [Fintype RK] [Nonempty RK] [CryptoWord W]

/-- The real secure-messaging game of the Signal double ratchet, as a family over `Unit`. -/
noncomputable abbrev signalDRReal (kdf : RK → G → RK × W) (cfg : FSAEAD.FSAEADConfig W)
    (msgs : List (List W)) : Unit → SPComp (SMView G W) :=
  fun _ => sm_real (Messaging.dhCKA G) (hkdfRoot kdf) (FSAEAD.toPRG cfg) (FSAEAD.toAEAD cfg)
    (signalMsgs msgs)

/-- The ideal secure-messaging game of the Signal double ratchet, as a family over `Unit`. -/
noncomputable abbrev signalDRIdeal (msgs : List (List W)) : Unit → SPComp (SMView G W) :=
  fun _ => sm_ideal (Ct := W) (Messaging.dhCKA G) (signalMsgs msgs)

/-- The real secure-messaging game of the Signal double ratchet does not touch the heap. -/
instance (kdf : RK → G → RK × W) (cfg : FSAEAD.FSAEADConfig W) (msgs : List (List W)) :
    PureGame (signalDRReal G kdf cfg msgs) :=
  ⟨fun _ => sm_real_isPure _ (dhCKA_init_isPure G) (dhCKA_send_isPure G) _ _ _ _⟩

/-- The ideal secure-messaging game of the Signal double ratchet does not touch the heap. -/
instance (msgs : List (List W)) : PureGame (signalDRIdeal (W := W) G msgs) :=
  ⟨fun _ => sm_ideal_isPure _ (dhCKA_init_isPure G) (dhCKA_send_isPure G) _⟩

/-- The per-adversary bound of the Signal double ratchet, `signalDRBound`, from
`signal_dr_confidentiality`. -/
instance instSignalDRGameAdvBoundC (kdf : RK → G → RK × W) (cfg : FSAEAD.FSAEADConfig W)
    (msgs : List (List W)) :
    GameAdvBoundC (signalDRReal G kdf cfg msgs) (signalDRIdeal G msgs)
      (fun _ A => signalDRBound G kdf cfg msgs A) :=
  ⟨fun _ A => signal_dr_confidentiality G kdf cfg msgs A⟩

/-- **UC security of the Signal double ratchet.** The secure-messaging game of the Signal
double ratchet (Diffie–Hellman CKA over `G`, HKDF root step `hkdfRoot kdf`, symmetric ratchet
`cfg`, plaintexts `msgs`), in which the adversary sees the CKA public values and messages and
the ciphertexts of all epochs, UC-emulates the game with uniform ciphertexts; the bound for the
adversary `A` and the environment `Z` is `signalDRBound` at `envReduction A Z`. -/
theorem dr_uc_secure (kdf : RK → G → RK × W) (cfg : FSAEAD.FSAEADConfig W)
    (msgs : List (List W)) (V : Type) :
    UCEmulatesCSim (UCSpec.ofGame Unit (SMView G W) V)
      (UCProtocol.ofGame (signalDRReal G kdf cfg msgs))
      (UCProtocol.ofGame (signalDRIdeal G msgs)) id
      (gameUCBound fun _ A => signalDRBound G kdf cfg msgs A) :=
  (inferInstance : UCFromGameC (signalDRReal G kdf cfg msgs) (signalDRIdeal G msgs) V
    (fun _ A => signalDRBound G kdf cfg msgs A)).uc

/-- **Concrete distance of the wrapped Signal double ratchet games**, on inputs of any type
`α`: every environment `Z` is charged `signalDRBound` at `envReduction SPComp.pure Z`. -/
theorem signal_dr_distC {α : Type} (kdf : RK → G → RK × W) (cfg : FSAEAD.FSAEADConfig W)
    (msgs : List (List W)) :
    DistC (fun _ : α => UCProtocol.ofGame (signalDRReal G kdf cfg msgs) ())
      (fun _ => UCProtocol.ofGame (signalDRIdeal G msgs) ())
      (fun Z => signalDRBound G kdf cfg msgs (envReduction SPComp.pure Z)) :=
  DistC_ofGame (bound := fun _ A => signalDRBound G kdf cfg msgs A) ()

end CatCrypt.Crypto.Signal.DoubleRatchet_UC
