/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Party.UnwindingTransfer
public import CatCryptCore.Crypto.Party.Timed

/-!
# X3DH in the party language

**Ideal functionality.** `F_AKE (SPComp.sample K) true` of `CatCryptCore.Crypto.AKE.FAKESys`, the
authenticated key exchange with adversarial key delivery, the unlinked delivery
`newKeyUnlinked`, corruption of parties and uniform keys in `K`, and its program form
`FAKEProg.sys (SPComp.sample K) true` (`Party.Protocols.FAKE`).

**Real protocol.** `X3DHSquare.x3dhReal G`, X3DH (Marlinspike and Perrin, 2016) over the group
`G : DHGroup S W` for every session, with static corruption and the key derivation a lazily
sampled random function into `K` (`CatCryptCore.Crypto.AKE.X3DHSquare`).

**Simulator.** The X3DH simulator written as a program of the party language,
`X3DHProg.simBody G`, one iteration per activation, as the multi-call hybrid
`X3DHProg.simLoop G` over `F_AKE` (`CatCryptCore.Crypto.Party.Call`): it keeps a copy of the
real state, draws the secrets itself, forwards honest events to `F_AKE` and delivers keys by
`newKey` or `newKeyUnlinked`. Its structure is derived from the program by the generic theorems
of the party language: the unwinding relation is information flow `ProgE.ViewRel` of the loop
(`Prog.loopSys_unwinding`), transferred to the multi-call hybrid (`MultiHybrid.unwinding_ofSys`),
so the simulator is opaque (`X3DH.simLoop_opaque`) and bundles as `X3DH.x3dhSimP G`; its time
certificate is the graded bound of the costed program `X3DHProg.simBodyT G`
(`X3DH.simLoop_time`).

**Results.** `X3DH.x3dh_realizesSim_prog`: `x3dhReal G` realizes `F_AKE` behind the program
simulator `x3dhSimP G` with the oracle-game bound of `X3DHSquare.x3dh_realizesSim_oracleGame`,
the advantage of `OProt.oracle.reduction Z` between `realGame G` and `simGame G`.
`X3DH.x3dh_realizesSim_progFAKE`: the same bound against the program form of `F_AKE`.

Search words: party language, X3DH, UC, simulator, F_AKE, opacity, unwinding, time certificate.

## Main definitions

* `X3DH.x3dhSimP`: the X3DH simulator program as a bundled opaque simulator.

## Main results

* `X3DH.simLoop_unwinding`, `X3DH.simLoop_opaque`: the unwinding condition and the opacity of the
  simulator program.
* `X3DH.simLoop_time`: the time of `q` iterations of the costed simulator program.
* `X3DH.x3dh_realizesSim_prog`: X3DH realizes `F_AKE` behind the program simulator.
* `X3DH.x3dh_realizesSim_progFAKE`: X3DH realizes the program form of `F_AKE` behind the program
  simulator.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Party.Protocols.X3DH

open CatCrypt.Core CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCConcrete
open CatCrypt.Crypto.AKE.X3DHSquare CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.PAKE.DHExtract CatCrypt.Crypto.Party.X3DHProg Prog

variable {S W K : Type} [Field S] [Fintype S] [DecidableEq W] [Fintype K]
  [Nonempty K] [Inhabited K] (G : DHGroup S W)

/-- **The unwinding condition of the X3DH simulator program**: information flow of the loop of
`simBody` for the view of the sum interface is an unwinding relation of `simLoop`. -/
theorem simLoop_unwinding :
    (simLoop (K := K) G).Unwinding outerView subView
      (ProgE.ViewRel (PubView.callView outerView subView) Eq) :=
  MultiHybrid.unwinding_ofSys
    (loopSys_unwinding (simBody G) _ rfl fun s _ hs => hs ▸ simBody_viewRel G s)
    (stepRel_refl (S := S) (W := W) (K := K) (.inr default)) 0

/-- **Opacity of the X3DH simulator program**: it reads no key of `F_AKE`. -/
theorem simLoop_opaque : (simLoop (K := K) G).Opaque outerView subView :=
  ⟨_, simLoop_unwinding G⟩

/-- **The X3DH simulator program** as a bundled opaque simulator. -/
noncomputable def x3dhSimP :
    Simulator (OEv W) (OOut S W K) (FEv K) (FOut K) outerView subView :=
  Simulator.ofMultiHybrid (simLoop G) (simLoop_opaque G)

/-- **Time certificate of the X3DH simulator program**: the first `q` iterations of its costed
form, which erases to `simBody` (`simBodyT_erase`), cost at most `7 q + q (q - 1) / 2`, and the
key-derivation table then holds at most `q` entries. -/
theorem simLoop_time (q : ℕ) :
    ProgE.Bound Costed.weight
      (ProgE.iterate (simBodyT G) q ((rInit, fun _ => none, .fwd) : SimSt S W K))
      (q * 7 + 1 * (q * (q - 1) / 2)) (fun s => s.1.ro.length ≤ q) :=
  (simBodyT_loopBoundGraded G).iterate_time_le q

/-- **X3DH realizes `F_AKE` behind the program simulator.** For every environment `Z`, the
distance between the real X3DH protocol and the simulator program running with `F_AKE` is at most
the advantage of `OProt.oracle.reduction Z` between `realGame G` and `simGame G`. -/
theorem x3dh_realizesSim_prog :
    RealizesSim (x3dhReal (K := K) G) (F_AKE (SPComp.sample K) true) (x3dhSimP G)
      (fun _ Z => KeyedGame.advantage (realGame G) (simGame G) (OProt.oracle.reduction Z)) :=
  fun ζ Z => le_of_le_of_eq (((x3dh_realizesSim_oracleGame G).trans
    (Sys.StepEq.realizes (simProt_stepEq_simLoop G (F_AKE (SPComp.sample K) true))).1) ζ Z)
    (add_zero _)

end CatCrypt.Crypto.Party.Protocols.X3DH
