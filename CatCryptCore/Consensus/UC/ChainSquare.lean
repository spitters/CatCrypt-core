/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCTransparentSquare
public import CatCryptCore.Consensus.UC.ChainEnvROM

/-!
# PoS-NSB and FFG over PoS-NSB behind opaque simulators

The realizations `chain_realizesE_rom` and `stack_realizesE_rom` place the simulators
`chainSimE` and `stackSimE` inside the transparent ideal world `ideal F S`, in which the
simulator receives every input of the environment. This file restates both as realizations
behind bundled opaque simulators (`RealizesSim`) of the port systems of the functionalities,
with the same bounds, through `realizesSim_ports_of_realizes`.

* Ideal functionality: the port system of `F_Tree^P` (`(chainFE …).ports`), respectively of
  `F_FinTree^P'` (`(stackFE …).ports`). Its honest port takes the honest transactions
  `TxIn Tx np` (`submit`) and answers the current output (`read`); its adversary port leaks the
  pending honest transaction (`peek`) and takes proposals of the next entry of the trace, which
  it accepts while the guard of the functionality holds and otherwise explodes.
* Real protocol: PoS-NSB driven by an environment with the reference clock and network
  (`chainRealE`), respectively the FFG gadget running with it (`stackRealE`), in the
  random-oracle model with the uniform tree types and an oracle adversary family.
* Simulator: `transSimulator` of `chainSimE`, respectively `stackSimE`, for the splitting of
  events into honest transactions and the rest (`EvSplit.sum`, `EvSplit.sum.prod`). It forwards
  an honest transaction to the honest port without keeping it, reads it back through `peek`,
  runs the protocol with the ideal clock and network on the completed event (drawing the seed,
  honest keys included, on its first activation), proposes the result, and answers with the
  honest `read`. It is opaque (`transSim_opaque`): its decisions do not depend on honest
  transactions.

## Main results

* `chain_realizesSimE_rom`: `chainRealE` realizes the port system of `F_Tree^P` behind the
  simulator of `chainSimE`, with the bound of `chain_realizesE_rom`.
* `stack_realizesSimE_rom`: `stackRealE` realizes the port system of `F_FinTree^P'` behind the
  simulator of `stackSimE`, with the bound of `stack_realizesE_rom`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCryptCore.Consensus.UC.ChainEnv

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open CatCrypt.Crypto.UCTransparent CatCrypt.NonUniform
open CatCryptCore.Consensus.UC.FTree CatCryptCore.Consensus.UC.Chain
open CatCrypt.Crypto.Signatures CatCrypt.Crypto.Assumptions
open PoSNSB Parameters BlockParameters Corruption Execution ClockNet
open scoped ENNReal

section ROMSquare

variable {Tx Hash : Type} [DecidableEq Tx] [DecidableEq Hash] {np : ℕ} [Corruption (Fin np)]
  {n Hz : ℕ} {PK SK Sig : Type}
  (Sch : PSigScheme (Block Tx Hash (Fin np)) PK SK Sig) [Sch.Deterministic]
  (IP : List (Fin np)) (h0 : Fin np) (GB : Block Tx Hash (Fin np))
  (U : (L : Fin n → Option (Fin np)) → Fin np →
    @UTreeType Tx Hash (Fin np) (leaderParams IP h0 L) GB)
  (UT : (L : Fin n → Option (Fin np)) → @UTreeType Tx Hash (Fin np) (leaderParams IP h0 L) GB)
  {X S : Type} (OF : OAdvFamily X S Tx Hash np n Hz PK Sig) (x₀ : X) (dt : Slot → Fin np → Tx)
  [Fintype Tx] [Fintype Hash] [Nonempty Hash]

/-- **PoS-NSB realizes the port system of `F_Tree` behind an opaque simulator, in the
random-oracle model.** Under the hypotheses of `chain_realizesE_rom`, the protocol driven by an
environment with the reference clock and network (`chainRealE`) realizes the port system of
`F_Tree^P` (`chainFE`), whose honest port takes honest transactions and whose adversary port
takes the proposals of the simulator, behind the opaque simulator `transSimulator` of
`chainSimE`, with the bound of `chain_realizesE_rom`: `slotBound (kindLaw μ) n d w ε +
qT (qT - 1) / 2 / |Hash| + ∑ᵢ eufcmaAdvantage Sch.toSigScheme (toEUFAdversary (forgerE … Z i))`
with `qT = 1 + Z.input.rounds + K (|IP| (qc + m + 1))`. -/
theorem chain_realizesSimE_rom {qc m : ℕ} (hOF : OF.Bounded qc m)
    (hP : ProtocolHyp (Protocol.ofUniform (Hz := Hz) IP h0 GB U dt))
    (hTree : (TreeFamily.ofUniform (P := Protocol.ofUniform (Hz := Hz) IP h0 GB U dt) UT).Longest)
    (μ : PMF (Option (Fin np))) (W K d w : ℕ) (ε : ℝ) (Δ : ℕ)
    (hwd : w ≤ d) (hWn : W + d ≤ n) (hn : K + 2 ≤ n) (hHz : K + 1 ≤ Hz)
    (hε : 0 ≤ ε) (hγ : 2 * pA (kindLaw μ) ≤ pH (kindLaw μ))
    (hw : (w : ℝ) ≤ d * (pH (kindLaw μ) - pA (kindLaw μ)))
    (h3 : (3 : ℝ) ≤ d * (pH (kindLaw μ) - 2 * pA (kindLaw μ)))
    (hGB : GB.sl = 0) (hw4 : K + 1 < d + 2 ∨ 4 ≤ w) :
    RealizesSim (chainRealE (Protocol.ofUniform (Hz := Hz) IP h0 GB U dt) Sch OF.toAdvFamily
        x₀ dt (TreeFamily.ofUniform UT) (HashScheme.randomFun (BlockDom Tx Hash np Hz) Hash)
        (HashScheme.Codec.id _) K μ W Δ)
      ((chainFE (Protocol.ofUniform (Hz := Hz) IP h0 GB U dt) Δ (kindLaw μ) d w ε).ports
        (P := TxIn Tx np))
      (transSimulator (chainSimE (Protocol.ofUniform (Hz := Hz) IP h0 GB U dt) Sch
          OF.toAdvFamily x₀ dt (TreeFamily.ofUniform UT)
          (HashScheme.randomFun (BlockDom Tx Hash np Hz) Hash) (HashScheme.Codec.id _) K μ W Δ)
        EvSplit.sum Lossless.noFail (Stack.exCE Tx Hash np))
      (fun _ Z => slotBound (kindLaw μ) n d w ε +
        (((1 + Z.input.rounds + K * (IP.length * (qc + m + 1))) *
          (1 + Z.input.rounds + K * (IP.length * (qc + m + 1)) - 1) / 2 : ℕ) : ℝ≥0∞) /
          Fintype.card Hash +
        ∑ i : Fin np, eufcmaAdvantage Sch.toSigScheme
          (toEUFAdversary (forgerE (Protocol.ofUniform (Hz := Hz) IP h0 GB U dt) Sch
            OF.toAdvFamily x₀ dt (TreeFamily.ofUniform UT)
            (HashScheme.randomFun (BlockDom Tx Hash np Hz) Hash) (HashScheme.Codec.id _) μ W K Δ
            Z i))) :=
  realizesSim_ports_of_realizes _ _ EvSplit.sum Lossless.noFail
    (chain_realizesE_rom Sch IP h0 GB U UT OF x₀ dt hOF hP hTree μ W K d w ε Δ hwd hWn hn hHz
      hε hγ hw h3 hGB hw4).realizes

open CatCryptCore.Consensus.UC.Stack CatCryptCore.Consensus.Finality FFG
  CatCryptCore.Consensus.UC.FFGGadget in
/-- **FFG over PoS-NSB realizes the port system of `F_FinTree` behind an opaque simulator, in
the random-oracle model.** Under the hypotheses of `stack_realizesE_rom`, the FFG gadget running
with the protocol driven by an environment with the reference clock and network (`stackRealE`)
realizes the port system of `F_FinTree^P'` (`stackFE`), whose honest port takes the honest
transactions of the events and whose adversary port takes the proposals of the simulator,
behind the opaque simulator `transSimulator` of `stackSimE`, with the bound of
`stack_realizesE_rom` at the environment `Z' = (stackHybridE …).reduceEnv Z` of the PoS-NSB
layer. -/
theorem stack_realizesSimE_rom {qc m : ℕ} (hOF : OF.Bounded qc m)
    (hP : ProtocolHyp (Protocol.ofUniform (Hz := Hz) IP h0 GB U dt))
    (hTree : (TreeFamily.ofUniform (P := Protocol.ofUniform (Hz := Hz) IP h0 GB U dt) UT).Longest)
    (μ : PMF (Option (Fin np))) (W K d w : ℕ) (ε : ℝ) (Δ : ℕ)
    (c : Cfg (Option (Fin np)) (Block Tx Hash (Fin np)))
    (exF : TreeView (Option (Fin np)) (Block Tx Hash (Fin np)))
    (hwd : w ≤ d) (hWn : W + d ≤ n) (hn : K + 2 ≤ n) (hHz : K + 1 ≤ Hz)
    (hε : 0 ≤ ε) (hγ : 2 * pA (kindLaw μ) ≤ pH (kindLaw μ))
    (hw : (w : ℝ) ≤ d * (pH (kindLaw μ) - pA (kindLaw μ)))
    (h3 : (3 : ℝ) ≤ d * (pH (kindLaw μ) - 2 * pA (kindLaw μ)))
    (hGB : GB.sl = 0) (hw4 : K + 1 < d + 2 ∨ 4 ≤ w)
    (hT : c.T = slotTree (Protocol.ofUniform (Hz := Hz) IP h0 GB U dt))
    (hsl : c.slot = Block.sl) (hH : ∀ o, o ∈ c.H ↔ honestP o)
    (hcut : c.cut = slotCut Block.sl d) (hΔ : 1 ≤ c.Δ) (hE : 1 ≤ c.E) (hv₀ : c.v₀ ∈ c.H)
    (hstart : c.start = 2 * c.E + (d + 2) + d)
    (hA : 3 * stake c.w (Finset.univ \ c.H) < totalStake c.w) :
    RealizesSim (stackRealE (Protocol.ofUniform (Hz := Hz) IP h0 GB U dt) Sch OF.toAdvFamily
        x₀ dt (TreeFamily.ofUniform UT) (HashScheme.randomFun (BlockDom Tx Hash np Hz) Hash)
        (HashScheme.Codec.id _) c K μ W Δ exF)
      ((stackFE (Protocol.ofUniform (Hz := Hz) IP h0 GB U dt) Sch OF.toAdvFamily x₀ dt
          (TreeFamily.ofUniform UT) (HashScheme.randomFun (BlockDom Tx Hash np Hz) Hash)
          (HashScheme.Codec.id _) μ W K d w ε Δ c exF).ports (P := TxIn Tx np))
      (transSimulator (stackSimE (Protocol.ofUniform (Hz := Hz) IP h0 GB U dt) Sch
          OF.toAdvFamily x₀ dt (TreeFamily.ofUniform UT)
          (HashScheme.randomFun (BlockDom Tx Hash np Hz) Hash) (HashScheme.Codec.id _) μ W K d w
          ε Δ c exF)
        EvSplit.sum.prod Lossless.noFail
        (stackFE (Protocol.ofUniform (Hz := Hz) IP h0 GB U dt) Sch OF.toAdvFamily x₀ dt
          (TreeFamily.ofUniform UT) (HashScheme.randomFun (BlockDom Tx Hash np Hz) Hash)
          (HashScheme.Codec.id _) μ W K d w ε Δ c exF).exploded)
      (fun _ Z =>
        let Z' := (stackHybridE (Protocol.ofUniform (Hz := Hz) IP h0 GB U dt) Sch OF.toAdvFamily
          x₀ dt (TreeFamily.ofUniform UT) (HashScheme.randomFun (BlockDom Tx Hash np Hz) Hash)
          (HashScheme.Codec.id _) c K μ W Δ exF).reduceEnv Z
        slotBound (kindLaw μ) n d w ε +
          (((1 + Z'.input.rounds + K * (IP.length * (qc + m + 1))) *
            (1 + Z'.input.rounds + K * (IP.length * (qc + m + 1)) - 1) / 2 : ℕ) : ℝ≥0∞) /
            Fintype.card Hash +
          ∑ i : Fin np, eufcmaAdvantage Sch.toSigScheme
            (toEUFAdversary (forgerE (Protocol.ofUniform (Hz := Hz) IP h0 GB U dt) Sch
              OF.toAdvFamily x₀ dt (TreeFamily.ofUniform UT)
              (HashScheme.randomFun (BlockDom Tx Hash np Hz) Hash) (HashScheme.Codec.id _) μ W K
              Δ Z' i))) :=
  realizesSim_ports_of_realizes _ _ EvSplit.sum.prod Lossless.noFail
    (stack_realizesE_rom Sch IP h0 GB U UT OF x₀ dt hOF hP hTree μ W K d w ε Δ c exF hwd hWn hn
      hHz hε hγ hw h3 hGB hw4 hT hsl hH hcut hΔ hE hv₀ hstart hA).realizes

end ROMSquare

end CatCryptCore.Consensus.UC.ChainEnv
