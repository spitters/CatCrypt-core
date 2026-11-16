/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.FSAEADCorruptSM
public import CatCryptCore.Crypto.Signal.EndToEnd

/-!
# The Signal stack over the extracted ratchet from PRG and AEAD security

The hop reduction `smHopRed i j Z` of the Signal stack runs the schedule `Sch` against the
hybrid handler `smHybImpl`, which answers each query by at most one query, so it asks at most
the queries of the schedule, whatever the environment `Z` (`smHopRed_play_isQueryBound`). For a
schedule with at most `q` queries on every public value, `fsaead_corrupt_advantage_le` bounds
each FS-AEAD term of `signalExtractedBound` by PRG advantages of the chain PRG `F` and one AEAD
advantage of `D` at explicit reductions (`signalExtractedBound_le_prim`).

## Main results

* `smHopRed_play_isQueryBound` — the hop reduction asks at most the queries of the schedule
* `signalExtractedBoundPrim` — the bound of the Signal stack over the extracted ratchet with the
  FS-AEAD terms replaced by PRG and AEAD terms
* `signalExtractedBound_le_prim` — `signalExtractedBound` is at most `signalExtractedBoundPrim`
* `signal_stack_realizes_FSM_extracted_prim` — the Signal stack over the extracted ratchet
  realizes `F_SM` with the bound `signalExtractedBoundPrim`
-/

set_option autoImplicit false

@[expose] public section

namespace CatCrypt.Crypto.Signal.EndToEnd

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Messaging
open CatCrypt.Crypto.Assumptions CatCryptCore.Examples.CyclicGroupDDH
open CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.PAKE.DHExtract (DHGroup)
open CatCrypt.Crypto.PAKE.CPaceSquare (PureNF pureNF_pure pureNF_sample)
open CatCrypt.Crypto.AKE.X3DHSquare CatCrypt.Crypto.AKE.X3DHSquareGDH
open CatCrypt.Crypto.AKE.X3DH.SquareCorrespondence CatCrypt.Crypto.AKE.X3DH.ExtractedGame
open CatCrypt.Crypto.Messaging.SignalStack CatCrypt.Crypto.Messaging.SignalStackUC
open CatCrypt.Crypto.Messaging.SignalStackSM
open CatCrypt.Crypto.Signal.DoubleRatchet.ExtractedCorrespondence
open CatCrypt.Crypto.Signal.DoubleRatchet.ExtractedScheme
open CatCrypt.Crypto.Signal.SessionExtracted
open scoped ENNReal

/-! ## The query bound of the hop reduction -/

section QueryBound

variable {K Sst Pub Rand Wd Ct Leak V : Type} [Fintype Rand] [Nonempty Rand] [Fintype K]
  [Nonempty K] [Inhabited K]

/-- **The query bound of the hop reduction.** If the schedule `Sch` asks at most `q` queries on
every public value, every interaction of `smHopRed M ini Sch t n ΔFS ΔPCS i j Z` asks at most
`q` queries, for every environment `Z`. -/
theorem smHopRed_play_isQueryBound (M : SMScheme Sst Pub Rand Wd Ct Leak)
    (ini : K → SPComp (Pub × Sst × Sst))
    (Sch : Pub → OracleAdv (SMQuery Wd) (SMSchemeAns Pub Ct Leak) V) (t n ΔFS ΔPCS i j : ℕ)
    {ζ : Type} (Z : Env (Strat ζ (HEv ⊕ AEv K) (HOut V ⊕ AOut)) ζ) {q : ℕ}
    (hSch : ∀ T, (Sch T).IsQueryBound q) (t' : ℕ) (T : Pub) :
    ((smHopRed M ini Sch t n ΔFS ΔPCS i j Z).play t' T).IsQueryBound q := by
  have himpl : ∀ s d, (smHybImpl M t' n j s d).IsQueryBound 1 := by
    intro s d
    cases d <;> query_bound [smHybImpl]
  have hplay : ∀ (Dst : V → SPComp Bool), (smHopPlay Sch Dst T).IsQueryBound q := by
    intro Dst
    unfold smHopPlay
    simpa using OracleAdv.isQueryBound_bind (n := 0)
      (f := fun v => OracleAdv.rand (outBool Dst v) OracleAdv.ret) (hSch T) (fun _ _ => trivial)
  simp only [smHopRed, SMSchemeAdv.hyb, smHopAdv]
  simpa using OracleAdv.isQueryBound_bind (n := 0) (f := fun x => OracleAdv.ret x.1)
    (OracleAdv.isQueryBound_simulate _ (fun _ => 1) himpl (hplay _).isQueryBoundBy_one _)
    (fun _ => trivial)

end QueryBound

/-! ## The Signal stack over the extracted ratchet -/

section Stack

variable [Doubleratchet.DoubleratchetDeps]

attribute [local instance high] CyclicGroup.finG

variable {S RK Sa Wd Ct Sk G V : Type} [Field S] [Fintype S] [Nonempty S] [SampleableType G]
  [CG : CyclicGroup G] [Fintype RK] [Nonempty RK] [Inhabited RK] [DecidableEq RK]
  [Fintype Sa] [Nonempty Sa] [SampleableType Wd] [Fintype Sk] [Nonempty Sk] [SampleableType Ct]

/-- **The bound of the Signal stack over the extracted ratchet from PRG and AEAD security** at
an environment `Z`: the bound `signalExtractedBound` with the FS-AEAD term of each key `i` and
challenge `j` replaced by the PRG advantages of `F` at `fsCorrPRGRed F D b k` for the positions
`k < q` and both challenge bits `b`, and the AEAD advantage of `D` at `fsCorrAEADRed F D`, both
at the FS-AEAD reduction `smcFSRed` of the encoded reduction `smHopRed i j Z'`. -/
noncomputable def signalExtractedBoundPrim (GX : DHGroup S G) (P : Finset PartyId)
    (R : PRGDef (RK × G) (RK × Sa)) (F : PRGDef Sa (Wd × Sa)) (D : AEADDef Wd Ct) (ptLen : Int)
    (encR : RK → Array Int) (encG : G → Array Int) (encSk : Sk → Array Int) (decE : Sk → CG.Exp)
    (encS : Sa → Array Int) (encW : Wd → Array Int) (encC : Ct → Array Int)
    (Sch : Array Int →
      OracleAdv (SMQuery Wd) (SMSchemeAns (Array Int) (Array Int) DrLeak) V)
    (t n ΔFS ΔPCS q : ℕ) (ζ : Type) (Z : Env (Strat ζ (OEv G) (HOut V ⊕ ROut S G RK)) ζ) :
    ℝ≥0∞ :=
  gdhBound GX P ((OProt.oracle (Q := OEv G) (A := OOut S G RK)).reduction
      ((Hybrid.seqCtxR (E := OEv G)
        (smCorruptLayer (drExtractedSM RK ptLen encR encG encSk decE encW encC)
          (drExtractedIni encR encG encSk decE) Sch t n ΔFS ΔPCS)
        (keyLayer_noFail fun k => (smSessView_pureNF
          (drExtractedIni_pureNF encR encG encSk decE) Sch t n ΔFS ΔPCS _ k).2)).reduceEnv Z)) +
    ∑ i ∈ Finset.range ((simSC (V := V) GX).reduceEnv (.inr .idle) Z).input.rounds,
      ((∑ j ∈ Finset.range n,
          (∑ b : Bool, CKA_Corrupt_Advantage (dhCKAOf G decE) ΔFS ΔPCS
              (smcCKARed R F D b ((smHopRed (drExtractedSM RK ptLen encR encG encSk decE encW
                encC) (drExtractedIni encR encG encSk decE) Sch t n ΔFS ΔPCS i j
                ((simSC GX).reduceEnv (.inr .idle) Z)).comap encG encC
                (drEncLeak encR encG encSk decE encS)).toSM) +
            ∑ b : Bool, PRFPRNG_Advantage R (smcRootRed (dhCKAOf G decE) R F D ΔFS ΔPCS b
              (dhInitPOf G decE) ((smHopRed (drExtractedSM RK ptLen encR encG encSk decE encW
                encC) (drExtractedIni encR encG encSk decE) Sch t n ΔFS ΔPCS i j
                ((simSC GX).reduceEnv (.inr .idle) Z)).comap encG encC
                (drEncLeak encR encG encSk decE encS)).toSM) +
            (∑ k ∈ Finset.range q, PRG_Advantage F (fsCorrPRGRed F D false k
                (smcFSRed (dhCKAOf G decE) R F D ΔFS ΔPCS (dhInitPOf G decE)
                  ((smHopRed (drExtractedSM RK ptLen encR encG encSk decE encW encC)
                    (drExtractedIni encR encG encSk decE) Sch t n ΔFS ΔPCS i j
                    ((simSC GX).reduceEnv (.inr .idle) Z)).comap encG encC
                    (drEncLeak encR encG encSk decE encS)).toSM)) +
              ∑ k ∈ Finset.range q, PRG_Advantage F (fsCorrPRGRed F D true k
                (smcFSRed (dhCKAOf G decE) R F D ΔFS ΔPCS (dhInitPOf G decE)
                  ((smHopRed (drExtractedSM RK ptLen encR encG encSk decE encW encC)
                    (drExtractedIni encR encG encSk decE) Sch t n ΔFS ΔPCS i j
                    ((simSC GX).reduceEnv (.inr .idle) Z)).comap encG encC
                    (drEncLeak encR encG encSk decE encS)).toSM)) +
              AEAD_CCA_Advantage D (fsCorrAEADRed F D
                (smcFSRed (dhCKAOf G decE) R F D ΔFS ΔPCS (dhInitPOf G decE)
                  ((smHopRed (drExtractedSM RK ptLen encR encG encSk decE encW encC)
                    (drExtractedIni encR encG encSk decE) Sch t n ΔFS ΔPCS i j
                    ((simSC GX).reduceEnv (.inr .idle) Z)).comap encG encC
                    (drEncLeak encR encG encSk decE encS)).toSM))))) +
        prBad (hyb (smRealView (drExtractedSM RK ptLen encR encG encSk decE encW encC)
            (drExtractedIni encR encG encSk decE) Sch t n ΔFS ΔPCS)
          (smIdealView (drExtractedSM RK ptLen encR encG encSk decE encW encC)
            (drExtractedIni encR encG encSk decE) Sch t n ΔFS ΔPCS) i)
          (reuse i) ((simSC GX).reduceEnv (.inr .idle) Z))

omit [Nonempty S] in
/-- **The FS-AEAD terms of the Signal stack from PRG and AEAD security.** For a schedule `Sch`
with at most `q` queries on every public value, `signalExtractedBound` is at most
`signalExtractedBoundPrim` at every environment. -/
theorem signalExtractedBound_le_prim (GX : DHGroup S G) (P : Finset PartyId)
    (R : PRGDef (RK × G) (RK × Sa)) (F : PRGDef Sa (Wd × Sa)) (D : AEADDef Wd Ct) (ptLen : Int)
    (encR : RK → Array Int) (encG : G → Array Int) (encSk : Sk → Array Int) (decE : Sk → CG.Exp)
    (encS : Sa → Array Int) (encW : Wd → Array Int) (encC : Ct → Array Int)
    (Sch : Array Int →
      OracleAdv (SMQuery Wd) (SMSchemeAns (Array Int) (Array Int) DrLeak) V)
    (t n ΔFS ΔPCS q : ℕ) (hSch : ∀ T, (Sch T).IsQueryBound q) (ζ : Type)
    (Z : Env (Strat ζ (OEv G) (HOut V ⊕ ROut S G RK)) ζ) :
    signalExtractedBound GX P R F D ptLen encR encG encSk decE encS encW encC Sch t n ΔFS ΔPCS
        ζ Z ≤
      signalExtractedBoundPrim GX P R F D ptLen encR encG encSk decE encS encW encC Sch t n ΔFS
        ΔPCS q ζ Z := by
  unfold signalExtractedBound signalExtractedBoundPrim
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro i _
  apply add_le_add_left
  apply Finset.sum_le_sum
  intro j _
  have hQ := smHopRed_play_isQueryBound (drExtractedSM RK ptLen encR encG encSk decE encW encC)
    (drExtractedIni encR encG encSk decE) Sch t n ΔFS ΔPCS i j
    ((simSC GX).reduceEnv (.inr .idle) Z) hSch
  have hQ' := SMSchemeAdv.comap_play_isQueryBound (encP := encG) (encC := encC)
    (encL := drEncLeak encR encG encSk decE encS) hQ
  have hB := smcFSRed_isQueryBoundBy (dhCKAOf G decE) R F D ΔFS ΔPCS (dhInitPOf G decE) _ q
    (SMSchemeAdv.toSM_play_isQueryBound hQ')
  have h := fsaead_corrupt_advantage_le F D q _ hB
  exact add_le_add_right h _

variable {R : PRGDef (RK × G) (RK × Sa)} {F : PRGDef Sa (Wd × Sa)} {D : AEADDef Wd Ct}
  {ptLen : Int} {encR : RK → Array Int} {encG : G → Array Int} {encSk : Sk → Array Int}
  {decE : Sk → CG.Exp} {encS : Sa → Array Int} {encW : Wd → Array Int} {encC : Ct → Array Int}

omit [Nonempty S] in
/-- **The Signal stack over the extracted double ratchet realizes secure messaging with
corruption, from PRG and AEAD security** (genuine UC).

*Ideal functionality, real world, simulator.* Those of `signal_stack_realizes_FSM_extracted`:
`F_SM (drExtractedSM …) (drExtractedIni …) Sch t n ΔFS ΔPCS`, X3DH over `GX` followed by the
ratchet layer over the extracted scheme, and `scSim GX`.

*Bound.* Under `DrHom`, with `2 ≤ ΔFS` and `1 ≤ ΔPCS`, for a schedule `Sch` with at most `q`
queries on every public value, `signalExtractedBoundPrim`: the gap Diffie–Hellman bound of X3DH
and, over the keys of the run and the challenges `j < n`, the CKA corruption and PRF-PRNG
advantages of `signalExtractedBound`, the PRG advantages of the chain PRG `F` at `q` hybrid
positions and the AEAD advantage of `D`, all at explicit reductions, and the probability that a
key is read twice. -/
theorem signal_stack_realizes_FSM_extracted_prim (GX : DHGroup S G) (P : Finset PartyId)
    (hD : DrHom G R F D ptLen encR encG encSk decE encS encW encC)
    {ΔFS ΔPCS : ℕ} (hFS : 2 ≤ ΔFS) (hPCS : 1 ≤ ΔPCS)
    (Sch : Array Int →
      OracleAdv (SMQuery Wd) (SMSchemeAns (Array Int) (Array Int) DrLeak) V) (t n q : ℕ)
    (hSch : ∀ T, (Sch T).IsQueryBound q) :
    RealizesSim ((x3dhReal (K := RK) GX).seq
        (smCorruptLayer (drExtractedSM RK ptLen encR encG encSk decE encW encC)
          (drExtractedIni encR encG encSk decE) Sch t n ΔFS ΔPCS))
      (F_SM (drExtractedSM RK ptLen encR encG encSk decE encW encC)
        (drExtractedIni encR encG encSk decE) Sch t n ΔFS ΔPCS) (scSim GX)
      (signalExtractedBoundPrim GX P R F D ptLen encR encG encSk decE encS encW encC Sch t n ΔFS
        ΔPCS q) := by
  intro ζ Z
  exact (signal_stack_realizes_FSM_extracted GX P hD hFS hPCS Sch t n ζ Z).trans
    (signalExtractedBound_le_prim GX P R F D ptLen encR encG encSk decE encS encW encC Sch t n
      ΔFS ΔPCS q hSch ζ Z)

end Stack

end CatCrypt.Crypto.Signal.EndToEnd
