/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.PAKE.CPaceBadReductions
public import CatCryptCore.Crypto.PAKE.CPaceSquareTimed
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveTimeBound
public import CatCryptCore.Tactics.AutoTime

/-!
# Running time of the reductions of the CPace bad events

The reductions of `CatCryptCore.Crypto.PAKE.CPaceBadReductions` are instances of
`OracleAdv.stepRedO`, which runs an oracle adversary against a world stepped by oracle programs,
then a final program, and answers the queries of these programs by the programs of a
translation. The double-match adversary `dmAdv G B` is `stepRedO` at the world with handles
`hImpl`, the final sweep of match tests and the translation `dmTrans`; the program `psProg` of
the passive-session reduction `psAdv` (`psOut_eq`) draws the table of `H1` and runs `stepRedO`
at `hImpl`, the output `psExtract` and the answers `psAns`.

**The generic reduction.** `derive_timed stepRedO` defines `stepRedO.timed`, generic in the
state, the step, the final program and the translation, which become binders with cost
companions, and proves `stepRedO.erase_timed`. Its time (`stepRedO.timeBound_timed`): with the
steps from the states reached after `i` steps of time at most `F i`, the final program of time
at most `Ext` and the programs of the translation of time at most `c`, a costed adversary of time
`T` with at most `q` queries gives a costed reduction of time at most
`(T + q · F q + Ext) · (c + 1)`.

**The costed instances.** The programs of the world with handles (`extractO`, …, `simStartO`),
the translation `dmTrans`, the sweep `dmFin`, the answers `psTrans` and the output `psFin` are
derived by `derive_timed`; the data functions of the end of an activation (`fStepD`,
`simResumeV`, `simAnswer`, `drive1D`) and the messages `msgDM`, `msgPS` by `derive_cost`. The
costed step `hImplC` is the uniform draw, the costed start `simStartO.timed` from the state with
its tables read at unit cost (`liftCore`), and the end of the activation at its derived cost
`finTime`; it erases to `hImpl` (`hImplC_erase`). `dmAdvC` and `psProgC` are the corresponding
instances of `stepRedO.timed`; they erase to `dmAdv` and `psProg` (`dmAdvC_erase`,
`psProgC_erase`).

**The time of the pieces.** An extraction over the candidates `cands` costs at most
`6 · |cands| + 1` (`extractO.timeBound_timed`), a late test at most `12 · |cands| + 100` plus the
cost companions read (`lateTargetO.timeBound_timed`), the search of a table `l` of `H2` at most
`(6 · |cands| + 30) · |l| + 1` (`findMatchO.timeBound_timed`), and a translated query at most
`20 + te + 2 tf` (`dmTrans.timeBound_timed`).

## Main results

* `OracleAdv.stepRedO.timed`, `OracleAdv.stepRedO.erase_timed` (derived),
  `OracleAdv.stepRedO.timeBound_timed`: the certificate of the generic reduction.
* `hImplC_erase`, `dmAdvC_erase`, `psProgC_erase`: the costed instances erase to the step of the
  world with handles, to `dmAdv` and to the program of `psAdv`.
* `extractO.timeBound_timed`, `extractAtO.timeBound_timed`, `lateAtO.timeBound_timed`,
  `lateTargetO.timeBound_timed`, `findMatchO.timeBound_timed`, `dmTrans.timeBound_timed`: the
  time of the pieces.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.OracleAdv

open CatCrypt.Core OracleAdv.Timed

derive_timed stepRedO

variable {D R σ τ ρ E A D' R' Out : Type}

/-- **The time of `stepRedO`.** Let `Inv i` hold of the states reached after `i` steps, each
step from a state of `Inv i` of time at most `F i` (`F` monotone) with its cost of computing the
program, the final program from a state of `Inv q` of time at most `Ext`, and each program of
`trans` of time at most `c`. Then a costed adversary `B` of time `T` with at most `q` queries
gives a costed reduction of time at most `(T + q · F q + Ext) · (c + 1)`: the program of the world
has time at most `T + q · F q + Ext`, hence at most that many queries, each answered by a program
of `trans`. -/
theorem stepRedO.timeBound_timed (impl : σ → E → OracleAdv.Timed D R (A × σ))
    (implCost : σ → E → ℕ) (fin : σ → OracleAdv.Timed D R Out) (finCost : σ → ℕ)
    (trans : τ → D → OracleAdv.Timed D' R' (R × τ)) (transCost : τ → D → ℕ)
    (Inv : ℕ → σ → Prop) (F : ℕ → ℕ) (hF : Monotone F) {Ext c : ℕ}
    (hmono : ∀ i s, Inv i s → Inv (i + 1) s)
    (himpl : ∀ i s e, Inv i s →
      StepTimeBound (1 + implCost s e, impl s e) (F i) ∧
        AllRet (fun y => Inv (i + 1) y.2) (impl s e))
    (B : OracleAdv.Timed E A ρ) {T q : ℕ} (hB : B.TimeBound T) (hq : B.erase.IsQueryBound q)
    (hfin : ∀ s, Inv q s → StepTimeBound (1 + finCost s, fin s) Ext)
    (htrans : ∀ t d, StepTimeBound (1 + transCost t d, trans t d) c)
    (s₀ : σ) (t₀ : τ) (h0 : Inv 0 s₀) :
    StepTimeBound (stepRedO.timed impl implCost fin finCost trans transCost B s₀ t₀)
      ((T + q * F q + Ext) * (c + 1)) := by
  have hsim := timeBound_simulateHat_inv id id (fun s e => (1 + implCost s e, impl s e)) Inv F
    himpl hB hq 0 s₀ h0
  have hall := allRet_simulateHat_inv id id (fun s e => (1 + implCost s e, impl s e)) Inv
    (fun i s e h => (himpl i s e h).2) hmono hq 0 s₀ h0
  unfold simulateHat at hsim hall
  rw [Nat.zero_add] at hall
  have hsum : ∑ j ∈ Finset.range q, F (0 + j) ≤ q * F q := by
    calc ∑ j ∈ Finset.range q, F (0 + j) ≤ ∑ _j ∈ Finset.range q, F q :=
          Finset.sum_le_sum fun j hj => hF (by have := Finset.mem_range.mp hj; omega)
      _ = q * F q := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have h2 := timeBound_bind_of_allRet (n := Ext) hsim.2 hall fun p hp => hfin p.2 hp
  have h3 := timeBound_simulate (fun t d => (1 + transCost t d, trans t d)) htrans h2.2
    (isQueryBound_of_timeBound h2.2) t₀
  have h4 := timeBound_bind (n := 0) h3.2 fun p => (⟨le_rfl, trivial⟩ :
    StepTimeBound ((0 : ℕ), (OracleAdv.Timed.ret p.1 : OracleAdv.Timed D' R' Out)) 0)
  unfold stepRedO.timed
  refine (stepTimeBound_delay h4).mono ?_
  have e1 := hsim.1
  have e2 := h2.1
  have e3 := h3.1
  have hm := Nat.mul_le_mul_right c (show T + ∑ j ∈ Finset.range q, F (0 + j) -
    (Timed.simulate (fun s e => (1 + implCost s e, impl s e)) B s₀).1 + Ext -
      ((Timed.simulate (fun s e => (1 + implCost s e, impl s e)) B s₀).2.bind
        fun p => (1 + finCost p.2, fin p.2)).1 ≤ T + q * F q + Ext by omega)
  rw [Nat.mul_succ]
  omega

end CatCrypt.Crypto.OracleAdv

namespace CatCrypt.Crypto.PAKE.CPaceBadReductions

open CatCrypt.Core OracleAdv.Timed UCTransparent.FPAKE CPaceSquare CPaceHops OracleGameUpToBad
  DHExtract

derive_timed extractO
derive_timed extractAtO
derive_timed lateAtO
derive_timed lateTargetO
derive_timed findMatchO
derive_timed sendCoreO
derive_timed h2CoreO
derive_timed advCoreO
derive_timed simStartO
derive_timed queryAll
derive_timed dmTrans
derive_cost fStepD
derive_cost simResumeV
derive_cost simAnswer
derive_cost drive1D

section Pieces

variable {S W Pw K : Type} [Field S] (G : DHGroup S W) [DecidableEq W] [DecidableEq Pw]
  [Inhabited K]

/-- The final program of the double-match reduction: the match tests of the final sweep. -/
def dmFin (s : SimSt S W Pw K × St Pw K) : OracleAdv (HQ S W Pw) (HA W) Unit :=
  queryAll (sweepQ s.1)

/-- The answers of the passive-session reduction as a program. -/
def psTrans (O : W → W → W → Bool) (A B' : W) (td : Pw → Sˣ) (_ : Unit) (q : HQ S W Pw) :
    OracleAdv Empty Empty (HA W × Unit) :=
  .ret (psAns G O A B' td q, ())

/-- The final program of the passive-session reduction: its output. -/
def psFin (O : W → W → W → Bool) (A B' : W) (td : Pw → Sˣ) (s : SimSt S W Pw K × St Pw K) :
    OracleAdv (HQ S W Pw) (HA W) W :=
  .ret (psExtract G O A B' td s)

end Pieces

derive_timed dmFin
derive_timed psTrans
derive_timed psFin
/-- **The time of an extraction**: one query and a constant per candidate. -/
theorem extractO.timeBound_timed {S W Pw : Type} (pid : PartyId) (u : S) (peer k : W)
    (l : List Pw) : StepTimeBound (extractO.timed pid u peer k l) (6 * l.length + 1) := by
  induction l with
  | nil => exact ⟨by simp [extractO.timed, delay], trivial⟩
  | cons pw rest ih =>
    simp only [extractO.timed, delay, StepTimeBound, timeBound_query_iff, List.length_cons]
    refine ⟨by omega, by omega, fun a => ?_⟩
    split_ifs
    · exact ⟨by omega, trivial⟩
    · exact ⟨by have := ih.1; omega, ih.2.mono (by omega)⟩

/-- The time of an extraction at an input of `H2`. -/
theorem extractAtO.timeBound_timed {S W Pw : Type} (cands : List Pw) (u : S) (pid : PartyId)
    (x : Inp W) : StepTimeBound (extractAtO.timed cands u pid x) (6 * cands.length + 20) := by
  time_bound

/-- The time of a late test of one party, plus the cost companions of its tables read. -/
theorem lateAtO.timeBound_timed {S W Pw K : Type} [Field S] [DecidableEq W]
    (c : SimCore S W Pw K) (x : Inp W) (pid : PartyId) (pendCost zsCost : PartyId → ℕ) :
    StepTimeBound (lateAtO.timed c x pid pendCost zsCost)
      (6 * c.cands.length + 40 + pendCost pid + zsCost pid) := by
  time_bound

/-- The time of the late tests of the two parties, plus the cost companions read. -/
theorem lateTargetO.timeBound_timed {S W Pw K : Type} [Field S] [DecidableEq W]
    (c : SimCore S W Pw K) (x : Inp W) (pendCost zsCost : PartyId → ℕ) :
    StepTimeBound (lateTargetO.timed c x pendCost zsCost)
      (12 * c.cands.length + 100 + pendCost 0 + zsCost 0 + pendCost 1 + zsCost 1) := by
  time_bound

/-- **The time of the search of a table of `H2`**: an extraction and a constant per entry. -/
theorem findMatchO.timeBound_timed {S W Pw K : Type} [DecidableEq W] (cands : List Pw) (u : S)
    (pid : PartyId) (T : Role × W × W) (l : List (Inp W × K)) :
    StepTimeBound (findMatchO.timed cands u pid T l)
      ((6 * cands.length + 30) * l.length + 1) := by
  induction l with
  | nil => exact ⟨by simp [findMatchO.timed, delay], trivial⟩
  | cons e rest ih =>
    have hx := extractAtO.timeBound_timed cands u pid e.1
    have hf : ∀ o : Option Pw, StepTimeBound (delay 1 (match o with
        | some pw => ((0 : ℕ), OracleAdv.Timed.ret (some (pw, e.2)))
        | none => delay 1 (findMatchO.timed cands u pid T rest)))
        ((6 * cands.length + 30) * rest.length + 3) := by
      intro o
      cases o with
      | none => exact (stepTimeBound_delay (stepTimeBound_delay ih)).mono (by omega)
      | some pw => exact ⟨by simp only [delay]; omega, trivial⟩
    simp only [findMatchO.timed, List.length_cons]
    split_ifs
    · refine (stepTimeBound_delay (stepTimeBound_delay (stepTimeBound_delay
        (timeBound_bind hx.2 hf)))).mono ?_
      have := hx.1
      simp only [extractAtO.timed, delay] at this ⊢
      rw [Nat.mul_succ]
      omega
    · refine (stepTimeBound_delay (stepTimeBound_delay (stepTimeBound_delay ih))).mono ?_
      rw [Nat.mul_succ]
      omega

section Costed

variable {S W Pw K : Type} [Field S] [Fintype S] [DecidableEq W] [DecidableEq Pw] [Fintype K]
  [Nonempty K] [Inhabited K] (G : DHGroup S W)

/-- The core state of the simulator with its tables read at unit cost: every cost companion is
zero. -/
def liftCore (c : SimCore S W Pw K) : CoreHat S W Pw K :=
  (c.td.map fun f => (f, fun _ => 0), c.cands, (c.info, fun _ => 0), (c.zs, fun _ => 0),
    (c.keyed, fun _ => 0), (c.pend, fun _ => 0), c.h2, c.phase)

/-- The erasure of a result of the costed start of the simulator. -/
def eraseStart (y : (CoreHat S W Pw K × List (Inp W × K)) × Dec Pw W K) :
    SimSt S W Pw K × Dec Pw W K :=
  (({ td := Option.map (fun x => x.1) y.1.1.1, cands := y.1.1.2.1, info := y.1.1.2.2.1.1,
      zs := y.1.1.2.2.2.1.1, keyed := y.1.1.2.2.2.2.1.1, pend := y.1.1.2.2.2.2.2.1.1,
      h2 := y.1.1.2.2.2.2.2.2.1, phase := y.1.1.2.2.2.2.2.2.2 }, y.1.2), y.2)

/-- The end of an activation of the world with handles, as in `hImpl`. -/
def finishH (st : SimSt S W Pw K × Dec Pw W K) (t : St Pw K) (k : K × K) :
    OOut W K × (SimSt S W Pw K × St Pw K) :=
  ((drive1D fStepD simResumeV simAnswer st.1 st.2 t k).2.2,
    ((drive1D fStepD simResumeV simAnswer st.1 st.2 t k).1,
      (drive1D fStepD simResumeV simAnswer st.1 st.2 t k).2.1))

/-- The cost of the end of an activation of the world with handles: the derived cost of
`drive1D` with the step `fStepD` of `F_lePAKE`, its records read at unit cost. -/
noncomputable def finTime (st : SimSt S W Pw K × Dec Pw W K) (t : St Pw K) (k : K × K) : ℕ :=
  drive1D.timedCost fStepD (fun t e kf => fStepD.timedCost t e kf fun _ => 0) simResumeV
    simResumeV.timedCost simAnswer simAnswer.timedCost st.1 st.2 t k

variable (msgF : PartyId → S → W) (msgFCost : PartyId → S → ℕ) (toFunCost : S → ℕ)

/-- The costed start of the simulator with handles from a state with its tables read at unit
cost. -/
noncomputable def startC (t : SimSt S W Pw K × St Pw K) (e : OEv Pw W) (r : S × K) :
    ℕ × OracleAdv.Timed (HQ S W Pw) (HA W) ((CoreHat S W Pw K × List (Inp W × K)) × Dec Pw W K) :=
  simStartO.timed G msgF msgFCost t.1 e r (fun _ => 0) (liftCore t.1.1) (fun _ => 0) (fun _ => 0)
    (fun _ => 0) toFunCost

/-- The costed activation after the draw `r`: the costed start, then the end of the activation
at the cost `finTime`. -/
noncomputable def stepC (t : SimSt S W Pw K × St Pw K) (e : OEv Pw W) (r : (S × K) × K × K) :
    ℕ × OracleAdv.Timed (HQ S W Pw) (HA W) (OOut W K × (SimSt S W Pw K × St Pw K)) :=
  (startC G msgF msgFCost toFunCost t e r.1).2.bind fun y =>
    (finTime (eraseStart y) t.2 r.2, .ret (finishH (eraseStart y) t.2 r.2))

/-- **The costed step of the world with handles**: the uniform draw, the costed start of the
simulator `simStartO.timed` and the end of the activation at the cost `finTime`. -/
noncomputable def hImplC (t : SimSt S W Pw K × St Pw K) (e : OEv Pw W) :
    OracleAdv.Timed (HQ S W Pw) (HA W) (OOut W K × (SimSt S W Pw K × St Pw K)) :=
  .rand (PMF.uniformFintype ((S × K) × K × K))
    (fun r => (startC G msgF msgFCost toFunCost t e r.1).1 +
      (stepC G msgF msgFCost toFunCost t e r).1)
    fun r => (stepC G msgF msgFCost toFunCost t e r).2

/-- The costed step of the world with handles erases to the step `hImpl`. -/
theorem hImplC_erase (t : SimSt S W Pw K × St Pw K) (e : OEv Pw W) :
    (hImplC G msgF msgFCost toFunCost t e).erase = hImpl G msgF t e := by
  unfold hImplC hImpl
  simp only [OracleAdv.Timed.erase]
  refine congrArg _ (funext fun r => ?_)
  unfold stepC
  rw [OracleAdv.Timed.erase_bind]
  rw [← simStartO.erase_timed G msgF msgFCost t.1 e r.1 (fun _ => 0) (liftCore t.1.1)
    (fun _ => 0) (fun _ => 0) (fun _ => 0) toFunCost]
  rw [OracleAdv.bind_assoc]
  rfl

end Costed

derive_cost msgDM
derive_cost msgPS
section Instances

variable {S W Pw K : Type} [Field S] [Fintype S] [DecidableEq S] [DecidableEq W] [Fintype Pw]
  [DecidableEq Pw] [Fintype K] [Nonempty K] [Inhabited K] (G : DHGroup S W)
  (expCost : W → S → ℕ) (mulCost : W → W → ℕ) (toFunCost : S → ℕ)

/-- **The costed double-match adversary** on the simulated message `X`: `stepRedO.timed` at the
costed step of the world with handles, a party with handle `u` sending `X^u`, the costed sweep
`dmFin.timed` and the costed translation `dmTrans.timed`, the tables of the states read at unit
cost. -/
noncomputable def dmAdvC (B : OracleAdv.Timed (OEv Pw W) (OOut W K) Bool) (X : W) :
    ℕ × OracleAdv.Timed (CPaceH1.Query W Pw) (CPaceH1.Answer W) Unit :=
  OracleAdv.stepRedO.timed
    (hImplC G (msgDM G X) (fun pid u => msgDM.timedCost G X pid u expCost) toFunCost)
    (fun _ _ => 0) (fun s => (dmFin.timed s fun _ => 0).2) (fun s => (dmFin.timed s fun _ => 0).1)
    (fun t d => (dmTrans.timed G t d expCost toFunCost).2)
    (fun t d => (dmTrans.timed G t d expCost toFunCost).1) B (hInit G) ()

/-- The costed double-match adversary erases to `dmAdv`. -/
theorem dmAdvC_erase (B : OracleAdv.Timed (OEv Pw W) (OOut W K) Bool) (X : W) :
    (dmAdvC G expCost toFunCost B X).2.erase = dmAdv G B.erase X := by
  simp only [dmAdvC, dmAdv, OracleAdv.stepRedO.erase_timed, hImplC_erase, dmFin.erase_timed,
    dmTrans.erase_timed, dmFin]

variable (O : W → W → W → Bool) (OCost : W → W → W → ℕ) (A B' : W)

/-- The costed run of the passive-session reduction at the table `td` of `H1`:
`stepRedO.timed` at the costed step of the world with handles, a party with handle `u` sending
its challenge value times `g^u`, the costed output `psFin.timed` and the costed answers
`psTrans.timed`, the tables of the states read at unit cost. -/
noncomputable def psRunC (B : OracleAdv.Timed (OEv Pw W) (OOut W K) Bool) (td : Pw → Sˣ) :
    ℕ × OracleAdv.Timed Empty Empty W :=
  OracleAdv.stepRedO.timed
    (hImplC G (msgPS G A B') (fun pid u => msgPS.timedCost G A B' pid u mulCost toFunCost)
      toFunCost)
    (fun _ _ => 0)
    (fun s => (psFin.timed G O OCost A B' td (fun _ => 0) s (fun _ => 0) (fun _ => 0) mulCost
      toFunCost expCost).2)
    (fun s => (psFin.timed G O OCost A B' td (fun _ => 0) s (fun _ => 0) (fun _ => 0) mulCost
      toFunCost expCost).1)
    (fun t q => (psTrans.timed G O OCost A B' td (fun _ => 0) t q toFunCost mulCost expCost).2)
    (fun t q => (psTrans.timed G O OCost A B' td (fun _ => 0) t q toFunCost mulCost expCost).1)
    B (hInit G) ()

/-- **The costed program of the passive-session reduction**: the uniform draw of the table of
`H1`, then `psRunC`. -/
noncomputable def psProgC (B : OracleAdv.Timed (OEv Pw W) (OOut W K) Bool) :
    ℕ × OracleAdv.Timed Empty Empty W :=
  (0, .rand (PMF.uniformFintype (Pw → Sˣ))
    (fun td => (psRunC G expCost mulCost toFunCost O OCost A B' B td).1)
    fun td => (psRunC G expCost mulCost toFunCost O OCost A B' B td).2)

/-- The costed program of the passive-session reduction erases to `psProg`, whose output
distribution is that of the reduction `psAdv` (`psOut_eq`). -/
theorem psProgC_erase (B : OracleAdv.Timed (OEv Pw W) (OOut W K) Bool) :
    (psProgC G expCost mulCost toFunCost O OCost A B' B).2.erase = psProg G B.erase O A B' := by
  simp only [psProgC, psProg, psRunC, OracleAdv.Timed.erase, OracleAdv.stepRedO.erase_timed,
    hImplC_erase, psFin.erase_timed, psTrans.erase_timed, psFin, psTrans]

omit [Fintype S] [Fintype Pw] [DecidableEq Pw] in
/-- **The time of a translated query of the double-match reduction**, at exponentiations of
cost at most `te` and public values of cost at most `tf`. -/
theorem dmTrans.timeBound_timed (t : Unit) (d : HQ S W Pw) {te tf : ℕ}
    (he : ∀ x y, expCost x y ≤ te) (hf : ∀ x, toFunCost x ≤ tf) :
    StepTimeBound (dmTrans.timed G t d expCost toFunCost) (20 + te + 2 * tf) := by
  time_bound

end Instances

end CatCrypt.Crypto.PAKE.CPaceBadReductions
