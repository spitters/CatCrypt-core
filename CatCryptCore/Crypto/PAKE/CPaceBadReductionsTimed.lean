/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.PAKE.CPaceBadReductions
public import CatCryptCore.Crypto.PAKE.CPaceSquareTimed
public import CatCryptCore.Crypto.PAKE.CPaceH1Timed
public import CatCryptCore.Tactics.DeriveReduction.Basic
public import CatCryptCore.Tactics.DeriveTimeBound.Basic
import CatCryptCore.Tactics.AutoTime
public import CatCryptCore.Tactics.AutoTime.Basic
import CatCryptCore.Tactics.DeriveCost

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
`20 + te + 2 tf` (`dmTrans.timeBound_timed`). With the tables of the parties read at unit cost,
a `send` of a party that holds a handle costs at most `(6 · |cands| + 30) · |h2| + 60 + 3 tm + tf`
(`sendCoreO.timeBound_timed`): the subtraction `1 - pid` is linear in `pid`, and only the parties
`0` and `1` hold a handle. An adversary event costs at most
`(6 · |cands| + 35) · |h2| + 12 · |cands| + 130 + 3 tm + tf` (`advCoreO.timeBound_timed`), the
costed start at most that plus five units per programmed input (`startC.timeBound`), and the end
of an activation at most `64 · |notices| + 700` (`finTime_le`), at most two steps of `F_lePAKE`,
each linear in its notices.

**The invariant.** `HInv i` holds of the states reached after `i` activations: the queried
passwords are distinct, the table of `H2` and the programmed inputs have at most `i` entries, only
the parties `0` and `1` hold a handle, and `F_lePAKE` holds at most `2 i` notices. Each step
adds at most one entry to each table and one notice per call of `F_lePAKE`. From a state of
`HInv i` a costed step has time at most `F i = (6 |Pw| + 168) i + 12 |Pw| + 850 + 3 tm + tf` and
returns states of `HInv (i + 1)` (`hImplC.timeBound`), the graded form of the time of the
simulator `cpaceSim.timeBoundGraded_timed_len`. The final sweep costs at most
`(24 |cands| + 40) · (|progs| + |h2|) + 20` (`dmFin.timeBound_timed`), the output of the
passive-session reduction a constant per input of the tables (`psFin.timeBound_timed`), and an
answer a constant (`psTrans.timeBound_timed`).

**The time of the reductions.** `stepRedO.timeBound_timed` at `HInv` gives the time of `dmAdvC`
and of `psProgC` for a costed adversary of time `T` with at most `q` queries, a polynomial in
`q`, `|Pw|` and `T` at the costs of the group operations (`dmAdvC.timeBound`,
`psProgC.timeBound`).

**The reductions of the concrete bound.** The strong SDH term of `cpaceConcreteBound` is at the
reduction `ssdhReduction G (matchWrap (dmAdv G B))`. Its costed form `ssdhDmC` is
`ssdhReduction.timed` at `matchWrap.timed` of `dmAdvC` and erases to it (`ssdhDmC_erase`). The
time `D` of `dmAdvC` bounds its number of queries, so `matchWrap.timeBound_timed` and
`ssdhReduction.timeBound_timed` give the time `(h + 18) (te + 6) (D + 1)² + 2 te + 10` at
lookups of the generator table of cost at most `h` (`ssdhDmC.timeBound`). The gap
Diffie–Hellman term is at `psAdv G B`, which on the decision oracle `O` and the challenge
`(A, B')` is the lift of the output of `psProg`. Its costed form `psAdvC` is `psProgC` at `O`;
the lift of the output of the run of its erasure is `psAdv G B` (`psAdvC_erase`), and its time
is that of `psProgC` (`psAdvC.timeBound`).

## Main results

* `OracleAdv.stepRedO.timed`, `OracleAdv.stepRedO.erase_timed` (derived),
  `OracleAdv.stepRedO.timeBound_timed`: the certificate of the generic reduction.
* `hImplC_erase`, `dmAdvC_erase`, `psProgC_erase`: the costed instances erase to the step of the
  world with handles, to `dmAdv` and to the program of `psAdv`.
* `extractO.timeBound_timed`, `extractAtO.timeBound_timed`, `lateAtO.timeBound_timed`,
  `lateTargetO.timeBound_timed`, `findMatchO.timeBound_timed`, `sendCoreO.timeBound_timed`,
  `h2CoreO.timeBound_timed`, `advCoreO.timeBound_timed`, `startC.timeBound`, `finTime_le`,
  `dmFin.timeBound_timed`, `psFin.timeBound_timed`, `psTrans.timeBound_timed`,
  `dmTrans.timeBound_timed`: the time of the pieces.
* `hImplC.timeBound`: the step time of the world with handles on the invariant `HInv`.
* `dmAdvC.timeBound`, `psProgC.timeBound`: the time of the two reductions.
* `ssdhDmC_erase`, `ssdhDmC.timeBound`: the costed strong SDH reduction of the double-match
  adversary erases to `ssdhReduction G (matchWrap (dmAdv G B))`, with its time, a polynomial in
  `q`, `|Pw|` and `T`.
* `psAdvC_erase`, `psAdvC.timeBound`: the costed gap Diffie–Hellman adversary erases to
  `psAdv G B`, with its time, a polynomial in `q`, `|Pw|` and `T`.
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

section PieceTime

variable {S W Pw K : Type} [Field S] (G : DHGroup S W) [DecidableEq W] [Inhabited K]

/-- **The time of a `send` with handles**, the tables of the parties read at unit cost: the
subtraction `1 - pid` for a party `pid ≤ 1` holding a handle, the messages of cost at most `tm`,
the public value of cost at most `tf`, and the search of the table of `H2`. -/
theorem sendCoreO.timeBound_timed (msgF : PartyId → S → W) (msgFCost : PartyId → S → ℕ)
    (c : SimCore S W Pw K) (pid : PartyId) (m : W) (toFunCost : S → ℕ) {tm tf : ℕ}
    (hm : ∀ p u, msgFCost p u ≤ tm) (hf : ∀ u, toFunCost u ≤ tf)
    (h01 : ∀ p, (c.zs p).isSome → p ≤ 1) :
    StepTimeBound (sendCoreO.timed G msgF msgFCost c pid m (fun _ => 0) (fun _ => 0) (fun _ => 0)
      (fun _ => 0) toFunCost) ((6 * c.cands.length + 30) * c.h2.length + 60 + 3 * tm + tf) := by
  unfold sendCoreO.timed
  rcases hzs : c.zs pid with _ | u
  · exact ⟨by simp [delay]; omega, trivial⟩
  · have hp : pid ≤ 1 := h01 pid (by simp [hzs])
    have hs := sub_one_timedCost_le hp
    rcases c.info pid with _ | ⟨_, role⟩
    · exact ⟨by simp [delay]; omega, trivial⟩
    · have := hf 0
      have := hm pid u
      dsimp only
      split_ifs with h1 h2
      · rcases hz' : c.zs (1 - pid) with _ | u'
        · simp [hz'] at h2
        · have := hm (1 - pid) u'
          refine ⟨?_, trivial⟩
          simp only [delay]
          omega
      all_goals first
        | exact ⟨by simp only [delay]; omega, trivial⟩
        | have hfm := findMatchO.timeBound_timed (K := K) c.cands u pid
            (h2Inp pid role (msgF pid u) m m).tr c.h2
          refine (stepTimeBound_delay (stepTimeBound_delay (stepTimeBound_delay
            (stepTimeBound_delay (timeBound_bind (n := 10 + tm) hfm.2 ?_))))).mono ?_
          · intro fm
            rcases fm with _ | ⟨pw, k⟩
            · exact ⟨by simp only [delay]; omega, trivial⟩
            · exact ⟨by simp only [delay]; omega, trivial⟩
          · have := hfm.1
            rcases hz' : c.zs (1 - pid) with _ | u' <;> simp only <;>
              (try have := hm (1 - pid) u') <;> omega

omit [Inhabited K] in
/-- The time of a fresh `H2` query with handles, the tables of the parties read at unit cost:
the late tests of the two parties. -/
theorem h2CoreO.timeBound_timed (c : SimCore S W Pw K) (x : Inp W) (k : K) :
    StepTimeBound (h2CoreO.timed c x k (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0))
      (12 * c.cands.length + 110) := by
  have hl := lateTargetO.timeBound_timed c x (fun _ => 0) (fun _ => 0)
  unfold h2CoreO.timed
  refine (stepTimeBound_delay (timeBound_bind (n := 8) hl.2 ?_)).mono ?_
  · intro lt
    rcases lt with _ | ⟨pid, pw⟩
    · exact ⟨by simp only [delay]; omega, trivial⟩
    · exact ⟨by simp only [delay]; omega, trivial⟩
  · have := hl.1
    omega

/-- The frame of a leaf of a costed step of the simulator core from the core `c`: the queried
passwords are distinct, the table of `H2` has at most one more entry than in `c`, and only the
parties `0` and `1` hold a handle. -/
def CoreLeaf (c : SimCore S W Pw K) (y : CoreHat S W Pw K) : Prop :=
  y.2.1.Nodup ∧ y.2.2.2.2.2.2.1.length ≤ c.h2.length + 1 ∧ ∀ q, (y.2.2.2.1.1 q).isSome → q ≤ 1

/-- The leaves of a costed `send` with handles keep the frame of the core. -/
theorem sendCoreO.allRet_timed (msgF : PartyId → S → W) (msgFCost : PartyId → S → ℕ)
    (c : SimCore S W Pw K) (pid : PartyId) (m : W) (toFunCost : S → ℕ) (hn : c.cands.Nodup)
    (h01 : ∀ p, (c.zs p).isSome → p ≤ 1) :
    AllRet (fun y => CoreLeaf c y.1) (sendCoreO.timed G msgF msgFCost c pid m (fun _ => 0)
      (fun _ => 0) (fun _ => 0) (fun _ => 0) toFunCost).2 := by
  have htriv : ∀ {α : Type} (A : OracleAdv.Timed (HQ S W Pw) (HA W) α),
      AllRet (fun _ => True) A := fun A => by
    induction A with
    | ret a => trivial
    | rand p c k ih => exact ih
    | query d c k ih => exact ih
  unfold sendCoreO.timed
  simp only [delay]
  repeat' split
  all_goals first
    | exact ⟨hn, by simp, h01⟩
    | exact allRet_bind (htriv _) fun fm _ => by
        rcases fm with _ | ⟨pw, k⟩ <;> exact ⟨hn, by simp, h01⟩

omit [Inhabited K] in
/-- The leaves of a costed fresh `H2` query with handles keep the frame of the core. -/
theorem h2CoreO.allRet_timed (c : SimCore S W Pw K) (x : Inp W) (k : K) (hn : c.cands.Nodup)
    (h01 : ∀ p, (c.zs p).isSome → p ≤ 1) :
    AllRet (fun y => CoreLeaf c y.1)
      (h2CoreO.timed c x k (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0)).2 := by
  have htriv : ∀ {α : Type} (A : OracleAdv.Timed (HQ S W Pw) (HA W) α),
      AllRet (fun _ => True) A := fun A => by
    induction A with
    | ret a => trivial
    | rand p c k ih => exact ih
    | query d c k ih => exact ih
  unfold h2CoreO.timed
  simp only [delay]
  exact allRet_bind (htriv _) fun lt _ => by
    rcases lt with _ | ⟨pid, pw⟩
    · exact ⟨hn, by simp, h01⟩
    · exact ⟨hn, by simp, h01⟩

variable [DecidableEq Pw]

/-- **The time of an adversary event with handles**, the tables of the parties read at unit
cost: at most the search of the table of `H2` at a `send`, or its lookup and the late tests at
a fresh `H2` query, or the membership test and the append on the queried passwords at an `H1`
query. -/
theorem advCoreO.timeBound_timed (msgF : PartyId → S → W) (msgFCost : PartyId → S → ℕ)
    (c : SimCore S W Pw K) (a : RAEv Pw W) (k : K) (toFunCost : S → ℕ) {tm tf : ℕ}
    (hm : ∀ p u, msgFCost p u ≤ tm) (hf : ∀ u, toFunCost u ≤ tf)
    (h01 : ∀ p, (c.zs p).isSome → p ≤ 1) :
    StepTimeBound (advCoreO.timed G msgF msgFCost c a k (fun _ => 0) (fun _ => 0) (fun _ => 0)
      (fun _ => 0) toFunCost)
      ((6 * c.cands.length + 35) * c.h2.length + 12 * c.cands.length + 130 + 3 * tm + tf) := by
  unfold advCoreO.timed
  cases a with
  | idle => exact ⟨by simp only [delay]; omega, trivial⟩
  | poll => exact ⟨by simp only [delay]; omega, trivial⟩
  | msg pid =>
    refine ⟨?_, trivial⟩
    simp only [delay]
    rcases c.zs pid with _ | u
    · simp only; omega
    · have := hm pid u
      simp only; omega
  | h1 pw =>
    have := List.elem.timedCost_le pw c.cands
    have := List.append.timedCost_eq c.cands [pw]
    have := hf 0
    simp only [delay, StepTimeBound, timeBound_query_iff]
    refine ⟨by omega, by omega, fun ans => ⟨?_, trivial⟩⟩
    split_ifs <;> omega
  | h2 x =>
    have hlk := List.lookup.timedCost_le x c.h2
    have hc := h2CoreO.timeBound_timed c x k
    have h5 : 5 * c.h2.length ≤ (6 * c.cands.length + 35) * c.h2.length :=
      Nat.mul_le_mul_right _ (by omega)
    dsimp only
    rcases hl : List.lookup x c.h2 with _ | k'
    · refine (stepTimeBound_delay (stepTimeBound_delay (stepTimeBound_delay hc))).mono ?_
      omega
    · exact ⟨by simp only [delay]; omega, trivial⟩
  | send pid m =>
    have hs := sendCoreO.timeBound_timed G msgF msgFCost c pid m toFunCost hm hf h01
    refine (stepTimeBound_delay (stepTimeBound_delay hs)).mono ?_
    have := Nat.le_mul_of_pos_right 5 (show 0 < 1 by omega)
    nlinarith

/-- The leaves of a costed adversary event with handles keep the frame of the core. -/
theorem advCoreO.allRet_timed (msgF : PartyId → S → W) (msgFCost : PartyId → S → ℕ)
    (c : SimCore S W Pw K) (a : RAEv Pw W) (k : K) (toFunCost : S → ℕ) (hn : c.cands.Nodup)
    (h01 : ∀ p, (c.zs p).isSome → p ≤ 1) :
    AllRet (fun y => CoreLeaf c y.1) (advCoreO.timed G msgF msgFCost c a k (fun _ => 0)
      (fun _ => 0) (fun _ => 0) (fun _ => 0) toFunCost).2 := by
  unfold advCoreO.timed
  cases a with
  | h1 pw =>
    intro ans
    refine ⟨?_, by simp, h01⟩
    dsimp only
    split_ifs with hm
    · exact hn
    · exact hn.append (List.nodup_singleton pw) (by simpa using hm)
  | h2 x =>
    simp only [delay]
    split
    · exact ⟨hn, by simp, h01⟩
    · exact h2CoreO.allRet_timed c x k hn h01
  | send pid m => exact sendCoreO.allRet_timed G msgF msgFCost c pid m toFunCost hn h01
  | _ => exact ⟨hn, by simp, h01⟩

end PieceTime

/-- A step of `F_lePAKE` with its records read at unit cost costs at most eight units per notice:
the append of a notice and the read at the cursor. -/
theorem fStepD.timedCost_le {Pw K : Type} [DecidableEq Pw] (t : St Pw K) (e : FEv Pw K)
    (kf : K) : fStepD.timedCost t e kf (fun _ => 0) ≤ 8 * t.notices.length + 60 := by
  have := List.get?Internal.timedCost_le t.notices t.cursor
  unfold fStepD.timedCost
  rcases e with h | a
  · cases h <;> dsimp only <;> (repeat' split) <;> (try rw [List.append.timedCost_eq]) <;> omega
  · cases a <;> dsimp only <;> (repeat' split) <;> omega

/-- **The invariant of the world with handles after `i` activations**: the queried passwords are
distinct, the table of `H2` and the programmed inputs have at most `i` entries, only the parties
`0` and `1` hold a handle, and `F_lePAKE` holds at most `2 i` notices. -/
def HInv {S W Pw K : Type} [Field S] (i : ℕ) (t : SimSt S W Pw K × St Pw K) : Prop :=
  t.1.1.cands.Nodup ∧ t.1.1.h2.length ≤ i ∧ t.1.2.length ≤ i ∧
    (∀ p, (t.1.1.zs p).isSome → p ≤ 1) ∧ t.2.notices.length ≤ 2 * i

/-- The invariant holds at every later activation count. -/
theorem HInv.succ {S W Pw K : Type} [Field S] {i : ℕ} {t : SimSt S W Pw K × St Pw K}
    (h : HInv i t) : HInv (i + 1) t := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  exact ⟨h1, by omega, by omega, h4, by omega⟩

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

omit [Fintype S] [DecidableEq W] [Fintype K] [Nonempty K] in
/-- **The cost of the end of an activation**: at most two steps of `F_lePAKE`, linear in its
notices, and constant work of the simulator. -/
theorem finTime_le (st : SimSt S W Pw K × Dec Pw W K) (t : St Pw K) (k : K × K) :
    finTime st t k ≤ 64 * t.notices.length + 700 := by
  have hr : ∀ (s : SimSt S W Pw K) (o : FOut K), simResumeV.timedCost s o ≤ 13 := fun s o => by
    unfold simResumeV.timedCost
    repeat' split
    all_goals omega
  have ha : ∀ (s : SimSt S W Pw K) (o : FOut K), simAnswer.timedCost s o ≤ 5 := fun s o => by
    unfold simAnswer.timedCost
    split <;> omega
  unfold finTime drive1D.timedCost
  rcases st with ⟨s, d⟩
  rcases d with g | o
  · dsimp only
    have h1 := fStepD.timedCost_le t g k.1
    have := hr s (fStepD t g k.1).2
    split
    · omega
    · rename_i g' _
      have h2 := fStepD.timedCost_le (fStepD t g k.1).1 g' k.2
      have h3 := fStepD_notices_length t g k.1
      have := ha (s := by assumption) (fStepD (fStepD t g k.1).1 g' k.2).2
      omega
  · dsimp only
    omega

omit [Fintype S] [Fintype K] [Nonempty K] in
/-- **The time of the costed start**, from a state in which only the parties `0` and `1` hold a
handle: the lookup of the programmed inputs and the adversary event, or a constant at an honest
event. -/
theorem startC.timeBound (t : SimSt S W Pw K × St Pw K) (e : OEv Pw W) (r : S × K) {tm tf : ℕ}
    (hm : ∀ p u, msgFCost p u ≤ tm) (hf : ∀ u, toFunCost u ≤ tf)
    (h01 : ∀ p, (t.1.1.zs p).isSome → p ≤ 1) :
    StepTimeBound (startC G msgF msgFCost toFunCost t e r)
      ((6 * t.1.1.cands.length + 35) * t.1.1.h2.length + 12 * t.1.1.cands.length +
        5 * t.1.2.length + 140 + 3 * tm + tf) := by
  have ha := fun a => advCoreO.timeBound_timed G msgF msgFCost t.1.1 a r.2 toFunCost hm hf h01
  unfold startC simStartO.timed
  rcases e with h | a
  · refine ⟨?_, trivial⟩
    simp only [delay, liftCore]
    split <;> (try split_ifs) <;> omega
  · have hgen : ∀ (a : RAEv Pw W) {β : Type} (g : _ → β),
        StepTimeBound (delay 1 (delay (1 + (advCoreO.timed G msgF msgFCost t.1.1 a r.2 (fun _ => 0)
          (fun _ => 0) (fun _ => 0) (fun _ => 0) toFunCost).1) ((advCoreO.timed G msgF msgFCost
            t.1.1 a r.2 (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) toFunCost).2.bind
              fun p => (0, OracleAdv.Timed.ret (g p)))))
          ((6 * t.1.1.cands.length + 35) * t.1.1.h2.length + 12 * t.1.1.cands.length +
            5 * t.1.2.length + 140 + 3 * tm + tf) := fun a β g => by
      refine (stepTimeBound_delay (stepTimeBound_delay (timeBound_bind (n := 0) (ha a).2
        ?_))).mono ?_
      · intro p
        exact ⟨le_rfl, trivial⟩
      · have := (ha a).1
        omega
    cases a
    case h2 x =>
      have hlk := List.lookup.timedCost_le x t.1.2
      dsimp only
      rcases hl : List.lookup x t.1.2 with _ | k
      · refine (stepTimeBound_delay (stepTimeBound_delay (stepTimeBound_delay
          (timeBound_bind (n := 0) (ha (.h2 x)).2 ?_)))).mono ?_
        · intro p
          exact ⟨le_rfl, trivial⟩
        · have := (ha (.h2 x)).1
          omega
      · exact ⟨by simp only [delay]; omega, trivial⟩
    all_goals
      dsimp only
      exact hgen _ _

/-- The frame of a leaf of the costed start from the state `t`: the queried passwords are
distinct, the table of `H2` has at most one more entry, the programmed inputs are those of `t`,
and only the parties `0` and `1` hold a handle. -/
def StartLeaf (t : SimSt S W Pw K × St Pw K)
    (y : (CoreHat S W Pw K × List (Inp W × K)) × Dec Pw W K) : Prop :=
  (eraseStart y).1.1.cands.Nodup ∧ (eraseStart y).1.1.h2.length ≤ t.1.1.h2.length + 1 ∧
    (eraseStart y).1.2 = t.1.2 ∧ ∀ p, ((eraseStart y).1.1.zs p).isSome → p ≤ 1

omit [Fintype S] [Fintype K] [Nonempty K] in
/-- The leaves of the costed start keep the frame of the state. -/
theorem startC.allRet (t : SimSt S W Pw K × St Pw K) (e : OEv Pw W) (r : S × K)
    (hn : t.1.1.cands.Nodup) (h01 : ∀ p, (t.1.1.zs p).isSome → p ≤ 1) :
    AllRet (StartLeaf t) (startC G msgF msgFCost toFunCost t e r).2 := by
  have ha := fun a => advCoreO.allRet_timed G msgF msgFCost t.1.1 a r.2 toFunCost hn h01
  have hgen : ∀ a : RAEv Pw W, AllRet (StartLeaf t) ((advCoreO.timed G msgF msgFCost t.1.1 a r.2
      (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) toFunCost).2.bind fun p => (0,
        OracleAdv.Timed.ret ((p.1, t.1.2), p.2))).2 := fun a =>
    allRet_bind (ha a) fun p hp => ⟨hp.1, hp.2.1, rfl, hp.2.2⟩
  unfold startC simStartO.timed
  rcases e with h | a
  · simp only [delay, AllRet]
    generalize honPub h = o
    rcases o with _ | ⟨sid, pid, peer, role⟩
    · exact ⟨hn, by simp [eraseStart], rfl, h01⟩
    · dsimp only
      split_ifs with h1 h2
      · refine ⟨by simp only [eraseStart, honCoreD]; split_ifs; exact hn,
          by simp only [eraseStart, honCoreD]; split_ifs; simp, rfl, fun q hq => ?_⟩
        by_cases hqp : q = pid
        · exact hqp ▸ h1.2.1
        · simp only [eraseStart, Function.update_of_ne hqp] at hq
          exact h01 q hq
      · exact ⟨by simp only [eraseStart, honCoreD]; split_ifs; exact hn,
          by simp only [eraseStart, honCoreD]; split_ifs; simp, rfl, h01⟩
      · exact ⟨by simp only [eraseStart, honCoreD]; split_ifs; exact hn,
          by simp only [eraseStart, honCoreD]; split_ifs; simp, rfl, h01⟩
  · cases a
    case h2 x =>
      simp only [delay]
      split
      · exact ⟨hn, by simp [eraseStart], rfl, h01⟩
      · exact hgen _
    all_goals exact hgen _

/-- **The step time of the costed world with handles.** From a state of the invariant `HInv i`,
with messages of cost at most `tm` and public values of cost at most `tf`, a step costs at most
`(6 |Pw| + 168) i + 12 |Pw| + 850 + 3 tm + tf` and returns states of `HInv (i + 1)`. -/
theorem hImplC.timeBound [Fintype Pw] {tm tf : ℕ} (hm : ∀ p u, msgFCost p u ≤ tm)
    (hf : ∀ u, toFunCost u ≤ tf) (i : ℕ) (t : SimSt S W Pw K × St Pw K) (e : OEv Pw W)
    (ht : HInv i t) :
    StepTimeBound (1 + 0, hImplC G msgF msgFCost toFunCost t e)
        ((6 * Fintype.card Pw + 168) * i + 12 * Fintype.card Pw + 850 + 3 * tm + tf) ∧
      AllRet (fun y => HInv (i + 1) y.2) (hImplC G msgF msgFCost toFunCost t e) := by
  obtain ⟨hn, hh, hp, h01, hno⟩ := ht
  have hc := hn.length_le_card
  refine ⟨⟨by omega, ?_⟩, fun r => ?_⟩
  · refine ⟨by omega, fun r => ?_⟩
    have hs := startC.timeBound G msgF msgFCost toFunCost t e r.1 hm hf h01
    have hb := timeBound_bind (n := 64 * t.2.notices.length + 700) hs.2
      (f := fun y => (finTime (eraseStart y) t.2 r.2, OracleAdv.Timed.ret
        (finishH (eraseStart y) t.2 r.2))) fun y => ⟨finTime_le _ _ _, trivial⟩
    refine (stepTimeBound_delay hb).mono ?_
    have := hs.1
    have h1 : (6 * t.1.1.cands.length + 35) * t.1.1.h2.length ≤
        (6 * Fintype.card Pw + 35) * i := Nat.mul_le_mul (by omega) hh
    have h2 : (6 * Fintype.card Pw + 168) * i = (6 * Fintype.card Pw + 35) * i + 133 * i := by
      ring
    omega
  · refine allRet_bind (startC.allRet G msgF msgFCost toFunCost t e r.1 hn h01) fun y hy => ?_
    obtain ⟨hn', hh', hp', h01'⟩ := hy
    obtain ⟨hf1, hf2⟩ := drive1D_frame (eraseStart y).1 (eraseStart y).2 t.2 r.2
    have hno' := drive1D_notices_length (eraseStart y).1 (eraseStart y).2 t.2 r.2
    have hcands := congrArg SimCore.cands hf1
    have hh2 := congrArg SimCore.h2 hf1
    have hzs := congrArg SimCore.zs hf1
    simp only at hcands hh2 hzs
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [finishH]
    · rw [hcands]
      exact hn'
    · rw [hh2]
      omega
    · rcases hf2 with h | ⟨x, h⟩ <;> rw [h, hp'] <;> (try simp only [List.length_cons]) <;> omega
    · rw [hzs]
      exact h01'
    · omega

end Costed

section FinalTime

variable {S W Pw K : Type} [Field S]

omit [Field S] in
/-- The time of asking the queries of a list: three units per query and one more. -/
theorem queryAll.timeBound_timed (l : List (HQ S W Pw)) :
    StepTimeBound (queryAll.timed l) (3 * l.length + 1) := by
  induction l with
  | nil => exact ⟨by simp [queryAll.timed, delay], trivial⟩
  | cons q l ih =>
    simp only [queryAll.timed, delay, StepTimeBound, timeBound_query_iff, List.length_cons]
    have := ih.1
    exact ⟨by omega, by omega, fun _ => ⟨by omega, ih.2.mono (by omega)⟩⟩

/-- **The time of the final sweep of the double-match reduction**: linear in the number of
inputs of the simulator's tables times the number of queried passwords. -/
theorem dmFin.timeBound_timed (s : SimSt S W Pw K × St Pw K) :
    StepTimeBound (dmFin.timed s fun _ => 0)
      ((24 * s.1.1.cands.length + 40) * (s.1.2.length + s.1.1.h2.length) + 20) := by
  unfold dmFin.timed
  refine (stepTimeBound_delay (queryAll.timeBound_timed _)).mono ?_
  have hq := sweepQ_length s.1
  have := List.map.timedCost_le Prod.fst (fun _ => 0) (k := 0) (fun _ => le_rfl) s.1.2
  have := List.map.timedCost_le Prod.fst (fun _ => 0) (k := 0) (fun _ => le_rfl) s.1.1.h2
  rw [List.append.timedCost_eq]
  grw [List.map.timedCost_le _ _ (k := 14 * s.1.1.cands.length + 27) ?_
    (List.map Prod.fst s.1.2 ++ List.map Prod.fst s.1.1.h2)]
  grw [List.flatten.timedCost_le (2 * s.1.1.cands.length) _ ?_]
  · simp only [List.length_append, List.length_map]
    nlinarith
  · intro l hl
    obtain ⟨x, -, rfl⟩ := List.mem_map.1 hl
    simp only [List.flatMap_cons, List.flatMap_nil, List.length_append, List.append_nil]
    split <;> split <;> simp <;> omega
  · intro x
    have hc : ∀ f : Pw → HQ S W Pw, List.map.timedCost f (fun _ => 2) s.1.1.cands ≤
        5 * s.1.1.cands.length + 1 := fun f =>
      List.map.timedCost_le f _ (k := 2) (fun _ => le_rfl) _
    simp only [List.map.timedCost, List.map_cons, List.map_nil, List.flatten.timedCost,
      List.append.timedCost_eq]
    split <;> split <;> simp only [List.length_map, List.length_nil] <;> grind

variable (G : DHGroup S W) [DecidableEq W]

/-- **The time of an answer of the passive-session reduction**, at decisions of cost at most
`tO`, products at most `tμ`, exponentiations at most `te` and public values at most `tf`. -/
theorem psTrans.timeBound_timed (O : W → W → W → Bool) (OCost : W → W → W → ℕ) (A B' : W)
    (td : Pw → Sˣ) (t : Unit) (q : HQ S W Pw) (toFunCost : S → ℕ) (mulCost : W → W → ℕ)
    (expCost : W → S → ℕ) {tO tμ te tf : ℕ} (hO : ∀ a b c, OCost a b c ≤ tO)
    (hμ : ∀ a b, mulCost a b ≤ tμ) (he : ∀ a b, expCost a b ≤ te) (hf : ∀ u, toFunCost u ≤ tf) :
    StepTimeBound (psTrans.timed G O OCost A B' td (fun _ => 0) t q toFunCost mulCost expCost)
      (20 + tO + tμ + te + 3 * tf) := by
  time_bound

/-- **The time of the output of the passive-session reduction**: a constant per input of the
simulator's tables and party, at the costs of the decisions and group operations. -/
theorem psFin.timeBound_timed (O : W → W → W → Bool) (OCost : W → W → W → ℕ) (A B' : W)
    (td : Pw → Sˣ) (s : SimSt S W Pw K × St Pw K) (toFunCost : S → ℕ) (mulCost : W → W → ℕ)
    (expCost : W → S → ℕ) {tO tμ te tf : ℕ} (hO : ∀ a b c, OCost a b c ≤ tO)
    (hμ : ∀ a b, mulCost a b ≤ tμ) (he : ∀ a b, expCost a b ≤ te) (hf : ∀ u, toFunCost u ≤ tf) :
    StepTimeBound (psFin.timed G O OCost A B' td (fun _ => 0) s (fun _ => 0) (fun _ => 0) mulCost
      toFunCost expCost)
      ((250 + 2 * tO + 12 * tμ + 12 * te + 6 * tf) * (s.1.2.length + s.1.1.h2.length) + 20 +
        tf) := by
  unfold psFin.timed
  refine ⟨?_, trivial⟩
  dsimp only
  grw [List.findSome?.timedCost_le (k := 230 + 2 * tO + 12 * tμ + 12 * te + 6 * tf)]
  · have := List.map.timedCost_le Prod.fst (fun _ => 0) (k := 0) (fun _ => le_rfl) s.1.2
    have := List.map.timedCost_le Prod.fst (fun _ => 0) (k := 0) (fun _ => le_rfl) s.1.1.h2
    have := hf 0
    rw [List.append.timedCost_eq]
    simp only [List.length_append, List.length_map]
    nlinarith
  · intro x
    simp only [List.findSome?.timedCost]
    have := sub_one_timedCost_le (p := 0) (by omega)
    have := sub_one_timedCost_le (p := 1) le_rfl
    repeat' split
    all_goals grind

end FinalTime

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

/-- The initial state of the world with handles satisfies the invariant at zero activations. -/
theorem hInit_hInv : HInv 0 (hInit G (S := S) (W := W) (Pw := Pw) (K := K)) := by
  simp [HInv, hInit, simProt, initSt]

/-- **The time of the costed double-match adversary.** For a costed oracle adversary `B` of time
`T` with at most `q` queries, exponentiations of cost at most `te` and public values of cost at
most `tf`, the costed reduction `dmAdvC` on any message has time at most
`(T + q · F q + (48 |Pw| + 80) q + 21) · (22 + te + 2 tf)`, with the step time
`F i = (6 |Pw| + 168) i + 12 |Pw| + 853 + 3 te + tf` of the world with handles: a polynomial in
`q`, `|Pw|` and `T`. -/
theorem dmAdvC.timeBound (B : OracleAdv.Timed (OEv Pw W) (OOut W K) Bool) (X : W)
    {T q te tf : ℕ} (hB : B.TimeBound T) (hq : B.erase.IsQueryBound q)
    (he : ∀ x y, expCost x y ≤ te) (hf : ∀ x, toFunCost x ≤ tf) :
    StepTimeBound (dmAdvC G expCost toFunCost B X)
      ((T + q * ((6 * Fintype.card Pw + 168) * q + 12 * Fintype.card Pw + 853 + 3 * te + tf) +
          ((48 * Fintype.card Pw + 80) * q + 21)) * (22 + te + 2 * tf)) := by
  have h := OracleAdv.stepRedO.timeBound_timed
    (hImplC G (msgDM G X) (fun pid u => msgDM.timedCost G X pid u expCost) toFunCost)
    (fun _ _ => 0) (fun s => (dmFin.timed s fun _ => 0).2) (fun s => (dmFin.timed s fun _ => 0).1)
    (fun t d => (dmTrans.timed G t d expCost toFunCost).2)
    (fun t d => (dmTrans.timed G t d expCost toFunCost).1) HInv
    (fun i => (6 * Fintype.card Pw + 168) * i + 12 * Fintype.card Pw + 853 + 3 * te + tf)
    (fun i j hij => by dsimp only; gcongr)
    (Ext := (48 * Fintype.card Pw + 80) * q + 21) (c := 21 + te + 2 * tf)
    (fun i s h => HInv.succ h)
    (fun i s e h => by
      have := hImplC.timeBound G (msgDM G X) (fun pid u => msgDM.timedCost G X pid u expCost)
        toFunCost (tm := 1 + te) (fun p u => by simp only [msgDM.timedCost]; have := he X u; omega)
        hf i s e h
      exact ⟨this.1.mono (by omega), this.2⟩)
    B hB hq
    (fun s hs => by
      obtain ⟨hn, hh, hp, -, -⟩ := hs
      have hc := hn.length_le_card
      refine (stepTimeBound_delay (c := 1) (dmFin.timeBound_timed s)).mono ?_
      have : (24 * s.1.1.cands.length + 40) * (s.1.2.length + s.1.1.h2.length) ≤
          (24 * Fintype.card Pw + 40) * (2 * q) := Nat.mul_le_mul (by omega) (by omega)
      nlinarith)
    (fun t d => (stepTimeBound_delay (c := 1) (dmTrans.timeBound_timed G expCost toFunCost t d
      he hf)).mono (by omega))
    (hInit G) () (hInit_hInv G)
  exact h.mono (by nlinarith)

/-- **The time of the costed program of the passive-session reduction.** For a costed oracle
adversary `B` of time `T` with at most `q` queries, decisions of cost at most `tO`, products at
most `tμ`, exponentiations at most `te` and public values at most `tf`, the costed program
`psProgC` has time at most `1 + (T + q · F q + E) · (22 + tO + tμ + te + 3 tf)`, with the step
time `F i = (6 |Pw| + 168) i + 12 |Pw| + 862 + 3 tμ + 4 tf` of the world with handles and the
output time `E = (500 + 4 tO + 24 tμ + 24 te + 12 tf) q + 21 + tf`: a polynomial in `q`, `|Pw|`
and `T`. -/
theorem psProgC.timeBound (B : OracleAdv.Timed (OEv Pw W) (OOut W K) Bool)
    {T q tO tμ te tf : ℕ} (hB : B.TimeBound T) (hq : B.erase.IsQueryBound q)
    (hO : ∀ a b c, OCost a b c ≤ tO) (hμ : ∀ a b, mulCost a b ≤ tμ)
    (he : ∀ x y, expCost x y ≤ te) (hf : ∀ x, toFunCost x ≤ tf) :
    StepTimeBound (psProgC G expCost mulCost toFunCost O OCost A B' B)
      (1 + (T + q * ((6 * Fintype.card Pw + 168) * q + 12 * Fintype.card Pw + 862 + 3 * tμ +
          4 * tf) + ((500 + 4 * tO + 24 * tμ + 24 * te + 12 * tf) * q + 21 + tf)) *
        (22 + tO + tμ + te + 3 * tf)) := by
  have hrun : ∀ td, StepTimeBound (psRunC G expCost mulCost toFunCost O OCost A B' B td)
      ((T + q * ((6 * Fintype.card Pw + 168) * q + 12 * Fintype.card Pw + 862 + 3 * tμ +
          4 * tf) + ((500 + 4 * tO + 24 * tμ + 24 * te + 12 * tf) * q + 21 + tf)) *
        (22 + tO + tμ + te + 3 * tf)) := fun td => by
    have h := OracleAdv.stepRedO.timeBound_timed
      (hImplC G (msgPS G A B') (fun pid u => msgPS.timedCost G A B' pid u mulCost toFunCost)
        toFunCost)
      (fun _ _ => 0)
      (fun s => (psFin.timed G O OCost A B' td (fun _ => 0) s (fun _ => 0) (fun _ => 0) mulCost
        toFunCost expCost).2)
      (fun s => (psFin.timed G O OCost A B' td (fun _ => 0) s (fun _ => 0) (fun _ => 0) mulCost
        toFunCost expCost).1)
      (fun t q => (psTrans.timed G O OCost A B' td (fun _ => 0) t q toFunCost mulCost
        expCost).2)
      (fun t q => (psTrans.timed G O OCost A B' td (fun _ => 0) t q toFunCost mulCost
        expCost).1) HInv
      (fun i => (6 * Fintype.card Pw + 168) * i + 12 * Fintype.card Pw + 862 + 3 * tμ + 4 * tf)
      (fun i j hij => by dsimp only; gcongr)
      (Ext := (500 + 4 * tO + 24 * tμ + 24 * te + 12 * tf) * q + 21 + tf)
      (c := 21 + tO + tμ + te + 3 * tf)
      (fun i s h => HInv.succ h)
      (fun i s e h => by
        have := hImplC.timeBound G (msgPS G A B')
          (fun pid u => msgPS.timedCost G A B' pid u mulCost toFunCost) toFunCost
          (tm := 4 + tμ + tf) (fun p u => by
            simp only [msgPS.timedCost]
            have := hμ (psBase A B' p) (G.pub u)
            have := hf u
            omega) hf i s e h
        exact ⟨this.1.mono (by omega), this.2⟩)
      B hB hq
      (fun s hs => by
        obtain ⟨-, hh, hp, -, -⟩ := hs
        refine (stepTimeBound_delay (c := 1) (psFin.timeBound_timed G O OCost A B' td s toFunCost
          mulCost expCost hO hμ he hf)).mono ?_
        have : (250 + 2 * tO + 12 * tμ + 12 * te + 6 * tf) * (s.1.2.length + s.1.1.h2.length) ≤
            (250 + 2 * tO + 12 * tμ + 12 * te + 6 * tf) * (2 * q) :=
          Nat.mul_le_mul_left _ (by omega)
        nlinarith)
      (fun t d => (stepTimeBound_delay (c := 1) (psTrans.timeBound_timed G O OCost A B' td t d
        toFunCost mulCost expCost hO hμ he hf)).mono (by omega))
      (hInit G) () (hInit_hInv G)
    exact h.mono (by nlinarith)
  unfold psProgC
  simp only [StepTimeBound, timeBound_rand_iff, Nat.sub_zero]
  exact ⟨Nat.zero_le _, by omega, fun td => (hrun td).mono (by omega)⟩

end Instances

section Composed

variable {S W Pw K : Type} [Field S] [Fintype S] [DecidableEq S] [DecidableEq W] [Fintype Pw]
  [DecidableEq Pw] [Fintype K] [Nonempty K] [Inhabited K] (G : DHGroup S W)
  (expCost : W → S → ℕ) (toFunCost : S → ℕ)

section SSDH

variable [Inhabited Pw]

/-- **The costed strong SDH reduction of the double-match adversary**: `ssdhReduction.timed` at
the costed match-recording reduction `matchWrap.timed` of the costed double-match adversary
`dmAdvC`, a lookup of the generator table costing `HCost`. -/
noncomputable def ssdhDmC (HCost : Pw → ℕ) (B : OracleAdv.Timed (OEv Pw W) (OOut W K) Bool)
    (X gen₁ gen₂ : W) : ℕ × OracleAdv.Timed (Bool × W × W) Bool (W × W × W) :=
  ssdhReduction.timed G
    (fun X H => (CPaceH1.matchWrap.timed (fun X => (dmAdvC G expCost toFunCost B X).2)
      (fun X => (dmAdvC G expCost toFunCost B X).1) X H HCost).2)
    (fun X H => (CPaceH1.matchWrap.timed (fun X => (dmAdvC G expCost toFunCost B X).2)
      (fun X => (dmAdvC G expCost toFunCost B X).1) X H HCost).1) X gen₁ gen₂ expCost

/-- The costed strong SDH reduction of the double-match adversary erases to the reduction
`ssdhReduction G (matchWrap (dmAdv G B))` of the concrete bound `cpaceConcreteBound`. -/
theorem ssdhDmC_erase (HCost : Pw → ℕ) (B : OracleAdv.Timed (OEv Pw W) (OOut W K) Bool)
    (X gen₁ gen₂ : W) :
    (ssdhDmC G expCost toFunCost HCost B X gen₁ gen₂).2.erase =
      ssdhReduction G (CPaceH1.matchWrap (dmAdv G B.erase)) X gen₁ gen₂ := by
  simp only [ssdhDmC, ssdhReduction.erase_timed, CPaceH1.matchWrap.erase_timed, dmAdvC_erase]

/-- **The time of the strong SDH reduction of the double-match adversary.** For a costed oracle
adversary `B` of time `T` with at most `q` queries, exponentiations of cost at most `te`, public
values of cost at most `tf` and lookups of the generator table of cost at most `h`, the costed
reduction `ssdhDmC` erases to `ssdhReduction G (matchWrap (dmAdv G B))` and has time at most
`(h + 18) (te + 6) (D + 1)² + 2 te + 10`, where
`D = (T + q · ((6 |Pw| + 168) q + 12 |Pw| + 853 + 3 te + tf) + (48 |Pw| + 80) q + 21)
(22 + te + 2 tf)` is the time of `dmAdvC` (`dmAdvC.timeBound`): a polynomial in `q`, `|Pw|`
and `T`. The time `D` bounds the number of queries of the double-match adversary, so the search
of the match log by `matchWrap` (`matchWrap.timeBound_timed`) is quadratic in `D`, and each
match query costs one exponentiation in `ssdhReduction` (`ssdhReduction.timeBound_timed`). -/
theorem ssdhDmC.timeBound (HCost : Pw → ℕ) (B : OracleAdv.Timed (OEv Pw W) (OOut W K) Bool)
    (X gen₁ gen₂ : W) {T q te tf h : ℕ} (hB : B.TimeBound T) (hq : B.erase.IsQueryBound q)
    (he : ∀ x y, expCost x y ≤ te) (hf : ∀ x, toFunCost x ≤ tf) (hH : ∀ pw, HCost pw ≤ h) :
    (ssdhDmC G expCost toFunCost HCost B X gen₁ gen₂).2.erase =
        ssdhReduction G (CPaceH1.matchWrap (dmAdv G B.erase)) X gen₁ gen₂ ∧
      StepTimeBound (ssdhDmC G expCost toFunCost HCost B X gen₁ gen₂)
        ((h + 18) * (te + 6) * ((T + q * ((6 * Fintype.card Pw + 168) * q +
          12 * Fintype.card Pw + 853 + 3 * te + tf) + ((48 * Fintype.card Pw + 80) * q + 21)) *
            (22 + te + 2 * tf) + 1) ^ 2 + 2 * te + 10) := by
  refine ⟨ssdhDmC_erase G expCost toFunCost HCost B X gen₁ gen₂, ?_⟩
  refine (?_ : ∀ D, (∀ X, StepTimeBound (dmAdvC G expCost toFunCost B X) D) →
      StepTimeBound (ssdhDmC G expCost toFunCost HCost B X gen₁ gen₂)
        ((h + 18) * (te + 6) * (D + 1) ^ 2 + 2 * te + 10)) _
    fun X => dmAdvC.timeBound G expCost toFunCost B X hB hq he hf
  intro D hdm
  have hA : ∀ X, (dmAdvC G expCost toFunCost B X).2.TimeBound D :=
    fun X => (hdm X).2.mono (Nat.sub_le _ _)
  have hmw := fun X H => CPaceH1.matchWrap.timeBound_timed
    (fun X => (dmAdvC G expCost toFunCost B X).2) (fun X => (dmAdvC G expCost toFunCost B X).1)
    X H HCost hA (fun X => isQueryBound_of_timeBound (hA X)) (fun X => (hdm X).1) hH
  have hM := fun X H => (hmw X H).2.mono (Nat.sub_le _ _)
  have hs := ssdhReduction.timeBound_timed G
    (fun X H => (CPaceH1.matchWrap.timed (fun X => (dmAdvC G expCost toFunCost B X).2)
      (fun X => (dmAdvC G expCost toFunCost B X).1) X H HCost).2)
    (fun X H => (CPaceH1.matchWrap.timed (fun X => (dmAdvC G expCost toFunCost B X).2)
      (fun X => (dmAdvC G expCost toFunCost B X).1) X H HCost).1) X gen₁ gen₂ expCost
    hM (fun X H => isQueryBound_of_timeBound (hM X H)) (fun X H => (hmw X H).1) he
  refine hs.mono ?_
  have hD : 1 + D + (D + D * (h + 4)) + 12 * (D + 1) * (D + 1) ≤ (h + 18) * (D + 1) ^ 2 :=
    calc _ ≤ 1 + D + (D + D * (h + 4)) + 12 * (D + 1) * (D + 1) +
          (h * D * D + h * D + h + 6 * D * D + 6 * D + 5) := Nat.le_add_right _ _
      _ = _ := by ring
  calc _ = (1 + D + (D + D * (h + 4)) + 12 * (D + 1) * (D + 1)) * (te + 6) + 2 * te + 10 := by
        ring
    _ ≤ (h + 18) * (D + 1) ^ 2 * (te + 6) + 2 * te + 10 := by gcongr
    _ = _ := by ring

end SSDH

variable (mulCost : W → W → ℕ) (OCost : W → W → W → ℕ)

/-- **The costed gap Diffie–Hellman adversary for passive sessions**: on the decision oracle `O`
and the challenge `(A, B')`, the costed program `psProgC` at `O`, a call of the decision oracle
costing `OCost`. The gap Diffie–Hellman game runs it at its decision oracle `ddhOracle`. -/
noncomputable def psAdvC (B : OracleAdv.Timed (OEv Pw W) (OOut W K) Bool)
    (O : W → W → W → Bool) (A B' : W) : ℕ × OracleAdv.Timed Empty Empty W :=
  psProgC G expCost mulCost toFunCost O OCost A B' B

variable [SampleableType W]

/-- The costed gap Diffie–Hellman adversary for passive sessions erases to `psAdv G B`, the
reduction of the concrete bound `cpaceConcreteBound`: on every decision oracle and challenge,
`psAdv G B` is the lift of the output of the run of the erased program. -/
theorem psAdvC_erase (B : OracleAdv.Timed (OEv Pw W) (OOut W K) Bool) (O : W → W → W → Bool)
    (A B' : W) :
    liftPMF ((OracleAdv.run (fun (_ : Unit) (q : Empty) => q.elim)
        (psAdvC G expCost toFunCost mulCost OCost B O A B').2.erase ()).map Prod.fst) =
      psAdv G B.erase O A B' := by
  rw [psAdv, psAdvC, psProgC_erase, psOut_eq]

/-- **The time of the gap Diffie–Hellman adversary for passive sessions.** For a costed oracle
adversary `B` of time `T` with at most `q` queries, decisions of cost at most `tO`, products at
most `tμ`, exponentiations at most `te` and public values at most `tf`, on every decision oracle
`O` and challenge `(A, B')` the costed adversary `psAdvC` erases to `psAdv G B` and has time at
most `1 + (T + q · F q + E) · (22 + tO + tμ + te + 3 tf)`, with
`F i = (6 |Pw| + 168) i + 12 |Pw| + 862 + 3 tμ + 4 tf` and
`E = (500 + 4 tO + 24 tμ + 24 te + 12 tf) q + 21 + tf` (`psProgC.timeBound`): a polynomial in
`q`, `|Pw|` and `T`. -/
theorem psAdvC.timeBound (B : OracleAdv.Timed (OEv Pw W) (OOut W K) Bool)
    (O : W → W → W → Bool) (A B' : W) {T q tO tμ te tf : ℕ} (hB : B.TimeBound T)
    (hq : B.erase.IsQueryBound q) (hO : ∀ a b c, OCost a b c ≤ tO)
    (hμ : ∀ a b, mulCost a b ≤ tμ) (he : ∀ x y, expCost x y ≤ te) (hf : ∀ x, toFunCost x ≤ tf) :
    liftPMF ((OracleAdv.run (fun (_ : Unit) (q : Empty) => q.elim)
        (psAdvC G expCost toFunCost mulCost OCost B O A B').2.erase ()).map Prod.fst) =
        psAdv G B.erase O A B' ∧
      StepTimeBound (psAdvC G expCost toFunCost mulCost OCost B O A B')
        (1 + (T + q * ((6 * Fintype.card Pw + 168) * q + 12 * Fintype.card Pw + 862 + 3 * tμ +
            4 * tf) + ((500 + 4 * tO + 24 * tμ + 24 * te + 12 * tf) * q + 21 + tf)) *
          (22 + tO + tμ + te + 3 * tf)) :=
  ⟨psAdvC_erase G expCost toFunCost mulCost OCost B O A B',
    psProgC.timeBound G expCost mulCost toFunCost O OCost A B' B hB hq hO hμ he hf⟩

end Composed

end CatCrypt.Crypto.PAKE.CPaceBadReductions
