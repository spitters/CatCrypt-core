/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.PQXDHSquareKEM
public import CatCryptCore.Crypto.AKE.X3DHSquareGDHTimed
public import CatCryptCore.Tactics.DeriveReduction

/-!
# Running time of the KEM reduction of the PQXDH square

The IND-CCA reduction `kemRed P G g B` of `PQXDHSquareKEM.lean` is the stepped oracle program
`stepRedQ` at the query decision `needQ` (a decapsulation query on each delivered encapsulation
other than the challenge), the draws of the simulated world, the step `kemStep` of the world of
the reduction and the extraction of the membership of the key in the received shared secrets.
`stepRedQ` is the program `X3DHSquareGDH.stepRedD` with one oracle query per step.

**The costed reduction.** `derive_timed stepImplQ` and `derive_timed stepRedQ` define the costed
forms `stepImplQ.timed` (the answer to one query: a query node, a draw node and the step, with
the costs of the query decision, the draw distribution and the step as companions) and
`stepRedQ.timed`, generic in the state, the decision, the draw distribution, the step and the
extraction, with their erasure theorems.

**The time.** `stepRedQ.timeBound_timed`: under a state invariant `Inv i` with the costs of the
decision, the draw and the step at most `F i` and the extraction at most `Ext i`, an adversary of
time `T` with at most `q` queries gives a reduction of time at most `T + q · (F q + 7) + Ext q + 1`.
A step of the world of the reduction adds at most two to the size of its state, the lengths of its
key-derivation table, its notices and its received shared secrets (`simStartD_size`,
`sizeY_kemStep`), so that for costs bounded by monotone functions `F`, `Ext` of the size the
reduction runs in time at most `T + q · (F (2q) + 7) + Ext (2q) + 1` (`kemRed_timeBound`), the time
of the adversary plus a polynomial in its queries for polynomial `F` and `Ext`. The costs of the
step and the extraction are companions bounded by hypothesis: the step programs of the world of
the reduction are not derived here.

**The certificates.** `kemRedRun.tree` is `stepRedQ` at the query decision `needQ`, with the
draws, the step and the extraction as parameters over a state type `σ`, so that `derive_timed`
gives the costed form `kemRedRun.tree.timed` with cost companions of the parameters;
`kemRedRun.compile_tree` erases it, at the draws of the simulated world, the step `kemStep` and
the membership of the key, to `kemRedRun`, and `kemRedRun.timeBound_timed` gives its time from
`kemRed_timeBound`. The IND-CCA adversary `kemRed` is certified as a structure-valued reduction:
`derive_timed_structure` gives the costed mirror `KEM.Games.INDCCAAdversary.Timed`, the
structure `kemRed.tree` bundles `kemRedRun.tree` with its query bound, `derive_reduction` gives
`kemRed.tree.timed` and its erasure, `kemRed.compile_tree` erases it to `kemRed`, and
`kemRed.timeBound_timed` bounds its stage.

`derive_timed kemRedRun` refuses the program of `kemRed` with the step `kemStep` unfolded:

    derive_timed: a function bound in data: the field `Prod.fst` is applied in
    `t.1.1.2.1 (x.1, r.peer)`

(the table of recorded inputs of the state, applied in the delivery `deliverD`). The
restatement over a parameter `step` with a cost companion avoids it; at a concrete state type
the initial state `yInit` is priced as a costed value while `stepRedQ.timed` takes a plain
state, so the state type is a parameter of the tree as well.

No module imports this file.

## Main results

* `stepImplQ.timed`, `stepRedQ.timed`, `stepRedQ.erase_timed` (derived): the costed forms.
* `stepRedQ.timeBound_timed`: the time of the costed stepped program with queries.
* `simStartD_size`, `sizeY_kemStep`: a step adds at most two to the size of the state.
* `kemRed_erase_timed`, `kemRed_timeBound`: the erasure of the costed reduction to the program
  of `kemRed` and its time.
* `kemRedRun.tree`, `kemRedRun.tree.timed`, `kemRedRun.compile_tree`, `kemRedRun.timeBound_timed`:
  the certificate of `kemRedRun`.
* `kemRed.tree`, `kemRed.tree.timed`, `kemRed.compile_tree`, `kemRed.timeBound_timed`: the
  certificate of `kemRed`.

## References

* K. Bhargavan, C. Jacomme, F. Kiefer, R. Schmidt, *Formal verification of the PQXDH
  post-quantum key agreement protocol for end-to-end secure messaging*, USENIX Security 2024.
* D. Hofheinz, K. Hövelmanns, E. Kiltz, *A Modular Analysis of the Fujisaki–Okamoto
  Transformation*, TCC 2017.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.KEM.Games

derive_timed_structure INDCCAAdversary

end CatCrypt.Crypto.KEM.Games

namespace CatCrypt.Crypto.AKE.PQXDHSquareKEM

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto

derive_timed stepImplQ

derive_timed stepRedQ


section Generic

variable {σ E A V Q Ans Out : Type}

/-- **The time of `stepRedQ`.** Let `Inv i` hold of the states reached after `i` steps, with the
costs of the query decision, of the draw distribution and of a step from a state of `Inv i`
together at most `F i` (`F` monotone), and an extraction from a state of `Inv i` of cost at most
`Ext i`. Then a costed adversary `B` of time `T` with at most `q` queries gives a costed reduction
of time at most `T + q · (F q + 7) + Ext q + 1`. -/
theorem stepRedQ.timeBound_timed (need : σ → E → Option Q) (needCost : σ → E → ℕ)
    (μ : σ → E → PMF V) (μCost : σ → E → ℕ) (step : Option Ans → σ → E → V → σ × A)
    (stepCost : Option Ans → σ → E → V → ℕ) (ext : σ → Out) (extCost : σ → ℕ)
    (Inv : ℕ → σ → Prop) (F Ext : ℕ → ℕ) (hF : Monotone F)
    (hmono : ∀ i t, Inv i t → Inv (i + 1) t)
    (hstep : ∀ i t e oa r, Inv i t → Inv (i + 1) (step oa t e r).1)
    (hcost : ∀ i t e oa r, Inv i t → needCost t e + μCost t e + stepCost oa t e r ≤ F i)
    (hext : ∀ i t, Inv i t → extCost t ≤ Ext i)
    (B : OracleAdv.Timed E A Bool) {T q : ℕ} (hB : B.TimeBound T) (hq : B.erase.IsQueryBound q)
    (s₀ : σ) (h0 : Inv 0 s₀) :
    OracleAdv.Timed.StepTimeBound
      (stepRedQ.timed need needCost μ μCost step stepCost ext extCost B s₀)
      (T + q * (F q + 7) + (Ext q + 1)) := by
  unfold stepRedQ.timed
  generalize hI : (fun (t : σ) (e : E) => OracleAdv.Timed.delay 1
    (stepImplQ.timed need needCost μ μCost step stepCost t e)) = impl
  have himpl : ∀ i s d, Inv i s →
      OracleAdv.Timed.StepTimeBound (impl s d) (F i + 7) ∧
        OracleAdv.Timed.AllRet (fun y => Inv (i + 1) y.2) (impl s d).2 := by
    intro i s d hs
    subst hI
    obtain ⟨r₀, -⟩ := (μ s d).support_nonempty
    have h₀ := hcost i s d none r₀ hs
    simp only [stepImplQ.timed, OracleAdv.Timed.delay]
    cases hn : need s d with
    | some c =>
      dsimp only
      refine ⟨⟨?_, ?_, fun a => ⟨?_, ?_, fun r => ⟨?_, trivial⟩⟩⟩, fun a r => hstep i s d _ r hs⟩
      · dsimp only; omega
      · dsimp only; omega
      · dsimp only; omega
      · dsimp only; omega
      · have := hcost i s d (some a) r hs
        dsimp only; omega
    | none =>
      dsimp only
      refine ⟨⟨?_, ?_, fun r => ⟨?_, trivial⟩⟩, fun r => hstep i s d _ r hs⟩
      · dsimp only; omega
      · dsimp only; omega
      · have := hcost i s d none r hs
        dsimp only; omega
  have hsim := OracleAdv.Timed.timeBound_simulateHat_inv id id impl Inv (fun i => F i + 7) himpl
    hB hq 0 s₀ h0
  have hall := OracleAdv.Timed.allRet_simulateHat_inv id id impl Inv
    (fun i s d h => (himpl i s d h).2) hmono hq 0 s₀ h0
  unfold OracleAdv.Timed.simulateHat at hsim hall
  simp only [Nat.zero_add] at hsim hall
  have hsum : ∑ j ∈ Finset.range q, (F j + 7) ≤ q * (F q + 7) := by
    calc ∑ j ∈ Finset.range q, (F j + 7) ≤ ∑ _j ∈ Finset.range q, (F q + 7) :=
          Finset.sum_le_sum fun j hj => by
            have := hF (le_of_lt (Finset.mem_range.mp hj)); omega
      _ = q * (F q + 7) := by rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have hbind := OracleAdv.Timed.timeBound_bind_of_allRet (n := Ext q + 1)
    (f := fun p => (1 + extCost p.2, OracleAdv.Timed.ret (ext p.2))) hsim.2 hall
    fun y hy => ⟨by have := hext q y.2 hy; dsimp only; omega, trivial⟩
  refine (OracleAdv.Timed.stepTimeBound_delay hbind).mono ?_
  have := hsim.1
  omega

end Generic

/-! ## The size of the world of the reduction -/

section Size

open CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.PAKE.DHExtract
open CatCrypt.Crypto.AKE.X3DHSquareHops (Draw ltD ltD_st pollStep_fst)
open CatCrypt.Crypto.OracleGameUpToBad (roDet)
open CatCrypt.Crypto.AKE.PQXDHSquare CatCrypt.Crypto.AKE.PQXDHSquareHops
open CatCrypt.Crypto.KEM.Games (Scheme)

variable {S W K PK SK SS C : Type} [Field S] [Fintype S] [DecidableEq W] [Fintype K]
  [Nonempty K] [Inhabited K] [DecidableEq SS] (P : Scheme PK SK SS C) (G : DHGroup S W)

omit [Field S] [Fintype S] [Fintype K] [Nonempty K] in
theorem deliverD_size (s : PSt S W K PK SK SS C) (inp : Inst → Option (PInp W SS)) (x : Inst)
    (r : Rec K) (ip : PInp W SS) (k : K) :
    (PQXDHSquareHops.deliverD s inp x r ip k).1.1.ro.length ≤ s.ro.length + 1 ∧
      (PQXDHSquareHops.deliverD s inp x r ip k).1.1.x.st.notices = s.x.st.notices := by
  unfold PQXDHSquareHops.deliverD
  split
  · refine ⟨?_, rfl⟩
    simp only [pKeyed]
    unfold roDet
    split <;> simp
  · exact ⟨by simp [pKeyed], rfl⟩

omit [Field S] [Fintype S] [Fintype K] [Nonempty K] in
theorem deliverD_size' (s s' : PSt S W K PK SK SS C) (hro : s'.ro = s.ro)
    (hn : s'.x.st.notices = s.x.st.notices) (inp : Inst → Option (PInp W SS)) (x : Inst)
    (r : Rec K) (ip : PInp W SS) (k : K) :
    (PQXDHSquareHops.deliverD s' inp x r ip k).1.1.ro.length +
        (PQXDHSquareHops.deliverD s' inp x r ip k).1.1.x.st.notices.length ≤
      s.ro.length + s.x.st.notices.length + 1 := by
  have h := deliverD_size s' inp x r ip k
  rw [h.2, hn, ← hro]
  omega

omit [Fintype S] [Fintype K] [Nonempty K] in
/-- **A start of the simulator adds at most one entry** to the key-derivation table and the list
of notices together. -/
theorem simStartD_size (s : SimSt S W K PK SK SS C) (e : OEv W SS C)
    (d : PDraw S K PK SK SS C) :
    (simStartD P G s e d).1.1.ro.length + (simStartD P G s e d).1.1.x.st.notices.length ≤
      s.1.ro.length + s.1.x.st.notices.length + 1 := by
  rcases e with (⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) | (_ | _ | pid | ⟨sid, pid⟩ |
    ⟨sid, pid⟩ | pid | ⟨sid, pid⟩ | ⟨sid, pid, e, c⟩ | q)
  · simp only [simStartD]
    have h : (addSession s.1.x.st (sid, pid) peer role).notices.length ≤
        s.1.x.st.notices.length + 1 := by
      unfold addSession; split <;> simp
    split
    · split <;> (dsimp only; omega)
    · dsimp only; omega
  · dsimp only [simStartD]; omega
  · dsimp only [simStartD]; omega
  · dsimp only [simStartD]; rw [(pollStep_fst _).2.2]; omega
  · dsimp only [simStartD]; rw [ltD_st]; omega
  · dsimp only [simStartD]; omega
  · dsimp only [simStartD]; omega
  · simp only [simStartD]
    split
    · dsimp only; omega
    · dsimp only [corruptStep]; rw [ltD_st]; omega
  · simp only [simStartD, simCompleteD]
    repeat' split
    all_goals first
      | (dsimp only; omega)
      | (refine deliverD_size' s.1 _ ?_ ?_ _ _ _ _ _
         · rfl
         · simp only [ltD_st])
  · simp only [simStartD, simSendD]
    repeat' split
    all_goals first
      | (dsimp only; omega)
      | (refine deliverD_size' s.1 _ ?_ ?_ _ _ _ _ _
         · rfl
         · simp only [ltD_st])
  · simp only [simStartD]
    unfold roDet
    split <;> (simp only [List.length_cons]; omega)

end Size

/-! ## The time of the KEM reduction -/

section Instance

open CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.PAKE.DHExtract
open CatCrypt.Crypto.AKE.PQXDHSquare CatCrypt.Crypto.AKE.PQXDHSquareHops
open CatCrypt.Crypto.KEM.Games (Scheme)

variable {S W K PK SK SS C : Type} [Field S] [Fintype S] [SampleableType W] [Fintype K]
  [Nonempty K] [Inhabited K] [DecidableEq SS] [DecidableEq C] (P : Scheme PK SK SS C)
  (G : DHGroup S W) (g : Guess)

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K]
  [DecidableEq SS] [DecidableEq C] in
/-- The size of a state of the world of the reduction: the lengths of its key-derivation table,
of its list of notices and of its list of concrete shared secrets. -/
def sizeY (t : YSt S W K PK SK SS C) : ℕ :=
  t.1.1.1.ro.length + t.1.1.1.x.st.notices.length + t.2.length

omit [Fintype S] [Fintype K] [Nonempty K] in
/-- A step of the world of the reduction adds at most two to its size. -/
theorem sizeY_kemStep (pk : PK) (cs : C) (oa : Option (Option SS)) (t : YSt S W K PK SK SS C)
    (e : OEv W SS C) (r : PDraw S K PK SK SS C × K) :
    sizeY (kemStep P G g pk cs oa t e r).1 ≤ sizeY t + 2 := by
  have h := simStartD_size (symP P cs (fun _ => oa.getD none)) G t.1.1 (liftE e)
    (liftD g pk cs t.1.1 e r).1
  have hv : (newVal P cs (fun _ => oa.getD none) t.1.1 e r).toList.length ≤ 1 := by
    cases newVal P cs (fun _ => oa.getD none) t.1.1 e r <;> simp
  simp only [sizeY, kemStep, yStep, simWorldD_fst, List.length_append]
  omega

/-- **Erasure of the costed KEM reduction**: the derived costed form of `stepRedQ` at the query
decision `needQ`, the draws of the simulated world, the step `kemStep` and the extraction of
the membership of the key `k`, with any cost companions, erases to the program `kemRedRun` of
the IND-CCA reduction `kemRed`. -/
theorem kemRed_erase_timed (pk : PK) (cs : C) (k : SS) (needCost : YSt S W K PK SK SS C →
    OEv W SS C → ℕ) (μCost : YSt S W K PK SK SS C → OEv W SS C → ℕ)
    (stepCost : Option (Option SS) → YSt S W K PK SK SS C → OEv W SS C →
      PDraw S K PK SK SS C × K → ℕ) (extCost : YSt S W K PK SK SS C → ℕ)
    (B : OracleAdv.Timed (OEv W SS C) (OOut S W K PK C) Bool) :
    (stepRedQ.timed (fun _ e => needQ cs e) needCost
        (fun t e => simDist P (encPk t.1.1.1 (liftE e))) μCost (kemStep P G g pk cs) stepCost
        (fun t => decide (k ∈ t.2)) extCost B yInit).2.erase =
      kemRedRun P G g B.erase pk cs k :=
  stepRedQ.erase_timed _ _ _ _ _ _ _ _ B yInit

/-- **The time of the KEM reduction.** Let the costs of the query decision, of the draw and of
a step from a state of size `n` together be at most `F n`, and the cost of the extraction at
most `Ext n`, with `F` and `Ext` monotone. Then for a costed oracle adversary `B` of time `T`
with at most `q` queries, the costed reduction, whose erasure is the program of `kemRed`, runs
in time at most `T + q · (F (2q) + 7) + Ext (2q) + 1`: a step adds at most two to the size of
the state. -/
theorem kemRed_timeBound (pk : PK) (cs : C) (k : SS) (needCost : YSt S W K PK SK SS C →
    OEv W SS C → ℕ) (μCost : YSt S W K PK SK SS C → OEv W SS C → ℕ)
    (stepCost : Option (Option SS) → YSt S W K PK SK SS C → OEv W SS C →
      PDraw S K PK SK SS C × K → ℕ) (extCost : YSt S W K PK SK SS C → ℕ) (F Ext : ℕ → ℕ)
    (hF : Monotone F) (hE : Monotone Ext)
    (hcost : ∀ t e oa r, needCost t e + μCost t e + stepCost oa t e r ≤ F (sizeY t))
    (hext : ∀ t, extCost t ≤ Ext (sizeY t))
    (B : OracleAdv.Timed (OEv W SS C) (OOut S W K PK C) Bool) {T q : ℕ} (hB : B.TimeBound T)
    (hq : B.erase.IsQueryBound q) :
    OracleAdv.Timed.StepTimeBound
      (stepRedQ.timed (fun _ e => needQ cs e) needCost
        (fun t e => simDist P (encPk t.1.1.1 (liftE e))) μCost (kemStep P G g pk cs) stepCost
        (fun t => decide (k ∈ t.2)) extCost B yInit)
      (T + q * (F (2 * q) + 7) + (Ext (2 * q) + 1)) :=
  stepRedQ.timeBound_timed _ _ _ _ _ _ _ _ (fun i t => sizeY t ≤ 2 * i) (fun i => F (2 * i))
    (fun i => Ext (2 * i)) (fun _ _ h => hF (by omega)) (fun _ _ h => by omega)
    (fun i t e oa r h => by have := sizeY_kemStep P G g pk cs oa t e r; omega)
    (fun i t e oa r h => (hcost t e oa r).trans (hF h))
    (fun i t h => (hext t).trans (hE h)) B hB hq yInit
    (by simp [sizeY, yInit, pInit, X3DHSquare.rInit, initSt])

end Instance

/-! ## The certificates of the KEM reduction -/

section Certificate

open CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.PAKE.DHExtract
open CatCrypt.Crypto.AKE.PQXDHSquare CatCrypt.Crypto.AKE.PQXDHSquareHops
open CatCrypt.Crypto.KEM.Games (Scheme)

/-- **The tree of the program of the KEM reduction**: the stepped oracle program `stepRedQ` at
the query decision `needQ cs` (a decapsulation query on each delivered encapsulation other than
the challenge `cs`), with the draw distribution `μ`, the step `step pk cs`, the extraction
`ext k` and the initial state `s₀` as parameters. -/
noncomputable def kemRedRun.tree {σ V PK SS C A : Type} [DecidableEq C] {W : Type}
    (μ : σ → OEv W SS C → PMF V) (step : PK → C → Option (Option SS) → σ → OEv W SS C → V → σ × A)
    (ext : SS → σ → Bool) (s₀ : σ) (B : OracleAdv (OEv W SS C) A Bool) (pk : PK) (cs : C)
    (k : SS) : OracleAdv C (Option SS) Bool :=
  stepRedQ (fun _ e => needQ cs e) μ (step pk cs) (ext k) B s₀

derive_timed kemRedRun.tree

/-- The tree asks at most as many decapsulation queries as the adversary asks queries. -/
theorem kemRedRun.tree_isQueryBound {σ V PK SS C A : Type} [DecidableEq C] {W : Type}
    (μ : σ → OEv W SS C → PMF V) (step : PK → C → Option (Option SS) → σ → OEv W SS C → V → σ × A)
    (ext : SS → σ → Bool) (s₀ : σ) {q : ℕ}
    (B : {B : OracleAdv (OEv W SS C) A Bool // B.IsQueryBound q}) (pk : PK) (cs : C) (k : SS) :
    (kemRedRun.tree μ step ext s₀ B.1 pk cs k).IsQueryBound q := by
  have h := OracleAdv.isQueryBound_simulate_mul (c := 1)
    (impl := stepImplQ (fun _ e => needQ cs e) μ (step pk cs))
    (fun t e => by
      unfold stepImplQ
      split
      · exact fun _ _ => trivial
      · exact fun _ => trivial) B.2 s₀
  rw [Nat.mul_one] at h
  have h' := OracleAdv.isQueryBound_bind (n := 0)
    (f := fun x => OracleAdv.ret (ext k x.2)) h fun _ => trivial
  rw [Nat.add_zero] at h'
  exact h'

/-- **The tree of the IND-CCA reduction**: the tree `kemRedRun.tree` of the program with its
query bound, for an adversary bundled with its query bound. -/
noncomputable def kemRed.tree {σ V PK SS C A : Type} [DecidableEq C] {W : Type}
    (μ : σ → OEv W SS C → PMF V) (step : PK → C → Option (Option SS) → σ → OEv W SS C → V → σ × A)
    (ext : SS → σ → Bool) (s₀ : σ) {q : ℕ}
    (B : {B : OracleAdv (OEv W SS C) A Bool // B.IsQueryBound q}) :
    KEM.Games.INDCCAAdversary PK SS C q :=
  ⟨kemRedRun.tree μ step ext s₀ B.1, kemRedRun.tree_isQueryBound μ step ext s₀ B⟩

derive_reduction kemRed.tree

variable {S W K PK SK SS C : Type} [Field S] [Fintype S] [SampleableType W] [Fintype K]
  [Nonempty K] [Inhabited K] [DecidableEq SS] [DecidableEq C] (P : Scheme PK SK SS C)
  (G : DHGroup S W) (g : Guess)

/-- **The costed tree of the program erases to `kemRedRun`** at the draws of the simulated
world, the step `kemStep`, the membership of the key in the received shared secrets and the
initial state `yInit`, for any cost companions. -/
theorem kemRedRun.compile_tree (μCost : YSt S W K PK SK SS C → OEv W SS C → ℕ)
    (stepCost : PK → C → Option (Option SS) → YSt S W K PK SK SS C → OEv W SS C →
      PDraw S K PK SK SS C × K → ℕ) (extCost : SS → YSt S W K PK SK SS C → ℕ)
    (B : OracleAdv.Timed (OEv W SS C) (OOut S W K PK C) Bool) (pk : PK) (cs : C) (k : SS) :
    (kemRedRun.tree.timed (fun t e => simDist P (encPk t.1.1.1 (liftE e))) μCost
        (kemStep P G g) stepCost (fun k t => decide (k ∈ t.2)) extCost yInit B pk cs k).2.erase =
      kemRedRun P G g B.erase pk cs k :=
  kemRedRun.tree.erase_timed _ _ _ _ _ _ _ B pk cs k

/-- **Time of the program of the KEM reduction.** With the costs of the draw and of a step from a
state of size `n` together at most `F n` and the cost of the extraction at most `Ext n`, `F` and
`Ext` monotone, a costed oracle adversary `B` of time `T` with at most `q` queries gives the
costed tree of `kemRedRun` a time of at most `1 + (T + q · (F (2q) + 11) + Ext (2q) + 2)`. -/
theorem kemRedRun.timeBound_timed (pk : PK) (cs : C) (k : SS)
    (μCost : YSt S W K PK SK SS C → OEv W SS C → ℕ)
    (stepCost : PK → C → Option (Option SS) → YSt S W K PK SK SS C → OEv W SS C →
      PDraw S K PK SK SS C × K → ℕ) (extCost : SS → YSt S W K PK SK SS C → ℕ) (F Ext : ℕ → ℕ)
    (hF : Monotone F) (hE : Monotone Ext)
    (hcost : ∀ t e oa r, μCost t e + stepCost pk cs oa t e r ≤ F (sizeY t))
    (hext : ∀ t, extCost k t ≤ Ext (sizeY t))
    (B : OracleAdv.Timed (OEv W SS C) (OOut S W K PK C) Bool) {T q : ℕ} (hB : B.TimeBound T)
    (hq : B.erase.IsQueryBound q) :
    OracleAdv.Timed.StepTimeBound
      (kemRedRun.tree.timed (fun t e => simDist P (encPk t.1.1.1 (liftE e))) μCost
        (kemStep P G g) stepCost (fun k t => decide (k ∈ t.2)) extCost yInit B pk cs k)
      (1 + (T + q * (F (2 * q) + 11) + (Ext (2 * q) + 2))) := by
  unfold kemRedRun.tree.timed
  refine (OracleAdv.Timed.stepTimeBound_delay (kemRed_timeBound P G g pk cs k _ μCost
    (fun oa t e r => 1 + stepCost pk cs oa t e r) (fun t => 1 + extCost k t) (fun n => F n + 4)
    (fun n => Ext n + 1) (fun _ _ h => Nat.add_le_add_right (hF h) _)
    (fun _ _ h => Nat.add_le_add_right (hE h) _) ?_ ?_ B hB hq)).mono ?_
  · intro t e oa r
    have := hcost t e oa r
    split <;> omega
  · intro t
    have := hext t
    omega
  have : F (2 * q) + 4 + 7 = F (2 * q) + 11 := by omega
  rw [this]

/-- **The costed IND-CCA reduction erases to `kemRed`**: at a costed adversary `B'` erasing to
`B`, the derived costed form of `kemRed.tree` erases to `kemRed P G g B hB`. -/
theorem kemRed.compile_tree (μCost : YSt S W K PK SK SS C → OEv W SS C → ℕ)
    (stepCost : PK → C → Option (Option SS) → YSt S W K PK SK SS C → OEv W SS C →
      PDraw S K PK SK SS C × K → ℕ) (extCost : SS → YSt S W K PK SK SS C → ℕ)
    (B : OracleAdv (OEv W SS C) (OOut S W K PK C) Bool) {q : ℕ} (hB : B.IsQueryBound q)
    (B' : OracleAdv.Timed (OEv W SS C) (OOut S W K PK C) Bool) (hB' : B'.erase = B) :
    (kemRed.tree.timed (fun t e => simDist P (encPk t.1.1.1 (liftE e))) μCost
        (kemStep P G g) stepCost (fun k t => decide (k ∈ t.2)) extCost yInit
        ⟨B, hB⟩ B').Erases (kemRed P G g B hB) :=
  kemRed.tree.erase_timed _ _ _ _ _ _ _ _ _ hB'

/-- **Time of the IND-CCA reduction**: under the cost bounds of `kemRedRun.timeBound_timed`
for every public key and challenge, the stage of the costed reduction takes at most
`2 + (T + q · (F (2q) + 11) + Ext (2q) + 2)` for a costed adversary of time `T` erasing to an
adversary with at most `q` queries. -/
theorem kemRed.timeBound_timed (μCost : YSt S W K PK SK SS C → OEv W SS C → ℕ)
    (stepCost : PK → C → Option (Option SS) → YSt S W K PK SK SS C → OEv W SS C →
      PDraw S K PK SK SS C × K → ℕ) (extCost : SS → YSt S W K PK SK SS C → ℕ) (F Ext : ℕ → ℕ)
    (hF : Monotone F) (hE : Monotone Ext)
    (hcost : ∀ pk cs t e oa r, μCost t e + stepCost pk cs oa t e r ≤ F (sizeY t))
    (hext : ∀ k t, extCost k t ≤ Ext (sizeY t))
    (B : OracleAdv (OEv W SS C) (OOut S W K PK C) Bool) {q : ℕ} (hB : B.IsQueryBound q)
    (B' : OracleAdv.Timed (OEv W SS C) (OOut S W K PK C) Bool) (hB' : B'.erase = B) {T : ℕ}
    (hT : B'.TimeBound T) :
    (kemRed.tree.timed (fun t e => simDist P (encPk t.1.1.1 (liftE e))) μCost
        (kemStep P G g) stepCost (fun k t => decide (k ∈ t.2)) extCost yInit
        ⟨B, hB⟩ B').TimeBound (2 + (T + q * (F (2 * q) + 11) + (Ext (2 * q) + 2))) := by
  intro pk cs k
  have h := kemRedRun.timeBound_timed P G g pk cs k μCost stepCost extCost F Ext hF hE
    (hcost pk cs) (hext k) B' hT (hB' ▸ hB)
  have h' := OracleAdv.Timed.stepTimeBound_delay (c := 1) h
  simp only [kemRed.tree.timed, kemRed.tree.run.tree.timed]
  exact h'.mono (by omega)

end Certificate

end CatCrypt.Crypto.AKE.PQXDHSquareKEM
