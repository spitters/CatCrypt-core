/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.PQXDHSquareKEM
public import CatCryptCore.Crypto.AKE.X3DHSquareGDHTimed
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveTimeBound
public import CatCryptCore.Tactics.StdCosts

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
of the adversary plus a polynomial in its queries for polynomial `F` and `Ext`.

**The costed step.** A step `kemStep` of the world of the reduction is a function of its draw, and
it is written as deterministic computations whose costed trees `derive_reduction` builds:
`kLiftCP` (the draw `liftD`, which embeds the challenge public key and the challenge
encapsulation at the sessions of the guess), `kOtherCP`, `kCguardCP`, `kSguardCP`, `kLtCP`,
`kCompleteCP` and `kSendCP` (the start `simStartD` of the simulator over the symbolic KEM
`symP`, whose decapsulation at the absent secret key of the guess is the answer of the
decapsulation oracle), `kFinCP` (the call to `F_AKE` and the finish), `kNewCP` and `kAppCP` (the
concrete shared secret of the step and its append), and `kNeedCP`, `kEncPkCP`, `kExtCP` (the query
decision, the public key of the draw and the extraction). The programs are those of
`PQXDHSquareGDHTimed` over the group `W` instead of `W ⊕ W`, with the guards and deliveries
split in the same way; `kOtherCP_eq`, `simCompleteD_eq` and `simSendD_eq` state that they compute
the start of the simulator. The step costs `kemStepTime`, the sum of the times of the costed
trees on the states they read with zero cost companions, the query decision `kemNeedTime`, the
draw `kemDrawTime` and the extraction `kemExtTime`. With the public value of an exponent of cost
at most `tc`, exponentiation at most `te` and decapsulation at most `tD`, a step from a state of
size at most `n` whose functionality has at most `n` notices costs at most `kemStepBound tc te tD n
= 2000 + 50 (tc + te) + 2 tD + 200 n` (`kemStepTime_le`), the extraction at most
`kemExtBound n = 10 n + 10` (`kemExtTime_le`). A step adds at most one notice to `F_AKE`
(`fNotices_kemStep`), so that the costed reduction runs in time at most
`T + q · (kemStepBound tc te tD (2q) + 7) + kemExtBound (2q) + 1` (`kemRed_timeBound_cost`), and
the stage of the costed IND-CCA reduction in time at most
`2 + (T + q · (kemStepBound tc te tD (2q) + 11) + kemExtBound (2q) + 2)` (`kemRed.timeBound_cost`),
without hypotheses on the costs of the step and of the extraction. The draws of the world are
the distribution `simDist` of a step, priced at one unit with the public key it reads, so that
the key generation and the encapsulation of the KEM enter through the draw and not through the
step. The decisions `isEnc` of `liftD` compare public keys by the instance binder
`[DecidableEq PK]`, and `derive_reduction` charges them by the cost of their conditions.

`derive_reduction` refuses the step as one program, `SPComp.pure (kemStep P G g pk cs oa t e r)`:

    derive_reduction: the first attempt fails:
      derive_timed: needs a registered primitive: `Function.update` unfolds deeper than 16
      definitions (option `derive_timed.maxDepth`)
    with the data definitions applied to a structure binder unfolded:
      (deterministic) timeout at `whnf`, maximum number of heartbeats (200000) has been reached

and the start as one program `SPComp.pure (simStartD P' G s e d)` and the start of `send`
`SPComp.pure (simSendD P' G s x e c d)` fail in the proof of their compile equations by a
time-out of `simp`; the restatement by events (`kOtherCP`), by guards (`kCguardCP`,
`kSguardCP` with the decapsulation as a parameter), by the draws of long-term secrets (`kLtCP`)
and by deliveries at a given state (`kCompleteCP`, `kSendCP`) avoids it.

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
* `kemStepTime`, `kemNeedTime`, `kemDrawTime`, `kemExtTime`: the derived costs of the step, the
  query decision, the draw and the extraction; `kemStepTime_le`, `kemExtTime_le`: their bounds.
* `kOtherCP_eq`, `simCompleteD_eq`, `simSendD_eq`: the step programs compute the start of the
  simulator.
* `kemRed_timeBound_cost`, `kemRedRun.timeBound_cost`, `kemRed.timeBound_cost`: the time of the
  KEM reduction at the derived costs.

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
theorem sizeY_kemStep [DecidableEq PK]
    (pk : PK) (cs : C) (oa : Option (Option SS)) (t : YSt S W K PK SK SS C)
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
theorem kemRed_erase_timed [DecidableEq PK]
    (pk : PK) (cs : C) (k : SS) (needCost : YSt S W K PK SK SS C →
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
theorem kemRed_timeBound [DecidableEq PK]
    (pk : PK) (cs : C) (k : SS) (needCost : YSt S W K PK SK SS C →
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
theorem kemRedRun.compile_tree [DecidableEq PK] (μCost : YSt S W K PK SK SS C → OEv W SS C → ℕ)
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
theorem kemRedRun.timeBound_timed [DecidableEq PK] (pk : PK) (cs : C) (k : SS)
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
theorem kemRed.compile_tree [DecidableEq PK] (μCost : YSt S W K PK SK SS C → OEv W SS C → ℕ)
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
theorem kemRed.timeBound_timed [DecidableEq PK] (μCost : YSt S W K PK SK SS C → OEv W SS C → ℕ)
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

/-! ## The costed step of the world of the reduction -/

section KemCost

open CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.PAKE.DHExtract
open CatCrypt.Crypto.AKE.X3DHSquare (RSt Named bobInp ephPubOf)
open CatCrypt.Crypto.AKE.X3DHSquareHops (Draw ltD drive0D fStepD)
open CatCrypt.Crypto.OracleGameUpToBad (roDet)
open CatCrypt.Crypto.AKE.PQXDHSquare CatCrypt.Crypto.AKE.PQXDHSquareHops
open CatCrypt.Crypto.KEM.Games (Scheme)

/-- The state of the symbolic simulator of the world of the reduction. -/
abbrev SimY (S W K PK SK SS C : Type) := SimSt S W K PK (Option SK) (Option SS) C

section Prog
variable {S W K PK SK SS C : Type} [Field S] [Fintype S] [SampleableType W] [Fintype K]
  [Nonempty K] [Inhabited K] [DecidableEq SS] [DecidableEq C] (P : Scheme PK SK SS C)
  (G : DHGroup S W) (g : Guess)

noncomputable def kNeedCP (cs : C) (e : OEv W SS C) : SPComp (Option C) := SPComp.pure (needQ cs e)

noncomputable def kEncPkCP (s : PSt S W K PK (Option SK) (Option SS) C) (e : OEv W SS C) :
    SPComp (Option PK) := SPComp.pure (encPk s (liftE e))

noncomputable def kLiftCP [DecidableEq PK] (pk : PK) (cs : C) (t : SimY S W K PK SK SS C)
    (e : OEv W SS C) (r : PDraw S K PK SK SS C × K) :
    SPComp (PDraw S K PK (Option SK) (Option SS) C × K) :=
  SPComp.pure (liftD g pk cs t e r)

noncomputable def kNewCP (cs : C) (dec : C → Option SS) (t : SimY S W K PK SK SS C)
    (e : OEv W SS C) (r : PDraw S K PK SK SS C × K) : SPComp (Option SS) :=
  SPComp.pure (newVal P cs dec t e r)

/-- The append of the concrete shared secret of a step to the received shared secrets. -/
noncomputable def kAppCP (l : List SS) (o : Option SS) : SPComp (List SS) :=
  SPComp.pure (l ++ o.toList)

/-- The extraction of the reduction as a computation: the membership of the key `k`. -/
noncomputable def kExtCP (k : SS) (l : List SS) : SPComp Bool := SPComp.pure (decide (k ∈ l))

/-- The guard of `complete` in the symbolic simulator: the record, the ephemeral secret, the
one-time prekey and the KEM public key of the peer, when the session completes. -/
def kCguard (s : SimY S W K PK SK SS C) (x : Inst) : Option (Rec K × S × S × PK) :=
  match s.1.x.st.recs x, s.1.x.eph x with
  | some rc, some ek =>
    match X3DHSquare.opkOf s.1.x x.1 rc.peer, pkOf s.1 x.1 rc.peer with
    | some opk, some pk =>
      if rc.role = .initiator ∧ rc.key.isNone then some (rc, ek, opk, pk) else none
    | _, _ => none
  | _, _ => none

/-- The guard of `complete` as a computation. -/
noncomputable def kCguardCP (s : SimY S W K PK SK SS C) (x : Inst) :
    SPComp (Option (Rec K × S × S × PK)) :=
  SPComp.pure (kCguard s x)

/-- The delivery of `complete` as a computation, at the long-term secrets `l1`, `l2` and the
encapsulated secret `ss`. -/
noncomputable def kCompleteCP (rs : PSt S W K PK (Option SK) (Option SS) C)
    (inp : Inst → Option (PInp W (Option SS))) (x : Inst) (r : Rec K) (ek opk : S)
    (ss : Option SS) (l1 l2 : S × S) (k : K) :
    SPComp (SimY S W K PK SK SS C × Dec S W K PK C) :=
  SPComp.pure (deliverD rs inp x r (X3DHSquare.aliceInp G x.1 x.2 r.peer l1.1 ek (G.pub l2.1)
    (G.pub l2.2) (G.pub opk), ss) k)

/-- The guard of `send` in the symbolic simulator, with the decapsulation `decaps`. -/
def kSguard (decaps : Option SK → C → Option (Option SS)) (s : SimY S W K PK SK SS C)
    (x : Inst) (c : C) : Option (Rec K × S × Option SS) :=
  match s.1.x.st.recs x, s.1.x.eph x, s.1.kem x with
  | some r, some opk, some kp =>
    match decaps kp.2 c with
    | some ss => if r.role = .responder ∧ r.key.isNone then some (r, opk, ss) else none
    | none => none
  | _, _, _ => none

/-- The guard of `send` as a computation. -/
noncomputable def kSguardCP (decaps : Option SK → C → Option (Option SS))
    (s : SimY S W K PK SK SS C) (x : Inst) (c : C) : SPComp (Option (Rec K × S × Option SS)) :=
  SPComp.pure (kSguard decaps s x c)

/-- The draw of long-term secrets `ltD` as a computation. -/
noncomputable def kLtCP (rs : RSt S W K) (pid : PartyId) (l : S × S) :
    SPComp ((S × S) × RSt S W K) :=
  SPComp.pure (ltD rs pid l)

/-- The delivery of `send` as a computation, at the long-term secrets `l1`, `l2` and the
decapsulated secret `ss`. -/
noncomputable def kSendCP (rs : PSt S W K PK (Option SK) (Option SS) C)
    (inp : Inst → Option (PInp W (Option SS))) (x : Inst) (e : W) (r : Rec K) (opk : S)
    (ss : Option SS) (l1 l2 : S × S) (k : K) :
    SPComp (SimY S W K PK SK SS C × Dec S W K PK C) :=
  SPComp.pure (deliverD rs inp x r (bobInp G x.1 r.peer x.2 (G.pub l2.1) e l1.1 l1.2 opk, ss) k)

/-- The start of the symbolic simulator on the events other than `complete` and `send`, with the
draw `d`, as a computation. -/
noncomputable def kOtherCP (s : SimY S W K PK SK SS C) (e : OEv W (Option SS) C)
    (d : PDraw S K PK (Option SK) (Option SS) C) :
    SPComp (SimY S W K PK SK SS C × Dec S W K PK C) :=
  match e with
  | .inl (.newSession sid pid peer role) =>
    if (s.1.x.st.recs (sid, pid)).isNone then
      if role = .responder then
        SPComp.pure (({ s.1 with
            x := { s.1.x with st := addSession s.1.x.st (sid, pid) peer role,
                              eph := Function.update s.1.x.eph (sid, pid) (some d.1.1) },
            kem := Function.update s.1.kem (sid, pid) (some d.2.1) }, s.2.1, .fwd),
          .inl (.inl (.newSession sid pid peer role)))
      else
        SPComp.pure (({ s.1 with
            x := { s.1.x with st := addSession s.1.x.st (sid, pid) peer role,
                              eph := Function.update s.1.x.eph (sid, pid) (some d.1.1) } },
            s.2.1, .fwd), .inl (.inl (.newSession sid pid peer role)))
    else SPComp.pure ((s.1, s.2.1, .fwd), .inl (.inl (.newSession sid pid peer role)))
  | .inl (.getKey sid pid) => SPComp.pure ((s.1, s.2.1, .fwd), .inl (.inl (.getKey sid pid)))
  | .inr .idle => SPComp.pure ((s.1, s.2.1, .fwd), .inr (.inr (.inl .ack)))
  | .inr .poll =>
    SPComp.pure (({ s.1 with x := { s.1.x with st := (pollStep s.1.x.st).1 } }, s.2.1, .fwd),
      .inr (.inr (.inl (.notice (pollStep s.1.x.st).2))))
  | .inr (.pub pid) =>
    SPComp.pure (({ s.1 with x := (ltD s.1.x pid d.1.2.1).2 }, s.2.1, .fwd),
      .inr (.inr (.inl (.pub (G.pub (ltD s.1.x pid d.1.2.1).1.1)
        (G.pub (ltD s.1.x pid d.1.2.1).1.2)))))
  | .inr (.ephPub sid pid) =>
    SPComp.pure ((s.1, s.2.1, .fwd), .inr (.inr (.inl (.eph (ephPubOf G s.1.x (sid, pid))))))
  | .inr (.pqPub sid pid) =>
    SPComp.pure ((s.1, s.2.1, .fwd), .inr (.inr (.inr (pkOf s.1 sid pid, s.1.ct (sid, pid)))))
  | .inr (.corrupt pid) =>
    if Named s.1.x.st pid then
      SPComp.pure ((s.1, s.2.1, .fwd), .inr (.inr (.inl (.secret none))))
    else
      SPComp.pure (({ s.1 with x := { (ltD s.1.x pid d.1.2.1).2 with
                            st := corruptStep (ltD s.1.x pid d.1.2.1).2.st pid } }, s.2.1,
          .out (.inl (.secret (some (ltD s.1.x pid d.1.2.1).1)))), .inl (.inr (.corrupt pid)))
  | .inr (.complete _ _) => SPComp.pure ((s.1, s.2.1, .fwd), .inr (.inr (.inl .ack)))
  | .inr (.send _ _ _ _) => SPComp.pure ((s.1, s.2.1, .fwd), .inr (.inr (.inl .ack)))
  | .inr (.kdf x) =>
    SPComp.pure (({ s.1 with ro := (roDet s.1.ro x d.1.2.2.2).2 }, s.2.1, .fwd),
      .inr (.inr (.inl (.hash (roDet s.1.ro x d.1.2.2.2).1))))

/-- The finish of a step as a computation: the decision of the start passed to `F_AKE` with the
fresh key `kf`, and its answer to `finV`. -/
noncomputable def kFinCP (p : SimY S W K PK SK SS C × Dec S W K PK C) (t : St K) (kf : K) :
    SPComp (SimY S W K PK SK SS C × St K × OOut S W K PK C) :=
  SPComp.pure (drive0D fStepD finV p.1 p.2 t kf)
end Prog

derive_reduction kNeedCP
derive_reduction kEncPkCP
derive_reduction kLiftCP
derive_reduction kNewCP
derive_reduction kAppCP
derive_reduction kExtCP
derive_reduction kCguardCP
derive_reduction kCompleteCP
derive_reduction kSguardCP
derive_reduction kLtCP
derive_reduction kSendCP
derive_reduction kOtherCP
derive_reduction kFinCP


/-- The records and corruptions of a state read at unit cost. -/
abbrev liftStY {K : Type} (t : St K) :
    ((Inst → Option (Rec K)) × (Inst → ℕ)) × ((PartyId → Bool) × (PartyId → ℕ)) × List Notice × ℕ :=
  ((t.recs, fun _ => 0), (t.corrupt, fun _ => 0), t.notices, t.cursor)

/-- The X3DH part of a state with its tables read at unit cost. -/
abbrev liftXY {S W K : Type} (rs : RSt S W K) :=
  (liftStY rs.st, (rs.lt, fun (_ : PartyId) => 0), (rs.eph, fun (_ : Inst) => 0), rs.ro)

/-- A state of the symbolic simulator with its tables read at unit cost: every cost companion is
zero. -/
abbrev liftY {S W K PK SK SS C : Type} (s : SimY S W K PK SK SS C) :=
  ((liftXY s.1.x, (s.1.kem, fun (_ : Inst) => 0), (s.1.ct, fun (_ : Inst) => 0), s.1.ro),
    (s.2.1, fun (_ : Inst) => 0), s.2.2)

section Costed
variable {S W K PK SK SS C : Type} [Field S] [Fintype S] [SampleableType W] [Fintype K]
  [Nonempty K] [Inhabited K] [DecidableEq SS] [DecidableEq C] (P : Scheme PK SK SS C)
  (G : DHGroup S W) (g : Guess) (coeCost : S ≃ W → S → ℕ) (expCost : W → S → ℕ)
  (decCost : SK → C → ℕ)

/-- The cost of the decapsulation of the symbolic KEM: `decCost` at a secret key, one unit at the
absent secret key of the challenge. -/
def symDecCost (osk : Option SK) (c : C) : ℕ :=
  match osk with
  | some sk => decCost sk c
  | none => 1

/-- The time of `send` on the ephemeral key `e'` and the encapsulation `c` with the draw `d`: the
guard with its decapsulation, the two draws of long-term secrets and the delivery, each on the
state it reads. -/
noncomputable def kSendTime (decaps : Option SK → C → Option (Option SS))
    (s : SimY S W K PK SK SS C) (sid : SessionId) (pid : PartyId) (e' : W) (c : C)
    (d : Draw S K) : ℕ :=
  SPTree.Timed.stepTime (kSguardCP.tree.timed decaps (symDecCost decCost) (liftY s) (sid, pid) c
      (fun _ => 0) (fun _ => 0) (fun _ => 0)) +
    match kSguard decaps s (sid, pid) c with
    | some (rc, opk, ss) =>
      SPTree.Timed.stepTime (kLtCP.tree.timed s.1.x pid d.2.1 (fun _ => 0) (liftStY s.1.x.st)
          (fun _ => 0)) +
        SPTree.Timed.stepTime (kLtCP.tree.timed (ltD s.1.x pid d.2.1).2 rc.peer d.2.2.1
          (fun _ => 0) (liftStY (ltD s.1.x pid d.2.1).2.st) (fun _ => 0)) +
        SPTree.Timed.stepTime (kSendCP.tree.timed G
          { s.1 with x := (ltD (ltD s.1.x pid d.2.1).2 rc.peer d.2.2.1).2 } s.2.1 (fun _ => 0)
          (sid, pid) e' rc opk ss (ltD s.1.x pid d.2.1).1
          (ltD (ltD s.1.x pid d.2.1).2 rc.peer d.2.2.1).1 d.2.2.2 DFunLike.coe coeCost expCost
          (liftXY (ltD (ltD s.1.x pid d.2.1).2 rc.peer d.2.2.1).2) (fun _ => 0) (fun _ => 0))
    | none => 0

/-- The time of `complete` with the draw `d` and the encapsulation `kc`: the guard, the two draws
of long-term secrets and the delivery, each on the state it reads. -/
noncomputable def kCompleteTime (s : SimY S W K PK SK SS C) (sid : SessionId) (pid : PartyId)
    (d : Draw S K) (kc : Option (Option SS × C)) : ℕ :=
  SPTree.Timed.stepTime (kCguardCP.tree.timed (liftY s) (sid, pid) (fun _ => 0) (fun _ => 0)
      (fun _ => 0)) +
    match kCguard s (sid, pid), kc with
    | some (rc, ek, opk, _), some kc =>
      SPTree.Timed.stepTime (kLtCP.tree.timed s.1.x pid d.2.1 (fun _ => 0) (liftStY s.1.x.st)
          (fun _ => 0)) +
        SPTree.Timed.stepTime (kLtCP.tree.timed (ltD s.1.x pid d.2.1).2 rc.peer d.2.2.1
          (fun _ => 0) (liftStY (ltD s.1.x pid d.2.1).2.st) (fun _ => 0)) +
        SPTree.Timed.stepTime (kCompleteCP.tree.timed G
          { s.1 with x := (ltD (ltD s.1.x pid d.2.1).2 rc.peer d.2.2.1).2,
                     ct := Function.update s.1.ct (sid, pid) (some kc.2) } s.2.1 (fun _ => 0)
          (sid, pid) rc ek opk kc.1 (ltD s.1.x pid d.2.1).1
          (ltD (ltD s.1.x pid d.2.1).2 rc.peer d.2.2.1).1 d.2.2.2 DFunLike.coe coeCost expCost
          (liftXY (ltD (ltD s.1.x pid d.2.1).2 rc.peer d.2.2.1).2) (fun _ => 0) (fun _ => 0))
    | _, _ => 0

/-- The time of the other events: the costed tree of `kOtherCP` with the tables read at unit cost. -/
noncomputable def kOtherTime (s : SimY S W K PK SK SS C) (e : OEv W (Option SS) C)
    (d : PDraw S K PK (Option SK) (Option SS) C) : ℕ :=
  SPTree.Timed.stepTime (kOtherCP.tree.timed G (liftY s) e d s.1.x.st.recs (fun _ => 0)
    s.1.x.eph (fun _ => 0) s.1.kem (fun _ => 0) s.2.1 (fun _ => 0) DFunLike.coe coeCost s.1.ct
    (fun _ => 0))

/-- **The time of the start** of the simulator of the world of the reduction on the event `e`
with the draw `d`: one unit for the dispatch on the event and the time of `complete`, of `send`
or of the costed tree of `kOtherCP`. -/
noncomputable def kStartTime (decaps : Option SK → C → Option (Option SS))
    (s : SimY S W K PK SK SS C) (e : OEv W (Option SS) C)
    (d : PDraw S K PK (Option SK) (Option SS) C) : ℕ :=
  1 + match e with
    | .inr (.complete sid pid) => kCompleteTime G coeCost expCost s sid pid d.1 d.2.2
    | .inr (.send sid pid e' c) => kSendTime G coeCost expCost decCost decaps s sid pid e' c d.1
    | e => kOtherTime G coeCost s e d

/-- **The time of a step** of the world of the reduction with the answer `oa` of the
decapsulation oracle and the draw `r`: the lift of the draw, the start of the simulator over
the symbolic KEM, the finish with `F_AKE`, the concrete shared secret brought by the event and
its append to the list of received shared secrets. -/
noncomputable def kemStepTime [DecidableEq PK] (pk : PK) (cs : C) (oa : Option (Option SS))
    (t : YSt S W K PK SK SS C) (e : OEv W SS C) (r : PDraw S K PK SK SS C × K) : ℕ :=
  SPTree.Timed.stepTime (kLiftCP.tree.timed g pk cs (liftY t.1.1) e r (fun _ => 0) (fun _ => 0)
      (fun _ => 0)) +
    kStartTime G coeCost expCost decCost (symP P cs fun _ => oa.getD none).decaps t.1.1 (liftE e)
      (liftD g pk cs t.1.1 e r).1 +
    SPTree.Timed.stepTime (kFinCP.tree.timed
      (liftY (simStartD (symP P cs fun _ => oa.getD none) G t.1.1 (liftE e)
          (liftD g pk cs t.1.1 e r).1).1,
        (simStartD (symP P cs fun _ => oa.getD none) G t.1.1 (liftE e)
          (liftD g pk cs t.1.1 e r).1).2) t.1.2 (liftD g pk cs t.1.1 e r).2 (fun _ => 0)
      (fun _ => 0)) +
    SPTree.Timed.stepTime (kNewCP.tree.timed P cs (fun _ => oa.getD none) (fun _ => 0)
      (liftY t.1.1) e r (fun _ => 0) decCost) +
    SPTree.Timed.stepTime (kAppCP.tree.timed t.2 (newVal P cs (fun _ => oa.getD none) t.1.1 e r)
      (· ++ ·) (fun l _ => l.length + 1))

/-- The time of the query decision `needQ`. -/
noncomputable def kemNeedTime (cs : C) (_t : YSt S W K PK SK SS C) (e : OEv W SS C) : ℕ :=
  SPTree.Timed.stepTime (kNeedCP.tree.timed cs e)

/-- The time of the draw of a step: the public key of the encapsulation read from the state
and one unit for the draw of `simDist`. -/
noncomputable def kemDrawTime (t : YSt S W K PK SK SS C) (e : OEv W SS C) : ℕ :=
  1 + SPTree.Timed.stepTime (kEncPkCP.tree.timed t.1.1.1 e (fun _ => 0) (fun _ => 0))

/-- The time of the extraction of the membership of the key `k`. -/
noncomputable def kemExtTime (k : SS) (t : YSt S W K PK SK SS C) : ℕ :=
  SPTree.Timed.stepTime (kExtCP.tree.timed k t.2)

end Costed

section Bounds
variable {S W K PK SK SS C : Type} [Field S] [Fintype S] [SampleableType W] [Fintype K]
  [Nonempty K] [Inhabited K] [DecidableEq SS] [DecidableEq C] (P : Scheme PK SK SS C)
  (G : DHGroup S W) (g : Guess) (coeCost : S ≃ W → S → ℕ) (expCost : W → S → ℕ)
  (decCost : SK → C → ℕ)

omit [SampleableType W] [DecidableEq SS] in
theorem kNeed_time (cs : C) (e : OEv W SS C) :
    SPTree.Timed.stepTime (kNeedCP.tree.timed cs e) ≤ 10 := by
  time_bound

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K]
  [DecidableEq SS] [DecidableEq C] in
theorem kEncPk_time (s : PSt S W K PK (Option SK) (Option SS) C) (e : OEv W SS C) :
    SPTree.Timed.stepTime (kEncPkCP.tree.timed s e (fun _ => 0) (fun _ => 0)) ≤ 20 := by
  time_bound

theorem kExt_time (k : SS) (l : List SS) :
    SPTree.Timed.stepTime (kExtCP.tree.timed k l) ≤ 10 * l.length + 10 := by
  time_bound

omit [DecidableEq SS] in
theorem kApp_time (l : List SS) (o : Option SS) :
    SPTree.Timed.stepTime (kAppCP.tree.timed l o (· ++ ·) (fun l _ => l.length + 1)) ≤
      l.length + 10 := by
  time_bound

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K]
  [DecidableEq SS] [DecidableEq C] in
theorem kLift_time [DecidableEq PK] (pk : PK) (cs : C) (t : SimY S W K PK SK SS C) (e : OEv W SS C)
    (r : PDraw S K PK SK SS C × K) :
    SPTree.Timed.stepTime (kLiftCP.tree.timed g pk cs (liftY t) e r (fun _ => 0) (fun _ => 0)
      (fun _ => 0)) ≤ 100 := by
  time_bound

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K]
  [DecidableEq SS] in
theorem kNew_time (cs : C) (dec : C → Option SS) (t : SimY S W K PK SK SS C) (e : OEv W SS C)
    (r : PDraw S K PK SK SS C × K) {tD : ℕ} (hD : ∀ sk c, decCost sk c ≤ tD) :
    SPTree.Timed.stepTime (kNewCP.tree.timed P cs dec (fun _ => 0) (liftY t) e r (fun _ => 0)
      decCost) ≤ 40 + tD := by
  time_bound

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K]
  [DecidableEq SS] [DecidableEq C] in
theorem kFin_time (p : SimY S W K PK SK SS C × Dec S W K PK C) (t : St K) (kf : K) :
    SPTree.Timed.stepTime (kFinCP.tree.timed (liftY p.1, p.2) t kf (fun _ => 0) (fun _ => 0)) ≤
      300 + 30 * t.notices.length := by
  time_bound

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K] in
theorem kLt_time (rs : RSt S W K) (pid : PartyId) (l : S × S) :
    SPTree.Timed.stepTime (kLtCP.tree.timed rs pid l (fun _ => 0) (liftStY rs.st) (fun _ => 0)) ≤
      20 := by
  time_bound

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K]
  [DecidableEq SS] [DecidableEq C] in
theorem kSguard_time (decaps : Option SK → C → Option (Option SS))
    (decapsCost : Option SK → C → ℕ) (s : SimY S W K PK SK SS C)
    (x : Inst) (c : C) {tD : ℕ} (hD : ∀ sk c, decapsCost sk c ≤ tD) :
    SPTree.Timed.stepTime (kSguardCP.tree.timed decaps decapsCost (liftY s) x c
      (fun _ => 0) (fun _ => 0) (fun _ => 0)) ≤ 40 + tD := by
  time_bound

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K]
  [DecidableEq SS] [DecidableEq C] in
theorem kCguard_time (s : SimY S W K PK SK SS C) (x : Inst) :
    SPTree.Timed.stepTime (kCguardCP.tree.timed (liftY s) x (fun _ => 0) (fun _ => 0)
      (fun _ => 0)) ≤ 40 := by
  time_bound

omit [Fintype S] [Fintype K] [Nonempty K] [DecidableEq C] in
theorem kCompleteDel_time (rs : PSt S W K PK (Option SK) (Option SS) C)
    (inp : Inst → Option (PInp W (Option SS))) (x : Inst) (r : Rec K) (ek opk : S)
    (ss : Option SS) (l1 l2 : S × S) (k : K) {tc te : ℕ} (hc : ∀ a b, coeCost a b ≤ tc)
    (he : ∀ a b, expCost a b ≤ te) :
    SPTree.Timed.stepTime (kCompleteCP.tree.timed G rs inp (fun _ => 0) x r ek opk ss l1 l2 k
      DFunLike.coe coeCost expCost (liftXY rs.x) (fun _ => 0) (fun _ => 0)) ≤
      500 + 50 * (tc + te) + 50 * rs.ro.length := by
  time_bound

omit [Fintype S] [Fintype K] [Nonempty K] [Inhabited K] [DecidableEq C] in
theorem kOther_time (s : SimY S W K PK SK SS C) (e : OEv W (Option SS) C)
    (d : PDraw S K PK (Option SK) (Option SS) C) {tc : ℕ} (hc : ∀ a b, coeCost a b ≤ tc) :
    kOtherTime G coeCost s e d ≤
      500 + 50 * tc + 50 * s.1.ro.length + 50 * s.1.x.st.notices.length := by
  unfold kOtherTime
  rcases e with (⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) | (_ | _ | pid | ⟨sid, pid⟩ |
    ⟨sid, pid⟩ | pid | ⟨sid, pid⟩ | ⟨sid, pid, e, c⟩ | q)
  all_goals time_bound

omit [Fintype S] [Fintype K] [Nonempty K] [DecidableEq C] in
theorem kSendDel_time (rs : PSt S W K PK (Option SK) (Option SS) C)
    (inp : Inst → Option (PInp W (Option SS))) (x : Inst) (e : W) (r : Rec K) (opk : S)
    (ss : Option SS) (l1 l2 : S × S) (k : K) {tc te : ℕ} (hc : ∀ a b, coeCost a b ≤ tc)
    (he : ∀ a b, expCost a b ≤ te) :
    SPTree.Timed.stepTime (kSendCP.tree.timed G rs inp (fun _ => 0) x e r opk ss l1 l2 k
      DFunLike.coe coeCost expCost (liftXY rs.x) (fun _ => 0) (fun _ => 0)) ≤
      500 + 50 * (tc + te) + 50 * rs.ro.length := by
  time_bound

omit [DecidableEq C] in
theorem symDecCost_le {tD : ℕ} (hD : ∀ sk c, decCost sk c ≤ tD) (o : Option SK) (c : C) :
    symDecCost decCost o c ≤ tD + 1 := by
  cases o with
  | none => simp only [symDecCost]; omega
  | some sk => have := hD sk c; simp only [symDecCost]; omega

omit [Fintype S] [Fintype K] [Nonempty K] [DecidableEq C] in
theorem kStartTime_le (decaps : Option SK → C → Option (Option SS)) (s : SimY S W K PK SK SS C)
    (e : OEv W (Option SS) C) (d : PDraw S K PK (Option SK) (Option SS) C) {tc te tD : ℕ}
    (hc : ∀ a b, coeCost a b ≤ tc) (he : ∀ a b, expCost a b ≤ te)
    (hD : ∀ sk c, decCost sk c ≤ tD) :
    kStartTime G coeCost expCost decCost decaps s e d ≤
      700 + tD + 50 * (tc + te) + 50 * s.1.ro.length + 50 * s.1.x.st.notices.length := by
  unfold kStartTime
  rcases e with (⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) | (_ | _ | pid | ⟨sid, pid⟩ |
    ⟨sid, pid⟩ | pid | ⟨sid, pid⟩ | ⟨sid, pid, e', c⟩ | q)
  rotate_left 8
  · dsimp only
    unfold kCompleteTime
    have := kCguard_time s (sid, pid)
    split
    · rename_i rc ek opk _ kc _ _
      have := kLt_time s.1.x pid d.1.2.1
      have := kLt_time (ltD s.1.x pid d.1.2.1).2 rc.peer d.1.2.2.1
      have := kCompleteDel_time G coeCost expCost
        { s.1 with x := (ltD (ltD s.1.x pid d.1.2.1).2 rc.peer d.1.2.2.1).2,
                   ct := Function.update s.1.ct (sid, pid) (some kc.2) } s.2.1 (sid, pid) rc ek
        opk kc.1 (ltD s.1.x pid d.1.2.1).1 (ltD (ltD s.1.x pid d.1.2.1).2 rc.peer d.1.2.2.1).1
        d.1.2.2.2 hc he
      dsimp only at this ⊢
      grind
    · omega
  · dsimp only
    unfold kSendTime
    have := kSguard_time decaps (symDecCost decCost) s (sid, pid) c (symDecCost_le decCost hD)
    split
    · rename_i rc opk ss _
      have := kLt_time s.1.x pid d.1.2.1
      have := kLt_time (ltD s.1.x pid d.1.2.1).2 rc.peer d.1.2.2.1
      have := kSendDel_time G coeCost expCost
        { s.1 with x := (ltD (ltD s.1.x pid d.1.2.1).2 rc.peer d.1.2.2.1).2 } s.2.1 (sid, pid) e'
        rc opk ss (ltD s.1.x pid d.1.2.1).1 (ltD (ltD s.1.x pid d.1.2.1).2 rc.peer d.1.2.2.1).1
        d.1.2.2.2 hc he
      dsimp only at this ⊢
      grind
    · omega
  all_goals
    dsimp only
    refine le_trans (Nat.add_le_add_left (kOther_time G coeCost s _ d hc) 1) ?_
    omega

/-- The bound of a step of the world of the reduction from a state whose sizes are at most `n`,
for costs at most `tc` (public value of an exponent), `te` (exponentiation) and `tD`
(decapsulation). -/
def kemStepBound (tc te tD n : ℕ) : ℕ :=
  2000 + 50 * (tc + te) + 2 * tD + 200 * n

/-- The bound of the extraction from a state whose list of received shared secrets has at most
`n` entries. -/
def kemExtBound (n : ℕ) : ℕ := 10 * n + 10

theorem kemStepBound_mono (tc te tD : ℕ) : Monotone (kemStepBound tc te tD) :=
  fun _ _ h => by unfold kemStepBound; omega

theorem kemExtBound_mono : Monotone kemExtBound := fun _ _ h => by unfold kemExtBound; omega

omit [Fintype S] [Fintype K] [Nonempty K] in
/-- **The time of a step** of the world of the reduction, with the times of the query decision
and of the draw, from a state of size at most `n` whose functionality has at most `n` notices,
is at most `kemStepBound … n`. -/
theorem kemStepTime_le [DecidableEq PK] (pk : PK) (cs : C) (oa : Option (Option SS)) {n : ℕ}
    (t : YSt S W K PK SK SS C) (hs : sizeY t ≤ n) (hf : t.1.2.notices.length ≤ n)
    (e : OEv W SS C) (r : PDraw S K PK SK SS C × K) {tc te tD : ℕ}
    (hc : ∀ a b, coeCost a b ≤ tc) (he : ∀ a b, expCost a b ≤ te)
    (hD : ∀ sk c, decCost sk c ≤ tD) :
    kemNeedTime cs t e + kemDrawTime t e +
        kemStepTime P G g coeCost expCost decCost pk cs oa t e r ≤ kemStepBound tc te tD n := by
  unfold kemNeedTime kemDrawTime kemStepTime kemStepBound
  have h1 := kNeed_time cs e
  have h2 := kEncPk_time t.1.1.1 e
  have h3 := kLift_time g pk cs t.1.1 e r
  have h4 := kStartTime_le G coeCost expCost decCost (symP P cs fun _ => oa.getD none).decaps
    t.1.1 (liftE e) (liftD g pk cs t.1.1 e r).1 hc he hD
  have h5 := kFin_time (simStartD (symP P cs fun _ => oa.getD none) G t.1.1 (liftE e)
    (liftD g pk cs t.1.1 e r).1) t.1.2 (liftD g pk cs t.1.1 e r).2
  have h6 := kNew_time P decCost cs (fun _ => oa.getD none) t.1.1 e r hD
  have h7 := kApp_time t.2 (newVal P cs (fun _ => oa.getD none) t.1.1 e r)
  simp only [sizeY] at hs
  omega

omit [Field S] [Fintype S] [SampleableType W] [Fintype K] [Nonempty K] [Inhabited K]
  [DecidableEq C] in
theorem kemExtTime_le (k : SS) {n : ℕ} (t : YSt S W K PK SK SS C) (hs : sizeY t ≤ n) :
    kemExtTime k t ≤ kemExtBound n := by
  unfold kemExtTime kemExtBound
  have := kExt_time k t.2
  simp only [sizeY] at hs
  omega

end Bounds

section Correct
variable {S W K PK SK SS C : Type} [Field S] [Fintype S] [SampleableType W] [Fintype K]
  [Nonempty K] [Inhabited K] [DecidableEq SS] [DecidableEq C] (P : Scheme PK SK SS C)
  (G : DHGroup S W) (g : Guess)

omit [Fintype S] [Fintype K] [Nonempty K] [DecidableEq C] in
/-- **`kOtherCP` computes the start of the simulator** on the events other than `complete`
and `send`, for every KEM `P'` of the symbolic world. -/
theorem kOtherCP_eq (P' : Scheme PK (Option SK) (Option SS) C) (s : SimY S W K PK SK SS C)
    (e : OEv W (Option SS) C) (d : PDraw S K PK (Option SK) (Option SS) C)
    (hc : ∀ sid pid, e ≠ .inr (.complete sid pid))
    (hs : ∀ sid pid E c, e ≠ .inr (.send sid pid E c)) :
    kOtherCP G s e d = SPComp.pure (simStartD P' G s e d) := by
  rcases e with (⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) | (_ | _ | pid | ⟨sid, pid⟩ |
    ⟨sid, pid⟩ | pid | ⟨sid, pid⟩ | ⟨sid, pid, E, c⟩ | q)
  · simp only [kOtherCP, simStartD]
    split_ifs <;> rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · simp only [kOtherCP, simStartD]
    split_ifs <;> rfl
  · exact absurd rfl (hc sid pid)
  · exact absurd rfl (hs sid pid E c)
  · rfl

omit [Fintype S] [Fintype K] [Nonempty K] [DecidableEq C] in
/-- **`complete` through its guard**: the start of the simulator on `complete` is the delivery
`kCompleteCP` after the two draws of long-term secrets, when the guard `kCguard` holds. -/
theorem simCompleteD_eq (s : SimY S W K PK SK SS C) (sid : SessionId) (pid : PartyId)
    (d : Draw S K) (kc : Option (Option SS × C)) :
    SPComp.pure (simCompleteD G s (sid, pid) d kc) =
      match kCguard s (sid, pid), kc with
      | some (rc, ek, opk, _), some kc =>
        kCompleteCP G
          { s.1 with x := (ltD (ltD s.1.x pid d.2.1).2 rc.peer d.2.2.1).2,
                     ct := Function.update s.1.ct (sid, pid) (some kc.2) } s.2.1 (sid, pid) rc ek
          opk kc.1 (ltD s.1.x pid d.2.1).1 (ltD (ltD s.1.x pid d.2.1).2 rc.peer d.2.2.1).1
          d.2.2.2
      | _, _ => SPComp.pure ((s.1, s.2.1, .fwd), .inr (.inr (.inl .ack))) := by
  unfold simCompleteD kCguard
  cases hr : s.1.x.st.recs (sid, pid) with
  | none => rfl
  | some rc =>
    cases he : s.1.x.eph (sid, pid) with
    | none => rfl
    | some ek =>
      dsimp only
      cases ho : X3DHSquare.opkOf s.1.x sid rc.peer with
      | none => rfl
      | some opk =>
        cases hk : pkOf s.1 sid rc.peer with
        | none => rfl
        | some pk =>
          by_cases hc : rc.role = .initiator ∧ rc.key.isNone = true
          · cases kc
            · simp only [hc, and_self, ↓reduceIte]
            · simp only [hc, and_self, ↓reduceIte]; rfl
          · cases kc <;> simp only [hc, ↓reduceIte]

omit [Fintype S] [Fintype K] [Nonempty K] [DecidableEq C] in
/-- **`send` through its guard**: the start of the simulator on `send` is the delivery `kSendCP`
after the two draws of long-term secrets, when the guard `kSguard` with the decapsulation of
`P'` holds. -/
theorem simSendD_eq (P' : Scheme PK (Option SK) (Option SS) C) (s : SimY S W K PK SK SS C)
    (sid : SessionId) (pid : PartyId) (e : W) (c : C) (d : Draw S K) :
    SPComp.pure (simSendD P' G s (sid, pid) e c d) =
      match kSguard P'.decaps s (sid, pid) c with
      | some (rc, opk, ss) =>
        kSendCP G { s.1 with x := (ltD (ltD s.1.x pid d.2.1).2 rc.peer d.2.2.1).2 } s.2.1
          (sid, pid) e rc opk ss (ltD s.1.x pid d.2.1).1
          (ltD (ltD s.1.x pid d.2.1).2 rc.peer d.2.2.1).1 d.2.2.2
      | none => SPComp.pure ((s.1, s.2.1, .fwd), .inr (.inr (.inl .ack))) := by
  unfold simSendD kSguard
  cases hr : s.1.x.st.recs (sid, pid) with
  | none => rfl
  | some rc =>
    cases he : s.1.x.eph (sid, pid) with
    | none => rfl
    | some opk =>
      cases hk : s.1.kem (sid, pid) with
      | none => rfl
      | some kp =>
        dsimp only
        cases hd : P'.decaps kp.2 c with
        | none => rfl
        | some ss =>
          by_cases hc : rc.role = .responder ∧ rc.key.isNone = true
          · simp only [hc, and_self, ↓reduceIte]; rfl
          · simp only [hc, ↓reduceIte]

end Correct

section Time
variable {S W K PK SK SS C : Type} [Field S] [Fintype S] [SampleableType W] [Fintype K]
  [Nonempty K] [Inhabited K] [DecidableEq SS] [DecidableEq C] (P : Scheme PK SK SS C)
  (G : DHGroup S W) (g : Guess) (coeCost : S ≃ W → S → ℕ) (expCost : W → S → ℕ)
  (decCost : SK → C → ℕ)

omit [Fintype S] [Fintype K] [Nonempty K] in
/-- A step of the world of the reduction adds at most one notice to the state of `F_AKE`. -/
theorem fNotices_kemStep [DecidableEq PK]
    (pk : PK) (cs : C) (oa : Option (Option SS)) (t : YSt S W K PK SK SS C)
    (e : OEv W SS C) (r : PDraw S K PK SK SS C × K) :
    (kemStep P G g pk cs oa t e r).1.1.2.notices.length ≤ t.1.2.notices.length + 1 := by
  simp only [kemStep, yStep, simWorldD]
  unfold drive0D
  split
  · dsimp only; omega
  · exact X3DHSquareGDH.fStepD_len _ _ _

/-- **The time of the KEM reduction under a size invariant.** Let the costs of the query
decision, of the draw and of a step from a state of size at most `2i` whose functionality has
at most `i` notices together be at most `F i`, and the cost of the extraction from such a state
at most `Ext i`, with `F` monotone. Then for a costed oracle adversary `B` of time `T` with at
most `q` queries the costed reduction runs in time at most `T + q · (F q + 7) + Ext q + 1`. -/
theorem kemRed_timeBound_inv [DecidableEq PK]
    (pk : PK) (cs : C) (k : SS) (needCost : YSt S W K PK SK SS C →
    OEv W SS C → ℕ) (μCost : YSt S W K PK SK SS C → OEv W SS C → ℕ)
    (stepCost : Option (Option SS) → YSt S W K PK SK SS C → OEv W SS C →
      PDraw S K PK SK SS C × K → ℕ) (extCost : YSt S W K PK SK SS C → ℕ) (F Ext : ℕ → ℕ)
    (hF : Monotone F)
    (hcost : ∀ i t e oa r, sizeY t ≤ 2 * i → t.1.2.notices.length ≤ i →
      needCost t e + μCost t e + stepCost oa t e r ≤ F i)
    (hext : ∀ i t, sizeY t ≤ 2 * i → t.1.2.notices.length ≤ i → extCost t ≤ Ext i)
    (B : OracleAdv.Timed (OEv W SS C) (OOut S W K PK C) Bool) {T q : ℕ} (hB : B.TimeBound T)
    (hq : B.erase.IsQueryBound q) :
    OracleAdv.Timed.StepTimeBound
      (stepRedQ.timed (fun _ e => needQ cs e) needCost
        (fun t e => simDist P (encPk t.1.1.1 (liftE e))) μCost (kemStep P G g pk cs) stepCost
        (fun t => decide (k ∈ t.2)) extCost B yInit)
      (T + q * (F q + 7) + (Ext q + 1)) :=
  stepRedQ.timeBound_timed _ _ _ _ _ _ _ _
    (fun i t => sizeY t ≤ 2 * i ∧ t.1.2.notices.length ≤ i) F Ext hF
    (fun _ _ h => ⟨by omega, by omega⟩)
    (fun i t e oa r h => by
      have := sizeY_kemStep P G g pk cs oa t e r
      have := fNotices_kemStep P G g pk cs oa t e r
      exact ⟨by omega, by omega⟩)
    (fun i t e oa r h => hcost i t e oa r h.1 h.2)
    (fun i t h => hext i t h.1 h.2) B hB hq yInit
    ⟨by simp [sizeY, yInit, pInit, X3DHSquare.rInit, initSt],
      by simp [yInit, initSt]⟩

/-- **The time of the KEM reduction** at the derived costs: with the query decision of cost
`kemNeedTime`, the draw of cost `kemDrawTime`, the step `kemStep` of cost `kemStepTime` and the
extraction of cost `kemExtTime`, a costed oracle adversary `B` of time `T` with at most `q`
queries gives a costed reduction, whose erasure is the program of `kemRed`
(`kemRed_erase_timed`), of time at most `T + q · (kemStepBound … (2q) + 7) + kemExtBound (2q) + 1`,
for costs of the public value of an exponent at most `tc`, of exponentiation at most `te` and of
decapsulation at most `tD`: the time of the adversary plus a polynomial of degree two in `q`. -/
theorem kemRed_timeBound_cost [DecidableEq PK] (pk : PK) (cs : C) (k : SS)
    (B : OracleAdv.Timed (OEv W SS C) (OOut S W K PK C) Bool) {T q : ℕ} (hB : B.TimeBound T)
    (hq : B.erase.IsQueryBound q) {tc te tD : ℕ} (hc : ∀ a b, coeCost a b ≤ tc)
    (he : ∀ a b, expCost a b ≤ te) (hD : ∀ sk c, decCost sk c ≤ tD) :
    OracleAdv.Timed.StepTimeBound
      (stepRedQ.timed (fun _ e => needQ cs e) (kemNeedTime cs)
        (fun t e => simDist P (encPk t.1.1.1 (liftE e))) kemDrawTime (kemStep P G g pk cs)
        (kemStepTime P G g coeCost expCost decCost pk cs) (fun t => decide (k ∈ t.2))
        (kemExtTime k) B yInit)
      (T + q * (kemStepBound tc te tD (2 * q) + 7) + (kemExtBound (2 * q) + 1)) :=
  kemRed_timeBound_inv P G g pk cs k _ _ _ _ (fun i => kemStepBound tc te tD (2 * i))
    (fun i => kemExtBound (2 * i)) (fun _ _ h => kemStepBound_mono tc te tD (by omega))
    (fun i t e oa r h1 h2 => kemStepTime_le P G g coeCost expCost decCost pk cs oa t h1
      (by omega) e r hc he hD)
    (fun i t h1 _ => kemExtTime_le k t h1) B hB hq

/-- **Time of the program of the KEM reduction** at the derived costs: the costed tree of
`kemRedRun`, at the draw of cost `kemDrawTime`, the step `kemStep` of cost `kemStepTime` and the
extraction of cost `kemExtTime`, runs in time at most
`1 + (T + q · (kemStepBound … (2q) + 11) + kemExtBound (2q) + 2)`. -/
theorem kemRedRun.timeBound_cost [DecidableEq PK] (pk : PK) (cs : C) (k : SS)
    (B : OracleAdv.Timed (OEv W SS C) (OOut S W K PK C) Bool) {T q : ℕ} (hB : B.TimeBound T)
    (hq : B.erase.IsQueryBound q) {tc te tD : ℕ} (hc : ∀ a b, coeCost a b ≤ tc)
    (he : ∀ a b, expCost a b ≤ te) (hD : ∀ sk c, decCost sk c ≤ tD) :
    OracleAdv.Timed.StepTimeBound
      (kemRedRun.tree.timed (fun t e => simDist P (encPk t.1.1.1 (liftE e))) kemDrawTime
        (kemStep P G g) (kemStepTime P G g coeCost expCost decCost) (fun k t => decide (k ∈ t.2))
        kemExtTime yInit B pk cs k)
      (1 + (T + q * (kemStepBound tc te tD (2 * q) + 11) + (kemExtBound (2 * q) + 2))) := by
  unfold kemRedRun.tree.timed
  refine (OracleAdv.Timed.stepTimeBound_delay (kemRed_timeBound_inv P G g pk cs k _ kemDrawTime
    (fun oa t e r => 1 + kemStepTime P G g coeCost expCost decCost pk cs oa t e r)
    (fun t => 1 + kemExtTime k t) (fun i => kemStepBound tc te tD (2 * i) + 4)
    (fun i => kemExtBound (2 * i) + 1)
    (fun _ _ h => Nat.add_le_add_right (kemStepBound_mono tc te tD (by omega)) _) ?_ ?_ B hB
    hq)).mono ?_
  · intro i t e oa r h1 h2
    have := kemStepTime_le P G g coeCost expCost decCost pk cs oa t h1 (by omega) e r hc he hD
    split <;> omega
  · intro i t h1 _
    have := kemExtTime_le k t h1
    omega
  · have h11 : kemStepBound tc te tD (2 * q) + 4 + 7 = kemStepBound tc te tD (2 * q) + 11 := by
      omega
    rw [h11]

/-- **Time of the IND-CCA reduction** at the derived costs: for a costed adversary `B'` of time
`T` erasing to an adversary `B` with at most `q` queries, the stage of the costed reduction,
which erases to `kemRed P G g B hB` (`kemRed.compile_tree`), takes at most
`2 + (T + q · (kemStepBound … (2q) + 11) + kemExtBound (2q) + 2)`, without hypotheses on the
costs of the step and of the extraction. -/
theorem kemRed.timeBound_cost [DecidableEq PK]
    (B : OracleAdv (OEv W SS C) (OOut S W K PK C) Bool) {q : ℕ}
    (hB : B.IsQueryBound q) (B' : OracleAdv.Timed (OEv W SS C) (OOut S W K PK C) Bool)
    (hB' : B'.erase = B) {T : ℕ} (hT : B'.TimeBound T) {tc te tD : ℕ}
    (hc : ∀ a b, coeCost a b ≤ tc) (he : ∀ a b, expCost a b ≤ te)
    (hD : ∀ sk c, decCost sk c ≤ tD) :
    (kemRed.tree.timed (fun t e => simDist P (encPk t.1.1.1 (liftE e))) kemDrawTime
        (kemStep P G g) (kemStepTime P G g coeCost expCost decCost) (fun k t => decide (k ∈ t.2))
        kemExtTime yInit ⟨B, hB⟩ B').TimeBound
      (2 + (T + q * (kemStepBound tc te tD (2 * q) + 11) + (kemExtBound (2 * q) + 2))) := by
  intro pk cs k
  have h := kemRedRun.timeBound_cost P G g coeCost expCost decCost pk cs k B' hT (hB' ▸ hB) hc
    he hD
  have h' := OracleAdv.Timed.stepTimeBound_delay (c := 1) h
  simp only [kemRed.tree.timed, kemRed.tree.run.tree.timed]
  exact h'.mono (by omega)

end Time

end KemCost

end CatCrypt.Crypto.AKE.PQXDHSquareKEM
