/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.PQXDHSquareKEM
public import CatCryptCore.Crypto.AKE.X3DHSquareGDHTimed

/-!
# Running time of the KEM reduction of the PQXDH square

Draft.
-/

@[expose] public section

set_option autoImplicit false

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
    (fun i t h => (hext t).trans (hE h)) B hB hq yInit (by simp [sizeY, yInit, pInit, X3DHSquare.rInit, initSt])

end Instance

end CatCrypt.Crypto.AKE.PQXDHSquareKEM
