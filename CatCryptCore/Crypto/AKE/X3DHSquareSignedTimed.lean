/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.AKE.X3DHSquareSigned
public import CatCryptCore.Crypto.UCOracleGameTimed
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveTimeBound
public import CatCryptCore.Tactics.AutoTime

/-!
# Running time of the forger of the signed X3DH square

The forger `forgeRed A p B pk` of `X3DHSquareSigned.lean` is `stopRed` at the step `forgeStep`
of the simulated filtered world, the forgery test `forgeryAt` and a final signing query: it runs
the oracle adversary `B` and stops at the first forgery. This module gives the costed form of the
generic reduction `stopRed`, derived by `derive_timed`, its running time for an arbitrary step
under a state invariant, and its running time at the forger.

**The costed reduction.** `derive_timed stopRed` defines `stopRed.timed`, generic in the state,
the step, the stop test and the final tree, and proves `stopRed.erase_timed`. The step of the
forger is the derived costed form of `forgeStep` (`derive_timed forgeStep`), with the tables of
its input state read at unit cost (zero cost companions), followed by the erasure of the costed
state it returns (`forgeStepC`, of step prefix `forgeStepCost`); it erases to `forgeStep`
(`forgeStepC_erase`). A draw of the real X3DH step `realStep` and of the signing layer is one
`rand` node of the costed tree; the decisions on the event and the lookups in the notices and in
the key-derivation table are priced by the cost model of `derive_timed`.

**The time.** A step of the real state machine adds at most one notice and one entry of the
key-derivation table (`realStep_length`), so on the paths through outcomes of positive
probability a state after `i` steps has at most `i` of each (`SzF`, `forgeStepC_ret`), and a step
from it takes time at most `80 + tp + 14 · i` (`forgeStepC_time`). The generic bound
`stopRed.timeBound_timed` gives, for an adversary of time `T` with at most `q` queries, a forger
of time at most `4 · T + q · (2 · (120 + tp + tv + tF + 14 · q) + 6) + 2` (`forgeRed_timeBound`):
linear in the time of the adversary plus a polynomial of degree two in its number of queries.
Each node of the adversary costs at most four units of the costed reduction, which gives the
factor `4`.

## Main results

* `stopRed.timed`, `stopRed.erase_timed` (derived), `stopRed.timeBound_timed`: the costed form of
  the generic reduction, its erasure and its time under a state invariant.
* `forgeRed_erase_timed`, `forgeRed_timeBound`: the costed forger erases to `forgeRed` and its
  time bound.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.AKE.X3DHSquareSigned

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.AKE.X3DHSquare
open OracleAdv.Timed

/-! ## The costed reduction that stops at the first output -/

derive_timed stopRed

section Generic

variable {σ E A D R Out : Type}

/-- **The time of `stopRed`** on the paths through outcomes of positive probability. Let `Inv i`
hold of the states reached after `i` steps, with the costs of computing the step and the stop test
from a state of `Inv i` together at most `F i` (`F` monotone), the time of the step at most `F i`,
the states the step returns in `Inv (i + 1)`, and the time of `fin` at most `tFin`. Then a costed
adversary `B` of time `T` with at most `q` queries, run from a state of `Inv i`, gives a costed
reduction of time at most `4 · T + q · (2 · F (i + q) + 6) + tFin + 1`. -/
theorem stopRed.timeBound_timed (step : σ → E → OracleAdv.Timed D R (A × σ))
    (stepCost : σ → E → ℕ) (stop : σ → E → Option Out) (stopCost : σ → E → ℕ)
    (fin : OracleAdv.Timed D R Out) (Inv : ℕ → σ → Prop) (F : ℕ → ℕ) (hF : Monotone F)
    (tFin : ℕ) (hcost : ∀ i t e, Inv i t → stepCost t e + stopCost t e ≤ F i)
    (htime : ∀ i t e, Inv i t → (step t e).TimeBoundOn supportOutcome (F i))
    (hret : ∀ i t e, Inv i t → (step t e).AllRetOn supportOutcome fun y => Inv (i + 1) y.2)
    (hfin : fin.TimeBoundOn supportOutcome tFin) (B : OracleAdv.Timed E A Bool) :
    ∀ {T q : ℕ} (i : ℕ) (t : σ), B.TimeBound T → B.erase.IsQueryBound q → Inv i t →
      StepTimeBoundOn supportOutcome (stopRed.timed step stepCost stop stopCost fin B t)
        (4 * T + q * (2 * F (i + q) + 6) + tFin + 1) := by
  induction B with
  | ret a =>
    intro T q i t _ _ _
    rw [stopRed.timed.eq_1]
    dsimp only
    exact ⟨by omega, hfin.mono (by omega)⟩
  | rand p c k ih =>
    intro T q i t hT hq hi
    rw [stopRed.timed.eq_1]
    dsimp only
    have hT1 := hT.1
    refine ⟨by omega, by omega, fun b _ => ?_⟩
    obtain ⟨hcb, hkb⟩ := hT.2 b
    have h := ih b i t hkb (hq b) hi
    have h1 := h.1
    dsimp only
    refine ⟨by omega, h.2.mono (by omega)⟩
  | query d c k ih =>
    intro T q i t hT hq hi
    obtain _ | q := q
    · exact absurd hq id
    rw [stopRed.timed.eq_1]
    dsimp only
    have hFi : F i ≤ F (i + (q + 1)) := hF (by omega)
    have hFq : F (i + 1 + q) = F (i + (q + 1)) := by rw [Nat.add_right_comm, Nat.add_assoc]
    have hc := hcost i t d hi
    have hb := timeBoundOn_bind (htime i t d hi) (hret i t d hi)
      (f := fun x => delay (2 + stopCost t d)
        (match stop t d with
          | some f => (0, OracleAdv.Timed.ret f)
          | none => delay (2 + c x.1)
              (stopRed.timed step stepCost stop stopCost fin (k x.1) x.2)))
      (n := 2 + stopCost t d + (2 + 4 * (T - 1) + q * (2 * F (i + (q + 1)) + 6) + tFin + 1))
      (fun x hx => by
        refine stepTimeBoundOn_delay ?_
        split
        · exact ⟨Nat.zero_le _, trivial⟩
        · obtain ⟨hcx, hkx⟩ := hT.2 x.1
          have h := ih x.1 (i + 1) x.2 hkx (hq x.1) hx
          rw [hFq] at h
          exact (stepTimeBoundOn_delay h).mono (by omega))
    have hsm : (q + 1) * (2 * F (i + (q + 1)) + 6) =
        q * (2 * F (i + (q + 1)) + 6) + (2 * F (i + (q + 1)) + 6) := Nat.succ_mul _ _
    exact (stepTimeBoundOn_delay hb).mono (by have := hT.1; omega)

end Generic

/-! ## The forger -/

section Forger

open CatCrypt.Crypto.PAKE.CPaceSquare (roAt)

variable {S W K VK SK Sig : Type} [Fintype S] [Nonempty S] [DecidableEq W] [Fintype K]
  [Nonempty K]

derive_timed forgeStep

/-- The sizes of the state of the simulated filtered world after `i` steps: at most `i` notices
and at most `i` entries of the key-derivation table. -/
def SzF (i : ℕ) (t : LSt W VK SK × RSt S W K) : Prop :=
  t.2.st.notices.length ≤ i ∧ t.2.ro.length ≤ i

omit [Fintype S] [Nonempty S] [DecidableEq W] [Fintype K] [Nonempty K] in
/-- An answer of the lazily sampled random function adds at most one entry to its table. -/
theorem roAt_length {D L : Type} [DecidableEq D] [Fintype L] [Nonempty L] (tb : List (D × L))
    (x : D) : ∀ q ∈ (roAt tb x).support, q.2.length ≤ tb.length + 1 := by
  intro q hq
  unfold roAt at hq
  split at hq
  · simp only [PMF.support_pure, Set.mem_singleton_iff] at hq
    subst hq
    grind
  · simp only [PMF.support_map, Set.mem_image] at hq
    obtain ⟨v, -, rfl⟩ := hq
    simp

/-- A step of the real X3DH state machine adds at most one notice and at most one entry of the
key-derivation table. -/
theorem realStep_length (A : AKEAlg S W) (s : RSt S W K) (g : OEv W) :
    ∀ q ∈ (realStep A s g).support, q.2.st.notices.length ≤ s.st.notices.length + 1 ∧
      q.2.ro.length ≤ s.ro.length + 1 := by
  intro q hq
  rcases g with ((⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) |
    (_ | _ | pid | ⟨sid, pid⟩ | pid | ⟨sid, pid⟩ | ⟨sid, pid, e⟩ | x)) <;>
    simp only [realStep, realGame, realGameK, realHonK, realAdvK, lazyKDF, PMF.support_map,
      Set.mem_image] at hq <;> obtain ⟨p, hp, rfl⟩ := hq
  · split_ifs at hp with hn
    · simp only [PMF.support_bind, PMF.support_map, PMF.support_pure, Set.mem_iUnion,
        Set.mem_image, Set.mem_singleton_iff] at hp
      obtain ⟨y, -, t, rfl, rfl⟩ := hp
      unfold addSession
      split <;> simp
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at hp
      subst hp
      simp
  · simp only [PMF.support_pure, Set.mem_singleton_iff] at hp
    subst hp
    simp
  · simp only [PMF.support_pure, Set.mem_singleton_iff] at hp
    subst hp
    simp
  · simp only [PMF.support_pure, Set.mem_singleton_iff] at hp
    subst hp
    simp only [pollStep]
    split <;> simp
  · obtain ⟨l, hl, rfl⟩ := hp
    obtain ⟨h1, -, h3, -, -⟩ := ltAt_support s pid l hl
    simp [h1, h3]
  · simp only [PMF.support_pure, Set.mem_singleton_iff] at hp
    subst hp
    simp
  · unfold corruptRStep at hp
    split_ifs at hp
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at hp
      subst hp
      simp
    · simp only [PMF.support_map, Set.mem_image] at hp
      obtain ⟨l, hl, rfl⟩ := hp
      obtain ⟨h1, -, h3, -, -⟩ := ltAt_support s pid l hl
      simp [corruptStep, h1, h3]
  all_goals try unfold completeStepK at hp
  all_goals try unfold sendStepK at hp
  all_goals try (repeat' split at hp)
  all_goals dsimp only
  all_goals first
    | (simp only [PMF.support_pure, Set.mem_singleton_iff] at hp; subst hp; simp)
    | (simp only [PMF.support_bind, PMF.support_map, Set.mem_iUnion, Set.mem_image] at hp
       obtain ⟨la, hla, lb, hlb, k', hk', rfl⟩ := hp
       obtain ⟨a1, -, a3, -, -⟩ := ltAt_support _ _ la hla
       obtain ⟨b1, -, b3, -, -⟩ := ltAt_support _ _ lb hlb
       have := roAt_length _ _ k' hk'
       simp only [keyed, setRec, b1, a1, b3, a3] at this ⊢
       grind)
    | (obtain ⟨k', hk', rfl⟩ := hp
       have := roAt_length _ _ k' hk'
       simp only at this ⊢
       grind)

/-- The costed step of the forger: the derived costed form of `forgeStep`, with the tables of its
input state read at unit cost (zero cost companions), the public value of an exponent of cost
`pubCost` and a verification of cost `verifyCost`, followed by the erasure of the costed state
it returns. -/
noncomputable def forgeStepC (A : SigAKEAlg S W VK SK Sig) (p : PartyId) (pk : VK)
    (pubCost : S → ℕ) (verifyCost : VK → W → Sig → ℕ) (t : LSt W VK SK × RSt S W K)
    (e : SEv W Sig) : OracleAdv.Timed W Sig (SOut S W K VK Sig × (LSt W VK SK × RSt S W K)) :=
  ((forgeStep.timed A p pk t e (fun _ => 0) (fun _ => 0) (fun _ => 0) pubCost (fun _ => 0)
      verifyCost (fun _ => 0) (fun _ => 0)).2.bind fun y =>
    (0, .ret (y.1, (LSt.mk y.2.1.1.1 y.2.1.2.1.1 y.2.1.2.2.1.1 y.2.1.2.2.2,
      RStT.mk (St.mk y.2.2.1.1.1 y.2.2.1.2.1.1 y.2.2.1.2.2.1 y.2.2.1.2.2.2)
        y.2.2.2.1.1 y.2.2.2.2.1.1 y.2.2.2.2.2)))).2

/-- The step cost of `forgeStepC`: the step prefix of the derived costed form of `forgeStep`. -/
noncomputable def forgeStepCost (A : SigAKEAlg S W VK SK Sig) (p : PartyId) (pk : VK)
    (pubCost : S → ℕ) (verifyCost : VK → W → Sig → ℕ) (t : LSt W VK SK × RSt S W K)
    (e : SEv W Sig) : ℕ :=
  (forgeStep.timed A p pk t e (fun _ => 0) (fun _ => 0) (fun _ => 0) pubCost (fun _ => 0)
    verifyCost (fun _ => 0) (fun _ => 0)).1

/-- The costed step erases to `forgeStep`. -/
theorem forgeStepC_erase (A : SigAKEAlg S W VK SK Sig) (p : PartyId) (pk : VK)
    (pubCost : S → ℕ) (verifyCost : VK → W → Sig → ℕ) (t : LSt W VK SK × RSt S W K)
    (e : SEv W Sig) : (forgeStepC A p pk pubCost verifyCost t e).erase = forgeStep A p pk t e := by
  rw [forgeStepC, erase_bind]
  exact forgeStep.erase_timed A p pk t e _ _ _ _ _ _ _ _

/-- The step prefix of the costed step is at most `40 + tv` for verifications of cost at most
`tv`. -/
theorem forgeStepCost_le (A : SigAKEAlg S W VK SK Sig) (p : PartyId) (pk : VK)
    (pubCost : S → ℕ) (verifyCost : VK → W → Sig → ℕ) {tv : ℕ}
    (hv : ∀ a b c, verifyCost a b c ≤ tv) (t : LSt W VK SK × RSt S W K) (e : SEv W Sig) :
    forgeStepCost A p pk pubCost verifyCost t e ≤ 40 + tv := by
  unfold forgeStepCost forgeStep.timed
  have := hv pk
  split <;> grind

omit [Fintype S] [Nonempty S] [DecidableEq W] [Fintype K] [Nonempty K] in
/-- A costed tree followed by a return of zero step cost has no step prefix. -/
@[simp] theorem bindRet_fst {D R α β : Type} (X : OracleAdv.Timed D R α) (g : α → β) :
    (X.bind fun r => (0, OracleAdv.Timed.ret (g r))).1 = 0 := by
  cases X <;> rfl

omit [Fintype S] [Nonempty S] [DecidableEq W] [Fintype K] [Nonempty K] in
/-- A costed tree followed by a return of zero step cost keeps its time bound. -/
theorem bindRet_timeBound {D R α β : Type} {X : OracleAdv.Timed D R α} {n : ℕ}
    (h : X.TimeBound n) (g : α → β) :
    (X.bind fun r => (0, OracleAdv.Timed.ret (g r))).2.TimeBound n := by
  have := timeBound_bind h (f := fun r => (0, OracleAdv.Timed.ret (g r))) (n := 0)
    (fun _ => ⟨le_rfl, trivial⟩)
  simpa [StepTimeBound] using this.2

omit [Fintype S] [Nonempty S] [DecidableEq W] [Fintype K] [Nonempty K] in
/-- The leaves of a costed tree followed by a return of `g` are the images under `g` of its
leaves. -/
theorem bindRet_allRetOn {D R α β : Type} {F : OutcomeFilter} {X : OracleAdv.Timed D R α}
    {g : α → β} {P : β → Prop} (h : X.AllRetOn F fun r => P (g r)) :
    (X.bind fun r => (0, OracleAdv.Timed.ret (g r))).2.AllRetOn F P := by
  induction X with
  | ret a => exact h
  | rand p c k ih => exact fun b hb => ih b (h b hb)
  | query d c k ih => exact fun r => ih r (h r)

omit [Fintype S] [Nonempty S] [DecidableEq W] [Fintype K] [Nonempty K] in
/-- The derived costed form of `postF`, with zero cost companions, takes time at most `20`. -/
theorem postF_time (A : SigAKEAlg S W VK SK Sig) (p : PartyId) (pk : VK) (l : LSt W VK SK)
    (o : OOut S W K) :
    StepTimeBound (postF.timed A p pk l o (fun _ => 0) (fun _ => 0) (fun _ => 0)) 20 := by
  unfold postF.timed
  time_bound

/-- The time of the costed step from a state of `SzF i` is at most `80 + tp + 14 · i` for public
values of cost at most `tp`. -/
theorem forgeStepC_time (A : SigAKEAlg S W VK SK Sig) (p : PartyId) (pk : VK)
    (pubCost : S → ℕ) (verifyCost : VK → W → Sig → ℕ) {tp : ℕ} (hp : ∀ x, pubCost x ≤ tp)
    {i : ℕ} (t : LSt W VK SK × RSt S W K) (ht : SzF i t) (e : SEv W Sig) :
    (forgeStepC A p pk pubCost verifyCost t e).TimeBound (80 + tp + 14 * i) := by
  obtain ⟨hn, hm⟩ := ht
  have h1 := List.get?Internal.timedCost_le t.2.st.notices t.2.st.cursor
  have h2 := fun (q : Notice → Bool) => List.any.timedCost_le t.2.st.notices q (fun _ => 4)
    (k := 4) (fun _ => le_rfl)
  have h3 := fun x => List.lookup.timedCost_le x t.2.ro
  unfold forgeStepC forgeStep.timed
  simp only [OracleAdv.Timed.bind, OracleAdv.Timed.timeBound_rand_iff]
  refine ⟨by omega, fun a => ⟨?_, OracleAdv.Timed.TimeBound.mono (m := 30) ?_ ?_⟩⟩
  · rcases a with ⟨l, (h | a)⟩
    · cases h <;> dsimp only <;> (repeat' split) <;> omega
    · cases a <;> dsimp only <;> (repeat' split) <;> grind
  · refine ⟨by omega, fun q => ?_⟩
    have hP := postF_time A p pk a.1 q.1
    simp only [bindRet_fst]
    have := hP.1
    exact ⟨by omega, bindRet_timeBound (bindRet_timeBound (hP.2.mono (by omega)) _) _⟩
  · rcases a with ⟨l, (h | a)⟩
    · cases h <;> dsimp only <;> (repeat' split) <;> omega
    · cases a <;> dsimp only <;> (repeat' split) <;> grind

/-- The states returned by the costed step from a state of `SzF i`, on the paths through outcomes
of positive probability, are states of `SzF (i + 1)`. -/
theorem forgeStepC_ret (A : SigAKEAlg S W VK SK Sig) (p : PartyId) (pk : VK)
    (pubCost : S → ℕ) (verifyCost : VK → W → Sig → ℕ) {i : ℕ}
    (t : LSt W VK SK × RSt S W K) (ht : SzF i t) (e : SEv W Sig) :
    (forgeStepC A p pk pubCost verifyCost t e).AllRetOn supportOutcome
      fun y => SzF (i + 1) y.2 := by
  unfold forgeStepC forgeStep.timed
  simp only [OracleAdv.Timed.bind]
  intro a _ q hq
  obtain ⟨h1, h2⟩ := realStep_length A.toAKEAlg t.2 a.2 q hq
  refine bindRet_allRetOn (bindRet_allRetOn (allRetOn_of_forall _ (fun r => ?_) _))
  exact ⟨by have := ht.1; dsimp only; omega, by have := ht.2; dsimp only; omega⟩

/-- **Erasure of the costed forger.** The derived costed form of `stopRed` at the costed step
`forgeStepC`, of cost `forgeStepCost`, the forgery test `forgeryAt`, of cost `stopCost`, and the
final signing query at `A.pub (Classical.arbitrary S)`, of zero step costs, run from `fInit`,
erases to the forger `forgeRed A p B.erase pk`. -/
theorem forgeRed_erase_timed (A : SigAKEAlg S W VK SK Sig) (p : PartyId) (pk : VK)
    (pubCost : S → ℕ) (verifyCost : VK → W → Sig → ℕ)
    (stopCost : LSt W VK SK × RSt S W K → SEv W Sig → ℕ)
    (B : OracleAdv.Timed (SEv W Sig) (SOut S W K VK Sig) Bool) :
    (stopRed.timed (forgeStepC A p pk pubCost verifyCost)
        (forgeStepCost A p pk pubCost verifyCost) (fun t e => forgeryAt A p pk t.1 e) stopCost
        (ofAdv (.query (A.pub (Classical.arbitrary S)) fun σ =>
          .ret (A.pub (Classical.arbitrary S), σ))) B fInit).2.erase =
      forgeRed A p B.erase pk := by
  simp only [stopRed.erase_timed, erase_ofAdv, forgeStepC_erase]
  rfl

/-- **The time of the forger.** For a costed oracle adversary `B` of time `T` with at most `q`
queries, public values of cost at most `tp`, verifications of cost at most `tv` and a forgery
test of cost at most `tF`, the costed forger of `forgeRed_erase_timed` takes time at most
`4 · T + q · (2 · (120 + tp + tv + tF + 14 · q) + 6) + 2` on the paths through outcomes of
positive probability: linear in the time of the adversary plus a polynomial of degree two in its
number of queries. A step after `i` steps costs at most `120 + tp + tv + tF + 14 · i`, since the
notices and the key-derivation table grow by at most one entry per step (`realStep_length`). -/
theorem forgeRed_timeBound (A : SigAKEAlg S W VK SK Sig) (p : PartyId) (pk : VK)
    (pubCost : S → ℕ) (verifyCost : VK → W → Sig → ℕ)
    (stopCost : LSt W VK SK × RSt S W K → SEv W Sig → ℕ) {tp tv tF T q : ℕ}
    (hp : ∀ x, pubCost x ≤ tp) (hv : ∀ a b c, verifyCost a b c ≤ tv)
    (hs : ∀ t e, stopCost t e ≤ tF)
    (B : OracleAdv.Timed (SEv W Sig) (SOut S W K VK Sig) Bool) (hB : B.TimeBound T)
    (hq : B.erase.IsQueryBound q) :
    StepTimeBoundOn supportOutcome
      (stopRed.timed (forgeStepC A p pk pubCost verifyCost)
        (forgeStepCost A p pk pubCost verifyCost) (fun t e => forgeryAt A p pk t.1 e) stopCost
        (ofAdv (.query (A.pub (Classical.arbitrary S)) fun σ =>
          .ret (A.pub (Classical.arbitrary S), σ))) B fInit)
      (4 * T + q * (2 * (120 + tp + tv + tF + 14 * q) + 6) + 2) := by
  have h := stopRed.timeBound_timed (forgeStepC A p pk pubCost verifyCost)
    (forgeStepCost A p pk pubCost verifyCost) (fun t e => forgeryAt A p pk t.1 e) stopCost
    (ofAdv (.query (A.pub (Classical.arbitrary S)) fun σ =>
      .ret (A.pub (Classical.arbitrary S), σ))) SzF (fun i => 120 + tp + tv + tF + 14 * i)
    (fun _ _ h => by dsimp only; omega) 1
    (fun i t e _ => by
      have := forgeStepCost_le A p pk pubCost verifyCost hv t e
      have := hs t e
      omega)
    (fun i t e ht => ((forgeStepC_time A p pk pubCost verifyCost hp t ht e).mono
      (by omega)).timeBoundOn _)
    (fun i t e ht => forgeStepC_ret A p pk pubCost verifyCost t ht e)
    ⟨le_rfl, fun _ => ⟨le_rfl, trivial⟩⟩ B 0 fInit hB hq
    ⟨by simp [fInit, rInit, initSt], by simp [fInit, rInit]⟩
  simpa using h

end Forger

end CatCrypt.Crypto.AKE.X3DHSquareSigned
