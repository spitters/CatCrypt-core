/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.PAKE.CPaceSquare
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveSimulator
public import CatCryptCore.Tactics.DeriveTimeBound
public import CatCryptCore.Crypto.UCSimulatorCostGraded

/-!
# Running time of the CPace simulator

`derive_reduction` builds the costed form of the multi-call simulator `simProt G` of
`CPaceSquare.lean`, whose state holds the table of `H1` (a function of the passwords, sampled at
the first activation), the tables of the sessions and the lists of candidates and programmed
inputs, at the costed state in which each stored function carries a cost companion.
`derive_simulator` builds the costed form of the bundled simulator `cpaceSim G` from it.

The table of `H2` and the list of programmed inputs grow by at most one entry per activation,
and each update of a table of the parties adds three units to its cost companion. The invariant
`SimInv i` bounds these lengths and companions by `i` and `3 i` after `i` activations, and keeps
the queried passwords distinct, so that a search of the candidates costs at most
`(15 + t_coe + t_exp) · card Pw + 1`. A step from a state of `SimInv i` then costs at most
`a + b i` (`simProt.timeBoundGraded_timed`), the graded form for simulators whose state grows
with the activations, and `derive_simulator` lifts it to `cpaceSim`.

No module imports this file.

## Main results

* `simProt.timed`, `simProt.erase_timed`: the costed multi-call simulator and its erasure.
* `simProt.timeBoundGraded_timed`: its graded time bound on the invariant `SimInv`.
* `cpaceSim.timed`, `cpaceSim.erase_timed`, `cpaceSim.timeBoundGraded_timed`: the costed bundled
  simulator, its erasure, and its graded time bound.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.PAKE.CPaceSquare

set_option maxHeartbeats 1000000 in
-- The derivation prices and erases the nested matches of `simStart` and `simCore` over a state
-- of eight fields, five of them holding functions; it exceeds the default budget of the
-- command (it needs between 400000 and 1000000 heartbeats).
derive_reduction simProt

derive_time_bound simProt.finish.treeHat

derive_time_bound simProt.resume.treeHat

/-- The search `List.find?` costs at most `4 + B` units per element and one more when the
predicate costs at most `B`. -/
theorem find?_timedCost_le {α : Type} (p : α → Bool) (pc : α → ℕ) {B : ℕ}
    (h : ∀ a, pc a ≤ B) (l : List α) :
    List.find?.timedCost p pc l ≤ (4 + B) * l.length + 1 := by
  induction l with
  | nil => simp [List.find?.timedCost.eq_1]
  | cons a l ih =>
    rw [List.find?.timedCost.eq_2]
    have := h a
    split <;> simp only [List.length_cons, Nat.mul_succ] <;> omega

/-- The search `List.findSome?` costs at most `4 + B` units per element and one more when the
function costs at most `B`. -/
theorem findSome?_timedCost_le {α β : Type} (f : α → Option β) (fc : α → ℕ) {B : ℕ}
    (h : ∀ a, fc a ≤ B) (l : List α) :
    List.findSome?.timedCost f fc l ≤ (4 + B) * l.length + 1 := by
  induction l with
  | nil => simp [List.findSome?.timedCost.eq_1]
  | cons a l ih =>
    rw [List.findSome?.timedCost.eq_2]
    have := h a
    split <;> simp only [List.length_cons, Nat.mul_succ] <;> omega

/-- The subtraction `1 - p` costs at most five units at `p ≤ 1`. -/
theorem sub_one_timedCost_le {p : ℕ} (hp : p ≤ 1) : Nat.sub.timedCost 1 p ≤ 5 := by
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hp with rfl | rfl <;>
    simp [Nat.sub.timedCost.eq_1, Nat.sub.timedCost.eq_2]

/-- The maximum of zero over a finite type is zero. -/
theorem sup_zero {γ : Type} [Fintype γ] : (Finset.univ.sup fun _ : γ => (0 : ℕ)) = 0 :=
  (Finset.sup_eq_bot_iff _ _).2 fun _ _ => rfl

/-- The costed core state of the simulator: the table of `H1` with its cost companion, the
queried passwords, the four tables of the parties with their cost companions, the table of `H2`
and the phase. -/
abbrev CoreHat (S W Pw K : Type) [Monoid S] : Type :=
  Option ((Pw → Sˣ) × (Pw → ℕ)) × List Pw ×
    ((UCTransparent.FPAKE.PartyId →
        Option (UCTransparent.FPAKE.PartyId × UCTransparent.FPAKE.Role)) ×
      (UCTransparent.FPAKE.PartyId → ℕ)) ×
    ((UCTransparent.FPAKE.PartyId → Option S) × (UCTransparent.FPAKE.PartyId → ℕ)) ×
    ((UCTransparent.FPAKE.PartyId → Bool) × (UCTransparent.FPAKE.PartyId → ℕ)) ×
    ((UCTransparent.FPAKE.PartyId → Option (UCTransparent.FPAKE.Role × W × W)) ×
      (UCTransparent.FPAKE.PartyId → ℕ)) ×
    List (Inp W × K) × Phase W K

/-- The invariant of the costed core state after `i` activations: the queried passwords are
distinct, the table of `H2` has at most `i` entries, the cost companions of the four tables of
the parties are at most `3 i`, and only the parties `0` and `1` hold a secret. -/
def CoreInv {S W Pw K : Type} [Monoid S] (i : ℕ) (c : CoreHat S W Pw K) : Prop :=
  c.2.1.Nodup ∧ c.2.2.2.2.2.2.1.length ≤ i ∧ (∀ p, c.2.2.1.2 p ≤ 3 * i) ∧
    (∀ p, c.2.2.2.1.2 p ≤ 3 * i) ∧ (∀ p, c.2.2.2.2.1.2 p ≤ 3 * i) ∧
    (∀ p, c.2.2.2.2.2.1.2 p ≤ 3 * i) ∧ (∀ p, (c.2.2.2.1.1 p).isSome → p ≤ 1)

/-- The invariant of the costed state of the simulator after `i` activations: the invariant of
the core, and at most `i` inputs programmed by late tests. -/
def SimInv {S W Pw K : Type} [Monoid S] (i : ℕ) (s : CoreHat S W Pw K × List (Inp W × K)) :
    Prop :=
  CoreInv i s.1 ∧ s.2.length ≤ i

/-- The invariant of the core holds at every later activation count. -/
theorem CoreInv.succ {S W Pw K : Type} [Monoid S] {i : ℕ} {c : CoreHat S W Pw K}
    (h : CoreInv i c) : CoreInv (i + 1) c := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨h1, by omega, fun p => by grind, fun p => by grind, fun p => by grind,
    fun p => by grind, h7⟩

section Time

open CatCrypt.Core
open SPTree.Timed (stepTime_bind_bind_ret_le allRet_bind_bind_ret)

-- The costed steps of `simProt` are compiled through the auxiliary matchers of its source, and
-- the bounds below unfold them by name.
set_option linter.auxLemma false

variable {S W Pw K : Type} [Field S] [Fintype S] [DecidableEq S] [DecidableEq W] [Fintype Pw]
  [DecidableEq Pw] [Fintype K] [Nonempty K] [Inhabited K] (G : DHExtract.DHGroup S W)
  (coeCost : S ≃ W → S → ℕ) (hAppendCost : List Pw → List Pw → ℕ) (expCost : W → S → ℕ)

omit [Fintype S] [DecidableEq S] [Fintype Pw] [DecidableEq Pw] [Inhabited K] in
/-- The fresh `H2` query `y` (`h2Core`): two late-test searches over the queried passwords,
each within `F`, the reads of the two tables of the parties at their cost companions `pc`
and `zc`, at most `T`, and the sample of a fresh value. -/
theorem h2Core_time (x : ((Pw → Sˣ) × (Pw → ℕ)) × CoreHat S W Pw K) (y : Inp W)
    (hx0 : x.1.2 = fun _ => 0) {tc te F T : ℕ} (hc : ∀ a b, coeCost a b ≤ tc)
    (he : ∀ a b, expCost a b ≤ te)
    (key : ∀ (p : Pw → Bool) (g : Pw → ℕ), (∀ a, g a ≤ te) →
      List.find?.timedCost p (fun pw => 1 + (3 + coeCost G.pub 0 + (2 + (g pw + (4 + 0)) + 1)))
        x.2.2.1 ≤ F)
    {pc zc : UCTransparent.FPAKE.PartyId → ℕ} (hp : ∀ p, pc p ≤ T) (hz : ∀ p, zc p ≤ T) :
    SPTree.Timed.stepTime (simProt.start.tree.match_10.timed G DFunLike.coe coeCost x y expCost
      pc zc) ≤ 2 * F + 4 * T + 20 := by
  have := hp 0
  have := hp 1
  have := hz 0
  have := hz 1
  have := hc G.pub 0
  simp only [simProt.start.tree.match_10.timed, hx0, SPTree.Timed.stepTime, SPTree.Timed.delay,
    ite_true, one_ne_zero, ite_false]
  rcases x.2.2.2.2.2.2.1.1 0 with _ | T0 <;> rcases x.2.2.2.2.1.1 0 with _ | z0 <;>
    rcases x.2.2.2.2.2.2.1.1 1 with _ | T1 <;> rcases x.2.2.2.2.1.1 1 with _ | z1 <;>
    dsimp only <;> (try split_ifs) <;> (try split) <;>
    (try grw [key _ _ (fun _ => he _ _)]) <;> (try grw [key _ _ (fun _ => he _ _)]) <;>
    (try simp only [Option.map_none]) <;> (try split) <;>
    (try simp only [SPTree.Timed.time_ret, SPTree.Timed.time_sample, sup_zero,
      Nat.add_zero]) <;> omega

omit [Fintype S] [DecidableEq S] [Fintype Pw] in
/-- The adversary's `send pid m` (`sendCore`): the reads of the tables of the parties at their
cost companions, at most `T`, the subtraction `1 - pid` for a party `pid ≤ 1` holding a secret,
and the search of the table of `H2` for a matching query, each entry within `9 + F`. -/
theorem send_time (x : ((Pw → Sˣ) × (Pw → ℕ)) × CoreHat S W Pw K) (pid : ℕ) (m : W)
    (hx0 : x.1.2 = fun _ => 0) (h01 : ∀ p, (x.2.2.2.2.1.1 p).isSome → p ≤ 1)
    {tc te F T : ℕ} (hc : ∀ a b, coeCost a b ≤ tc) (he : ∀ a b, expCost a b ≤ te)
    (key : ∀ (p : Pw → Bool) (g : Pw → ℕ), (∀ a, g a ≤ te) →
      List.find?.timedCost p (fun pw => 1 + (3 + coeCost G.pub 0 + (2 + (g pw + (4 + 0)) + 1)))
        x.2.2.1 ≤ F)
    {zc ic kc pc : UCTransparent.FPAKE.PartyId → ℕ} (hz : ∀ p, zc p ≤ T) (hi : ∀ p, ic p ≤ T)
    (hk : ∀ p, kc p ≤ T) :
    SPTree.Timed.stepTime (simProt.start.tree.match_12.timed G DFunLike.coe coeCost
      HAppend.hAppend hAppendCost x (.send pid m) expCost zc ic kc pc) ≤
      40 + 4 * tc + 4 * T + (9 + F) * x.2.2.2.2.2.2.2.1.length := by
  have kfs : ∀ (f : Inp W × K → Option (Pw × K)) (pp : Inp W × K → Pw → Bool)
      (w : Inp W × K → W) (z : S) (T' : UCTransparent.FPAKE.Role × W × W),
      List.findSome?.timedCost f (fun e => 2 + if e.1.tr = T' then 1 + (1 +
        List.find?.timedCost (pp e) (fun pw => 1 + (3 + coeCost G.pub 0 +
          (2 + (expCost (w e) (z * (↑(x.1.1 pw))⁻¹) + (4 + 0)) + 1))) x.2.2.1 + 1) else 0)
        x.2.2.2.2.2.2.2.1 ≤ (9 + F) * x.2.2.2.2.2.2.2.1.length + 1 := by
    intro f pp w z T'
    have := findSome?_timedCost_le f (fun e => 2 + if e.1.tr = T' then 1 + (1 +
        List.find?.timedCost (pp e) (fun pw => 1 + (3 + coeCost G.pub 0 +
          (2 + (expCost (w e) (z * (↑(x.1.1 pw))⁻¹) + (4 + 0)) + 1))) x.2.2.1 + 1) else 0)
      (B := 5 + F) (fun e => by
        have := key (pp e) (fun pw => expCost (w e) (z * (↑(x.1.1 pw))⁻¹)) (fun _ => he _ _)
        split_ifs <;> omega) x.2.2.2.2.2.2.2.1
    rw [show 4 + (5 + F) = 9 + F by omega] at this
    exact this
  have := hz pid
  have := hz (1 - pid)
  have := hi pid
  have := hk pid
  have := hc G.pub 0
  simp only [simProt.start.tree.match_12.timed, hx0, SPTree.Timed.stepTime,
    SPTree.Timed.delay, SPTree.Timed.time_ret]
  rcases hzs : x.2.2.2.2.1.1 pid with _ | z
  · dsimp only
    omega
  · have hp1 : pid ≤ 1 := h01 pid (by simp [hzs])
    have := sub_one_timedCost_le hp1
    have := hc G.pub z
    rcases x.2.2.2.1.1 pid with _ | ⟨_, role⟩
    · dsimp only
      omega
    · dsimp only
      split_ifs <;> (try split) <;> (try (rename_i w _; have := hc G.pub w)) <;>
        (try grw [kfs _ _ _ z _]) <;> omega

omit [DecidableEq S] in
/-- The core step from a core state of the invariant `CoreInv i`, with the zero cost companion
of the table of `H1`, costs at most `60 + 10 t_coe + t_app + 2 F + 30 i + F i`. -/
theorem core_time (e : OEv Pw W) (i : ℕ) (x : ((Pw → Sˣ) × (Pw → ℕ)) × CoreHat S W Pw K)
    (hx0 : x.1.2 = fun _ => 0) (hx : CoreInv i x.2) {tc th te : ℕ}
    (hc : ∀ a b, coeCost a b ≤ tc) (hh : ∀ a b, hAppendCost a b ≤ th)
    (he : ∀ a b, expCost a b ≤ te) {F : ℕ} (hF : (15 + tc + te) * Fintype.card Pw + 1 ≤ F) :
    SPTree.Timed.stepTime (simProt.start.tree.match_13.timed G e DFunLike.coe coeCost
        HAppend.hAppend hAppendCost x expCost) ≤
      60 + 10 * tc + th + 2 * F + 30 * i + F * i := by
  obtain ⟨hn, hl, hi, hz, hk, hp, h01⟩ := hx
  rcases e with h | a
  · simp only [simProt.start.tree.match_13.timed, simProt.start.tree.match_9.timed]
    generalize honPub h = o
    rcases o with _ | ⟨sid, pid, peer, role⟩
    · simp [SPTree.Timed.stepTime, SPTree.Timed.delay, SPTree.Timed.bind, SPTree.Timed.time_ret]
      omega
    · have := hi pid
      dsimp only
      split_ifs <;>
        simp [SPTree.Timed.stepTime, SPTree.Timed.delay, SPTree.Timed.bind,
          SPTree.Timed.time_ret, SPTree.Timed.time_sample, sup_zero] <;> omega
  · simp only [simProt.start.tree.match_13.timed]
    cases a with
    | idle =>
      simp [simProt.start.tree.match_12.timed, SPTree.Timed.stepTime, SPTree.Timed.delay,
        SPTree.Timed.time_ret]
      omega
    | poll =>
      simp [simProt.start.tree.match_12.timed, SPTree.Timed.stepTime, SPTree.Timed.delay,
        SPTree.Timed.time_ret]
      omega
    | msg pid =>
      have := hz pid
      simp only [simProt.start.tree.match_12.timed]
      split <;> rename_i heq <;>
        simp [SPTree.Timed.stepTime, SPTree.Timed.delay, SPTree.Timed.time_ret, heq] <;>
        grind
    | h1 pw =>
      have := hc (G.pub) (x.1.1 pw)
      have := hh x.2.2.1 [pw]
      simp only [simProt.start.tree.match_12.timed, hx0]
      split_ifs <;> simp [SPTree.Timed.stepTime, SPTree.Timed.delay, SPTree.Timed.time_ret] <;>
        omega
    | h2 y =>
      have hlk := List.lookup.timedCost_le y x.2.2.2.2.2.2.2.1
      have hcands := Nat.mul_le_mul_left (15 + tc + te) hn.length_le_card
      have key : ∀ (p : Pw → Bool) (g : Pw → ℕ), (∀ a, g a ≤ te) →
          List.find?.timedCost p (fun pw => 1 + (3 + coeCost G.pub 0 + (2 + (g pw + (4 + 0)) + 1)))
            x.2.2.1 ≤ F := fun p g hg => by
        have := find?_timedCost_le p
          (fun pw => 1 + (3 + coeCost G.pub 0 + (2 + (g pw + (4 + 0)) + 1))) (B := 11 + tc + te)
          (fun a => by have := hg a; have := hc G.pub 0; omega) x.2.2.1
        rw [show 4 + (11 + tc + te) = 15 + tc + te by omega] at this
        omega
      simp only [simProt.start.tree.match_12.timed, simProt.start.tree.match_11.timed]
      split
      · simp [SPTree.Timed.stepTime, SPTree.Timed.delay, SPTree.Timed.time_ret]
        omega
      · have := h2Core_time G coeCost expCost x y hx0 hc he key hp hz
        simp only [SPTree.Timed.stepTime, SPTree.Timed.delay] at this ⊢
        omega
    | send pid m =>
      have key : ∀ (p : Pw → Bool) (g : Pw → ℕ), (∀ a, g a ≤ te) →
          List.find?.timedCost p (fun pw => 1 + (3 + coeCost G.pub 0 + (2 + (g pw + (4 + 0)) + 1)))
            x.2.2.1 ≤ F := fun p g hg => by
        have := find?_timedCost_le p
          (fun pw => 1 + (3 + coeCost G.pub 0 + (2 + (g pw + (4 + 0)) + 1))) (B := 11 + tc + te)
          (fun a => by have := hg a; have := hc G.pub 0; omega) x.2.2.1
        have hcands := Nat.mul_le_mul_left (15 + tc + te) hn.length_le_card
        rw [show 4 + (11 + tc + te) = 15 + tc + te by omega] at this
        omega
      have := send_time G coeCost hAppendCost expCost x pid m hx0 h01 hc he key
        (pc := x.2.2.2.2.2.2.1.2) hz hi hk
      have hm := Nat.mul_le_mul_left (9 + F) hl
      simp only [Nat.add_mul] at this hm
      simp only [SPTree.Timed.stepTime, SPTree.Timed.delay] at this ⊢
      omega

/-- The updated cost companion of a table of the parties stays within `3 (i + 1)`. -/
theorem update_cost_le {c : UCTransparent.FPAKE.PartyId → ℕ} {i : ℕ} (h : ∀ p, c p ≤ 3 * i)
    (pid : UCTransparent.FPAKE.PartyId) :
    ∀ p, (2 + if _ : p = pid then 0 else 1 + c p) ≤ 3 * (i + 1) := by
  intro p
  have := h p
  split <;> omega

omit [DecidableEq S] [Fintype Pw] in
/-- The core step preserves the invariant of the core, one activation later. -/
theorem core_allRet (e : OEv Pw W) (i : ℕ) (x : ((Pw → Sˣ) × (Pw → ℕ)) × CoreHat S W Pw K)
    (hx : CoreInv i x.2) :
    SPTree.Timed.AllRet (fun y => CoreInv (i + 1) y.1)
      (simProt.start.tree.match_13.timed G e DFunLike.coe coeCost HAppend.hAppend hAppendCost x
        expCost).2 := by
  have hs := hx.succ
  obtain ⟨hn, hl, hi, hz, hk, hp, h01⟩ := hx
  rcases e with h | a
  · simp only [simProt.start.tree.match_13.timed, simProt.start.tree.match_9.timed,
      SPTree.Timed.delay, SPTree.Timed.allRet_bind]
    generalize honPub h = o
    rcases o with _ | ⟨sid, pid, peer, role⟩
    · exact hs
    · dsimp only
      split_ifs with hc ha
      · simp only [SPTree.Timed.AllRet, SPTree.Timed.allRet_bind]
        intro b
        refine ⟨hn, by dsimp only; omega, update_cost_le hi pid, update_cost_le hz pid,
          hs.2.2.2.2.1, hs.2.2.2.2.2.1, fun p hp' => ?_⟩
        by_cases hpp : p = pid
        · exact hpp ▸ hc.2.1
        · simp only [Function.update_of_ne hpp] at hp'
          exact h01 p hp'
      · simp only [SPTree.Timed.AllRet, SPTree.Timed.allRet_bind]
        exact ⟨hn, by dsimp only; omega, update_cost_le hi pid, hs.2.2.2.1, hs.2.2.2.2.1,
          hs.2.2.2.2.2.1, h01⟩
      · exact hs
  · simp only [simProt.start.tree.match_13.timed, simProt.start.tree.match_12.timed,
      SPTree.Timed.delay]
    cases a with
    | idle => exact hs
    | poll => exact hs
    | msg pid => exact hs
    | h1 pw =>
      simp only [SPTree.Timed.AllRet]
      refine ⟨?_, hs.2⟩
      split_ifs with hm
      · exact hn
      · exact hn.append (List.nodup_singleton pw) (by simpa using hm)
    | h2 y =>
      simp only [simProt.start.tree.match_11.timed, simProt.start.tree.match_10.timed,
        SPTree.Timed.delay]
      repeat' split
      all_goals first
        | exact hs
        | exact ⟨hn, by dsimp only; omega, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1,
            update_cost_le hp _, h01⟩
        | exact fun b => ⟨hn, by dsimp only; simp only [List.length_cons]; omega, hs.2.2.1,
            hs.2.2.2.1, hs.2.2.2.2.1, hs.2.2.2.2.2.1, h01⟩
    | send pid m =>
      simp only [SPTree.Timed.AllRet]
      repeat' split
      all_goals first
        | exact hs
        | exact ⟨hn, by dsimp only; omega, hs.2.2.1, hs.2.2.2.1, update_cost_le hk pid,
            hs.2.2.2.2.2.1, h01⟩
        | exact ⟨hn, by dsimp only; omega, hs.2.2.1, hs.2.2.2.1, update_cost_le hk pid,
            update_cost_le hp pid, h01⟩

omit [DecidableEq W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- The table of `H1` after its sampling step carries the zero cost companion, and the rest of
the core state is that of the input. -/
theorem tdStep_allRet (s : CoreHat S W Pw K × List (Inp W × K)) {i : ℕ} (hc : CoreInv i s.1) :
    SPTree.Timed.AllRet (fun y => y.1.2 = (fun _ => 0) ∧ CoreInv i y.2)
      (simProt.start.tree.match_8.timed
        ({ td := Option.map (fun x => x.1) s.1.1, cands := s.1.2.1, info := s.1.2.2.1.1,
            zs := s.1.2.2.2.1.1, keyed := s.1.2.2.2.2.1.1, pend := s.1.2.2.2.2.2.1.1,
            h2 := s.1.2.2.2.2.2.2.1, phase := s.1.2.2.2.2.2.2.2 }, s.2) s.1).2 := by
  obtain ⟨hn, hl, hi, hz, hk, hp, h01⟩ := hc
  simp only [simProt.start.tree.match_8.timed, SPTree.Timed.delay]
  rcases s.1.1 with _ | ⟨t, tc⟩
  · exact fun _ => ⟨rfl, hn, hl, hi, hz, hk, hp, h01⟩
  · exact ⟨rfl, hn, hl, hi, hz, hk, hp, h01⟩

omit [DecidableEq W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- The sampling step of the table of `H1` runs within two units. -/
theorem tdStep_time (s : CoreHat S W Pw K × List (Inp W × K)) :
    SPTree.Timed.stepTime (simProt.start.tree.match_8.timed
        ({ td := Option.map (fun x => x.1) s.1.1, cands := s.1.2.1, info := s.1.2.2.1.1,
            zs := s.1.2.2.2.1.1, keyed := s.1.2.2.2.2.1.1, pend := s.1.2.2.2.2.2.1.1,
            h2 := s.1.2.2.2.2.2.2.1, phase := s.1.2.2.2.2.2.2.2 }, s.2) s.1) ≤ 2 := by
  simp only [simProt.start.tree.match_8.timed, SPTree.Timed.delay, SPTree.Timed.stepTime]
  rcases s.1.1 with _ | ⟨t, tc⟩ <;>
    simp [SPTree.Timed.time_ret, SPTree.Timed.time_sample, sup_zero]

/-- The `start` step from a state of `SimInv i` costs at most `70 + 10 t_coe + t_app + 2 F +
35 i + F i`: the lookup of the programmed inputs, the sampling step of the table of `H1` and the
core step. -/
theorem start_time (s : CoreHat S W Pw K × List (Inp W × K)) (e : OEv Pw W) (i : ℕ)
    (hs : SimInv i s) {tc th te : ℕ}
    (hc : ∀ a b, coeCost a b ≤ tc) (hh : ∀ a b, hAppendCost a b ≤ th)
    (he : ∀ a b, expCost a b ≤ te) {F : ℕ} (hF : (15 + tc + te) * Fintype.card Pw + 1 ≤ F) :
    SPTree.Timed.stepTime
      ((simProt.timed G DFunLike.coe coeCost HAppend.hAppend hAppendCost expCost).startCost s e,
        (simProt.timed G DFunLike.coe coeCost HAppend.hAppend hAppendCost expCost).start s e) ≤
      70 + 10 * tc + th + 2 * F + 35 * i + F * i := by
  obtain ⟨hc0, h2l⟩ := hs
  have htd := tdStep_time s
  have hcore : ∀ (e : OEv Pw W) (x : ((Pw → Sˣ) × (Pw → ℕ)) × CoreHat S W Pw K),
      x.1.2 = (fun _ => 0) ∧ CoreInv i x.2 →
      SPTree.Timed.stepTime (SPTree.Timed.delay 1 (simProt.start.tree.match_13.timed G e
        DFunLike.coe coeCost HAppend.hAppend hAppendCost x expCost)) ≤
        1 + (60 + 10 * tc + th + 2 * F + 30 * i + F * i) := fun e x hx => by
    rw [SPTree.Timed.stepTime_delay]
    have := core_time G coeCost hAppendCost expCost e i x hx.1 hx.2 hc hh he hF
    omega
  have hgen := fun e => stepTime_bind_bind_ret_le 1 _ _ (fun x => ((x.1, s.2), x.2))
    (tdStep_allRet s hc0) (hcore e)
  simp only [simProt.timed, simProt.start.treeHat.timed, simProt.start.tree.match_14.timed,
    Prod.mk.eta]
  rcases e with h | a
  · dsimp only
    simp only [SPTree.Timed.stepTime_delay]
    have := stepTime_bind_bind_ret_le 1 _ _ (fun x => ((x.1, s.2), x.2)) (tdStep_allRet s hc0)
      (hcore (.inl h))
    grind only [SPTree.Timed.stepTime_delay]
  · cases a
    case h2 y =>
      dsimp only
      simp only [simProt.start.tree.match_7.timed, SPTree.Timed.stepTime_delay,
        show @simProt.start.tree.match_1.timed S W Pw K _ _ _ _ _ =
          @simProt.start.tree.match_8.timed S W Pw K _ _ _ _ _ from rfl,
        show @simProt.start.tree.match_6.timed S W Pw K _ _ _ _ _ _ _ =
          @simProt.start.tree.match_13.timed S W Pw K _ _ _ _ _ _ _ from rfl]
      have hlk := List.lookup.timedCost_le y s.2
      split
      · simp only [SPTree.Timed.stepTime, SPTree.Timed.time_ret]
        omega
      · have := stepTime_bind_bind_ret_le 1 _ _ (fun x => ((x.1, s.2), x.2))
          (tdStep_allRet s hc0) (hcore (.inr (.h2 y)))
        omega
    case idle =>
      have := hgen (.inr .idle)
      dsimp only
      grind only [SPTree.Timed.stepTime_delay]
    case poll =>
      have := hgen (.inr .poll)
      dsimp only
      grind only [SPTree.Timed.stepTime_delay]
    case msg pid =>
      have := hgen (.inr (.msg pid))
      dsimp only
      grind only [SPTree.Timed.stepTime_delay]
    case h1 pw =>
      have := hgen (.inr (.h1 pw))
      dsimp only
      grind only [SPTree.Timed.stepTime_delay]
    case send pid m =>
      have := hgen (.inr (.send pid m))
      dsimp only
      grind only [SPTree.Timed.stepTime_delay]

/-- The `start` step preserves the invariant of the simulator, one activation later. -/
theorem start_allRet (s : CoreHat S W Pw K × List (Inp W × K)) (e : OEv Pw W) (i : ℕ)
    (hs : SimInv i s) :
    SPTree.Timed.AllRet (fun y => SimInv (i + 1) y.1)
      ((simProt.timed G DFunLike.coe coeCost HAppend.hAppend hAppendCost expCost).start s e) := by
  obtain ⟨hc0, h2l⟩ := hs
  have hgen := fun e => allRet_bind_bind_ret (P := fun y => SimInv (i + 1) y.1) 1 _
    (fun x => SPTree.Timed.delay 1 (simProt.start.tree.match_13.timed G e DFunLike.coe coeCost
      HAppend.hAppend hAppendCost x expCost))
    (fun x => ((x.1, s.2), x.2)) (tdStep_allRet s hc0)
    (fun a ha => SPTree.Timed.allRet_mono (fun y hy => ⟨hy, by dsimp only; omega⟩) _
      (core_allRet G coeCost hAppendCost expCost e i a ha.2))
  simp only [simProt.timed, simProt.start.treeHat.timed, simProt.start.tree.match_14.timed,
    Prod.mk.eta, SPTree.Timed.delay]
  rcases e with h | a
  · exact hgen (.inl h)
  · cases a
    case h2 y =>
      simp only [simProt.start.tree.match_7.timed, SPTree.Timed.delay,
        show @simProt.start.tree.match_1.timed S W Pw K _ _ _ _ _ =
          @simProt.start.tree.match_8.timed S W Pw K _ _ _ _ _ from rfl,
        show @simProt.start.tree.match_6.timed S W Pw K _ _ _ _ _ _ _ =
          @simProt.start.tree.match_13.timed S W Pw K _ _ _ _ _ _ _ from rfl]
      split
      · obtain ⟨hn, hl, hi, hz, hk, hp, h01⟩ := hc0.succ
        exact ⟨⟨hn, hl, hi, hz, hk, hp, h01⟩, by dsimp only; omega⟩
      · exact hgen (.inr (.h2 y))
    case idle => exact hgen (.inr .idle)
    case poll => exact hgen (.inr .poll)
    case msg pid => exact hgen (.inr (.msg pid))
    case h1 pw => exact hgen (.inr (.h1 pw))
    case send pid m => exact hgen (.inr (.send pid m))

/-- The `resume` step preserves the invariant of the simulator, one activation later. -/
theorem resume_allRet (s : CoreHat S W Pw K × List (Inp W × K)) (o : FOut K) (i : ℕ)
    (hs : SimInv i s) :
    SPTree.Timed.AllRet (fun y => SimInv (i + 1) y.1)
      ((simProt.timed G DFunLike.coe coeCost HAppend.hAppend hAppendCost expCost).resume s o) := by
  obtain ⟨hc0, h2l⟩ := hs
  obtain ⟨hn, hl, hi, hz, hk, hp, h01⟩ := hc0.succ
  simp only [simProt.timed, simProt.resume.treeHat.timed, simProt.resume.tree.match_1.timed,
    SPTree.Timed.delay]
  repeat' split
  all_goals first
    | exact ⟨⟨hn, hl, hi, hz, hk, hp, h01⟩, by dsimp only; omega⟩
    | exact ⟨⟨hn, hl, hi, hz, hk, hp, h01⟩, by dsimp only; simp only [List.length_cons]; omega⟩

/-- The `finish` step preserves the invariant of the simulator, one activation later. -/
theorem finish_allRet (s : CoreHat S W Pw K × List (Inp W × K)) (o : FOut K) (i : ℕ)
    (hs : SimInv i s) :
    SPTree.Timed.AllRet (fun y => SimInv (i + 1) y.1)
      ((simProt.timed G DFunLike.coe coeCost HAppend.hAppend hAppendCost expCost).finish s o) := by
  obtain ⟨hc0, h2l⟩ := hs
  obtain ⟨hn, hl, hi, hz, hk, hp, h01⟩ := hc0.succ
  simp only [simProt.timed, simProt.finish.treeHat.timed]
  repeat' split
  all_goals first
    | exact ⟨⟨hn, hl, hi, hz, hk, hp, h01⟩, by dsimp only; omega⟩
    | exact ⟨⟨hn, hl, hi, hz, hk, hp, h01⟩, by dsimp only; simp only [List.length_cons]; omega⟩

/-- **Graded running time of the costed CPace simulator** on the invariant `SimInv`: after `i`
activations every step costs at most `a + b i`, the growth `b` coming from the table of `H2`,
searched at each `send` and each fresh `H2` query, and the programmed inputs, the search of a
candidate password costing at most `15 + t_coe + t_exp` per password. -/
theorem simProt.timeBoundGraded_timed {tc th te : ℕ} (hc : ∀ a b, coeCost a b ≤ tc)
    (hh : ∀ a b, hAppendCost a b ≤ th) (he : ∀ a b, expCost a b ≤ te) :
    (simProt.timed (K := K) G DFunLike.coe coeCost HAppend.hAppend hAppendCost
      expCost).TimeBoundGraded SimInv
      (70 + 10 * tc + th + 2 * ((15 + tc + te) * Fintype.card Pw + 1))
      (35 + ((15 + tc + te) * Fintype.card Pw + 1)) := by
  have hr := fun (s : CoreHat S W Pw K × List (Inp W × K)) (o : FOut K) =>
    simProt.resume.treeHat.timeBound_timed G DFunLike.coe coeCost HAppend.hAppend hAppendCost
      s o hc hh
  have hf := fun (s : CoreHat S W Pw K × List (Inp W × K)) (o : FOut K) =>
    simProt.finish.treeHat.timeBound_timed G DFunLike.coe coeCost HAppend.hAppend hAppendCost
      s o hc hh
  have hinit : SimInv 0 (simProt.timed (K := K) G DFunLike.coe coeCost HAppend.hAppend
      hAppendCost expCost).init := by
    simp [SimInv, CoreInv, simProt.timed]
  refine ⟨hinit, fun i s e hs => ⟨?_,
      start_allRet G coeCost hAppendCost expCost s e i hs⟩, fun i s o hs => ⟨?_,
      resume_allRet G coeCost hAppendCost expCost s o i hs⟩, fun i s o hs => ⟨?_,
      finish_allRet G coeCost hAppendCost expCost s o i hs⟩⟩
  · have := start_time G coeCost hAppendCost expCost s e i hs hc hh he le_rfl
    have e1 := Nat.add_mul 35 ((15 + tc + te) * Fintype.card Pw + 1) i
    omega
  · have := hr s o
    simp only [simProt.timed, Prod.mk.eta] at this ⊢
    simp at this
    omega
  · have := hf s o
    simp only [simProt.timed, Prod.mk.eta] at this ⊢
    simp at this
    omega

end Time

derive_simulator cpaceSim

end CatCrypt.Crypto.PAKE.CPaceSquare
