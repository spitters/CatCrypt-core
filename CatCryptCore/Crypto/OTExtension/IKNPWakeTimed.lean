/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OTExtension.IKNPWake
public import CatCryptCore.Crypto.UCTransparentMultiTimed
public import CatCryptCore.Crypto.UCSimulatorCost
import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveReduction.Basic
public import CatCryptCore.Tactics.DeriveSimulator
import CatCryptCore.Tactics.DeriveTimeBound
public import CatCryptCore.Tactics.DeriveTimeBound.Basic
public import CatCryptCore.Tactics.StdCosts
public import CatCryptCore.Crypto.UCConcreteTimed

/-!
# Costed form of the IKNP simulator over the scheduled base OTs

`derive_reduction` builds the costed form `simW.timed` of the multi-call simulator `simW` of
`IKNPWake.lean` over costed forms of the view completions `simS` and `simR`. The state of `simW`
and its port events hold functions, so the costed form runs on costed states and events (the
trees `simW.start.treeHat`, `simW.resume.treeHat`, `simW.finish.treeHat`), and its erasure
theorem `simW.erase_timed` states `MultiHybrid.Timed.ErasesHat`.

The costed state carries cost tables of the delivery and column flags, which grow with each
update, and the simulated channel, whose queue and inbox the steps read. The invariant `InvW`
bounds each cost table by three times the number of set flags and the messages of the channel by
the one message the simulator sends; the initial state satisfies it and every step preserves it.
On the states of `InvW` the steps cost at most a constant in `κ` and the costs of the
primitives (`simW.timeBoundInv_timed`). `derive_simulator` then gives the costed form of the
simulator `iknpSimH` with both parties honest and its time theorem.

The reduction to correlation-robust hashing `iknpWakeCRRed H Z` is the environment reduction of
`UCConcreteTimed` over the family `(crA H).withKey`: its tree `iknpWakeCRRed.tree` over
`sysEnvTree` compiles to it, its costed form is derived by `derive_timed`, and its time is the
time of the environment, the time of one step of the keyed system per activation, the reset to
the heap of the environment and a constant (`iknpWakeCRRed.tree.timeBound_timed`). No module
imports this file.

## Main definitions

* `simW.timed`: the costed multi-call simulator.
* `InvW`: the invariant of its costed states.

## Main results

* `simW.erase_timed`: its erasure through the erasure maps of the costed state and events.
* `simW.timeBoundInv_timed`: the running time of its steps on the states of `InvW`.
* `iknpSimH.timed`, `iknpSimH.erase_timed`, `iknpSimH.timeBound_timed`: the costed simulator
  with both parties honest, its erasure and its time.
* `iknpWakeCRRed.compile_tree`, `iknpWakeCRRed.tree.timed`, `iknpWakeCRRed.tree.erase_timed`,
  `iknpWakeCRRed.tree.timeBound_timed`: the certificate of the reduction to correlation-robust
  hashing.
-/

@[expose] public section

set_option autoImplicit false

derive_reduction CatCrypt.Crypto.OT.IKNPWake.simW
derive_time_bound CatCrypt.Crypto.OT.IKNPWake.simW.start.treeHat
derive_time_bound CatCrypt.Crypto.OT.IKNPWake.simW.finish.treeHat

namespace CatCrypt.Crypto.OT.IKNPWake

open CatCrypt.Core CatCrypt.Crypto.UCTransparent

/-- The costed state of `simW.timed`: the flags of `SSt` with the cost tables of `dR` and
`col`. -/
abbrev SStHat (κ m : ℕ) (M LS LR : Type) :=
  ((Fin κ → Bool) × (Fin κ → ℕ)) × ((Fin κ → Bool) × (Fin κ → ℕ)) × Bool ×
    ChanSt (Msg m M) × Option LS × Option LR × SPh κ

/-- The number of set flags. -/
def nTrue {κ : ℕ} (c : Fin κ → Bool) : ℕ := (Finset.univ.filter fun j => c j = true).card

/-- **The invariant of the costed states of `simW`**: each cost table is at most three times
the number of set flags of its table, the queue and the inbox of the simulated channel hold
together at most the one message the simulator sends, and the cursor stays within the
queue. -/
def InvW {κ m : ℕ} {M LS LR : Type} (s : SStHat κ m M LS LR) : Prop :=
  (∀ a, s.1.2 a ≤ 3 * nTrue s.1.1) ∧ (∀ a, s.2.1.2 a ≤ 3 * nTrue s.2.1.1) ∧
  s.2.2.2.1.queue.length + s.2.2.2.1.inbox.length ≤ (if s.2.2.1 then 1 else 0) ∧
  s.2.2.2.1.cursor ≤ s.2.2.2.1.queue.length

/-- Setting an unset flag adds one set flag. -/
theorem nTrue_update {κ : ℕ} (c : Fin κ → Bool) (i : Fin κ) (hi : c i = false) :
    nTrue (Function.update c i true) = nTrue c + 1 := by
  unfold nTrue
  rw [← Finset.card_insert_of_notMem (s := Finset.univ.filter fun j => c j = true) (a := i)
    (by simp [hi])]
  congr 1
  ext j
  by_cases h : j = i <;> simp [h, Function.update]

/-- The cost table after setting an unset flag stays within three times the set flags. -/
theorem table_update {κ : ℕ} (c : Fin κ → Bool) (t : Fin κ → ℕ) (i : Fin κ) (hi : c i = false)
    (ht : ∀ a, t a ≤ 3 * nTrue c) (a : Fin κ) :
    (2 + if a = i then 0 else 1 + t a) ≤ 3 * nTrue (Function.update c i true) := by
  rw [nTrue_update c i hi]
  have := ht a
  split <;> omega

/-- At most `κ` flags are set. -/
theorem nTrue_le {κ : ℕ} (c : Fin κ → Bool) : nTrue c ≤ κ := by
  unfold nTrue
  exact (Finset.card_filter_le _ _).trans (by simp)

/-- The head of a list and the rest of its length make up its length. -/
theorem head_toList_length {α : Type} (l : List α) :
    l.head?.toList.length + (l.length - 1) = l.length := by
  cases l <;> simp [Nat.add_comm]

/-- A step that charges `k` and `c` before a costed bind whose continuation returns at zero
cost runs within `k + c` and the time of the bound tree. -/
theorem stepTime_delay_bind_ret {α β : Type} (k c : ℕ) (A : SPTree.Timed α) (h : α → β) :
    SPTree.Timed.stepTime (k + (SPTree.Timed.delay c (A.bind fun y => (0, .ret (h y)))).1,
      (SPTree.Timed.delay c (A.bind fun y => (0, .ret (h y)))).2) ≤ k + c + A.time := by
  have := SPTree.Timed.bind_ret_stepTime_le (0, A) h
  simp only [SPTree.Timed.stepTime, SPTree.Timed.delay] at this ⊢
  omega

section Inv

variable {κ m : ℕ} {M : Type} [Zero M] {LS LR P L EGA OGA : Type}
  (ans : Option LS → Option LR → P → L) (ansCost : Option LS → Option LR → P → ℕ)
  (sch : SchedEv → EGA) (schCost : SchedEv → ℕ) (stat : OGA → Bool × Bool)
  (statCost : OGA → ℕ) (pkEv : EGA) (simS : OGA → SPComp LS) (simSCost : OGA → ℕ)
  (simR : OGA → SPComp LR) (simRCost : OGA → ℕ) (hS : ∀ a, SPComp.NoFail (simS a))
  (hR : ∀ a, SPComp.NoFail (simR a)) (simS' : OGA → SPTree.Timed LS) (simSCost' : OGA → ℕ)
  (simR' : OGA → SPTree.Timed LR) (simRCost' : OGA → ℕ)

/-- The initial costed state satisfies the invariant. -/
theorem simW.init_inv :
    InvW (simW.timed (κ := κ) (m := m) (M := M) ans ansCost sch schCost stat statCost pkEv simS
      simSCost simR simRCost hS hR simS' simSCost' simR' simRCost').init := by
  simp [InvW, simW.timed, FChan.initSt]

/-- The `start` step preserves the invariant. -/
theorem simW.start_allRet (s : SStHat κ m M LS LR) (hs : InvW s) e :
    SPTree.Timed.AllRet (fun y => InvW y.1)
      ((simW.timed ans ansCost sch schCost stat statCost pkEv simS simSCost simR simRCost hS
        hR simS' simSCost' simR' simRCost').start s e) := by
  obtain ⟨h1, h2, h3, h4⟩ := hs
  rcases e with ((⟨x, c⟩ | ⟨x, c⟩) | (i | _)) | ((⟨i, ev⟩ | d) | p) <;>
    simp only [simW.timed, simW.start.treeHat.timed, SPTree.Timed.AllRet, Sum.map_inl,
      Sum.map_inr]
  · exact ⟨h1, h2, h3, h4⟩
  · exact ⟨h1, h2, h3, h4⟩
  · split_ifs with hc hd
    · simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc hd
      refine ⟨h1, table_update _ _ i hc.2 h2, ?_, ?_⟩
      · simp only [hd.2, FChan.honStep] at h3 ⊢
        simp
        grind
      · simp only [FChan.honStep, List.length_append]
        omega
    · simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc
      exact ⟨h1, table_update _ _ i hc.2 h2, h3, h4⟩
    · exact ⟨h1, h2, h3, h4⟩
  · split
    · exact ⟨h1, h2, h3, h4⟩
    · rename_i hd _ rest heq
      refine ⟨h1, h2, ?_, h4⟩
      simp only [heq, List.length_cons] at h3 ⊢
      omega
  · cases ev <;> exact ⟨h1, h2, h3, h4⟩
  · cases d <;> refine ⟨h1, h2, ?_, ?_⟩ <;>
      simp [FChan.advStep, FChan.popTo, Choreography.ChannelCap.secure] at h3 h4 ⊢ <;>
      grind [head_toList_length]
  · exact ⟨h1, h2, h3, h4⟩

/-- The `finish` step preserves the invariant. -/
theorem simW.finish_allRet (s : SStHat κ m M LS LR) (hs : InvW s) o :
    SPTree.Timed.AllRet (fun y => InvW y.1)
      ((simW.timed ans ansCost sch schCost stat statCost pkEv simS simSCost simR simRCost hS
        hR simS' simSCost' simR' simRCost').finish s o) := by
  simp only [simW.timed, simW.finish.treeHat.timed, SPTree.Timed.AllRet]
  exact hs

omit [Zero M] in
/-- The answer step of `simW.timed` on an answer of the adversary port preserves the
invariant. -/
theorem simW.match_2_allRet (S : SSt κ m M LS LR) (dc cc : Fin κ → ℕ)
    (hI : InvW ((S.dR, dc), (S.col, cc), S.ysent, S.ch, S.lvS, S.lvR, S.ph)) (a : OGA) :
    SPTree.Timed.AllRet (fun y => InvW y.1)
      (simW.resume.tree.match_2.timed (L := L) stat statCost pkEv S simS' simSCost' simR'
        simRCost' a dc cc).2 := by
  obtain ⟨h1, h2, h3, h4⟩ := hI
  unfold simW.resume.tree.match_2.timed
  dsimp only
  split <;> simp only [SPTree.Timed.delay, SPTree.Timed.allRet_bind, SPTree.Timed.AllRet] <;>
    (try split_ifs with hc) <;>
    first
    | exact ⟨h1, h2, h3, h4⟩
    | exact SPTree.Timed.allRet_of_forall
        (fun _ => by exact ⟨h1, h2, h3, h4⟩) _
    | exact ⟨fun x => table_update _ _ _ (by simp_all) h1 x, h2, h3, h4⟩

omit [Zero M] in
/-- The answer step of `simW.timed` on an answer of the honest port where none is awaited
preserves the invariant. -/
theorem simW.match_1_allRet (S : SSt κ m M LS LR) (dc cc : Fin κ → ℕ)
    (hI : InvW ((S.dR, dc), (S.col, cc), S.ysent, S.ch, S.lvS, S.lvR, S.ph)) :
    SPTree.Timed.AllRet (fun y => InvW y.1)
      (simW.resume.tree.match_1.timed (L := L) stat statCost pkEv S simS' simSCost' simR'
        simRCost' dc cc).2 := by
  obtain ⟨h1, h2, h3, h4⟩ := hI
  unfold simW.resume.tree.match_1.timed
  dsimp only
  split <;> simp only [SPTree.Timed.delay, SPTree.Timed.allRet_bind, SPTree.Timed.AllRet] <;>
    (try split_ifs with hc) <;>
    first
    | exact ⟨h1, h2, h3, h4⟩
    | exact SPTree.Timed.allRet_of_forall
        (fun _ => by exact ⟨h1, h2, h3, h4⟩) _
    | exact ⟨fun x => table_update _ _ _ (by simp_all) h1 x, h2, h3, h4⟩

/-- The `resume` step preserves the invariant. -/
theorem simW.resume_allRet (s : SStHat κ m M LS LR) (hs : InvW s) o :
    SPTree.Timed.AllRet (fun y => InvW y.1)
      ((simW.timed ans ansCost sch schCost stat statCost pkEv simS simSCost simR simRCost hS
        hR simS' simSCost' simR' simRCost').resume s o) := by
  simp only [simW.timed, simW.resume.treeHat.timed, simW.resume.tree.match_3.timed,
    SPTree.Timed.delay]
  rcases o with o | a
  · simp only [Sum.map_inl]
    split_ifs
    · exact hs
    · exact simW.match_1_allRet _ _ _ _ _ _ _ _ _ _ hs
  · exact simW.match_2_allRet _ _ _ _ _ _ _ _ _ _ hs _

omit [Zero M] in
/-- The time of the answer step of `simW.timed` on an answer of the adversary port, from a
cost table of the delivery flags bounded by `3 κ`. -/
theorem simW.match_2_time (S : SSt κ m M LS LR) (dc cc : Fin κ → ℕ) (hdc : ∀ i, dc i ≤ 3 * κ)
    {ts tSc TS tRc TR : ℕ} (hst : ∀ a, statCost a ≤ ts) (hSc : ∀ a, simSCost' a ≤ tSc)
    (hTS : ∀ a, (simS' a).time ≤ TS) (hRc : ∀ a, simRCost' a ≤ tRc)
    (hTR : ∀ a, (simR' a).time ≤ TR) (a : OGA) :
    SPTree.Timed.stepTime (simW.resume.tree.match_2.timed (L := L) stat statCost pkEv S simS'
      simSCost' simR' simRCost' a dc cc) ≤ 11 + 2 * ts + 3 * κ + tSc + TS + tRc + TR := by
  unfold simW.resume.tree.match_2.timed
  dsimp only
  have := hSc a
  have := hTS a
  have := hRc a
  have := hTR a
  rcases S.ph <;>
    first
    | exact le_trans (stepTime_delay_bind_ret _ _ _ _) (by omega)
    | (simp only [SPTree.Timed.stepTime]
       (try split_ifs) <;> simp only [SPTree.Timed.delay, SPTree.Timed.time_ret] <;> grind)

omit [Zero M] in
/-- The time of the answer step of `simW.timed` on an answer of the honest port where none is
awaited. -/
theorem simW.match_1_time (S : SSt κ m M LS LR) (dc cc : Fin κ → ℕ) :
    SPTree.Timed.stepTime (simW.resume.tree.match_1.timed (L := L) stat statCost pkEv S simS'
      simSCost' simR' simRCost' dc cc) ≤ 4 := by
  unfold simW.resume.tree.match_1.timed
  dsimp only
  rcases S.ph <;> simp only [SPTree.Timed.stepTime] <;>
    (try split_ifs) <;> simp only [SPTree.Timed.delay, SPTree.Timed.time_ret] <;> omega

/-- The `resume` step of `simW.timed` from a state of the invariant. -/
theorem simW.resume_time (s : SStHat κ m M LS LR) (hs : InvW s) o
    {ts tSc TS tRc TR : ℕ} (hst : ∀ a, statCost a ≤ ts) (hSc : ∀ a, simSCost' a ≤ tSc)
    (hTS : ∀ a, (simS' a).time ≤ TS) (hRc : ∀ a, simRCost' a ≤ tRc)
    (hTR : ∀ a, (simR' a).time ≤ TR) :
    SPTree.Timed.stepTime
      ((simW.timed ans ansCost sch schCost stat statCost pkEv simS simSCost simR simRCost hS
        hR simS' simSCost' simR' simRCost').resumeCost s o,
       (simW.timed ans ansCost sch schCost stat statCost pkEv simS simSCost simR simRCost hS
        hR simS' simSCost' simR' simRCost').resume s o) ≤
      14 + 2 * ts + 3 * κ + tSc + TS + tRc + TR := by
  have hdc : ∀ i, s.1.2 i ≤ 3 * κ := fun i => (hs.1 i).trans (by have := nTrue_le s.1.1; omega)
  simp only [simW.timed, simW.resume.treeHat.timed, simW.resume.tree.match_3.timed,
    SPTree.Timed.delay, SPTree.Timed.stepTime]
  rcases o with o | a
  · simp only [Sum.map_inl]
    have := simW.match_1_time (L := L) stat statCost pkEv simS' simSCost' simR' simRCost'
      { dR := s.1.1, col := s.2.1.1, ysent := s.2.2.1, ch := s.2.2.2.1, lvS := s.2.2.2.2.1,
        lvR := s.2.2.2.2.2.1, ph := s.2.2.2.2.2.2 } s.1.2 s.2.1.2
    simp only [SPTree.Timed.stepTime] at this
    split_ifs <;> simp only [SPTree.Timed.time_ret] <;> omega
  · simp only [Sum.map_inr]
    have := simW.match_2_time (L := L) stat statCost pkEv simS' simSCost' simR' simRCost'
      { dR := s.1.1, col := s.2.1.1, ysent := s.2.2.1, ch := s.2.2.2.1, lvS := s.2.2.2.2.1,
        lvR := s.2.2.2.2.2.1, ph := s.2.2.2.2.2.2 } s.1.2 s.2.1.2 hdc hst hSc hTS hRc hTR a
    simp only [SPTree.Timed.stepTime] at this
    omega

/-- The `start` step of `simW.timed` from a state of the invariant costs at most
`6 κ + t_schCost + t_ansCost + 60`. -/
theorem simW.start_time (s : SStHat κ m M LS LR) (hs : InvW s) e
    {t_ansCost t_schCost t_statCost t_simSCost t_simRCost T_simS t_simSCost' T_simR
      t_simRCost' : ℕ}
    (ha : ∀ a b p, ansCost a b p ≤ t_ansCost) (hsch : ∀ a, schCost a ≤ t_schCost)
    (hst : ∀ a, statCost a ≤ t_statCost) (hSc : ∀ a, simSCost a ≤ t_simSCost)
    (hRc : ∀ a, simRCost a ≤ t_simRCost) (hTS : ∀ a, (simS' a).time ≤ T_simS)
    (hSc' : ∀ a, simSCost' a ≤ t_simSCost') (hTR : ∀ a, (simR' a).time ≤ T_simR)
    (hRc' : ∀ a, simRCost' a ≤ t_simRCost') :
    SPTree.Timed.stepTime
      ((simW.timed ans ansCost sch schCost stat statCost pkEv simS simSCost simR simRCost hS
        hR simS' simSCost' simR' simRCost').startCost s e,
       (simW.timed ans ansCost sch schCost stat statCost pkEv simS simSCost simR simRCost hS
        hR simS' simSCost' simR' simRCost').start s e) ≤ 6 * κ + t_schCost + t_ansCost + 60 := by
  refine le_trans (simW.start.treeHat.timeBound_timed ans ansCost sch schCost stat statCost pkEv
    simS simSCost simR simRCost hS hR simS' simSCost' simR' simRCost' s e ha hsch hst hSc hRc
    hTS hSc' hTR hRc') ?_
  obtain ⟨i1, i2, i3, i4⟩ := hs
  have := nTrue_le s.1.1
  have := nTrue_le s.2.1.1
  have hq : s.2.2.2.1.queue.length ≤ 1 ∧ s.2.2.2.1.inbox.length ≤ 1 := by
    split_ifs at i3 <;> omega
  have hh : s.2.2.2.1.queue.head?.toList.length ≤ 1 := by
    cases s.2.2.2.1.queue.head? <;> simp
  rcases e with ((⟨x, c⟩ | ⟨x, c⟩) | (i | _)) | ((⟨i, ev⟩ | d) | p) <;>
    simp only [Sum.map_inl, Sum.map_inr]
  · omega
  · omega
  · have := i1 i
    have := i2 i
    omega
  · omega
  · omega
  · have hd := List.drop.timedCost_le s.2.2.2.1.cursor
      (List.map (Choreography.ChannelCap.secure.wireLeak msgLeak) s.2.2.2.1.queue)
    have hread : Choreography.ChannelCap.secure.read = false := rfl
    have hm := List.map.timedCost_le (Choreography.ChannelCap.secure.wireLeak msgLeak)
      (fun _ => 4 + 1) (k := 5) (fun _ => le_rfl) s.2.2.2.1.queue
    simp only [List.length.timedCost_eq, List.append.timedCost_eq, List.length_map, hread]
      at hd hm ⊢
    omega
  · omega

/-- **Running time of the costed IKNP simulator on the states of its invariant**: from a state
of `InvW`, `start` costs at most `6 κ + t_schCost + t_ansCost + 60`, `resume` at most
`14 + 2 t_statCost + 3 κ` plus the costs and times of the view completions, `finish` nothing,
and every step returns states of `InvW`. -/
theorem simW.timeBoundInv_timed
    {t_ansCost t_schCost t_statCost t_simSCost t_simRCost T_simS t_simSCost' T_simR
      t_simRCost' : ℕ}
    (ha : ∀ a b p, ansCost a b p ≤ t_ansCost) (hsch : ∀ a, schCost a ≤ t_schCost)
    (hst : ∀ a, statCost a ≤ t_statCost) (hSc : ∀ a, simSCost a ≤ t_simSCost)
    (hRc : ∀ a, simRCost a ≤ t_simRCost) (hTS : ∀ a, (simS' a).time ≤ T_simS)
    (hSc' : ∀ a, simSCost' a ≤ t_simSCost') (hTR : ∀ a, (simR' a).time ≤ T_simR)
    (hRc' : ∀ a, simRCost' a ≤ t_simRCost') :
    (simW.timed (κ := κ) (m := m) (M := M) ans ansCost sch schCost stat statCost pkEv simS
        simSCost simR simRCost hS hR simS' simSCost' simR' simRCost').TimeBoundInv InvW
      (6 * κ + t_schCost + t_ansCost + 60)
      (14 + 2 * t_statCost + 3 * κ + t_simSCost' + T_simS + t_simRCost' + T_simR) 0 :=
  ⟨simW.init_inv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _,
    fun s e hs => ⟨simW.start_time _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s hs e ha hsch hst hSc hRc
        hTS hSc' hTR hRc',
      simW.start_allRet _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s hs e⟩,
    fun s o hs => ⟨simW.resume_time _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s hs o hst hSc' hTS hRc'
        hTR,
      simW.resume_allRet _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s hs o⟩,
    fun s o hs => ⟨simW.finish.treeHat.timeBound_timed ans ansCost sch schCost stat statCost pkEv
        simS simSCost simR simRCost hS hR simS' simSCost' simR' simRCost' s o ha hsch hst hSc hRc
        hTS hSc' hTR hRc',
      simW.finish_allRet _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ s hs o⟩⟩

end Inv

end CatCrypt.Crypto.OT.IKNPWake

derive_simulator CatCrypt.Crypto.OT.IKNPWake.iknpSimH

namespace CatCrypt.Crypto.OT.IKNPWake

open CatCrypt.Core CatCrypt.Crypto.UCTransparent

section CRRed

/-- The events of the keyed system of the reduction to correlation-robust hashing. -/
abbrev CREv (κ m : ℕ) (M : Type) := (InEv m M ⊕ WakeEv κ) ⊕ (AEv κ m M ⊕ Unit)

/-- The outputs of the keyed system of the reduction to correlation-robust hashing. -/
abbrev CROut (κ m : ℕ) (M : Type) := InOut m M ⊕ (AOut m M ⊕ Option (RView κ m M))

/-- The state of the keyed system of the reduction to correlation-robust hashing. -/
abbrev CRSt (κ m : ℕ) (M : Type) := ASt κ m M Unit (RView κ m M)

variable {κ m : ℕ} {M : Type} [AddCommGroup M] (H : Fin m → (Fin κ → Bool) → M)

/-- The computation tree of `iknpWakeCRRed H Z`, over a family `S` of systems indexed by the key
(`(crA H).withKey` for the reduction) and a tree `step` of the step of `S` at a key. -/
noncomputable def iknpWakeCRRed.tree {K : Type}
    (S : K → Sys (CRSt κ m M) (CREv κ m M) (CROut κ m M)) {ζ : Type}
    (Z : UCConcrete.Env (Strat ζ (CREv κ m M) (CROut κ m M)) ζ)
    (next : ζ → SPTree (ζ × CREv κ m M))
    (step : K → CRSt κ m M → CREv κ m M → SPTree (CRSt κ m M × CROut κ m M))
    (obs : ζ → CROut κ m M → SPTree ζ) (dist : ζ → SPTree Bool) (k : K) : SPTree Bool :=
  sysEnvTree S Z next step obs dist k

/-- The tree of `iknpWakeCRRed H Z` compiles to `iknpWakeCRRed H Z`. -/
theorem iknpWakeCRRed.compile_tree [NeZero κ] [Fintype M] [Nonempty M] {ζ : Type}
    (Z : UCConcrete.Env (Strat ζ (CREv κ m M) (CROut κ m M)) ζ)
    {next : ζ → SPTree (ζ × CREv κ m M)}
    {step : CRKey κ m M → CRSt κ m M → CREv κ m M → SPTree (CRSt κ m M × CROut κ m M)}
    {obs : ζ → CROut κ m M → SPTree ζ}
    {dist : ζ → SPTree Bool} (hn : ∀ z, (next z).compile = Z.input.next z)
    (hs : ∀ th t e, (step th t e).compile = ((crA H).withKey th).step t e)
    (ho : ∀ z o, (obs z o).compile = Z.input.obs z o) (hd : ∀ z, (dist z).compile = Z.dist z)
    (th : CRKey κ m M) :
    (iknpWakeCRRed.tree (crA H).withKey Z next step obs dist th).compile =
      iknpWakeCRRed H Z th :=
  sysEnvTree_compile _ Z hn hs ho hd th

derive_timed iknpWakeCRRed.tree

omit [AddCommGroup M] in
/-- **Time of the reduction to correlation-robust hashing.** On the key `k`, for a costed
strategy of `Z` and a costed step of `S k`, from initial states of their invariants
and with a distinguisher of time at most `tD`, the reduction costs at most the reset to the heap
of `Z`, the time of the strategy over its `q = Z.input.rounds` activations, `tD`, the time of
`q` steps of the keyed system, `9` per activation and a constant. -/
theorem iknpWakeCRRed.tree.timeBound_timed {K : Type}
    (S : K → Sys (CRSt κ m M) (CREv κ m M) (CROut κ m M)) (SCost : K → ℕ) {ζ : Type}
    (Z : UCConcrete.Env (Strat ζ (CREv κ m M) (CROut κ m M)) ζ)
    {next : ζ → SPTree.Timed (ζ × CREv κ m M)} {nextCost : ζ → ℕ}
    {step : K → CRSt κ m M → CREv κ m M → SPTree.Timed (CRSt κ m M × CROut κ m M)}
    {stepCost : K → CRSt κ m M → CREv κ m M → ℕ}
    {obs : ζ → CROut κ m M → SPTree.Timed ζ} {obsCost : ζ → CROut κ m M → ℕ}
    {dist : ζ → SPTree.Timed Bool} {distCost : ζ → ℕ} (k : K)
    {InvZ MidZ : ℕ → ζ → Prop} {InvS : ℕ → CRSt κ m M → Prop}
    {Ev : ℕ → CREv κ m M → Prop}
    {Out : ℕ → CROut κ m M → Prop} {tN tS tO : ℕ → ℕ} {tD : ℕ}
    (hZ : StratRunBound next nextCost obs obsCost InvZ MidZ Ev Out tN tO)
    (hS : SysRunBound (step k) (stepCost k) InvS Ev Out tS)
    (hz : InvZ 0 Z.input.init) (ht : InvS 0 (S k).init)
    (hd : ∀ z, InvZ Z.input.rounds z → SPTree.Timed.stepTime (distCost z, dist z) ≤ tD) :
    SPTree.Timed.stepTime
        (iknpWakeCRRed.tree.timed S SCost Z next nextCost step stepCost obs obsCost dist
          distCost k) ≤
      Z.heap.data.keys.card + (∑ i ∈ Finset.range Z.input.rounds, (tN i + tO i)) + tD +
        (∑ i ∈ Finset.range Z.input.rounds, tS i) + 9 * Z.input.rounds + SCost k + 7 := by
  have h := sysEnvTree.timeBound_timed S SCost Z k hZ hS hz ht hd
  simp only [iknpWakeCRRed.tree.timed, SPTree.Timed.stepTime_delay]
  omega

end CRRed

end CatCrypt.Crypto.OT.IKNPWake
