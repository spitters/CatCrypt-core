/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Consensus.PoSNSB.Prob
public import CatCryptCore.Consensus.UC.Chain

/-!
# PoS-NSB: instances of the probability bound with random lotteries

This file discharges the hypotheses of `pos_nsb_security` and of `UC.Chain.chain_realizes` for
protocols without corrupt parties and gives a family of instances whose failure bound is
below `1`.

## Candidate blocks and the random-oracle hypothesis

In an execution without corrupt parties, every broadcast block is baked by an honest party on
the head of its best chain. The head is the genesis block or a broadcast block of a smaller
slot, so every broadcast block of slot `s` lies in the list `cands GB h s` of candidate
blocks: the genesis block, and for every slot `t ≤ s` the blocks of slot `t` whose predecessor
hash is the hash `h b'` of a candidate `b'` of a smaller slot (or of the genesis block). The
querier `candQuerier` enumerates the candidates of the slots up to `Hz`, learning the hash of
each candidate from its own transcript before it queries the children of that candidate.

* `query_candQuerier`: the `k`-th query of `candQuerier` is the `k`-th candidate.
* `hRO_candQuerier`: without corrupt parties, the genesis block and the broadcast blocks of the
  first `K` phases are among the first `(1 + |Tx| np) ^ (Hz + 1)` queries of `candQuerier`.
* `eufAdv_forger_of_honest`: without corrupt parties, the forgers have advantage `0`.

## The family of instances

`LotteryInstance` has one honest party leading the honest slots, the longest-chain tree type,
`Hash = Fin M`, and slot kinds drawn from `ν` with `pH = 3/4`, `pA = 1/8` on the first
`1000` of `2000` slots. With `d = 1000`, `w = 10` and `ε = 1/4`:

* `slotBound_le`, `slotBound_lt_one`: `slotBound ν 2000 1000 10 (1/4) ≤ 1/16 < 1`;
* `instance_security`: for every `K` with `K + 2 ≤ 2000`, every signature scheme and every
  adversary, chain growth, chain quality and common prefix hold for the first `K` phases
  except with probability at most `slotBound ν 2000 1000 10 (1/4) + q (q - 1) / 2 / M` with
  `q = 2 ^ (K + 2)`;
* `instance_bound_lt_one`: with `M = 4 ^ (K + 5)` this bound is below `1`;
* `UC.Chain.LotteryInstance.instance_realizes`: the same protocols realize `F_Tree` with the
  same bound.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

namespace CatCryptCore.Consensus.PoSNSB

open Parameters BlockParameters Corruption Execution
open scoped ENNReal

/-! ## Candidate blocks -/

section Cands

variable {Tx Hash : Type} [Fintype Tx] {np : ℕ}

/-- The blocks of slot `s` with predecessor hash `h b'`, one for every transaction and every
baker. -/
noncomputable def kids (h : Block Tx Hash (Fin np) → Hash) (s : ℕ)
    (b' : Block Tx Hash (Fin np)) : List (Block Tx Hash (Fin np)) :=
  (Finset.univ : Finset (Tx × Fin np)).toList.map fun x => ⟨s, x.1, h b', x.2⟩

/-- The candidate blocks of the slots up to `s`: the genesis block, its children of slot `0`,
and for every slot `t + 1 ≤ s` the children of slot `t + 1` of the candidates of the slots up
to `t`. -/
noncomputable def cands (GB : Block Tx Hash (Fin np)) (h : Block Tx Hash (Fin np) → Hash) :
    ℕ → List (Block Tx Hash (Fin np))
  | 0 => GB :: kids h 0 GB
  | s + 1 => cands GB h s ++ (cands GB h s).flatMap (kids h (s + 1))

variable {GB : Block Tx Hash (Fin np)} {h : Block Tx Hash (Fin np) → Hash}

theorem mem_kids {s : ℕ} {b' : Block Tx Hash (Fin np)} (tx : Tx) (i : Fin np) :
    (⟨s, tx, h b', i⟩ : Block Tx Hash (Fin np)) ∈ kids h s b' := by
  simp only [kids, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and]
  exact ⟨(tx, i), rfl⟩

theorem cands_mono {s s' : ℕ} (hs : s ≤ s') {b : Block Tx Hash (Fin np)}
    (hb : b ∈ cands GB h s) : b ∈ cands GB h s' := by
  induction hs with
  | refl => exact hb
  | step _ ih => exact List.mem_append_left _ ih

theorem gb_mem_cands (s : ℕ) : GB ∈ cands GB h s :=
  cands_mono (Nat.zero_le s) List.mem_cons_self

/-- The children of the genesis block of slot `t` are candidates of the slots up to `t`. -/
theorem kid_gb_mem_cands (t : ℕ) (tx : Tx) (i : Fin np) :
    (⟨t, tx, h GB, i⟩ : Block Tx Hash (Fin np)) ∈ cands GB h t := by
  cases t with
  | zero => exact List.mem_cons_of_mem _ (mem_kids tx i)
  | succ s =>
    exact List.mem_append_right _ (List.mem_flatMap.2 ⟨GB, gb_mem_cands s, mem_kids tx i⟩)

/-- The children of slot `t` of a candidate of the slots up to `s < t` are candidates of the
slots up to `t`. -/
theorem kid_mem_cands {s t : ℕ} {b' : Block Tx Hash (Fin np)} (hb' : b' ∈ cands GB h s)
    (hst : s < t) (tx : Tx) (i : Fin np) :
    (⟨t, tx, h b', i⟩ : Block Tx Hash (Fin np)) ∈ cands GB h t := by
  obtain ⟨t, rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
  exact List.mem_append_right _
    (List.mem_flatMap.2 ⟨b', cands_mono (by omega) hb', mem_kids tx i⟩)

theorem length_kids (s : ℕ) (b' : Block Tx Hash (Fin np)) :
    (kids h s b').length = Fintype.card (Tx × Fin np) := by
  simp [kids]

/-- The number of candidates does not depend on the hash function. -/
theorem length_cands (s : ℕ) :
    (cands GB h s).length = (1 + Fintype.card (Tx × Fin np)) ^ (s + 1) := by
  induction s with
  | zero => simp [cands, length_kids, add_comm]
  | succ s ih =>
    simp only [cands, List.length_append, List.length_flatMap, length_kids, List.map_const',
      List.sum_replicate, smul_eq_mul, ih]
    ring

/-- The candidates of index below `k` depend only on the hash function at the candidates of
index below `k`. -/
theorem cands_getElem?_congr (g : Block Tx Hash (Fin np) → Hash) (s k : ℕ)
    (hgh : ∀ j, j < k → ∀ (hj' : j < (cands GB h s).length),
      g (cands GB h s)[j] = h (cands GB h s)[j]) :
    (cands GB g s)[k]? = (cands GB h s)[k]? := by
  induction s generalizing k with
  | zero =>
    cases k with
    | zero => simp [cands]
    | succ k =>
      have hGB : g GB = h GB := by
        simpa [cands] using hgh 0 (by omega) (by simp [cands])
      simp only [cands, kids, hGB, List.getElem?_cons_succ]
  | succ s ih =>
    have hlen : (cands GB g s).length = (cands GB h s).length := by
      rw [length_cands, length_cands]
    by_cases hk : k < (cands GB h s).length
    · simp only [cands]
      rw [List.getElem?_append_left (by omega), List.getElem?_append_left hk]
      refine ih k fun j hj hj' => ?_
      have := hgh j hj (by simp only [cands, List.length_append]; omega)
      simpa only [cands, List.getElem_append_left hj'] using this
    · have heq : cands GB g s = cands GB h s := by
        refine List.ext_getElem? fun k' => ?_
        by_cases hk' : k' < (cands GB h s).length
        · refine ih k' fun j hj hj' => ?_
          have := hgh j (by omega) (by simp only [cands, List.length_append]; omega)
          simpa only [cands, List.getElem_append_left hj'] using this
        · rw [List.getElem?_eq_none (by omega), List.getElem?_eq_none (by omega)]
      have hkids : ∀ b' ∈ cands GB h s, kids g (s + 1) b' = kids h (s + 1) b' := by
        intro b' hb'
        obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hb'
        have := hgh j (by omega) (by simp only [cands, List.length_append]; omega)
        simp only [cands, List.getElem_append_left hj] at this
        simp only [kids, this]
      simp only [cands, heq, List.flatMap_congr hkids]

end Cands

/-! ## The candidate querier -/

section Querier

variable {Tx Hash : Type} [DecidableEq Tx] [DecidableEq Hash] [Fintype Tx] [Fintype Hash]
  {np : ℕ}

/-- The answer recorded for `x` in a transcript, or `d` if there is none. -/
def lookD {D R : Type} [DecidableEq D] (d : R) (tr : List (D × R)) (x : D) : R :=
  (tr.lookup x).getD d

theorem lookD_map {D R : Type} [DecidableEq D] (d : R) (f : D → R) (l : List D) {x : D}
    (hx : x ∈ l) : lookD d (l.map fun y => (y, f y)) x = f x := by
  induction l with
  | nil => simp at hx
  | cons a l ih =>
    by_cases hxa : x = a
    · subst hxa; simp [lookD]
    · have hx' : x ∈ l := by simpa [hxa] using hx
      have hb : (x == a) = false := by simpa using hxa
      have := ih hx'
      simp only [lookD, List.map_cons, List.lookup, hb] at this ⊢
      exact this

/-- The querier that enumerates the candidates of the slots up to `Hz`, with the hashes read
off its transcript. -/
noncomputable def candQuerier (GB : Block Tx Hash (Fin np)) (Hz : ℕ) :
    Querier (BlockDom Tx Hash np Hz) Hash :=
  fun tr => encB Hz ((cands GB (fun b => lookD GB.pred tr (encB Hz b)) Hz).getD tr.length GB)

/-- **The queries of the candidate querier.** The `k`-th query of `candQuerier GB Hz` to `f`
is the `k`-th candidate for the hash function `b ↦ f (encB b)`. -/
theorem query_candQuerier (GB : Block Tx Hash (Fin np)) (Hz : ℕ)
    (f : BlockDom Tx Hash np Hz → Hash) :
    ∀ k (hk : k < (cands GB (fun b => f (encB Hz b)) Hz).length),
      query (candQuerier GB Hz) f k = encB Hz (cands GB (fun b => f (encB Hz b)) Hz)[k] := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    set L := cands GB (fun b => f (encB Hz b)) Hz
    have htr : transcript (candQuerier GB Hz) f k =
        ((List.range k).map (query (candQuerier GB Hz) f)).map fun y => (y, f y) := by
      rw [transcript_eq, List.map_map]; rfl
    have hcongr := cands_getElem?_congr (GB := GB) (h := fun b => f (encB Hz b))
      (fun b => lookD GB.pred (transcript (candQuerier GB Hz) f k) (encB Hz b)) Hz k
      (fun j hj hj' => by
        rw [htr]
        refine lookD_map _ _ _ (List.mem_map.2 ⟨j, List.mem_range.2 hj, ?_⟩)
        exact ih j hj hj')
    simp only [query, candQuerier]
    rw [show (transcript (candQuerier GB Hz) f k).length = k by simp [htr],
      List.getD_eq_getElem?_getD, hcongr, List.getElem?_eq_getElem hk, Option.getD_some]

end Querier

/-! ## Executions without corrupt parties -/

section Honest

variable {Tx Hash : Type} [DecidableEq Tx] [DecidableEq Hash] [Fintype Tx] [Fintype Hash]
  {np : ℕ} [Corruption (Fin np)] {n Hz : ℕ} {Sch : SigScheme (Block Tx Hash (Fin np))}
  (P : Protocol Tx Hash np n Hz) (ω : Seed Tx Hash np n Hz Sch)
  (A : Adversary Tx Hash np n Hz Sch)

/-- The head of a valid chain is the genesis block or has a larger slot. -/
theorem headD_gb_or {Party : Type} [Parameters Party] [BlockParameters Tx Hash Party]
    {c : Chain Tx Hash Party} (hc : valid_chain c) :
    c.headD GenesisBlock = GenesisBlock ∨
      (GenesisBlock : Block Tx Hash Party).sl < (c.headD GenesisBlock).sl := by
  cases c with
  | nil => exact Or.inl rfl
  | cons b c =>
    rcases List.mem_cons.1 (valid_chain_starts_gb hc) with hg | hg
    · exact Or.inl hg.symm
    · exact Or.inr (List.rel_of_pairwise_cons hc.2.2 hg)

/-- The invariant of an execution without corrupt parties: `HistInv`, and every broadcast
block of slot `s` is a candidate of the slots up to `s`. -/
def CandInv (M : GS P ω A) : Prop :=
  letI := ω.params P; letI := ω.bparams P; letI := mkExec false P ω A
  HistInv M ∧ ∀ m ∈ M.history,
    get_block m ∈ cands P.GB (fun b => ω.f (encB Hz b)) (get_block m).sl

variable {P ω A}

theorem sBake_cand (hcor : ∀ p : Fin np, is_corrupt p = false) (p : Fin np) (M : GS P ω A)
    (hM : CandInv P ω A M) : CandInv P ω A (sBake P ω A false p M) := by
  let _ := ω.params P; let _ := ω.bparams P; let _ := mkExec false P ω A
  refine ⟨hM.1.bake p, fun m hm => ?_⟩
  simp only [sBake] at hm
  rcases (bake_history M p m).1 hm with hm | ⟨l, hl, ⟨_, hm⟩ | ⟨hc, _⟩⟩
  · exact hM.2 m hm
  · rw [honest_bake_eq] at hm
    split_ifs at hm
    · simp only [List.mem_singleton] at hm
      subst hm
      simp only [get_block]
      have hv := l.tT.best_chain_valid l.tree (M.t_now - 1)
      rcases headD_gb_or hv with hg | hg
      · rw [hg]
        exact kid_gb_mem_cands _ _ _
      · have hmem : (l.tT.bestChain (M.t_now - 1) l.tree).headD GenesisBlock ∈
            l.tT.bestChain (M.t_now - 1) l.tree := by
          cases hc : l.tT.bestChain (M.t_now - 1) l.tree with
          | nil => exact absurd hc (valid_chain_ne_nil hv)
          | cons b c => exact List.mem_cons_self
        have hall := List.mem_filter.1 (l.tT.best_chain_in_all _ _ _ hmem)
        have hsl := of_decide_eq_true hall.2
        rcases List.mem_cons.1 (hM.1.state p l hl _ hall.1) with heq | hhist
        · rw [heq] at hg
          exact absurd hg (lt_irrefl _)
        · obtain ⟨m', hm', he⟩ := List.mem_map.1 hhist
          have hc := hM.2 m' hm'
          rw [he] at hc
          exact kid_mem_cands hc (by omega) _ _
    · simp at hm
  · exact absurd hc (by rw [hcor]; decide)

theorem sRcv_cand (hcor : ∀ p : Fin np, is_corrupt p = false) (p : Fin np) (M : GS P ω A)
    (hM : CandInv P ω A M) : CandInv P ω A (sRcv P ω A false p M) := by
  let _ := ω.params P; let _ := ω.bparams P; let _ := mkExec false P ω A
  refine ⟨hM.1.rcv p, fun m hm => ?_⟩
  simp only [sRcv] at hm
  rcases (rcv_history M p m).1 hm with hm | ⟨_, hc, _⟩
  · exact hM.2 m hm
  · exact absurd hc (by rw [hcor]; decide)

theorem foldr_cand (g : Fin np → GS P ω A → GS P ω A)
    (hg : ∀ p M, CandInv P ω A M → CandInv P ω A (g p M)) (M : GS P ω A)
    (hM : CandInv P ω A M) (l : List (Fin np)) : CandInv P ω A (l.foldr g M) := by
  induction l with
  | nil => exact hM
  | cons p ps ih => exact hg p _ ih

/-- **Broadcast blocks are candidates.** In the real execution of a protocol without corrupt
parties, every broadcast block of slot `s` is a candidate of the slots up to `s`. -/
theorem sTrace_cands (hcor : ∀ p : Fin np, is_corrupt p = false) (k : ℕ) :
    letI := ω.params P; letI := ω.bparams P
    ∀ m ∈ (sTrace P ω A false k).history,
      get_block m ∈ cands P.GB (fun b => ω.f (encB Hz b)) (get_block m).sl := by
  induction k with
  | zero => intro m hm; simp [sTrace, runTrace, N0] at hm
  | succ k ih =>
    let _ := ω.params P; let _ := ω.bparams P; let _ := mkExec false P ω A
    have hI : CandInv P ω A (sTrace P ω A false k) :=
      ⟨reachable_hist_inv (reach_runTrace (Tx := Tx) (Hash := Hash) (Party := Fin np)
        (AdvState := A.AdvState) k), ih⟩
    rw [sTrace_succ, sPhase_def]
    cases (sTrace P ω A false k).progress with
    | Ready => exact (foldr_cand _ (sRcv_cand hcor) _ hI (sTrace P ω A false k).exec_order).2
    | Delivered =>
      exact (foldr_cand _ (sBake_cand hcor) _ hI (sTrace P ω A false k).exec_order).2
    | Baked =>
      intro m hm
      simp only [inc_round, round_tick] at hm
      exact ih m hm

variable (P A)

/-- **The random-oracle hypothesis without corrupt parties.** For a protocol without corrupt
parties, the genesis block and the broadcast blocks of the first `K` phases of the real
execution are among the first `(1 + |Tx| np) ^ (Hz + 1)` queries of the candidate querier,
for every seed. -/
theorem hRO_candQuerier (hcor : ∀ p : Fin np, is_corrupt p = false) (K : ℕ)
    (hHz : K + 1 ≤ Hz) :
    ∀ ω : Seed Tx Hash np n Hz Sch, ∀ j ≤ K, letI := ω.params P; letI := ω.bparams P;
      ∀ b ∈ block_hist_gb (sTrace P ω A false j),
        ∃ k < (1 + Fintype.card (Tx × Fin np)) ^ (Hz + 1),
          query ((fun _ _ => candQuerier P.GB Hz : (Fin n → SlotKind) →
            (Fin np → Sch.PK × Sch.SK) → Querier (BlockDom Tx Hash np Hz) Hash) ω.κ ω.ks)
            ω.f k = encB Hz b := by
  intro ω j hj
  let _ := ω.params P; let _ := ω.bparams P
  intro b hb
  have hc : b ∈ cands P.GB (fun b => ω.f (encB Hz b)) Hz := by
    rcases List.mem_cons.1 hb with rfl | hm
    · exact gb_mem_cands Hz
    · simp only [block_history] at hm
      obtain ⟨m, hm', rfl⟩ := List.mem_map.1 hm
      have h1 := sTrace_cands (P := P) (ω := ω) (A := A) hcor j m hm'
      have h2 := sTrace_slots P ω A j m hm'
      have h3 := sTrace_t_now P A ω false j
      exact cands_mono (by omega) h1
  obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hc
  exact ⟨k, by rwa [length_cands] at hk, query_candQuerier P.GB Hz ω.f k hk⟩

/-- Without corrupt parties, the adversary is never called. -/
theorem not_mem_traceCalls (hcor : ∀ p : Fin np, is_corrupt p = false)
    (ω : Seed Tx Hash np n Hz Sch) (K : ℕ) (c : CallInput Tx Hash np A.AdvState) :
    c ∉ traceCalls P ω A K := by
  simp only [traceCalls, List.mem_flatMap, not_exists, not_and]
  intro k _
  unfold phaseCalls
  split <;> simp [stepCalls, hcor]

/-- **No forgery without corrupt parties.** For a protocol without corrupt parties, the
forgers `forger P A ν W K i` have EUF-CMA advantage `0`. -/
theorem eufAdv_forger_of_honest [Nonempty Hash]
    (hcor : ∀ p : Fin np, is_corrupt p = false) (ν : PMF SlotKind) (W K : ℕ) (i : Fin np) :
    eufAdv (forger P A ν W K i) = 0 := by
  rw [eufAdv_eq, PMF.toOuterMeasure_apply_eq_zero_iff, Set.disjoint_left]
  rintro ⟨⟨pk, sk⟩, ω⟩ - hw
  have hs := (run_simTrace P A i pk ω sk K).1 fun c hc =>
    absurd hc (not_mem_traceCalls P A hcor _ K c)
  have hw' : eufWins (forger P A ν W K i) (pk, sk) ω = true := hw
  simp [eufWins, forger, forgerProg, OracleProg.run_bind, hs.1, OracleProg.run] at hw'

end Honest

/-! ## A family of instances -/

/-- `exp (-x) ≤ 2⁻ᵐ` for `m ≤ x`. -/
theorem exp_neg_le_inv_pow (m : ℕ) {x : ℝ} (hx : (m : ℝ) ≤ x) :
    Real.exp (-x) ≤ ((2 : ℝ) ^ m)⁻¹ := by
  have h1 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp 1; linarith
  rw [Real.exp_neg]
  refine inv_anti₀ (by positivity) ?_
  calc (2 : ℝ) ^ m ≤ Real.exp 1 ^ m := pow_le_pow_left₀ (by norm_num) h1 m
    _ = Real.exp m := Real.exp_one_pow m
    _ ≤ Real.exp x := Real.exp_le_exp.2 hx

namespace LotteryInstance

attribute [local instance] Instance.corruption

/-- The slot-kind distribution: honest with probability `3/4`, adversarial with probability
`1/8`, empty with probability `1/8`. -/
noncomputable def ν : PMF SlotKind :=
  PMF.ofFintype (fun k => match k with
    | .honest => 6 / 8
    | .adversarial => 1 / 8
    | .empty => 1 / 8) (by
      rw [show (Finset.univ : Finset SlotKind) = {.honest, .adversarial, .empty} from rfl]
      simp only [Finset.mem_insert, Finset.mem_singleton, reduceCtorEq, or_self,
        not_false_eq_true, Finset.sum_insert, Finset.sum_singleton]
      rw [ENNReal.div_add_div_same, ENNReal.div_add_div_same]
      norm_num
      exact ENNReal.div_self (by norm_num) (by norm_num))

theorem pH_ν : pH ν = 3 / 4 := by
  simp only [pH, ν, PMF.ofFintype_apply, ENNReal.toReal_div]
  norm_num

theorem pA_ν : pA ν = 1 / 8 := by
  simp only [pA, ν, PMF.ofFintype_apply, ENNReal.toReal_div]
  norm_num

/-- **The slot bound of the instance.** For `n = 2000` slots, windows of `d = 1000` slots,
`w = 10` and `ε = 1/4`, the slot conditions fail with probability at most `1/16`. -/
theorem slotBound_le : slotBound ν 2000 1000 10 (1 / 4) ≤ ENNReal.ofReal (1 / 16) := by
  have e1 : Real.exp (-2 * (1 / 4 * ((1000 : ℕ) : ℝ)) ^ 2 / ((1000 : ℕ) : ℝ)) ≤
      ((2 : ℝ) ^ 124)⁻¹ := by
    rw [show -2 * (1 / 4 * ((1000 : ℕ) : ℝ)) ^ 2 / ((1000 : ℕ) : ℝ) = -125 by norm_num]
    exact exp_neg_le_inv_pow 124 (by norm_num)
  have e2 : Real.exp (-2 * ((((1000 : ℕ) : ℝ) * (3 / 4 - 1 / 8) - ((10 : ℕ) : ℝ)) / 2) ^ 2 /
      ((1000 : ℕ) : ℝ)) ≤ ((2 : ℝ) ^ 188)⁻¹ := by
    rw [show -2 * ((((1000 : ℕ) : ℝ) * (3 / 4 - 1 / 8) - ((10 : ℕ) : ℝ)) / 2) ^ 2 /
      ((1000 : ℕ) : ℝ) = -(15129 / 80) by norm_num]
    exact exp_neg_le_inv_pow 188 (by norm_num)
  have e3 : Real.exp (-2 * ((((1000 : ℕ) : ℝ) * (3 / 4 - 2 * (1 / 8)) - 3) / 3) ^ 2 /
      ((1000 : ℕ) : ℝ)) ≤ ((2 : ℝ) ^ 54)⁻¹ := by
    rw [show -2 * ((((1000 : ℕ) : ℝ) * (3 / 4 - 2 * (1 / 8)) - 3) / 3) ^ 2 /
      ((1000 : ℕ) : ℝ) = -(247009 / 4500) by norm_num]
    exact exp_neg_le_inv_pow 54 (by norm_num)
  simp only [slotBound, pH_ν, pA_ν]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hN : (0 : ℝ) ≤ (((2000 + 1) ^ 2 : ℕ) : ℝ) := by positivity
  calc _ ≤ (((2000 + 1) ^ 2 : ℕ) : ℝ) * ((2 : ℝ) ^ 124)⁻¹ +
        (((2000 + 1) ^ 2 : ℕ) : ℝ) * ((2 : ℝ) ^ 188)⁻¹ +
        (((2000 + 1) ^ 2 : ℕ) : ℝ) * ((2 : ℝ) ^ 54)⁻¹ := by gcongr
    _ ≤ 1 / 16 := by norm_num

/-- **The slot bound is below `1`.** -/
theorem slotBound_lt_one : slotBound ν 2000 1000 10 (1 / 4) < 1 :=
  slotBound_le.trans_lt (by rw [ENNReal.ofReal_lt_one]; norm_num)

variable (M : ℕ) [NeZero M] (Hz : ℕ)

/-- The genesis block: slot `0`, predecessor hash `0`, baked by the single party. -/
def GB : Block Unit (Fin M) (Fin 1) := ⟨0, (), 0, 0⟩

/-- The single party leads exactly the honest slots. -/
def lot : SlotKind → Fin 1 → Bool := fun k _ => decide (k = .honest)

theorem gb_valid (κ : Fin 2000 → SlotKind) (f : BlockDom Unit (Fin M) 1 Hz → Fin M) :
    letI := lotteryParams [0] lot κ
    letI : BlockParameters Unit (Fin M) (Fin 1) := ⟨GB M, fun b => f (encB Hz b)⟩
    valid_chain [(GenesisBlock : Block Unit (Fin M) (Fin 1))] := by
  refine ⟨?_, rfl, List.pairwise_singleton _ _⟩
  intro b hb
  rw [List.mem_singleton] at hb
  subst hb
  rfl

/-- The protocol: one honest party leading the honest slots, the longest-chain tree type,
`2000` slots of lottery and the random oracle on blocks of slots at most `Hz`. -/
noncomputable def P : Protocol Unit (Fin M) 1 2000 Hz where
  IP := [0]
  lot := lot
  GB := GB M
  trees κ f _ :=
    letI := lotteryParams [0] lot κ
    letI : BlockParameters Unit (Fin M) (Fin 1) := ⟨GB M, fun b => f (encB Hz b)⟩
    longestTree (gb_valid M Hz κ f) rfl
  txSel _ _ := ()

/-- The honest tree chain is selected by the longest-chain tree type. -/
noncomputable def Tree : TreeFamily (P M Hz) := fun κ f =>
  letI := lotteryParams [0] lot κ
  letI : BlockParameters Unit (Fin M) (Fin 1) := ⟨GB M, fun b => f (encB Hz b)⟩
  longestTree (gb_valid M Hz κ f) rfl

theorem hcor : ∀ p : Fin 1, is_corrupt p = false := fun _ => rfl

theorem protocolHyp : ProtocolHyp (P M Hz) :=
  ⟨by simp [P], ⟨rfl, fun _ p _ hc => absurd hc (by rw [hcor]; decide)⟩,
    fun κ f _ =>
      letI := lotteryParams [0] lot κ
      letI : BlockParameters Unit (Fin M) (Fin 1) := ⟨GB M, fun b => f (encB Hz b)⟩
      longestTree_longest (gb_valid M Hz κ f) rfl, rfl, Nat.zero_le _⟩

theorem tree_longest : (Tree M Hz).Longest := fun κ f =>
  letI := lotteryParams [0] lot κ
  letI : BlockParameters Unit (Fin M) (Fin 1) := ⟨GB M, fun b => f (encB Hz b)⟩
  longestTree_longest (gb_valid M Hz κ f) rfl

/-- **The family of instances of the security theorem.** For every phase count `K` with
`K + 2 ≤ 2000`, every signature scheme and every adversary, with `W = 1000`, `d = 1000`,
`w = 10`, `ε = 1/4`, `Hz = K + 1` and the candidate querier, chain growth, chain quality and
common prefix hold for the first `K` phases except with probability at most
`slotBound ν 2000 1000 10 (1/4) + q (q - 1) / 2 / M` with `q = 2 ^ (K + 2)`. -/
theorem instance_security (K : ℕ) (hK : K + 2 ≤ 2000)
    (Sch : SigScheme (Block Unit (Fin M) (Fin 1)))
    (A : Adversary Unit (Fin M) 1 2000 (K + 1) Sch) :
    (seedDist ν 1000 2000 (K + 1) Sch).toOuterMeasure
        {ω | ¬Good (P M (K + 1)) A (Tree M (K + 1)) ν K 1000 10 (1 / 4) ω} ≤
      slotBound ν 2000 1000 10 (1 / 4) +
        ((2 ^ (K + 2) * (2 ^ (K + 2) - 1) / 2 : ℕ) : ℝ≥0∞) / M := by
  have h := pos_nsb_security (P M (K + 1)) A (Tree M (K + 1)) (protocolHyp M (K + 1))
    (tree_longest M (K + 1)) ν 1000 K 1000 10 (1 / 4) (by norm_num) (by norm_num)
    (by norm_num) hK le_rfl (by norm_num) (by rw [pH_ν, pA_ν]; norm_num)
    (by rw [pH_ν, pA_ν]; norm_num) (by rw [pH_ν, pA_ν]; norm_num) _
    (fun _ _ => candQuerier (GB M) (K + 1))
    (hRO_candQuerier (P M (K + 1)) A hcor K le_rfl)
  have hq : (1 + Fintype.card (Unit × Fin 1)) ^ (K + 1 + 1) = 2 ^ (K + 2) := by simp
  rw [Finset.sum_eq_zero fun i _ => eufAdv_forger_of_honest (P M (K + 1)) A hcor ν 1000 K i,
    add_zero, hq, Fintype.card_fin] at h
  exact h

/-- **The bound of the family is below `1`.** With `M = 4 ^ (K + 5)` hash values, the failure
bound of `instance_security` is below `1`. -/
theorem instance_bound_lt_one (K : ℕ) :
    slotBound ν 2000 1000 10 (1 / 4) +
        ((2 ^ (K + 2) * (2 ^ (K + 2) - 1) / 2 : ℕ) : ℝ≥0∞) / ((4 ^ (K + 5) : ℕ) : ℝ≥0∞) < 1 := by
  have hc : ((2 ^ (K + 2) * (2 ^ (K + 2) - 1) / 2 : ℕ) : ℝ≥0∞) / ((4 ^ (K + 5) : ℕ) : ℝ≥0∞) ≤
      ENNReal.ofReal (1 / 64) := by
    have hnat : 64 * (2 ^ (K + 2) * (2 ^ (K + 2) - 1) / 2) ≤ 4 ^ (K + 5) := by
      have h1 : 2 ^ (K + 2) * (2 ^ (K + 2) - 1) / 2 ≤ 2 ^ (K + 2) * 2 ^ (K + 2) :=
        (Nat.div_le_self _ _).trans (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
      have h2 : 4 ^ (K + 5) = 64 * (2 ^ (K + 2) * 2 ^ (K + 2)) := by
        rw [← pow_add, show (4 : ℕ) = 2 ^ 2 from rfl, ← pow_mul]; ring
      omega
    rw [ENNReal.div_le_iff (by positivity) (by simp)]
    rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_natCast (4 ^ (K + 5)),
      ← ENNReal.ofReal_mul (by norm_num)]
    refine ENNReal.ofReal_le_ofReal ?_
    have : (64 : ℝ) * ((2 ^ (K + 2) * (2 ^ (K + 2) - 1) / 2 : ℕ) : ℝ) ≤
        ((4 ^ (K + 5) : ℕ) : ℝ) := by
      exact_mod_cast hnat
    linarith
  calc _ ≤ ENNReal.ofReal (1 / 16) + ENNReal.ofReal (1 / 64) := add_le_add slotBound_le hc
    _ = ENNReal.ofReal (1 / 16 + 1 / 64) := (ENNReal.ofReal_add (by norm_num) (by norm_num)).symm
    _ < 1 := by rw [ENNReal.ofReal_lt_one]; norm_num

end LotteryInstance

end CatCryptCore.Consensus.PoSNSB

namespace CatCryptCore.Consensus.UC.Chain.LotteryInstance

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open CatCrypt.Crypto.UCTransparent CatCrypt.NonUniform
open CatCryptCore.Consensus.UC.FTree
open PoSNSB PoSNSB.LotteryInstance Corruption
open scoped ENNReal

attribute [local instance] PoSNSB.Instance.corruption

/-- **Instances with a random lottery** (composition plumbing). For the protocols
`PoSNSB.LotteryInstance.P` (one honest party leading the honest slots, slot kinds drawn with
`pH = 3/4` and `pA = 1/8` on the first `1000` of `2000` slots, `Hash = Fin M`), every phase
count `K` with `K + 2 ≤ 2000`, every signature scheme, every adversary and every delay bound
`Δ`, with `W = 1000`, `d = 1000`, `w = 10`, `ε = 1/4` and the candidate querier, every
hypothesis of `chain_realizes` holds, so the protocol realizes `F_Tree` with bound
`slotBound ν 2000 1000 10 (1/4) + q (q - 1) / 2 / M` with `q = 2 ^ (K + 2)`; the bound is
below `1` for `M = 4 ^ (K + 5)` (`PoSNSB.LotteryInstance.instance_bound_lt_one`). -/
theorem instance_realizes (M : ℕ) [NeZero M] (K : ℕ) (hK : K + 2 ≤ 2000)
    (Sch : SigScheme (Block Unit (Fin M) (Fin 1)))
    (A : Adversary Unit (Fin M) 1 2000 (K + 1) Sch) (Δ : ℕ) :
    Realizes (chainReal (P M (K + 1)) A (Tree M (K + 1)) K ν 1000 Δ)
      (ideal (chainF (P M (K + 1)) A (Tree M (K + 1)) K ν 1000 Δ 1000 10 (1 / 4))
        (chainSim (P M (K + 1)) A (Tree M (K + 1)) K ν 1000 Δ))
      (fun _ _ => slotBound ν 2000 1000 10 (1 / 4) +
        ((2 ^ (K + 2) * (2 ^ (K + 2) - 1) / 2 : ℕ) : ℝ≥0∞) / M) := by
  have h := chain_realizes (P M (K + 1)) A (Tree M (K + 1)) (protocolHyp M (K + 1))
    (fun p _ => by simp [P, Fin.fin_one_eq_zero p]) (tree_longest M (K + 1)) ν 1000 K 1000 10
    (1 / 4) Δ (by norm_num) (by norm_num) (by norm_num) hK le_rfl (by norm_num)
    (by rw [pH_ν, pA_ν]; norm_num) (by rw [pH_ν, pA_ν]; norm_num)
    (by rw [pH_ν, pA_ν]; norm_num) _ (fun _ _ => candQuerier (GB M) (K + 1))
    (hRO_candQuerier (P M (K + 1)) A hcor K le_rfl)
  have hq : (1 + Fintype.card (Unit × Fin 1)) ^ (K + 1 + 1) = 2 ^ (K + 2) := by simp
  simp only [Finset.sum_eq_zero fun i _ =>
      eufAdv_forger_of_honest (P M (K + 1)) A hcor ν 1000 K i, add_zero, hq,
    Fintype.card_fin] at h
  exact h

end CatCryptCore.Consensus.UC.Chain.LotteryInstance
