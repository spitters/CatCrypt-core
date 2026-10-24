/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.EagerLazyRF
public import CatCryptCore.Crypto.HybridArgument

/-!
# Multi-key PRF security by a hybrid over the queried indices

For a keyed function `F : K → D → R` and an index type `N`, the multi-key function
`mkPRF F φ (n, d) = F (φ n) d` holds one key of `F` for every index. An adversary that asks
queries at no more than `u` distinct indices (`OracleAdv.IndexBound Prod.fst A ∅ u`)
has a PRF advantage against `mkPRF F` of at most the sum of the PRF advantages of `F`
against the reductions `mkHybRed F A j` for `j < u`.

The indices are ranked in the order of their first query. The hybrid `hybGame F A j`
answers the queries at an index of rank below `j` by a random function, sampled lazily in
one table per rank, and the queries at an index of rank `j` or more by `F` under a key of
that rank, drawn when the rank is first queried. The reduction `mkHybRed F A j` runs `A`,
answers the ranks below `j` by lazily sampled random functions, the rank `j` by its own
oracle, and the ranks above `j` by `F` under keys it draws when the rank is first queried;
it samples no whole table.

## Main definitions

* `mkPRF F` — the multi-key function with one key of `F` per index
* `OracleAdv.IndexBound ι A G u` — every path of `A` asks queries at indices `ι d` of which,
  together with `G`, there are at most `u` distinct ones
* `hybOracle F j`, `hybGame F A j` — the hybrid oracle and game
* `hybImpl F j`, `mkHybRed F A j` — the reduction to the PRF games of `F` at rank `j`
* `mkHybRed.timed` — its costed form

## Main results

* `run_map_fst_eq_of_indexBound` — two oracles whose calls from related states are coupled
  with related successor states give an adversary with an index bound the same output
* `realGame_mkHybRed_eq` — the real PRF game of `F` against `mkHybRed F A j` is the hybrid
  `j`
* `rfGame_mkHybRed_eq` — the random-function game against `mkHybRed F A j` is the hybrid
  `j + 1`
* `realGame_mkPRF_eq_hybGame_zero` — the real game of `mkPRF F` is the hybrid `0`
* `rfGame_eq_hybGame_of_indexBound` — the random-function game of an adversary with at most
  `u` indices is the hybrid `u`
* `mkPRF_advantage_le` — the multi-key PRF advantage is at most the sum of the PRF advantages
  of `F` against `mkHybRed F A j`, `j < u`
* `isIndexBound_simulate` — a simulation whose every program asks at one index adds at most
  one index per query
* `mkHybRed.timeBound_timed` — the time of the reduction
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.OracleAdv

variable {D R α N : Type} [DecidableEq N]

/-- `IndexBound ι A G u`: on every path of `A`, the indices `ι d` of the queries `d`, with the
indices in `G`, number at most `u`. -/
def IndexBound (ι : D → N) : OracleAdv D R α → Finset N → ℕ → Prop
  | .ret _, _, _ => True
  | .rand _ k, G, u => ∀ b, IndexBound ι (k b) G u
  | .query d k, G, u => (insert (ι d) G).card ≤ u ∧ ∀ r, IndexBound ι (k r) (insert (ι d) G) u

theorem IndexBound.mono {ι : D → N} {A : OracleAdv D R α} {G G' : Finset N} {u u' : ℕ}
    (h : A.IndexBound ι G' u) (hG : G ⊆ G') (hu : u ≤ u') : A.IndexBound ι G u' := by
  induction A generalizing G G' with
  | ret a => trivial
  | rand p k ih => exact fun b => ih b (h b) hG
  | query d k ih =>
    exact ⟨(Finset.card_le_card (Finset.insert_subset_insert _ hG)).trans (h.1.trans hu),
      fun r => ih r (h.2 r) (Finset.insert_subset_insert _ hG)⟩

/-- `AtIndex ι n A`: every query of `A` is at the index `n`. -/
def AtIndex (ι : D → N) (n : N) : OracleAdv D R α → Prop
  | .ret _ => True
  | .rand _ k => ∀ b, AtIndex ι n (k b)
  | .query d k => ι d = n ∧ ∀ r, AtIndex ι n (k r)

omit [DecidableEq N] in
theorem atIndex_bind {β : Type} {ι : D → N} {n : N} {A : OracleAdv D R α}
    {f : α → OracleAdv D R β} (hA : A.AtIndex ι n) (hf : ∀ a, (f a).AtIndex ι n) :
    (A.bind f).AtIndex ι n := by
  induction A with
  | ret a => exact hf a
  | rand p k ih => exact fun b => ih b (hA b)
  | query d k ih => exact ⟨hA.1, fun r => ih r (hA.2 r)⟩

theorem indexBound_bind {β : Type} {ι : D → N} {n : N} {A : OracleAdv D R α}
    {f : α → OracleAdv D R β} {G : Finset N} {u : ℕ} (hA : A.AtIndex ι n)
    (hn : (insert n G).card ≤ u) (hf : ∀ a, (f a).IndexBound ι (insert n G) u) :
    (A.bind f).IndexBound ι G u := by
  induction A generalizing G with
  | ret a => exact (hf a).mono (Finset.subset_insert _ _) le_rfl
  | rand p k ih => exact fun b => ih b (hA b) hn hf
  | query d k ih =>
    obtain ⟨hd, hk⟩ := hA
    subst hd
    refine ⟨hn, fun r => ih r (hk r) ?_ ?_⟩
    · rwa [Finset.insert_idem]
    · intro a; rw [Finset.insert_idem]; exact hf a

theorem indexBound_bind_ret {β : Type} {ι : D → N} {A : OracleAdv D R α} {g : α → β}
    {G : Finset N} {u : ℕ} (hA : A.IndexBound ι G u) :
    (A.bind fun a => .ret (g a)).IndexBound ι G u := by
  induction A generalizing G with
  | ret a => trivial
  | rand p k ih => exact fun b => ih b (hA b)
  | query d k ih => exact ⟨hA.1, fun r => ih r (hA.2 r)⟩

/-- **Indices of a simulation.** If every program `impl s d` asks only at one index `κ d`,
the simulation of an adversary with at most `q` queries asks at most `q` indices beyond
`G`. -/
theorem isIndexBound_simulate {D' R' S : Type} {ι : D' → N} (κ : D → N)
    (impl : S → D → OracleAdv D' R' (R × S)) (himpl : ∀ s d, (impl s d).AtIndex ι (κ d))
    {A : OracleAdv D R α} {q : ℕ} (hA : A.IsQueryBound q) (G : Finset N) (s : S) :
    (simulate impl A s).IndexBound ι G (G.card + q) := by
  induction A generalizing q G s with
  | ret a => trivial
  | rand p k ih => exact fun b => ih b (hA b) G s
  | query d k ih =>
    cases q with
    | zero => exact hA.elim
    | succ q =>
      refine indexBound_bind (himpl s d) ?_ fun x => ?_
      · have := Finset.card_insert_le (κ d) G
        omega
      · refine (ih x.1 (hA x.1) (insert (κ d) G) x.2).mono le_rfl ?_
        have := Finset.card_insert_le (κ d) G
        omega

end CatCrypt.Crypto.OracleAdv

namespace CatCrypt.Crypto.MultiKeyPRF

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.PRPPRF
open CatCrypt.Crypto.HybridArgument
open scoped ENNReal

variable {N D R K : Type}

/-- The multi-key function of `F`: the key `φ` holds a key of `F` for every index, and the
input `(n, d)` is answered by `F (φ n) d`. -/
def mkPRF (F : K → D → R) (φ : N → K) (p : N × D) : R := F (φ p.1) p.2

/-! ## Coupled runs -/

/-- **Coupled runs.** Let a relation `Rel s s' G` between the states of two oracles, indexed
by the set `G` of indices asked, be such that from related states, a call at a new index
count within `u` is a common distribution `μ` mapped to the answers and to related successor
states of both oracles. Then an adversary with index bound `u` has the same output against
both oracles from related states. -/
theorem run_map_fst_eq_of_indexBound [DecidableEq N] {D' S S' α : Type} (ι : D' → N)
    (O : S → D' → PMF (R × S)) (O' : S' → D' → PMF (R × S'))
    (Rel : S → S' → Finset N → Prop) (u : ℕ)
    (hO : ∀ s s' G d, Rel s s' G → (insert (ι d) G).card ≤ u →
      ∃ (V : Type) (μ : PMF V) (a : V → R) (f : V → S) (g : V → S'),
        O s d = μ.map (fun v => (a v, f v)) ∧ O' s' d = μ.map (fun v => (a v, g v)) ∧
        ∀ v, Rel (f v) (g v) (insert (ι d) G))
    (A : OracleAdv D' R α) (G : Finset N) (hA : A.IndexBound ι G u) (s : S) (s' : S')
    (h : Rel s s' G) :
    (OracleAdv.run O A s).map Prod.fst = (OracleAdv.run O' A s').map Prod.fst := by
  induction A generalizing G s s' with
  | ret a => simp [PMF.pure_map]
  | rand p k ih =>
    simp only [OracleAdv.run_rand, PMF.map_bind]
    exact congrArg _ (funext fun b => ih b G (hA b) s s' h)
  | query d k ih =>
    obtain ⟨V, μ, a, f, g, h1, h2, h3⟩ := hO s s' G d h hA.1
    simp only [OracleAdv.run_query, PMF.map_bind, h1, h2, PMF.bind_map]
    exact congrArg _ (funext fun v => ih (a v) _ (hA.2 (a v)) (f v) (g v) (h3 v))

/-! ## Ranks of indices -/

section Rank

variable [DecidableEq N]

/-- The indices in the order of their first query, after a query at `n`. -/
def addIdx (seen : List N) (n : N) : List N := if n ∈ seen then seen else seen ++ [n]

/-- The rank of `n` among the indices `seen`, after a query at `n`. -/
def rank (seen : List N) (n : N) : ℕ := (addIdx seen n).idxOf n

theorem mem_addIdx (seen : List N) (n : N) : n ∈ addIdx seen n := by
  unfold addIdx; split <;> simp_all

theorem mem_addIdx_iff (seen : List N) (n m : N) : m ∈ addIdx seen n ↔ m = n ∨ m ∈ seen := by
  unfold addIdx; split <;> grind

theorem nodup_addIdx {seen : List N} (h : seen.Nodup) (n : N) : (addIdx seen n).Nodup := by
  unfold addIdx; split
  · exact h
  · exact List.nodup_append.2 ⟨h, List.nodup_singleton n, by rintro a ha b hb rfl; simp only [List.mem_singleton] at hb; subst hb; contradiction⟩

theorem toFinset_addIdx (seen : List N) (n : N) :
    (addIdx seen n).toFinset = insert n seen.toFinset := by
  ext m; simp [mem_addIdx_iff]

theorem rank_lt_length (seen : List N) (n : N) : rank seen n < (addIdx seen n).length :=
  List.idxOf_lt_length_of_mem (mem_addIdx seen n)

/-- `RankRel e seen st L`: the storage `st` per rank holds, at the rank of each index of
`seen`, the storage `L` of that index, and `e` at every other rank; an index outside `seen`
has storage `e`. -/
def RankRel {X : Type} (e : X) (seen : List N) (st : ℕ → X) (L : N → X) : Prop :=
  (∀ r, seen.length ≤ r → st r = e) ∧ ∀ n, L n = if n ∈ seen then st (seen.idxOf n) else e

theorem rankRel_nil {X : Type} (e : X) : RankRel e ([] : List N) (fun _ => e) (fun _ => e) :=
  ⟨fun _ _ => rfl, fun _ => by simp⟩

theorem RankRel.extend {X : Type} {e : X} {seen : List N} {st : ℕ → X} {L : N → X}
    (h : RankRel e seen st L) (n : N) : RankRel e (addIdx seen n) st L := by
  obtain ⟨h1, h2⟩ := h
  unfold addIdx
  split
  · exact ⟨h1, h2⟩
  · next hn =>
    refine ⟨fun r hr => h1 r (by simp at hr; omega), fun m => ?_⟩
    rw [h2 m]
    by_cases hm : m ∈ seen
    · simp [hm, List.idxOf_append_of_mem hm]
    · by_cases hmn : m = n
      · subst hmn
        simp [hm, List.idxOf_append_of_notMem hm, h1]
      · simp [hm, hmn]

theorem RankRel.apply {X : Type} {e : X} {seen : List N} {n : N} {st : ℕ → X} {L : N → X}
    (h : RankRel e (addIdx seen n) st L) : st (rank seen n) = L n := by
  rw [h.2 n, ite_eq_left (mem_addIdx seen n), rank]

theorem RankRel.update {X : Type} {e : X} {seen : List N} {n : N} {st : ℕ → X} {L : N → X}
    (h : RankRel e (addIdx seen n) st L) (x : X) :
    RankRel e (addIdx seen n) (Function.update st (rank seen n) x) (Function.update L n x) := by
  obtain ⟨h1, h2⟩ := h
  have hlt := rank_lt_length seen n
  refine ⟨fun r hr => ?_, fun m => ?_⟩
  · rw [Function.update_of_ne (by omega)]
    exact h1 r hr
  · by_cases hmn : m = n
    · subst hmn
      simp [mem_addIdx, rank]
    · rw [Function.update_of_ne hmn, h2 m]
      split
      · next hm =>
        rw [Function.update_of_ne]
        intro heq
        exact hmn ((List.idxOf_inj hm).1 heq)
      · rfl

end Rank

/-! ## The hybrids -/

/-- The state of the hybrid oracles: the indices in the order of their first query, one table
of the random function per rank, and the key of each rank drawn so far. -/
abbrev HybState (N D R K : Type) : Type := List N × (ℕ → List (D × R)) × (ℕ → Option K)

/-- The initial hybrid state. -/
def hybInit : HybState N D R K := ([], fun _ => [], fun _ => none)

section Hybrid

variable [DecidableEq N] [DecidableEq D] [Fintype R] [Nonempty R] [Fintype K] [Nonempty K]

/-- The hybrid oracle `j`: a query `(n, d)` at an index of rank below `j` is answered by the
random function of that rank; at rank `j` or more by `F k d` under the key `k` of that rank,
drawn uniformly when the rank is first queried. -/
noncomputable def hybOracle (F : K → D → R) (j : ℕ) (s : HybState N D R K) (q : N × D) :
    PMF (R × HybState N D R K) :=
  if rank s.1 q.1 < j then
    (rfOracle (s.2.1 (rank s.1 q.1)) q.2).map fun x =>
      (x.1, (addIdx s.1 q.1, Function.update s.2.1 (rank s.1 q.1) x.2, s.2.2))
  else
    match s.2.2 (rank s.1 q.1) with
    | some k => PMF.pure (F k q.2, (addIdx s.1 q.1, s.2.1, s.2.2))
    | none => (PMF.uniformFintype K).map fun k =>
        (F k q.2, (addIdx s.1 q.1, s.2.1, Function.update s.2.2 (rank s.1 q.1) (some k)))

/-- The hybrid game `j`. -/
noncomputable def hybGame (F : K → D → R) (A : OracleAdv (N × D) R Bool) (j : ℕ) :
    SPComp Bool :=
  liftPMF ((OracleAdv.run (hybOracle F j) A hybInit).map Prod.fst)

/-- One query of `mkHybRed F A j` from the hybrid state `s`: a query `(n, d)` at an index of
rank below `j` is answered from the table of that rank, a new point drawing a uniform value;
at rank `j` by the query `d` to the oracle of the reduction; above `j` by `F k d` under the
key `k` of that rank, drawn uniformly when the rank is first queried. -/
noncomputable def hybImpl (F : K → D → R) (j : ℕ) (s : HybState N D R K) (q : N × D) :
    OracleAdv D R (R × HybState N D R K) :=
  if rank s.1 q.1 < j then
    match List.lookup q.2 (s.2.1 (rank s.1 q.1)) with
    | some v => .ret (v, (addIdx s.1 q.1, s.2.1, s.2.2))
    | none => .rand (PMF.uniformFintype R) fun v =>
        .ret (v, (addIdx s.1 q.1,
          Function.update s.2.1 (rank s.1 q.1) ((q.2, v) :: s.2.1 (rank s.1 q.1)), s.2.2))
  else if rank s.1 q.1 = j then
    .query q.2 fun v => .ret (v, (addIdx s.1 q.1, s.2.1, s.2.2))
  else
    match s.2.2 (rank s.1 q.1) with
    | some k => .ret (F k q.2, (addIdx s.1 q.1, s.2.1, s.2.2))
    | none => .rand (PMF.uniformFintype K) fun k =>
        .ret (F k q.2, (addIdx s.1 q.1, s.2.1, Function.update s.2.2 (rank s.1 q.1) (some k)))

/-- **Reduction** to the PRF games of `F` at rank `j`: run `A`, answering each query by
`hybImpl F j`. -/
noncomputable def mkHybRed (F : K → D → R) (A : OracleAdv (N × D) R Bool) (j : ℕ) :
    OracleAdv D R Bool :=
  (OracleAdv.simulate (hybImpl F j) A hybInit).bind fun x => .ret x.1

/-- The hybrid state with the key of rank `j` set to `v`. -/
def setKey (j : ℕ) (v : Option K) (s : HybState N D R K) : HybState N D R K :=
  (s.1, s.2.1, Function.update s.2.2 j v)

theorem hybOracle_setKey (F : K → D → R) (j : ℕ) (v : Option K) (s : HybState N D R K)
    (q : N × D) (hq : rank s.1 q.1 ≠ j) :
    hybOracle F j (setKey j v s) q = (hybOracle F j s q).map (Prod.map id (setKey j v)) := by
  have hk : Function.update s.2.2 j v (rank s.1 q.1) = s.2.2 (rank s.1 q.1) :=
    Function.update_of_ne hq _ _
  unfold hybOracle setKey
  dsimp only
  split_ifs with hr
  · rw [PMF.map_comp]
    rfl
  · rw [hk]
    rcases h : s.2.2 (rank s.1 q.1) with _ | k
    · simp only [PMF.map_comp]
      congr 1
      funext k
      simp [Function.update_comm hq]
    · simp [PMF.pure_map]

/-- **Deferred key.** The key of rank `j` drawn before the run gives the output of the key
drawn when the rank is first queried. -/
theorem uniform_bind_run_setKey (F : K → D → R) (j : ℕ) {α : Type}
    (A : OracleAdv (N × D) R α) (s : HybState N D R K) :
    (PMF.uniformFintype K).bind (fun k =>
        (OracleAdv.run (hybOracle F j) A (setKey j (some k) s)).map Prod.fst) =
      (OracleAdv.run (hybOracle F j) A (setKey j none s)).map Prod.fst := by
  induction A generalizing s with
  | ret a => simp [PMF.pure_map]
  | rand p k ih =>
    simp only [OracleAdv.run_rand, PMF.map_bind]
    rw [PMF.bind_comm]
    exact congrArg _ (funext fun b => ih b s)
  | query q k ih =>
    by_cases hr : rank s.1 q.1 = j
    · have h1 : ∀ v, hybOracle F j (setKey j (some v) s) q =
          PMF.pure (F v q.2, setKey j (some v) (addIdx s.1 q.1, s.2.1, s.2.2)) := by
        intro v
        simp [hybOracle, setKey, hr]
      have h2 : hybOracle F j (setKey j none s) q = (PMF.uniformFintype K).map
          fun v => (F v q.2, setKey j (some v) (addIdx s.1 q.1, s.2.1, s.2.2)) := by
        simp [hybOracle, setKey, hr]
      simp only [OracleAdv.run_query, h1, h2, PMF.pure_bind, PMF.bind_map, PMF.map_bind]
      rfl
    · simp only [OracleAdv.run_query, hybOracle_setKey F j _ s q hr, PMF.bind_map, PMF.map_bind]
      rw [PMF.bind_comm]
      refine congrArg _ (funext fun x => ?_)
      exact ih x.1 x.2

theorem simOracle_keyed_hybImpl (F : K → D → R) (j : ℕ) (k : K) (s : HybState N D R K)
    (q : N × D) :
    (OracleAdv.simOracle (hybImpl F j) (keyedOracle F k) (s, ()) q).map
        (Prod.map id fun p => setKey j (some k) p.1) =
      hybOracle F j (setKey j (some k) s) q := by
  have hbp : ∀ {α β : Type} (p : PMF α) (f : α → β),
      p.bind (fun a => PMF.pure (f a)) = p.map f := fun _ _ => rfl
  unfold OracleAdv.simOracle hybImpl hybOracle setKey
  dsimp only
  split_ifs with h1 h2
  · rcases hl : List.lookup q.2 (s.2.1 (rank s.1 q.1)) with _ | v
    · simp [rfOracle, hl, PMF.map_comp, Function.comp_def, hbp]
    · simp [rfOracle, hl, PMF.pure_map]
  · simp [h2, keyedOracle, PMF.pure_map]
  · have hne : rank s.1 q.1 ≠ j := h2
    rw [Function.update_of_ne hne]
    rcases hk : s.2.2 (rank s.1 q.1) with _ | k'
    · simp [PMF.map_comp, Function.comp_def, hbp,
        Function.update_comm hne]
    · simp [PMF.pure_map]

theorem simOracle_rf_hybImpl [DecidableEq R] (F : K → D → R) (j : ℕ) (s : HybState N D R K)
    (t : List (D × R)) (q : N × D) :
    (OracleAdv.simOracle (hybImpl F j) rfOracle (s, t) q).map
        (Prod.map id fun p => (p.1.1, Function.update p.1.2.1 j p.2, p.1.2.2)) =
      hybOracle F (j + 1) (s.1, Function.update s.2.1 j t, s.2.2) q := by
  have hbp : ∀ {α β : Type} (p : PMF α) (f : α → β),
      p.bind (fun a => PMF.pure (f a)) = p.map f := fun _ _ => rfl
  unfold OracleAdv.simOracle hybImpl hybOracle
  dsimp only
  by_cases h1 : rank s.1 q.1 < j
  · have hne : rank s.1 q.1 ≠ j := by omega
    rw [ite_eq_left h1, ite_eq_left (by omega), Function.update_of_ne hne]
    rcases hl : List.lookup q.2 (s.2.1 (rank s.1 q.1)) with _ | v
    · simp [rfOracle, hl, PMF.map_comp, Function.comp_def, hbp,
        Function.update_comm hne]
    · simp only [rfOracle, hl, OracleAdv.run_ret, PMF.pure_map, Prod.map, id]
      refine congrArg PMF.pure (Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ rfl)))
      funext r
      by_cases hr : r = rank s.1 q.1
      · subst hr; simp [Function.update_of_ne hne]
      · simp [Function.update_of_ne hr]
  · by_cases h2 : rank s.1 q.1 = j
    · rw [ite_eq_right h1, ite_eq_left h2, ite_eq_left (by omega), h2]
      simp [PMF.map_comp, Function.comp_def, hbp]
    · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right (by omega)]
      rcases hk : s.2.2 (rank s.1 q.1) with _ | k'
      · simp [PMF.map_comp, Function.comp_def, hbp]
      · simp [PMF.pure_map]

/-- The real PRF game of `F` against `mkHybRed F A j` is the hybrid `j`. -/
theorem realGame_mkHybRed_eq (F : K → D → R) (A : OracleAdv (N × D) R Bool) (j : ℕ) :
    realGame F (mkHybRed F A j) = hybGame F A j := by
  unfold realGame hybGame mkHybRed
  congr 1
  simp only [OracleAdv.run_simulate_fst]
  have h : ∀ k, (OracleAdv.run (OracleAdv.simOracle (hybImpl F j) (keyedOracle F k)) A
      (hybInit, ())).map Prod.fst =
      (OracleAdv.run (hybOracle F j) A (setKey j (some k) hybInit)).map Prod.fst := fun k =>
    Constructions.SIV.run_map_fst_eq_of_map_state _ _ (fun p => setKey j (some k) p.1)
      (fun p q => by obtain ⟨s, ⟨⟩⟩ := p; exact simOracle_keyed_hybImpl F j k s q) A (hybInit, ())
  have hi : setKey j none (hybInit : HybState N D R K) = hybInit := by
    simp [setKey, hybInit]
  simp only [h]
  rw [uniform_bind_run_setKey, hi]

/-- The random-function game against `mkHybRed F A j` is the hybrid `j + 1`. -/
theorem rfGame_mkHybRed_eq [DecidableEq R] (F : K → D → R) (A : OracleAdv (N × D) R Bool)
    (j : ℕ) : rfGame (mkHybRed F A j) = hybGame F A (j + 1) := by
  unfold rfGame hybGame mkHybRed
  congr 1
  rw [OracleAdv.run_simulate_fst,
    Constructions.SIV.run_map_fst_eq_of_map_state _ (hybOracle F (j + 1))
      (fun p => (p.1.1, Function.update p.1.2.1 j p.2, p.1.2.2))
      (fun p q => simOracle_rf_hybImpl F j p.1 p.2 q) A (hybInit, [])]
  congr 2
  simp [hybInit]

/-- The real game of `mkPRF F` is the hybrid `0`. -/
theorem realGame_mkPRF_eq_hybGame_zero [Fintype N] [DecidableEq K] (F : K → D → R)
    (A : OracleAdv (N × D) R Bool) (u : ℕ) (hA : A.IndexBound Prod.fst ∅ u) :
    realGame (mkPRF F) A = hybGame F A 0 := by
  let implK : Unit → N × D → OracleAdv N K (R × Unit) := fun _ q =>
    .query q.1 fun k => .ret (F k q.2, ())
  unfold realGame hybGame
  congr 1
  have h1 : ∀ φ : N → K, (OracleAdv.run (keyedOracle (mkPRF F) φ) A ()).map Prod.fst =
      (OracleAdv.run (OracleAdv.simOracle implK (keyedOracle (fun f p => f p) φ)) A
        ((), ())).map Prod.fst := fun φ =>
    Constructions.SIV.run_map_fst_eq_of_map_state _ _ (fun _ => ((), ()))
      (fun _ q => by simp [implK, OracleAdv.simOracle, keyedOracle, mkPRF, PMF.pure_map]) A ()
  simp only [h1]
  rw [Constructions.SIVNonce.uniform_bind_run_simOracle_keyed implK A ()]
  symm
  refine run_map_fst_eq_of_indexBound Prod.fst _ _
    (fun s s' _ => RankRel none s.1 s.2.2 (fun n => List.lookup n s'.2)) u ?_ A ∅ hA hybInit
    ((), []) ?_
  · rintro s ⟨⟨⟩, tK⟩ G ⟨n, d⟩ h -
    have hk := (h.extend n).apply
    dsimp only at hk
    rcases hl : List.lookup n tK with _ | k
    · refine ⟨K, PMF.uniformFintype K, fun k => F k d,
        fun k => (addIdx s.1 n, s.2.1, Function.update s.2.2 (rank s.1 n) (some k)),
        fun k => ((), (n, k) :: tK), ?_, ?_, fun k => ?_⟩
      · simp [hybOracle, hk, hl]
      · simp [implK, OracleAdv.simOracle, rfOracle, hl, Function.comp_def,
          PMF.map_bind, PMF.pure_map]
        rfl
      · have := (h.extend n).update (some k)
        convert this using 1
        funext m
        by_cases hm : m = n
        · subst hm; simp
        · have hb : (m == n) = false := by simpa using hm
          simp [List.lookup, hb, Function.update_of_ne hm]
    · refine ⟨Unit, PMF.pure (), fun _ => F k d, fun _ => (addIdx s.1 n, s.2.1, s.2.2),
        fun _ => ((), tK), ?_, ?_, fun _ => h.extend n⟩
      · simp [hybOracle, hk, hl, PMF.pure_map]
      · simp [implK, OracleAdv.simOracle, rfOracle, hl, PMF.pure_map]
  · convert rankRel_nil (N := N) (none : Option K) using 1 <;> rfl

/-- The random-function game of an adversary asking at most `u` indices is the hybrid
`u`. -/
theorem rfGame_eq_hybGame_of_indexBound [DecidableEq R] (F : K → D → R)
    (A : OracleAdv (N × D) R Bool) (u : ℕ) (hA : A.IndexBound Prod.fst ∅ u) :
    rfGame A = hybGame F A u := by
  unfold rfGame hybGame
  congr 1
  symm
  refine run_map_fst_eq_of_indexBound Prod.fst _ _
    (fun s T G => s.1.Nodup ∧ s.1.toFinset = G ∧
      RankRel (fun _ => none) s.1 (fun r d => List.lookup d (s.2.1 r))
        (fun n d => @List.lookup (N × D) R instBEqOfDecidableEq (n, d) T)) u ?_ A ∅ hA hybInit [] ?_
  · rintro s T G ⟨n, d⟩ ⟨hnd, hG, h⟩ hc
    dsimp only at hc ⊢
    have hr : rank s.1 n < u := by
      have := rank_lt_length s.1 n
      rw [← List.toFinset_card_of_nodup (nodup_addIdx hnd n), toFinset_addIdx, hG] at this
      omega
    have hk : ∀ d', List.lookup d' (s.2.1 (rank s.1 n)) = @List.lookup (N × D) R instBEqOfDecidableEq (n, d') T :=
      fun d' => congrFun (h.extend n).apply d'
    rcases hl : @List.lookup (N × D) R instBEqOfDecidableEq (n, d) T with _ | v
    · refine ⟨R, PMF.uniformFintype R, id,
        fun v => (addIdx s.1 n,
          Function.update s.2.1 (rank s.1 n) ((d, v) :: s.2.1 (rank s.1 n)), s.2.2),
        fun v => ((n, d), v) :: T, ?_, ?_,
        fun v => ⟨nodup_addIdx hnd n, by rw [toFinset_addIdx, hG], ?_⟩⟩
      · simp [hybOracle, hr, rfOracle, hk, hl, PMF.map_comp, Function.comp_def]
      · simp [rfOracle, hl]
      · have := (h.extend n).update (Function.update (fun d' => @List.lookup (N × D) R instBEqOfDecidableEq (n, d') T) d (some v))
        convert this using 1
        · funext r d'
          by_cases hr' : r = rank s.1 n
          · subst hr'
            by_cases hd : d' = d
            · subst hd; simp
            · have hb : (d' == d) = false := by simpa using hd
              simp [List.lookup, hb, hd, hk]
          · simp [Function.update_of_ne hr']
        · funext m d'
          by_cases hm : m = n
          · subst hm
            by_cases hd : d' = d
            · subst hd; simp [List.lookup]
            · simp only [List.lookup]
              rw [@beq_false_of_ne _ instBEqOfDecidableEq _ _ _ (fun h => hd (Prod.mk.inj h).2)]
              simp [hd]
          · simp only [List.lookup]
            rw [@beq_false_of_ne _ instBEqOfDecidableEq _ _ _ (fun h => hm (Prod.mk.inj h).1)]
            simp [hm]
    · refine ⟨Unit, PMF.pure (), fun _ => v, fun _ => (addIdx s.1 n, s.2.1, s.2.2),
        fun _ => T, ?_, ?_, fun _ => ⟨nodup_addIdx hnd n, by rw [toFinset_addIdx, hG],
          h.extend n⟩⟩
      · simp [hybOracle, hr, rfOracle, hk, hl, PMF.pure_map]
      · simp [rfOracle, hl, PMF.pure_map]
  · refine ⟨List.nodup_nil, rfl, ?_⟩
    convert rankRel_nil (N := N) (fun _ : D => (none : Option R)) using 1 <;> rfl

/-- **Multi-key PRF.** For every adversary `A` asking queries at no more than `u` distinct
indices, the PRF advantage against the multi-key function `mkPRF F` is at most the sum over
`j < u` of the PRF advantages of `F` against `mkHybRed F A j`. -/
theorem mkPRF_advantage_le [Fintype N] [DecidableEq K] [DecidableEq R] (F : K → D → R)
    (A : OracleAdv (N × D) R Bool) (u : ℕ) (hA : A.IndexBound Prod.fst ∅ u) :
    PRF_q_Advantage (mkPRF F) A ≤
      ∑ j ∈ Finset.range u, PRF_q_Advantage F (mkHybRed F A j) := by
  unfold PRF_q_Advantage
  rw [realGame_mkPRF_eq_hybGame_zero F A u hA, rfGame_eq_hybGame_of_indexBound F A u hA]
  refine (advantage_hybrid_dep_bool (hybGame F A) u).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [realGame_mkHybRed_eq, rfGame_mkHybRed_eq]

/-! ## Running time

The costs of `CatCryptCore.Crypto.OracleAdversaryTimed`: one unit per `rand` and per `query`
node. The step cost `c` of a query of `mkHybRed` is the cost of its bookkeeping: the rank of
its index, the lookup in the table of that rank or of its key, and the update of the state. -/

/-- The costed form of `hybImpl`: the step cost `c`, then the program `hybImpl F j s q`, which
has at most one `rand` or `query` node. -/
noncomputable def hybImpl.timed (c : ℕ) (F : K → D → R) (j : ℕ) (s : HybState N D R K)
    (q : N × D) : ℕ × OracleAdv.Timed D R (R × HybState N D R K) :=
  (c, OracleAdv.Timed.ofAdv (hybImpl F j s q))

theorem hybImpl.erase_timed (c : ℕ) (F : K → D → R) (j : ℕ) (s : HybState N D R K)
    (q : N × D) : (hybImpl.timed c F j s q).2.erase = hybImpl F j s q :=
  OracleAdv.Timed.erase_ofAdv _

/-- One query of `mkHybRed` takes time at most `c + 1`. -/
theorem hybImpl.timeBound_timed (c : ℕ) (F : K → D → R) (j : ℕ) (s : HybState N D R K)
    (q : N × D) : OracleAdv.Timed.StepTimeBound (hybImpl.timed c F j s q) (c + 1) := by
  refine ⟨Nat.le_succ c, ?_⟩
  show (OracleAdv.Timed.ofAdv (hybImpl F j s q)).TimeBound (c + 1 - c)
  rw [Nat.add_sub_cancel_left]
  unfold hybImpl
  split_ifs
  · split
    · trivial
    · exact ⟨le_rfl, fun _ => ⟨Nat.zero_le _, trivial⟩⟩
  · exact ⟨le_rfl, fun _ => ⟨Nat.zero_le _, trivial⟩⟩
  · split
    · trivial
    · exact ⟨le_rfl, fun _ => ⟨Nat.zero_le _, trivial⟩⟩

/-- The costed form of the reduction `mkHybRed`. -/
noncomputable def mkHybRed.timed (c : ℕ) (F : K → D → R)
    (A' : OracleAdv.Timed (N × D) R Bool) (j : ℕ) : ℕ × OracleAdv.Timed D R Bool :=
  OracleAdv.Timed.delay (OracleAdv.Timed.simulate (hybImpl.timed c F j) A' hybInit).1
    ((OracleAdv.Timed.simulate (hybImpl.timed c F j) A' hybInit).2.bind fun y => (0, .ret y.1))

/-- Erasing the step costs of the costed reduction gives the reduction of the erased
adversary. -/
theorem mkHybRed.erase_timed (c : ℕ) (F : K → D → R) (A' : OracleAdv.Timed (N × D) R Bool)
    (j : ℕ) : (mkHybRed.timed c F A' j).2.erase = mkHybRed F A'.erase j := by
  simp only [mkHybRed.timed, mkHybRed, OracleAdv.Timed.delay, OracleAdv.Timed.erase_bind,
    OracleAdv.Timed.erase_simulate, hybImpl.erase_timed]
  rfl

/-- **Time of the hybrid reduction.** An adversary of time `T` with at most `q` queries gives
a reduction of time at most `T + q * c`. -/
theorem mkHybRed.timeBound_timed (c : ℕ) (F : K → D → R) (j : ℕ)
    {A' : OracleAdv.Timed (N × D) R Bool} {T q : ℕ} (hT : A'.TimeBound T)
    (hq : A'.erase.IsQueryBound q) :
    OracleAdv.Timed.StepTimeBound (mkHybRed.timed c F A' j) (T + q * c) := by
  have h := Constructions.SIVNonce.timeBound_simulate_succ (hybImpl.timed c F j)
    (fun s d => hybImpl.timeBound_timed c F j s d) hT hq hybInit
  have h' := OracleAdv.Timed.stepTimeBound_delay
    (c := (OracleAdv.Timed.simulate (hybImpl.timed c F j) A' hybInit).1)
    (OracleAdv.Timed.timeBound_bind (n := 0) (f := fun y => (0, .ret y.1)) h.2
      fun _ => ⟨le_rfl, trivial⟩)
  exact h'.mono (by have := h.1; omega)

end Hybrid

end CatCrypt.Crypto.MultiKeyPRF
