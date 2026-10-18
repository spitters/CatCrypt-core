/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Consensus.PoSNSB.Prob.Reduction

/-!
# PoS-NSB: hash collisions reduce to collision resistance

The theorems of the PoS-NSB port assume `collision_free`: the hash function is injective on the
genesis block and the broadcast blocks. For a keyed hash family `H` (`HashFam`), this file
defines the collision-resistance game and, for every adversary `A` against the signed protocol,
an explicit collision finder `collFinder P A H μ W K`. Given the key, the finder samples the
lottery and the key pairs of the parties itself, runs the real execution of the first `K`
phases with the hash function under the key, and outputs the encodings of two distinct blocks of
the final state with equal hashes (Thomsen and Spitters, CSF 2021, Remark 1).

The advantage `crAdv B` is the probability, over a uniformly random key and the coins of `B`,
that `B` outputs two distinct points with the same hash. It is the search game
`CR_Search_Game` of `CatCryptCore/Crypto/Assumptions/CR.lean` for the keyed family `H`, stated
over `PMF` with the coins of the adversary drawn independently of the key.

## Main definitions

* `CRAdversary H`, `crWins`, `crInputs`, `crAdv`: the collision-resistance game and the
  advantage; `crAdv_le_of_forall` bounds the advantage by a bound for every choice of coins.
* `findColl h l`: the first pair of distinct elements of `l` with equal images under `h`.
* `collFinder P A H μ W K`: the reduction.

## Main results

* `seedDistH_eq_map`: the seed distribution `seedDistH H` is the image of the inputs of the
  collision-resistance game of the finder.
* `collFinder_wins`: a collision among the broadcast blocks of some state of the first `K`
  phases makes the finder win.
* `prob_collision_le`: the probability that some state of the first `K` phases is not
  collision free is at most `crAdv (collFinder P A H μ W K)`.
* `crAdv_randomFun_le_of_queries`: for the random oracle `HashFam.randomFun`, if the broadcast
  blocks are among the first `q` queries of a querier, the advantage of the finder is at most
  the birthday bound `q (q - 1) / 2 / |Hash|`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

namespace CatCryptCore.Consensus.PoSNSB

open Parameters BlockParameters Corruption Execution
open scoped ENNReal

/-! ## The collision-resistance game -/

section CR

variable {D R : Type}

/-- An adversary against the collision resistance of the keyed hash family `H`: coins drawn
from a distribution, and a function of the key and the coins that outputs a candidate
collision. -/
structure CRAdversary (H : HashFam D R) where
  /-- The coins of the adversary. -/
  Coins : Type
  /-- The distribution of the coins. -/
  coins : PMF Coins
  /-- The candidate collision for a key and coins. -/
  find : H.Key → Coins → D × D

/-- The adversary wins with key `k` and coins `c`: it outputs two distinct points with the same
hash under `k`. -/
def crWins {H : HashFam D R} (B : CRAdversary H) (k : H.Key) (c : B.Coins) : Prop :=
  (B.find k c).1 ≠ (B.find k c).2 ∧ H.hash k (B.find k c).1 = H.hash k (B.find k c).2

/-- The joint distribution of the key and the coins: a uniformly random key and independent
coins. -/
noncomputable def crInputs {H : HashFam D R} (B : CRAdversary H) : PMF (H.Key × B.Coins) :=
  (PMF.uniformOfFintype H.Key).bind fun k => B.coins.bind fun c => PMF.pure (k, c)

/-- The collision-resistance advantage: the probability that the adversary wins. -/
noncomputable def crAdv {H : HashFam D R} (B : CRAdversary H) : ℝ≥0∞ :=
  (crInputs B).toOuterMeasure {x | crWins B x.1 x.2}

/-- If for all coins the adversary wins with probability at most `ε` over the key, its
advantage is at most `ε`. -/
theorem crAdv_le_of_forall {H : HashFam D R} (B : CRAdversary H) (ε : ℝ≥0∞)
    (h : ∀ c, (PMF.uniformOfFintype H.Key).toOuterMeasure {k | crWins B k c} ≤ ε) :
    crAdv B ≤ ε := by
  have hin : crInputs B = B.coins.bind fun c =>
      (PMF.uniformOfFintype H.Key).map fun k => (k, c) := by
    simp only [crInputs, ← PMF.bind_pure_comp]
    exact PMF.bind_comm _ _ _
  rw [crAdv, hin, PMF.toOuterMeasure_bind_apply]
  calc ∑' c, B.coins c * ((PMF.uniformOfFintype H.Key).map fun k => (k, c)).toOuterMeasure
          {x | crWins B x.1 x.2}
      ≤ ∑' c, B.coins c * ε := by
        refine ENNReal.tsum_le_tsum fun c => mul_le_mul_right ?_ _
        rw [PMF.toOuterMeasure_map_apply]
        exact h c
    _ = ε := by rw [ENNReal.tsum_mul_right, B.coins.tsum_coe, one_mul]

end CR

/-! ## Finding a colliding pair in a list -/

section FindColl

variable {B R : Type} [DecidableEq B] [DecidableEq R]

/-- The first pair of distinct elements of `l` with equal images under `h`. -/
def findColl (h : B → R) (l : List B) : Option (B × B) :=
  (l.flatMap fun b => l.map fun b' => (b, b')).find? fun p => decide (p.1 ≠ p.2 ∧ h p.1 = h p.2)

theorem findColl_some {h : B → R} {l : List B} {b b' : B} (hf : findColl h l = some (b, b')) :
    b ∈ l ∧ b' ∈ l ∧ b ≠ b' ∧ h b = h b' := by
  have h1 := List.mem_of_find?_eq_some hf
  have h2 := List.find?_some hf
  simp only [List.mem_flatMap, List.mem_map, Prod.mk.injEq] at h1
  simp only [decide_eq_true_eq] at h2
  obtain ⟨x, hx, y, hy, rfl, rfl⟩ := h1
  exact ⟨hx, hy, h2⟩

theorem findColl_eq_none {h : B → R} {l : List B} (hf : findColl h l = none) :
    ∀ b ∈ l, ∀ b' ∈ l, h b = h b' → b = b' := by
  intro b hb b' hb' hh
  by_contra hne
  have := List.find?_eq_none.1 hf (b, b') (List.mem_flatMap.2 ⟨b, hb, List.mem_map_of_mem hb'⟩)
  simp [hne, hh] at this

end FindColl

/-! ## The collision finder -/

section Finder

variable {Tx Hash : Type} [DecidableEq Tx] [DecidableEq Hash] [Fintype Tx] [Fintype Hash]
  [Nonempty Hash] {np : ℕ} [Corruption (Fin np)] {n Hz : ℕ}
  {Sch : SigScheme (Block Tx Hash (Fin np))}
  (P : Protocol Tx Hash np n Hz) (A : Adversary Tx Hash np n Hz Sch)

/-- A colliding pair among the genesis block and the broadcast blocks of the state after `K`
phases of the real execution for the seed `ω`. -/
def collPair (ω : Seed Tx Hash np n Hz Sch) (K : ℕ) :
    Option (Block Tx Hash (Fin np) × Block Tx Hash (Fin np)) :=
  letI := ω.params P; letI := ω.bparams P
  findColl HashB (block_hist_gb (sTrace P ω A false K))

/-- **The reduction.** The collision finder obtained from the adversary `A` against the signed
protocol: its coins are a leader string drawn from `leaderDist μ P.h0 W n` and key pairs drawn
from `keyDist Sch`. Given the key `k`, it runs the first `K` phases of the real execution with the
hash function `H.hash k` and outputs the encodings of a colliding pair of the genesis block and
the broadcast blocks of the final state, and a fixed pair of equal points when there is none. -/
noncomputable def collFinder (H : HashFam (BlockDom Tx Hash np Hz) Hash)
    (μ : PMF (Option (Fin np))) (W K : ℕ) : CRAdversary H where
  Coins := (Fin n → Option (Fin np)) × (Fin np → Sch.PK × Sch.SK)
  coins := (leaderDist μ P.h0 W n).bind fun L => (keyDist Sch).bind fun ks => PMF.pure (L, ks)
  find := fun k c =>
    match collPair P A (⟨c.1, H.hash k, c.2⟩ : Seed Tx Hash np n Hz Sch) K with
    | some (b, b') => (encB Hz b, encB Hz b')
    | none => (encB Hz P.GB, encB Hz P.GB)

/-- The seed distribution `seedDistH H` is the image of the inputs of the collision-resistance
game of the finder under `(k, (L, ks)) ↦ ⟨L, H.hash k, ks⟩`. -/
theorem seedDistH_eq_map (H : HashFam (BlockDom Tx Hash np Hz) Hash)
    (μ : PMF (Option (Fin np))) (W K : ℕ) :
    seedDistH H μ P.h0 W n Sch = (crInputs (collFinder P A H μ W K)).map
      fun x => (⟨x.2.1, H.hash x.1, x.2.2⟩ : Seed Tx Hash np n Hz Sch) := by
  simp only [crInputs, collFinder, seedDistH, PMF.map_bind, PMF.pure_map, PMF.bind_bind,
    PMF.pure_bind]
  exact PMF.bind_comm _ _ _

/-- The genesis block and the broadcast blocks of the state after `K` phases of the real
execution have slots at most `Hz`. -/
theorem block_hist_gb_sl_le (ω : Seed Tx Hash np n Hz Sch) (K : ℕ) (hHz : K + 1 ≤ Hz)
    (hGB : P.GB.sl ≤ 1) :
    letI := ω.params P; letI := ω.bparams P
    ∀ b ∈ block_hist_gb (sTrace P ω A false K), b.sl ≤ Hz := by
  let _ := ω.params P; let _ := ω.bparams P
  intro b hb
  rcases List.mem_cons.1 hb with rfl | hm
  · simp only [GenesisBlock]; omega
  · simp only [block_history] at hm
    obtain ⟨m, hm', rfl⟩ := List.mem_map.1 hm
    have h1 := sTrace_slots P ω A K m hm'
    have h2 : (sTrace P ω A false K).t_now ≤ K + 1 := by
      let _ := mkExec false P ω A
      exact runTrace_t_now (Tx := Tx) (Hash := Hash) (Party := Fin np) (AdvState := A.AdvState) K
    omega

/-- **The finder wins on a collision.** If some state of the first `K` phases of the real
execution for the seed `⟨L, H.hash k, ks⟩` is not collision free, the finder wins with key `k`
and coins `(L, ks)`. -/
theorem collFinder_wins (H : HashFam (BlockDom Tx Hash np Hz) Hash) (μ : PMF (Option (Fin np)))
    (W K : ℕ) (hHz : K + 1 ≤ Hz) (hGB : P.GB.sl ≤ 1) (k : H.Key)
    (c : (collFinder P A H μ W K).Coins) (j : ℕ) (hj : j ≤ K)
    (hcf : letI := (⟨c.1, H.hash k, c.2⟩ : Seed Tx Hash np n Hz Sch).params P
      letI := (⟨c.1, H.hash k, c.2⟩ : Seed Tx Hash np n Hz Sch).bparams P
      ¬collision_free (sTrace P (⟨c.1, H.hash k, c.2⟩ : Seed Tx Hash np n Hz Sch) A false j)) :
    crWins (collFinder P A H μ W K) k c := by
  set ω : Seed Tx Hash np n Hz Sch := ⟨c.1, H.hash k, c.2⟩ with hω
  let _ := ω.params P; let _ := ω.bparams P
  have hK : ¬collision_free (sTrace P ω A false K) := by
    intro h
    let _ := mkExec false P ω A
    exact hcf (collision_free_prev (runTrace_reach hj) h)
  have hsl := block_hist_gb_sl_le P A ω K hHz hGB
  cases hp : collPair P A ω K with
  | none => exact absurd (findColl_eq_none hp) hK
  | some bb =>
    obtain ⟨b, b'⟩ := bb
    obtain ⟨hb, hb', hne, hh⟩ := findColl_some hp
    have hfind : (collFinder P A H μ W K).find k c = (encB Hz b, encB Hz b') := by
      simp only [collFinder, ← hω, hp]
    simp only [crWins, hfind]
    exact ⟨fun he => hne (encB_inj (hsl b hb) (hsl b' hb') he), hh⟩

/-- **Hash collisions.** Over the seed distribution `seedDistH H`, the probability that some
state of the first `K` phases of the real execution is not collision free is at most the
collision-resistance advantage of the explicit adversary `collFinder P A H μ W K`. -/
theorem prob_collision_le (H : HashFam (BlockDom Tx Hash np Hz) Hash)
    (μ : PMF (Option (Fin np))) (W K : ℕ) (hHz : K + 1 ≤ Hz) (hGB : P.GB.sl ≤ 1) :
    (seedDistH H μ P.h0 W n Sch).toOuterMeasure
        {ω | ∃ j ≤ K, letI := ω.params P; letI := ω.bparams P;
          ¬collision_free (sTrace P ω A false j)} ≤
      crAdv (collFinder P A H μ W K) := by
  rw [seedDistH_eq_map P A H μ W K, PMF.toOuterMeasure_map_apply, crAdv]
  refine MeasureTheory.OuterMeasure.mono _ fun x hx => ?_
  obtain ⟨j, hj, hcf⟩ := hx
  exact collFinder_wins P A H μ W K hHz hGB x.1 x.2 j hj hcf

/-- **The finder against the random oracle.** For the hash family `HashFam.randomFun`, if the
genesis block and the broadcast blocks of the first `K` phases of the real execution are among
the first `q` queries of the querier `next ω.κ ω.ks` to `ω.f` for every seed `ω`, the
collision-resistance advantage of `collFinder` is at most the birthday bound
`q (q - 1) / 2 / |Hash|`. -/
theorem crAdv_randomFun_le_of_queries (μ : PMF (Option (Fin np))) (W K q : ℕ)
    (next : (Fin n → SlotKind) → (Fin np → Sch.PK × Sch.SK) →
      Querier (BlockDom Tx Hash np Hz) Hash)
    (hRO : ∀ ω : Seed Tx Hash np n Hz Sch, ∀ j ≤ K, letI := ω.params P; letI := ω.bparams P;
      ∀ b ∈ block_hist_gb (sTrace P ω A false j), ∃ k < q, query (next ω.κ ω.ks) ω.f k = encB Hz b) :
    crAdv (collFinder P A (HashFam.randomFun (BlockDom Tx Hash np Hz) Hash) μ W K) ≤
      ((q * (q - 1) / 2 : ℕ) : ℝ≥0∞) / Fintype.card Hash := by
  have hwin : ∀ (f : BlockDom Tx Hash np Hz → Hash) (L : Fin n → Option (Fin np))
      (ks : Fin np → Sch.PK × Sch.SK),
      crWins (collFinder P A (HashFam.randomFun (BlockDom Tx Hash np Hz) Hash) μ W K) f (L, ks) →
        ROCollision (next (kinds L) ks) q f := by
    intro f L ks ⟨hne, hh⟩
    set ω : Seed Tx Hash np n Hz Sch := ⟨L, f, ks⟩ with hω
    cases hp : collPair P A ω K with
    | none =>
      simp only [collFinder, HashFam.randomFun, id, ← hω, hp] at hne
      exact absurd rfl hne
    | some bb =>
      obtain ⟨b, b'⟩ := bb
      obtain ⟨hb, hb', -, -⟩ := findColl_some hp
      simp only [collFinder, HashFam.randomFun, id, ← hω, hp] at hne hh
      obtain ⟨a, ha, hqa⟩ := hRO ω K le_rfl b hb
      obtain ⟨a', ha', hqa'⟩ := hRO ω K le_rfl b' hb'
      exact ⟨a, ha, a', ha', by rw [hqa, hqa']; exact hne, by rw [hqa, hqa']; exact hh⟩
  refine crAdv_le_of_forall _ _ fun c => ?_
  refine (MeasureTheory.OuterMeasure.mono _ fun f hf => hwin f c.1 c.2 hf).trans ?_
  exact prob_ROCollision_le (next (kinds c.1) c.2) q

end Finder

end CatCryptCore.Consensus.PoSNSB
