/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Consensus.PoSNSB.Prob.Reduction
public import CatCryptCore.Crypto.Assumptions.CRCoins

/-!
# PoS-NSB: hash collisions reduce to collision resistance

The theorems of the PoS-NSB port assume `collision_free`: the hash function is injective on the
genesis block and the broadcast blocks. For a keyed hash family `H` (`HashScheme` of
`CatCryptCore/Crypto/Assumptions/CR.lean`) with a codec `cd` of the block domain, this file
defines, for every adversary `A` against the signed protocol, an explicit collision-search
adversary `collFinder Sch P A H cd μ W K` against `H`. Its coins are a lottery and key pairs
(`CR_Search_Adversary.ofCoins`); given the key, it runs the real execution of the first `K`
phases with the hash function `cd.hashOn` under the key, and outputs the encoded inputs of two
distinct blocks of the final state with equal hashes (Thomsen and Spitters, CSF 2021,
Remark 1). Its advantage is `CR_Search_Advantage H (collFinder …)`, the search game
`CR_Search_Game`.

## Main definitions

* `findColl h l`: the first pair of distinct elements of `l` with equal images under `h`.
* `collCoins`, `collFind`, `collFinder Sch P A H cd μ W K`: the reduction.
* `collFinderG Sch P H cd μ W K G tx adv`: the reduction for a computation `G` of a value `x`
  from the seed, with the transactions `tx x` and the adversary `adv x`.

## Main results

* `seedDist_eq_map`: the seed distribution `seedDist Sch H cd` is the uniform key bound to the
  image of the coins of the finder.
* `collFind_wins`: a collision among the broadcast blocks of some state of the first `K`
  phases makes the output of the finder a collision.
* `prob_collision_le`: the probability that some state of the first `K` phases is not
  collision free is at most `CR_Search_Advantage H (collFinder Sch P A H cd μ W K)`.
* `prob_collisionG_le`: the same bound for the transactions and the adversary computed by `G`
  from the seed, against `collFinderG`.
* `sampleFrom_ofPMF_bind`, `sampleFrom_ofPMF_map`: sampling from a bound or mapped `PMF`.
* `collFinder_advantage_randomFun_le`: for the random function `HashScheme.randomFun` and the
  identity codec, if the broadcast blocks are among the first `q` queries of a querier, the
  advantage of the finder is at most the birthday bound `q (q - 1) / 2 / |Hash|`.
* `collFind_zero_fst_eq`, `collFinderG_zero_advantage_eq_zero`: at zero phases the finder
  outputs two equal inputs, so `collFinderG … 0 …` has advantage `0` for every computation `G`,
  every transaction selection and every adversary.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

namespace CatCryptCore.Consensus.PoSNSB

open Parameters BlockParameters Corruption Execution
open CatCrypt.Crypto CatCrypt.Crypto.Signatures CatCrypt.Crypto.Assumptions
open scoped ENNReal

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

/-- If for every second coordinate `b` the event `g a b` has probability at most `ε` over
`a ∼ p`, the event has probability at most `ε` over independent `a ∼ p` and `b ∼ q`. -/
theorem bind_map_apply_le {α β : Type} (p : PMF α) (q : PMF β) (g : α → β → Bool) (ε : ℝ≥0∞)
    (h : ∀ b, (p.map fun a => g a b) true ≤ ε) : (p.bind fun a => q.map (g a)) true ≤ ε := by
  have e : (p.bind fun a => q.map (g a)) = q.bind fun b => p.map fun a => g a b := by
    show (p.bind fun a => q.bind fun b => PMF.pure (g a b)) =
      q.bind fun b => p.bind fun a => PMF.pure (g a b)
    exact PMF.bind_comm _ _ _
  rw [e, PMF.bind_apply]
  calc ∑' b, q b * (p.map fun a => g a b) true ≤ ∑' b, q b * ε :=
        ENNReal.tsum_le_tsum fun b => by gcongr; exact h b
    _ = ε := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-! ## The collision finder -/

section Finder

variable {Tx Hash : Type} [DecidableEq Tx] [DecidableEq Hash] {np : ℕ} [Corruption (Fin np)]
  {n Hz : ℕ} {PK SK Sig : Type}
  (Sch : PSigScheme (Block Tx Hash (Fin np)) PK SK Sig) [hS : Sch.Deterministic]
  (P : Protocol Tx Hash np n Hz) (A : Adversary Tx Hash np n Hz PK Sig)

/-- A colliding pair among the genesis block and the broadcast blocks of the state after `K`
phases of the real execution for the seed `ω`. -/
def collPair (ω : Seed Tx Hash np n Hz PK SK) (K : ℕ) :
    Option (Block Tx Hash (Fin np) × Block Tx Hash (Fin np)) :=
  letI := ω.params P; letI := ω.bparams P
  findColl HashB (block_hist_gb (sTrace Sch P ω A false K))

/-- The coins of the collision finder: a leader string drawn from `leaderDist μ P.h0 W n` and
independent key pairs from `Sch.keyDist`. -/
noncomputable def collCoins (μ : PMF (Option (Fin np))) (W : ℕ) :
    PMF ((Fin n → Option (Fin np)) × (Fin np → PK × SK)) :=
  (leaderDist μ P.h0 W n).bind fun L =>
    (PMF.piFin fun _ => Sch.keyDist).bind fun ks => PMF.pure (L, ks)

/-- The output of the collision finder under the key `k` with coins `c`: run the first `K`
phases of the real execution for the seed `⟨c.1, cd.hashOn k, c.2⟩` and output the encoded
inputs of a colliding pair of the genesis block and the broadcast blocks of the final state,
and the encoded genesis block twice when there is none. -/
def collFind (H : HashScheme) (cd : H.Codec (BlockDom Tx Hash np Hz) Hash) (K : ℕ) (k : H.Key)
    (c : (Fin n → Option (Fin np)) × (Fin np → PK × SK)) : H.Input × H.Input :=
  match collPair Sch P A (⟨c.1, cd.hashOn k, c.2⟩ : Seed Tx Hash np n Hz PK SK) K with
  | some (b, b') => (cd.inp (encB Hz b), cd.inp (encB Hz b'))
  | none => (cd.inp (encB Hz P.GB), cd.inp (encB Hz P.GB))

/-- **The reduction.** The collision-search adversary obtained from the adversary `A` against
the signed protocol: coins from `collCoins Sch P μ W` and output `collFind`. -/
noncomputable def collFinder (H : HashScheme) (cd : H.Codec (BlockDom Tx Hash np Hz) Hash)
    (μ : PMF (Option (Fin np))) (W K : ℕ) : CR_Search_Adversary H :=
  CR_Search_Adversary.ofCoins (collCoins Sch P μ W) (collFind Sch P A H cd K)

/-- The seed distribution `seedDist Sch H cd` draws a uniform key `k` and maps the coins of
the finder by `(L, ks) ↦ ⟨L, cd.hashOn k, ks⟩`. -/
theorem seedDist_eq_map (H : HashScheme) (cd : H.Codec (BlockDom Tx Hash np Hz) Hash)
    (μ : PMF (Option (Fin np))) (W : ℕ) :
    seedDist Sch H cd μ P.h0 W n = (PMF.uniformFintype H.Key).bind fun k =>
      (collCoins Sch P μ W).map fun c => (⟨c.1, cd.hashOn k, c.2⟩ : Seed Tx Hash np n Hz PK SK) := by
  simp only [collCoins, seedDist, PMF.map_bind, PMF.pure_map]
  exact PMF.bind_comm _ _ _

/-- The genesis block and the broadcast blocks of the state after `K` phases of the real
execution have slots at most `Hz`. -/
theorem block_hist_gb_sl_le (ω : Seed Tx Hash np n Hz PK SK) (K : ℕ) (hHz : K + 1 ≤ Hz)
    (hGB : P.GB.sl ≤ 1) :
    letI := ω.params P; letI := ω.bparams P
    ∀ b ∈ block_hist_gb (sTrace Sch P ω A false K), b.sl ≤ Hz := by
  let _ := ω.params P; let _ := ω.bparams P
  intro b hb
  rcases List.mem_cons.1 hb with rfl | hm
  · simp only [GenesisBlock]; omega
  · simp only [block_history] at hm
    obtain ⟨m, hm', rfl⟩ := List.mem_map.1 hm
    have h1 := sTrace_slots Sch P ω A K m hm'
    have h2 : (sTrace Sch P ω A false K).t_now ≤ K + 1 := by
      let _ := mkExec Sch false P ω A
      exact runTrace_t_now (Tx := Tx) (Hash := Hash) (Party := Fin np) (AdvState := A.AdvState) K
    omega

/-- **The finder wins on a collision.** If some state of the first `K` phases of the real
execution for the seed `⟨c.1, cd.hashOn k, c.2⟩` is not collision free, the output of the
finder under the key `k` with coins `c` is a collision of `H` under `k`. -/
theorem collFind_wins (H : HashScheme) (cd : H.Codec (BlockDom Tx Hash np Hz) Hash) (K : ℕ)
    (hHz : K + 1 ≤ Hz) (hGB : P.GB.sl ≤ 1) (k : H.Key)
    (c : (Fin n → Option (Fin np)) × (Fin np → PK × SK)) (j : ℕ) (hj : j ≤ K)
    (hcf : letI := (⟨c.1, cd.hashOn k, c.2⟩ : Seed Tx Hash np n Hz PK SK).params P
      letI := (⟨c.1, cd.hashOn k, c.2⟩ : Seed Tx Hash np n Hz PK SK).bparams P
      ¬collision_free
        (sTrace Sch P (⟨c.1, cd.hashOn k, c.2⟩ : Seed Tx Hash np n Hz PK SK) A false j)) :
    coinsCollision (collFind Sch P A H cd K) k c = true := by
  set ω : Seed Tx Hash np n Hz PK SK := ⟨c.1, cd.hashOn k, c.2⟩ with hω
  let _ := ω.params P; let _ := ω.bparams P
  have hK : ¬collision_free (sTrace Sch P ω A false K) := by
    intro h
    let _ := mkExec Sch false P ω A
    exact hcf (collision_free_prev (runTrace_reach hj) h)
  have hsl := block_hist_gb_sl_le Sch P A ω K hHz hGB
  cases hp : collPair Sch P A ω K with
  | none => exact absurd (findColl_eq_none hp) hK
  | some bb =>
    obtain ⟨b, b'⟩ := bb
    obtain ⟨hb, hb', hne, hh⟩ := findColl_some hp
    have hfind : collFind Sch P A H cd K k c = (cd.inp (encB Hz b), cd.inp (encB Hz b')) := by
      simp only [collFind, ← hω, hp]
    have hcoll : cd.collision k (encB Hz b) (encB Hz b') :=
      ⟨hh, fun he => hne (encB_inj (hsl b hb) (hsl b' hb') he)⟩
    rw [cd.collision_iff] at hcoll
    simp only [coinsCollision, hfind, decide_eq_true_eq]
    exact hcoll

/-- **Hash collisions.** Over the seed distribution `seedDist Sch H cd`, the probability that
some state of the first `K` phases of the real execution is not collision free is at most the
collision-resistance advantage `CR_Search_Advantage H` of the explicit adversary
`collFinder Sch P A H cd μ W K`. -/
theorem prob_collision_le (H : HashScheme) (cd : H.Codec (BlockDom Tx Hash np Hz) Hash)
    (μ : PMF (Option (Fin np))) (W K : ℕ) (hHz : K + 1 ≤ Hz) (hGB : P.GB.sl ≤ 1) :
    (seedDist Sch H cd μ P.h0 W n).toOuterMeasure
        {ω | ∃ j ≤ K, letI := ω.params P; letI := ω.bparams P;
          ¬collision_free (sTrace Sch P ω A false j)} ≤
      CR_Search_Advantage H (collFinder Sch P A H cd μ W K) := by
  rw [seedDist_eq_map Sch P H cd μ W, collFinder, CR_Search_Advantage_ofCoins,
    ← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_bind_apply,
    PMF.toOuterMeasure_bind_apply]
  refine ENNReal.tsum_le_tsum fun k => ?_
  gcongr
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply]
  refine MeasureTheory.OuterMeasure.mono _ fun c hc => ?_
  obtain ⟨j, hj, hcf⟩ := hc
  exact collFind_wins Sch P A H cd K hHz hGB k c j hj hcf

open CatCrypt.Core CatCrypt.NonUniform

omit [DecidableEq Tx] [DecidableEq Hash] [Corruption (Fin np)] in
/-- Sampling from a bound `PMF` is sampling the first value and then from its continuation. -/
theorem sampleFrom_ofPMF_bind {α β : Type} (p : PMF α) (f : α → PMF β) :
    sampleFrom (ofPMF (p.bind f)) =
      SPComp.bind (sampleFrom (ofPMF p)) fun a => sampleFrom (ofPMF (f a)) := by
  rw [sampleFrom_bind_sampleFrom]
  congr 1
  simp only [ofPMF, CatCrypt.Prob.SDistr.bind, PMF.map_bind, PMF.bind_map, Function.comp_def]

omit [DecidableEq Tx] [DecidableEq Hash] [Corruption (Fin np)] in
/-- Sampling from the image of a `PMF` is sampling from the `PMF` and returning the image. -/
theorem sampleFrom_ofPMF_map {α β : Type} (p : PMF α) (g : α → β) :
    sampleFrom (ofPMF (p.map g)) =
      SPComp.bind (sampleFrom (ofPMF p)) fun a => SPComp.pure (g a) := by
  show sampleFrom (ofPMF (p.bind (PMF.pure ∘ g))) = _
  rw [sampleFrom_ofPMF_bind]
  congr 1; funext a
  rw [← sampleFrom_pure]
  congr 1
  simp [ofPMF, CatCrypt.Prob.SDistr.pure, PMF.pure_map]

/-- **The generalised reduction.** For a computation `G` of a value `x` from the seed, the
transactions `tx x` and the adversary `adv x`: draw coins `c` from `collCoins Sch P μ W`, run `G`
on the seed `⟨c.1, cd.hashOn k, c.2⟩` of the key `k`, and output
`collFind` for the protocol with the transactions `tx x` and the adversary `adv x`. -/
noncomputable def collFinderG {X : Type} (H : HashScheme)
    (cd : H.Codec (BlockDom Tx Hash np Hz) Hash) (μ : PMF (Option (Fin np))) (W K : ℕ)
    (G : Seed Tx Hash np n Hz PK SK → SPComp X) (tx : X → Slot → Fin np → Tx)
    (adv : X → Adversary Tx Hash np n Hz PK Sig) : CR_Search_Adversary H :=
  fun k => SPComp.bind (sampleFrom (ofPMF (collCoins Sch P μ W))) fun c =>
    SPComp.bind (G ⟨c.1, cd.hashOn k, c.2⟩) fun x =>
      SPComp.pure (collFind Sch { P with txSel := tx x } (adv x) H cd K k c)

open Classical in
/-- **Hash collisions of a computation of the adversary.** Over the seed distribution
`seedDist Sch H cd` and the value `x` that `G` computes from the seed, from the empty heap, the
probability that some state of the first `K` phases of the real execution with the transactions
`tx x` and the adversary `adv x` is not collision free is at most the collision-resistance
advantage of the explicit adversary `collFinderG Sch P H cd μ W K G tx adv`. -/
theorem prob_collisionG_le {X : Type} (H : HashScheme)
    (cd : H.Codec (BlockDom Tx Hash np Hz) Hash) (μ : PMF (Option (Fin np))) (W K : ℕ)
    (hHz : K + 1 ≤ Hz) (hGB : P.GB.sl ≤ 1) (G : Seed Tx Hash np n Hz PK SK → SPComp X)
    (tx : X → Slot → Fin np → Tx) (adv : X → Adversary Tx Hash np n Hz PK Sig) :
    prTrue (SPComp.bind (sampleFrom (ofPMF (seedDist Sch H cd μ P.h0 W n))) fun ω =>
      SPComp.bind (G ω) fun x => SPComp.pure (decide (∃ j ≤ K,
        letI := ω.params P; letI := ω.bparams P
        ¬collision_free (sTrace Sch { P with txSel := tx x } ω (adv x) false j)))) Heap.empty ≤
      CR_Search_Advantage H (collFinderG Sch P H cd μ W K G tx adv) := by
  rw [seedDist_eq_map Sch P H cd μ W, sampleFrom_ofPMF_bind]
  simp_rw [sampleFrom_ofPMF_map]
  unfold CR_Search_Advantage CR_Search_Game collFinderG
  rw [show SPComp.sample H.Key = sampleFrom (ofPMF (PMF.uniformFintype H.Key)) from rfl]
  simp only [SPComp.monad_bind_eq, SPComp.bind_assoc, SPComp.pure_bind]
  rw [prTrue_bind_sampleFrom, prTrue_bind_sampleFrom]
  refine ENNReal.tsum_le_tsum fun k => ?_
  gcongr
  rw [prTrue_bind_sampleFrom, prTrue_bind_sampleFrom]
  refine ENNReal.tsum_le_tsum fun c => ?_
  gcongr
  refine ForkingLemma.prTrue_bind_mono _ _ _ _ fun x h' => ?_
  by_cases hb : ∃ j ≤ K, letI := (⟨c.1, cd.hashOn k, c.2⟩ : Seed Tx Hash np n Hz PK SK).params P
      letI := (⟨c.1, cd.hashOn k, c.2⟩ : Seed Tx Hash np n Hz PK SK).bparams P
      ¬collision_free (sTrace Sch { P with txSel := tx x }
        (⟨c.1, cd.hashOn k, c.2⟩ : Seed Tx Hash np n Hz PK SK) (adv x) false j)
  · obtain ⟨j, hj, hcf⟩ := hb
    have hw := collFind_wins Sch { P with txSel := tx x } (adv x) H cd K hHz hGB k c j hj hcf
    simp only [coinsCollision] at hw
    rw [hw]
    exact (prTrue_le_one _ _).trans (by simp [ForkingLemma.prTrue_pure_bool])
  · simp only [hb, decide_false, ForkingLemma.prTrue_pure_bool]
    simp

/-- **The finder against the random function.** For the keyed family
`HashScheme.randomFun` with the identity codec, if the genesis block and the broadcast blocks
of the first `K` phases of the real execution are among the first `q` queries of the querier
`next ω.κ ω.ks` to `ω.f` for every seed `ω`, the collision-resistance advantage of
`collFinder` is at most the birthday bound `q (q - 1) / 2 / |Hash|`. -/
theorem collFinder_advantage_randomFun_le [Fintype Tx] [Fintype Hash] [Nonempty Hash]
    (μ : PMF (Option (Fin np))) (W K q : ℕ)
    (next : (Fin n → SlotKind) → (Fin np → PK × SK) → Querier (BlockDom Tx Hash np Hz) Hash)
    (hRO : ∀ ω : Seed Tx Hash np n Hz PK SK, ∀ j ≤ K, letI := ω.params P; letI := ω.bparams P;
      ∀ b ∈ block_hist_gb (sTrace Sch P ω A false j),
        ∃ k < q, query (next ω.κ ω.ks) ω.f k = encB Hz b) :
    CR_Search_Advantage (HashScheme.randomFun (BlockDom Tx Hash np Hz) Hash)
        (collFinder Sch P A (HashScheme.randomFun (BlockDom Tx Hash np Hz) Hash)
          (HashScheme.Codec.id _) μ W K) ≤
      ((q * (q - 1) / 2 : ℕ) : ℝ≥0∞) / Fintype.card Hash := by
  have hwin : ∀ (f : BlockDom Tx Hash np Hz → Hash)
      (c : (Fin n → Option (Fin np)) × (Fin np → PK × SK)),
      coinsCollision (collFind Sch P A (HashScheme.randomFun (BlockDom Tx Hash np Hz) Hash)
        (HashScheme.Codec.id _) K) f c = true → ROCollision (next (kinds c.1) c.2) q f := by
    intro f c hc
    simp only [coinsCollision, decide_eq_true_eq] at hc
    obtain ⟨hh, hne⟩ := hc
    cases hp : collPair Sch P A (⟨c.1, (HashScheme.Codec.id
        (HashScheme.randomFun (BlockDom Tx Hash np Hz) Hash)).hashOn f, c.2⟩ :
          Seed Tx Hash np n Hz PK SK) K with
    | none =>
      simp only [collFind, hp] at hne
      exact absurd rfl hne
    | some bb =>
      obtain ⟨b, b'⟩ := bb
      obtain ⟨hb, hb', -, -⟩ := findColl_some hp
      simp only [collFind, hp] at hne hh
      obtain ⟨a, ha, hqa⟩ := hRO _ K le_rfl b hb
      obtain ⟨a', ha', hqa'⟩ := hRO _ K le_rfl b' hb'
      have hqa : query (next (kinds c.1) c.2) f a = encB Hz b := hqa
      have hqa' : query (next (kinds c.1) c.2) f a' = encB Hz b' := hqa'
      exact ⟨a, ha, a', ha', by rw [hqa, hqa']; exact hne, by rw [hqa, hqa']; exact hh⟩
  rw [collFinder, CR_Search_Advantage_ofCoins]
  refine bind_map_apply_le _ _ _ _ fun c => ?_
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  refine (MeasureTheory.OuterMeasure.mono _ fun f hf => hwin f c hf).trans ?_
  exact prob_ROCollision_le (next (kinds c.1) c.2) q

end Finder

/-! ## The collision finder at zero phases -/

section CollZero

open CatCrypt.Core

variable {Tx Hash : Type} [DecidableEq Tx] [DecidableEq Hash] {np : ℕ} [Corruption (Fin np)]
  {n Hz : ℕ} {PK SK Sig : Type}
  (P : Protocol Tx Hash np n Hz) (Sch : PSigScheme (Block Tx Hash (Fin np)) PK SK Sig)
  [Sch.Deterministic]

/-- At zero phases the finder outputs two equal inputs: the genesis block is the only block of
the initial state. -/
theorem collFind_zero_fst_eq (A : Adversary Tx Hash np n Hz PK Sig) (H : HashScheme)
    (cd : H.Codec (BlockDom Tx Hash np Hz) Hash) (k : H.Key)
    (c : (Fin n → Option (Fin np)) × (Fin np → PK × SK)) :
    (collFind Sch P A H cd 0 k c).1 = (collFind Sch P A H cd 0 k c).2 := by
  unfold collFind
  cases hp : collPair Sch P A (⟨c.1, cd.hashOn k, c.2⟩ : Seed Tx Hash np n Hz PK SK) 0 with
  | none => rfl
  | some bb =>
    obtain ⟨b, b'⟩ := bb
    obtain ⟨hb, hb', hne, -⟩ := findColl_some hp
    simp only [sTrace, runTrace, Function.iterate_zero, id, block_hist_gb, block_history, N0,
      List.map_nil, List.mem_singleton] at hb hb'
    exact absurd (hb.trans hb'.symm) hne

/-- **The collision finder at zero phases has advantage `0`**, for every computation `G` of a
value from the seed, every transaction selection and every adversary. -/
theorem collFinderG_zero_advantage_eq_zero {X : Type} (H : HashScheme)
    (cd : H.Codec (BlockDom Tx Hash np Hz) Hash) (μ : PMF (Option (Fin np))) (W : ℕ)
    (G : Seed Tx Hash np n Hz PK SK → SPComp X) (tx : X → Slot → Fin np → Tx)
    (adv : X → Adversary Tx Hash np n Hz PK Sig) :
    CR_Search_Advantage H (collFinderG Sch P H cd μ W 0 G tx adv) = 0 := by
  unfold CR_Search_Advantage CR_Search_Game collFinderG
  simp only [SPComp.monad_bind_eq, SPComp.bind_assoc, SPComp.pure_bind]
  refine Signatures.prTrue_bind_eq_zero _ _ _ fun k _ =>
    Signatures.prTrue_bind_eq_zero _ _ _ fun c _ =>
      Signatures.prTrue_bind_eq_zero _ _ _ fun x h => ?_
  rw [collFind_zero_fst_eq]
  simp [ForkingLemma.prTrue_pure_bool]

end CollZero

end CatCryptCore.Consensus.PoSNSB
