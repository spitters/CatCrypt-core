/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Constructions.ECBCPRF
public import CatCryptCore.Crypto.OracleQueryVec
public import CatCryptCore.Tactics.QueryBound

/-!
# NMAC and HMAC are multi-query PRFs

For a compression function `f : K → B → K`, the cascade `cascade f k M` iterates
`f` over the blocks of `M` from the chaining value `k`, and generalized NMAC
(Bellare, *New Proofs for NMAC and HMAC: Security without Collision Resistance*,
CRYPTO 2006, §3) over messages of at most `ℓ` blocks with the key pair
`(k_in, k_out)` is `nmac f fpad ℓ (k_in, k_out) M = f k_out (fpad (cascade f k_in M))`,
where `fpad : K → B` is an injective padding of a chaining value into a block.

Against an adaptive adversary asking at most `q` queries, in the games of
`CatCryptCore.Crypto.PRPPRFSwitching`, the PRF advantage of NMAC is at most the PRF
advantage of `f` against the outer reduction `nmacOuterAdv`, plus, for every pair
of query positions `i < j < q` and every hybrid step `n < 2ℓ + 1`, the PRF
advantage of `f` against the two-query reduction `cascadeAdv f A i j n`, plus
`q(q-1)/2 / |K|` (`nmac_prf_bound`). This is Bellare 2006, Theorem 3.3, with the
averaging adversaries of Lemmas 3.1 and 3.2 written as a sum of fixed-index
reductions.

HMAC with key `k : Kh` (padded into a block by `kpad`) is NMAC keyed by
`(f iv (kpad k ⊕ ipad), f iv (kpad k ⊕ opad))`. Its PRF advantage is at most the
PRF advantage of the dual family `fun k x => f iv (kpad k ⊕ x)` against the
two-query reduction `hmacKeyAdv`, which queries `ipad` and `opad` and answers
every query of the adversary with NMAC under the two answers, plus the NMAC
bound (`hmac_prf_bound`). The dual-family game is the related-key PRF game of
Bellare 2006, §5, restricted to the two relations `⊕ ipad` and `⊕ opad`.

## Main definitions

* `cascade`, `nmac`, `hmac`
* `nmacOuterAdv f fpad A` — samples `k_in` and queries its oracle at
  `fpad (cascade f k_in M)` for each message query `M`
* `cascadeAdv f A i j n` — runs `A` against a lazily sampled random function,
  takes its `i`-th and `j`-th queries, and runs step `n` of the hybrid argument
  for the collision probability of the cascade on these two messages
* `hmacKeyAdv` — reduction from HMAC to the dual family

## Main results

* `nmac_prf_bound` — the multi-query PRF bound for NMAC
* `hmac_prf_bound` — the multi-query PRF bound for HMAC
* `cascade_coll_le` — the expected collision probability of the cascade on the
  queries of an adversary, bounded by the hybrid reductions (Bellare 2006,
  Lemmas 3.1 and 3.2)
* `pair_chain` — the hybrid chain for one pair of query positions

## Proof

The first hop replaces `f k_out` by a lazy random function (`realGame_nmac_eq`,
`rfGame_nmacOuterAdv_eq`). The second is `advantage_compose_le`: the random
function queried at the cascade value is distinguished from a random function on
messages by at most the expected probability that the cascade collides on the
table of queries. The union bound over pairs of positions reduces this to the
collision probability of two distinct messages, which the hybrid states
`List B × List B × Bool` bound: a state holds the two remaining suffixes and
whether they still share their chaining value. Each step replaces the leading
application of `f` by a uniform value (`hop_real_ge`, `hop_rf_eq`); when one
suffix is empty and the chaining value is shared, the step uses a second query at
another block to test the chaining value (Bellare 2006, Claim 3.6).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Constructions.NMACPRF

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.PRPPRF
open CatCrypt.Crypto.Constructions.ECBCPRF
open CatCrypt.Crypto.HashThenRF (advantage_compose_le)
open CatCrypt.Crypto.OracleAdv (QueryCollision)
open scoped ENNReal

/-! ## Cascade and NMAC -/

section Defs

variable {K B : Type}

/-- The cascade of `f` over the blocks of `M` from the chaining value `k`. -/
def cascade (f : K → B → K) (k : K) (M : List B) : K := M.foldl f k

@[simp] theorem cascade_nil (f : K → B → K) (k : K) : cascade f k [] = k := rfl

@[simp] theorem cascade_cons (f : K → B → K) (k : K) (b : B) (M : List B) :
    cascade f k (b :: M) = cascade f (f k b) M := rfl

/-- Generalized NMAC with the key pair `(k_in, k_out)` on messages of at most `ℓ`
blocks: `f k_out (fpad (cascade f k_in M))`. -/
def nmac (f : K → B → K) (fpad : K → B) (ℓ : ℕ) (k : K × K) (M : Msg B ℓ) : K :=
  f k.2 (fpad (cascade f k.1 M.1))

end Defs

/-! ## Lazy random functions with relabelled queries -/

section Relabel

variable {X Y R : Type} [DecidableEq X] [DecidableEq Y] [Fintype R] [Nonempty R]

/-- A table with its queries relabelled along `g`. -/
def relabel (g : X → Y) (t : List (X × R)) : List (Y × R) := t.map fun p => (g p.1, p.2)

omit [Fintype R] [Nonempty R] in
theorem lookup_relabel {g : X → Y} (hg : Function.Injective g) (d : X) (t : List (X × R)) :
    List.lookup (g d) (relabel g t) = List.lookup d t := by
  induction t with
  | nil => rfl
  | cons p t ih =>
    obtain ⟨a, b⟩ := p
    by_cases h : d = a
    · subst h; simp [relabel]
    · have h1 : (g d == g a) = false := by simpa using fun h' => h (hg h')
      have h2 : (d == a) = false := by simpa using h
      simp only [relabel, List.map_cons, List.lookup_cons, h1, h2] at ih ⊢
      exact ih

theorem rfOracle_relabel {g : X → Y} (hg : Function.Injective g) (t : List (X × R)) (d : X) :
    (rfOracle t d).map (Prod.map id (relabel g)) = rfOracle (relabel g t) (g d) := by
  unfold rfOracle
  rw [lookup_relabel hg]
  cases List.lookup d t with
  | some r => simp [PMF.pure_map]
  | none => simp [PMF.map_comp, Function.comp_def, relabel]

/-- A lazy random function queried through an injective map `g` gives the same
output distribution as a lazy random function queried directly. -/
theorem run_rfOracle_comp_injective {D α : Type} {g : X → Y} (hg : Function.Injective g)
    (c : D → X) (A : OracleAdv D R α) :
    (OracleAdv.run (fun t d => rfOracle t (g (c d))) A []).map Prod.fst =
      (OracleAdv.run (fun t d => rfOracle t (c d)) A []).map Prod.fst := by
  have h := OracleAdv.run_map_state (fun t d => rfOracle t (c d))
    (fun t d => rfOracle t (g (c d))) (relabel g) (fun s d => rfOracle_relabel hg s (c d)) A []
  change _ = OracleAdv.run _ A [] at h
  rw [← h, PMF.map_comp]
  rfl

end Relabel

/-! ## The outer hop -/

section Outer

variable {K B : Type} [Fintype K] [Nonempty K] {ℓ : ℕ}

/-- Reduction to the PRF security of the outer application of `f`: sample `k_in`
and answer each message query `M` with one oracle query at
`fpad (cascade f k_in M)`. It runs `A` once and asks as many queries as `A`. -/
noncomputable def nmacOuterAdv (f : K → B → K) (fpad : K → B)
    (A : OracleAdv (Msg B ℓ) K Bool) : OracleAdv B K Bool :=
  .rand (PMF.uniformFintype K) fun k₁ =>
    OracleAdv.mapQuery (fun M : Msg B ℓ => fpad (cascade f k₁ M.1)) A

theorem isQueryBound_nmacOuterAdv (f : K → B → K) (fpad : K → B) {q : ℕ}
    {A : OracleAdv (Msg B ℓ) K Bool} (hA : A.IsQueryBound q) :
    (nmacOuterAdv f fpad A).IsQueryBound q :=
  fun _ => OracleAdv.isQueryBound_mapQuery _ hA

/-- The real game of NMAC is the real game of `f` against the outer reduction. -/
theorem realGame_nmac_eq (f : K → B → K) (fpad : K → B) (A : OracleAdv (Msg B ℓ) K Bool) :
    realGame (nmac f fpad ℓ) A = realGame f (nmacOuterAdv f fpad A) := by
  unfold realGame nmacOuterAdv
  congr 1
  simp only [OracleAdv.run_rand, OracleAdv.run_mapQuery, PMF.map_bind]
  rw [PMF.uniform_prod_eq_bind, PMF.bind_comm (PMF.uniformFintype K), PMF.bind_bind]
  refine congrArg _ (funext fun k₁ => ?_)
  rw [PMF.bind_map]
  rfl

variable [DecidableEq K] [DecidableEq B]

/-- The ideal game of the outer reduction: a lazy random function on `K` queried at
the cascade value under a uniform `k_in`. -/
theorem rfGame_nmacOuterAdv_eq (f : K → B → K) {fpad : K → B}
    (hfpad : Function.Injective fpad) (A : OracleAdv (Msg B ℓ) K Bool) :
    rfGame (nmacOuterAdv f fpad A) =
      liftPMF ((PMF.uniformFintype K).bind fun k₁ =>
        (OracleAdv.run (fun t (M : Msg B ℓ) => rfOracle t (cascade f k₁ M.1)) A []).map
          Prod.fst) := by
  unfold rfGame nmacOuterAdv
  simp only [OracleAdv.run_rand, OracleAdv.run_mapQuery, PMF.map_bind]
  congr 1
  refine congrArg _ (funext fun k₁ => ?_)
  simp_all [run_rfOracle_comp_injective]

/-- The outer hop and the composition bound: the NMAC advantage is at most the PRF
advantage of the outer reduction plus the expected collision probability of the
cascade on the table of a lazy random function run. -/
theorem nmac_prf_le_outer_add_coll (f : K → B → K) {fpad : K → B}
    (hfpad : Function.Injective fpad) (A : OracleAdv (Msg B ℓ) K Bool) :
    PRF_q_Advantage (nmac f fpad ℓ) A ≤ PRF_q_Advantage f (nmacOuterAdv f fpad A) +
      ∑' x, OracleAdv.run rfOracle A [] x * (PMF.uniformFintype K).toOuterMeasure
        {k | QueryCollision (fun M : Msg B ℓ => cascade f k M.1) (x.2.map Prod.fst)} := by
  unfold PRF_q_Advantage
  rw [realGame_nmac_eq]
  refine (advantage_triangle _ (rfGame (nmacOuterAdv f fpad A)) _).trans (add_le_add le_rfl ?_)
  rw [rfGame_nmacOuterAdv_eq f hfpad]
  exact advantage_compose_le (fun (k : K) (M : Msg B ℓ) => cascade f k M.1) A

end Outer

/-! ## Hybrid steps for the collision probability of two messages -/

section Hybrid

variable {K B : Type} [Fintype K] [Nonempty K] [DecidableEq K] [DecidableEq B]

/-- The output distribution of `B` in the real game of `f`. -/
noncomputable def realPMF (f : K → B → K) (B' : OracleAdv B K Bool) : PMF Bool :=
  (PMF.uniformFintype K).bind fun k => (OracleAdv.run (keyedOracle f k) B' ()).map Prod.fst

/-- The output distribution of `B` in the random-function game. -/
noncomputable def rfPMF (B' : OracleAdv B K Bool) : PMF Bool :=
  (OracleAdv.run rfOracle B' []).map Prod.fst

omit [DecidableEq K] in
theorem realPMF_le_rfPMF_add (f : K → B → K) (B' : OracleAdv B K Bool) :
    realPMF f B' true ≤ rfPMF B' true + PRF_q_Advantage f B' := by
  have h : PRF_q_Advantage f B' =
      max (realPMF f B' true - rfPMF B' true) (rfPMF B' true - realPMF f B' true) := by
    simp only [PRF_q_Advantage, Advantage, realGame, rfGame, prTrue_liftPMF]
    rfl
  rw [h, add_comm]
  exact le_tsub_add.trans (add_le_add (le_max_left _ _) le_rfl)

/-- A hybrid state: the two remaining suffixes, and whether their chaining values
are the same uniform value (`true`) or two independent uniform values (`false`). -/
abbrev HState (B : Type) : Type := List B × List B × Bool

/-- The distribution of the event that the cascades of the two suffixes of a
hybrid state agree. -/
noncomputable def collPMF (f : K → B → K) : HState B → PMF Bool
  | (S₁, S₂, true) =>
      (PMF.uniformFintype K).map fun a => decide (cascade f a S₁ = cascade f a S₂)
  | (S₁, S₂, false) => (PMF.uniformFintype K).bind fun a =>
      (PMF.uniformFintype K).map fun b => decide (cascade f a S₁ = cascade f b S₂)

/-- One step of the hybrid argument: remove the leading block of each suffix whose
chaining value is replaced by a uniform value; a shared state whose suffixes
diverge, or of which one suffix is empty, becomes unshared. -/
def hstep : HState B → HState B
  | (x :: S₁, y :: S₂, true) => (S₁, S₂, decide (x = y))
  | ([], _ :: _, true) => ([], [], false)
  | (_ :: _, [], true) => ([], [], false)
  | ([], [], true) => ([], [], true)
  | (_ :: S₁, S₂, false) => (S₁, S₂, false)
  | ([], _ :: S₂, false) => ([], S₂, false)
  | ([], [], false) => ([], [], false)

/-- A block different from `y`. -/
noncomputable def otherBlock [Nontrivial B] (y : B) : B := Classical.choose (exists_ne y)

omit [DecidableEq B] in
theorem otherBlock_ne [Nontrivial B] (y : B) : otherBlock y ≠ y :=
  Classical.choose_spec (exists_ne y)

/-- The PRF adversary for one hybrid step, asking at most two queries. On a shared
state with nonempty suffixes it queries the leading blocks and compares the
cascades of the rest; on a shared state with one empty suffix `[]` and `y :: S` it
queries `y` and `otherBlock y` and tests whether `f` keyed by the cascade of `S`
agrees with the oracle at `otherBlock y` (Bellare 2006, adversary `A₂`); on an
unshared state it samples the other chaining value itself. -/
noncomputable def hop [Nontrivial B] (f : K → B → K) : HState B → OracleAdv B K Bool
  | (x :: S₁, y :: S₂, true) =>
      if x = y then .query x fun a => .ret (decide (cascade f a S₁ = cascade f a S₂))
      else .query x fun a => .query y fun b => .ret (decide (cascade f a S₁ = cascade f b S₂))
  | ([], y :: S₂, true) => .query y fun z => .query (otherBlock y) fun u =>
      .ret (decide (f (cascade f z S₂) (otherBlock y) = u))
  | (x :: S₁, [], true) => .query x fun z => .query (otherBlock x) fun u =>
      .ret (decide (f (cascade f z S₁) (otherBlock x) = u))
  | ([], [], true) => .ret true
  | (x :: S₁, S₂, false) => .rand (PMF.uniformFintype K) fun b =>
      .query x fun a => .ret (decide (cascade f a S₁ = cascade f b S₂))
  | ([], y :: S₂, false) => .rand (PMF.uniformFintype K) fun a =>
      .query y fun b => .ret (decide (a = cascade f b S₂))
  | ([], [], false) => .rand (PMF.uniformFintype K) fun a =>
      .rand (PMF.uniformFintype K) fun b => .ret (decide (a = b))

theorem isQueryBound_hop [Nontrivial B] (f : K → B → K) (s : HState B) :
    (hop f s).IsQueryBound 2 := by
  query_bound

omit [DecidableEq K] in
theorem rfOracle_nil (d : B) :
    rfOracle ([] : List (B × K)) d = (PMF.uniformFintype K).map fun r => (r, [(d, r)]) := rfl

omit [DecidableEq K] in
theorem rfOracle_single_of_ne {d e : B} (h : e ≠ d) (r : K) :
    rfOracle [(d, r)] e = (PMF.uniformFintype K).map fun r' => (r', [(e, r'), (d, r)]) := by
  have hb : (e == d) = false := by simpa using h
  simp [rfOracle, List.lookup_cons, hb]

omit [DecidableEq B] in
theorem uniform_map_decide_eq (w w' : K) :
    (PMF.uniformFintype K).map (fun u => decide (w = u)) =
      (PMF.uniformFintype K).map (fun u => decide (w' = u)) := by
  ext b
  cases b <;> simp [PMF.map_apply, tsum_fintype, Finset.sum_ite, Finset.filter_eq,
    Finset.filter_ne, Finset.card_erase_of_mem]

theorem hop_rf_eq [Nontrivial B] (f : K → B → K) (s : HState B) :
    rfPMF (hop f s) = collPMF f (hstep s) := by
  have hq : ∀ (w : K → K) (d e : B), e ≠ d →
      ((PMF.uniformFintype K).bind fun a =>
        (rfOracle [(d, a)] e).bind fun a₁ => PMF.pure (decide (w a = a₁.1))) =
      (PMF.uniformFintype K).bind fun a => (PMF.uniformFintype K).map fun b =>
        decide (a = b) := by
    intro w d e hed
    refine congrArg _ (funext fun a => ?_)
    rw [rfOracle_single_of_ne hed, PMF.bind_map]
    exact uniform_map_decide_eq (w a) a
  rcases s with ⟨_ | ⟨x, S₁⟩, _ | ⟨y, S₂⟩, _ | _⟩
  all_goals simp only [hop, hstep, collPMF, rfPMF, OracleAdv.run_query, OracleAdv.run_rand,
    OracleAdv.run_ret, rfOracle_nil, PMF.bind_map, PMF.map_bind, Function.comp_def,
    PMF.pure_map, cascade_nil, cascade_cons]
  · rfl
  · exact (PMF.map_const _ _).symm
  · rfl
  · exact hq _ _ _ (otherBlock_ne y)
  · rw [PMF.bind_comm]; rfl
  · exact hq _ _ _ (otherBlock_ne x)
  · rw [PMF.bind_comm]; rfl
  · split_ifs with h
    · subst h
      simp only [decide_true, OracleAdv.run_query, OracleAdv.run_ret, rfOracle_nil, PMF.bind_map,
        Function.comp_def, PMF.map_bind, PMF.pure_map]
      rfl
    · simp only [h, decide_false, OracleAdv.run_query, OracleAdv.run_ret, rfOracle_nil,
        PMF.bind_map, Function.comp_def, PMF.pure_map, PMF.map_bind,
        rfOracle_single_of_ne (Ne.symm h)]
      rfl

omit [DecidableEq K] [DecidableEq B] in
theorem uniform_map_apply_true_le (g h : K → Bool) (hgh : ∀ k, g k = true → h k = true) :
    ((PMF.uniformFintype K).map g) true ≤
      ((PMF.uniformFintype K).bind fun k => PMF.pure (h k)) true := by
  simp only [PMF.map_apply, PMF.bind_apply, PMF.pure_apply]
  refine ENNReal.tsum_le_tsum fun k => ?_
  by_cases hk : g k = true
  · simp [hk, hgh k hk]
  · simp [Ne.symm hk]

theorem hop_real_ge [Nontrivial B] (f : K → B → K) (s : HState B) :
    collPMF f s true ≤ realPMF f (hop f s) true := by
  rcases s with ⟨_ | ⟨x, S₁⟩, _ | ⟨y, S₂⟩, _ | _⟩
  all_goals simp only [hop, collPMF, realPMF, OracleAdv.run_query, OracleAdv.run_rand,
    OracleAdv.run_ret, keyedOracle, PMF.pure_bind, PMF.map_bind, PMF.pure_map, cascade_nil,
    cascade_cons]
  · rw [PMF.bind_const]; rfl
  · simp
  · rw [PMF.bind_comm]; rfl
  · refine uniform_map_apply_true_le _ _ fun k hk => ?_
    simp only [decide_eq_true_eq]
    rw [← of_decide_eq_true hk]
  · rfl
  · refine uniform_map_apply_true_le _ _ fun k hk => ?_
    simp only [decide_eq_true_eq]
    rw [of_decide_eq_true hk]
  · rfl
  · split_ifs with h
    · subst h
      simp only [OracleAdv.run_query, OracleAdv.run_ret, keyedOracle, PMF.pure_bind, PMF.pure_map]
      rfl
    · simp only [OracleAdv.run_query, OracleAdv.run_ret, keyedOracle, PMF.pure_bind, PMF.pure_map]
      rfl

/-! ### Termination of the hybrid sequence -/

/-- The length of the hybrid sequence left from a state. -/
def hpot (s : HState B) : ℕ := s.1.length + s.2.1.length + (if s.2.2 then 1 else 0)

/-- A shared state has distinct suffixes. -/
def HInv (s : HState B) : Prop := s.2.2 = true → s.1 ≠ s.2.1

omit [Fintype K] [Nonempty K] [DecidableEq K] in
theorem hInv_hstep {s : HState B} (hs : HInv s) : HInv (hstep s) := by
  rcases s with ⟨_ | ⟨x, S₁⟩, _ | ⟨y, S₂⟩, _ | _⟩ <;>
    simp_all [HInv, hstep]

omit [Fintype K] [Nonempty K] [DecidableEq K] in
theorem hpot_hstep {s : HState B} (hs : HInv s) :
    hpot (hstep s) + 1 ≤ hpot s ∨ s = ([], [], false) := by
  rcases s with ⟨_ | ⟨x, S₁⟩, _ | ⟨y, S₂⟩, _ | _⟩ <;>
    simp_all [HInv, hstep, hpot]
  split_ifs <;> (simp; try omega)

omit [Fintype K] [Nonempty K] [DecidableEq K] in
theorem hstep_iterate_eq {s : HState B} (hs : HInv s) {N : ℕ} (hN : hpot s ≤ N) :
    hstep^[N] s = ([], [], false) := by
  induction N generalizing s with
  | zero =>
    rcases s with ⟨_ | ⟨x, S₁⟩, _ | ⟨y, S₂⟩, _ | _⟩ <;> simp_all [hpot]
  | succ N ih =>
    rw [Function.iterate_succ_apply]
    rcases hpot_hstep hs with h | h
    · exact ih (hInv_hstep hs) (by omega)
    · subst h
      exact ih (by simp [HInv, hstep]) (by simp [hpot, hstep])

omit [DecidableEq B] in
theorem collPMF_terminal (f : K → B → K) :
    collPMF f ([], [], false) true = (Fintype.card K : ℝ≥0∞)⁻¹ := by
  obtain ⟨a₀⟩ := ‹Nonempty K›
  have h : collPMF f ([], [], false) =
      (PMF.uniformFintype K).map (fun b => decide (a₀ = b)) := by
    show ((PMF.uniformFintype K).bind fun a =>
      (PMF.uniformFintype K).map fun b => decide (a = b)) = _
    simp only [uniform_map_decide_eq _ a₀]
    exact PMF.bind_const _ _
  rw [h, PMF.map_apply, tsum_fintype, Finset.sum_eq_single a₀]
  · simp
  · grind
  · simp

omit [DecidableEq K] [DecidableEq B] in
theorem realPMF_rand (f : K → B → K) {β : Type} (p : PMF β) (g : β → OracleAdv B K Bool) :
    realPMF f (.rand p g) = p.bind fun x => realPMF f (g x) := by
  unfold realPMF
  simp only [OracleAdv.run_rand, PMF.map_bind]
  exact PMF.bind_comm _ _ _

omit [DecidableEq K] in
theorem rfPMF_rand {β : Type} (p : PMF β) (g : β → OracleAdv B K Bool) :
    rfPMF (.rand p g) = p.bind fun x => rfPMF (g x) := by
  simp_all [rfPMF, OracleAdv.run_rand, PMF.map_bind]

end Hybrid

/-! ## The collision term -/

section Coll

variable {K B : Type} [Fintype K] [Nonempty K] [DecidableEq K] [DecidableEq B] {ℓ : ℕ}

/-- The hybrid state of the `i`-th and `j`-th entries of a query table, when both
exist and carry distinct messages. -/
def pairState (T : List (Msg B ℓ × K)) (i j : ℕ) : Option (HState B) :=
  match T[i]?, T[j]? with
  | some p, some p' => if p.1 = p'.1 then none else some (p.1.1, p'.1.1, true)
  | _, _ => none

omit [Fintype K] [Nonempty K] [DecidableEq K] in
theorem pairState_spec {T : List (Msg B ℓ × K)} {i j : ℕ} {s : HState B}
    (h : pairState T i j = some s) : HInv s ∧ hpot s ≤ 2 * ℓ + 1 ∧ s.2.2 = true := by
  unfold pairState at h
  split at h
  · rename_i p p' _ _
    split_ifs at h with hpp
    cases h
    refine ⟨fun _ hM => hpp (Subtype.ext hM), ?_, rfl⟩
    have h₁ := p.1.2
    have h₂ := p'.1.2
    simp only [hpot, ite_true]
    omega
  · cases h

/-- Reduction for step `n` of the hybrid argument on the `i`-th and `j`-th queries:
run `A` once against a lazily sampled random function, and, when its table has
entries `i` and `j` with distinct messages, run the two-query adversary `hop` of
the `n`-th hybrid state of the two messages. -/
noncomputable def cascadeAdv [Nontrivial B] (f : K → B → K) (A : OracleAdv (Msg B ℓ) K Bool)
    (i j n : ℕ) : OracleAdv B K Bool :=
  .rand (OracleAdv.run rfOracle A []) fun x =>
    match pairState x.2 i j with
    | some s => hop f (hstep^[n] s)
    | none => .ret false

theorem isQueryBound_cascadeAdv [Nontrivial B] (f : K → B → K) (A : OracleAdv (Msg B ℓ) K Bool)
    (i j n : ℕ) : (cascadeAdv f A i j n).IsQueryBound 2 := by
  query_bound

/-- The probability of the `n`-th hybrid state of the `i`-th and `j`-th entries of a
table, and `0` when they do not form a pair of distinct messages. -/
noncomputable def pairG (f : K → B → K) (T : List (Msg B ℓ × K)) (i j n : ℕ) : ℝ≥0∞ :=
  match pairState T i j with
  | some s => collPMF f (hstep^[n] s) true
  | none => 0

theorem pair_chain_step [Nontrivial B] (f : K → B → K) (A : OracleAdv (Msg B ℓ) K Bool)
    (i j n : ℕ) :
    ∑' x, OracleAdv.run rfOracle A [] x * pairG f x.2 i j n ≤
      ∑' x, OracleAdv.run rfOracle A [] x * pairG f x.2 i j (n + 1) +
        PRF_q_Advantage f (cascadeAdv f A i j n) := by
  have hR : ∑' x, OracleAdv.run rfOracle A [] x * pairG f x.2 i j n ≤
      realPMF f (cascadeAdv f A i j n) true := by
    rw [cascadeAdv, realPMF_rand, PMF.bind_apply]
    refine ENNReal.tsum_le_tsum fun x => ?_
    gcongr
    cases h : pairState x.2 i j with
    | some s => simpa only [pairG, h] using hop_real_ge f _
    | none => simp only [pairG, h, zero_le]
  have hQ : rfPMF (cascadeAdv f A i j n) true =
      ∑' x, OracleAdv.run rfOracle A [] x * pairG f x.2 i j (n + 1) := by
    rw [cascadeAdv, rfPMF_rand, PMF.bind_apply]
    refine tsum_congr fun x => congrArg _ ?_
    cases h : pairState x.2 i j with
    | some s =>
      simp only [pairG, h]
      rw [hop_rf_eq, Function.iterate_succ_apply']
    | none => simp [pairG, h, rfPMF]
  exact hR.trans ((realPMF_le_rfPMF_add f _).trans_eq (by rw [hQ]))

theorem pair_chain [Nontrivial B] (f : K → B → K) (A : OracleAdv (Msg B ℓ) K Bool)
    (i j N : ℕ) :
    ∑' x, OracleAdv.run rfOracle A [] x * pairG f x.2 i j 0 ≤
      ∑' x, OracleAdv.run rfOracle A [] x * pairG f x.2 i j N +
        ∑ n ∈ Finset.range N, PRF_q_Advantage f (cascadeAdv f A i j n) := by
  induction N with
  | zero => simp
  | succ N ih =>
    refine ih.trans ?_
    rw [Finset.sum_range_succ]
    calc _ ≤ (∑' x, OracleAdv.run rfOracle A [] x * pairG f x.2 i j (N + 1) +
          PRF_q_Advantage f (cascadeAdv f A i j N)) +
          ∑ n ∈ Finset.range N, PRF_q_Advantage f (cascadeAdv f A i j n) :=
          add_le_add_left (pair_chain_step f A i j N) _
      _ = _ := by ring

theorem tsum_pairG_terminal (f : K → B → K) (A : OracleAdv (Msg B ℓ) K Bool) (i j : ℕ) :
    ∑' x, OracleAdv.run rfOracle A [] x * pairG f x.2 i j (2 * ℓ + 1) ≤
      (Fintype.card K : ℝ≥0∞)⁻¹ := by
  have h : ∀ T : List (Msg B ℓ × K), pairG f T i j (2 * ℓ + 1) ≤ (Fintype.card K : ℝ≥0∞)⁻¹ := by
    intro T
    cases h : pairState T i j with
    | some s =>
      obtain ⟨hinv, hpot, -⟩ := pairState_spec h
      simp only [pairG, h, hstep_iterate_eq hinv hpot, collPMF_terminal, le_refl]
    | none => simp only [pairG, h, zero_le]
  calc ∑' x, OracleAdv.run rfOracle A [] x * pairG f x.2 i j (2 * ℓ + 1)
      ≤ ∑' x, OracleAdv.run rfOracle A [] x * (Fintype.card K : ℝ≥0∞)⁻¹ :=
        ENNReal.tsum_le_tsum fun x => by gcongr; exact h x.2
    _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

theorem pairG_zero_eq (f : K → B → K) (T : List (Msg B ℓ × K)) (i j : ℕ) :
    (PMF.uniformFintype K).toOuterMeasure
        {k | ∃ s, pairState T i j = some s ∧ cascade f k s.1 = cascade f k s.2.1} =
      pairG f T i j 0 := by
  cases h : pairState T i j with
  | some s =>
    obtain ⟨-, -, hs⟩ := pairState_spec h
    obtain ⟨S₁, S₂, sh⟩ := s
    simp only at hs
    subst hs
    simp only [pairG, h, Function.iterate_zero, id, collPMF]
    rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
    congr 1
    ext k
    simp
  | none => simp [pairG, h]

omit [Fintype K] [Nonempty K] [DecidableEq K] in
theorem hasColl_pairState (f : K → B → K) (T : List (Msg B ℓ × K)) (k : K) {q : ℕ}
    (hT : T.length ≤ q)
    (h : QueryCollision (fun M : Msg B ℓ => cascade f k M.1) (T.map Prod.fst)) :
    ∃ j ∈ Finset.range q, ∃ i ∈ Finset.range j,
      ∃ s, pairState T i j = some s ∧ cascade f k s.1 = cascade f k s.2.1 := by
  obtain ⟨x, hx, y, hy, hne, hc⟩ := h
  obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
  obtain ⟨p', hp', rfl⟩ := List.mem_map.1 hy
  obtain ⟨a, ha⟩ := List.mem_iff_getElem?.1 hp
  obtain ⟨b, hb⟩ := List.mem_iff_getElem?.1 hp'
  have ha' : a < T.length := (List.getElem?_eq_some_iff.1 ha).1
  have hb' : b < T.length := (List.getElem?_eq_some_iff.1 hb).1
  rcases lt_trichotomy a b with hab | rfl | hab
  · refine ⟨b, Finset.mem_range.2 (by omega), a, Finset.mem_range.2 hab,
      (p.1.1, p'.1.1, true), ?_, hc⟩
    simp [pairState, ha, hb, hne]
  · exact (hne (by rw [Option.some.inj (ha.symm.trans hb)])).elim
  · refine ⟨a, Finset.mem_range.2 (by omega), b, Finset.mem_range.2 hab,
      (p'.1.1, p.1.1, true), ?_, hc.symm⟩
    simp [pairState, ha, hb, Ne.symm hne]

omit [DecidableEq K] in
theorem length_le_of_mem_support_run_rfOracle {D α : Type} [DecidableEq D]
    (A : OracleAdv D K α) (n : ℕ) (hA : A.IsQueryBound n) (t : List (D × K)) :
    ∀ x ∈ (OracleAdv.run rfOracle A t).support, x.2.length ≤ t.length + n := by
  induction A generalizing n t with
  | ret a =>
    simp_all
  | rand p k ih =>
    intro x hx
    simp only [OracleAdv.run_rand, PMF.mem_support_bind_iff] at hx
    obtain ⟨b, -, hb⟩ := hx
    exact ih b n (hA b) t x hb
  | query d k ih =>
    cases n with
    | zero => exact hA.elim
    | succ n =>
    intro x hx
    simp only [OracleAdv.run_query, PMF.mem_support_bind_iff] at hx
    obtain ⟨y, hy, hxy⟩ := hx
    have hlen : y.2.length ≤ t.length + 1 := by
      unfold rfOracle at hy
      cases hl : List.lookup d t with
      | some r =>
        grind [PMF.support_pure]
      | none =>
        rw [hl] at hy
        simp only [PMF.support_map, Set.mem_image] at hy
        obtain ⟨r, -, rfl⟩ := hy
        simp
    have := ih y.1 n (hA y.1) y.2 x hxy
    omega

/-- **Collision term of the cascade.** For an adversary asking at most `q` queries,
the expected probability, over the table of a lazy random function run and a
uniform key, that the cascade collides on two distinct queried messages is at
most, summed over the pairs of positions `i < j < q`, the PRF advantages of `f`
against the `2ℓ + 1` hybrid reductions plus `1/|K|` (Bellare 2006, Lemmas 3.1
and 3.2). -/
theorem cascade_coll_le [Nontrivial B] (f : K → B → K) (A : OracleAdv (Msg B ℓ) K Bool) (q : ℕ)
    (hA : A.IsQueryBound q) :
    ∑' x, OracleAdv.run rfOracle A [] x * (PMF.uniformFintype K).toOuterMeasure
        {k | QueryCollision (fun M : Msg B ℓ => cascade f k M.1) (x.2.map Prod.fst)} ≤
      ∑ j ∈ Finset.range q, ∑ i ∈ Finset.range j,
        (∑ n ∈ Finset.range (2 * ℓ + 1), PRF_q_Advantage f (cascadeAdv f A i j n) +
          (Fintype.card K : ℝ≥0∞)⁻¹) := by
  have hpt : ∀ x, OracleAdv.run rfOracle A [] x * (PMF.uniformFintype K).toOuterMeasure
      {k | QueryCollision (fun M : Msg B ℓ => cascade f k M.1) (x.2.map Prod.fst)} ≤
      OracleAdv.run rfOracle A [] x *
        ∑ j ∈ Finset.range q, ∑ i ∈ Finset.range j, pairG f x.2 i j 0 := by
    intro x
    by_cases hx : x ∈ (OracleAdv.run rfOracle A []).support
    · have hT : x.2.length ≤ q := by
        simpa using length_le_of_mem_support_run_rfOracle A q hA [] x hx
      gcongr
      refine (MeasureTheory.measure_mono (s := {k | QueryCollision _ (x.2.map Prod.fst)})
        (t := ⋃ j ∈ Finset.range q, ⋃ i ∈ Finset.range j,
          {k | ∃ s, pairState x.2 i j = some s ∧ cascade f k s.1 = cascade f k s.2.1})
        fun k hk => ?_).trans ?_
      · obtain ⟨j, hj, i, hi, hs⟩ := hasColl_pairState f x.2 k hT hk
        simp only [Set.mem_iUnion]
        grind
      · refine (MeasureTheory.measure_biUnion_finset_le _ _).trans
          (Finset.sum_le_sum fun j _ => (MeasureTheory.measure_biUnion_finset_le _ _).trans
            (Finset.sum_le_sum fun i _ => (pairG_zero_eq f x.2 i j).le))
    · simp_all [zero_mul]
  refine (ENNReal.tsum_le_tsum hpt).trans ?_
  simp only [Finset.mul_sum]
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  refine Finset.sum_le_sum fun i _ => ?_
  refine (pair_chain f A i j (2 * ℓ + 1)).trans ?_
  rw [add_comm]
  gcongr
  simp_all [tsum_pairG_terminal]

end Coll

/-! ## NMAC is a PRF -/

section NMAC

variable {K B : Type} [Fintype K] [Nonempty K] [DecidableEq K] [DecidableEq B] [Nontrivial B]
  {ℓ : ℕ}

/-- **NMAC is a multi-query PRF** (Bellare 2006, Theorem 3.3). For a compression
function `f`, an injective padding `fpad`, and an adversary asking at most `q`
adaptive queries of at most `ℓ` blocks, the PRF advantage of NMAC is at most the
PRF advantage of `f` against `nmacOuterAdv f fpad A` (at most `q` queries), plus
the PRF advantages of `f` against the reductions `cascadeAdv f A i j n` (at most
two queries each) for `i < j < q` and `n < 2ℓ + 1`, plus `q(q-1)/2 / |K|`.
Bellare's bound has `(n₁ + n₂ - 1)` hybrid steps per pair of messages of `n₁`
and `n₂` blocks, averaged into one adversary; here the steps of a pair beyond its
length are reductions without queries, whose advantage is `0`. -/
theorem nmac_prf_bound (f : K → B → K) {fpad : K → B} (hfpad : Function.Injective fpad)
    (A : OracleAdv (Msg B ℓ) K Bool) (q : ℕ) (hA : A.IsQueryBound q) :
    PRF_q_Advantage (nmac f fpad ℓ) A ≤
      PRF_q_Advantage f (nmacOuterAdv f fpad A) +
        ∑ j ∈ Finset.range q, ∑ i ∈ Finset.range j,
          ∑ n ∈ Finset.range (2 * ℓ + 1), PRF_q_Advantage f (cascadeAdv f A i j n) +
        ((q * (q - 1) / 2 : ℕ) : ℝ≥0∞) / Fintype.card K := by
  refine (nmac_prf_le_outer_add_coll f hfpad A).trans ?_
  rw [add_assoc]
  gcongr
  refine (cascade_coll_le f A q hA).trans_eq ?_
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  congr 1
  rw [ENNReal.div_eq_inv_mul, mul_comm]
  grind [Finset.sum_mul, Nat.cast_sum, Finset.sum_range_id]

end NMAC

/-! ## HMAC -/

section HMAC

variable {K B Kh : Type} [XorOp B]

/-- The dual family of HMAC key derivation: the key `k` padded into a block,
masked with the block `x`, compressed from the initial value `iv`. -/
def hmacKeyFamily (f : K → B → K) (iv : K) (kpad : Kh → B) (k : Kh) (x : B) : K :=
  f iv (kpad k ^^^ x)

/-- HMAC with key `k`: NMAC keyed by `(f iv (kpad k ⊕ ipad), f iv (kpad k ⊕ opad))`. -/
def hmac (f : K → B → K) (fpad : K → B) (iv : K) (ipad opad : B) (kpad : Kh → B) (ℓ : ℕ)
    (k : Kh) (M : Msg B ℓ) : K :=
  nmac f fpad ℓ (hmacKeyFamily f iv kpad k ipad, hmacKeyFamily f iv kpad k opad) M

/-- Reduction from HMAC to the dual family: query `ipad` and `opad`, and answer
every query `M` of `A` with NMAC keyed by the two answers. It runs `A` once and
asks two queries. -/
def hmacKeyAdv (f : K → B → K) (fpad : K → B) (ipad opad : B) {ℓ : ℕ}
    (A : OracleAdv (Msg B ℓ) K Bool) : OracleAdv B K Bool :=
  .query ipad fun kin => .query opad fun kout =>
    OracleAdv.subst (fun M : Msg B ℓ => .ret (nmac f fpad ℓ (kin, kout) M)) A

omit [XorOp B] in
theorem isQueryBound_hmacKeyAdv (f : K → B → K) (fpad : K → B) (ipad opad : B) {ℓ q : ℕ}
    {A : OracleAdv (Msg B ℓ) K Bool} (hA : A.IsQueryBound q) :
    (hmacKeyAdv f fpad ipad opad A).IsQueryBound 2 := by
  have h : ∀ kin kout : K, (OracleAdv.subst (fun M : Msg B ℓ =>
      (.ret (nmac f fpad ℓ (kin, kout) M) : OracleAdv B K K)) A).IsQueryBound 0 :=
    fun _ _ => OracleAdv.isQueryBound_subst (c := 0) (fun _ => by query_bound) hA
  query_bound

omit [XorOp B] in
/-- Running the simulation of every query by a fixed function from any state gives
the output distribution of the keyed oracle of that function. -/
theorem run_simulate_ret_map_fst {D S R₀ : Type} (F : D → R₀) (A : OracleAdv D R₀ Bool)
    (O : S → B → PMF (K × S)) (s : S) :
    (OracleAdv.run O (OracleAdv.subst (fun d => .ret (F d)) A) s).map Prod.fst =
      (OracleAdv.run (keyedOracle (fun (F : D → R₀) d => F d) F) A ()).map Prod.fst := by
  rw [OracleAdv.run_subst]
  have h := OracleAdv.run_map_state (keyedOracle (fun (F : D → R₀) d => F d) F)
    (fun s d => OracleAdv.run O (.ret (F d)) s) (fun _ => s)
    (fun _ _ => by simp [keyedOracle, PMF.pure_map]) A ()
  rw [← h, PMF.map_comp]
  rfl

variable [Fintype K] [Nonempty K] [Fintype Kh] [Nonempty Kh] {ℓ : ℕ}

omit [Fintype K] [Nonempty K] in
/-- The real game of HMAC is the real game of the dual family against the key
reduction. -/
theorem realGame_hmac_eq (f : K → B → K) (fpad : K → B) (iv : K) (ipad opad : B)
    (kpad : Kh → B) (A : OracleAdv (Msg B ℓ) K Bool) :
    realGame (hmac f fpad iv ipad opad kpad ℓ) A =
      realGame (hmacKeyFamily f iv kpad) (hmacKeyAdv f fpad ipad opad A) := by
  unfold realGame
  congr 1
  refine congrArg _ (funext fun k => ?_)
  simp only [hmacKeyAdv, OracleAdv.run_query, keyedOracle, PMF.pure_bind]
  rw [run_simulate_ret_map_fst]
  rfl

variable [DecidableEq B]

omit [XorOp B] in
/-- The ideal game of the key reduction is the real game of NMAC when
`ipad ≠ opad`: the two answers are independent uniform keys. -/
theorem rfGame_hmacKeyAdv_eq (f : K → B → K) (fpad : K → B) {ipad opad : B}
    (hpad : ipad ≠ opad) (A : OracleAdv (Msg B ℓ) K Bool) :
    rfGame (hmacKeyAdv f fpad ipad opad A) = realGame (nmac f fpad ℓ) A := by
  unfold rfGame realGame
  congr 1
  have hne : (opad == ipad) = false := by simpa using Ne.symm hpad
  simp only [hmacKeyAdv, OracleAdv.run_query, PMF.map_bind]
  rw [PMF.uniform_prod_eq_bind]
  simp only [rfOracle, List.lookup_nil, List.lookup_cons, hne, PMF.bind_map, Function.comp_def,
    PMF.bind_bind]
  refine congrArg _ (funext fun kin => ?_)
  refine congrArg _ (funext fun kout => ?_)
  rw [run_simulate_ret_map_fst]
  rfl

variable [DecidableEq K] [Nontrivial B]

/-- **HMAC is a multi-query PRF** (Bellare 2006, §5). For `ipad ≠ opad`, an
injective padding `fpad` and an adversary asking at most `q` adaptive queries of
at most `ℓ` blocks, the PRF advantage of HMAC is at most the PRF advantage of the
dual family `hmacKeyFamily f iv kpad` against the two-query reduction
`hmacKeyAdv` (the related-key PRF game on the key `k`, with the relations
`⊕ ipad` and `⊕ opad`), plus the NMAC bound `nmac_prf_bound`. -/
theorem hmac_prf_bound (f : K → B → K) {fpad : K → B} (hfpad : Function.Injective fpad)
    (iv : K) {ipad opad : B} (hpad : ipad ≠ opad) (kpad : Kh → B)
    (A : OracleAdv (Msg B ℓ) K Bool) (q : ℕ) (hA : A.IsQueryBound q) :
    PRF_q_Advantage (hmac f fpad iv ipad opad kpad ℓ) A ≤
      PRF_q_Advantage (hmacKeyFamily f iv kpad) (hmacKeyAdv f fpad ipad opad A) +
        (PRF_q_Advantage f (nmacOuterAdv f fpad A) +
          ∑ j ∈ Finset.range q, ∑ i ∈ Finset.range j,
            ∑ n ∈ Finset.range (2 * ℓ + 1), PRF_q_Advantage f (cascadeAdv f A i j n) +
          ((q * (q - 1) / 2 : ℕ) : ℝ≥0∞) / Fintype.card K) := by
  have h := nmac_prf_bound f hfpad A q hA
  unfold PRF_q_Advantage at h ⊢
  rw [realGame_hmac_eq]
  refine (advantage_triangle _ (rfGame (hmacKeyAdv f fpad ipad opad A)) _).trans
    (add_le_add le_rfl ?_)
  rw [rfGame_hmacKeyAdv_eq f fpad hpad]
  exact h

end HMAC

end CatCrypt.Crypto.Constructions.NMACPRF
