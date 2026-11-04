/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Constructions.ECBCPRF
public import CatCryptCore.Tactics.AutoMetrics

/-!
# CBC$ is IND-CPA secure

CBC$ encrypts a message `M = m₁ … mₙ` of at most `ℓ` blocks under a keyed block
function `E k` by sampling a uniform IV `c₀` and returning `(c₀, c₁ … cₙ)` with
`cᵢ = E k (cᵢ₋₁ ⊕ mᵢ)`. Against an adaptive adversary asking at most `q`
encryption queries, in the games of `CatCryptCore.Crypto.PRPPRFSwitching`:

* the real-or-random advantage (encryptions against a uniform IV with uniform
  blocks) is at most `PRP_q_Advantage E (cbcRorAdv A) + qℓ(qℓ-1) / |B|`;
* the left-or-right advantage is at most the PRP advantages of `E` against the
  two reductions `cbcLorAdv false A` and `cbcLorAdv true A` plus
  `2 qℓ(qℓ-1) / |B|`.

Each reduction asks at most `qℓ` queries. This is the CBC bound of
Bellare–Desai–Jokipii–Rogaway (FOCS 1997).

## Main definitions

* `cbcBlocks f s M` — the CBC blocks of `M` under `f` from the chaining value `s`
* `blocksVec cs`, `cbcVec f iv m` — a list of blocks as a vector of `n` blocks, and the CBC
  encryption of a vector of blocks
* `cbcEncrypt f M`, `randCiphertext n` — CBC$ encryption and a uniform ciphertext
* `cbcRealGame E A`, `cbcRandGame A`, `CBC_ROR_Advantage E A` — real-or-random game
* `cbcLRGame E b A`, `CBC_IND_CPA_Advantage E A` — left-or-right game on pairs of
  messages with the same number of blocks
* `cbcRorAdv A`, `cbcLorAdv b A` — the reductions to the PRP games of `E`
* `repFlagOracle`, `freshFlagOracle` — a lazy random function and a fresh-answer
  oracle, both flagging a repeated query

## Main results

* `cbc_ror_bound` — the real-or-random bound
* `cbc_ind_cpa_bound`, `cbc_ind_cpa_bound_sq` — the left-or-right bound, and its
  form `2 (qℓ)² / |B|`
* `advantage_rfGame_cbcRorAdv_le` — CBC$ over a random function is at advantage at
  most `qℓ(qℓ-1)/2 / |B|` from random ciphertexts
* `run_flag_le_of_step` — a flag probability bound for an adversary from a
  per-query bound on an oracle whose state grows by at most `ℓ` per query

## Proof

`cbcRorAdv A` answers each encryption query by sampling the IV and querying its
oracle at every block-cipher input, so the real game is the real PRP game of `E`
against it (`cbcRealGame_eq`). The PRP game is replaced by the random-function
game at the cost of the switching term (`PRF_q_Advantage_le`). Against a lazy
random function (`repFlagOracle`) and against an oracle answering every query
with a fresh uniform value (`freshFlagOracle`), with a flag set on a repeated
query, the runs agree on every outcome with the flag cleared. The fresh-answer run
is the random-ciphertext game. Its flag is set with probability at most
`qℓ(qℓ-1)/2 / |B|`: every block-cipher input is `s ⊕ m` with `s` a fresh uniform
IV or answer, so it repeats one of the at most `k` earlier inputs with probability
at most `k / |B|`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Constructions.CBCINDCPA

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.PRPPRF
open CatCrypt.Crypto.Constructions.ECBCPRF
open scoped ENNReal

/-! ## Probability helpers -/

section Helpers

theorem toOuterMeasure_le_one {α : Type} (p : PMF α) (S : Set α) : p.toOuterMeasure S ≤ 1 :=
  (MeasureTheory.measure_mono (Set.subset_univ _)).trans_eq
    ((PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr (Set.subset_univ _))

/-- The flag probability of a distribution on flagged outcomes as a sum. -/
theorem toOuterMeasure_flag_eq_tsum {α σ : Type} (p : PMF (α × (σ × Bool))) :
    p.toOuterMeasure {x | x.2.2 = true} = ∑' x, p x * (if x.2.2 = true then 1 else 0) := by
  rw [PMF.toOuterMeasure_apply]
  refine tsum_congr fun x => ?_
  by_cases h : x.2.2 = true
  · simp [h]
  · simp [h]

end Helpers

/-! ## Flag probability of a run from per-query bounds -/

section FlagBound

variable {D R σ α : Type}

/-- **Flag probability of a run.** Let `O` be an oracle on flagged states whose
state size `len` grows by at most `ℓ` per query and which, from an unflagged state
of size `L`, sets the flag with probability at most `c L` for a monotone `c`. An
adversary asking at most `n` queries from an unflagged state of size `L` sets the
flag with probability at most `∑ i < n, c (L + i ℓ)`. -/
theorem run_flag_le_of_step (O : σ × Bool → D → PMF (R × (σ × Bool))) (len : σ → ℕ) (ℓ : ℕ)
    (c : ℕ → ℝ≥0∞) (hc : Monotone c)
    (hstep : ∀ t d, (O (t, false) d).toOuterMeasure {x | x.2.2 = true} ≤ c (len t))
    (hlen : ∀ t d, ∀ x ∈ (O (t, false) d).support, len x.2.1 ≤ len t + ℓ)
    (A : OracleAdv D R α) (n : ℕ) (hA : A.IsQueryBound n) (t : σ) :
    (OracleAdv.run O A (t, false)).toOuterMeasure {x | x.2.2 = true} ≤
      ∑ i ∈ Finset.range n, c (len t + i * ℓ) := by
  induction A generalizing n t with
  | ret a => simp [PMF.toOuterMeasure_pure_apply]
  | rand p k ih =>
    rw [OracleAdv.run_rand, PMF.toOuterMeasure_bind_apply]
    calc ∑' b, p b * (OracleAdv.run O (k b) (t, false)).toOuterMeasure _
        ≤ ∑' b, p b * ∑ i ∈ Finset.range n, c (len t + i * ℓ) :=
          ENNReal.tsum_le_tsum fun b => by gcongr; exact ih b n (hA b) t
      _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  | query d k ih =>
    cases n with
    | zero => exact hA.elim
    | succ n =>
    set T : ℝ≥0∞ := ∑ i ∈ Finset.range n, c (len t + (i + 1) * ℓ)
    rw [OracleAdv.run_query, PMF.toOuterMeasure_bind_apply]
    have hterm : ∀ x : R × (σ × Bool), O (t, false) d x *
        (OracleAdv.run O (k x.1) x.2).toOuterMeasure {x | x.2.2 = true} ≤
        O (t, false) d x * ((if x.2.2 = true then 1 else 0) + T) := by
      intro x
      by_cases hx : x ∈ (O (t, false) d).support
      · gcongr
        obtain ⟨r, t', fl⟩ := x
        cases fl with
        | true => exact (toOuterMeasure_le_one _ _).trans (by simp)
        | false =>
          simp only [Bool.false_eq_true, ite_false, zero_add]
          refine (ih r n (hA r) t').trans (Finset.sum_le_sum fun i _ => hc ?_)
          have := hlen t d _ hx
          simp only at this
          nlinarith
      · simp_all [zero_mul]
    calc ∑' x, O (t, false) d x *
          (OracleAdv.run O (k x.1) x.2).toOuterMeasure {x | x.2.2 = true}
        ≤ ∑' x, O (t, false) d x * ((if x.2.2 = true then 1 else 0) + T) :=
          ENNReal.tsum_le_tsum hterm
      _ = (O (t, false) d).toOuterMeasure {x | x.2.2 = true} + T := by
          simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul,
            toOuterMeasure_flag_eq_tsum]
      _ ≤ c (len t) + T := by gcongr; exact hstep t d
      _ = ∑ i ∈ Finset.range (n + 1), c (len t + i * ℓ) := by
          rw [Finset.sum_range_succ', zero_mul, add_zero, add_comm]

end FlagBound

/-! ## Oracles flagging a repeated query -/

section RepeatFlag

variable {D R : Type} [DecidableEq D] [Fintype R] [Nonempty R]

/-- The oracle answering every query with a fresh uniform value, without state. -/
noncomputable def freshOracle (_ : Unit) (_ : D) : PMF (R × Unit) :=
  (PMF.uniformFintype R).map fun r => (r, ())

/-- The lazy random function with its table as state and a flag set when a query
is already recorded. -/
noncomputable def repFlagOracle (s : List (D × R) × Bool) (d : D) :
    PMF (R × (List (D × R) × Bool)) :=
  match List.lookup d s.1 with
  | some r => PMF.pure (r, (s.1, true))
  | none => (PMF.uniformFintype R).map fun r => (r, ((d, r) :: s.1, s.2))

/-- The oracle answering every query with a fresh uniform value, recording it in
the table and setting the flag when the query is already recorded. -/
noncomputable def freshFlagOracle (s : List (D × R) × Bool) (d : D) :
    PMF (R × (List (D × R) × Bool)) :=
  (PMF.uniformFintype R).map fun r =>
    (r, ((d, r) :: s.1, s.2 || decide (d ∈ s.1.map Prod.fst)))

/-- `freshFlagOracle` with the table replaced by its list of queries. -/
noncomputable def keysFlagOracle (s : List D × Bool) (d : D) : PMF (R × (List D × Bool)) :=
  (PMF.uniformFintype R).map fun r => (r, (d :: s.1, s.2 || decide (d ∈ s.1)))

omit [Fintype R] [Nonempty R] in
theorem mem_keys_of_lookup_eq_some (t : List (D × R)) (d : D) (r : R)
    (h : List.lookup d t = some r) : d ∈ t.map Prod.fst :=
  List.mem_map.mpr ⟨(d, r), HashThenRF.mem_of_lookup_eq_some t d r h, rfl⟩

omit [Fintype R] [Nonempty R] in
theorem notMem_keys_of_lookup_eq_none (t : List (D × R)) (d : D)
    (h : List.lookup d t = none) : d ∉ t.map Prod.fst := by
  grind

theorem repFlagOracle_map (s : List (D × R) × Bool) (d : D) :
    (repFlagOracle s d).map (Prod.map id Prod.fst) = rfOracle s.1 d := by
  unfold repFlagOracle rfOracle
  cases List.lookup d s.1 with
  | some r => simp [PMF.pure_map]
  | none => simp [PMF.map_comp, Function.comp_def]

theorem freshFlagOracle_map (s : List (D × R) × Bool) (d : D) :
    (freshFlagOracle s d).map (Prod.map id fun _ => ()) = freshOracle () d := by
  simp [freshFlagOracle, freshOracle, PMF.map_comp, Function.comp_def]

theorem freshFlagOracle_map_keys (s : List (D × R) × Bool) (d : D) :
    (freshFlagOracle s d).map (Prod.map id fun s => (s.1.map Prod.fst, s.2)) =
      keysFlagOracle (s.1.map Prod.fst, s.2) d := by
  simp [freshFlagOracle, keysFlagOracle, PMF.map_comp, Function.comp_def]

theorem repFlagOracle_apply_true_false (t : List (D × R)) (d : D) (r : R) (t' : List (D × R)) :
    repFlagOracle (t, true) d (r, (t', false)) = 0 := by
  unfold repFlagOracle
  cases List.lookup d t with
  | some r₀ => simp [PMF.pure_apply]
  | none => simp [PMF.map_apply]

theorem freshFlagOracle_apply_true_false (t : List (D × R)) (d : D) (r : R)
    (t' : List (D × R)) : freshFlagOracle (t, true) d (r, (t', false)) = 0 := by
  simp [freshFlagOracle, PMF.map_apply]

theorem repFlagOracle_apply_false_eq (s : List (D × R) × Bool) (d : D) (r : R)
    (t' : List (D × R)) :
    repFlagOracle s d (r, (t', false)) = freshFlagOracle s d (r, (t', false)) := by
  unfold repFlagOracle freshFlagOracle
  cases hl : List.lookup d s.1 with
  | some r₀ =>
    have hmem := mem_keys_of_lookup_eq_some s.1 d r₀ hl
    simp [PMF.pure_apply, PMF.map_apply, hmem]
  | none =>
    grind

end RepeatFlag

/-! ## CBC$ encryption -/

section BlocksVec

variable {B : Type} {n : ℕ} [Inhabited B]

/-- The first `n` entries of a list of blocks, padded with `default`. -/
def blocksVec (cs : List B) : Fin n → B := fun i => cs.getD i default

/-- The vector of the list of a vector of blocks is that vector. -/
theorem blocksVec_ofFn (c : Fin n → B) : blocksVec (List.ofFn c) = c := by
  funext i
  simp [blocksVec]

end BlocksVec

section CBC

variable {B : Type} [CryptoWord B]

/-- The CBC blocks of `M` under `f` from the chaining value `s`: `cᵢ = f (cᵢ₋₁ ⊕ mᵢ)`
with `c₀ = s`, returning `c₁ … cₙ`. -/
def cbcBlocks (f : B → B) : B → List B → List B
  | _, [] => []
  | s, m :: ms => f (CryptoWord.wxor s m) :: cbcBlocks f (f (CryptoWord.wxor s m)) ms

/-- CBC$ encryption of `M` under `f`: a uniform IV `s` with the CBC blocks of `M`
from `s`. -/
noncomputable def cbcEncrypt (f : B → B) (M : List B) : PMF (B × List B) :=
  (PMF.uniformFintype B).map fun s => (s, cbcBlocks f s M)

/-- A uniform list of `n` blocks. -/
noncomputable def randBlocks : ℕ → PMF (List B)
  | 0 => PMF.pure []
  | n + 1 => (PMF.uniformFintype B).bind fun r => (randBlocks n).map (r :: ·)

/-- A uniform IV with `n` uniform blocks. -/
noncomputable def randCiphertext (n : ℕ) : PMF (B × List B) :=
  (PMF.uniformFintype B).bind fun s => (randBlocks n).map (s, ·)

/-- The CBC encryption of the `n` blocks `m` under `f` from the IV `iv`. -/
def cbcVec {n : ℕ} (f : B → B) (iv : B) (m : Fin n → B) : Fin n → B :=
  blocksVec (cbcBlocks f iv (List.ofFn m))

/-- A uniform list of `m` blocks is the list of a uniform vector of `m` blocks. -/
theorem randBlocks_eq_map_ofFn (m : ℕ) :
    randBlocks (B := B) m = (PMF.uniformFintype (Fin m → B)).map List.ofFn := by
  induction m with
  | zero =>
    have h : (List.ofFn : (Fin 0 → B) → List B) = Function.const _ [] :=
      funext fun _ => List.ofFn_zero
    rw [randBlocks, h, PMF.map_const]
  | succ m ih =>
    rw [randBlocks, ← PMF.uniformFintype_map_equiv (Fin.consEquiv fun _ : Fin (m + 1) => B),
      PMF.uniform_prod_eq_bind, PMF.map_comp, PMF.map_bind]
    refine congrArg _ (funext fun r => ?_)
    rw [ih, PMF.map_comp, PMF.map_comp]
    congr 1
    funext f
    simp [Fin.consEquiv, List.ofFn_succ]

/-! ### Games -/

variable {K : Type} [Fintype K] [Nonempty K] {ℓ : ℕ}

/-- The CBC$ encryption oracle under `E k` on messages of at most `ℓ` blocks. -/
noncomputable def encOracle (E : K → B → B) (k : K) (_ : Unit) (M : Msg B ℓ) :
    PMF ((B × List B) × Unit) :=
  (cbcEncrypt (E k) M.1).map fun c => (c, ())

/-- The oracle answering a message with a uniform IV and as many uniform blocks. -/
noncomputable def randOracle (_ : Unit) (M : Msg B ℓ) : PMF ((B × List B) × Unit) :=
  (randCiphertext M.1.length).map fun c => (c, ())

/-- Real-or-random real game: sample a key, then run `A` against the CBC$
encryption oracle. -/
noncomputable def cbcRealGame (E : K → B → B) (A : OracleAdv (Msg B ℓ) (B × List B) Bool) :
    SPComp Bool :=
  liftPMF ((PMF.uniformFintype K).bind fun k =>
    (OracleAdv.run (encOracle E k) A ()).map Prod.fst)

/-- Real-or-random random game: run `A` against uniform ciphertexts. -/
noncomputable def cbcRandGame (A : OracleAdv (Msg B ℓ) (B × List B) Bool) : SPComp Bool :=
  liftPMF ((OracleAdv.run randOracle A ()).map Prod.fst)

/-- Real-or-random IND-CPA advantage of `A` against CBC$ over `E`. -/
noncomputable def CBC_ROR_Advantage (E : K → B → B) (A : OracleAdv (Msg B ℓ) (B × List B) Bool) :
    ℝ≥0∞ :=
  Advantage (cbcRealGame E A) (cbcRandGame A)

/-- Pairs of messages of at most `ℓ` blocks with the same number of blocks. -/
abbrev MsgPair (B : Type) (ℓ : ℕ) : Type :=
  {p : Msg B ℓ × Msg B ℓ // p.1.1.length = p.2.1.length}

/-- The left message of a pair for `b = false`, the right one for `b = true`. -/
def select (b : Bool) (p : MsgPair B ℓ) : Msg B ℓ := if b then p.1.2 else p.1.1

omit [CryptoWord B] in
theorem length_select (b : Bool) (p : MsgPair B ℓ) : (select b p).1.length = p.1.1.1.length := by
  cases b
  · rfl
  · exact p.2.symm

/-- Left-or-right game with bit `b`: sample a key, then answer each pair of
messages with the CBC$ encryption of the message selected by `b`. -/
noncomputable def cbcLRGame (E : K → B → B) (b : Bool)
    (A : OracleAdv (MsgPair B ℓ) (B × List B) Bool) : SPComp Bool :=
  liftPMF ((PMF.uniformFintype K).bind fun k =>
    (OracleAdv.run (fun s p => encOracle E k s (select b p)) A ()).map Prod.fst)

/-- Left-or-right IND-CPA advantage of `A` against CBC$ over `E`. -/
noncomputable def CBC_IND_CPA_Advantage (E : K → B → B)
    (A : OracleAdv (MsgPair B ℓ) (B × List B) Bool) : ℝ≥0∞ :=
  Advantage (cbcLRGame E false A) (cbcLRGame E true A)

/-! ### Reductions -/

/-- The adversary computing `g` of the CBC blocks of `ms` from `s` by querying its
oracle at each block-cipher input. -/
def cbcBlocksAdv {X : Type} (g : List B → X) : B → List B → OracleAdv B B X
  | _, [] => .ret (g [])
  | s, m :: ms => .query (CryptoWord.wxor s m) fun r => cbcBlocksAdv (fun cs => g (r :: cs)) r ms

/-- One CBC$ encryption of `M` with oracle queries for the block function: sample
the IV, then query the oracle at each block-cipher input. -/
noncomputable def cbcEncAdv (M : Msg B ℓ) : OracleAdv B B (B × List B) :=
  .rand (PMF.uniformFintype B) fun s => cbcBlocksAdv (fun cs => (s, cs)) s M.1

/-- Reduction from real-or-random CBC$ to the PRP games of the block function:
answer each encryption query with `cbcEncAdv`. -/
noncomputable def cbcRorAdv (A : OracleAdv (Msg B ℓ) (B × List B) Bool) : OracleAdv B B Bool :=
  OracleAdv.subst cbcEncAdv A

/-- Reduction from left-or-right CBC$ with bit `b` to the PRP games of the block
function. -/
noncomputable def cbcLorAdv (b : Bool) (A : OracleAdv (MsgPair B ℓ) (B × List B) Bool) :
    OracleAdv B B Bool :=
  cbcRorAdv (OracleAdv.mapQuery (select b) A)

theorem isQueryBound_cbcBlocksAdv {X : Type} (g : List B → X) (s : B) (ms : List B) :
    (cbcBlocksAdv g s ms).IsQueryBound ms.length := by
  induction ms generalizing s g with
  | nil => trivial
  | cons m ms ih => exact fun r => ih _ r

theorem isQueryBound_cbcEncAdv (M : Msg B ℓ) : (cbcEncAdv M).IsQueryBound ℓ :=
  fun s => (isQueryBound_cbcBlocksAdv _ s M.1).mono M.2

theorem isQueryBound_cbcRorAdv {A : OracleAdv (Msg B ℓ) (B × List B) Bool} {q : ℕ}
    (hA : A.IsQueryBound q) : (cbcRorAdv A).IsQueryBound (q * ℓ) := by
  unfold CatCrypt.Crypto.Constructions.CBCINDCPA.cbcRorAdv
  simp_all [OracleAdv.isQueryBound_subst, isQueryBound_cbcEncAdv]

theorem isQueryBound_cbcLorAdv (b : Bool) {A : OracleAdv (MsgPair B ℓ) (B × List B) Bool}
    {q : ℕ} (hA : A.IsQueryBound q) : (cbcLorAdv b A).IsQueryBound (q * ℓ) := by
  unfold CatCrypt.Crypto.Constructions.CBCINDCPA.cbcLorAdv
  simp_all [isQueryBound_cbcRorAdv, OracleAdv.isQueryBound_mapQuery]

omit [Fintype K] [Nonempty K] in
theorem run_keyed_cbcBlocksAdv {X : Type} (F : K → B → B) (k : K) (g : List B → X) (s : B)
    (ms : List B) (u : Unit) :
    OracleAdv.run (keyedOracle F k) (cbcBlocksAdv g s ms) u =
      PMF.pure (g (cbcBlocks (F k) s ms), ()) := by
  induction ms generalizing s g with
  | nil => rfl
  | cons m ms ih =>
    simp only [cbcBlocksAdv, OracleAdv.run_query, keyedOracle, PMF.pure_bind, ih]
    rfl

theorem run_fresh_cbcBlocksAdv {X : Type} (g : List B → X) (s : B) (ms : List B) :
    OracleAdv.run freshOracle (cbcBlocksAdv g s ms) () =
      (randBlocks ms.length).map fun cs => (g cs, ()) := by
  induction ms generalizing s g with
  | nil => simp [cbcBlocksAdv, randBlocks, PMF.pure_map]
  | cons m ms ih =>
    simp only [cbcBlocksAdv, OracleAdv.run_query, freshOracle, PMF.bind_map, Function.comp_def,
      ih, randBlocks, List.length_cons, PMF.map_bind, PMF.map_comp]

/-- The real game of CBC$ is the real PRP game of `E` against `cbcRorAdv A`. -/
theorem cbcRealGame_eq (E : K → B → B) (A : OracleAdv (Msg B ℓ) (B × List B) Bool) :
    cbcRealGame E A = realGame E (cbcRorAdv A) := by
  unfold cbcRealGame realGame cbcRorAdv
  congr 1
  refine congrArg _ (funext fun k => ?_)
  rw [OracleAdv.run_subst]
  congr 2
  funext u M
  simp only [cbcEncAdv, OracleAdv.run_rand, run_keyed_cbcBlocksAdv, encOracle, cbcEncrypt,
    PMF.map_comp, Function.comp_def]
  rw [← PMF.bind_pure_comp]
  rfl

/-- The random game of CBC$ is the run of `cbcRorAdv A` against fresh answers. -/
theorem run_randOracle_eq (A : OracleAdv (Msg B ℓ) (B × List B) Bool) :
    OracleAdv.run randOracle A () = OracleAdv.run freshOracle (cbcRorAdv A) () := by
  unfold cbcRorAdv
  rw [OracleAdv.run_subst]
  congr 1
  funext u M
  cases u
  simp only [cbcEncAdv, OracleAdv.run_rand, run_fresh_cbcBlocksAdv, randOracle, randCiphertext,
    PMF.map_bind, PMF.map_comp, Function.comp_def]

/-! ### The flag probability of CBC$ against fresh answers -/

theorem run_keysFlag_flag_le_indicator {X : Type} (A : OracleAdv B B X) (ks : List B) (b : Bool) :
    (OracleAdv.run keysFlagOracle A (ks, b)).toOuterMeasure {x | x.2.2 = true} ≤
      (if b = true then 1 else 0) +
        (OracleAdv.run keysFlagOracle A (ks, false)).toOuterMeasure {x | x.2.2 = true} := by
  cases b
  · simp
  · exact (toOuterMeasure_le_one _ _).trans (by simp)

/-- A uniform `s` has `s ⊕ m` in `ks` with probability at most `|ks| / |B|`. -/
theorem uniform_wxor_mem_le (m : B) (ks : List B) :
    (PMF.uniformFintype B).toOuterMeasure {s | CryptoWord.wxor s m ∈ ks} ≤
      (ks.length : ℝ≥0∞) / Fintype.card B := by
  classical
  rw [PMF.toOuterMeasure_uniformFintype_apply]
  gcongr
  rw [Fintype.card_subtype]
  refine le_trans (Finset.card_le_card (t := ks.toFinset.image fun y => CryptoWord.wxor y m)
    fun s hs => ?_) (Finset.card_image_le.trans (List.toFinset_card_le _))
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hs
  exact Finset.mem_image.mpr ⟨_, List.mem_toFinset.mpr hs, CryptoWord.wxor_cancel s m⟩

/-- For a uniform start `s`, the CBC block queries of `ms` against fresh answers set
the flag from an unflagged state with queries `ks` with probability at most
`∑ i < |ms|, (|ks| + i) / |B|`. -/
theorem uniform_run_keysFlag_cbcBlocksAdv_le {X : Type} (ms : List B) :
    ∀ (g : B → List B → X) (ks : List B),
      ∑' s, PMF.uniformFintype B s *
          (OracleAdv.run keysFlagOracle (cbcBlocksAdv (g s) s ms) (ks, false)).toOuterMeasure
            {x | x.2.2 = true} ≤
        ((∑ i ∈ Finset.range ms.length, (ks.length + i) : ℕ) : ℝ≥0∞) / Fintype.card B := by
  induction ms with
  | nil => intro g ks; simp [cbcBlocksAdv, PMF.toOuterMeasure_pure_apply]
  | cons m ms ih =>
    intro g ks
    set T : ℝ≥0∞ := ((∑ i ∈ Finset.range ms.length, (ks.length + 1 + i) : ℕ) : ℝ≥0∞) /
      Fintype.card B
    have hstep : ∀ s, (OracleAdv.run keysFlagOracle (cbcBlocksAdv (g s) s (m :: ms))
        (ks, false)).toOuterMeasure {x | x.2.2 = true} ≤
        (if CryptoWord.wxor s m ∈ ks then 1 else 0) + T := by
      intro s
      simp only [cbcBlocksAdv, OracleAdv.run_query, keysFlagOracle, PMF.bind_map,
        Function.comp_def, Bool.false_or]
      rw [PMF.toOuterMeasure_bind_apply]
      calc ∑' r, PMF.uniformFintype B r * (OracleAdv.run keysFlagOracle
            (cbcBlocksAdv (fun cs => g s (r :: cs)) r ms)
            (CryptoWord.wxor s m :: ks, decide (CryptoWord.wxor s m ∈ ks))).toOuterMeasure
              {x | x.2.2 = true}
          ≤ ∑' r, PMF.uniformFintype B r * ((if CryptoWord.wxor s m ∈ ks then 1 else 0) +
            (OracleAdv.run keysFlagOracle (cbcBlocksAdv (fun cs => g s (r :: cs)) r ms)
              (CryptoWord.wxor s m :: ks, false)).toOuterMeasure {x | x.2.2 = true}) := by
            refine ENNReal.tsum_le_tsum fun r => ?_
            gcongr
            refine (run_keysFlag_flag_le_indicator _ _ _).trans_eq ?_
            simp
        _ = (if CryptoWord.wxor s m ∈ ks then 1 else 0) +
            ∑' r, PMF.uniformFintype B r * (OracleAdv.run keysFlagOracle
              (cbcBlocksAdv (fun cs => g s (r :: cs)) r ms)
              (CryptoWord.wxor s m :: ks, false)).toOuterMeasure {x | x.2.2 = true} := by
            simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
        _ ≤ (if CryptoWord.wxor s m ∈ ks then 1 else 0) + T := by
            gcongr
            have h := ih (fun r cs => g s (r :: cs)) (CryptoWord.wxor s m :: ks)
            grind [List.length_cons]
    calc ∑' s, PMF.uniformFintype B s * (OracleAdv.run keysFlagOracle
          (cbcBlocksAdv (g s) s (m :: ms)) (ks, false)).toOuterMeasure {x | x.2.2 = true}
        ≤ ∑' s, PMF.uniformFintype B s * ((if CryptoWord.wxor s m ∈ ks then 1 else 0) + T) :=
          ENNReal.tsum_le_tsum fun s => by gcongr; exact hstep s
      _ = (PMF.uniformFintype B).toOuterMeasure {s | CryptoWord.wxor s m ∈ ks} + T := by
          simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul,
            PMF.toOuterMeasure_apply]
          congr 1
          refine tsum_congr fun s => ?_
          by_cases h : CryptoWord.wxor s m ∈ ks
          · simp [h]
          · simp [h]
      _ ≤ (ks.length : ℝ≥0∞) / Fintype.card B + T := by gcongr; exact uniform_wxor_mem_le m ks
      _ = _ := by
          rw [ENNReal.div_add_div_same, List.length_cons, Finset.sum_range_succ']
          congr 1
          push_cast
          rw [add_zero, add_comm]
          congr 1
          grind [Finset.sum_congr]

theorem length_run_keysFlag_cbcBlocksAdv {X : Type} (g : List B → X) (s : B)
    (ms ks : List B) (fl : Bool) :
    ∀ x ∈ (OracleAdv.run keysFlagOracle (cbcBlocksAdv g s ms) (ks, fl)).support,
      x.2.1.length = ks.length + ms.length := by
  induction ms generalizing s g ks fl with
  | nil =>
    intro x hx
    simp only [cbcBlocksAdv, OracleAdv.run_ret, PMF.support_pure, Set.mem_singleton_iff] at hx
    subst hx
    simp
  | cons m ms ih =>
    intro x hx
    simp only [cbcBlocksAdv, OracleAdv.run_query, keysFlagOracle, PMF.bind_map, Function.comp_def,
      PMF.mem_support_bind_iff] at hx
    obtain ⟨r, -, hr⟩ := hx
    rw [ih _ _ _ _ x hr]
    simp only [List.length_cons]
    omega

theorem length_run_keysFlag_cbcEncAdv (M : Msg B ℓ) (ks : List B) :
    ∀ x ∈ (OracleAdv.run keysFlagOracle (cbcEncAdv M) (ks, false)).support,
      x.2.1.length ≤ ks.length + ℓ := by
  intro x hx
  simp only [cbcEncAdv, OracleAdv.run_rand, PMF.mem_support_bind_iff] at hx
  obtain ⟨s, -, hs⟩ := hx
  rw [length_run_keysFlag_cbcBlocksAdv _ _ _ _ _ x hs]
  exact Nat.add_le_add_left M.2 _

/-- One CBC$ encryption query against fresh answers sets the flag from an
unflagged state with queries `ks` with probability at most
`∑ i < ℓ, (|ks| + i) / |B|`. -/
theorem run_keysFlag_cbcEncAdv_flag_le (M : Msg B ℓ) (ks : List B) :
    (OracleAdv.run keysFlagOracle (cbcEncAdv M) (ks, false)).toOuterMeasure {x | x.2.2 = true} ≤
      ((∑ i ∈ Finset.range ℓ, (ks.length + i) : ℕ) : ℝ≥0∞) / Fintype.card B := by
  rw [cbcEncAdv, OracleAdv.run_rand, PMF.toOuterMeasure_bind_apply]
  refine (uniform_run_keysFlag_cbcBlocksAdv_le M.1 (fun s cs => (s, cs)) ks).trans ?_
  gcongr
  exact M.2

omit [CryptoWord B] in
theorem sum_range_sum_range_mul (q ℓ : ℕ) :
    ∑ i ∈ Finset.range q, ∑ j ∈ Finset.range ℓ, (i * ℓ + j) = ∑ k ∈ Finset.range (q * ℓ), k := by
  induction q with
  | zero => simp
  | succ q ih => rw [Finset.sum_range_succ, ih, add_one_mul, Finset.sum_range_add]

/-- **Random function to random ciphertexts.** For an adversary asking at most `q`
queries of at most `ℓ` blocks, CBC$ over the lazy random function is at advantage
at most `qℓ(qℓ-1)/2 / |B|` from uniform ciphertexts. -/
theorem advantage_rfGame_cbcRorAdv_le (A : OracleAdv (Msg B ℓ) (B × List B) Bool) (q : ℕ)
    (hA : A.IsQueryBound q) :
    Advantage (rfGame (cbcRorAdv A)) (cbcRandGame A) ≤
      ((q * ℓ * (q * ℓ - 1) / 2 : ℕ) : ℝ≥0∞) / Fintype.card B := by
  set p₁ := OracleAdv.run repFlagOracle (cbcRorAdv A) ([], false)
  set p₂ := OracleAdv.run freshFlagOracle (cbcRorAdv A) ([], false)
  have hagree : ∀ a t, p₁ (a, (t, false)) = p₂ (a, (t, false)) := fun a t =>
    OracleAdv.run_apply_flag_false_eq _ _ repFlagOracle_apply_true_false
      freshFlagOracle_apply_true_false repFlagOracle_apply_false_eq _ _ a t
  have hreal : prTrue (rfGame (cbcRorAdv A)) Heap.empty =
      p₁.toOuterMeasure {x | x.1 ∈ ({true} : Set Bool)} := by
    unfold rfGame
    rw [← OracleAdv.run_map_state repFlagOracle rfOracle Prod.fst repFlagOracle_map _ ([], false),
      PMF.map_comp, prTrue_liftPMF_map]
    rfl
  have hideal : prTrue (cbcRandGame A) Heap.empty =
      p₂.toOuterMeasure {x | x.1 ∈ ({true} : Set Bool)} := by
    unfold cbcRandGame
    rw [run_randOracle_eq, ← OracleAdv.run_map_state freshFlagOracle freshOracle (fun _ => ())
      freshFlagOracle_map _ ([], false), PMF.map_comp, prTrue_liftPMF_map]
    rfl
  have hflag : p₂.toOuterMeasure {x | x.2.2 = true} ≤
      ((q * ℓ * (q * ℓ - 1) / 2 : ℕ) : ℝ≥0∞) / Fintype.card B := by
    have hmap := OracleAdv.run_map_state freshFlagOracle keysFlagOracle
      (fun s : List (B × B) × Bool => (s.1.map Prod.fst, s.2)) freshFlagOracle_map_keys
      (cbcRorAdv A) ([], false)
    have h1 : p₂.toOuterMeasure {x | x.2.2 = true} =
        (OracleAdv.run keysFlagOracle (cbcRorAdv A) ([], false)).toOuterMeasure
          {x | x.2.2 = true} := by
      rw [← List.map_nil (f := (Prod.fst : B × B → B)), ← hmap, PMF.toOuterMeasure_map_apply]
      rfl
    rw [h1, cbcRorAdv, OracleAdv.run_subst]
    have hmono : Monotone fun L : ℕ =>
        ((∑ i ∈ Finset.range ℓ, (L + i) : ℕ) : ℝ≥0∞) / Fintype.card B := by
      intro a b hab
      simp only
      gcongr
    refine (run_flag_le_of_step _ List.length ℓ _ hmono
      (fun t M => run_keysFlag_cbcEncAdv_flag_le M t) (fun t M => length_run_keysFlag_cbcEncAdv M t)
      A q hA []).trans_eq ?_
    simp only [List.length_nil, zero_add, ENNReal.div_eq_inv_mul, ← Finset.mul_sum, ← Nat.cast_sum]
    rw [sum_range_sum_range_mul, CatCrypt.Prob.BirthdayBound.gauss_sum_nat]
  simp only [Advantage, hreal, hideal]
  refine max_le (tsub_le_iff_left.mpr ?_) (tsub_le_iff_left.mpr ?_)
  · calc p₁.toOuterMeasure {x | x.1 ∈ ({true} : Set Bool)}
        ≤ p₂.toOuterMeasure {x | x.1 ∈ ({true} : Set Bool)} +
            p₂.toOuterMeasure {x | x.2.2 = true} :=
          toOuterMeasure_le_add_flag p₁ p₂ hagree _
      _ ≤ _ := add_le_add le_rfl hflag
  · calc p₂.toOuterMeasure {x | x.1 ∈ ({true} : Set Bool)}
        ≤ p₁.toOuterMeasure {x | x.1 ∈ ({true} : Set Bool)} +
            p₁.toOuterMeasure {x | x.2.2 = true} :=
          toOuterMeasure_le_add_flag p₂ p₁ (fun a t => (hagree a t).symm) _
      _ = p₁.toOuterMeasure {x | x.1 ∈ ({true} : Set Bool)} +
          p₂.toOuterMeasure {x | x.2.2 = true} := by
          rw [toOuterMeasure_flag_eq p₁ p₂ hagree]
      _ ≤ _ := add_le_add le_rfl hflag

/-! ### The bounds -/

/-- **CBC$ is real-or-random IND-CPA secure.** For a keyed block function `E` and an
adversary asking at most `q` encryption queries of at most `ℓ` blocks, the
real-or-random advantage is at most the PRP advantage of `E` against
`cbcRorAdv A`, which asks at most `qℓ` queries, plus `qℓ(qℓ-1) / |B|`: the PRP/PRF
switching term and the repeated-input term, each `qℓ(qℓ-1)/2 / |B|`. -/
theorem cbc_ror_bound (E : K → B → B) (A : OracleAdv (Msg B ℓ) (B × List B) Bool) (q : ℕ)
    (hA : A.IsQueryBound q) :
    CBC_ROR_Advantage E A ≤
      PRP_q_Advantage E (cbcRorAdv A) + ((q * ℓ * (q * ℓ - 1) : ℕ) : ℝ≥0∞) / Fintype.card B := by
  have h₁ := PRF_q_Advantage_le E (cbcRorAdv A) (q * ℓ) (isQueryBound_cbcRorAdv hA)
  have h₂ := advantage_rfGame_cbcRorAdv_le A q hA
  unfold PRF_q_Advantage at h₁
  unfold CBC_ROR_Advantage
  rw [cbcRealGame_eq]
  refine (advantage_triangle _ (rfGame (cbcRorAdv A)) _).trans ((add_le_add h₁ h₂).trans_eq ?_)
  rw [add_assoc, ENNReal.div_add_div_same, ← Nat.cast_add, ← two_mul,
    Nat.two_mul_div_two_of_even (Nat.even_mul_pred_self _)]

theorem cbcLRGame_eq (E : K → B → B) (b : Bool) (A : OracleAdv (MsgPair B ℓ) (B × List B) Bool) :
    cbcLRGame E b A = cbcRealGame E (OracleAdv.mapQuery (select b) A) := by
  unfold cbcLRGame cbcRealGame
  simp only [OracleAdv.run_mapQuery]

theorem cbcRandGame_mapQuery_select (b : Bool) (A : OracleAdv (MsgPair B ℓ) (B × List B) Bool) :
    cbcRandGame (OracleAdv.mapQuery (select b) A) =
      cbcRandGame (OracleAdv.mapQuery (select false) A) := by
  unfold cbcRandGame
  simp only [OracleAdv.run_mapQuery]
  congr 3
  funext u p
  simp_all [randOracle, length_select]

/-- **CBC$ is left-or-right IND-CPA secure** (Bellare–Desai–Jokipii–Rogaway). For a
keyed block function `E` and an adversary asking at most `q` queries, each a pair
of messages of at most `ℓ` blocks with the same number of blocks, the
left-or-right advantage is at most the PRP advantages of `E` against
`cbcLorAdv false A` and `cbcLorAdv true A`, each asking at most `qℓ` queries, plus
`2 qℓ(qℓ-1) / |B|`. -/
theorem cbc_ind_cpa_bound (E : K → B → B) (A : OracleAdv (MsgPair B ℓ) (B × List B) Bool)
    (q : ℕ) (hA : A.IsQueryBound q) :
    CBC_IND_CPA_Advantage E A ≤
      PRP_q_Advantage E (cbcLorAdv false A) + PRP_q_Advantage E (cbcLorAdv true A) +
        ((2 * (q * ℓ * (q * ℓ - 1)) : ℕ) : ℝ≥0∞) / Fintype.card B := by
  have h₀ := cbc_ror_bound E (OracleAdv.mapQuery (select false) A) q
    (OracleAdv.isQueryBound_mapQuery _ hA)
  have h₁ := cbc_ror_bound E (OracleAdv.mapQuery (select true) A) q
    (OracleAdv.isQueryBound_mapQuery _ hA)
  unfold CBC_ROR_Advantage at h₀ h₁
  rw [cbcRandGame_mapQuery_select true, Advantage_sym] at h₁
  unfold CBC_IND_CPA_Advantage
  rw [cbcLRGame_eq, cbcLRGame_eq]
  refine (advantage_triangle _ (cbcRandGame (OracleAdv.mapQuery (select false) A)) _).trans
    ((add_le_add h₀ h₁).trans_eq ?_)
  simp only [cbcLorAdv, Nat.cast_mul, Nat.cast_ofNat, mul_div_assoc]
  ring

/-- `cbc_ind_cpa_bound` with the collision term bounded by `2 (qℓ)² / |B|`. -/
theorem cbc_ind_cpa_bound_sq (E : K → B → B) (A : OracleAdv (MsgPair B ℓ) (B × List B) Bool)
    (q : ℕ) (hA : A.IsQueryBound q) :
    CBC_IND_CPA_Advantage E A ≤
      PRP_q_Advantage E (cbcLorAdv false A) + PRP_q_Advantage E (cbcLorAdv true A) +
        ((2 * (q * ℓ) ^ 2 : ℕ) : ℝ≥0∞) / Fintype.card B := by
  refine (cbc_ind_cpa_bound E A q hA).trans ?_
  gcongr
  rw [sq]
  gcongr_unfold

end CBC

end CatCrypt.Crypto.Constructions.CBCINDCPA
