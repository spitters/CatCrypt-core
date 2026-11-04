/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Constructions.NMACPRF
public import Mathlib.Data.Fintype.Vector
public import CatCryptCore.ForMathlib.PMFUniform

/-!
# HKDF Extract and Expand are multi-query PRFs

HKDF (Krawczyk, *Cryptographic Extraction and Key Derivation: The HKDF Scheme*,
CRYPTO 2010; RFC 5869) derives key material with HMAC in two stages.

* `hkdfExtract` is HMAC keyed by the salt and applied to the input keying material.
  As a PRF keyed by the salt its multi-query advantage is the HMAC advantage
  (`hkdfExtract_prf_bound`).
* `expand H msg n prk info` is the feedback chain `T(i) = H prk (msg T(i-1) info i)`
  for `i = 1, …, n`, with `T(0)` absent, for any keyed function `H`; `msg` encodes
  the previous block, the context `info` and the counter `i` into an input of `H`,
  and is injective in `(info, i)`. Its multi-query PRF advantage, with outputs in
  `List.Vector K n`, equals the PRF advantage of `H` against `expandAdv msg n A`,
  which answers each query `info` of `A` with `n` chained queries
  (`expand_prf_eq`). `hkdfExpand` instantiates `H` with HMAC keyed by the pseudorandom
  key (`hkdfExpand_prf_bound`).

## Main definitions

* `expand`, `expandQ`, `expandAdv`
* `hkdfSalted X H msg n ikm` — Extract-then-Expand keyed by the salt with fixed
  input keying material; `extractAdv` — its one-query extraction reduction
* `hkdfExtract`, `hkdfExpand`

## Main results

* `expand_prf_eq` — `PRF_q_Advantage (expand H msg n) A = PRF_q_Advantage H (expandAdv msg n A)`
* `isQueryBound_expandAdv` — `expandAdv msg n A` asks at most `q n` queries
* `hkdfSalted_prf_bound` — Extract-then-Expand: the extraction advantage of
  `extractAdv` plus the expansion advantage of `expandAdv`
* `hkdfExtract_prf_bound`, `hkdfExpand_prf_bound`, `hkdf_prf_bound` — the bounds
  for HMAC-based HKDF in terms of the compression function

## Proof

The real games agree because the chained queries against the keyed oracle compute
the chain. For the ideal games, a lazy random function on contexts with vector
answers is mapped to a lazy random function on inputs of `H` by replacing each
recorded `(info, v)` with the `n` chain inputs and answers (`tab`). Injectivity of
`msg` in `(info, i)` makes a recorded context answer every chain input from its
recorded vector (`known_tab_of_lookup`), and a fresh context leaves every chain
input fresh, so its `n` answers are independent and uniform
(`run_expandQ_fresh`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Constructions.HKDFPRF

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.PRPPRF
open CatCrypt.Crypto.Constructions.ECBCPRF CatCrypt.Crypto.Constructions.NMACPRF
open scoped ENNReal

/-! ## The expansion chain -/

section Expand

variable {K D I Kp : Type}

/-- The chain `T(i), …, T(i+m-1)` of `F` from the previous block `prev`. -/
def expandVec (F : D → K) (msg : Option K → I → ℕ → D) (info : I) :
    (m i : ℕ) → Option K → List.Vector K m
  | 0, _, _ => List.Vector.nil
  | m + 1, i, prev =>
    F (msg prev info i) ::ᵥ expandVec F msg info m (i + 1) (some (F (msg prev info i)))

/-- The expansion of `info` under the key `prk`: `n` chained blocks from counter `1`. -/
def expand (H : Kp → D → K) (msg : Option K → I → ℕ → D) (n : ℕ) (prk : Kp) (info : I) :
    List.Vector K n :=
  expandVec (H prk) msg info n 1 none

/-- The chain of `m` blocks computed with oracle queries. -/
def expandQ (msg : Option K → I → ℕ → D) (info : I) :
    (m i : ℕ) → Option K → OracleAdv D K (List.Vector K m)
  | 0, _, _ => .ret List.Vector.nil
  | m + 1, i, prev => .query (msg prev info i) fun t =>
      OracleAdv.bind (expandQ msg info m (i + 1) (some t)) fun v => .ret (t ::ᵥ v)

/-- Reduction from the expansion to its keyed function: run `A` once and answer
each query `info` with the chain of `n` oracle queries. -/
def expandAdv (msg : Option K → I → ℕ → D) (n : ℕ) (A : OracleAdv I (List.Vector K n) Bool) :
    OracleAdv D K Bool :=
  OracleAdv.subst (fun info => expandQ msg info n 1 none) A

theorem isQueryBound_expandQ (msg : Option K → I → ℕ → D) (info : I) (m i : ℕ)
    (prev : Option K) : (expandQ msg info m i prev).IsQueryBound m := by
  induction m generalizing i prev with
  | zero => trivial
  | succ m ih =>
    intro t
    have h := OracleAdv.isQueryBound_bind
      (f := fun v => (OracleAdv.ret (t ::ᵥ v) : OracleAdv D K (List.Vector K (m + 1))))
      (n := 0) (ih (i + 1) (some t)) fun _ => trivial
    simpa using h

theorem isQueryBound_expandAdv (msg : Option K → I → ℕ → D) (n : ℕ)
    {A : OracleAdv I (List.Vector K n) Bool} {q : ℕ} (hA : A.IsQueryBound q) :
    (expandAdv msg n A).IsQueryBound (q * n) :=
  OracleAdv.isQueryBound_subst (fun info => isQueryBound_expandQ msg info n 1 none) hA

theorem run_keyed_expandQ (F : D → K) (msg : Option K → I → ℕ → D) (info : I) (m i : ℕ)
    (prev : Option K) (u : Unit) :
    OracleAdv.run (keyedOracle (fun (F : D → K) d => F d) F) (expandQ msg info m i prev) u =
      PMF.pure (expandVec F msg info m i prev, ()) := by
  induction m generalizing i prev with
  | zero => rfl
  | succ m ih =>
    simp only [expandQ, OracleAdv.run_query, keyedOracle, PMF.pure_bind, OracleAdv.run_bind,
      ih, OracleAdv.run_ret]
    rfl

variable [Fintype K] [Nonempty K] [Fintype Kp] [Nonempty Kp]

omit [Fintype K] [Nonempty K] in
/-- The real game of the expansion is the real game of `H` against `expandAdv`. -/
theorem realGame_expand_eq (H : Kp → D → K) (msg : Option K → I → ℕ → D) (n : ℕ)
    (A : OracleAdv I (List.Vector K n) Bool) :
    realGame (expand H msg n) A = realGame H (expandAdv msg n A) := by
  unfold realGame expandAdv
  congr 1
  refine congrArg _ (funext fun k => ?_)
  rw [OracleAdv.run_subst]
  congr 1
  congr 1
  funext _ info
  exact (run_keyed_expandQ (H k) msg info n 1 none ()).symm

/-! ### The ideal games -/

variable [DecidableEq D] [DecidableEq I]

/-- The inputs and answers of the chain of the vector `v`, most recent first, as
recorded by a lazy random function. -/
def entries (msg : Option K → I → ℕ → D) (info : I) :
    (m i : ℕ) → Option K → List.Vector K m → List (D × K)
  | 0, _, _, _ => []
  | m + 1, i, prev, v =>
    entries msg info m (i + 1) (some v.head) v.tail ++ [(msg prev info i, v.head)]

/-- The table on inputs of `H` corresponding to a table on contexts. -/
def tab (msg : Option K → I → ℕ → D) (n : ℕ) (s : List (I × List.Vector K n)) :
    List (D × K) :=
  s.flatMap fun p => entries msg p.1 n 1 none p.2

/-- The table `T` answers the chain of `v` from counter `i` and previous block
`prev`. -/
def Known (msg : Option K → I → ℕ → D) (info : I) (T : List (D × K)) :
    (m i : ℕ) → Option K → List.Vector K m → Prop
  | 0, _, _, _ => True
  | m + 1, i, prev, v => List.lookup (msg prev info i) T = some v.head ∧
      Known msg info T m (i + 1) (some v.head) v.tail

omit [Fintype Kp] [Nonempty Kp] [DecidableEq I] in
theorem run_expandQ_known (msg : Option K → I → ℕ → D) (info : I) (m i : ℕ)
    (prev : Option K) (v : List.Vector K m) (T : List (D × K))
    (h : Known msg info T m i prev v) :
    OracleAdv.run rfOracle (expandQ msg info m i prev) T = PMF.pure (v, T) := by
  induction m generalizing i prev with
  | zero => simp [expandQ, List.Vector.eq_nil v]
  | succ m ih =>
    obtain ⟨h₁, h₂⟩ := h
    simp only [expandQ, OracleAdv.run_query, rfOracle, h₁, PMF.pure_bind, OracleAdv.run_bind,
      ih (i + 1) (some v.head) v.tail h₂, OracleAdv.run_ret, List.Vector.cons_head_tail]

/-- `msg` determines the context and the counter. -/
def MsgInj (msg : Option K → I → ℕ → D) : Prop :=
  ∀ p p' info info' i i', msg p info i = msg p' info' i' → info = info' ∧ i = i'

omit [Fintype K] [Nonempty K] [Fintype Kp] [Nonempty Kp] [DecidableEq I] in
theorem lookup_entries_ne {msg : Option K → I → ℕ → D} (hinj : MsgInj msg) {info info' : I}
    (m i : ℕ) (prev : Option K) (v : List.Vector K m) (p : Option K) (j : ℕ)
    (h : info ≠ info' ∨ j < i) :
    List.lookup (msg p info j) (entries msg info' m i prev v) = none := by
  induction m generalizing i prev with
  | zero => rfl
  | succ m ih =>
    simp only [entries, List.lookup_append, ih (i + 1) _ _ (h.imp id fun hj => by omega)]
    have hne : msg p info j ≠ msg prev info' i := fun he => by
      obtain ⟨h1, h2⟩ := hinj _ _ _ _ _ _ he
      rcases h with h | h
      · exact h h1
      · omega
    simp [hne]

omit [Fintype K] [Nonempty K] [Fintype Kp] [Nonempty Kp] [DecidableEq I] in
theorem known_entries_append {msg : Option K → I → ℕ → D} (hinj : MsgInj msg) (info : I)
    (m i : ℕ) (prev : Option K) (v : List.Vector K m) (T : List (D × K)) :
    Known msg info (entries msg info m i prev v ++ T) m i prev v := by
  induction m generalizing i prev T with
  | zero => trivial
  | succ m ih =>
    refine ⟨?_, ?_⟩
    · simp only [entries, List.append_assoc, List.lookup_append,
        lookup_entries_ne hinj m (i + 1) _ _ prev i (Or.inr (Nat.lt_succ_self i))]
      simp
    · simpa only [entries, List.append_assoc] using ih (i + 1) (some v.head) v.tail _

omit [Fintype K] [Nonempty K] [Fintype Kp] [Nonempty Kp] [DecidableEq I] in
theorem known_append_of_fresh {msg : Option K → I → ℕ → D} (info : I) (T₀ T : List (D × K))
    (h₀ : ∀ p j, List.lookup (msg p info j) T₀ = none) (m i : ℕ) (prev : Option K)
    (v : List.Vector K m) (h : Known msg info T m i prev v) :
    Known msg info (T₀ ++ T) m i prev v := by
  induction m generalizing i prev with
  | zero => trivial
  | succ m ih =>
    obtain ⟨h₁, h₂⟩ := h
    exact ⟨by rw [List.lookup_append, h₀, h₁]; rfl, ih _ _ v.tail h₂⟩

omit [Fintype K] [Nonempty K] [Fintype Kp] [Nonempty Kp] in
theorem lookup_tab_of_lookup_none {msg : Option K → I → ℕ → D} (hinj : MsgInj msg) {n : ℕ}
    (info : I) (s : List (I × List.Vector K n)) (hs : List.lookup info s = none) (p : Option K)
    (j : ℕ) : List.lookup (msg p info j) (tab msg n s) = none := by
  induction s with
  | nil => rfl
  | cons a s ih =>
    obtain ⟨info', v⟩ := a
    have hne : info ≠ info' := by
      rintro rfl
      simp at hs
    have hb : (info == info') = false := by simpa using hne
    simp only [List.lookup_cons, hb] at hs
    simp only [tab, List.flatMap_cons, List.lookup_append] at ih ⊢
    rw [lookup_entries_ne hinj n 1 none v p j (Or.inl hne), ih hs]
    rfl

omit [Fintype K] [Nonempty K] [Fintype Kp] [Nonempty Kp] in
theorem known_tab_of_lookup {msg : Option K → I → ℕ → D} (hinj : MsgInj msg) {n : ℕ}
    (info : I) (s : List (I × List.Vector K n)) (v : List.Vector K n)
    (hs : List.lookup info s = some v) : Known msg info (tab msg n s) n 1 none v := by
  induction s with
  | nil => simp at hs
  | cons a s ih =>
    obtain ⟨info', v'⟩ := a
    by_cases hne : info = info'
    · subst hne
      simp only [List.lookup_cons_self, Option.some.injEq] at hs
      subst hs
      simpa only [tab, List.flatMap_cons] using known_entries_append hinj info n 1 none v' _
    · have hb : (info == info') = false := by simpa using hne
      simp only [List.lookup_cons, hb] at hs
      simp only [tab, List.flatMap_cons]
      exact known_append_of_fresh info _ _
        (fun p j => lookup_entries_ne hinj n 1 none v' p j (Or.inl hne)) n 1 none v (ih hs)

omit [Fintype Kp] [Nonempty Kp] [DecidableEq I] in
theorem run_expandQ_fresh {msg : Option K → I → ℕ → D} (hinj : MsgInj msg) (info : I)
    (m i : ℕ) (prev : Option K) (T : List (D × K))
    (hT : ∀ p j, i ≤ j → List.lookup (msg p info j) T = none) :
    OracleAdv.run rfOracle (expandQ msg info m i prev) T =
      (PMF.uniformFintype (List.Vector K m)).map
        fun v => (v, entries msg info m i prev v ++ T) := by
  induction m generalizing i prev T with
  | zero =>
    have h : (fun v : List.Vector K 0 => (v, entries msg info 0 i prev v ++ T)) =
        fun _ => (List.Vector.nil, T) :=
      funext fun v => by simp [entries, List.Vector.eq_nil v]
    simp only [expandQ, OracleAdv.run_ret, h]
    exact (PMF.map_const _ _).symm
  | succ m ih =>
    have hl : List.lookup (msg prev info i) T = none := hT prev i le_rfl
    have hT' : ∀ (t : K) p j, i + 1 ≤ j →
        List.lookup (msg p info j) ((msg prev info i, t) :: T) = none := by
      intro t p j hj
      have hne : (msg p info j == msg prev info i) = false := by
        simpa using fun he => by have := (hinj _ _ _ _ _ _ he).2; omega
      simp only [List.lookup_cons, hne]
      exact hT p j (by omega)
    simp only [expandQ, OracleAdv.run_query, rfOracle, hl, PMF.bind_map, Function.comp_def,
      OracleAdv.run_bind, OracleAdv.run_ret, ih (i + 1) _ _ (hT' _), PMF.bind_map]
    rw [PMF.uniformFintype_vector_succ, PMF.map_bind]
    refine congrArg _ (funext fun t => ?_)
    simp only [Function.comp_def, ← PMF.bind_pure_comp]
    simp [entries]

omit [Fintype Kp] [Nonempty Kp] in
theorem rfOracle_map_tab {msg : Option K → I → ℕ → D} (hinj : MsgInj msg) {n : ℕ}
    (s : List (I × List.Vector K n)) (info : I) :
    (rfOracle s info).map (Prod.map id (tab msg n)) =
      OracleAdv.run rfOracle (expandQ msg info n 1 none) (tab msg n s) := by
  cases hs : List.lookup info s with
  | some v =>
    rw [run_expandQ_known msg info n 1 none v _ (known_tab_of_lookup hinj info s v hs)]
    simp [rfOracle, hs, PMF.pure_map]
  | none =>
    rw [run_expandQ_fresh hinj info n 1 none _
      (fun p j _ => lookup_tab_of_lookup_none hinj info s hs p j)]
    simp [rfOracle, hs, PMF.map_comp, Function.comp_def, tab]

omit [Fintype Kp] [Nonempty Kp] in
/-- The ideal game of the expansion reduction is the random-function game on
contexts. -/
theorem rfGame_expandAdv_eq {msg : Option K → I → ℕ → D} (hinj : MsgInj msg) (n : ℕ)
    (A : OracleAdv I (List.Vector K n) Bool) :
    rfGame (expandAdv msg n A) = rfGame A := by
  unfold rfGame expandAdv
  rw [OracleAdv.run_subst]
  have h := OracleAdv.run_map_state rfOracle
    (fun T info => OracleAdv.run rfOracle (expandQ msg info n 1 none) T) (tab msg n)
    (fun s info => rfOracle_map_tab hinj s info) A []
  change _ = OracleAdv.run _ A [] at h
  rw [← h, PMF.map_comp]
  rfl

/-- **The expansion is a PRF with the PRF advantage of its keyed function.** For a
`msg` injective in the context and counter, the multi-query PRF advantage of the
expansion to `n` blocks equals the PRF advantage of `H` against `expandAdv msg n A`,
which runs `A` once and asks `n` queries per query of `A`. -/
theorem expand_prf_eq (H : Kp → D → K) {msg : Option K → I → ℕ → D} (hinj : MsgInj msg)
    (n : ℕ) (A : OracleAdv I (List.Vector K n) Bool) :
    PRF_q_Advantage (expand H msg n) A = PRF_q_Advantage H (expandAdv msg n A) := by
  unfold PRF_q_Advantage
  rw [realGame_expand_eq, rfGame_expandAdv_eq hinj]

end Expand

/-! ## Extract then Expand -/

section ExtractExpand

variable {K D I Kp S M : Type}

/-- HKDF with a fixed input keying material `ikm`, keyed by the salt: the expansion
under the pseudorandom key `X salt ikm`. -/
def hkdfSalted (X : S → M → Kp) (H : Kp → D → K) (msg : Option K → I → ℕ → D) (n : ℕ)
    (ikm : M) (salt : S) (info : I) : List.Vector K n :=
  expand H msg n (X salt ikm) info

/-- Reduction to the extraction step: query `ikm` once and answer every query `info`
of `A` with the expansion under the answer. It runs `A` once and asks one query. -/
def extractAdv (H : Kp → D → K) (msg : Option K → I → ℕ → D) (n : ℕ) (ikm : M)
    (A : OracleAdv I (List.Vector K n) Bool) : OracleAdv M Kp Bool :=
  .query ikm fun prk => OracleAdv.subst (fun info => .ret (expand H msg n prk info)) A

theorem isQueryBound_extractAdv (H : Kp → D → K) (msg : Option K → I → ℕ → D) (n : ℕ)
    (ikm : M) {A : OracleAdv I (List.Vector K n) Bool} {q : ℕ} (hA : A.IsQueryBound q) :
    (extractAdv H msg n ikm A).IsQueryBound 1 := by
  intro prk
  have h := OracleAdv.isQueryBound_subst
    (impl := fun info => (OracleAdv.ret (expand H msg n prk info) :
      OracleAdv M Kp (List.Vector K n))) (c := 0) (fun _ => trivial) hA
  exact h.mono (by simp)

variable [Fintype K] [Nonempty K] [Fintype Kp] [Nonempty Kp] [Fintype S] [Nonempty S]
  [DecidableEq D] [DecidableEq I] [DecidableEq M]

/-- **Extract then Expand is a multi-query PRF.** With the input keying material
fixed and the salt as key, the PRF advantage of HKDF against an adversary asking
adaptive context queries is at most the PRF advantage of the extraction `X`
against the one-query reduction `extractAdv` plus the PRF advantage of `H` against
`expandAdv msg n A` (Krawczyk 2010, §4, with the salt as the extractor key). -/
theorem hkdfSalted_prf_bound (X : S → M → Kp) (H : Kp → D → K)
    {msg : Option K → I → ℕ → D} (hinj : MsgInj msg) (n : ℕ) (ikm : M)
    (A : OracleAdv I (List.Vector K n) Bool) :
    PRF_q_Advantage (hkdfSalted X H msg n ikm) A ≤
      PRF_q_Advantage X (extractAdv H msg n ikm A) +
        PRF_q_Advantage H (expandAdv msg n A) := by
  have hreal : realGame (hkdfSalted X H msg n ikm) A = realGame X (extractAdv H msg n ikm A) := by
    unfold realGame
    congr 1
    refine congrArg _ (funext fun salt => ?_)
    simp only [extractAdv, OracleAdv.run_query, keyedOracle, PMF.pure_bind]
    rw [run_simulate_ret_map_fst]
    rfl
  have hmid : rfGame (extractAdv H msg n ikm A) = realGame (expand H msg n) A := by
    unfold rfGame realGame
    congr 1
    simp only [extractAdv, OracleAdv.run_query, rfOracle, List.lookup_nil, PMF.bind_map,
      Function.comp_def, PMF.map_bind]
    refine congrArg _ (funext fun prk => ?_)
    rw [run_simulate_ret_map_fst]
    rfl
  unfold PRF_q_Advantage
  rw [hreal]
  refine (advantage_triangle _ (rfGame (extractAdv H msg n ikm A)) _).trans
    (add_le_add le_rfl ?_)
  rw [hmid]
  exact (expand_prf_eq H hinj n A).le

end ExtractExpand

/-! ## HKDF with HMAC -/

section HMAC

variable {K B S I : Type} [Fintype K] [Nonempty K] [DecidableEq K] [DecidableEq B] [Nontrivial B]
  [XorOp B] [Fintype S] [Nonempty S] [DecidableEq I] {ℓ : ℕ}

/-- HKDF-Extract: HMAC keyed by the salt, padded into a block by `spad`, on the input
keying material. -/
def hkdfExtract (f : K → B → K) (fpad : K → B) (iv : K) (ipad opad : B) (spad : S → B)
    (ℓ : ℕ) (salt : S) (ikm : Msg B ℓ) : K :=
  hmac f fpad iv ipad opad spad ℓ salt ikm

/-- HKDF-Expand: the chain of HMAC keyed by the pseudorandom key, padded into a block
by `kpad`, with inputs `msg T(i-1) info i`. -/
def hkdfExpand (f : K → B → K) (fpad : K → B) (iv : K) (ipad opad : B) (kpad : K → B)
    (ℓ : ℕ) (msg : Option K → I → ℕ → Msg B ℓ) (n : ℕ) (prk : K) (info : I) :
    List.Vector K n :=
  expand (hmac f fpad iv ipad opad kpad ℓ) msg n prk info

/-- **HKDF-Extract is a multi-query PRF keyed by the salt**: its advantage is the
HMAC advantage of `hmac_prf_bound`. -/
theorem hkdfExtract_prf_bound (f : K → B → K) {fpad : K → B} (hfpad : Function.Injective fpad)
    (iv : K) {ipad opad : B} (hpad : ipad ≠ opad) (spad : S → B)
    (A : OracleAdv (Msg B ℓ) K Bool) (q : ℕ) (hA : A.IsQueryBound q) :
    PRF_q_Advantage (hkdfExtract f fpad iv ipad opad spad ℓ) A ≤
      PRF_q_Advantage (hmacKeyFamily f iv spad) (hmacKeyAdv f fpad ipad opad A) +
        (PRF_q_Advantage f (nmacOuterAdv f fpad A) +
          ∑ j ∈ Finset.range q, ∑ i ∈ Finset.range j,
            ∑ m ∈ Finset.range (2 * ℓ + 1), PRF_q_Advantage f (cascadeAdv f A i j m) +
          ((q * (q - 1) / 2 : ℕ) : ℝ≥0∞) / Fintype.card K) :=
  hmac_prf_bound f hfpad iv hpad spad A q hA

/-- **HKDF-Expand is a multi-query PRF keyed by the pseudorandom key.** For `msg`
injective in the context and counter and an adversary asking at most `q` context
queries, its advantage is at most the HMAC bound of `hmac_prf_bound` for the
reduction `expandAdv msg n A`, which asks at most `q n` queries. -/
theorem hkdfExpand_prf_bound (f : K → B → K) {fpad : K → B} (hfpad : Function.Injective fpad)
    (iv : K) {ipad opad : B} (hpad : ipad ≠ opad) (kpad : K → B)
    {msg : Option K → I → ℕ → Msg B ℓ} (hinj : MsgInj msg) (n : ℕ)
    (A : OracleAdv I (List.Vector K n) Bool) (q : ℕ) (hA : A.IsQueryBound q) :
    PRF_q_Advantage (hkdfExpand f fpad iv ipad opad kpad ℓ msg n) A ≤
      PRF_q_Advantage (hmacKeyFamily f iv kpad)
          (hmacKeyAdv f fpad ipad opad (expandAdv msg n A)) +
        (PRF_q_Advantage f (nmacOuterAdv f fpad (expandAdv msg n A)) +
          ∑ j ∈ Finset.range (q * n), ∑ i ∈ Finset.range j,
            ∑ m ∈ Finset.range (2 * ℓ + 1),
              PRF_q_Advantage f (cascadeAdv f (expandAdv msg n A) i j m) +
          ((q * n * (q * n - 1) / 2 : ℕ) : ℝ≥0∞) / Fintype.card K) :=
  (expand_prf_eq (hmac f fpad iv ipad opad kpad ℓ) hinj n A).trans_le
    (hmac_prf_bound f hfpad iv hpad kpad (expandAdv msg n A) (q * n)
      (isQueryBound_expandAdv msg n hA))

/-- **HKDF is a multi-query PRF keyed by the salt** (Krawczyk 2010). With the input
keying material `ikm` fixed and adaptive context queries, the advantage of
Extract-then-Expand is at most the HMAC bound for the one-query extraction
reduction `extractAdv`, in which the collision terms vanish, plus the HMAC bound
for the expansion reduction `expandAdv msg n A`. -/
theorem hkdf_prf_bound (f : K → B → K) {fpad : K → B} (hfpad : Function.Injective fpad)
    (iv : K) {ipad opad : B} (hpad : ipad ≠ opad) (spad : S → B) (kpad : K → B)
    {msg : Option K → I → ℕ → Msg B ℓ} (hinj : MsgInj msg) (n : ℕ) (ikm : Msg B ℓ)
    (A : OracleAdv I (List.Vector K n) Bool) (q : ℕ) (hA : A.IsQueryBound q) :
    PRF_q_Advantage
        (hkdfSalted (hkdfExtract f fpad iv ipad opad spad ℓ) (hmac f fpad iv ipad opad kpad ℓ)
          msg n ikm) A ≤
      (PRF_q_Advantage (hmacKeyFamily f iv spad)
          (hmacKeyAdv f fpad ipad opad
            (extractAdv (hmac f fpad iv ipad opad kpad ℓ) msg n ikm A)) +
        PRF_q_Advantage f
          (nmacOuterAdv f fpad (extractAdv (hmac f fpad iv ipad opad kpad ℓ) msg n ikm A))) +
      (PRF_q_Advantage (hmacKeyFamily f iv kpad)
          (hmacKeyAdv f fpad ipad opad (expandAdv msg n A)) +
        (PRF_q_Advantage f (nmacOuterAdv f fpad (expandAdv msg n A)) +
          ∑ j ∈ Finset.range (q * n), ∑ i ∈ Finset.range j,
            ∑ m ∈ Finset.range (2 * ℓ + 1),
              PRF_q_Advantage f (cascadeAdv f (expandAdv msg n A) i j m) +
          ((q * n * (q * n - 1) / 2 : ℕ) : ℝ≥0∞) / Fintype.card K)) := by
  have h₁ := hkdfExtract_prf_bound f hfpad iv hpad spad
    (extractAdv (hmac f fpad iv ipad opad kpad ℓ) msg n ikm A) 1
    (isQueryBound_extractAdv _ msg n ikm hA)
  simp only [Finset.range_one, Finset.sum_singleton, Finset.range_zero, Finset.sum_empty,
    add_zero, Nat.sub_self, mul_zero, Nat.zero_div, Nat.cast_zero, ENNReal.zero_div] at h₁
  exact (hkdfSalted_prf_bound _ _ hinj n ikm A).trans
    (add_le_add h₁
      (hmac_prf_bound f hfpad iv hpad kpad (expandAdv msg n A) (q * n)
        (isQueryBound_expandAdv msg n hA)))

end HMAC

end CatCrypt.Crypto.Constructions.HKDFPRF
