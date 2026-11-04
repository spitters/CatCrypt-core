/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Constructions.HKDFPRF
public import CatCryptCore.Crypto.Constructions.QueryList
public import CatCryptCore.Crypto.AEAD.NonceBased
public import CatCryptCore.Crypto.UCConcrete
public import CatCryptCore.Crypto.OracleQueryVec
public import CatCryptCore.Tactics.QueryBound

/-!
# KBKDF is a multi-query PRF with variable-length output

NIST SP 800-108 Rev. 1 derives key material from a PRF `H` keyed by the key-derivation
key. For a query `x = (Label, Context, L)` it computes `n = ⌈L / h⌉` blocks
`K(i) = H KI (msg K(i-1) x i)` for `i = 1, …, n`, where `msg` encodes the counter `i`, the
fixed input data `Label ∥ 0x00 ∥ Context ∥ [L]₃₂` and, in feedback mode, the previous
block `K(i-1)` (the IV for `i = 1`). This is the chain `expand` of `HKDFPRF` with a
number of blocks depending on the query (`expandVar`).

The ideal object for variable-length output is the lazily sampled random function
`rfVarOracle len` that answers a fresh query `x` with a uniform list of `len x` blocks.
For an encoding injective in the query and the counter on the counters `1, …, N`
(`MsgInjOn msg N`) and output lengths of at most `N` blocks, the advantage of an
adversary against `expandVar` in this game equals the multi-query PRF advantage of `H`
against the reduction `expandVarAdv msg len A`, which answers each query `x` of `A` with
the `len x` chained queries (`expandVar_prf_eq_of_injOn`).

## Main definitions

* `rfVarOracle`, `rfVarGame`, `PRFVar_Advantage` — the variable-length PRF game
* `expandVar`, `chainQ`, `expandVarAdv` — the construction and its reduction
* `MsgInjOn` — injectivity of an encoding in the query and the counter on the counters
  `1, …, N`
* `be32`, `fixedInput`, `KbkdfQuery`, `ctrMsg`, `fbMsg`, `ctrMsgVia`, `fbMsgVia`,
  `kbkdfBlocks` — the SP 800-108 byte encoding for counter mode (§4.1) and feedback mode
  (§4.2) with an 8-bit separator and 32-bit big-endian counter and length fields
* `PRFStrategy`, `prfDistAdv`, `prfReal`, `FVarPRF` — the variable-length PRF as a
  concrete UC functionality on deterministic strategies of the environment

## Main results

* `expandVar_prf_eq` — for `MsgInj msg`, the variable-length PRF advantage of
  `expandVar H msg len` against `A` is the PRF advantage of `H` against
  `expandVarAdv msg len A`
* `expandVar_prf_eq_of_injOn`, `rfGame_expandVarAdv_eq_of_injOn` — the same for
  `MsgInjOn msg N` and `len ≤ N`
* `isQueryBound_expandVarAdv` — the reduction asks at most `q N` queries
* `msgInjOn_ctrMsg`, `msgInjOn_fbMsg`, `msgInjOn_ctrMsgVia`, `msgInjOn_fbMsgVia` — the
  SP 800-108 counter-mode and feedback-mode encodings are injective in the query and the
  counter on the counters below `2³²`, for labels without a zero byte
* `expandVar_hmac_prf_bound`, `kbkdfCounter_hmac_prf_bound` — the bound for HMAC as the
  PRF, in terms of the compression function
* `advantageA_prfReal_FVarPRF`, `expandVar_uc_of_injOn` — concrete UC emulation of
  `FVarPRF` with the PRF advantage of the reduction as bound

## Proof

The real games agree because the chained queries against the keyed oracle compute the
chain (`realGame_expandVar_eq`). For the ideal games, a table of the variable-length
random function is mapped to a table on inputs of `H` by `tabL`; every recorded list has
the length of its query, an invariant of `rfVarOracle`, so the chain of a recorded query
is answered from its list, and the chain of a fresh query consists of fresh inputs
(`rfVarOracle_map_tabL`). An encoding injective only on the counters `1, …, N` is
extended to a globally injective one on `D ⊕ (I × ℕ)` that tags the other counters
(`msgExt`); the reduction for the extension is the reduction for `msg` with its queries
relabelled by `Sum.inl`, which does not change the PRF advantage (`prf_extFun_mapQuery`).

The separator `0x00` makes the fixed input data parse uniquely only when the label has no
zero byte; `KbkdfQuery` carries this condition.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Constructions.KBKDFPRF

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.PRPPRF
open CatCrypt.Crypto.Constructions.ECBCPRF CatCrypt.Crypto.Constructions.NMACPRF
open CatCrypt.Crypto.Constructions.HKDFPRF
open scoped ENNReal

/-! ## Variable-length random functions -/

section VarPRF

variable {D K : Type} [DecidableEq D] [Fintype K] [Nonempty K]

/-- Lazily sampled random function with answers of length `len d` on the query `d`, with
the table as state: a recorded query returns its recorded answer; a fresh query samples a
uniform list of `len d` blocks and records it. -/
noncomputable def rfVarOracle (len : D → ℕ) (t : List (D × List K)) (d : D) :
    PMF (List K × List (D × List K)) :=
  match List.lookup d t with
  | some r => PMF.pure (r, t)
  | none => (PMF.uniformFintype (List.Vector K (len d))).map
      fun v => (v.toList, (d, v.toList) :: t)

/-- Ideal variable-length PRF game: run `A` against `rfVarOracle len`. -/
noncomputable def rfVarGame (len : D → ℕ) (A : OracleAdv D (List K) Bool) : SPComp Bool :=
  liftPMF ((OracleAdv.run (rfVarOracle len) A []).map Prod.fst)

/-- Adaptive variable-length PRF advantage of `A` against `F`, whose output on `d` has
`len d` blocks. -/
noncomputable def PRFVar_Advantage {Kp : Type} [Fintype Kp] [Nonempty Kp]
    (F : Kp → D → List K) (len : D → ℕ) (A : OracleAdv D (List K) Bool) : ℝ≥0∞ :=
  Advantage (realGame F A) (rfVarGame len A)

end VarPRF

/-! ## The variable-length chain -/

section ExpandVar

variable {K D I Kp : Type}

/-- The chain of `m` blocks for `info` computed with oracle queries, as a list. -/
def chainQ (msg : Option K → I → ℕ → D) (m : ℕ) (info : I) : OracleAdv D K (List K) :=
  OracleAdv.bind (expandQ msg info m 1 none) fun v => .ret v.toList

/-- The chain of `H` under the key `k` for the query `x`, with `len x` blocks. -/
def expandVar (H : Kp → D → K) (msg : Option K → I → ℕ → D) (len : I → ℕ) (k : Kp)
    (x : I) : List K :=
  (expand H msg (len x) k x).toList

/-- Reduction from the variable-length chain to its keyed function: run `A` once and
answer each query `x` with the chain of `len x` oracle queries. -/
def expandVarAdv (msg : Option K → I → ℕ → D) (len : I → ℕ)
    (A : OracleAdv I (List K) Bool) : OracleAdv D K Bool :=
  OracleAdv.subst (fun x => chainQ msg (len x) x) A

theorem isQueryBound_chainQ (msg : Option K → I → ℕ → D) (m : ℕ) (info : I) :
    (chainQ msg m info).IsQueryBound m := by
  query_bound [isQueryBound_expandQ]

/-- For output lengths of at most `N` blocks and an adversary asking at most `q`
queries, the reduction asks at most `q N` queries. -/
theorem isQueryBound_expandVarAdv (msg : Option K → I → ℕ → D) {len : I → ℕ} {N : ℕ}
    (hlen : ∀ x, len x ≤ N) {A : OracleAdv I (List K) Bool} {q : ℕ} (hA : A.IsQueryBound q) :
    (expandVarAdv msg len A).IsQueryBound (q * N) :=
  OracleAdv.isQueryBound_subst
    (fun x => (isQueryBound_chainQ msg (len x) x).mono (hlen x)) hA

variable [Fintype Kp] [Nonempty Kp]

/-- The real game of the variable-length chain is the real game of `H` against
`expandVarAdv`. -/
theorem realGame_expandVar_eq (H : Kp → D → K) (msg : Option K → I → ℕ → D) (len : I → ℕ)
    (A : OracleAdv I (List K) Bool) :
    realGame (expandVar H msg len) A = realGame H (expandVarAdv msg len A) := by
  unfold realGame expandVarAdv
  congr 1
  refine congrArg _ (funext fun k => ?_)
  rw [OracleAdv.run_subst]
  congr 1
  congr 1
  funext _ x
  simp only [chainQ, OracleAdv.run_bind]
  erw [run_keyed_expandQ (H k) msg x (len x) 1 none]
  simp [expandVar, expand, keyedOracle]

/-! ### The ideal games -/

variable [Fintype K] [Nonempty K] [DecidableEq D] [DecidableEq I]

/-- The inputs and answers of the chain of the list `v` from counter `i` and previous
block `prev`, most recent first. -/
def entriesL (msg : Option K → I → ℕ → D) (info : I) :
    ℕ → Option K → List K → List (D × K)
  | _, _, [] => []
  | i, prev, t :: v => entriesL msg info (i + 1) (some t) v ++ [(msg prev info i, t)]

omit [Fintype Kp] [Nonempty Kp] [Fintype K] [Nonempty K] [DecidableEq D] [DecidableEq I] in
theorem entries_eq_entriesL (msg : Option K → I → ℕ → D) (info : I) (m i : ℕ)
    (prev : Option K) (v : List.Vector K m) :
    entries msg info m i prev v = entriesL msg info i prev v.toList := by
  induction m generalizing i prev with
  | zero => simp [entries, entriesL, List.Vector.eq_nil v]
  | succ m ih =>
    conv_rhs => rw [← List.Vector.cons_head_tail v]
    rw [List.Vector.toList_cons, entriesL, ← ih]
    rfl

/-- The table on inputs of `H` corresponding to a table of the variable-length random
function. -/
def tabL (msg : Option K → I → ℕ → D) (s : List (I × List K)) : List (D × K) :=
  s.flatMap fun p => entriesL msg p.1 1 none p.2

omit [Fintype Kp] [Nonempty Kp] [Fintype K] [Nonempty K] in
theorem lookup_tabL_of_lookup_none {msg : Option K → I → ℕ → D} (hinj : MsgInj msg)
    (info : I) (s : List (I × List K)) (hs : List.lookup info s = none) (p : Option K)
    (j : ℕ) : List.lookup (msg p info j) (tabL msg s) = none := by
  induction s with
  | nil => rfl
  | cons a s ih =>
    obtain ⟨info', l⟩ := a
    have hne : info ≠ info' := by
      rintro rfl
      simp at hs
    have hb : (info == info') = false := by simpa using hne
    simp only [List.lookup_cons, hb] at hs
    simp only [tabL, List.flatMap_cons, List.lookup_append] at ih ⊢
    have h := lookup_entries_ne hinj l.length 1 none (⟨l, rfl⟩ : List.Vector K l.length) p j
      (Or.inl hne)
    erw [entries_eq_entriesL] at h
    rw [show List.lookup (msg p info j) (entriesL msg info' 1 none l) = none from h, ih hs]
    rfl

omit [Fintype Kp] [Nonempty Kp] [Fintype K] [Nonempty K] in
theorem known_tabL_of_lookup {msg : Option K → I → ℕ → D} (hinj : MsgInj msg) (info : I)
    (s : List (I × List K)) (l : List K) (hs : List.lookup info s = some l) :
    Known msg info (tabL msg s) l.length 1 none ⟨l, rfl⟩ := by
  induction s with
  | nil => simp at hs
  | cons a s ih =>
    obtain ⟨info', l'⟩ := a
    by_cases hne : info = info'
    · subst hne
      simp only [List.lookup_cons_self, Option.some.injEq] at hs
      subst hs
      have h := known_entries_append hinj info l'.length 1 none
        (⟨l', rfl⟩ : List.Vector K l'.length) (tabL msg s)
      erw [entries_eq_entriesL] at h
      exact h
    · have hb : (info == info') = false := by simpa using hne
      simp only [List.lookup_cons, hb] at hs
      simp only [tabL, List.flatMap_cons]
      refine known_append_of_fresh info _ _ (fun p j => ?_) l.length 1 none _ (ih hs)
      have h := lookup_entries_ne hinj l'.length 1 none (⟨l', rfl⟩ : List.Vector K l'.length)
        p j (Or.inl hne)
      erw [entries_eq_entriesL] at h
      exact h

/-- Every recorded list has the length of its query. -/
def LenInv (len : I → ℕ) (s : List (I × List K)) : Prop := ∀ p ∈ s, p.2.length = len p.1

omit [Fintype Kp] [Nonempty Kp] [DecidableEq D] in
theorem lenInv_rfVarOracle (len : I → ℕ) (s : List (I × List K)) (d : I)
    (x : List K × List (I × List K)) (hs : LenInv len s)
    (hx : x ∈ (rfVarOracle len s d).support) : LenInv len x.2 := by
  unfold rfVarOracle at hx
  split at hx
  · simp only [PMF.support_pure, Set.mem_singleton_iff] at hx
    subst hx
    exact hs
  · simp only [PMF.support_map, Set.mem_image] at hx
    obtain ⟨v, -, rfl⟩ := hx
    intro p hp
    rcases List.mem_cons.mp hp with rfl | hp
    · simp
    · exact hs p hp

omit [Fintype Kp] [Nonempty Kp] [Fintype K] [Nonempty K] [DecidableEq D] in
theorem length_of_lookup {len : I → ℕ} {s : List (I × List K)} (hs : LenInv len s) {info : I}
    {l : List K} (h : List.lookup info s = some l) : l.length = len info := by
  induction s with
  | nil => simp at h
  | cons a s ih =>
    obtain ⟨info', l'⟩ := a
    by_cases hne : info = info'
    · subst hne
      simp only [List.lookup_cons_self, Option.some.injEq] at h
      subst h
      exact hs _ (List.mem_cons_self ..)
    · have hb : (info == info') = false := by simpa using hne
      simp only [List.lookup_cons, hb] at h
      exact ih (fun p hp => hs p (List.mem_cons_of_mem _ hp)) h

omit [Fintype Kp] [Nonempty Kp] in
theorem rfVarOracle_map_tabL {msg : Option K → I → ℕ → D} (hinj : MsgInj msg)
    (len : I → ℕ) (s : List (I × List K)) (hs : LenInv len s) (info : I) :
    (rfVarOracle len s info).map (Prod.map id (tabL msg)) =
      OracleAdv.run rfOracle (chainQ msg (len info) info) (tabL msg s) := by
  cases hl : List.lookup info s with
  | some l =>
    have hk := run_expandQ_known msg info l.length 1 none ⟨l, rfl⟩ _
      (known_tabL_of_lookup hinj info s l hl)
    have hc : OracleAdv.run rfOracle (chainQ msg l.length info) (tabL msg s) =
        PMF.pure (l, tabL msg s) := by
      simp only [chainQ, OracleAdv.run_bind, hk, PMF.pure_bind, OracleAdv.run_ret]
      rfl
    rw [← length_of_lookup hs hl, hc]
    simp [rfVarOracle, hl, PMF.pure_map]
  | none =>
    rw [chainQ, OracleAdv.run_bind, run_expandQ_fresh hinj info (len info) 1 none _
      (fun p j _ => lookup_tabL_of_lookup_none hinj info s hl p j)]
    simp only [rfVarOracle, hl, PMF.map_comp, Function.comp_def, tabL, entries_eq_entriesL,
      PMF.bind_map, OracleAdv.run_ret, Prod.map, id, List.flatMap_cons]
    exact (PMF.bind_pure_comp _ _).symm

omit [Fintype Kp] [Nonempty Kp] in
/-- The ideal game of the variable-length reduction is the variable-length random-function
game on queries. -/
theorem rfGame_expandVarAdv_eq {msg : Option K → I → ℕ → D} (hinj : MsgInj msg)
    (len : I → ℕ) (A : OracleAdv I (List K) Bool) :
    rfGame (expandVarAdv msg len A) = rfVarGame len A := by
  unfold rfGame rfVarGame expandVarAdv
  rw [OracleAdv.run_subst]
  have h := CatCrypt.Crypto.AEAD.NonceBased.OracleAdv.run_map_state_of_inv (rfVarOracle len)
    (fun T x => OracleAdv.run rfOracle (chainQ msg (len x) x) T) (tabL msg) (LenInv len)
    (fun s d x hs hx => lenInv_rfVarOracle len s d x hs hx)
    (fun s d hs => rfVarOracle_map_tabL hinj len s hs d) A [] (fun _ h => by simp at h)
  change _ = OracleAdv.run _ A [] at h
  rw [← h, PMF.map_comp]
  rfl

/-- **The variable-length chain is a PRF with the PRF advantage of its keyed function.**
For `msg` injective in the query and the counter, the variable-length PRF advantage of
`expandVar H msg len` against `A` equals the PRF advantage of `H` against
`expandVarAdv msg len A`, which runs `A` once and asks `len x` queries per query `x`. -/
theorem expandVar_prf_eq (H : Kp → D → K) {msg : Option K → I → ℕ → D} (hinj : MsgInj msg)
    (len : I → ℕ) (A : OracleAdv I (List K) Bool) :
    PRFVar_Advantage (expandVar H msg len) len A =
      PRF_q_Advantage H (expandVarAdv msg len A) := by
  unfold PRFVar_Advantage PRF_q_Advantage
  rw [realGame_expandVar_eq, rfGame_expandVarAdv_eq hinj]

end ExpandVar

/-! ## Encodings injective on a range of counters -/

section InjOn

variable {K D I Kp : Type}

/-- `msg` determines the query and the counter on the counters `1, …, n`. -/
def MsgInjOn (msg : Option K → I → ℕ → D) (n : ℕ) : Prop :=
  ∀ p p' info info' i i', 1 ≤ i → i ≤ n → 1 ≤ i' → i' ≤ n →
    msg p info i = msg p' info' i' → info = info' ∧ i = i'

/-- An injective map on the messages at the counters `1, …, n` preserves `MsgInjOn`. -/
theorem MsgInjOn.comp {D' : Type} {msg : Option K → I → ℕ → D} {n : ℕ}
    (h : MsgInjOn msg n) (g : D → D')
    (hg : ∀ p p' info info' i i', 1 ≤ i → i ≤ n → 1 ≤ i' → i' ≤ n →
      g (msg p info i) = g (msg p' info' i') → msg p info i = msg p' info' i') :
    MsgInjOn (fun p info i => g (msg p info i)) n :=
  fun p p' info info' i i' h1 h2 h3 h4 he =>
    h p p' info info' i i' h1 h2 h3 h4 (hg p p' info info' i i' h1 h2 h3 h4 he)

/-- The encoding `msg` on the counters `1, …, n`, and the tagged query and counter
elsewhere. -/
def msgExt (msg : Option K → I → ℕ → D) (n : ℕ) :
    Option K → I → ℕ → D ⊕ (I × ℕ) :=
  fun p info i => if 1 ≤ i ∧ i ≤ n then .inl (msg p info i) else .inr (info, i)

theorem msgInj_msgExt {msg : Option K → I → ℕ → D} {n : ℕ} (h : MsgInjOn msg n) :
    MsgInj (msgExt msg n) := by
  intro p p' info info' i i' he
  unfold msgExt at he
  split_ifs at he with h1 h2
  · exact h p p' info info' i i' h1.1 h1.2 h2.1 h2.2 (Sum.inl_injective he)
  all_goals (cases he; try exact ⟨rfl, rfl⟩)

/-- `H` on `D`, and the constant `k₀` on the tags. -/
def extFun (H : Kp → D → K) (k₀ : K) : Kp → D ⊕ (I × ℕ) → K :=
  fun k => Sum.elim (H k) fun _ => k₀

theorem expandVec_extFun (H : Kp → D → K) (k₀ : K) (k : Kp) (msg : Option K → I → ℕ → D)
    (n : ℕ) (info : I) (m i : ℕ) (prev : Option K) (hi : 1 ≤ i) (hm : i + m ≤ n + 1) :
    expandVec (extFun H k₀ k) (msgExt msg n) info m i prev =
      expandVec (H k) msg info m i prev := by
  induction m generalizing i prev with
  | zero => rfl
  | succ m ih =>
    have hc : 1 ≤ i ∧ i ≤ n := ⟨hi, by omega⟩
    simp only [expandVec, msgExt, ite_eq_left hc, extFun, Sum.elim_inl]
    rw [← ih (i + 1) _ (by omega) (by omega)]
    rfl

theorem mapQuery_bind {D₀ R α β : Type} (c : D → D₀) (t : OracleAdv D R β)
    (k : β → OracleAdv D R α) :
    OracleAdv.mapQuery c (OracleAdv.bind t k) =
      OracleAdv.bind (OracleAdv.mapQuery c t) fun x => OracleAdv.mapQuery c (k x) := by
  induction t with
  | ret b => rfl
  | rand p k' ih => simp only [OracleAdv.bind, OracleAdv.mapQuery, ih]
  | query d k' ih => simp only [OracleAdv.bind, OracleAdv.mapQuery, ih]

theorem subst_mapQuery {D₁ D₀ R R₀ α : Type} (c : D₁ → D₀)
    (impl : D → OracleAdv D₁ R₀ R) (A : OracleAdv D R α) :
    OracleAdv.subst (fun d => OracleAdv.mapQuery c (impl d)) A =
      OracleAdv.mapQuery c (OracleAdv.subst impl A) := by
  induction A with
  | ret a => rfl
  | rand p k ih => simp only [OracleAdv.subst_rand, OracleAdv.mapQuery, ih]
  | query d k ih => simp only [OracleAdv.subst_query, mapQuery_bind, ih]

theorem expandQ_msgExt (msg : Option K → I → ℕ → D) (n : ℕ) (info : I) (m i : ℕ)
    (prev : Option K) (hi : 1 ≤ i) (hm : i + m ≤ n + 1) :
    expandQ (msgExt msg n) info m i prev =
      OracleAdv.mapQuery Sum.inl (expandQ msg info m i prev) := by
  induction m generalizing i prev with
  | zero => rfl
  | succ m ih =>
    have hc : 1 ≤ i ∧ i ≤ n := ⟨hi, by omega⟩
    simp only [expandQ, msgExt, ite_eq_left hc, OracleAdv.mapQuery, mapQuery_bind]
    congr 1
    funext t
    grind

theorem expandVarAdv_msgExt (msg : Option K → I → ℕ → D) {n : ℕ} {len : I → ℕ}
    (hlen : ∀ x, len x ≤ n) (A : OracleAdv I (List K) Bool) :
    expandVarAdv (msgExt msg n) len A =
      OracleAdv.mapQuery Sum.inl (expandVarAdv msg len A) := by
  unfold expandVarAdv
  rw [← subst_mapQuery]
  congr 1
  funext x
  simp only [chainQ, expandQ_msgExt msg n x (len x) 1 none le_rfl (by have := hlen x; omega),
    mapQuery_bind]
  rfl

variable [Fintype Kp] [Nonempty Kp] [Fintype K] [Nonempty K] [DecidableEq D] [DecidableEq I]

/-- Relabelling the queries of an adversary by `Sum.inl` and extending the keyed function
to the tags does not change the PRF advantage. -/
theorem prf_extFun_mapQuery (H : Kp → D → K) (k₀ : K) (B : OracleAdv D K Bool) :
    PRF_q_Advantage (extFun (I := I) H k₀) (OracleAdv.mapQuery Sum.inl B) =
      PRF_q_Advantage H B := by
  unfold PRF_q_Advantage realGame rfGame
  simp only [OracleAdv.run_mapQuery]
  congr 2
  exact run_rfOracle_comp_injective (X := D) (Y := D ⊕ (I × ℕ)) (R := K) Sum.inl_injective id B

/-- **The variable-length chain is a PRF for an encoding injective on a range of
counters.** For `msg` injective in the query and the counter on the counters `1, …, N` and
output lengths of at most `N` blocks, the variable-length PRF advantage of
`expandVar H msg len` against `A` equals the PRF advantage of `H` against
`expandVarAdv msg len A`. -/
theorem expandVar_prf_eq_of_injOn (H : Kp → D → K) {msg : Option K → I → ℕ → D} {N : ℕ}
    (hinj : MsgInjOn msg N) {len : I → ℕ} (hlen : ∀ x, len x ≤ N)
    (A : OracleAdv I (List K) Bool) :
    PRFVar_Advantage (expandVar H msg len) len A =
      PRF_q_Advantage H (expandVarAdv msg len A) := by
  obtain ⟨k₀⟩ := ‹Nonempty K›
  have e : expandVar (extFun H k₀) (msgExt msg N) len = expandVar H msg len := by
    funext k x
    exact congrArg List.Vector.toList
      (expandVec_extFun H k₀ k msg N x (len x) 1 none le_rfl (by have := hlen x; omega))
  rw [← e, expandVar_prf_eq _ (msgInj_msgExt hinj), expandVarAdv_msgExt msg hlen,
    prf_extFun_mapQuery]

omit [Fintype Kp] [Nonempty Kp] in
/-- The ideal game of the variable-length reduction is the variable-length random-function
game, for an encoding injective on the counters `1, …, N` and lengths of at most `N`. -/
theorem rfGame_expandVarAdv_eq_of_injOn {msg : Option K → I → ℕ → D} {N : ℕ}
    (hinj : MsgInjOn msg N) {len : I → ℕ} (hlen : ∀ x, len x ≤ N)
    (A : OracleAdv I (List K) Bool) :
    rfGame (expandVarAdv msg len A) = rfVarGame len A := by
  rw [← rfGame_expandVarAdv_eq (msgInj_msgExt hinj) len A, expandVarAdv_msgExt msg hlen]
  unfold rfGame
  simp only [OracleAdv.run_mapQuery]
  exact congrArg liftPMF
    (run_rfOracle_comp_injective (X := D) (Y := D ⊕ (I × ℕ)) (R := K) Sum.inl_injective id
      _).symm

end InjOn

/-! ## The SP 800-108 encoding -/

section SP800108

/-- The big-endian 32-bit encoding of `n mod 2³²`. -/
def be32 (n : ℕ) : List UInt8 :=
  [UInt8.ofNat (n / 2 ^ 24), UInt8.ofNat (n / 2 ^ 16), UInt8.ofNat (n / 2 ^ 8), UInt8.ofNat n]

@[simp] theorem length_be32 (n : ℕ) : (be32 n).length = 4 := rfl

theorem be32_inj {a b : ℕ} (ha : a < 2 ^ 32) (hb : b < 2 ^ 32) (h : be32 a = be32 b) :
    a = b := by
  simp only [be32, List.cons.injEq, and_true] at h
  obtain ⟨h1, h2, h3, h4⟩ := h
  have e1 := congrArg UInt8.toNat h1
  have e2 := congrArg UInt8.toNat h2
  have e3 := congrArg UInt8.toNat h3
  have e4 := congrArg UInt8.toNat h4
  simp only [UInt8.toNat_ofNat'] at e1 e2 e3 e4
  omega

/-- A prefix without a zero byte followed by a zero byte is determined by the list. -/
theorem append_zero_cons_inj {l l' r r' : List UInt8} (hl : (0 : UInt8) ∉ l)
    (hl' : (0 : UInt8) ∉ l') (h : l ++ 0 :: r = l' ++ 0 :: r') : l = l' ∧ r = r' := by
  induction l generalizing l' with
  | nil =>
    cases l' with
    | nil => simpa using h
    | cons b l' =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1 ▸ List.mem_cons_self ..) hl'
  | cons a l ih =>
    cases l' with
    | nil =>
      simp only [List.nil_append, List.cons_append, List.cons.injEq] at h
      exact absurd (h.1 ▸ List.mem_cons_self ..) hl
    | cons b l' =>
      simp only [List.cons_append, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      obtain ⟨h1, h2⟩ := ih (fun hm => hl (List.mem_cons_of_mem _ hm))
        (fun hm => hl' (List.mem_cons_of_mem _ hm)) h
      exact ⟨by rw [h1], h2⟩

/-- A KBKDF query of SP 800-108: a label without a zero byte of at most `lmax` bytes, a
context of at most `cmax` bytes, and the output length `L` in bits. -/
structure KbkdfQuery (lmax cmax : ℕ) where
  /-- The label. -/
  label : List UInt8
  /-- The context. -/
  context : List UInt8
  /-- The output length in bits. -/
  outBits : UInt32
  label_zero_free : (0 : UInt8) ∉ label
  label_le : label.length ≤ lmax
  context_le : context.length ≤ cmax
deriving DecidableEq

variable {lmax cmax : ℕ}

/-- The fixed input data `Label ∥ 0x00 ∥ Context ∥ [L]₃₂` (SP 800-108 Rev. 1, §4). -/
def fixedInput (x : KbkdfQuery lmax cmax) : List UInt8 :=
  x.label ++ 0 :: (x.context ++ be32 x.outBits.toNat)

theorem length_fixedInput_le (x : KbkdfQuery lmax cmax) :
    (fixedInput x).length ≤ lmax + cmax + 5 := by
  have := x.label_le
  have := x.context_le
  simp only [fixedInput, List.length_append, List.length_cons, length_be32]
  omega

theorem fixedInput_inj {x x' : KbkdfQuery lmax cmax} (h : fixedInput x = fixedInput x') :
    x = x' := by
  obtain ⟨hl, hr⟩ := append_zero_cons_inj x.label_zero_free x'.label_zero_free h
  obtain ⟨hc, hL⟩ := List.append_inj' hr (by simp)
  have hb := be32_inj x.outBits.toNat_lt x'.outBits.toNat_lt hL
  cases x
  cases x'
  simp only at hl hc hb
  subst hl hc
  simp only [KbkdfQuery.mk.injEq, true_and]
  exact UInt32.toNat_inj.mp hb

/-- The counter-mode PRF input `[i]₃₂ ∥ Label ∥ 0x00 ∥ Context ∥ [L]₃₂`
(SP 800-108 Rev. 1, §4.1). -/
def ctrMsg (K : Type) (lmax cmax : ℕ) :
    Option K → KbkdfQuery lmax cmax → ℕ → List UInt8 :=
  fun _ x i => be32 i ++ fixedInput x

/-- The feedback-mode PRF input `K(i-1) ∥ [i]₃₂ ∥ Label ∥ 0x00 ∥ Context ∥ [L]₃₂`, with
the IV in place of `K(0)`, for a byte encoding `blk` of the blocks (SP 800-108 Rev. 1,
§4.2). -/
def fbMsg {K : Type} (blk : K → List UInt8) (iv : List UInt8) (lmax cmax : ℕ) :
    Option K → KbkdfQuery lmax cmax → ℕ → List UInt8 :=
  fun p x i => p.elim iv blk ++ (be32 i ++ fixedInput x)

/-- **The counter-mode encoding is injective** in the query and the counter on the
counters below `2³²`. -/
theorem msgInjOn_ctrMsg (K : Type) (lmax cmax : ℕ) {N : ℕ} (hN : N < 2 ^ 32) :
    MsgInjOn (ctrMsg K lmax cmax) N := by
  intro p p' x x' i i' _ hi _ hi' he
  obtain ⟨hc, hf⟩ := List.append_inj he (by simp)
  exact ⟨fixedInput_inj hf, be32_inj (by omega) (by omega) hc⟩

/-- **The feedback-mode encoding is injective** in the query and the counter on the
counters below `2³²`, for block encodings and an IV of one length `w`. -/
theorem msgInjOn_fbMsg {K : Type} {blk : K → List UInt8} {iv : List UInt8} {w : ℕ}
    (hblk : ∀ k, (blk k).length = w) (hiv : iv.length = w) (lmax cmax : ℕ) {N : ℕ}
    (hN : N < 2 ^ 32) : MsgInjOn (fbMsg blk iv lmax cmax) N := by
  intro p p' x x' i i' _ hi _ hi' he
  have hlen : ∀ q : Option K, (q.elim iv blk).length = w := by
    intro q; cases q <;> simp [hblk, hiv]
  obtain ⟨-, he⟩ := List.append_inj he (by rw [hlen, hlen])
  obtain ⟨hc, hf⟩ := List.append_inj he (by simp)
  exact ⟨fixedInput_inj hf, be32_inj (by omega) (by omega) hc⟩

/-- The number of blocks `⌈L / h⌉` of a query for blocks of `h` bits. -/
def kbkdfBlocks (h : ℕ) (x : KbkdfQuery lmax cmax) : ℕ := (x.outBits.toNat + h - 1) / h

/-- The number of blocks `⌈(2³² - 1) / h⌉` of the longest output. -/
def kbkdfMaxBlocks (h : ℕ) : ℕ := (2 ^ 32 - 1 + h - 1) / h

theorem kbkdfBlocks_le (h : ℕ) (x : KbkdfQuery lmax cmax) :
    kbkdfBlocks h x ≤ kbkdfMaxBlocks h :=
  Nat.div_le_div_right (by have := x.outBits.toNat_lt; omega)

theorem kbkdfMaxBlocks_lt (h : ℕ) : kbkdfMaxBlocks h < 2 ^ 32 := by
  unfold kbkdfMaxBlocks
  rcases Nat.eq_zero_or_pos h with rfl | hh
  · simp
  · exact (Nat.div_lt_iff_lt_mul hh).mpr (by omega)

/-- The counter-mode PRF inputs mapped into the input type of the PRF by `toMsg`. -/
def ctrMsgVia (K : Type) {M : Type} (toMsg : List UInt8 → M) (lmax cmax : ℕ) :
    Option K → KbkdfQuery lmax cmax → ℕ → M :=
  fun p x i => toMsg (ctrMsg K lmax cmax p x i)

/-- The feedback-mode PRF inputs mapped into the input type of the PRF by `toMsg`. -/
def fbMsgVia {K M : Type} (blk : K → List UInt8) (iv : List UInt8) (toMsg : List UInt8 → M)
    (lmax cmax : ℕ) : Option K → KbkdfQuery lmax cmax → ℕ → M :=
  fun p x i => toMsg (fbMsg blk iv lmax cmax p x i)

/-- The counter-mode encoding through a map injective on byte strings of the lengths that
occur is injective in the query and the counter on the counters below `2³²`. -/
theorem msgInjOn_ctrMsgVia (K : Type) {M : Type} {toMsg : List UInt8 → M}
    (htoMsg : Set.InjOn toMsg {m | m.length ≤ lmax + cmax + 9}) {N : ℕ} (hN : N < 2 ^ 32) :
    MsgInjOn (ctrMsgVia K toMsg lmax cmax) N := by
  refine (msgInjOn_ctrMsg K lmax cmax hN).comp toMsg fun p p' x x' i i' _ _ _ _ he =>
    htoMsg ?_ ?_ he
  · have := length_fixedInput_le x
    simp only [Set.mem_ofPred_eq, ctrMsg, List.length_append, length_be32]
    omega
  · have := length_fixedInput_le x'
    simp only [Set.mem_ofPred_eq, ctrMsg, List.length_append, length_be32]
    omega

/-- The feedback-mode encoding through a map injective on byte strings of the lengths that
occur is injective in the query and the counter on the counters below `2³²`. -/
theorem msgInjOn_fbMsgVia {K M : Type} {blk : K → List UInt8} {iv : List UInt8} {w : ℕ}
    (hblk : ∀ k, (blk k).length = w) (hiv : iv.length = w) {toMsg : List UInt8 → M}
    (htoMsg : Set.InjOn toMsg {m | m.length ≤ w + lmax + cmax + 9}) {N : ℕ}
    (hN : N < 2 ^ 32) : MsgInjOn (fbMsgVia blk iv toMsg lmax cmax) N := by
  have hlen : ∀ (p : Option K) (x : KbkdfQuery lmax cmax) (i : ℕ),
      (fbMsg blk iv lmax cmax p x i).length ≤ w + lmax + cmax + 9 := by
    intro p x i
    have := length_fixedInput_le x
    have hp : (p.elim iv blk).length = w := by cases p <;> simp [hblk, hiv]
    simp only [fbMsg, List.length_append, length_be32, hp]
    omega
  exact (msgInjOn_fbMsg hblk hiv lmax cmax hN).comp toMsg
    fun p p' x x' i i' _ _ _ _ he => htoMsg (hlen p x i) (hlen p' x' i') he

end SP800108

/-! ## KBKDF with HMAC -/

section HMAC

variable {K B Kh I : Type} [Fintype K] [Nonempty K] [DecidableEq K] [DecidableEq B]
  [Nontrivial B] [XorOp B] [Fintype Kh] [Nonempty Kh] [DecidableEq I] {ℓ : ℕ}

/-- **The variable-length HMAC chain is a multi-query PRF.** For `msg` injective in the
query and the counter on the counters `1, …, N`, output lengths of at most `N` blocks and
an adversary asking at most `q` queries, the variable-length PRF advantage is at most the
HMAC bound of `hmac_prf_bound` for the reduction `expandVarAdv msg len A`, which asks at
most `q N` queries. -/
theorem expandVar_hmac_prf_bound (f : K → B → K) {fpad : K → B}
    (hfpad : Function.Injective fpad) (iv : K) {ipad opad : B} (hpad : ipad ≠ opad)
    (kpad : Kh → B) {msg : Option K → I → ℕ → Msg B ℓ} {N : ℕ} (hinj : MsgInjOn msg N)
    {len : I → ℕ} (hlen : ∀ x, len x ≤ N) (A : OracleAdv I (List K) Bool) (q : ℕ)
    (hA : A.IsQueryBound q) :
    PRFVar_Advantage (expandVar (hmac f fpad iv ipad opad kpad ℓ) msg len) len A ≤
      PRF_q_Advantage (hmacKeyFamily f iv kpad)
          (hmacKeyAdv f fpad ipad opad (expandVarAdv msg len A)) +
        (PRF_q_Advantage f (nmacOuterAdv f fpad (expandVarAdv msg len A)) +
          ∑ j ∈ Finset.range (q * N), ∑ i ∈ Finset.range j,
            ∑ m ∈ Finset.range (2 * ℓ + 1),
              PRF_q_Advantage f (cascadeAdv f (expandVarAdv msg len A) i j m) +
          ((q * N * (q * N - 1) / 2 : ℕ) : ℝ≥0∞) / Fintype.card K) :=
  (expandVar_prf_eq_of_injOn _ hinj hlen A).trans_le
    (hmac_prf_bound f hfpad iv hpad kpad _ (q * N) (isQueryBound_expandVarAdv msg hlen hA))

/-- **KBKDF in counter mode with HMAC is a multi-query PRF** (SP 800-108 Rev. 1, §4.1).
For blocks of `h` bits, PRF inputs mapped to HMAC messages by `toMsg`, injective on byte
strings of the lengths that occur, and an adversary asking at most `q` queries
`(Label, Context, L)`, each answered with `⌈L / h⌉` blocks, the advantage against KBKDF is
at most the HMAC bound for the reduction `expandVarAdv`, which asks at most
`q ⌈(2³² - 1) / h⌉` queries: the related-key PRF advantage of the key derivation, the PRF
advantage of the compression function against the outer and the cascade reductions, and
the collision term. -/
theorem kbkdfCounter_hmac_prf_bound (f : K → B → K) {fpad : K → B}
    (hfpad : Function.Injective fpad) (iv : K) {ipad opad : B} (hpad : ipad ≠ opad)
    (kpad : Kh → B) {lmax cmax : ℕ} {toMsg : List UInt8 → Msg B ℓ}
    (htoMsg : Set.InjOn toMsg {m | m.length ≤ lmax + cmax + 9}) (h : ℕ)
    (A : OracleAdv (KbkdfQuery lmax cmax) (List K) Bool) (q : ℕ) (hA : A.IsQueryBound q) :
    PRFVar_Advantage (expandVar (hmac f fpad iv ipad opad kpad ℓ)
        (ctrMsgVia K toMsg lmax cmax) (kbkdfBlocks h)) (kbkdfBlocks h) A ≤
      PRF_q_Advantage (hmacKeyFamily f iv kpad)
          (hmacKeyAdv f fpad ipad opad
            (expandVarAdv (ctrMsgVia K toMsg lmax cmax) (kbkdfBlocks h) A)) +
        (PRF_q_Advantage f
            (nmacOuterAdv f fpad (expandVarAdv (ctrMsgVia K toMsg lmax cmax) (kbkdfBlocks h) A)) +
          ∑ j ∈ Finset.range (q * kbkdfMaxBlocks h), ∑ i ∈ Finset.range j,
            ∑ m ∈ Finset.range (2 * ℓ + 1),
              PRF_q_Advantage f
                (cascadeAdv f (expandVarAdv (ctrMsgVia K toMsg lmax cmax) (kbkdfBlocks h) A)
                  i j m) +
          ((q * kbkdfMaxBlocks h * (q * kbkdfMaxBlocks h - 1) / 2 : ℕ) : ℝ≥0∞) /
            Fintype.card K) := by
  grind [expandVar_hmac_prf_bound, msgInjOn_ctrMsgVia, kbkdfMaxBlocks_lt, kbkdfBlocks_le]

end HMAC

/-! ## The variable-length PRF functionality -/

section Functionality

open CatCrypt.Crypto.Constructions.QueryList CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCDSL

variable {D K Kp : Type}

/-- A deterministic adaptive strategy of an environment of a variable-length PRF: from the
transcript of queries and answers so far, latest first, the next query or `none` to
stop. -/
structure PRFStrategy (D K : Type) where
  /-- The next query on a transcript, `none` to stop. -/
  next : List (D × List K) → Option D

/-- The strategy `S` from the transcript `h` as an oracle adversary with at most `n`
further queries, returning the final transcript. -/
def PRFStrategy.toAdv (S : PRFStrategy D K) :
    ℕ → List (D × List K) → OracleAdv D (List K) (List (D × List K))
  | 0, h => .ret h
  | n + 1, h => match S.next h with
    | none => .ret h
    | some d => .query d fun r => S.toAdv n ((d, r) :: h)

@[query_fold] theorem PRFStrategy.isQueryBound_toAdv (S : PRFStrategy D K) (n : ℕ)
    (h : List (D × List K)) : (S.toAdv n h).IsQueryBound n := by
  induction n generalizing h <;> query_bound

/-- The PRF adversary of a strategy and a distinguisher: run `S` for at most `q` queries
and output a sample of the output bit of `Dist` on the transcript. -/
noncomputable def prfDistAdv (q : ℕ) (S : PRFStrategy D K)
    (Dist : List (D × List K) → SPComp Bool) : OracleAdv D (List K) Bool :=
  OracleAdv.bind (S.toAdv q []) fun tr => .rand (outBool Dist tr) .ret

theorem isQueryBound_prfDistAdv (q : ℕ) (S : PRFStrategy D K)
    (Dist : List (D × List K) → SPComp Bool) : (prfDistAdv q S Dist).IsQueryBound q := by
  query_bound

theorem run_prfDistAdv_map_fst {St : Type} (O : St → D → PMF (List K × St)) (q : ℕ)
    (S : PRFStrategy D K) (Dist : List (D × List K) → SPComp Bool) (s : St) :
    (OracleAdv.run O (prfDistAdv q S Dist) s).map Prod.fst =
      ((OracleAdv.run O (S.toAdv q []) s).map Prod.fst).bind (outBool Dist) := by
  simp only [prfDistAdv, OracleAdv.run_bind, OracleAdv.run_rand, OracleAdv.run_ret,
    PMF.map_bind, PMF.bind_map, PMF.pure_map]
  refine congrArg _ (funext fun x => ?_)
  exact PMF.bind_pure _

/-- **The real protocol of a variable-length PRF** `F` on strategies run for at most `q`
queries: sample a key and answer the queries with `F`; the view is the transcript. -/
noncomputable def prfReal [Fintype Kp] [Nonempty Kp] (F : Kp → D → List K) (q : ℕ) :
    PRFStrategy D K → SPComp (List (D × List K)) :=
  fun S => liftPMF ((PMF.uniformFintype Kp).bind fun k =>
    (OracleAdv.run (keyedOracle F k) (S.toAdv q []) ()).map Prod.fst)

/-- **The ideal functionality of a variable-length PRF** on strategies run for at most `q`
queries: answer every fresh query `d` with a uniform list of `len d` blocks and every
repeated query consistently; the view is the transcript. -/
noncomputable def FVarPRF [DecidableEq D] [Fintype K] [Nonempty K] (len : D → ℕ) (q : ℕ) :
    PRFStrategy D K → SPComp (List (D × List K)) :=
  fun S => liftPMF ((OracleAdv.run (rfVarOracle len) (S.toAdv q []) []).map Prod.fst)

variable [Fintype Kp] [Nonempty Kp] [DecidableEq D] [Fintype K] [Nonempty K]

/-- **Distinguishing the real protocol from `FVarPRF` is the variable-length PRF game.** -/
theorem advantageA_prfReal_FVarPRF (F : Kp → D → List K) (len : D → ℕ) (q : ℕ)
    (S : PRFStrategy D K) (Dist : List (D × List K) → SPComp Bool) :
    AdvantageA (prfReal F q S) (FVarPRF len q S) Dist =
      PRFVar_Advantage F len (prfDistAdv q S Dist) := by
  simp_all [AdvantageA, Advantage, prfReal, FVarPRF, PRFVar_Advantage, realGame, rfVarGame,
      prTrue_liftPMF_bind, prTrue_liftPMF, run_prfDistAdv_map_fst, PMF.bind_bind]

omit [DecidableEq D] [Fintype K] [Nonempty K] in
theorem prfReal_isPure (F : Kp → D → List K) (q : ℕ) (S : PRFStrategy D K) :
    SPComp.IsPure (prfReal F q S) :=
  liftPMF_isPure _

omit [Fintype Kp] [Nonempty Kp] in
theorem FVarPRF_isPure (len : D → ℕ) (q : ℕ) (S : PRFStrategy D K) :
    SPComp.IsPure (FVarPRF len q S) :=
  liftPMF_isPure _

omit [DecidableEq D] [Fintype K] [Nonempty K] in
instance pureGame_prfReal (F : Kp → D → List K) (q : ℕ) : PureGame (prfReal F q) :=
  ⟨prfReal_isPure F q⟩

omit [Fintype Kp] [Nonempty Kp] in
instance pureGame_FVarPRF (len : D → ℕ) (q : ℕ) : PureGame (FVarPRF (K := K) len q) :=
  ⟨FVarPRF_isPure len q⟩

variable {I : Type} [DecidableEq I]

/-- The concrete game bound of the variable-length chain: for every strategy `S` and
distinguisher `Dist`, the advantage is the PRF advantage of `H` against
`expandVarAdv msg len (prfDistAdv q S Dist)`. -/
theorem gameAdvBoundC_expandVar (H : Kp → D → K) {msg : Option K → I → ℕ → D} {N : ℕ}
    (hinj : MsgInjOn msg N) {len : I → ℕ} (hlen : ∀ x, len x ≤ N) (q : ℕ) :
    GameAdvBoundC (prfReal (expandVar H msg len) q) (FVarPRF len q)
      (fun S Dist => PRF_q_Advantage H (expandVarAdv msg len (prfDistAdv q S Dist))) :=
  ⟨fun S Dist => by rw [advantageA_prfReal_FVarPRF, expandVar_prf_eq_of_injOn H hinj hlen]⟩

/-- **Concrete UC security of the variable-length chain**, `UCFromGameC.uc` at
`gameAdvBoundC_expandVar`. For
`msg` injective in the query and the counter on the counters `1, …, N` and output lengths
of at most `N` blocks, the real protocol of `expandVar H msg len` on strategies run for at
most `q` queries concretely UC-emulates `FVarPRF len q`, with simulator the adversary and
gap at most the PRF advantage of `H` against `expandVarAdv msg len (prfDistAdv q S Dist)`
at the environment's strategy `S` and the distinguisher `envReduction A Z`. -/
theorem expandVar_uc_of_injOn (H : Kp → D → K) {msg : Option K → I → ℕ → D} {N : ℕ}
    (hinj : MsgInjOn msg N) {len : I → ℕ} (hlen : ∀ x, len x ≤ N) (q : ℕ) (V : Type) :
    UCEmulatesCSim (UCSpec.ofGame (PRFStrategy I K) (List (I × List K)) V)
      (UCProtocol.ofGame (prfReal (expandVar H msg len) q))
      (UCProtocol.ofGame (FVarPRF len q)) id
      (gameUCBound fun S Dist =>
        PRF_q_Advantage H (expandVarAdv msg len (prfDistAdv q S Dist))) :=
  have := gameAdvBoundC_expandVar H hinj hlen q
  (inferInstance : UCFromGameC (prfReal (expandVar H msg len) q) (FVarPRF len q) V
    (fun S Dist => PRF_q_Advantage H (expandVarAdv msg len (prfDistAdv q S Dist)))).uc

end Functionality

end CatCrypt.Crypto.Constructions.KBKDFPRF
