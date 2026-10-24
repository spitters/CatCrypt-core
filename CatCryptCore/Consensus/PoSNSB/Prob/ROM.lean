/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OracleEval
public import CatCryptCore.Consensus.PoSNSB.Prob.Hash
public import CatCryptCore.Consensus.PoSNSB.Prob.Erasure

/-!
# PoS-NSB: oracle adversaries as queriers

An oracle adversary `A : OracleAdv D R α` determines an adaptive querier in the sense of
`CatCryptCore/Consensus/PoSNSB/Prob/Hash.lean`: given the transcript of the previous queries
and their answers, `A.toQuerier d` replays `A` on the answers of the transcript and returns the
next query of `A`, or the default point `d` when `A` asks no further query. The `k`-th query of
`A.toQuerier d` to `f` is the `k`-th query logged by `OracleAdv.evalOn f A`.

For a protocol with uniform tree types and an oracle adversary `A`, the hash program
`hashProg K` is an oracle program that runs the first `K` phases of the hash-free execution
of `CatCryptCore/Consensus/PoSNSB/Prob/Erasure.lean` against `A.toAdversary`. It queries the
encoding of the genesis block, sends the queries of the adversary calls to the oracle, and
queries the encoding of every block added to the history: one per honest baking step and the
accepted blocks of each corrupt call, at most `m` of them. It keeps a table of the answers to
these queries and computes the chain selection and the hash of the parent block of honest
baking through the table; the locality law `UTreeType.bestChain_local` and the history
invariant make the result agree with the hash function.

## Main definitions

* `OracleAdv.nextQuery d A tr` — the query of `A` after the answers of the transcript `tr`
* `OracleAdv.toQuerier A d` — the querier of `A` with default point `d`
* `logBlocks`, `hRcv`, `hBake`, `hFold`, `hPhase`, `hTrace` — the steps of the hash program
* `hashProg` — the hash program
* `HInv`, `HSim` — the invariant of the hash program and simulation of a hash-free step

## Main results

* `OracleAdv.transcript_toQuerier` — the first `k` transcript entries are the first `k` logged
  queries with their answers
* `OracleAdv.query_toQuerier` — the `k`-th query of `A.toQuerier d` is the `k`-th logged query
* `evalOn_hashProg` — evaluated against `f`, the hash program returns the hash-free state after
  `K` phases
* `encB_mem_hashProg` — the encodings of the genesis block and of the broadcast blocks after
  at most `K` phases are among the logged queries
* `isQueryBound_hashProg` — the hash program asks at most `1 + K * (|IP| * (qc + m + 1))`
  queries for an oracle adversary with `Bounded qc m`
* `collFinder_advantage_oracle_le` — for an oracle adversary with `Bounded qc m`, the collision
  finder against the random function has advantage at most `qT (qT - 1) / 2 / |Hash|` with
  `qT = 1 + K * (|IP| * (qc + m + 1))`
* `pos_nsb_security_rom` — `pos_nsb_security` for an oracle adversary against the random
  function, with this bound as the collision term
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

@[expose] public section

namespace CatCrypt.Crypto

namespace OracleAdv

open CatCryptCore.Consensus.PoSNSB

variable {D R α : Type}

/-- The query of `A` after the answers of the transcript `tr`, with `rand` nodes resolved as in
`evalOn`, or `d` when `A` returns before asking it. -/
noncomputable def nextQuery (d : D) : OracleAdv D R α → List (D × R) → D
  | ret _, _ => d
  | rand p k, tr => nextQuery d (k p.support_nonempty.some) tr
  | query x _, [] => x
  | query _ k, (_, r) :: tr => nextQuery d (k r) tr

/-- The querier of `A` with default point `d`: the next query after a transcript. -/
noncomputable def toQuerier (A : OracleAdv D R α) (d : D) : Querier D R := nextQuery d A

/-- After the first `k` logged queries of `evalOn f A` with their answers, the next query is
the `k`-th logged query. -/
theorem nextQuery_take (d : D) (f : D → R) (A : OracleAdv D R α) (k : ℕ)
    (hk : k < (evalOn f A).2.length) :
    nextQuery d A (((evalOn f A).2.take k).map fun x => (x, f x)) = (evalOn f A).2[k] := by
  induction A generalizing k with
  | ret a => simp at hk
  | rand p g ih => exact ih _ k hk
  | query x g ih =>
    cases k with
    | zero => rfl
    | succ k =>
      simp only [evalOn_query, List.length_cons] at hk
      simp only [evalOn_query, List.take_succ_cons, List.map_cons, List.getElem_cons_succ,
        nextQuery]
      exact ih _ k (by omega)

variable [Fintype D] [DecidableEq D] [Fintype R] [DecidableEq R]

/-- The transcript of the first `k` queries of `A.toQuerier d` to `f` is the list of the first
`k` logged queries of `evalOn f A` with their answers. -/
theorem transcript_toQuerier (A : OracleAdv D R α) (d : D) (f : D → R) (k : ℕ)
    (hk : k ≤ (evalOn f A).2.length) :
    transcript (A.toQuerier d) f k = ((evalOn f A).2.take k).map fun x => (x, f x) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [transcript, ih (by omega), List.take_succ_eq_append_getElem (by omega), List.map_append,
      List.map_singleton]
    simp only [toQuerier, nextQuery_take d f A k (by omega)]

/-- The `k`-th query of `A.toQuerier d` to `f` is the `k`-th query logged by `evalOn f A`. -/
theorem query_toQuerier (A : OracleAdv D R α) (d : D) (f : D → R) (k : ℕ)
    (hk : k < (evalOn f A).2.length) :
    CatCryptCore.Consensus.PoSNSB.query (A.toQuerier d) f k = (evalOn f A).2[k] := by
  rw [CatCryptCore.Consensus.PoSNSB.query, transcript_toQuerier A d f k hk.le]
  exact nextQuery_take d f A k hk

end OracleAdv

end CatCrypt.Crypto

namespace CatCryptCore.Consensus.PoSNSB

open Parameters BlockParameters Corruption Execution
open CatCrypt.Crypto CatCrypt.Crypto.Signatures

/-! ## Recording oracle answers -/

section LogBlocks

variable {Tx Hash : Type} {np Hz : ℕ}

/-- Query the encodings of the blocks `bs` in order and record the answers in the table
`tbl`. -/
def logBlocks [DecidableEq Tx] [DecidableEq Hash] :
    List (Block Tx Hash (Fin np)) → (BlockDom Tx Hash np Hz → Hash) →
      OracleAdv (BlockDom Tx Hash np Hz) Hash (BlockDom Tx Hash np Hz → Hash)
  | [], tbl => .ret tbl
  | b :: bs, tbl => .query (encB Hz b) fun r => logBlocks bs (Function.update tbl (encB Hz b) r)

variable [DecidableEq Tx] [DecidableEq Hash]

/-- `logBlocks bs` queries the encodings of the blocks `bs`. -/
theorem evalOn_logBlocks_snd (f : BlockDom Tx Hash np Hz → Hash)
    (bs : List (Block Tx Hash (Fin np))) (tbl : BlockDom Tx Hash np Hz → Hash) :
    (OracleAdv.evalOn f (logBlocks bs tbl)).2 = bs.map (encB Hz) := by
  induction bs generalizing tbl with
  | nil => rfl
  | cons b bs ih => simp only [logBlocks, OracleAdv.evalOn_query, ih, List.map_cons]

/-- After `logBlocks bs`, the table agrees with `f` at the queried points and wherever it
agreed with `f` before. -/
theorem evalOn_logBlocks_fst (f : BlockDom Tx Hash np Hz → Hash)
    (bs : List (Block Tx Hash (Fin np))) (tbl : BlockDom Tx Hash np Hz → Hash)
    (d : BlockDom Tx Hash np Hz) (hd : d ∈ bs.map (encB Hz) ∨ tbl d = f d) :
    (OracleAdv.evalOn f (logBlocks bs tbl)).1 d = f d := by
  induction bs generalizing tbl with
  | nil => simpa [logBlocks] using hd
  | cons b bs ih =>
    simp only [logBlocks, OracleAdv.evalOn_query]
    apply ih
    by_cases h : d = encB Hz b
    · subst h
      exact Or.inr (Function.update_self _ _ _)
    · rcases hd with hd | hd
      · simp only [List.map_cons, List.mem_cons] at hd
        exact hd.resolve_left h |> Or.inl
      · exact Or.inr ((Function.update_of_ne h _ _).trans hd)

theorem isQueryBound_logBlocks (bs : List (Block Tx Hash (Fin np)))
    (tbl : BlockDom Tx Hash np Hz → Hash) : (logBlocks bs tbl).IsQueryBound bs.length := by
  induction bs generalizing tbl with
  | nil => trivial
  | cons b bs ih => exact fun _ => ih _

end LogBlocks

/-! ## The hash program -/

section HashProg

variable {Tx Hash : Type} [DecidableEq Tx] [DecidableEq Hash] {np : ℕ} [Corruption (Fin np)]
  {n Hz : ℕ} {PK SK Sig : Type}
  (Sch : PSigScheme (Block Tx Hash (Fin np)) PK SK Sig) [Sch.Deterministic]
  (IP : List (Fin np)) (h0 : Fin np) (GB : Block Tx Hash (Fin np))
  (U : (L : Fin n → Option (Fin np)) → Fin np →
    @UTreeType Tx Hash (Fin np) (leaderParams IP h0 L) GB)
  (txSel : Slot → Fin np → Tx) (L : Fin n → Option (Fin np)) (ks : Fin np → PK × SK)
  (A : OAdversary Tx Hash np n Hz PK Sig) (m : ℕ)

/-- The states of the hash program: a hash-free state of the execution of `A.toAdversary` and
a table of oracle answers. -/
abbrev HState := XS IP h0 GB U L A.toAdversary × (BlockDom Tx Hash np Hz → Hash)

/-- The receiving step of party `p` in the hash program. An honest party adds the fetched
blocks to its tree; for a corrupt party the oracle adversary `A.rcv` runs with its queries
sent to the oracle, and the encodings of the first `m` blocks the network accepts are queried
and recorded in the table. -/
def hRcv (p : Fin np) (s : HState IP h0 GB U L A) :
    OracleAdv (BlockDom Tx Hash np Hz) Hash (HState IP h0 GB U L A) :=
  letI := leaderParams IP h0 L
  match s.1.trees p with
  | some t =>
    if !is_corrupt p then
      .ret ((s.1.fetch p).2.updTree p
        ((s.1.fetch p).1.foldr (fun msg t => (U L p).extendTree t (get_block msg)) t), s.2)
    else
      (A.rcv (L, fun j => (ks j).1) (s.1.fetch p).1 (s.1.fetch p).2.t_now
          (s.1.fetch p).2.history (sigTable Sch ks (s.1.fetch p).2.history)
          (s.1.fetch p).2.msg_buff (s.1.fetch p).2.adv_state).bind fun o =>
        (logBlocks (((outFilter Sch false (fun j => (ks j).1) (s.1.fetch p).2.t_now
            (s.1.fetch p).2.history o.1).map fun y => get_block y.1).take m) s.2).bind
          fun tbl =>
            .ret ({ (s.1.fetch p).2.floodsAdv (outFilter Sch false (fun j => (ks j).1)
              (s.1.fetch p).2.t_now (s.1.fetch p).2.history o.1) with adv_state := o.2 }, tbl)
  | none => .ret s

/-- The baking step of party `p` in the hash program. An honest winner selects its chain and
the hash of its parent through the table, then queries and records the encoding of its new
block; for a corrupt party the oracle adversary `A.bake` runs with its queries sent to the
oracle, and the encodings of the first `m` blocks the network accepts are queried and
recorded in the table. -/
def hBake (p : Fin np) (s : HState IP h0 GB U L A) :
    OracleAdv (BlockDom Tx Hash np Hz) Hash (HState IP h0 GB U L A) :=
  letI := leaderParams IP h0 L
  match s.1.trees p with
  | some t =>
    if !is_corrupt p then
      if Winner p s.1.t_now then
        .query (encB Hz (⟨s.1.t_now, txSel s.1.t_now p, s.2 (encB Hz
            (((U L p).bestChain (fun b => s.2 (encB Hz b)) (s.1.t_now - 1) t).headD GB)), p⟩ :
              Block Tx Hash (Fin np))) fun r =>
          .ret ((s.1.updTree p ((U L p).extendTree t ⟨s.1.t_now, txSel s.1.t_now p, s.2 (encB Hz
            (((U L p).bestChain (fun b => s.2 (encB Hz b)) (s.1.t_now - 1) t).headD GB)),
              p⟩)).floods
              [Message.BlockMsg ⟨s.1.t_now, txSel s.1.t_now p, s.2 (encB Hz
                (((U L p).bestChain (fun b => s.2 (encB Hz b)) (s.1.t_now - 1) t).headD GB)), p⟩],
            Function.update s.2 (encB Hz ⟨s.1.t_now, txSel s.1.t_now p, s.2 (encB Hz
              (((U L p).bestChain (fun b => s.2 (encB Hz b)) (s.1.t_now - 1) t).headD GB)), p⟩) r)
      else .ret ((s.1.updTree p t).floods [], s.2)
    else
      (A.bake (L, fun j => (ks j).1) s.1.t_now s.1.history (sigTable Sch ks s.1.history)
          s.1.msg_buff s.1.adv_state).bind fun o =>
        (logBlocks (((outFilter Sch false (fun j => (ks j).1) s.1.t_now s.1.history o.1).map
            fun y => get_block y.1).take m) s.2).bind fun tbl =>
          .ret ({ s.1.floodsAdv (outFilter Sch false (fun j => (ks j).1) s.1.t_now s.1.history
            o.1) with adv_state := o.2 }, tbl)
  | none => .ret s

/-- The steps `step` of a list of parties, in the order of `List.foldr`. -/
def hFold {S : Type} (step : Fin np → S → OracleAdv (BlockDom Tx Hash np Hz) Hash S) :
    List (Fin np) → S → OracleAdv (BlockDom Tx Hash np Hz) Hash S
  | [], s => .ret s
  | p :: ps, s => (hFold step ps s).bind (step p)

/-- One phase of the hash program: the receiving or the baking steps of the initial parties,
or the end of the round. -/
def hPhase (s : HState IP h0 GB U L A) :
    OracleAdv (BlockDom Tx Hash np Hz) Hash (HState IP h0 GB U L A) :=
  match s.1.progress with
  | .Ready => (hFold (hRcv Sch IP h0 GB U L ks A m) IP s).bind fun s' =>
      .ret ({ s'.1 with progress := .Delivered }, s'.2)
  | .Delivered => (hFold (hBake Sch IP h0 GB U txSel L ks A m) IP s).bind fun s' =>
      .ret ({ s'.1 with progress := .Baked }, s'.2)
  | .Baked => .ret ({ s.1.tick with progress := .Ready }, s.2)

/-- The first `j` phases of the hash program, after the query of the genesis block, whose
answer initialises the table. -/
noncomputable def hTrace : ℕ → OracleAdv (BlockDom Tx Hash np Hz) Hash (HState IP h0 GB U L A)
  | 0 => .query (encB Hz GB) fun r => .ret (x₀ IP h0 GB U L A.toAdversary, fun _ => r)
  | j + 1 => (hTrace j).bind (hPhase Sch IP h0 GB U txSel L ks A m)

/-- **The hash program.** The oracle program that runs the first `K` phases of the hash-free
execution of the uniform protocol against `A.toAdversary`, with every query of the adversary
sent to the oracle, and queries the encodings of the genesis block and of every block added
to the history (for a corrupt call, of the first `m` accepted blocks). It returns the
hash-free state after `K` phases. -/
noncomputable def hashProg (K : ℕ) :
    OracleAdv (BlockDom Tx Hash np Hz) Hash (XS IP h0 GB U L A.toAdversary) :=
  (hTrace Sch IP h0 GB U txSel L ks A m K).bind fun s => .ret s.1

/-! ### The query bound -/

section Bound

variable {qc : ℕ}

theorem isQueryBound_hRcv
    (hq : ∀ pub ms sl hist tbl mb st, (A.rcv pub ms sl hist tbl mb st).IsQueryBound qc)
    (p : Fin np) (s : HState IP h0 GB U L A) :
    (hRcv Sch IP h0 GB U L ks A m p s).IsQueryBound (qc + m) := by
  unfold hRcv
  split
  · split
    · trivial
    · refine OracleAdv.isQueryBound_bind (hq _ _ _ _ _ _ _) fun o => ?_
      refine (OracleAdv.isQueryBound_bind (n := 0) (isQueryBound_logBlocks _ _)
        fun _ => by trivial).mono ?_
      simp
  · trivial

theorem isQueryBound_hBake
    (hq : ∀ pub sl hist tbl mb st, (A.bake pub sl hist tbl mb st).IsQueryBound qc)
    (p : Fin np) (s : HState IP h0 GB U L A) :
    (hBake Sch IP h0 GB U txSel L ks A m p s).IsQueryBound (qc + m + 1) := by
  unfold hBake
  split
  · split
    · split
      · exact fun _ => trivial
      · trivial
    · refine (OracleAdv.isQueryBound_bind (n := m) (hq _ _ _ _ _ _) fun o => ?_).mono
        (by omega)
      refine (OracleAdv.isQueryBound_bind (n := 0) (isQueryBound_logBlocks _ _)
        fun _ => by trivial).mono ?_
      simp
  · trivial

theorem isQueryBound_hFold {S : Type}
    {step : Fin np → S → OracleAdv (BlockDom Tx Hash np Hz) Hash S} {c : ℕ}
    (h : ∀ p s, (step p s).IsQueryBound c) (l : List (Fin np)) (s : S) :
    (hFold step l s).IsQueryBound (l.length * c) := by
  induction l with
  | nil => trivial
  | cons p ps ih =>
    refine (OracleAdv.isQueryBound_bind ih (h p)).mono ?_
    rw [List.length_cons, Nat.succ_mul]

theorem isQueryBound_hPhase
    (hb : ∀ pub sl hist tbl mb st, (A.bake pub sl hist tbl mb st).IsQueryBound qc)
    (hr : ∀ pub ms sl hist tbl mb st, (A.rcv pub ms sl hist tbl mb st).IsQueryBound qc)
    (s : HState IP h0 GB U L A) :
    (hPhase Sch IP h0 GB U txSel L ks A m s).IsQueryBound (IP.length * (qc + m + 1)) := by
  unfold hPhase
  split
  · exact (OracleAdv.isQueryBound_bind (n := 0) (isQueryBound_hFold
      (fun p s => (isQueryBound_hRcv Sch IP h0 GB U L ks A m hr p s).mono
        (n := qc + m + 1) (by omega)) IP s)
      fun _ => by trivial).mono (by omega)
  · exact (OracleAdv.isQueryBound_bind (n := 0) (isQueryBound_hFold
      (isQueryBound_hBake Sch IP h0 GB U txSel L ks A m hb) IP s)
      fun _ => by trivial).mono (by omega)
  · trivial

theorem isQueryBound_hTrace
    (hb : ∀ pub sl hist tbl mb st, (A.bake pub sl hist tbl mb st).IsQueryBound qc)
    (hr : ∀ pub ms sl hist tbl mb st, (A.rcv pub ms sl hist tbl mb st).IsQueryBound qc)
    (j : ℕ) :
    (hTrace Sch IP h0 GB U txSel L ks A m j).IsQueryBound
      (1 + j * (IP.length * (qc + m + 1))) := by
  induction j with
  | zero => exact OracleAdv.IsQueryBound.mono (m := 1) (fun _ => trivial) (by simp)
  | succ j ih =>
    refine (OracleAdv.isQueryBound_bind ih
      (isQueryBound_hPhase Sch IP h0 GB U txSel L ks A m hb hr)).mono (le_of_eq ?_)
    ring

/-- **The query bound of the hash program.** For an oracle adversary whose calls ask at most
`qc` queries and output at most `m` messages, the hash program for `K` phases asks at most
`1 + K * (|IP| * (qc + m + 1))` queries. -/
theorem isQueryBound_hashProg (hA : A.Bounded qc m) (K : ℕ) :
    (hashProg Sch IP h0 GB U txSel L ks A m K).IsQueryBound
      (1 + K * (IP.length * (qc + m + 1))) :=
  (OracleAdv.isQueryBound_bind (n := 0)
    (isQueryBound_hTrace Sch IP h0 GB U txSel L ks A m hA.1.1 hA.1.2 K)
    fun _ => by trivial).mono (by omega)

end Bound

/-! ### The evaluation of the hash program -/

section Eval

/-- The invariant of the hash program at the hash-free state `x` with the table `tbl`, for
the oracle `f`: the history invariant holds, and the table agrees with `f` at the encodings
of the genesis block and of the blocks of the history. -/
structure HInv (f : BlockDom Tx Hash np Hz → Hash) (x : XS IP h0 GB U L A.toAdversary)
    (tbl : BlockDom Tx Hash np Hz → Hash) : Prop where
  hist : XSt.HistInv IP h0 GB U L A.toAdversary x
  tbl : ∀ b ∈ GB :: x.history.map get_block, tbl (encB Hz b) = f (encB Hz b)

/-- The program `prog` simulates the hash-free step `g` against the oracle `f`: from a state
with the invariant, its evaluation returns `g x` with a table satisfying the invariant, and
every block of the history of `g x` is in the history of `x` or has its encoding queried. -/
def HSim (f : BlockDom Tx Hash np Hz → Hash)
    (g : XS IP h0 GB U L A.toAdversary → XS IP h0 GB U L A.toAdversary)
    (prog : HState IP h0 GB U L A →
      OracleAdv (BlockDom Tx Hash np Hz) Hash (HState IP h0 GB U L A)) : Prop :=
  ∀ x tbl, HInv IP h0 GB U L A f x tbl →
    (OracleAdv.evalOn f (prog (x, tbl))).1.1 = g x ∧
    HInv IP h0 GB U L A f (g x) (OracleAdv.evalOn f (prog (x, tbl))).1.2 ∧
    ∀ b ∈ (g x).history.map get_block,
      b ∈ x.history.map get_block ∨ encB Hz b ∈ (OracleAdv.evalOn f (prog (x, tbl))).2

variable {IP h0 GB U L A} in
theorem HSim.bind {f : BlockDom Tx Hash np Hz → Hash}
    {g g' : XS IP h0 GB U L A.toAdversary → XS IP h0 GB U L A.toAdversary}
    {P P' : HState IP h0 GB U L A →
      OracleAdv (BlockDom Tx Hash np Hz) Hash (HState IP h0 GB U L A)}
    (h : HSim IP h0 GB U L A f g P) (h' : HSim IP h0 GB U L A f g' P') :
    HSim IP h0 GB U L A f (fun x => g' (g x)) (fun s => (P s).bind P') := by
  intro x tbl hI
  obtain ⟨h1, h2, h3⟩ := h x tbl hI
  have e : (OracleAdv.evalOn f (P (x, tbl))).1 = (g x, (OracleAdv.evalOn f (P (x, tbl))).1.2) :=
    Prod.ext h1 rfl
  obtain ⟨h1', h2', h3'⟩ := h' (g x) _ h2
  rw [OracleAdv.evalOn_bind, e]
  refine ⟨h1', h2', fun b hb => ?_⟩
  rcases h3' b hb with hb | hb
  · rcases h3 b hb with hb | hb
    · exact Or.inl hb
    · exact Or.inr (List.mem_append_left _ hb)
  · exact Or.inr (List.mem_append_right _ hb)

variable {IP h0 GB U L A} in
theorem HSim.ret {f : BlockDom Tx Hash np Hz → Hash}
    {g : XS IP h0 GB U L A.toAdversary → XS IP h0 GB U L A.toAdversary}
    (h : ∀ x tbl, HInv IP h0 GB U L A f x tbl → HInv IP h0 GB U L A f (g x) tbl)
    (hh : ∀ x, (g x).history = x.history) :
    HSim IP h0 GB U L A f g fun s => .ret (g s.1, s.2) :=
  fun x tbl hI => ⟨rfl, h x tbl hI, fun _ hb => Or.inl (hh x ▸ hb)⟩

variable {IP h0 GB U L A} in
theorem hsim_hFold {f : BlockDom Tx Hash np Hz → Hash}
    {g : Fin np → XS IP h0 GB U L A.toAdversary → XS IP h0 GB U L A.toAdversary}
    {step : Fin np → HState IP h0 GB U L A →
      OracleAdv (BlockDom Tx Hash np Hz) Hash (HState IP h0 GB U L A)}
    (h : ∀ p, HSim IP h0 GB U L A f (g p) (step p)) (l : List (Fin np)) :
    HSim IP h0 GB U L A f (fun x => l.foldr g x) (hFold step l) := by
  induction l with
  | nil => exact fun _ _ hI => ⟨rfl, hI, fun _ hb => Or.inl hb⟩
  | cons p ps ih => exact HSim.bind ih (h p)

theorem histInv_xRcv (f : BlockDom Tx Hash np Hz → Hash) (p : Fin np)
    (x : XS IP h0 GB U L A.toAdversary) (h : XSt.HistInv IP h0 GB U L A.toAdversary x) :
    XSt.HistInv IP h0 GB U L A.toAdversary
      (xRcv Sch IP h0 GB U txSel L ks A.toAdversary false f p x) := by
  have := (histInv_emb_iff IP h0 GB U txSel L ks A.toAdversary f x).2 h
  rw [← histInv_emb_iff IP h0 GB U txSel L ks A.toAdversary f, ← sRcv_emb]
  let _ := leaderParams IP h0 L
  let _ : BlockParameters Tx Hash (Fin np) := ⟨GB, fun b => f (encB Hz b)⟩
  let _ := mkExec Sch false (Protocol.ofUniform (Hz := Hz) IP h0 GB U txSel) (uSeed L ks f)
    A.toAdversary
  exact this.rcv p

theorem histInv_xBake (f : BlockDom Tx Hash np Hz → Hash) (p : Fin np)
    (x : XS IP h0 GB U L A.toAdversary) (h : XSt.HistInv IP h0 GB U L A.toAdversary x) :
    XSt.HistInv IP h0 GB U L A.toAdversary
      (xBake Sch IP h0 GB U txSel L ks A.toAdversary false f p x) := by
  have := (histInv_emb_iff IP h0 GB U txSel L ks A.toAdversary f x).2 h
  rw [← histInv_emb_iff IP h0 GB U txSel L ks A.toAdversary f, ← sBake_emb]
  let _ := leaderParams IP h0 L
  let _ : BlockParameters Tx Hash (Fin np) := ⟨GB, fun b => f (encB Hz b)⟩
  let _ := mkExec Sch false (Protocol.ofUniform (Hz := Hz) IP h0 GB U txSel) (uSeed L ks f)
    A.toAdversary
  exact this.bake p

theorem XSt.history_floodsAdv {T : Fin np → Type} {S : Type}
    (msgs : List (Message Tx Hash (Fin np) × DelayMap (Fin np))) (x : XSt Tx Hash np T S) :
    (x.floodsAdv msgs).history = msgs.map Prod.fst ++ x.history := by
  induction msgs with
  | nil => rfl
  | cons m ms ih => exact congrArg (m.1 :: ·) ih

/-- A corrupt step that broadcasts the accepted messages `out` from a state `y` with the
history of `x`, then records the first `m` accepted blocks, keeps the invariant and logs every
new block of the history, when at most `m` messages are accepted. -/
theorem hInv_corrupt (f : BlockDom Tx Hash np Hz → Hash) (x y : XS IP h0 GB U L A.toAdversary)
    (tbl : BlockDom Tx Hash np Hz → Hash)
    (out : List (Message Tx Hash (Fin np) × DelayMap (Fin np))) (st' : A.AdvState)
    (Q : List (BlockDom Tx Hash np Hz)) (hI : HInv IP h0 GB U L A f x tbl)
    (hy : y.history = x.history) (hlen : out.length ≤ m)
    (hH : XSt.HistInv IP h0 GB U L A.toAdversary { y.floodsAdv out with adv_state := st' }) :
    HInv IP h0 GB U L A f { y.floodsAdv out with adv_state := st' }
        (OracleAdv.evalOn f (logBlocks ((out.map fun z => get_block z.1).take m) tbl)).1 ∧
      ∀ b ∈ (y.floodsAdv out).history.map get_block, b ∈ x.history.map get_block ∨
        encB Hz b ∈ Q ++ ((OracleAdv.evalOn f
          (logBlocks ((out.map fun z => get_block z.1).take m) tbl)).2 ++ []) := by
  have htake : (out.map fun z => get_block z.1).take m = out.map fun z => get_block z.1 :=
    List.take_of_length_le (by simpa using hlen)
  rw [htake]
  have hmem : ∀ b ∈ (y.floodsAdv out).history.map get_block,
      b ∈ x.history.map get_block ∨ b ∈ out.map fun z => get_block z.1 := by
    intro b hb
    rw [XSt.history_floodsAdv, hy, List.map_append, List.map_map, List.mem_append] at hb
    exact hb.symm
  refine ⟨⟨hH, fun b hb => ?_⟩, fun b hb => ?_⟩
  · apply evalOn_logBlocks_fst
    rcases List.mem_cons.1 hb with rfl | hb
    · exact Or.inr (hI.tbl _ List.mem_cons_self)
    · rcases hmem b hb with hb | hb
      · exact Or.inr (hI.tbl _ (List.mem_cons_of_mem _ hb))
      · exact Or.inl (List.mem_map_of_mem hb)
  · rcases hmem b hb with hb | hb
    · exact Or.inl hb
    · refine Or.inr (List.mem_append_right _ ?_)
      rw [List.append_nil, evalOn_logBlocks_snd]
      exact List.mem_map_of_mem hb

theorem hsim_hRcv (hA : A.toAdversary.OutputBound m) (f : BlockDom Tx Hash np Hz → Hash)
    (p : Fin np) :
    HSim IP h0 GB U L A f (xRcv Sch IP h0 GB U txSel L ks A.toAdversary false f p)
      (hRcv Sch IP h0 GB U L ks A m p) := by
  intro x tbl hI
  have hH := histInv_xRcv Sch IP h0 GB U txSel L ks A f p x hI.hist
  revert hH
  cases ht : x.trees p with
  | none =>
    intro _
    simp only [hRcv, xRcv, XSt.rcv, ht]
    exact ⟨rfl, hI, fun _ hb => Or.inl hb⟩
  | some t =>
    cases hc : is_corrupt p
    · intro hH
      simp only [hRcv, xRcv, XSt.rcv, ht, hc] at hH ⊢
      exact ⟨rfl, ⟨hH, hI.tbl⟩, fun _ hb => Or.inl hb⟩
    · intro hH
      simp only [hRcv, xRcv, XSt.rcv, ht, hc, Bool.not_true, Bool.false_eq_true, ite_false,
        OracleAdv.evalOn_bind, OracleAdv.evalOn_ret] at hH ⊢
      exact ⟨rfl, hInv_corrupt IP h0 GB U L A m f x _ tbl _ _ _ hI rfl
        ((outFilter_length_le _ _ _ _ _ _).trans
          (hA.2 (L, f, fun j => (ks j).1) _ _ _ _ _ _)) hH⟩

/-- An honest baking step that broadcasts the block `b₀` and records the answer at its
encoding keeps the invariant and logs the new block of the history. -/
theorem hInv_honestBake (f : BlockDom Tx Hash np Hz → Hash) (x : XS IP h0 GB U L A.toAdversary)
    (tbl : BlockDom Tx Hash np Hz → Hash) (p : Fin np)
    (t' : @UTreeType.T Tx Hash (Fin np) (leaderParams IP h0 L) GB (U L p))
    (b₀ : Block Tx Hash (Fin np)) (hI : HInv IP h0 GB U L A f x tbl)
    (hH : XSt.HistInv IP h0 GB U L A.toAdversary
      ((x.updTree p t').floods [Message.BlockMsg b₀])) :
    HInv IP h0 GB U L A f ((x.updTree p t').floods [Message.BlockMsg b₀])
        (Function.update tbl (encB Hz b₀) (f (encB Hz b₀))) ∧
      ∀ b ∈ ((x.updTree p t').floods [Message.BlockMsg b₀]).history.map get_block,
        b ∈ x.history.map get_block ∨ encB Hz b ∈ [encB Hz b₀] := by
  have hmem : ∀ b ∈ ((x.updTree p t').floods [Message.BlockMsg b₀]).history.map get_block,
      b = b₀ ∨ b ∈ x.history.map get_block := fun b hb => List.mem_cons.1 hb
  refine ⟨⟨hH, fun b hb => ?_⟩, fun b hb => ?_⟩
  · by_cases h : encB Hz b = encB Hz b₀
    · rw [h, Function.update_self]
    · rw [Function.update_of_ne h]
      rcases List.mem_cons.1 hb with rfl | hb
      · exact hI.tbl _ List.mem_cons_self
      · rcases hmem b hb with rfl | hb
        · exact absurd rfl h
        · exact hI.tbl _ (List.mem_cons_of_mem _ hb)
  · rcases hmem b hb with rfl | hb
    · exact Or.inr List.mem_cons_self
    · exact Or.inl hb

theorem hsim_hBake (hA : A.toAdversary.OutputBound m) (f : BlockDom Tx Hash np Hz → Hash)
    (p : Fin np) :
    HSim IP h0 GB U L A f (xBake Sch IP h0 GB U txSel L ks A.toAdversary false f p)
      (hBake Sch IP h0 GB U txSel L ks A m p) := by
  let _ := leaderParams IP h0 L
  intro x tbl hI
  have hH := histInv_xBake Sch IP h0 GB U txSel L ks A f p x hI.hist
  revert hH
  cases ht : x.trees p with
  | none =>
    intro _
    simp only [hBake, xBake, XSt.bake, ht]
    exact ⟨rfl, hI, fun _ hb => Or.inl hb⟩
  | some t =>
    cases hc : is_corrupt p
    · by_cases hw : Winner p x.t_now = true
      · have hloc : ∀ b ∈ (U L p).allBlocks t, tbl (encB Hz b) = f (encB Hz b) :=
          fun b hb => hI.tbl b (hI.hist.state p t ht b hb)
        have hbest := (U L p).bestChain_local (fun b => tbl (encB Hz b))
          (fun b => f (encB Hz b)) (x.t_now - 1) t hloc
        have hhead : tbl (encB Hz (((U L p).bestChain (fun b => f (encB Hz b)) (x.t_now - 1)
            t).headD GB)) = f (encB Hz (((U L p).bestChain (fun b => f (encB Hz b))
              (x.t_now - 1) t).headD GB)) := by
          cases hcb : (U L p).bestChain (fun b => f (encB Hz b)) (x.t_now - 1) t with
          | nil => exact hI.tbl GB List.mem_cons_self
          | cons b bs =>
            have hb := (U L p).best_chain_in_all _ (x.t_now - 1) t b (by rw [hcb]; simp)
            exact hloc b (List.mem_filter.1 hb).1
        intro hH
        simp only [hBake, xBake, XSt.bake, ht, hc, hw, hbest, hhead, Bool.not_false, ite_true,
          OracleAdv.evalOn_query, OracleAdv.evalOn_ret] at hH ⊢
        exact ⟨trivial, hInv_honestBake IP h0 GB U L A f x tbl p _ _ hI hH⟩
      · intro hH
        simp only [hBake, xBake, XSt.bake, ht, hc, hw, Bool.not_false, ite_true] at hH ⊢
        exact ⟨rfl, ⟨hH, hI.tbl⟩, fun _ hb => Or.inl hb⟩
    · intro hH
      simp only [hBake, xBake, XSt.bake, ht, hc, Bool.not_true, Bool.false_eq_true, ite_false,
        OracleAdv.evalOn_bind, OracleAdv.evalOn_ret] at hH ⊢
      exact ⟨rfl, hInv_corrupt IP h0 GB U L A m f x _ tbl _ _ _ hI rfl
        ((outFilter_length_le _ _ _ _ _ _).trans
          (hA.1 (L, f, fun j => (ks j).1) _ _ _ _ _)) hH⟩

/-- From a state with the invariant whose execution order is `IP`, a phase of the hash
program simulates the hash-free phase. -/
theorem hPhase_spec (hA : A.toAdversary.OutputBound m) (f : BlockDom Tx Hash np Hz → Hash)
    (x : XS IP h0 GB U L A.toAdversary) (tbl : BlockDom Tx Hash np Hz → Hash)
    (hI : HInv IP h0 GB U L A f x tbl) (ho : x.exec_order = IP) :
    (OracleAdv.evalOn f (hPhase Sch IP h0 GB U txSel L ks A m (x, tbl))).1.1 =
        xPhase Sch IP h0 GB U txSel L ks A.toAdversary false f x ∧
      HInv IP h0 GB U L A f (xPhase Sch IP h0 GB U txSel L ks A.toAdversary false f x)
        (OracleAdv.evalOn f (hPhase Sch IP h0 GB U txSel L ks A m (x, tbl))).1.2 ∧
      ∀ b ∈ (xPhase Sch IP h0 GB U txSel L ks A.toAdversary false f x).history.map get_block,
        b ∈ x.history.map get_block ∨
          encB Hz b ∈ (OracleAdv.evalOn f (hPhase Sch IP h0 GB U txSel L ks A m (x, tbl))).2 := by
  obtain ⟨t_now, mb, trees, hist, st, ord, prog⟩ := x
  simp only at ho
  subst ord
  cases prog with
  | Ready =>
    exact HSim.bind (hsim_hFold (hsim_hRcv Sch IP h0 GB U txSel L ks A m hA f) IP)
      (HSim.ret (g := fun y => { y with progress := .Delivered })
        (fun _ _ h => ⟨⟨h.hist.buff, h.hist.state⟩, h.tbl⟩) fun _ => rfl) _ tbl hI
  | Delivered =>
    exact HSim.bind (hsim_hFold (hsim_hBake Sch IP h0 GB U txSel L ks A m hA f) IP)
      (HSim.ret (g := fun y => { y with progress := .Baked })
        (fun _ _ h => ⟨⟨h.hist.buff, h.hist.state⟩, h.tbl⟩) fun _ => rfl) _ tbl hI
  | Baked =>
    refine HSim.ret (g := fun y => { y.tick with progress := .Ready })
      (fun _ _ h => ⟨⟨fun mt hmt => ?_, h.hist.state⟩, h.tbl⟩) (fun _ => rfl) _ tbl hI
    obtain ⟨mt', hmt', rfl⟩ := List.mem_map.1 hmt
    exact h.hist.buff mt' hmt'

include Sch txSel ks in
/-- The hash-free initial state satisfies the invariant with the table answering every point
by the answer at the genesis block. -/
theorem hInv_x₀ (f : BlockDom Tx Hash np Hz → Hash) :
    HInv IP h0 GB U L A f (x₀ IP h0 GB U L A.toAdversary) fun _ => f (encB Hz GB) := by
  refine ⟨?_, fun b hb => ?_⟩
  · rw [← histInv_emb_iff IP h0 GB U txSel L ks A.toAdversary f,
      ← N0_eq_emb Sch IP h0 GB U txSel L ks A.toAdversary false f]
    let _ := leaderParams IP h0 L
    let _ : BlockParameters Tx Hash (Fin np) := ⟨GB, fun b => f (encB Hz b)⟩
    let _ := mkExec Sch false (Protocol.ofUniform (Hz := Hz) IP h0 GB U txSel) (uSeed L ks f)
      A.toAdversary
    exact hist_inv_N0
  · have : b = GB := by simpa [x₀] using hb
    rw [this]

/-- After `j` phases, the hash program has computed the hash-free state after `j` phases with
a table satisfying the invariant, and has queried the encodings of the genesis block and of
every block of the history of the hash-free states after at most `j` phases. -/
theorem hTrace_spec (hA : A.toAdversary.OutputBound m) (f : BlockDom Tx Hash np Hz → Hash)
    (j : ℕ) :
    (OracleAdv.evalOn f (hTrace Sch IP h0 GB U txSel L ks A m j)).1.1 =
        (xPhase Sch IP h0 GB U txSel L ks A.toAdversary false f)^[j]
          (x₀ IP h0 GB U L A.toAdversary) ∧
      HInv IP h0 GB U L A f ((xPhase Sch IP h0 GB U txSel L ks A.toAdversary false f)^[j]
          (x₀ IP h0 GB U L A.toAdversary))
        (OracleAdv.evalOn f (hTrace Sch IP h0 GB U txSel L ks A m j)).1.2 ∧
      ∀ i ≤ j, ∀ b ∈ GB :: ((xPhase Sch IP h0 GB U txSel L ks A.toAdversary false f)^[i]
          (x₀ IP h0 GB U L A.toAdversary)).history.map get_block,
        encB Hz b ∈ (OracleAdv.evalOn f (hTrace Sch IP h0 GB U txSel L ks A m j)).2 := by
  induction j with
  | zero =>
    refine ⟨rfl, hInv_x₀ Sch IP h0 GB U txSel L ks A f, fun i hi b hb => ?_⟩
    obtain rfl : i = 0 := by omega
    have : b = GB := by simpa [x₀] using hb
    rw [this]
    exact List.mem_cons_self
  | succ j ih =>
    obtain ⟨h1, h2, h3⟩ := ih
    have ho : ((xPhase Sch IP h0 GB U txSel L ks A.toAdversary false f)^[j]
        (x₀ IP h0 GB U L A.toAdversary)).exec_order = IP := by
      have := (histBound_sTrace Sch (Protocol.ofUniform (Hz := Hz) IP h0 GB U txSel)
        A.toAdversary (uSeed L ks f) hA j).1
      rw [sTrace_eq_emb] at this
      exact this
    have e : (OracleAdv.evalOn f (hTrace Sch IP h0 GB U txSel L ks A m j)).1 =
        ((xPhase Sch IP h0 GB U txSel L ks A.toAdversary false f)^[j]
          (x₀ IP h0 GB U L A.toAdversary),
          (OracleAdv.evalOn f (hTrace Sch IP h0 GB U txSel L ks A m j)).1.2) := Prod.ext h1 rfl
    obtain ⟨p1, p2, p3⟩ := hPhase_spec Sch IP h0 GB U txSel L ks A m hA f _ _ h2 ho
    simp only [hTrace, OracleAdv.evalOn_bind, Function.iterate_succ_apply']
    rw [e]
    refine ⟨p1, p2, fun i hi b hb => ?_⟩
    rcases Nat.lt_or_eq_of_le hi with hi | rfl
    · exact List.mem_append_left _ (h3 i (by omega) b hb)
    · rw [Function.iterate_succ_apply'] at hb
      rcases List.mem_cons.1 hb with rfl | hb
      · exact List.mem_append_left _ (h3 0 (by omega) _ List.mem_cons_self)
      · rcases p3 b hb with hb | hb
        · exact List.mem_append_left _ (h3 _ le_rfl b (List.mem_cons_of_mem _ hb))
        · exact List.mem_append_right _ hb

/-- **The evaluation of the hash program.** Evaluated against the oracle `f`, the hash program
returns the hash-free state of the real execution after `K` phases. -/
theorem evalOn_hashProg (hA : A.toAdversary.OutputBound m) (f : BlockDom Tx Hash np Hz → Hash)
    (K : ℕ) :
    (OracleAdv.evalOn f (hashProg Sch IP h0 GB U txSel L ks A m K)).1 =
      (xPhase Sch IP h0 GB U txSel L ks A.toAdversary false f)^[K]
        (x₀ IP h0 GB U L A.toAdversary) := by
  simp only [hashProg, OracleAdv.evalOn_bind, OracleAdv.evalOn_ret]
  exact (hTrace_spec Sch IP h0 GB U txSel L ks A m hA f K).1

/-- **The hash program logs the history.** Evaluated against the oracle `f`, the hash program
for `K` phases queries the encoding of the genesis block and of every broadcast block of the
real execution after at most `K` phases. -/
theorem encB_mem_hashProg (hA : A.toAdversary.OutputBound m) (f : BlockDom Tx Hash np Hz → Hash)
    {K j : ℕ} (hj : j ≤ K) :
    letI := leaderParams IP h0 L
    letI : BlockParameters Tx Hash (Fin np) := ⟨GB, fun b => f (encB Hz b)⟩
    ∀ b ∈ block_hist_gb (sTrace Sch (Protocol.ofUniform (Hz := Hz) IP h0 GB U txSel)
        (uSeed L ks f) A.toAdversary false j),
      encB Hz b ∈ (OracleAdv.evalOn f (hashProg Sch IP h0 GB U txSel L ks A m K)).2 := by
  intro b hb
  rw [sTrace_eq_emb] at hb
  simp only [hashProg, OracleAdv.evalOn_bind, OracleAdv.evalOn_ret, List.append_nil]
  exact (hTrace_spec Sch IP h0 GB U txSel L ks A m hA f K).2.2 j hj b hb

end Eval

end HashProg

/-! ### The collision term in the random-oracle model -/

section ROMBound

open CatCrypt.Crypto.Assumptions
open scoped ENNReal

variable {Tx Hash : Type} [DecidableEq Tx] [DecidableEq Hash] {np : ℕ} [Corruption (Fin np)]
  {n Hz : ℕ} {PK SK Sig : Type}
  (Sch : PSigScheme (Block Tx Hash (Fin np)) PK SK Sig) [Sch.Deterministic]
  (IP : List (Fin np)) (h0 : Fin np) (GB : Block Tx Hash (Fin np))
  (U : (L : Fin n → Option (Fin np)) → Fin np →
    @UTreeType Tx Hash (Fin np) (leaderParams IP h0 L) GB)
  (txSel : Slot → Fin np → Tx) (A : OAdversary Tx Hash np n Hz PK Sig) {qc m : ℕ}

/-- **The collision term for an oracle adversary.** For a protocol with uniform tree types and
an oracle adversary `A` whose calls ask at most `qc` queries and output at most `m` messages,
the collision finder of the first `K` phases of the execution of `A.toAdversary` against the
random function `HashScheme.randomFun` with the identity codec has collision-search advantage
at most the birthday bound `qT (qT - 1) / 2 / |Hash|` with `qT = 1 + K (|IP| (qc + m + 1))`,
the query bound of the hash program `hashProg`. -/
theorem collFinder_advantage_oracle_le [Fintype Tx] [Fintype Hash] [Nonempty Hash]
    (hA : A.Bounded qc m) (μ : PMF (Option (Fin np))) (W K : ℕ) :
    CR_Search_Advantage (HashScheme.randomFun (BlockDom Tx Hash np Hz) Hash)
        (collFinder Sch (Protocol.ofUniform (Hz := Hz) IP h0 GB U txSel) A.toAdversary
          (HashScheme.randomFun (BlockDom Tx Hash np Hz) Hash) (HashScheme.Codec.id _) μ W K) ≤
      (((1 + K * (IP.length * (qc + m + 1))) * (1 + K * (IP.length * (qc + m + 1)) - 1) / 2 :
        ℕ) : ℝ≥0∞) / Fintype.card Hash := by
  set qT := 1 + K * (IP.length * (qc + m + 1))
  let next : (Fin n → Option (Fin np)) → (Fin np → PK × SK) →
      Querier (BlockDom Tx Hash np Hz) Hash := fun L ks =>
    (hashProg Sch IP h0 GB U txSel L ks A m K).toQuerier (encB Hz GB)
  have hwin : ∀ (f : BlockDom Tx Hash np Hz → Hash)
      (c : (Fin n → Option (Fin np)) × (Fin np → PK × SK)),
      coinsCollision (collFind Sch (Protocol.ofUniform (Hz := Hz) IP h0 GB U txSel) A.toAdversary
        (HashScheme.randomFun (BlockDom Tx Hash np Hz) Hash) (HashScheme.Codec.id _) K) f c =
          true → ROCollision (next c.1 c.2) qT f := by
    intro f c hc
    have hRO : ∀ b ∈ (letI := leaderParams IP h0 c.1
        letI : BlockParameters Tx Hash (Fin np) := ⟨GB, fun b => f (encB Hz b)⟩
        block_hist_gb (sTrace Sch (Protocol.ofUniform (Hz := Hz) IP h0 GB U txSel)
          (uSeed c.1 c.2 f) A.toAdversary false K)),
        ∃ k < qT, query (next c.1 c.2) f k = encB Hz b := by
      intro b hb
      have hm := encB_mem_hashProg Sch IP h0 GB U txSel c.1 c.2 A m hA.2 f (le_refl K) b hb
      obtain ⟨k, hk, hkb⟩ := List.mem_iff_getElem.1 hm
      refine ⟨k, lt_of_lt_of_le hk (OracleAdv.length_evalOn_le_of_isQueryBound f
        (isQueryBound_hashProg Sch IP h0 GB U txSel c.1 c.2 A m hA K)), ?_⟩
      rw [OracleAdv.query_toQuerier _ _ f k hk, hkb]
    simp only [coinsCollision, decide_eq_true_eq] at hc
    obtain ⟨hh, hne⟩ := hc
    cases hp : collPair Sch (Protocol.ofUniform (Hz := Hz) IP h0 GB U txSel) A.toAdversary
        (⟨c.1, (HashScheme.Codec.id
          (HashScheme.randomFun (BlockDom Tx Hash np Hz) Hash)).hashOn f, c.2⟩ :
            Seed Tx Hash np n Hz PK SK) K with
    | none =>
      simp only [collFind, hp] at hne
      exact absurd rfl hne
    | some bb =>
      obtain ⟨b, b'⟩ := bb
      obtain ⟨hb, hb', -, -⟩ := findColl_some hp
      simp only [collFind, hp] at hne hh
      obtain ⟨a, ha, hqa⟩ := hRO b hb
      obtain ⟨a', ha', hqa'⟩ := hRO b' hb'
      exact ⟨a, ha, a', ha', by rw [hqa, hqa']; exact hne, by rw [hqa, hqa']; exact hh⟩
  rw [collFinder, CR_Search_Advantage_ofCoins]
  refine bind_map_apply_le _ _ _ _ fun c => ?_
  rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
  refine (MeasureTheory.OuterMeasure.mono _ fun f hf => hwin f c hf).trans ?_
  exact prob_ROCollision_le (next c.1 c.2) qT

/-- **Security of PoS-NSB in the random-oracle model.** For a protocol with uniform tree types,
an oracle adversary `A` whose calls ask at most `qc` queries and output at most `m` messages,
the random function `HashScheme.randomFun` with the identity codec and the hypotheses of
`pos_nsb_security`, chain growth, chain quality, common prefix and the honest tip hold for the
first `K` phases of the real execution of `A.toAdversary` except with probability at most
`slotBound (kindLaw μ) n d w ε + qT (qT - 1) / 2 / |Hash| +
∑ᵢ eufcmaAdvantage Sch.toSigScheme (toEUFAdversary (forger … i))` with
`qT = 1 + K (|IP| (qc + m + 1))`. -/
theorem pos_nsb_security_rom [Fintype Tx] [Fintype Hash] [Nonempty Hash]
    (hA : A.Bounded qc m) (Tree : TreeFamily (Protocol.ofUniform (Hz := Hz) IP h0 GB U txSel))
    (hP : ProtocolHyp (Protocol.ofUniform (Hz := Hz) IP h0 GB U txSel)) (hTree : Tree.Longest)
    (μ : PMF (Option (Fin np))) (W K d w : ℕ) (ε : ℝ)
    (hwd : w ≤ d) (hWn : W + d ≤ n) (hn : K + 2 ≤ n) (hHz : K + 1 ≤ Hz)
    (hε : 0 ≤ ε) (hγ : 2 * pA (kindLaw μ) ≤ pH (kindLaw μ))
    (hw : (w : ℝ) ≤ d * (pH (kindLaw μ) - pA (kindLaw μ)))
    (h3 : (3 : ℝ) ≤ d * (pH (kindLaw μ) - 2 * pA (kindLaw μ))) :
    (seedDist Sch (HashScheme.randomFun (BlockDom Tx Hash np Hz) Hash) (HashScheme.Codec.id _) μ
        h0 W n).toOuterMeasure
        {ω | ¬Good (Protocol.ofUniform (Hz := Hz) IP h0 GB U txSel) Sch A.toAdversary Tree
          (kindLaw μ) K d w ε ω} ≤
      slotBound (kindLaw μ) n d w ε +
        (((1 + K * (IP.length * (qc + m + 1))) * (1 + K * (IP.length * (qc + m + 1)) - 1) / 2 :
          ℕ) : ℝ≥0∞) / Fintype.card Hash +
        ∑ i : Fin np, eufcmaAdvantage Sch.toSigScheme
          (toEUFAdversary (forger Sch (Protocol.ofUniform (Hz := Hz) IP h0 GB U txSel)
            A.toAdversary (HashScheme.randomFun (BlockDom Tx Hash np Hz) Hash)
            (HashScheme.Codec.id _) μ W K i)) :=
  (pos_nsb_security _ Sch A.toAdversary Tree hP hTree _ _ μ W K d w ε hwd hWn hn hHz hε hγ hw
    h3).trans (add_le_add_left (add_le_add_right
      (collFinder_advantage_oracle_le Sch IP h0 GB U txSel A hA μ W K) _) _)

end ROMBound

end CatCryptCore.Consensus.PoSNSB
