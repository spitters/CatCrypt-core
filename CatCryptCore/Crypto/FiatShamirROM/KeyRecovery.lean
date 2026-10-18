/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.FiatShamirROM.ProgFlag

/-!
# Fiat–Shamir in the random-oracle model: key recovery from hidden entries

A recovery `ρ : G.Recovery κ rel` marks the key classes `ρ.R` whose hidden entries
determine a witness: from the points and values visible to the adversary, `ρ.recover`
returns a witness of `rel`, and it succeeds once the public entries of an attempt and
the point of one of its hidden entries of a marked class are visible
(`Protocol.Recovery.CompleteAt`).

The game `attStepPR ρ D` has the tables and answers of the game with the programmed
flag `attStepP D`; its flag is not set when a hash query, an evaluated public entry or
a programmed entry lands on a hidden point of a marked class. Each such event records
the touched point in the visible tables, so a run of `attStepP D` that sets the flag
sets it in `attStepPR ρ D` or ends with visible tables on which the recovery succeeds
(`recTest`).

## Main definitions

* `Protocol.Recovery κ rel`, `Protocol.Recovery.none` — a recovery of witnesses from
  visible entries for the marked classes, and the recovery with no marked class
* `Protocol.Recovery.CompleteAt ρ D xw` — the recovery succeeds on every list that
  contains the public entries of an attempt of the sampler and the point of a hidden
  entry of a marked class
* `recTest ρ x t` — the recovery succeeds on the visible entries of the tables `t`
* `attSignOutPR`, `attSignPR`, `attStepPR ρ D` — the signing answer, signing oracle and
  oracle of the game with the flag exempt on marked hidden points
* `Protocol.AttKeyBoundClsAtNRB ρ κ N D xw Γ B` — the class-wise key bound of a sampler
  over the oracles satisfying `B`, with the entries of marked classes at undefined
  points left out of the charge

## Main results

* `attStepPR_none` — with no marked class the exempt game is the game with the
  programmed flag
* `run_attP_le_attPR` — a test of a run of the game with the programmed flag is at
  most a test of the run of the exempt game, for tests related by the invariant
  `RecInv`
* `run_attP_winsOrFlag_le_recR` — the probability that the forgery wins or the flag is
  set in a run of the game with the programmed flag is at most the probability that
  the forgery wins, the flag is set or the recovery succeeds in the exempt game
* `Protocol.attAdvantageByP_le_recR` — the same bound for the advantages
* `Protocol.AttKeyBoundClsAtN.toRB` — the class-wise key bound of a sampler is its
  bound with marked classes and a lookup predicate
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.FiatShamirROM

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.OracleForking
open CatCrypt.Crypto.Constructions.ECBCPRF (tsum_bind_mul tsum_pure_mul)
open scoped ENNReal

/-! ## Recoveries -/

/-- **A recovery of witnesses from visible entries.** The classes `R c` are the
key-dependent hidden classes; `recover x l` is a witness for `x` from the entries `l`,
or nothing, and every recovered witness satisfies `rel`. -/
structure Protocol.Recovery (G : Protocol) (κ : G.Classes) (rel : G.Stmt → G.Wit → Prop) :
    Type where
  /-- The marked classes. -/
  R : κ.ι → Bool
  /-- The witness recovered from the entries. -/
  recover : G.Stmt → List (G.Key × G.Ch) → Option G.Wit
  /-- A recovered witness is a witness. -/
  sound : ∀ x l w, recover x l = some w → rel x w

namespace Protocol.Recovery

variable {G : Protocol} {κ : G.Classes} {rel : G.Stmt → G.Wit → Prop}

/-- The recovery with no marked class, which recovers nothing. -/
def none : G.Recovery κ rel where
  R := fun _ => false
  recover := fun _ _ => Option.none
  sound := fun _ _ _ h => by cases h

/-- **Completeness of a recovery at a sampler.** For every attempt in the support of
`D xw m e`, every oracle `look` and every hidden entry `i` of a marked class, the
recovery succeeds on every list that contains the public entries of the attempt
against `look` and an entry at the point of `i`. -/
def CompleteAt (ρ : G.Recovery κ rel) (D : G.Sampler) (xw : G.Stmt × G.Wit) : Prop :=
  ∀ (m : G.Msg) (e : Fin G.μ → G.Ch), ∀ a ∈ (D xw m e).support,
    ∀ (look : G.Key → Option G.Ch) (i : Fin G.μ),
      a.pub (a.vals look e) i = false → ρ.R (κ.cls (a.key (a.vals look e) i)) = true →
      ∀ l : List (G.Key × G.Ch),
        (∀ p ∈ a.evEntries (a.vals look e) ++ a.pubEntries (a.vals look e), p ∈ l) →
        (∃ p ∈ l, p.1 = a.key (a.vals look e) i) → (ρ.recover xw.1 l).isSome

/-- The point `k` is a hidden point of a marked class in `t`: undefined in the visible
entries, defined in the hidden ones, and of a marked class. -/
def hidR (ρ : G.Recovery κ rel) (t : G.Tables) (k : G.Key) : Bool :=
  ρ.R (κ.cls k) && (t.lookup k).isNone && (lookupIn t.rej k).isSome

end Protocol.Recovery

section RecGame

variable {G : Protocol} {κ : G.Classes} {rel : G.Stmt → G.Wit → Prop}

/-- The recovery succeeds on the visible entries of the tables `t`. -/
def recTest (ρ : G.Recovery κ rel) (x : G.Stmt) (t : G.Tables) : Bool :=
  (ρ.recover x (t.prog ++ t.hash)).isSome

/-- The flag of a signing attempt `a` with the values `e` against `t` in the exempt
game: a hidden entry lands on a defined point, an evaluated public entry lands on a
hidden point of an unmarked class, or a programmed entry lands on a defined point
other than a hidden point of a marked class. -/
def attFlagR (ρ : G.Recovery κ rel) (t : G.Tables) (e : Fin G.μ → G.Ch) (a : G.Attempt) :
    Bool :=
  ((List.finRange G.μ).any fun i =>
    if a.pub (a.vals t.lookupAll e) i then
      G.ev i && (t.lookup (a.key (a.vals t.lookupAll e) i)).isNone &&
        (lookupIn t.rej (a.key (a.vals t.lookupAll e) i)).isSome &&
        !ρ.R (κ.cls (a.key (a.vals t.lookupAll e) i))
    else (t.lookupAll (a.key (a.vals t.lookupAll e) i)).isSome) ||
  (List.finRange G.μ).any fun i =>
    !G.ev i && (t.lookupAll (a.key (a.vals t.lookupAll e) i)).isSome &&
      !ρ.hidR t (a.key (a.vals t.lookupAll e) i)

/-- The signing answer on `m` of the attempt `a` with the values `e` from the tables
`t` in the exempt game: the answer and tables of `attSignOut`, with the flag
`attFlagR`. -/
def attSignOutPR (ρ : G.Recovery κ rel) (t : G.Tables) (b : Bool) (m : G.Msg)
    (e : Fin G.μ → G.Ch) (a : G.Attempt) : G.Answer × (G.Tables × Bool) :=
  ((attSignOut t b m e a).1, ((attSignOut t b m e a).2.1, b || attFlagR ρ t e a))

/-- The signing oracle of the exempt game of the sampler `D` for the pair `xw` on `m`
from the state `s`: uniform values `e`, then an attempt from `D xw m e`. -/
noncomputable def attSignPR (ρ : G.Recovery κ rel) (D : G.Sampler) (xw : G.Stmt × G.Wit)
    (s : G.Tables × Bool) (m : G.Msg) : PMF (G.Answer × (G.Tables × Bool)) :=
  (PMF.uniformOfFintype (Fin G.μ → G.Ch)).bind fun e =>
    (D xw m e).map (attSignOutPR ρ s.1 s.2 m e)

/-- A hash query of the exempt game: the hash query of the real game, whose flag is
not set when the point is a hidden point of a marked class. -/
noncomputable def realHashStepR (ρ : G.Recovery κ rel) (t : G.Tables) (b : Bool) (k : G.Key) :
    Step G.Answer (G.Tables × Bool) G.Ch :=
  match t.lookup k with
  | some e => .plain (PMF.pure (.inl e, (t, b)))
  | none =>
    match lookupIn t.rej k with
    | some e => .plain (PMF.pure (.inl e, ({ t with hash := t.hash ++ [(k, e)] },
        b || !ρ.R (κ.cls k))))
    | none => .fresh fun e => (.inl e, ({ t with hash := t.hash ++ [(k, e)] }, b))

/-- **The exempt game** of the recovery `ρ` at the sampler `D` for the pair `xw`: the
hash queries `realHashStepR` and the signing oracle `attSignPR`. -/
noncomputable def attStepPR (ρ : G.Recovery κ rel) (D : G.Sampler) (xw : G.Stmt × G.Wit)
    (s : G.Tables × Bool) : G.Query → Step G.Answer (G.Tables × Bool) G.Ch
  | .inl k => realHashStepR ρ s.1 s.2 k
  | .inr m => .plain (attSignPR ρ D xw s m)

/-- The exempt game of `ρ` at the sampler `D` whose outcome is decided by `P`. -/
noncomputable def attGameByPR (P : G.Stmt → G.Forgery × (G.Tables × Bool) → Bool)
    (ρ : G.Recovery κ rel) (D : G.Sampler) {qH qS : ℕ} (A : G.Adversary qH qS) : SPComp Bool :=
  PRPPRF.pmfGame (gameDistBy P (attStepPR ρ D) A)

/-- The advantage in the exempt game of `ρ` at the sampler `D` whose outcome is decided
by `P`. -/
noncomputable def attAdvantageByPR (P : G.Stmt → G.Forgery × (G.Tables × Bool) → Bool)
    (ρ : G.Recovery κ rel) (D : G.Sampler) {qH qS : ℕ} (A : G.Adversary qH qS) : ℝ≥0∞ :=
  prTrue (attGameByPR P ρ D A) Heap.empty

/-- With no marked class the exempt game is the game with the programmed flag. -/
theorem attStepPR_none (D : G.Sampler) :
    attStepPR (Protocol.Recovery.none : G.Recovery κ rel) D = attStepP D := by
  funext xw s d
  cases d with
  | inl k =>
    simp only [attStepPR, attStepP, realHashStepR, realHashStep, Protocol.Recovery.none,
      Bool.not_false, Bool.or_true]
    rfl
  | inr m =>
    have h : ∀ t b m e, attSignOutPR (Protocol.Recovery.none : G.Recovery κ rel) t b m e =
        attSignOutP t b m e := by
      intro t b m e
      funext a
      simp only [attSignOutPR, attSignOutP, attSignOut, attFlagR, Protocol.Attempt.progHit,
        Protocol.Recovery.hidR, Protocol.Recovery.none, Bool.not_false, Bool.and_true,
        Bool.false_and, Bool.or_assoc]
    simp only [attStepPR, attStepP, attSignPR, attSignP, h]

end RecGame

/-! ## Visible entries of the tables -/

section Visible

variable {G : Protocol}

theorem mem_of_lookupIn_eq_some {K C : Type} [DecidableEq K] {l : List (K × C)} {k : K}
    {c : C} (h : lookupIn l k = some c) : (k, c) ∈ l := by
  unfold lookupIn findKey at h
  cases hf : l.findIdx? (fun p => decide (p.1 = k)) with
  | none => simp [hf] at h
  | some i =>
    obtain ⟨hi, hp, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
    simp only [hf, Option.bind_some, List.getElem?_eq_getElem hi, Option.map_some,
      Option.some.injEq] at h
    simp only [decide_eq_true_eq] at hp
    rw [← hp, ← h]
    exact List.getElem_mem hi

theorem Protocol.mem_of_lookup_eq_some {t : G.Tables} {k : G.Key} {c : G.Ch}
    (h : t.lookup k = some c) : (k, c) ∈ t.prog ++ t.hash := by
  unfold Protocol.Tables.lookup at h
  cases hp : lookupIn t.prog k with
  | some c' =>
    rw [hp, Option.some_or] at h
    cases h
    exact List.mem_append_left _ (mem_of_lookupIn_eq_some hp)
  | none =>
    rw [hp, Option.none_or] at h
    exact List.mem_append_right _ (mem_of_lookupIn_eq_some h)

/-- The value of an evaluated entry of an attempt against `look` is the value of
`look` at its point when defined. -/
theorem Protocol.Attempt.vals_of_ev (a : G.Attempt) (look : G.Key → Option G.Ch)
    (e : Fin G.μ → G.Ch) (i : Fin G.μ) (hi : G.ev i = true) :
    a.vals look e i = (look (a.key (a.vals look e) i)).getD (e i) := by
  change effVal _ a.key e i = _
  rw [effVal_eq _ a.key a.key_causal e i, if_pos hi]
  rfl

theorem Protocol.Attempt.nodup_entries (a : G.Attempt) (v : Fin G.μ → G.Ch)
    (p : Fin G.μ → Bool) : ((a.entries v p).map Prod.fst).Nodup := by
  simp only [Protocol.Attempt.entries, List.map_map]
  exact ((List.nodup_finRange _).filter _).map fun i j h => a.key_inj v i j h

/-- The point of a programmed entry of an attempt is not the point of an evaluated
public entry. -/
theorem Protocol.Attempt.key_notMem_evEntries (a : G.Attempt) {v : Fin G.μ → G.Ch}
    {i : Fin G.μ} (hi : G.ev i = false) : a.key v i ∉ (a.evEntries v).map Prod.fst := by
  intro h
  obtain ⟨p, hp, hpk⟩ := List.mem_map.mp h
  obtain ⟨j, hj, rfl⟩ := Protocol.Attempt.mem_entries hp
  obtain rfl := a.key_inj v j i hpk
  simp [hi] at hj

/-- Programming entries at distinct points records an entry whose point is undefined. -/
theorem programAll_mem_prog (t : G.Tables) (b : Bool) (l : List (G.Key × G.Ch))
    (hnd : (l.map Prod.fst).Nodup) {p : G.Key × G.Ch} (hp : p ∈ l)
    (ht : t.lookup p.1 = none) : p ∈ (programAll t b l).1.prog := by
  induction l generalizing t b with
  | nil => simp at hp
  | cons q l ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map, not_exists, not_and] at hnd
    unfold programAll
    rcases List.mem_cons.mp hp with rfl | hp'
    · rw [ht]
      exact (programAll_tables _ b l).2.2.2.1.subset (by simp)
    · have hne : p.1 ≠ q.1 := fun h => hnd.1 p hp' h
      split
      · exact ih t true hnd.2 hp' ht
      · refine ih _ b hnd.2 hp' ?_
        change (lookupIn (t.prog ++ [q]) p.1).or (lookupIn t.hash p.1) = Option.none
        rw [lookupIn_append_singleton_of_ne _ _ hne]
        exact ht

/-- The answer and tables of a signing attempt do not depend on the flag. -/
theorem attSignOut_flag_indep (t : G.Tables) (b b' : Bool) (m : G.Msg) (e : Fin G.μ → G.Ch)
    (a : G.Attempt) :
    (attSignOut t b m e a).1 = (attSignOut t b' m e a).1 ∧
      (attSignOut t b m e a).2.1 = (attSignOut t b' m e a).2.1 := by
  refine ⟨rfl, ?_⟩
  simp only [attSignOut, traceOut, programOut, programAll_fst_flag _ b b']

end Visible

/-! ## The invariant of the coupling -/

section RecInvSection

variable {G : Protocol} {κ : G.Classes} {rel : G.Stmt → G.Wit → Prop}

/-- The recovery succeeds on every list that contains the visible entries of `t`. -/
def RecReady (ρ : G.Recovery κ rel) (x : G.Stmt) (t : G.Tables) : Prop :=
  ∀ l : List (G.Key × G.Ch), (∀ q ∈ t.prog ++ t.hash, q ∈ l) → (ρ.recover x l).isSome

/-- **The invariant of the coupling** between the game with the programmed flag, with
flag `bP`, and the exempt game, with flag `bPR`, on the same tables `t`: when `bP` is
set, `bPR` is set or the recovery is ready on `t`; when `bPR` is not set, every hidden
entry of a marked class makes the recovery succeed on every list containing the
visible entries of `t` and an entry at its point. -/
def RecInv (ρ : G.Recovery κ rel) (x : G.Stmt) (t : G.Tables) (bP bPR : Bool) : Prop :=
  (bP = true → bPR = true ∨ RecReady ρ x t) ∧
  (bPR = false → ∀ p ∈ t.rej, ρ.R (κ.cls p.1) = true →
    ∀ l : List (G.Key × G.Ch), (∀ q ∈ t.prog ++ t.hash, q ∈ l) →
      (∃ q ∈ l, q.1 = p.1) → (ρ.recover x l).isSome)

variable (ρ : G.Recovery κ rel) (x : G.Stmt)

theorem recInv_empty : RecInv ρ x Protocol.Tables.empty false false :=
  ⟨fun h => Bool.noConfusion h, fun _ p hp => by simp [Protocol.Tables.empty] at hp⟩

theorem RecReady.mono {t t' : G.Tables} (h : RecReady ρ x t)
    (hvis : ∀ q ∈ t.prog ++ t.hash, q ∈ t'.prog ++ t'.hash) : RecReady ρ x t' :=
  fun l hl => h l fun q hq => hl q (hvis q hq)

theorem recTest_of_recReady {t : G.Tables} (h : RecReady ρ x t) : recTest ρ x t = true :=
  h _ fun _ hq => hq

theorem RecInv.mono {t t' : G.Tables} {bP bPR : Bool} (h : RecInv ρ x t bP bPR)
    (hvis : ∀ q ∈ t.prog ++ t.hash, q ∈ t'.prog ++ t'.hash) (hrej : t'.rej = t.rej) :
    RecInv ρ x t' bP bPR :=
  ⟨fun hb => (h.1 hb).imp id fun hr => hr.mono ρ x hvis, fun hb p hp hR l hl hk =>
    h.2 hb p (hrej ▸ hp) hR l (fun q hq => hl q (hvis q hq)) hk⟩

/-- A touch of a hidden entry of a marked class whose point becomes visible makes the
recovery ready. -/
theorem recReady_of_touch {t t' : G.Tables} {bP : Bool} (h : RecInv ρ x t bP false)
    {p : G.Key × G.Ch} (hp : p ∈ t.rej) (hR : ρ.R (κ.cls p.1) = true)
    (hvis : ∀ q ∈ t.prog ++ t.hash, q ∈ t'.prog ++ t'.hash)
    {q : G.Key × G.Ch} (hq : q ∈ t'.prog ++ t'.hash) (hqk : q.1 = p.1) : RecReady ρ x t' :=
  fun l hl => h.2 rfl p hp hR l (fun q' hq' => hl q' (hvis q' hq')) ⟨q, hl q hq, hqk⟩

end RecInvSection

/-! ## One signing attempt -/

section RecSign

variable {G : Protocol} {κ : G.Classes} {rel : G.Stmt → G.Wit → Prop}
  (ρ : G.Recovery κ rel) {D : G.Sampler} {xw : G.Stmt × G.Wit}

/-- **The invariant across a signing attempt** of a sampler at which the recovery is
complete. -/
theorem recInv_attSignOut (hrec : ρ.CompleteAt D xw) {m : G.Msg} {e : Fin G.μ → G.Ch}
    {a : G.Attempt} (ha : a ∈ (D xw m e).support) {t : G.Tables} {bP bPR : Bool}
    (hI : RecInv ρ xw.1 t bP bPR) :
    RecInv ρ xw.1 (attSignOut t bP m e a).2.1 (attSignOutP t bP m e a).2.2
      (attSignOutPR ρ t bPR m e a).2.2 := by
  set v := a.vals t.lookupAll e with hv
  set T' := (attSignOut t bP m e a).2.1 with hT'
  have hL := le_traceOut t bP m (a.trace v)
  have hvis : ∀ q ∈ t.prog ++ t.hash, q ∈ T'.prog ++ T'.hash := by
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact List.mem_append_left _ (hL.1.subset hq)
    · exact List.mem_append_right _ (hL.2.1.subset hq)
  by_cases hf : (bPR || attFlagR ρ t e a) = true
  · refine ⟨fun _ => Or.inl hf, fun hb => ?_⟩
    simp only [attSignOutPR] at hb
    rw [hf] at hb
    exact absurd hb (by simp)
  simp only [Bool.or_eq_true, not_or, Bool.not_eq_true] at hf
  obtain ⟨hb, hfR⟩ := hf
  subst hb
  simp only [attFlagR, ← hv, Bool.or_eq_false_iff, List.any_eq_false, List.mem_finRange,
    true_implies] at hfR
  obtain ⟨h1, h2⟩ := hfR
  -- the points of programmed entries are undefined in the visible entries
  have hprogNone : ∀ j, G.ev j = false → t.lookup (a.key v j) = Option.none := by
    intro j hj
    have := h2 j
    simp only [hj, Bool.not_false, Bool.true_and] at this
    cases hn : (t.lookupAll (a.key v j)).isSome
    · exact Protocol.lookup_eq_none_of_lookupAll (by simpa using hn)
    · cases hr : ρ.hidR t (a.key v j)
      · simp [hn, hr] at this
      · simp only [Protocol.Recovery.hidR, Bool.and_eq_true] at hr
        simpa using hr.1.2
  -- the public entries of the attempt are visible after it
  have hpubmem : ∀ q ∈ a.evEntries v ++ a.pubEntries v, q ∈ T'.prog ++ T'.hash := by
    intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · obtain ⟨j, hj, rfl⟩ := Protocol.Attempt.mem_entries hq
      simp only [Bool.and_eq_true] at hj
      cases hl : t.lookup (a.key v j) with
      | some c =>
        have hvj : v j = c := by
          rw [hv, Protocol.Attempt.vals_of_ev a _ e j hj.1, ← hv]
          simp [Protocol.Tables.lookupAll, hl]
        rw [hvj]
        exact hvis _ (Protocol.mem_of_lookup_eq_some hl)
      | none =>
        refine List.mem_append_right _ ?_
        change _ ∈ (programAll (hashAll t (a.evEntries v)) bP (a.pubEntries v)).1.hash
        rw [(programAll_tables _ _ _).1]
        exact List.mem_append_right _ (List.mem_filter.mpr ⟨hq, by simp [hl]⟩)
    · obtain ⟨j, hj, rfl⟩ := Protocol.Attempt.mem_entries hq
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hj
      refine List.mem_append_left _ ?_
      change _ ∈ (programAll (hashAll t (a.evEntries v)) bP (a.pubEntries v)).1.prog
      refine programAll_mem_prog _ _ _ (a.nodup_entries v _) hq ?_
      rw [Protocol.lookup_hashAll_of_notMem _ _ (a.key_notMem_evEntries hj.1)]
      exact hprogNone j hj.1
  refine ⟨fun hP => Or.inr ?_, fun _ p hp hR l hl hk => ?_⟩
  · simp only [attSignOutP, attSignOut, ← hv, Bool.or_eq_true, List.any_eq_true,
      List.mem_finRange, true_and] at hP
    rcases hP with (hP | ⟨i, hi⟩) | hi
    · rcases hI.1 hP with h | h
      · exact absurd h (by simp)
      · exact h.mono ρ xw.1 hvis
    · have h1i := h1 i
      by_cases hpi : a.pub v i = true
      · simp only [hpi, if_true, Bool.and_eq_true] at hi h1i
        obtain ⟨⟨hev, hnone⟩, hsome⟩ := hi
        have hR : ρ.R (κ.cls (a.key v i)) = true := by
          simpa [hev, hnone, hsome] using h1i
        obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hsome
        exact recReady_of_touch ρ xw.1 hI (mem_of_lookupIn_eq_some hc) hR hvis
          (hpubmem _ (List.mem_append_left _
            (Protocol.Attempt.mem_entries_of (by simp [hev, hpi])))) rfl
      · simp only [hpi, Bool.false_eq_true, if_false] at hi h1i
        rw [hi] at h1i
        exact absurd h1i (by simp)
    · simp only [Protocol.Attempt.progHit, ← hv, List.any_eq_true, List.mem_finRange,
        true_and, Bool.and_eq_true, Bool.not_eq_true'] at hi
      obtain ⟨i, hev, hsome⟩ := hi
      have h2i := h2 i
      simp only [hev, hsome, Bool.not_false, Bool.true_and] at h2i
      have hhid : ρ.hidR t (a.key v i) = true := by
        by_contra hc
        exact h2i (by simpa using hc)
      simp only [Protocol.Recovery.hidR, Bool.and_eq_true] at hhid
      obtain ⟨⟨hR, -⟩, hrej⟩ := hhid
      obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hrej
      by_cases hpi : a.pub v i = true
      · exact recReady_of_touch ρ xw.1 hI (mem_of_lookupIn_eq_some hc) hR hvis
          (hpubmem _ (List.mem_append_right _
            (Protocol.Attempt.mem_entries_of (by simp [hev, hpi])))) rfl
      · have h1i := h1 i
        simp only [hpi, Bool.false_eq_true, if_false, hsome] at h1i
        exact absurd h1i (by simp)
  · change p ∈ t.rej ++ _ at hp
    rcases List.mem_append.mp hp with hp | hp
    · exact hI.2 rfl p hp hR l (fun q hq => hl q (hvis q hq)) hk
    · obtain ⟨j, hj, rfl⟩ := Protocol.Attempt.mem_entries (List.mem_filter.mp hp).1
      simp only [Bool.not_eq_true'] at hj
      exact hrec m e a ha t.lookupAll j hj hR l (fun q hq => hl q (hpubmem q hq)) hk

end RecSign

/-! ## The coupling -/

section RecCouple

variable {G : Protocol} {κ : G.Classes} {rel : G.Stmt → G.Wit → Prop} {α : Type}
  (ρ : G.Recovery κ rel) {D : G.Sampler} {xw : G.Stmt × G.Wit}

/-- One transition of the coupling: a test of a transition of the game with the
programmed flag is at most a test of the transition of the exempt game on the same
query, for tests related by the invariant. -/
theorem attStepP_le_attStepPR (hrec : ρ.CompleteAt D xw) (t : G.Tables) (bP bPR : Bool)
    (hI : RecInv ρ xw.1 t bP bPR) (d : G.Query) (F F' : G.Answer × (G.Tables × Bool) → ℝ≥0∞)
    (hF : ∀ r t' bP' bPR', RecInv ρ xw.1 t' bP' bPR' → F (r, (t', bP')) ≤ F' (r, (t', bPR'))) :
    ∑' o, toOracle (attStepP D xw) (t, bP) d o * F o ≤
      ∑' o, toOracle (attStepPR ρ D xw) (t, bPR) d o * F' o := by
  cases d with
  | inl k =>
    simp only [toOracle, attStepP, attStepPR, realHashStep, realHashStepR]
    cases hl : t.lookup k with
    | some c =>
      simp only [Step.toPMF, tsum_pure_mul]
      exact hF _ _ _ _ hI
    | none =>
      have hvis : ∀ c, ∀ q ∈ t.prog ++ t.hash,
          q ∈ ({ t with hash := t.hash ++ [(k, c)] } : G.Tables).prog ++
            ({ t with hash := t.hash ++ [(k, c)] } : G.Tables).hash := fun c q hq => by
        rcases List.mem_append.mp hq with hq | hq
        · exact List.mem_append_left _ hq
        · exact List.mem_append_right _ (List.mem_append_left _ hq)
      cases hr : lookupIn t.rej k with
      | some c =>
        simp only [Step.toPMF, tsum_pure_mul]
        refine hF _ _ _ _ ⟨fun _ => ?_, fun hb => ?_⟩
        · cases hR : ρ.R (κ.cls k)
          · exact Or.inl (by simp)
          · cases hbPR : bPR
            · refine Or.inr (recReady_of_touch ρ xw.1 (hbPR ▸ hI)
                (mem_of_lookupIn_eq_some hr) hR (hvis c) (q := (k, c))
                (List.mem_append_right _ (List.mem_append_right _ (by simp))) rfl)
            · exact Or.inl rfl
        · simp only [Bool.or_eq_false_iff, Bool.not_eq_false'] at hb
          exact (hI.mono ρ xw.1 (hvis c) rfl).2 hb.1
      | none =>
        simp only [Step.toPMF, tsum_map_mul']
        exact ENNReal.tsum_le_tsum fun c => mul_le_mul_right
          (hF _ _ _ _ (hI.mono ρ xw.1 (hvis c) rfl)) _
  | inr m =>
    simp only [toOracle, attStepP, attStepPR, Step.toPMF, attSignP, attSignPR, tsum_bind_mul,
      tsum_map_mul']
    refine ENNReal.tsum_le_tsum fun e => mul_le_mul_right
      (ENNReal.tsum_le_tsum fun a => ?_) _
    by_cases ha : D xw m e a = 0
    · simp [ha]
    refine mul_le_mul_right ?_ _
    have hI' := recInv_attSignOut ρ hrec ((PMF.mem_support_iff _ _).mpr ha) hI
    obtain ⟨h1, h2⟩ := attSignOut_flag_indep t bPR bP m e a
    have := hF (attSignOut t bP m e a).1 (attSignOut t bP m e a).2.1 _ _ hI'
    change F (attSignOutP t bP m e a) ≤ F' ((attSignOut t bPR m e a).1,
      ((attSignOut t bPR m e a).2.1, (attSignOutPR ρ t bPR m e a).2.2))
    rw [h1, h2]
    exact this

/-- **The coupling of the game with the programmed flag and the exempt game.** For a
recovery complete at the sampler, a test `f` of a run of the game with the programmed
flag is at most a test `g` of the run of the exempt game from the same tables, when
`f` is at most `g` on outcomes related by the invariant. -/
theorem run_attP_le_attPR (hrec : ρ.CompleteAt D xw) (A : OracleAdv G.Query G.Answer α)
    (t : G.Tables) (bP bPR : Bool) (hI : RecInv ρ xw.1 t bP bPR)
    (f g : α × (G.Tables × Bool) → ℝ≥0∞)
    (hfg : ∀ y t' bP' bPR', RecInv ρ xw.1 t' bP' bPR' → f (y, (t', bP')) ≤ g (y, (t', bPR'))) :
    ∑' y, OracleAdv.run (toOracle (attStepP D xw)) A (t, bP) y * f y ≤
      ∑' y, OracleAdv.run (toOracle (attStepPR ρ D xw)) A (t, bPR) y * g y := by
  induction A generalizing t bP bPR with
  | ret a =>
    simp only [OracleAdv.run_ret, tsum_pure_mul]
    exact hfg a t bP bPR hI
  | rand p k ih =>
    simp only [OracleAdv.run_rand, tsum_bind_mul]
    exact ENNReal.tsum_le_tsum fun c => mul_le_mul_right (ih c t bP bPR hI) _
  | query d k ih =>
    simp only [OracleAdv.run_query, tsum_bind_mul]
    exact attStepP_le_attStepPR ρ hrec t bP bPR hI d _ _ fun r t' bP' bPR' h =>
      ih r t' bP' bPR' h

/-- **Exempt touches are recoveries, for runs.** For a recovery complete at the
sampler, the probability that the forgery wins or the flag is set in a run of the game
with the programmed flag is at most the probability that the forgery wins, the flag is
set or the recovery succeeds on the visible entries in the run of the exempt game. -/
theorem run_attP_winsOrFlag_le_recR (hrec : ρ.CompleteAt D xw)
    (A : OracleAdv G.Query G.Answer G.Forgery) :
    (OracleAdv.run (toOracle (attStepP D xw)) A (Protocol.Tables.empty, false)).toOuterMeasure
        {y | winsOrFlag xw.1 y = true} ≤
      (OracleAdv.run (toOracle (attStepPR ρ D xw)) A (Protocol.Tables.empty, false)).toOuterMeasure
        {y | winsOrFlag xw.1 y = true ∨ recTest ρ xw.1 y.2.1 = true} := by
  have hset : {y : G.Forgery × (G.Tables × Bool) |
      winsOrFlag xw.1 y = true ∨ recTest ρ xw.1 y.2.1 = true} =
      {y | (winsOrFlag xw.1 y || recTest ρ xw.1 y.2.1) = true} := by
    ext y
    simp
  rw [hset, toOuterMeasure_eq_tsum_ite, toOuterMeasure_eq_tsum_ite]
  refine run_attP_le_attPR ρ hrec A _ false false (recInv_empty ρ xw.1) _ _
    fun y t' bP' bPR' h => ?_
  by_cases hw : winsOrFlag xw.1 (y, (t', bP')) = true
  · rw [if_pos hw, if_pos]
    simp only [winsOrFlag, Bool.or_eq_true] at hw ⊢
    rcases hw with hw | hw
    · exact Or.inl (Or.inl hw)
    · rcases h.1 hw with h' | h'
      · exact Or.inl (Or.inr h')
      · exact Or.inr (recTest_of_recReady ρ xw.1 h')
  · rw [if_neg hw]
    exact zero_le

/-- **Exempt touches are recoveries.** For a recovery complete at the sampler at every
generated pair, the advantage that the forgery wins or the flag is set in the game with
the programmed flag is at most the advantage that the forgery wins, the flag is set or
the recovery succeeds in the exempt game. -/
theorem Protocol.attAdvantageByP_le_recR (D : G.Sampler)
    (hrec : ∀ xw ∈ G.gen.support, ρ.CompleteAt D xw) {qH qS : ℕ} (A : G.Adversary qH qS) :
    attAdvantageByP winsOrFlag D A ≤
      attAdvantageByPR (fun x y => winsOrFlag x y || recTest ρ x y.2.1) ρ D A := by
  unfold attAdvantageByP attAdvantageByPR attGameByP attGameByPR
  rw [prTrue_gameDistBy, prTrue_gameDistBy]
  refine ENNReal.tsum_le_tsum fun xw => ?_
  by_cases hxw : G.gen xw = 0
  · simp [hxw]
  refine mul_le_mul_right ?_ _
  refine (run_attP_winsOrFlag_le_recR ρ (hrec xw ((PMF.mem_support_iff _ _).mpr hxw))
    _).trans (le_of_eq ?_)
  congr 1
  ext y
  simp [Bool.or_eq_true]

end RecCouple

/-! ## The key bound with marked classes -/

namespace Protocol

variable (G : Protocol)

/-- **Class-wise key bound of a sampler with marked classes, over the oracles
satisfying `B`.** The bound `AttKeyBoundClsAtN` restricted to the oracles `look`
satisfying `B`, with the charge of an entry `i` of a marked class `ρ.R (κ.ecls i)`
restricted to entries whose point is defined in `look`. -/
def AttKeyBoundClsAtNRB {κ : G.Classes} {rel : G.Stmt → G.Wit → Prop} (ρ : G.Recovery κ rel)
    (N : ℕ) (D : G.Sampler) (xw : G.Stmt × G.Wit) (Γ : κ.ι → ℝ≥0∞)
    (B : (G.Key → Option G.Ch) → Prop) : Prop :=
  ∀ (c : κ.ι) (m : G.Msg) (look : G.Key → Option G.Ch), B look →
    (∃ ks : List G.Key, ks.length ≤ N ∧ ∀ k, (look k).isSome → k ∈ ks) →
    ∀ (Q : G.Trace → PMF G.Key),
    ∑' e, PMF.uniformOfFintype (Fin G.μ → G.Ch) e * ∑' a, D xw m e a *
      ∑ i ∈ Finset.univ.filter (fun i => κ.ecls i = c),
        (if a.charged look e i &&
            (!ρ.R (κ.ecls i) || (look (a.key (a.vals look e) i)).isSome) then
          Q (a.guessView look e i) (a.key (a.vals look e) i) else 0) ≤ Γ c

variable {G}

/-- The class-wise key bound of a sampler is its bound with marked classes over the
oracles satisfying any predicate. -/
theorem AttKeyBoundClsAtN.toRB {κ : G.Classes} {rel : G.Stmt → G.Wit → Prop}
    {N : ℕ} {D : G.Sampler} {xw : G.Stmt × G.Wit} {Γ : κ.ι → ℝ≥0∞}
    (h : G.AttKeyBoundClsAtN κ N D xw Γ) (ρ : G.Recovery κ rel)
    (B : (G.Key → Option G.Ch) → Prop) : G.AttKeyBoundClsAtNRB ρ N D xw Γ B := by
  intro c m look _ hlook Q
  refine le_trans ?_ (h c m look hlook Q)
  refine ENNReal.tsum_le_tsum fun e => mul_le_mul_right
    (ENNReal.tsum_le_tsum fun a => mul_le_mul_right
      (Finset.sum_le_sum fun i _ => ?_) _) _
  split_ifs with h1 h2 <;> simp_all

end Protocol

end CatCrypt.Crypto.FiatShamirROM
