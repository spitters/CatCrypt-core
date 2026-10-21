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
flag `attStepP D`; its flag is not set when a hash query or a programmed entry lands
on a hidden point of a marked class, nor when an evaluated public entry lands on a
hidden point of a marked class while the hidden entries of the attempt against the
visible entries are at undefined points. Each exempt event records
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
* `Protocol.AttPubCausalAt D xw` — the public marks of the attempts of a sampler read
  only the values of earlier and of programmed entries

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
* `recReady_traceOut_of_land` — for causal public marks, an evaluated public entry that
  lands on a hidden point without setting the flag of the exempt game is an evaluated
  public entry of the attempt against the visible entries, so the recovery is ready on
  the tables of its trace
* `run_attPR_le_sim` — for a sampler with causal public marks and a test that is `1`
  whenever the recovery succeeds, the test of a run of the exempt game on the outcomes
  with the flag cleared is at most the test of the simulated run plus `q·δ`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.FiatShamirROM

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.OracleForking
open CatCrypt.Crypto.Constructions.ECBCPRF (tsum_pure_mul)
open PMF (tsum_bind_mul)
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
game: a hidden entry lands on a defined point; an evaluated public entry lands on a
hidden point of an unmarked class, or on a hidden point while a hidden entry of the
attempt against the visible entries lands on a visible point; or a programmed entry
lands on a defined point other than a hidden point of a marked class. -/
def attFlagR (ρ : G.Recovery κ rel) (t : G.Tables) (e : Fin G.μ → G.Ch) (a : G.Attempt) :
    Bool :=
  ((List.finRange G.μ).any fun i =>
    if a.pub (a.vals t.lookupAll e) i then
      G.ev i && (t.lookup (a.key (a.vals t.lookupAll e) i)).isNone &&
        (lookupIn t.rej (a.key (a.vals t.lookupAll e) i)).isSome &&
        (!ρ.R (κ.cls (a.key (a.vals t.lookupAll e) i)) ||
          !a.hidFresh t.lookup (a.vals t.lookup e))
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
  liftPMF (gameDistBy P (attStepPR ρ D) A)

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
        Bool.false_and, Bool.or_assoc, Bool.true_or]
    simp only [attStepPR, attStepP, attSignPR, attSignP, h]

end RecGame

/-! ## Visible entries of the tables -/

/-- Two oracles that agree at the points of the entries before `j` of an attempt against
the first give the same values before `j`. -/
theorem effVec_congr_lt {μ : ℕ} {K C : Type} (look look' : Fin μ → K → Option C)
    (key : (Fin μ → C) → Fin μ → K)
    (hk : ∀ (v v' : Fin μ → C) (i : Fin μ), (∀ j, j < i → v j = v' j) → key v i = key v' i)
    (e : Fin μ → C) (j : Fin μ)
    (h : ∀ i, i < j → look' i (key (effVec look key e) i) = look i (key (effVec look key e) i)) :
    ∀ i, i < j → effVec look' key e i = effVec look key e i := by
  have H : ∀ n, ∀ i : Fin μ, i.val < n → i < j → effVec look' key e i = effVec look key e i := by
    intro n
    induction n with
    | zero => exact fun i hi => absurd hi (Nat.not_lt_zero _)
    | succ n ih =>
      intro i hi hij
      change effVal look' key e i = effVal look key e i
      have hkey : key (effVec look' key e) i = key (effVec look key e) i :=
        hk _ _ i fun j' hj' => ih j' (by have : j'.val < i.val := hj'; omega) (lt_trans hj' hij)
      rw [effVal_eq look' key hk e i, effVal_eq look key hk e i, hkey, h i hij]
  exact fun i hij => H _ i i.isLt hij

section Visible

variable {G : Protocol}

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

/-- The value of an entry of an attempt that is programmed or at a point undefined in
`look` is its value in `e`. -/
theorem Protocol.Attempt.vals_eq_of_fresh (a : G.Attempt) (look : G.Key → Option G.Ch)
    (e : Fin G.μ → G.Ch) (i : Fin G.μ)
    (h : (!G.ev i || (look (a.key (a.vals look e) i)).isNone) = true) :
    a.vals look e i = e i := by
  cases hi : G.ev i
  · change effVal _ a.key e i = _
    rw [effVal_eq _ a.key a.key_causal e i, if_neg (by simp [hi])]
    rfl
  · rw [a.vals_of_ev look e i hi]
    simp only [hi, Bool.not_true, Bool.false_or, Option.isNone_iff_eq_none] at h
    rw [h, Option.getD_none]

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
      cases hpi : a.pub v i
      · simp only [hpi, Bool.false_eq_true, if_false] at hi h1i
        rw [hi] at h1i
        exact absurd h1i (by simp)
      · simp only [hpi, if_true, Bool.and_eq_true] at hi
        obtain ⟨⟨hev, hnone⟩, hrej⟩ := hi
        have hR : ρ.R (κ.cls (a.key v i)) = true := by
          cases hc : ρ.R (κ.cls (a.key v i))
          · simp [hpi, hev, hnone, hrej, hc] at h1i
          · rfl
        obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hrej
        exact recReady_of_touch ρ xw.1 hI (mem_of_lookupIn_eq_some hc) hR hvis
          (hpubmem _ (List.mem_append_left _
            (Protocol.Attempt.mem_entries_of (by simp [hev, hpi])))) rfl
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

/-- **Causal public marks of a sampler at one pair.** For every attempt of `D xw m e`, the
public mark of entry `i` reads only the values of the entries before `i` and of the
programmed entries. -/
def AttPubCausalAt (D : G.Sampler) (xw : G.Stmt × G.Wit) : Prop :=
  ∀ (m : G.Msg) (e : Fin G.μ → G.Ch), ∀ a ∈ (D xw m e).support,
    ∀ (v v' : Fin G.μ → G.Ch) (i : Fin G.μ),
      (∀ j, j < i ∨ G.ev j = false → v j = v' j) → a.pub v i = a.pub v' i

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

/-! ## The statistical hop of the exempt game -/

section RecSim

variable {G : Protocol} {κ : G.Classes} {rel : G.Stmt → G.Wit → Prop} {α : Type}
  (ρ : G.Recovery κ rel) {D : G.Sampler} {xw : G.Stmt × G.Wit}

/-- A transition of the simulated game extends the tables. -/
theorem simStep_support_le (x₀ : G.Stmt) (s : G.Tables × Bool) (d : G.Query)
    (o : G.Answer × (G.Tables × Bool)) (ho : o ∈ (toOracle (simStep x₀) s d).support) :
    s.1.Le o.2.1 := by
  obtain ⟨t, b⟩ := s
  cases d with
  | inl k =>
    simp only [toOracle, simStep, hashStep] at ho
    cases hl : t.lookup k with
    | some e =>
      simp only [hl, Step.toPMF, PMF.support_pure, Set.mem_singleton_iff] at ho
      subst ho
      exact Protocol.Tables.Le.refl _
    | none =>
      simp only [hl, Step.toPMF, PMF.support_map, Set.mem_image] at ho
      obtain ⟨e, _, rfl⟩ := ho
      exact ⟨List.prefix_refl _, List.prefix_append _ _, List.prefix_refl _⟩
  | inr m =>
    simp only [toOracle, simStep, Step.toPMF] at ho
    obtain ⟨e, r, rfl⟩ := mem_support_sampleVec ho
    exact le_traceOut _ _ _ _

/-- A run of the simulated game extends the tables. -/
theorem run_sim_support_le (x₀ : G.Stmt) (A : OracleAdv G.Query G.Answer α)
    (s : G.Tables × Bool) (y : α × (G.Tables × Bool))
    (hy : y ∈ (OracleAdv.run (toOracle (simStep x₀)) A s).support) : s.1.Le y.2.1 := by
  induction A generalizing s with
  | ret a =>
    rw [OracleAdv.run_ret, PMF.support_pure, Set.mem_singleton_iff] at hy
    subst hy
    exact Protocol.Tables.Le.refl _
  | rand p k ih =>
    rw [OracleAdv.run_rand, PMF.mem_support_bind_iff] at hy
    obtain ⟨b, _, hb⟩ := hy
    exact ih b s hb
  | query d k ih =>
    rw [OracleAdv.run_query, PMF.mem_support_bind_iff] at hy
    obtain ⟨o, ho, hy⟩ := hy
    exact (simStep_support_le x₀ s d o ho).trans (ih o.1 o.2 hy)

/-- A recovery ready on the tables `t` is ready on every extension of `t`. -/
theorem RecReady.of_le {x : G.Stmt} {t t' : G.Tables} (h : RecReady ρ x t) (hle : t.Le t') :
    RecReady ρ x t' :=
  h.mono ρ x fun q hq => by
    rcases List.mem_append.mp hq with hq | hq
    · exact List.mem_append_left _ (hle.1.subset hq)
    · exact List.mem_append_right _ (hle.2.1.subset hq)

/-- The flag of a transition of the exempt game stays set. -/
theorem attStepPR_flag (t : G.Tables) (d : G.Query) (o : G.Answer × (G.Tables × Bool))
    (ho : o ∈ (toOracle (attStepPR ρ D xw) (t, true) d).support) : o.2.2 = true := by
  cases d with
  | inl k =>
    simp only [toOracle, attStepPR, realHashStepR] at ho
    cases hl : t.lookup k with
    | some e =>
      simp only [hl, Step.toPMF, PMF.support_pure, Set.mem_singleton_iff] at ho
      subst ho
      rfl
    | none =>
      cases hr : lookupIn t.rej k with
      | some e =>
        simp only [hl, hr, Step.toPMF, PMF.support_pure, Set.mem_singleton_iff] at ho
        subst ho
        simp
      | none =>
        simp only [hl, hr, Step.toPMF, PMF.support_map, Set.mem_image] at ho
        obtain ⟨e, _, rfl⟩ := ho
        rfl
  | inr m =>
    simp only [toOracle, attStepPR, Step.toPMF, attSignPR, PMF.mem_support_bind_iff,
      PMF.support_map, Set.mem_image] at ho
    obtain ⟨e, _, a, _, rfl⟩ := ho
    simp [attSignOutPR]

/-- A run of the exempt game started with the flag set gives every test of `offFlag`
the value `0`. -/
theorem run_attPR_offFlag_true (A : OracleAdv G.Query G.Answer α) (t : G.Tables)
    (g : α × (G.Tables × Bool) → ℝ≥0∞) :
    ∑' y, OracleAdv.run (toOracle (attStepPR ρ D xw)) A (t, true) y * offFlag g y = 0 := by
  refine ENNReal.tsum_eq_zero.mpr fun y => ?_
  obtain ⟨a, t', fl⟩ := y
  cases fl with
  | true => simp [offFlag]
  | false =>
    rw [OracleAdv.run_flag_apply_false_of_true _ (fun t d r t' =>
      (PMF.apply_eq_zero_iff _ _).mpr fun hx => Bool.noConfusion (attStepPR_flag ρ t d _ hx)),
      zero_mul]

/-- **The invariant across a transition of the exempt game** with the flag cleared, on
the outcomes that leave it cleared. -/
theorem recInv_attStepPR (hrec : ρ.CompleteAt D xw) {t : G.Tables}
    (hI : RecInv ρ xw.1 t false false) (d : G.Query) (o : G.Answer × (G.Tables × Bool))
    (ho : o ∈ (toOracle (attStepPR ρ D xw) (t, false) d).support) (hf : o.2.2 = false) :
    RecInv ρ xw.1 o.2.1 false false := by
  have hvis : ∀ (k : G.Key) (c : G.Ch), ∀ q ∈ t.prog ++ t.hash,
      q ∈ ({ t with hash := t.hash ++ [(k, c)] } : G.Tables).prog ++
        ({ t with hash := t.hash ++ [(k, c)] } : G.Tables).hash := fun k c q hq => by
    rcases List.mem_append.mp hq with hq | hq
    · exact List.mem_append_left _ hq
    · exact List.mem_append_right _ (List.mem_append_left _ hq)
  cases d with
  | inl k =>
    simp only [toOracle, attStepPR, realHashStepR] at ho
    cases hl : t.lookup k with
    | some e =>
      simp only [hl, Step.toPMF, PMF.support_pure, Set.mem_singleton_iff] at ho
      subst ho
      exact hI
    | none =>
      cases hr : lookupIn t.rej k with
      | some e =>
        simp only [hl, hr, Step.toPMF, PMF.support_pure, Set.mem_singleton_iff] at ho
        subst ho
        exact hI.mono ρ xw.1 (hvis k e) rfl
      | none =>
        simp only [hl, hr, Step.toPMF, PMF.support_map, Set.mem_image] at ho
        obtain ⟨e, _, rfl⟩ := ho
        exact hI.mono ρ xw.1 (hvis k e) rfl
  | inr m =>
    simp only [toOracle, attStepPR, Step.toPMF, attSignPR, PMF.mem_support_bind_iff,
      PMF.support_map, Set.mem_image] at ho
    obtain ⟨e, _, a, ha, rfl⟩ := ho
    exact ⟨fun h' => absurd h' (by simp), fun _ => (recInv_attSignOut ρ hrec ha hI).2 hf⟩

/-- **An exempt landing makes the recovery ready on the visible run.** For a sampler
with causal public marks, from tables satisfying the invariant, an attempt that sets the
flag of `attSignOut` and not the flag of the exempt game has its hidden entries against
the visible entries at undefined points, and the recovery is ready on the tables of the
answer of its trace against the visible entries. -/
theorem recReady_traceOut_of_land (hpc : G.AttPubCausalAt D xw) {m : G.Msg}
    {e : Fin G.μ → G.Ch} {a : G.Attempt} (ha : a ∈ (D xw m e).support) {t : G.Tables}
    (hI : RecInv ρ xw.1 t false false) (hf : attFlagR ρ t e a = false)
    (hl : (attSignOut t false m e a).2.2 = true) :
    a.hidFresh t.lookup (a.vals t.lookup e) = true ∧
      RecReady ρ xw.1 (traceOut t false m (a.trace (a.vals t.lookup e))).2.1 := by
  set v := a.vals t.lookupAll e with hv
  set w := a.vals t.lookup e with hw
  simp only [attFlagR, ← hv, ← hw, Bool.or_eq_false_iff, List.any_eq_false, List.mem_finRange,
    true_implies] at hf
  obtain ⟨h1, -⟩ := hf
  simp only [attSignOut, ← hv, Bool.false_or, List.any_eq_true, List.mem_finRange,
    true_and] at hl
  set S := Finset.univ.filter fun i => a.pub v i = true ∧ G.ev i = true ∧
    (t.lookup (a.key v i)).isNone = true ∧ (lookupIn t.rej (a.key v i)).isSome = true with hSdef
  have hS : S.Nonempty := by
    obtain ⟨i, hi⟩ := hl
    refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩⟩
    have h1i := h1 i
    cases hpi : a.pub v i
    · simp only [hpi, Bool.false_eq_true, if_false] at hi h1i
      rw [hi] at h1i
      exact absurd h1i (by simp)
    · simp only [hpi, if_true, Bool.and_eq_true] at hi
      exact ⟨rfl, hi.1.1, hi.1.2, hi.2⟩
  set j := S.min' hS with hj
  have hjS : j ∈ S := S.min'_mem hS
  obtain ⟨hpj, hevj, hnj, hrj⟩ := (Finset.mem_filter.mp hjS).2
  have hmin : ∀ i, i < j → ¬ (a.pub v i = true ∧ G.ev i = true ∧
      (t.lookup (a.key v i)).isNone = true ∧ (lookupIn t.rej (a.key v i)).isSome = true) :=
    fun i hij hi => absurd (S.min'_le i (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩))
      (not_le.mpr hij)
  -- the runs against the visible and against all entries agree below `j`
  have hagree : ∀ i, i < j → w i = v i := by
    refine effVec_congr_lt _ _ a.key a.key_causal e j fun i hij => ?_
    change (if G.ev i then t.lookup else fun _ => none) (a.key v i) =
      (if G.ev i then t.lookupAll else fun _ => none) (a.key v i)
    cases hev : G.ev i
    · rfl
    · simp only [if_true]
      refine (Protocol.lookupAll_eq_lookup fun hn => ?_).symm
      cases hr : lookupIn t.rej (a.key v i) with
      | none => rfl
      | some c =>
        exfalso
        cases hpi : a.pub v i
        · have h1i := h1 i
          simp only [hpi, Bool.false_eq_true, if_false] at h1i
          have : (t.lookupAll (a.key v i)).isSome = true := by
            simp [Protocol.Tables.lookupAll, Option.isNone_iff_eq_none.mp hn, hr]
          rw [this] at h1i
          exact absurd h1i (by simp)
        · exact hmin i hij ⟨hpi, hev, hn, by simp [hr]⟩
  have hkj : a.key w j = a.key v j := a.key_causal w v j hagree
  have hpw : a.pub w j = a.pub v j := hpc m e a ha w v j fun i hi => by
    rcases hi with hi | hi
    · exact hagree i hi
    · rw [hw, a.vals_eq_of_fresh _ e i (by simp [hi]), hv,
        a.vals_eq_of_fresh _ e i (by simp [hi])]
  have hwj : w j = e j := by
    rw [hw, a.vals_eq_of_fresh _ e j (by rw [← hw, hkj]; simp [Option.isNone_iff_eq_none.mp hnj])]
  have h1j := h1 j
  simp only [hpj, hevj, hnj, hrj, if_true, Bool.true_and] at h1j
  have hR : ρ.R (κ.cls (a.key v j)) = true := by
    cases hc : ρ.R (κ.cls (a.key v j))
    · exact absurd (by simp [hc]) h1j
    · rfl
  have hfr : a.hidFresh t.lookup w = true := by
    cases hc : a.hidFresh t.lookup w
    · exact absurd (by simp [hc]) h1j
    · rfl
  refine ⟨hfr, ?_⟩
  obtain ⟨c, hc⟩ := Option.isSome_iff_exists.mp hrj
  have hL := le_traceOut t false m (a.trace w)
  refine recReady_of_touch ρ xw.1 hI (p := (a.key v j, c)) (mem_of_lookupIn_eq_some hc) hR
    (fun q hq => ?_) (q := (a.key w j, w j)) ?_ hkj
  · rcases List.mem_append.mp hq with hq | hq
    · exact List.mem_append_left _ (hL.1.subset hq)
    · exact List.mem_append_right _ (hL.2.1.subset hq)
  · refine List.mem_append_right _ ?_
    change _ ∈ (programAll (hashAll t (a.evEntries w)) false (a.pubEntries w)).1.hash
    rw [(programAll_tables _ _ _).1]
    exact List.mem_append_right _ (List.mem_filter.mpr
      ⟨Protocol.Attempt.mem_entries_of (by simp [hevj, hpw, hpj]), by simp [hkj, hnj]⟩)

/-- **The signing answer of the exempt game on the outcomes with the flag cleared.** For
a sampler with causal public marks, from tables satisfying the invariant and for a test
`F` with values in `[0, 1]` that reads neither the hidden entries nor the flag and is `1`
on tables on which the recovery is ready, the test of the signing answer of an attempt
with the flag cleared is at most the test of the answer of its trace against the
visible entries when its hidden points are undefined there, and `0` otherwise. -/
theorem offFlag_attSignOutPR_le_land (hpc : G.AttPubCausalAt D xw) {m : G.Msg}
    {e : Fin G.μ → G.Ch} {a : G.Attempt} (ha : a ∈ (D xw m e).support) {t : G.Tables}
    (hI : RecInv ρ xw.1 t false false) (F : G.Answer × (G.Tables × Bool) → ℝ≥0∞)
    (hF : ∀ y, F y ≤ 1) (hFr : RejInsensitive F) (hFf : FlagInsensitive F)
    (hFs : ∀ y, RecReady ρ xw.1 y.2.1 → F y = 1) :
    offFlag F (attSignOutPR ρ t false m e a) ≤
      if a.hidFresh t.lookup (a.vals t.lookup e) then
        F (traceOut t false m (a.trace (a.vals t.lookup e))) else 0 := by
  cases hf : attFlagR ρ t e a with
  | true => simp [offFlag, attSignOutPR, hf]
  | false =>
    cases hl : (attSignOut t false m e a).2.2 with
    | false =>
      have heq : attSignOutPR ρ t false m e a = attSignOut t false m e a :=
        Prod.ext rfl (Prod.ext rfl (by rw [hl]; simp [attSignOutPR, hf]))
      rw [heq]
      exact offFlag_attSignOut_le F hFr hFf t false m e a
    | true =>
      obtain ⟨hfr, hrd⟩ := recReady_traceOut_of_land ρ hpc ha hI hf hl
      rw [if_pos hfr, hFs _ hrd]
      exact (offFlag_le F _).trans (hF _)

/-- **A hash query of the exempt game.** From tables satisfying the invariant and for a
test `F` with values in `[0, 1]` that is `1` on tables on which the recovery is ready,
on the outcomes with the flag cleared a test of a hash query of the exempt game is at
most the same test of the hash query of the simulated game. -/
theorem realHashStepR_le_hashStep {t : G.Tables} (hI : RecInv ρ xw.1 t false false)
    (k : G.Key) (F : G.Answer × (G.Tables × Bool) → ℝ≥0∞) (hF : ∀ y, F y ≤ 1)
    (hFs : ∀ y, RecReady ρ xw.1 y.2.1 → F y = 1) :
    ∑' o, (realHashStepR ρ t false k).toPMF o * offFlag F o ≤
      ∑' o, (hashStep t false k).toPMF o * F o := by
  simp only [realHashStepR, hashStep]
  cases hl : t.lookup k with
  | some e => exact ENNReal.tsum_le_tsum fun o => mul_le_mul_right (offFlag_le F o) _
  | none =>
    cases hr : lookupIn t.rej k with
    | some c =>
      simp only [Step.toPMF]
      rw [tsum_pure_mul]
      cases hR : ρ.R (κ.cls k)
      · simp [offFlag]
      · have hone : ∀ c' : G.Ch,
            F (.inl c', ({ t with hash := t.hash ++ [(k, c')] }, false)) = 1 := fun c' =>
          hFs _ (recReady_of_touch ρ xw.1 hI (mem_of_lookupIn_eq_some hr) hR
            (fun q hq => by
              rcases List.mem_append.mp hq with hq | hq
              · exact List.mem_append_left _ hq
              · exact List.mem_append_right _ (List.mem_append_left _ hq))
            (q := (k, c')) (List.mem_append_right _ (List.mem_append_right _ (by simp))) rfl)
        calc _ ≤ (1 : ℝ≥0∞) := (offFlag_le F _).trans (hF _)
          _ = _ := by simp only [tsum_map_mul', hone, mul_one, PMF.tsum_coe]
    | none => exact ENNReal.tsum_le_tsum fun o => mul_le_mul_right (offFlag_le F o) _

/-- **A signing query of the exempt game.** For a sampler with statistical HVZK
distance `δ` and causal public marks at the pair, from tables satisfying the invariant
and for a test `F` with values in `[0, 1]` that reads neither the hidden entries nor the
flag and is `1` on tables on which the recovery is ready, on the outcomes with the flag
cleared a test of a signing query of the exempt game is at most the same test of the
simulated signing query plus `δ`. -/
theorem attSignPR_le_simSign {δ : ℝ≥0∞} (hZK : G.AttHVZKAt D xw δ)
    (hpc : G.AttPubCausalAt D xw) {t : G.Tables} (hI : RecInv ρ xw.1 t false false)
    (m : G.Msg) (F : G.Answer × (G.Tables × Bool) → ℝ≥0∞) (hF : ∀ y, F y ≤ 1)
    (hFr : RejInsensitive F) (hFf : FlagInsensitive F)
    (hFs : ∀ y, RecReady ρ xw.1 y.2.1 → F y = 1) :
    ∑' o, attSignPR ρ D xw (t, false) m o * offFlag F o ≤
      ∑' o, sampleVec G (simSignOut xw.1 t false m) o * F o + δ := by
  simp only [attSignPR, sampleVec, tsum_bind_mul, tsum_map_mul']
  calc ∑' e, PMF.uniformOfFintype (Fin G.μ → G.Ch) e * ∑' a, D xw m e a *
        offFlag F (attSignOutPR ρ t false m e a)
      ≤ ∑' e, PMF.uniformOfFintype (Fin G.μ → G.Ch) e * ∑' a, D xw m e a *
          (if a.hidFresh t.lookup (a.vals t.lookup e) then
            F (traceOut t false m (a.trace (a.vals t.lookup e))) else 0) :=
        ENNReal.tsum_le_tsum fun e => mul_le_mul_right
          (ENNReal.tsum_le_tsum fun a => by
            by_cases ha : D xw m e a = 0
            · simp [ha]
            · exact mul_le_mul_right (offFlag_attSignOutPR_le_land ρ hpc
                ((PMF.mem_support_iff _ _).mpr ha) hI F hF hFr hFf hFs) _) _
    _ ≤ _ := hZK m t.lookup (fun tr => F (traceOut t false m tr)) fun _ => hF _

/-- **One transition of the exempt game.** For a sampler with statistical HVZK
distance `δ` and causal public marks at the pair, from tables satisfying the invariant
and a test `F` with values in `[0, 1]` that reads neither the hidden entries nor the
flag and is `1` on tables on which the recovery is ready, on the outcomes with the flag
cleared a test of one transition of the exempt game is at most the same test of one
simulated transition, plus `δ` for a signing query. -/
theorem attStepPR_le_simStep {δ : ℝ≥0∞} (hZK : G.AttHVZKAt D xw δ)
    (hpc : G.AttPubCausalAt D xw)
    {t : G.Tables} (hI : RecInv ρ xw.1 t false false) (d : G.Query)
    (F : G.Answer × (G.Tables × Bool) → ℝ≥0∞) (hF : ∀ y, F y ≤ 1) (hFr : RejInsensitive F)
    (hFf : FlagInsensitive F) (hFs : ∀ y, RecReady ρ xw.1 y.2.1 → F y = 1) :
    ∑' o, toOracle (attStepPR ρ D xw) (t, false) d o * offFlag F o ≤
      ∑' o, toOracle (simStep xw.1) (t, false) d o * F o + (if d.isRight then δ else 0) := by
  cases d with
  | inl k => exact le_add_right (realHashStepR_le_hashStep ρ hI k F hF hFs)
  | inr m => exact attSignPR_le_simSign ρ hZK hpc hI m F hF hFr hFf hFs

/-- **Statistical hop for runs of the exempt game.** For a recovery complete at the
sampler with statistical HVZK distance `δ` and causal public marks at the pair, a run
with at most `h` hash and `q` signing queries from tables satisfying the invariant, and
a test `g` with values in `[0, 1]`
that reads neither the hidden entries nor the flag and is `1` whenever the recovery
succeeds on the visible entries, the test on the outcomes with the flag cleared is at
most the test on the simulated run plus `q·δ`. -/
theorem run_attPR_le_sim (hrec : ρ.CompleteAt D xw) {δ : ℝ≥0∞}
    (hZK : G.AttHVZKAt D xw δ) (hpc : G.AttPubCausalAt D xw)
    (A : OracleAdv G.Query G.Answer α) (h q : ℕ)
    (hA : IsQueryBound₂ A h q) (t : G.Tables) (hI : RecInv ρ xw.1 t false false)
    (g : α × (G.Tables × Bool) → ℝ≥0∞) (hg : ∀ y, g y ≤ 1) (hgr : RejInsensitive g)
    (hgf : FlagInsensitive g) (hgs : ∀ y, recTest ρ xw.1 y.2.1 = true → g y = 1) :
    ∑' y, OracleAdv.run (toOracle (attStepPR ρ D xw)) A (t, false) y * offFlag g y ≤
      ∑' y, OracleAdv.run (toOracle (simStep xw.1)) A (t, false) y * g y + q * δ := by
  induction A generalizing h q t with
  | ret a =>
    simp only [OracleAdv.run_ret, tsum_pure_mul]
    exact (offFlag_le g _).trans le_self_add
  | rand p k ih =>
    simp only [OracleAdv.run_rand, tsum_bind_mul]
    calc _ ≤ ∑' b, p b * (∑' y, OracleAdv.run (toOracle (simStep xw.1)) (k b) (t, false) y *
            g y + q * δ) := ENNReal.tsum_le_tsum fun b => mul_le_mul_right (ih b h q (hA b) t hI) _
      _ = _ := by
          simp only [mul_add]
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  | query d k ih =>
    simp only [OracleAdv.run_query, tsum_bind_mul]
    set Y : G.Answer × (G.Tables × Bool) → ℝ≥0∞ := fun o =>
      ∑' y, OracleAdv.run (toOracle (simStep xw.1)) (k o.1) o.2 y * g y with hY
    have hY1 : ∀ o, Y o ≤ 1 := fun o =>
      (ENNReal.tsum_le_tsum fun y => mul_le_of_le_one_right' (hg y)).trans
        (le_of_eq (PMF.tsum_coe _))
    have hYr : RejInsensitive Y := fun o l =>
      tsum_run_sim_setRej xw.1 (k o.1) g hgr o.2 l
    have hYf : FlagInsensitive Y := fun o c =>
      (tsum_run_sim_setFlag xw.1 (k o.1) g hgf o.2.1 c).trans
        (tsum_run_sim_setFlag xw.1 (k o.1) g hgf o.2.1 o.2.2).symm
    have hYs : ∀ o, RecReady ρ xw.1 o.2.1 → Y o = 1 := fun o ho => by
      refine (tsum_congr fun y => ?_).trans
        (PMF.tsum_coe (OracleAdv.run (toOracle (simStep xw.1)) (k o.1) o.2))
      by_cases hy : y ∈ (OracleAdv.run (toOracle (simStep xw.1)) (k o.1) o.2).support
      · rw [hgs y (recTest_of_recReady ρ xw.1
          (RecReady.of_le ρ ho (run_sim_support_le xw.1 _ _ y hy))), mul_one]
      · rw [(PMF.apply_eq_zero_iff _ _).mpr hy, zero_mul]
    obtain ⟨h', q', hq', hk⟩ := isQueryBound₂_query_cases d k h q hA
    have hpt : ∀ o ∈ (toOracle (attStepPR ρ D xw) (t, false) d).support,
        ∑' y, OracleAdv.run (toOracle (attStepPR ρ D xw)) (k o.1) o.2 y * offFlag g y ≤
          offFlag Y o + q' * δ := by
      rintro ⟨r, t', fl⟩ ho
      cases fl with
      | true =>
        rw [run_attPR_offFlag_true]
        exact zero_le
      | false => exact ih r h' q' (hk r) t' (recInv_attStepPR ρ hrec hI d _ ho rfl)
    calc _ ≤ ∑' o, toOracle (attStepPR ρ D xw) (t, false) d o * (offFlag Y o + q' * δ) :=
          ENNReal.tsum_le_tsum fun o => by
            by_cases ho : o ∈ (toOracle (attStepPR ρ D xw) (t, false) d).support
            · exact mul_le_mul_right (hpt o ho) _
            · simp [(PMF.apply_eq_zero_iff _ _).mpr ho]
      _ = ∑' o, toOracle (attStepPR ρ D xw) (t, false) d o * offFlag Y o + q' * δ := by
          simp only [mul_add]
          rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
      _ ≤ ∑' o, toOracle (simStep xw.1) (t, false) d o * Y o +
            (if d.isRight then δ else 0) + q' * δ :=
          add_le_add (attStepPR_le_simStep ρ hZK hpc hI d Y hY1 hYr hYf hYs) le_rfl
      _ = _ := by rw [add_assoc, ← hq', ite_add_mul_eq]

end RecSim

end CatCrypt.Crypto.FiatShamirROM
