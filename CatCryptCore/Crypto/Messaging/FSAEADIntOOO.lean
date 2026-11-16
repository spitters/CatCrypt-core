/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.FSAEADInt

/-!
# FS-AEAD integrity with out-of-order delivery

The FS-AEAD integrity game with immediate decryption (Alwen, Coretti and Dodis, §5) for a
receiver after the Signal Double Ratchet specification: the receiver keeps the next position
`nr` of its chain and a store of skipped positions. A decryption at a position `j ≥ nr` steps
the chain when `j - nr ≤ maxSkip` (Signal's `MAX_SKIP`) and the store with the skipped positions
holds at most `maxStored` positions, and stores the positions from `nr` below `j`; a decryption
at a position `j < nr` uses a stored position. On success the position is used up and its
delivered flag is set. The real game decrypts under the key at the position of the chain, the
ideal game answers the plaintext of an undelivered honest ciphertext at the position.

The real and the ideal game agree until a decryption at an available position whose answer
under the key differs from the decryption from the log of the undelivered ciphertexts. Before
that event every accepted decryption is at the position of an honest ciphertext, so the next
position `nr` is at most the number of encryptions, and every available position is below
`q + maxSkip + 1` for an adversary with at most `q` encryptions. The adversary `fsOOORed` keeps
the bookkeeping of the receiver and forwards the decryptions at available positions below
`q + maxSkip + 1` to the FS-AEAD integrity game `fsaead_int_game`; until the event its runs
against the keyed oracle of `FSAEADInt` are the runs of the out-of-order game, so the bound of
`fsaead_int_advantage_le` at `q + maxSkip + 1` positions applies.

## Main definitions

* `FSOOOSt`, `fsOOOKey`, `fsOOOStep`, `fsIntOOOOracle`, `fsaead_int_ooo_game`,
  `FSAEAD_Int_OOO_Advantage` — the out-of-order integrity game
* `fsOOOBad`, `fsOOOFlag` — the event and its probability in the real game
* `fsOOORedImpl`, `fsOOORed` — the adversary of the integrity game with in-place positions
* `fsIntEncCost` — the encryption queries

## Main results

* `run_map_eq_of_sim_bad` — two deterministic oracles related until a stop or a flag give the
  same flag distribution
* `fsaead_int_ooo_advantage_le_flag` — the advantage is at most the probability of the event
* `fsOOOFlag_eq_fsKeyFlag` — the event of the out-of-order game is the event of the keyed oracle
  at `fsOOORed`
* `fsaead_int_ooo_advantage_le` — for an adversary with at most `q` encryptions, the advantage is
  at most the FS-PRG advantage of `fsIntPost` and the AEAD advantages of `fsIntRed` at
  `fsOOORed` with `q + maxSkip + 1` positions

## References

* J. Alwen, S. Coretti, Y. Dodis, *The Double Ratchet: Security Notions, Proofs, and
  Modularization for the Signal Protocol*, EUROCRYPT 2019, §4.3 and §5
* T. Perrin, M. Marlinspike, *The Double Ratchet Algorithm*, Signal specification, 2016,
  §3.5 (`MAX_SKIP`)
-/

set_option autoImplicit false

@[expose] public section

namespace CatCrypt.Crypto.Messaging

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Assumptions
open scoped ENNReal

/-! ## Deterministic oracles related until a stop or a flag -/

section SimBad

variable {D R α S S' : Type}

/-- A run of a deterministic oracle from a state of `P`, which every call keeps with the same
value of `g`, ends with that value of `g`. -/
theorem run_pure_map_eq_of_frozen (F : S → D → R × S) (P : S → Prop) (g : S → Bool)
    (h : ∀ t d, P t → P (F t d).2 ∧ g (F t d).2 = g t) (B : OracleAdv D R α) (t : S)
    (ht : P t) :
    (OracleAdv.run (fun s d => PMF.pure (F s d)) B t).map (fun y => g y.2) = PMF.pure (g t) := by
  refine OracleAdv.run_map_eq_pure_of_frozen _ P g ?_ B t ht
  intro t d ht x hx
  rw [PMF.mem_support_pure_iff] at hx
  subst hx
  exact h t d ht

/-- **Deterministic oracles related until a stop or a flag.** Let the states be related by
`Rel n` for the remaining budget `n`, with equal flags `g` and `g'`, and with `Stop` related only
to `Stop'`. Let the flags stay set, let `Stop` and `Stop'` be kept with their flags, and let a
call of cost at most `n` from related states outside `Stop` with the flag clear give equal
flags, lead from `Stop` to `Stop'` and, outside `Stop` with the flag clear, give the same answer
and states related at the budget `n - cost d`. Then the runs of an adversary within the budget
give the same flag distribution. -/
theorem run_map_eq_of_sim_bad (F : S → D → R × S) (F' : S' → D → R × S')
    (g : S → Bool) (g' : S' → Bool) (cost : D → ℕ) (Rel : ℕ → S → S' → Prop)
    (Stop : S → Prop) (Stop' : S' → Prop)
    (hg : ∀ s d, g s = true → g (F s d).2 = true)
    (hg' : ∀ s d, g' s = true → g' (F' s d).2 = true)
    (hStop : ∀ s d, Stop s → Stop (F s d).2 ∧ g (F s d).2 = g s)
    (hStop' : ∀ s d, Stop' s → Stop' (F' s d).2 ∧ g' (F' s d).2 = g' s)
    (hRel : ∀ n s s', Rel n s s' → g s = g' s' ∧ (Stop s → Stop' s'))
    (hstep : ∀ n s s' d, Rel n s s' → ¬ Stop s → g s = false → cost d ≤ n →
      g (F s d).2 = g' (F' s' d).2 ∧
      (g (F s d).2 = false → Stop (F s d).2 → Stop' (F' s' d).2) ∧
      (g (F s d).2 = false → ¬ Stop (F s d).2 →
        (F s d).1 = (F' s' d).1 ∧ Rel (n - cost d) (F s d).2 (F' s' d).2))
    (A : OracleAdv D R α) (n : ℕ) (hA : A.IsQueryBoundBy cost n) (s : S) (s' : S')
    (hs : Rel n s s') :
    (OracleAdv.run (fun s d => PMF.pure (F s d)) A s).map (fun y => g y.2) =
      (OracleAdv.run (fun s d => PMF.pure (F' s d)) A s').map (fun y => g' y.2) := by
  have frzT : ∀ {T : Type} (F : T → D → R × T) (g : T → Bool),
      (∀ s d, g s = true → g (F s d).2 = true) → ∀ (B : OracleAdv D R α) (t : T), g t = true →
      (OracleAdv.run (fun s d => PMF.pure (F s d)) B t).map (fun y => g y.2) = PMF.pure true :=
    fun F g h B t ht => by
      rw [run_pure_map_eq_of_frozen F (fun t => g t = true) g
        (fun t d ht => ⟨h t d ht, by rw [h t d ht, ht]⟩) B t ht, ht]
  induction A generalizing n s s' with
  | ret a => simp [PMF.pure_map, (hRel n s s' hs).1]
  | rand p k ih =>
    simp only [OracleAdv.run_rand, PMF.map_bind]
    congr 1
    funext b
    exact ih b n (hA b) s s' hs
  | query d k ih =>
    obtain ⟨hgs, hRS⟩ := hRel n s s' hs
    by_cases hS : Stop s
    · rw [run_pure_map_eq_of_frozen F Stop g hStop _ s hS,
        run_pure_map_eq_of_frozen F' Stop' g' hStop' _ s' (hRS hS), hgs]
    by_cases hg1 : g s = true
    · rw [frzT F g hg _ s hg1, frzT F' g' hg' _ s' (hgs ▸ hg1)]
    have hg0 : g s = false := by simpa using hg1
    obtain ⟨hgeq, hstop, hlive⟩ := hstep n s s' d hs hS hg0 hA.1
    simp only [OracleAdv.run_query, PMF.pure_bind]
    by_cases hT : g (F s d).2 = true
    · rw [frzT F g hg _ _ hT, frzT F' g' hg' _ _ (hgeq ▸ hT)]
    have hT0 : g (F s d).2 = false := by simpa using hT
    by_cases hS' : Stop (F s d).2
    · rw [run_pure_map_eq_of_frozen F Stop g hStop _ _ hS',
        run_pure_map_eq_of_frozen F' Stop' g' hStop' _ _ (hstop hT0 hS'), hgeq]
    obtain ⟨hans, hrel⟩ := hlive hT0 hS'
    rw [hans]
    exact ih _ _ (hA.2 _) _ _ hrel

end SimBad

/-! ## The out-of-order integrity game -/

section Game

variable {Sa W Ct : Type} [SampleableType W] [DecidableEq W] [DecidableEq Ct]

/-- The state of the out-of-order integrity game: the state of the FS-AEAD integrity game, the
next position `nr` of the receiving chain, the skipped positions of the store and the delivered
flag of each position. -/
structure FSOOOSt (Sa W Ct : Type) where
  /-- The sender's chain, the initial state, the log and the corruption flag. -/
  fs : FSIntSt Sa W Ct
  /-- The next position of the receiving chain. -/
  nr : ℕ
  /-- The skipped positions whose keys are stored. -/
  store : List ℕ
  /-- The delivered flag of each position. -/
  dlv : ℕ → Bool

/-- The initial state of the out-of-order game from the state `sa` of the chain. -/
def fsOOOInit (sa : Sa) : FSOOOSt Sa W Ct := ⟨⟨sa, sa, [], false⟩, 0, [], fun _ => false⟩

/-- The key lookup of the receiver at the position `j`, from the next position `nr` and the
store: at a position from `nr` on, within `maxSkip` positions and with at most `maxStored`
stored positions, the next position `j + 1` and the store with the positions from `nr` below
`j`; at a stored position, the store without it; `none` otherwise. -/
def fsOOOKey (maxSkip maxStored nr : ℕ) (store : List ℕ) (j : ℕ) : Option (ℕ × List ℕ) :=
  if nr ≤ j then
    if j - nr ≤ maxSkip ∧ store.length + (j - nr) ≤ maxStored then
      some (j + 1, List.range' nr (j - nr) ++ store)
    else none
  else if j ∈ store then some (nr, store.erase j) else none

/-- The key lookup of the receiver in the state `s`, refused after the corruption. -/
def fsOOOAt (maxSkip maxStored : ℕ) (s : FSOOOSt Sa W Ct) (j : ℕ) : Option (ℕ × List ℕ) :=
  if s.fs.corr then none else fsOOOKey maxSkip maxStored s.nr s.store j

/-- Decryption from the log of the undelivered honest ciphertexts. -/
def FSOOOSt.logDecU (s : FSOOOSt Sa W Ct) (j : ℕ) (ad : W) (c : Ct) : Option W :=
  if s.dlv j then none else s.fs.logDec j ad c

/-- The state after an accepted decryption at `j` with the lookup result `k`. -/
def FSOOOSt.accept (s : FSOOOSt Sa W Ct) (j : ℕ) (k : ℕ × List ℕ) : FSOOOSt Sa W Ct :=
  { s with nr := k.1, store := k.2, dlv := Function.update s.dlv j true }

/-- A call of the out-of-order integrity oracle: `enc m` encrypts under the next key of the
sender's chain and logs the ciphertext; `dec j ad c` looks up the position `j` and, when it is
available, decrypts under the key at `j` of the chain from the initial state (`ideal = false`)
or from the log of the undelivered ciphertexts (`ideal = true`), and on success uses up `j`;
`corrupt` returns the state of the sender and refuses later decryptions. -/
def fsOOOStep (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (maxSkip maxStored : ℕ)
    (ideal : Bool) (s : FSOOOSt Sa W Ct) :
    FSIntQuery W Ct → FSIntAns Sa Ct W × FSOOOSt Sa W Ct
  | .enc m => (.ct (D.encrypt (G.stretch s.fs.cur).1 m.1 m.2),
      ⟨⟨(G.stretch s.fs.cur).2, s.fs.init,
        (s.fs.log.length, m.1, m.2, D.encrypt (G.stretch s.fs.cur).1 m.1 m.2) :: s.fs.log,
        s.fs.corr⟩, s.nr, s.store, s.dlv⟩)
  | .dec j ad c =>
    match fsOOOAt maxSkip maxStored s j with
    | none => (.dec none, s)
    | some k =>
      (.dec (if ideal then s.logDecU j ad c else D.decrypt (chainKey G s.fs.init j) c ad),
        if (if ideal then s.logDecU j ad c else D.decrypt (chainKey G s.fs.init j) c ad).isSome
        then s.accept j k else s)
  | .corrupt => (.state s.fs.cur, ⟨⟨s.fs.cur, s.fs.init, s.fs.log, true⟩, s.nr, s.store, s.dlv⟩)

/-- The out-of-order integrity oracle: the point mass at `fsOOOStep`. -/
noncomputable def fsIntOOOOracle (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (maxSkip maxStored : ℕ) (ideal : Bool) (s : FSOOOSt Sa W Ct) (d : FSIntQuery W Ct) :
    PMF (FSIntAns Sa Ct W × FSOOOSt Sa W Ct) :=
  PMF.pure (fsOOOStep G D maxSkip maxStored ideal s d)

/-- The event of the out-of-order game: a decryption at an available position whose answer
under the key differs from the decryption from the log of the undelivered ciphertexts. -/
def fsOOOBad (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (maxSkip maxStored : ℕ)
    (s : FSOOOSt Sa W Ct) : FSIntQuery W Ct → Bool
  | .dec j ad c => (fsOOOAt maxSkip maxStored s j).isSome &&
      decide (D.decrypt (chainKey G s.fs.init j) c ad ≠ s.logDecU j ad c)
  | _ => false

/-- The cost of the encryption queries: `1` for an encryption, `0` otherwise. -/
def fsIntEncCost : FSIntQuery W Ct → ℕ
  | .enc _ => 1
  | _ => 0

variable [SampleableType Ct] [Fintype Sa] [Nonempty Sa]

/-- **The FS-AEAD integrity game with out-of-order delivery**: a uniform initial state of the
chain, and the run of the adversary against `fsIntOOOOracle`. -/
noncomputable def fsaead_int_ooo_game (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (maxSkip maxStored : ℕ) (ideal : Bool)
    (A : OracleAdv (FSIntQuery W Ct) (FSIntAns Sa Ct W) Bool) : SPComp Bool :=
  liftPMF ((PMF.uniformFintype Sa).bind fun sa =>
    (OracleAdv.run (fsIntOOOOracle G D maxSkip maxStored ideal) A (fsOOOInit sa)).map Prod.fst)

/-- **The FS-AEAD integrity advantage with out-of-order delivery**: real decryption against
decryption from the log of the undelivered ciphertexts. -/
noncomputable def FSAEAD_Int_OOO_Advantage (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (maxSkip maxStored : ℕ) (A : OracleAdv (FSIntQuery W Ct) (FSIntAns Sa Ct W) Bool) : ℝ≥0∞ :=
  Advantage (fsaead_int_ooo_game G D maxSkip maxStored false A)
    (fsaead_int_ooo_game G D maxSkip maxStored true A)

omit [SampleableType Ct] [Fintype Sa] [Nonempty Sa] in
/-- The probability that the run of `A` against the real out-of-order oracle from the state
`sa` sets the event. -/
noncomputable def fsOOOFlag (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (maxSkip maxStored : ℕ)
    (sa : Sa) (A : OracleAdv (FSIntQuery W Ct) (FSIntAns Sa Ct W) Bool) : PMF Bool :=
  (OracleAdv.run (OracleAdv.flagWhen
      (fun s d _ => fsOOOBad G D maxSkip maxStored s d = true)
      (fsIntOOOOracle G D maxSkip maxStored false)) A (fsOOOInit sa, false)).map fun y => y.2.2

omit [SampleableType Ct] in
/-- **Identical until the event.** The out-of-order integrity advantage is at most the
probability of the event in the real game. -/
theorem fsaead_int_ooo_advantage_le_flag (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (maxSkip maxStored : ℕ) (A : OracleAdv (FSIntQuery W Ct) (FSIntAns Sa Ct W) Bool) :
    FSAEAD_Int_OOO_Advantage G D maxSkip maxStored A ≤
      ((PMF.uniformFintype Sa).bind fun sa => fsOOOFlag G D maxSkip maxStored sa A) true := by
  let bad : FSOOOSt Sa W Ct → FSIntQuery W Ct → FSIntAns Sa Ct W × FSOOOSt Sa W Ct → Prop :=
    fun s d _ => fsOOOBad G D maxSkip maxStored s d = true
  have hbad : ∀ s d x, ¬ bad s d x → fsIntOOOOracle G D maxSkip maxStored true s d x =
      fsIntOOOOracle G D maxSkip maxStored false s d x := by
    intro s d x h
    cases d with
    | dec j ad c =>
      simp only [bad, fsOOOBad] at h
      cases hk : fsOOOAt maxSkip maxStored s j with
      | none => simp [fsIntOOOOracle, fsOOOStep, hk]
      | some k =>
        simp only [hk, Option.isSome_some, Bool.true_and, decide_eq_true_eq, not_not] at h
        simp [fsIntOOOOracle, fsOOOStep, hk, h]
    | enc m => rfl
    | corrupt => rfl
  have hflag : ∀ sa : Sa, (OracleAdv.run (OracleAdv.flagWhen bad
      (fsIntOOOOracle G D maxSkip maxStored false)) A (fsOOOInit sa, false)).toOuterMeasure
        {y | y.2.2 = true} = fsOOOFlag G D maxSkip maxStored sa A true := by
    intro sa
    rw [← OracleGameUpToBad.map_flag_apply]
    rfl
  unfold FSAEAD_Int_OOO_Advantage fsaead_int_ooo_game
  simp only [Advantage, prTrue_liftPMF]
  refine max_le (tsub_le_iff_left.mpr ?_) (tsub_le_iff_left.mpr ?_)
  · refine bind_apply_true_le_add _ _ _ _ fun sa => ?_
    rw [OracleGameUpToBad.map_fst_apply_true, OracleGameUpToBad.map_fst_apply_true, ← hflag,
      ← OracleAdv.run_flagWhen_prob_eq bad _ _ hbad]
    exact OracleAdv.run_toOuterMeasure_le_add_flagWhen bad _ _
      (fun s d x hx => (hbad s d x hx).symm) A _ _
  · refine bind_apply_true_le_add _ _ _ _ fun sa => ?_
    rw [OracleGameUpToBad.map_fst_apply_true, OracleGameUpToBad.map_fst_apply_true, ← hflag]
    exact OracleAdv.run_toOuterMeasure_le_add_flagWhen bad _ _ hbad A _ _

end Game

/-! ## The bookkeeping of the receiver and the adversary of the integrity game -/

section Red

variable {Sa W Ct : Type} [SampleableType W] [DecidableEq W] [DecidableEq Ct]

/-- The two cases of an available position: a step of the chain within the skip window, or a
stored position. -/
theorem fsOOOKey_eq_some {maxSkip maxStored nr j : ℕ} {store : List ℕ} {k : ℕ × List ℕ}
    (h : fsOOOKey maxSkip maxStored nr store j = some k) :
    (nr ≤ j ∧ j - nr ≤ maxSkip ∧ k = (j + 1, List.range' nr (j - nr) ++ store)) ∨
      (j < nr ∧ j ∈ store ∧ k = (nr, store.erase j)) := by
  unfold fsOOOKey at h
  split_ifs at h <;> grind

omit [SampleableType W] [DecidableEq W] [DecidableEq Ct] in
/-- The invariant of the receiver bookkeeping: the positions of the log are below its length,
the stored positions are distinct and below `nr`, a delivered position is below `nr` and not
stored, and `nr` is at most the length of the log. -/
def FSOOOSt.Inv (s : FSOOOSt Sa W Ct) : Prop :=
  (∀ e ∈ s.fs.log, e.1 < s.fs.log.length) ∧ (∀ i ∈ s.store, i < s.nr) ∧ s.store.Nodup ∧
    (∀ i, s.dlv i = true → i < s.nr ∧ i ∉ s.store) ∧ s.nr ≤ s.fs.log.length

omit [SampleableType W] [DecidableEq W] [DecidableEq Ct] in
/-- An available position is not delivered. -/
theorem FSOOOSt.Inv.dlv_eq_false {s : FSOOOSt Sa W Ct} (hs : s.Inv) {maxSkip maxStored j : ℕ}
    {k : ℕ × List ℕ} (hk : fsOOOKey maxSkip maxStored s.nr s.store j = some k) :
    s.dlv j = false := by
  rcases fsOOOKey_eq_some hk with ⟨h1, -, -⟩ | ⟨-, h2, -⟩
  · cases h : s.dlv j
    · rfl
    · exact absurd (hs.2.2.2.1 j h).1 (by omega)
  · cases h : s.dlv j
    · rfl
    · exact absurd h2 (hs.2.2.2.1 j h).2

/-- An available position is at most `nr + maxSkip`. -/
theorem fsOOOKey_le {maxSkip maxStored nr j : ℕ} {store : List ℕ} {k : ℕ × List ℕ}
    (hk : fsOOOKey maxSkip maxStored nr store j = some k) : j ≤ nr + maxSkip := by
  rcases fsOOOKey_eq_some hk with ⟨h1, h2, -⟩ | ⟨h1, -, -⟩ <;> omega

omit [SampleableType W] in
/-- A decryption from a log whose positions are below its length is at a position below its
length. -/
theorem FSIntSt.logDec_lt {s : FSIntSt Sa W Ct} (h : ∀ e ∈ s.log, e.1 < s.log.length)
    {j : ℕ} {ad : W} {c : Ct} {m : W} (hm : s.logDec j ad c = some m) : j < s.log.length := by
  unfold FSIntSt.logDec at hm
  obtain ⟨e, he, -⟩ := Option.map_eq_some_iff.1 hm
  have hp := List.find?_some he
  have hmem := List.mem_of_find?_eq_some he
  simp only [decide_eq_true_eq] at hp
  grind

omit [SampleableType W] [DecidableEq W] [DecidableEq Ct] in
/-- An accepted decryption at a position below the length of the log keeps the invariant. -/
theorem FSOOOSt.Inv.accept {s : FSOOOSt Sa W Ct} (hs : s.Inv) {maxSkip maxStored j : ℕ}
    {k : ℕ × List ℕ} (hk : fsOOOKey maxSkip maxStored s.nr s.store j = some k)
    (hj : j < s.fs.log.length) : (s.accept j k).Inv := by
  obtain ⟨hl, hst, hnd, hd, hnr⟩ := hs
  rcases fsOOOKey_eq_some hk with ⟨h1, -, rfl⟩ | ⟨h1, h2, rfl⟩
  · refine ⟨hl, ?_, ?_, ?_, ?_⟩ <;> simp only [FSOOOSt.accept]
    · grind
    · grind
    · grind
    · omega
  · refine ⟨hl, ?_, ?_, ?_, ?_⟩ <;> simp only [FSOOOSt.accept]
    · grind
    · exact hnd.erase j
    · grind
    · omega

omit [SampleableType W] [DecidableEq W] [DecidableEq Ct] in
/-- Whether an answer of the integrity game is an accepted decryption. -/
def fsAnsOk : FSIntAns Sa Ct W → Bool
  | .dec (some _) => true
  | _ => false

omit [SampleableType W] [DecidableEq W] [DecidableEq Ct] in
/-- The simulator of the adversary `fsOOORed`, with the next position and the stored positions
of the receiver as its state: it forwards encryptions and corruptions, and forwards a decryption
at a position that the lookup `fsOOOKey` makes available and that is below `M`; on an accepted
decryption it moves to the bookkeeping of the lookup. -/
def fsOOORedImpl (maxSkip maxStored M : ℕ) (w : ℕ × List ℕ) :
    FSIntQuery W Ct → OracleAdv (FSIntQuery W Ct) (FSIntAns Sa Ct W)
      (FSIntAns Sa Ct W × (ℕ × List ℕ))
  | .enc m => .query (.enc m) fun a => .ret (a, w)
  | .dec j ad c =>
    match fsOOOKey maxSkip maxStored w.1 w.2 j with
    | none => .ret (.dec none, w)
    | some k =>
      if j < M then .query (.dec j ad c) fun a => .ret (a, if fsAnsOk a then k else w)
      else .ret (.dec none, w)
  | .corrupt => .query .corrupt fun a => .ret (a, w)

omit [SampleableType W] [DecidableEq W] [DecidableEq Ct] in
/-- **The adversary of the FS-AEAD integrity game with in-place positions** for an adversary
`A` of the out-of-order game: it runs `A` with the bookkeeping of the receiver kept by
`fsOOORedImpl` and decrypts at positions below `M` only. -/
def fsOOORed (maxSkip maxStored M : ℕ)
    (A : OracleAdv (FSIntQuery W Ct) (FSIntAns Sa Ct W) Bool) :
    OracleAdv (FSIntQuery W Ct) (FSIntAns Sa Ct W) Bool :=
  (OracleAdv.simulate (fsOOORedImpl maxSkip maxStored M) A (0, [])).bind fun x => .ret x.1

/-- A call of the keyed integrity oracle with the flag of the event at all positions. -/
def fsKeyCall (D : AEADDef W Ct) (k : ℕ → W) (st : FSIntSt Unit W Ct × Bool)
    (d : FSIntQuery W Ct) : FSIntAns Sa Ct W × (FSIntSt Unit W Ct × Bool) :=
  ((fsKeyStep (Sa := Sa) D k st.1 d).1, ((fsKeyStep (Sa := Sa) D k st.1 d).2,
    st.2 || fsDecBad D k (fun _ => true) st.1 d))

/-- A call of the simulator `fsOOORedImpl` against the keyed integrity oracle with the flag of
the event, as a function of the joint state. -/
def fsOOORedStep (D : AEADDef W Ct) (k : ℕ → W) (maxSkip maxStored M : ℕ)
    (st : (ℕ × List ℕ) × (FSIntSt Unit W Ct × Bool)) :
    FSIntQuery W Ct → FSIntAns Sa Ct W × ((ℕ × List ℕ) × (FSIntSt Unit W Ct × Bool))
  | .enc m => ((fsKeyCall (Sa := Sa) D k st.2 (.enc m)).1,
      (st.1, (fsKeyCall (Sa := Sa) D k st.2 (.enc m)).2))
  | .dec j ad c =>
    match fsOOOKey maxSkip maxStored st.1.1 st.1.2 j with
    | none => (.dec none, st)
    | some kk =>
      if j < M then
        ((fsKeyCall (Sa := Sa) D k st.2 (.dec j ad c)).1,
          (if fsAnsOk (fsKeyCall (Sa := Sa) D k st.2 (.dec j ad c)).1 then kk else st.1,
            (fsKeyCall (Sa := Sa) D k st.2 (.dec j ad c)).2))
      else (.dec none, st)
  | .corrupt => ((fsKeyCall (Sa := Sa) D k st.2 .corrupt).1,
      (st.1, (fsKeyCall (Sa := Sa) D k st.2 .corrupt).2))

/-- The simulator against the flagged keyed oracle is the point mass at `fsOOORedStep`. -/
theorem simOracle_fsOOORedImpl (D : AEADDef W Ct) (k : ℕ → W) (maxSkip maxStored M : ℕ) :
    OracleAdv.simOracle (fsOOORedImpl (Sa := Sa) maxSkip maxStored M)
      (OracleAdv.flagWhen (fun s d _ => fsDecBad D k (fun _ => true) s d = true)
        (fsKeyOracle D k)) =
      fun st d => PMF.pure (fsOOORedStep D k maxSkip maxStored M st d) := by
  funext st d
  cases d with
  | enc m =>
    simp [OracleAdv.simOracle, fsOOORedImpl, fsOOORedStep, fsKeyCall, OracleAdv.flagWhen,
      fsKeyOracle, PMF.pure_map]
  | dec j ad c =>
    cases hk : fsOOOKey maxSkip maxStored st.1.1 st.1.2 j with
    | none => simp [OracleAdv.simOracle, fsOOORedImpl, fsOOORedStep, hk, PMF.pure_map]
    | some kk =>
      by_cases hj : j < M
      · simp [OracleAdv.simOracle, fsOOORedImpl, fsOOORedStep, fsKeyCall, OracleAdv.flagWhen,
          fsKeyOracle, PMF.pure_map, hk, hj]
        grind
      · simp [OracleAdv.simOracle, fsOOORedImpl, fsOOORedStep, hk, hj, PMF.pure_map]
  | corrupt =>
    simp [OracleAdv.simOracle, fsOOORedImpl, fsOOORedStep, fsKeyCall, OracleAdv.flagWhen,
      fsKeyOracle, PMF.pure_map]

/-- The flag of the keyed oracle at `fsOOORed` is the flag of the run of `A` against
`fsOOORedStep`. -/
theorem fsKeyFlag_fsOOORed (D : AEADDef W Ct) (k : ℕ → W) (maxSkip maxStored M : ℕ)
    (A : OracleAdv (FSIntQuery W Ct) (FSIntAns Sa Ct W) Bool) :
    fsKeyFlag D k (fun _ => true) (fsOOORed maxSkip maxStored M A) =
      (OracleAdv.run (fun st d => PMF.pure (fsOOORedStep D k maxSkip maxStored M st d)) A
        ((0, []), (fsKeyInit, false))).map fun y => y.2.2.2 := by
  rw [fsKeyFlag, fsOOORed, OracleAdv.run_bind, OracleAdv.run_simulate,
    simOracle_fsOOORedImpl]
  simp [PMF.map_bind, PMF.bind_map, Function.comp_def, PMF.pure_map]
  rfl

omit [SampleableType W] [DecidableEq W] [DecidableEq Ct] in
/-- The initial state satisfies the invariant. -/
theorem fsOOOInit_inv (sa : Sa) : (fsOOOInit sa : FSOOOSt Sa W Ct).Inv := by
  simp [FSOOOSt.Inv, fsOOOInit]

/-- **The event of the out-of-order game at `fsOOORed`.** For an adversary with at most `q`
encryptions, the event of the real out-of-order game from the state `sa` has the distribution
of the event of the keyed oracle with the keys of the chain from `sa` at the adversary
`fsOOORed` with `q + maxSkip + 1` positions. -/
theorem fsOOOFlag_eq_fsKeyFlag (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (maxSkip maxStored q : ℕ) (sa : Sa)
    (A : OracleAdv (FSIntQuery W Ct) (FSIntAns Sa Ct W) Bool)
    (hA : A.IsQueryBoundBy fsIntEncCost q) :
    fsOOOFlag G D maxSkip maxStored sa A =
      fsKeyFlag D (chainKey G sa) (fun _ => true)
        (fsOOORed maxSkip maxStored (q + maxSkip + 1) A) := by
  have hL : OracleAdv.flagWhen (fun s d _ => fsOOOBad G D maxSkip maxStored s d = true)
      (fsIntOOOOracle G D maxSkip maxStored false) = fun st d => PMF.pure
        (((fsOOOStep G D maxSkip maxStored false st.1 d).1,
          ((fsOOOStep G D maxSkip maxStored false st.1 d).2,
            st.2 || fsOOOBad G D maxSkip maxStored st.1 d)) :
          FSIntAns Sa Ct W × (FSOOOSt Sa W Ct × Bool)) := by
    funext st d
    simp [OracleAdv.flagWhen, fsIntOOOOracle, PMF.pure_map]
  rw [fsOOOFlag, hL, fsKeyFlag_fsOOORed]
  refine run_map_eq_of_sim_bad (S := FSOOOSt Sa W Ct × Bool)
    (S' := (ℕ × List ℕ) × (FSIntSt Unit W Ct × Bool)) _ _ (fun st => st.2) (fun st => st.2.2)
    fsIntEncCost
    (fun n st st' => st'.1 = (st.1.nr, st.1.store) ∧ st'.2.1.log = st.1.fs.log ∧
      st'.2.1.corr = st.1.fs.corr ∧ st'.2.2 = st.2 ∧ st.1.fs.init = sa ∧
      st.1.fs.cur = (fun x => (G.stretch x).2)^[st.1.fs.log.length] sa ∧ st.1.Inv ∧
      st.1.fs.log.length + n ≤ q)
    (fun st => st.1.fs.corr = true) (fun st => st.2.1.corr = true)
    ?_ ?_ ?_ ?_ ?_ ?_ A q hA _ _ ?_
  rotate_left 6
  · simp [fsOOOInit, fsKeyInit, FSOOOSt.Inv]
  · intro st d h
    simp [h]
  · intro st d h
    cases d with
    | dec j ad c =>
      simp only [fsOOORedStep]
      split
      · exact h
      · split <;> simp [fsKeyCall, h]
    | _ => simp [fsOOORedStep, fsKeyCall, h]
  · intro st d h
    cases d with
    | dec j ad c => simp [fsOOOStep, fsOOOAt, fsOOOBad, h]
    | _ => simp [fsOOOStep, fsOOOBad, h]
  · intro st d h
    cases d with
    | dec j ad c =>
      simp only [fsOOORedStep]
      split
      · exact ⟨h, rfl⟩
      · split <;> simp [fsKeyCall, fsKeyStep, fsDecBad, h]
    | _ => simp [fsOOORedStep, fsKeyCall, fsKeyStep, fsDecBad, h]
  · rintro n st st' ⟨-, -, hc, hf, -⟩
    exact ⟨hf.symm, fun h => hc.trans h⟩
  · rintro n ⟨s, b⟩ ⟨w, s', b'⟩ d ⟨hw, hlog, hcorr, hflag, hinit, hcur, hI, hbud⟩ hS hg hcost
    simp only at hw hlog hcorr hflag hinit hcur hI hbud hS hg hcost ⊢
    subst hw hflag hg
    have hc0 : s.fs.corr = false := by simpa using hS
    cases d with
    | enc m =>
      simp only [fsIntEncCost] at hcost
      refine ⟨?_, ?_, ?_⟩
      · simp [fsOOORedStep, fsKeyCall, fsKeyStep, fsOOOBad, fsDecBad]
      · simp [fsOOOStep, fsOOORedStep, fsKeyCall, fsKeyStep, hcorr, hc0]
      · intro _ _
        refine ⟨?_, ?_⟩
        · simp [fsOOOStep, fsOOORedStep, fsKeyCall, fsKeyStep, hlog, hcur, chainKey]
        · simp only [fsOOOStep, fsOOORedStep, fsKeyCall, fsKeyStep, hlog, hcorr, hinit,
            List.length_cons, fsDecBad, Bool.or_false, true_and]
          refine ⟨by simp [hcur, chainKey], by simp [fsOOOBad],
            by rw [Function.iterate_succ_apply', ← hcur], ?_, by simp [fsIntEncCost]; omega⟩
          obtain ⟨hl, hst, hnd, hd, hnr⟩ := hI
          refine ⟨?_, hst, hnd, hd, by simp; omega⟩
          simp only [List.length_cons, List.mem_cons, forall_eq_or_imp]
          exact ⟨Nat.lt_succ_self _, fun e he => Nat.lt_succ_of_lt (hl e he)⟩
    | corrupt =>
      refine ⟨?_, ?_, ?_⟩
      · simp [fsOOORedStep, fsKeyCall, fsKeyStep, fsOOOBad, fsDecBad]
      · simp [fsOOOStep, fsOOORedStep, fsKeyCall, fsKeyStep]
      · intro _ h
        simp [fsOOOStep] at h
    | dec j ad c =>
      have hat : fsOOOAt maxSkip maxStored s j = fsOOOKey maxSkip maxStored s.nr s.store j := by
        simp [fsOOOAt, hc0]
      cases hk : fsOOOKey maxSkip maxStored s.nr s.store j with
      | none =>
        refine ⟨?_, ?_, ?_⟩
        · simp [fsOOORedStep, fsOOOBad, hat, hk]
        · simp [fsOOOStep, fsOOORedStep, hat, hk, hcorr]
        · intro _ _
          simp only [fsOOOStep, fsOOORedStep, hat, hk, fsOOOBad, fsIntEncCost]
          simp [hlog, hcorr, hinit, hcur, hI]
          omega
      | some kk =>
        have hjM : j < q + maxSkip + 1 := by
          have := fsOOOKey_le hk
          have := hI.2.2.2.2
          omega
        have hLD : s'.logDec j ad c = s.fs.logDec j ad c := by
          simp [FSIntSt.logDec, hlog]
        have hdl : s.dlv j = false := hI.dlv_eq_false hk
        have hU : s.logDecU j ad c = s.fs.logDec j ad c := by simp [FSOOOSt.logDecU, hdl]
        refine ⟨?_, ?_, ?_⟩
        · simp [fsOOORedStep, fsOOOBad, fsKeyCall, fsKeyStep, fsDecBad, hat, hk,
            hjM, hU, hLD, hcorr, hc0, hinit]
        · intro _ h
          simp [fsOOOStep, hat, hk] at h
          grind [FSOOOSt.accept]
        · intro hT _
          have hbad : D.decrypt (chainKey G sa j) c ad = s.fs.logDec j ad c := by
            simpa [fsOOOStep, fsOOOBad, hat, hk, hU, hinit] using hT
          refine ⟨?_, ?_⟩
          · simp [fsOOOStep, fsOOORedStep, fsKeyCall, fsKeyStep, hat, hk, hjM, hcorr, hc0,
              hinit]
          · simp only [fsOOOStep, fsOOORedStep, fsKeyCall, fsKeyStep, hat, hk, hjM, hinit,
              hcorr, hc0, ↓reduceIte, Bool.false_eq_true, fsAnsOk]
            have hfb : fsDecBad D (chainKey G sa) (fun _ => true) s' (.dec j ad c) =
                fsOOOBad G D maxSkip maxStored s (.dec j ad c) := by
              simp [fsDecBad, fsOOOBad, hat, hk, hcorr, hc0, hU, hLD, hinit]
            rw [hfb]
            cases hr : D.decrypt (chainKey G sa j) c ad with
            | none =>
              simp [hlog, hc0, hinit, hcur, hI, fsIntEncCost]
              omega
            | some m =>
              have hjl : j < s.fs.log.length := FSIntSt.logDec_lt hI.1 (hbad.symm.trans hr)
              simpa [FSOOOSt.accept, hlog, hc0, hinit, hcur, fsIntEncCost] using
                And.intro (hI.accept hk hjl) hbud

omit [SampleableType W] [DecidableEq W] [DecidableEq Ct] in
/-- The adversary `fsOOORed` decrypts at positions below `M` only. -/
theorem fsOOORed_isQueryBoundBy (maxSkip maxStored M : ℕ)
    (A : OracleAdv (FSIntQuery W Ct) (FSIntAns Sa Ct W) Bool) :
    (fsOOORed maxSkip maxStored M A).IsQueryBoundBy (fsIntFar M) 0 := by
  have h0 : ∀ B : OracleAdv (FSIntQuery W Ct) (FSIntAns Sa Ct W) Bool,
      B.IsQueryBoundBy (fun _ => 0) 0 := by
    intro B
    induction B with
    | ret => trivial
    | rand p k ih => exact ih
    | query d k ih => exact ⟨le_rfl, ih⟩
  have himpl : ∀ w d, (fsOOORedImpl (Sa := Sa) (W := W) (Ct := Ct) maxSkip maxStored M w
      d).IsQueryBoundBy (fsIntFar M) ((fun _ => 0) d) := by
    intro w d
    cases d with
    | enc m => exact ⟨by simp [fsIntFar], fun _ => trivial⟩
    | dec j ad c =>
      simp only [fsOOORedImpl]
      split
      · trivial
      · split
        · exact ⟨by simp [fsIntFar]; omega, fun _ => trivial⟩
        · trivial
    | corrupt => exact ⟨by simp [fsIntFar], fun _ => trivial⟩
  unfold fsOOORed
  simpa using OracleAdv.isQueryBoundBy_bind (b := 0) (f := fun x => OracleAdv.ret x.1)
    (OracleAdv.isQueryBoundBy_simulate _ (fun _ => 0) _ himpl (h0 A) _) (fun _ => trivial)

end Red

/-! ## The bound -/

section Bound

variable {Sa W Ct : Type} [SampleableType W] [SampleableType Ct] [DecidableEq W]
  [DecidableEq Ct] [Fintype Sa] [Nonempty Sa]

/-- **The event of the keyed oracle with the keys of a uniform chain.** For an adversary `B`
that decrypts at positions below `N` only, the probability of the event of the keyed oracle
with the keys of the chain from a uniform state is at most the FS-PRG advantage of
`fsIntPost G D B` over `N` steps plus the AEAD advantages of `fsIntRed G D N j B` for
`j < N`. -/
theorem fsKeyFlag_chain_le (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (N : ℕ)
    (B : OracleAdv (FSIntQuery W Ct) (FSIntAns Sa Ct W) Bool)
    (hB : B.IsQueryBoundBy (fsIntFar N) 0) :
    ((PMF.uniformFintype Sa).bind fun sa => fsKeyFlag D (chainKey G sa) (fun _ => true) B)
        true ≤
      FSPRG_Advantage G N (fsIntPost G D B) +
        ∑ j ∈ Finset.range N, AEAD_CCA_Advantage D (fsIntRed G D N j B) := by
  have hreal : prTrue ((fsprg_real G N).bind (fsIntPost G D B)) Heap.empty =
      ((PMF.uniformFintype Sa).bind fun sa => fsKeyFlag D (chainKey G sa) (fun _ => true) B)
        true := by
    simp only [fsprg_real, fsIntPost, SPComp.monad_bind_eq, SPComp.bind_assoc, SPComp.pure_bind,
      fsKeyOf_fsprgRun]
    rw [prTrue_sample_bind_liftPMF]
  have hideal : prTrue ((fsprg_ideal (St := Sa) N).bind (fsIntPost G D B)) Heap.empty =
      ((PMF.uniformFintype (Fin N → W)).bind fun v => (PMF.uniformFintype Sa).bind fun sN =>
        fsKeyFlag D (fsKeyOf G (List.ofFn v) sN) (fun _ => true) B) true := by
    simp only [fsprg_ideal, fsIntPost, SPComp.monad_bind_eq, SPComp.bind_assoc,
      SPComp.pure_bind, sample_eq_liftPMF Sa, liftPMF_bind_liftPMF]
    rw [prTrue_sample_bind_liftPMF]
  have hprg : prTrue ((fsprg_real G N).bind (fsIntPost G D B)) Heap.empty -
      prTrue ((fsprg_ideal (St := Sa) N).bind (fsIntPost G D B)) Heap.empty ≤
        FSPRG_Advantage G N (fsIntPost G D B) := le_max_left _ _
  rw [tsub_le_iff_right, hreal, hideal] at hprg
  refine hprg.trans (add_le_add le_rfl ?_)
  refine (bind_apply_true_le_sum _ _ _ _ fun v => bind_apply_true_le_sum _ _ _ _ fun sN =>
    fsKeyFlag_apply_le_sum D _ N B hB).trans (Finset.sum_le_sum fun j hj => ?_)
  exact fsKeyFlag_le_aead G D (Finset.mem_range.mp hj) B

/-- **FS-AEAD integrity with out-of-order delivery from PRG and AEAD security.** For every
adversary `A` with at most `q` encryptions, the out-of-order integrity advantage with the skip
bound `maxSkip` and the store capacity `maxStored` is at most the FS-PRG advantage of
`fsIntPost G D (fsOOORed …)` over `q + maxSkip + 1` steps plus the AEAD advantages of
`fsIntRed G D (q + maxSkip + 1) j (fsOOORed …)` for `j < q + maxSkip + 1`. -/
theorem fsaead_int_ooo_advantage_le (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (maxSkip maxStored q : ℕ) (A : OracleAdv (FSIntQuery W Ct) (FSIntAns Sa Ct W) Bool)
    (hA : A.IsQueryBoundBy fsIntEncCost q) :
    FSAEAD_Int_OOO_Advantage G D maxSkip maxStored A ≤
      FSPRG_Advantage G (q + maxSkip + 1)
          (fsIntPost G D (fsOOORed maxSkip maxStored (q + maxSkip + 1) A)) +
        ∑ j ∈ Finset.range (q + maxSkip + 1), AEAD_CCA_Advantage D
          (fsIntRed G D (q + maxSkip + 1) j (fsOOORed maxSkip maxStored (q + maxSkip + 1) A)) := by
  refine (fsaead_int_ooo_advantage_le_flag G D maxSkip maxStored A).trans ?_
  simp only [fsOOOFlag_eq_fsKeyFlag G D maxSkip maxStored q _ A hA]
  exact fsKeyFlag_chain_le G D _ _ (fsOOORed_isQueryBoundBy maxSkip maxStored _ A)

end Bound

end CatCrypt.Crypto.Messaging
