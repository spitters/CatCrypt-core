/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.FSAEAD
public import CatCryptCore.Crypto.OracleGameUpToBad
public import CatCryptCore.Crypto.Constructions.ECBCPRFFlag

/-!
# FS-AEAD integrity from PRG and AEAD security

The FS-AEAD integrity game `fsaead_int_game` (Alwen, Coretti and Dodis, §4.3) answers a
decryption at a position `j` under the key `chainKey G sa j` of the chain of the generator
`G` (real) or from the log of the honest ciphertexts (ideal); decryptions are refused after
the corruption of the sender. The two games agree until a decryption before the corruption
whose answer under the key differs from the decryption from the log, so the advantage is at
most the probability of that event in the real game.

The event is decided before the corruption, so it depends on the keys of the chain only and
not on the state of the sender. For an adversary that decrypts at positions below `N` only,
the keys at positions below `N` are the outputs of `N` steps of the generator, and the keys at
the positions from `N` on are the keys of the chain from the state after them. The FS-PRG
distinguisher `fsIntPost` runs the adversary with these keys and outputs the event, so the
keys at positions below `N` are replaced by uniform keys at the cost of its FS-PRG advantage.
Under uniform keys, the event at the position `j` is detected by the AEAD reduction
`fsIntRed`, which embeds the key of the authenticated-encryption challenger at `j`: in the
real game of the challenger it outputs the event, and in the ideal game the decryption of the
challenger is the decryption from the log, so it outputs `false`.

## Main definitions

* `fsKeyStep`, `fsKeyOracle` — the integrity oracle with the keys given by a function on the
  positions, and the corruption answered without a state
* `fsDecBad` — a decryption before the corruption at a position of a set, whose answer under
  the key differs from the decryption from the log
* `fsIntFar` — the decryption queries at positions from `N` on
* `fsKeyOf` — the key function of the outputs of `N` steps of the generator and the state
  after them
* `fsKeyFlag` — the probability that the run of the keyed oracle sets the event
* `fsIntPost` — the FS-PRG distinguisher
* `fsIntRedImpl`, `fsIntRed` — the AEAD reduction of the position `j`

## Main results

* `run_flag_map_eq_of_sim` — two deterministic flagged oracles related until a stop give the
  same flag distribution
* `fsaead_int_advantage_le_flag` — the integrity advantage is at most the probability of the
  event in the real game
* `fsKeyFlag_apply_le_sum` — the union bound over the positions
* `fsIntRed_real_eq`, `fsIntRed_ideal_eq_zero` — the AEAD games of `fsIntRed`
* `fsaead_int_advantage_le` — for every adversary `A` decrypting at positions below `N`, the
  integrity advantage is at most the FS-PRG advantage of `fsIntPost G D A` plus the AEAD
  advantages of `fsIntRed G D N j A` for `j < N`
* `fsaead_int_advantage_le_prg` — the same with the FS-PRG advantage bounded by the PRG
  advantages of the FS-PRG reductions

## References

* J. Alwen, S. Coretti, Y. Dodis, *The Double Ratchet: Security Notions, Proofs, and
  Modularization for the Signal Protocol*, EUROCRYPT 2019, §4.3
-/

set_option autoImplicit false

@[expose] public section

namespace CatCrypt.Crypto.Messaging

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Assumptions
open scoped ENNReal

/-! ## Flagged deterministic oracles related until a stop -/

section FlagSim

variable {D R α S S' : Type}

/-- From a state of `Stop`, which every call keeps and from which no call is bad, a flagged
run keeps its flag. -/
theorem run_flag_map_eq_pure_of_stop (F : S → D → R × S) (bad : S → D → Bool)
    (Stop : S → Prop) (hStop : ∀ s d, Stop s → Stop (F s d).2 ∧ bad s d = false)
    (A : OracleAdv D R α) (s : S) (b : Bool) (hs : Stop s) :
    (OracleAdv.run (OracleAdv.flagWhen (fun s d _ => bad s d = true)
        fun s d => PMF.pure (F s d)) A (s, b)).map (fun y => y.2.2) = PMF.pure b := by
  refine OracleAdv.run_map_eq_pure_of_frozen _ (fun y => Stop y.1) (fun y => y.2) ?_ A (s, b) hs
  intro y d hy x hx
  simp only [OracleAdv.flagWhen, PMF.pure_map, PMF.support_pure, Set.mem_singleton_iff] at hx
  subst hx
  simp [(hStop y.1 d hy).1, (hStop y.1 d hy).2]

/-- **Flagged deterministic oracles related until a stop.** Let the states `s` and `s'` be
related by `Rel`. If, at related states outside `Stop`, every call has the same bad flag, and
either leads into `Stop` and `Stop'` or gives the same answer and related states; if `Stop`
and `Stop'` are kept by every call and no call from them is bad; and if `Rel` relates states
of `Stop` only to states of `Stop'`, then the flagged runs give the same flag distribution. -/
theorem run_flag_map_eq_of_sim (F : S → D → R × S) (F' : S' → D → R × S')
    (bad : S → D → Bool) (bad' : S' → D → Bool) (Rel : S → S' → Prop)
    (Stop : S → Prop) (Stop' : S' → Prop)
    (hStop : ∀ s d, Stop s → Stop (F s d).2 ∧ bad s d = false)
    (hStop' : ∀ s d, Stop' s → Stop' (F' s d).2 ∧ bad' s d = false)
    (hRelStop : ∀ s s', Rel s s' → Stop s → Stop' s')
    (hstep : ∀ s s' d, Rel s s' → ¬ Stop s → bad s d = bad' s' d ∧
      (Stop (F s d).2 → Stop' (F' s' d).2) ∧
      (¬ Stop (F s d).2 → (F s d).1 = (F' s' d).1 ∧ Rel (F s d).2 (F' s' d).2))
    (A : OracleAdv D R α) (s : S) (s' : S') (b : Bool) (hs : Rel s s') :
    (OracleAdv.run (OracleAdv.flagWhen (fun s d _ => bad s d = true)
        fun s d => PMF.pure (F s d)) A (s, b)).map (fun y => y.2.2) =
      (OracleAdv.run (OracleAdv.flagWhen (fun s d _ => bad' s d = true)
        fun s d => PMF.pure (F' s d)) A (s', b)).map (fun y => y.2.2) := by
  induction A generalizing s s' b with
  | ret a => simp [PMF.pure_map]
  | rand p k ih => simp only [OracleAdv.run_rand, PMF.map_bind, fun x => ih x s s' b hs]
  | query d k ih =>
    by_cases hS : Stop s
    · rw [run_flag_map_eq_pure_of_stop F bad Stop hStop _ s b hS,
        run_flag_map_eq_pure_of_stop F' bad' Stop' hStop' _ s' b (hRelStop s s' hs hS)]
    · obtain ⟨hb, hst, hlive⟩ := hstep s s' d hs hS
      simp only [OracleAdv.run_query, OracleAdv.flagWhen, PMF.pure_map, PMF.pure_bind, hb]
      by_cases hT : Stop (F s d).2
      · rw [run_flag_map_eq_pure_of_stop F bad Stop hStop _ _ _ hT,
          run_flag_map_eq_pure_of_stop F' bad' Stop' hStop' _ _ _ (hst hT)]
      · rw [(hlive hT).1]
        exact ih _ _ _ _ (hlive hT).2

/-- A flagged run of an adversary that asks no query of positive cost, against an oracle whose
bad calls have positive cost, does not set the flag. -/
theorem run_flagWhen_eq_zero_of_isQueryBoundBy (O : S → D → PMF (R × S))
    (bad : S → D → Bool) (cost : D → ℕ) (hbad : ∀ s d, bad s d = true → 0 < cost d)
    (A : OracleAdv D R α) (hA : A.IsQueryBoundBy cost 0) (s : S) :
    (OracleAdv.run (OracleAdv.flagWhen (fun s d _ => bad s d = true) O) A (s, false)).toOuterMeasure
      {y | y.2.2 = true} = 0 := by
  induction A generalizing s with
  | ret a => simp [PMF.toOuterMeasure_pure_apply]
  | rand p k ih =>
    rw [OracleAdv.run_rand, PMF.toOuterMeasure_bind_apply]
    simp [fun b => ih b (hA b)]
  | query d k ih =>
    have hd : bad s d = false := by
      cases h : bad s d
      · rfl
      · exact absurd hA.1 (by have := hbad s d h; omega)
    have hk : ∀ r, (k r).IsQueryBoundBy cost 0 := fun r => by
      simpa [Nat.zero_sub] using hA.2 r
    rw [OracleAdv.run_query, OracleAdv.flagWhen, PMF.bind_map, PMF.toOuterMeasure_bind_apply]
    refine ENNReal.tsum_eq_zero.mpr fun x => ?_
    simp only [Function.comp_apply, hd, Bool.false_eq_true, decide_false, Bool.or_false]
    rw [ih x.1 (hk x.1) x.2, mul_zero]

end FlagSim

/-! ## The keyed integrity oracle -/

section Keyed

variable {Sa W Ct : Type} [SampleableType W] [SampleableType Ct] [DecidableEq W]
  [DecidableEq Ct]

/-- The initial state of the keyed integrity oracle: an empty log and no corruption. The
generator states of `FSIntSt` are not used. -/
def fsKeyInit : FSIntSt Unit W Ct := ⟨(), (), [], false⟩

omit [SampleableType W] [SampleableType Ct] in
/-- A call of the integrity oracle with the key `k j` at the position `j`: `enc m` encrypts
under the key at the next position and logs the ciphertext, `dec j ad c` decrypts under `k j`
and is refused after the corruption, and `corrupt` sets the corruption and answers `none`. -/
def fsKeyStep (D : AEADDef W Ct) (k : ℕ → W) (s : FSIntSt Unit W Ct) :
    FSIntQuery W Ct → FSIntAns Sa Ct W × FSIntSt Unit W Ct
  | .enc m => (.ct (D.encrypt (k s.log.length) m.1 m.2),
      { s with log := (s.log.length, m.1, m.2, D.encrypt (k s.log.length) m.1 m.2) :: s.log })
  | .dec j ad c => (.dec (if s.corr then none else D.decrypt (k j) c ad), s)
  | .corrupt => (.dec none, { s with corr := true })

omit [SampleableType W] [SampleableType Ct] in
/-- The keyed integrity oracle: the point mass at `fsKeyStep`. -/
noncomputable def fsKeyOracle (D : AEADDef W Ct) (k : ℕ → W) (s : FSIntSt Unit W Ct)
    (d : FSIntQuery W Ct) : PMF (FSIntAns Sa Ct W × FSIntSt Unit W Ct) :=
  PMF.pure (fsKeyStep D k s d)

omit [SampleableType W] [SampleableType Ct] in
/-- The bad event of the integrity game at the positions `j` with `P j`: a decryption before
the corruption whose answer under the key `k j` differs from the decryption from the log. -/
def fsDecBad (D : AEADDef W Ct) (k : ℕ → W) (P : ℕ → Bool) {S : Type} (s : FSIntSt S W Ct) :
    FSIntQuery W Ct → Bool
  | .dec j ad c => P j && !s.corr && decide (D.decrypt (k j) c ad ≠ s.logDec j ad c)
  | _ => false

/-- The cost of a query that decrypts at a position from `N` on: `1` for such a query, `0`
otherwise. An adversary bounded by `0` in this cost decrypts at positions below `N` only. -/
def fsIntFar (N : ℕ) : FSIntQuery W Ct → ℕ
  | .dec j _ _ => if N ≤ j then 1 else 0
  | _ => 0

omit [SampleableType W] [SampleableType Ct] [DecidableEq W] [DecidableEq Ct] in
/-- The key function of the outputs `ks` of the generator `G` and the state `sN` after them:
the output at a position below the number of outputs, and the key of the chain from `sN`
after them. -/
def fsKeyOf (G : PRGDef Sa (W × Sa)) (ks : List W) (sN : Sa) (j : ℕ) : W :=
  if h : j < ks.length then ks[j] else chainKey G sN (j - ks.length)

omit [SampleableType Ct] in
/-- The flag of the run of `A` against the keyed oracle with the key function `k`, flagged by
the bad event at the positions of `P`. -/
noncomputable def fsKeyFlag (D : AEADDef W Ct) (k : ℕ → W) (P : ℕ → Bool)
    (A : OracleAdv (FSIntQuery W Ct) (FSIntAns Sa Ct W) Bool) : PMF Bool :=
  (OracleAdv.run (OracleAdv.flagWhen (fun s d _ => fsDecBad D k P s d = true)
    (fsKeyOracle D k)) A (fsKeyInit, false)).map fun y => y.2.2

omit [SampleableType W] [SampleableType Ct] in
/-- The decryption from a log with a new entry `e`: the plaintext of `e` if it matches, the
decryption from the old log otherwise. -/
theorem logDec_cons {S : Type} (s : FSIntSt S W Ct) (e : ℕ × W × W × Ct) (j : ℕ) (ad : W)
    (c : Ct) :
    ({ s with log := e :: s.log } : FSIntSt S W Ct).logDec j ad c =
      if e.1 = j ∧ e.2.2.1 = ad ∧ e.2.2.2 = c then some e.2.1 else s.logDec j ad c := by
  unfold FSIntSt.logDec; rw [List.find?_cons]; split <;> simp_all

omit [SampleableType W] [SampleableType Ct] [DecidableEq W] [DecidableEq Ct] in
/-- The key function of the outputs and the final state of `N` steps of the generator from `s`
is the key chain from `s`. -/
theorem fsKeyOf_fsprgRun (G : PRGDef Sa (W × Sa)) (N : ℕ) (s : Sa) :
    fsKeyOf G (fsprgRun G N s).1 (fsprgRun G N s).2 = chainKey G s := by
  induction N generalizing s with
  | zero => funext j; simp [fsKeyOf, fsprgRun]
  | succ n ih =>
    funext j
    rw [fsprgRun_succ]
    cases j with
    | zero => simp [fsKeyOf, chainKey]
    | succ i =>
      have h := congrFun (ih (G.stretch s).2) i
      have hc : chainKey G s (i + 1) = chainKey G (G.stretch s).2 i := by
        simp only [chainKey, Function.iterate_succ_apply]
      rw [hc, ← h]
      unfold fsKeyOf
      simp only [List.length_cons, Nat.add_lt_add_iff_right, List.getElem_cons_succ,
        Nat.add_sub_add_right]

omit [SampleableType Ct] in
/-- **The union bound over the positions.** For an adversary that decrypts at positions below
`N` only, the event at all positions is set with at most the sum over `j < N` of the
probabilities of the event at `j`. -/
theorem fsKeyFlag_apply_le_sum (D : AEADDef W Ct) (k : ℕ → W) (N : ℕ)
    (A : OracleAdv (FSIntQuery W Ct) (FSIntAns Sa Ct W) Bool)
    (hA : A.IsQueryBoundBy (fsIntFar N) 0) :
    fsKeyFlag D k (fun _ => true) A true ≤
      ∑ j ∈ Finset.range N, fsKeyFlag D k (fun i => i == j) A true := by
  simp only [fsKeyFlag, OracleGameUpToBad.map_flag_apply]
  have key : ∀ n, (OracleAdv.run (OracleAdv.flagWhen
      (fun s d _ => fsDecBad D k (fun i => decide (i < n)) s d = true) (fsKeyOracle D k)) A
        (fsKeyInit, false)).toOuterMeasure {y | y.2.2 = true} ≤
      ∑ j ∈ Finset.range n, (OracleAdv.run (OracleAdv.flagWhen
        (fun s d _ => fsDecBad D k (fun i => i == j) s d = true) (fsKeyOracle D k)) A
          (fsKeyInit, false)).toOuterMeasure {y | y.2.2 = true} := by
    intro n
    induction n with
    | zero =>
      rw [run_flagWhen_eq_zero_of_isQueryBoundBy _ _ (fsIntFar N) ?_ A hA]
      · exact zero_le
      · intro s d h
        cases d <;> simp [fsDecBad] at h
    | succ n ih =>
      rw [Finset.sum_range_succ]
      refine (OracleAdv.run_flagWhen_mono _ _ (fun s d _ =>
        fsDecBad D k (fun i => decide (i < n)) s d = true ∨
          fsDecBad D k (fun i => i == n) s d = true) ?_ A _).trans
        ((OracleAdv.run_flagWhen_or_le _ _ _ A _).trans (add_le_add ih le_rfl))
      intro s d x h
      cases d <;> simp [fsDecBad] at h ⊢
      grind
  refine (OracleAdv.run_flagWhen_mono _ _ (fun s d _ =>
    fsDecBad D k (fun i => decide (i < N)) s d = true ∨
      fsDecBad D k (fun i => decide (N ≤ i)) s d = true) ?_ A _).trans ?_
  · intro s d x h
    cases d <;> simp [fsDecBad] at h ⊢
    grind
  refine (OracleAdv.run_flagWhen_or_le _ _ _ A _).trans ?_
  rw [run_flagWhen_eq_zero_of_isQueryBoundBy _
    (fun s d => fsDecBad D k (fun i => decide (N ≤ i)) s d) (fsIntFar N) ?_ A hA, add_zero]
  · exact key N
  · intro s d h
    cases d <;> simp [fsDecBad, fsIntFar] at h ⊢
    grind

omit [SampleableType Ct] in
/-- **The FS-PRG distinguisher of FS-AEAD integrity.** On the outputs `ks` of the generator and
the state `sN` after them, it runs `A` against the keyed oracle with the key function
`fsKeyOf G ks sN` and outputs the bad event at all positions. -/
noncomputable def fsIntPost (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (A : OracleAdv (FSIntQuery W Ct) (FSIntAns Sa Ct W) Bool) (ks : List W × Sa) :
    SPComp Bool :=
  liftPMF (fsKeyFlag D (fsKeyOf G ks.1 ks.2) (fun _ => true) A)

omit [SampleableType Ct] in
/-- The simulator of the AEAD reduction of the position `j`, with the keys `k` at the other
positions and a flag: the encryption at the position `j` and the decryptions at `j` before the
corruption are queries to the authenticated-encryption challenger, and a decryption answer of
the challenger that differs from the decryption from the log sets the flag. The other queries
are answered by `fsKeyStep` with the keys `k`. -/
def fsIntRedImpl (D : AEADDef W Ct) (j : ℕ) (k : ℕ → W) (s : FSIntSt Unit W Ct × Bool) :
    FSIntQuery W Ct → OracleAdv (AEAD_CCA_Query W Ct) (AEAD_CCA_Answer W Ct)
      (FSIntAns Sa Ct W × (FSIntSt Unit W Ct × Bool))
  | .enc m =>
    if s.1.log.length = j then
      .query (.inl (m.1, m.2)) fun a => match a with
        | .inl ct => .ret (.ct ct, ({ s.1 with log := (s.1.log.length, m.1, m.2, ct) :: s.1.log },
            s.2))
        | .inr _ => .ret (.dec none, s)
    else .ret ((fsKeyStep (Sa := Sa) D k s.1 (.enc m)).1,
      ((fsKeyStep (Sa := Sa) D k s.1 (.enc m)).2, s.2))
  | .dec i ad c =>
    if i = j ∧ s.1.corr = false then
      .query (.inr (c, ad)) fun a => match a with
        | .inr r => .ret (.dec r, (s.1, s.2 || decide (r ≠ s.1.logDec j ad c)))
        | .inl _ => .ret (.dec none, s)
    else .ret ((fsKeyStep (Sa := Sa) D k s.1 (.dec i ad c)).1, (s.1, s.2))
  | .corrupt => .ret (.dec none, ({ s.1 with corr := true }, s.2))

omit [SampleableType W] [SampleableType Ct] [DecidableEq W] [DecidableEq Ct] in
/-- The key function of uniform outputs with the output at `j` replaced by `key`. -/
theorem update_fsKeyOf_ofFn (G : PRGDef Sa (W × Sa)) {N : ℕ} (v : Fin N → W) (sN : Sa) (j : ℕ)
    (hj : j < N) (key : W) :
    Function.update (fsKeyOf G (List.ofFn v) sN) j key =
      fsKeyOf G (List.ofFn (Function.update v ⟨j, hj⟩ key)) sN := by
  funext i
  by_cases hi : i = j
  · subst hi
    simp [fsKeyOf, hj]
  · rw [Function.update_of_ne hi]
    unfold fsKeyOf
    simp only [List.length_ofFn, List.getElem_ofFn]
    split_ifs with h
    · rw [Function.update_of_ne]
      exact fun h' => hi (congrArg Fin.val h')
    · rfl

omit [SampleableType Ct] in
/-- **The AEAD reduction in the real game.** Against the real oracles of the key `key`, the
simulated adversary outputs the bad event at `j` of the keyed oracle with the key `key` at `j`
and the keys `k` elsewhere. -/
theorem fsIntRed_run_real (D : AEADDef W Ct) (j : ℕ) (k : ℕ → W) (key : W)
    (A : OracleAdv (FSIntQuery W Ct) (FSIntAns Sa Ct W) Bool) :
    (OracleAdv.run (aeadRealOracle D key)
        ((OracleAdv.simulate (fsIntRedImpl D j k) A (fsKeyInit, false)).bind
          fun x => .ret x.2.2) ()).map Prod.fst =
      fsKeyFlag D (Function.update k j key) (fun i => i == j) A := by
  rw [OracleAdv.run_bind, OracleAdv.run_simulate, fsKeyFlag,
    ← OracleAdv.run_map_state (OracleAdv.simOracle (fsIntRedImpl D j k) (aeadRealOracle D key))
      _ Prod.fst ?_ A ((fsKeyInit, false), ())]
  · simp only [OracleAdv.run_ret, PMF.bind_map, PMF.map_comp]
    rw [← PMF.bind_pure_comp, PMF.bind_bind]
    simp only [Function.comp_def, PMF.pure_bind]
    rfl
  · rintro ⟨⟨st, fl⟩, u⟩ d
    cases d with
    | enc m =>
      by_cases h : st.log.length = j
      · simp [OracleAdv.simOracle, fsIntRedImpl, h, aeadRealOracle, OracleAdv.flagWhen,
          fsKeyOracle, fsKeyStep, fsDecBad, PMF.pure_map]
      · simp [OracleAdv.simOracle, fsIntRedImpl, h, OracleAdv.flagWhen, fsKeyOracle, fsKeyStep,
          fsDecBad, PMF.pure_map]
    | dec i ad c =>
      by_cases h : i = j ∧ st.corr = false
      · obtain ⟨rfl, hc⟩ := h
        simp [OracleAdv.simOracle, fsIntRedImpl, hc, aeadRealOracle, OracleAdv.flagWhen,
          fsKeyOracle, fsKeyStep, fsDecBad, PMF.pure_map]
      · simp only [OracleAdv.simOracle, fsIntRedImpl, h, ↓reduceIte, OracleAdv.run_ret,
          OracleAdv.flagWhen, fsKeyOracle, PMF.pure_map]
        grind [fsKeyStep, fsDecBad, Function.update]
    | corrupt =>
      simp [OracleAdv.simOracle, fsIntRedImpl, OracleAdv.flagWhen, fsKeyOracle, fsKeyStep,
        fsDecBad, PMF.pure_map]

/-- **The AEAD reduction in the ideal game.** Against the ideal oracles, the decryption answer
of the challenger at `j` is the decryption from the log, so the simulated adversary outputs
`false`. -/
theorem fsIntRed_run_ideal (D : AEADDef W Ct) (j : ℕ) (k : ℕ → W)
    (A : OracleAdv (FSIntQuery W Ct) (FSIntAns Sa Ct W) Bool) :
    ((OracleAdv.run aeadIdealOracle
        ((OracleAdv.simulate (fsIntRedImpl D j k) A (fsKeyInit, false)).bind
          fun x => .ret x.2.2) []).map Prod.fst) true = 0 := by
  let Inv : (FSIntSt Unit W Ct × Bool) × List ((W × W) × Ct) → Prop := fun s =>
    s.1.2 = false ∧ (s.1.1.log.length ≤ j → s.2 = []) ∧
      ∀ ad c, s.1.1.logDec j ad c = aeadLogDecrypt s.2 c ad
  have hinv := OracleAdv.run_support_inv
    (OracleAdv.simOracle (fsIntRedImpl (Sa := Sa) D j k) aeadIdealOracle) Inv ?_ A
    ((fsKeyInit, false), []) ⟨rfl, fun _ => rfl, fun _ _ => rfl⟩
  · rw [OracleAdv.run_bind, OracleAdv.run_simulate, PMF.apply_eq_zero_iff]
    intro ht
    simp only [PMF.support_map, PMF.support_bind, OracleAdv.run_ret, PMF.support_pure,
      Set.mem_image, Set.mem_iUnion, Set.mem_singleton_iff] at ht
    obtain ⟨_, ⟨_, ⟨x, hx, rfl⟩, _, rfl⟩, hfl⟩ := ht
    simp [(hinv x hx).1] at hfl
  · rintro ⟨⟨st, fl⟩, L⟩ d x ⟨hfl, hlen, hdec⟩ hx
    simp only at hfl hlen hdec
    subst hfl
    cases d with
    | enc m =>
      by_cases h : st.log.length = j
      · obtain rfl : L = [] := hlen h.le
        simp only [OracleAdv.simOracle, fsIntRedImpl, h, ↓reduceIte, Prod.mk.eta,
          OracleAdv.run_query, aeadIdealOracle, List.lookup_nil, PMF.bind_map, PMF.support_map,
          PMF.support_bind, PMF.support_uniformFintype, Set.top_eq_univ, Set.mem_univ,
          Function.comp_apply, OracleAdv.run_ret, PMF.support_pure, Set.iUnion_true,
          Set.iUnion_singleton_eq_range, Set.mem_image, Set.mem_range,
          exists_exists_eq_and] at hx
        obtain ⟨ct, rfl⟩ := hx
        refine ⟨rfl, fun hl => by simp at hl; omega, fun ad c => ?_⟩
        rw [logDec_cons, hdec ad c]
        simp only [aeadLogDecrypt]
        grind
      · simp only [OracleAdv.simOracle, fsIntRedImpl, h, ↓reduceIte, fsKeyStep,
          OracleAdv.run_ret, PMF.support_map, PMF.support_pure, Set.image_singleton,
          Set.mem_singleton_iff] at hx
        subst hx
        refine ⟨rfl, fun hl => hlen (by simp at hl; omega), fun ad c => ?_⟩
        simp only [logDec_cons, h, false_and, ↓reduceIte]
        exact hdec ad c
    | dec i ad c =>
      by_cases h : i = j ∧ st.corr = false
      · obtain ⟨rfl, hc⟩ := h
        simp only [OracleAdv.simOracle, fsIntRedImpl, hc, and_self, ↓reduceIte, ne_eq,
          decide_not, Bool.false_or, OracleAdv.run_query, aeadIdealOracle, PMF.pure_bind,
          OracleAdv.run_ret, PMF.support_map, PMF.support_pure, Set.image_singleton,
          Set.mem_singleton_iff] at hx
        subst hx
        exact ⟨by simp [hdec], hlen, hdec⟩
      · simp only [OracleAdv.simOracle, fsIntRedImpl, h, ↓reduceIte, OracleAdv.run_ret,
          PMF.support_map, PMF.support_pure, Set.image_singleton, Set.mem_singleton_iff] at hx
        subst hx
        exact ⟨rfl, hlen, hdec⟩
    | corrupt =>
      simp only [OracleAdv.simOracle, fsIntRedImpl, OracleAdv.run_ret, PMF.support_map,
        PMF.support_pure, Set.image_singleton, Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨rfl, hlen, hdec⟩

/-- A bind whose continuation at `true` is bounded by a sum is bounded by the sum of the
binds. -/
theorem bind_apply_true_le_sum {α : Type} (p : PMF α) (f : α → PMF Bool) (g : ℕ → α → PMF Bool)
    (t : Finset ℕ) (h : ∀ a, f a true ≤ ∑ j ∈ t, g j a true) :
    (p.bind f) true ≤ ∑ j ∈ t, (p.bind (g j)) true := by
  simp only [PMF.bind_apply]
  rw [← Summable.tsum_finsetSum (fun _ _ => ENNReal.summable)]
  exact ENNReal.tsum_le_tsum fun a => by rw [← Finset.mul_sum]; gcongr; exact h a

/-- A bind whose continuation at `true` is bounded by a sum of two terms is bounded by the sum
of the binds. -/
theorem bind_apply_true_le_add {α : Type} (p : PMF α) (f g h : α → PMF Bool)
    (hle : ∀ a, f a true ≤ g a true + h a true) :
    (p.bind f) true ≤ (p.bind g) true + (p.bind h) true := by
  simp only [PMF.bind_apply, ← ENNReal.tsum_add, ← mul_add]
  exact ENNReal.tsum_le_tsum fun a => by gcongr; exact hle a

end Keyed

/-! ## The integrity games -/

section Games

variable {Sa W Ct : Type} [SampleableType W] [SampleableType Ct] [DecidableEq W]
  [DecidableEq Ct] [Fintype Sa] [Nonempty Sa]

/-- **The AEAD reduction of the position `j`.** It samples uniform keys for the positions
below `N` and a uniform state for the chain of the positions from `N` on, and simulates the
integrity game for `A` with the key of the challenger at `j` (`fsIntRedImpl`); it outputs the
bad event at `j`. -/
noncomputable def fsIntRed (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (N j : ℕ)
    (A : OracleAdv (FSIntQuery W Ct) (FSIntAns Sa Ct W) Bool) : AEAD_CCA_Adversary W Ct :=
  .rand (PMF.uniformFintype (Fin N → W)) fun v => .rand (PMF.uniformFintype Sa) fun sN =>
    (OracleAdv.simulate (fsIntRedImpl D j (fsKeyOf G (List.ofFn v) sN)) A
      (fsKeyInit, false)).bind fun x => .ret x.2.2

omit [SampleableType Ct] [Fintype Sa] [Nonempty Sa] in
/-- The flagged real integrity game from the initial state `sa`, flagged by the bad event, has
the flag distribution of the keyed oracle with the keys of the chain from `sa`. -/
theorem fsInt_real_flag_eq (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (sa : Sa)
    (A : OracleAdv (FSIntQuery W Ct) (FSIntAns Sa Ct W) Bool) :
    (OracleAdv.run (OracleAdv.flagWhen
        (fun s d _ => fsDecBad D (chainKey G s.init) (fun _ => true) s d = true)
        (fsIntOracle G D false)) A (⟨sa, sa, [], false⟩, false)).map (fun y => y.2.2) =
      fsKeyFlag D (chainKey G sa) (fun _ => true) A := by
  set Fr : FSIntSt Sa W Ct → FSIntQuery W Ct → FSIntAns Sa Ct W × FSIntSt Sa W Ct :=
    fun s d => match d with
    | .enc m => (.ct (D.encrypt (G.stretch s.cur).1 m.1 m.2),
        { s with cur := (G.stretch s.cur).2,
                 log := (s.log.length, m.1, m.2, D.encrypt (G.stretch s.cur).1 m.1 m.2) :: s.log })
    | .dec j ad c => (.dec (if s.corr then none else D.decrypt (chainKey G s.init j) c ad), s)
    | .corrupt => (.state s.cur, { s with corr := true }) with hFr
  have hO : fsIntOracle G D false = fun s d => PMF.pure (Fr s d) := by
    funext s d; cases d <;> rfl
  rw [hO, fsKeyFlag]
  refine run_flag_map_eq_of_sim Fr (fsKeyStep D (chainKey G sa))
    (fun s d => fsDecBad D (chainKey G s.init) (fun _ => true) s d)
    (fun s d => fsDecBad D (chainKey G sa) (fun _ => true) s d)
    (fun s s' => s.init = sa ∧ s.cur = (fun x => (G.stretch x).2)^[s.log.length] sa ∧
      s.log = s'.log ∧ s.corr = s'.corr)
    (fun s => s.corr = true) (fun s => s.corr = true) ?_ ?_ ?_ ?_ A _ _ false
    ⟨rfl, rfl, rfl, rfl⟩
  · intro s d h
    cases d <;> simp [hFr, fsDecBad, h]
  · intro s d h
    cases d <;> simp [fsKeyStep, fsDecBad, h]
  · rintro s s' ⟨-, -, -, hcorr⟩ h
    rwa [← hcorr]
  · rintro s s' d ⟨hi, hc, hl, hcorr⟩ hS
    cases d with
    | enc m =>
      simp [hFr, fsKeyStep, fsDecBad, chainKey, hi, hc, hl, hcorr, Function.iterate_succ_apply']
    | dec j ad c =>
      simp [hFr, fsKeyStep, fsDecBad, hi, hcorr, FSIntSt.logDec, ← hl, hc]
    | corrupt => simp [hFr, fsKeyStep, fsDecBad]

omit [SampleableType Ct] in
/-- **Identical until the bad event.** The FS-AEAD integrity advantage is at most the
probability of the bad event in the real game, the keyed oracle with the keys of the chain
from a uniform state. -/
theorem fsaead_int_advantage_le_flag (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (A : OracleAdv (FSIntQuery W Ct) (FSIntAns Sa Ct W) Bool) :
    FSAEAD_Int_Advantage G D A ≤
      ((PMF.uniformFintype Sa).bind fun sa => fsKeyFlag D (chainKey G sa) (fun _ => true) A)
        true := by
  let bad : FSIntSt Sa W Ct → FSIntQuery W Ct → FSIntAns Sa Ct W × FSIntSt Sa W Ct → Prop :=
    fun s d _ => fsDecBad D (chainKey G s.init) (fun _ => true) s d = true
  have hbad : ∀ s d x, ¬ bad s d x → fsIntOracle G D true s d x = fsIntOracle G D false s d x := by
    intro s d x h
    cases d with
    | dec j ad c =>
      simp only [bad, fsDecBad] at h
      by_cases hc : s.corr = true
      · simp [fsIntOracle, hc]
      · simp_all [fsIntOracle]
    | enc m => rfl
    | corrupt => rfl
  have hflag : ∀ sa : Sa, (OracleAdv.run (OracleAdv.flagWhen bad (fsIntOracle G D false)) A
      (⟨sa, sa, [], false⟩, false)).toOuterMeasure {y | y.2.2 = true} =
        fsKeyFlag D (chainKey G sa) (fun _ => true) A true := by
    intro sa
    rw [← OracleGameUpToBad.map_flag_apply, fsInt_real_flag_eq]
  unfold FSAEAD_Int_Advantage fsaead_int_game
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

/-- **The bad event at `j` under uniform keys is detected by `fsIntRed`.** The probability of
the bad event at `j < N` of the keyed oracle with `N` uniform keys and the chain from a uniform
state after them is at most the authenticated-encryption advantage of `fsIntRed G D N j A`. -/
theorem fsKeyFlag_le_aead (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) {N j : ℕ} (hj : j < N)
    (A : OracleAdv (FSIntQuery W Ct) (FSIntAns Sa Ct W) Bool) :
    ((PMF.uniformFintype (Fin N → W)).bind fun v => (PMF.uniformFintype Sa).bind fun sN =>
        fsKeyFlag D (fsKeyOf G (List.ofFn v) sN) (fun i => i == j) A) true ≤
      AEAD_CCA_Advantage D (fsIntRed G D N j A) := by
  have hreal : prTrue (AEAD_CCA_Game_Real D (fsIntRed G D N j A)) Heap.empty =
      ((PMF.uniformFintype (Fin N → W)).bind fun v => (PMF.uniformFintype Sa).bind fun sN =>
        fsKeyFlag D (fsKeyOf G (List.ofFn v) sN) (fun i => i == j) A) true := by
    rw [AEAD_CCA_Game_Real, prTrue_liftPMF]
    simp only [fsIntRed, OracleAdv.run_rand, PMF.map_bind, fsIntRed_run_real,
      update_fsKeyOf_ofFn G _ _ j hj]
    rw [PMF.bind_comm]
    congr 1
    conv_rhs => rw [← Constructions.ECBCPRF.uniform_bind_update (⟨j, hj⟩ : Fin N)]
    rw [PMF.bind_bind]
    simp only [PMF.bind_map, Function.comp_def]
  have hideal : prTrue (AEAD_CCA_Game_Ideal (fsIntRed G D N j A)) Heap.empty = 0 := by
    rw [AEAD_CCA_Game_Ideal, prTrue_liftPMF]
    simp only [fsIntRed, OracleAdv.run_rand, PMF.map_bind, PMF.bind_apply, fsIntRed_run_ideal,
      mul_zero, tsum_zero]
  unfold AEAD_CCA_Advantage Advantage
  grind [tsub_zero, le_max_left]

/-- **FS-AEAD integrity from PRG and AEAD security.** For every adversary `A` that decrypts at
positions below `N` only, the FS-AEAD integrity advantage is at most the FS-PRG advantage of
`fsIntPost G D A` over `N` steps plus the authenticated-encryption advantages of the reductions
`fsIntRed G D N j A` for `j < N`. -/
theorem fsaead_int_advantage_le (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (N : ℕ)
    (A : OracleAdv (FSIntQuery W Ct) (FSIntAns Sa Ct W) Bool)
    (hA : A.IsQueryBoundBy (fsIntFar N) 0) :
    FSAEAD_Int_Advantage G D A ≤
      FSPRG_Advantage G N (fsIntPost G D A) +
        ∑ j ∈ Finset.range N, AEAD_CCA_Advantage D (fsIntRed G D N j A) := by
  have hreal : prTrue ((fsprg_real G N).bind (fsIntPost G D A)) Heap.empty =
      ((PMF.uniformFintype Sa).bind fun sa => fsKeyFlag D (chainKey G sa) (fun _ => true) A)
        true := by
    simp only [fsprg_real, fsIntPost, SPComp.monad_bind_eq, SPComp.bind_assoc, SPComp.pure_bind,
      fsKeyOf_fsprgRun]
    rw [prTrue_sample_bind_liftPMF]
  have hideal : prTrue ((fsprg_ideal (St := Sa) N).bind (fsIntPost G D A)) Heap.empty =
      ((PMF.uniformFintype (Fin N → W)).bind fun v => (PMF.uniformFintype Sa).bind fun sN =>
        fsKeyFlag D (fsKeyOf G (List.ofFn v) sN) (fun _ => true) A) true := by
    simp only [fsprg_ideal, fsIntPost, SPComp.monad_bind_eq, SPComp.bind_assoc,
      SPComp.pure_bind, sample_eq_liftPMF Sa, liftPMF_bind_liftPMF]
    rw [prTrue_sample_bind_liftPMF]
  have hprg : prTrue ((fsprg_real G N).bind (fsIntPost G D A)) Heap.empty -
      prTrue ((fsprg_ideal (St := Sa) N).bind (fsIntPost G D A)) Heap.empty ≤
        FSPRG_Advantage G N (fsIntPost G D A) := le_max_left _ _
  rw [tsub_le_iff_right, hreal, hideal] at hprg
  refine (fsaead_int_advantage_le_flag G D A).trans (hprg.trans (add_le_add le_rfl ?_))
  refine (bind_apply_true_le_sum _ _ _ _ fun v => bind_apply_true_le_sum _ _ _ _ fun sN =>
    fsKeyFlag_apply_le_sum D _ N A hA).trans (Finset.sum_le_sum fun j hj => ?_)
  exact fsKeyFlag_le_aead G D (Finset.mem_range.mp hj) A

/-- **FS-AEAD integrity from PRG and AEAD security, with the PRG advantages.** For every
adversary `A` that decrypts at positions below `N` only, the FS-AEAD integrity advantage is at
most the PRG advantages of the FS-PRG reductions `fsprgRed G N i (fsIntPost G D A)` plus the
authenticated-encryption advantages of the reductions `fsIntRed G D N j A` for `j < N`. -/
theorem fsaead_int_advantage_le_prg (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (N : ℕ)
    (A : OracleAdv (FSIntQuery W Ct) (FSIntAns Sa Ct W) Bool)
    (hA : A.IsQueryBoundBy (fsIntFar N) 0) :
    FSAEAD_Int_Advantage G D A ≤
      ∑ i ∈ Finset.range N, PRG_Advantage G (fsprgRed G N i (fsIntPost G D A)) +
        ∑ j ∈ Finset.range N, AEAD_CCA_Advantage D (fsIntRed G D N j A) :=
  (fsaead_int_advantage_le G D N A hA).trans (add_le_add_left (fsprg_advantage_le G N _) _)

end Games

end CatCrypt.Crypto.Messaging
