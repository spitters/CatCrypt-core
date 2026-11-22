/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Assumptions.AEAD
public import CatCryptCore.Crypto.Assumptions.DualPRF
public import CatCryptCore.Crypto.MultiKeyPRF

/-!
# AEAD under a key derived from a salt by a dual PRF

The deployed Signal Triple Ratchet encrypts each message under the key
`KDF_HYBRID(ec_mk, pq_mk)`: HKDF with salt `pq_mk`, the message key of the post-quantum
ratchet (SPQR), and input key material `ec_mk`, the message key of the Double Ratchet. In the
construction of Dodis, Jost, Katsumata, Prest and Schmidt (*Triple Ratchet*, ePrint 2025/078)
this is the step `K_aead ← KDF3(K^C_aead, K^Q_aead)` with a dual PRF `KDF3`.

For an AEAD `D` with keys in `Kt` and a function `F : Kt → S → Kt`, `saltedAEAD D F` is the
AEAD whose key is the classical key `k` and whose associated data carry a salt `s`: it
encrypts under `F k s`. In the multi-salt game the adversary chooses the salt of each query
and the classical key is uniform and hidden. The bound uses that `F` is a PRF keyed by its
first argument (the left half of a dual PRF). HKDF-Extract is HMAC keyed by the salt, so
this is the PRF property of HMAC in its message input, which Backendal, Bellare, Günther and
Scarlata analyse (*When messages are keys: is HMAC a dual-PRF?*, CRYPTO 2023; reference not
confirmed by DOI).

The proof has two steps. Replacing `F k` by a random function of the salt costs the left
dual-PRF advantage against `saltedPRFRed D A`; the keys of distinct salts are then independent
and uniform. A hybrid over the salts in the order of their first query, as in
`MultiKeyPRF.mkPRF_advantage_le`, replaces the real AEAD oracles of one salt at a time by the
ideal oracles of `AEAD_CCA_Advantage`; the hybrid `j` is the game of `D` against
`saltedAEADRed D A j`. The ideal oracles of all salts together are the ideal oracles of the
salted AEAD. The bound has one AEAD term per salt.

## Main definitions

* `saltedAEAD D F` — the AEAD that encrypts under `F k s` with the salt `s` in the associated
  data
* `saltedPRFRed D A` — the reduction to the left dual-PRF game of `F`
* `saltedAEADRed D A j` — the reduction to the authenticated-encryption game of `D` at the
  salt of rank `j`
* `saltHybGame D A j` — the hybrid game `j`

## Main results

* `aeadReal_salted_eq_realGame` — the real game of `saltedAEAD D F` is the real PRF game of
  `F` against `saltedPRFRed D A`
* `rfGame_saltedPRFRed_eq` — the random-function game against `saltedPRFRed D A` is the
  hybrid `0`
* `saltHybGame_eq_ideal` — the hybrid `u` is the ideal game of the salted AEAD
* `saltedAEAD_advantage_le` — the advantage against `saltedAEAD D F` of an adversary with at
  most `u` salts is at most the left dual-PRF advantage of `F` against `saltedPRFRed D A`
  plus the sum over `j < u` of the advantages of `D` against `saltedAEADRed D A j`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Messaging

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.PRPPRF
open CatCrypt.Crypto.Assumptions CatCrypt.Crypto.MultiKeyPRF CatCrypt.Crypto.HybridArgument
open scoped ENNReal

variable {W : Type} [SampleableType W] {C : Type} [SampleableType C] {AD S : Type}
  {Kt : Type} [SampleableType Kt]

/-! ## The construction -/

/-- The AEAD under a derived key: the associated data `(s, ad)` carry the salt `s`, and the
key `k` encrypts and decrypts as `D` under the key `F k s`. -/
def saltedAEAD (D : AEADDef W C AD Kt) (F : Kt → S → Kt) : AEADDef W C (S × AD) Kt where
  encrypt k pt sa := D.encrypt (F k sa.1) pt sa.2
  decrypt k ct sa := D.decrypt (F k sa.1) ct sa.2

/-- The salt of a query of the salted game. -/
def querySalt : AEAD_CCA_Query W C (S × AD) → S
  | .inl (_, sa) => sa.1
  | .inr (_, sa) => sa.1

/-- A query of the salted game with the salt removed from its associated data. -/
def queryUnsalt : AEAD_CCA_Query W C (S × AD) → AEAD_CCA_Query W C AD
  | .inl (pt, sa) => .inl (pt, sa.2)
  | .inr (ct, sa) => .inr (ct, sa.2)

/-- The answer of the real oracles of `D` under the key `k`. -/
def aeadAnswer (D : AEADDef W C AD Kt) (k : Kt) : AEAD_CCA_Query W C AD → AEAD_CCA_Answer W C
  | .inl (pt, ad) => .inl (D.encrypt k pt ad)
  | .inr (ct, ad) => .inr (D.decrypt k ct ad)

omit [SampleableType C] [SampleableType Kt] in
/-- The real oracles of `D` under `k` answer with `aeadAnswer D k`. -/
theorem aeadRealOracle_eq_pure (D : AEADDef W C AD Kt) (k : Kt) (u : Unit)
    (q : AEAD_CCA_Query W C AD) : aeadRealOracle D k u q = PMF.pure (aeadAnswer D k q, ()) := by
  rcases q with ⟨pt, ad⟩ | ⟨ct, ad⟩ <;> rfl

omit [SampleableType C] [SampleableType Kt] in
/-- The answer of `saltedAEAD D F` under `k` is the answer of `D` under `F k s` at the salt
`s` of the query. -/
theorem aeadAnswer_saltedAEAD (D : AEADDef W C AD Kt) (F : Kt → S → Kt) (k : Kt)
    (q : AEAD_CCA_Query W C (S × AD)) :
    aeadAnswer (saltedAEAD D F) k q = aeadAnswer D (F k (querySalt q)) (queryUnsalt q) := by
  rcases q with ⟨pt, s, ad⟩ | ⟨ct, s, ad⟩ <;> rfl

/-! ## The dual-PRF step -/

/-- One query of `saltedPRFRed D`: query the salt to the PRF oracle and answer with the real
oracles of `D` under the returned key. -/
noncomputable def saltedKeyImpl (D : AEADDef W C AD Kt) (_ : Unit)
    (q : AEAD_CCA_Query W C (S × AD)) : OracleAdv S Kt (AEAD_CCA_Answer W C × Unit) :=
  .query (querySalt q) fun k => .ret (aeadAnswer D k (queryUnsalt q), ())

/-- **Reduction** to the left dual-PRF game of `F`: run `A`, answering each query with the
real oracles of `D` under the key that the PRF oracle returns at the salt of the query. -/
noncomputable def saltedPRFRed (D : AEADDef W C AD Kt) (A : AEAD_CCA_Adversary W C (S × AD)) :
    OracleAdv S Kt Bool :=
  (OracleAdv.simulate (saltedKeyImpl D) A ()).bind fun x => .ret x.1

omit [SampleableType C] in
/-- The real game of `saltedAEAD D F` is the real PRF game of `F` against
`saltedPRFRed D A`. -/
theorem aeadReal_salted_eq_realGame (D : AEADDef W C AD Kt) (F : Kt → S → Kt)
    (A : AEAD_CCA_Adversary W C (S × AD)) :
    AEAD_CCA_Game_Real (saltedAEAD D F) A = realGame F (saltedPRFRed D A) := by
  unfold AEAD_CCA_Game_Real realGame saltedPRFRed
  congr 2
  funext k
  rw [OracleAdv.run_simulate_fst]
  symm
  exact Constructions.SIV.run_map_fst_eq_of_map_state _ _ (fun _ => ())
    (fun _ q => by
      simp [OracleAdv.simOracle, saltedKeyImpl, keyedOracle, aeadRealOracle_eq_pure,
        aeadAnswer_saltedAEAD, PMF.pure_map])
    A ((), ())

/-! ## The hybrids over the salts -/

variable [DecidableEq S]

/-- The hybrid oracle `j`: a query at a salt of rank below `j` is answered by the ideal oracles
of the authenticated-encryption game with the log of that rank; at rank `j` or more by the
real oracles of `D` under the key of that rank, drawn uniformly when the rank is first
queried. -/
noncomputable def saltHybOracle [DecidableEq AD] (D : AEADDef W C AD Kt) (j : ℕ)
    (s : HybState S (W × AD) C Kt) (q : AEAD_CCA_Query W C (S × AD)) :
    PMF (AEAD_CCA_Answer W C × HybState S (W × AD) C Kt) :=
  if rank s.1 (querySalt q) < j then
    (aeadIdealOracle (s.2.1 (rank s.1 (querySalt q))) (queryUnsalt q)).map fun x =>
      (x.1, (addIdx s.1 (querySalt q), Function.update s.2.1 (rank s.1 (querySalt q)) x.2,
        s.2.2))
  else
    match s.2.2 (rank s.1 (querySalt q)) with
    | some k => PMF.pure (aeadAnswer D k (queryUnsalt q), (addIdx s.1 (querySalt q), s.2.1, s.2.2))
    | none => (PMF.uniformFintype Kt).map fun k =>
        (aeadAnswer D k (queryUnsalt q), (addIdx s.1 (querySalt q), s.2.1,
          Function.update s.2.2 (rank s.1 (querySalt q)) (some k)))

/-- The hybrid game `j`. -/
noncomputable def saltHybGame [DecidableEq AD] (D : AEADDef W C AD Kt)
    (A : AEAD_CCA_Adversary W C (S × AD)) (j : ℕ) : SPComp Bool :=
  liftPMF ((OracleAdv.run (saltHybOracle D j) A hybInit).map Prod.fst)

/-- One query of `saltedAEADRed D A j`: at a salt of rank below `j`, an answer drawn from the
ideal oracles with the log of that rank; at rank `j`, the query without its salt to the
oracles of the reduction; above `j`, the real oracles of `D` under the key of that rank, drawn
uniformly when the rank is first queried. -/
noncomputable def saltHybImpl [DecidableEq AD] (D : AEADDef W C AD Kt) (j : ℕ)
    (s : HybState S (W × AD) C Kt) (q : AEAD_CCA_Query W C (S × AD)) :
    OracleAdv (AEAD_CCA_Query W C AD) (AEAD_CCA_Answer W C)
      (AEAD_CCA_Answer W C × HybState S (W × AD) C Kt) :=
  if rank s.1 (querySalt q) < j then
    .rand (aeadIdealOracle (s.2.1 (rank s.1 (querySalt q))) (queryUnsalt q)) fun x =>
      .ret (x.1, (addIdx s.1 (querySalt q), Function.update s.2.1 (rank s.1 (querySalt q)) x.2,
        s.2.2))
  else if rank s.1 (querySalt q) = j then
    .query (queryUnsalt q) fun a => .ret (a, (addIdx s.1 (querySalt q), s.2.1, s.2.2))
  else
    match s.2.2 (rank s.1 (querySalt q)) with
    | some k => .ret (aeadAnswer D k (queryUnsalt q), (addIdx s.1 (querySalt q), s.2.1, s.2.2))
    | none => .rand (PMF.uniformFintype Kt) fun k =>
        .ret (aeadAnswer D k (queryUnsalt q), (addIdx s.1 (querySalt q), s.2.1,
          Function.update s.2.2 (rank s.1 (querySalt q)) (some k)))

/-- **Reduction** to the authenticated-encryption game of `D` at the salt of rank `j`: run
`A`, answering each query by `saltHybImpl D j`. -/
noncomputable def saltedAEADRed [DecidableEq AD] (D : AEADDef W C AD Kt)
    (A : AEAD_CCA_Adversary W C (S × AD)) (j : ℕ) : AEAD_CCA_Adversary W C AD :=
  (OracleAdv.simulate (saltHybImpl D j) A hybInit).bind fun x => .ret x.1

section Hybrid

variable [DecidableEq AD]

/-- A call of the hybrid oracle at a rank other than `j` commutes with setting the key of
rank `j`. -/
theorem saltHybOracle_setKey (D : AEADDef W C AD Kt) (j : ℕ) (v : Option Kt)
    (s : HybState S (W × AD) C Kt) (q : AEAD_CCA_Query W C (S × AD))
    (hq : rank s.1 (querySalt q) ≠ j) :
    saltHybOracle D j (setKey j v s) q =
      (saltHybOracle D j s q).map (Prod.map id (setKey j v)) := by
  have hk : Function.update s.2.2 j v (rank s.1 (querySalt q)) =
      s.2.2 (rank s.1 (querySalt q)) := Function.update_of_ne hq _ _
  unfold saltHybOracle setKey
  dsimp only
  split_ifs with hr
  · rw [PMF.map_comp]
    rfl
  · rw [hk]
    rcases h : s.2.2 (rank s.1 (querySalt q)) with _ | k
    · simp only [PMF.map_comp]
      congr 1
      funext k
      simp [Function.update_comm hq]
    · simp [PMF.pure_map]

/-- **Deferred key.** The key of rank `j` drawn before the run gives the output of the key
drawn when the rank is first queried. -/
theorem uniform_bind_run_saltHyb_setKey (D : AEADDef W C AD Kt) (j : ℕ) {α : Type}
    (A : OracleAdv (AEAD_CCA_Query W C (S × AD)) (AEAD_CCA_Answer W C) α)
    (s : HybState S (W × AD) C Kt) :
    (PMF.uniformFintype Kt).bind (fun k =>
        (OracleAdv.run (saltHybOracle D j) A (setKey j (some k) s)).map Prod.fst) =
      (OracleAdv.run (saltHybOracle D j) A (setKey j none s)).map Prod.fst := by
  have e : ∀ v w, setKey (N := S) (D := W × AD) (R := C) j v (setKey j w s) = setKey j v s :=
    fun v w => by simp only [setKey, Function.update_idem]
  have h := OracleAdv.run_map_fst_eq_bind_run_set_of_trigger (PMF.uniformFintype Kt)
    (saltHybOracle D j) (fun k => setKey j (some k)) (fun t => t.2.2 j = none)
    (fun t q => rank t.1 (querySalt q) = j) (fun t q ht hr => ?_)
    (fun k t q _ hr => saltHybOracle_setKey D j _ t q hr)
    (fun t q ht hr x hx => ?_) A (setKey j none s) (by simp only [setKey, Function.update_self])
  · simp only [e] at h
    exact h.symm
  · simp only [saltHybOracle, setKey, hr, lt_self_iff_false, ↓reduceIte, Function.update_self,
      ht]
    rfl
  · have h0 : setKey j none t = t := by rw [setKey, ← ht, Function.update_eq_self]
    rw [← h0, saltHybOracle_setKey D j none t q hr] at hx
    obtain ⟨y, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hx
    simp only [Prod.map_snd, setKey, Function.update_self]

/-- A query of `saltHybImpl D j` run against the real oracles of `D` under `k` is a call of
the hybrid oracle `j` with `k` as the key of rank `j`. -/
theorem simOracle_real_saltHybImpl (D : AEADDef W C AD Kt) (j : ℕ) (k : Kt)
    (s : HybState S (W × AD) C Kt) (q : AEAD_CCA_Query W C (S × AD)) :
    (OracleAdv.simOracle (saltHybImpl D j) (aeadRealOracle D k) (s, ()) q).map
        (Prod.map id fun p => setKey j (some k) p.1) =
      saltHybOracle D j (setKey j (some k) s) q := by
  have hbp : ∀ {α β : Type} (p : PMF α) (f : α → β),
      p.bind (fun a => PMF.pure (f a)) = p.map f := fun _ _ => rfl
  unfold OracleAdv.simOracle saltHybImpl saltHybOracle setKey
  dsimp only
  split_ifs with h1 h2
  · simp [PMF.map_comp, Function.comp_def, hbp]
  · simp [h2, aeadRealOracle_eq_pure, PMF.pure_map]
  · have hne : rank s.1 (querySalt q) ≠ j := h2
    rw [Function.update_of_ne hne]
    rcases hk : s.2.2 (rank s.1 (querySalt q)) with _ | k'
    · simp [PMF.map_comp, Function.comp_def, hbp, Function.update_comm hne]
    · simp [PMF.pure_map]

/-- A query of `saltHybImpl D j` run against the ideal oracles with log `t` is a call of the
hybrid oracle `j + 1` with `t` as the log of rank `j`. -/
theorem simOracle_ideal_saltHybImpl (D : AEADDef W C AD Kt) (j : ℕ)
    (s : HybState S (W × AD) C Kt) (t : List ((W × AD) × C))
    (q : AEAD_CCA_Query W C (S × AD)) :
    (OracleAdv.simOracle (saltHybImpl D j) aeadIdealOracle (s, t) q).map
        (Prod.map id fun p => (p.1.1, Function.update p.1.2.1 j p.2, p.1.2.2)) =
      saltHybOracle D (j + 1) (s.1, Function.update s.2.1 j t, s.2.2) q := by
  have hbp : ∀ {α β : Type} (p : PMF α) (f : α → β),
      p.bind (fun a => PMF.pure (f a)) = p.map f := fun _ _ => rfl
  unfold OracleAdv.simOracle saltHybImpl saltHybOracle
  dsimp only
  by_cases h1 : rank s.1 (querySalt q) < j
  · have hne : rank s.1 (querySalt q) ≠ j := by omega
    rw [ite_eq_left h1, ite_eq_left (by omega), Function.update_of_ne hne]
    simp only [OracleAdv.run_rand, OracleAdv.run_ret, PMF.map_bind, PMF.pure_map, Prod.map,
      id]
    rw [PMF.map]
    refine congrArg _ (funext fun x => ?_)
    refine congrArg PMF.pure (Prod.ext rfl (Prod.ext rfl (Prod.ext ?_ rfl)))
    funext r
    by_cases hr : r = rank s.1 (querySalt q)
    · subst hr; simp [Function.update_of_ne hne]
    · simp [Function.update_of_ne hr]
      grind
  · by_cases h2 : rank s.1 (querySalt q) = j
    · rw [ite_eq_right h1, ite_eq_left h2, ite_eq_left (by omega), h2]
      simp [PMF.map_comp, Function.comp_def, hbp]
    · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right (by omega)]
      rcases hk : s.2.2 (rank s.1 (querySalt q)) with _ | k'
      · simp [PMF.map_comp, Function.comp_def, hbp]
      · simp [PMF.pure_map]

/-- The real game of `D` against `saltedAEADRed D A j` is the hybrid `j`. -/
theorem aeadReal_saltedAEADRed_eq (D : AEADDef W C AD Kt) (A : AEAD_CCA_Adversary W C (S × AD))
    (j : ℕ) : AEAD_CCA_Game_Real D (saltedAEADRed D A j) = saltHybGame D A j := by
  unfold AEAD_CCA_Game_Real saltHybGame saltedAEADRed
  congr 1
  simp only [OracleAdv.run_simulate_fst]
  have h : ∀ k, (OracleAdv.run (OracleAdv.simOracle (saltHybImpl D j) (aeadRealOracle D k)) A
      (hybInit, ())).map Prod.fst =
      (OracleAdv.run (saltHybOracle D j) A (setKey j (some k) hybInit)).map Prod.fst := fun k =>
    Constructions.SIV.run_map_fst_eq_of_map_state _ _ (fun p => setKey j (some k) p.1)
      (fun p q => by obtain ⟨s, ⟨⟩⟩ := p; exact simOracle_real_saltHybImpl D j k s q) A
      (hybInit, ())
  have hi : setKey j none (hybInit : HybState S (W × AD) C Kt) = hybInit := by
    simp [setKey, hybInit]
  simp only [h]
  rw [uniform_bind_run_saltHyb_setKey, hi]

/-- The ideal game against `saltedAEADRed D A j` is the hybrid `j + 1`. -/
theorem aeadIdeal_saltedAEADRed_eq (D : AEADDef W C AD Kt) (A : AEAD_CCA_Adversary W C (S × AD))
    (j : ℕ) : AEAD_CCA_Game_Ideal (saltedAEADRed D A j) = saltHybGame D A (j + 1) := by
  unfold AEAD_CCA_Game_Ideal saltHybGame saltedAEADRed
  congr 1
  rw [OracleAdv.run_simulate_fst,
    Constructions.SIV.run_map_fst_eq_of_map_state _ (saltHybOracle D (j + 1))
      (fun p => (p.1.1, Function.update p.1.2.1 j p.2, p.1.2.2))
      (fun p q => simOracle_ideal_saltHybImpl D j p.1 p.2 q) A (hybInit, [])]
  congr 2
  simp [hybInit]

/-- The random-function game against `saltedPRFRed D A` is the hybrid `0`. -/
theorem rfGame_saltedPRFRed_eq (D : AEADDef W C AD Kt) (A : AEAD_CCA_Adversary W C (S × AD))
    (u : ℕ) (hA : A.IndexBound querySalt ∅ u) :
    rfGame (saltedPRFRed D A) = saltHybGame D A 0 := by
  unfold rfGame saltHybGame saltedPRFRed
  congr 1
  rw [OracleAdv.run_simulate_fst]
  symm
  refine run_map_fst_eq_of_indexBound querySalt _ _
    (fun s s' _ => RankRel none s.1 s.2.2 (fun n => List.lookup n s'.2)) u ?_ A ∅ hA hybInit
    ((), []) ?_
  · rintro s ⟨⟨⟩, tK⟩ G q h -
    have hk := (h.extend (querySalt q)).apply
    dsimp only at hk
    rcases hl : List.lookup (querySalt q) tK with _ | k
    · refine ⟨Kt, PMF.uniformFintype Kt, fun k => aeadAnswer D k (queryUnsalt q),
        fun k => (addIdx s.1 (querySalt q), s.2.1,
          Function.update s.2.2 (rank s.1 (querySalt q)) (some k)),
        fun k => ((), (querySalt q, k) :: tK), ?_, ?_, fun k => ?_⟩
      · simp [saltHybOracle, hk, hl]
      · simp [saltedKeyImpl, OracleAdv.simOracle, rfOracle, hl, Function.comp_def,
          PMF.map_bind, PMF.pure_map]
        rfl
      · have := (h.extend (querySalt q)).update (some k)
        convert this using 1
        funext m
        by_cases hm : m = querySalt q
        · subst hm; simp
        · have hb : (m == querySalt q) = false := by simpa using hm
          simp [List.lookup, hb, Function.update_of_ne hm]
    · refine ⟨Unit, PMF.pure (), fun _ => aeadAnswer D k (queryUnsalt q),
        fun _ => (addIdx s.1 (querySalt q), s.2.1, s.2.2), fun _ => ((), tK), ?_, ?_,
        fun _ => h.extend (querySalt q)⟩
      · simp [saltHybOracle, hk, hl, PMF.pure_map]
      · simp [saltedKeyImpl, OracleAdv.simOracle, rfOracle, hl, PMF.pure_map]
  · convert rankRel_nil (N := S) (none : Option Kt) using 1 <;> rfl

/-! ## The ideal oracles of all salts -/

/-- The entries of a log of the salted ideal oracles at the salt `n`, with the salt removed. -/
def saltLog (n : S) (T : List ((W × (S × AD)) × C)) : List ((W × AD) × C) :=
  T.filterMap fun e => if e.1.2.1 = n then some ((e.1.1, e.1.2.2), e.2) else none

omit [SampleableType W] [SampleableType C] [DecidableEq AD] in
/-- `saltLog` of a log with one more entry. -/
theorem saltLog_cons (n : S) (e : (W × (S × AD)) × C) (T : List ((W × (S × AD)) × C)) :
    saltLog n (e :: T) =
      if e.1.2.1 = n then ((e.1.1, e.1.2.2), e.2) :: saltLog n T else saltLog n T := by
  unfold saltLog
  split_ifs with h <;> simp [h]

omit [SampleableType C] in
/-- The ciphertext recorded for `(pt, (n, ad))` is the one recorded for `(pt, ad)` in the log
of the salt `n`. -/
theorem lookup_saltLog (pt : W) (n : S) (ad : AD) (T : List ((W × (S × AD)) × C)) :
    List.lookup (pt, (n, ad)) T = List.lookup (pt, ad) (saltLog n T) := by
  induction T with
  | nil => rfl
  | cons e T ih =>
    obtain ⟨⟨pt', n', ad'⟩, c⟩ := e
    rw [saltLog_cons]
    by_cases hn : n' = n
    · subst hn
      simp only [ite_true]
      grind
    · grind

omit [SampleableType W] in
/-- Decryption from the log at the associated data `(n, ad)` is decryption from the log of the
salt `n` at `ad`. -/
theorem aeadLogDecrypt_saltLog (ct : C) (n : S) (ad : AD) (T : List ((W × (S × AD)) × C)) :
    aeadLogDecrypt T ct (n, ad) = aeadLogDecrypt (saltLog n T) ct ad := by
  induction T with
  | nil => rfl
  | cons e T ih =>
    obtain ⟨⟨pt', n', ad'⟩, c⟩ := e
    rw [saltLog_cons]
    unfold aeadLogDecrypt at ih ⊢
    by_cases hn : n' = n
    · subst hn
      grind
    · grind

/-- The hybrid `u` of an adversary asking at most `u` salts is the ideal game of the salted
AEAD. -/
theorem saltHybGame_eq_ideal (D : AEADDef W C AD Kt) (A : AEAD_CCA_Adversary W C (S × AD))
    (u : ℕ) (hA : A.IndexBound querySalt ∅ u) :
    saltHybGame D A u = AEAD_CCA_Game_Ideal A := by
  unfold AEAD_CCA_Game_Ideal saltHybGame
  congr 1
  refine run_map_fst_eq_of_indexBound querySalt _ _
    (fun s T G => s.1.Nodup ∧ s.1.toFinset = G ∧
      RankRel [] s.1 s.2.1 (fun n => saltLog n T)) u ?_ A ∅ hA hybInit [] ?_
  · rintro s T G q ⟨hnd, hG, h⟩ hc
    have hr : rank s.1 (querySalt q) < u := by
      have := rank_lt_length s.1 (querySalt q)
      rw [← List.toFinset_card_of_nodup (nodup_addIdx hnd _), toFinset_addIdx, hG] at this
      omega
    have hk : s.2.1 (rank s.1 (querySalt q)) = saltLog (querySalt q) T :=
      (h.extend (querySalt q)).apply
    rcases q with ⟨pt, n, ad⟩ | ⟨ct, n, ad⟩ <;> simp only [querySalt] at hr hk
    · rcases hl : List.lookup (pt, (n, ad)) T with _ | c
      · refine ⟨C, PMF.uniformFintype C, fun c => .inl c,
          fun c => (addIdx s.1 n,
            Function.update s.2.1 (rank s.1 n) (((pt, ad), c) :: saltLog n T), s.2.2),
          fun c => ((pt, (n, ad)), c) :: T, ?_, ?_,
          fun c => ⟨nodup_addIdx hnd n, by rw [toFinset_addIdx, hG]; rfl, ?_⟩⟩
        · have hl' : List.lookup (pt, ad) (saltLog n T) = none := by
            rw [← lookup_saltLog]; exact hl
          simp [saltHybOracle, querySalt, queryUnsalt, hr, hk, aeadIdealOracle, hl',
            PMF.map_comp, Function.comp_def]
        · simp [aeadIdealOracle, hl]
        · have := (h.extend n).update (((pt, ad), c) :: saltLog n T)
          convert this using 1
          funext m
          rw [saltLog_cons]
          by_cases hm : m = n
          · subst hm; simp
          · simp [hm, Ne.symm hm]
      · refine ⟨Unit, PMF.pure (), fun _ => .inl c, fun _ => (addIdx s.1 n, s.2.1, s.2.2),
          fun _ => T, ?_, ?_, fun _ => ⟨nodup_addIdx hnd n, by rw [toFinset_addIdx, hG]; rfl,
            h.extend n⟩⟩
        · have hl' : List.lookup (pt, ad) (saltLog n T) = some c := by
            rw [← lookup_saltLog]; exact hl
          have hu : Function.update s.2.1 (rank s.1 n) (saltLog n T) = s.2.1 := by
            rw [← hk, Function.update_eq_self]
          simp [saltHybOracle, querySalt, queryUnsalt, hr, hk, aeadIdealOracle, hl', hu,
            PMF.pure_map]
        · simp [aeadIdealOracle, hl, PMF.pure_map]
    · refine ⟨Unit, PMF.pure (), fun _ => .inr (aeadLogDecrypt (saltLog n T) ct ad),
        fun _ => (addIdx s.1 n, s.2.1, s.2.2), fun _ => T, ?_, ?_,
        fun _ => ⟨nodup_addIdx hnd n, by rw [toFinset_addIdx, hG]; rfl, h.extend n⟩⟩
      · have hu : Function.update s.2.1 (rank s.1 n) (saltLog n T) = s.2.1 := by
          rw [← hk, Function.update_eq_self]
        simp [saltHybOracle, querySalt, queryUnsalt, hr, hk, hu, aeadIdealOracle, PMF.pure_map]
      · simp [aeadIdealOracle, aeadLogDecrypt_saltLog, PMF.pure_map]
  · refine ⟨List.nodup_nil, rfl, ?_⟩
    convert rankRel_nil (N := S) ([] : List ((W × AD) × C)) using 1 <;> rfl

/-! ## The bound -/

/-- **AEAD under a salted key.** For every adversary `A` of the authenticated-encryption game
of `saltedAEAD D F` that asks at no more than `u` distinct salts, the advantage is at most the
left dual-PRF advantage of `F` against `saltedPRFRed D A` plus the sum over `j < u` of the
authenticated-encryption advantages of `D` against `saltedAEADRed D A j`. -/
theorem saltedAEAD_advantage_le (D : AEADDef W C AD Kt) (F : Kt → S → Kt)
    (A : AEAD_CCA_Adversary W C (S × AD)) (u : ℕ) (hA : A.IndexBound querySalt ∅ u) :
    AEAD_CCA_Advantage (saltedAEAD D F) A ≤
      DualPRF_Left_Advantage F (saltedPRFRed D A) +
        ∑ j ∈ Finset.range u, AEAD_CCA_Advantage D (saltedAEADRed D A j) := by
  unfold AEAD_CCA_Advantage DualPRF_Left_Advantage PRF_q_Advantage
  rw [aeadReal_salted_eq_realGame, ← saltHybGame_eq_ideal D A u hA]
  refine (advantage_triangle _ (rfGame (saltedPRFRed D A)) _).trans (add_le_add le_rfl ?_)
  rw [rfGame_saltedPRFRed_eq D A u hA]
  refine (advantage_hybrid_dep_bool (saltHybGame D A) u).trans (le_of_eq ?_)
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [aeadReal_saltedAEADRed_eq, aeadIdeal_saltedAEADRed_eq]

end Hybrid

end CatCrypt.Crypto.Messaging
