/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.PKE.Games
public import CatCryptCore.Crypto.KEM.Games
public import CatCryptCore.Crypto.Constructions.ECBCPRFFlag

/-!
# The U-transforms of Hofheinz–Hövelmanns–Kiltz in the random-oracle model

For a public-key encryption scheme `P` with messages `M` and ciphertexts `C` and a
random oracle `H : M × C → K`, the KEM `uNotBot P = U̸⊥[P, H]` has secret key
`(sk, s)` with `s` uniform in `M`; encapsulation samples `m`, encrypts it to `c`
and returns `K = H(m, c)`; decapsulation returns `H(m', c)` for `m' = Dec(sk, c)`
and `H(s, c)` when decryption rejects. `uBot P = U⊥[P, H]` returns `none` on
rejection instead.

## Main definitions

* `uNotBot`, `uBot` — the transforms
* `uReduction B` — the OW-PCA adversary built from an IND-CCA adversary `B` against
  `uNotBot P`: it samples a key `k*`, runs `B` on `(pk, c*, k*)`, answers each
  random-oracle query `(m, c)` with one plaintext-checking query — from a table
  indexed by `c` when `Pco(m, c) = 1`, from a table indexed by `(m, c)` otherwise,
  and with `k*` when `c = c*` and `Pco(m, c*) = 1` — answers decapsulation queries
  from the table indexed by `c`, and outputs a message `m` with `Pco(m, c*) = 1`
  found among the queries

## Main results

* `uNotBot_indcca` — for every IND-CCA adversary `B` with at most `qH` random-oracle
  queries,
  `romINDCCAAdvantage (uNotBot P) B ≤ owpcaAdvantage P (uReduction B) + qH/|M| + P.corrErr`

The advantage on the left is the distance between the real-key and random-key
games; `P.corrErr` is the decryption-failure probability of a fresh encryption of a
uniform message.

## Proof outline

1. The real-key and random-key games agree until `B` queries the random oracle at
   the challenge point `(m*, c*)` (`oFlag`).
2. When `Dec(sk, c*) = m*`, the table of the random oracle is re-indexed: points
   `(m, c)` with `m = Dec(sk, c)` (or `m = s` when decryption rejects) are indexed
   by `c`, which is how decapsulation reads them (`oTwo`).
3. Replacing the selector `m = Dec(sk, c)`-or-`s` by the plaintext-checking
   predicate changes the oracle only at queries with `m = s`, which happen with
   probability at most `qH/|M|` because the oracle does not depend on `s`.
4. The resulting oracle is the simulation of `uReduction B`, and a hit at the
   challenge point supplies the reduction with a message passing `Pco(·, c*)`.

## References

* D. Hofheinz, K. Hövelmanns, E. Kiltz, *A Modular Analysis of the
  Fujisaki–Okamoto Transformation*, TCC 2017, ePrint 2017/604, Theorem 3.4.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.KEM.FOTransformU

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.PRPPRF
open CatCrypt.Crypto.PKE.Games CatCrypt.Crypto.KEM.Games
open CatCrypt.Crypto.Constructions.ECBCPRF (toOuterMeasure_flag_eq toOuterMeasure_le_add_flag
  toOuterMeasure_eq_of_subset_false toOuterMeasure_add_compl run_support_rel)
open scoped ENNReal

variable {PK SK M C R K : Type} [Fintype R] [Nonempty R] [Fintype M] [Nonempty M]
  [DecidableEq M] [DecidableEq C] [Fintype K] [Nonempty K]

/-! ## The transforms -/

/-- The key point read by decapsulation of `c`: `(Dec(sk, c), c)`, or `(s, c)` when
decryption rejects. -/
def decIdx (P : Scheme PK SK M C R) (sk : SK) (s : M) (c : C) : M × C :=
  ((P.dec sk c).getD s, c)

/-- The transform `U̸⊥[P, H]` with implicit rejection. -/
noncomputable def uNotBot (P : Scheme PK SK M C R) :
    KEM.Games.ROMScheme PK (SK × M) K C (M × C) K where
  keygen := P.keygen.bind fun ks => (PMF.uniformOfFintype M).map fun s => (ks.1, (ks.2, s))
  encaps pk := .rand (PMF.uniformOfFintype M) fun m => .rand (PMF.uniformOfFintype R) fun r =>
    .query (m, P.enc pk m r) fun k => .ret (k, P.enc pk m r)
  decaps sk c := .query (decIdx P sk.1 sk.2 c) fun k => .ret (some k)

/-- The transform `U⊥[P, H]` with explicit rejection. -/
noncomputable def uBot (P : Scheme PK SK M C R) : KEM.Games.ROMScheme PK SK K C (M × C) K where
  keygen := P.keygen
  encaps pk := .rand (PMF.uniformOfFintype M) fun m => .rand (PMF.uniformOfFintype R) fun r =>
    .query (m, P.enc pk m r) fun k => .ret (k, P.enc pk m r)
  decaps sk c := match P.dec sk c with
    | some m => .query (m, c) fun k => .ret (some k)
    | none => .ret none

/-! ## The reduction -/

variable (M C K) in
/-- The state of the simulation: the table indexed by ciphertexts, the table
indexed by message–ciphertext pairs, and a message found to decrypt the challenge. -/
structure SimState where
  /-- Keys indexed by ciphertexts. -/
  LD : C → Option K
  /-- Keys indexed by message–ciphertext pairs. -/
  LQ : M × C → Option K
  /-- A message `m` with `Pco(m, c*) = 1` queried by the adversary. -/
  found : Option M

/-- The initial simulation state. -/
def SimState.init : SimState M C K := ⟨fun _ => none, fun _ => none, none⟩

/-- Answer from the table indexed by `c`, sampling and recording a fresh key. -/
noncomputable def lazyDProg {A : Type} (st : SimState M C K) (c : C) (w : K → A) :
    OracleAdv (M × C) Bool (A × SimState M C K) :=
  match st.LD c with
  | some k => .ret (w k, st)
  | none => .rand (PMF.uniformOfFintype K) fun k => .ret (w k, { st with LD := Function.update st.LD c (some k) })

/-- Answer from the table indexed by `(m, c)`, sampling and recording a fresh key. -/
noncomputable def lazyQProg {A : Type} (st : SimState M C K) (q : M × C) (w : K → A) :
    OracleAdv (M × C) Bool (A × SimState M C K) :=
  match st.LQ q with
  | some k => .ret (w k, st)
  | none => .rand (PMF.uniformOfFintype K) fun k => .ret (w k, { st with LQ := Function.update st.LQ q (some k) })

/-- The simulation of the random oracle and the decapsulation oracle from the
challenge `c*`, the key `k*` and plaintext-checking queries. -/
noncomputable def simImpl (cstar : C) (kstar : K) (st : SimState M C K) :
    (M × C) ⊕ C → OracleAdv (M × C) Bool ((K ⊕ Option K) × SimState M C K)
  | .inl q => .query q fun b =>
      if b then
        (if q.2 = cstar then .ret (.inl kstar, { st with found := some q.1 })
         else lazyDProg st q.2 Sum.inl)
      else lazyQProg st q Sum.inl
  | .inr c => if c = cstar then .ret (.inr none, st) else lazyDProg st c fun k => .inr (some k)

omit [Fintype M] [Nonempty M] [DecidableEq M] in
theorem isQueryBound_lazyDProg {A : Type} (st : SimState M C K) (c : C) (w : K → A) :
    (lazyDProg st c w).IsQueryBound 0 := by
  unfold lazyDProg; split
  · trivial
  · exact fun _ => trivial

omit [Fintype M] [Nonempty M] in
theorem isQueryBound_lazyQProg {A : Type} (st : SimState M C K) (q : M × C) (w : K → A) :
    (lazyQProg st q w).IsQueryBound 0 := by
  unfold lazyQProg; split
  · trivial
  · exact fun _ => trivial

omit [Fintype M] [Nonempty M] in
theorem isQueryBound_simImpl (cstar : C) (kstar : K) (st : SimState M C K) (d : (M × C) ⊕ C) :
    (simImpl cstar kstar st d).IsQueryBound (Sum.elim (fun _ => 1) (fun _ => 0) d) := by
  cases d with
  | inl q =>
    intro b
    dsimp only
    split
    · split
      · trivial
      · exact isQueryBound_lazyDProg _ _ _
    · exact isQueryBound_lazyQProg _ _ _
  | inr c =>
    dsimp only [simImpl, Sum.elim_inr]; split
    · trivial
    · exact isQueryBound_lazyDProg _ _ _

/-- The OW-PCA adversary built from an IND-CCA adversary `B` against `uNotBot P`. It
runs `B` once on `(pk, c*, k*)` for a uniform key `k*`, asks one
plaintext-checking query per random-oracle query of `B`, and outputs the message
found to decrypt `c*` (an arbitrary message if none was found). -/
noncomputable def uReduction {qH qD : ℕ} (B : ROMINDCCAAdversary PK K C (M × C) K qH qD) :
    OWPCAAdversary PK M C qH where
  run pk cstar := .rand (PMF.uniformOfFintype K) fun kstar =>
    (OracleAdv.simulate (simImpl cstar kstar) (B.run pk cstar kstar) SimState.init).bind
      fun x => .ret (x.2.found.getD (Classical.arbitrary M))
  isQueryBound pk cstar kstar := by
    have h := OracleAdv.isQueryBound_bind
      (OracleAdv.isQueryBound_simulate (simImpl cstar kstar) _ (isQueryBound_simImpl cstar kstar)
        (B.isQueryBoundH pk cstar kstar) SimState.init)
      (f := fun x => .ret (x.2.found.getD (Classical.arbitrary M))) (n := 0) fun _ => trivial
    simpa using h

/-! ## The challenge hop -/

section ChallengeHop

variable (PK SK M R K) in
/-- The randomness of the IND-CCA experiment: key pair, rejection seed, challenge
message and coins, and the two candidate keys. -/
structure Draw where
  /-- The public key. -/
  pk : PK
  /-- The secret key of `P`. -/
  sk : SK
  /-- The rejection seed. -/
  s : M
  /-- The challenge message. -/
  m : M
  /-- The challenge coins. -/
  r : R
  /-- The encapsulated key. -/
  k₀ : K
  /-- The independent key. -/
  k₁ : K

variable (P : Scheme PK SK M C R)

/-- The joint distribution of the randomness of the IND-CCA experiment. -/
noncomputable def setup : PMF (Draw PK SK M R K) :=
  P.keygen.bind fun ks => (PMF.uniformOfFintype M).bind fun s =>
    (PMF.uniformOfFintype M).bind fun m => (PMF.uniformOfFintype R).bind fun r =>
      (PMF.uniformOfFintype K).bind fun k₀ => (PMF.uniformOfFintype K).map fun k₁ =>
        ⟨ks.1, ks.2, s, m, r, k₀, k₁⟩

/-- The challenge ciphertext of a draw. -/
def Draw.c (x : Draw PK SK M R K) : C := P.enc x.pk x.m x.r

/-- Exchange the two candidate keys of a draw. -/
def Draw.swap (x : Draw PK SK M R K) : Draw PK SK M R K := { x with k₀ := x.k₁, k₁ := x.k₀ }

omit [DecidableEq M] [DecidableEq C] in
theorem setup_map_swap : (setup (K := K) P).map Draw.swap = setup P := by
  simp only [setup, PMF.map_bind, PMF.map_comp]
  refine congrArg _ (funext fun ks => congrArg _ (funext fun s => congrArg _ (funext fun m =>
    congrArg _ (funext fun r => ?_))))
  simp only [PMF.map, Function.comp_def, Draw.swap]
  exact PMF.bind_comm _ _ _

/-- The oracle of the IND-CCA experiment for `uNotBot P` with the point `kpt` of the
random oracle removed from the table: a query at `kpt` returns `v` and sets the
flag. -/
noncomputable def oFlag (sk : SK) (s : M) (kpt : M × C) (v : K) (st : (M × C → Option K) × Bool) :
    (M × C) ⊕ C → PMF ((K ⊕ Option K) × ((M × C → Option K) × Bool))
  | .inl d => if d = kpt then PMF.pure (.inl v, (st.1, true)) else
      (roOracle st.1 d).map fun x => (.inl x.1, (x.2, st.2))
  | .inr c => if c = kpt.2 then PMF.pure (.inr none, st) else
      (roOracle st.1 (decIdx P sk s c)).map fun x => (.inr (some x.1), (x.2, st.2))

/-- The distribution of the flagged run; `swap` selects the candidate key stored
at the challenge point. -/
noncomputable def flagDist {qH qD : ℕ} (B : ROMINDCCAAdversary PK K C (M × C) K qH qD)
    (swap : Bool) : PMF (Bool × ((M × C → Option K) × Bool)) :=
  (setup P).bind fun x => OracleAdv.run
    (oFlag P x.sk x.s (x.m, x.c P) (if swap then x.k₁ else x.k₀)) (B.run x.pk (x.c P) x.k₀)
    (emptyTable, false)

omit [Fintype M] [Nonempty M] [DecidableEq M] [DecidableEq C] in
theorem roOracle_update_ne {D : Type} [DecidableEq D] (T : D → Option K) (d k : D) (w : K)
    (h : d ≠ k) :
    (roOracle T d).map (fun x => (x.1, Function.update x.2 k (some w))) =
      roOracle (Function.update T k (some w)) d := by
  unfold roOracle
  rw [Function.update_of_ne h]
  cases T d with
  | some v => simp [PMF.pure_map]
  | none =>
    simp only [PMF.map_comp, Function.comp_def]
    congr 1; funext v
    rw [Function.update_comm h]

/-- Storing `v` at the challenge point commutes with each transition of the flagged
oracle and the oracle of the experiment. -/
theorem oFlag_map (sk : SK) (s : M) (m : M) (c : C) (v : K)
    (st : (M × C → Option K) × Bool) (d : (M × C) ⊕ C) :
    (oFlag P sk s (m, c) v st d).map (Prod.map id fun y => Function.update y.1 (m, c) (some v)) =
      romCCAOracle (uNotBot P) (sk, s) c (Function.update st.1 (m, c) (some v)) d := by
  cases d with
  | inl d =>
    by_cases hd : d = (m, c)
    · subst hd
      simp [oFlag, romCCAOracle, roOracle, PMF.pure_map]
    · simp only [oFlag, romCCAOracle, hd, if_false, PMF.map_comp]
      rw [← roOracle_update_ne _ _ _ _ hd, PMF.map_comp]
      rfl
  | inr c' =>
    by_cases hc : c' = c
    · subst hc
      simp [oFlag, romCCAOracle, PMF.pure_map]
    · have hne : decIdx P sk s c' ≠ (m, c) := fun h => hc (congrArg Prod.snd h)
      simp only [oFlag, romCCAOracle, hc, if_false, PMF.map_comp, uNotBot, OracleAdv.run_query,
        OracleAdv.run_ret]
      rw [← roOracle_update_ne _ _ _ _ hne]
      rw [show (fun x : K × (M × C → Option K) => PMF.pure (some x.1, x.2)) =
        PMF.pure ∘ (fun x => (some x.1, x.2)) from rfl, PMF.bind_pure_comp, PMF.map_comp,
        PMF.map_comp]
      rfl

/-- A run of the experiment's oracle from the table holding only `v` at the
challenge point is the flagged run with the flag and the table forgotten. -/
theorem run_romCCAOracle_eq {α : Type} (sk : SK) (s m : M) (c : C) (v : K)
    (A : OracleAdv ((M × C) ⊕ C) (K ⊕ Option K) α) :
    (OracleAdv.run (romCCAOracle (uNotBot P) (sk, s) c) A
      (Function.update emptyTable (m, c) (some v))).map Prod.fst =
    (OracleAdv.run (oFlag P sk s (m, c) v) A (emptyTable, false)).map Prod.fst := by
  have h := OracleAdv.run_map_state (oFlag P sk s (m, c) v) (romCCAOracle (uNotBot P) (sk, s) c)
    (fun y => Function.update y.1 (m, c) (some v)) (fun st d => oFlag_map P sk s m c v st d) A
    (emptyTable, false)
  rw [← h, PMF.map_comp]
  rfl

theorem romINDCCAGame_uNotBot {qH qD : ℕ} (B : ROMINDCCAAdversary PK K C (M × C) K qH qD)
    (b : Bool) :
    romINDCCAGame (uNotBot P) B b = (setup P).bind fun x =>
      (OracleAdv.run (oFlag P x.sk x.s (x.m, x.c P) x.k₀)
        (B.run x.pk (x.c P) (if b then x.k₀ else x.k₁)) (emptyTable, false)).map Prod.fst := by
  simp only [romINDCCAGame, setup, uNotBot, PMF.bind_bind, PMF.bind_map, Function.comp_def,
    OracleAdv.run_rand, OracleAdv.run_query, OracleAdv.run_ret]
  refine congrArg _ (funext fun ks => congrArg _ (funext fun s => congrArg _ (funext fun m =>
    congrArg _ (funext fun r => ?_))))
  simp only [roOracle, emptyTable, PMF.bind_map, Function.comp_def, PMF.pure_bind]
  refine congrArg _ (funext fun k₀ => ?_)
  simp only [PMF.map, Function.comp_def]
  refine congrArg _ (funext fun k₁ => ?_)
  exact run_romCCAOracle_eq P ks.2 s m _ k₀ _

omit [Fintype R] [Nonempty R] [Fintype M] [Nonempty M] in
theorem oFlag_apply_true_false (sk : SK) (s : M) (kpt : M × C) (v : K) (T : M × C → Option K)
    (d : (M × C) ⊕ C) (a : K ⊕ Option K) (T' : M × C → Option K) :
    oFlag P sk s kpt v (T, true) d (a, (T', false)) = 0 := by
  cases d with
  | inl d =>
    simp only [oFlag]
    split_ifs
    · simp [PMF.pure_apply]
    · rw [PMF.map_apply]; simp
  | inr c =>
    simp only [oFlag]
    split_ifs
    · simp [PMF.pure_apply]
    · rw [PMF.map_apply]; simp

omit [Fintype R] [Nonempty R] [Fintype M] [Nonempty M] in
theorem oFlag_apply_false_eq (sk : SK) (s : M) (kpt : M × C) (v v' : K)
    (st : (M × C → Option K) × Bool) (d : (M × C) ⊕ C) (a : K ⊕ Option K)
    (T' : M × C → Option K) :
    oFlag P sk s kpt v st d (a, (T', false)) = oFlag P sk s kpt v' st d (a, (T', false)) := by
  cases d with
  | inl d =>
    simp only [oFlag]
    split_ifs
    · simp [PMF.pure_apply]
    · rfl
  | inr c => rfl

/-- **Challenge hop.** The IND-CCA advantage against `uNotBot P` is at most the
probability that the adversary queries the random oracle at the challenge point. -/
theorem romINDCCAAdvantage_le_flag {qH qD : ℕ} (B : ROMINDCCAAdversary PK K C (M × C) K qH qD) :
    romINDCCAAdvantage (uNotBot P) B ≤ (flagDist P B false).toOuterMeasure {x | x.2.2 = true} := by
  have h₁ : romINDCCAGame (uNotBot P) B true = (flagDist P B false).map Prod.fst := by
    rw [romINDCCAGame_uNotBot, flagDist, PMF.map_bind]
    rfl
  have h₂ : romINDCCAGame (uNotBot P) B false = (flagDist P B true).map Prod.fst := by
    rw [romINDCCAGame_uNotBot, flagDist, PMF.map_bind]
    conv_lhs => rw [← setup_map_swap P, PMF.bind_map]
    rfl
  have h : ∀ a t, flagDist P B false (a, (t, false)) = flagDist P B true (a, (t, false)) := by
    intro a t
    simp only [flagDist, PMF.bind_apply]
    refine tsum_congr fun x => congrArg _ ?_
    grind [OracleAdv.run_apply_flag_false_eq, oFlag_apply_true_false, oFlag_apply_false_eq]
  unfold romINDCCAAdvantage
  rw [h₁, h₂]
  simp only [Advantage, prTrue_liftPMF_map]
  refine max_le (tsub_le_iff_left.mpr ?_) (tsub_le_iff_left.mpr ?_)
  · rw [toOuterMeasure_flag_eq _ _ h]
    simpa only [Set.mem_singleton_iff] using toOuterMeasure_le_add_flag _ _ h {true}
  · simpa only [Set.mem_singleton_iff] using
      toOuterMeasure_le_add_flag _ _ (fun a t => (h a t).symm) {true}

end ChallengeHop

/-! ## The re-indexed oracle -/

section Reindex

variable {G : Type}

/-- Answer from the table indexed by `c` with ghost state `g`. -/
noncomputable def lazyD {A : Type} (st : SimState M C K) (c : C) (w : K → A) (g : G) :
    PMF (A × (SimState M C K × G)) :=
  match st.LD c with
  | some k => PMF.pure (w k, (st, g))
  | none => (PMF.uniformOfFintype K).map fun k =>
      (w k, ({ st with LD := Function.update st.LD c (some k) }, g))

/-- Answer from the table indexed by `(m, c)` with ghost state `g`. -/
noncomputable def lazyQ {A : Type} (st : SimState M C K) (q : M × C) (w : K → A) (g : G) :
    PMF (A × (SimState M C K × G)) :=
  match st.LQ q with
  | some k => PMF.pure (w k, (st, g))
  | none => (PMF.uniformOfFintype K).map fun k =>
      (w k, ({ st with LQ := Function.update st.LQ q (some k) }, g))

/-- The re-indexed oracle with selector `sel`, challenge `c*` and key `v`: a
random-oracle query `q` with `sel q` is answered from the table indexed by `q.2`
(and by `v`, recording `q.1` as found, when `q.2 = c*`), any other query from the
table indexed by `q`; a decapsulation query is answered from the table indexed by
the ciphertext. Each random-oracle query updates the ghost state with `upd q.1`. -/
noncomputable def oTwo (upd : M → G → G) (sel : M × C → Bool) (cstar : C) (v : K)
    (x : SimState M C K × G) : (M × C) ⊕ C → PMF ((K ⊕ Option K) × (SimState M C K × G))
  | .inl q =>
    if sel q then
      (if q.2 = cstar then PMF.pure (.inl v, ({ x.1 with found := some q.1 }, upd q.1 x.2))
       else lazyD x.1 q.2 Sum.inl (upd q.1 x.2))
    else lazyQ x.1 q Sum.inl (upd q.1 x.2)
  | .inr c => if c = cstar then PMF.pure (.inr none, x) else
      lazyD x.1 c (fun k => .inr (some k)) x.2

omit [Fintype M] [Nonempty M] [DecidableEq M] in
theorem lazyD_map_ghost {G' A : Type} (f : G → G') (st : SimState M C K) (c : C) (w : K → A)
    (g : G) : (lazyD st c w g).map (Prod.map id (Prod.map id f)) = lazyD st c w (f g) := by
  unfold lazyD; split <;> simp [PMF.pure_map, PMF.map_comp, Function.comp_def]

omit [Fintype M] [Nonempty M] in
theorem lazyQ_map_ghost {G' A : Type} (f : G → G') (st : SimState M C K) (q : M × C) (w : K → A)
    (g : G) : (lazyQ st q w g).map (Prod.map id (Prod.map id f)) = lazyQ st q w (f g) := by
  unfold lazyQ; split <;> simp [PMF.pure_map, PMF.map_comp, Function.comp_def]

omit [Fintype M] [Nonempty M] in
/-- A map of ghost states that commutes with the ghost updates commutes with the
re-indexed oracle. -/
theorem oTwo_map_ghost {G' : Type} (upd : M → G → G) (upd' : M → G' → G') (f : G → G')
    (hf : ∀ m g, f (upd m g) = upd' m (f g)) (sel : M × C → Bool) (cstar : C) (v : K)
    (x : SimState M C K × G) (d : (M × C) ⊕ C) :
    (oTwo upd sel cstar v x d).map (Prod.map id (Prod.map id f)) =
      oTwo upd' sel cstar v (x.1, f x.2) d := by
  cases d with
  | inl q =>
    simp only [oTwo]
    split_ifs <;> simp [PMF.pure_map, lazyD_map_ghost, lazyQ_map_ghost, hf]
  | inr c =>
    simp only [oTwo]
    split_ifs
    · simp only [PMF.pure_map]; rfl
    · simp [lazyD_map_ghost]

variable (P : Scheme PK SK M C R)

/-- The random-oracle table represented by a simulation state: the point `(m, c)` is
read from the table indexed by `c` when `m` is `Dec(sk, c)` (or `s` when decryption
rejects), and from the table indexed by `(m, c)` otherwise. -/
def table (sk : SK) (s : M) (st : SimState M C K) : M × C → Option K :=
  fun q => if (P.dec sk q.2).getD s = q.1 then st.LD q.2 else st.LQ q

/-- The selector of `table`. -/
def selIdx (sk : SK) (s : M) (q : M × C) : Bool := decide ((P.dec sk q.2).getD s = q.1)

omit [Fintype R] [Nonempty R] [Fintype M] [Nonempty M] [Fintype K] [Nonempty K] in
theorem table_updateLD (sk : SK) (s : M) (st : SimState M C K) (c : C) (k : K) :
    table P sk s { st with LD := Function.update st.LD c (some k) } =
      Function.update (table P sk s st) (decIdx P sk s c) (some k) := by
  funext q
  obtain ⟨m, c'⟩ := q
  simp only [table, decIdx, Function.update_apply, Prod.mk.injEq]
  by_cases hc : c' = c
  · subst hc
    by_cases hm : (P.dec sk c').getD s = m
    · simp [hm]
    · simpa [hm] using fun h => absurd h.symm hm
  · simp [hc]

omit [Fintype R] [Nonempty R] [Fintype M] [Nonempty M] [Fintype K] [Nonempty K] in
theorem table_updateLQ (sk : SK) (s : M) (st : SimState M C K) (q : M × C) (k : K)
    (hq : (P.dec sk q.2).getD s ≠ q.1) :
    table P sk s { st with LQ := Function.update st.LQ q (some k) } =
      Function.update (table P sk s st) q (some k) := by
  funext q'
  simp only [table, Function.update_apply]
  by_cases h : q' = q
  · subst h; simp [hq]
  · simp [h]

omit [Fintype R] [Nonempty R] [Fintype M] [Nonempty M] in
/-- Forgetting the ghost state and reading the table maps the re-indexed oracle with
selector `selIdx` to the flagged oracle, when `c*` decrypts to `m*`. -/
theorem oTwo_map_table (sk : SK) (s mstar : M) (cstar : C) (v : K)
    (hdec : P.dec sk cstar = some mstar) {G : Type} (upd : M → G → G)
    (x : SimState M C K × G) (d : (M × C) ⊕ C) :
    (oTwo upd (selIdx P sk s) cstar v x d).map
        (Prod.map id fun y => (table P sk s y.1, y.1.found.isSome)) =
      oFlag P sk s (mstar, cstar) v (table P sk s x.1, x.1.found.isSome) d := by
  obtain ⟨st, g⟩ := x
  cases d with
  | inl q =>
    obtain ⟨m, c⟩ := q
    by_cases hsel : (P.dec sk c).getD s = m
    · by_cases hc : c = cstar
      · subst hc
        rw [hdec, Option.getD_some] at hsel
        subst hsel
        simp [oTwo, oFlag, selIdx, hdec, PMF.pure_map]
        rfl
      · have hq : (m, c) ≠ (mstar, cstar) := fun h => hc (congrArg Prod.snd h)
        have ht : table P sk s st (m, c) = st.LD c := by simp [table, hsel]
        simp only [oTwo, oFlag, selIdx, hsel, decide_true, if_true, hc, if_false, hq]
        unfold lazyD roOracle
        rw [ht]
        cases st.LD c with
        | some k => simp [PMF.pure_map]
        | none =>
          simp only [PMF.map_comp, Function.comp_def, Prod.map_apply, id]
          congr 1; funext k
          have := table_updateLD P sk s st c k
          simp only [decIdx, hsel] at this
          simp [this]
    · have hq : (m, c) ≠ (mstar, cstar) := by
        rintro ⟨rfl, rfl⟩; exact hsel (by rw [hdec, Option.getD_some])
      have ht : table P sk s st (m, c) = st.LQ (m, c) := by simp [table, hsel]
      simp only [oTwo, oFlag, selIdx, hsel, decide_false, Bool.false_eq_true, if_false, hq]
      unfold lazyQ roOracle
      rw [ht]
      cases st.LQ (m, c) with
      | some k => simp [PMF.pure_map]
      | none =>
        simp only [PMF.map_comp, Function.comp_def, Prod.map_apply, id]
        congr 1; funext k
        simp [table_updateLQ P sk s st (m, c) k hsel]
  | inr c =>
    by_cases hc : c = cstar
    · subst hc; simp [oTwo, oFlag, PMF.pure_map]
    · have ht : table P sk s st (decIdx P sk s c) = st.LD c := by simp [table, decIdx]
      simp only [oTwo, oFlag, hc, if_false]
      unfold lazyD roOracle
      rw [ht]
      cases st.LD c with
      | some k => simp [PMF.pure_map]
      | none =>
        simp only [PMF.map_comp, Function.comp_def, Prod.map_apply, id]
        congr 1; funext k
        simp [table_updateLD P sk s st c k]

end Reindex

/-! ## Replacing the selector by the plaintext-checking predicate -/

section Selector

/-- The ghost update recording whether a random-oracle query at `s` was made. -/
def badUpd (s : M) (m : M) (b : Bool) : Bool := b || decide (m = s)

/-- The plaintext-checking selector. -/
def selPco (P : Scheme PK SK M C R) (sk : SK) (q : M × C) : Bool := P.pco sk q.1 q.2

omit [Fintype R] [Nonempty R] [Fintype M] [Nonempty M] [DecidableEq C] in
theorem selIdx_eq_selPco (P : Scheme PK SK M C R) (sk : SK) (s : M) (q : M × C) (hq : q.1 ≠ s) :
    selIdx P sk s q = selPco P sk q := by
  obtain ⟨m, c⟩ := q
  simp only [selIdx, selPco, Scheme.pco]
  cases h : P.dec sk c with
  | some m' => simp [eq_comm]
  | none => simp [Ne.symm hq]

omit [Fintype M] [Nonempty M] [DecidableEq M] in
theorem lazyD_apply_ghost_ne {G A : Type} (st : SimState M C K) (c : C) (w : K → A) (g : G)
    (a : A) (st' : SimState M C K) (g' : G) (h : g ≠ g') : lazyD st c w g (a, (st', g')) = 0 := by
  unfold lazyD; split
  · simp [PMF.pure_apply, Ne.symm h]
  · rw [PMF.map_apply]; simp [Ne.symm h]

omit [Fintype M] [Nonempty M] in
theorem lazyQ_apply_ghost_ne {G A : Type} (st : SimState M C K) (q : M × C) (w : K → A) (g : G)
    (a : A) (st' : SimState M C K) (g' : G) (h : g ≠ g') : lazyQ st q w g (a, (st', g')) = 0 := by
  unfold lazyQ; split
  · simp [PMF.pure_apply, Ne.symm h]
  · rw [PMF.map_apply]; simp [Ne.symm h]

omit [Fintype M] [Nonempty M] in
theorem oTwo_bad_apply_true_false (s : M) (sel : M × C → Bool) (cstar : C) (v : K)
    (st : SimState M C K) (d : (M × C) ⊕ C) (a : K ⊕ Option K) (st' : SimState M C K) :
    oTwo (badUpd s) sel cstar v (st, true) d (a, (st', false)) = 0 := by
  cases d with
  | inl q =>
    simp only [oTwo, badUpd, Bool.true_or]
    split_ifs
    · simp [PMF.pure_apply]
    · exact lazyD_apply_ghost_ne _ _ _ _ _ _ _ (by decide)
    · exact lazyQ_apply_ghost_ne _ _ _ _ _ _ _ (by decide)
  | inr c =>
    simp only [oTwo]
    split_ifs
    · simp [PMF.pure_apply]
    · exact lazyD_apply_ghost_ne _ _ _ _ _ _ _ (by decide)

omit [Fintype M] [Nonempty M] in
theorem oTwo_bad_apply_false_eq (s : M) (sel sel' : M × C → Bool)
    (hsel : ∀ q : M × C, q.1 ≠ s → sel q = sel' q) (cstar : C) (v : K)
    (x : SimState M C K × Bool) (d : (M × C) ⊕ C) (a : K ⊕ Option K) (st' : SimState M C K) :
    oTwo (badUpd s) sel cstar v x d (a, (st', false)) =
      oTwo (badUpd s) sel' cstar v x d (a, (st', false)) := by
  cases d with
  | inl q =>
    by_cases hq : q.1 = s
    · have hb : badUpd s q.1 x.2 = true := by simp [badUpd, hq]
      have hz : ∀ sel₀ : M × C → Bool,
          oTwo (badUpd s) sel₀ cstar v x (.inl q) (a, (st', false)) = 0 := by
        intro sel₀
        simp only [oTwo, hb]
        split_ifs
        · simp [PMF.pure_apply]
        · exact lazyD_apply_ghost_ne _ _ _ _ _ _ _ (by decide)
        · exact lazyQ_apply_ghost_ne _ _ _ _ _ _ _ (by decide)
      rw [hz, hz]
    · simp only [oTwo, hsel q hq]
  | inr c => rfl

omit [Fintype R] [Nonempty R] [Fintype M] [Nonempty M] [DecidableEq M] [DecidableEq C]
  [Fintype K] [Nonempty K] in
/-- **Identical until bad, on events.** For distributions that agree on every
outcome with the flag cleared, the probability of any event under the first is at
most its probability under the second plus the flag probability. -/
theorem toOuterMeasure_le_add_flag_set {α σ : Type} (p₁ p₂ : PMF (α × (σ × Bool)))
    (h : ∀ a t, p₁ (a, (t, false)) = p₂ (a, (t, false))) (S : Set (α × (σ × Bool))) :
    p₁.toOuterMeasure S ≤ p₂.toOuterMeasure S + p₂.toOuterMeasure {x | x.2.2 = true} := by
  refine (MeasureTheory.measure_le_inter_add_sdiff p₁.toOuterMeasure S
    {x | x.2.2 = false}).trans (add_le_add ?_ ?_)
  · rw [toOuterMeasure_eq_of_subset_false p₁ p₂ h _ fun x hx => hx.2]
    exact MeasureTheory.measure_mono Set.inter_subset_left
  · rw [← toOuterMeasure_flag_eq p₁ p₂ h]
    refine MeasureTheory.measure_mono fun x hx => ?_
    simpa using hx.2

end Selector

/-! ## Queries at the rejection seed -/

section Seed

/-- The query cost counting random-oracle queries. -/
def costH : (M × C) ⊕ C → ℕ := Sum.elim (fun _ => 1) fun _ => 0

omit [Fintype M] [Nonempty M] [DecidableEq M] in
theorem mem_support_lazyD_ghost {G A : Type} {st : SimState M C K} {c : C} {w : K → A} {g : G}
    {x : A × (SimState M C K × G)} (hx : x ∈ (lazyD st c w g).support) : x.2.2 = g := by
  by_contra h
  obtain ⟨a, st', g'⟩ := x
  exact (PMF.mem_support_iff _ _).mp hx (lazyD_apply_ghost_ne _ _ _ _ _ _ _ (Ne.symm h))

omit [Fintype M] [Nonempty M] in
theorem mem_support_lazyQ_ghost {G A : Type} {st : SimState M C K} {q : M × C} {w : K → A}
    {g : G} {x : A × (SimState M C K × G)} (hx : x ∈ (lazyQ st q w g).support) : x.2.2 = g := by
  by_contra h
  obtain ⟨a, st', g'⟩ := x
  exact (PMF.mem_support_iff _ _).mp hx (lazyQ_apply_ghost_ne _ _ _ _ _ _ _ (Ne.symm h))

omit [Fintype M] [Nonempty M] in
theorem mem_support_oTwo_log {sel : M × C → Bool} {cstar : C} {v : K} {st : SimState M C K}
    {l : List M} {d : (M × C) ⊕ C} {x : (K ⊕ Option K) × (SimState M C K × List M)}
    (hx : x ∈ (oTwo List.cons sel cstar v (st, l) d).support) :
    x.2.2.length = l.length + costH d := by
  cases d with
  | inl q =>
    simp only [oTwo] at hx
    split_ifs at hx
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at hx; subst hx; simp [costH]
    · simp [mem_support_lazyD_ghost hx, costH]
    · simp [mem_support_lazyQ_ghost hx, costH]
  | inr c =>
    simp only [oTwo] at hx
    split_ifs at hx
    · simp only [PMF.support_pure, Set.mem_singleton_iff] at hx; subst hx; simp [costH]
    · simp [mem_support_lazyD_ghost hx, costH]

omit [Fintype M] [Nonempty M] in
/-- On every outcome of a run with random-oracle query cost at most `n`, the log
grows by at most `n`. -/
theorem length_log_le_of_mem_support {α : Type} (sel : M × C → Bool) (cstar : C) (v : K)
    (A : OracleAdv ((M × C) ⊕ C) (K ⊕ Option K) α) (n : ℕ) (hA : A.IsQueryBoundBy costH n)
    (st : SimState M C K) (l : List M) (y : α × (SimState M C K × List M))
    (hy : y ∈ (OracleAdv.run (oTwo List.cons sel cstar v) A (st, l)).support) :
    y.2.2.length ≤ l.length + n := by
  induction A generalizing n st l with
  | ret a =>
    simp only [OracleAdv.run_ret, PMF.support_pure, Set.mem_singleton_iff] at hy
    subst hy; simp
  | rand p k ih =>
    simp only [OracleAdv.run_rand, PMF.support_bind, Set.mem_iUnion] at hy
    obtain ⟨b, _, hy⟩ := hy
    exact ih b n (hA b) st l hy
  | query d k ih =>
    simp only [OracleAdv.run_query, PMF.support_bind, Set.mem_iUnion] at hy
    obtain ⟨x, hx, hy⟩ := hy
    obtain ⟨hle, hk⟩ := hA
    have h1 := ih x.1 (n - costH d) (hk x.1) x.2.1 x.2.2 hy
    have h2 := mem_support_oTwo_log hx
    omega

omit [Fintype M] [Nonempty M] in
/-- The bad-flag run is the log run with the flag read as membership of `s`. -/
theorem run_oTwo_bad_eq {α : Type} (s : M) (sel : M × C → Bool) (cstar : C) (v : K)
    (A : OracleAdv ((M × C) ⊕ C) (K ⊕ Option K) α) (st : SimState M C K) :
    OracleAdv.run (oTwo (badUpd s) sel cstar v) A (st, false) =
      (OracleAdv.run (oTwo List.cons sel cstar v) A (st, [])).map
        (Prod.map id (Prod.map id fun l => decide (s ∈ l))) := by
  have h := OracleAdv.run_map_state (oTwo List.cons sel cstar v) (oTwo (badUpd s) sel cstar v)
    (Prod.map id fun l => decide (s ∈ l))
    (fun x d => oTwo_map_ghost List.cons (badUpd s) _
      (fun m l => by simp [badUpd, List.mem_cons, eq_comm, Bool.or_comm]) sel cstar v x d) A (st, [])
  simpa using h.symm

/-- **Guessing the rejection seed.** Averaged over a uniform seed `s`, a run with at
most `n` random-oracle queries queries the oracle at `s` with probability at most
`n / |M|`. -/
theorem tsum_bad_le (sel : M × C → Bool) (cstar : C) (v : K)
    {α : Type} (A : OracleAdv ((M × C) ⊕ C) (K ⊕ Option K) α) (n : ℕ)
    (hA : A.IsQueryBoundBy costH n) :
    ∑' s, PMF.uniformOfFintype M s *
      (OracleAdv.run (oTwo (badUpd s) sel cstar v) A (SimState.init, false)).toOuterMeasure
        {y | y.2.2 = true} ≤ (n : ℝ≥0∞) / Fintype.card M := by
  classical
  set p := OracleAdv.run (oTwo List.cons sel cstar v) A (SimState.init, [])
  have hs : ∀ s, (OracleAdv.run (oTwo (badUpd s) sel cstar v) A (SimState.init, false)).toOuterMeasure
      {y | y.2.2 = true} = ∑' y, p y * (if s ∈ y.2.2 then 1 else 0) := by
    intro s
    rw [run_oTwo_bad_eq, PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply]
    refine tsum_congr fun y => ?_
    by_cases h : s ∈ y.2.2 <;> simp [Set.indicator, h, p]
  simp_rw [hs, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  calc ∑' y, ∑' s, PMF.uniformOfFintype M s * (p y * (if s ∈ y.2.2 then 1 else 0))
      ≤ ∑' y, p y * ((n : ℝ≥0∞) / Fintype.card M) := by
        refine ENNReal.tsum_le_tsum fun y => ?_
        by_cases hy : p y = 0
        · simp [hy]
        have hlen : y.2.2.length ≤ n := by
          simpa [SimState.init] using length_log_le_of_mem_support sel cstar v A n hA
            SimState.init [] y ((PMF.mem_support_iff _ _).mpr hy)
        have hcard : ∑' s, PMF.uniformOfFintype M s * (if s ∈ y.2.2 then 1 else 0) ≤
            (n : ℝ≥0∞) / Fintype.card M := by
          rw [tsum_fintype]
          simp only [PMF.uniformOfFintype_apply, mul_ite, mul_one, mul_zero]
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
            ENNReal.div_eq_inv_mul, mul_comm]
          gcongr
          exact (Finset.card_le_card fun s hs => by simpa using hs).trans
            ((List.toFinset_card_le _).trans hlen)
        calc ∑' s, PMF.uniformOfFintype M s * (p y * (if s ∈ y.2.2 then 1 else 0))
            = p y * ∑' s, PMF.uniformOfFintype M s * (if s ∈ y.2.2 then 1 else 0) := by
              rw [← ENNReal.tsum_mul_left]; exact tsum_congr fun s => by ring
          _ ≤ _ := by gcongr
    _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

end Seed

/-! ## The simulation -/

section Simulation

variable (P : Scheme PK SK M C R)

omit [Fintype R] [Nonempty R] [Fintype M] [Nonempty M] in
theorem run_lazyDProg {A : Type} (sk : SK) (st : SimState M C K) (c : C) (w : K → A) :
    (OracleAdv.run (pcoOracle P sk) (lazyDProg st c w) ()).map
      (fun x => (x.1.1, (x.1.2, x.2))) = lazyD st c w () := by
  unfold lazyDProg lazyD
  split <;> simp [PMF.pure_map, PMF.map_bind]; rfl

omit [Fintype R] [Nonempty R] [Fintype M] [Nonempty M] in
theorem run_lazyQProg {A : Type} (sk : SK) (st : SimState M C K) (q : M × C) (w : K → A) :
    (OracleAdv.run (pcoOracle P sk) (lazyQProg st q w) ()).map
      (fun x => (x.1.1, (x.1.2, x.2))) = lazyQ st q w () := by
  unfold lazyQProg lazyQ
  split <;> simp [PMF.pure_map, PMF.map_bind]; rfl

omit [Fintype R] [Nonempty R] [Fintype M] [Nonempty M] in
/-- The composite oracle of the reduction is the re-indexed oracle with the
plaintext-checking selector. -/
theorem simOracle_eq_oTwo (sk : SK) (cstar : C) (v : K) (x : SimState M C K × Unit)
    (d : (M × C) ⊕ C) :
    OracleAdv.simOracle (simImpl cstar v) (pcoOracle P sk) x d =
      oTwo (fun _ _ => ()) (selPco P sk) cstar v x d := by
  obtain ⟨st, u⟩ := x
  cases d with
  | inl q =>
    simp only [OracleAdv.simOracle, simImpl, oTwo, OracleAdv.run_query, pcoOracle, PMF.pure_bind,
      selPco]
    split_ifs
    · simp [PMF.pure_map]
    · exact run_lazyDProg P sk st q.2 Sum.inl
    · exact run_lazyQProg P sk st q Sum.inl
  | inr c =>
    simp only [OracleAdv.simOracle, simImpl, oTwo]
    split_ifs
    · simp [PMF.pure_map]
    · exact run_lazyDProg P sk st c _

omit [Fintype M] [Nonempty M] [DecidableEq M] in
theorem found_of_mem_support_lazyD {G A : Type} {st : SimState M C K} {c : C} {w : K → A}
    {g : G} {x : A × (SimState M C K × G)} (hx : x ∈ (lazyD st c w g).support) :
    x.2.1.found = st.found := by
  unfold lazyD at hx; split at hx
  · simp only [PMF.support_pure, Set.mem_singleton_iff] at hx; subst hx; rfl
  · simp only [PMF.support_map, Set.mem_image] at hx
    obtain ⟨k, _, rfl⟩ := hx; rfl

omit [Fintype M] [Nonempty M] in
theorem found_of_mem_support_lazyQ {G A : Type} {st : SimState M C K} {q : M × C} {w : K → A}
    {g : G} {x : A × (SimState M C K × G)} (hx : x ∈ (lazyQ st q w g).support) :
    x.2.1.found = st.found := by
  unfold lazyQ at hx; split at hx
  · simp only [PMF.support_pure, Set.mem_singleton_iff] at hx; subst hx; rfl
  · simp only [PMF.support_map, Set.mem_image] at hx
    obtain ⟨k, _, rfl⟩ := hx; rfl

/-- A found message decrypts the challenge. -/
def FoundValid (sk : SK) (cstar : C) (st : SimState M C K) : Prop :=
  ∀ m, st.found = some m → P.pco sk m cstar = true

omit [Fintype R] [Nonempty R] [Fintype M] [Nonempty M] in
/-- On every outcome of a run of the re-indexed oracle with the plaintext-checking
selector from the initial state, a found message decrypts the challenge. -/
theorem foundValid_of_mem_support {G α : Type} (upd : M → G → G) (sk : SK) (cstar : C) (v : K)
    (A : OracleAdv ((M × C) ⊕ C) (K ⊕ Option K) α) (g : G)
    (y : α × (SimState M C K × G))
    (hy : y ∈ (OracleAdv.run (oTwo upd (selPco P sk) cstar v) A (SimState.init, g)).support) :
    FoundValid P sk cstar y.2.1 := by
  have h := run_support_rel (oTwo upd (selPco P sk) cstar v)
    (fun a b => FoundValid P sk cstar a.1 → FoundValid P sk cstar b.1) (fun _ h => h)
    (fun _ _ _ h₁ h₂ h => h₂ (h₁ h)) ?_ A (SimState.init, g) y hy
  · exact h fun m hm => by simp [SimState.init] at hm
  · intro x d z hz hx
    cases d with
    | inl q =>
      simp only [oTwo] at hz
      split_ifs at hz with hsel hc
      · simp only [PMF.support_pure, Set.mem_singleton_iff] at hz
        subst hz
        intro m hm
        simp only [Option.some.injEq] at hm
        subst hm
        simpa [selPco, hc] using hsel
      · intro m hm; rw [found_of_mem_support_lazyD hz] at hm; exact hx m hm
      · intro m hm; rw [found_of_mem_support_lazyQ hz] at hm; exact hx m hm
    | inr c =>
      simp only [oTwo] at hz
      split_ifs at hz
      · simp only [PMF.support_pure, Set.mem_singleton_iff] at hz; subst hz; exact hx
      · intro m hm; rw [found_of_mem_support_lazyD hz] at hm; exact hx m hm

/-- The indicator of a decryption failure: `0` when `Dec(sk, c) = m`, `1` otherwise. -/
noncomputable def failInd (sk : SK) (m : M) (c : C) : ℝ≥0∞ :=
  if P.dec sk c = some m then 0 else 1

omit [Fintype R] [Nonempty R] [Fintype M] [Nonempty M] [DecidableEq C] [Fintype K] [Nonempty K] in
theorem table_init (sk : SK) (s : M) :
    table P sk s (SimState.init : SimState M C K) = emptyTable := by
  funext q; simp [table, SimState.init, emptyTable]

omit [Fintype R] [Nonempty R] [Fintype M] in
/-- **Per-draw bound.** For a fixed draw, the probability that the flagged run hits
the challenge point is at most the indicator of a decryption failure of the
challenge, plus the probability that the simulation finds a message decrypting the
challenge, plus the probability that the adversary queries the random oracle at
the rejection seed. -/
theorem flag_le (sk : SK) (s m : M) (c : C) (v : K)
    (A : OracleAdv ((M × C) ⊕ C) (K ⊕ Option K) Bool) :
    (OracleAdv.run (oFlag P sk s (m, c) v) A (emptyTable, false)).toOuterMeasure
        {y | y.2.2 = true} ≤
      failInd P sk m c +
      (OracleAdv.run (OracleAdv.simOracle (simImpl c v) (pcoOracle P sk)) A
        (SimState.init, ())).toOuterMeasure
          {y | P.pco sk (y.2.1.found.getD (Classical.arbitrary M)) c = true} +
      (OracleAdv.run (oTwo (badUpd s) (selPco P sk) c v) A (SimState.init, false)).toOuterMeasure
        {y | y.2.2 = true} := by
  by_cases hdec : P.dec sk c = some m
  swap
  · simp only [failInd, hdec, if_false]
    exact (le_self_add.trans_eq (toOuterMeasure_add_compl _ _)).trans (le_add_right le_self_add)
  simp only [failInd, hdec, if_true, zero_add]
  -- re-indexing
  have h1 : (OracleAdv.run (oFlag P sk s (m, c) v) A (emptyTable, false)).toOuterMeasure
      {y | y.2.2 = true} =
      (OracleAdv.run (oTwo (badUpd s) (selIdx P sk s) c v) A (SimState.init, false)).toOuterMeasure
        {y | y.2.1.found.isSome = true} := by
    have h := OracleAdv.run_map_state (oTwo (badUpd s) (selIdx P sk s) c v)
      (oFlag P sk s (m, c) v) (fun y => (table P sk s y.1, y.1.found.isSome))
      (fun x d => oTwo_map_table P sk s m c v hdec (badUpd s) x d) A (SimState.init, false)
    simp only [table_init] at h
    rw [show ((SimState.init : SimState M C K).found.isSome) = false from rfl] at h
    rw [← h, PMF.toOuterMeasure_map_apply]
    rfl
  -- selector replacement
  have h2 := toOuterMeasure_le_add_flag_set
    (OracleAdv.run (oTwo (badUpd s) (selIdx P sk s) c v) A (SimState.init, false))
    (OracleAdv.run (oTwo (badUpd s) (selPco P sk) c v) A (SimState.init, false))
    (fun a t => OracleAdv.run_apply_flag_false_eq _ _ (oTwo_bad_apply_true_false s _ c v)
      (oTwo_bad_apply_true_false s _ c v)
      (fun x d r t' => oTwo_bad_apply_false_eq s _ _ (fun q hq => selIdx_eq_selPco P sk s q hq)
        c v x d r t') A _ a t)
    {y | y.2.1.found.isSome = true}
  -- dropping the ghost flag
  have h3 : (OracleAdv.run (oTwo (badUpd s) (selPco P sk) c v) A (SimState.init, false)).toOuterMeasure
      {y | y.2.1.found.isSome = true} =
      (OracleAdv.run (OracleAdv.simOracle (simImpl c v) (pcoOracle P sk)) A
        (SimState.init, ())).toOuterMeasure {y | y.2.1.found.isSome = true} := by
    have h := OracleAdv.run_map_state (oTwo (badUpd s) (selPco P sk) c v)
      (oTwo (fun _ _ => ()) (selPco P sk) c v) (Prod.map id fun _ => ())
      (fun x d => oTwo_map_ghost (badUpd s) (fun _ _ => ()) (fun _ => ()) (fun _ _ => rfl) _ c v x d)
      A (SimState.init, false)
    have hs : OracleAdv.simOracle (simImpl c v) (pcoOracle P sk) =
        oTwo (fun _ _ => ()) (selPco P sk) c v :=
      funext fun x => funext fun d => simOracle_eq_oTwo P sk c v x d
    rw [hs, show (SimState.init, ()) = Prod.map id (fun _ => ()) ((SimState.init : SimState M C K),
      false) from rfl, ← h, PMF.toOuterMeasure_map_apply]
    rfl
  -- a found message wins
  have h4 : (OracleAdv.run (OracleAdv.simOracle (simImpl c v) (pcoOracle P sk)) A
        (SimState.init, ())).toOuterMeasure {y | y.2.1.found.isSome = true} ≤
      (OracleAdv.run (OracleAdv.simOracle (simImpl c v) (pcoOracle P sk)) A
        (SimState.init, ())).toOuterMeasure
          {y | P.pco sk (y.2.1.found.getD (Classical.arbitrary M)) c = true} := by
    refine PMF.toOuterMeasure_mono _ fun y ⟨hy, hsupp⟩ => ?_
    have hs : OracleAdv.simOracle (simImpl c v) (pcoOracle P sk) =
        oTwo (fun _ _ => ()) (selPco P sk) c v :=
      funext fun x => funext fun d => simOracle_eq_oTwo P sk c v x d
    rw [hs] at hsupp
    have hv := foundValid_of_mem_support P (fun _ _ => ()) sk c v A () y hsupp
    simp only [Set.mem_ofPred_eq, Option.isSome_iff_exists] at hy ⊢
    obtain ⟨m', hm'⟩ := hy
    rw [hm', Option.getD_some]
    exact hv m' hm'
  rw [h1]
  calc _ ≤ _ := h2
    _ ≤ _ := by rw [h3]; gcongr

end Simulation

/-! ## Summing over the draws -/

section Summation

open PMF (tsum_bind_mul)

omit [Fintype R] [Nonempty R] [Fintype M] [Nonempty M] [DecidableEq M] [DecidableEq C]
  [Fintype K] [Nonempty K] in
theorem tsum_map_mul {α β : Type} (p : PMF α) (g : α → β) (F : β → ℝ≥0∞) :
    ∑' x, (p.map g) x * F x = ∑' a, p a * F (g a) := by
  rw [PMF.map, tsum_bind_mul]
  refine tsum_congr fun a => congrArg _ ?_
  simp only [Function.comp_apply, PMF.pure_apply, ite_mul, one_mul, zero_mul]
  rw [tsum_eq_single (g a) fun b hb => if_neg hb, if_pos rfl]

omit [Fintype R] [Nonempty R] [Fintype M] [Nonempty M] [DecidableEq M] [DecidableEq C]
  [Fintype K] [Nonempty K] in
theorem tsum_mul_const {α : Type} (p : PMF α) (c : ℝ≥0∞) : ∑' a, p a * c = c := by
  rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

omit [Fintype R] [Nonempty R] [Fintype M] [Nonempty M] [DecidableEq M] [DecidableEq C]
  [Fintype K] [Nonempty K] in
theorem tsum_mul_comm {α β : Type} (p : α → ℝ≥0∞) (q : β → ℝ≥0∞) (F : α → β → ℝ≥0∞) :
    ∑' a, p a * ∑' b, q b * F a b = ∑' b, q b * ∑' a, p a * F a b := by
  simp only [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  exact tsum_congr fun b => tsum_congr fun a => by ring

variable (P : Scheme PK SK M C R)

omit [DecidableEq M] [DecidableEq C] in
theorem tsum_setup_mul (F : Draw PK SK M R K → ℝ≥0∞) :
    ∑' x, setup P x * F x = ∑' ks, P.keygen ks * ∑' s, PMF.uniformOfFintype M s *
      ∑' m, PMF.uniformOfFintype M m * ∑' r, PMF.uniformOfFintype R r *
        ∑' k₀, PMF.uniformOfFintype K k₀ * ∑' k₁, PMF.uniformOfFintype K k₁ *
          F ⟨ks.1, ks.2, s, m, r, k₀, k₁⟩ := by
  simp only [setup, tsum_bind_mul, tsum_map_mul]

omit [Fintype R] [Nonempty R] [Fintype M] in
/-- The OW-PCA success probability of `uReduction B` for a fixed key pair and
challenge ciphertext. -/
theorem uReduction_prob {qH qD : ℕ} (B : ROMINDCCAAdversary PK K C (M × C) K qH qD) (pk : PK)
    (sk : SK) (c : C) :
    ((OracleAdv.run (pcoOracle P sk) ((uReduction B).run pk c) ()).map
      fun x => P.pco sk x.1 c).toOuterMeasure {b | b = true} =
    ∑' k, PMF.uniformOfFintype K k *
      (OracleAdv.run (OracleAdv.simOracle (simImpl c k) (pcoOracle P sk)) (B.run pk c k)
        (SimState.init, ())).toOuterMeasure
          {y | P.pco sk (y.2.1.found.getD (Classical.arbitrary M)) c = true} := by
  unfold uReduction
  dsimp only
  rw [OracleAdv.run_rand, PMF.map_bind, PMF.toOuterMeasure_bind_apply]
  refine tsum_congr fun k => congrArg _ ?_
  rw [OracleAdv.run_bind, OracleAdv.run_simulate, PMF.bind_map]
  simp only [OracleAdv.run_ret, Function.comp_def, PMF.map_bind, PMF.pure_map,
    PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_pure_apply]
  rw [PMF.toOuterMeasure_apply]
  refine tsum_congr fun y => ?_
  by_cases h : P.pco sk (y.2.1.found.getD (Classical.arbitrary M)) c = true <;>
    simp [Set.indicator, h]


theorem owpcaAdvantage_uReduction {qH qD : ℕ} (B : ROMINDCCAAdversary PK K C (M × C) K qH qD) :
    owpcaAdvantage P (uReduction B) =
      ∑' ks, P.keygen ks * ∑' m, PMF.uniformOfFintype M m * ∑' r, PMF.uniformOfFintype R r *
        ∑' k, PMF.uniformOfFintype K k *
          (OracleAdv.run (OracleAdv.simOracle (simImpl (P.enc ks.1 m r) k) (pcoOracle P ks.2))
            (B.run ks.1 (P.enc ks.1 m r) k) (SimState.init, ())).toOuterMeasure
              {y | P.pco ks.2 (y.2.1.found.getD (Classical.arbitrary M)) (P.enc ks.1 m r) = true} := by
  rw [owpcaAdvantage, prTrue_liftPMF_toOuterMeasure, owpcaGame]
  simp only [PMF.toOuterMeasure_bind_apply, Scheme.encDist, PMF.bind_map, Function.comp_def]
  refine tsum_congr fun ks => congrArg _ (tsum_congr fun m => congrArg _
    (tsum_congr fun r => congrArg _ ?_))
  grind [uReduction_prob]

omit [DecidableEq C] in
theorem corrErr_eq :
    P.corrErr = ∑' ks, P.keygen ks * ∑' m, PMF.uniformOfFintype M m *
      ∑' r, PMF.uniformOfFintype R r *
        failInd P ks.2 m (P.enc ks.1 m r) := by
  unfold PKE.Games.Scheme.corrErr PKE.Games.Scheme.failProb
  refine tsum_congr fun ks => congrArg _ (tsum_congr fun m => congrArg _ ?_)
  rw [PMF.toOuterMeasure_apply]
  refine tsum_congr fun r => ?_
  by_cases h : P.dec ks.2 (P.enc ks.1 m r) = some m <;> simp [Set.indicator, h, failInd]

end Summation

/-! ## The theorem -/

/-- **U̸⊥ is IND-CCA secure in the random-oracle model** (Hofheinz–Hövelmanns–Kiltz,
Theorem 3.4). For every public-key encryption scheme `P` and every IND-CCA adversary
`B` against `uNotBot P` asking at most `qH` random-oracle queries,

`romINDCCAAdvantage (uNotBot P) B ≤ owpcaAdvantage P (uReduction B) + qH/|M| + P.corrErr`.

The reduction `uReduction B` runs `B` once and asks at most `qH` plaintext-checking
queries. The term `qH/|M|` bounds the probability that `B` queries the random oracle
at the rejection seed; `P.corrErr` is the probability that a fresh encryption of a
uniform message does not decrypt to that message (`P.corrErr ≤ P.corrWorst`, the δ of
δ-correctness). The advantage is the distance between the real-key and random-key
experiments. -/
theorem uNotBot_indcca {qH qD : ℕ} (P : Scheme PK SK M C R)
    (B : ROMINDCCAAdversary PK K C (M × C) K qH qD) :
    romINDCCAAdvantage (uNotBot P) B ≤
      owpcaAdvantage P (uReduction B) + (qH : ℝ≥0∞) / Fintype.card M + P.corrErr := by
  refine (romINDCCAAdvantage_le_flag P B).trans ?_
  rw [flagDist, PMF.toOuterMeasure_bind_apply]
  calc ∑' x, setup P x * (OracleAdv.run (oFlag P x.sk x.s (x.m, x.c P) x.k₀)
          (B.run x.pk (x.c P) x.k₀) (emptyTable, false)).toOuterMeasure {y | y.2.2 = true}
      ≤ ∑' x, setup P x * (failInd P x.sk x.m (x.c P) +
          (OracleAdv.run (OracleAdv.simOracle (simImpl (x.c P) x.k₀) (pcoOracle P x.sk))
            (B.run x.pk (x.c P) x.k₀) (SimState.init, ())).toOuterMeasure
              {y | P.pco x.sk (y.2.1.found.getD (Classical.arbitrary M)) (x.c P) = true} +
          (OracleAdv.run (oTwo (badUpd x.s) (selPco P x.sk) (x.c P) x.k₀) (B.run x.pk (x.c P) x.k₀)
            (SimState.init, false)).toOuterMeasure {y | y.2.2 = true}) :=
        ENNReal.tsum_le_tsum fun x => mul_le_mul_right (flag_le P _ _ _ _ _ _) _
    _ = P.corrErr + owpcaAdvantage P (uReduction B) +
          ∑' x, setup P x * (OracleAdv.run (oTwo (badUpd x.s) (selPco P x.sk) (x.c P) x.k₀)
            (B.run x.pk (x.c P) x.k₀) (SimState.init, false)).toOuterMeasure {y | y.2.2 = true} := by
        simp only [mul_add, ENNReal.tsum_add]
        congr 2
        · rw [tsum_setup_mul, corrErr_eq]
          dsimp only [Draw.c]
          simp only [tsum_mul_const]
        · rw [tsum_setup_mul, owpcaAdvantage_uReduction]
          dsimp only [Draw.c]
          simp only [tsum_mul_const]
    _ ≤ P.corrErr + owpcaAdvantage P (uReduction B) + (qH : ℝ≥0∞) / Fintype.card M := by
        gcongr
        rw [tsum_setup_mul]
        simp only [Draw.c, tsum_mul_const]
        calc _ ≤ ∑' ks, P.keygen ks * ((qH : ℝ≥0∞) / Fintype.card M) := by
              refine ENNReal.tsum_le_tsum fun ks => mul_le_mul_right ?_ _
              rw [tsum_mul_comm]
              calc _ ≤ ∑' m, PMF.uniformOfFintype M m * ((qH : ℝ≥0∞) / Fintype.card M) := by
                    refine ENNReal.tsum_le_tsum fun m => mul_le_mul_right ?_ _
                    rw [tsum_mul_comm]
                    calc _ ≤ ∑' r, PMF.uniformOfFintype R r * ((qH : ℝ≥0∞) / Fintype.card M) := by
                          refine ENNReal.tsum_le_tsum fun r => mul_le_mul_right ?_ _
                          rw [tsum_mul_comm]
                          calc _ ≤ ∑' k₀, PMF.uniformOfFintype K k₀ *
                                ((qH : ℝ≥0∞) / Fintype.card M) := by
                                refine ENNReal.tsum_le_tsum fun k₀ => mul_le_mul_right ?_ _
                                exact tsum_bad_le _ _ _ _ qH (B.isQueryBoundH _ _ _)
                            _ = _ := tsum_mul_const _ _
                      _ = _ := tsum_mul_const _ _
                _ = _ := tsum_mul_const _ _
          _ = _ := tsum_mul_const _ _
    _ = _ := by ring

end CatCrypt.Crypto.KEM.FOTransformU
