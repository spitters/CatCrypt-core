/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.KEM.FIPS203KEM
public import CatCryptCore.Crypto.KEM.FOTransform

/-!
# IND-CCA security of the ML-KEM transform in the random-oracle model

`fips203 P hpk` (`CatCrypt.Crypto.KEM.FIPS203KEM`) is the KEM of FIPS 203 over a
public-key encryption scheme `P` with two random oracles `G : M × Hash → K × R` and
`J : Z × C → K`. This module carries the classical proof of
`KEM.FOTransform.foNotBot_indcca` (`U⊥̸[T[P, G], H]`) over to it: the reductions, the
bridge from `tKeyed` to `fixedT`, the challenge hop, the re-indexing of the oracle
tables, the `J`-prefix hop and the per-draw bound.

## Main definitions

* `SimStateF` — the state of the simulation of `G`, `J` and decapsulation
* `simImplF`, `redRun`, `redROM B` — the OW-PCA adversary against `tTransform P`
  built from an IND-CCA adversary `B` against `fips203 P hpk`
* `simImplFix`, `redFix B` — the same against `fixedT P f` for a fixed derandomiser
* `logged O key` — an oracle with a ghost log of the keys of its queries
* `Draw`, `setup`, `oFlag`, `flagDist` — the randomness of the IND-CCA experiment and
  the oracle with the challenge point of `G` removed and a query at it flagged
* `SplitTab`, `oSplit` — the tables and the flagged oracle with the coins at prefix
  `hpk pk` given by a fixed derandomiser
* `progF`, `progS` — the flagged and the split oracle as programs on an oracle for the
  values of `G` at prefix `hpk pk`, with `joinG`, `flatF` and `flatS` assembling their
  states
* `oSim`, `table`, `selK`, `selJ` — the re-indexed oracle, the tables it represents,
  and the selectors of the keys at prefix `hpk pk` and of `J`

## Main results

* `tKeyed_enc_eq_fixedT`, `tKeyed_dec_eq_fixedT` — on a key pair `(pk, sk)`,
  `tKeyed P f` is `fixedT P (f pk)`
* `uniformOfFintype_prod` — a uniform pair is a pair of independent uniform draws
* `tsum_uniform_mem_log_le` — averaged over a uniform `z`, a run whose queries carry
  at most `n` keys logs `z` with probability at most `n / |Z|`
* `advantage_le_flag` — the IND-CCA advantage against `fips203 P hpk` is at most the
  probability that the adversary queries `G` at the challenge point
* `oSim_map_table` — the re-indexed oracle maps onto `oSplit` through `table`
* `tsum_bad_le` — averaged over a uniform seed `z`, a run with at most `n`
  random-oracle queries makes a `J`-query with prefix `z` with probability at most
  `n / |Z|`
* `simOracle_simImplFix_eq` — the composite oracle of `redFix` is the re-indexed
  oracle with the selectors `selK` and `false`
* `flag_le` — the per-draw bound: the flagged split run hits the challenge point with
  probability at most the challenge's decryption-failure indicator, plus the success
  probability of the simulation, plus the `J`-prefix probability
* `oFlag_eq_eager` — the eager-sampling hop: averaged over a uniform challenge coin,
  the flagged run has the output and flag distribution of the split run averaged over
  a uniform derandomiser `f`, the challenge coin being `f m*`
* `advantage_le_eager` — the challenge hop stated over the split oracle
* `owpcaAdvantage_redFix` — the OW-PCA advantage of `redFix` as a sum over the key
  pair, the challenge message and the key
* `cca_le_three_terms` — the IND-CCA advantage bounded by the correctness error, the
  average over the derandomiser of the OW-PCA advantage of `redFix`, and `qRO/|Z|`
* `owpca_eq_redROM` — that average is the OW-PCA advantage of `redROM B` against
  `tTransform P`
* `fips203_indcca` — the IND-CCA advantage of `fips203 P hpk` bounded by two OW-CPA
  advantages, the correctness terms and `qRO/|Z|`

## Proof route

The steps of `FOTransformU.uNotBot_indcca`, and how each maps onto `fips203`:

1. Challenge hop (`romINDCCAAdvantage_le_flag`). Transfers, with the challenge point
   `(m*, hpk pk)` of `G` in place of `(m*, c*)` of `H` and the removed value the pair
   `(v, r*)`. Decapsulation of `c ≠ c*` with `P.dec sk c = some m*` reads the removed
   point; since `P.enc pk m* r* = c* ≠ c` it takes the rejection branch, so the flagged
   oracle answers it from `J` without reading the point. This is where rigidity of the
   derandomised scheme enters: `(tKeyed P f).dec (pk, sk) c = some m*` forces `c = c*`.
   Proved here as `advantage_le_flag`.
2. Re-indexing (`oTwo`, `table`, `oTwo_map_table`). Changes. In `uNotBot` the point
   `(m, c)` with `m = Dec(c)` is stored at `LD c`. Here the point `(m, hpk pk)` holds
   `(k, r)`; its `K`-part is the decapsulation key of `c_m := P.enc pk m r` exactly
   when `P.dec sk c_m = some m`, so it is stored at `LD c_m` and otherwise at `LQ m`;
   the `R`-part is the derandomiser and is not re-indexed. The selector is
   `pco(m, c_m)`, one plaintext-checking query per `G`-query at prefix `hpk pk` (the
   `U_m` variant: the key names `m`, not `c`, so the simulator recomputes the
   ciphertext from the coins). Two messages `m₁ ≠ m₂` with `c_{m₁} = c_{m₂}` cannot
   both pass the selector, so no injectivity of `P.enc` is needed. Decapsulation of `c`
   reads `LD c`, both when `c` rejects (the real game reads `J(z, c)`) and when
   `c = c_m`.
3. Seed hop (`tsum_bad_le` at `s ∈ M`). Becomes the `J`-prefix hop at `z ∈ Z`: the
   adversary's `J`-queries at prefix `z` alias `LD`, those at other prefixes are
   answered from a table `LJ` the scheme never reads. The two selectors agree on
   queries with prefix `≠ z`, and the bad probability averaged over `z` is at most
   `qRO / |Z|` (`tsum_uniform_mem_log_le`).
4. Simulation (`simImpl`, `simOracle_eq_oTwo`). The reduction is a `ROMOWPCAAdversary`
   against `tTransform P` rather than an `OWPCAAdversary` against a fixed scheme: it
   forwards the `R`-part of each `G`-query at prefix `hpk pk` to the random oracle of
   the OW-PCA game and samples the `K`-part and the other prefixes locally
   (`simImplF`). The passage from the lazily sampled coins of `oFlag` to a fixed
   derandomiser `f` is `oFlag_eq_eager`, which sends the `K`- and `R`-parts of the
   `G`-table to an eager pair of functions and keeps the keys lazy on the split side;
   `tKeyed_enc_eq_fixedT` and `tKeyed_dec_eq_fixedT` identify the
   derandomised scheme with `fixedT P (f pk)` on the key pair in play, and
   `uniformOfFintype_prod` separates the `K`- and `R`-coordinates of one `G`-value.
5. Correctness (`failInd`, `corrErr_eq`). Transfers: the challenge decrypts to `m*`
   except with probability `P.corrErr`.
6. Composition. `tTransform_owpca_of_total` with `n = 2·qRO`, since each `G`-query at
   prefix `hpk pk` costs one random-oracle and one plaintext-checking query.

Side conditions on `P`: only the correctness terms; rigidity is supplied by the
re-encryption in decapsulation, and no injectivity of `P.enc` is used.

## The model

* `fips203_indcca` is stated in the classical random-oracle model, with `hpk` a fixed
  function.
* `P` is a public-key encryption scheme with finite message, coin and key spaces, and
  `fips203_indcca` bounds the advantage against `fips203 P hpk` for every such `P`.
* The query bound passed to `tTransform_owpca_of_total` is the total `2·qRO`, one
  random-oracle and one plaintext-checking query per `G`-query at prefix `hpk pk`.

## References

* NIST FIPS 203, Algorithms 16–18.
* D. Hofheinz, K. Hövelmanns, E. Kiltz, *A Modular Analysis of the
  Fujisaki–Okamoto Transformation*, TCC 2017, ePrint 2017/604, Sections 3.3–3.4.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.KEM.FIPS203

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.PRPPRF
open CatCrypt.Crypto.PKE.Games CatCrypt.Crypto.KEM.Games
open CatCrypt.Crypto.KEM.FOTransform (fixedT)
open CatCrypt.Crypto.Constructions.ECBCPRF (toOuterMeasure_flag_eq toOuterMeasure_le_add_flag)
open scoped ENNReal

variable {PK SK M C R K Hash Z : Type} [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z]
  [Nonempty R] [Nonempty K] [DecidableEq C]

/-! ## The derandomised scheme -/

section Bridge

variable (P : Scheme PK SK M C R) (f : PK → M → R)

omit [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] [Nonempty R] [Nonempty K] in
/-- `tKeyed P f` encrypts under `pk` as `fixedT P (f pk)`. -/
theorem tKeyed_enc_eq_fixedT (pk : PK) (m : M) (u : Unit) :
    (tKeyed P f).enc pk m u = (fixedT P (f pk)).enc pk m u := rfl

omit [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] [Nonempty R] [Nonempty K] in
/-- `tKeyed P f` decrypts under `(pk, sk)` as `fixedT P (f pk)`. -/
theorem tKeyed_dec_eq_fixedT (pk : PK) (sk : SK) (c : C) :
    (tKeyed P f).dec (pk, sk) c = (fixedT P (f pk)).dec (pk, sk) c := rfl

omit [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] [Nonempty R] [Nonempty K] in
/-- `tKeyed P f` and `fixedT P g` generate keys alike. -/
theorem tKeyed_keygen_eq_fixedT (g : M → R) :
    (tKeyed P f).keygen = (fixedT P g).keygen := rfl

end Bridge

/-! ## A uniform pair -/

omit [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] [Nonempty R] [Nonempty K] [DecidableEq C] in
/-- A uniform pair is a uniform first coordinate followed by an independent uniform
second coordinate. -/
theorem uniformOfFintype_prod {α β : Type} [Fintype α] [Nonempty α] [Fintype β] [Nonempty β] :
    PMF.uniformOfFintype (α × β) =
      (PMF.uniformOfFintype α).bind fun a => (PMF.uniformOfFintype β).map fun b => (a, b) := by
  classical
  ext ⟨a, b⟩
  simp only [PMF.uniformOfFintype_apply, Fintype.card_prod, Nat.cast_mul, PMF.bind_apply,
    PMF.map_apply, tsum_fintype, Prod.mk.injEq]
  have hα : (Fintype.card α : ℝ≥0∞) ≠ 0 := by simp
  rw [Finset.sum_eq_single a]
  · rw [Finset.sum_eq_single b]
    · simp [ENNReal.mul_inv (Or.inl hα) (Or.inl (ENNReal.natCast_ne_top _))]
    · intro b' _ hb; simp [Ne.symm hb]
    · simp
  · intro a' _ ha
    simp [Ne.symm ha]
  · simp

/-! ## Logged oracles -/

section Logged

variable {D A σ : Type}

/-- The oracle `O` with a ghost log of the keys `key d` of its queries, most recent
first. -/
noncomputable def logged (O : σ → D → PMF (A × σ)) (key : D → Option Z) (s : σ × List Z)
    (d : D) : PMF (A × (σ × List Z)) :=
  (O s.1 d).map fun x => (x.1, (x.2, (key d).toList ++ s.2))

/-- The query cost counting queries that carry a key. -/
def keyCost (key : D → Option Z) (d : D) : ℕ := (key d).toList.length

omit [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] [Nonempty R] [Nonempty K] [DecidableEq C] in
/-- On every outcome of a run whose queries carry at most `n` keys, the log grows by
at most `n`. -/
theorem length_log_le_of_mem_support {α : Type} (O : σ → D → PMF (A × σ)) (key : D → Option Z)
    (B : OracleAdv D A α) (n : ℕ) (hB : B.IsQueryBoundBy (keyCost key) n) (s : σ) (l : List Z)
    (y : α × (σ × List Z)) (hy : y ∈ (OracleAdv.run (logged O key) B (s, l)).support) :
    y.2.2.length ≤ l.length + n := by
  induction B generalizing n s l with
  | ret a =>
    simp only [OracleAdv.run_ret, PMF.support_pure, Set.mem_singleton_iff] at hy
    subst hy; simp
  | rand p k ih =>
    simp only [OracleAdv.run_rand, PMF.mem_support_bind_iff] at hy
    obtain ⟨b, -, hy⟩ := hy
    exact ih b n (hB b) s l hy
  | query d k ih =>
    simp only [OracleAdv.run_query, PMF.mem_support_bind_iff] at hy
    obtain ⟨x, hx, hy⟩ := hy
    obtain ⟨hle, hk⟩ := hB
    have h1 := ih x.1 (n - keyCost key d) (hk x.1) x.2.1 x.2.2 hy
    have h2 : x.2.2.length = l.length + keyCost key d := by
      simp only [logged, PMF.support_map, Set.mem_image] at hx
      obtain ⟨z, -, rfl⟩ := hx
      simp [keyCost, Nat.add_comm]
    omega

omit [Fintype M] [Nonempty M] [Nonempty R] [Nonempty K] [DecidableEq C] in
/-- **Guessing a logged key.** Averaged over a uniform `z`, a run whose queries carry
at most `n` keys logs `z` with probability at most `n / |Z|`. -/
theorem tsum_uniform_mem_log_le {α : Type} [DecidableEq Z] (O : σ → D → PMF (A × σ))
    (key : D → Option Z) (B : OracleAdv D A α) (n : ℕ) (hB : B.IsQueryBoundBy (keyCost key) n)
    (s : σ) :
    ∑' z, PMF.uniformOfFintype Z z *
      (OracleAdv.run (logged O key) B (s, [])).toOuterMeasure {y | z ∈ y.2.2} ≤
      (n : ℝ≥0∞) / Fintype.card Z := by
  classical
  set p := OracleAdv.run (logged O key) B (s, [])
  have hs : ∀ z, p.toOuterMeasure {y | z ∈ y.2.2} = ∑' y, p y * (if z ∈ y.2.2 then 1 else 0) := by
    intro z
    rw [PMF.toOuterMeasure_apply]
    refine tsum_congr fun y => ?_
    by_cases h : z ∈ y.2.2 <;> simp [Set.indicator, h]
  simp_rw [hs, ← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  calc ∑' y, ∑' z, PMF.uniformOfFintype Z z * (p y * (if z ∈ y.2.2 then 1 else 0))
      ≤ ∑' y, p y * ((n : ℝ≥0∞) / Fintype.card Z) := by
        refine ENNReal.tsum_le_tsum fun y => ?_
        by_cases hy : p y = 0
        · simp [hy]
        have hlen : y.2.2.length ≤ n := by
          simpa using length_log_le_of_mem_support O key B n hB s [] y
            ((PMF.mem_support_iff _ _).mpr hy)
        have hcard : ∑' z, PMF.uniformOfFintype Z z * (if z ∈ y.2.2 then 1 else 0) ≤
            (n : ℝ≥0∞) / Fintype.card Z := by
          rw [tsum_fintype]
          simp only [PMF.uniformOfFintype_apply, mul_ite, mul_one, mul_zero]
          rw [Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const, nsmul_eq_mul,
            ENNReal.div_eq_inv_mul, mul_comm]
          gcongr
          exact (Finset.card_le_card fun z hz => by simpa using hz).trans
            ((List.toFinset_card_le _).trans hlen)
        calc ∑' z, PMF.uniformOfFintype Z z * (p y * (if z ∈ y.2.2 then 1 else 0))
            = p y * ∑' z, PMF.uniformOfFintype Z z * (if z ∈ y.2.2 then 1 else 0) := by
              rw [← ENNReal.tsum_mul_left]; exact tsum_congr fun z => by ring
          _ ≤ _ := by gcongr
    _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

end Logged

/-! ## The reduction -/

section Reduction

variable [DecidableEq M] [DecidableEq Hash] [DecidableEq Z] [Fintype R] [Fintype K]

variable (M C R K Hash Z) in
/-- The state of the simulation: the keys indexed by ciphertexts (decapsulation keys),
the keys of `G`-points at prefix `hpk pk` not aliased to a ciphertext, the values of
`G`-points at other prefixes, the values of the adversary's `J`-queries, and a message
found to encrypt to the challenge. -/
structure SimStateF where
  /-- Keys indexed by ciphertexts. -/
  LD : C → Option K
  /-- Keys of `G`-points at prefix `hpk pk` indexed by the message. -/
  LQ : M → Option K
  /-- Values of `G`-points at other prefixes. -/
  LO : M × Hash → Option (K × R)
  /-- Values of the adversary's `J`-queries. -/
  LJ : Z × C → Option K
  /-- A message `m` with `Pco(m, c*) = 1` found among the queries. -/
  found : Option M

/-- The initial simulation state. -/
def SimStateF.init : SimStateF M C R K Hash Z :=
  ⟨fun _ => none, fun _ => none, fun _ => none, fun _ => none, none⟩

/-- Answer from the table `tab` at `i`, sampling and recording a fresh value; `set`
stores the table back into the state and `w` shapes the answer. -/
noncomputable def lazyTab {D' R' I V S A : Type} [DecidableEq I] [Fintype V] [Nonempty V]
    (tab : I → Option V) (i : I) (set : (I → Option V) → S) (w : V → A) :
    OracleAdv D' R' (A × S) :=
  match tab i with
  | some v => .ret (w v, set tab)
  | none => .rand (PMF.uniformOfFintype V) fun v => .ret (w v, set (Function.update tab i (some v)))

omit [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] [Nonempty R] [Nonempty K] [DecidableEq C]
  [DecidableEq M] [DecidableEq Hash] [DecidableEq Z] [Fintype R] [Fintype K] in
theorem isQueryBoundBy_lazyTab {D' R' I V S A : Type} [DecidableEq I] [Fintype V] [Nonempty V]
    (cost : D' → ℕ) (tab : I → Option V) (i : I) (set : (I → Option V) → S) (w : V → A) (n : ℕ) :
    (lazyTab (D' := D') (R' := R') tab i set w).IsQueryBoundBy cost n := by
  unfold lazyTab; split
  · trivial
  · exact fun _ => trivial

/-- The simulation of `G`, `J` and decapsulation by the OW-PCA adversary against
`tTransform P`, from the challenge `c*` and the key `k*`. A `G`-query `(m, hpk pk)` is
answered by one random-oracle query for the coins `r`, one plaintext-checking query
on `(m, P.enc pk m r)`, and a key from the table indexed by `P.enc pk m r` when the
check passes (by `k*`, recording `m` as found, when `P.enc pk m r = c*`) and from the
table indexed by `m` otherwise; a `G`-query at another prefix and a `J`-query are
answered from their own tables; a decapsulation query is answered from the table
indexed by the ciphertext. -/
noncomputable def simImplF (P : Scheme PK SK M C R) (hpk : PK → Hash) (pk : PK) (cstar : C)
    (kstar : K) (st : SimStateF M C R K Hash Z) :
    ((M × Hash) ⊕ (Z × C)) ⊕ C →
      OracleAdv (M ⊕ (M × C)) (R ⊕ Bool) ((((K × R) ⊕ K) ⊕ Option K) × SimStateF M C R K Hash Z)
  | .inl (.inl q) =>
    if q.2 = hpk pk then
      .query (.inl q.1) fun a =>
        let r : R := a.elim id fun _ => Classical.arbitrary R
        .query (.inr (q.1, P.enc pk q.1 r)) fun b =>
          if b.elim (fun _ => false) id then
            (if P.enc pk q.1 r = cstar then
              .ret (.inl (.inl (kstar, r)), { st with found := some q.1 })
             else lazyTab st.LD (P.enc pk q.1 r) (fun t => { st with LD := t })
              fun k => .inl (.inl (k, r)))
          else lazyTab st.LQ q.1 (fun t => { st with LQ := t }) fun k => .inl (.inl (k, r))
    else lazyTab st.LO q (fun t => { st with LO := t }) fun kr => .inl (.inl kr)
  | .inl (.inr q) => lazyTab st.LJ q (fun t => { st with LJ := t }) fun k => .inl (.inr k)
  | .inr c => if c = cstar then .ret (.inr none, st) else
      lazyTab st.LD c (fun t => { st with LD := t }) fun k => .inr (some k)

omit [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] in
/-- Each query of the simulation costs at most one random-oracle query and one
plaintext-checking query, both on a `G`-query. -/
theorem isQueryBoundBy_simImplF (P : Scheme PK SK M C R) (hpk : PK → Hash) (pk : PK) (cstar : C)
    (kstar : K) (cost : M ⊕ (M × C) → ℕ) (hc : ∀ m q, cost (.inl m) + cost (.inr q) ≤ 1)
    (st : SimStateF M C R K Hash Z) (d : ((M × Hash) ⊕ (Z × C)) ⊕ C) :
    (simImplF P hpk pk cstar kstar st d).IsQueryBoundBy cost
      (Sum.elim (fun _ => 1) (fun _ => 0) d) := by
  rcases d with (q | q) | c
  · simp only [simImplF, Sum.elim_inl]
    split_ifs
    · refine ⟨(Nat.le_add_right _ _).trans (hc q.1 (q.1, cstar)), fun a => ?_⟩
      dsimp only
      have h2 := hc q.1 (q.1, P.enc pk q.1 (a.elim id fun _ => Classical.arbitrary R))
      refine ⟨by omega, fun b => ?_⟩
      dsimp only
      split_ifs
      · trivial
      · exact isQueryBoundBy_lazyTab _ _ _ _ _ _
      · exact isQueryBoundBy_lazyTab _ _ _ _ _ _
    · exact isQueryBoundBy_lazyTab _ _ _ _ _ _
  · simp only [simImplF]
    exact isQueryBoundBy_lazyTab _ _ _ _ _ _
  · simp only [simImplF, Sum.elim_inr]
    split_ifs
    · trivial
    · exact isQueryBoundBy_lazyTab _ _ _ _ _ _

/-- The run of the OW-PCA adversary against `tTransform P` built from `B`. -/
noncomputable def redRun (P : Scheme PK SK M C R) (hpk : PK → Hash) {qRO qD : ℕ}
    (B : ROM2INDCCAAdversary PK K C (M × Hash) (K × R) (Z × C) K qRO qD) (pk : PK) (c : C) :
    OracleAdv (M ⊕ (M × C)) (R ⊕ Bool) M :=
  .rand (PMF.uniformOfFintype K) fun kstar =>
    (OracleAdv.simulate (simImplF P hpk pk c kstar) (B.run pk c kstar) SimStateF.init).bind
      fun x => .ret (x.2.found.getD (Classical.arbitrary M))

omit [Fintype M] [Fintype Z] [Nonempty Z] in
theorem isQueryBoundBy_redRun (P : Scheme PK SK M C R) (hpk : PK → Hash) {qRO qD : ℕ}
    (B : ROM2INDCCAAdversary PK K C (M × Hash) (K × R) (Z × C) K qRO qD)
    (cost : M ⊕ (M × C) → ℕ) (hc : ∀ m q, cost (.inl m) + cost (.inr q) ≤ 1) (pk : PK) (c : C) :
    (redRun P hpk B pk c).IsQueryBoundBy cost qRO := by
  intro kstar
  have h := OracleAdv.isQueryBoundBy_bind (OracleAdv.isQueryBoundBy_simulate _ _ cost
    (isQueryBoundBy_simImplF P hpk pk c kstar cost hc) (B.isQueryBoundRO pk c kstar)
    SimStateF.init) (b := 0) (f := fun x : Bool × SimStateF M C R K Hash Z =>
      (OracleAdv.ret (x.2.found.getD (Classical.arbitrary M)) :
        OracleAdv (M ⊕ (M × C)) (R ⊕ Bool) M)) fun _ => trivial
  simpa using h

/-- The OW-PCA adversary against `tTransform P` built from an IND-CCA adversary `B`
against `fips203 P hpk`. It samples a key `k*`, runs `B` once on `(pk, c*, k*)` with
its oracles simulated by `simImplF`, and outputs a message found to encrypt to `c*`.
It asks at most `qRO` random-oracle and `qRO` plaintext-checking queries. -/
noncomputable def redROM (P : Scheme PK SK M C R) (hpk : PK → Hash) {qRO qD : ℕ}
    (B : ROM2INDCCAAdversary PK K C (M × Hash) (K × R) (Z × C) K qRO qD) :
    ROMOWPCAAdversary PK M C M R qRO qRO where
  run := redRun P hpk B
  isQueryBoundG := isQueryBoundBy_redRun P hpk B _ fun _ _ => le_rfl
  isQueryBoundP := isQueryBoundBy_redRun P hpk B _ fun _ _ => le_rfl

end Reduction

/-! ## The challenge hop -/

section ChallengeHop

variable [DecidableEq M] [DecidableEq Hash] [DecidableEq Z] [Fintype R] [Fintype K]

variable (PK SK M R K Z) in
/-- The randomness of the IND-CCA experiment: key pair, rejection seed, challenge
message and coins, and the two candidate keys. -/
structure Draw where
  /-- The public key. -/
  pk : PK
  /-- The secret key of `P`. -/
  sk : SK
  /-- The rejection seed. -/
  z : Z
  /-- The challenge message. -/
  m : M
  /-- The challenge coins. -/
  r : R
  /-- The encapsulated key. -/
  k₀ : K
  /-- The independent key. -/
  k₁ : K

variable (P : Scheme PK SK M C R) (hpk : PK → Hash)

/-- The joint distribution of the randomness of the IND-CCA experiment. -/
noncomputable def setup : PMF (Draw PK SK M R K Z) :=
  P.keygen.bind fun ks => (PMF.uniformOfFintype Z).bind fun z =>
    (PMF.uniformOfFintype M).bind fun m => (PMF.uniformOfFintype K).bind fun k₀ =>
      (PMF.uniformOfFintype R).bind fun r => (PMF.uniformOfFintype K).map fun k₁ =>
        ⟨ks.1, ks.2, z, m, r, k₀, k₁⟩

/-- The challenge ciphertext of a draw. -/
def Draw.c (x : Draw PK SK M R K Z) : C := P.enc x.pk x.m x.r

/-- Exchange the two candidate keys of a draw. -/
def Draw.swap (x : Draw PK SK M R K Z) : Draw PK SK M R K Z := { x with k₀ := x.k₁, k₁ := x.k₀ }

omit [DecidableEq M] [DecidableEq Hash] [DecidableEq Z] [DecidableEq C] in
theorem setup_map_swap :
    (setup (K := K) (Z := Z) P).map Draw.swap = setup (K := K) (Z := Z) P := by
  simp only [setup, PMF.map_bind, PMF.map_comp]
  refine congrArg _ (funext fun ks => congrArg _ (funext fun z => congrArg _ (funext fun m => ?_)))
  simp only [PMF.map, Function.comp_def, Draw.swap]
  rw [PMF.bind_comm (PMF.uniformOfFintype K) (PMF.uniformOfFintype R)]
  conv_rhs => rw [PMF.bind_comm (PMF.uniformOfFintype K) (PMF.uniformOfFintype R)]
  refine congrArg _ (funext fun r => ?_)
  exact PMF.bind_comm _ _ _

/-- The tables of the two random oracles. -/
abbrev Tab (M C R K Hash Z : Type) : Type :=
  ((M × Hash) → Option (K × R)) × ((Z × C) → Option K)

/-- A read of `J` at `(z, c)` from the tables `T`, as a decapsulation answer. -/
noncomputable def jRead (T : Tab M C R K Hash Z) (b : Bool) (q : Z × C) :
    PMF ((((K × R) ⊕ K) ⊕ Option K) × (Tab M C R K Hash Z × Bool)) :=
  (roOracle T.2 q).map fun y => (.inr (some y.1), ((T.1, y.2), b))

/-- The oracle of the IND-CCA experiment for `fips203 P hpk` with the point
`(m*, hpk pk)` of `G` removed from the table: a query of the adversary at it returns
`(v, r*)` and sets the flag; decapsulation of `c ≠ c*` decrypting to `m*` takes the
rejection branch, since `P.enc pk m* r* = c* ≠ c`. -/
noncomputable def oFlag (sk : SK) (pk : PK) (z : Z) (mstar : M) (rstar : R) (v : K)
    (st : Tab M C R K Hash Z × Bool) :
    ((M × Hash) ⊕ (Z × C)) ⊕ C → PMF ((((K × R) ⊕ K) ⊕ Option K) × (Tab M C R K Hash Z × Bool))
  | .inl (.inl q) => if q = (mstar, hpk pk) then PMF.pure (.inl (.inl (v, rstar)), (st.1, true))
      else (roOracle st.1.1 q).map fun x => (.inl (.inl x.1), ((x.2, st.1.2), st.2))
  | .inl (.inr q) => (roOracle st.1.2 q).map fun x => (.inl (.inr x.1), ((st.1.1, x.2), st.2))
  | .inr c => if c = P.enc pk mstar rstar then PMF.pure (.inr none, st) else
      match P.dec sk c with
      | none => jRead st.1 st.2 (z, c)
      | some m => if m = mstar then jRead st.1 st.2 (z, c) else
          (roOracle st.1.1 (m, hpk pk)).bind fun x =>
            if P.enc pk m x.1.2 = c then PMF.pure (.inr (some x.1.1), ((x.2, st.1.2), st.2))
            else jRead (x.2, st.1.2) st.2 (z, c)

/-- The distribution of the flagged run; `swap` selects the candidate key stored at
the challenge point. -/
noncomputable def flagDist {qRO qD : ℕ}
    (B : ROM2INDCCAAdversary PK K C (M × Hash) (K × R) (Z × C) K qRO qD) (swap : Bool) :
    PMF (Bool × (Tab M C R K Hash Z × Bool)) :=
  (setup P).bind fun x => OracleAdv.run
    (oFlag P hpk x.sk x.pk x.z x.m x.r (if swap then x.k₁ else x.k₀))
    (B.run x.pk (x.c P) x.k₀) ((emptyTable, emptyTable), false)

omit [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] [DecidableEq M] [DecidableEq Hash]
  [DecidableEq Z] [DecidableEq C] in
theorem roOracle_update_ne {D V : Type} [DecidableEq D] [Fintype V] [Nonempty V]
    (T : D → Option V) (d k : D) (w : V) (h : d ≠ k) :
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

/-- The map storing `(v, r*)` at the challenge point of the tables. -/
def storePt (pk : PK) (mstar : M) (rstar : R) (v : K) (y : Tab M C R K Hash Z × Bool) :
    Tab M C R K Hash Z :=
  (Function.update y.1.1 (mstar, hpk pk) (some (v, rstar)), y.1.2)

omit [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] in
theorem jRead_map_store (pk : PK) (mstar : M) (rstar : R) (v : K) (T : Tab M C R K Hash Z)
    (b : Bool) (q : Z × C) :
    (jRead T b q).map (Prod.map id (storePt hpk pk mstar rstar v)) =
      (OracleAdv.run ro2Oracle ((jQ (M := M) (Hash := Hash) (R := R) q).bind fun k => .ret (some k))
        (storePt hpk pk mstar rstar v (T, b))).map fun x =>
          ((Sum.inr x.1 : ((K × R) ⊕ K) ⊕ Option K), x.2) := by
  simp only [jRead, jQ, storePt, OracleAdv.run_bind, OracleAdv.run_query, OracleAdv.run_ret,
    ro2Oracle, Function.comp_def, Sum.elim_inr, id, PMF.bind_bind, PMF.pure_bind, PMF.map]
  rfl

/-- Storing `(v, r*)` at the challenge point commutes with each transition of the
flagged oracle and the oracle of the experiment. -/
theorem oFlag_map (sk : SK) (pk : PK) (z : Z) (mstar : M) (rstar : R) (v : K)
    (st : Tab M C R K Hash Z × Bool) (d : ((M × Hash) ⊕ (Z × C)) ⊕ C) :
    (oFlag P hpk sk pk z mstar rstar v st d).map (Prod.map id (storePt hpk pk mstar rstar v)) =
      rom2CCAOracle (fips203 P hpk) (sk, pk, z) (P.enc pk mstar rstar)
        (storePt hpk pk mstar rstar v st) d := by
  rcases d with (q | q) | c
  · by_cases hq : q = (mstar, hpk pk)
    · subst hq
      simp [oFlag, rom2CCAOracle, ro2Oracle, roOracle, storePt, PMF.pure_map]
    · simp only [oFlag, rom2CCAOracle, ro2Oracle, hq, if_false, PMF.map_comp, storePt]
      rw [← roOracle_update_ne _ _ _ _ hq, PMF.map_comp]
      rfl
  · simp only [oFlag, rom2CCAOracle, ro2Oracle, PMF.map_comp, storePt]
    rfl
  · by_cases hc : c = P.enc pk mstar rstar
    · subst hc
      simp [oFlag, rom2CCAOracle, storePt, PMF.pure_map]
    · simp only [oFlag, rom2CCAOracle, hc, if_false]
      rcases hd : P.dec sk c with _ | m
      · dsimp only
        rw [jRead_map_store]
        simp only [fips203, hd]
      · dsimp only
        by_cases hm : m = mstar
        · subst hm
          rw [if_pos rfl, jRead_map_store]
          have hc' : P.enc pk m rstar ≠ c := Ne.symm hc
          simp only [fips203, hd, gQ, OracleAdv.run_bind, OracleAdv.run_query, OracleAdv.run_ret,
            ro2Oracle, storePt, roOracle, Function.update_self, PMF.map_bind, PMF.pure_map,
            PMF.pure_bind, Sum.elim_inl, id, hc', if_false]
        · have hne : (m, hpk pk) ≠ (mstar, hpk pk) := fun h => hm (congrArg Prod.fst h)
          simp only [fips203, hd, hm, if_false, gQ, OracleAdv.run_bind, OracleAdv.run_query,
            OracleAdv.run_ret, ro2Oracle, PMF.map_bind, PMF.bind_map, storePt]
          rw [← roOracle_update_ne _ _ _ _ hne, PMF.bind_map, PMF.bind_bind]
          refine congrArg _ (funext fun x => ?_)
          simp only [Function.comp_def, PMF.pure_bind, Sum.elim_inl, id]
          split_ifs with he
          · simp [PMF.pure_map, storePt]
          · have := jRead_map_store hpk pk mstar rstar v (x.2, st.1.2) st.2 (z, c)
            simp only [storePt] at this
            rw [this]

/-- A run of the experiment's oracle from the tables holding only `(v, r*)` at the
challenge point is the flagged run with the flag and the tables forgotten. -/
theorem run_rom2CCAOracle_eq {α : Type} (sk : SK) (pk : PK) (z : Z) (mstar : M) (rstar : R)
    (v : K) (A : OracleAdv (((M × Hash) ⊕ (Z × C)) ⊕ C) (((K × R) ⊕ K) ⊕ Option K) α) :
    (OracleAdv.run (rom2CCAOracle (fips203 P hpk) (sk, pk, z) (P.enc pk mstar rstar)) A
      (Function.update emptyTable (mstar, hpk pk) (some (v, rstar)), emptyTable)).map Prod.fst =
    (OracleAdv.run (oFlag P hpk sk pk z mstar rstar v) A ((emptyTable, emptyTable), false)).map
      Prod.fst := by
  have h := OracleAdv.run_map_state (oFlag P hpk sk pk z mstar rstar v)
    (rom2CCAOracle (fips203 P hpk) (sk, pk, z) (P.enc pk mstar rstar)) (storePt hpk pk mstar rstar v)
    (fun st d => oFlag_map P hpk sk pk z mstar rstar v st d) A ((emptyTable, emptyTable), false)
  calc _ = ((OracleAdv.run (oFlag P hpk sk pk z mstar rstar v) A ((emptyTable, emptyTable), false)).map
        (Prod.map id (storePt hpk pk mstar rstar v))).map Prod.fst := by rw [h]; rfl
    _ = _ := by rw [PMF.map_comp]; rfl

theorem rom2INDCCAGame_fips203 {qRO qD : ℕ}
    (B : ROM2INDCCAAdversary PK K C (M × Hash) (K × R) (Z × C) K qRO qD) (b : Bool) :
    rom2INDCCAGame (fips203 P hpk) B b = (setup P).bind fun x =>
      (OracleAdv.run (oFlag P hpk x.sk x.pk x.z x.m x.r x.k₀)
        (B.run x.pk (x.c P) (if b then x.k₀ else x.k₁)) ((emptyTable, emptyTable), false)).map
          Prod.fst := by
  have hempty : ∀ q : M × Hash, (emptyTable : M × Hash → Option (K × R)) q = none := fun _ => rfl
  simp only [rom2INDCCAGame, setup, fips203, gQ, PMF.bind_bind, PMF.bind_map, Function.comp_def,
    OracleAdv.run_rand, OracleAdv.run_bind, OracleAdv.run_query, OracleAdv.run_ret, ro2Oracle,
    roOracle, hempty, PMF.map_bind, PMF.pure_bind, Sum.elim_inl, id, uniformOfFintype_prod]
  refine congrArg _ (funext fun ks => congrArg _ (funext fun z => congrArg _ (funext fun m =>
    congrArg _ (funext fun k₀ => congrArg _ (funext fun r => ?_)))))
  simp only [PMF.map, Function.comp_def]
  refine congrArg _ (funext fun k₁ => ?_)
  exact run_rom2CCAOracle_eq P hpk ks.2 ks.1 z m r k₀ _

omit [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] [Nonempty R] [DecidableEq M]
  [DecidableEq Hash] [Fintype R] in
theorem jRead_apply_true_false (T : Tab M C R K Hash Z) (q : Z × C)
    (a : ((K × R) ⊕ K) ⊕ Option K) (T' : Tab M C R K Hash Z) :
    jRead T true q (a, (T', false)) = 0 := by
  rw [jRead, PMF.map_apply]; simp

omit [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] in
theorem oFlag_apply_true_false (sk : SK) (pk : PK) (z : Z) (mstar : M) (rstar : R) (v : K)
    (T : Tab M C R K Hash Z) (d : ((M × Hash) ⊕ (Z × C)) ⊕ C) (a : ((K × R) ⊕ K) ⊕ Option K)
    (T' : Tab M C R K Hash Z) :
    oFlag P hpk sk pk z mstar rstar v (T, true) d (a, (T', false)) = 0 := by
  rcases d with (q | q) | c
  · simp only [oFlag]
    split_ifs
    · simp [PMF.pure_apply]
    · rw [PMF.map_apply]; simp
  · simp only [oFlag]
    rw [PMF.map_apply]; simp
  · simp only [oFlag]
    split_ifs
    · simp [PMF.pure_apply]
    · rcases P.dec sk c with _ | m
      · exact jRead_apply_true_false _ _ _ _
      · dsimp only
        split_ifs
        · exact jRead_apply_true_false _ _ _ _
        · rw [PMF.bind_apply]
          refine ENNReal.tsum_eq_zero.mpr fun x => ?_
          split_ifs
          · simp [PMF.pure_apply]
          · simp [jRead_apply_true_false]

omit [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] in
theorem oFlag_apply_false_eq (sk : SK) (pk : PK) (z : Z) (mstar : M) (rstar : R) (v v' : K)
    (st : Tab M C R K Hash Z × Bool) (d : ((M × Hash) ⊕ (Z × C)) ⊕ C)
    (a : ((K × R) ⊕ K) ⊕ Option K) (T' : Tab M C R K Hash Z) :
    oFlag P hpk sk pk z mstar rstar v st d (a, (T', false)) =
      oFlag P hpk sk pk z mstar rstar v' st d (a, (T', false)) := by
  rcases d with (q | q) | c
  · simp only [oFlag]
    split_ifs
    · simp [PMF.pure_apply]
    · rfl
  · rfl
  · rfl

/-- **Challenge hop.** The IND-CCA advantage against `fips203 P hpk` is at most the
probability that the adversary queries `G` at the challenge point. -/
theorem advantage_le_flag {qRO qD : ℕ}
    (B : ROM2INDCCAAdversary PK K C (M × Hash) (K × R) (Z × C) K qRO qD) :
    rom2INDCCAAdvantage (fips203 P hpk) B ≤
      (flagDist P hpk B false).toOuterMeasure {x | x.2.2 = true} := by
  have h₁ : rom2INDCCAGame (fips203 P hpk) B true = (flagDist P hpk B false).map Prod.fst := by
    rw [rom2INDCCAGame_fips203, flagDist, PMF.map_bind]
    rfl
  have h₂ : rom2INDCCAGame (fips203 P hpk) B false = (flagDist P hpk B true).map Prod.fst := by
    rw [rom2INDCCAGame_fips203, flagDist, PMF.map_bind]
    conv_lhs => rw [← setup_map_swap P, PMF.bind_map]
    rfl
  have h : ∀ a t, flagDist P hpk B false (a, (t, false)) = flagDist P hpk B true (a, (t, false)) := by
    intro a t
    simp only [flagDist, PMF.bind_apply]
    refine tsum_congr fun x => congrArg _ ?_
    grind [OracleAdv.run_apply_flag_false_eq, oFlag_apply_true_false, oFlag_apply_false_eq]
  unfold rom2INDCCAAdvantage
  rw [h₁, h₂]
  simp only [Advantage, prTrue_pmfGame_map]
  refine max_le (tsub_le_iff_left.mpr ?_) (tsub_le_iff_left.mpr ?_)
  · rw [toOuterMeasure_flag_eq _ _ h]
    simpa only [Set.mem_singleton_iff] using toOuterMeasure_le_add_flag _ _ h {true}
  · simpa only [Set.mem_singleton_iff] using
      toOuterMeasure_le_add_flag _ _ (fun a t => (h a t).symm) {true}

end ChallengeHop

/-! ## The split oracle and its re-indexing -/

section Split

variable [DecidableEq M] [DecidableEq Hash] [DecidableEq Z] [Fintype R] [Fintype K]

variable (M C R K Hash Z) in
/-- The tables of the flagged oracle with the coins at prefix `hpk pk` fixed: the keys
of `G` at prefix `hpk pk` by message, the values of `G` at other prefixes, and `J`. -/
structure SplitTab where
  /-- Keys of `G` at prefix `hpk pk`. -/
  TK : M → Option K
  /-- Values of `G` at other prefixes. -/
  LO : M × Hash → Option (K × R)
  /-- The table of `J`. -/
  TJ : Z × C → Option K

/-- The empty tables. -/
def SplitTab.empty : SplitTab M C R K Hash Z := ⟨fun _ => none, fun _ => none, fun _ => none⟩

/-- Answer from the table `tab` at `i` with ghost state `g`, sampling and recording a
fresh value; `set` stores the table back into the state and `w` shapes the answer. -/
noncomputable def lazyRead {I V S G A : Type} [DecidableEq I] [Fintype V] [Nonempty V]
    (tab : I → Option V) (i : I) (set : (I → Option V) → S) (w : V → A) (g : G) :
    PMF (A × (S × G)) :=
  match tab i with
  | some v => PMF.pure (w v, (set tab, g))
  | none => (PMF.uniformOfFintype V).map fun v =>
      (w v, (set (Function.update tab i (some v)), g))

omit [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] [Nonempty R] [Nonempty K] [DecidableEq C]
  [DecidableEq M] [DecidableEq Hash] [DecidableEq Z] [Fintype R] [Fintype K] in
theorem lazyRead_eq {I V S G A : Type} [DecidableEq I] [Fintype V] [Nonempty V]
    (tab : I → Option V) (i : I) (set : (I → Option V) → S) (w : V → A) (g : G) :
    lazyRead tab i set w g = (roOracle tab i).map fun x => (w x.1, (set x.2, g)) := by
  unfold lazyRead roOracle
  cases tab i <;> simp [PMF.pure_map, PMF.map_comp, Function.comp_def]

omit [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] [Nonempty R] [Nonempty K] [DecidableEq C]
  [DecidableEq M] [DecidableEq Hash] [DecidableEq Z] [Fintype R] [Fintype K] in
theorem lazyRead_map_ghost {I V S G G' A : Type} [DecidableEq I] [Fintype V] [Nonempty V]
    (φ : G → G') (tab : I → Option V) (i : I) (set : (I → Option V) → S) (w : V → A) (g : G) :
    (lazyRead tab i set w g).map (Prod.map id (Prod.map id φ)) = lazyRead tab i set w (φ g) := by
  unfold lazyRead; split <;> simp [PMF.pure_map, PMF.map_comp, Function.comp_def]

omit [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] [Nonempty R] [Nonempty K] [DecidableEq C]
  [DecidableEq M] [DecidableEq Hash] [DecidableEq Z] [Fintype R] [Fintype K] in
theorem lazyRead_map_const {I V S G G' A : Type} [DecidableEq I] [Fintype V] [Nonempty V]
    (tab : I → Option V) (i : I) (set : (I → Option V) → S) (w : V → A) (g : G) (g' : G') :
    (lazyRead tab i set w g).map (fun y => (y.1, (y.2.1, g'))) = lazyRead tab i set w g' := by
  unfold lazyRead; split <;> simp [PMF.pure_map, PMF.map_comp, Function.comp_def]

omit [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] [Nonempty R] [Nonempty K] [DecidableEq C]
  [DecidableEq M] [DecidableEq Hash] [DecidableEq Z] [Fintype R] [Fintype K] in
theorem lazyRead_apply_ghost_ne {I V S G A : Type} [DecidableEq I] [Fintype V] [Nonempty V]
    (tab : I → Option V) (i : I) (set : (I → Option V) → S) (w : V → A) (g : G) (a : A) (s : S)
    (g' : G) (h : g ≠ g') : lazyRead tab i set w g (a, (s, g')) = 0 := by
  unfold lazyRead; split
  · simp [PMF.pure_apply, Ne.symm h]
  · rw [PMF.map_apply]; simp [Ne.symm h]

omit [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] [Nonempty R] [Nonempty K] [DecidableEq C]
  [DecidableEq M] [DecidableEq Hash] [DecidableEq Z] [Fintype R] [Fintype K] in
theorem mem_support_lazyRead_ghost {I V S G A : Type} [DecidableEq I] [Fintype V] [Nonempty V]
    {tab : I → Option V} {i : I} {set : (I → Option V) → S} {w : V → A} {g : G}
    {x : A × (S × G)} (hx : x ∈ (lazyRead tab i set w g).support) : x.2.2 = g := by
  by_contra h
  obtain ⟨a, s, g'⟩ := x
  exact (PMF.mem_support_iff _ _).mp hx (lazyRead_apply_ghost_ne _ _ _ _ _ _ _ _ (Ne.symm h))

omit [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] [Nonempty R] [Nonempty K] [DecidableEq C]
  [DecidableEq M] [DecidableEq Hash] [DecidableEq Z] [Fintype R] [Fintype K] in
/-- A run of `lazyTab` against any oracle is `lazyRead` with the oracle state as
ghost. -/
theorem run_lazyTab {D' R' U I V S A : Type} [DecidableEq I] [Fintype V] [Nonempty V]
    (O : U → D' → PMF (R' × U)) (tab : I → Option V) (i : I) (set : (I → Option V) → S)
    (w : V → A) (u : U) :
    (OracleAdv.run O (lazyTab tab i set w) u).map (fun x => (x.1.1, (x.1.2, x.2))) =
      lazyRead tab i set w u := by
  unfold lazyTab lazyRead
  split <;> simp [PMF.pure_map, PMF.map_bind]; rfl

variable (P : Scheme PK SK M C R) (hpk : PK → Hash) (f : M → R)

/-- The ciphertext of `m` under `pk` with the coins `f m`. -/
def cOf (pk : PK) (m : M) : C := P.enc pk m (f m)

/-- The selector of the keys at prefix `hpk pk`: the key of `m` is the decapsulation
key of `cOf f pk m` when that ciphertext decrypts to `m`. -/
def selK (sk : SK) (pk : PK) (m : M) : Bool := decide (P.dec sk (cOf P f pk m) = some m)

/-- `c` is valid: the derandomised scheme decrypts it. -/
noncomputable def validB (sk : SK) (pk : PK) (c : C) : Bool :=
  ((fixedT P f).dec (pk, sk) c).isSome

/-- The selector of `J`: the query `(z', c)` reads the decapsulation key of `c` when
`z' = z` and `c` is not valid. -/
noncomputable def selJ (sk : SK) (pk : PK) (z : Z) (q : Z × C) : Bool :=
  decide (q.1 = z) && !validB P f sk pk q.2

/-- A read of `J` from the split tables, as a decapsulation answer. -/
noncomputable def jSplit (st : SplitTab M C R K Hash Z × Bool) (q : Z × C) :
    PMF ((((K × R) ⊕ K) ⊕ Option K) × (SplitTab M C R K Hash Z × Bool)) :=
  (roOracle st.1.TJ q).map fun x => (.inr (some x.1), ({ st.1 with TJ := x.2 }, st.2))

/-- The flagged oracle with the coins at prefix `hpk pk` given by `f`: the keys at that
prefix, the values at other prefixes and `J` are sampled lazily; a query of the
adversary at `(m*, hpk pk)` returns `(v, f m*)` and sets the flag; decapsulation reads
the key of `m = Dec(sk, c)` when `cOf f pk m = c` and `J` at `(z, c)` otherwise. -/
noncomputable def oSplit (sk : SK) (pk : PK) (z : Z) (mstar : M) (v : K)
    (st : SplitTab M C R K Hash Z × Bool) :
    ((M × Hash) ⊕ (Z × C)) ⊕ C →
      PMF ((((K × R) ⊕ K) ⊕ Option K) × (SplitTab M C R K Hash Z × Bool))
  | .inl (.inl q) =>
    if q.2 = hpk pk then
      (if q.1 = mstar then PMF.pure (.inl (.inl (v, f mstar)), (st.1, true))
       else (roOracle st.1.TK q.1).map fun x =>
        (.inl (.inl (x.1, f q.1)), ({ st.1 with TK := x.2 }, st.2)))
    else (roOracle st.1.LO q).map fun x => (.inl (.inl x.1), ({ st.1 with LO := x.2 }, st.2))
  | .inl (.inr q) => (roOracle st.1.TJ q).map fun x =>
      (.inl (.inr x.1), ({ st.1 with TJ := x.2 }, st.2))
  | .inr c => if c = cOf P f pk mstar then PMF.pure (.inr none, st) else
      match P.dec sk c with
      | none => jSplit st (z, c)
      | some m => if m = mstar then jSplit st (z, c) else
          if cOf P f pk m = c then
            (roOracle st.1.TK m).map fun x => (.inr (some x.1), ({ st.1 with TK := x.2 }, st.2))
          else jSplit st (z, c)

/-- The re-indexed oracle with selectors `sK` for the keys at prefix `hpk pk` and `sJ`
for `J`, challenge `c*` and key `v`: a `G`-query `(m, hpk pk)` with `sK m` is answered
from the table indexed by `cOf f pk m` (by `v`, recording `m` as found, when that
ciphertext is `c*`), without `sK m` from the table indexed by `m`; a `G`-query at
another prefix from its own table; a `J`-query `q` with `sJ q` from the table indexed
by `q.2` and otherwise from the table of `J`-queries; a decapsulation query from the
table indexed by the ciphertext. Each `J`-query updates the ghost state with
`upd q.1`. -/
noncomputable def oSim {G : Type} (upd : Z → G → G) (sK : M → Bool) (sJ : Z × C → Bool)
    (pk : PK) (cstar : C) (v : K) (x : SimStateF M C R K Hash Z × G) :
    ((M × Hash) ⊕ (Z × C)) ⊕ C →
      PMF ((((K × R) ⊕ K) ⊕ Option K) × (SimStateF M C R K Hash Z × G))
  | .inl (.inl q) =>
    if q.2 = hpk pk then
      (if sK q.1 then
        (if cOf P f pk q.1 = cstar then
          PMF.pure (.inl (.inl (v, f q.1)), ({ x.1 with found := some q.1 }, x.2))
         else lazyRead x.1.LD (cOf P f pk q.1) (fun t => { x.1 with LD := t })
          (fun k => .inl (.inl (k, f q.1))) x.2)
       else lazyRead x.1.LQ q.1 (fun t => { x.1 with LQ := t }) (fun k => .inl (.inl (k, f q.1))) x.2)
    else lazyRead x.1.LO q (fun t => { x.1 with LO := t }) (fun kr => .inl (.inl kr)) x.2
  | .inl (.inr q) =>
    if sJ q then lazyRead x.1.LD q.2 (fun t => { x.1 with LD := t }) (fun k => .inl (.inr k))
      (upd q.1 x.2)
    else lazyRead x.1.LJ q (fun t => { x.1 with LJ := t }) (fun k => .inl (.inr k)) (upd q.1 x.2)
  | .inr c => if c = cstar then PMF.pure (.inr none, x) else
      lazyRead x.1.LD c (fun t => { x.1 with LD := t }) (fun k => .inr (some k)) x.2

/-- The split tables represented by a simulation state: the key of `m` is read from
the table indexed by `cOf f pk m` when `selK`, and from the table indexed by `m`
otherwise; `J` at `q` is read from the table indexed by `q.2` when `selJ`, and from
the table of `J`-queries otherwise. -/
noncomputable def table (sk : SK) (pk : PK) (z : Z) (st : SimStateF M C R K Hash Z) :
    SplitTab M C R K Hash Z :=
  ⟨fun m => if selK P f sk pk m then st.LD (cOf P f pk m) else st.LQ m, st.LO,
    fun q => if selJ P f sk pk z q then st.LD q.2 else st.LJ q⟩

omit [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] [Nonempty R] [Nonempty K] [Fintype R]
  [Fintype K] [DecidableEq C] in
theorem selK_of_dec (sk : SK) (pk : PK) (m : M) (c : C) (hd : P.dec sk c = some m)
    (hc : cOf P f pk m = c) : selK P f sk pk m = true := by
  simp [selK, hc, hd]

omit [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] [Nonempty R] [Nonempty K] [Fintype R]
  [Fintype K] [DecidableEq M] in
theorem validB_eq_true_iff (sk : SK) (pk : PK) (c : C) :
    validB P f sk pk c = true ↔ ∃ m, P.dec sk c = some m ∧ cOf P f pk m = c := by
  simp only [validB, fixedT, cOf, Option.isSome_iff_exists]
  cases P.dec sk c with
  | none => simp
  | some m =>
    dsimp only
    constructor
    · rintro ⟨m', hm'⟩
      split_ifs at hm' with he
      exact ⟨m, rfl, he⟩
    · rintro ⟨m', hm', he⟩
      simp only [Option.some.injEq] at hm'
      subst hm'
      exact ⟨_, if_pos he⟩

omit [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] [Nonempty R] [Nonempty K] [Fintype R]
  [Fintype K] [DecidableEq Hash] in
/-- Storing a key at an invalid ciphertext updates the table of `J` at `(z, c)`. -/
theorem table_updateLD_of_invalid (sk : SK) (pk : PK) (z : Z) (st : SimStateF M C R K Hash Z)
    (c : C) (k : K) (hc : validB P f sk pk c = false) :
    table P f sk pk z { st with LD := Function.update st.LD c (some k) } =
      { table P f sk pk z st with TJ := Function.update (table P f sk pk z st).TJ (z, c) (some k) } := by
  simp only [table, SplitTab.mk.injEq]
  refine ⟨funext fun m => ?_, trivial, funext fun q => ?_⟩
  · by_cases hs : selK P f sk pk m = true
    · simp only [hs, if_true]
      rw [Function.update_of_ne]
      intro he
      have : validB P f sk pk c = true := (validB_eq_true_iff P f sk pk c).mpr
        ⟨m, by simpa [selK, he] using hs, he⟩
      exact Bool.noConfusion (this.symm.trans hc)
    · simp [hs]
  · obtain ⟨z', c'⟩ := q
    by_cases hq : (z', c') = (z, c)
    · simp only [Prod.mk.injEq] at hq
      obtain ⟨rfl, rfl⟩ := hq
      simp [selJ, hc]
    · rw [Function.update_of_ne hq]
      by_cases hs : selJ P f sk pk z (z', c') = true
      · simp only [hs, if_true]
        rw [Function.update_of_ne]
        intro he
        subst he
        simp only [selJ, Bool.and_eq_true, decide_eq_true_eq] at hs
        exact hq (by rw [hs.1])
      · simp [hs]

omit [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] [Nonempty R] [Nonempty K] [Fintype R]
  [Fintype K] [DecidableEq Hash] in
/-- Storing a key at a valid ciphertext decrypting to `m` updates the key of `m`. -/
theorem table_updateLD_of_valid (sk : SK) (pk : PK) (z : Z) (st : SimStateF M C R K Hash Z)
    (c : C) (m : M) (k : K) (hd : P.dec sk c = some m) (hc : cOf P f pk m = c) :
    table P f sk pk z { st with LD := Function.update st.LD c (some k) } =
      { table P f sk pk z st with TK := Function.update (table P f sk pk z st).TK m (some k) } := by
  have hv : validB P f sk pk c = true := (validB_eq_true_iff P f sk pk c).mpr ⟨m, hd, hc⟩
  simp only [table, SplitTab.mk.injEq]
  refine ⟨funext fun m' => ?_, trivial, funext fun q => ?_⟩
  · by_cases hm : m' = m
    · subst hm
      simp [selK_of_dec P f sk pk m' c hd hc, hc]
    · rw [Function.update_of_ne hm]
      by_cases hs : selK P f sk pk m' = true
      · simp only [hs, if_true]
        rw [Function.update_of_ne]
        intro he
        simp only [selK, he, hd, Option.some.injEq, decide_eq_true_eq] at hs
        exact hm hs.symm
      · simp [hs]
  · by_cases hs : selJ P f sk pk z q = true
    · simp only [hs, if_true]
      rw [Function.update_of_ne]
      intro he
      simp only [selJ, Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hs
      rw [he] at hs
      simp [hv] at hs
    · simp [hs]

omit [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] [Nonempty R] [Nonempty K] [Fintype R]
  [Fintype K] [DecidableEq Hash] in
theorem table_updateLQ (sk : SK) (pk : PK) (z : Z) (st : SimStateF M C R K Hash Z) (m : M)
    (k : K) (hs : selK P f sk pk m = false) :
    table P f sk pk z { st with LQ := Function.update st.LQ m (some k) } =
      { table P f sk pk z st with TK := Function.update (table P f sk pk z st).TK m (some k) } := by
  simp only [table, SplitTab.mk.injEq]
  refine ⟨funext fun m' => ?_, trivial, trivial⟩
  by_cases hm : m' = m
  · subst hm; simp [hs]
  · simp [Function.update_of_ne hm]

omit [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] [Nonempty R] [Nonempty K] [Fintype R]
  [Fintype K] in
theorem table_updateLO (sk : SK) (pk : PK) (z : Z) (st : SimStateF M C R K Hash Z)
    (q : M × Hash) (kr : K × R) :
    table P f sk pk z { st with LO := Function.update st.LO q (some kr) } =
      { table P f sk pk z st with LO := Function.update (table P f sk pk z st).LO q (some kr) } :=
  rfl

omit [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] [Nonempty R] [Nonempty K] [Fintype R]
  [Fintype K] [DecidableEq Hash] in
theorem table_updateLJ (sk : SK) (pk : PK) (z : Z) (st : SimStateF M C R K Hash Z) (q : Z × C)
    (k : K) (hs : selJ P f sk pk z q = false) :
    table P f sk pk z { st with LJ := Function.update st.LJ q (some k) } =
      { table P f sk pk z st with TJ := Function.update (table P f sk pk z st).TJ q (some k) } := by
  simp only [table, SplitTab.mk.injEq]
  refine ⟨trivial, trivial, funext fun q' => ?_⟩
  by_cases hq : q' = q
  · subst hq; simp [hs]
  · simp [Function.update_of_ne hq]

omit [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] [Nonempty R] [Nonempty K] [Fintype R]
  [Fintype K] [DecidableEq Hash] in
theorem table_init (sk : SK) (pk : PK) (z : Z) :
    table P f sk pk z (SimStateF.init : SimStateF M C R K Hash Z) = SplitTab.empty := by
  simp only [table, SimStateF.init, SplitTab.empty, SplitTab.mk.injEq]
  refine ⟨funext fun m => ?_, trivial, funext fun q => ?_⟩ <;> split_ifs <;> rfl

omit [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] [Nonempty R] [Nonempty K] [Fintype R]
  [Fintype K] [DecidableEq Hash] [DecidableEq Z] [DecidableEq M] in
theorem validB_eq_false_of_dec_none (sk : SK) (pk : PK) (c : C) (hd : P.dec sk c = none) :
    validB P f sk pk c = false := by
  simp [validB, fixedT, hd]

omit [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] [Nonempty R] [Nonempty K] [Fintype R]
  [Fintype K] [DecidableEq Hash] [DecidableEq Z] [DecidableEq M] in
theorem validB_eq_false_of_dec_some (sk : SK) (pk : PK) (c : C) (m : M) (hd : P.dec sk c = some m)
    (he : cOf P f pk m ≠ c) : validB P f sk pk c = false := by
  have he' : P.enc pk m (f m) ≠ c := he
  simp [validB, fixedT, hd, he']

omit [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] [Nonempty R] [Nonempty K] [Fintype R]
  [Fintype K] [DecidableEq Hash] [DecidableEq M] in
theorem selJ_eq_true_iff (sk : SK) (pk : PK) (z : Z) (q : Z × C) :
    selJ P f sk pk z q = true ↔ q.1 = z ∧ validB P f sk pk q.2 = false := by
  simp [selJ]

omit [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] [Nonempty R] [Nonempty K] [DecidableEq C]
  [DecidableEq M] [DecidableEq Hash] [DecidableEq Z] [Fintype R] [Fintype K] in
/-- Two lazy reads with the same value and related updates give the same
distribution after mapping the state. -/
theorem roOracle_map_eq {I I' V S S' A : Type} [DecidableEq I] [DecidableEq I'] [Fintype V]
    [Nonempty V] (tab : I → Option V) (i : I) (tab' : I' → Option V) (i' : I')
    (F : V × (I → Option V) → A × S) (F' : V × (I' → Option V) → A × S') (φ : S → S')
    (hread : tab' i' = tab i) (h0 : ∀ v, Prod.map id φ (F (v, tab)) = F' (v, tab'))
    (h1 : ∀ v, Prod.map id φ (F (v, Function.update tab i (some v))) =
      F' (v, Function.update tab' i' (some v))) :
    ((roOracle tab i).map F).map (Prod.map id φ) = (roOracle tab' i').map F' := by
  unfold roOracle
  rw [hread]
  cases tab i with
  | some v => simp [PMF.pure_map, h0]
  | none =>
    simp only [PMF.map_comp, Function.comp_def]
    exact congrArg (fun F => PMF.map F _) (funext h1)

omit [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] in
/-- Forgetting the ghost state and reading the tables maps the re-indexed oracle with
the selectors `selK` and `selJ` to the flagged split oracle, when `c*` decrypts to
`m*`. -/
theorem oSim_map_table (sk : SK) (pk : PK) (z : Z) (mstar : M) (v : K)
    (hdec : P.dec sk (cOf P f pk mstar) = some mstar) {G : Type} (upd : Z → G → G)
    (x : SimStateF M C R K Hash Z × G) (d : ((M × Hash) ⊕ (Z × C)) ⊕ C) :
    (oSim P hpk f upd (selK P f sk pk) (selJ P f sk pk z) pk (cOf P f pk mstar) v x d).map
        (Prod.map id fun y => (table P f sk pk z y.1, y.1.found.isSome)) =
      oSplit P hpk f sk pk z mstar v (table P f sk pk z x.1, x.1.found.isSome) d := by
  obtain ⟨st, g⟩ := x
  rcases d with (⟨m, h⟩ | q) | c
  · by_cases hh : h = hpk pk
    · subst hh
      by_cases hm : m = mstar
      · subst hm
        have hs : selK P f sk pk m = true := selK_of_dec P f sk pk m _ hdec rfl
        simp [oSim, oSplit, hs, PMF.pure_map, table]
      · simp only [oSim, oSplit, if_true, hm, if_false]
        by_cases hs : selK P f sk pk m = true
        · have hne : cOf P f pk m ≠ cOf P f pk mstar := by
            intro he
            simp only [selK, he, hdec, Option.some.injEq, decide_eq_true_eq] at hs
            exact hm hs.symm
          simp only [hs, if_true, hne, if_false]
          rw [lazyRead_eq]
          refine roOracle_map_eq _ _ _ _ _ _ _ ?_ ?_ ?_
          · simp [table, hs]
          · intro k; rfl
          · intro k
            simp only [Prod.map_apply, id]
            rw [table_updateLD_of_valid P f sk pk z st _ m k (by simpa [selK] using hs) rfl]
        · simp only [hs, Bool.false_eq_true, if_false]
          rw [lazyRead_eq]
          refine roOracle_map_eq _ _ _ _ _ _ _ ?_ ?_ ?_
          · simp [table, hs]
          · intro k; rfl
          · intro k
            simp only [Prod.map_apply, id]
            rw [table_updateLQ P f sk pk z st m k (by simpa using hs)]
    · simp only [oSim, oSplit, hh, if_false]
      rw [lazyRead_eq]
      exact roOracle_map_eq _ _ _ _ _ _ _ rfl (fun _ => rfl) (fun _ => rfl)
  · by_cases hs : selJ P f sk pk z q = true
    · obtain ⟨hz, hv⟩ := (selJ_eq_true_iff P f sk pk z q).mp hs
      simp only [oSim, oSplit, hs, if_true]
      rw [lazyRead_eq]
      refine roOracle_map_eq _ _ _ _ _ _ _ ?_ ?_ ?_
      · simp [table, hs]
      · intro k; rfl
      · intro k
        simp only [Prod.map_apply, id]
        rw [table_updateLD_of_invalid P f sk pk z st _ k hv, ← hz]
    · simp only [oSim, oSplit, hs, Bool.false_eq_true, if_false]
      rw [lazyRead_eq]
      refine roOracle_map_eq _ _ _ _ _ _ _ ?_ ?_ ?_
      · simp [table, hs]
      · intro k; rfl
      · intro k
        simp only [Prod.map_apply, id]
        rw [table_updateLJ P f sk pk z st q k (by simpa using hs)]
  · by_cases hc : c = cOf P f pk mstar
    · subst hc
      simp [oSim, oSplit, PMF.pure_map]
    · simp only [oSim, oSplit, hc, if_false]
      rw [lazyRead_eq]
      have hj : ∀ hv : validB P f sk pk c = false,
          ((roOracle st.LD c).map fun y =>
            ((Sum.inr (some y.1) : ((K × R) ⊕ K) ⊕ Option K), ({ st with LD := y.2 }, g))).map
              (Prod.map id fun y => (table P f sk pk z y.1, y.1.found.isSome)) =
            jSplit (table P f sk pk z st, st.found.isSome) (z, c) := by
        intro hv
        have hsj : selJ P f sk pk z (z, c) = true := (selJ_eq_true_iff P f sk pk z (z, c)).mpr ⟨rfl, hv⟩
        unfold jSplit
        refine roOracle_map_eq _ _ _ _ _ _ _ ?_ ?_ ?_
        · simp [table, hsj]
        · intro k; rfl
        · intro k
          simp only [Prod.map_apply, id]
          rw [table_updateLD_of_invalid P f sk pk z st c k hv]
      rcases hd : P.dec sk c with _ | m
      · exact hj (validB_eq_false_of_dec_none P f sk pk c hd)
      · dsimp only
        by_cases hm : m = mstar
        · subst hm
          rw [if_pos rfl]
          exact hj (validB_eq_false_of_dec_some P f sk pk c m hd (Ne.symm hc))
        · rw [if_neg hm]
          by_cases he : cOf P f pk m = c
          · rw [if_pos he]
            have hs : selK P f sk pk m = true := selK_of_dec P f sk pk m c hd he
            refine roOracle_map_eq _ _ _ _ _ _ _ ?_ ?_ ?_
            · simp [table, hs, he]
            · intro k; rfl
            · intro k
              simp only [Prod.map_apply, id]
              rw [table_updateLD_of_valid P f sk pk z st c m k hd he]
          · rw [if_neg he]
            exact hj (validB_eq_false_of_dec_some P f sk pk c m hd he)

end Split

/-! ## Replacing the selector of `J` -/

section SelectorJ

variable [DecidableEq M] [DecidableEq Hash] [DecidableEq Z] [Fintype R] [Fintype K]
variable (P : Scheme PK SK M C R) (hpk : PK → Hash) (f : M → R)

/-- The ghost update recording whether a `J`-query with prefix `z` was made. -/
def badUpd (z z' : Z) (b : Bool) : Bool := b || decide (z' = z)

omit [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] in
/-- A map of ghost states that commutes with the ghost updates commutes with the
re-indexed oracle. -/
theorem oSim_map_ghost {G G' : Type} (upd : Z → G → G) (upd' : Z → G' → G') (φ : G → G')
    (hφ : ∀ z g, φ (upd z g) = upd' z (φ g)) (sK : M → Bool) (sJ : Z × C → Bool) (pk : PK)
    (cstar : C) (v : K) (x : SimStateF M C R K Hash Z × G) (d : ((M × Hash) ⊕ (Z × C)) ⊕ C) :
    (oSim P hpk f upd sK sJ pk cstar v x d).map (Prod.map id (Prod.map id φ)) =
      oSim P hpk f upd' sK sJ pk cstar v (x.1, φ x.2) d := by
  rcases d with (q | q) | c
  · simp only [oSim]
    split_ifs <;> simp [PMF.pure_map, lazyRead_map_ghost]
  · simp only [oSim]
    split_ifs <;> simp [lazyRead_map_ghost, hφ]
  · simp only [oSim]
    split_ifs
    · simp only [PMF.pure_map]; rfl
    · simp [lazyRead_map_ghost]

omit [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] in
theorem oSim_bad_apply_true_false (z : Z) (sK : M → Bool) (sJ : Z × C → Bool) (pk : PK)
    (cstar : C) (v : K) (st : SimStateF M C R K Hash Z) (d : ((M × Hash) ⊕ (Z × C)) ⊕ C)
    (a : ((K × R) ⊕ K) ⊕ Option K) (st' : SimStateF M C R K Hash Z) :
    oSim P hpk f (badUpd z) sK sJ pk cstar v (st, true) d (a, (st', false)) = 0 := by
  rcases d with (q | q) | c
  · simp only [oSim]
    split_ifs
    · simp [PMF.pure_apply]
    all_goals exact lazyRead_apply_ghost_ne _ _ _ _ _ _ _ _ (by decide)
  · simp only [oSim, badUpd, Bool.true_or]
    split_ifs
    all_goals exact lazyRead_apply_ghost_ne _ _ _ _ _ _ _ _ (by decide)
  · simp only [oSim]
    split_ifs
    · simp [PMF.pure_apply]
    · exact lazyRead_apply_ghost_ne _ _ _ _ _ _ _ _ (by decide)

omit [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] in
/-- Two selectors of `J` agreeing on prefixes other than `z` give oracles agreeing on
every unflagged transition. -/
theorem oSim_bad_apply_false_eq (z : Z) (sK : M → Bool) (sJ sJ' : Z × C → Bool)
    (hsel : ∀ q : Z × C, q.1 ≠ z → sJ q = sJ' q) (pk : PK) (cstar : C) (v : K)
    (x : SimStateF M C R K Hash Z × Bool) (d : ((M × Hash) ⊕ (Z × C)) ⊕ C)
    (a : ((K × R) ⊕ K) ⊕ Option K) (st' : SimStateF M C R K Hash Z) :
    oSim P hpk f (badUpd z) sK sJ pk cstar v x d (a, (st', false)) =
      oSim P hpk f (badUpd z) sK sJ' pk cstar v x d (a, (st', false)) := by
  rcases d with (q | q) | c
  · rfl
  · by_cases hq : q.1 = z
    · have hb : badUpd z q.1 x.2 = true := by simp [badUpd, hq]
      have hz : ∀ s : Z × C → Bool,
          oSim P hpk f (badUpd z) sK s pk cstar v x (.inl (.inr q)) (a, (st', false)) = 0 := by
        intro s
        simp only [oSim, hb]
        split_ifs
        all_goals exact lazyRead_apply_ghost_ne _ _ _ _ _ _ _ _ (by decide)
      rw [hz, hz]
    · simp only [oSim, hsel q hq]
  · rfl

/-- The key of a query: the prefix of a `J`-query. -/
def keyJ : ((M × Hash) ⊕ (Z × C)) ⊕ C → Option Z
  | .inl (.inr q) => some q.1
  | _ => none

/-- The re-indexed oracle without ghost state. -/
noncomputable def oSimU (sK : M → Bool) (sJ : Z × C → Bool) (pk : PK) (cstar : C) (v : K)
    (st : SimStateF M C R K Hash Z) (d : ((M × Hash) ⊕ (Z × C)) ⊕ C) :
    PMF ((((K × R) ⊕ K) ⊕ Option K) × SimStateF M C R K Hash Z) :=
  (oSim P hpk f (fun _ _ => ()) sK sJ pk cstar v (st, ()) d).map fun y => (y.1, y.2.1)

omit [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] in
/-- The re-indexed oracle with a log of the prefixes of `J`-queries is the logged
oracle. -/
theorem oSim_cons_eq_logged (sK : M → Bool) (sJ : Z × C → Bool) (pk : PK) (cstar : C) (v : K)
    (x : SimStateF M C R K Hash Z × List Z) (d : ((M × Hash) ⊕ (Z × C)) ⊕ C) :
    oSim P hpk f List.cons sK sJ pk cstar v x d = logged (oSimU P hpk f sK sJ pk cstar v) keyJ x d := by
  obtain ⟨st, l⟩ := x
  rcases d with (q | q) | c
  · simp only [oSim, logged, oSimU, keyJ, PMF.map_comp, Function.comp_def, Option.toList,
      List.nil_append]
    split_ifs <;> simp [PMF.pure_map, lazyRead_map_const]
  · simp only [oSim, logged, oSimU, keyJ, PMF.map_comp, Function.comp_def, Option.toList,
      List.singleton_append]
    split_ifs <;> simp [lazyRead_map_const]
  · simp only [oSim, logged, oSimU, keyJ, PMF.map_comp, Function.comp_def, Option.toList,
      List.nil_append]
    split_ifs <;> simp [PMF.pure_map, lazyRead_map_const]

omit [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] in
/-- The bad-flag run is the log run with the flag read as membership of `z`. -/
theorem run_oSim_bad_eq {α : Type} (z : Z) (sK : M → Bool) (sJ : Z × C → Bool) (pk : PK)
    (cstar : C) (v : K) (A : OracleAdv (((M × Hash) ⊕ (Z × C)) ⊕ C) (((K × R) ⊕ K) ⊕ Option K) α)
    (st : SimStateF M C R K Hash Z) :
    OracleAdv.run (oSim P hpk f (badUpd z) sK sJ pk cstar v) A (st, false) =
      (OracleAdv.run (logged (oSimU P hpk f sK sJ pk cstar v) keyJ) A (st, [])).map
        (Prod.map id (Prod.map id fun l => decide (z ∈ l))) := by
  have h := OracleAdv.run_map_state (oSim P hpk f List.cons sK sJ pk cstar v)
    (oSim P hpk f (badUpd z) sK sJ pk cstar v) (Prod.map id fun l => decide (z ∈ l))
    (fun x d => oSim_map_ghost P hpk f List.cons (badUpd z) _
      (fun z' l => by simp [badUpd, List.mem_cons, eq_comm, Bool.or_comm]) sK sJ pk cstar v x d)
    A (st, [])
  have e : oSim P hpk f List.cons sK sJ pk cstar v = logged (oSimU P hpk f sK sJ pk cstar v) keyJ :=
    funext fun x => funext fun d => oSim_cons_eq_logged P hpk f sK sJ pk cstar v x d
  rw [← e]
  simpa using h.symm

omit [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] [Nonempty R] [Nonempty K] [DecidableEq C]
  [DecidableEq M] [DecidableEq Hash] [DecidableEq Z] [Fintype R] [Fintype K] in
/-- A query bound for a cost dominates the bound for a smaller cost. -/
theorem isQueryBoundBy_of_cost_le {D A α : Type} {cost cost' : D → ℕ} (hc : ∀ d, cost' d ≤ cost d)
    {B : OracleAdv D A α} {n : ℕ} (hB : B.IsQueryBoundBy cost n) : B.IsQueryBoundBy cost' n := by
  induction B generalizing n with
  | ret a => trivial
  | rand p k ih => exact fun b => ih b (hB b)
  | query d k ih =>
    obtain ⟨hle, hk⟩ := hB
    exact ⟨(hc d).trans hle, fun r => (ih r (hk r)).mono (by have := hc d; omega)⟩

omit [Fintype M] [Nonempty M] in
/-- **Guessing the seed.** Averaged over a uniform seed `z`, a run with at most `n`
random-oracle queries makes a `J`-query with prefix `z` with probability at most
`n / |Z|`. -/
theorem tsum_bad_le {α : Type} (sK : M → Bool) (sJ : Z × C → Bool) (pk : PK) (cstar : C) (v : K)
    (A : OracleAdv (((M × Hash) ⊕ (Z × C)) ⊕ C) (((K × R) ⊕ K) ⊕ Option K) α) (n : ℕ)
    (hA : A.IsQueryBoundBy (Sum.elim (fun _ => 1) fun _ => 0) n) :
    ∑' z, PMF.uniformOfFintype Z z *
      (OracleAdv.run (oSim P hpk f (badUpd z) sK sJ pk cstar v) A (SimStateF.init, false)).toOuterMeasure
        {y | y.2.2 = true} ≤ (n : ℝ≥0∞) / Fintype.card Z := by
  have hA' : A.IsQueryBoundBy (keyCost keyJ) n :=
    isQueryBoundBy_of_cost_le (fun d => by rcases d with (q | q) | c <;> simp [keyCost, keyJ]) hA
  refine (le_of_eq (tsum_congr fun z => congrArg _ ?_)).trans
    (tsum_uniform_mem_log_le (oSimU P hpk f sK sJ pk cstar v) keyJ A n hA' SimStateF.init)
  rw [run_oSim_bad_eq, PMF.toOuterMeasure_map_apply]
  congr 1
  ext y
  simp

end SelectorJ

/-! ## The simulation with a fixed derandomiser -/

section Simulation

variable [DecidableEq M] [DecidableEq Hash] [DecidableEq Z] [Fintype R] [Fintype K]
variable (P : Scheme PK SK M C R) (hpk : PK → Hash) (f : M → R)

/-- The simulation of `G`, `J` and decapsulation by the OW-PCA adversary against
`fixedT P f`, from the challenge `c*` and the key `k*`: as `simImplF`, with the coins
of a `G`-query at prefix `hpk pk` given by `f`. -/
noncomputable def simImplFix (pk : PK) (cstar : C) (kstar : K) (st : SimStateF M C R K Hash Z) :
    ((M × Hash) ⊕ (Z × C)) ⊕ C →
      OracleAdv (M × C) Bool ((((K × R) ⊕ K) ⊕ Option K) × SimStateF M C R K Hash Z)
  | .inl (.inl q) =>
    if q.2 = hpk pk then
      .query (q.1, cOf P f pk q.1) fun b =>
        if b then
          (if cOf P f pk q.1 = cstar then
            .ret (.inl (.inl (kstar, f q.1)), { st with found := some q.1 })
           else lazyTab st.LD (cOf P f pk q.1) (fun t => { st with LD := t })
            fun k => .inl (.inl (k, f q.1)))
        else lazyTab st.LQ q.1 (fun t => { st with LQ := t }) fun k => .inl (.inl (k, f q.1))
    else lazyTab st.LO q (fun t => { st with LO := t }) fun kr => .inl (.inl kr)
  | .inl (.inr q) => lazyTab st.LJ q (fun t => { st with LJ := t }) fun k => .inl (.inr k)
  | .inr c => if c = cstar then .ret (.inr none, st) else
      lazyTab st.LD c (fun t => { st with LD := t }) fun k => .inr (some k)

omit [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] [Nonempty R] [Nonempty K] [DecidableEq C]
  [DecidableEq M] [DecidableEq Hash] [DecidableEq Z] [Fintype R] [Fintype K] in
theorem isQueryBound_lazyTab {D' R' I V S A : Type} [DecidableEq I] [Fintype V] [Nonempty V]
    (tab : I → Option V) (i : I) (set : (I → Option V) → S) (w : V → A) (n : ℕ) :
    (lazyTab (D' := D') (R' := R') tab i set w).IsQueryBound n := by
  unfold lazyTab; split
  · trivial
  · exact fun _ => trivial

omit [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] in
theorem isQueryBound_simImplFix (pk : PK) (cstar : C) (kstar : K) (st : SimStateF M C R K Hash Z)
    (d : ((M × Hash) ⊕ (Z × C)) ⊕ C) :
    (simImplFix P hpk f pk cstar kstar st d).IsQueryBound (Sum.elim (fun _ => 1) (fun _ => 0) d) := by
  rcases d with (q | q) | c
  · simp only [simImplFix, Sum.elim_inl]
    by_cases hh : q.2 = hpk pk
    · rw [if_pos hh]
      intro b
      dsimp only
      by_cases hb : b = true
      · rw [if_pos hb]
        by_cases hc : cOf P f pk q.1 = cstar
        · rw [if_pos hc]; trivial
        · rw [if_neg hc]; apply isQueryBound_lazyTab
      · rw [if_neg hb]; apply isQueryBound_lazyTab
    · rw [if_neg hh]; apply isQueryBound_lazyTab
  · simp only [simImplFix, Sum.elim_inl]
    apply isQueryBound_lazyTab
  · simp only [simImplFix, Sum.elim_inr]
    by_cases hc : c = cstar
    · rw [if_pos hc]; trivial
    · rw [if_neg hc]; apply isQueryBound_lazyTab

/-- The OW-PCA adversary against `fixedT P f` built from an IND-CCA adversary `B`
against `fips203 P hpk`, with the coins at prefix `hpk pk` given by `f`. -/
noncomputable def redFix {qRO qD : ℕ}
    (B : ROM2INDCCAAdversary PK K C (M × Hash) (K × R) (Z × C) K qRO qD) :
    OWPCAAdversary PK M C qRO where
  run pk cstar := .rand (PMF.uniformOfFintype K) fun kstar =>
    (OracleAdv.simulate (simImplFix P hpk f pk cstar kstar) (B.run pk cstar kstar)
      SimStateF.init).bind fun x => .ret (x.2.found.getD (Classical.arbitrary M))
  isQueryBound pk cstar kstar := by
    have h := OracleAdv.isQueryBound_bind
      (OracleAdv.isQueryBound_simulate (simImplFix P hpk f pk cstar kstar) _
        (isQueryBound_simImplFix P hpk f pk cstar kstar) (B.isQueryBoundRO pk cstar kstar)
        SimStateF.init)
      (f := fun x => .ret (x.2.found.getD (Classical.arbitrary M))) (n := 0) fun _ => trivial
    simpa using h

omit [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] [Nonempty R] [Nonempty K] [DecidableEq Hash]
  [DecidableEq Z] [Fintype R] [Fintype K] in
/-- The plaintext-checking answer of `fixedT P f` on `(m, cOf f pk m)` is `selK`. -/
theorem pco_fixedT_cOf (sk : SK) (pk : PK) (m : M) :
    (fixedT P f).pco (pk, sk) m (cOf P f pk m) = selK P f sk pk m := by
  simp only [Scheme.pco, fixedT, selK, cOf]
  refine decide_eq_decide.mpr ?_
  cases hd : P.dec sk (P.enc pk m (f m)) with
  | none => simp
  | some m' =>
    by_cases hm : m' = m
    · subst hm; simp
    · simp [hm]

omit [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] in
/-- The composite oracle of the reduction is the re-indexed oracle with the selectors
`selK` and `false`. -/
theorem simOracle_eq_oSim (sk : SK) (pk : PK) (cstar : C) (v : K)
    (x : SimStateF M C R K Hash Z × Unit) (d : ((M × Hash) ⊕ (Z × C)) ⊕ C) :
    OracleAdv.simOracle (simImplFix P hpk f pk cstar v) (pcoOracle (fixedT P f) (pk, sk)) x d =
      oSim P hpk f (fun _ _ => ()) (selK P f sk pk) (fun _ => false) pk cstar v x d := by
  obtain ⟨st, u⟩ := x
  rcases d with (q | q) | c
  · simp only [OracleAdv.simOracle, simImplFix, oSim]
    by_cases hh : q.2 = hpk pk
    · simp only [hh, if_true, OracleAdv.run_query, pcoOracle, PMF.pure_bind, pco_fixedT_cOf]
      by_cases hs : selK P f sk pk q.1 = true
      · simp only [hs, if_true]
        by_cases hc : cOf P f pk q.1 = cstar
        · simp [hc, PMF.pure_map]
        · simp only [hc, if_false]
          exact run_lazyTab _ _ _ _ _ _
      · simp only [hs, Bool.false_eq_true, if_false]
        exact run_lazyTab _ _ _ _ _ _
    · simp only [hh, if_false]
      exact run_lazyTab _ _ _ _ _ _
  · simp only [OracleAdv.simOracle, simImplFix, oSim, Bool.false_eq_true, if_false]
    exact run_lazyTab _ _ _ _ _ _
  · simp only [OracleAdv.simOracle, simImplFix, oSim]
    split_ifs
    · simp [PMF.pure_map]
    · exact run_lazyTab _ _ _ _ _ _

omit [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] [Nonempty R] [Nonempty K] [DecidableEq C]
  [DecidableEq M] [DecidableEq Hash] [DecidableEq Z] [Fintype R] [Fintype K] in
theorem found_of_mem_support_lazyRead {I V G A : Type} [DecidableEq I] [Fintype V] [Nonempty V]
    {tab : I → Option V} {i : I} {set : (I → Option V) → SimStateF M C R K Hash Z} {w : V → A}
    {g : G} (hset : ∀ t, (set t).found = (set tab).found) {x : A × (SimStateF M C R K Hash Z × G)}
    (hx : x ∈ (lazyRead tab i set w g).support) : x.2.1.found = (set tab).found := by
  unfold lazyRead at hx; split at hx
  · simp only [PMF.support_pure, Set.mem_singleton_iff] at hx; subst hx; rfl
  · simp only [PMF.support_map, Set.mem_image] at hx
    obtain ⟨k, _, rfl⟩ := hx
    exact hset _

/-- A found message decrypts the challenge under `fixedT P f`. -/
def FoundValid (sk : SK) (pk : PK) (cstar : C) (st : SimStateF M C R K Hash Z) : Prop :=
  ∀ m, st.found = some m → (fixedT P f).pco (pk, sk) m cstar = true

omit [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] in
/-- On every outcome of a run of the re-indexed oracle with the selector `selK` from
the initial state, a found message decrypts the challenge. -/
theorem foundValid_of_mem_support {G α : Type} (upd : Z → G → G) (sJ : Z × C → Bool) (sk : SK)
    (pk : PK) (cstar : C) (v : K)
    (A : OracleAdv (((M × Hash) ⊕ (Z × C)) ⊕ C) (((K × R) ⊕ K) ⊕ Option K) α) (g : G)
    (y : α × (SimStateF M C R K Hash Z × G))
    (hy : y ∈ (OracleAdv.run (oSim P hpk f upd (selK P f sk pk) sJ pk cstar v) A
      (SimStateF.init, g)).support) :
    FoundValid P f sk pk cstar y.2.1 := by
  have h := Constructions.ECBCPRF.run_support_rel (oSim P hpk f upd (selK P f sk pk) sJ pk cstar v)
    (fun a b => FoundValid P f sk pk cstar a.1 → FoundValid P f sk pk cstar b.1) (fun _ h => h)
    (fun _ _ _ h₁ h₂ h => h₂ (h₁ h)) ?_ A (SimStateF.init, g) y hy
  · exact h fun m hm => by simp [SimStateF.init] at hm
  · intro x d z hz hx
    rcases d with (q | q) | c
    · simp only [oSim] at hz
      split_ifs at hz with hh hs hc
      · simp only [PMF.support_pure, Set.mem_singleton_iff] at hz
        subst hz
        intro m hm
        simp only [Option.some.injEq] at hm
        subst hm
        rw [← hc, pco_fixedT_cOf]
        exact hs
      all_goals
        intro m hm
        rw [found_of_mem_support_lazyRead (fun _ => rfl) hz] at hm
        exact hx m hm
    · simp only [oSim] at hz
      split_ifs at hz
      all_goals
        intro m hm
        rw [found_of_mem_support_lazyRead (fun _ => rfl) hz] at hm
        exact hx m hm
    · simp only [oSim] at hz
      split_ifs at hz
      · simp only [PMF.support_pure, Set.mem_singleton_iff] at hz; subst hz; exact hx
      · intro m hm
        rw [found_of_mem_support_lazyRead (fun _ => rfl) hz] at hm
        exact hx m hm

omit [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] in
/-- The composite oracle of the reduction against `fixedT P f`, as an oracle. -/
theorem simOracle_simImplFix_eq (sk : SK) (pk : PK) (cstar : C) (v : K) :
    OracleAdv.simOracle (S := SimStateF M C R K Hash Z) (U := Unit)
        (simImplFix P hpk f pk cstar v) (pcoOracle (fixedT P f) (pk, sk)) =
      oSim (G := Unit) P hpk f (fun _ _ => ()) (selK P f sk pk) (fun _ => false) pk cstar v :=
  funext fun x => funext fun d => simOracle_eq_oSim P hpk f sk pk cstar v x d

omit [Fintype M] [Fintype Z] [Nonempty Z] in
/-- **Per-draw bound.** For a fixed draw and derandomiser `f`, the probability that
the flagged split run hits the challenge point is at most the indicator of a
decryption failure of the challenge, plus the probability that the simulation finds a
message decrypting the challenge, plus the probability that the adversary makes a
`J`-query with prefix `z`. -/
theorem flag_le (sk : SK) (pk : PK) (z : Z) (mstar : M) (v : K)
    (A : OracleAdv (((M × Hash) ⊕ (Z × C)) ⊕ C) (((K × R) ⊕ K) ⊕ Option K) Bool) :
    (OracleAdv.run (oSplit P hpk f sk pk z mstar v) A (SplitTab.empty, false)).toOuterMeasure
        {y | y.2.2 = true} ≤
      FOTransformU.failInd P sk mstar (cOf P f pk mstar) +
      (OracleAdv.run (OracleAdv.simOracle (simImplFix P hpk f pk (cOf P f pk mstar) v)
        (pcoOracle (fixedT P f) (pk, sk))) A (SimStateF.init, ())).toOuterMeasure
          {y | (fixedT P f).pco (pk, sk) (y.2.1.found.getD (Classical.arbitrary M))
            (cOf P f pk mstar) = true} +
      (OracleAdv.run (oSim P hpk f (badUpd z) (selK P f sk pk) (fun _ => false) pk
        (cOf P f pk mstar) v) A (SimStateF.init, false)).toOuterMeasure {y | y.2.2 = true} := by
  by_cases hdec : P.dec sk (cOf P f pk mstar) = some mstar
  swap
  · simp only [FOTransformU.failInd, hdec, if_false]
    exact (le_self_add.trans_eq (Constructions.ECBCPRF.toOuterMeasure_add_compl _ _)).trans
      (le_add_right le_self_add)
  simp only [FOTransformU.failInd, hdec, if_true, zero_add]
  have h1 : (OracleAdv.run (oSplit P hpk f sk pk z mstar v) A (SplitTab.empty, false)).toOuterMeasure
      {y | y.2.2 = true} =
      (OracleAdv.run (oSim P hpk f (badUpd z) (selK P f sk pk) (selJ P f sk pk z) pk
        (cOf P f pk mstar) v) A (SimStateF.init, false)).toOuterMeasure
          {y | y.2.1.found.isSome = true} := by
    have h := OracleAdv.run_map_state
      (oSim P hpk f (badUpd z) (selK P f sk pk) (selJ P f sk pk z) pk (cOf P f pk mstar) v)
      (oSplit P hpk f sk pk z mstar v) (fun y => (table P f sk pk z y.1, y.1.found.isSome))
      (fun x d => oSim_map_table P hpk f sk pk z mstar v hdec (badUpd z) x d) A
      (SimStateF.init, false)
    simp only [table_init] at h
    rw [show ((SimStateF.init : SimStateF M C R K Hash Z).found.isSome) = false from rfl] at h
    rw [← h, PMF.toOuterMeasure_map_apply]
    rfl
  have h2 := FOTransformU.toOuterMeasure_le_add_flag_set
    (OracleAdv.run (oSim P hpk f (badUpd z) (selK P f sk pk) (selJ P f sk pk z) pk
      (cOf P f pk mstar) v) A (SimStateF.init, false))
    (OracleAdv.run (oSim P hpk f (badUpd z) (selK P f sk pk) (fun _ => false) pk
      (cOf P f pk mstar) v) A (SimStateF.init, false))
    (fun a t => OracleAdv.run_apply_flag_false_eq _ _
      (oSim_bad_apply_true_false P hpk f z _ _ pk _ v)
      (oSim_bad_apply_true_false P hpk f z _ _ pk _ v)
      (fun x d r t' => oSim_bad_apply_false_eq P hpk f z _ _ _
        (fun q hq => by simp [selJ, hq]) pk _ v x d r t') A _ a t)
    {y | y.2.1.found.isSome = true}
  have h3 : (OracleAdv.run (oSim P hpk f (badUpd z) (selK P f sk pk) (fun _ => false) pk
        (cOf P f pk mstar) v) A (SimStateF.init, false)).toOuterMeasure
          {y | y.2.1.found.isSome = true} =
      (OracleAdv.run (OracleAdv.simOracle (simImplFix P hpk f pk (cOf P f pk mstar) v)
        (pcoOracle (fixedT P f) (pk, sk))) A (SimStateF.init, ())).toOuterMeasure
          {y | y.2.1.found.isSome = true} := by
    have h := OracleAdv.run_map_state
      (oSim P hpk f (badUpd z) (selK P f sk pk) (fun _ => false) pk (cOf P f pk mstar) v)
      (oSim P hpk f (fun _ _ => ()) (selK P f sk pk) (fun _ => false) pk (cOf P f pk mstar) v)
      (Prod.map id fun _ => ())
      (fun x d => oSim_map_ghost P hpk f (badUpd z) (fun _ _ => ()) (fun _ => ()) (fun _ _ => rfl)
        _ _ pk _ v x d) A (SimStateF.init, false)
    have hs := simOracle_simImplFix_eq (Z := Z) P hpk f sk pk (cOf P f pk mstar) v
    rw [hs, show (SimStateF.init, ()) = Prod.map id (fun _ => ())
      ((SimStateF.init : SimStateF M C R K Hash Z), false) from rfl, ← h,
      PMF.toOuterMeasure_map_apply]
    rfl
  have h4 : (OracleAdv.run (OracleAdv.simOracle (simImplFix P hpk f pk (cOf P f pk mstar) v)
        (pcoOracle (fixedT P f) (pk, sk))) A (SimStateF.init, ())).toOuterMeasure
          {y | y.2.1.found.isSome = true} ≤
      (OracleAdv.run (OracleAdv.simOracle (simImplFix P hpk f pk (cOf P f pk mstar) v)
        (pcoOracle (fixedT P f) (pk, sk))) A (SimStateF.init, ())).toOuterMeasure
          {y | (fixedT P f).pco (pk, sk) (y.2.1.found.getD (Classical.arbitrary M))
            (cOf P f pk mstar) = true} := by
    refine PMF.toOuterMeasure_mono _ fun y ⟨hy, hsupp⟩ => ?_
    have hs := simOracle_simImplFix_eq (Z := Z) P hpk f sk pk (cOf P f pk mstar) v
    rw [hs] at hsupp
    have hv := foundValid_of_mem_support P hpk f (fun _ _ => ()) (fun _ => false) sk pk _ v A ()
      y hsupp
    simp only [Set.mem_ofPred_eq, Option.isSome_iff_exists] at hy ⊢
    obtain ⟨m', hm'⟩ := hy
    rw [hm', Option.getD_some]
    exact hv m' hm'
  rw [h1]
  calc _ ≤ _ := h2
    _ ≤ _ := by rw [h3]; gcongr

end Simulation

/-! ## The eager-sampling hop -/

section Eager

variable [DecidableEq M] [DecidableEq Hash] [DecidableEq Z] [Fintype R] [Fintype K]
variable (P : Scheme PK SK M C R) (hpk : PK → Hash)

/-- The table of `G` assembled from a table of the values at prefix `hpk pk`, indexed
by the message, and a table of the values at the other prefixes. -/
def joinG (pk : PK) (T : M × Hash → Option (K × R)) (U : M → Option (K × R)) :
    M × Hash → Option (K × R) := fun q => if q.2 = hpk pk then U q.1 else T q

/-- The state of the flagged oracle assembled from the state of `progF` and the table
of the coin oracle. -/
def flatF (pk : PK) (x : (Tab M C R K Hash Z × Bool) × (M → Option (K × R))) :
    Tab M C R K Hash Z × Bool := ((joinG hpk pk x.1.1.1 x.2, x.1.1.2), x.1.2)

omit [Fintype M] [Nonempty M] [Nonempty R] [Nonempty K] [Fintype R] [Fintype K] in
theorem joinG_update (pk : PK) (T : M × Hash → Option (K × R)) (U : M → Option (K × R))
    (m : M) (w : K × R) :
    joinG hpk pk T (Function.update U m (some w)) =
      Function.update (joinG hpk pk T U) (m, hpk pk) (some w) := by
  funext q
  obtain ⟨m', h⟩ := q
  by_cases hh : h = hpk pk
  · subst hh
    by_cases hm : m' = m
    · subst hm; simp [joinG]
    · have hne : (m', hpk pk) ≠ (m, hpk pk) := by simp [hm]
      simp [joinG, Function.update_of_ne hm, Function.update_of_ne hne]
  · simp [joinG, hh]

omit [Fintype M] [Nonempty M] [Nonempty R] [Nonempty K] [DecidableEq M] [Fintype R]
  [Fintype K] in
theorem joinG_apply_off (pk : PK) (T : M × Hash → Option (K × R)) (U : M → Option (K × R))
    (q : M × Hash) (hq : q.2 ≠ hpk pk) : joinG hpk pk T U q = T q := by
  simp [joinG, hq]

omit [Fintype M] [Nonempty M] [Nonempty R] [Nonempty K] [DecidableEq M] [Fintype R]
  [Fintype K] in
theorem joinG_apply_on (pk : PK) (T : M × Hash → Option (K × R)) (U : M → Option (K × R))
    (m : M) : joinG hpk pk T U (m, hpk pk) = U m := by
  simp [joinG]

omit [Fintype M] [Nonempty M] [Nonempty R] [Nonempty K] [Fintype R] [Fintype K] in
theorem joinG_update_off (pk : PK) (T : M × Hash → Option (K × R)) (U : M → Option (K × R))
    (q : M × Hash) (hq : q.2 ≠ hpk pk) (w : K × R) :
    joinG hpk pk (Function.update T q (some w)) U =
      Function.update (joinG hpk pk T U) q (some w) := by
  funext q'
  by_cases hq' : q' = q
  · subst hq'; simp [joinG, hq]
  · simp [joinG, Function.update_of_ne hq']

omit [Fintype M] [Nonempty M] [Nonempty R] [Nonempty K] [DecidableEq M] [Fintype R]
  [Fintype K] in
theorem joinG_empty (pk : PK) :
    joinG hpk pk (emptyTable : M × Hash → Option (K × R)) emptyTable = emptyTable := by
  funext q; simp only [joinG]; split_ifs <;> rfl

/-- A read of `J` from the tables of the flagged oracle, as a program on a further
oracle. -/
noncomputable def jProg {D' R' : Type} (s : Tab M C R K Hash Z × Bool) (q : Z × C) :
    OracleAdv D' R' ((((K × R) ⊕ K) ⊕ Option K) × (Tab M C R K Hash Z × Bool)) :=
  lazyTab s.1.2 q (fun t => ((s.1.1, t), s.2)) fun k => .inr (some k)

/-- The flagged oracle as a program on an oracle giving the value of `G` at prefix
`hpk pk`: the values at the other prefixes and those of `J` are sampled locally. -/
noncomputable def progF (sk : SK) (pk : PK) (z : Z) (mstar : M) (rstar : R) (v : K)
    (s : Tab M C R K Hash Z × Bool) :
    ((M × Hash) ⊕ (Z × C)) ⊕ C →
      OracleAdv M (K × R) ((((K × R) ⊕ K) ⊕ Option K) × (Tab M C R K Hash Z × Bool))
  | .inl (.inl q) =>
    if q.2 = hpk pk then
      (if q.1 = mstar then .ret (.inl (.inl (v, rstar)), (s.1, true))
       else .query q.1 fun kr => .ret (.inl (.inl kr), s))
    else lazyTab s.1.1 q (fun t => ((t, s.1.2), s.2)) fun kr => .inl (.inl kr)
  | .inl (.inr q) => lazyTab s.1.2 q (fun t => ((s.1.1, t), s.2)) fun k => .inl (.inr k)
  | .inr c =>
    if c = P.enc pk mstar rstar then .ret (.inr none, s) else
      match P.dec sk c with
      | none => jProg s (z, c)
      | some m =>
        if m = mstar then jProg s (z, c) else
          .query m fun kr =>
            if P.enc pk m kr.2 = c then .ret (.inr (some kr.1), s) else jProg s (z, c)

omit [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] [DecidableEq M] [DecidableEq Hash]
  [DecidableEq Z] [DecidableEq C] [Fintype R] [Fintype K] in
/-- Two lazy reads with the same value and related continuations give the same
distribution after mapping the state. -/
theorem roOracle_bind_eq {I I' V S S' A : Type} [DecidableEq I] [DecidableEq I'] [Fintype V]
    [Nonempty V] (tab : I → Option V) (i : I) (tab' : I' → Option V) (i' : I')
    (F : V × (I → Option V) → PMF (A × S)) (F' : V × (I' → Option V) → PMF (A × S'))
    (φ : S → S') (hread : tab' i' = tab i)
    (h0 : ∀ w, (F (w, tab)).map (Prod.map id φ) = F' (w, tab'))
    (h1 : ∀ w, (F (w, Function.update tab i (some w))).map (Prod.map id φ) =
      F' (w, Function.update tab' i' (some w))) :
    ((roOracle tab i).bind F).map (Prod.map id φ) = (roOracle tab' i').bind F' := by
  unfold roOracle
  rw [hread]
  cases tab i with
  | some w => simp [PMF.pure_bind, h0]
  | none =>
    simp only [PMF.map_bind, PMF.bind_map, Function.comp_def]
    exact congrArg _ (funext h1)

omit [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] in
/-- Assembling the state of `progF` with the table of the coin oracle maps each
transition of the composite oracle to a transition of the flagged oracle. -/
theorem simOracle_progF_map (sk : SK) (pk : PK) (z : Z) (mstar : M) (rstar : R) (v : K)
    (x : (Tab M C R K Hash Z × Bool) × (M → Option (K × R)))
    (d : ((M × Hash) ⊕ (Z × C)) ⊕ C) :
    (OracleAdv.simOracle (progF P hpk sk pk z mstar rstar v) roOracle x d).map
        (Prod.map id (flatF hpk pk)) =
      oFlag P hpk sk pk z mstar rstar v (flatF hpk pk x) d := by
  obtain ⟨s, U⟩ := x
  rcases d with (⟨m, h⟩ | q) | c
  · by_cases hh : h = hpk pk
    · subst hh
      by_cases hm : m = mstar
      · subst hm
        simp [OracleAdv.simOracle, progF, oFlag, flatF, PMF.pure_map]
      · have hq : ((m, hpk pk) : M × Hash) ≠ (mstar, hpk pk) := by simp [hm]
        have hL : OracleAdv.simOracle (progF P hpk sk pk z mstar rstar v) roOracle (s, U)
            (.inl (.inl (m, hpk pk))) =
            (roOracle U m).map fun y =>
              ((Sum.inl (Sum.inl y.1) : (((K × R) ⊕ K) ⊕ Option K)), (s, y.2)) := by
          simp [OracleAdv.simOracle, progF, hm, PMF.map, Function.comp_def]
        rw [hL]
        simp only [oFlag, if_neg hq, flatF]
        refine roOracle_map_eq _ _ _ _ _ _ _ (joinG_apply_on hpk pk _ _ _) (fun _ => rfl)
          (fun w => ?_)
        simp [flatF, joinG_update]
    · have hq : ((m, h) : M × Hash) ≠ (mstar, hpk pk) := by simp [hh]
      have hL : OracleAdv.simOracle (progF P hpk sk pk z mstar rstar v) roOracle (s, U)
          (.inl (.inl (m, h))) =
          lazyRead s.1.1 (m, h) (fun t => ((t, s.1.2), s.2))
            (fun kr => (Sum.inl (Sum.inl kr) : (((K × R) ⊕ K) ⊕ Option K))) U := by
        rw [← run_lazyTab roOracle s.1.1 (m, h) (fun t => ((t, s.1.2), s.2))
          (fun kr => (Sum.inl (Sum.inl kr) : (((K × R) ⊕ K) ⊕ Option K))) U]
        simp only [OracleAdv.simOracle, progF, if_neg hh]
      rw [hL, lazyRead_eq]
      simp only [oFlag, if_neg hq, flatF]
      refine roOracle_map_eq _ _ _ _ _ _ _ (joinG_apply_off hpk pk _ _ _ hh) (fun _ => rfl)
        (fun w => ?_)
      simp only [flatF, Prod.map_apply, id]
      rw [joinG_update_off hpk pk s.1.1 U (m, h) hh w]
  · have hL : OracleAdv.simOracle (progF P hpk sk pk z mstar rstar v) roOracle (s, U)
        (.inl (.inr q)) =
        lazyRead s.1.2 q (fun t => ((s.1.1, t), s.2))
          (fun k => (Sum.inl (Sum.inr k) : (((K × R) ⊕ K) ⊕ Option K))) U := by
      rw [← run_lazyTab roOracle s.1.2 q (fun t => ((s.1.1, t), s.2))
        (fun k => (Sum.inl (Sum.inr k) : (((K × R) ⊕ K) ⊕ Option K))) U]
      simp only [OracleAdv.simOracle, progF]
    rw [hL, lazyRead_eq]
    simp only [oFlag, flatF]
    exact roOracle_map_eq _ _ _ _ _ _ _ rfl (fun _ => rfl) (fun _ => rfl)
  · have hjR : ∀ U' : M → Option (K × R),
        ((OracleAdv.run roOracle (jProg (D' := M) (R' := K × R) s (z, c)) U').map
            fun y => (y.1.1, (y.1.2, y.2))).map (Prod.map id (flatF hpk pk)) =
          jRead (flatF hpk pk (s, U')).1 (flatF hpk pk (s, U')).2 (z, c) := by
      intro U'
      simp only [jProg]
      rw [run_lazyTab roOracle s.1.2 (z, c) (fun t => ((s.1.1, t), s.2))
        (fun k => (Sum.inr (some k) : (((K × R) ⊕ K) ⊕ Option K))) U', lazyRead_eq]
      simp only [jRead, flatF]
      exact roOracle_map_eq _ _ _ _ _ _ _ rfl (fun _ => rfl) (fun _ => rfl)
    by_cases hc : c = P.enc pk mstar rstar
    · subst hc
      simp [OracleAdv.simOracle, progF, oFlag, flatF, PMF.pure_map]
    · simp only [OracleAdv.simOracle, progF, oFlag, if_neg hc, flatF]
      rcases hd : P.dec sk c with _ | m
      · exact hjR U
      · dsimp only
        by_cases hm : m = mstar
        · subst hm
          rw [if_pos rfl, if_pos rfl]
          exact hjR U
        · rw [if_neg hm, if_neg hm]
          simp only [OracleAdv.run_query]
          rw [PMF.map_bind]
          refine roOracle_bind_eq (V := K × R) U m (joinG hpk pk s.1.1 U) (m, hpk pk) _ _
            (flatF hpk pk) (joinG_apply_on hpk pk _ _ _) (fun w => ?_) (fun w => ?_)
          · by_cases he : P.enc pk m w.2 = c
            · simp [he, flatF, PMF.pure_map]
            · rw [if_neg he, if_neg he]
              exact hjR U
          · by_cases he : P.enc pk m w.2 = c
            · simp [he, flatF, PMF.pure_map, joinG_update]
            · rw [if_neg he, if_neg he]
              simp [hjR (Function.update U m (some w)), flatF, joinG_update]

/-- The state of the split oracle assembled from the state of `progS` and the table of
the key oracle. -/
def flatS (x : (Tab M C R K Hash Z × Bool) × (M → Option K)) : SplitTab M C R K Hash Z × Bool :=
  (⟨x.2, x.1.1.1, x.1.1.2⟩, x.1.2)

/-- The split oracle as a program on an oracle giving the key of `G` at prefix
`hpk pk`: the values at the other prefixes and those of `J` are sampled locally. -/
noncomputable def progS (f : M → R) (sk : SK) (pk : PK) (z : Z) (mstar : M) (v : K)
    (s : Tab M C R K Hash Z × Bool) :
    ((M × Hash) ⊕ (Z × C)) ⊕ C →
      OracleAdv M K ((((K × R) ⊕ K) ⊕ Option K) × (Tab M C R K Hash Z × Bool))
  | .inl (.inl q) =>
    if q.2 = hpk pk then
      (if q.1 = mstar then .ret (.inl (.inl (v, f mstar)), (s.1, true))
       else .query q.1 fun k => .ret (.inl (.inl (k, f q.1)), s))
    else lazyTab s.1.1 q (fun t => ((t, s.1.2), s.2)) fun kr => .inl (.inl kr)
  | .inl (.inr q) => lazyTab s.1.2 q (fun t => ((s.1.1, t), s.2)) fun k => .inl (.inr k)
  | .inr c =>
    if c = cOf P f pk mstar then .ret (.inr none, s) else
      match P.dec sk c with
      | none => jProg s (z, c)
      | some m =>
        if m = mstar then jProg s (z, c) else
          if cOf P f pk m = c then .query m fun k => .ret (.inr (some k), s)
          else jProg s (z, c)

omit [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] in
/-- Assembling the state of `progS` with the table of the key oracle maps each
transition of the composite oracle to a transition of the split oracle. -/
theorem simOracle_progS_map (f : M → R) (sk : SK) (pk : PK) (z : Z) (mstar : M) (v : K)
    (x : (Tab M C R K Hash Z × Bool) × (M → Option K)) (d : ((M × Hash) ⊕ (Z × C)) ⊕ C) :
    (OracleAdv.simOracle (progS P hpk f sk pk z mstar v) roOracle x d).map (Prod.map id flatS) =
      oSplit P hpk f sk pk z mstar v (flatS x) d := by
  obtain ⟨s, U⟩ := x
  rcases d with (⟨m, h⟩ | q) | c
  · by_cases hh : h = hpk pk
    · subst hh
      by_cases hm : m = mstar
      · subst hm
        simp [OracleAdv.simOracle, progS, oSplit, flatS, PMF.pure_map]
      · have hL : OracleAdv.simOracle (progS P hpk f sk pk z mstar v) roOracle (s, U)
            (.inl (.inl (m, hpk pk))) =
            (roOracle U m).map fun y =>
              ((Sum.inl (Sum.inl (y.1, f m)) : (((K × R) ⊕ K) ⊕ Option K)), (s, y.2)) := by
          simp [OracleAdv.simOracle, progS, hm, PMF.map, Function.comp_def]
        rw [hL]
        simp only [oSplit, if_neg hm, flatS]
        exact roOracle_map_eq _ _ _ _ _ _ _ rfl (fun _ => rfl) (fun _ => rfl)
    · have hL : OracleAdv.simOracle (progS P hpk f sk pk z mstar v) roOracle (s, U)
          (.inl (.inl (m, h))) =
          lazyRead s.1.1 (m, h) (fun t => ((t, s.1.2), s.2))
            (fun kr => (Sum.inl (Sum.inl kr) : (((K × R) ⊕ K) ⊕ Option K))) U := by
        rw [← run_lazyTab roOracle s.1.1 (m, h) (fun t => ((t, s.1.2), s.2))
          (fun kr => (Sum.inl (Sum.inl kr) : (((K × R) ⊕ K) ⊕ Option K))) U]
        simp only [OracleAdv.simOracle, progS, if_neg hh]
      rw [hL, lazyRead_eq]
      simp only [oSplit, if_neg hh, flatS]
      exact roOracle_map_eq _ _ _ _ _ _ _ rfl (fun _ => rfl) (fun _ => rfl)
  · have hL : OracleAdv.simOracle (progS P hpk f sk pk z mstar v) roOracle (s, U)
        (.inl (.inr q)) =
        lazyRead s.1.2 q (fun t => ((s.1.1, t), s.2))
          (fun k => (Sum.inl (Sum.inr k) : (((K × R) ⊕ K) ⊕ Option K))) U := by
      rw [← run_lazyTab roOracle s.1.2 q (fun t => ((s.1.1, t), s.2))
        (fun k => (Sum.inl (Sum.inr k) : (((K × R) ⊕ K) ⊕ Option K))) U]
      simp only [OracleAdv.simOracle, progS]
    rw [hL, lazyRead_eq]
    simp only [oSplit, flatS]
    exact roOracle_map_eq _ _ _ _ _ _ _ rfl (fun _ => rfl) (fun _ => rfl)
  · have hjS : ∀ U' : M → Option K,
        ((OracleAdv.run roOracle (jProg (D' := M) (R' := K) s (z, c)) U').map
            fun y => (y.1.1, (y.1.2, y.2))).map (Prod.map id flatS) =
          jSplit (flatS (s, U')) (z, c) := by
      intro U'
      simp only [jProg]
      rw [run_lazyTab roOracle s.1.2 (z, c) (fun t => ((s.1.1, t), s.2))
        (fun k => (Sum.inr (some k) : (((K × R) ⊕ K) ⊕ Option K))) U', lazyRead_eq]
      simp only [jSplit, flatS]
      exact roOracle_map_eq _ _ _ _ _ _ _ rfl (fun _ => rfl) (fun _ => rfl)
    by_cases hc : c = cOf P f pk mstar
    · subst hc
      simp [OracleAdv.simOracle, progS, oSplit, flatS, PMF.pure_map]
    · simp only [OracleAdv.simOracle, progS, oSplit, if_neg hc]
      rcases hd : P.dec sk c with _ | m
      · exact hjS U
      · dsimp only
        by_cases hm : m = mstar
        · subst hm
          rw [if_pos rfl, if_pos rfl]
          exact hjS U
        · rw [if_neg hm, if_neg hm]
          by_cases he : cOf P f pk m = c
          · rw [if_pos he, if_pos he]
            have hL : ((OracleAdv.run roOracle
                (OracleAdv.query (R := K) m fun k =>
                  OracleAdv.ret ((Sum.inr (some k) : (((K × R) ⊕ K) ⊕ Option K)), s)) U).map
                  fun y => (y.1.1, (y.1.2, y.2))) =
                (roOracle U m).map fun y =>
                  ((Sum.inr (some y.1) : (((K × R) ⊕ K) ⊕ Option K)), (s, y.2)) := by
              simp [PMF.map, Function.comp_def]
            rw [hL]
            simp only [flatS]
            exact roOracle_map_eq _ _ _ _ _ _ _ rfl (fun _ => rfl) (fun _ => rfl)
          · rw [if_neg he, if_neg he]
            exact hjS U

omit [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] in
/-- With the values of `G` at prefix `hpk pk` answered by functions, the composite
oracle of `progF` is the composite oracle of `progS`. -/
theorem simOracle_keyed_eq (f : M → R) (g : M → K) (F : M → K × R) (sk : SK) (pk : PK) (z : Z)
    (mstar : M) (rstar : R) (v : K) (hF : ∀ m, m ≠ mstar → F m = (g m, f m))
    (hr : f mstar = rstar) (x : (Tab M C R K Hash Z × Bool) × Unit)
    (d : ((M × Hash) ⊕ (Z × C)) ⊕ C) :
    OracleAdv.simOracle (progF P hpk sk pk z mstar rstar v) (PKE.FOTransformT.keyedRO F) x d =
      OracleAdv.simOracle (progS P hpk f sk pk z mstar v) (PKE.FOTransformT.keyedRO g) x d := by
  obtain ⟨s, u⟩ := x
  have hc : cOf P f pk mstar = P.enc pk mstar rstar := by rw [cOf, hr]
  rcases d with (⟨m, h⟩ | q) | c
  · by_cases hh : h = hpk pk
    · subst hh
      by_cases hm : m = mstar
      · subst hm
        simp [OracleAdv.simOracle, progF, progS, hr]
      · simp [OracleAdv.simOracle, progF, progS, hm, PKE.FOTransformT.keyedRO, hF m hm]
    · simp only [OracleAdv.simOracle, progF, progS, if_neg hh]
      rw [run_lazyTab, run_lazyTab]
  · simp only [OracleAdv.simOracle, progF, progS]
    rw [run_lazyTab, run_lazyTab]
  · by_cases hcc : c = P.enc pk mstar rstar
    · simp [OracleAdv.simOracle, progF, progS, hcc, hc]
    · simp only [OracleAdv.simOracle, progF, progS, hc, if_neg hcc]
      rcases hd : P.dec sk c with _ | m
      · simp only [jProg]
        rw [run_lazyTab, run_lazyTab]
      · dsimp only
        by_cases hm : m = mstar
        · subst hm
          rw [if_pos rfl, if_pos rfl]
          simp only [jProg]
          rw [run_lazyTab, run_lazyTab]
        · rw [if_neg hm, if_neg hm]
          simp only [OracleAdv.run_query, PKE.FOTransformT.keyedRO, PMF.pure_bind, hF m hm]
          by_cases he : cOf P f pk m = c
          · rw [if_pos he, if_pos (show P.enc pk m (f m) = c from he)]
            simp [PKE.FOTransformT.keyedRO]
          · rw [if_neg he, if_neg (show ¬P.enc pk m (f m) = c from he)]
            simp only [jProg]
            rw [run_lazyTab, run_lazyTab]

omit [Nonempty M] [Fintype Z] [Nonempty Z] in
/-- **Eager coins and keys at the challenge prefix.** The output and the flag of a run
against the flagged oracle are those of a run against the composite oracle of `progF`
answered by a uniform function. -/
theorem run_oFlag_eq_keyed {α : Type} (sk : SK) (pk : PK) (z : Z) (mstar : M) (rstar : R)
    (v : K) (A : OracleAdv (((M × Hash) ⊕ (Z × C)) ⊕ C) (((K × R) ⊕ K) ⊕ Option K) α) :
    (OracleAdv.run (oFlag P hpk sk pk z mstar rstar v) A ((emptyTable, emptyTable), false)).map
        (fun y => (y.1, y.2.2)) =
      (PMF.uniformOfFintype (M → K × R)).bind fun F =>
        (OracleAdv.run (OracleAdv.simOracle (progF P hpk sk pk z mstar rstar v)
          (PKE.FOTransformT.keyedRO F)) A (((emptyTable, emptyTable), false), ())).map
            fun x => (x.1, x.2.1.2) := by
  have h1 := OracleAdv.run_map_state
    (OracleAdv.simOracle (progF P hpk sk pk z mstar rstar v) roOracle)
    (oFlag P hpk sk pk z mstar rstar v) (flatF hpk pk)
    (fun x d => simOracle_progF_map P hpk sk pk z mstar rstar v x d) A
    ((((emptyTable : M × Hash → Option (K × R)), emptyTable), false), emptyTable)
  have hinit : flatF hpk pk (((((emptyTable : M × Hash → Option (K × R)), emptyTable), false) :
      Tab M C R K Hash Z × Bool), (emptyTable : M → Option (K × R))) =
      ((emptyTable, emptyTable), false) := by
    simp [flatF, joinG_empty]
  rw [hinit] at h1
  have h2 := PKE.FOTransformT.run_simOracle_roOracle_eq
    (progF P hpk sk pk z mstar rstar v) A ((emptyTable, emptyTable), false) emptyTable
  rw [PKE.FOTransformT.extDist_empty] at h2
  rw [← h1, PMF.map_comp,
    show ((fun y : α × (Tab M C R K Hash Z × Bool) => (y.1, y.2.2)) ∘
        Prod.map id (flatF hpk pk)) =
      (fun y : α × (Tab M C R K Hash Z × Bool) => (y.1, y.2.2)) ∘
        (fun x : α × ((Tab M C R K Hash Z × Bool) × (M → Option (K × R))) => (x.1, x.2.1)) from rfl,
    ← PMF.map_comp, h2, PMF.map_bind]
  exact congrArg _ (funext fun F => by rw [PMF.map_comp]; rfl)

omit [Nonempty M] [Fintype Z] [Nonempty Z] in
/-- **Eager keys at the challenge prefix.** The output and the flag of a run against
the split oracle are those of a run against the composite oracle of `progS` answered by
a uniform function. -/
theorem run_oSplit_eq_keyed {α : Type} (f : M → R) (sk : SK) (pk : PK) (z : Z) (mstar : M)
    (v : K) (A : OracleAdv (((M × Hash) ⊕ (Z × C)) ⊕ C) (((K × R) ⊕ K) ⊕ Option K) α) :
    (OracleAdv.run (oSplit P hpk f sk pk z mstar v) A (SplitTab.empty, false)).map
        (fun y => (y.1, y.2.2)) =
      (PMF.uniformOfFintype (M → K)).bind fun g =>
        (OracleAdv.run (OracleAdv.simOracle (progS P hpk f sk pk z mstar v)
          (PKE.FOTransformT.keyedRO g)) A (((emptyTable, emptyTable), false), ())).map
            fun x => (x.1, x.2.1.2) := by
  have h1 := OracleAdv.run_map_state
    (OracleAdv.simOracle (progS P hpk f sk pk z mstar v) roOracle)
    (oSplit P hpk f sk pk z mstar v) flatS
    (fun x d => simOracle_progS_map P hpk f sk pk z mstar v x d) A
    ((((emptyTable : M × Hash → Option (K × R)), emptyTable), false), emptyTable)
  have hinit : flatS (((((emptyTable : M × Hash → Option (K × R)), emptyTable), false) :
      Tab M C R K Hash Z × Bool), (emptyTable : M → Option K)) = (SplitTab.empty, false) := rfl
  rw [hinit] at h1
  have h2 := PKE.FOTransformT.run_simOracle_roOracle_eq
    (progS P hpk f sk pk z mstar v) A ((emptyTable, emptyTable), false) emptyTable
  rw [PKE.FOTransformT.extDist_empty] at h2
  rw [← h1, PMF.map_comp,
    show ((fun y : α × (SplitTab M C R K Hash Z × Bool) => (y.1, y.2.2)) ∘ Prod.map id flatS) =
      (fun y : α × (Tab M C R K Hash Z × Bool) => (y.1, y.2.2)) ∘
        (fun x : α × ((Tab M C R K Hash Z × Bool) × (M → Option K)) => (x.1, x.2.1)) from rfl,
    ← PMF.map_comp, h2, PMF.map_bind]
  exact congrArg _ (funext fun g => by rw [PMF.map_comp]; rfl)

omit [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] [Nonempty R] [Nonempty K] [DecidableEq C]
  [DecidableEq M] [DecidableEq Hash] [DecidableEq Z] [Fintype R] [Fintype K] in
/-- A uniform function into a product is a pair of independent uniform functions. -/
theorem uniform_arrow_prod {α β γ : Type} [Fintype α] [DecidableEq α] [Fintype β] [Nonempty β]
    [Fintype γ] [Nonempty γ] :
    PMF.uniformOfFintype (α → β × γ) =
      (PMF.uniformOfFintype (α → β)).bind fun g =>
        (PMF.uniformOfFintype (α → γ)).map fun f => fun a => (g a, f a) := by
  rw [← PMF.uniformOfFintype_map_equiv (β := α → β × γ)
      ⟨fun p a => (p.1 a, p.2 a), fun h => (fun a => (h a).1, fun a => (h a).2),
        fun _ => rfl, fun _ => rfl⟩,
    uniformOfFintype_prod, PMF.map_bind]
  refine congrArg _ (funext fun g => ?_)
  rw [PMF.map_comp]
  rfl

omit [Nonempty M] [Fintype Z] [Nonempty Z] in
/-- **The eager hop at a fixed challenge coin.** The flagged run with the challenge
coin `rstar` has the output and flag distribution of the split run, averaged over a
uniform derandomiser whose value at the challenge message is `rstar`. -/
theorem run_oFlag_eq_oSplit_avg {α : Type} (sk : SK) (pk : PK) (z : Z) (mstar : M) (rstar : R)
    (v : K) (A : OracleAdv (((M × Hash) ⊕ (Z × C)) ⊕ C) (((K × R) ⊕ K) ⊕ Option K) α) :
    (OracleAdv.run (oFlag P hpk sk pk z mstar rstar v) A ((emptyTable, emptyTable), false)).map
        (fun y => (y.1, y.2.2)) =
      (PMF.uniformOfFintype (M → R)).bind fun f₀ =>
        (OracleAdv.run (oSplit P hpk (Function.update f₀ mstar rstar) sk pk z mstar v) A
          (SplitTab.empty, false)).map fun y => (y.1, y.2.2) := by
  have hstep : ∀ (g : M → K) (f₀ : M → R),
      OracleAdv.simOracle (progF P hpk sk pk z mstar rstar v)
          (PKE.FOTransformT.keyedRO fun m => (g m, f₀ m)) =
        OracleAdv.simOracle (progS P hpk (Function.update f₀ mstar rstar) sk pk z mstar v)
          (PKE.FOTransformT.keyedRO g) := by
    intro g f₀
    exact funext fun x => funext fun d => simOracle_keyed_eq P hpk
      (Function.update f₀ mstar rstar) g (fun m => (g m, f₀ m)) sk pk z mstar rstar v
      (fun m hm => by simp [Function.update_of_ne hm]) (by simp) x d
  rw [run_oFlag_eq_keyed, uniform_arrow_prod, PMF.bind_bind]
  calc (PMF.uniformOfFintype (M → K)).bind (fun g =>
        ((PMF.uniformOfFintype (M → R)).map fun f => fun m => (g m, f m)).bind fun F =>
          (OracleAdv.run (OracleAdv.simOracle (progF P hpk sk pk z mstar rstar v)
            (PKE.FOTransformT.keyedRO F)) A (((emptyTable, emptyTable), false), ())).map
              fun x => (x.1, x.2.1.2))
      = (PMF.uniformOfFintype (M → K)).bind fun g => (PMF.uniformOfFintype (M → R)).bind
          fun f₀ => (OracleAdv.run (OracleAdv.simOracle
            (progS P hpk (Function.update f₀ mstar rstar) sk pk z mstar v)
            (PKE.FOTransformT.keyedRO g)) A (((emptyTable, emptyTable), false), ())).map
              fun x => (x.1, x.2.1.2) := by
        refine congrArg _ (funext fun g => ?_)
        rw [PMF.bind_map]
        exact congrArg _ (funext fun f₀ => by rw [Function.comp_apply, hstep g f₀])
    _ = _ := by
        rw [PMF.bind_comm]
        exact congrArg _ (funext fun f₀ =>
          (run_oSplit_eq_keyed P hpk (Function.update f₀ mstar rstar) sk pk z mstar v A).symm)

omit [Nonempty M] [Fintype Z] [Nonempty Z] in
/-- **The eager hop.** Averaged over a uniform challenge coin, the flagged run, whose
coins at prefix `hpk pk` are sampled lazily, has the output and flag distribution of
the split run averaged over a uniform derandomiser `f`, the challenge coin being
`f mstar`. -/
theorem oFlag_eq_eager {α : Type} (sk : SK) (pk : PK) (z : Z) (mstar : M) (v : K)
    (A : R → OracleAdv (((M × Hash) ⊕ (Z × C)) ⊕ C) (((K × R) ⊕ K) ⊕ Option K) α) :
    ((PMF.uniformOfFintype R).bind fun rstar =>
      (OracleAdv.run (oFlag P hpk sk pk z mstar rstar v) (A rstar)
        ((emptyTable, emptyTable), false)).map fun y => (y.1, y.2.2)) =
      (PMF.uniformOfFintype (M → R)).bind fun f =>
        (OracleAdv.run (oSplit P hpk f sk pk z mstar v) (A (f mstar))
          (SplitTab.empty, false)).map fun y => (y.1, y.2.2) := by
  conv_rhs => rw [← Constructions.ECBCPRF.uniform_bind_update mstar]
  rw [PMF.bind_bind]
  simp only [PMF.bind_map, Function.comp_def, Function.update_self]
  rw [PMF.bind_comm]
  exact congrArg _ (funext fun rstar =>
    run_oFlag_eq_oSplit_avg P hpk sk pk z mstar rstar v (A rstar))

/-- The flagged run of the IND-CCA experiment, with the coins at prefix `hpk pk` given
by a uniform derandomiser and the challenge point of `G` removed. -/
theorem flagDist_map_eq_eager {qRO qD : ℕ}
    (B : ROM2INDCCAAdversary PK K C (M × Hash) (K × R) (Z × C) K qRO qD) :
    (flagDist P hpk B false).map (fun y => (y.1, y.2.2)) =
      P.keygen.bind fun ks => (PMF.uniformOfFintype Z).bind fun z =>
        (PMF.uniformOfFintype M).bind fun m => (PMF.uniformOfFintype K).bind fun k₀ =>
          (PMF.uniformOfFintype (M → R)).bind fun f =>
            (OracleAdv.run (oSplit P hpk f ks.2 ks.1 z m k₀)
              (B.run ks.1 (cOf P f ks.1 m) k₀) (SplitTab.empty, false)).map
                fun y => (y.1, y.2.2) := by
  simp only [flagDist, setup, PMF.map_bind, PMF.bind_bind, PMF.bind_map, Function.comp_def,
    Bool.false_eq_true, if_false, Draw.c]
  refine congrArg _ (funext fun ks => congrArg _ (funext fun z => congrArg _ (funext fun m =>
    congrArg _ (funext fun k₀ => ?_))))
  rw [show (PMF.uniformOfFintype R).bind (fun r => (PMF.uniformOfFintype K).bind fun _ =>
      (OracleAdv.run (oFlag P hpk ks.2 ks.1 z m r k₀) (B.run ks.1 (P.enc ks.1 m r) k₀)
        ((emptyTable, emptyTable), false)).map fun y => (y.1, y.2.2)) =
      (PMF.uniformOfFintype R).bind fun r =>
        (OracleAdv.run (oFlag P hpk ks.2 ks.1 z m r k₀) (B.run ks.1 (P.enc ks.1 m r) k₀)
          ((emptyTable, emptyTable), false)).map fun y => (y.1, y.2.2) from
      congrArg _ (funext fun _ => PMF.bind_const _ _)]
  exact oFlag_eq_eager P hpk ks.2 ks.1 z m k₀ fun r => B.run ks.1 (P.enc ks.1 m r) k₀

/-- **The challenge hop over the split oracle.** The IND-CCA advantage against
`fips203 P hpk` is at most the probability that the adversary queries `G` at the
challenge point of the split run, averaged over the key pair, the rejection seed, the
challenge message and key, and the derandomiser. -/
theorem advantage_le_eager {qRO qD : ℕ}
    (B : ROM2INDCCAAdversary PK K C (M × Hash) (K × R) (Z × C) K qRO qD) :
    rom2INDCCAAdvantage (fips203 P hpk) B ≤
      (P.keygen.bind fun ks => (PMF.uniformOfFintype Z).bind fun z =>
        (PMF.uniformOfFintype M).bind fun m => (PMF.uniformOfFintype K).bind fun k₀ =>
          (PMF.uniformOfFintype (M → R)).bind fun f =>
            (OracleAdv.run (oSplit P hpk f ks.2 ks.1 z m k₀)
              (B.run ks.1 (cOf P f ks.1 m) k₀) (SplitTab.empty, false)).map
                fun y => (y.1, y.2.2)).toOuterMeasure {y | y.2 = true} := by
  refine (advantage_le_flag P hpk B).trans (le_of_eq ?_)
  rw [← flagDist_map_eq_eager P hpk B, PMF.toOuterMeasure_map_apply]
  rfl

end Eager

/-! ## Summation of the per-draw bound -/

section Summation

variable [DecidableEq M] [DecidableEq Hash] [DecidableEq Z] [Fintype R] [Fintype K]
variable (P : Scheme PK SK M C R) (hpk : PK → Hash) (f : M → R)

omit [Fintype M] [Fintype Z] [Nonempty Z] in
/-- The OW-PCA success probability of `redFix` for a fixed key pair and challenge
ciphertext. -/
theorem redFix_prob {qRO qD : ℕ}
    (B : ROM2INDCCAAdversary PK K C (M × Hash) (K × R) (Z × C) K qRO qD) (pk : PK) (sk : SK)
    (c : C) :
    ((OracleAdv.run (pcoOracle (fixedT P f) (pk, sk)) ((redFix P hpk f B).run pk c) ()).map
      fun x => (fixedT P f).pco (pk, sk) x.1 c).toOuterMeasure {b | b = true} =
    ∑' k, PMF.uniformOfFintype K k *
      (OracleAdv.run (OracleAdv.simOracle (simImplFix P hpk f pk c k)
        (pcoOracle (fixedT P f) (pk, sk))) (B.run pk c k) (SimStateF.init, ())).toOuterMeasure
          {y | (fixedT P f).pco (pk, sk) (y.2.1.found.getD (Classical.arbitrary M)) c = true} := by
  unfold redFix
  dsimp only
  rw [OracleAdv.run_rand, PMF.map_bind, PMF.toOuterMeasure_bind_apply]
  refine tsum_congr fun k => congrArg _ ?_
  rw [OracleAdv.run_bind, OracleAdv.run_simulate, PMF.bind_map]
  simp only [OracleAdv.run_ret, Function.comp_def, PMF.map_bind, PMF.pure_map,
    PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_pure_apply]
  rw [PMF.toOuterMeasure_apply]
  refine tsum_congr fun y => ?_
  by_cases h : (fixedT P f).pco (pk, sk) (y.2.1.found.getD (Classical.arbitrary M)) c = true <;>
    simp [Set.indicator, h]

omit [Fintype Z] [Nonempty Z] in
/-- The OW-PCA advantage of `redFix` as a sum over the key pair, the challenge message
and the key `k*`. -/
theorem owpcaAdvantage_redFix {qRO qD : ℕ}
    (B : ROM2INDCCAAdversary PK K C (M × Hash) (K × R) (Z × C) K qRO qD) :
    owpcaAdvantage (fixedT P f) (redFix P hpk f B) =
      ∑' ks, P.keygen ks * ∑' m, PMF.uniformOfFintype M m * ∑' k, PMF.uniformOfFintype K k *
        (OracleAdv.run (OracleAdv.simOracle (simImplFix P hpk f ks.1 (cOf P f ks.1 m) k)
          (pcoOracle (fixedT P f) (ks.1, ks.2))) (B.run ks.1 (cOf P f ks.1 m) k)
            (SimStateF.init, ())).toOuterMeasure
              {y | (fixedT P f).pco (ks.1, ks.2) (y.2.1.found.getD (Classical.arbitrary M))
                (cOf P f ks.1 m) = true} := by
  have hU : (PMF.uniformOfFintype Unit) = PMF.pure () := by ext u; simp
  rw [owpcaAdvantage, PKE.FOTransformT.prTrue_pmfGame_eq, owpcaGame,
    show (fixedT P f).keygen = P.keygen.map (fun ks => (ks.1, (ks.1, ks.2))) from rfl]
  simp only [Scheme.encDist, PMF.bind_map, Function.comp_def, hU, PMF.pure_bind,
    PMF.toOuterMeasure_bind_apply]
  refine tsum_congr fun ks => congrArg _ (tsum_congr fun m => congrArg _ ?_)
  exact redFix_prob P hpk f B ks.1 ks.2 _

omit [DecidableEq C] [DecidableEq Z] in
/-- An average whose summand does not depend on the rejection seed. -/
theorem tsum_seed_const (H : (PK × SK) → M → K → (M → R) → ℝ≥0∞) :
    ∑' ks, P.keygen ks * ∑' _z : Z, PMF.uniformOfFintype Z _z *
        ∑' m, PMF.uniformOfFintype M m * ∑' k, PMF.uniformOfFintype K k *
          ∑' f, PMF.uniformOfFintype (M → R) f * H ks m k f =
      ∑' ks, P.keygen ks * ∑' m, PMF.uniformOfFintype M m * ∑' k, PMF.uniformOfFintype K k *
        ∑' f, PMF.uniformOfFintype (M → R) f * H ks m k f :=
  tsum_congr fun _ks => congrArg _ (FOTransformU.tsum_mul_const _ _)

omit [DecidableEq C] in
/-- The average over the derandomiser moves outside the averages over the key pair, the
challenge message and the key. -/
theorem tsum_arrow_comm (H : (PK × SK) → M → K → (M → R) → ℝ≥0∞) :
    ∑' ks, P.keygen ks * ∑' m, PMF.uniformOfFintype M m * ∑' k, PMF.uniformOfFintype K k *
        ∑' f, PMF.uniformOfFintype (M → R) f * H ks m k f =
      ∑' f, PMF.uniformOfFintype (M → R) f * ∑' ks, P.keygen ks * ∑' m,
        PMF.uniformOfFintype M m * ∑' k, PMF.uniformOfFintype K k * H ks m k f := by
  have h1 : ∀ (ks : PK × SK) (m : M),
      ∑' k, PMF.uniformOfFintype K k * ∑' f, PMF.uniformOfFintype (M → R) f * H ks m k f =
        ∑' f, PMF.uniformOfFintype (M → R) f * ∑' k, PMF.uniformOfFintype K k * H ks m k f :=
    fun ks m => FOTransformU.tsum_mul_comm _ _ _
  simp only [h1]
  have h2 : ∀ ks : PK × SK,
      ∑' m, PMF.uniformOfFintype M m *
          ∑' f, PMF.uniformOfFintype (M → R) f * ∑' k, PMF.uniformOfFintype K k * H ks m k f =
        ∑' f, PMF.uniformOfFintype (M → R) f *
          ∑' m, PMF.uniformOfFintype M m * ∑' k, PMF.uniformOfFintype K k * H ks m k f :=
    fun ks => FOTransformU.tsum_mul_comm _ _ _
  simp only [h2]
  exact FOTransformU.tsum_mul_comm _ _ _

omit [DecidableEq C] [DecidableEq Z] in
/-- The average over the rejection seed moves inside the other averages. -/
theorem tsum_seed_inner (H : (PK × SK) → Z → M → K → (M → R) → ℝ≥0∞) :
    ∑' ks, P.keygen ks * ∑' z, PMF.uniformOfFintype Z z *
        ∑' m, PMF.uniformOfFintype M m * ∑' k, PMF.uniformOfFintype K k *
          ∑' f, PMF.uniformOfFintype (M → R) f * H ks z m k f =
      ∑' ks, P.keygen ks * ∑' m, PMF.uniformOfFintype M m * ∑' k, PMF.uniformOfFintype K k *
        ∑' f, PMF.uniformOfFintype (M → R) f * ∑' z, PMF.uniformOfFintype Z z * H ks z m k f := by
  refine tsum_congr fun ks => congrArg _ ?_
  rw [FOTransformU.tsum_mul_comm]
  refine tsum_congr fun m => congrArg _ ?_
  rw [FOTransformU.tsum_mul_comm]
  exact tsum_congr fun k => congrArg _ (FOTransformU.tsum_mul_comm _ _ _)

end Summation

section ThreeTerms

variable [DecidableEq M] [DecidableEq Hash] [DecidableEq Z] [Fintype R] [Fintype K]
variable (P : Scheme PK SK M C R) (hpk : PK → Hash)

/-- **The three terms.** The IND-CCA advantage against `fips203 P hpk` is at most the
correctness error of `P`, plus the average over the derandomiser of the OW-PCA
advantage of `redFix` against `fixedT P f`, plus `qRO/|Z|`. -/
theorem cca_le_three_terms {qRO qD : ℕ}
    (B : ROM2INDCCAAdversary PK K C (M × Hash) (K × R) (Z × C) K qRO qD) :
    rom2INDCCAAdvantage (fips203 P hpk) B ≤
      P.corrErr +
        (∑' f, PMF.uniformOfFintype (M → R) f * owpcaAdvantage (fixedT P f) (redFix P hpk f B)) +
        (qRO : ℝ≥0∞) / Fintype.card Z := by
  refine (advantage_le_eager P hpk B).trans ?_
  simp only [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_map_apply]
  have hflag : ∀ (ks : PK × SK) (z : Z) (m : M) (k₀ : K) (f : M → R),
      (OracleAdv.run (oSplit P hpk f ks.2 ks.1 z m k₀) (B.run ks.1 (cOf P f ks.1 m) k₀)
          (SplitTab.empty, false)).toOuterMeasure
            ((fun y : Bool × (SplitTab M C R K Hash Z × Bool) => (y.1, y.2.2)) ⁻¹'
              {y | y.2 = true}) ≤
        FOTransformU.failInd P ks.2 m (cOf P f ks.1 m) +
        (OracleAdv.run (OracleAdv.simOracle (simImplFix P hpk f ks.1 (cOf P f ks.1 m) k₀)
          (pcoOracle (fixedT P f) (ks.1, ks.2))) (B.run ks.1 (cOf P f ks.1 m) k₀)
            (SimStateF.init, ())).toOuterMeasure
              {y | (fixedT P f).pco (ks.1, ks.2) (y.2.1.found.getD (Classical.arbitrary M))
                (cOf P f ks.1 m) = true} +
        (OracleAdv.run (oSim P hpk f (badUpd z) (selK P f ks.2 ks.1) (fun _ => false) ks.1
          (cOf P f ks.1 m) k₀) (B.run ks.1 (cOf P f ks.1 m) k₀)
            (SimStateF.init, false)).toOuterMeasure {y | y.2.2 = true} :=
    fun ks z m k₀ f => flag_le P hpk f ks.2 ks.1 z m k₀ _
  refine le_trans (ENNReal.tsum_le_tsum fun ks => mul_le_mul_right
    (ENNReal.tsum_le_tsum fun z => mul_le_mul_right
      (ENNReal.tsum_le_tsum fun m => mul_le_mul_right
        (ENNReal.tsum_le_tsum fun k₀ => mul_le_mul_right
          (ENNReal.tsum_le_tsum fun f => mul_le_mul_right (hflag ks z m k₀ f) _) _) _) _) _) ?_
  simp only [mul_add, ENNReal.tsum_add]
  refine add_le_add (add_le_add (le_of_eq ?_) (le_of_eq ?_)) ?_
  · rw [tsum_seed_const, FOTransformU.corrErr_eq]
    refine tsum_congr fun ks => congrArg _ (tsum_congr fun m => congrArg _ ?_)
    rw [FOTransformU.tsum_mul_const]
    exact FOTransform.tsum_uniform_eval m fun r => FOTransformU.failInd P ks.2 m (P.enc ks.1 m r)
  · rw [tsum_seed_const, tsum_arrow_comm]
    exact tsum_congr fun f => congrArg _ (owpcaAdvantage_redFix P hpk f B).symm
  · rw [tsum_seed_inner]
    refine le_trans (ENNReal.tsum_le_tsum fun ks => mul_le_mul_right
      (ENNReal.tsum_le_tsum fun m => mul_le_mul_right
        (ENNReal.tsum_le_tsum fun k => mul_le_mul_right
          (ENNReal.tsum_le_tsum fun f => mul_le_mul_right
            (tsum_bad_le P hpk f (selK P f ks.2 ks.1) (fun _ => false) ks.1 (cOf P f ks.1 m) k
              (B.run ks.1 (cOf P f ks.1 m) k) qRO (B.isQueryBoundRO _ _ _)) _) _) _) _)
      (le_of_eq ?_)
    simp only [FOTransformU.tsum_mul_const]

end ThreeTerms

/-! ## The reduction against the transform -/

section Composition

variable [DecidableEq M] [DecidableEq Hash] [DecidableEq Z] [Fintype R] [Fintype K]
variable (P : Scheme PK SK M C R) (hpk : PK → Hash) (f : M → R)

omit [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] in
/-- The composite oracle of the reduction against `tTransform P`, with the random
oracle answered eagerly by `f`, is the re-indexed oracle with the selectors `selK` and
`false`. -/
theorem simOracle_simImplF_eq_oSim (ks : PK × SK) (cstar : C) (v : K)
    (x : SimStateF M C R K Hash Z × Unit) (d : ((M × Hash) ⊕ (Z × C)) ⊕ C) :
    OracleAdv.simOracle (simImplF P hpk ks.1 cstar v)
        (PKE.FOTransformT.eO (PKE.FOTransformT.ansReal P ks) (fun _ _ u => u) f) x d =
      oSim P hpk f (fun _ _ => ()) (selK P f ks.2 ks.1) (fun _ => false) ks.1 cstar v x d := by
  obtain ⟨st, u⟩ := x
  have hc : ∀ m : M, P.enc ks.1 m (f m) = cOf P f ks.1 m := fun _ => rfl
  rcases d with (q | q) | c
  · simp only [OracleAdv.simOracle, simImplF, oSim]
    by_cases hh : q.2 = hpk ks.1
    · simp only [hh, if_true, OracleAdv.run_query, PKE.FOTransformT.eO, PMF.pure_bind,
        Sum.elim_inl, Sum.elim_inr, id, hc, FOTransform.ansReal_eq_pco, pco_fixedT_cOf]
      by_cases hs : selK P f ks.2 ks.1 q.1 = true
      · simp only [hs, if_true]
        by_cases hcs : cOf P f ks.1 q.1 = cstar
        · simp [hcs, PMF.pure_map]
        · simp only [hcs, if_false]
          exact run_lazyTab _ _ _ _ _ _
      · simp only [hs, Bool.false_eq_true, if_false]
        exact run_lazyTab _ _ _ _ _ _
    · simp only [hh, if_false]
      exact run_lazyTab _ _ _ _ _ _
  · simp only [OracleAdv.simOracle, simImplF, oSim, Bool.false_eq_true, if_false]
    exact run_lazyTab _ _ _ _ _ _
  · simp only [OracleAdv.simOracle, simImplF, oSim]
    split_ifs
    · simp [PMF.pure_map]
    · exact run_lazyTab _ _ _ _ _ _

omit [Fintype M] [Fintype Z] [Nonempty Z] in
/-- The run of `redRun` against the eagerly answered random oracle is the run of
`redFix` against the plaintext-checking oracle of `fixedT P f`. -/
theorem run_redRun_eq (ks : PK × SK) (c : C) {qRO qD : ℕ}
    (B : ROM2INDCCAAdversary PK K C (M × Hash) (K × R) (Z × C) K qRO qD) :
    (OracleAdv.run (PKE.FOTransformT.eO (PKE.FOTransformT.ansReal P ks) (fun _ _ u => u) f)
        (redRun P hpk B ks.1 c) ()).map Prod.fst =
      (OracleAdv.run (pcoOracle (fixedT P f) (ks.1, ks.2)) ((redFix P hpk f B).run ks.1 c) ()).map
        Prod.fst := by
  have hsim : ∀ kstar : K, OracleAdv.simOracle (S := SimStateF M C R K Hash Z) (U := Unit)
        (simImplF P hpk ks.1 c kstar)
        (PKE.FOTransformT.eO (PKE.FOTransformT.ansReal P ks) (fun _ _ u => u) f) =
      OracleAdv.simOracle (S := SimStateF M C R K Hash Z) (U := Unit)
        (simImplFix P hpk f ks.1 c kstar) (pcoOracle (fixedT P f) (ks.1, ks.2)) :=
    fun kstar => funext fun x => funext fun d =>
      (simOracle_simImplF_eq_oSim P hpk f ks c kstar x d).trans
        (simOracle_eq_oSim P hpk f ks.2 ks.1 c kstar x d).symm
  simp only [redRun, redFix, OracleAdv.run_rand, PMF.map_bind]
  refine congrArg _ (funext fun kstar => ?_)
  simp only [OracleAdv.run_bind, OracleAdv.run_simulate, OracleAdv.run_ret, hsim kstar]

/-- The success of the OW-PCA experiment of `redFix` against `fixedT P f`, for a key
pair and challenge message. -/
noncomputable def owpcaInnerF {qRO qD : ℕ}
    (B : ROM2INDCCAAdversary PK K C (M × Hash) (K × R) (Z × C) K qRO qD) (ks : PK × SK) (m : M)
    (f : M → R) : PMF Bool :=
  (OracleAdv.run (pcoOracle (fixedT P f) (ks.1, ks.2))
    ((redFix P hpk f B).run ks.1 (cOf P f ks.1 m)) ()).map fun x =>
      (fixedT P f).pco (ks.1, ks.2) x.1 (cOf P f ks.1 m)

omit [Fintype Z] [Nonempty Z] in
theorem owpcaGame_fixedT_redFix {qRO qD : ℕ}
    (B : ROM2INDCCAAdversary PK K C (M × Hash) (K × R) (Z × C) K qRO qD) :
    owpcaGame (fixedT P f) (redFix P hpk f B) = P.keygen.bind fun ks =>
      (PMF.uniformOfFintype M).bind fun m => owpcaInnerF P hpk B ks m f := by
  simp only [owpcaGame, Scheme.encDist, PMF.bind_map, Function.comp_def, owpcaInnerF]
  rw [show (fixedT P f).keygen = P.keygen.map fun ks => (ks.1, (ks.1, ks.2)) from rfl, PMF.bind_map]
  have hU : PMF.uniformOfFintype Unit = PMF.pure () := by ext u; simp
  simp only [Function.comp_def, hU, PMF.pure_bind]
  rfl

omit [Fintype Z] [Nonempty Z] in
theorem romOWPCAGame_redROM {qRO qD : ℕ}
    (B : ROM2INDCCAAdversary PK K C (M × Hash) (K × R) (Z × C) K qRO qD) :
    romOWPCAGame (PKE.FOTransformT.tTransform P) (redROM P hpk B) = P.keygen.bind fun ks =>
      (PMF.uniformOfFintype M).bind fun m => (PMF.uniformOfFintype (M → R)).bind fun f =>
        owpcaInnerF P hpk B ks m f := by
  rw [PKE.FOTransformT.romOWPCAGame_eq]
  refine congrArg _ (funext fun ks => congrArg _ (funext fun m => ?_))
  rw [PKE.FOTransformT.game_eq_eager]
  refine congrArg _ (funext fun f => ?_)
  simp only [PKE.FOTransformT.withCheck, OracleAdv.run_bind, OracleAdv.run_query,
    OracleAdv.run_ret, PKE.FOTransformT.eO, PMF.pure_bind, PMF.map_bind, PMF.pure_map,
    Sum.elim_inr, id]
  have h := run_redRun_eq P hpk f ks (cOf P f ks.1 m) B
  have hans : ∀ (m' : M) (c' : C),
      PKE.FOTransformT.ansReal P ks (m', c') (f m') = (fixedT P f).pco (ks.1, ks.2) m' c' :=
    fun m' c' => FOTransform.ansReal_eq_pco P f ks (m', c')
  have h2 := congrArg
    (PMF.map fun m' => (fixedT P f).pco (ks.1, ks.2) m' (cOf P f ks.1 m)) h
  simp only [PMF.map_comp, Function.comp_def] at h2
  unfold owpcaInnerF
  simp only [hans]
  rw [← h2, PMF.map]
  rfl

end Composition

/-! ## The theorem -/

section Main

variable [DecidableEq M] [DecidableEq Hash] [DecidableEq Z] [Fintype R] [Fintype K]
variable (P : Scheme PK SK M C R) (hpk : PK → Hash)

omit [Fintype Z] [Nonempty Z] in
/-- The OW-PCA advantage of `redROM B` against `tTransform P` is the average over the
derandomiser of the OW-PCA advantage of `redFix` against `fixedT P f`. -/
theorem owpca_eq_redROM {qRO qD : ℕ}
    (B : ROM2INDCCAAdversary PK K C (M × Hash) (K × R) (Z × C) K qRO qD) :
    romOWPCAAdvantage (PKE.FOTransformT.tTransform P) (redROM P hpk B) =
      ∑' f, PMF.uniformOfFintype (M → R) f *
        owpcaAdvantage (fixedT P f) (redFix P hpk f B) := by
  simp only [romOWPCAAdvantage, owpcaAdvantage, PKE.FOTransformT.prTrue_pmfGame_eq,
    romOWPCAGame_redROM, owpcaGame_fixedT_redFix]
  rw [← PMF.toOuterMeasure_bind_apply, PMF.bind_comm (PMF.uniformOfFintype (M → R)) P.keygen]
  refine congrArg (fun p : PMF Bool => p.toOuterMeasure _) (congrArg _ (funext fun ks => ?_))
  exact (PMF.bind_comm _ _ _).symm

omit [Fintype M] [Fintype Z] [Nonempty Z] in
/-- The reduction asks at most `qRO` random-oracle and `qRO` plaintext-checking
queries, hence at most `2 · qRO` queries in total. -/
theorem isQueryBoundBy_redROM_total {qRO qD : ℕ}
    (B : ROM2INDCCAAdversary PK K C (M × Hash) (K × R) (Z × C) K qRO qD) (pk : PK) (c : C) :
    ((redROM P hpk B).run pk c).IsQueryBoundBy (fun _ => 1) (qRO + qRO) := by
  have hcost : (fun d : M ⊕ (M × C) => Sum.elim (fun _ => 1) (fun _ => 0) d +
      Sum.elim (fun _ => 0) (fun _ => 1) d) = fun _ => 1 := by
    funext d; cases d <;> rfl
  have h := ((redROM P hpk B).isQueryBoundG pk c).add ((redROM P hpk B).isQueryBoundP pk c)
  rwa [hcost] at h

/-- **ML-KEM's transform is IND-CCA secure in the random-oracle model.** For every
public-key encryption scheme `P`, every `hpk : PK → Hash` and every IND-CCA adversary
`B` against `fips203 P hpk` asking at most `qRO` random-oracle queries, with
`n = 2 · qRO`,

`rom2INDCCAAdvantage (fips203 P hpk) B ≤ owcpaAdvantage P (tReductionC P (redROM B)) +
  (n + 1)·P.corrWorst + P.corrErr + (n + 1)·owcpaAdvantage P (tReductionD P (redROM B) n) +
  qRO/|Z| + P.corrErr`

with `P.corrWorst` the correctness error δ and `P.corrErr ≤ δ`. The reductions are
explicit: `redROM B` runs `B` once and asks at most `qRO` random-oracle and `qRO`
plaintext-checking queries; `tReductionC` and `tReductionD` run it once with a lazily
sampled `G` and re-encryption answers. The term `qRO/|Z|` bounds the probability that
`B` queries `J` at the rejection seed. The statement is in the classical random-oracle
model; it says nothing about quantum adversaries with superposition access to `G` and
`J`. -/
theorem fips203_indcca {qRO qD : ℕ}
    (B : ROM2INDCCAAdversary PK K C (M × Hash) (K × R) (Z × C) K qRO qD) :
    rom2INDCCAAdvantage (fips203 P hpk) B ≤
      owcpaAdvantage P (PKE.FOTransformT.tReductionC P (redROM P hpk B)) +
        ((qRO + qRO + 1 : ℕ) : ℝ≥0∞) * P.corrWorst + P.corrErr +
        ((qRO + qRO + 1 : ℕ) : ℝ≥0∞) *
          owcpaAdvantage P (PKE.FOTransformT.tReductionD P (redROM P hpk B) (qRO + qRO)) +
        (qRO : ℝ≥0∞) / Fintype.card Z + P.corrErr := by
  refine (cca_le_three_terms P hpk B).trans ?_
  rw [← owpca_eq_redROM]
  calc P.corrErr + romOWPCAAdvantage (PKE.FOTransformT.tTransform P) (redROM P hpk B) +
        (qRO : ℝ≥0∞) / Fintype.card Z
      = romOWPCAAdvantage (PKE.FOTransformT.tTransform P) (redROM P hpk B) +
          (qRO : ℝ≥0∞) / Fintype.card Z + P.corrErr := by ring
    _ ≤ _ := by
        gcongr
        exact PKE.FOTransformT.tTransform_owpca_of_total P (redROM P hpk B) (qRO + qRO)
          (isQueryBoundBy_redROM_total P hpk B)

end Main

end CatCrypt.Crypto.KEM.FIPS203
