/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.KEM.FIPS203Security
public import CatCryptCore.Crypto.PKE.GamesTimed
public import CatCryptCore.Tactics.DeriveTimed
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.AutoTime

/-!
# Running time of the FIPS 203 reductions

The costed forms of the OW-PCA adversaries built from an IND-CCA adversary against
`fips203 P hpk`: `redRun` and `redROM` (the simulation `simImplF`, against `tTransform P`) and
`redFix` (the simulation `simImplFix`, against `fixedT P f`), derived by `derive_timed` and
`derive_reduction`. The simulation state holds four lazily sampled tables; in the costed form
each table carries a cost companion, which grows by at most `3` per query, so query `j` of the
adversary costs at most a constant plus `6 j`.

## Cost model

The registered costs of `CatCryptCore.Crypto.OracleAdversaryTimed`: one unit per `rand` and
per `query` node. The public-key hash `hpk`, the encryption `P.enc`, the coin function `f` and
the call of the adversary are priced by their cost companions `hpkCost`, `encCost`, `fCost`
and `runCost`.

## Main definitions

* `redRun.timed`, `redROM.timed`, `redFix.timed` — the costed forms

## Main results

* `redRun.erase_timed`, `redROM.erase_timed`, `redFix.erase_timed` — erasure
* `simImplF.timeBound`, `simImplFix.timeBound` — one query of the costed handlers
* `simImplF.allRet_le`, `simImplFix.allRet_le` — the table companions grow by at most `3` per
  query
* `redRun.timeBound`, `redROM.timeBound`, `redFix.timeBound` — an adversary of time `T` with at
  most `q` queries gives time at most `rc + T + ∑_{j < q} (6 j + c) + 5` (`+ 6` for `redROM`),
  with `c` a constant in the cost bounds of `hpk`, `P.enc` and `f`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.KEM.FIPS203

open CatCrypt.Crypto CatCrypt.Crypto.PKE.Games CatCrypt.Crypto.KEM.Games

derive_timed redRun

derive_reduction redROM

derive_reduction redFix


open OracleAdv.Timed

variable {PK SK M C R K Hash Z : Type} [Nonempty M] [Nonempty R] [Nonempty K] [DecidableEq C]
  [DecidableEq M] [DecidableEq Hash] [DecidableEq Z] [Fintype R] [Fintype K]

omit [Nonempty M] in
/-- One query of the costed handler `simImplF.timed`, with `hpk` of cost at most `eh`,
encryption of cost at most `ee` and the four table companions at most `b`, takes time at
most `2 b + eh + 6 ee + 25`. -/
theorem simImplF.timeBound (P : Scheme PK SK M C R) (hpk : PK → Hash) (hpkCost : PK → ℕ)
    (pk : PK) (cstar : C) (kstar : K) (st : SimStateF M C R K Hash Z)
    (d : ((M × Hash) ⊕ (Z × C)) ⊕ C) (encCost : PK → M → R → ℕ) (LDCost : C → ℕ)
    (LQCost : M → ℕ) (LOCost : M × Hash → ℕ) (LJCost : Z × C → ℕ) {eh ee b : ℕ}
    (hh : ∀ pk, hpkCost pk ≤ eh) (he : ∀ pk m r, encCost pk m r ≤ ee)
    (hD : ∀ x, LDCost x ≤ b) (hQ : ∀ x, LQCost x ≤ b) (hO : ∀ x, LOCost x ≤ b)
    (hJ : ∀ x, LJCost x ≤ b) :
    StepTimeBound (simImplF.timed P hpk hpkCost pk cstar kstar st d encCost LDCost LQCost
      LOCost LJCost) (2 * b + eh + 6 * ee + 25) := by
  have hs : ∀ s : R ⊕ Bool, (@Sum.rec R Bool (fun _ => ℕ) (fun _ => 0) (fun _ => 0) s) = 0 :=
    fun s => by cases s <;> rfl
  rcases d with (q | q) | c
  · by_cases h : q.2 = hpk pk <;> simp only [simImplF.timed, h, hs, ↓reduceIte] <;>
      show StepTimeBound _ _ <;> time_bound
  · show StepTimeBound _ _; time_bound
  · show StepTimeBound _ _; time_bound

omit [Nonempty M] in
/-- The costed handler `simImplF.timed` returns tables whose companions exceed those it
receives by at most `3`. -/
theorem simImplF.allRet_le (P : Scheme PK SK M C R) (hpk : PK → Hash) (hpkCost : PK → ℕ)
    (pk : PK) (cstar : C) (kstar : K) (st : SimStateF M C R K Hash Z)
    (d : ((M × Hash) ⊕ (Z × C)) ⊕ C) (encCost : PK → M → R → ℕ) (LDCost : C → ℕ)
    (LQCost : M → ℕ) (LOCost : M × Hash → ℕ) (LJCost : Z × C → ℕ) {b : ℕ}
    (hD : ∀ x, LDCost x ≤ b) (hQ : ∀ x, LQCost x ≤ b) (hO : ∀ x, LOCost x ≤ b)
    (hJ : ∀ x, LJCost x ≤ b) :
    AllRet (fun y => (∀ x, y.2.1.2 x ≤ b + 3) ∧ (∀ x, y.2.2.1.2 x ≤ b + 3) ∧
        (∀ x, y.2.2.2.1.2 x ≤ b + 3) ∧ (∀ x, y.2.2.2.2.1.2 x ≤ b + 3))
      (simImplF.timed P hpk hpkCost pk cstar kstar st d encCost LDCost LQCost LOCost
        LJCost).2 := by
  rcases d with (q | q) | c <;> dsimp only [simImplF.timed, delay] <;>
    (repeat' (first | split_ifs | split | intro _ | dsimp only [AllRet])) <;>
    refine ⟨fun x => ?_, fun x => ?_, fun x => ?_, fun x => ?_⟩ <;>
    (try split) <;> (try have := hD x) <;> (try have := hQ x) <;> (try have := hO x) <;>
    (try have := hJ x) <;> omega

/-- **Time of `redRun.timed`.** With `hpk` of cost at most `eh`, encryption of cost at most
`ee`, the call of `B.run pk c` of cost at most `rc`, and `B.run pk c k` of time at most `T`
with at most `q` queries for every `k`, the costed reduction takes time at most
`rc + T + ∑_{j < q} (6 j + eh + 6 ee + 26) + 5`: query `j` meets table companions of at most
`3 j`. -/
theorem redRun.timeBound (P : Scheme PK SK M C R) (hpk : PK → Hash) (hpkCost : PK → ℕ)
    {qRO qD : ℕ} (B : ROM2INDCCAAdversary PK K C (M × Hash) (K × R) (Z × C) K qRO qD)
    (pk : PK) (c : C) (runCost : PK → C → K → ℕ) (encCost : PK → M → R → ℕ)
    {eh ee rc T q : ℕ} (hh : ∀ pk, hpkCost pk ≤ eh) (he : ∀ pk m r, encCost pk m r ≤ ee)
    (hr : ∀ k, runCost pk c k ≤ rc) (hA : ∀ k, (ofAdv (B.run pk c k)).TimeBound T)
    (hq : ∀ k, (B.run pk c k).IsQueryBound q) :
    StepTimeBound (redRun.timed P hpk hpkCost B pk c runCost encCost)
      (rc + T + ∑ j ∈ Finset.range q, (2 * (3 * (0 + j)) + eh + 6 * ee + 26) + 5) := by
  unfold redRun.timed
  refine stepTimeBound_zero.2 ⟨by omega, fun kstar => ?_⟩
  have himpl : ∀ (i : ℕ) (s : ((C → Option K) × (C → ℕ)) × ((M → Option K) × (M → ℕ)) ×
        ((M × Hash → Option (K × R)) × (M × Hash → ℕ)) ×
        ((Z × C → Option K) × (Z × C → ℕ)) × Option M) (d : ((M × Hash) ⊕ (Z × C)) ⊕ C),
      ((∀ x, s.1.2 x ≤ 3 * i) ∧ (∀ x, s.2.1.2 x ≤ 3 * i) ∧ (∀ x, s.2.2.1.2 x ≤ 3 * i) ∧
        (∀ x, s.2.2.2.1.2 x ≤ 3 * i)) →
      StepTimeBound (delay 1 (simImplF.timed P hpk hpkCost pk c kstar
          { LD := s.1.1, LQ := s.2.1.1, LO := s.2.2.1.1, LJ := s.2.2.2.1.1, found := s.2.2.2.2 }
          d encCost s.1.2 s.2.1.2 s.2.2.1.2 s.2.2.2.1.2))
        (2 * (3 * i) + eh + 6 * ee + 26) ∧
      AllRet (fun y => (∀ x, y.2.1.2 x ≤ 3 * (i + 1)) ∧ (∀ x, y.2.2.1.2 x ≤ 3 * (i + 1)) ∧
          (∀ x, y.2.2.2.1.2 x ≤ 3 * (i + 1)) ∧ (∀ x, y.2.2.2.2.1.2 x ≤ 3 * (i + 1)))
        (delay 1 (simImplF.timed P hpk hpkCost pk c kstar
          { LD := s.1.1, LQ := s.2.1.1, LO := s.2.2.1.1, LJ := s.2.2.2.1.1, found := s.2.2.2.2 }
          d encCost s.1.2 s.2.1.2 s.2.2.1.2 s.2.2.2.1.2)).2 := by
    intro i s d hs
    refine ⟨?_, ?_⟩
    · exact (stepTimeBound_delay (simImplF.timeBound P hpk hpkCost pk c kstar _ d encCost _ _ _ _
        hh he hs.1 hs.2.1 hs.2.2.1 hs.2.2.2)).mono (by omega)
    · exact allRet_mono (fun y hy => ⟨fun x => (hy.1 x).trans (by omega),
        fun x => (hy.2.1 x).trans (by omega), fun x => (hy.2.2.1 x).trans (by omega),
        fun x => (hy.2.2.2 x).trans (by omega)⟩)
        (simImplF.allRet_le P hpk hpkCost pk c kstar _ d encCost _ _ _ _
          hs.1 hs.2.1 hs.2.2.1 hs.2.2.2)
  have hX := OracleAdv.Timed.timeBound_simulateHat_inv
    (fun y : ((C → Option K) × (C → ℕ)) × ((M → Option K) × (M → ℕ)) ×
        ((M × Hash → Option (K × R)) × (M × Hash → ℕ)) ×
        ((Z × C → Option K) × (Z × C → ℕ)) × Option M =>
      ({ LD := y.1.1, LQ := y.2.1.1, LO := y.2.2.1.1, LJ := y.2.2.2.1.1, found := y.2.2.2.2 } :
        SimStateF M C R K Hash Z))
    (fun y : SimStateF M C R K Hash Z =>
      ((fun a => y.LD a, fun _ => 0), (fun a => y.LQ a, fun _ => 0),
        (fun a => y.LO a, fun _ => 0), (fun a => y.LJ a, fun _ => 0), y.found))
    (fun st a => delay 1 (simImplF.timed P hpk hpkCost pk c kstar
      { LD := st.1.1, LQ := st.2.1.1, LO := st.2.2.1.1, LJ := st.2.2.2.1.1, found := st.2.2.2.2 }
      a encCost st.1.2 st.2.1.2 st.2.2.1.2 st.2.2.2.1.2))
    (fun i s => (∀ x, s.1.2 x ≤ 3 * i) ∧ (∀ x, s.2.1.2 x ≤ 3 * i) ∧
      (∀ x, s.2.2.1.2 x ≤ 3 * i) ∧ (∀ x, s.2.2.2.1.2 x ≤ 3 * i))
    (fun i => 2 * (3 * i) + eh + 6 * ee + 26) himpl (hA kstar)
    (by simpa using hq kstar) 0
    ((fun _ => none, fun _ => 0), (fun _ => none, fun _ => 0), (fun _ => none, fun _ => 0),
      (fun _ => none, fun _ => 0), none)
    ⟨fun _ => Nat.zero_le _, fun _ => Nat.zero_le _, fun _ => Nat.zero_le _,
      fun _ => Nat.zero_le _⟩
  have key : ∀ {β : Type} (X : ℕ × OracleAdv.Timed (M ⊕ M × C) (R ⊕ Bool) β)
      (f : β → ℕ × OracleAdv.Timed (M ⊕ M × C) (R ⊕ Bool) M) (N₁ N₂ : ℕ),
      StepTimeBound X (N₁ + N₂) → (∀ x, StepTimeBound (f x) 2) →
      1 + runCost pk c kstar + 1 + X.1 + (X.2.bind f).1 ≤ rc + N₁ + N₂ + 5 - 1 ∧
        (X.2.bind f).2.TimeBound
          (rc + N₁ + N₂ + 5 - 1 - (1 + runCost pk c kstar + 1 + X.1 + (X.2.bind f).1)) := by
    intro β X f N₁ N₂ hX hf
    have hB := timeBound_bind hX.2 hf
    have h1 := hX.1
    have h2 := hB.1
    have h3 := hr kstar
    exact ⟨by omega, hB.2.mono (by omega)⟩
  exact key _ _ _ _ hX fun _ => ⟨le_rfl, trivial⟩

/-- **Time of `redROM.timed`.** The bound of `redRun.timeBound`, for every public key and
challenge. -/
theorem redROM.timeBound (P : Scheme PK SK M C R) (hpk : PK → Hash) (hpkCost : PK → ℕ)
    {qRO qD : ℕ} (B : ROM2INDCCAAdversary PK K C (M × Hash) (K × R) (Z × C) K qRO qD)
    (runCost : PK → C → K → ℕ) (encCost : PK → M → R → ℕ)
    {eh ee rc T q : ℕ} (hh : ∀ pk, hpkCost pk ≤ eh) (he : ∀ pk m r, encCost pk m r ≤ ee)
    (hr : ∀ pk c k, runCost pk c k ≤ rc) (hA : ∀ pk c k, (ofAdv (B.run pk c k)).TimeBound T)
    (hq : ∀ pk c k, (B.run pk c k).IsQueryBound q) :
    (redROM.timed P hpk hpkCost B runCost encCost).TimeBound
      (rc + T + ∑ j ∈ Finset.range q, (2 * (3 * (0 + j)) + eh + 6 * ee + 26) + 6) :=
  fun pk c => by
    unfold redROM.timed
    dsimp only
    unfold redROM.run.tree.timed
    exact (stepTimeBound_delay (redRun.timeBound P hpk hpkCost B pk c runCost encCost hh he
      (hr pk c) (hA pk c) (hq pk c))).mono (by omega)

omit [Nonempty M] in
/-- The case of `simImplFix.timeBound` of a random-oracle query at the prefix `hpk pk` whose
ciphertext is the challenge. -/
theorem simImplFix.timeBound_ro_hit (P : Scheme PK SK M C R) (hpk : PK → Hash)
    (hpkCost : PK → ℕ) (f : M → R) (fCost : M → ℕ) (pk : PK) (cstar : C) (kstar : K)
    (st : SimStateF M C R K Hash Z) (q : M × Hash) (LDCost : C → ℕ)
    (encCost : PK → M → R → ℕ) (LQCost : M → ℕ) (LOCost : M × Hash → ℕ) (LJCost : Z × C → ℕ)
    {eh ef ee b : ℕ} (hh : ∀ pk, hpkCost pk ≤ eh) (hf : ∀ m, fCost m ≤ ef)
    (he : ∀ pk m r, encCost pk m r ≤ ee) (hQ : ∀ x, LQCost x ≤ b) (h : q.2 = hpk pk)
    (hc : cOf P f pk q.1 = cstar) :
    StepTimeBound (simImplFix.timed P hpk hpkCost f fCost pk cstar kstar st (.inl (.inl q))
      LDCost encCost LQCost LOCost LJCost) (2 * b + eh + 8 * ef + 6 * ee + 32) := by
  simp only [simImplFix.timed, h, hc, ↓reduceIte]
  show StepTimeBound _ _
  time_bound

omit [Nonempty M] in
/-- The case of `simImplFix.timeBound` of a random-oracle query at the prefix `hpk pk` whose
ciphertext is not the challenge. -/
theorem simImplFix.timeBound_ro_miss (P : Scheme PK SK M C R) (hpk : PK → Hash)
    (hpkCost : PK → ℕ) (f : M → R) (fCost : M → ℕ) (pk : PK) (cstar : C) (kstar : K)
    (st : SimStateF M C R K Hash Z) (q : M × Hash) (LDCost : C → ℕ)
    (encCost : PK → M → R → ℕ) (LQCost : M → ℕ) (LOCost : M × Hash → ℕ) (LJCost : Z × C → ℕ)
    {eh ef ee b : ℕ} (hh : ∀ pk, hpkCost pk ≤ eh) (hf : ∀ m, fCost m ≤ ef)
    (he : ∀ pk m r, encCost pk m r ≤ ee) (hD : ∀ x, LDCost x ≤ b) (hQ : ∀ x, LQCost x ≤ b)
    (h : q.2 = hpk pk) (hc : ¬cOf P f pk q.1 = cstar) :
    StepTimeBound (simImplFix.timed P hpk hpkCost f fCost pk cstar kstar st (.inl (.inl q))
      LDCost encCost LQCost LOCost LJCost) (2 * b + eh + 8 * ef + 6 * ee + 32) := by
  simp only [simImplFix.timed, h, hc, ↓reduceIte]
  show StepTimeBound _ _
  time_bound

omit [Nonempty M] in
/-- The case of `simImplFix.timeBound` of a random-oracle query at another prefix. -/
theorem simImplFix.timeBound_ro_ne (P : Scheme PK SK M C R) (hpk : PK → Hash)
    (hpkCost : PK → ℕ) (f : M → R) (fCost : M → ℕ) (pk : PK) (cstar : C) (kstar : K)
    (st : SimStateF M C R K Hash Z) (q : M × Hash) (LDCost : C → ℕ)
    (encCost : PK → M → R → ℕ) (LQCost : M → ℕ) (LOCost : M × Hash → ℕ) (LJCost : Z × C → ℕ)
    {eh ef ee b : ℕ} (hh : ∀ pk, hpkCost pk ≤ eh) (hO : ∀ x, LOCost x ≤ b)
    (h : ¬q.2 = hpk pk) :
    StepTimeBound (simImplFix.timed P hpk hpkCost f fCost pk cstar kstar st (.inl (.inl q))
      LDCost encCost LQCost LOCost LJCost) (2 * b + eh + 8 * ef + 6 * ee + 32) := by
  simp only [simImplFix.timed, h, ↓reduceIte]
  show StepTimeBound _ _
  time_bound

omit [Nonempty M] in
/-- One query of the costed handler `simImplFix.timed`, with `hpk` of cost at most `eh`, `f`
of cost at most `ef`, encryption of cost at most `ee` and the four table companions at most
`b`, takes time at most `2 b + eh + 8 ef + 6 ee + 32`. -/
theorem simImplFix.timeBound (P : Scheme PK SK M C R) (hpk : PK → Hash) (hpkCost : PK → ℕ)
    (f : M → R) (fCost : M → ℕ) (pk : PK) (cstar : C) (kstar : K)
    (st : SimStateF M C R K Hash Z) (d : ((M × Hash) ⊕ (Z × C)) ⊕ C) (LDCost : C → ℕ)
    (encCost : PK → M → R → ℕ) (LQCost : M → ℕ) (LOCost : M × Hash → ℕ) (LJCost : Z × C → ℕ)
    {eh ef ee b : ℕ} (hh : ∀ pk, hpkCost pk ≤ eh) (hf : ∀ m, fCost m ≤ ef)
    (he : ∀ pk m r, encCost pk m r ≤ ee) (hD : ∀ x, LDCost x ≤ b) (hQ : ∀ x, LQCost x ≤ b)
    (hO : ∀ x, LOCost x ≤ b) (hJ : ∀ x, LJCost x ≤ b) :
    StepTimeBound (simImplFix.timed P hpk hpkCost f fCost pk cstar kstar st d LDCost encCost
      LQCost LOCost LJCost) (2 * b + eh + 8 * ef + 6 * ee + 32) := by
  rcases d with (q | q) | c
  · by_cases h : q.2 = hpk pk
    · by_cases hc : cOf P f pk q.1 = cstar
      · exact simImplFix.timeBound_ro_hit P hpk hpkCost f fCost pk cstar kstar st q LDCost
          encCost LQCost LOCost LJCost hh hf he hQ h hc
      · exact simImplFix.timeBound_ro_miss P hpk hpkCost f fCost pk cstar kstar st q LDCost
          encCost LQCost LOCost LJCost hh hf he hD hQ h hc
    · exact simImplFix.timeBound_ro_ne (ef := ef) (ee := ee) P hpk hpkCost f fCost pk cstar
        kstar st q LDCost encCost LQCost LOCost LJCost hh hO h
  · show StepTimeBound _ _; time_bound
  · show StepTimeBound _ _; time_bound

omit [Nonempty M] in
/-- The costed handler `simImplFix.timed` returns tables whose companions exceed those it
receives by at most `3`. -/
theorem simImplFix.allRet_le (P : Scheme PK SK M C R) (hpk : PK → Hash) (hpkCost : PK → ℕ)
    (f : M → R) (fCost : M → ℕ) (pk : PK) (cstar : C) (kstar : K)
    (st : SimStateF M C R K Hash Z) (d : ((M × Hash) ⊕ (Z × C)) ⊕ C) (LDCost : C → ℕ)
    (encCost : PK → M → R → ℕ) (LQCost : M → ℕ) (LOCost : M × Hash → ℕ) (LJCost : Z × C → ℕ)
    {b : ℕ} (hD : ∀ x, LDCost x ≤ b) (hQ : ∀ x, LQCost x ≤ b) (hO : ∀ x, LOCost x ≤ b)
    (hJ : ∀ x, LJCost x ≤ b) :
    AllRet (fun y => (∀ x, y.2.1.2 x ≤ b + 3) ∧ (∀ x, y.2.2.1.2 x ≤ b + 3) ∧
        (∀ x, y.2.2.2.1.2 x ≤ b + 3) ∧ (∀ x, y.2.2.2.2.1.2 x ≤ b + 3))
      (simImplFix.timed P hpk hpkCost f fCost pk cstar kstar st d LDCost encCost LQCost LOCost
        LJCost).2 := by
  rcases d with (q | q) | c <;> dsimp only [simImplFix.timed, delay] <;>
    (repeat' (first | split_ifs | split | intro _ | dsimp only [AllRet])) <;>
    refine ⟨fun x => ?_, fun x => ?_, fun x => ?_, fun x => ?_⟩ <;>
    (try split) <;> (try have := hD x) <;> (try have := hQ x) <;> (try have := hO x) <;>
    (try have := hJ x) <;> omega

/-- **Time of `redFix.timed`.** With `hpk` of cost at most `eh`, `f` of cost at most `ef`,
encryption of cost at most `ee`, the call of `run pk c` of cost at most `rc`, and the costed
adversary `run pk c k` of time at most `T` with at most `q` queries, the costed reduction
takes time at most `rc + T + ∑_{j < q} (6 j + eh + 8 ef + 6 ee + 33) + 6`. -/
theorem redFix.timeBound (P : Scheme PK SK M C R) (hpk : PK → Hash) (hpkCost : PK → ℕ)
    (f : M → R) (fCost : M → ℕ) {qRO qD : ℕ}
    (B : ROM2INDCCAAdversary PK K C (M × Hash) (K × R) (Z × C) K qRO qD)
    (run : PK → C → K → OracleAdv.Timed ((M × Hash ⊕ Z × C) ⊕ C) ((K × R ⊕ K) ⊕ Option K) Bool)
    (runCost : PK → C → K → ℕ) (encCost : PK → M → R → ℕ) {eh ef ee rc T q : ℕ}
    (hh : ∀ pk, hpkCost pk ≤ eh) (hf : ∀ m, fCost m ≤ ef) (he : ∀ pk m r, encCost pk m r ≤ ee)
    (hr : ∀ pk c k, runCost pk c k ≤ rc) (hA : ∀ pk c k, (run pk c k).TimeBound T)
    (hq : ∀ pk c k, (run pk c k).erase.IsQueryBound q) :
    (redFix.timed P hpk hpkCost f fCost B run runCost encCost).TimeBound
      (rc + T + ∑ j ∈ Finset.range q, (2 * (3 * (0 + j)) + eh + 8 * ef + 6 * ee + 33) + 5) := by
  intro pk c
  unfold redFix.timed
  dsimp only
  unfold redFix.run.tree.timed
  refine stepTimeBound_zero.2 ⟨by omega, fun kstar => ?_⟩
  have himpl : ∀ (i : ℕ) (s : ((C → Option K) × (C → ℕ)) × ((M → Option K) × (M → ℕ)) ×
        ((M × Hash → Option (K × R)) × (M × Hash → ℕ)) ×
        ((Z × C → Option K) × (Z × C → ℕ)) × Option M) (d : ((M × Hash) ⊕ (Z × C)) ⊕ C),
      ((∀ x, s.1.2 x ≤ 3 * i) ∧ (∀ x, s.2.1.2 x ≤ 3 * i) ∧ (∀ x, s.2.2.1.2 x ≤ 3 * i) ∧
        (∀ x, s.2.2.2.1.2 x ≤ 3 * i)) →
      StepTimeBound (delay 1 (simImplFix.timed P hpk hpkCost f fCost pk c kstar
          { LD := s.1.1, LQ := s.2.1.1, LO := s.2.2.1.1, LJ := s.2.2.2.1.1, found := s.2.2.2.2 }
          d s.1.2 encCost s.2.1.2 s.2.2.1.2 s.2.2.2.1.2))
        (2 * (3 * i) + eh + 8 * ef + 6 * ee + 33) ∧
      AllRet (fun y => (∀ x, y.2.1.2 x ≤ 3 * (i + 1)) ∧ (∀ x, y.2.2.1.2 x ≤ 3 * (i + 1)) ∧
          (∀ x, y.2.2.2.1.2 x ≤ 3 * (i + 1)) ∧ (∀ x, y.2.2.2.2.1.2 x ≤ 3 * (i + 1)))
        (delay 1 (simImplFix.timed P hpk hpkCost f fCost pk c kstar
          { LD := s.1.1, LQ := s.2.1.1, LO := s.2.2.1.1, LJ := s.2.2.2.1.1, found := s.2.2.2.2 }
          d s.1.2 encCost s.2.1.2 s.2.2.1.2 s.2.2.2.1.2)).2 := by
    intro i s d hs
    refine ⟨?_, ?_⟩
    · exact (stepTimeBound_delay (simImplFix.timeBound P hpk hpkCost f fCost pk c kstar _ d _
        encCost _ _ _ hh hf he hs.1 hs.2.1 hs.2.2.1 hs.2.2.2)).mono (by omega)
    · exact allRet_mono (fun y hy => ⟨fun x => (hy.1 x).trans (by omega),
        fun x => (hy.2.1 x).trans (by omega), fun x => (hy.2.2.1 x).trans (by omega),
        fun x => (hy.2.2.2 x).trans (by omega)⟩)
        (simImplFix.allRet_le P hpk hpkCost f fCost pk c kstar _ d _ encCost _ _ _
          hs.1 hs.2.1 hs.2.2.1 hs.2.2.2)
  have hX := OracleAdv.Timed.timeBound_simulateHat_inv
    (fun y : ((C → Option K) × (C → ℕ)) × ((M → Option K) × (M → ℕ)) ×
        ((M × Hash → Option (K × R)) × (M × Hash → ℕ)) ×
        ((Z × C → Option K) × (Z × C → ℕ)) × Option M =>
      ({ LD := y.1.1, LQ := y.2.1.1, LO := y.2.2.1.1, LJ := y.2.2.2.1.1, found := y.2.2.2.2 } :
        SimStateF M C R K Hash Z))
    (fun y : SimStateF M C R K Hash Z =>
      ((fun a => y.LD a, fun _ => 0), (fun a => y.LQ a, fun _ => 0),
        (fun a => y.LO a, fun _ => 0), (fun a => y.LJ a, fun _ => 0), y.found))
    (fun st a => delay 1 (simImplFix.timed P hpk hpkCost f fCost pk c kstar
      { LD := st.1.1, LQ := st.2.1.1, LO := st.2.2.1.1, LJ := st.2.2.2.1.1, found := st.2.2.2.2 }
      a st.1.2 encCost st.2.1.2 st.2.2.1.2 st.2.2.2.1.2))
    (fun i s => (∀ x, s.1.2 x ≤ 3 * i) ∧ (∀ x, s.2.1.2 x ≤ 3 * i) ∧
      (∀ x, s.2.2.1.2 x ≤ 3 * i) ∧ (∀ x, s.2.2.2.1.2 x ≤ 3 * i))
    (fun i => 2 * (3 * i) + eh + 8 * ef + 6 * ee + 33) himpl (hA pk c kstar) (hq pk c kstar) 0
    ((fun _ => none, fun _ => 0), (fun _ => none, fun _ => 0), (fun _ => none, fun _ => 0),
      (fun _ => none, fun _ => 0), none)
    ⟨fun _ => Nat.zero_le _, fun _ => Nat.zero_le _, fun _ => Nat.zero_le _,
      fun _ => Nat.zero_le _⟩
  have key : ∀ {β : Type} (X : ℕ × OracleAdv.Timed (M × C) Bool β)
      (g : β → ℕ × OracleAdv.Timed (M × C) Bool M) (N₁ N₂ : ℕ),
      StepTimeBound X (N₁ + N₂) → (∀ x, StepTimeBound (g x) 2) →
      1 + runCost pk c kstar + 1 + X.1 + (X.2.bind g).1 ≤ rc + N₁ + N₂ + 5 - 1 ∧
        (X.2.bind g).2.TimeBound
          (rc + N₁ + N₂ + 5 - 1 - (1 + runCost pk c kstar + 1 + X.1 + (X.2.bind g).1)) := by
    intro β X g N₁ N₂ hX hg
    have hB := timeBound_bind hX.2 hg
    have h1 := hX.1
    have h2 := hB.1
    have h3 := hr pk c kstar
    exact ⟨by omega, hB.2.mono (by omega)⟩
  exact key _ _ _ _ hX fun _ => ⟨le_rfl, trivial⟩

end CatCrypt.Crypto.KEM.FIPS203
