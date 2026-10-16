/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.FiatShamirROM.StatHVZK

/-!
# EUF-CMA security of Fiat–Shamir signatures in the random-oracle model: the reduction

The relation reduction `extractReduction A` for an EUF-CMA adversary `A` against
the Fiat–Shamir signature scheme over a Σ-protocol `P`. On the statement `x` it
runs the simulated EUF-CMA game of `ROMGame` (signing queries answered from `x`
by the HVZK simulator and programming of the random oracle) as a forking run
(`OracleForking.forkRun`): at every fresh random-oracle value `e₁` it continues
the run, and when the forgery `(m, (a, z₁))` verifies against that value, it runs
the rest of the game again from the same state with a fresh value `e₂`, obtaining
a second forgery `(m, (a, z₂))` at the same point. It outputs
`P.extract x a e₁ z₁ e₂ z₂`, and the default witness when the fork fails.

The reduction runs `A` at most twice, answers its queries with the simulated
oracle, and calls the special-soundness extractor once.

## Main definitions

* `hitAt x c y` — the forgery in `y` was never signed, its point is the hash entry
  at position `c`, and it verifies against that entry
* `extractW x r` — the witness computed from a forked pair
* `extractReduction A` — the relation adversary

## Main results

* `simAdvantage_sq_div_sub_le` — `ε²/(qH + 1) − ε/|Ch| ≤ relAdvantage (extractReduction A)`
  for the simulated-game advantage `ε`
* `fiatShamir_rom_eufcma` — for a special-sound Σ-protocol with perfect HVZK and
  commitment bound `γ`, and every adversary with at most `qH` hash and `qS`
  signing queries,
  `ε'·(ε'/(qH + 1) − 1/|Ch|) ≤ relAdvantage (extractReduction A)` with
  `ε' = eufcmaAdvantage A − qS·(qH + 1 + qS)·γ`

## References

* D. Pointcheval, J. Stern, *Security arguments for digital signatures and blind
  signatures*, J. Cryptology 13(3), 2000.
* M. Bellare, G. Neven, *Multi-signatures in the plain public-key model and a
  general forking lemma*, CCS 2006.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.FiatShamirROM

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.OracleForking
open scoped ENNReal

variable {P : Sigma} {M : Type} [DecidableEq M]

/-! ## Forking data for the simulated game -/

/-- The number of hash entries, which numbers the fresh random-oracle values. -/
def hashCount (s : Tables P M × Bool) : ℕ := s.1.hash.length

/-- The forgery in `y` was never signed, its point first occurs in `hash` at
position `c`, and it verifies against the value recorded there. -/
def hitAt (x : P.Stmt) (c : ℕ) (y : Forgery P M × (Tables P M × Bool)) : Bool :=
  !(y.2.1.signed.contains y.1.1) &&
    decide (findKey y.2.1.hash (y.1.2.1, y.1.1) = some c) &&
    match y.2.1.hash[c]? with
    | some p => P.verify x y.1.2.1 p.2 y.1.2.2
    | none => false

/-- The witness computed from a forked pair by the special-soundness extractor,
and the default witness when there is no second run. -/
def extractW (x : P.Stmt) (r : (Forgery P M × (Tables P M × Bool)) ×
    Option ((Forgery P M × (Tables P M × Bool)) × P.Ch × P.Ch)) : P.Wit :=
  match r.2 with
  | some (y₂, e₁, e₂) => P.extract x r.1.1.2.1 e₁ r.1.1.2.2 e₂ y₂.1.2.2
  | none => default

variable {qH qS : ℕ}

/-- The forking run of the simulated game on the statement `x`. -/
noncomputable def forkGame (A : Adversary P M qH qS) (x : P.Stmt) :
    PMF ((Forgery P M × (Tables P M × Bool)) ×
      Option ((Forgery P M × (Tables P M × Bool)) × P.Ch × P.Ch)) :=
  forkRun (simStep (G := P.toProtocol M) x) hashCount (hitAt x) (withVerify x (A.run x))
    (Protocol.Tables.empty, false)

/-- **The relation reduction.** On the statement `x`, run the simulated EUF-CMA
game as a forking run and output the extracted witness from the two forgeries and
the two random-oracle values at the fork point. -/
noncomputable def extractReduction (A : Adversary P M qH qS) : P.Stmt → PMF P.Wit :=
  fun x => (forkGame A x).map (extractW x)

/-! ## Transitions of the simulated oracle -/

section Transitions

theorem simSignOut_hash (x : P.Stmt) (t : Tables P M) (b : Bool) (m : M)
    (e : Fin 1 → P.Ch) (s : P.SimRand) : (simSignOut x t b m e s).2.1.hash = t.hash :=
  (programAll_tables t b _).1

/-- The public entries programmed by a simulated signing attempt on `m` are on
`m`. -/
theorem simSignOut_prog (x : P.Stmt) (t : Tables P M) (b : Bool) (m : M) (e : Fin 1 → P.Ch)
    (s : P.SimRand) (p : (P.Com × M) × P.Ch) (hp : p ∈ (simSignOut x t b m e s).2.1.prog) :
    p ∈ t.prog ∨ p.1.2 = m := by
  rcases (programAll_tables t b _).2.2.2.2 p hp with hp | hp
  · exact Or.inl hp
  · refine Or.inr ?_
    change p ∈ (P.transcriptView m (e 0) (P.simulate x (e 0) s)).1 at hp
    unfold Sigma.transcriptView at hp
    split at hp
    · rw [List.mem_singleton] at hp
      subst hp
      rfl
    · simp at hp

theorem simStep_plain (x₀ : P.Stmt) (s : Tables P M × Bool) (d : Query P M)
    (p : PMF (Answer P × (Tables P M × Bool))) (h : simStep x₀ s d = .plain p)
    (x : Answer P × (Tables P M × Bool)) (hx : x ∈ p.support) :
    hashCount x.2 = hashCount s := by
  cases d with
  | inl k =>
    simp only [simStep, hashStep] at h
    cases hl : s.1.lookup k with
    | some e =>
      rw [hl] at h
      cases h
      rw [PMF.support_pure, Set.mem_singleton_iff] at hx
      subst hx
      rfl
    | none =>
      rw [hl] at h
      cases h
  | inr m =>
    simp only [simStep] at h
    cases h
    obtain ⟨e, z, rfl⟩ := mem_support_sampleVec hx
    exact congrArg List.length (simSignOut_hash x₀ s.1 s.2 m e z)

theorem simStep_fresh (x₀ : P.Stmt) (s : Tables P M × Bool) (d : Query P M)
    (f : P.Ch → Answer P × (Tables P M × Bool)) (h : simStep x₀ s d = .fresh f) :
    ∃ k, ∀ e, (f e).2.1.hash = s.1.hash ++ [(k, e)] ∧ (f e).2.1.prog = s.1.prog ∧
      (f e).2.1.signed = s.1.signed := by
  cases d with
  | inl k =>
    simp only [simStep, hashStep] at h
    cases hl : s.1.lookup k with
    | some e =>
      rw [hl] at h
      cases h
    | none =>
      rw [hl] at h
      cases h
      exact ⟨k, fun e => ⟨rfl, rfl, rfl⟩⟩
  | inr m =>
    simp only [simStep] at h
    cases h

theorem simStep_hashCount_fresh (x₀ : P.Stmt) (s : Tables P M × Bool) (d : Query P M)
    (f : P.Ch → Answer P × (Tables P M × Bool)) (h : simStep x₀ s d = .fresh f)
    (e : P.Ch) : hashCount (f e).2 = hashCount s + 1 := by
  obtain ⟨k, hk⟩ := simStep_fresh x₀ s d f h
  simp [hashCount, (hk e).1]

/-- Every simulated transition extends the hash list, keeps every signing entry
on a signed message, and adds at most one hash entry per hash query. -/
theorem simStep_support (x₀ : P.Stmt) (s : Tables P M × Bool) (d : Query P M)
    (x : Answer P × (Tables P M × Bool)) (hx : x ∈ (toOracle (simStep x₀) s d).support) :
    s.1.hash <+: x.2.1.hash ∧
      ((∀ p ∈ s.1.prog, p.1.2 ∈ s.1.signed) → ∀ p ∈ x.2.1.prog, p.1.2 ∈ x.2.1.signed) ∧
      (d.isRight → x.2.1.hash = s.1.hash) ∧ x.2.1.hash.length ≤ s.1.hash.length + 1 := by
  cases d with
  | inl k =>
    simp only [toOracle, simStep, hashStep] at hx
    cases hl : s.1.lookup k with
    | some e =>
      simp only [hl, Step.toPMF, PMF.support_pure, Set.mem_singleton_iff] at hx
      subst hx
      exact ⟨List.prefix_refl _, id, fun h => by simp at h, by simp⟩
    | none =>
      simp only [hl, Step.toPMF, PMF.support_map, Set.mem_image] at hx
      obtain ⟨e, _, rfl⟩ := hx
      exact ⟨List.prefix_append _ _, id, fun h => by simp at h, by simp⟩
  | inr m =>
    simp only [toOracle, simStep, Step.toPMF] at hx
    obtain ⟨e, z, rfl⟩ := mem_support_sampleVec hx
    refine ⟨by rw [simSignOut_hash], ?_, fun _ => simSignOut_hash _ _ _ _ _ _,
      by rw [simSignOut_hash]; omega⟩
    intro hinv p hp
    change p.1.2 ∈ s.1.signed ++ [m]
    rcases simSignOut_prog x₀ s.1 s.2 m e z p hp with hp | hp
    · exact List.mem_append_left _ (hinv p hp)
    · exact List.mem_append_right _ (List.mem_singleton.mpr hp)

variable {α : Type}

/-- Along a simulated run, the hash list is extended, every signing entry stays
on a signed message, and a run asking at most `h` hash queries adds at most `h`
hash entries. -/
theorem run_sim_support (x₀ : P.Stmt) (A : OracleAdv (Query P M) (Answer P) α) (h q : ℕ)
    (hA : IsQueryBound₂ A h q) (s : Tables P M × Bool) (y : α × (Tables P M × Bool))
    (hy : y ∈ (OracleAdv.run (toOracle (simStep x₀)) A s).support) :
    s.1.hash <+: y.2.1.hash ∧
      ((∀ p ∈ s.1.prog, p.1.2 ∈ s.1.signed) → ∀ p ∈ y.2.1.prog, p.1.2 ∈ y.2.1.signed) ∧
      y.2.1.hash.length ≤ s.1.hash.length + h := by
  induction A generalizing h q s with
  | ret a =>
    rw [OracleAdv.run_ret, PMF.support_pure, Set.mem_singleton_iff] at hy
    subst hy
    exact ⟨List.prefix_refl _, id, Nat.le_add_right _ _⟩
  | rand p k ih =>
    rw [OracleAdv.run_rand, PMF.mem_support_bind_iff] at hy
    obtain ⟨b, _, hb⟩ := hy
    exact ih b h q (hA b) s hb
  | query d k ih =>
    rw [OracleAdv.run_query, PMF.mem_support_bind_iff] at hy
    obtain ⟨x, hx, hy⟩ := hy
    obtain ⟨hpx, hinvx, hrx, hlx⟩ := simStep_support x₀ s d x hx
    cases d with
    | inl key =>
      cases h with
      | zero => exact hA.elim
      | succ h =>
        obtain ⟨hpy, hinvy, hly⟩ := ih x.1 h q (hA x.1) x.2 hy
        exact ⟨hpx.trans hpy, fun hs => hinvy (hinvx hs), by omega⟩
    | inr m =>
      cases q with
      | zero => exact hA.elim
      | succ q =>
        obtain ⟨hpy, hinvy, hly⟩ := ih x.1 h q (hA x.1) x.2 hy
        have hlen := congrArg List.length (hrx rfl)
        exact ⟨hpx.trans hpy, fun hs => hinvy (hinvx hs), by omega⟩

end Transitions

/-! ## Hits -/

section Hits

theorem hitAt_lt (x : P.Stmt) (c : ℕ) (y : Forgery P M × (Tables P M × Bool))
    (h : hitAt x c y = true) : c < hashCount y.2 := by
  simp only [hitAt, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hi, _, _⟩ := List.findIdx?_eq_some_iff_getElem.mp h.1.2
  exact hi

theorem hitAt_disj (x : P.Stmt) (c c' : ℕ) (y : Forgery P M × (Tables P M × Bool))
    (h : hitAt x c y = true) (h' : hitAt x c' y = true) : c = c' := by
  simp only [hitAt, Bool.and_eq_true, decide_eq_true_eq] at h h'
  exact Option.some_injective _ (h.1.2.symm.trans h'.1.2)

/-- When every signing entry is on a signed message, the forgery wins exactly
when it hits some position of the hash list. -/
theorem wins_iff_exists_hitAt (x : P.Stmt) (y : Forgery P M × (Tables P M × Bool))
    (hinv : ∀ p ∈ y.2.1.prog, p.1.2 ∈ y.2.1.signed) :
    wins x y = true ↔ ∃ c, hitAt x c y = true := by
  obtain ⟨⟨m, a, z⟩, t, fl⟩ := y
  dsimp only at hinv
  by_cases hm : t.signed.contains m = true
  · have hm' : m ∈ t.signed := List.contains_iff_mem.mp hm
    unfold wins hitAt
    simp [hm']
  · have hprog : lookupIn t.prog (a, m) = none := by
      cases hl : lookupIn t.prog (a, m) with
      | none => rfl
      | some e =>
        exfalso
        have hsome : (lookupIn t.prog (a, m)).isSome := by rw [hl]; rfl
        obtain ⟨p, hp, hpk⟩ := List.mem_map.mp (lookupIn_isSome_mem hsome)
        have hmem := hinv p hp
        rw [hpk] at hmem
        exact hm (List.contains_iff_mem.mpr hmem)
    have hc : t.signed.contains m = false := Bool.eq_false_iff.mpr hm
    have hlk : t.lookup (a, m) = lookupIn t.hash (a, m) := by
      unfold Protocol.Tables.lookup
      rw [hprog]
      rfl
    have hv : verifyVals t.lookup x m (a, z) 1 [] = (lookupIn t.hash (a, m)).map fun e => [e] := by
      simp only [verifyVals, hlk]
      cases lookupIn t.hash (a, m) <;> rfl
    unfold wins hitAt
    dsimp only
    simp only [hc, Bool.not_false, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq]
    rw [hv]
    unfold lookupIn
    cases hf : findKey t.hash (a, m) with
    | none => simp
    | some i =>
      simp only [Option.bind_some, Option.some.injEq, exists_eq_left']
      cases hg : t.hash[i]? <;> simp

/-- A forgery that hits the position of an entry `(k, e)` of an extended hash
list is at the point `k` and verifies against `e`. -/
theorem hitAt_prefix (x : P.Stmt) (l : List ((P.Com × M) × P.Ch)) (k : P.Com × M)
    (e : P.Ch) (y : Forgery P M × (Tables P M × Bool))
    (hp : l ++ [(k, e)] <+: y.2.1.hash) (hy : hitAt x l.length y = true) :
    (y.1.2.1, y.1.1) = k ∧ P.verify x y.1.2.1 e y.1.2.2 = true := by
  have hget : y.2.1.hash[l.length]? = some (k, e) := by
    have := List.prefix_iff_getElem?.mp hp l.length (by simp)
    simpa using this
  simp only [hitAt, Bool.and_eq_true, decide_eq_true_eq, hget] at hy
  obtain ⟨⟨_, hfk⟩, hv⟩ := hy
  refine ⟨?_, hv⟩
  unfold findKey at hfk
  obtain ⟨hi, hpk, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hfk
  simp only [decide_eq_true_eq] at hpk
  have hk : y.2.1.hash[l.length] = (k, e) := (List.getElem?_eq_some_iff.mp hget).2
  rw [hk] at hpk
  exact hpk.symm

end Hits

/-! ## Probability bounds -/

section Bounds

/-- On a successful fork at any index, the reduction outputs a witness for `x`. -/
theorem rel_extractW_of_forkSucc (hSS : P.SpecialSound) (A : Adversary P M qH qS)
    (x : P.Stmt) (r : (Forgery P M × (Tables P M × Bool)) ×
      Option ((Forgery P M × (Tables P M × Bool)) × P.Ch × P.Ch))
    (hr : r ∈ (forkGame A x).support) (c : ℕ) (hc : forkSucc (hitAt x) c r = true) :
    P.rel x (extractW x r) := by
  rcases h2 : r.2 with _ | ⟨y₂, e₁, e₂⟩
  · simp [forkSucc, h2] at hc
  · simp only [forkSucc, h2, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨h₁, h₂⟩, hne⟩ := hc
    obtain ⟨s₀, d₀, f, hf, hh, hp₁, hp₂⟩ :=
      exists_fresh_of_mem_support_forkRun (simStep (G := P.toProtocol M) x) hashCount (hitAt x)
        (fun s t => s.1.hash <+: t.1.hash) (fun _ => List.prefix_refl _)
        (fun _ _ _ h h' => h.trans h') (fun s d y hy => (simStep_support x s d y hy).1)
        _ _ r y₂ e₁ e₂ hr h2
    have hc0 : c = hashCount s₀ := hitAt_disj x _ _ _ h₁ hh
    obtain ⟨k, hk⟩ := simStep_fresh x s₀ d₀ f hf
    rw [(hk e₁).1] at hp₁
    rw [(hk e₂).1] at hp₂
    subst hc0
    obtain ⟨hk₁, hv₁⟩ := hitAt_prefix x s₀.1.hash k e₁ r.1 hp₁ h₁
    obtain ⟨hk₂, hv₂⟩ := hitAt_prefix x s₀.1.hash k e₂ y₂ hp₂ h₂
    have ha : y₂.1.2.1 = r.1.1.2.1 := (Prod.ext_iff.mp (hk₂.trans hk₁.symm)).1
    rw [ha] at hv₂
    simp only [extractW, h2]
    exact hSS x _ e₁ _ e₂ _ hv₁ hv₂ hne

/-- **Forking bound for one statement.** The probability that the simulated game
is won, `ε`, satisfies `ε²/(qH + 1) − ε/|Ch|` at most the probability that the
reduction outputs a witness for `x`. -/
theorem winProb_sq_div_sub_le (hSS : P.SpecialSound) (A : Adversary P M qH qS) (x : P.Stmt) :
    (OracleAdv.run (toOracle (simStep (G := P.toProtocol M) x)) (withVerify x (A.run x))
          (Protocol.Tables.empty, false)).toOuterMeasure {y | wins x y = true} ^ 2 /
        ((qH + 1 : ℕ) : ℝ≥0∞) -
      (OracleAdv.run (toOracle (simStep (G := P.toProtocol M) x)) (withVerify x (A.run x))
          (Protocol.Tables.empty, false)).toOuterMeasure {y | wins x y = true} /
        Fintype.card P.Ch ≤
      (forkGame A x).toOuterMeasure {r | P.rel x (extractW x r)} := by
  have hB : IsQueryBound₂ (withVerify x (A.run x)) (qH + 1) qS :=
    isQueryBound₂_withVerify x _ qH qS (A.isQueryBound x)
  have hsum : ∑ c : Fin (qH + 1), accProb (simStep (G := P.toProtocol M) x) (hitAt x) c
      (withVerify x (A.run x)) (Protocol.Tables.empty, false) =
      (OracleAdv.run (toOracle (simStep (G := P.toProtocol M) x)) (withVerify x (A.run x))
        (Protocol.Tables.empty, false)).toOuterMeasure {y | wins x y = true} := by
    refine sum_fin_toOuterMeasure_eq _ _ (hitAt x) (wins x) (hitAt_disj x) fun y hy => ?_
    obtain ⟨_, hinv, hlen⟩ := run_sim_support x _ _ _ hB _ y hy
    rw [wins_iff_exists_hitAt x y (hinv (by simp [Protocol.Tables.empty]))]
    constructor
    · rintro ⟨c, hc⟩
      have hlt := hitAt_lt x c y hc
      simp only [hashCount, Protocol.Tables.empty, List.length_nil, zero_add] at hlt hlen
      exact ⟨⟨c, by omega⟩, hc⟩
    · rintro ⟨c, hc⟩
      exact ⟨c, hc⟩
  have hBN := sum_accProb_sq_div_sub_le (simStep (G := P.toProtocol M) x) hashCount (hitAt x)
    (simStep_plain x) (simStep_hashCount_fresh x) (hitAt_lt x) (hitAt_disj x) (qH + 1) (Nat.succ_pos _)
    (withVerify x (A.run x)) (Protocol.Tables.empty, false) rfl
  rw [hsum] at hBN
  refine hBN.trans (sum_forkProb_le (simStep (G := P.toProtocol M) x) hashCount (hitAt x)
    (hitAt_disj x) (qH + 1) _ _ (fun r => P.rel x (extractW x r)) fun r hr c hc => ?_)
  exact rel_extractW_of_forkSucc hSS A x r hr c hc

/-- The relation advantage of `extractReduction A` as an average over generated
pairs. -/
theorem relAdvantage_extractReduction (A : Adversary P M qH qS) :
    P.relAdvantage (extractReduction A) =
      ∑' xw, P.gen xw *
        (forkGame A xw.1).toOuterMeasure {r | P.rel xw.1 (extractW xw.1 r)} := by
  unfold Sigma.relAdvantage Sigma.relGame
  rw [prTrue_pmfGame]
  simp only [PMF.toOuterMeasure_bind_apply, extractReduction, PMF.map_comp,
    PMF.toOuterMeasure_map_apply]
  refine tsum_congr fun xw => ?_
  congr 2
  ext r
  simp

/-- **Forking bound.** For a special-sound Σ-protocol and every adversary with at
most `qH` hash queries, the advantage `ε` in the simulated game satisfies
`ε²/(qH + 1) − ε/|Ch| ≤ relAdvantage (extractReduction A)`. -/
theorem simAdvantage_sq_div_sub_le (hSS : P.SpecialSound) (A : Adversary P M qH qS) :
    simAdvantage A ^ 2 / ((qH + 1 : ℕ) : ℝ≥0∞) - simAdvantage A / Fintype.card P.Ch ≤
      P.relAdvantage (extractReduction A) := by
  unfold simAdvantage simGame
  rw [prTrue_gameDist, relAdvantage_extractReduction]
  refine (tsum_mul_sq_div_sub_le _ _ (le_of_eq (PMF.tsum_coe _))
    (fun _ => toOuterMeasure_le_one _ _) _ _).trans
    (ENNReal.tsum_le_tsum fun xw => mul_le_mul_right ?_ _)
  exact winProb_sq_div_sub_le hSS A xw.1

/-- **EUF-CMA security of Fiat–Shamir signatures in the random-oracle model.** For
a Σ-protocol `P` that is special sound, perfect HVZK and has commitment bound `γ`,
and every adversary `A` making at most `qH` hash queries and `qS` signing queries,
with `ε' = eufcmaAdvantage A − qS·(qH + 1 + qS)·γ`,

`ε'·(ε'/(qH + 1) − 1/|Ch|) ≤ relAdvantage (extractReduction A)`,

where `extractReduction A` runs `A` at most twice and calls the extractor once.
The loss `qS·(qH + 1 + qS)·γ` is the signing simulation
(`eufcmaAdvantage_le_simAdvantage`), the rest the forking bound
(`simAdvantage_sq_div_sub_le`). -/
theorem fiatShamir_rom_eufcma (hSS : P.SpecialSound) (hZK : P.PerfectHVZK) {γ : ℝ≥0∞}
    (hγ : P.CommitBound γ) (A : Adversary P M qH qS) :
    (eufcmaAdvantage A - ((qS * (qH + 1 + qS) : ℕ) : ℝ≥0∞) * γ) *
        ((eufcmaAdvantage A - ((qS * (qH + 1 + qS) : ℕ) : ℝ≥0∞) * γ) /
            ((qH + 1 : ℕ) : ℝ≥0∞) - 1 / Fintype.card P.Ch) ≤
      P.relAdvantage (extractReduction A) := by
  have hε1 : simAdvantage A ≤ 1 := by
    unfold simAdvantage simGame
    rw [prTrue_pmfGame]
    exact toOuterMeasure_le_one _ _
  exact (mul_div_tsub_le_sq_div_tsub
    (tsub_le_iff_right.mpr (eufcmaAdvantage_le_simAdvantage hZK hγ A))
    (ne_top_of_le_ne_top ENNReal.one_ne_top hε1)).trans (simAdvantage_sq_div_sub_le hSS A)

end Bounds

end CatCrypt.Crypto.FiatShamirROM
