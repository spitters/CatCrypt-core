/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.SamplerCert
public import CatCryptCore.Crypto.UCOracleGame

/-!
# Sampler certificates for oracle games and their systems

An oracle game whose oracle draws its secrets from a sampler `p` is a family of oracle games
indexed by `p` (`SampledKeyedGame`). The family draws at most `m` samples per query
(`SampledKeyedGame.DrawsAtMost`) when, at every key, state and query, the answer distributions
at two samplers are at total variation distance at most `m` times the distance of the samplers.
Steps built from draws of the sampler, common randomness, branches and binds have this property
(`StepDraws` and its closure lemmas).

The run of an adversary with at most `n` queries then moves by at most `n * m` times the
distance of the samplers (`tvDist_run_le`), and so does its acceptance probability. For a
sampler certificate `c`, the system of a protocol over the game at the certified sampler
realizes the system over the game at the reference sampler with the bound
`rounds * mP * m * c.δ` at an environment with `rounds` activations, where `mP` bounds the
queries of one activation of the protocol (`realizes_samplerCert`). At the oracle protocol,
which asks one query per activation, the bound is `rounds * m * c.δ`
(`realizes_oracle_samplerCert`): this is the form of the real systems of the
Diffie–Hellman squares, which draw their secrets in the oracle of a keyed game.

## Main definitions

* `SDistr.toPMFOfMass` — a sub-distribution of mass one as a probability mass function
* `SamplerCert.pmfμ`, `SamplerCert.pmfν` — the two samplers of a certificate as `PMF`s
* `StepDraws` — a sampler-indexed distribution draws at most `m` samples
* `SampledKeyedGame`, `SampledKeyedGame.at`, `SampledKeyedGame.DrawsAtMost`

## Main results

* `StepDraws.sample`, `StepDraws.const`, `StepDraws.bind`, `StepDraws.map`, `StepDraws.ite`,
  `StepDraws.mono`, `StepDraws.sample₂` — closure of `StepDraws`
* `tvDist_run_le` — `tvDist (run O₀ B s) (run O₁ B s) ≤ n * ε` for a step distance `ε`
* `SampledKeyedGame.advantage_le` — `advantage (G.at p) (G.at q) B ≤ n * m * tvDist p q`
* `SampledKeyedGame.realizes_samplerCert`, `SampledKeyedGame.realizes_oracle_samplerCert`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto

open CatCrypt.Core CatCrypt.Prob CatCrypt.NonUniform CatCrypt.Crypto.UCConcrete
open CatCrypt.Crypto.UCTransparent
open scoped ENNReal

/-! ## Sub-distributions of mass one -/

/-- A sub-distribution that does not fail, as a probability mass function. -/
noncomputable def pmfOfNoFail {α : Type} (d : SDistr α) (hd : d none = 0) : PMF α :=
  ⟨fun a => d (some a), by
    have h := d.tsum_coe
    rw [SDistr.tsum_option_eq_add, hd, zero_add] at h
    exact ENNReal.summable.hasSum_iff.2 h⟩

theorem ofPMF_pmfOfNoFail {α : Type} (d : SDistr α) (hd : d none = 0) :
    ofPMF (pmfOfNoFail d hd) = d := by
  ext o
  cases o with
  | none => rw [ofPMF_apply_none, hd]
  | some a => rw [ofPMF_apply_some]; rfl

theorem none_eq_zero_of_mass {α : Type} {d : SDistr α} (hd : SDistr.mass d = 1) :
    d none = 0 := by
  by_contra h
  have hlt : 1 - d none < 1 := ENNReal.sub_lt_self ENNReal.one_ne_top one_ne_zero h
  unfold SDistr.mass at hd
  rw [hd] at hlt
  exact lt_irrefl _ hlt

namespace SamplerCert

variable {X : Type}

/-- The certified sampler as a probability mass function. -/
noncomputable def pmfμ (c : SamplerCert X) : PMF X :=
  pmfOfNoFail c.μ (none_eq_zero_of_mass c.mass_μ)

/-- The reference sampler as a probability mass function. -/
noncomputable def pmfν (c : SamplerCert X) : PMF X :=
  pmfOfNoFail c.ν (none_eq_zero_of_mass c.mass_ν)

theorem tvDist_pmf_le (c : SamplerCert X) : tvDist (ofPMF c.pmfμ) (ofPMF c.pmfν) ≤ c.δ := by
  rw [pmfμ, pmfν, ofPMF_pmfOfNoFail, ofPMF_pmfOfNoFail]
  exact c.tv_le

end SamplerCert

/-! ## Distributions that draw from a sampler -/

/-- **`m` draws.** The distribution `f p`, built from the sampler `p`, moves by at most `m`
times the distance of the samplers. -/
def StepDraws {X β : Type} (f : PMF X → PMF β) (m : ℕ) : Prop :=
  ∀ p q : PMF X, tvDist (ofPMF (f p)) (ofPMF (f q)) ≤ m * tvDist (ofPMF p) (ofPMF q)

namespace StepDraws

variable {X β γ : Type}

theorem ofPMF_bind (p : PMF β) (K : β → PMF γ) :
    ofPMF (p.bind K) = (ofPMF p).bind fun b => ofPMF (K b) := by
  simp only [ofPMF, SDistr.bind, PMF.map_bind, PMF.bind_map, Function.comp_def]

/-- One draw of the sampler. -/
theorem sample : StepDraws (fun p : PMF X => p) 1 := fun p q => by simp

/-- A distribution that does not read the sampler. -/
theorem const (r : PMF β) (m : ℕ) : StepDraws (fun _ : PMF X => r) m := fun p q => by
  simp [tvDist_self]

theorem mono {f : PMF X → PMF β} {m m' : ℕ} (h : StepDraws f m) (hm : m ≤ m') :
    StepDraws f m' := fun p q =>
  (h p q).trans (by gcongr)

/-- A bind of two steps adds their draws. -/
theorem bind {f : PMF X → PMF β} {g : PMF X → β → PMF γ} {m m' : ℕ} (hf : StepDraws f m)
    (hg : ∀ b, StepDraws (fun p => g p b) m') :
    StepDraws (fun p => (f p).bind (g p)) (m + m') := fun p q => by
  rw [ofPMF_bind, ofPMF_bind]
  refine (tvDist_bind_bind_le _ _ _ _ _ fun b => hg b p q).trans ?_
  push_cast
  rw [add_mul]
  exact add_le_add_left (hf p q) _

/-- A function of a step draws as the step. -/
theorem map {f : PMF X → PMF β} {m : ℕ} (hf : StepDraws f m) (g : β → γ) :
    StepDraws (fun p => (f p).map g) m := by
  exact bind (g := fun _ b => PMF.pure (g b)) hf fun b => const (PMF.pure (g b)) 0

/-- A branch on a condition that does not read the sampler. -/
theorem ite (c : Prop) [Decidable c] {f g : PMF X → PMF β} {m : ℕ} (hf : StepDraws f m)
    (hg : StepDraws g m) : StepDraws (fun p => if c then f p else g p) m := by
  by_cases h : c
  · simpa [h] using hf
  · simpa [h] using hg

/-- Two independent draws of the sampler. -/
theorem sample₂ : StepDraws (fun p : PMF X => p.bind fun a => p.map fun b => (a, b)) 2 :=
  bind sample fun a => map sample fun b => (a, b)

end StepDraws

/-! ## Runs of oracle adversaries -/

section Run

variable {D R S α : Type}

/-- **Hybrid over the queries.** Two oracles whose answers at every state and query are at
distance at most `ε` give runs of an adversary with at most `n` queries at distance at most
`n * ε`. -/
theorem tvDist_run_le (O₀ O₁ : S → D → PMF (R × S)) (ε : ℝ≥0∞)
    (hO : ∀ s d, tvDist (ofPMF (O₀ s d)) (ofPMF (O₁ s d)) ≤ ε) :
    ∀ (B : OracleAdv D R α) (n : ℕ), B.IsQueryBound n → ∀ s : S,
      tvDist (ofPMF (OracleAdv.run O₀ B s)) (ofPMF (OracleAdv.run O₁ B s)) ≤ n * ε := by
  intro B
  induction B with
  | ret a => intro n _ s; simp [tvDist_self]
  | rand p k ih =>
    intro n hB s
    simp only [OracleAdv.run_rand, StepDraws.ofPMF_bind]
    exact tvDist_bind_right_le _ _ _ _ fun b => ih b n (hB b) s
  | query d k ih =>
    intro n hB s
    cases n with
    | zero => exact hB.elim
    | succ n =>
      simp only [OracleAdv.run_query, StepDraws.ofPMF_bind]
      refine (tvDist_bind_bind_le (ofPMF (O₀ s d)) (ofPMF (O₁ s d))
        (fun x => ofPMF (OracleAdv.run O₀ (k x.1) x.2))
        (fun x => ofPMF (OracleAdv.run O₁ (k x.1) x.2)) (n * ε)
        fun x => ih x.1 n (hB x.1) x.2).trans ?_
      refine (add_le_add (hO s d) le_rfl).trans (le_of_eq ?_)
      push_cast
      ring

/-- The probability of `true` moves by at most the distance of the distributions. -/
theorem absDiff_apply_true_le (p q : PMF Bool) :
    absDiff (p true) (q true) ≤ tvDist (ofPMF p) (ofPMF q) := by
  have e : ∀ r : PMF Bool,
      ∑' x, ofPMF r x * (fun o : Option Bool => if o = some true then (1 : ℝ≥0∞) else 0) x =
        r true := fun r => by
    rw [tsum_eq_single (some true) fun o ho => by simp [ho]]
    simp
  refine le_iSup₂_of_le (fun o : Option Bool => if o = some true then (1 : ℝ≥0∞) else 0)
    (fun o => by dsimp only; split_ifs <;> simp) ?_
  rw [e p, e q]

end Run

/-! ## Oracle games over a sampler -/

/-- **An oracle game over a sampler.** The key distribution, the initial state, and for each
sampler `p` on `X` a stateful oracle with a key, which may draw from `p`. -/
structure SampledKeyedGame (X Q A : Type) where
  /-- Keys. -/
  Key : Type
  /-- Oracle states. -/
  State : Type
  /-- Key distribution. -/
  keyDist : PMF Key
  /-- The stateful oracle with a key, over the sampler. -/
  oracle : PMF X → Key → State → Q → PMF (A × State)
  /-- Initial oracle state. -/
  init : State

namespace SampledKeyedGame

variable {X Q A : Type}

/-- The game at the sampler `p`. -/
def «at» (G : SampledKeyedGame X Q A) (p : PMF X) : KeyedGame Q A where
  Key := G.Key
  State := G.State
  keyDist := G.keyDist
  oracle := G.oracle p
  init := G.init

/-- Every query of the oracle draws at most `m` samples. -/
def DrawsAtMost (G : SampledKeyedGame X Q A) (m : ℕ) : Prop :=
  ∀ k s q, StepDraws (fun p => G.oracle p k s q) m

/-- **Sampler distance in an oracle game.** An adversary with at most `n` queries has advantage
at most `n * m * tvDist p q` between the games at the samplers `p` and `q`. -/
theorem advantage_le (G : SampledKeyedGame X Q A) {m : ℕ} (hG : G.DrawsAtMost m)
    (p q : PMF X) (B : OracleAdv Q A Bool) {n : ℕ} (hB : B.IsQueryBound n) :
    KeyedGame.advantage (G.at p) (G.at q) B ≤ n * m * tvDist (ofPMF p) (ofPMF q) := by
  refine (absDiff_apply_true_le _ _).trans ?_
  simp only [«at», StepDraws.ofPMF_bind]
  refine tvDist_bind_right_le _ _ _ _ fun k => ?_
  simp only [PMF.map, StepDraws.ofPMF_bind]
  refine (tvDist_bind_le _ _ _).trans ?_
  refine (tvDist_run_le (G.oracle p k) (G.oracle q k) (m * tvDist (ofPMF p) (ofPMF q))
    (fun s d => hG k s d p q) B n hB G.init).trans ?_
  rw [mul_assoc]

/-- **Sampler certificate for the system of a protocol over the game.** If every activation of
`P` asks at most `mP` queries and every query draws at most `m` samples, the system of `P` over
the game at the certified sampler realizes the system over the game at the reference sampler
with the bound `rounds * mP * m * c.δ` at an environment with `rounds` activations. -/
theorem realizes_samplerCert {τ E O : Type} (G : SampledKeyedGame X Q A) {m : ℕ}
    (hG : G.DrawsAtMost m) (c : SamplerCert X) (P : OProt τ E O Q A) {mP : ℕ}
    (hP : ∀ t e, (P.step t e).IsQueryBound mP) :
    Realizes (P.sys (G.at c.pmfμ)) (P.sys (G.at c.pmfν))
      (fun _ Z => Z.input.rounds * mP * m * c.δ) := by
  intro _ Z
  refine (le_of_eq (P.adv_sys _ _ Z)).trans ?_
  refine (G.advantage_le hG c.pmfμ c.pmfν (P.reduction Z)
    (P.isQueryBound_reduce Z.input Z.dist hP Z.input.rounds Z.input.init P.init Z.heap)).trans ?_
  push_cast
  gcongr
  exact c.tvDist_pmf_le

/-- **Sampler certificate for the oracle system of the game.** The oracle protocol asks one
query per activation: the system of the game at the certified sampler realizes the system at
the reference sampler with the bound `rounds * m * c.δ`. -/
theorem realizes_oracle_samplerCert (G : SampledKeyedGame X Q A) {m : ℕ}
    (hG : G.DrawsAtMost m) (c : SamplerCert X) :
    Realizes ((OProt.oracle (Q := Q) (A := A)).sys (G.at c.pmfμ))
      ((OProt.oracle (Q := Q) (A := A)).sys (G.at c.pmfν))
      (fun _ Z => Z.input.rounds * m * c.δ) := by
  have h := G.realizes_samplerCert hG c (OProt.oracle (Q := Q) (A := A)) (mP := 1)
    (fun _ _ _ => trivial)
  simpa only [Nat.cast_one, mul_one] using h

end SampledKeyedGame

end CatCrypt.Crypto
