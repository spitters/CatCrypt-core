/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.SigGame
public import CatCryptCore.Quantum.QROM.MRGenFinalH
public import CatCryptCore.Quantum.QROM.RecordRounds
public import CatCryptCore.Quantum.QROM.RecordRoundsFinal
public import CatCryptCore.Quantum.QROM.RoundOracleDep
public import CatCryptCore.Quantum.QROM.RoundsViaOracle
public import CatCryptCore.Quantum.QROM.MRGenFinalQuery
public import CatCryptCore.Quantum.QROM.QSearch
public import CatCryptCore.Quantum.QROM.FSInteractiveDefer

/-!
# Salted hash-and-sign with preimage-sampleable functions

A `SaltedPSF` is a salted hash-and-sign scheme: the signer of a message `μ` draws a salt `r`
and preimage coins, and returns a preimage of the target `H (μ, r)` under the public function
`f pk`, sampled with the secret key by `samplePre`; verification tests that the signature is
short and maps to the target. The salt and the preimage coins are independent coordinates of
the signing coins (`toQROMSig`). The simulator samples a domain element with `sampleDom` and
publishes its image.

The quantities of the security bound are defined per key pair and averaged over the key
distribution: `condDist`, the largest distance over targets `θ` between the preimage law
`samplePre sk θ` and the law of a domain sample conditioned on its image `θ`; `domDist`, the
distance between the image of a domain sample and the uniform target; `preMass`, the largest
conditional probability of a domain sample given its image.

The honest signing table of a uniform coin table has the law of the table that, at each entry
`y = (μ, τ)`, applies a conditional sampler `κ y : Tgt → Option Sig` with independent values
`κ y θ ~ samplePre sk θ` to the target at the salted point `(μ, r y)`
(`sum_signTab_eq_sum_honestTab`).

The maximal coupling of two weights `p`, `q` on a finite type is a weight on
`Bool × α × α × α`: a failure bit `b`, a common value `z` and two residuals. Its first output
(`cplFst`) has law `p`, its second (`cplSnd`) law `q`, the two agree when `b` is false, and the
pair `(b, z)` has the product law of a bit of weight `tvW p q` and the common law `commonW p q`
(`maxCouplingW_sum_fst`, `maxCouplingW_sum_snd`, `maxCouplingW_sum_resid`).

## Main definitions

* `SaltedPSF` — salted hash-and-sign with split coins
* `SaltedPSF.toQROMSig` — the scheme as a `QROMSig` on the salted points `Msg × Salt`
* `SaltedPSF.preW`, `domW`, `imgW`, `condW` — the preimage law, the domain law, its image and
  the domain law conditioned on the image
* `SaltedPSF.condDistAt`, `domDistAt`, `preMassAt` and their key averages `condDist`,
  `domDist`, `preMass`
* `SaltedPSF.samplerW`, `SaltedPSF.honestTab` — the weight of a conditional sampler and the
  signing table built from salts and samplers
* `tvW`, `commonW`, `maxCouplingW`, `cplFst`, `cplSnd` — the one-sided statistical distance of
  two weights and their maximal coupling
* `SaltedPSF.simW`, `simSamplerW`, `cplSamplerW` — the simulator's preimage law, its
  conditional sampler and the coupled sampler
* `SaltedPSF.collides`, `simTab`, `forgeGen`, `condGameAt`, `condGame` — the simulated signing
  table, the forgery adversary with recorded rounds, and the game after hop A
* `SaltedPSF.offGraph`, `forgeOffGen`, `offGameAt`, `offGame` — the event that the salt of the
  forgery differs from the salts of all entries of its message, the forgery adversary whose
  final test also requires it, and the game after hop C
* `SaltedPSF.imgN`, `oCplW`, `salted`, `progW`, `forgeImgGen`, `imgGameAt`, `imgGame` — the
  image law on the encoded targets, the coupling of a uniform oracle value with it, the salted
  points of a table, the law of the programmed oracle, the forgery adversary whose forgery test
  and signing rounds are oracle queries, and the game after hop B
* `SaltedPSF.ansTab`, `domTab`, `domOracle`, `domGameAt`, `domGame` — the table answering
  each entry with a fixed value, the table and the oracle built from domain samples at the
  salted points, and the image game sampled from uniform salts, oracle values and domain coins
* `SaltedPSF.invGame`, `SaltedPSF.collGame` — the inversion game of the public function at a
  uniform target and its collision game, as `SearchGame`s
* `fsDeferDec` — the work register and the commitment ancilla read from a basis state of the
  register of `fsDefer`
* `SaltedPSF.invTest`, `invProver`, `invVer` — the forgery adversary against the table of domain
  samples as a Fiat–Shamir prover with the forgery point as its commitment, and its verifier
* `SaltedPSF.B_invQ`, `SaltedPSF.invOut` — the inversion reduction without oracle access and the
  answer it reads from its register
* `extPerm`, `extAdv` — an adversary followed by writing a function of its final basis state
  into a fresh ancilla
* `SaltedPSF.allWin`, `forgeAllGen`, `allGameAt`, `allGame` — the winning probability of the
  forgery adversary, its form with the forgery test and the signing rounds as oracle queries,
  and the game after hop B at every point
* `SaltedPSF.domAllOracle`, `domAllGameAt`, `domAllGame` — the oracle programmed at every point
  with images of domain samples and the game sampled from salts and domain coins
* `SaltedPSF.mskTab`, `ptWin` — a signing table masked at one message and the winning test at
  one forgery point with a fixed oracle value and preimage
* `SaltedPSF.B_collQ`, `SaltedPSF.collOut` — the collision reduction without oracle access and
  the pair it reads from its register

## Main results

* `sum_pi_comp_eq` — independent coordinates with equal one-coordinate laws give equal laws of
  every function of the coordinates
* `SaltedPSF.sum_samplerW_eval` — the value of a conditional sampler at one target has the
  preimage law
* `SaltedPSF.sum_signTab_eq_sum_honestTab` — the per-entry rewrite of the coin table
* `maxCouplingW_sum_fst`, `maxCouplingW_sum_snd`, `maxCouplingW_sum_resid`,
  `maxCouplingW_sum_fail` — the marginals, the independence of the failure bit and the common
  value, and the failure mass of the maximal coupling
* `sum_prod_mul_le_of_coord` — conditioning a product weight on all coordinates but one
* `SaltedPSF.sum_cplFstTab`, `SaltedPSF.sum_cplSndTab` — the two outputs of a table of
  coupled samplers have the laws of the honest and of the simulator's samplers
* `SaltedPSF.hopCondAt`, `SaltedPSF.saltedPSF_hopCond` — hop A: replacing the preimage sampler
  by the simulator's conditional sampler (`simW`), with a signing failure at every entry that
  repeats a salt (`simTab`), costs `k · (condDist + (T - 1) / card Salt)`; the proof is
  `rounds_upto_bad_local_dep` on the maximal coupling of the two samplers at each target
* `prOutMRGen_recordGen_le_sum_tests`, `prOutMRGen_recordGen_eq_sum_fn` — the union bound and
  the partition of the final test of the recorded adversary
* `SaltedPSF.offGraphAt`, `SaltedPSF.saltedPSF_offGraph` — hop C: a winning forgery whose salt
  is the salt of an entry of its message has probability at most `T / card Salt` in the game
  after hop A. For each entry `(μ, τ)` the test reads no round outcome of `μ`
  (`prOutMRGen_recordGen_eq_prOutAvoidMRGen`), so its probability does not depend on that
  entry (`prOutMRGen_simTab_update`), whose salt is uniform (`sum_sim_salt_le`)
* `maxCouplingW_sum_bz`, `sum_prod_maxCouplingW_fail` — given the common values of independent
  couplings, the failure bit at one coordinate is set with probability `tvW p q`
* `SaltedPSF.hopImageAt`, `SaltedPSF.saltedPSF_hopImage` — hop B: programming the oracle at
  the salted points with the image law of a domain sample costs
  `4 (flatQ q k q + 2 (k + 1)) domDist^(1/2)`. The forgery test is a final query
  (`prOutMRGen_withFinalQuery_eq`) and each signing round one more query
  (`prOutMRGen_viaOracle_eq`), so `forgeImgGen` has `q + 2` queries per segment; the bound is
  `prOutMRGen_resample_gentle_fiber_le` twice, from the uniform and from the programmed oracle
  to the common values of the couplings, indexed by the table
* `sum_prod_comp_eq_of_injOn` — independent coordinates reindexed along a map injective on the
  coordinates that are read
* `SaltedPSF.imgGameAt_eq_domGameAt`, `SaltedPSF.imgGame_eq_domGame` — the image game is the
  game in which, at each salted point `x`, the oracle value and the answer of the entries of
  `x` are `(f pk (sampleDom pk d_x), sampleDom pk d_x)` for independent uniform domain coins
  `d_x`, and the oracle is uniform elsewhere; no secret key is used. Only the entries that
  repeat no salt are answered, and they have distinct salted points
  (`sum_ans_eq_sum_pt`); at one point the image law and the simulator's preimage law form the
  law of a domain sample and its image (`sum_imgN_simW`)
* `SaltedPSF.saltedPSF_qeufcma_le_img` — hops A, C and B in sequence: the EUF-CMA advantage is
  at most `imgGame` plus the three hop terms
* `prOutAt_withVerifier_eq_zero`, `prOut_withFinalB_mono`, `fsDefer_final_ofPred` — a zero
  verifier projector accepts nothing, a diagonal test is monotone, and the final projector of
  the deferred interactive game of a diagonal verifier is diagonal
* `SaltedPSF.domGameAt_le_fsInteractive` — in the game with domain samples the off-graph forgery
  point is not salted, so its oracle value is uniform and independent of the prover
  (`sum_prOutAt_unsalted`), and `fiatShamir_interactive` bounds the game by `(2 Q + 1)²` times
  the interactive game, `Q = flatQ q k q`
* `SaltedPSF.domGame_le_inv`, `SaltedPSF.saltedPSF_qeufcma_le_inv` — route I: the EUF-CMA
  advantage is at most `(2 Q + 1)²` times the inversion advantage of `B_invQ` plus the three hop
  terms. `B_invQ` samples the salts, the oracle values and the domain coins itself and places
  the challenge at the measured commitment
* `sum_prod_coord_eq` — integrating out one coordinate of independent coordinates
* `prOut_extAdv_withFinalB` — a diagonal test of `extAdv F g` is the test of `F` that reads
  `g` at the final basis state
* `SaltedPSF.hopAllAt`, `SaltedPSF.saltedPSF_hopAll` — hop B at every point: from the game after
  hop A, programming the oracle at every point with the image law costs
  `4 (flatQ q k q + 2 (k + 1)) domDist^(1/2)`; no off-graph test is used
* `SaltedPSF.allGameAt_eq_domAllGameAt`, `SaltedPSF.allGame_eq_domAllGame` — the game with the
  image law at every point is the game with a domain sample at every point
* `SaltedPSF.sum_domAll_pt_le` — a winning forgery at a point equals the domain sample of that
  point with probability at most `preMassAt`: the forgery message reads no round
  (`prOutMRGen_recordGen_congr_msg`), so the run reads the sample only through its image
* `SaltedPSF.prOutMRGen_ne_le_coll` — otherwise the forgery and the sample collide under
  `f pk`, found by `B_collQ`, when domain samples are short
* `SaltedPSF.saltedPSF_qeufcma_le_coll` — route II: the EUF-CMA advantage is at most the
  collision advantage of `B_collQ` plus `preMass`, the term of hop A and the term of hop B at
  every point
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## Laws of independent coordinates -/

/-- Independent coordinates whose one-coordinate laws agree give the same law of every
    function of all coordinates: the weights `ω i` push forward along `ρ i` to the same law as
    the weights `ω' i` along `ρ' i`. -/
theorem sum_pi_comp_eq {ι α β γ : Type} [Fintype ι] [DecidableEq ι] [Fintype α] [Fintype β]
    [Finite γ] (ω : ι → α → ℝ≥0∞) (ω' : ι → β → ℝ≥0∞) (ρ : ι → α → γ) (ρ' : ι → β → γ)
    (h : ∀ i (g : γ → ℝ≥0∞), ∑ a, ω i a * g (ρ i a) = ∑ b, ω' i b * g (ρ' i b))
    (F : (ι → γ) → ℝ≥0∞) :
    ∑ u : ι → α, (∏ i, ω i (u i)) * F (fun i => ρ i (u i)) =
      ∑ u : ι → β, (∏ i, ω' i (u i)) * F (fun i => ρ' i (u i)) := by
  have := Fintype.ofFinite γ
  classical
  have key : ∀ {δ : Type} [Fintype δ] (w : ι → δ → ℝ≥0∞) (r : ι → δ → γ),
      ∑ u : ι → δ, (∏ i, w i (u i)) * F (fun i => r i (u i)) =
        ∑ K : ι → γ, F K * ∏ i, ∑ d, w i d * (if r i d = K i then 1 else 0) := by
    intro δ _ w r
    simp_rw [Fintype.prod_sum, Finset.mul_sum, Finset.prod_mul_distrib, Fintype.prod_boole]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.sum_eq_single (fun i => r i (u i))]
    · simp [mul_comm]
    · intro K _ hK
      have hn : ¬ ∀ i, r i (u i) = K i := fun h' => hK (funext h').symm
      simp [hn]
    · simp
  rw [key ω ρ, key ω' ρ']
  refine Finset.sum_congr rfl fun K _ => ?_
  congr 1
  exact Finset.prod_congr rfl fun i _ => h i fun x => if x = K i then 1 else 0

/-- A triple sum of a product of three factors is the product of the three sums. -/
theorem sum_sum_sum_mul {α : Type} [Fintype α] (x y w : α → ℝ≥0∞) :
    ∑ z, ∑ r₁, ∑ r₂, x z * y r₁ * w r₂ = (∑ z, x z) * (∑ r, y r) * ∑ r, w r := by
  rw [Finset.sum_mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun z _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun r₁ _ => ?_
  rw [Finset.mul_sum]

/-- Independent coordinates of mass one: the value at one coordinate has the law of that
    coordinate. -/
theorem sum_prod_eval {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β]
    (w : ι → β → ℝ≥0∞) (i₀ : ι) (hw : ∀ i, ∑ b, w i b = 1) (g : β → ℝ≥0∞) :
    ∑ u : ι → β, (∏ i, w i (u i)) * g (u i₀) = ∑ b, w i₀ b * g b := by
  have h := Fintype.prod_sum fun i (b : β) => w i b * if i = i₀ then g b else 1
  rw [Finset.prod_eq_single i₀ (fun i _ hne => by simp [hne, hw]) (by simp)] at h
  simp only [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ,
    ↓reduceIte] at h
  exact h.symm

/-- Independent coordinates of mass one have total mass one. -/
theorem sum_prod_eq_one {ι β : Type} [Fintype ι] [DecidableEq ι] [Fintype β]
    (w : ι → β → ℝ≥0∞) (hw : ∀ i, ∑ b, w i b = 1) :
    ∑ u : ι → β, ∏ i, w i (u i) = 1 := by
  rw [← Fintype.prod_sum]
  simp [hw]

/-- Overwriting one coordinate of a table by every value counts each table `card α` times. -/
theorem sum_sum_update_coord {ι α : Type} [Fintype ι] [DecidableEq ι] [Fintype α] (i₀ : ι)
    (Ψ : (ι → α) → ℝ≥0∞) :
    ∑ x : α, ∑ u : ι → α, Ψ (Function.update u i₀ x) = Fintype.card α * ∑ u, Ψ u := by
  rw [← Fintype.sum_prod_type']
  let e : Equiv.Perm (α × (ι → α)) :=
    { toFun := fun p => (p.2 i₀, Function.update p.2 i₀ p.1)
      invFun := fun p => (p.2 i₀, Function.update p.2 i₀ p.1)
      left_inv := fun p => by simp
      right_inv := fun p => by simp }
  rw [show (∑ p : α × (ι → α), Ψ (Function.update p.2 i₀ p.1)) =
      ∑ p : α × (ι → α), Ψ (e p).2 from rfl, Equiv.sum_comp e (fun p => Ψ p.2),
    Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The product weight of a table overwritten at one coordinate. -/
theorem prod_update_coord {ι α : Type} [Fintype ι] [DecidableEq ι] (w : ι → α → ℝ≥0∞)
    (i₀ : ι) (u : ι → α) (x : α) :
    ∏ i, w i (Function.update u i₀ x i) = w i₀ x * ∏ i ∈ Finset.univ.erase i₀, w i (u i) := by
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ i₀), Function.update_self]
  congr 1
  exact Finset.prod_congr rfl fun i hi => by
    rw [Function.update_of_ne (Finset.ne_of_mem_erase hi)]

/-- Conditioning on all coordinates but one: if `Φ` does not read the coordinate `i₀` and, at
    every value of the other coordinates, the weight of `β` over the coordinate `i₀` is at most
    `λ` times its mass, then the weighted sum of `Φ · β` is at most `λ` times that of `Φ`. -/
theorem sum_prod_mul_le_of_coord {ι α : Type} [Fintype ι] [DecidableEq ι] [Fintype α]
    [Nonempty α] (w : ι → α → ℝ≥0∞) (i₀ : ι) (Φ β : (ι → α) → ℝ≥0∞) (lam : ℝ≥0∞)
    (hΦ : ∀ u x, Φ (Function.update u i₀ x) = Φ u)
    (hβ : ∀ u, ∑ x, w i₀ x * β (Function.update u i₀ x) ≤ lam * ∑ x, w i₀ x) :
    ∑ u, (∏ i, w i (u i)) * Φ u * β u ≤ lam * ∑ u, (∏ i, w i (u i)) * Φ u := by
  set P : (ι → α) → ℝ≥0∞ := fun u => ∏ i ∈ Finset.univ.erase i₀, w i (u i) with hP
  have hc0 : (Fintype.card α : ℝ≥0∞) ≠ 0 := by simp [Fintype.card_ne_zero]
  have hct : (Fintype.card α : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hL : (Fintype.card α : ℝ≥0∞) * ∑ u, (∏ i, w i (u i)) * Φ u * β u =
      ∑ u, P u * Φ u * ∑ x, w i₀ x * β (Function.update u i₀ x) := by
    rw [← sum_sum_update_coord i₀ (fun u => (∏ i, w i (u i)) * Φ u * β u), Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [prod_update_coord, hΦ]
    ring
  have hR : (Fintype.card α : ℝ≥0∞) * ∑ u, (∏ i, w i (u i)) * Φ u =
      ∑ u, P u * Φ u * ∑ x, w i₀ x := by
    rw [← sum_sum_update_coord i₀ (fun u => (∏ i, w i (u i)) * Φ u), Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [prod_update_coord, hΦ]
    ring
  have key : (Fintype.card α : ℝ≥0∞) * ∑ u, (∏ i, w i (u i)) * Φ u * β u ≤
      (Fintype.card α : ℝ≥0∞) * (lam * ∑ u, (∏ i, w i (u i)) * Φ u) := by
    rw [hL, mul_left_comm, hR, Finset.mul_sum]
    refine Finset.sum_le_sum fun u _ => ?_
    calc P u * Φ u * ∑ x, w i₀ x * β (Function.update u i₀ x)
        ≤ P u * Φ u * (lam * ∑ x, w i₀ x) := by gcongr; exact hβ u
      _ = _ := by ring
  exact (ENNReal.mul_le_mul_iff_right hc0 hct).mp key

/-- Reindexing independent coordinates along a map `p : ι → κ` injective on the coordinates
    that are read: if `G` reads its argument only on `N` and `p` is injective on `N`, then
    independent coordinates `o i` of the laws `w (p i)` give `G` the law that independent
    coordinates `o' x` of the laws `w x`, read at `p i`, give it. -/
theorem sum_prod_comp_eq_of_injOn {ι κ β : Type} [Fintype ι] [DecidableEq ι] [Fintype κ]
    [DecidableEq κ] [Fintype β] (p : ι → κ) (N : Finset ι) (hp : Set.InjOn p N)
    (w : κ → β → ℝ≥0∞) (hw : ∀ x, ∑ b, w x b = 1) (G : (ι → β) → ℝ≥0∞)
    (hG : ∀ o o' : ι → β, (∀ i ∈ N, o i = o' i) → G o = G o') :
    ∑ o : ι → β, (∏ i, w (p i) (o i)) * G o =
      ∑ o : κ → β, (∏ x, w x (o x)) * G (fun i => o (p i)) := by
  classical
  have hch : ∀ i ∈ N, ∀ h : ∃ j ∈ N, p j = p i, h.choose = i :=
    fun i hi h => hp h.choose_spec.1 hi h.choose_spec.2
  let Φ : (ι → β) × (κ → β) → (ι → β) × (κ → β) := fun ω =>
    (fun i => if i ∈ N then ω.2 (p i) else ω.1 i,
      fun x => if h : ∃ i ∈ N, p i = x then ω.1 h.choose else ω.2 x)
  have hΦ1 : ∀ ω, ∀ i ∈ N, (Φ ω).1 i = ω.2 (p i) := fun ω i hi => by simp [Φ, hi]
  have hΦ2 : ∀ ω, ∀ i ∈ N, (Φ ω).2 (p i) = ω.1 i := fun ω i hi => by
    have h : ∃ j ∈ N, p j = p i := ⟨i, hi, rfl⟩
    simp only [Φ, dite_eq_left h, hch i hi h]
  have hΦ3 : ∀ ω, ∀ i ∉ N, (Φ ω).1 i = ω.1 i := fun ω i hi => by simp [Φ, hi]
  have hΦ4 : ∀ ω x, x ∉ N.image p → (Φ ω).2 x = ω.2 x := fun ω x hx => by
    have h : ¬ ∃ i ∈ N, p i = x := fun ⟨i, hi, he⟩ => hx (Finset.mem_image.mpr ⟨i, hi, he⟩)
    simp only [Φ, dite_eq_right h]
  have hinv : Function.Involutive Φ := by
    intro ω
    refine Prod.ext (funext fun i => ?_) (funext fun x => ?_)
    · by_cases hi : i ∈ N
      · rw [hΦ1 _ i hi, hΦ2 _ i hi]
      · rw [hΦ3 _ i hi, hΦ3 _ i hi]
    · by_cases hx : x ∈ N.image p
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
        rw [hΦ2 _ i hi, hΦ1 _ i hi]
      · rw [hΦ4 _ x hx, hΦ4 _ x hx]
  let W : (ι → β) × (κ → β) → ℝ≥0∞ := fun ω => (∏ i, w (p i) (ω.1 i)) * ∏ x, w x (ω.2 x)
  have hW : ∀ ω, W (Φ ω) = W ω := by
    intro ω
    have h1 : ∀ o : ι → β, ∏ i, w (p i) (o i) =
        (∏ i ∈ N, w (p i) (o i)) * ∏ i ∈ Nᶜ, w (p i) (o i) :=
      fun o => (Finset.prod_mul_prod_compl N _).symm
    have h2 : ∀ o : κ → β, ∏ x, w x (o x) =
        (∏ i ∈ N, w (p i) (o (p i))) * ∏ x ∈ (N.image p)ᶜ, w x (o x) := fun o => by
      rw [← Finset.prod_image (f := fun x => w x (o x)) hp]
      exact (Finset.prod_mul_prod_compl _ _).symm
    simp only [W]
    rw [h1, h2, h1 ω.1, h2 ω.2,
      Finset.prod_congr rfl fun i hi => congrArg (w (p i)) (hΦ1 ω i hi),
      Finset.prod_congr rfl fun i hi => congrArg (w (p i)) (hΦ3 ω i (Finset.mem_compl.mp hi)),
      Finset.prod_congr rfl fun i hi => congrArg (w (p i)) (hΦ2 ω i hi),
      Finset.prod_congr rfl fun x hx => congrArg (w x) (hΦ4 ω x (Finset.mem_compl.mp hx))]
    ring
  have hL : ∑ o : ι → β, (∏ i, w (p i) (o i)) * G o = ∑ ω, W ω * G ω.1 := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun o _ => ?_
    simp only [W, mul_right_comm _ _ (G o), ← Finset.mul_sum, sum_prod_eq_one w hw, mul_one]
  have hR : ∑ o : κ → β, (∏ x, w x (o x)) * G (fun i => o (p i)) =
      ∑ ω, W ω * G (fun i => ω.2 (p i)) := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun o _ => ?_
    simp only [W, mul_assoc, ← Finset.sum_mul,
      sum_prod_eq_one (fun i => w (p i)) fun i => hw (p i), one_mul]
  rw [hL, hR, ← Equiv.sum_comp hinv.toPerm]
  refine Finset.sum_congr rfl fun ω _ => ?_
  rw [Function.Involutive.coe_toPerm, hW, hG _ _ fun i hi => hΦ1 ω i hi]

/-! ## The maximal coupling of two weights -/

section Coupling

variable {α : Type}

/-- The one-sided statistical distance `∑ a, (p a - q a)` of two weights. -/
def tvW [Fintype α] (p q : α → ℝ≥0∞) : ℝ≥0∞ := ∑ a, (p a - q a)

/-- The common law of the maximal coupling: the normalised minimum `min p q / (1 - tvW p q)`,
    and `p` when the two weights have disjoint supports. -/
def commonW [Fintype α] (p q : α → ℝ≥0∞) (z : α) : ℝ≥0∞ :=
  if tvW p q = 1 then p z else min (p z) (q z) / (1 - tvW p q)

/-- The maximal coupling of `p` and `q` on (failure bit, common value, two residuals): with
    the bit set, the common value has law `commonW p q` and the residuals the normalised
    excesses `(p - q) / tvW p q` and `(q - p) / tvW p q`; with the bit clear, both residuals
    are the common value, of weight `min p q`. -/
def maxCouplingW [Fintype α] [DecidableEq α] (p q : α → ℝ≥0∞) : Bool × α × α × α → ℝ≥0∞
  | (true, z, r₁, r₂) => commonW p q z * (p r₁ - q r₁) * (q r₂ - p r₂) * (tvW p q)⁻¹
  | (false, z, r₁, r₂) => if r₁ = z ∧ r₂ = z then min (p z) (q z) else 0

/-- The first output of the coupling: the first residual if the failure bit is set, the
    common value otherwise. -/
def cplFst (ω : Bool × α × α × α) : α := if ω.1 then ω.2.2.1 else ω.2.1

/-- The second output of the coupling: the second residual if the failure bit is set, the
    common value otherwise. -/
def cplSnd (ω : Bool × α × α × α) : α := if ω.1 then ω.2.2.2 else ω.2.1

/-- With the failure bit clear the two outputs of the coupling agree. -/
theorem cplFst_eq_cplSnd (ω : Bool × α × α × α) (h : ω.1 = false) : cplFst ω = cplSnd ω := by
  simp [cplFst, cplSnd, h]

variable [Fintype α] {p q : α → ℝ≥0∞}

/-- The one-sided distance of two probability weights is at most one. -/
theorem tvW_le_one (hp : ∑ a, p a = 1) : tvW p q ≤ 1 :=
  hp ▸ Finset.sum_le_sum fun _ _ => tsub_le_self

/-- The one-sided distance of two probability weights is finite. -/
theorem tvW_ne_top (hp : ∑ a, p a = 1) : tvW p q ≠ ∞ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (tvW_le_one hp)

/-- The minimum and the one-sided distance split the mass of `p`. -/
theorem sum_min_add_tvW (p q : α → ℝ≥0∞) : ∑ a, min (p a) (q a) + tvW p q = ∑ a, p a := by
  rw [tvW, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by rw [add_comm, tsub_add_min]

/-- The mass of the minimum of two probability weights is one minus their distance. -/
theorem sum_min_eq (hp : ∑ a, p a = 1) : ∑ a, min (p a) (q a) = 1 - tvW p q :=
  ENNReal.eq_sub_of_add_eq (tvW_ne_top hp) ((sum_min_add_tvW p q).trans hp)

/-- The one-sided distances of two probability weights agree. -/
theorem tvW_comm (hp : ∑ a, p a = 1) (hq : ∑ a, q a = 1) : tvW q p = tvW p q := by
  have h1 := sum_min_add_tvW p q
  have h2 := sum_min_add_tvW q p
  simp_rw [min_comm (q _)] at h2
  rw [hp] at h1
  rw [hq] at h2
  have hne : ∑ a, min (p a) (q a) ≠ ∞ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (h1 ▸ le_self_add)
  exact (ENNReal.add_right_inj hne).mp (h2.trans h1.symm)

/-- One minus a distance below one is not zero. -/
theorem one_sub_tvW_ne_zero (hp : ∑ a, p a = 1) (h : tvW p q ≠ 1) : 1 - tvW p q ≠ 0 :=
  (tsub_pos_of_lt (lt_of_le_of_ne (tvW_le_one hp) h)).ne'

/-- The common law has mass one. -/
theorem sum_commonW (hp : ∑ a, p a = 1) : ∑ z, commonW p q z = 1 := by
  by_cases hδ : tvW p q = 1
  · simp only [commonW, hδ, ↓reduceIte, hp]
  · simp only [commonW, hδ, ↓reduceIte, div_eq_mul_inv]
    rw [← Finset.sum_mul, sum_min_eq hp]
    exact ENNReal.mul_inv_cancel (one_sub_tvW_ne_zero hp hδ)
      (ENNReal.sub_ne_top ENNReal.one_ne_top)

/-- The bit-clear weight of the common value `z` is `1 - tvW p q` times its common law. -/
theorem min_eq_commonW (hp : ∑ a, p a = 1) (z : α) :
    min (p z) (q z) = (1 - tvW p q) * commonW p q z := by
  by_cases hδ : tvW p q = 1
  · have h0 := sum_min_eq (q := q) hp
    rw [hδ, tsub_self] at h0
    have hz := (Finset.sum_eq_zero_iff.mp h0) z (Finset.mem_univ z)
    simp [hz, hδ]
  · simp only [commonW, hδ, ↓reduceIte]
    exact (ENNReal.mul_div_cancel (one_sub_tvW_ne_zero hp hδ)
      (ENNReal.sub_ne_top ENNReal.one_ne_top)).symm

/-- The excess of `p` over `q`, against any function, times `tvW p q / tvW p q`. -/
theorem excess_mul_tvW_inv (g : α → ℝ≥0∞) (hp : ∑ a, p a = 1) :
    (∑ a, (p a - q a) * g a) * (tvW p q * (tvW p q)⁻¹) = ∑ a, (p a - q a) * g a := by
  by_cases h0 : tvW p q = 0
  · have hz := Finset.sum_eq_zero_iff.mp h0
    simp [hz]
  · rw [ENNReal.mul_inv_cancel h0 (tvW_ne_top hp), mul_one]

variable [DecidableEq α]

/-- A sum against the coupling splits by the failure bit; with the bit clear only the diagonal
    residuals carry weight. -/
theorem maxCouplingW_sum (G : Bool × α × α × α → ℝ≥0∞) :
    ∑ ω, maxCouplingW p q ω * G ω =
      ∑ z, ∑ r₁, ∑ r₂, commonW p q z * (p r₁ - q r₁) * (q r₂ - p r₂) * (tvW p q)⁻¹ *
          G (true, z, r₁, r₂) +
        ∑ z, min (p z) (q z) * G (false, z, z, z) := by
  simp only [Fintype.sum_prod_type, Fintype.sum_bool, maxCouplingW]
  congr 1
  refine Finset.sum_congr rfl fun z _ => ?_
  simp [ite_and]

/-- The failure bit and the common value are independent: summing out the residuals gives the
    weight `tvW p q` (bit set) or `1 - tvW p q` (bit clear) times the common law. -/
theorem maxCouplingW_sum_resid (hp : ∑ a, p a = 1) (hq : ∑ a, q a = 1) (b : Bool) (z : α) :
    ∑ r₁, ∑ r₂, maxCouplingW p q (b, z, r₁, r₂) =
      (if b then tvW p q else 1 - tvW p q) * commonW p q z := by
  cases b
  · simp only [maxCouplingW, Bool.false_eq_true, ↓reduceIte]
    rw [← min_eq_commonW hp]
    simp [ite_and]
  · simp only [maxCouplingW, ↓reduceIte]
    calc _ = ∑ r₁ : α, ∑ r₂ : α,
          commonW p q z * (p r₁ - q r₁) * ((q r₂ - p r₂) * (tvW p q)⁻¹) :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
      _ = commonW p q z * tvW p q * (tvW q p * (tvW p q)⁻¹) := by
          simp only [← Finset.mul_sum, ← Finset.sum_mul]
          rfl
      _ = _ := by
          rw [tvW_comm hp hq]
          by_cases h0 : tvW p q = 0
          · simp [h0]
          · rw [ENNReal.mul_inv_cancel h0 (tvW_ne_top hp), mul_one, mul_comm]

/-- The first output of the coupling has law `p`. -/
theorem maxCouplingW_sum_fst (hp : ∑ a, p a = 1) (hq : ∑ a, q a = 1) (g : α → ℝ≥0∞) :
    ∑ ω, maxCouplingW p q ω * g (cplFst ω) = ∑ a, p a * g a := by
  rw [maxCouplingW_sum]
  simp only [cplFst, Bool.false_eq_true, ↓reduceIte]
  have ht : ∑ z, ∑ r₁, ∑ r₂,
      commonW p q z * (p r₁ - q r₁) * (q r₂ - p r₂) * (tvW p q)⁻¹ * g r₁ =
        ∑ a, (p a - q a) * g a := by
    calc _ = ∑ z, ∑ r₁, ∑ r₂,
          commonW p q z * ((p r₁ - q r₁) * g r₁) * ((q r₂ - p r₂) * (tvW p q)⁻¹) :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
            Finset.sum_congr rfl fun _ _ => by ring
      _ = (∑ z, commonW p q z) * (∑ a, (p a - q a) * g a) *
          ∑ r, (q r - p r) * (tvW p q)⁻¹ := sum_sum_sum_mul _ _ _
      _ = _ := by
          rw [sum_commonW hp, one_mul, ← Finset.sum_mul]
          change (∑ a, (p a - q a) * g a) * (tvW q p * (tvW p q)⁻¹) = _
          rw [tvW_comm hp hq, excess_mul_tvW_inv g hp]
  rw [ht, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by rw [← add_mul, tsub_add_min]

/-- The second output of the coupling has law `q`. -/
theorem maxCouplingW_sum_snd (hp : ∑ a, p a = 1) (hq : ∑ a, q a = 1) (g : α → ℝ≥0∞) :
    ∑ ω, maxCouplingW p q ω * g (cplSnd ω) = ∑ a, q a * g a := by
  rw [maxCouplingW_sum]
  simp only [cplSnd, Bool.false_eq_true, ↓reduceIte]
  have ht : ∑ z, ∑ r₁, ∑ r₂,
      commonW p q z * (p r₁ - q r₁) * (q r₂ - p r₂) * (tvW p q)⁻¹ * g r₂ =
        ∑ a, (q a - p a) * g a := by
    calc _ = ∑ z, ∑ r₁, ∑ r₂,
          commonW p q z * (p r₁ - q r₁) * ((q r₂ - p r₂) * g r₂ * (tvW p q)⁻¹) :=
          Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ =>
            Finset.sum_congr rfl fun _ _ => by ring
      _ = (∑ z, commonW p q z) * (∑ a, (p a - q a)) *
          ∑ r, (q r - p r) * g r * (tvW p q)⁻¹ := sum_sum_sum_mul _ _ _
      _ = _ := by
          rw [sum_commonW hp, one_mul, ← Finset.sum_mul]
          change tvW p q * ((∑ a, (q a - p a) * g a) * (tvW p q)⁻¹) = _
          rw [← tvW_comm hp hq, ← mul_assoc, mul_comm (tvW q p), mul_assoc]
          exact excess_mul_tvW_inv g hq
  rw [ht, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun a _ => by rw [← add_mul, min_comm, tsub_add_min]

/-- The failure bit of the coupling is set with probability `tvW p q`. -/
theorem maxCouplingW_sum_fail (hp : ∑ a, p a = 1) (hq : ∑ a, q a = 1) :
    ∑ ω, maxCouplingW p q ω * (if ω.1 then 1 else 0) = tvW p q := by
  rw [maxCouplingW_sum]
  simp only [Bool.false_eq_true, ↓reduceIte, mul_zero, Finset.sum_const_zero, add_zero,
    mul_one]
  have hr := fun z => maxCouplingW_sum_resid hp hq true z
  simp only [maxCouplingW, ↓reduceIte] at hr
  rw [Finset.sum_congr rfl fun z _ => hr z, ← Finset.mul_sum, sum_commonW hp, mul_one]

/-- A sum against the coupling of a function of the failure bit and the common value is the
    sum against the product of the law of the bit and the common law. -/
theorem maxCouplingW_sum_bz (hp : ∑ a, p a = 1) (hq : ∑ a, q a = 1)
    (G : Bool → α → ℝ≥0∞) :
    ∑ ω, maxCouplingW p q ω * G ω.1 ω.2.1 =
      ∑ b, ∑ z, (if b then tvW p q else 1 - tvW p q) * commonW p q z * G b z := by
  simp only [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun z _ => ?_
  rw [← maxCouplingW_sum_resid hp hq b z, Finset.sum_mul]
  refine Finset.sum_congr rfl fun r₁ _ => ?_
  rw [Finset.sum_mul]

/-- Independent couplings at the coordinates of `ι`: given the common values, the failure bit
    at the coordinate `x` is set with probability `tvW p q`. -/
theorem sum_prod_maxCouplingW_fail {ι : Type} [Fintype ι] [DecidableEq ι]
    (hp : ∑ a, p a = 1) (hq : ∑ a, q a = 1) (x : ι) (h : ι → α) :
    ∑ u : ι → Bool × α × α × α, (∏ i, maxCouplingW p q (u i)) *
        (if (fun i => (u i).2.1) = h ∧ (u x).1 = true then 1 else 0) =
      tvW p q * ∑ u : ι → Bool × α × α × α, (∏ i, maxCouplingW p q (u i)) *
        (if (fun i => (u i).2.1) = h then 1 else 0) := by
  have hfac : ∀ e : ι → Bool × α × α × α → ℝ≥0∞,
      ∑ u : ι → Bool × α × α × α, (∏ i, maxCouplingW p q (u i)) * ∏ i, e i (u i) =
        ∏ i, ∑ ω, maxCouplingW p q ω * e i ω := by
    intro e
    rw [Fintype.prod_sum]
    simp only [Finset.prod_mul_distrib]
  have hL : ∀ u : ι → Bool × α × α × α,
      (if (fun i => (u i).2.1) = h ∧ (u x).1 = true then (1 : ℝ≥0∞) else 0) =
        ∏ i, if (u i).2.1 = h i ∧ (i = x → (u i).1 = true) then 1 else 0 := by
    intro u
    rw [Fintype.prod_boole]
    congr 1
    apply propext
    constructor
    · rintro ⟨h1, h2⟩ i
      exact ⟨congrFun h1 i, fun hi => hi ▸ h2⟩
    · intro h1
      exact ⟨funext fun i => (h1 i).1, (h1 x).2 rfl⟩
  have hR : ∀ u : ι → Bool × α × α × α,
      (if (fun i => (u i).2.1) = h then (1 : ℝ≥0∞) else 0) =
        ∏ i, if (u i).2.1 = h i then 1 else 0 := by
    intro u
    simp only [Fintype.prod_boole, funext_iff]
  have hcoord : ∀ i, ∑ ω, maxCouplingW p q ω *
      (if ω.2.1 = h i ∧ (i = x → ω.1 = true) then 1 else 0) =
        (if i = x then tvW p q else 1) *
          ∑ ω, maxCouplingW p q ω * (if ω.2.1 = h i then 1 else 0) := by
    intro i
    rw [maxCouplingW_sum_bz hp hq (fun b z => if z = h i ∧ (i = x → b = true) then 1 else 0),
      maxCouplingW_sum_bz hp hq (fun _ z => if z = h i then 1 else 0)]
    have h1 : tvW p q + (1 - tvW p q) = 1 := add_tsub_cancel_of_le (tvW_le_one hp)
    by_cases hi : i = x
    · simp only [Fintype.univ_bool, ite_mul, hi, forall_const, mul_ite, mul_one, mul_zero,
        Finset.mem_singleton, Bool.true_eq_false, not_false_eq_true, Finset.sum_insert,
        and_true, ↓reduceIte, Finset.sum_ite_eq', Finset.mem_univ, Finset.sum_singleton,
        Bool.false_eq_true, and_false, Finset.sum_const_zero, add_zero]
      rw [← add_mul, h1, one_mul]
    · simp only [hi, IsEmpty.forall_iff, and_true, mul_ite, mul_one, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte, Fintype.sum_bool, one_mul]
  have e1 := hfac fun i ω => if ω.2.1 = h i ∧ (i = x → ω.1 = true) then 1 else 0
  have e2 := hfac fun i ω => if ω.2.1 = h i then 1 else 0
  simp only [hL, hR, e1, e2, hcoord, Finset.prod_mul_distrib, Finset.prod_ite_eq',
    Finset.mem_univ, ↓reduceIte]

end Coupling

/-! ## Splitting the final test of the recorded adversary -/

section TestSplit

variable {m n w q k c a : ℕ} [NeZero n]

/-- Union bound over diagonal tests: if the indicator of `G` is at most the sum of the
    indicators of the tests `Gt t`, the acceptance probability of `G` is at most the sum of
    theirs. -/
theorem prOut_withFinalB_le_sum_tests {ι : Type} (B : QAdv m n w q) (s : Finset ι)
    (G : Fin (m * n * w) → Bool) (Gt : ι → Fin (m * n * w) → Bool)
    (h : ∀ i, (if G i then (1 : ℝ) else 0) ≤ ∑ t ∈ s, if Gt t i then 1 else 0)
    (H : Fin m → Fin n) :
    prOut (B.withFinalB G) H ≤ ∑ t ∈ s, prOut (B.withFinalB (Gt t)) H := by
  simp only [prOut_withFinalB_eq_prOutW]
  rw [← ENNReal.ofReal_sum_of_nonneg fun t _ =>
    prOutW_nonneg B (fun i => by dsimp only; split_ifs <;> simp) H]
  refine ENNReal.ofReal_le_ofReal ?_
  have hs := prOutW_sum B s (fun _ => (1 : ℝ)) (fun t i => if Gt t i then 1 else 0) H
  simp only [one_mul, one_smul] at hs
  rw [← hs]
  exact prOutW_mono B (fun i => by rw [Finset.sum_apply]; exact h i) H

/-- Partition of a diagonal test by the value of a function `φ` of the basis states. -/
theorem prOut_withFinalB_eq_sum_fn {Z : Type} [Fintype Z] [DecidableEq Z] (B : QAdv m n w q)
    (G : Fin (m * n * w) → Bool) (φ : Fin (m * n * w) → Z) (H : Fin m → Fin n) :
    prOut (B.withFinalB G) H =
      ∑ z, prOut (B.withFinalB fun i => G i && decide (φ i = z)) H := by
  simp only [prOut_withFinalB_eq_prOutW]
  rw [← ENNReal.ofReal_sum_of_nonneg fun z _ =>
    prOutW_nonneg B (fun i => by dsimp only; split_ifs <;> simp) H]
  congr 1
  have hs := prOutW_sum B Finset.univ (fun _ => (1 : ℝ))
    (fun z i => if (G i && decide (φ i = z)) then 1 else 0) H
  simp only [one_mul, one_smul] at hs
  rw [← hs]
  congr 1
  funext i
  rw [Finset.sum_apply]
  cases G i <;> simp

variable [NeZero c]

/-- Union bound over the final tests of the recorded adversary. -/
theorem prOutMRGen_recordGen_le_sum_tests {ι : Type} (A : QAdvMR m n w q k c a)
    (f : Fin c → Fin a) (s : Finset ι) (G : Fin (m * n * ancW c k w) → Bool)
    (Gt : ι → Fin (m * n * ancW c k w) → Bool)
    (h : ∀ i, (if G i then (1 : ℝ) else 0) ≤ ∑ t ∈ s, if Gt t i then 1 else 0)
    (H : Fin m → Fin n) :
    prOutMRGen (recordGen A G) H f ≤ ∑ t ∈ s, prOutMRGen (recordGen A (Gt t)) H f := by
  simp only [← prOut_withFinalB_toQAdv_eq]
  exact prOut_withFinalB_le_sum_tests _ s G Gt h H

/-- Partition of the final test of the recorded adversary by the value of a function `φ` of
    the basis states. -/
theorem prOutMRGen_recordGen_eq_sum_fn {Z : Type} [Fintype Z] [DecidableEq Z]
    (A : QAdvMR m n w q k c a) (f : Fin c → Fin a) (G : Fin (m * n * ancW c k w) → Bool)
    (φ : Fin (m * n * ancW c k w) → Z) (H : Fin m → Fin n) :
    prOutMRGen (recordGen A G) H f =
      ∑ z, prOutMRGen (recordGen A fun i => G i && decide (φ i = z)) H f := by
  simp only [← prOut_withFinalB_toQAdv_eq]
  exact prOut_withFinalB_eq_sum_fn _ G φ H

end TestSplit

/-! ## Deferred interactive provers with diagonal verifiers -/

section Deferred

open CatCrypt.Quantum.TensorProduct

variable {m n w q : ℕ}

/-- A prover whose verifier projector at `(x, θ)` is zero outputs `x` and is accepted with
    probability zero. -/
theorem prOutAt_withVerifier_eq_zero [NeZero n] (A : QAdv m n w q) (V : QVerifier m n w)
    (G : Fin m → Fin n) (x : Fin m) (θ : Fin n) (h : V.proj x θ = 0) :
    prOutAt (A.withVerifier V x θ) G x = 0 := by
  unfold prOutAt prTrue_Q
  rw [qbind_decide_eq_branch_true, outRun_branch]
  simp [QAdv.withVerifier, h]

/-- An adversary whose final projector is the diagonal projector of `G` is `A.withFinalB G`. -/
theorem QAdv.eq_withFinalB (A : QAdv m n w q) (G : Fin (m * n * w) → Bool)
    (h : A.final = diagB G) : A = A.withFinalB G := by
  cases A
  simp only [QAdv.withFinalB, QAdv.mk.injEq]
  grind

/-- The acceptance probability of a diagonal final test is monotone in the test. -/
theorem prOut_withFinalB_mono [NeZero n] (B : QAdv m n w q) {G G' : Fin (m * n * w) → Bool}
    (h : ∀ i, G i = true → G' i = true) (H : Fin m → Fin n) :
    prOut (B.withFinalB G) H ≤ prOut (B.withFinalB G') H := by
  rw [prOut_withFinalB_eq_prOutW, prOut_withFinalB_eq_prOutW]
  refine ENNReal.ofReal_le_ofReal (prOutW_mono B (fun i => ?_) H)
  cases hG : G i
  · grind
  · simp [h i hG]

/-- The ancilla projector `|y⟩⟨y|` is the diagonal projector of `z = y`. -/
theorem ancProj_eq_diagB {c : ℕ} (y : Fin c) : ancProj y = diagB fun z => decide (z = y) := by
  unfold ancProj diagB
  congr 1
  funext z
  by_cases hz : z = y
  · subst hz
    simp
  · simp [hz]

/-- The two ancillas of the register of `fsDefer`, read from a basis state: the basis state of
    the work register of the prover and the commitment ancilla. -/
def fsDeferDec (m n w : ℕ) (j : Fin (m * n * (w * m * m))) : Fin (m * n * w) × Fin m :=
  (finProdEquiv (m * n * w) m).symm ((ancE m n w m).symm
    ((finProdEquiv (m * n * (w * m)) m).symm ((ancE m n (w * m) m).symm j)).1)

variable [NeZero m] [NeZero n]

omit [NeZero m] [NeZero n] in
/-- The verifier projector controlled on the commitment ancilla of a diagonal verifier is the
    diagonal projector of the predicate at the commitment read from the ancilla. -/
theorem verProj_ofPred (acc : Fin m → Fin n → Fin (m * n * w) → Bool) (θ : Fin n) :
    verProj (QVerifier.ofPred acc) θ = diagB fun i =>
      acc ((finProdEquiv (m * n * w) m).symm ((ancE m n w m).symm i)).2 θ
        ((finProdEquiv (m * n * w) m).symm ((ancE m n w m).symm i)).1 := by
  unfold verProj
  simp only [QVerifier.ofPred, ancProj_eq_diagB, kr_diagB]
  ext i j
  simp only [diagB, Matrix.sum_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij
    simp only [ite_true]
    rw [Finset.sum_eq_single ((finProdEquiv (m * n * w) m).symm ((ancE m n w m).symm i)).2]
    · simp
    · intro x _ hx
      simp [Ne.symm hx]
    · simp
  · simp [hij]

/-- The final projector of the deferred interactive game of a diagonal verifier is the
    diagonal projector of the predicate at the decoded basis state. -/
theorem fsDefer_final_ofPred (A : QAdv m n w q) (acc : Fin m → Fin n → Fin (m * n * w) → Bool)
    (H : Fin m → Fin n) (t : Option (Fin q × Bool)) (θ : Fin n) :
    (fsDefer A (QVerifier.ofPred acc) H t θ).final =
      diagB fun j => acc (fsDeferDec m n w j).2 θ (fsDeferDec m n w j).1 := by
  change kr _ (verProj _ θ) 1 = _
  rw [verProj_ofPred, ← diagB_true, kr_diagB]
  simp [fsDeferDec]

end Deferred

/-! ## An ancilla holding a function of the final basis state -/

section Extend

open scoped Matrix
open Matrix CatCrypt.Quantum CatCrypt.Quantum.TensorProduct

variable {m n w q K : ℕ}

/-- Integrating out one coordinate: if `Ψ u b` does not read the coordinate `i₀` of `u`, the
    average of `Ψ u (u i₀)` over independent coordinates is the average of `Ψ u b` over the
    coordinates and an independent value `b` of the law of the coordinate `i₀`. -/
theorem sum_prod_coord_eq {ι α : Type} [Fintype ι] [DecidableEq ι] [Fintype α] [Nonempty α]
    (wt : ι → α → ℝ≥0∞) (i₀ : ι) (hw : ∑ b, wt i₀ b = 1) (Ψ : (ι → α) → α → ℝ≥0∞)
    (hΨ : ∀ u b x, Ψ (Function.update u i₀ b) x = Ψ u x) :
    ∑ u, (∏ i, wt i (u i)) * Ψ u (u i₀) = ∑ u, (∏ i, wt i (u i)) * ∑ b, wt i₀ b * Ψ u b := by
  have hc0 : (Fintype.card α : ℝ≥0∞) ≠ 0 := by simp [Fintype.card_ne_zero]
  have hct : (Fintype.card α : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  refine (ENNReal.mul_right_inj hc0 hct).mp ?_
  have hL : ∑ x, ∑ u, (∏ i, wt i (Function.update u i₀ x i)) *
      Ψ (Function.update u i₀ x) (Function.update u i₀ x i₀) =
        ∑ u, (∏ i ∈ Finset.univ.erase i₀, wt i (u i)) * ∑ x, wt i₀ x * Ψ u x := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [prod_update_coord, hΨ, Function.update_self]
    ring
  have hR : ∑ x, ∑ u, (∏ i, wt i (Function.update u i₀ x i)) *
      ∑ b, wt i₀ b * Ψ (Function.update u i₀ x) b =
        ∑ u, (∏ i ∈ Finset.univ.erase i₀, wt i (u i)) * ∑ b, wt i₀ b * Ψ u b := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun u _ => ?_
    simp only [prod_update_coord, hΨ]
    rw [← Finset.sum_mul, ← Finset.sum_mul, hw, one_mul]
  rw [← sum_sum_update_coord i₀ (fun u => (∏ i, wt i (u i)) * Ψ u (u i₀)),
    ← sum_sum_update_coord i₀ (fun u => (∏ i, wt i (u i)) * ∑ b, wt i₀ b * Ψ u b)]
  exact hL.trans hR.symm

/-- The permutation `(j, b) ↦ (j, b + g j)` of the register with the ancilla `Fin K` inside the
    work register. -/
def extPerm [NeZero K] (g : Fin (m * n * w) → Fin K) : Equiv.Perm (Fin (m * n * (w * K))) :=
  ((finProdEquiv (m * n * w) K).trans (ancE m n w K)).permCongr
    { toFun := fun u => (u.1, u.2 + g u.1)
      invFun := fun u => (u.1, u.2 - g u.1)
      left_inv := fun u => by simp
      right_inv := fun u => by simp }

/-- The adversary `F` on the register with the ancilla `Fin K` started in `|0⟩`, followed by
    the permutation unitary of `extPerm g`: at the end the ancilla holds `g` of the final basis
    state of `F`. Its query count is the one of `F`. -/
def extAdv [NeZero K] (F : QAdv m n w q) (g : Fin (m * n * w) → Fin K) :
    QAdv m n (w * K) q where
  U := postU (permUnitary (extPerm g)) (liftU (ancE m n w K) ∘ F.U)
  init := liftInit F.init
  final := kr (ancE m n w K) F.final 1
  final_conjTranspose := by rw [kr_conjTranspose, F.final_conjTranspose, conjTranspose_one]
  final_mul_self := by rw [kr_mul, F.final_mul_self, one_mul]

variable [NeZero n]

/-- The run operator of `extAdv F g` is the permutation unitary after the lifted run operator
    of `F`. -/
theorem runOp_extAdv [NeZero K] (F : QAdv m n w q) (g : Fin (m * n * w) → Fin K)
    (H : Fin m → Fin n) :
    runOp (extAdv F g) H =
      (permUnitary (extPerm g) : Matrix _ _ ℂ) * kr (ancE m n w K) (runOp F H) 1 := by
  unfold runOp extAdv
  simp only
  rw [chainOp_postU, oracleU_lift, chainOp_liftU]

/-- The acceptance probability of a diagonal final test is the sum of the diagonal entries of
    the final state on the accepted basis states. -/
theorem prOut_withFinalB_eq_ofReal {w' : ℕ} (F : QAdv m n w' q) (G : Fin (m * n * w') → Bool)
    (H : Fin m → Fin n) :
    prOut (F.withFinalB G) H = ENNReal.ofReal (∑ j, if G j then
      ((runOp F H * F.init.val * (runOp F H)ᴴ) j j).re else 0) := by
  unfold prOut prTrue_Q
  rw [run_branch_true]
  have hc : (F.withFinalB G).final * runOp (F.withFinalB G) H * (F.withFinalB G).init.val *
      ((F.withFinalB G).final * runOp (F.withFinalB G) H)ᴴ =
      diagB G * (runOp F H * F.init.val * (runOp F H)ᴴ) * (diagB G)ᴴ := by
    simp only [QAdv.withFinalB, runOp, conjTranspose_mul, Matrix.mul_assoc]
  rw [hc, trace_diagB_conj, Complex.re_sum]
  refine congrArg _ (Finset.sum_congr rfl fun j _ => ?_)
  split_ifs <;> simp

/-- A diagonal final test of `extAdv F g` accepts with the probability of the test of `F` that
    reads the ancilla value `g j` at the basis state `j`. -/
theorem prOut_extAdv_withFinalB [NeZero K] (F : QAdv m n w q) (g : Fin (m * n * w) → Fin K)
    (G : Fin (m * n * (w * K)) → Bool) (H : Fin m → Fin n) :
    prOut ((extAdv F g).withFinalB G) H =
      prOut (F.withFinalB fun j => G (ancE m n w K (finProdEquiv (m * n * w) K (j, g j)))) H := by
  rw [prOut_withFinalB_eq_ofReal, prOut_withFinalB_eq_ofReal]
  congr 1
  set N := runOp F H * F.init.val * (runOp F H)ᴴ with hN
  have hM : runOp (extAdv F g) H * (extAdv F g).init.val * (runOp (extAdv F g) H)ᴴ =
      (kr (ancE m n w K) N (ancProj 0)).submatrix (extPerm g).symm (extPerm g).symm := by
    have hkr : kr (ancE m n w K) (runOp F H) 1 * kr (ancE m n w K) F.init.val (ancProj 0) *
        (kr (ancE m n w K) (runOp F H) 1)ᴴ = kr (ancE m n w K) N (ancProj 0) := by
      rw [kr_conjTranspose, conjTranspose_one, kr_mul, kr_mul, one_mul, mul_one]
    rw [runOp_extAdv, ← permUnitary_conj, ← hkr]
    change _ * kr (ancE m n w K) F.init.val (ancProj 0) * _ = _
    simp only [conjTranspose_mul, Matrix.mul_assoc]
  rw [hM]
  simp only [Matrix.submatrix_apply]
  rw [← Equiv.sum_comp (extPerm g)]
  simp only [Equiv.symm_apply_apply]
  rw [← ((finProdEquiv (m * n * w) K).trans (ancE m n w K)).sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single 0]
  · simp [extPerm, Equiv.permCongr_apply, kr, kronecker_apply, ancProj]
  · intro b _ hb
    simp [kr, kronecker_apply, ancProj, hb]
  · simp

end Extend

/-! ## Salted preimage-sampleable signatures -/

/-- Salted hash-and-sign: a signature of `μ` is a salt `r` and a preimage, sampled by
    `samplePre` with the secret key, of the target `H (μ, r)` under `f pk`; it verifies when it
    is short and maps to the target. The salt and the preimage coins are independent; the
    simulator's domain sampler `sampleDom` has coins of its own. A preimage `none` is a signing
    failure. -/
structure SaltedPSF (Msg Salt PK SK Sig Tgt : Type) where
  /-- The preimage-sampling coins. -/
  PCoins : Type
  [finPCoins : Fintype PCoins]
  [nePCoins : Nonempty PCoins]
  /-- The domain-sampling coins. -/
  DCoins : Type
  [finDCoins : Fintype DCoins]
  [neDCoins : Nonempty DCoins]
  /-- The key distribution. -/
  keygen : PMF (PK × SK)
  /-- The public function. -/
  f : PK → Sig → Tgt
  /-- The shortness test of a signature. -/
  short : PK → Sig → Bool
  /-- Preimage sampling of a target with the secret key. -/
  samplePre : SK → Tgt → PCoins → Option Sig
  /-- Domain sampling with the public key. -/
  sampleDom : PK → DCoins → Sig

attribute [instance] SaltedPSF.finPCoins SaltedPSF.nePCoins SaltedPSF.finDCoins
  SaltedPSF.neDCoins

namespace SaltedPSF

variable {Msg Salt PK SK Sig Tgt : Type}

/-- The scheme as a `QROMSig` on the salted points `Msg × Salt`: the coins are a salt and
    preimage coins, a signature is the salt and a preimage of `H (μ, r)`, verification reads
    the hash at `(μ, r)` and tests shortness and the image. -/
def toQROMSig [Fintype Salt] [Nonempty Salt] [DecidableEq Tgt]
    (S : SaltedPSF Msg Salt PK SK Sig Tgt) : QROMSig Msg PK SK (Salt × Sig) (Msg × Salt) Tgt where
  Coins := Salt × S.PCoins
  keygen := S.keygen
  sign H sk μ rc := (S.samplePre sk (H (μ, rc.1)) rc.2).map fun s => (rc.1, s)
  point _ μ σ := (μ, σ.1)
  check pk _ σ θ := S.short pk σ.2 && decide (S.f pk σ.2 = θ)

variable (S : SaltedPSF Msg Salt PK SK Sig Tgt)

/-! ## The laws of the samplers -/

section Pre

variable [Fintype Sig] [DecidableEq Sig]

/-- The preimage law of the target `θ`: the weight of `o` is the fraction of preimage coins on
    which `samplePre sk θ` returns `o`. -/
def preW (sk : SK) (θ : Tgt) (o : Option Sig) : ℝ≥0∞ :=
  ∑ ρ : S.PCoins, (Fintype.card S.PCoins : ℝ≥0∞)⁻¹ * if S.samplePre sk θ ρ = o then 1 else 0

/-- An average against the preimage law is an average over the preimage coins. -/
theorem sum_preW_mul (sk : SK) (θ : Tgt) (g : Option Sig → ℝ≥0∞) :
    ∑ o, S.preW sk θ o * g o =
      ∑ ρ : S.PCoins, (Fintype.card S.PCoins : ℝ≥0∞)⁻¹ * g (S.samplePre sk θ ρ) := by
  simp only [preW, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun ρ _ => ?_
  simp

/-- The preimage law has mass one. -/
theorem sum_preW (sk : SK) (θ : Tgt) : ∑ o, S.preW sk θ o = 1 := by
  have h := S.sum_preW_mul sk θ fun _ => 1
  simp only [mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  rw [h, ENNReal.mul_inv_cancel (by simp) (ENNReal.natCast_ne_top _)]

end Pre

section Laws

variable [Fintype Sig] [DecidableEq Sig] [Fintype Tgt] [DecidableEq Tgt]

/-- The domain law: the weight of `s` is the fraction of domain coins on which `sampleDom pk`
    returns `s`. -/
def domW (pk : PK) (s : Sig) : ℝ≥0∞ :=
  ∑ d : S.DCoins, (Fintype.card S.DCoins : ℝ≥0∞)⁻¹ * if S.sampleDom pk d = s then 1 else 0

/-- The image law of a domain sample under `f pk`. -/
def imgW (pk : PK) (θ : Tgt) : ℝ≥0∞ :=
  ∑ s, S.domW pk s * if S.f pk s = θ then 1 else 0

/-- The domain law conditioned on the image `θ`, on `Option Sig` with no mass at `none`. -/
def condW (pk : PK) (θ : Tgt) : Option Sig → ℝ≥0∞
  | none => 0
  | some s => S.domW pk s * (if S.f pk s = θ then 1 else 0) / S.imgW pk θ

open Classical in
/-- The conditional preimage distance of a key pair: the largest one-sided distance over
    targets between the preimage law and the conditioned domain law, a signing failure
    counting as a difference; `1` when some target is not an image of a domain sample. -/
def condDistAt (ks : PK × SK) : ℝ≥0∞ :=
  if ∃ θ, S.imgW ks.1 θ = 0 then 1 else ⨆ θ, tvW (S.preW ks.2 θ) (S.condW ks.1 θ)

/-- The image distance of a public key: the one-sided distance between the image law and the
    uniform target. -/
def domDistAt (pk : PK) : ℝ≥0∞ :=
  tvW (S.imgW pk) fun _ => (Fintype.card Tgt : ℝ≥0∞)⁻¹

/-- The preimage mass of a public key: the largest conditional probability of a domain sample
    given its image. -/
def preMassAt (pk : PK) : ℝ≥0∞ :=
  ⨆ θ, ⨆ s, S.condW pk θ (some s)

variable [Fintype PK] [Fintype SK]

/-- The conditional preimage distance averaged over the key distribution. -/
def condDist : ℝ≥0∞ := ∑ ks, S.keygen ks * S.condDistAt ks

/-- The image distance averaged over the key distribution. -/
def domDist : ℝ≥0∞ := ∑ ks, S.keygen ks * S.domDistAt ks.1

/-- The preimage mass averaged over the key distribution. -/
def preMass : ℝ≥0∞ := ∑ ks, S.keygen ks * S.preMassAt ks.1

end Laws

/-! ## Conditional samplers and the coin-table rewrite -/

section Samplers

variable [Fintype Sig] [DecidableEq Sig] [Fintype Tgt] [DecidableEq Tgt]

/-- The weight of a conditional sampler `κ : Tgt → Option Sig`: its values are independent,
    the value at `θ` of the preimage law of `θ`. -/
def samplerW (sk : SK) (κ : Tgt → Option Sig) : ℝ≥0∞ := ∏ θ, S.preW sk θ (κ θ)

/-- The value of a conditional sampler at one target has the preimage law of that target. -/
theorem sum_samplerW_eval (sk : SK) (θ : Tgt) (g : Option Sig → ℝ≥0∞) :
    ∑ κ, S.samplerW sk κ * g (κ θ) = ∑ o, S.preW sk θ o * g o := by
  have h := Fintype.prod_sum fun θ' (o : Option Sig) =>
    S.preW sk θ' o * if θ' = θ then g o else 1
  rw [Finset.prod_eq_single θ (fun θ' _ hne => by simp [hne, S.sum_preW]) (by simp)] at h
  simp only [Finset.prod_mul_distrib, Finset.prod_ite_eq', Finset.mem_univ,
    ↓reduceIte] at h
  exact h.symm

variable {T c a : ℕ}

/-- The signing table of salts and conditional samplers: entry `y = (μ, τ)` with salt `r` and
    sampler `κ` is answered by the salt and the value of `κ` at the target `H (μ, r)`. -/
def honestTab (eQ : Msg × Fin T ≃ Fin c) (eA : Option (Salt × Sig) ≃ Fin a)
    (H : Msg × Salt → Tgt) (u : Msg × Fin T → Salt × (Tgt → Option Sig)) : Fin c → Fin a :=
  fun i => eA (((u (eQ.symm i)).2 (H ((eQ.symm i).1, (u (eQ.symm i)).1))).map
    fun s => ((u (eQ.symm i)).1, s))

variable [Fintype Msg] [DecidableEq Msg] [Fintype Salt] [Nonempty Salt]

/-- The per-entry rewrite of the coin table: the signing table of a uniform coin table has the
    law of the table of uniform salts and independent conditional samplers. -/
theorem sum_signTab_eq_sum_honestTab (eQ : Msg × Fin T ≃ Fin c)
    (eA : Option (Salt × Sig) ≃ Fin a) (sk : SK) (H : Msg × Salt → Tgt)
    (F : (Fin c → Fin a) → ℝ≥0∞) :
    ∑ R : Msg × Fin T → Salt × S.PCoins,
        (Fintype.card (Msg × Fin T → Salt × S.PCoins) : ℝ≥0∞)⁻¹ *
          F (signTab S.toQROMSig eQ eA sk H R) =
      ∑ u : Msg × Fin T → Salt × (Tgt → Option Sig),
        (∏ y, (Fintype.card Salt : ℝ≥0∞)⁻¹ * S.samplerW sk (u y).2) *
          F (honestTab eQ eA H u) := by
  have hcard : ((Fintype.card (Msg × Fin T → Salt × S.PCoins) : ℝ≥0∞))⁻¹ =
      ∏ _y : Msg × Fin T, ((Fintype.card (Salt × S.PCoins) : ℝ≥0∞))⁻¹ := by
    simp [ENNReal.inv_pow]
  rw [hcard]
  refine sum_pi_comp_eq
    (fun _ (_ : Salt × S.PCoins) => ((Fintype.card (Salt × S.PCoins) : ℝ≥0∞))⁻¹)
    (fun _ (v : Salt × (Tgt → Option Sig)) => (Fintype.card Salt : ℝ≥0∞)⁻¹ * S.samplerW sk v.2)
    (fun (y : Msg × Fin T) (rc : Salt × S.PCoins) =>
      eA ((S.samplePre sk (H (y.1, rc.1)) rc.2).map fun s => (rc.1, s)))
    (fun (y : Msg × Fin T) (v : Salt × (Tgt → Option Sig)) =>
      eA ((v.2 (H (y.1, v.1))).map fun s => (v.1, s))) ?_
    (fun t => F fun i => t (eQ.symm i))
  intro y g
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp_rw [mul_assoc, ← Finset.mul_sum]
  rw [S.sum_samplerW_eval sk (H (y.1, r)) (fun o => g (eA (o.map fun s => (r, s)))),
    S.sum_preW_mul, Fintype.card_prod, Nat.cast_mul,
    ENNReal.mul_inv (Or.inr (ENNReal.natCast_ne_top _)) (Or.inl (ENNReal.natCast_ne_top _))]
  simp_rw [mul_assoc]
  rw [Finset.mul_sum]

end Samplers

/-! ## The simulator's conditional samplers -/

section Sim

variable [Fintype Sig] [DecidableEq Sig] [Fintype Tgt] [DecidableEq Tgt]

omit [Fintype Tgt] [DecidableEq Tgt] in
/-- The domain law has mass one. -/
theorem sum_domW (pk : PK) : ∑ s, S.domW pk s = 1 := by
  simp only [domW]
  rw [Finset.sum_comm]
  simp only [← Finset.mul_sum, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte, mul_one,
    Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact ENNReal.mul_inv_cancel (by simp) (ENNReal.natCast_ne_top _)

omit [Fintype Tgt] in
/-- The image law of a target is at most one. -/
theorem imgW_le_one (pk : PK) (θ : Tgt) : S.imgW pk θ ≤ 1 :=
  (Finset.sum_le_sum fun s _ => mul_le_of_le_one_right' (by split_ifs <;> simp)).trans
    (S.sum_domW pk).le

omit [Fintype Tgt] in
/-- The conditioned domain law of an image has mass one. -/
theorem sum_condW (pk : PK) (θ : Tgt) (h : S.imgW pk θ ≠ 0) : ∑ o, S.condW pk θ o = 1 := by
  rw [Fintype.sum_option]
  simp only [condW, zero_add, div_eq_mul_inv, ← Finset.sum_mul]
  exact ENNReal.mul_inv_cancel h (ne_top_of_le_ne_top ENNReal.one_ne_top (S.imgW_le_one pk θ))

/-- The simulator's law of a preimage of `θ`: the domain law conditioned on the image `θ`,
    and a signing failure when `θ` is not an image of a domain sample. -/
def simW (pk : PK) (θ : Tgt) (o : Option Sig) : ℝ≥0∞ :=
  if S.imgW pk θ = 0 then (if o = none then 1 else 0) else S.condW pk θ o

omit [Fintype Tgt] in
/-- The simulator's law of a preimage has mass one. -/
theorem sum_simW (pk : PK) (θ : Tgt) : ∑ o, S.simW pk θ o = 1 := by
  by_cases h : S.imgW pk θ = 0
  · simp [simW, h]
  · simp only [simW, h, ↓reduceIte]
    exact S.sum_condW pk θ h

/-- The distance between the preimage law and the simulator's law at one target is at most the
    conditional preimage distance of the key pair. -/
theorem tvW_preW_simW_le (ks : PK × SK) (θ : Tgt) :
    tvW (S.preW ks.2 θ) (S.simW ks.1 θ) ≤ S.condDistAt ks := by
  classical
  unfold condDistAt
  split_ifs with h
  · exact tvW_le_one (S.sum_preW ks.2 θ)
  · push Not at h
    have he : S.simW ks.1 θ = S.condW ks.1 θ := funext fun o => by simp [simW, h θ]
    rw [he]
    exact le_iSup (fun θ' => tvW (S.preW ks.2 θ') (S.condW ks.1 θ')) θ

/-- The weight of a conditional sampler of the simulator: its values are independent, the
    value at `θ` of the simulator's law of a preimage of `θ`. -/
def simSamplerW (pk : PK) (κ : Tgt → Option Sig) : ℝ≥0∞ := ∏ θ, S.simW pk θ (κ θ)

/-- The weight of a coupled sampler: at each target the maximal coupling of the preimage law
    and the simulator's law. -/
def cplSamplerW (ks : PK × SK) (κ : Tgt → Bool × Option Sig × Option Sig × Option Sig) :
    ℝ≥0∞ :=
  ∏ θ, maxCouplingW (S.preW ks.2 θ) (S.simW ks.1 θ) (κ θ)

/-- The first outputs of a coupled sampler have the law of the honest conditional sampler. -/
theorem sum_cplSamplerW_fst (ks : PK × SK) (g : (Tgt → Option Sig) → ℝ≥0∞) :
    ∑ κ, S.cplSamplerW ks κ * g (fun θ => cplFst (κ θ)) = ∑ κ, S.samplerW ks.2 κ * g κ :=
  sum_pi_comp_eq _ (fun θ => S.preW ks.2 θ) (fun _ => cplFst) (fun _ o => o)
    (fun θ g' => maxCouplingW_sum_fst (S.sum_preW ks.2 θ) (S.sum_simW ks.1 θ) g') g

/-- The second outputs of a coupled sampler have the law of the simulator's sampler. -/
theorem sum_cplSamplerW_snd (ks : PK × SK) (g : (Tgt → Option Sig) → ℝ≥0∞) :
    ∑ κ, S.cplSamplerW ks κ * g (fun θ => cplSnd (κ θ)) = ∑ κ, S.simSamplerW ks.1 κ * g κ :=
  sum_pi_comp_eq _ (fun θ => S.simW ks.1 θ) (fun _ => cplSnd) (fun _ o => o)
    (fun θ g' => maxCouplingW_sum_snd (S.sum_preW ks.2 θ) (S.sum_simW ks.1 θ) g') g

omit [Fintype Tgt] in
/-- The maximal coupling of the preimage law and the simulator's law has mass one. -/
theorem sum_maxCouplingW (ks : PK × SK) (θ : Tgt) :
    ∑ ω, maxCouplingW (S.preW ks.2 θ) (S.simW ks.1 θ) ω = 1 := by
  have h := maxCouplingW_sum_fst (S.sum_preW ks.2 θ) (S.sum_simW ks.1 θ) fun _ => 1
  simp only [mul_one] at h
  rw [h, S.sum_preW]

/-- A coupled sampler fails at one target with the distance of the two laws. -/
theorem sum_cplSamplerW_fail (ks : PK × SK) (θ : Tgt) :
    ∑ κ, S.cplSamplerW ks κ * (if (κ θ).1 then 1 else 0) =
      tvW (S.preW ks.2 θ) (S.simW ks.1 θ) := by
  unfold cplSamplerW
  rw [sum_prod_eval _ θ (fun θ' => S.sum_maxCouplingW ks θ') fun ω => if ω.1 then 1 else 0]
  exact maxCouplingW_sum_fail (S.sum_preW ks.2 θ) (S.sum_simW ks.1 θ)

/-- The weights of coupled samplers have mass one. -/
theorem sum_cplSamplerW (ks : PK × SK) : ∑ κ, S.cplSamplerW ks κ = 1 :=
  sum_prod_eq_one _ fun θ => S.sum_maxCouplingW ks θ

variable [Fintype Salt]

/-- A uniform salt and a coupled sampler: a test of the salt has the probability it has for the
    salt alone. -/
theorem sum_salt_cpl (ks : PK × SK) (P : Salt → Prop) [DecidablePred P] :
    ∑ x : Salt × (Tgt → Bool × Option Sig × Option Sig × Option Sig),
        (Fintype.card Salt : ℝ≥0∞)⁻¹ * S.cplSamplerW ks x.2 * (if P x.1 then 1 else 0) =
      ∑ r, (Fintype.card Salt : ℝ≥0∞)⁻¹ * (if P r then 1 else 0) := by
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun r _ => ?_
  calc _ = ∑ κ, ((Fintype.card Salt : ℝ≥0∞)⁻¹ * if P r then 1 else 0) * S.cplSamplerW ks κ :=
        Finset.sum_congr rfl fun κ _ => by ring
    _ = _ := by rw [← Finset.mul_sum, S.sum_cplSamplerW, mul_one]

/-- A uniform salt and a coupled sampler have mass one. -/
theorem sum_salt_cpl_mass [Nonempty Salt] (ks : PK × SK) :
    ∑ x : Salt × (Tgt → Bool × Option Sig × Option Sig × Option Sig),
      (Fintype.card Salt : ℝ≥0∞)⁻¹ * S.cplSamplerW ks x.2 = 1 := by
  have h := S.sum_salt_cpl ks fun _ => True
  simp only [↓reduceIte, mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
  rw [h, ENNReal.mul_inv_cancel (by simp) (ENNReal.natCast_ne_top _)]

/-- With a uniform salt `r`, the coupled sampler fails at the target `θ r` with probability at
    most the conditional preimage distance. -/
theorem sum_salt_cpl_fail_le [Nonempty Salt] (ks : PK × SK) (θ : Salt → Tgt) :
    ∑ x : Salt × (Tgt → Bool × Option Sig × Option Sig × Option Sig),
        (Fintype.card Salt : ℝ≥0∞)⁻¹ * S.cplSamplerW ks x.2 *
          (if (x.2 (θ x.1)).1 then 1 else 0) ≤ S.condDistAt ks := by
  rw [Fintype.sum_prod_type]
  calc _ = ∑ r : Salt, (Fintype.card Salt : ℝ≥0∞)⁻¹ *
        tvW (S.preW ks.2 (θ r)) (S.simW ks.1 (θ r)) := by
        refine Finset.sum_congr rfl fun r _ => ?_
        simp only [mul_assoc, ← Finset.mul_sum]
        rw [S.sum_cplSamplerW_fail ks (θ r)]
    _ ≤ ∑ r : Salt, (Fintype.card Salt : ℝ≥0∞)⁻¹ * S.condDistAt ks := by
        gcongr with r
        exact S.tvW_preW_simW_le ks _
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
          ENNReal.mul_inv_cancel (by simp) (ENNReal.natCast_ne_top _), one_mul]

end Sim

/-- A uniform salt equals one of the salts `s τ` of the tags `τ` below `t` with probability at
    most `(T - 1) / card Salt`. -/
theorem sum_salt_collide_le [Fintype Salt] [DecidableEq Salt] {T : ℕ} (t : Fin T)
    (s : Fin T → Salt) :
    ∑ r : Salt, (Fintype.card Salt : ℝ≥0∞)⁻¹ * (if ∃ τ, τ < t ∧ s τ = r then 1 else 0) ≤
      ((T - 1 : ℕ) : ℝ≥0∞) * (Fintype.card Salt : ℝ≥0∞)⁻¹ := by
  calc _ ≤ ∑ r : Salt, (Fintype.card Salt : ℝ≥0∞)⁻¹ *
        ∑ τ : Fin T, (if τ ≠ t then 1 else 0) * (if s τ = r then 1 else 0) := by
        gcongr with r
        split_ifs with h
        · obtain ⟨τ, hτ, hs⟩ := h
          refine le_trans ?_ (Finset.single_le_sum (f := fun τ =>
            (if τ ≠ t then (1 : ℝ≥0∞) else 0) * (if s τ = r then 1 else 0))
            (fun _ _ => zero_le) (Finset.mem_univ τ))
          simp [hτ.ne, hs]
        · exact zero_le
    _ = (Fintype.card Salt : ℝ≥0∞)⁻¹ * ∑ τ : Fin T, (if τ ≠ t then 1 else 0) := by
        rw [← Finset.mul_sum, Finset.sum_comm]
        congr 1
        refine Finset.sum_congr rfl fun τ _ => ?_
        rw [← Finset.mul_sum]
        simp
    _ = _ := by
        rw [mul_comm]
        congr 1
        rw [Finset.sum_boole, Finset.filter_ne', Finset.card_erase_of_mem (Finset.mem_univ t),
          Finset.card_univ, Fintype.card_fin]

/-! ## Hop A: conditional preimages -/

section HopCond

variable [Fintype Sig] [DecidableEq Sig] [Fintype Tgt] [DecidableEq Tgt] [DecidableEq Salt]
  {m n w q k c a T : ℕ}

/-- Entry `y` repeats a salt: an entry of the same message with a smaller tag has the salt of
    `y`. -/
def collides {β : Type} (v : Msg × Fin T → Salt × β) (y : Msg × Fin T) : Bool :=
  decide (∃ τ : Fin T, τ < y.2 ∧ (v (y.1, τ)).1 = (v y).1)

/-- The signing table of the simulated world: the table of salts and conditional samplers, with
    a signing failure at every entry that repeats a salt. -/
def simTab (eQ : Msg × Fin T ≃ Fin c) (eA : Option (Salt × Sig) ≃ Fin a)
    (H : Msg × Salt → Tgt) (v : Msg × Fin T → Salt × (Tgt → Option Sig)) : Fin c → Fin a :=
  fun i => if collides v (eQ.symm i) then eA none else honestTab eQ eA H v i

variable [Fintype Msg] [DecidableEq Msg] [Fintype Salt] [Nonempty Salt] [NeZero n] [NeZero c]

/-- The weight of a uniform salt and a coupled sampler. -/
def cplSaltW (ks : PK × SK) (x : Salt × (Tgt → Bool × Option Sig × Option Sig × Option Sig)) :
    ℝ≥0∞ :=
  (Fintype.card Salt : ℝ≥0∞)⁻¹ * S.cplSamplerW ks x.2

/-- The salts and first outputs of a table of salts and coupled samplers. -/
def cplFstTab (u : Msg × Fin T → Salt × (Tgt → Bool × Option Sig × Option Sig × Option Sig)) :
    Msg × Fin T → Salt × (Tgt → Option Sig) :=
  fun y => ((u y).1, fun θ => cplFst ((u y).2 θ))

/-- The salts and second outputs of a table of salts and coupled samplers. -/
def cplSndTab (u : Msg × Fin T → Salt × (Tgt → Bool × Option Sig × Option Sig × Option Sig)) :
    Msg × Fin T → Salt × (Tgt → Option Sig) :=
  fun y => ((u y).1, fun θ => cplSnd ((u y).2 θ))

/-- The forgery adversary at the public key `pk` and the oracle `H`: the rounds of `A` recorded
    in the ancillas of the flattened register, with the final projector of the forgery test at
    the values of `H`. -/
def forgeGen (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c)
    (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig)) (pk : PK) (H : Fin m → Fin n) :
    QAdvMRGen m n (ancW c k w) q k c a :=
  recordGen (A.run pk) fun i =>
    forgeTest S.toQROMSig eY eQ A pk i (H (forgePoint S.toQROMSig eX A pk i))

/-- The winning probability with the simulator's conditional samplers at the public key `pk`:
    a uniform oracle, uniform salts, independent conditional samplers of the simulator, and the
    forgery test of `forgeGen` at the simulated signing table. -/
def condGameAt (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c)
    (eA : Option (Salt × Sig) ≃ Fin a) (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig))
    (pk : PK) : ℝ≥0∞ :=
  ∑ H : Fin m → Fin n, (Fintype.card (Fin m → Fin n) : ℝ≥0∞)⁻¹ *
    ∑ v : Msg × Fin T → Salt × (Tgt → Option Sig),
      (∏ y, (Fintype.card Salt : ℝ≥0∞)⁻¹ * S.simSamplerW pk (v y).2) *
        prOutMRGen (S.forgeGen eX eY eQ A pk H) H (simTab eQ eA (hashOf eX eY H) v)

omit [DecidableEq Salt] [Nonempty Salt] [NeZero n] [NeZero c] in
/-- The salts and first outputs of a table of uniform salts and coupled samplers have the law of
    the table of uniform salts and honest conditional samplers. -/
theorem sum_cplFstTab (ks : PK × SK)
    (G : (Msg × Fin T → Salt × (Tgt → Option Sig)) → ℝ≥0∞) :
    ∑ u : Msg × Fin T → Salt × (Tgt → Bool × Option Sig × Option Sig × Option Sig),
        (∏ y, S.cplSaltW ks (u y)) * G (cplFstTab u) =
      ∑ v : Msg × Fin T → Salt × (Tgt → Option Sig),
        (∏ y, (Fintype.card Salt : ℝ≥0∞)⁻¹ * S.samplerW ks.2 (v y).2) * G v := by
  have h := sum_pi_comp_eq (ι := Msg × Fin T)
    (α := Salt × (Tgt → Bool × Option Sig × Option Sig × Option Sig))
    (β := Salt × (Tgt → Option Sig)) (γ := Salt × (Tgt → Option Sig))
    (fun _ x => S.cplSaltW ks x)
    (fun _ b => (Fintype.card Salt : ℝ≥0∞)⁻¹ * S.samplerW ks.2 b.2)
    (fun _ x => (x.1, fun θ => cplFst (x.2 θ))) (fun _ b => b) ?_ G
  · exact h
  intro y g
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [cplSaltW, mul_assoc, ← Finset.mul_sum]
  exact congrArg _ (S.sum_cplSamplerW_fst ks fun κ => g (r, κ))

omit [DecidableEq Salt] [Nonempty Salt] [NeZero n] [NeZero c] in
/-- The salts and second outputs of a table of uniform salts and coupled samplers have the law
    of the table of uniform salts and the simulator's conditional samplers. -/
theorem sum_cplSndTab (ks : PK × SK)
    (G : (Msg × Fin T → Salt × (Tgt → Option Sig)) → ℝ≥0∞) :
    ∑ u : Msg × Fin T → Salt × (Tgt → Bool × Option Sig × Option Sig × Option Sig),
        (∏ y, S.cplSaltW ks (u y)) * G (cplSndTab u) =
      ∑ v : Msg × Fin T → Salt × (Tgt → Option Sig),
        (∏ y, (Fintype.card Salt : ℝ≥0∞)⁻¹ * S.simSamplerW ks.1 (v y).2) * G v := by
  have h := sum_pi_comp_eq (ι := Msg × Fin T)
    (α := Salt × (Tgt → Bool × Option Sig × Option Sig × Option Sig))
    (β := Salt × (Tgt → Option Sig)) (γ := Salt × (Tgt → Option Sig))
    (fun _ x => S.cplSaltW ks x)
    (fun _ b => (Fintype.card Salt : ℝ≥0∞)⁻¹ * S.simSamplerW ks.1 b.2)
    (fun _ x => (x.1, fun θ => cplSnd (x.2 θ))) (fun _ b => b) ?_ G
  · exact h
  intro y g
  rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [cplSaltW, mul_assoc, ← Finset.mul_sum]
  exact congrArg _ (S.sum_cplSamplerW_snd ks fun κ => g (r, κ))

/-- Hop A at one key pair: replacing the preimage sampler by the simulator's conditional
    sampler, and answering a signing failure at every entry that repeats a salt, changes the
    winning probability by at most `k · (condDistAt + (T - 1) / card Salt)`. -/
theorem hopCondAt (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c)
    (eA : Option (Salt × Sig) ≃ Fin a) (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig))
    (ks : PK × SK) :
    absDiff (∑ R : Msg × Fin T → Salt × S.PCoins,
        (Fintype.card (Msg × Fin T → Salt × S.PCoins) : ℝ≥0∞)⁻¹ *
          ∑ H : Fin m → Fin n, (Fintype.card (Fin m → Fin n) : ℝ≥0∞)⁻¹ *
            prForge S.toQROMSig eX eY eQ eA A ks H R)
      (S.condGameAt eX eY eQ eA A ks.1) ≤
      k * (S.condDistAt ks + ((T - 1 : ℕ) : ℝ≥0∞) * (Fintype.card Salt : ℝ≥0∞)⁻¹) := by
  classical
  set cH : ℝ≥0∞ := (Fintype.card (Fin m → Fin n) : ℝ≥0∞)⁻¹ with hcH
  set cS : ℝ≥0∞ := (Fintype.card Salt : ℝ≥0∞)⁻¹ with hcS
  set μ : (Fin m → Fin n) × (Msg × Fin T → Salt × (Tgt → Bool × Option Sig × Option Sig ×
      Option Sig)) → ℝ≥0∞ := fun ω => cH * ∏ y, S.cplSaltW ks (ω.2 y) with hμdef
  set lam : ℝ≥0∞ := S.condDistAt ks + ((T - 1 : ℕ) : ℝ≥0∞) * cS with hlamdef
  have hsplit : ∀ G : (Fin m → Fin n) → (Msg × Fin T →
      Salt × (Tgt → Bool × Option Sig × Option Sig × Option Sig)) → ℝ≥0∞,
      ∑ H : Fin m → Fin n, cH * ∑ u, (∏ y, S.cplSaltW ks (u y)) * G H u =
        ∑ ω, μ ω * G ω.1 ω.2 := by
    intro G
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun H _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun u _ => by rw [hμdef]; ring
  have hG0 : (∑ R : Msg × Fin T → Salt × S.PCoins,
        (Fintype.card (Msg × Fin T → Salt × S.PCoins) : ℝ≥0∞)⁻¹ *
          ∑ H : Fin m → Fin n, cH * prForge S.toQROMSig eX eY eQ eA A ks H R) =
      ∑ ω, μ ω * prOutMRGen (S.forgeGen eX eY eQ A ks.1 ω.1) ω.1
        (honestTab eQ eA (hashOf eX eY ω.1) (cplFstTab ω.2)) := by
    rw [← hsplit fun H u => prOutMRGen (S.forgeGen eX eY eQ A ks.1 H) H
      (honestTab eQ eA (hashOf eX eY H) (cplFstTab u))]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun H _ => ?_
    have h1 := S.sum_signTab_eq_sum_honestTab eQ eA ks.2 (hashOf eX eY H)
      (fun tab => prOutMRGen (S.forgeGen eX eY eQ A ks.1 H) H tab)
    rw [← S.sum_cplFstTab ks] at h1
    simp only [← Finset.mul_sum]
    rw [← h1, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun R _ => ?_
    rw [show prForge S.toQROMSig eX eY eQ eA A ks H R =
        prOutMRGen (S.forgeGen eX eY eQ A ks.1 H) H
          (signTab S.toQROMSig eQ eA ks.2 (hashOf eX eY H) R) from
      prOut_withFinalB_toQAdv_eq _ _ _ H]
    ring
  have hG1 : S.condGameAt eX eY eQ eA A ks.1 =
      ∑ ω, μ ω * prOutMRGen (S.forgeGen eX eY eQ A ks.1 ω.1) ω.1
        (simTab eQ eA (hashOf eX eY ω.1) (cplSndTab ω.2)) := by
    rw [← hsplit fun H u => prOutMRGen (S.forgeGen eX eY eQ A ks.1 H) H
      (simTab eQ eA (hashOf eX eY H) (cplSndTab u))]
    refine Finset.sum_congr rfl fun H _ => ?_
    rw [S.sum_cplSndTab ks fun v => prOutMRGen (S.forgeGen eX eY eQ A ks.1 H) H
      (simTab eQ eA (hashOf eX eY H) v)]
  have hwmass : ∀ _y : Msg × Fin T, ∑ x, S.cplSaltW ks x = 1 := fun _ => S.sum_salt_cpl_mass ks
  have hμ : ∑ ω, μ ω ≤ 1 := by
    have h := hsplit fun _ _ => 1
    simp only [mul_one, sum_prod_eq_one (fun _ x => S.cplSaltW ks x) hwmass, Finset.sum_const,
      Finset.card_univ,
      nsmul_eq_mul] at h
    have hn := NeZero.ne n
    rw [← h, hcH, ENNReal.mul_inv_cancel (by simp [hn]) (ENNReal.natCast_ne_top _)]
  set E : (Fin m → Fin n) × (Msg × Fin T →
      Salt × (Tgt → Bool × Option Sig × Option Sig × Option Sig)) → Finset (Fin c) :=
    fun ω => Finset.univ.filter fun i =>
      ((ω.2 (eQ.symm i)).2 (hashOf eX eY ω.1 ((eQ.symm i).1, (ω.2 (eQ.symm i)).1))).1 = true ∨
        collides ω.2 (eQ.symm i) = true with hE
  have hf : ∀ ω i, i ∉ E ω → simTab eQ eA (hashOf eX eY ω.1) (cplSndTab ω.2) i =
      honestTab eQ eA (hashOf eX eY ω.1) (cplFstTab ω.2) i := by
    intro ω i hi
    simp only [hE, Finset.mem_filter, Finset.mem_univ, true_and, not_or,
      Bool.not_eq_true] at hi
    have hc : collides (cplSndTab ω.2) (eQ.symm i) = false := hi.2
    simp only [simTab, hc, Bool.false_eq_true, ↓reduceIte, honestTab, cplSndTab, cplFstTab]
    rw [cplFst_eq_cplSnd _ hi.1]
  have hloc : ∀ (H : Fin m → Fin n) u x i i', i' ≠ i →
      honestTab eQ eA (hashOf eX eY H) (cplFstTab (Function.update u (eQ.symm i) x)) i' =
        honestTab eQ eA (hashOf eX eY H) (cplFstTab u) i' := by
    intro H u x i i' hi'
    have hne : eQ.symm i' ≠ eQ.symm i := fun h => hi' (eQ.symm.injective h)
    simp only [honestTab, cplFstTab, Function.update_of_ne hne]
  have hlam : ∀ (j : Fin m → Fin n) (i : Fin c) (h₀ : Fin m → Fin n) (g : Fin c → Fin a),
      ∑ ω, μ ω * (if ω.1 = j ∧ ω.1 = h₀ ∧ ∀ i', i' ≠ i →
          honestTab eQ eA (hashOf eX eY ω.1) (cplFstTab ω.2) i' = g i' then 1 else 0) *
          (if i ∈ E ω then 1 else 0) ≤
        lam * ∑ ω, μ ω * (if ω.1 = j ∧ ω.1 = h₀ ∧ ∀ i', i' ≠ i →
          honestTab eQ eA (hashOf eX eY ω.1) (cplFstTab ω.2) i' = g i' then 1 else 0) := by
    intro j i h₀ g
    set y₀ := eQ.symm i with hy₀
    have hcol : ∀ (u : Msg × Fin T →
        Salt × (Tgt → Bool × Option Sig × Option Sig × Option Sig)) x,
        collides (Function.update u y₀ x) y₀ =
        decide (∃ τ : Fin T, τ < y₀.2 ∧ (u (y₀.1, τ)).1 = x.1) := by
      intro u x
      have hne : ∀ τ : Fin T, τ < y₀.2 → (y₀.1, τ) ≠ y₀ := fun τ hτ h =>
        (ne_of_lt hτ) (congrArg Prod.snd h)
      simp only [collides, Function.update_self, decide_eq_decide]
      exact exists_congr fun τ => and_congr_right fun hτ => by
        rw [Function.update_of_ne (hne τ hτ)]
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_le_sum fun H _ => ?_
    have scale : ∀ Φ β : (Msg × Fin T →
        Salt × (Tgt → Bool × Option Sig × Option Sig × Option Sig)) → ℝ≥0∞,
        ∑ u, (∏ y, S.cplSaltW ks (u y)) * Φ u * β u ≤
          lam * ∑ u, (∏ y, S.cplSaltW ks (u y)) * Φ u →
        ∑ u, μ (H, u) * Φ u * β u ≤ lam * ∑ u, μ (H, u) * Φ u := by
      intro Φ β hk
      have e1 : ∑ u, μ (H, u) * Φ u * β u =
          cH * ∑ u, (∏ y, S.cplSaltW ks (u y)) * Φ u * β u := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun u _ => by simp only [hμdef]; ring
      have e2 : ∑ u, μ (H, u) * Φ u = cH * ∑ u, (∏ y, S.cplSaltW ks (u y)) * Φ u := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun u _ => by simp only [hμdef]; ring
      rw [e1, e2, mul_left_comm]
      gcongr
    refine scale _ _ (sum_prod_mul_le_of_coord (fun _ x => S.cplSaltW ks x) y₀ _ _ lam ?_ ?_)
    · intro u x
      have hiff : (∀ i', i' ≠ i → honestTab eQ eA (hashOf eX eY H)
            (cplFstTab (Function.update u y₀ x)) i' = g i') ↔
          (∀ i', i' ≠ i → honestTab eQ eA (hashOf eX eY H) (cplFstTab u) i' = g i') :=
        forall_congr' fun i' => imp_congr_right fun hi' => by rw [hloc H u x i i' hi']
      simp only [hiff]
    · intro u
      rw [hwmass y₀, mul_one]
      have hmem : ∀ x, (if i ∈ E (H, Function.update u y₀ x) then (1 : ℝ≥0∞) else 0) ≤
          (if (x.2 (hashOf eX eY H (y₀.1, x.1))).1 then 1 else 0) +
            (if ∃ τ : Fin T, τ < y₀.2 ∧ (u (y₀.1, τ)).1 = x.1 then 1 else 0) := by
        intro x
        have hE' : i ∈ E (H, Function.update u y₀ x) ↔
            ((x.2 (hashOf eX eY H (y₀.1, x.1))).1 = true ∨
              ∃ τ : Fin T, τ < y₀.2 ∧ (u (y₀.1, τ)).1 = x.1) := by
          simp only [hE, Finset.mem_filter, Finset.mem_univ, true_and, ← hy₀,
            Function.update_self, hcol, decide_eq_true_eq]
        by_cases hA : (x.2 (hashOf eX eY H (y₀.1, x.1))).1 = true <;>
          by_cases hB : ∃ τ : Fin T, τ < y₀.2 ∧ (u (y₀.1, τ)).1 = x.1 <;>
          simp [hE', hA, hB]
      calc ∑ x, S.cplSaltW ks x * (if i ∈ E (H, Function.update u y₀ x) then 1 else 0)
          ≤ ∑ x, (S.cplSaltW ks x * (if (x.2 (hashOf eX eY H (y₀.1, x.1))).1 then 1 else 0) +
              S.cplSaltW ks x *
                (if ∃ τ : Fin T, τ < y₀.2 ∧ (u (y₀.1, τ)).1 = x.1 then 1 else 0)) :=
            Finset.sum_le_sum fun x _ => by
              rw [← mul_add]
              gcongr
              exact hmem x
        _ = (∑ x, S.cplSaltW ks x * (if (x.2 (hashOf eX eY H (y₀.1, x.1))).1 then 1 else 0)) +
              ∑ x, S.cplSaltW ks x *
                (if ∃ τ : Fin T, τ < y₀.2 ∧ (u (y₀.1, τ)).1 = x.1 then 1 else 0) :=
            Finset.sum_add_distrib
        _ ≤ lam := by
            refine add_le_add ?_ ?_
            · simpa only [cplSaltW] using
                S.sum_salt_cpl_fail_le ks fun r => hashOf eX eY H (y₀.1, r)
            · have h2 := S.sum_salt_cpl ks fun r =>
                ∃ τ : Fin T, τ < y₀.2 ∧ (u (y₀.1, τ)).1 = r
              simp only [cplSaltW] at h2 ⊢
              rw [h2]
              exact sum_salt_collide_le y₀.2 fun τ => (u (y₀.1, τ)).1
  rw [hG0, hG1]
  exact rounds_upto_bad_local_dep (S.forgeGen eX eY eQ A ks.1) Prod.fst Prod.fst
    (fun ω => honestTab eQ eA (hashOf eX eY ω.1) (cplFstTab ω.2))
    (fun ω => simTab eQ eA (hashOf eX eY ω.1) (cplSndTab ω.2)) E μ lam hμ hf hlam

variable [Fintype PK] [Fintype SK]

/-- The winning probability with the simulator's conditional samplers, averaged over the key
    distribution. -/
def condGame (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c)
    (eA : Option (Salt × Sig) ≃ Fin a) (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig)) :
    ℝ≥0∞ :=
  ∑ ks, S.keygen ks * S.condGameAt eX eY eQ eA A ks.1

/-- Hop A: the EUF-CMA advantage and the winning probability with the simulator's conditional
    samplers (`condGame`) differ by at most `k · (condDist + (T - 1) / card Salt)`. -/
theorem saltedPSF_hopCond (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n)
    (eQ : Msg × Fin T ≃ Fin c) (eA : Option (Salt × Sig) ≃ Fin a)
    (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig)) :
    absDiff (qEUFCMAAdvantage S.toQROMSig eX eY eQ eA A) (S.condGame eX eY eQ eA A) ≤
      k * (S.condDist + ((T - 1 : ℕ) : ℝ≥0∞) * (Fintype.card Salt : ℝ≥0∞)⁻¹) := by
  have hkey : ∑ ks, S.keygen ks = 1 := by
    rw [← tsum_fintype (L := SummationFilter.unconditional (PK × SK))]
    exact S.keygen.tsum_coe
  unfold qEUFCMAAdvantage condGame
  refine (absDiff_sum_le _ _).trans ?_
  calc ∑ ks, absDiff (S.keygen ks * _) (S.keygen ks * S.condGameAt eX eY eQ eA A ks.1)
      ≤ ∑ ks, S.keygen ks * (k * (S.condDistAt ks +
          ((T - 1 : ℕ) : ℝ≥0∞) * (Fintype.card Salt : ℝ≥0∞)⁻¹)) :=
        Finset.sum_le_sum fun ks _ =>
          (absDiff_mul_left_le _ _ _).trans (by gcongr; exact S.hopCondAt eX eY eQ eA A ks)
    _ = _ := by
        simp only [condDist, mul_add, Finset.sum_add_distrib, Finset.mul_sum]
        congr 1
        · exact Finset.sum_congr rfl fun ks _ => by ring
        · rw [← Finset.sum_mul, hkey, one_mul]

end HopCond

/-! ## Hop C: the forgery off the salted graph -/

section OffGraph

variable [Fintype Sig] [DecidableEq Sig] [Fintype Tgt] [DecidableEq Tgt] [DecidableEq Salt]
  {m n w q k c a T : ℕ}

/-- The forgery of the basis state `i` is off the salted graph of the table `v`: its salt
    differs from the salt of every entry of its message. -/
def offGraph {β : Type} (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig))
    (v : Msg × Fin T → Salt × β) (i : Fin (m * n * ancW c k w)) : Bool :=
  decide (∀ τ : Fin T, (v ((A.forge i).1, τ)).1 ≠ (A.forge i).2.1)

variable [Fintype Msg] [DecidableEq Msg] [Fintype Salt] [Nonempty Salt] [NeZero n] [NeZero c]

/-- The forgery adversary of `forgeGen` whose final test also requires the forgery to be off
    the salted graph of the table `v`. -/
def forgeOffGen (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c)
    (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig)) (pk : PK) (H : Fin m → Fin n)
    (v : Msg × Fin T → Salt × (Tgt → Option Sig)) : QAdvMRGen m n (ancW c k w) q k c a :=
  recordGen (A.run pk) fun i =>
    forgeTest S.toQROMSig eY eQ A pk i (H (forgePoint S.toQROMSig eX A pk i)) &&
      offGraph A v i

/-- The winning probability of `condGameAt` with the forgery off the salted graph. -/
def offGameAt (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c)
    (eA : Option (Salt × Sig) ≃ Fin a) (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig))
    (pk : PK) : ℝ≥0∞ :=
  ∑ H : Fin m → Fin n, (Fintype.card (Fin m → Fin n) : ℝ≥0∞)⁻¹ *
    ∑ v : Msg × Fin T → Salt × (Tgt → Option Sig),
      (∏ y, (Fintype.card Salt : ℝ≥0∞)⁻¹ * S.simSamplerW pk (v y).2) *
        prOutMRGen (S.forgeOffGen eX eY eQ A pk H v) H (simTab eQ eA (hashOf eX eY H) v)

omit [DecidableEq Salt] [Fintype Msg] [DecidableEq Msg] [NeZero n] [NeZero c] in
/-- A uniform salt and a sampler of the simulator have mass one. -/
theorem sum_salt_sim_mass (pk : PK) :
    ∑ x : Salt × (Tgt → Option Sig),
      (Fintype.card Salt : ℝ≥0∞)⁻¹ * S.simSamplerW pk x.2 = 1 := by
  have hs : ∑ κ, S.simSamplerW pk κ = 1 := sum_prod_eq_one _ fun θ => S.sum_simW pk θ
  rw [Fintype.sum_prod_type]
  simp only [← Finset.mul_sum, hs, mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact ENNReal.mul_inv_cancel (by simp) (ENNReal.natCast_ne_top _)

omit [Fintype Msg] [DecidableEq Msg] [Nonempty Salt] [NeZero n] [NeZero c] in
/-- A uniform salt and a sampler of the simulator: the salt equals a fixed salt `r` with
    probability `1 / card Salt`. -/
theorem sum_salt_sim_eq (pk : PK) (r : Salt) :
    ∑ x : Salt × (Tgt → Option Sig),
      (Fintype.card Salt : ℝ≥0∞)⁻¹ * S.simSamplerW pk x.2 * (if x.1 = r then 1 else 0) =
      (Fintype.card Salt : ℝ≥0∞)⁻¹ := by
  have hs : ∑ κ, S.simSamplerW pk κ = 1 := sum_prod_eq_one _ fun θ => S.sum_simW pk θ
  rw [Fintype.sum_prod_type]
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single r (fun b _ hb => by simp [hb]) (by simp)]
  simp only [↓reduceIte, ← Finset.mul_sum, hs, mul_one]

omit [Fintype Sig] [DecidableEq Sig] [Fintype Tgt] [DecidableEq Tgt] [Fintype Msg]
  [Fintype Salt] [Nonempty Salt] in
/-- A final test of the recorded adversary that reads no round outcome of the message `μ` has
    the same acceptance probability at the simulated signing tables of two tables of salts and
    samplers that differ at one entry of `μ`. -/
theorem prOutMRGen_simTab_update (eQ : Msg × Fin T ≃ Fin c) (eA : Option (Salt × Sig) ≃ Fin a)
    (R : QAdvMR m n w q k c a) (G : Fin (m * n * ancW c k w) → Bool) (μ : Msg)
    (hG : ∀ i, G i = true → ∀ j, (eQ.symm (roundOutcomes m n c i j)).1 ≠ μ)
    (H : Fin m → Fin n) (Hx : Msg × Salt → Tgt) (v : Msg × Fin T → Salt × (Tgt → Option Sig))
    (τ : Fin T) (x : Salt × (Tgt → Option Sig)) :
    prOutMRGen (recordGen R G) H (simTab eQ eA Hx (Function.update v (μ, τ) x)) =
      prOutMRGen (recordGen R G) H (simTab eQ eA Hx v) := by
  set Y : Finset (Fin c) := Finset.univ.filter fun j => (eQ.symm j).1 = μ with hY
  have hG' : ∀ i, G i = true → ∀ j, roundOutcomes m n c i j ∉ Y := by
    intro i hi j hj
    simp only [hY, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact hG i hi j hj
  rw [prOutMRGen_recordGen_eq_prOutAvoidMRGen _ _ Y hG',
    prOutMRGen_recordGen_eq_prOutAvoidMRGen _ _ Y hG']
  refine prOutMRGen_congr_unread _ H fun j hj => ?_
  simp only [hY, Finset.mem_filter, Finset.mem_univ, true_and] at hj
  have hupd : ∀ τ', Function.update v (μ, τ) x ((eQ.symm j).1, τ') =
      v ((eQ.symm j).1, τ') := fun τ' =>
    Function.update_of_ne (fun h => hj (congrArg Prod.fst h)) _ _
  simp only [simTab, collides, honestTab, hupd, Prod.mk.eta]
  rfl

omit [DecidableEq Salt] [NeZero n] [NeZero c] in
/-- Conditioning on all entries of the table but `y`: if `Φ r` does not read the entry `y`,
    the weight of `Φ` at the salt of `y` is at most `1 / card Salt` times the weight of the sum
    of `Φ r` over the salts `r`. -/
theorem sum_sim_salt_le (pk : PK) (y : Msg × Fin T)
    (Φ : Salt → (Msg × Fin T → Salt × (Tgt → Option Sig)) → ℝ≥0∞)
    (hΦ : ∀ r u x, Φ r (Function.update u y x) = Φ r u) :
    ∑ v : Msg × Fin T → Salt × (Tgt → Option Sig),
        (∏ y', (Fintype.card Salt : ℝ≥0∞)⁻¹ * S.simSamplerW pk (v y').2) * Φ (v y).1 v ≤
      (Fintype.card Salt : ℝ≥0∞)⁻¹ * ∑ v : Msg × Fin T → Salt × (Tgt → Option Sig),
        (∏ y', (Fintype.card Salt : ℝ≥0∞)⁻¹ * S.simSamplerW pk (v y').2) * ∑ r, Φ r v := by
  classical
  have hsel : ∀ v : Msg × Fin T → Salt × (Tgt → Option Sig),
      Φ (v y).1 v = ∑ r, Φ r v * (if (v y).1 = r then 1 else 0) := by
    intro v
    simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  calc _ = ∑ r, ∑ v : Msg × Fin T → Salt × (Tgt → Option Sig),
        (∏ y', (Fintype.card Salt : ℝ≥0∞)⁻¹ * S.simSamplerW pk (v y').2) * Φ r v *
          (if (v y).1 = r then 1 else 0) := by
        simp only [hsel, Finset.mul_sum, mul_assoc]
        exact Finset.sum_comm
    _ ≤ ∑ r, (Fintype.card Salt : ℝ≥0∞)⁻¹ * ∑ v : Msg × Fin T → Salt × (Tgt → Option Sig),
        (∏ y', (Fintype.card Salt : ℝ≥0∞)⁻¹ * S.simSamplerW pk (v y').2) * Φ r v := by
        refine Finset.sum_le_sum fun r _ => ?_
        have h := sum_prod_mul_le_of_coord
          (fun _ (x : Salt × (Tgt → Option Sig)) =>
            (Fintype.card Salt : ℝ≥0∞)⁻¹ * S.simSamplerW pk x.2) y (Φ r)
          (fun u => if (u y).1 = r then 1 else 0) (Fintype.card Salt : ℝ≥0∞)⁻¹
          (fun u x => hΦ r u x) fun u => by
            simp only [Function.update_self]
            rw [S.sum_salt_sim_eq pk r, S.sum_salt_sim_mass pk, mul_one]
        exact h
    _ = _ := by
        simp only [Finset.mul_sum]
        rw [Finset.sum_comm]

/-- Hop C at one public key: a winning forgery whose salt is the salt of an entry of its
    message has probability at most `T / card Salt`. For each message `μ` and tag `τ` the test
    reads no round outcome of `μ`, so its probability does not depend on the salt of the entry
    `(μ, τ)`, which is uniform. -/
theorem offGraphAt (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c)
    (eA : Option (Salt × Sig) ≃ Fin a) (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig))
    (pk : PK) :
    S.condGameAt eX eY eQ eA A pk ≤
      S.offGameAt eX eY eQ eA A pk + (T : ℝ≥0∞) * (Fintype.card Salt : ℝ≥0∞)⁻¹ := by
  classical
  set cH : ℝ≥0∞ := (Fintype.card (Fin m → Fin n) : ℝ≥0∞)⁻¹ with hcH
  set cS : ℝ≥0∞ := (Fintype.card Salt : ℝ≥0∞)⁻¹ with hcS
  set wt : (Msg × Fin T → Salt × (Tgt → Option Sig)) → ℝ≥0∞ :=
    fun v => ∏ y, cS * S.simSamplerW pk (v y).2 with hwt
  set Gf : (Fin m → Fin n) → Fin (m * n * ancW c k w) → Bool := fun H i =>
    forgeTest S.toQROMSig eY eQ A pk i (H (forgePoint S.toQROMSig eX A pk i)) with hGf
  set P : (Fin m → Fin n) → (Fin (m * n * ancW c k w) → Bool) →
      (Msg × Fin T → Salt × (Tgt → Option Sig)) → ℝ≥0∞ :=
    fun H G v => prOutMRGen (recordGen (A.run pk) G) H (simTab eQ eA (hashOf eX eY H) v)
    with hP
  -- the split of the test by the off-graph event
  have hsplit : ∀ H v, prOutMRGen (S.forgeGen eX eY eQ A pk H) H
      (simTab eQ eA (hashOf eX eY H) v) =
      prOutMRGen (S.forgeOffGen eX eY eQ A pk H v) H (simTab eQ eA (hashOf eX eY H) v) +
        P H (fun i => Gf H i && !offGraph A v i) v := fun H v =>
    prOutMRGen_recordGen_add _ _ _ _ H
  -- the mass of the weights
  have hmass : ∑ v, wt v = 1 := sum_prod_eq_one _ fun _ => S.sum_salt_sim_mass pk
  -- the bound at one oracle
  have hbad : ∀ H, ∑ v, wt v * P H (fun i => Gf H i && !offGraph A v i) v ≤ T * cS := by
    intro H
    set Gμ : Msg → Fin (m * n * ancW c k w) → Bool := fun μ i =>
      Gf H i && decide ((A.forge i).1 = μ) with hGμ
    set Gmr : Msg → Salt → Fin (m * n * ancW c k w) → Bool := fun μ r i =>
      Gμ μ i && decide ((A.forge i).2.1 = r) with hGmr
    -- the union bound over the entries
    have hunion : ∀ v, P H (fun i => Gf H i && !offGraph A v i) v ≤
        ∑ y : Msg × Fin T, P H (Gmr y.1 (v y).1) v := by
      intro v
      refine prOutMRGen_recordGen_le_sum_tests _ _ Finset.univ _ _ (fun i => ?_) H
      by_cases hG : (Gf H i && !offGraph A v i) = true
      · simp only [hG, ↓reduceIte]
        have hG' := hG
        simp only [Bool.and_eq_true, Bool.not_eq_true', offGraph, decide_eq_false_iff_not,
          not_forall, not_not] at hG'
        obtain ⟨hf, τ, hτ⟩ := hG'
        refine le_trans ?_ (Finset.single_le_sum (f := fun y : Msg × Fin T =>
          if Gmr y.1 (v y).1 i then (1 : ℝ) else 0) (fun _ _ => by split_ifs <;> simp)
          (Finset.mem_univ ((A.forge i).1, τ)))
        simp [hGmr, hGμ, hf, hτ]
      · simp only [Bool.not_eq_true] at hG
        simp only [hG]
        exact Finset.sum_nonneg fun _ _ => by split_ifs <;> simp
    -- the test of `Gmr μ r` reads no round outcome of `μ`
    have hinv : ∀ μ τ r v x, P H (Gmr μ r) (Function.update v (μ, τ) x) = P H (Gmr μ r) v := by
      intro μ τ r v x
      refine prOutMRGen_simTab_update eQ eA (A.run pk) (Gmr μ r) μ (fun i hi j => ?_) H
        (hashOf eX eY H) v τ x
      simp only [hGmr, hGμ, hGf, forgeTest, Bool.and_eq_true, decide_eq_true_eq] at hi
      exact fun hj => hi.1.1.2 j (hj.trans hi.1.2.symm)
    -- one entry
    have hentry : ∀ y : Msg × Fin T, ∑ v, wt v * P H (Gmr y.1 (v y).1) v ≤
        cS * ∑ v, wt v * P H (Gμ y.1) v := by
      intro y
      have hpart : ∀ v, P H (Gμ y.1) v = ∑ r, P H (Gmr y.1 r) v := fun v =>
        prOutMRGen_recordGen_eq_sum_fn _ _ _ (fun i => (A.forge i).2.1) H
      have h := S.sum_sim_salt_le pk y (fun r v => P H (Gmr y.1 r) v)
        (fun r u x => hinv y.1 y.2 r u x)
      simp only [← hpart] at h
      exact h
    have hmsg : ∀ v, P H (Gf H) v = ∑ μ, P H (Gμ μ) v := fun v =>
      prOutMRGen_recordGen_eq_sum_fn _ _ _ (fun i => (A.forge i).1) H
    have hle1 : ∀ G v, P H G v ≤ 1 := fun _ _ => prTrue_Q_le_one _ _
    calc ∑ v, wt v * P H (fun i => Gf H i && !offGraph A v i) v
        ≤ ∑ v, wt v * ∑ y : Msg × Fin T, P H (Gmr y.1 (v y).1) v := by
          gcongr with v
          exact hunion v
      _ = ∑ y : Msg × Fin T, ∑ v, wt v * P H (Gmr y.1 (v y).1) v := by
          simp only [Finset.mul_sum]
          exact Finset.sum_comm
      _ ≤ ∑ y : Msg × Fin T, cS * ∑ v, wt v * P H (Gμ y.1) v :=
          Finset.sum_le_sum fun y _ => hentry y
      _ = T * cS * ∑ v, wt v * P H (Gf H) v := by
          rw [Fintype.sum_prod_type]
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hmsg,
            Finset.mul_sum]
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun v _ => Finset.sum_congr rfl fun μ _ => ?_
          ring
      _ ≤ T * cS * ∑ v, wt v * 1 := by
          gcongr with v
          exact hle1 _ v
      _ = T * cS := by rw [Finset.sum_congr rfl fun v _ => mul_one (wt v), hmass, mul_one]
  have hcHsum : ∑ _H : Fin m → Fin n, cH = 1 := by
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hcH]
    exact ENNReal.mul_inv_cancel (by simp [NeZero.ne n]) (ENNReal.natCast_ne_top _)
  calc S.condGameAt eX eY eQ eA A pk
      = S.offGameAt eX eY eQ eA A pk +
          ∑ H, cH * ∑ v, wt v * P H (fun i => Gf H i && !offGraph A v i) v := by
        simp only [condGameAt, offGameAt, hsplit, mul_add, Finset.sum_add_distrib]
        rfl
    _ ≤ S.offGameAt eX eY eQ eA A pk + ∑ H : Fin m → Fin n, cH * (T * cS) := by
        gcongr with H
        exact hbad H
    _ = _ := by rw [← Finset.sum_mul, hcHsum, one_mul]

variable [Fintype PK] [Fintype SK]

/-- The winning probability of `condGame` with the forgery off the salted graph, averaged over
    the key distribution. -/
def offGame (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c)
    (eA : Option (Salt × Sig) ≃ Fin a) (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig)) :
    ℝ≥0∞ :=
  ∑ ks, S.keygen ks * S.offGameAt eX eY eQ eA A ks.1

/-- Hop C: in the game with the simulator's conditional samplers (`condGame`), a winning
    forgery whose salt is the salt of an entry of its message has probability at most
    `T / card Salt`; the rest is `offGame`. -/
theorem saltedPSF_offGraph (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n)
    (eQ : Msg × Fin T ≃ Fin c) (eA : Option (Salt × Sig) ≃ Fin a)
    (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig)) :
    S.condGame eX eY eQ eA A ≤
      S.offGame eX eY eQ eA A + (T : ℝ≥0∞) * (Fintype.card Salt : ℝ≥0∞)⁻¹ := by
  have hkey : ∑ ks, S.keygen ks = 1 := by
    rw [← tsum_fintype (L := SummationFilter.unconditional (PK × SK))]
    exact S.keygen.tsum_coe
  unfold condGame offGame
  calc ∑ ks, S.keygen ks * S.condGameAt eX eY eQ eA A ks.1
      ≤ ∑ ks, S.keygen ks * (S.offGameAt eX eY eQ eA A ks.1 +
          (T : ℝ≥0∞) * (Fintype.card Salt : ℝ≥0∞)⁻¹) :=
        Finset.sum_le_sum fun ks _ => by gcongr; exact S.offGraphAt eX eY eQ eA A ks.1
    _ = _ := by
        simp only [mul_add, Finset.sum_add_distrib]
        rw [← Finset.sum_mul, hkey, one_mul]

end OffGraph

/-! ## Hop B: the image law at the salted points -/

section HopImage

variable [Fintype Sig] [DecidableEq Sig] [Fintype Tgt] [DecidableEq Tgt] [DecidableEq Salt]
  {m n w q k c a T : ℕ}

omit [DecidableEq Salt] in
/-- The image law has mass one. -/
theorem sum_imgW (pk : PK) : ∑ θ, S.imgW pk θ = 1 := by
  simp only [imgW]
  rw [Finset.sum_comm]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ↓reduceIte]
  exact S.sum_domW pk

/-- The image law of a domain sample at the public key `pk` on the encoded targets. -/
def imgN (eY : Tgt ≃ Fin n) (pk : PK) (z : Fin n) : ℝ≥0∞ := S.imgW pk (eY.symm z)

/-- The maximal coupling, at one point of the oracle, of the uniform value and the image law
    of a domain sample. -/
def oCplW (eY : Tgt ≃ Fin n) (pk : PK) : Bool × Fin n × Fin n × Fin n → ℝ≥0∞ :=
  maxCouplingW (fun _ => (n : ℝ≥0∞)⁻¹) (S.imgN eY pk)

/-- The point `x` is the salted point of an entry of the table `v`. -/
def salted {β : Type} [Fintype Msg] (eX : Msg × Salt ≃ Fin m) (v : Msg × Fin T → Salt × β)
    (x : Fin m) : Bool :=
  decide (∃ y : Msg × Fin T, eX (y.1, (v y).1) = x)

/-- The law of the programmed oracle value at the point `x`: the image law of a domain sample
    at a salted point of the table `v`, the uniform value elsewhere. -/
def progW [Fintype Msg] (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n) (pk : PK)
    (v : Msg × Fin T → Salt × (Tgt → Option Sig)) (x : Fin m) (z : Fin n) : ℝ≥0∞ :=
  if salted eX v x then S.imgN eY pk z else (n : ℝ≥0∞)⁻¹

variable [Fintype Msg] [DecidableEq Msg] [Fintype Salt] [Nonempty Salt] [NeZero m] [NeZero n]
  [NeZero c]

/-- The forgery adversary of `forgeOffGen` with its forgery test as a final query and its
    signing rounds answered through the oracle: the round of input `i` reads the oracle at the
    salted point of the entry `eQ.symm i` of the table `v` and answers the value of its sampler
    there, or a signing failure at an entry that repeats a salt. It does not depend on the
    oracle. -/
def forgeImgGen (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c)
    (eA : Option (Salt × Sig) ≃ Fin a) (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig))
    (pk : PK) (v : Msg × Fin T → Salt × (Tgt → Option Sig)) :
    QAdvMRGen m n (ancW c k w * (m * n) * (m * n)) (q + 1 + 1) k c a :=
  ((recordGen (A.run pk) fun _ => true).withFinalQuery (forgePoint S.toQROMSig eX A pk)
      (fun i θ => forgeTest S.toQROMSig eY eQ A pk i θ && offGraph A v i)).viaOracle
    (fun i => eX ((eQ.symm i).1, (v (eQ.symm i)).1))
    (fun i z => if collides v (eQ.symm i) then eA none else
      eA (((v (eQ.symm i)).2 (eY.symm z)).map fun s => ((v (eQ.symm i)).1, s)))

omit [Fintype Sig] [DecidableEq Sig] [Fintype Tgt] [Fintype Msg] in
/-- The adversary `forgeImgGen` at every round function accepts with the probability of
    `forgeOffGen` at the simulated signing table. -/
theorem prOutMRGen_forgeImgGen (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n)
    (eQ : Msg × Fin T ≃ Fin c) (eA : Option (Salt × Sig) ≃ Fin a)
    (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig)) (pk : PK)
    (v : Msg × Fin T → Salt × (Tgt → Option Sig)) (H : Fin m → Fin n) (f₀ : Fin c → Fin a) :
    prOutMRGen (S.forgeImgGen eX eY eQ eA A pk v) H f₀ =
      prOutMRGen (S.forgeOffGen eX eY eQ A pk H v) H (simTab eQ eA (hashOf eX eY H) v) := by
  rw [forgeImgGen, prOutMRGen_viaOracle_eq, prOutMRGen_withFinalQuery_eq]
  rfl

/-- The winning probability of `offGameAt` with the oracle programmed at the salted points:
    uniform salts and samplers of the simulator, at each salted point of the table an oracle
    value of the image law of a domain sample, uniform values elsewhere. -/
def imgGameAt (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c)
    (eA : Option (Salt × Sig) ≃ Fin a) (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig))
    (pk : PK) : ℝ≥0∞ :=
  ∑ v : Msg × Fin T → Salt × (Tgt → Option Sig),
    (∏ y, (Fintype.card Salt : ℝ≥0∞)⁻¹ * S.simSamplerW pk (v y).2) *
      ∑ H : Fin m → Fin n, (∏ x, S.progW eX eY pk v x (H x)) *
        prOutMRGen (S.forgeOffGen eX eY eQ A pk H v) H (simTab eQ eA (hashOf eX eY H) v)

omit [DecidableEq Salt] [Fintype Msg] [DecidableEq Msg] [Fintype Salt] [Nonempty Salt]
  [NeZero m] [NeZero c] [Fintype Tgt] in
/-- The uniform value and the image law on the encoded targets have mass one. -/
theorem oCplW_laws [Finite Tgt] (eY : Tgt ≃ Fin n) (pk : PK) :
    (∑ _ : Fin n, (n : ℝ≥0∞)⁻¹ = 1) ∧ ∑ z, S.imgN eY pk z = 1 := by
  have := Fintype.ofFinite Tgt
  refine ⟨?_, ?_⟩
  · simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel (by simp [NeZero.ne n]) (ENNReal.natCast_ne_top _)
  · simp only [imgN]
    rw [Equiv.sum_comp eY.symm (S.imgW pk)]
    exact S.sum_imgW pk

omit [DecidableEq Salt] [Fintype Msg] [DecidableEq Msg] [Fintype Salt] [Nonempty Salt]
  [NeZero m] [NeZero c] [Fintype Tgt] in
/-- The coupling at one point of the oracle has mass one. -/
theorem sum_oCplW [Finite Tgt] (eY : Tgt ≃ Fin n) (pk : PK) : ∑ ω, S.oCplW eY pk ω = 1 := by
  have h := maxCouplingW_sum_fst (S.oCplW_laws eY pk).1 (S.oCplW_laws eY pk).2 fun _ => 1
  simp only [mul_one] at h
  rw [oCplW, h, (S.oCplW_laws eY pk).1]

omit [DecidableEq Salt] [Fintype Msg] [DecidableEq Msg] [Fintype Salt] [Nonempty Salt]
  [NeZero m] [NeZero c] in
/-- The failure probability of the coupling at one point of the oracle is the image distance
    of the public key. -/
theorem tvW_oCpl_eq (eY : Tgt ≃ Fin n) (pk : PK) :
    tvW (fun _ : Fin n => (n : ℝ≥0∞)⁻¹) (S.imgN eY pk) = S.domDistAt pk := by
  rw [← tvW_comm (S.oCplW_laws eY pk).1 (S.oCplW_laws eY pk).2]
  have hn : Fintype.card Tgt = n := (Fintype.card_congr eY).trans (Fintype.card_fin n)
  simp only [tvW, imgN, domDistAt, hn]
  exact Equiv.sum_comp eY.symm fun θ => S.imgW pk θ - (n : ℝ≥0∞)⁻¹

/-- `offGameAt` with the uniform oracle written as the first outputs of independent couplings
    of the uniform value and the image law, and the forgery adversary `forgeImgGen`. -/
theorem offGameAt_eq_cpl (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n)
    (eQ : Msg × Fin T ≃ Fin c) (eA : Option (Salt × Sig) ≃ Fin a)
    (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig)) (pk : PK) :
    S.offGameAt eX eY eQ eA A pk =
      ∑ v : Msg × Fin T → Salt × (Tgt → Option Sig),
        (∏ y, (Fintype.card Salt : ℝ≥0∞)⁻¹ * S.simSamplerW pk (v y).2) *
          ∑ u : Fin m → Bool × Fin n × Fin n × Fin n, (∏ x, S.oCplW eY pk (u x)) *
            prOutMRGen (S.forgeImgGen eX eY eQ eA A pk v) (fun x => cplFst (u x))
              (fun _ => eA none) := by
  unfold offGameAt
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hpi := sum_pi_comp_eq (ι := Fin m) (fun _ => S.oCplW eY pk)
    (fun _ _ => (n : ℝ≥0∞)⁻¹) (fun _ => cplFst) (fun _ z => z)
    (fun _ g => maxCouplingW_sum_fst (S.oCplW_laws eY pk).1 (S.oCplW_laws eY pk).2 g)
    (fun H => prOutMRGen (S.forgeImgGen eX eY eQ eA A pk v) H (fun _ => eA none))
  simp only [← Finset.mul_sum]
  rw [hpi]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun H _ => ?_
  rw [prOutMRGen_forgeImgGen, Finset.prod_const, Finset.card_univ, Fintype.card_fin,
    Fintype.card_fun, Fintype.card_fin, Fintype.card_fin, Nat.cast_pow, ENNReal.inv_pow]
  ring

/-- `imgGameAt` with the programmed oracle written as the second outputs of the couplings at
    the salted points and the first outputs elsewhere, and the forgery adversary
    `forgeImgGen`. -/
theorem imgGameAt_eq_cpl (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n)
    (eQ : Msg × Fin T ≃ Fin c) (eA : Option (Salt × Sig) ≃ Fin a)
    (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig)) (pk : PK) :
    S.imgGameAt eX eY eQ eA A pk =
      ∑ v : Msg × Fin T → Salt × (Tgt → Option Sig),
        (∏ y, (Fintype.card Salt : ℝ≥0∞)⁻¹ * S.simSamplerW pk (v y).2) *
          ∑ u : Fin m → Bool × Fin n × Fin n × Fin n, (∏ x, S.oCplW eY pk (u x)) *
            prOutMRGen (S.forgeImgGen eX eY eQ eA A pk v)
              (fun x => if salted eX v x then cplSnd (u x) else cplFst (u x))
              (fun _ => eA none) := by
  unfold imgGameAt
  refine Finset.sum_congr rfl fun v _ => ?_
  congr 1
  have hρ : ∀ (x : Fin m) (g : Fin n → ℝ≥0∞),
      ∑ ω, S.oCplW eY pk ω * g (if salted eX v x then cplSnd ω else cplFst ω) =
        ∑ z, S.progW eX eY pk v x z * g z := by
    intro x g
    unfold progW
    cases salted eX v x
    · simp only [Bool.false_eq_true, ↓reduceIte]
      exact maxCouplingW_sum_fst (S.oCplW_laws eY pk).1 (S.oCplW_laws eY pk).2 g
    · simp only [↓reduceIte]
      exact maxCouplingW_sum_snd (S.oCplW_laws eY pk).1 (S.oCplW_laws eY pk).2 g
  have hpi := sum_pi_comp_eq (ι := Fin m) (fun _ => S.oCplW eY pk)
    (fun x z => S.progW eX eY pk v x z)
    (fun x ω => if salted eX v x then cplSnd ω else cplFst ω) (fun _ z => z) hρ
    (fun H => prOutMRGen (S.forgeImgGen eX eY eQ eA A pk v) H (fun _ => eA none))
  rw [hpi]
  refine Finset.sum_congr rfl fun H _ => ?_
  rw [prOutMRGen_forgeImgGen]

omit [Nonempty Salt] [NeZero m] [NeZero c] in
/-- The sparsity of the failure set of the oracle couplings: given the table, the common
    values and any event `P` of neither, the coupling at the point `x` fails with probability
    `tvW` of the uniform value and the image law. -/
theorem sum_tab_cpl_fail_le (eY : Tgt ≃ Fin n) (pk : PK)
    (wt : (Msg × Fin T → Salt × (Tgt → Option Sig)) → ℝ≥0∞)
    (j : Msg × Fin T → Salt × (Tgt → Option Sig)) (x : Fin m) (h : Fin m → Fin n) (P : Prop)
    [Decidable P] :
    ∑ ω : (Msg × Fin T → Salt × (Tgt → Option Sig)) × (Fin m → Bool × Fin n × Fin n × Fin n),
        wt ω.1 * (∏ x', S.oCplW eY pk (ω.2 x')) *
          (if ω.1 = j ∧ (fun x' => (ω.2 x').2.1) = h ∧ P ∧
            x ∈ Finset.univ.filter (fun x' => (ω.2 x').1 = true) then 1 else 0) ≤
      tvW (fun _ : Fin n => (n : ℝ≥0∞)⁻¹) (S.imgN eY pk) *
        ∑ ω : (Msg × Fin T → Salt × (Tgt → Option Sig)) ×
            (Fin m → Bool × Fin n × Fin n × Fin n),
          wt ω.1 * (∏ x', S.oCplW eY pk (ω.2 x')) *
            (if ω.1 = j ∧ (fun x' => (ω.2 x').2.1) = h ∧ P then 1 else 0) := by
  by_cases hP : P
  · simp only [hP, true_and, Finset.mem_filter, Finset.mem_univ, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single j (fun v _ hv => by simp [hv]) (by simp),
      Finset.sum_eq_single j (fun v _ hv => by simp [hv]) (by simp)]
    simp only [true_and, and_true, mul_assoc, ← Finset.mul_sum, oCplW]
    rw [sum_prod_maxCouplingW_fail (S.oCplW_laws eY pk).1 (S.oCplW_laws eY pk).2 x h]
    exact le_of_eq (by ring)
  · simp [hP]

/-- Hop B at one public key: programming the oracle at the salted points of the table with the
    image law of a domain sample changes the winning probability of `offGameAt` by at most
    `4 (flatQ q k q + 2 (k + 1)) domDistAt^(1/2)`. The forgery test and the signing rounds are
    oracle queries of `forgeImgGen`, which has `q + 2` queries per segment, and the bound is
    `prOutMRGen_resample_gentle_fiber_le` twice, from each of the two oracles to the common
    values of the couplings, indexed by the table. -/
theorem hopImageAt (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c)
    (eA : Option (Salt × Sig) ≃ Fin a) (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig))
    (pk : PK) :
    absDiff (S.offGameAt eX eY eQ eA A pk) (S.imgGameAt eX eY eQ eA A pk) ≤
      4 * ((flatQ q k q + 2 * (k + 1) : ℕ) : ℝ≥0∞) * S.domDistAt pk ^ (1 / 2 : ℝ) := by
  classical
  set μ : (Msg × Fin T → Salt × (Tgt → Option Sig)) × (Fin m → Bool × Fin n × Fin n × Fin n) →
      ℝ≥0∞ := fun ω =>
    (∏ y, (Fintype.card Salt : ℝ≥0∞)⁻¹ * S.simSamplerW pk (ω.1 y).2) *
      ∏ x, S.oCplW eY pk (ω.2 x) with hμdef
  have hsplit : ∀ G : (Msg × Fin T → Salt × (Tgt → Option Sig)) →
      (Fin m → Bool × Fin n × Fin n × Fin n) → ℝ≥0∞,
      ∑ ω, μ ω * G ω.1 ω.2 = ∑ v, (∏ y, (Fintype.card Salt : ℝ≥0∞)⁻¹ *
        S.simSamplerW pk (v y).2) * ∑ u, (∏ x, S.oCplW eY pk (u x)) * G v u := by
    intro G
    simp only [hμdef, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]
  have hμ : ∑ ω, μ ω = 1 := by
    have h := hsplit fun _ _ => 1
    simp only [mul_one] at h
    rw [h, sum_prod_eq_one _ fun _ => S.sum_oCplW eY pk]
    simp only [mul_one]
    have h2 := sum_prod_eq_one (ι := Msg × Fin T) (β := Salt × (Tgt → Option Sig))
      (fun _ x => (Fintype.card Salt : ℝ≥0∞)⁻¹ * S.simSamplerW pk x.2)
      fun _ => S.sum_salt_sim_mass pk
    exact h2
  set D : (Msg × Fin T → Salt × (Tgt → Option Sig)) ×
      (Fin m → Bool × Fin n × Fin n × Fin n) → Finset (Fin m) :=
    fun ω => Finset.univ.filter fun x => (ω.2 x).1 = true with hD
  set lam := tvW (fun _ : Fin n => (n : ℝ≥0∞)⁻¹) (S.imgN eY pk) with hlam
  have hsp : ∀ j x h (g : Fin c → Fin a),
      ∑ ω, μ ω * (if ω.1 = j ∧ (fun x' => (ω.2 x').2.1) = h ∧ (fun _ => eA none) = g ∧
        x ∈ D ω then 1 else 0) ≤
      lam * ∑ ω, μ ω * (if ω.1 = j ∧ (fun x' => (ω.2 x').2.1) = h ∧
        (fun _ => eA none) = g then 1 else 0) := by
    intro j x h g
    exact S.sum_tab_cpl_fail_le eY pk
      (fun v => ∏ y, (Fintype.card Salt : ℝ≥0∞)⁻¹ * S.simSamplerW pk (v y).2) j x h
      ((fun _ : Fin c => eA none) = g)
  have h1 := prOutMRGen_resample_gentle_fiber_le (S.forgeImgGen eX eY eQ eA A pk) Prod.fst μ hμ
    (fun ω x => cplFst (ω.2 x)) (fun ω x => (ω.2 x).2.1) (fun _ _ => eA none) D lam
    (fun ω x hx => by simp_all [cplFst]) hsp
  have h3 := prOutMRGen_resample_gentle_fiber_le (S.forgeImgGen eX eY eQ eA A pk) Prod.fst μ hμ
    (fun ω x => if salted eX ω.1 x then cplSnd (ω.2 x) else cplFst (ω.2 x))
    (fun ω x => (ω.2 x).2.1) (fun _ _ => eA none) D lam
    (fun ω x hx => by split_ifs <;> simp_all [cplFst, cplSnd]) hsp
  have hE1 := S.offGameAt_eq_cpl eX eY eQ eA A pk
  have hE3 := S.imgGameAt_eq_cpl eX eY eQ eA A pk
  rw [← hsplit] at hE1 hE3
  have hQ : flatQ (q + 1 + 1) k (q + 1 + 1) = flatQ q k q + 2 * (k + 1) := by
    rw [flatQ_succ_succ, flatQ_succ_succ]
    ring
  beta_reduce at h1 h3
  rw [absDiff_comm] at h3
  have key := (absDiff_triangle _ _ _).trans (add_le_add h1 h3)
  rw [hE1, hE3, ← hQ, ← S.tvW_oCpl_eq eY pk, ← hlam]
  refine key.trans (le_of_eq ?_)
  ring

variable [Fintype PK] [Fintype SK]

/-- The winning probability of `imgGameAt`, averaged over the key distribution. -/
def imgGame (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c)
    (eA : Option (Salt × Sig) ≃ Fin a) (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig)) :
    ℝ≥0∞ :=
  ∑ ks, S.keygen ks * S.imgGameAt eX eY eQ eA A ks.1

/-- Hop B: in the game after hops A and C (`offGame`), programming the oracle at the salted
    points of the table with the image law of a domain sample (`imgGame`) changes the winning
    probability by at most `4 (flatQ q k q + 2 (k + 1)) domDist^(1/2)`. -/
theorem saltedPSF_hopImage (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n)
    (eQ : Msg × Fin T ≃ Fin c) (eA : Option (Salt × Sig) ≃ Fin a)
    (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig)) :
    absDiff (S.offGame eX eY eQ eA A) (S.imgGame eX eY eQ eA A) ≤
      4 * ((flatQ q k q + 2 * (k + 1) : ℕ) : ℝ≥0∞) * S.domDist ^ (1 / 2 : ℝ) := by
  have hkey : ∑ ks, S.keygen ks = 1 := by
    rw [← tsum_fintype (L := SummationFilter.unconditional (PK × SK))]
    exact S.keygen.tsum_coe
  unfold offGame imgGame
  refine (absDiff_sum_le _ _).trans ?_
  calc ∑ ks, absDiff (S.keygen ks * _) (S.keygen ks * S.imgGameAt eX eY eQ eA A ks.1)
      ≤ ∑ ks, S.keygen ks * (4 * ((flatQ q k q + 2 * (k + 1) : ℕ) : ℝ≥0∞) *
          S.domDistAt ks.1 ^ (1 / 2 : ℝ)) :=
        Finset.sum_le_sum fun ks _ =>
          (absDiff_mul_left_le _ _ _).trans (by gcongr; exact S.hopImageAt eX eY eQ eA A ks.1)
    _ = 4 * ((flatQ q k q + 2 * (k + 1) : ℕ) : ℝ≥0∞) *
          ∑ ks, S.keygen ks * S.domDistAt ks.1 ^ (1 / 2 : ℝ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun ks _ => by ring
    _ ≤ _ := by
        gcongr
        exact sum_mul_rpow_half_le (fun ks => S.keygen ks) (fun ks => S.domDistAt ks.1) hkey

end HopImage

/-! ## The image game with domain samples -/

section DomSample

/-- The table of salts `r` whose entry `y` answers every target with `o y`. -/
def ansTab {Sig Tgt : Type} {T : ℕ} (r : Msg × Fin T → Salt) (o : Msg × Fin T → Option Sig) :
    Msg × Fin T → Salt × (Tgt → Option Sig) :=
  fun y => (r y, fun _ => o y)

/-- Whether an entry repeats a salt depends on the salts of the table only. -/
theorem collides_congr [DecidableEq Salt] {β β' : Type} {T : ℕ} (v : Msg × Fin T → Salt × β)
    (v' : Msg × Fin T → Salt × β') (h : ∀ y, (v y).1 = (v' y).1) (y : Msg × Fin T) :
    collides v y = collides v' y := by
  simp only [collides, h]

/-- Whether a point is salted depends on the salts of the table only. -/
theorem salted_congr [Fintype Msg] {β β' : Type} {m T : ℕ} (eX : Msg × Salt ≃ Fin m)
    (v : Msg × Fin T → Salt × β) (v' : Msg × Fin T → Salt × β') (h : ∀ y, (v y).1 = (v' y).1)
    (x : Fin m) : salted eX v x = salted eX v' x := by
  simp only [salted, h]

/-- The salted point of an entry is salted. -/
theorem salted_self [Fintype Msg] {β : Type} {m T : ℕ} (eX : Msg × Salt ≃ Fin m)
    (v : Msg × Fin T → Salt × β) (y : Msg × Fin T) : salted eX v (eX (y.1, (v y).1)) = true := by
  simp only [salted, decide_eq_true_eq]
  exact ⟨y, rfl⟩

variable [Fintype Sig] [DecidableEq Sig] [Fintype Tgt] [DecidableEq Tgt] [DecidableEq Salt]
  {m n w q k c a T : ℕ}

omit [Fintype Tgt] [DecidableEq Tgt] [DecidableEq Salt] in
/-- An average against the domain law is an average over the domain coins. -/
theorem sum_domW_mul (pk : PK) (g : Sig → ℝ≥0∞) :
    ∑ s, S.domW pk s * g s =
      ∑ d : S.DCoins, (Fintype.card S.DCoins : ℝ≥0∞)⁻¹ * g (S.sampleDom pk d) := by
  simp only [domW, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun d _ => ?_
  simp

omit [Fintype Tgt] [DecidableEq Salt] in
/-- The joint law of a target of the image law and a preimage of the simulator's law is the
    law of the image of a domain sample and the sample. -/
theorem sum_imgW_mul_simW (pk : PK) (θ : Tgt) (g : Option Sig → ℝ≥0∞) :
    ∑ o, S.imgW pk θ * S.simW pk θ o * g o =
      ∑ s, S.domW pk s * (if S.f pk s = θ then 1 else 0) * g (some s) := by
  rw [Fintype.sum_option]
  by_cases h : S.imgW pk θ = 0
  · have h0 : ∀ s, S.domW pk s * (if S.f pk s = θ then 1 else 0) = 0 := fun s =>
      (Finset.sum_eq_zero_iff.mp h) s (Finset.mem_univ s)
    simp [h, h0]
  · have hI : S.imgW pk θ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (S.imgW_le_one pk θ)
    simp only [simW, h, ↓reduceIte, condW, mul_zero, zero_mul, zero_add]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [ENNReal.mul_div_cancel h hI]

omit [Fintype Tgt] [DecidableEq Salt] in
/-- At one point of the oracle, a value of the image law and a preimage of the simulator's law
    at that value have the law of the image of a domain sample and the sample. -/
theorem sum_imgN_simW [Finite Tgt] (eY : Tgt ≃ Fin n) (pk : PK)
    (g : Fin n × Option Sig → ℝ≥0∞) :
    ∑ zo : Fin n × Option Sig, S.imgN eY pk zo.1 * S.simW pk (eY.symm zo.1) zo.2 * g zo =
      ∑ d : S.DCoins, (Fintype.card S.DCoins : ℝ≥0∞)⁻¹ *
        g (eY (S.f pk (S.sampleDom pk d)), some (S.sampleDom pk d)) := by
  have := Fintype.ofFinite Tgt
  rw [Fintype.sum_prod_type, ← Equiv.sum_comp eY]
  simp only [imgN, Equiv.symm_apply_apply]
  simp_rw [S.sum_imgW_mul_simW pk _ fun o => g (eY _, o)]
  rw [Finset.sum_comm, ← S.sum_domW_mul pk fun s => g (eY (S.f pk s), some s)]
  refine Finset.sum_congr rfl fun s _ => ?_
  simp [mul_ite]

omit [Fintype Sig] [DecidableEq Sig] [Fintype Tgt] [DecidableEq Tgt] [DecidableEq Salt] in
/-- The uniform weight of the domain coins has mass one. -/
theorem sum_inv_card_DCoins :
    ∑ _d : S.DCoins, (Fintype.card S.DCoins : ℝ≥0∞)⁻¹ = 1 := by
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  exact ENNReal.mul_inv_cancel (by simp) (ENNReal.natCast_ne_top _)

variable [Fintype Msg] [DecidableEq Msg] [Fintype Salt] [Nonempty Salt] [NeZero n] [NeZero c]

/-- The winning probability of the off-graph forgery adversary at the oracle `H` and the
    table `v`, with the simulated signing table of `v`. -/
def offWin (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c)
    (eA : Option (Salt × Sig) ≃ Fin a) (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig))
    (pk : PK) (H : Fin m → Fin n) (v : Msg × Fin T → Salt × (Tgt → Option Sig)) : ℝ≥0∞ :=
  prOutMRGen (S.forgeOffGen eX eY eQ A pk H v) H (simTab eQ eA (hashOf eX eY H) v)

/-- The table of salts `r` whose entry `y` answers with the domain sample of the coins `d` at
    its salted point. -/
def domTab (eX : Msg × Salt ≃ Fin m) (pk : PK) (r : Msg × Fin T → Salt)
    (d : Fin m → S.DCoins) : Msg × Fin T → Salt × (Tgt → Option Sig) :=
  ansTab r fun y => some (S.sampleDom pk (d (eX (y.1, r y))))

/-- The oracle programmed with domain samples: at a point salted by the salts `r`, the image
    of the domain sample of the coins `(u x).2`; the value `(u x).1` elsewhere. -/
def domOracle (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n) (pk : PK) (r : Msg × Fin T → Salt)
    (u : Fin m → Fin n × S.DCoins) : Fin m → Fin n :=
  fun x => if salted eX (fun y => (r y, ())) x then eY (S.f pk (S.sampleDom pk (u x).2))
    else (u x).1

/-- The image game with domain samples at the public key `pk`: uniform salts `r`, at each
    point of the oracle a uniform value and uniform domain coins; at a salted point the oracle
    is the image of the domain sample and the entries of that point answer the sample. No
    secret key is used. -/
def domGameAt (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c)
    (eA : Option (Salt × Sig) ≃ Fin a) (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig))
    (pk : PK) : ℝ≥0∞ :=
  ∑ r : Msg × Fin T → Salt, (∏ _y : Msg × Fin T, (Fintype.card Salt : ℝ≥0∞)⁻¹) *
    ∑ u : Fin m → Fin n × S.DCoins,
      (∏ _x : Fin m, (n : ℝ≥0∞)⁻¹ * (Fintype.card S.DCoins : ℝ≥0∞)⁻¹) *
        S.offWin eX eY eQ eA A pk (S.domOracle eX eY pk r u) (S.domTab eX pk r fun x => (u x).2)

/-- `imgGameAt` with the table split into salts and samplers and each sampler replaced by its
    value at the target of its salted point. -/
theorem imgGameAt_eq_ans (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n)
    (eQ : Msg × Fin T ≃ Fin c) (eA : Option (Salt × Sig) ≃ Fin a)
    (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig)) (pk : PK) :
    S.imgGameAt eX eY eQ eA A pk =
      ∑ r : Msg × Fin T → Salt, (∏ _y : Msg × Fin T, (Fintype.card Salt : ℝ≥0∞)⁻¹) *
        ∑ H : Fin m → Fin n, (∏ x, S.progW eX eY pk (ansTab r fun _ => none) x (H x)) *
          ∑ o : Msg × Fin T → Option Sig,
            (∏ y, S.simW pk (hashOf eX eY H (y.1, r y)) (o y)) *
              S.offWin eX eY eQ eA A pk H (ansTab r o) := by
  unfold imgGameAt
  rw [← (Equiv.arrowProdEquivProdArrow (Msg × Fin T) (fun _ => Salt)
      (fun _ => Tgt → Option Sig)).symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [Equiv.arrowProdEquivProdArrow, Equiv.coe_fn_symm_mk, Finset.prod_mul_distrib,
    mul_assoc, ← Finset.mul_sum]
  congr 1
  have hP : ∀ (κ : Msg × Fin T → Tgt → Option Sig) (H : Fin m → Fin n),
      (∏ x, S.progW eX eY pk (fun c => (r c, κ c)) x (H x)) =
        ∏ x, S.progW eX eY pk (ansTab r fun _ => none) x (H x) := fun κ H => by
    simp only [progW, salted_congr eX (fun c => (r c, κ c))
      (ansTab (Tgt := Tgt) r fun _ => (none : Option Sig)) fun _ => rfl]
  simp only [hP, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun H _ => ?_
  refine (Finset.sum_congr rfl fun κ _ => mul_left_comm _ _ _).trans ?_
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  congr 1
  have hev : ∀ (y : Msg × Fin T) (g : Option Sig → ℝ≥0∞),
      ∑ κ, S.simSamplerW pk κ * g (κ (hashOf eX eY H (y.1, r y))) =
        ∑ o, S.simW pk (hashOf eX eY H (y.1, r y)) o * g o := fun y g =>
    sum_prod_eval (fun θ => S.simW pk θ) _ (fun θ => S.sum_simW pk θ) g
  have hpi := sum_pi_comp_eq (ι := Msg × Fin T) (α := Tgt → Option Sig) (β := Option Sig)
    (γ := Option Sig) (fun _ κ => S.simSamplerW pk κ)
    (fun y o => S.simW pk (hashOf eX eY H (y.1, r y)) o)
    (fun y κ => κ (hashOf eX eY H (y.1, r y))) (fun _ o => o) hev
    (fun o => S.offWin eX eY eQ eA A pk H (ansTab r o))
  exact hpi

omit [Fintype Tgt] in
/-- Reindexing the answers of the entries by the salted points: the entries that repeat no
    salt have distinct salted points, and only their answers are read. -/
theorem sum_ans_eq_sum_pt (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n)
    (eQ : Msg × Fin T ≃ Fin c) (eA : Option (Salt × Sig) ≃ Fin a)
    (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig)) (pk : PK) (r : Msg × Fin T → Salt)
    (H : Fin m → Fin n) :
    ∑ o : Msg × Fin T → Option Sig, (∏ y, S.simW pk (hashOf eX eY H (y.1, r y)) (o y)) *
        S.offWin eX eY eQ eA A pk H (ansTab r o) =
      ∑ o : Fin m → Option Sig, (∏ x, S.simW pk (eY.symm (H x)) (o x)) *
        S.offWin eX eY eQ eA A pk H (ansTab r fun y => o (eX (y.1, r y))) := by
  let N : Finset (Msg × Fin T) :=
    Finset.univ.filter fun y => collides (fun y => (r y, ())) y = false
  have hinj : Set.InjOn (fun y : Msg × Fin T => eX (y.1, r y)) N := by
    intro y hy y' hy' h
    simp only [N, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hy hy'
    obtain ⟨h1, h2⟩ := Prod.mk.inj (eX.injective h)
    have hc : ∀ z z' : Msg × Fin T, z.1 = z'.1 → r z = r z' → z.2 < z'.2 →
        collides (fun y => (r y, ())) z' = true := fun z z' e1 e2 hlt => by
      simp only [collides, decide_eq_true_eq]
      refine ⟨z.2, hlt, ?_⟩
      rw [show ((z'.1, z.2) : Msg × Fin T) = z from Prod.ext e1.symm rfl, e2]
    rcases lt_trichotomy y.2 y'.2 with hlt | heq | hgt
    · simp [hc y y' h1 h2 hlt] at hy'
    · exact Prod.ext h1 heq
    · simp [hc y' y h1.symm h2.symm hgt] at hy
  refine sum_prod_comp_eq_of_injOn (fun y => eX (y.1, r y)) N hinj
    (fun x => S.simW pk (eY.symm (H x))) (fun x => S.sum_simW pk _)
    (fun o => S.offWin eX eY eQ eA A pk H (ansTab r o)) ?_
  intro o o' hoo
  have hT : simTab eQ eA (hashOf eX eY H) (ansTab r o) =
      simTab eQ eA (hashOf eX eY H) (ansTab r o') := by
    funext i
    simp only [simTab, collides_congr (ansTab r o) (fun y => (r y, ())) (fun _ => rfl),
      collides_congr (ansTab r o') (fun y => (r y, ())) (fun _ => rfl)]
    split_ifs with hcol
    · rfl
    · simp only [honestTab, ansTab]
      rw [hoo _ (by simp [N, hcol])]
  unfold offWin
  rw [hT]
  rfl

omit [Fintype Tgt] in
/-- At fixed salts, the programmed oracle and the preimages at its points have the law of the
    oracle programmed with domain samples and the samples. -/
theorem sum_progW_pt_eq_dom [Finite Tgt] (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n)
    (eQ : Msg × Fin T ≃ Fin c) (eA : Option (Salt × Sig) ≃ Fin a)
    (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig)) (pk : PK) (r : Msg × Fin T → Salt) :
    ∑ H : Fin m → Fin n, (∏ x, S.progW eX eY pk (ansTab r fun _ => none) x (H x)) *
        ∑ o : Fin m → Option Sig, (∏ x, S.simW pk (eY.symm (H x)) (o x)) *
          S.offWin eX eY eQ eA A pk H (ansTab r fun y => o (eX (y.1, r y))) =
      ∑ u : Fin m → Fin n × S.DCoins,
        (∏ _x : Fin m, (n : ℝ≥0∞)⁻¹ * (Fintype.card S.DCoins : ℝ≥0∞)⁻¹) *
          S.offWin eX eY eQ eA A pk (S.domOracle eX eY pk r u)
            (S.domTab eX pk r fun x => (u x).2) := by
  have hp : ∀ x, S.progW eX eY pk (ansTab r fun _ => none) x = fun z =>
      if salted eX (fun y => (r y, ())) x then S.imgN eY pk z else (n : ℝ≥0∞)⁻¹ := fun x => by
    funext z
    simp only [progW, salted_congr eX (ansTab r fun _ => none) (fun y => (r y, ())) fun _ => rfl]
  have hs : ∀ y : Msg × Fin T, salted eX (fun y => (r y, ())) (eX (y.1, r y)) = true :=
    fun y => salted_self eX (fun y => (r y, ())) y
  have hcomb : ∑ H : Fin m → Fin n, (∏ x, S.progW eX eY pk (ansTab r fun _ => none) x (H x)) *
        ∑ o : Fin m → Option Sig, (∏ x, S.simW pk (eY.symm (H x)) (o x)) *
          S.offWin eX eY eQ eA A pk H (ansTab r fun y => o (eX (y.1, r y))) =
      ∑ u : Fin m → Fin n × Option Sig, (∏ x, S.progW eX eY pk (ansTab r fun _ => none) x
          (u x).1 * S.simW pk (eY.symm (u x).1) (u x).2) *
        S.offWin eX eY eQ eA A pk (fun x => (u x).1) (ansTab r fun y => (u (eX (y.1, r y))).2) := by
    rw [← (Equiv.arrowProdEquivProdArrow (Fin m) (fun _ => Fin n)
      (fun _ => Option Sig)).symm.sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun H _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun o _ => ?_
    simp only [Equiv.arrowProdEquivProdArrow_symm_apply, Finset.prod_mul_distrib, mul_assoc]
  have hcoord : ∀ (x : Fin m) (g : Fin n × Option Sig → ℝ≥0∞),
      ∑ zo : Fin n × Option Sig, S.progW eX eY pk (ansTab r fun _ => none) x zo.1 *
          S.simW pk (eY.symm zo.1) zo.2 *
            g (zo.1, if salted eX (fun y => (r y, ())) x then zo.2 else none) =
        ∑ zd : Fin n × S.DCoins, (n : ℝ≥0∞)⁻¹ * (Fintype.card S.DCoins : ℝ≥0∞)⁻¹ *
          g (if salted eX (fun y => (r y, ())) x then
              (eY (S.f pk (S.sampleDom pk zd.2)), some (S.sampleDom pk zd.2))
            else (zd.1, none)) := by
    intro x g
    simp only [hp x]
    cases salted eX (fun y => (r y, ())) x
    · simp only [Bool.false_eq_true, ↓reduceIte]
      rw [Fintype.sum_prod_type, Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun z _ => ?_
      dsimp only
      rw [← Finset.sum_mul, ← Finset.mul_sum, S.sum_simW, mul_one, ← Finset.sum_mul,
        ← Finset.mul_sum, S.sum_inv_card_DCoins, mul_one]
    · simp only [↓reduceIte, Prod.mk.eta]
      rw [S.sum_imgN_simW eY pk g, Fintype.sum_prod_type]
      simp only [mul_assoc, ← Finset.mul_sum]
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        mul_left_comm (n : ℝ≥0∞)⁻¹, ← mul_assoc (n : ℝ≥0∞)⁻¹,
        ENNReal.inv_mul_cancel (Nat.cast_ne_zero.mpr (NeZero.ne n)) (ENNReal.natCast_ne_top _),
        one_mul]
  have hpi := sum_pi_comp_eq (ι := Fin m) (α := Fin n × Option Sig) (β := Fin n × S.DCoins)
    (γ := Fin n × Option Sig)
    (fun x zo => S.progW eX eY pk (ansTab r fun _ => none) x zo.1 * S.simW pk (eY.symm zo.1) zo.2)
    (fun _ _ => (n : ℝ≥0∞)⁻¹ * (Fintype.card S.DCoins : ℝ≥0∞)⁻¹)
    (fun x zo => (zo.1, if salted eX (fun y => (r y, ())) x then zo.2 else none))
    (fun x zd => if salted eX (fun y => (r y, ())) x then
        (eY (S.f pk (S.sampleDom pk zd.2)), some (S.sampleDom pk zd.2))
      else (zd.1, none)) hcoord
    (fun K => S.offWin eX eY eQ eA A pk (fun x => (K x).1)
      (ansTab r fun y => (K (eX (y.1, r y))).2))
  rw [hcomb]
  refine (Finset.sum_congr rfl fun u _ => ?_).trans (hpi.trans (Finset.sum_congr rfl fun u _ => ?_))
  · simp only [hs, ↓reduceIte]
  · have ho : (fun x => (if salted eX (fun y => (r y, ())) x then
          (eY (S.f pk (S.sampleDom pk (u x).2)), some (S.sampleDom pk (u x).2))
        else ((u x).1, none)).1) = S.domOracle eX eY pk r u := by
      funext x
      unfold domOracle
      split_ifs <;> rfl
    simp only [hs, ↓reduceIte, ho]
    rfl

/-- The image game is the image game with domain samples: at each salted point the oracle
    value and the answer of the entries of that point have the law of the image of a domain
    sample and the sample, so the game is sampled from uniform salts, uniform oracle values
    and uniform domain coins without the secret key. -/
theorem imgGameAt_eq_domGameAt (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n)
    (eQ : Msg × Fin T ≃ Fin c) (eA : Option (Salt × Sig) ≃ Fin a)
    (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig)) (pk : PK) :
    S.imgGameAt eX eY eQ eA A pk = S.domGameAt eX eY eQ eA A pk := by
  rw [S.imgGameAt_eq_ans]
  unfold domGameAt
  refine Finset.sum_congr rfl fun r _ => ?_
  simp_rw [S.sum_ans_eq_sum_pt eX eY eQ eA A pk r]
  rw [S.sum_progW_pt_eq_dom]

variable [Fintype PK] [Fintype SK]

/-- The winning probability of `domGameAt`, averaged over the key distribution. -/
def domGame (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c)
    (eA : Option (Salt × Sig) ≃ Fin a) (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig)) :
    ℝ≥0∞ :=
  ∑ ks, S.keygen ks * S.domGameAt eX eY eQ eA A ks.1

/-- The image game averaged over the keys is the image game with domain samples. -/
theorem imgGame_eq_domGame (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n)
    (eQ : Msg × Fin T ≃ Fin c) (eA : Option (Salt × Sig) ≃ Fin a)
    (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig)) :
    S.imgGame eX eY eQ eA A = S.domGame eX eY eQ eA A := by
  unfold imgGame domGame
  simp_rw [S.imgGameAt_eq_domGameAt]

end DomSample

/-! ## The terminal games and the chain of hops -/

section Terminal

open CatCrypt.Prob

/-- The inversion game of the public function: a public key of the key distribution and a
    uniform target `θ`; an answer `s` wins when it is short and maps to `θ`. -/
def invGame [Fintype Tgt] [Nonempty Tgt] [DecidableEq Tgt] : SearchGame (PK × Tgt) Sig where
  gen := SDistr.bind (S.keygen.map fun ks => some ks.1) fun pk =>
    SDistr.bind (SDistr.uniform Tgt) fun θ => SDistr.pure (pk, θ)
  win x s := S.short x.1 s && decide (S.f x.1 s = x.2)

/-- The collision game of the public function: a public key of the key distribution; an answer
    `(s, s')` wins when the two signatures differ, are short and have the same image. -/
def collGame [DecidableEq Sig] [DecidableEq Tgt] : SearchGame PK (Sig × Sig) where
  gen := S.keygen.map fun ks => some ks.1
  win pk s := decide (s.1 ≠ s.2) && S.short pk s.1 && S.short pk s.2 &&
    decide (S.f pk s.1 = S.f pk s.2)

variable [Fintype Sig] [DecidableEq Sig] [Fintype Tgt] [DecidableEq Tgt] [DecidableEq Salt]
  {m n w q k c a T : ℕ} [Fintype Msg] [DecidableEq Msg] [Fintype Salt] [Nonempty Salt]
  [NeZero m] [NeZero n] [NeZero c] [Fintype PK] [Fintype SK]

/-- Hops A, C and B in sequence: the EUF-CMA advantage is at most the winning probability with
    the oracle programmed at the salted points (`imgGame`) plus
    `k · (condDist + (T - 1) / card Salt)` (hop A), `4 (flatQ q k q + 2 (k + 1)) domDist^(1/2)`
    (hop B) and `T / card Salt` (hop C). -/
theorem saltedPSF_qeufcma_le_img (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n)
    (eQ : Msg × Fin T ≃ Fin c) (eA : Option (Salt × Sig) ≃ Fin a)
    (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig)) :
    qEUFCMAAdvantage S.toQROMSig eX eY eQ eA A ≤
      S.imgGame eX eY eQ eA A +
        k * (S.condDist + ((T - 1 : ℕ) : ℝ≥0∞) * (Fintype.card Salt : ℝ≥0∞)⁻¹) +
        4 * ((flatQ q k q + 2 * (k + 1) : ℕ) : ℝ≥0∞) * S.domDist ^ (1 / 2 : ℝ) +
        (T : ℝ≥0∞) * (Fintype.card Salt : ℝ≥0∞)⁻¹ := by
  have h1 := tsub_le_iff_left.mp ((le_sup_left).trans (S.saltedPSF_hopCond eX eY eQ eA A))
  have h2 := S.saltedPSF_offGraph eX eY eQ eA A
  have h3 := tsub_le_iff_left.mp ((le_sup_left).trans (S.saltedPSF_hopImage eX eY eQ eA A))
  calc qEUFCMAAdvantage S.toQROMSig eX eY eQ eA A
      ≤ S.condGame eX eY eQ eA A +
          k * (S.condDist + ((T - 1 : ℕ) : ℝ≥0∞) * (Fintype.card Salt : ℝ≥0∞)⁻¹) := h1
    _ ≤ (S.imgGame eX eY eQ eA A +
          4 * ((flatQ q k q + 2 * (k + 1) : ℕ) : ℝ≥0∞) * S.domDist ^ (1 / 2 : ℝ) +
          (T : ℝ≥0∞) * (Fintype.card Salt : ℝ≥0∞)⁻¹) +
          k * (S.condDist + ((T - 1 : ℕ) : ℝ≥0∞) * (Fintype.card Salt : ℝ≥0∞)⁻¹) := by
        gcongr
        exact h2.trans (by gcongr)
    _ = _ := by ring

/-! ### Route I: the forgery inverts the public function at a fresh target -/

/-- The expectation under a bind is the expectation of the inner expectations. -/
theorem sdExp_sdBind {α β : Type} (d : SDistr α) (f : α → SDistr β) (g : β → ℝ≥0∞) :
    sdExp (d.bind f) g = sdExp d fun a => sdExp (f a) g := by
  simp only [sdExp, SDistr.bind, PMF.bind_apply]
  simp_rw [← ENNReal.tsum_mul_right]
  rw [ENNReal.tsum_comm, SDistr.tsum_option_eq_add]
  simp_rw [mul_assoc, ENNReal.tsum_mul_left]
  simp [SDistr.fail_apply_some]

omit [Fintype Sig] [DecidableEq Sig] [DecidableEq Salt] [Fintype Msg] [DecidableEq Msg]
  [Fintype Salt] [Nonempty Salt] [NeZero m] [NeZero n] [NeZero c] in
/-- The expectation over the instances of the inversion game: a key pair of the key
    distribution and a uniform target. -/
theorem sdExp_invGame_gen [Nonempty Tgt] (φ : PK × Tgt → ℝ≥0∞) :
    sdExp S.invGame.gen φ =
      ∑ ks, S.keygen ks * ∑ θ, (Fintype.card Tgt : ℝ≥0∞)⁻¹ * φ (ks.1, θ) := by
  unfold invGame
  rw [sdExp_sdBind]
  simp only [sdExp_sdBind]
  classical
  simp only [sdExp, SDistr.pure_apply_some, SDistr.uniform_apply_some, PMF.map_apply,
    tsum_fintype, Finset.sum_mul, ite_mul, Option.some.injEq]
  rw [Finset.sum_comm]
  simp [mul_comm]

/-- The winning predicate of the prover of the inversion reduction at the salts `r`: the
    forgery passes `forgeTest` at the challenge and is off the salted graph of `r`. -/
def invTest (eY : Tgt ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c)
    (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig)) (pk : PK) (r : Msg × Fin T → Salt) :
    Fin (m * n * ancW c k w) → Fin n → Bool :=
  fun i θ => forgeTest S.toQROMSig eY eQ A pk i θ && offGraph A (fun y => (r y, ())) i

/-- The prover of the inversion reduction at the salts `r` and the coins `u`: the flattened
    adversary against the signing table of the domain samples, with its query register moved
    into an ancilla and the forgery point written into the query register. -/
def invProver (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c)
    (eA : Option (Salt × Sig) ≃ Fin a) (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig))
    (pk : PK) (r : Msg × Fin T → Salt) (u : Fin m → Fin n × S.DCoins) :
    QAdv m n (ancW c k w * m) (flatQ q k q) :=
  moveAdv (toQAdv (A.run pk) (simTab eQ eA (hashOf eX eY (S.domOracle eX eY pk r u))
      (S.domTab eX pk r fun x => (u x).2))) (forgePoint S.toQROMSig eX A pk)

/-- The verifier of the prover `invProver` at the salts `r`. -/
def invVer (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c)
    (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig)) (pk : PK) (r : Msg × Fin T → Salt) :
    QVerifier m n (ancW c k w * m) :=
  QVerifier.ofPred (moveAcc (forgePoint S.toQROMSig eX A pk) (S.invTest eY eQ A pk r))

/-- The inversion reduction: on the public key `pk` and the target `θ`, with uniform coins of
    salts `r`, oracle values and domain coins `u` and a slot `t`, the deferred interactive game
    of `invProver` against the oracle programmed with domain samples, with the challenge `θ`
    at the measured commitment. It uses no secret key. -/
def B_invQ (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c)
    (eA : Option (Salt × Sig) ≃ Fin a) (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig))
    (x : PK × Tgt)
    (i : (Msg × Fin T → Salt) × (Fin m → Fin n × S.DCoins) × Option (Fin (flatQ q k q) × Bool)) :
    QAdv m n (ancW c k w * m * m * m) 0 :=
  fsDefer (S.invProver eX eY eQ eA A x.1 i.1 i.2.1) (S.invVer eX eY eQ A x.1 i.1)
    (S.domOracle eX eY x.1 i.1 i.2.1) i.2.2 (eY x.2)

/-- The answer of the inversion reduction read from a basis state of its register: the
    preimage of the forgery of the basis state of the flattened adversary. -/
def invOut (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig))
    (j : Fin (m * n * (ancW c k w * m * m * m))) : Sig :=
  let u := (regIdx m n (ancW c k w)).symm (fsDeferDec m n (ancW c k w * m) j).1
  (A.forge (oracleIndex m n (ancW c k w) ((u.2, u.1.1.2), u.1.2))).2.2

omit [Fintype Sig] [DecidableEq Sig] [Fintype Tgt] [DecidableEq Tgt] [DecidableEq Salt]
  [DecidableEq Msg] [Fintype Salt] [Nonempty Salt] [NeZero m] [NeZero n] [NeZero c] [Fintype PK]
  [Fintype SK] in
/-- At a point that is not salted, updating the coins updates the oracle programmed with
    domain samples by the oracle value of the coins. -/
theorem domOracle_update (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n) (pk : PK)
    (r : Msg × Fin T → Salt) (u : Fin m → Fin n × S.DCoins) (x : Fin m) (z : Fin n × S.DCoins)
    (hx : salted eX (fun y => (r y, ())) x = false) :
    S.domOracle eX eY pk r (Function.update u x z) =
      Function.update (S.domOracle eX eY pk r u) x z.1 := by
  funext x'
  by_cases h : x' = x
  · subst h
    simp [domOracle, hx]
  · simp [domOracle, Function.update_of_ne h]

omit [Fintype Sig] [DecidableEq Sig] [Fintype Tgt] [DecidableEq Tgt] [DecidableEq Salt]
  [DecidableEq Msg] [Fintype Salt] [Nonempty Salt] [NeZero m] [NeZero n] [NeZero c] [Fintype PK]
  [Fintype SK] in
/-- At a point that is not salted, the table of domain samples does not read the coins. -/
theorem domTab_update (eX : Msg × Salt ≃ Fin m) (pk : PK) (r : Msg × Fin T → Salt)
    (u : Fin m → Fin n × S.DCoins) (x : Fin m) (z : Fin n × S.DCoins)
    (hx : salted eX (fun y => (r y, ())) x = false) :
    (S.domTab eX pk r fun x' => (Function.update u x z x').2) =
      S.domTab eX pk r fun x' => (u x').2 := by
  funext y
  have hne : eX (y.1, r y) ≠ x := fun h => by
    have hs := salted_self eX (fun y => (r y, ())) y
    rw [h, hx] at hs
    exact Bool.false_ne_true hs
  simp [domTab, ansTab, Function.update_of_ne hne]

omit [Fintype Sig] [DecidableEq Sig] [Fintype Tgt] [DecidableEq Tgt] [Fintype Msg]
  [DecidableEq Msg] [Fintype Salt] [Nonempty Salt] [NeZero m] [NeZero n] [NeZero c] [Fintype PK]
  [Fintype SK] in
/-- The simulated signing table of the domain samples does not read the hash. -/
theorem simTab_domTab_congr (eX : Msg × Salt ≃ Fin m) (eQ : Msg × Fin T ≃ Fin c)
    (eA : Option (Salt × Sig) ≃ Fin a) (H H' : Msg × Salt → Tgt) (pk : PK)
    (r : Msg × Fin T → Salt) (d : Fin m → S.DCoins) :
    simTab eQ eA H (S.domTab eX pk r d) = simTab eQ eA H' (S.domTab eX pk r d) := by
  funext i
  simp [simTab, honestTab, domTab, ansTab]

omit [Fintype Sig] [DecidableEq Sig] [Fintype Tgt] [DecidableEq Msg] [NeZero n] [Fintype PK]
  [Fintype SK] in
/-- At a point that is not salted, the prover of the inversion reduction does not read the
    coins. -/
theorem invProver_update (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n)
    (eQ : Msg × Fin T ≃ Fin c) (eA : Option (Salt × Sig) ≃ Fin a)
    (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig)) (pk : PK) (r : Msg × Fin T → Salt)
    (u : Fin m → Fin n × S.DCoins) (x : Fin m) (z : Fin n × S.DCoins)
    (hx : salted eX (fun y => (r y, ())) x = false) :
    S.invProver eX eY eQ eA A pk r (Function.update u x z) =
      S.invProver eX eY eQ eA A pk r u := by
  unfold invProver
  rw [S.domTab_update eX pk r u x z hx, S.simTab_domTab_congr eX eQ eA _
    (hashOf eX eY (S.domOracle eX eY pk r u))]

omit [Fintype Sig] [DecidableEq Sig] [Fintype Tgt] [NeZero m] [NeZero n] [NeZero c] [Fintype PK]
  [Fintype SK] in
/-- At a salted point, the verifier of the inversion reduction is zero: a forgery off the
    salted graph has an unsalted point. -/
theorem invVer_proj_salted (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n)
    (eQ : Msg × Fin T ≃ Fin c) (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig)) (pk : PK)
    (r : Msg × Fin T → Salt) (x : Fin m) (θ : Fin n)
    (hx : salted eX (fun y => (r y, ())) x = true) :
    (S.invVer eX eY eQ A pk r).proj x θ = 0 := by
  refine diagB_eq_zero fun j => ?_
  simp only [salted, decide_eq_true_eq] at hx
  obtain ⟨y, hy⟩ := hx
  simp only [moveAcc, invTest, offGraph, forgePoint, toQROMSig]
  rw [Bool.eq_false_iff]
  intro h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hx', -, hoff⟩ := h
  rw [← hy] at hx'
  obtain ⟨h1, h2⟩ := Prod.mk.inj (eX.injective (of_decide_eq_true hx'))
  apply hoff y.2
  rw [← h1, ← h2]

omit [Fintype Sig] [DecidableEq Sig] [Fintype Tgt] [Fintype PK] [Fintype SK] in
/-- The winning probability of the off-graph forgery adversary in the game with domain samples
    is the probability that the prover of the inversion reduction outputs a point `x` and is
    accepted at the oracle value at `x`. -/
theorem offWin_dom_eq (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n)
    (eQ : Msg × Fin T ≃ Fin c) (eA : Option (Salt × Sig) ≃ Fin a)
    (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig)) (pk : PK) (r : Msg × Fin T → Salt)
    (u : Fin m → Fin n × S.DCoins) :
    S.offWin eX eY eQ eA A pk (S.domOracle eX eY pk r u) (S.domTab eX pk r fun x => (u x).2) =
      ∑ x, prOutAt ((S.invProver eX eY eQ eA A pk r u).withVerifier
        (S.invVer eX eY eQ A pk r) x (S.domOracle eX eY pk r u x))
          (S.domOracle eX eY pk r u) x := by
  unfold offWin forgeOffGen
  rw [← prOut_withFinalB_toQAdv_eq]
  exact prOut_withFinalB_eq_sum_prOutAt _ (forgePoint S.toQROMSig eX A pk)
    (S.invTest eY eQ A pk r) _

omit [Fintype Sig] [DecidableEq Sig] [Fintype Tgt] [Fintype PK] [Fintype SK] in
/-- At a point that is not salted, the oracle value is uniform and independent of the prover:
    the probability of output `x` accepted at the oracle value is the Fiat–Shamir success
    probability at `x`, summed over the coins. -/
theorem sum_prOutAt_unsalted (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n)
    (eQ : Msg × Fin T ≃ Fin c) (eA : Option (Salt × Sig) ≃ Fin a)
    (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig)) (pk : PK) (r : Msg × Fin T → Salt)
    (x : Fin m) (hx : salted eX (fun y => (r y, ())) x = false) :
    ∑ u : Fin m → Fin n × S.DCoins, prOutAt ((S.invProver eX eY eQ eA A pk r u).withVerifier
        (S.invVer eX eY eQ A pk r) x (S.domOracle eX eY pk r u x)) (S.domOracle eX eY pk r u) x =
      ∑ u : Fin m → Fin n × S.DCoins, prFSAt (S.invProver eX eY eQ eA A pk r u)
        (S.invVer eX eY eQ A pk r) (S.domOracle eX eY pk r u) x := by
  have hc0 : (Fintype.card (Fin n × S.DCoins) : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hct : (Fintype.card (Fin n × S.DCoins) : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top _
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hnt : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
  refine (ENNReal.mul_right_inj hc0 hct).mp ?_
  rw [← sum_sum_update_coord x, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  simp only [S.invProver_update eX eY eQ eA A pk r u x _ hx,
    S.domOracle_update eX eY pk r u x _ hx, Function.update_self]
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Fintype.card_prod,
    Fintype.card_fin, Nat.cast_mul, prFSAt]
  rw [← Finset.mul_sum]
  rw [mul_comm (n : ℝ≥0∞), mul_assoc, ← mul_assoc (n : ℝ≥0∞), ENNReal.mul_inv_cancel hn0 hnt,
    one_mul]

omit [Fintype Sig] [DecidableEq Sig] [Fintype Tgt] [Fintype PK] [Fintype SK] in
/-- Route I at the public key `pk`: the game with domain samples is at most `(2 Q + 1)²`,
    `Q = flatQ q k q`, times the acceptance probability of the interactive game of the prover
    of the inversion reduction, averaged over the salts and the coins. -/
theorem domGameAt_le_fsInteractive (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n)
    (eQ : Msg × Fin T ≃ Fin c) (eA : Option (Salt × Sig) ≃ Fin a)
    (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig)) (pk : PK) :
    S.domGameAt eX eY eQ eA A pk ≤ ((2 * flatQ q k q + 1 : ℕ) : ℝ≥0∞) ^ 2 *
      ∑ r : Msg × Fin T → Salt, (∏ _y : Msg × Fin T, (Fintype.card Salt : ℝ≥0∞)⁻¹) *
        ∑ u : Fin m → Fin n × S.DCoins,
          (∏ _x : Fin m, (n : ℝ≥0∞)⁻¹ * (Fintype.card S.DCoins : ℝ≥0∞)⁻¹) *
            prTrue_Q (fsInteractive (S.invProver eX eY eQ eA A pk r u)
              (S.invVer eX eY eQ A pk r) (S.domOracle eX eY pk r u))
              (S.invProver eX eY eQ eA A pk r u).init := by
  unfold domGameAt
  simp only [S.offWin_dom_eq]
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun r _ => ?_
  rw [mul_left_comm]
  gcongr
  rw [← Finset.mul_sum, ← Finset.mul_sum, mul_left_comm]
  gcongr
  rw [Finset.sum_comm]
  calc ∑ x, ∑ u : Fin m → Fin n × S.DCoins,
          prOutAt ((S.invProver eX eY eQ eA A pk r u).withVerifier
            (S.invVer eX eY eQ A pk r) x (S.domOracle eX eY pk r u x))
            (S.domOracle eX eY pk r u) x
      ≤ ∑ x, ∑ u : Fin m → Fin n × S.DCoins, prFSAt (S.invProver eX eY eQ eA A pk r u)
          (S.invVer eX eY eQ A pk r) (S.domOracle eX eY pk r u) x := by
        refine Finset.sum_le_sum fun x _ => ?_
        cases hx : salted eX (fun y => (r y, ())) x
        · exact (S.sum_prOutAt_unsalted eX eY eQ eA A pk r x hx).le
        · simp [prOutAt_withVerifier_eq_zero _ _ _ _ _
            (S.invVer_proj_salted eX eY eQ A pk r x _ hx)]
    _ = ∑ u : Fin m → Fin n × S.DCoins, ∑ x, prFSAt (S.invProver eX eY eQ eA A pk r u)
          (S.invVer eX eY eQ A pk r) (S.domOracle eX eY pk r u) x := Finset.sum_comm
    _ ≤ _ := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun u _ => fiatShamir_interactive _ _ _

omit [Fintype Sig] [DecidableEq Sig] [Fintype Tgt] [Fintype PK] [Fintype SK] in
/-- The deferred interactive game of the prover of the inversion reduction at the challenge
    `eY θ` accepts only on basis states whose answer inverts the public function at `θ`. -/
theorem prOut0_fsDefer_le_inv (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n)
    (eQ : Msg × Fin T ≃ Fin c) (eA : Option (Salt × Sig) ≃ Fin a)
    (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig)) (pk : PK) (r : Msg × Fin T → Salt)
    (u : Fin m → Fin n × S.DCoins) (t : Option (Fin (flatQ q k q) × Bool)) (θ : Tgt) :
    prOut0 (fsDefer (S.invProver eX eY eQ eA A pk r u) (S.invVer eX eY eQ A pk r)
        (S.domOracle eX eY pk r u) t (eY θ)) ≤
      prOut0 ((S.B_invQ eX eY eQ eA A (pk, θ) (r, u, t)).withFinalB fun j =>
        S.short pk (invOut A j) && decide (S.f pk (invOut A j) = θ)) := by
  unfold prOut0 invVer
  rw [QAdv.eq_withFinalB _ _ (fsDefer_final_ofPred _ _ _ _ _)]
  refine prOut_withFinalB_mono (fsDefer (S.invProver eX eY eQ eA A pk r u) _
    (S.domOracle eX eY pk r u) t (eY θ)) (fun j hj => ?_) _
  simp only [moveAcc, invTest, forgeTest, toQROMSig, Equiv.symm_apply_apply,
    Bool.and_eq_true, decide_eq_true_eq] at hj
  unfold invOut
  simp_all

omit [Fintype Sig] [DecidableEq Sig] [DecidableEq Tgt] [DecidableEq Salt]
  [Nonempty Salt] [NeZero m] [NeZero n] [NeZero c] [Fintype PK] [Fintype SK] in
/-- The weights of the salts, the coins, the slot and the challenge of the deferred game are
    the uniform weights of the target and the coins of the inversion reduction. -/
theorem sum_invCoins_eq [Nonempty Tgt] (eY : Tgt ≃ Fin n) {Q : ℕ}
    (G : (Msg × Fin T → Salt) → (Fin m → Fin n × S.DCoins) → Option (Fin Q × Bool) → Tgt →
      ℝ≥0∞) :
    ∑ r : Msg × Fin T → Salt, (∏ _y : Msg × Fin T, (Fintype.card Salt : ℝ≥0∞)⁻¹) *
        ∑ u : Fin m → Fin n × S.DCoins,
          (∏ _x : Fin m, (n : ℝ≥0∞)⁻¹ * (Fintype.card S.DCoins : ℝ≥0∞)⁻¹) *
            ∑ i : Option (Fin Q × Bool) × Fin n,
              (Fintype.card (Option (Fin Q × Bool) × Fin n) : ℝ≥0∞)⁻¹ *
                G r u i.1 (eY.symm i.2) =
      ∑ θ, (Fintype.card Tgt : ℝ≥0∞)⁻¹ *
        ∑ i : (Msg × Fin T → Salt) × (Fin m → Fin n × S.DCoins) × Option (Fin Q × Bool),
          (Fintype.card ((Msg × Fin T → Salt) × (Fin m → Fin n × S.DCoins) ×
            Option (Fin Q × Bool)) : ℝ≥0∞)⁻¹ * G i.1 i.2.1 i.2.2 θ := by
  have ht : ∀ k : ℕ, (k : ℝ≥0∞) ≠ ⊤ := fun k => ENNReal.natCast_ne_top k
  have hT : (Fintype.card Tgt : ℝ≥0∞) = n := by rw [Fintype.card_congr eY, Fintype.card_fin]
  have hR : ∏ _y : Msg × Fin T, (Fintype.card Salt : ℝ≥0∞)⁻¹ =
      (Fintype.card (Msg × Fin T → Salt) : ℝ≥0∞)⁻¹ := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fun, Nat.cast_pow, ENNReal.inv_pow]
  have hU : ∏ _x : Fin m, (n : ℝ≥0∞)⁻¹ * (Fintype.card S.DCoins : ℝ≥0∞)⁻¹ =
      (Fintype.card (Fin m → Fin n × S.DCoins) : ℝ≥0∞)⁻¹ := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fun, Fintype.card_prod, Fintype.card_fin,
      Fintype.card_fin, Nat.cast_pow, Nat.cast_mul,
      ← ENNReal.mul_inv (Or.inr (ht _)) (Or.inl (ht _)), ENNReal.inv_pow]
  have hI : (Fintype.card (Option (Fin Q × Bool) × Fin n) : ℝ≥0∞)⁻¹ =
      (Fintype.card (Option (Fin Q × Bool)) : ℝ≥0∞)⁻¹ * (n : ℝ≥0∞)⁻¹ := by
    rw [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul,
      ENNReal.mul_inv (Or.inr (ht _)) (Or.inl (ht _))]
  have hJ : (Fintype.card ((Msg × Fin T → Salt) × (Fin m → Fin n × S.DCoins) ×
      Option (Fin Q × Bool)) : ℝ≥0∞)⁻¹ = (Fintype.card (Msg × Fin T → Salt) : ℝ≥0∞)⁻¹ *
        ((Fintype.card (Fin m → Fin n × S.DCoins) : ℝ≥0∞)⁻¹ *
          (Fintype.card (Option (Fin Q × Bool)) : ℝ≥0∞)⁻¹) := by
    rw [Fintype.card_prod, Fintype.card_prod, Nat.cast_mul,
      ENNReal.mul_inv (Or.inr (ht _)) (Or.inl (ht _)), Nat.cast_mul,
      ENNReal.mul_inv (Or.inr (ht _)) (Or.inl (ht _))]
  rw [hR, hU, hT, hJ]
  simp only [hI, Fintype.sum_prod_type, Finset.mul_sum]
  symm
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [← Equiv.sum_comp eY.symm]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring

omit [Fintype Sig] [DecidableEq Sig] in
/-- Route I averaged over the keys: the game with domain samples is at most `(2 Q + 1)²` times
    the inversion advantage of `B_invQ`, `Q = flatQ q k q`. -/
theorem domGame_le_inv [Nonempty Tgt] (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n)
    (eQ : Msg × Fin T ≃ Fin c) (eA : Option (Salt × Sig) ≃ Fin a)
    (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig)) :
    S.domGame eX eY eQ eA A ≤ ((2 * flatQ q k q + 1 : ℕ) : ℝ≥0∞) ^ 2 *
      qSearchAdv S.invGame (S.B_invQ eX eY eQ eA A) (invOut A) := by
  unfold domGame qSearchAdv
  rw [S.sdExp_invGame_gen, Finset.mul_sum]
  refine Finset.sum_le_sum fun ks _ => ?_
  rw [mul_left_comm]
  gcongr
  refine (S.domGameAt_le_fsInteractive eX eY eQ eA A ks.1).trans ?_
  gcongr
  simp only [prTrue_fsInteractive_eq_sum_prOut0_fsDefer]
  refine le_of_le_of_eq ?_ (S.sum_invCoins_eq eY fun r u t θ =>
    prOut0 ((S.B_invQ eX eY eQ eA A (ks.1, θ) (r, u, t)).withFinalB fun j =>
      S.invGame.win (ks.1, θ) (invOut A j)))
  gcongr with r _ u _ i _
  have h := S.prOut0_fsDefer_le_inv eX eY eQ eA A ks.1 r u i.1 (eY.symm i.2)
  simp only [Equiv.apply_symm_apply] at h
  exact h

/-- Route I: the EUF-CMA advantage of salted hash-and-sign is at most `(2 Q + 1)²` times the
    inversion advantage of `B_invQ`, `Q = flatQ q k q`, plus the terms of hops A, B and C. -/
theorem saltedPSF_qeufcma_le_inv [Nonempty Tgt] (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n)
    (eQ : Msg × Fin T ≃ Fin c) (eA : Option (Salt × Sig) ≃ Fin a)
    (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig)) :
    qEUFCMAAdvantage S.toQROMSig eX eY eQ eA A ≤
      ((2 * flatQ q k q + 1 : ℕ) : ℝ≥0∞) ^ 2 *
          qSearchAdv S.invGame (S.B_invQ eX eY eQ eA A) (invOut A) +
        k * (S.condDist + ((T - 1 : ℕ) : ℝ≥0∞) * (Fintype.card Salt : ℝ≥0∞)⁻¹) +
        4 * ((flatQ q k q + 2 * (k + 1) : ℕ) : ℝ≥0∞) * S.domDist ^ (1 / 2 : ℝ) +
        (T : ℝ≥0∞) * (Fintype.card Salt : ℝ≥0∞)⁻¹ := by
  refine (S.saltedPSF_qeufcma_le_img eX eY eQ eA A).trans ?_
  rw [S.imgGame_eq_domGame]
  gcongr
  exact S.domGame_le_inv eX eY eQ eA A

end Terminal

/-! ## Route II, hop B at every point: the oracle programmed with the image law -/

section HopAll

variable [Fintype Sig] [DecidableEq Sig] [Fintype Tgt] [DecidableEq Tgt] [DecidableEq Salt]
  {m n w q k c a T : ℕ} [Fintype Msg] [DecidableEq Msg] [Fintype Salt] [Nonempty Salt]
  [NeZero m] [NeZero n] [NeZero c]

/-- The winning probability of the forgery adversary at the oracle `H` and the table `v`, with
    the simulated signing table of `v`. -/
def allWin (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c)
    (eA : Option (Salt × Sig) ≃ Fin a) (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig))
    (pk : PK) (H : Fin m → Fin n) (v : Msg × Fin T → Salt × (Tgt → Option Sig)) : ℝ≥0∞ :=
  prOutMRGen (S.forgeGen eX eY eQ A pk H) H (simTab eQ eA (hashOf eX eY H) v)

/-- The forgery adversary of `forgeGen` with its forgery test as a final query and its signing
    rounds answered through the oracle at the salted points of the table `v`: the adversary
    `forgeImgGen` without the off-graph test. It does not depend on the oracle. -/
def forgeAllGen (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c)
    (eA : Option (Salt × Sig) ≃ Fin a) (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig))
    (pk : PK) (v : Msg × Fin T → Salt × (Tgt → Option Sig)) :
    QAdvMRGen m n (ancW c k w * (m * n) * (m * n)) (q + 1 + 1) k c a :=
  ((recordGen (A.run pk) fun _ => true).withFinalQuery (forgePoint S.toQROMSig eX A pk)
      (fun i θ => forgeTest S.toQROMSig eY eQ A pk i θ)).viaOracle
    (fun i => eX ((eQ.symm i).1, (v (eQ.symm i)).1))
    (fun i z => if collides v (eQ.symm i) then eA none else
      eA (((v (eQ.symm i)).2 (eY.symm z)).map fun s => ((v (eQ.symm i)).1, s)))

omit [Fintype Sig] [DecidableEq Sig] [Fintype Tgt] [Fintype Msg] in
/-- The adversary `forgeAllGen` at every round function accepts with the probability of
    `forgeGen` at the simulated signing table. -/
theorem prOutMRGen_forgeAllGen (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n)
    (eQ : Msg × Fin T ≃ Fin c) (eA : Option (Salt × Sig) ≃ Fin a)
    (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig)) (pk : PK)
    (v : Msg × Fin T → Salt × (Tgt → Option Sig)) (H : Fin m → Fin n) (f₀ : Fin c → Fin a) :
    prOutMRGen (S.forgeAllGen eX eY eQ eA A pk v) H f₀ = S.allWin eX eY eQ eA A pk H v := by
  rw [forgeAllGen, prOutMRGen_viaOracle_eq, prOutMRGen_withFinalQuery_eq]
  rfl

/-- The winning probability of `condGameAt` with the oracle programmed at every point:
    uniform salts and samplers of the simulator, and independent oracle values of the image law
    of a domain sample. -/
def allGameAt (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c)
    (eA : Option (Salt × Sig) ≃ Fin a) (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig))
    (pk : PK) : ℝ≥0∞ :=
  ∑ v : Msg × Fin T → Salt × (Tgt → Option Sig),
    (∏ y, (Fintype.card Salt : ℝ≥0∞)⁻¹ * S.simSamplerW pk (v y).2) *
      ∑ H : Fin m → Fin n, (∏ x, S.imgN eY pk (H x)) * S.allWin eX eY eQ eA A pk H v

/-- `condGameAt` with the uniform oracle written as the first outputs of independent couplings
    of the uniform value and the image law, and the forgery adversary `forgeAllGen`. -/
theorem condGameAt_eq_cpl (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n)
    (eQ : Msg × Fin T ≃ Fin c) (eA : Option (Salt × Sig) ≃ Fin a)
    (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig)) (pk : PK) :
    S.condGameAt eX eY eQ eA A pk =
      ∑ v : Msg × Fin T → Salt × (Tgt → Option Sig),
        (∏ y, (Fintype.card Salt : ℝ≥0∞)⁻¹ * S.simSamplerW pk (v y).2) *
          ∑ u : Fin m → Bool × Fin n × Fin n × Fin n, (∏ x, S.oCplW eY pk (u x)) *
            prOutMRGen (S.forgeAllGen eX eY eQ eA A pk v) (fun x => cplFst (u x))
              (fun _ => eA none) := by
  unfold condGameAt
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun v _ => ?_
  have hpi := sum_pi_comp_eq (ι := Fin m) (fun _ => S.oCplW eY pk)
    (fun _ _ => (n : ℝ≥0∞)⁻¹) (fun _ => cplFst) (fun _ z => z)
    (fun _ g => maxCouplingW_sum_fst (S.oCplW_laws eY pk).1 (S.oCplW_laws eY pk).2 g)
    (fun H => prOutMRGen (S.forgeAllGen eX eY eQ eA A pk v) H (fun _ => eA none))
  simp only [← Finset.mul_sum]
  rw [hpi]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun H _ => ?_
  rw [prOutMRGen_forgeAllGen]
  unfold allWin
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, Fintype.card_fun, Fintype.card_fin,
    Fintype.card_fin, Nat.cast_pow, ENNReal.inv_pow]
  ring

/-- `allGameAt` with the programmed oracle written as the second outputs of the couplings and
    the forgery adversary `forgeAllGen`. -/
theorem allGameAt_eq_cpl (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n)
    (eQ : Msg × Fin T ≃ Fin c) (eA : Option (Salt × Sig) ≃ Fin a)
    (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig)) (pk : PK) :
    S.allGameAt eX eY eQ eA A pk =
      ∑ v : Msg × Fin T → Salt × (Tgt → Option Sig),
        (∏ y, (Fintype.card Salt : ℝ≥0∞)⁻¹ * S.simSamplerW pk (v y).2) *
          ∑ u : Fin m → Bool × Fin n × Fin n × Fin n, (∏ x, S.oCplW eY pk (u x)) *
            prOutMRGen (S.forgeAllGen eX eY eQ eA A pk v) (fun x => cplSnd (u x))
              (fun _ => eA none) := by
  unfold allGameAt
  refine Finset.sum_congr rfl fun v _ => ?_
  congr 1
  have hpi := sum_pi_comp_eq (ι := Fin m) (fun _ => S.oCplW eY pk)
    (fun _ z => S.imgN eY pk z) (fun _ => cplSnd) (fun _ z => z)
    (fun _ g => maxCouplingW_sum_snd (S.oCplW_laws eY pk).1 (S.oCplW_laws eY pk).2 g)
    (fun H => prOutMRGen (S.forgeAllGen eX eY eQ eA A pk v) H (fun _ => eA none))
  rw [hpi]
  refine Finset.sum_congr rfl fun H _ => ?_
  rw [prOutMRGen_forgeAllGen]

/-- Hop B at every point and one public key: programming the oracle at every point with the
    image law of a domain sample changes the winning probability of `condGameAt` by at most
    `4 (flatQ q k q + 2 (k + 1)) domDistAt^(1/2)`. The proof is the one of `hopImageAt` with
    the second outputs of the couplings at every point. -/
theorem hopAllAt (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c)
    (eA : Option (Salt × Sig) ≃ Fin a) (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig))
    (pk : PK) :
    absDiff (S.condGameAt eX eY eQ eA A pk) (S.allGameAt eX eY eQ eA A pk) ≤
      4 * ((flatQ q k q + 2 * (k + 1) : ℕ) : ℝ≥0∞) * S.domDistAt pk ^ (1 / 2 : ℝ) := by
  classical
  set μ : (Msg × Fin T → Salt × (Tgt → Option Sig)) × (Fin m → Bool × Fin n × Fin n × Fin n) →
      ℝ≥0∞ := fun ω =>
    (∏ y, (Fintype.card Salt : ℝ≥0∞)⁻¹ * S.simSamplerW pk (ω.1 y).2) *
      ∏ x, S.oCplW eY pk (ω.2 x) with hμdef
  have hsplit : ∀ G : (Msg × Fin T → Salt × (Tgt → Option Sig)) →
      (Fin m → Bool × Fin n × Fin n × Fin n) → ℝ≥0∞,
      ∑ ω, μ ω * G ω.1 ω.2 = ∑ v, (∏ y, (Fintype.card Salt : ℝ≥0∞)⁻¹ *
        S.simSamplerW pk (v y).2) * ∑ u, (∏ x, S.oCplW eY pk (u x)) * G v u := by
    intro G
    simp only [hμdef, Fintype.sum_prod_type, Finset.mul_sum, mul_assoc]
  have hμ : ∑ ω, μ ω = 1 := by
    have h := hsplit fun _ _ => 1
    simp only [mul_one] at h
    rw [h, sum_prod_eq_one _ fun _ => S.sum_oCplW eY pk]
    simp only [mul_one]
    exact sum_prod_eq_one (ι := Msg × Fin T) (β := Salt × (Tgt → Option Sig))
      (fun _ x => (Fintype.card Salt : ℝ≥0∞)⁻¹ * S.simSamplerW pk x.2)
      fun _ => S.sum_salt_sim_mass pk
  set D : (Msg × Fin T → Salt × (Tgt → Option Sig)) ×
      (Fin m → Bool × Fin n × Fin n × Fin n) → Finset (Fin m) :=
    fun ω => Finset.univ.filter fun x => (ω.2 x).1 = true with hD
  set lam := tvW (fun _ : Fin n => (n : ℝ≥0∞)⁻¹) (S.imgN eY pk) with hlam
  have hsp : ∀ j x h (g : Fin c → Fin a),
      ∑ ω, μ ω * (if ω.1 = j ∧ (fun x' => (ω.2 x').2.1) = h ∧ (fun _ => eA none) = g ∧
        x ∈ D ω then 1 else 0) ≤
      lam * ∑ ω, μ ω * (if ω.1 = j ∧ (fun x' => (ω.2 x').2.1) = h ∧
        (fun _ => eA none) = g then 1 else 0) := by
    intro j x h g
    exact S.sum_tab_cpl_fail_le eY pk
      (fun v => ∏ y, (Fintype.card Salt : ℝ≥0∞)⁻¹ * S.simSamplerW pk (v y).2) j x h
      ((fun _ : Fin c => eA none) = g)
  have h1 := prOutMRGen_resample_gentle_fiber_le (S.forgeAllGen eX eY eQ eA A pk) Prod.fst μ hμ
    (fun ω x => cplFst (ω.2 x)) (fun ω x => (ω.2 x).2.1) (fun _ _ => eA none) D lam
    (fun ω x hx => by simp_all [cplFst]) hsp
  have h3 := prOutMRGen_resample_gentle_fiber_le (S.forgeAllGen eX eY eQ eA A pk) Prod.fst μ hμ
    (fun ω x => cplSnd (ω.2 x)) (fun ω x => (ω.2 x).2.1) (fun _ _ => eA none) D lam
    (fun ω x hx => by simp_all [cplSnd]) hsp
  have hE1 := S.condGameAt_eq_cpl eX eY eQ eA A pk
  have hE3 := S.allGameAt_eq_cpl eX eY eQ eA A pk
  rw [← hsplit] at hE1 hE3
  have hQ : flatQ (q + 1 + 1) k (q + 1 + 1) = flatQ q k q + 2 * (k + 1) := by
    rw [flatQ_succ_succ, flatQ_succ_succ]
    ring
  beta_reduce at h1 h3
  rw [absDiff_comm] at h3
  have key := (absDiff_triangle _ _ _).trans (add_le_add h1 h3)
  rw [hE1, hE3, ← hQ, ← S.tvW_oCpl_eq eY pk, ← hlam]
  refine key.trans (le_of_eq ?_)
  ring

variable [Fintype PK] [Fintype SK]

/-- The winning probability of `allGameAt`, averaged over the key distribution. -/
def allGame (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c)
    (eA : Option (Salt × Sig) ≃ Fin a) (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig)) :
    ℝ≥0∞ :=
  ∑ ks, S.keygen ks * S.allGameAt eX eY eQ eA A ks.1

/-- Hop B at every point: in the game after hop A (`condGame`), programming the oracle at every
    point with the image law of a domain sample (`allGame`) changes the winning probability by
    at most `4 (flatQ q k q + 2 (k + 1)) domDist^(1/2)`. -/
theorem saltedPSF_hopAll (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n)
    (eQ : Msg × Fin T ≃ Fin c) (eA : Option (Salt × Sig) ≃ Fin a)
    (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig)) :
    absDiff (S.condGame eX eY eQ eA A) (S.allGame eX eY eQ eA A) ≤
      4 * ((flatQ q k q + 2 * (k + 1) : ℕ) : ℝ≥0∞) * S.domDist ^ (1 / 2 : ℝ) := by
  have hkey : ∑ ks, S.keygen ks = 1 := by
    rw [← tsum_fintype (L := SummationFilter.unconditional (PK × SK))]
    exact S.keygen.tsum_coe
  unfold condGame allGame
  refine (absDiff_sum_le _ _).trans ?_
  calc ∑ ks, absDiff (S.keygen ks * _) (S.keygen ks * S.allGameAt eX eY eQ eA A ks.1)
      ≤ ∑ ks, S.keygen ks * (4 * ((flatQ q k q + 2 * (k + 1) : ℕ) : ℝ≥0∞) *
          S.domDistAt ks.1 ^ (1 / 2 : ℝ)) :=
        Finset.sum_le_sum fun ks _ =>
          (absDiff_mul_left_le _ _ _).trans (by gcongr; exact S.hopAllAt eX eY eQ eA A ks.1)
    _ = 4 * ((flatQ q k q + 2 * (k + 1) : ℕ) : ℝ≥0∞) *
          ∑ ks, S.keygen ks * S.domDistAt ks.1 ^ (1 / 2 : ℝ) := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun ks _ => by ring
    _ ≤ _ := by
        gcongr
        exact sum_mul_rpow_half_le (fun ks => S.keygen ks) (fun ks => S.domDistAt ks.1) hkey

end HopAll

/-! ## Route II: the game with domain samples at every point -/

section DomAll

variable [Fintype Sig] [DecidableEq Sig] [Fintype Tgt] [DecidableEq Tgt] [DecidableEq Salt]
  {m n w q k c a T : ℕ} [Fintype Msg] [DecidableEq Msg] [Fintype Salt] [Nonempty Salt]
  [NeZero m] [NeZero n] [NeZero c]

/-- The oracle programmed at every point `x` with the image of the domain sample of the coins
    `d x`. -/
def domAllOracle (eY : Tgt ≃ Fin n) (pk : PK) (d : Fin m → S.DCoins) : Fin m → Fin n :=
  fun x => eY (S.f pk (S.sampleDom pk (d x)))

/-- The game with domain samples at every point at the public key `pk`: uniform salts `r` and
    uniform domain coins `d x` at every point `x`; the oracle at `x` is the image of the domain
    sample of `d x`, and the entries of a salted point answer that sample. No secret key is
    used. -/
def domAllGameAt (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c)
    (eA : Option (Salt × Sig) ≃ Fin a) (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig))
    (pk : PK) : ℝ≥0∞ :=
  ∑ r : Msg × Fin T → Salt, (∏ _y : Msg × Fin T, (Fintype.card Salt : ℝ≥0∞)⁻¹) *
    ∑ d : Fin m → S.DCoins, (∏ _x : Fin m, (Fintype.card S.DCoins : ℝ≥0∞)⁻¹) *
      S.allWin eX eY eQ eA A pk (S.domAllOracle eY pk d) (S.domTab eX pk r d)

omit [NeZero m] in
/-- `allGameAt` with the table split into salts and samplers and each sampler replaced by its
    value at the target of its salted point. -/
theorem allGameAt_eq_ans (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n)
    (eQ : Msg × Fin T ≃ Fin c) (eA : Option (Salt × Sig) ≃ Fin a)
    (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig)) (pk : PK) :
    S.allGameAt eX eY eQ eA A pk =
      ∑ r : Msg × Fin T → Salt, (∏ _y : Msg × Fin T, (Fintype.card Salt : ℝ≥0∞)⁻¹) *
        ∑ H : Fin m → Fin n, (∏ x, S.imgN eY pk (H x)) *
          ∑ o : Msg × Fin T → Option Sig,
            (∏ y, S.simW pk (hashOf eX eY H (y.1, r y)) (o y)) *
              S.allWin eX eY eQ eA A pk H (ansTab r o) := by
  unfold allGameAt
  rw [← (Equiv.arrowProdEquivProdArrow (Msg × Fin T) (fun _ => Salt)
      (fun _ => Tgt → Option Sig)).symm.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun r _ => ?_
  simp only [Equiv.arrowProdEquivProdArrow, Equiv.coe_fn_symm_mk, Finset.prod_mul_distrib,
    mul_assoc, ← Finset.mul_sum]
  congr 1
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun H _ => ?_
  refine (Finset.sum_congr rfl fun κ _ => mul_left_comm _ _ _).trans ?_
  rw [← Finset.mul_sum, ← Finset.mul_sum]
  congr 1
  have hev : ∀ (y : Msg × Fin T) (g : Option Sig → ℝ≥0∞),
      ∑ κ, S.simSamplerW pk κ * g (κ (hashOf eX eY H (y.1, r y))) =
        ∑ o, S.simW pk (hashOf eX eY H (y.1, r y)) o * g o := fun y g =>
    sum_prod_eval (fun θ => S.simW pk θ) _ (fun θ => S.sum_simW pk θ) g
  exact sum_pi_comp_eq (ι := Msg × Fin T) (α := Tgt → Option Sig) (β := Option Sig)
    (γ := Option Sig) (fun _ κ => S.simSamplerW pk κ)
    (fun y o => S.simW pk (hashOf eX eY H (y.1, r y)) o)
    (fun y κ => κ (hashOf eX eY H (y.1, r y))) (fun _ o => o) hev
    (fun o => S.allWin eX eY eQ eA A pk H (ansTab r o))

omit [Fintype Tgt] [NeZero m] in
/-- Reindexing the answers of the entries by the salted points in `allWin`: the entries that
    repeat no salt have distinct salted points, and only their answers are read. -/
theorem sum_ans_eq_sum_pt_all (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n)
    (eQ : Msg × Fin T ≃ Fin c) (eA : Option (Salt × Sig) ≃ Fin a)
    (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig)) (pk : PK) (r : Msg × Fin T → Salt)
    (H : Fin m → Fin n) :
    ∑ o : Msg × Fin T → Option Sig, (∏ y, S.simW pk (hashOf eX eY H (y.1, r y)) (o y)) *
        S.allWin eX eY eQ eA A pk H (ansTab r o) =
      ∑ o : Fin m → Option Sig, (∏ x, S.simW pk (eY.symm (H x)) (o x)) *
        S.allWin eX eY eQ eA A pk H (ansTab r fun y => o (eX (y.1, r y))) := by
  let N : Finset (Msg × Fin T) :=
    Finset.univ.filter fun y => collides (fun y => (r y, ())) y = false
  have hinj : Set.InjOn (fun y : Msg × Fin T => eX (y.1, r y)) N := by
    intro y hy y' hy' h
    simp only [N, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hy hy'
    obtain ⟨h1, h2⟩ := Prod.mk.inj (eX.injective h)
    have hc : ∀ z z' : Msg × Fin T, z.1 = z'.1 → r z = r z' → z.2 < z'.2 →
        collides (fun y => (r y, ())) z' = true := fun z z' e1 e2 hlt => by
      simp only [collides, decide_eq_true_eq]
      refine ⟨z.2, hlt, ?_⟩
      rw [show ((z'.1, z.2) : Msg × Fin T) = z from Prod.ext e1.symm rfl, e2]
    rcases lt_trichotomy y.2 y'.2 with hlt | heq | hgt
    · simp [hc y y' h1 h2 hlt] at hy'
    · exact Prod.ext h1 heq
    · simp [hc y' y h1.symm h2.symm hgt] at hy
  refine sum_prod_comp_eq_of_injOn (fun y => eX (y.1, r y)) N hinj
    (fun x => S.simW pk (eY.symm (H x))) (fun x => S.sum_simW pk _)
    (fun o => S.allWin eX eY eQ eA A pk H (ansTab r o)) ?_
  intro o o' hoo
  have hT : simTab eQ eA (hashOf eX eY H) (ansTab r o) =
      simTab eQ eA (hashOf eX eY H) (ansTab r o') := by
    funext i
    simp only [simTab, collides_congr (ansTab r o) (fun y => (r y, ())) (fun _ => rfl),
      collides_congr (ansTab r o') (fun y => (r y, ())) (fun _ => rfl)]
    split_ifs with hcol
    · rfl
    · simp only [honestTab, ansTab]
      rw [hoo _ (by simp [N, hcol])]
  unfold allWin
  rw [hT]

omit [Fintype Tgt] [NeZero m] [Fintype Msg] in
/-- At fixed salts, the oracle of the image law at every point and the preimages at its points
    have the law of the oracle programmed with domain samples at every point and the samples. -/
theorem sum_imgN_pt_eq_dom [Finite Tgt] (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n)
    (eQ : Msg × Fin T ≃ Fin c) (eA : Option (Salt × Sig) ≃ Fin a)
    (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig)) (pk : PK) (r : Msg × Fin T → Salt) :
    ∑ H : Fin m → Fin n, (∏ x, S.imgN eY pk (H x)) *
        ∑ o : Fin m → Option Sig, (∏ x, S.simW pk (eY.symm (H x)) (o x)) *
          S.allWin eX eY eQ eA A pk H (ansTab r fun y => o (eX (y.1, r y))) =
      ∑ d : Fin m → S.DCoins, (∏ _x : Fin m, (Fintype.card S.DCoins : ℝ≥0∞)⁻¹) *
        S.allWin eX eY eQ eA A pk (S.domAllOracle eY pk d) (S.domTab eX pk r d) := by
  have hcomb : ∑ H : Fin m → Fin n, (∏ x, S.imgN eY pk (H x)) *
        ∑ o : Fin m → Option Sig, (∏ x, S.simW pk (eY.symm (H x)) (o x)) *
          S.allWin eX eY eQ eA A pk H (ansTab r fun y => o (eX (y.1, r y))) =
      ∑ u : Fin m → Fin n × Option Sig, (∏ x, S.imgN eY pk (u x).1 *
          S.simW pk (eY.symm (u x).1) (u x).2) *
        S.allWin eX eY eQ eA A pk (fun x => (u x).1)
          (ansTab r fun y => (u (eX (y.1, r y))).2) := by
    rw [← (Equiv.arrowProdEquivProdArrow (Fin m) (fun _ => Fin n)
      (fun _ => Option Sig)).symm.sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun H _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun o _ => ?_
    simp only [Equiv.arrowProdEquivProdArrow_symm_apply, Finset.prod_mul_distrib, mul_assoc]
  rw [hcomb]
  exact sum_pi_comp_eq (ι := Fin m) (α := Fin n × Option Sig) (β := S.DCoins)
    (γ := Fin n × Option Sig)
    (fun _ zo => S.imgN eY pk zo.1 * S.simW pk (eY.symm zo.1) zo.2)
    (fun _ _ => (Fintype.card S.DCoins : ℝ≥0∞)⁻¹) (fun _ zo => zo)
    (fun _ δ => (eY (S.f pk (S.sampleDom pk δ)), some (S.sampleDom pk δ)))
    (fun _ g => S.sum_imgN_simW eY pk g)
    (fun K => S.allWin eX eY eQ eA A pk (fun x => (K x).1)
      (ansTab r fun y => (K (eX (y.1, r y))).2))

omit [NeZero m] in
/-- The game with the oracle of the image law at every point is the game with domain samples
    at every point: at each point the oracle value and the answer of the entries of that point
    have the law of the image of a domain sample and the sample. -/
theorem allGameAt_eq_domAllGameAt (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n)
    (eQ : Msg × Fin T ≃ Fin c) (eA : Option (Salt × Sig) ≃ Fin a)
    (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig)) (pk : PK) :
    S.allGameAt eX eY eQ eA A pk = S.domAllGameAt eX eY eQ eA A pk := by
  rw [S.allGameAt_eq_ans]
  unfold domAllGameAt
  refine Finset.sum_congr rfl fun r _ => ?_
  simp_rw [S.sum_ans_eq_sum_pt_all eX eY eQ eA A pk r]
  rw [S.sum_imgN_pt_eq_dom]

variable [Fintype PK] [Fintype SK]

/-- The winning probability of `domAllGameAt`, averaged over the key distribution. -/
def domAllGame (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c)
    (eA : Option (Salt × Sig) ≃ Fin a) (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig)) :
    ℝ≥0∞ :=
  ∑ ks, S.keygen ks * S.domAllGameAt eX eY eQ eA A ks.1

omit [NeZero m] in
/-- The game with the oracle of the image law at every point, averaged over the keys, is the
    game with domain samples at every point. -/
theorem allGame_eq_domAllGame (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n)
    (eQ : Msg × Fin T ≃ Fin c) (eA : Option (Salt × Sig) ≃ Fin a)
    (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig)) :
    S.allGame eX eY eQ eA A = S.domAllGame eX eY eQ eA A := by
  unfold allGame domAllGame
  simp_rw [S.allGameAt_eq_domAllGameAt]

end DomAll

/-! ### Route II: the forgery collides with the programmed preimage -/

section TerminalColl

open CatCrypt.Prob CatCrypt.Quantum.TensorProduct

variable [Fintype Sig] [DecidableEq Sig] [Fintype Tgt] [DecidableEq Tgt] [DecidableEq Salt]
  {m n w q k c a T : ℕ} [Fintype Msg] [DecidableEq Msg] [Fintype Salt] [Nonempty Salt]
  [NeZero m] [NeZero n] [NeZero c]

/-- The round function `f` with a signing failure at every round input of the message `μ`. -/
def mskTab (eQ : Msg × Fin T ≃ Fin c) (eA : Option (Salt × Sig) ≃ Fin a) (μ : Msg)
    (f : Fin c → Fin a) : Fin c → Fin a :=
  fun j => if (eQ.symm j).1 = μ then eA none else f j

omit [Fintype Sig] [DecidableEq Sig] [Fintype Tgt] [DecidableEq Tgt] [DecidableEq Salt]
  [Fintype Msg] [DecidableEq Msg] [Fintype Salt] [Nonempty Salt] [NeZero m] in
/-- A final test of the recorded adversary that reads no round outcome of the message `μ` has
    the same acceptance probability at two round functions that agree off the round inputs of
    `μ`. -/
theorem prOutMRGen_recordGen_congr_msg (eQ : Msg × Fin T ≃ Fin c) (R : QAdvMR m n w q k c a)
    (G : Fin (m * n * ancW c k w) → Bool) (μ : Msg)
    (hG : ∀ i, G i = true → ∀ j, (eQ.symm (roundOutcomes m n c i j)).1 ≠ μ)
    (H : Fin m → Fin n) (f f' : Fin c → Fin a) (hf : ∀ j, (eQ.symm j).1 ≠ μ → f j = f' j) :
    prOutMRGen (recordGen R G) H f = prOutMRGen (recordGen R G) H f' := by
  classical
  set Y : Finset (Fin c) := Finset.univ.filter fun j => (eQ.symm j).1 = μ with hY
  have hG' : ∀ i, G i = true → ∀ j, roundOutcomes m n c i j ∉ Y := by
    intro i hi j hj
    simp only [hY, Finset.mem_filter, Finset.mem_univ, true_and] at hj
    exact hG i hi j hj
  rw [prOutMRGen_recordGen_eq_prOutAvoidMRGen _ _ Y hG',
    prOutMRGen_recordGen_eq_prOutAvoidMRGen _ _ Y hG']
  refine prOutMRGen_congr_unread _ H fun j hj => ?_
  simp only [hY, Finset.mem_filter, Finset.mem_univ, true_and] at hj
  exact hf j hj

omit [Fintype Tgt] [DecidableEq Salt] [Fintype Msg] [DecidableEq Msg] [Fintype Salt]
  [Nonempty Salt] [NeZero m] [NeZero n] [NeZero c] in
/-- The weight of a domain sample with image `θ` is at most the image weight of `θ` times the
    preimage mass. -/
theorem domW_mul_ite_le (pk : PK) (θ : Tgt) (s : Sig) :
    S.domW pk s * (if S.f pk s = θ then 1 else 0) ≤ S.imgW pk θ * S.preMassAt pk := by
  by_cases h : S.imgW pk θ = 0
  · have h0 := (Finset.sum_eq_zero_iff.mp (show (∑ s, S.domW pk s *
      (if S.f pk s = θ then 1 else 0)) = 0 from h)) s (Finset.mem_univ s)
    rw [h0]
    grind
  · have hI : S.imgW pk θ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top (S.imgW_le_one pk θ)
    calc S.domW pk s * (if S.f pk s = θ then 1 else 0)
        = S.imgW pk θ * S.condW pk θ (some s) := by
          simp only [condW]
          rw [ENNReal.mul_div_cancel h hI]
      _ ≤ S.imgW pk θ * S.preMassAt pk := by
          gcongr
          exact le_iSup₂ (f := fun θ s => S.condW pk θ (some s)) θ s

omit [Fintype Tgt] [DecidableEq Salt] [Fintype Msg] [DecidableEq Msg] [Fintype Salt]
  [Nonempty Salt] [NeZero m] [NeZero n] [NeZero c] in
/-- An average over a domain sample `s` of a function `Φ (f pk s) s` is at most the preimage
    mass times the average of `Φ (f pk s) s'` summed over all `s'`: given its image, a domain
    sample takes each value with probability at most `preMassAt`. -/
theorem sum_domW_self_le [Finite Tgt] (pk : PK) (Φ : Tgt → Sig → ℝ≥0∞) :
    ∑ s, S.domW pk s * Φ (S.f pk s) s ≤
      S.preMassAt pk * ∑ s, S.domW pk s * ∑ s', Φ (S.f pk s) s' := by
  have := Fintype.ofFinite Tgt
  have himg : ∀ g : Tgt → ℝ≥0∞, ∑ s, S.domW pk s * g (S.f pk s) = ∑ θ, S.imgW pk θ * g θ := by
    intro g
    simp only [imgW, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s _ => ?_
    simp only [mul_assoc, ite_mul, one_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, ↓reduceIte]
  calc ∑ s, S.domW pk s * Φ (S.f pk s) s
      = ∑ θ, ∑ s, S.domW pk s * (if S.f pk s = θ then 1 else 0) * Φ θ s := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun s _ => ?_
        simp only [mul_assoc, ite_mul, one_mul, zero_mul, mul_ite, mul_zero, Finset.sum_ite_eq,
          Finset.mem_univ, ↓reduceIte]
    _ ≤ ∑ θ, ∑ s, S.imgW pk θ * S.preMassAt pk * Φ θ s := by
        exact Finset.sum_le_sum fun θ _ => Finset.sum_le_sum fun s _ =>
          mul_le_mul_left (S.domW_mul_ite_le pk θ s) _
    _ = S.preMassAt pk * ∑ θ, S.imgW pk θ * ∑ s', Φ θ s' := by
        simp only [Finset.mul_sum]
        exact Finset.sum_congr rfl fun θ _ => Finset.sum_congr rfl fun s _ => by ring
    _ = _ := by rw [himg fun θ => ∑ s', Φ θ s']

/-- The answer of the collision reduction read from a basis state of its register: the
    preimage of the forgery of the basis state of the flattened adversary, and the domain
    sample held in the ancilla. -/
def collOut (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig))
    (j : Fin (m * n * (ancW c k w * Fintype.card Sig))) : Sig × Sig :=
  ((A.forge ((finProdEquiv (m * n * ancW c k w) (Fintype.card Sig)).symm
      ((ancE m n (ancW c k w) (Fintype.card Sig)).symm j)).1).2.2,
    (Fintype.equivFin Sig).symm ((finProdEquiv (m * n * ancW c k w) (Fintype.card Sig)).symm
      ((ancE m n (ancW c k w) (Fintype.card Sig)).symm j)).2)

variable [Nonempty Sig]

/-- The collision reduction: on the public key `pk`, with uniform salts `r` and domain coins
    `d`, the flattened adversary run against the oracle programmed with domain samples at every
    point and the signing table of those samples, without oracle access, followed by writing the
    domain sample at the forgery point into an ancilla. It uses no secret key. -/
def B_collQ (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c)
    (eA : Option (Salt × Sig) ≃ Fin a) (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig))
    (pk : PK) (i : (Msg × Fin T → Salt) × (Fin m → S.DCoins)) :
    QAdv m n (ancW c k w * Fintype.card Sig) 0 :=
  extAdv (absorbOracle (toQAdv (A.run pk) (simTab eQ eA
      (hashOf eX eY (S.domAllOracle eY pk i.2)) (S.domTab eX pk i.1 i.2)))
      (S.domAllOracle eY pk i.2))
    fun j => Fintype.equivFin Sig (S.sampleDom pk (i.2 (forgePoint S.toQROMSig eX A pk j)))

omit [Fintype Tgt] [Fintype Msg] [NeZero m] in
/-- A winning forgery that differs from the domain sample at its point is a collision of the
    public function found by `B_collQ`, when domain samples are short. -/
theorem prOutMRGen_ne_le_coll (hshort : ∀ pk d, S.short pk (S.sampleDom pk d) = true)
    (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c)
    (eA : Option (Salt × Sig) ≃ Fin a) (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig))
    (pk : PK) (r : Msg × Fin T → Salt) (d : Fin m → S.DCoins) :
    prOutMRGen (recordGen (A.run pk) fun i =>
        forgeTest S.toQROMSig eY eQ A pk i
            (S.domAllOracle eY pk d (forgePoint S.toQROMSig eX A pk i)) &&
          !decide ((A.forge i).2.2 = S.sampleDom pk (d (forgePoint S.toQROMSig eX A pk i))))
        (S.domAllOracle eY pk d)
        (simTab eQ eA (hashOf eX eY (S.domAllOracle eY pk d)) (S.domTab eX pk r d)) ≤
      prOut0 ((S.B_collQ eX eY eQ eA A pk (r, d)).withFinalB fun j =>
        S.collGame.win pk (collOut A j)) := by
  have habs : ∀ (F : QAdv m n (ancW c k w) (flatQ q k q)) G H,
      (absorbOracle F H).withFinalB G = absorbOracle (F.withFinalB G) H := fun _ _ _ => rfl
  rw [← prOut_withFinalB_toQAdv_eq]
  unfold prOut0 B_collQ
  rw [prOut_extAdv_withFinalB, habs, prOut_absorbOracle]
  refine prOut_withFinalB_mono _ (fun i hi => ?_) _
  generalize forgePoint S.toQROMSig eX A pk i = p at hi ⊢
  simp only [forgeTest, toQROMSig, domAllOracle, Equiv.symm_apply_apply, Bool.and_eq_true,
    Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq] at hi
  simp only [collOut, collGame, Equiv.symm_apply_apply, Bool.and_eq_true, decide_eq_true_eq,
    hshort, and_true]
  grind

/-- The test of the forgery adversary at the point `x`, read with the oracle value `θ` at `x`,
    a preimage `s`, and the signing table masked at the message of `x`. -/
def ptWin (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c)
    (eA : Option (Salt × Sig) ≃ Fin a) (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig))
    (pk : PK) (r : Msg × Fin T → Salt) (x : Fin m) (d : Fin m → S.DCoins) (θ : Tgt) (s : Sig) :
    ℝ≥0∞ :=
  prOutMRGen (recordGen (A.run pk) fun i =>
      (forgeTest S.toQROMSig eY eQ A pk i (eY θ) &&
        decide (forgePoint S.toQROMSig eX A pk i = x)) && decide ((A.forge i).2.2 = s))
    (Function.update (S.domAllOracle eY pk d) x (eY θ))
    (mskTab eQ eA (eX.symm x).1
      (simTab eQ eA (hashOf eX eY (S.domAllOracle eY pk d)) (S.domTab eX pk r d)))

omit [Fintype Sig] [Fintype Tgt] [Fintype Msg] [NeZero m] [Nonempty Sig] in
/-- `ptWin` at the point `x` does not read the domain coins at `x`. -/
theorem ptWin_update (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c)
    (eA : Option (Salt × Sig) ≃ Fin a) (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig))
    (pk : PK) (r : Msg × Fin T → Salt) (x : Fin m) (d : Fin m → S.DCoins) (δ : S.DCoins)
    (θ : Tgt) (s : Sig) :
    S.ptWin eX eY eQ eA A pk r x (Function.update d x δ) θ s =
      S.ptWin eX eY eQ eA A pk r x d θ s := by
  have hO : Function.update (S.domAllOracle eY pk (Function.update d x δ)) x (eY θ) =
      Function.update (S.domAllOracle eY pk d) x (eY θ) := by
    funext z
    by_cases hz : z = x
    · subst hz
      simp
    · simp [Function.update_of_ne hz, domAllOracle]
  have hT : mskTab eQ eA (eX.symm x).1 (simTab eQ eA
        (hashOf eX eY (S.domAllOracle eY pk (Function.update d x δ)))
        (S.domTab eX pk r (Function.update d x δ))) =
      mskTab eQ eA (eX.symm x).1
        (simTab eQ eA (hashOf eX eY (S.domAllOracle eY pk d)) (S.domTab eX pk r d)) := by
    funext j
    unfold mskTab
    split_ifs with hj
    · rfl
    · have hne : eX ((eQ.symm j).1, r (eQ.symm j)) ≠ x := by
        intro h
        apply hj
        rw [← h, Equiv.symm_apply_apply]
      simp only [simTab, honestTab, domTab, ansTab, collides, Function.update_of_ne hne]
      rfl
  unfold ptWin
  rw [hO, hT]

omit [Fintype Sig] [Fintype Tgt] [Fintype Msg] [NeZero m] [Nonempty Sig] in
/-- The winning test of the game with domain samples at the point `x` with the preimage `s` is
    `ptWin` at the oracle value of `x`: the test reads no round outcome of the message of `x`,
    and at `x` the oracle is the image of the domain sample of `d x`. -/
theorem prOutMRGen_pt_eq_ptWin (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n)
    (eQ : Msg × Fin T ≃ Fin c) (eA : Option (Salt × Sig) ≃ Fin a)
    (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig)) (pk : PK) (r : Msg × Fin T → Salt)
    (x : Fin m) (d : Fin m → S.DCoins) (s : Sig) :
    prOutMRGen (recordGen (A.run pk) fun i =>
        (forgeTest S.toQROMSig eY eQ A pk i
            (S.domAllOracle eY pk d (forgePoint S.toQROMSig eX A pk i)) &&
          decide (forgePoint S.toQROMSig eX A pk i = x)) && decide ((A.forge i).2.2 = s))
        (S.domAllOracle eY pk d)
        (simTab eQ eA (hashOf eX eY (S.domAllOracle eY pk d)) (S.domTab eX pk r d)) =
      S.ptWin eX eY eQ eA A pk r x d (S.f pk (S.sampleDom pk (d x))) s := by
  have htest : (fun i => (forgeTest S.toQROMSig eY eQ A pk i
        (S.domAllOracle eY pk d (forgePoint S.toQROMSig eX A pk i)) &&
          decide (forgePoint S.toQROMSig eX A pk i = x)) && decide ((A.forge i).2.2 = s)) =
      fun i => (forgeTest S.toQROMSig eY eQ A pk i (eY (S.f pk (S.sampleDom pk (d x)))) &&
        decide (forgePoint S.toQROMSig eX A pk i = x)) && decide ((A.forge i).2.2 = s) := by
    funext i
    by_cases hi : forgePoint S.toQROMSig eX A pk i = x
    · simp only [hi]
      rfl
    · simp [hi]
  have hG : ∀ i, ((forgeTest S.toQROMSig eY eQ A pk i (eY (S.f pk (S.sampleDom pk (d x)))) &&
      decide (forgePoint S.toQROMSig eX A pk i = x)) && decide ((A.forge i).2.2 = s)) = true →
        ∀ j, (eQ.symm (roundOutcomes m n c i j)).1 ≠ (eX.symm x).1 := by
    intro i hi j
    simp only [forgeTest, forgePoint, toQROMSig, Bool.and_eq_true, decide_eq_true_eq] at hi
    obtain ⟨⟨⟨_, hfr⟩, hx⟩, _⟩ := hi
    rw [← of_decide_eq_true hx, Equiv.symm_apply_apply]
    exact hfr j
  rw [htest, prOutMRGen_recordGen_congr_msg eQ (A.run pk) _ (eX.symm x).1 hG
    (S.domAllOracle eY pk d)
    (simTab eQ eA (hashOf eX eY (S.domAllOracle eY pk d)) (S.domTab eX pk r d))
    (mskTab eQ eA (eX.symm x).1
      (simTab eQ eA (hashOf eX eY (S.domAllOracle eY pk d)) (S.domTab eX pk r d)))
    fun j hj => by simp [mskTab, hj]]
  unfold ptWin
  congr 1
  exact (Function.update_eq_self x _).symm

omit [Fintype Tgt] [Fintype Msg] [NeZero m] [Nonempty Sig] in
/-- The preimage step at the point `x`: a winning forgery at `x` equal to the domain sample of
    `x` has probability at most `preMassAt` times the probability of a winning forgery at
    `x`, since the run reads the domain sample of `x` only through its image. -/
theorem sum_domAll_pt_le [Finite Tgt] (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n)
    (eQ : Msg × Fin T ≃ Fin c) (eA : Option (Salt × Sig) ≃ Fin a)
    (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig)) (pk : PK) (r : Msg × Fin T → Salt)
    (x : Fin m) :
    ∑ d : Fin m → S.DCoins, (∏ _x : Fin m, (Fintype.card S.DCoins : ℝ≥0∞)⁻¹) *
        prOutMRGen (recordGen (A.run pk) fun i =>
          (forgeTest S.toQROMSig eY eQ A pk i
              (S.domAllOracle eY pk d (forgePoint S.toQROMSig eX A pk i)) &&
            decide (forgePoint S.toQROMSig eX A pk i = x)) &&
            decide ((A.forge i).2.2 = S.sampleDom pk (d x)))
          (S.domAllOracle eY pk d)
          (simTab eQ eA (hashOf eX eY (S.domAllOracle eY pk d)) (S.domTab eX pk r d)) ≤
      S.preMassAt pk * ∑ d : Fin m → S.DCoins,
        (∏ _x : Fin m, (Fintype.card S.DCoins : ℝ≥0∞)⁻¹) *
          prOutMRGen (recordGen (A.run pk) fun i =>
            forgeTest S.toQROMSig eY eQ A pk i
                (S.domAllOracle eY pk d (forgePoint S.toQROMSig eX A pk i)) &&
              decide (forgePoint S.toQROMSig eX A pk i = x))
            (S.domAllOracle eY pk d)
            (simTab eQ eA (hashOf eX eY (S.domAllOracle eY pk d)) (S.domTab eX pk r d)) := by
  have hpart : ∀ d : Fin m → S.DCoins, prOutMRGen (recordGen (A.run pk) fun i =>
      forgeTest S.toQROMSig eY eQ A pk i
          (S.domAllOracle eY pk d (forgePoint S.toQROMSig eX A pk i)) &&
        decide (forgePoint S.toQROMSig eX A pk i = x))
      (S.domAllOracle eY pk d)
      (simTab eQ eA (hashOf eX eY (S.domAllOracle eY pk d)) (S.domTab eX pk r d)) =
        ∑ s, S.ptWin eX eY eQ eA A pk r x d (S.f pk (S.sampleDom pk (d x))) s := by
    intro d
    rw [prOutMRGen_recordGen_eq_sum_fn _ _ _ (fun i => (A.forge i).2.2)]
    exact Finset.sum_congr rfl fun s _ => S.prOutMRGen_pt_eq_ptWin eX eY eQ eA A pk r x d s
  conv_lhs => enter [2, d, 2]; rw [S.prOutMRGen_pt_eq_ptWin]
  conv_rhs => enter [2, 2, d, 2]; rw [hpart d]
  have h1 := sum_prod_coord_eq (ι := Fin m) (α := S.DCoins)
    (fun _ _ => (Fintype.card S.DCoins : ℝ≥0∞)⁻¹) x S.sum_inv_card_DCoins
    (fun d δ => S.ptWin eX eY eQ eA A pk r x d (S.f pk (S.sampleDom pk δ)) (S.sampleDom pk δ))
    fun u b δ => S.ptWin_update eX eY eQ eA A pk r x u b _ _
  have h2 := sum_prod_coord_eq (ι := Fin m) (α := S.DCoins)
    (fun _ _ => (Fintype.card S.DCoins : ℝ≥0∞)⁻¹) x S.sum_inv_card_DCoins
    (fun d δ => ∑ s, S.ptWin eX eY eQ eA A pk r x d (S.f pk (S.sampleDom pk δ)) s)
    fun u b δ => Finset.sum_congr rfl fun s _ => S.ptWin_update eX eY eQ eA A pk r x u b _ _
  rw [h1, h2, Finset.mul_sum]
  refine Finset.sum_le_sum fun d _ => ?_
  rw [mul_left_comm]
  gcongr
  rw [← S.sum_domW_mul pk fun s' => S.ptWin eX eY eQ eA A pk r x d (S.f pk s') s',
    ← S.sum_domW_mul pk fun s' => ∑ s, S.ptWin eX eY eQ eA A pk r x d (S.f pk s') s]
  exact S.sum_domW_self_le pk (S.ptWin eX eY eQ eA A pk r x d)

omit [Fintype Tgt] [NeZero m] in
/-- Route II at the public key `pk`: the game with domain samples at every point is at most
    `preMassAt` plus the collision probability of `B_collQ`, averaged over its coins. A winning
    forgery equals the domain sample at its point (`sum_domAll_pt_le`) or collides with it
    (`prOutMRGen_ne_le_coll`). -/
theorem domAllGameAt_le_coll [Finite Tgt] (hshort : ∀ pk d, S.short pk (S.sampleDom pk d) = true)
    (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c)
    (eA : Option (Salt × Sig) ≃ Fin a) (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig))
    (pk : PK) :
    S.domAllGameAt eX eY eQ eA A pk ≤ S.preMassAt pk +
      ∑ r : Msg × Fin T → Salt, (∏ _y : Msg × Fin T, (Fintype.card Salt : ℝ≥0∞)⁻¹) *
        ∑ d : Fin m → S.DCoins, (∏ _x : Fin m, (Fintype.card S.DCoins : ℝ≥0∞)⁻¹) *
          prOut0 ((S.B_collQ eX eY eQ eA A pk (r, d)).withFinalB fun j =>
            S.collGame.win pk (collOut A j)) := by
  have hmS : ∑ _r : Msg × Fin T → Salt, ∏ _y : Msg × Fin T, (Fintype.card Salt : ℝ≥0∞)⁻¹ =
      1 :=
    sum_prod_eq_one (fun _ _ => (Fintype.card Salt : ℝ≥0∞)⁻¹) fun _ => by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact ENNReal.mul_inv_cancel (by simp) (ENNReal.natCast_ne_top _)
  have hmD : ∑ _d : Fin m → S.DCoins, ∏ _x : Fin m, (Fintype.card S.DCoins : ℝ≥0∞)⁻¹ = 1 :=
    sum_prod_eq_one (fun _ _ => (Fintype.card S.DCoins : ℝ≥0∞)⁻¹) fun _ => S.sum_inv_card_DCoins
  -- the preimage part at fixed salts
  have heq : ∀ r, ∑ d : Fin m → S.DCoins, (∏ _x : Fin m, (Fintype.card S.DCoins : ℝ≥0∞)⁻¹) *
      prOutMRGen (recordGen (A.run pk) fun i =>
        forgeTest S.toQROMSig eY eQ A pk i
            (S.domAllOracle eY pk d (forgePoint S.toQROMSig eX A pk i)) &&
          decide ((A.forge i).2.2 = S.sampleDom pk (d (forgePoint S.toQROMSig eX A pk i))))
        (S.domAllOracle eY pk d)
        (simTab eQ eA (hashOf eX eY (S.domAllOracle eY pk d)) (S.domTab eX pk r d)) ≤
        S.preMassAt pk := by
    intro r
    have hp : ∀ d : Fin m → S.DCoins, prOutMRGen (recordGen (A.run pk) fun i =>
        forgeTest S.toQROMSig eY eQ A pk i
            (S.domAllOracle eY pk d (forgePoint S.toQROMSig eX A pk i)) &&
          decide ((A.forge i).2.2 = S.sampleDom pk (d (forgePoint S.toQROMSig eX A pk i))))
        (S.domAllOracle eY pk d)
        (simTab eQ eA (hashOf eX eY (S.domAllOracle eY pk d)) (S.domTab eX pk r d)) =
          ∑ x, prOutMRGen (recordGen (A.run pk) fun i =>
            (forgeTest S.toQROMSig eY eQ A pk i
                (S.domAllOracle eY pk d (forgePoint S.toQROMSig eX A pk i)) &&
              decide (forgePoint S.toQROMSig eX A pk i = x)) &&
              decide ((A.forge i).2.2 = S.sampleDom pk (d x)))
            (S.domAllOracle eY pk d)
            (simTab eQ eA (hashOf eX eY (S.domAllOracle eY pk d)) (S.domTab eX pk r d)) := by
      intro d
      rw [prOutMRGen_recordGen_eq_sum_fn _ _ _ (forgePoint S.toQROMSig eX A pk)]
      refine Finset.sum_congr rfl fun x _ => ?_
      congr 2
      funext i
      by_cases hi : forgePoint S.toQROMSig eX A pk i = x
      · simp only [hi, decide_true, Bool.and_true]
      · simp [hi]
    have hq : ∀ d : Fin m → S.DCoins,
        S.allWin eX eY eQ eA A pk (S.domAllOracle eY pk d) (S.domTab eX pk r d) =
          ∑ x, prOutMRGen (recordGen (A.run pk) fun i =>
            forgeTest S.toQROMSig eY eQ A pk i
                (S.domAllOracle eY pk d (forgePoint S.toQROMSig eX A pk i)) &&
              decide (forgePoint S.toQROMSig eX A pk i = x))
            (S.domAllOracle eY pk d)
            (simTab eQ eA (hashOf eX eY (S.domAllOracle eY pk d)) (S.domTab eX pk r d)) :=
      fun d => prOutMRGen_recordGen_eq_sum_fn _ _ _ (forgePoint S.toQROMSig eX A pk) _
    simp only [hp, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine (Finset.sum_le_sum fun x _ => S.sum_domAll_pt_le eX eY eQ eA A pk r x).trans ?_
    rw [← Finset.mul_sum, Finset.sum_comm]
    simp only [← Finset.mul_sum, ← hq]
    calc _ ≤ S.preMassAt pk * ((∏ _x : Fin m, (Fintype.card S.DCoins : ℝ≥0∞)⁻¹) *
            ∑ _d : Fin m → S.DCoins, 1) := by
          gcongr with d
          exact prTrue_Q_le_one _ _
      _ = S.preMassAt pk := by rw [Finset.mul_sum]; simp only [mul_one, hmD]
  unfold domAllGameAt
  calc ∑ r : Msg × Fin T → Salt, (∏ _y : Msg × Fin T, (Fintype.card Salt : ℝ≥0∞)⁻¹) *
        ∑ d : Fin m → S.DCoins, (∏ _x : Fin m, (Fintype.card S.DCoins : ℝ≥0∞)⁻¹) *
          S.allWin eX eY eQ eA A pk (S.domAllOracle eY pk d) (S.domTab eX pk r d)
      ≤ ∑ r : Msg × Fin T → Salt, (∏ _y : Msg × Fin T, (Fintype.card Salt : ℝ≥0∞)⁻¹) *
          (S.preMassAt pk + ∑ d : Fin m → S.DCoins,
            (∏ _x : Fin m, (Fintype.card S.DCoins : ℝ≥0∞)⁻¹) *
              prOut0 ((S.B_collQ eX eY eQ eA A pk (r, d)).withFinalB fun j =>
                S.collGame.win pk (collOut A j))) := by
        gcongr with r
        have hsplit : ∀ d : Fin m → S.DCoins,
            S.allWin eX eY eQ eA A pk (S.domAllOracle eY pk d) (S.domTab eX pk r d) =
              prOutMRGen (recordGen (A.run pk) fun i =>
                forgeTest S.toQROMSig eY eQ A pk i
                    (S.domAllOracle eY pk d (forgePoint S.toQROMSig eX A pk i)) &&
                  decide ((A.forge i).2.2 =
                    S.sampleDom pk (d (forgePoint S.toQROMSig eX A pk i))))
                (S.domAllOracle eY pk d)
                (simTab eQ eA (hashOf eX eY (S.domAllOracle eY pk d)) (S.domTab eX pk r d)) +
              prOutMRGen (recordGen (A.run pk) fun i =>
                forgeTest S.toQROMSig eY eQ A pk i
                    (S.domAllOracle eY pk d (forgePoint S.toQROMSig eX A pk i)) &&
                  !decide ((A.forge i).2.2 =
                    S.sampleDom pk (d (forgePoint S.toQROMSig eX A pk i))))
                (S.domAllOracle eY pk d)
                (simTab eQ eA (hashOf eX eY (S.domAllOracle eY pk d)) (S.domTab eX pk r d)) :=
          fun d => prOutMRGen_recordGen_add _ _ _ _ _
        simp only [hsplit, mul_add, Finset.sum_add_distrib]
        refine add_le_add (heq r) (Finset.sum_le_sum fun d _ => ?_)
        gcongr
        exact S.prOutMRGen_ne_le_coll hshort eX eY eQ eA A pk r d
    _ = _ := by
        simp only [mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hmS, one_mul]

omit [Fintype Sig] [Fintype Tgt] [DecidableEq Salt] [Fintype Msg] [DecidableEq Msg]
  [Fintype Salt] [Nonempty Salt] [Nonempty Sig] in
/-- The expectation over the instances of the collision game: a public key of the key
    distribution. -/
theorem sdExp_collGame_gen [Fintype PK] [Fintype SK] (φ : PK → ℝ≥0∞) :
    sdExp S.collGame.gen φ = ∑ ks, S.keygen ks * φ ks.1 := by
  classical
  unfold collGame
  simp only [sdExp, PMF.map_apply, tsum_fintype, Finset.sum_mul, ite_mul, zero_mul,
    Option.some.injEq]
  rw [Finset.sum_comm]
  simp

omit [Fintype Sig] [DecidableEq Sig] [Fintype Tgt] [DecidableEq Tgt] [DecidableEq Salt]
  [Nonempty Salt] [NeZero m] [Nonempty Sig] in
/-- The weights of the salts and the domain coins are the uniform weight of the coins of the
    collision reduction. -/
theorem sum_collCoins_eq (G : (Msg × Fin T → Salt) × (Fin m → S.DCoins) → ℝ≥0∞) :
    ∑ r : Msg × Fin T → Salt, (∏ _y : Msg × Fin T, (Fintype.card Salt : ℝ≥0∞)⁻¹) *
        ∑ d : Fin m → S.DCoins, (∏ _x : Fin m, (Fintype.card S.DCoins : ℝ≥0∞)⁻¹) * G (r, d) =
      ∑ i : (Msg × Fin T → Salt) × (Fin m → S.DCoins),
        (Fintype.card ((Msg × Fin T → Salt) × (Fin m → S.DCoins)) : ℝ≥0∞)⁻¹ * G i := by
  have ht : ∀ k : ℕ, (k : ℝ≥0∞) ≠ ⊤ := fun k => ENNReal.natCast_ne_top k
  have hR : ∏ _y : Msg × Fin T, (Fintype.card Salt : ℝ≥0∞)⁻¹ =
      (Fintype.card (Msg × Fin T → Salt) : ℝ≥0∞)⁻¹ := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fun, Nat.cast_pow, ENNReal.inv_pow]
  have hD : ∏ _x : Fin m, (Fintype.card S.DCoins : ℝ≥0∞)⁻¹ =
      (Fintype.card (Fin m → S.DCoins) : ℝ≥0∞)⁻¹ := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin, Nat.cast_pow,
      ENNReal.inv_pow]
  rw [hR, hD, Fintype.card_prod, Nat.cast_mul, ENNReal.mul_inv (Or.inr (ht _)) (Or.inl (ht _)),
    Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun d _ => by ring

variable [Fintype PK] [Fintype SK]

omit [Fintype Tgt] [NeZero m] in
/-- Route II averaged over the keys: the game with domain samples at every point is at most
    `preMass` plus the collision advantage of `B_collQ`. -/
theorem domAllGame_le_coll [Finite Tgt] (hshort : ∀ pk d, S.short pk (S.sampleDom pk d) = true)
    (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c)
    (eA : Option (Salt × Sig) ≃ Fin a) (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig)) :
    S.domAllGame eX eY eQ eA A ≤
      S.preMass + qSearchAdv S.collGame (S.B_collQ eX eY eQ eA A) (collOut A) := by
  unfold domAllGame preMass qSearchAdv
  rw [S.sdExp_collGame_gen, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun ks _ => ?_
  rw [← mul_add]
  gcongr
  refine (S.domAllGameAt_le_coll hshort eX eY eQ eA A ks.1).trans (le_of_eq ?_)
  congr 1
  exact S.sum_collCoins_eq fun i => prOut0 ((S.B_collQ eX eY eQ eA A ks.1 i).withFinalB
    fun j => S.collGame.win ks.1 (collOut A j))

/-- Route II: the EUF-CMA advantage of salted hash-and-sign is at most the collision advantage
    of `B_collQ` plus `preMass`, `k · (condDist + (T - 1) / card Salt)` (hop A) and
    `4 (flatQ q k q + 2 (k + 1)) domDist^(1/2)` (hop B at every point), when domain samples are
    short. `B_collQ` samples the salts and the domain coins itself, programs the oracle at every
    point with the images of the domain samples and answers each signing entry with the sample
    at its salted point; it uses no secret key. -/
theorem saltedPSF_qeufcma_le_coll (hshort : ∀ pk d, S.short pk (S.sampleDom pk d) = true)
    (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c)
    (eA : Option (Salt × Sig) ≃ Fin a) (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig)) :
    qEUFCMAAdvantage S.toQROMSig eX eY eQ eA A ≤
      qSearchAdv S.collGame (S.B_collQ eX eY eQ eA A) (collOut A) + S.preMass +
        k * (S.condDist + ((T - 1 : ℕ) : ℝ≥0∞) * (Fintype.card Salt : ℝ≥0∞)⁻¹) +
        4 * ((flatQ q k q + 2 * (k + 1) : ℕ) : ℝ≥0∞) * S.domDist ^ (1 / 2 : ℝ) := by
  have h1 := tsub_le_iff_left.mp ((le_sup_left).trans (S.saltedPSF_hopCond eX eY eQ eA A))
  have h2 := tsub_le_iff_left.mp ((le_sup_left).trans (S.saltedPSF_hopAll eX eY eQ eA A))
  have h3 := S.domAllGame_le_coll hshort eX eY eQ eA A
  rw [← S.allGame_eq_domAllGame] at h3
  calc qEUFCMAAdvantage S.toQROMSig eX eY eQ eA A
      ≤ S.condGame eX eY eQ eA A +
          k * (S.condDist + ((T - 1 : ℕ) : ℝ≥0∞) * (Fintype.card Salt : ℝ≥0∞)⁻¹) := h1
    _ ≤ (S.allGame eX eY eQ eA A +
          4 * ((flatQ q k q + 2 * (k + 1) : ℕ) : ℝ≥0∞) * S.domDist ^ (1 / 2 : ℝ)) +
          k * (S.condDist + ((T - 1 : ℕ) : ℝ≥0∞) * (Fintype.card Salt : ℝ≥0∞)⁻¹) := by
        gcongr
    _ ≤ ((S.preMass + qSearchAdv S.collGame (S.B_collQ eX eY eQ eA A) (collOut A)) +
          4 * ((flatQ q k q + 2 * (k + 1) : ℕ) : ℝ≥0∞) * S.domDist ^ (1 / 2 : ℝ)) +
          k * (S.condDist + ((T - 1 : ℕ) : ℝ≥0∞) * (Fintype.card Salt : ℝ≥0∞)⁻¹) := by
        gcongr
    _ = _ := by ring

end TerminalColl

end SaltedPSF

end CatCrypt.Quantum.QROM
