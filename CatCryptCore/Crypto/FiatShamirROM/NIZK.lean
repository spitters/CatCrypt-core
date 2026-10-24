/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.FiatShamirROM.Timed
public import CatCryptCore.Crypto.FiatShamirROM.LinearRelation

/-!
# The strong Fiat–Shamir transform of a Σ-protocol in the random-oracle model

The non-interactive proof system obtained from a Σ-protocol `P` by the strong
Fiat–Shamir transform: the challenge for the commitment `a` on the statement `x` in
the session `sid` is the random-oracle value `H(sid, x, a)`, with the oracle input
in the order of draft-irtf-cfrg-fiat-shamir-03 (session identifier, instance, prover
message). A proof is a transcript `(a, z)`; it verifies for `(sid, x)` when
`(a, H(sid, x, a), z)` is an accepting transcript.

**Knowledge soundness.** An adversary is an oracle adversary with at most `qH`
random-oracle queries that outputs a session identifier, a statement of its choice
and a proof. The challenger then queries the oracle at the input of the proof, and
the adversary succeeds when the proof verifies. The extractor `ksExtractor A` runs
this experiment as a forking run (`OracleForking.forkRun`): at every fresh oracle
value it continues the run, and when the final proof verifies against that value it
runs the rest again from the same oracle state with a fresh value. Both proofs are
then at the same oracle input, so for the same statement and commitment, and the
extractor applies the special-soundness extractor to the two transcripts.

**Zero knowledge.** A distinguisher queries the random oracle and a proving oracle on
a session identifier and a statement–witness pair in the relation. In the real game
the proving oracle runs the honest prover against the random oracle; in the simulated
game it answers from the session identifier and the statement only, by the HVZK
simulator, and programs the oracle at the simulated input. The proving oracle is the
signing oracle of the protocol `Sigma.nizkProtocol P Sid` with the oracle input
`(sid, x, a)` and the statement and witness carried by the query, so the
signing-oracle simulation of `FiatShamirROM.StatHVZK` applies.

## Main definitions

* `Sigma.NizkInput`, `Sigma.NizkProof`, `Sigma.nizkProve`, `Sigma.nizkVerify` — the
  strong Fiat–Shamir proof system for an oracle `H`
* `ksStep`, `KSAdversary`, `ksWithVerify`, `ksAccepts`, `ksAdvantage` — the
  knowledge-soundness experiment
* `ksHitAt`, `ksExtractW`, `ksForkGame`, `ksExtractor`, `ksExtractProb` — the forking
  extractor and its success probability
* `ksExtractor.timed` — the costed extractor
* `Sigma.ProveQuery`, `Sigma.nizkSimulate`, `Sigma.nizkProtocol` — proving queries,
  the simulated proving answer, and the protocol of the proving oracle
* `ZKDistinguisher`, `zkReal`, `zkSim` — the zero-knowledge games

## Main results

* `ksExtractProb_ge` — for a special-sound Σ-protocol and every adversary with at most
  `qH` oracle queries, with `ε = ksAdvantage A`,
  `ε·(ε/(qH + 1) − 1/|Ch|) ≤ ksExtractProb A`
* `ksExtractor.run_erase_timed`, `ksExtractor.timeBound_timed` — the costed extractor
  has the distribution of `ksExtractor A` and time at most
  `2 * (T + 1 + (tH + tF + 1) * (qH + 1)) + tExt`
* `Sigma.statHVZKAt_nizkProtocol`, `Sigma.keyBoundAt_nizkProtocol` — statistical HVZK
  and the commitment bound at every pair of the relation give those of the protocol of
  the proving oracle
* `zkReal_le_zkSim`, `zkSim_le_zkReal` — for statistical HVZK distance `δ` and
  commitment bound `γ` at every pair of the relation, and every distinguisher with at
  most `qH` oracle and `qP` proving queries, the probabilities of output `true` in the
  two games differ by at most `qP·δ + qP·(qH + qP)·γ`
* `linearSigma_ksExtractProb_ge`, `linearSigma_zkReal_le_zkSim`,
  `linearSigma_zkSim_le_zkReal` — the instances for the Σ-protocol of a linear
  relation, with the distance `qP·(qH + qP)·γ`

## References

* A. Fiat, A. Shamir, *How to prove yourself*, CRYPTO 1986.
* D. Bernhard, O. Pereira, B. Warinschi, *How not to prove yourself: pitfalls of the
  Fiat-Shamir heuristic and applications to Helios*, ASIACRYPT 2012.
* M. Bellare, G. Neven, *Multi-signatures in the plain public-key model and a general
  forking lemma*, CCS 2006.
* M. Orrù, *Fiat-Shamir transformation*, draft-irtf-cfrg-fiat-shamir-03.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.FiatShamirROM

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.OracleForking
open scoped ENNReal

/-! ## The proof system -/

namespace Sigma

variable (P : Sigma) (Sid : Type)

/-- The input of the random oracle of the strong Fiat–Shamir transform: the session
identifier, the statement and the commitment. -/
abbrev NizkInput := Sid × P.Stmt × P.Com

/-- A proof of the strong Fiat–Shamir transform: a commitment and a response. -/
abbrev NizkProof := P.Com × P.Resp

variable {P Sid}

/-- The honest prover against the oracle `H` on the statement `x` with witness `w` in
the session `sid` from the randomness `r`: the commitment `a`, the challenge
`H(sid, x, a)` and its response, or nothing when the response is rejected. -/
def nizkProve (H : P.NizkInput Sid → P.Ch) (sid : Sid) (x : P.Stmt) (w : P.Wit)
    (r : P.Rand) : Option P.NizkProof :=
  if P.accept (P.respond x w r (H (sid, x, P.commit x w r))) then
    some (P.commit x w r, P.respond x w r (H (sid, x, P.commit x w r)))
  else none

/-- The verifier against the oracle `H`: the proof `(a, z)` for `x` in the session
`sid` verifies when `(a, H(sid, x, a), z)` is an accepting transcript. -/
def nizkVerify (H : P.NizkInput Sid → P.Ch) (sid : Sid) (x : P.Stmt) (π : P.NizkProof) :
    Bool :=
  P.verify x π.1 (H (sid, x, π.1)) π.2

end Sigma

/-! ## Knowledge soundness -/

section Knowledge

variable {P : Sigma} {Sid : Type} [DecidableEq Sid] [DecidableEq P.Stmt]

/-- The random oracle of the knowledge-soundness experiment on its list of entries: the
recorded value of a point, or a fresh uniform value appended to the list. -/
noncomputable def ksStep (l : List (P.NizkInput Sid × P.Ch)) (k : P.NizkInput Sid) :
    Step P.Ch (List (P.NizkInput Sid × P.Ch)) P.Ch :=
  match lookupIn l k with
  | some e => .plain (PMF.pure (e, l))
  | none => .fresh fun e => (e, l ++ [(k, e)])

variable (P Sid) in
/-- A knowledge-soundness adversary: an oracle adversary with at most `qH` random-oracle
queries on every path that outputs a session identifier, a statement and a proof. -/
structure KSAdversary (qH : ℕ) : Type 1 where
  /-- The adversary. -/
  run : OracleAdv (P.NizkInput Sid) P.Ch (Sid × P.Stmt × P.NizkProof)
  /-- The query bound. -/
  isQueryBound : run.IsQueryBound qH

/-- The oracle input of an output `(sid, x, (a, z))`: `(sid, x, a)`. -/
def ksInput (y : Sid × P.Stmt × P.NizkProof) : P.NizkInput Sid := (y.1, y.2.1, y.2.2.1)

/-- The adversary followed by the challenger's query at the oracle input of its
output. -/
def ksWithVerify (A : OracleAdv (P.NizkInput Sid) P.Ch (Sid × P.Stmt × P.NizkProof)) :
    OracleAdv (P.NizkInput Sid) P.Ch (Sid × P.Stmt × P.NizkProof) :=
  A.bind fun y => .query (ksInput y) fun _ => .ret y

/-- The output proof verifies against the value recorded at its oracle input. -/
def ksAccepts (y : (Sid × P.Stmt × P.NizkProof) × List (P.NizkInput Sid × P.Ch)) : Bool :=
  match lookupIn y.2 (ksInput y.1) with
  | some e => P.verify y.1.2.1 y.1.2.2.1 e y.1.2.2.2
  | none => false

/-- The probability that the adversary outputs a verifying proof. -/
noncomputable def ksAdvantage {qH : ℕ} (A : KSAdversary P Sid qH) : ℝ≥0∞ :=
  (OracleAdv.run (toOracle ksStep) (ksWithVerify A.run) []).toOuterMeasure
    {y | ksAccepts y = true}

/-- The oracle input of the output first occurs at position `c` of the list, and the
proof verifies against the value recorded there. -/
def ksHitAt (c : ℕ) (y : (Sid × P.Stmt × P.NizkProof) × List (P.NizkInput Sid × P.Ch)) :
    Bool :=
  decide (findKey y.2 (ksInput y.1) = some c) &&
    match y.2[c]? with
    | some p => P.verify y.1.2.1 y.1.2.2.1 p.2 y.1.2.2.2
    | none => false

/-- The statement of the first output of a forked pair with the witness computed by the
special-soundness extractor, and the default witness when there is no second run. -/
def ksExtractW (r : ((Sid × P.Stmt × P.NizkProof) × List (P.NizkInput Sid × P.Ch)) ×
    Option (((Sid × P.Stmt × P.NizkProof) × List (P.NizkInput Sid × P.Ch)) × P.Ch × P.Ch)) :
    P.Stmt × P.Wit :=
  (r.1.1.2.1, match r.2 with
    | some (y₂, e₁, e₂) => P.extract r.1.1.2.1 r.1.1.2.2.1 e₁ r.1.1.2.2.2 e₂ y₂.1.2.2.2
    | none => default)

/-- The forking run of the knowledge-soundness experiment. -/
noncomputable def ksForkGame {qH : ℕ} (A : KSAdversary P Sid qH) :
    PMF (((Sid × P.Stmt × P.NizkProof) × List (P.NizkInput Sid × P.Ch)) ×
      Option (((Sid × P.Stmt × P.NizkProof) × List (P.NizkInput Sid × P.Ch)) × P.Ch × P.Ch)) :=
  forkRun ksStep List.length ksHitAt (ksWithVerify A.run) []

/-- **The forking extractor.** Run the knowledge-soundness experiment as a forking run
and output the statement of the first run with the witness extracted from the two
transcripts at the fork point. -/
noncomputable def ksExtractor {qH : ℕ} (A : KSAdversary P Sid qH) : PMF (P.Stmt × P.Wit) :=
  (ksForkGame A).map ksExtractW

/-- The probability that the extractor outputs a statement with a witness for it. -/
noncomputable def ksExtractProb {qH : ℕ} (A : KSAdversary P Sid qH) : ℝ≥0∞ :=
  (ksExtractor A).toOuterMeasure {xw | P.rel xw.1 xw.2}

/-! ### Transitions -/

theorem ksStep_plain (l : List (P.NizkInput Sid × P.Ch)) (k : P.NizkInput Sid)
    (p : PMF (P.Ch × List (P.NizkInput Sid × P.Ch))) (h : ksStep l k = .plain p)
    (x : P.Ch × List (P.NizkInput Sid × P.Ch)) (hx : x ∈ p.support) :
    x.2.length = l.length := by
  simp only [ksStep] at h
  cases hl : lookupIn l k with
  | some e =>
    rw [hl] at h
    cases h
    rw [PMF.support_pure, Set.mem_singleton_iff] at hx
    subst hx
    rfl
  | none =>
    rw [hl] at h
    cases h

theorem ksStep_fresh (l : List (P.NizkInput Sid × P.Ch)) (k : P.NizkInput Sid)
    (f : P.Ch → P.Ch × List (P.NizkInput Sid × P.Ch)) (h : ksStep l k = .fresh f) (e : P.Ch) :
    (f e).2 = l ++ [(k, e)] := by
  simp only [ksStep] at h
  cases hl : lookupIn l k with
  | some e' =>
    rw [hl] at h
    cases h
  | none =>
    rw [hl] at h
    cases h
    rfl

theorem ksStep_length_fresh (l : List (P.NizkInput Sid × P.Ch)) (k : P.NizkInput Sid)
    (f : P.Ch → P.Ch × List (P.NizkInput Sid × P.Ch)) (h : ksStep l k = .fresh f) (e : P.Ch) :
    (f e).2.length = l.length + 1 := by
  rw [ksStep_fresh l k f h e, List.length_append, List.length_singleton]

/-- Every oracle transition extends the list by at most one entry. -/
theorem ksStep_support (l : List (P.NizkInput Sid × P.Ch)) (k : P.NizkInput Sid)
    (x : P.Ch × List (P.NizkInput Sid × P.Ch)) (hx : x ∈ (toOracle ksStep l k).support) :
    l <+: x.2 ∧ x.2.length ≤ l.length + 1 := by
  simp only [toOracle, ksStep] at hx
  cases hl : lookupIn l k with
  | some e =>
    simp only [hl, Step.toPMF, PMF.support_pure, Set.mem_singleton_iff] at hx
    subst hx
    exact ⟨List.prefix_refl _, by simp⟩
  | none =>
    simp only [hl, Step.toPMF, PMF.support_map, Set.mem_image] at hx
    obtain ⟨e, _, rfl⟩ := hx
    exact ⟨List.prefix_append _ _, by simp⟩

/-- Along a run with at most `h` queries the list is extended by at most `h` entries. -/
theorem ksRun_support {α : Type} (A : OracleAdv (P.NizkInput Sid) P.Ch α) (h : ℕ)
    (hA : A.IsQueryBound h) (l : List (P.NizkInput Sid × P.Ch))
    (y : α × List (P.NizkInput Sid × P.Ch))
    (hy : y ∈ (OracleAdv.run (toOracle ksStep) A l).support) :
    l <+: y.2 ∧ y.2.length ≤ l.length + h := by
  induction A generalizing h l with
  | ret a =>
    rw [OracleAdv.run_ret, PMF.support_pure, Set.mem_singleton_iff] at hy
    subst hy
    exact ⟨List.prefix_refl _, Nat.le_add_right _ _⟩
  | rand p k ih =>
    rw [OracleAdv.run_rand, PMF.mem_support_bind_iff] at hy
    obtain ⟨b, _, hb⟩ := hy
    exact ih b h (hA b) l hb
  | query d k ih =>
    rw [OracleAdv.run_query, PMF.mem_support_bind_iff] at hy
    obtain ⟨x, hx, hy⟩ := hy
    cases h with
    | zero => exact hA.elim
    | succ h =>
      obtain ⟨hp, hlen⟩ := ksStep_support l d x hx
      obtain ⟨hp', hlen'⟩ := ih x.1 h (hA x.1) x.2 hy
      exact ⟨hp.trans hp', by omega⟩

omit [DecidableEq Sid] [DecidableEq P.Stmt] in
theorem isQueryBound_ksWithVerify (A : OracleAdv (P.NizkInput Sid) P.Ch
    (Sid × P.Stmt × P.NizkProof)) {qH : ℕ} (hA : A.IsQueryBound qH) :
    (ksWithVerify A).IsQueryBound (qH + 1) :=
  OracleAdv.isQueryBound_bind hA fun _ _ => trivial

/-! ### Hits -/

theorem ksHitAt_lt (c : ℕ) (y : (Sid × P.Stmt × P.NizkProof) × List (P.NizkInput Sid × P.Ch))
    (h : ksHitAt c y = true) : c < y.2.length := by
  simp only [ksHitAt, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨hi, _, _⟩ := List.findIdx?_eq_some_iff_getElem.mp h.1
  exact hi

theorem ksHitAt_disj (c c' : ℕ)
    (y : (Sid × P.Stmt × P.NizkProof) × List (P.NizkInput Sid × P.Ch))
    (h : ksHitAt c y = true) (h' : ksHitAt c' y = true) : c = c' := by
  simp only [ksHitAt, Bool.and_eq_true, decide_eq_true_eq] at h h'
  exact Option.some_injective _ (h.1.symm.trans h'.1)

/-- The output proof verifies exactly when it hits some position of the list. -/
theorem ksAccepts_iff_exists_ksHitAt
    (y : (Sid × P.Stmt × P.NizkProof) × List (P.NizkInput Sid × P.Ch)) :
    ksAccepts y = true ↔ ∃ c, ksHitAt c y = true := by
  obtain ⟨o, l⟩ := y
  unfold ksAccepts ksHitAt lookupIn
  dsimp only
  cases hf : findKey l (ksInput o) with
  | none => simp
  | some i =>
    simp only [Option.bind_some, Option.some.injEq, decide_eq_true_eq, Bool.and_eq_true,
      exists_eq_left']
    cases hg : l[i]? <;> simp

/-- An output that hits the position of an entry `(k, e)` of an extended list has the
oracle input `k` and verifies against `e`. -/
theorem ksHitAt_prefix (l : List (P.NizkInput Sid × P.Ch)) (k : P.NizkInput Sid) (e : P.Ch)
    (y : (Sid × P.Stmt × P.NizkProof) × List (P.NizkInput Sid × P.Ch))
    (hp : l ++ [(k, e)] <+: y.2) (hy : ksHitAt l.length y = true) :
    ksInput y.1 = k ∧ P.verify y.1.2.1 y.1.2.2.1 e y.1.2.2.2 = true := by
  have hget : y.2[l.length]? = some (k, e) := by
    have := List.prefix_iff_getElem?.mp hp l.length (by simp)
    simpa using this
  simp only [ksHitAt, Bool.and_eq_true, decide_eq_true_eq, hget] at hy
  obtain ⟨hfk, hv⟩ := hy
  refine ⟨?_, hv⟩
  unfold findKey at hfk
  obtain ⟨hi, hpk, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hfk
  simp only [decide_eq_true_eq] at hpk
  have hk : y.2[l.length] = (k, e) := (List.getElem?_eq_some_iff.mp hget).2
  rw [hk] at hpk
  exact hpk.symm

/-! ### The bound -/

/-- On a successful fork at any index, the extractor outputs a statement with a witness
for it. -/
theorem rel_ksExtractW_of_forkSucc (hSS : P.SpecialSound) {qH : ℕ} (A : KSAdversary P Sid qH)
    (r : ((Sid × P.Stmt × P.NizkProof) × List (P.NizkInput Sid × P.Ch)) ×
      Option (((Sid × P.Stmt × P.NizkProof) × List (P.NizkInput Sid × P.Ch)) × P.Ch × P.Ch))
    (hr : r ∈ (ksForkGame A).support) (c : ℕ) (hc : forkSucc ksHitAt c r = true) :
    P.rel (ksExtractW r).1 (ksExtractW r).2 := by
  rcases h2 : r.2 with _ | ⟨y₂, e₁, e₂⟩
  · simp [forkSucc, h2] at hc
  · simp only [forkSucc, h2, Bool.and_eq_true, decide_eq_true_eq] at hc
    obtain ⟨⟨h₁, h₂⟩, hne⟩ := hc
    obtain ⟨s₀, d₀, f, hf, hh, hp₁, hp₂⟩ :=
      exists_fresh_of_mem_support_forkRun ksStep List.length ksHitAt
        (fun s t => s <+: t) (fun _ => List.prefix_refl _)
        (fun _ _ _ h h' => h.trans h') (fun s d y hy => (ksStep_support s d y hy).1)
        _ _ r y₂ e₁ e₂ hr h2
    have hc0 : c = s₀.length := ksHitAt_disj _ _ _ h₁ hh
    rw [ksStep_fresh s₀ d₀ f hf e₁] at hp₁
    rw [ksStep_fresh s₀ d₀ f hf e₂] at hp₂
    subst hc0
    obtain ⟨hk₁, hv₁⟩ := ksHitAt_prefix s₀ d₀ e₁ r.1 hp₁ h₁
    obtain ⟨hk₂, hv₂⟩ := ksHitAt_prefix s₀ d₀ e₂ y₂ hp₂ h₂
    have hk := hk₂.trans hk₁.symm
    simp only [ksInput, Prod.mk.injEq] at hk
    obtain ⟨_, hx, ha⟩ := hk
    rw [hx, ha] at hv₂
    simp only [ksExtractW, h2]
    exact hSS _ _ e₁ _ e₂ _ hv₁ hv₂ hne

/-- **Forking bound.** The probability `ε` that the adversary outputs a verifying proof
satisfies `ε²/(qH + 1) − ε/|Ch| ≤ ksExtractProb A`. -/
theorem ksAdvantage_sq_div_sub_le (hSS : P.SpecialSound) {qH : ℕ} (A : KSAdversary P Sid qH) :
    ksAdvantage A ^ 2 / ((qH + 1 : ℕ) : ℝ≥0∞) - ksAdvantage A / Fintype.card P.Ch ≤
      ksExtractProb A := by
  have hB := isQueryBound_ksWithVerify A.run A.isQueryBound
  have hsum : ∑ c : Fin (qH + 1), accProb ksStep ksHitAt c (ksWithVerify A.run) [] =
      ksAdvantage A := by
    refine sum_fin_toOuterMeasure_eq _ _ ksHitAt ksAccepts ksHitAt_disj fun y hy => ?_
    obtain ⟨_, hlen⟩ := ksRun_support _ _ hB _ y hy
    rw [ksAccepts_iff_exists_ksHitAt]
    constructor
    · rintro ⟨c, hc⟩
      have hlt := ksHitAt_lt c y hc
      simp only [List.length_nil, zero_add] at hlen
      exact ⟨⟨c, by omega⟩, hc⟩
    · rintro ⟨c, hc⟩
      exact ⟨c, hc⟩
  have hBN := sum_accProb_sq_div_sub_le ksStep List.length ksHitAt ksStep_plain
    ksStep_length_fresh ksHitAt_lt ksHitAt_disj (qH + 1) (Nat.succ_pos _) (ksWithVerify A.run)
    [] rfl
  rw [hsum] at hBN
  refine hBN.trans ((sum_forkProb_le ksStep List.length ksHitAt ksHitAt_disj (qH + 1) _ _
    (fun r => P.rel (ksExtractW r).1 (ksExtractW r).2)
    fun r hr c hc => rel_ksExtractW_of_forkSucc hSS A r hr c hc).trans (le_of_eq ?_))
  unfold ksExtractProb ksExtractor ksForkGame
  rw [PMF.toOuterMeasure_map_apply]
  rfl

/-- **Knowledge soundness of the strong Fiat–Shamir transform in the random-oracle
model.** For a special-sound Σ-protocol `P` and every adversary `A` with at most `qH`
random-oracle queries that chooses its statement, session identifier and proof, with
`ε = ksAdvantage A` the probability that the proof verifies,

`ε·(ε/(qH + 1) − 1/|Ch|) ≤ ksExtractProb A`,

where the forking extractor `ksExtractor A` runs `A` at most twice and calls the
special-soundness extractor once, and outputs the statement of `A` with a witness. -/
theorem ksExtractProb_ge (hSS : P.SpecialSound) {qH : ℕ} (A : KSAdversary P Sid qH) :
    ksAdvantage A * (ksAdvantage A / ((qH + 1 : ℕ) : ℝ≥0∞) - 1 / Fintype.card P.Ch) ≤
      ksExtractProb A := by
  have hε1 : ksAdvantage A ≤ 1 := toOuterMeasure_le_one _ _
  exact (mul_div_tsub_le_sq_div_tsub le_rfl (ne_top_of_le_ne_top ENNReal.one_ne_top hε1)).trans
    (ksAdvantage_sq_div_sub_le hSS A)

/-! ### The costed extractor -/

/-- The costed adversary followed by the challenger's query. -/
def ksWithVerify.timed
    (A' : OracleAdv.Timed (P.NizkInput Sid) P.Ch (Sid × P.Stmt × P.NizkProof)) :
    ℕ × OracleAdv.Timed (P.NizkInput Sid) P.Ch (Sid × P.Stmt × P.NizkProof) :=
  A'.bind fun y => (0, .query (ksInput y) (fun _ => 0) fun _ => .ret y)

omit [DecidableEq Sid] [DecidableEq P.Stmt] in
theorem ksWithVerify.erase_timed
    (A' : OracleAdv.Timed (P.NizkInput Sid) P.Ch (Sid × P.Stmt × P.NizkProof)) :
    (ksWithVerify.timed A').2.erase = ksWithVerify A'.erase := by
  rw [ksWithVerify.timed, OracleAdv.Timed.erase_bind]
  rfl

omit [DecidableEq Sid] [DecidableEq P.Stmt] in
theorem ksWithVerify.timeBound_timed
    {A' : OracleAdv.Timed (P.NizkInput Sid) P.Ch (Sid × P.Stmt × P.NizkProof)} {T : ℕ}
    (hT : A'.TimeBound T) : OracleAdv.Timed.StepTimeBound (ksWithVerify.timed A') (T + 1) :=
  OracleAdv.Timed.timeBound_bind hT fun _ =>
    ⟨Nat.zero_le _, le_rfl, fun _ => ⟨Nat.zero_le _, trivial⟩⟩

/-- The costed forking extractor: the costed adversary `A'` with the challenger's query,
run as the costed forking run (`OracleForking.forkRun.timedK`) against the random
oracle with step cost `tH` and fork decision cost `tF`, followed by the special-soundness
extractor at cost `tExt`. -/
noncomputable def ksExtractor.timed (tH tF tExt : ℕ)
    (A' : OracleAdv.Timed (P.NizkInput Sid) P.Ch (Sid × P.Stmt × P.NizkProof)) :
    ℕ × OracleAdv.Timed Empty Empty (P.Stmt × P.Wit) :=
  OracleAdv.Timed.delay (ksWithVerify.timed A').1
    (forkRun.timedK ksStep List.length ksHitAt (fun _ => tH) tF (ksWithVerify.timed A').2 []
      fun r => (tExt, .ret (ksExtractW r)))

/-- Under any oracle, the costed extractor has the output distribution of
`ksExtractor A`. -/
theorem ksExtractor.run_erase_timed {qH : ℕ} (A : KSAdversary P Sid qH)
    (A' : OracleAdv.Timed (P.NizkInput Sid) P.Ch (Sid × P.Stmt × P.NizkProof))
    (hA : A'.erase = A.run) (tH tF tExt : ℕ) {U : Type} (O' : U → Empty → PMF (Empty × U))
    (u : U) :
    (OracleAdv.run O' (ksExtractor.timed tH tF tExt A').2.erase u).map Prod.fst =
      ksExtractor A := by
  rw [ksExtractor.timed, OracleAdv.Timed.delay,
    forkRun.run_erase_timedK _ _ _ _ _ ksStep_plain ksStep_length_fresh ksHitAt_disj,
    ksWithVerify.erase_timed, hA]
  simp only [OracleAdv.Timed.erase, OracleAdv.run_ret, PMF.pure_map]
  rfl

/-- **Time of the forking extractor.** With `A'` of time `T` and at most `qH` queries, the
costed extractor has time at most `2 * (T + 1 + (tH + tF + 1) * (qH + 1)) + tExt`: the
adversary with the challenger's query is run at most twice, each query is charged its
step, its node and the fork decision, and the special-soundness extractor is called
once. -/
theorem ksExtractor.timeBound_timed {qH : ℕ} (A : KSAdversary P Sid qH)
    {A' : OracleAdv.Timed (P.NizkInput Sid) P.Ch (Sid × P.Stmt × P.NizkProof)}
    (hA : A'.erase = A.run) (tH tF tExt : ℕ) {T : ℕ} (hT : A'.TimeBound T) :
    OracleAdv.Timed.StepTimeBound (ksExtractor.timed tH tF tExt A')
      (2 * (T + 1 + (tH + tF + 1) * (qH + 1)) + tExt) := by
  have hw := ksWithVerify.timeBound_timed hT
  have hq : (ksWithVerify.timed A').2.erase.IsQueryBoundBy (fun _ => tH + tF + 1)
      ((tH + tF + 1) * (qH + 1)) := by
    rw [ksWithVerify.erase_timed, hA]
    exact ((isQueryBound_ksWithVerify A.run A.isQueryBound).isQueryBoundBy_one.mul_left
      (tH + tF + 1)).of_cost_le fun _ => by simp
  have hr := forkRun.timeBound_timedK ksStep List.length ksHitAt (fun _ => tH) tF
    (fun _ => tH + tF + 1) (fun _ => by omega) (fun _ _ _ _ => by omega) _ _ hw.2 hq le_rfl []
    (fun r => (tExt, .ret (ksExtractW r))) tExt fun _ => ⟨by omega, trivial⟩
  exact (OracleAdv.Timed.stepTimeBound_delay (c := (ksWithVerify.timed A').1) hr).mono
    (by have := hw.1; omega)

end Knowledge

/-! ## Zero knowledge -/

namespace Sigma

variable (P : Sigma) (Sid : Type)

/-- A proving query: a session identifier and a statement–witness pair in the
relation. -/
abbrev ProveQuery := Sid × {xw : P.Stmt × P.Wit // P.rel xw.1 xw.2}

variable {P Sid}

/-- The simulated proving answer in the session `sid` on the statement `x` for the
challenge `e` and simulator randomness `s`: the simulated transcript `(a, z)` and the
oracle entry `((sid, x, a), e)` to program when `z` is accepted, nothing otherwise. -/
def nizkSimulate (sid : Sid) (x : P.Stmt) (e : P.Ch) (s : P.SimRand) :
    List (P.NizkInput Sid × P.Ch) × Option P.NizkProof :=
  if P.accept (P.simulate x e s).2 then
    ([((sid, x, (P.simulate x e s).1), e)], some (P.simulate x e s))
  else ([], none)

variable (P Sid) [DecidableEq Sid] [DecidableEq P.Stmt]

/-- The protocol of the proving oracle of the strong Fiat–Shamir transform: no global
statement, the proving queries as messages, one entry at the oracle input
`(sid, x, P.commit x w r)` of the query `(sid, (x, w))`, public when the response is
accepted; the simulator reads the session identifier and the statement of the query
(`nizkSimulate`). -/
@[reducible] noncomputable def nizkProtocol : Protocol where
  Stmt := Unit
  Wit := Unit
  Msg := P.ProveQuery Sid
  Key := P.NizkInput Sid
  Ch := P.Ch
  Sig := P.NizkProof
  Rand := P.Rand
  SimRand := P.SimRand
  decMsg := Classical.decEq _
  gen := PMF.pure ((), ())
  μ := 1
  key _ _ q r _ _ := (q.1, q.2.1.1, P.commit q.2.1.1 q.2.1.2 r)
  key_causal _ _ _ _ _ _ _ _ := rfl
  key_inj _ _ _ _ _ i j _ := Subsingleton.elim i j
  pub _ _ q r v _ := P.accept (P.respond q.2.1.1 q.2.1.2 r (v 0))
  sign _ _ q r v :=
    if P.accept (P.respond q.2.1.1 q.2.1.2 r (v 0)) then
      some (P.commit q.2.1.1 q.2.1.2 r, P.respond q.2.1.1 q.2.1.2 r (v 0))
    else none
  simulate _ q v s := P.nizkSimulate q.1 q.2.1.1 (v 0) s
  V := 1
  vkey _ q σ _ := (q.1, q.2.1.1, σ.1)
  verify _ q σ vs := match vs with
    | [e] => P.verify q.2.1.1 σ.1 e σ.2
    | _ => false

variable {P Sid}

/-- The view of a transcript `(a, z)` on the query `q` with challenge `e`: the entry
`((sid, x, a), e)` and the proof `(a, z)` when `z` is accepted, nothing otherwise. -/
def nizkView (q : P.ProveQuery Sid) (e : P.Ch) (az : P.Com × P.Resp) :
    (P.nizkProtocol Sid).View :=
  if P.accept az.2 then ([((q.1, q.2.1.1, az.1), e)], some az) else ([], none)

theorem trace_nizkProtocol (q : P.ProveQuery Sid) (r : P.Rand) (e : Fin 1 → P.Ch) :
    (P.nizkProtocol Sid).trace () () q r e =
      ([], P.nizkView q (e 0) (P.commit q.2.1.1 q.2.1.2 r, P.respond q.2.1.1 q.2.1.2 r (e 0))) := by
  rw [Protocol.trace, Protocol.evEntries_of_ev_false (fun _ => rfl)]
  unfold Protocol.view Protocol.pubEntries Protocol.entries nizkView
  cases h : P.accept (P.respond q.2.1.1 q.2.1.2 r (e 0)) <;>
    simp [nizkProtocol, h, List.finRange_succ, Fin.fin_one_eq_zero]

theorem simTrace_nizkProtocol (look : P.NizkInput Sid → Option P.Ch) (q : P.ProveQuery Sid)
    (e : Fin 1 → P.Ch) (s : P.SimRand) :
    (P.nizkProtocol Sid).simTrace look () q e s =
      ([], P.nizkView q (e 0) (P.simulate q.2.1.1 (e 0) s)) := by
  rw [Protocol.simTrace_of_simKey_none (fun _ _ => rfl)]
  rfl

theorem vals_nizkProtocol (look : P.NizkInput Sid → Option P.Ch) (q : P.ProveQuery Sid)
    (r : P.Rand) (e : Fin 1 → P.Ch) : (P.nizkProtocol Sid).vals look () () q r e = e :=
  Protocol.vals_of_ev_false (G := P.nizkProtocol Sid) (fun _ => rfl) look () () q r e

theorem guessView_nizkProtocol (look : P.NizkInput Sid → Option P.Ch) (q : P.ProveQuery Sid)
    (r : P.Rand) (e : Fin 1 → P.Ch) (i : Fin 1) :
    (P.nizkProtocol Sid).guessView look () () q r e i = ([], [], none) := by
  unfold Protocol.guessView
  split
  · rfl
  · next h =>
    rw [vals_nizkProtocol, trace_nizkProtocol]
    rw [vals_nizkProtocol] at h
    have h' : P.accept (P.respond q.2.1.1 q.2.1.2 r (e 0)) = false := by
      simp only [nizkProtocol, Bool.or_eq_true, not_or, Bool.not_eq_true] at h
      exact h.1
    simp [nizkView, h']

/-- Statistical HVZK of `P` with distance `δ` at every pair of the relation gives
statistical HVZK of the protocol of the proving oracle. -/
theorem statHVZKAt_nizkProtocol {δ : ℝ≥0∞} (h : ∀ x w, P.rel x w → P.StatHVZKAt x w δ) :
    (P.nizkProtocol Sid).StatHVZKAt () () δ := by
  intro q look g hg
  simp only [vals_nizkProtocol, trace_nizkProtocol, simTrace_nizkProtocol]
  have hstep : ∀ e : Fin 1 → P.Ch, ∑' r, PMF.uniformFintype P.Rand r *
      (if (P.nizkProtocol Sid).hidFresh look () () q r e then
        g ([], P.nizkView q (e 0) (P.commit q.2.1.1 q.2.1.2 r, P.respond q.2.1.1 q.2.1.2 r (e 0)))
        else 0) ≤
      ∑' s, PMF.uniformFintype P.SimRand s *
        g ([], P.nizkView q (e 0) (P.simulate q.2.1.1 (e 0) s)) + δ := fun e => by
    have hb : P.RejectBlind (fun az => g ([], P.nizkView q (e 0) az)) := by
      intro a a' z hz
      simp [nizkView, hz]
    refine (ENNReal.tsum_le_tsum fun r => mul_le_mul_right ?_ _).trans
      (h q.2.1.1 q.2.1.2 q.2.2 (e 0) (fun az => g ([], P.nizkView q (e 0) az)) (fun _ => hg _) hb)
    split_ifs
    · exact le_rfl
    · exact zero_le
  calc _ ≤ ∑' e, PMF.uniformFintype (Fin 1 → P.Ch) e *
          (∑' s, PMF.uniformFintype P.SimRand s *
            g ([], P.nizkView q (e 0) (P.simulate q.2.1.1 (e 0) s)) + δ) :=
        ENNReal.tsum_le_tsum fun e => mul_le_mul_right (hstep e) _
    _ = _ := by
        simp only [mul_add]
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- The commitment bound `γ` of `P` at every pair of the relation is a key bound of the
protocol of the proving oracle. -/
theorem keyBoundAt_nizkProtocol {γ : ℝ≥0∞} (h : ∀ x w, P.rel x w → P.CommitBoundAt x w γ) :
    (P.nizkProtocol Sid).KeyBoundAt () () γ := by
  intro q look Q
  simp only [guessView_nizkProtocol, vals_nizkProtocol, Fin.sum_univ_one]
  set Qv := Q ([], [], none)
  have hr : ∑' r, PMF.uniformFintype P.Rand r *
      Qv (q.1, q.2.1.1, P.commit q.2.1.1 q.2.1.2 r) ≤ γ := by
    rw [← tsum_map_mul' (PMF.uniformFintype P.Rand)
      (fun r => (q.1, q.2.1.1, P.commit q.2.1.1 q.2.1.2 r)) Qv]
    calc ∑' y, ((PMF.uniformFintype P.Rand).map
            fun r => (q.1, q.2.1.1, P.commit q.2.1.1 q.2.1.2 r)) y * Qv y
        ≤ ∑' y, γ * Qv y := by
          refine ENNReal.tsum_le_tsum fun y => mul_le_mul_left ?_ _
          rw [← PMF.toOuterMeasure_apply_singleton, PMF.toOuterMeasure_map_apply]
          exact (MeasureTheory.measure_mono fun r hr => congrArg (fun k => k.2.2) hr).trans
            (h q.2.1.1 q.2.1.2 q.2.2 y.2.2)
      _ = γ := by rw [ENNReal.tsum_mul_left, PMF.tsum_coe, mul_one]
  calc _ ≤ ∑' e, PMF.uniformFintype (Fin 1 → P.Ch) e *
        ∑' r, PMF.uniformFintype P.Rand r * Qv (q.1, q.2.1.1, P.commit q.2.1.1 q.2.1.2 r) := by
        refine ENNReal.tsum_le_tsum fun e => mul_le_mul_right
          (ENNReal.tsum_le_tsum fun r => mul_le_mul_right ?_ _) _
        split_ifs
        · exact le_rfl
        · exact zero_le
    _ ≤ ∑' e, PMF.uniformFintype (Fin 1 → P.Ch) e * γ :=
        ENNReal.tsum_le_tsum fun e => mul_le_mul_right hr _
    _ = γ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

end Sigma

section ZK

variable {P : Sigma} {Sid : Type} [DecidableEq Sid] [DecidableEq P.Stmt]

variable (P Sid) in
/-- A zero-knowledge distinguisher: an oracle adversary with at most `qH` random-oracle
queries `inl (sid, x, a)` and `qP` proving queries `inr (sid, (x, w))` on every path that
outputs a bit. -/
structure ZKDistinguisher (qH qP : ℕ) : Type 1 where
  /-- The distinguisher. -/
  run : OracleAdv (P.nizkProtocol Sid).Query (P.nizkProtocol Sid).Answer Bool
  /-- The query bounds. -/
  isQueryBound : IsQueryBound₂ run qH qP

/-- The probability that the distinguisher outputs `true` against the random oracle and
the honest prover. -/
noncomputable def zkReal {qH qP : ℕ} (D : ZKDistinguisher P Sid qH qP) : ℝ≥0∞ :=
  (OracleAdv.run (toOracle (realStep (G := P.nizkProtocol Sid) ((), ()))) D.run
    (Protocol.Tables.empty, false)).toOuterMeasure {y | y.1 = true}

/-- The probability that the distinguisher outputs `true` against the random oracle
programmed by the simulator, which answers proving queries from the session identifier
and the statement. -/
noncomputable def zkSim {qH qP : ℕ} (D : ZKDistinguisher P Sid qH qP) : ℝ≥0∞ :=
  (OracleAdv.run (toOracle (simStep (G := P.nizkProtocol Sid) ())) D.run
    (Protocol.Tables.empty, false)).toOuterMeasure {y | y.1 = true}

/-- For a statistical HVZK distance `δ` and commitment bound `γ` at every pair of the
relation, the probability that a distinguisher outputs the bit `b` in the real game is
at most that in the simulated game plus `qP·δ + qP·(qH + qP)·γ`. -/
theorem zk_output_le {δ γ : ℝ≥0∞} (hZK : ∀ x w, P.rel x w → P.StatHVZKAt x w δ)
    (hγ : ∀ x w, P.rel x w → P.CommitBoundAt x w γ) {qH qP : ℕ}
    (D : ZKDistinguisher P Sid qH qP) (b : Bool) :
    (OracleAdv.run (toOracle (realStep (G := P.nizkProtocol Sid) ((), ()))) D.run
        (Protocol.Tables.empty, false)).toOuterMeasure {y | y.1 = b} ≤
      (OracleAdv.run (toOracle (simStep (G := P.nizkProtocol Sid) ())) D.run
        (Protocol.Tables.empty, false)).toOuterMeasure {y | y.1 = b} +
        (qP * δ + ((qP * (qH + qP) : ℕ) : ℝ≥0∞) * γ) := by
  set g : Bool × ((P.nizkProtocol Sid).Tables × Bool) → ℝ≥0∞ :=
    fun y => if y.1 = b then 1 else 0 with hgdef
  have hg : ∀ y, g y ≤ 1 := fun y => by simp only [g]; split_ifs <;> simp
  have hgr : RejInsensitive g := fun _ _ => rfl
  have hE : ∀ p : PMF (Bool × ((P.nizkProtocol Sid).Tables × Bool)),
      p.toOuterMeasure {y | y.1 = b} = ∑' y, p y * g y := fun p => by
    rw [PMF.toOuterMeasure_apply]
    refine tsum_congr fun y => ?_
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, g, mul_ite, mul_one, mul_zero]
  have hflag := run_real_flag_le ((), ()) (Sigma.keyBoundAt_nizkProtocol (Sid := Sid) hγ) D.run qH qP
    D.isQueryBound Protocol.Tables.empty rfl
  replace hflag := (toOuterMeasure_eq_tsum_ite _
    fun y : Bool × ((P.nizkProtocol Sid).Tables × Bool) => y.2.2).symm.trans_le hflag
  have hflag' : ((qP * ((Protocol.Tables.empty : (P.nizkProtocol Sid).Tables).hash.length +
      (Protocol.Tables.empty : (P.nizkProtocol Sid).Tables).prog.length + qH +
      (P.nizkProtocol Sid).μ * qP) : ℕ) : ℝ≥0∞) = ((qP * (qH + qP) : ℕ) : ℝ≥0∞) := by
    simp [Protocol.Tables.empty]
  rw [hflag'] at hflag
  have hsim := run_real_le_sim ((), ()) (Sigma.statHVZKAt_nizkProtocol (Sid := Sid) hZK) D.run qH qP
    D.isQueryBound (Protocol.Tables.empty, false) g hg hgr
  rw [hE, hE]
  calc _ ≤ ∑' y, OracleAdv.run (toOracle (realStep (G := P.nizkProtocol Sid) ((), ()))) D.run
          (Protocol.Tables.empty, false) y * (offFlag g y + if y.2.2 = true then 1 else 0) := by
        refine ENNReal.tsum_le_tsum fun y => mul_le_mul_right ?_ _
        simp only [offFlag]
        split_ifs <;> simp [hg]
    _ = ∑' y, OracleAdv.run (toOracle (realStep (G := P.nizkProtocol Sid) ((), ()))) D.run
          (Protocol.Tables.empty, false) y * offFlag g y +
        ∑' y, OracleAdv.run (toOracle (realStep (G := P.nizkProtocol Sid) ((), ()))) D.run
          (Protocol.Tables.empty, false) y * (if y.2.2 = true then 1 else 0) := by
        simp only [mul_add]
        rw [ENNReal.tsum_add]
    _ ≤ _ := by
        rw [← add_assoc]
        exact add_le_add hsim hflag

/-- For a distribution on outputs `(b, s)`, the probabilities of `b = true` and of
`b = false` add up to `1`. -/
theorem toOuterMeasure_fst_true_add_false {σ : Type} (p : PMF (Bool × σ)) :
    p.toOuterMeasure {y | y.1 = true} + p.toOuterMeasure {y | y.1 = false} = 1 := by
  rw [PMF.toOuterMeasure_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_add]
  refine (tsum_congr fun y => ?_).trans p.tsum_coe
  rcases y with ⟨_ | _, s⟩ <;> simp

/-- **Zero knowledge of the strong Fiat–Shamir transform, real against simulated.** For
a Σ-protocol with statistical HVZK distance `δ` and commitment bound `γ` at every pair of
the relation, and every distinguisher with at most `qH` random-oracle and `qP` proving
queries, `zkReal D ≤ zkSim D + qP·δ + qP·(qH + qP)·γ`. -/
theorem zkReal_le_zkSim {δ γ : ℝ≥0∞} (hZK : ∀ x w, P.rel x w → P.StatHVZKAt x w δ)
    (hγ : ∀ x w, P.rel x w → P.CommitBoundAt x w γ) {qH qP : ℕ}
    (D : ZKDistinguisher P Sid qH qP) :
    zkReal D ≤ zkSim D + (qP * δ + ((qP * (qH + qP) : ℕ) : ℝ≥0∞) * γ) :=
  zk_output_le hZK hγ D true

/-- **Zero knowledge of the strong Fiat–Shamir transform, simulated against real.**
Under the hypotheses of `zkReal_le_zkSim`,
`zkSim D ≤ zkReal D + qP·δ + qP·(qH + qP)·γ`. -/
theorem zkSim_le_zkReal {δ γ : ℝ≥0∞} (hZK : ∀ x w, P.rel x w → P.StatHVZKAt x w δ)
    (hγ : ∀ x w, P.rel x w → P.CommitBoundAt x w γ) {qH qP : ℕ}
    (D : ZKDistinguisher P Sid qH qP) :
    zkSim D ≤ zkReal D + (qP * δ + ((qP * (qH + qP) : ℕ) : ℝ≥0∞) * γ) := by
  have h := zk_output_le hZK hγ D false
  have hs := toOuterMeasure_fst_true_add_false
    (OracleAdv.run (toOracle (simStep (G := P.nizkProtocol Sid) ())) D.run
      (Protocol.Tables.empty, false))
  have hr := toOuterMeasure_fst_true_add_false
    (OracleAdv.run (toOracle (realStep (G := P.nizkProtocol Sid) ((), ()))) D.run
      (Protocol.Tables.empty, false))
  have hfin : (OracleAdv.run (toOracle (realStep (G := P.nizkProtocol Sid) ((), ()))) D.run
      (Protocol.Tables.empty, false)).toOuterMeasure {y | y.1 = false} ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (toOuterMeasure_le_one _ _)
  refine ENNReal.le_of_add_le_add_right hfin ?_
  unfold zkSim zkReal
  calc _ ≤ _ + ((OracleAdv.run (toOracle (simStep (G := P.nizkProtocol Sid) ())) D.run
          (Protocol.Tables.empty, false)).toOuterMeasure {y | y.1 = false} +
          (qP * δ + ((qP * (qH + qP) : ℕ) : ℝ≥0∞) * γ)) := add_le_add le_rfl h
    _ = 1 + (qP * δ + ((qP * (qH + qP) : ℕ) : ℝ≥0∞) * γ) := by rw [← add_assoc, hs]
    _ = _ := by rw [← hr]; ring

end ZK

/-! ## The Σ-protocol of a linear relation -/

section Linear

open CatCrypt.Examples

variable {gp : GroupParam} {n m : ℕ} {S : Type} {toRel : S → LinearRelation gp n m}
  {gen : PMF (S × (Fin n → gp.Scalar))} [DecidableEq S] {Sid : Type} [DecidableEq Sid]

instance : DecidableEq (linearSigma gp n m toRel gen).Stmt := inferInstanceAs (DecidableEq S)

omit [DecidableEq S] in
/-- The Σ-protocol of a linear relation has perfect HVZK at every pair of the
relation. -/
theorem linearSigma_statHVZKAt (s : S) (w : Fin n → gp.Scalar) (hw : (toRel s).Holds w) :
    (linearSigma gp n m toRel gen).StatHVZKAt s w 0 := by
  have h := (linearSigma_perfectHVZK (gen := PMF.pure (s, w)) toRel fun s' w' hsw => by
    rw [PMF.support_pure, Set.mem_singleton_iff, Prod.mk.injEq] at hsw
    obtain ⟨rfl, rfl⟩ := hsw
    exact hw).statHVZK s w ((PMF.mem_support_pure_iff _ _).mpr rfl)
  exact h

/-- **Knowledge soundness of the strong Fiat–Shamir proofs for a linear relation.** For
every adversary `A` with at most `qH` random-oracle queries that chooses its statement,
with `ε = ksAdvantage A`, `ε·(ε/(qH + 1) − 1/|Scalar|) ≤ ksExtractProb A`. -/
theorem linearSigma_ksExtractProb_ge {qH : ℕ}
    (A : KSAdversary (linearSigma gp n m toRel gen) Sid qH) :
    ksAdvantage A * (ksAdvantage A / ((qH + 1 : ℕ) : ℝ≥0∞) - 1 / Fintype.card gp.Scalar) ≤
      ksExtractProb A :=
  ksExtractProb_ge (linearSigma_specialSound toRel gen) A

/-- **Zero knowledge of the strong Fiat–Shamir proofs for a linear relation, real
against simulated.** For a commitment bound `γ` at every pair of the relation and every
distinguisher with at most `qH` random-oracle and `qP` proving queries,
`zkReal D ≤ zkSim D + qP·(qH + qP)·γ`. -/
theorem linearSigma_zkReal_le_zkSim {γ : ℝ≥0∞}
    (hγ : ∀ s w, (toRel s).Holds w → (linearSigma gp n m toRel gen).CommitBoundAt s w γ)
    {qH qP : ℕ} (D : ZKDistinguisher (linearSigma gp n m toRel gen) Sid qH qP) :
    zkReal D ≤ zkSim D + ((qP * (qH + qP) : ℕ) : ℝ≥0∞) * γ := by
  simpa using zkReal_le_zkSim (δ := 0) (fun s w hw => linearSigma_statHVZKAt s w hw) hγ D

/-- **Zero knowledge of the strong Fiat–Shamir proofs for a linear relation, simulated
against real.** Under the hypotheses of `linearSigma_zkReal_le_zkSim`,
`zkSim D ≤ zkReal D + qP·(qH + qP)·γ`. -/
theorem linearSigma_zkSim_le_zkReal {γ : ℝ≥0∞}
    (hγ : ∀ s w, (toRel s).Holds w → (linearSigma gp n m toRel gen).CommitBoundAt s w γ)
    {qH qP : ℕ} (D : ZKDistinguisher (linearSigma gp n m toRel gen) Sid qH qP) :
    zkSim D ≤ zkReal D + ((qP * (qH + qP) : ℕ) : ℝ≥0∞) * γ := by
  simpa using zkSim_le_zkReal (δ := 0) (fun s w hw => linearSigma_statHVZKAt s w hw) hγ D

end Linear

end CatCrypt.Crypto.FiatShamirROM
