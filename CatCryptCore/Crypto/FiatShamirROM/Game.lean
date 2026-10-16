/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OracleForkingLemma

/-!
# EUF-CMA security of Fiat–Shamir signatures in the random-oracle model: the game

A Σ-protocol `P` with explicit prover randomness `P.Rand` and simulator
randomness `P.SimRand`, and the Fiat–Shamir signature scheme over it: a signature
on `m` under the statement `x` is `(a, z)` with `a = P.commit x w r`,
`e = H(a, m)` and `z = P.respond x w r e`; it verifies when
`P.verify x a H(a, m) z`. The hash function `H : Com × M → Ch` is a random
oracle.

The EUF-CMA game samples `(x, w)` from the generator `P.gen` and runs an adaptive
oracle adversary (`OracleAdv`) on `x` with hash queries `inl (a, m)` and signing
queries `inr m`, at most `qH` and `qS` of them on every path
(`OracleForking.IsQueryBound₂`). The challenger keeps the oracle state
`Tables × Bool`:

* `hash` — the random-oracle entries created by hash queries, in creation order;
* `prog` — the random-oracle entries created by signing queries;
* `signed` — the messages submitted to the signing oracle;
* the flag — set when a signing query needs the oracle value at a point that is
  already defined.

A hash query returns the recorded value of its point or samples a fresh uniform
value and records it. The real signing oracle samples `e` and `r`, defines
`H(P.commit x w r, m) := e` and answers `(P.commit x w r, P.respond x w r e)`.
The simulated signing oracle knows only `x`: it samples `e` and `s`, computes
`(a, z) = P.simulate x e s`, defines `H(a, m) := e` and answers `(a, z)`. When the
point is already defined both oracles set the flag, and the real oracle responds
to the recorded value. At the end the challenger queries `H(a*, m*)` for the
forgery `(m*, (a*, z*))`, and the adversary wins when `P.verify x a* H(a*, m*) z*`
holds and `m*` was never signed.

## Main definitions

* `Sigma` — a Σ-protocol with explicit randomness, generator and extractor
* `Sigma.SpecialSound`, `Sigma.PerfectHVZK`, `Sigma.CommitBound γ` — special
  soundness, perfect honest-verifier zero knowledge, and the bound `γ` on the
  probability of each commitment
* `Sigma.Complete`, `Sigma.UniqueResp` — completeness of the honest transcript
  and uniqueness of accepted responses
* `Sigma.relGame B`, `Sigma.relAdvantage B` — the relation game: sample
  `(x, w) ← P.gen`; `B x` outputs `w'` and wins when `P.rel x w'`
* `realStep`, `simStep` — the real and simulated oracles
* `eufcmaGame A`, `eufcmaAdvantage A` — the EUF-CMA game and advantage
* `simGame A`, `simAdvantage A` — the game with the simulated signing oracle

## Main results

* `run_real_apply_false_eq_sim` — for a generated pair, the real and simulated
  runs agree on every outcome with the flag cleared
* `run_real_flag_le` — from tables with `L` entries, a run with at most `h` hash
  and `q` signing queries sets the flag with probability at most
  `q·(L + h + q)·γ`
* `eufcmaAdvantage_le_simAdvantage` — the EUF-CMA advantage is at most the
  simulated-game advantage plus `qS·(qH + 1 + qS)·γ`

## References

* A. Fiat, A. Shamir, *How to prove yourself*, CRYPTO 1986.
* D. Pointcheval, J. Stern, *Security arguments for digital signatures and blind
  signatures*, J. Cryptology 13(3), 2000.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.FiatShamirROM

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.OracleForking
open scoped ENNReal

/-! ## Σ-protocols with explicit randomness -/

/-- A Σ-protocol for the relation `rel`, with a generator of statement–witness
pairs, prover randomness `Rand`, simulator randomness `SimRand`, and a
special-soundness extractor. -/
structure Sigma : Type 1 where
  /-- Statements. -/
  Stmt : Type
  /-- Witnesses. -/
  Wit : Type
  /-- Commitments (first messages). -/
  Com : Type
  /-- Challenges. -/
  Ch : Type
  /-- Responses. -/
  Resp : Type
  /-- Prover randomness. -/
  Rand : Type
  /-- Simulator randomness. -/
  SimRand : Type
  [finCh : Fintype Ch]
  [neCh : Nonempty Ch]
  [decCh : DecidableEq Ch]
  [decCom : DecidableEq Com]
  [finRand : Fintype Rand]
  [neRand : Nonempty Rand]
  [finSimRand : Fintype SimRand]
  [neSimRand : Nonempty SimRand]
  [inhWit : Inhabited Wit]
  /-- The relation. -/
  rel : Stmt → Wit → Prop
  [decRel : ∀ x w, Decidable (rel x w)]
  /-- The generator of statement–witness pairs (key generation). -/
  gen : PMF (Stmt × Wit)
  /-- The commitment from the prover randomness. -/
  commit : Stmt → Wit → Rand → Com
  /-- The response to a challenge from the prover randomness. -/
  respond : Stmt → Wit → Rand → Ch → Resp
  /-- The verifier. -/
  verify : Stmt → Com → Ch → Resp → Bool
  /-- The HVZK simulator: a commitment and response for a given challenge. -/
  simulate : Stmt → Ch → SimRand → Com × Resp
  /-- The special-soundness extractor on two transcripts with the same commitment. -/
  extract : Stmt → Com → Ch → Resp → Ch → Resp → Wit

attribute [instance] Sigma.finCh Sigma.neCh Sigma.decCh Sigma.decCom Sigma.finRand
  Sigma.neRand Sigma.finSimRand Sigma.neSimRand Sigma.inhWit Sigma.decRel

namespace Sigma

variable (P : Sigma)

/-- **Special soundness.** Two accepting transcripts `(a, e, z)` and `(a, e', z')`
with `e ≠ e'` give a witness through the extractor. -/
def SpecialSound : Prop :=
  ∀ x a e z e' z', P.verify x a e z = true → P.verify x a e' z' = true → e ≠ e' →
    P.rel x (P.extract x a e z e' z')

/-- **Perfect honest-verifier zero knowledge.** For every generated pair and every
challenge `e`, the commitment and response of the honest prover on uniform
randomness have the same distribution as the simulator output on uniform
simulator randomness. -/
def PerfectHVZK : Prop :=
  ∀ x w, (x, w) ∈ P.gen.support → ∀ e,
    (PMF.uniformOfFintype P.Rand).map (fun r => (P.commit x w r, P.respond x w r e)) =
      (PMF.uniformOfFintype P.SimRand).map (P.simulate x e)

/-- **Commitment bound.** For every generated pair, each commitment value has
probability at most `γ` under uniform prover randomness. -/
def CommitBound (γ : ℝ≥0∞) : Prop :=
  ∀ x w, (x, w) ∈ P.gen.support → ∀ a,
    (PMF.uniformOfFintype P.Rand).toOuterMeasure {r | P.commit x w r = a} ≤ γ

/-- **Completeness.** For a statement `x` with witness `w`, the honest
transcript `(P.commit x w r, e, P.respond x w r e)` verifies for every prover
randomness `r` and every challenge `e`. -/
def Complete : Prop :=
  ∀ x w, P.rel x w → ∀ r e, P.verify x (P.commit x w r) e (P.respond x w r e) = true

/-- **Unique responses.** Two accepting transcripts with the same statement,
commitment and challenge have the same response. -/
def UniqueResp : Prop :=
  ∀ x a e z z', P.verify x a e z = true → P.verify x a e z' = true → z = z'

/-- The relation game: sample `(x, w) ← P.gen`, run `B` on `x`, and check that its
output is a witness for `x`. -/
noncomputable def relGame (B : P.Stmt → PMF P.Wit) : SPComp Bool :=
  PRPPRF.pmfGame (P.gen.bind fun xw => (B xw.1).map fun w' => decide (P.rel xw.1 w'))

/-- The advantage in the relation game. -/
noncomputable def relAdvantage (B : P.Stmt → PMF P.Wit) : ℝ≥0∞ :=
  prTrue (P.relGame B) Heap.empty

end Sigma

variable (P : Sigma) (M : Type) [DecidableEq M]

/-! ## Oracle state -/

/-- A query: `inl (a, m)` asks the random oracle at `(a, m)`, `inr m` asks for a
signature on `m`. -/
abbrev Query := (P.Com × M) ⊕ M

/-- An answer: `inl e` for a hash query, `inr (a, z)` for a signing query. -/
abbrev Answer := P.Ch ⊕ (P.Com × P.Resp)

/-- A forgery `(m, (a, z))`. -/
abbrev Forgery := M × (P.Com × P.Resp)

/-- The challenger's tables. -/
structure Tables where
  /-- Random-oracle entries created by hash queries, oldest first. -/
  hash : List ((P.Com × M) × P.Ch)
  /-- Random-oracle entries created by signing queries, oldest first. -/
  prog : List ((P.Com × M) × P.Ch)
  /-- Messages submitted to the signing oracle. -/
  signed : List M

variable {P M}

/-- The empty tables. -/
def Tables.empty : Tables P M := ⟨[], [], []⟩

/-- Position of the first entry at point `k`. -/
def findKey (l : List ((P.Com × M) × P.Ch)) (k : P.Com × M) : Option ℕ :=
  l.findIdx? fun p => decide (p.1 = k)

/-- Value of the first entry at point `k`. -/
def lookupIn (l : List ((P.Com × M) × P.Ch)) (k : P.Com × M) : Option P.Ch :=
  (findKey l k).bind fun i => l[i]?.map Prod.snd

/-- The random-oracle value at `k`, if defined. -/
def Tables.lookup (t : Tables P M) (k : P.Com × M) : Option P.Ch :=
  (lookupIn t.prog k).or (lookupIn t.hash k)

/-! ## Oracles -/

/-- A hash query: the recorded value, or a fresh uniform value recorded in `hash`. -/
noncomputable def hashStep (t : Tables P M) (b : Bool) (k : P.Com × M) :
    Step (Answer P) (Tables P M × Bool) P.Ch :=
  match t.lookup k with
  | some e => .plain (PMF.pure (.inl e, (t, b)))
  | none => .fresh fun e => (.inl e, ({ t with hash := t.hash ++ [(k, e)] }, b))

/-- The signing answer `(a, z)` on `m` with oracle value `e`: if `H(a, m)` is
defined the flag is set, otherwise `H(a, m) := e` is recorded in `prog`. -/
def signOutOf (t : Tables P M) (b : Bool) (m : M) (az : P.Com × P.Resp) (e : P.Ch) :
    Answer P × (Tables P M × Bool) :=
  match t.lookup (az.1, m) with
  | some _ => (.inr az, ({ t with signed := t.signed ++ [m] }, true))
  | none => (.inr az, ({ t with prog := t.prog ++ [((az.1, m), e)], signed := t.signed ++ [m] }, b))

/-- The real signing oracle on `m` for the pair `(x, w)`, from the sampled
challenge `e` and prover randomness `r`: commitment `a = P.commit x w r`, oracle
value `H(a, m) := e`, response `P.respond x w r e`. If `H(a, m)` is already
defined, the response is to the recorded value and the flag is set. -/
def realSignOut (x : P.Stmt) (w : P.Wit) (t : Tables P M) (b : Bool) (m : M) (e : P.Ch)
    (r : P.Rand) : Answer P × (Tables P M × Bool) :=
  match t.lookup (P.commit x w r, m) with
  | some e' => (.inr (P.commit x w r, P.respond x w r e'),
      ({ t with signed := t.signed ++ [m] }, true))
  | none => (.inr (P.commit x w r, P.respond x w r e),
      ({ t with prog := t.prog ++ [((P.commit x w r, m), e)], signed := t.signed ++ [m] }, b))

/-- The simulated signing oracle on `m` for the statement `x`, from the sampled
challenge `e` and simulator randomness `s`. -/
def simSignOut (x : P.Stmt) (t : Tables P M) (b : Bool) (m : M) (e : P.Ch) (s : P.SimRand) :
    Answer P × (Tables P M × Bool) :=
  signOutOf t b m (P.simulate x e s) e

/-- A uniform challenge followed by an independent uniform value of `β`, mapped
by `F`. -/
noncomputable def sampleCh {β γ : Type} [Fintype β] [Nonempty β] (F : P.Ch → β → γ) : PMF γ :=
  (PMF.uniformOfFintype P.Ch).bind fun e => (PMF.uniformOfFintype β).map fun y => F e y

/-- The real oracle for the pair `(x, w)`. -/
noncomputable def realStep (xw : P.Stmt × P.Wit) (s : Tables P M × Bool) :
    Query P M → Step (Answer P) (Tables P M × Bool) P.Ch
  | .inl k => hashStep s.1 s.2 k
  | .inr m => .plain (sampleCh (realSignOut xw.1 xw.2 s.1 s.2 m))

/-- The simulated oracle for the statement `x`. -/
noncomputable def simStep (x : P.Stmt) (s : Tables P M × Bool) :
    Query P M → Step (Answer P) (Tables P M × Bool) P.Ch
  | .inl k => hashStep s.1 s.2 k
  | .inr m => .plain (sampleCh (simSignOut x s.1 s.2 m))

/-! ## Adversaries and games -/

variable (P M) in
/-- An EUF-CMA adversary in the random-oracle model: on the statement (public key),
an adaptive oracle adversary outputting a forgery with at most `qH` hash queries
and `qS` signing queries. -/
structure Adversary (qH qS : ℕ) : Type 1 where
  /-- The adversary on statement `x`. -/
  run : P.Stmt → OracleAdv (Query P M) (Answer P) (Forgery P M)
  /-- The query bounds. -/
  isQueryBound : ∀ x, IsQueryBound₂ (run x) qH qS

/-- The adversary followed by the challenger's hash query on the forgery point. -/
def withVerify : OracleAdv (Query P M) (Answer P) (Forgery P M) →
    OracleAdv (Query P M) (Answer P) (Forgery P M)
  | .ret (m, a, z) => .query (.inl (a, m)) fun _ => .ret (m, a, z)
  | .rand p k => .rand p fun b => withVerify (k b)
  | .query d k => .query d fun r => withVerify (k r)

/-- The winning condition on the final forgery and tables: the message was never
signed and `P.verify x a H(a, m) z`. -/
def wins (x : P.Stmt) (y : Forgery P M × (Tables P M × Bool)) : Bool :=
  !(y.2.1.signed.contains y.1.1) &&
    match y.2.1.lookup (y.1.2.1, y.1.1) with
    | some e => P.verify x y.1.2.1 e y.1.2.2
    | none => false

/-- The distribution of the EUF-CMA experiment against the oracle family `O`
indexed by the generated pair. -/
noncomputable def gameDist (O : P.Stmt × P.Wit → Tables P M × Bool → Query P M →
    Step (Answer P) (Tables P M × Bool) P.Ch) {qH qS : ℕ} (A : Adversary P M qH qS) :
    PMF Bool :=
  P.gen.bind fun xw =>
    (OracleAdv.run (toOracle (O xw)) (withVerify (A.run xw.1)) (Tables.empty, false)).map
      (wins xw.1)

/-- The EUF-CMA game in the random-oracle model. -/
noncomputable def eufcmaGame {qH qS : ℕ} (A : Adversary P M qH qS) : SPComp Bool :=
  PRPPRF.pmfGame (gameDist realStep A)

/-- The EUF-CMA advantage in the random-oracle model. -/
noncomputable def eufcmaAdvantage {qH qS : ℕ} (A : Adversary P M qH qS) : ℝ≥0∞ :=
  prTrue (eufcmaGame A) Heap.empty

/-- The EUF-CMA game with the simulated signing oracle. -/
noncomputable def simGame {qH qS : ℕ} (A : Adversary P M qH qS) : SPComp Bool :=
  PRPPRF.pmfGame (gameDist (fun xw => simStep xw.1) A)

/-- The advantage in the simulated game. -/
noncomputable def simAdvantage {qH qS : ℕ} (A : Adversary P M qH qS) : ℝ≥0∞ :=
  prTrue (simGame A) Heap.empty

/-! ## The real and simulated oracles agree until the flag is set -/

section Hop

variable {α : Type}

omit [DecidableEq M] in
theorem sampleCh_bind {β γ δ : Type} [Fintype β] [Nonempty β] (F : P.Ch → β → γ)
    (g : γ → PMF δ) :
    (sampleCh F).bind g = (PMF.uniformOfFintype P.Ch).bind fun e =>
      (PMF.uniformOfFintype β).bind fun y => g (F e y) := by
  simp only [sampleCh, PMF.bind_bind, PMF.bind_map, Function.comp_def]

theorem realStep_flag (xw : P.Stmt × P.Wit) (t : Tables P M) (d : Query P M)
    (x : Answer P × (Tables P M × Bool))
    (hx : x ∈ (toOracle (realStep xw) (t, true) d).support) : x.2.2 = true := by
  cases d with
  | inl k =>
    simp only [toOracle, realStep, hashStep] at hx
    cases hl : t.lookup k with
    | some e =>
      simp only [hl, Step.toPMF, PMF.support_pure, Set.mem_singleton_iff] at hx
      subst hx; rfl
    | none =>
      simp only [hl, Step.toPMF, PMF.support_map, Set.mem_image] at hx
      obtain ⟨e, _, rfl⟩ := hx
      rfl
  | inr m =>
    simp only [toOracle, realStep, Step.toPMF, sampleCh, PMF.mem_support_bind_iff,
      PMF.support_map, Set.mem_image] at hx
    obtain ⟨e, _, r, _, rfl⟩ := hx
    unfold realSignOut
    split <;> rfl

theorem simStep_flag (x₀ : P.Stmt) (t : Tables P M) (d : Query P M)
    (x : Answer P × (Tables P M × Bool))
    (hx : x ∈ (toOracle (simStep x₀) (t, true) d).support) : x.2.2 = true := by
  cases d with
  | inl k =>
    simp only [toOracle, simStep, hashStep] at hx
    cases hl : t.lookup k with
    | some e =>
      simp only [hl, Step.toPMF, PMF.support_pure, Set.mem_singleton_iff] at hx
      subst hx; rfl
    | none =>
      simp only [hl, Step.toPMF, PMF.support_map, Set.mem_image] at hx
      obtain ⟨e, _, rfl⟩ := hx
      rfl
  | inr m =>
    simp only [toOracle, simStep, Step.toPMF, sampleCh, PMF.mem_support_bind_iff,
      PMF.support_map, Set.mem_image] at hx
    obtain ⟨e, _, s, _, rfl⟩ := hx
    unfold simSignOut signOutOf
    split <;> rfl

/-- On an outcome with the flag cleared, the real signing answer from `(e, r)` is
that outcome exactly when the answer built by `signOutOf` from the honest
transcript is. -/
theorem eq_realSignOut_iff (x : P.Stmt) (w : P.Wit) (t : Tables P M) (b : Bool) (m : M)
    (e : P.Ch) (r : P.Rand) (o : Answer P × (Tables P M × Bool)) (ho : o.2.2 = false) :
    o = realSignOut x w t b m e r ↔
      o = signOutOf t b m (P.commit x w r, P.respond x w r e) e := by
  unfold realSignOut signOutOf
  dsimp only
  cases t.lookup (P.commit x w r, m) with
  | some e' =>
    constructor <;> intro h <;> rw [h] at ho <;> exact absurd ho (by simp)
  | none => rfl

/-- On outcomes with the flag cleared, one real transition and one simulated
transition have the same probability, for a generated pair. -/
theorem realStep_apply_false_eq (hZK : P.PerfectHVZK) (xw : P.Stmt × P.Wit)
    (hxw : xw ∈ P.gen.support) (s : Tables P M × Bool) (d : Query P M)
    (r : Answer P) (t' : Tables P M) :
    toOracle (realStep xw) s d (r, (t', false)) =
      toOracle (simStep xw.1) s d (r, (t', false)) := by
  classical
  cases d with
  | inl k => rfl
  | inr m =>
    simp only [toOracle, realStep, simStep, Step.toPMF, sampleCh, PMF.bind_apply]
    refine tsum_congr fun e => ?_
    congr 1
    have hmap : ∀ {β : Type} (p : PMF β) (F G : β → Answer P × (Tables P M × Bool)),
        (∀ y, ((r, (t', false)) = F y ↔ (r, (t', false)) = G y)) →
        p.map F (r, (t', false)) = p.map G (r, (t', false)) := by
      intro β p F G hFG
      simp only [PMF.map_apply]
      refine tsum_congr fun y => ?_
      split_ifs with h1 h2 h2
      · rfl
      · exact absurd ((hFG y).mp h1) h2
      · exact absurd ((hFG y).mpr h2) h1
      · rfl
    rw [hmap _ _ (fun y => signOutOf s.1 s.2 m (P.commit xw.1 xw.2 y, P.respond xw.1 xw.2 y e) e)
      (fun y => eq_realSignOut_iff xw.1 xw.2 s.1 s.2 m e y _ rfl)]
    have hc : (PMF.uniformOfFintype P.Rand).map
        (fun y => signOutOf s.1 s.2 m (P.commit xw.1 xw.2 y, P.respond xw.1 xw.2 y e) e) =
        ((PMF.uniformOfFintype P.Rand).map
          (fun y => (P.commit xw.1 xw.2 y, P.respond xw.1 xw.2 y e))).map
          (fun az => signOutOf s.1 s.2 m az e) := by
      rw [PMF.map_comp]; rfl
    rw [hc, hZK xw.1 xw.2 hxw e, PMF.map_comp]
    rfl

/-- **Identical until the flag is set.** For a generated pair, the real and
simulated runs give every outcome with the flag cleared the same probability. -/
theorem run_real_apply_false_eq_sim (hZK : P.PerfectHVZK) (xw : P.Stmt × P.Wit)
    (hxw : xw ∈ P.gen.support) (A : OracleAdv (Query P M) (Answer P) α)
    (s : Tables P M × Bool) (a : α) (t' : Tables P M) :
    OracleAdv.run (toOracle (realStep xw)) A s (a, (t', false)) =
      OracleAdv.run (toOracle (simStep xw.1)) A s (a, (t', false)) :=
  OracleAdv.run_apply_flag_false_eq _ _
    (fun t d _ _ => (PMF.apply_eq_zero_iff _ _).mpr fun hx =>
      Bool.noConfusion (realStep_flag xw t d _ hx))
    (fun t d _ _ => (PMF.apply_eq_zero_iff _ _).mpr fun hx =>
      Bool.noConfusion (simStep_flag xw.1 t d _ hx))
    (realStep_apply_false_eq hZK xw hxw) A s a t'

/-- Winning in the real run has probability at most winning in the simulated run
plus the probability that the real run sets the flag. -/
theorem run_real_wins_le (hZK : P.PerfectHVZK) (xw : P.Stmt × P.Wit)
    (hxw : xw ∈ P.gen.support) (A : OracleAdv (Query P M) (Answer P) (Forgery P M))
    (s : Tables P M × Bool) (x : P.Stmt) :
    (OracleAdv.run (toOracle (realStep xw)) A s).toOuterMeasure {y | wins x y = true} ≤
      (OracleAdv.run (toOracle (simStep xw.1)) A s).toOuterMeasure {y | wins x y = true} +
      (OracleAdv.run (toOracle (realStep xw)) A s).toOuterMeasure {y | y.2.2 = true} := by
  simp only [PMF.toOuterMeasure_apply]
  rw [← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun y => ?_
  obtain ⟨a, t', fl⟩ := y
  cases fl with
  | false =>
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, Bool.false_eq_true, if_false, add_zero]
    split_ifs
    · exact le_of_eq (run_real_apply_false_eq_sim hZK xw hxw A s a t')
    · exact le_rfl
  | true =>
    simp only [Set.indicator_apply, Set.mem_ofPred_eq, if_true]
    split_ifs
    · exact le_add_left le_rfl
    · simp

end Hop

/-! ## The flag is set with small probability -/

section Flag

variable {α : Type}

theorem lookupIn_isSome_mem {l : List ((P.Com × M) × P.Ch)} {k : P.Com × M}
    (h : (lookupIn l k).isSome) : k ∈ l.map Prod.fst := by
  unfold lookupIn findKey at h
  cases hf : l.findIdx? (fun p => decide (p.1 = k)) with
  | none => simp [hf] at h
  | some i =>
    obtain ⟨hi, hp, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
    simp only [decide_eq_true_eq] at hp
    exact List.mem_map.mpr ⟨l[i], List.getElem_mem hi, hp⟩

theorem lookup_isSome_mem {t : Tables P M} {k : P.Com × M} (h : (t.lookup k).isSome) :
    k ∈ (t.prog ++ t.hash).map Prod.fst := by
  unfold Tables.lookup at h
  rw [List.map_append, List.mem_append]
  cases hp : lookupIn t.prog k with
  | some e => exact Or.inl (lookupIn_isSome_mem (by simp [hp]))
  | none =>
    simp only [hp, Option.none_or] at h
    exact Or.inr (lookupIn_isSome_mem h)

omit [DecidableEq M] in
/-- Union bound: the probability that the commitment is the first component of
some point of a list is at most the length of the list times `γ`. -/
theorem prob_commit_mem_le {γ : ℝ≥0∞} (hγ : P.CommitBound γ) (x : P.Stmt) (w : P.Wit)
    (hxw : (x, w) ∈ P.gen.support) (m : M) (l : List (P.Com × M)) :
    (PMF.uniformOfFintype P.Rand).toOuterMeasure {r | (P.commit x w r, m) ∈ l} ≤
      (l.length : ℝ≥0∞) * γ := by
  induction l with
  | nil => simp
  | cons k l ih =>
    calc (PMF.uniformOfFintype P.Rand).toOuterMeasure {r | (P.commit x w r, m) ∈ k :: l}
        ≤ (PMF.uniformOfFintype P.Rand).toOuterMeasure
            ({r | P.commit x w r = k.1} ∪ {r | (P.commit x w r, m) ∈ l}) := by
          refine MeasureTheory.measure_mono fun r hr => ?_
          simp only [Set.mem_ofPred_eq, List.mem_cons] at hr
          rcases hr with hr | hr
          · exact Or.inl (congrArg Prod.fst hr)
          · exact Or.inr hr
      _ ≤ γ + (l.length : ℝ≥0∞) * γ :=
          (MeasureTheory.measure_union_le _ _).trans (add_le_add (hγ x w hxw k.1) ih)
      _ = _ := by simp [List.length_cons, add_mul, add_comm]

/-- The probability that a real commitment collides with a defined point is at
most `(|hash| + |prog|)·γ`. -/
theorem prob_collision_le {γ : ℝ≥0∞} (hγ : P.CommitBound γ) (x : P.Stmt) (w : P.Wit)
    (hxw : (x, w) ∈ P.gen.support) (t : Tables P M) (m : M) :
    (PMF.uniformOfFintype P.Rand).toOuterMeasure {r | (t.lookup (P.commit x w r, m)).isSome} ≤
      ((t.hash.length + t.prog.length : ℕ) : ℝ≥0∞) * γ := by
  refine (MeasureTheory.measure_mono fun r hr => lookup_isSome_mem hr).trans
    ((prob_commit_mem_le hγ x w hxw m _).trans (le_of_eq ?_))
  simp [Nat.add_comm]

/-- **Collision bound.** For a generated pair, from tables with `L` entries and the
flag cleared, a run of the real oracles asking at most `h` hash and `q` signing
queries sets the flag with probability at most `q·(L + h + q)·γ`. -/
theorem run_real_flag_le {γ : ℝ≥0∞} (hγ : P.CommitBound γ) (xw : P.Stmt × P.Wit)
    (hxw : xw ∈ P.gen.support) (A : OracleAdv (Query P M) (Answer P) α) (h q : ℕ)
    (hA : IsQueryBound₂ A h q) (t : Tables P M) :
    (OracleAdv.run (toOracle (realStep xw)) A (t, false)).toOuterMeasure {y | y.2.2 = true} ≤
      ((q * (t.hash.length + t.prog.length + h + q) : ℕ) : ℝ≥0∞) * γ := by
  induction A generalizing h q t with
  | ret a => simp [PMF.toOuterMeasure_pure_apply]
  | rand p k ih =>
    rw [OracleAdv.run_rand, PMF.toOuterMeasure_bind_apply]
    calc ∑' b, p b * (OracleAdv.run (toOracle (realStep xw)) (k b) (t, false)).toOuterMeasure _
        ≤ ∑' b, p b * (((q * (t.hash.length + t.prog.length + h + q) : ℕ) : ℝ≥0∞) * γ) :=
          ENNReal.tsum_le_tsum fun b => by gcongr; exact ih b h q (hA b) t
      _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  | query d k ih =>
    rw [OracleAdv.run_query]
    cases d with
    | inl key =>
      cases h with
      | zero => exact hA.elim
      | succ h =>
      have hk : ∀ r, IsQueryBound₂ (k r) h q := hA
      simp only [toOracle, realStep, hashStep]
      cases hl : t.lookup key with
      | some e =>
        simp only [Step.toPMF, PMF.pure_bind]
        refine (ih _ h q (hk _) t).trans ?_
        gcongr
        omega
      | none =>
        simp only [Step.toPMF, PMF.bind_map, Function.comp_def, PMF.toOuterMeasure_bind_apply]
        calc ∑' e, PMF.uniformOfFintype P.Ch e * (OracleAdv.run (toOracle (realStep xw))
              (k (.inl e)) ({ t with hash := t.hash ++ [(key, e)] }, false)).toOuterMeasure _
            ≤ ∑' e, PMF.uniformOfFintype P.Ch e *
              (((q * (t.hash.length + t.prog.length + (h + 1) + q) : ℕ) : ℝ≥0∞) * γ) := by
              refine ENNReal.tsum_le_tsum fun e => mul_le_mul_right ?_ _
              refine (ih _ h q (hk _) _).trans (le_of_eq ?_)
              simp only [List.length_append, List.length_singleton]
              congr 3
              omega
          _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    | inr m =>
      cases q with
      | zero => exact hA.elim
      | succ q =>
      have hk : ∀ r, IsQueryBound₂ (k r) h q := hA
      set L := t.hash.length + t.prog.length with hL
      set B : ℝ≥0∞ := ((q * (L + 1 + h + q) : ℕ) : ℝ≥0∞) * γ with hB
      simp only [toOracle, realStep, Step.toPMF, sampleCh_bind, PMF.toOuterMeasure_bind_apply]
      have hterm : ∀ e r, (OracleAdv.run (toOracle (realStep xw))
          (k (realSignOut xw.1 xw.2 t false m e r).1)
            (realSignOut xw.1 xw.2 t false m e r).2).toOuterMeasure {y | y.2.2 = true} ≤
          (if (t.lookup (P.commit xw.1 xw.2 r, m)).isSome then 1 else 0) + B := by
        intro e r
        unfold realSignOut
        cases hl : t.lookup (P.commit xw.1 xw.2 r, m) with
        | some e' =>
          simp only [Option.isSome_some, if_true]
          exact (toOuterMeasure_le_one _ _).trans le_self_add
        | none =>
          simp only [Option.isSome_none, Bool.false_eq_true, if_false, zero_add]
          refine (ih _ h q (hk _) _).trans (le_of_eq ?_)
          simp only [List.length_append, List.length_singleton, hB, hL]
          congr 3
      have hcoll := prob_collision_le hγ xw.1 xw.2 hxw t m
      rw [PMF.toOuterMeasure_apply] at hcoll
      calc ∑' e, PMF.uniformOfFintype P.Ch e * ∑' r, PMF.uniformOfFintype P.Rand r *
            (OracleAdv.run (toOracle (realStep xw)) (k (realSignOut xw.1 xw.2 t false m e r).1)
              (realSignOut xw.1 xw.2 t false m e r).2).toOuterMeasure {y | y.2.2 = true}
          ≤ ∑' e, PMF.uniformOfFintype P.Ch e * ∑' r, PMF.uniformOfFintype P.Rand r *
              ((if (t.lookup (P.commit xw.1 xw.2 r, m)).isSome then 1 else 0) + B) :=
            ENNReal.tsum_le_tsum fun e => mul_le_mul_right
              (ENNReal.tsum_le_tsum fun r => mul_le_mul_right (hterm e r) _) _
        _ = ∑' r, PMF.uniformOfFintype P.Rand r *
              ((if (t.lookup (P.commit xw.1 xw.2 r, m)).isSome then 1 else 0) + B) := by
            rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
        _ = (∑' r, Set.indicator {r | (t.lookup (P.commit xw.1 xw.2 r, m)).isSome}
                (PMF.uniformOfFintype P.Rand) r) + B := by
            simp only [mul_add]
            rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
            congr 1
            refine tsum_congr fun r => ?_
            simp only [Set.indicator_apply, Set.mem_ofPred_eq]
            split_ifs <;> simp
        _ ≤ ((L : ℕ) : ℝ≥0∞) * γ + B := add_le_add_left hcoll _
        _ ≤ _ := by
            rw [hB, ← add_mul]
            gcongr
            rw [← Nat.cast_add, Nat.cast_le]
            have : L + 1 + h + q = L + h + (q + 1) := by omega
            rw [this, Nat.succ_mul]
            omega

end Flag

/-! ## The signing-oracle simulation hop -/

section Game

omit [DecidableEq M] in
theorem isQueryBound₂_withVerify (A : OracleAdv (Query P M) (Answer P) (Forgery P M))
    (h q : ℕ) (hA : IsQueryBound₂ A h q) : IsQueryBound₂ (withVerify A) (h + 1) q := by
  induction A generalizing h q with
  | ret y =>
    obtain ⟨m, a, z⟩ := y
    exact fun _ => trivial
  | rand p k ih => exact fun b => ih b h q (hA b)
  | query d k ih =>
    cases d with
    | inl key =>
      cases h with
      | zero => exact hA.elim
      | succ h => exact fun r => ih r h q (hA r)
    | inr m =>
      cases q with
      | zero => exact hA.elim
      | succ q => exact fun r => ih r h q (hA r)

/-- The advantage in a game built by `gameDist` as an average over generated
pairs. -/
theorem prTrue_gameDist (O : P.Stmt × P.Wit → Tables P M × Bool → Query P M →
    Step (Answer P) (Tables P M × Bool) P.Ch) {qH qS : ℕ} (A : Adversary P M qH qS) :
    prTrue (PRPPRF.pmfGame (gameDist O A)) Heap.empty =
      ∑' xw, P.gen xw *
        (OracleAdv.run (toOracle (O xw)) (withVerify (A.run xw.1))
          (Tables.empty, false)).toOuterMeasure {y | wins xw.1 y = true} := by
  rw [prTrue_pmfGame]
  simp only [gameDist, PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_map_apply]
  rfl

/-- **Signing-oracle simulation.** For a Σ-protocol with perfect HVZK and
commitment bound `γ`, and every adversary with at most `qH` hash queries and `qS`
signing queries, the EUF-CMA advantage is at most the advantage in the game whose
signing oracle is simulated from the statement by programming the random oracle,
plus `qS·(qH + 1 + qS)·γ`. -/
theorem eufcmaAdvantage_le_simAdvantage (hZK : P.PerfectHVZK) {γ : ℝ≥0∞}
    (hγ : P.CommitBound γ) {qH qS : ℕ} (A : Adversary P M qH qS) :
    eufcmaAdvantage A ≤ simAdvantage A + ((qS * (qH + 1 + qS) : ℕ) : ℝ≥0∞) * γ := by
  unfold eufcmaAdvantage simAdvantage eufcmaGame simGame
  rw [prTrue_gameDist, prTrue_gameDist]
  calc _ ≤ ∑' xw, P.gen xw *
          ((OracleAdv.run (toOracle (simStep xw.1)) (withVerify (A.run xw.1))
            (Tables.empty, false)).toOuterMeasure {y | wins xw.1 y = true} +
          ((qS * (qH + 1 + qS) : ℕ) : ℝ≥0∞) * γ) := by
        refine ENNReal.tsum_le_tsum fun xw => ?_
        by_cases hxw : xw ∈ P.gen.support
        · refine mul_le_mul_right ?_ _
          refine (run_real_wins_le hZK xw hxw _ _ _).trans (add_le_add_right ?_ _)
          refine (run_real_flag_le hγ xw hxw _ (qH + 1) qS
            (isQueryBound₂_withVerify _ qH qS (A.isQueryBound _)) Tables.empty).trans
            (le_of_eq ?_)
          simp [Tables.empty]
        · simp [(PMF.apply_eq_zero_iff _ _).mpr hxw]
    _ = _ := by
        simp only [mul_add]
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

end Game

end CatCrypt.Crypto.FiatShamirROM
