/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OracleForkingLemma

/-!
# EUF-CMA security of Fiat–Shamir signatures in the random-oracle model: the game

A Σ-protocol `P` with explicit prover randomness `P.Rand`, simulator randomness
`P.SimRand` and an acceptance test `P.accept` on responses, and the Fiat–Shamir
signature scheme over it: a signing attempt on `m` under the statement `x` computes
`a = P.commit x w r`, `e = H(a, m)` and `z = P.respond x w r e`, and returns the
signature `(a, z)` when `P.accept z` and nothing otherwise; a signature verifies
when `P.verify x a H(a, m) z`. The hash function `H : Com × M → Ch` is a random
oracle.

The EUF-CMA game samples `(x, w)` from the generator `P.gen` and runs an adaptive
oracle adversary (`OracleAdv`) on `x` with hash queries `inl (a, m)` and signing
queries `inr m`, at most `qH` and `qS` of them on every path
(`OracleForking.IsQueryBound₂`). The challenger keeps the oracle state
`Tables × Bool`:

* `hash` — the random-oracle entries created by hash queries, in creation order;
* `prog` — the random-oracle entries created by accepted signing attempts;
* `signed` — the messages submitted to the signing oracle;
* `rej` — the random-oracle entries created by rejected signing attempts, whose
  points the adversary is not shown;
* the flag — set when a query needs the oracle value at a point defined by an
  earlier signing attempt that the adversary did not see, or when a signing
  attempt needs the oracle value at a point already defined.

A hash query returns the recorded value of its point or samples a fresh uniform
value and records it. The real signing oracle samples `e` and `r` and computes
`a = P.commit x w r` and `z = P.respond x w r e`; it defines `H(a, m) := e` and
answers `some (a, z)` when `z` is accepted, and answers `none`, keeping the entry
in `rej`, when `z` is rejected. The simulated signing oracle knows only `x`: it
samples `e` and `s`, computes `(a, z) = P.simulate x e s`, and when `z` is accepted
defines `H(a, m) := e` and answers `some (a, z)`; a rejected `z` is answered `none`
and leaves the oracle unchanged. At the end the challenger queries `H(a*, m*)` for
the forgery `(m*, (a*, z*))`, and the adversary wins when
`P.verify x a* H(a*, m*) z*` holds and `m*` was never signed.

## Main definitions

* `Sigma` — a Σ-protocol with explicit randomness, generator, extractor and
  acceptance test
* `Sigma.SpecialSound`, `Sigma.PerfectHVZK`, `Sigma.CommitBoundAt x w γ`,
  `Sigma.CommitBound γ` — special soundness, perfect honest-verifier zero
  knowledge, and the bound `γ` on the probability of each commitment at one pair
  and at every generated pair
* `Sigma.Complete`, `Sigma.UniqueResp` — completeness of the honest transcript
  and uniqueness of accepted responses
* `Sigma.relGame B`, `Sigma.relAdvantage B` — the relation game: sample
  `(x, w) ← P.gen`; `B x` outputs `w'` and wins when `P.rel x w'`
* `realStep`, `simStep` — the real and simulated oracles
* `eufcmaGame A`, `eufcmaAdvantage A` — the EUF-CMA game and advantage
* `simGame A`, `simAdvantage A` — the game with the simulated signing oracle

## Main results

* `run_real_addRej_flag_le` — an entry of a rejected attempt changes the flag of a
  real run only when the run reaches its point
* `run_real_flag_le` — for a pair `(x, w)` with commitment bound `γ`, from tables
  with `L` entries and no entry of a rejected attempt, a run with at most `h` hash
  and `q` signing queries sets the flag with probability at most
  `q·(L + h + q)·γ`

## References

* A. Fiat, A. Shamir, *How to prove yourself*, CRYPTO 1986.
* D. Pointcheval, J. Stern, *Security arguments for digital signatures and blind
  signatures*, J. Cryptology 13(3), 2000.
* M. Barbosa, G. Barthe, C. Doczkal, J. Don, S. Fehr, B. Grégoire, Y.-H. Huang,
  A. Hülsing, Y. Lee, X. Wu, *Fixing and mechanizing the security proof of
  Fiat-Shamir with aborts and Dilithium*, CRYPTO 2023.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.FiatShamirROM

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.OracleForking
open scoped ENNReal

/-! ## Σ-protocols with explicit randomness -/

/-- A Σ-protocol for the relation `rel`, with a generator of statement–witness
pairs, prover randomness `Rand`, simulator randomness `SimRand`, a
special-soundness extractor and an acceptance test on responses. -/
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
  /-- The acceptance test of a signing attempt on its response: a rejected attempt
  (`accept z = false`) produces no signature. Every response is accepted by
  default. -/
  accept : Resp → Bool := fun _ => true

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

/-- **Commitment bound at one pair.** For the pair `(x, w)`, each commitment value
has probability at most `γ` under uniform prover randomness. -/
def CommitBoundAt (x : P.Stmt) (w : P.Wit) (γ : ℝ≥0∞) : Prop :=
  ∀ a, (PMF.uniformOfFintype P.Rand).toOuterMeasure {r | P.commit x w r = a} ≤ γ

/-- **Commitment bound.** For every generated pair, each commitment value has
probability at most `γ` under uniform prover randomness. -/
def CommitBound (γ : ℝ≥0∞) : Prop :=
  ∀ x w, (x, w) ∈ P.gen.support → P.CommitBoundAt x w γ

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

/-- An answer: `inl e` for a hash query; `inr (some (a, z))` for an accepted
signing attempt and `inr none` for a rejected one. -/
abbrev Answer := P.Ch ⊕ Option (P.Com × P.Resp)

/-- A forgery `(m, (a, z))`. -/
abbrev Forgery := M × (P.Com × P.Resp)

/-- The challenger's tables. -/
structure Tables where
  /-- Random-oracle entries created by hash queries, oldest first. -/
  hash : List ((P.Com × M) × P.Ch)
  /-- Random-oracle entries created by accepted signing attempts, oldest first. -/
  prog : List ((P.Com × M) × P.Ch)
  /-- Messages submitted to the signing oracle. -/
  signed : List M
  /-- Random-oracle entries created by rejected signing attempts, oldest first. -/
  rej : List ((P.Com × M) × P.Ch)

variable {P M}

/-- The empty tables. -/
def Tables.empty : Tables P M := ⟨[], [], [], []⟩

/-- Position of the first entry at point `k`. -/
def findKey (l : List ((P.Com × M) × P.Ch)) (k : P.Com × M) : Option ℕ :=
  l.findIdx? fun p => decide (p.1 = k)

/-- Value of the first entry at point `k`. -/
def lookupIn (l : List ((P.Com × M) × P.Ch)) (k : P.Com × M) : Option P.Ch :=
  (findKey l k).bind fun i => l[i]?.map Prod.snd

/-- The random-oracle value at `k` from the entries of hash queries and accepted
signing attempts, if defined. -/
def Tables.lookup (t : Tables P M) (k : P.Com × M) : Option P.Ch :=
  (lookupIn t.prog k).or (lookupIn t.hash k)

/-- The random-oracle value at `k` from all entries, including those of rejected
signing attempts. -/
def Tables.lookupAll (t : Tables P M) (k : P.Com × M) : Option P.Ch :=
  (t.lookup k).or (lookupIn t.rej k)

/-- The points at which the random oracle is defined. -/
def Tables.keys (t : Tables P M) : List (P.Com × M) :=
  (t.prog ++ t.hash ++ t.rej).map Prod.fst

/-- The number of entries. -/
def Tables.size (t : Tables P M) : ℕ :=
  t.prog.length + t.hash.length + t.rej.length

/-- The tables `t` with the entry `ent` placed first among the entries of
rejected attempts. -/
def Tables.addRej (ent : (P.Com × M) × P.Ch) (t : Tables P M) : Tables P M :=
  { t with rej := ent :: t.rej }

/-! ## Oracles -/

/-- A hash query of the simulated game: the recorded value of a hash or signing
entry, or a fresh uniform value recorded in `hash`. -/
noncomputable def hashStep (t : Tables P M) (b : Bool) (k : P.Com × M) :
    Step (Answer P) (Tables P M × Bool) P.Ch :=
  match t.lookup k with
  | some e => .plain (PMF.pure (.inl e, (t, b)))
  | none => .fresh fun e => (.inl e, ({ t with hash := t.hash ++ [(k, e)] }, b))

/-- A hash query of the real game: the recorded value of a hash or accepted
signing entry; the value recorded by a rejected signing attempt, copied to `hash`
with the flag set; or a fresh uniform value recorded in `hash`. -/
noncomputable def realHashStep (t : Tables P M) (b : Bool) (k : P.Com × M) :
    Step (Answer P) (Tables P M × Bool) P.Ch :=
  match t.lookup k with
  | some e => .plain (PMF.pure (.inl e, (t, b)))
  | none =>
    match lookupIn t.rej k with
    | some e => .plain (PMF.pure (.inl e, ({ t with hash := t.hash ++ [(k, e)] }, true)))
    | none => .fresh fun e => (.inl e, ({ t with hash := t.hash ++ [(k, e)] }, b))

/-- The answer to a signing attempt with commitment `a` and response `z`:
`some (a, z)` when `z` is accepted, `none` otherwise. -/
def signAnswer (a : P.Com) (z : P.Resp) : Answer P :=
  .inr (if P.accept z then some (a, z) else none)

/-- The accepted signing answer `(a, z)` on `m` with oracle value `e`: if `H(a, m)`
is defined the flag is set, otherwise `H(a, m) := e` is recorded in `prog`. -/
def signOutOf (t : Tables P M) (b : Bool) (m : M) (az : P.Com × P.Resp) (e : P.Ch) :
    Answer P × (Tables P M × Bool) :=
  match t.lookup (az.1, m) with
  | some _ => (.inr (some az), ({ t with signed := t.signed ++ [m] }, true))
  | none => (.inr (some az),
      ({ t with prog := t.prog ++ [((az.1, m), e)], signed := t.signed ++ [m] }, b))

/-- The real signing oracle on `m` for the pair `(x, w)`, from the sampled
challenge `e` and prover randomness `r`: commitment `a = P.commit x w r`, oracle
value `H(a, m) := e`, response `z = P.respond x w r e`. An accepted `z` is answered
`some (a, z)` with the entry in `prog`; a rejected `z` is answered `none` with the
entry in `rej`. If `H(a, m)` is already defined, the response is to the recorded
value and the flag is set. -/
def realSignOut (x : P.Stmt) (w : P.Wit) (t : Tables P M) (b : Bool) (m : M) (e : P.Ch)
    (r : P.Rand) : Answer P × (Tables P M × Bool) :=
  match t.lookupAll (P.commit x w r, m) with
  | some e' => (signAnswer (P.commit x w r) (P.respond x w r e'),
      ({ t with signed := t.signed ++ [m] }, true))
  | none =>
    if P.accept (P.respond x w r e) then
      (.inr (some (P.commit x w r, P.respond x w r e)),
        ({ t with prog := t.prog ++ [((P.commit x w r, m), e)], signed := t.signed ++ [m] }, b))
    else
      (.inr none,
        ({ t with signed := t.signed ++ [m], rej := t.rej ++ [((P.commit x w r, m), e)] }, b))

/-- The simulated signing oracle on `m` for the statement `x`, from the sampled
challenge `e` and simulator randomness `s`: an accepted simulated transcript is
answered and programmed by `signOutOf`, a rejected one is answered `none`. -/
def simSignOut (x : P.Stmt) (t : Tables P M) (b : Bool) (m : M) (e : P.Ch) (s : P.SimRand) :
    Answer P × (Tables P M × Bool) :=
  if P.accept (P.simulate x e s).2 then signOutOf t b m (P.simulate x e s) e
  else (.inr none, ({ t with signed := t.signed ++ [m] }, b))

/-- A uniform challenge followed by an independent uniform value of `β`, mapped
by `F`. -/
noncomputable def sampleCh {β γ : Type} [Fintype β] [Nonempty β] (F : P.Ch → β → γ) : PMF γ :=
  (PMF.uniformOfFintype P.Ch).bind fun e => (PMF.uniformOfFintype β).map fun y => F e y

/-- The real oracle for the pair `(x, w)`. -/
noncomputable def realStep (xw : P.Stmt × P.Wit) (s : Tables P M × Bool) :
    Query P M → Step (Answer P) (Tables P M × Bool) P.Ch
  | .inl k => realHashStep s.1 s.2 k
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

/-! ## Transitions -/

section Transitions

variable {α : Type}

omit [DecidableEq M] in
theorem sampleCh_bind {β γ δ : Type} [Fintype β] [Nonempty β] (F : P.Ch → β → γ)
    (g : γ → PMF δ) :
    (sampleCh F).bind g = (PMF.uniformOfFintype P.Ch).bind fun e =>
      (PMF.uniformOfFintype β).bind fun y => g (F e y) := by
  simp only [sampleCh, PMF.bind_bind, PMF.bind_map, Function.comp_def]

omit [DecidableEq M] in
theorem mem_support_sampleCh {β γ : Type} [Fintype β] [Nonempty β] {F : P.Ch → β → γ}
    {y : γ} (hy : y ∈ (sampleCh F).support) : ∃ e b, y = F e b := by
  simp only [sampleCh, PMF.mem_support_bind_iff, PMF.support_map, Set.mem_image] at hy
  obtain ⟨e, _, b, _, rfl⟩ := hy
  exact ⟨e, b, rfl⟩

theorem realStep_flag (xw : P.Stmt × P.Wit) (t : Tables P M) (d : Query P M)
    (x : Answer P × (Tables P M × Bool))
    (hx : x ∈ (toOracle (realStep xw) (t, true) d).support) : x.2.2 = true := by
  cases d with
  | inl k =>
    simp only [toOracle, realStep, realHashStep] at hx
    cases hl : t.lookup k with
    | some e =>
      simp only [hl, Step.toPMF, PMF.support_pure, Set.mem_singleton_iff] at hx
      subst hx; rfl
    | none =>
      cases hr : lookupIn t.rej k with
      | some e =>
        simp only [hl, hr, Step.toPMF, PMF.support_pure, Set.mem_singleton_iff] at hx
        subst hx; rfl
      | none =>
        simp only [hl, hr, Step.toPMF, PMF.support_map, Set.mem_image] at hx
        obtain ⟨e, _, rfl⟩ := hx
        rfl
  | inr m =>
    simp only [toOracle, realStep, Step.toPMF] at hx
    obtain ⟨e, r, rfl⟩ := mem_support_sampleCh hx
    unfold realSignOut
    split
    · rfl
    · split <;> rfl

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
    simp only [toOracle, simStep, Step.toPMF] at hx
    obtain ⟨e, s, rfl⟩ := mem_support_sampleCh hx
    unfold simSignOut signOutOf
    split
    · split <;> rfl
    · rfl

end Transitions

/-! ## Tables grow along a real run -/

section Grow

variable {α : Type}

/-- `t'` extends `t`: every entry list of `t` is a prefix of the one of `t'`. -/
def Tables.Le (t t' : Tables P M) : Prop :=
  t.prog <+: t'.prog ∧ t.hash <+: t'.hash ∧ t.rej <+: t'.rej

omit [DecidableEq M] in
theorem Tables.Le.refl (t : Tables P M) : t.Le t :=
  ⟨List.prefix_refl _, List.prefix_refl _, List.prefix_refl _⟩

omit [DecidableEq M] in
theorem Tables.Le.trans {t t' t'' : Tables P M} (h : t.Le t') (h' : t'.Le t'') : t.Le t'' :=
  ⟨h.1.trans h'.1, h.2.1.trans h'.2.1, h.2.2.trans h'.2.2⟩

omit [DecidableEq M] in
theorem Tables.mem_keys {t : Tables P M} {k : P.Com × M} :
    k ∈ t.keys ↔ ∃ p, (p ∈ t.prog ∨ p ∈ t.hash ∨ p ∈ t.rej) ∧ p.1 = k := by
  simp only [Tables.keys, List.mem_map, List.mem_append]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, by tauto, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, by tauto, rfl⟩

omit [DecidableEq M] in
theorem Tables.Le.keys_subset {t t' : Tables P M} (h : t.Le t') {k : P.Com × M}
    (hk : k ∈ t.keys) : k ∈ t'.keys := by
  obtain ⟨p, hp, rfl⟩ := Tables.mem_keys.mp hk
  refine Tables.mem_keys.mpr ⟨p, ?_, rfl⟩
  rcases hp with hp | hp | hp
  · exact Or.inl (h.1.subset hp)
  · exact Or.inr (Or.inl (h.2.1.subset hp))
  · exact Or.inr (Or.inr (h.2.2.subset hp))

omit [DecidableEq M] in
theorem Tables.length_keys (t : Tables P M) : t.keys.length = t.size := by
  simp [Tables.keys, Tables.size, Nat.add_assoc]

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

theorem lookupAll_isSome_mem {t : Tables P M} {k : P.Com × M} (h : (t.lookupAll k).isSome) :
    k ∈ t.keys := by
  unfold Tables.lookupAll at h
  unfold Tables.keys
  rw [List.map_append, List.mem_append]
  cases hl : t.lookup k with
  | some e => exact Or.inl (lookup_isSome_mem (by simp [hl]))
  | none =>
    simp only [hl, Option.none_or] at h
    exact Or.inr (lookupIn_isSome_mem h)

theorem lookupIn_nil (k : P.Com × M) : lookupIn ([] : List ((P.Com × M) × P.Ch)) k = none := by
  simp [lookupIn, findKey]

theorem lookupIn_cons_of_ne (ent : (P.Com × M) × P.Ch) (l : List ((P.Com × M) × P.Ch))
    {k : P.Com × M} (hk : k ≠ ent.1) : lookupIn (ent :: l) k = lookupIn l k := by
  unfold lookupIn findKey
  rw [List.findIdx?_cons]
  have hne : decide (ent.1 = k) = false := decide_eq_false fun h => hk h.symm
  rw [hne]
  cases l.findIdx? (fun p => decide (p.1 = k)) <;> simp

theorem lookupAll_addRej_of_ne (ent : (P.Com × M) × P.Ch) (t : Tables P M) {k : P.Com × M}
    (hk : k ≠ ent.1) : (t.addRej ent).lookupAll k = t.lookupAll k := by
  unfold Tables.lookupAll
  rw [show (t.addRej ent).rej = ent :: t.rej from rfl, lookupIn_cons_of_ne ent t.rej hk]
  rfl

/-- A hash query at a point other than `ent.1` commutes with adding `ent` to the
entries of rejected attempts. -/
theorem realStep_addRej_inl (xw : P.Stmt × P.Wit) (ent : (P.Com × M) × P.Ch) (t : Tables P M)
    (b : Bool) (k : P.Com × M) (hk : k ≠ ent.1) :
    toOracle (realStep xw) (t.addRej ent, b) (.inl k) =
      (toOracle (realStep xw) (t, b) (.inl k)).map
        (Prod.map id (Prod.map (Tables.addRej ent) id)) := by
  simp only [toOracle, realStep, realHashStep]
  rw [show (t.addRej ent).lookup k = t.lookup k from rfl,
    show lookupIn (t.addRej ent).rej k = lookupIn t.rej k from lookupIn_cons_of_ne ent t.rej hk]
  cases t.lookup k with
  | some e => simp only [Step.toPMF, PMF.pure_map]; rfl
  | none =>
    cases lookupIn t.rej k with
    | some e => simp only [Step.toPMF, PMF.pure_map]; rfl
    | none => simp only [Step.toPMF, PMF.map_comp]; rfl

/-- A signing attempt whose point is not `ent.1` commutes with adding `ent` to the
entries of rejected attempts. -/
theorem realSignOut_addRej (ent : (P.Com × M) × P.Ch) (x : P.Stmt) (w : P.Wit) (t : Tables P M)
    (b : Bool) (m : M) (e : P.Ch) (r : P.Rand) (hk : (P.commit x w r, m) ≠ ent.1) :
    realSignOut x w (t.addRej ent) b m e r =
      Prod.map id (Prod.map (Tables.addRej ent) id) (realSignOut x w t b m e r) := by
  unfold realSignOut
  rw [lookupAll_addRej_of_ne ent t hk]
  cases t.lookupAll (P.commit x w r, m) with
  | some e' => rfl
  | none =>
    dsimp only
    split_ifs <;> rfl

/-- Every real transition extends the tables by at most one entry. -/
theorem realStep_support (xw : P.Stmt × P.Wit) (s : Tables P M × Bool) (d : Query P M)
    (o : Answer P × (Tables P M × Bool)) (ho : o ∈ (toOracle (realStep xw) s d).support) :
    s.1.Le o.2.1 ∧ o.2.1.size ≤ s.1.size + 1 := by
  obtain ⟨t, b⟩ := s
  cases d with
  | inl k =>
    simp only [toOracle, realStep, realHashStep] at ho
    cases hl : t.lookup k with
    | some e =>
      simp only [hl, Step.toPMF, PMF.support_pure, Set.mem_singleton_iff] at ho
      subst ho
      exact ⟨Tables.Le.refl _, Nat.le_succ _⟩
    | none =>
      cases hr : lookupIn t.rej k with
      | some e =>
        simp only [hl, hr, Step.toPMF, PMF.support_pure, Set.mem_singleton_iff] at ho
        subst ho
        exact ⟨⟨List.prefix_refl _, List.prefix_append _ _, List.prefix_refl _⟩,
          by simp [Tables.size]; omega⟩
      | none =>
        simp only [hl, hr, Step.toPMF, PMF.support_map, Set.mem_image] at ho
        obtain ⟨e, _, rfl⟩ := ho
        exact ⟨⟨List.prefix_refl _, List.prefix_append _ _, List.prefix_refl _⟩,
          by simp [Tables.size]; omega⟩
  | inr m =>
    simp only [toOracle, realStep, Step.toPMF] at ho
    obtain ⟨e, r, rfl⟩ := mem_support_sampleCh ho
    unfold realSignOut
    split
    · exact ⟨Tables.Le.refl _, by simp [Tables.size]⟩
    · split
      · exact ⟨⟨List.prefix_append _ _, List.prefix_refl _, List.prefix_refl _⟩,
          by simp [Tables.size]; omega⟩
      · exact ⟨⟨List.prefix_refl _, List.prefix_refl _, List.prefix_append _ _⟩,
          by simp [Tables.size]; omega⟩

/-- The point of a hash query is defined after the real transition. -/
theorem realStep_key_inl (xw : P.Stmt × P.Wit) (s : Tables P M × Bool) (k : P.Com × M)
    (o : Answer P × (Tables P M × Bool))
    (ho : o ∈ (toOracle (realStep xw) s (.inl k)).support) : k ∈ o.2.1.keys := by
  obtain ⟨t, b⟩ := s
  simp only [toOracle, realStep, realHashStep] at ho
  have happ : ∀ e : P.Ch, k ∈ ({ t with hash := t.hash ++ [(k, e)] } : Tables P M).keys :=
    fun e => Tables.mem_keys.mpr ⟨(k, e), Or.inr (Or.inl (by simp)), rfl⟩
  cases hl : t.lookup k with
  | some e =>
    simp only [hl, Step.toPMF, PMF.support_pure, Set.mem_singleton_iff] at ho
    subst ho
    have := lookup_isSome_mem (show (t.lookup k).isSome by rw [hl]; rfl)
    simp only [Tables.keys, List.map_append, List.mem_append] at this ⊢
    exact Or.inl this
  | none =>
    cases hr : lookupIn t.rej k with
    | some e =>
      simp only [hl, hr, Step.toPMF, PMF.support_pure, Set.mem_singleton_iff] at ho
      subst ho
      exact happ e
    | none =>
      simp only [hl, hr, Step.toPMF, PMF.support_map, Set.mem_image] at ho
      obtain ⟨e, _, rfl⟩ := ho
      exact happ e

/-- The point of a signing attempt is defined after the real transition. -/
theorem realSignOut_key (x : P.Stmt) (w : P.Wit) (t : Tables P M) (b : Bool) (m : M) (e : P.Ch)
    (r : P.Rand) : (P.commit x w r, m) ∈ (realSignOut x w t b m e r).2.1.keys := by
  unfold realSignOut
  split
  · next e' hl =>
    exact lookupAll_isSome_mem (show (t.lookupAll _).isSome by rw [hl]; rfl)
  · split
    · exact Tables.mem_keys.mpr ⟨((P.commit x w r, m), e), Or.inl (by simp), rfl⟩
    · exact Tables.mem_keys.mpr ⟨((P.commit x w r, m), e), Or.inr (Or.inr (by simp)), rfl⟩

theorem run_real_support_le (xw : P.Stmt × P.Wit) (A : OracleAdv (Query P M) (Answer P) α)
    (s : Tables P M × Bool) (y : α × (Tables P M × Bool))
    (hy : y ∈ (OracleAdv.run (toOracle (realStep xw)) A s).support) : s.1.Le y.2.1 := by
  induction A generalizing s with
  | ret a =>
    rw [OracleAdv.run_ret, PMF.support_pure, Set.mem_singleton_iff] at hy
    subst hy
    exact Tables.Le.refl _
  | rand p k ih =>
    rw [OracleAdv.run_rand, PMF.mem_support_bind_iff] at hy
    obtain ⟨b, _, hb⟩ := hy
    exact ih b s hb
  | query d k ih =>
    rw [OracleAdv.run_query, PMF.mem_support_bind_iff] at hy
    obtain ⟨o, ho, hy⟩ := hy
    exact (realStep_support xw s d o ho).1.trans (ih o.1 o.2 hy)

theorem run_real_support_flag (xw : P.Stmt × P.Wit) (A : OracleAdv (Query P M) (Answer P) α)
    (s : Tables P M × Bool) (y : α × (Tables P M × Bool))
    (hy : y ∈ (OracleAdv.run (toOracle (realStep xw)) A s).support) (hs : s.2 = true) :
    y.2.2 = true := by
  induction A generalizing s with
  | ret a =>
    rw [OracleAdv.run_ret, PMF.support_pure, Set.mem_singleton_iff] at hy
    subst hy
    exact hs
  | rand p k ih =>
    rw [OracleAdv.run_rand, PMF.mem_support_bind_iff] at hy
    obtain ⟨b, _, hb⟩ := hy
    exact ih b s hb hs
  | query d k ih =>
    rw [OracleAdv.run_query, PMF.mem_support_bind_iff] at hy
    obtain ⟨o, ho, hy⟩ := hy
    obtain ⟨t, b⟩ := s
    dsimp only at hs
    subst hs
    exact ih o.1 o.2 hy (realStep_flag xw t d o ho)

theorem run_real_support_size (xw : P.Stmt × P.Wit) (A : OracleAdv (Query P M) (Answer P) α)
    (h q : ℕ) (hA : IsQueryBound₂ A h q) (s : Tables P M × Bool) (y : α × (Tables P M × Bool))
    (hy : y ∈ (OracleAdv.run (toOracle (realStep xw)) A s).support) :
    y.2.1.size ≤ s.1.size + h + q := by
  induction A generalizing h q s with
  | ret a =>
    rw [OracleAdv.run_ret, PMF.support_pure, Set.mem_singleton_iff] at hy
    subst hy
    exact (Nat.le_add_right _ h).trans (Nat.le_add_right _ q)
  | rand p k ih =>
    rw [OracleAdv.run_rand, PMF.mem_support_bind_iff] at hy
    obtain ⟨b, _, hb⟩ := hy
    exact ih b h q (hA b) s hb
  | query d k ih =>
    rw [OracleAdv.run_query, PMF.mem_support_bind_iff] at hy
    obtain ⟨o, ho, hy⟩ := hy
    have hs := (realStep_support xw s d o ho).2
    cases d with
    | inl key =>
      cases h with
      | zero => exact hA.elim
      | succ h =>
        have := ih o.1 h q (hA o.1) o.2 hy
        omega
    | inr m =>
      cases q with
      | zero => exact hA.elim
      | succ q =>
        have := ih o.1 h q (hA o.1) o.2 hy
        omega

end Grow

/-! ## The flag is set with small probability -/

section Flag

variable {α : Type}

omit [DecidableEq M] in
/-- Union bound: the probability that the commitment is the first component of
some point of a list is at most the length of the list times `γ`. -/
theorem prob_commit_mem_le {γ : ℝ≥0∞} (x : P.Stmt) (w : P.Wit) (hγ : P.CommitBoundAt x w γ)
    (m : M) (l : List (P.Com × M)) :
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
          (MeasureTheory.measure_union_le _ _).trans (add_le_add (hγ k.1) ih)
      _ = _ := by simp [List.length_cons, add_mul, add_comm]

/-- The probability that a real commitment collides with a point of a hash or
accepted signing entry is at most `(|hash| + |prog|)·γ`. -/
theorem prob_collision_le {γ : ℝ≥0∞} (x : P.Stmt) (w : P.Wit) (hγ : P.CommitBoundAt x w γ)
    (t : Tables P M) (m : M) :
    (PMF.uniformOfFintype P.Rand).toOuterMeasure {r | (t.lookup (P.commit x w r, m)).isSome} ≤
      ((t.hash.length + t.prog.length : ℕ) : ℝ≥0∞) * γ := by
  refine (MeasureTheory.measure_mono fun r hr => lookup_isSome_mem hr).trans
    ((prob_commit_mem_le x w hγ m _).trans (le_of_eq ?_))
  simp [Nat.add_comm]

theorem toOuterMeasure_eq_one_of_support {β : Type} (p : PMF β) (S : Set β)
    (h : ∀ y ∈ p.support, y ∈ S) : p.toOuterMeasure S = 1 :=
  (PMF.toOuterMeasure_apply_eq_one_iff p S).mpr h

/-- A real run from tables in which `k₀` is defined defines `k₀` at the end. -/
theorem run_real_keys_eq_one (xw : P.Stmt × P.Wit) (A : OracleAdv (Query P M) (Answer P) α)
    (s : Tables P M × Bool) (k₀ : P.Com × M) (hk : k₀ ∈ s.1.keys) (E : Set (α × (Tables P M × Bool)))
    (hE : ∀ y, k₀ ∈ y.2.1.keys → y ∈ E) :
    (OracleAdv.run (toOracle (realStep xw)) A s).toOuterMeasure E = 1 :=
  toOuterMeasure_eq_one_of_support _ _ fun y hy =>
    hE y ((run_real_support_le xw A s y hy).keys_subset hk)

/-- **An entry of a rejected attempt changes the flag only where it is reached.**
For the entry `ent`, the probability that a real run from `t` with `ent` added to
the entries of rejected attempts sets the flag is at most the probability that the
run from `t` sets the flag or ends with the point of `ent` defined. -/
theorem run_real_addRej_flag_le (xw : P.Stmt × P.Wit) (ent : (P.Com × M) × P.Ch)
    (A : OracleAdv (Query P M) (Answer P) α) (t : Tables P M) (b : Bool) :
    (OracleAdv.run (toOracle (realStep xw)) A (t.addRej ent, b)).toOuterMeasure
        {y | y.2.2 = true} ≤
      (OracleAdv.run (toOracle (realStep xw)) A (t, b)).toOuterMeasure
        {y | y.2.2 = true ∨ ent.1 ∈ y.2.1.keys} := by
  induction A generalizing t b with
  | ret a =>
    simp only [OracleAdv.run_ret, PMF.toOuterMeasure_pure_apply, Set.mem_ofPred_eq]
    split_ifs with h1 h2 <;> simp_all
  | rand p k ih =>
    simp only [OracleAdv.run_rand, PMF.toOuterMeasure_bind_apply]
    exact ENNReal.tsum_le_tsum fun c => mul_le_mul_right (ih c t b) _
  | query d k ih =>
    by_cases hb : b = true ∨ ent.1 ∈ t.keys
    · refine (toOuterMeasure_le_one _ _).trans (le_of_eq ?_)
      refine (toOuterMeasure_eq_one_of_support _ _ fun y hy => ?_).symm
      rcases hb with hb | hk
      · exact Or.inl (run_real_support_flag xw _ (t, b) y hy hb)
      · exact Or.inr ((run_real_support_le xw _ (t, b) y hy).keys_subset hk)
    simp only [not_or, Bool.not_eq_true] at hb
    obtain ⟨rfl, hk⟩ := hb
    cases d with
    | inl key =>
      by_cases hke : key = ent.1
      · subst hke
        refine (toOuterMeasure_le_one _ _).trans (le_of_eq ?_)
        refine (toOuterMeasure_eq_one_of_support _ _ fun y hy => ?_).symm
        rw [OracleAdv.run_query, PMF.mem_support_bind_iff] at hy
        obtain ⟨o, ho, hy⟩ := hy
        exact Or.inr ((run_real_support_le xw _ o.2 y hy).keys_subset
          (realStep_key_inl xw _ _ o ho))
      · rw [OracleAdv.run_query, OracleAdv.run_query, realStep_addRej_inl xw ent t false key hke,
          PMF.bind_map, PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
        exact ENNReal.tsum_le_tsum fun o => mul_le_mul_right (ih o.1 o.2.1 o.2.2) _
    | inr m =>
      simp only [OracleAdv.run_query, toOracle, realStep, Step.toPMF, sampleCh_bind,
        PMF.toOuterMeasure_bind_apply]
      refine ENNReal.tsum_le_tsum fun e => mul_le_mul_right
        (ENNReal.tsum_le_tsum fun r => mul_le_mul_right ?_ _) _
      by_cases hc : (P.commit xw.1 xw.2 r, m) = ent.1
      · refine (toOuterMeasure_le_one _ _).trans (le_of_eq
          (run_real_keys_eq_one xw _ _ ent.1 ?_ _ fun y hy => Or.inr hy).symm)
        rw [← hc]
        exact realSignOut_key _ _ _ _ _ _ _
      · rw [realSignOut_addRej ent xw.1 xw.2 t false m e r hc]
        exact ih _ _ _

/-- The expectation, over uniform prover randomness, of the probability that the
commitment is a point defined at the end of a real run is at most `(L + h + q)·γ`,
for a run from tables with `L` entries asking at most `h` hash and `q` signing
queries. -/
theorem tsum_commit_keys_le {γ : ℝ≥0∞} (xw : P.Stmt × P.Wit) (hγ : P.CommitBoundAt xw.1 xw.2 γ)
    (A : OracleAdv (Query P M) (Answer P) α) (h q : ℕ) (hA : IsQueryBound₂ A h q)
    (s : Tables P M × Bool) (m : M) :
    ∑' r, PMF.uniformOfFintype P.Rand r *
        (OracleAdv.run (toOracle (realStep xw)) A s).toOuterMeasure
          {y | (P.commit xw.1 xw.2 r, m) ∈ y.2.1.keys} ≤
      ((s.1.size + h + q : ℕ) : ℝ≥0∞) * γ := by
  set p := OracleAdv.run (toOracle (realStep xw)) A s with hp
  simp only [PMF.toOuterMeasure_apply]
  calc ∑' r, PMF.uniformOfFintype P.Rand r *
        ∑' y, Set.indicator {y | (P.commit xw.1 xw.2 r, m) ∈ y.2.1.keys} p y
      = ∑' y, p y * ∑' r, Set.indicator {r | (P.commit xw.1 xw.2 r, m) ∈ y.2.1.keys}
          (PMF.uniformOfFintype P.Rand) r := by
        simp only [← ENNReal.tsum_mul_left]
        rw [ENNReal.tsum_comm]
        refine tsum_congr fun y => tsum_congr fun r => ?_
        simp only [Set.indicator_apply, Set.mem_ofPred_eq]
        split_ifs <;> simp [mul_comm]
    _ ≤ ∑' y, p y * (((s.1.size + h + q : ℕ) : ℝ≥0∞) * γ) := by
        refine ENNReal.tsum_le_tsum fun y => ?_
        by_cases hy : y ∈ p.support
        · refine mul_le_mul_right ?_ _
          rw [← PMF.toOuterMeasure_apply]
          refine (prob_commit_mem_le xw.1 xw.2 hγ m y.2.1.keys).trans ?_
          gcongr
          rw [Tables.length_keys]
          exact_mod_cast run_real_support_size xw A h q hA s y hy
        · simp [(PMF.apply_eq_zero_iff _ _).mpr hy]
    _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- One signing attempt in the induction of `run_real_flag_le`: the probability
that the rest of the run sets the flag is at most the bound for the tables after
an accepted attempt plus the probability that the commitment is defined at the end
of the run after a rejected attempt. -/
theorem flag_sign_term_le (xw : P.Stmt × P.Wit) {γ : ℝ≥0∞}
    (k : Answer P → OracleAdv (Query P M) (Answer P) α) (h q : ℕ) (t : Tables P M)
    (ht : t.rej = []) (m : M) (e : P.Ch) (r : P.Rand)
    (ih : ∀ c (t' : Tables P M), t'.rej = [] →
      (OracleAdv.run (toOracle (realStep xw)) (k c) (t', false)).toOuterMeasure
        {y | y.2.2 = true} ≤ ((q * (t'.hash.length + t'.prog.length + h + q) : ℕ) : ℝ≥0∞) * γ) :
    (OracleAdv.run (toOracle (realStep xw)) (k (realSignOut xw.1 xw.2 t false m e r).1)
        (realSignOut xw.1 xw.2 t false m e r).2).toOuterMeasure {y | y.2.2 = true} ≤
      ((q * (t.hash.length + t.prog.length + 1 + h + q) : ℕ) : ℝ≥0∞) * γ +
        (OracleAdv.run (toOracle (realStep xw)) (k (.inr none))
          ({ t with signed := t.signed ++ [m] }, false)).toOuterMeasure
          {y | (P.commit xw.1 xw.2 r, m) ∈ y.2.1.keys} := by
  obtain ⟨hash, prog, signed, rej⟩ := t
  dsimp only at ht
  subst ht
  unfold realSignOut
  split
  · next e' hl =>
    refine (toOuterMeasure_le_one _ _).trans (le_trans (le_of_eq ?_) le_add_self)
    refine (run_real_keys_eq_one xw _ _ _ ?_ _ fun y hy => hy).symm
    exact lookupAll_isSome_mem (t := ⟨hash, prog, signed, []⟩) (by rw [hl]; rfl)
  · split
    · refine (ih _ _ rfl).trans (le_trans (le_of_eq ?_) le_self_add)
      congr 3
      simp only [List.length_append, List.length_singleton]
      omega
    · refine (run_real_addRej_flag_le xw ((P.commit xw.1 xw.2 r, m), e) _
        ⟨hash, prog, signed ++ [m], []⟩ false).trans ?_
      refine (MeasureTheory.measure_mono (fun y hy => hy)).trans
        ((MeasureTheory.measure_union_le _ _).trans (add_le_add ?_ le_rfl))
      refine (ih _ _ rfl).trans (mul_le_mul_of_nonneg_right ?_ zero_le)
      exact_mod_cast Nat.mul_le_mul_left q (by dsimp only; omega)

/-- **Collision bound.** For a pair `(x, w)` with commitment bound `γ`, from tables
with no entry of a rejected attempt, with `L` entries and the flag cleared, a run
of the real oracles asking at most `h` hash and `q` signing queries sets the flag
with probability at most `q·(L + h + q)·γ`. -/
theorem run_real_flag_le {γ : ℝ≥0∞} (xw : P.Stmt × P.Wit) (hγ : P.CommitBoundAt xw.1 xw.2 γ)
    (A : OracleAdv (Query P M) (Answer P) α) (h q : ℕ) (hA : IsQueryBound₂ A h q)
    (t : Tables P M) (ht : t.rej = []) :
    (OracleAdv.run (toOracle (realStep xw)) A (t, false)).toOuterMeasure {y | y.2.2 = true} ≤
      ((q * (t.hash.length + t.prog.length + h + q) : ℕ) : ℝ≥0∞) * γ := by
  induction A generalizing h q t with
  | ret a => simp [PMF.toOuterMeasure_pure_apply]
  | rand p k ih =>
    rw [OracleAdv.run_rand, PMF.toOuterMeasure_bind_apply]
    calc ∑' b, p b * (OracleAdv.run (toOracle (realStep xw)) (k b) (t, false)).toOuterMeasure _
        ≤ ∑' b, p b * (((q * (t.hash.length + t.prog.length + h + q) : ℕ) : ℝ≥0∞) * γ) :=
          ENNReal.tsum_le_tsum fun b => mul_le_mul_right (ih b h q (hA b) t ht) _
      _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  | query d k ih =>
    rw [OracleAdv.run_query]
    cases d with
    | inl key =>
      cases h with
      | zero => exact hA.elim
      | succ h =>
      have hk : ∀ r, IsQueryBound₂ (k r) h q := hA
      simp only [toOracle, realStep, realHashStep]
      cases hl : t.lookup key with
      | some e =>
        simp only [Step.toPMF, PMF.pure_bind]
        refine (ih _ h q (hk _) t ht).trans (mul_le_mul_of_nonneg_right ?_ zero_le)
        exact_mod_cast Nat.mul_le_mul_left q (by omega)
      | none =>
        have hr : lookupIn t.rej key = none := by rw [ht]; exact lookupIn_nil key
        simp only [hr, Step.toPMF, PMF.bind_map, Function.comp_def, PMF.toOuterMeasure_bind_apply]
        calc ∑' e, PMF.uniformOfFintype P.Ch e * (OracleAdv.run (toOracle (realStep xw))
              (k (.inl e)) ({ t with hash := t.hash ++ [(key, e)] }, false)).toOuterMeasure _
            ≤ ∑' e, PMF.uniformOfFintype P.Ch e *
              (((q * (t.hash.length + t.prog.length + (h + 1) + q) : ℕ) : ℝ≥0∞) * γ) := by
              refine ENNReal.tsum_le_tsum fun e => mul_le_mul_right ?_ _
              refine (ih _ h q (hk _) { t with hash := t.hash ++ [(key, e)] } ht).trans
                (le_of_eq ?_)
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
      set V : P.Rand → ℝ≥0∞ := fun r =>
        (OracleAdv.run (toOracle (realStep xw)) (k (.inr none))
          ({ t with signed := t.signed ++ [m] }, false)).toOuterMeasure
          {y | (P.commit xw.1 xw.2 r, m) ∈ y.2.1.keys} with hV
      have hterm := fun e r => flag_sign_term_le xw k h q t ht m e r
        (fun c t' ht' => ih c h q (hk c) t' ht')
      have hsum := tsum_commit_keys_le xw hγ (k (.inr none)) h q (hk _)
        ({ t with signed := t.signed ++ [m] }, false) m
      simp only [toOracle, realStep, Step.toPMF, sampleCh_bind, PMF.toOuterMeasure_bind_apply]
      calc _ ≤ ∑' e, PMF.uniformOfFintype P.Ch e *
            ∑' r, PMF.uniformOfFintype P.Rand r * (B + V r) :=
            ENNReal.tsum_le_tsum fun e => mul_le_mul_right
              (ENNReal.tsum_le_tsum fun r => mul_le_mul_right (hterm e r) _) _
        _ = B + ∑' r, PMF.uniformOfFintype P.Rand r * V r := by
            simp only [mul_add]
            rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul,
              ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
        _ ≤ B + ((({ t with signed := t.signed ++ [m] } : Tables P M).size + h + q : ℕ) :
              ℝ≥0∞) * γ := add_le_add_right hsum _
        _ ≤ _ := by
            rw [hB, ← add_mul]
            gcongr
            rw [← Nat.cast_add, Nat.cast_le]
            simp only [Tables.size, ht, List.length_nil, add_zero]
            have : L + 1 + h + q = L + h + (q + 1) := by omega
            rw [this, Nat.succ_mul]
            omega

end Flag

/-! ## The game as an average over generated pairs -/

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

end Game

end CatCrypt.Crypto.FiatShamirROM
