/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OracleForkingLemma

/-!
# EUF-CMA security of Fiat–Shamir signatures in the random-oracle model: the game

A multi-round public-coin protocol `G : Protocol` made non-interactive by a random
oracle `H : G.Key → G.Ch` with uniform values. Several random oracles are one
oracle on a sum type of points; an oracle whose values are shorter than `G.Ch`
decodes a uniform value of `G.Ch`. A signing attempt on the message `m` for the
pair `(x, w)` from the randomness `r` defines `G.μ` oracle entries: the entry `i`
is at the point `G.key x w m r v i` with value `v i = H(G.key x w m r v i)`, and
the point reads only the values `v j` with `j < i`. An entry is public
(`G.pub x w m r v i`) when the answer reveals its point, and hidden otherwise; the
answer is `G.sign x w m r v`, a signature or nothing. The simulator
`G.simulate x m v s` computes the public entries and the answer from the statement
and the values `v`. The verifier of a signature `σ` on `m` reads `H` at `G.V`
points, the next one `G.vkey x m σ vs` from the values `vs` read so far, and
decides with `G.verify x m σ vs`.

The EUF-CMA game samples `(x, w)` from the generator `G.gen` and runs an adaptive
oracle adversary (`OracleAdv`) on `x` with hash queries `inl k` and signing queries
`inr m`, at most `qH` and `qS` of them on every path
(`OracleForking.IsQueryBound₂`). The challenger keeps the oracle state
`G.Tables × Bool`:

* `hash` — the random-oracle entries created by hash queries, in creation order;
* `prog` — the public entries created by signing attempts;
* `signed` — the messages submitted to the signing oracle;
* `rej` — the hidden entries created by signing attempts;
* the flag — set when a query needs the oracle value at the point of a hidden
  entry, or when a signing attempt needs the oracle value at a point already
  defined.

A hash query returns the recorded value of its point or samples a fresh uniform
value and records it. The real signing oracle samples the values `e` and the
randomness `r`; each entry takes the recorded value of its point when there is
one (setting the flag) and its value in `e` otherwise; the new entries go to
`prog` and `rej`. The simulated signing oracle knows only `x`: it samples `e` and
`s`, and records the public entries of `G.simulate x m e s` in `prog`, setting the
flag for an entry whose point is already defined. At the end the challenger reads
the verifier's points for the forgery `(m*, σ*)`, and the adversary wins when the
verifier accepts and `m*` was never signed.

A Σ-protocol `P : Sigma` with explicit prover randomness, simulator randomness and
an acceptance test on responses is the instance `P.toProtocol M` with one entry
at the point `(P.commit x w r, m)`, public when the response is accepted.

## Main definitions

* `Protocol` — a multi-round public-coin protocol with its random-oracle entries
* `Protocol.view`, `Protocol.guessView` — the view of an attempt (public entries and
  answer), and the view from which the point of an entry is guessed
* `Protocol.StatHVZKAt x w δ`, `Protocol.KeyBoundAt x w γ` — statistical HVZK on
  views, and the bound `γ` on guessing the point of an entry, at one pair
* `Sigma` — a Σ-protocol with explicit randomness, generator, extractor and
  acceptance test, and `Sigma.toProtocol P M`
* `Sigma.SpecialSound`, `Sigma.PerfectHVZK`, `Sigma.CommitBoundAt x w γ`,
  `Sigma.CommitBound γ`, `Sigma.Complete`, `Sigma.UniqueResp`, `Sigma.relGame B`,
  `Sigma.relAdvantage B`
* `realStep`, `simStep` — the real and simulated oracles
* `eufcmaGame A`, `eufcmaAdvantage A` — the EUF-CMA game and advantage
* `simGame A`, `simAdvantage A` — the game with the simulated signing oracle

## Main results

* `run_real_addRejs_flag_le` — hidden entries change the flag of a real run only
  when the run reaches one of their points
* `run_real_flag_le` — for a pair `(x, w)` with key bound `γ`, from tables with `L`
  entries and no hidden entry, a run with at most `h` hash and `q` signing queries
  sets the flag with probability at most `q·μ·(L + h + μ·q)·γ`

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

/-! ## Multi-round public-coin protocols -/

/-- A public-coin protocol made non-interactive by a random oracle from `Key` to
uniform values `Ch`, presented by the oracle entries of a signing attempt. An
attempt on the message `m` for the pair `(x, w)` with randomness `r` and oracle
values `v` defines `μ` entries, the entry `i` at the point `key x w m r v i` with
value `v i`; it is public when `pub x w m r v i` holds and hidden otherwise, and
the answer of the attempt is `sign x w m r v`. The simulator gives the public
entries and the answer from the statement and the values. The verifier of `σ` on
`m` reads the oracle at `V` points, each from the values read before. -/
structure Protocol : Type 1 where
  /-- Statements (public keys). -/
  Stmt : Type
  /-- Witnesses (secret keys). -/
  Wit : Type
  /-- Messages. -/
  Msg : Type
  /-- Points of the random oracle. -/
  Key : Type
  /-- Values of the random oracle. -/
  Ch : Type
  /-- Signatures. -/
  Sig : Type
  /-- Signing randomness. -/
  Rand : Type
  /-- Simulator randomness. -/
  SimRand : Type
  [finCh : Fintype Ch]
  [neCh : Nonempty Ch]
  [decCh : DecidableEq Ch]
  [decKey : DecidableEq Key]
  [decMsg : DecidableEq Msg]
  [finRand : Fintype Rand]
  [neRand : Nonempty Rand]
  [finSimRand : Fintype SimRand]
  [neSimRand : Nonempty SimRand]
  /-- The generator of statement–witness pairs (key generation). -/
  gen : PMF (Stmt × Wit)
  /-- The number of oracle entries of a signing attempt. -/
  μ : ℕ
  /-- The point of entry `i` of an attempt, from the oracle values `v`. -/
  key : Stmt → Wit → Msg → Rand → (Fin μ → Ch) → Fin μ → Key
  /-- The point of entry `i` reads only the values of the entries before it. -/
  key_causal : ∀ x w m r (v v' : Fin μ → Ch) (i : Fin μ),
    (∀ j, j < i → v j = v' j) → key x w m r v i = key x w m r v' i
  /-- The entries of an attempt are at distinct points. -/
  key_inj : ∀ x w m r (v : Fin μ → Ch) (i j : Fin μ), key x w m r v i = key x w m r v j → i = j
  /-- Entry `i` is public. -/
  pub : Stmt → Wit → Msg → Rand → (Fin μ → Ch) → Fin μ → Bool
  /-- The answer of an attempt: a signature, or nothing. -/
  sign : Stmt → Wit → Msg → Rand → (Fin μ → Ch) → Option Sig
  /-- The simulator: the public entries and the answer from the values. -/
  simulate : Stmt → Msg → (Fin μ → Ch) → SimRand → List (Key × Ch) × Option Sig
  /-- The number of oracle points the verifier reads. -/
  V : ℕ
  /-- The next point the verifier reads, from the values read before. -/
  vkey : Stmt → Msg → Sig → List Ch → Key
  /-- The verifier on the values read at its points. -/
  verify : Stmt → Msg → Sig → List Ch → Bool

attribute [instance] Protocol.finCh Protocol.neCh Protocol.decCh Protocol.decKey
  Protocol.decMsg Protocol.finRand Protocol.neRand Protocol.finSimRand Protocol.neSimRand

namespace Protocol

variable (G : Protocol)

/-- The view of an attempt: its public entries and its answer. -/
abbrev View := List (G.Key × G.Ch) × Option G.Sig

/-- A query: `inl k` asks the random oracle at `k`, `inr m` asks for a signature
on `m`. -/
abbrev Query := G.Key ⊕ G.Msg

/-- An answer: `inl e` for a hash query, `inr a` for a signing attempt with answer
`a`. -/
abbrev Answer := G.Ch ⊕ Option G.Sig

/-- A forgery `(m, σ)`. -/
abbrev Forgery := G.Msg × G.Sig

/-- The challenger's tables. -/
structure Tables where
  /-- Random-oracle entries created by hash queries, oldest first. -/
  hash : List (G.Key × G.Ch)
  /-- Public entries created by signing attempts, oldest first. -/
  prog : List (G.Key × G.Ch)
  /-- Messages submitted to the signing oracle. -/
  signed : List G.Msg
  /-- Hidden entries created by signing attempts, oldest first. -/
  rej : List (G.Key × G.Ch)

/-- The public entries of an attempt with the values `e`. -/
def pubEntries (x : G.Stmt) (w : G.Wit) (m : G.Msg) (r : G.Rand) (e : Fin G.μ → G.Ch) :
    List (G.Key × G.Ch) :=
  ((List.finRange G.μ).filter (G.pub x w m r e)).map fun i => (G.key x w m r e i, e i)

/-- The hidden entries of an attempt with the values `e`. -/
def hidEntries (x : G.Stmt) (w : G.Wit) (m : G.Msg) (r : G.Rand) (e : Fin G.μ → G.Ch) :
    List (G.Key × G.Ch) :=
  ((List.finRange G.μ).filter fun i => !G.pub x w m r e i).map fun i => (G.key x w m r e i, e i)

/-- The view of an attempt with the values `e`: its public entries and its answer. -/
def view (x : G.Stmt) (w : G.Wit) (m : G.Msg) (r : G.Rand) (e : Fin G.μ → G.Ch) : G.View :=
  (G.pubEntries x w m r e, G.sign x w m r e)

/-- The view that determines the guess of the point of entry `i`: the view of the
attempt when the entry is hidden, and the empty view when it is public. -/
def guessView (x : G.Stmt) (w : G.Wit) (m : G.Msg) (r : G.Rand) (e : Fin G.μ → G.Ch)
    (i : Fin G.μ) : G.View :=
  if G.pub x w m r e i then ([], none) else G.view x w m r e

/-- **Key bound at one pair.** For the pair `(x, w)`, every message, all values `e`
and every entry `i`, a guess of the point of the entry from `guessView` (the view of
the attempt for a hidden entry, nothing for a public one) by any randomized guesser
`Q` succeeds with probability at most `γ` over uniform randomness. -/
def KeyBoundAt (x : G.Stmt) (w : G.Wit) (γ : ℝ≥0∞) : Prop :=
  ∀ (m : G.Msg) (e : Fin G.μ → G.Ch) (i : Fin G.μ) (Q : G.View → PMF G.Key),
    ∑' r, PMF.uniformOfFintype G.Rand r *
      Q (G.guessView x w m r e i) (G.key x w m r e i) ≤ γ

/-- **Statistical honest-verifier zero knowledge at one pair** with distance `δ`.
For the pair `(x, w)`, every message `m`, all values `e` and every test `g` with
values in `[0, 1]` on views, the expectation of `g` on the view of the attempt
under uniform randomness is at most its expectation on the simulator output under
uniform simulator randomness, plus `δ`. -/
def StatHVZKAt (x : G.Stmt) (w : G.Wit) (δ : ℝ≥0∞) : Prop :=
  ∀ (m : G.Msg) (e : Fin G.μ → G.Ch) (g : G.View → ℝ≥0∞), (∀ y, g y ≤ 1) →
    ∑' r, PMF.uniformOfFintype G.Rand r * g (G.view x w m r e) ≤
      ∑' s, PMF.uniformOfFintype G.SimRand s * g (G.simulate x m e s) + δ

end Protocol

/-! ## Σ-protocols as protocols with one entry -/

namespace Sigma

variable (P : Sigma) (M : Type) [DecidableEq M]

/-- The Fiat–Shamir signature scheme over `P` on messages `M`: one entry, at the
point `(P.commit x w r, m)` with the challenge `e` as value, public when the
response `z = P.respond x w r e` is accepted; the answer is `(P.commit x w r, z)`
when `z` is accepted and nothing otherwise. The simulator answers
`P.simulate x e s` and programs its point when its response is accepted. The
verifier reads `(a, m)` for the signature `(a, z)`. -/
@[reducible] def toProtocol : Protocol where
  Stmt := P.Stmt
  Wit := P.Wit
  Msg := M
  Key := P.Com × M
  Ch := P.Ch
  Sig := P.Com × P.Resp
  Rand := P.Rand
  SimRand := P.SimRand
  gen := P.gen
  μ := 1
  key x w m r _ _ := (P.commit x w r, m)
  key_causal _ _ _ _ _ _ _ _ := rfl
  key_inj _ _ _ _ _ i j _ := Subsingleton.elim i j
  pub x w _ r v _ := P.accept (P.respond x w r (v 0))
  sign x w _ r v :=
    if P.accept (P.respond x w r (v 0)) then some (P.commit x w r, P.respond x w r (v 0))
    else none
  simulate x m v s :=
    if P.accept (P.simulate x (v 0) s).2 then ([(((P.simulate x (v 0) s).1, m), v 0)],
      some (P.simulate x (v 0) s)) else ([], none)
  V := 1
  vkey _ m σ _ := (σ.1, m)
  verify x _ σ vs := match vs with
    | [e] => P.verify x σ.1 e σ.2
    | _ => false

@[simp] theorem toProtocol_μ : (P.toProtocol M).μ = 1 := rfl

@[simp] theorem toProtocol_V : (P.toProtocol M).V = 1 := rfl

end Sigma

variable (P : Sigma) (M : Type) [DecidableEq M]

/-- A query of the Fiat–Shamir game over `P`: `inl (a, m)` asks the random oracle
at `(a, m)`, `inr m` asks for a signature on `m`. -/
abbrev Query := (P.toProtocol M).Query

/-- An answer of the Fiat–Shamir game over `P`: `inl e` for a hash query;
`inr (some (a, z))` for an accepted signing attempt and `inr none` for a rejected
one. -/
abbrev Answer := P.Ch ⊕ Option (P.Com × P.Resp)

/-- A forgery `(m, (a, z))`. -/
abbrev Forgery := (P.toProtocol M).Forgery

/-- The challenger's tables of the Fiat–Shamir game over `P`. -/
abbrev Tables := (P.toProtocol M).Tables

variable {P M}

/-! ## Tables -/

section TablesOps

variable {K C : Type} [DecidableEq K]

/-- Position of the first entry at point `k`. -/
def findKey (l : List (K × C)) (k : K) : Option ℕ :=
  l.findIdx? fun p => decide (p.1 = k)

/-- Value of the first entry at point `k`. -/
def lookupIn (l : List (K × C)) (k : K) : Option C :=
  (findKey l k).bind fun i => l[i]?.map Prod.snd

end TablesOps

namespace Protocol

variable {G : Protocol}

/-- The empty tables. -/
def Tables.empty : G.Tables := ⟨[], [], [], []⟩

/-- The random-oracle value at `k` from the entries of hash queries and public
entries, if defined. -/
def Tables.lookup (t : G.Tables) (k : G.Key) : Option G.Ch :=
  (lookupIn t.prog k).or (lookupIn t.hash k)

/-- The random-oracle value at `k` from all entries, including the hidden ones. -/
def Tables.lookupAll (t : G.Tables) (k : G.Key) : Option G.Ch :=
  (t.lookup k).or (lookupIn t.rej k)

/-- The points at which the random oracle is defined. -/
def Tables.keys (t : G.Tables) : List G.Key :=
  (t.prog ++ t.hash ++ t.rej).map Prod.fst

/-- The number of entries. -/
def Tables.size (t : G.Tables) : ℕ :=
  t.prog.length + t.hash.length + t.rej.length

/-- The tables `t` with the entries `l` placed first among the hidden entries. -/
def Tables.addRejs (l : List (G.Key × G.Ch)) (t : G.Tables) : G.Tables :=
  { t with rej := l ++ t.rej }

end Protocol

open Protocol

/-! ## The values of a signing attempt -/

section Eff

variable {μ : ℕ} {K C : Type}

/-- The value of entry `i` of an attempt against the oracle `look`: the recorded
value at its point when there is one, and `e i` otherwise; the point reads the
values of the entries before `i`. -/
def effVal (look : K → Option C) (key : (Fin μ → C) → Fin μ → K) (e : Fin μ → C)
    (i : Fin μ) : C :=
  (look (key (fun j => if j < i then effVal look key e j else e j) i)).getD (e i)
termination_by i.val
decreasing_by exact ‹j < i›

/-- The values of the entries of an attempt against the oracle `look`. -/
def effVec (look : K → Option C) (key : (Fin μ → C) → Fin μ → K) (e : Fin μ → C) :
    Fin μ → C :=
  fun i => effVal look key e i

end Eff

/-! ## Oracles -/

section Oracles

variable {G : Protocol}

/-- A hash query of the simulated game: the recorded value of a hash or public
entry, or a fresh uniform value recorded in `hash`. -/
noncomputable def hashStep (t : G.Tables) (b : Bool) (k : G.Key) :
    Step G.Answer (G.Tables × Bool) G.Ch :=
  match t.lookup k with
  | some e => .plain (PMF.pure (.inl e, (t, b)))
  | none => .fresh fun e => (.inl e, ({ t with hash := t.hash ++ [(k, e)] }, b))

/-- A hash query of the real game: the recorded value of a hash or public entry;
the value of a hidden entry, copied to `hash` with the flag set; or a fresh uniform
value recorded in `hash`. -/
noncomputable def realHashStep (t : G.Tables) (b : Bool) (k : G.Key) :
    Step G.Answer (G.Tables × Bool) G.Ch :=
  match t.lookup k with
  | some e => .plain (PMF.pure (.inl e, (t, b)))
  | none =>
    match lookupIn t.rej k with
    | some e => .plain (PMF.pure (.inl e, ({ t with hash := t.hash ++ [(k, e)] }, true)))
    | none => .fresh fun e => (.inl e, ({ t with hash := t.hash ++ [(k, e)] }, b))

/-- The real signing oracle on `m` for the pair `(x, w)`, from the sampled values
`e` and randomness `r`. Each entry takes the recorded value at its point when there
is one and its value in `e` otherwise (`effVec`); the entries at undefined points
are recorded, the public ones in `prog` and the hidden ones in `rej`; the flag is
set when some point was defined. -/
def realSignOut (x : G.Stmt) (w : G.Wit) (t : G.Tables) (b : Bool) (m : G.Msg)
    (e : Fin G.μ → G.Ch) (r : G.Rand) : G.Answer × (G.Tables × Bool) :=
  let v := effVec t.lookupAll (G.key x w m r) e
  let fresh := (List.finRange G.μ).filter fun i => (t.lookupAll (G.key x w m r v i)).isNone
  (.inr (G.sign x w m r v),
    ({ t with
        prog := t.prog ++ (fresh.filter (G.pub x w m r v)).map fun i => (G.key x w m r v i, v i)
        signed := t.signed ++ [m]
        rej := t.rej ++ (fresh.filter fun i => !G.pub x w m r v i).map
          fun i => (G.key x w m r v i, v i) },
      b || (List.finRange G.μ).any fun i => (t.lookupAll (G.key x w m r v i)).isSome))

/-- Programming the entries `l` in order: an entry at a defined point sets the flag
and is dropped, the others are recorded in `prog`. -/
def programAll : G.Tables → Bool → List (G.Key × G.Ch) → G.Tables × Bool
  | t, b, [] => (t, b)
  | t, b, p :: l =>
    match t.lookup p.1 with
    | some _ => programAll t true l
    | none => programAll { t with prog := t.prog ++ [p] } b l

/-- The signing answer with the view `v` on `m`: the public entries of `v` are
programmed and `m` is recorded as signed. -/
def programOut (t : G.Tables) (b : Bool) (m : G.Msg) (v : G.View) :
    G.Answer × (G.Tables × Bool) :=
  (.inr v.2, ({ (programAll t b v.1).1 with signed := t.signed ++ [m] }, (programAll t b v.1).2))

/-- The simulated signing oracle on `m` for the statement `x`, from the sampled
values `e` and simulator randomness `s`: the view `G.simulate x m e s` is answered
and programmed by `programOut`. -/
def simSignOut (x : G.Stmt) (t : G.Tables) (b : Bool) (m : G.Msg) (e : Fin G.μ → G.Ch)
    (s : G.SimRand) : G.Answer × (G.Tables × Bool) :=
  programOut t b m (G.simulate x m e s)

variable (G) in
/-- Uniform values for the entries of an attempt followed by an independent uniform
value of `β`, mapped by `F`. -/
noncomputable def sampleVec {β γ : Type} [Fintype β] [Nonempty β]
    (F : (Fin G.μ → G.Ch) → β → γ) : PMF γ :=
  (PMF.uniformOfFintype (Fin G.μ → G.Ch)).bind fun e =>
    (PMF.uniformOfFintype β).map fun y => F e y

/-- The real oracle for the pair `(x, w)`. -/
noncomputable def realStep (xw : G.Stmt × G.Wit) (s : G.Tables × Bool) :
    G.Query → Step G.Answer (G.Tables × Bool) G.Ch
  | .inl k => realHashStep s.1 s.2 k
  | .inr m => .plain (sampleVec G (realSignOut xw.1 xw.2 s.1 s.2 m))

/-- The simulated oracle for the statement `x`. -/
noncomputable def simStep (x : G.Stmt) (s : G.Tables × Bool) :
    G.Query → Step G.Answer (G.Tables × Bool) G.Ch
  | .inl k => hashStep s.1 s.2 k
  | .inr m => .plain (sampleVec G (simSignOut x s.1 s.2 m))

end Oracles

/-! ## Adversaries and games -/

namespace Protocol

variable (G : Protocol)

/-- An EUF-CMA adversary in the random-oracle model: on the statement (public key),
an adaptive oracle adversary outputting a forgery with at most `qH` hash queries
and `qS` signing queries. -/
structure Adversary (qH qS : ℕ) : Type 1 where
  /-- The adversary on statement `x`. -/
  run : G.Stmt → OracleAdv G.Query G.Answer G.Forgery
  /-- The query bounds. -/
  isQueryBound : ∀ x, IsQueryBound₂ (run x) qH qS

end Protocol

variable (P M) in
/-- An EUF-CMA adversary against the Fiat–Shamir signature scheme over `P`. -/
abbrev Adversary (qH qS : ℕ) := (P.toProtocol M).Adversary qH qS

section Games

variable {G : Protocol}

/-- The verifier's queries for the forgery `(m, σ)`, `n` of them remaining after the
values `acc`, followed by the forgery. -/
def verifyQueries (x : G.Stmt) (m : G.Msg) (σ : G.Sig) :
    ℕ → List G.Ch → OracleAdv G.Query G.Answer G.Forgery
  | 0, _ => .ret (m, σ)
  | n + 1, acc => .query (.inl (G.vkey x m σ acc)) fun a => match a with
    | .inl e => verifyQueries x m σ n (acc ++ [e])
    | .inr _ => .ret (m, σ)

/-- The adversary followed by the challenger's hash queries at the verifier's points
for the forgery. -/
def withVerify (x : G.Stmt) : OracleAdv G.Query G.Answer G.Forgery →
    OracleAdv G.Query G.Answer G.Forgery
  | .ret (m, σ) => verifyQueries x m σ G.V []
  | .rand p k => .rand p fun b => withVerify x (k b)
  | .query d k => .query d fun r => withVerify x (k r)

/-- The values at the verifier's points for `(m, σ)` from the oracle `look`, `n` of
them remaining after the values `acc`, if all are defined. -/
def verifyVals (look : G.Key → Option G.Ch) (x : G.Stmt) (m : G.Msg) (σ : G.Sig) :
    ℕ → List G.Ch → Option (List G.Ch)
  | 0, acc => some acc
  | n + 1, acc => (look (G.vkey x m σ acc)).bind fun e => verifyVals look x m σ n (acc ++ [e])

/-- The winning condition on the final forgery and tables: the message was never
signed and the verifier accepts the values recorded at its points. -/
def wins (x : G.Stmt) (y : G.Forgery × (G.Tables × Bool)) : Bool :=
  !(y.2.1.signed.contains y.1.1) &&
    match verifyVals y.2.1.lookup x y.1.1 y.1.2 G.V [] with
    | some vs => G.verify x y.1.1 y.1.2 vs
    | none => false

/-- The distribution of the EUF-CMA experiment against the oracle family `O`
indexed by the generated pair. -/
noncomputable def gameDist (O : G.Stmt × G.Wit → G.Tables × Bool → G.Query →
    Step G.Answer (G.Tables × Bool) G.Ch) {qH qS : ℕ} (A : G.Adversary qH qS) :
    PMF Bool :=
  G.gen.bind fun xw =>
    (OracleAdv.run (toOracle (O xw)) (withVerify xw.1 (A.run xw.1))
      (Tables.empty, false)).map (wins xw.1)

/-- The EUF-CMA game in the random-oracle model. -/
noncomputable def eufcmaGame {qH qS : ℕ} (A : G.Adversary qH qS) : SPComp Bool :=
  PRPPRF.pmfGame (gameDist realStep A)

/-- The EUF-CMA advantage in the random-oracle model. -/
noncomputable def eufcmaAdvantage {qH qS : ℕ} (A : G.Adversary qH qS) : ℝ≥0∞ :=
  prTrue (eufcmaGame A) Heap.empty

/-- The EUF-CMA game with the simulated signing oracle. -/
noncomputable def simGame {qH qS : ℕ} (A : G.Adversary qH qS) : SPComp Bool :=
  PRPPRF.pmfGame (gameDist (fun xw => simStep xw.1) A)

/-- The advantage in the simulated game. -/
noncomputable def simAdvantage {qH qS : ℕ} (A : G.Adversary qH qS) : ℝ≥0∞ :=
  prTrue (simGame A) Heap.empty

end Games

/-! ## The values of an attempt -/

section EffLemmas

variable {μ : ℕ} {K C : Type} (look : K → Option C) (key : (Fin μ → C) → Fin μ → K)
  (hk : ∀ (v v' : Fin μ → C) (i : Fin μ), (∀ j, j < i → v j = v' j) → key v i = key v' i)
  (e : Fin μ → C)

include hk in
theorem effVal_eq (i : Fin μ) :
    effVal look key e i = (look (key (effVec look key e) i)).getD (e i) := by
  rw [effVal]
  congr 2
  exact hk _ _ i fun j hj => by simp [hj, effVec]

include hk in
/-- The values of an attempt are the only solution of their defining equations. -/
theorem effVec_unique (v : Fin μ → C) (hv : ∀ i, v i = (look (key v i)).getD (e i)) :
    v = effVec look key e := by
  have h : ∀ n, ∀ i : Fin μ, i.val < n → v i = effVec look key e i := by
    intro n
    induction n with
    | zero => exact fun i hi => absurd hi (Nat.not_lt_zero _)
    | succ n ih =>
      intro i hi
      rw [hv i]
      change _ = effVal look key e i
      rw [effVal_eq look key hk e i]
      congr 2
      exact hk _ _ i fun j hj => ih j (by have : j.val < i.val := hj; omega)
  funext i
  exact h _ i i.isLt

include hk in
/-- When no point of the attempt with the values `e` is defined, its values are `e`. -/
theorem effVec_of_none (h : ∀ i, look (key e i) = none) : effVec look key e = e :=
  (effVec_unique look key hk e e fun i => by rw [h i]; rfl).symm

include hk in
/-- When no point of the attempt is defined, its values are `e`, and no point of the
attempt with the values `e` is defined. -/
theorem effVec_eq_of_none (h : ∀ i, look (key (effVec look key e) i) = none) :
    effVec look key e = e := by
  funext i
  change effVal look key e i = e i
  rw [effVal_eq look key hk e i, h i]
  rfl

include hk in
/-- Two oracles that agree at the points of the attempt against the first give the
same values. -/
theorem effVec_congr (look' : K → Option C)
    (h : ∀ i, look' (key (effVec look key e) i) = look (key (effVec look key e) i)) :
    effVec look' key e = effVec look key e :=
  (effVec_unique look' key hk e _ fun i => by
    rw [h i]
    exact effVal_eq look key hk e i).symm

end EffLemmas

/-! ## Entry lists -/

section Lists

variable {K C : Type} [DecidableEq K]

theorem lookupIn_isSome_mem {l : List (K × C)} {k : K} (h : (lookupIn l k).isSome) :
    k ∈ l.map Prod.fst := by
  unfold lookupIn findKey at h
  cases hf : l.findIdx? (fun p => decide (p.1 = k)) with
  | none => simp [hf] at h
  | some i =>
    obtain ⟨hi, hp, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
    simp only [decide_eq_true_eq] at hp
    exact List.mem_map.mpr ⟨l[i], List.getElem_mem hi, hp⟩

theorem lookupIn_nil (k : K) : lookupIn ([] : List (K × C)) k = none := by
  simp [lookupIn, findKey]

theorem lookupIn_cons_of_ne (ent : K × C) (l : List (K × C)) {k : K} (hk : k ≠ ent.1) :
    lookupIn (ent :: l) k = lookupIn l k := by
  unfold lookupIn findKey
  rw [List.findIdx?_cons]
  have hne : decide (ent.1 = k) = false := decide_eq_false fun h => hk h.symm
  rw [hne]
  cases l.findIdx? (fun p => decide (p.1 = k)) <;> simp

theorem lookupIn_append_of_notMem (l l' : List (K × C)) {k : K} (hk : k ∉ l'.map Prod.fst) :
    lookupIn (l' ++ l) k = lookupIn l k := by
  induction l' with
  | nil => rfl
  | cons p l' ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hk
    rw [List.cons_append, lookupIn_cons_of_ne p _ hk.1, ih hk.2]

theorem lookupIn_eq_none_of_notMem {l : List (K × C)} {k : K} (hk : k ∉ l.map Prod.fst) :
    lookupIn l k = none := by
  have := lookupIn_append_of_notMem ([] : List (K × C)) l hk
  rwa [List.append_nil, lookupIn_nil] at this

theorem lookupIn_append_singleton_of_ne (l : List (K × C)) (p : K × C) {k : K}
    (hk : k ≠ p.1) : lookupIn (l ++ [p]) k = lookupIn l k := by
  unfold lookupIn findKey
  rw [List.findIdx?_append]
  cases hf : l.findIdx? (fun p => decide (p.1 = k)) with
  | some i =>
    obtain ⟨hi, _, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
    simp [List.getElem?_append_left hi]
  | none =>
    have hne : decide (p.1 = k) = false := decide_eq_false fun h => hk h.symm
    simp [List.findIdx?_cons, hne]

end Lists

/-! ## Transitions -/

section Transitions

variable {G : Protocol}

namespace Protocol

/-- `t'` extends `t`: every entry list of `t` is a prefix of the one of `t'`. -/
def Tables.Le (t t' : G.Tables) : Prop :=
  t.prog <+: t'.prog ∧ t.hash <+: t'.hash ∧ t.rej <+: t'.rej

theorem Tables.Le.refl (t : G.Tables) : t.Le t :=
  ⟨List.prefix_refl _, List.prefix_refl _, List.prefix_refl _⟩

theorem Tables.Le.trans {t t' t'' : G.Tables} (h : t.Le t') (h' : t'.Le t'') : t.Le t'' :=
  ⟨h.1.trans h'.1, h.2.1.trans h'.2.1, h.2.2.trans h'.2.2⟩

theorem Tables.mem_keys {t : G.Tables} {k : G.Key} :
    k ∈ t.keys ↔ ∃ p, (p ∈ t.prog ∨ p ∈ t.hash ∨ p ∈ t.rej) ∧ p.1 = k := by
  simp only [Tables.keys, List.mem_map, List.mem_append]
  constructor
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, by tauto, rfl⟩
  · rintro ⟨p, hp, rfl⟩
    exact ⟨p, by tauto, rfl⟩

theorem Tables.Le.keys_subset {t t' : G.Tables} (h : t.Le t') {k : G.Key}
    (hk : k ∈ t.keys) : k ∈ t'.keys := by
  obtain ⟨p, hp, rfl⟩ := Tables.mem_keys.mp hk
  refine Tables.mem_keys.mpr ⟨p, ?_, rfl⟩
  rcases hp with hp | hp | hp
  · exact Or.inl (h.1.subset hp)
  · exact Or.inr (Or.inl (h.2.1.subset hp))
  · exact Or.inr (Or.inr (h.2.2.subset hp))

theorem Tables.length_keys (t : G.Tables) : t.keys.length = t.size := by
  simp [Tables.keys, Tables.size, Nat.add_assoc]

theorem lookup_isSome_mem {t : G.Tables} {k : G.Key} (h : (t.lookup k).isSome) :
    k ∈ (t.prog ++ t.hash).map Prod.fst := by
  unfold Tables.lookup at h
  rw [List.map_append, List.mem_append]
  cases hp : lookupIn t.prog k with
  | some e => exact Or.inl (lookupIn_isSome_mem (by simp [hp]))
  | none =>
    simp only [hp, Option.none_or] at h
    exact Or.inr (lookupIn_isSome_mem h)

theorem lookupAll_isSome_mem {t : G.Tables} {k : G.Key} (h : (t.lookupAll k).isSome) :
    k ∈ t.keys := by
  unfold Tables.lookupAll at h
  unfold Tables.keys
  rw [List.map_append, List.mem_append]
  cases hl : t.lookup k with
  | some e => exact Or.inl (lookup_isSome_mem (by simp [hl]))
  | none =>
    simp only [hl, Option.none_or] at h
    exact Or.inr (lookupIn_isSome_mem h)

theorem lookupAll_eq_none_of_notMem {t : G.Tables} {k : G.Key} (h : k ∉ t.keys) :
    t.lookupAll k = none := by
  cases hl : t.lookupAll k with
  | none => rfl
  | some _ => exact absurd (lookupAll_isSome_mem (by rw [hl]; rfl)) h

theorem lookup_eq_none_of_lookupAll {t : G.Tables} {k : G.Key} (h : t.lookupAll k = none) :
    t.lookup k = none := by
  unfold Tables.lookupAll at h
  cases hl : t.lookup k with
  | none => rfl
  | some _ => simp [hl] at h

theorem lookupAll_addRejs_of_notMem (l : List (G.Key × G.Ch)) (t : G.Tables) {k : G.Key}
    (hk : k ∉ l.map Prod.fst) : (t.addRejs l).lookupAll k = t.lookupAll k := by
  unfold Tables.lookupAll
  rw [show (t.addRejs l).rej = l ++ t.rej from rfl, lookupIn_append_of_notMem _ _ hk]
  rfl

end Protocol

theorem sampleVec_bind {β γ δ : Type} [Fintype β] [Nonempty β]
    (F : (Fin G.μ → G.Ch) → β → γ) (g : γ → PMF δ) :
    (sampleVec G F).bind g = (PMF.uniformOfFintype (Fin G.μ → G.Ch)).bind fun e =>
      (PMF.uniformOfFintype β).bind fun y => g (F e y) := by
  simp only [sampleVec, PMF.bind_bind, PMF.bind_map, Function.comp_def]

theorem mem_support_sampleVec {β γ : Type} [Fintype β] [Nonempty β]
    {F : (Fin G.μ → G.Ch) → β → γ} {y : γ} (hy : y ∈ (sampleVec G F).support) :
    ∃ e b, y = F e b := by
  simp only [sampleVec, PMF.mem_support_bind_iff, PMF.support_map, Set.mem_image] at hy
  obtain ⟨e, _, b, _, rfl⟩ := hy
  exact ⟨e, b, rfl⟩

theorem programAll_flag (t : G.Tables) (l : List (G.Key × G.Ch)) :
    (programAll t true l).2 = true := by
  induction l generalizing t with
  | nil => rfl
  | cons p l ih =>
    unfold programAll
    split
    · exact ih t
    · exact ih _

/-- Programming entries keeps the hash entries and adds public entries taken from
the programmed list. -/
theorem programAll_tables (t : G.Tables) (b : Bool) (l : List (G.Key × G.Ch)) :
    (programAll t b l).1.hash = t.hash ∧ (programAll t b l).1.signed = t.signed ∧
      (programAll t b l).1.rej = t.rej ∧ t.prog <+: (programAll t b l).1.prog ∧
      (∀ p ∈ (programAll t b l).1.prog, p ∈ t.prog ∨ p ∈ l) := by
  induction l generalizing t b with
  | nil => exact ⟨rfl, rfl, rfl, List.prefix_refl _, fun p hp => Or.inl hp⟩
  | cons q l ih =>
    unfold programAll
    split
    · obtain ⟨h1, h2, h3, h4, h5⟩ := ih t true
      exact ⟨h1, h2, h3, h4, fun p hp => (h5 p hp).imp id (List.mem_cons_of_mem q)⟩
    · obtain ⟨h1, h2, h3, h4, h5⟩ := ih { t with prog := t.prog ++ [q] } b
      refine ⟨h1, h2, h3, (List.prefix_append _ _).trans h4, fun p hp => ?_⟩
      rcases h5 p hp with hp | hp
      · rcases List.mem_append.mp hp with hp | hp
        · exact Or.inl hp
        · exact Or.inr (by simp_all)
      · exact Or.inr (List.mem_cons_of_mem q hp)

/-- Programming entries at undefined and distinct points records all of them. -/
theorem programAll_of_fresh (t : G.Tables) (b : Bool) (l : List (G.Key × G.Ch))
    (hl : ∀ p ∈ l, t.lookup p.1 = none) (hnd : (l.map Prod.fst).Nodup) :
    programAll t b l = ({ t with prog := t.prog ++ l }, b) := by
  induction l generalizing t with
  | nil => simp [programAll]
  | cons q l ih =>
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    unfold programAll
    rw [hl q (List.mem_cons_self ..)]
    dsimp only
    rw [ih _ (fun p hp => ?_) hnd.2]
    · simp
    · change (lookupIn (t.prog ++ [q]) p.1).or (lookupIn t.hash p.1) = none
      rw [lookupIn_append_singleton_of_ne _ _ fun h => hnd.1 ⟨p, hp, h⟩]
      exact hl p (List.mem_cons_of_mem q hp)

theorem realStep_flag (xw : G.Stmt × G.Wit) (t : G.Tables) (d : G.Query)
    (x : G.Answer × (G.Tables × Bool))
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
    obtain ⟨e, r, rfl⟩ := mem_support_sampleVec hx
    rfl

theorem simStep_flag (x₀ : G.Stmt) (t : G.Tables) (d : G.Query)
    (x : G.Answer × (G.Tables × Bool))
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
    obtain ⟨e, s, rfl⟩ := mem_support_sampleVec hx
    exact programAll_flag t _

end Transitions

/-! ## The real signing oracle -/

section RealSign

variable {G : Protocol} (x : G.Stmt) (w : G.Wit) (t : G.Tables) (b : Bool) (m : G.Msg)
  (e : Fin G.μ → G.Ch) (r : G.Rand)

/-- An attempt none of whose points is defined records its public and hidden
entries and keeps the flag. -/
theorem realSignOut_of_none (h : ∀ i, t.lookupAll (G.key x w m r e i) = none) :
    realSignOut x w t b m e r = (.inr (G.sign x w m r e),
      ({ t with
          prog := t.prog ++ G.pubEntries x w m r e
          signed := t.signed ++ [m]
          rej := t.rej ++ G.hidEntries x w m r e }, b)) := by
  have hv : effVec t.lookupAll (G.key x w m r) e = e :=
    effVec_of_none _ _ (G.key_causal x w m r) e h
  simp [realSignOut, hv, h, Protocol.pubEntries, Protocol.hidEntries]

/-- An attempt one of whose points is defined sets the flag. -/
theorem realSignOut_flag_of_some (h : ∃ i, (t.lookupAll (G.key x w m r e i)).isSome) :
    (realSignOut x w t b m e r).2.2 = true := by
  simp only [realSignOut, Bool.or_eq_true, List.any_eq_true, List.mem_finRange, true_and]
  refine Or.inr (by_contra fun hn => ?_)
  have hn' : ∀ i, t.lookupAll (G.key x w m r (effVec t.lookupAll (G.key x w m r) e) i) = none :=
    fun i => Option.not_isSome_iff_eq_none.mp fun hs => hn ⟨i, hs⟩
  have hv := effVec_eq_of_none _ _ (G.key_causal x w m r) e hn'
  obtain ⟨i, hi⟩ := h
  rw [hv] at hn'
  rw [hn' i] at hi
  exact Bool.false_ne_true hi

/-- A real signing attempt extends the tables by at most `μ` entries. -/
theorem realSignOut_support :
    t.Le (realSignOut x w t b m e r).2.1 ∧
      (realSignOut x w t b m e r).2.1.size ≤ t.size + G.μ := by
  refine ⟨⟨List.prefix_append _ _, List.prefix_refl _, List.prefix_append _ _⟩, ?_⟩
  simp only [realSignOut, Protocol.Tables.size, List.length_append, List.length_map]
  set v := effVec t.lookupAll (G.key x w m r) e
  set fr := (List.finRange G.μ).filter fun i => (t.lookupAll (G.key x w m r v i)).isNone
  have h1 := List.length_eq_length_filter_add (G.pub x w m r v) (l := fr)
  have h2 : fr.length ≤ G.μ := (List.length_filter_le _ _).trans (List.length_finRange).le
  omega

/-- Every point of a real signing attempt is defined after it. -/
theorem realSignOut_key (i : Fin G.μ) :
    G.key x w m r (effVec t.lookupAll (G.key x w m r) e) i ∈
      (realSignOut x w t b m e r).2.1.keys := by
  set v := effVec t.lookupAll (G.key x w m r) e
  cases hl : t.lookupAll (G.key x w m r v i) with
  | some _ =>
    exact (realSignOut_support x w t b m e r).1.keys_subset
      (Protocol.lookupAll_isSome_mem (by rw [hl]; rfl))
  | none =>
    refine Protocol.Tables.mem_keys.mpr ⟨(G.key x w m r v i, v i), ?_, rfl⟩
    have hf : i ∈ (List.finRange G.μ).filter fun i => (t.lookupAll (G.key x w m r v i)).isNone :=
      List.mem_filter.mpr ⟨List.mem_finRange i, by simp [hl]⟩
    cases hp : G.pub x w m r v i
    · refine Or.inr (Or.inr (List.mem_append_right _ (List.mem_map.mpr ⟨i, ?_, rfl⟩)))
      exact List.mem_filter.mpr ⟨hf, by simpa using hp⟩
    · refine Or.inl (List.mem_append_right _ (List.mem_map.mpr ⟨i, ?_, rfl⟩))
      exact List.mem_filter.mpr ⟨hf, hp⟩

/-- A signing attempt none of whose points is among the entries `l` commutes with
adding `l` to the hidden entries. -/
theorem realSignOut_addRejs (l : List (G.Key × G.Ch))
    (hk : ∀ i, G.key x w m r (effVec t.lookupAll (G.key x w m r) e) i ∉ l.map Prod.fst) :
    realSignOut x w (t.addRejs l) b m e r =
      Prod.map id (Prod.map (Protocol.Tables.addRejs l) id) (realSignOut x w t b m e r) := by
  have hv : effVec (t.addRejs l).lookupAll (G.key x w m r) e =
      effVec t.lookupAll (G.key x w m r) e :=
    effVec_congr _ _ (G.key_causal x w m r) e _ fun i =>
      Protocol.lookupAll_addRejs_of_notMem l t (hk i)
  have hl : ∀ i, (t.addRejs l).lookupAll
      (G.key x w m r (effVec t.lookupAll (G.key x w m r) e) i) =
      t.lookupAll (G.key x w m r (effVec t.lookupAll (G.key x w m r) e) i) :=
    fun i => Protocol.lookupAll_addRejs_of_notMem l t (hk i)
  simp only [realSignOut, hv, hl]
  simp [Protocol.Tables.addRejs]

end RealSign

/-! ## Tables grow along a real run -/

section Grow

variable {G : Protocol} {α : Type}

/-- A hash query at a point outside the entries `l` commutes with adding `l` to
the hidden entries. -/
theorem realStep_addRejs_inl (xw : G.Stmt × G.Wit) (l : List (G.Key × G.Ch)) (t : G.Tables)
    (b : Bool) (k : G.Key) (hk : k ∉ l.map Prod.fst) :
    toOracle (realStep xw) (t.addRejs l, b) (.inl k) =
      (toOracle (realStep xw) (t, b) (.inl k)).map
        (Prod.map id (Prod.map (Protocol.Tables.addRejs l) id)) := by
  simp only [toOracle, realStep, realHashStep]
  rw [show (t.addRejs l).lookup k = t.lookup k from rfl,
    show lookupIn (t.addRejs l).rej k = lookupIn t.rej k from lookupIn_append_of_notMem _ _ hk]
  cases t.lookup k with
  | some e => simp only [Step.toPMF, PMF.pure_map]; rfl
  | none =>
    cases lookupIn t.rej k with
    | some e => simp only [Step.toPMF, PMF.pure_map]; rfl
    | none => simp only [Step.toPMF, PMF.map_comp]; rfl

/-- Every real transition extends the tables, by at most one entry for a hash query
and at most `μ` entries for a signing query. -/
theorem realStep_support (xw : G.Stmt × G.Wit) (s : G.Tables × Bool) (d : G.Query)
    (o : G.Answer × (G.Tables × Bool)) (ho : o ∈ (toOracle (realStep xw) s d).support) :
    s.1.Le o.2.1 ∧ o.2.1.size ≤ s.1.size + Sum.elim (fun _ => 1) (fun _ => G.μ) d := by
  obtain ⟨t, b⟩ := s
  cases d with
  | inl k =>
    simp only [toOracle, realStep, realHashStep] at ho
    cases hl : t.lookup k with
    | some e =>
      simp only [hl, Step.toPMF, PMF.support_pure, Set.mem_singleton_iff] at ho
      subst ho
      exact ⟨Protocol.Tables.Le.refl _, Nat.le_succ _⟩
    | none =>
      cases hr : lookupIn t.rej k with
      | some e =>
        simp only [hl, hr, Step.toPMF, PMF.support_pure, Set.mem_singleton_iff] at ho
        subst ho
        exact ⟨⟨List.prefix_refl _, List.prefix_append _ _, List.prefix_refl _⟩,
          by simp [Protocol.Tables.size]; omega⟩
      | none =>
        simp only [hl, hr, Step.toPMF, PMF.support_map, Set.mem_image] at ho
        obtain ⟨e, _, rfl⟩ := ho
        exact ⟨⟨List.prefix_refl _, List.prefix_append _ _, List.prefix_refl _⟩,
          by simp [Protocol.Tables.size]; omega⟩
  | inr m =>
    simp only [toOracle, realStep, Step.toPMF] at ho
    obtain ⟨e, r, rfl⟩ := mem_support_sampleVec ho
    exact realSignOut_support _ _ _ _ _ _ _

/-- The point of a hash query is defined after the real transition. -/
theorem realStep_key_inl (xw : G.Stmt × G.Wit) (s : G.Tables × Bool) (k : G.Key)
    (o : G.Answer × (G.Tables × Bool))
    (ho : o ∈ (toOracle (realStep xw) s (.inl k)).support) : k ∈ o.2.1.keys := by
  obtain ⟨t, b⟩ := s
  simp only [toOracle, realStep, realHashStep] at ho
  have happ : ∀ e : G.Ch, k ∈ ({ t with hash := t.hash ++ [(k, e)] } : G.Tables).keys :=
    fun e => Protocol.Tables.mem_keys.mpr ⟨(k, e), Or.inr (Or.inl (by simp)), rfl⟩
  cases hl : t.lookup k with
  | some e =>
    simp only [hl, Step.toPMF, PMF.support_pure, Set.mem_singleton_iff] at ho
    subst ho
    have := Protocol.lookup_isSome_mem (show (t.lookup k).isSome by rw [hl]; rfl)
    simp only [Protocol.Tables.keys, List.map_append, List.mem_append] at this ⊢
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

theorem run_real_support_le (xw : G.Stmt × G.Wit) (A : OracleAdv G.Query G.Answer α)
    (s : G.Tables × Bool) (y : α × (G.Tables × Bool))
    (hy : y ∈ (OracleAdv.run (toOracle (realStep xw)) A s).support) : s.1.Le y.2.1 := by
  induction A generalizing s with
  | ret a =>
    rw [OracleAdv.run_ret, PMF.support_pure, Set.mem_singleton_iff] at hy
    subst hy
    exact Protocol.Tables.Le.refl _
  | rand p k ih =>
    rw [OracleAdv.run_rand, PMF.mem_support_bind_iff] at hy
    obtain ⟨b, _, hb⟩ := hy
    exact ih b s hb
  | query d k ih =>
    rw [OracleAdv.run_query, PMF.mem_support_bind_iff] at hy
    obtain ⟨o, ho, hy⟩ := hy
    exact (realStep_support xw s d o ho).1.trans (ih o.1 o.2 hy)

theorem run_real_support_flag (xw : G.Stmt × G.Wit) (A : OracleAdv G.Query G.Answer α)
    (s : G.Tables × Bool) (y : α × (G.Tables × Bool))
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

theorem run_real_support_size (xw : G.Stmt × G.Wit) (A : OracleAdv G.Query G.Answer α)
    (h q : ℕ) (hA : IsQueryBound₂ A h q) (s : G.Tables × Bool) (y : α × (G.Tables × Bool))
    (hy : y ∈ (OracleAdv.run (toOracle (realStep xw)) A s).support) :
    y.2.1.size ≤ s.1.size + h + G.μ * q := by
  induction A generalizing h q s with
  | ret a =>
    rw [OracleAdv.run_ret, PMF.support_pure, Set.mem_singleton_iff] at hy
    subst hy
    show s.1.size ≤ _
    omega
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
        simp only [Sum.elim_inl] at hs
        omega
    | inr m =>
      cases q with
      | zero => exact hA.elim
      | succ q =>
        have := ih o.1 h q (hA o.1) o.2 hy
        simp only [Sum.elim_inr] at hs
        rw [Nat.mul_succ]
        omega

end Grow

/-! ## Hidden entries change the flag only where they are reached -/

section Hidden

variable {G : Protocol} {α : Type}

theorem toOuterMeasure_eq_one_of_support {β : Type} (p : PMF β) (S : Set β)
    (h : ∀ y ∈ p.support, y ∈ S) : p.toOuterMeasure S = 1 :=
  (PMF.toOuterMeasure_apply_eq_one_iff p S).mpr h

/-- A real run from tables in which `k₀` is defined defines `k₀` at the end. -/
theorem run_real_keys_eq_one (xw : G.Stmt × G.Wit) (A : OracleAdv G.Query G.Answer α)
    (s : G.Tables × Bool) (k₀ : G.Key) (hk : k₀ ∈ s.1.keys) (E : Set (α × (G.Tables × Bool)))
    (hE : ∀ y, k₀ ∈ y.2.1.keys → y ∈ E) :
    (OracleAdv.run (toOracle (realStep xw)) A s).toOuterMeasure E = 1 :=
  toOuterMeasure_eq_one_of_support _ _ fun y hy =>
    hE y ((run_real_support_le xw A s y hy).keys_subset hk)

/-- A signing query in the induction of `run_real_addRejs_flag_le`. -/
theorem run_real_addRejs_sign_le (xw : G.Stmt × G.Wit) (l : List (G.Key × G.Ch))
    (k : G.Answer → OracleAdv G.Query G.Answer α) (t : G.Tables) (m : G.Msg)
    (ih : ∀ c (t' : G.Tables) (b' : Bool),
      (OracleAdv.run (toOracle (realStep xw)) (k c) (t'.addRejs l, b')).toOuterMeasure
          {y | y.2.2 = true} ≤
        (OracleAdv.run (toOracle (realStep xw)) (k c) (t', b')).toOuterMeasure
          {y | y.2.2 = true ∨ ∃ p ∈ l, p.1 ∈ y.2.1.keys}) :
    (OracleAdv.run (toOracle (realStep xw)) (.query (.inr m) k) (t.addRejs l, false)).toOuterMeasure
        {y | y.2.2 = true} ≤
      (OracleAdv.run (toOracle (realStep xw)) (.query (.inr m) k) (t, false)).toOuterMeasure
        {y | y.2.2 = true ∨ ∃ p ∈ l, p.1 ∈ y.2.1.keys} := by
  simp only [OracleAdv.run_query, toOracle, realStep, Step.toPMF, sampleVec_bind,
    PMF.toOuterMeasure_bind_apply]
  refine ENNReal.tsum_le_tsum fun e => mul_le_mul_right
    (ENNReal.tsum_le_tsum fun r => mul_le_mul_right ?_ _) _
  by_cases hc : ∃ i, G.key xw.1 xw.2 m r (effVec t.lookupAll (G.key xw.1 xw.2 m r) e) i ∈
      l.map Prod.fst
  · obtain ⟨i, hi⟩ := hc
    obtain ⟨p, hp, hpk⟩ := List.mem_map.mp hi
    refine (toOuterMeasure_le_one _ _).trans (le_of_eq
      (run_real_keys_eq_one xw _ _ p.1 ?_ _ fun y hy => Or.inr ⟨p, hp, hy⟩).symm)
    rw [hpk]
    exact realSignOut_key _ _ _ _ _ _ _ i
  · rw [realSignOut_addRejs xw.1 xw.2 t false m e r l fun i hi => hc ⟨i, hi⟩]
    exact ih _ _ _

/-- **Hidden entries change the flag only where they are reached.** For the entries
`l`, the probability that a real run from `t` with `l` added to the hidden entries
sets the flag is at most the probability that the run from `t` sets the flag or ends
with the point of some entry of `l` defined. -/
theorem run_real_addRejs_flag_le (xw : G.Stmt × G.Wit) (l : List (G.Key × G.Ch))
    (A : OracleAdv G.Query G.Answer α) (t : G.Tables) (b : Bool) :
    (OracleAdv.run (toOracle (realStep xw)) A (t.addRejs l, b)).toOuterMeasure
        {y | y.2.2 = true} ≤
      (OracleAdv.run (toOracle (realStep xw)) A (t, b)).toOuterMeasure
        {y | y.2.2 = true ∨ ∃ p ∈ l, p.1 ∈ y.2.1.keys} := by
  induction A generalizing t b with
  | ret a =>
    simp only [OracleAdv.run_ret, PMF.toOuterMeasure_pure_apply]
    split_ifs with h1 h2 <;> first | exact le_rfl | exact zero_le | exact absurd (Or.inl h1) h2
  | rand p k ih =>
    simp only [OracleAdv.run_rand, PMF.toOuterMeasure_bind_apply]
    exact ENNReal.tsum_le_tsum fun c => mul_le_mul_right (ih c t b) _
  | query d k ih =>
    by_cases hb : b = true ∨ ∃ p ∈ l, p.1 ∈ t.keys
    · refine (toOuterMeasure_le_one _ _).trans (le_of_eq ?_)
      refine (toOuterMeasure_eq_one_of_support _ _ fun y hy => ?_).symm
      rcases hb with hb | ⟨p, hp, hk⟩
      · exact Or.inl (run_real_support_flag xw _ (t, b) y hy hb)
      · exact Or.inr ⟨p, hp, (run_real_support_le xw _ (t, b) y hy).keys_subset hk⟩
    simp only [not_or, Bool.not_eq_true, not_exists, not_and] at hb
    obtain ⟨rfl, hk⟩ := hb
    cases d with
    | inl key =>
      by_cases hke : key ∈ l.map Prod.fst
      · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hke
        refine (toOuterMeasure_le_one _ _).trans (le_of_eq ?_)
        refine (toOuterMeasure_eq_one_of_support _ _ fun y hy => ?_).symm
        rw [OracleAdv.run_query, PMF.mem_support_bind_iff] at hy
        obtain ⟨o, ho, hy⟩ := hy
        exact Or.inr ⟨p, hp, (run_real_support_le xw _ o.2 y hy).keys_subset
          (realStep_key_inl xw _ _ o ho)⟩
      · rw [OracleAdv.run_query, OracleAdv.run_query, realStep_addRejs_inl xw l t false key hke,
          PMF.bind_map, PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_bind_apply]
        exact ENNReal.tsum_le_tsum fun o => mul_le_mul_right (ih o.1 o.2.1 o.2.2) _
    | inr m => exact run_real_addRejs_sign_le xw l k t m fun c => ih c

end Hidden

/-! ## The flag is set with small probability -/

section Flag

variable {G : Protocol} {α : Type}

/-- The probability that `k` is in a list `L y` of length at most `N` is at most the
sum over `j < N` of the probability that the entry `j` of `L y` (`k₀` past its end)
is `k`. -/
theorem toOuterMeasure_mem_le_sum {β K : Type} (p : PMF β) (L : β → List K) (N : ℕ)
    (k₀ k : K) (hN : ∀ y ∈ p.support, (L y).length ≤ N) :
    p.toOuterMeasure {y | k ∈ L y} ≤
      ∑ j ∈ Finset.range N, (p.map fun y => (L y).getD j k₀) k := by
  rw [← PMF.toOuterMeasure_apply_inter_support]
  calc p.toOuterMeasure ({y | k ∈ L y} ∩ p.support)
      ≤ p.toOuterMeasure (⋃ j ∈ Finset.range N, (fun y => (L y).getD j k₀) ⁻¹' {k}) := by
        refine MeasureTheory.measure_mono fun y hy => ?_
        obtain ⟨hk, hy⟩ := hy
        obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem (show k ∈ L y from hk)
        simp only [Set.mem_iUnion, Set.mem_preimage, Set.mem_singleton_iff, Finset.mem_range]
        exact ⟨j, lt_of_lt_of_le hj (hN y hy), by simp [hj]⟩
    _ ≤ ∑ j ∈ Finset.range N, p.toOuterMeasure ((fun y => (L y).getD j k₀) ⁻¹' {k}) :=
        MeasureTheory.measure_biUnion_finset_le _ _
    _ = _ := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply_singleton]

/-- **Guessing the point of an entry.** For a pair with key bound `γ` and runs `R v`
indexed by views whose final tables have at most `N` points on the views
`guessView`, the expectation over the randomness of the probability that the point
of entry `i` is defined at the end of `R (guessView …)` is at most `N·γ`. -/
theorem tsum_guess_le {γ : ℝ≥0∞} (x : G.Stmt) (w : G.Wit) (hγ : G.KeyBoundAt x w γ)
    (m : G.Msg) (e : Fin G.μ → G.Ch) (i : Fin G.μ) (R : G.View → PMF (α × (G.Tables × Bool)))
    (N : ℕ) (hN : ∀ r, ∀ y ∈ (R (G.guessView x w m r e i)).support, y.2.1.keys.length ≤ N) :
    ∑' r, PMF.uniformOfFintype G.Rand r *
        (R (G.guessView x w m r e i)).toOuterMeasure {y | G.key x w m r e i ∈ y.2.1.keys} ≤
      N * γ := by
  obtain ⟨k₀⟩ : Nonempty G.Key := ⟨G.key x w m (Classical.arbitrary G.Rand) e i⟩
  -- the guess of the `j`-th point of the final tables
  let Q : ℕ → G.View → PMF G.Key := fun j v => (R v).map fun y => y.2.1.keys.getD j k₀
  have h1 : ∀ r, (R (G.guessView x w m r e i)).toOuterMeasure
      {y | G.key x w m r e i ∈ y.2.1.keys} ≤
        ∑ j ∈ Finset.range N, Q j (G.guessView x w m r e i) (G.key x w m r e i) := fun r =>
    toOuterMeasure_mem_le_sum (R (G.guessView x w m r e i)) (fun y => y.2.1.keys) N k₀
      (G.key x w m r e i) (hN r)
  have h2 : ∀ j ∈ Finset.range N, ∑' r, PMF.uniformOfFintype G.Rand r *
      Q j (G.guessView x w m r e i) (G.key x w m r e i) ≤ γ := fun j _ => hγ m e i (Q j)
  calc _ ≤ ∑' r, PMF.uniformOfFintype G.Rand r *
          ∑ j ∈ Finset.range N, Q j (G.guessView x w m r e i) (G.key x w m r e i) :=
        ENNReal.tsum_le_tsum fun r => mul_le_mul_right (h1 r) _
    _ = ∑ j ∈ Finset.range N, ∑' r, PMF.uniformOfFintype G.Rand r *
          Q j (G.guessView x w m r e i) (G.key x w m r e i) := by
        simp only [Finset.mul_sum]
        exact Summable.tsum_finsetSum fun _ _ => ENNReal.summable
    _ ≤ ∑ _j ∈ Finset.range N, γ := Finset.sum_le_sum h2
    _ = N * γ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The rest of a real run after a signing attempt on `m` from `t` with the view
`v`, the flag cleared and the hidden entries left out. -/
noncomputable def contRun (xw : G.Stmt × G.Wit) (k : G.Answer → OracleAdv G.Query G.Answer α)
    (t : G.Tables) (m : G.Msg) (v : G.View) : PMF (α × (G.Tables × Bool)) :=
  OracleAdv.run (toOracle (realStep xw)) (k (.inr v.2))
    ({ t with prog := t.prog ++ v.1, signed := t.signed ++ [m] }, false)

theorem length_pubEntries_le (x : G.Stmt) (w : G.Wit) (m : G.Msg) (r : G.Rand)
    (e : Fin G.μ → G.Ch) : (G.pubEntries x w m r e).length ≤ G.μ := by
  simp only [Protocol.pubEntries, List.length_map]
  exact (List.length_filter_le _ _).trans List.length_finRange.le

theorem length_guessView_le (x : G.Stmt) (w : G.Wit) (m : G.Msg) (r : G.Rand)
    (e : Fin G.μ → G.Ch) (i : Fin G.μ) : (G.guessView x w m r e i).1.length ≤ G.μ := by
  unfold Protocol.guessView
  split
  · exact Nat.zero_le _
  · exact length_pubEntries_le x w m r e

/-- The hidden entries of an attempt are at the points of its entries that are not
public. -/
theorem mem_hidEntries {x : G.Stmt} {w : G.Wit} {m : G.Msg} {r : G.Rand}
    {e : Fin G.μ → G.Ch} {p : G.Key × G.Ch} (hp : p ∈ G.hidEntries x w m r e) :
    ∃ i, G.pub x w m r e i = false ∧ p.1 = G.key x w m r e i := by
  simp only [Protocol.hidEntries, List.mem_map, List.mem_filter, List.mem_finRange, true_and,
    Bool.not_eq_true'] at hp
  obtain ⟨i, hi, rfl⟩ := hp
  exact ⟨i, hi, rfl⟩

/-- One signing attempt in the induction of `run_real_flag_le`: the probability
that the rest of the run sets the flag is at most the bound for the tables after the
attempt plus, for each entry, the probability that its point is defined at the end
of the rest of the run from the view `guessView`. -/
theorem flag_sign_term_le (xw : G.Stmt × G.Wit) {γ : ℝ≥0∞}
    (k : G.Answer → OracleAdv G.Query G.Answer α) (h q : ℕ) (t : G.Tables)
    (ht : t.rej = []) (m : G.Msg) (e : Fin G.μ → G.Ch) (r : G.Rand)
    (ih : ∀ c (t' : G.Tables), t'.rej = [] →
      (OracleAdv.run (toOracle (realStep xw)) (k c) (t', false)).toOuterMeasure
        {y | y.2.2 = true} ≤
        ((q * G.μ * (t'.hash.length + t'.prog.length + h + G.μ * q) : ℕ) : ℝ≥0∞) * γ) :
    (OracleAdv.run (toOracle (realStep xw)) (k (realSignOut xw.1 xw.2 t false m e r).1)
        (realSignOut xw.1 xw.2 t false m e r).2).toOuterMeasure {y | y.2.2 = true} ≤
      ((q * G.μ * (t.hash.length + t.prog.length + G.μ + h + G.μ * q) : ℕ) : ℝ≥0∞) * γ +
        ∑ i, (contRun xw k t m (G.guessView xw.1 xw.2 m r e i)).toOuterMeasure
          {y | G.key xw.1 xw.2 m r e i ∈ y.2.1.keys} := by
  by_cases hc : ∃ i, (t.lookupAll (G.key xw.1 xw.2 m r e i)).isSome
  · obtain ⟨i, hi⟩ := hc
    refine (toOuterMeasure_le_one _ _).trans (le_trans ?_ le_add_self)
    refine le_trans (le_of_eq ?_) (Finset.single_le_sum (fun _ _ => zero_le)
      (Finset.mem_univ i))
    refine (run_real_keys_eq_one xw _ _ _ ?_ _ fun y hy => hy).symm
    exact (show t.Le { t with prog := t.prog ++ _, signed := t.signed ++ [m] } from
      ⟨List.prefix_append _ _, List.prefix_refl _, List.prefix_refl _⟩).keys_subset
      (Protocol.lookupAll_isSome_mem hi)
  simp only [not_exists, Bool.not_eq_true, Option.isSome_eq_false_iff, Option.isNone_iff_eq_none]
    at hc
  rw [realSignOut_of_none _ _ _ _ _ _ _ hc]
  obtain ⟨hash, prog, signed, rej⟩ := t
  dsimp only at ht
  subst ht
  set T₀ : G.Tables := ⟨hash, prog ++ G.pubEntries xw.1 xw.2 m r e, signed ++ [m], []⟩
  have hT : ({ (⟨hash, prog, signed, []⟩ : G.Tables) with
      prog := prog ++ G.pubEntries xw.1 xw.2 m r e
      signed := signed ++ [m]
      rej := [] ++ G.hidEntries xw.1 xw.2 m r e } : G.Tables) =
      T₀.addRejs (G.hidEntries xw.1 xw.2 m r e) := by
    simp [T₀, Protocol.Tables.addRejs]
  rw [hT]
  refine (run_real_addRejs_flag_le xw _ _ T₀ false).trans ?_
  refine (MeasureTheory.measure_mono (fun y hy => hy)).trans
    ((MeasureTheory.measure_union_le _ _).trans (add_le_add ?_ ?_))
  · refine (ih _ T₀ rfl).trans (mul_le_mul_of_nonneg_right ?_ zero_le)
    have := length_pubEntries_le xw.1 xw.2 m r e
    simp only [T₀, List.length_append]
    exact_mod_cast Nat.mul_le_mul_left _ (by omega)
  · calc _ ≤ (OracleAdv.run (toOracle (realStep xw)) (k (.inr (G.sign xw.1 xw.2 m r e)))
            (T₀, false)).toOuterMeasure (⋃ i ∈ Finset.univ.filter
              (fun i => G.pub xw.1 xw.2 m r e i = false),
              {y | G.key xw.1 xw.2 m r e i ∈ y.2.1.keys}) := by
          refine MeasureTheory.measure_mono fun y hy => ?_
          obtain ⟨p, hp, hk⟩ := hy
          obtain ⟨i, hi, hpk⟩ := mem_hidEntries hp
          simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨i, hi, hpk ▸ hk⟩
      _ ≤ ∑ i ∈ Finset.univ.filter (fun i => G.pub xw.1 xw.2 m r e i = false),
            (OracleAdv.run (toOracle (realStep xw)) (k (.inr (G.sign xw.1 xw.2 m r e)))
              (T₀, false)).toOuterMeasure {y | G.key xw.1 xw.2 m r e i ∈ y.2.1.keys} :=
          MeasureTheory.measure_biUnion_finset_le _ _
      _ = ∑ i ∈ Finset.univ.filter (fun i => G.pub xw.1 xw.2 m r e i = false),
            (contRun xw k ⟨hash, prog, signed, []⟩ m
              (G.guessView xw.1 xw.2 m r e i)).toOuterMeasure
              {y | G.key xw.1 xw.2 m r e i ∈ y.2.1.keys} := by
          refine Finset.sum_congr rfl fun i hi => ?_
          have hi' : G.pub xw.1 xw.2 m r e i = false := (Finset.mem_filter.mp hi).2
          simp only [contRun, Protocol.guessView, hi', Protocol.view]
          rfl
      _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- A hash query in the induction of `run_real_flag_le`. -/
theorem flag_hash_step_le (xw : G.Stmt × G.Wit) {γ : ℝ≥0∞}
    (k : G.Answer → OracleAdv G.Query G.Answer α) (h q : ℕ) (t : G.Tables)
    (ht : t.rej = []) (key : G.Key)
    (ih : ∀ c (t' : G.Tables), t'.rej = [] →
      (OracleAdv.run (toOracle (realStep xw)) (k c) (t', false)).toOuterMeasure
        {y | y.2.2 = true} ≤
        ((q * G.μ * (t'.hash.length + t'.prog.length + h + G.μ * q) : ℕ) : ℝ≥0∞) * γ) :
    (OracleAdv.run (toOracle (realStep xw)) (.query (.inl key) k) (t, false)).toOuterMeasure
        {y | y.2.2 = true} ≤
      ((q * G.μ * (t.hash.length + t.prog.length + (h + 1) + G.μ * q) : ℕ) : ℝ≥0∞) * γ := by
  rw [OracleAdv.run_query]
  simp only [toOracle, realStep, realHashStep]
  cases hl : t.lookup key with
  | some e =>
    simp only [Step.toPMF, PMF.pure_bind]
    refine (ih _ t ht).trans (mul_le_mul_of_nonneg_right ?_ zero_le)
    exact_mod_cast Nat.mul_le_mul_left _ (by omega)
  | none =>
    have hr : lookupIn t.rej key = none := by rw [ht]; exact lookupIn_nil key
    simp only [hr, Step.toPMF, PMF.bind_map, Function.comp_def, PMF.toOuterMeasure_bind_apply]
    calc ∑' e, PMF.uniformOfFintype G.Ch e * (OracleAdv.run (toOracle (realStep xw))
          (k (.inl e)) ({ t with hash := t.hash ++ [(key, e)] }, false)).toOuterMeasure _
        ≤ ∑' e, PMF.uniformOfFintype G.Ch e *
          (((q * G.μ * (t.hash.length + t.prog.length + (h + 1) + G.μ * q) : ℕ) :
            ℝ≥0∞) * γ) := by
          refine ENNReal.tsum_le_tsum fun e => mul_le_mul_right ?_ _
          refine (ih _ { t with hash := t.hash ++ [(key, e)] } ht).trans (le_of_eq ?_)
          simp only [List.length_append, List.length_singleton]
          congr 3
          omega
      _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- The guess terms of a signing attempt in the induction of `run_real_flag_le`:
for each entry, the expectation over the randomness of the probability that its
point is defined at the end of the rest of the run is at most
`(L + μ + h + μ·q)·γ`. -/
theorem flag_guess_le (xw : G.Stmt × G.Wit) {γ : ℝ≥0∞} (hγ : G.KeyBoundAt xw.1 xw.2 γ)
    (k : G.Answer → OracleAdv G.Query G.Answer α) (h q : ℕ)
    (hk : ∀ r, IsQueryBound₂ (k r) h q) (t : G.Tables) (ht : t.rej = []) (m : G.Msg)
    (e : Fin G.μ → G.Ch) (i : Fin G.μ) :
    ∑' r, PMF.uniformOfFintype G.Rand r *
        (contRun xw k t m (G.guessView xw.1 xw.2 m r e i)).toOuterMeasure
          {y | G.key xw.1 xw.2 m r e i ∈ y.2.1.keys} ≤
      ((t.hash.length + t.prog.length + G.μ + h + G.μ * q : ℕ) : ℝ≥0∞) * γ := by
  refine tsum_guess_le xw.1 xw.2 hγ m e i (contRun xw k t m) _ fun r y hy => ?_
  rw [Protocol.Tables.length_keys]
  have h1 := run_real_support_size xw _ h q (hk _) _ y hy
  have h2 := length_guessView_le xw.1 xw.2 m r e i
  simp only [Protocol.Tables.size, List.length_append, ht, List.length_nil] at h1 ⊢
  omega

/-- A signing query in the induction of `run_real_flag_le`. -/
theorem flag_sign_step_le (xw : G.Stmt × G.Wit) {γ : ℝ≥0∞} (hγ : G.KeyBoundAt xw.1 xw.2 γ)
    (k : G.Answer → OracleAdv G.Query G.Answer α) (h q : ℕ)
    (hk : ∀ r, IsQueryBound₂ (k r) h q) (t : G.Tables) (ht : t.rej = []) (m : G.Msg)
    (ih : ∀ c (t' : G.Tables), t'.rej = [] →
      (OracleAdv.run (toOracle (realStep xw)) (k c) (t', false)).toOuterMeasure
        {y | y.2.2 = true} ≤
        ((q * G.μ * (t'.hash.length + t'.prog.length + h + G.μ * q) : ℕ) : ℝ≥0∞) * γ) :
    (OracleAdv.run (toOracle (realStep xw)) (.query (.inr m) k) (t, false)).toOuterMeasure
        {y | y.2.2 = true} ≤
      (((q + 1) * G.μ * (t.hash.length + t.prog.length + h + G.μ * (q + 1)) : ℕ) :
        ℝ≥0∞) * γ := by
  set L := t.hash.length + t.prog.length with hL
  set N := L + G.μ + h + G.μ * q with hN
  set B : ℝ≥0∞ := ((q * G.μ * N : ℕ) : ℝ≥0∞) * γ with hB
  have hterm := fun e r => flag_sign_term_le xw k h q t ht m e r ih
  have hsum := flag_guess_le xw hγ k h q hk t ht m
  rw [OracleAdv.run_query]
  simp only [toOracle, realStep, Step.toPMF, sampleVec_bind, PMF.toOuterMeasure_bind_apply]
  calc _ ≤ ∑' e, PMF.uniformOfFintype (Fin G.μ → G.Ch) e *
        ∑' r, PMF.uniformOfFintype G.Rand r * (B + ∑ i,
          (contRun xw k t m (G.guessView xw.1 xw.2 m r e i)).toOuterMeasure
            {y | G.key xw.1 xw.2 m r e i ∈ y.2.1.keys}) :=
        ENNReal.tsum_le_tsum fun e => mul_le_mul_right
          (ENNReal.tsum_le_tsum fun r => mul_le_mul_right (by
            refine (hterm e r).trans (add_le_add_left (mul_le_mul_of_nonneg_right ?_ zero_le) _)
            exact_mod_cast le_of_eq (by rw [hN])) _) _
    _ ≤ ∑' e, PMF.uniformOfFintype (Fin G.μ → G.Ch) e * (B + G.μ * (N * γ)) := by
        refine ENNReal.tsum_le_tsum fun e => mul_le_mul_right ?_ _
        simp only [mul_add, Finset.mul_sum]
        rw [ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul,
          Summable.tsum_finsetSum fun _ _ => ENNReal.summable]
        refine add_le_add_right ((Finset.sum_le_sum fun i _ => hsum e i).trans
          (le_of_eq ?_)) _
        simp [hN, hL]
    _ = B + G.μ * (N * γ) := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    _ = ((q * G.μ * N + G.μ * N : ℕ) : ℝ≥0∞) * γ := by
        rw [hB]; push_cast; ring
    _ = _ := by
        congr 2
        rw [hN, hL]
        ring

/-- **Collision bound.** For a pair `(x, w)` with key bound `γ`, from tables with no
hidden entry, with `L` entries and the flag cleared, a run of the real oracles
asking at most `h` hash and `q` signing queries sets the flag with probability at
most `q·μ·(L + h + μ·q)·γ`. -/
theorem run_real_flag_le {γ : ℝ≥0∞} (xw : G.Stmt × G.Wit) (hγ : G.KeyBoundAt xw.1 xw.2 γ)
    (A : OracleAdv G.Query G.Answer α) (h q : ℕ) (hA : IsQueryBound₂ A h q)
    (t : G.Tables) (ht : t.rej = []) :
    (OracleAdv.run (toOracle (realStep xw)) A (t, false)).toOuterMeasure {y | y.2.2 = true} ≤
      ((q * G.μ * (t.hash.length + t.prog.length + h + G.μ * q) : ℕ) : ℝ≥0∞) * γ := by
  induction A generalizing h q t with
  | ret a => simp [PMF.toOuterMeasure_pure_apply]
  | rand p k ih =>
    rw [OracleAdv.run_rand, PMF.toOuterMeasure_bind_apply]
    calc ∑' b, p b * (OracleAdv.run (toOracle (realStep xw)) (k b) (t, false)).toOuterMeasure _
        ≤ ∑' b, p b *
            (((q * G.μ * (t.hash.length + t.prog.length + h + G.μ * q) : ℕ) : ℝ≥0∞) * γ) :=
          ENNReal.tsum_le_tsum fun b => mul_le_mul_right (ih b h q (hA b) t ht) _
      _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  | query d k ih =>
    cases d with
    | inl key =>
      cases h with
      | zero => exact hA.elim
      | succ h => exact flag_hash_step_le xw k h q t ht key fun c t' ht' => ih c h q (hA c) t' ht'
    | inr m =>
      cases q with
      | zero => exact hA.elim
      | succ q =>
        exact flag_sign_step_le xw hγ k h q hA t ht m fun c t' ht' => ih c h q (hA c) t' ht'

end Flag

/-! ## The game as an average over generated pairs -/

section Game

variable {G : Protocol}

theorem isQueryBound₂_verifyQueries (x : G.Stmt) (m : G.Msg) (σ : G.Sig) (h q n : ℕ)
    (acc : List G.Ch) : IsQueryBound₂ (verifyQueries x m σ n acc) (h + n) q := by
  induction n generalizing acc with
  | zero => trivial
  | succ n ih =>
    intro a
    cases a with
    | inl e => exact ih _
    | inr _ => trivial

theorem isQueryBound₂_withVerify (x : G.Stmt) (A : OracleAdv G.Query G.Answer G.Forgery)
    (h q : ℕ) (hA : IsQueryBound₂ A h q) : IsQueryBound₂ (withVerify x A) (h + G.V) q := by
  induction A generalizing h q with
  | ret y =>
    obtain ⟨m, σ⟩ := y
    exact isQueryBound₂_verifyQueries x m σ h q G.V []
  | rand p k ih => exact fun b => ih b h q (hA b)
  | query d k ih =>
    cases d with
    | inl key =>
      cases h with
      | zero => exact hA.elim
      | succ h =>
        have : h + 1 + G.V = h + G.V + 1 := by omega
        rw [this]
        exact fun r => ih r h q (hA r)
    | inr m =>
      cases q with
      | zero => exact hA.elim
      | succ q => exact fun r => ih r h q (hA r)

/-- The advantage in a game built by `gameDist` as an average over generated
pairs. -/
theorem prTrue_gameDist (O : G.Stmt × G.Wit → G.Tables × Bool → G.Query →
    Step G.Answer (G.Tables × Bool) G.Ch) {qH qS : ℕ} (A : G.Adversary qH qS) :
    prTrue (PRPPRF.pmfGame (gameDist O A)) Heap.empty =
      ∑' xw, G.gen xw *
        (OracleAdv.run (toOracle (O xw)) (withVerify xw.1 (A.run xw.1))
          (Protocol.Tables.empty, false)).toOuterMeasure {y | wins xw.1 y = true} := by
  rw [prTrue_pmfGame]
  simp only [gameDist, PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_map_apply]
  rfl

end Game

end CatCrypt.Crypto.FiatShamirROM
