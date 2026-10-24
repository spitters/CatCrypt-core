/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OracleForkingLemma
public import CatCryptCore.Crypto.OracleSimulation

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
answer is `G.sign x w m r v`, a signature or nothing. An entry is evaluated
(`G.ev i`) when the signer answers it by an honest query to `H`, and programmed
otherwise. The simulator knows only the statement: for an evaluated entry it queries
`H` at the point `G.simKey x m s v i`, and `G.simulate x m v s` computes the
programmed public entries and the answer from the values `v`, which are the oracle
answers at the evaluated entries. The verifier of a signature `σ` on `m` reads `H`
at `G.V` points, the next one `G.vkey x m σ vs` from the values `vs` read so far,
and decides with `G.verify x m σ vs`.

The EUF-CMA game samples `(x, w)` from the generator `G.gen` and runs an adaptive
oracle adversary (`OracleAdv`) on `x` with hash queries `inl k` and signing queries
`inr m`, at most `qH` and `qS` of them on every path
(`OracleForking.IsQueryBound₂`). The challenger keeps the oracle state
`G.Tables × Bool`:

* `hash` — the random-oracle entries created by hash queries and by evaluated
  public entries, in creation order;
* `prog` — the programmed public entries created by signing attempts;
* `signed` — the messages submitted to the signing oracle;
* `rej` — the hidden entries created by signing attempts;
* the flag — set when a query needs the oracle value at the point of a hidden
  entry only, or when a programmed or hidden entry of a signing attempt lands on a
  point already defined.

A hash query returns the recorded value of its point or samples a fresh uniform
value and records it. The real signing oracle samples the values `e` and the
randomness `r`; an evaluated entry takes the recorded value of its point when there
is one and its value in `e` otherwise, a programmed entry its value in `e`; the new
evaluated public entries go to `hash`, the programmed public ones to `prog` and the
hidden ones to `rej`. The simulated signing oracle knows only `x`: it samples `e`
and `s`, answers the simulator's queries from the tables and `e`, records the fresh
answers in `hash`, and records the public entries of `G.simulate x m u s` on those
answers `u` in `prog`, setting the flag for an entry whose point is already defined.
At the end the challenger reads the verifier's points for the forgery `(m*, σ*)`,
and the adversary wins when the verifier accepts and `m*` was never signed.

A Σ-protocol `P : Sigma` with explicit prover randomness, simulator randomness and
an acceptance test on responses is the instance `P.toProtocol M` with one entry
at the point `(P.commit x w r, m)`, public when the response is accepted.

## Main definitions

* `effVal`, `effVec` — the values of the entries of an attempt against oracles
* `Protocol` — a multi-round public-coin protocol with its random-oracle entries
* `Protocol.vals`, `Protocol.trace`, `Protocol.simTrace` — the values of an attempt
  against a visible oracle, its trace (evaluated public entries, programmed public
  entries and answer), and the trace of the simulator
* `Protocol.guessView` — the trace from which the point of an entry is guessed
* `Protocol.StatHVZKAt x w δ`, `Protocol.KeyBoundAt x w Γ` — statistical HVZK on
  traces, and the bound `Γ` on guessing the points of the programmed and hidden
  entries of an attempt, at one pair
* `Protocol.Classes` — key classes: a partition of the oracle points with the class
  of each entry and of each verifier point; `Protocol.Classes.unit`, the counts
  `μc`, `Vc` and the per-class query cost `hashCost`
* `Protocol.KeyBoundClsAt κ x w Γ` — the key bound class by class, on the entries
  charged by `Protocol.charged`: the hidden ones, and the programmed public ones on
  attempts whose hidden points are undefined in the visible oracle
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
* `run_real_flag_le` — for a pair `(x, w)` with key bound `Γ`, from tables with `L`
  entries and no hidden entry, a run with at most `h` hash and `q` signing queries
  sets the flag with probability at most `q·(L + h + μ·q)·Γ`
* `run_real_flag_le_cls` — for a pair with class-wise key bound `Γ`, from tables
  with `L_c` points of class `c` and no hidden entry, a run with at most `q` signing
  queries and hash queries of cost at most `h_c` for each class `c` sets the flag
  with probability at most `Σ_c q·(L_c + h_c + μc c·q)·Γ c`
* `Protocol.KeyBoundAt.toCls` — a key bound is a class-wise key bound for every
  partition

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
    (PMF.uniformFintype P.Rand).map (fun r => (P.commit x w r, P.respond x w r e)) =
      (PMF.uniformFintype P.SimRand).map (P.simulate x e)

/-- **Commitment bound at one pair.** For the pair `(x, w)`, each commitment value
has probability at most `γ` under uniform prover randomness. -/
def CommitBoundAt (x : P.Stmt) (w : P.Wit) (γ : ℝ≥0∞) : Prop :=
  ∀ a, (PMF.uniformFintype P.Rand).toOuterMeasure {r | P.commit x w r = a} ≤ γ

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
  liftPMF (P.gen.bind fun xw => (B xw.1).map fun w' => decide (P.rel xw.1 w'))

/-- The advantage in the relation game. -/
noncomputable def relAdvantage (B : P.Stmt → PMF P.Wit) : ℝ≥0∞ :=
  prTrue (P.relGame B) Heap.empty

end Sigma

/-! ## The values of a signing attempt -/

section Eff

variable {μ : ℕ} {K C : Type}

/-- The value of entry `i` of an attempt against the oracles `look`: the value of
`look i` at its point when defined, and `e i` otherwise; the point reads the values
of the entries before `i`. -/
def effVal (look : Fin μ → K → Option C) (key : (Fin μ → C) → Fin μ → K) (e : Fin μ → C)
    (i : Fin μ) : C :=
  (look i (key (fun j => if j < i then effVal look key e j else e j) i)).getD (e i)
termination_by i.val
decreasing_by exact ‹j < i›

/-- The values of the entries of an attempt against the oracles `look`. -/
def effVec (look : Fin μ → K → Option C) (key : (Fin μ → C) → Fin μ → K) (e : Fin μ → C) :
    Fin μ → C :=
  fun i => effVal look key e i

end Eff

/-! ## Multi-round public-coin protocols -/

/-- A public-coin protocol made non-interactive by a random oracle from `Key` to
uniform values `Ch`, presented by the oracle entries of a signing attempt. An
attempt on the message `m` for the pair `(x, w)` with randomness `r` and oracle
values `v` defines `μ` entries, the entry `i` at the point `key x w m r v i` with
value `v i`; it is public when `pub x w m r v i` holds and hidden otherwise, and
the answer of the attempt is `sign x w m r v`. An entry `i` with `ev i` is
evaluated (answered by an honest oracle query) and the others are programmed. The
simulator queries the oracle at the points `simKey x m s v i` and gives the
programmed public entries and the answer from the statement and the values. The
verifier of `σ` on `m` reads the oracle at `V` points, each from the values read
before. -/
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
  /-- The simulator: the programmed public entries and the answer from the values;
  the value of an evaluated entry is the oracle answer at its simulator point. -/
  simulate : Stmt → Msg → (Fin μ → Ch) → SimRand → List (Key × Ch) × Option Sig
  /-- Entry `i` is evaluated: the signer answers it by an honest query to the random
  oracle. The other entries are programmed. Every entry is programmed by default. -/
  ev : Fin μ → Bool := fun _ => false
  /-- The point at which the simulator queries the random oracle for entry `i`, from
  the statement, the message, the simulator randomness and the values `v`, or
  nothing. Nothing by default. -/
  simKey : Stmt → Msg → SimRand → (Fin μ → Ch) → Fin μ → Option Key :=
    fun _ _ _ _ _ => none
  /-- The simulator point of entry `i` reads only the values of the entries before
  `i` and of the programmed entries. -/
  simKey_causal : ∀ x m s (v v' : Fin μ → Ch) (i : Fin μ),
    (∀ j, j < i ∨ ev j = false → v j = v' j) → simKey x m s v i = simKey x m s v' i := by
    intros; rfl
  /-- The simulator queries the random oracle only for evaluated entries. -/
  simKey_ev : ∀ x m s (v : Fin μ → Ch) (i : Fin μ), (simKey x m s v i).isSome → ev i = true := by
    intro _ _ _ _ _ h; simp at h
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

/-- The view of an attempt: its programmed public entries and its answer. -/
abbrev View := List (G.Key × G.Ch) × Option G.Sig

/-- The trace of an attempt: its evaluated public entries and its view. -/
abbrev Trace := List (G.Key × G.Ch) × G.View

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

/-- The entries `i` of an attempt with the values `v` that satisfy `p`, in order. -/
def entries (x : G.Stmt) (w : G.Wit) (m : G.Msg) (r : G.Rand) (v : Fin G.μ → G.Ch)
    (p : Fin G.μ → Bool) : List (G.Key × G.Ch) :=
  ((List.finRange G.μ).filter p).map fun i => (G.key x w m r v i, v i)

/-- The programmed public entries of an attempt with the values `v`. -/
def pubEntries (x : G.Stmt) (w : G.Wit) (m : G.Msg) (r : G.Rand) (v : Fin G.μ → G.Ch) :
    List (G.Key × G.Ch) :=
  G.entries x w m r v fun i => !G.ev i && G.pub x w m r v i

/-- The evaluated public entries of an attempt with the values `v`. -/
def evEntries (x : G.Stmt) (w : G.Wit) (m : G.Msg) (r : G.Rand) (v : Fin G.μ → G.Ch) :
    List (G.Key × G.Ch) :=
  G.entries x w m r v fun i => G.ev i && G.pub x w m r v i

/-- The hidden entries of an attempt with the values `v`. -/
def hidEntries (x : G.Stmt) (w : G.Wit) (m : G.Msg) (r : G.Rand) (v : Fin G.μ → G.Ch) :
    List (G.Key × G.Ch) :=
  G.entries x w m r v fun i => !G.pub x w m r v i

/-- The view of an attempt with the values `v`: its programmed public entries and
its answer. -/
def view (x : G.Stmt) (w : G.Wit) (m : G.Msg) (r : G.Rand) (v : Fin G.μ → G.Ch) : G.View :=
  (G.pubEntries x w m r v, G.sign x w m r v)

/-- The trace of an attempt with the values `v`: its evaluated public entries and
its view. -/
def trace (x : G.Stmt) (w : G.Wit) (m : G.Msg) (r : G.Rand) (v : Fin G.μ → G.Ch) : G.Trace :=
  (G.evEntries x w m r v, G.view x w m r v)

/-- Entry `i` of an attempt with the values `v` is programmed or hidden: such an
entry sets the flag when its point is already defined. -/
def flagging (x : G.Stmt) (w : G.Wit) (m : G.Msg) (r : G.Rand) (v : Fin G.μ → G.Ch)
    (i : Fin G.μ) : Bool :=
  !G.ev i || !G.pub x w m r v i

/-- The values of an attempt against the oracle `look`: an evaluated entry takes
the value of `look` at its point when defined and its value in `e` otherwise; a
programmed entry takes its value in `e`. -/
def vals (look : G.Key → Option G.Ch) (x : G.Stmt) (w : G.Wit) (m : G.Msg) (r : G.Rand)
    (e : Fin G.μ → G.Ch) : Fin G.μ → G.Ch :=
  effVec (fun i => if G.ev i then look else fun _ => none) (G.key x w m r) e

/-- The values of an honest attempt against the oracle `look`: every entry takes the
value of `look` at its point when defined and its value in `e` otherwise. -/
def honestVals (look : G.Key → Option G.Ch) (x : G.Stmt) (w : G.Wit) (m : G.Msg)
    (r : G.Rand) (e : Fin G.μ → G.Ch) : Fin G.μ → G.Ch :=
  effVec (fun _ => look) (G.key x w m r) e

/-- The hidden entries of an attempt with the values `v` are at points undefined in
`look`. -/
def hidFresh (look : G.Key → Option G.Ch) (x : G.Stmt) (w : G.Wit) (m : G.Msg) (r : G.Rand)
    (v : Fin G.μ → G.Ch) : Bool :=
  (List.finRange G.μ).all fun i => G.pub x w m r v i || (look (G.key x w m r v i)).isNone

/-- The trace that determines the guess of the point of entry `i` of the attempt
with the values against `look`: the trace of the attempt when the entry is hidden
at a point undefined in `look`, and the empty trace otherwise. -/
def guessView (look : G.Key → Option G.Ch) (x : G.Stmt) (w : G.Wit) (m : G.Msg) (r : G.Rand)
    (e : Fin G.μ → G.Ch) (i : Fin G.μ) : G.Trace :=
  if G.pub x w m r (G.vals look x w m r e) i ||
      (look (G.key x w m r (G.vals look x w m r e) i)).isSome then ([], [], none)
  else G.trace x w m r (G.vals look x w m r e)

/-- The values of a simulated attempt against the oracle `look`: an entry with a
simulator point takes the value of `look` there when defined, and its value in `e`
otherwise. -/
def simVals (look : G.Key → Option G.Ch) (x : G.Stmt) (m : G.Msg) (s : G.SimRand)
    (e : Fin G.μ → G.Ch) : Fin G.μ → G.Ch :=
  effVec (fun _ k => k.bind look) (G.simKey x m s) e

/-- The trace of a simulated attempt against the oracle `look`: the entries at the
simulator points with their values, and the output of `simulate` on those values. -/
def simTrace (look : G.Key → Option G.Ch) (x : G.Stmt) (m : G.Msg) (e : Fin G.μ → G.Ch)
    (s : G.SimRand) : G.Trace :=
  ((List.finRange G.μ).filterMap fun i =>
      (G.simKey x m s (G.simVals look x m s e) i).map fun k => (k, G.simVals look x m s e i),
    G.simulate x m (G.simVals look x m s e) s)

/-- **Key bound at one pair.** For the pair `(x, w)`, every message, every oracle
`look` and every randomized guesser `Q` on traces, the expected number of
programmed or hidden entries of the attempt against `look` whose point the guess
from `guessView` hits, over uniform values and uniform randomness, is at most `Γ`. -/
def KeyBoundAt (x : G.Stmt) (w : G.Wit) (Γ : ℝ≥0∞) : Prop :=
  ∀ (m : G.Msg) (look : G.Key → Option G.Ch) (Q : G.Trace → PMF G.Key),
    ∑' e, PMF.uniformFintype (Fin G.μ → G.Ch) e * ∑' r, PMF.uniformFintype G.Rand r *
      ∑ i, (if G.flagging x w m r (G.vals look x w m r e) i then
        Q (G.guessView look x w m r e i) (G.key x w m r (G.vals look x w m r e) i) else 0) ≤ Γ

/-- **Statistical honest-verifier zero knowledge at one pair** with distance `δ`.
For the pair `(x, w)`, every message `m`, every oracle `look` and every test `g`
with values in `[0, 1]` on traces, the expectation of `g` on the trace of the
attempt against `look`, restricted to the attempts whose hidden points are undefined
in `look`, under uniform values and randomness, is at most its expectation on the
simulated trace against `look` under uniform values and simulator randomness, plus
`δ`. -/
def StatHVZKAt (x : G.Stmt) (w : G.Wit) (δ : ℝ≥0∞) : Prop :=
  ∀ (m : G.Msg) (look : G.Key → Option G.Ch) (g : G.Trace → ℝ≥0∞), (∀ y, g y ≤ 1) →
    ∑' e, PMF.uniformFintype (Fin G.μ → G.Ch) e * ∑' r, PMF.uniformFintype G.Rand r *
      (if G.hidFresh look x w m r (G.vals look x w m r e) then
        g (G.trace x w m r (G.vals look x w m r e)) else 0) ≤
    ∑' e, PMF.uniformFintype (Fin G.μ → G.Ch) e * ∑' s, PMF.uniformFintype G.SimRand s *
      g (G.simTrace look x m e s) + δ

/-- **Key classes.** A partition of the oracle points into finitely many classes
`ι` by `cls`, such that the point of entry `i` of every attempt is in the class
`ecls i` and the `j`-th point the verifier reads is in the class `vcls j`. Points
of different classes never coincide, so collisions are counted class by class. -/
structure Classes : Type 1 where
  /-- The classes. -/
  ι : Type
  [finι : Fintype ι]
  [decι : DecidableEq ι]
  /-- The class of a point. -/
  cls : G.Key → ι
  /-- The class of the point of entry `i`. -/
  ecls : Fin G.μ → ι
  /-- The point of entry `i` of every attempt is in the class `ecls i`. -/
  key_cls : ∀ x w m r (v : Fin G.μ → G.Ch) (i : Fin G.μ), cls (G.key x w m r v i) = ecls i
  /-- The class of the `j`-th point the verifier reads. -/
  vcls : Fin G.V → ι
  /-- The point the verifier reads after the values `vs` is in the class
  `vcls vs.length`. -/
  vkey_cls : ∀ x m σ (vs : List G.Ch) (h : vs.length < G.V),
    cls (G.vkey x m σ vs) = vcls ⟨vs.length, h⟩

attribute [instance] Classes.finι Classes.decι

/-- Entry `i` of an attempt with the values `v` against `look` is charged in the
class-wise key bound: it is programmed or hidden, and it is hidden or the hidden
entries of the attempt are at points undefined in `look`. -/
def charged (look : G.Key → Option G.Ch) (x : G.Stmt) (w : G.Wit) (m : G.Msg) (r : G.Rand)
    (v : Fin G.μ → G.Ch) (i : Fin G.μ) : Bool :=
  G.flagging x w m r v i && (!G.pub x w m r v i || G.hidFresh look x w m r v)

/-- **Class-wise key bound at one pair.** For the pair `(x, w)`, every class `c`,
every message, every oracle `look` and every randomized guesser `Q` on traces, the
expected number of charged entries of class `c` of the attempt against `look` whose
point the guess from `guessView` hits, over uniform values and uniform randomness,
is at most `Γ c`. -/
def KeyBoundClsAt (κ : G.Classes) (x : G.Stmt) (w : G.Wit) (Γ : κ.ι → ℝ≥0∞) : Prop :=
  ∀ (c : κ.ι) (m : G.Msg) (look : G.Key → Option G.Ch) (Q : G.Trace → PMF G.Key),
    ∑' e, PMF.uniformFintype (Fin G.μ → G.Ch) e * ∑' r, PMF.uniformFintype G.Rand r *
      ∑ i ∈ Finset.univ.filter (fun i => κ.ecls i = c),
        (if G.charged look x w m r (G.vals look x w m r e) i then
          Q (G.guessView look x w m r e i) (G.key x w m r (G.vals look x w m r e) i) else 0) ≤
      Γ c

namespace Classes

/-- The partition into one class. -/
@[reducible] def unit : G.Classes where
  ι := Unit
  cls _ := ()
  ecls _ := ()
  key_cls _ _ _ _ _ _ := rfl
  vcls _ := ()
  vkey_cls _ _ _ _ _ := rfl

variable {G} (κ : G.Classes)

/-- The number of entries of an attempt in the class `c`. -/
def μc (c : κ.ι) : ℕ := (Finset.univ.filter fun i => κ.ecls i = c).card

/-- The number of verifier points in the class `c`. -/
def Vc (c : κ.ι) : ℕ := (Finset.univ.filter fun j => κ.vcls j = c).card

/-- The cost of a query for the class `c`: one for a hash query at a point of
class `c`, zero otherwise. -/
def hashCost (c : κ.ι) : G.Query → ℕ :=
  Sum.elim (fun k => if κ.cls k = c then 1 else 0) fun _ => 0

/-- The number of points of class `c` in `l`. -/
def count (l : List G.Key) (c : κ.ι) : ℕ := (l.filter fun k => κ.cls k = c).length

theorem count_append (l l' : List G.Key) (c : κ.ι) :
    κ.count (l ++ l') c = κ.count l c + κ.count l' c := by
  simp [count]

theorem count_le_of_sublist {l l' : List G.Key} (h : l.Sublist l') (c : κ.ι) :
    κ.count l c ≤ κ.count l' c :=
  (h.filter _).length_le

theorem length_filter_finRange_eq_μc (c : κ.ι) :
    ((List.finRange G.μ).filter fun i => κ.ecls i = c).length = κ.μc c := by
  rw [μc, Fin.univ_def]
  rfl

/-- The points of class `c` among the entries of an attempt satisfying `p`. -/
theorem count_entries (x : G.Stmt) (w : G.Wit) (m : G.Msg) (r : G.Rand) (v : Fin G.μ → G.Ch)
    (p : Fin G.μ → Bool) (c : κ.ι) :
    κ.count ((G.entries x w m r v p).map Prod.fst) c =
      (((List.finRange G.μ).filter fun i => κ.ecls i = c).filter p).length := by
  simp only [count, Protocol.entries, List.map_map, List.filter_map, List.length_map,
    List.filter_filter]
  congr 1
  refine List.filter_congr fun i _ => ?_
  simp [κ.key_cls, Bool.and_comm]

/-- The evaluated public, programmed public and hidden entries of an attempt have
`μc c` points of class `c` in all. -/
theorem count_trace_entries (x : G.Stmt) (w : G.Wit) (m : G.Msg) (r : G.Rand)
    (v : Fin G.μ → G.Ch) (c : κ.ι) :
    κ.count ((G.evEntries x w m r v).map Prod.fst) c +
      κ.count ((G.pubEntries x w m r v).map Prod.fst) c +
      κ.count ((G.hidEntries x w m r v).map Prod.fst) c = κ.μc c := by
  simp only [Protocol.evEntries, Protocol.pubEntries, Protocol.hidEntries, count_entries,
    ← length_filter_finRange_eq_μc]
  have h1 := List.length_eq_length_filter_add (G.pub x w m r v)
    (l := (List.finRange G.μ).filter fun i => κ.ecls i = c)
  have h2 := List.length_eq_length_filter_add G.ev
    (l := ((List.finRange G.μ).filter fun i => κ.ecls i = c).filter (G.pub x w m r v))
  simp only [List.filter_filter, Bool.and_assoc] at h1 h2 ⊢
  omega

@[simp] theorem unit_μc : (unit G).μc () = G.μ := by simp [μc, unit]

@[simp] theorem unit_Vc : (unit G).Vc () = G.V := by simp [Vc, unit]

@[simp] theorem unit_count (l : List G.Key) : (unit G).count l () = l.length := by
  simp [count, unit]

end Classes

variable {G}

/-- A key bound is a class-wise key bound with the same bound for every class. -/
theorem KeyBoundAt.toCls {x : G.Stmt} {w : G.Wit} {Γ : ℝ≥0∞} (h : G.KeyBoundAt x w Γ)
    (κ : G.Classes) : G.KeyBoundClsAt κ x w fun _ => Γ := by
  intro c m look Q
  refine le_trans ?_ (h m look Q)
  refine ENNReal.tsum_le_tsum fun e => mul_le_mul_right
    (ENNReal.tsum_le_tsum fun r => mul_le_mul_right ?_ _) _
  refine (Finset.sum_le_sum fun i _ => ?_).trans
    (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _))
  unfold charged
  cases G.flagging x w m r (G.vals look x w m r e) i <;> simp only [Bool.false_and, Bool.true_and,
    Bool.false_eq_true, ite_false, ite_true, le_refl]
  split_ifs <;> simp

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

/-- The tables `t` with the entries of `l` at points undefined in `t` recorded in
`hash`: the answers of honest oracle queries. -/
def hashAll (t : G.Tables) (l : List (G.Key × G.Ch)) : G.Tables :=
  { t with hash := t.hash ++ l.filter fun p => (t.lookup p.1).isNone }

/-- The tables after a signing attempt on `m` with the trace `tr` from `t`: the
fresh evaluated public entries recorded in `hash`, the programmed public entries in
`prog`, and `m` in `signed`. -/
def traceTables (t : G.Tables) (m : G.Msg) (tr : G.Trace) : G.Tables :=
  { hashAll t tr.1 with prog := t.prog ++ tr.2.1, signed := t.signed ++ [m] }

/-- The real signing oracle on `m` for the pair `(x, w)`, from the sampled values
`e` and randomness `r`. Every entry takes the recorded value at its point when
there is one and its value in `e` otherwise (`Protocol.honestVals`). The evaluated public entries at points without a value
visible to the adversary are recorded in `hash`, the programmed public entries at
undefined points in `prog`, and the hidden entries at undefined points in `rej`.
The flag is set when a programmed or hidden entry lands on a defined point, or an
evaluated public entry on the point of a hidden entry only. -/
def realSignOut (x : G.Stmt) (w : G.Wit) (t : G.Tables) (b : Bool) (m : G.Msg)
    (e : Fin G.μ → G.Ch) (r : G.Rand) : G.Answer × (G.Tables × Bool) :=
  let v := G.honestVals t.lookupAll x w m r e
  (.inr (G.sign x w m r v),
    ({ hashAll t (G.evEntries x w m r v) with
        prog := t.prog ++ (G.pubEntries x w m r v).filter fun p => (t.lookupAll p.1).isNone
        signed := t.signed ++ [m]
        rej := t.rej ++ (G.hidEntries x w m r v).filter fun p => (t.lookupAll p.1).isNone },
      b || (List.finRange G.μ).any fun i =>
        if G.flagging x w m r v i then (t.lookupAll (G.key x w m r v i)).isSome
        else (t.lookup (G.key x w m r v i)).isNone &&
          (lookupIn t.rej (G.key x w m r v i)).isSome))

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

/-- The signing answer with the trace `tr` on `m`: the fresh evaluated entries of
`tr` are recorded in `hash`, then its view is answered and programmed by
`programOut`. -/
def traceOut (t : G.Tables) (b : Bool) (m : G.Msg) (tr : G.Trace) :
    G.Answer × (G.Tables × Bool) :=
  programOut (hashAll t tr.1) b m tr.2

/-- The simulated signing oracle on `m` for the statement `x`, from the sampled
values `e` and simulator randomness `s`: the simulated trace against the visible
oracle (`Protocol.simTrace`) is answered by `traceOut`. -/
def simSignOut (x : G.Stmt) (t : G.Tables) (b : Bool) (m : G.Msg) (e : Fin G.μ → G.Ch)
    (s : G.SimRand) : G.Answer × (G.Tables × Bool) :=
  traceOut t b m (G.simTrace t.lookup x m e s)

variable (G) in
/-- Uniform values for the entries of an attempt followed by an independent uniform
value of `β`, mapped by `F`. -/
noncomputable def sampleVec {β γ : Type} [Fintype β] [Nonempty β]
    (F : (Fin G.μ → G.Ch) → β → γ) : PMF γ :=
  (PMF.uniformFintype (Fin G.μ → G.Ch)).bind fun e =>
    (PMF.uniformFintype β).map fun y => F e y

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
  liftPMF (gameDist realStep A)

/-- The EUF-CMA advantage in the random-oracle model. -/
noncomputable def eufcmaAdvantage {qH qS : ℕ} (A : G.Adversary qH qS) : ℝ≥0∞ :=
  prTrue (eufcmaGame A) Heap.empty

/-- The EUF-CMA game with the simulated signing oracle. -/
noncomputable def simGame {qH qS : ℕ} (A : G.Adversary qH qS) : SPComp Bool :=
  liftPMF (gameDist (fun xw => simStep xw.1) A)

/-- The advantage in the simulated game. -/
noncomputable def simAdvantage {qH qS : ℕ} (A : G.Adversary qH qS) : ℝ≥0∞ :=
  prTrue (simGame A) Heap.empty

end Games

/-! ## The values of an attempt -/

section EffLemmas

variable {μ : ℕ} {K C : Type} (look : Fin μ → K → Option C) (key : (Fin μ → C) → Fin μ → K)

/-- When no oracle is defined at the points of the attempt, its values are `e`. -/
theorem effVec_of_forall_none (e : Fin μ → C) (h : ∀ (v : Fin μ → C) i, look i (key v i) = none) :
    effVec look key e = e := by
  funext i
  change effVal look key e i = e i
  rw [effVal, h]
  rfl

variable (hk : ∀ (v v' : Fin μ → C) (i : Fin μ), (∀ j, j < i → v j = v' j) → key v i = key v' i)
  (e : Fin μ → C)

include hk in
theorem effVal_eq (i : Fin μ) :
    effVal look key e i = (look i (key (effVec look key e) i)).getD (e i) := by
  rw [effVal]
  congr 2
  exact hk _ _ i fun j hj => by simp [hj, effVec]

include hk in
/-- The values of an attempt are the only solution of their defining equations. -/
theorem effVec_unique (v : Fin μ → C) (hv : ∀ i, v i = (look i (key v i)).getD (e i)) :
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
theorem effVec_of_none (h : ∀ i, look i (key e i) = none) : effVec look key e = e :=
  (effVec_unique look key hk e e fun i => by rw [h i]; rfl).symm

include hk in
/-- When no point of the attempt is defined, its values are `e`, and no point of the
attempt with the values `e` is defined. -/
theorem effVec_eq_of_none (h : ∀ i, look i (key (effVec look key e) i) = none) :
    effVec look key e = e := by
  funext i
  change effVal look key e i = e i
  rw [effVal_eq look key hk e i, h i]
  rfl

include hk in
/-- Two oracles that agree at the points of the attempt against the first give the
same values. -/
theorem effVec_congr (look' : Fin μ → K → Option C)
    (h : ∀ i, look' i (key (effVec look key e) i) = look i (key (effVec look key e) i)) :
    effVec look' key e = effVec look key e :=
  (effVec_unique look' key hk e _ fun i => by
    rw [h i]
    exact effVal_eq look key hk e i).symm

end EffLemmas

/-! ## Attempts without evaluated entries -/

namespace Protocol

variable {G : Protocol}

/-- When every entry is programmed, the values of an attempt are the sampled ones. -/
theorem vals_of_ev_false (hev : ∀ i, G.ev i = false) (look : G.Key → Option G.Ch)
    (x : G.Stmt) (w : G.Wit) (m : G.Msg) (r : G.Rand) (e : Fin G.μ → G.Ch) :
    G.vals look x w m r e = e :=
  effVec_of_forall_none _ _ e fun _ i => by simp [hev i]

/-- When every entry is programmed, an attempt has no evaluated public entry. -/
theorem evEntries_of_ev_false (hev : ∀ i, G.ev i = false) (x : G.Stmt) (w : G.Wit)
    (m : G.Msg) (r : G.Rand) (v : Fin G.μ → G.Ch) : G.evEntries x w m r v = [] := by
  simp [evEntries, entries, hev]

/-- When the simulator queries no point, its values are the sampled ones. -/
theorem simVals_of_simKey_none {x : G.Stmt} {m : G.Msg} {s : G.SimRand}
    (h : ∀ v i, G.simKey x m s v i = none) (look : G.Key → Option G.Ch) (e : Fin G.μ → G.Ch) :
    G.simVals look x m s e = e :=
  effVec_of_forall_none _ _ e fun v i => by simp [h v i]

/-- When the simulator queries no point, its trace is the output of `simulate` on the
sampled values. -/
theorem simTrace_of_simKey_none {x : G.Stmt} {m : G.Msg} {s : G.SimRand}
    (h : ∀ v i, G.simKey x m s v i = none) (look : G.Key → Option G.Ch) (e : Fin G.μ → G.Ch) :
    G.simTrace look x m e s = ([], G.simulate x m e s) := by
  simp [simTrace, simVals_of_simKey_none h, h]

end Protocol

/-! ## The values of a simulated attempt -/

namespace Protocol

variable {G : Protocol} (look : G.Key → Option G.Ch) (x : G.Stmt) (m : G.Msg)
  (s : G.SimRand)

/-- The simulator queries no point for a programmed entry. -/
theorem simKey_eq_none_of_ev_false (v : Fin G.μ → G.Ch) {i : Fin G.μ} (h : G.ev i = false) :
    G.simKey x m s v i = none := by
  cases hk : G.simKey x m s v i with
  | none => rfl
  | some k =>
    have := G.simKey_ev x m s v i (by simp [hk])
    simp [h] at this

/-- A programmed entry of a simulated attempt takes its sampled value. -/
theorem simVals_apply_of_ev_false (e : Fin G.μ → G.Ch) {i : Fin G.μ} (h : G.ev i = false) :
    G.simVals look x m s e i = e i := by
  change effVal _ _ e i = e i
  rw [effVal, simKey_eq_none_of_ev_false x m s _ h]
  rfl

/-- The value of the entry `i` of a simulated attempt is the value of `look` at its
simulator point when defined, and its sampled value otherwise. -/
theorem simVals_apply (e : Fin G.μ → G.Ch) (i : Fin G.μ) :
    G.simVals look x m s e i =
      ((G.simKey x m s (G.simVals look x m s e) i).bind look).getD (e i) := by
  change effVal _ _ e i = _
  rw [effVal]
  congr 2
  refine G.simKey_causal x m s _ _ i fun j hj => ?_
  by_cases hji : j < i
  · simp only [hji, ite_true]
    rfl
  · simp only [hji, ite_false]
    exact (simVals_apply_of_ev_false look x m s e (hj.resolve_left hji)).symm

variable {look x m s}

/-- Changing the sampled value of an evaluated entry `i` changes no value of a
programmed entry or of an entry before `i`. -/
theorem simVals_update_apply {i : Fin G.μ} (hi : G.ev i = true) (e : Fin G.μ → G.Ch)
    (c : G.Ch) (j : Fin G.μ) (hj : j < i ∨ G.ev j = false) :
    G.simVals look x m s (Function.update e i c) j = G.simVals look x m s e j := by
  have hprog : ∀ j', G.ev j' = false →
      G.simVals look x m s (Function.update e i c) j' = G.simVals look x m s e j' := by
    intro j' hj'
    have hne : j' ≠ i := by
      rintro rfl
      simp [hi] at hj'
    rw [simVals_apply_of_ev_false look x m s _ hj', simVals_apply_of_ev_false look x m s _ hj',
      Function.update_of_ne hne]
  induction j using WellFoundedLT.induction with
  | _ j ih =>
    rcases hj with hj | hj
    · rw [simVals_apply look x m s (Function.update e i c) j, simVals_apply look x m s e j,
        Function.update_of_ne (ne_of_lt hj)]
      congr 2
      refine G.simKey_causal x m s _ _ j fun j' hj' => ?_
      rcases hj' with hj' | hj'
      · exact ih j' hj' (Or.inl (lt_trans hj' hj))
      · exact hprog j' hj'
    · exact hprog j hj

/-- Changing the sampled value of an evaluated entry `i` changes neither the simulator
point of an entry `j ≤ i` nor the evaluated entries before `i`. -/
theorem simKey_update {i : Fin G.μ} (hi : G.ev i = true) (e : Fin G.μ → G.Ch) (c : G.Ch)
    (j : Fin G.μ) (hj : j ≤ i) :
    G.simKey x m s (G.simVals look x m s (Function.update e i c)) j =
      G.simKey x m s (G.simVals look x m s e) j :=
  G.simKey_causal x m s _ _ j fun j' hj' =>
    simVals_update_apply hi e c j' (hj'.imp_left fun h => lt_of_lt_of_le h hj)

end Protocol

/-! ## Uniform functions on `Fin 1` -/

/-- A uniform function on `Fin 1` read at `0` is uniform. -/
theorem map_uniformFintype_fin_one {C : Type} [Fintype C] [Nonempty C] :
    (PMF.uniformFintype (Fin 1 → C)).map (fun e => e 0) = PMF.uniformFintype C := by
  classical
  ext z
  rw [PMF.map_apply, tsum_eq_single (fun _ => z)]
  · simp [PMF.uniformFintype_apply]
  · intro e he
    rw [ite_eq_right]
    intro h
    exact he (funext fun i => by rw [Subsingleton.elim i 0, h])

/-- Sampling a uniform function on `Fin 1` is sampling its value at `0`. -/
theorem bind_uniformFintype_fin_one {C β : Type} [Fintype C] [Nonempty C]
    (f : (Fin 1 → C) → PMF β) :
    (PMF.uniformFintype (Fin 1 → C)).bind f =
      (PMF.uniformFintype C).bind fun c => f fun _ => c := by
  conv_rhs => rw [← map_uniformFintype_fin_one]
  rw [PMF.bind_map]
  refine congrArg _ (funext fun e => congrArg f (funext fun i => ?_))
  simp only [Subsingleton.elim i 0]

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

/-- A value found by `lookupIn l k` is an entry `(k, c)` of `l`. -/
theorem mem_of_lookupIn_eq_some {l : List (K × C)} {k : K} {c : C}
    (h : lookupIn l k = some c) : (k, c) ∈ l := by
  unfold lookupIn findKey at h
  cases hf : l.findIdx? (fun p => decide (p.1 = k)) with
  | none => simp [hf] at h
  | some i =>
    obtain ⟨hi, hp, _⟩ := List.findIdx?_eq_some_iff_getElem.mp hf
    simp only [hf, Option.bind_some, List.getElem?_eq_getElem hi, Option.map_some,
      Option.some.injEq] at h
    simp only [decide_eq_true_eq] at hp
    rw [← hp, ← h]
    exact List.getElem_mem hi

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

theorem lookupIn_append_of_notMem_right (l l' : List (K × C)) {k : K}
    (hk : k ∉ l'.map Prod.fst) : lookupIn (l ++ l') k = lookupIn l k := by
  induction l' generalizing l with
  | nil => rw [List.append_nil]
  | cons p l' ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at hk
    rw [show l ++ p :: l' = (l ++ [p]) ++ l' by simp, ih _ hk.2,
      lookupIn_append_singleton_of_ne _ _ hk.1]

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

theorem lookupAll_of_rej_nil {t : G.Tables} (ht : t.rej = []) (k : G.Key) :
    t.lookupAll k = t.lookup k := by
  unfold Tables.lookupAll
  rw [ht, lookupIn_nil]
  cases t.lookup k <;> rfl

theorem lookupAll_eq_lookup {t : G.Tables} {k : G.Key}
    (h : (t.lookup k).isNone → lookupIn t.rej k = none) : t.lookupAll k = t.lookup k := by
  unfold Tables.lookupAll
  cases hl : t.lookup k with
  | some _ => rfl
  | none => rw [h (by rw [hl]; rfl)]; rfl

theorem lookup_isSome_mem_keys {t : G.Tables} {k : G.Key} (h : (t.lookup k).isSome) :
    k ∈ t.keys := by
  have := lookup_isSome_mem h
  simp only [Tables.keys, List.map_append, List.mem_append] at this ⊢
  exact Or.inl this

theorem lookup_hashAll_of_notMem (t : G.Tables) (l : List (G.Key × G.Ch)) {k : G.Key}
    (hk : k ∉ l.map Prod.fst) : (hashAll t l).lookup k = t.lookup k := by
  have hk' : k ∉ (l.filter fun p => (t.lookup p.1).isNone).map Prod.fst := fun h => hk <| by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp h
    exact List.mem_map.mpr ⟨p, (List.mem_filter.mp hp).1, rfl⟩
  change (lookupIn t.prog k).or
      (lookupIn (t.hash ++ l.filter fun p => (t.lookup p.1).isNone) k) =
    (lookupIn t.prog k).or (lookupIn t.hash k)
  rw [lookupIn_append_of_notMem_right _ _ hk']

theorem mem_entries {x : G.Stmt} {w : G.Wit} {m : G.Msg} {r : G.Rand} {v : Fin G.μ → G.Ch}
    {p : Fin G.μ → Bool} {q : G.Key × G.Ch} (hq : q ∈ G.entries x w m r v p) :
    ∃ i, p i = true ∧ q = (G.key x w m r v i, v i) := by
  simp only [Protocol.entries, List.mem_map, List.mem_filter, List.mem_finRange, true_and] at hq
  obtain ⟨i, hi, rfl⟩ := hq
  exact ⟨i, hi, rfl⟩

theorem mem_entries_of {x : G.Stmt} {w : G.Wit} {m : G.Msg} {r : G.Rand} {v : Fin G.μ → G.Ch}
    {p : Fin G.μ → Bool} {i : Fin G.μ} (hi : p i = true) :
    (G.key x w m r v i, v i) ∈ G.entries x w m r v p :=
  List.mem_map.mpr ⟨i, List.mem_filter.mpr ⟨List.mem_finRange i, hi⟩, rfl⟩

/-- The evaluated public, programmed public and hidden entries of an attempt are
`μ` entries in all. -/
theorem length_entries (x : G.Stmt) (w : G.Wit) (m : G.Msg) (r : G.Rand)
    (v : Fin G.μ → G.Ch) :
    (G.evEntries x w m r v).length + (G.pubEntries x w m r v).length +
      (G.hidEntries x w m r v).length = G.μ := by
  simp only [Protocol.evEntries, Protocol.pubEntries, Protocol.hidEntries, Protocol.entries,
    List.length_map]
  have h1 := List.length_eq_length_filter_add (G.pub x w m r v) (l := List.finRange G.μ)
  have h2 := List.length_eq_length_filter_add G.ev
    (l := (List.finRange G.μ).filter (G.pub x w m r v))
  simp only [List.filter_filter, List.length_finRange] at h1 h2
  omega

/-- The point of a programmed entry is not the point of an evaluated public entry. -/
theorem key_notMem_evEntries {x : G.Stmt} {w : G.Wit} {m : G.Msg} {r : G.Rand}
    {v : Fin G.μ → G.Ch} {i : Fin G.μ} (hi : G.ev i = false) :
    G.key x w m r v i ∉ (G.evEntries x w m r v).map Prod.fst := by
  intro h
  obtain ⟨p, hp, hpk⟩ := List.mem_map.mp h
  obtain ⟨j, hj, rfl⟩ := mem_entries hp
  obtain rfl := G.key_inj x w m r v j i hpk
  simp [hi] at hj

end Protocol

theorem le_traceTables (t : G.Tables) (m : G.Msg) (tr : G.Trace) : t.Le (traceTables t m tr) :=
  ⟨List.prefix_append _ _, List.prefix_append _ _, List.prefix_refl _⟩

theorem size_traceTables_le (t : G.Tables) (m : G.Msg) (tr : G.Trace) :
    (traceTables t m tr).hash.length + (traceTables t m tr).prog.length ≤
      t.hash.length + t.prog.length + tr.1.length + tr.2.1.length := by
  simp only [traceTables, hashAll, List.length_append]
  have := List.length_filter_le (fun p : G.Key × G.Ch => (t.lookup p.1).isNone) tr.1
  omega

theorem rej_traceTables (t : G.Tables) (m : G.Msg) (tr : G.Trace) :
    (traceTables t m tr).rej = t.rej := rfl

theorem sampleVec_bind {β γ δ : Type} [Fintype β] [Nonempty β]
    (F : (Fin G.μ → G.Ch) → β → γ) (g : γ → PMF δ) :
    (sampleVec G F).bind g = (PMF.uniformFintype (Fin G.μ → G.Ch)).bind fun e =>
      (PMF.uniformFintype β).bind fun y => g (F e y) := by
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
    exact programAll_flag _ _

theorem hashAll_nil (t : G.Tables) : hashAll t [] = t := by
  simp [hashAll]

/-- When the simulator queries no point, a simulated signing attempt programs the
output of `simulate` on the sampled values. -/
theorem simSignOut_of_simKey_none {x₀ : G.Stmt} {m : G.Msg} {s : G.SimRand}
    (h : ∀ v i, G.simKey x₀ m s v i = none) (t : G.Tables) (b : Bool) (e : Fin G.μ → G.Ch) :
    simSignOut x₀ t b m e s = programOut t b m (G.simulate x₀ m e s) := by
  simp only [simSignOut, traceOut, Protocol.simTrace_of_simKey_none h, hashAll_nil]

end Transitions

/-! ## The real signing oracle -/

section RealSign

variable {G : Protocol} (x : G.Stmt) (w : G.Wit) (t : G.Tables) (b : Bool) (m : G.Msg)
  (e : Fin G.μ → G.Ch) (r : G.Rand)

/-- An attempt whose programmed and hidden entries are at undefined points and whose
evaluated public entries are not at the points of hidden entries only takes the
values against the visible oracle, records its entries and keeps the flag. -/
theorem realSignOut_of_fresh
    (h1 : ∀ i, G.flagging x w m r (G.vals t.lookup x w m r e) i = true →
      t.lookupAll (G.key x w m r (G.vals t.lookup x w m r e) i) = none)
    (h2 : ∀ i, G.flagging x w m r (G.vals t.lookup x w m r e) i = false →
      (t.lookup (G.key x w m r (G.vals t.lookup x w m r e) i)).isNone →
        lookupIn t.rej (G.key x w m r (G.vals t.lookup x w m r e) i) = none) :
    realSignOut x w t b m e r = (.inr (G.sign x w m r (G.vals t.lookup x w m r e)),
      ({ traceTables t m (G.trace x w m r (G.vals t.lookup x w m r e)) with
          rej := t.rej ++ G.hidEntries x w m r (G.vals t.lookup x w m r e) }, b)) := by
  have hr : G.honestVals t.lookupAll x w m r e = G.vals t.lookup x w m r e := by
    refine effVec_congr _ _ (G.key_causal x w m r) e _ fun i => ?_
    change t.lookupAll (G.key x w m r (G.vals t.lookup x w m r e) i) =
      (if G.ev i then t.lookup else fun _ => none) (G.key x w m r (G.vals t.lookup x w m r e) i)
    cases hev : G.ev i
    · exact h1 i (by simp [Protocol.flagging, hev])
    · simp only [ite_true]
      cases hf : G.flagging x w m r (G.vals t.lookup x w m r e) i
      · exact Protocol.lookupAll_eq_lookup (h2 i hf)
      · rw [h1 i hf, Protocol.lookup_eq_none_of_lookupAll (h1 i hf)]
  set v := G.vals t.lookup x w m r e
  have hp : (G.pubEntries x w m r v).filter (fun p => (t.lookupAll p.1).isNone) =
      G.pubEntries x w m r v := List.filter_eq_self.mpr fun p hp => by
    obtain ⟨i, hi, rfl⟩ := Protocol.mem_entries hp
    have hf : G.flagging x w m r v i = true := by
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hi
      simp [Protocol.flagging, hi.1]
    simp [h1 i hf]
  have hh : (G.hidEntries x w m r v).filter (fun p => (t.lookupAll p.1).isNone) =
      G.hidEntries x w m r v := List.filter_eq_self.mpr fun p hp => by
    obtain ⟨i, hi, rfl⟩ := Protocol.mem_entries hp
    have hf : G.flagging x w m r v i = true := by simp [Protocol.flagging, hi]
    simp [h1 i hf]
  have hany : ((List.finRange G.μ).any fun i =>
      if G.flagging x w m r v i then (t.lookupAll (G.key x w m r v i)).isSome
      else (t.lookup (G.key x w m r v i)).isNone &&
        (lookupIn t.rej (G.key x w m r v i)).isSome) = false := by
    refine List.any_eq_false.mpr fun i _ => ?_
    cases hf : G.flagging x w m r v i
    · simp only [Bool.false_eq_true, ite_false, Bool.and_eq_true, not_and]
      intro hn
      simp [h2 i hf hn]
    · simp [h1 i hf]
  simp only [realSignOut, hr]
  rw [hp, hh, hany, Bool.or_false]
  rfl

/-- A real signing attempt that leaves the flag cleared starts with the flag cleared
and satisfies the hypotheses of `realSignOut_of_fresh`. -/
theorem fresh_of_realSignOut (h : (realSignOut x w t b m e r).2.2 = false) :
    b = false ∧
      (∀ i, G.flagging x w m r (G.vals t.lookup x w m r e) i = true →
        t.lookupAll (G.key x w m r (G.vals t.lookup x w m r e) i) = none) ∧
      (∀ i, G.flagging x w m r (G.vals t.lookup x w m r e) i = false →
        (t.lookup (G.key x w m r (G.vals t.lookup x w m r e) i)).isNone →
          lookupIn t.rej (G.key x w m r (G.vals t.lookup x w m r e) i) = none) := by
  simp only [realSignOut, Bool.or_eq_false_iff, List.any_eq_false, List.mem_finRange,
    true_implies] at h
  obtain ⟨hb, h⟩ := h
  set v := G.honestVals t.lookupAll x w m r e with hv
  have c1 : ∀ i, G.flagging x w m r v i = true → t.lookupAll (G.key x w m r v i) = none :=
    fun i hf => by
      have := h i
      rw [ite_eq_left hf] at this
      simpa using this
  have c2 : ∀ i, G.flagging x w m r v i = false → (t.lookup (G.key x w m r v i)).isNone →
      lookupIn t.rej (G.key x w m r v i) = none := fun i hf hn => by
    have := h i
    rw [ite_eq_right (by simp [hf])] at this
    simpa [hn] using this
  have hr : G.vals t.lookup x w m r e = v := by
    refine effVec_congr _ _ (G.key_causal x w m r) e _ fun i => ?_
    change (if G.ev i then t.lookup else fun _ => none) (G.key x w m r v i) =
      t.lookupAll (G.key x w m r v i)
    cases hev : G.ev i
    · exact (c1 i (by simp [Protocol.flagging, hev])).symm
    · simp only [ite_true]
      cases hf : G.flagging x w m r v i
      · exact (Protocol.lookupAll_eq_lookup (c2 i hf)).symm
      · rw [c1 i hf, Protocol.lookup_eq_none_of_lookupAll (c1 i hf)]
  rw [hr]
  exact ⟨hb, c1, c2⟩

/-- A real signing attempt extends the tables by at most `μ` entries. -/
theorem realSignOut_support :
    t.Le (realSignOut x w t b m e r).2.1 ∧
      (realSignOut x w t b m e r).2.1.size ≤ t.size + G.μ := by
  refine ⟨⟨List.prefix_append _ _, List.prefix_append _ _, List.prefix_append _ _⟩, ?_⟩
  simp only [realSignOut, hashAll, Protocol.Tables.size, List.length_append]
  set v := G.honestVals t.lookupAll x w m r e
  have h0 := Protocol.length_entries x w m r v
  have h1 := List.length_filter_le (fun p : G.Key × G.Ch => (t.lookup p.1).isNone)
    (G.evEntries x w m r v)
  have h2 := List.length_filter_le (fun p : G.Key × G.Ch => (t.lookupAll p.1).isNone)
    (G.pubEntries x w m r v)
  have h3 := List.length_filter_le (fun p : G.Key × G.Ch => (t.lookupAll p.1).isNone)
    (G.hidEntries x w m r v)
  omega

/-- Every point of a real signing attempt is defined after it. -/
theorem realSignOut_key (i : Fin G.μ) :
    G.key x w m r (G.honestVals t.lookupAll x w m r e) i ∈
      (realSignOut x w t b m e r).2.1.keys := by
  set v := G.honestVals t.lookupAll x w m r e
  cases hl : t.lookupAll (G.key x w m r v i) with
  | some _ =>
    exact (realSignOut_support x w t b m e r).1.keys_subset
      (Protocol.lookupAll_isSome_mem (by rw [hl]; rfl))
  | none =>
    refine Protocol.Tables.mem_keys.mpr ⟨(G.key x w m r v i, v i), ?_, rfl⟩
    cases hp : G.pub x w m r v i
    · refine Or.inr (Or.inr (List.mem_append_right _ (List.mem_filter.mpr
        ⟨Protocol.mem_entries_of (by rw [Bool.not_eq_true']; exact hp), by simp [hl]⟩)))
    · cases hev : G.ev i
      · refine Or.inl (List.mem_append_right _ (List.mem_filter.mpr
          ⟨Protocol.mem_entries_of (by simp only [hev, Bool.not_false, Bool.true_and]; exact hp),
            by simp [hl]⟩))
      · refine Or.inr (Or.inl (List.mem_append_right _ (List.mem_filter.mpr
          ⟨Protocol.mem_entries_of (by simp only [hev, Bool.true_and]; exact hp), ?_⟩)))
        simp [Protocol.lookup_eq_none_of_lookupAll hl]

/-- A signing attempt none of whose points is among the entries `l` commutes with
adding `l` to the hidden entries. -/
theorem realSignOut_addRejs (l : List (G.Key × G.Ch))
    (hk : ∀ i, G.key x w m r (G.honestVals t.lookupAll x w m r e) i ∉ l.map Prod.fst) :
    realSignOut x w (t.addRejs l) b m e r =
      Prod.map id (Prod.map (Protocol.Tables.addRejs l) id) (realSignOut x w t b m e r) := by
  have hv : G.honestVals (t.addRejs l).lookupAll x w m r e =
      G.honestVals t.lookupAll x w m r e :=
    effVec_congr _ _ (G.key_causal x w m r) e _ fun i =>
      Protocol.lookupAll_addRejs_of_notMem l t (hk i)
  set v := G.honestVals t.lookupAll x w m r e
  have hl : ∀ i, (t.addRejs l).lookupAll (G.key x w m r v i) = t.lookupAll (G.key x w m r v i) :=
    fun i => Protocol.lookupAll_addRejs_of_notMem l t (hk i)
  have hr : ∀ i, lookupIn (t.addRejs l).rej (G.key x w m r v i) =
      lookupIn t.rej (G.key x w m r v i) :=
    fun i => lookupIn_append_of_notMem _ _ (hk i)
  have hf : ∀ p : Fin G.μ → Bool,
      (G.entries x w m r v p).filter (fun q => ((t.addRejs l).lookupAll q.1).isNone) =
        (G.entries x w m r v p).filter (fun q => (t.lookupAll q.1).isNone) := fun p =>
    List.filter_congr fun q hq => by
      obtain ⟨i, _, rfl⟩ := Protocol.mem_entries hq
      rw [hl i]
  simp only [realSignOut, hv, hl, hr, Protocol.pubEntries, Protocol.hidEntries, hf]
  simp only [Protocol.Tables.addRejs, hashAll, Prod.map, id, List.append_assoc]
  rfl

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

/-- A hash entry at `key` adds `hashCost c (inl key)` points of class `c`. -/
theorem count_hash_append (κ : G.Classes) (t : G.Tables) (key : G.Key) (e : G.Ch) (c : κ.ι) :
    κ.count ({ t with hash := t.hash ++ [(key, e)] } : G.Tables).keys c =
      κ.count t.keys c + κ.hashCost c (.inl key) := by
  simp only [Protocol.Tables.keys, List.map_append, List.map_cons, List.map_nil, κ.count_append]
  by_cases hc : κ.cls key = c
  · simp [Protocol.Classes.count, Protocol.Classes.hashCost, hc]
    omega
  · simp [Protocol.Classes.count, Protocol.Classes.hashCost, hc]

/-- A real signing attempt adds at most `μc c` points of class `c`. -/
theorem realSignOut_count_le (κ : G.Classes) (x : G.Stmt) (w : G.Wit) (t : G.Tables)
    (b : Bool) (m : G.Msg) (e : Fin G.μ → G.Ch) (r : G.Rand) (c : κ.ι) :
    κ.count (realSignOut x w t b m e r).2.1.keys c ≤ κ.count t.keys c + κ.μc c := by
  have h0 := κ.count_trace_entries x w m r (G.honestVals t.lookupAll x w m r e) c
  have h1 := κ.count_le_of_sublist ((List.filter_sublist (p := fun p : G.Key × G.Ch =>
    (t.lookup p.1).isNone) (l := G.evEntries x w m r (G.honestVals t.lookupAll x w m r e))).map
    Prod.fst) c
  have h2 := κ.count_le_of_sublist ((List.filter_sublist (p := fun p : G.Key × G.Ch =>
    (t.lookupAll p.1).isNone) (l := G.pubEntries x w m r (G.honestVals t.lookupAll x w m r e))).map
    Prod.fst) c
  have h3 := κ.count_le_of_sublist ((List.filter_sublist (p := fun p : G.Key × G.Ch =>
    (t.lookupAll p.1).isNone) (l := G.hidEntries x w m r (G.honestVals t.lookupAll x w m r e))).map
    Prod.fst) c
  simp only [realSignOut, hashAll, Protocol.Tables.keys, List.map_append, κ.count_append]
  omega

/-- Every real transition adds at most `hashCost c d` points of class `c` for a hash
query and at most `μc c` for a signing query. -/
theorem realStep_count_le (κ : G.Classes) (xw : G.Stmt × G.Wit) (s : G.Tables × Bool)
    (d : G.Query) (o : G.Answer × (G.Tables × Bool))
    (ho : o ∈ (toOracle (realStep xw) s d).support) (c : κ.ι) :
    κ.count o.2.1.keys c ≤ κ.count s.1.keys c + κ.hashCost c d +
      Sum.elim (fun _ => 0) (fun _ => κ.μc c) d := by
  obtain ⟨t, b⟩ := s
  cases d with
  | inl k =>
    simp only [toOracle, realStep, realHashStep] at ho
    cases hl : t.lookup k with
    | some e =>
      simp only [hl, Step.toPMF, PMF.support_pure, Set.mem_singleton_iff] at ho
      subst ho
      exact Nat.le_add_right_of_le (Nat.le_add_right _ _)
    | none =>
      cases hr : lookupIn t.rej k with
      | some e =>
        simp only [hl, hr, Step.toPMF, PMF.support_pure, Set.mem_singleton_iff] at ho
        subst ho
        exact (count_hash_append κ t k e c).le
      | none =>
        simp only [hl, hr, Step.toPMF, PMF.support_map, Set.mem_image] at ho
        obtain ⟨e, _, rfl⟩ := ho
        exact (count_hash_append κ t k e c).le
  | inr m =>
    simp only [toOracle, realStep, Step.toPMF] at ho
    obtain ⟨e, r, rfl⟩ := mem_support_sampleVec ho
    simpa [Protocol.Classes.hashCost] using realSignOut_count_le κ _ _ _ _ _ _ _ c

/-- Along a real run with at most `q` signing queries and hash queries of total
cost at most `n` for the class `c`, the tables gain at most `n + μc c·q` points of
class `c`. -/
theorem run_real_support_size_cls (κ : G.Classes) (xw : G.Stmt × G.Wit)
    (A : OracleAdv G.Query G.Answer α) (c : κ.ι) (h q n : ℕ) (hA : IsQueryBound₂ A h q)
    (hn : A.IsQueryBoundBy (κ.hashCost c) n) (s : G.Tables × Bool) (y : α × (G.Tables × Bool))
    (hy : y ∈ (OracleAdv.run (toOracle (realStep xw)) A s).support) :
    κ.count y.2.1.keys c ≤ κ.count s.1.keys c + n + κ.μc c * q := by
  induction A generalizing h q n s with
  | ret a =>
    rw [OracleAdv.run_ret, PMF.support_pure, Set.mem_singleton_iff] at hy
    subst hy
    show κ.count s.1.keys c ≤ _
    omega
  | rand p k ih =>
    rw [OracleAdv.run_rand, PMF.mem_support_bind_iff] at hy
    obtain ⟨b, _, hb⟩ := hy
    exact ih b h q n (hA b) (hn b) s hb
  | query d k ih =>
    rw [OracleAdv.run_query, PMF.mem_support_bind_iff] at hy
    obtain ⟨o, ho, hy⟩ := hy
    have hs := realStep_count_le κ xw s d o ho c
    obtain ⟨hn1, hn2⟩ := hn
    cases d with
    | inl key =>
      cases h with
      | zero => exact hA.elim
      | succ h =>
        have := ih o.1 h q _ (hA o.1) (hn2 o.1) o.2 hy
        simp only [Sum.elim_inl] at hs
        omega
    | inr m =>
      cases q with
      | zero => exact hA.elim
      | succ q =>
        have := ih o.1 h q _ (hA o.1) (hn2 o.1) o.2 hy
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
  by_cases hc : ∃ i, G.key xw.1 xw.2 m r (G.honestVals t.lookupAll xw.1 xw.2 m r e) i ∈
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

/-- A finite sum inside two weighted sums is the finite sum of the weighted sums. -/
theorem tsum_mul_tsum_mul_finsetSum {β γ ι : Type} (p : β → ℝ≥0∞) (p' : γ → ℝ≥0∞)
    (s : Finset ι) (F : ι → β → γ → ℝ≥0∞) :
    ∑' b, p b * ∑' c, p' c * ∑ j ∈ s, F j b c = ∑ j ∈ s, ∑' b, p b * ∑' c, p' c * F j b c := by
  have h1 : ∀ b, ∑' c, p' c * ∑ j ∈ s, F j b c = ∑ j ∈ s, ∑' c, p' c * F j b c := fun b => by
    simp only [Finset.mul_sum]
    exact Summable.tsum_finsetSum fun _ _ => ENNReal.summable
  calc _ = ∑' b, ∑ j ∈ s, p b * ∑' c, p' c * F j b c :=
        tsum_congr fun b => by rw [h1 b, Finset.mul_sum]
    _ = _ := Summable.tsum_finsetSum fun _ _ => ENNReal.summable

/-- **Guessing the points of an attempt.** For a pair with key bound `Γ` and runs
`R tr` indexed by traces whose final tables have at most `N` points on the traces
`guessView`, the expectation over the values and the randomness of the number of
programmed or hidden entries whose point is defined at the end of
`R (guessView …)` is at most `N·Γ`. -/
theorem tsum_guess_le {Γ : ℝ≥0∞} (x : G.Stmt) (w : G.Wit) (hΓ : G.KeyBoundAt x w Γ)
    (m : G.Msg) (look : G.Key → Option G.Ch) (R : G.Trace → PMF (α × (G.Tables × Bool)))
    (N : ℕ) (hN : ∀ e r i, ∀ y ∈ (R (G.guessView look x w m r e i)).support,
      y.2.1.keys.length ≤ N) :
    ∑' e, PMF.uniformFintype (Fin G.μ → G.Ch) e * ∑' r, PMF.uniformFintype G.Rand r *
      ∑ i, (if G.flagging x w m r (G.vals look x w m r e) i then
        (R (G.guessView look x w m r e i)).toOuterMeasure
          {y | G.key x w m r (G.vals look x w m r e) i ∈ y.2.1.keys} else 0) ≤ N * Γ := by
  rcases isEmpty_or_nonempty G.Key with hK | ⟨⟨k₀⟩⟩
  · have : IsEmpty (Fin G.μ) := ⟨fun i => hK.false (G.key x w m (Classical.arbitrary _)
      (Classical.arbitrary _) i)⟩
    simp
  -- the guess of the `j`-th point of the final tables
  let Q : ℕ → G.Trace → PMF G.Key := fun j tr => (R tr).map fun y => y.2.1.keys.getD j k₀
  have h1 : ∀ e r i, (if G.flagging x w m r (G.vals look x w m r e) i then
      (R (G.guessView look x w m r e i)).toOuterMeasure
        {y | G.key x w m r (G.vals look x w m r e) i ∈ y.2.1.keys} else 0) ≤
      ∑ j ∈ Finset.range N, (if G.flagging x w m r (G.vals look x w m r e) i then
        Q j (G.guessView look x w m r e i) (G.key x w m r (G.vals look x w m r e) i)
        else 0) := fun e r i => by
    split_ifs
    · exact toOuterMeasure_mem_le_sum (R (G.guessView look x w m r e i)) (fun y => y.2.1.keys)
        N k₀ (G.key x w m r (G.vals look x w m r e) i) (hN e r i)
    · exact zero_le
  calc _ ≤ ∑' e, PMF.uniformFintype (Fin G.μ → G.Ch) e * ∑' r, PMF.uniformFintype G.Rand r *
        ∑ j ∈ Finset.range N, ∑ i, (if G.flagging x w m r (G.vals look x w m r e) i then
          Q j (G.guessView look x w m r e i) (G.key x w m r (G.vals look x w m r e) i)
          else 0) := by
        refine ENNReal.tsum_le_tsum fun e => mul_le_mul_right
          (ENNReal.tsum_le_tsum fun r => mul_le_mul_right ?_ _) _
        rw [Finset.sum_comm]
        exact Finset.sum_le_sum fun i _ => h1 e r i
    _ = ∑ j ∈ Finset.range N, ∑' e, PMF.uniformFintype (Fin G.μ → G.Ch) e *
          ∑' r, PMF.uniformFintype G.Rand r * ∑ i,
            (if G.flagging x w m r (G.vals look x w m r e) i then
              Q j (G.guessView look x w m r e i) (G.key x w m r (G.vals look x w m r e) i)
              else 0) := tsum_mul_tsum_mul_finsetSum _ _ _ _
    _ ≤ ∑ _j ∈ Finset.range N, Γ := Finset.sum_le_sum fun j _ => hΓ m look (Q j)
    _ = N * Γ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The rest of a real run after a signing attempt on `m` from `t` with the trace
`tr`, the flag cleared and the hidden entries left out. -/
noncomputable def contRun (xw : G.Stmt × G.Wit) (k : G.Answer → OracleAdv G.Query G.Answer α)
    (t : G.Tables) (m : G.Msg) (tr : G.Trace) : PMF (α × (G.Tables × Bool)) :=
  OracleAdv.run (toOracle (realStep xw)) (k (.inr tr.2.2)) (traceTables t m tr, false)

theorem length_guessView_le (look : G.Key → Option G.Ch) (x : G.Stmt) (w : G.Wit) (m : G.Msg)
    (r : G.Rand) (e : Fin G.μ → G.Ch) (i : Fin G.μ) :
    (G.guessView look x w m r e i).1.length + (G.guessView look x w m r e i).2.1.length ≤ G.μ := by
  unfold Protocol.guessView
  split
  · exact Nat.zero_le _
  · have := Protocol.length_entries x w m r (G.vals look x w m r e)
    simp only [Protocol.trace, Protocol.view]
    omega

/-- One signing attempt in the induction of `run_real_flag_le`: the probability
that the rest of the run sets the flag is at most the bound for the tables after the
attempt plus, for each programmed or hidden entry, the probability that its point is
defined at the end of the rest of the run from the trace `guessView`. -/
theorem flag_sign_term_le (xw : G.Stmt × G.Wit) {Γ : ℝ≥0∞}
    (k : G.Answer → OracleAdv G.Query G.Answer α) (h q : ℕ) (t : G.Tables)
    (ht : t.rej = []) (m : G.Msg) (e : Fin G.μ → G.Ch) (r : G.Rand)
    (ih : ∀ c (t' : G.Tables), t'.rej = [] →
      (OracleAdv.run (toOracle (realStep xw)) (k c) (t', false)).toOuterMeasure
        {y | y.2.2 = true} ≤
        ((q * (t'.hash.length + t'.prog.length + h + G.μ * q) : ℕ) : ℝ≥0∞) * Γ) :
    (OracleAdv.run (toOracle (realStep xw)) (k (realSignOut xw.1 xw.2 t false m e r).1)
        (realSignOut xw.1 xw.2 t false m e r).2).toOuterMeasure {y | y.2.2 = true} ≤
      ((q * (t.hash.length + t.prog.length + G.μ + h + G.μ * q) : ℕ) : ℝ≥0∞) * Γ +
        ∑ i, (if G.flagging xw.1 xw.2 m r (G.vals t.lookup xw.1 xw.2 m r e) i then
          (contRun xw k t m (G.guessView t.lookup xw.1 xw.2 m r e i)).toOuterMeasure
            {y | G.key xw.1 xw.2 m r (G.vals t.lookup xw.1 xw.2 m r e) i ∈ y.2.1.keys}
          else 0) := by
  set v := G.vals t.lookup xw.1 xw.2 m r e with hv
  by_cases hc : ∃ i, G.flagging xw.1 xw.2 m r v i = true ∧
      (t.lookup (G.key xw.1 xw.2 m r v i)).isSome
  · obtain ⟨i, hf, hi⟩ := hc
    refine (toOuterMeasure_le_one _ _).trans (le_trans ?_ le_add_self)
    refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun i =>
      if G.flagging xw.1 xw.2 m r v i then
        (contRun xw k t m (G.guessView t.lookup xw.1 xw.2 m r e i)).toOuterMeasure
          {y | G.key xw.1 xw.2 m r v i ∈ y.2.1.keys} else 0) (fun _ _ => zero_le)
      (Finset.mem_univ i))
    have hg : G.guessView t.lookup xw.1 xw.2 m r e i = ([], [], none) := by
      simp only [Protocol.guessView, ← hv, hi, Bool.or_true, ite_true]
    simp only [hf, ite_true, hg]
    refine (run_real_keys_eq_one xw _ _ _ ?_ _ fun y hy => hy).symm
    exact (le_traceTables t m _).keys_subset (Protocol.lookup_isSome_mem_keys hi)
  simp only [not_exists, not_and, Bool.not_eq_true, Option.isSome_eq_false_iff,
    Option.isNone_iff_eq_none] at hc
  rw [realSignOut_of_fresh _ _ _ _ _ _ _
    (fun i hf => (Protocol.lookupAll_of_rej_nil ht _).trans (hc i hf))
    (fun i _ _ => by rw [ht]; exact lookupIn_nil _)]
  set T₀ : G.Tables := traceTables t m (G.trace xw.1 xw.2 m r v)
  have hT : ({ T₀ with rej := t.rej ++ G.hidEntries xw.1 xw.2 m r v } : G.Tables) =
      T₀.addRejs (G.hidEntries xw.1 xw.2 m r v) := by
    simp only [Protocol.Tables.addRejs, T₀, rej_traceTables, ht, List.nil_append,
      List.append_nil]
  rw [hT]
  refine (run_real_addRejs_flag_le xw _ _ T₀ false).trans ?_
  refine (MeasureTheory.measure_mono (fun y hy => hy)).trans
    ((MeasureTheory.measure_union_le _ _).trans (add_le_add ?_ ?_))
  · refine (ih _ T₀ ht).trans (mul_le_mul_of_nonneg_right ?_ zero_le)
    have h1 : T₀.hash.length + T₀.prog.length ≤ t.hash.length + t.prog.length +
        (G.trace xw.1 xw.2 m r v).1.length + (G.trace xw.1 xw.2 m r v).2.1.length :=
      size_traceTables_le t m (G.trace xw.1 xw.2 m r v)
    have h2 := Protocol.length_entries xw.1 xw.2 m r v
    simp only [Protocol.trace, Protocol.view] at h1
    exact_mod_cast Nat.mul_le_mul_left _ (by omega)
  · calc _ ≤ (contRun xw k t m (G.trace xw.1 xw.2 m r v)).toOuterMeasure
            (⋃ i ∈ Finset.univ.filter (fun i => G.pub xw.1 xw.2 m r v i = false),
              {y | G.key xw.1 xw.2 m r v i ∈ y.2.1.keys}) := by
          refine MeasureTheory.measure_mono fun y hy => ?_
          obtain ⟨p, hp, hk⟩ := hy
          obtain ⟨i, hi, rfl⟩ := Protocol.mem_entries hp
          simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨i, by simpa using hi, hk⟩
      _ ≤ ∑ i ∈ Finset.univ.filter (fun i => G.pub xw.1 xw.2 m r v i = false),
            (contRun xw k t m (G.trace xw.1 xw.2 m r v)).toOuterMeasure
              {y | G.key xw.1 xw.2 m r v i ∈ y.2.1.keys} :=
          MeasureTheory.measure_biUnion_finset_le _ _
      _ = ∑ i ∈ Finset.univ.filter (fun i => G.pub xw.1 xw.2 m r v i = false),
            (if G.flagging xw.1 xw.2 m r v i then
              (contRun xw k t m (G.guessView t.lookup xw.1 xw.2 m r e i)).toOuterMeasure
                {y | G.key xw.1 xw.2 m r v i ∈ y.2.1.keys} else 0) := by
          refine Finset.sum_congr rfl fun i hi => ?_
          have hi' : G.pub xw.1 xw.2 m r v i = false := (Finset.mem_filter.mp hi).2
          have hf : G.flagging xw.1 xw.2 m r v i = true := by simp [Protocol.flagging, hi']
          have hg : G.guessView t.lookup xw.1 xw.2 m r e i = G.trace xw.1 xw.2 m r v := by
            simp only [Protocol.guessView, ← hv, hi', hc i hf, Option.isSome_none,
              Bool.or_false, Bool.false_eq_true, ite_false]
          rw [ite_eq_left hf, hg]
      _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- A hash query in the induction of `run_real_flag_le`. -/
theorem flag_hash_step_le (xw : G.Stmt × G.Wit) {Γ : ℝ≥0∞}
    (k : G.Answer → OracleAdv G.Query G.Answer α) (h q : ℕ) (t : G.Tables)
    (ht : t.rej = []) (key : G.Key)
    (ih : ∀ c (t' : G.Tables), t'.rej = [] →
      (OracleAdv.run (toOracle (realStep xw)) (k c) (t', false)).toOuterMeasure
        {y | y.2.2 = true} ≤
        ((q * (t'.hash.length + t'.prog.length + h + G.μ * q) : ℕ) : ℝ≥0∞) * Γ) :
    (OracleAdv.run (toOracle (realStep xw)) (.query (.inl key) k) (t, false)).toOuterMeasure
        {y | y.2.2 = true} ≤
      ((q * (t.hash.length + t.prog.length + (h + 1) + G.μ * q) : ℕ) : ℝ≥0∞) * Γ := by
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
    calc ∑' e, PMF.uniformFintype G.Ch e * (OracleAdv.run (toOracle (realStep xw))
          (k (.inl e)) ({ t with hash := t.hash ++ [(key, e)] }, false)).toOuterMeasure _
        ≤ ∑' e, PMF.uniformFintype G.Ch e *
          (((q * (t.hash.length + t.prog.length + (h + 1) + G.μ * q) : ℕ) :
            ℝ≥0∞) * Γ) := by
          refine ENNReal.tsum_le_tsum fun e => mul_le_mul_right ?_ _
          refine (ih _ { t with hash := t.hash ++ [(key, e)] } ht).trans (le_of_eq ?_)
          simp only [List.length_append, List.length_singleton]
          congr 3
          omega
      _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- The guess terms of a signing attempt in the induction of `run_real_flag_le`:
the expectation over the values and the randomness of the number of programmed or
hidden entries whose point is defined at the end of the rest of the run is at most
`(L + μ + h + μ·q)·Γ`. -/
theorem flag_guess_le (xw : G.Stmt × G.Wit) {Γ : ℝ≥0∞} (hΓ : G.KeyBoundAt xw.1 xw.2 Γ)
    (k : G.Answer → OracleAdv G.Query G.Answer α) (h q : ℕ)
    (hk : ∀ r, IsQueryBound₂ (k r) h q) (t : G.Tables) (ht : t.rej = []) (m : G.Msg) :
    ∑' e, PMF.uniformFintype (Fin G.μ → G.Ch) e * ∑' r, PMF.uniformFintype G.Rand r *
      ∑ i, (if G.flagging xw.1 xw.2 m r (G.vals t.lookup xw.1 xw.2 m r e) i then
        (contRun xw k t m (G.guessView t.lookup xw.1 xw.2 m r e i)).toOuterMeasure
          {y | G.key xw.1 xw.2 m r (G.vals t.lookup xw.1 xw.2 m r e) i ∈ y.2.1.keys}
        else 0) ≤
      ((t.hash.length + t.prog.length + G.μ + h + G.μ * q : ℕ) : ℝ≥0∞) * Γ := by
  refine tsum_guess_le xw.1 xw.2 hΓ m t.lookup (contRun xw k t m) _ fun e r i y hy => ?_
  rw [Protocol.Tables.length_keys]
  have h1 := run_real_support_size xw _ h q (hk _) _ y hy
  have h2 := length_guessView_le t.lookup xw.1 xw.2 m r e i
  have h3 := size_traceTables_le t m (G.guessView t.lookup xw.1 xw.2 m r e i)
  simp only [Protocol.Tables.size, rej_traceTables, ht, List.length_nil] at h1 h3 ⊢
  omega

/-- A signing query in the induction of `run_real_flag_le`. -/
theorem flag_sign_step_le (xw : G.Stmt × G.Wit) {Γ : ℝ≥0∞} (hΓ : G.KeyBoundAt xw.1 xw.2 Γ)
    (k : G.Answer → OracleAdv G.Query G.Answer α) (h q : ℕ)
    (hk : ∀ r, IsQueryBound₂ (k r) h q) (t : G.Tables) (ht : t.rej = []) (m : G.Msg)
    (ih : ∀ c (t' : G.Tables), t'.rej = [] →
      (OracleAdv.run (toOracle (realStep xw)) (k c) (t', false)).toOuterMeasure
        {y | y.2.2 = true} ≤
        ((q * (t'.hash.length + t'.prog.length + h + G.μ * q) : ℕ) : ℝ≥0∞) * Γ) :
    (OracleAdv.run (toOracle (realStep xw)) (.query (.inr m) k) (t, false)).toOuterMeasure
        {y | y.2.2 = true} ≤
      (((q + 1) * (t.hash.length + t.prog.length + h + G.μ * (q + 1)) : ℕ) : ℝ≥0∞) * Γ := by
  set L := t.hash.length + t.prog.length with hL
  set N := L + G.μ + h + G.μ * q with hN
  set B : ℝ≥0∞ := ((q * N : ℕ) : ℝ≥0∞) * Γ with hB
  -- the guess terms of the attempt with the values `e` and the randomness `r`
  set S : (Fin G.μ → G.Ch) → G.Rand → ℝ≥0∞ := fun e r =>
    ∑ i, (if G.flagging xw.1 xw.2 m r (G.vals t.lookup xw.1 xw.2 m r e) i then
      (contRun xw k t m (G.guessView t.lookup xw.1 xw.2 m r e i)).toOuterMeasure
        {y | G.key xw.1 xw.2 m r (G.vals t.lookup xw.1 xw.2 m r e) i ∈ y.2.1.keys}
      else 0) with hS
  have hterm := fun e r => flag_sign_term_le xw k h q t ht m e r ih
  have hsum : ∑' e, PMF.uniformFintype (Fin G.μ → G.Ch) e *
      ∑' r, PMF.uniformFintype G.Rand r * S e r ≤ (N : ℝ≥0∞) * Γ := by
    have := flag_guess_le xw hΓ k h q hk t ht m
    rw [hS, hN, hL]
    exact_mod_cast this
  rw [OracleAdv.run_query]
  simp only [toOracle, realStep, Step.toPMF, sampleVec_bind, PMF.toOuterMeasure_bind_apply]
  calc _ ≤ ∑' e, PMF.uniformFintype (Fin G.μ → G.Ch) e *
        ∑' r, PMF.uniformFintype G.Rand r * (B + S e r) :=
        ENNReal.tsum_le_tsum fun e => mul_le_mul_right
          (ENNReal.tsum_le_tsum fun r => mul_le_mul_right ((hterm e r).trans (le_of_eq (by
            rw [hB, hN, hL, hS]))) _) _
    _ = B + ∑' e, PMF.uniformFintype (Fin G.μ → G.Ch) e *
          ∑' r, PMF.uniformFintype G.Rand r * S e r := by
        simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    _ ≤ B + N * Γ := add_le_add_right hsum _
    _ = _ := by
        rw [hB, hN, hL]
        push_cast
        ring

/-- **Collision bound.** For a pair `(x, w)` with key bound `Γ`, from tables with no
hidden entry, with `L` entries and the flag cleared, a run of the real oracles
asking at most `h` hash and `q` signing queries sets the flag with probability at
most `q·(L + h + μ·q)·Γ`. -/
theorem run_real_flag_le {Γ : ℝ≥0∞} (xw : G.Stmt × G.Wit) (hΓ : G.KeyBoundAt xw.1 xw.2 Γ)
    (A : OracleAdv G.Query G.Answer α) (h q : ℕ) (hA : IsQueryBound₂ A h q)
    (t : G.Tables) (ht : t.rej = []) :
    (OracleAdv.run (toOracle (realStep xw)) A (t, false)).toOuterMeasure {y | y.2.2 = true} ≤
      ((q * (t.hash.length + t.prog.length + h + G.μ * q) : ℕ) : ℝ≥0∞) * Γ := by
  induction A generalizing h q t with
  | ret a => simp [PMF.toOuterMeasure_pure_apply]
  | rand p k ih =>
    rw [OracleAdv.run_rand, PMF.toOuterMeasure_bind_apply]
    calc ∑' b, p b * (OracleAdv.run (toOracle (realStep xw)) (k b) (t, false)).toOuterMeasure _
        ≤ ∑' b, p b *
            (((q * (t.hash.length + t.prog.length + h + G.μ * q) : ℕ) : ℝ≥0∞) * Γ) :=
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
        exact flag_sign_step_le xw hΓ k h q hA t ht m fun c t' ht' => ih c h q (hA c) t' ht'

/-! ### The collision bound class by class -/

/-- The tables after an attempt with the trace `tr` gain at most the points of class
`c` of the entries of `tr`. -/
theorem count_traceTables_le (κ : G.Classes) (t : G.Tables) (m : G.Msg) (tr : G.Trace)
    (c : κ.ι) :
    κ.count (traceTables t m tr).keys c ≤
      κ.count t.keys c + κ.count (tr.1.map Prod.fst) c + κ.count (tr.2.1.map Prod.fst) c := by
  have := κ.count_le_of_sublist ((List.filter_sublist (p := fun p : G.Key × G.Ch =>
    (t.lookup p.1).isNone) (l := tr.1)).map Prod.fst) c
  simp only [traceTables, hashAll, Protocol.Tables.keys, List.map_append, κ.count_append] at this ⊢
  omega

theorem count_guessView_le (κ : G.Classes) (look : G.Key → Option G.Ch) (x : G.Stmt)
    (w : G.Wit) (m : G.Msg) (r : G.Rand) (e : Fin G.μ → G.Ch) (i : Fin G.μ) (c : κ.ι) :
    κ.count ((G.guessView look x w m r e i).1.map Prod.fst) c +
      κ.count ((G.guessView look x w m r e i).2.1.map Prod.fst) c ≤ κ.μc c := by
  unfold Protocol.guessView
  split
  · exact Nat.zero_le _
  · have := κ.count_trace_entries x w m r (G.vals look x w m r e) c
    simp only [Protocol.trace, Protocol.view]
    omega

/-- When a programmed or hidden entry of an attempt is at a point defined in `look`,
so is a charged entry: the entry itself, or a hidden entry at a defined point. -/
theorem exists_charged_of_flagging (look : G.Key → Option G.Ch) (x : G.Stmt) (w : G.Wit)
    (m : G.Msg) (r : G.Rand) (v : Fin G.μ → G.Ch)
    (h : ∃ i, G.flagging x w m r v i = true ∧ (look (G.key x w m r v i)).isSome) :
    ∃ i, G.charged look x w m r v i = true ∧ (look (G.key x w m r v i)).isSome := by
  obtain ⟨i, hf, hi⟩ := h
  cases hc : G.charged look x w m r v i
  · have hh : G.hidFresh look x w m r v = false := by
      simp only [Protocol.charged, hf, Bool.true_and, Bool.or_eq_false_iff] at hc
      exact hc.2
    simp only [Protocol.hidFresh, List.all_eq_false, List.mem_finRange, true_and,
      Bool.or_eq_true, not_or, Bool.not_eq_true, Option.isNone_eq_false_iff] at hh
    obtain ⟨j, hj, hk⟩ := hh
    refine ⟨j, ?_, by simpa using hk⟩
    simp [Protocol.charged, Protocol.flagging, hj]
  · exact ⟨i, hc, hi⟩

/-- **Guessing the points of one class.** For a pair with class-wise key bound `Γ`
and runs `R tr` indexed by traces whose final tables have at most `N` points of
class `c` on the traces `guessView`, the expectation over the values and the
randomness of the number of charged entries of class `c` whose point is defined at
the end of `R (guessView …)` is at most `N·Γ c`. -/
theorem tsum_guess_le_cls (κ : G.Classes) {Γ : κ.ι → ℝ≥0∞} (x : G.Stmt) (w : G.Wit)
    (hΓ : G.KeyBoundClsAt κ x w Γ) (c : κ.ι) (m : G.Msg) (look : G.Key → Option G.Ch)
    (R : G.Trace → PMF (α × (G.Tables × Bool))) (N : ℕ)
    (hN : ∀ e r i, ∀ y ∈ (R (G.guessView look x w m r e i)).support,
      κ.count y.2.1.keys c ≤ N) :
    ∑' e, PMF.uniformFintype (Fin G.μ → G.Ch) e * ∑' r, PMF.uniformFintype G.Rand r *
      ∑ i ∈ Finset.univ.filter (fun i => κ.ecls i = c),
        (if G.charged look x w m r (G.vals look x w m r e) i then
          (R (G.guessView look x w m r e i)).toOuterMeasure
            {y | G.key x w m r (G.vals look x w m r e) i ∈ y.2.1.keys} else 0) ≤ N * Γ c := by
  rcases isEmpty_or_nonempty G.Key with hK | ⟨⟨k₀⟩⟩
  · have : IsEmpty (Fin G.μ) := ⟨fun i => hK.false (G.key x w m (Classical.arbitrary _)
      (Classical.arbitrary _) i)⟩
    simp
  -- the guess of the `j`-th point of class `c` of the final tables
  let Q : ℕ → G.Trace → PMF G.Key := fun j tr =>
    (R tr).map fun y => (y.2.1.keys.filter fun k => κ.cls k = c).getD j k₀
  have h1 : ∀ e r, ∀ i ∈ Finset.univ.filter (fun i => κ.ecls i = c),
      (if G.charged look x w m r (G.vals look x w m r e) i then
        (R (G.guessView look x w m r e i)).toOuterMeasure
          {y | G.key x w m r (G.vals look x w m r e) i ∈ y.2.1.keys} else 0) ≤
      ∑ j ∈ Finset.range N, (if G.charged look x w m r (G.vals look x w m r e) i then
        Q j (G.guessView look x w m r e i) (G.key x w m r (G.vals look x w m r e) i)
        else 0) := fun e r i hi => by
    split_ifs
    · refine le_trans (MeasureTheory.measure_mono fun y hy => ?_)
        (toOuterMeasure_mem_le_sum (R (G.guessView look x w m r e i))
          (fun y => y.2.1.keys.filter fun k => κ.cls k = c) N k₀
          (G.key x w m r (G.vals look x w m r e) i) (hN e r i))
      refine List.mem_filter.mpr ⟨hy, ?_⟩
      simpa [κ.key_cls] using (Finset.mem_filter.mp hi).2
    · exact zero_le
  calc _ ≤ ∑' e, PMF.uniformFintype (Fin G.μ → G.Ch) e * ∑' r, PMF.uniformFintype G.Rand r *
        ∑ j ∈ Finset.range N, ∑ i ∈ Finset.univ.filter (fun i => κ.ecls i = c),
          (if G.charged look x w m r (G.vals look x w m r e) i then
            Q j (G.guessView look x w m r e i) (G.key x w m r (G.vals look x w m r e) i)
            else 0) := by
        refine ENNReal.tsum_le_tsum fun e => mul_le_mul_right
          (ENNReal.tsum_le_tsum fun r => mul_le_mul_right ?_ _) _
        rw [Finset.sum_comm]
        exact Finset.sum_le_sum fun i hi => h1 e r i hi
    _ = ∑ j ∈ Finset.range N, ∑' e, PMF.uniformFintype (Fin G.μ → G.Ch) e *
          ∑' r, PMF.uniformFintype G.Rand r *
            ∑ i ∈ Finset.univ.filter (fun i => κ.ecls i = c),
            (if G.charged look x w m r (G.vals look x w m r e) i then
              Q j (G.guessView look x w m r e i) (G.key x w m r (G.vals look x w m r e) i)
              else 0) := tsum_mul_tsum_mul_finsetSum _ _ _ _
    _ ≤ ∑ _j ∈ Finset.range N, Γ c := Finset.sum_le_sum fun j _ => hΓ c m look (Q j)
    _ = N * Γ c := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

/-- The class-wise collision bound `Σ_c q·(L_c + n_c + μc c·q)·Γ c` from the tables
`t`, with `L_c` the points of class `c` in `t`. -/
noncomputable def flagBoundCls (κ : G.Classes) (Γ : κ.ι → ℝ≥0∞) (n : κ.ι → ℕ) (q : ℕ)
    (t : G.Tables) : ℝ≥0∞ :=
  ∑ c, ((q * (κ.count t.keys c + n c + κ.μc c * q) : ℕ) : ℝ≥0∞) * Γ c

/-- One signing attempt in the induction of `run_real_flag_le_cls`: the probability
that the rest of the run sets the flag is at most the bound for the tables after the
attempt plus, for each charged entry, the probability that its point is defined at
the end of the rest of the run from the trace `guessView`. -/
theorem flag_sign_term_le_cls (κ : G.Classes) (xw : G.Stmt × G.Wit) {Γ : κ.ι → ℝ≥0∞}
    (k : G.Answer → OracleAdv G.Query G.Answer α) (n : κ.ι → ℕ) (q : ℕ) (t : G.Tables)
    (ht : t.rej = []) (m : G.Msg) (e : Fin G.μ → G.Ch) (r : G.Rand)
    (ih : ∀ c (t' : G.Tables), t'.rej = [] →
      (OracleAdv.run (toOracle (realStep xw)) (k c) (t', false)).toOuterMeasure
        {y | y.2.2 = true} ≤ flagBoundCls κ Γ n q t') :
    (OracleAdv.run (toOracle (realStep xw)) (k (realSignOut xw.1 xw.2 t false m e r).1)
        (realSignOut xw.1 xw.2 t false m e r).2).toOuterMeasure {y | y.2.2 = true} ≤
      ∑ c, ((q * (κ.count t.keys c + κ.μc c + n c + κ.μc c * q) : ℕ) : ℝ≥0∞) * Γ c +
        ∑ i, (if G.charged t.lookup xw.1 xw.2 m r (G.vals t.lookup xw.1 xw.2 m r e) i then
          (contRun xw k t m (G.guessView t.lookup xw.1 xw.2 m r e i)).toOuterMeasure
            {y | G.key xw.1 xw.2 m r (G.vals t.lookup xw.1 xw.2 m r e) i ∈ y.2.1.keys}
          else 0) := by
  set v := G.vals t.lookup xw.1 xw.2 m r e with hv
  by_cases hc : ∃ i, G.flagging xw.1 xw.2 m r v i = true ∧
      (t.lookup (G.key xw.1 xw.2 m r v i)).isSome
  · obtain ⟨i, hf, hi⟩ := exists_charged_of_flagging t.lookup xw.1 xw.2 m r v hc
    refine (toOuterMeasure_le_one _ _).trans (le_trans ?_ le_add_self)
    refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun i =>
      if G.charged t.lookup xw.1 xw.2 m r v i then
        (contRun xw k t m (G.guessView t.lookup xw.1 xw.2 m r e i)).toOuterMeasure
          {y | G.key xw.1 xw.2 m r v i ∈ y.2.1.keys} else 0) (fun _ _ => zero_le)
      (Finset.mem_univ i))
    have hg : G.guessView t.lookup xw.1 xw.2 m r e i = ([], [], none) := by
      simp only [Protocol.guessView, ← hv, hi, Bool.or_true, ite_true]
    simp only [hf, ite_true, hg]
    refine (run_real_keys_eq_one xw _ _ _ ?_ _ fun y hy => hy).symm
    exact (le_traceTables t m _).keys_subset (Protocol.lookup_isSome_mem_keys hi)
  simp only [not_exists, not_and, Bool.not_eq_true, Option.isSome_eq_false_iff,
    Option.isNone_iff_eq_none] at hc
  rw [realSignOut_of_fresh _ _ _ _ _ _ _
    (fun i hf => (Protocol.lookupAll_of_rej_nil ht _).trans (hc i hf))
    (fun i _ _ => by rw [ht]; exact lookupIn_nil _)]
  set T₀ : G.Tables := traceTables t m (G.trace xw.1 xw.2 m r v)
  have hT : ({ T₀ with rej := t.rej ++ G.hidEntries xw.1 xw.2 m r v } : G.Tables) =
      T₀.addRejs (G.hidEntries xw.1 xw.2 m r v) := by
    simp only [Protocol.Tables.addRejs, T₀, rej_traceTables, ht, List.nil_append,
      List.append_nil]
  rw [hT]
  refine (run_real_addRejs_flag_le xw _ _ T₀ false).trans ?_
  refine (MeasureTheory.measure_mono (fun y hy => hy)).trans
    ((MeasureTheory.measure_union_le _ _).trans (add_le_add ?_ ?_))
  · refine (ih _ T₀ ht).trans
      (Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_right ?_ zero_le)
    have h1 : κ.count T₀.keys c ≤ κ.count t.keys c +
        κ.count ((G.evEntries xw.1 xw.2 m r v).map Prod.fst) c +
        κ.count ((G.pubEntries xw.1 xw.2 m r v).map Prod.fst) c :=
      count_traceTables_le κ t m _ c
    have h2 := κ.count_trace_entries xw.1 xw.2 m r v c
    exact_mod_cast Nat.mul_le_mul_left _ (by omega)
  · calc _ ≤ (contRun xw k t m (G.trace xw.1 xw.2 m r v)).toOuterMeasure
            (⋃ i ∈ Finset.univ.filter (fun i => G.pub xw.1 xw.2 m r v i = false),
              {y | G.key xw.1 xw.2 m r v i ∈ y.2.1.keys}) := by
          refine MeasureTheory.measure_mono fun y hy => ?_
          obtain ⟨p, hp, hk⟩ := hy
          obtain ⟨i, hi, rfl⟩ := Protocol.mem_entries hp
          simp only [Set.mem_iUnion, Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨i, by simpa using hi, hk⟩
      _ ≤ ∑ i ∈ Finset.univ.filter (fun i => G.pub xw.1 xw.2 m r v i = false),
            (contRun xw k t m (G.trace xw.1 xw.2 m r v)).toOuterMeasure
              {y | G.key xw.1 xw.2 m r v i ∈ y.2.1.keys} :=
          MeasureTheory.measure_biUnion_finset_le _ _
      _ = ∑ i ∈ Finset.univ.filter (fun i => G.pub xw.1 xw.2 m r v i = false),
            (if G.charged t.lookup xw.1 xw.2 m r v i then
              (contRun xw k t m (G.guessView t.lookup xw.1 xw.2 m r e i)).toOuterMeasure
                {y | G.key xw.1 xw.2 m r v i ∈ y.2.1.keys} else 0) := by
          refine Finset.sum_congr rfl fun i hi => ?_
          have hi' : G.pub xw.1 xw.2 m r v i = false := (Finset.mem_filter.mp hi).2
          have hf : G.flagging xw.1 xw.2 m r v i = true := by simp [Protocol.flagging, hi']
          have hch : G.charged t.lookup xw.1 xw.2 m r v i = true := by
            simp [Protocol.charged, hf, hi']
          have hg : G.guessView t.lookup xw.1 xw.2 m r e i = G.trace xw.1 xw.2 m r v := by
            simp only [Protocol.guessView, ← hv, hi', hc i hf, Option.isSome_none,
              Bool.or_false, Bool.false_eq_true, ite_false]
          rw [ite_eq_left hch, hg]
      _ ≤ _ := Finset.sum_le_sum_of_subset (Finset.filter_subset _ _)

/-- A hash query in the induction of `run_real_flag_le_cls`. -/
theorem flag_hash_step_le_cls (κ : G.Classes) (xw : G.Stmt × G.Wit) {Γ : κ.ι → ℝ≥0∞}
    (k : G.Answer → OracleAdv G.Query G.Answer α) (n : κ.ι → ℕ) (q : ℕ) (t : G.Tables)
    (ht : t.rej = []) (key : G.Key) (hn : ∀ c, κ.hashCost c (.inl key) ≤ n c)
    (ih : ∀ c (t' : G.Tables), t'.rej = [] →
      (OracleAdv.run (toOracle (realStep xw)) (k c) (t', false)).toOuterMeasure
        {y | y.2.2 = true} ≤ flagBoundCls κ Γ (fun c => n c - κ.hashCost c (.inl key)) q t') :
    (OracleAdv.run (toOracle (realStep xw)) (.query (.inl key) k) (t, false)).toOuterMeasure
        {y | y.2.2 = true} ≤ flagBoundCls κ Γ n q t := by
  rw [OracleAdv.run_query]
  simp only [toOracle, realStep, realHashStep]
  cases hl : t.lookup key with
  | some e =>
    simp only [Step.toPMF, PMF.pure_bind]
    refine (ih _ t ht).trans
      (Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_right ?_ zero_le)
    exact_mod_cast Nat.mul_le_mul_left _ (by dsimp only; omega)
  | none =>
    have hr : lookupIn t.rej key = none := by rw [ht]; exact lookupIn_nil key
    simp only [hr, Step.toPMF, PMF.bind_map, Function.comp_def, PMF.toOuterMeasure_bind_apply]
    calc ∑' e, PMF.uniformFintype G.Ch e * (OracleAdv.run (toOracle (realStep xw))
          (k (.inl e)) ({ t with hash := t.hash ++ [(key, e)] }, false)).toOuterMeasure _
        ≤ ∑' e, PMF.uniformFintype G.Ch e * flagBoundCls κ Γ n q t := by
          refine ENNReal.tsum_le_tsum fun e => mul_le_mul_right ?_ _
          refine (ih _ { t with hash := t.hash ++ [(key, e)] } ht).trans
            (Finset.sum_le_sum fun c _ => mul_le_mul_of_nonneg_right ?_ zero_le)
          have h1 := hn c
          have h2 := count_hash_append κ t key e c
          exact_mod_cast Nat.mul_le_mul_left _ (by dsimp only; omega)
      _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- The guess terms of a signing attempt in the induction of `run_real_flag_le_cls`:
the expectation over the values and the randomness of the number of charged entries
whose point is defined at the end of the rest of the run is at most
`Σ_c (L_c + μc c + n_c + μc c·q)·Γ c`. -/
theorem flag_guess_le_cls (κ : G.Classes) (xw : G.Stmt × G.Wit) {Γ : κ.ι → ℝ≥0∞}
    (hΓ : G.KeyBoundClsAt κ xw.1 xw.2 Γ) (k : G.Answer → OracleAdv G.Query G.Answer α)
    (h q : ℕ) (n : κ.ι → ℕ) (hk : ∀ r, IsQueryBound₂ (k r) h q)
    (hn : ∀ c r, (k r).IsQueryBoundBy (κ.hashCost c) (n c)) (t : G.Tables) (m : G.Msg) :
    ∑' e, PMF.uniformFintype (Fin G.μ → G.Ch) e * ∑' r, PMF.uniformFintype G.Rand r *
      ∑ i, (if G.charged t.lookup xw.1 xw.2 m r (G.vals t.lookup xw.1 xw.2 m r e) i then
        (contRun xw k t m (G.guessView t.lookup xw.1 xw.2 m r e i)).toOuterMeasure
          {y | G.key xw.1 xw.2 m r (G.vals t.lookup xw.1 xw.2 m r e) i ∈ y.2.1.keys}
        else 0) ≤
      ∑ c, ((κ.count t.keys c + κ.μc c + n c + κ.μc c * q : ℕ) : ℝ≥0∞) * Γ c := by
  simp only [← Finset.sum_fiberwise Finset.univ κ.ecls]
  rw [tsum_mul_tsum_mul_finsetSum]
  refine Finset.sum_le_sum fun c _ => ?_
  refine tsum_guess_le_cls κ xw.1 xw.2 hΓ c m t.lookup (contRun xw k t m) _ fun e r i y hy => ?_
  have h1 := run_real_support_size_cls κ xw _ c h q (n c) (hk _) (hn c _) _ y hy
  have h2 := count_guessView_le κ t.lookup xw.1 xw.2 m r e i c
  have h3 := count_traceTables_le κ t m (G.guessView t.lookup xw.1 xw.2 m r e i) c
  dsimp only at h1
  omega

/-- A signing query in the induction of `run_real_flag_le_cls`. -/
theorem flag_sign_step_le_cls (κ : G.Classes) (xw : G.Stmt × G.Wit) {Γ : κ.ι → ℝ≥0∞}
    (hΓ : G.KeyBoundClsAt κ xw.1 xw.2 Γ) (k : G.Answer → OracleAdv G.Query G.Answer α)
    (h q : ℕ) (n : κ.ι → ℕ) (hk : ∀ r, IsQueryBound₂ (k r) h q)
    (hn : ∀ c r, (k r).IsQueryBoundBy (κ.hashCost c) (n c)) (t : G.Tables) (ht : t.rej = [])
    (m : G.Msg)
    (ih : ∀ c (t' : G.Tables), t'.rej = [] →
      (OracleAdv.run (toOracle (realStep xw)) (k c) (t', false)).toOuterMeasure
        {y | y.2.2 = true} ≤ flagBoundCls κ Γ n q t') :
    (OracleAdv.run (toOracle (realStep xw)) (.query (.inr m) k) (t, false)).toOuterMeasure
        {y | y.2.2 = true} ≤ flagBoundCls κ Γ n (q + 1) t := by
  set N : κ.ι → ℕ := fun c => κ.count t.keys c + κ.μc c + n c + κ.μc c * q with hN
  set B : ℝ≥0∞ := ∑ c, ((q * N c : ℕ) : ℝ≥0∞) * Γ c with hB
  -- the guess terms of the attempt with the values `e` and the randomness `r`
  set S : (Fin G.μ → G.Ch) → G.Rand → ℝ≥0∞ := fun e r =>
    ∑ i, (if G.charged t.lookup xw.1 xw.2 m r (G.vals t.lookup xw.1 xw.2 m r e) i then
      (contRun xw k t m (G.guessView t.lookup xw.1 xw.2 m r e i)).toOuterMeasure
        {y | G.key xw.1 xw.2 m r (G.vals t.lookup xw.1 xw.2 m r e) i ∈ y.2.1.keys}
      else 0) with hS
  have hterm := fun e r => flag_sign_term_le_cls κ xw k n q t ht m e r ih
  have hsum : ∑' e, PMF.uniformFintype (Fin G.μ → G.Ch) e *
      ∑' r, PMF.uniformFintype G.Rand r * S e r ≤ ∑ c, (N c : ℝ≥0∞) * Γ c :=
    flag_guess_le_cls κ xw hΓ k h q n hk hn t m
  rw [OracleAdv.run_query]
  simp only [toOracle, realStep, Step.toPMF, sampleVec_bind, PMF.toOuterMeasure_bind_apply]
  calc _ ≤ ∑' e, PMF.uniformFintype (Fin G.μ → G.Ch) e *
        ∑' r, PMF.uniformFintype G.Rand r * (B + S e r) :=
        ENNReal.tsum_le_tsum fun e => mul_le_mul_right
          (ENNReal.tsum_le_tsum fun r => mul_le_mul_right (hterm e r) _) _
    _ = B + ∑' e, PMF.uniformFintype (Fin G.μ → G.Ch) e *
          ∑' r, PMF.uniformFintype G.Rand r * S e r := by
        simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    _ ≤ B + ∑ c, (N c : ℝ≥0∞) * Γ c := add_le_add_right hsum _
    _ = _ := by
        rw [hB, flagBoundCls, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [hN]
        push_cast
        ring

/-- **Class-wise collision bound.** For a pair `(x, w)` with class-wise key bound
`Γ`, from tables with no hidden entry, with `L_c` points of class `c` and the flag
cleared, a run of the real oracles asking at most `q` signing queries and hash
queries of total cost at most `n c` for each class `c` sets the flag with
probability at most `Σ_c q·(L_c + n c + μc c·q)·Γ c`. -/
theorem run_real_flag_le_cls (κ : G.Classes) {Γ : κ.ι → ℝ≥0∞} (xw : G.Stmt × G.Wit)
    (hΓ : G.KeyBoundClsAt κ xw.1 xw.2 Γ) (A : OracleAdv G.Query G.Answer α) (h q : ℕ)
    (hA : IsQueryBound₂ A h q) (n : κ.ι → ℕ) (hn : ∀ c, A.IsQueryBoundBy (κ.hashCost c) (n c))
    (t : G.Tables) (ht : t.rej = []) :
    (OracleAdv.run (toOracle (realStep xw)) A (t, false)).toOuterMeasure {y | y.2.2 = true} ≤
      ∑ c, ((q * (κ.count t.keys c + n c + κ.μc c * q) : ℕ) : ℝ≥0∞) * Γ c := by
  induction A generalizing h q n t with
  | ret a => simp [PMF.toOuterMeasure_pure_apply]
  | rand p k ih =>
    rw [OracleAdv.run_rand, PMF.toOuterMeasure_bind_apply]
    calc ∑' b, p b * (OracleAdv.run (toOracle (realStep xw)) (k b) (t, false)).toOuterMeasure _
        ≤ ∑' b, p b * flagBoundCls κ Γ n q t :=
          ENNReal.tsum_le_tsum fun b =>
            mul_le_mul_right (ih b h q (hA b) n (fun c => hn c b) t ht) _
      _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul, flagBoundCls]
  | query d k ih =>
    cases d with
    | inl key =>
      cases h with
      | zero => exact hA.elim
      | succ h =>
        exact flag_hash_step_le_cls κ xw k n q t ht key (fun c => (hn c).1)
          fun a t' ht' => ih a h q (hA a) _ (fun c => (hn c).2 a) t' ht'
    | inr m =>
      have hn' : ∀ c r, (k r).IsQueryBoundBy (κ.hashCost c) (n c) := fun c r => by
        simpa [Protocol.Classes.hashCost] using (hn c).2 r
      cases q with
      | zero => exact hA.elim
      | succ q =>
        exact flag_sign_step_le_cls κ xw hΓ k h q n hA hn' t ht m
          fun a t' ht' => ih a h q (hA a) n (fun c => hn' c a) t' ht'

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

/-- The verifier points of class `c` from the `a`-th one on are the point `a`, when
it is of class `c`, and those from the `(a + 1)`-th one on. -/
theorem card_vcls_ge (κ : G.Classes) (c : κ.ι) (a : ℕ) (h : a < G.V) :
    (Finset.univ.filter fun j : Fin G.V => a ≤ j.val ∧ κ.vcls j = c).card =
      (Finset.univ.filter fun j : Fin G.V => a + 1 ≤ j.val ∧ κ.vcls j = c).card +
        if κ.vcls ⟨a, h⟩ = c then 1 else 0 := by
  have : (Finset.univ.filter fun j : Fin G.V => a ≤ j.val ∧ κ.vcls j = c) =
      (Finset.univ.filter fun j : Fin G.V => a + 1 ≤ j.val ∧ κ.vcls j = c) ∪
        (Finset.univ.filter fun j : Fin G.V => j = ⟨a, h⟩ ∧ κ.vcls j = c) := by
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Fin.ext_iff]
    by_cases hj : κ.vcls j = c
    · simp only [hj, and_true]
      omega
    · simp [hj]
  rw [this, Finset.card_union_of_disjoint]
  · congr 1
    split_ifs with hc
    · rw [Finset.card_eq_one]
      refine ⟨⟨a, h⟩, ?_⟩
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
      exact ⟨fun h => h.1, fun h => ⟨h, h ▸ hc⟩⟩
    · rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      rintro j - ⟨rfl, hj⟩
      exact hc hj
  · rw [Finset.disjoint_filter]
    rintro j - ⟨h1, -⟩ ⟨rfl, -⟩
    simp only at h1
    omega

/-- The verifier's remaining queries after the values `acc` cost at most the number
of verifier points of class `c` from the `acc.length`-th one on. -/
theorem isQueryBoundBy_verifyQueries_cls (κ : G.Classes) (c : κ.ι) (x : G.Stmt) (m : G.Msg)
    (σ : G.Sig) (n : ℕ) (acc : List G.Ch) (hn : acc.length + n = G.V) :
    (verifyQueries x m σ n acc).IsQueryBoundBy (κ.hashCost c)
      (Finset.univ.filter fun j : Fin G.V => acc.length ≤ j.val ∧ κ.vcls j = c).card := by
  induction n generalizing acc with
  | zero => trivial
  | succ n ih =>
    have ha : acc.length < G.V := by omega
    have hcost : κ.hashCost c (.inl (G.vkey x m σ acc)) =
        if κ.vcls ⟨acc.length, ha⟩ = c then 1 else 0 := by
      simp only [Protocol.Classes.hashCost, Sum.elim_inl, κ.vkey_cls x m σ acc ha]
    rw [card_vcls_ge κ c acc.length ha]
    refine ⟨by rw [hcost]; omega, fun a => ?_⟩
    rw [hcost, Nat.add_sub_cancel]
    cases a with
    | inl e =>
      have := ih (acc ++ [e]) (by simp only [List.length_append, List.length_singleton]; omega)
      simpa only [List.length_append, List.length_singleton] using this
    | inr _ => trivial

/-- An adversary whose hash queries cost at most `n` for the class `c`, followed by
the verifier's queries, costs at most `n + Vc c`. -/
theorem isQueryBoundBy_withVerify_cls (κ : G.Classes) (c : κ.ι) (x : G.Stmt)
    (A : OracleAdv G.Query G.Answer G.Forgery) (n : ℕ)
    (hA : A.IsQueryBoundBy (κ.hashCost c) n) :
    (withVerify x A).IsQueryBoundBy (κ.hashCost c) (n + κ.Vc c) := by
  induction A generalizing n with
  | ret y =>
    obtain ⟨m, σ⟩ := y
    refine (isQueryBoundBy_verifyQueries_cls κ c x m σ G.V [] (by simp)).mono ?_
    simp only [List.length_nil, Nat.zero_le, true_and, Protocol.Classes.Vc]
    omega
  | rand p k ih => exact fun b => ih b n (hA b)
  | query d k ih =>
    refine ⟨hA.1.trans (Nat.le_add_right _ _), fun r => ?_⟩
    have := ih r _ (hA.2 r)
    rwa [show n + κ.Vc c - κ.hashCost c d = n - κ.hashCost c d + κ.Vc c by
      have := hA.1; omega]

/-- The advantage in a game built by `gameDist` as an average over generated
pairs. -/
theorem prTrue_gameDist (O : G.Stmt × G.Wit → G.Tables × Bool → G.Query →
    Step G.Answer (G.Tables × Bool) G.Ch) {qH qS : ℕ} (A : G.Adversary qH qS) :
    prTrue (liftPMF (gameDist O A)) Heap.empty =
      ∑' xw, G.gen xw *
        (OracleAdv.run (toOracle (O xw)) (withVerify xw.1 (A.run xw.1))
          (Protocol.Tables.empty, false)).toOuterMeasure {y | wins xw.1 y = true} := by
  rw [prTrue_liftPMF_toOuterMeasure]
  simp only [gameDist, PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_map_apply]
  rfl

end Game

end CatCrypt.Crypto.FiatShamirROM
