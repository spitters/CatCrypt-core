/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Signatures.Scheme
public import CatCryptCore.Crypto.ForkingLemma

/-!
# Generic EUF-CMA Security Game

Existential Unforgeability under Chosen Message Attack (EUF-CMA) for
generic signature schemes, with a signing oracle whose queries are logged
by the challenger.

An adversary is an oracle program (`OracleProg`): a tree of `SPComp` steps
and signing queries. The game interprets it with `OracleProg.runLog`, which
answers each query with the signing algorithm and appends the query and its
answer to a log. The forgery must be on a message absent from that log.

## Main definitions

* `OracleProg` — programs with `SPComp` steps and queries to one oracle
* `OracleProg.runWith` — interpretation against an oracle that returns log entries
* `OracleProg.runLog` — interpretation logging every `(query, answer)` pair
* `OracleProg.bindQueries` — replace each query by an oracle program
* `OracleProg.collectLog` — replace each query by an oracle program that also
  returns records, collecting the records
* `QueryCostLe` — the query costs on every path sum to at most a bound
* `EUFCMAAdversary` — adversary: public key to an oracle program producing a forgery
* `eufcmaGame` — the EUF-CMA security game
* `eufcmaAdvantage` — forgery probability

## Main results

* `OracleProg.runWith_bind`, `OracleProg.runWith_bindQueries`,
  `OracleProg.runWith_mapLog`, `OracleProg.runWith_collectLog` — equations for
  the interpretation
* `OracleProg.runWith_any_le` — union bound over the queries of a program with
  bounded query cost
* `eufcmaAdvantage_replay` — the adversary `eufcmaReplayAdversary`, which outputs
  a signature it obtained from the oracle, has advantage 0
* `eufcmaAdvantage_eq_zero_of_verify_false` — against a scheme whose verifier
  rejects every input, every adversary has advantage 0

## References

* [Goldreich — Foundations of Cryptography, Vol. 2, §6.1]
* [Boneh, Shoup — A Graduate Course in Applied Cryptography, Def. 13.2]
* [Cohen, Lindell, Osborn, Shany — ePrint 2024/1807]
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal

namespace CatCrypt.Crypto

/-! ## Oracle programs -/

/-- A probabilistic program with access to one oracle `I → O`, returning `α`.

    `pure a` returns `a`; `query i k` asks the oracle on `i` and continues
    with `k` applied to the answer; `lift c k` runs the stateful probabilistic
    computation `c` and continues with `k` applied to its result. -/
inductive OracleProg (I O α : Type) : Type 1 where
  | pure (a : α) : OracleProg I O α
  | query (i : I) (k : O → OracleProg I O α) : OracleProg I O α
  | lift {β : Type} (c : SPComp β) (k : β → OracleProg I O α) : OracleProg I O α

/-- `QueryCostLe cost p n`: on every path of `p` the costs of the queries sum to
    at most `n`. -/
def QueryCostLe {I O α : Type} (cost : I → ℕ) : OracleProg I O α → ℕ → Prop
  | .pure _, _ => True
  | .query i k, n => cost i ≤ n ∧ ∀ o, QueryCostLe cost (k o) (n - cost i)
  | .lift _ k, n => ∀ b, QueryCostLe cost (k b) n

namespace OracleProg

variable {I O I' O' α β γ : Type}

/-- Sequential composition of oracle programs. -/
def bind : OracleProg I O α → (α → OracleProg I O β) → OracleProg I O β
  | .pure a, f => f a
  | .query i k, f => .query i (fun o => bind (k o) f)
  | .lift c k, f => .lift c (fun b => bind (k b) f)

instance : Monad (OracleProg I O) where
  pure := OracleProg.pure
  bind := OracleProg.bind

/-- One oracle query, returning the answer. -/
def ask (i : I) : OracleProg I O O := .query i OracleProg.pure

/-- One `SPComp` step, returning its result. -/
def step (c : SPComp β) : OracleProg I O β := .lift c OracleProg.pure

@[simp] theorem pure_eq (a : α) : (Pure.pure a : OracleProg I O α) = .pure a := rfl

@[simp] theorem bind_eq (p : OracleProg I O α) (f : α → OracleProg I O β) :
    p >>= f = p.bind f := rfl

@[simp] theorem pure_bind (a : α) (f : α → OracleProg I O β) :
    (OracleProg.pure a).bind f = f a := rfl

@[simp] theorem query_bind (i : I) (k : O → OracleProg I O α) (f : α → OracleProg I O β) :
    (OracleProg.query i k).bind f = .query i (fun o => (k o).bind f) := rfl

@[simp] theorem lift_bind (c : SPComp γ) (k : γ → OracleProg I O α)
    (f : α → OracleProg I O β) :
    (OracleProg.lift c k).bind f = .lift c (fun b => (k b).bind f) := rfl

@[simp] theorem ask_bind (i : I) (f : O → OracleProg I O β) :
    (ask i).bind f = .query i f := rfl

@[simp] theorem step_bind (c : SPComp γ) (f : γ → OracleProg I O β) :
    (step c : OracleProg I O γ).bind f = .lift c f := rfl

/-! ## Interpretation -/

/-- Run an oracle program against an oracle that returns, with each answer, a
    list of log entries. The result carries the concatenation of the entries
    of all queries in query order. -/
noncomputable def runWith {L : Type} (oracle : I → SPComp (O × List L)) :
    OracleProg I O α → SPComp (α × List L)
  | .pure a => SPComp.pure (a, [])
  | .query i k => SPComp.bind (oracle i) (fun ol =>
      SPComp.bind (runWith oracle (k ol.1)) (fun al => SPComp.pure (al.1, ol.2 ++ al.2)))
  | .lift c k => SPComp.bind c (fun b => runWith oracle (k b))

/-- The oracle `oracle` with each answer logged together with its query. -/
noncomputable def logging (oracle : I → SPComp O) : I → SPComp (O × List (I × O)) :=
  fun i => SPComp.bind (oracle i) (fun o => SPComp.pure (o, [(i, o)]))

/-- Run an oracle program against `oracle`, logging every query with its answer. -/
noncomputable def runLog (oracle : I → SPComp O) (p : OracleProg I O α) :
    SPComp (α × List (I × O)) :=
  runWith (logging oracle) p

/-- Replace every query of a program by an oracle program over another oracle. -/
def bindQueries (h : I → OracleProg I' O' O) : OracleProg I O α → OracleProg I' O' α
  | .pure a => .pure a
  | .query i k => (h i).bind (fun o => bindQueries h (k o))
  | .lift c k => .lift c (fun b => bindQueries h (k b))

section Equations

variable {L L' : Type}

@[simp] theorem runWith_pure (oracle : I → SPComp (O × List L)) (a : α) :
    runWith oracle (OracleProg.pure a) = SPComp.pure (a, []) := rfl

@[simp] theorem runWith_query (oracle : I → SPComp (O × List L)) (i : I)
    (k : O → OracleProg I O α) :
    runWith oracle (OracleProg.query i k) =
      SPComp.bind (oracle i) (fun ol =>
        SPComp.bind (runWith oracle (k ol.1)) (fun al => SPComp.pure (al.1, ol.2 ++ al.2))) :=
  rfl

@[simp] theorem runWith_lift (oracle : I → SPComp (O × List L)) (c : SPComp β)
    (k : β → OracleProg I O α) :
    runWith oracle (OracleProg.lift c k) = SPComp.bind c (fun b => runWith oracle (k b)) :=
  rfl

/-- The interpretation of a composite program runs the two parts in sequence
    and concatenates their logs. -/
theorem runWith_bind (oracle : I → SPComp (O × List L)) (p : OracleProg I O α)
    (f : α → OracleProg I O β) :
    runWith oracle (p.bind f) =
      SPComp.bind (runWith oracle p) (fun al =>
        SPComp.bind (runWith oracle (f al.1)) (fun bl => SPComp.pure (bl.1, al.2 ++ bl.2))) := by
  induction p with
  | pure a =>
    simp only [pure_bind, runWith_pure, SPComp.pure_bind, List.nil_append]
    exact (SPComp.bind_pure _).symm
  | query i k ih =>
    simp only [query_bind, runWith_query, ih, SPComp.bind_assoc, SPComp.pure_bind,
      List.append_assoc]
  | lift c k ih =>
    simp only [lift_bind, runWith_lift, ih, SPComp.bind_assoc]

/-- Substituting oracle programs for the queries of `p` and interpreting the
    result is interpreting `p` against the interpreted substitutes. -/
theorem runWith_bindQueries (oracle : I' → SPComp (O' × List L))
    (h : I → OracleProg I' O' O) (p : OracleProg I O α) :
    runWith oracle (bindQueries h p) = runWith (fun i => runWith oracle (h i)) p := by
  induction p with
  | pure a => rfl
  | query i k ih =>
    simp only [bindQueries, runWith_bind, runWith_query, ih]
  | lift c k ih =>
    simp only [bindQueries, runWith_lift, ih]

/-- Mapping every log entry of the oracle maps the log of the run. -/
theorem runWith_mapLog (oracle : I → SPComp (O × List L)) (g : L → L')
    (p : OracleProg I O α) :
    runWith (fun i => SPComp.bind (oracle i) (fun ol => SPComp.pure (ol.1, ol.2.map g))) p =
      SPComp.bind (runWith oracle p) (fun al => SPComp.pure (al.1, al.2.map g)) := by
  induction p with
  | pure a => simp only [runWith_pure, SPComp.pure_bind, List.map_nil]
  | query i k ih =>
    simp only [runWith_query, ih, SPComp.bind_assoc, SPComp.pure_bind, List.map_append]
  | lift c k ih =>
    simp only [runWith_lift, ih, SPComp.bind_assoc]

end Equations

section Records

variable {Q R L M : Type}

/-- Replace every query of `p` by an oracle program that returns an answer and a
    list of records, and collect the records of all queries in query order. -/
def collectLog (h : Q → OracleProg I O (R × List L)) :
    OracleProg Q R α → OracleProg I O (α × List L)
  | .pure a => .pure (a, [])
  | .query q k => (h q).bind fun rl =>
      (collectLog h (k rl.1)).bind fun al => .pure (al.1, rl.2 ++ al.2)
  | .lift c k => .lift c fun b => collectLog h (k b)

/-- If every query program `h q`, run against `oracle`, is the oracle `expO q`
    followed by the log `proj` of its records, then running `collectLog h p`
    against `oracle` is running `p` against `expO`, with the oracle's log the
    concatenation of `proj` over the records. -/
theorem runWith_collectLog (oracle : I → SPComp (O × List M))
    (h : Q → OracleProg I O (R × List L)) (expO : Q → SPComp (R × List L)) (proj : L → List M)
    (hq : ∀ q, (h q).runWith oracle =
      SPComp.bind (expO q) fun rl => SPComp.pure (rl, rl.2.flatMap proj))
    (p : OracleProg Q R α) :
    (collectLog h p).runWith oracle =
      SPComp.bind (p.runWith expO) fun al => SPComp.pure (al, al.2.flatMap proj) := by
  induction p with
  | pure a => simp [collectLog, SPComp.pure_bind]
  | query q k ih =>
    simp only [collectLog, runWith_bind, hq, ih, runWith_query, runWith_pure, SPComp.bind_assoc,
      SPComp.pure_bind, List.flatMap_append, List.append_nil]
  | lift c k ih =>
    simp only [collectLog, runWith_lift, ih, SPComp.bind_assoc]

/-- **Union bound over queries**: if each query `i` produces a record in `bad`
    with probability at most `cost i * ε` from every heap, a program whose
    query costs sum to at most `n` on every path produces one with probability
    at most `n * ε`. -/
theorem runWith_any_le (oracle : I → SPComp (O × List L)) (bad : L → Bool) (cost : I → ℕ)
    (ε : ℝ≥0∞)
    (hstep : ∀ i h, prTrue (SPComp.bind (oracle i) fun ol => SPComp.pure (ol.2.any bad)) h ≤
      cost i * ε)
    (p : OracleProg I O α) (n : ℕ) (hp : QueryCostLe cost p n) (h₀ : Heap) :
    prTrue (SPComp.bind (p.runWith oracle) fun al => SPComp.pure (al.2.any bad)) h₀ ≤ n * ε := by
  have hconst : ∀ {β : Type} (c : SPComp β) (f : β → SPComp Bool) (h₁ : Heap) (δ : ℝ≥0∞),
      (∀ b h, prTrue (f b) h ≤ δ) → prTrue (SPComp.bind c f) h₁ ≤ δ := by
    intro β c f h₁ δ hf
    calc _ ≤ δ * prTrue (SPComp.bind c fun _ => SPComp.pure true) h₁ :=
          ForkingLemma.prTrue_bind_mono_const δ c f _ h₁ fun b h => by
            rw [ForkingLemma.prTrue_pure_bool, ite_eq_left rfl, mul_one]; exact hf b h
      _ ≤ δ := mul_le_of_le_one_right' (prTrue_le_one _ _)
  induction p generalizing n h₀ with
  | pure a =>
    simp only [runWith_pure, SPComp.pure_bind, List.any_nil, ForkingLemma.prTrue_pure_bool]
    simp
  | query i k ih =>
    obtain ⟨hle, hk⟩ := hp
    simp only [runWith_query, SPComp.bind_assoc, SPComp.pure_bind, List.any_append]
    calc _ ≤ prTrue (SPComp.bind (oracle i) fun ol => SPComp.pure (ol.2.any bad)) h₀ +
          prTrue (SPComp.bind (oracle i) fun ol =>
            SPComp.bind ((k ol.1).runWith oracle) fun al => SPComp.pure (al.2.any bad)) h₀ := by
          refine ForkingLemma.prTrue_bind_le_add _ _ _ _ _ fun ol h' => ?_
          cases hb : ol.2.any bad
          · simp only [Bool.false_or, ForkingLemma.prTrue_pure_bool]
            simp
          · simp only [Bool.true_or, ForkingLemma.prTrue_pure_bool, ite_true]
            exact le_add_right (prTrue_le_one _ _)
      _ ≤ cost i * ε + (n - cost i : ℕ) * ε := by
          gcongr
          · exact hstep i h₀
          · exact hconst _ _ _ _ fun ol h' => ih ol.1 (n - cost i) (hk ol.1) h'
      _ = n * ε := by
          rw [← add_mul]; congr 1; exact_mod_cast Nat.add_sub_cancel' hle
  | lift c k ih =>
    simp only [runWith_lift, SPComp.bind_assoc]
    exact hconst _ _ _ _ fun b h' => ih b n (hp b) h'

end Records

end OracleProg

end CatCrypt.Crypto

namespace CatCrypt.Crypto.Signatures

variable {Msg PK SK Sig : Type}

/-! ## EUF-CMA Adversary -/

/-- EUF-CMA adversary for a generic signature scheme: given the public key, an
    oracle program with signing queries that outputs a candidate forgery
    `(message, signature)`. The queries are recorded by the game, not by the
    adversary. -/
structure EUFCMAAdversary (Msg PK SK Sig : Type) : Type 1 where
  /-- The adversary's program on public key `pk`. -/
  run : PK → OracleProg Msg Sig (Msg × Sig)

/-- EUF-CMA game.

    1. Run key generation to get `(pk, sk)`.
    2. Run the adversary on `pk` with the signing oracle `S.sign sk`, logging
       every query.
    3. The adversary wins if the forgery verifies and its message is not
       among the logged queries. -/
noncomputable def eufcmaGame [DecidableEq Msg]
    (S : SigScheme Msg PK SK Sig) (A : EUFCMAAdversary Msg PK SK Sig) :
    SPComp Bool :=
  SPComp.bind S.keygen (fun ks =>
    SPComp.bind ((A.run ks.1).runLog (S.sign ks.2)) (fun out =>
      SPComp.pure (S.verify ks.1 out.1.1 out.1.2 && !(out.2.map Prod.fst).contains out.1.1)))

/-- EUF-CMA advantage: probability that the adversary produces a valid forgery. -/
noncomputable def eufcmaAdvantage [DecidableEq Msg]
    (S : SigScheme Msg PK SK Sig) (A : EUFCMAAdversary Msg PK SK Sig) :
    ℝ≥0∞ :=
  prTrue (eufcmaGame S A) Heap.empty

/-! ## Satisfiability of the game -/

/-- A game whose continuation wins with probability 0 from every intermediate
    result and heap wins with probability 0. -/
theorem prTrue_bind_eq_zero {α : Type} (c : SPComp α) (k : α → SPComp Bool) (h₀ : Heap)
    (hk : ∀ a h, prTrue (k a) h = 0) :
    prTrue (SPComp.bind c k) h₀ = 0 := by
  rw [ForkingLemma.prTrue_bind_eq_weighted]
  refine ENNReal.tsum_eq_zero.mpr (fun p => ?_)
  rcases p with _ | ⟨a, h⟩
  · simp
  · simp [hk a h]

/-- The replay adversary: query the signing oracle on `m` and output the
    answer as a forgery on `m`. -/
def eufcmaReplayAdversary (m : Msg) : EUFCMAAdversary Msg PK SK Sig where
  run := fun _ => (OracleProg.ask m).bind (fun σ => OracleProg.pure (m, σ))

/-- The replay adversary never wins: its forgery message is in the log. -/
theorem eufcmaAdvantage_replay [DecidableEq Msg]
    (S : SigScheme Msg PK SK Sig) (m : Msg) :
    eufcmaAdvantage S (eufcmaReplayAdversary m : EUFCMAAdversary Msg PK SK Sig) = 0 := by
  have hgame : eufcmaGame S (eufcmaReplayAdversary m : EUFCMAAdversary Msg PK SK Sig) =
      SPComp.bind S.keygen (fun ks =>
        SPComp.bind (S.sign ks.2 m) (fun _ => SPComp.pure false)) := by
    unfold eufcmaGame eufcmaReplayAdversary OracleProg.runLog OracleProg.logging
    simp only [OracleProg.ask_bind, OracleProg.runWith_query, OracleProg.runWith_pure,
      SPComp.bind_assoc, SPComp.pure_bind, List.append_nil, List.map_cons, List.map_nil,
      List.contains_cons, List.contains_nil, BEq.rfl, Bool.or_false, Bool.not_true,
      Bool.and_false]
  unfold eufcmaAdvantage
  rw [hgame]
  refine prTrue_bind_eq_zero _ _ _ (fun ks h => prTrue_bind_eq_zero _ _ _ (fun _ h' => ?_))
  exact ForkingLemma.prTrue_pure_bool false h'

/-- A scheme whose verifier rejects every input gives every adversary advantage 0. -/
theorem eufcmaAdvantage_eq_zero_of_verify_false [DecidableEq Msg]
    (S : SigScheme Msg PK SK Sig) (hv : ∀ pk m σ, S.verify pk m σ = false)
    (A : EUFCMAAdversary Msg PK SK Sig) :
    eufcmaAdvantage S A = 0 := by
  unfold eufcmaAdvantage eufcmaGame
  refine prTrue_bind_eq_zero _ _ _ (fun ks h => prTrue_bind_eq_zero _ _ _ (fun out h' => ?_))
  rw [hv, Bool.false_and]
  exact ForkingLemma.prTrue_pure_bool false h'

end CatCrypt.Crypto.Signatures
