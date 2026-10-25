/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Core.SPTreeTimedOps
public import CatCryptCore.Crypto.OracleAdversaryTimed
public import CatCryptCore.Tactics.AutoDispatchCore
public import Mathlib.Tactic.Linarith
public import CatCryptCore.XDijkstra.XTimedMonad
/-!
# The time-bound procedure `time_bound`

`time_bound` proves the time bounds of costed trees in the step-prefixed convention of
`derive_timed`:

* `SPTree.Timed.stepTime x ≤ B` and `t.time ≤ B` for costed computation trees;
* `OracleAdv.Timed.StepTimeBound x n` and `A.TimeBound n` for costed oracle adversaries.

The procedure is syntax-directed on the costed tree. A goal is kept in an accumulated form:
`P + stepTime x ≤ B` (or `P + t.time ≤ B`) for computation trees, and `StepTimeBound x (B - P)`
(or `A.TimeBound (B - P)`) for oracle adversaries, where `P` is the cost of the path already
traversed. Each node of the tree is consumed by one rule lemma of this module:

* a pair `(c, t)` and `delay c x` add `c` to `P`; a pair `(c + y.1, y.2)` is read as `y` after
  `c`; a tree `y.2` on a path whose cost `P` has the summand `y.1` is read as `y`, the summand
  removed from `P` (`time_snd_fst`: a costed prefix bind `C + (D + y.1) + y.2.time` nested in
  the arithmetic of a `delay`); `map` is read as `bind`;
* a bind `y.2.bind k` after the tree of a costed bind `y = A.bind g`, on a path whose cost `P`
  has the summand `y.1`, is read as the bind of `A` into the continuations `g s` followed by
  `k`, the summand removed from `P` (`st_snd_bind_fst`, from the equation
  `stepTime_fst_bind_bind`): the form `delay (C + y.1) (y.2.bind k)` of a value bound by `have`
  before a costed bind, at the root or in a branch of a sample node; the step costs of pairs on
  `P` are reduced before `y.1` is sought;
* a node `sample`, `get`, `set`, `rand`, `query` adds its unit and its step cost and leaves one
  goal for every branch (`∀ b`), so that a maximum over a finite support becomes a universal
  statement;
* `bind A f` with `A` a node is pushed into the node; with `A` not a node, the time of `A` is
  added to `P` (`stepTime_bind_le`, `timeBound_bind`) and the continuation is bounded for
  every value;
* when that continuation bound fails, it is bounded only at the values `A` can return
  (`st_bind_inv`, from `stepTime_bind_le_of_allRet`): for each cost companion `π a : X → ℕ`
  of the bound value that the continuation reads (a chain of pair projections of `a`) and each
  local hypothesis `∀ x : X, h x ≤ c` on a companion binder `h`, the invariant
  `∀ u, π a u ≤ c + N` with the least slack `N` of `invSlack` is proved at every leaf of `A`
  by a traversal of its visible structure (`ar_*` rules, definitions unfolded, a tree without
  visible leaves by `ar_any`, each leaf closed by `omega` after its `if`s and Boolean locals
  are split); the invariants found are conjoined and assumed by the continuation;
* a heap reset `load h c t` adds `1 + |keys h| + c` to `P`;
* `if`, `if h :` and `match` are split, and a recursor or `casesOn` on a local variable is
  split by `cases` on the variable; a tree with an `if b = true` on a Boolean local `b` below a
  projection is split by `cases` on `b`; a tree `(delay c x).2` is read as `x.2`;
* a definition is unfolded when its body is visible and it is not recursive.

Before each rule, the `let` and `have` binders of the goal whose values do not depend on bound
variables are taken out of the target (`liftLets`). A binder of a costed tree, a number, a
proof or an atom is inlined. Any other binder (a state, a cost companion) becomes a let-bound
local `x := v` of the context, the binder of the smallest value first; every binder of the same
value and every occurrence of the value in the target are replaced by `x`. A step cost and a
tree that bind the same values, one through `have` binders and one with some values inlined,
then name the same locals, the rules above match them syntactically, and each value is read
once. For each cost companion `π x : X → ℕ` (a chain of pair projections of `x`), the bound
`∀ u, π x u ≤ B` is added to the context, with `B` read off the value (`ubLin`: sums, the
componentwise maximum of the branches of an `if` or a `match`, the bounds of the companions of
the locals bound before) and proved on the value by splitting its own case distinctions; later
companions are bounded from these facts, never from the inlined values.

At an arithmetic leaf, each summand that is an `if`, an `if h :` or a `match` is bounded on its
own (`addCaseFacts`, the same bound and proof), so that linear arithmetic closes the leaf with
these summands as atoms; the leaf is split on its case distinctions only when that fails.

A subtree that no rule consumes is bounded by a source: a local hypothesis whose conclusion
bounds it (`∀ x, (A x).time ≤ T`, `∀ x, (A x).TimeBound T`), or, below the definition named in
the goal or below a root of the goal's tree that is a constructor or a constant read as tree
structure (`structuralRoot`), the time theorems of the callees: the theorem `N.timeBound_timed`
(or `N.timeBound`) of a definition `N.timed` (or `N`), or the theorem `Ns.timeBound_f` of a
combinator `Ns.f` (`timeBound_simulate`, `timeBound_mapQuery`). A time theorem stated in
another namespace than its definition (`simImpl.timeBound` in namespace `FOTransform` for
`FOTransformU.simImpl.timed`) is found by resolving the trailing parts of the definition's name
in the current namespaces and the open declarations (`resolvedCompanions`). An adversary `y.2`
is bounded from a source of the step-prefixed tree `y` (`tb_snd_of_stb`), so that the premise
`A.TimeBound ?T` of a callee's time theorem (`liftP.timeBound_timed`) is closed from a
hypothesis `StepTimeBound X N` at `A = X.2`. The premises of a source are closed in this order:

* by a local hypothesis whose type unifies with the premise, or, for a cost bound
  `∀ x, c x ≤ ?t` whose bound is still free, by reflexivity when `c x` does not depend on `x`;
* a time premise `∀ x, StepTimeBound (g x) ?t` (or another kind) with a free bound, by a
  source of `g x` whose bound does not depend on `x`;
* a query bound `(N.timed …).2.erase.IsQueryBound ?q`, by the theorem `N.isQueryBound_erase`,
  found by name as the time theorems are (`queryBoundSource`); any other query bound
  `A.erase.IsQueryBound ?q` of a costed adversary, by
  `OracleAdv.Timed.isQueryBound_of_timeBound` from a time bound of `A`;
* any other premise, by the procedure.

An arithmetic leaf is reduced and extended before it is closed: its step costs `x.1` are
reduced (when `x` is a `delay` or its head definition unfolds to a pair) or bounded by a source
of `x`; projections of pairs, applied or not (`(a, b).2 x`), and beta redexes are reduced; a
recursor or `casesOn` on a constructor is reduced by iota, and a number-valued application of a
definition to a constructor is reduced to its numeral (`reduceCtorArg?`:
`Sum.elim (fun _ => 1) (fun _ => 0) (.inl q)` to `1`); and the bounded atoms are added: for
every subterm `f a` of the leaf and every local hypothesis `∀ x, f x ≤ b`, the instance
`f a ≤ b[a/x]`; for every subtype value `↑m`, its invariant `m.property`; for every registered
cost `f.timedCost a`, the instance of `f.timedCost_eq` or `f.timedCost_le` (premises by the
context). A summand `m₁` of the left side that is a `match` and a summand `m₂` of the right side
that is a `match` of the same matcher on the same discriminants are compared by cases
(`matchFacts`): the matcher proves `m₁ ≤ m₂` with the motive `fun ds => m₁[ds] ≤ m₂[ds]`, each
alternative comparing the alternatives of `m₁` and `m₂` at its pattern (`cmpLe`: reflexivity, a
nested `match` of the same discriminants, `add_le_add`, `max_le_max`, an `if` against the `if`
or the maximum of its branches, else `omega` with the bounded atoms), and `omega` is tried first
on the leaf with the compared matches replaced by variables bounded by these facts. The leaf is
then closed by `omega`. When `omega` fails, the case distinctions of the
leaf are split before `linarith` and `nlinarith` are tried, each case solved again: an
`if b = true` on a Boolean local `b` by cases on `b`; a recursor or `casesOn` on a local
variable or a pair projection of one (the answer cost `Sum.rec (fun _ => 0) (fun _ => 0) r`) by
cases on the variable (`recCases?`); an `if` or a `match` on its condition or scrutinee. A leaf
without case distinctions is closed by `omega`, then `linarith`, then `nlinarith`; when these
fail, a summand `t.time` of a tree that the rules consume (a second projection, a definition
with a visible body) is read with the rest of the leaf as its path (`arith_time`). A summand
`y.1` on the path is sought as it stands before the step costs of the path are reduced.

Every reduction to weak head normal form, unfolding and case split runs under its own
heartbeat budget (`stepHeartbeats`); a step that exceeds it is not taken, and the subtree is
treated as one that no rule consumes.

Definitions whose bodies are not visible from the calling module are unfolded by the lemmas
of the simp set `time_bound_simps` (an equation `R.timed … = …`), applied where unfolding
fails.

`time_bound` is registered with `catcrypt_auto` as the arm of the shape `time bound`, read
in the direct stage on goals whose head is `StepTimeBound` or `TimeBound`, or that are `≤`
over `ℕ` mentioning `SPTree.Timed.stepTime` or `SPTree.Timed.time`.

The tactic `allret_bound` proves leaf invariants `AllRet P t` of costed oracle adversaries:
the head of `t` is unfolded, a node is read by the definition of `AllRet`, an `if`, `match` or
recursor on a local variable is split, a bind `(A.bind f).2` takes a leaf invariant of `A` from
a source (`allRet_bind`), a tree with a source is closed through `allRet_mono`, and each leaf is
closed by `omega` with the instances of the hypotheses `∀ x, f x ≤ b` at its subterms. The
sources are local hypotheses, the theorem `N.allRet_le` of a costed definition `N.timed`, and
the theorem `allRet_f` of a combinator `f` (`allRet_mapQueryAnswer`), each resolved by name in
the current namespaces.

## Main definitions

* `time_bound` — the procedure
* `allret_bound` — the leaf invariants of costed oracle adversaries
* `time_bound_simps` — the simp set of unfolding equations
-/

public section

set_option autoImplicit false

/-- Unfolding equations of costed definitions whose bodies `time_bound` does not see. -/
register_simp_attr time_bound_simps

/-! ## Time bounds of costed binds under a leaf invariant -/

namespace CatCrypt.Core.SPTree.Timed

variable {α β γ : Type}

/-- A predicate that holds everywhere holds at every leaf. -/
theorem allRet_of_forall {Q : α → Prop} (h : ∀ a, Q a) (t : SPTree.Timed α) : AllRet Q t :=
  allRet_mono (Q := fun _ => True) (fun a _ => h a) t (by
    induction t with
    | ret a => exact trivial
    | sample γ finγ neγ c k ih => exact ih
    | get l c k ih => exact ih
    | set l v c t ih => exact ih
    | fail => exact trivial
    | load h₀ c t ih => exact ih)

/-- Two leaf invariants give their conjunction. -/
theorem allRet_and {Q R : α → Prop} {t : SPTree.Timed α} (hQ : AllRet Q t)
    (hR : AllRet R t) : AllRet (fun a => Q a ∧ R a) t := by
  induction t with
  | ret a => exact ⟨hQ, hR⟩
  | sample γ finγ neγ c k ih => exact fun b => ih b (hQ b) (hR b)
  | get l c k ih => exact fun v => ih v (hQ v) (hR v)
  | set l v c t ih => exact ih hQ hR
  | fail => exact trivial
  | load h₀ c t ih => exact ih hQ hR

/-- The leaves of a costed bind satisfy `Q` when, at every leaf `a` of the tree, the leaves of
the continuation at `a` do. -/
theorem allRet_bind_of {Q : β → Prop} {t : SPTree.Timed α} {f : α → ℕ × SPTree.Timed β}
    (h : AllRet (fun a => AllRet Q (f a).2) t) : AllRet Q (t.bind f).2 :=
  (allRet_bind Q t f).2 h

/-- The time of a costed bind is at most the time of the tree plus a bound `T` on the
continuation at the values satisfying a leaf invariant `Q` of the tree. -/
theorem stepTime_bind_le_of_allRet {Q : α → Prop} (A : SPTree.Timed α)
    (f : α → ℕ × SPTree.Timed β) (T : ℕ) (hA : AllRet Q A)
    (hf : ∀ a, Q a → stepTime (f a) ≤ T) : stepTime (A.bind f) ≤ A.time + T := by
  induction A with
  | ret a => simpa [bind, time_ret] using hf a hA
  | sample γ finγ neγ c k ih =>
    let _ := finγ
    simp only [stepTime, bind, time_sample, Nat.zero_add]
    have hs : (Finset.univ.sup fun b => c b + (bind (k b) f).1 + (bind (k b) f).2.time) ≤
        (Finset.univ.sup fun b => c b + (k b).time) + T :=
      Finset.sup_le fun b _ => by
        have h1 := ih b (hA b)
        have h2 : c b + (k b).time ≤ Finset.univ.sup fun b => c b + (k b).time :=
          Finset.le_sup (f := fun b => c b + (k b).time) (Finset.mem_univ b)
        simp only [stepTime] at h1
        omega
    omega
  | get l c k ih =>
    simp only [stepTime, bind, time_get, Nat.zero_add]
    have hs : (Finset.univ.sup fun v => c v + (bind (k v) f).1 + (bind (k v) f).2.time) ≤
        (Finset.univ.sup fun v => c v + (k v).time) + T :=
      Finset.sup_le fun v _ => by
        have h1 := ih v (hA v)
        have h2 : c v + (k v).time ≤ Finset.univ.sup fun v => c v + (k v).time :=
          Finset.le_sup (f := fun v => c v + (k v).time) (Finset.mem_univ v)
        simp only [stepTime] at h1
        omega
    omega
  | set l v c t ih =>
    have := ih hA
    simp only [stepTime, bind, time_set] at this ⊢
    omega
  | fail => simp [stepTime, bind, time_fail]
  | load h₀ c t ih =>
    have := ih hA
    simp only [stepTime, bind, time_load] at this ⊢
    omega

/-- A step cost `C` in front of a costed bind whose continuation is bounded at the values
satisfying a leaf invariant of the tree. -/
theorem prefix_bind_le_of_allRet {Q : α → Prop} (C : ℕ) (k : SPTree.Timed α)
    (f : α → ℕ × SPTree.Timed β) (B : ℕ) (hk : AllRet Q k)
    (h : ∀ s, Q s → stepTime (f s) ≤ B) :
    C + (k.bind f).1 + (k.bind f).2.time ≤ C + (k.time + B) := by
  have := stepTime_bind_le_of_allRet k f B hk h
  simp only [stepTime] at this
  omega

/-- A costed run from a reset heap of a prefix `P` followed by a continuation `k` bounded at the
values satisfying a leaf invariant of `P`, in the step-prefixed form of `derive_reduction`. -/
theorem stepTime_load_bind_le_of_allRet {Q : β → Prop} (h₀ : Heap) (c₁ c₂ : ℕ)
    (P : ℕ × SPTree.Timed β) (k : β → ℕ × SPTree.Timed γ) {B K : ℕ} (hP : stepTime P ≤ B)
    (hQ : AllRet Q P.2) (hk : ∀ x, Q x → stepTime (k x) ≤ K) :
    stepTime ((0 : ℕ), load h₀ (c₁ + (c₂ + P.1) + (P.2.bind k).1) (P.2.bind k).2) ≤
      h₀.data.keys.card + c₁ + c₂ + B + K + 1 := by
  have := stepTime_bind_le_of_allRet P.2 k K hQ hk
  simp only [stepTime, time_load] at hP this ⊢
  omega

end CatCrypt.Core.SPTree.Timed

namespace CatCrypt.Tactics.AutoTime

open CatCrypt.Core CatCrypt.Crypto

/-! ## Rules for costed computation trees -/

section SPTree

variable {α β : Type} {P B : ℕ}

theorem st_start {x : ℕ × SPTree.Timed α} (h : 0 + SPTree.Timed.stepTime x ≤ B) :
    SPTree.Timed.stepTime x ≤ B := by
  simpa using h

theorem time_start {t : SPTree.Timed α} (h : 0 + t.time ≤ B) : t.time ≤ B := by
  simpa using h

theorem st_pair {c : ℕ} {t : SPTree.Timed α} (h : P + c + t.time ≤ B) :
    P + SPTree.Timed.stepTime (c, t) ≤ B := by
  simp only [SPTree.Timed.stepTime]
  omega

/-- A pair `(e, y.2)` whose step cost `e` is `c + y.1`: the pair is `y` after `c`. -/
theorem st_pair_fst {e c : ℕ} {y : ℕ × SPTree.Timed α} (he : e = c + y.1)
    (h : P + c + SPTree.Timed.stepTime y ≤ B) : P + SPTree.Timed.stepTime (e, y.2) ≤ B := by
  subst he
  simp only [SPTree.Timed.stepTime] at h ⊢
  omega

theorem fst_le_of_stepTime {x : ℕ × SPTree.Timed α} {E : ℕ}
    (h : SPTree.Timed.stepTime x ≤ E) : x.1 ≤ E := by
  simp only [SPTree.Timed.stepTime] at h
  omega

theorem st_delay {c : ℕ} {x : ℕ × SPTree.Timed α} (h : P + c + SPTree.Timed.stepTime x ≤ B) :
    P + SPTree.Timed.stepTime (SPTree.Timed.delay c x) ≤ B := by
  rw [SPTree.Timed.stepTime_delay]
  omega

theorem st_map {f : α → β} {fc : α → ℕ} {A : SPTree.Timed α}
    (h : P + SPTree.Timed.stepTime (A.bind fun a => (fc a, .ret (f a))) ≤ B) :
    P + SPTree.Timed.stepTime (A.map f fc) ≤ B :=
  h

theorem st_ite {c : Prop} [Decidable c] {x y : ℕ × SPTree.Timed α}
    (hx : c → P + SPTree.Timed.stepTime x ≤ B) (hy : ¬c → P + SPTree.Timed.stepTime y ≤ B) :
    P + SPTree.Timed.stepTime (if c then x else y) ≤ B := by
  by_cases hc : c
  · simpa only [ite_eq_left hc] using hx hc
  · simpa only [ite_eq_right hc] using hy hc

theorem st_dite {c : Prop} [Decidable c] {x : c → ℕ × SPTree.Timed α}
    {y : ¬c → ℕ × SPTree.Timed α} (hx : ∀ h : c, P + SPTree.Timed.stepTime (x h) ≤ B)
    (hy : ∀ h : ¬c, P + SPTree.Timed.stepTime (y h) ≤ B) :
    P + SPTree.Timed.stepTime (if h : c then x h else y h) ≤ B := by
  by_cases hc : c
  · simpa only [dite_eq_left hc] using hx hc
  · simpa only [dite_eq_right hc] using hy hc

theorem st_bind_ret {a : α} {f : α → ℕ × SPTree.Timed β}
    (h : P + SPTree.Timed.stepTime (f a) ≤ B) :
    P + SPTree.Timed.stepTime ((SPTree.Timed.ret a).bind f) ≤ B := by
  simpa only [SPTree.Timed.bind] using h

theorem st_bind_sample {γ : Type} {fγ : Fintype γ} {nγ : Nonempty γ} {c : γ → ℕ}
    {k : γ → SPTree.Timed α} {f : α → ℕ × SPTree.Timed β}
    (h : ∀ b, P + 1 + c b + SPTree.Timed.stepTime ((k b).bind f) ≤ B) :
    P + SPTree.Timed.stepTime ((SPTree.Timed.sample γ fγ nγ c k).bind f) ≤ B := by
  let _ := fγ
  simp only [SPTree.Timed.bind, SPTree.Timed.stepTime, SPTree.Timed.time_sample, Nat.zero_add]
  have hs : (Finset.univ.sup fun b => c b + (SPTree.Timed.bind (k b) f).1 +
      (SPTree.Timed.bind (k b) f).2.time) ≤ B - P - 1 :=
    Finset.sup_le fun b _ => by
      have := h b
      simp only [SPTree.Timed.stepTime] at this
      omega
  have h0 := h (Classical.choice nγ)
  omega

theorem st_bind_get {l : Location} {c : l.ty → ℕ} {k : l.ty → SPTree.Timed α}
    {f : α → ℕ × SPTree.Timed β} (h0 : P + 1 ≤ B)
    (h : ∀ v, P + 1 + c v + SPTree.Timed.stepTime ((k v).bind f) ≤ B) :
    P + SPTree.Timed.stepTime ((SPTree.Timed.get l c k).bind f) ≤ B := by
  simp only [SPTree.Timed.bind, SPTree.Timed.stepTime, SPTree.Timed.time_get, Nat.zero_add]
  have hs : (Finset.univ.sup fun v => c v + (SPTree.Timed.bind (k v) f).1 +
      (SPTree.Timed.bind (k v) f).2.time) ≤ B - P - 1 :=
    Finset.sup_le fun v _ => by
      have := h v
      simp only [SPTree.Timed.stepTime] at this
      omega
  omega

theorem st_bind_set {l : Location} {v : l.ty} {c : ℕ} {t : SPTree.Timed α}
    {f : α → ℕ × SPTree.Timed β} (h : P + 1 + c + SPTree.Timed.stepTime (t.bind f) ≤ B) :
    P + SPTree.Timed.stepTime ((SPTree.Timed.set l v c t).bind f) ≤ B := by
  simp only [SPTree.Timed.bind, SPTree.Timed.stepTime, SPTree.Timed.time_set] at h ⊢
  omega

theorem st_bind_fail {f : α → ℕ × SPTree.Timed β} (h : P ≤ B) :
    P + SPTree.Timed.stepTime ((SPTree.Timed.fail : SPTree.Timed α).bind f) ≤ B := by
  simp only [SPTree.Timed.bind, SPTree.Timed.stepTime, SPTree.Timed.time_fail]
  omega

/-- A bind after a tree `A` that is not a node: the time of `A` joins the path. -/
theorem st_bind {A : SPTree.Timed α} {f : α → ℕ × SPTree.Timed β} (h0 : P + A.time ≤ B)
    (h : ∀ a, P + A.time + SPTree.Timed.stepTime (f a) ≤ B) :
    P + SPTree.Timed.stepTime (A.bind f) ≤ B := by
  have := SPTree.Timed.stepTime_bind_le A f (B - P - A.time) fun a => by
    have := h a
    omega
  omega

theorem st_of {x : ℕ × SPTree.Timed α} {T : ℕ} (h : SPTree.Timed.stepTime x ≤ T)
    (h0 : P + T ≤ B) : P + SPTree.Timed.stepTime x ≤ B := by
  omega

theorem time_ret {a : α} (h : P ≤ B) : P + (SPTree.Timed.ret a).time ≤ B := by
  simp only [SPTree.Timed.time_ret]
  omega

theorem time_sample {γ : Type} {fγ : Fintype γ} {nγ : Nonempty γ} {c : γ → ℕ}
    {k : γ → SPTree.Timed α} (h : ∀ b, P + 1 + c b + (k b).time ≤ B) :
    P + (SPTree.Timed.sample γ fγ nγ c k).time ≤ B := by
  let _ := fγ
  rw [SPTree.Timed.time_sample]
  have hs : (Finset.univ.sup fun b => c b + (k b).time) ≤ B - P - 1 :=
    Finset.sup_le fun b _ => by
      have := h b
      omega
  have h0 := h (Classical.choice nγ)
  omega

theorem time_get {l : Location} {c : l.ty → ℕ} {k : l.ty → SPTree.Timed α} (h0 : P + 1 ≤ B)
    (h : ∀ v, P + 1 + c v + (k v).time ≤ B) : P + (SPTree.Timed.get l c k).time ≤ B := by
  rw [SPTree.Timed.time_get]
  have hs : (Finset.univ.sup fun v => c v + (k v).time) ≤ B - P - 1 :=
    Finset.sup_le fun v _ => by
      have := h v
      omega
  omega

theorem time_set {l : Location} {v : l.ty} {c : ℕ} {t : SPTree.Timed α}
    (h : P + 1 + c + t.time ≤ B) : P + (SPTree.Timed.set l v c t).time ≤ B := by
  rw [SPTree.Timed.time_set]
  omega

theorem time_fail (h : P ≤ B) : P + (SPTree.Timed.fail : SPTree.Timed α).time ≤ B := by
  rw [SPTree.Timed.time_fail]
  omega

/-- The tree `y.2` on a path whose cost `P` has the summand `y.1`: the two are `stepTime y`. -/
theorem time_snd_fst {Q : ℕ} {y : ℕ × SPTree.Timed α} (he : P = Q + y.1)
    (h : Q + SPTree.Timed.stepTime y ≤ B) : P + y.2.time ≤ B := by
  subst he
  simp only [SPTree.Timed.stepTime] at h
  omega

/-- The step cost of a costed bind `A.bind g` in front of a bind after its tree: the time of
the bind of `A` into the continuations `g s` followed by `k`. -/
theorem stepTime_fst_bind_bind {γ : Type} (A : SPTree.Timed γ) (g : γ → ℕ × SPTree.Timed α)
    (k : α → ℕ × SPTree.Timed β) :
    (A.bind g).1 + SPTree.Timed.stepTime ((A.bind g).2.bind k) =
      SPTree.Timed.stepTime (A.bind fun s => SPTree.Timed.delay (g s).1 ((g s).2.bind k)) := by
  induction A with
  | ret a => simp only [SPTree.Timed.bind, SPTree.Timed.stepTime, SPTree.Timed.delay]; omega
  | sample γ' finγ neγ c k' ih =>
    let _ := finγ
    simp only [SPTree.Timed.bind, SPTree.Timed.stepTime, SPTree.Timed.time_sample,
      Nat.zero_add]
    congr 2
    funext b
    have := ih b
    simp only [SPTree.Timed.stepTime] at this
    omega
  | get l c k' ih =>
    simp only [SPTree.Timed.bind, SPTree.Timed.stepTime, SPTree.Timed.time_get, Nat.zero_add]
    congr 2
    funext v
    have := ih v
    simp only [SPTree.Timed.stepTime] at this
    omega
  | set l v c t ih =>
    simp only [SPTree.Timed.bind, SPTree.Timed.stepTime, SPTree.Timed.time_set] at ih ⊢
    omega
  | fail => simp only [SPTree.Timed.bind, SPTree.Timed.stepTime, SPTree.Timed.time_fail]
  | load h₀ c t ih =>
    simp only [SPTree.Timed.bind, SPTree.Timed.stepTime, SPTree.Timed.time_load] at ih ⊢
    omega

/-- A bind after the tree `y.2` of a costed bind `y = A.bind g` on a path whose cost `P` has the
summand `y.1`: the two are the bind of `A` into the continuations `g s` followed by `k`. -/
theorem st_snd_bind_fst {γ : Type} {Q : ℕ} {A : SPTree.Timed γ} {g : γ → ℕ × SPTree.Timed α}
    {k : α → ℕ × SPTree.Timed β} (he : P = Q + (A.bind g).1)
    (h : Q + SPTree.Timed.stepTime
      (A.bind fun s => SPTree.Timed.delay (g s).1 ((g s).2.bind k)) ≤ B) :
    P + SPTree.Timed.stepTime ((A.bind g).2.bind k) ≤ B := by
  subst he
  rw [← stepTime_fst_bind_bind] at h
  omega

theorem time_snd {x : ℕ × SPTree.Timed α} (h : P + SPTree.Timed.stepTime x ≤ B) :
    P + x.2.time ≤ B := by
  simp only [SPTree.Timed.stepTime] at h
  omega

theorem time_ite {c : Prop} [Decidable c] {x y : SPTree.Timed α}
    (hx : c → P + x.time ≤ B) (hy : ¬c → P + y.time ≤ B) :
    P + (if c then x else y).time ≤ B := by
  by_cases hc : c
  · simpa only [ite_eq_left hc] using hx hc
  · simpa only [ite_eq_right hc] using hy hc

theorem time_dite {c : Prop} [Decidable c] {x : c → SPTree.Timed α} {y : ¬c → SPTree.Timed α}
    (hx : ∀ h : c, P + (x h).time ≤ B) (hy : ∀ h : ¬c, P + (y h).time ≤ B) :
    P + (if h : c then x h else y h).time ≤ B := by
  by_cases hc : c
  · simpa only [dite_eq_left hc] using hx hc
  · simpa only [dite_eq_right hc] using hy hc

theorem time_of {t : SPTree.Timed α} {T : ℕ} (h : t.time ≤ T) (h0 : P + T ≤ B) :
    P + t.time ≤ B := by
  omega

theorem time_load {h₀ : Heap} {c : ℕ} {t : SPTree.Timed α}
    (h : P + 1 + h₀.data.keys.card + c + t.time ≤ B) :
    P + (SPTree.Timed.load h₀ c t).time ≤ B := by
  rw [SPTree.Timed.time_load]
  omega

/-- An arithmetic leaf read as a path `Q` followed by the time `T` of a tree. -/
theorem arith_time (l Q T B : ℕ) (he : l = Q + T) (h : Q + T ≤ B) : l ≤ B := by
  omega

/-- A bind after a tree `A` that is not a node, with a leaf invariant `Q` of `A`: the
continuation is bounded at the values satisfying `Q`. -/
theorem st_bind_inv {Q : α → Prop} {A : SPTree.Timed α} {f : α → ℕ × SPTree.Timed β}
    (hA : SPTree.Timed.AllRet Q A) (h0 : P + A.time ≤ B)
    (h : ∀ a, Q a → P + A.time + SPTree.Timed.stepTime (f a) ≤ B) :
    P + SPTree.Timed.stepTime (A.bind f) ≤ B := by
  have := SPTree.Timed.stepTime_bind_le_of_allRet A f (B - P - A.time) hA fun a ha => by
    have := h a ha
    omega
  omega

/-! ### Rules for leaf invariants -/

theorem ar_ret {Q : α → Prop} {a : α} (h : Q a) : SPTree.Timed.AllRet Q (.ret a) := h

theorem ar_sample {Q : α → Prop} {γ : Type} {fγ : Fintype γ} {nγ : Nonempty γ} {c : γ → ℕ}
    {k : γ → SPTree.Timed α} (h : ∀ b, SPTree.Timed.AllRet Q (k b)) :
    SPTree.Timed.AllRet Q (.sample γ fγ nγ c k) := h

theorem ar_get {Q : α → Prop} {l : Location} {c : l.ty → ℕ} {k : l.ty → SPTree.Timed α}
    (h : ∀ v, SPTree.Timed.AllRet Q (k v)) : SPTree.Timed.AllRet Q (.get l c k) := h

theorem ar_set {Q : α → Prop} {l : Location} {v : l.ty} {c : ℕ} {t : SPTree.Timed α}
    (h : SPTree.Timed.AllRet Q t) : SPTree.Timed.AllRet Q (.set l v c t) := h

theorem ar_load {Q : α → Prop} {h₀ : Heap} {c : ℕ} {t : SPTree.Timed α}
    (h : SPTree.Timed.AllRet Q t) : SPTree.Timed.AllRet Q (.load h₀ c t) := h

theorem ar_fail {Q : α → Prop} : SPTree.Timed.AllRet Q (.fail : SPTree.Timed α) := trivial

theorem ar_ite {Q : α → Prop} {c : Prop} [Decidable c] {x y : SPTree.Timed α}
    (hx : c → SPTree.Timed.AllRet Q x) (hy : ¬c → SPTree.Timed.AllRet Q y) :
    SPTree.Timed.AllRet Q (if c then x else y) := by
  by_cases hc : c
  · simpa only [ite_eq_left hc] using hx hc
  · simpa only [ite_eq_right hc] using hy hc

theorem ar_dite {Q : α → Prop} {c : Prop} [Decidable c] {x : c → SPTree.Timed α}
    {y : ¬c → SPTree.Timed α} (hx : ∀ h : c, SPTree.Timed.AllRet Q (x h))
    (hy : ∀ h : ¬c, SPTree.Timed.AllRet Q (y h)) :
    SPTree.Timed.AllRet Q (if h : c then x h else y h) := by
  by_cases hc : c
  · simpa only [dite_eq_left hc] using hx hc
  · simpa only [dite_eq_right hc] using hy hc

theorem ar_bind {Q : β → Prop} {A : SPTree.Timed α} {f : α → ℕ × SPTree.Timed β}
    (h : SPTree.Timed.AllRet (fun a => SPTree.Timed.AllRet Q (f a).2) A) :
    SPTree.Timed.AllRet Q (A.bind f).2 :=
  SPTree.Timed.allRet_bind_of h

/-- A tree whose leaves are not visible: the invariant at every value. -/
theorem ar_any {Q : α → Prop} {t : SPTree.Timed α} (h : ∀ a, Q a) : SPTree.Timed.AllRet Q t :=
  SPTree.Timed.allRet_of_forall h t

end SPTree

/-! ## Rules for costed oracle adversaries -/

section Oracle

variable {D R α β : Type} {P B : ℕ}

theorem tb_start {A : OracleAdv.Timed D R α} {n : ℕ} (h : A.TimeBound (n - 0)) :
    A.TimeBound n := by
  simpa using h

theorem stb_start {x : ℕ × OracleAdv.Timed D R α} {n : ℕ}
    (h : OracleAdv.Timed.StepTimeBound x (n - 0)) : OracleAdv.Timed.StepTimeBound x n := by
  simpa using h

theorem tb_ret {a : α} {n : ℕ} : (OracleAdv.Timed.ret a : OracleAdv.Timed D R α).TimeBound n :=
  trivial

theorem tb_rand {γ : Type} {p : PMF γ} {c : γ → ℕ} {k : γ → OracleAdv.Timed D R α}
    (h0 : P + 1 ≤ B) (h1 : ∀ b, P + 1 + c b ≤ B)
    (h2 : ∀ b, (k b).TimeBound (B - (P + 1 + c b))) :
    (OracleAdv.Timed.rand p c k).TimeBound (B - P) := by
  refine ⟨by omega, fun b => ⟨by have := h1 b; omega, ?_⟩⟩
  have e : B - P - 1 - c b = B - (P + 1 + c b) := by omega
  rw [e]
  exact h2 b

theorem tb_query {d : D} {c : R → ℕ} {k : R → OracleAdv.Timed D R α}
    (h0 : P + 1 ≤ B) (h1 : ∀ r, P + 1 + c r ≤ B)
    (h2 : ∀ r, (k r).TimeBound (B - (P + 1 + c r))) :
    (OracleAdv.Timed.query d c k).TimeBound (B - P) := by
  refine ⟨by omega, fun r => ⟨by have := h1 r; omega, ?_⟩⟩
  have e : B - P - 1 - c r = B - (P + 1 + c r) := by omega
  rw [e]
  exact h2 r

theorem tb_ite {c : Prop} [Decidable c] {x y : OracleAdv.Timed D R α}
    (hx : c → x.TimeBound (B - P)) (hy : ¬c → y.TimeBound (B - P)) :
    (if c then x else y).TimeBound (B - P) := by
  by_cases hc : c
  · simpa only [ite_eq_left hc] using hx hc
  · simpa only [ite_eq_right hc] using hy hc

theorem tb_dite {c : Prop} [Decidable c] {x : c → OracleAdv.Timed D R α}
    {y : ¬c → OracleAdv.Timed D R α} (hx : ∀ h : c, (x h).TimeBound (B - P))
    (hy : ∀ h : ¬c, (y h).TimeBound (B - P)) :
    (if h : c then x h else y h).TimeBound (B - P) := by
  by_cases hc : c
  · simpa only [dite_eq_left hc] using hx hc
  · simpa only [dite_eq_right hc] using hy hc

theorem tb_of {A : OracleAdv.Timed D R α} {T : ℕ} (h : A.TimeBound T) (h0 : P + T ≤ B) :
    A.TimeBound (B - P) :=
  h.mono (by omega)

theorem tb_snd {x : ℕ × OracleAdv.Timed D R α} (h : OracleAdv.Timed.StepTimeBound x (B - P)) :
    x.2.TimeBound (B - P) :=
  h.2.mono (Nat.sub_le _ _)

/-- The adversary of a step-prefixed tree of time `T` has time `T` less the step cost. -/
theorem tb_snd_of_stb {x : ℕ × OracleAdv.Timed D R α} {T : ℕ}
    (h : OracleAdv.Timed.StepTimeBound x T) : x.2.TimeBound (T - x.1) :=
  h.2

theorem stb_pair {c : ℕ} {A : OracleAdv.Timed D R α} (h0 : P + c ≤ B)
    (h : A.TimeBound (B - (P + c))) : OracleAdv.Timed.StepTimeBound (c, A) (B - P) := by
  refine ⟨by dsimp only; omega, ?_⟩
  have e : B - P - c = B - (P + c) := by omega
  simpa only [e] using h

/-- A pair `(e, y.2)` whose step cost `e` is `c + y.1`: the pair is `y` after `c`. -/
theorem stb_pair_fst {e c : ℕ} {y : ℕ × OracleAdv.Timed D R α} (he : e = c + y.1)
    (h0 : P + c ≤ B) (h : OracleAdv.Timed.StepTimeBound y (B - (P + c))) :
    OracleAdv.Timed.StepTimeBound (e, y.2) (B - P) := by
  subst he
  obtain ⟨h1, h2⟩ := h
  refine ⟨by dsimp only; omega, ?_⟩
  have e' : B - P - (c + y.1) = B - (P + c) - y.1 := by omega
  dsimp only
  rw [e']
  exact h2

theorem fst_le_of_stb {x : ℕ × OracleAdv.Timed D R α} {E : ℕ}
    (h : OracleAdv.Timed.StepTimeBound x E) : x.1 ≤ E :=
  h.1

theorem stb_delay {c : ℕ} {x : ℕ × OracleAdv.Timed D R α} (h0 : P + c ≤ B)
    (h : OracleAdv.Timed.StepTimeBound x (B - (P + c))) :
    OracleAdv.Timed.StepTimeBound (OracleAdv.Timed.delay c x) (B - P) :=
  (OracleAdv.Timed.stepTimeBound_delay h).mono (by omega)

theorem stb_ite {c : Prop} [Decidable c] {x y : ℕ × OracleAdv.Timed D R α}
    (hx : c → OracleAdv.Timed.StepTimeBound x (B - P))
    (hy : ¬c → OracleAdv.Timed.StepTimeBound y (B - P)) :
    OracleAdv.Timed.StepTimeBound (if c then x else y) (B - P) := by
  by_cases hc : c
  · simpa only [ite_eq_left hc] using hx hc
  · simpa only [ite_eq_right hc] using hy hc

theorem stb_dite {c : Prop} [Decidable c] {x : c → ℕ × OracleAdv.Timed D R α}
    {y : ¬c → ℕ × OracleAdv.Timed D R α}
    (hx : ∀ h : c, OracleAdv.Timed.StepTimeBound (x h) (B - P))
    (hy : ∀ h : ¬c, OracleAdv.Timed.StepTimeBound (y h) (B - P)) :
    OracleAdv.Timed.StepTimeBound (if h : c then x h else y h) (B - P) := by
  by_cases hc : c
  · simpa only [dite_eq_left hc] using hx hc
  · simpa only [dite_eq_right hc] using hy hc

theorem stb_bind_ret {a : α} {f : α → ℕ × OracleAdv.Timed D R β}
    (h : OracleAdv.Timed.StepTimeBound (f a) (B - P)) :
    OracleAdv.Timed.StepTimeBound ((OracleAdv.Timed.ret a).bind f) (B - P) := by
  simpa only [OracleAdv.Timed.bind] using h

theorem stb_bind_rand {γ : Type} {p : PMF γ} {c : γ → ℕ} {k : γ → OracleAdv.Timed D R α}
    {f : α → ℕ × OracleAdv.Timed D R β} (h0 : P + 1 ≤ B) (h1 : ∀ b, P + 1 + c b ≤ B)
    (h2 : ∀ b, OracleAdv.Timed.StepTimeBound ((k b).bind f) (B - (P + 1 + c b))) :
    OracleAdv.Timed.StepTimeBound ((OracleAdv.Timed.rand p c k).bind f) (B - P) := by
  simp only [OracleAdv.Timed.bind, OracleAdv.Timed.stepTimeBound_zero]
  refine ⟨by omega, fun b => ⟨?_, ?_⟩⟩ <;> dsimp only
  · have := h1 b
    have := (h2 b).1
    omega
  · have := h1 b
    have := (h2 b).1
    have e : B - P - 1 - (c b + ((k b).bind f).1) = B - (P + 1 + c b) - ((k b).bind f).1 := by
      omega
    rw [e]
    exact (h2 b).2

theorem stb_bind_query {d : D} {c : R → ℕ} {k : R → OracleAdv.Timed D R α}
    {f : α → ℕ × OracleAdv.Timed D R β} (h0 : P + 1 ≤ B) (h1 : ∀ r, P + 1 + c r ≤ B)
    (h2 : ∀ r, OracleAdv.Timed.StepTimeBound ((k r).bind f) (B - (P + 1 + c r))) :
    OracleAdv.Timed.StepTimeBound ((OracleAdv.Timed.query d c k).bind f) (B - P) := by
  simp only [OracleAdv.Timed.bind, OracleAdv.Timed.stepTimeBound_zero]
  refine ⟨by omega, fun r => ⟨?_, ?_⟩⟩ <;> dsimp only
  · have := h1 r
    have := (h2 r).1
    omega
  · have := h1 r
    have := (h2 r).1
    have e : B - P - 1 - (c r + ((k r).bind f).1) = B - (P + 1 + c r) - ((k r).bind f).1 := by
      omega
    rw [e]
    exact (h2 r).2

/-- A bind after an adversary `A` of time `T` that is not a node: `T` joins the path. -/
theorem stb_bind {A : OracleAdv.Timed D R α} {f : α → ℕ × OracleAdv.Timed D R β} {T : ℕ}
    (hA : A.TimeBound T) (h0 : P + T ≤ B)
    (hf : ∀ a, OracleAdv.Timed.StepTimeBound (f a) (B - (P + T))) :
    OracleAdv.Timed.StepTimeBound (A.bind f) (B - P) :=
  (OracleAdv.Timed.timeBound_bind hA hf).mono (by omega)

theorem stb_of {x : ℕ × OracleAdv.Timed D R α} {T : ℕ}
    (h : OracleAdv.Timed.StepTimeBound x T) (h0 : P + T ≤ B) :
    OracleAdv.Timed.StepTimeBound x (B - P) :=
  h.mono (by omega)

end Oracle

/-- An `if` is at most the `if` on the same condition of larger branches. -/
theorem ite_le_ite_of {c : Prop} [Decidable c] {a b a' b' : ℕ} (h₁ : a ≤ a') (h₂ : b ≤ b') :
    (if c then a else b) ≤ (if c then a' else b') := by
  split <;> assumption

/-- An `if` is at most the maximum of larger branches. -/
theorem ite_le_max_of {c : Prop} [Decidable c] {a b a' b' : ℕ} (h₁ : a ≤ a') (h₂ : b ≤ b') :
    (if c then a else b) ≤ max a' b' := by
  split <;> omega

/-! ## The procedure -/

meta section

open Lean Meta Elab Tactic

/-- The forms of a time goal, by the subterm that carries the tree. -/
inductive Kind where
  /-- `P + SPTree.Timed.stepTime x ≤ B` -/
  | step
  /-- `P + t.time ≤ B` -/
  | time
  /-- `A.TimeBound (B - P)` -/
  | tb
  /-- `StepTimeBound x (B - P)` -/
  | stb

/-- The rule that closes a goal of kind `k` from a bound of its tree. -/
def Kind.ofRule : Kind → Name
  | .step => ``st_of
  | .time => ``time_of
  | .tb => ``tb_of
  | .stb => ``stb_of

/-- The left side of an inequality `l ≤ r` over `ℕ`. -/
def natLe? (e : Expr) : Option (Expr × Expr) :=
  if e.isAppOfArity ``LE.le 4 && (e.getArg! 0).isConstOf ``Nat then
    some (e.getArg! 2, e.getArg! 3)
  else none

/-- The tree of a bound of kind `k`: `y` in `stepTime y ≤ E`, `y.time ≤ E`, `y.TimeBound E`,
`StepTimeBound y E`. -/
def Kind.treeOf (k : Kind) (e : Expr) : Option Expr :=
  match k with
  | .step => do
    let (l, _) ← natLe? e
    guard (l.isAppOfArity ``SPTree.Timed.stepTime 2)
    return l.appArg!
  | .time => do
    let (l, _) ← natLe? e
    guard (l.isAppOfArity ``SPTree.Timed.time 2)
    return l.appArg!
  | .tb => if e.isAppOfArity ``OracleAdv.Timed.TimeBound 5 then some (e.getArg! 3) else none
  | .stb =>
    if e.isAppOfArity ``OracleAdv.Timed.StepTimeBound 5 then some (e.getArg! 3) else none

/-- Constants read as tree structure, never unfolded. -/
def structural : List Name :=
  [``Prod.mk, ``Prod.fst, ``Prod.snd, ``ite, ``dite, ``SPTree.Timed.bind,
    ``SPTree.Timed.map, ``SPTree.Timed.delay, ``SPTree.Timed.stepTime, ``SPTree.Timed.time,
    ``OracleAdv.Timed.bind, ``OracleAdv.Timed.delay, ``OracleAdv.Timed.TimeBound,
    ``OracleAdv.Timed.StepTimeBound]

/-- Whether the body of the definition `n` is visible and not recursive. -/
def unfoldableDef (n : Name) : MetaM Bool := do
  let env ← getEnv
  if structural.contains n then return false
  if env.contains (n ++ `_sunfold) then return false
  let some (.defnInfo d) := env.find? n | return false
  let rec_ := d.value.find? fun
    | .const m _ => m == ``WellFounded.fix || m.lastComponentAsString == "brecOn"
    | _ => false
  return rec_.isNone

/-- Whether the head of the tree `x` is a constructor or a constant read as tree structure:
the subtrees of such a root are below the root, where the time theorems of the environment
are sources. -/
def structuralRoot (x : Expr) : MetaM Bool := do
  let some n := x.getAppFn.constName? | return false
  if structural.contains n then return true
  return (← getEnv).find? n matches some (.ctorInfo _)

/-- The heartbeat budget, in thousands, of one reduction or case split of the procedure. -/
def stepHeartbeats : Nat := 50000

/-- `x` under its own budget of `stepHeartbeats` heartbeats (at most the enclosing budget);
`none`, with the state restored, when it fails or exceeds the budget. An interrupt is passed
on. -/
def capped {α : Type} (x : MetaM α) : MetaM (Option α) := do
  let s ← saveState
  let cap (c : Core.Context) : Core.Context :=
    let m := if c.maxHeartbeats == 0 then stepHeartbeats * 1000
      else min c.maxHeartbeats (stepHeartbeats * 1000)
    { c with maxHeartbeats := m }
  tryCatchRuntimeEx
    (withCurrHeartbeats <| withTheReader Core.Context cap (some <$> x))
    fun e => do
      if e.isInterrupt then throw e
      s.restore
      return none

/-- `whnfR e` under the budget of `capped`; `e` itself when the budget is exceeded. -/
def whnfC (e : Expr) : MetaM Expr := do
  return (← capped (whnfR e)).getD e

/-- `e` with every `let` and `have` binder replaced by its value (zeta-normal form). -/
def zetaAll (e : Expr) : CoreM Expr :=
  Core.transform e (pre := fun e => match e with
    | .letE _ _ v b _ => return .visit (b.instantiate1 v)
    | _ => return .continue)

/-- The tree `e` with its head definition unfolded, then reduced by `whnfR`, under the budget
of `capped`. Its inner `let` and `have` binders are kept; `liftLets` binds them in the
context. -/
def unfoldTree? (e : Expr) : MetaM (Option Expr) := do
  let some n := e.getAppFn.constName? | return none
  unless ← unfoldableDef n do return none
  let r ← capped do
    let some e' ← withDefault (unfoldDefinition? e) | return none
    return some (← whnfR e'.headBeta)
  return r.join

/-- The major premise of an application of a recursor or `casesOn`. -/
def recMajorArg? (e : Expr) : MetaM (Option Expr) := do
  let some n := e.getAppFn.constName? | return none
  let some info := (← getEnv).find? n | return none
  let idx? ← match info with
    | .recInfo r => pure (some r.getMajorIdx)
    | _ =>
      if isCasesOnRecursor (← getEnv) n then
        let ind ← getConstInfoInduct n.getPrefix
        pure (some (ind.numParams + 1 + ind.numIndices))
      else pure none
  let some i := idx? | return none
  return e.getAppArgs[i]?

/-- The local variable that an application of a recursor or `casesOn` analyses, when it is
one. -/
def recMajor? (e : Expr) : MetaM (Option FVarId) := do
  let some a ← recMajorArg? e | return none
  return if a.isFVar then some a.fvarId! else none

/-- The target of `g` with the subterm `x` replaced by the definitionally equal `x'`. -/
def replaceIn (g : MVarId) (x x' : Expr) : MetaM MVarId := do
  if x == x' then return g
  let t ← instantiateMVars (← g.getType)
  g.replaceTargetDefEq (t.replace fun e => if e == x then some x' else none)

/-- Apply the rule lemma `n` to `g`: its conclusion is unified with the target at reducible
transparency, each term of `hints` is assigned to the first unassigned argument whose type it
has, and the unassigned premises are returned. `none` when the rule does not apply. -/
def applyRule (g : MVarId) (n : Name) (hints : List Expr := []) :
    MetaM (Option (List MVarId)) := g.withContext do
  let s ← saveState
  let e ← mkConstWithFreshMVarLevels n
  let (ms, _, concl) ← forallMetaTelescopeReducing (← inferType e)
  unless ← withReducible (isDefEq concl (← g.getType)) do
    s.restore
    return none
  for pf in hints do
    let pty ← inferType pf
    let mut done := false
    for m in ms do
      if done then break
      if ← m.mvarId!.isAssigned then continue
      if ← isDefEq (← inferType m) pty then
        m.mvarId!.assign pf
        done := true
    unless done do
      s.restore
      return none
  let mut gs := []
  for m in ms do
    let m := m.mvarId!
    unless ← m.isAssigned do
      unless ← isProp (← m.getType) do
        s.restore
        return none
      gs := gs ++ [m]
  g.assign (mkAppN e ms)
  return some gs

/-- The applications in `e` without loose bound variables. -/
partial def appsOf (e : Expr) (acc : Array Expr) : Array Expr :=
  match e with
  | .app f a =>
    let acc := if e.hasLooseBVars then acc else acc.push e
    appsOf a (appsOf f acc)
  | .mdata _ b => appsOf b acc
  | .lam _ t b _ => appsOf b (appsOf t acc)
  | .forallE _ t b _ => appsOf b (appsOf t acc)
  | .proj _ _ b =>
    let acc := if e.hasLooseBVars then acc else acc.push e
    appsOf b acc
  | _ => acc

/-- The pair `y` of a first projection `y.1`, as an application of `Prod.fst` or as a
primitive projection. -/
def fstOf? (e : Expr) : Option Expr :=
  if e.isAppOfArity ``Prod.fst 3 then some e.appArg!
  else match e with
    | .proj ``Prod 0 y => some y
    | _ => none

/-- The pair `y` of a second projection `y.2`, as an application of `Prod.snd` or as a
primitive projection. -/
def sndOf? (e : Expr) : Option Expr :=
  if e.isAppOfArity ``Prod.snd 3 then some e.appArg!
  else match e with
    | .proj ``Prod 1 y => some y
    | _ => none

/-- The first projection `o` with its pair replaced by `y`. -/
def withFstArg (o y : Expr) : Expr :=
  match o with
  | .proj n i _ => .proj n i y
  | _ => mkApp3 o.getAppFn (o.getArg! 0) (o.getArg! 1) y

/-- Bounded atoms: for every subterm `f a` of the target and every local hypothesis
`∀ x, f x ≤ b` without propositional premises, the instance `f a ≤ b[a/x]` is added to the
context. -/
def addBoundedAtoms (g : MVarId) : MetaM MVarId := g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  let subs := appsOf tgt #[]
  let mut g := g
  let mut added : Array Expr := #[]
  for ld in (← getLCtx) do
    if ld.isImplementationDetail then continue
    let ty ← instantiateMVars ld.type
    unless ty.isForall do continue
    let s0 ← saveState
    let (ms0, _, body0) ← forallMetaTelescopeReducing ty
    let some (pat, _) := natLe? body0 | s0.restore; continue
    let hd := pat.getAppFn
    let nargs := pat.getAppNumArgs
    let hasProp ← ms0.anyM fun m => do isProp (← inferType m)
    s0.restore
    if hasProp || !(hd.isConst || hd.isFVar || hd.isProj) then continue
    for s in subs do
      unless s.getAppNumArgs == nargs && s.getAppFn == hd do continue
      let s1 ← saveState
      let (ms, _, body) ← forallMetaTelescopeReducing ty
      let some (l, _) := natLe? body | s1.restore; continue
      if ← isDefEq l s then
        let pf ← instantiateMVars (mkAppN ld.toExpr ms)
        if pf.hasExprMVar then
          s1.restore
          continue
        let pty ← instantiateMVars (← inferType pf)
        s1.restore
        if added.contains pty then continue
        added := added.push pty
        let (_, g') ← (← g.assert `hb pty pf).intro1P
        g := g'
      else
        s1.restore
  return g

/-- The invariant `m.property` of every subterm `↑m` of the target, added to the context. -/
def addSubtypeFacts (g : MVarId) : MetaM MVarId := g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  let mut g := g
  let mut seen : Array Expr := #[]
  for s in appsOf tgt #[] do
    unless s.isAppOfArity ``Subtype.val 3 do continue
    let m := s.appArg!
    if seen.contains m then continue
    seen := seen.push m
    let pf ← mkAppM ``Subtype.property #[m]
    let pty ← instantiateMVars (← inferType pf)
    let (_, g') ← (← g.assert `hs pty.headBeta pf).intro1P
    g := g'
  return g

/-- Close an arithmetic leaf by `omega`, then (unless `omegaOnly`) `linarith`, then
`nlinarith`, after adding the bounded atoms and the invariants of subtype values. -/
def closeArithCore (g : MVarId) (omegaOnly : Bool := false) : TacticM Unit := do
  let g ← addBoundedAtoms g
  let g ← addSubtypeFacts g
  let om ← `(tactic| omega)
  let li ← `(tactic| linarith)
  let nl ← `(tactic| nlinarith)
  let tacs := if omegaOnly then #[om] else #[om, li, nl]
  for tac in tacs do
    let s ← saveState
    try
      setGoals [g]
      evalTactic tac
      if (← getUnsolvedGoals).isEmpty then return
    catch _ => pure ()
    s.restore
  throwError "time_bound: arithmetic leaf not closed{indentExpr (← g.getType)}"

/-- The constants `s.t` for the tags `t` and the trailing parts `s` of the name `p` (its last
component, its last two, and so on), each resolved in the current namespaces and the open
declarations: the companion theorems of a definition `p` stated in another namespace than
`p`, as `simImpl.timeBound` in namespace `FOTransform` of `FOTransformU.simImpl.timed`. -/
def resolvedCompanions (p : Name) (tags : List Name) : CoreM (List Name) := do
  let comps := p.components
  let mut out : List Name := []
  for i in [0:comps.length] do
    let s := (comps.drop (comps.length - 1 - i)).foldl (· ++ ·) Name.anonymous
    for t in tags do
      for (c, fields) in ← resolveGlobalName (s ++ t) do
        if fields.isEmpty && (← getEnv).contains c && !out.contains c then
          out := out ++ [c]
  return out

/-- The theorems `N.timeBound_timed`, `N.timeBound` of the definition `N.timed` at the head
of `x`, `M.timeBound` of a head `M`, and `Ns.timeBound_f` of a combinator `Ns.f`
(`OracleAdv.Timed.timeBound_simulate` of `OracleAdv.Timed.simulate`). -/
def envSources (x : Expr) : MetaM (Array Expr) := do
  let x ← zetaReduce x
  let some n := x.getAppFn.constName? | return #[]
  let last := n.lastComponentAsString
  let cands :=
    (if last == "timed" then
      [n.getPrefix ++ `timeBound_timed, n.getPrefix ++ `timeBound] else []) ++
      [n ++ `timeBound, Name.str n.getPrefix ("timeBound_" ++ last)]
  let env ← getEnv
  let mut out := cands.filter env.contains
  if last == "timed" then
    for c in ← resolvedCompanions n.getPrefix [`timeBound_timed, `timeBound] do
      unless out.contains c do out := out ++ [c]
  out.toArray.mapM mkConstWithFreshMVarLevels

/-- Close the proposition `mid` from the context: a local hypothesis whose type unifies with
it, or, for `∀ x, l ≤ ?r` with `?r` unassigned and independent of `x`, reflexivity. -/
def closeByContext (mid : MVarId) : MetaM Bool := mid.withContext do
  let ty ← instantiateMVars (← mid.getType)
  for ld in (← getLCtx) do
    if ld.isImplementationDetail then continue
    let s ← saveState
    if ← isDefEq ty ld.type then
      mid.assign ld.toExpr
      return true
    s.restore
  let s ← saveState
  let ok ← forallTelescopeReducing ty fun xs body => do
    let some (l, r) := natLe? body | return false
    unless (← instantiateMVars r).getAppFn.isMVar do return false
    unless ← isDefEq r l do return false
    mid.assign (← mkLambdaFVars xs (← mkAppM ``Nat.le_refl #[l]))
    return true
  unless ok do s.restore
  return ok

/-- A proof of the query bound `body` (`A.erase.IsQueryBound ?q`) of the adversary `A = y.2`
of a costed definition `y = N.timed …` by the theorem `N.isQueryBound_erase`, found by name as
the time theorems of `envSources` are, with its propositional premises closed by the
context. -/
def queryBoundSource (body A : Expr) : MetaM (Option Expr) := do
  let some y := sndOf? A | return none
  let y ← zetaReduce y
  let some n := y.getAppFn.constName? | return none
  unless n.lastComponentAsString == "timed" do return none
  let exact := n.getPrefix ++ `isQueryBound_erase
  let mut names := if (← getEnv).contains exact then [exact] else []
  for c in ← resolvedCompanions n.getPrefix [`isQueryBound_erase] do
    unless names.contains c do names := names ++ [c]
  for c in names do
    let s ← saveState
    let e ← mkConstWithFreshMVarLevels c
    let (ms, _, concl) ← forallMetaTelescopeReducing (← inferType e)
    if ← isDefEq concl body then
      let mut ok := true
      for m in ms do
        let mid := m.mvarId!
        if ← mid.isAssigned then continue
        unless ← isProp (← mid.getType) do continue
        unless ← closeByContext mid do
          ok := false
          break
      let pf ← instantiateMVars (mkAppN e ms)
      if ok && !pf.hasExprMVar then return some pf
    s.restore
  return none

/-- The lemmas `f.timedCost_eq`, `f.timedCost_le` of the registered cost `f.timedCost`. -/
def costLemmas (n : Name) : MetaM (Array Expr) := do
  match n with
  | .str p s =>
    let env ← getEnv
    [Name.str p (s ++ "_eq"), Name.str p (s ++ "_le")].filter env.contains
      |>.toArray.mapM mkConstWithFreshMVarLevels
  | _ => return #[]

/-- Registered costs: for every subterm `f.timedCost a` of the target, the instance at `a` of
`f.timedCost_eq` (an equation) or `f.timedCost_le` (a bound), with its premises closed by
`closeByContext`, is added to the context. -/
def addCostFacts (g : MVarId) : MetaM MVarId := g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  let mut g := g
  let mut added : Array Expr := #[]
  for s in appsOf tgt #[] do
    let some n := s.getAppFn.constName? | continue
    unless n.lastComponentAsString == "timedCost" do continue
    for c in ← costLemmas n do
      let st ← saveState
      let (ms, _, body) ← forallMetaTelescopeReducing (← inferType c)
      let lhs? := if body.isAppOfArity ``Eq 3 then some (body.getArg! 1)
        else (natLe? body).map (·.1)
      let some l := lhs? | st.restore; continue
      unless ← isDefEq l s do
        st.restore
        continue
      let mut ok := true
      for m in ms do
        let mid := m.mvarId!
        if ← mid.isAssigned then continue
        unless ← isProp (← mid.getType) do continue
        unless ← closeByContext mid do
          ok := false
          break
      let pf ← instantiateMVars (mkAppN c ms)
      if !ok || pf.hasExprMVar then
        st.restore
        continue
      let pty ← instantiateMVars (← inferType pf)
      if added.contains pty then continue
      added := added.push pty
      let (_, g') ← (← g.assert `hc pty pf).intro1P
      g := g'
  return g

/-- The step cost `x.1` of a pair `x` whose head definition unfolds to a pair, replaced by the
first component of that pair, in the target. -/
def reduceStepCosts (g : MVarId) : MetaM MVarId := g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  let tgt' ← Meta.transform tgt (post := fun e => do
    let some y := fstOf? e | return .continue
    let mut x ← whnfC y
    for _ in [0:8] do
      if x.isAppOfArity ``Prod.mk 4 then break
      if x.isAppOf ``SPTree.Timed.delay || x.isAppOf ``OracleAdv.Timed.delay then
        match ← withDefault (unfoldDefinition? x) with
        | some x' => x ← whnfC x'.headBeta
        | none => break
      else
        match ← unfoldTree? x with
        | some x' => x := x'
        | none => break
    if x.isAppOfArity ``Prod.mk 4 then return .visit (x.getArg! 2)
    return .continue)
  if tgt' == tgt then return g
  g.replaceTargetDefEq tgt'

/-- The component `i` of the pair `y` when `y` is syntactically a pair. -/
def pairComponent? (y : Expr) (i : Nat) : Option Expr :=
  if y.isAppOfArity ``Prod.mk 4 then some (y.getArg! (2 + i)) else none

/-- A projection of a pair, applied to arguments: `(a, b).1 xs` is `a xs`, `(a, b).2 xs` is
`b xs`, beta-reduced. -/
def reduceProjApp? (e : Expr) : Option Expr :=
  let fn := e.getAppFn
  let args := e.getAppArgs
  match fn with
  | .proj ``Prod i y => (pairComponent? y i).map fun c => (mkAppN c args).headBeta
  | .const n _ =>
    if (n == ``Prod.fst || n == ``Prod.snd) && args.size ≥ 3 then
      let i := if n == ``Prod.fst then 0 else 1
      (pairComponent? args[2]! i).map fun c => (mkAppN c args[3:]).headBeta
    else none
  | _ => none

/-- Case analysis on a local variable, not a `let` variable, that a recursor or `casesOn` in
`x` analyses; `none` when there is none. -/
def recCases? (g : MVarId) (x : Expr) : MetaM (Option (List MVarId)) := g.withContext do
  for s in appsOf x #[] do
    let some a ← recMajorArg? s | continue
    -- a major premise `p.1` (a chain of pair projections of `p`): case analysis on `p`
    let mut r := a
    for _ in [0:16] do
      match fstOf? r <|> sndOf? r with
      | some y => r := y
      | none => break
    unless r.isFVar do continue
    let fv := r.fvarId!
    if ← fv.isLetVar then continue
    let some subgoals ← capped (g.cases fv) | continue
    return some (subgoals.toList.map (·.mvarId))
  return none

/-- An application with a constructor argument, reduced: a recursor or `casesOn` on a
constructor by iota reduction, and a number-valued application of a definition to its value
when that is a numeral (`Sum.elim (fun _ => 1) (fun _ => 0) (.inl q)` to `1`). -/
def reduceCtorArg? (e : Expr) : MetaM (Option Expr) := do
  let some n := e.getAppFn.constName? | return none
  if structural.contains n || e.hasLooseBVars then return none
  let env ← getEnv
  let isCtor (a : Expr) : Bool :=
    (a.getAppFn.constName?.bind env.find?) matches some (.ctorInfo _)
  if let some a ← recMajorArg? e then
    unless isCtor a do return none
    let r ← whnfC e
    return if r == e then none else some r
  unless e.getAppArgs.any isCtor do return none
  if env.find? n matches some (.ctorInfo _) then return none
  let some ty ← capped (inferType e) | return none
  unless ty.isConstOf ``Nat do return none
  -- one unfolding of the head, then reducible reduction (iota and matchers)
  let some (some r) ← capped (do
    let some e' ← withDefault (unfoldDefinition? e) | return none
    return some (← whnfR e'.headBeta)) | return none
  match r.nat? with
  | some k => return some (mkNatLit k)
  | none => match r.rawNatLit? with
    | some k => return some (mkNatLit k)
    | none => return none

/-- The target with projections of pairs (applied or not) and beta redexes reduced. -/
def reduceProjBeta (g : MVarId) : MetaM MVarId := g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  let tgt' ← Meta.transform tgt (post := fun e => do
    if e.isHeadBetaTarget then return .visit e.headBeta
    if let some e' := reduceProjApp? e then return .visit e'
    if let some e' ← reduceCtorArg? e then return .visit e'
    return .continue)
  if tgt' == tgt then return g
  g.replaceTargetDefEq tgt'

/-- The tree `(delay c x).2` read as `x.2`, repeatedly. -/
def sndThroughDelay (e : Expr) : MetaM Expr := do
  let mut e := e
  for _ in [0:8] do
    let some y := sndOf? e | return e
    unless y.isAppOfArity ``SPTree.Timed.delay 3 do return e
    e ← whnfC (← mkAppM ``Prod.snd #[y.appArg!])
  return e

/-- The root of a chain of pair projections. -/
partial def projRoot (e : Expr) : Expr :=
  match fstOf? e with
  | some y => projRoot y
  | none => match sndOf? e with
    | some y => projRoot y
    | none => e

/-- Case analysis on a Boolean local `b` that an `if b = true` of `x` tests, each case
simplified by `↓reduceIte`; `none` when there is no such local. -/
def boolCases? (g : MVarId) (x : Expr) : TacticM (Option (List MVarId)) := g.withContext do
  let cand := (appsOf x #[]).findSome? fun e =>
    if e.isAppOfArity ``ite 5 || e.isAppOfArity ``dite 5 then
      let c := e.getArg! 1
      if c.isAppOfArity ``Eq 3 && (c.getArg! 1).isFVar then some (c.getArg! 1) else none
    else none
  let some b := cand | return none
  unless (← whnfR (← inferType b)).isConstOf ``Bool do return none
  let s ← saveState
  let some subs ← capped (g.cases b.fvarId!) | return none
  let mut out : List MVarId := []
  for sg in subs do
    setGoals [sg.mvarId]
    try
      evalTactic (← `(tactic| simp only [Bool.false_eq_true, ↓reduceIte, ↓reduceDIte]))
    catch _ => pure ()
    out := out ++ (← getGoals)
  if out.isEmpty && subs.isEmpty then
    s.restore
    return none
  return some out

/-- A leaf of an invariant: projections of pairs reduced, binders introduced, then `omega`
with the bounded atoms of the context, else a case analysis on a Boolean local, an `if` or a
`match`. -/
partial def invLeaf (g : MVarId) (fuel : Nat) : TacticM Unit := g.withContext do
  if fuel == 0 then throwError "time_bound: depth bound reached"
  let g ← reduceProjBeta g
  let tgt ← instantiateMVars (← g.getType)
  if tgt.isForall then
    let (_, g') ← g.intro1P
    invLeaf g' (fuel - 1)
    return
  if tgt.isAppOfArity ``And 2 then
    let some gs ← applyRule g ``And.intro | throwError "time_bound: no conjunction"
    for g' in gs do invLeaf g' (fuel - 1)
    return
  let s ← saveState
  try
    let g1 ← addBoundedAtoms g
    setGoals [g1]
    evalTactic (← `(tactic| omega))
    unless (← getUnsolvedGoals).isEmpty do throwError "time_bound: invariant leaf not closed"
  catch e =>
    s.restore
    if let some gs ← boolCases? g tgt then
      for g' in gs do invLeaf g' (fuel - 1)
      return
    let some (some gs) ← capped (splitTarget? g) | throw e
    for g' in gs do invLeaf g' (fuel - 1)

/-! ### Let-bound values -/

/-- A linear bound over `ℕ`: a constant and atoms with their coefficients. -/
abbrev LinB := Nat × Array (Expr × Nat)

/-- The bound `a` with `k` times the atom `x` added. -/
def LinB.addAtom (a : LinB) (x : Expr) (k : Nat) : LinB :=
  match a.2.findIdx? (·.1 == x) with
  | some i => (a.1, a.2.modify i fun (y, j) => (y, j + k))
  | none => (a.1, a.2.push (x, k))

/-- The sum of two bounds. -/
def LinB.add (a b : LinB) : LinB :=
  b.2.foldl (fun acc (x, k) => acc.addAtom x k) (a.1 + b.1, a.2)

/-- The bound `a` multiplied by `k`. -/
def LinB.scale (k : Nat) (a : LinB) : LinB :=
  (k * a.1, a.2.map fun (x, j) => (x, k * j))

/-- The componentwise maximum of two bounds, a bound of both over `ℕ`. -/
def LinB.max (a b : LinB) : LinB :=
  b.2.foldl (fun acc (x, k) => match acc.2.findIdx? (·.1 == x) with
    | some i => (acc.1, acc.2.modify i fun (y, j) => (y, Nat.max j k))
    | none => (acc.1, acc.2.push (x, k))) (Nat.max a.1 b.1, a.2)

/-- The term `c + k₁ * x₁ + …` of a bound. -/
def LinB.toExpr (a : LinB) : MetaM Expr :=
  a.2.foldlM (init := mkNatLit a.1) fun acc (x, k) => do
    let t ← if k == 1 then pure x else mkAppM ``HMul.hMul #[mkNatLit k, x]
    mkAppM ``HAdd.hAdd #[acc, t]

/-- The natural number of a numeral. -/
def natNum? (e : Expr) : Option Nat :=
  match e.rawNatLit? with
  | some n => some n
  | none => e.nat?

/-- The linear form of a bound term: numerals, sums and products by numerals are read, every
other subterm is an atom. -/
partial def linOf (e : Expr) : LinB :=
  if let some n := natNum? e then (n, #[])
  else if e.isAppOfArity ``HAdd.hAdd 6 then (linOf (e.getArg! 4)).add (linOf (e.getArg! 5))
  else if e.isAppOfArity ``HMul.hMul 6 then
    match natNum? (e.getArg! 4) with
    | some k => (linOf (e.getArg! 5)).scale k
    | none => (0, #[(e, 1)])
  else (0, #[(e, 1)])

/-- The alternatives of a chain of pair projections applied to arguments: a projection of a
pair is reduced, a projection of an `if` is taken in each branch. -/
partial def projAlts (e : Expr) (fuel : Nat) : Array Expr := Id.run do
  if fuel == 0 then return #[e]
  let fn := e.getAppFn
  let args := e.getAppArgs
  let dec : Option (Nat × Expr × Array Expr × (Expr → Expr)) := match fn with
    | .proj ``Prod i y => some (i, y, args, fun y' => mkAppN (.proj ``Prod i y') args)
    | .const n _ =>
      if (n == ``Prod.fst || n == ``Prod.snd) && args.size ≥ 3 then
        let rest := args.extract 3 args.size
        some (if n == ``Prod.fst then 0 else 1, args[2]!, rest,
          fun y' => mkAppN (mkAppN fn (args.extract 0 2)) (#[y'] ++ rest))
      else none
    | _ => none
  let some (i, y, rest, rebuild) := dec | return #[e]
  let mut out := #[]
  for y' in projAlts y (fuel - 1) do
    let y' := y'.headBeta
    if y'.isAppOfArity ``Prod.mk 4 then
      out := out ++ projAlts (mkAppN (y'.getArg! (2 + i)) rest).headBeta (fuel - 1)
    else if y'.isAppOfArity ``ite 5 then
      out := out ++ projAlts (rebuild (y'.getArg! 3)) (fuel - 1) ++
        projAlts (rebuild (y'.getArg! 4)) (fuel - 1)
    else out := out.push (rebuild y')
  return out

/-- The bound `b[a/x]` of a local hypothesis `∀ x, l ≤ b` whose left side unifies with `e` at
reducible transparency. -/
def hypBound? (e : Expr) : MetaM (Option Expr) := do
  for ld in (← getLCtx) do
    if ld.isImplementationDetail then continue
    let ty ← instantiateMVars ld.type
    let s ← saveState
    let (ms, _, body) ← forallMetaTelescopeReducing ty
    let some (l, b) := natLe? body | s.restore; continue
    if ← ms.anyM fun m => do isProp (← inferType m) then s.restore; continue
    if ← withReducible (isDefEq l e) then
      let b ← instantiateMVars b
      s.restore
      unless b.hasExprMVar do return some b
    else s.restore
  return none

/-- A proposed linear bound of the natural number `e`: sums, products by numerals, `if`
(the componentwise maximum of the branches), projections of pairs and of `if`s, and the
bounds of local hypotheses `∀ x, l ≤ b` at the atoms. -/
partial def ubLin (e : Expr) (fuel : Nat) : MetaM (Option LinB) := do
  if fuel == 0 then return none
  let e := e.headBeta
  if let some n := natNum? e then return some (n, #[])
  if e.isAppOfArity ``HAdd.hAdd 6 then
    let some a ← ubLin (e.getArg! 4) (fuel - 1) | return none
    let some b ← ubLin (e.getArg! 5) (fuel - 1) | return none
    return some (a.add b)
  if e.isAppOfArity ``HMul.hMul 6 then
    if let some k := natNum? (e.getArg! 4) then
      return (← ubLin (e.getArg! 5) (fuel - 1)).map (·.scale k)
  -- an `if a = a` is its first branch
  if (e.isAppOfArity ``ite 5 || e.isAppOfArity ``dite 5) then
    let c := e.getArg! 1
    if c.isAppOfArity ``Eq 3 && c.getArg! 1 == c.getArg! 2 then
      let mut br := e.getArg! 3
      if e.isAppOfArity ``dite 5 then
        let u ← getLevel (c.getArg! 0)
        br := mkApp br (mkApp2 (mkConst ``Eq.refl [u]) (c.getArg! 0) (c.getArg! 1))
      return ← ubLin br (fuel - 1)
  if e.isAppOfArity ``ite 5 then
    let some a ← ubLin (e.getArg! 3) (fuel - 1) | return none
    let some b ← ubLin (e.getArg! 4) (fuel - 1) | return none
    return some (a.max b)
  -- `dite` and `match`: the maximum over the alternatives, whose bounds do not depend on the
  -- fields of the alternative
  let alts? ← if e.isAppOfArity ``dite 5 then pure (some #[e.getArg! 3, e.getArg! 4])
    else pure ((← matchMatcherApp? e).map (·.alts))
  if let some alts := alts? then
    let mut acc : Option LinB := none
    for alt in alts do
      let r ← lambdaTelescope alt fun xs b => do
        let some l ← ubLin b (fuel - 1) | return none
        if l.2.any fun (a, _) => xs.any fun x => a.containsFVar x.fvarId! then return none
        return some l
      let some l := r | return none
      acc := some (match acc with | some m => m.max l | none => l)
    return acc
  let alts := projAlts e 16
  unless alts.size == 1 && alts[0]! == e do
    let mut acc : Option LinB := none
    for a in alts do
      let some l ← ubLin a (fuel - 1) | return none
      acc := some (match acc with | some m => m.max l | none => l)
    return acc
  if let some b ← hypBound? e then return some (linOf b)
  if e.isFVar && (← whnfR (← inferType e)).isConstOf ``Nat then return some (0, #[(e, 1)])
  return none

/-- The cost companions of a value `e` of type `ty`: the chains of pair projections of `e`
whose type is `ℕ` (with `none`) or `X → ℕ` (with `some X`). -/
partial def compPaths (e ty : Expr) (d : Nat) : MetaM (Array (Expr × Option Expr)) := do
  if d == 0 then return #[]
  let ty ← whnfR ty
  if ty.isAppOfArity ``Prod 2 then
    let a ← compPaths (← mkAppM ``Prod.fst #[e]) (ty.getArg! 0) (d - 1)
    let b ← compPaths (← mkAppM ``Prod.snd #[e]) (ty.getArg! 1) (d - 1)
    return a ++ b
  if ty.isConstOf ``Nat then return #[(e, none)]
  if let .forallE _ X cod _ := ty then
    if !cod.hasLooseBVars && (← whnfR cod).isConstOf ``Nat then return #[(e, some X)]
  return #[]

/-- The statement `∀ u, p u ≤ B` (with `some X`, `u : X`) or `p ≤ B` (with `none`) for the
companion `p` of a let-bound local whose value form is `pv`, with the bound `B` proposed by
`ubLin` on `pv u`, independent of `u`. -/
def companionBound? (p pv : Expr) (X? : Option Expr) : MetaM (Option Expr) := do
  match X? with
  | some X => withLocalDeclD `u X fun u => do
    let some lin ← ubLin (mkApp pv u) 64 | return none
    if lin.2.any (·.1.containsFVar u.fvarId!) then return none
    let b ← lin.toExpr
    return some (← mkForallFVars #[u] (← mkAppM ``LE.le #[mkApp p u, b]))
  | none =>
    let some lin ← ubLin pv 64 | return none
    return some (← mkAppM ``LE.le #[p, ← lin.toExpr])

/-- Bounds of the cost companions of the let-bound local `x := v`, added to the context: for
each companion `π x` (`compPaths`), the statement of `companionBound?` on `π v`, proved by
`invLeaf` on `π v u`, with the bounds of the locals bound before `x` in the context. A
companion whose bound is not found or not proved gets no fact. -/
def addLetFacts (g : MVarId) (x : FVarId) : TacticM MVarId := g.withContext do
  let some v ← x.getValue? | return g
  let xe := mkFVar x
  let paths ← compPaths xe (← x.getType) 8
  let mut g := g
  for (p, X?) in paths do
    let g0 := g
    let r : Option MVarId ← g0.withContext do
      let some stmt ← companionBound? p (p.replaceFVar xe v) X? | return none
      let s ← saveState
      let m ← mkFreshExprMVar stmt
      try
        let g1 ← m.mvarId!.replaceTargetDefEq (stmt.replaceFVar xe v)
        invLeaf g1 32
        let pf ← instantiateMVars m
        let (_, g') ← (← g0.assert `hf stmt pf).intro1P
        return some g'
      catch _ =>
        s.restore
        return none
    if let some g' := r then g := g'
  return g

/-- Whether a `let` of type `t` is inlined rather than bound: costed trees and step-prefixed
trees (read structurally by the rules), natural numbers (read by `omega`) and proofs. -/
def inlineType (t : Expr) : MetaM Bool := do
  if (t.find? fun e => e.isConstOf ``SPTree.Timed || e.isConstOf ``OracleAdv.Timed).isSome then
    return true
  if (← whnfR t).isConstOf ``Nat then return true
  isProp t

/-- Whether a let-bound value is an atom, inlined rather than bound. -/
def atomicVal (v : Expr) : Bool :=
  v.isFVar || v.isConst || v.isLit || v.isSort || (natNum? v).isSome

/-- The number of nodes of `e`, at most `cap`. -/
partial def sizeCapped (e : Expr) (cap : Nat) : Nat :=
  if cap == 0 then 0 else
  match e with
  | .app f a => let n := sizeCapped f (cap - 1); n + 1 + sizeCapped a (cap - 1 - min n (cap - 1))
  | .lam _ t b _ | .forallE _ t b _ =>
    let n := sizeCapped t (cap - 1); n + 1 + sizeCapped b (cap - 1 - min n (cap - 1))
  | .letE _ t v b _ => sizeCapped t (cap - 1) + sizeCapped v (cap - 1) + sizeCapped b (cap - 1)
  | .mdata _ b => sizeCapped b cap
  | .proj _ _ b => 1 + sizeCapped b (cap - 1)
  | _ => 1

/-- The `let` and `have` nodes of `e` whose value and type have no loose bound variables. -/
def closedLets (e : Expr) : MetaM (Array Expr) := do
  let r ← IO.mkRef #[]
  e.forEach' fun s => do
    if let .letE _ t v _ _ := s then
      if !t.hasLooseBVars && !v.hasLooseBVars then r.modify (·.push s)
    return true
  r.get

/-- The goal `g` with the `let` and `have` binders of its target that do not depend on bound
variables taken out of the target: a binder of a tree, a number, a proof or an atom is inlined;
any other binder, the one with the smallest value first, becomes a let-bound local `x := v` of
the context, every binder of the same value and every occurrence of the value in the target are
replaced by `x`, and the bounds of the cost companions of `x` are added (`addLetFacts`). Each
value is thus read once, and the companions of later values are bounded from those of earlier
ones. -/
partial def liftLets (g : MVarId) (fuel : Nat := 64) : TacticM MVarId := g.withContext do
  if fuel == 0 then return g
  let tgt ← instantiateMVars (← g.getType)
  unless (tgt.find? Expr.isLet).isSome do return g
  let lets ← closedLets tgt
  if lets.isEmpty then return g
  let mut inl : Array Expr := #[]
  let mut best : Option (Expr × Nat) := none
  for l in lets do
    let .letE _ t v _ _ := l | continue
    if atomicVal v || (← inlineType t) then
      inl := inl.push l
    else
      let n := sizeCapped v 100000
      if best.all (n < ·.2) then best := some (l, n)
  if !inl.isEmpty then
    let tgt' ← Core.transform tgt (pre := fun e => match e with
      | .letE _ _ v b _ =>
        return if inl.contains e then .visit (b.instantiate1 v) else .continue
      | _ => return .continue)
    return ← liftLets (← g.replaceTargetDefEq tgt') (fuel - 1)
  let some (.letE n t v _ _, _) := best | return g
  let g1 ← g.define n t v
  let (x, g2) ← g1.intro1P
  let g4 ← g2.withContext do
    let xe := mkFVar x
    let tgt2 ← instantiateMVars (← g2.getType)
    let tgt3 ← Core.transform tgt2 (pre := fun e => do
      if let .letE _ _ v' b _ := e then
        if v' == v then return .visit (b.instantiate1 xe)
      if e == v then return .done xe
      return .continue)
    let g3 ← g2.replaceTargetDefEq tgt3
    addLetFacts g3 x
  liftLets g4 (fuel - 1)

/-- The summands of a sum, through products by numerals. -/
partial def linAtoms (e : Expr) (acc : Array Expr) : Array Expr :=
  if e.isAppOfArity ``HAdd.hAdd 6 then linAtoms (e.getArg! 5) (linAtoms (e.getArg! 4) acc)
  else if e.isAppOfArity ``HMul.hMul 6 && (natNum? (e.getArg! 4)).isSome then
    linAtoms (e.getArg! 5) acc
  else acc.push e

/-- Bounds of the case distinctions of an arithmetic leaf `l ≤ B`, added to the context: for
each summand `t` of `l` that is an `if`, an `if h :` or a `match`, the statement `t ≤ U` with
the bound `U` proposed by `ubLin` (the componentwise maximum of the bounds of the branches),
proved by `invLeaf` on `t ≤ U` alone. The leaf is then closed by linear arithmetic over these
summands as atoms, and its case distinctions are split one summand at a time, never all
together. -/
def addCaseFacts (g : MVarId) : TacticM MVarId := g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  let some (l, _) := natLe? tgt | return g
  let mut g := g
  let mut seen : Array Expr := #[]
  for t in linAtoms l #[] do
    unless t.isAppOfArity ``ite 5 || t.isAppOfArity ``dite 5 ||
      (← matchMatcherApp? t).isSome do continue
    if t.hasLooseBVars || t.hasExprMVar || seen.contains t then continue
    seen := seen.push t
    let some lin ← ubLin t 64 | continue
    let stmt ← mkAppM ``LE.le #[t, ← lin.toExpr]
    let s ← saveState
    let m ← mkFreshExprMVar stmt
    try
      invLeaf m.mvarId! 32
      let (_, g') ← (← g.assert `hi stmt (← instantiateMVars m)).intro1P
      g := g'
    catch _ => s.restore
  return g

/-- The summands of a sum. -/
partial def summands (e : Expr) (acc : Array Expr) : Array Expr :=
  if e.isAppOfArity ``HAdd.hAdd 6 then summands (e.getArg! 5) (summands (e.getArg! 4) acc)
  else acc.push e

/-- An arithmetic leaf `l ≤ B` with a summand `t.time` of a tree that the rules can consume
(a second projection or a definition with a visible body): the leaf read as the path `l`
without the summand followed by `t.time` (`arith_time`). -/
def timeAtom? (g : MVarId) : TacticM (Option MVarId) := g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  let some (l, b) := natLe? tgt | return none
  for s in summands l #[] do
    unless s.isAppOfArity ``SPTree.Timed.time 2 do continue
    let t := s.appArg!
    unless (sndOf? t).isSome || (← unfoldTree? t).isSome do continue
    let q := l.replace fun e => if e == s then some (mkNatLit 0) else none
    let st ← saveState
    try
      let gs ← g.apply (mkApp4 (mkConst ``arith_time) l q s b)
      let [he, h] := gs | throwError "time_bound: arith_time"
      setGoals [he]
      evalTactic (← `(tactic| omega))
      unless (← getUnsolvedGoals).isEmpty do throwError "time_bound: arith_time"
      return some h
    catch _ => st.restore
  return none

/-- The slack ladder of an inferred companion bound `e u ≤ c + N`. -/
def invSlack : List Nat := [0, 1, 2, 3, 4, 6, 8, 12, 16]

/-- Candidate leaf invariants of a bind `A.bind f` over values of type `α`: for every
companion `π a : X → ℕ` that the continuation `f a` reads (a chain of pair projections of the
bound value `a`) and every local hypothesis `∀ x : X, h x ≤ c`, the predicates
`fun a => ∀ u, π a u ≤ c + N` for `N` in `invSlack`, one list per companion and hypothesis. -/
def invCandidates (α f : Expr) : MetaM (Array (Array Expr)) := do
  withLocalDeclD `a α fun a => do
    let body ← zetaAll (← instantiateMVars (mkApp f a).headBeta)
    let mut paths : Array (Expr × Expr) := #[]
    for s in appsOf body #[] do
      unless (fstOf? s).isSome || (sndOf? s).isSome do continue
      unless projRoot s == a do continue
      if paths.any (·.1 == s) then continue
      let ty ← whnfR (← inferType s)
      let .forallE _ X cod _ := ty | continue
      if cod.hasLooseBVars then continue
      unless (← whnfR cod).isConstOf ``Nat do continue
      paths := paths.push (s, X)
    let mut out := #[]
    for (p, X) in paths do
      for ld in (← getLCtx) do
        if ld.isImplementationDetail || ld.fvarId == a.fvarId! then continue
        let ty ← instantiateMVars ld.type
        let .forallE _ X' b _ := ty | continue
        let some (l, r) := natLe? b | continue
        if r.hasLooseBVars then continue
        unless l.hasLooseBVars do continue
        -- a companion binder `h x`, or a companion `π h x` of a binder `h` that is not let-bound
        let root := if l.isApp then projRoot l.appFn! else l
        let rootOk ← if root.isFVar then do pure !(← root.fvarId!.isLetVar) else pure false
        unless l.getAppFn.isFVar || rootOk do continue
        unless ← isDefEq X X' do continue
        let mut ladder := #[]
        for n in invSlack do
          let q ← withLocalDeclD `u X fun u => do
            let bound ← mkAppM ``HAdd.hAdd #[r, mkNatLit n]
            mkForallFVars #[u] (← mkAppM ``LE.le #[(mkApp p u).headBeta, bound])
          ladder := ladder.push (← mkLambdaFVars #[a] q)
        out := out.push ladder
    return out

/-- The proposition `a ≤ b` over `ℕ`. -/
def mkNatLe (a b : Expr) : Expr :=
  mkApp4 (mkConst ``LE.le [Level.zero]) (mkConst ``Nat) (mkConst ``instLENat) a b

/-- Whether `m₁` and `m₂` are applications of the same matcher to the same discriminants,
without arguments after their alternatives. -/
def sameMatch (m₁ m₂ : MatcherApp) : MetaM Bool := do
  unless m₁.matcherName == m₂.matcherName && m₁.discrs.size == m₂.discrs.size &&
    m₁.remaining.isEmpty && m₂.remaining.isEmpty && m₁.uElimPos?.isSome do return false
  for d₁ in m₁.discrs, d₂ in m₂.discrs do
    unless d₁ == d₂ do
      unless ← withReducible (isDefEq d₁ d₂) do return false
  return true

/-- The application `e` of a matcher reduced by iota at its pattern, beta-reduced; `e` when
it does not reduce. -/
def reduceMatch (e : Expr) : MetaM Expr := do
  match ← reduceMatcher? e with
  | .reduced e' => return e'.headBeta
  | _ => return e

/-- `g : a ≤ b` reduced by `rule` (`Nat.add_le_add`, `max_le_max`, `ite_le_ite_of`,
`ite_le_max_of`) to the comparisons of its parts; `none` when the conclusion of the rule does
not match the target. -/
def splitLe (g : MVarId) (rule : Name) : MetaM (Option (MVarId × MVarId)) := do
  let s ← saveState
  match ← applyRule g rule with
  | some [g₁, g₂] => return some (g₁, g₂)
  | _ =>
    s.restore
    return none

mutual

/-- `a ≤ b` by the structure of the two costs: reflexivity; two matches of the same
discriminants by `matchLe`; two sums by `Nat.add_le_add`, two maxima by `max_le_max`, an `if`
against the `if` on the same condition or the maximum of two branches by `ite_le_ite_of` or
`ite_le_max_of`, each with its parts compared; else `omega` with the bounded atoms of the
context. -/
partial def cmpLe (g : MVarId) (fuel : Nat) : TacticM Unit := g.withContext do
  if fuel == 0 then throwError "time_bound: depth bound reached"
  let tgt ← zetaAll (← instantiateMVars (← g.getType))
  let some (a, b) := natLe? tgt | throwError "time_bound: not a comparison{indentExpr tgt}"
  let a := a.headBeta
  let b := b.headBeta
  let g ← g.replaceTargetDefEq (mkNatLe a b)
  if a == b then
    g.assign (mkApp (mkConst ``Nat.le_refl) a)
    return
  if let some m₁ ← matchMatcherApp? a then
    let m₂? ← match ← matchMatcherApp? b with
      | some m₂ => do pure (if ← sameMatch m₁ m₂ then some m₂ else none)
      | none => pure none
    -- the matches compared by cases, or the match of `a` against the bound `b` by cases
    let s ← saveState
    try
      matchLe g m₁ m₂? b (fuel - 1)
      return
    catch _ => s.restore
  let rule? : Option Name :=
    if a.isAppOfArity ``HAdd.hAdd 6 && b.isAppOfArity ``HAdd.hAdd 6 then some ``Nat.add_le_add
    else if a.isAppOfArity ``Max.max 4 && b.isAppOfArity ``Max.max 4 then some ``max_le_max
    else if a.isAppOfArity ``ite 5 && b.isAppOfArity ``ite 5 && a.getArg! 1 == b.getArg! 1 then
      some ``ite_le_ite_of
    else if a.isAppOfArity ``ite 5 && b.isAppOfArity ``Max.max 4 then some ``ite_le_max_of
    else none
  if let some rule := rule? then
    let s ← saveState
    try
      if let some (g₁, g₂) ← splitLe g rule then
        cmpLe g₁ (fuel - 1)
        cmpLe g₂ (fuel - 1)
        return
    catch _ => pure ()
    s.restore
  -- a cost against a maximum: against one of its arguments
  if b.isAppOfArity ``Max.max 4 then
    for rule in [``le_max_of_le_left, ``le_max_of_le_right] do
      let s ← saveState
      try
        if let some [g₁] ← applyRule g rule then
          cmpLe g₁ (fuel - 1)
          return
      catch _ => pure ()
      s.restore
  closeArithCore (← addCostFacts g) (omegaOnly := true)

/-- `m₁ ≤ b` by the matcher of `m₁`: with the motive `fun ds => m₁[ds] ≤ m₂[ds]` when `b` is
the match `m₂` of the same matcher on the same discriminants, else `fun ds => m₁[ds] ≤ b`; at
each alternative the two sides are reduced at the pattern and compared by `cmpLe`. -/
partial def matchLe (g : MVarId) (m₁ : MatcherApp) (m₂? : Option MatcherApp) (b : Expr)
    (fuel : Nat) : TacticM Unit := g.withContext do
  let some pos := m₁.uElimPos? | throwError "time_bound: match without a motive universe"
  let motive ← forallBoundedTelescope (← inferType m₁.motive) m₁.discrs.size fun xs _ => do
    let rhs := match m₂? with
      | some m₂ => { m₂ with discrs := xs }.toExpr
      | none => b
    mkLambdaFVars xs (mkNatLe { m₁ with discrs := xs }.toExpr rhs)
  let lvls := m₁.matcherLevels.set! pos Level.zero
  let f := mkAppN (mkConst m₁.matcherName lvls.toList) (m₁.params ++ #[motive] ++ m₁.discrs)
  let mut fty ← inferType f
  let mut alts : Array Expr := #[]
  for _ in m₁.altNumParams do
    let .forallE _ d b _ ← whnfD fty | throwError "time_bound: matcher type"
    let mv ← mkFreshExprSyntheticOpaqueMVar d
    alts := alts.push mv
    fty := b.instantiate1 mv
  let pf := mkAppN f alts
  unless ← isDefEq (← inferType pf) (← g.getType) do
    throwError "time_bound: matcher motive"
  g.assign pf
  for mv in alts, n in m₁.altNumParams do
    let (_, g') ← mv.mvarId!.introN n
    g'.withContext do
      let tgt := (← instantiateMVars (← g'.getType)).headBeta
      let some (a, b) := natLe? tgt | throwError "time_bound: alternative"
      cmpLe (← g'.replaceTargetDefEq (mkNatLe (← reduceMatch a) (← reduceMatch b))) fuel

end

/-- An arithmetic leaf `l ≤ r` with a summand `m₁` of `l` and a summand `m₂` of `r` that are
matches of the same discriminants, `m₁ ≤ m₂` proved by `cmpLe`: the leaf
`∀ x₁ y₁ …, x₁ ≤ y₁ → … → l[xᵢ/m₁ᵢ] ≤ r[yᵢ/m₂ᵢ]` with its binders introduced, which proves
`l ≤ r` from these facts. `none` when no pair is compared. -/
def matchFacts (g : MVarId) : TacticM (Option MVarId) := g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  let some (l, r) := natLe? tgt | return none
  let rs := linAtoms r #[]
  let mut pairs : Array (Expr × Expr × Expr) := #[]
  for t in linAtoms l #[] do
    if t.hasLooseBVars || t.hasExprMVar || pairs.any (·.1 == t) then continue
    let some m₁ ← matchMatcherApp? t | continue
    for u in rs do
      if u.hasLooseBVars || u.hasExprMVar then continue
      let some m₂ ← matchMatcherApp? u | continue
      unless ← sameMatch m₁ m₂ do continue
      let s ← saveState
      let mv ← mkFreshExprMVar (mkNatLe t u)
      try
        cmpLe mv.mvarId! 64
        pairs := pairs.push (t, u, ← instantiateMVars mv)
        break
      catch _ => s.restore
  if pairs.isEmpty then return none
  let n := pairs.size
  let decls := (Array.range (2 * n)).map fun i => (Name.mkSimple s!"m{i}", fun _ => pure (mkConst ``Nat))
  let stmt ← withLocalDeclsD decls fun xs => do
    let sub (side : Nat) (e : Expr) : Expr := e.replace fun e' =>
      match pairs.findIdx? fun p => (if side == 0 then p.1 else p.2.1) == e' with
      | some i => some xs[2 * i + side]!
      | none => none
    let mut body := mkNatLe (sub 0 l) (sub 1 r)
    for i in (List.range n).reverse do
      body := mkForall `h .default (mkNatLe xs[2 * i]! xs[2 * i + 1]!) body
    mkForallFVars xs body
  let G ← mkFreshExprSyntheticOpaqueMVar stmt
  let args := (pairs.foldl (fun acc p => acc.push p.1 |>.push p.2.1) #[]) ++ pairs.map (·.2.2)
  let pf := mkAppN G args
  unless ← isDefEq (← inferType pf) tgt do return none
  g.assign pf
  let (_, g') ← G.mvarId!.introN (3 * n)
  return some g'

mutual

/-- An arithmetic leaf: the step costs of pairs are reduced, each remaining step cost `x.1` of a
costed tree is bounded by a source of `x`, the matches of the same discriminants on its two
sides are compared by cases (`matchFacts`), and `closeArithCore` closes the goal. -/
partial def closeArith (g : MVarId) (env : Bool) (fuel : Nat) : TacticM Unit := do
  let s0 ← saveState
  let g0 := g
  let g ← liftLets (← reduceStepCosts (← reduceProjBeta g))
  let mut g := g
  let tgt ← g.withContext do instantiateMVars (← g.getType)
  let mut seen : Array Expr := #[]
  for s in appsOf tgt #[] do
    let some x := fstOf? s | continue
    if seen.contains x then continue
    seen := seen.push x
    let xty ← g.withContext do whnfR (← inferType x)
    let snd := if xty.isAppOfArity ``Prod 2 then xty.getArg! 1 else xty
    let kind? : Option (Kind × Name) :=
      if snd.isAppOf ``SPTree.Timed then some (.step, ``fst_le_of_stepTime)
      else if snd.isAppOf ``OracleAdv.Timed then some (.stb, ``fst_le_of_stb)
      else none
    let some (k, lem) := kind? | continue
    let g0 := g
    let r ← g0.withContext do
      match ← findSource k x env fuel with
      | some pf =>
        let fact ← mkAppM lem #[pf]
        let (_, g') ← (← g0.assert `hx (← inferType fact) fact).intro1P
        pure (some g')
      | none => pure none
    if let some g' := r then g := g'
  g ← addCostFacts g
  -- the matches of the same discriminants on the two sides, compared by cases
  let sm ← saveState
  if let some gm ← matchFacts g then
    try
      closeArithCore gm (omegaOnly := true)
      return
    catch _ => sm.restore
  let gc ← addCaseFacts g
  let s ← saveState
  try
    closeArithCore gc (omegaOnly := true)
  catch _ =>
    s.restore
    -- case distinctions of the leaf before `linarith` and `nlinarith`, whose failed searches
    -- on a leaf that a split closes are the expensive part of a leaf
    let tgtc ← gc.withContext do instantiateMVars (← gc.getType)
    -- an `if b = true` on a Boolean local: case analysis on `b`
    if let some gs ← boolCases? gc tgtc then
      for g' in gs do solve g' env (fuel - 1)
      return
    -- a recursor or `casesOn` on a local variable (a cost `Sum.rec (fun _ => 0) (fun _ => 0) r`
    -- of an answer `r`): case analysis on the variable, the cases reduced by iota
    if let some gs ← recCases? gc tgtc then
      for g' in gs do solve g' env (fuel - 1)
      return
    -- an `if` or `match` in the leaf: split on its condition or scrutinee
    if let some (some gs) ← capped (splitTarget? gc) then
      for g' in gs do solve g' env (fuel - 1)
      return
    let s2 ← saveState
    try
      closeArithCore gc
    catch e =>
      s2.restore
      -- the time of a tree that the rules consume, with the rest of the leaf as its path (on
      -- the leaf before its step costs are reduced, so that `fstSummand` finds them)
      s0.restore
      let some g' ← timeAtom? g0 | throw e
      solve g' env (fuel - 1)

/-- A premise of a source with metavariables in its type: by the context
(`closeByContext`); a time premise `∀ x, StepTimeBound (g x) ?t` (or another kind) by a
source of `g x` whose bound does not depend on `x`; a query bound `A.erase.IsQueryBound ?q`
of a costed adversary by `isQueryBound_of_timeBound` from a time bound of `A`. -/
partial def solvePremise (mid : MVarId) (env : Bool) (fuel : Nat) : TacticM Bool :=
    mid.withContext do
  if ← closeByContext mid then return true
  let ty ← instantiateMVars (← mid.getType)
  let s ← saveState
  let r ← forallTelescopeReducing ty fun xs body => do
    for k in [Kind.stb, .tb, .step, .time] do
      if let some x := k.treeOf body then
        if let some pf ← findSource k x env fuel then
          if ← isDefEq (← inferType pf) body then
            mid.assign (← mkLambdaFVars xs pf)
            return true
    if body.isAppOfArity ``OracleAdv.IsQueryBound 5 then
      let a := body.getArg! 3
      if a.isAppOfArity ``OracleAdv.Timed.erase 4 then
        if let some pf ← queryBoundSource body a.appArg! then
          mid.assign (← mkLambdaFVars xs pf)
          return true
        if let some pf ← findSource .tb a.appArg! env fuel then
          let q ← mkAppM ``OracleAdv.Timed.isQueryBound_of_timeBound #[pf]
          if ← isDefEq (← inferType q) body then
            mid.assign (← mkLambdaFVars xs q)
            return true
    return false
  unless r do s.restore
  return r

/-- A proof that the tree `x` of kind `k` is bounded, from a local hypothesis or (when `env`)
a theorem of `envSources`, with its premises closed by the context or by `solve`. -/
partial def findSource (k : Kind) (x : Expr) (env : Bool) (fuel : Nat) :
    TacticM (Option Expr) := do
  let locals ← (← getLCtx).getFVars.filterM fun f => do
    return !(← f.fvarId!.getDecl).isImplementationDetail
  let envs ← if env then envSources x else pure #[]
  let cands := locals ++ envs
  for c in cands do
    let s ← saveState
    try
      let cty ← instantiateMVars (← inferType c)
      let (ms, bis, body) ← forallMetaTelescopeReducing cty
      let some y := k.treeOf body | throwError "no"
      unless ← withReducible (isDefEq y x) do throwError "no"
      -- premises: the context first, then instances, then `solvePremise`, then the procedure
      for m in ms do
        let mid := m.mvarId!
        if ← mid.isAssigned then continue
        if ← isProp (← mid.getType) then
          discard <| closeByContext mid
      for m in ms, bi in bis do
        let mid := m.mvarId!
        if ← mid.isAssigned then continue
        if bi.isInstImplicit then
          mid.assign (← synthInstance (← mid.getType))
      for m in ms do
        let mid := m.mvarId!
        if ← mid.isAssigned then continue
        unless ← isProp (← mid.getType) do continue
        if ← solvePremise mid env (fuel - 1) then continue
        if (← instantiateMVars (← mid.getType)).hasExprMVar then continue
        solve mid env (fuel - 1)
      for m in ms do
        let mid := m.mvarId!
        if ← mid.isAssigned then continue
        unless ← isProp (← mid.getType) do throwError "no"
        if ← solvePremise mid env (fuel - 1) then continue
        if (← instantiateMVars (← mid.getType)).hasExprMVar then throwError "no"
        solve mid env (fuel - 1)
      let pf ← instantiateMVars (mkAppN c ms)
      if pf.hasExprMVar then throwError "no"
      return some pf
    catch _ =>
      s.restore
  -- the adversary `y.2` of a step-prefixed tree `y` bounded as a whole
  if let (.tb, some y) := (k, sndOf? x) then
    if let some pf ← findSource .stb y env fuel then
      return some (← mkAppM ``tb_snd_of_stb #[pf])
  return none

/-- A subtree that no structural rule consumes: a source, else the unfolding of its head
definition, else the simp set `time_bound_simps`, else (computation trees) an arithmetic
leaf. -/
partial def leaf (g : MVarId) (k : Kind) (x : Expr) (env : Bool) (fuel : Nat) :
    TacticM Unit := g.withContext do
  if let some pf ← findSource k x env fuel then
    if ← applyAndSolve g k.ofRule [pf] env fuel then return
  if let some x' ← unfoldTree? x then
    solve (← replaceIn g x x') true (fuel - 1)
    return
  let s ← saveState
  try
    setGoals [g]
    evalTactic (← `(tactic| simp only [time_bound_simps]))
    let gs ← getGoals
    for g' in gs do solve g' true (fuel - 1)
    return
  catch _ => s.restore
  match k with
  | .step | .time => closeArith g env fuel
  | _ => throwError "time_bound: no bound for the subtree{indentExpr x}"

/-- Apply the rule `n` and solve its premises. -/
partial def applyAndSolve (g : MVarId) (n : Name) (hints : List Expr) (env : Bool)
    (fuel : Nat) : TacticM Bool := do
  let some gs ← applyRule g n hints | return false
  for g' in gs do solve g' env (fuel - 1)
  return true

/-- Apply the rule `n`, failing when it does not apply. -/
partial def rule (g : MVarId) (n : Name) (env : Bool) (fuel : Nat) (hints : List Expr := []) :
    TacticM Unit := do
  unless ← applyAndSolve g n hints env fuel do
    throwError "time_bound: rule {n} does not apply to{indentExpr (← g.getType)}"

/-- Split a `match` at the head of the tree, or case on the local variable that a recursor or
`casesOn` at the head analyses, when there is one. -/
partial def splitMatch (g : MVarId) (x : Expr) (env : Bool) (fuel : Nat) : TacticM Bool := do
  if (← matchMatcherApp? x).isSome then
    let some (some gs) ← capped (splitTarget? g) | return false
    for g' in gs do solve g' env (fuel - 1)
    return true
  let some fv ← recMajor? x | return false
  let s ← saveState
  try
    let some subgoals ← capped (g.cases fv) | return false
    for sg in subgoals do solve sg.mvarId env (fuel - 1)
    return true
  catch _ =>
    s.restore
    return false

/-- A pair `(e, y.2)`: by `fstRule` when the step cost `e` has the summand `y.1` (with
`e = c + y.1` closed by `omega`), else by `plainRule`. -/
partial def pairRule (g : MVarId) (x : Expr) (plainRule fstRule : Name) (env : Bool)
    (fuel : Nat) : TacticM Unit := do
  let e := x.getArg! 2
  let snd0 := x.getArg! 3
  let snd ← if (sndOf? snd0).isSome then pure snd0 else whnfC snd0
  if let some y := sndOf? snd then
    let fsts := (appsOf e #[]).filter fun t => (fstOf? t).isSome
    for o in fsts do
      let s ← saveState
      if ← withReducible (isDefEq (fstOf? o).get! y) then
        let y1 := withFstArg o y
        let e' := e.replace fun t => if t == o then some y1 else none
        let c := e.replace fun t => if t == o then some (mkNatLit 0) else none
        let x' := mkApp4 x.getAppFn (x.getArg! 0) (x.getArg! 1) e' snd
        let g' ← replaceIn g x x'
        try
          if ← applyAndSolve g' fstRule [c] env fuel then return
        catch _ => pure ()
      s.restore
  rule g plainRule env fuel

/-- `P + stepTime x ≤ B`. -/
partial def stepCase (g : MVarId) (x : Expr) (env : Bool) (fuel : Nat) : TacticM Unit := do
  let x' ← whnfC x
  let g ← replaceIn g x x'
  g.withContext do
  if x'.isAppOfArity ``Prod.mk 4 then pairRule g x' ``st_pair ``st_pair_fst env fuel
  else if x'.isAppOf ``SPTree.Timed.delay then rule g ``st_delay env fuel
  else if x'.isAppOf ``SPTree.Timed.map then rule g ``st_map env fuel
  else if x'.isAppOfArity ``ite 5 then rule g ``st_ite env fuel
  else if x'.isAppOfArity ``dite 5 then rule g ``st_dite env fuel
  else if x'.isAppOfArity ``SPTree.Timed.bind 4 then
    let a := x'.getArg! 2
    let a' ← sndThroughDelay (← whnfC a)
    let a' := (← unfoldTree? a').getD a'
    let node : Option Name :=
      if a'.isAppOf ``SPTree.Timed.ret then some ``st_bind_ret
      else if a'.isAppOf ``SPTree.Timed.sample then some ``st_bind_sample
      else if a'.isAppOf ``SPTree.Timed.get then some ``st_bind_get
      else if a'.isAppOf ``SPTree.Timed.set then some ``st_bind_set
      else if a'.isAppOf ``SPTree.Timed.fail then some ``st_bind_fail
      else none
    match node with
    | some n => rule (← replaceIn g a a') n env fuel
    | none =>
      -- a bind after the tree `y.2` of a costed bind `y`, with `y.1` on the path
      for b in [a, a'] do
        if let some y := sndOf? b then
          if y.isAppOfArity ``SPTree.Timed.bind 4 then
            let s ← saveState
            if ← fstSummand (← replaceIn g a b) y ``st_snd_bind_fst env fuel then return
            s.restore
      let s ← saveState
      try
        rule g ``st_bind env fuel
      catch e =>
        s.restore
        -- the continuation bounded at the values satisfying an inferred leaf invariant
        if ← bindInv g x' env fuel then return
        throw e
  else if ← splitMatch g x' env fuel then return
  else if let some gs ← boolCases? g x' then
    for g' in gs do solve g' env (fuel - 1)
  else leaf g .step x' env fuel

/-- `AllRet Q t` by the rules `ar_*` on the visible structure of `t` (a definition unfolded, a
tree without visible leaves by `ar_any`); a leaf goal `Q a` by `solve`. -/
partial def arSolve (g : MVarId) (env : Bool) (fuel : Nat) : TacticM Unit := do
  if fuel == 0 then throwError "time_bound: depth bound reached"
  let g ← liftLets g
  g.withContext do
  let tgt0 ← instantiateMVars (← g.getType)
  let tgt ← Core.betaReduce tgt0
  let g ← if tgt == tgt0 then pure g else g.replaceTargetDefEq tgt
  if tgt.isForall then
    let (_, g') ← g.intro1P
    arSolve g' env (fuel - 1)
    return
  unless tgt.isAppOfArity ``SPTree.Timed.AllRet 3 do
    invLeaf g fuel
    return
  let t := tgt.appArg!
  let mut t1 ← sndThroughDelay (← whnfC t)
  if let some y := sndOf? t1 then
    if let some y' ← unfoldTree? y then
      t1 ← sndThroughDelay (← whnfC (← mkAppM ``Prod.snd #[y']))
  else if let some t2 ← unfoldTree? t1 then
    t1 := t2
  let g ← replaceIn g t t1
  let n? : Option Name :=
    if t1.isAppOf ``SPTree.Timed.ret then some ``ar_ret
    else if t1.isAppOf ``SPTree.Timed.sample then some ``ar_sample
    else if t1.isAppOf ``SPTree.Timed.get then some ``ar_get
    else if t1.isAppOf ``SPTree.Timed.set then some ``ar_set
    else if t1.isAppOf ``SPTree.Timed.load then some ``ar_load
    else if t1.isAppOf ``SPTree.Timed.fail then some ``ar_fail
    else if t1.isAppOfArity ``ite 5 then some ``ar_ite
    else if t1.isAppOfArity ``dite 5 then some ``ar_dite
    else match sndOf? t1 with
      | some b => if b.isAppOfArity ``SPTree.Timed.bind 4 then some ``ar_bind else none
      | none => none
  if let some n := n? then
    let some gs ← applyRule g n | throwError "time_bound: rule {n} does not apply"
    for g' in gs do arSolve g' env (fuel - 1)
    return
  if (← matchMatcherApp? t1).isSome then
    let some (some gs) ← capped (splitTarget? g) | throwError "time_bound: match not split"
    for g' in gs do arSolve g' env (fuel - 1)
    return
  let some gs ← applyRule g ``ar_any | throwError "time_bound: no leaf invariant"
  for g' in gs do arSolve g' env (fuel - 1)

/-- A bind `A.bind f` whose continuation is not bounded at every value: for each companion
that `f` reads and each hypothesis bounding a companion of its type (`invCandidates`), the
least slack of the ladder at which `arSolve` proves the leaf invariant of `A`; the invariants
found are conjoined and `st_bind_inv` applied. -/
partial def bindInv (g : MVarId) (x : Expr) (env : Bool) (fuel : Nat) : TacticM Bool :=
    g.withContext do
  let α := x.getArg! 0
  let A := x.getArg! 2
  let f := x.getArg! 3
  let cands ← invCandidates α f
  if cands.isEmpty then return false
  let mut proofs : Array Expr := #[]
  for ladder in cands do
    for q in ladder do
      let s ← saveState
      let m ← mkFreshExprMVar (← mkAppM ``SPTree.Timed.AllRet #[q, A])
      try
        arSolve m.mvarId! env (fuel - 1)
        proofs := proofs.push (← instantiateMVars m)
        break
      catch _ => s.restore
  if proofs.isEmpty then return false
  let mut pf := proofs[0]!
  for p in proofs[1:] do
    pf ← mkAppM ``SPTree.Timed.allRet_and #[pf, p]
  let s ← saveState
  try
    let some gs ← applyRule g ``st_bind_inv [pf] | return false
    let some hk := gs.getLast? | return false
    for g' in gs.dropLast do solve g' env (fuel - 1)
    let (_, g1) ← hk.intro1P
    let (hq, g2) ← g1.intro1P
    let g3 ← g2.withContext do
      let ty ← instantiateMVars (← hq.getType)
      g2.replaceLocalDeclDefEq hq (← Core.betaReduce ty)
    let g4 ← g3.casesAnd
    solve g4 env (fuel - 1)
    return true
  catch _ =>
    s.restore
    return false

/-- `P + t ≤ B` where `t` is the tree `y.2` or a bind after it, with the summand `y.1` in `P`
(up to reducible defeq): the rule `lem` (`time_snd_fst`, `st_snd_bind_fst`) reads the two
together, with `P` less the summand as its first free argument. -/
partial def fstSummand (g : MVarId) (y : Expr) (lem : Name) (env : Bool) (fuel : Nat) :
    TacticM Bool := g.withContext do
  let s0 ← saveState
  -- the summand `y.1` as it stands on the path, else after the step costs are reduced
  for reduce in [false, true] do
    let g ← if reduce then reduceStepCosts g else pure g
    let tgt ← instantiateMVars (← g.getType)
    let some (l, _) := natLe? tgt | s0.restore; return false
    unless l.isAppOfArity ``HAdd.hAdd 6 do s0.restore; return false
    let p := l.getArg! 4
    let fsts := (appsOf p #[]).filter fun t => (fstOf? t).isSome
    for o in fsts do
      let s ← saveState
      if ← withReducible (isDefEq (fstOf? o).get! y) then
        let y1 := withFstArg o y
        let p' := p.replace fun t => if t == o then some y1 else none
        let q := p.replace fun t => if t == o then some (mkNatLit 0) else none
        let g' ← replaceIn g p p'
        try
          if ← applyAndSolve g' lem [q] env fuel then return true
        catch _ => pure ()
      s.restore
    s0.restore
  return false

/-- `P + t.time ≤ B`. -/
partial def treeCase (g : MVarId) (t : Expr) (env : Bool) (fuel : Nat) : TacticM Unit := do
  let t1 ← whnfC t
  -- a stuck second projection keeps its form `Prod.snd y`
  let t' := if (sndOf? t1).isSome && (sndOf? t).isSome then t else t1
  let g ← replaceIn g t t'
  g.withContext do
  if t'.isAppOf ``SPTree.Timed.ret then rule g ``time_ret env fuel
  else if t'.isAppOf ``SPTree.Timed.sample then rule g ``time_sample env fuel
  else if t'.isAppOf ``SPTree.Timed.get then rule g ``time_get env fuel
  else if t'.isAppOf ``SPTree.Timed.set then rule g ``time_set env fuel
  else if t'.isAppOf ``SPTree.Timed.fail then rule g ``time_fail env fuel
  else if t'.isAppOf ``SPTree.Timed.load then rule g ``time_load env fuel
  else if t'.isAppOfArity ``ite 5 then rule g ``time_ite env fuel
  else if t'.isAppOfArity ``dite 5 then rule g ``time_dite env fuel
  else if let some y := sndOf? t' then
    if ← fstSummand g y ``time_snd_fst env fuel then return
    rule g ``time_snd env fuel
  else if ← splitMatch g t' env fuel then return
  else leaf g .time t' env fuel

/-- `A.TimeBound (B - P)`. -/
partial def tbCase (g : MVarId) (a : Expr) (env : Bool) (fuel : Nat) : TacticM Unit := do
  let a' ← whnfC a
  let g ← replaceIn g a a'
  g.withContext do
  if a'.isAppOf ``OracleAdv.Timed.ret then rule g ``tb_ret env fuel
  else if a'.isAppOf ``OracleAdv.Timed.rand then rule g ``tb_rand env fuel
  else if a'.isAppOf ``OracleAdv.Timed.query then rule g ``tb_query env fuel
  else if a'.isAppOfArity ``ite 5 then rule g ``tb_ite env fuel
  else if a'.isAppOfArity ``dite 5 then rule g ``tb_dite env fuel
  else if (sndOf? a').isSome then rule g ``tb_snd env fuel
  else if ← splitMatch g a' env fuel then return
  else leaf g .tb a' env fuel

/-- `StepTimeBound x (B - P)`. -/
partial def stbCase (g : MVarId) (x : Expr) (env : Bool) (fuel : Nat) : TacticM Unit := do
  let x' ← whnfC x
  let g ← replaceIn g x x'
  g.withContext do
  if x'.isAppOfArity ``Prod.mk 4 then pairRule g x' ``stb_pair ``stb_pair_fst env fuel
  else if x'.isAppOf ``OracleAdv.Timed.delay then rule g ``stb_delay env fuel
  else if x'.isAppOfArity ``ite 5 then rule g ``stb_ite env fuel
  else if x'.isAppOfArity ``dite 5 then rule g ``stb_dite env fuel
  else if x'.isAppOfArity ``OracleAdv.Timed.bind 6 then
    let a := x'.getArg! 4
    let a' ← whnfC a
    let a' := (← unfoldTree? a').getD a'
    let node : Option Name :=
      if a'.isAppOf ``OracleAdv.Timed.ret then some ``stb_bind_ret
      else if a'.isAppOf ``OracleAdv.Timed.rand then some ``stb_bind_rand
      else if a'.isAppOf ``OracleAdv.Timed.query then some ``stb_bind_query
      else none
    match node with
    | some n => rule (← replaceIn g a a') n env fuel
    | none =>
      let some pf ← findSource .tb a env fuel |
        throwError "time_bound: no time bound for the adversary{indentExpr a}"
      rule g ``stb_bind env fuel [pf]
  else if ← splitMatch g x' env fuel then return
  else leaf g .stb x' env fuel

/-- One goal of the procedure. -/
partial def solve (g : MVarId) (env : Bool) (fuel : Nat) : TacticM Unit := do
  if fuel == 0 then throwError "time_bound: depth bound reached"
  let g ← liftLets g
  g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  if tgt.isForall then
    let (_, g') ← g.intro1P
    solve g' env (fuel - 1)
  else if tgt.isAppOfArity ``And 2 then rule g ``And.intro env fuel
  else if tgt.isConstOf ``True then g.assign (mkConst ``True.intro)
  else if let some (l, _) := natLe? tgt then
    if l.isAppOfArity ``SPTree.Timed.stepTime 2 then
      rule g ``st_start (env || (← structuralRoot l.appArg!)) fuel
    else if l.isAppOfArity ``SPTree.Timed.time 2 then
      rule g ``time_start (env || (← structuralRoot l.appArg!)) fuel
    else if l.isAppOfArity ``HAdd.hAdd 6 then
      let y := l.appArg!
      if y.isAppOfArity ``SPTree.Timed.stepTime 2 then stepCase g y.appArg! env fuel
      else if y.isAppOfArity ``SPTree.Timed.time 2 then treeCase g y.appArg! env fuel
      else closeArith g env fuel
    else closeArith g env fuel
  else if tgt.isAppOfArity ``OracleAdv.Timed.TimeBound 5 then
    if (tgt.getArg! 4).isAppOfArity ``HSub.hSub 6 then tbCase g (tgt.getArg! 3) env fuel
    else rule g ``tb_start (env || (← structuralRoot (tgt.getArg! 3))) fuel
  else if tgt.isAppOfArity ``OracleAdv.Timed.StepTimeBound 5 then
    if (tgt.getArg! 4).isAppOfArity ``HSub.hSub 6 then stbCase g (tgt.getArg! 3) env fuel
    else rule g ``stb_start (env || (← structuralRoot (tgt.getArg! 3))) fuel
  else
    let s ← saveState
    try
      g.assumption
    catch _ =>
      s.restore
      closeArith g env fuel

end

/-! ### Leaf invariants of costed oracle adversaries -/

/-- `OracleAdv.Timed.AllRet`, named without the import of its module. -/
def advAllRet : Name := `CatCrypt.Crypto.OracleAdv.Timed.AllRet

/-- The adversary `t` with its head brought to view: `(c, A).2` is `A`, `(delay c x).2` is
`x.2`, and a head definition (also below a second projection) is unfolded. A bind
`(A.bind f).2` is kept. -/
def advHead (t : Expr) : MetaM Expr := do
  let mut t ← whnfC t
  for _ in [0:32] do
    if let some y := sndOf? t then
      let y' ← whnfC y
      if y'.isAppOfArity ``Prod.mk 4 then t ← whnfC (y'.getArg! 3)
      else if y'.isAppOfArity ``OracleAdv.Timed.delay 5 then
        t ← whnfC (← mkAppM ``Prod.snd #[y'.getArg! 4])
      else if y'.isAppOfArity ``OracleAdv.Timed.bind 6 then
        return ← mkAppM ``Prod.snd #[y']
      else if let some y'' ← unfoldTree? y' then
        t ← whnfC (← mkAppM ``Prod.snd #[y''])
      else return ← mkAppM ``Prod.snd #[y']
    else if let some t' ← unfoldTree? t then t := t'
    else return t
  return t

/-- The names of the leaf-invariant theorems of the adversary `t`: `N.allRet_le` for
`t = (N.timed …).2`, and `Ns.allRet_f` for a combinator `Ns.f` at the head of `t`, each also
resolved in the current namespaces. -/
def allRetNames (t : Expr) : MetaM (List Name) := do
  let t ← zetaReduce t
  let mut out : List Name := []
  if let some y := sndOf? t then
    if let some n := y.getAppFn.constName? then
      if n.lastComponentAsString == "timed" then
        let ex := n.getPrefix ++ `allRet_le
        if (← getEnv).contains ex then out := out ++ [ex]
        for c in ← resolvedCompanions n.getPrefix [`allRet_le] do
          unless out.contains c do out := out ++ [c]
  if let some n := t.getAppFn.constName? then
    let tag := Name.mkSimple ("allRet_" ++ n.lastComponentAsString)
    let ex := n.getPrefix ++ tag
    if (← getEnv).contains ex && !out.contains ex then out := out ++ [ex]
    for (c, fields) in ← resolveGlobalName tag do
      if fields.isEmpty && (← getEnv).contains c && !out.contains c then out := out ++ [c]
  return out

mutual

/-- A proof of `AllRet ?Q t`, `?Q` possibly unassigned, by a local hypothesis or a theorem of
`allRetNames`, its premises closed by the context or (for leaf invariants) by `arSource`. -/
partial def arSource (Q t : Expr) (fuel : Nat) : TacticM (Option Expr) := do
  if fuel == 0 then return none
  if let some pf ← arSourceAt Q t fuel then return some pf
  let t' ← advHead t
  if t' == t then return none
  arSourceAt Q t' fuel

/-- `arSource` at the tree `t` as it stands. -/
partial def arSourceAt (Q t : Expr) (fuel : Nat) : TacticM (Option Expr) := do
  let locals ← (← getLCtx).getFVars.filterM fun f => do
    return !(← f.fvarId!.getDecl).isImplementationDetail
  let names ← allRetNames t
  let cands := locals ++ (← names.toArray.mapM fun n => mkConstWithFreshMVarLevels n)
  for c in cands do
    let s ← saveState
    try
      let (ms, _, body) ← forallMetaTelescopeReducing (← inferType c)
      unless body.isAppOfArity advAllRet 5 do throwError "no"
      unless ← isDefEq (body.getArg! 4) t do throwError "no"
      unless ← isDefEq (body.getArg! 3) Q do throwError "no"
      for m in ms do
        let mid := m.mvarId!
        if ← mid.isAssigned then continue
        let ty ← instantiateMVars (← mid.getType)
        unless ← isProp ty do continue
        if ty.isAppOfArity advAllRet 5 then
          let some pf ← arSource (ty.getArg! 3) (ty.getArg! 4) (fuel - 1) | throwError "no"
          mid.assign pf
        else unless ← closeByContext mid do throwError "no"
      let pf ← instantiateMVars (mkAppN c ms)
      if pf.hasExprMVar then throwError "no"
      return some pf
    catch _ => s.restore
  return none

/-- An arithmetic or propositional leaf of a leaf invariant: conjunctions and universal
statements are split, the conjunctions of the context are split, and the goal is closed by
`omega` with the bounded atoms of the context, after case splits. -/
partial def arLeaf (g : MVarId) (fuel : Nat) : TacticM Unit := do
  if fuel == 0 then throwError "allret_bound: depth bound reached"
  let g ← g.casesAnd
  let g ← reduceProjBeta g
  g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  if tgt.isForall then
    let (_, g') ← g.intro1P
    arLeaf g' (fuel - 1)
  else if tgt.isAppOfArity ``And 2 then
    let [g1, g2] ← g.apply (mkConst ``And.intro) | throwError "allret_bound: And"
    arLeaf g1 (fuel - 1)
    arLeaf g2 (fuel - 1)
  else if tgt.isConstOf ``True then g.assign (mkConst ``True.intro)
  else if tgt.isAppOfArity advAllRet 5 then arAdv g (fuel - 1)
  else
    let s ← saveState
    try
      g.assumption
      return
    catch _ => s.restore
    let g1 ← addBoundedAtoms g
    try
      setGoals [g1]
      evalTactic (← `(tactic| omega))
      if (← getUnsolvedGoals).isEmpty then return
    catch _ => pure ()
    s.restore
    if let some gs ← recCases? g tgt then
      for g' in gs do arLeaf g' (fuel - 1)
      return
    let some (some gs) ← capped (splitTarget? g) |
      throwError "allret_bound: leaf not closed{indentExpr tgt}"
    for g' in gs do arLeaf g' (fuel - 1)

/-- `AllRet P t` for a costed oracle adversary `t`: a node by the definition of `AllRet`, an
`if` or `match` by a split, a bind `(A.bind f).2` by a leaf invariant of `A` from `arSource`
(`allRet_bind`) or by reducing the bind at a node, and any tree by a source (`allRet_mono`). -/
partial def arAdv (g : MVarId) (fuel : Nat) : TacticM Unit := do
  if fuel == 0 then throwError "allret_bound: depth bound reached"
  g.withContext do
  let tgt ← instantiateMVars (← g.getType)
  unless tgt.isAppOfArity advAllRet 5 do
    arLeaf g (fuel - 1)
    return
  let P := tgt.getArg! 3
  let t0 := tgt.getArg! 4
  let t ← advHead t0
  let g ← replaceIn g t0 t
  let isNode := t.isAppOf ``OracleAdv.Timed.ret || t.isAppOf ``OracleAdv.Timed.rand ||
    t.isAppOf ``OracleAdv.Timed.query
  if isNode then
    let some tgt' ← capped (whnfD (← g.getType)) | throwError "allret_bound: node"
    arLeaf (← g.replaceTargetDefEq (← Core.betaReduce tgt')) (fuel - 1)
    return
  let inner := (sndOf? t).getD t
  if inner.isAppOfArity ``ite 5 || inner.isAppOfArity ``dite 5 ||
      (← matchMatcherApp? inner).isSome then
    if let some (some gs) ← capped (splitTarget? g) then
      for g' in gs do arAdv g' (fuel - 1)
      return
  if let some fv ← recMajor? inner then
    if let some subgoals ← capped (g.cases fv) then
      for sg in subgoals do arAdv sg.mvarId (fuel - 1)
      return
  -- a source for the whole tree
  let s ← saveState
  let Q ← mkFreshExprMVar (← inferType P)
  if let some pf ← arSource Q t fuel then
    let e ← mkConstWithFreshMVarLevels `CatCrypt.Crypto.OracleAdv.Timed.allRet_mono
    let (ms, _, concl) ← forallMetaTelescopeReducing (← inferType e)
    if ← isDefEq concl (← g.getType) then
      let h := ms.back!
      if ← isDefEq h pf then
        g.assign (mkAppN e ms)
        for m in ms do
          unless ← m.mvarId!.isAssigned do arLeaf m.mvarId! (fuel - 1)
        return
  s.restore
  -- a bind: a leaf invariant of its first tree
  if let some b := sndOf? t then
    if b.isAppOfArity ``OracleAdv.Timed.bind 6 then
      let A := b.getArg! 4
      let α := b.getArg! 2
      let Q ← mkFreshExprMVar (← mkArrow α (mkSort .zero))
      let s1 ← saveState
      if let some pf ← arSource Q A fuel then
        let e ← mkConstWithFreshMVarLevels `CatCrypt.Crypto.OracleAdv.Timed.allRet_bind
        let (ms, _, concl) ← forallMetaTelescopeReducing (← inferType e)
        if ← isDefEq concl (← g.getType) then
          let hA := ms[ms.size - 2]!
          if ← isDefEq hA pf then
            g.assign (mkAppN e ms)
            let hf := ms.back!.mvarId!
            let (_, g1) ← hf.intro1P
            let (hq, g2) ← g1.intro1P
            let g3 ← g2.withContext do
              g2.replaceLocalDeclDefEq hq (← Core.betaReduce (← instantiateMVars (← hq.getType)))
            arAdv g3 (fuel - 1)
            return
      s1.restore
      -- the first tree at a node: the bind reduced
      let A' ← advHead A
      if A'.isAppOf ``OracleAdv.Timed.ret || A'.isAppOf ``OracleAdv.Timed.rand ||
          A'.isAppOf ``OracleAdv.Timed.query then
        let b' := mkAppN b.getAppFn (b.getAppArgs.set! 4 A')
        let some t' ← capped (whnfD (← mkAppM ``Prod.snd #[b'])) |
          throwError "allret_bound: bind"
        let g' ← g.replaceTargetDefEq (mkAppN tgt.getAppFn (tgt.getAppArgs.set! 4 t'))
        arAdv g' (fuel - 1)
        return
  throwError "allret_bound: no leaf invariant for{indentExpr t}"

end

/-- `allret_bound` proves a leaf invariant `AllRet P t` of a costed oracle adversary `t`, as
the companion bounds `∀ x, y.2.1.2 x ≤ b + 3` of the states that a costed handler returns, from
the hypotheses bounding the companions it receives (see `arAdv`). -/
syntax (name := allRetBoundStx) "allret_bound" : tactic

@[tactic allRetBoundStx] def evalAllRetBound : Tactic := fun _ => do
  let g ← getMainGoal
  let rest := (← getGoals).tail
  arLeaf g 256
  setGoals rest

/-- The depth bound of `time_bound`. -/
def maxDepth : Nat := 512

/-- `time_bound` proves `SPTree.Timed.stepTime x ≤ B`, `t.time ≤ B`,
`OracleAdv.Timed.StepTimeBound x n` and `A.TimeBound n` by consuming the costed tree node by
node, bounding the subtrees it cannot consume by local hypotheses or by the time theorems of
the definitions below the one named in the goal, and closing the arithmetic leaves by `omega`
or `linarith` with the bounded atoms of the context (see the module docstring). -/
syntax (name := timeBoundStx) "time_bound" : tactic

@[tactic timeBoundStx] def evalTimeBound : Tactic := fun _ => do
  let g ← getMainGoal
  let rest := (← getGoals).tail
  solve g false maxDepth
  setGoals rest

end

end CatCrypt.Tactics.AutoTime

/-! ## Registration with `catcrypt_auto` -/

catcrypt_auto_shape "time bound" direct priority 120 :=
  any [app CatCrypt.Crypto.OracleAdv.Timed.TimeBound,
    app CatCrypt.Crypto.OracleAdv.Timed.StepTimeBound,
    all [app LE.le, mentions [CatCrypt.Core.SPTree.Timed.stepTime, CatCrypt.Core.SPTree.Timed.time]]]

catcrypt_auto_arm "time bound" order 10 := "time_bound"

end
