/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.XDijkstra.XMvcgen


@[expose] public section
set_option autoImplicit false

/-!
# `XMvcgenControl`: lifting `xmvcgen` from straight-line code to control flow

This module is **Phase 3** of the extended-PostShape Dijkstra framework. Phase 2
(`XMvcgen`) gave a verification-condition generator `xmvcgen` that discharges
*straight-line* fused goals — a single graded step, a framed pure step, a
relational product. This module extends it along the dimension a program logic
must cover: **control flow**. Three forms are added, each with its
weakest-precondition reduction and a demo on which `xmvcgen` fires:

1. **Bind-chains / multi-step.** A 3-plus-step program built as an `xseq`-chain.
   The grade threads through `xseq` (additive grade accumulation lives on `xseq`,
   not the value-dependent `bind`), so a chain of unit-cost steps reduces to the
   `n`-fold sum. `xmvcgen` computes the total grade to `1 + 1 + 1` and leaves the
   residual budget VC `3 ≤ budget`.

2. **Branching (if-then-else / φ-merge).** Two combinators:
   * `xite c t e` — the exact `Bool`-selected conditional (`bif c then t else e`);
     its WP is `bif c then t.apply Q else e.apply Q`, its head grade is the
     selected branch grade, and the triple rule `xite_triple` needs *both* branch
     obligations (the symbolic-`c` case). `xmvcgen` reduces the WP/grade to a
     `bif`, and casing on `c` leaves the two branch VCs.
   * `xphi t e` — the **φ-merge**: the branch-agnostic worst case. Its WP is the
     **meet** `t.apply Q ∧ e.apply Q` (both branches must establish `Q`) and its
     head grade is the **max** `max t.grade.1 e.grade.1`. `xphi_triple` splits a
     merge goal into both branch VCs in one shot.

3. **Bounded loop.** `xfor n body` folds `body` `n` times through `xseq`. Its head
   grade is `n · body.grade.1` (`xfor_grade_fst`, proved by induction — the
   **general `n` closes**, no unrolling needed), and the invariant rule
   `xfor_triple` threads a loop invariant through the `n` iterations. A counted
   loop of unit-cost `tick 1` therefore has grade `n`, leaving the budget VC
   `n ≤ budget`.

Grades are threaded through `xseq` throughout: the value-dependent `xbind` cannot
carry a static additive grade, so every control-flow combinator here (`xseq`-chains,
the `xfor` fold) sequences with `xseq`, and the branch grade is a `bif`/`max` of the
per-branch `xseq`-grades.

## `@[xspec]` and downstream extensibility

The per-operation reductions below are tagged `@[simp, xspec]`: this is downstream
of `XMvcgen`, so — unlike in that defining file — the `xspec` attribute registered
there *is* taggable and referenceable here. Tagging populates the open `xspec`
simp set with the control-flow reductions; the demos drive `xmvcgen [extra…]`
(which appends the new lemmas to Phase 2's explicit bundle), and `xmvcgen_ctl`
below is the `simp only [xspec, …]`-driven variant that picks them up
automatically.
-/

namespace CatCrypt.XDijkstra

/-! ## 0. A parameterized unit-cost step

`tick k` is a cost-`k` step at shape `.graded ℕ .pure` returning `()`. It is the
atom every control-flow demo is built from; `tick 1` is the unit-cost step. -/

/-- A cost-`k` step at shape `.graded ℕ .pure`, grade `(k, ⟨⟩)`, returning `()`. -/
def tick (k : ℕ) : XPredTrans (.graded ℕ .pure) Prop Unit where
  apply Q := Q.1 ()
  grade := (k, ⟨⟩)
  mono h := h.1 ()

@[simp] theorem tick_grade_fst (k : ℕ) : (tick k).grade.1 = k := rfl

@[simp] theorem tick_apply (k : ℕ) (Q : XPostCond Unit (.graded ℕ .pure) Prop) :
    (tick k).apply Q = Q.1 () := rfl

/-! ## 1. Bind-chains / multi-step

A multi-step program is an `xseq`-chain. `xseq_grade` / `xwp_graded_bind` (both in
`xmvcgen`'s bundle) rewrite the chain's head grade to the summed cost, so an
`n`-step chain reduces automatically. The demo threads a 3-step chain and leaves
the budget residual. -/

/-- A 3-step unit-cost program: `tick 1 ; tick 1 ; tick 1`, sequenced by `xseq`. -/
def prog3 : XPredTrans (.graded ℕ .pure) Prop Unit :=
  xseq (tick 1) (xseq (tick 1) (tick 1))

/-- **Multi-step grade demo.** `xmvcgen` threads the 3-fold `xseq`-chain's grade to
`1 + 1 + 1` and leaves the budget VC. The chain's head grade reduces through
`xwp_graded_bind` twice; `omega` closes `3 ≤ budget`. -/
theorem demo_multistep (budget : ℕ) (h : 3 ≤ budget) :
    prog3.grade.1 ≤ budget := by
  xmvcgen [prog3, tick_grade_fst]
  omega

/-- The 3-step chain has grade exactly `3`. -/
theorem prog3_grade : prog3.grade.1 = 3 := rfl

/-- **Multi-step triple demo.** A Hoare triple threaded through all three steps via
`xseq_triple` with intermediate assertion `True`. The grade is the summed `3`. -/
theorem demo_multistep_triple :
    XPT (ps := .graded ℕ .pure) True prog3 (fun _ => True, ⟨⟩) := by
  unfold prog3
  refine xseq_triple (Ω := Prop) (ps := .graded ℕ .pure) (R := True) (fun _ => trivial) ?_
  refine xseq_triple (Ω := Prop) (ps := .graded ℕ .pure) (R := True) (fun _ => trivial) (fun _ => trivial)

/-! ## 2. Branching

### 2a. The exact `Bool`-selected conditional `xite`

`xite c t e = bif c then t else e`: the program that runs `t` when `c` is `true`
and `e` when `c` is `false`. Its WP and head grade reduce to a `bif`; verifying it
for a *symbolic* `c` (`xite_triple`) needs both branch obligations. -/

/-- The `Bool`-selected conditional: `bif c then t else e`. -/
def xite {ps : XPostShape} {Ω : Type} [Preorder Ω] [LE Ω] {α : Type}
    (c : Bool) (t e : XPredTrans ps Ω α) : XPredTrans ps Ω α :=
  bif c then t else e

@[simp, xspec] theorem xite_apply {ps : XPostShape} {Ω : Type} [Preorder Ω] {α : Type}
    (c : Bool) (t e : XPredTrans ps Ω α) (Q : XPostCond α ps Ω) :
    (xite c t e).apply Q = bif c then t.apply Q else e.apply Q := by
  cases c <;> rfl

@[simp, xspec] theorem xite_grade {ps : XPostShape} {Ω : Type} [Preorder Ω] {α : Type}
    (c : Bool) (t e : XPredTrans ps Ω α) :
    (xite c t e).grade = bif c then t.grade else e.grade := by
  cases c <;> rfl

/-- The head grade of a conditional at a `.graded G ps'` shape is the `bif` of the
two branch grades — the reduction `xmvcgen` uses to expose per-branch budget VCs. -/
@[simp, xspec] theorem xite_grade_fst {G : Type} {ps' : XPostShape} {Ω : Type}
    [Preorder Ω] {α : Type} (c : Bool)
    (t e : XPredTrans (.graded G ps') Ω α) :
    (xite c t e).grade.1 = bif c then t.grade.1 else e.grade.1 := by
  cases c <;> rfl

/-- **Conditional rule (symbolic `c`).** To verify `xite c t e` for *every* `c`,
verify both branches: from `⦃P⦄ t ⦃Q⦄` and `⦃P⦄ e ⦃Q⦄` obtain `⦃P⦄ xite c t e ⦃Q⦄`.
-/
theorem xite_triple {ps : XPostShape} {Ω : Type} [Preorder Ω] {α : Type}
    {P : XAssertion ps Ω} {t e : XPredTrans ps Ω α} {Q : XPostCond α ps Ω}
    (c : Bool) (ht : XPT P t Q) (he : XPT P e Q) : XPT P (xite c t e) Q := by
  cases c
  · exact he
  · exact ht

/-- **Conditional demo.** The program `if b then tick 1 else tick 2`. `xmvcgen`
reduces the head grade to `bif b then 1 else 2`; casing on `b` leaves the two
per-branch budget VCs (`1 ≤ budget` and `2 ≤ budget`), each closed by `omega`. The
triple splits into both branches via `xite_triple`. -/
theorem demo_branch (budget : ℕ) (h : 2 ≤ budget) (b : Bool) :
    (xite b (tick 1) (tick 2)).grade.1 ≤ budget
    ∧ XPT (ps := .graded ℕ .pure) True (xite b (tick 1) (tick 2)) (fun _ => True, ⟨⟩) := by
  refine ⟨?_, ?_⟩
  · -- grade axis: xmvcgen exposes the `bif`; both branches ≤ budget.
    xmvcgen [xite_grade_fst, tick_grade_fst]
    cases b <;> simp <;> omega
  · -- control axis: both branch VCs via `xite_triple` (here both trivially true).
    exact xite_triple b (fun _ => trivial) (fun _ => trivial)

/-! ### 2b. The φ-merge `xphi` — meet postcondition, max grade

`xphi t e` is the branch-agnostic join point (an SSA φ-node): its weakest
precondition is the **meet** `t.apply Q ∧ e.apply Q` (to pass the merge, *both*
incoming branches must establish `Q`), and its head grade is the worst case
`max t.grade.1 e.grade.1`. It is stated at shape `.graded ℕ .pure` over `Prop`,
where an assertion *is* a `Prop` and the meet is `∧`. -/

/-- The **φ-merge** of two branches: WP is the meet `∧`, grade is the `max`. -/
def xphi {α : Type}
    (t e : XPredTrans (.graded ℕ .pure) Prop α) : XPredTrans (.graded ℕ .pure) Prop α where
  apply Q := t.apply Q ∧ e.apply Q
  grade := (max t.grade.1 e.grade.1, ⟨⟩)
  mono h := fun hpre => ⟨t.mono h hpre.1, e.mono h hpre.2⟩

@[simp, xspec] theorem xphi_apply {α : Type}
    (t e : XPredTrans (.graded ℕ .pure) Prop α) (Q : XPostCond α (.graded ℕ .pure) Prop) :
    (xphi t e).apply Q = (t.apply Q ∧ e.apply Q) := rfl

@[simp, xspec] theorem xphi_grade_fst {α : Type}
    (t e : XPredTrans (.graded ℕ .pure) Prop α) :
    (xphi t e).grade.1 = max t.grade.1 e.grade.1 := rfl

/-- **φ-merge rule.** A merge goal splits into both branch VCs: from `⦃P⦄ t ⦃Q⦄`
and `⦃P⦄ e ⦃Q⦄` obtain `⦃P⦄ xphi t e ⦃Q⦄`. -/
theorem xphi_triple {α : Type} {P : XAssertion (.graded ℕ .pure) Prop}
    {t e : XPredTrans (.graded ℕ .pure) Prop α} {Q : XPostCond α (.graded ℕ .pure) Prop}
    (ht : XPT P t Q) (he : XPT P e Q) : XPT P (xphi t e) Q :=
  fun hP => ⟨ht hP, he hP⟩

/-- **φ-merge demo.** Merging `tick 1` and `tick 2`: `xmvcgen` reduces the head
grade to `max 1 2 = 2` and leaves the single budget VC, and the triple obligation
is the meet of both branches. -/
theorem demo_phi (budget : ℕ) (h : 2 ≤ budget) :
    (xphi (tick 1) (tick 2)).grade.1 ≤ budget
    ∧ XPT (ps := .graded ℕ .pure) True (xphi (tick 1) (tick 2)) (fun _ => True, ⟨⟩) := by
  refine ⟨?_, ?_⟩
  · -- grade axis: xmvcgen threads the worst-case `max 1 2`.
    xmvcgen [xphi_grade_fst, tick_grade_fst]
    omega
  · -- control axis: both branch VCs (trivially true) via `xphi_triple`.
    exact xphi_triple (fun _ => trivial) (fun _ => trivial)

/-! ## 3. Bounded loop `xfor`

`xfor n body` folds `body` `n` times through `xseq`. The head grade is `n ·
body.grade.1` — the **general `n`** closes by induction (`xfor_grade_fst`), so no
unrolling is needed — and `xfor_triple` threads a loop invariant through the `n`
iterations. -/

/-- The counted loop: fold `body` `n` times, sequencing with `xseq`. -/
def xfor (n : ℕ) (body : XPredTrans (.graded ℕ .pure) Prop Unit) :
    XPredTrans (.graded ℕ .pure) Prop Unit :=
  match n with
  | 0 => xpure ()
  | n + 1 => xseq body (xfor n body)

/-- **The loop grade is `n · body.grade.1`.** Proved by induction on `n`; the
general `n` closes (no concrete unrolling). At each step the head grade adds one
`body.grade.1` through `xseq`. -/
theorem xfor_grade_fst (n : ℕ) (body : XPredTrans (.graded ℕ .pure) Prop Unit) :
    (xfor n body).grade.1 = n * body.grade.1 := by
  induction n with
  | zero => rw [Nat.zero_mul]; rfl
  | succ k ih =>
    show (xseq body (xfor k body)).grade.1 = (k + 1) * body.grade.1
    rw [xseq_grade]
    show body.grade.1 + (xfor k body).grade.1 = (k + 1) * body.grade.1
    rw [ih, Nat.add_mul, Nat.one_mul]; omega

/-- **Loop invariant rule.** If `body` preserves the invariant `I`
(`⦃I⦄ body ⦃_ ↦ I⦄`) then so does the whole loop: `⦃I⦄ xfor n body ⦃_ ↦ I⦄`.
Proved by induction on `n`, threading `I` with `xseq_triple` at each iteration. -/
theorem xfor_triple {I : Prop} {body : XPredTrans (.graded ℕ .pure) Prop Unit}
    (hb : XPT (ps := .graded ℕ .pure) I body (fun _ => I, ⟨⟩)) (n : ℕ) :
    XPT (ps := .graded ℕ .pure) I (xfor n body) (fun _ => I, ⟨⟩) := by
  induction n with
  | zero => exact fun hI => hI
  | succ k ih =>
    exact xseq_triple (Ω := Prop) (ps := .graded ℕ .pure) (R := I) hb ih

/-- **Bounded-loop demo.** A counted loop of unit-cost `tick 1`, run `n` times, has
grade `n · 1 = n`; `xfor_grade_fst` reduces the head grade for **general `n`**,
leaving the budget VC `n ≤ budget`, closed by `omega`. -/
theorem demo_loop (n budget : ℕ) (h : n ≤ budget) :
    (xfor n (tick 1)).grade.1 ≤ budget := by
  rw [xfor_grade_fst, tick_grade_fst, Nat.mul_one]
  omega

/-- **Bounded-loop triple demo.** The invariant `True` is preserved through every
iteration of `xfor n (tick 1)`, for general `n`, via `xfor_triple`. -/
theorem demo_loop_triple (n : ℕ) :
    XPT (ps := .graded ℕ .pure) True (xfor n (tick 1)) (fun _ => True, ⟨⟩) :=
  xfor_triple (fun hI => hI) n

/-! ## 4. Downstream `xmvcgen_ctl`: the `xspec`-driven control-flow variant

`xmvcgen`'s in-file bundle (Phase 2) is explicit because the `xspec` attribute is
untaggable in its own defining file. Here, downstream, the attribute *is* live:
the control-flow reductions above are tagged `@[xspec]`, so a `simp only [xspec,
…]` normalizer picks them up automatically. `xmvcgen_ctl` is that variant — it
folds the open `xspec` set into Phase 2's core reductions, so a further-downstream
module adding another control-flow operation need only tag its reduction `@[xspec]`
for `xmvcgen_ctl` to handle it, with no change to the tactic. -/

open Lean Parser.Tactic in
/-- Control-flow VC generator: Phase 2's core reductions plus the open `xspec` set
(the `@[xspec]`-tagged control-flow reductions). `xmvcgen_ctl [h, …]` adds extra
simp lemmas. -/
syntax (name := xmvcgenCtlTac) "xmvcgen_ctl" (" [" simpLemma,* "]")? : tactic

macro_rules
  | `(tactic| xmvcgen_ctl) =>
    `(tactic| simp only [xspec, XTriple, XPT, xwp_self,
        xpure_apply, xbind_apply, xseq_apply, xprod_apply, xwp_graded_bind, xseq_grade,
        XAssertion.le, XExceptConds.le])
  | `(tactic| xmvcgen_ctl [$xs,*]) =>
    `(tactic| simp only [xspec, XTriple, XPT, xwp_self,
        xpure_apply, xbind_apply, xseq_apply, xprod_apply, xwp_graded_bind, xseq_grade,
        XAssertion.le, XExceptConds.le, $xs,*])

/-- **`xmvcgen_ctl` demo.** The same branch grade goal as `demo_branch`, but driven
by the `xspec`-set variant: `xmvcgen_ctl` picks up `xite_grade_fst` automatically
(it is `@[xspec]`-tagged), reducing to the per-branch `bif`. -/
theorem demo_branch_ctl (budget : ℕ) (h : 2 ≤ budget) (b : Bool) :
    (xite b (tick 1) (tick 2)).grade.1 ≤ budget := by
  xmvcgen_ctl
  cases b <;> simp <;> omega

end CatCrypt.XDijkstra
