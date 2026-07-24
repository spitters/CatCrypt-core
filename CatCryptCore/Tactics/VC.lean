/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Core.StdDoBridge
import CatCryptCore.Tactics.UpToBad
import CatCryptCore.Deep.PureCode

/-!
# VC tactics: `mvcgen`-driven closers for SPComp side conditions

The support-level `Std.Do` bridge (`CatCrypt.Core.StdDoBridge`) makes
`mvcgen` walk `SPComp` do-blocks. This file packages that into
goal-shape-dispatched tactics for the recurring side conditions of
CatCrypt's security proofs:

* `ssprove_ispure` — closes `SPComp.IsPure c` goals. It first tries the
  *syntactic* backend `ssprove_ispure_syn` (reify `c` into `RawCode` via
  `Reflect.reifySPComp`, apply `RawCode.eval_isPure_of_stateFree`, discharge
  `StateFree` by constructor search — see `CatCrypt.Deep.PureCode`), then
  falls back to the structural combinator cascade `ssprove_ispure_cascade`
  (`bind_isPure` / `sample_isPure` / `pure_isPure` / `fail_isPure` /
  `liftSDistr_isPure` / `assumption`). The syntactic branch only fires on
  fully concrete programs (sample/pure/fail/bind); the cascade additionally
  handles abstract sub-programs via hypotheses. `IsPure` is a
  distribution-equality statement (heap-independence of the *whole*
  distribution), strictly stronger than any support-level fact, so it is not
  `Triple`-expressible: the bridge's `isPure_wpProp_iff` *consumes* an
  `IsPure` witness (it simplifies `wpProp` given purity); it cannot produce
  one. Hence the structural/syntactic routes for this goal shape.
* `ssprove_nofail` — closes `SPComp.NoFail c` by lowering through
  `triple_noThrow_true_iff_noFail`, running `mvcgen` over the bridge's
  `@[spec]` lemmas, and finishing with the closing-simp cascade. These are
  exactly the NoFail side goals `ssprove_upto` produces.
* `ssprove_phoare` — lowers a unary `pHoare` goal through `pHoare_iff_triple`
  and runs `mvcgen`; VCs the closer cascade misses are left to the user
  (partial progress is intended).
* `ssprove_vc` — umbrella: `first | ssprove_ispure | ssprove_nofail |
  ssprove_phoare`.

Each tactic also takes an optional ident list (e.g. `ssprove_nofail [myGame]`)
that `unfold`s the named definitions first, so `mvcgen` / the combinator
cascade can see the underlying do-block.
-/

set_option autoImplicit false

namespace CatCrypt.Tactics.VC

/-! ## Closing-simp cascade

The bridge's examples show the closing idiom for the VCs `mvcgen` leaves:
either pure `rfl`, or a `simp` with the WP-unfolding lemmas plus the
support-shape lemmas and `Heap.get_set_same`. -/

/-- Closer for `mvcgen`-generated VCs on `SPComp` goals: `rfl`, then the
bridge unfolding simp set, then `simp_all`. Fails if any goal survives. -/
macro "sp_vc_close" : tactic =>
  `(tactic| all_goals first
    | rfl
    | (simp [CatCrypt.Core.SPComp.wp_eq, CatCrypt.Core.SPComp.wpSupport_apply_down,
        CatCrypt.Core.SPComp.bind_apply_some_ne_zero_iff,
        CatCrypt.Core.SPComp.bind_apply_none_ne_zero_iff,
        CatCrypt.Core.SPComp.pure_def, CatCrypt.Core.SPComp.get_def,
        CatCrypt.Core.SPComp.set_def, CatCrypt.Core.SPComp.monad_bind_eq,
        CatCrypt.Core.SPComp.monad_pure_eq,
        CatCrypt.Prob.SDistr.pure_apply_none,
        CatCrypt.Core.Heap.get_set_same])
    | simp_all)

/-- Best-effort variant of `sp_vc_close`: never fails, leaves the VCs the
cascade misses (used by `ssprove_phoare`, where partial progress is the
point). -/
macro "sp_vc_close?" : tactic =>
  `(tactic| all_goals try first
    | rfl
    | (simp [CatCrypt.Core.SPComp.wp_eq, CatCrypt.Core.SPComp.wpSupport_apply_down,
        CatCrypt.Core.SPComp.bind_apply_some_ne_zero_iff,
        CatCrypt.Core.SPComp.bind_apply_none_ne_zero_iff,
        CatCrypt.Core.SPComp.pure_def, CatCrypt.Core.SPComp.get_def,
        CatCrypt.Core.SPComp.set_def, CatCrypt.Core.SPComp.monad_bind_eq,
        CatCrypt.Core.SPComp.monad_pure_eq,
        CatCrypt.Prob.SDistr.pure_apply_none,
        CatCrypt.Core.Heap.get_set_same])
    | simp_all)

/-! ## `ssprove_ispure` -/

/-- `ssprove_ispure_syn` closes `SPComp.IsPure c` goals for *fully concrete*
`c` built from `sample` / `pure` / `fail` / `bind` (and `do`-notation over
them) by the syntactic route: reify `c` into `RawCode`, apply the soundness
lemma `RawCode.eval_isPure_of_stateFree`, and discharge `StateFree` by
constructor search. Depth-independent: no per-step combinator search.
Fails cleanly (for `first`-fallback) on programs containing abstract
sub-programs, `liftSDistr`, `ite`, or heap access. -/
macro "ssprove_ispure_syn" : tactic =>
  `(tactic| focus
      (show CatCrypt.Core.SPComp.IsPure _
       try simp only [CatCrypt.Core.SPComp.monad_bind_eq,
         CatCrypt.Core.SPComp.monad_pure_eq]
       ssprove_ispure_reflect
       apply CatCrypt.Deep.RawCode.eval_isPure_of_stateFree
       ssprove_statefree
       done))

/-- `ssprove_ispure_syn [d₁, d₂, ...]` unfolds the named game definitions
first, then runs the syntactic route. -/
macro "ssprove_ispure_syn" "[" ids:ident,* "]" : tactic => do
  let idArr := ids.getElems
  `(tactic| (unfold $idArr*; ssprove_ispure_syn))

/-- `ssprove_ispure_cascade` closes `SPComp.IsPure c` goals for `c` built from
`sample` / `pure` / `fail` / `liftSDistr` / `bind` (and hypotheses), by the
structural combinator cascade. The leading `show` is the goal-shape guard
that makes `ssprove_vc` dispatch correctly. -/
macro "ssprove_ispure_cascade" : tactic =>
  `(tactic| (show CatCrypt.Core.SPComp.IsPure _
             try simp only [CatCrypt.Core.SPComp.monad_bind_eq,
               CatCrypt.Core.SPComp.monad_pure_eq]
             repeat' first
               | assumption
               | exact CatCrypt.Core.SPComp.pure_isPure _
               | exact CatCrypt.Core.SPComp.sample_isPure _
               | exact CatCrypt.Core.SPComp.fail_isPure
               | exact CatCrypt.Core.liftSDistr_isPure _
               | apply CatCrypt.Core.SPComp.bind_isPure
               | intro _))

/-- `ssprove_ispure` closes `SPComp.IsPure c` goals: syntactic backend first
(`ssprove_ispure_syn` — all-or-nothing), then the structural combinator
cascade (`ssprove_ispure_cascade` — handles abstract sub-programs via
hypotheses). -/
macro "ssprove_ispure" : tactic =>
  `(tactic| first
    | ssprove_ispure_syn
    | ssprove_ispure_cascade)

/-- `ssprove_ispure [d₁, d₂, ...]` unfolds the named game definitions first,
then runs the syntactic-then-cascade dispatch. -/
macro "ssprove_ispure" "[" ids:ident,* "]" : tactic => do
  let idArr := ids.getElems
  `(tactic| (unfold $idArr*; ssprove_ispure))

/-! ## `ssprove_nofail` -/

/-- `ssprove_nofail` closes `SPComp.NoFail c`: lowers to the trivial
total-correctness triple via `triple_noThrow_true_iff_noFail`, runs `mvcgen`
over the bridge's `@[spec]` lemmas, and closes the VCs with `sp_vc_close`.
This is the shape of the NoFail side goals `ssprove_upto` leaves. -/
macro "ssprove_nofail" : tactic =>
  `(tactic| (rw [← CatCrypt.Core.SPComp.triple_noThrow_true_iff_noFail]
             mvcgen
             sp_vc_close))

/-- `ssprove_nofail [d₁, d₂, ...]` unfolds the named game definitions first
so `mvcgen` can walk the do-block. -/
macro "ssprove_nofail" "[" ids:ident,* "]" : tactic => do
  let idArr := ids.getElems
  `(tactic| (unfold $idArr*; ssprove_nofail))

/-! ## `ssprove_phoare` -/

/-- `ssprove_phoare` lowers a unary pHL goal `pHoare P c Q` to the
partial-correctness (`⇓?`) `Std.Do` triple via `pHoare_iff_triple`, runs
`mvcgen`, and best-effort-closes the VCs. VCs the cascade misses are left
open for the user. -/
macro "ssprove_phoare" : tactic =>
  `(tactic| (rw [CatCrypt.Core.SPComp.pHoare_iff_triple]
             mvcgen
             sp_vc_close?))

/-- `ssprove_phoare [d₁, d₂, ...]` unfolds the named definitions first. -/
macro "ssprove_phoare" "[" ids:ident,* "]" : tactic => do
  let idArr := ids.getElems
  `(tactic| (unfold $idArr*; ssprove_phoare))

/-! ## `ssprove_vc` umbrella -/

/-- `ssprove_vc` dispatches on the goal head: `SPComp.IsPure` →
`ssprove_ispure`, `SPComp.NoFail` → `ssprove_nofail`, `pHoare` →
`ssprove_phoare`. -/
macro "ssprove_vc" : tactic =>
  `(tactic| first
    | ssprove_ispure
    | ssprove_nofail
    | ssprove_phoare)

/-- `ssprove_vc [d₁, d₂, ...]` unfolds the named definitions first. -/
macro "ssprove_vc" "[" ids:ident,* "]" : tactic => do
  let idArr := ids.getElems
  `(tactic| (unfold $idArr*; ssprove_vc))

end CatCrypt.Tactics.VC

/-! ## Tactic Tests

IsPure of a sampled do-block, NoFail of a sample/set/get block (the
side-goal shape `ssprove_upto` produces), and a pHoare lowering. -/

section VCTests

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.BadEvent
open scoped ENNReal

set_option mvcgen.warning false

/-- Demo location storing a `Bool`. -/
abbrev vcLoc : Location := ⟨0, Bool⟩

/-- IsPure of a two-sample/pure do-block (manually: a 4-combinator chain). -/
example : SPComp.IsPure (do
    let b ← SPComp.sample Bool
    let c ← SPComp.sample Bool
    pure (b && c)) := by
  ssprove_ispure

/-! ### Syntactic-branch tests (`ssprove_ispure_syn`) -/

/-- Sample-only: closed by the syntactic branch alone. -/
example : SPComp.IsPure (SPComp.sample Bool) := by
  ssprove_ispure_syn

/-- Sample-bind-pure do-block: closed by the syntactic branch alone. -/
example : SPComp.IsPure (do
    let b ← SPComp.sample Bool
    let c ← SPComp.sample Bool
    pure (b && c)) := by
  ssprove_ispure_syn

/-- Sample-then-fail: closed by the syntactic branch alone. -/
example : SPComp.IsPure (do
    let _b ← SPComp.sample Bool
    (SPComp.fail : SPComp Bool)) := by
  ssprove_ispure_syn

/-- Abstract adversary application: unreifiable, so the syntactic branch
must FAIL, and `ssprove_ispure` falls back to the combinator cascade
(closing the abstract leaf by `assumption`). -/
example (A : SPComp Bool) (hA : SPComp.IsPure A) :
    SPComp.IsPure (do
      let b ← SPComp.sample Bool
      let a ← A
      pure (a && b)) := by
  fail_if_success ssprove_ispure_syn
  ssprove_ispure

/-- NoFail through sample, set, get, and pure — closed by `mvcgen` over the
bridge's `@[spec]` lemmas. -/
example : SPComp.NoFail (do
    let b ← SPComp.sample Bool
    SPComp.set vcLoc b
    let r ← SPComp.get vcLoc
    pure (r == b)) := by
  ssprove_nofail

/-- Demo game writing its sampled bit to the heap. -/
noncomputable def vcG₀ : SPComp Bool := do
  let b ← SPComp.sample Bool
  SPComp.set vcLoc b
  pure b

/-- Demo game writing the negated bit. -/
noncomputable def vcG₁ : SPComp Bool := do
  let b ← SPComp.sample Bool
  SPComp.set vcLoc (!b)
  pure b

/-- The NoFail side goals of `ssprove_upto` are closed by `ssprove_vc`
(umbrella dispatch to `ssprove_nofail`). -/
example (bad : SPComp Bool) (ε : ℝ≥0∞) (A : Bool → SPComp Bool)
    (h_iub : ∀ A : Bool → SPComp Bool,
      IdenticalUntilBad (vcG₀.bind A) (vcG₁.bind A) bad)
    (hnfA : ∀ a, SPComp.NoFail (A a))
    (h_bad : prTrue bad Heap.empty ≤ ε) :
    AdvantageA vcG₀ vcG₁ A ≤ ε := by
  ssprove_upto bad
  · exact h_iub
  · ssprove_vc [vcG₀]
  · ssprove_vc [vcG₁]
  · exact h_bad
  · exact hnfA

/-- pHoare lowering: write-then-read returns the written value. -/
example (l : Location) (v : l.ty) :
    CatCrypt.Unary.pHoare (fun _ => True) (do SPComp.set l v; SPComp.get l)
      (fun r _ => r = v) := by
  ssprove_phoare

end VCTests
