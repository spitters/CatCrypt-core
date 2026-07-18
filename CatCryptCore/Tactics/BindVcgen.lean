/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Tactics.BindAlign
import CatCryptCore.Core.Code

/-!
# `bind_vcgen` — run-to-completion for `SPComp`-*equality* goals

Distributional-equivalence proofs commonly have the shape

```
  SPComp.bind X (fun a => … pure (…)) = SPComp.bind Y (fun b => … pure (…))
```

i.e. an equality of two `SPComp.bind` chains, *not* a refinement. The proof is
always the same run-to-completion loop: repeatedly **normalize** (flatten
`bind_assoc`, fire `pure_bind`) and **peel** (`bind_align`) matching layers,
commuting a pure sample past an independent bind where needed, until the two
chains coincide up to a single change-of-variables residual — which the caller
supplies via a bijection.

## Attribution

The run-to-completion relational-VC-gen design is borrowed from **VCVio**'s
`rvcgen` (Devon Tuma, *VCVio: Verified Cryptography in Lean via Oracle Effects
and Handlers*, ePrint 2026/899) and **Loom** (`verse-lab/loom`). Those drive a
*refinement* (approximate-coupling / arWP) judgement to completion; `bind_vcgen`
is the `SPComp`-*equality* analogue — the exact-coupling, ε = 0 case, where the
two sides are provably the same distribution rather than ε-close. The `using`
clause mirrors `rvcstep using`: the caller hands in the change-of-variables
`Equiv` that the mechanical loop cannot guess.

## What is automated vs. supplied

`bind_vcgen` fully automates the *mechanical* part shared by every such proof:

* `spcomp_normalize` — a `simp only` over the monad rewrite set
  (`monad_bind_eq`, `bind_assoc`, `pure_bind`, `map`). Unfolding `SPComp.map`
  lets `bind_assoc` fuse a `map`-of-`bind` into the inner bind. It fails cleanly
  when it makes no progress, so it is safe inside `first`/`repeat`.
* `bind_step` (from `BindAlign`) — peels one matching `SPComp.bind` (head-strict
  `congrArg` + `funext`). Stops at the first head mismatch.

The loop `repeat (first | rfl | spcomp_normalize | bind_step)` runs these to a
fixpoint, closing goals that are pure reassociation / `pure`-elimination /
matching-prefix peeling, and otherwise reducing to the genuine residual.

The crux step is **caller-supplied**, because it needs data the loop cannot
synthesize:

* **change of variables** — `bind_vcgen using e` rewrites the `sample`-residual
  `bind (sample α) f = bind (sample β) g` by `SPComp.sample_bind_equiv e`
  (targeting the RHS only, via `refine Eq.trans ?_ (…)`, which pins the change
  to the right-hand `sample`), then peels again, leaving the pointwise
  `f a = g (e a)` obligation (discharged from `e.left_inv`).
-/

namespace CatCrypt.Tactic

open Lean Elab Tactic

/-- Normalize an `SPComp` bind-chain: rewrite `>>=` to `SPComp.bind`, flatten
    `bind_assoc`, fire `pure_bind`, and unfold `SPComp.map` (so `bind_assoc` can
    fuse a `map`-of-`bind` into its inner bind).

    Uses `simp only`, so it **fails cleanly when it makes no progress** — this
    makes it safe as an alternative inside `first`/`repeat`. -/
syntax "spcomp_normalize" : tactic
macro_rules
  | `(tactic| spcomp_normalize) => `(tactic|
      -- The rewrite set is fixed and generic, so not every lemma fires on every
      -- goal; silence the `unusedSimpArgs` linter at the call site.
      set_option linter.unusedSimpArgs false in
      simp only [CatCrypt.Core.SPComp.monad_bind_eq, CatCrypt.Core.SPComp.bind_assoc,
                 CatCrypt.Core.SPComp.pure_bind, CatCrypt.Core.SPComp.map])

/-- Run-to-completion driver for `SPComp`-*equality* goals.

    `bind_vcgen` repeatedly normalizes (`spcomp_normalize`) and peels matching
    `SPComp.bind` layers (`bind_step`) until it is stuck — closing the goal
    outright when the two bind-chains coincide, or leaving the genuine residual
    (a leaf equality / a `sample`-change-of-variables) for the caller.

    `bind_vcgen using e` additionally applies the change-of-variables
    `SPComp.sample_bind_equiv e` to the `sample`-residual (rewriting the RHS
    only), then peels again — leaving the pointwise `f a = g (e a)` obligation,
    which follows from `e.left_inv`.

    See the module docstring for the VCVio/Loom attribution and the precise
    "automated vs. supplied" split. -/
syntax "bind_vcgen" (" using " term)? : tactic
macro_rules
  | `(tactic| bind_vcgen) => `(tactic|
      repeat (first | rfl | spcomp_normalize | bind_step))
  | `(tactic| bind_vcgen using $e) => `(tactic|
      (try spcomp_normalize);
      (try (refine Eq.trans ?_ (CatCrypt.Core.SPComp.sample_bind_equiv $e _)));
      (repeat (first | rfl | spcomp_normalize | bind_step)))

end CatCrypt.Tactic
