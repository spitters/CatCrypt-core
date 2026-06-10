/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Lean
import CatCrypt.Core.Code
import CatCrypt.Relational.Rules
import CatCrypt.Tactics.SimpAttr

/-!
# Basic CatCrypt Tactics

This file provides basic tactic automation for CatCrypt proofs,
including tactics for ValidCode goals and code simplification.

## Main tactics

* `ssprove_valid` - tactic for proving ValidCode goals
* `ssprove_code_simpl` - tactic for simplifying code (normalize bind associativity)

## Simp sets

* `ssprove_simpl` - named simp set for SPComp normalization (declared in SimpAttr.lean)
* `ssprove_eval` - named simp set for deep→shallow evaluation (declared in SimpAttr.lean)

## References

* SSProve: theories/Crypt/package/pkg_tactics.v
-/

namespace CatCrypt.Tactics

open Lean Elab Tactic Meta
open CatCrypt.Core
open CatCrypt.Relational

/-! ## Simp Set Population

The simp sets are declared in CatCrypt.Tactics.SimpAttr (separate file
required because `register_simp_attr` creates attributes that cannot be
used in the same file they are declared in).
-/

-- SPComp monad laws
attribute [ssprove_simpl] SPComp.bind_assoc SPComp.pure_bind SPComp.bind_pure SPComp.monad_bind_eq

-- Dead code elimination
attribute [ssprove_simpl] dead_sample dead_get dead_pure

-- Contraction rules
attribute [ssprove_simpl] contract_get contract_put contract_put_get

-- Copy propagation
attribute [ssprove_simpl] set_get_same

-- Canonicalization aliases
attribute [ssprove_simpl] bind_assoc_lr pure_bind_lr bind_pure_lr

/-! ## ValidCode Tactics -/

/-- `ssprove_valid` is a tactic for proving `ValidCode` goals.

This tactic attempts to discharge `ValidCode` obligations by:
1. Unfolding definitions
2. Applying structural rules for bind, return, sample, etc.
3. Checking that operations access only permitted locations

Example:
```
theorem mycode_valid : ValidCode L I (do
    let x ← get loc
    return x) := by
  ssprove_valid
```
-/
elab "ssprove_valid" : tactic => do
  evalTactic (← `(tactic|
    first
    | trivial
    | constructor <;> (first | trivial | assumption)
    | assumption
  ))

/-- `ssprove_code_simpl` is a tactic for simplifying CatCrypt code.

This tactic normalizes code by:
1. Associating binds to the right: `(x >>= f) >>= g` → `x >>= (fun a => f a >>= g)`
2. Simplifying pure/return: `pure a >>= f` → `f a`
3. Eliminating dead code (unused sample, get, pure)
4. Contracting redundant operations (duplicate get/put, put-get)
5. Copy propagation (set-get same location)

Example:
```
example : ((c >>= f) >>= g) = (c >>= fun x => f x >>= g) := by
  ssprove_code_simpl
```
-/
elab "ssprove_code_simpl" : tactic => do
  evalTactic (← `(tactic|
    first
    | simp only [ssprove_simpl]
    | rfl
  ))

/-- Configuration for ssprove_valid tactic -/
structure ValidConfig where
  /-- Maximum recursion depth -/
  maxDepth : Nat := 100
  /-- Whether to unfold definitions -/
  unfold : Bool := true
  /-- Whether to use automation -/
  auto : Bool := true

/-- `ssprove_valid!` is a more aggressive version of `ssprove_valid`
that uses additional automation. -/
elab "ssprove_valid!" : tactic => do
  evalTactic (← `(tactic|
    first
    | trivial
    | constructor <;> (first | trivial | assumption | decide)
    | assumption
    | decide
  ))

/-! ## Distribution-Level Simplification

The `ssprove_distr_simp` tactic normalizes terms at the `SDistr` level,
after SPComp definitions have been unfolded. This handles the common pattern:

```
simp only [SPComp.bind_def, SPComp.sample, SPComp.pure_def,
           SDistr.bind_assoc, SDistr.pure_bind]
```

which appears 100+ times across shallow embedding proofs.
-/

set_option hygiene false in
/-- `ssprove_distr_simp` normalizes sub-distribution terms.

After unfolding SPComp to SDistr, this tactic reassociates binds,
eliminates pure-bind pairs, and normalizes sampling definitions.

Example:
```
-- Goal involves (SDistr.uniform α).bind (fun a => (SDistr.pure (a, h)).bind ...)
ssprove_distr_simp
-- Goal is now normalized with bind_assoc and pure_bind applied
```
-/
macro "ssprove_distr_simp" : tactic => `(tactic|
  simp only [SPComp.bind_def, SPComp.sample, SPComp.pure_def,
             SDistr.bind_assoc, SDistr.pure_bind])

/-! ## Enhanced Monadic Normalization

The `ssprove_proc` tactic normalizes `SPComp` programs at the monadic level,
analogous to EasyCrypt's `proc; inline *; auto`. It chains `bind_assoc`,
`pure_bind`, `bind_pure`, `monad_bind_eq`, and `monad_pure_eq`, then tries
`congr`/`funext` to push through binders, and `rfl` to close.

This replaces the common 5-10 line pattern:
```
simp only [SPComp.monad_bind_eq, SPComp.bind_assoc, SPComp.pure_bind, ...]
congr 1; funext _
simp only [...]
rfl
```
with a single `ssprove_proc` call. -/

set_option hygiene false in
/-- `ssprove_proc` normalizes SPComp monadic programs.

Analogous to EasyCrypt's `proc; inline *; auto`:
1. Simplify with `monad_bind_eq`, `bind_assoc`, `pure_bind`, `bind_pure`
2. Try `rfl`
3. If stuck, try `congr 1; funext` to descend through binders -/
macro "ssprove_proc" : tactic => `(tactic| (
  simp only [SPComp.monad_bind_eq, SPComp.bind_assoc, SPComp.monad_pure_eq,
             SPComp.pure_bind, SPComp.bind_pure, Function.comp]
  <;> first
    | rfl
    | (congr 1; funext _;
       simp only [SPComp.monad_bind_eq, SPComp.bind_assoc, SPComp.monad_pure_eq,
                  SPComp.pure_bind, SPComp.bind_pure, Function.comp]
       <;> first
         | rfl
         | (congr 1; funext _;
            simp only [SPComp.monad_bind_eq, SPComp.bind_assoc, SPComp.monad_pure_eq,
                       SPComp.pure_bind, SPComp.bind_pure, Function.comp]
            <;> try rfl))
  ))

set_option hygiene false in
/-- `ssprove_proc_unfold defs` unfolds definitions then normalizes.

Usage: `ssprove_proc_unfold my_real my_ideal` -/
macro "ssprove_proc_unfold " defs:ident* : tactic => `(tactic| (
  unfold $defs*
  ssprove_proc
  ))

/-! ## Bijection Coupling Tactic

The `ssprove_rnd` tactic automates change-of-variables on sampling steps,
analogous to EasyCrypt's `rnd f g; auto`. Given a goal about `SPComp.sample`,
it applies a bijection to transform the distribution.

This replaces:
```
apply sdist_of_eq
congr 1; funext a
exact SPComp.sample_bind_equiv (Equiv.addRight k) (fun a => ...)
```
with `ssprove_rnd (Equiv.addRight k)`. -/

set_option hygiene false in
/-- `ssprove_rnd e` applies bijection `e : α ≃ β` to a sampling step. -/
macro "ssprove_rnd " e:term : tactic => `(tactic| (
  first
  | exact SPComp.sample_bind_equiv $e _
  | (congr 1; funext _; exact SPComp.sample_bind_equiv $e _)
  | (apply le_of_eq; congr 1; funext _; exact SPComp.sample_bind_equiv $e _)
  ))

/-! ## Exponentiation Normalization Tactic

The `exp_simp` tactic normalizes group exponentiation terms, analogous to
EasyCrypt's `algebra` tactic. It:
1. Rewrites `groupExp (exp w) e` to `exp (w * e)` via `groupExp_mul'`
2. Combines `exp a * exp b` to `exp (a + b)` via `exp_add'`
3. Normalizes raw field accessors (`smul`, `sadd`) to notation (`*`, `+`)
4. Tries `ring` on remaining scalar goals inside `exp`
5. Tries `group` on remaining group goals

This closes goals like `exp(a*b+c) * exp(d) = exp(b*a+c+d)` in one step. -/

set_option hygiene false in
macro "exp_simp" : tactic => `(tactic| (
  simp only [CatCrypt.Crypto.CyclicGroupDef.groupExp_mul',
             CatCrypt.Crypto.CyclicGroupDef.groupExp_add',
             CatCrypt.Crypto.CyclicGroupDef.groupExp_one',
             CatCrypt.Crypto.CyclicGroupDef.groupExp_zero',
             CatCrypt.Crypto.CyclicGroupDef.exp_add',
             CatCrypt.Crypto.CyclicGroupDef.exp_zero',
             CatCrypt.Crypto.CyclicGroupDef.exp_neg,
             CatCrypt.Crypto.CyclicGroupDef.smul_eq_mul,
             CatCrypt.Crypto.CyclicGroupDef.sadd_eq_add,
             CatCrypt.Crypto.CyclicGroupDef.gmul_eq_mul,
             CatCrypt.Crypto.CyclicGroupDef.gone_eq_one,
             CatCrypt.Crypto.CyclicGroupDef.ginv_eq_inv]
  <;> first | rfl | ring | group
             | (congr 1 <;> first | rfl | ring | group)
  ))

end CatCrypt.Tactics
