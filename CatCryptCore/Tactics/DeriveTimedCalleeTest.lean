/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveTimed
public import CatCryptCore.Crypto.SPCompPMF
public import CatCryptCore.Tactics.AutoTime

/-!
# Tests for `derive_timed`: extra arguments of a local function and a `match` under a binder

Two reductions in the shapes of the ChaCha20-Poly1305 single-query adversary and of the
decapsulation program of the KEM combiner's PRF reduction:

* `oneQuery` asks one query and on an answer `some o` samples `outBool D o`, which unfolds to
  `D o Heap.empty`: the local function `D : X → SPComp Bool` is applied to two arguments,
  one more than its cost companion `DCost : X → ℕ` takes, since `SPComp Bool` is a function
  of the heap under a non-reducible name. The call costs one plus `DCost o`, and the
  application of its result, a table, to the heap costs one.
* `optProg` binds a tree to a continuation `fun o => match o with …` on an `Option`; the
  erasure theorem rewrites the erasure of the costed `match` under the binder by the erasure
  lemma of its matcher.

For each, `derive_timed` defines the costed form and proves the erasure theorem, pinned by an
`example`, and `time_bound` proves a time theorem.

## Main results

* the time theorems of `oneQuery` and `optProg`, each by `time_bound`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveTimedCalleeTest

open CatCrypt.Core CatCrypt.Crypto

/-! ## A local function applied to more arguments than its companion takes -/

/-- Ask `q`; on an answer `some o`, output the bit `outBool D o`; on `none`, output `false`. -/
noncomputable def oneQuery (q : ℕ) (D : ℕ × Bool → SPComp Bool) :
    OracleAdv ℕ (Option (ℕ × Bool)) Bool :=
  .query q fun ans => match ans with
    | some o => .rand (outBool D o) .ret
    | none => .ret false

derive_timed oneQuery

example (q : ℕ) (D : ℕ × Bool → SPComp Bool) (DCost : ℕ × Bool → ℕ) :
    (oneQuery.timed q D DCost).2.erase = oneQuery q D :=
  oneQuery.erase_timed q D DCost

/-- A distinguisher of cost companion at most `a`: the costed form takes at most
`2 * a + 16` steps. -/
theorem oneQuery.timeBound_timed (q : ℕ) (D : ℕ × Bool → SPComp Bool)
    {DCost : ℕ × Bool → ℕ} {a : ℕ} (hD : ∀ o, DCost o ≤ a) :
    OracleAdv.Timed.StepTimeBound (oneQuery.timed q D DCost) (2 * a + 16) := by
  time_bound

/-! ## A `match` on an `Option` under a bind -/

/-- On the challenge `cstar` return `none`; otherwise run `dec c` and, on a key `some k`,
query `(k, c)` and return the answer. -/
noncomputable def optProg (dec : ℕ → OracleAdv (ℕ ⊕ (ℕ × ℕ)) ℕ (Option ℕ)) (cstar c : ℕ) :
    OracleAdv (ℕ ⊕ (ℕ × ℕ)) ℕ (Option ℕ) :=
  if c = cstar then .ret none else
    (dec c).bind fun o => match o with
      | none => .ret none
      | some k => .query (.inr (k, c)) fun a => .ret (some a)

derive_timed optProg

example (dec : ℕ → OracleAdv.Timed (ℕ ⊕ (ℕ × ℕ)) ℕ (Option ℕ)) (decCost : ℕ → ℕ)
    (cstar c : ℕ) :
    (optProg.timed dec decCost cstar c).2.erase = optProg (fun x => (dec x).erase) cstar c :=
  optProg.erase_timed dec decCost cstar c

/-- A decapsulation of time at most `T` and cost companion at most `a`: the costed form
takes at most `T + a + 6` steps. -/
theorem optProg.timeBound_timed (dec : ℕ → OracleAdv.Timed (ℕ ⊕ (ℕ × ℕ)) ℕ (Option ℕ))
    {decCost : ℕ → ℕ} {T a : ℕ} (hdec : ∀ c, (dec c).TimeBound T) (hC : ∀ c, decCost c ≤ a)
    (cstar c : ℕ) :
    OracleAdv.Timed.StepTimeBound (optProg.timed dec decCost cstar c) (T + a + 6) := by
  time_bound

end CatCrypt.Tactics.DeriveTimedCalleeTest
