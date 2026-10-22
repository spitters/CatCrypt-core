/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Core.Code

/-!
# Dead uniform samples

A uniform sample whose result is not used can be removed: `SDistr.uniform α` has mass one, so
binding it to a constant continuation gives the continuation.

## Main results

* `CatCrypt.Relational.dead_sample` — `(SPComp.sample α).bind (fun _ => k) = k`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Relational

open CatCrypt.Core CatCrypt.Prob

/-- Dead sample: a uniform sample whose result is not used can be removed,
    `let _ ← sample α; k` = `k`. -/
@[simp] theorem dead_sample {α β : Type} [Fintype α] [Nonempty α] (k : SPComp β) :
    (SPComp.sample α).bind (fun _ => k) = k := by
  funext h
  simp only [SPComp.bind_def, SPComp.sample]
  rw [SDistr.bind_assoc]
  simp only [SDistr.pure_bind]
  exact SDistr.uniform_bind_const (k h)

end CatCrypt.Relational
