/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Crypto.UCTransparentMultiTimed

/-!
# Tests of `derive_reduction`: the attempts of a structure-valued reduction

`miniSim` is the hybrid machine of `CatCryptCore.Tactics.DeriveReductionHatStateTest`, whose
state has a table field: `derive_reduction` derives it with the costed state, as the attempt
after the plain interface fails. No module imports this file.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveReductionAttemptTest

open CatCrypt.Core CatCrypt.Crypto
open CatCrypt.Crypto.UCTransparent (MultiHybrid)

/-- A state with a table and a counter. -/
structure MiniSt where
  /-- The table. -/
  tab : ℕ → List ℕ
  /-- The counter. -/
  cnt : ℕ

/-- A hybrid machine that records the adversary's answer at the event in its table, forwards
the answer, and reads the table on the subroutine's answer. -/
noncomputable def miniSim (A : ℕ → SPComp ℕ) (hA : ∀ n, SPComp.NoFail (A n)) :
    MultiHybrid MiniSt ℕ ℕ ℕ ℕ where
  init := ⟨fun _ => [], 0⟩
  fuel := 0
  start s e := SPComp.bind (A e) fun a =>
    SPComp.pure (⟨fun n => if n = e then a :: s.tab n else s.tab n, s.cnt + 1⟩, .inl a)
  resume s o := SPComp.pure (s, .inr (o + (s.tab o).length))
  finish s o := SPComp.pure (s, (s.tab o).length + s.cnt)
  start_noFail _ e := Assumptions.SPComp.bind_noFail (hA e) fun _ => SPComp.pure_noFail _
  resume_noFail _ _ := SPComp.pure_noFail _
  finish_noFail _ _ := SPComp.pure_noFail _

derive_reduction miniSim

/-- The erasure relation through the erasure of the state. -/
example (A : ℕ → SPComp ℕ) (hA : ∀ n, SPComp.NoFail (A n)) (ACost : ℕ → ℕ)
    (A' : ℕ → SPTree.Timed ℕ) (ACost' : ℕ → ℕ) (h : ∀ a, (A' a).erase.compile = A a) :
    MultiHybrid.Timed.ErasesHat (((ℕ → List ℕ) × (ℕ → ℕ)) × ℕ) ℕ ℕ ℕ ℕ
      (fun y => ⟨y.1.1, y.2⟩) id id id id (miniSim.timed A ACost hA A' ACost') (miniSim A hA) :=
  miniSim.erase_timed A hA ACost A' ACost' h

end CatCrypt.Tactics.DeriveReductionAttemptTest
