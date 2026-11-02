/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Crypto.UCTransparentMultiTimed
public import CatCryptCore.Crypto.FiatShamirROM.NIZK

/-!
# Fixtures for rules of `derive_reduction`

`rSim` has a state holding a function and a table type over a structure value `B.gp` with a type
field, a function field and a proof field, and an output type stated by a type abbreviation over
the structure value. No module imports this file.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveWaveBTest

open CatCrypt.Core CatCrypt.Crypto
open CatCrypt.Crypto.UCTransparent (MultiHybrid)

/-- A protocol: a type field, a function field and a proof field. -/
structure GP : Type 1 where
  /-- The signatures. -/
  Sig : Type
  /-- The key function. -/
  key : ℕ → ℕ
  /-- The law of the key function. -/
  key_eq : ∀ n, key n = key n

/-- A table of a protocol. -/
structure GP.Tab (G : GP) : Type where
  /-- The entries. -/
  l : List G.Sig

/-- The answer of a protocol. -/
abbrev GP.Answer (G : GP) := ℕ ⊕ Option G.Sig

/-- The output of a step, stated by an abbreviation. -/
abbrev Zk (A : Type) : Type := Option ℕ × Option A

/-- The data of a protocol. -/
structure Base : Type 1 where
  /-- The signatures. -/
  Sg : Type
  /-- The key function. -/
  k : ℕ → ℕ

/-- The protocol of the data. -/
@[reducible] def Base.gp (B : Base) (_u : Unit) : GP where
  Sig := B.Sg
  key := B.k
  key_eq _ := rfl

/-- The first part of a step. -/
noncomputable def finishStep (s : (ℕ → ℕ) × ℕ) (o : Option ℕ) :
    SPComp (((ℕ → ℕ) × ℕ) × Option ℕ) :=
  match o with
  | none => SPComp.pure (s, none)
  | some v => SPComp.pure ((fun n => s.1 n + v, s.2), some v)

/-- The second part of a step. -/
noncomputable def prove (B : Base) (u : Unit) (tab : (B.gp u).Tab) (vs : Option ℕ)
    (o : Option ℕ) : SPComp ((B.gp u).Tab × Zk (B.gp u).Answer) :=
  match vs, o with
  | some v, some _ => SPComp.bind (SPComp.sample Bool) fun b =>
      SPComp.pure (tab, (o, if b then some (Sum.inl v) else none))
  | _, _ => SPComp.pure (tab, (o, none))

/-- The first part of a step does not fail. -/
theorem finishStep_noFail (s : (ℕ → ℕ) × ℕ) (o : Option ℕ) : SPComp.NoFail (finishStep s o) := by
  unfold finishStep; split <;> exact SPComp.pure_noFail _

/-- The second part of a step does not fail. -/
theorem prove_noFail (B : Base) (u : Unit) (t : (B.gp u).Tab) (v o : Option ℕ) :
    SPComp.NoFail (prove B u t v o) := by
  unfold prove
  split
  · exact Assumptions.SPComp.bind_noFail Assumptions.SPComp.sample_noFail fun _ =>
      SPComp.pure_noFail _
  · exact SPComp.pure_noFail _

/-- A hybrid machine over the protocol of the data. -/
noncomputable def rSim (B : Base) (u : Unit) :
    MultiHybrid (((ℕ → ℕ) × ℕ) × (B.gp u).Tab) ℕ (Zk (B.gp u).Answer) ℕ (Option ℕ × Option ℕ) where
  init := ((fun _ => 0, 0), ⟨[]⟩)
  fuel := 0
  start s e := SPComp.pure (s, .inl e)
  resume s o := SPComp.bind (finishStep s.1 o.1) fun r =>
    SPComp.map (fun q => ((r.1, q.1), .inr q.2)) (prove B u s.2 o.2 r.2)
  finish s o := SPComp.bind (finishStep s.1 o.1) fun r =>
    SPComp.map (fun q => ((r.1, q.1), q.2)) (prove B u s.2 o.2 r.2)
  start_noFail _ _ := SPComp.pure_noFail _
  resume_noFail _ _ := Assumptions.SPComp.bind_noFail (finishStep_noFail _ _) fun _ =>
    Assumptions.SPComp.bind_noFail (prove_noFail _ _ _ _ _) fun _ => SPComp.pure_noFail _
  finish_noFail _ _ := Assumptions.SPComp.bind_noFail (finishStep_noFail _ _) fun _ =>
    Assumptions.SPComp.bind_noFail (prove_noFail _ _ _ _ _) fun _ => SPComp.pure_noFail _

derive_reduction rSim

open CatCrypt.Crypto.FiatShamirROM in
/-- The second part of a step over the NIZK protocol. -/
noncomputable def prove2 (P : Sigma) (Sid : Type) [DecidableEq Sid] [DecidableEq P.Stmt]
    (tab : (P.nizkProtocol Sid).Tables × Bool) (vs : Option ℕ) (o : Option ℕ) :
    SPComp (((P.nizkProtocol Sid).Tables × Bool) × Zk (P.nizkProtocol Sid).Answer) :=
  match vs, o with
  | some _, some _ => SPComp.bind (SPComp.sample Bool) fun _ => SPComp.pure (tab, (o, none))
  | _, _ => SPComp.pure (tab, (o, none))

open CatCrypt.Crypto.FiatShamirROM in
/-- The second part of a step over the NIZK protocol does not fail. -/
theorem prove2_noFail (P : Sigma) (Sid : Type) [DecidableEq Sid] [DecidableEq P.Stmt]
    (t : (P.nizkProtocol Sid).Tables × Bool) (v o : Option ℕ) :
    SPComp.NoFail (prove2 P Sid t v o) := by
  unfold prove2
  split
  · exact Assumptions.SPComp.bind_noFail Assumptions.SPComp.sample_noFail fun _ =>
      SPComp.pure_noFail _
  · exact SPComp.pure_noFail _

open CatCrypt.Crypto.FiatShamirROM in
/-- A hybrid machine with the tables of the NIZK protocol in its state. -/
noncomputable def rSim2 (P : Sigma) (Sid : Type) [DecidableEq Sid] [DecidableEq P.Stmt] :
    MultiHybrid (((ℕ → ℕ) × ℕ) × ((P.nizkProtocol Sid).Tables × Bool)) ℕ
      (Zk (P.nizkProtocol Sid).Answer) ℕ (Option ℕ × Option ℕ) where
  init := ((fun _ => 0, 0), (Protocol.Tables.empty, false))
  fuel := 0
  start s e := SPComp.pure (s, .inl e)
  resume s o := SPComp.bind (finishStep s.1 o.1) fun r =>
    SPComp.map (fun q => ((r.1, q.1), .inr q.2)) (prove2 P Sid s.2 o.2 r.2)
  finish s o := SPComp.bind (finishStep s.1 o.1) fun r =>
    SPComp.map (fun q => ((r.1, q.1), q.2)) (prove2 P Sid s.2 o.2 r.2)
  start_noFail _ _ := SPComp.pure_noFail _
  resume_noFail _ _ := Assumptions.SPComp.bind_noFail (finishStep_noFail _ _) fun _ =>
    Assumptions.SPComp.bind_noFail (prove2_noFail _ _ _ _ _) fun _ => SPComp.pure_noFail _
  finish_noFail _ _ := Assumptions.SPComp.bind_noFail (finishStep_noFail _ _) fun _ =>
    Assumptions.SPComp.bind_noFail (prove2_noFail _ _ _ _ _) fun _ => SPComp.pure_noFail _

derive_reduction rSim2

end CatCrypt.Tactics.DeriveWaveBTest
