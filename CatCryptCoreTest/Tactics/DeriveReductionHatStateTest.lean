/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Crypto.UCTransparentMultiTimed

/-!
# Tests of `derive_reduction` on a hybrid machine with a costed state

`miniSim` is a reduction into `MultiHybrid` whose state `MiniSt` has a table field
`ℕ → List ℕ`. `derive_reduction` gives its costed form at the costed state
`((ℕ → List ℕ) × (ℕ → ℕ)) × ℕ`, in which the step fields take and return the table with its cost
companion, and the erasure relation `MultiHybrid.Timed.ErasesHat` through the erasure of the
state. `phaseSim` has the state `ℕ × Phase`, with `Phase` an inductive type two of whose
constructors store a function; its costed state is `ℕ × (Unit ⊕ (P̂ ⊕ (P̂ ⊕ Unit)))` with
`P̂ = (ℕ → ℕ) × (ℕ → ℕ)`, and its steps match on the phase `t.2` and apply the stored function.
`kitSim` uses a structure value `kitOf G` with a proof field stated over the function field
`G.pub` of its binder. `lawSim` passes the structure value `lawKitOf G`, whose proof field is the
proof field `G.pub_inv` of its binder, to the definition `LawKit.trip`, and applies `G.pub`
directly: the consumer is unfolded and the projections of the value are reduced to its fields.
No module imports this file.

## Main results

* `miniSim.timed` and `miniSim.erase_timed`, emitted by `derive_reduction`; the relation
  `MultiHybrid.Timed.ErasesHat` is generated in `CatCryptCore.Crypto.UCTransparentMultiTimed`
* `phaseSim.timed`, `phaseSim.erase_timed`, `kitSim.timed` and `kitSim.erase_timed`
* `lawSim.timed` and `lawSim.erase_timed`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveReductionHatStateTest

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

/-- The costed form is a hybrid machine at the costed state. -/
noncomputable example (A : ℕ → SPComp ℕ) (ACost : ℕ → ℕ) (hA : ∀ n, SPComp.NoFail (A n))
    (A' : ℕ → SPTree.Timed ℕ) (ACost' : ℕ → ℕ) :
    MultiHybrid.Timed (((ℕ → List ℕ) × (ℕ → ℕ)) × ℕ) ℕ ℕ ℕ ℕ :=
  miniSim.timed A ACost hA A' ACost'

/-- The erasure relation through the erasure of the state. -/
example (A : ℕ → SPComp ℕ) (hA : ∀ n, SPComp.NoFail (A n)) (ACost : ℕ → ℕ)
    (A' : ℕ → SPTree.Timed ℕ) (ACost' : ℕ → ℕ) (h : ∀ a, (A' a).erase.compile = A a) :
    MultiHybrid.Timed.ErasesHat (((ℕ → List ℕ) × (ℕ → ℕ)) × ℕ) ℕ ℕ ℕ ℕ
      (fun y => ⟨y.1.1, y.2⟩) id id id id (miniSim.timed A ACost hA A' ACost') (miniSim A hA) :=
  miniSim.erase_timed A hA ACost A' ACost' h

/-! ## A state with a phase that stores a function -/

/-- The phase of a machine within an activation; two constructors store a completion `r`. -/
inductive Phase where
  /-- Between activations. -/
  | idle
  /-- A completion was stored. -/
  | sub (r : ℕ → ℕ)
  /-- The stored completion was applied once. -/
  | peek (r : ℕ → ℕ)
  /-- The activation is over. -/
  | done

/-- A hybrid machine whose state holds a phase: `start` stores the closure `fun n => n + a`,
and `resume` and `finish` match on the phase `t.2` and apply the stored completion. -/
noncomputable def phaseSim (A : ℕ → SPComp ℕ) (hA : ∀ n, SPComp.NoFail (A n)) :
    MultiHybrid (ℕ × Phase) ℕ ℕ ℕ ℕ where
  init := (0, .idle)
  fuel := 1
  start t e := SPComp.bind (A e) fun a =>
    SPComp.pure ((t.1 + 1, .sub fun n => n + a), .inl a)
  resume t o :=
    match t.2 with
    | .sub r => SPComp.pure ((t.1, .peek r), .inr (r o))
    | .peek r => SPComp.pure ((t.1, .done), .inr (r o + 1))
    | _ => SPComp.pure ((t.1, .idle), .inr o)
  finish t o :=
    match t.2 with
    | .peek r => SPComp.pure ((t.1, .idle), r o)
    | _ => SPComp.pure ((t.1, .idle), o)
  start_noFail _ e := Assumptions.SPComp.bind_noFail (hA e) fun _ => SPComp.pure_noFail _
  resume_noFail t _ := by split <;> exact SPComp.pure_noFail _
  finish_noFail t _ := by split <;> exact SPComp.pure_noFail _

derive_reduction phaseSim

/-- The costed form is a hybrid machine at the costed state, in which the phase is the sum of
the costed tuples of the fields of its constructors. -/
noncomputable example (A : ℕ → SPComp ℕ) (ACost : ℕ → ℕ) (hA : ∀ n, SPComp.NoFail (A n))
    (A' : ℕ → SPTree.Timed ℕ) (ACost' : ℕ → ℕ) :
    MultiHybrid.Timed
      (ℕ × (Unit ⊕ (((ℕ → ℕ) × (ℕ → ℕ)) ⊕ (((ℕ → ℕ) × (ℕ → ℕ)) ⊕ Unit)))) ℕ ℕ ℕ ℕ :=
  phaseSim.timed A ACost hA A' ACost'

/-- The erasure relation through the erasure of the state. -/
example (A : ℕ → SPComp ℕ) (hA : ∀ n, SPComp.NoFail (A n)) (ACost : ℕ → ℕ)
    (A' : ℕ → SPTree.Timed ℕ) (ACost' : ℕ → ℕ) (h : ∀ a, (A' a).erase.compile = A a) :=
  phaseSim.erase_timed A hA ACost A' ACost' h

/-! ## A structure value with a proof field -/

/-- A pair of functions with a law relating them. -/
structure Kit where
  /-- The first function. -/
  f : ℕ → ℕ
  /-- The second function. -/
  g : ℕ → ℕ
  /-- The two functions commute. -/
  f_g : ∀ n, f (g n) = g (f n)

/-- A binder structure with a function field. -/
structure Grp where
  /-- The public map. -/
  pub : ℕ → ℕ

/-- The kit of `G`: its public map twice. -/
def kitOf (G : Grp) : Kit := ⟨G.pub, G.pub, fun _ => rfl⟩

/-- A hybrid machine that applies the public map of `G` and, in a match, the kit of `G`, whose
proof field is stated over the public map. -/
noncomputable def kitSim (G : Grp) (A : ℕ → SPComp ℕ) (hA : ∀ n, SPComp.NoFail (A n)) :
    MultiHybrid ℕ ℕ ℕ ℕ ℕ where
  init := 0
  fuel := 0
  start s e := SPComp.bind (A e) fun a =>
    match a with
    | 0 => SPComp.pure (s, .inr (G.pub e))
    | n + 1 => SPComp.pure (s, .inr ((kitOf G).f n))
  resume s o := SPComp.pure (s, .inr o)
  finish s o := SPComp.pure (s, o)
  start_noFail _ e := Assumptions.SPComp.bind_noFail (hA e) fun _ => by
    split <;> exact SPComp.pure_noFail _
  resume_noFail _ _ := SPComp.pure_noFail _
  finish_noFail _ _ := SPComp.pure_noFail _

derive_reduction kitSim

/-! ## A structure value whose proof field is a proof field of the binder -/

/-- A pair of maps with a law. -/
structure LawKit where
  /-- The first map. -/
  f : ℕ → ℕ
  /-- The second map. -/
  g : ℕ → ℕ
  /-- The first map inverts the second. -/
  f_g : ∀ n, f (g n) = n

/-- A binder structure with two maps and a law. -/
structure LawGrp where
  /-- The public map. -/
  pub : ℕ → ℕ
  /-- Its inverse. -/
  inv : ℕ → ℕ
  /-- The public map inverts the inverse. -/
  pub_inv : ∀ n, pub (inv n) = n

/-- The kit of `G`, whose law is the law of `G`. -/
def lawKitOf (G : LawGrp) : LawKit := ⟨G.pub, G.inv, G.pub_inv⟩

/-- The round trip of a kit. -/
def LawKit.trip (k : LawKit) (n : ℕ) : ℕ := k.f (k.g n)

/-- A hybrid machine that passes the kit of `G` to `LawKit.trip` and applies the public map of
`G`. -/
noncomputable def lawSim (G : LawGrp) (A : ℕ → SPComp ℕ) (hA : ∀ n, SPComp.NoFail (A n)) :
    MultiHybrid ℕ ℕ ℕ ℕ ℕ where
  init := 0
  fuel := 0
  start s e := SPComp.bind (A e) fun a => SPComp.pure (s, .inr (G.pub ((lawKitOf G).trip a)))
  resume s o := SPComp.pure (s, .inr o)
  finish s o := SPComp.pure (s, o)
  start_noFail _ e := Assumptions.SPComp.bind_noFail (hA e) fun _ => SPComp.pure_noFail _
  resume_noFail _ _ := SPComp.pure_noFail _
  finish_noFail _ _ := SPComp.pure_noFail _

derive_reduction lawSim

end CatCrypt.Tactics.DeriveReductionHatStateTest
