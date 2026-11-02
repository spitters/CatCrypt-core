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
`seedSim` draws a structure of functions and keeps it in its state; the erasure theorem of the
case without seed is the right unit law of the bind up to structure eta. `tdSim` matches on an
optional function in the first component of its state, and its costed form matches on the
erasure of the costed value; the case hypotheses of the two matches are reduced into each
other and the rebuilt state closes by structure eta.
No module imports this file.

## Main results

* `miniSim.timed` and `miniSim.erase_timed`, emitted by `derive_reduction`; the relation
  `MultiHybrid.Timed.ErasesHat` is generated in `CatCryptCore.Crypto.UCTransparentMultiTimed`
* `phaseSim.timed`, `phaseSim.erase_timed`, `kitSim.timed` and `kitSim.erase_timed`
* `lawSim.timed` and `lawSim.erase_timed`
* `seedSim.timed`, `seedSim.erase_timed`, `tdSim.timed` and `tdSim.erase_timed`
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

/-! ## A drawn structure of functions kept in the state -/

/-- A seed of two functions. -/
structure FnSeed where
  /-- The first function. -/
  f : ℕ → ℕ
  /-- The second function. -/
  g : ℕ → ℕ

/-- The seed of a state: the seed drawn from `c` for a state without seed. -/
noncomputable def seedPick (c : SPComp FnSeed) (s : Option FnSeed × ℕ) : SPComp FnSeed :=
  match s.1 with
  | none => c
  | some ω => SPComp.pure ω

/-- `seedPick` does not fail when `c` does not. -/
theorem seedPick_noFail (c : SPComp FnSeed) (hc : SPComp.NoFail c) (s : Option FnSeed × ℕ) :
    SPComp.NoFail (seedPick c s) := by
  unfold seedPick; split
  · exact hc
  · exact SPComp.pure_noFail _

/-- A hybrid machine that draws a seed of functions at its first activation and keeps it: the
costed form rebuilds the drawn seed field by field, and the erasure theorem of the case without
seed is the right unit law of the bind up to structure eta. -/
noncomputable def seedSim (c : SPComp FnSeed) (hc : SPComp.NoFail c) :
    MultiHybrid (Option FnSeed × ℕ) ℕ ℕ ℕ ℕ where
  init := (none, 0)
  fuel := 0
  start s e := SPComp.bind (seedPick c s) fun ω =>
    SPComp.pure ((some ω, s.2 + 1), .inr (ω.f e))
  resume s o := SPComp.pure (s, .inr o)
  finish s o := SPComp.pure (s, o)
  start_noFail s _ := Assumptions.SPComp.bind_noFail (seedPick_noFail c hc s) fun _ =>
    SPComp.pure_noFail _
  resume_noFail _ _ := SPComp.pure_noFail _
  finish_noFail _ _ := SPComp.pure_noFail _

derive_reduction seedSim

/-! ## A match on an optional function in a projection of the state -/

/-- A state with an optional table, sampled on first use, and a table with a counter. -/
structure TdCore where
  /-- The optional table. -/
  td : Option (Bool → Bool)
  /-- A second table. -/
  tab : Bool → ℕ
  /-- A counter. -/
  cnt : ℕ

/-- The table of `c`, sampled and stored when absent. -/
noncomputable def tdPick (c : TdCore) : SPComp ((Bool → Bool) × TdCore) :=
  match c.td with
  | some td => SPComp.pure (td, c)
  | none => SPComp.bind (SPComp.sample (Bool → Bool)) fun td =>
      SPComp.pure (td, { c with td := some td })

/-- `tdPick` does not fail. -/
theorem tdPick_noFail (c : TdCore) : SPComp.NoFail (tdPick c) := by
  unfold tdPick; split
  · exact SPComp.pure_noFail _
  · exact Assumptions.SPComp.bind_noFail Assumptions.SPComp.sample_noFail fun _ =>
      SPComp.pure_noFail _

/-- The table of `c` applied at the test of the second table at `e`. -/
noncomputable def tdCore (c : TdCore) (e : Bool) : SPComp (TdCore × Bool) :=
  SPComp.bind (tdPick c) fun p => SPComp.pure (p.2, p.1 (decide (p.2.tab e = 0)))

/-- `tdCore` does not fail. -/
theorem tdCore_noFail (c : TdCore) (e : Bool) : SPComp.NoFail (tdCore c e) :=
  Assumptions.SPComp.bind_noFail (tdPick_noFail c) fun _ => SPComp.pure_noFail _

/-- A hybrid machine that answers from a log or from `tdCore` on the first component of its
state: in the costed form the match on the optional table is a match on the erasure of its
costed value, whose case hypothesis is reduced by the case hypothesis of the source match, and
the rebuilt state is the state by structure eta. -/
noncomputable def tdSim : MultiHybrid (TdCore × List (Bool × Bool)) Bool Bool Bool Bool where
  init := (⟨none, fun _ => 0, 0⟩, [])
  fuel := 0
  start s e := match s.2.lookup e with
    | some b => SPComp.pure (s, .inr b)
    | none => SPComp.map (fun q => ((q.1, (e, q.2) :: s.2), .inr q.2)) (tdCore s.1 e)
  resume s o := SPComp.pure (s, .inr o)
  finish s o := SPComp.pure (s, o)
  start_noFail s e := by
    split
    · exact SPComp.pure_noFail _
    · exact Assumptions.SPComp.bind_noFail (tdCore_noFail s.1 e) fun _ => SPComp.pure_noFail _
  resume_noFail _ _ := SPComp.pure_noFail _
  finish_noFail _ _ := SPComp.pure_noFail _

derive_reduction tdSim

end CatCrypt.Tactics.DeriveReductionHatStateTest
