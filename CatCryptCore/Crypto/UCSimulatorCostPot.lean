/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCSimulatorCostSized

/-!
# Potential time bounds of costed simulators

Canetti's revised UC framework measures the running time of an interactive machine against its
import: the total import of the inputs it has received less the import it has passed on with
the inputs it wrote [Canetti, *Universally Composable Security*, J. ACM 67(5), 2020]. The
potential time bound `MultiHybrid.Timed.PotentialBound A gE gO hEG hO a b` states this notion
for a costed multi-call simulator with a potential `Φ` on its states: the import `gE` of an outer
event and `gO` of an answer received, the import `hEG` of an inner event and `hO` of an outer
output passed on, and an invariant `Inv` on the states. A step on the input `x` from a state `s`
of `Inv` costs at most `a + b * (Φ s + g x)`, and every state `s'` it returns with the output `y`
satisfies `Inv` and `Φ s' + h y ≤ Φ s + g x`. At `h = 0` the potential clause is
`Φ s' ≤ Φ s + g x` (`MultiHybrid.Timed.PotentialBound.ofZero`).

Sizes of messages are given by the class `ImportSize` (every message has size at least `1`),
and the import measures are linear in the size when `ImportLinear gE gO c` holds. A run of `k`
activations receiving the imports `m j` costs at most `k * a + b * k * (Φ₀ + ∑ m j)`
(`MultiHybrid.Timed.PotentialBound.actRun_le`). The invariant, graded and size-graded time
bounds are potential time bounds, with the potential `0` and the least activation count.

## Main definitions

* `ImportSize`, `ImportLinear`: sizes of messages, and import measures linear in the size.
* `MultiHybrid.Timed.PotentialBound`: the potential time bound of a costed multi-call simulator.
* `MultiHybrid.Timed.PotentialBound.ofZero`: the potential time bound from the clause
  `Φ s' ≤ Φ s + g x`.
* `MultiHybrid.Timed.PotentialBound.tensor`: the potential time bound of the costed tensor, with
  the sum of the potentials.
* `MultiHybrid.Timed.TimeBoundInv.potentialBound`,
  `MultiHybrid.Timed.TimeBoundGraded.potentialBound`,
  `MultiHybrid.Timed.TimeBoundSized.potentialBound`: the potential time bounds of the
  invariant, graded and size-graded time bounds.

## Main results

* `MultiHybrid.Timed.PotentialBound.act_le`: the time and the potential clause of an activation.
* `MultiHybrid.Timed.PotentialBound.actRun_le`,
  `MultiHybrid.Timed.PotentialBound.actRun_le_of_importLinear`: the time of a run of
  activations.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core

/-- The size of the messages of type `X`, as counted by the import of Canetti's notion of
polynomial time: every message has size at least `1`. -/
class ImportSize (X : Type) where
  /-- The size of a message. -/
  size : X → ℕ
  /-- Every message has size at least `1`. -/
  one_le : ∀ x, 1 ≤ size x

namespace ImportSize

/-- A natural number has the size `1 + n`: a declared number is counted in unary. -/
instance instNat : ImportSize ℕ := ⟨fun n => 1 + n, fun _ => Nat.le_add_right 1 _⟩

/-- The unit message has size `1`. -/
instance instUnit : ImportSize Unit := ⟨fun _ => 1, fun _ => le_rfl⟩

/-- A boolean has size `1`. -/
instance instBool : ImportSize Bool := ⟨fun _ => 1, fun _ => le_rfl⟩

/-- A pair has the size `1` plus the sizes of its components. -/
instance instProd {X Y : Type} [ImportSize X] [ImportSize Y] : ImportSize (X × Y) :=
  ⟨fun p => 1 + size p.1 + size p.2, fun _ => by omega⟩

/-- A message of a sum has the size `1` plus the size of its part. -/
instance instSum {X Y : Type} [ImportSize X] [ImportSize Y] : ImportSize (X ⊕ Y) :=
  ⟨Sum.elim (fun x => 1 + size x) (fun y => 1 + size y), fun p => by cases p <;> simp⟩

/-- An option has the size `1` plus the size of its present part. -/
instance instOption {X : Type} [ImportSize X] : ImportSize (Option X) :=
  ⟨fun o => 1 + o.elim 0 size, fun _ => Nat.le_add_right 1 _⟩

/-- A list has the size `1` plus the sizes of its elements. -/
instance instList {X : Type} [ImportSize X] : ImportSize (List X) :=
  ⟨fun l => 1 + (l.map size).sum, fun _ => Nat.le_add_right 1 _⟩

end ImportSize

/-- The import measures `gE` of the outer events and `gO` of the answers are linear in the
size: each is at most `c` times the size of its message. -/
def ImportLinear {E OG : Type} [ImportSize E] [ImportSize OG] (gE : E → ℕ) (gO : OG → ℕ)
    (c : ℕ) : Prop :=
  (∀ e, gE e ≤ c * ImportSize.size e) ∧ ∀ o, gO o ≤ c * ImportSize.size o

/-- The import `1` of every message is linear in the size, with the constant `1`. -/
theorem ImportLinear.one {E OG : Type} [ImportSize E] [ImportSize OG] :
    ImportLinear (1 : E → ℕ) (1 : OG → ℕ) 1 :=
  ⟨fun e => by simpa using ImportSize.one_le e, fun o => by simpa using ImportSize.one_le o⟩

/-- The import `1` plus a size at most `c₀` times the message size is linear in the size, with
the constant `1 + c₀`. -/
theorem ImportLinear.one_add {E OG : Type} [ImportSize E] [ImportSize OG] {sE : E → ℕ}
    {sO : OG → ℕ} {c₀ : ℕ} (hE : ∀ e, sE e ≤ c₀ * ImportSize.size e)
    (hO : ∀ o, sO o ≤ c₀ * ImportSize.size o) :
    ImportLinear (fun e => 1 + sE e) (fun o => 1 + sO o) (1 + c₀) := by
  refine ⟨fun e => ?_, fun o => ?_⟩
  · have := ImportSize.one_le e
    have := hE e
    grind
  · have := ImportSize.one_le o
    have := hO o
    grind

namespace MultiHybrid.Timed

variable {σ E O EG OG : Type}

/-- The potential time bound of a costed multi-call simulator, with the import `gE` of the outer
events and `gO` of the answers it receives, the import `hEG` of the inner events and `hO` of the
outer outputs it passes on, and the constants `a`, `b`: an invariant `Inv` and a potential `Φ`
on the states, with `Inv` at the initial state, such that a `start` step on `e` from a state `s`
of `Inv` costs at most `a + b * (Φ s + gE e)` and returns states `s'` of `Inv` with outputs `y`
where `Φ s' + h y ≤ Φ s + gE e`, and likewise a `resume` or `finish` step on `o` with `gO o`. -/
structure PotentialBound (A : MultiHybrid.Timed σ E O EG OG) (gE : E → ℕ) (gO : OG → ℕ)
    (hEG : EG → ℕ) (hO : O → ℕ) (a b : ℕ) where
  /-- The invariant on the states. -/
  Inv : σ → Prop
  /-- The potential of a state. -/
  Φ : σ → ℕ
  /-- The initial state satisfies the invariant. -/
  init : Inv A.init
  /-- The time and the potential clause of a `start` step. -/
  start : ∀ s e, Inv s →
    SPTree.Timed.stepTime (A.startCost s e, A.start s e) ≤ a + b * (Φ s + gE e) ∧
    SPTree.Timed.AllRet (fun y => Inv y.1 ∧ Φ y.1 + Sum.elim hEG hO y.2 ≤ Φ s + gE e)
      (A.start s e)
  /-- The time and the potential clause of a `resume` step. -/
  resume : ∀ s o, Inv s →
    SPTree.Timed.stepTime (A.resumeCost s o, A.resume s o) ≤ a + b * (Φ s + gO o) ∧
    SPTree.Timed.AllRet (fun y => Inv y.1 ∧ Φ y.1 + Sum.elim hEG hO y.2 ≤ Φ s + gO o)
      (A.resume s o)
  /-- The time and the potential clause of a `finish` step. -/
  finish : ∀ s o, Inv s →
    SPTree.Timed.stepTime (A.finishCost s o, A.finish s o) ≤ a + b * (Φ s + gO o) ∧
    SPTree.Timed.AllRet (fun y => Inv y.1 ∧ Φ y.1 + hO y.2 ≤ Φ s + gO o) (A.finish s o)

variable {A : MultiHybrid.Timed σ E O EG OG} {gE : E → ℕ} {gO : OG → ℕ} {hEG : EG → ℕ}
  {hO : O → ℕ} {a b : ℕ}

namespace PotentialBound

/-- **Activation under a potential time bound**: an activation on `x` from a state `s` of the
invariant costs at most `a + b * (Φ s + g x)`, and returns states `s'` of the invariant with
outputs `y` where `Φ s' + h y ≤ Φ s + g x`. -/
theorem act_le (P : A.PotentialBound gE gO hEG hO a b) {s : σ} (hs : P.Inv s)
    (x : E ⊕ OG ⊕ OG) :
    SPTree.Timed.stepTime (A.act s x) ≤ a + b * (P.Φ s + Sum.elim gE (Sum.elim gO gO) x) ∧
      SPTree.Timed.AllRet (fun y => P.Inv y.1 ∧
        P.Φ y.1 + Sum.elim hEG hO y.2 ≤ P.Φ s + Sum.elim gE (Sum.elim gO gO) x)
        (A.act s x).2 := by
  rcases x with e | o | o
  · exact P.start s e hs
  · exact P.resume s o hs
  · obtain ⟨ht, hr⟩ := P.finish s o hs
    refine ⟨?_, ?_⟩
    · have := SPTree.Timed.stepTime_map_le (fun y : σ × O => (y.1, (Sum.inr y.2 : EG ⊕ O)))
        (fun _ => 0) (A.finish s o) 0 fun _ => le_rfl
      simp only [MultiHybrid.Timed.act, SPTree.Timed.stepTime_delay, Sum.elim_inr] at this ⊢
      simp only [SPTree.Timed.stepTime] at ht
      omega
    · simp only [MultiHybrid.Timed.act, SPTree.Timed.delay, SPTree.Timed.map,
        SPTree.Timed.allRet_bind]
      exact hr

/-- An activation on `x` returns states `s'` with `Φ s' ≤ Φ s + g x`, for every import `h`
passed on. -/
theorem act_pot_le (P : A.PotentialBound gE gO hEG hO a b) {s : σ} (hs : P.Inv s)
    (x : E ⊕ OG ⊕ OG) :
    SPTree.Timed.AllRet (fun y => P.Inv y.1 ∧ P.Φ y.1 ≤ P.Φ s + Sum.elim gE (Sum.elim gO gO) x)
      (A.act s x).2 :=
  SPTree.Timed.allRet_mono (fun _ hy => ⟨hy.1, le_trans (Nat.le_add_right _ _) hy.2⟩) _
    (P.act_le hs x).2

/-- The potential time bound with no import passed on (`h = 0`), from the clause
`Φ s' ≤ Φ s + g x`: an invariant `Inv` and a potential `Φ` such that each step on `x` from a
state `s` of `Inv` costs at most `a + b * (Φ s + g x)` and returns states `s'` of `Inv` with
`Φ s' ≤ Φ s + g x`. -/
def ofZero (Inv : σ → Prop) (Φ : σ → ℕ) (h0 : Inv A.init)
    (hstart : ∀ s e, Inv s →
      SPTree.Timed.stepTime (A.startCost s e, A.start s e) ≤ a + b * (Φ s + gE e) ∧
      SPTree.Timed.AllRet (fun y => Inv y.1 ∧ Φ y.1 ≤ Φ s + gE e) (A.start s e))
    (hresume : ∀ s o, Inv s →
      SPTree.Timed.stepTime (A.resumeCost s o, A.resume s o) ≤ a + b * (Φ s + gO o) ∧
      SPTree.Timed.AllRet (fun y => Inv y.1 ∧ Φ y.1 ≤ Φ s + gO o) (A.resume s o))
    (hfinish : ∀ s o, Inv s →
      SPTree.Timed.stepTime (A.finishCost s o, A.finish s o) ≤ a + b * (Φ s + gO o) ∧
      SPTree.Timed.AllRet (fun y => Inv y.1 ∧ Φ y.1 ≤ Φ s + gO o) (A.finish s o)) :
    A.PotentialBound gE gO 0 0 a b where
  Inv := Inv
  Φ := Φ
  init := h0
  start s e hs := ⟨(hstart s e hs).1, SPTree.Timed.allRet_mono
    (fun y hy => ⟨hy.1, by simpa [Sum.elim_zero_zero] using hy.2⟩) _ (hstart s e hs).2⟩
  resume s o hs := ⟨(hresume s o hs).1, SPTree.Timed.allRet_mono
    (fun y hy => ⟨hy.1, by simpa [Sum.elim_zero_zero] using hy.2⟩) _ (hresume s o hs).2⟩
  finish s o hs := ⟨(hfinish s o hs).1, SPTree.Timed.allRet_mono
    (fun y hy => ⟨hy.1, by simpa using hy.2⟩) _ (hfinish s o hs).2⟩

/-- Under a potential time bound, `n` activations from a state `s` of the invariant with
`Φ s ≤ B`, the `j`-th receiving import at most `m (i + j)`, cost at most
`n * a + b * n * (B + ∑ j < n, m (i + j))`. -/
theorem actRun_le_aux (P : A.PotentialBound gE gO hEG hO a b)
    (next : ℕ → σ → Option (EG ⊕ O) → E ⊕ OG ⊕ OG) (m : ℕ → ℕ)
    (hm : ∀ j s o, Sum.elim gE (Sum.elim gO gO) (next j s o) ≤ m j) (n : ℕ) :
    ∀ (i B : ℕ) (s : σ) (o : Option (EG ⊕ O)), P.Inv s → P.Φ s ≤ B →
      SPTree.Timed.stepTime (A.actRun next i n s o) ≤
        n * a + b * n * (B + ∑ j ∈ Finset.range n, m (i + j)) := by
  induction n with
  | zero =>
    intro i B s o _ _
    simp [MultiHybrid.Timed.actRun, SPTree.Timed.stepTime, SPTree.Timed.time_ret]
  | succ n ih =>
    intro i B s o hs hB
    have hx := P.act_le hs (next i s o)
    have hmi := hm i s o
    have hb := SPTree.Timed.stepTime_bind_le_of_allRet (A.act s (next i s o)).2
      (fun y => A.actRun next (i + 1) n y.1 (some y.2)) _ hx.2
      (fun y hy => ih (i + 1) (B + m i) y.1 (some y.2) hy.1 (by omega))
    have hsum : ∑ j ∈ Finset.range (n + 1), m (i + j) =
        m i + ∑ j ∈ Finset.range n, m (i + 1 + j) := by
      rw [Finset.sum_range_succ', add_comm]
      exact congrArg₂ _ (by simp) (Finset.sum_congr rfl fun j _ => by grind)
    have h1 : b * (P.Φ s + Sum.elim gE (Sum.elim gO gO) (next i s o)) ≤
        b * (B + (m i + ∑ j ∈ Finset.range n, m (i + 1 + j))) :=
      Nat.mul_le_mul_left _ (by omega)
    have h2 : b * (n + 1) * (B + (m i + ∑ j ∈ Finset.range n, m (i + 1 + j))) =
        b * n * (B + m i + ∑ j ∈ Finset.range n, m (i + 1 + j)) +
          b * (B + (m i + ∑ j ∈ Finset.range n, m (i + 1 + j))) := by ring
    simp only [MultiHybrid.Timed.actRun, SPTree.Timed.stepTime_delay, hsum]
    simp only [SPTree.Timed.stepTime] at hx hb ⊢
    rw [h2, Nat.succ_mul]
    omega

/-- **Time of `k` activations under a potential time bound.** If the `j`-th activation of the
schedule `next` receives import at most `m j`, a run of `k` activations from the initial state
costs at most `k * a + b * k * (Φ₀ + ∑ j < k, m j)`, with `Φ₀` the potential of the initial
state. -/
theorem actRun_le (P : A.PotentialBound gE gO hEG hO a b)
    (next : ℕ → σ → Option (EG ⊕ O) → E ⊕ OG ⊕ OG) (m : ℕ → ℕ)
    (hm : ∀ j s o, Sum.elim gE (Sum.elim gO gO) (next j s o) ≤ m j) (k : ℕ)
    (o : Option (EG ⊕ O)) :
    SPTree.Timed.stepTime (A.actRun next 0 k A.init o) ≤
      k * a + b * k * (P.Φ A.init + ∑ j ∈ Finset.range k, m j) := by
  simpa using P.actRun_le_aux next m hm k 0 (P.Φ A.init) A.init o P.init le_rfl

/-- **Time of `k` activations with import linear in the size.** Under `ImportLinear gE gO c`, if
the `j`-th activation of the schedule `next` has a message of size at most `M j`, a run of `k`
activations from the initial state costs at most `k * a + b * k * (Φ₀ + c * ∑ j < k, M j)`. -/
theorem actRun_le_of_importLinear [ImportSize E] [ImportSize OG]
    (P : A.PotentialBound gE gO hEG hO a b) {c : ℕ} (hL : ImportLinear gE gO c)
    (next : ℕ → σ → Option (EG ⊕ O) → E ⊕ OG ⊕ OG) (M : ℕ → ℕ)
    (hM : ∀ j s o, Sum.elim ImportSize.size (Sum.elim ImportSize.size ImportSize.size)
      (next j s o) ≤ M j) (k : ℕ) (o : Option (EG ⊕ O)) :
    SPTree.Timed.stepTime (A.actRun next 0 k A.init o) ≤
      k * a + b * k * (P.Φ A.init + c * ∑ j ∈ Finset.range k, M j) := by
  rw [Finset.mul_sum]
  refine P.actRun_le next (fun j => c * M j) (fun j s o => ?_) k o
  have := hM j s o
  generalize next j s o = x at this ⊢
  rcases x with e | o' | o'
  · exact le_trans (hL.1 e) (Nat.mul_le_mul_left c this)
  · exact le_trans (hL.2 o') (Nat.mul_le_mul_left c this)
  · exact le_trans (hL.2 o') (Nat.mul_le_mul_left c this)

set_option linter.auxLemma false in
/-- **Potential time bound of the costed tensor**: if `πT` and `π'T` have potential time bounds
with constants `a`, `b` and `a'`, `b'`, the costed tensor has the potential time bound with the
imports of the components on the two sides, the constants `max a a' + 7`, `max b b'`, the
conjunction of the invariants and the sum of the potentials. -/
def tensor {σ' E' O' EG' OG' : Type} (π : MultiHybrid σ E O EG OG)
    (π' : MultiHybrid σ' E' O' EG' OG') {πT : MultiHybrid.Timed σ E O EG OG}
    {π'T : MultiHybrid.Timed σ' E' O' EG' OG'} {gE' : E' → ℕ} {gO' : OG' → ℕ}
    {hEG' : EG' → ℕ} {hO' : O' → ℕ} {a' b' : ℕ}
    (hinit : πT.init = π.init) (hinit' : π'T.init = π'.init)
    (P : πT.PotentialBound gE gO hEG hO a b) (P' : π'T.PotentialBound gE' gO' hEG' hO' a' b') :
    (MultiHybrid.Timed.tensor π π' πT π'T).PotentialBound (Sum.elim gE gE') (Sum.elim gO gO')
      (Sum.elim hEG hEG') (Sum.elim hO hO') (max a a' + 7) (max b b') where
  Inv s := P.Inv s.1 ∧ P'.Inv s.2
  Φ s := P.Φ s.1 + P'.Φ s.2
  init := ⟨(show P.Inv π.init from hinit ▸ P.init), (show P'.Inv π'.init from hinit' ▸ P'.init)⟩
  start s e hs := by
    obtain ⟨hs1, hs2⟩ := hs
    rcases e with e | e <;>
      simp only [MultiHybrid.Timed.tensor, MultiHybrid.tensor.timed,
        MultiHybrid.tensor.start.tree.timed, MultiHybrid.tensor.start.tree.match_1.timed,
        Sum.elim_inl, Sum.elim_inr]
    · obtain ⟨ht, hr⟩ := P.start s.1 e hs1
      refine (tensor_step_le _ _ 4 _ _ _ (fun x => ?_) ht hr (fun x hx => ?_)).imp
        (fun h => le_trans h ?_) id
      · rcases x with ⟨_, _ | _⟩ <;> simp
      · rcases x with ⟨_, _ | _⟩ <;>
          simp only [Sum.map_inl, Sum.map_inr, Sum.elim_inl, Sum.elim_inr] at hx ⊢ <;>
          exact ⟨by tauto, by omega⟩
      · have := Nat.mul_le_mul (le_max_left b b')
          (show P.Φ s.1 + gE e ≤ P.Φ s.1 + P'.Φ s.2 + gE e by omega)
        have := le_max_left a a'
        omega
    · obtain ⟨ht, hr⟩ := P'.start s.2 e hs2
      refine (tensor_step_le _ _ 4 _ _ _ (fun x => ?_) ht hr (fun x hx => ?_)).imp
        (fun h => le_trans h ?_) id
      · rcases x with ⟨_, _ | _⟩ <;> simp
      · rcases x with ⟨_, _ | _⟩ <;>
          simp only [Sum.map_inl, Sum.map_inr, Sum.elim_inl, Sum.elim_inr] at hx ⊢ <;>
          exact ⟨by tauto, by omega⟩
      · have := Nat.mul_le_mul (le_max_right b b')
          (show P'.Φ s.2 + gE' e ≤ P.Φ s.1 + P'.Φ s.2 + gE' e by omega)
        have := le_max_right a a'
        omega
  resume s o hs := by
    obtain ⟨hs1, hs2⟩ := hs
    rcases o with o | o <;>
      simp only [MultiHybrid.Timed.tensor, MultiHybrid.tensor.timed,
        MultiHybrid.tensor.resume.tree.timed, MultiHybrid.tensor.resume.tree.match_1.timed,
        Sum.elim_inl, Sum.elim_inr]
    · obtain ⟨ht, hr⟩ := P.resume s.1 o hs1
      refine (tensor_step_le _ _ 4 _ _ _ (fun x => ?_) ht hr (fun x hx => ?_)).imp
        (fun h => le_trans h ?_) id
      · rcases x with ⟨_, _ | _⟩ <;> simp
      · rcases x with ⟨_, _ | _⟩ <;>
          simp only [Sum.map_inl, Sum.map_inr, Sum.elim_inl, Sum.elim_inr] at hx ⊢ <;>
          exact ⟨by tauto, by omega⟩
      · have := Nat.mul_le_mul (le_max_left b b')
          (show P.Φ s.1 + gO o ≤ P.Φ s.1 + P'.Φ s.2 + gO o by omega)
        have := le_max_left a a'
        omega
    · obtain ⟨ht, hr⟩ := P'.resume s.2 o hs2
      refine (tensor_step_le _ _ 4 _ _ _ (fun x => ?_) ht hr (fun x hx => ?_)).imp
        (fun h => le_trans h ?_) id
      · rcases x with ⟨_, _ | _⟩ <;> simp
      · rcases x with ⟨_, _ | _⟩ <;>
          simp only [Sum.map_inl, Sum.map_inr, Sum.elim_inl, Sum.elim_inr] at hx ⊢ <;>
          exact ⟨by tauto, by omega⟩
      · have := Nat.mul_le_mul (le_max_right b b')
          (show P'.Φ s.2 + gO' o ≤ P.Φ s.1 + P'.Φ s.2 + gO' o by omega)
        have := le_max_right a a'
        omega
  finish s o hs := by
    obtain ⟨hs1, hs2⟩ := hs
    rcases o with o | o <;>
      simp only [MultiHybrid.Timed.tensor, MultiHybrid.tensor.timed,
        MultiHybrid.tensor.finish.tree.timed, MultiHybrid.tensor.finish.tree.match_1.timed,
        Sum.elim_inl, Sum.elim_inr]
    · obtain ⟨ht, hr⟩ := P.finish s.1 o hs1
      refine (tensor_step_le _ _ 0 _ _ _ (fun _ => le_rfl) ht hr (fun x hx => ?_)).imp
        (fun h => le_trans h ?_) id
      · simp only [Sum.elim_inl] at hx ⊢
        exact ⟨by tauto, by omega⟩
      · have := Nat.mul_le_mul (le_max_left b b')
          (show P.Φ s.1 + gO o ≤ P.Φ s.1 + P'.Φ s.2 + gO o by omega)
        have := le_max_left a a'
        omega
    · obtain ⟨ht, hr⟩ := P'.finish s.2 o hs2
      refine (tensor_step_le _ _ 0 _ _ _ (fun _ => le_rfl) ht hr (fun x hx => ?_)).imp
        (fun h => le_trans h ?_) id
      · simp only [Sum.elim_inr] at hx ⊢
        exact ⟨by tauto, by omega⟩
      · have := Nat.mul_le_mul (le_max_right b b')
          (show P'.Φ s.2 + gO' o ≤ P.Φ s.1 + P'.Φ s.2 + gO' o by omega)
        have := le_max_right a a'
        omega

/-- The potential time bound of an activation-indexed invariant `Inv` with no import passed on:
if the initial state satisfies `Inv 0`, a step on `x` from a state of `Inv i` costs at most
`a + b * (i + g x)` and returns states of `Inv (i + 1)`, and every import is at least `1`, then
the potential of a state is the least `i` with `Inv i s`. -/
noncomputable def ofIndexed (Inv : ℕ → σ → Prop) (h0 : Inv 0 A.init)
    (hstart : ∀ i s e, Inv i s →
      SPTree.Timed.stepTime (A.startCost s e, A.start s e) ≤ a + b * (i + gE e) ∧
      SPTree.Timed.AllRet (fun y => Inv (i + 1) y.1) (A.start s e))
    (hresume : ∀ i s o, Inv i s →
      SPTree.Timed.stepTime (A.resumeCost s o, A.resume s o) ≤ a + b * (i + gO o) ∧
      SPTree.Timed.AllRet (fun y => Inv (i + 1) y.1) (A.resume s o))
    (hfinish : ∀ i s o, Inv i s →
      SPTree.Timed.stepTime (A.finishCost s o, A.finish s o) ≤ a + b * (i + gO o) ∧
      SPTree.Timed.AllRet (fun y => Inv (i + 1) y.1) (A.finish s o))
    (hE : ∀ e, 1 ≤ gE e) (hO : ∀ o, 1 ≤ gO o) : A.PotentialBound gE gO 0 0 a b :=
  ofZero (fun s => ∃ i, Inv i s) (fun s => sInf {i | Inv i s}) ⟨0, h0⟩
    (fun s e hs => by
      obtain ⟨ht, hr⟩ := hstart _ s e (Nat.sInf_mem hs)
      refine ⟨ht, SPTree.Timed.allRet_mono (fun y hy => ⟨⟨_, hy⟩, ?_⟩) _ hr⟩
      have := Nat.sInf_le (show sInf {i | Inv i s} + 1 ∈ {i | Inv i y.1} from hy)
      have := hE e
      omega)
    (fun s o hs => by
      obtain ⟨ht, hr⟩ := hresume _ s o (Nat.sInf_mem hs)
      refine ⟨ht, SPTree.Timed.allRet_mono (fun y hy => ⟨⟨_, hy⟩, ?_⟩) _ hr⟩
      have := Nat.sInf_le (show sInf {i | Inv i s} + 1 ∈ {i | Inv i y.1} from hy)
      have := hO o
      omega)
    (fun s o hs => by
      obtain ⟨ht, hr⟩ := hfinish _ s o (Nat.sInf_mem hs)
      refine ⟨ht, SPTree.Timed.allRet_mono (fun y hy => ⟨⟨_, hy⟩, ?_⟩) _ hr⟩
      have := Nat.sInf_le (show sInf {i | Inv i s} + 1 ∈ {i | Inv i y.1} from hy)
      have := hO o
      omega)

end PotentialBound

/-- **An invariant time bound is a potential time bound** with no import, the potential `0` and
no growth: its constant is the largest step bound. -/
def TimeBoundInv.potentialBound {Inv : σ → Prop} {a r f : ℕ} (h : A.TimeBoundInv Inv a r f) :
    A.PotentialBound 0 0 0 0 (max a (max r f)) 0 :=
  have hm : ∀ t n, t ≤ max a (max r f) → t ≤ max a (max r f) + 0 * n := fun _ _ ht => by
    rw [Nat.zero_mul, Nat.add_zero]
    exact ht
  PotentialBound.ofZero Inv (fun _ => 0) h.1
    (fun s e hs => ⟨hm _ _ (by have := (h.2.1 s e hs).1; omega),
      SPTree.Timed.allRet_mono (fun _ hy => ⟨hy, le_rfl⟩) _ (h.2.1 s e hs).2⟩)
    (fun s o hs => ⟨hm _ _ (by have := (h.2.2.1 s o hs).1; omega),
      SPTree.Timed.allRet_mono (fun _ hy => ⟨hy, le_rfl⟩) _ (h.2.2.1 s o hs).2⟩)
    (fun s o hs => ⟨hm _ _ (by have := (h.2.2.2 s o hs).1; omega),
      SPTree.Timed.allRet_mono (fun _ hy => ⟨hy, le_rfl⟩) _ (h.2.2.2 s o hs).2⟩)

/-- **A graded time bound is a potential time bound** with the import `1` of every message and
the potential of a state the least activation count at which it satisfies the invariant. -/
noncomputable def TimeBoundGraded.potentialBound {Inv : ℕ → σ → Prop}
    (h : A.TimeBoundGraded Inv a b) : A.PotentialBound 1 1 0 0 a b :=
  have hm : ∀ i n, a + b * i ≤ a + b * (i + n) := fun i n =>
    Nat.add_le_add_left (Nat.mul_le_mul_left b (Nat.le_add_right i n)) a
  PotentialBound.ofIndexed Inv h.1
    (fun i s e hs => ⟨le_trans (h.2.1 i s e hs).1 (hm i _), (h.2.1 i s e hs).2⟩)
    (fun i s o hs => ⟨le_trans (h.2.2.1 i s o hs).1 (hm i _), (h.2.2.1 i s o hs).2⟩)
    (fun i s o hs => ⟨le_trans (h.2.2.2 i s o hs).1 (hm i _), (h.2.2.2 i s o hs).2⟩)
    (fun _ => le_rfl) (fun _ => le_rfl)

/-- **A size-graded time bound is a potential time bound** with the import `1 + sE e` of an event
and `1 + sO o` of an answer, the constant `max b c` and the potential of a state the least
activation count at which it satisfies the invariant. -/
noncomputable def TimeBoundSized.potentialBound {Inv : ℕ → σ → Prop} {sE : E → ℕ}
    {sO : OG → ℕ} {c : ℕ} (h : A.TimeBoundSized Inv sE sO a b c) :
    A.PotentialBound (fun e => 1 + sE e) (fun o => 1 + sO o) 0 0 a (max b c) :=
  have hm : ∀ i n, a + b * i + c * n ≤ a + max b c * (i + (1 + n)) := fun i n => by
    have := Nat.mul_le_mul_right i (le_max_left b c)
    have := Nat.mul_le_mul_right n (le_max_right b c)
    rw [Nat.mul_add, Nat.mul_add, Nat.mul_one]
    omega
  PotentialBound.ofIndexed Inv h.1
    (fun i s e hs => ⟨le_trans (h.2.1 i s e hs).1 (hm i _), (h.2.1 i s e hs).2⟩)
    (fun i s o hs => ⟨le_trans (h.2.2.1 i s o hs).1 (hm i _), (h.2.2.1 i s o hs).2⟩)
    (fun i s o hs => ⟨le_trans (h.2.2.2 i s o hs).1 (hm i _), (h.2.2.2 i s o hs).2⟩)
    (fun _ => Nat.le_add_right 1 _) (fun _ => Nat.le_add_right 1 _)

end MultiHybrid.Timed

end CatCrypt.Crypto.UCTransparent
