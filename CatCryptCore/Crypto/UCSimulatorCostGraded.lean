/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCSimulatorCost

/-!
# Graded time bounds of costed simulators

A costed multi-call simulator whose state grows with the activations (a lazily sampled table,
a list of notices) has no constant bound on its steps. Its graded time bound
`MultiHybrid.Timed.TimeBoundGraded A Inv a b` indexes an invariant by the number of activations:
the initial state satisfies `Inv 0`, a step from a state of `Inv i` returns states of
`Inv (i + 1)` and costs at most `a + b * i`. The run `MultiHybrid.Timed.actRun` of `q`
activations, each chosen by a schedule from the activation index, the state and the last
output, then costs at most `q * a + b * (q * (q - 1) / 2)`. At `b = 0` the graded bound is the
invariant bound `MultiHybrid.Timed.TimeBoundInv`.

## Main definitions

* `MultiHybrid.Timed.TimeBoundGraded`: the graded time bound of a costed multi-call simulator.
* `MultiHybrid.Timed.act`, `MultiHybrid.Timed.actRun`: one activation, and a run of activations.
* `Simulator.Timed.TimeBoundGraded`: the graded time bound of a costed simulator.

## Main results

* `MultiHybrid.Timed.TimeBoundGraded.of_timeBoundInv`,
  `MultiHybrid.Timed.TimeBoundGraded.timeBoundInv`: the case `b = 0`.
* `MultiHybrid.Timed.TimeBoundGraded.actRun_time_le`: the time of `q` activations from the
  initial state.
* `MultiHybrid.Timed.tensor_timeBoundGraded`: the costed tensor on the invariant `tensorInv`.
* `Simulator.Timed.TimeBound.timeBoundGraded`, `Simulator.Timed.TimeBoundGraded.mono` and the
  graded bounds of the constructors and the tensor (`Simulator.tensor.timeBoundGraded_timed`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core

namespace MultiHybrid.Timed

variable {σ E O EG OG : Type}

/-- The graded time bound of a costed multi-call simulator on the invariant `Inv`, indexed by
the number of activations: the initial state satisfies `Inv 0`, and every `start`, `resume` or
`finish` step from a state of `Inv i` costs at most `a + b * i` and returns states of
`Inv (i + 1)`. -/
def TimeBoundGraded (A : MultiHybrid.Timed σ E O EG OG) (Inv : ℕ → σ → Prop) (a b : ℕ) :
    Prop :=
  Inv 0 A.init ∧
  (∀ i s e, Inv i s → SPTree.Timed.stepTime (A.startCost s e, A.start s e) ≤ a + b * i ∧
    SPTree.Timed.AllRet (fun y => Inv (i + 1) y.1) (A.start s e)) ∧
  (∀ i s o, Inv i s → SPTree.Timed.stepTime (A.resumeCost s o, A.resume s o) ≤ a + b * i ∧
    SPTree.Timed.AllRet (fun y => Inv (i + 1) y.1) (A.resume s o)) ∧
  (∀ i s o, Inv i s → SPTree.Timed.stepTime (A.finishCost s o, A.finish s o) ≤ a + b * i ∧
    SPTree.Timed.AllRet (fun y => Inv (i + 1) y.1) (A.finish s o))

/-- A graded time bound is a graded time bound of all larger constants. -/
theorem TimeBoundGraded.mono {A : MultiHybrid.Timed σ E O EG OG} {Inv : ℕ → σ → Prop}
    {a b a' b' : ℕ} (h : A.TimeBoundGraded Inv a b) (ha : a ≤ a') (hb : b ≤ b') :
    A.TimeBoundGraded Inv a' b' := by
  have hm : ∀ i, a + b * i ≤ a' + b' * i := fun i =>
    Nat.add_le_add ha (Nat.mul_le_mul_right i hb)
  obtain ⟨h0, h1, h2, h3⟩ := h
  exact ⟨h0, fun i s e hs => ⟨le_trans (h1 i s e hs).1 (hm i), (h1 i s e hs).2⟩,
    fun i s o hs => ⟨le_trans (h2 i s o hs).1 (hm i), (h2 i s o hs).2⟩,
    fun i s o hs => ⟨le_trans (h3 i s o hs).1 (hm i), (h3 i s o hs).2⟩⟩

/-- An invariant time bound with step bounds `a`, `b`, `c` is a graded time bound with the
constant invariant, the constant `max a (max b c)` and no growth. -/
theorem TimeBoundGraded.of_timeBoundInv {A : MultiHybrid.Timed σ E O EG OG} {Inv : σ → Prop}
    {a b c : ℕ} (h : A.TimeBoundInv Inv a b c) :
    A.TimeBoundGraded (fun _ => Inv) (max a (max b c)) 0 := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  exact ⟨h0, fun _ s e hs => ⟨by grind, (h1 s e hs).2⟩,
    fun _ s o hs => ⟨by grind, (h2 s o hs).2⟩,
    fun _ s o hs => ⟨by grind, (h3 s o hs).2⟩⟩

/-- A graded time bound without growth is an invariant time bound on the states that satisfy
the invariant at some activation count. -/
theorem TimeBoundGraded.timeBoundInv {A : MultiHybrid.Timed σ E O EG OG} {Inv : ℕ → σ → Prop}
    {a : ℕ} (h : A.TimeBoundGraded Inv a 0) :
    A.TimeBoundInv (fun s => ∃ i, Inv i s) a a a := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  refine ⟨⟨0, h0⟩, fun s e ⟨i, hs⟩ => ⟨by grind, ?_⟩, fun s o ⟨i, hs⟩ => ⟨by grind, ?_⟩,
    fun s o ⟨i, hs⟩ => ⟨by grind, ?_⟩⟩
  · exact SPTree.Timed.allRet_mono (fun y hy => ⟨i + 1, hy⟩) _ (h1 i s e hs).2
  · exact SPTree.Timed.allRet_mono (fun y hy => ⟨i + 1, hy⟩) _ (h2 i s o hs).2
  · exact SPTree.Timed.allRet_mono (fun y hy => ⟨i + 1, hy⟩) _ (h3 i s o hs).2

/-- One activation of a costed multi-call simulator on the input `x`: `start` on an outer
event, `resume` or `finish` on an answer, with the outer output of `finish` as a decision. -/
noncomputable def act (A : MultiHybrid.Timed σ E O EG OG) (s : σ) :
    E ⊕ OG ⊕ OG → ℕ × SPTree.Timed (σ × (EG ⊕ O))
  | .inl e => (A.startCost s e, A.start s e)
  | .inr (.inl o) => (A.resumeCost s o, A.resume s o)
  | .inr (.inr o) => SPTree.Timed.delay (A.finishCost s o)
      ((A.finish s o).map (fun y => (y.1, .inr y.2)) fun _ => 0)

/-- The run of `n` activations of a costed multi-call simulator from the state `s` after `i`
activations, the last output being `o`: the schedule `next` chooses each input from the
activation index, the state and the last output. -/
noncomputable def actRun (A : MultiHybrid.Timed σ E O EG OG)
    (next : ℕ → σ → Option (EG ⊕ O) → E ⊕ OG ⊕ OG) :
    ℕ → ℕ → σ → Option (EG ⊕ O) → ℕ × SPTree.Timed σ
  | _, 0, s, _ => (0, .ret s)
  | i, n + 1, s, o =>
    SPTree.Timed.delay (A.act s (next i s o)).1
      ((A.act s (next i s o)).2.bind fun y => actRun A next (i + 1) n y.1 (some y.2))

/-- Under a graded time bound, an activation from a state of `Inv i` costs at most `a + b * i`
and returns states of `Inv (i + 1)`. -/
theorem TimeBoundGraded.act_le {A : MultiHybrid.Timed σ E O EG OG} {Inv : ℕ → σ → Prop}
    {a b : ℕ} (h : A.TimeBoundGraded Inv a b) {i : ℕ} {s : σ} (hs : Inv i s)
    (x : E ⊕ OG ⊕ OG) :
    SPTree.Timed.stepTime (A.act s x) ≤ a + b * i ∧
      SPTree.Timed.AllRet (fun y => Inv (i + 1) y.1) (A.act s x).2 := by
  obtain ⟨_, h1, h2, h3⟩ := h
  rcases x with e | o | o
  · exact h1 i s e hs
  · exact h2 i s o hs
  · obtain ⟨ht, hr⟩ := h3 i s o hs
    refine ⟨?_, ?_⟩
    · have := SPTree.Timed.stepTime_map_le (fun y : σ × O => (y.1, (Sum.inr y.2 : EG ⊕ O)))
        (fun _ => 0) (A.finish s o) 0 fun _ => le_rfl
      simp only [MultiHybrid.Timed.act, SPTree.Timed.stepTime_delay] at this ⊢
      simp only [SPTree.Timed.stepTime] at ht
      omega
    · simp only [MultiHybrid.Timed.act, SPTree.Timed.delay, SPTree.Timed.map,
        SPTree.Timed.allRet_bind]
      exact hr

/-- Under a graded time bound, `n` activations from a state of `Inv i` cost at most the sum of
`a + b * (i + j)` over `j < n`. -/
theorem TimeBoundGraded.actRun_le {A : MultiHybrid.Timed σ E O EG OG} {Inv : ℕ → σ → Prop}
    {a b : ℕ} (h : A.TimeBoundGraded Inv a b)
    (next : ℕ → σ → Option (EG ⊕ O) → E ⊕ OG ⊕ OG) (n : ℕ) :
    ∀ (i : ℕ) (s : σ) (o : Option (EG ⊕ O)), Inv i s →
      SPTree.Timed.stepTime (A.actRun next i n s o) ≤
        ∑ j ∈ Finset.range n, (a + b * (i + j)) := by
  induction n with
  | zero =>
    intro i s o _
    simp [MultiHybrid.Timed.actRun, SPTree.Timed.stepTime, SPTree.Timed.time_ret]
  | succ n ih =>
    intro i s o hs
    have hx := h.act_le hs (next i s o)
    have hb := SPTree.Timed.stepTime_bind_le_of_allRet (A.act s (next i s o)).2
      (fun y => A.actRun next (i + 1) n y.1 (some y.2)) _ hx.2
      (fun y hy => ih (i + 1) y.1 (some y.2) hy)
    have hsum : ∑ j ∈ Finset.range (n + 1), (a + b * (i + j)) =
        (a + b * i) + ∑ j ∈ Finset.range n, (a + b * (i + 1 + j)) := by
      rw [Finset.sum_range_succ', add_comm]
      refine congrArg₂ _ (by simp) (Finset.sum_congr rfl fun j _ => by grind)
    simp only [MultiHybrid.Timed.actRun, SPTree.Timed.stepTime_delay, hsum]
    simp only [SPTree.Timed.stepTime] at hx hb ⊢
    omega

/-- **Time of `q` activations.** Under a graded time bound, a run of `q` activations from the
initial state costs at most `q * a + b * (q * (q - 1) / 2)`. -/
theorem TimeBoundGraded.actRun_time_le {A : MultiHybrid.Timed σ E O EG OG}
    {Inv : ℕ → σ → Prop} {a b : ℕ} (h : A.TimeBoundGraded Inv a b)
    (next : ℕ → σ → Option (EG ⊕ O) → E ⊕ OG ⊕ OG) (q : ℕ) (o : Option (EG ⊕ O)) :
    SPTree.Timed.stepTime (A.actRun next 0 q A.init o) ≤ q * a + b * (q * (q - 1) / 2) := by
  have h' := h.actRun_le next q 0 A.init o h.1
  rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, smul_eq_mul,
    ← Finset.mul_sum] at h'
  simpa [Finset.sum_range_id] using h'

/-- The invariant of the tensor at `i` activations: the components satisfy their invariants at
activation counts of sum at most `i`. -/
def tensorInv {σ' : Type} (Inv : ℕ → σ → Prop) (Inv' : ℕ → σ' → Prop) (i : ℕ) (s : σ × σ') :
    Prop :=
  ∃ i₁ i₂, i₁ + i₂ ≤ i ∧ Inv i₁ s.1 ∧ Inv' i₂ s.2

/-- A step of the costed tensor: a component step `(C, A)` of time at most `B` whose leaves
satisfy `Q`, followed by a return of cost at most `K` behind three delays, has time at most
`B + K + 3`, and its leaves satisfy `P` when `g` maps `Q` to `P`. -/
theorem tensor_step_le {α β : Type} {Q : α → Prop} {P : β → Prop} (A : SPTree.Timed α)
    (C K B : ℕ) (g : α → β) (k : α → ℕ) (hk : ∀ x, k x ≤ K)
    (hA : SPTree.Timed.stepTime (C, A) ≤ B) (hQ : SPTree.Timed.AllRet Q A)
    (hP : ∀ x, Q x → P (g x)) :
    SPTree.Timed.stepTime (SPTree.Timed.delay 1 (SPTree.Timed.delay 1
      (SPTree.Timed.delay (1 + C) (A.bind fun x => (k x, SPTree.Timed.ret (g x)))))) ≤
        B + K + 3 ∧
    SPTree.Timed.AllRet P (SPTree.Timed.delay 1 (SPTree.Timed.delay 1
      (SPTree.Timed.delay (1 + C) (A.bind fun x => (k x, SPTree.Timed.ret (g x)))))).2 := by
  refine ⟨le_trans (stepTime_delay3_bind_le _ _ _ K fun x => ?_) ?_, ?_⟩
  · simpa [SPTree.Timed.stepTime, SPTree.Timed.time_ret] using hk x
  · simp only [SPTree.Timed.stepTime] at hA
    omega
  · simp only [SPTree.Timed.delay, SPTree.Timed.allRet_bind, SPTree.Timed.AllRet]
    exact SPTree.Timed.allRet_mono hP _ hQ

set_option linter.auxLemma false in
/-- **Graded running time of the costed tensor**: if `πT` and `π'T` have graded time bounds
`a`, `b` and `a'`, `b'`, the costed tensor has the graded time bound
`max a a' + 7`, `max b b'` on the invariant `tensorInv`. -/
theorem tensor_timeBoundGraded {σ' E' O' EG' OG' : Type} (π : MultiHybrid σ E O EG OG)
    (π' : MultiHybrid σ' E' O' EG' OG') {πT : MultiHybrid.Timed σ E O EG OG}
    {π'T : MultiHybrid.Timed σ' E' O' EG' OG'} {Inv : ℕ → σ → Prop} {Inv' : ℕ → σ' → Prop}
    {a b a' b' : ℕ} (hinit : πT.init = π.init) (hinit' : π'T.init = π'.init)
    (hT : πT.TimeBoundGraded Inv a b) (hT' : π'T.TimeBoundGraded Inv' a' b') :
    (tensor π π' πT π'T).TimeBoundGraded (tensorInv Inv Inv') (max a a' + 7) (max b b') := by
  obtain ⟨h0, h1, h2, h3⟩ := hT
  obtain ⟨h0', h1', h2', h3'⟩ := hT'
  refine ⟨⟨0, 0, le_rfl, (show Inv 0 π.init from hinit ▸ h0),
    (show Inv' 0 π'.init from hinit' ▸ h0')⟩, fun i s e hs => ?_, fun i s o hs => ?_,
    fun i s o hs => ?_⟩
  · obtain ⟨i₁, i₂, hi, hs1, hs2⟩ := hs
    rcases e with e | e <;>
      simp only [tensor, MultiHybrid.tensor.timed, MultiHybrid.tensor.start.tree.timed,
        MultiHybrid.tensor.start.tree.match_1.timed]
    · obtain ⟨ht, hr⟩ := h1 i₁ s.1 e hs1
      refine (tensor_step_le _ _ 4 _ _ _ (fun x => ?_) ht hr
        (fun x hx => ⟨i₁ + 1, i₂, by omega, hx, hs2⟩)).imp (fun h => le_trans h ?_) id
      · rcases x with ⟨_, _ | _⟩ <;> simp
      · have := Nat.mul_le_mul (le_max_left b b') (show i₁ ≤ i by omega)
        omega
    · obtain ⟨ht, hr⟩ := h1' i₂ s.2 e hs2
      refine (tensor_step_le _ _ 4 _ _ _ (fun x => ?_) ht hr
        (fun x hx => ⟨i₁, i₂ + 1, by omega, hs1, hx⟩)).imp (fun h => le_trans h ?_) id
      · rcases x with ⟨_, _ | _⟩ <;> simp
      · have := Nat.mul_le_mul (le_max_right b b') (show i₂ ≤ i by omega)
        omega
  · obtain ⟨i₁, i₂, hi, hs1, hs2⟩ := hs
    rcases o with o | o <;>
      simp only [tensor, MultiHybrid.tensor.timed, MultiHybrid.tensor.resume.tree.timed,
        MultiHybrid.tensor.resume.tree.match_1.timed]
    · obtain ⟨ht, hr⟩ := h2 i₁ s.1 o hs1
      refine (tensor_step_le _ _ 4 _ _ _ (fun x => ?_) ht hr
        (fun x hx => ⟨i₁ + 1, i₂, by omega, hx, hs2⟩)).imp (fun h => le_trans h ?_) id
      · rcases x with ⟨_, _ | _⟩ <;> simp
      · have := Nat.mul_le_mul (le_max_left b b') (show i₁ ≤ i by omega)
        omega
    · obtain ⟨ht, hr⟩ := h2' i₂ s.2 o hs2
      refine (tensor_step_le _ _ 4 _ _ _ (fun x => ?_) ht hr
        (fun x hx => ⟨i₁, i₂ + 1, by omega, hs1, hx⟩)).imp (fun h => le_trans h ?_) id
      · rcases x with ⟨_, _ | _⟩ <;> simp
      · have := Nat.mul_le_mul (le_max_right b b') (show i₂ ≤ i by omega)
        omega
  · obtain ⟨i₁, i₂, hi, hs1, hs2⟩ := hs
    rcases o with o | o <;>
      simp only [tensor, MultiHybrid.tensor.timed, MultiHybrid.tensor.finish.tree.timed,
        MultiHybrid.tensor.finish.tree.match_1.timed]
    · obtain ⟨ht, hr⟩ := h3 i₁ s.1 o hs1
      refine (tensor_step_le _ _ 0 _ _ _ (fun _ => le_rfl) ht hr
        (fun x hx => ⟨i₁ + 1, i₂, by omega, hx, hs2⟩)).imp (fun h => le_trans h ?_) id
      have := Nat.mul_le_mul (le_max_left b b') (show i₁ ≤ i by omega)
      omega
    · obtain ⟨ht, hr⟩ := h3' i₂ s.2 o hs2
      refine (tensor_step_le _ _ 0 _ _ _ (fun _ => le_rfl) ht hr
        (fun x hx => ⟨i₁, i₂ + 1, by omega, hs1, hx⟩)).imp (fun h => le_trans h ?_) id
      have := Nat.mul_le_mul (le_max_right b b') (show i₂ ≤ i by omega)
      omega

end MultiHybrid.Timed

namespace Simulator.Timed

/-- The graded time bound `a`, `b` of a costed simulator: a costed multi-call simulator has a
graded time bound with constants `a`, `b` on some invariant; the parts of a costed composite
have graded time bounds whose constants sum to at most `a` and `b`; a relabelled simulator has
the graded time bound of its simulator. -/
def TimeBoundGraded : {E O EG OG : Type} → {V : PubView E O} → {W : PubView EG OG} →
    Simulator.Timed E O EG OG V W → ℕ → ℕ → Prop
  | _, _, _, _, _, _, .ofMultiHybrid (σ := σ) πT, a, b =>
    ∃ Inv : ℕ → σ → Prop, πT.TimeBoundGraded Inv a b
  | _, _, _, _, _, _, .ofMultiHybridHat (σHat := σHat) _ _ _ _ _ πT, a, b =>
    ∃ Inv : ℕ → σHat → Prop, πT.TimeBoundGraded Inv a b
  | _, _, _, _, _, _, .comp T₁ T₂, a, b => ∃ a₁ b₁ a₂ b₂, TimeBoundGraded T₁ a₁ b₁ ∧
    TimeBoundGraded T₂ a₂ b₂ ∧ a₁ + a₂ ≤ a ∧ b₁ + b₂ ≤ b
  | _, _, _, _, _, _, .mapPorts T _ _, a, b => TimeBoundGraded T a b

/-- A graded time bound of a costed simulator is a graded time bound of all larger
constants. -/
theorem TimeBoundGraded.mono {E O EG OG : Type} {V : PubView E O} {W : PubView EG OG}
    {T : Simulator.Timed E O EG OG V W} {a b a' b' : ℕ} (h : T.TimeBoundGraded a b)
    (ha : a ≤ a') (hb : b ≤ b') : T.TimeBoundGraded a' b' := by
  induction T generalizing a b a' b' with
  | ofMultiHybrid πT =>
    obtain ⟨Inv, hI⟩ := h
    exact ⟨Inv, hI.mono ha hb⟩
  | ofMultiHybridHat εσ εE εO εEG εOG πT =>
    obtain ⟨Inv, hI⟩ := h
    exact ⟨Inv, hI.mono ha hb⟩
  | mapPorts T f g ih => exact ih h ha hb
  | comp T₁ T₂ _ _ =>
    obtain ⟨a₁, b₁, a₂, b₂, h₁, h₂, h3, h4⟩ := h
    exact ⟨a₁, b₁, a₂, b₂, h₁, h₂, by omega, by omega⟩

/-- A time bound `t` of a costed simulator is a graded time bound with constant `t` and no
growth. -/
theorem TimeBound.timeBoundGraded {E O EG OG : Type} {V : PubView E O} {W : PubView EG OG}
    {T : Simulator.Timed E O EG OG V W} {t : ℕ} (h : T.TimeBound t) : T.TimeBoundGraded t 0 := by
  induction T generalizing t with
  | ofMultiHybrid πT =>
    have h' := MultiHybrid.Timed.TimeBoundGraded.of_timeBoundInv
      (MultiHybrid.Timed.TimeBoundInv.of_timeBound h)
    exact ⟨_, h'.mono (by omega) le_rfl⟩
  | ofMultiHybridHat εσ εE εO εEG εOG πT =>
    obtain ⟨Inv, hI⟩ := h
    exact ⟨_, (MultiHybrid.Timed.TimeBoundGraded.of_timeBoundInv hI).mono (by omega) le_rfl⟩
  | mapPorts T f g ih => exact ih h
  | comp T₁ T₂ ih₁ ih₂ =>
    obtain ⟨t₁, t₂, h₁, h₂, hle⟩ := h
    exact ⟨t₁, 0, t₂, 0, ih₁ h₁, ih₂ h₂, hle, le_rfl⟩

end Simulator.Timed

namespace Simulator

variable {σ σ' E O E' O' EM OM EG OG EG' OG' : Type} {V : PubView E O} {U : PubView EM OM}
  {W : PubView EG OG} {V' : PubView E' O'} {W' : PubView EG' OG'}

/-- **Graded running time of a costed multi-call simulator**: a graded time bound of its steps
is a graded time bound of the costed simulator. -/
theorem ofMultiHybrid.timeBoundGraded_timed {πT : MultiHybrid.Timed σ E O EG OG}
    {Inv : ℕ → σ → Prop} {a b : ℕ} (hT : πT.TimeBoundGraded Inv a b) :
    (Simulator.Timed.ofMultiHybrid πT : Simulator.Timed E O EG OG V W).TimeBoundGraded a b :=
  ⟨Inv, hT⟩

/-- **Graded running time of a costed multi-call simulator on costed states**: a graded time
bound of its steps is a graded time bound of the costed simulator. -/
theorem ofMultiHybridHat.timeBoundGraded_timed {σHat EHat OHat EGHat OGHat : Type}
    {εσ : σHat → σ} {εE : EHat → E} {εO : OHat → O} {εEG : EGHat → EG} {εOG : OGHat → OG}
    {πT : MultiHybrid.Timed σHat EHat OHat EGHat OGHat} {Inv : ℕ → σHat → Prop} {a b : ℕ}
    (hT : πT.TimeBoundGraded Inv a b) :
    (Simulator.Timed.ofMultiHybridHat εσ εE εO εEG εOG πT :
      Simulator.Timed E O EG OG V W).TimeBoundGraded a b :=
  ⟨Inv, hT⟩

/-- **Graded running time of a relabelled costed simulator**: that of its simulator. -/
theorem mapPorts.timeBoundGraded_timed {T : Simulator.Timed EM OM EG OG U W} {a b : ℕ}
    (hT : T.TimeBoundGraded a b) (f : E → EM) (g : OM → O) :
    (Simulator.Timed.mapPorts T f g : Simulator.Timed E O EG OG V W).TimeBoundGraded a b :=
  hT

/-- **Graded running time of a costed composite**: the sums of the constants of its parts. -/
theorem comp.timeBoundGraded_timed {T₁ : Simulator.Timed E O EM OM V U}
    {T₂ : Simulator.Timed EM OM EG OG U W} {a₁ b₁ a₂ b₂ : ℕ} (h₁ : T₁.TimeBoundGraded a₁ b₁)
    (h₂ : T₂.TimeBoundGraded a₂ b₂) : (T₁.comp T₂).TimeBoundGraded (a₁ + a₂) (b₁ + b₂) :=
  ⟨a₁, b₁, a₂, b₂, h₁, h₂, le_rfl, le_rfl⟩

/-- **Graded running time of the costed tensor**: if `πT` and `π'T` erase to `π` and `π'` and
have graded time bounds `a`, `b` and `a'`, `b'`, the costed tensor has the graded time bound
`max a a' + 7`, `max b b'`. -/
theorem tensor.timeBoundGraded_timed {π : MultiHybrid σ E O EG OG}
    {π' : MultiHybrid σ' E' O' EG' OG'} {πT : MultiHybrid.Timed σ E O EG OG}
    {π'T : MultiHybrid.Timed σ' E' O' EG' OG'} {Inv : ℕ → σ → Prop} {Inv' : ℕ → σ' → Prop}
    {a b a' b' : ℕ} (hE : πT.Erases π) (hE' : π'T.Erases π') (hT : πT.TimeBoundGraded Inv a b)
    (hT' : π'T.TimeBoundGraded Inv' a' b') :
    (tensor.timed (V := V) (W := W) (V' := V') (W' := W') π π' πT π'T).TimeBoundGraded
      (max a a' + 7) (max b b') := by
  obtain ⟨_, _, _, rfl⟩ := hE
  obtain ⟨_, _, _, rfl⟩ := hE'
  exact ofMultiHybrid.timeBoundGraded_timed
    (MultiHybrid.Timed.tensor_timeBoundGraded _ _ rfl rfl hT hT')

end Simulator

end CatCrypt.Crypto.UCTransparent
