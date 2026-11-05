/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCSimulatorCostGraded

/-!
# Size-graded time bounds of costed simulators

A costed simulator whose step handles data of the environment's size (a ciphertext of the
length of the message, a board of the number of voters) has no bound on its steps that is
independent of the event. Its size-graded time bound
`MultiHybrid.Timed.TimeBoundSized A Inv sE sO a b c` extends the graded time bound
`MultiHybrid.Timed.TimeBoundGraded A Inv a b` by the sizes `sE` of the outer events and `sO`
of the answers: a step on the event or answer `x` from a state of `Inv i` costs at most
`a + b * i + c * s x` and returns states of `Inv (i + 1)`. At `c = 0`, or on sizes bounded by
`m`, it is the graded time bound (`MultiHybrid.Timed.TimeBoundSized.timeBoundGraded`), and a
graded time bound is a size-graded one of every size (`TimeBoundGraded.timeBoundSized`).

The size-graded time bound of a costed simulator, `Simulator.Timed.TimeBoundSized T sE sO a b c`,
counts sizes at the outer ports of `T` and at the answers of the middle interface of a
composite: the outer factor of a composite is bounded with a size `sM` on the answers of the
inner factor, the inner factor with the size `0` on its events, and every answer `o` of the inner
factor has size `sM o` at most the time of the step that returns it
(`Simulator.Timed.AnswerSizeLe`). A relabelled simulator is bounded by a size on its events that
the relabelling does not increase.

The bound of the size of an answer by the time of its step is a field of the certificate, since a
return costs nothing and a costed step may return a list of any length at time `0`. At the size
`0` on the middle answers the field holds for every simulator
(`Simulator.Timed.AnswerSizeLe.zero`).

## Main definitions

* `MultiHybrid.Timed.TimeBoundSized`: the size-graded time bound of a costed multi-call
  simulator.
* `MultiHybrid.Timed.AnswerSizeLe`, `Simulator.Timed.AnswerSizeLe`: the answers of a costed
  simulator have sizes at most the times of the steps that return them.
* `Simulator.Timed.TimeBoundSized`: the size-graded time bound of a costed simulator.

## Main results

* `MultiHybrid.Timed.TimeBoundGraded.timeBoundSized`,
  `MultiHybrid.Timed.TimeBoundSized.timeBoundGraded`: the graded time bound as a size-graded one,
  and the size-graded time bound on bounded sizes as a graded one.
* `MultiHybrid.Timed.tensor_timeBoundSized`: the costed tensor on the invariant `tensorInv`.
* `Simulator.comp.timeBoundSized_timed_of_answerSizeLe`: the size-graded bound of a composite
  whose outer factor is bounded with the sizes of the answers of the inner factor.
* `Simulator.ofMultiHybrid.timeBoundSized_timed`, `Simulator.ofMultiHybridHat.timeBoundSized_timed`,
  `Simulator.comp.timeBoundSized_timed`, `Simulator.mapPorts.timeBoundSized_timed`,
  `Simulator.tensor.timeBoundSized_timed`: the size-graded bounds of the constructors.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core

namespace MultiHybrid.Timed

variable {σ E O EG OG : Type}

/-- The size-graded time bound of a costed multi-call simulator on the invariant `Inv`, indexed
by the number of activations, with the sizes `sE` of the outer events and `sO` of the answers:
the initial state satisfies `Inv 0`, and a `start` step on `e`, or a `resume` or `finish` step
on `o`, from a state of `Inv i` costs at most `a + b * i + c * sE e`, or
`a + b * i + c * sO o`, and returns states of `Inv (i + 1)`. -/
def TimeBoundSized (A : MultiHybrid.Timed σ E O EG OG) (Inv : ℕ → σ → Prop) (sE : E → ℕ)
    (sO : OG → ℕ) (a b c : ℕ) : Prop :=
  Inv 0 A.init ∧
  (∀ i s e, Inv i s →
    SPTree.Timed.stepTime (A.startCost s e, A.start s e) ≤ a + b * i + c * sE e ∧
    SPTree.Timed.AllRet (fun y => Inv (i + 1) y.1) (A.start s e)) ∧
  (∀ i s o, Inv i s →
    SPTree.Timed.stepTime (A.resumeCost s o, A.resume s o) ≤ a + b * i + c * sO o ∧
    SPTree.Timed.AllRet (fun y => Inv (i + 1) y.1) (A.resume s o)) ∧
  (∀ i s o, Inv i s →
    SPTree.Timed.stepTime (A.finishCost s o, A.finish s o) ≤ a + b * i + c * sO o ∧
    SPTree.Timed.AllRet (fun y => Inv (i + 1) y.1) (A.finish s o))

/-- A size-graded time bound is a size-graded time bound of all larger constants and sizes. -/
theorem TimeBoundSized.mono {A : MultiHybrid.Timed σ E O EG OG} {Inv : ℕ → σ → Prop}
    {sE sE' : E → ℕ} {sO sO' : OG → ℕ} {a b c a' b' c' : ℕ}
    (h : A.TimeBoundSized Inv sE sO a b c) (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c')
    (hE : ∀ e, sE e ≤ sE' e) (hO : ∀ o, sO o ≤ sO' o) :
    A.TimeBoundSized Inv sE' sO' a' b' c' := by
  have hm : ∀ i n n', n ≤ n' → a + b * i + c * n ≤ a' + b' * i + c' * n' := fun i n n' hn =>
    Nat.add_le_add (Nat.add_le_add ha (Nat.mul_le_mul_right i hb)) (Nat.mul_le_mul hc hn)
  obtain ⟨h0, h1, h2, h3⟩ := h
  exact ⟨h0, fun i s e hs => ⟨le_trans (h1 i s e hs).1 (hm i _ _ (hE e)), (h1 i s e hs).2⟩,
    fun i s o hs => ⟨le_trans (h2 i s o hs).1 (hm i _ _ (hO o)), (h2 i s o hs).2⟩,
    fun i s o hs => ⟨le_trans (h3 i s o hs).1 (hm i _ _ (hO o)), (h3 i s o hs).2⟩⟩

/-- A graded time bound is a size-graded time bound of every size. -/
theorem TimeBoundGraded.timeBoundSized {A : MultiHybrid.Timed σ E O EG OG}
    {Inv : ℕ → σ → Prop} {a b : ℕ} (h : A.TimeBoundGraded Inv a b) (sE : E → ℕ) (sO : OG → ℕ)
    (c : ℕ) : A.TimeBoundSized Inv sE sO a b c := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  exact ⟨h0, fun i s e hs => ⟨le_trans (h1 i s e hs).1 (Nat.le_add_right _ _), (h1 i s e hs).2⟩,
    fun i s o hs => ⟨le_trans (h2 i s o hs).1 (Nat.le_add_right _ _), (h2 i s o hs).2⟩,
    fun i s o hs => ⟨le_trans (h3 i s o hs).1 (Nat.le_add_right _ _), (h3 i s o hs).2⟩⟩

/-- A size-graded time bound on sizes at most `m` is a graded time bound with the constant
`a + c * m`. -/
theorem TimeBoundSized.timeBoundGraded {A : MultiHybrid.Timed σ E O EG OG}
    {Inv : ℕ → σ → Prop} {sE : E → ℕ} {sO : OG → ℕ} {a b c m : ℕ}
    (h : A.TimeBoundSized Inv sE sO a b c) (hE : ∀ e, sE e ≤ m) (hO : ∀ o, sO o ≤ m) :
    A.TimeBoundGraded Inv (a + c * m) b := by
  obtain ⟨h0, h1, h2, h3⟩ := h
  have hm : ∀ i n, n ≤ m → a + b * i + c * n ≤ a + c * m + b * i := fun i n hn => by
    have := Nat.mul_le_mul_left c hn
    omega
  exact ⟨h0, fun i s e hs => ⟨le_trans (h1 i s e hs).1 (hm i _ (hE e)), (h1 i s e hs).2⟩,
    fun i s o hs => ⟨le_trans (h2 i s o hs).1 (hm i _ (hO o)), (h2 i s o hs).2⟩,
    fun i s o hs => ⟨le_trans (h3 i s o hs).1 (hm i _ (hO o)), (h3 i s o hs).2⟩⟩

set_option linter.auxLemma false in
/-- **Size-graded running time of the costed tensor**: if `πT` and `π'T` have size-graded time
bounds `a`, `b`, `c` and `a'`, `b'`, `c'`, the costed tensor has the size-graded time bound
`max a a' + 7`, `max b b'`, `max c c'` on the invariant `tensorInv`, with the sizes of the
components on the two sides. -/
theorem tensor_timeBoundSized {σ' E' O' EG' OG' : Type} (π : MultiHybrid σ E O EG OG)
    (π' : MultiHybrid σ' E' O' EG' OG') {πT : MultiHybrid.Timed σ E O EG OG}
    {π'T : MultiHybrid.Timed σ' E' O' EG' OG'} {Inv : ℕ → σ → Prop} {Inv' : ℕ → σ' → Prop}
    {sE : E → ℕ} {sO : OG → ℕ} {sE' : E' → ℕ} {sO' : OG' → ℕ} {a b c a' b' c' : ℕ}
    (hinit : πT.init = π.init) (hinit' : π'T.init = π'.init)
    (hT : πT.TimeBoundSized Inv sE sO a b c) (hT' : π'T.TimeBoundSized Inv' sE' sO' a' b' c') :
    (tensor π π' πT π'T).TimeBoundSized (tensorInv Inv Inv') (Sum.elim sE sE')
      (Sum.elim sO sO') (max a a' + 7) (max b b') (max c c') := by
  obtain ⟨h0, h1, h2, h3⟩ := hT
  obtain ⟨h0', h1', h2', h3'⟩ := hT'
  refine ⟨⟨0, 0, le_rfl, (show Inv 0 π.init from hinit ▸ h0),
    (show Inv' 0 π'.init from hinit' ▸ h0')⟩, fun i s e hs => ?_, fun i s o hs => ?_,
    fun i s o hs => ?_⟩
  · obtain ⟨i₁, i₂, hi, hs1, hs2⟩ := hs
    rcases e with e | e <;>
      simp only [tensor, MultiHybrid.tensor.timed, MultiHybrid.tensor.start.tree.timed,
        MultiHybrid.tensor.start.tree.match_1.timed, Sum.elim_inl, Sum.elim_inr]
    · obtain ⟨ht, hr⟩ := h1 i₁ s.1 e hs1
      refine (tensor_step_le _ _ 4 _ _ _ (fun x => ?_) ht hr
        (fun x hx => ⟨i₁ + 1, i₂, by omega, hx, hs2⟩)).imp (fun h => le_trans h ?_) id
      · rcases x with ⟨_, _ | _⟩ <;> simp
      · have := Nat.mul_le_mul (le_max_left b b') (show i₁ ≤ i by omega)
        have := Nat.mul_le_mul_right (sE e) (le_max_left c c')
        omega
    · obtain ⟨ht, hr⟩ := h1' i₂ s.2 e hs2
      refine (tensor_step_le _ _ 4 _ _ _ (fun x => ?_) ht hr
        (fun x hx => ⟨i₁, i₂ + 1, by omega, hs1, hx⟩)).imp (fun h => le_trans h ?_) id
      · rcases x with ⟨_, _ | _⟩ <;> simp
      · have := Nat.mul_le_mul (le_max_right b b') (show i₂ ≤ i by omega)
        have := Nat.mul_le_mul_right (sE' e) (le_max_right c c')
        omega
  · obtain ⟨i₁, i₂, hi, hs1, hs2⟩ := hs
    rcases o with o | o <;>
      simp only [tensor, MultiHybrid.tensor.timed, MultiHybrid.tensor.resume.tree.timed,
        MultiHybrid.tensor.resume.tree.match_1.timed, Sum.elim_inl, Sum.elim_inr]
    · obtain ⟨ht, hr⟩ := h2 i₁ s.1 o hs1
      refine (tensor_step_le _ _ 4 _ _ _ (fun x => ?_) ht hr
        (fun x hx => ⟨i₁ + 1, i₂, by omega, hx, hs2⟩)).imp (fun h => le_trans h ?_) id
      · rcases x with ⟨_, _ | _⟩ <;> simp
      · have := Nat.mul_le_mul (le_max_left b b') (show i₁ ≤ i by omega)
        have := Nat.mul_le_mul_right (sO o) (le_max_left c c')
        omega
    · obtain ⟨ht, hr⟩ := h2' i₂ s.2 o hs2
      refine (tensor_step_le _ _ 4 _ _ _ (fun x => ?_) ht hr
        (fun x hx => ⟨i₁, i₂ + 1, by omega, hs1, hx⟩)).imp (fun h => le_trans h ?_) id
      · rcases x with ⟨_, _ | _⟩ <;> simp
      · have := Nat.mul_le_mul (le_max_right b b') (show i₂ ≤ i by omega)
        have := Nat.mul_le_mul_right (sO' o) (le_max_right c c')
        omega
  · obtain ⟨i₁, i₂, hi, hs1, hs2⟩ := hs
    rcases o with o | o <;>
      simp only [tensor, MultiHybrid.tensor.timed, MultiHybrid.tensor.finish.tree.timed,
        MultiHybrid.tensor.finish.tree.match_1.timed, Sum.elim_inl, Sum.elim_inr]
    · obtain ⟨ht, hr⟩ := h3 i₁ s.1 o hs1
      refine (tensor_step_le _ _ 0 _ _ _ (fun _ => le_rfl) ht hr
        (fun x hx => ⟨i₁ + 1, i₂, by omega, hx, hs2⟩)).imp (fun h => le_trans h ?_) id
      have := Nat.mul_le_mul (le_max_left b b') (show i₁ ≤ i by omega)
      have := Nat.mul_le_mul_right (sO o) (le_max_left c c')
      omega
    · obtain ⟨ht, hr⟩ := h3' i₂ s.2 o hs2
      refine (tensor_step_le _ _ 0 _ _ _ (fun _ => le_rfl) ht hr
        (fun x hx => ⟨i₁, i₂ + 1, by omega, hs1, hx⟩)).imp (fun h => le_trans h ?_) id
      have := Nat.mul_le_mul (le_max_right b b') (show i₂ ≤ i by omega)
      have := Nat.mul_le_mul_right (sO' o) (le_max_right c c')
      omega

/-- The answers of a costed multi-call simulator have sizes `sA` at most the time of the step
that returns them: from every state, an outer output of a `start` step on `e` or of a `resume`
step on `o`, and the output of a `finish` step on `o`, has size at most the time of that step. -/
def AnswerSizeLe (A : MultiHybrid.Timed σ E O EG OG) (sA : O → ℕ) : Prop :=
  (∀ s e, SPTree.Timed.AllRet (fun y => ∀ o, y.2 = Sum.inr o →
    sA o ≤ SPTree.Timed.stepTime (A.startCost s e, A.start s e)) (A.start s e)) ∧
  (∀ s o, SPTree.Timed.AllRet (fun y => ∀ o', y.2 = Sum.inr o' →
    sA o' ≤ SPTree.Timed.stepTime (A.resumeCost s o, A.resume s o)) (A.resume s o)) ∧
  (∀ s o, SPTree.Timed.AllRet (fun y =>
    sA y.2 ≤ SPTree.Timed.stepTime (A.finishCost s o, A.finish s o)) (A.finish s o))

/-- Every costed multi-call simulator has answers of size `0` at most the times of its steps. -/
theorem AnswerSizeLe.zero (A : MultiHybrid.Timed σ E O EG OG) : A.AnswerSizeLe fun _ => 0 :=
  ⟨fun _ _ => SPTree.Timed.allRet_of_forall (fun _ _ _ => Nat.zero_le _) _,
    fun _ _ => SPTree.Timed.allRet_of_forall (fun _ _ _ => Nat.zero_le _) _,
    fun _ _ => SPTree.Timed.allRet_of_forall (fun _ => Nat.zero_le _) _⟩

/-- Answer sizes bounded by the times of the steps bound every smaller size. -/
theorem AnswerSizeLe.mono {A : MultiHybrid.Timed σ E O EG OG} {sA sA' : O → ℕ}
    (h : A.AnswerSizeLe sA) (hA : ∀ o, sA' o ≤ sA o) : A.AnswerSizeLe sA' :=
  ⟨fun s e => SPTree.Timed.allRet_mono (fun _ hy o ho => (hA o).trans (hy o ho)) _ (h.1 s e),
    fun s o => SPTree.Timed.allRet_mono (fun _ hy o' ho => (hA o').trans (hy o' ho)) _
      (h.2.1 s o),
    fun s o => SPTree.Timed.allRet_mono (fun y hy => (hA y.2).trans hy) _ (h.2.2 s o)⟩

end MultiHybrid.Timed

namespace Simulator.Timed

/-- The answers of a costed simulator have sizes `sA` at most the times of the steps that
return them: those of a costed multi-call simulator, through the erasure map of the outer
outputs for one on costed outputs; those of the outer factor of a composite; those of the
simulator of a relabelling, at the size of the relabelled answers. -/
def AnswerSizeLe : {E O EG OG : Type} → {V : PubView E O} → {W : PubView EG OG} →
    Simulator.Timed E O EG OG V W → (O → ℕ) → Prop
  | _, _, _, _, _, _, .ofMultiHybrid πT, sA => πT.AnswerSizeLe sA
  | _, _, _, _, _, _, .ofMultiHybridHat _ _ εO _ _ πT, sA => πT.AnswerSizeLe fun o => sA (εO o)
  | _, _, _, _, _, _, .comp T₁ _, sA => AnswerSizeLe T₁ sA
  | _, _, _, _, _, _, .mapPorts T _ g, sA => AnswerSizeLe T fun o => sA (g o)

/-- Every costed simulator has answers of size `0` at most the times of its steps. -/
theorem AnswerSizeLe.zero {E O EG OG : Type} {V : PubView E O} {W : PubView EG OG}
    (T : Simulator.Timed E O EG OG V W) : T.AnswerSizeLe fun _ => 0 := by
  induction T with
  | ofMultiHybrid πT => exact MultiHybrid.Timed.AnswerSizeLe.zero πT
  | ofMultiHybridHat εσ εE εO εEG εOG πT => exact MultiHybrid.Timed.AnswerSizeLe.zero πT
  | comp T₁ T₂ ih₁ _ => exact ih₁
  | mapPorts T f g ih => exact ih

/-- The size-graded time bound `a`, `b`, `c` of a costed simulator with the sizes `sE` of its
outer events and `sO` of its answers: a costed multi-call simulator has a size-graded time bound
on some invariant, through the erasure maps of the ports for one on costed events; the outer
factor of a costed composite has a size-graded time bound with a size `sM` on the answers of the
inner factor, the inner factor one with the size `0` on its events and answers of size `sM` at
most the times of its steps, with constants that sum to at most `a`, `b` and `c`; a relabelled
simulator has the size-graded time bound of its simulator at a size on its events that the
relabelling does not increase. -/
def TimeBoundSized : {E O EG OG : Type} → {V : PubView E O} → {W : PubView EG OG} →
    Simulator.Timed E O EG OG V W → (E → ℕ) → (OG → ℕ) → ℕ → ℕ → ℕ → Prop
  | _, _, _, _, _, _, .ofMultiHybrid (σ := σ) πT, sE, sO, a, b, c =>
    ∃ Inv : ℕ → σ → Prop, πT.TimeBoundSized Inv sE sO a b c
  | _, _, _, _, _, _, .ofMultiHybridHat (σHat := σHat) _ εE _ _ εOG πT, sE, sO, a, b, c =>
    ∃ Inv : ℕ → σHat → Prop,
      πT.TimeBoundSized Inv (fun e => sE (εE e)) (fun o => sO (εOG o)) a b c
  | _, _, _, _, _, _, .comp (OM := OM) T₁ T₂, sE, sO, a, b, c =>
    ∃ (sM : OM → ℕ) (a₁ b₁ c₁ a₂ b₂ c₂ : ℕ),
    TimeBoundSized T₁ sE sM a₁ b₁ c₁ ∧ TimeBoundSized T₂ (fun _ => 0) sO a₂ b₂ c₂ ∧
      AnswerSizeLe T₂ sM ∧ a₁ + a₂ ≤ a ∧ b₁ + b₂ ≤ b ∧ c₁ + c₂ ≤ c
  | _, _, _, _, _, _, .mapPorts T f _, sE, sO, a, b, c =>
    ∃ sM, (∀ e, sM (f e) ≤ sE e) ∧ TimeBoundSized T sM sO a b c

/-- A size-graded time bound of a costed simulator is a size-graded time bound of all larger
constants and sizes. -/
theorem TimeBoundSized.mono {E O EG OG : Type} {V : PubView E O} {W : PubView EG OG}
    {T : Simulator.Timed E O EG OG V W} {sE sE' : E → ℕ} {sO sO' : OG → ℕ} {a b c a' b' c' : ℕ}
    (h : T.TimeBoundSized sE sO a b c) (ha : a ≤ a') (hb : b ≤ b') (hc : c ≤ c')
    (hE : ∀ e, sE e ≤ sE' e) (hO : ∀ o, sO o ≤ sO' o) : T.TimeBoundSized sE' sO' a' b' c' := by
  induction T generalizing a b c a' b' c' with
  | ofMultiHybrid πT =>
    obtain ⟨Inv, hI⟩ := h
    exact ⟨Inv, hI.mono ha hb hc hE hO⟩
  | ofMultiHybridHat εσ εE εO εEG εOG πT =>
    obtain ⟨Inv, hI⟩ := h
    exact ⟨Inv, hI.mono ha hb hc (fun e => hE (εE e)) (fun o => hO (εOG o))⟩
  | mapPorts T f g ih =>
    obtain ⟨sM, hM, hT⟩ := h
    exact ⟨sM, fun e => (hM e).trans (hE e), ih hT ha hb hc (fun _ => le_rfl) hO⟩
  | comp T₁ T₂ ih₁ ih₂ =>
    obtain ⟨sM, a₁, b₁, c₁, a₂, b₂, c₂, h₁, h₂, hM, h3, h4, h5⟩ := h
    exact ⟨sM, a₁, b₁, c₁, a₂, b₂, c₂, ih₁ h₁ le_rfl le_rfl le_rfl hE fun _ => le_rfl,
      ih₂ h₂ le_rfl le_rfl le_rfl (fun _ => le_rfl) hO, hM, by omega, by omega, by omega⟩

/-- A graded time bound of a costed simulator is a size-graded time bound of every size, with
the constant `0` of the size. -/
theorem TimeBoundGraded.timeBoundSized {E O EG OG : Type} {V : PubView E O} {W : PubView EG OG}
    {T : Simulator.Timed E O EG OG V W} {a b : ℕ} (h : T.TimeBoundGraded a b) (sE : E → ℕ)
    (sO : OG → ℕ) : T.TimeBoundSized sE sO a b 0 := by
  induction T generalizing a b with
  | ofMultiHybrid πT =>
    obtain ⟨Inv, hI⟩ := h
    exact ⟨Inv, hI.timeBoundSized _ _ 0⟩
  | ofMultiHybridHat εσ εE εO εEG εOG πT =>
    obtain ⟨Inv, hI⟩ := h
    exact ⟨Inv, hI.timeBoundSized _ _ 0⟩
  | mapPorts T f g ih => exact ⟨fun _ => 0, fun _ => Nat.zero_le _, ih h _ sO⟩
  | comp T₁ T₂ ih₁ ih₂ =>
    obtain ⟨a₁, b₁, a₂, b₂, h₁, h₂, h3, h4⟩ := h
    exact ⟨fun _ => 0, a₁, b₁, 0, a₂, b₂, 0, ih₁ h₁ sE _, ih₂ h₂ _ sO, AnswerSizeLe.zero T₂, h3,
      h4, le_rfl⟩

end Simulator.Timed

namespace Simulator

variable {σ σ' E O E' O' EM OM EG OG EG' OG' : Type} {V : PubView E O} {U : PubView EM OM}
  {W : PubView EG OG} {V' : PubView E' O'} {W' : PubView EG' OG'}

/-- **Size-graded running time of a costed multi-call simulator**: a size-graded time bound of
its steps is a size-graded time bound of the costed simulator. -/
theorem ofMultiHybrid.timeBoundSized_timed {πT : MultiHybrid.Timed σ E O EG OG}
    {Inv : ℕ → σ → Prop} {sE : E → ℕ} {sO : OG → ℕ} {a b c : ℕ}
    (hT : πT.TimeBoundSized Inv sE sO a b c) :
    (Simulator.Timed.ofMultiHybrid πT : Simulator.Timed E O EG OG V W).TimeBoundSized sE sO
      a b c :=
  ⟨Inv, hT⟩

/-- **Size-graded running time of a costed multi-call simulator on costed states**: a
size-graded time bound of its steps at the sizes through the erasure maps of the ports is a
size-graded time bound of the costed simulator. -/
theorem ofMultiHybridHat.timeBoundSized_timed {σHat EHat OHat EGHat OGHat : Type}
    {εσ : σHat → σ} {εE : EHat → E} {εO : OHat → O} {εEG : EGHat → EG} {εOG : OGHat → OG}
    {πT : MultiHybrid.Timed σHat EHat OHat EGHat OGHat} {Inv : ℕ → σHat → Prop} {sE : E → ℕ}
    {sO : OG → ℕ} {a b c : ℕ}
    (hT : πT.TimeBoundSized Inv (fun e => sE (εE e)) (fun o => sO (εOG o)) a b c) :
    (Simulator.Timed.ofMultiHybridHat εσ εE εO εEG εOG πT :
      Simulator.Timed E O EG OG V W).TimeBoundSized sE sO a b c :=
  ⟨Inv, hT⟩

/-- **Size-graded running time of a relabelled costed simulator**: that of its simulator, at the
size of the relabelled events. -/
theorem mapPorts.timeBoundSized_timed {T : Simulator.Timed EM OM EG OG U W} {sM : EM → ℕ}
    {sO : OG → ℕ} {a b c : ℕ} (hT : T.TimeBoundSized sM sO a b c) (f : E → EM) (g : OM → O) :
    (Simulator.Timed.mapPorts T f g : Simulator.Timed E O EG OG V W).TimeBoundSized
      (fun e => sM (f e)) sO a b c :=
  ⟨sM, fun _ => le_rfl, hT⟩

/-- **Size-graded running time of a costed composite**: the sums of the constants of its parts,
the outer factor bounded with the size `sM` on the answers of the inner factor, whose answers
have size `sM` at most the times of the steps that return them. -/
theorem comp.timeBoundSized_timed_of_answerSizeLe {T₁ : Simulator.Timed E O EM OM V U}
    {T₂ : Simulator.Timed EM OM EG OG U W} {sE : E → ℕ} {sM : OM → ℕ} {sO : OG → ℕ}
    {a₁ b₁ c₁ a₂ b₂ c₂ : ℕ} (h₁ : T₁.TimeBoundSized sE sM a₁ b₁ c₁)
    (h₂ : T₂.TimeBoundSized (fun _ => 0) sO a₂ b₂ c₂) (hM : T₂.AnswerSizeLe sM) :
    (T₁.comp T₂).TimeBoundSized sE sO (a₁ + a₂) (b₁ + b₂) (c₁ + c₂) :=
  ⟨sM, a₁, b₁, c₁, a₂, b₂, c₂, h₁, h₂, hM, le_rfl, le_rfl, le_rfl⟩

/-- **Size-graded running time of a costed composite** at the size `0` on the answers of the
inner factor: the sums of the constants of its parts. This is the form `derive_simulator`
applies. -/
theorem comp.timeBoundSized_timed {T₁ : Simulator.Timed E O EM OM V U}
    {T₂ : Simulator.Timed EM OM EG OG U W} {sE : E → ℕ} {sO : OG → ℕ} {a₁ b₁ c₁ a₂ b₂ c₂ : ℕ}
    (h₁ : T₁.TimeBoundSized sE (fun _ => 0) a₁ b₁ c₁)
    (h₂ : T₂.TimeBoundSized (fun _ => 0) sO a₂ b₂ c₂) :
    (T₁.comp T₂).TimeBoundSized sE sO (a₁ + a₂) (b₁ + b₂) (c₁ + c₂) :=
  comp.timeBoundSized_timed_of_answerSizeLe h₁ h₂ (Simulator.Timed.AnswerSizeLe.zero T₂)

/-- **Size-graded running time of the costed tensor**: if `πT` and `π'T` erase to `π` and `π'`
and have size-graded time bounds `a`, `b`, `c` and `a'`, `b'`, `c'`, the costed tensor has the
size-graded time bound `max a a' + 7`, `max b b'`, `max c c'`. -/
theorem tensor.timeBoundSized_timed {π : MultiHybrid σ E O EG OG}
    {π' : MultiHybrid σ' E' O' EG' OG'} {πT : MultiHybrid.Timed σ E O EG OG}
    {π'T : MultiHybrid.Timed σ' E' O' EG' OG'} {Inv : ℕ → σ → Prop} {Inv' : ℕ → σ' → Prop}
    {sE : E → ℕ} {sO : OG → ℕ} {sE' : E' → ℕ} {sO' : OG' → ℕ} {a b c a' b' c' : ℕ}
    (hE : πT.Erases π) (hE' : π'T.Erases π') (hT : πT.TimeBoundSized Inv sE sO a b c)
    (hT' : π'T.TimeBoundSized Inv' sE' sO' a' b' c') :
    (tensor.timed (V := V) (W := W) (V' := V') (W' := W') π π' πT π'T).TimeBoundSized
      (Sum.elim sE sE') (Sum.elim sO sO') (max a a' + 7) (max b b') (max c c') := by
  obtain ⟨_, _, _, rfl⟩ := hE
  obtain ⟨_, _, _, rfl⟩ := hE'
  exact ofMultiHybrid.timeBoundSized_timed
    (MultiHybrid.Timed.tensor_timeBoundSized _ _ rfl rfl hT hT')

end Simulator

end CatCrypt.Crypto.UCTransparent
