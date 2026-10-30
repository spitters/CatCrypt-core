/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCInterleave
public import CatCryptCore.Crypto.UCTransparentMultiTimed
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveTimeBound
public import CatCryptCore.Tactics.StdCosts

/-!
# Running time of the tensor of multi-call simulators

The costed form of the tensor `MultiHybrid.tensor` of `UCInterleave.lean`, derived by
`derive_reduction`, and the time theorems of its three steps, derived by `derive_time_bound`.
The steps of the components are the primitives of the derivation: the costed tensor takes the
costed steps of the components and their cost companions.

`MultiHybrid.Timed.tensor` is the costed tensor of two costed multi-call simulators, the
derived costed form with the steps and cost companions of the components taken from them. A
step of it costs the step of the component on the port of its input plus a constant.

## Main definitions

* `MultiHybrid.tensor.timed`: the derived costed form of the tensor.
* `MultiHybrid.Timed.tensor`: the costed tensor of costed multi-call simulators.

## Main results

* `MultiHybrid.tensor.erase_timed`, `MultiHybrid.tensor.start.tree.timeBound_timed`,
  `MultiHybrid.tensor.resume.tree.timeBound_timed`,
  `MultiHybrid.tensor.finish.tree.timeBound_timed`: the derived erasure and step theorems.
* `MultiHybrid.Timed.tensor_erases`: the costed tensor of costed simulators that erase to `π`
  and `π'` erases to `π.tensor π'`.
* `MultiHybrid.Timed.tensor_timeBound`: a start or resume step of the costed tensor costs the
  larger bound of the components plus `7`, a finish step the larger bound plus `3`.
-/

@[expose] public section

set_option autoImplicit false

derive_reduction CatCrypt.Crypto.UCTransparent.MultiHybrid.tensor
derive_time_bound CatCrypt.Crypto.UCTransparent.MultiHybrid.tensor.start.tree
derive_time_bound CatCrypt.Crypto.UCTransparent.MultiHybrid.tensor.resume.tree
derive_time_bound CatCrypt.Crypto.UCTransparent.MultiHybrid.tensor.finish.tree

namespace CatCrypt.Crypto.UCTransparent.MultiHybrid.Timed

open CatCrypt.Core

variable {σ σ' E O E' O' EG OG EG' OG' : Type}

/-- A costed bind of `A` behind three delays, the last carrying the step cost `C`: its time is
at most `C`, the time of `A`, a bound `T` on the times of the continuation, and `3`. -/
theorem stepTime_delay3_bind_le {α β : Type} (A : SPTree.Timed α)
    (f : α → ℕ × SPTree.Timed β) (C T : ℕ) (hf : ∀ x, SPTree.Timed.stepTime (f x) ≤ T) :
    SPTree.Timed.stepTime (SPTree.Timed.delay 1 (SPTree.Timed.delay 1
      (SPTree.Timed.delay (1 + C) (A.bind f)))) ≤ C + A.time + T + 3 := by
  have := SPTree.Timed.stepTime_bind_le A f T hf
  simp only [SPTree.Timed.stepTime, SPTree.Timed.delay] at *
  omega

/-- The costed tensor of the costed multi-call simulators `πT` and `π'T`: the costed form
`MultiHybrid.tensor.timed π π'` with the steps and cost companions of `πT` and `π'T`. -/
noncomputable def tensor (π : MultiHybrid σ E O EG OG) (π' : MultiHybrid σ' E' O' EG' OG')
    (πT : MultiHybrid.Timed σ E O EG OG) (π'T : MultiHybrid.Timed σ' E' O' EG' OG') :
    MultiHybrid.Timed (σ × σ') (E ⊕ E') (O ⊕ O') (EG ⊕ EG') (OG ⊕ OG') :=
  MultiHybrid.tensor.timed π π' πT.start πT.startCost π'T.start π'T.startCost πT.resume
    πT.resumeCost π'T.resume π'T.resumeCost πT.finish πT.finishCost π'T.finish π'T.finishCost

/-- **Erasure of the costed tensor**: the costed tensor of costed multi-call simulators that
erase to `π` and `π'` erases to `π.tensor π'`. -/
theorem tensor_erases {π : MultiHybrid σ E O EG OG} {π' : MultiHybrid σ' E' O' EG' OG'}
    {πT : MultiHybrid.Timed σ E O EG OG} {π'T : MultiHybrid.Timed σ' E' O' EG' OG'}
    (hT : πT.Erases π) (hT' : π'T.Erases π') : (tensor π π' πT π'T).Erases (π.tensor π') := by
  obtain ⟨_, _, _, rfl⟩ := hT
  obtain ⟨_, _, _, rfl⟩ := hT'
  exact MultiHybrid.tensor.erase_timed _ _ _ _ _ _ _ _ _ _ _ _ _ _ (fun _ _ => rfl)
    (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)

set_option linter.auxLemma false in
/-- **Running time of the costed tensor**: if the steps of `πT` cost at most `a`, `b`, `c` and
those of `π'T` at most `a'`, `b'`, `c'`, a start or resume step of the costed tensor costs at
most the larger bound plus `7`, and a finish step at most the larger bound plus `3`. -/
theorem tensor_timeBound (π : MultiHybrid σ E O EG OG) (π' : MultiHybrid σ' E' O' EG' OG')
    {πT : MultiHybrid.Timed σ E O EG OG} {π'T : MultiHybrid.Timed σ' E' O' EG' OG'}
    {a b c a' b' c' : ℕ} (hT : πT.TimeBound a b c) (hT' : π'T.TimeBound a' b' c') :
    (tensor π π' πT π'T).TimeBound (max a a' + 7) (max b b' + 7) (max c c' + 3) := by
  obtain ⟨h1, h2, h3⟩ := hT
  obtain ⟨h1', h2', h3'⟩ := hT'
  simp only [SPTree.Timed.stepTime] at h1 h2 h3 h1' h2' h3'
  refine ⟨fun s e => ?_, fun s o => ?_, fun s o => ?_⟩
  · rcases e with e | e <;>
      simp only [tensor, MultiHybrid.tensor.timed, MultiHybrid.tensor.start.tree.timed,
        MultiHybrid.tensor.start.tree.match_1.timed] <;>
      refine le_trans (stepTime_delay3_bind_le _ _ _ 4 ?_) ?_ <;>
      first
        | (rintro ⟨_, _ | _⟩ <;> simp [SPTree.Timed.stepTime, SPTree.Timed.time_ret])
        | grind
  · rcases o with o | o <;>
      simp only [tensor, MultiHybrid.tensor.timed, MultiHybrid.tensor.resume.tree.timed,
        MultiHybrid.tensor.resume.tree.match_1.timed] <;>
      refine le_trans (stepTime_delay3_bind_le _ _ _ 4 ?_) ?_ <;>
      first
        | (rintro ⟨_, _ | _⟩ <;> simp [SPTree.Timed.stepTime, SPTree.Timed.time_ret])
        | grind
  · rcases o with o | o <;>
      simp only [tensor, MultiHybrid.tensor.timed, MultiHybrid.tensor.finish.tree.timed,
        MultiHybrid.tensor.finish.tree.match_1.timed] <;>
      refine le_trans (stepTime_delay3_bind_le _ _ _ 0 ?_) ?_ <;>
      first
        | (intro x; simp [SPTree.Timed.stepTime, SPTree.Timed.time_ret])
        | grind

end CatCrypt.Crypto.UCTransparent.MultiHybrid.Timed
