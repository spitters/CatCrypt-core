/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCInterleave

/-!
# Activations of multi-call hybrids, one call at a time

An activation of a multi-call hybrid `π` against a subroutine `X` (`MultiHybrid.withSub`,
`MultiHybrid.stepFuel`) is the start of `π`, at most `n + 1` calls of `X`, each answered by
`resume` (or by `finish` at the last allowed call), and the output. When the start, a call of
`X` or a resumption is deterministic (`SPComp.pure`), the activation is the rest of the
activation from its value. The lemmas of this file state this one call at a time, for any `π`,
`X` and fuel, so that an activation is evaluated call by call, each call simplified alone,
without simplifying the rest of the activation for an unknown answer first.

## Main results

* `MultiHybrid.withSub_step_of_start`, `MultiHybrid.stepFuel_of_start`: a deterministic start.
* `MultiHybrid.drive_succ_of_step`, `MultiHybrid.drive_zero_of_step`: a deterministic call.
* `MultiHybrid.drive_succ_of_step_of_resume`: a deterministic call and resumption.
* `MultiHybrid.drive_output`: the output ends the activation.
* `MultiHybrid.idSim_start`, `MultiHybrid.idSim_resume`, `MultiHybrid.idSim_finish`,
  `MultiHybrid.idSim_drive`: the forwarding hybrid, whose activation is one call at any fuel.

The forwarding hybrid `idSim` is rewritten by its start, resumption and finish rather than
unfolded, so that its activation at a fuel that is not a numeral (the maximum with the fuel of an
unknown hybrid beside it in a tensor) is still one call (`idSim_drive`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent.MultiHybrid

open CatCrypt.Core

variable {σ τ E O EG OG : Type} (π : MultiHybrid σ E O EG OG) (X : Sys τ EG OG)

/-- An activation over `X` whose start is deterministic, with value `r`, is the rest of the
activation from `r`. -/
theorem withSub_step_of_start (s : σ) (t : τ) (e : E) (r : σ × (EG ⊕ O))
    (h : π.start s e = SPComp.pure r) :
    (π.withSub X).step (s, t) e =
      SPComp.bind (π.drive X π.fuel r.1 r.2 t) fun p => SPComp.pure ((p.1, p.2.1), p.2.2) := by
  simp only [withSub, h, SPComp.pure_bind]

/-- An activation with `n` calls after the first whose start is deterministic, with value `r`,
is the rest of the activation from `r`. -/
theorem stepFuel_of_start (n : ℕ) (s : σ) (t : τ) (e : E) (r : σ × (EG ⊕ O))
    (h : π.start s e = SPComp.pure r) :
    π.stepFuel X n (s, t) e =
      SPComp.bind (π.drive X n r.1 r.2 t) fun p => SPComp.pure ((p.1, p.2.1), p.2.2) := by
  simp only [stepFuel, h, SPComp.pure_bind]

/-- An output of the hybrid ends the activation. -/
theorem drive_output (n : ℕ) (s : σ) (o : O) (t : τ) :
    π.drive X n s (.inr o) t = SPComp.pure (s, t, o) := by
  cases n <;> rfl

/-- A call of `X` with calls left whose answer is deterministic, with value `q`, is followed by
the resumption on the answer. -/
theorem drive_succ_of_step (n : ℕ) (s : σ) (g : EG) (t : τ) (q : τ × OG)
    (h : X.step t g = SPComp.pure q) :
    π.drive X (n + 1) s (.inl g) t =
      SPComp.bind (π.resume s q.2) fun r => π.drive X n r.1 r.2 q.1 := by
  simp only [drive, h, SPComp.pure_bind]

/-- A deterministic call of `X` with calls left followed by a deterministic resumption, with
value `r`, is the rest of the activation from `r`. -/
theorem drive_succ_of_step_of_resume (n : ℕ) (s : σ) (g : EG) (t : τ) (q : τ × OG)
    (r : σ × (EG ⊕ O)) (h : X.step t g = SPComp.pure q) (hr : π.resume s q.2 = SPComp.pure r) :
    π.drive X (n + 1) s (.inl g) t = π.drive X n r.1 r.2 q.1 := by
  simp only [drive_succ_of_step π X n s g t q h, hr, SPComp.pure_bind]

/-- The last allowed call of `X`, with deterministic answer `q`, is followed by `finish`. -/
theorem drive_zero_of_step (s : σ) (g : EG) (t : τ) (q : τ × OG)
    (h : X.step t g = SPComp.pure q) :
    π.drive X 0 s (.inl g) t =
      SPComp.bind (π.finish s q.2) fun r => SPComp.pure (r.1, q.1, r.2) := by
  simp only [drive, h, SPComp.pure_bind]

variable {E O : Type}

/-- The start of the forwarding hybrid: the event is passed to the subroutine. -/
theorem idSim_start (s : Unit) (e : E) :
    (idSim E O).start s e = SPComp.pure ((), .inl e) := rfl

/-- The resumption of the forwarding hybrid: the answer of the subroutine is the output. -/
theorem idSim_resume (s : Unit) (o : O) :
    (idSim E O).resume s o = SPComp.pure ((), .inr o) := rfl

/-- The finish of the forwarding hybrid: the answer of the subroutine is the output. -/
theorem idSim_finish (s : Unit) (o : O) : (idSim E O).finish s o = SPComp.pure ((), o) := rfl

/-- An activation of the forwarding hybrid is one call of the subroutine, at any fuel. -/
theorem idSim_drive (X : Sys τ E O) (n : ℕ) (s : Unit) (e : E) (t : τ) :
    (idSim E O).drive X n s (.inl e) t =
      SPComp.bind (X.step t e) fun q => SPComp.pure ((), q.1, q.2) := by
  cases n <;> simp [drive, idSim, SPComp.pure_bind]

end CatCrypt.Crypto.UCTransparent.MultiHybrid
