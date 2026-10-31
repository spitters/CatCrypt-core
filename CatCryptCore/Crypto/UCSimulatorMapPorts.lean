/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCSimulator
public import CatCryptCore.Crypto.UCGlobal

/-!
# Simulators on relabelled outer ports

`Simulator.mapPorts`: a bundled simulator of `UCSimulator.lean` running with the subroutine, on
outer ports relabelled by maps of events and outputs that respect the views. Its opacity is
`Sys.Opaque.mapPorts`: a system opaque for `W` is opaque for `V` on ports relabelled by maps that
send related events to related events and related outputs to related outputs.

## Main definitions

* `Simulator.mapPorts`: a simulator on relabelled outer ports.

## Main results

* `Sys.Opaque.mapPorts`: opacity is preserved by relabelling the ports.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CatCrypt.Relational

namespace Sys

variable {τ E O EG OG : Type}

/-- A system opaque for `W` is opaque for `V` on ports relabelled by `f` and `g`, when `f` sends
events related by `V` to events related by `W` and `g` sends outputs related by `W` to outputs
related by `V`. -/
theorem Opaque.mapPorts {X : Sys τ EG OG} {V : PubView E O} {W : PubView EG OG}
    (h : X.Opaque W) (f : E → EG) (g : OG → O) (hf : ∀ e e', V.ev e e' → W.ev (f e) (f e'))
    (hg : ∀ o o', W.out o o' → V.out (g o) (g o')) : (X.mapPorts f g).Opaque V := by
  obtain ⟨T, hT⟩ := h
  refine ⟨T, hT.init, fun t t' e e' ht he => ?_⟩
  simp only [Sys.mapPorts, Sys.relabel, SPComp.map]
  exact rHoare_bind (hT.step t t' (f e) (f e') ht (hf e e' he)) fun _ _ =>
    rHoare_ret fun _ _ hp => ⟨hp.1, hp.2.1, hg _ _ hp.2.2⟩

end Sys

namespace Simulator

variable {E O EM OM EG OG : Type} {V : PubView E O} {U : PubView EM OM} {W : PubView EG OG}

/-- **A simulator on relabelled outer ports**: `S` running with the subroutine, on outer ports
relabelled by `f` and `g`. -/
noncomputable def mapPorts (S : Simulator EM OM EG OG U W) (f : E → EM) (g : OM → O)
    (hf : ∀ e e', V.ev e e' → U.ev (f e) (f e'))
    (hg : ∀ o o', U.out o o' → V.out (g o) (g o')) : Simulator E O EG OG V W where
  St := S.St
  withSub X := (S.withSub X).mapPorts f g
  isOpaque X hX := (S.isOpaque X hX).mapPorts f g hf hg

end Simulator

end CatCrypt.Crypto.UCTransparent
