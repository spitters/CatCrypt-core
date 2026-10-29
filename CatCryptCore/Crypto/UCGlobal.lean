/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCParallel

/-!
# Shared global functionalities: the merge as an open system

A global functionality `G : Sys τ EG OG` is shared by several sessions through the merge
`G.merge` (`Sys.merge`), which serves two ports with one copy of `G`. This file makes the merge
an open system and states its comonoid laws at distance `0`.

A port relabelling `X.relabel fe fo` runs the system `X` on the event `(fe e).2` and maps its
answer by `fo (fe e).1`, where the tag `(fe e).1` records the port of the event. It is the open
system `Open.relabel k₀ fe fo` whose reduced environment remembers the tag of the pending event
(`Hybrid.relabel`, a hybrid without state change other than the tag). The merge is the open
system `Open.merge EG OG` with the tag `Bool`. A relabelling by maps that ignore the tag is
`Sys.mapPorts`.

The merge is coassociative, cocommutative and counital up to relabelling of the ports: merging
one port of `G.merge` gives the three-port merge `G.merge3`, in either bracketing up to the
associator (`realizes_mergeRight_merge`, `realizes_mergeLeft_merge`); swapping the ports of
`G.merge` gives `G.merge` (`realizes_merge_swap`); and one port of `G.merge` alone is `G`
(`realizes_merge_counitL`, `realizes_merge_counitR`). Each law is a pair of realizations at
distance `0`.

The tensor of a multi-call hybrid `π` with the forwarding simulator over a parallel composition
is the parallel composition of `π` over the left component with the right component, at
distance `0`, for every fuel of `π` (`realizes_tensor_idSim_withSub_par` and its mirror
`realizes_idSim_tensor_withSub_par`).

## Main definitions

* `Sys.relabel`, `Sys.mapPorts`: relabelling the ports of a system.
* `Hybrid.relabel`, `Open.relabel`, `Open.mapPorts`: relabellings as open systems.
* `Open.merge`: the merge as an open system.
* `Sys.merge3`: three ports onto one system.
* `Open.mergeLeft`, `Open.mergeRight`: the merge on one port of a two-port system.

## Main results

* `Hybrid.view_relabel`: the view of a relabelled system is the view of the reduced
  environment.
* `realizes_mergeRight_merge`, `realizes_mergeLeft_merge`: coassociativity.
* `realizes_merge_swap`: cocommutativity.
* `realizes_merge_counitL`, `realizes_merge_counitR`: the counit laws.
* `realizes_tensor_idSim_withSub_par`, `realizes_idSim_tensor_withSub_par`: the tensor with the
  forwarding simulator over a parallel composition.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open scoped ENNReal

/-! ## Relabelling the ports of a system -/

namespace Sys

variable {K τ E O EG OG : Type}

/-- The system `X` on relabelled ports: the event `e` is the event `(fe e).2` of `X`, and the
answer is mapped by `fo` at the tag `(fe e).1`. -/
noncomputable def relabel (X : Sys τ EG OG) (fe : E → K × EG) (fo : K → OG → O) : Sys τ E O where
  init := X.init
  step t e := SPComp.map (fun q => (q.1, fo (fe e).1 q.2)) (X.step t (fe e).2)

/-- The system `X` on ports relabelled by the maps `f` on events and `g` on outputs. -/
noncomputable def mapPorts (X : Sys τ EG OG) (f : E → EG) (g : OG → O) : Sys τ E O :=
  X.relabel (fun e => ((), f e)) fun _ => g

end Sys

/-- Two systems with the same state, the same initial state and the same steps realize one
another at distance `0`. -/
theorem realizes_zero_of_step_eq {τ E O : Type} (R I : Sys τ E O) (hinit : R.init = I.init)
    (hstep : ∀ t e, R.step t e = I.step t e) :
    Realizes R I (fun _ _ => 0) ∧ Realizes I R (fun _ _ => 0) :=
  ⟨realizes_zero_of_stepMap R I _root_.id hinit fun t e => by
      simp [hstep, SPComp.map, SPComp.bind_pure],
    realizes_zero_of_stepMap I R _root_.id hinit.symm fun t e => by
      simp [hstep, SPComp.map, SPComp.bind_pure]⟩

namespace Hybrid

variable {K τ ζ E O EG OG : Type}

/-- The hybrid of a relabelling: the state is the tag of the last event, `pre` sends the event
`e` to `(fe e).2` and records its tag, and `post` maps the answer by `fo` at the tag. -/
noncomputable def relabel (k₀ : K) (fe : E → K × EG) (fo : K → OG → O) :
    Hybrid K E O EG OG where
  init := k₀
  pre _ e := SPComp.pure (fe e)
  post k o := SPComp.pure (k, fo k o)
  pre_noFail _ _ := SPComp.pure_noFail _
  post_noFail _ _ := SPComp.pure_noFail _

/-- **The view of a relabelled system.** If the steps of `Y` are those of `X` on ports relabelled
by `fe` and `fo`, the view of `Z` against `Y` is the view of the reduced environment
`(relabel k₀ fe fo).reduce Z` against `X`, followed by the first projection. -/
theorem view_relabel (k₀ : K) (fe : E → K × EG) (fo : K → OG → O) (X : Sys τ EG OG)
    (Y : Sys τ E O) (hinit : Y.init = X.init)
    (hY : ∀ t e, Y.step t e = SPComp.map (fun q => (q.1, fo (fe e).1 q.2)) (X.step t (fe e).2))
    (Z : Strat ζ E O) :
    view Y Z = SPComp.bind (view X ((relabel k₀ fe fo).reduce Z)) fun c => SPComp.pure c.1 := by
  rw [← view_eq_of_stepMap ((relabel k₀ fe fo).withSub X) Y Prod.snd hinit.symm ?_ Z,
    view_withSub]
  · rfl
  · intro t e
    simp [withSub, relabel, hY, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]

end Hybrid

namespace Open

variable {K E O EG OG : Type}

/-- A port relabelling as an open system: the subroutine on ports relabelled by `fe` and `fo`.
The reduced environment remembers the tag of the pending event, from the initial tag `k₀`.
Every subroutine is admissible. -/
noncomputable def relabel (k₀ : K) (fe : E → K × EG) (fo : K → OG → O) : Open E O EG OG where
  St τ := τ
  withSub X := X.relabel fe fo
  Ctx ζ := ζ × K
  reduce Z := (Hybrid.relabel k₀ fe fo).reduce Z
  proj c := SPComp.pure c.1
  Adm _ := True
  view_withSub X Z _ := Hybrid.view_relabel k₀ fe fo X _ rfl (fun _ _ => rfl) Z

/-- A relabelling by the maps `f` on events and `g` on outputs as an open system. -/
noncomputable def mapPorts (f : E → EG) (g : OG → O) : Open E O EG OG :=
  relabel () (fun e => ((), f e)) fun _ => g

/-- A realization between subroutines is a realization between their relabellings, with the
bound at the reduced environment. -/
theorem realizes_relabel {τ υ : Type} (k₀ : K) (fe : E → K × EG) (fo : K → OG → O)
    {X : Sys τ EG OG} {Y : Sys υ EG OG} {b : (ζ : Type) → Env (Strat ζ EG OG) ζ → ℝ≥0∞}
    (h : Realizes X Y b) :
    Realizes (X.relabel fe fo) (Y.relabel fe fo)
      (fun ζ Z => b (ζ × K) ((relabel k₀ fe fo).reduceEnv Z)) :=
  (relabel k₀ fe fo).realizes_withSub trivial trivial h

end Open

/-! ## The merge -/

namespace Sys

variable {τ EG OG : Type}

/-- The event map of the merge: the port of the event as a tag (`true` for the left port), and
the event of `G`. -/
def mergeEv : EG ⊕ EG → Bool × EG
  | .inl g => (true, g)
  | .inr g => (false, g)

/-- The output map of the merge: the answer of `G` on the port named by the tag. -/
def mergeOut : Bool → OG → OG ⊕ OG
  | true, o => .inl o
  | false, o => .inr o

/-- The steps of the merge are those of `G` on ports relabelled by `mergeEv` and `mergeOut`. -/
theorem merge_step_relabel (G : Sys τ EG OG) (t : τ) (e : EG ⊕ EG) :
    G.merge.step t e = SPComp.map (fun q => (q.1, mergeOut (mergeEv e).1 q.2))
      (G.step t (mergeEv e).2) := by
  rcases e with g | g <;> rfl

/-- Three ports onto one copy of `G`: an event on any port is a step of `G`, answered on the
port of the event. -/
noncomputable def merge3 (G : Sys τ EG OG) : Sys τ (EG ⊕ EG ⊕ EG) (OG ⊕ OG ⊕ OG) where
  init := G.init
  step t e := match e with
    | .inl g => SPComp.map (fun q => (q.1, .inl q.2)) (G.step t g)
    | .inr (.inl g) => SPComp.map (fun q => (q.1, .inr (.inl q.2))) (G.step t g)
    | .inr (.inr g) => SPComp.map (fun q => (q.1, .inr (.inr q.2))) (G.step t g)

end Sys

namespace Open

/-- **The merge as an open system**: two ports onto one copy of the subroutine. The reduced
environment remembers the port of the pending event; every subroutine is admissible. -/
noncomputable def merge (EG OG : Type) : Open (EG ⊕ EG) (OG ⊕ OG) EG OG where
  St τ := τ
  withSub G := G.merge
  Ctx ζ := ζ × Bool
  reduce Z := (Hybrid.relabel true Sys.mergeEv Sys.mergeOut).reduce Z
  proj c := SPComp.pure c.1
  Adm _ := True
  view_withSub G Z _ :=
    Hybrid.view_relabel true Sys.mergeEv Sys.mergeOut G _ rfl (Sys.merge_step_relabel G) Z

variable {A OA EG OG : Type}

/-- The event map of the merge on the right port: the left port is passed on, an event on
either right port goes to the right port with its tag. -/
def mergeRightEv : A ⊕ (EG ⊕ EG) → Bool × (A ⊕ EG)
  | .inl a => (true, .inl a)
  | .inr (.inl g) => (true, .inr g)
  | .inr (.inr g) => (false, .inr g)

/-- The output map of the merge on the right port. -/
def mergeRightOut : Bool → OA ⊕ OG → OA ⊕ (OG ⊕ OG)
  | _, .inl o => .inl o
  | b, .inr o => .inr (Sys.mergeOut b o)

/-- The event map of the merge on the left port. -/
def mergeLeftEv : (EG ⊕ EG) ⊕ A → Bool × (EG ⊕ A)
  | .inl (.inl g) => (true, .inl g)
  | .inl (.inr g) => (false, .inl g)
  | .inr a => (true, .inr a)

/-- The output map of the merge on the left port. -/
def mergeLeftOut : Bool → OG ⊕ OA → (OG ⊕ OG) ⊕ OA
  | b, .inl o => .inl (Sys.mergeOut b o)
  | _, .inr o => .inr o

/-- The merge on the right port of a two-port subroutine (`id ⊗ merge`). -/
noncomputable def mergeRight (A OA EG OG : Type) :
    Open (A ⊕ (EG ⊕ EG)) (OA ⊕ (OG ⊕ OG)) (A ⊕ EG) (OA ⊕ OG) :=
  relabel true mergeRightEv mergeRightOut

/-- The merge on the left port of a two-port subroutine (`merge ⊗ id`). -/
noncomputable def mergeLeft (A OA EG OG : Type) :
    Open ((EG ⊕ EG) ⊕ A) ((OG ⊕ OG) ⊕ OA) (EG ⊕ A) (OG ⊕ OA) :=
  relabel true mergeLeftEv mergeLeftOut

end Open

/-! ## The comonoid laws of the merge -/

section Laws

variable {τ EG OG : Type}

/-- **Coassociativity, right bracketing.** The merge on the right port of `G.merge` and the
three-port merge `G.merge3` realize one another at distance `0`. -/
theorem realizes_mergeRight_merge (G : Sys τ EG OG) :
    Realizes ((Open.mergeRight EG OG EG OG).withSub ((Open.merge EG OG).withSub G)) G.merge3
      (fun _ _ => 0) ∧
    Realizes G.merge3 ((Open.mergeRight EG OG EG OG).withSub ((Open.merge EG OG).withSub G))
      (fun _ _ => 0) :=
  realizes_zero_of_step_eq _ _ rfl fun t e => by
    rcases e with g | g | g <;>
      simp [Open.mergeRight, Open.relabel, Open.merge, Sys.relabel, Sys.merge, Sys.merge3,
        Open.mergeRightEv, Open.mergeRightOut, Sys.mergeOut, SPComp.map, SPComp.bind_assoc,
        SPComp.pure_bind]

/-- **Coassociativity, left bracketing.** The merge on the left port of `G.merge` and the
three-port merge `G.merge3` on ports relabelled by the associator realize one another at
distance `0`. -/
theorem realizes_mergeLeft_merge (G : Sys τ EG OG) :
    Realizes ((Open.mergeLeft EG OG EG OG).withSub ((Open.merge EG OG).withSub G))
      (G.merge3.mapPorts (Equiv.sumAssoc EG EG EG) (Equiv.sumAssoc OG OG OG).symm)
      (fun _ _ => 0) ∧
    Realizes (G.merge3.mapPorts (Equiv.sumAssoc EG EG EG) (Equiv.sumAssoc OG OG OG).symm)
      ((Open.mergeLeft EG OG EG OG).withSub ((Open.merge EG OG).withSub G)) (fun _ _ => 0) :=
  realizes_zero_of_step_eq _ _ rfl fun t e => by
    rcases e with (g | g) | g <;>
      simp [Open.mergeLeft, Open.relabel, Open.merge, Sys.relabel, Sys.mapPorts, Sys.merge,
        Sys.merge3, Open.mergeLeftEv, Open.mergeLeftOut, Sys.mergeOut, SPComp.map,
        SPComp.bind_assoc, SPComp.pure_bind]

/-- **Cocommutativity.** The merge on swapped ports and the merge realize one another at
distance `0`. -/
theorem realizes_merge_swap (G : Sys τ EG OG) :
    Realizes (G.merge.mapPorts Sum.swap Sum.swap) G.merge (fun _ _ => 0) ∧
    Realizes G.merge (G.merge.mapPorts Sum.swap Sum.swap) (fun _ _ => 0) :=
  realizes_zero_of_step_eq _ _ rfl fun t e => by
    rcases e with g | g <;>
      simp [Sys.relabel, Sys.mapPorts, Sys.merge, SPComp.map, SPComp.bind_assoc,
        SPComp.pure_bind]

/-- **Counit, left port.** The left port of the merge alone and `G` realize one another at
distance `0`. -/
theorem realizes_merge_counitL (G : Sys τ EG OG) :
    Realizes (G.merge.mapPorts Sum.inl (Sum.elim _root_.id _root_.id)) G (fun _ _ => 0) ∧
    Realizes G (G.merge.mapPorts Sum.inl (Sum.elim _root_.id _root_.id)) (fun _ _ => 0) :=
  realizes_zero_of_step_eq _ _ rfl fun t g => by
    simp [Sys.relabel, Sys.mapPorts, Sys.merge, SPComp.map, SPComp.bind_assoc,
      SPComp.pure_bind, SPComp.bind_pure]

/-- **Counit, right port.** The right port of the merge alone and `G` realize one another at
distance `0`. -/
theorem realizes_merge_counitR (G : Sys τ EG OG) :
    Realizes (G.merge.mapPorts Sum.inr (Sum.elim _root_.id _root_.id)) G (fun _ _ => 0) ∧
    Realizes G (G.merge.mapPorts Sum.inr (Sum.elim _root_.id _root_.id)) (fun _ _ => 0) :=
  realizes_zero_of_step_eq _ _ rfl fun t g => by
    simp [Sys.relabel, Sys.mapPorts, Sys.merge, SPComp.map, SPComp.bind_assoc,
      SPComp.pure_bind, SPComp.bind_pure]

end Laws

/-! ## The tensor with the forwarding simulator over a parallel composition -/

namespace MultiHybrid

variable {σ τ υ E O EG OG E' O' : Type}

/-- **Tensor with the forwarding simulator, right.** The tensor of `π` with the forwarding
simulator over the parallel composition of `X` and `Y` and the parallel composition of `π` over
`X` with `Y` realize each other at distance `0`, for every fuel of `π`. -/
theorem realizes_tensor_idSim_withSub_par (π : MultiHybrid σ E O EG OG) (X : Sys τ EG OG)
    (Y : Sys υ E' O') :
    Realizes ((π.tensor (idSim E' O')).withSub (X.par Y)) ((π.withSub X).par Y)
      (fun _ _ => 0) := by
  have hL : ∀ t g, (X.par Y).step t (.inl g) =
      SPComp.map (fun q => (q.1, .inl q.2)) ((X.onFst Y.init).step t g) := by
    intro t g
    simp [Sys.onFst, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  have hR : ∀ t g, (X.par Y).step t (.inr g) =
      SPComp.map (fun q => (q.1, .inr q.2)) ((Y.onSnd X.init).step t g) := by
    intro t g
    simp [Sys.onSnd, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  refine realizes_zero_of_stepMap _ _ (fun p => ((p.1.1, p.2.1), p.2.2)) rfl ?_
  rintro ⟨⟨s, u⟩, ⟨x, y⟩⟩ (e | e)
  · rw [tensor_withSub_step_inl π (idSim E' O') (X.par Y) (X.onFst Y.init) hL s u (x, y) e,
      stepFuel_onFst]
    simp [withSub, stepFuel, idSim, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  · rw [tensor_withSub_step_inr π (idSim E' O') (X.par Y) (Y.onSnd X.init) hR s u (x, y) e,
      idSim_stepFuel]
    simp [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]

/-- **Tensor with the forwarding simulator, left.** The tensor of the forwarding simulator with
`π'` over the parallel composition of `X` and `Y` and the parallel composition of `X` with `π'`
over `Y` realize each other at distance `0`, for every fuel of `π'`. -/
theorem realizes_idSim_tensor_withSub_par (π' : MultiHybrid σ E' O' EG OG) (X : Sys τ E O)
    (Y : Sys υ EG OG) :
    Realizes (((idSim E O).tensor π').withSub (X.par Y)) (X.par (π'.withSub Y))
      (fun _ _ => 0) := by
  have hL : ∀ t g, (X.par Y).step t (.inl g) =
      SPComp.map (fun q => (q.1, .inl q.2)) ((X.onFst Y.init).step t g) := by
    intro t g
    simp [Sys.onFst, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  have hR : ∀ t g, (X.par Y).step t (.inr g) =
      SPComp.map (fun q => (q.1, .inr q.2)) ((Y.onSnd X.init).step t g) := by
    intro t g
    simp [Sys.onSnd, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  refine realizes_zero_of_stepMap _ _ (fun p => (p.2.1, (p.1.2, p.2.2))) rfl ?_
  rintro ⟨⟨u, s⟩, ⟨x, y⟩⟩ (e | e)
  · rw [tensor_withSub_step_inl (idSim E O) π' (X.par Y) (X.onFst Y.init) hL u s (x, y) e,
      idSim_stepFuel]
    simp [SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  · rw [tensor_withSub_step_inr (idSim E O) π' (X.par Y) (Y.onSnd X.init) hR u s (x, y) e,
      stepFuel_onSnd]
    simp [withSub, stepFuel, idSim, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]

end MultiHybrid

end CatCrypt.Crypto.UCTransparent
