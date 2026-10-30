/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCFeedback
public import CatCryptCore.Crypto.UCGlobal

/-!
# Activation on delivery: the wake closure

A system `R` on the interface `((EH ⊕ W) ⊕ EA, OH ⊕ OA)` has an honest port that accepts, beside
the honest events `EH`, the wake events `W`, which name a recipient and carry no value. The wake
closure `R.wakeClose dlv cut` is a system on `(EH ⊕ EA, OH ⊕ OA)`: an adversary event `a` with
`dlv a = some w` is a delivery to the recipient `w`; `R` takes its step on `a`, and its answer
is replaced by the wake `w`, which activates `R` on its honest port with the event `w` in the
same outer activation. The output of that activation is the output of `R` on the wake. The
construction tags each event by `wakeEv dlv` with `Sys.relabel` and closes the wire `W` by
`Sys.loopback` with fuel `1`; the cut-off map `cut` answers a wake that would need a second
pass. The woken party reads a delivered value by its own poll of the subroutine, so the wire
carries recipients only.

The simulator `Simulator.wakeClose S` is the same construction over the simulator `S`: the
relabelling hybrid `wakeHybrid dlv`, then the feedback hybrid. Its views: the inner simulator
`S` is opaque for the honest view `VH.wake W` (wakes public, honest values related by `VH`) and
the adversary view `VA`; the closure is opaque for `VH.sum VA` when `dlv` takes equal values on
adversary events related by `VA`.

## Main definitions

* `PubView.wake`: the honest view with public wakes.
* `wakeEv`, `wakeOut`: the tagging of deliveries and the replacement of their answers.
* `wakeHybrid`: the relabelling by `wakeEv` and `wakeOut` as a multi-call hybrid.
* `Sys.wakeClose`: the wake closure of a system.
* `Simulator.wakeClose`: the wake closure of a simulator.

## Main results

* `MultiHybrid.relabel_opaque`: the relabelling hybrid is opaque when its event map preserves
  the view and the tag, and its output map preserves the view at every tag.
* `wakeHybrid_opaque`: the relabelling hybrid of the wake closure is opaque from
  `VH.wake W` and `VA` to `VH.sum VA` with the equality view on wakes.
* `MultiHybrid.drive_stepMap`, `MultiHybrid.withSub_stepMap`: a state map between subroutines
  that commutes with their steps commutes with a multi-call hybrid running with them.
* `RealizesSim.wakeClose`: if `R` realizes `I` behind the simulator `S` with bound `b`, then the
  wake closure of `R` realizes `I` behind `Simulator.wakeClose S`, with bound `b` at the reduced
  environment of the feedback hybrid and the relabelling.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open CatCrypt.Relational
open scoped ENNReal

/-! ## State maps through a multi-call hybrid -/

namespace MultiHybrid

variable {σ τ υ E O EG OG : Type}

/-- The rest of an activation commutes with a state map `f` between subroutines whose steps
commute with `f`. -/
theorem drive_stepMap (π : MultiHybrid σ E O EG OG) {X : Sys τ EG OG} {Y : Sys υ EG OG}
    (f : τ → υ)
    (hstep : ∀ t g, SPComp.map (fun p => (f p.1, p.2)) (X.step t g) = Y.step (f t) g) :
    ∀ (n : ℕ) (s : σ) (d : EG ⊕ O) (t : τ),
      SPComp.map (fun p => (p.1, f p.2.1, p.2.2)) (π.drive X n s d t) = π.drive Y n s d (f t) := by
  intro n
  induction n with
  | zero =>
    rintro s (g | o) t
    · simp only [drive, ← hstep, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
    · simp only [drive, SPComp.map, SPComp.pure_bind]
  | succ n ih =>
    rintro s (g | o) t
    · simp only [drive, ← hstep, ← ih, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
    · simp only [drive, SPComp.map, SPComp.pure_bind]

/-- A step of `π` running with `X` commutes with a state map `f` from `X` to `Y` whose steps
commute with `f`. -/
theorem withSub_stepMap (π : MultiHybrid σ E O EG OG) {X : Sys τ EG OG} {Y : Sys υ EG OG}
    (f : τ → υ)
    (hstep : ∀ t g, SPComp.map (fun p => (f p.1, p.2)) (X.step t g) = Y.step (f t) g)
    (t : σ × τ) (e : E) :
    SPComp.map (fun p => ((p.1.1, f p.1.2), p.2)) ((π.withSub X).step t e) =
      (π.withSub Y).step (t.1, f t.2) e := by
  simp only [withSub, ← drive_stepMap π f hstep, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]

/-- **Opacity of a relabelling.** The relabelling hybrid is opaque from `W` to `V` when the
event map `fe` sends events related by `V.ev` to equal tags and to events related by `W.ev`,
and the output map `fo` sends outputs related by `W.out` to outputs related by `V.out`. -/
theorem relabel_opaque {K : Type} (k₀ : K) (fe : E → K × EG) (fo : K → OG → O)
    (V : PubView E O) (W : PubView EG OG)
    (hfe : ∀ e e', V.ev e e' → (fe e).1 = (fe e').1 ∧ W.ev (fe e).2 (fe e').2)
    (hfo : ∀ k o o', W.out o o' → V.out (fo k o) (fo k o')) :
    (ofHybrid (Hybrid.relabel k₀ fe fo)).Opaque V W := by
  refine ⟨Eq, rfl, ?_, ?_, ?_⟩
  · rintro s _ e e' rfl he
    simp only [ofHybrid, Hybrid.relabel, SPComp.map, SPComp.pure_bind]
    exact rHoare_ret fun _ _ h => ⟨h, (hfe e e' he).1, (hfe e e' he).2⟩
  · rintro s _ o o' rfl ho
    simp only [ofHybrid, Hybrid.relabel, SPComp.map, SPComp.pure_bind]
    exact rHoare_ret fun _ _ h => ⟨h, rfl, hfo s o o' ho⟩
  · rintro s _ o o' rfl ho
    exact rHoare_ret fun _ _ h => ⟨h, rfl, hfo s o o' ho⟩

end MultiHybrid

namespace Sys

variable {K τ E O EG OG : Type}

/-- A system idle at the event `(fe e).2` with output `o` gives a relabelling idle at `e` with
output `fo (fe e).1 o`. -/
theorem idleAt_relabel {X : Sys τ EG OG} {fe : E → K × EG} {fo : K → OG → O} {e : E} {o : OG}
    (h : MultiHybrid.IdleAt X (fe e).2 o) :
    MultiHybrid.IdleAt (X.relabel fe fo) e (fo (fe e).1 o) := fun t => by
  simp only [relabel, h t, SPComp.map, SPComp.pure_bind]

/-- The loopback of the relabelling hybrid running with `X` has the view of the loopback of the
relabelling of `X`. -/
theorem view_loopback_relabel {X' : Type} {ζ : Type} (k₀ : K) (fe : E ⊕ X' → K × EG)
    (fo : K → OG → O ⊕ X') (X : Sys τ EG OG) (n : ℕ) (cut : X' → O) (Z : Strat ζ E O) :
    view (((MultiHybrid.ofHybrid (Hybrid.relabel k₀ fe fo)).withSub X).loopback n cut) Z =
      view ((X.relabel fe fo).loopback n cut) Z := by
  have hsub : ∀ t g, SPComp.map (fun p => (p.1.2, p.2))
      (((MultiHybrid.ofHybrid (Hybrid.relabel k₀ fe fo)).withSub X).step t g) =
        (X.relabel fe fo).step t.2 g := by
    intro t g
    rw [MultiHybrid.ofHybrid_withSub]
    simp [Hybrid.withSub, Hybrid.relabel, relabel, SPComp.map, SPComp.bind_assoc,
      SPComp.pure_bind]
  exact view_eq_of_stepMap _ _ (fun p => (p.1, p.2.2)) rfl
    (fun t e => MultiHybrid.withSub_stepMap _ Prod.snd hsub t e) Z

end Sys

/-! ## The wake closure -/

namespace PubView

variable {EH OH : Type}

/-- The honest view with public wakes: honest events related by `V.ev`, wake events related when
equal, outputs related by `V.out`. -/
def wake (V : PubView EH OH) (W : Type) : PubView (EH ⊕ W) OH where
  ev := Sum.LiftRel V.ev Eq
  out := V.out

end PubView

variable {EH EA OH OA W : Type}

/-- The tagging of deliveries: an adversary event `a` is tagged by its recipient `dlv a`; an
honest event and a wake are tagged `none`, and a wake `w` is the honest event `inr w`. -/
def wakeEv (dlv : EA → Option W) : (EH ⊕ EA) ⊕ W → Option W × ((EH ⊕ W) ⊕ EA)
  | .inl (.inl h) => (none, .inl (.inl h))
  | .inl (.inr a) => (dlv a, .inr a)
  | .inr w => (none, .inl (.inr w))

/-- The answer of a delivery to `w` is replaced by the wake `w` on the wire; every other answer
is an outer output. -/
def wakeOut {O : Type} : Option W → O → O ⊕ W
  | some w, _ => .inr w
  | none, o => .inl o

/-- The relabelling of the wake closure as a multi-call hybrid. -/
noncomputable def wakeHybrid (dlv : EA → Option W) :
    MultiHybrid (Option W) ((EH ⊕ EA) ⊕ W) ((OH ⊕ OA) ⊕ W) ((EH ⊕ W) ⊕ EA) (OH ⊕ OA) :=
  MultiHybrid.ofHybrid (Hybrid.relabel none (wakeEv dlv) wakeOut)

/-- **Opacity of the wake relabelling.** If `dlv` takes equal values on adversary events
related by `VA`, the relabelling hybrid is opaque from the honest view `VH.wake W` with the
adversary view `VA` to `VH.sum VA` with the equality view on wakes. -/
theorem wakeHybrid_opaque (VH : PubView EH OH) (VA : PubView EA OA) (dlv : EA → Option W)
    (hdlv : ∀ a a', VA.ev a a' → dlv a = dlv a') :
    (wakeHybrid (OH := OH) (OA := OA) dlv).Opaque ((VH.sum VA).sum (PubView.ofProj id id))
      ((VH.wake W).sum VA) := by
  refine MultiHybrid.relabel_opaque _ _ _ _ _ ?_ ?_
  · rintro ((h | a) | w) ((h' | a') | w') he
    all_goals (simp only [wakeEv, PubView.sum, PubView.wake, PubView.ofProj] at he ⊢; grind)
  · rintro (_ | w) o o' ho
    · exact Sum.LiftRel.inl ho
    · exact Sum.LiftRel.inr rfl

/-- **The wake closure** of `R` with the delivery map `dlv` and the cut-off map `cut`: each
event tagged by `wakeEv dlv` with `Sys.relabel`, the wire of wakes closed by `Sys.loopback`
with fuel `1`. -/
noncomputable def Sys.wakeClose {τ : Type} (R : Sys τ ((EH ⊕ W) ⊕ EA) (OH ⊕ OA))
    (dlv : EA → Option W) (cut : W → OH ⊕ OA) : Sys (Unit × τ) (EH ⊕ EA) (OH ⊕ OA) :=
  (R.relabel (wakeEv dlv) wakeOut).loopback 1 cut

/-- **The wake closure of a simulator**: the feedback hybrid with fuel `1` running with the
relabelling hybrid `wakeHybrid dlv` running with `S`. It is opaque for `VH.sum VA` when `dlv`
takes equal values on adversary events related by `VA` and the outputs `cut w` are related to
themselves. -/
noncomputable def Simulator.wakeClose {EG OG : Type} {VH : PubView EH OH} {VA : PubView EA OA}
    {VG : PubView EG OG} (S : Simulator ((EH ⊕ W) ⊕ EA) (OH ⊕ OA) EG OG ((VH.wake W).sum VA) VG)
    (dlv : EA → Option W) (hdlv : ∀ a a', VA.ev a a' → dlv a = dlv a') (cut : W → OH ⊕ OA)
    (hcut : ∀ w, (VH.sum VA).out (cut w) (cut w)) :
    Simulator (EH ⊕ EA) (OH ⊕ OA) EG OG (VH.sum VA) VG :=
  ((Simulator.ofMultiHybrid (wakeHybrid dlv) (wakeHybrid_opaque VH VA dlv hdlv)).comp S).loopback
    1 cut (fun _ _ h => h) (fun w w' h => by
      change w = w' at h
      subst h
      exact hcut w)

/-- **Realization under the wake closure** (composition plumbing). If `R` realizes `I` behind
the simulator `S` with bound `b`, and `R` and `S` running with `I` are idle at the event
`(wakeEv dlv idle).2`, then the wake closure of `R` realizes `I` behind the wake closure of `S`,
with bound `b` at the reduced environment of the relabelling and of the feedback hybrid, which
runs two rounds of `R` per round of the outer environment. -/
theorem RealizesSim.wakeClose {τ υ EG OG : Type} {VH : PubView EH OH} {VA : PubView EA OA}
    {VG : PubView EG OG} {R : Sys τ ((EH ⊕ W) ⊕ EA) (OH ⊕ OA)} {I : Sys υ EG OG}
    {S : Simulator ((EH ⊕ W) ⊕ EA) (OH ⊕ OA) EG OG ((VH.wake W).sum VA) VG}
    {b : (ζ : Type) → Env (Strat ζ ((EH ⊕ W) ⊕ EA) (OH ⊕ OA)) ζ → ℝ≥0∞}
    (dlv : EA → Option W) (hdlv : ∀ a a', VA.ev a a' → dlv a = dlv a') (cut : W → OH ⊕ OA)
    (hcut : ∀ w, (VH.sum VA).out (cut w) (cut w)) (idle : (EH ⊕ EA) ⊕ W) (oR oI : OH ⊕ OA)
    (hR : MultiHybrid.IdleAt R (wakeEv dlv idle).2 oR)
    (hI : MultiHybrid.IdleAt (S.withSub I) (wakeEv dlv idle).2 oI) (h : RealizesSim R I S b) :
    RealizesSim (R.wakeClose dlv cut) I (S.wakeClose dlv hdlv cut hcut)
      (fun ζ Z => b (MultiHybrid.RState Unit ζ ((EH ⊕ EA) ⊕ W) (OH ⊕ OA) × Option W)
        ((Open.relabel none (wakeEv dlv) wakeOut).reduceEnv
          ((MultiHybrid.fbHybrid 1 cut).reduceEnv idle Z))) := by
  have h₁ := Open.realizes_relabel (none : Option W) (wakeEv dlv) wakeOut h
  have h₂ := Realizes.loopback idle _ _ (Sys.idleAt_relabel (fo := wakeOut) hR)
    (Sys.idleAt_relabel (fo := wakeOut) hI) h₁ 1 cut
  intro ζ
  have hv : (view ((S.wakeClose dlv hdlv cut hcut).withSub I) : Strat ζ _ _ → _) =
      view (((S.withSub I).relabel (wakeEv dlv) wakeOut).loopback 1 cut) :=
    funext fun Z => Sys.view_loopback_relabel _ _ _ _ _ _ Z
  change DistC _ (view ((S.wakeClose dlv hdlv cut hcut).withSub I)) _
  rw [hv]
  exact h₂ ζ

end CatCrypt.Crypto.UCTransparent
