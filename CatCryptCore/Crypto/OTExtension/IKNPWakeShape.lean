/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OTExtension.IKNPWake
public import CatCryptCore.Crypto.UCGlobal
public import CatCryptCore.Crypto.UCSimulatorMapPorts
public import CatCryptCore.Examples.GroupParam

/-!
# IKNP over scheduled base OTs: the protocol shape for composition

The IKNP protocol of `OTExtension/IKNPWake.lean` draws its randomness `(T, s)` in a lazily keyed
system around the whole protocol (`iknpW`). For modular composition the protocol has to be a
multi-call hybrid over the base OTs beside the channel, with no key outside it. This module moves
the draw into the parties and supplies the relabellings that substitute a one-transfer OT for a
base OT.

**The key moves into the party.** For a family `π k` of multi-call hybrids indexed by a key, the
hybrid `MultiHybrid.lazyKey π k₀ μ u` keeps an optional key in its state, draws it from `μ` at the
first activation that reads it (`u`), and runs `π k` with it, and `π k₀` before. Running with a
subroutine `X`, it is the lazily keyed system of the family `(π k).withSub X`
(`MultiHybrid.view_lazyKey_withSub`); it commutes with the tensor by a hybrid that reads no key
(`MultiHybrid.lazyKey_tensor_withSub_step`). For IKNP, `iknpW` has the view of the parties with
their own draw over the base OTs beside the channel (`view_iknpW_eq_lazy`).

**Relabelling.** A realization behind a simulator is a realization of the relabelled real system
behind the relabelled simulator (`RealizesSim.mapPorts`). A realization behind a multi-call
simulator carries over to an ideal system related by a state map (`RealizesSim.subst_stepMap`).
The scheduled transfer of one tuple `Fin 1 → X` is the scheduled transfer of `X` relabelled
(`FOTSched.one_stepMap`).

**Encoding.** The columns `Fin m → Bool` are encoded into the group of `gp` through an embedding
into the scalars and decoded by the inverse function (`bitsDecode_bitsCode`); an embedding exists
when `2 ^ m` is at most the number of scalars (`bitsEmb_nonempty`).

## Main definitions

* `MultiHybrid.lazyKey`: a keyed family of hybrids with the key drawn in the hybrid's state.
* `MultiHybrid.keyedWithSub`: the keyed family running with a subroutine, as a keyed system.
* `IKNPWake.partyLazy`, `IKNPWake.realLazyW`: the IKNP parties with their own draw, and the
  protocol over them.
* `bitsCode`, `bitsDecode`: the encoding of columns into the group.

## Main results

* `MultiHybrid.withSub_hybMap`: a state map between hybrids commutes with their steps.
* `MultiHybrid.view_lazyKey_withSub`: the drawing hybrid is the lazily keyed system.
* `IKNPWake.view_iknpW_eq_lazy`: `iknpW` is the protocol over the drawing parties.
* `RealizesSim.mapPorts`, `RealizesSim.subst_stepMap`, `RealizesSim.of_mapPorts_sub`.
* `FOTSched.one_stepMap`, `bitsDecode_bitsCode`, `bitsEmb_nonempty`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open CatCrypt.NonUniform CatCrypt.Relational
open scoped ENNReal

/-- Sampling from a `PMF` never fails. -/
private theorem sampleFrom_ofPMF_noFail {α : Type} (μ : PMF α) :
    SPComp.NoFail (sampleFrom (ofPMF μ)) := by
  intro h
  simp only [sampleFrom_apply, SDistr.bind, PMF.bind_apply]
  refine ENNReal.tsum_eq_zero.2 fun o => ?_
  rcases o with _ | a
  · simp
  · simp [SDistr.pure, PMF.pure_apply]

/-! ## State maps between hybrids -/

namespace MultiHybrid

variable {K σ σ₁ σ₂ σ' τ ζ E O EG OG E' O' EG' OG' : Type}

/-- The rest of an activation commutes with a state map `h` between hybrids whose resumptions
and finishes commute with `h`. -/
theorem drive_hybMap (π₁ : MultiHybrid σ₁ E O EG OG) (π₂ : MultiHybrid σ₂ E O EG OG)
    (h : σ₁ → σ₂)
    (hres : ∀ s o, SPComp.map (fun r => (h r.1, r.2)) (π₁.resume s o) = π₂.resume (h s) o)
    (hfin : ∀ s o, SPComp.map (fun r => (h r.1, r.2)) (π₁.finish s o) = π₂.finish (h s) o)
    (X : Sys τ EG OG) :
    ∀ (n : ℕ) (s : σ₁) (d : EG ⊕ O) (t : τ),
      SPComp.map (fun p => (h p.1, p.2)) (π₁.drive X n s d t) = π₂.drive X n (h s) d t := by
  intro n
  induction n with
  | zero =>
    rintro s (g | o) t
    · simp only [drive, ← hfin, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
    · simp only [drive, SPComp.map, SPComp.pure_bind]
  | succ n ih =>
    rintro s (g | o) t
    · simp only [drive, ← hres, ← ih, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
    · simp only [drive, SPComp.map, SPComp.pure_bind]

/-- **State maps between hybrids.** A step of `π₁` running with `X` commutes with a state map `h`
to `π₂` of the same fuel whose starts, resumptions and finishes commute with `h`. -/
theorem withSub_hybMap (π₁ : MultiHybrid σ₁ E O EG OG) (π₂ : MultiHybrid σ₂ E O EG OG)
    (h : σ₁ → σ₂) (hfuel : π₁.fuel = π₂.fuel)
    (hstart : ∀ s e, SPComp.map (fun r => (h r.1, r.2)) (π₁.start s e) = π₂.start (h s) e)
    (hres : ∀ s o, SPComp.map (fun r => (h r.1, r.2)) (π₁.resume s o) = π₂.resume (h s) o)
    (hfin : ∀ s o, SPComp.map (fun r => (h r.1, r.2)) (π₁.finish s o) = π₂.finish (h s) o)
    (X : Sys τ EG OG) (t : σ₁ × τ) (e : E) :
    SPComp.map (fun p => ((h p.1.1, p.1.2), p.2)) ((π₁.withSub X).step t e) =
      (π₂.withSub X).step (h t.1, t.2) e := by
  simp only [withSub, ← hstart, ← hfuel, ← drive_hybMap π₁ π₂ h hres hfin X, SPComp.map,
    SPComp.bind_assoc, SPComp.pure_bind]

/-! ## The key drawn in the hybrid -/

/-- **A keyed family of hybrids with the key drawn in the hybrid.** The state holds an optional
key. Without a key, an activation whose event `e` at the state `s` reads the key (`u s e`) draws
it from `μ` and runs `π k`; every other activation runs `π k₀`. With a key `k`, it runs `π k`. -/
noncomputable def lazyKey (π : K → MultiHybrid σ E O EG OG) (k₀ : K) (μ : PMF K)
    (u : σ → E → Bool) : MultiHybrid (Option K × σ) E O EG OG where
  init := (none, (π k₀).init)
  fuel := (π k₀).fuel
  start s e :=
    if s.1.isNone && u s.2 e then
      SPComp.bind (sampleFrom (ofPMF μ)) fun k =>
        SPComp.map (fun r => ((some k, r.1), r.2)) ((π k).start s.2 e)
    else SPComp.map (fun r => ((s.1, r.1), r.2)) ((π (s.1.getD k₀)).start s.2 e)
  resume s o := SPComp.map (fun r => ((s.1, r.1), r.2)) ((π (s.1.getD k₀)).resume s.2 o)
  finish s o := SPComp.map (fun r => ((s.1, r.1), r.2)) ((π (s.1.getD k₀)).finish s.2 o)
  start_noFail s e := by
    split
    · exact Assumptions.SPComp.bind_noFail (sampleFrom_ofPMF_noFail μ) fun k =>
        Assumptions.SPComp.bind_noFail ((π k).start_noFail _ _) fun _ => SPComp.pure_noFail _
    · exact Assumptions.SPComp.bind_noFail ((π _).start_noFail _ _) fun _ =>
        SPComp.pure_noFail _
  resume_noFail s o :=
    Assumptions.SPComp.bind_noFail ((π _).resume_noFail _ _) fun _ => SPComp.pure_noFail _
  finish_noFail s o :=
    Assumptions.SPComp.bind_noFail ((π _).finish_noFail _ _) fun _ => SPComp.pure_noFail _

/-- The keyed family `π k` running with the subroutine `X` as a keyed system: the step with key
`k` is that of `π k`, the step without key that of `π k₀`, and an activation reads the key when
`u` says so at the hybrid's state. -/
noncomputable def keyedWithSub (π : K → MultiHybrid σ E O EG OG) (k₀ : K) (u : σ → E → Bool)
    (X : Sys τ EG OG) : KeyedSys K (σ × τ) E O where
  init := ((π k₀).init, X.init)
  step k := ((π k).withSub X).step
  step₀ := ((π k₀).withSub X).step
  uses t e := u t.1 e

/-- The rest of an activation of the drawing hybrid with the key `ko` is that of `π` at the key
`ko`, or `k₀` without key. -/
theorem lazyKey_drive (π : K → MultiHybrid σ E O EG OG) (k₀ : K) (μ : PMF K)
    (u : σ → E → Bool) (X : Sys τ EG OG) (n : ℕ) (p : Option K × σ) (d : EG ⊕ O)
    (t : τ) :
    (lazyKey π k₀ μ u).drive X n p d t =
      SPComp.map (fun q => ((p.1, q.1), q.2)) ((π (p.1.getD k₀)).drive X n p.2 d t) :=
  (drive_hybMap (π (p.1.getD k₀)) (lazyKey π k₀ μ u) (fun s => (p.1, s)) (fun _ _ => rfl)
    (fun _ _ => rfl) X n p.2 d t).symm

/-- **The key moves into the hybrid**, on steps: the drawing hybrid running with `X` steps as
the lazily keyed system of the family `π k` running with `X`, up to the regrouping of the state,
when the hybrids of the family have equal fuel. -/
theorem lazyKey_withSub_step (π : K → MultiHybrid σ E O EG OG) (k₀ : K) (μ : PMF K)
    (u : σ → E → Bool) (hfuel : ∀ k, (π k).fuel = (π k₀).fuel) (X : Sys τ EG OG)
    (t : (Option K × σ) × τ) (e : E) :
    SPComp.map (fun p => ((p.1.1.1, (p.1.1.2, p.1.2)), p.2))
        (((lazyKey π k₀ μ u).withSub X).step t e) =
      ((keyedWithSub π k₀ u X).lazy μ).step (t.1.1, (t.1.2, t.2)) e := by
  obtain ⟨⟨ko, s⟩, x⟩ := t
  simp only [withSub, lazyKey_drive]
  cases ko with
  | none =>
    cases hu : u s e
    · simp [lazyKey, keyedWithSub, withSub, KeyedSys.lazy, KeyedSys.lazyStep, hu, SPComp.map,
        SPComp.bind_assoc, SPComp.pure_bind]
    · simp [lazyKey, keyedWithSub, withSub, KeyedSys.lazy, KeyedSys.lazyStep, hu, hfuel,
        SPComp.map,
        SPComp.bind_assoc, SPComp.pure_bind]
  | some k =>
    simp [lazyKey, keyedWithSub, withSub, KeyedSys.lazy, KeyedSys.lazyStep, hfuel, SPComp.map,
      SPComp.bind_assoc, SPComp.pure_bind]

/-- **The key moves into the hybrid.** The drawing hybrid running with `X` has the view of the
lazily keyed system of the family `π k` running with `X`, when the hybrids of the family have
equal fuel. -/
theorem view_lazyKey_withSub (π : K → MultiHybrid σ E O EG OG) (k₀ : K) (μ : PMF K)
    (u : σ → E → Bool) (hfuel : ∀ k, (π k).fuel = (π k₀).fuel) (X : Sys τ EG OG)
    (Z : Strat ζ E O) :
    view ((lazyKey π k₀ μ u).withSub X) Z = view ((keyedWithSub π k₀ u X).lazy μ) Z :=
  view_eq_of_stepMap _ _ (fun t => (t.1.1, (t.1.2, t.2))) rfl
    (fun t e => lazyKey_withSub_step π k₀ μ u hfuel X t e) Z

/-- The key-reading predicate of the tensor with a hybrid that reads no key: the events of the
left component read the key as `u` says, the events of the right component never. -/
def tensorUses (u : σ → E → Bool) : σ × σ' → E ⊕ E' → Bool
  | s, .inl e => u s.1 e
  | _, .inr _ => false

/-- **The drawing hybrid commutes with the tensor.** The tensor of the drawing hybrid with `ρ`
running with `X` steps as the drawing hybrid of the tensors `π k ⊗ ρ`, up to the regrouping of
the state. -/
theorem lazyKey_tensor_withSub_step (π : K → MultiHybrid σ E O EG OG)
    (ρ : MultiHybrid σ' E' O' EG' OG') (k₀ : K) (μ : PMF K) (u : σ → E → Bool)
    (X : Sys τ (EG ⊕ EG') (OG ⊕ OG')) (t : ((Option K × σ) × σ') × τ) (e : E ⊕ E') :
    SPComp.map (fun p => (((p.1.1.1.1, (p.1.1.1.2, p.1.1.2)), p.1.2), p.2))
        ((((lazyKey π k₀ μ u).tensor ρ).withSub X).step t e) =
      ((lazyKey (fun k => (π k).tensor ρ) k₀ μ (tensorUses u)).withSub X).step
        ((t.1.1.1, (t.1.1.2, t.1.2)), t.2) e := by
  refine withSub_hybMap ((lazyKey π k₀ μ u).tensor ρ)
    (lazyKey (fun k => (π k).tensor ρ) k₀ μ (tensorUses u))
    (fun s => (s.1.1, (s.1.2, s.2))) rfl ?_ ?_ ?_ X t e
  · rintro ⟨⟨ko, s⟩, s'⟩ (e | e)
    · cases ko <;> cases hu : u s e <;>
        simp [tensor, lazyKey, tensorUses, hu, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
    · cases ko <;>
        simp [tensor, lazyKey, tensorUses, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  · rintro ⟨⟨ko, s⟩, s'⟩ (o | o) <;>
      simp [tensor, lazyKey, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  · rintro ⟨⟨ko, s⟩, s'⟩ (o | o) <;>
      simp [tensor, lazyKey, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]

end MultiHybrid

/-! ## Relabelled ports -/

namespace Sys

variable {τ υ E O EG OG : Type}

/-- A state map commuting with the steps of `X` and `Y` commutes with the steps of their
relabellings. -/
theorem mapPorts_stepMap {X : Sys τ EG OG} {Y : Sys υ EG OG} (F : τ → υ)
    (hstep : ∀ t g, SPComp.map (fun p => (F p.1, p.2)) (X.step t g) = Y.step (F t) g)
    (f : E → EG) (g : OG → O) (t : τ) (e : E) :
    SPComp.map (fun p => (F p.1, p.2)) ((X.mapPorts f g).step t e) =
      (Y.mapPorts f g).step (F t) e := by
  simp only [mapPorts, relabel, ← hstep, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]

end Sys

namespace RealizesSim

variable {τ υ υ' σ E O EM OM EG OG EG' OG' : Type} {V : PubView E O} {U : PubView EM OM}
  {W : PubView EG OG}

/-- **Realization on relabelled ports.** If `R` realizes `I` behind `S` with bound `b`, then `R`
on ports relabelled by `f` and `g` realizes `I` behind `S` on the same relabelled ports, with
bound `b` at the environment reduced through the relabelling. -/
theorem mapPorts {R : Sys τ EM OM} {I : Sys υ EG OG} {S : Simulator EM OM EG OG U W}
    {b : (ζ : Type) → Env (Strat ζ EM OM) ζ → ℝ≥0∞} (f : E → EM) (g : OM → O)
    (hf : ∀ e e', V.ev e e' → U.ev (f e) (f e')) (hg : ∀ o o', U.out o o' → V.out (g o) (g o'))
    (h : RealizesSim R I S b) :
    RealizesSim (R.mapPorts f g) I (S.mapPorts f g hf hg)
      (fun ζ Z => b (ζ × Unit) ((Open.mapPorts f g).reduceEnv Z)) :=
  Open.realizes_relabel () (fun e => ((), f e)) (fun _ => g) h

/-- **Substitution of the ideal system along a state map.** If `R` realizes `X` behind the
multi-call simulator `π` with bound `b`, and a state map from `X` to `Y` sends the initial state
to the initial state and commutes with steps, then `R` realizes `Y` behind `π` with bound `b`. -/
theorem subst_stepMap {R : Sys τ E O} {X : Sys υ EG OG} {Y : Sys υ' EG OG}
    {π : MultiHybrid σ E O EG OG} {hπ : π.Opaque V W}
    {b : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞} (F : υ → υ') (hinit : F X.init = Y.init)
    (hstep : ∀ t g, SPComp.map (fun p => (F p.1, p.2)) (X.step t g) = Y.step (F t) g)
    (h : RealizesSim R X (Simulator.ofMultiHybrid π hπ) b) :
    RealizesSim R Y (Simulator.ofMultiHybrid π hπ) b := by
  intro ζ
  have hv : (view (π.withSub Y) : Strat ζ E O → SPComp ζ) = view (π.withSub X) :=
    funext fun Z => (view_eq_of_stepMap (π.withSub X) (π.withSub Y) (fun t => (t.1, F t.2))
      (by simp [MultiHybrid.withSub, hinit])
      (fun t e => MultiHybrid.withSub_stepMap π X Y F hstep t e) Z).symm
  change DistC _ (view (π.withSub Y)) _
  rw [hv]
  exact h ζ

/-- A realization behind `S` of a relabelled ideal system `I.mapPorts f g` is a realization of
`I` behind `S` composed with the relabelling. -/
theorem of_mapPorts_sub {R : Sys τ E O} {I : Sys υ EG' OG'} {S : Simulator E O EG OG V W}
    {W' : PubView EG' OG'} {b : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞} (f : EG → EG')
    (g : OG' → OG) (hf : ∀ e e', W.ev e e' → W'.ev (f e) (f e'))
    (hg : ∀ o o', W'.out o o' → W.out (g o) (g o'))
    (h : RealizesSim R (I.mapPorts f g) S b) :
    RealizesSim R I (S.comp ((Simulator.id EG' OG' W').mapPorts f g hf hg)) b :=
  h

end RealizesSim

end CatCrypt.Crypto.UCTransparent

/-! ## One transfer as a tuple of one -/

namespace CatCrypt.Crypto.OT

open CatCrypt.Core CatCrypt.Crypto.UCTransparent

namespace FOTSched

variable {X C Y : Type}

/-- The state of the transfer of tuples of one, read at the index `0`. -/
def oneSt (t : SchedSt (Fin 1 → X) (Fin 1 → C) (Fin 1 → Y)) : SchedSt X C Y :=
  ⟨t.sent.map (· 0), t.chosen.map (· 0), t.inbox.map (· 0), t.dRecv, t.dSend⟩

/-- The events of the transfer of tuples of one as events of the transfer of single values. -/
def oneEv : ((Fin 1 → X) ⊕ (Fin 1 → C)) ⊕ SchedEv → (X ⊕ C) ⊕ SchedEv
  | .inl (.inl x) => .inl (.inl (x 0))
  | .inl (.inr c) => .inl (.inr (c 0))
  | .inr a => .inr a

/-- The outputs of the transfer of single values as outputs of the transfer of tuples of one. -/
def oneOut : (Bool ⊕ Option Y) ⊕ SchedOut → (Bool ⊕ Option (Fin 1 → Y)) ⊕ SchedOut
  | .inl (.inl b) => .inl (.inl b)
  | .inl (.inr y) => .inl (.inr (y.map fun v _ => v))
  | .inr a => .inr a

/-- **One transfer as a tuple of one.** The scheduled transfer of tuples `Fin 1 → X` with the
output map applied at each index is the scheduled transfer of `X` on relabelled ports, by the
state map `oneSt`. -/
theorem one_stepMap (out : X → C → Y)
    (t : SchedSt (Fin 1 → X) (Fin 1 → C) (Fin 1 → Y))
    (e : ((Fin 1 → X) ⊕ (Fin 1 → C)) ⊕ SchedEv) :
    SPComp.map (fun p => (oneSt p.1, p.2))
        ((FOTSched (fun (x : Fin 1 → X) (c : Fin 1 → C) i => out (x i) (c i))).step t e) =
      ((FOTSched out).mapPorts oneEv oneOut).step (oneSt t) e := by
  obtain ⟨sent, chosen, inbox, dR, dS⟩ := t
  rcases e with (x | c) | a
  · cases sent <;> simp [FOTSched, sendSys, sendStep, oneSt, oneEv, oneOut, Sys.mapPorts,
      Sys.relabel, SPComp.map, SPComp.pure_bind]
  · cases inbox with
    | none => simp [FOTSched, recvSys, recvStep, oneSt, oneEv, oneOut, Sys.mapPorts,
        Sys.relabel, SPComp.map, SPComp.pure_bind]
    | some v =>
      have hv : (fun _ : Fin 1 => v 0) = v := funext fun i => by rw [Subsingleton.elim i 0]
      simp [FOTSched, recvSys, recvStep, oneSt, oneEv, oneOut, Sys.mapPorts, Sys.relabel,
        SPComp.map, SPComp.pure_bind, hv]
  · cases a <;> cases sent <;> cases chosen <;> cases dR <;>
      simp [FOTSched, schedSys, schedStep, oneSt, oneEv, oneOut, Sys.mapPorts, Sys.relabel,
        SPComp.map, SPComp.pure_bind]

/-- The state map `oneSt` sends the initial state to the initial state. -/
theorem oneSt_init : oneSt (initSt : SchedSt (Fin 1 → X) (Fin 1 → C) (Fin 1 → Y)) = initSt :=
  rfl

end FOTSched

end CatCrypt.Crypto.OT

/-! ## Columns encoded into the group -/

namespace CatCrypt.Examples

variable (gp : GroupParam) {m : ℕ}

/-- The encoding of a column into the group of `gp` through an embedding `ι` into the scalars:
the generator raised to the scalar of the column. -/
def bitsCode (ι : (Fin m → Bool) ↪ gp.Scalar) (v : Fin m → Bool) : gp.G := gp.exp (ι v)

/-- The decoding of a group element: the inverse function of `bitsCode`. -/
noncomputable def bitsDecode (ι : (Fin m → Bool) ↪ gp.Scalar) : gp.G → Fin m → Bool :=
  Function.invFun (bitsCode gp ι)

/-- **Decoding inverts encoding.** -/
theorem bitsDecode_bitsCode (ι : (Fin m → Bool) ↪ gp.Scalar) (v : Fin m → Bool) :
    bitsDecode gp ι (bitsCode gp ι v) = v :=
  Function.leftInverse_invFun (fun _ _ hab => ι.injective (gp.exp_inj _ _ hab)) v

/-- An embedding of the columns into the scalars exists when `2 ^ m` is at most the number of
scalars. -/
theorem bitsEmb_nonempty (h : 2 ^ m ≤ Fintype.card gp.Scalar) :
    Nonempty ((Fin m → Bool) ↪ gp.Scalar) :=
  Function.Embedding.nonempty_of_card_le (by simpa using h)

end CatCrypt.Examples

/-! ## IKNP with the draw in the parties -/

namespace CatCrypt.Crypto.OT.IKNPWake

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.OT.IKNPSquare

variable {κ m : ℕ} {M : Type}

/-- Whether an activation of the parties reads their randomness: an input, or any event once a
party has its input. -/
def partyUses {P : Type} (st : PSt κ m M) : (InEv m M ⊕ WakeEv κ) ⊕ P → Bool
  | .inl (.inl _) => true
  | _ => st.xo.isSome || st.ro.isSome

section Lazy

variable [AddCommGroup M] (H : Fin m → (Fin κ → Bool) → M) {P L LS LR : Type}
  (φS : IKNPSenderView κ m Unit → LS) (φR : IKNPReceiverView κ m M Unit × (Fin m → M) → LR)
  (ans : Option LS → Option LR → P → L)

/-- **The IKNP parties with their own draw**: the parties of `partyW` whose randomness `(T, s)`
is drawn uniformly in their state at the first input of a party. -/
noncomputable def partyLazy [NeZero κ] :
    MultiHybrid (Option (IKNPKey κ m) × PSt κ m M) ((InEv m M ⊕ WakeEv κ) ⊕ P) (InOut m M ⊕ L)
      (HEv κ m ⊕ ChanHEv (Msg m M)) (HOut m ⊕ ChanHOut (Msg m M)) :=
  MultiHybrid.lazyKey (partyW H φS φR ans) default (PMF.uniformFintype _) partyUses

/-- **The IKNP protocol over the drawing parties**: the parties with their own draw over the `κ`
base OTs beside the channel, the adversary ports of both forwarded, the corruption events on the
adversary port. -/
noncomputable def realLazyW [NeZero κ] :
    Sys (((Option (IKNPKey κ m) × PSt κ m M) × Unit) × SubSt κ m M)
      ((InEv m M ⊕ WakeEv κ) ⊕ (AEv κ m M ⊕ P)) (InOut m M ⊕ (AOut m M ⊕ L)) :=
  (((partyLazy H φS φR ans).tensor (MultiHybrid.idSim (AEv κ m M) (AOut m M))).withSub
    ((baseG κ m).withChan (chanC m M))).mapPorts peekEv peekOut

variable [NeZero κ]

/-- The key-reading predicate of `realKeyed` is that of the drawing parties beside the
forwarding of the adversary port. -/
theorem realKeyed_uses (t : (PSt κ m M × Unit) × SubSt κ m M)
    (e : (InEv m M ⊕ WakeEv κ) ⊕ (AEv κ m M ⊕ P)) :
    (realKeyed H φS φR ans).uses t e =
      MultiHybrid.tensorUses (σ' := Unit) (E' := AEv κ m M) partyUses t.1 (peekEv e) := by
  rcases e with ((x | r) | w) | (a | p) <;> simp [realKeyed, isAdv, isInput, peekEv,
    MultiHybrid.tensorUses, partyUses]

/-- **`iknpW` with the draw in the parties.** The IKNP protocol with its randomness drawn around
it has the view of the protocol over the parties that draw their randomness themselves. -/
theorem view_iknpW_eq_lazy {ζ : Type}
    (Z : Strat ζ ((InEv m M ⊕ WakeEv κ) ⊕ (AEv κ m M ⊕ P)) (InOut m M ⊕ (AOut m M ⊕ L))) :
    view (iknpW H φS φR ans) Z = view (realLazyW H φS φR ans) Z := by
  have h1 : view (realLazyW H φS φR ans) Z =
      view (((MultiHybrid.lazyKey (fun k => (partyW H φS φR ans k).tensor
          (MultiHybrid.idSim (AEv κ m M) (AOut m M))) default (PMF.uniformFintype _)
          (MultiHybrid.tensorUses partyUses)).withSub
          ((baseG κ m).withChan (chanC m M))).mapPorts peekEv peekOut) Z :=
    view_eq_of_stepMap _ _ (fun t => ((t.1.1.1, (t.1.1.2, t.1.2)), t.2)) rfl
      (fun t e => by
        unfold realLazyW partyLazy
        exact Sys.mapPorts_stepMap (fun s => ((s.1.1.1, (s.1.1.2, s.1.2)), s.2))
          (fun t g => MultiHybrid.lazyKey_tensor_withSub_step _ _ _ _ _ _ t g) peekEv peekOut t e)
      Z
  have h2 : view (((MultiHybrid.lazyKey (fun k => (partyW H φS φR ans k).tensor
          (MultiHybrid.idSim (AEv κ m M) (AOut m M))) default (PMF.uniformFintype _)
          (MultiHybrid.tensorUses partyUses)).withSub
          ((baseG κ m).withChan (chanC m M))).mapPorts peekEv peekOut) Z =
      view (((MultiHybrid.keyedWithSub (fun k => (partyW H φS φR ans k).tensor
          (MultiHybrid.idSim (AEv κ m M) (AOut m M))) default
          (MultiHybrid.tensorUses partyUses) ((baseG κ m).withChan (chanC m M))).lazy
          (PMF.uniformFintype _)).mapPorts peekEv peekOut) Z :=
    view_eq_of_stepMap _ _ (fun t => (t.1.1, (t.1.2, t.2))) rfl
      (fun t e => Sys.mapPorts_stepMap (fun s => (s.1.1, (s.1.2, s.2)))
        (fun t g => MultiHybrid.lazyKey_withSub_step _ _ _ _ (fun _ => rfl) _ t g)
        peekEv peekOut t e) Z
  have h3 : view (iknpW H φS φR ans) Z =
      view (((MultiHybrid.keyedWithSub (fun k => (partyW H φS φR ans k).tensor
          (MultiHybrid.idSim (AEv κ m M) (AOut m M))) default
          (MultiHybrid.tensorUses partyUses) ((baseG κ m).withChan (chanC m M))).lazy
          (PMF.uniformFintype _)).mapPorts peekEv peekOut) Z := by
    refine view_eq_of_stepMap _ _ id ?_ (fun t e => ?_) Z
    · rfl
    obtain ⟨ko, x⟩ := t
    cases ko with
    | none =>
      have hu := realKeyed_uses H φS φR ans x e
      cases h : MultiHybrid.tensorUses (σ' := Unit) (E' := AEv κ m M) partyUses x.1 (peekEv e)
      all_goals
        simp only [iknpW, KeyedSys.lazy, KeyedSys.lazyStep, hu, h, MultiHybrid.keyedWithSub]
        simp [realKeyed, realW, Sys.mapPorts, Sys.relabel, KeyedSys.lazyStep, h, SPComp.map,
          SPComp.bind_assoc, SPComp.pure_bind]
    | some k =>
      simp [iknpW, KeyedSys.lazy, KeyedSys.lazyStep, MultiHybrid.keyedWithSub, realKeyed, realW,
        Sys.mapPorts, Sys.relabel, SPComp.map, SPComp.bind_assoc, SPComp.pure_bind]
  rw [h3, h1, h2]

end Lazy

end CatCrypt.Crypto.OT.IKNPWake
