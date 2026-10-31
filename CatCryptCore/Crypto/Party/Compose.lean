/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Party.Prog
public import CatCryptCore.Crypto.UCLoopbackOpenTheory
public import CatCryptCore.Crypto.UCChannel

/-!
# Composition of party programs

The parallel composition `Prog.par p q` of the party programs `p` (events `E`, outputs `O`) and
`q` (events `E'`, outputs `O'`) is a program on the events `E ⊕ E'` and outputs `O ⊕ O'`. It
waits for an event and dispatches it by its side: an event `inl e` runs one activation of `p` on
`e` and emits its output tagged `inl`, and the other residual program is left untouched; an event
`inr e'` runs one activation of `q`. Only the party addressed by the event is active within an
activation. The party language is one generic tree `ProgE` with two effect handlers, the
classical handler `Prog.handler` and the quantum party handler `QProg.handler`; the parallel
composition is the generic `ProgE.par`, a well-founded recursion on the pair of programs ordered
lexicographically by the immediate-subprogram relation `ProgE.Child`, and its activations at the
classical handler are those of `ProgE.act_par_inl` and `ProgE.act_par_inr`.

The denotation of `par p q` is step-equivalent to the parallel composition `Sys.par` of the
denotations (`Prog.toSys_par`), so its class in the Int construction on systems is the tensor
product of the classes of `p` and `q` (`Prog.sysHom_toSys_par`), and protocols written as
programs compose through the monoidal laws of `IntConstruction SysCat` and of the open theory
`loopOpenTheory`.

Wiring of two parties needs no operation on programs: the class `sysHom` of a system depends only
on its step-equivalence class (`SysCat.sysHom_eq_of_stepEq`), so the class of the loop of a party
program equals the class of the system it is step-equivalent to (`Prog.sysHom_loopSys`), and
every Int or open-theory composite of program parties is the composite of the systems they
re-express.

## Main definitions

* `Party.Prog.sampleBody`: the loop body of a system that samples and then updates
  deterministically.
* `Party.Prog.chanBody`: the ideal channel `FChan` as the loop body of a program.

## Main results

* `Party.Prog.toSys_par`: the denotation of `par p q` is `Sys.par` of the denotations.
* `SysCat.sysHom_par`: `sysHom` sends `SysObj.par` to the tensor product.
* `Party.Prog.sysHom_toSys_par`: the Int class of `par p q` is the tensor product of the classes.
* `Party.Prog.sysHom_loopSys`: the Int class of a loop of one-activation iterations is the class
  of the system with the iteration as its step.
* `Party.Prog.sampleBody_stepEq`: a system that samples and updates deterministically is the loop
  of a program.
* `Party.Prog.chanBody_stepEq`: the loop of `chanBody` is step-equivalent to `FChan`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent.SysCat

open CatCrypt.Core CategoryTheory MonoidalCategory

variable {E O E' O' : Type}

/-- Step-equivalent systems have the same class in the Int construction. -/
theorem sysHom_eq_of_stepEq {A B : SysObj E O} (h : Sys.StepEq A B) : sysHom A = sysHom B :=
  IntConstruction.hom_ext (Quotient.sound (Sys.StepEq.mapPorts h _ _))

/-- **`sysHom` is monoidal.** The class of the parallel composition of two systems is the tensor
product of their classes, followed by the unitor of the unit. -/
theorem sysHom_par (A : SysObj E O) (B : SysObj E' O') :
    sysHom (A.par B) = (sysHom A ⊗ₘ sysHom B) ≫ (λ_ (𝟙_ (IntConstruction SysCat))).hom := by
  apply IntConstruction.hom_ext
  simp only [IntConstruction.leftUnitor_hom, IntConstruction.comp_mkHom_hom]
  erw [IntConstruction.tensorHom_hom]
  simp only [sysHom, tensorμ, associator_def, braiding_def,
    leftUnitor_def, isoOfEquiv_hom, isoOfEquiv_inv, whiskerLeft_homOfFun,
    whiskerRight_homOfFun, homOfFun_comp, Category.assoc]
  rw [← Category.assoc, homOfFun_comp]
  refine Quotient.sound (Relation.EqvGen.trans _ _ _ ?_
    (Relation.EqvGen.symm _ _ (Sys.StepMapOn.ofFun_seq_seq_ofFun _ _ _).stepEq))
  refine Relation.EqvGen.rel _ _ ⟨fun _ => True, id, Sys.StepMapOn.of_step _ rfl fun s e => ?_⟩
  change A.St × B.St at s
  rcases e with (e | e) | e
  · simp [SysObj.par, SysObj.mapPorts, Sys.mapPorts_step, SPComp.map, SPComp.bind_assoc,
      Equiv.sumAssoc, Equiv.emptySum, Equiv.sumComm]
  · simp [SysObj.par, SysObj.mapPorts, Sys.mapPorts_step, SPComp.map, SPComp.bind_assoc,
      Equiv.sumAssoc, Equiv.emptySum, Equiv.sumComm]
  · exact e.elim

end CatCrypt.Crypto.UCTransparent.SysCat

namespace CatCrypt.Crypto.Party

open CatCrypt.Core CatCrypt.Crypto.UCTransparent CategoryTheory MonoidalCategory

namespace Prog

variable {E O E' O' α β σ : Type}

export ProgE (Child child_wf par parAwL parEmL parAwR parEmR)

/-! ## The denotation of the parallel composition -/

/-- The emit phase of `parEmL p q` is the emit phase of `p`, its residual composed with `q` and
its output tagged `inl`. -/
theorem emitK_parEmL (q : Prog E' O' β) (p : Prog E O α) :
    emitK (fun o r => SPComp.pure (r, o)) (fun _ => SPComp.fail) (parEmL p q) =
      SPComp.map (fun x => (par x.1 q, Sum.inl x.2))
        (emitK (fun o r => SPComp.pure (r, o)) (fun _ => SPComp.fail) p) :=
  ProgE.emitK_parEmL handler handler_lawful q p

/-- The emit phase of `parEmR p q` is the emit phase of `q`, `p` composed with its residual and
its output tagged `inr`. -/
theorem emitK_parEmR (p : Prog E O α) (q : Prog E' O' β) :
    emitK (fun o r => SPComp.pure (r, o)) (fun _ => SPComp.fail) (parEmR p q) =
      SPComp.map (fun x => (par p x.1, Sum.inr x.2))
        (emitK (fun o r => SPComp.pure (r, o)) (fun _ => SPComp.fail) q) :=
  ProgE.emitK_parEmR handler handler_lawful p q

/-- The emit phase of `parAwL e p q` is the activation of `p` on `e`. -/
theorem emitK_parAwL (e : E) (q : Prog E' O' β) (p : Prog E O α) :
    emitK (fun o r => SPComp.pure (r, o)) (fun _ => SPComp.fail) (parAwL e p q) =
      SPComp.map (fun x => (par x.1 q, Sum.inl x.2)) (act p e) :=
  ProgE.emitK_parAwL handler handler_lawful e q p

/-- The emit phase of `parAwR e p q` is the activation of `q` on `e`. -/
theorem emitK_parAwR (e : E') (p : Prog E O α) (q : Prog E' O' β) :
    emitK (fun o r => SPComp.pure (r, o)) (fun _ => SPComp.fail) (parAwR e p q) =
      SPComp.map (fun x => (par p x.1, Sum.inr x.2)) (act q e) :=
  ProgE.emitK_parAwR handler handler_lawful e p q

/-- An activation of `par p q` on a left event is the activation of `p`. -/
theorem act_par_inl (p : Prog E O α) (q : Prog E' O' β) (e : E) :
    act (par p q) (.inl e) = SPComp.map (fun x => (par x.1 q, Sum.inl x.2)) (act p e) :=
  ProgE.act_par_inl handler handler_lawful p q e

/-- An activation of `par p q` on a right event is the activation of `q`. -/
theorem act_par_inr (p : Prog E O α) (q : Prog E' O' β) (e : E') :
    act (par p q) (.inr e) = SPComp.map (fun x => (par p x.1, Sum.inr x.2)) (act q e) :=
  ProgE.act_par_inr handler handler_lawful p q e

/-- **The denotation of the parallel composition** is step-equivalent to the parallel
composition of the denotations. -/
theorem toSys_par (p : Prog E O α) (q : Prog E' O' β) :
    Sys.StepEq ⟨_, toSys (par p q)⟩ ⟨_, (toSys p).par (toSys q)⟩ := by
  refine Relation.EqvGen.symm _ _ (Relation.EqvGen.rel _ _
    ⟨fun _ => True, fun s => par s.1 s.2, Sys.StepMapOn.of_step _ rfl fun s e => ?_⟩)
  rcases e with e | e
  · rw [Sys.par_step_inl, SPComp.map_comp]
    exact (act_par_inl s.1 s.2 e).symm
  · rw [Sys.par_step_inr, SPComp.map_comp]
    exact (act_par_inr s.1 s.2 e).symm

/-- **The Int class of the parallel composition** is the tensor product of the classes. -/
theorem sysHom_toSys_par (p : Prog E O α) (q : Prog E' O' β) :
    SysCat.sysHom ⟨_, toSys (par p q)⟩ =
      (SysCat.sysHom ⟨_, toSys p⟩ ⊗ₘ SysCat.sysHom ⟨_, toSys q⟩) ≫
        (λ_ (𝟙_ (IntConstruction SysCat))).hom := by
  rw [SysCat.sysHom_eq_of_stepEq (toSys_par p q)]
  exact SysCat.sysHom_par ⟨_, toSys p⟩ ⟨_, toSys q⟩

/-- **Loops in the Int construction.** When every iteration of `body` is one activation, the
class of the loop of `body` is the class of the system with the iteration as its step. -/
theorem sysHom_loopSys (body : σ → Prog E O σ) (s₀ : σ) (step : σ → E → SPComp (σ × O))
    (h : ∀ s e, act (body s) e = SPComp.map (fun q => (Prog.ret q.1, q.2)) (step s e)) :
    SysCat.sysHom ⟨_, loopSys body s₀⟩ = SysCat.sysHom ⟨σ, ⟨s₀, step⟩⟩ :=
  SysCat.sysHom_eq_of_stepEq (loopSys_stepEq body s₀ step h)

/-! ## Systems as loops of programs -/

/-- The loop body of a system that samples `rand s e` and then updates by `next`: receive `e`,
sample `r`, emit the output of `next s e r` and return its state. -/
noncomputable def sampleBody {ρ : Type} [Countable ρ] (rand : σ → E → SPComp ρ)
    (next : σ → E → ρ → σ × O) (s : σ) : Prog E O σ := do
  let e ← recvE
  let r ← sampleE (rand s e)
  sendE (next s e r).2
  pure (next s e r).1

/-- **A sampling system is the loop of a program.** -/
theorem sampleBody_stepEq {ρ : Type} [Countable ρ] (rand : σ → E → SPComp ρ)
    (next : σ → E → ρ → σ × O) (s₀ : σ) :
    Sys.StepEq ⟨_, loopSys (sampleBody rand next) s₀⟩
      ⟨σ, ⟨s₀, fun s e => SPComp.map (next s e) (rand s e)⟩⟩ :=
  loopSys_stepEq _ _ _ fun s e => by
    simp [sampleBody, act_def, stepWith_def, ProgE.recvE, sampleE, ProgE.sendE, ProgE.bind,
      emitK_bind, emitK_sample, SPComp.map, SPComp.bind_assoc]

/-! ## Example: the ideal channel -/

section Channel

open CatCrypt.Crypto.Choreography (ChannelCap)

variable {V Leak : Type}

/-- The ideal channel `FChan cap ℓ` as the loop body of a program: receive an event, take the
step of its port on the channel state, emit the output and return the new state. -/
def chanBody (cap : ChannelCap) (ℓ : V → Leak) (t : ChanSt V) :
    Prog (ChanHEv V ⊕ ChanAEv V) (ChanHOut V ⊕ ChanAOut V Leak) (ChanSt V) := do
  match ← recvE with
  | .inl h =>
    sendE (.inl (FChan.honStep t h).2)
    pure (FChan.honStep t h).1
  | .inr a =>
    sendE (.inr (FChan.advStep cap ℓ t a).2)
    pure (FChan.advStep cap ℓ t a).1

/-- **The ideal channel as a program.** The loop of `chanBody cap ℓ` from the empty channel is
step-equivalent to `FChan cap ℓ`. -/
theorem chanBody_stepEq (cap : ChannelCap) (ℓ : V → Leak) :
    Sys.StepEq ⟨_, loopSys (chanBody cap ℓ) FChan.initSt⟩ ⟨ChanSt V, FChan cap ℓ⟩ :=
  loopSys_stepEq _ _ _ fun t e => by
    rcases e with h | a
    · simp [chanBody, act_def, stepWith_def, ProgE.recvE, ProgE.sendE, ProgE.bind,
        FChan.honSys, SPComp.map]
    · simp [chanBody, act_def, stepWith_def, ProgE.recvE, ProgE.sendE, ProgE.bind,
        FChan.advSys, SPComp.map]

end Channel

end Prog

end CatCrypt.Crypto.Party
