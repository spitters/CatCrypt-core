/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Party.Derived
public import CatCryptCore.Crypto.Party.GuardCoupling

/-!
# Transfer of unwinding to multi-hybrid simulators

A system `X` on the sum interface of a multi-call simulator gives the multi-hybrid
`MultiHybrid.ofSys X n` (`CatCryptCore/Crypto/Party/Call.lean`). An unwinding relation of `X`
for the view `PubView.callView V W` is an unwinding relation of `ofSys X n` from the subroutine
view `W` to the outer view `V`, when the default output is related to itself by `V.out`: the
no-failure guards of `ofSys` take the same branch on both sides (`rHoare_guardNF`), and the
final step maps related decisions to related outputs. Opacity transfers in the same way.

An embedding `MultiHybrid.Embeds π π' b c` with injective `b` and `c` pulls an unwinding
relation of `π'` back to `π`, for a relation on the states of `π` that `b` and `c` preserve and
reflect. A coupling of the images of two computations under maps with left inverses gives a
coupling of the computations (`rHoare_of_map`).

The worked example is the X3DH simulator: the opacity of its program form
(`X3DHProg.simBody_viewRel`, the content of `X3DHProg.simLoopSys_opaque`) gives the unwinding
condition of the hand-written simulator `X3DHSquare.simProt` for the equality of states
(`X3DHProg.simProt_unwinding_of_prog`) and its opacity (`X3DHProg.simProt_opaque_of_prog`).

Search words: unwinding, opacity, multi-hybrid, party language, information flow, transfer,
embedding, coupling of maps.

## Main results

* `CatCrypt.Relational.rHoare_and_isOutcome`: a triple holds with the possible outcomes added to
  its postcondition.
* `CatCrypt.Relational.rHoare_of_map`: a triple on maps with left inverses gives a triple on the
  computations.
* `MultiHybrid.unwinding_ofSys`, `MultiHybrid.opaque_ofSys`: unwinding and opacity transfer from
  a system on the sum interface to its multi-hybrid.
* `MultiHybrid.Embeds.unwinding`: unwinding pulls back along an embedding.
* `Party.X3DHProg.simProt_unwinding_of_prog`, `Party.X3DHProg.simProt_opaque_of_prog`: the
  unwinding condition and the opacity of the X3DH simulator from its program form.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Relational

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCTransparent

variable {α β γ δ : Type}

/-- A triple holds with the possible outcomes of both computations added to its
postcondition. -/
theorem rHoare_and_isOutcome {Φ : RPre} {c₁ : SPComp α} {c₂ : SPComp β} {Ψ : RPost α β}
    (h : rHoare Φ c₁ c₂ Ψ) :
    rHoare Φ c₁ c₂ (fun a h₁ b h₂ => Ψ a h₁ b h₂ ∧ IsOutcome c₁ a ∧ IsOutcome c₂ b) := by
  intro h₁ h₂ hΦ
  obtain ⟨cp, hcp⟩ := h h₁ h₂ hΦ
  exact ⟨cp, fun p p' hp => ⟨hcp p p' hp, ⟨h₁, p.2, cp.in_left_support hp⟩,
    ⟨h₂, p'.2, cp.in_right_support hp⟩⟩⟩

/-- **Couplings of maps.** A triple on the images of two computations under maps with left
inverses gives a triple on the computations, with the postcondition read on the images. -/
theorem rHoare_of_map {Φ : RPre} {c₁ : SPComp α} {c₂ : SPComp β} {f₁ : α → γ} {f₂ : β → δ}
    {g₁ : γ → α} {g₂ : δ → β} (hg₁ : Function.LeftInverse g₁ f₁)
    (hg₂ : Function.LeftInverse g₂ f₂) {Ψ : RPost γ δ}
    (h : rHoare Φ (SPComp.map f₁ c₁) (SPComp.map f₂ c₂) Ψ) :
    rHoare Φ c₁ c₂ (fun a h₁ b h₂ => Ψ (f₁ a) h₁ (f₂ b) h₂) := by
  have key : rHoare Φ (SPComp.map g₁ (SPComp.map f₁ c₁)) (SPComp.map g₂ (SPComp.map f₂ c₂))
      (fun a h₁ b h₂ => Ψ (f₁ a) h₁ (f₂ b) h₂) :=
    rHoare_bind (rHoare_and_isOutcome h) fun y y' => rHoare_ret fun h₁ h₂ hp => by
      obtain ⟨hΨ, hy, hy'⟩ := hp
      obtain ⟨x, -, rfl⟩ := isOutcome_map_iff.mp hy
      obtain ⟨x', -, rfl⟩ := isOutcome_map_iff.mp hy'
      simpa only [hg₁ x, hg₂ x'] using hΨ
  rwa [SPComp.map_comp, SPComp.map_comp, hg₁.comp_eq_id, hg₂.comp_eq_id, SPComp.map_id,
    SPComp.map_id] at key

end CatCrypt.Relational

namespace CatCrypt.Crypto.UCTransparent.MultiHybrid

open CatCrypt.Core CatCrypt.Relational

variable {σ σ' τ E O Q A : Type}

/-- The final step of `ofSys` maps decisions related by `V.StepRel W` to outputs related by
`V.out`: two outputs are returned, and two calls fail. -/
theorem rHoare_bind_toOut {V : PubView E O} {W : PubView Q A} {T : τ → τ → Prop}
    {c c' : SPComp (τ × (Q ⊕ O))}
    (h : rHoare eqPre c c' (fun p h p' h' => h = h' ∧ T p.1 p'.1 ∧ V.StepRel W p.2 p'.2)) :
    rHoare eqPre (c.bind toOut) (c'.bind toOut)
      (fun r h r' h' => h = h' ∧ T r.1 r'.1 ∧ V.out r.2 r'.2) := by
  refine rHoare_bind h fun p p' => ?_
  rcases p with ⟨t, g | o⟩ <;> rcases p' with ⟨t', g' | o'⟩
  · exact rHoare_fail
  · intro h₁ h₂ hp
    exact hp.2.2.elim
  · intro h₁ h₂ hp
    exact hp.2.2.elim
  · exact rHoare_ret fun _ _ hp => hp

/-- **Transfer of unwinding to the multi-hybrid of a system.** An unwinding relation of `X` for
the view of the sum interface is an unwinding relation of `ofSys X n`, when the default output
is related to itself. -/
theorem unwinding_ofSys [Inhabited O] {X : Sys τ (E ⊕ A) (Q ⊕ O)} {V : PubView E O}
    {W : PubView Q A} {T : τ → τ → Prop} (hX : X.Unwinding (PubView.callView V W) T)
    (hd : V.out default default) (n : ℕ) : (ofSys X n).Unwinding V W T where
  init := hX.init
  start t t' _ _ ht he := rHoare_guardNF (hX.step t t' _ _ ht (Sum.LiftRel.inl he))
    (fun _ _ _ _ hp => hp) fun _ => ⟨rfl, ht, hd⟩
  resume t t' _ _ ht ha := rHoare_guardNF (hX.step t t' _ _ ht (Sum.LiftRel.inr ha))
    (fun _ _ _ _ hp => hp) fun _ => ⟨rfl, ht, hd⟩
  finish t t' _ _ ht ha := rHoare_guardNF
    (rHoare_bind_toOut (hX.step t t' _ _ ht (Sum.LiftRel.inr ha)))
    (fun _ _ _ _ hp => hp) fun _ => ⟨rfl, ht, hd⟩

/-- **Transfer of opacity to the multi-hybrid of a system.** A system opaque for the view of
the sum interface gives an opaque multi-hybrid, when the default output is related to
itself. -/
theorem opaque_ofSys [Inhabited O] {X : Sys τ (E ⊕ A) (Q ⊕ O)} {V : PubView E O}
    {W : PubView Q A} (hX : X.Opaque (PubView.callView V W)) (hd : V.out default default)
    (n : ℕ) : (ofSys X n).Opaque V W := by
  obtain ⟨T, hT⟩ := hX
  exact ⟨T, unwinding_ofSys hT hd n⟩

/-- **Unwinding pulls back along an embedding.** For an embedding with injective `b` and `c`,
an unwinding relation `R'` of `π'` gives the unwinding relation `R` of `π`, when `b` and `c`
preserve and reflect the relations. -/
theorem Embeds.unwinding {π : MultiHybrid σ E O Q A} {π' : MultiHybrid σ' E O Q A}
    {b c : σ → σ'} (h : Embeds π π' b c) (hb : Function.Injective b)
    (hc : Function.Injective c) {V : PubView E O} {W : PubView Q A} {R' : σ' → σ' → Prop}
    (hπ' : π'.Unwinding V W R') {R : σ → σ → Prop}
    (hbR : ∀ s s', R s s' → R' (b s) (b s')) (hcR : ∀ s s', R s s' → R' (c s) (c s'))
    (hbR' : ∀ s s', R' (b s) (b s') → R s s') (hcR' : ∀ s s', R' (c s) (c s') → R s s') :
    π.Unwinding V W R := by
  classical
  have : Nonempty σ := ⟨π.init⟩
  have hgb := Function.leftInverse_invFun hb
  have hgc := Function.leftInverse_invFun hc
  have hL : Function.LeftInverse
      (fun q : σ' × (Q ⊕ O) =>
        ((match q.2 with
          | .inl _ => Function.invFun c q.1
          | .inr _ => Function.invFun b q.1), q.2))
      (liftDec b c) := by
    rintro ⟨s, g | o⟩
    · simp only [liftDec_inl, hgc s]
    · simp only [liftDec_inr, hgb s]
  have hF : Function.LeftInverse (fun q : σ' × O => (Function.invFun b q.1, q.2))
      (fun q : σ × O => (b q.1, q.2)) := by
    rintro ⟨s, o⟩
    simp only [hgb s]
  have hdec : ∀ q q' : σ × (Q ⊕ O), V.StepRel W q.2 q'.2 →
      R' (liftDec b c q).1 (liftDec b c q').1 → R q.1 q'.1 := by
    rintro ⟨s, g | o⟩ ⟨s', g' | o'⟩ hd hr
    · exact hcR' _ _ hr
    · exact hd.elim
    · exact hd.elim
    · exact hbR' _ _ hr
  refine ⟨hbR' _ _ (h.init ▸ hπ'.init), ?_, ?_, ?_⟩
  · intro s s' e e' hs he
    have h' := hπ'.start _ _ e e' (hbR s s' hs) he
    rw [h.start, h.start] at h'
    exact rHoare_mono_post (rHoare_of_map hL hL h')
      fun q _ q' _ hp => ⟨hp.1, hdec q q' hp.2.2 hp.2.1, hp.2.2⟩
  · intro s s' o o' hs ho
    have h' := hπ'.resume _ _ o o' (hcR s s' hs) ho
    rw [h.resume, h.resume] at h'
    exact rHoare_mono_post (rHoare_of_map hL hL h')
      fun q _ q' _ hp => ⟨hp.1, hdec q q' hp.2.2 hp.2.1, hp.2.2⟩
  · intro s s' o o' hs ho
    have h' := hπ'.finish _ _ o o' (hcR s s' hs) ho
    rw [h.finish, h.finish] at h'
    exact rHoare_mono_post (rHoare_of_map hF hF h')
      fun q _ q' _ hp => ⟨hp.1, hbR' _ _ hp.2.1, hp.2.2⟩

end CatCrypt.Crypto.UCTransparent.MultiHybrid

namespace CatCrypt.Crypto.Party.X3DHProg

open CatCrypt.Core CatCrypt.Relational CatCrypt.Crypto.UCTransparent
open CatCrypt.Crypto.AKE.X3DHSquare CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.PAKE.DHExtract Prog

variable {S W K : Type} [Field S] [Fintype S] [DecidableEq W] [Fintype K]
  [Nonempty K] [Inhabited K] (G : DHGroup S W)

/-- The program form of the X3DH simulator embeds the hand-written simulator: a state at an
activation boundary is the returned program, a state with a call pending is the continuation
`simK`. -/
theorem simProt_embeds :
    MultiHybrid.Embeds (simProt (K := K) G) (simLoop G) (fun s => .ret s)
      fun s => callK (simK s) :=
  MultiHybrid.ofSys_embeds (simProt G) (loopSys (simBody G) (simProt (K := K) G).init)
    (fun s => .ret s) (fun s => callK (simK s)) rfl (fun s e => by
      change emitK (fun o p => SPComp.pure (p, o)) (fun _ => SPComp.fail)
        (ProgE.bind (simStartP G s e) simDecide) = _
      rw [(simStartP_samples G s e).emitK_bind]
      simp only [emitK_simDecide, SPComp.map]
      rfl)
    (fun s a => by
      simp only [simProt, SPComp.map_pure]
      rfl)
    (fun s a => by
      simp only [simProt, SPComp.map_pure]
      rfl)

omit [Field S] [Fintype S] [DecidableEq W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- The continuation of a pending call is related to itself for the view of the sum
interface. -/
theorem callK_simK_viewRel (s : SimSt S W K) :
    ProgE.ViewRel (PubView.callView outerView subView) Eq (callK (simK s)) (callK (simK s)) := by
  refine ProgE.ViewRel.recv fun x x' hx => ?_
  cases hx with
  | inl _ => exact ProgE.ViewRel.fail
  | inr ha => exact ProgE.ViewRel.send (simOut_rel s.2.2 ha) (ProgE.ViewRel.ret rfl)

omit [Field S] [Fintype S] [DecidableEq W] [Fintype K] [Nonempty K] [Inhabited K] in
/-- Related continuations of pending calls come from equal states: the answer on the honest
port of `F_AKE` separates the phases. -/
theorem eq_of_callK_simK_viewRel {s s' : SimSt S W K}
    (h : ProgE.ViewRel (PubView.callView outerView subView) Eq (callK (simK s))
      (callK (simK s'))) : s = s' := by
  unfold callK at h
  cases h with
  | recv hk =>
    have h1 := hk (.inr (.inl .ok)) (.inr (.inl .ok)) (Sum.LiftRel.inr (Sum.LiftRel.inl trivial))
    clear hk
    simp only [simK, outE, ProgE.bind] at h1
    cases h1 with
    | send ho hp =>
      cases hp with
      | ret hr =>
        obtain ⟨rs, inp, ph⟩ := s
        obtain ⟨rs', inp', ph'⟩ := s'
        simp only [Prod.mk.injEq] at hr
        obtain ⟨rfl, rfl, -⟩ := hr
        cases ph <;> cases ph' <;> simp_all [simOut, PubView.callView, PubView.StepRel,
          PubView.sum, PubView.eqView]

/-- **The unwinding condition of the X3DH simulator from its program form**, for the equality
of states: the unwinding relation of the program loop (`simBody_viewRel`) transfers to the
multi-hybrid `simLoop` and pulls back along the embedding `simProt_embeds`. -/
theorem simProt_unwinding_of_prog : (simProt (K := K) G).Unwinding outerView subView Eq := by
  have hloop := MultiHybrid.unwinding_ofSys (V := outerView) (W := subView)
    (loopSys_unwinding (simBody G) (simProt G).init rfl fun s s' hs => by
      subst hs
      exact simBody_viewRel G s)
    (stepRel_refl (S := S) (W := W) (K := K) (.inr default)) 0
  refine (simProt_embeds G).unwinding (fun _ _ h => ProgE.ret.inj h) (fun s s' h => ?_) hloop
    (fun _ _ h => h ▸ ProgE.ViewRel.ret rfl) (fun s _ h => h ▸ callK_simK_viewRel s)
    (fun _ _ h => by cases h with | ret h => exact h) fun _ _ h => eq_of_callK_simK_viewRel h
  have h' := callK_simK_viewRel (S := S) (W := W) (K := K) s
  grind [eq_of_callK_simK_viewRel]

/-- **Opacity of the X3DH simulator from its program form.** -/
theorem simProt_opaque_of_prog : (simProt (K := K) G).Opaque outerView subView :=
  ⟨Eq, simProt_unwinding_of_prog G⟩

end CatCrypt.Crypto.Party.X3DHProg
