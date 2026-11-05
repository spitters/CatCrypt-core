/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCSimulatorCostPot

/-!
# Potential time bounds of costed simulators under composition

The potential time bound `Simulator.Timed.TimeBoundPot T gE gO hEG hO a b` of a costed
simulator, by recursion on `T`: a costed multi-call simulator has a potential time bound
(`MultiHybrid.Timed.PotentialBound`) with the imports `gE`, `gO` received and `hEG`, `hO`
passed on; the factors of a costed composite have potential time bounds that conserve import at
the middle interface up to `κ` per message, the composite potential being the sum of the
potentials of the factors; a relabelled simulator has the potential time bound of its simulator
at imports the relabelling does not increase. One outer activation of a composite passes at most
`Simulator.Timed.msgBound` messages across its inner interfaces, so its potential grows by at
most `κ * msgBound` beyond the import received, which enters the constant `a`.

The certificate `Simulator.Timed.PotCert T a b c` is a potential time bound with no import
passed on at the outer ports and import measures linear in the size (`ImportLinear`). The
constant, graded and size-graded time bounds of costed simulators are potential time bounds,
the size-graded one when the composites are built with the size `0` on the middle answers
(`Simulator.Timed.TimeBoundSizedZero`).

## Main definitions

* `Simulator.Timed.calls`, `Simulator.Timed.msgBound`, `Simulator.Timed.msgSum`: the number of
  inner events per activation, the number of messages across inner interfaces per activation,
  and the sum of the latter over the composites of a costed simulator.
* `Simulator.Timed.TimeBoundPot`, `Simulator.Timed.PotCert`: the potential time bound and the
  potential certificate of a costed simulator.
* `Simulator.Timed.TimeBoundSizedZero`: the size-graded time bound with the size `0` on the
  answers of the inner factor of every composite.
* `MultiHybrid.Timed.PotentialBound.mono`: a potential time bound at larger constants and
  received imports and smaller imports passed on.

## Main results

* `Simulator.ofMultiHybrid.timeBoundPot_timed`, `Simulator.ofMultiHybridHat.timeBoundPot_timed`,
  `Simulator.comp.timeBoundPot_timed`, `Simulator.mapPorts.timeBoundPot_timed`,
  `Simulator.tensor.timeBoundPot_timed`: the constructor rules.
* `Simulator.Timed.TimeBoundPot.mono`: monotonicity in the constants and imports.
* `Simulator.Timed.TimeBound.timeBoundPot`, `Simulator.Timed.TimeBoundGraded.timeBoundPot`,
  `Simulator.Timed.TimeBoundSizedZero.timeBoundPot`: the instances, and their certificates
  `Simulator.Timed.TimeBound.potCert`, `Simulator.Timed.TimeBoundGraded.potCert`,
  `Simulator.Timed.TimeBoundSizedZero.potCert`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core

namespace MultiHybrid.Timed.PotentialBound

variable {σ E O EG OG : Type} {A : MultiHybrid.Timed σ E O EG OG} {gE : E → ℕ} {gO : OG → ℕ}
  {hEG : EG → ℕ} {hO : O → ℕ} {a b : ℕ}

/-- `Sum.elim` of pointwise smaller measures is pointwise smaller. -/
theorem sum_elim_le {hEG hEG' : EG → ℕ} {hO hO' : O → ℕ} (hhEG : ∀ g, hEG' g ≤ hEG g)
    (hhO : ∀ o, hO' o ≤ hO o) (z : EG ⊕ O) : Sum.elim hEG' hO' z ≤ Sum.elim hEG hO z := by
  cases z <;> simp [hhEG, hhO]

/-- A potential time bound is a potential time bound at larger constants, larger imports
received and smaller imports passed on, with the same invariant and potential. -/
def mono (P : A.PotentialBound gE gO hEG hO a b) {gE' : E → ℕ} {gO' : OG → ℕ}
    {hEG' : EG → ℕ} {hO' : O → ℕ} {a' b' : ℕ} (ha : a ≤ a') (hb : b ≤ b')
    (hgE : ∀ e, gE e ≤ gE' e) (hgO : ∀ o, gO o ≤ gO' o) (hhEG : ∀ g, hEG' g ≤ hEG g)
    (hhO : ∀ o, hO' o ≤ hO o) : A.PotentialBound gE' gO' hEG' hO' a' b' where
  Inv := P.Inv
  Φ := P.Φ
  init := P.init
  start s e hs := by
    refine ⟨le_trans (P.start s e hs).1
      (Nat.add_le_add ha (Nat.mul_le_mul hb (Nat.add_le_add_left (hgE e) _))),
      SPTree.Timed.allRet_mono (fun y hy => ⟨hy.1, ?_⟩) _ (P.start s e hs).2⟩
    have := sum_elim_le hhEG hhO y.2
    have := hgE e
    omega
  resume s o hs := by
    refine ⟨le_trans (P.resume s o hs).1
      (Nat.add_le_add ha (Nat.mul_le_mul hb (Nat.add_le_add_left (hgO o) _))),
      SPTree.Timed.allRet_mono (fun y hy => ⟨hy.1, ?_⟩) _ (P.resume s o hs).2⟩
    have := sum_elim_le hhEG hhO y.2
    have := hgO o
    omega
  finish s o hs := by
    refine ⟨le_trans (P.finish s o hs).1
      (Nat.add_le_add ha (Nat.mul_le_mul hb (Nat.add_le_add_left (hgO o) _))),
      SPTree.Timed.allRet_mono (fun y hy => ⟨hy.1, ?_⟩) _ (P.finish s o hs).2⟩
    have := hhO y.2
    have := hgO o
    omega

end MultiHybrid.Timed.PotentialBound

namespace Simulator.Timed

/-- The number of inner events of one activation of a costed simulator: `fuel + 1` for a costed
multi-call simulator, the product for a composite, that of its simulator for a relabelling. -/
def calls : {E O EG OG : Type} → {V : PubView E O} → {W : PubView EG OG} →
    Simulator.Timed E O EG OG V W → ℕ
  | _, _, _, _, _, _, .ofMultiHybrid πT => πT.fuel + 1
  | _, _, _, _, _, _, .ofMultiHybridHat _ _ _ _ _ πT => πT.fuel + 1
  | _, _, _, _, _, _, .comp T₁ T₂ => calls T₁ * calls T₂
  | _, _, _, _, _, _, .mapPorts T _ _ => calls T

/-- The number of messages across the inner interfaces of a costed simulator in one outer
activation: `0` for a costed multi-call simulator; for a composite, those of the outer factor,
and for each of its `calls` middle events the event, its answer and the messages of one
activation of the inner factor; for a relabelling, those of its simulator. -/
def msgBound : {E O EG OG : Type} → {V : PubView E O} → {W : PubView EG OG} →
    Simulator.Timed E O EG OG V W → ℕ
  | _, _, _, _, _, _, .ofMultiHybrid _ => 0
  | _, _, _, _, _, _, .ofMultiHybridHat _ _ _ _ _ _ => 0
  | _, _, _, _, _, _, .comp T₁ T₂ => msgBound T₁ + calls T₁ * (2 + msgBound T₂)
  | _, _, _, _, _, _, .mapPorts T _ _ => msgBound T

/-- The sum of `msgBound` over the composites of a costed simulator. -/
def msgSum : {E O EG OG : Type} → {V : PubView E O} → {W : PubView EG OG} →
    Simulator.Timed E O EG OG V W → ℕ
  | _, _, _, _, _, _, .ofMultiHybrid _ => 0
  | _, _, _, _, _, _, .ofMultiHybridHat _ _ _ _ _ _ => 0
  | _, _, _, _, _, _, .comp T₁ T₂ => msgSum T₁ + msgSum T₂ + msgBound (T₁.comp T₂)
  | _, _, _, _, _, _, .mapPorts T _ _ => msgSum T

/-- The potential time bound of a costed simulator with the import `gE` of its outer events and
`gO` of the answers it receives, the import `hEG` of its inner events and `hO` of its outer
outputs passed on, and the constants `a`, `b`. A costed multi-call simulator has a potential time
bound, through the erasure maps of the ports for one on costed events. The outer factor of a
composite has a potential time bound with the import `gM` of the middle answers it receives and
`hEM` of the middle events it passes on, the inner factor one with the import `gEM` of the
middle events it receives and `hM` of the middle answers it passes on; the middle interface
conserves import up to `κ` per message (`gEM ≤ hEM + κ`, `gM ≤ hM + κ`), and the constants
satisfy `a₁ + a₂ + (b₁ + b₂) * κ * msgBound ≤ a` and `b₁ + b₂ ≤ b`. A relabelled simulator has
the potential time bound of its simulator at imports the relabelling does not increase. -/
def TimeBoundPot : {E O EG OG : Type} → {V : PubView E O} → {W : PubView EG OG} →
    Simulator.Timed E O EG OG V W → (E → ℕ) → (OG → ℕ) → (EG → ℕ) → (O → ℕ) → ℕ → ℕ → Prop
  | _, _, _, _, _, _, .ofMultiHybrid πT, gE, gO, hEG, hO, a, b =>
    Nonempty (πT.PotentialBound gE gO hEG hO a b)
  | _, _, _, _, _, _, .ofMultiHybridHat _ εE εO εEG εOG πT, gE, gO, hEG, hO, a, b =>
    Nonempty (πT.PotentialBound (fun e => gE (εE e)) (fun o => gO (εOG o))
      (fun g => hEG (εEG g)) (fun o => hO (εO o)) a b)
  | _, _, _, _, _, _, .comp (EM := EM) (OM := OM) T₁ T₂, gE, gO, hEG, hO, a, b =>
    ∃ (κ : ℕ) (gM hM : OM → ℕ) (gEM hEM : EM → ℕ) (a₁ b₁ a₂ b₂ : ℕ),
      TimeBoundPot T₁ gE gM hEM hO a₁ b₁ ∧ TimeBoundPot T₂ gEM gO hEG hM a₂ b₂ ∧
      (∀ m, gEM m ≤ hEM m + κ) ∧ (∀ o, gM o ≤ hM o + κ) ∧
      a₁ + a₂ + (b₁ + b₂) * κ * msgBound (T₁.comp T₂) ≤ a ∧ b₁ + b₂ ≤ b
  | _, _, _, _, _, _, .mapPorts (EM := EM) (OM := OM) T f g, gE, gO, hEG, hO, a, b =>
    ∃ (gM : EM → ℕ) (hM : OM → ℕ), (∀ e, gM (f e) ≤ gE e) ∧ (∀ o, hO (g o) ≤ hM o) ∧
      TimeBoundPot T gM gO hEG hM a b

/-- The potential certificate `a`, `b`, `c` of a costed simulator: a potential time bound with
constants `a`, `b`, no import passed on at the outer ports, and import measures at most `c` times
the size of the message. -/
def PotCert {E O EG OG : Type} {V : PubView E O} {W : PubView EG OG} [ImportSize E]
    [ImportSize OG] (T : Simulator.Timed E O EG OG V W) (a b c : ℕ) : Prop :=
  ∃ (gE : E → ℕ) (gO : OG → ℕ), T.TimeBoundPot gE gO 0 0 a b ∧ ImportLinear gE gO c

/-- A potential time bound of a costed simulator is a potential time bound at larger constants,
larger imports received and smaller imports passed on. -/
theorem TimeBoundPot.mono {E O EG OG : Type} {V : PubView E O} {W : PubView EG OG}
    {T : Simulator.Timed E O EG OG V W} {gE gE' : E → ℕ} {gO gO' : OG → ℕ} {hEG hEG' : EG → ℕ}
    {hO hO' : O → ℕ} {a b a' b' : ℕ} (h : T.TimeBoundPot gE gO hEG hO a b) (ha : a ≤ a')
    (hb : b ≤ b') (hgE : ∀ e, gE e ≤ gE' e) (hgO : ∀ o, gO o ≤ gO' o)
    (hhEG : ∀ g, hEG' g ≤ hEG g) (hhO : ∀ o, hO' o ≤ hO o) :
    T.TimeBoundPot gE' gO' hEG' hO' a' b' := by
  induction T generalizing a b a' b' with
  | ofMultiHybrid πT =>
    obtain ⟨P⟩ := h
    exact ⟨P.mono ha hb hgE hgO hhEG hhO⟩
  | ofMultiHybridHat εσ εE εO εEG εOG πT =>
    obtain ⟨P⟩ := h
    exact ⟨P.mono ha hb (fun e => hgE (εE e)) (fun o => hgO (εOG o)) (fun g => hhEG (εEG g))
      (fun o => hhO (εO o))⟩
  | mapPorts T f g ih =>
    obtain ⟨gM, hM, hf, hg, hT⟩ := h
    exact ⟨gM, hM, fun e => (hf e).trans (hgE e), fun o => (hhO (g o)).trans (hg o),
      ih hT ha hb (fun _ => le_rfl) hgO hhEG (fun _ => le_rfl)⟩
  | comp T₁ T₂ ih₁ ih₂ =>
    obtain ⟨κ, gM, hM, gEM, hEM, a₁, b₁, a₂, b₂, h₁, h₂, hE, hA, h3, h4⟩ := h
    exact ⟨κ, gM, hM, gEM, hEM, a₁, b₁, a₂, b₂,
      ih₁ h₁ le_rfl le_rfl hgE (fun _ => le_rfl) (fun _ => le_rfl) hhO,
      ih₂ h₂ le_rfl le_rfl (fun _ => le_rfl) hgO hhEG (fun _ => le_rfl), hE, hA, by omega,
      by omega⟩

/-- A time bound `t` of a costed simulator is a potential time bound with no import, the
constant `t` and no growth. -/
theorem TimeBound.timeBoundPot {E O EG OG : Type} {V : PubView E O} {W : PubView EG OG}
    {T : Simulator.Timed E O EG OG V W} {t : ℕ} (h : T.TimeBound t) :
    T.TimeBoundPot 0 0 0 0 t 0 := by
  induction T generalizing t with
  | ofMultiHybrid πT =>
    exact ⟨(MultiHybrid.Timed.TimeBoundInv.of_timeBound h).potentialBound.mono (by omega)
      le_rfl (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => le_rfl)⟩
  | ofMultiHybridHat εσ εE εO εEG εOG πT =>
    obtain ⟨Inv, hI⟩ := h
    exact ⟨hI.potentialBound.mono (by omega) le_rfl (fun _ => le_rfl) (fun _ => le_rfl)
      (fun _ => le_rfl) (fun _ => le_rfl)⟩
  | mapPorts T f g ih => exact ⟨0, 0, fun _ => le_rfl, fun _ => le_rfl, ih h⟩
  | comp T₁ T₂ ih₁ ih₂ =>
    obtain ⟨t₁, t₂, h₁, h₂, hle⟩ := h
    exact ⟨0, 0, 0, 0, 0, t₁, 0, t₂, 0, ih₁ h₁, ih₂ h₂, fun _ => le_rfl, fun _ => le_rfl,
      by simpa using hle, le_rfl⟩

/-- A graded time bound `a`, `b` of a costed simulator is a potential time bound with the import
`1` of every message, the constants `a + b * msgSum` and `b`, and the composites conserving
import up to `1` per message. -/
theorem TimeBoundGraded.timeBoundPot {E O EG OG : Type} {V : PubView E O} {W : PubView EG OG}
    {T : Simulator.Timed E O EG OG V W} {a b : ℕ} (h : T.TimeBoundGraded a b) :
    T.TimeBoundPot 1 1 0 0 (a + b * T.msgSum) b := by
  induction T generalizing a b with
  | ofMultiHybrid πT =>
    obtain ⟨Inv, hI⟩ := h
    exact ⟨hI.potentialBound.mono (Nat.le_add_right _ _) le_rfl (fun _ => le_rfl)
      (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => le_rfl)⟩
  | ofMultiHybridHat εσ εE εO εEG εOG πT =>
    obtain ⟨Inv, hI⟩ := h
    exact ⟨hI.potentialBound.mono (Nat.le_add_right _ _) le_rfl (fun _ => le_rfl)
      (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => le_rfl)⟩
  | mapPorts T f g ih => exact ⟨1, 0, fun _ => le_rfl, fun _ => le_rfl, ih h⟩
  | comp T₁ T₂ ih₁ ih₂ =>
    obtain ⟨a₁, b₁, a₂, b₂, h₁, h₂, h3, h4⟩ := h
    refine ⟨1, 1, 0, 1, 0, _, _, _, _, ih₁ h₁, ih₂ h₂, fun _ => le_rfl, fun _ => le_rfl, ?_,
      h4⟩
    have := Nat.mul_le_mul_right T₁.msgSum (show b₁ ≤ b by omega)
    have := Nat.mul_le_mul_right T₂.msgSum (show b₂ ≤ b by omega)
    have := Nat.mul_le_mul_right (T₁.comp T₂).msgBound h4
    simp only [msgSum, Nat.mul_one, Nat.mul_add] at *
    omega

/-- The size-graded time bound `a`, `b`, `c` of a costed simulator built with the size `0` on
the answers of the inner factor of every composite: as `TimeBoundSized`, with the outer factor
of a composite bounded at the size `0` on the middle answers. -/
def TimeBoundSizedZero : {E O EG OG : Type} → {V : PubView E O} → {W : PubView EG OG} →
    Simulator.Timed E O EG OG V W → (E → ℕ) → (OG → ℕ) → ℕ → ℕ → ℕ → Prop
  | _, _, _, _, _, _, .ofMultiHybrid (σ := σ) πT, sE, sO, a, b, c =>
    ∃ Inv : ℕ → σ → Prop, πT.TimeBoundSized Inv sE sO a b c
  | _, _, _, _, _, _, .ofMultiHybridHat (σHat := σHat) _ εE _ _ εOG πT, sE, sO, a, b, c =>
    ∃ Inv : ℕ → σHat → Prop,
      πT.TimeBoundSized Inv (fun e => sE (εE e)) (fun o => sO (εOG o)) a b c
  | _, _, _, _, _, _, .comp T₁ T₂, sE, sO, a, b, c =>
    ∃ (a₁ b₁ c₁ a₂ b₂ c₂ : ℕ), TimeBoundSizedZero T₁ sE (fun _ => 0) a₁ b₁ c₁ ∧
      TimeBoundSizedZero T₂ (fun _ => 0) sO a₂ b₂ c₂ ∧ a₁ + a₂ ≤ a ∧ b₁ + b₂ ≤ b ∧ c₁ + c₂ ≤ c
  | _, _, _, _, _, _, .mapPorts T f _, sE, sO, a, b, c =>
    ∃ sM, (∀ e, sM (f e) ≤ sE e) ∧ TimeBoundSizedZero T sM sO a b c

/-- A size-graded time bound with the size `0` on the middle answers is a size-graded time
bound. -/
theorem TimeBoundSizedZero.timeBoundSized {E O EG OG : Type} {V : PubView E O}
    {W : PubView EG OG} {T : Simulator.Timed E O EG OG V W} {sE : E → ℕ} {sO : OG → ℕ}
    {a b c : ℕ} (h : T.TimeBoundSizedZero sE sO a b c) : T.TimeBoundSized sE sO a b c := by
  induction T generalizing a b c with
  | ofMultiHybrid πT => exact h
  | ofMultiHybridHat εσ εE εO εEG εOG πT => exact h
  | mapPorts T f g ih =>
    obtain ⟨sM, hM, hT⟩ := h
    exact ⟨sM, hM, ih hT⟩
  | comp T₁ T₂ ih₁ ih₂ =>
    obtain ⟨a₁, b₁, c₁, a₂, b₂, c₂, h₁, h₂, h3, h4, h5⟩ := h
    exact ⟨fun _ => 0, a₁, b₁, c₁, a₂, b₂, c₂, ih₁ h₁, ih₂ h₂, AnswerSizeLe.zero T₂, h3, h4, h5⟩

/-- A size-graded time bound `a`, `b`, `c` of a costed simulator built with the size `0` on the
middle answers is a potential time bound with the import `1 + sE e` of an event and `1 + sO o`
of an answer, the constants `a + (b + c) * msgSum` and `b + c`, and the composites conserving
import up to `1` per message. -/
theorem TimeBoundSizedZero.timeBoundPot {E O EG OG : Type} {V : PubView E O}
    {W : PubView EG OG} {T : Simulator.Timed E O EG OG V W} {sE : E → ℕ} {sO : OG → ℕ}
    {a b c : ℕ} (h : T.TimeBoundSizedZero sE sO a b c) :
    T.TimeBoundPot (fun e => 1 + sE e) (fun o => 1 + sO o) 0 0 (a + (b + c) * T.msgSum)
      (b + c) := by
  induction T generalizing a b c with
  | ofMultiHybrid πT =>
    obtain ⟨Inv, hI⟩ := h
    exact ⟨hI.potentialBound.mono (Nat.le_add_right _ _) (by omega) (fun _ => le_rfl)
      (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => le_rfl)⟩
  | ofMultiHybridHat εσ εE εO εEG εOG πT =>
    obtain ⟨Inv, hI⟩ := h
    exact ⟨hI.potentialBound.mono (Nat.le_add_right _ _) (by omega) (fun _ => le_rfl)
      (fun _ => le_rfl) (fun _ => le_rfl) (fun _ => le_rfl)⟩
  | mapPorts T f g ih =>
    obtain ⟨sM, hM, hT⟩ := h
    exact ⟨fun e => 1 + sM e, 0, fun e => Nat.add_le_add_left (hM e) 1, fun _ => le_rfl, ih hT⟩
  | comp T₁ T₂ ih₁ ih₂ =>
    obtain ⟨a₁, b₁, c₁, a₂, b₂, c₂, h₁, h₂, h3, h4, h5⟩ := h
    refine ⟨1, _, 0, _, 0, _, _, _, _, ih₁ h₁, ih₂ h₂, fun _ => le_rfl, fun _ => le_rfl, ?_,
      by omega⟩
    have := Nat.mul_le_mul_right T₁.msgSum (show b₁ + c₁ ≤ b + c by omega)
    have := Nat.mul_le_mul_right T₂.msgSum (show b₂ + c₂ ≤ b + c by omega)
    have := Nat.mul_le_mul_right (T₁.comp T₂).msgBound
      (show b₁ + c₁ + (b₂ + c₂) ≤ b + c by omega)
    simp only [msgSum, Nat.mul_one, Nat.mul_add] at *
    omega

/-- The potential certificate of a time bound `t`: the constants `t`, `0`, for every `c`. -/
theorem TimeBound.potCert {E O EG OG : Type} {V : PubView E O} {W : PubView EG OG}
    [ImportSize E] [ImportSize OG] {T : Simulator.Timed E O EG OG V W} {t : ℕ}
    (h : T.TimeBound t) (c : ℕ) : T.PotCert t 0 c :=
  ⟨0, 0, h.timeBoundPot, fun _ => Nat.zero_le _, fun _ => Nat.zero_le _⟩

/-- The potential certificate of a graded time bound `a`, `b`: the constants `a + b * msgSum`,
`b` and `1`. -/
theorem TimeBoundGraded.potCert {E O EG OG : Type} {V : PubView E O} {W : PubView EG OG}
    [ImportSize E] [ImportSize OG] {T : Simulator.Timed E O EG OG V W} {a b : ℕ}
    (h : T.TimeBoundGraded a b) : T.PotCert (a + b * T.msgSum) b 1 :=
  ⟨1, 1, h.timeBoundPot, ImportLinear.one⟩

/-- The potential certificate of a size-graded time bound built with the size `0` on the middle
answers, with sizes `sE`, `sO` at most `c₀` times the message size: the constants
`a + (b + c) * msgSum`, `b + c` and `1 + c₀`. -/
theorem TimeBoundSizedZero.potCert {E O EG OG : Type} {V : PubView E O} {W : PubView EG OG}
    [ImportSize E] [ImportSize OG] {T : Simulator.Timed E O EG OG V W} {sE : E → ℕ}
    {sO : OG → ℕ} {a b c c₀ : ℕ} (h : T.TimeBoundSizedZero sE sO a b c)
    (hE : ∀ e, sE e ≤ c₀ * ImportSize.size e) (hO : ∀ o, sO o ≤ c₀ * ImportSize.size o) :
    T.PotCert (a + (b + c) * T.msgSum) (b + c) (1 + c₀) :=
  ⟨_, _, h.timeBoundPot, ImportLinear.one_add hE hO⟩

end Simulator.Timed

namespace Simulator

variable {σ σ' E O E' O' EM OM EG OG EG' OG' : Type} {V : PubView E O} {U : PubView EM OM}
  {W : PubView EG OG} {V' : PubView E' O'} {W' : PubView EG' OG'}

/-- **Potential running time of a costed multi-call simulator**: a potential time bound of its
steps is a potential time bound of the costed simulator. -/
theorem ofMultiHybrid.timeBoundPot_timed {πT : MultiHybrid.Timed σ E O EG OG} {gE : E → ℕ}
    {gO : OG → ℕ} {hEG : EG → ℕ} {hO : O → ℕ} {a b : ℕ}
    (P : πT.PotentialBound gE gO hEG hO a b) :
    (Simulator.Timed.ofMultiHybrid πT : Simulator.Timed E O EG OG V W).TimeBoundPot gE gO hEG hO
      a b :=
  ⟨P⟩

/-- **Potential running time of a costed multi-call simulator on costed states**: a potential
time bound of its steps at the imports through the erasure maps of the ports is a potential time
bound of the costed simulator. -/
theorem ofMultiHybridHat.timeBoundPot_timed {σHat EHat OHat EGHat OGHat : Type}
    {εσ : σHat → σ} {εE : EHat → E} {εO : OHat → O} {εEG : EGHat → EG} {εOG : OGHat → OG}
    {πT : MultiHybrid.Timed σHat EHat OHat EGHat OGHat} {gE : E → ℕ} {gO : OG → ℕ}
    {hEG : EG → ℕ} {hO : O → ℕ} {a b : ℕ}
    (P : πT.PotentialBound (fun e => gE (εE e)) (fun o => gO (εOG o)) (fun g => hEG (εEG g))
      (fun o => hO (εO o)) a b) :
    (Simulator.Timed.ofMultiHybridHat εσ εE εO εEG εOG πT :
      Simulator.Timed E O EG OG V W).TimeBoundPot gE gO hEG hO a b :=
  ⟨P⟩

/-- **Potential running time of a costed composite**: if the middle interface conserves import
up to `κ` per message, the composite has the potential time bound with the constants
`a₁ + a₂ + (b₁ + b₂) * κ * msgBound` and `b₁ + b₂`, and the sum of the potentials of its
factors. -/
theorem comp.timeBoundPot_timed {T₁ : Simulator.Timed E O EM OM V U}
    {T₂ : Simulator.Timed EM OM EG OG U W} {gE : E → ℕ} {gM hM : OM → ℕ} {gEM hEM : EM → ℕ}
    {gO : OG → ℕ} {hEG : EG → ℕ} {hO : O → ℕ} {κ a₁ b₁ a₂ b₂ : ℕ}
    (h₁ : T₁.TimeBoundPot gE gM hEM hO a₁ b₁) (h₂ : T₂.TimeBoundPot gEM gO hEG hM a₂ b₂)
    (hE : ∀ m, gEM m ≤ hEM m + κ) (hA : ∀ o, gM o ≤ hM o + κ) :
    (T₁.comp T₂).TimeBoundPot gE gO hEG hO (a₁ + a₂ + (b₁ + b₂) * κ * (T₁.comp T₂).msgBound)
      (b₁ + b₂) :=
  ⟨κ, gM, hM, gEM, hEM, a₁, b₁, a₂, b₂, h₁, h₂, hE, hA, le_rfl, le_rfl⟩

/-- **Potential running time of a relabelled costed simulator**: that of its simulator, at an
import of the events that the relabelling does not increase and an import of the outputs that
it does not increase. -/
theorem mapPorts.timeBoundPot_timed {T : Simulator.Timed EM OM EG OG U W} {gM : EM → ℕ}
    {gO : OG → ℕ} {hEG : EG → ℕ} {hM : OM → ℕ} {a b : ℕ}
    (hT : T.TimeBoundPot gM gO hEG hM a b) (f : E → EM) (g : OM → O) {gE : E → ℕ} {hO : O → ℕ}
    (hf : ∀ e, gM (f e) ≤ gE e) (hg : ∀ o, hO (g o) ≤ hM o) :
    (Simulator.Timed.mapPorts T f g : Simulator.Timed E O EG OG V W).TimeBoundPot gE gO hEG hO
      a b :=
  ⟨gM, hM, hf, hg, hT⟩

/-- **Potential running time of the costed tensor**: if `πT` and `π'T` erase to `π` and `π'` and
have potential time bounds with constants `a`, `b` and `a'`, `b'`, the costed tensor has the
potential time bound with the imports of the components on the two sides, the constants
`max a a' + 7`, `max b b'` and the sum of the potentials. -/
theorem tensor.timeBoundPot_timed {π : MultiHybrid σ E O EG OG}
    {π' : MultiHybrid σ' E' O' EG' OG'} {πT : MultiHybrid.Timed σ E O EG OG}
    {π'T : MultiHybrid.Timed σ' E' O' EG' OG'} {gE : E → ℕ} {gO : OG → ℕ} {hEG : EG → ℕ}
    {hO : O → ℕ} {gE' : E' → ℕ} {gO' : OG' → ℕ} {hEG' : EG' → ℕ} {hO' : O' → ℕ}
    {a b a' b' : ℕ} (hE : πT.Erases π) (hE' : π'T.Erases π')
    (P : πT.PotentialBound gE gO hEG hO a b) (P' : π'T.PotentialBound gE' gO' hEG' hO' a' b') :
    (tensor.timed (V := V) (W := W) (V' := V') (W' := W') π π' πT π'T).TimeBoundPot
      (Sum.elim gE gE') (Sum.elim gO gO') (Sum.elim hEG hEG') (Sum.elim hO hO') (max a a' + 7)
      (max b b') := by
  obtain ⟨_, _, _, rfl⟩ := hE
  obtain ⟨_, _, _, rfl⟩ := hE'
  exact ofMultiHybrid.timeBoundPot_timed (MultiHybrid.Timed.PotentialBound.tensor _ _ rfl rfl P P')

end Simulator

end CatCrypt.Crypto.UCTransparent
