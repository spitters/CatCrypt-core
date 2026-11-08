/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OracleAdversaryEager
public meta import CatCryptCore.Crypto.OracleAdversaryEager
public import CatCryptCore.Crypto.AKE.PQXDHSquareKEM
public import CatCryptCore.Crypto.AKE.X3DHSquareSigned

/-!
# Tests for `eager_draw`

The first part applies `eager_draw` to the generic statements of
`CatCryptCore.Crypto.OracleAdversaryEager` with their hypotheses in the context: the run
equality with a parametrised eager oracle, its flagged form, and the flagged form with the value
placed in the state. The second part proves two eager-sampling steps of the protocol proofs
with `eager_draw`: `X3DHSquareSigned.flag_lazy` (the key pair of a party drawn at its first
use, placed in the state) and `PQXDHSquareKEM.flag_w_eq_gw1` (the KEM key pair of the
responder session of a guess, read by a parametrised oracle). The side conditions left by the
tactic are those of the original proofs.
-/

@[expose] public section

set_option autoImplicit false

section Generic

open CatCrypt.Crypto

example {σ D R α X : Type} (ν : PMF X) (O₁ : σ → D → PMF (R × σ))
    (O₂ : X → σ → D → PMF (R × σ)) (U : σ → Prop) (use : σ → D → Prop)
    (hno : ∀ x s d, ¬ use s d → O₂ x s d = O₁ s d)
    (huse : ∀ s d, U s → use s d → O₁ s d = ν.bind fun x => O₂ x s d)
    (hnext : ∀ x s d, U s → use s d → ∀ y ∈ (O₂ x s d).support, ¬ U y.2)
    (hpers : ∀ s d, ¬ U s → ∀ y ∈ (O₁ s d).support, ¬ U y.2)
    (hnu : ∀ s d, ¬ U s → ¬ use s d) (A : OracleAdv D R α) (s : σ) (hs : U s) :
    OracleAdv.run O₁ A s = ν.bind fun x => OracleAdv.run (O₂ x) A s := by
  eager_draw U use

example {σ D R α X : Type} (ν : PMF X) (O : σ × Bool → D → PMF (R × (σ × Bool)))
    (set : X → σ → σ) (U : σ → Prop) (use : σ → D → Prop)
    (huse : ∀ t d, U t.1 → use t.1 d → O t d = ν.bind fun x => O (set x t.1, t.2) d)
    (hcomm : ∀ x t d, U t.1 → ¬ use t.1 d →
      O (set x t.1, t.2) d = (O t d).map (Prod.map id fun u => (set x u.1, u.2)))
    (hstay : ∀ t d, U t.1 → ¬ use t.1 d → ∀ y ∈ (O t d).support, U y.2.1)
    (A : OracleAdv D R α) (s : σ) (hs : U s) :
    (OracleAdv.run O A (s, false)).toOuterMeasure {y | y.2.2 = true} =
      ∑' x, ν x * (OracleAdv.run O A (set x s, false)).toOuterMeasure {y | y.2.2 = true} := by
  eager_draw U use

open Classical in
example {σ D R α X : Type} (ν : PMF X) (O₁ : σ → D → PMF (R × σ))
    (O₂ : X → σ → D → PMF (R × σ)) (E : σ → Prop) (U : σ → Prop) (use : σ → D → Prop)
    (hno : ∀ x s d, ¬ use s d → O₂ x s d = O₁ s d)
    (huse : ∀ s d, U s → use s d → O₁ s d = ν.bind fun x => O₂ x s d)
    (hnext : ∀ x s d, U s → use s d → ∀ y ∈ (O₂ x s d).support, ¬ U y.2)
    (hpers : ∀ s d, ¬ U s → ∀ y ∈ (O₁ s d).support, ¬ U y.2)
    (hnu : ∀ s d, ¬ U s → ¬ use s d) (A : OracleAdv D R α) (s : σ) (hs : U s) :
    (OracleAdv.run (OracleAdv.flagWhen (fun _ _ x => E x.2) O₁) A (s, false)).toOuterMeasure
        {y | y.2.2 = true} =
      ∑' x, ν x * (OracleAdv.run (OracleAdv.flagWhen (fun _ _ y => E y.2) (O₂ x)) A
        (s, false)).toOuterMeasure {y | y.2.2 = true} := by
  eager_draw U use

end Generic

namespace CatCrypt.Crypto.AKE.X3DHSquareSigned

open CatCrypt.Core CatCrypt.Crypto CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.Signatures CatCrypt.Crypto.AKE.X3DHSquare CatCrypt.Crypto.AKE.X3DHSquareGDH

variable {S W K VK SK Sig : Type} [Fintype S] [Nonempty S] [DecidableEq W] [Fintype K]
  [Nonempty K]

open Classical in
/-- `flag_lazy` by `eager_draw`: the key pair of `p` drawn at its first use. -/
theorem flag_lazy_eager_draw (A : SigAKEAlg S W VK SK Sig) (p : PartyId)
    (B : OracleAdv (SEv W Sig) (SOut S W K VK Sig) Bool) :
    (OracleAdv.run (OracleAdv.flagWhen (BadAt A p) (filtO A (keyD A))) B
        (fInit, false)).toOuterMeasure {y | y.2.2 = true} =
      ∑' kr, PMF.uniformFintype A.sig.KR kr *
        (OracleAdv.run (OracleAdv.flagWhen (BadAt A p) (filtO A (keyD A))) B
          (((fInit : LSt W VK SK × RSt S W K).1.modKey p (some (A.sig.keygen kr)),
            (fInit : LSt W VK SK × RSt S W K).2), false)).toOuterMeasure
          {y | y.2.2 = true} := by
  eager_draw (fun l : LSt W VK SK × RSt S W K => l.1.keys p = none)
    (fun l d => TrigAt p l.1 d)
    with (fun kr (l : LSt W VK SK × RSt S W K) => (l.1.modKey p (some (A.sig.keygen kr)), l.2))
  · intro t d hs hcs
    simp only [OracleAdv.flagWhen]
    rw [filtO_trigger A p t.1 d hs hcs, PMF.map_bind]
    rfl
  · intro k t d hs hcs
    simp only [OracleAdv.flagWhen]
    rw [filtO_modKey A (keyD A) t.1 p _ d hcs, PMF.map_comp, PMF.map_comp]
    congr 1
    funext x
    have h1 : ¬ BadAt A p t.1 d x := fun h => hcs (trigAt_of_badAt A p _ _ _ h)
    have h2 : ¬ BadAt A p (t.1.1.modKey p (some (A.sig.keygen k)), t.1.2) d
        (x.1, (x.2.1.modKey p (some (A.sig.keygen k)), x.2.2)) := fun h =>
      hcs (trigAt_of_badAt A p _ _ _ h)
    simp [h1, h2]
  · intro t d hs hcs x hx
    simp only [OracleAdv.flagWhen, PMF.support_map, Set.mem_image] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact (filtO_keys_of_not_trig A (keyD A) t.1 p d hcs y hy).trans hs

end CatCrypt.Crypto.AKE.X3DHSquareSigned

namespace CatCrypt.Crypto.AKE.PQXDHSquareKEM

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Relational
open CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.PAKE.DHExtract CatCrypt.Crypto.Assumptions
open CatCrypt.Crypto.KEM.Games (Scheme)
open CatCrypt.Crypto.AKE.PQXDHSquare CatCrypt.Crypto.AKE.PQXDHSquareHops
open CatCrypt.Crypto.AKE.PQXDHSquareGDH

variable {S W K PK SK SS C : Type} [Field S] [Fintype S] [SampleableType W] [Fintype K]
  [Nonempty K] [Inhabited K] [DecidableEq SS] (P : Scheme PK SK SS C) (G : DHGroup S W)
  (g : Guess)

open Classical in
/-- `flag_w_eq_gw1` by `eager_draw`: the KEM key pair of the responder session of `g`. -/
theorem flag_w_eq_gw1_eager_draw (E : WSt S W K PK SK SS C → Prop)
    (B : OracleAdv (OEv W SS C) (OOut S W K PK C) Bool) :
    (OracleAdv.run (OracleAdv.flagWhen (fun _ _ x => E x.2) (wO P G)) B
        (wInit, false)).toOuterMeasure {y | y.2.2 = true} =
      ∑' kp, P.keygen kp * (OracleAdv.run (OracleAdv.flagWhen (fun _ _ x => E x.2)
        (gw1O P G g kp)) B (wInit, false)).toOuterMeasure {y | y.2.2 = true} := by
  eager_draw (fun t => t.1.1.1.x.st.recs (gR g) = none) (fun t e => isCreate g t.1.1 e = true)
  · intro kp t e h
    simp only [Bool.not_eq_true] at h
    simp only [gw1O, wO, subKP, h, Bool.false_eq_true, ↓reduceIte, Prod.mk.eta]
  · intro t e _ h
    unfold wO gw1O
    rw [isCreate_encPk g h, simDist_none_eager P (wStep P G t e)]
    simp only [subKP, h, ↓reduceIte]
  · intro kp t e _ h y hy
    simp only [gw1O, PMF.support_map, Set.mem_image] at hy
    obtain ⟨r, -, rfl⟩ := hy
    have := isCreate_recs P G g h (subKP g kp t.1.1 e r)
    simp only [wStep]
    intro hc
    rw [hc] at this
    cases this
  · intro t e ht y hy
    simp only [wO, PMF.support_map, Set.mem_image] at hy
    obtain ⟨r, -, rfl⟩ := hy
    intro hc
    cases h₀ : t.1.1.1.x.st.recs (gR g) with
    | none => exact ht h₀
    | some r₀ =>
      obtain ⟨r', hr', -⟩ := (wStep_frame P G t e r).1 _ r₀ h₀
      rw [hc] at hr'
      cases hr'
  · intro t e ht h
    rcases e with (⟨sid, pid, peer, role⟩ | ⟨sid, pid⟩) | _ <;>
      simp only [isCreate, Bool.and_eq_true, decide_eq_true_eq, Bool.false_eq_true] at h
    obtain ⟨⟨rfl, rfl, rfl⟩, hn⟩ := h
    exact ht (Option.isNone_iff_eq_none.mp hn)

end CatCrypt.Crypto.AKE.PQXDHSquareKEM
