/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Container.DNLogic
public import CatCryptCore.Crypto.SchnorrForking
public import CatCryptCore.Examples.ChaumPedersen

/-!
# Special soundness of Σ-protocols as derivations, with their extractors as realizers

Special soundness of a Σ-protocol is a derivation in positive many-sorted logic
(`Container/DNLogic.lean`). Over the sorts `I` of a statement and a first message, the hypothesis
"the prover answers every challenge" is the formula `∀ e, ∃ z, V (i, e, z)`, and the conclusion
is `∀ (e₁, e₂) with e₁ ≠ e₂, ∃ w, R (i, w)`. The derivation `ssDeriv` instantiates the hypothesis
at `e₁` and at `e₂`, eliminates the two existentials, and introduces the witness
`ext i e₁ e₂ z₁ z₂` by the atomic step `Deriv.atom₂` from the two accepting transcripts.

Its realizer is the program `Deriv.program` that answers a pair of distinct challenges from an
oracle `g` (a prover's responses): it returns `ext i e₁ e₂ (g e₁) (g e₂)` (`ssDeriv_program`),
consults the oracle at exactly `e₁` and `e₂` (`ssDeriv_queries`), and the use count `2` of the
hypothesis read off the derivation bounds the number of oracle calls (`ssDeriv_useCount`,
`ssDeriv_queries_card_le`). The answer satisfies the relation when the oracle accepts at the two
queries (`ssDeriv_program_sound`), which gives `SpecialSoundness` of a Σ-protocol from its
extractor (`specialSoundness_of_ssDeriv`).

The instances are Schnorr's protocol (`schnorrSS`) and the Chaum–Pedersen protocol (`cpSS`),
with the existing extractors `schnorrExtractor` and `cpExtractor` as the extraction step: the
program of each derivation is the existing extractor's output wherever that output is defined.

## Main definitions

* `ChPair`, `answers`, `extracts` — distinct challenge pairs, the hypothesis and the conclusion;
* `ssDeriv` — special soundness as a derivation from an extraction step;
* `sigmaSS`, `schnorrSS`, `cpSS` — the derivations of a Σ-protocol, of Schnorr's protocol and of
  the Chaum–Pedersen protocol.

## Main results

* `ssDeriv_useCount`, `ssDeriv_queries`, `ssDeriv_queries_card_le` — two oracle calls;
* `ssDeriv_program`, `ssDeriv_program_sound` — the realizer is the extraction step, and it is
  sound;
* `specialSoundness_of_ssDeriv` — special soundness of a Σ-protocol from the derivation;
* `schnorrExtractor_eq_program`, `schnorrExtractor_some_program`, `schnorrSS_sound` — Schnorr;
* `cpExtractor_eq_program`, `cpSS_sound`, `groupExp_extract_eq` — Chaum–Pedersen.

## References

* R. Cramer, *Modular Design of Secure yet Practical Cryptographic Protocols*, PhD thesis,
  University of Amsterdam (1996).
* J. Diller, W. Nahm, *Eine Variante zur Dialectica-Interpretation der Heyting-Arithmetik
  endlicher Typen*, Archiv für mathematische Logik 16 (1974).

Search words: special soundness, Σ-protocol, extractor, rewinding, two transcripts, realizer,
Dialectica interpretation, Diller–Nahm, query bound, Schnorr, Chaum–Pedersen.
-/

set_option autoImplicit false

@[expose] public section

universe u

namespace CatCrypt.Container.DNLogic

/-! ## Special soundness as a derivation -/

section SpecialSoundness

variable {I E Rsp Wit : Type u}

/-- Pairs of distinct challenges. -/
abbrev ChPair (E : Type u) : Type u := {p : E × E // p.1 ≠ p.2}

/-- The hypothesis that the prover answers every challenge: `∀ e, ∃ z, V i e z`. -/
abbrev answers (V : I → E → Rsp → Prop) : Form I :=
  Deriv.allEx (X := fun _ => E) (Y := fun _ => Rsp) fun x => V x.1.1 x.1.2 x.2

/-- The conclusion that every pair of distinct challenges gives a witness:
`∀ (e₁, e₂), e₁ ≠ e₂ → ∃ w, R i w`. -/
abbrev extracts (E : Type u) (R : I → Wit → Prop) : Form I :=
  Deriv.allEx (X := fun _ => ChPair E) (Y := fun _ => Wit) fun x => R x.1.1 x.2

/-- Special soundness as a derivation: instantiate the hypothesis at both challenges of the pair,
eliminate the two responses, and introduce the witness of the extraction step `ext`, whose
correctness `hext` on two accepting transcripts with distinct challenges is the atomic step. -/
def ssDeriv (V : I → E → Rsp → Prop) (R : I → Wit → Prop) (ext : I → E → E → Rsp → Rsp → Wit)
    (hext : ∀ i e₁ e₂ z₁ z₂, e₁ ≠ e₂ → V i e₁ z₁ → V i e₂ z₂ → R i (ext i e₁ e₂ z₁ z₂)) :
    Deriv (fun _ : Fin 1 => answers V) (extracts E R) :=
  .allI <|
  .exE (φ := .atom fun y : (Σ _ : (Σ _ : I, ChPair E), Rsp) => V y.1.1 y.1.2.1.1 y.2)
    (.conv
      (.allE (K := fun _ : (Σ _ : I, ChPair E) => E) (t := fun j => j.2.1.1)
        (φ := .ex (K := fun _ => Rsp) (.atom fun y => V y.1.1.1 y.1.2 y.2))
        (.conv (.hyp 0)))) <|
  .exE (φ := .atom fun y : (Σ _ : (Σ _ : (Σ _ : I, ChPair E), Rsp), Rsp) =>
      V y.1.1.1 y.1.1.2.1.2 y.2)
    (.conv
      (.allE (K := fun _ : (Σ _ : (Σ _ : I, ChPair E), Rsp) => E) (t := fun j => j.1.2.1.2)
        (φ := .ex (K := fun _ => Rsp) (.atom fun y => V y.1.1.1.1 y.1.2 y.2))
        (.conv (.hyp 1)))) <|
  .conv <|
  .exI (K := fun _ : (Σ _ : (Σ _ : (Σ _ : I, ChPair E), Rsp), Rsp) => Wit)
    (t := fun j => ext j.1.1.1 j.1.1.2.1.1 j.1.1.2.1.2 j.1.2 j.2)
    (φ := .atom fun y => R y.1.1.1.1 y.2) <|
  .conv <|
  .atom₂ (p := fun j : (Σ _ : (Σ _ : (Σ _ : I, ChPair E), Rsp), Rsp) =>
      V j.1.1.1 j.1.1.2.1.1 j.1.2)
    (s := fun j : (Σ _ : (Σ _ : (Σ _ : I, ChPair E), Rsp), Rsp) =>
      R j.1.1.1 (ext j.1.1.1 j.1.1.2.1.1 j.1.1.2.1.2 j.1.2 j.2))
    (fun j h₁ h₂ => hext _ _ _ _ _ j.1.1.2.2 h₁ h₂)
    (.conv (.hyp 1)) (.conv (.hyp 0))

variable (V : I → E → Rsp → Prop) (R : I → Wit → Prop) (ext : I → E → E → Rsp → Rsp → Wit)
  (hext : ∀ i e₁ e₂ z₁ z₂, e₁ ≠ e₂ → V i e₁ z₁ → V i e₂ z₂ → R i (ext i e₁ e₂ z₁ z₂))

/-- The derivation uses the hypothesis twice (computed from the derivation). -/
theorem ssDeriv_useCount : (ssDeriv V R ext hext).useCount 0 = 2 := rfl

/-- The realizer of the derivation is the extraction step at the oracle's two responses
(computed from the derivation). -/
theorem ssDeriv_program (g : ∀ (_ : I) (_ : E), Rsp) (i : I) (p : ChPair E) :
    (ssDeriv V R ext hext).program g i p = ext i p.1.1 p.1.2 (g i p.1.1) (g i p.1.2) := rfl

/-- The realizer consults the oracle at the two challenges of the pair. -/
theorem ssDeriv_queries (g : ∀ (_ : I) (_ : E), Rsp) (i : I) (p : ChPair E) :
    (ssDeriv V R ext hext).queries g i p = {p.1.1, p.1.2} := Multiset.pair_comm _ _

/-- The realizer makes at most two oracle calls, the use count of the hypothesis. -/
theorem ssDeriv_queries_card_le (g : ∀ (_ : I) (_ : E), Rsp) (i : I) (p : ChPair E) :
    ((((ssDeriv V R ext hext).queries g i p).card : ℕ) : ℕ∞) ≤ 2 :=
  ssDeriv_useCount V R ext hext ▸ (ssDeriv V R ext hext).queries_card_le g i p

/-- The answer of the realizer satisfies the relation when the oracle's responses at the two
challenges are accepted. -/
theorem ssDeriv_program_sound (g : ∀ (_ : I) (_ : E), Rsp) (i : I) (p : ChPair E)
    (h₁ : V i p.1.1 (g i p.1.1)) (h₂ : V i p.1.2 (g i p.1.2)) :
    R i ((ssDeriv V R ext hext).program g i p) :=
  (ssDeriv V R ext hext).query_sound g i p fun x hx => by
    rw [ssDeriv_queries, Multiset.insert_eq_cons, Multiset.mem_cons, Multiset.mem_singleton]
      at hx
    rcases hx with rfl | rfl
    · exact h₁
    · exact h₂

end SpecialSoundness

/-! ## Σ-protocols -/

section Sigma

open CatCrypt.Examples.Sigma

variable (sp : SigmaProtocol)

/-- Special soundness of a Σ-protocol as a derivation over statements and first messages, from
an extraction step `ext` that is correct on two accepting transcripts with distinct
challenges. -/
def sigmaSS (ext : sp.Statement → sp.Message → sp.Challenge → sp.Challenge → sp.Response →
      sp.Response → sp.Witness)
    (hext : ∀ x m e₁ e₂ z₁ z₂, e₁ ≠ e₂ → sp.verify x m e₁ z₁ = true →
      sp.verify x m e₂ z₂ = true → sp.relation x (ext x m e₁ e₂ z₁ z₂)) :
    Deriv (fun _ : Fin 1 => answers fun (i : sp.Statement × sp.Message) e z =>
        sp.verify i.1 i.2 e z = true)
      (extracts sp.Challenge fun (i : sp.Statement × sp.Message) w => sp.relation i.1 w) :=
  ssDeriv _ _ (fun i => ext i.1 i.2) fun i => hext i.1 i.2

open Classical in
/-- **Special soundness from the derivation.** The program of `sigmaSS`, run on the oracle that
answers the two challenges of two accepting transcripts with their responses, extracts a
witness. -/
theorem specialSoundness_of_ssDeriv
    (ext : sp.Statement → sp.Message → sp.Challenge → sp.Challenge → sp.Response →
      sp.Response → sp.Witness)
    (hext : ∀ x m e₁ e₂ z₁ z₂, e₁ ≠ e₂ → sp.verify x m e₁ z₁ = true →
      sp.verify x m e₂ z₂ = true → sp.relation x (ext x m e₁ e₂ z₁ z₂)) :
    SpecialSoundness sp := by
  refine ⟨fun x tt => (sigmaSS sp ext hext).program
    (fun _ e => if e = tt.challenge1 then tt.response1 else tt.response2)
    (x, tt.message) ⟨(tt.challenge1, tt.challenge2), tt.diff⟩, fun x tt => ?_⟩
  refine ssDeriv_program_sound _ _ _ _ _ (x, tt.message) _ ?_ ?_
  · simpa using tt.accept1
  · simpa [Ne.symm tt.diff] using tt.accept2

end Sigma

/-! ## Schnorr's protocol -/

section Schnorr

open CatCrypt.Examples CatCrypt.Examples.Schnorr CatCrypt.Examples.Sigma

variable (gp : GroupParam)

/-- `schnorrExtractor` is correct on two accepting Schnorr transcripts with distinct
challenges. -/
theorem schnorrExtractor_getD_sound (x : gp.G) (m : gp.Scalar × gp.G)
    (e₁ e₂ z₁ z₂ : gp.Scalar) (hne : e₁ ≠ e₂)
    (h₁ : (schnorrSigma gp).verify x m e₁ z₁ = true)
    (h₂ : (schnorrSigma gp).verify x m e₂ z₂ = true) :
    (schnorrSigma gp).relation x
      ((schnorrExtractor gp x m e₁ e₂ z₁ z₂).getD gp.scalarZero) := by
  simp only [schnorrSigma, schnorrVerifyGP, beq_iff_eq] at h₁ h₂
  simp only [schnorrSigma, dlRelation, schnorrExtractor, beq_iff_eq, hne, ite_false,
    Option.getD_some]
  exact (gp.exp_extract_eq x _ _ _ _ _ h₁ h₂ hne).symm

/-- Special soundness of Schnorr's protocol as a derivation, with `schnorrExtractor` as the
extraction step. -/
noncomputable def schnorrSS :=
  sigmaSS (schnorrSigma gp) (fun x m e₁ e₂ z₁ z₂ =>
    (schnorrExtractor gp x m e₁ e₂ z₁ z₂).getD gp.scalarZero) (schnorrExtractor_getD_sound gp)

/-- The program of `schnorrSS` makes at most two oracle calls. -/
theorem schnorrSS_queries_card_le (g : ∀ (_ : gp.G × (gp.Scalar × gp.G)) (_ : gp.Scalar),
      gp.Scalar) (i : gp.G × (gp.Scalar × gp.G)) (p : ChPair gp.Scalar) :
    ((((schnorrSS gp).queries g i p).card : ℕ) : ℕ∞) ≤ 2 := by
  unfold schnorrSS sigmaSS
  exact ssDeriv_queries_card_le _ _ _ _ g i p

/-- `schnorrExtractor` on the oracle's responses at a pair of distinct challenges returns the
program of `schnorrSS`. -/
theorem schnorrExtractor_eq_program (g : ∀ (_ : gp.G × (gp.Scalar × gp.G)) (_ : gp.Scalar),
      gp.Scalar) (i : gp.G × (gp.Scalar × gp.G)) (p : ChPair gp.Scalar) :
    schnorrExtractor gp i.1 i.2 p.1.1 p.1.2 (g i p.1.1) (g i p.1.2) =
      some ((schnorrSS gp).program g i p) := by
  rw [schnorrSS, sigmaSS, ssDeriv_program]
  simp [schnorrExtractor, beq_iff_eq, p.2]

/-- At a first message `(0, a)`, the program of `schnorrSS` is the witness of
`SchnorrForking.schnorrExtractor_some`. -/
theorem schnorrExtractor_some_program (g : ∀ (_ : gp.G × (gp.Scalar × gp.G)) (_ : gp.Scalar),
      gp.Scalar) (pk a : gp.G) (p : ChPair gp.Scalar) :
    (schnorrSS gp).program g (pk, (gp.scalarZero, a)) p =
      gp.scalarDiv (gp.scalarSub (g (pk, (gp.scalarZero, a)) p.1.1)
        (g (pk, (gp.scalarZero, a)) p.1.2)) (gp.scalarSub p.1.1 p.1.2) :=
  Option.some_injective _ ((schnorrExtractor_eq_program gp g _ p).symm.trans
    (Crypto.SchnorrForking.schnorrExtractor_some pk a _ _ _ _ p.2))

/-- The program of `schnorrSS` returns a discrete logarithm when the oracle's responses at the
two challenges are accepted. -/
theorem schnorrSS_sound (g : ∀ (_ : gp.G × (gp.Scalar × gp.G)) (_ : gp.Scalar), gp.Scalar)
    (i : gp.G × (gp.Scalar × gp.G)) (p : ChPair gp.Scalar)
    (h₁ : schnorrVerifyGP gp i.1 i.2 p.1.1 (g i p.1.1) = true)
    (h₂ : schnorrVerifyGP gp i.1 i.2 p.1.2 (g i p.1.2) = true) :
    dlRelation gp i.1 ((schnorrSS gp).program g i p) := by
  unfold schnorrSS sigmaSS
  exact ssDeriv_program_sound _ _ _ _ g i p h₁ h₂

end Schnorr

/-! ## The Chaum–Pedersen protocol -/

section ChaumPedersen

open CatCrypt.Examples CatCrypt.Examples.ChaumPedersen CatCrypt.Examples.Sigma

variable (gp : GroupParam)

/-- Two accepting transcripts `Bᶻⁱ = A · Uᵉⁱ` with the same commitment and distinct challenges
give `U = B^((z₁ − z₂)/(e₁ − e₂))`, for any base `B`. -/
theorem groupExp_extract_eq (B U A : gp.G) (e₁ e₂ z₁ z₂ : gp.Scalar)
    (hv₁ : gp.groupExp B z₁ = gp.groupMul A (gp.groupExp U e₁))
    (hv₂ : gp.groupExp B z₂ = gp.groupMul A (gp.groupExp U e₂)) (hne : e₁ ≠ e₂) :
    U = gp.groupExp B (gp.scalarDiv (gp.scalarSub z₁ z₂) (gp.scalarSub e₁ e₂)) := by
  obtain ⟨k, rfl⟩ := gp.exp_surj B
  rw [gp.groupExp_exp] at hv₁ hv₂ ⊢
  rw [← gp.exp_extract_eq U A e₁ e₂ _ _ hv₁ hv₂ hne,
    ← scalarMul_div gp k _ _ (gp.scalarSub_ne_zero _ _ hne)]
  congr 2
  rw [gp.scalarSub_eq, gp.scalarSub_eq, gp.scalarMul_add, scalarMul_neg]

/-- `cpExtractor` is correct on two accepting Chaum–Pedersen transcripts with distinct
challenges. -/
theorem cpExtractor_getD_sound (x : CPStatement gp) (m : CPMessage gp)
    (e₁ e₂ z₁ z₂ : gp.Scalar) (hne : e₁ ≠ e₂)
    (h₁ : (chaumPedersenSigma gp).verify x m e₁ z₁ = true)
    (h₂ : (chaumPedersenSigma gp).verify x m e₂ z₂ = true) :
    (chaumPedersenSigma gp).relation x
      ((cpExtractor gp x m e₁ e₂ z₁ z₂).getD gp.scalarZero) := by
  simp only [chaumPedersenSigma, cpVerify, Bool.and_eq_true, beq_iff_eq] at h₁ h₂
  simp only [chaumPedersenSigma, cpRelation, cpExtractor, beq_iff_eq, hne, ite_false,
    Option.getD_some]
  exact ⟨groupExp_extract_eq gp _ _ _ _ _ _ _ h₁.1 h₂.1 hne,
    groupExp_extract_eq gp _ _ _ _ _ _ _ h₁.2 h₂.2 hne⟩

/-- Special soundness of the Chaum–Pedersen protocol as a derivation, with `cpExtractor` as the
extraction step. -/
noncomputable def cpSS :=
  sigmaSS (chaumPedersenSigma gp) (fun x m e₁ e₂ z₁ z₂ =>
    (cpExtractor gp x m e₁ e₂ z₁ z₂).getD gp.scalarZero) (cpExtractor_getD_sound gp)

/-- The program of `cpSS` makes at most two oracle calls. -/
theorem cpSS_queries_card_le (g : ∀ (_ : CPStatement gp × CPMessage gp) (_ : gp.Scalar),
      gp.Scalar) (i : CPStatement gp × CPMessage gp) (p : ChPair gp.Scalar) :
    ((((cpSS gp).queries g i p).card : ℕ) : ℕ∞) ≤ 2 := by
  unfold cpSS sigmaSS
  exact ssDeriv_queries_card_le _ _ _ _ g i p

/-- `cpExtractor` on the oracle's responses at a pair of distinct challenges returns the program
of `cpSS`. -/
theorem cpExtractor_eq_program (g : ∀ (_ : CPStatement gp × CPMessage gp) (_ : gp.Scalar),
      gp.Scalar) (i : CPStatement gp × CPMessage gp) (p : ChPair gp.Scalar) :
    cpExtractor gp i.1 i.2 p.1.1 p.1.2 (g i p.1.1) (g i p.1.2) =
      some ((cpSS gp).program g i p) := by
  rw [cpSS, sigmaSS, ssDeriv_program]
  simp [cpExtractor, beq_iff_eq, p.2]

/-- The program of `cpSS` returns a common discrete logarithm when the oracle's responses at the
two challenges are accepted. -/
theorem cpSS_sound (g : ∀ (_ : CPStatement gp × CPMessage gp) (_ : gp.Scalar), gp.Scalar)
    (i : CPStatement gp × CPMessage gp) (p : ChPair gp.Scalar)
    (h₁ : cpVerify gp i.1 i.2 p.1.1 (g i p.1.1) = true)
    (h₂ : cpVerify gp i.1 i.2 p.1.2 (g i p.1.2) = true) :
    cpRelation gp i.1 ((cpSS gp).program g i p) := by
  unfold cpSS sigmaSS
  exact ssDeriv_program_sound _ _ _ _ g i p h₁ h₂

end ChaumPedersen

end CatCrypt.Container.DNLogic
