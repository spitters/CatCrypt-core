/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Container.DNLogicSigma
public import CatCryptCore.Container.DNGraded
public import CatCryptCore.Crypto.FiatShamirROM.SigmaVerifyCost
public import CatCryptCore.Crypto.FiatShamirROM.Schnorr

/-!
# The Schnorr extraction reduction through the Diller–Nahm layers

The rewinding reduction from Schnorr signatures in the random-oracle model to the discrete
logarithm, followed through four layers.

1. **Logic.** Special soundness of Schnorr's protocol is the derivation `schnorrSS` of positive
   many-sorted logic, whose hypothesis "the prover answers every challenge" is used twice
   (`schnorrSS_useCount`). Its realizer consults the prover at the two challenges and returns
   `(z₁ − z₂)/(e₁ − e₂)`; this is the extractor `FiatShamirROM.schnorrSigma.extract` that the
   rewinding reduction calls (`schnorrSigma_extract_eq_program`), and it returns a discrete
   logarithm on two accepting transcripts (`schnorrSS_sound_dlog`).
2. **Costed reduction.** The time of `extractReduction.timed` at the derived verifier cost is
   `2 · T + c` for an adversary of time `T`, where `c = extractCost` collects the forking
   overhead and the extractor's charge. It is the time of the costed function with use counts
   `extractClocked` (uses `2`, cost `c`) (`extractReduction_stepTimeBound_time`), whose
   Diller–Nahm morphism has the count matrix `[[2, c], [0, 1]]`
   (`extractClocked_countMat`).
3. **Composition and price.** An adversary of time `T` is the costed function `advClocked T`
   with count matrix `[[0, T], [0, 1]]`. The composite of the reduction with the adversary is
   the composite of their Diller–Nahm morphisms, and its count matrix is the product
   `[[2, c], [0, 1]] · [[0, T], [0, 1]] = [[0, c + 2 · T], [0, 1]]`
   (`extract_comp_adv_toDN`, `extract_comp_adv_countMat`). Its price at a data token is
   `c + 2 · T` (`extract_comp_adv_price`), the bound of the time theorem
   (`extractReduction_stepTimeBound_price`).
4. **Representation independence.** The realizer reads the statement and the first message
   only through the prover's responses: it is invariant under every relabelling of the group
   elements (`schnorrSS_program_congr`, `schnorrSS_program_relabel`).

The two uses of the logical layer and the two runs of the adversary in the costed layer are
the same number by inspection: the derivation `schnorrSS` and the reduction
`extractReduction.timed` are separate definitions, and no theorem derives the factor `2` of
the time bound from `useCount`. The costed function `extractClocked` records the counts of
the time theorem and its function component is the identity on statements; the reduction's
program is `extractReduction.timed`, and the link between the two is the equation of the
time bound with `Clocked.time`. The generic-group free theorem of D (`GenericGroup.powT_commute`)
applies to a group computation written as a term of D; the group operations of `GroupParam`
are fields of a structure, not a term of D, so the free theorem of layer 4 is stated for the
realizer, which performs no group operation.

## Main definitions

* `extractCost`, `extractClocked` — the costed form of the rewinding reduction;
* `advClocked` — an adversary of time `T` as a costed function.

## Main results

* `schnorrSS_useCount`, `schnorrSS_queries_card_le'`, `schnorrSigma_extract_eq_program`,
  `schnorrSS_sound_dlog` — special soundness as a derivation with use count `2`, realized by
  the Schnorr extractor;
* `extractReduction_stepTimeBound_time`, `extractClocked_countMat` — the reduction as a
  Diller–Nahm morphism with count matrix `[[2, c], [0, 1]]`;
* `extract_comp_adv_toDN`, `extract_comp_adv_countMat`, `extract_comp_adv_price`,
  `extractReduction_stepTimeBound_price` — composition with the adversary as a product of
  count matrices, and the time bound as its price;
* `schnorrSS_program_congr`, `schnorrSS_program_relabel` — the realizer is independent of the
  representation of the group.

## References

* D. Pointcheval, J. Stern, *Security arguments for digital signatures and blind signatures*,
  J. Cryptology 13(3), 2000.
* J. Diller, W. Nahm, *Eine Variante zur Dialectica-Interpretation der Heyting-Arithmetik
  endlicher Typen*, Archiv für mathematische Logik 16 (1974).

Search words: Schnorr, forking lemma, rewinding, extraction reduction, special soundness,
Diller–Nahm, count matrix, price, use count, representation independence, worked example.
-/

set_option autoImplicit false

@[expose] public section

namespace CatCrypt.Container.SchnorrDN

open CatCrypt.Examples CatCrypt.Crypto CatCrypt.Crypto.FiatShamirROM
open CatCrypt.Container.DNLogic

/-! ## Layer 1: special soundness as a derivation -/

section Logic

variable (gp : GroupParam)

/-- **Use count.** The derivation of special soundness of Schnorr's protocol uses the hypothesis
"the prover answers every challenge" twice. -/
theorem schnorrSS_useCount : (schnorrSS gp).useCount 0 = 2 := by
  unfold schnorrSS sigmaSS
  exact ssDeriv_useCount _ _ _ _

/-- The realizer of `schnorrSS` makes at most `useCount = 2` oracle calls. -/
theorem schnorrSS_queries_card_le' (g : ∀ (_ : gp.G × (gp.Scalar × gp.G)) (_ : gp.Scalar),
      gp.Scalar) (i : gp.G × (gp.Scalar × gp.G)) (p : ChPair gp.Scalar) :
    ((((schnorrSS gp).queries g i p).card : ℕ) : ℕ∞) ≤ (schnorrSS gp).useCount 0 := by
  rw [schnorrSS_useCount]
  exact schnorrSS_queries_card_le gp g i p

/-- **The realizer is the extractor of the reduction.** The program of `schnorrSS` at a pair of
distinct challenges is the extractor `(z₁ − z₂)/(e₁ − e₂)` of the Fiat–Shamir Σ-protocol
`FiatShamirROM.schnorrSigma`, applied to the oracle's responses. -/
theorem schnorrSigma_extract_eq_program
    (g : ∀ (_ : gp.G × (gp.Scalar × gp.G)) (_ : gp.Scalar), gp.Scalar)
    (i : gp.G × (gp.Scalar × gp.G)) (p : ChPair gp.Scalar) :
    (FiatShamirROM.schnorrSigma gp).extract i.1 i.2.2 p.1.1 (g i p.1.1) p.1.2 (g i p.1.2) =
      (schnorrSS gp).program g i p := by
  rw [schnorrSS, sigmaSS, ssDeriv_program]
  simp [Schnorr.schnorrExtractor, FiatShamirROM.schnorrSigma, p.2]

/-- **Soundness of the realizer.** On two accepting Schnorr transcripts the realizer of the
derivation returns a discrete logarithm of the statement. -/
theorem schnorrSS_sound_dlog
    (g : ∀ (_ : gp.G × (gp.Scalar × gp.G)) (_ : gp.Scalar), gp.Scalar)
    (i : gp.G × (gp.Scalar × gp.G)) (p : ChPair gp.Scalar)
    (h₁ : Schnorr.schnorrVerifyGP gp i.1 i.2 p.1.1 (g i p.1.1) = true)
    (h₂ : Schnorr.schnorrVerifyGP gp i.1 i.2 p.1.2 (g i p.1.2) = true) :
    Schnorr.dlRelation gp i.1 ((schnorrSS gp).program g i p) :=
  schnorrSS_sound gp g i p h₁ h₂

end Logic

/-! ## Layer 2: the reduction as a Diller–Nahm morphism -/

section Costed

/-- The cost of the rewinding reduction beyond the two runs of the adversary: the forking
overhead of two runs with at most `qH` hash and `qS` signing queries, and the extractor. -/
def extractCost (qH qS tH tS tF tExt : ℕ) : ℕ :=
  2 * (17 + ((tH + tF + 1) * (qH + 1) + (tS + 1) * qS)) + tExt

/-- The rewinding reduction as a costed function with use counts: it uses the adversary twice
and adds `extractCost`. -/
def extractClocked (X : Type) (qH qS tH tS tF tExt : ℕ) : Clocked X X where
  fn := id
  uses _ := 2
  cost _ := extractCost qH qS tH tS tF tExt

/-- **Count matrix of the reduction.** The Diller–Nahm morphism of the rewinding reduction has
the count matrix `[[2, c], [0, 1]]` with `c = extractCost`. -/
theorem extractClocked_countMat (X : Type) (qH qS tH tS tF tExt : ℕ) (x : X) :
    (Clocked.toDN (extractClocked X qH qS tH tS tF tExt)).countMat x =
      clockMat 2 (extractCost qH qS tH tS tF tExt) :=
  Clocked.countMat_toDN _ x

variable {P : Sigma} {M : Type} [DecidableEq M]

/-- **The time theorem as the time of a costed function.** With `A'` of time `T`, the rewinding
reduction at the derived verifier cost has time at most the time `2 · T + extractCost` of
`extractClocked` at input time `T`. -/
theorem extractReduction_stepTimeBound_time {qH qS : ℕ} (A : Adversary P M qH qS)
    {A' : P.Stmt → OracleAdv.Timed (Query P M) (Answer P) (Forgery P M)}
    (hA : ∀ x, (A' x).erase = A.run x) (tH tS tF tExt : ℕ) {T : ℕ}
    (hT : ∀ x, (A' x).TimeBound T) (x : P.Stmt) :
    OracleAdv.Timed.StepTimeBound
      (extractReduction.timed (Sigma.vkeyFn.timedCost P M) tH tS tF tExt A' x)
      ((extractClocked P.Stmt qH qS tH tS tF tExt).time T x) := by
  have h := extractReduction.timeBound_timed_vkeyFn A hA tH tS tF tExt hT x
  have e : (extractClocked P.Stmt qH qS tH tS tF tExt).time T x =
      2 * (T + 17 + ((tH + tF + 1) * (qH + 1) + (tS + 1) * qS)) + tExt := by
    simp only [Clocked.time, extractClocked, extractCost]
    ring
  rw [e]
  exact h

end Costed

/-! ## Layer 3: composition with the adversary and its price -/

section Composition

/-- An adversary of time `T` as a costed function: it demands no input and costs `T`. -/
def advClocked (X : Type) (T : ℕ) : Clocked X X where
  fn := id
  uses _ := 0
  cost _ := T

/-- **Composition is composition of Diller–Nahm morphisms.** The morphism of the reduction run
on the adversary is the composite of their morphisms, derived from the product of their count
matrices. -/
theorem extract_comp_adv_toDN (X : Type) (qH qS tH tS tF tExt T : ℕ) :
    Clocked.toDN (Clocked.comp (extractClocked X qH qS tH tS tF tExt) (advClocked X T)) =
      DNLens.comp (Clocked.toDN (extractClocked X qH qS tH tS tF tExt))
        (Clocked.toDN (advClocked X T)) :=
  Clocked.toDN_comp_of_countMat _ _

/-- **The count matrix of the composite is the product.**
`[[2, c], [0, 1]] · [[0, T], [0, 1]] = [[0, c + 2 · T], [0, 1]]`. -/
theorem extract_comp_adv_countMat (X : Type) (qH qS tH tS tF tExt T : ℕ) (x : X) :
    (DNLens.comp (Clocked.toDN (extractClocked X qH qS tH tS tF tExt))
        (Clocked.toDN (advClocked X T))).countMat x =
      clockMat 0 (extractCost qH qS tH tS tF tExt + 2 * T) := by
  rw [DNLens.countMat_comp, Clocked.countMat_toDN, Clocked.countMat_toDN, clockMat_mul]
  rfl

/-- **Price of the composite.** At every price of the clock tick `1`, a data token of the
composite of the reduction with the adversary costs `extractCost + 2 · T`. -/
theorem extract_comp_adv_price (X : Type) (qH qS tH tS tF tExt T T₀ : ℕ) (x : X) :
    (DNLens.comp (Clocked.toDN (extractClocked X qH qS tH tS tF tExt))
        (Clocked.toDN (advClocked X T))).price (Clocked.timePrice T₀) x false =
      extractCost qH qS tH tS tF tExt + 2 * T := by
  rw [← extract_comp_adv_toDN, ← Clocked.time_eq_price]
  simp only [Clocked.time, Clocked.comp, extractClocked, advClocked, id]
  ring

variable {P : Sigma} {M : Type} [DecidableEq M]

/-- **The time bound is the price of the composite.** With `A'` of time `T`, the rewinding
reduction at the derived verifier cost has time at most the price of a data token of the
composite Diller–Nahm morphism of the reduction and the adversary. -/
theorem extractReduction_stepTimeBound_price {qH qS : ℕ} (A : Adversary P M qH qS)
    {A' : P.Stmt → OracleAdv.Timed (Query P M) (Answer P) (Forgery P M)}
    (hA : ∀ x, (A' x).erase = A.run x) (tH tS tF tExt : ℕ) {T : ℕ}
    (hT : ∀ x, (A' x).TimeBound T) (T₀ : ℕ) (x : P.Stmt) :
    OracleAdv.Timed.StepTimeBound
      (extractReduction.timed (Sigma.vkeyFn.timedCost P M) tH tS tF tExt A' x)
      ((DNLens.comp (Clocked.toDN (extractClocked P.Stmt qH qS tH tS tF tExt))
        (Clocked.toDN (advClocked P.Stmt T))).price (Clocked.timePrice T₀) x false) := by
  rw [extract_comp_adv_price]
  have h := extractReduction_stepTimeBound_time A hA tH tS tF tExt hT x
  have e : (extractClocked P.Stmt qH qS tH tS tF tExt).time T x =
      extractCost qH qS tH tS tF tExt + 2 * T := by
    simp only [Clocked.time, extractClocked]
  rwa [e] at h

end Composition

/-! ## Layer 4: representation independence of the realizer -/

section Free

variable (gp : GroupParam)

/-- **Representation independence.** The realizer of `schnorrSS` reads the statement and the
first message only through the oracle's responses at the two challenges. -/
theorem schnorrSS_program_congr
    (g g' : ∀ (_ : gp.G × (gp.Scalar × gp.G)) (_ : gp.Scalar), gp.Scalar)
    (i i' : gp.G × (gp.Scalar × gp.G)) (p : ChPair gp.Scalar)
    (h₁ : g i p.1.1 = g' i' p.1.1) (h₂ : g i p.1.2 = g' i' p.1.2) :
    (schnorrSS gp).program g i p = (schnorrSS gp).program g' i' p := by
  rw [← schnorrSigma_extract_eq_program, ← schnorrSigma_extract_eq_program, h₁, h₂]
  rfl

/-- **Relabelling the group.** For every map `φ` of the group elements, the realizer on the
relabelled statement and first message, with the oracle transported along `φ`, returns the
same witness. -/
theorem schnorrSS_program_relabel (φ : gp.G → gp.G)
    (g : ∀ (_ : gp.G × (gp.Scalar × gp.G)) (_ : gp.Scalar), gp.Scalar)
    (i : gp.G × (gp.Scalar × gp.G)) (p : ChPair gp.Scalar) :
    (schnorrSS gp).program g (φ i.1, (i.2.1, φ i.2.2)) p =
      (schnorrSS gp).program (fun j e => g (φ j.1, (j.2.1, φ j.2.2)) e) i p :=
  schnorrSS_program_congr gp _ _ _ _ p rfl rfl

end Free

end CatCrypt.Container.SchnorrDN
