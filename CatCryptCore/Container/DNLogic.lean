/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Container.GodelFibration
public import Mathlib.Data.ENat.Monoid

/-!
# Soundness of positive many-sorted logic in the Gödel fibration, with use counts

The formulas (`Form`) of positive many-sorted intuitionistic logic over Lean sorts have atoms
`I → Prop`, `⊤`, `∧`, `→`, `∨`, the quantifiers `∀`, `∃` over a family of sorts
`K : I → Type u`, and an explicit substitution `Form.sub` along a map of sort contexts. Each
quantifier carries, as an implicit field, a size `∀ i, K i → ℕ` of its sorts: the truth value, the
Diller–Nahm meaning and the use counts ignore it, and only the monotone interpretation reads it.
A formula is interpreted twice: by its truth value `Form.eval`, and by a Dialectica predicate
`Form.dn` of the Gödel fibration of the Diller–Nahm category, through the connectives of
`Container/GodelFibration.lean`.

Derivations (`Deriv`) are natural deduction derivations with hypotheses, as data: the rules of
`⊤`, `∧`, `→`, `∨`, `∀`, `∃`, and the axioms of choice, independence of a universal premise and the
Diller–Nahm form of Markov's principle. A context of `n` hypotheses is a function `Fin n → Form I`,
interpreted as the predicate `ctx Γ` whose witnesses are witnesses of every hypothesis and whose
counter-witnesses are counter-witnesses of one of them.

The soundness theorem `Deriv.realize` sends a derivation to a morphism of the fibre from the
context to the conclusion: its forward map is the realizer, and its backward map sends a
counter-witness of the conclusion to the finite multiset of counter-witnesses of the hypotheses
that it demands. The demand on hypothesis `k` is bounded by the use count `Deriv.useCount d k`
(`Deriv.card_back_le`): one use at a leaf, the maximum at `∧`-introduction, and at a cut
(`→`-elimination, `∃`-elimination) the product of the uses of the cut formula with the uses in the
derivation of the cut formula.

The bound of an implication on its premise is a demand of the formula (`Form.Dem`): at each
implication an optional demand of the premise and an `ℕ∞`, hereditarily through the connectives,
with `Form.Resp` the witnesses and `Form.CResp` the counter-witnesses that respect it. The
premise demand is contravariant: a witness of an implication respects its demand on the
arguments that respect the premise demand, and the order `Form.demLE` of demands reverses it.
`Deriv.uses` takes an annotation of the context by demands (default `⊤`), a transport `HomDem`
of demands along realized axioms and a choice `PremDem` of the premise demand that each
`→`-introduction declares on its new hypothesis, and computes the uses of each hypothesis and
the demand of the conclusion; `Deriv.bounds_resp` states that for a coherent derivation
(`Deriv.Coherent`: at each cut the argument's demand is counter-free and below the premise
demand) and witnesses of the hypotheses respecting their declared demands the realizer respects
these counts on the counter-witnesses respecting the demand of the conclusion. Under the
defaults every derivation is coherent and every counter-witness respects its demand
(`Deriv.coherent_free`, `Deriv.cfree_uses_free`). With `HomDem.keep` a conversion keeps the
demand of the converted derivation (`Deriv.uses_conv_keep`), so that the cut of the negative
translation of an `∃`-introduction (`Deriv.uses_exICut`) and the `→`-introduction around it
(`Deriv.uses_impI_exICut_lt_top`) have finite use counts.

For a hypothesis `∀ x, ∃ y, a (x, y)` (an oracle, adversary or callee, given as a relation) and a
conclusion `∀ x', ∃ z, r (x', z)`, a derivation gives a program `Deriv.program` that answers
`x'` from an oracle `g`, and a multiset `Deriv.queries` of the arguments at which it consults the
oracle, of size at most `useCount d 0`, such that the answer is correct whenever the oracle is
correct at the queries (`Deriv.query_sound`). Under a price of an oracle call the price of the
queries is at most the use count times the largest price (`Deriv.queryPrice_le`): the time of the
program is its own time plus this price, as in `DNLens.price_comp`.

## Main definitions

* `Form`, `Form.eval`, `Form.dn` — formulas and their two interpretations;
* `ctx`, `consF` — contexts and their interpretation;
* `Deriv` — derivations;
* `Deriv.realize` — the morphism of the fibre of a derivation;
* `Deriv.useCount` — the uses of a hypothesis;
* `Form.Dem`, `Form.Resp`, `Form.CResp`, `Form.demLE`, `Form.cfree`, `ctxResp`, `HomDem`,
  `PremDem`, `Deriv.uses`, `Deriv.Coherent` — demands of formulas, their respecting witnesses
  and counter-witnesses, their order, transports and premise choices, and the use counts and
  demand of a derivation with their side conditions;
* `Deriv.program`, `Deriv.queries`, `Deriv.queryPrice` — the program of a derivation from an
  oracle hypothesis.

## Main results

* `Deriv.eval` — soundness for truth;
* `Deriv.holds_dn` — soundness for the Dialectica meaning;
* `Deriv.card_back_le` — quantitative soundness: the demand on a hypothesis is at most its uses;
* `Deriv.bounds_resp` — hereditary quantitative soundness under declared demands;
* `Deriv.bounds_resp_cfree` — hereditary quantitative soundness without premise demands;
* `Form.demLE_sound`, `Form.cresp_of_cfree`, `Deriv.coherent_of`, `Deriv.cfree_uses_of` —
  the order of demands, and counter-free annotations;
* `Deriv.uses_conv_keep`, `Deriv.uses_exICut_sel`, `Deriv.uses_exICut_lt_top_sel`,
  `Deriv.uses_impI_exICut_lt_top`, `Deriv.coherent_impI_exICut` — the demand of a conversion,
  and the finite use counts of the cut of an `∃`-introduction and of the `→`-introduction
  around it;
* `Deriv.queries_card_le`, `Deriv.query_sound`, `Deriv.queryPrice_le` — the query bound;
* `Deriv.useCount_orE`, `Deriv.useCount_efq`, `Deriv.useCount_orComm` — use counts of
  `∨`-elimination, of ex falso (`Deriv.efq`, for a conclusion with a witness) and of the
  commutation of a disjunction.

## References

* K. Gödel, *Über eine bisher noch nicht benützte Erweiterung des finiten Standpunktes*,
  Dialectica 12 (1958).
* J. Diller, W. Nahm, *Eine Variante zur Dialectica-Interpretation der Heyting-Arithmetik
  endlicher Typen*, Archiv für mathematische Logik 16 (1974).
* E. Bishop, *Mathematics as a numerical language*, in Intuitionism and Proof Theory (1970).
* U. Kohlenbach, *Applied Proof Theory: Proof Interpretations and their Use in Mathematics*,
  Springer (2008).

Search words: Dialectica interpretation, Diller–Nahm, soundness, realizer, natural deduction,
use count, query bound, numerical implication, Gödel fibration.
-/

set_option autoImplicit false

@[expose] public section

universe u

namespace CatCrypt.Container.DPred

variable {I : Type u}

/-- Disjunction of Dialectica predicates: a witness of one of the two disjuncts, and a
counter-witness of the disjunct it witnesses. -/
def or (φ ψ : DPred I) : DPred I where
  W i := φ.W i ⊕ ψ.W i
  C i := Sum.elim (φ.C i) (ψ.C i)
  mat i w c := match w, c with
    | .inl a, c => φ.mat i a c
    | .inr b, c => ψ.mat i b c

end CatCrypt.Container.DPred

namespace CatCrypt.Container.DNLogic

open DPred

/-- Formulas of positive many-sorted intuitionistic logic over the sort context `I`. -/
inductive Form : Type u → Type (u + 1)
  /-- An atom: a proposition on the sort context. -/
  | atom {I : Type u} (p : I → Prop) : Form I
  /-- Truth. -/
  | top {I : Type u} : Form I
  /-- Conjunction. -/
  | and {I : Type u} (φ ψ : Form I) : Form I
  /-- Implication. -/
  | imp {I : Type u} (φ ψ : Form I) : Form I
  /-- Disjunction. -/
  | or {I : Type u} (φ ψ : Form I) : Form I
  /-- Universal quantification over a family of sorts, with a size on each sort. Only the
  monotone interpretation reads the size. -/
  | all {I : Type u} {K : I → Type u} {sz : ∀ i, K i → ℕ} (φ : Form (Σ i, K i)) : Form I
  /-- Existential quantification over a family of sorts, with a size on each sort. Only the
  monotone interpretation reads the size. -/
  | ex {I : Type u} {K : I → Type u} {sz : ∀ i, K i → ℕ} (φ : Form (Σ i, K i)) : Form I
  /-- Substitution along a map of sort contexts. -/
  | sub {I J : Type u} (h : J → I) (φ : Form I) : Form J

namespace Form

/-- The truth value of a formula at a point of its sort context. -/
def eval : {I : Type u} → Form I → I → Prop
  | _, .atom p, i => p i
  | _, .top, _ => True
  | _, .and φ ψ, i => φ.eval i ∧ ψ.eval i
  | _, .imp φ ψ, i => φ.eval i → ψ.eval i
  | _, .or φ ψ, i => φ.eval i ∨ ψ.eval i
  | _, .all (K := K) φ, i => ∀ k : K i, φ.eval ⟨i, k⟩
  | _, .ex (K := K) φ, i => ∃ k : K i, φ.eval ⟨i, k⟩
  | _, .sub h φ, j => φ.eval (h j)

/-- The Diller–Nahm interpretation: a Dialectica predicate of the Gödel fibration. -/
def dn : {I : Type u} → Form I → DPred I
  | _, .atom p => DPred.ofProp p
  | _, .top => DPred.top
  | _, .and φ ψ => DPred.and φ.dn ψ.dn
  | _, .imp φ ψ => DPred.imp φ.dn ψ.dn
  | _, .or φ ψ => DPred.or φ.dn ψ.dn
  | _, .all φ => DPred.pi φ.dn
  | _, .ex φ => DPred.sigma φ.dn
  | _, .sub h φ => φ.dn.reindex h

/-- Falsity: the atom `False`. -/
abbrev bot {I : Type u} : Form I := .atom fun _ => False

/-- Negation: implication of falsity. -/
abbrev not {I : Type u} (φ : Form I) : Form I := .imp φ bot

/-- Unfolding equation of `eval` at a disjunction. -/
@[simp] theorem eval_or {I : Type u} (φ ψ : Form I) (i : I) :
    (Form.or φ ψ).eval i = (φ.eval i ∨ ψ.eval i) := rfl

/-- Unfolding equation of `eval` at falsity. -/
@[simp] theorem eval_bot {I : Type u} (i : I) : (bot : Form I).eval i = False := rfl

/-- The witness of a negation that answers every witness of the premise with the unit witness of
falsity and demands no counter-witness. -/
def notW {I : Type u} (φ : Form I) (i : I) : (not φ).dn.W i :=
  ⟨fun _ => PUnit.unit, fun _ _ => 0⟩

/-- The demands of a formula: at each implication an optional demand of the premise (`none`:
every witness of the premise), a bound in `ℕ∞` on the counter-witnesses of the premise that a
witness demands, and the demand of its conclusion; the demands of the components of `∧`, `∨`,
`∀`, `∃` and of a substitution. -/
def Dem : {I : Type u} → Form I → Type
  | _, .atom _ => Unit
  | _, .top => Unit
  | _, .and φ ψ => φ.Dem × ψ.Dem
  | _, .imp φ ψ => Option φ.Dem × ℕ∞ × ψ.Dem
  | _, .or φ ψ => φ.Dem × ψ.Dem
  | _, .all φ => φ.Dem
  | _, .ex φ => φ.Dem
  | _, .sub _ φ => φ.Dem

/-- The demand `⊤` at every implication of a formula, on every witness of its premise. -/
def demTop : {I : Type u} → (φ : Form I) → φ.Dem
  | _, .atom _ => ()
  | _, .top => ()
  | _, .and φ ψ => (φ.demTop, ψ.demTop)
  | _, .imp _ ψ => (none, ⊤, ψ.demTop)
  | _, .or φ ψ => (φ.demTop, ψ.demTop)
  | _, .all φ => φ.demTop
  | _, .ex φ => φ.demTop
  | _, .sub _ φ => φ.demTop

mutual

/-- A witness respects a demand: at each implication, for every witness of the premise that
respects the premise demand and every counter-witness of the conclusion that respects the
conclusion demand, the backward map demands at most the bound of counter-witnesses of the
premise, and the image respects the demand of the conclusion; hereditarily through the other
connectives. -/
def Resp : {I : Type u} → (φ : Form I) → φ.Dem → (i : I) → φ.dn.W i → Prop
  | _, .atom _, _, _, _ => True
  | _, .top, _, _, _ => True
  | _, .and φ ψ, D, i, w => φ.Resp D.1 i w.1 ∧ ψ.Resp D.2 i w.2
  | _, .imp φ ψ, D, i, F => ∀ a, (∀ P, D.1 = some P → φ.Resp P i a) →
      (∀ c, ψ.CResp D.2.2 i (F.1 a) c → (((F.2 a c).card : ℕ) : ℕ∞) ≤ D.2.1) ∧
        ψ.Resp D.2.2 i (F.1 a)
  | _, .or φ ψ, D, i, w =>
    Sum.elim (φ.Resp D.1 i) (ψ.Resp D.2 i) (w : φ.dn.W i ⊕ ψ.dn.W i)
  | _, .all φ, D, i, w => ∀ k, φ.Resp D ⟨i, k⟩ (w k)
  | _, .ex φ, D, i, w => φ.Resp D ⟨i, w.1⟩ w.2
  | _, .sub h φ, D, j, w => φ.Resp D (h j) w

/-- A counter-witness respects a demand: at an implication, its witness of the premise respects
the premise demand and its counter-witness of the conclusion the conclusion demand;
hereditarily through the other connectives. -/
def CResp : {I : Type u} → (φ : Form I) → φ.Dem → (i : I) → (w : φ.dn.W i) → φ.dn.C i w → Prop
  | _, .atom _, _, _, _, _ => True
  | _, .top, _, _, _, _ => True
  | _, .and φ ψ, D, i, w, c => Sum.elim (φ.CResp D.1 i w.1) (ψ.CResp D.2 i w.2) c
  | _, .imp φ ψ, D, i, F, c => (∀ P, D.1 = some P → φ.Resp P i c.1) ∧
      ψ.CResp D.2.2 i (F.1 c.1) c.2
  | _, .or φ ψ, D, i, w, c =>
    Sum.rec (motive := fun s => (DPred.or φ.dn ψ.dn).C i s → Prop)
      (fun a c => φ.CResp D.1 i a c) (fun b c => ψ.CResp D.2 i b c)
      (w : φ.dn.W i ⊕ ψ.dn.W i) c
  | _, .all φ, D, i, w, c => φ.CResp D ⟨i, c.1⟩ (w c.1) c.2
  | _, .ex φ, D, i, w, c => φ.CResp D ⟨i, w.1⟩ w.2 c
  | _, .sub h φ, D, j, w, c => φ.CResp D (h j) w c

end

/-- Every witness respects the demand `⊤`. -/
theorem resp_demTop : ∀ {I : Type u} (φ : Form I) (i : I) (w : φ.dn.W i), φ.Resp φ.demTop i w
  | _, .atom _, _, _ => trivial
  | _, .top, _, _ => trivial
  | _, .and φ ψ, i, w => ⟨resp_demTop φ i w.1, resp_demTop ψ i w.2⟩
  | _, .imp _ ψ, i, F => fun a _ => ⟨fun _ _ => le_top, resp_demTop ψ i (F.1 a)⟩
  | _, .or φ ψ, i, w =>
    Sum.rec (motive := fun s => Sum.elim (φ.Resp φ.demTop i) (ψ.Resp ψ.demTop i) s)
      (fun a => resp_demTop φ i a) (fun b => resp_demTop ψ i b) (w : φ.dn.W i ⊕ ψ.dn.W i)
  | _, .all φ, i, w => fun k => resp_demTop φ ⟨i, k⟩ (w k)
  | _, .ex φ, i, w => resp_demTop φ ⟨i, w.1⟩ w.2
  | _, .sub h φ, j, w => resp_demTop φ (h j) w

/-- A demand is counter-free when its implications in positive position declare no premise
demand: every counter-witness respects it (`Form.cresp_of_cfree`). -/
def cfree : {I : Type u} → (φ : Form I) → φ.Dem → Bool
  | _, .atom _, _ => true
  | _, .top, _ => true
  | _, .and φ ψ, D => φ.cfree D.1 && ψ.cfree D.2
  | _, .imp _ ψ, D => D.1.isNone && ψ.cfree D.2.2
  | _, .or φ ψ, D => φ.cfree D.1 && ψ.cfree D.2
  | _, .all φ, D => φ.cfree D
  | _, .ex φ, D => φ.cfree D
  | _, .sub _ φ, D => φ.cfree D

/-- Every counter-witness respects a counter-free demand. -/
theorem cresp_of_cfree : ∀ {I : Type u} (φ : Form I) (D : φ.Dem), φ.cfree D = true →
    ∀ (i : I) (w : φ.dn.W i) (c : φ.dn.C i w), φ.CResp D i w c
  | _, .atom _, _, _, _, _, _ => trivial
  | _, .top, _, _, _, _, _ => trivial
  | _, .and φ ψ, D, h, i, w, c => by
    simp only [cfree, Bool.and_eq_true] at h
    cases c with
    | inl c => exact cresp_of_cfree φ D.1 h.1 i w.1 c
    | inr c => exact cresp_of_cfree ψ D.2 h.2 i w.2 c
  | _, .imp _ ψ, D, h, i, F, c => by
    simp only [cfree, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
    refine ⟨fun P hP => ?_, cresp_of_cfree ψ D.2.2 h.2 i (F.1 c.1) c.2⟩
    rw [h.1] at hP
    cases hP
  | _, .or φ ψ, D, h, i, w, c => by
    simp only [cfree, Bool.and_eq_true] at h
    revert c
    change ∀ c : (DPred.or φ.dn ψ.dn).C i (w : φ.dn.W i ⊕ ψ.dn.W i),
      Sum.rec (motive := fun s => (DPred.or φ.dn ψ.dn).C i s → Prop)
        (fun a c => φ.CResp D.1 i a c) (fun b c => ψ.CResp D.2 i b c) _ c
    cases (w : φ.dn.W i ⊕ ψ.dn.W i) with
    | inl a => exact fun c => cresp_of_cfree φ D.1 h.1 i a c
    | inr b => exact fun c => cresp_of_cfree ψ D.2 h.2 i b c
  | _, .all φ, D, h, i, w, c => cresp_of_cfree φ D h ⟨i, c.1⟩ (w c.1) c.2
  | _, .ex φ, D, h, i, w, c => cresp_of_cfree φ D h ⟨i, w.1⟩ w.2 c
  | _, .sub _ φ, D, h, j, w, c => cresp_of_cfree φ D h _ w c

/-- The demand `⊤` is counter-free. -/
theorem cfree_demTop : ∀ {I : Type u} (φ : Form I), φ.cfree φ.demTop = true
  | _, .atom _ => rfl
  | _, .top => rfl
  | _, .and φ ψ => by simp only [cfree, demTop, cfree_demTop φ, cfree_demTop ψ, Bool.and_self]
  | _, .imp _ ψ => by simp only [cfree, demTop, cfree_demTop ψ, Option.isNone_none, Bool.and_self]
  | _, .or φ ψ => by simp only [cfree, demTop, cfree_demTop φ, cfree_demTop ψ, Bool.and_self]
  | _, .all φ => cfree_demTop φ
  | _, .ex φ => cfree_demTop φ
  | _, .sub _ φ => cfree_demTop φ

/-- The order of demands: `D ≤ D'` when every witness respecting `D` respects `D'` and every
counter-witness respecting `D'` respects `D` (`Form.demLE_sound`). It is contravariant in the
premise demand of an implication, where `none` is the least demand, and covariant in the bound
and in the conclusion demand. -/
def demLE : {I : Type u} → (φ : Form I) → φ.Dem → φ.Dem → Bool
  | _, .atom _, _, _ => true
  | _, .top, _, _ => true
  | _, .and φ ψ, D, D' => φ.demLE D.1 D'.1 && ψ.demLE D.2 D'.2
  | _, .imp φ ψ, D, D' => D.1.elim true (fun P => D'.1.elim false fun P' => φ.demLE P' P) &&
      decide (D.2.1 ≤ D'.2.1) && ψ.demLE D.2.2 D'.2.2
  | _, .or φ ψ, D, D' => φ.demLE D.1 D'.1 && ψ.demLE D.2 D'.2
  | _, .all φ, D, D' => φ.demLE D D'
  | _, .ex φ, D, D' => φ.demLE D D'
  | _, .sub _ φ, D, D' => φ.demLE D D'

/-- Soundness of the order of demands: a witness respecting the smaller demand respects the
larger one, and a counter-witness respecting the larger demand respects the smaller one. -/
theorem demLE_sound : ∀ {I : Type u} (φ : Form I) (D D' : φ.Dem), φ.demLE D D' = true →
    ∀ (i : I) (w : φ.dn.W i),
      (φ.Resp D i w → φ.Resp D' i w) ∧ ∀ c, φ.CResp D' i w c → φ.CResp D i w c
  | _, .atom _, _, _, _, _, _ => ⟨id, fun _ => id⟩
  | _, .top, _, _, _, _, _ => ⟨id, fun _ => id⟩
  | _, .and φ ψ, D, D', h, i, w => by
    simp only [demLE, Bool.and_eq_true] at h
    have h₁ := demLE_sound φ D.1 D'.1 h.1 i w.1
    have h₂ := demLE_sound ψ D.2 D'.2 h.2 i w.2
    refine ⟨fun hw => ⟨h₁.1 hw.1, h₂.1 hw.2⟩, fun c hc => ?_⟩
    cases c with
    | inl c => exact h₁.2 c hc
    | inr c => exact h₂.2 c hc
  | _, .imp φ ψ, D, D', h, i, F => by
    simp only [demLE, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hP, hN⟩, hψ⟩ := h
    have hpre : ∀ a, (∀ P', D'.1 = some P' → φ.Resp P' i a) → ∀ P, D.1 = some P →
        φ.Resp P i a := by
      intro a ha P hP'
      rw [hP'] at hP
      cases hD' : D'.1 with
      | none => rw [hD'] at hP; cases hP
      | some P' =>
        rw [hD'] at hP
        exact (demLE_sound φ P' P hP i a).1 (ha P' hD')
    refine ⟨fun hF a ha => ?_, fun c hc => ⟨hpre c.1 hc.1, ?_⟩⟩
    · obtain ⟨hc, hr⟩ := hF a (hpre a ha)
      refine ⟨fun c hc' => (hc c ((demLE_sound ψ _ _ hψ i _).2 c hc')).trans hN, ?_⟩
      exact (demLE_sound ψ _ _ hψ i _).1 hr
    · exact (demLE_sound ψ _ _ hψ i _).2 c.2 hc.2
  | _, .or φ ψ, D, D', h, i, w => by
    simp only [demLE, Bool.and_eq_true] at h
    change (Sum.elim (φ.Resp D.1 i) (ψ.Resp D.2 i) (w : φ.dn.W i ⊕ ψ.dn.W i) →
        Sum.elim (φ.Resp D'.1 i) (ψ.Resp D'.2 i) (w : φ.dn.W i ⊕ ψ.dn.W i)) ∧
      ∀ c : (DPred.or φ.dn ψ.dn).C i (w : φ.dn.W i ⊕ ψ.dn.W i),
        Sum.rec (motive := fun s => (DPred.or φ.dn ψ.dn).C i s → Prop)
          (fun a c => φ.CResp D'.1 i a c) (fun b c => ψ.CResp D'.2 i b c) _ c →
        Sum.rec (motive := fun s => (DPred.or φ.dn ψ.dn).C i s → Prop)
          (fun a c => φ.CResp D.1 i a c) (fun b c => ψ.CResp D.2 i b c) _ c
    cases (w : φ.dn.W i ⊕ ψ.dn.W i) with
    | inl a => exact demLE_sound φ D.1 D'.1 h.1 i a
    | inr b => exact demLE_sound ψ D.2 D'.2 h.2 i b
  | _, .all φ, D, D', h, i, w =>
    ⟨fun hw k => (demLE_sound φ D D' h ⟨i, k⟩ (w k)).1 (hw k),
      fun c hc => (demLE_sound φ D D' h ⟨i, c.1⟩ (w c.1)).2 c.2 hc⟩
  | _, .ex φ, D, D', h, i, w => demLE_sound φ D D' h ⟨i, w.1⟩ w.2
  | _, .sub _ φ, D, D', h, j, w => demLE_sound φ D D' h _ w

/-- The argument demand of a formula: the bound at an implication, `⊤` otherwise. -/
def demArg : {I : Type u} → (φ : Form I) → φ.Dem → ℕ∞
  | _, .imp _ _, D => D.2.1
  | _, _, _ => ⊤

end Form

variable {I : Type u} {n : ℕ}

/-- The context `Γ` extended by the hypothesis `φ` at position `0`. -/
def consF (φ : Form I) (Γ : Fin n → Form I) : Fin (n + 1) → Form I
  | ⟨0, _⟩ => φ
  | ⟨j + 1, h⟩ => Γ ⟨j, Nat.lt_of_succ_lt_succ h⟩

/-- A property of every hypothesis of an extended context. -/
theorem consF_forall (P : Form I → Prop) {φ : Form I} {Γ : Fin n → Form I} (hφ : P φ)
    (hΓ : ∀ k, P (Γ k)) : ∀ k, P (consF φ Γ k)
  | ⟨0, _⟩ => hφ
  | ⟨_ + 1, _⟩ => hΓ _

/-- The interpretation of a context: a witness of every hypothesis, and a counter-witness of one
hypothesis. -/
def ctx (Γ : Fin n → Form I) : DPred I where
  W i := ∀ k, (Γ k).dn.W i
  C i w := Σ k, (Γ k).dn.C i (w k)
  mat i w c := (Γ c.1).dn.mat i (w c.1) c.2

/-- The meaning of a context is the meaning of each hypothesis. -/
theorem holds_ctx (Γ : Fin n → Form I) (i : I) :
    (ctx Γ).holds i ↔ ∀ k, (Γ k).dn.holds i := by
  constructor
  · rintro ⟨w, hw⟩ k
    exact ⟨w k, fun c => hw ⟨k, c⟩⟩
  · intro h
    choose w hw using h
    exact ⟨w, fun c => hw c.1 c.2⟩

section Cons

variable {φ : Form I} {Γ : Fin n → Form I}

/-- A witness of an extended context. -/
def consW (i : I) (a : φ.dn.W i) (w : (ctx Γ).W i) : (ctx (consF φ Γ)).W i := fun
  | ⟨0, _⟩ => a
  | ⟨j + 1, h⟩ => w ⟨j, Nat.lt_of_succ_lt_succ h⟩

/-- The demands of an extended context: `a` on the new hypothesis, `δ` on the old ones. -/
def consD (a : φ.Dem) (δ : ∀ k, (Γ k).Dem) : ∀ k, (consF φ Γ k).Dem
  | ⟨0, _⟩ => a
  | ⟨j + 1, h⟩ => δ ⟨j, Nat.lt_of_succ_lt_succ h⟩

/-- The counter-witness of the new hypothesis, if it is one. -/
def headC? {i : I} {a : φ.dn.W i} {w : (ctx Γ).W i} :
    (ctx (consF φ Γ)).C i (consW i a w) → Option (φ.dn.C i a)
  | ⟨⟨0, _⟩, c⟩ => some c
  | ⟨⟨_ + 1, _⟩, _⟩ => none

/-- The counter-witness of an old hypothesis, if it is one. -/
def tailC? {i : I} {a : φ.dn.W i} {w : (ctx Γ).W i} :
    (ctx (consF φ Γ)).C i (consW i a w) → Option ((ctx Γ).C i w)
  | ⟨⟨0, _⟩, _⟩ => none
  | ⟨⟨j + 1, h⟩, c⟩ => some ⟨⟨j, Nat.lt_of_succ_lt_succ h⟩, c⟩

/-- A counter-witness of an extended context is withstood when its part in the new hypothesis
and its part in the old ones are. -/
theorem ctx_cons_mat {i : I} {a : φ.dn.W i} {w : (ctx Γ).W i}
    (y : (ctx (consF φ Γ)).C i (consW i a w))
    (hh : ∀ c, headC? y = some c → φ.dn.mat i a c)
    (ht : ∀ c, tailC? y = some c → (ctx Γ).mat i w c) :
    (ctx (consF φ Γ)).mat i (consW i a w) y := by
  obtain ⟨⟨_ | j, hj⟩, c⟩ := y
  · exact hh c rfl
  · exact ht _ rfl

/-- `headC?` selects the counter-witnesses at position `0`. -/
theorem headC?_fst {i : I} {a : φ.dn.W i} {w : (ctx Γ).W i}
    (y : (ctx (consF φ Γ)).C i (consW i a w)) (c : φ.dn.C i a) (h : headC? y = some c) :
    y.1 = 0 := by
  obtain ⟨⟨_ | j, hj⟩, c'⟩ := y
  · exact Fin.ext (by simp)
  · simp [headC?] at h

/-- `tailC?` sends a counter-witness at position `k + 1` to one at position `k`. -/
theorem tailC?_fst {i : I} {a : φ.dn.W i} {w : (ctx Γ).W i}
    (y : (ctx (consF φ Γ)).C i (consW i a w)) (c : (ctx Γ).C i w) (h : tailC? y = some c) :
    y.1 = c.1.succ := by
  obtain ⟨⟨_ | j, hj⟩, c'⟩ := y
  · simp [tailC?] at h
  · simp only [tailC?] at h
    cases h
    rfl

end Cons

/-- A witness of a context respects an annotation of the context by demands: `none` declares
`⊤` on every hypothesis, `some δ` the demand `δ k` on hypothesis `k`. -/
def ctxResp (Γ : Fin n → Form I) : Option (∀ k, (Γ k).Dem) → (i : I) → (ctx Γ).W i → Prop
  | none, _, _ => True
  | some δ, i, w => ∀ k, (Γ k).Resp (δ k) i (w k)

/-- A witness of an extended context respects the extended annotation. -/
theorem ctxResp_cons {φ : Form I} {Γ : Fin n → Form I} {δ : Option (∀ k, (Γ k).Dem)} {i : I}
    {w : (ctx Γ).W i} (hw : ctxResp Γ δ i w) (D : φ.Dem) {a : φ.dn.W i} (ha : φ.Resp D i a) :
    ctxResp (consF φ Γ) (δ.map (consD D)) i (consW i a w) := by
  cases δ with
  | none => trivial
  | some δ =>
    intro k
    match k with
    | ⟨0, _⟩ => exact ha
    | ⟨j + 1, h⟩ => exact hw ⟨j, Nat.lt_of_succ_lt_succ h⟩

/-- A counter-witness of the context reindexed along `Sigma.fst`, at `⟨i, x⟩`, is a
counter-witness of the context at `i`. -/
def ctxSubC {K : I → Type u} (Γ : Fin n → Form I) (i : I) (x : K i) (w : (ctx Γ).W i)
    (c : (ctx fun k => (Γ k).sub Sigma.fst).C ⟨i, x⟩ w) : (ctx Γ).C i w := c

section OrCase

variable {φ ψ χ : Form I} {Γ : Fin n → Form I}

/-- The witness of a case analysis on a witness of `φ ∨ ψ`: the realizer of the branch it
selects. -/
def orCaseFwd (E₁ : (ctx (consF φ Γ)).Hom χ.dn) (E₂ : (ctx (consF ψ Γ)).Hom χ.dn) (i : I)
    (w : (ctx Γ).W i) : (DPred.or φ.dn ψ.dn).W i → χ.dn.W i
  | .inl a => E₁.fwd i (consW i a w)
  | .inr b => E₂.fwd i (consW i b w)

/-- The demand of a case analysis on a witness `x` of `φ ∨ ψ` whose counter-witnesses demand
`g`: the demand of the selected branch on the old hypotheses, and `g` at its demand on the new
one. -/
def orCaseBack (E₁ : (ctx (consF φ Γ)).Hom χ.dn) (E₂ : (ctx (consF ψ Γ)).Hom χ.dn) (i : I)
    (w : (ctx Γ).W i) : (x : (DPred.or φ.dn ψ.dn).W i) →
    ((DPred.or φ.dn ψ.dn).C i x → Multiset ((ctx Γ).C i w)) →
    χ.dn.C i (orCaseFwd E₁ E₂ i w x) → Multiset ((ctx Γ).C i w)
  | .inl a, g, c => ((E₁.back i (consW i a w) c).filterMap tailC?) +
      ((E₁.back i (consW i a w) c).filterMap headC?).bind g
  | .inr b, g, c => ((E₂.back i (consW i b w) c).filterMap tailC?) +
      ((E₂.back i (consW i b w) c).filterMap headC?).bind g

/-- Soundness of the case analysis. -/
theorem orCase_sound (E₁ : (ctx (consF φ Γ)).Hom χ.dn) (E₂ : (ctx (consF ψ Γ)).Hom χ.dn)
    (i : I) (w : (ctx Γ).W i) (x : (DPred.or φ.dn ψ.dn).W i)
    (g : (DPred.or φ.dn ψ.dn).C i x → Multiset ((ctx Γ).C i w))
    (hg : ∀ c, (∀ y ∈ g c, (ctx Γ).mat i w y) → (DPred.or φ.dn ψ.dn).mat i x c)
    (c : χ.dn.C i (orCaseFwd E₁ E₂ i w x))
    (h : ∀ y ∈ orCaseBack E₁ E₂ i w x g c, (ctx Γ).mat i w y) :
    χ.dn.mat i (orCaseFwd E₁ E₂ i w x) c := by
  cases x with
  | inl a =>
    exact E₁.sound i _ c fun y hy => ctx_cons_mat y
      (fun z hz => hg z fun v hv => h v (Multiset.mem_add.2 (.inr
        (Multiset.mem_bind.2 ⟨z, (Multiset.mem_filterMap _ _).2 ⟨y, hy, hz⟩, hv⟩))))
      (fun z hz => h z (Multiset.mem_add.2 (.inl ((Multiset.mem_filterMap _ _).2 ⟨y, hy, hz⟩))))
  | inr b =>
    exact E₂.sound i _ c fun y hy => ctx_cons_mat y
      (fun z hz => hg z fun v hv => h v (Multiset.mem_add.2 (.inr
        (Multiset.mem_bind.2 ⟨z, (Multiset.mem_filterMap _ _).2 ⟨y, hy, hz⟩, hv⟩))))
      (fun z hz => h z (Multiset.mem_add.2 (.inl ((Multiset.mem_filterMap _ _).2 ⟨y, hy, hz⟩))))

end OrCase

/-- A transport of demands along morphisms of the Diller–Nahm meanings: a demand of the target
for each demand of the source, respected by the image of every witness respecting the source
demand. It gives the demand of the conclusion of a realized axiom `Deriv.hom`. -/
structure HomDem : Type (u + 1) where
  /-- The demand of the target. -/
  map : ∀ {I : Type u} {φ ψ : Form I}, φ.dn.Hom ψ.dn → φ.Dem → ψ.Dem
  /-- The image of a witness respecting the source demand respects the target demand. -/
  sound : ∀ {I : Type u} {φ ψ : Form I} (f : φ.dn.Hom ψ.dn) (D : φ.Dem) (i : I)
    (w : φ.dn.W i), φ.Resp D i w → ψ.Resp (map f D) i (f.fwd i w)

/-- The transport that gives the demand `⊤` to every target. -/
def HomDem.top : HomDem.{u} where
  map {_ _ ψ} _ _ := ψ.demTop
  sound {_ _ ψ} _ _ i _ _ := Form.resp_demTop ψ i _

/-- A choice of premise demands: the demand that `→`-introduction declares on the premise `φ`,
on its new hypothesis and in the demand of the implication (`none`: every witness). -/
structure PremDem : Type (u + 1) where
  /-- The premise demand declared at an implication with premise `φ`. -/
  sel : ∀ {I : Type u} (φ : Form I), Option φ.Dem

/-- The choice that declares no premise demand. -/
def PremDem.free : PremDem.{u} where
  sel _ := Option.none

/-- Natural deduction derivations of positive many-sorted logic, as data. -/
inductive Deriv : {I : Type u} → {n : ℕ} → (Fin n → Form I) → Form I → Type (u + 1)
  /-- A hypothesis. -/
  | hyp {I : Type u} {n : ℕ} {Γ : Fin n → Form I} (k : Fin n) : Deriv Γ (Γ k)
  /-- `⊤`-introduction. -/
  | topI {I : Type u} {n : ℕ} {Γ : Fin n → Form I} : Deriv Γ .top
  /-- `∧`-introduction. -/
  | andI {I : Type u} {n : ℕ} {Γ : Fin n → Form I} {φ ψ : Form I} (d : Deriv Γ φ)
      (e : Deriv Γ ψ) : Deriv Γ (.and φ ψ)
  /-- `∧`-elimination, left. -/
  | andE₁ {I : Type u} {n : ℕ} {Γ : Fin n → Form I} {φ ψ : Form I} (d : Deriv Γ (.and φ ψ)) :
      Deriv Γ φ
  /-- `∧`-elimination, right. -/
  | andE₂ {I : Type u} {n : ℕ} {Γ : Fin n → Form I} {φ ψ : Form I} (d : Deriv Γ (.and φ ψ)) :
      Deriv Γ ψ
  /-- `→`-introduction: the premise becomes the hypothesis at position `0`. -/
  | impI {I : Type u} {n : ℕ} {Γ : Fin n → Form I} {φ ψ : Form I} (d : Deriv (consF φ Γ) ψ) :
      Deriv Γ (.imp φ ψ)
  /-- `→`-elimination. -/
  | impE {I : Type u} {n : ℕ} {Γ : Fin n → Form I} {φ ψ : Form I} (d : Deriv Γ (.imp φ ψ))
      (e : Deriv Γ φ) : Deriv Γ ψ
  /-- `∨`-introduction, left. -/
  | orI₁ {I : Type u} {n : ℕ} {Γ : Fin n → Form I} {φ ψ : Form I} (d : Deriv Γ φ) :
      Deriv Γ (.or φ ψ)
  /-- `∨`-introduction, right. -/
  | orI₂ {I : Type u} {n : ℕ} {Γ : Fin n → Form I} {φ ψ : Form I} (d : Deriv Γ ψ) :
      Deriv Γ (.or φ ψ)
  /-- `∨`-elimination: each disjunct becomes the hypothesis at position `0` of its branch. -/
  | orE {I : Type u} {n : ℕ} {Γ : Fin n → Form I} {φ ψ χ : Form I} (d : Deriv Γ (.or φ ψ))
      (e₁ : Deriv (consF φ Γ) χ) (e₂ : Deriv (consF ψ Γ) χ) : Deriv Γ χ
  /-- `∀`-introduction: a derivation over the extended sort context. -/
  | allI {I : Type u} {n : ℕ} {Γ : Fin n → Form I} {K : I → Type u} {s : ∀ i, K i → ℕ}
      {φ : Form (Σ i, K i)}
      (d : Deriv (fun k => (Γ k).sub Sigma.fst) φ) : Deriv Γ (.all (sz := s) φ)
  /-- `∀`-elimination at a term `t`. -/
  | allE {I : Type u} {n : ℕ} {Γ : Fin n → Form I} {K : I → Type u} {s : ∀ i, K i → ℕ}
      {φ : Form (Σ i, K i)}
      (t : ∀ i, K i) (d : Deriv Γ (.all (sz := s) φ)) : Deriv Γ (φ.sub fun i => ⟨i, t i⟩)
  /-- `∃`-introduction at a term `t`. -/
  | exI {I : Type u} {n : ℕ} {Γ : Fin n → Form I} {K : I → Type u} {s : ∀ i, K i → ℕ}
      {φ : Form (Σ i, K i)}
      (t : ∀ i, K i) (d : Deriv Γ (φ.sub fun i => ⟨i, t i⟩)) : Deriv Γ (.ex (sz := s) φ)
  /-- `∃`-elimination: the body becomes the hypothesis at position `0` over the extended sort
  context. -/
  | exE {I : Type u} {n : ℕ} {Γ : Fin n → Form I} {K : I → Type u} {s : ∀ i, K i → ℕ}
      {φ : Form (Σ i, K i)}
      {ψ : Form I} (d : Deriv Γ (.ex (sz := s) φ))
      (e : Deriv (consF φ fun k => (Γ k).sub Sigma.fst) (ψ.sub Sigma.fst)) : Deriv Γ ψ
  /-- The axiom of choice: `∀ k ∃ l, φ` gives `∃ f ∀ k, φ (k, f k)`. The size `sF` of the
  functions is free. -/
  | ac {I : Type u} {n : ℕ} {Γ : Fin n → Form I} {K : I → Type u} {L : (Σ i, K i) → Type u}
      {sK : ∀ i, K i → ℕ} {sL : ∀ x, L x → ℕ} {sF : ∀ i, (∀ k : K i, L ⟨i, k⟩) → ℕ}
      {φ : Form (Σ x : Σ i, K i, L x)} (d : Deriv Γ (.all (sz := sK) (.ex (sz := sL) φ))) :
      Deriv Γ (.ex (K := fun i => ∀ k : K i, L ⟨i, k⟩) (sz := sF)
        (.all (K := fun p => K p.1) (sz := fun p => sK p.1)
          (φ.sub fun y => ⟨⟨y.1.1, y.2⟩, y.1.2 y.2⟩)))
  /-- Independence of a universal premise, for inhabited sorts of the existential. -/
  | ip {I : Type u} {n : ℕ} {Γ : Fin n → Form I} {K L : I → Type u} (p : (Σ i, K i) → Prop)
      {sK : ∀ i, K i → ℕ} {sL : ∀ i, L i → ℕ}
      {ψ : Form (Σ i, L i)} (hL : ∀ i, Nonempty (L i))
      (d : Deriv Γ (.imp (.all (sz := sK) (.atom p)) (.ex (sz := sL) ψ))) :
      Deriv Γ (.ex (sz := sL) (.imp ((Form.all (sz := sK) (.atom p)).sub Sigma.fst) ψ))
  /-- Markov's principle, Diller–Nahm form: finitely many candidates suffice. The size `sM` of
  the finite multisets of candidates is free. -/
  | markov {I : Type u} {n : ℕ} {Γ : Fin n → Form I} {K : I → Type u} (p : (Σ i, K i) → Prop)
      {sK : ∀ i, K i → ℕ} {sM : ∀ i, Multiset (K i) → ℕ}
      (q : I → Prop) (d : Deriv Γ (.imp (.all (sz := sK) (.atom p)) (.atom q))) :
      Deriv Γ (.ex (K := fun i => Multiset (K i)) (sz := sM)
        (.atom fun x => (∀ k ∈ x.2, p ⟨x.1, k⟩) → q x.1))
  /-- A realized axiom: a true entailment given by a morphism `f` of the Diller–Nahm meanings
  whose backward map demands at most `N` counter-witnesses of the premise. -/
  | hom {I : Type u} {n : ℕ} {Γ : Fin n → Form I} {φ ψ : Form I} (f : φ.dn.Hom ψ.dn) (N : ℕ)
      (hN : ∀ i w c, (f.back i w c).card ≤ N) (hev : ∀ i, φ.eval i → ψ.eval i)
      (d : Deriv Γ φ) : Deriv Γ ψ
  /-- An atom entailed by two atoms: its counter-witness demands one of each premise. -/
  | atom₂ {I : Type u} {n : ℕ} {Γ : Fin n → Form I} {p q s : I → Prop}
      (h : ∀ i, p i → q i → s i) (d : Deriv Γ (.atom p)) (e : Deriv Γ (.atom q)) :
      Deriv Γ (.atom s)

namespace Deriv

/-- **Soundness for truth.** A derivation sends true hypotheses to a true conclusion. -/
theorem eval {Γ : Fin n → Form I} {φ : Form I} (d : Deriv Γ φ) (i : I)
    (h : ∀ k, (Γ k).eval i) : φ.eval i := by
  induction d with
  | hyp k => exact h k
  | topI => trivial
  | andI d e ihd ihe => exact ⟨ihd i h, ihe i h⟩
  | andE₁ d ih => exact (ih i h).1
  | andE₂ d ih => exact (ih i h).2
  | impI d ih => exact fun ha => ih i (consF_forall (fun ψ => ψ.eval i) ha h)
  | impE d e ihd ihe => exact ihd i h (ihe i h)
  | orI₁ d ih => exact .inl (ih i h)
  | orI₂ d ih => exact .inr (ih i h)
  | orE d e₁ e₂ ihd ih₁ ih₂ =>
    rcases ihd i h with ha | hb
    · exact ih₁ i (consF_forall (fun ψ => ψ.eval i) ha h)
    · exact ih₂ i (consF_forall (fun ψ => ψ.eval i) hb h)
  | allI d ih => exact fun x => ih ⟨i, x⟩ h
  | allE t d ih => exact ih i h (t i)
  | exI t d ih => exact ⟨t i, ih i h⟩
  | exE d e ihd ihe =>
    obtain ⟨x, hx⟩ := ihd i h
    exact ihe ⟨i, x⟩ (consF_forall (fun ψ => ψ.eval (Sigma.mk i x)) hx h)
  | ac d ih =>
    choose f hf using ih i h
    exact ⟨f, hf⟩
  | ip p hL d ih =>
    by_cases hp : ∀ k, p ⟨i, k⟩
    · obtain ⟨l, hl⟩ := ih i h hp
      exact ⟨l, fun _ => hl⟩
    · exact ⟨Classical.choice (hL i), fun hp' => absurd hp' hp⟩
  | markov p q d ih =>
    by_cases hq : q i
    · exact ⟨0, fun _ => hq⟩
    · have : ¬ ∀ k, p ⟨i, k⟩ := fun hp => hq (ih i h hp)
      push Not at this
      obtain ⟨k, hk⟩ := this
      exact ⟨{k}, fun hk' => absurd (hk' k (Multiset.mem_singleton_self k)) hk⟩
  | hom f N hN hev d ih => exact hev i (ih i h)
  | atom₂ hs d e ihd ihe => exact hs i (ihd i h) (ihe i h)

/-- **Soundness.** A derivation gives a morphism of the fibre from the context to the conclusion:
the forward map is the realizer, the backward map the demand on the hypotheses. -/
def realize : {I : Type u} → {n : ℕ} → {Γ : Fin n → Form I} → {φ : Form I} → Deriv Γ φ →
    (ctx Γ).Hom φ.dn
  | _, _, Γ, .(Γ k), .hyp k =>
    { fwd := fun _ w => w k
      back := fun _ _ c => {⟨k, c⟩}
      sound := fun _ _ c h => h ⟨k, c⟩ (Multiset.mem_singleton_self _) }
  | _, _, _, _, .topI =>
    { fwd := fun _ _ => PUnit.unit
      back := fun _ _ _ => 0
      sound := fun _ _ _ _ => trivial }
  | _, _, _, _, .andI d e =>
    { fwd := fun i w => (d.realize.fwd i w, e.realize.fwd i w)
      back := fun i w c => Sum.elim (d.realize.back i w) (e.realize.back i w) c
      sound := fun i w c h => by
        cases c with
        | inl c => exact d.realize.sound i w c h
        | inr c => exact e.realize.sound i w c h }
  | _, _, _, _, .andE₁ d =>
    { fwd := fun i w => (d.realize.fwd i w).1
      back := fun i w c => d.realize.back i w (.inl c)
      sound := fun i w c h => d.realize.sound i w (.inl c) h }
  | _, _, _, _, .andE₂ d =>
    { fwd := fun i w => (d.realize.fwd i w).2
      back := fun i w c => d.realize.back i w (.inr c)
      sound := fun i w c h => d.realize.sound i w (.inr c) h }
  | _, _, _, _, .impI d =>
    { fwd := fun i w => ⟨fun a => d.realize.fwd i (consW i a w),
        fun a c => (d.realize.back i (consW i a w) c).filterMap headC?⟩
      back := fun i w c => (d.realize.back i (consW i c.1 w) c.2).filterMap tailC?
      sound := fun i w c hw ha => d.realize.sound i _ c.2 fun y hy =>
        ctx_cons_mat y (fun x hx => ha x ((Multiset.mem_filterMap _ _).2 ⟨y, hy, hx⟩))
          (fun x hx => hw x ((Multiset.mem_filterMap _ _).2 ⟨y, hy, hx⟩)) }
  | _, _, _, _, .impE d e =>
    { fwd := fun i w => (d.realize.fwd i w).1 (e.realize.fwd i w)
      back := fun i w c => d.realize.back i w ⟨e.realize.fwd i w, c⟩ +
        ((d.realize.fwd i w).2 (e.realize.fwd i w) c).bind (e.realize.back i w)
      sound := fun i w c h => d.realize.sound i w ⟨e.realize.fwd i w, c⟩
        (fun x hx => h x (Multiset.mem_add.2 (.inl hx)))
        (fun x hx => e.realize.sound i w x fun y hy =>
          h y (Multiset.mem_add.2 (.inr (Multiset.mem_bind.2 ⟨x, hx, hy⟩)))) }
  | _, _, _, _, .orI₁ d =>
    { fwd := fun i w => .inl (d.realize.fwd i w)
      back := fun i w c => d.realize.back i w c
      sound := fun i w c h => d.realize.sound i w c h }
  | _, _, _, _, .orI₂ d =>
    { fwd := fun i w => .inr (d.realize.fwd i w)
      back := fun i w c => d.realize.back i w c
      sound := fun i w c h => d.realize.sound i w c h }
  | _, _, _, _, .orE d e₁ e₂ =>
    { fwd := fun i w => orCaseFwd e₁.realize e₂.realize i w (d.realize.fwd i w)
      back := fun i w c => orCaseBack e₁.realize e₂.realize i w _ (d.realize.back i w) c
      sound := fun i w c h => orCase_sound e₁.realize e₂.realize i w _ _ (d.realize.sound i w)
        c h }
  | _, _, _, _, .allI d =>
    { fwd := fun i w x => d.realize.fwd ⟨i, x⟩ w
      back := fun i w c => d.realize.back ⟨i, c.1⟩ w c.2
      sound := fun i w c h => d.realize.sound ⟨i, c.1⟩ w c.2 h }
  | _, _, _, _, .allE t d =>
    { fwd := fun i w => d.realize.fwd i w (t i)
      back := fun i w c => d.realize.back i w ⟨t i, c⟩
      sound := fun i w c h => d.realize.sound i w ⟨t i, c⟩ h }
  | _, _, _, _, .exI t d =>
    { fwd := fun i w => ⟨t i, d.realize.fwd i w⟩
      back := fun i w c => d.realize.back i w c
      sound := fun i w c h => d.realize.sound i w c h }
  | _, _, _, _, .exE (Γ := Γ) d e =>
    { fwd := fun i w => e.realize.fwd ⟨i, (d.realize.fwd i w).1⟩
        (consW _ (d.realize.fwd i w).2 w)
      back := fun i w c =>
        ((e.realize.back ⟨i, (d.realize.fwd i w).1⟩ (consW _ (d.realize.fwd i w).2 w) c).filterMap
            tailC?).map (ctxSubC Γ i _ w) +
          ((e.realize.back ⟨i, (d.realize.fwd i w).1⟩
            (consW _ (d.realize.fwd i w).2 w) c).filterMap headC?).bind (d.realize.back i w)
      sound := fun i w c h => e.realize.sound ⟨i, (d.realize.fwd i w).1⟩
        (consW _ (d.realize.fwd i w).2 w) c fun y hy =>
        ctx_cons_mat y
          (fun a ha => d.realize.sound i w a fun z hz => h z (Multiset.mem_add.2 (.inr
            (Multiset.mem_bind.2 ⟨a, (Multiset.mem_filterMap _ _).2 ⟨y, hy, ha⟩, hz⟩))))
          (fun x hx => h x (Multiset.mem_add.2 (.inl
            (Multiset.mem_map_of_mem _ ((Multiset.mem_filterMap _ _).2 ⟨y, hy, hx⟩))))) }
  | _, _, _, _, .ac (φ := φ) d => Hom.comp d.realize (DPred.choice φ.dn).hom
  | _, _, _, _, .ip p (ψ := ψ) _ d => Hom.comp d.realize (DPred.ip p ψ.dn)
  | _, _, _, _, .markov p q d => Hom.comp d.realize (DPred.markovDN p q)
  | _, _, _, _, .hom f _ _ _ d => Hom.comp d.realize f
  | _, _, _, _, .atom₂ h d e =>
    { fwd := fun _ _ => PUnit.unit
      back := fun i w _ => d.realize.back i w PUnit.unit + e.realize.back i w PUnit.unit
      sound := fun i w _ hw => h i
        (d.realize.sound i w PUnit.unit fun x hx => hw x (Multiset.mem_add.2 (.inl hx)))
        (e.realize.sound i w PUnit.unit fun x hx => hw x (Multiset.mem_add.2 (.inr hx))) }

/-- The use counts and the demand of a derivation, under an annotation `δ` of the context by
demands (`none`: `⊤` on every hypothesis), a transport `T` of demands along realized axioms and
a choice `S` of premise demands. The first component counts the uses of each hypothesis: one at
a leaf, the maximum at `∧`-introduction, and at a cut the bound of the implication on its
premise times the uses in the derivation of the premise. The second is the demand of the
conclusion, read off hereditarily: the declared demand at a hypothesis, the premise demand
`S.sel φ` and the uses of the premise at `→`-introduction, which declares that premise demand
on its new hypothesis, the components at the eliminations, `T` at a realized axiom, and `⊤`
where the rule determines none (`∨`-elimination, choice, independence of premise). At `∃`- and
`∨`-elimination the eliminated component receives the demand of the eliminated formula. -/
def uses : {I : Type u} → {n : ℕ} → {Γ : Fin n → Form I} → {φ : Form I} → Deriv Γ φ →
    (δ : Option (∀ k, (Γ k).Dem) := none) → (T : HomDem.{u} := HomDem.top) →
    (S : PremDem.{u} := PremDem.free) → (Fin n → ℕ∞) × φ.Dem
  | _, _, Γ, .(Γ k), .hyp k, δ, _, _ =>
    (fun j => if j = k then 1 else 0, δ.elim (Γ k).demTop (· k))
  | _, _, _, _, .topI, _, _, _ => (fun _ => 0, ())
  | _, _, _, _, .andI d e, δ, T, S =>
    (fun j => max ((d.uses δ T S).1 j) ((e.uses δ T S).1 j),
      ((d.uses δ T S).2, (e.uses δ T S).2))
  | _, _, _, _, .andE₁ d, δ, T, S => ((d.uses δ T S).1, (d.uses δ T S).2.1)
  | _, _, _, _, .andE₂ d, δ, T, S => ((d.uses δ T S).1, (d.uses δ T S).2.2)
  | _, _, _, _, .impI (φ := φ) d, δ, T, S =>
    (fun j => (d.uses (δ.map (consD ((S.sel φ).getD φ.demTop))) T S).1 j.succ,
      (S.sel φ, (d.uses (δ.map (consD ((S.sel φ).getD φ.demTop))) T S).1 0,
        (d.uses (δ.map (consD ((S.sel φ).getD φ.demTop))) T S).2))
  | _, _, _, _, .impE d e, δ, T, S =>
    (fun j => (d.uses δ T S).1 j + (d.uses δ T S).2.2.1 * (e.uses δ T S).1 j,
      (d.uses δ T S).2.2.2)
  | _, _, _, _, .orI₁ (ψ := ψ) d, δ, T, S => ((d.uses δ T S).1, ((d.uses δ T S).2, ψ.demTop))
  | _, _, _, _, .orI₂ (φ := φ) d, δ, T, S => ((d.uses δ T S).1, (φ.demTop, (d.uses δ T S).2))
  | _, _, _, _, .orE (χ := χ) d e₁ e₂, δ, T, S =>
    (fun j => max
      ((e₁.uses (δ.map (consD (d.uses δ T S).2.1)) T S).1 j.succ +
        (e₁.uses (δ.map (consD (d.uses δ T S).2.1)) T S).1 0 * (d.uses δ T S).1 j)
      ((e₂.uses (δ.map (consD (d.uses δ T S).2.2)) T S).1 j.succ +
        (e₂.uses (δ.map (consD (d.uses δ T S).2.2)) T S).1 0 * (d.uses δ T S).1 j), χ.demTop)
  | _, _, _, _, .allI d, δ, T, S => ((d.uses δ T S).1, (d.uses δ T S).2)
  | _, _, _, _, .allE _ d, δ, T, S => ((d.uses δ T S).1, (d.uses δ T S).2)
  | _, _, _, _, .exI _ d, δ, T, S => ((d.uses δ T S).1, (d.uses δ T S).2)
  | _, _, _, _, .exE d e, δ, T, S =>
    (fun j => (e.uses (δ.map (consD (d.uses δ T S).2)) T S).1 j.succ +
      (e.uses (δ.map (consD (d.uses δ T S).2)) T S).1 0 * (d.uses δ T S).1 j,
      (e.uses (δ.map (consD (d.uses δ T S).2)) T S).2)
  | _, _, _, _, .ac d, δ, T, S => ((d.uses δ T S).1, Form.demTop _)
  | _, _, _, _, .ip _ _ d, δ, T, S => ((d.uses δ T S).1, Form.demTop _)
  | _, _, _, _, .markov _ _ d, δ, T, S => ((d.uses δ T S).1, ())
  | _, _, _, _, .hom f N _ _ d, δ, T, S =>
    (fun j => (N : ℕ∞) * (d.uses δ T S).1 j, T.map f (d.uses δ T S).2)
  | _, _, _, _, .atom₂ _ d e, δ, T, S =>
    (fun j => (d.uses δ T S).1 j + (e.uses δ T S).1 j, ())

/-- The side conditions under which the counts of `Deriv.uses` bound the realizer
(`Deriv.bounds_resp`): at a cut, the demand of the argument is counter-free and below the
premise demand of the function (`Form.demLE`); at `∨`- and `∃`-elimination, choice,
independence of premise, Markov's principle and a realized axiom, whose rules pass
counter-witnesses that no demand restricts, the demands of the premises involved are
counter-free. -/
def Coherent : {I : Type u} → {n : ℕ} → {Γ : Fin n → Form I} → {φ : Form I} → Deriv Γ φ →
    Option (∀ k, (Γ k).Dem) → HomDem.{u} → PremDem.{u} → Prop
  | _, _, Γ, .(Γ k), .hyp k, _, _, _ => True
  | _, _, _, _, .topI, _, _, _ => True
  | _, _, _, _, .andI d e, δ, T, S => d.Coherent δ T S ∧ e.Coherent δ T S
  | _, _, _, _, .andE₁ d, δ, T, S => d.Coherent δ T S
  | _, _, _, _, .andE₂ d, δ, T, S => d.Coherent δ T S
  | _, _, _, _, .impI (φ := φ) d, δ, T, S =>
    d.Coherent (δ.map (consD ((S.sel φ).getD φ.demTop))) T S
  | _, _, _, _, .impE (φ := φ) d e, δ, T, S => d.Coherent δ T S ∧ e.Coherent δ T S ∧
      φ.cfree (e.uses δ T S).2 = true ∧
      ∀ P, (d.uses δ T S).2.1 = some P → φ.demLE (e.uses δ T S).2 P = true
  | _, _, _, _, .orI₁ d, δ, T, S => d.Coherent δ T S
  | _, _, _, _, .orI₂ d, δ, T, S => d.Coherent δ T S
  | _, _, _, _, .orE (φ := φ) (ψ := ψ) (χ := χ) d e₁ e₂, δ, T, S => d.Coherent δ T S ∧
      e₁.Coherent (δ.map (consD (d.uses δ T S).2.1)) T S ∧
      e₂.Coherent (δ.map (consD (d.uses δ T S).2.2)) T S ∧
      (Form.or φ ψ).cfree (d.uses δ T S).2 = true ∧
      χ.cfree (e₁.uses (δ.map (consD (d.uses δ T S).2.1)) T S).2 = true ∧
      χ.cfree (e₂.uses (δ.map (consD (d.uses δ T S).2.2)) T S).2 = true
  | _, _, _, _, .allI d, δ, T, S => d.Coherent δ T S
  | _, _, _, _, .allE _ d, δ, T, S => d.Coherent δ T S
  | _, _, _, _, .exI _ d, δ, T, S => d.Coherent δ T S
  | _, _, _, _, .exE (φ := φ) d e, δ, T, S => d.Coherent δ T S ∧
      e.Coherent (δ.map (consD (d.uses δ T S).2)) T S ∧
      (Form.ex φ).cfree (d.uses δ T S).2 = true
  | _, _, _, _, .ac d, δ, T, S => d.Coherent δ T S ∧ Form.cfree _ (d.uses δ T S).2 = true
  | _, _, _, _, .ip _ _ d, δ, T, S => d.Coherent δ T S ∧ Form.cfree _ (d.uses δ T S).2 = true
  | _, _, _, _, .markov _ _ d, δ, T, S =>
    d.Coherent δ T S ∧ Form.cfree _ (d.uses δ T S).2 = true
  | _, _, _, _, .hom (φ := φ) _ _ _ _ d, δ, T, S =>
    d.Coherent δ T S ∧ φ.cfree (d.uses δ T S).2 = true
  | _, _, _, _, .atom₂ _ d e, δ, T, S => d.Coherent δ T S ∧ e.Coherent δ T S

/-- The number of uses of hypothesis `k` in a derivation. -/
def useCount {Γ : Fin n → Form I} {φ : Form I} (d : Deriv Γ φ) (k : Fin n) : ℕ∞ := d.uses.1 k

/-- The number of uses of the premise by a derivation of an implication. -/
def argUses {Γ : Fin n → Form I} {φ : Form I} (d : Deriv Γ φ) : ℕ∞ := φ.demArg d.uses.2

end Deriv

/-- For a morphism into an implication, the bound `b` on the multiset of counter-witnesses of
the premise that its witnesses demand; true for other conclusions. -/
def ArgBound {Γ : Fin n → Form I} : {χ : Form I} → (ctx Γ).Hom χ.dn → ℕ∞ → Prop
  | .imp _ _, f, b => ∀ i w a c, ((((f.fwd i w).2 a c).card : ℕ) : ℕ∞) ≤ b
  | _, _, _ => True

/-- A morphism whose witnesses respect the counter-free demand `D` satisfies the bound
`demArg D`. -/
theorem argBound_of_resp {Γ : Fin n → Form I} {χ : Form I} (f : (ctx Γ).Hom χ.dn) (D : χ.Dem)
    (hD : χ.cfree D = true) (h : ∀ i w, χ.Resp D i (f.fwd i w)) : ArgBound f (χ.demArg D) := by
  cases χ with
  | imp φ ψ =>
    simp only [Form.cfree, Bool.and_eq_true, Option.isNone_iff_eq_none] at hD
    refine fun i w a c => (h i w a fun P hP => ?_).1 c (Form.cresp_of_cfree ψ _ hD.2 i _ c)
    rw [hD.1] at hP
    cases hP
  | _ => trivial

/-- Every morphism satisfies the bound `⊤`. -/
theorem argBound_top {Γ : Fin n → Form I} {χ : Form I} (f : (ctx Γ).Hom χ.dn) :
    ArgBound f ⊤ := by
  cases χ <;> simp [ArgBound]

/-- A counter-witness kept by `filterMap` is counted where its preimage is. -/
theorem countP_filterMap_le {α β : Type*} (f : α → Option β) (p : β → Prop) (q : α → Prop)
    [DecidablePred p] [DecidablePred q] (hf : ∀ y x, f y = some x → p x → q y)
    (m : Multiset α) : (m.filterMap f).countP p ≤ m.countP q := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons y m ih =>
    cases h : f y with
    | none =>
      rw [Multiset.filterMap_cons_none _ _ h]
      grind [Multiset.countP_cons]
    | some x =>
      rw [Multiset.filterMap_cons_some _ _ _ h]
      grind [Multiset.countP_cons]

/-- The size of a `filterMap` is at most the count of the preimages of its elements. -/
theorem card_filterMap_le {α β : Type*} (f : α → Option β) (q : α → Prop) [DecidablePred q]
    (hf : ∀ y x, f y = some x → q y) (m : Multiset α) : (m.filterMap f).card ≤ m.countP q := by
  simpa using countP_filterMap_le f (fun _ => True) q (fun y x hx _ => hf y x hx) m

/-- The count in a bind is at most the size of the outer multiset times a bound on the inner
counts. -/
theorem countP_bind_le {α β : Type*} (m : Multiset α) (f : α → Multiset β) (p : β → Prop)
    [DecidablePred p] (b : ℕ∞) (h : ∀ x ∈ m, (((f x).countP p : ℕ) : ℕ∞) ≤ b) :
    (((m.bind f).countP p : ℕ) : ℕ∞) ≤ m.card * b := by
  induction m using Multiset.induction_on with
  | empty => simp
  | cons y m ih =>
    simp only [Multiset.cons_bind, Multiset.countP_add, Multiset.card_cons, Nat.cast_add,
      Nat.cast_one, add_mul, one_mul]
    rw [add_comm]
    exact add_le_add (ih fun x hx => h x (Multiset.mem_cons_of_mem hx))
      (h y (Multiset.mem_cons_self y m))

/-- The demand of a case analysis on hypothesis `k`, from bounds on the branch selected by the
witness `x` of the disjunction: in that branch, its uses of `k` plus its uses of the disjunct
times the bound `b` on the demand of the disjunction. -/
theorem orCaseBack_countP_le_of {φ ψ χ : Form I} {Γ : Fin n → Form I}
    (E₁ : (ctx (consF φ Γ)).Hom χ.dn) (E₂ : (ctx (consF ψ Γ)).Hom χ.dn)
    (u₁ u₂ : Fin (n + 1) → ℕ∞) (k : Fin n) (i : I) (w : (ctx Γ).W i)
    (x : (DPred.or φ.dn ψ.dn).W i)
    (h₁ : ∀ a, x = .inl a → ∀ k c,
      (((E₁.back i (consW i a w) c).countP fun x => x.1 = k : ℕ) : ℕ∞) ≤ u₁ k)
    (h₂ : ∀ a, x = .inr a → ∀ k c,
      (((E₂.back i (consW i a w) c).countP fun x => x.1 = k : ℕ) : ℕ∞) ≤ u₂ k)
    (g : (DPred.or φ.dn ψ.dn).C i x → Multiset ((ctx Γ).C i w)) (b : ℕ∞)
    (hg : ∀ c, (((g c).countP fun y => y.1 = k : ℕ) : ℕ∞) ≤ b)
    (c : χ.dn.C i (orCaseFwd E₁ E₂ i w x)) :
    (((orCaseBack E₁ E₂ i w x g c).countP fun y => y.1 = k : ℕ) : ℕ∞) ≤
      max (u₁ k.succ + u₁ 0 * b) (u₂ k.succ + u₂ 0 * b) := by
  cases x with
  | inl a =>
    refine le_max_of_le_left ?_
    simp only [orCaseBack, Multiset.countP_add, Nat.cast_add]
    exact add_le_add (le_trans (Nat.cast_le.2 (countP_filterMap_le
        (m := E₁.back i (consW i a w) c) _ _ (fun y => y.1 = k.succ)
        (fun y x hx hp => by rw [tailC?_fst y x hx, hp]))) (h₁ a rfl k.succ c))
      ((countP_bind_le _ _ _ _ fun x _ => hg x).trans (mul_le_mul_of_nonneg_right
        (le_trans (Nat.cast_le.2 (card_filterMap_le _ _ (fun y x hx => headC?_fst y x hx) _))
          (h₁ a rfl 0 c)) (by simp)))
  | inr b' =>
    refine le_max_of_le_right ?_
    simp only [orCaseBack, Multiset.countP_add, Nat.cast_add]
    exact add_le_add (le_trans (Nat.cast_le.2 (countP_filterMap_le
        (m := E₂.back i (consW i b' w) c) _ _ (fun y => y.1 = k.succ)
        (fun y x hx hp => by rw [tailC?_fst y x hx, hp]))) (h₂ b' rfl k.succ c))
      ((countP_bind_le _ _ _ _ fun x _ => hg x).trans (mul_le_mul_of_nonneg_right
        (le_trans (Nat.cast_le.2 (card_filterMap_le _ _ (fun y x hx => headC?_fst y x hx) _))
          (h₂ b' rfl 0 c)) (by simp)))

/-- The demand of a case analysis on hypothesis `k`: in the selected branch, its uses of `k`
plus its uses of the disjunct times the bound `b` on the demand of the disjunction. -/
theorem orCaseBack_countP_le {φ ψ χ : Form I} {Γ : Fin n → Form I}
    (E₁ : (ctx (consF φ Γ)).Hom χ.dn) (E₂ : (ctx (consF ψ Γ)).Hom χ.dn)
    (u₁ u₂ : Fin (n + 1) → ℕ∞)
    (h₁ : ∀ k i w c, (((E₁.back i w c).countP fun x => x.1 = k : ℕ) : ℕ∞) ≤ u₁ k)
    (h₂ : ∀ k i w c, (((E₂.back i w c).countP fun x => x.1 = k : ℕ) : ℕ∞) ≤ u₂ k)
    (k : Fin n) (i : I) (w : (ctx Γ).W i) (x : (DPred.or φ.dn ψ.dn).W i)
    (g : (DPred.or φ.dn ψ.dn).C i x → Multiset ((ctx Γ).C i w)) (b : ℕ∞)
    (hg : ∀ c, (((g c).countP fun y => y.1 = k : ℕ) : ℕ∞) ≤ b)
    (c : χ.dn.C i (orCaseFwd E₁ E₂ i w x)) :
    (((orCaseBack E₁ E₂ i w x g c).countP fun y => y.1 = k : ℕ) : ℕ∞) ≤
      max (u₁ k.succ + u₁ 0 * b) (u₂ k.succ + u₂ 0 * b) :=
  orCaseBack_countP_le_of E₁ E₂ u₁ u₂ k i w x (fun _ _ k c => h₁ k i _ c)
    (fun _ _ k c => h₂ k i _ c) g b hg c

namespace Deriv

/-- **Hereditary demand bounds.** For a coherent derivation (`Deriv.Coherent`) and a witness `w`
of the context respecting the annotation `δ`, the realizer demands at most `(d.uses δ T S).1 k`
counter-witnesses of hypothesis `k` for each counter-witness of the conclusion respecting the
demand `(d.uses δ T S).2`, and its witness of the conclusion respects that demand. -/
theorem bounds_resp {Γ : Fin n → Form I} {φ : Form I} (d : Deriv Γ φ) (T : HomDem.{u})
    (S : PremDem.{u}) :
    ∀ (δ : Option (∀ k, (Γ k).Dem)) (i : I) (w : (ctx Γ).W i), d.Coherent δ T S →
      ctxResp Γ δ i w →
      (∀ k c, φ.CResp (d.uses δ T S).2 i (d.realize.fwd i w) c →
        (((d.realize.back i w c).countP fun x => x.1 = k : ℕ) : ℕ∞) ≤ (d.uses δ T S).1 k) ∧
        φ.Resp (d.uses δ T S).2 i (d.realize.fwd i w) := by
  induction d with
  | hyp j =>
    intro δ i w _ hw
    refine ⟨fun k c _ => ?_, ?_⟩
    · simp only [realize, uses]
      by_cases h : k = j
      · subst h
        simp only [↓reduceIte]
        exact_mod_cast (Multiset.countP_le_card _ _).trans (Multiset.card_singleton _).le
      · simp only [h, ↓reduceIte, nonpos_iff_eq_zero, Nat.cast_eq_zero, Multiset.countP_eq_zero]
        intro x hx
        rw [Multiset.mem_singleton.1 hx]
        exact fun e => h e.symm
    · cases δ with
      | none => exact Form.resp_demTop _ i _
      | some δ => exact hw j
  | topI => exact fun δ i w _ _ => ⟨fun k c _ => by simp [realize, uses], trivial⟩
  | andI d e ihd ihe =>
    intro δ i w hc hw
    obtain ⟨hd₁, hd₂⟩ := ihd δ i w hc.1 hw
    obtain ⟨he₁, he₂⟩ := ihe δ i w hc.2 hw
    refine ⟨fun k c hc' => ?_, ⟨hd₂, he₂⟩⟩
    cases c with
    | inl c => exact (hd₁ k c hc').trans (le_max_left _ _)
    | inr c => exact (he₁ k c hc').trans (le_max_right _ _)
  | andE₁ d ih =>
    exact fun δ i w hc hw =>
      ⟨fun k c hc' => (ih δ i w hc hw).1 k _ hc', (ih δ i w hc hw).2.1⟩
  | andE₂ d ih =>
    exact fun δ i w hc hw =>
      ⟨fun k c hc' => (ih δ i w hc hw).1 k _ hc', (ih δ i w hc hw).2.2⟩
  | @impI _ _ Γ φ ψ d ih =>
    intro δ i w hc hw
    have hget : ∀ a, (∀ P, S.sel φ = some P → φ.Resp P i a) →
        φ.Resp ((S.sel φ).getD φ.demTop) i a := by
      intro a ha
      cases hS : S.sel φ with
      | none => exact Form.resp_demTop _ i a
      | some P => exact ha P hS
    have h := fun a ha => ih _ i _ hc (ctxResp_cons hw _ (hget a ha))
    refine ⟨fun k c hc' => ?_, fun a ha => ⟨fun c hc' => ?_, (h a ha).2⟩⟩
    · exact le_trans (Nat.cast_le.2 (countP_filterMap_le
        (m := d.realize.back i (consW i c.1 w) c.2) _ _ (fun y => y.1 = k.succ)
        (fun y x hx hp => by rw [tailC?_fst y x hx, hp]))) ((h c.1 hc'.1).1 k.succ c.2 hc'.2)
    · refine le_trans (Nat.cast_le.2 ?_) ((h a ha).1 0 c hc')
      exact card_filterMap_le _ _ (fun y x hx => headC?_fst y x hx) _
  | @impE _ _ Γ φ ψ d e ihd ihe =>
    intro δ i w hc hw
    obtain ⟨hcd, hce, hcf, hle⟩ := hc
    obtain ⟨hd₁, hd₂⟩ := ihd δ i w hcd hw
    obtain ⟨he₁, he₂⟩ := ihe δ i w hce hw
    have ha : ∀ P, (d.uses δ T S).2.1 = some P → φ.Resp P i (e.realize.fwd i w) :=
      fun P hP => (Form.demLE_sound φ _ _ (hle P hP) i _).1 he₂
    obtain ⟨hcard, hψ⟩ := hd₂ _ ha
    refine ⟨fun k c hc' => ?_, hψ⟩
    simp only [realize, uses, Multiset.countP_add, Nat.cast_add]
    exact add_le_add (hd₁ k _ ⟨ha, hc'⟩) ((countP_bind_le _ _ _ _ fun x _ =>
      he₁ k x (Form.cresp_of_cfree φ _ hcf i _ x)).trans
      (mul_le_mul_of_nonneg_right (hcard c hc') (by simp)))
  | orI₁ d ih =>
    exact fun δ i w hc hw => ⟨fun k c hc' => (ih δ i w hc hw).1 k _ hc', (ih δ i w hc hw).2⟩
  | orI₂ d ih =>
    exact fun δ i w hc hw => ⟨fun k c hc' => (ih δ i w hc hw).1 k _ hc', (ih δ i w hc hw).2⟩
  | orE d e₁ e₂ ihd ih₁ ih₂ =>
    intro δ i w hc hw
    obtain ⟨hcd, hc₁, hc₂, hfd, hf₁, hf₂⟩ := hc
    obtain ⟨hd₁, hd₂⟩ := ihd δ i w hcd hw
    refine ⟨fun k c _ => orCaseBack_countP_le_of _ _ _ _ k i w _ (fun a hx => ?_)
      (fun a hx => ?_) _ _ (fun c' => hd₁ k c' (Form.cresp_of_cfree _ _ hfd i _ c')) c,
      Form.resp_demTop _ i _⟩
    · rw [hx] at hd₂
      exact fun k c => (ih₁ _ i _ hc₁ (ctxResp_cons hw _ hd₂)).1 k c
        (Form.cresp_of_cfree _ _ hf₁ _ _ c)
    · rw [hx] at hd₂
      exact fun k c => (ih₂ _ i _ hc₂ (ctxResp_cons hw _ hd₂)).1 k c
        (Form.cresp_of_cfree _ _ hf₂ _ _ c)
  | allI d ih =>
    intro δ i w hc hw
    have h := fun x => ih δ ⟨i, x⟩ w hc (by cases δ <;> exact hw)
    exact ⟨fun k c hc' => (h c.1).1 k c.2 hc', fun x => (h x).2⟩
  | allE t d ih =>
    exact fun δ i w hc hw =>
      ⟨fun k c hc' => (ih δ i w hc hw).1 k _ hc', (ih δ i w hc hw).2 (t i)⟩
  | exI t d ih =>
    exact fun δ i w hc hw => ⟨fun k c hc' => (ih δ i w hc hw).1 k _ hc', (ih δ i w hc hw).2⟩
  | @exE _ _ Γ K _ φ _ d e ihd ihe =>
    intro δ i w hc hw
    obtain ⟨hcd, hce, hfd⟩ := hc
    obtain ⟨hd₁, hd₂⟩ := ihd δ i w hcd hw
    have hw' : ctxResp (fun k => (Γ k).sub (Sigma.fst : (Σ i, K i) → _)) δ
        ⟨i, (d.realize.fwd i w).1⟩ w := by
      cases δ <;> exact hw
    have he := ihe _ ⟨i, (d.realize.fwd i w).1⟩ (consW _ (d.realize.fwd i w).2 w) hce
      (ctxResp_cons (φ := φ) hw' _ hd₂)
    refine ⟨fun k c hc' => ?_, he.2⟩
    simp only [realize, uses, Multiset.countP_add, Nat.cast_add, Multiset.countP_map,
      ← Multiset.countP_eq_card_filter]
    refine add_le_add (le_trans (Nat.cast_le.2 (countP_filterMap_le
        (m := e.realize.back ⟨i, (d.realize.fwd i w).1⟩ (consW _ (d.realize.fwd i w).2 w) c)
        _ _ (fun y => y.1 = k.succ)
        (fun y x hx hp => by rw [tailC?_fst y x hx]; exact congrArg Fin.succ hp) ))
        (he.1 k.succ c hc')) ?_
    refine (countP_bind_le _ _ _ _ fun x _ =>
      hd₁ k x (Form.cresp_of_cfree _ _ hfd i _ x)).trans
      (mul_le_mul_of_nonneg_right ?_ (by simp))
    refine le_trans (Nat.cast_le.2 ?_) (he.1 0 c hc')
    exact card_filterMap_le _ _ (fun y x hx => headC?_fst y x hx) _
  | ac d ih =>
    intro δ i w hc hw
    refine ⟨fun k c _ => ?_, Form.resp_demTop _ i _⟩
    change ((Multiset.countP _ (({_} : Multiset _).bind (d.realize.back i w)) : ℕ) : ℕ∞) ≤ _
    exact (congrArg (fun m => ((Multiset.countP (fun x => x.1 = k) m : ℕ) : ℕ∞))
      (Multiset.singleton_bind _ (d.realize.back i w))).trans_le
      ((ih δ i w hc.1 hw).1 k _ (Form.cresp_of_cfree _ _ hc.2 i _ _))
  | ip p hL d ih =>
    intro δ i w hc hw
    refine ⟨fun k c _ => ?_, Form.resp_demTop _ i _⟩
    change ((Multiset.countP _ (({_} : Multiset _).bind (d.realize.back i w)) : ℕ) : ℕ∞) ≤ _
    exact (congrArg (fun m => ((Multiset.countP (fun x => x.1 = k) m : ℕ) : ℕ∞))
      (Multiset.singleton_bind _ (d.realize.back i w))).trans_le
      ((ih δ i w hc.1 hw).1 k _ (Form.cresp_of_cfree _ _ hc.2 i _ _))
  | markov p q d ih =>
    intro δ i w hc hw
    refine ⟨fun k c _ => ?_, trivial⟩
    change ((Multiset.countP _ (({_} : Multiset _).bind (d.realize.back i w)) : ℕ) : ℕ∞) ≤ _
    exact (congrArg (fun m => ((Multiset.countP (fun x => x.1 = k) m : ℕ) : ℕ∞))
      (Multiset.singleton_bind _ (d.realize.back i w))).trans_le
      ((ih δ i w hc.1 hw).1 k _ (Form.cresp_of_cfree _ _ hc.2 i _ _))
  | hom f N hN hev d ih =>
    intro δ i w hc hw
    refine ⟨fun k c _ => ?_, T.sound f _ i _ (ih δ i w hc.1 hw).2⟩
    exact (countP_bind_le _ _ _ _ fun x _ =>
      (ih δ i w hc.1 hw).1 k x (Form.cresp_of_cfree _ _ hc.2 i _ x)).trans
      (mul_le_mul_of_nonneg_right (by exact_mod_cast hN i _ c) (by simp))
  | atom₂ h d e ihd ihe =>
    intro δ i w hc hw
    refine ⟨fun k c _ => ?_, trivial⟩
    simp only [realize, uses, Multiset.countP_add, Nat.cast_add]
    exact add_le_add ((ihd δ i w hc.1 hw).1 k _ trivial) ((ihe δ i w hc.2 hw).1 k _ trivial)

/-- An annotation of the context is counter-free when every declared demand is (`none`: the
demand `⊤` on every hypothesis). -/
def ctxCfree (Γ : Fin n → Form I) : Option (∀ k, (Γ k).Dem) → Prop
  | none => True
  | some δ => ∀ k, (Γ k).cfree (δ k) = true

/-- The extension of a counter-free annotation by a counter-free demand is counter-free. -/
theorem ctxCfree_cons {φ : Form I} {Γ : Fin n → Form I} {δ : Option (∀ k, (Γ k).Dem)}
    (hδ : ctxCfree Γ δ) {D : φ.Dem} (hD : φ.cfree D = true) :
    ctxCfree (consF φ Γ) (δ.map (consD D)) := by
  cases δ with
  | none => trivial
  | some δ =>
    intro k
    match k with
    | ⟨0, _⟩ => exact hD
    | ⟨j + 1, h⟩ => exact hδ ⟨j, Nat.lt_of_succ_lt_succ h⟩

/-- Under a counter-free annotation, a transport of demands with counter-free targets and no
premise demands, the demand of a derivation is counter-free. -/
theorem cfree_uses_of {Γ : Fin n → Form I} {φ : Form I} (d : Deriv Γ φ) (T : HomDem.{u})
    (hT : ∀ {J : Type u} {φ ψ : Form J} (f : φ.dn.Hom ψ.dn) (D : φ.Dem),
      ψ.cfree (T.map f D) = true) :
    ∀ δ, ctxCfree Γ δ → φ.cfree (d.uses δ T PremDem.free).2 = true := by
  induction d with
  | hyp j =>
    intro δ hδ
    cases δ with
    | none => exact Form.cfree_demTop _
    | some δ => exact hδ j
  | topI => exact fun _ _ => rfl
  | andI d e ihd ihe =>
    intro δ hδ
    simp only [uses, Form.cfree, ihd δ hδ, ihe δ hδ, Bool.and_self]
  | andE₁ d ih =>
    intro δ hδ
    have h := ih δ hδ
    simp only [Form.cfree, Bool.and_eq_true] at h
    exact h.1
  | andE₂ d ih =>
    intro δ hδ
    have h := ih δ hδ
    simp only [Form.cfree, Bool.and_eq_true] at h
    exact h.2
  | @impI _ _ Γ φ ψ d ih =>
    intro δ hδ
    simp only [uses, Form.cfree, Bool.and_eq_true]
    exact ⟨rfl, ih _ (ctxCfree_cons hδ (Form.cfree_demTop φ))⟩
  | impE d e ihd ihe =>
    intro δ hδ
    have h := ihd δ hδ
    simp only [Form.cfree, Bool.and_eq_true] at h
    exact h.2
  | orI₁ d ih =>
    intro δ hδ
    simp only [uses, Form.cfree, ih δ hδ, Form.cfree_demTop, Bool.and_self]
  | orI₂ d ih =>
    intro δ hδ
    simp only [uses, Form.cfree, ih δ hδ, Form.cfree_demTop, Bool.and_self]
  | orE d e₁ e₂ ihd ih₁ ih₂ => exact fun _ _ => Form.cfree_demTop _
  | allI d ih =>
    intro δ hδ
    exact ih δ (by cases δ <;> exact hδ)
  | allE t d ih => exact fun δ hδ => ih δ hδ
  | exI t d ih => exact fun δ hδ => ih δ hδ
  | @exE _ _ Γ K _ φ _ d e ihd ihe =>
    intro δ hδ
    have hδ' : ctxCfree (fun k => (Γ k).sub (Sigma.fst : (Σ i, K i) → _)) δ := by
      cases δ <;> exact hδ
    exact ihe _ (ctxCfree_cons (φ := φ) hδ' (ihd δ hδ))
  | ac d ih => exact fun _ _ => Form.cfree_demTop _
  | ip p hL d ih => exact fun _ _ => Form.cfree_demTop _
  | markov p q d ih => exact fun _ _ => rfl
  | hom f N hN hev d ih => exact fun _ _ => hT f _
  | atom₂ h d e ihd ihe => exact fun _ _ => rfl

/-- Under the default annotation, transport and choice of premise demands, the demand of a
derivation is counter-free. -/
theorem cfree_uses_free {Γ : Fin n → Form I} {φ : Form I} (d : Deriv Γ φ) :
    φ.cfree (d.uses none HomDem.top PremDem.free).2 = true :=
  cfree_uses_of d HomDem.top (fun {_ _ ψ} _ _ => Form.cfree_demTop ψ) none trivial

/-- Every derivation is coherent under a counter-free annotation, a transport of demands with
counter-free targets and no premise demands. -/
theorem coherent_of {Γ : Fin n → Form I} {φ : Form I} (d : Deriv Γ φ) (T : HomDem.{u})
    (hT : ∀ {J : Type u} {φ ψ : Form J} (f : φ.dn.Hom ψ.dn) (D : φ.Dem),
      ψ.cfree (T.map f D) = true) :
    ∀ δ, ctxCfree Γ δ → d.Coherent δ T PremDem.free := by
  induction d with
  | hyp j => exact fun _ _ => trivial
  | topI => exact fun _ _ => trivial
  | andI d e ihd ihe => exact fun δ hδ => ⟨ihd δ hδ, ihe δ hδ⟩
  | andE₁ d ih => exact fun δ hδ => ih δ hδ
  | andE₂ d ih => exact fun δ hδ => ih δ hδ
  | @impI _ _ Γ φ ψ d ih =>
    exact fun δ hδ => ih _ (ctxCfree_cons hδ (Form.cfree_demTop φ))
  | impE d e ihd ihe =>
    intro δ hδ
    have h := cfree_uses_of d T hT δ hδ
    simp only [Form.cfree, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
    refine ⟨ihd δ hδ, ihe δ hδ, cfree_uses_of e T hT δ hδ, fun P hP => ?_⟩
    rw [h.1] at hP
    cases hP
  | orI₁ d ih => exact fun δ hδ => ih δ hδ
  | orI₂ d ih => exact fun δ hδ => ih δ hδ
  | orE d e₁ e₂ ihd ih₁ ih₂ =>
    intro δ hδ
    have hd := cfree_uses_of d T hT δ hδ
    have hd' := hd
    simp only [Form.cfree, Bool.and_eq_true] at hd'
    have h₁ := ctxCfree_cons hδ hd'.1
    have h₂ := ctxCfree_cons hδ hd'.2
    exact ⟨ihd δ hδ, ih₁ _ h₁, ih₂ _ h₂, hd, cfree_uses_of e₁ T hT _ h₁,
      cfree_uses_of e₂ T hT _ h₂⟩
  | allI d ih =>
    intro δ hδ
    exact ih δ (by cases δ <;> exact hδ)
  | allE t d ih => exact fun δ hδ => ih δ hδ
  | exI t d ih => exact fun δ hδ => ih δ hδ
  | @exE _ _ Γ K _ φ _ d e ihd ihe =>
    intro δ hδ
    have hδ' : ctxCfree (fun k => (Γ k).sub (Sigma.fst : (Σ i, K i) → _)) δ := by
      cases δ <;> exact hδ
    have hd := cfree_uses_of d T hT δ hδ
    exact ⟨ihd δ hδ, ihe _ (ctxCfree_cons (φ := φ) hδ' hd), hd⟩
  | ac d ih => exact fun δ hδ => ⟨ih δ hδ, cfree_uses_of d T hT δ hδ⟩
  | ip p hL d ih => exact fun δ hδ => ⟨ih δ hδ, cfree_uses_of d T hT δ hδ⟩
  | markov p q d ih => exact fun δ hδ => ⟨ih δ hδ, cfree_uses_of d T hT δ hδ⟩
  | hom f N hN hev d ih => exact fun δ hδ => ⟨ih δ hδ, cfree_uses_of d T hT δ hδ⟩
  | atom₂ h d e ihd ihe => exact fun δ hδ => ⟨ihd δ hδ, ihe δ hδ⟩

/-- Every derivation is coherent under the default annotation, transport and choice of premise
demands. -/
theorem coherent_free {Γ : Fin n → Form I} {φ : Form I} (d : Deriv Γ φ) :
    d.Coherent none HomDem.top PremDem.free :=
  coherent_of d HomDem.top (fun {_ _ ψ} _ _ => Form.cfree_demTop ψ) none trivial

/-- **Hereditary demand bounds without premise demands.** For a counter-free annotation `δ`, a
transport `T` with counter-free targets and a witness `w` of the context respecting `δ`, the
realizer demands at most `(d.uses δ T).1 k` counter-witnesses of hypothesis `k` for every
counter-witness of the conclusion, and its witness of the conclusion respects `(d.uses δ T).2`. -/
theorem bounds_resp_cfree {Γ : Fin n → Form I} {φ : Form I} (d : Deriv Γ φ) (T : HomDem.{u})
    (hT : ∀ {J : Type u} {φ ψ : Form J} (f : φ.dn.Hom ψ.dn) (D : φ.Dem),
      ψ.cfree (T.map f D) = true) :
    ∀ (δ : Option (∀ k, (Γ k).Dem)) (i : I) (w : (ctx Γ).W i), ctxCfree Γ δ →
      ctxResp Γ δ i w →
      (∀ k c, (((d.realize.back i w c).countP fun x => x.1 = k : ℕ) : ℕ∞) ≤ (d.uses δ T).1 k) ∧
        φ.Resp (d.uses δ T).2 i (d.realize.fwd i w) := fun δ i w hδ hw =>
  ⟨fun k c => (d.bounds_resp T PremDem.free δ i w (coherent_of d T hT δ hδ) hw).1 k c
      (Form.cresp_of_cfree _ _ (cfree_uses_of d T hT δ hδ) i _ c),
    (d.bounds_resp T PremDem.free δ i w (coherent_of d T hT δ hδ) hw).2⟩

/-- The demand bounds of a derivation: on each hypothesis by its use count, and on the premise
of an implication by `argUses`. -/
theorem bounds {Γ : Fin n → Form I} {φ : Form I} (d : Deriv Γ φ) :
    (∀ k i w c, (((d.realize.back i w c).countP fun x => x.1 = k : ℕ) : ℕ∞) ≤ d.useCount k) ∧
      ArgBound d.realize d.argUses :=
  ⟨fun k i w c => (d.bounds_resp HomDem.top PremDem.free none i w (coherent_free d) trivial).1
      k c (Form.cresp_of_cfree _ _ (cfree_uses_free d) i _ c),
    argBound_of_resp _ _ (cfree_uses_free d) fun i w =>
      (d.bounds_resp HomDem.top PremDem.free none i w (coherent_free d) trivial).2⟩

/-- **Quantitative soundness.** The realizer of a derivation demands at most `useCount d k`
counter-witnesses of hypothesis `k`. -/
theorem card_back_le {Γ : Fin n → Form I} {φ : Form I} (d : Deriv Γ φ) (k : Fin n) (i : I)
    (w : (ctx Γ).W i) (c : φ.dn.C i (d.realize.fwd i w)) :
    (((d.realize.back i w c).countP fun x => x.1 = k : ℕ) : ℕ∞) ≤ d.useCount k :=
  d.bounds.1 k i w c

/-- **Soundness for the Dialectica meaning.** -/
theorem holds_dn {Γ : Fin n → Form I} {φ : Form I} (d : Deriv Γ φ) (i : I)
    (h : ∀ k, (Γ k).dn.holds i) : φ.dn.holds i :=
  d.realize.holds i ((holds_ctx Γ i).2 h)

/-! ## Programs from an oracle hypothesis -/

section Oracle

variable {X : I → Type u} {Y : (Σ i, X i) → Type u} {a : (Σ x : Σ i, X i, Y x) → Prop}
  {X' : I → Type u} {Z : (Σ i, X' i) → Type u} {r : (Σ x : Σ i, X' i, Z x) → Prop}
  {sX : ∀ i, X i → ℕ} {sY : ∀ x, Y x → ℕ} {sX' : ∀ i, X' i → ℕ} {sZ : ∀ x, Z x → ℕ}

/-- The formula `∀ x, ∃ y, a (x, y)`, with the sizes `sX` and `sY` of its quantifiers. -/
abbrev allEx (sX : ∀ i, X i → ℕ) (sY : ∀ x, Y x → ℕ) (a : (Σ x : Σ i, X i, Y x) → Prop) : Form I :=
  .all (K := X) (sz := sX) (.ex (K := Y) (sz := sY) (.atom a))

/-- The hypothesis of the oracle programs of this section. -/
local notation "𝒜" => allEx sX sY a
/-- The conclusion of the oracle programs of this section. -/
local notation "ℛ" => allEx sX' sZ r

/-- The witness of the hypothesis `∀ x, ∃ y, a (x, y)` given by an oracle `g`. -/
def oracleW (a : (Σ x : Σ i, X i, Y x) → Prop) (g : ∀ i (x : X i), Y ⟨i, x⟩) (i : I) :
    (ctx fun _ : Fin 1 => allEx sX sY a).W i :=
  fun _ x => ⟨g i x, PUnit.unit⟩

/-- The program of a derivation of `∀ x', ∃ z, r (x', z)` from `∀ x, ∃ y, a (x, y)`: the answer
at `x'` computed with the oracle `g`. -/
def program (d : Deriv (fun _ : Fin 1 => 𝒜) ℛ) (g : ∀ i (x : X i), Y ⟨i, x⟩)
    (i : I) (x' : X' i) : Z ⟨i, x'⟩ :=
  (d.realize.fwd i (oracleW a g i) x').1

/-- The arguments at which the program of a derivation consults the oracle to answer `x'`. -/
def queries (d : Deriv (fun _ : Fin 1 => 𝒜) ℛ) (g : ∀ i (x : X i), Y ⟨i, x⟩)
    (i : I) (x' : X' i) : Multiset (X i) :=
  (d.realize.back i (oracleW a g i) ⟨x', PUnit.unit⟩).map fun c => c.2.1

/-- **Query bound.** The program of a derivation consults the oracle at most `useCount d 0`
times. -/
theorem queries_card_le (d : Deriv (fun _ : Fin 1 => 𝒜) ℛ)
    (g : ∀ i (x : X i), Y ⟨i, x⟩) (i : I) (x' : X' i) :
    (((d.queries g i x').card : ℕ) : ℕ∞) ≤ d.useCount 0 := by
  refine le_trans (le_of_eq ?_) (d.card_back_le 0 i (oracleW a g i) ⟨x', PUnit.unit⟩)
  rw [queries, Multiset.card_map, Multiset.countP_eq_card.2 fun x _ => Subsingleton.elim _ _]

/-- **Correctness from the queries.** The answer of the program at `x'` satisfies `r` whenever
the oracle satisfies `a` at the queries. -/
theorem query_sound (d : Deriv (fun _ : Fin 1 => 𝒜) ℛ)
    (g : ∀ i (x : X i), Y ⟨i, x⟩) (i : I) (x' : X' i)
    (h : ∀ x ∈ d.queries g i x', a ⟨⟨i, x⟩, g i x⟩) :
    r ⟨⟨i, x'⟩, d.program g i x'⟩ :=
  d.realize.sound i (oracleW a g i) ⟨x', PUnit.unit⟩ fun y hy =>
    h y.2.1 (Multiset.mem_map_of_mem _ hy)

/-- The price of the queries of the program at `x'`, under a price `t` of an oracle call. -/
def queryPrice (d : Deriv (fun _ : Fin 1 => 𝒜) ℛ) (g : ∀ i (x : X i), Y ⟨i, x⟩)
    (t : ∀ i, X i → ℕ) (i : I) (x' : X' i) : ℕ :=
  ((d.queries g i x').map (t i)).sum

/-- **Price bound.** When each oracle call costs at most `T`, the queries of the program cost at
most `useCount d 0 * T`: the time of the program is its own time plus this price. -/
theorem queryPrice_le (d : Deriv (fun _ : Fin 1 => 𝒜) ℛ)
    (g : ∀ i (x : X i), Y ⟨i, x⟩) (t : ∀ i, X i → ℕ) (T : ℕ) (ht : ∀ i x, t i x ≤ T) (i : I)
    (x' : X' i) : ((d.queryPrice g t i x' : ℕ) : ℕ∞) ≤ d.useCount 0 * T := by
  have hs : d.queryPrice g t i x' ≤ (d.queries g i x').card * T := by
    rw [queryPrice]
    generalize d.queries g i x' = m
    induction m using Multiset.induction_on with
    | empty => simp
    | cons x m ih =>
      simp only [Multiset.map_cons, Multiset.sum_cons, Multiset.card_cons, add_mul, one_mul]
      have := ht i x
      omega
  calc ((d.queryPrice g t i x' : ℕ) : ℕ∞) ≤ (((d.queries g i x').card : ℕ) : ℕ∞) * T := by
        exact_mod_cast hs
    _ ≤ d.useCount 0 * T := mul_le_mul_of_nonneg_right (d.queries_card_le g i x') (by simp)

end Oracle

end Deriv

/-! ## Use counts of realized axioms, choice and `∃`-elimination

A realized axiom `Deriv.hom f N` multiplies the uses of its premise by the bound `N` on the
counter-witnesses that `f` demands; a finite conjunction over `N` instances is one such axiom.
The equations below compute use counts of derivations built from hypotheses, choice,
`∃`-elimination and realized axioms. -/

namespace Deriv

section UseCountEquations

variable {Γ : Fin n → Form I}

/-- Unfolding equation of `useCount` at a hypothesis: it is used once. -/
@[simp] theorem useCount_hyp (k j : Fin n) :
    (hyp (Γ := Γ) k).useCount j = if j = k then 1 else 0 := rfl

/-- Unfolding equation of `useCount` at a realized axiom: the uses of its premise times its
demand bound. -/
@[simp] theorem useCount_hom {φ ψ : Form I} (f : φ.dn.Hom ψ.dn) (N : ℕ)
    (hN : ∀ i w c, (f.back i w c).card ≤ N) (hev : ∀ i, φ.eval i → ψ.eval i) (d : Deriv Γ φ)
    (k : Fin n) : (hom f N hN hev d).useCount k = N * d.useCount k := rfl

/-- Unfolding equation of `useCount` at the axiom of choice: the use counts of its premise. -/
@[simp] theorem useCount_ac {K : I → Type u} {L : (Σ i, K i) → Type u}
    {sK : ∀ i, K i → ℕ} {sL : ∀ x, L x → ℕ} {sF : ∀ i, (∀ k : K i, L ⟨i, k⟩) → ℕ}
    {φ : Form (Σ x : Σ i, K i, L x)} (d : Deriv Γ (.all (sz := sK) (.ex (sz := sL) φ)))
    (k : Fin n) : (ac (sF := sF) d).useCount k = d.useCount k := rfl

/-- Unfolding equation of `useCount` at `∃`-elimination: the uses in the body, plus the uses of
the eliminated witness times its uses in the derivation of the existential. -/
@[simp] theorem useCount_exE {K : I → Type u} {s : ∀ i, K i → ℕ} {φ : Form (Σ i, K i)}
    {ψ : Form I} (d : Deriv Γ (.ex (sz := s) φ))
    (e : Deriv (consF φ fun k => (Γ k).sub Sigma.fst) (ψ.sub Sigma.fst))
    (k : Fin n) : (exE d e).useCount k = e.useCount k.succ + e.useCount 0 * d.useCount k := rfl

end UseCountEquations

end Deriv

/-! ## Conversion between formulas of equal meaning, and atoms from two atoms

A formula and its substitution pushed through the connectives have the same Diller–Nahm
meaning; `Deriv.conv` passes between them along the identity of that meaning, as a realized
axiom demanding one counter-witness, so that a hypothesis reindexed by `∀`- or
`∃`-introduction can be eliminated. `Deriv.atom₂` concludes an atom from two atoms, demanding
one counter-witness of each: its use counts are the sums of those of its premises. -/

/-- The morphism of the fibre along an equality of Dialectica predicates. -/
def homOfEq {P Q : DPred I} (h : P = Q) : P.Hom Q := h ▸ Hom.id P

/-- The morphism along an equality demands at most one counter-witness. -/
theorem homOfEq_back_card {P Q : DPred I} (h : P = Q) (i : I) (w : P.W i)
    (c : Q.C i ((homOfEq h).fwd i w)) : ((homOfEq h).back i w c).card ≤ 1 := by
  subst h
  exact (Multiset.card_singleton _).le

namespace Deriv

section Conv

variable {Γ : Fin n → Form I}

/-- Conversion to a formula of the same Diller–Nahm meaning and weaker truth value; both side
conditions hold by `rfl` when the two formulas are definitionally equal after unfolding the
interpretations. -/
def conv {φ ψ : Form I} (d : Deriv Γ φ) (h : φ.dn = ψ.dn := by rfl)
    (hev : ∀ i, φ.eval i → ψ.eval i := by exact fun _ h => h) : Deriv Γ ψ :=
  hom (homOfEq h) 1 (homOfEq_back_card h) hev d

/-- Conversion keeps the use counts. -/
@[simp] theorem useCount_conv {φ ψ : Form I} (d : Deriv Γ φ) (h : φ.dn = ψ.dn)
    (hev : ∀ i, φ.eval i → ψ.eval i) (k : Fin n) :
    (conv d h hev).useCount k = d.useCount k := by
  simp [conv]

/-- The transport of demands that keeps the demand of the source along every morphism that
carries it: when the source and target have the same type of demands and the morphism sends
witnesses respecting the demand to witnesses respecting it, and `⊤` otherwise. -/
noncomputable def _root_.CatCrypt.Container.DNLogic.HomDem.keep : HomDem.{u} where
  map {_ φ ψ} f D :=
    @dite _ (∃ e : φ.Dem = ψ.Dem, ∀ i w, φ.Resp D i w → ψ.Resp (cast e D) i (f.fwd i w))
      (Classical.propDecidable _) (fun h => cast h.choose D) fun _ => ψ.demTop
  sound {_ φ ψ} f D i w hw := by
    split
    · next h => exact h.choose_spec i w hw
    · exact Form.resp_demTop ψ i _

/-- `HomDem.keep` keeps the demand along a morphism that carries it. -/
theorem _root_.CatCrypt.Container.DNLogic.HomDem.keep_map {φ ψ : Form I} (f : φ.dn.Hom ψ.dn)
    (D : φ.Dem) (e : φ.Dem = ψ.Dem)
    (h : ∀ i w, φ.Resp D i w → ψ.Resp (cast e D) i (f.fwd i w)) :
    HomDem.keep.map f D = cast e D := by
  change @dite _ _ (Classical.propDecidable _) _ _ = _
  exact dite_eq_left ⟨e, h⟩

/-- Under the transport `HomDem.keep`, the demand of a conversion is the demand of the converted
derivation, when the conversion carries it. -/
theorem uses_conv_keep {φ ψ : Form I} (d : Deriv Γ φ) (h : φ.dn = ψ.dn)
    (hev : ∀ i, φ.eval i → ψ.eval i) (δ : Option (∀ k, (Γ k).Dem)) (e : φ.Dem = ψ.Dem)
    (hR : ∀ D i w, φ.Resp D i w → ψ.Resp (cast e D) i ((homOfEq h).fwd i w)) :
    ((conv d h hev).uses δ HomDem.keep).2 = cast e (d.uses δ HomDem.keep).2 :=
  HomDem.keep_map _ _ e (hR _)

variable {K : I → Type u} {sz : ∀ i, K i → ℕ}

/-- The hypothesis `∀ x, ¬ X x` of the translated `∃`-introduction, at the size `sz`. -/
local notation:max "∀¬ " X:max => Form.all (sz := sz) (Form.not X)

/-- The cut of the negative translation of an `∃`-introduction at the term `t`: the hypothesis
`∀ x, ¬ X x`, instantiated at `t` and converted to `¬ X t`, applied to a derivation `e` of
`X t`. -/
def exICut (X : Form (Σ i, K i)) (t : ∀ i, K i) {Δ : Fin n → Form I}
    (e : Deriv (consF (∀¬ X) Δ) (X.sub fun i => ⟨i, t i⟩)) :
    Deriv (consF (∀¬ X) Δ) Form.bot :=
  .impE (conv (ψ := Form.not (X.sub fun i => (⟨i, t i⟩ : Σ i, K i)))
    (.allE t (.hyp ⟨0, Nat.succ_pos _⟩))) e

/-- **Use counts of the cut of an `∃`-introduction.** When the hypothesis `∀ x, ¬ X x` is
declared to demand at most `N` counter-witnesses of `X x`, the cut uses hypothesis `k` as often
as the instantiation does plus `N` times the uses of `k` by `e`, under any choice `S` of premise
demands. -/
theorem uses_exICut_sel (X : Form (Σ i, K i)) (t : ∀ i, K i) {Δ : Fin n → Form I}
    (e : Deriv (consF (∀¬ X) Δ) (X.sub fun i => ⟨i, t i⟩)) (N : ℕ∞)
    (δ : ∀ k, (Δ k).Dem) (S : PremDem.{u}) (k : Fin (n + 1)) :
    ((exICut X t e).uses (some (consD ((none, N, ()) : (∀¬ X).Dem) δ))
        HomDem.keep S).1 k =
      1 * (if k = 0 then 1 else 0) +
        N * (e.uses (some (consD ((none, N, ()) : (∀¬ X).Dem) δ))
          HomDem.keep S).1 k := by
  have hm := HomDem.keep_map
    (homOfEq (P := ((Form.not X).sub fun i => (⟨i, t i⟩ : Σ i, K i)).dn)
      (Q := (Form.not (X.sub fun i => (⟨i, t i⟩ : Σ i, K i))).dn) rfl)
    ((none, N, ()) : (Form.not X).Dem) rfl (fun _ _ hw => hw)
  simp only [exICut, conv, uses]
  erw [hm]
  rfl

/-- **Use counts of the cut of an `∃`-introduction**, with no premise demands: `uses_exICut_sel`
at `PremDem.free`. -/
theorem uses_exICut (X : Form (Σ i, K i)) (t : ∀ i, K i) {Δ : Fin n → Form I}
    (e : Deriv (consF (∀¬ X) Δ) (X.sub fun i => ⟨i, t i⟩)) (N : ℕ∞)
    (δ : ∀ k, (Δ k).Dem) (k : Fin (n + 1)) :
    ((exICut X t e).uses (some (consD ((none, N, ()) : (∀¬ X).Dem) δ))
        HomDem.keep).1 k =
      1 * (if k = 0 then 1 else 0) +
        N * (e.uses (some (consD ((none, N, ()) : (∀¬ X).Dem) δ))
          HomDem.keep).1 k :=
  uses_exICut_sel X t e N δ PremDem.free k

/-- The cut of an `∃`-introduction has finite use counts when the declared demand `N` and the use
counts of `e` are finite, under any choice `S` of premise demands. -/
theorem uses_exICut_lt_top_sel (X : Form (Σ i, K i)) (t : ∀ i, K i)
    {Δ : Fin n → Form I}
    (e : Deriv (consF (∀¬ X) Δ) (X.sub fun i => ⟨i, t i⟩)) (N : ℕ∞)
    (δ : ∀ k, (Δ k).Dem) (S : PremDem.{u}) (k : Fin (n + 1)) (hN : N < ⊤)
    (he : (e.uses (some (consD ((none, N, ()) : (∀¬ X).Dem) δ))
      HomDem.keep S).1 k < ⊤) :
    ((exICut X t e).uses (some (consD ((none, N, ()) : (∀¬ X).Dem) δ))
        HomDem.keep S).1 k < ⊤ := by
  rw [uses_exICut_sel]
  refine ENat.add_lt_top.2 ⟨?_, WithTop.mul_lt_top hN he⟩
  split_ifs <;> simp

/-- The cut of an `∃`-introduction has finite use counts when the declared demand `N` and the use
counts of `e` are finite, with no premise demands. -/
theorem uses_exICut_lt_top (X : Form (Σ i, K i)) (t : ∀ i, K i)
    {Δ : Fin n → Form I}
    (e : Deriv (consF (∀¬ X) Δ) (X.sub fun i => ⟨i, t i⟩)) (N : ℕ∞)
    (δ : ∀ k, (Δ k).Dem) (k : Fin (n + 1)) (hN : N < ⊤)
    (he : (e.uses (some (consD ((none, N, ()) : (∀¬ X).Dem) δ))
      HomDem.keep).1 k < ⊤) :
    ((exICut X t e).uses (some (consD ((none, N, ()) : (∀¬ X).Dem) δ))
        HomDem.keep).1 k < ⊤ :=
  uses_exICut_lt_top_sel X t e N δ PremDem.free k hN he

/-- **The translated `∃`-introduction has finite use counts.** When the choice `S` declares the
premise demand `N` (with no demand on `X`) on the premise `∀ x, ¬ X x` of the `→`-introduction
around the cut of an `∃`-introduction, `N` and the use counts of `e` are finite, the
`→`-introduction uses each hypothesis finitely often and its premise finitely often. -/
theorem uses_impI_exICut_lt_top (X : Form (Σ i, K i)) (t : ∀ i, K i)
    {Δ : Fin n → Form I}
    (e : Deriv (consF (∀¬ X) Δ) (X.sub fun i => ⟨i, t i⟩)) (N : ℕ∞)
    (δ : ∀ k, (Δ k).Dem) (S : PremDem.{u})
    (hS : S.sel (∀¬ X) = some ((none, N, ()) : (∀¬ X).Dem))
    (hN : N < ⊤)
    (he : ∀ k, (e.uses (some (consD ((none, N, ()) : (∀¬ X).Dem) δ))
      HomDem.keep S).1 k < ⊤) :
    (∀ k, ((impI (exICut (sz := sz) X t e)).uses (some δ) HomDem.keep S).1 k < ⊤) ∧
      ((impI (exICut (sz := sz) X t e)).uses (some δ) HomDem.keep S).2.2.1 < ⊤ := by
  have hδ : (some δ).map (consD ((S.sel (∀¬ X)).getD
      (∀¬ X).demTop)) =
      some (consD (φ := ∀¬ X) (none, N, ()) δ) := by
    rw [hS]
    rfl
  simp only [uses]
  rw [hδ]
  exact ⟨fun k => uses_exICut_lt_top_sel X t e N δ S k.succ hN (he _),
    uses_exICut_lt_top_sel X t e N δ S 0 hN (he _)⟩

/-- The `→`-introduction around the cut of an `∃`-introduction is coherent under the choice `S`
of the premise demand `N` when `e` is coherent and its demand is counter-free. -/
theorem coherent_impI_exICut (X : Form (Σ i, K i)) (t : ∀ i, K i)
    {Δ : Fin n → Form I}
    (e : Deriv (consF (∀¬ X) Δ) (X.sub fun i => ⟨i, t i⟩)) (N : ℕ∞)
    (δ : ∀ k, (Δ k).Dem) (S : PremDem.{u})
    (hS : S.sel (∀¬ X) = some ((none, N, ()) : (∀¬ X).Dem))
    (he : e.Coherent (some (consD ((none, N, ()) : (∀¬ X).Dem) δ))
      HomDem.keep S)
    (hf : (X.sub fun i => (⟨i, t i⟩ : Σ i, K i)).cfree
      (e.uses (some (consD ((none, N, ()) : (∀¬ X).Dem) δ))
        HomDem.keep S).2 = true) :
    (impI (exICut (sz := sz) X t e)).Coherent (some δ) HomDem.keep S := by
  have hm := HomDem.keep_map
    (homOfEq (P := ((Form.not X).sub fun i => (⟨i, t i⟩ : Σ i, K i)).dn)
      (Q := (Form.not (X.sub fun i => (⟨i, t i⟩ : Σ i, K i))).dn) rfl)
    ((none, N, ()) : (Form.not X).Dem) rfl (fun _ _ hw => hw)
  have hδ : (some δ).map (consD ((S.sel (∀¬ X)).getD
      (∀¬ X).demTop)) =
      some (consD (φ := ∀¬ X) (none, N, ()) δ) := by
    rw [hS]
    rfl
  simp only [Coherent]
  rw [hδ]
  refine ⟨⟨trivial, rfl⟩, he, hf, fun P hP => ?_⟩
  simp only [conv, uses] at hP
  erw [hm] at hP
  cases hP

/-- An atom from two atoms uses each hypothesis as often as both premises together (the
unfolding equation of `useCount` at `atom₂`). -/
@[simp] theorem useCount_atom₂ {p q s : I → Prop} (h : ∀ i, p i → q i → s i)
    (d : Deriv Γ (.atom p)) (e : Deriv Γ (.atom q)) (k : Fin n) :
    (atom₂ h d e).useCount k = d.useCount k + e.useCount k := rfl

end Conv

/-! ## Disjunction and falsity

`∨`-introduction keeps the use counts; `∨`-elimination uses hypothesis `j` as often as the
branch that uses it more, with the uses of the disjunct in that branch multiplied by the uses
of `j` in the derivation of the disjunction. Ex falso is a realized axiom demanding the one
counter-witness of falsity; its forward map needs a witness `w₀` of the conclusion, which
`Form.notW` gives for a negation and `PUnit.unit` for an atom. -/

section Disj

variable {Γ : Fin n → Form I}

/-- The morphism of ex falso: the witness `w₀` of `φ`, demanding the counter-witness of
falsity. -/
def efqHom (φ : Form I) (w₀ : ∀ i, φ.dn.W i) : (Form.bot : Form I).dn.Hom φ.dn where
  fwd i _ := w₀ i
  back _ _ _ := {PUnit.unit}
  sound _ _ _ h := (h PUnit.unit (Multiset.mem_singleton_self _)).elim

/-- **Ex falso quodlibet**, for a conclusion `φ` with a witness `w₀` of its Diller–Nahm
meaning. -/
def efq {φ : Form I} (w₀ : ∀ i, φ.dn.W i) (d : Deriv Γ .bot) : Deriv Γ φ :=
  hom (efqHom φ w₀) 1 (fun _ _ _ => (Multiset.card_singleton _).le) (fun _ h => h.elim) d

/-- Ex falso keeps the use counts. -/
@[simp] theorem useCount_efq {φ : Form I} (w₀ : ∀ i, φ.dn.W i) (d : Deriv Γ .bot)
    (k : Fin n) : (efq w₀ d).useCount k = d.useCount k := by
  change ((1 : ℕ) : ℕ∞) * d.useCount k = d.useCount k
  rw [Nat.cast_one, one_mul]

/-- Unfolding equation of `useCount` at `∨`-introduction, left. -/
@[simp] theorem useCount_orI₁ {φ ψ : Form I} (d : Deriv Γ φ) (k : Fin n) :
    (orI₁ (ψ := ψ) d).useCount k = d.useCount k := rfl

/-- Unfolding equation of `useCount` at `∨`-introduction, right. -/
@[simp] theorem useCount_orI₂ {φ ψ : Form I} (d : Deriv Γ ψ) (k : Fin n) :
    (orI₂ (φ := φ) d).useCount k = d.useCount k := rfl

/-- Unfolding equation of `useCount` at `∨`-elimination: the larger of the two branches, each
counting its uses of `k` plus its uses of the disjunct times the uses of `k` in the derivation
of the disjunction. -/
@[simp] theorem useCount_orE {φ ψ χ : Form I} (d : Deriv Γ (.or φ ψ))
    (e₁ : Deriv (consF φ Γ) χ) (e₂ : Deriv (consF ψ Γ) χ) (k : Fin n) :
    (orE d e₁ e₂).useCount k = max (e₁.useCount k.succ + e₁.useCount 0 * d.useCount k)
      (e₂.useCount k.succ + e₂.useCount 0 * d.useCount k) := rfl

/-- Commutativity of disjunction, as a derivation from the hypothesis `φ ∨ ψ`. -/
def orComm (φ ψ : Form I) : Deriv (fun _ : Fin 1 => Form.or φ ψ) (.or ψ φ) :=
  orE (hyp 0) (orI₂ (hyp (Γ := consF φ fun _ => Form.or φ ψ) 0))
    (orI₁ (hyp (Γ := consF ψ fun _ => Form.or φ ψ) 0))

/-- The commutation of a disjunction uses its hypothesis once. -/
theorem useCount_orComm (φ ψ : Form I) : (orComm φ ψ).useCount 0 = 1 := by
  change max ((0 : ℕ∞) + 1 * 1) (0 + 1 * 1) = 1
  simp

end Disj

end Deriv

end CatCrypt.Container.DNLogic
