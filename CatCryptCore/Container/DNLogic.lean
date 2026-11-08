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
`I → Prop`, `⊤`, `∧`, `→`, the quantifiers `∀`, `∃` over a family of sorts `K : I → Type u`, and
an explicit substitution `Form.sub` along a map of sort contexts. A formula is interpreted twice:
by its truth value `Form.eval`, and by a Dialectica predicate `Form.dn` of the Gödel fibration of
the Diller–Nahm category, through the connectives of `Container/GodelFibration.lean`.

Derivations (`Deriv`) are natural deduction derivations with hypotheses, as data: the rules of
`⊤`, `∧`, `→`, `∀`, `∃`, and the axioms of choice, independence of a universal premise and the
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
* `Deriv.program`, `Deriv.queries`, `Deriv.queryPrice` — the program of a derivation from an
  oracle hypothesis.

## Main results

* `Deriv.eval` — soundness for truth;
* `Deriv.holds_dn` — soundness for the Dialectica meaning;
* `Deriv.card_back_le` — quantitative soundness: the demand on a hypothesis is at most its uses;
* `Deriv.queries_card_le`, `Deriv.query_sound`, `Deriv.queryPrice_le` — the query bound.

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
  /-- Universal quantification over a family of sorts. -/
  | all {I : Type u} {K : I → Type u} (φ : Form (Σ i, K i)) : Form I
  /-- Existential quantification over a family of sorts. -/
  | ex {I : Type u} {K : I → Type u} (φ : Form (Σ i, K i)) : Form I
  /-- Substitution along a map of sort contexts. -/
  | sub {I J : Type u} (h : J → I) (φ : Form I) : Form J

namespace Form

/-- The truth value of a formula at a point of its sort context. -/
def eval : {I : Type u} → Form I → I → Prop
  | _, .atom p, i => p i
  | _, .top, _ => True
  | _, .and φ ψ, i => φ.eval i ∧ ψ.eval i
  | _, .imp φ ψ, i => φ.eval i → ψ.eval i
  | _, .all (K := K) φ, i => ∀ k : K i, φ.eval ⟨i, k⟩
  | _, .ex (K := K) φ, i => ∃ k : K i, φ.eval ⟨i, k⟩
  | _, .sub h φ, j => φ.eval (h j)

/-- The Diller–Nahm interpretation: a Dialectica predicate of the Gödel fibration. -/
def dn : {I : Type u} → Form I → DPred I
  | _, .atom p => DPred.ofProp p
  | _, .top => DPred.top
  | _, .and φ ψ => DPred.and φ.dn ψ.dn
  | _, .imp φ ψ => DPred.imp φ.dn ψ.dn
  | _, .all φ => DPred.pi φ.dn
  | _, .ex φ => DPred.sigma φ.dn
  | _, .sub h φ => φ.dn.reindex h

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

/-- A counter-witness of the context reindexed along `Sigma.fst`, at `⟨i, x⟩`, is a
counter-witness of the context at `i`. -/
def ctxSubC {K : I → Type u} (Γ : Fin n → Form I) (i : I) (x : K i) (w : (ctx Γ).W i)
    (c : (ctx fun k => (Γ k).sub Sigma.fst).C ⟨i, x⟩ w) : (ctx Γ).C i w := c

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
  /-- `∀`-introduction: a derivation over the extended sort context. -/
  | allI {I : Type u} {n : ℕ} {Γ : Fin n → Form I} {K : I → Type u} {φ : Form (Σ i, K i)}
      (d : Deriv (fun k => (Γ k).sub Sigma.fst) φ) : Deriv Γ (.all φ)
  /-- `∀`-elimination at a term `t`. -/
  | allE {I : Type u} {n : ℕ} {Γ : Fin n → Form I} {K : I → Type u} {φ : Form (Σ i, K i)}
      (t : ∀ i, K i) (d : Deriv Γ (.all φ)) : Deriv Γ (φ.sub fun i => ⟨i, t i⟩)
  /-- `∃`-introduction at a term `t`. -/
  | exI {I : Type u} {n : ℕ} {Γ : Fin n → Form I} {K : I → Type u} {φ : Form (Σ i, K i)}
      (t : ∀ i, K i) (d : Deriv Γ (φ.sub fun i => ⟨i, t i⟩)) : Deriv Γ (.ex φ)
  /-- `∃`-elimination: the body becomes the hypothesis at position `0` over the extended sort
  context. -/
  | exE {I : Type u} {n : ℕ} {Γ : Fin n → Form I} {K : I → Type u} {φ : Form (Σ i, K i)}
      {ψ : Form I} (d : Deriv Γ (.ex φ))
      (e : Deriv (consF φ fun k => (Γ k).sub Sigma.fst) (ψ.sub Sigma.fst)) : Deriv Γ ψ
  /-- The axiom of choice: `∀ k ∃ l, φ` gives `∃ f ∀ k, φ (k, f k)`. -/
  | ac {I : Type u} {n : ℕ} {Γ : Fin n → Form I} {K : I → Type u} {L : (Σ i, K i) → Type u}
      {φ : Form (Σ x : Σ i, K i, L x)} (d : Deriv Γ (.all (.ex φ))) :
      Deriv Γ (.ex (K := fun i => ∀ k : K i, L ⟨i, k⟩)
        (.all (K := fun p => K p.1) (φ.sub fun y => ⟨⟨y.1.1, y.2⟩, y.1.2 y.2⟩)))
  /-- Independence of a universal premise, for inhabited sorts of the existential. -/
  | ip {I : Type u} {n : ℕ} {Γ : Fin n → Form I} {K L : I → Type u} (p : (Σ i, K i) → Prop)
      {ψ : Form (Σ i, L i)} (hL : ∀ i, Nonempty (L i))
      (d : Deriv Γ (.imp (.all (.atom p)) (.ex ψ))) :
      Deriv Γ (.ex (.imp ((Form.all (.atom p)).sub Sigma.fst) ψ))
  /-- Markov's principle, Diller–Nahm form: finitely many candidates suffice. -/
  | markov {I : Type u} {n : ℕ} {Γ : Fin n → Form I} {K : I → Type u} (p : (Σ i, K i) → Prop)
      (q : I → Prop) (d : Deriv Γ (.imp (.all (.atom p)) (.atom q))) :
      Deriv Γ (.ex (K := fun i => Multiset (K i))
        (.atom fun x => (∀ k ∈ x.2, p ⟨x.1, k⟩) → q x.1))

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

/-- The use counts of a derivation: the uses of each hypothesis (one at a leaf, the maximum at
`∧`-introduction, and at a cut the product of the uses of the cut formula with the uses in the
derivation of the cut formula), and the uses of the premise by a derivation of an implication
(finite for `→`-introduction, `⊤` otherwise). -/
def uses : {I : Type u} → {n : ℕ} → {Γ : Fin n → Form I} → {φ : Form I} → Deriv Γ φ →
    (Fin n → ℕ∞) × ℕ∞
  | _, _, Γ, .(Γ k), .hyp k => (fun j => if j = k then 1 else 0, ⊤)
  | _, _, _, _, .topI => (fun _ => 0, ⊤)
  | _, _, _, _, .andI d e => (fun j => max (d.uses.1 j) (e.uses.1 j), ⊤)
  | _, _, _, _, .andE₁ d => (d.uses.1, ⊤)
  | _, _, _, _, .andE₂ d => (d.uses.1, ⊤)
  | _, _, _, _, .impI d => (fun j => d.uses.1 j.succ, d.uses.1 0)
  | _, _, _, _, .impE d e => (fun j => d.uses.1 j + d.uses.2 * e.uses.1 j, ⊤)
  | _, _, _, _, .allI d => (d.uses.1, ⊤)
  | _, _, _, _, .allE _ d => (d.uses.1, ⊤)
  | _, _, _, _, .exI _ d => (d.uses.1, ⊤)
  | _, _, _, _, .exE d e => (fun j => e.uses.1 j.succ + e.uses.1 0 * d.uses.1 j, ⊤)
  | _, _, _, _, .ac d => (d.uses.1, ⊤)
  | _, _, _, _, .ip _ _ d => (d.uses.1, ⊤)
  | _, _, _, _, .markov _ _ d => (d.uses.1, ⊤)

/-- The number of uses of hypothesis `k` in a derivation. -/
def useCount {Γ : Fin n → Form I} {φ : Form I} (d : Deriv Γ φ) (k : Fin n) : ℕ∞ := d.uses.1 k

/-- The number of uses of the premise by a derivation of an implication. -/
def argUses {Γ : Fin n → Form I} {φ : Form I} (d : Deriv Γ φ) : ℕ∞ := d.uses.2

end Deriv

/-- For a morphism into an implication, the bound `b` on the multiset of counter-witnesses of
the premise that its witnesses demand; true for other conclusions. -/
def ArgBound {Γ : Fin n → Form I} : {χ : Form I} → (ctx Γ).Hom χ.dn → ℕ∞ → Prop
  | .imp _ _, f, b => ∀ i w a c, ((((f.fwd i w).2 a c).card : ℕ) : ℕ∞) ≤ b
  | _, _, _ => True

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

namespace Deriv

/-- The demand bounds of a derivation: on each hypothesis by its use count, and on the premise
of an implication by `argUses`. -/
theorem bounds {Γ : Fin n → Form I} {φ : Form I} (d : Deriv Γ φ) :
    (∀ k i w c, (((d.realize.back i w c).countP fun x => x.1 = k : ℕ) : ℕ∞) ≤ d.useCount k) ∧
      ArgBound d.realize d.argUses := by
  induction d with
  | hyp j =>
    refine ⟨fun k i w c => ?_, argBound_top _⟩
    simp only [realize, useCount, uses]
    by_cases h : k = j
    · subst h
      simp only [↓reduceIte]
      exact_mod_cast (Multiset.countP_le_card _ _).trans (Multiset.card_singleton _).le
    · simp only [h, ↓reduceIte, nonpos_iff_eq_zero, Nat.cast_eq_zero, Multiset.countP_eq_zero]
      intro x hx
      rw [Multiset.mem_singleton.1 hx]
      exact fun e => h e.symm
  | topI => exact ⟨fun k i w c => by simp [realize, useCount, uses], argBound_top _⟩
  | andI d e ihd ihe =>
    refine ⟨fun k i w c => ?_, argBound_top _⟩
    cases c with
    | inl c => exact (ihd.1 k i w c).trans (le_max_left _ _)
    | inr c => exact (ihe.1 k i w c).trans (le_max_right _ _)
  | andE₁ d ih => exact ⟨fun k i w c => ih.1 k i w _, argBound_top _⟩
  | andE₂ d ih => exact ⟨fun k i w c => ih.1 k i w _, argBound_top _⟩
  | impI d ih =>
    refine ⟨fun k i w c => ?_, fun i w a c => ?_⟩
    · exact le_trans (Nat.cast_le.2 (countP_filterMap_le (m := d.realize.back i (consW i c.1 w) c.2)
        _ _ (fun y => y.1 = k.succ)
        (fun y x hx hp => by rw [tailC?_fst y x hx, hp]))) (ih.1 k.succ i _ c.2)
    · refine le_trans (Nat.cast_le.2 ?_) (ih.1 0 i _ c)
      exact card_filterMap_le _ _ (fun y x hx => headC?_fst y x hx) _
  | impE d e ihd ihe =>
    refine ⟨fun k i w c => ?_, argBound_top _⟩
    simp only [realize, useCount, uses, Multiset.countP_add, Nat.cast_add]
    exact add_le_add (ihd.1 k i w _) ((countP_bind_le _ _ _ _ fun x _ => ihe.1 k i w x).trans
      (mul_le_mul_of_nonneg_right (ihd.2 i w _ c) (by simp)))
  | allI d ih => exact ⟨fun k i w c => ih.1 k ⟨i, c.1⟩ w c.2, argBound_top _⟩
  | allE t d ih => exact ⟨fun k i w c => ih.1 k i w _, argBound_top _⟩
  | exI t d ih => exact ⟨fun k i w c => ih.1 k i w _, argBound_top _⟩
  | exE d e ihd ihe =>
    refine ⟨fun k i w c => ?_, argBound_top _⟩
    simp only [realize, useCount, uses, Multiset.countP_add, Nat.cast_add, Multiset.countP_map,
      ← Multiset.countP_eq_card_filter]
    refine add_le_add (le_trans (Nat.cast_le.2 (countP_filterMap_le
        (m := e.realize.back ⟨i, (d.realize.fwd i w).1⟩ (consW _ (d.realize.fwd i w).2 w) c)
        _ _ (fun y => y.1 = k.succ)
        (fun y x hx hp => by rw [tailC?_fst y x hx]; exact congrArg Fin.succ hp) ))
        (ihe.1 k.succ ⟨i, (d.realize.fwd i w).1⟩ (consW _ (d.realize.fwd i w).2 w) c)) ?_
    refine (countP_bind_le _ _ _ _ fun x _ => ihd.1 k i w x).trans
      (mul_le_mul_of_nonneg_right ?_ (by simp))
    refine le_trans (Nat.cast_le.2 ?_)
      (ihe.1 0 ⟨i, (d.realize.fwd i w).1⟩ (consW _ (d.realize.fwd i w).2 w) c)
    exact card_filterMap_le _ _ (fun y x hx => headC?_fst y x hx) _
  | ac d ih =>
    refine ⟨fun k i w c => ?_, argBound_top _⟩
    change ((Multiset.countP _ (({_} : Multiset _).bind (d.realize.back i w)) : ℕ) : ℕ∞) ≤ _
    exact (congrArg (fun m => ((Multiset.countP (fun x => x.1 = k) m : ℕ) : ℕ∞))
      (Multiset.singleton_bind _ (d.realize.back i w))).trans_le (ih.1 k i w _)
  | ip p hL d ih =>
    refine ⟨fun k i w c => ?_, argBound_top _⟩
    change ((Multiset.countP _ (({_} : Multiset _).bind (d.realize.back i w)) : ℕ) : ℕ∞) ≤ _
    exact (congrArg (fun m => ((Multiset.countP (fun x => x.1 = k) m : ℕ) : ℕ∞))
      (Multiset.singleton_bind _ (d.realize.back i w))).trans_le (ih.1 k i w _)
  | markov p q d ih =>
    refine ⟨fun k i w c => ?_, argBound_top _⟩
    change ((Multiset.countP _ (({_} : Multiset _).bind (d.realize.back i w)) : ℕ) : ℕ∞) ≤ _
    exact (congrArg (fun m => ((Multiset.countP (fun x => x.1 = k) m : ℕ) : ℕ∞))
      (Multiset.singleton_bind _ (d.realize.back i w))).trans_le (ih.1 k i w _)

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

/-- The formula `∀ x, ∃ y, a (x, y)`. -/
abbrev allEx (a : (Σ x : Σ i, X i, Y x) → Prop) : Form I :=
  .all (K := X) (.ex (K := Y) (.atom a))

/-- The witness of the hypothesis `∀ x, ∃ y, a (x, y)` given by an oracle `g`. -/
def oracleW (a : (Σ x : Σ i, X i, Y x) → Prop) (g : ∀ i (x : X i), Y ⟨i, x⟩) (i : I) :
    (ctx fun _ : Fin 1 => allEx a).W i :=
  fun _ x => ⟨g i x, PUnit.unit⟩

/-- The program of a derivation of `∀ x', ∃ z, r (x', z)` from `∀ x, ∃ y, a (x, y)`: the answer
at `x'` computed with the oracle `g`. -/
def program (d : Deriv (fun _ : Fin 1 => allEx a) (allEx r)) (g : ∀ i (x : X i), Y ⟨i, x⟩)
    (i : I) (x' : X' i) : Z ⟨i, x'⟩ :=
  (d.realize.fwd i (oracleW a g i) x').1

/-- The arguments at which the program of a derivation consults the oracle to answer `x'`. -/
def queries (d : Deriv (fun _ : Fin 1 => allEx a) (allEx r)) (g : ∀ i (x : X i), Y ⟨i, x⟩)
    (i : I) (x' : X' i) : Multiset (X i) :=
  (d.realize.back i (oracleW a g i) ⟨x', PUnit.unit⟩).map fun c => c.2.1

/-- **Query bound.** The program of a derivation consults the oracle at most `useCount d 0`
times. -/
theorem queries_card_le (d : Deriv (fun _ : Fin 1 => allEx a) (allEx r))
    (g : ∀ i (x : X i), Y ⟨i, x⟩) (i : I) (x' : X' i) :
    (((d.queries g i x').card : ℕ) : ℕ∞) ≤ d.useCount 0 := by
  refine le_trans (le_of_eq ?_) (d.card_back_le 0 i (oracleW a g i) ⟨x', PUnit.unit⟩)
  rw [queries, Multiset.card_map, Multiset.countP_eq_card.2 fun x _ => Subsingleton.elim _ _]

/-- **Correctness from the queries.** The answer of the program at `x'` satisfies `r` whenever
the oracle satisfies `a` at the queries. -/
theorem query_sound (d : Deriv (fun _ : Fin 1 => allEx a) (allEx r))
    (g : ∀ i (x : X i), Y ⟨i, x⟩) (i : I) (x' : X' i)
    (h : ∀ x ∈ d.queries g i x', a ⟨⟨i, x⟩, g i x⟩) :
    r ⟨⟨i, x'⟩, d.program g i x'⟩ :=
  d.realize.sound i (oracleW a g i) ⟨x', PUnit.unit⟩ fun y hy =>
    h y.2.1 (Multiset.mem_map_of_mem _ hy)

/-- The price of the queries of the program at `x'`, under a price `t` of an oracle call. -/
def queryPrice (d : Deriv (fun _ : Fin 1 => allEx a) (allEx r)) (g : ∀ i (x : X i), Y ⟨i, x⟩)
    (t : ∀ i, X i → ℕ) (i : I) (x' : X' i) : ℕ :=
  ((d.queries g i x').map (t i)).sum

/-- **Price bound.** When each oracle call costs at most `T`, the queries of the program cost at
most `useCount d 0 * T`: the time of the program is its own time plus this price. -/
theorem queryPrice_le (d : Deriv (fun _ : Fin 1 => allEx a) (allEx r))
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

end CatCrypt.Container.DNLogic
