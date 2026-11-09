/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Container.DNLogic

/-!
# Classical logic, the negative translation and Π⁰₂ extraction in the Gödel fibration

`CDeriv` is classical natural deduction over the formulas `Form` of `Container/DNLogic.lean`:
the intuitionistic rules of `Deriv` for `⊤`, `∧`, `→`, `∨`, `∀`, `∃`, reductio ad absurdum
`CDeriv.raa`, renaming of hypotheses along a map of contexts `CDeriv.rename` (which gives
weakening), and a conversion `CDeriv.conv` between formulas whose negative translations have the
same Diller–Nahm meaning (substitution pushed through a connective). Its soundness for truth is
`CDeriv.eval`.

The Gödel–Gentzen negative translation `Form.negT` sends an atom `p` to `¬¬p`, `∨` to
`¬(¬_ ∧ ¬_)`, `∃` to `¬∀¬` and commutes with `⊤`, `∧`, `→`, `∀` and substitution. Falsity is
the atom `False`, so its translation is `¬¬⊥`. Every translated formula is stable: `Deriv.stab`
derives `¬¬φᴺ → φᴺ` in every context, without ex falso or the realized axioms. The translation of
derivations `CDeriv.translate` is a definition by recursion, so the translated derivation is a
`Deriv` with a realizer and use counts. It is the instance at the identity of `CDeriv.toDerivAt`,
which translates into any context that holds the translated hypotheses at positions given by a
map `ρ`; this map gives the weakenings the translation of `∨`- and `∃`-elimination and of
reductio need, so `Deriv` needs no weakening lemma.

For a classical derivation of `∀ x, ∃ y, p (x, y)`, `CDeriv.pi2` composes the translation with
Markov's principle (`Deriv.markov`) and a selection `sel` of a candidate satisfying `p` from a
finite multiset of candidates, giving a `Deriv` of `∀ x, ∃ y, p (x, y)` itself. Its realizer is
the extracted function `CDeriv.extract`, and `CDeriv.extract_spec` states that it satisfies `p`.

## Main definitions

* `CDeriv` — classical derivations;
* `Form.negT` — the negative translation;
* `Deriv.stab` — stability of translated formulas;
* `CDeriv.translate` — the translation of derivations;
* `CDeriv.pi2`, `CDeriv.extract` — the derivation and the function extracted from a classical
  proof of a Π⁰₂ statement.

## Main results

* `CDeriv.eval` — classical soundness for truth;
* `CDeriv.extract_spec`, `CDeriv.extractClosed_spec` — the extracted function satisfies `p`;
* `CDeriv.useCount_pi2` — the extracted derivation uses each hypothesis as often as the
  translated derivation;
* `CDeriv.useCount_translate_dneAtom` — the translation of double negation elimination uses its
  hypothesis once.

## References

* U. Kohlenbach, *Applied Proof Theory: Proof Interpretations and their Use in Mathematics*,
  Springer (2008), chapter 10.
* G. Gentzen, *Die Widerspruchsfreiheit der reinen Zahlentheorie*, Mathematische Annalen 112
  (1936).

Search words: negative translation, double negation translation, Gödel–Gentzen, Markov's
principle, Π⁰₂ conservativity, proof mining, program extraction, Diller–Nahm.
-/

set_option autoImplicit false

@[expose] public section

universe u

namespace CatCrypt.Container.DNLogic

open DPred

namespace Form

/-- The Gödel–Gentzen negative translation. -/
def negT : {I : Type u} → Form I → Form I
  | _, .atom p => Form.not (Form.not (.atom p))
  | _, .top => .top
  | _, .and φ ψ => .and φ.negT ψ.negT
  | _, .imp φ ψ => .imp φ.negT ψ.negT
  | _, .or φ ψ => Form.not (.and (Form.not φ.negT) (Form.not ψ.negT))
  | _, .all φ => .all φ.negT
  | _, .ex φ => Form.not (.all (Form.not φ.negT))
  | _, .sub h φ => .sub h φ.negT

end Form

/-- Classical natural deduction derivations, as data. -/
inductive CDeriv : {I : Type u} → {n : ℕ} → (Fin n → Form I) → Form I → Type (u + 1)
  /-- A hypothesis. -/
  | hyp {I : Type u} {n : ℕ} {Γ : Fin n → Form I} (k : Fin n) : CDeriv Γ (Γ k)
  /-- `⊤`-introduction. -/
  | topI {I : Type u} {n : ℕ} {Γ : Fin n → Form I} : CDeriv Γ .top
  /-- `∧`-introduction. -/
  | andI {I : Type u} {n : ℕ} {Γ : Fin n → Form I} {φ ψ : Form I} (d : CDeriv Γ φ)
      (e : CDeriv Γ ψ) : CDeriv Γ (.and φ ψ)
  /-- `∧`-elimination, left. -/
  | andE₁ {I : Type u} {n : ℕ} {Γ : Fin n → Form I} {φ ψ : Form I} (d : CDeriv Γ (.and φ ψ)) :
      CDeriv Γ φ
  /-- `∧`-elimination, right. -/
  | andE₂ {I : Type u} {n : ℕ} {Γ : Fin n → Form I} {φ ψ : Form I} (d : CDeriv Γ (.and φ ψ)) :
      CDeriv Γ ψ
  /-- `→`-introduction: the premise becomes the hypothesis at position `0`. -/
  | impI {I : Type u} {n : ℕ} {Γ : Fin n → Form I} {φ ψ : Form I} (d : CDeriv (consF φ Γ) ψ) :
      CDeriv Γ (.imp φ ψ)
  /-- `→`-elimination. -/
  | impE {I : Type u} {n : ℕ} {Γ : Fin n → Form I} {φ ψ : Form I} (d : CDeriv Γ (.imp φ ψ))
      (e : CDeriv Γ φ) : CDeriv Γ ψ
  /-- `∨`-introduction, left. -/
  | orI₁ {I : Type u} {n : ℕ} {Γ : Fin n → Form I} {φ ψ : Form I} (d : CDeriv Γ φ) :
      CDeriv Γ (.or φ ψ)
  /-- `∨`-introduction, right. -/
  | orI₂ {I : Type u} {n : ℕ} {Γ : Fin n → Form I} {φ ψ : Form I} (d : CDeriv Γ ψ) :
      CDeriv Γ (.or φ ψ)
  /-- `∨`-elimination: each disjunct becomes the hypothesis at position `0` of its branch. -/
  | orE {I : Type u} {n : ℕ} {Γ : Fin n → Form I} {φ ψ χ : Form I} (d : CDeriv Γ (.or φ ψ))
      (e₁ : CDeriv (consF φ Γ) χ) (e₂ : CDeriv (consF ψ Γ) χ) : CDeriv Γ χ
  /-- `∀`-introduction: a derivation over the extended sort context. -/
  | allI {I : Type u} {n : ℕ} {Γ : Fin n → Form I} {K : I → Type u} {φ : Form (Σ i, K i)}
      (d : CDeriv (fun k => (Γ k).sub Sigma.fst) φ) : CDeriv Γ (.all φ)
  /-- `∀`-elimination at a term `t`. -/
  | allE {I : Type u} {n : ℕ} {Γ : Fin n → Form I} {K : I → Type u} {φ : Form (Σ i, K i)}
      (t : ∀ i, K i) (d : CDeriv Γ (.all φ)) : CDeriv Γ (φ.sub fun i => ⟨i, t i⟩)
  /-- `∃`-introduction at a term `t`. -/
  | exI {I : Type u} {n : ℕ} {Γ : Fin n → Form I} {K : I → Type u} {φ : Form (Σ i, K i)}
      (t : ∀ i, K i) (d : CDeriv Γ (φ.sub fun i => ⟨i, t i⟩)) : CDeriv Γ (.ex φ)
  /-- `∃`-elimination: the body becomes the hypothesis at position `0` over the extended sort
  context. -/
  | exE {I : Type u} {n : ℕ} {Γ : Fin n → Form I} {K : I → Type u} {φ : Form (Σ i, K i)}
      {ψ : Form I} (d : CDeriv Γ (.ex φ))
      (e : CDeriv (consF φ fun k => (Γ k).sub Sigma.fst) (ψ.sub Sigma.fst)) : CDeriv Γ ψ
  /-- Reductio ad absurdum. -/
  | raa {I : Type u} {n : ℕ} {Γ : Fin n → Form I} {φ : Form I}
      (d : CDeriv (consF (Form.not φ) Γ) Form.bot) : CDeriv Γ φ
  /-- Renaming of hypotheses along a map of contexts that keeps their formulas. -/
  | rename {I : Type u} {n m : ℕ} {Γ : Fin n → Form I} {Δ : Fin m → Form I} {φ : Form I}
      (ρ : Fin n → Fin m) (hρ : ∀ k, Δ (ρ k) = Γ k) (d : CDeriv Γ φ) : CDeriv Δ φ
  /-- Conversion to a formula of weaker truth value whose negative translation has the same
  Diller–Nahm meaning and a weaker truth value than the translation of the premise. -/
  | conv {I : Type u} {n : ℕ} {Γ : Fin n → Form I} {φ ψ : Form I}
      (hdn : φ.negT.dn = ψ.negT.dn) (hev : ∀ i, φ.eval i → ψ.eval i)
      (hevN : ∀ i, φ.negT.eval i → ψ.negT.eval i) (d : CDeriv Γ φ) : CDeriv Γ ψ

variable {I : Type u} {n : ℕ}

namespace CDeriv

/-- **Classical soundness for truth.** A classical derivation sends true hypotheses to a true
conclusion. -/
theorem eval {Γ : Fin n → Form I} {φ : Form I} (d : CDeriv Γ φ) (i : I)
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
  | raa d ih =>
    by_contra hφ
    exact ih i (consF_forall (fun ψ => ψ.eval i) hφ h)
  | rename ρ hρ d ih => exact ih i fun k => hρ k ▸ h (ρ k)
  | conv hdn hev hevN d ih => exact hev i (ih i h)

/-- Ex falso quodlibet, from reductio and a renaming. -/
def efq {Γ : Fin n → Form I} {φ : Form I} (d : CDeriv Γ Form.bot) : CDeriv Γ φ :=
  raa (rename Fin.succ (fun _ => rfl) d)

end CDeriv

namespace Deriv

/-- Transport of a derivation along an equality of conclusions. -/
def castC {Γ : Fin n → Form I} {φ ψ : Form I} (e : φ = ψ) (d : Deriv Γ φ) : Deriv Γ ψ := e ▸ d

/-- Transport keeps the use counts. -/
@[simp] theorem useCount_castC {Γ : Fin n → Form I} {φ ψ : Form I} (e : φ = ψ) (d : Deriv Γ φ)
    (k : Fin n) : (castC e d).useCount k = d.useCount k := by
  subst e
  rfl

/-- The instance at the bound variable of a universal formula reindexed along `Sigma.fst`. -/
def instSelf {K : I → Type u} {X : Form (Σ i, K i)} {Δ : Fin n → Form (Σ i, K i)}
    (d : Deriv Δ ((Form.all (K := K) X).sub Sigma.fst)) : Deriv Δ X :=
  conv (allE (K := fun x : Σ i, K i => K x.1) (φ := X.sub fun y => ⟨y.1.1, y.2⟩)
    (fun x => x.2) (conv d))

/-- The stability derivation `¬¬X → X` of a formula `X`. -/
abbrev Stab {m : ℕ} (Δ : Fin m → Form I) (X : Form I) : Type (u + 1) :=
  Deriv Δ (.imp (Form.not (Form.not X)) X)

/-- A negation is stable. -/
def stabNot {m : ℕ} (Δ : Fin m → Form I) (X : Form I) : Stab Δ (Form.not X) :=
  impI (impI (impE (hyp ⟨1, by omega⟩)
    (impI (impE (hyp ⟨0, by omega⟩) (hyp ⟨1, by omega⟩)))))

/-- Truth is stable. -/
def stabTop {m : ℕ} (Δ : Fin m → Form I) : Stab Δ .top :=
  impI topI

/-- A conjunction of stable formulas is stable. -/
def stabAnd {X Y : Form I} (sX : ∀ (m : ℕ) (Δ : Fin m → Form I), Stab Δ X)
    (sY : ∀ (m : ℕ) (Δ : Fin m → Form I), Stab Δ Y) {m : ℕ} (Δ : Fin m → Form I) :
    Stab Δ (.and X Y) :=
  impI (andI
    (impE (sX _ _) (impI (impE (hyp ⟨1, by omega⟩)
      (impI (impE (hyp ⟨1, by omega⟩) (andE₁ (hyp ⟨0, by omega⟩)))))))
    (impE (sY _ _) (impI (impE (hyp ⟨1, by omega⟩)
      (impI (impE (hyp ⟨1, by omega⟩) (andE₂ (hyp ⟨0, by omega⟩))))))))

/-- An implication with a stable conclusion is stable. -/
def stabImp {X Y : Form I} (sY : ∀ (m : ℕ) (Δ : Fin m → Form I), Stab Δ Y) {m : ℕ}
    (Δ : Fin m → Form I) : Stab Δ (.imp X Y) :=
  impI (impI (impE (sY _ _) (impI (impE (hyp ⟨2, by omega⟩)
    (impI (impE (hyp ⟨1, by omega⟩) (impE (hyp ⟨0, by omega⟩) (hyp ⟨2, by omega⟩))))))))

/-- A universal quantification of a stable formula is stable. -/
def stabAll {K : I → Type u} {X : Form (Σ i, K i)}
    (sX : ∀ (m : ℕ) (Δ : Fin m → Form (Σ i, K i)), Stab Δ X) {m : ℕ} (Δ : Fin m → Form I) :
    Stab Δ (.all X) :=
  impI (allI (impE (sX _ _) (impI (impE
    (conv (ψ := Form.not (Form.not ((Form.all X).sub Sigma.fst))) (hyp ⟨1, by omega⟩))
    (impI (impE (hyp ⟨1, by omega⟩) (instSelf (hyp ⟨0, by omega⟩))))))))

/-- Stability of a translated formula under a substitution. -/
def stabSub : {I : Type u} → (φ : Form I) → {J : Type u} → (h : J → I) → {m : ℕ} →
    (Δ : Fin m → Form J) → Stab Δ (φ.negT.sub h)
  | _, .atom p, _, h, _, Δ => conv (stabNot Δ (Form.not (.atom fun j => p (h j))))
  | _, .top, _, _, _, Δ => conv (stabTop Δ)
  | _, .and φ ψ, _, h, _, Δ =>
    conv (stabAnd (fun _ Δ' => stabSub φ h Δ') (fun _ Δ' => stabSub ψ h Δ') Δ)
  | _, .imp φ ψ, _, h, _, Δ =>
    conv (stabImp (X := φ.negT.sub h) (fun _ Δ' => stabSub ψ h Δ') Δ)
  | _, .or φ ψ, _, h, _, Δ =>
    conv (stabNot Δ ((Form.and (Form.not φ.negT) (Form.not ψ.negT)).sub h))
  | _, .all (K := K) φ, _, h, _, Δ =>
    conv (stabAll (K := fun j => K (h j)) (fun _ Δ' => stabSub φ (fun x => ⟨h x.1, x.2⟩) Δ') Δ)
  | _, .ex φ, _, h, _, Δ => conv (stabNot Δ ((Form.all (Form.not φ.negT)).sub h))
  | _, .sub g φ, _, h, _, Δ => conv (stabSub φ (fun j => g (h j)) Δ)

/-- **Stability.** Every negative translation is stable: `¬¬φᴺ → φᴺ` is derivable in every
context, without ex falso and without the realized axioms. -/
def stab : {I : Type u} → (φ : Form I) → {m : ℕ} → (Δ : Fin m → Form I) → Stab Δ φ.negT
  | _, .atom p, _, Δ => stabNot Δ (Form.not (.atom p))
  | _, .top, _, Δ => stabTop Δ
  | _, .and φ ψ, _, Δ => stabAnd (fun _ Δ' => stab φ Δ') (fun _ Δ' => stab ψ Δ') Δ
  | _, .imp _ ψ, _, Δ => stabImp (fun _ Δ' => stab ψ Δ') Δ
  | _, .or _ _, _, Δ => stabNot Δ _
  | _, .all φ, _, Δ => stabAll (fun _ Δ' => stab φ Δ') Δ
  | _, .ex _, _, Δ => stabNot Δ _
  | _, .sub h φ, _, Δ => stabSub φ h Δ

end Deriv

/-- The lift of a map of hypothesis positions to contexts extended at position `0`. -/
def liftR {m : ℕ} (ρ : Fin n → Fin m) : Fin (n + 1) → Fin (m + 1)
  | ⟨0, _⟩ => ⟨0, Nat.succ_pos _⟩
  | ⟨j + 1, h⟩ => (ρ ⟨j, Nat.lt_of_succ_lt_succ h⟩).succ

/-- The lifted map holds the translated hypotheses of an extended context. -/
theorem consF_liftR {Γ : Fin n → Form I} {m : ℕ} {Δ : Fin m → Form I} {ρ : Fin n → Fin m}
    (h : ∀ k, Δ (ρ k) = (Γ k).negT) (φ : Form I) :
    ∀ k, consF φ.negT Δ (liftR ρ k) = (consF φ Γ k).negT
  | ⟨0, _⟩ => rfl
  | ⟨_ + 1, _⟩ => h _

namespace CDeriv

/-- **The negative translation of derivations**, into a context `Δ` that holds the translated
hypotheses at the positions given by `ρ`. -/
def toDerivAt : {I : Type u} → {n : ℕ} → {Γ : Fin n → Form I} → {φ : Form I} → CDeriv Γ φ →
    {m : ℕ} → (Δ : Fin m → Form I) → (ρ : Fin n → Fin m) → (∀ k, Δ (ρ k) = (Γ k).negT) →
    Deriv Δ φ.negT
  | _, _, Γ, .(Γ k), .hyp k, _, _, ρ, h => Deriv.castC (h k) (.hyp (ρ k))
  | _, _, _, _, .topI, _, _, _, _ => .topI
  | _, _, _, _, .andI d e, _, Δ, ρ, h => .andI (d.toDerivAt Δ ρ h) (e.toDerivAt Δ ρ h)
  | _, _, _, _, .andE₁ d, _, Δ, ρ, h => .andE₁ (d.toDerivAt Δ ρ h)
  | _, _, _, _, .andE₂ d, _, Δ, ρ, h => .andE₂ (d.toDerivAt Δ ρ h)
  | _, _, _, _, .impI (φ := φ) d, _, Δ, ρ, h =>
    .impI (d.toDerivAt (consF φ.negT Δ) (liftR ρ) (consF_liftR h φ))
  | _, _, _, _, .impE d e, _, Δ, ρ, h => .impE (d.toDerivAt Δ ρ h) (e.toDerivAt Δ ρ h)
  | _, _, _, _, .orI₁ (φ := φ) (ψ := ψ) d, _, Δ, ρ, h =>
    .impI (.impE (.andE₁ (.hyp ⟨0, Nat.succ_pos _⟩))
      (d.toDerivAt (consF (.and (Form.not φ.negT) (Form.not ψ.negT)) Δ) (fun k => (ρ k).succ) h))
  | _, _, _, _, .orI₂ (φ := φ) (ψ := ψ) d, _, Δ, ρ, h =>
    .impI (.impE (.andE₂ (.hyp ⟨0, Nat.succ_pos _⟩))
      (d.toDerivAt (consF (.and (Form.not φ.negT) (Form.not ψ.negT)) Δ) (fun k => (ρ k).succ) h))
  | _, _, Γ, _, .orE (φ := φ) (ψ := ψ) (χ := χ) d e₁ e₂, _, Δ, ρ, h =>
    .impE (Deriv.stab χ Δ) (.impI (.impE
      (d.toDerivAt (consF (Form.not χ.negT) Δ) (fun k => (ρ k).succ) h)
      (.andI
        (.impI (.impE (.hyp ⟨1, by omega⟩)
          (e₁.toDerivAt _ (liftR fun k => (ρ k).succ)
            (consF_liftR (Γ := Γ) (Δ := consF (Form.not χ.negT) Δ) (ρ := fun k => (ρ k).succ)
              h φ))))
        (.impI (.impE (.hyp ⟨1, by omega⟩)
          (e₂.toDerivAt _ (liftR fun k => (ρ k).succ)
            (consF_liftR (Γ := Γ) (Δ := consF (Form.not χ.negT) Δ) (ρ := fun k => (ρ k).succ)
              h ψ)))))))
  | _, _, _, _, .allI d, _, Δ, ρ, h =>
    .allI (d.toDerivAt (fun k => (Δ k).sub Sigma.fst) ρ
      fun k => congrArg (Form.sub Sigma.fst) (h k))
  | _, _, _, _, .allE t d, _, Δ, ρ, h => .allE t (d.toDerivAt Δ ρ h)
  | _, _, _, _, .exI (K := K) (φ := φ) t d, _, Δ, ρ, h =>
    .impI (.impE (Deriv.conv (ψ := Form.not (φ.negT.sub fun i => (⟨i, t i⟩ : Σ i, K i)))
        (.allE t (.hyp ⟨0, Nat.succ_pos _⟩)))
      (d.toDerivAt (consF (.all (Form.not φ.negT)) Δ) (fun k => (ρ k).succ) h))
  | _, _, Γ, _, .exE (K := K) (φ := φ) (ψ := ψ) d e, _, Δ, ρ, h =>
    .impE (Deriv.stab ψ Δ) (.impI (.impE
      (d.toDerivAt (consF (Form.not ψ.negT) Δ) (fun k => (ρ k).succ) h)
      (.allI (.impI (.impE
        (Deriv.conv (ψ := Form.not (ψ.negT.sub Sigma.fst)) (.hyp ⟨1, by omega⟩))
        (e.toDerivAt _ (liftR fun k => (ρ k).succ)
          (consF_liftR (Γ := fun k => (Γ k).sub Sigma.fst)
            (Δ := fun k => (consF (Form.not ψ.negT) Δ k).sub Sigma.fst)
            (ρ := fun k => (ρ k).succ)
            (fun k => congrArg (Form.sub (Sigma.fst : (Σ i, K i) → _)) (h k)) φ)))))))
  | _, _, Γ, _, .raa (φ := φ) d, _, Δ, ρ, h =>
    .impE (Deriv.stab φ Δ) (.impI (.impE
      (.impE
        (.impI (d.toDerivAt (consF (Form.not φ).negT (consF (Form.not φ.negT) Δ))
          (liftR fun k => (ρ k).succ)
          (consF_liftR (Γ := Γ) (Δ := consF (Form.not φ.negT) Δ) (ρ := fun k => (ρ k).succ)
            h (Form.not φ))))
        (.impI (.impI (.impE (.hyp ⟨2, by omega⟩) (.hyp ⟨1, by omega⟩)))))
      (.impI (.hyp ⟨0, Nat.succ_pos _⟩))))
  | _, _, _, _, .rename ρ₀ hρ d, _, Δ, ρ, h =>
    d.toDerivAt Δ (fun k => ρ (ρ₀ k)) fun k => (h (ρ₀ k)).trans (congrArg Form.negT (hρ k))
  | _, _, _, _, .conv hdn _ hevN d, _, Δ, ρ, h => Deriv.conv (d.toDerivAt Δ ρ h) hdn hevN

/-- **The translation theorem.** The negative translation of a classical derivation, as a
derivation of `Deriv` from the translated hypotheses. -/
def translate {Γ : Fin n → Form I} {φ : Form I} (d : CDeriv Γ φ) :
    Deriv (fun k => (Γ k).negT) φ.negT :=
  d.toDerivAt _ id fun _ => rfl

/-! ## Π⁰₂ extraction -/

section Pi2

variable {K : I → Type u} {L : (Σ i, K i) → Type u} (p : (Σ x : Σ i, K i, L x) → Prop)
  (sel : ∀ x : Σ i, K i, Multiset (L x) → L x)
  (hsel : ∀ x ys, ((∀ y ∈ ys, ¬ p ⟨x, y⟩) → False) → p ⟨x, sel x ys⟩)

/-- The selection of a candidate: from a multiset of candidates not all of which fail `p`, the
candidate chosen by `sel`, demanding the one counter-witness of the premise. -/
def selHom : (Form.ex (K := fun x : Σ i, K i => Multiset (L x))
      (.atom fun z => (∀ y ∈ z.2, ¬ p ⟨z.1, y⟩) → False)).dn.Hom
      (Form.ex (K := L) (.atom p)).dn where
  fwd x w := ⟨sel x w.1, PUnit.unit⟩
  back _ _ _ := {PUnit.unit}
  sound x w _ h := hsel x w.1 (h PUnit.unit (Multiset.mem_singleton_self _))

/-- The derivation of `∀ x, ∃ y, p (x, y)` from its negative translation, by Markov's principle
and the selection `sel`, in every context. -/
def pi2Imp {m : ℕ} (Δ : Fin m → Form I) :
    Deriv Δ (.imp (Deriv.allEx (X := K) (Y := L) p).negT (Deriv.allEx p)) :=
  .impI (.allI (.hom (selHom p sel hsel) 1 (fun _ _ _ => (Multiset.card_singleton _).le)
    (fun x hx => by
      obtain ⟨ys, hq⟩ := hx
      exact ⟨sel x ys, hsel x ys hq⟩)
    (.markov (fun z => ¬ p z) (fun _ => False)
      (.impI (.impE (Deriv.instSelf (.hyp ⟨1, by omega⟩))
        (.allI (.impI (.impE (.hyp ⟨0, by omega⟩)
          (.impI (.atom₂ (p := fun z => ¬ p z) (q := p) (fun _ hnp hp => hnp hp)
            (Deriv.instSelf (.hyp ⟨2, by omega⟩)) (.hyp ⟨0, by omega⟩)))))))))))

/-- **Π⁰₂ extraction.** A classical derivation of `∀ x, ∃ y, p (x, y)` gives a derivation of
`∀ x, ∃ y, p (x, y)` from the translated hypotheses: the negative translation followed by
Markov's principle and the selection `sel`. -/
def pi2 {Γ : Fin n → Form I} (c : CDeriv Γ (Deriv.allEx (X := K) (Y := L) p)) :
    Deriv (fun k => (Γ k).negT) (Deriv.allEx p) :=
  .impE (pi2Imp p sel hsel _) c.translate

/-- The extracted derivation uses each translated hypothesis as often as the translated
derivation does. -/
theorem useCount_pi2 {Γ : Fin n → Form I} (c : CDeriv Γ (Deriv.allEx (X := K) (Y := L) p))
    (k : Fin n) : (pi2 p sel hsel c).useCount k = c.translate.useCount k := by
  have h₁ : k.succ.succ ≠ 1 := by simp [Fin.ext_iff]
  have h₂ : k.succ.succ.succ.succ ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  simp [pi2, pi2Imp, Deriv.useCount, Deriv.uses, Deriv.instSelf, Deriv.conv, h₁, h₂]
  split_ifs with h <;> simp_all [Fin.ext_iff, Nat.mod_eq_of_lt]

/-- The function extracted from a classical derivation of `∀ x, ∃ y, p (x, y)`: the realizer of
`pi2` at a witness `w` of the translated hypotheses. -/
def extract {Γ : Fin n → Form I} (c : CDeriv Γ (Deriv.allEx (X := K) (Y := L) p)) (i : I)
    (w : (ctx fun k => (Γ k).negT).W i) (x : K i) : L ⟨i, x⟩ :=
  ((pi2 p sel hsel c).realize.fwd i w x).1

/-- **Correctness of the extracted function.** When the witness `w` withstands every
counter-witness of the translated hypotheses, the extracted function satisfies `p`. -/
theorem extract_spec {Γ : Fin n → Form I} (c : CDeriv Γ (Deriv.allEx (X := K) (Y := L) p))
    (i : I) (w : (ctx fun k => (Γ k).negT).W i)
    (hw : ∀ c', (ctx fun k => (Γ k).negT).mat i w c') (x : K i) :
    p ⟨⟨i, x⟩, extract p sel hsel c i w x⟩ :=
  (pi2 p sel hsel c).realize.sound i w ⟨x, PUnit.unit⟩ fun y _ => hw y

/-- The function extracted from a closed classical derivation of `∀ x, ∃ y, p (x, y)`. -/
def extractClosed {Γ : Fin 0 → Form I} (c : CDeriv Γ (Deriv.allEx (X := K) (Y := L) p))
    (i : I) (x : K i) : L ⟨i, x⟩ :=
  extract p sel hsel c i (fun k => k.elim0) x

/-- **Correctness of the function extracted from a closed derivation.** -/
theorem extractClosed_spec {Γ : Fin 0 → Form I} (c : CDeriv Γ (Deriv.allEx (X := K) (Y := L) p))
    (i : I) (x : K i) : p ⟨⟨i, x⟩, extractClosed p sel hsel c i x⟩ :=
  extract_spec p sel hsel c i _ (fun c' => c'.1.elim0) x

end Pi2

/-- A selection of a satisfying candidate by choice, with a default `y₀`. -/
noncomputable def classicalSel {K : I → Type u} {L : (Σ i, K i) → Type u}
    (p : (Σ x : Σ i, K i, L x) → Prop) (y₀ : ∀ x, L x) (x : Σ i, K i) (ys : Multiset (L x)) :
    L x :=
  open Classical in if h : ∃ y ∈ ys, p ⟨x, y⟩ then h.choose else y₀ x

/-- The selection by choice picks a satisfying candidate when not all candidates fail. -/
theorem classicalSel_spec {K : I → Type u} {L : (Σ i, K i) → Type u}
    (p : (Σ x : Σ i, K i, L x) → Prop) (y₀ : ∀ x, L x) (x : Σ i, K i) (ys : Multiset (L x))
    (h : (∀ y ∈ ys, ¬ p ⟨x, y⟩) → False) : p ⟨x, classicalSel p y₀ x ys⟩ := by
  have he : ∃ y ∈ ys, p ⟨x, y⟩ := by
    by_contra hn
    exact h fun y hy hp => hn ⟨y, hy, hp⟩
  simp only [classicalSel, he, ↓reduceDIte]
  exact he.choose_spec.2

/-! ## Example: double negation elimination -/

/-- Double negation elimination for an atom, a classical derivation from the hypothesis `¬¬q`. -/
def dneAtom (q : I → Prop) :
    CDeriv (fun _ : Fin 1 => Form.not (Form.not (.atom q))) (.atom q) :=
  .raa (.impE (.hyp ⟨1, by omega⟩) (.hyp ⟨0, by omega⟩))

/-- The negative translation of double negation elimination uses its hypothesis once. -/
theorem useCount_translate_dneAtom (q : I → Prop) : (dneAtom q).translate.useCount 0 = 1 :=
  rfl

end CDeriv

end CatCrypt.Container.DNLogic
