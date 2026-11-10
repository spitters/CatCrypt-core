/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Container.DNLogicMono

/-!
# Majorant data of classical derivations

The bound extraction `CDeriv.extract_costMaj` of `Container/DNLogicMono.lean` reads majorant data
`Deriv.MajD` of the extracted derivation `CDeriv.pi2`. This module builds those data from data
stated on the classical derivation and on the selection:

* `CDeriv.MajData` — a majorant of each term of `∀`-elimination and `∃`-introduction of the
  classical derivation, and a majorant of each conversion `CDeriv.conv` (whose two translated
  formulas may have different majorant types);
* `CDeriv.Pi2Maj` — a majorant of Markov's principle and of the selection `sel` at the
  extracted statement, which depend on the size of finite multisets of candidates and on `sel`.

Every other step the translation inserts has canonical data: the conversions of `Deriv.conv`
between formulas of the same majorization have the identity majorant (`HomMaj.ofFun` at the
identity, and `Deriv.stabSubAndConv` through `Deriv.maj_sub_and` at a conjunction), the
stability derivations `Deriv.stab` and `Deriv.stabSub` have the data `Deriv.stab_majD` built from
those of their parts, the term `fun x => x.2` of `Deriv.instSelf` has the majorant `id` in an
extended environment, and renamings and hypotheses need no data. `CDeriv.toMajD` translates the
data along `CDeriv.toDerivAt`, and `CDeriv.pi2MajD` gives the data of `CDeriv.pi2`.

`CDeriv.Pi2Maj.ofSize` builds the data of Markov's principle and the selection for a size that
bounds a multiset by a bound on its elements and a selection bounded by a function of the size of
the multiset; `CDeriv.Pi2Maj.ofSup` is its instance at the maximum of the sizes of the elements
(`CDeriv.supSize`), which needs only the bound on the selection. The example `CDeriv.dneAllEx` is
double negation elimination for a Π⁰₂ statement, and `CDeriv.dneAllEx_exists_le` is its bound
extraction.

## Main definitions

* `CDeriv.MajData`, `CDeriv.Pi2Maj`, `CDeriv.supSize` — majorant data of classical derivations
  and the size of a multiset of candidates;
* `CDeriv.toMajD`, `CDeriv.pi2MajD` — the majorant data of the translated and the extracted
  derivation.

## Main results

* `CDeriv.extract_costMaj'`, `CDeriv.exists_le_extract_pi2Bound'` — bound extraction from
  classical derivations with majorant data on the classical derivation;
* `CDeriv.dneAllEx_exists_le` — the bound of double negation elimination.

Search words: monotone functional interpretation, majorant, negative translation, proof mining,
bound extraction, classical derivation.
-/

set_option autoImplicit false

@[expose] public section

universe u

namespace CatCrypt.Container.DNLogic

open DPred CatCrypt.Core Form

variable {I : Type u} {n : ℕ}

/-- A majorant of a morphism of meanings that sends each majorant of the source to one majorant
of the target and back, independent of the environment. -/
def HomMaj.ofFun {R : ℕ → I → Prop} {φ ψ : Form I} (f : φ.dn.Hom ψ.dn) (e : φ.B → ψ.B)
    (e' : φ.B → ψ.Bc → φ.Bc)
    (h : ∀ i a ba, Maj φ i ba a → Maj ψ i (e ba) (f.fwd i a) ∧
      ∀ bc c, MajC ψ i bc (f.fwd i a) c → ∀ x ∈ f.back i a c, MajC φ i (e' ba bc) a x) :
    HomMaj R φ ψ f :=
  ⟨(fun _ => e, fun _ ba bc => [e' ba bc]), fun _ i _ a ba ha =>
    ⟨(h i a ba ha).1, fun bc c hc x hx =>
      ⟨e' ba bc, List.mem_singleton_self _, (h i a ba ha).2 bc c hc x hx⟩⟩⟩

/-- The identity majorant of a conversion between formulas whose majorant types and
majorization agree definitionally. -/
local macro "conv_maj%" : term =>
  `(HomMaj.ofFun _ (fun b => b) (fun _ bc => bc) (by
    intro i a ba ha
    refine ⟨ha, fun bc c hc x hx => ?_⟩
    have e : x = c := Multiset.mem_singleton.1 hx
    subst e
    exact hc))

namespace Deriv

/-- Transport of majorant data along an equality of conclusions. -/
def castC_majD {Γ : Fin n → Form I} {φ ψ : Form I} (e : φ = ψ) (d : Deriv Γ φ)
    (R : ℕ → I → Prop) (D : MajD d R) : MajD (castC e d) R := by
  subst e
  exact D

/-- The majorant of the term `fun x => x.2` of `instSelf` in an extended environment. -/
def sndTermMaj {K : I → Type u} (s : ∀ i, K i → ℕ) (R : ℕ → I → Prop) :
    TermMaj (K := fun x : Σ i, K i => K x.1) (fun x => s x.1) (envExt R s) fun x => x.2 :=
  ⟨id, fun _ _ h => h.2⟩

/-- Majorant data of `instSelf` in an extended environment. -/
def instSelf_majD {K : I → Type u} {s : ∀ i, K i → ℕ} {X : Form (Σ i, K i)}
    {Δ : Fin n → Form (Σ i, K i)}
    (d : Deriv Δ ((Form.all (K := K) (sz := s) X).sub Sigma.fst)) (R : ℕ → I → Prop)
    (D : MajD d (envExt R s)) : MajD (instSelf d) (envExt R s) :=
  ((sndTermMaj s R, (D, HomMaj.ofFun _ (fun b => b) (fun _ bc => bc) (by
    intro i a ba ha
    refine ⟨ha, fun bc c hc x hx => ?_⟩
    obtain rfl := Multiset.mem_singleton.1 hx
    revert hc
    unfold homOfEq
    intro hc
    refine ⟨hc.1, ?_⟩
    exact hc.2
    ))), HomMaj.ofFun _ (fun b => b) (fun _ bc => bc) (by
    intro i a ba ha
    refine ⟨ha, fun bc c hc x hx => ?_⟩
    obtain rfl := Multiset.mem_singleton.1 hx
    revert hc
    exact id
    ))

/-- Majorant data of `stabNot`. -/
def stabNot_majD {m : ℕ} (Δ : Fin m → Form I) (X : Form I) (R : ℕ → I → Prop) :
    MajD (stabNot Δ X) R :=
  ((), ((), ()))

/-- Majorant data of `stabTop`. -/
def stabTop_majD {m : ℕ} (Δ : Fin m → Form I) (R : ℕ → I → Prop) : MajD (stabTop Δ) R :=
  ()

/-- Majorant data of `stabAnd`, from those of the stability of the conjuncts. -/
def stabAnd_majD {X Y : Form I} (sX : ∀ (m : ℕ) (Δ : Fin m → Form I), Stab Δ X)
    (sY : ∀ (m : ℕ) (Δ : Fin m → Form I), Stab Δ Y)
    (hX : ∀ (m : ℕ) (Δ : Fin m → Form I) (R : ℕ → I → Prop), MajD (sX m Δ) R)
    (hY : ∀ (m : ℕ) (Δ : Fin m → Form I) (R : ℕ → I → Prop), MajD (sY m Δ) R) {m : ℕ}
    (Δ : Fin m → Form I) (R : ℕ → I → Prop) : MajD (stabAnd sX sY Δ) R :=
  ((hX _ _ R, ((), ((), ()))), (hY _ _ R, ((), ((), ()))))

/-- Majorant data of `stabImp`, from those of the stability of the conclusion. -/
def stabImp_majD {X Y : Form I} (sY : ∀ (m : ℕ) (Δ : Fin m → Form I), Stab Δ Y)
    (hY : ∀ (m : ℕ) (Δ : Fin m → Form I) (R : ℕ → I → Prop), MajD (sY m Δ) R) {m : ℕ}
    (Δ : Fin m → Form I) (R : ℕ → I → Prop) : MajD (stabImp (X := X) sY Δ) R :=
  (hY _ _ R, ((), ((), ((), ()))))

/-- Majorant data of `stabAll`, from those of the stability of the body. -/
def stabAll_majD {K : I → Type u} {s : ∀ i, K i → ℕ} {X : Form (Σ i, K i)}
    (sX : ∀ (m : ℕ) (Δ : Fin m → Form (Σ i, K i)), Stab Δ X)
    (hX : ∀ (m : ℕ) (Δ : Fin m → Form (Σ i, K i)) (R : ℕ → (Σ i, K i) → Prop),
      MajD (sX m Δ) R) {m : ℕ} (Δ : Fin m → Form I) (R : ℕ → I → Prop) :
    MajD (stabAll (s := s) sX Δ) R :=
  (hX _ _ _, ((((), conv_maj%), ((), instSelf_majD _ R ()))))

/-- Majorization of a substituted conjunction is that of the conjunction of the substituted
conjuncts. -/
theorem maj_sub_and {J : Type u} (φ ψ : Form I) (h : J → I) (j : J) :
    maj ((φ.sub h).and (ψ.sub h)) j = maj ((φ.and ψ).sub h) j := by
  refine Prod.ext rfl ?_
  funext bc w c
  rcases bc with b | b <;> rcases c with c | c <;> rfl

/-- The identity majorant of the conversion of `stabSub` at a conjunction. -/
def stabSubAndConv {J : Type u} (φ ψ : Form I) (h : J → I) (R : ℕ → J → Prop) :
    HomMaj R (Form.imp (Form.not (Form.not ((φ.negT.sub h).and (ψ.negT.sub h))))
        ((φ.negT.sub h).and (ψ.negT.sub h)))
      (Form.imp (Form.not (Form.not ((φ.and ψ).negT.sub h))) ((φ.and ψ).negT.sub h))
      (homOfEq rfl) :=
  HomMaj.ofFun _ (fun b => b) (fun _ bc => bc) (by
    intro i a ba ha
    have hX := maj_sub_and φ.negT ψ.negT h i
    refine ⟨?_, fun bc c hc x hx => ?_⟩
    · simp only [Maj, Form.maj.eq_4] at ha ⊢
      rw [hX] at ha
      exact ha
    · have e : x = c := Multiset.mem_singleton.1 hx
      subst e
      have hX' : maj ((φ.negT.sub h).and (ψ.negT.sub h)) i = maj ((φ.and ψ).negT.sub h) i :=
        hX
      simp only [MajC, Form.maj.eq_4] at hc ⊢
      rw [← hX'] at hc
      exact hc)

/-- Majorant data of `stabSub`. -/
def stabSub_majD : {I : Type u} → (φ : Form I) → {J : Type u} → (h : J → I) → {m : ℕ} →
    (Δ : Fin m → Form J) → (R : ℕ → J → Prop) → MajD (stabSub φ h Δ) R
  | _, .atom _, _, _, _, Δ, R => (stabNot_majD Δ _ R, conv_maj%)
  | _, .top, _, _, _, Δ, R => (stabTop_majD Δ R, conv_maj%)
  | _, .and φ ψ, _, h, _, Δ, R =>
    (stabAnd_majD _ _ (fun _ Δ' R' => stabSub_majD φ h Δ' R')
      (fun _ Δ' R' => stabSub_majD ψ h Δ' R') Δ R, stabSubAndConv φ ψ h R)
  | _, .imp _ ψ, _, h, _, Δ, R =>
    (stabImp_majD _ (fun _ Δ' R' => stabSub_majD ψ h Δ' R') Δ R, conv_maj%)
  | _, .or _ _, _, _, _, Δ, R => (stabNot_majD Δ _ R, conv_maj%)
  | _, .all φ, _, h, _, Δ, R =>
    (stabAll_majD _ (fun _ Δ' R' => stabSub_majD φ (fun x => ⟨h x.1, x.2⟩) Δ' R') Δ R,
      conv_maj%)
  | _, .ex _, _, _, _, Δ, R => (stabNot_majD Δ _ R, conv_maj%)
  | _, .sub g φ, _, h, _, Δ, R => (stabSub_majD φ (fun j => g (h j)) Δ R, conv_maj%)

/-- **Majorant data of stability.** The stability derivation of a translated formula has
canonical majorant data in every environment. -/
def stab_majD : {I : Type u} → (φ : Form I) → {m : ℕ} → (Δ : Fin m → Form I) →
    (R : ℕ → I → Prop) → MajD (stab φ Δ) R
  | _, .atom _, _, Δ, R => stabNot_majD Δ _ R
  | _, .top, _, Δ, R => stabTop_majD Δ R
  | _, .and φ ψ, _, Δ, R =>
    stabAnd_majD _ _ (fun _ Δ' R' => stab_majD φ Δ' R') (fun _ Δ' R' => stab_majD ψ Δ' R') Δ R
  | _, .imp _ ψ, _, Δ, R => stabImp_majD _ (fun _ Δ' R' => stab_majD ψ Δ' R') Δ R
  | _, .or _ _, _, Δ, R => stabNot_majD Δ _ R
  | _, .all φ, _, Δ, R => stabAll_majD _ (fun _ Δ' R' => stab_majD φ Δ' R') Δ R
  | _, .ex _, _, Δ, R => stabNot_majD Δ _ R
  | _, .sub h φ, _, Δ, R => stabSub_majD φ h Δ R

end Deriv

namespace CDeriv

/-- **Majorant data of a classical derivation** over the environment `R`: a majorant of each term
of `∀`-elimination and `∃`-introduction, and a majorant of the morphism of each conversion
between the translated formulas. -/
def MajData : {I : Type u} → {n : ℕ} → {Γ : Fin n → Form I} → {φ : Form I} → CDeriv Γ φ →
    (ℕ → I → Prop) → Type
  | _, _, Γ, .(Γ k), .hyp k, _ => Unit
  | _, _, _, _, .topI, _ => Unit
  | _, _, _, _, .andI d e, R => MajData d R × MajData e R
  | _, _, _, _, .andE₁ d, R => MajData d R
  | _, _, _, _, .andE₂ d, R => MajData d R
  | _, _, _, _, .impI d, R => MajData d R
  | _, _, _, _, .impE d e, R => MajData d R × MajData e R
  | _, _, _, _, .orI₁ d, R => MajData d R
  | _, _, _, _, .orI₂ d, R => MajData d R
  | _, _, _, _, .orE d e₁ e₂, R => MajData d R × MajData e₁ R × MajData e₂ R
  | _, _, _, _, .allI (s := s) d, R => MajData d (envExt R s)
  | _, _, _, _, .allE (s := s) t d, R => TermMaj s R t × MajData d R
  | _, _, _, _, .exI (s := s) t d, R => TermMaj s R t × MajData d R
  | _, _, _, _, .exE (s := s) d e, R => MajData d R × MajData e (envExt R s)
  | _, _, _, _, .raa d, R => MajData d R
  | _, _, _, _, .rename _ _ d, R => MajData d R
  | _, _, _, _, .conv (φ := φ) (ψ := ψ) hdn _ _ d, R =>
    MajData d R × HomMaj R φ.negT ψ.negT (homOfEq hdn)

/-- **The majorant data of the negative translation.** From majorant data of a classical
derivation, the majorant data of its translation `toDerivAt` into every context. -/
def toMajD : {I : Type u} → {n : ℕ} → {Γ : Fin n → Form I} → {φ : Form I} →
    (d : CDeriv Γ φ) → (R : ℕ → I → Prop) → MajData d R → {m : ℕ} →
    (Δ : Fin m → Form I) → (ρ : Fin n → Fin m) → (h : ∀ k, Δ (ρ k) = (Γ k).negT) →
    Deriv.MajD (d.toDerivAt Δ ρ h) R
  | _, _, Γ, .(Γ k), .hyp k, R, _, _, _, ρ, h => Deriv.castC_majD (h k) (.hyp (ρ k)) R ()
  | _, _, _, _, .topI, _, _, _, _, _, _ => ()
  | _, _, _, _, .andI d e, R, D, _, Δ, ρ, h => (toMajD d R D.1 Δ ρ h, toMajD e R D.2 Δ ρ h)
  | _, _, _, _, .andE₁ d, R, D, _, Δ, ρ, h => toMajD d R D Δ ρ h
  | _, _, _, _, .andE₂ d, R, D, _, Δ, ρ, h => toMajD d R D Δ ρ h
  | _, _, _, _, .impI d, R, D, _, _, _, _ => toMajD d R D _ _ _
  | _, _, _, _, .impE d e, R, D, _, Δ, ρ, h => (toMajD d R D.1 Δ ρ h, toMajD e R D.2 Δ ρ h)
  | _, _, _, _, .orI₁ d, R, D, _, _, _, _ => ((), toMajD d R D _ _ _)
  | _, _, _, _, .orI₂ d, R, D, _, _, _, _ => ((), toMajD d R D _ _ _)
  | _, _, _, _, .orE (χ := χ) d e₁ e₂, R, D, _, Δ, _, _ =>
    (Deriv.stab_majD χ Δ R, (toMajD d R D.1 _ _ _,
      (((), toMajD e₁ R D.2.1 _ _ _), ((), toMajD e₂ R D.2.2 _ _ _))))
  | _, _, _, _, .allI (s := s) d, R, D, _, _, _, _ => toMajD d (envExt R s) D _ _ _
  | _, _, _, _, .allE _ d, R, D, _, Δ, ρ, h => (D.1, toMajD d R D.2 Δ ρ h)
  | _, _, _, _, .exI _ d, R, D, _, _, _, _ => (((D.1, ()), conv_maj%), toMajD d R D.2 _ _ _)
  | _, _, _, _, .exE (s := s) (ψ := ψ) d e, R, D, _, Δ, _, _ =>
    (Deriv.stab_majD ψ Δ R, (toMajD d R D.1 _ _ _,
      (((), conv_maj%), toMajD e (envExt R s) D.2 _ _ _)))
  | _, _, _, _, .raa (φ := φ) d, R, D, _, Δ, _, _ =>
    (Deriv.stab_majD φ Δ R, ((toMajD d R D _ _ _, ((), ())), ()))
  | _, _, _, _, .rename _ _ d, R, D, _, _, _, _ => toMajD d R D _ _ _
  | _, _, _, _, .conv _ _ _ d, R, D, _, Δ, ρ, h => (toMajD d R D.1 Δ ρ h, D.2)

/-- The majorant data of the translation `translate`. -/
def translateMajD {Γ : Fin n → Form I} {φ : Form I} (d : CDeriv Γ φ) (R : ℕ → I → Prop)
    (D : MajData d R) : Deriv.MajD d.translate R :=
  toMajD d R D _ id fun _ => rfl

section Pi2

variable {K : I → Type u} {L : (Σ i, K i) → Type u} (p : (Σ x : Σ i, K i, L x) → Prop)
  (sel : ∀ x : Σ i, K i, Multiset (L x) → L x)
  (hsel : ∀ x ys, ((∀ y ∈ ys, ¬ p ⟨x, y⟩) → False) → p ⟨x, sel x ys⟩)
  (sM : ∀ x : Σ i, K i, Multiset (L x) → ℕ)
  {sX : ∀ i, K i → ℕ} {sY : ∀ x, L x → ℕ}

variable (sX sY) in
/-- **Majorant data of the extraction step**: majorants, in the environment extended by the
argument, of Markov's principle for `¬ p` and of the selection `sel`. They concern the size of
finite multisets of candidates and the selection, which the classical derivation does not
determine. -/
structure Pi2Maj (R : ℕ → I → Prop) : Type where
  /-- A majorant of Markov's principle. -/
  markov : HomMaj (envExt R sX)
    (.imp (.all (sz := sY) (.atom fun z => ¬ p z)) (.atom fun _ => False))
    (.ex (K := fun x => Multiset (L x)) (sz := sM)
      (.atom fun x => (∀ k ∈ x.2, ¬ p ⟨x.1, k⟩) → False))
    (DPred.markovDN (fun z => ¬ p z) fun _ => False)
  /-- A majorant of the selection. -/
  sel : HomMaj (envExt R sX) (Form.ex (K := fun x : Σ i, K i => Multiset (L x)) (sz := sM)
      (.atom fun z => (∀ y ∈ z.2, ¬ p ⟨z.1, y⟩) → False))
    (Form.ex (K := L) (sz := sY) (.atom p))
    (selHom p sel hsel sM)

/-- The majorant data of `pi2Imp`. -/
def pi2Imp_majD (R : ℕ → I → Prop) (P : Pi2Maj p sel hsel sM sX sY R) {m : ℕ}
    (Δ : Fin m → Form I) :
    Deriv.MajD (pi2Imp (sX := sX) (sY := sY) p sel hsel sM Δ) R :=
  (((Deriv.instSelf_majD _ R (), ((), (Deriv.instSelf_majD _ _ (), ()))), P.markov),
    P.sel)

/-- **The majorant data of the extracted derivation** `pi2`, from majorant data of the classical
derivation and of the extraction step. -/
def pi2MajD {Γ : Fin n → Form I} (c : CDeriv Γ (Deriv.allEx (X := K) (Y := L) sX sY p))
    (R : ℕ → I → Prop) (D : MajData c R) (P : Pi2Maj p sel hsel sM sX sY R) :
    Deriv.MajD (pi2 p sel hsel sM c) R :=
  (pi2Imp_majD p sel hsel sM R P _, translateMajD c R D)

/-- **Bound extraction from classical derivations, with data on the classical derivation.** The
bound of the extracted derivation, computed from majorant data of the classical derivation and
of the extraction step, is a cost majorant of the size of the extracted function. -/
theorem extract_costMaj' {Γ : Fin n → Form I}
    (c : CDeriv Γ (Deriv.allEx (X := K) (Y := L) sX sY p)) (R : ℕ → I → Prop) (hR : Monotone R)
    (D : MajData c R) (P : Pi2Maj p sel hsel sM sX sY R) (hm : CtxB fun k => (Γ k).negT) (m₀ : ℕ)
    (i : I) (hi : R m₀ i) (w : (ctx fun k => (Γ k).negT).W i)
    (hw : ∀ k, Maj (Γ k).negT i (hm k) (w k)) :
    CostMaj (sX i)
      (pi2Bound (Deriv.bnd (pi2 p sel hsel sM c) R (pi2MajD p sel hsel sM c R D P) hm m₀).1)
      (fun x => sY ⟨i, x⟩ (extract p sel hsel sM c i w x)) :=
  extract_costMaj p sel hsel sM c R hR _ hm m₀ i hi w hw

/-- **Π⁰₂ bound for classical derivations, with data on the classical derivation.** -/
theorem exists_le_extract_pi2Bound' {Γ : Fin n → Form I}
    (c : CDeriv Γ (Deriv.allEx (X := K) (Y := L) sX sY p)) (R : ℕ → I → Prop) (hR : Monotone R)
    (D : MajData c R) (P : Pi2Maj p sel hsel sM sX sY R) (hm : CtxB fun k => (Γ k).negT) (m₀ : ℕ)
    (i : I) (hi : R m₀ i) (w : (ctx fun k => (Γ k).negT).W i)
    (hw : ∀ k, Maj (Γ k).negT i (hm k) (w k))
    (hmat : ∀ c', (ctx fun k => (Γ k).negT).mat i w c') (x : K i) :
    ∃ y : L ⟨i, x⟩, sY ⟨i, x⟩ y ≤
        pi2Bound (Deriv.bnd (pi2 p sel hsel sM c) R (pi2MajD p sel hsel sM c R D P) hm m₀).1
          (sX i x) ∧ p ⟨⟨i, x⟩, y⟩ :=
  exists_le_extract_pi2Bound p sel hsel sM c R hR _ hm m₀ i hi w hw hmat x

/-- The first component of a member of a list is at most the sum of the first components. -/
theorem le_sum_map_fst {L : List (ℕ × Unit)} {b : ℕ × Unit} (h : b ∈ L) :
    b.1 ≤ (L.map Prod.fst).sum := by
  induction L with
  | nil => cases h
  | cons a L ih =>
    rcases List.mem_cons.1 h with rfl | h
    · simp
    · simp only [List.map_cons, List.sum_cons]
      exact (ih h).trans (Nat.le_add_left _ _)

/-- **Majorant data of the extraction step from sizes.** For a size `sM` that bounds a multiset of
candidates by every bound on its elements, and a selection whose size is bounded by `sb` of a
bound on the size of the multiset, Markov's principle has the majorant that bounds the multiset
by the sum of the bounds of the demanded candidates, and the selection has the majorant `sb`. -/
def Pi2Maj.ofSize (hms : ∀ x (ms : Multiset (L x)) (B : ℕ), (∀ k ∈ ms, sY x k ≤ B) → sM x ms ≤ B)
    (sb : ℕ → ℕ) (hsb : ∀ x (ys : Multiset (L x)) (B : ℕ), sM x ys ≤ B → sY x (sel x ys) ≤ sb B)
    (R : ℕ → I → Prop) : Pi2Maj p sel hsel sM sX sY R where
  markov := HomMaj.ofFun _
    (fun ba => (((ba.2 (fun _ => ()) ()).map Prod.fst).sum, ()))
    (fun _ _ => (fun _ => (), ())) (fun x F ba hF => by
      refine ⟨⟨hms x _ _ fun k hk => ?_, trivial⟩, fun _ _ _ _ _ => ⟨fun _ _ _ => trivial, trivial⟩⟩
      obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hk
      obtain ⟨b', hb', hle, -⟩ :=
        (hF _ (fun _ => ()) (fun _ _ _ => trivial)).2 () PUnit.unit trivial y hy
      exact hle.trans (le_sum_map_fst hb'))
  sel := HomMaj.ofFun _ (fun ba => (sb ba.1, ())) (fun _ _ => ()) (fun x ys ba hys =>
    ⟨⟨hsb x ys.1 ba.1 hys.1, trivial⟩, fun _ _ _ _ _ => trivial⟩)

/-- The size of a multiset of candidates: the maximum of the sizes of its elements. -/
def supSize (sY : ∀ x, L x → ℕ) : ∀ x : Σ i, K i, Multiset (L x) → ℕ :=
  fun x ms => (ms.map (sY x)).sup

/-- **Majorant data of the extraction step at the maximum size.** At `supSize`, the bound of a
multiset by a bound on its elements is the universal property of the supremum, and the only
hypothesis is a bound on the selection. -/
def Pi2Maj.ofSup (sb : ℕ → ℕ)
    (hsb : ∀ x (ys : Multiset (L x)) (B : ℕ), supSize sY x ys ≤ B → sY x (sel x ys) ≤ sb B)
    (R : ℕ → I → Prop) : Pi2Maj p sel hsel (supSize sY) sX sY R :=
  Pi2Maj.ofSize p sel hsel (supSize sY) (fun x ms B h => Multiset.sup_le.2 fun b hb => by
    obtain ⟨k, hk, rfl⟩ := Multiset.mem_map.1 hb
    exact h k hk) sb hsb R

end Pi2

/-! ## Example: double negation elimination for a Π⁰₂ statement -/

section Dne

variable {K : I → Type u} {L : (Σ i, K i) → Type u} (r : (Σ x : Σ i, K i, L x) → Prop)
  (sX : ∀ i, K i → ℕ) (sY : ∀ x, L x → ℕ)

/-- Double negation elimination for `∀ x, ∃ y, r (x, y)`, a classical derivation from the
hypothesis `¬¬ ∀ x, ∃ y, r (x, y)`. -/
def dneAllEx :
    CDeriv (fun _ : Fin 1 => Form.not (Form.not (Deriv.allEx (X := K) (Y := L) sX sY r)))
      (Deriv.allEx sX sY r) :=
  .raa (.impE (.hyp ⟨1, by omega⟩) (.hyp ⟨0, by omega⟩))

/-- The majorant data of `dneAllEx`: it has no term and no conversion. -/
def dneAllExMajData (R : ℕ → I → Prop) : MajData (dneAllEx r sX sY) R :=
  ((), ())

/-- The negative translation of the hypothesis of `dneAllEx`. -/
local notation "𝒩" => Form.negT (Form.not (Form.not (Deriv.allEx (X := K) (Y := L) sX sY r)))

/-- **Bound extraction for double negation elimination.** For a size `sM` that bounds a multiset
of candidates by every bound on its elements and a selection bounded by `sb`, every `x` has a `y`
with `r (x, y)` whose size is at most the bound computed from the majorant of the hypothesis. -/
theorem dneAllEx_exists_le (sel : ∀ x : Σ i, K i, Multiset (L x) → L x)
    (hsel : ∀ x ys, ((∀ y ∈ ys, ¬ r ⟨x, y⟩) → False) → r ⟨x, sel x ys⟩)
    (sM : ∀ x : Σ i, K i, Multiset (L x) → ℕ)
    (hms : ∀ x (ms : Multiset (L x)) (B : ℕ), (∀ k ∈ ms, sY x k ≤ B) → sM x ms ≤ B)
    (sb : ℕ → ℕ) (hsb : ∀ x (ys : Multiset (L x)) (B : ℕ), sM x ys ≤ B → sY x (sel x ys) ≤ sb B)
    (R : ℕ → I → Prop) (hR : Monotone R)
    (hm : CtxB fun _ : Fin 1 => 𝒩)
    (m₀ : ℕ) (i : I) (hi : R m₀ i)
    (w : (ctx fun _ : Fin 1 => 𝒩).W i)
    (hw : ∀ k, Maj 𝒩 i (hm k) (w k))
    (hmat : ∀ c', (ctx fun _ : Fin 1 => 𝒩).mat i w c')
    (x : K i) :
    ∃ y : L ⟨i, x⟩, sY ⟨i, x⟩ y ≤
        pi2Bound (Deriv.bnd (pi2 r sel hsel sM (dneAllEx r sX sY)) R
          (pi2MajD r sel hsel sM (dneAllEx r sX sY) R (dneAllExMajData r sX sY R)
            (Pi2Maj.ofSize r sel hsel sM hms sb hsb R)) hm m₀).1 (sX i x) ∧ r ⟨⟨i, x⟩, y⟩ :=
  exists_le_extract_pi2Bound' r sel hsel sM _ R hR _ _ hm m₀ i hi w hw hmat x

end Dne

end CDeriv

end CatCrypt.Container.DNLogic
