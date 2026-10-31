/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.FiatShamirROM.Game
public import CatCryptCore.ForMathlib.PMFUniform

/-!
# OR composition of Σ-protocols

The OR composition of Cramer, Damgård and Schoenmakers of two Σ-protocols `P₀` and `P₁`
whose challenge spaces are identified by an equivalence `e : P₀.Ch ≃ P₁.Ch`, with `P₀.Ch` an
additive group. A statement is a pair `(x₀, x₁)` and a witness is a witness for one of the
two. The prover runs the honest protocol on the branch of its witness and the simulator on
the other branch with a uniform challenge `cs`; on the master challenge `c` the challenge of
the honest branch is the remainder: `c − cs` on branch 0, `e (c − cs)` on branch 1. A
response `(c₀, z₀, z₁)` carries the challenge `c₀` of branch 0; the challenge of branch 1 is
`e (c − c₀)`. The simulator runs both simulators with a uniform `c₀`.

## Main definitions

* `Sigma.SimVerifies` — every simulated transcript verifies, for every statement
* `Sigma.RelHVZK` — honest and simulated transcripts have the same distribution at every
  pair of the relation
* `orRel`, `orSigma` — the OR relation and the OR Σ-protocol

## Main statements

* `orSigma_complete` — completeness, from completeness and `SimVerifies` of both branches
* `orSigma_specialSound` — special soundness, from special soundness of both branches
* `orSigma_relHVZK`, `orSigma_perfectHVZK` — honest-verifier zero knowledge, from
  `RelHVZK` of both branches
* `PMF.map_uniform_prod_pair_congr`, `PMF.map_uniform_prod_dep_congr` — the uniform-product
  identities behind the zero-knowledge proof

## References

* R. Cramer, I. Damgård, B. Schoenmakers, *Proofs of partial knowledge and simplified design
  of witness hiding protocols*, CRYPTO 1994.
-/

@[expose] public section

set_option autoImplicit false

namespace PMF

variable {A A' B B' C β : Type} [Fintype A] [Nonempty A] [Fintype A'] [Nonempty A']
  [Fintype B] [Nonempty B] [Fintype B'] [Nonempty B'] [Fintype C] [Nonempty C]

/-- A function of the first component of a uniform pair has the distribution of that function
of a uniform first component. -/
theorem map_uniform_prod_fst (f : A → β) :
    (PMF.uniformFintype (A × B)).map (fun p => f p.1) = (PMF.uniformFintype A).map f := by
  rw [← map_uniform_fst (A := A) (B := B), PMF.map_comp]
  rfl

/-- A function of the second component of a uniform pair has the distribution of that function
of a uniform second component. -/
theorem map_uniform_prod_snd (g : B → β) :
    (PMF.uniformFintype (A × B)).map (fun p => g p.2) = (PMF.uniformFintype B).map g := by
  rw [← uniformFintype_map_equiv (Equiv.prodComm B A), PMF.map_comp]
  exact map_uniform_prod_fst g

/-- Maps of the two components of a uniform pair with equal image distributions give equal
distributions of the pair of images. -/
theorem map_uniform_prod_pair_congr {X Y : Type} {f : A → X} {f' : A' → X} {g : B → Y}
    {g' : B' → Y} (hf : (PMF.uniformFintype A).map f = (PMF.uniformFintype A').map f')
    (hg : (PMF.uniformFintype B).map g = (PMF.uniformFintype B').map g') :
    (PMF.uniformFintype (A × B)).map (fun p => (f p.1, g p.2)) =
      (PMF.uniformFintype (A' × B')).map (fun p => (f' p.1, g' p.2)) := by
  have key : ∀ {A₁ B₁ : Type} [Fintype A₁] [Nonempty A₁] [Fintype B₁] [Nonempty B₁]
      (f₁ : A₁ → X) (g₁ : B₁ → Y),
      (PMF.uniformFintype (A₁ × B₁)).map (fun p => (f₁ p.1, g₁ p.2)) =
        ((PMF.uniformFintype A₁).map f₁).bind fun x =>
          ((PMF.uniformFintype B₁).map g₁).map (Prod.mk x) := by
    intro A₁ B₁ _ _ _ _ f₁ g₁
    rw [uniform_prod_eq_bind, PMF.map_bind, PMF.bind_map]
    refine congrArg _ (funext fun a => ?_)
    simp only [Function.comp_apply, PMF.map_comp]
    rfl
  rw [key, key, hf, hg]

/-- A function of a uniform `c` and of a map at `c` of an independent uniform `a` keeps its
distribution when, for every `c`, the map is replaced by one with the same image
distribution. -/
theorem map_uniform_prod_dep_congr {X : Type} (Φ : C → X → β) {f : C → A → X}
    {f' : C → A' → X}
    (hf : ∀ c, (PMF.uniformFintype A).map (f c) = (PMF.uniformFintype A').map (f' c)) :
    (PMF.uniformFintype (C × A)).map (fun p => Φ p.1 (f p.1 p.2)) =
      (PMF.uniformFintype (C × A')).map (fun p => Φ p.1 (f' p.1 p.2)) := by
  rw [uniform_prod_eq_bind, uniform_prod_eq_bind, PMF.map_bind, PMF.map_bind]
  refine congrArg _ (funext fun c => ?_)
  have h : ∀ {A₁ : Type} [Fintype A₁] [Nonempty A₁] (f₁ : C → A₁ → X),
      ((PMF.uniformFintype A₁).map (Prod.mk c)).map (fun p => Φ p.1 (f₁ p.1 p.2)) =
        ((PMF.uniformFintype A₁).map (f₁ c)).map (Φ c) := by
    intro A₁ _ _ f₁
    rw [PMF.map_comp, PMF.map_comp]
    rfl
  rw [h, h, hf]

end PMF

namespace CatCrypt.Crypto.FiatShamirROM

namespace Sigma

variable (P : Sigma)

/-- **Simulator acceptance.** Every simulated transcript verifies, for every statement and
challenge. -/
def SimVerifies : Prop :=
  ∀ x e s, P.verify x (P.simulate x e s).1 e (P.simulate x e s).2 = true

/-- **Honest-verifier zero knowledge on the relation.** At every pair `(x, w)` of the relation
and every challenge `e`, the honest commitment and response on uniform randomness have the
distribution of the simulator output on uniform simulator randomness. -/
def RelHVZK : Prop :=
  ∀ x w, P.rel x w → ∀ e,
    (PMF.uniformFintype P.Rand).map (fun r => (P.commit x w r, P.respond x w r e)) =
      (PMF.uniformFintype P.SimRand).map (P.simulate x e)

/-- `RelHVZK` gives perfect HVZK for a generator supported on the relation. -/
theorem RelHVZK.perfectHVZK {P : Sigma} (h : P.RelHVZK)
    (hgen : ∀ x w, (x, w) ∈ P.gen.support → P.rel x w) : P.PerfectHVZK :=
  fun x w hxw e => h x w (hgen x w hxw) e

end Sigma

section Or

variable (P₀ P₁ : Sigma) [AddCommGroup P₀.Ch] (e : P₀.Ch ≃ P₁.Ch)
  (gen : PMF ((P₀.Stmt × P₁.Stmt) × (P₀.Wit ⊕ P₁.Wit)))

/-- The OR relation: a witness for `(x₀, x₁)` is a witness for `x₀` or a witness for `x₁`. -/
def orRel (s : P₀.Stmt × P₁.Stmt) : P₀.Wit ⊕ P₁.Wit → Prop :=
  Sum.elim (P₀.rel s.1) (P₁.rel s.2)

instance (s : P₀.Stmt × P₁.Stmt) (w : P₀.Wit ⊕ P₁.Wit) : Decidable (orRel P₀ P₁ s w) :=
  match w with
  | .inl w₀ => inferInstanceAs (Decidable (P₀.rel s.1 w₀))
  | .inr w₁ => inferInstanceAs (Decidable (P₁.rel s.2 w₁))

/-- The OR Σ-protocol of `P₀` and `P₁` with challenge identification `e` and generator `gen`.
The prover randomness is `(cs, (r₀, s₁), (s₀, r₁))`: the simulated challenge, the randomness of
the honest branch 0 and of the simulated branch 1, and those of the simulated branch 0 and of
the honest branch 1. -/
noncomputable def orSigma : Sigma where
  Stmt := P₀.Stmt × P₁.Stmt
  Wit := P₀.Wit ⊕ P₁.Wit
  Com := P₀.Com × P₁.Com
  Ch := P₀.Ch
  Resp := P₀.Ch × P₀.Resp × P₁.Resp
  Rand := P₀.Ch × (P₀.Rand × P₁.SimRand) × (P₀.SimRand × P₁.Rand)
  SimRand := P₀.Ch × P₀.SimRand × P₁.SimRand
  inhWit := ⟨.inl default⟩
  rel := orRel P₀ P₁
  gen := gen
  commit s w r := match w with
    | .inl w₀ => (P₀.commit s.1 w₀ r.2.1.1, (P₁.simulate s.2 (e r.1) r.2.1.2).1)
    | .inr w₁ => ((P₀.simulate s.1 r.1 r.2.2.1).1, P₁.commit s.2 w₁ r.2.2.2)
  respond s w r c := match w with
    | .inl w₀ =>
      (c - r.1, P₀.respond s.1 w₀ r.2.1.1 (c - r.1), (P₁.simulate s.2 (e r.1) r.2.1.2).2)
    | .inr w₁ => (r.1, (P₀.simulate s.1 r.1 r.2.2.1).2, P₁.respond s.2 w₁ r.2.2.2 (e (c - r.1)))
  verify s a c z := P₀.verify s.1 a.1 z.1 z.2.1 && P₁.verify s.2 a.2 (e (c - z.1)) z.2.2
  simulate s c σ :=
    (((P₀.simulate s.1 σ.1 σ.2.1).1, (P₁.simulate s.2 (e (c - σ.1)) σ.2.2).1),
      (σ.1, (P₀.simulate s.1 σ.1 σ.2.1).2, (P₁.simulate s.2 (e (c - σ.1)) σ.2.2).2))
  extract s a c z c' z' :=
    if z.1 = z'.1 then .inr (P₁.extract s.2 a.2 (e (c - z.1)) z.2.2 (e (c' - z'.1)) z'.2.2)
    else .inl (P₀.extract s.1 a.1 z.1 z.2.1 z'.1 z'.2.1)

variable {P₀ P₁}

/-- **Completeness of the OR composition.** -/
theorem orSigma_complete (h₀ : P₀.Complete) (h₁ : P₁.Complete) (hs₀ : P₀.SimVerifies)
    (hs₁ : P₁.SimVerifies) : (orSigma P₀ P₁ e gen).Complete := by
  rintro ⟨x₀, x₁⟩ (w₀ | w₁) hw r c
  · change P₀.Ch at c
    simp only [orSigma, Bool.and_eq_true]
    refine ⟨h₀ x₀ w₀ hw _ _, ?_⟩
    rw [sub_sub_cancel c r.1]
    exact hs₁ _ _ _
  · simp only [orSigma, Bool.and_eq_true]
    exact ⟨hs₀ _ _ _, h₁ x₁ w₁ hw _ _⟩

/-- **Special soundness of the OR composition.** Two accepting transcripts with distinct master
challenges differ in the challenge of branch 0 or in that of branch 1, and the extractor of
that branch gives its witness. -/
theorem orSigma_specialSound (h₀ : P₀.SpecialSound) (h₁ : P₁.SpecialSound) :
    (orSigma P₀ P₁ e gen).SpecialSound := by
  rintro ⟨x₀, x₁⟩ ⟨a₀, a₁⟩ c ⟨c₀, z₀, z₁⟩ c' ⟨c₀', z₀', z₁'⟩ hv hv' hne
  change P₀.Ch at c c'
  simp only [orSigma, Bool.and_eq_true] at hv hv'
  by_cases hc : c₀ = c₀'
  · subst hc
    have hne₁ : e (c - c₀) ≠ e (c' - c₀) := fun h =>
      hne (sub_left_injective (G := P₀.Ch) (b := c₀) (e.injective h))
    simp only [orSigma, ↓reduceIte]
    exact h₁ x₁ a₁ _ z₁ _ z₁' hv.2 hv'.2 hne₁
  · simp only [orSigma, hc, ↓reduceIte]
    exact h₀ x₀ a₀ c₀ z₀ c₀' z₀' hv.1 hv'.1 hc

/-- **Honest-verifier zero knowledge of the OR composition.** At every pair of the OR relation,
honest and simulated transcripts have the same distribution. -/
theorem orSigma_relHVZK (h₀ : P₀.RelHVZK) (h₁ : P₁.RelHVZK) :
    (orSigma P₀ P₁ e gen).RelHVZK := by
  let Φ (c₀ : P₀.Ch) (t : (P₀.Com × P₀.Resp) × (P₁.Com × P₁.Resp)) :
      (orSigma P₀ P₁ e gen).Com × (orSigma P₀ P₁ e gen).Resp :=
    ((t.1.1, t.2.1), (c₀, t.1.2, t.2.2))
  rintro ⟨x₀, x₁⟩ (w₀ | w₁) hw c
  · change P₀.Ch at c
    have hL := PMF.map_uniform_prod_dep_congr Φ
      (A := (P₀.Rand × P₁.SimRand) × (P₀.SimRand × P₁.Rand))
      (A' := P₀.SimRand × P₁.SimRand)
      (f := fun c₀ t => ((P₀.commit x₀ w₀ t.1.1, P₀.respond x₀ w₀ t.1.1 c₀),
        P₁.simulate x₁ (e (c - c₀)) t.1.2))
      (f' := fun c₀ σ => (P₀.simulate x₀ c₀ σ.1, P₁.simulate x₁ (e (c - c₀)) σ.2))
      (fun c₀ => (PMF.map_uniform_prod_fst (B := P₀.SimRand × P₁.Rand)
        (fun t : P₀.Rand × P₁.SimRand => ((P₀.commit x₀ w₀ t.1, P₀.respond x₀ w₀ t.1 c₀),
          P₁.simulate x₁ (e (c - c₀)) t.2))).trans
        (PMF.map_uniform_prod_pair_congr (h₀ x₀ w₀ hw c₀) rfl))
    refine Eq.trans ?_ hL
    rw [← PMF.uniformFintype_map_equiv ((Equiv.subLeft c).prodCongr
      (Equiv.refl ((P₀.Rand × P₁.SimRand) × (P₀.SimRand × P₁.Rand)))), PMF.map_comp]
    congr 1
    funext ρ
    obtain ⟨cs, ⟨r₀, s₁⟩, t⟩ := ρ
    change ((P₀.commit x₀ w₀ r₀, (P₁.simulate x₁ (e cs) s₁).1),
        (c - cs, P₀.respond x₀ w₀ r₀ (c - cs), (P₁.simulate x₁ (e cs) s₁).2)) =
      ((P₀.commit x₀ w₀ r₀, (P₁.simulate x₁ (e (c - (c - cs))) s₁).1),
        (c - cs, P₀.respond x₀ w₀ r₀ (c - cs), (P₁.simulate x₁ (e (c - (c - cs))) s₁).2))
    rw [sub_sub_cancel]
  · change P₀.Ch at c
    exact PMF.map_uniform_prod_dep_congr Φ
      (A := (P₀.Rand × P₁.SimRand) × (P₀.SimRand × P₁.Rand))
      (A' := P₀.SimRand × P₁.SimRand)
      (f := fun c₀ t => (P₀.simulate x₀ c₀ t.2.1,
        (P₁.commit x₁ w₁ t.2.2, P₁.respond x₁ w₁ t.2.2 (e (c - c₀)))))
      (f' := fun c₀ σ => (P₀.simulate x₀ c₀ σ.1, P₁.simulate x₁ (e (c - c₀)) σ.2))
      (fun c₀ => (PMF.map_uniform_prod_snd (A := P₀.Rand × P₁.SimRand)
        (fun t : P₀.SimRand × P₁.Rand => (P₀.simulate x₀ c₀ t.1,
          (P₁.commit x₁ w₁ t.2, P₁.respond x₁ w₁ t.2 (e (c - c₀)))))).trans
        (PMF.map_uniform_prod_pair_congr rfl (h₁ x₁ w₁ hw (e (c - c₀)))))

/-- **Perfect honest-verifier zero knowledge of the OR composition**, for a generator supported
on the OR relation. -/
theorem orSigma_perfectHVZK (h₀ : P₀.RelHVZK) (h₁ : P₁.RelHVZK)
    (hgen : ∀ s w, (s, w) ∈ gen.support → orRel P₀ P₁ s w) :
    (orSigma P₀ P₁ e gen).PerfectHVZK :=
  (orSigma_relHVZK e gen h₀ h₁).perfectHVZK hgen

end Or

end CatCrypt.Crypto.FiatShamirROM
