/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Container.DNLogicMonoClassical

/-!
# The ∃∀ readback of classical derivations: metastability

For a classical derivation of `∀ x, ∃ y, ∀ z, p (x, y, z)`, the Diller–Nahm meaning of the negative
translation is the finite-set form of Kreisel's no-counterexample interpretation. A witness sends
each counterexample function `G`, which gives for every `y` a finite multiset of values `z`, to a
finite multiset of candidates `y`, and one candidate satisfies `p (x, y, z)` for every `z ∈ G y`.

The counterexample function enters the realizer as the witness `CDeriv.metaW` of the premise
`∀ y, ¬ ∀ z, ¬¬ p`. At every `z ∈ G y` that witness demands the counter-witness made of `z` and of
the witness `CDeriv.metaNotW` of `¬ p`, which refutes `p` by demanding it once. The matrix of `¬¬ p`
at that counter-witness then implies `p` classically, whatever the witness of `∀ z, ¬¬ p` is.

The bound comes from `Deriv.bnd_sound`. A majorant `Gs` of `G` in the sense of Howard
(`CDeriv.IsCounterMaj`) gives the majorant `CDeriv.metaMaj` of `CDeriv.metaW`, and the second
component of the bound of the translated derivation at that majorant bounds every candidate
(`CDeriv.metaBound`).

## Main definitions

* `Deriv.allExAll` — the formula `∀ x, ∃ y, ∀ z, p (x, y, z)`;
* `CDeriv.metaCandidates` — the finite multiset of candidates of a witness at `G`;
* `CDeriv.IsCounterMaj` — majorization of a counterexample function;
* `CDeriv.metaBound` — the bound on the candidates, read from a majorant.

## Main results

* `CDeriv.metaCandidates_spec` — some candidate satisfies `p` at every value of `G`;
* `CDeriv.metaCandidates_le` — the bound on the candidates;
* `CDeriv.exAll_candidates`, `CDeriv.exAll_metastable` — the readback of a classical derivation.

## References

* U. Kohlenbach, *Applied Proof Theory: Proof Interpretations and their Use in Mathematics*,
  Springer (2008).
* W. A. Howard, *Hereditarily majorizable functionals of finite type*, LNM 344 (1973).

Search words: metastability, no-counterexample interpretation, Diller–Nahm, negative translation,
monotone functional interpretation, Howard majorant, proof mining, counterexample function.
-/

set_option autoImplicit false

@[expose] public section

universe u

namespace CatCrypt.Container.DNLogic

open DPred Form

variable {I : Type u} {n : ℕ}

variable {K : I → Type u} {L : (Σ i, K i) → Type u} {M : (Σ x : Σ i, K i, L x) → Type u}

namespace Deriv

/-- The formula `∀ x, ∃ y, ∀ z, p (x, y, z)`, with the sizes of the three quantifiers. -/
abbrev allExAll (sX : ∀ i, K i → ℕ) (sY : ∀ x, L x → ℕ) (sZ : ∀ y, M y → ℕ)
    (p : (Σ y : Σ x : Σ i, K i, L x, M y) → Prop) : Form I :=
  .all (K := K) (sz := sX) (.ex (K := L) (sz := sY) (.all (K := M) (sz := sZ) (.atom p)))

end Deriv

namespace CDeriv

section Metastable

variable (sX : ∀ i, K i → ℕ) (sY : ∀ x, L x → ℕ) (sZ : ∀ y, M y → ℕ)
  (p : (Σ y : Σ x : Σ i, K i, L x, M y) → Prop)

/-- The negative translation of `∀ z, p (x, y, z)`. -/
abbrev metaInner : Form (Σ x : Σ i, K i, L x) :=
  Form.all (K := M) (sz := sZ) (Form.not (Form.not (.atom p)))

/-- The formula `∀ y, ¬ ∀ z, ¬¬ p (x, y, z)`, the premise of the negated body of the translation of
`∀ x, ∃ y, ∀ z, p (x, y, z)`. -/
abbrev metaBody : Form (Σ i, K i) :=
  Form.all (K := L) (sz := sY) (Form.not (metaInner sZ p))

/-- The witness of `¬ p` that refutes `p` by demanding it once. -/
def metaNotW (z : Σ y : Σ x : Σ i, K i, L x, M y) : (Form.not (.atom p)).dn.W z :=
  ⟨fun _ => PUnit.unit, fun _ _ => {PUnit.unit}⟩

/-- The witness of `∀ y, ¬ ∀ z, ¬¬ p` given by a counterexample function `G`: at `y` it demands, for
every `z ∈ G y`, the counter-witness made of `z` and the witness `metaNotW` of `¬ p`. -/
def metaW {x : Σ i, K i} (G : ∀ y : L x, Multiset (M ⟨x, y⟩)) : (metaBody sY sZ p).dn.W x :=
  fun y => ⟨fun _ => PUnit.unit, fun _ _ =>
    (G y).map fun z => ⟨z, metaNotW p ⟨⟨x, y⟩, z⟩, PUnit.unit⟩⟩

/-- The majorant of the witness `metaNotW` of `¬ p`. -/
def metaNotMaj : (Form.not (.atom p)).B :=
  (fun _ => (), fun _ _ => [()])

/-- The majorant of `metaW` given by a majorant `Gs` of the counterexample function. -/
def metaMaj (Gs : ℕ → List ℕ) : (metaBody sY sZ p).B :=
  fun j => (fun _ => (), fun _ _ => (Gs j).map fun b => (b, metaNotMaj p, ()))

/-- Majorization of a counterexample function, in the sense of Howard: at every bound `j` on the
size of `y`, each value of `G y` has size at most an element of the list `Gs j`. -/
def IsCounterMaj {x : Σ i, K i} (G : ∀ y : L x, Multiset (M ⟨x, y⟩)) (Gs : ℕ → List ℕ) : Prop :=
  ∀ y j, sY x y ≤ j → ∀ z ∈ G y, ∃ b ∈ Gs j, sZ ⟨x, y⟩ z ≤ b

/-- The bound on the candidates read from a majorant `b` of the translated formula, at a bound `k`
on the size of `x` and a majorant `Gs` of the counterexample function: the maximum of the first
components of the counter-witness majorants that `b k` demands at `metaMaj Gs`. -/
def metaBound (b : (Deriv.allExAll sX sY sZ p).negT.B) (k : ℕ) (Gs : ℕ → List ℕ) : ℕ :=
  ((((b k).2 (metaMaj sY sZ p Gs) ()).map Prod.fst : List ℕ) : Multiset ℕ).sup

/-- The finite multiset of candidates that a witness of the translated formula gives at `x` and at
a counterexample function `G`. -/
def metaCandidates {i : I} (w : (Deriv.allExAll sX sY sZ p).negT.dn.W i) (x : K i)
    (G : ∀ y : L ⟨i, x⟩, Multiset (M ⟨⟨i, x⟩, y⟩)) : Multiset (L ⟨i, x⟩) :=
  ((w x).2 (metaW sY sZ p G) PUnit.unit).map Sigma.fst

/-- **The readback of the matrix.** A witness of the translated formula that withstands every
counter-witness has, at every counterexample function, a candidate that satisfies `p` at each value
of the counterexample function. -/
theorem metaCandidates_spec {i : I} (w : (Deriv.allExAll sX sY sZ p).negT.dn.W i)
    (hw : ∀ c, (Deriv.allExAll sX sY sZ p).negT.dn.mat i w c) (x : K i)
    (G : ∀ y : L ⟨i, x⟩, Multiset (M ⟨⟨i, x⟩, y⟩)) :
    ∃ y ∈ metaCandidates sX sY sZ p w x G, ∀ z ∈ G y, p ⟨⟨⟨i, x⟩, y⟩, z⟩ := by
  by_contra hno
  refine hw ⟨x, metaW sY sZ p G, PUnit.unit⟩ fun c hc hx => hno ?_
  refine ⟨c.1, Multiset.mem_map_of_mem Sigma.fst hc, fun z hz => ?_⟩
  by_contra hnp
  have hm : (⟨z, metaNotW p ⟨⟨⟨i, x⟩, c.1⟩, z⟩, PUnit.unit⟩ :
      (metaInner sZ p).dn.C ⟨⟨i, x⟩, c.1⟩ c.2.1) ∈
      (metaW sY sZ p G c.1).2 c.2.1 c.2.2 :=
    Multiset.mem_map_of_mem _ hz
  exact hx _ hm fun _ _ h => hnp (h PUnit.unit (Multiset.mem_singleton_self _))

/-- The majorant `metaMaj` of a majorant of a counterexample function majorizes `metaW`. -/
theorem maj_metaW {x : Σ i, K i} {G : ∀ y : L x, Multiset (M ⟨x, y⟩)} {Gs : ℕ → List ℕ}
    (hG : IsCounterMaj sY sZ G Gs) :
    Maj (metaBody sY sZ p) x (metaMaj sY sZ p Gs) (metaW sY sZ p G) := by
  intro y j hj v bv _
  refine ⟨trivial, fun _ _ _ c hc => ?_⟩
  obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hc
  obtain ⟨b, hb, hle⟩ := hG y j hj z hz
  exact ⟨(b, metaNotMaj p, ()), List.mem_map_of_mem hb,
    hle, fun _ _ _ => ⟨trivial, fun _ _ _ _ _ => ⟨(), List.mem_singleton_self _, trivial⟩⟩, trivial⟩

/-- **The bound on the candidates.** A majorant of a witness of the translated formula bounds each
candidate of the witness at a counterexample function by `metaBound` at a majorant of it. -/
theorem metaCandidates_le {i : I} {b : (Deriv.allExAll sX sY sZ p).negT.B}
    {w : (Deriv.allExAll sX sY sZ p).negT.dn.W i}
    (hb : Maj (Deriv.allExAll sX sY sZ p).negT i b w) {x : K i} {k : ℕ} (hk : sX i x ≤ k)
    {G : ∀ y : L ⟨i, x⟩, Multiset (M ⟨⟨i, x⟩, y⟩)} {Gs : ℕ → List ℕ}
    (hG : IsCounterMaj sY sZ G Gs) {y : L ⟨i, x⟩}
    (hy : y ∈ metaCandidates sX sY sZ p w x G) :
    sY ⟨i, x⟩ y ≤ metaBound sX sY sZ p b k Gs := by
  obtain ⟨c, hc, rfl⟩ := Multiset.mem_map.1 hy
  obtain ⟨b', hb', hle⟩ :=
    (hb x k hk (metaW sY sZ p G) (metaMaj sY sZ p Gs) (maj_metaW sY sZ p hG)).2 () PUnit.unit
      trivial c hc
  exact hle.1.trans (Multiset.le_sup (Multiset.mem_coe.2 (List.mem_map_of_mem hb')))

/-- **The ∃∀ readback, with the candidates.** For a classical derivation of
`∀ x, ∃ y, ∀ z, p (x, y, z)`, the realizer of its translation gives at every counterexample function
`G` a finite multiset of candidates. Each candidate is bounded by the second component of the bound
of the translated derivation at a majorant of `G`, and some candidate satisfies `p` at every value
of `G`. -/
theorem exAll_candidates {Γ : Fin n → Form I} (c : CDeriv Γ (Deriv.allExAll sX sY sZ p))
    (R : ℕ → I → Prop) (hR : Monotone R) (D : MajData c R) (hm : CtxB fun k => (Γ k).negT)
    (m₀ : ℕ) (i : I) (hi : R m₀ i) (w : (ctx fun k => (Γ k).negT).W i)
    (hw : ∀ k, Maj (Γ k).negT i (hm k) (w k))
    (hmat : ∀ c', (ctx fun k => (Γ k).negT).mat i w c') (x : K i) (k : ℕ) (hk : sX i x ≤ k)
    (G : ∀ y : L ⟨i, x⟩, Multiset (M ⟨⟨i, x⟩, y⟩)) (Gs : ℕ → List ℕ)
    (hG : IsCounterMaj sY sZ G Gs) :
    (∀ y ∈ metaCandidates sX sY sZ p (c.translate.realize.fwd i w) x G,
      sY ⟨i, x⟩ y ≤
        metaBound sX sY sZ p (Deriv.bnd c.translate R (translateMajD c R D) hm m₀).1 k Gs) ∧
    ∃ y ∈ metaCandidates sX sY sZ p (c.translate.realize.fwd i w) x G,
      ∀ z ∈ G y, p ⟨⟨⟨i, x⟩, y⟩, z⟩ :=
  ⟨fun _ hy => metaCandidates_le sX sY sZ p
      (Deriv.bnd_sound c.translate R hR (translateMajD c R D) hm m₀ i hi w hw).1 hk hG hy,
    metaCandidates_spec sX sY sZ p _
      (fun c' => c.translate.realize.sound i w c' fun y _ => hmat y) x G⟩

/-- **Metastability from a classical derivation.** For a classical derivation of
`∀ x, ∃ y, ∀ z, p (x, y, z)`, every counterexample function `G` has a `y` that satisfies `p` at each
value of `G y`, of size at most the second component of the bound of the translated derivation at a
majorant of `G`. -/
theorem exAll_metastable {Γ : Fin n → Form I} (c : CDeriv Γ (Deriv.allExAll sX sY sZ p))
    (R : ℕ → I → Prop) (hR : Monotone R) (D : MajData c R) (hm : CtxB fun k => (Γ k).negT)
    (m₀ : ℕ) (i : I) (hi : R m₀ i) (w : (ctx fun k => (Γ k).negT).W i)
    (hw : ∀ k, Maj (Γ k).negT i (hm k) (w k))
    (hmat : ∀ c', (ctx fun k => (Γ k).negT).mat i w c') (x : K i) (k : ℕ) (hk : sX i x ≤ k)
    (G : ∀ y : L ⟨i, x⟩, Multiset (M ⟨⟨i, x⟩, y⟩)) (Gs : ℕ → List ℕ)
    (hG : IsCounterMaj sY sZ G Gs) :
    ∃ y : L ⟨i, x⟩, sY ⟨i, x⟩ y ≤
        metaBound sX sY sZ p (Deriv.bnd c.translate R (translateMajD c R D) hm m₀).1 k Gs ∧
      ∀ z ∈ G y, p ⟨⟨⟨i, x⟩, y⟩, z⟩ := by
  obtain ⟨hle, y, hy, hp⟩ :=
    exAll_candidates sX sY sZ p c R hR D hm m₀ i hi w hw hmat x k hk G Gs hG
  exact ⟨y, hle y hy, hp⟩

end Metastable

end CDeriv

end CatCrypt.Container.DNLogic
