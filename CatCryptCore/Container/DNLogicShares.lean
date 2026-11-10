/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Container.DNLogic
public import CatCryptCore.ForMathlib.LagrangeAtZero

/-!
# Extraction from finitely many answers in Diller–Nahm logic

An extractor that consults a party, a prover or an adversary at finitely many points and decodes
the answers is a derivation of positive many-sorted logic (`Container/DNLogic.lean`) from the
hypothesis `∀ x, ∃ y, a (x, y)` (the party answers every point correctly) to the conclusion
`∃ z, R z`. The derivation `Decode.extract` chooses the answer function by the axiom of choice,
eliminates the existential, and closes with a realized axiom that decodes the chosen function
from its values at an enumeration `e` of at most `N` points. Its use count of the hypothesis is
`N` (`Decode.extract_useCount`), so the program of the derivation consults the party at most `N`
times (`Deriv.queries_card_le`), and its answer satisfies `R` whenever the party answers
correctly at the queries (`Deriv.query_sound`).

Three extractors are instances:

* threshold reconstruction of Shamir secret sharing: from the shares of the parties of a set `s`
  of size `t`, the secret is the Lagrange combination of the shares at `0`; `t` queries;
* MPC-in-the-head and cut-and-choose: from consistent openings of the views indexed by a finite
  type `J`, a decoding function computes the witness; `#J` queries (`3` for ZKB++);
* rewinding: an extractor that runs an adversary on `#J` challenges and combines its responses;
  the number of rewinds is the use count of the adversary hypothesis.

## Main definitions

* `Decode.extract` — the extraction derivation from a decoding function;
* `thresholdDeriv` — threshold reconstruction by Lagrange interpolation at `0`;
* `viewDeriv` — witness extraction from consistent views;
* `rewindDeriv` — witness extraction by rewinding at finitely many challenges.

## Main results

* `Decode.extract_useCount`, `Decode.extract_program`, `Decode.extract_sound` — the use count,
  the realizer and its correctness;
* `threshold_useCount`, `threshold_queries_card_le`, `threshold_reconstruct` — the secret is
  computed from at most `t` shares;
* `viewDeriv_useCount`, `viewDeriv_queries_card_le`, `viewDeriv_useCount_fin_three`;
* `rewindDeriv_useCount`, `rewindDeriv_queries_card_le`.

## References

* A. Shamir, *How to share a secret*, Communications of the ACM 22 (1979).
* Y. Ishai, E. Kushilevitz, R. Ostrovsky, A. Sahai, *Zero-knowledge from secure multiparty
  computation*, STOC 2007.
* M. Chase et al., *Post-quantum zero-knowledge and signatures from symmetric-key primitives*
  (ZKB++), CCS 2017.
* J. Diller, W. Nahm, *Eine Variante zur Dialectica-Interpretation der Heyting-Arithmetik
  endlicher Typen*, Archiv für mathematische Logik 16 (1974).

Search words: threshold reconstruction, Shamir, Lagrange interpolation, MPC-in-the-head,
cut-and-choose, view extraction, rewinding, forking, query bound, use count.
-/

set_option autoImplicit false

@[expose] public section

universe u

namespace CatCrypt.Container.DNLogic

open DPred

namespace Decode

variable {I : Type u} {X : I → Type u} {Y : (Σ i, X i) → Type u} {Wt : I → Type u}

/-- The body of the choice formula: the chosen function answers every point correctly. -/
abbrev choiceBody (a : (Σ x : Σ i, X i, Y x) → Prop) : Form (Σ i, ∀ k : X i, Y ⟨i, k⟩) :=
  .all (K := fun p => X p.1) (sz := 0) ((Form.atom a).sub fun y => ⟨⟨y.1.1, y.2⟩, y.1.2 y.2⟩)

/-- The formula `∃ z, R (i, z)`. -/
abbrev exAtom (R : (Σ i, Wt i) → Prop) : Form I := .ex (K := Wt) (sz := 0) (.atom R)

/-- The formula `∀ _ : PUnit, ∃ z, R (i, z)`, the oracle form of `Deriv.program`. -/
abbrev allExUnit (R : (Σ i, Wt i) → Prop) : Form I :=
  Deriv.allEx (X := fun _ => PUnit.{u + 1}) (Y := fun x => Wt x.1) 0 0 fun y => R ⟨y.1.1, y.2⟩

/-- Decoding as a realized axiom: the decoded value `D i g` from a chosen function `g`, which
demands the counter-witnesses at the points of `e i`. -/
def decodeHom (a : (Σ x : Σ i, X i, Y x) → Prop) (R : (Σ i, Wt i) → Prop)
    (e : ∀ i, Multiset (X i)) (D : ∀ i, (∀ k : X i, Y ⟨i, k⟩) → Wt i)
    (hD : ∀ i g, (∀ k ∈ e i, a ⟨⟨i, k⟩, g k⟩) → R ⟨i, D i g⟩) :
    (choiceBody a).dn.Hom ((exAtom R).sub Sigma.fst).dn where
  fwd q _ := (⟨D q.1 q.2, PUnit.unit⟩ : Σ _ : Wt q.1, PUnit.{u + 1})
  back q _ _ := (e q.1).map fun k => (⟨k, PUnit.unit⟩ : Σ _ : X q.1, PUnit.{u + 1})
  sound q _ _ h := hD q.1 q.2 fun k hk => h ⟨k, PUnit.unit⟩ (Multiset.mem_map_of_mem _ hk)

/-- The entailment from `∃ z, R` to its oracle form `∀ _ : PUnit, ∃ z, R`. -/
def exToAll (R : (Σ i, Wt i) → Prop) : (exAtom R).dn.Hom (allExUnit R).dn where
  fwd _ w := fun _ => (w : Σ _ : Wt _, PUnit.{u + 1})
  back _ _ _ := {PUnit.unit}
  sound _ _ _ h := h PUnit.unit (Multiset.mem_singleton_self _)

/-- Decoding preserves truth. -/
theorem decode_eval (a : (Σ x : Σ i, X i, Y x) → Prop) (R : (Σ i, Wt i) → Prop)
    (e : ∀ i, Multiset (X i)) (D : ∀ i, (∀ k : X i, Y ⟨i, k⟩) → Wt i)
    (hD : ∀ i g, (∀ k ∈ e i, a ⟨⟨i, k⟩, g k⟩) → R ⟨i, D i g⟩) (q : Σ i, ∀ k : X i, Y ⟨i, k⟩) :
    (choiceBody a).eval q → ((exAtom R).sub Sigma.fst).eval q :=
  fun h => ⟨D q.1 q.2, hD q.1 q.2 fun k _ => h k⟩

/-- `∃ z, R` entails its oracle form in truth. -/
theorem exToAll_eval (R : (Σ i, Wt i) → Prop) (i : I) :
    (exAtom R).eval i → (allExUnit R).eval i :=
  fun h _ => h

/-- **Extraction.** The derivation of `∃ z, R` from `∀ x, ∃ y, a (x, y)`: choose the answer
function, eliminate it, and decode it from its values at the `≤ N` points of `e`. -/
def extract (a : (Σ x : Σ i, X i, Y x) → Prop) (R : (Σ i, Wt i) → Prop)
    (e : ∀ i, Multiset (X i)) (N : ℕ) (hN : ∀ i, (e i).card ≤ N)
    (D : ∀ i, (∀ k : X i, Y ⟨i, k⟩) → Wt i)
    (hD : ∀ i g, (∀ k ∈ e i, a ⟨⟨i, k⟩, g k⟩) → R ⟨i, D i g⟩) :
    Deriv (fun _ : Fin 1 => Deriv.allEx 0 0 a) (allExUnit R) :=
  .hom (exToAll R) 1 (fun _ _ _ => le_of_eq (Multiset.card_singleton _)) (exToAll_eval R)
    (.exE (.ac (sF := 0) (φ := .atom a) (.hyp 0))
      (.hom (decodeHom a R e D hD) N (fun q _ _ => (Multiset.card_map _ _).trans_le (hN q.1))
        (decode_eval a R e D hD)
        (.hyp (Γ := consF (choiceBody a) _) ⟨0, Nat.zero_lt_succ 1⟩)))

variable (a : (Σ x : Σ i, X i, Y x) → Prop) (R : (Σ i, Wt i) → Prop)
  (e : ∀ i, Multiset (X i)) (N : ℕ) (hN : ∀ i, (e i).card ≤ N)
  (D : ∀ i, (∀ k : X i, Y ⟨i, k⟩) → Wt i)
  (hD : ∀ i g, (∀ k ∈ e i, a ⟨⟨i, k⟩, g k⟩) → R ⟨i, D i g⟩)

/-- The extraction derivation uses the hypothesis `N` times. -/
theorem extract_useCount : (extract a R e N hN D hD).useCount 0 = N := by
  simp only [extract, Deriv.useCount, Deriv.uses]
  simp

/-- Computation of the realizer of `extract`: it decodes the answer function of the oracle. -/
theorem extract_program (g : ∀ i (x : X i), Y ⟨i, x⟩) (i : I) :
    (extract a R e N hN D hD).program g i PUnit.unit = D i (g i) := rfl

/-- The extraction program consults the oracle at most `N` times. -/
theorem extract_queries_card_le (g : ∀ i (x : X i), Y ⟨i, x⟩) (i : I) :
    ((((extract a R e N hN D hD).queries g i PUnit.unit).card : ℕ) : ℕ∞) ≤ N :=
  (Deriv.queries_card_le _ g i PUnit.unit).trans_eq (extract_useCount a R e N hN D hD)

/-- **Correctness of extraction.** The decoded value satisfies `R` whenever the oracle answers
correctly at the queries of the program. -/
theorem extract_sound (g : ∀ i (x : X i), Y ⟨i, x⟩) (i : I)
    (h : ∀ x ∈ (extract a R e N hN D hD).queries g i PUnit.unit, a ⟨⟨i, x⟩, g i x⟩) :
    R ⟨i, D i (g i)⟩ :=
  Deriv.query_sound (extract a R e N hN D hD) g i PUnit.unit h

end Decode

/-! ## Threshold reconstruction -/

section Threshold

variable {F ι : Type} [Field F] [DecidableEq ι] (s : Finset ι) (x : ι → F)

/-- Dealer polynomials of degree less than the size of the reconstruction set `s`. -/
abbrev DealerPoly : Type := {f : Polynomial F // f.degree < s.card}

/-- The share of party `p` is the dealer polynomial at its node `x p`. -/
def shareRel : (Σ _ : Σ _ : DealerPoly (F := F) s, ↥s, F) → Prop :=
  fun y => y.2 = y.1.1.1.eval (x y.1.2)

/-- The secret is the dealer polynomial at `0`. -/
def secretRel : (Σ _ : DealerPoly (F := F) s, F) → Prop :=
  fun z => z.2 = z.1.1.eval 0

/-- Lagrange reconstruction at `0` from the shares of the parties of `s`. -/
noncomputable def lagrangeDecode (g : ∀ _ : ↥s, F) : F :=
  ∑ p : ↥s, Lagrange.lagrangeAt0 s x p * g p

/-- Lagrange reconstruction returns the secret from correct shares. -/
theorem lagrangeDecode_eq (hx : Set.InjOn x s) (f : DealerPoly (F := F) s) (g : ∀ _ : ↥s, F)
    (hg : ∀ p : ↥s, g p = f.1.eval (x p)) : lagrangeDecode s x g = f.1.eval 0 := by
  simp only [lagrangeDecode, hg]
  rw [Finset.sum_coe_sort s fun i => Lagrange.lagrangeAt0 s x i * f.1.eval (x i)]
  exact Lagrange.sum_lagrangeAt0_mul_eval hx f.1 f.2

/-- **Threshold reconstruction** as a derivation from the hypothesis that every party of `s`
gives its share: the realizer computes the secret by Lagrange interpolation at `0`. -/
noncomputable def thresholdDeriv (hx : Set.InjOn x s) :
    Deriv (fun _ : Fin 1 => Deriv.allEx (X := fun _ => ↥s) (Y := fun _ => F) 0 0 (shareRel s x))
      (Decode.allExUnit (Wt := fun _ => F) (secretRel s)) :=
  Decode.extract (X := fun _ => ↥s) (Y := fun _ => F) (Wt := fun _ => F) (shareRel s x)
    (secretRel s) (fun _ => Finset.univ.val) s.card
    (fun _ => le_of_eq (by rw [Finset.card_val, Finset.card_univ, Fintype.card_coe]))
    (fun _ => lagrangeDecode s x)
    (fun f g hg => lagrangeDecode_eq s x hx f g fun p => hg p (Finset.mem_univ p))

variable {s x}

/-- Threshold reconstruction uses the share hypothesis `#s` times. -/
theorem threshold_useCount (hx : Set.InjOn x s) : (thresholdDeriv s x hx).useCount 0 = s.card :=
  Decode.extract_useCount ..

/-- Threshold reconstruction asks for at most `#s` shares. -/
theorem threshold_queries_card_le (hx : Set.InjOn x s)
    (g : ∀ (_ : DealerPoly (F := F) s) (_ : ↥s), F) (f : DealerPoly (F := F) s) :
    ((((thresholdDeriv s x hx).queries g f PUnit.unit).card : ℕ) : ℕ∞) ≤ s.card :=
  Decode.extract_queries_card_le ..

/-- **Correctness of threshold reconstruction.** The program of the derivation is the Lagrange
combination of the shares, and it equals the secret when the shares it asks for are correct. -/
theorem threshold_reconstruct (hx : Set.InjOn x s)
    (g : ∀ (_ : DealerPoly (F := F) s) (_ : ↥s), F) (f : DealerPoly (F := F) s)
    (h : ∀ p ∈ (thresholdDeriv s x hx).queries g f PUnit.unit, g f p = f.1.eval (x p)) :
    (thresholdDeriv s x hx).program g f PUnit.unit = lagrangeDecode s x (g f) ∧
      (thresholdDeriv s x hx).program g f PUnit.unit = f.1.eval 0 := by
  have hp : (thresholdDeriv s x hx).program g f PUnit.unit = lagrangeDecode s x (g f) :=
    Decode.extract_program ..
  have hs : secretRel s ⟨f, lagrangeDecode s x (g f)⟩ :=
    Decode.extract_sound (X := fun _ => ↥s) (Y := fun _ => F) (Wt := fun _ => F) _ _ _ _ _ _ _
      g f h
  exact ⟨hp, hp.trans hs⟩

end Threshold

/-! ## Views of MPC-in-the-head and cut-and-choose -/

section Views

variable {I J : Type u} [Fintype J] {V : J → Type u} {Wt : I → Type u}

/-- **View extraction**: from the hypothesis that every view `j : J` is opened consistently with
the statement, a decoding function `D` of the opened views gives a witness. -/
def viewDeriv (cons : I → ∀ j, V j → Prop) (R : (Σ i, Wt i) → Prop) (D : ∀ i, (∀ j, V j) → Wt i)
    (hD : ∀ i v, (∀ j, cons i j (v j)) → R ⟨i, D i v⟩) :
    Deriv (fun _ : Fin 1 => Deriv.allEx (X := fun _ => J) (Y := fun q => V q.2) 0 0
      fun y => cons y.1.1 y.1.2 y.2) (Decode.allExUnit R) :=
  Decode.extract (X := fun _ => J) (Y := fun q => V q.2) _ R (fun _ => Finset.univ.val)
    (Fintype.card J) (fun _ => by simp) D fun i v hv => hD i v fun j => hv j (Finset.mem_univ j)

variable (cons : I → ∀ j, V j → Prop) (R : (Σ i, Wt i) → Prop) (D : ∀ i, (∀ j, V j) → Wt i)
  (hD : ∀ i v, (∀ j, cons i j (v j)) → R ⟨i, D i v⟩)

/-- View extraction uses the view hypothesis `#J` times. -/
theorem viewDeriv_useCount : (viewDeriv cons R D hD).useCount 0 = Fintype.card J :=
  Decode.extract_useCount ..

/-- View extraction opens at most `#J` views. -/
theorem viewDeriv_queries_card_le (g : ∀ (_ : I) (j : J), V j) (i : I) :
    ((((viewDeriv cons R D hD).queries g i PUnit.unit).card : ℕ) : ℕ∞) ≤ Fintype.card J :=
  Decode.extract_queries_card_le ..

end Views

/-- Three views, as in the extractor of ZKB++, are three uses of the view hypothesis. -/
theorem viewDeriv_useCount_fin_three {I : Type} {V : Fin 3 → Type} {Wt : I → Type}
    (cons : I → ∀ j, V j → Prop) (R : (Σ i, Wt i) → Prop) (D : ∀ i, (∀ j, V j) → Wt i)
    (hD : ∀ i v, (∀ j, cons i j (v j)) → R ⟨i, D i v⟩) :
    (viewDeriv cons R D hD).useCount 0 = 3 := by
  simp [viewDeriv_useCount]

/-! ## Rewinding -/

section Rewind

variable {I J : Type u} [Fintype J] {Ch : I → Type u} {Z : (Σ i, Ch i) → Type u}
  {Wt : I → Type u}

/-- **Rewinding extraction**: from the hypothesis that the adversary answers every challenge
acceptably, an extractor that runs it at the challenges `ch i j` (`j : J`) and combines the
responses by `Ext` gives a witness. -/
def rewindDeriv (acc : (Σ x : Σ i, Ch i, Z x) → Prop) (R : (Σ i, Wt i) → Prop)
    (ch : ∀ i, J → Ch i) (Ext : ∀ i, (∀ j, Z ⟨i, ch i j⟩) → Wt i)
    (hExt : ∀ i zs, (∀ j, acc ⟨⟨i, ch i j⟩, zs j⟩) → R ⟨i, Ext i zs⟩) :
    Deriv (fun _ : Fin 1 => Deriv.allEx 0 0 acc) (Decode.allExUnit R) :=
  Decode.extract acc R (fun i => Finset.univ.val.map (ch i)) (Fintype.card J) (fun _ => by simp)
    (fun i g => Ext i fun j => g (ch i j))
    fun i g hg => hExt i _ fun j => hg _ (Multiset.mem_map_of_mem _ (Finset.mem_univ j))

variable (acc : (Σ x : Σ i, Ch i, Z x) → Prop) (R : (Σ i, Wt i) → Prop)
  (ch : ∀ i, J → Ch i) (Ext : ∀ i, (∀ j, Z ⟨i, ch i j⟩) → Wt i)
  (hExt : ∀ i zs, (∀ j, acc ⟨⟨i, ch i j⟩, zs j⟩) → R ⟨i, Ext i zs⟩)

/-- The number of rewinds is the use count of the adversary hypothesis: `#J`. -/
theorem rewindDeriv_useCount : (rewindDeriv acc R ch Ext hExt).useCount 0 = Fintype.card J :=
  Decode.extract_useCount ..

/-- The rewinding extractor runs the adversary at most `#J` times. -/
theorem rewindDeriv_queries_card_le (g : ∀ i (c : Ch i), Z ⟨i, c⟩) (i : I) :
    ((((rewindDeriv acc R ch Ext hExt).queries g i PUnit.unit).card : ℕ) : ℕ∞) ≤
      Fintype.card J :=
  Decode.extract_queries_card_le ..

end Rewind

end CatCrypt.Container.DNLogic
