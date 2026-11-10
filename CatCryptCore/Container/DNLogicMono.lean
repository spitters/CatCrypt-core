/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Container.DNLogicNeg
public import CatCryptCore.Core.CostMajorant
public import Mathlib.Order.PartialSups
public import Mathlib.Data.Nat.Prime.Defs

/-!
# The monotone Diller–Nahm interpretation: majorants of witnesses and bound extraction

Relative to the size that each quantifier of `Form` carries for its sorts, the witnesses and
counter-witnesses of the Diller–Nahm meaning `Form.dn` of a formula are majorized hereditarily,
in the style of Howard's majorizability and Kohlenbach's monotone functional interpretation. The
majorants of a formula `φ` have the types `φ.B` (of witnesses) and `φ.Bc` (of counter-witnesses),
built from `ℕ`, products, sums, function types and lists, independent of the point of the sort
context:

* a witness of `∀ k, φ` is majorized by `b : ℕ → φ.B` when `b m` majorizes its value at every
  `k` of size at most `m`;
* a witness `⟨k, a⟩` of `∃ k, φ` is majorized by `(m, b)` when the size of `k` is at most `m`
  and `b` majorizes `a`;
* a witness `(f, g)` of `φ → ψ` is majorized by `(bf, bg)` when `bf` sends majorants of witnesses
  of `φ` to majorants of the images under `f`, and `bg` sends them, with a majorant of a
  counter-witness of `ψ`, to a list of majorants that covers the counter-witnesses of `φ` that
  `g` demands;
* a witness of `φ ∨ ψ` is majorized by a pair of majorants, one for each disjunct.

A derivation is interpreted over an environment `R : ℕ → I → Prop` of the sort context (`R m i`:
the variables of `i` have size at most `m`), extended along each quantifier by the size of the
new variable (`envExt`). The majorant data of a derivation (`Deriv.MajD`) are a majorant of each
term of `∀`-elimination and `∃`-introduction (`TermMaj`) and a majorant of each realized axiom
(`HomMaj`, for `hom`, the axiom of choice `ac`, independence of premise `ip` and Markov's
principle `markov`): a majorant of the realizer of the axiom, not the realizer. `Deriv.bnd` sends
majorants of the hypotheses to a majorant of the conclusion and a majorant of the demanded
counter-witnesses, by a recursion that reads the majorant data and the shape of the derivation and
never a realizer. `Deriv.bnd_sound` is the soundness of the monotone interpretation for every
rule.

At the Π⁰₂ level, a derivation of `∀ x, ∃ y, r (x, y)` gives the monotone bound
`pi2Bound`, the partial maxima of the first components of the majorant of the conclusion, and
`Deriv.allEx_costMaj` states that it majorizes the size of the realizer along the size of the
argument (`CostMaj` of `Core/CostMajorant.lean`). Through `CDeriv.pi2` the same holds for
classical derivations (`CDeriv.extract_costMaj`). The example `primeDiv` realizes a prime divisor
of `x + 2` by `Classical.choose` and has the majorant `m ↦ m + 2`, whose bound is that function
(`primeDiv_pi2Bound`).

## Main definitions

* `Form.B`, `Form.Bc`, `Form.maj`, `Form.Maj`, `Form.MajC`, `Form.MajL` — majorant types and
  majorization;
* `envExt`, `TermMaj`, `HomMaj`, `Deriv.MajD` — environments and majorant data;
* `Deriv.bnd` — the bound of a derivation;
* `pi2Bound` — the monotone bound at the Π⁰₂ level.

## Main results

* `Form.maj_join` — majorization is upward closed along the join of majorants;
* `Deriv.bnd_hyp`, `Deriv.bnd_impE_fst`, `Deriv.bnd_impE_snd`, … — the unfolding lemmas of
  `Deriv.bnd`, one for each rule and each component of the bound;
* `Deriv.bnd_sound` — soundness of the monotone interpretation;
* `Deriv.allEx_costMaj`, `Deriv.exists_le_pi2Bound` — bound extraction at the Π⁰₂ level;
* `CDeriv.extract_costMaj`, `CDeriv.exists_le_extract_pi2Bound` — the same for classical
  derivations;
* `primeDiv_pi2Bound`, `primeDiv_exists_le` — a noncomputable realizer with a computable bound.

## References

* W. A. Howard, *Hereditarily majorizable functionals of finite type*, in Metamathematical
  Investigation of Intuitionistic Arithmetic and Analysis, LNM 344 (1973).
* U. Kohlenbach, *Applied Proof Theory: Proof Interpretations and their Use in Mathematics*,
  Springer (2008), chapter 9.

Search words: monotone functional interpretation, majorizability, majorant, proof mining, bound
extraction, Diller–Nahm, Dialectica, Π⁰₂, cost majorant.
-/

set_option autoImplicit false

@[expose] public section

universe u

namespace CatCrypt.Container.DNLogic

open DPred CatCrypt.Core

namespace Form

/-- The majorant types of a formula: of its witnesses, and of its counter-witnesses. -/
def bty : {I : Type u} → Form I → Type × Type
  | _, .atom _ => (Unit, Unit)
  | _, .top => (Unit, Unit)
  | _, .and φ ψ => (φ.bty.1 × ψ.bty.1, φ.bty.2 ⊕ ψ.bty.2)
  | _, .imp φ ψ => ((φ.bty.1 → ψ.bty.1) × (φ.bty.1 → ψ.bty.2 → List φ.bty.2),
      φ.bty.1 × ψ.bty.2)
  | _, .or φ ψ => (φ.bty.1 × ψ.bty.1, φ.bty.2 ⊕ ψ.bty.2)
  | _, .all φ => (ℕ → φ.bty.1, ℕ × φ.bty.2)
  | _, .ex φ => (ℕ × φ.bty.1, φ.bty.2)
  | _, .sub _ φ => φ.bty

/-- The type of majorants of the witnesses of a formula. -/
abbrev B {I : Type u} (φ : Form I) : Type := φ.bty.1

/-- The type of majorants of the counter-witnesses of a formula. -/
abbrev Bc {I : Type u} (φ : Form I) : Type := φ.bty.2

/-- The least majorant: `0` at every size, no counter-witness majorant. -/
def bdef : {I : Type u} → (φ : Form I) → φ.B
  | _, .atom _ => ()
  | _, .top => ()
  | _, .and φ ψ => (φ.bdef, ψ.bdef)
  | _, .imp _ ψ => (fun _ => ψ.bdef, fun _ _ => [])
  | _, .or φ ψ => (φ.bdef, ψ.bdef)
  | _, .all φ => fun _ => φ.bdef
  | _, .ex φ => (0, φ.bdef)
  | _, .sub _ φ => φ.bdef

/-- The join of two majorants: the maximum of sizes and the concatenation of lists of
counter-witness majorants. -/
def join : {I : Type u} → (φ : Form I) → φ.B → φ.B → φ.B
  | _, .atom _, _, _ => ()
  | _, .top, _, _ => ()
  | _, .and φ ψ, b, b' => (φ.join b.1 b'.1, ψ.join b.2 b'.2)
  | _, .imp _ ψ, b, b' => (fun a => ψ.join (b.1 a) (b'.1 a), fun a c => b.2 a c ++ b'.2 a c)
  | _, .or φ ψ, b, b' => (φ.join b.1 b'.1, ψ.join b.2 b'.2)
  | _, .all φ, b, b' => fun m => φ.join (b m) (b' m)
  | _, .ex φ, b, b' => (max b.1 b'.1, φ.join b.2 b'.2)
  | _, .sub _ φ, b, b' => φ.join b b'

/-- Hereditary majorization relative to the sizes of the quantifiers: the relation between
majorants and witnesses, and between majorants and counter-witnesses of a witness. -/
def maj : {I : Type u} → (φ : Form I) → (i : I) →
    (φ.B → φ.dn.W i → Prop) × (φ.Bc → (w : φ.dn.W i) → φ.dn.C i w → Prop)
  | _, .atom _, _ => (fun _ _ => True, fun _ _ _ => True)
  | _, .top, _ => (fun _ _ => True, fun _ _ _ => True)
  | _, .and φ ψ, i => (fun b w => (maj φ i).1 b.1 w.1 ∧ (maj ψ i).1 b.2 w.2,
      fun bc w c => match bc, c with
        | .inl b, .inl c => (maj φ i).2 b w.1 c
        | .inr b, .inr c => (maj ψ i).2 b w.2 c
        | _, _ => False)
  | _, .imp φ ψ, i => (fun b F => ∀ a ba, (maj φ i).1 ba a →
        (maj ψ i).1 (b.1 ba) (F.1 a) ∧ ∀ bc c, (maj ψ i).2 bc (F.1 a) c →
          ∀ x ∈ F.2 a c, ∃ b' ∈ b.2 ba bc, (maj φ i).2 b' a x,
      fun bc F c => (maj φ i).1 bc.1 c.1 ∧ (maj ψ i).2 bc.2 (F.1 c.1) c.2)
  | _, .or φ ψ, i => (fun b w => match w with
        | .inl a => (maj φ i).1 b.1 a
        | .inr a => (maj ψ i).1 b.2 a,
      fun bc w c => match bc, w, c with
        | .inl b, .inl a, c => (maj φ i).2 b a c
        | .inr b, .inr a, c => (maj ψ i).2 b a c
        | _, _, _ => False)
  | _, .all (K := K) (sz := s) φ, i => (fun b w => ∀ (k : K i) (m : ℕ), s i k ≤ m →
        (maj φ ⟨i, k⟩).1 (b m) (w k),
      fun bc w c => s i c.1 ≤ bc.1 ∧ (maj φ ⟨i, c.1⟩).2 bc.2 (w c.1) c.2)
  | _, .ex (sz := s) φ, i => (fun b w => s i w.1 ≤ b.1 ∧ (maj φ ⟨i, w.1⟩).1 b.2 w.2,
      fun bc w c => (maj φ ⟨i, w.1⟩).2 bc w.2 c)
  | _, .sub h φ, j => maj φ (h j)

/-- `b` majorizes the witness `w` of `φ` at `i`. -/
abbrev Maj {I : Type u} (φ : Form I) (i : I) : φ.B → φ.dn.W i → Prop := (maj φ i).1

/-- `b` majorizes the counter-witness `c` of the witness `w` of `φ` at `i`. -/
abbrev MajC {I : Type u} (φ : Form I) (i : I) : φ.Bc → (w : φ.dn.W i) → φ.dn.C i w → Prop :=
  (maj φ i).2

/-- One of the majorants of the list `L` majorizes the counter-witness `c` of `w`. -/
def MajL {I : Type u} (φ : Form I) (i : I) (L : List φ.Bc) (w : φ.dn.W i) (c : φ.dn.C i w) :
    Prop :=
  ∃ b ∈ L, MajC φ i b w c

/-- A list containing the majorants of `L` covers what `L` covers. -/
theorem MajL.mono {I : Type u} {φ : Form I} {i : I} {L L' : List φ.Bc} {w : φ.dn.W i}
    {c : φ.dn.C i w} (hL : ∀ b ∈ L, b ∈ L') (h : MajL φ i L w c) : MajL φ i L' w c := by
  obtain ⟨b, hb, h⟩ := h
  exact ⟨b, hL b hb, h⟩

/-- A `flatMap` covers what the image of each of its elements covers. -/
theorem MajL.flatMap {α : Type} {I : Type u} {φ : Form I} {i : I} {L : List α}
    {f : α → List φ.Bc} {a : α} (ha : a ∈ L) {w : φ.dn.W i} {c : φ.dn.C i w}
    (h : MajL φ i (f a) w c) : MajL φ i (L.flatMap f) w c :=
  h.mono fun _ hb => List.mem_flatMap.2 ⟨a, ha, hb⟩

/-- **Majorization is upward closed along the join.** -/
theorem maj_join : ∀ {I : Type u} (φ : Form I) (i : I) (b b' : φ.B) (w : φ.dn.W i),
    (Maj φ i b w → Maj φ i (φ.join b b') w) ∧
      (Maj φ i b' w → Maj φ i (φ.join b b') w) := by
  intro I φ
  induction φ with
  | atom p => exact fun _ _ _ _ => ⟨fun _ => trivial, fun _ => trivial⟩
  | top => exact fun _ _ _ _ => ⟨fun _ => trivial, fun _ => trivial⟩
  | and φ ψ ihφ ihψ =>
    intro i b b' w
    exact ⟨fun h => ⟨(ihφ i _ _ _).1 h.1, (ihψ i _ _ _).1 h.2⟩,
      fun h => ⟨(ihφ i _ _ _).2 h.1, (ihψ i _ _ _).2 h.2⟩⟩
  | imp φ ψ _ ihψ =>
    intro i b b' w
    refine ⟨fun h a ba ha => ?_, fun h a ba ha => ?_⟩
    · obtain ⟨h1, h2⟩ := h a ba ha
      exact ⟨(ihψ i _ _ _).1 h1, fun bc c hc x hx =>
        MajL.mono (fun _ hb => List.mem_append_left _ hb) (h2 bc c hc x hx)⟩
    · obtain ⟨h1, h2⟩ := h a ba ha
      exact ⟨(ihψ i _ _ _).2 h1, fun bc c hc x hx =>
        MajL.mono (fun _ hb => List.mem_append_right _ hb) (h2 bc c hc x hx)⟩
  | or φ ψ ihφ ihψ =>
    intro i b b' w
    cases w with
    | inl a => exact ⟨fun h => (ihφ i _ _ a).1 h, fun h => (ihφ i _ _ a).2 h⟩
    | inr a => exact ⟨fun h => (ihψ i _ _ a).1 h, fun h => (ihψ i _ _ a).2 h⟩
  | all φ ih =>
    intro i b b' w
    exact ⟨fun h k m hk => (ih _ _ _ _).1 (h k m hk), fun h k m hk => (ih _ _ _ _).2 (h k m hk)⟩
  | ex φ ih =>
    intro i b b' w
    exact ⟨fun h => ⟨h.1.trans (le_max_left _ _), (ih _ _ _ _).1 h.2⟩,
      fun h => ⟨h.1.trans (le_max_right _ _), (ih _ _ _ _).2 h.2⟩⟩
  | sub h φ ih => exact fun j b b' w => ih (h j) b b' w

end Form

open Form

variable {I : Type u} {n : ℕ}

/-- Majorants of the hypotheses of a context. -/
abbrev CtxB (Γ : Fin n → Form I) : Type := ∀ k, (Γ k).B

/-- The majorants of an extended context. -/
def consB {φ : Form I} {Γ : Fin n → Form I} (a : φ.B) (hm : CtxB Γ) : CtxB (consF φ Γ)
  | ⟨0, _⟩ => a
  | ⟨j + 1, h⟩ => hm ⟨j, Nat.lt_of_succ_lt_succ h⟩

/-- The extension of an environment along a quantifier over `K` of size `s`: the old variables
and the new one have size at most `m`. -/
def envExt (R : ℕ → I → Prop) {K : I → Type u} (s : ∀ i, K i → ℕ) : ℕ → (Σ i, K i) → Prop :=
  fun m x => R m x.1 ∧ s x.1 x.2 ≤ m

/-- A majorant of a term `t` of sort `K`, of size `s`, over the environment `R`: a bound `tb m`
on the size of `t i` at every point `i` that `R m` admits. -/
def TermMaj {K : I → Type u} (s : ∀ i, K i → ℕ) (R : ℕ → I → Prop) (t : ∀ i, K i) : Type :=
  {tb : ℕ → ℕ // ∀ m i, R m i → s i (t i) ≤ tb m}

/-- A majorant of a morphism `f` of Diller–Nahm meanings over the environment `R`: a majorant of
its forward map and of its backward map, as for a witness of an implication. -/
def HomMaj (R : ℕ → I → Prop) (φ ψ : Form I) (f : φ.dn.Hom ψ.dn) : Type :=
  {g : (ℕ → φ.B → ψ.B) × (ℕ → φ.B → ψ.Bc → List φ.Bc) //
    ∀ m i, R m i → ∀ a ba, Maj φ i ba a → Maj ψ i (g.1 m ba) (f.fwd i a) ∧
      ∀ bc c, MajC ψ i bc (f.fwd i a) c → ∀ x ∈ f.back i a c, MajL φ i (g.2 m ba bc) a x}

/-- An extended environment is monotone when the environment is. -/
theorem envExt_mono {R : ℕ → I → Prop} (hR : Monotone R) {K : I → Type u}
    (s : ∀ i, K i → ℕ) : Monotone (envExt R s) :=
  fun _ _ h _ hx => ⟨hR h _ hx.1, hx.2.trans h⟩

/-- Majorized witnesses of the hypotheses and of a new hypothesis are majorized witnesses of the
extended context. -/
theorem maj_consW {φ : Form I} {Γ : Fin n → Form I} {i : I} {ba : φ.B} {a : φ.dn.W i}
    {hm : CtxB Γ} {w : (ctx Γ).W i} (ha : Maj φ i ba a)
    (hw : ∀ k, Maj (Γ k) i (hm k) (w k)) :
    ∀ k, Maj (consF φ Γ k) i (consB ba hm k) (consW i a w k)
  | ⟨0, _⟩ => ha
  | ⟨_ + 1, _⟩ => hw _

/-- The counter-witness of the new hypothesis kept by `headC?` is covered by the majorants at
position `0`. -/
theorem majL_headC? {φ : Form I} {Γ : Fin n → Form I} {i : I} {a : φ.dn.W i}
    {w : (ctx Γ).W i} (L : ∀ k, List (consF φ Γ k).Bc)
    (y : (ctx (consF φ Γ)).C i (consW i a w)) (c : φ.dn.C i a) (h : headC? y = some c)
    (hy : MajL (consF φ Γ y.1) i (L y.1) (consW i a w y.1) y.2) :
    MajL φ i (L ⟨0, Nat.succ_pos _⟩) a c := by
  obtain ⟨⟨_ | j, hj⟩, c'⟩ := y
  · cases h
    exact hy
  · simp [headC?] at h

/-- The counter-witness of an old hypothesis kept by `tailC?` is covered by the majorants at the
successor position. -/
theorem majL_tailC? {φ : Form I} {Γ : Fin n → Form I} {i : I} {a : φ.dn.W i}
    {w : (ctx Γ).W i} (L : ∀ k, List (consF φ Γ k).Bc)
    (y : (ctx (consF φ Γ)).C i (consW i a w)) (c : (ctx Γ).C i w) (h : tailC? y = some c)
    (hy : MajL (consF φ Γ y.1) i (L y.1) (consW i a w y.1) y.2) :
    MajL (Γ c.1) i (L c.1.succ) (w c.1) c.2 := by
  obtain ⟨⟨_ | j, hj⟩, c'⟩ := y
  · simp [tailC?] at h
  · cases h
    exact hy

namespace Deriv

/-- The majorant data of a derivation over the environment `R`: a majorant of each term of
`∀`-elimination and `∃`-introduction, and a majorant of each realized axiom (`hom`, `ac`, `ip`,
`markov`). -/
def MajD : {I : Type u} → {n : ℕ} → {Γ : Fin n → Form I} → {φ : Form I} → Deriv Γ φ →
    (ℕ → I → Prop) → Type
  | _, _, Γ, .(Γ k), .hyp k, _ => Unit
  | _, _, _, _, .topI, _ => Unit
  | _, _, _, _, .andI d e, R => MajD d R × MajD e R
  | _, _, _, _, .andE₁ d, R => MajD d R
  | _, _, _, _, .andE₂ d, R => MajD d R
  | _, _, _, _, .impI d, R => MajD d R
  | _, _, _, _, .impE d e, R => MajD d R × MajD e R
  | _, _, _, _, .orI₁ d, R => MajD d R
  | _, _, _, _, .orI₂ d, R => MajD d R
  | _, _, _, _, .orE d e₁ e₂, R => MajD d R × MajD e₁ R × MajD e₂ R
  | _, _, _, _, .allI (s := s) d, R => MajD d (envExt R s)
  | _, _, _, _, .allE (s := s) t d, R => TermMaj s R t × MajD d R
  | _, _, _, _, .exI (s := s) t d, R => TermMaj s R t × MajD d R
  | _, _, _, _, .exE (s := s) d e, R => MajD d R × MajD e (envExt R s)
  | _, _, _, _, .ac (K := K) (L := L) (sK := sK) (sL := sL) (sF := sF) (φ := φ) d, R =>
    MajD d R × HomMaj R (.all (sz := sK) (.ex (sz := sL) φ))
      (.ex (K := fun i => ∀ k : K i, L ⟨i, k⟩) (sz := sF)
        (.all (K := fun p => K p.1) (sz := fun p => sK p.1)
          (φ.sub fun (y : Σ p : (Σ i, ∀ k : K i, L ⟨i, k⟩), K p.1) =>
          (⟨⟨y.1.1, y.2⟩, y.1.2 y.2⟩ : Σ x : Σ i, K i, L x))))
      (DPred.choice φ.dn).hom
  | _, _, _, _, .ip p (sK := sK) (sL := sL) (ψ := ψ) _ d, R => MajD d R × HomMaj R
      (.imp (.all (sz := sK) (.atom p)) (.ex (sz := sL) ψ))
      (.ex (sz := sL) (.imp ((Form.all (sz := sK) (.atom p)).sub Sigma.fst) ψ))
      (DPred.ip p ψ.dn)
  | _, _, _, _, .markov (K := K) (sK := sK) (sM := sM) p q d, R => MajD d R × HomMaj R
      (.imp (.all (sz := sK) (.atom p)) (.atom q))
      (.ex (K := fun i => Multiset (K i)) (sz := sM)
        (.atom fun x => (∀ k ∈ x.2, p ⟨x.1, k⟩) → q x.1))
      (DPred.markovDN p q)
  | _, _, _, _, .hom (φ := φ) (ψ := ψ) f _ _ _ d, R => MajD d R × HomMaj R φ ψ f
  | _, _, _, _, .atom₂ _ d e, R => MajD d R × MajD e R

/-- The counter-witness majorants of a case analysis: those of each branch on the old
hypotheses, and those of the derivation of the disjunction at the majorants of each branch on
the disjunct. -/
def orBack {φ ψ χ : Form I} {Γ : Fin n → Form I} (gb : (Form.or φ ψ).Bc → ∀ k, List (Γ k).Bc)
    (k₁ : χ.Bc → ∀ k, List (consF φ Γ k).Bc) (k₂ : χ.Bc → ∀ k, List (consF ψ Γ k).Bc)
    (bc : χ.Bc) (k : Fin n) : List (Γ k).Bc :=
  List.append (List.append (List.append (k₁ bc k.succ)
    ((k₁ bc ⟨0, Nat.succ_pos _⟩).flatMap (fun b => gb (.inl b) k)))
    (k₂ bc k.succ)) ((k₂ bc ⟨0, Nat.succ_pos _⟩).flatMap (fun b => gb (.inr b) k))

/-- **The bound of a derivation.** From majorants `hm` of the hypotheses at the environment
`m`, a majorant of the conclusion, and for a majorant of a counter-witness of the conclusion,
the lists of majorants that cover the demanded counter-witnesses of each hypothesis. It reads
the majorant data `D` and the shape of the derivation, and no realizer. -/
def bnd : {I : Type u} → {n : ℕ} → {Γ : Fin n → Form I} → {φ : Form I} → (d : Deriv Γ φ) →
    (R : ℕ → I → Prop) → MajD d R → CtxB Γ → ℕ → φ.B × (φ.Bc → ∀ k, List (Γ k).Bc)
  | _, _, Γ, .(Γ k), .hyp k, _, _, hm, _ =>
    (hm k, fun bc j => if h : j = k then [h ▸ bc] else [])
  | _, _, _, _, .topI, _, _, _, _ => ((), fun _ _ => [])
  | _, _, _, _, .andI d e, R, D, hm, m =>
    (((bnd d R D.1 hm m).1, (bnd e R D.2 hm m).1),
      fun bc k => Sum.elim (fun b => (bnd d R D.1 hm m).2 b k)
        (fun b => (bnd e R D.2 hm m).2 b k) bc)
  | _, _, _, _, .andE₁ d, R, D, hm, m =>
    ((bnd d R D hm m).1.1, fun bc k => (bnd d R D hm m).2 (.inl bc) k)
  | _, _, _, _, .andE₂ d, R, D, hm, m =>
    ((bnd d R D hm m).1.2, fun bc k => (bnd d R D hm m).2 (.inr bc) k)
  | _, _, _, _, .impI d, R, D, hm, m =>
    ((fun a => (bnd d R D (consB a hm) m).1,
        fun a bc => (bnd d R D (consB a hm) m).2 bc ⟨0, Nat.succ_pos _⟩),
      fun bc k => (bnd d R D (consB bc.1 hm) m).2 bc.2 k.succ)
  | _, _, _, _, .impE d e, R, D, hm, m =>
    ((bnd d R D.1 hm m).1.1 (bnd e R D.2 hm m).1,
      fun bc k => (bnd d R D.1 hm m).2 ((bnd e R D.2 hm m).1, bc) k ++
        ((bnd d R D.1 hm m).1.2 (bnd e R D.2 hm m).1 bc).flatMap
          fun b => (bnd e R D.2 hm m).2 b k)
  | _, _, _, _, .orI₁ (ψ := ψ) d, R, D, hm, m =>
    (((bnd d R D hm m).1, ψ.bdef),
      fun bc k => Sum.elim (fun b => (bnd d R D hm m).2 b k) (fun _ => []) bc)
  | _, _, _, _, .orI₂ (φ := φ) d, R, D, hm, m =>
    ((φ.bdef, (bnd d R D hm m).1),
      fun bc k => Sum.elim (fun _ => []) (fun b => (bnd d R D hm m).2 b k) bc)
  | _, _, _, _, .orE (χ := χ) d e₁ e₂, R, D, hm, m =>
    (χ.join (bnd e₁ R D.2.1 (consB (bnd d R D.1 hm m).1.1 hm) m).1
        (bnd e₂ R D.2.2 (consB (bnd d R D.1 hm m).1.2 hm) m).1,
      orBack (bnd d R D.1 hm m).2 (bnd e₁ R D.2.1 (consB (bnd d R D.1 hm m).1.1 hm) m).2
        (bnd e₂ R D.2.2 (consB (bnd d R D.1 hm m).1.2 hm) m).2)
  | _, _, _, _, .allI (s := s) d, R, D, hm, m =>
    (fun m' => (bnd d (envExt R s) D hm (max m m')).1,
      fun bc k => (bnd d (envExt R s) D hm (max m bc.1)).2 bc.2 k)
  | _, _, _, _, .allE _ d, R, D, hm, m =>
    ((bnd d R D.2 hm m).1 (D.1.1 m), fun bc k => (bnd d R D.2 hm m).2 (D.1.1 m, bc) k)
  | _, _, _, _, .exI _ d, R, D, hm, m =>
    ((D.1.1 m, (bnd d R D.2 hm m).1), (bnd d R D.2 hm m).2)
  | _, _, _, _, .exE (s := s) d e, R, D, hm, m =>
    ((bnd e (envExt R s) D.2 (consB (bnd d R D.1 hm m).1.2 hm)
        (max m (bnd d R D.1 hm m).1.1)).1,
      fun bc k => List.append ((bnd e (envExt R s) D.2 (consB (bnd d R D.1 hm m).1.2 hm)
          (max m (bnd d R D.1 hm m).1.1)).2 bc k.succ)
        (((bnd e (envExt R s) D.2 (consB (bnd d R D.1 hm m).1.2 hm)
          (max m (bnd d R D.1 hm m).1.1)).2 bc ⟨0, Nat.succ_pos _⟩).flatMap
            fun b => (bnd d R D.1 hm m).2 b k))
  | _, _, _, _, .ac d, R, D, hm, m =>
    (D.2.1.1 m (bnd d R D.1 hm m).1,
      fun bc k => (D.2.1.2 m (bnd d R D.1 hm m).1 bc).flatMap fun b => (bnd d R D.1 hm m).2 b k)
  | _, _, _, _, .ip _ _ d, R, D, hm, m =>
    (D.2.1.1 m (bnd d R D.1 hm m).1,
      fun bc k => (D.2.1.2 m (bnd d R D.1 hm m).1 bc).flatMap fun b => (bnd d R D.1 hm m).2 b k)
  | _, _, _, _, .markov _ _ d, R, D, hm, m =>
    (D.2.1.1 m (bnd d R D.1 hm m).1,
      fun bc k => (D.2.1.2 m (bnd d R D.1 hm m).1 bc).flatMap fun b => (bnd d R D.1 hm m).2 b k)
  | _, _, _, _, .hom _ _ _ _ d, R, D, hm, m =>
    (D.2.1.1 m (bnd d R D.1 hm m).1,
      fun bc k => (D.2.1.2 m (bnd d R D.1 hm m).1 bc).flatMap fun b => (bnd d R D.1 hm m).2 b k)
  | _, _, _, _, .atom₂ _ d e, R, D, hm, m =>
    ((), fun _ k => (bnd d R D.1 hm m).2 () k ++ (bnd e R D.2 hm m).2 () k)

/-! ### Unfolding lemmas of `bnd`

One lemma for each rule and each component of the bound: `_fst` gives the majorant of the
conclusion and `_snd` the counter-witness majorants. Each mentions only the components of the
bounds of the premises that it reads, so that `simp only` with these lemmas unfolds the bound of
a concrete derivation without expanding the components that the result does not read. -/

section Unfold

variable {Γ : Fin n → Form I} (R : ℕ → I → Prop) (hm : CtxB Γ) (m : ℕ)

/-- Unfolding lemma of `bnd` at a hypothesis. -/
theorem bnd_hyp (k : Fin n) (D : MajD (Deriv.hyp (Γ := Γ) k) R) :
    bnd (.hyp k) R D hm m = (hm k, fun bc j => if h : j = k then [h ▸ bc] else []) := rfl

/-- Unfolding lemma of `bnd` at `⊤`-introduction. -/
theorem bnd_topI (D : MajD (Deriv.topI (Γ := Γ)) R) :
    bnd .topI R D hm m = ((), fun _ _ => []) := rfl

section Props

variable {φ ψ χ : Form I}

/-- Unfolding lemma of the majorant of `bnd` at a conjunction introduction. -/
theorem bnd_andI_fst (d : Deriv Γ φ) (e : Deriv Γ ψ) (D : MajD (.andI d e) R) :
    (bnd (.andI d e) R D hm m).1 = ((bnd d R D.1 hm m).1, (bnd e R D.2 hm m).1) := rfl

/-- Unfolding lemma of the counter-witness majorants of `bnd` at a conjunction introduction. -/
theorem bnd_andI_snd (d : Deriv Γ φ) (e : Deriv Γ ψ) (D : MajD (.andI d e) R) :
    (bnd (.andI d e) R D hm m).2 = fun bc k => Sum.elim (fun b => (bnd d R D.1 hm m).2 b k)
      (fun b => (bnd e R D.2 hm m).2 b k) bc := rfl

/-- Unfolding lemma of the majorant of `bnd` at the first conjunction elimination. -/
theorem bnd_andE₁_fst (d : Deriv Γ (.and φ ψ)) (D : MajD (.andE₁ d) R) :
    (bnd (.andE₁ d) R D hm m).1 = (bnd d R D hm m).1.1 := rfl

/-- Unfolding lemma of the counter-witness majorants of `bnd` at the first conjunction
elimination. -/
theorem bnd_andE₁_snd (d : Deriv Γ (.and φ ψ)) (D : MajD (.andE₁ d) R) :
    (bnd (.andE₁ d) R D hm m).2 = fun bc k => (bnd d R D hm m).2 (.inl bc) k := rfl

/-- Unfolding lemma of the majorant of `bnd` at the second conjunction elimination. -/
theorem bnd_andE₂_fst (d : Deriv Γ (.and φ ψ)) (D : MajD (.andE₂ d) R) :
    (bnd (.andE₂ d) R D hm m).1 = (bnd d R D hm m).1.2 := rfl

/-- Unfolding lemma of the counter-witness majorants of `bnd` at the second conjunction
elimination. -/
theorem bnd_andE₂_snd (d : Deriv Γ (.and φ ψ)) (D : MajD (.andE₂ d) R) :
    (bnd (.andE₂ d) R D hm m).2 = fun bc k => (bnd d R D hm m).2 (.inr bc) k := rfl

/-- Unfolding lemma of the majorant of `bnd` at an implication introduction. -/
theorem bnd_impI_fst (d : Deriv (consF φ Γ) ψ) (D : MajD (.impI d) R) :
    (bnd (.impI d) R D hm m).1 = (fun a => (bnd d R D (consB a hm) m).1,
      fun a bc => (bnd d R D (consB a hm) m).2 bc ⟨0, Nat.succ_pos _⟩) := rfl

/-- Unfolding lemma of the counter-witness majorants of `bnd` at an implication
introduction. -/
theorem bnd_impI_snd (d : Deriv (consF φ Γ) ψ) (D : MajD (.impI d) R) :
    (bnd (.impI d) R D hm m).2 =
      fun (bc : (Form.imp φ ψ).Bc) (k : Fin n) => (bnd d R D (consB bc.1 hm) m).2 bc.2 k.succ :=
  rfl

/-- Unfolding lemma of the majorant of `bnd` at an implication elimination. -/
theorem bnd_impE_fst (d : Deriv Γ (.imp φ ψ)) (e : Deriv Γ φ) (D : MajD (.impE d e) R) :
    (bnd (.impE d e) R D hm m).1 = (bnd d R D.1 hm m).1.1 (bnd e R D.2 hm m).1 := rfl

/-- Unfolding lemma of the counter-witness majorants of `bnd` at an implication elimination. -/
theorem bnd_impE_snd (d : Deriv Γ (.imp φ ψ)) (e : Deriv Γ φ) (D : MajD (.impE d e) R) :
    (bnd (.impE d e) R D hm m).2 = fun bc k => (bnd d R D.1 hm m).2
      ((bnd e R D.2 hm m).1, bc) k ++
        ((bnd d R D.1 hm m).1.2 (bnd e R D.2 hm m).1 bc).flatMap
          fun b => (bnd e R D.2 hm m).2 b k := rfl

/-- Unfolding lemma of the majorant of `bnd` at the first disjunction introduction. -/
theorem bnd_orI₁_fst (d : Deriv Γ φ) (D : MajD (.orI₁ (ψ := ψ) d) R) :
    (bnd (.orI₁ (ψ := ψ) d) R D hm m).1 = ((bnd d R D hm m).1, ψ.bdef) := rfl

/-- Unfolding lemma of the counter-witness majorants of `bnd` at the first disjunction
introduction. -/
theorem bnd_orI₁_snd (d : Deriv Γ φ) (D : MajD (.orI₁ (ψ := ψ) d) R) :
    (bnd (.orI₁ (ψ := ψ) d) R D hm m).2 =
      fun bc k => Sum.elim (fun b => (bnd d R D hm m).2 b k) (fun _ => []) bc := rfl

/-- Unfolding lemma of the majorant of `bnd` at the second disjunction introduction. -/
theorem bnd_orI₂_fst (d : Deriv Γ ψ) (D : MajD (.orI₂ (φ := φ) d) R) :
    (bnd (.orI₂ (φ := φ) d) R D hm m).1 = (φ.bdef, (bnd d R D hm m).1) := rfl

/-- Unfolding lemma of the counter-witness majorants of `bnd` at the second disjunction
introduction. -/
theorem bnd_orI₂_snd (d : Deriv Γ ψ) (D : MajD (.orI₂ (φ := φ) d) R) :
    (bnd (.orI₂ (φ := φ) d) R D hm m).2 =
      fun bc k => Sum.elim (fun _ => []) (fun b => (bnd d R D hm m).2 b k) bc := rfl

/-- Unfolding lemma of the majorant of `bnd` at a case analysis. -/
theorem bnd_orE_fst (d : Deriv Γ (.or φ ψ)) (e₁ : Deriv (consF φ Γ) χ)
    (e₂ : Deriv (consF ψ Γ) χ) (D : MajD (.orE d e₁ e₂) R) :
    (bnd (.orE d e₁ e₂) R D hm m).1 =
      χ.join (bnd e₁ R D.2.1 (consB (bnd d R D.1 hm m).1.1 hm) m).1
        (bnd e₂ R D.2.2 (consB (bnd d R D.1 hm m).1.2 hm) m).1 := rfl

/-- Unfolding lemma of the counter-witness majorants of `bnd` at a case analysis. -/
theorem bnd_orE_snd (d : Deriv Γ (.or φ ψ)) (e₁ : Deriv (consF φ Γ) χ)
    (e₂ : Deriv (consF ψ Γ) χ) (D : MajD (.orE d e₁ e₂) R) :
    (bnd (.orE d e₁ e₂) R D hm m).2 =
      orBack (bnd d R D.1 hm m).2 (bnd e₁ R D.2.1 (consB (bnd d R D.1 hm m).1.1 hm) m).2
        (bnd e₂ R D.2.2 (consB (bnd d R D.1 hm m).1.2 hm) m).2 := rfl

/-- Unfolding lemma of the majorant of `bnd` at a realized axiom. -/
theorem bnd_hom_fst (f : φ.dn.Hom ψ.dn) (N : ℕ) (hN : ∀ i w c, (f.back i w c).card ≤ N)
    (hev : ∀ i, φ.eval i → ψ.eval i) (d : Deriv Γ φ) (D : MajD (.hom f N hN hev d) R) :
    (bnd (.hom f N hN hev d) R D hm m).1 = D.2.1.1 m (bnd d R D.1 hm m).1 := rfl

/-- Unfolding lemma of the counter-witness majorants of `bnd` at a realized axiom. -/
theorem bnd_hom_snd (f : φ.dn.Hom ψ.dn) (N : ℕ) (hN : ∀ i w c, (f.back i w c).card ≤ N)
    (hev : ∀ i, φ.eval i → ψ.eval i) (d : Deriv Γ φ) (D : MajD (.hom f N hN hev d) R) :
    (bnd (.hom f N hN hev d) R D hm m).2 = fun bc k =>
      (D.2.1.2 m (bnd d R D.1 hm m).1 bc).flatMap fun b => (bnd d R D.1 hm m).2 b k := rfl

/-- Unfolding lemma of the majorant of `bnd` at the atom rule. -/
theorem bnd_atom₂_fst {p q s : I → Prop} (h : ∀ i, p i → q i → s i) (d : Deriv Γ (.atom p))
    (e : Deriv Γ (.atom q)) (D : MajD (.atom₂ h d e) R) :
    (bnd (.atom₂ h d e) R D hm m).1 = () := rfl

/-- Unfolding lemma of the counter-witness majorants of `bnd` at the atom rule. -/
theorem bnd_atom₂_snd {p q s : I → Prop} (h : ∀ i, p i → q i → s i) (d : Deriv Γ (.atom p))
    (e : Deriv Γ (.atom q)) (D : MajD (.atom₂ h d e) R) :
    (bnd (.atom₂ h d e) R D hm m).2 =
      fun _ k => (bnd d R D.1 hm m).2 () k ++ (bnd e R D.2 hm m).2 () k := rfl

end Props

section Quant

variable {K : I → Type u} {s : ∀ i, K i → ℕ} {φ : Form (Σ i, K i)}

/-- Unfolding lemma of the majorant of `bnd` at a `∀`-introduction: the bound of the premise at
the larger environment. -/
theorem bnd_allI_fst (d : Deriv (fun k => (Γ k).sub Sigma.fst) φ)
    (D : MajD (.allI (s := s) d) R) :
    (bnd (.allI (s := s) d) R D hm m).1 = fun m' =>
      (@bnd _ _ (fun k => (Γ k).sub Sigma.fst) φ d (envExt R s) D hm (max m m')).1 := rfl

/-- Unfolding lemma of the counter-witness majorants of `bnd` at a `∀`-introduction. -/
theorem bnd_allI_snd (d : Deriv (fun k => (Γ k).sub Sigma.fst) φ)
    (D : MajD (.allI (s := s) d) R) :
    (bnd (.allI (s := s) d) R D hm m).2 = fun bc k =>
      (@bnd _ _ (fun k => (Γ k).sub Sigma.fst) φ d (envExt R s) D hm (max m bc.1)).2 bc.2 k :=
  rfl

/-- Unfolding lemma of the majorant of `bnd` at a `∀`-elimination: the majorant of the premise
at the bound of the term. -/
theorem bnd_allE_fst (t : ∀ i, K i) (d : Deriv Γ (.all (sz := s) φ)) (D : MajD (.allE t d) R) :
    (bnd (.allE t d) R D hm m).1 = (bnd d R D.2 hm m).1 (D.1.1 m) := rfl

/-- Unfolding lemma of the counter-witness majorants of `bnd` at a `∀`-elimination. -/
theorem bnd_allE_snd (t : ∀ i, K i) (d : Deriv Γ (.all (sz := s) φ)) (D : MajD (.allE t d) R) :
    (bnd (.allE t d) R D hm m).2 = fun bc k => (bnd d R D.2 hm m).2 (D.1.1 m, bc) k := rfl

/-- Unfolding lemma of the majorant of `bnd` at an `∃`-introduction: the bound of the term and
the majorant of the premise. -/
theorem bnd_exI_fst (t : ∀ i, K i) (d : Deriv Γ (φ.sub fun i => (⟨i, t i⟩ : Σ i, K i)))
    (D : MajD (.exI (s := s) (φ := φ) t d) R) :
    (bnd (.exI (s := s) (φ := φ) t d) R D hm m).1 = (D.1.1 m, (bnd d R D.2 hm m).1) := rfl

/-- Unfolding lemma of the counter-witness majorants of `bnd` at an `∃`-introduction. -/
theorem bnd_exI_snd (t : ∀ i, K i) (d : Deriv Γ (φ.sub fun i => (⟨i, t i⟩ : Σ i, K i)))
    (D : MajD (.exI (s := s) (φ := φ) t d) R) :
    (bnd (.exI (s := s) (φ := φ) t d) R D hm m).2 = (bnd d R D.2 hm m).2 := rfl

/-- Unfolding lemma of the majorant of `bnd` at an `∃`-elimination: the bound of the second
premise at the environment enlarged by the bound of the witness. -/
theorem bnd_exE_fst {ψ : Form I} (d : Deriv Γ (.ex (sz := s) φ))
    (e : Deriv (consF φ fun k => (Γ k).sub Sigma.fst) (ψ.sub Sigma.fst))
    (D : MajD (.exE d e) R) :
    (bnd (.exE d e) R D hm m).1 = (bnd e (envExt R s) D.2
      (consB (bnd d R D.1 hm m).1.2 hm) (max m (bnd d R D.1 hm m).1.1)).1 := rfl

/-- Unfolding lemma of the counter-witness majorants of `bnd` at an `∃`-elimination. -/
theorem bnd_exE_snd {ψ : Form I} (d : Deriv Γ (.ex (sz := s) φ))
    (e : Deriv (consF φ fun k => (Γ k).sub Sigma.fst) (ψ.sub Sigma.fst))
    (D : MajD (.exE d e) R) :
    (bnd (.exE d e) R D hm m).2 = fun bc k => List.append (α := (Γ k).Bc)
      ((bnd e (envExt R s) D.2 (consB (bnd d R D.1 hm m).1.2 hm)
        (max m (bnd d R D.1 hm m).1.1)).2 bc k.succ)
      (((bnd e (envExt R s) D.2 (consB (bnd d R D.1 hm m).1.2 hm)
        (max m (bnd d R D.1 hm m).1.1)).2 bc ⟨0, Nat.succ_pos _⟩).flatMap
          fun b => (bnd d R D.1 hm m).2 b k) := rfl

/-- Unfolding lemma of the majorant of `bnd` at Markov's principle. -/
theorem bnd_markov_fst {sM : ∀ i, Multiset (K i) → ℕ} (p : (Σ i, K i) → Prop) (q : I → Prop)
    (d : Deriv Γ (.imp (.all (sz := s) (.atom p)) (.atom q)))
    (D : MajD (.markov (sM := sM) p q d) R) :
    (bnd (.markov (sM := sM) p q d) R D hm m).1 = D.2.1.1 m (bnd d R D.1 hm m).1 := rfl

/-- Unfolding lemma of the counter-witness majorants of `bnd` at Markov's principle. -/
theorem bnd_markov_snd {sM : ∀ i, Multiset (K i) → ℕ} (p : (Σ i, K i) → Prop) (q : I → Prop)
    (d : Deriv Γ (.imp (.all (sz := s) (.atom p)) (.atom q)))
    (D : MajD (.markov (sM := sM) p q d) R) :
    (bnd (.markov (sM := sM) p q d) R D hm m).2 = fun bc k =>
      (D.2.1.2 m (bnd d R D.1 hm m).1 bc).flatMap fun b => (bnd d R D.1 hm m).2 b k := rfl

/-- Unfolding lemma of the majorant of `bnd` at independence of premise. -/
theorem bnd_ip_fst {L : I → Type u} {sL : ∀ i, L i → ℕ} (p : (Σ i, K i) → Prop)
    {ψ : Form (Σ i, L i)} (hL : ∀ i, Nonempty (L i))
    (d : Deriv Γ (.imp (.all (sz := s) (.atom p)) (.ex (sz := sL) ψ)))
    (D : MajD (.ip p hL d) R) :
    (bnd (.ip p hL d) R D hm m).1 = D.2.1.1 m (bnd d R D.1 hm m).1 := rfl

/-- Unfolding lemma of the counter-witness majorants of `bnd` at independence of premise. -/
theorem bnd_ip_snd {L : I → Type u} {sL : ∀ i, L i → ℕ} (p : (Σ i, K i) → Prop)
    {ψ : Form (Σ i, L i)} (hL : ∀ i, Nonempty (L i))
    (d : Deriv Γ (.imp (.all (sz := s) (.atom p)) (.ex (sz := sL) ψ)))
    (D : MajD (.ip p hL d) R) :
    (bnd (.ip p hL d) R D hm m).2 = fun bc k =>
      (D.2.1.2 m (bnd d R D.1 hm m).1 bc).flatMap fun b => (bnd d R D.1 hm m).2 b k := rfl

/-- Unfolding lemma of the majorant of `bnd` at the axiom of choice. -/
theorem bnd_ac_fst {L : (Σ i, K i) → Type u} {sL : ∀ x, L x → ℕ}
    {sF : ∀ i, (∀ k : K i, L ⟨i, k⟩) → ℕ} {φ : Form (Σ x : Σ i, K i, L x)}
    (d : Deriv Γ (.all (sz := s) (.ex (sz := sL) φ))) (D : MajD (.ac (sF := sF) d) R) :
    (bnd (.ac (sF := sF) d) R D hm m).1 = D.2.1.1 m (bnd d R D.1 hm m).1 := rfl

/-- Unfolding lemma of the counter-witness majorants of `bnd` at the axiom of choice. -/
theorem bnd_ac_snd {L : (Σ i, K i) → Type u} {sL : ∀ x, L x → ℕ}
    {sF : ∀ i, (∀ k : K i, L ⟨i, k⟩) → ℕ} {φ : Form (Σ x : Σ i, K i, L x)}
    (d : Deriv Γ (.all (sz := s) (.ex (sz := sL) φ))) (D : MajD (.ac (sF := sF) d) R) :
    (bnd (.ac (sF := sF) d) R D hm m).2 = fun bc k =>
      (D.2.1.2 m (bnd d R D.1 hm m).1 bc).flatMap fun b => (bnd d R D.1 hm m).2 b k := rfl

end Quant

end Unfold

/-- The majorant of the new hypothesis of an extended context. -/
theorem consB_zero {φ : Form I} {Γ : Fin n → Form I} (a : φ.B) (hm : CtxB Γ) (h : 0 < n + 1) :
    consB a hm ⟨0, h⟩ = a := rfl

/-- The majorant of an old hypothesis of an extended context. -/
theorem consB_succ {φ : Form I} {Γ : Fin n → Form I} (a : φ.B) (hm : CtxB Γ) (k : Fin n) :
    consB a hm k.succ = hm k := rfl

/-- Soundness of a case analysis for the majorants: the join of the majorants of the two branches
majorizes the selected branch, and `orBack` covers its demand. -/
theorem orCase_maj {φ ψ χ : Form I} {Γ : Fin n → Form I}
    (E₁ : (ctx (consF φ Γ)).Hom χ.dn) (E₂ : (ctx (consF ψ Γ)).Hom χ.dn) (i : I)
    (w : (ctx Γ).W i) (bx : (Form.or φ ψ).B) (x : (DPred.or φ.dn ψ.dn).W i)
    (hx : Maj (.or φ ψ) i bx x) (gb : (Form.or φ ψ).Bc → ∀ k, List (Γ k).Bc)
    (g : (DPred.or φ.dn ψ.dn).C i x → Multiset ((ctx Γ).C i w))
    (hg : ∀ bc c, MajC (.or φ ψ) i bc x c → ∀ y ∈ g c,
      MajL (Γ y.1) i (gb bc y.1) (w y.1) y.2)
    (b₁ : χ.B) (k₁ : χ.Bc → ∀ k, List (consF φ Γ k).Bc)
    (b₂ : χ.B) (k₂ : χ.Bc → ∀ k, List (consF ψ Γ k).Bc)
    (h₁ : ∀ a, Maj φ i bx.1 a → Maj χ i b₁ (E₁.fwd i (consW i a w)) ∧
      ∀ bc c, MajC χ i bc (E₁.fwd i (consW i a w)) c → ∀ y ∈ E₁.back i (consW i a w) c,
        MajL (consF φ Γ y.1) i (k₁ bc y.1) (consW i a w y.1) y.2)
    (h₂ : ∀ a, Maj ψ i bx.2 a → Maj χ i b₂ (E₂.fwd i (consW i a w)) ∧
      ∀ bc c, MajC χ i bc (E₂.fwd i (consW i a w)) c → ∀ y ∈ E₂.back i (consW i a w) c,
        MajL (consF ψ Γ y.1) i (k₂ bc y.1) (consW i a w y.1) y.2) :
    Maj χ i (χ.join b₁ b₂) (orCaseFwd E₁ E₂ i w x) ∧
    ∀ bc c, MajC χ i bc (orCaseFwd E₁ E₂ i w x) c → ∀ y ∈ orCaseBack E₁ E₂ i w x g c,
      MajL (Γ y.1) i (orBack gb k₁ k₂ bc y.1) (w y.1) y.2 := by
  cases x with
  | inl a =>
    obtain ⟨h1, h2⟩ := h₁ a hx
    refine ⟨(maj_join χ i _ _ _).1 h1, fun bc c hc y hy => ?_⟩
    rcases Multiset.mem_add.1 hy with hy | hy
    · obtain ⟨y', hy', hyy⟩ := (Multiset.mem_filterMap _ _).1 hy
      exact (majL_tailC? _ y' y hyy (h2 bc c hc y' hy')).mono fun _ hb =>
        List.mem_append_left _ (List.mem_append_left _ (List.mem_append_left _ hb))
    · obtain ⟨z, hz, hyz⟩ := Multiset.mem_bind.1 hy
      obtain ⟨y', hy', hz'⟩ := (Multiset.mem_filterMap _ _).1 hz
      obtain ⟨b, hb, hbz⟩ := majL_headC? _ y' z hz' (h2 bc c hc y' hy')
      exact (MajL.flatMap hb (hg (.inl b) z hbz y hyz)).mono fun _ hb' =>
        List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hb'))
  | inr a =>
    obtain ⟨h1, h2⟩ := h₂ a hx
    refine ⟨(maj_join χ i _ _ _).2 h1, fun bc c hc y hy => ?_⟩
    rcases Multiset.mem_add.1 hy with hy | hy
    · obtain ⟨y', hy', hyy⟩ := (Multiset.mem_filterMap _ _).1 hy
      exact (majL_tailC? _ y' y hyy (h2 bc c hc y' hy')).mono fun _ hb =>
        List.mem_append_left _ (List.mem_append_right _ hb)
    · obtain ⟨z, hz, hyz⟩ := Multiset.mem_bind.1 hy
      obtain ⟨y', hy', hz'⟩ := (Multiset.mem_filterMap _ _).1 hz
      obtain ⟨b, hb, hbz⟩ := majL_headC? _ y' z hz' (h2 bc c hc y' hy')
      exact (MajL.flatMap hb (hg (.inr b) z hbz y hyz)).mono fun _ hb' =>
        List.mem_append_right _ hb'

/-- Soundness of the composite with a realized axiom: the majorant of the axiom applied to the
majorant of its premise. -/
theorem comp_maj {φ ψ : Form I} {Γ : Fin n → Form I} (E : (ctx Γ).Hom φ.dn)
    (f : φ.dn.Hom ψ.dn) {R : ℕ → I → Prop} (g : HomMaj R φ ψ f) {m : ℕ} {i : I} (hi : R m i)
    (w : (ctx Γ).W i) (b : φ.B) (kb : φ.Bc → ∀ k, List (Γ k).Bc)
    (h : Maj φ i b (E.fwd i w) ∧ ∀ bc c, MajC φ i bc (E.fwd i w) c →
      ∀ y ∈ E.back i w c, MajL (Γ y.1) i (kb bc y.1) (w y.1) y.2) :
    Maj ψ i (g.1.1 m b) ((Hom.comp E f).fwd i w) ∧
    ∀ bc c, MajC ψ i bc ((Hom.comp E f).fwd i w) c → ∀ y ∈ (Hom.comp E f).back i w c,
      MajL (Γ y.1) i ((g.1.2 m b bc).flatMap fun b' => kb b' y.1) (w y.1) y.2 := by
  obtain ⟨h1, h2⟩ := g.2 m i hi _ b h.1
  refine ⟨h1, fun bc c hc y hy => ?_⟩
  obtain ⟨x, hx, hyx⟩ := Multiset.mem_bind.1 hy
  obtain ⟨b', hb', hbx⟩ := h2 bc c hc x hx
  exact MajL.flatMap hb' (h.2 b' x hbx y hyx)

/-- **Soundness of the monotone interpretation.** At a point `i` that the environment `R m`
admits, if `hm` majorizes the witnesses `w` of the hypotheses, the bound of a derivation
majorizes its realizer, and its counter-witness majorants cover the counter-witnesses of the
hypotheses that the realizer demands. Every rule is covered; the realized axioms `hom`, `ac`,
`ip`, `markov` through the majorants of their realizers. -/
theorem bnd_sound {Γ : Fin n → Form I} {φ : Form I} (d : Deriv Γ φ) (R : ℕ → I → Prop)
    (hR : Monotone R) (D : MajD d R) (hm : CtxB Γ) (m : ℕ) (i : I) (hi : R m i)
    (w : (ctx Γ).W i) (hw : ∀ k, Maj (Γ k) i (hm k) (w k)) :
    Maj φ i (bnd d R D hm m).1 (d.realize.fwd i w) ∧
    ∀ bc c, MajC φ i bc (d.realize.fwd i w) c → ∀ y ∈ d.realize.back i w c,
      MajL (Γ y.1) i ((bnd d R D hm m).2 bc y.1) (w y.1) y.2 := by
  induction d generalizing m with
  | hyp k =>
    refine ⟨hw k, fun bc c hc y hy => ?_⟩
    have hy' : y = ⟨k, c⟩ := Multiset.mem_singleton.1 hy
    subst hy'
    exact ⟨bc, by simp [bnd], hc⟩
  | topI => exact ⟨trivial, fun _ _ _ y hy => by simp [realize] at hy⟩
  | andI d e ihd ihe =>
    obtain ⟨hd1, hd2⟩ := ihd R hR D.1 hm m i hi w hw
    obtain ⟨he1, he2⟩ := ihe R hR D.2 hm m i hi w hw
    refine ⟨⟨hd1, he1⟩, fun bc c hc y hy => ?_⟩
    rcases bc with b | b <;> rcases c with c | c
    · exact hd2 b c hc y hy
    · exact False.elim hc
    · exact False.elim hc
    · exact he2 b c hc y hy
  | andE₁ d ih =>
    obtain ⟨h1, h2⟩ := ih R hR D hm m i hi w hw
    exact ⟨h1.1, fun bc c hc y hy => h2 (.inl bc) (.inl c) hc y hy⟩
  | andE₂ d ih =>
    obtain ⟨h1, h2⟩ := ih R hR D hm m i hi w hw
    exact ⟨h1.2, fun bc c hc y hy => h2 (.inr bc) (.inr c) hc y hy⟩
  | impI d ih =>
    refine ⟨fun a ba ha => ?_, fun bc c hc y hy => ?_⟩
    · obtain ⟨h1, h2⟩ := ih R hR D (consB ba hm) m i hi (consW i a w) (maj_consW ha hw)
      refine ⟨h1, fun bc c hc x hx => ?_⟩
      obtain ⟨y, hy, hyx⟩ := (Multiset.mem_filterMap _ _).1 hx
      exact majL_headC? _ y x hyx (h2 bc c hc y hy)
    · obtain ⟨h1, h2⟩ := ih R hR D (consB bc.1 hm) m i hi (consW i c.1 w) (maj_consW hc.1 hw)
      obtain ⟨y', hy', hyx⟩ := (Multiset.mem_filterMap _ _).1 hy
      exact majL_tailC? _ y' y hyx (h2 bc.2 c.2 hc.2 y' hy')
  | impE d e ihd ihe =>
    obtain ⟨hd1, hd2⟩ := ihd R hR D.1 hm m i hi w hw
    obtain ⟨he1, he2⟩ := ihe R hR D.2 hm m i hi w hw
    obtain ⟨h1, h2⟩ := hd1 _ _ he1
    refine ⟨h1, fun bc c hc y hy => ?_⟩
    rcases Multiset.mem_add.1 hy with hy | hy
    · exact (hd2 (_, bc) ⟨_, c⟩ ⟨he1, hc⟩ y hy).mono fun _ hb => List.mem_append_left _ hb
    · obtain ⟨x, hx, hyx⟩ := Multiset.mem_bind.1 hy
      obtain ⟨b, hb, hbx⟩ := h2 bc c hc x hx
      exact (MajL.flatMap hb (he2 b x hbx y hyx)).mono fun _ hb' => List.mem_append_right _ hb'
  | orI₁ d ih =>
    obtain ⟨h1, h2⟩ := ih R hR D hm m i hi w hw
    refine ⟨h1, fun bc c hc y hy => ?_⟩
    rcases bc with b | b
    · exact h2 b c hc y hy
    · exact False.elim hc
  | orI₂ d ih =>
    obtain ⟨h1, h2⟩ := ih R hR D hm m i hi w hw
    refine ⟨h1, fun bc c hc y hy => ?_⟩
    rcases bc with b | b
    · exact False.elim hc
    · exact h2 b c hc y hy
  | orE d e₁ e₂ ihd ih₁ ih₂ =>
    obtain ⟨hd1, hd2⟩ := ihd R hR D.1 hm m i hi w hw
    exact orCase_maj _ _ i w _ _ hd1 _ _ hd2 _ _ _ _
      (fun a ha => ih₁ R hR D.2.1 _ m i hi (consW i a w) (maj_consW ha hw))
      (fun a ha => ih₂ R hR D.2.2 _ m i hi (consW i a w) (maj_consW ha hw))
  | allI d ih =>
    refine ⟨fun k m' hk => (ih _ (envExt_mono hR _) D hm (max m m') ⟨i, k⟩
      ⟨hR (le_max_left _ _) i hi, hk.trans (le_max_right _ _)⟩ w hw).1,
      fun bc c hc y hy => ?_⟩
    exact (ih _ (envExt_mono hR _) D hm (max m bc.1) ⟨i, c.1⟩
      ⟨hR (le_max_left _ _) i hi, hc.1.trans (le_max_right _ _)⟩ w hw).2 bc.2 c.2 hc.2 y hy
  | allE t d ih =>
    obtain ⟨h1, h2⟩ := ih R hR D.2 hm m i hi w hw
    have ht := D.1.2 m i hi
    exact ⟨h1 (t i) _ ht, fun bc c hc y hy => h2 (D.1.1 m, bc) ⟨t i, c⟩ ⟨ht, hc⟩ y hy⟩
  | exI t d ih =>
    obtain ⟨h1, h2⟩ := ih R hR D.2 hm m i hi w hw
    exact ⟨⟨D.1.2 m i hi, h1⟩, fun bc c hc y hy => h2 bc c hc y hy⟩
  | @exE _ _ Γ' _ _ _ _ d e ihd ihe =>
    obtain ⟨hd1, hd2⟩ := ihd R hR D.1 hm m i hi w hw
    obtain ⟨he1, he2⟩ := ihe _ (envExt_mono hR _) D.2 (consB _ hm) _ _
      ⟨hR (le_max_left _ _) i hi, hd1.1.trans (le_max_right _ _)⟩
      (consW (Γ := fun k => (Γ' k).sub Sigma.fst) ⟨i, (d.realize.fwd i w).1⟩
        (d.realize.fwd i w).2 w)
      (maj_consW hd1.2 hw)
    refine ⟨he1, fun bc c hc y hy => ?_⟩
    rcases Multiset.mem_add.1 hy with hy | hy
    · obtain ⟨y', hy', rfl⟩ := Multiset.mem_map.1 hy
      obtain ⟨y'', hy'', hyy⟩ := (Multiset.mem_filterMap _ _).1 hy'
      exact (majL_tailC? _ y'' y' hyy (he2 bc c hc y'' hy'')).mono fun _ hb =>
        List.mem_append_left _ hb
    · obtain ⟨z, hz, hyz⟩ := Multiset.mem_bind.1 hy
      obtain ⟨y', hy', hz'⟩ := (Multiset.mem_filterMap _ _).1 hz
      obtain ⟨b, hb, hbz⟩ := majL_headC? _ y' z hz' (he2 bc c hc y' hy')
      exact (MajL.flatMap hb (hd2 b z hbz y hyz)).mono fun _ hb' => List.mem_append_right _ hb'
  | ac d ih => exact comp_maj _ _ D.2 hi w _ _ (ih R hR D.1 hm m i hi w hw)
  | ip p hL d ih => exact comp_maj _ _ D.2 hi w _ _ (ih R hR D.1 hm m i hi w hw)
  | markov p q d ih => exact comp_maj _ _ D.2 hi w _ _ (ih R hR D.1 hm m i hi w hw)
  | hom f N hN hev d ih => exact comp_maj _ _ D.2 hi w _ _ (ih R hR D.1 hm m i hi w hw)
  | atom₂ h d e ihd ihe =>
    refine ⟨trivial, fun bc c hc y hy => ?_⟩
    rcases Multiset.mem_add.1 hy with hy | hy
    · exact ((ihd R hR D.1 hm m i hi w hw).2 () PUnit.unit trivial y hy).mono fun _ hb =>
        List.mem_append_left _ hb
    · exact ((ihe R hR D.2 hm m i hi w hw).2 () PUnit.unit trivial y hy).mono fun _ hb =>
        List.mem_append_right _ hb

end Deriv

/-! ## Bound extraction at the Π⁰₂ level -/

/-- The monotone bound of a majorant of `∀ x, ∃ y, r (x, y)`: the partial maxima of its bounds on
the size of `y`. -/
def pi2Bound (b : ℕ → ℕ × Unit) : ℕ →o ℕ := partialSups fun m => (b m).1

namespace Deriv

section Pi2

variable {X : I → Type u} {Y : (Σ i, X i) → Type u} {r : (Σ x : Σ i, X i, Y x) → Prop}
  {sX : ∀ i, X i → ℕ} {sY : ∀ x, Y x → ℕ}

/-- A witness of `∀ x, ∃ y, a (x, y)` given by an oracle `g` is majorized by a cost majorant
`G` of the size of `g` along the size of its argument. -/
theorem maj_allEx_of_costMaj {a : (Σ x : Σ i, X i, Y x) → Prop} {i : I}
    {g : ∀ x : X i, Y ⟨i, x⟩} {G : ℕ → ℕ} (hG : CostMaj (sX i) G fun x => sY ⟨i, x⟩ (g x)) :
    Maj (allEx sX sY a) i (fun m => (G m, ())) (fun x => ⟨g x, PUnit.unit⟩) :=
  fun _ _ hx => ⟨hG.le hx, trivial⟩

/-- **Bound extraction.** The bound `pi2Bound` of a derivation of `∀ x, ∃ y, r (x, y)` is a cost
majorant of the size of the realizer along the size of the argument. It is computed from the
majorants `hm` of the hypotheses and the majorant data `D`, and not from the realizer. -/
theorem allEx_costMaj {Γ : Fin n → Form I} (d : Deriv Γ (allEx (X := X) (Y := Y) sX sY r))
    (R : ℕ → I → Prop) (hR : Monotone R) (D : MajD d R) (hm : CtxB Γ) (m₀ : ℕ) (i : I)
    (hi : R m₀ i) (w : (ctx Γ).W i) (hw : ∀ k, Maj (Γ k) i (hm k) (w k)) :
    CostMaj (sX i) (pi2Bound (bnd d R D hm m₀).1)
      (fun x => sY ⟨i, x⟩ (d.realize.fwd i w x).1) := by
  refine ⟨(pi2Bound _).monotone, fun x => ?_⟩
  have h := (bnd_sound d R hR D hm m₀ i hi w hw).1 x (sX i x) le_rfl
  exact h.1.trans (le_partialSups (fun m => ((bnd d R D hm m₀).1 m).1) (sX i x))

/-- **Π⁰₂ bound.** When the witnesses of the hypotheses withstand every counter-witness, every
`x` has a `y` with `r (x, y)` of size at most the bound at the size of `x`. -/
theorem exists_le_pi2Bound {Γ : Fin n → Form I} (d : Deriv Γ (allEx (X := X) (Y := Y) sX sY r))
    (R : ℕ → I → Prop) (hR : Monotone R) (D : MajD d R) (hm : CtxB Γ) (m₀ : ℕ) (i : I)
    (hi : R m₀ i) (w : (ctx Γ).W i) (hw : ∀ k, Maj (Γ k) i (hm k) (w k))
    (hmat : ∀ c, (ctx Γ).mat i w c) (x : X i) :
    ∃ y : Y ⟨i, x⟩, sY ⟨i, x⟩ y ≤ pi2Bound (bnd d R D hm m₀).1 (sX i x) ∧ r ⟨⟨i, x⟩, y⟩ :=
  ⟨(d.realize.fwd i w x).1, (allEx_costMaj d R hR D hm m₀ i hi w hw).2 x,
    d.realize.sound i w ⟨x, PUnit.unit⟩ fun y _ => hmat y⟩

end Pi2

end Deriv

namespace CDeriv

section Pi2

variable {K : I → Type u} {L : (Σ i, K i) → Type u} (p : (Σ x : Σ i, K i, L x) → Prop)
  (sel : ∀ x : Σ i, K i, Multiset (L x) → L x)
  (hsel : ∀ x ys, ((∀ y ∈ ys, ¬ p ⟨x, y⟩) → False) → p ⟨x, sel x ys⟩)
  (sM : ∀ x : Σ i, K i, Multiset (L x) → ℕ)
  {sX : ∀ i, K i → ℕ} {sY : ∀ x, L x → ℕ}

/-- **Bound extraction from classical derivations.** The bound of the extracted derivation
`pi2` is a cost majorant of the size of the extracted function along the size of the argument. -/
theorem extract_costMaj {Γ : Fin n → Form I}
    (c : CDeriv Γ (Deriv.allEx (X := K) (Y := L) sX sY p))
    (R : ℕ → I → Prop) (hR : Monotone R) (D : Deriv.MajD (pi2 p sel hsel sM c) R)
    (hm : CtxB fun k => (Γ k).negT) (m₀ : ℕ) (i : I) (hi : R m₀ i)
    (w : (ctx fun k => (Γ k).negT).W i) (hw : ∀ k, Maj (Γ k).negT i (hm k) (w k)) :
    CostMaj (sX i) (pi2Bound (Deriv.bnd (pi2 p sel hsel sM c) R D hm m₀).1)
      (fun x => sY ⟨i, x⟩ (extract p sel hsel sM c i w x)) :=
  Deriv.allEx_costMaj _ R hR D hm m₀ i hi w hw

/-- **Π⁰₂ bound for classical derivations.** -/
theorem exists_le_extract_pi2Bound {Γ : Fin n → Form I}
    (c : CDeriv Γ (Deriv.allEx (X := K) (Y := L) sX sY p)) (R : ℕ → I → Prop) (hR : Monotone R)
    (D : Deriv.MajD (pi2 p sel hsel sM c) R) (hm : CtxB fun k => (Γ k).negT) (m₀ : ℕ) (i : I)
    (hi : R m₀ i) (w : (ctx fun k => (Γ k).negT).W i)
    (hw : ∀ k, Maj (Γ k).negT i (hm k) (w k))
    (hmat : ∀ c', (ctx fun k => (Γ k).negT).mat i w c') (x : K i) :
    ∃ y : L ⟨i, x⟩, sY ⟨i, x⟩ y ≤
        pi2Bound (Deriv.bnd (pi2 p sel hsel sM c) R D hm m₀).1 (sX i x) ∧
      p ⟨⟨i, x⟩, y⟩ :=
  Deriv.exists_le_pi2Bound _ R hR D hm m₀ i hi w hw hmat x

end Pi2

end CDeriv

/-! ## Example: a noncomputable realizer with a computable bound -/

/-- The formula `∀ x, ∃ y, r (x, y)` over numbers, with each number of size itself. -/
abbrev allExNat (r : (Σ _ : (Σ _ : PUnit.{1}, ℕ), ℕ) → Prop) : Form PUnit.{1} :=
  Deriv.allEx (X := fun _ : PUnit.{1} => ℕ) (Y := fun _ => ℕ) (fun _ => id) (fun _ => id) r

/-- The relation: `y` is a prime divisor of `x + 2`. -/
def primeDivRel (z : Σ _ : (Σ _ : PUnit.{1}, ℕ), ℕ) : Prop := z.2.Prime ∧ z.2 ∣ z.1.2 + 2

/-- Every `x + 2` has a prime divisor. -/
theorem exists_primeDiv (x : ℕ) : ∃ y : ℕ, y.Prime ∧ y ∣ x + 2 :=
  Nat.exists_prime_and_dvd (by omega)

/-- The realized axiom `∀ x, ∃ y, y prime ∧ y ∣ x + 2`, whose realizer chooses a prime divisor
by `Classical.choose`. -/
noncomputable def primeDivHom : (Form.top : Form PUnit.{1}).dn.Hom
    (allExNat primeDivRel).dn where
  fwd _ _ x := ⟨Classical.choose (exists_primeDiv x), PUnit.unit⟩
  back _ _ _ := 0
  sound _ _ c _ := Classical.choose_spec (exists_primeDiv c.1)

/-- The derivation of `∀ x, ∃ y, y prime ∧ y ∣ x + 2` by the realized axiom `primeDivHom`. -/
noncomputable def primeDiv : Deriv (fun _ : Fin 0 => (Form.top : Form PUnit.{1}))
    (allExNat primeDivRel) :=
  .hom primeDivHom 0 (fun _ _ _ => by simp [primeDivHom]) (fun _ _ x => exists_primeDiv x) .topI

/-- The majorant data of `primeDiv`: the majorant `m ↦ m + 2` of the realizer. -/
def primeDivMajD : Deriv.MajD primeDiv (fun _ _ => True) :=
  ((), ⟨(fun _ _ m => (m + 2, ()), fun _ _ _ => []), by
    intro _ _ _ _ _ _
    refine ⟨fun x m hx => ⟨?_, trivial⟩, fun _ _ _ y hy => ?_⟩
    · have h := Classical.choose_spec (exists_primeDiv x)
      have := Nat.le_of_dvd (by omega) h.2
      change Classical.choose (exists_primeDiv x) ≤ m + 2
      exact this.trans (Nat.add_le_add_right hx 2)
    · simp [primeDivHom] at hy⟩)

/-- The bound extracted from `primeDiv` is `m ↦ m + 2`. -/
theorem primeDiv_pi2Bound (m : ℕ) :
    pi2Bound (Deriv.bnd primeDiv _ primeDivMajD (fun k => k.elim0) 0).1 m = m + 2 := by
  change partialSups (fun m : ℕ => m + 2) m = m + 2
  rw [Monotone.partialSups_eq fun _ _ h => by omega]

/-- The prime divisor of `x + 2` given by the realizer of `primeDiv` is at most `x + 2`, by the
extracted bound. -/
theorem primeDiv_exists_le (x : ℕ) : ∃ y : ℕ, y ≤ x + 2 ∧ y.Prime ∧ y ∣ x + 2 := by
  obtain ⟨y, hy, hp⟩ := Deriv.exists_le_pi2Bound primeDiv (fun _ _ => True)
    (fun _ _ _ _ _ => trivial) primeDivMajD (fun k => k.elim0) 0 PUnit.unit trivial
    (fun k => k.elim0) (fun k => k.elim0) (fun c => c.1.elim0) x
  rw [primeDiv_pi2Bound] at hy
  exact ⟨y, hy, hp⟩

end CatCrypt.Container.DNLogic
