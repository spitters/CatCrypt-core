/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Container.CodeRel
public import CatCryptCore.Container.DNGraded
public import Mathlib.Data.Multiset.Bind

/-!
# Squares of Diller–Nahm morphisms over signature relations

A signature relation `S : SigRel P Q` relates the shapes of two containers and, over related
shapes, their positions. A square of lenses over `S` and `S'` sends related shapes to related
shapes and pulls related positions back to related positions (`SigRel.Square`). A square of
Diller–Nahm morphisms (`SigRel.DNSquare`) pulls related positions back to multisets related by
the relation lifting of the finite multiset functor, `Multiset.Rel`: two multisets are related
when their elements can be paired by the relation (Gumm and Schröder, *Monoids, labeled
transition systems, and coalgebras*, CMCS 2001, for the lifting of the multiset functor).

The lifted relation `SigRel.bang S` relates the multiset exponentials, and a square of
Diller–Nahm morphisms is a square of the lenses out of the exponentials
(`SigRel.dnSquare_iff_square_bang`). The action of the exponential, its counit and
comultiplication, weakening, contraction and the Seely isomorphism are squares, and so are the
structure maps of the graded exponential `bangLE`.

Along a square, related prices give equal prices of related demands, grades transport, and count
matrices are reindexed by the bijections of related positions. The use bound of a free-monad tree
transfers along the heterogeneous lift `HFreeRel` (`HFreeRel.useBound`).

## Main definitions

* `SigRel.Square`, `SigRel.DNSquare` — squares of lenses and of Diller–Nahm morphisms;
* `SigRel.bang`, `SigRel.bangLE` — the relation lifted to the exponential and to its grades;
* `SigRel.unit`, `SigRel.tensor`, `SigRel.mul` — the relations on `y`, on `⊗` and on `*`;
* `SigRel.clock`, `SigRel.tok` — the relations of the clock and token objects.

## Main results

* `SigRel.DNSquare.id`, `SigRel.DNSquare.comp`, `SigRel.DNSquare.ofLens` — the category of
  squares;
* `SigRel.dnSquare_iff_square_bang` — the squares of the co-Kleisli category;
* `SigRel.square_bangMap`, `SigRel.square_bangCounit`, `SigRel.square_bangComult`,
  `SigRel.square_bangContr`, `SigRel.square_bangWeak`, `SigRel.square_seely`,
  `SigRel.square_seely_inv` and their graded forms;
* `SigRel.DNSquare.price_eq`, `SigRel.DNSquare.price_le`, `SigRel.DNSquare.usesLE`,
  `SigRel.DNSquare.countMat_eq` — prices, grades and count matrices along a square;
* `Clocked.dnSquare_clock_iff`, `Costed.dnSquare_clock_iff`, `VecCosted.dnSquare_tok_iff` —
  squares of costed functions;
* `HFreeRel.useBound` — use bounds transfer along the heterogeneous lift;
* `demandLens_dnSquare_iff` — squares of fixed demands.

Search words: Diller–Nahm, relational parametricity, relation lifting, multiset relator,
signature relation, square, exponential, Seely isomorphism, price, count matrix, use bound,
query bound, transfer.
-/

set_option autoImplicit false

@[expose] public section

universe u v w u₁ v₁ u₂ v₂ u₃ v₃ u₄ v₄ u₅ v₅ u₆ v₆

namespace CatCrypt.Container

open PFunctor

/-! ## Multiset lemmas -/

namespace Multiset

variable {α : Type u} {β : Type v} {γ : Type w} {δ : Type u₁}

/-- Related elements give related singletons. -/
theorem rel_singleton_of {r : α → β → Prop} {a : α} {b : β} (h : r a b) :
    _root_.Multiset.Rel r {a} {b} :=
  _root_.Multiset.Rel.cons h _root_.Multiset.Rel.zero

/-- The relation lifting commutes with `filterMap` along maps that relate related elements in
`Option.Rel`. -/
theorem rel_filterMap {r : α → β → Prop} {p : γ → δ → Prop} {f : α → Option γ}
    {g : β → Option δ} (hfg : ∀ a b, r a b → Option.Rel p (f a) (g b))
    {s : _root_.Multiset α} {t : _root_.Multiset β} (h : _root_.Multiset.Rel r s t) :
    _root_.Multiset.Rel p (s.filterMap f) (t.filterMap g) := by
  induction h with
  | zero => simp
  | @cons a b _ _ hab _ ih =>
    have hab' := hfg a b hab
    rcases hfa : f a with _ | c <;> rcases hgb : g b with _ | d <;> rw [hfa, hgb] at hab'
    · rw [_root_.Multiset.filterMap_cons_none _ _ hfa,
        _root_.Multiset.filterMap_cons_none _ _ hgb]
      exact ih
    · cases hab'
    · cases hab'
    · cases hab' with
      | some hcd =>
        rw [_root_.Multiset.filterMap_cons_some _ _ _ hfa,
          _root_.Multiset.filterMap_cons_some _ _ _ hgb]
        exact ih.cons hcd

/-- Related multisets of natural numbers in the order `≥` have sums in that order. -/
theorem sum_le_sum_of_rel {s t : _root_.Multiset ℕ}
    (h : _root_.Multiset.Rel (fun a b => b ≤ a) s t) : t.sum ≤ s.sum := by
  induction h with
  | zero => simp
  | cons hab _ ih => grind [_root_.Multiset.sum_cons]

end Multiset

/-! ## Squares of lenses and of Diller–Nahm morphisms -/

section Squares

variable {P : PFunctor.{u₁, v₁}} {Q : PFunctor.{u₂, v₂}} {P' : PFunctor.{u₃, v₃}}
  {Q' : PFunctor.{u₄, v₄}} {P'' : PFunctor.{u₅, v₅}} {Q'' : PFunctor.{u₆, v₆}}

/-- The square of signature relations over a pair of lenses: related shapes go to related shapes,
and related positions pull back to related positions. -/
structure SigRel.Square (S : SigRel P Q) (S' : SigRel P' Q') (f : Lens P P') (g : Lens Q Q') :
    Prop where
  /-- Related shapes go to related shapes. -/
  shape : ∀ {a b}, S.pos a b → S'.pos (f.toFunA a) (g.toFunA b)
  /-- Related positions pull back to related positions. -/
  pos : ∀ {a b}, S.pos a b → ∀ d' e', S'.dir (f.toFunA a) (g.toFunA b) d' e' →
    S.dir a b (f.toFunB a d') (g.toFunB b e')

/-- A square of Diller–Nahm morphisms over signature relations: forward maps preserve the relation
of shapes, and the demands of related positions are related by the multiset lifting. -/
structure SigRel.DNSquare (S : SigRel P Q) (S' : SigRel P' Q') (F : DNLens P P')
    (G : DNLens Q Q') : Prop where
  /-- Related shapes go to related shapes. -/
  shape : ∀ {a b}, S.pos a b → S'.pos (F.toFunA a) (G.toFunA b)
  /-- Related positions demand related multisets. -/
  pos : ∀ {a b}, S.pos a b → ∀ d' e', S'.dir (F.toFunA a) (G.toFunA b) d' e' →
    Multiset.Rel (S.dir a b) (F.toFunB a d') (G.toFunB b e')

/-- The identity square. -/
theorem SigRel.DNSquare.id (S : SigRel P Q) : S.DNSquare S (DNLens.id P) (DNLens.id Q) where
  shape h := h
  pos _ _ _ hde := Multiset.rel_singleton_of hde

/-- Squares compose; the demands compose by `Multiset.rel_bind`. -/
theorem SigRel.DNSquare.comp {S : SigRel P Q} {S' : SigRel P' Q'} {S'' : SigRel P'' Q''}
    {F : DNLens P P'} {G : DNLens Q Q'} {F' : DNLens P' P''} {G' : DNLens Q' Q''}
    (s : S.DNSquare S' F G) (s' : S'.DNSquare S'' F' G') :
    S.DNSquare S'' (DNLens.comp F' F) (DNLens.comp G' G) where
  shape h := s'.shape (s.shape h)
  pos h d e hde := Multiset.rel_bind (fun _ _ h' => s.pos h _ _ h') (s'.pos (s.shape h) d e hde)

/-- A square of lenses is a square of the Diller–Nahm morphisms they induce. -/
theorem SigRel.DNSquare.ofLens {S : SigRel P Q} {S' : SigRel P' Q'} {f : Lens P P'}
    {g : Lens Q Q'} (s : SigRel.Square S S' f g) :
    S.DNSquare S' (DNLens.ofLens f) (DNLens.ofLens g) where
  shape h := s.shape h
  pos h d e hde := Multiset.rel_singleton_of (s.pos h d e hde)

/-- The relation lifted to the exponentials: related shapes, and multisets related by the
multiset lifting of the relation of positions. -/
def SigRel.bang (S : SigRel P Q) : SigRel (bang P) (bang Q) where
  pos := S.pos
  dir a b := Multiset.Rel (S.dir a b)

/-- A square of Diller–Nahm morphisms is a square of the lenses out of the exponentials. -/
theorem SigRel.dnSquare_iff_square_bang {S : SigRel P Q} {S' : SigRel P' Q'} {F : DNLens P P'}
    {G : DNLens Q Q'} :
    S.DNSquare S' F G ↔ SigRel.Square S.bang S' F.toBangLens G.toBangLens :=
  ⟨fun s => ⟨s.shape, s.pos⟩, fun s => ⟨s.shape, s.pos⟩⟩

end Squares

/-! ## The exponential and its structure maps as squares -/

section BangSquares

variable {P : PFunctor.{u₁, v₁}} {Q : PFunctor.{u₂, v₂}} {P' : PFunctor.{u₃, v₃}}
  {Q' : PFunctor.{u₄, v₄}}

/-- The relation on the unit `y`: all shapes and all positions are related. -/
def SigRel.unit : SigRel y.{u₁, v₁} y.{u₂, v₂} where
  pos _ _ := True
  dir _ _ _ _ := True

/-- The relation on parallel products: shapes and positions related componentwise. -/
def SigRel.tensor (S : SigRel P Q) (S' : SigRel P' Q') : SigRel (P ⊗ P') (Q ⊗ Q') where
  pos a b := S.pos a.1 b.1 ∧ S'.pos a.2 b.2
  dir a b d e := S.dir a.1 b.1 d.1 e.1 ∧ S'.dir a.2 b.2 d.2 e.2

/-- The exponential of a square of lenses is a square. -/
theorem SigRel.square_bangMap {S : SigRel P Q} {S' : SigRel P' Q'} {f : Lens P P'}
    {g : Lens Q Q'} (s : SigRel.Square S S' f g) :
    SigRel.Square S.bang S'.bang (bangMap f) (bangMap g) where
  shape h := s.shape h
  pos h _ _ hde := by
    simp only [SigRel.bang, bangMap] at hde ⊢
    exact Multiset.rel_map.2 (hde.mono fun _ _ _ _ h' => s.pos h _ _ h')

/-- The counit of the exponential is a square. -/
theorem SigRel.square_bangCounit (S : SigRel P Q) :
    SigRel.Square S.bang S (bangCounit P) (bangCounit Q) where
  shape h := h
  pos _ _ _ hde := Multiset.rel_singleton_of hde

/-- The comultiplication of the exponential is a square. -/
theorem SigRel.square_bangComult (S : SigRel P Q) :
    SigRel.Square S.bang S.bang.bang (bangComult P) (bangComult Q) where
  shape h := h
  pos _ _ _ hde := Multiset.rel_join hde

/-- Contraction is a square. -/
theorem SigRel.square_bangContr (S : SigRel P Q) :
    SigRel.Square S.bang (S.bang.tensor S.bang) (bangContr P) (bangContr Q) where
  shape h := ⟨h, h⟩
  pos _ _ _ hde := hde.1.add hde.2

/-- Weakening is a square. -/
theorem SigRel.square_bangWeak (S : SigRel P Q) :
    SigRel.Square S.bang SigRel.unit (bangWeak P) (bangWeak Q) where
  shape _ := trivial
  pos _ _ _ _ := Multiset.Rel.zero

end BangSquares

/-! ## The Seely isomorphism as a square -/

section Seely

variable {P Q P' Q' : PFunctor.{u, v}}

/-- The relation on cartesian products: shapes related componentwise, and positions related on
the sum. -/
def SigRel.mul (S : SigRel P Q) (S' : SigRel P' Q') : SigRel (P * P') (Q * Q') where
  pos a b := S.pos a.1 b.1 ∧ S'.pos a.2 b.2
  dir a b := Sum.LiftRel (S.dir a.1 b.1) (S'.dir a.2 b.2)

/-- The Seely isomorphism is a square. -/
theorem SigRel.square_seely (S : SigRel P Q) (S' : SigRel P' Q') :
    SigRel.Square (S.mul S').bang (S.bang.tensor S'.bang) (seely P P').toLens
      (seely Q Q').toLens where
  shape h := h
  pos _ _ _ hde :=
    (Multiset.rel_map.2 (hde.1.mono fun _ _ _ _ h => Sum.LiftRel.inl h)).add
      (Multiset.rel_map.2 (hde.2.mono fun _ _ _ _ h => Sum.LiftRel.inr h))

/-- The inverse of the Seely isomorphism is a square. -/
theorem SigRel.square_seely_inv (S : SigRel P Q) (S' : SigRel P' Q') :
    SigRel.Square (S.bang.tensor S'.bang) (S.mul S').bang (seely P P').invLens
      (seely Q Q').invLens where
  shape h := h
  pos _ _ _ hde :=
    ⟨Multiset.rel_filterMap (fun _ _ h => by
        cases h with | inl h => exact .some h | inr _ => exact .none) hde,
      Multiset.rel_filterMap (fun _ _ h => by
        cases h with | inl _ => exact .none | inr h => exact .some h) hde⟩

end Seely

/-! ## The graded exponential -/

section Graded

variable {P : PFunctor.{u₁, v₁}} {Q : PFunctor.{u₂, v₂}} {P' : PFunctor.{u₃, v₃}}
  {Q' : PFunctor.{u₄, v₄}}

/-- The relation lifted to the graded exponential at grade `N`: related shapes, and bounded
multisets related by the multiset lifting. -/
def SigRel.bangLE (N : ℕ∞) (S : SigRel P Q) : SigRel (bangLE N P) (bangLE N Q) where
  pos := S.pos
  dir a b m n := Multiset.Rel (S.dir a b) m.1 n.1

/-- The graded exponential of a square of lenses is a square. -/
theorem SigRel.square_bangLE_map (N : ℕ∞) {S : SigRel P Q} {S' : SigRel P' Q'} {f : Lens P P'}
    {g : Lens Q Q'} (s : SigRel.Square S S' f g) :
    SigRel.Square (S.bangLE N) (S'.bangLE N) (bangLE.map N f) (bangLE.map N g) where
  shape h := s.shape h
  pos h _ _ hde := Multiset.rel_map.2 (hde.mono fun _ _ _ _ h' => s.pos h _ _ h')

/-- The counit at grade `1` is a square. -/
theorem SigRel.square_bangLE_counit (S : SigRel P Q) :
    SigRel.Square (S.bangLE 1) S (bangLE.counit P) (bangLE.counit Q) where
  shape h := h
  pos _ _ _ hde := Multiset.rel_singleton_of hde

/-- The comultiplication at grade `m * n` is a square. -/
theorem SigRel.square_bangLE_comult (m n : ℕ∞) (S : SigRel P Q) :
    SigRel.Square (S.bangLE (m * n)) ((S.bangLE n).bangLE m) (bangLE.comult m n P)
      (bangLE.comult m n Q) where
  shape h := h
  pos _ _ _ hde := Multiset.rel_bind (fun _ _ h => h) hde

/-- Contraction at grade `m + n` is a square. -/
theorem SigRel.square_bangLE_contr (m n : ℕ∞) (S : SigRel P Q) :
    SigRel.Square (S.bangLE (m + n)) ((S.bangLE m).tensor (S.bangLE n)) (bangLE.contr m n P)
      (bangLE.contr m n Q) where
  shape h := ⟨h, h⟩
  pos _ _ _ hde := hde.1.add hde.2

/-- Weakening at grade `0` is a square. -/
theorem SigRel.square_bangLE_weak (S : SigRel P Q) :
    SigRel.Square (S.bangLE 0) SigRel.unit (bangLE.weak P) (bangLE.weak Q) where
  shape _ := trivial
  pos _ _ _ _ := Multiset.Rel.zero

/-- The inclusion of grades is a square. -/
theorem SigRel.square_bangLE_sub {m n : ℕ∞} (hnm : n ≤ m) (S : SigRel P Q) :
    SigRel.Square (S.bangLE m) (S.bangLE n) (bangLE.sub hnm P) (bangLE.sub hnm Q) where
  shape h := h
  pos _ _ _ hde := hde

/-- The map from the exponential to the graded exponential is a square. -/
theorem SigRel.square_bangLE_ofBang (N : ℕ∞) (S : SigRel P Q) :
    SigRel.Square S.bang (S.bangLE N) (bangLE.ofBang N P) (bangLE.ofBang N Q) where
  shape h := h
  pos _ _ _ hde := hde

end Graded

/-! ## Prices, grades and count matrices along a square -/

section Transport

variable {P : PFunctor.{u₁, v₁}} {Q : PFunctor.{u₂, v₂}} {P' : PFunctor.{u₃, v₃}}
  {Q' : PFunctor.{u₄, v₄}} {S : SigRel P Q} {S' : SigRel P' Q'} {F : DNLens P P'}
  {G : DNLens Q Q'}

/-- Related prices give equal prices of related demands. -/
theorem SigRel.DNSquare.price_eq (s : S.DNSquare S' F G) {p : ∀ a, P.B a → ℕ}
    {p' : ∀ b, Q.B b → ℕ} (hp : ∀ a b, S.pos a b → ∀ d e, S.dir a b d e → p a d = p' b e)
    {a : P.A} {b : Q.A} (h : S.pos a b) {d' : P'.B (F.toFunA a)} {e' : Q'.B (G.toFunA b)}
    (he : S'.dir (F.toFunA a) (G.toFunA b) d' e') : F.price p a d' = G.price p' b e' := by
  unfold DNLens.price
  congr 1
  exact Multiset.rel_eq.1
    (Multiset.rel_map.2 ((s.pos h d' e' he).mono fun d _ e _ hde => hp a b h d e hde))

/-- The inequational form: prices in the order `p' ≤ p` at related positions give prices of
related demands in that order. -/
theorem SigRel.DNSquare.price_le (s : S.DNSquare S' F G) {p : ∀ a, P.B a → ℕ}
    {p' : ∀ b, Q.B b → ℕ} (hp : ∀ a b, S.pos a b → ∀ d e, S.dir a b d e → p' b e ≤ p a d)
    {a : P.A} {b : Q.A} (h : S.pos a b) {d' : P'.B (F.toFunA a)} {e' : Q'.B (G.toFunA b)}
    (he : S'.dir (F.toFunA a) (G.toFunA b) d' e') : G.price p' b e' ≤ F.price p a d' :=
  Multiset.sum_le_sum_of_rel
    (Multiset.rel_map.2 ((s.pos h d' e' he).mono fun d _ e _ hde => hp a b h d e hde))

/-- Grades transport: when every shape of `G` has a related shape of `F` and every position at
the image has a related position, the grade of `F` bounds the grade of `G`. -/
theorem SigRel.DNSquare.usesLE (s : S.DNSquare S' F G) {N : P.A → ℕ∞} {N' : Q.A → ℕ∞}
    (hN : ∀ a b, S.pos a b → N a ≤ N' b) (hb : ∀ b, ∃ a, S.pos a b)
    (hd : ∀ a b, S.pos a b → ∀ e', ∃ d', S'.dir (F.toFunA a) (G.toFunA b) d' e')
    (hF : F.UsesLE N) : G.UsesLE N' := by
  intro b e'
  obtain ⟨a, h⟩ := hb b
  obtain ⟨d', hde⟩ := hd a b h e'
  rw [← Multiset.card_eq_card_of_rel (s.pos h d' e' hde)]
  exact (hF a d').trans (hN a b h)

/-- Count matrices along position bijections: the count matrix of `G` is that of `F` reindexed. -/
theorem SigRel.DNSquare.countMat_eq [∀ a, DecidableEq (P.B a)] [∀ b, DecidableEq (Q.B b)]
    (s : S.DNSquare S' F G) {a : P.A} {b : Q.A} (h : S.pos a b) (eB : P.B a ≃ Q.B b)
    (heB : ∀ d e, S.dir a b d e ↔ eB d = e) (eB' : P'.B (F.toFunA a) ≃ Q'.B (G.toFunA b))
    (heB' : ∀ d e, S'.dir (F.toFunA a) (G.toFunA b) d e ↔ eB' d = e) :
    G.countMat b = (F.countMat a).submatrix eB'.symm eB.symm := by
  ext y x
  have hr := s.pos h (eB'.symm y) y ((heB' _ _).2 (eB'.apply_symm_apply y))
  have hmap : (F.toFunB a (eB'.symm y)).map eB = G.toFunB b y :=
    Multiset.rel_eq.1 (Multiset.rel_map_left.2 (hr.mono fun d _ e _ hde => (heB d e).1 hde))
  simp only [DNLens.countMat, Matrix.of_apply, Matrix.submatrix_apply, ← hmap]
  rw [← Multiset.count_map_eq_count' eB _ eB.injective, eB.apply_symm_apply]

end Transport

/-! ## Squares of costed functions -/

section Costed

variable {X : Type u} {Y : Type v} {X₁ : Type w} {Y₁ : Type u₁}

/-- The relation of clock objects: shapes related by `R`, and equal positions. -/
def SigRel.clock {X : Type u} {X₁ : Type w} (R : X → X₁ → Prop) :
    SigRel (clockPos X) (clockPos X₁) where
  pos := R
  dir _ _ := Eq

/-- A square of the Diller–Nahm morphisms of two costed functions with use counts over clock
relations holds exactly when related arguments have related results, equal use counts and equal
costs. -/
theorem Clocked.dnSquare_clock_iff {R : X → X₁ → Prop} {S : Y → Y₁ → Prop} (h : Clocked X Y)
    (h₁ : Clocked X₁ Y₁) :
    SigRel.DNSquare (SigRel.clock R) (SigRel.clock S) h.toDN h₁.toDN ↔
      ∀ x x₁, R x x₁ → S (h.fn x) (h₁.fn x₁) ∧ h.uses x = h₁.uses x₁ ∧
        h.cost x = h₁.cost x₁ := by
  constructor
  · intro s x x₁ hx
    have he := Multiset.rel_eq.1 (s.pos hx false false rfl : Multiset.Rel Eq _ _)
    have h1 := congrArg (Multiset.count false) he
    have h2 := congrArg (Multiset.count true) he
    rw [Clocked.count_false_toDN, Clocked.count_false_toDN] at h1
    rw [Clocked.count_true_toDN, Clocked.count_true_toDN] at h2
    exact ⟨s.shape hx, h1, h2⟩
  · intro H
    refine ⟨fun hx => (H _ _ hx).1, fun hx d e hde => ?_⟩
    obtain ⟨-, hu, hc⟩ := H _ _ hx
    change d = e at hde
    subst hde
    change Multiset.Rel Eq _ _
    rw [Multiset.rel_eq]
    simp [Clocked.toDN, hu, hc]

/-- A square of the Diller–Nahm morphisms of two costed functions over clock relations holds
exactly when related arguments have related results and equal costs. -/
theorem Costed.dnSquare_clock_iff {R : X → X₁ → Prop} {S : Y → Y₁ → Prop} (h : Costed X Y)
    (h₁ : Costed X₁ Y₁) :
    SigRel.DNSquare (SigRel.clock R) (SigRel.clock S) h.toDN h₁.toDN ↔
      ∀ x x₁, R x x₁ → S (h.fn x) (h₁.fn x₁) ∧ h.cost x = h₁.cost x₁ := by
  rw [Costed.toDN, Costed.toDN, Clocked.dnSquare_clock_iff]
  simp [Costed.toClocked]

variable {ι : Type v₁}

/-- The relation of token objects: shapes related by `R`, and equal positions. -/
def SigRel.tok {X : Type u} {X₁ : Type w} (ι : Type v₁) (R : X → X₁ → Prop) :
    SigRel (VecCosted.tokPos ι X) (VecCosted.tokPos ι X₁) where
  pos := R
  dir _ _ := Eq

/-- A square of the Diller–Nahm morphisms of two costed functions with a cost for each resource
over token relations holds exactly when related arguments have related results and equal costs. -/
theorem VecCosted.dnSquare_tok_iff {R : X → X₁ → Prop} {S : Y → Y₁ → Prop}
    (h : VecCosted ι X Y) (h₁ : VecCosted ι X₁ Y₁) :
    SigRel.DNSquare (SigRel.tok ι R) (SigRel.tok ι S) h.toDN h₁.toDN ↔
      ∀ x x₁, R x x₁ → S (h.fn x) (h₁.fn x₁) ∧ h.cost x = h₁.cost x₁ := by
  constructor
  · intro s x x₁ hx
    have he := Multiset.rel_eq.1 (s.pos hx none none rfl : Multiset.Rel Eq _ _)
    refine ⟨s.shape hx, ?_⟩
    have hm : (Finsupp.toMultiset (h.cost x)).map some =
        (Finsupp.toMultiset (h₁.cost x₁)).map some := by
      simpa [VecCosted.toDN, VecCosted.tokBack] using he
    classical
    simpa using congrArg Multiset.toFinsupp (Multiset.map_injective (Option.some_injective _) hm)
  · intro H
    refine ⟨fun hx => (H _ _ hx).1, fun hx d e hde => ?_⟩
    obtain ⟨-, hc⟩ := H _ _ hx
    change d = e at hde
    subst hde
    change Multiset.Rel Eq _ _
    rw [Multiset.rel_eq]
    simp [VecCosted.toDN, hc]

end Costed

/-! ## Use bounds along the heterogeneous lift -/

section UseBound

open PFunctor.FreeM

variable {P : PFunctor.{u₁, v}} {Q : PFunctor.{u₂, v}} {ι : Type w} {α β : Type v}

/-- The charge fold of the right tree is at most that of the left tree, along the lift. -/
theorem HFreeRel.wpFold_chargeUnder_le {S : SigRel P Q} {R : α → β → Prop}
    {c : P.A → ι → ℕ∞} {c' : Q.A → ι → ℕ∞} {allows : ∀ a, P.B a → Prop}
    {allows' : ∀ b, Q.B b → Prop} (hc : ∀ a b, S.pos a b → c' b ≤ c a)
    (ht : ∀ a b, S.pos a b → ∀ e, allows' b e → ∃ d, S.dir a b d e ∧ allows a d)
    {x : P.FreeM α} {y : Q.FreeM β} (hxy : HFreeRel S R x y) :
    wpFold (OpSpec.chargeUnder c' allows') y (fun _ => 0) ≤
      wpFold (OpSpec.chargeUnder c allows) x (fun _ => 0) := by
  induction hxy with
  | pure _ => exact le_rfl
  | @liftBind a b k k' hab _ ih =>
    change c' b + ⨆ e, ⨆ (_ : allows' b e),
        wpFold (OpSpec.chargeUnder c' allows') (k' e) (fun _ => 0) ≤
      c a + ⨆ d, ⨆ (_ : allows a d), wpFold (OpSpec.chargeUnder c allows) (k d) (fun _ => 0)
    refine add_le_add (hc a b hab) (iSup₂_le fun e he => ?_)
    obtain ⟨d, hde, hd⟩ := ht a b hab e he
    exact (ih d e hde).trans (le_iSup₂_of_le d hd le_rfl)

/-- **Use bounds transfer along the lift.** Charges in the order `c' ≤ c` at related shapes,
allowed answers reflected along related positions, and a related position for every position of
the right tree give the use bound of the left tree to the right tree. -/
theorem HFreeRel.useBound {S : SigRel P Q} {R : α → β → Prop} {c : P.A → ι → ℕ∞}
    {c' : Q.A → ι → ℕ∞} {allows : ∀ a, P.B a → Prop} {allows' : ∀ b, Q.B b → Prop}
    (hc : ∀ a b, S.pos a b → c' b ≤ c a)
    (ht : ∀ a b, S.pos a b → ∀ e, allows' b e → ∃ d, S.dir a b d e ∧ allows a d)
    {x : P.FreeM α} {y : Q.FreeM β} (hxy : HFreeRel S R x y) {u : ι → ℕ∞}
    (hx : UseBound c allows x u) : UseBound c' allows' y u :=
  (hxy.wpFold_chargeUnder_le hc ht).trans hx

end UseBound

/-! ## Squares of fixed demands -/

section Demand

variable {D D' D₁ D₁' : Type}

/-- The relation on a one-shape object with positions related by `r`. -/
def SigRel.ofDir (r : D → D₁ → Prop) :
    SigRel ⟨PUnit.{1}, fun _ => D⟩ ⟨PUnit.{1}, fun _ => D₁⟩ where
  pos _ _ := True
  dir _ _ := r

/-- A square of two fixed demands holds exactly when related positions demand related
multisets. -/
theorem demandLens_dnSquare_iff (δ : D → Multiset D') (δ₁ : D₁ → Multiset D₁')
    (r : D' → D₁' → Prop) (r' : D → D₁ → Prop) :
    SigRel.DNSquare (SigRel.ofDir r) (SigRel.ofDir r') (Crypto.OracleAdv.demandLens δ)
        (Crypto.OracleAdv.demandLens δ₁) ↔
      ∀ d d₁, r' d d₁ → Multiset.Rel r (δ d) (δ₁ d₁) :=
  ⟨fun s d d₁ h => s.pos (a := PUnit.unit) (b := PUnit.unit) trivial d d₁ h,
    fun H => ⟨fun _ => trivial, fun _ d d₁ h => H d d₁ h⟩⟩

/-- Along a square of fixed demands at the equality of resources, related positions demand each
resource equally often, so that the use counts of `useBound_liftM_eq_demandLens` agree. -/
theorem SigRel.DNSquare.count_demandLens_eq [DecidableEq D'] {δ δ₁ : _ → Multiset D'}
    {r' : D → D₁ → Prop}
    (s : SigRel.DNSquare (SigRel.ofDir Eq) (SigRel.ofDir r') (Crypto.OracleAdv.demandLens δ)
      (Crypto.OracleAdv.demandLens δ₁)) {d : D} {d₁ : D₁} (h : r' d d₁) (j : D') :
    (δ d).count j = (δ₁ d₁).count j := by
  rw [Multiset.rel_eq.1 ((demandLens_dnSquare_iff δ δ₁ Eq r').1 s d d₁ h)]

end Demand

end CatCrypt.Container
