/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Category.XCategoricalModel
public import CatCryptCore.XDijkstra.XPullback
public import CatCryptCore.XDijkstra.XFrameHet
public import CatCryptCore.XDijkstra.XStdWP

/-!
# `XCategoricalModelExt`: reindexing, the heterogeneous frame and the `Std.WP` bridge

`XCategoricalModel` states the grade, separation and morphism axes of the XDijkstra
framework as categorical structures over the shape-level observation `XWP`. This file
states the categorical reading of three constructions over the core observation
`XCoreWP`: pull-back of observations along monad morphisms (`XPullback`), the frame
rule along a separating map (`XFrameHet`), and the bridge to the toolchain's
`Std.WP` (`XStdWP`). Statements with a short proof from those modules are Lean
declarations here; the categorical statements beyond that scope are stated in this
docstring.

## 1. Observations as a fibred category; pull-back is reindexing

Fix the assertion types `Pred`, `EPred` and the grade type `G`. An object is a monad
`m` with an observation `XCoreWP m Pred EPred G`; a morphism from `(m, wp_m)` to
`(n, wp_n)` is a family `θ : m α → n α` with a morphism of observations
`XCoreWPHom` along `θ` (maps on postconditions and preconditions satisfying the
transfer law). `XCoreWPHom.id` and `XCoreWPHom.comp` are the identities and the
composition, with the unit and associativity laws `XCoreWPHom.id_comp`,
`XCoreWPHom.comp_id`, `XCoreWPHom.comp_assoc`; forgetting the observation is a
functor to monads and families of maps, and monad morphisms are closed under
identity and composition (`IsMonadMorphism.id`, `IsMonadMorphism.comp`).

Pull-back `XCoreWP.pullback h` along `h : m → n` is reindexing of the fibre over `n`
into the fibre over `m`. Reindexing along the identity is the identity
(`pullback_id`) and reindexing along `h ∘ k` is reindexing along `h`, then along `k`
(`pullback_comp`), on the nose: the fibration is split. `XCoreWP.pullbackHom h`, with
identity maps on assertions, is the cartesian arrow over `h`: a morphism along
`h ∘ k` into `(n, wp_n)` factors uniquely through it by a morphism along `k`
(`pullbackLift`, `pullbackLift_comp_pullbackHom`, `pullbackLift_unique`). Reindexing
along a monad morphism preserves lawful objects (`XCoreWP.lawful_pullback`), and it
transports triples: a triple of `c` in the reindexed fibre is a triple of `h c`
(`XCoreWP.pullback_triple_iff`). A handler interpreting free-monad syntax into an
observed monad is such a reindexing, so the syntax carries the program logic of its
target.

## 2. The heterogeneous frame as lax naturality

A separating map `sep : P₁ → P₂ → P₃`, monotone in its first argument, is an action of
the frame poset `P₂` that changes the assertion type: it sends an assertion `p` on the
small state and a frame `R` to the assertion `sep p R` on the large state. Each
transformer `t : XCorePT P₁ EPred G α` gives, at an exception postcondition `epost`,
a monotone map `t.apply · epost : (α → P₁) → P₁`. Locality
`XCorePT.LocalAlong sep adm t t'` is the lax naturality square

`sep (t.apply post epost) R ≤ t'.apply (fun a => sep (post a) R) epost`

for the action `sep · R`, at the admissible postconditions; the 2-cell points from the
framed weakest precondition to the weakest precondition at the framed postcondition.
The frame rule `XCorePT.frameAlong` is the induced map of triples: it composes the
monotonicity of `sep` with the lax square. Lax squares paste: the unit action
`fun p _ => p` has the identity square (`localAlong_unit`), and two lax squares along
`sep₁` and `sep₂` paste to the lax square along the composite action
`fun p (r, s) => sep₂ (sep₁ p r) s` (`localAlong_comp`), so the actions compose as an
action of the product of the frame posets. The return, bind and sequencing closures
(`XCorePT.ret_localAlong`, `XCorePT.bind_localAlong`, `XCorePT.seq_localAlong`) state
that the lax squares are compatible with the monad structure of `XCorePT`.

The homogeneous frame is the diagonal case `P₁ = P₂ = P₃`, `t' = t`, with
`sep = XCoreSep.sep` and every postcondition admissible:
`XCorePT.local_iff_localAlong` identifies `XCorePT.Local` with that case and
`XCorePT.frame_of_frameAlong` derives `XCorePT.frame` from `frameAlong`.

**Register-indexed reading.** Index the assertion types by registers `d`, with
`P d` the predicates on register `d` and a product of registers `d * e`. A family
`sep : P d → P e → P (d * e)`, monotone in its first argument, is a lax monoidal
action of the indexed family of predicate posets; a program on `d` and its lifting to
`d * e` form a pair `(t, t')`, and locality along `sep` is lax naturality of the
observation for that action. The old frame rule is the constant-index case
(`P d = Pred` for every `d`). Two instances are formalized in the development
library, outside this one: the tensor of quantum effects `E ⊗ F : Effect (d * e)`,
for which a quantum program `C` and its local lifting are local along `· ⊗ F` at every
postcondition (`XQuantumFrame`); and the quantum couplings of `XQRHLCoupling`, local
along the tensor with a spectator projector at the admissible postconditions
`linCoupling ∘ Q`.

## 3. The `Std.WP` bridge as a pair of functors

The observations of `Std.WP` are monads with a `WPMonad m Pred EPred` over complete
lattices ordered by `⊑`, with lower-bound laws; the observations of this library are
`XCoreWP m Pred EPred G` over preorders ordered by `≤`. Under the agreement
`LERelCompat` of the two orders:

* `XCoreWP.ofWPMonad` sends a `WPMonad` to an `XCoreWP` at grade `Unit` satisfying the
  lower-bound laws `XCoreWP.LowerLaws` (`lowerLaws_ofWPMonad`), with the same weakest
  preconditions (`xcore_wp_eq_wp`);
* `XCoreWP.toWPMonadOfLe` sends an `XCoreWP` satisfying `LowerLaws` to a `WPMonad`,
  forgetting the grade, with the same weakest preconditions (`wp_eq_xcore_wp`);
  `XCoreWP.toWPMonad` is its restriction to lawful observations.

On weakest preconditions the two constructions are mutually inverse: the round trip
through `ofWPMonad` and back is the identity on the transformers of a `WPMonad`
(`toWPMonad_ofWPMonad_wpTrans`, the counit equation), and the round trip through
`toWPMonadOfLe` and back is the identity on weakest preconditions with the grade
replaced by `()` (`ofWPMonad_toWPMonad_apply`, the unit equation, which is an
equation only up to forgetting the grade). Both constructions act on objects of the
fibres of §1. They commute with reindexing: the lower-bound laws are stable under
pull-back along a monad morphism (`lowerLaws_pullback`), and the `WPMonad` of a
pulled-back observation has the weakest preconditions and the triples of the image
program (`wp_toWPMonadOfLe_pullback`, `triple_toWPMonadOfLe_pullback_iff`).

## Main definitions

* `XCoreWPHom.id`, `XCoreWPHom.comp`: identity and composition of morphisms of
  observations.
* `XCoreWPHom.pullbackLift`: the factorization of a morphism along `h ∘ k` through the
  cartesian arrow `XCoreWP.pullbackHom h`.

## Main results

* `IsMonadMorphism.id`, `IsMonadMorphism.comp`: monad morphisms form a category.
* `XCoreWPHom.id_comp`, `XCoreWPHom.comp_id`, `XCoreWPHom.comp_assoc`: the category
  laws of morphisms of observations.
* `XCoreWP.pullback_id`, `XCoreWP.pullback_comp`: reindexing is split functorial.
* `XCoreWPHom.pullbackLift_comp_pullbackHom`, `XCoreWPHom.pullbackLift_unique`:
  `pullbackHom` is cartesian.
* `XCorePT.localAlong_unit`, `XCorePT.localAlong_comp`: lax squares along separating
  maps paste along the composite action.
* `wp_toWPMonadOfLe_pullback`, `triple_toWPMonadOfLe_pullback_iff`: the `Std.WP`
  bridge commutes with reindexing.

## References

* K. Maillard, D. Ahman, R. Atkey, G. Martínez, C. Hriţcu, E. Rivas, É. Tanter,
  "Dijkstra Monads for All", ICFP 2019.
* S. Katsumata, "Parametric effect monads and semantics of effect systems",
  POPL 2014.
* B. Jacobs, "Categorical Logic and Type Theory", Elsevier, 1999 (fibrations,
  cartesian arrows, split reindexing).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.XDijkstra

universe u v w x y y' z z'

/-! ## 1. Observations as a fibred category; pull-back is reindexing -/

namespace IsMonadMorphism

/-- The identity family is a monad morphism. -/
theorem id (m : Type x → Type y) [Monad m] : IsMonadMorphism m m (fun c => c) :=
  ⟨fun _ => rfl, fun _ _ => rfl⟩

/-- The composite of two monad morphisms is a monad morphism. -/
theorem comp {l : Type x → Type y'} {m : Type x → Type y} {n : Type x → Type z}
    [Monad l] [Monad m] [Monad n] {k : {α : Type x} → l α → m α}
    {h : {α : Type x} → m α → n α} (hk : IsMonadMorphism l m @k)
    (hh : IsMonadMorphism m n @h) : IsMonadMorphism l n (fun c => h (k c)) :=
  ⟨fun a => by rw [hk.map_pure, hh.map_pure],
    fun c f => by rw [hk.map_bind, hh.map_bind]⟩

end IsMonadMorphism

namespace XCoreWPHom

variable {l : Type x → Type y'} {m : Type x → Type y} {n : Type x → Type z}
  {o : Type x → Type z'}
  {Pred₁ Pred₂ Pred₃ Pred₄ : Type u} {EPred₁ EPred₂ EPred₃ EPred₄ : Type v}
  {G₁ G₂ G₃ G₄ : Type w}
  [LE Pred₁] [LE EPred₁] [LE Pred₂] [LE EPred₂] [LE Pred₃] [LE EPred₃]
  [LE Pred₄] [LE EPred₄]

/-- The identity morphism of an observation, along the identity family. -/
def id [i₁ : XCoreWP m Pred₁ EPred₁ G₁] :
    XCoreWPHom (m := m) (n := m) Pred₁ EPred₁ Pred₁ EPred₁ (fun c => c) where
  postMap Q := Q
  preMap P := P
  preMap_mono h := h
  transfer _ _ _ := rfl

/-- The composite of a morphism of observations along `θ` and one along `θ'`, along
`θ' ∘ θ`: postconditions are pulled back by `ψ` then `φ`, preconditions are pushed
forward by `φ` then `ψ`. -/
def comp [i₁ : XCoreWP m Pred₁ EPred₁ G₁] [i₂ : XCoreWP n Pred₂ EPred₂ G₂]
    [i₃ : XCoreWP o Pred₃ EPred₃ G₃]
    {θ : {α : Type x} → m α → n α} {θ' : {α : Type x} → n α → o α}
    (φ : XCoreWPHom (m := m) (n := n) Pred₁ EPred₁ Pred₂ EPred₂ θ)
    (ψ : XCoreWPHom (m := n) (n := o) Pred₂ EPred₂ Pred₃ EPred₃ θ') :
    XCoreWPHom (m := m) (n := o) Pred₁ EPred₁ Pred₃ EPred₃ (fun c => θ' (θ c)) where
  postMap Q := φ.postMap (ψ.postMap Q)
  preMap P := ψ.preMap (φ.preMap P)
  preMap_mono h := ψ.preMap_mono (φ.preMap_mono h)
  transfer c post epost := by
    rw [ψ.transfer (θ c) post epost, φ.transfer c]

/-- The identity is a left unit of composition (a law of `comp`, by unfolding). -/
theorem id_comp [i₁ : XCoreWP m Pred₁ EPred₁ G₁] [i₂ : XCoreWP n Pred₂ EPred₂ G₂]
    {θ : {α : Type x} → m α → n α}
    (φ : XCoreWPHom (m := m) (n := n) Pred₁ EPred₁ Pred₂ EPred₂ θ) :
    (XCoreWPHom.id (m := m) (Pred₁ := Pred₁) (EPred₁ := EPred₁)).comp φ = φ := rfl

/-- The identity is a right unit of composition (a law of `comp`, by unfolding). -/
theorem comp_id [i₁ : XCoreWP m Pred₁ EPred₁ G₁] [i₂ : XCoreWP n Pred₂ EPred₂ G₂]
    {θ : {α : Type x} → m α → n α}
    (φ : XCoreWPHom (m := m) (n := n) Pred₁ EPred₁ Pred₂ EPred₂ θ) :
    φ.comp (XCoreWPHom.id (m := n) (Pred₁ := Pred₂) (EPred₁ := EPred₂)) = φ := rfl

/-- Composition of morphisms of observations is associative (a law of `comp`, by
unfolding). -/
theorem comp_assoc {p : Type x → Type y'} [i₁ : XCoreWP m Pred₁ EPred₁ G₁]
    [i₂ : XCoreWP n Pred₂ EPred₂ G₂] [i₃ : XCoreWP o Pred₃ EPred₃ G₃]
    [i₄ : XCoreWP p Pred₄ EPred₄ G₄]
    {θ₁ : {α : Type x} → m α → n α} {θ₂ : {α : Type x} → n α → o α}
    {θ₃ : {α : Type x} → o α → p α}
    (φ₁ : XCoreWPHom (m := m) (n := n) Pred₁ EPred₁ Pred₂ EPred₂ θ₁)
    (φ₂ : XCoreWPHom (m := n) (n := o) Pred₂ EPred₂ Pred₃ EPred₃ θ₂)
    (φ₃ : XCoreWPHom (m := o) (n := p) Pred₃ EPred₃ Pred₄ EPred₄ θ₃) :
    (φ₁.comp φ₂).comp φ₃ = φ₁.comp (φ₂.comp φ₃) := rfl

/-- The factorization of a morphism `φ` along `h ∘ k` into the observation of `n`
through the cartesian arrow `XCoreWP.pullbackHom h`: the same maps on assertions, as a
morphism along `k` into the observation of `m` pulled back along `h`. -/
def pullbackLift [i₁ : XCoreWP l Pred₁ EPred₁ G₁] [i₂ : XCoreWP n Pred₂ EPred₂ G₂]
    (h : {α : Type x} → m α → n α) {k : {α : Type x} → l α → m α}
    (φ : XCoreWPHom (m := l) (n := n) Pred₁ EPred₁ Pred₂ EPred₂ (fun c => h (k c))) :
    @XCoreWPHom l m Pred₁ EPred₁ Pred₂ EPred₂ G₁ G₂ _ _ _ _ _ (XCoreWP.pullback @h) @k :=
  letI := XCoreWP.pullback (Pred := Pred₂) (EPred := EPred₂) (G := G₂) @h
  { postMap := φ.postMap
    preMap := φ.preMap
    preMap_mono := φ.preMap_mono
    transfer := φ.transfer }

/-- The factorization composed with the cartesian arrow is the given morphism (the
defining equation of `pullbackLift`). -/
theorem pullbackLift_comp_pullbackHom [i₁ : XCoreWP l Pred₁ EPred₁ G₁]
    [i₂ : XCoreWP n Pred₂ EPred₂ G₂]
    (h : {α : Type x} → m α → n α) {k : {α : Type x} → l α → m α}
    (φ : XCoreWPHom (m := l) (n := n) Pred₁ EPred₁ Pred₂ EPred₂ (fun c => h (k c))) :
    comp (i₂ := XCoreWP.pullback @h) (pullbackLift h φ) (XCoreWP.pullbackHom @h) = φ :=
  rfl

/-- The factorization through the cartesian arrow is unique. -/
theorem pullbackLift_unique [i₁ : XCoreWP l Pred₁ EPred₁ G₁]
    [i₂ : XCoreWP n Pred₂ EPred₂ G₂]
    (h : {α : Type x} → m α → n α) {k : {α : Type x} → l α → m α}
    (φ : XCoreWPHom (m := l) (n := n) Pred₁ EPred₁ Pred₂ EPred₂ (fun c => h (k c)))
    (ψ : @XCoreWPHom l m Pred₁ EPred₁ Pred₂ EPred₂ G₁ G₂ _ _ _ _ _
      (XCoreWP.pullback @h) @k)
    (hψ : comp (i₂ := XCoreWP.pullback @h) ψ (XCoreWP.pullbackHom @h) = φ) :
    ψ = pullbackLift h φ := by
  subst hψ
  rfl

end XCoreWPHom

namespace XCoreWP

variable {l : Type x → Type y'} {m : Type x → Type y} {n : Type x → Type z}
  {Pred : Type u} {EPred : Type v} {G : Type w} [LE Pred] [LE EPred]

/-- Reindexing along the identity family is the identity (a law of `pullback`, by
unfolding). -/
theorem pullback_id [i : XCoreWP m Pred EPred G] :
    (pullback (fun {_} (c : m _) => c) : XCoreWP m Pred EPred G) = i := rfl

/-- Reindexing along `h ∘ k` is reindexing along `h`, then along `k` (a law of
`pullback`, by unfolding). -/
theorem pullback_comp [XCoreWP n Pred EPred G] (h : {α : Type x} → m α → n α)
    (k : {α : Type x} → l α → m α) :
    (pullback (fun {_} (c : l _) => h (k c)) : XCoreWP l Pred EPred G)
      = @pullback l m Pred EPred G _ _ @k (pullback @h) := rfl

end XCoreWP

/-! ## 2. The heterogeneous frame as lax naturality -/

namespace XCorePT

universe u₁ u₂ u₃ u₄ u₅ v' w₁ w₂ w₃

variable {P₁ : Type u₁} {P₂ : Type u₂} {P₃ : Type u₃} {P₄ : Type u₄} {P₅ : Type u₅}
  {EPred : Type v'} {G : Type w₁} {G' : Type w₂} {G'' : Type w₃} {α : Type x}

/-- The unit action `fun p _ => p` has the identity square: every transformer is local
along it, paired with itself, at every postcondition. -/
theorem localAlong_unit [Preorder P₁] [LE EPred] (adm : (α → P₁) → Prop)
    (t : XCorePT P₁ EPred G α) :
    LocalAlong (fun p (_ : PUnit.{u₂ + 1}) => p) adm t t :=
  fun _ _ _ _ => le_rfl

/-- Lax squares paste: locality of `(t, t')` along `sep₁` and of `(t', t'')` along
`sep₂`, with `sep₂` monotone in its first argument and admissibility carried by
`sep₁`, gives locality of `(t, t'')` along the composite action
`fun p (r, s) => sep₂ (sep₁ p r) s` of the product of the frame posets. -/
theorem localAlong_comp [LE P₁] [LE P₃] [Preorder P₅] [LE EPred]
    {sep₁ : P₁ → P₂ → P₃} {sep₂ : P₃ → P₄ → P₅}
    (hsep₂ : ∀ {a b : P₃} (s : P₄), a ≤ b → sep₂ a s ≤ sep₂ b s)
    {adm₁ : (α → P₁) → Prop} {adm₂ : (α → P₃) → Prop}
    {t : XCorePT P₁ EPred G α} {t' : XCorePT P₃ EPred G' α} {t'' : XCorePT P₅ EPred G'' α}
    (h₁ : LocalAlong sep₁ adm₁ t t') (h₂ : LocalAlong sep₂ adm₂ t' t'')
    (hadm : ∀ post, adm₁ post → ∀ r, adm₂ (fun a => sep₁ (post a) r)) :
    LocalAlong (fun p (rs : P₂ × P₄) => sep₂ (sep₁ p rs.1) rs.2) adm₁ t t'' :=
  fun post hpost epost rs =>
    le_trans (hsep₂ rs.2 (h₁ post hpost epost rs.1)) (h₂ _ (hadm post hpost rs.1) epost rs.2)

end XCorePT

/-! ## 3. The `Std.WP` bridge commutes with reindexing -/

section StdWP

open CatCrypt.StdWPBridge

variable {m : Type x → Type y} {n : Type x → Type y} {Pred : Type u} {EPred : Type v}
  {G : Type w} [Monad m] [LawfulMonad m] [Monad n] [Std.WP.Assertion Pred]
  [Std.WP.Assertion EPred] [LE Pred] [LE EPred] [LERelCompat Pred] [LERelCompat EPred]

/-- The `WPMonad` of the observation pulled back along a monad morphism `h` has, at `c`,
the weakest precondition of `h c`. -/
theorem wp_toWPMonadOfLe_pullback (h : {α : Type x} → m α → n α)
    (hh : IsMonadMorphism m n @h) [XCoreWP n Pred EPred G]
    (hL : XCoreWP.LowerLaws n (Pred := Pred) (EPred := EPred) (G := G)) {α : Type x}
    (c : m α) :
    ((@XCoreWP.toWPMonadOfLe m Pred EPred G _ _ _ _ _ _ _ _ (XCoreWP.pullback @h)
        (lowerLaws_pullback @h hh hL)).toWP α).wp c =
      (XCoreWP.wp (h c) : XCorePT Pred EPred G α).apply :=
  @wp_eq_xcore_wp m Pred EPred G _ _ _ _ _ _ _ _ (XCoreWP.pullback @h)
    (lowerLaws_pullback @h hh hL) α c

/-- A triple of `c` for the `WPMonad` of the observation pulled back along a monad
morphism `h` is a triple of `h c` for the observation of `n`. -/
theorem triple_toWPMonadOfLe_pullback_iff (h : {α : Type x} → m α → n α)
    (hh : IsMonadMorphism m n @h) [XCoreWP n Pred EPred G]
    (hL : XCoreWP.LowerLaws n (Pred := Pred) (EPred := EPred) (G := G)) {α : Type x}
    {P : Pred} {c : m α} {post : α → Pred} {epost : EPred} :
    @Std.WP.Triple Pred EPred (m α) α _ _ c
        ((@XCoreWP.toWPMonadOfLe m Pred EPred G _ _ _ _ _ _ _ _ (XCoreWP.pullback @h)
          (lowerLaws_pullback @h hh hL)).toWP α) P post epost ↔
      XCoreWP.Triple (m := n) (G := G) P (h c) post epost :=
  (@xcoreTriple_iff_triple m Pred EPred G _ _ _ _ _ _ _ _ (XCoreWP.pullback @h)
    (lowerLaws_pullback @h hh hL) α P c post epost).symm

end StdWP

end CatCrypt.XDijkstra
