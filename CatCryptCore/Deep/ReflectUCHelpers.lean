/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Deep.OracleGamePackage
import CatCryptCore.Crypto.NomPkgBridge
import CatCryptCore.Crypto.UC
import CatCryptCore.Relational.Judgment
import CatCryptCore.Prob.Coupling

set_option autoImplicit false

/-!
# Reflection → Package → UC: shared lift helpers

`Examples/OneTimePad.lean` lifts a shallow perfect-security result to a
*composable* statement about deep nominal packages, following the stack
`shallow game → rawCode% → NomPackage.ofOracle → DeepNomAdvantage → sdist → UC`.
This file extracts the reusable boilerplate of that lift so each perfect-security
example reduces to: reflect the two game bodies, prove their evaluations coincide,
and instantiate the `ofOracle` combinators below.

## Main results

* `spcomp_eq_of_isPure_coupling` — for two `IsPure` computations, an empty-heap
  perfect coupling (`rHoare eqPre _ _ eqPost`) upgrades to full `SPComp` equality.
  This is what turns an existing shallow coupling into the `.eval` equality the
  `ofOracle` combinators consume, with no purity bridge on the adversary.
* `AdvantageA_pure` — `AdvantageA g₀ g₁ SPComp.pure = Advantage g₀ g₁`.
* `UCEmulates_of_boolGame_sdist` — from `sdist g₀ g₁ ≤ ε` on two `SPComp Bool`
  game families, conclude `UCEmulates ε` over the trivial-leak spec via the
  `Sum.inl : Bool → Bool ⊕ Empty` wrapper.
* `evalOp_singleton_congr` — discharges `runPkg_link_congr`'s per-op obligation
  for a single-oracle `ofOracle` package.
* `runPkg_link_ofOracle_congr` — linked runs coincide against every adversary when
  the two oracle bodies have equal evaluations.
* `deepNomAdvantage_ofOracle_zero`, `sdist_ofOracle_zero`, `nomPkgSecure_ofOracle`,
  `uc_ofOracle` — the full perfect stack, each a one-line consequence of body
  `.eval` equality.
-/

namespace CatCrypt.Deep

open CatCrypt.Core CatCrypt.Crypto CatCrypt.Prob CatCrypt.Relational
open scoped ENNReal

/-! ## From a pure coupling to `SPComp` equality -/

/-- Pushing an `SDistr` forward along `(· , h)` is injective: the reheaping map
    `d ↦ d.bind (fun a => SDistr.pure (a, h))` recovers `d` at every point
    (`d none` at `none`, `d (some a)` at `some (a, h)`), so two distributions with
    equal pushforwards are equal. -/
private theorem push_inj {α : Type} (h : Heap) {d₀ d₁ : SDistr α}
    (heq : d₀.bind (fun a => SDistr.pure (a, h)) = d₁.bind (fun a => SDistr.pure (a, h))) :
    d₀ = d₁ := by
  classical
  ext o
  cases o with
  | none =>
    have hc := congrArg (fun p => p none) heq
    simp only [SDistr.bind, PMF.bind_apply] at hc
    rw [SDistr.tsum_option_eq_add, SDistr.tsum_option_eq_add] at hc
    simp only [SDistr.pure, SDistr.fail, PMF.pure_apply] at hc
    simpa using hc
  | some a =>
    have hc := congrArg (fun p => p (some (a, h))) heq
    simp only [SDistr.bind, PMF.bind_apply] at hc
    rw [SDistr.tsum_option_eq_add, SDistr.tsum_option_eq_add] at hc
    simp only [SDistr.pure, SDistr.fail, PMF.pure_apply, reduceCtorEq, if_false, mul_zero,
      zero_add, mul_ite, mul_one] at hc
    have hsingle : ∀ (d : SDistr α),
        (∑' a_1, if some (a, h) = some (a_1, h) then d (some a_1) else 0) = d (some a) := by
      intro d
      rw [tsum_eq_single a (by
        intro b hb
        rw [if_neg (fun he => hb (congrArg Prod.fst (Option.some.inj he)).symm)])]
      rw [if_pos rfl]
    rw [hsingle d₀, hsingle d₁] at hc
    exact hc

/-- For two heap-independent (`IsPure`) computations, an empty-heap perfect
    coupling `rHoare eqPre G₀ G₁ eqPost` upgrades to full `SPComp` equality
    `G₀ = G₁`. The coupling fixes the empty-heap distributions; purity extends
    that agreement to every heap via `push_inj`.

    This is the bridge that lets a shallow perfect-security coupling feed the
    `ofOracle` combinators below without any `IsPure`/`NoFail` post-processing
    hypothesis on the adversary. -/
theorem spcomp_eq_of_isPure_coupling {α : Type} {G₀ G₁ : SPComp α}
    (h₀ : SPComp.IsPure G₀) (h₁ : SPComp.IsPure G₁)
    (hc : rHoare eqPre G₀ G₁ eqPost) : G₀ = G₁ := by
  obtain ⟨d₀, hd₀⟩ := h₀
  obtain ⟨d₁, hd₁⟩ := h₁
  have hemp : G₀ Heap.empty = G₁ Heap.empty := by
    have hl := hc Heap.empty Heap.empty rfl
    have hEq : liftR Eq (G₀ Heap.empty) (G₁ Heap.empty) := by
      apply liftR_mono _ hl
      rintro ⟨a₁, k₁⟩ ⟨a₂, k₂⟩ ⟨ha, hk⟩
      simp only [eqPost] at *
      subst ha; subst hk; rfl
    exact liftR_eq_implies_eq hEq
  have hdd : d₀ = d₁ := by
    apply push_inj Heap.empty
    rw [← hd₀ Heap.empty, ← hd₁ Heap.empty]; exact hemp
  funext h; rw [hd₀ h, hd₁ h, hdd]

/-! ## Advantage / UC packaging -/

/-- The identity distinguisher is a no-op: `AdvantageA g₀ g₁ pure = Advantage g₀ g₁`. -/
theorem AdvantageA_pure (g₀ g₁ : SPComp Bool) :
    AdvantageA g₀ g₁ SPComp.pure = Advantage g₀ g₁ := by
  unfold AdvantageA
  rw [SPComp.bind_pure, SPComp.bind_pure]

/-- From a statistical-distance bound on two `SPComp Bool` game families, conclude
    `UCEmulates` over the trivial-leak interface (`out = Bool`, `leak = Empty`),
    wrapping each output through `Sum.inl : Bool → Bool ⊕ Empty`. Post-composition
    with the pure injection `Sum.inl` is non-expansive (`sdist_comp_right`), so the
    wrapped distance is still `≤ ε` and `UCEmulates_of_sdist` (identity simulator)
    applies. -/
theorem UCEmulates_of_boolGame_sdist {ι : Type*} {ε : ℝ≥0∞}
    (g₀ g₁ : ι → SPComp Bool) (h : sdist g₀ g₁ ≤ ε) :
    UCEmulates ε ⟨ι, Bool, Empty, Empty, Bool⟩
      (fun a => SPComp.map (Sum.inl : Bool → Bool ⊕ Empty) (g₀ a))
      (fun a => SPComp.map (Sum.inl : Bool → Bool ⊕ Empty) (g₁ a)) := by
  apply UCEmulates_of_sdist
  refine le_trans ?_ h
  simpa only [SPComp.map] using
    sdist_comp_right g₀ g₁ (fun b => SPComp.pure (Sum.inl b))

/-! ## The `ofOracle` perfect stack

The remaining combinators take two single-oracle `ofOracle` packages whose oracle
bodies have equal evaluations and derive the full package-level perfect-security
stack. Feed each with the `.eval` equality of the reflected game bodies (obtained,
for a shallow perfect coupling, via `spcomp_eq_of_isPure_coupling`). -/

/-- Discharges `runPkg_link_congr`'s per-op obligation for two `ofOracle` packages
    that export the *same* single oracle `(op, dom, codom)`: singleton membership
    forces the queried operation to be that oracle, whereupon `evalOp_ofOracle`
    reduces both sides to the reflected bodies, equal by hypothesis. -/
theorem evalOp_singleton_congr {op : ℕ} {dom codom : Type}
    (impl₀ impl₁ : dom → RawCode codom)
    [∀ x, IsValid (∅ : LocSet) (impl₀ x)] [∀ x, IsValid (∅ : LocSet) (impl₁ x)]
    (h : ∀ x, (impl₀ x).eval = (impl₁ x).eval)
    (op' : ℕ) (dom' codom' : Type)
    (h₁ : (op', dom', codom') ∈ (NomPackage.ofOracle op dom codom impl₀).pkg.exports.ops)
    (h₂ : (op', dom', codom') ∈ (NomPackage.ofOracle op dom codom impl₁).pkg.exports.ops)
    (x : dom') :
    ((NomPackage.ofOracle op dom codom impl₀).pkg.impl op' dom' codom' h₁ x).code.eval =
    ((NomPackage.ofOracle op dom codom impl₁).pkg.impl op' dom' codom' h₂ x).code.eval := by
  have he : (op, dom, codom) = (op', dom', codom') := by
    have hh := List.mem_singleton.mp h₁
    simpa only [NomPackage.ofOracle, DeepPackage.ofOracle, eq_comm] using hh
  obtain ⟨rfl, rfl, rfl⟩ : op = op' ∧ dom = dom' ∧ codom = codom' := by
    simpa only [Prod.mk.injEq] using he
  show (NomPackage.ofOracle op dom codom impl₀).pkg.evalOp op dom codom h₁ x =
       (NomPackage.ofOracle op dom codom impl₁).pkg.evalOp op dom codom h₂ x
  simp only [NomPackage.ofOracle]
  rw [evalOp_ofOracle, evalOp_ofOracle]
  exact h x

/-- Linking any adversary package `A` with either of two `ofOracle` games produces
    the same `SPComp Bool`, when the two oracle bodies have equal evaluations.
    The single per-op obligation of `runPkg_link_congr` is `evalOp_singleton_congr`;
    the interfaces agree by `rfl`. -/
theorem runPkg_link_ofOracle_congr {op : ℕ} {dom codom : Type}
    (impl₀ impl₁ : dom → RawCode codom)
    [∀ x, IsValid (∅ : LocSet) (impl₀ x)] [∀ x, IsValid (∅ : LocSet) (impl₁ x)]
    (h : ∀ x, (impl₀ x).eval = (impl₁ x).eval) (A : NomPackage) :
    runPkg (DeepPackage.link A.pkg (NomPackage.ofOracle op dom codom impl₀).pkg) =
    runPkg (DeepPackage.link A.pkg (NomPackage.ofOracle op dom codom impl₁).pkg) := by
  apply runPkg_link_congr
  · exact evalOp_singleton_congr impl₀ impl₁ h
  · rfl

/-- Zero deep-nominal advantage against every adversary package: the reflected
    real/ideal games are perfectly indistinguishable in the deep package model. -/
theorem deepNomAdvantage_ofOracle_zero {op : ℕ} {dom codom : Type}
    (impl₀ impl₁ : dom → RawCode codom)
    [∀ x, IsValid (∅ : LocSet) (impl₀ x)] [∀ x, IsValid (∅ : LocSet) (impl₁ x)]
    (h : ∀ x, (impl₀ x).eval = (impl₁ x).eval) (A : NomPackage) :
    DeepNomAdvantage (NomPackage.ofOracle op dom codom impl₀)
      (NomPackage.ofOracle op dom codom impl₁) A = 0 := by
  unfold DeepNomAdvantage
  rw [runPkg_link_ofOracle_congr impl₀ impl₁ h A]
  exact Advantage_self _

/-- Statistical distance zero between the two linked-game families. Since the
    linked runs coincide against every adversary, the two functions are equal, and
    `sdist_self` collapses the distance — no purity bridge on the adversary. -/
theorem sdist_ofOracle_zero {op : ℕ} {dom codom : Type}
    (impl₀ impl₁ : dom → RawCode codom)
    [∀ x, IsValid (∅ : LocSet) (impl₀ x)] [∀ x, IsValid (∅ : LocSet) (impl₁ x)]
    (h : ∀ x, (impl₀ x).eval = (impl₁ x).eval) :
    sdist (fun A : NomPackage =>
             runPkg (DeepPackage.link A.pkg (NomPackage.ofOracle op dom codom impl₀).pkg))
          (fun A : NomPackage =>
             runPkg (DeepPackage.link A.pkg (NomPackage.ofOracle op dom codom impl₁).pkg)) = 0 := by
  have hfun :
      (fun A : NomPackage =>
        runPkg (DeepPackage.link A.pkg (NomPackage.ofOracle op dom codom impl₀).pkg)) =
      (fun A : NomPackage =>
        runPkg (DeepPackage.link A.pkg (NomPackage.ofOracle op dom codom impl₁).pkg)) := by
    funext A; exact runPkg_link_ofOracle_congr impl₀ impl₁ h A
  rw [hfun]; exact sdist_self _

/-- Package-level perfect security (`NomPkgSecure`): the reflected games emulate
    each other with zero adversary-dependent error. -/
theorem nomPkgSecure_ofOracle {op : ℕ} {dom codom : Type}
    (impl₀ impl₁ : dom → RawCode codom)
    [∀ x, IsValid (∅ : LocSet) (impl₀ x)] [∀ x, IsValid (∅ : LocSet) (impl₁ x)]
    (h : ∀ x, (impl₀ x).eval = (impl₁ x).eval) :
    NomPkgSecure (NomPackage.ofOracle op dom codom impl₀)
      (NomPackage.ofOracle op dom codom impl₁) (fun _ => 0) :=
  fun A => le_of_eq (deepNomAdvantage_ofOracle_zero impl₀ impl₁ h A)

/-- Perfect UC emulation of the linked-game families over the trivial-leak
    interface (`out = Bool`, `leak = Empty`): the identity simulator suffices
    because the linked runs coincide (`sdist_ofOracle_zero`). -/
theorem uc_ofOracle {op : ℕ} {dom codom : Type}
    (impl₀ impl₁ : dom → RawCode codom)
    [∀ x, IsValid (∅ : LocSet) (impl₀ x)] [∀ x, IsValid (∅ : LocSet) (impl₁ x)]
    (h : ∀ x, (impl₀ x).eval = (impl₁ x).eval) :
    UCEmulates 0 ⟨NomPackage, Bool, Empty, Empty, Bool⟩
      (fun A => SPComp.map (Sum.inl : Bool → Bool ⊕ Empty)
        (runPkg (DeepPackage.link A.pkg (NomPackage.ofOracle op dom codom impl₀).pkg)))
      (fun A => SPComp.map (Sum.inl : Bool → Bool ⊕ Empty)
        (runPkg (DeepPackage.link A.pkg (NomPackage.ofOracle op dom codom impl₁).pkg))) :=
  UCEmulates_of_boolGame_sdist _ _ (le_of_eq (sdist_ofOracle_zero impl₀ impl₁ h))

end CatCrypt.Deep
