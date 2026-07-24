/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import Mathlib.Order.BoundedOrder.Basic
import Mathlib.Topology.EMetricSpace.Defs

/-!
# Generic UC Monad Typeclass

This file abstracts the 4 axioms that any monad needs for the UC factorization
framework to work:

1. **Coproducts** (A1): `ucMapSum` — parallel composition on `Sum`
2. **Affine/failure** (A2): `ucFail` — abort/discard
3. **Pseudometric** (A3): `ucSdist` — statistical distance with PPL
4. **Monad laws** (A4): `LawfulMonad` — associativity and unit laws

All factorization theorems from `UCFactorization.lean`, `UC.lean`, and `UCAlg.lean`
are reproved generically over any monad satisfying these axioms.

## Two-Layer Architecture

The theory splits cleanly into two layers:

**Standard layer** (A1+A2+A4 — any affine monad):
  Protocol categories, simulator composition, exact (ungraded)
  simulator-existence preorder, and exact UC emulation, for any monad
  with coproducts and failure. Captures deterministic simulation and
  compiler correctness.

**Metric-enriched layer** (adds A3 — requires probabilistic/quantitative structure):
  Approximate factorization, ε-bounds, game hopping, statistical UC emulation.
  Makes `Kl(T)` into a Lawvere metric space (ℝ≥0∞-enriched category, BMPP 2022).
  This is the discriminating axiom: only monads with a probabilistic or
  nondeterministic base give meaningful intermediate distances.

## Main definitions

### Standard layer (no metric)
* `UCMonadBase` — A1 + A4: lawful monad with coproduct structure
* `UCMonadAffine` — A2: failure/abort
* `UCPure` — purity predicate / central submonad (Carette-Lemonnier-Zamdzhiev 2022)
* `UCMonad.ProtObj` — generic protocol object
* `UCMonad.ProtMor` — generic protocol morphism (simulator adapter)
* `UCMonad.ExactUCEmulates` — exact UC emulation (no metric needed)

### Metric-enriched layer
* `UCMonadMetric` — A3: Lawvere metric on `Kl(T)` with PPL (non-expansiveness)
* `UCMonad` — all four axioms combined
* `UCMonad.approxFact` — ε-approximate factorization
* `UCMonad.UCEmulates` — generic UC emulation with ε-bound
* `UCMonad.SimConstruction` — algebraic simulator map
* `UCMonad.UCEmulatesAlg` — algebraic UC emulation

## Main results

### Standard layer
* `protMor_comp`, `protMor_comp_assoc` — simulator composition
* `factPre_refl`, `factPre_trans` — exact factorization preorder
* `ExactUCEmulates_refl`, `ExactUCEmulates_trans` — exact UC emulation
* `ExactUCEmulates_of_factPre` — factorization → exact UC emulation

### Metric-enriched layer
* `approxFact_refl`, `approxFact_trans`, `approxFact_mono`
* `approxFact_implies_UCEmulates` — factorization → UC emulation
* `UCEmulates_refl`, `UCEmulates_trans`, `UCEmulates_mono`
* `UCEmulatesAlg.forget`, `.refl`, `.trans`, `.trans_general`
* `UCEmulates_of_ExactUCEmulates` — exact → approximate (ε = 0)

## Design

This file has **no CatCrypt imports** — it is self-contained, depending only on
Mathlib for `ℝ≥0∞`. The concrete `SPComp` instance is in `UCMonad/SPCompInstance.lean`.
-/

open scoped ENNReal

set_option linter.dupNamespace false

namespace UCMonad

/-! ## Section 1: Typeclass Hierarchy -/

/-- A1 + A4: Lawful monad with coproduct structure (`mapSum`).

    `ucMapSum f g` applies `f` on `.inl` and `g` on `.inr`, with functoriality
    laws ensuring it respects `pure` and Kleisli composition. -/
class UCMonadBase (T : Type → Type) extends Monad T, LawfulMonad T where
  /-- Parallel composition on `Sum`: applies `f` to `.inl`, `g` to `.inr`. -/
  ucMapSum {α β γ δ : Type} (f : α → T β) (g : γ → T δ) : (α ⊕ γ) → T (β ⊕ δ)
  /-- `ucMapSum f g (.inl a) = f a >>= fun b => pure (.inl b)` -/
  ucMapSum_inl {α β γ δ : Type} (f : α → T β) (g : γ → T δ) (a : α) :
    ucMapSum f g (.inl a) = f a >>= fun b => pure (.inl b)
  /-- `ucMapSum f g (.inr c) = g c >>= fun d => pure (.inr d)` -/
  ucMapSum_inr {α β γ δ : Type} (f : α → T β) (g : γ → T δ) (c : γ) :
    ucMapSum f g (.inr c) = g c >>= fun d => pure (.inr d)
  /-- Identity: `ucMapSum pure pure = pure` -/
  ucMapSum_pure_pure {α β : Type} :
    ucMapSum (pure : α → T α) (pure : β → T β) = pure
  /-- Kleisli functoriality: `(id ⊕ f) ∘ₖ (id ⊕ g) = id ⊕ (f ∘ₖ g)` -/
  ucMapSum_pure_kleisli {α β γ δ : Type} (f : β → T γ) (g : γ → T δ) :
    (fun x : α ⊕ β => ucMapSum pure f x >>= ucMapSum pure g)
    = ucMapSum pure (fun b => f b >>= g)

/-- A2: Failure/abort operation satisfying the affine property. -/
class UCMonadAffine (T : Type → Type) extends UCMonadBase T where
  /-- The failing computation. -/
  ucFail {α : Type} : T α
  /-- Binding any computation with `ucFail` gives `ucFail`. -/
  ucBind_fail {α β : Type} (c : T α) : (c >>= fun _ => (ucFail : T β)) = ucFail

/-- A3: Statistical distance pseudometric with post-processing lemmas (PPL).

    Categorically, this makes `Kl(T)` into a **Lawvere metric space**
    (ℝ≥0∞-enriched category) where hom-objects are extended non-negative reals
    and composition is non-expansive (Lawvere 1973, BMPP 2022). The PPL axioms
    (`ucSdist_comp_right`, `ucSdist_comp_left`) express that Kleisli composition
    is a non-expansive map on hom-objects — the enriched functoriality condition.

    This is the **discriminating axiom**: A1, A2, A4 hold for any monad with
    exceptions, but A3 requires a quantitative/probabilistic structure that
    gives meaningful intermediate distances (0 < ε < ∞). Deterministic monads
    (StateM, ReaderT, Id) only see distance 0 or ∞, making the enrichment trivial.

    Without A3, the exact factorization (Sections 1–3) still works — only the
    approximate/graded factorization (Section 4+) requires the metric. -/
class UCMonadMetric (T : Type → Type) extends UCMonadBase T where
  /-- Statistical distance between Kleisli morphisms. -/
  ucSdist {α β : Type} : (α → T β) → (α → T β) → ℝ≥0∞
  /-- Reflexivity: `ucSdist f f = 0` -/
  ucSdist_self {α β : Type} (f : α → T β) : ucSdist f f = 0
  /-- Symmetry -/
  ucSdist_sym {α β : Type} (f g : α → T β) : ucSdist f g = ucSdist g f
  /-- Triangle inequality -/
  ucSdist_triangle {α β : Type} (f g h : α → T β) :
    ucSdist f h ≤ ucSdist f g + ucSdist g h
  /-- Right PPL: post-composition doesn't increase distance. -/
  ucSdist_comp_right {α β γ : Type} (f g : α → T β) (k : β → T γ) :
    ucSdist (fun a => f a >>= k) (fun a => g a >>= k) ≤ ucSdist f g
  /-- Left PPL: pre-composition doesn't increase distance. -/
  ucSdist_comp_left {α β γ : Type} (f : α → T β) (g₁ g₂ : β → T γ) :
    ucSdist (fun a => f a >>= g₁) (fun a => f a >>= g₂) ≤ ucSdist g₁ g₂

/-- All four axioms combined: lawful monad + coproducts + failure + pseudometric. -/
class UCMonad (T : Type → Type) extends UCMonadMetric T, UCMonadAffine T

/-- Purity predicate: marks computations as state-independent.

    For `T = SPComp`, this corresponds to `SPComp.IsPure`.
    Pure computations commute with all others (Fubini property).
    In the directed type theory, purity is the `!A` (of-course) modality.

    Categorically, `UCPure` is the **center** (central submonad) of `T`
    in the sense of Carette-Lemonnier-Zamdzhiev (LICS 2022). The key
    property is `isPure_comm`: pure computations commute with all others,
    which is equivalent to saying that the pure fragment forms a
    commutative submonad (the premonoidal center of `Kl(T)`). -/
class UCPure (T : Type → Type) [Monad T] where
  /-- The purity predicate on individual computations. -/
  isPure : {α : Type} → T α → Prop
  /-- `pure` is always pure. -/
  isPure_pure {α : Type} (a : α) : isPure (pure a : T α)
  /-- `bind` preserves purity. -/
  isPure_bind {α β : Type} (c : T α) (f : α → T β) :
    isPure c → (∀ a, isPure (f a)) → isPure (c >>= f)
  /-- Commutativity: pure computations commute with all others (Fubini).

      This is the defining property of the **central submonad**
      (Carette-Lemonnier-Zamdzhiev, LICS 2022): a computation `c` is
      central iff `c >>= (fun a => d >>= fun b => k a b)` equals
      `d >>= (fun b => c >>= fun a => k a b)` for all `d` and `k`. -/
  isPure_comm {α β γ : Type} (c : T α) (d : T β) (k : α → β → T γ) :
    isPure c → (c >>= fun a => d >>= fun b => k a b)
             = (d >>= fun b => c >>= fun a => k a b)

/-! ## Section 2: Helper Lemmas -/

variable {T : Type → Type}

theorem ucMapSum_pure_left [UCMonadBase T] {α β γ : Type}
    (g : β → T γ) (a : α) :
    UCMonadBase.ucMapSum (pure : α → T α) g (.inl a) = (pure (.inl a) : T (α ⊕ γ)) := by
  rw [UCMonadBase.ucMapSum_inl]; simp

theorem ucMapSum_pure_right [UCMonadBase T] {α β γ : Type}
    (f : α → T β) (c : γ) :
    UCMonadBase.ucMapSum f (pure : γ → T γ) (.inr c) = (pure (.inr c) : T (β ⊕ γ)) := by
  rw [UCMonadBase.ucMapSum_inr]; simp

theorem ucSdist_le_of_eq [UCMonadMetric T] {α β : Type}
    {f g : α → T β} (h : f = g) : UCMonadMetric.ucSdist f g = 0 := by
  subst h; exact UCMonadMetric.ucSdist_self f

theorem ucSdist_comp_add [UCMonadMetric T] {α β γ : Type}
    (f₁ f₂ : α → T β) (g₁ g₂ : β → T γ) {ε₁ ε₂ : ℝ≥0∞}
    (hf : UCMonadMetric.ucSdist f₁ f₂ ≤ ε₁)
    (hg : UCMonadMetric.ucSdist g₁ g₂ ≤ ε₂) :
    UCMonadMetric.ucSdist (fun a => f₁ a >>= g₁) (fun a => f₂ a >>= g₂) ≤ ε₁ + ε₂ := by
  calc UCMonadMetric.ucSdist (fun a => f₁ a >>= g₁) (fun a => f₂ a >>= g₂)
      ≤ UCMonadMetric.ucSdist (fun a => f₁ a >>= g₁) (fun a => f₂ a >>= g₁)
        + UCMonadMetric.ucSdist (fun a => f₂ a >>= g₁) (fun a => f₂ a >>= g₂) :=
        UCMonadMetric.ucSdist_triangle _ _ _
    _ ≤ ε₁ + ε₂ := add_le_add
        (le_trans (UCMonadMetric.ucSdist_comp_right f₁ f₂ g₁) hf)
        (le_trans (UCMonadMetric.ucSdist_comp_left f₂ g₁ g₂) hg)

/-! ## Section 3: Generic Protocol Category -/

/-- A protocol object bundles an interface type with a protocol morphism.
    Parameterized over any monad `T` satisfying `UCMonadBase`. -/
structure ProtObj (T : Type → Type) [Monad T] (hon out : Type) where
  /-- The adversary/simulator interface type -/
  iface : Type
  /-- The protocol: maps honest inputs to honest output + interface -/
  prot : hon → T (out ⊕ iface)

/-- A protocol morphism from `P` to `Q` consists of a simulator transforming
    `P`'s interface into `Q`'s interface, with a commutativity proof. -/
structure ProtMor [UCMonadBase T] {hon out : Type}
    (P Q : ProtObj T hon out) where
  /-- The simulator: transforms `P`'s interface to `Q`'s interface -/
  sim : P.iface → T Q.iface
  /-- Commutativity: `(id ⊕ sim) ∘ₖ P.prot = Q.prot` -/
  comm : ∀ a, P.prot a >>= UCMonadBase.ucMapSum pure sim = Q.prot a

/-- Identity morphism: the `pure` simulator. -/
noncomputable def protMor_id [UCMonadBase T] {hon out : Type}
    (P : ProtObj T hon out) : ProtMor P P where
  sim := pure
  comm := by
    intro a
    have h := UCMonadBase.ucMapSum_pure_pure (T := T) (α := out) (β := P.iface)
    simp [h]

/-- Composition of protocol morphisms: Kleisli-compose the simulators. -/
noncomputable def protMor_comp [UCMonadBase T] {hon out : Type}
    {P Q R : ProtObj T hon out}
    (f : ProtMor P Q) (g : ProtMor Q R) : ProtMor P R where
  sim := fun x => f.sim x >>= g.sim
  comm := by
    intro a
    rw [← UCMonadBase.ucMapSum_pure_kleisli f.sim g.sim,
        ← bind_assoc, f.comm, g.comm]

/-- Left identity law for protocol morphism composition. -/
theorem protMor_comp_id_left [UCMonadBase T] {hon out : Type}
    {P Q : ProtObj T hon out} (f : ProtMor P Q) :
    (protMor_comp (protMor_id P) f).sim = f.sim := by
  funext x; simp [protMor_comp, protMor_id]

/-- Right identity law for protocol morphism composition. -/
theorem protMor_comp_id_right [UCMonadBase T] {hon out : Type}
    {P Q : ProtObj T hon out} (f : ProtMor P Q) :
    (protMor_comp f (protMor_id Q)).sim = f.sim := by
  funext x; simp [protMor_comp, protMor_id]

/-- Associativity of protocol morphism composition. -/
theorem protMor_comp_assoc [UCMonadBase T] {hon out : Type}
    {P Q R S : ProtObj T hon out}
    (f : ProtMor P Q) (g : ProtMor Q R) (h : ProtMor R S) :
    (protMor_comp (protMor_comp f g) h).sim
    = (protMor_comp f (protMor_comp g h)).sim := by
  funext x; simp [protMor_comp, bind_assoc]

/-- Exact factorization preorder (opposite to morphism direction). -/
def factPre [UCMonadBase T] {hon out : Type}
    (P Q : ProtObj T hon out) : Prop :=
  Nonempty (ProtMor Q P)

theorem factPre_of_protMor [UCMonadBase T] {hon out : Type}
    {P Q : ProtObj T hon out} (f : ProtMor Q P) : factPre P Q := ⟨f⟩

theorem factPre_refl [UCMonadBase T] {hon out : Type}
    (P : ProtObj T hon out) : factPre P P :=
  ⟨protMor_id P⟩

theorem factPre_trans [UCMonadBase T] {hon out : Type}
    {P Q R : ProtObj T hon out}
    (hPQ : factPre P Q) (hQR : factPre Q R) : factPre P R := by
  obtain ⟨fQP⟩ := hPQ
  obtain ⟨fRQ⟩ := hQR
  exact ⟨protMor_comp fRQ fQP⟩

/-! ## Section 3b: Exact UC Emulation (Standard Layer — no metric)

The exact factorization and UC emulation depend only on A1+A2+A4 (any affine monad).
This is the **standard layer** of the theory: protocol categories, simulator composition,
and exact simulation are available for any monad with coproducts and failure, without
requiring a probabilistic metric.

It captures deterministic simulation, compiler correctness, and robust
compilation (Patrignani et al., TOPLAS 2024).

The **metric-enriched layer** (Section 4+) adds A3 to get ε-approximate factorization,
statistical distance bounds, and game hopping — requiring a quantitative/probabilistic
structure (BMPP 2022). -/

/-- Exact UC emulation: for all adversaries A, there exists a simulator S such that
    the real and ideal views are **equal** (not just close in distance).

    This depends only on `UCMonadBase` (A1+A4) — no metric needed. -/
def ExactUCEmulates [UCMonadBase T]
    {hon out leak sim_if view : Type}
    (π : hon → T (out ⊕ leak))
    (F : hon → T (out ⊕ sim_if)) : Prop :=
  ∀ (A : leak → T view), ∃ (S : sim_if → T view),
    (fun a => π a >>= UCMonadBase.ucMapSum pure A)
    = (fun a => F a >>= UCMonadBase.ucMapSum pure S)

/-- Exact factorization implies exact UC emulation (no metric needed). -/
theorem ExactUCEmulates_of_factPre [UCMonadBase T] {hon out : Type}
    {P Q : ProtObj T hon out} {view : Type}
    (h : factPre P Q) : ExactUCEmulates (T := T) (view := view) P.prot Q.prot := by
  obtain ⟨⟨S, hcomm⟩⟩ := h
  intro A
  refine ⟨fun x => S x >>= A, ?_⟩
  funext a
  rw [← UCMonadBase.ucMapSum_pure_kleisli S A, ← bind_assoc, hcomm]

/-- Exact UC emulation is reflexive. -/
theorem ExactUCEmulates_refl [UCMonadBase T]
    {hon out leak view : Type}
    (π : hon → T (out ⊕ leak)) :
    ExactUCEmulates (T := T) (view := view) π π :=
  fun A => ⟨A, rfl⟩

/-- Exact UC emulation is transitive (same-interface). -/
theorem ExactUCEmulates_trans [UCMonadBase T]
    {hon out leak view : Type}
    {π₁ π₂ π₃ : hon → T (out ⊕ leak)}
    (h₁ : ExactUCEmulates (T := T) (view := view) π₁ π₂)
    (h₂ : ExactUCEmulates (T := T) (view := view) π₂ π₃) :
    ExactUCEmulates (T := T) (view := view) π₁ π₃ := by
  intro A
  obtain ⟨S₁, hS₁⟩ := h₁ A
  obtain ⟨S₂, hS₂⟩ := h₂ S₁
  exact ⟨S₂, hS₁.trans hS₂⟩

/-! ## Section 4: Generic Approximate Factorization -/

/-- ε-approximate factorization preorder.

    `approxFact ε P Q` means: there exists a simulator `S : Q.iface → T P.iface`
    such that `P.prot` is within statistical distance `ε` of `(id ⊕ S) ∘ₖ Q.prot`. -/
def approxFact [UCMonadMetric T] (ε : ℝ≥0∞) {hon out : Type}
    (P Q : ProtObj T hon out) : Prop :=
  ∃ S : Q.iface → T P.iface,
    UCMonadMetric.ucSdist P.prot
      (fun a => Q.prot a >>= UCMonadBase.ucMapSum pure S) ≤ ε

/-- Reflexivity: identity simulator gives distance 0. -/
theorem approxFact_refl [UCMonadMetric T] {hon out : Type}
    (P : ProtObj T hon out) : approxFact 0 P P := by
  refine ⟨pure, ?_⟩
  have h : (fun a => P.prot a >>= UCMonadBase.ucMapSum (T := T) pure pure)
      = P.prot := by
    funext a; simp [UCMonadBase.ucMapSum_pure_pure]
  rw [h]; exact le_of_eq (UCMonadMetric.ucSdist_self _)

/-- Monotonicity: tighter bound implies looser bound. -/
theorem approxFact_mono [UCMonadMetric T] {hon out : Type}
    {P Q : ProtObj T hon out} {ε₁ ε₂ : ℝ≥0∞}
    (h : approxFact ε₁ P Q) (hle : ε₁ ≤ ε₂) :
    approxFact ε₂ P Q := by
  obtain ⟨S, hS⟩ := h
  exact ⟨S, le_trans hS hle⟩

/-- Transitivity: simulator chaining gives additive bound. -/
theorem approxFact_trans [UCMonadMetric T] {hon out : Type}
    {P Q R : ProtObj T hon out} {ε₁ ε₂ : ℝ≥0∞}
    (h₁ : approxFact ε₁ P Q) (h₂ : approxFact ε₂ Q R) :
    approxFact (ε₁ + ε₂) P R := by
  obtain ⟨S₁, hS₁⟩ := h₁
  obtain ⟨S₂, hS₂⟩ := h₂
  refine ⟨fun x => S₂ x >>= S₁, ?_⟩
  -- Rewrite target via ucMapSum_pure_kleisli
  have target_eq :
      (fun a => R.prot a >>= UCMonadBase.ucMapSum (T := T) pure (fun x => S₂ x >>= S₁))
      = (fun a => (R.prot a >>= UCMonadBase.ucMapSum pure S₂)
          >>= UCMonadBase.ucMapSum pure S₁) := by
    funext a; rw [bind_assoc, UCMonadBase.ucMapSum_pure_kleisli]
  rw [target_eq]
  -- Triangle inequality via intermediate
  calc UCMonadMetric.ucSdist P.prot
        (fun a => (R.prot a >>= UCMonadBase.ucMapSum pure S₂)
          >>= UCMonadBase.ucMapSum pure S₁)
      ≤ UCMonadMetric.ucSdist P.prot
          (fun a => Q.prot a >>= UCMonadBase.ucMapSum pure S₁)
        + UCMonadMetric.ucSdist
            (fun a => Q.prot a >>= UCMonadBase.ucMapSum pure S₁)
            (fun a => (R.prot a >>= UCMonadBase.ucMapSum pure S₂)
              >>= UCMonadBase.ucMapSum pure S₁) :=
        UCMonadMetric.ucSdist_triangle _ _ _
    _ ≤ ε₁ + ε₂ := add_le_add hS₁
        (le_trans (UCMonadMetric.ucSdist_comp_right Q.prot
          (fun a => R.prot a >>= UCMonadBase.ucMapSum pure S₂)
          (UCMonadBase.ucMapSum pure S₁)) hS₂)

/-- Exact factorization implies approximate factorization at ε = 0. -/
theorem approxFact_of_factPre [UCMonadMetric T] {hon out : Type}
    {P Q : ProtObj T hon out}
    (h : factPre P Q) : approxFact 0 P Q := by
  obtain ⟨⟨S, hcomm⟩⟩ := h
  refine ⟨S, ?_⟩
  have : P.prot = (fun a => Q.prot a >>= UCMonadBase.ucMapSum pure S) := by
    funext a; exact (hcomm a).symm
  rw [this]; exact le_of_eq (UCMonadMetric.ucSdist_self _)

/-- Same-interface sdist bound gives approximate factorization. -/
theorem approxFact_of_sdist [UCMonadMetric T] {hon out iface : Type}
    {ε : ℝ≥0∞}
    (π F : hon → T (out ⊕ iface))
    (h : UCMonadMetric.ucSdist π F ≤ ε) :
    approxFact ε ⟨iface, π⟩ ⟨iface, F⟩ := by
  refine ⟨pure, ?_⟩
  have : (fun a => F a >>= UCMonadBase.ucMapSum (T := T) pure pure) = F := by
    funext a; simp [UCMonadBase.ucMapSum_pure_pure]
  rw [this]; exact h

/-! ## Section 5: Generic UC Emulation -/

/-- Protocol `π` UC-emulates ideal functionality `F` with statistical error `ε`.

    For ALL adversaries A, there EXISTS a simulator S such that
    the ucSdist of the post-adversary views is ≤ ε. -/
def UCEmulates [UCMonadMetric T] (ε : ℝ≥0∞)
    {hon out leak sim_if view : Type}
    (π : hon → T (out ⊕ leak))
    (F : hon → T (out ⊕ sim_if)) : Prop :=
  ∀ (A : leak → T view), ∃ (S : sim_if → T view),
    UCMonadMetric.ucSdist
      (fun a => π a >>= UCMonadBase.ucMapSum pure A)
      (fun a => F a >>= UCMonadBase.ucMapSum pure S) ≤ ε

/-- Perfect UC emulation: ε = 0. -/
def UCEmulatesPerfect [UCMonadMetric T]
    {hon out leak sim_if : Type} (view : Type)
    (π : hon → T (out ⊕ leak))
    (F : hon → T (out ⊕ sim_if)) : Prop :=
  UCEmulates (T := T) (view := view) 0 π F

/-- Same-interface UC: if `ucSdist π F ≤ ε`, then `UCEmulates ε` with `S = A`. -/
theorem UCEmulates_of_sdist [UCMonadMetric T]
    {hon out leak view : Type} (ε : ℝ≥0∞)
    (π F : hon → T (out ⊕ leak))
    (h : UCMonadMetric.ucSdist π F ≤ ε) :
    UCEmulates (T := T) (view := view) ε π F := by
  intro A
  exact ⟨A, le_trans (UCMonadMetric.ucSdist_comp_right π F
    (UCMonadBase.ucMapSum pure A)) h⟩

/-- Monotonicity: UC emulation with tighter bound implies looser bound. -/
theorem UCEmulates_mono [UCMonadMetric T]
    {hon out leak sim_if view : Type}
    {π : hon → T (out ⊕ leak)} {F : hon → T (out ⊕ sim_if)}
    {ε₁ ε₂ : ℝ≥0∞}
    (h : UCEmulates (T := T) (view := view) ε₁ π F) (hle : ε₁ ≤ ε₂) :
    UCEmulates (T := T) (view := view) ε₂ π F := by
  intro A
  obtain ⟨S, hS⟩ := h A
  exact ⟨S, le_trans hS hle⟩

/-- Reflexivity: any protocol UC-emulates itself perfectly (same-interface). -/
theorem UCEmulates_refl [UCMonadMetric T]
    {hon out leak view : Type}
    (π : hon → T (out ⊕ leak)) :
    UCEmulates (T := T) (view := view) 0 π π := by
  intro A
  exact ⟨A, by simp [UCMonadMetric.ucSdist_self]⟩

/-- Transitivity of UC emulation (same-interface case). -/
theorem UCEmulates_trans [UCMonadMetric T]
    {hon out leak view : Type} {ε₁ ε₂ : ℝ≥0∞}
    {π₁ π₂ π₃ : hon → T (out ⊕ leak)}
    (h₁ : UCEmulates (T := T) (view := view) ε₁ π₁ π₂)
    (h₂ : UCEmulates (T := T) (view := view) ε₂ π₂ π₃) :
    UCEmulates (T := T) (view := view) (ε₁ + ε₂) π₁ π₃ := by
  intro A
  obtain ⟨S₁, hS₁⟩ := h₁ A
  obtain ⟨S₂, hS₂⟩ := h₂ S₁
  exact ⟨S₂, le_trans (UCMonadMetric.ucSdist_triangle _ _ _) (add_le_add hS₁ hS₂)⟩

/-- Approximate factorization implies UC emulation. -/
theorem approxFact_implies_UCEmulates [UCMonadMetric T]
    {hon out : Type} {P Q : ProtObj T hon out}
    {view : Type} {ε : ℝ≥0∞}
    (h : approxFact ε P Q) :
    UCEmulates (T := T) (view := view) ε P.prot Q.prot := by
  obtain ⟨S, hS⟩ := h
  intro A
  refine ⟨fun x => S x >>= A, ?_⟩
  -- Rewrite using ucMapSum_pure_kleisli
  have target_eq :
      (fun a => Q.prot a >>= UCMonadBase.ucMapSum (T := T) pure (fun x => S x >>= A))
      = (fun a => (Q.prot a >>= UCMonadBase.ucMapSum pure S)
          >>= UCMonadBase.ucMapSum pure A) := by
    funext a; rw [bind_assoc, UCMonadBase.ucMapSum_pure_kleisli]
  rw [target_eq]
  -- Right PPL: post-composing with (id ⊕ A) preserves the sdist bound
  exact le_trans (UCMonadMetric.ucSdist_comp_right _ _
    (UCMonadBase.ucMapSum pure A)) hS

/-- Exact factorization implies perfect UC emulation. -/
theorem exact_factorization_implies_UCEmulatesPerfect [UCMonadMetric T]
    {hon out : Type} {P Q : ProtObj T hon out} (view : Type)
    (h : factPre P Q) :
    UCEmulatesPerfect (T := T) view P.prot Q.prot :=
  approxFact_implies_UCEmulates (approxFact_of_factPre h)

/-! ### Bridge: exact → approximate -/

/-- Exact UC emulation implies approximate UC emulation at ε = 0. -/
theorem UCEmulates_of_ExactUCEmulates [UCMonadMetric T]
    {hon out leak sim_if view : Type}
    {π : hon → T (out ⊕ leak)}
    {F : hon → T (out ⊕ sim_if)}
    (h : ExactUCEmulates (T := T) (view := view) π F) :
    UCEmulates (T := T) (view := view) 0 π F := by
  intro A
  obtain ⟨S, hS⟩ := h A
  exact ⟨S, by rw [hS]; exact le_of_eq (UCMonadMetric.ucSdist_self _)⟩

/-! ## Section 6: Generic Algebraic UC (Explicit Simulator Construction) -/

/-- A simulator construction: a functorial map from adversaries to simulators. -/
def SimConstruction (T : Type → Type) [Monad T]
    (leak sim_if view : Type) : Type :=
  (leak → T view) → (sim_if → T view)

/-- Identity simulator construction (same-interface). -/
def SimConstruction.id {T : Type → Type} [Monad T]
    {leak view : Type} :
    SimConstruction T leak leak view :=
  _root_.id

/-- Composition of simulator constructions. -/
def SimConstruction.comp {T : Type → Type} [Monad T]
    {leak₁ leak₂ leak₃ view : Type}
    (Sim₁ : SimConstruction T leak₁ leak₂ view)
    (Sim₂ : SimConstruction T leak₂ leak₃ view) :
    SimConstruction T leak₁ leak₃ view :=
  Sim₂ ∘ Sim₁

@[simp]
theorem SimConstruction.id_comp {T : Type → Type} [Monad T]
    {leak₁ leak₂ view : Type}
    (Sim : SimConstruction T leak₁ leak₂ view) :
    SimConstruction.comp SimConstruction.id Sim = Sim := rfl

@[simp]
theorem SimConstruction.comp_id {T : Type → Type} [Monad T]
    {leak₁ leak₂ view : Type}
    (Sim : SimConstruction T leak₁ leak₂ view) :
    SimConstruction.comp Sim SimConstruction.id = Sim := rfl

theorem SimConstruction.comp_assoc {T : Type → Type} [Monad T]
    {leak₁ leak₂ leak₃ leak₄ view : Type}
    (Sim₁ : SimConstruction T leak₁ leak₂ view)
    (Sim₂ : SimConstruction T leak₂ leak₃ view)
    (Sim₃ : SimConstruction T leak₃ leak₄ view) :
    SimConstruction.comp (SimConstruction.comp Sim₁ Sim₂) Sim₃ =
    SimConstruction.comp Sim₁ (SimConstruction.comp Sim₂ Sim₃) := rfl

/-- Algebraic UC emulation with explicit simulator construction. -/
def UCEmulatesAlg [UCMonadMetric T] (ε : ℝ≥0∞)
    {hon out leak sim_if view : Type}
    (π : hon → T (out ⊕ leak))
    (F : hon → T (out ⊕ sim_if))
    (Sim : SimConstruction T leak sim_if view) : Prop :=
  ∀ (A : leak → T view),
    UCMonadMetric.ucSdist
      (fun a => π a >>= UCMonadBase.ucMapSum pure A)
      (fun a => F a >>= UCMonadBase.ucMapSum pure (Sim A)) ≤ ε

/-- Forget the algebraic witness: `UCEmulatesAlg → UCEmulates`. -/
theorem UCEmulatesAlg.forget [UCMonadMetric T]
    {ε : ℝ≥0∞} {hon out leak sim_if view : Type}
    {π : hon → T (out ⊕ leak)}
    {F : hon → T (out ⊕ sim_if)}
    {Sim : SimConstruction T leak sim_if view}
    (h : UCEmulatesAlg (T := T) ε π F Sim) :
    UCEmulates (T := T) (view := view) ε π F :=
  fun A => ⟨Sim A, h A⟩

/-- Monotonicity for algebraic UC. -/
theorem UCEmulatesAlg.mono [UCMonadMetric T]
    {ε₁ ε₂ : ℝ≥0∞} {hon out leak sim_if view : Type}
    {π : hon → T (out ⊕ leak)}
    {F : hon → T (out ⊕ sim_if)}
    {Sim : SimConstruction T leak sim_if view}
    (h : UCEmulatesAlg (T := T) ε₁ π F Sim) (hle : ε₁ ≤ ε₂) :
    UCEmulatesAlg (T := T) ε₂ π F Sim :=
  fun A => le_trans (h A) hle

/-- Reflexivity: any protocol emulates itself with `Sim = id`. -/
theorem UCEmulatesAlg.refl [UCMonadMetric T]
    {hon out leak view : Type}
    (π : hon → T (out ⊕ leak)) :
    UCEmulatesAlg (T := T) (view := view) 0 π π SimConstruction.id :=
  fun _ => le_of_eq (UCMonadMetric.ucSdist_self _)

/-- From sdist: same-interface with `Sim = id`. -/
theorem UCEmulatesAlg_of_sdist [UCMonadMetric T]
    {hon out leak view : Type} (ε : ℝ≥0∞)
    (π F : hon → T (out ⊕ leak))
    (h : UCMonadMetric.ucSdist π F ≤ ε) :
    UCEmulatesAlg (T := T) (view := view) ε π F SimConstruction.id :=
  fun A => le_trans (UCMonadMetric.ucSdist_comp_right π F
    (UCMonadBase.ucMapSum pure A)) h

/-- Same-interface transitivity via simulator composition. -/
theorem UCEmulatesAlg.trans [UCMonadMetric T]
    {hon out leak view : Type} {ε₁ ε₂ : ℝ≥0∞}
    {π₁ π₂ π₃ : hon → T (out ⊕ leak)}
    {Sim₁ Sim₂ : SimConstruction T leak leak view}
    (h₁ : UCEmulatesAlg (T := T) ε₁ π₁ π₂ Sim₁)
    (h₂ : UCEmulatesAlg (T := T) ε₂ π₂ π₃ Sim₂) :
    UCEmulatesAlg (T := T) (ε₁ + ε₂) π₁ π₃ (Sim₂ ∘ Sim₁) :=
  fun A => le_trans (UCMonadMetric.ucSdist_triangle _ _ _)
    (add_le_add (h₁ A) (h₂ (Sim₁ A)))

/-- General transitivity through different interface types. -/
theorem UCEmulatesAlg.trans_general [UCMonadMetric T]
    {hon out leak₁ leak₂ leak₃ view : Type} {ε₁ ε₂ : ℝ≥0∞}
    {π₁ : hon → T (out ⊕ leak₁)}
    {π₂ : hon → T (out ⊕ leak₂)}
    {π₃ : hon → T (out ⊕ leak₃)}
    {Sim₁ : SimConstruction T leak₁ leak₂ view}
    {Sim₂ : SimConstruction T leak₂ leak₃ view}
    (h₁ : UCEmulatesAlg (T := T) ε₁ π₁ π₂ Sim₁)
    (h₂ : UCEmulatesAlg (T := T) ε₂ π₂ π₃ Sim₂) :
    UCEmulatesAlg (T := T) (ε₁ + ε₂) π₁ π₃ (SimConstruction.comp Sim₁ Sim₂) :=
  fun A => le_trans (UCMonadMetric.ucSdist_triangle _ _ _)
    (add_le_add (h₁ A) (h₂ (Sim₁ A)))

end UCMonad
