/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

import all Init.Data.Repr
public import CatCryptCore.Crypto.UCAdmClass
public import CatCryptCore.Core.SPTree
public import CatCryptCore.Crypto.UCMonad.SPCompInstance

/-!
# Monad cost model and query-bounded admissibility

This file defines `MonadCostModel`, an assignment of `ℕ∞` costs to Kleisli arrows that is
subadditive under bind, the admissibility class `adm f := cost f < ⊤` it induces, and the
query-bounded admissibility class `spTreeQueryAdm` on `SPComp`: an arrow is admissible when
it is the compilation of a family of `SPTree` syntax trees with uniformly bounded query cost.
It proves that the arrows of bounded cost are closed under `pure`, `bind` and `mapSum` and
are admissible.

Query cost is an instance of the class: `spTreeQueryCost f` is the least, over `SPTree`
families compiling to `f`, of the worst-case query cost, and the infimum is attained. The
class `spTreeQueryAdm` is the admissibility class induced by this instance
(`spTreeQueryAdm_eq_costModel`).

`spTreeQueryAdm` is a `def` and not an instance, which avoids a diamond with the trivial
`UCAdmClass SPComp` instance; it is used through `letI := spTreeQueryAdm`.

## Main definitions

* `MonadCostModel` — `ℕ∞` costs on Kleisli arrows, subadditive under bind
* `UCAdmClass_of_costModel` — the admissibility class `adm f := cost f < ⊤`
* `costBounded` — arrows of cost at most `n`
* `spTreeQueryAdm` — query-bounded admissibility on `SPComp` via `SPTree` witnesses
* `spTreeQueryCost` — least worst-case query cost over `SPTree` witnesses
* `MonadCostModel SPComp` — the instance with `cost := spTreeQueryCost`

## Main results

* `costBounded_pure`, `costBounded_bind`, `costBounded_mapSum`, `costBounded_mono` —
  closure of the cost-bounded arrows
* `adm_of_costBounded` — a cost-bounded arrow is admissible
* `exists_spTree_bind`, `exists_spTree_mapSum` — splicing of `SPTree` witnesses with
  additive and maximum query-cost bounds
* `spTreeQueryCost_le_iff` — `spTreeQueryCost f ≤ n` iff some witness family has query cost
  at most `n` at every input
* `spTreeQueryAdm_adm_iff`, `spTreeQueryAdm_eq_costModel` — `spTreeQueryAdm` is the class
  `UCAdmClass_of_costModel SPComp`

Relation to the literature: `CatCryptCore/Crypto/Complexity.md`.
-/

@[expose] public section

open scoped ENNReal

namespace UCMonad

/-! ## Section 1: Abstract Cost Model -/

/-- A cost model for a monad: assigns `ℕ∞`-valued costs to Kleisli arrows,
    subadditive under composition.

    The cost algebra `(ℕ∞, +, ≤)` is the same for both classical (`SPComp`)
    and quantum (`QComp d`) monads — only the cost function differs. -/
class MonadCostModel (T : Type → Type) [Monad T] [UCMonadBase T] where
  /-- Cost of a Kleisli arrow (worst-case over all inputs). -/
  cost : {α β : Type} → (α → T β) → WithTop ℕ
  /-- Pure (identity) has zero cost. -/
  cost_pure {α : Type} : cost (pure : α → T α) = 0
  /-- Cost is subadditive under Kleisli composition. -/
  cost_bind {α β γ : Type} {f : α → T β} {g : β → T γ} :
    cost (fun a => f a >>= g) ≤ cost f + cost g
  /-- Coproduct doesn't exceed maximum component cost. -/
  cost_mapSum {α β γ δ : Type} {f : α → T β} {g : γ → T δ} :
    cost (UCMonadBase.ucMapSum f g) ≤ max (cost f) (cost g)
  /-- Precomposing with a pure function doesn't increase cost. -/
  cost_precomp {α α' β : Type} {g : α → T β} (f : α' → α) :
    cost (g ∘ f) ≤ cost g

export MonadCostModel (cost cost_pure cost_bind cost_mapSum cost_precomp)

/-! ## Section 2: UCAdmClass from Cost Model -/

/-- Derive `UCAdmClass` from a cost model: `adm f := cost f < ⊤`.

    "Admissible" = "has finite worst-case cost". Closure:
    - `pure`: cost 0 < ⊤ ✓
    - `bind`: finite + finite < ⊤ ✓
    - `mapSum`: max(finite, finite) < ⊤ ✓

    This is a `def`, not an `instance`, to avoid diamonds with existing
    trivial instances. Use `letI := UCAdmClass_of_costModel T` locally. -/
noncomputable def UCAdmClass_of_costModel
    (T : Type → Type) [Monad T] [UCMonadBase T] [MonadCostModel T] :
    UCAdmClass T where
  adm f := cost f < ⊤
  adm_pure {α} := by rw [cost_pure]; exact WithTop.top_pos
  adm_bind hf hg := lt_of_le_of_lt cost_bind (WithTop.add_lt_top.mpr ⟨hf, hg⟩)
  adm_mapSum hf hg := by
    apply lt_of_le_of_lt
    · exact cost_mapSum
    · exact max_lt hf hg
  adm_precomp f hg := lt_of_le_of_lt (cost_precomp f) hg

/-! ## Section 3: Graded families of arrows -/

section GradedSubcategories

variable {T : Type → Type} [Monad T] [UCMonadBase T] [MonadCostModel T]

/-- A Kleisli arrow has cost bounded by `n`.

    The family `costBounded n` for `n : ℕ` is graded: identities lie in
    `costBounded 0`, composing an arrow of `costBounded n` with one of `costBounded m`
    gives an arrow of `costBounded (n + m)`, and `costBounded n ⊆ costBounded m` for
    `n ≤ m`; `adm = ⋃ₙ costBounded n = {f | cost f < ⊤}`. Only `costBounded 0` and `adm`
    are closed under composition, so only they are wide subcategories of Kl(T).

    The grades form the preordered monoid `(ℕ∞, ≤, 0, +)`, the kind of effect algebra of
    Katsumata's parametric effect monads ("Parametric effect monads and semantics of
    effect systems", POPL 2014); here the grading is on the Kleisli arrows of one monad,
    not a family of monads `T e`. -/
def costBounded (n : ℕ) {α β : Type} (f : α → T β) : Prop :=
  cost f ≤ n

/-- Pure has cost 0: identity morphisms are in `costBounded 0`. -/
theorem costBounded_pure {α : Type} : costBounded (T := T) 0 (pure : α → T α) := by
  simp [costBounded, cost_pure]

/-- Kleisli composition respects the grading: costs add. -/
theorem costBounded_bind {α β γ : Type} {f : α → T β} {g : β → T γ} {n m : ℕ}
    (hf : costBounded n f) (hg : costBounded m g) :
    costBounded (n + m) (fun a => f a >>= g) := by
  unfold costBounded at *
  calc cost (fun a => f a >>= g) ≤ cost f + cost g := cost_bind
    _ ≤ ↑n + ↑m := add_le_add hf hg
    _ = ↑(n + m) := by push_cast; ring

/-- Coproduct respects the grading: cost is max of components. -/
theorem costBounded_mapSum {α β γ δ : Type} {f : α → T β} {g : γ → T δ} {n m : ℕ}
    (hf : costBounded n f) (hg : costBounded m g) :
    costBounded (max n m) (UCMonadBase.ucMapSum f g) := by
  unfold costBounded at *
  calc cost (UCMonadBase.ucMapSum f g) ≤ max (cost f) (cost g) := cost_mapSum
    _ ≤ max (↑n) (↑m) := max_le_max hf hg
    _ = ↑(max n m) := by norm_cast

/-- Monotonicity: smaller cost bound implies larger cost bound. -/
theorem costBounded_mono {α β : Type} {f : α → T β} {n m : ℕ} (hnm : n ≤ m)
    (h : costBounded n f) : costBounded m f := by
  unfold costBounded at *
  exact le_trans h (WithTop.coe_le_coe.mpr hnm)

/-- Cost-bounded implies admissible (via `UCAdmClass_of_costModel`).

    Every `costBounded n f` arrow is admissible in the cost-derived `UCAdmClass`.
    This is the inclusion `⋃ₙ costBounded n ⊆ adm`. -/
theorem adm_of_costBounded {α β : Type} {f : α → T β} {n : ℕ}
    (h : costBounded n f) :
    (UCAdmClass_of_costModel T).adm f := by
  show cost f < ⊤
  exact lt_of_le_of_lt h (WithTop.coe_lt_top n)

end GradedSubcategories

/-! ## Section 4: SPComp Query-Bounded Admissibility via SPTree -/

open CatCrypt.Core CatCrypt.Crypto

/-! ### Bounded branching of `SPTree` witnesses under `bind`

The query-bounded classes admit only witness trees satisfying `SPTree.QueryBdd`, on which
`SPTree.queryCost` is the worst-case operation count. -/

/-- `ret` has bounded branching. -/
theorem _root_.CatCrypt.Core.SPTree.queryBdd_ret {α : Type} (a : α) :
    (SPTree.ret a).QueryBdd :=
  trivial

/-- Substituting continuations of bounded branching and uniformly bounded query cost into a
tree of bounded branching gives a tree of bounded branching. -/
theorem _root_.CatCrypt.Core.SPTree.QueryBdd.bind {α β : Type} {s : SPTree α}
    {f : α → SPTree β} {bound : ℕ} (hs : s.QueryBdd) (hf : ∀ a, (f a).QueryBdd)
    (hfc : ∀ a, (f a).queryCost ≤ bound) : (s.bind f).QueryBdd := by
  induction s with
  | ret a => exact hf a
  | sample γ finγ neγ k ih => exact fun c => ih c (hs c)
  | sampleDist γ μ k ih =>
    obtain ⟨⟨M, hM⟩, hk⟩ := hs
    refine ⟨⟨M + bound, ?_⟩, fun c => ih c (hk c)⟩
    rintro _ ⟨c, rfl⟩
    have h1 := hM ⟨c, rfl⟩
    have h2 := SPTree.queryCost_bind (k c) f bound hfc
    simp only at h1 ⊢
    omega
  | get l k ih => exact fun v => ih v (hs v)
  | set l v t ih => exact ih hs
  | fail => trivial
  | load h₀ t ih => exact ih hs

/-- Splicing `SPTree` witnesses: if `sf` compiles to `f` with query cost at most `n` and `sg`
    compiles to `g` with query cost at most `m`, both of bounded branching, then
    `fun a => (sf a).bind sg` compiles to `fun a => f a >>= g`, has bounded branching and
    has query cost at most `n + m`. -/
theorem exists_spTree_bind {α β γ : Type} {f : α → SPComp β} {g : β → SPComp γ} {n m : ℕ}
    (hf : ∃ s : α → SPTree β, (∀ a, (s a).compile = f a) ∧ (∀ a, (s a).QueryBdd) ∧
      ∀ a, (s a).queryCost ≤ n)
    (hg : ∃ s : β → SPTree γ, (∀ b, (s b).compile = g b) ∧ (∀ b, (s b).QueryBdd) ∧
      ∀ b, (s b).queryCost ≤ m) :
    ∃ s : α → SPTree γ, (∀ a, (s a).compile = f a >>= g) ∧ (∀ a, (s a).QueryBdd) ∧
      ∀ a, (s a).queryCost ≤ n + m := by
  obtain ⟨sf, hsf, hbf, hcf⟩ := hf
  obtain ⟨sg, hsg, hbg, hcg⟩ := hg
  refine ⟨fun a => (sf a).bind sg, ?_, fun a => (hbf a).bind hbg hcg, ?_⟩
  · intro a
    rw [SPTree.compile_bind, hsf a]
    congr 1; funext b; exact hsg b
  · intro a
    exact le_trans
      (SPTree.queryCost_bind (sf a) sg m hcg)
      (Nat.add_le_add_right (hcf a) m)

/-- `SPTree` witnesses for `ucMapSum`: case analysis on the sum, with bounded branching and
    query cost at most the maximum of the two bounds. -/
theorem exists_spTree_mapSum {α β γ δ : Type} {f : α → SPComp β} {g : γ → SPComp δ} {n m : ℕ}
    (hf : ∃ s : α → SPTree β, (∀ a, (s a).compile = f a) ∧ (∀ a, (s a).QueryBdd) ∧
      ∀ a, (s a).queryCost ≤ n)
    (hg : ∃ s : γ → SPTree δ, (∀ c, (s c).compile = g c) ∧ (∀ c, (s c).QueryBdd) ∧
      ∀ c, (s c).queryCost ≤ m) :
    ∃ s : α ⊕ γ → SPTree (β ⊕ δ),
      (∀ x, (s x).compile = UCMonadBase.ucMapSum f g x) ∧ (∀ x, (s x).QueryBdd) ∧
        ∀ x, (s x).queryCost ≤ max n m := by
  obtain ⟨sf, hsf, hbf, hcf⟩ := hf
  obtain ⟨sg, hsg, hbg, hcg⟩ := hg
  refine ⟨fun x => match x with
    | .inl a => (sf a).bind (fun b => SPTree.ret (.inl b))
    | .inr c => (sg c).bind (fun b => SPTree.ret (.inr b)), ?_, ?_, ?_⟩
  · intro x; cases x with
    | inl a =>
      simp only [SPTree.compile_bind, SPTree.compile_ret, hsf]
      show SPComp.bind (f a) (fun b => SPComp.pure (Sum.inl b)) =
        UCMonadBase.ucMapSum f g (.inl a)
      simp [UCMonadBase.ucMapSum, mapSumSP, SPComp.map]
    | inr c =>
      simp only [SPTree.compile_bind, SPTree.compile_ret, hsg]
      show SPComp.bind (g c) (fun b => SPComp.pure (Sum.inr b)) =
        UCMonadBase.ucMapSum f g (.inr c)
      simp [UCMonadBase.ucMapSum, mapSumSP, SPComp.map]
  · intro x; cases x with
    | inl a =>
      exact (hbf a).bind (bound := 0) (fun _ => SPTree.queryBdd_ret _) (fun _ => le_refl 0)
    | inr c =>
      exact (hbg c).bind (bound := 0) (fun _ => SPTree.queryBdd_ret _) (fun _ => le_refl 0)
  · intro x; cases x with
    | inl a =>
      show ((sf a).bind (fun b => SPTree.ret (Sum.inl b))).queryCost ≤ max n m
      calc ((sf a).bind (fun b => SPTree.ret (Sum.inl b))).queryCost
          ≤ (sf a).queryCost + 0 :=
            SPTree.queryCost_bind _ _ 0 (fun _ => le_refl 0)
        _ = (sf a).queryCost := Nat.add_zero _
        _ ≤ n := hcf a
        _ ≤ max n m := le_max_left _ _
    | inr c =>
      show ((sg c).bind (fun b => SPTree.ret (Sum.inr b))).queryCost ≤ max n m
      calc ((sg c).bind (fun b => SPTree.ret (Sum.inr b))).queryCost
          ≤ (sg c).queryCost + 0 :=
            SPTree.queryCost_bind _ _ 0 (fun _ => le_refl 0)
        _ = (sg c).queryCost := Nat.add_zero _
        _ ≤ m := hcg c
        _ ≤ max n m := le_max_right _ _

/-- A Kleisli arrow `f : α → SPComp β` is **query-bounded** if there exists
    a syntax tree representation of bounded branching (`SPTree.QueryBdd`) with uniformly
    bounded operation count.

    Membership in the class:
    - Opaque functions without syntax tree witnesses are NOT admissible
    - All programs built from standard SPComp constructors ARE admissible
    - The class is closed under bind (splicing trees) and mapSum (case analysis) -/
noncomputable def spTreeQueryAdm : UCAdmClass SPComp where
  adm {α β} f :=
    ∃ (s : α → SPTree β),
      (∀ a, (s a).compile = f a) ∧ (∀ a, (s a).QueryBdd) ∧
      ∃ n, ∀ a, (s a).queryCost ≤ n
  adm_pure :=
    ⟨SPTree.ret, fun _ => rfl, fun a => SPTree.queryBdd_ret a, 0, fun _ => le_refl 0⟩
  adm_bind {α β γ} {f g} hf hg := by
    obtain ⟨sf, hsf, hbf, nf, hcf⟩ := hf
    obtain ⟨sg, hsg, hbg, ng, hcg⟩ := hg
    obtain ⟨s, hs, hb, hc⟩ := exists_spTree_bind ⟨sf, hsf, hbf, hcf⟩ ⟨sg, hsg, hbg, hcg⟩
    exact ⟨s, hs, hb, nf + ng, hc⟩
  adm_mapSum {α β γ δ} {f g} hf hg := by
    obtain ⟨sf, hsf, hbf, nf, hcf⟩ := hf
    obtain ⟨sg, hsg, hbg, ng, hcg⟩ := hg
    obtain ⟨s, hs, hb, hc⟩ := exists_spTree_mapSum ⟨sf, hsf, hbf, hcf⟩ ⟨sg, hsg, hbg, hcg⟩
    exact ⟨s, hs, hb, max nf ng, hc⟩
  adm_precomp {α α' β} {g} f hg := by
    obtain ⟨sg, hsg, hbg, ng, hcg⟩ := hg
    exact ⟨sg ∘ f, fun a' => hsg (f a'), fun a' => hbg (f a'), ng, fun a' => hcg (f a')⟩

/-! ## Section 5: Query cost of `SPComp` as a cost model -/

/-- Query cost of a Kleisli arrow into `SPComp`: the least worst-case query cost over all
    `SPTree` families of bounded branching compiling to it, `⊤` when there is no such family
    or none with a uniform bound. -/
noncomputable def spTreeQueryCost {α β : Type} (f : α → SPComp β) : WithTop ℕ :=
  ⨅ s : {s : α → SPTree β // (∀ a, (s a).compile = f a) ∧ ∀ a, (s a).QueryBdd},
    ⨆ a, ((s.1 a).queryCost : ℕ∞)

/-- The infimum in `spTreeQueryCost` is attained: the query cost of `f` is at most `n` iff
    some `SPTree` family of bounded branching compiling to `f` has query cost at most `n` at
    every input. -/
theorem spTreeQueryCost_le_iff {α β : Type} {f : α → SPComp β} (n : ℕ) :
    spTreeQueryCost f ≤ n ↔
      ∃ s : α → SPTree β, (∀ a, (s a).compile = f a) ∧ (∀ a, (s a).QueryBdd) ∧
        ∀ a, (s a).queryCost ≤ n := by
  constructor
  · intro h
    have hne : Nonempty
        {s : α → SPTree β // (∀ a, (s a).compile = f a) ∧ ∀ a, (s a).QueryBdd} := by
      by_contra hem
      rw [not_nonempty_iff] at hem
      simp [spTreeQueryCost] at h
    obtain ⟨s, hs⟩ := ciInf_mem
      (fun s : {s : α → SPTree β // (∀ a, (s a).compile = f a) ∧ ∀ a, (s a).QueryBdd} =>
        ⨆ a, ((s.1 a).queryCost : ℕ∞))
    refine ⟨s.1, s.2.1, s.2.2, fun a => ?_⟩
    have : ((s.1 a).queryCost : ℕ∞) ≤ n :=
      le_trans (le_iSup (fun a => ((s.1 a).queryCost : ℕ∞)) a) (hs.trans_le h)
    exact_mod_cast this
  · rintro ⟨s, hs, hb, hc⟩
    exact iInf_le_of_le ⟨s, hs, hb⟩ (iSup_le fun a => Nat.cast_le.mpr (hc a))

noncomputable instance : MonadCostModel SPComp where
  cost := spTreeQueryCost
  cost_pure {α} := le_antisymm
    ((spTreeQueryCost_le_iff 0).mpr
      ⟨SPTree.ret, fun _ => rfl, fun a => SPTree.queryBdd_ret a, fun _ => le_refl 0⟩)
    bot_le
  cost_bind {α β γ} {f g} := by
    show spTreeQueryCost _ ≤ spTreeQueryCost f + spTreeQueryCost g
    by_cases hf : spTreeQueryCost f = ⊤
    · simp [hf]
    by_cases hg : spTreeQueryCost g = ⊤
    · simp [hg]
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hf
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hg
    rw [← hn, ← hm, ← WithTop.coe_add]
    exact (spTreeQueryCost_le_iff _).mpr (exists_spTree_bind
      ((spTreeQueryCost_le_iff n).mp hn.ge) ((spTreeQueryCost_le_iff m).mp hm.ge))
  cost_mapSum {α β γ δ} {f g} := by
    show spTreeQueryCost _ ≤ max (spTreeQueryCost f) (spTreeQueryCost g)
    by_cases hf : spTreeQueryCost f = ⊤
    · simp [hf]
    by_cases hg : spTreeQueryCost g = ⊤
    · simp [hg]
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp hf
    obtain ⟨m, hm⟩ := WithTop.ne_top_iff_exists.mp hg
    rw [← hn, ← hm, ← WithTop.coe_max]
    exact (spTreeQueryCost_le_iff _).mpr (exists_spTree_mapSum
      ((spTreeQueryCost_le_iff n).mp hn.ge) ((spTreeQueryCost_le_iff m).mp hm.ge))
  cost_precomp {α α' β} {g} f :=
    le_iInf fun sg =>
      iInf_le_of_le ⟨sg.1 ∘ f, fun a' => sg.2.1 (f a'), fun a' => sg.2.2 (f a')⟩
      (iSup_le fun a' => le_iSup (fun a => ((sg.1 a).queryCost : ℕ∞)) (f a'))

/-- Query-bounded admissibility is finiteness of the query cost. -/
theorem spTreeQueryAdm_adm_iff {α β : Type} {f : α → SPComp β} :
    spTreeQueryAdm.adm f ↔ cost f < ⊤ := by
  constructor
  · rintro ⟨s, hs, hb, n, hn⟩
    exact lt_of_le_of_lt ((spTreeQueryCost_le_iff n).mpr ⟨s, hs, hb, hn⟩)
      (WithTop.coe_lt_top n)
  · intro h
    obtain ⟨n, hn⟩ := WithTop.ne_top_iff_exists.mp h.ne
    obtain ⟨s, hs, hb, hc⟩ := (spTreeQueryCost_le_iff n).mp hn.ge
    exact ⟨s, hs, hb, n, hc⟩

/-- `spTreeQueryAdm` is the admissibility class induced by the query-cost model. -/
theorem spTreeQueryAdm_eq_costModel : spTreeQueryAdm = UCAdmClass_of_costModel SPComp := by
  have h : ∀ {α β : Type} (f : α → SPComp β),
      spTreeQueryAdm.adm f = (UCAdmClass_of_costModel SPComp).adm f :=
    fun _ => propext spTreeQueryAdm_adm_iff
  generalize hA : spTreeQueryAdm = A at h
  generalize hB : UCAdmClass_of_costModel SPComp = B at h
  cases A; cases B
  congr
  funext α β f
  exact h f

end UCMonad
