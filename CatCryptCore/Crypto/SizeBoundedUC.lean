/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.MonadCostModel
public import CatCryptCore.Crypto.CompUCEquivalence

/-!
# Size-bounded computational UC for `SPComp`

`QueryBoundedUC.lean` pairs the *query-cost* admissibility class
(`MonadCostModel.spTreeQueryAdm`, cost = number of sample/get/set operations on the
worst-case path) into a `UCMonadCompDist SPComp` and proves, on the canonical separating
pair, that it does **not** separate `ucCdist` from `ucSdist`: an output-threshold test has
query cost `0`, is therefore admissible, and already realises the full statistical distance.

This file builds the **size** (total-node-count) analogue and, on top of it, the *genuine
computational separation* — the conditional theorem `ucCdist_lt_ucSdist_of_bounded` that the
query model provably could not carry — and states what a concrete PRG instantiation
needs.

## What `size` measures, and how it differs from query cost

`SPTree.size` counts **every** constructor by **summing** over the branches of a `sample` /
`get` node (`size (sample β k) = 1 + ∑_{b} size (k b)`), whereas `queryCost` takes the
**supremum** (`queryCost (sample β k) = 1 + ⨆_b queryCost (k b)`). Query cost is therefore
the *depth* (number of oracle calls on the worst path); size is the *total gate/description
count* of the whole computation. The gap is exponential: `wideTree n` (a single fan-out over
`Fin (2^n)`) has `queryCost = 1` but `size ≥ 2^n` (`wideTree_queryCost`,
`wideTree_size_ge`). This is exactly the "counts the whole computation" content — a
distinguisher that is cheap in oracle calls can still be an enormous circuit.

Because total node count is **super-additive** under substitution (bind duplicates the
continuation at every leaf), `size` obeys a *multiplicative* bind law
`size_bind_mul : size (s.bind f) ≤ size s * (bound + 1)` rather than the additive
`queryCost_bind`. That super-additivity is why `size` is **not** a `MonadCostModel`
(whose `cost_bind` is additive and `cost_pure = 0`): the additive grading collapses total
count back to depth. So `spTreeSizeAdm` is built **directly** (the `UCAdmClass_of_costModel`
route is unavailable *by design* — that is the mathematical distinction from query cost),
mirroring `spTreeQueryAdm`'s closure proofs with `size_bind_mul` in place of
`queryCost_bind`.

## Main definitions and results

* `spTreeSizeAdm : UCAdmClass SPComp` — "has a syntax-tree family of uniformly bounded total
  node count". Genuinely non-trivial (`sizeCompDist_adm_iff`), not `fun _ => True`.
* `sizeCompDist : UCMonadCompDist SPComp` — the trivial per-distinguisher instance with only
  the `adm*` fields swapped for `spTreeSizeAdm`'s.
* `ucCdist_lt_ucSdist_of_bounded` / `..._strict` — **the computational separation**, generic
  over `[UCMonadCompDist T]` and specialised to `sizeCompDist`. Given the hardness assumption
  `h_bounded` (every *admissible* distinguisher has advantage `≤ ε`) and an *inadmissible*
  high-size witness beating `c`, it concludes `ucCdist ≤ ε` and `c ≤ ucSdist`, hence
  `ucCdist < ucSdist` when `ε < c`. The `ucCdist ≤ ε` half routes `h_bounded` through
  `iSup₂_le` (admissible sup); the `c ≤ ucSdist` half routes the witness through
  `ucSdist_eq_iSup_distComp` (unrestricted sup).
* The dummy-adversary / CC ⟺ UC equivalences at `sizeCompDist` (size-bounded adversaries).

## The separation is conditional; where the two lower bounds live

`ucCdist_lt_ucSdist_of_bounded` is a genuine *conditional* theorem; it is **not** an
unconditional `ucCdist < ucSdist` (that would need a circuit lower bound, which is open).
Two facts fix the scope precisely:

1. **The obstruction survives for output differences.** Every *pure predicate*
   `fun b => pure (p b)` has size `1` (`adm_pure_predicate_size`) and — by `adm_precomp` on
   `adm_pure` — is admissible in *every* lawful `UCAdmClass`. Pure predicates are
   statistically optimal for distinguishing two *output* distributions, so on the canonical
   output-difference pair `Example.π` / `Example.F` we still get
   `ucCdist sizeCompDist = ucSdist = 1` (`ex_size_no_separation`) — no gap, exactly as for
   query cost. A separation is therefore impossible for any pair whose optimal distinguisher
   is a pure output predicate.

2. **`h_bounded` becomes *consistent* (not automatically false) only for a pair the pure
   class cannot read.** The intended witness is a re-derivation / membership test whose
   *reified* computation is large (`size`-inadmissible) while the pure class it competes
   against has advantage bounded by `ε`. Proving `h_bounded` unconditionally for such a pair
   is a circuit/PRG lower bound (open); proving the witness `size`-inadmissible at the
   `SPComp` level needs a distribution-support ⇒ tree-size lower bound (the `SPComp`
   denotation forgets the tree, so the tree-level gap `wideTree_size_ge` does not transfer
   for free). Both are stated, neither is faked. The theorem is delivered with `h_bounded`
   and the inadmissible witness as **hypotheses** — this is the standard
   "separation conditional on a hardness assumption", made precise.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Core.SPTree

open CatCrypt.Prob

/-! ## Section 0: The total-size measure on syntax trees -/

set_option linter.unusedVariables false in
/-- **Total node count.** Counts every constructor, **summing** over the branches of a
    `sample` / `get` node (contrast `queryCost`, which takes the supremum). This is the
    "whole computation / description size" measure: it charges for the entire fan-out, not
    just the worst-case path depth. -/
def size {α : Type} : SPTree α → ℕ
  | .ret _ => 1
  | .sample β finβ _ k => letI := finβ; 1 + Finset.univ.sum (fun b => size (k b))
  | .get _l k => 1 + Finset.univ.sum (fun v => size (k v))
  | .set _ _ t => 1 + size t
  | .fail => 1

@[simp] theorem size_ret {α : Type} (a : α) : (SPTree.ret a : SPTree α).size = 1 := rfl

@[simp] theorem size_fail {α : Type} : (SPTree.fail : SPTree α).size = 1 := rfl

/-- **Multiplicative bind law.** Substituting a continuation of size `≤ bound` at every leaf
    of `s` blows the total node count up by a factor `bound + 1` (each of the up-to-`size s`
    leaves is replaced by a copy of the continuation). This is the total-count analogue of
    the additive `queryCost_bind`; the super-additivity is the structural fact that keeps
    `size` out of `MonadCostModel` and makes the size class strictly finer than query. -/
theorem size_bind_mul {α β : Type} (s : SPTree α) (f : α → SPTree β) (bound : ℕ)
    (hf : ∀ a, (f a).size ≤ bound) :
    (s.bind f).size ≤ s.size * (bound + 1) := by
  induction s with
  | ret a => simpa [SPTree.bind, size] using le_trans (hf a) (by nlinarith [Nat.zero_le bound])
  | sample γ finγ neγ k ih =>
    simp only [SPTree.bind, size]
    calc 1 + Finset.univ.sum (fun c => ((k c).bind f).size)
        ≤ 1 + Finset.univ.sum (fun c => (k c).size * (bound + 1)) := by
          gcongr with c; exact ih c
      _ = 1 + (Finset.univ.sum (fun c => (k c).size)) * (bound + 1) := by rw [Finset.sum_mul]
      _ ≤ (1 + Finset.univ.sum (fun c => (k c).size)) * (bound + 1) := by
          nlinarith [Nat.zero_le bound]
  | get l k ih =>
    simp only [SPTree.bind, size]
    calc 1 + Finset.univ.sum (fun v => ((k v).bind f).size)
        ≤ 1 + Finset.univ.sum (fun v => (k v).size * (bound + 1)) := by
          gcongr with v; exact ih v
      _ = 1 + (Finset.univ.sum (fun v => (k v).size)) * (bound + 1) := by rw [Finset.sum_mul]
      _ ≤ (1 + Finset.univ.sum (fun v => (k v).size)) * (bound + 1) := by
          nlinarith [Nat.zero_le bound]
  | set l v t ih => simp only [SPTree.bind, size]; nlinarith [ih, Nat.zero_le bound]
  | fail => simp [SPTree.bind, size]

/-! ## Section 0b: size ≠ query — the exponential tree-level gap

`wideTree n` fans out once over `Fin (2^n)` and returns immediately. It has query cost `1`
(one sampling node, then leaves) but total size `1 + 2^n`. So the family `wideTree` is
uniformly query-bounded yet has unbounded size: the size class strictly refines the query
class. This is the concrete witness that "size counts the whole computation" is a genuine
strengthening, not a relabelling. -/

/-- A single fan-out over `Fin (2^n)`: query cost `1`, total size `1 + 2^n`. -/
noncomputable def wideTree (n : ℕ) : SPTree Bool :=
  .sample (Fin (2 ^ n)) (inferInstance)
    ⟨⟨0, pow_pos (by norm_num : (0 : ℕ) < 2) n⟩⟩ (fun _ => .ret true)

/-- `wideTree` has query cost `1` for every `n`: one sample node over constant-`0` leaves. -/
theorem wideTree_queryCost (n : ℕ) : (wideTree n).queryCost = 1 := by
  simp [wideTree, SPTree.queryCost]

/-- `wideTree n` has total size `1 + 2^n` — exponentially larger than its query cost. -/
theorem wideTree_size (n : ℕ) : (wideTree n).size = 1 + 2 ^ n := by
  simp [wideTree, size, Finset.card_univ]

/-- Hence the size of `wideTree n` is at least `2^n`: unbounded across the family while the
    query cost stays at `1`. -/
theorem wideTree_size_ge (n : ℕ) : 2 ^ n ≤ (wideTree n).size := by
  rw [wideTree_size]; omega

end CatCrypt.Core.SPTree

namespace CatCrypt.Crypto.SizeBoundedUC

open UCMonad
open CatCrypt.Core CatCrypt.Core.SPTree CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.CompUCEquivalence
open scoped ENNReal

/-! ## Section 1: The size-bounded admissibility class (built directly) -/

/-- **Size-bounded admissibility.** A Kleisli arrow `f : α → SPComp β` is admissible iff it
    has a syntax-tree family of uniformly bounded **total node count**.

    Built directly (not via `UCAdmClass_of_costModel`): total node count is super-additive
    under bind (`size_bind_mul` is multiplicative), so it is not a `MonadCostModel`. Closure
    is proved by mirroring `spTreeQueryAdm` with `size_bind_mul` and multiplicative bounds
    (`nf * (ng + 1)` for bind, `max (nf*2) (ng*2)` for mapSum). -/
@[reducible] noncomputable def spTreeSizeAdm : UCAdmClass SPComp where
  adm {α β} f :=
    ∃ (s : α → SPTree β), (∀ a, (s a).compile = f a) ∧ ∃ n, ∀ a, (s a).size ≤ n
  adm_pure := ⟨SPTree.ret, fun _ => rfl, 1, fun _ => le_refl 1⟩
  adm_bind {α β γ} {f g} hf hg := by
    obtain ⟨sf, hsf, nf, hcf⟩ := hf
    obtain ⟨sg, hsg, ng, hcg⟩ := hg
    refine ⟨fun a => (sf a).bind sg, ?_, nf * (ng + 1), ?_⟩
    · intro a; rw [SPTree.compile_bind, hsf a]; congr 1; funext b; exact hsg b
    · intro a
      exact le_trans (size_bind_mul (sf a) sg ng hcg) (Nat.mul_le_mul_right _ (hcf a))
  adm_mapSum {α β γ δ} {f g} hf hg := by
    obtain ⟨sf, hsf, nf, hcf⟩ := hf
    obtain ⟨sg, hsg, ng, hcg⟩ := hg
    refine ⟨fun x => match x with
      | .inl a => (sf a).bind (fun b => SPTree.ret (.inl b))
      | .inr c => (sg c).bind (fun b => SPTree.ret (.inr b)), ?_, max (nf * 2) (ng * 2), ?_⟩
    · intro x; cases x with
      | inl a =>
        simp only [SPTree.compile_bind, SPTree.compile_ret, hsf]
        show SPComp.bind (f a) (fun b => SPComp.pure (Sum.inl b)) =
          UCMonadBase.ucMapSum f g (.inl a)
        simp [UCMonadBase.ucMapSum, mapSum, SPComp.map]
      | inr c =>
        simp only [SPTree.compile_bind, SPTree.compile_ret, hsg]
        show SPComp.bind (g c) (fun b => SPComp.pure (Sum.inr b)) =
          UCMonadBase.ucMapSum f g (.inr c)
        simp [UCMonadBase.ucMapSum, mapSum, SPComp.map]
    · intro x; cases x with
      | inl a =>
        show ((sf a).bind (fun b => SPTree.ret (Sum.inl b))).size ≤ max (nf * 2) (ng * 2)
        refine le_trans (le_trans (size_bind_mul (sf a) _ 1 (fun _ => le_refl 1))
          (Nat.mul_le_mul_right _ (hcf a))) (le_max_left _ _)
      | inr c =>
        show ((sg c).bind (fun b => SPTree.ret (Sum.inr b))).size ≤ max (nf * 2) (ng * 2)
        refine le_trans (le_trans (size_bind_mul (sg c) _ 1 (fun _ => le_refl 1))
          (Nat.mul_le_mul_right _ (hcg c))) (le_max_right _ _)
  adm_precomp {α α' β} {g} f hg := by
    obtain ⟨sg, hsg, ng, hcg⟩ := hg
    exact ⟨sg ∘ f, fun a' => hsg (f a'), ng, fun a' => hcg (f a')⟩

/-! ## Section 2: The size-bounded compdist -/

/-- **The size-bounded per-distinguisher compdist on `SPComp`.** Everything except
    admissibility is inherited verbatim from the trivial `UCMonadCompDist SPComp` instance;
    only the five `adm*` fields are swapped for `spTreeSizeAdm`'s size-bounded class. Kept a
    `def` (not `instance`) to avoid a diamond with the registered trivial instance. -/
@[reducible] noncomputable def sizeCompDist : UCMonadCompDist SPComp :=
  { (inferInstance : UCMonadCompDist SPComp) with
    adm := spTreeSizeAdm.adm
    adm_pure := spTreeSizeAdm.adm_pure
    adm_bind := spTreeSizeAdm.adm_bind
    adm_mapSum := spTreeSizeAdm.adm_mapSum
    adm_precomp := spTreeSizeAdm.adm_precomp }

/-- The admissibility of `sizeCompDist` is *definitionally* the size-bounded class: an arrow
    is admissible iff it has a syntax-tree family of uniformly bounded total node count. This
    is the non-triviality witness — it is not `fun _ => True`. -/
theorem sizeCompDist_adm_iff {α β : Type} (f : α → SPComp β) :
    adm (self := sizeCompDist.toUCAdmClass) f ↔
      ∃ (s : α → SPTree β),
        (∀ a, (s a).compile = f a) ∧ ∃ n, ∀ a, (s a).size ≤ n :=
  Iff.rfl

/-- The `adm` field of `sizeCompDist` equals `spTreeSizeAdm`'s on the nose. -/
theorem sizeCompDist_adm_eq {α β : Type} (f : α → SPComp β) :
    adm (self := sizeCompDist.toUCAdmClass) f = adm (self := spTreeSizeAdm) f := rfl

/-- **Every pure predicate test is size-admissible** (total size `1`). By `adm_precomp` on
    `adm_pure` this holds in *every* lawful `UCAdmClass`; it is the structural obstruction to
    a distinguisher-side separation on output-difference pairs — the admissible class already
    contains all output-thresholding distinguishers. -/
theorem adm_pure_predicate_size {β : Type} (p : β → Bool) :
    adm (self := sizeCompDist.toUCAdmClass) (fun b => SPComp.pure (p b)) :=
  ⟨fun b => SPTree.ret (p b), fun _ => rfl, 1, fun _ => Nat.le_refl 1⟩

/-! ## Section 3: The computational separation (the core) -/

variable {T : Type → Type} [UCMonadCompDist T]

/-- **The computational separation, generic over the admissibility instance.**

    Given the hardness assumption `h_bounded` — every **admissible** distinguisher has
    advantage `≤ ε` — and an **inadmissible** witness `D` whose advantage is `≥ c`, the
    admissible-distinguisher distance `ucCdist` is bounded by `ε` while the statistical
    distance `ucSdist` is bounded below by `c`.

    Routing: `ucCdist f g = ⨆ (D) (_ : adm D), ucDistComp f g D`, so `iSup₂_le h_bounded`
    gives `ucCdist ≤ ε`; and `ucSdist = ⨆ D, ucDistComp f g D` (unrestricted), so the witness
    lower-bounds it via `le_iSup`. The `¬ adm D` part of the witness is what keeps it out of
    the `ucCdist` supremum — that is the entire point of the separation. -/
theorem ucCdist_lt_ucSdist_of_bounded {α β : Type} (f g : α → T β) {ε c : ℝ≥0∞}
    (h_bounded : ∀ D : β → T Bool, adm D → UCMonadCompDist.ucDistComp f g D ≤ ε)
    (h_witness : ∃ D : β → T Bool, ¬ adm D ∧ c ≤ UCMonadCompDist.ucDistComp f g D) :
    ucCdist f g ≤ ε ∧ c ≤ UCMonadMetric.ucSdist f g := by
  refine ⟨iSup₂_le h_bounded, ?_⟩
  obtain ⟨D, _, hD⟩ := h_witness
  rw [UCMonadCompDist.ucSdist_eq_iSup_distComp]
  exact le_trans hD (le_iSup (fun D => UCMonadCompDist.ucDistComp f g D) D)

/-- **Strict computational separation.** With `ε < c`, the two bounds of
    `ucCdist_lt_ucSdist_of_bounded` sandwich a strict gap:
    `ucCdist f g ≤ ε < c ≤ ucSdist f g`. -/
theorem ucCdist_lt_ucSdist_strict {α β : Type} (f g : α → T β) {ε c : ℝ≥0∞}
    (hεc : ε < c)
    (h_bounded : ∀ D : β → T Bool, adm D → UCMonadCompDist.ucDistComp f g D ≤ ε)
    (h_witness : ∃ D : β → T Bool, ¬ adm D ∧ c ≤ UCMonadCompDist.ucDistComp f g D) :
    ucCdist f g < UCMonadMetric.ucSdist f g := by
  obtain ⟨h1, h2⟩ := ucCdist_lt_ucSdist_of_bounded f g h_bounded h_witness
  exact lt_of_le_of_lt h1 (lt_of_lt_of_le hεc h2)

/-- **The separation at `sizeCompDist`.** Specialisation of `ucCdist_lt_ucSdist_of_bounded`
    to `SPComp` with the size-bounded class supplied explicitly: `h_bounded` now ranges over
    **size-bounded** distinguishers, and the witness is a **size-unbounded** (inadmissible)
    one. This is the statement the query-cost model could not carry: for query cost the
    optimal output-thresholding distinguisher has cost `0` (admissible), so `h_bounded` with
    `ε < 1` is already false; the size model makes the hypotheses consistent for a pair the
    pure class cannot read (see Section 5). Conditional on `h_bounded` — not unconditional. -/
theorem size_ucCdist_lt_ucSdist_of_bounded {α β : Type}
    (f g : α → SPComp β) {ε c : ℝ≥0∞}
    (h_bounded : ∀ D : β → SPComp Bool, adm (self := sizeCompDist.toUCAdmClass) D →
      UCMonadCompDist.ucDistComp (self := sizeCompDist) f g D ≤ ε)
    (h_witness : ∃ D : β → SPComp Bool, ¬ adm (self := sizeCompDist.toUCAdmClass) D ∧
      c ≤ UCMonadCompDist.ucDistComp (self := sizeCompDist) f g D) :
    @ucCdist SPComp sizeCompDist α β f g ≤ ε ∧
      c ≤ UCMonadMetric.ucSdist (self := sizeCompDist.toUCMonadMetric) f g :=
  @ucCdist_lt_ucSdist_of_bounded SPComp sizeCompDist α β f g ε c h_bounded h_witness

/-- **Strict separation at `sizeCompDist`**: `ucCdist < ucSdist` under `ε < c`, `h_bounded`,
    and a size-inadmissible witness. -/
theorem size_ucCdist_lt_ucSdist_strict {α β : Type}
    (f g : α → SPComp β) {ε c : ℝ≥0∞} (hεc : ε < c)
    (h_bounded : ∀ D : β → SPComp Bool, adm (self := sizeCompDist.toUCAdmClass) D →
      UCMonadCompDist.ucDistComp (self := sizeCompDist) f g D ≤ ε)
    (h_witness : ∃ D : β → SPComp Bool, ¬ adm (self := sizeCompDist.toUCAdmClass) D ∧
      c ≤ UCMonadCompDist.ucDistComp (self := sizeCompDist) f g D) :
    @ucCdist SPComp sizeCompDist α β f g <
      UCMonadMetric.ucSdist (self := sizeCompDist.toUCMonadMetric) f g :=
  @ucCdist_lt_ucSdist_strict SPComp sizeCompDist α β f g ε c hεc h_bounded h_witness

/-! ## Section 4: The equivalences at `sizeCompDist` (size-bounded adversaries) -/

/-- **Size-bounded computational dummy-adversary completeness.** Emulation against the dummy
    adversary implies computational UC emulation against every **size-bounded** adversary and
    every environment view. -/
theorem size_dummy_completeness_cdist
    {hon out leak sim_if : Type} {ε : ℝ≥0∞}
    (π : hon → SPComp (out ⊕ leak)) (F : hon → SPComp (out ⊕ sim_if))
    (h : @EmulatesDummyCdist SPComp sizeCompDist ε hon out leak sim_if π F) :
    ∀ view : Type,
      @UCEmulatesCdist SPComp sizeCompDist ε hon out leak sim_if view π F :=
  @dummy_completeness_cdist SPComp sizeCompDist hon out leak sim_if ε π F h

/-- **Size-bounded computational dummy-adversary theorem** (equivalence over all views). -/
theorem size_ucEmulatesCdist_iff_dummy
    {hon out leak sim_if : Type} {ε : ℝ≥0∞}
    (π : hon → SPComp (out ⊕ leak)) (F : hon → SPComp (out ⊕ sim_if)) :
    (∀ view : Type,
        @UCEmulatesCdist SPComp sizeCompDist ε hon out leak sim_if view π F)
      ↔ @EmulatesDummyCdist SPComp sizeCompDist ε hon out leak sim_if π F :=
  @ucEmulatesCdist_iff_dummy SPComp sizeCompDist hon out leak sim_if ε π F

/-- **Size-bounded computational CC ⟺ UC.** A construction (Maurer, TOSCA 2011, Def. 3)
    within `ε` in the size-bounded-distinguisher distance is exactly computational UC emulation within `ε`
    against every **size-bounded** adversary and every view. -/
theorem size_ccConstructsCdist_iff_ucEmulatesCdist
    {hon out leak sim_if : Type} {ε : ℝ≥0∞}
    (π : hon → SPComp (out ⊕ leak)) (F : hon → SPComp (out ⊕ sim_if)) :
    @CCConstructsCdist SPComp sizeCompDist ε hon out leak sim_if π F ↔
      ∀ view : Type,
        @UCEmulatesCdist SPComp sizeCompDist ε hon out leak sim_if view π F :=
  @ccConstructsCdist_iff_ucEmulatesCdist SPComp sizeCompDist hon out leak sim_if ε π F

/-! ## Section 5: The obstruction survives for output differences

On the canonical **output-difference** pair `Example.π` / `Example.F`, the leaked bit is on
the output channel, so a pure predicate reads it directly. Pure predicates are size-`1`
admissible (`adm_pure_predicate_size`), so the size-bounded `ucCdist` still equals `ucSdist`
here: `size` does not beat query cost when the difference is in the output. A genuine
separation therefore needs a pair the pure class cannot read (a heap / re-derivation
difference), which is where `h_bounded` stops being automatically false. -/

/-- The canonical separating distinguisher (reads the leaked bit off the `.inr` channel),
    written as a pure predicate test so it is manifestly size-bounded. -/
noncomputable def exD : (Unit ⊕ Bool) → SPComp Bool :=
  fun x => SPComp.pure (Sum.elim (fun _ => false) id x)

/-- `exD` is size-bounded-admissible (total size `1`). -/
theorem exD_adm : adm (self := sizeCompDist.toUCAdmClass) exD :=
  adm_pure_predicate_size (Sum.elim (fun _ => false) id)

/-- The size-`1` distinguisher `exD` separates the real leak `true` from the ideal leak
    `false` with advantage `1`. -/
theorem exD_advantage_one :
    absDiff (prTrue (SPComp.bind (Example.π ()) exD) Heap.empty)
            (prTrue (SPComp.bind (Example.F ()) exD) Heap.empty) = 1 := by
  have h1 : SPComp.bind (Example.π ()) exD = SPComp.pure true := by
    simp [Example.π, exD, SPComp.pure_bind, Sum.elim_inr]
  have h2 : SPComp.bind (Example.F ()) exD = SPComp.pure false := by
    simp [Example.F, exD, SPComp.pure_bind, Sum.elim_inr]
  rw [h1, h2, ForkingLemma.prTrue_pure_bool, ForkingLemma.prTrue_pure_bool]
  simp [absDiff]

/-- The size-bounded computational distance on the canonical pair is at least `1`: the
    admissible size-`1` distinguisher `exD` already achieves advantage `1`. -/
theorem ex_size_ucCdist_ge_one :
    (1 : ℝ≥0∞) ≤
      @ucCdist SPComp sizeCompDist Unit (Unit ⊕ Bool) Example.π Example.F := by
  refine le_iSup₂_of_le exD exD_adm ?_
  show (1 : ℝ≥0∞) ≤ ⨆ (a : Unit) (h₀ : Heap),
      absDiff (prTrue (SPComp.bind (Example.π a) exD) h₀)
              (prTrue (SPComp.bind (Example.F a) exD) h₀)
  exact le_iSup₂_of_le () Heap.empty (le_of_eq exD_advantage_one.symm)

/-- The statistical distance on the canonical pair is at most `1`. -/
theorem ex_size_ucSdist_le_one :
    UCMonadMetric.ucSdist (self := sizeCompDist.toUCMonadMetric)
        Example.π Example.F ≤ 1 := by
  show sdist Example.π Example.F ≤ 1
  refine iSup_le (fun D => iSup_le (fun a => iSup_le (fun h₀ => ?_)))
  simp only [absDiff]
  exact sup_le (le_trans tsub_le_self (prTrue_le_one _ _))
               (le_trans tsub_le_self (prTrue_le_one _ _))

/-- **No separation on the canonical output-difference pair.** The size-bounded computational
    distance equals the statistical distance (both `1`), realised by the size-`1` `exD` — so
    on an output difference `size` is no better than query cost. This pins the scope: the
    conditional separation is real only for pairs the pure class cannot read. -/
theorem ex_size_no_separation :
    @ucCdist SPComp sizeCompDist Unit (Unit ⊕ Bool) Example.π Example.F
      = UCMonadMetric.ucSdist (self := sizeCompDist.toUCMonadMetric)
          Example.π Example.F :=
  le_antisymm
    (@ucCdist_le_ucSdist SPComp sizeCompDist Unit (Unit ⊕ Bool) Example.π Example.F)
    (le_trans ex_size_ucSdist_le_one ex_size_ucCdist_ge_one)

end CatCrypt.Crypto.SizeBoundedUC
