/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Crypto.NomAdvantage
import CatCryptCore.Crypto.SDist
import CatCryptCore.Crypto.EvalComplete
import CatCryptCore.Crypto.UC

/-!
# NomPkg Bridge: Game-Based Security → sdist

This file bridges game-based security (`∀ A, Advantage ≤ ε`) to the categorical
`sdist` framework, enabling composition via post-processing lemmas.

## Main results

* `SPComp.NoFail` — computation never produces failure
* `sdist_le_of_advantage_bool` — sdist for Bool-valued IsPure+NoFail SPComps from Advantage
* `sdist_of_deepNomAdvantage` — bridge for deep nominal packages
* `nomPkg_absorb` — general absorption of post-processing into the adversary

## Key insight

For Bool-valued IsPure+NoFail computations, any post-processing distinguisher
`D : Bool → SPComp Bool` cannot increase the advantage beyond what the identity
distinguisher achieves. This is a post-processing lemma for binary channels.
-/

namespace CatCrypt.Crypto

open CatCrypt.Core CatCrypt.Prob

open scoped ENNReal

/-! ## NoFail -/

/-- A computation never fails: all mass is on successful outcomes. -/
def SPComp.NoFail {α : Type*} (c : SPComp α) : Prop :=
  ∀ h, (c h) none = 0

/-- `pure a` never fails. -/
theorem SPComp.pure_noFail {α : Type*} (a : α) : SPComp.NoFail (SPComp.pure a) := by
  intro h; simp [SPComp.pure, SDistr.pure, PMF.pure_apply]

/-! ### Compositional NoFail helpers -/

namespace Assumptions

/-- **Bind preserves NoFail**: if `c` is NoFail and every `f a` is
NoFail, then `c >>= f` is NoFail. -/
theorem SPComp.bind_noFail {α β : Type*}
    {c : SPComp α} {f : α → SPComp β}
    (hc : SPComp.NoFail c) (hf : ∀ a, SPComp.NoFail (f a)) :
    SPComp.NoFail (SPComp.bind c f) := by
  intro h
  unfold SPComp.bind SDistr.bind
  simp only [PMF.bind_apply]
  rw [SDistr.tsum_option_eq_add]
  -- The `none` term: (c h) none · fail.none = 0 · 1 = 0 by hc.
  rw [hc h, zero_mul, zero_add]
  -- The `some` term: ∑' (a, h'), (c h)(some (a,h')) · (f a)(h')(none) = 0 by hf.
  apply ENNReal.tsum_eq_zero.mpr
  rintro ⟨a, h'⟩
  show (c h) (some (a, h')) * (f a h') none = 0
  rw [hf a h']
  ring

/-- **`SPComp.sample` is NoFail**: uniform distributions assign 0
mass to the failure slot. -/
theorem SPComp.sample_noFail {α : Type} [Fintype α] [Nonempty α] :
    SPComp.NoFail (SPComp.sample α) := by
  intro h
  simp only [SPComp.sample, SDistr.bind, PMF.bind_apply]
  rw [SDistr.tsum_option_eq_add]
  rw [SDistr.uniform_apply_none, zero_mul, zero_add]
  apply ENNReal.tsum_eq_zero.mpr
  intro a
  show (SDistr.uniform α) (some a) * (SDistr.pure (a, h)) none = 0
  rw [SDistr.pure_apply_none, mul_zero]

end Assumptions

/-! ## IsPure + NoFail Helpers -/

/-- For IsPure c, the bind `c >>= D` at h₀ equals `d.bind(fun a => D a h₀)`. -/
private theorem isPure_bind_eq {α β : Type*} {c : SPComp α} {d : SDistr α}
    (hc : ∀ h, c h = d.bind (fun a => SDistr.pure (a, h)))
    (D : α → SPComp β) (h₀ : Heap) :
    (SPComp.bind c D) h₀ = d.bind (fun a => D a h₀) := by
  simp only [SPComp.bind, hc h₀, SDistr.bind_assoc, SDistr.pure_bind]

/-- For IsPure+NoFail, the witness distribution d has d(none) = 0. -/
theorem isPure_noFail_d_none {α : Type*} {c : SPComp α} {d : SDistr α}
    (hc : ∀ h, c h = d.bind (fun a => SDistr.pure (a, h)))
    (hnf : SPComp.NoFail c) :
    d none = 0 := by
  have h := hnf Heap.empty
  rw [hc] at h
  simp only [SDistr.bind, PMF.bind_apply] at h
  rw [SDistr.tsum_option_eq_add] at h
  simp only [SDistr.fail_apply_none, mul_one, SDistr.pure_apply_none, mul_zero,
             tsum_zero, add_zero] at h
  exact h

/-- For IsPure c : SPComp Bool with witness d, the bind `(d.bind f)(some(b, h₀))`
    is zero when `h ≠ h₀`, because d.bind produces outputs only at heap h₀. -/
private theorem isPure_bind_some_ne {c : SPComp Bool} {d : SDistr Bool}
    (hc : ∀ h, c h = d.bind (fun a => SDistr.pure (a, h)))
    (h₀ h : Heap) (b : Bool) (hne : h ≠ h₀) :
    (c h₀) (some (b, h)) = 0 := by
  rw [hc]
  simp only [SDistr.bind, PMF.bind_apply]
  apply ENNReal.tsum_eq_zero.mpr
  intro ob
  rcases ob with _ | a
  · simp [SDistr.fail_apply_some]
  · simp only [SDistr.pure, PMF.pure_apply]
    have : some (b, h) ≠ some (a, h₀) := by
      intro h_eq; exact hne (congrArg Prod.snd (Option.some.inj h_eq))
    rw [if_neg this, mul_zero]

/-- For IsPure c : SPComp Bool, `prTrue c h₀ = d(some true)` for any h₀.
    The heap doesn't affect the output distribution. -/
theorem prTrue_isPure_eq {c : SPComp Bool} {d : SDistr Bool}
    (hc : ∀ h, c h = d.bind (fun a => SDistr.pure (a, h)))
    (h₀ : Heap) :
    prTrue c h₀ = d (some true) := by
  unfold prTrue
  -- The sum ∑' h, (c h₀)(some(true, h)) collapses to h = h₀
  rw [tsum_eq_single h₀ (fun h hne => isPure_bind_some_ne hc h₀ h true hne)]
  -- Remaining: (c h₀)(some(true, h₀)) = d(some true)
  rw [hc]
  simp only [SDistr.bind, PMF.bind_apply]
  rw [SDistr.tsum_option_eq_add]
  simp only [SDistr.fail_apply_some, mul_zero, zero_add]
  -- ∑' a, d(some a) * SDistr.pure(a, h₀)(some(true, h₀))
  rw [tsum_bool]
  simp [SDistr.pure, PMF.pure_apply]

/-- For IsPure+NoFail d : SDistr Bool, d(some false) = 1 - d(some true). -/
private theorem isPure_noFail_complement {d : SDistr Bool}
    (hnf : d none = 0) :
    d (some false) = 1 - d (some true) := by
  have htotal := d.tsum_coe
  rw [SDistr.tsum_option_eq_add, hnf, zero_add, tsum_bool, add_comm] at htotal
  -- htotal : d(some true) + d(some false) = 1
  have h_ne_top : d (some true) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.one_ne_top (htotal ▸ le_self_add)
  rw [← htotal]
  exact (ENNReal.add_sub_cancel_left h_ne_top).symm

/-- For IsPure+NoFail, d(some true) ≤ 1. -/
private theorem isPure_noFail_le_one {d : SDistr Bool}
    (hnf : d none = 0) :
    d (some true) ≤ 1 := by
  have htotal := d.tsum_coe
  rw [SDistr.tsum_option_eq_add, hnf, zero_add, tsum_bool, add_comm] at htotal
  -- htotal : d(some true) + d(some false) = 1
  rw [← htotal]; exact le_self_add

/-! ## Algebraic Inequality: Convex Combination Bound -/

/-- Auxiliary: for r ≤ s ≤ 1, the expression with smaller weight r is bounded by
    the expression with larger weight s plus the weight difference (s - r).
    This is one direction of the convex bound. -/
private theorem convex_le_add_tsub₁ {x y : ℝ≥0∞}
    (r s : ℝ≥0∞) (hrs : r ≤ s) (hs1 : s ≤ 1) (hy : y ≤ 1) :
    r * x + (1 - r) * y ≤ (s * x + (1 - s) * y) + (s - r) := by
  have h_split : 1 - r = (1 - s) + (s - r) := (tsub_add_tsub_cancel hs1 hrs).symm
  calc r * x + (1 - r) * y
      = r * x + ((1 - s) + (s - r)) * y := by rw [h_split]
    _ = r * x + ((1 - s) * y + (s - r) * y) := by rw [add_mul]
    _ = (r * x + (1 - s) * y) + (s - r) * y := by rw [add_assoc]
    _ ≤ (s * x + (1 - s) * y) + (s - r) * y := by gcongr
    _ ≤ (s * x + (1 - s) * y) + (s - r) := by
        gcongr; exact mul_le_of_le_one_right (zero_le) hy

/-- Auxiliary: the reverse direction — the expression with larger weight s is also
    bounded by the expression with smaller weight r plus (s - r). -/
private theorem convex_le_add_tsub₂ {x y : ℝ≥0∞}
    (r s : ℝ≥0∞) (hrs : r ≤ s) (_hs1 : s ≤ 1) (hx : x ≤ 1) :
    s * x + (1 - s) * y ≤ (r * x + (1 - r) * y) + (s - r) := by
  calc s * x + (1 - s) * y
      ≤ (r * x + (s - r)) + (1 - r) * y := by
        apply add_le_add
        · calc s * x = ((s - r) + r) * x := by rw [tsub_add_cancel_of_le hrs]
            _ = (s - r) * x + r * x := add_mul _ _ _
            _ ≤ (s - r) + r * x := by
                gcongr; exact mul_le_of_le_one_right (zero_le) hx
            _ = r * x + (s - r) := add_comm _ _
        · gcongr
    _ = (r * x + (1 - r) * y) + (s - r) := by
        rw [add_assoc, add_comm (s - r) ((1 - r) * y), ← add_assoc]

/-- Key algebraic fact: the absDiff of two convex combinations (with the same
    endpoints but different weights) is bounded by the absDiff of the weights.

    This is the post-processing lemma for binary channels. -/
theorem absDiff_convex_le (p q x y : ℝ≥0∞)
    (hp : p ≤ 1) (hq : q ≤ 1)
    (hx : x ≤ 1) (hy : y ≤ 1) :
    absDiff (p * x + (1 - p) * y) (q * x + (1 - q) * y) ≤ absDiff p q := by
  simp only [absDiff]
  -- tsub_le_iff_right rewrites (a - b ≤ c) to (a ≤ c + b)
  apply max_le <;> rw [tsub_le_iff_right]
  · -- p*x + (1-p)*y ≤ absDiff(p,q) + (q*x + (1-q)*y)
    rcases le_total p q with hpq | hqp
    · calc p * x + (1 - p) * y
          ≤ (q * x + (1 - q) * y) + (q - p) := convex_le_add_tsub₁ p q hpq hq hy
        _ ≤ (q * x + (1 - q) * y) + ((p - q) ⊔ (q - p)) := by
            gcongr; exact le_max_right _ _
        _ = ((p - q) ⊔ (q - p)) + (q * x + (1 - q) * y) := add_comm _ _
    · calc p * x + (1 - p) * y
          ≤ (q * x + (1 - q) * y) + (p - q) := convex_le_add_tsub₂ q p hqp hp hx
        _ ≤ (q * x + (1 - q) * y) + ((p - q) ⊔ (q - p)) := by
            gcongr; exact le_max_left _ _
        _ = ((p - q) ⊔ (q - p)) + (q * x + (1 - q) * y) := add_comm _ _
  · -- q*x + (1-q)*y ≤ absDiff(p,q) + (p*x + (1-p)*y)
    rcases le_total p q with hpq | hqp
    · calc q * x + (1 - q) * y
          ≤ (p * x + (1 - p) * y) + (q - p) := convex_le_add_tsub₂ p q hpq hq hx
        _ ≤ (p * x + (1 - p) * y) + ((p - q) ⊔ (q - p)) := by
            gcongr; exact le_max_right _ _
        _ = ((p - q) ⊔ (q - p)) + (p * x + (1 - p) * y) := add_comm _ _
    · calc q * x + (1 - q) * y
          ≤ (p * x + (1 - p) * y) + (p - q) := convex_le_add_tsub₁ q p hqp hp hy
        _ ≤ (p * x + (1 - p) * y) + ((p - q) ⊔ (q - p)) := by
            gcongr; exact le_max_left _ _
        _ = ((p - q) ⊔ (q - p)) + (p * x + (1 - p) * y) := add_comm _ _

/-! ## prTrue Decomposition for IsPure+NoFail Bool -/

/-- For IsPure+NoFail c : SPComp Bool, `prTrue(c >>= D, h₀)` decomposes as
    `p * prTrue(D true, h₀) + (1-p) * prTrue(D false, h₀)` where `p = d(some true)`. -/
theorem prTrue_isPure_noFail_bind {c : SPComp Bool} {d : SDistr Bool}
    (hc : ∀ h, c h = d.bind (fun a => SDistr.pure (a, h)))
    (hnf : d none = 0)
    (D : Bool → SPComp Bool) (h₀ : Heap) :
    prTrue (SPComp.bind c D) h₀ =
      d (some true) * prTrue (D true) h₀ +
      d (some false) * prTrue (D false) h₀ := by
  unfold prTrue
  -- Step 1: bind expansion via IsPure
  conv_lhs => arg 1; ext h; rw [isPure_bind_eq hc D h₀]
  -- Now: ∑' h, (d.bind(fun b => D b h₀))(some(true, h))
  -- Step 2: Expand SDistr.bind via PMF.bind_apply
  simp only [SDistr.bind, PMF.bind_apply]
  -- Step 3: Split the inner tsum over Option Bool and eliminate none
  conv_lhs =>
    arg 1; ext h
    rw [SDistr.tsum_option_eq_add]
  simp only [hnf, zero_mul, zero_add]
  -- Step 4: Split Bool tsum
  conv_lhs => arg 1; ext h; rw [tsum_bool]
  -- Step 5: Distribute outer tsum over addition, factor out constants
  -- tsum_bool gives f false + f true, so we need add_comm to match the goal
  rw [ENNReal.tsum_add, ENNReal.tsum_mul_left, ENNReal.tsum_mul_left, add_comm]

/-! ## D-Absorption for Bool (Post-Processing Lemma) -/

/-- Core D-absorption: for IsPure+NoFail c₁, c₂ : SPComp Bool, any D cannot
    increase the advantage beyond what the identity distinguisher achieves. -/
theorem absDiff_bind_le_advantage {c₁ c₂ : SPComp Bool}
    (hc₁ : SPComp.IsPure c₁) (hc₂ : SPComp.IsPure c₂)
    (hnf₁ : SPComp.NoFail c₁) (hnf₂ : SPComp.NoFail c₂)
    (D : Bool → SPComp Bool) (h₀ : Heap) :
    absDiff (prTrue (SPComp.bind c₁ D) h₀)
            (prTrue (SPComp.bind c₂ D) h₀) ≤ Advantage c₁ c₂ := by
  obtain ⟨d₁, hd₁⟩ := hc₁
  obtain ⟨d₂, hd₂⟩ := hc₂
  have hd₁_nf := isPure_noFail_d_none hd₁ hnf₁
  have hd₂_nf := isPure_noFail_d_none hd₂ hnf₂
  -- Decompose prTrue into weighted sums
  rw [prTrue_isPure_noFail_bind hd₁ hd₁_nf D h₀,
      prTrue_isPure_noFail_bind hd₂ hd₂_nf D h₀]
  -- Use d(some false) = 1 - d(some true) (NoFail)
  rw [isPure_noFail_complement hd₁_nf, isPure_noFail_complement hd₂_nf]
  -- Advantage = absDiff(d₁(some true), d₂(some true))
  have hAdv : Advantage c₁ c₂ = absDiff (d₁ (some true)) (d₂ (some true)) := by
    show absDiff (prTrue c₁ Heap.empty) (prTrue c₂ Heap.empty) =
      absDiff (d₁ (some true)) (d₂ (some true))
    congr 1
    · exact prTrue_isPure_eq hd₁ Heap.empty
    · exact prTrue_isPure_eq hd₂ Heap.empty
  rw [hAdv]
  exact absDiff_convex_le _ _ _ _
    (isPure_noFail_le_one hd₁_nf) (isPure_noFail_le_one hd₂_nf)
    (prTrue_le_one _ _) (prTrue_le_one _ _)

/-! ## Main Bridge: Advantage → sdist -/

/-- **Main bridge theorem**: for Bool-valued IsPure+NoFail computations,
    `∀ a, Advantage(f a)(g a) ≤ ε` implies `sdist f g ≤ ε`.

    This combines:
    1. `sdist_isPure_le` — absorbs h₀ into the distinguisher via IsPure
    2. `absDiff_bind_le_advantage` — D-absorption for Bool with NoFail -/
theorem sdist_le_of_advantage_bool {α : Type*} {f g : α → SPComp Bool} {ε : ℝ≥0∞}
    (hf_pure : ∀ a, SPComp.IsPure (f a))
    (hg_pure : ∀ a, SPComp.IsPure (g a))
    (hf_nf : ∀ a, SPComp.NoFail (f a))
    (hg_nf : ∀ a, SPComp.NoFail (g a))
    (hAdv : ∀ a, Advantage (f a) (g a) ≤ ε) :
    sdist f g ≤ ε := by
  apply sdist_isPure_le hf_pure hg_pure
  intro D a
  exact le_trans
    (absDiff_bind_le_advantage (hf_pure a) (hg_pure a) (hf_nf a) (hg_nf a) D _)
    (hAdv a)

/-! ## NomPkg Bridge -/

universe u_np in
/-- Bridge for deep nominal packages: game-based security implies sdist bound.

    Given `∀ A : NomPkg, DeepNomAdvantage G G' A ≤ ε`, this yields
    `sdist (fun A => runPkg(link A G)) (fun A => runPkg(link A G')) ≤ ε`.

    Requires IsPure+NoFail for the linked computations.
    Universe parameters are pinned to avoid auto-binding divergence. -/
theorem sdist_of_deepNomAdvantage
    {G G' : CatCrypt.Deep.NomPackage} {ε : ℝ≥0∞}
    (hPure_r : ∀ (A : CatCrypt.Deep.NomPackage),
      SPComp.IsPure (runPkg (CatCrypt.Deep.DeepPackage.link A.pkg G.pkg)))
    (hPure_i : ∀ (A : CatCrypt.Deep.NomPackage),
      SPComp.IsPure (runPkg (CatCrypt.Deep.DeepPackage.link A.pkg G'.pkg)))
    (hNF_r : ∀ (A : CatCrypt.Deep.NomPackage),
      SPComp.NoFail (runPkg (CatCrypt.Deep.DeepPackage.link A.pkg G.pkg)))
    (hNF_i : ∀ (A : CatCrypt.Deep.NomPackage),
      SPComp.NoFail (runPkg (CatCrypt.Deep.DeepPackage.link A.pkg G'.pkg)))
    (hAdv : ∀ (A : CatCrypt.Deep.NomPackage),
      DeepNomAdvantage G G' A ≤ ε) :
    sdist (fun (A : CatCrypt.Deep.NomPackage) =>
             runPkg (CatCrypt.Deep.DeepPackage.link A.pkg G.pkg))
          (fun (A : CatCrypt.Deep.NomPackage) =>
             runPkg (CatCrypt.Deep.DeepPackage.link A.pkg G'.pkg)) ≤ ε :=
  sdist_le_of_advantage_bool hPure_r hPure_i hNF_r hNF_i (fun A => hAdv A)

/-! ## General Absorption Bridge -/

/-- General absorption bridge: if for every (D, a, h₀) triple there exists
    an a' whose Advantage dominates the post-processed advantage, then
    `sdist f g ≤ ε`.

    This cleanly separates:
    - **General math** (this theorem): absorption implies sdist bound
    - **Protocol-specific claim** (caller-provided): the adversary space can
      absorb post-processing D and initial heap h₀ -/
theorem sdist_le_of_advantage_absorb {α : Type*} {f g : α → SPComp Bool} {ε : ℝ≥0∞}
    (h_absorb : ∀ (D : Bool → SPComp Bool) (a : α) (h₀ : Heap),
      ∃ a', absDiff (prTrue (SPComp.bind (f a) D) h₀)
                     (prTrue (SPComp.bind (g a) D) h₀) ≤
            Advantage (f a') (g a'))
    (hAdv : ∀ a, Advantage (f a) (g a) ≤ ε) :
    sdist f g ≤ ε := by
  apply iSup_le; intro D
  apply iSup_le; intro a
  apply iSup_le; intro h₀
  obtain ⟨a', ha'⟩ := h_absorb D a h₀
  exact le_trans ha' (hAdv a')

/-! ## NomPkg Absorption via Eval Completeness

The key theorem: for any game pair (G, G'), post-processor D, adversary A,
and initial heap h₀, there exists A' such that the post-processed absDiff
is bounded by A's Advantage.

This uses `RawCode.ofSPComp` (from `EvalComplete`) to embed arbitrary SPComp
computations into the deep embedding, enabling construction of A' that wraps
A's oracle-calling code with heap reset and post-processing. -/

/-- Reset heap to a target state. All existing heap contents are replaced. -/
noncomputable def heapReset (h₀ : Heap) : SPComp Unit :=
  fun _ => SDistr.pure ((), h₀)

/-- `heapReset h₀` at any initial heap produces `((), h₀)`. -/
theorem heapReset_apply (h₀ h : Heap) : (heapReset h₀) h = SDistr.pure ((), h₀) := rfl

/-- Binding with `heapReset` shifts the initial heap.
    `SPComp.bind (heapReset h₀) f` at any heap `h` equals `f () h₀`. -/
theorem bind_heapReset {β : Type*} (h₀ : Heap) (f : Unit → SPComp β) (h : Heap) :
    (SPComp.bind (heapReset h₀) f) h = f () h₀ := by
  simp only [SPComp.bind, heapReset, SDistr.pure_bind]

/-- `prTrue` after heap reset shifts the initial heap. -/
theorem prTrue_bind_heapReset (h₀ : Heap) (c : SPComp Bool) :
    prTrue (SPComp.bind (heapReset h₀) (fun _ => c)) Heap.empty = prTrue c h₀ := by
  unfold prTrue
  simp only [bind_heapReset]

/-- Construct a NomPkg that wraps A's main export with heap reset and
    post-processing D. A' has the same exports, imports, and locations as A,
    but the `(0, Unit, Bool)` export is wrapped:
    - Phase 1: `ofSPComp(heapReset h₀)` — reset heap (no oracle calls)
    - Phase 2: A's original code (with oracle calls to game)
    - Phase 3: `ofSPComp(D b)` — post-process (no oracle calls) -/
noncomputable def wrapMainNomPkg
    (A : CatCrypt.Deep.NomPackage)
    (h_main : (0, Unit, Bool) ∈ A.pkg.exports.ops)
    (D : Bool → SPComp Bool) (h₀ : Heap) : CatCrypt.Deep.NomPackage :=
  let a_vc := A.pkg.impl 0 Unit Bool h_main ()
  let wrapped_vc : CatCrypt.Deep.ValidCodeBundle A.pkg.locs Bool :=
    ⟨.bind (CatCrypt.Deep.RawCode.ofSPComp (heapReset h₀))
       (fun _ => .bind a_vc.code
         (fun b => CatCrypt.Deep.RawCode.ofSPComp (D b))),
     CatCrypt.Deep.ValidCode.bind _ _
       (CatCrypt.Deep.ValidCode.ofSPComp _ _) (fun _ =>
       CatCrypt.Deep.ValidCode.bind _ _ a_vc.valid
         (fun b => CatCrypt.Deep.ValidCode.ofSPComp _ _))⟩
  { pkg := {
      locs := A.pkg.locs
      imports := A.pkg.imports
      exports := A.pkg.exports
      impl := fun op dom codom h x => by
        classical
        by_cases h_eq : (op, dom, codom) = (0, Unit, Bool)
        · have h_codom : codom = Bool := congr_arg (fun p => p.2.2) h_eq
          subst h_codom
          exact wrapped_vc
        · exact A.pkg.impl op dom codom h x
    }
    registry := A.registry
    usedAtoms := A.usedAtoms
    locs_eq := A.locs_eq }

/-- Key evaluation lemma: `runPkg(wrapMain(A).link(G))` at `Heap.empty`
    equals `runPkg(A.link(G)).bind(D)` at `h₀`.

    After linking with G, oracle calls in A's code get resolved. The
    ofSPComp phases (heapReset and D) are transparent to substOracle. -/
private theorem wrapMainNomPkg_impl_code
    (A : CatCrypt.Deep.NomPackage)
    (h_main : (0, Unit, Bool) ∈ A.pkg.exports.ops)
    (D : Bool → SPComp Bool) (h₀ : Heap)
    (h' : (0, Unit, Bool) ∈ (wrapMainNomPkg A h_main D h₀).pkg.exports.ops) :
    ((wrapMainNomPkg A h_main D h₀).pkg.impl 0 Unit Bool h' ()).code =
    .bind (CatCrypt.Deep.RawCode.ofSPComp (heapReset h₀))
      (fun _ => .bind (A.pkg.impl 0 Unit Bool h_main ()).code
        (fun b => CatCrypt.Deep.RawCode.ofSPComp (D b))) := by
  unfold wrapMainNomPkg
  simp only [dite_true]

theorem runPkg_wrapMain_eq
    (A : CatCrypt.Deep.NomPackage)
    (G : CatCrypt.Deep.NomPackage)
    (h_main : (0, Unit, Bool) ∈ A.pkg.exports.ops)
    (D : Bool → SPComp Bool) (h₀ : Heap) :
    prTrue (runPkg (CatCrypt.Deep.DeepPackage.link
      (wrapMainNomPkg A h_main D h₀).pkg G.pkg)) Heap.empty =
    prTrue (SPComp.bind (runPkg (CatCrypt.Deep.DeepPackage.link A.pkg G.pkg)) D) h₀ := by
  -- Expand runPkg via runPkg_link
  rw [runPkg_link, runPkg_link]
  -- wrapMainNomPkg preserves exports, so (0, Unit, Bool) membership holds
  have h_wrap : (0, Unit, Bool) ∈ (wrapMainNomPkg A h_main D h₀).pkg.exports.ops := by
    simp only [wrapMainNomPkg]; exact h_main
  simp only [h_wrap, h_main, dite_true]
  -- Rewrite the wrapped impl's code using our helper lemma
  rw [wrapMainNomPkg_impl_code A h_main D h₀ h_wrap]
  -- Now the LHS code is: bind(ofSPComp(heapReset h₀), fun _ => bind(a_vc.code, fun b => ofSPComp(D b)))
  -- evalWith distributes through bind, and ofSPComp_evalWith simplifies ofSPComp terms
  simp only [CatCrypt.Deep.RawCode.evalWith]
  -- Now: prTrue(heapReset(h₀).bind(fun _ => a_vc.code.evalWith(handler).bind(D))) Heap.empty
  --    = prTrue(a_vc.code.evalWith(handler).bind(D)) h₀
  exact prTrue_bind_heapReset h₀ _

/-- **General NomPkg absorption theorem.**

    For any game pair (G, G'), post-processor D, adversary A, and initial
    heap h₀, there exists A' whose Advantage dominates the post-processed
    absDiff. This is the core lemma for lifting game-based security to sdist.

    The construction: A' wraps A's main export with `heapReset h₀` (to shift
    the initial heap) and `D` (to absorb post-processing). After linking with
    G, the oracle calls in A's code get resolved as before, while the
    `ofSPComp` phases are transparent to `substOracle`.

    This eliminates the need for `IsPure`/`NoFail` assumptions. -/
theorem nomPkg_absorb
    (G G' : CatCrypt.Deep.NomPackage)
    (D : Bool → SPComp Bool) (A : CatCrypt.Deep.NomPackage) (h₀ : Heap) :
    ∃ A' : CatCrypt.Deep.NomPackage,
      absDiff (prTrue (SPComp.bind (runPkg (CatCrypt.Deep.DeepPackage.link A.pkg G.pkg)) D) h₀)
              (prTrue (SPComp.bind (runPkg (CatCrypt.Deep.DeepPackage.link A.pkg G'.pkg)) D) h₀) ≤
      Advantage (runPkg (CatCrypt.Deep.DeepPackage.link A'.pkg G.pkg))
                (runPkg (CatCrypt.Deep.DeepPackage.link A'.pkg G'.pkg)) := by
  -- Case split: does A export the main operation?
  by_cases h_main : (0, Unit, Bool) ∈ A.pkg.exports.ops
  · -- A exports main: construct A' via wrapMain
    refine ⟨wrapMainNomPkg A h_main D h₀, ?_⟩
    -- Rewrite both prTrue using runPkg_wrapMain_eq
    rw [← runPkg_wrapMain_eq A G h_main D h₀,
        ← runPkg_wrapMain_eq A G' h_main D h₀]
    -- Now LHS = absDiff(prTrue f empty, prTrue g empty) ≤ Advantage f g = RHS
    exact le_of_eq (by unfold Advantage; rfl)
  · -- A doesn't export main: runPkg returns pure true for both games
    refine ⟨A, ?_⟩
    -- When (0, Unit, Bool) ∉ A.pkg.exports.ops, runPkg returns pure true
    -- link preserves exports, so the condition still fails
    have h_link_real : (0, Unit, Bool) ∉ (CatCrypt.Deep.DeepPackage.link A.pkg G.pkg).exports.ops := by
      simp only [CatCrypt.Deep.DeepPackage.link]; exact h_main
    have h_link_ideal : (0, Unit, Bool) ∉ (CatCrypt.Deep.DeepPackage.link A.pkg G'.pkg).exports.ops := by
      simp only [CatCrypt.Deep.DeepPackage.link]; exact h_main
    simp only [runPkg, h_link_real, h_link_ideal, dite_false]
    simp only [Advantage, absDiff_self]
    exact zero_le

/-! ## Automation Tactic -/

/-- Tactic: bridge game-based advantage to sdist bound for NomPkg games. -/
macro "sdist_from_deep" : tactic =>
  `(tactic| (apply sdist_of_deepNomAdvantage <;> assumption))

/-- Tactic: bridge a deep nominal advantage bound to a `UCEmulates` goal, via
    `UCEmulates_of_sdist` then `sdist_from_deep`. -/
macro "uc_from_deep" : tactic =>
  `(tactic| (apply UCEmulates_of_sdist; sdist_from_deep))

end CatCrypt.Crypto
