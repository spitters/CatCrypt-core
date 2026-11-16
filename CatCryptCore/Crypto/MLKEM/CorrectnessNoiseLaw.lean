/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.MLKEM.CorrectnessUnion
public import CatCryptCore.Crypto.MLKEM.SamplerCbd

/-!
# The law of one coefficient of the ML-KEM decryption noise

Under uniform key-generation and encryption coins, every coefficient of the decryption
noise `e · r + e₂ − s · e₁` at module rank `k` is the reduction modulo `3329` of an integer
`a + z − b`, where `a` is a sum of `256 k` independent products of two `cbd η₁` draws, `z`
is a `cbd η₂` draw and `b` is a sum of `256 k` independent products of a `cbd η₁` and a
`cbd η₂` draw, all independent.

The proof works at the level of the bit windows of the PRF blocks. The coefficient `i`
of a negacyclic product `x · y` is `Σ_l ± x_l y_{i−l}`, with sign `−1` exactly when
`l > i`; reindexing the windows of `y` by `l ↦ i − l` and swapping the two halves of a
window where the sign is `−1` is an involution of the window space, so it preserves the
uniform distribution and turns the coefficient into a plain sum of products of window
values.

## Main definitions

* `sumIID d n` — the law of the sum of `n` independent draws from `d`
* `cbdProd η η'` — the law of the product of independent `cbd η` and `cbd η'` draws
* `noiseCoeffLaw k η₁ η₂` — the law of one coefficient of the decryption noise over `ℤ`

## Main results

* `uniform_sum_law` — the sum of a function of the coordinates of a uniform function
  has the law `sumIID`
* `uniform_wDot` — the window dot product of two uniform window vectors has the law
  `sumIID (cbdProd η η') (k * 256)`
* `coinNoise_law` — the law of coefficient `i` of the decryption noise under uniform
  coins is `noiseCoeffLaw k η₁ η₂` reduced modulo `3329`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.MLKEM.MLKEMRankInstance

open CatCrypt.Prob CatCrypt.NonUniform CatCrypt.Util
open MLKEM512Instance (PrfBlock ringMul)
open SamplerCbd (Win windowVal windowMap windowMap_bijective samplePoly_eq uniform_windowVal
  bind_of_pushforward uniform_of_subsingleton)

/-! ## The laws -/

/-- The law of the sum of `n` independent draws from `d`. -/
noncomputable def sumIID (d : SDistr ℤ) : ℕ → SDistr ℤ
  | 0 => SDistr.pure 0
  | n + 1 => d.bind fun a => (sumIID d n).bind fun b => SDistr.pure (a + b)

/-- The law of the product of independent `cbd η` and `cbd η'` draws. -/
noncomputable def cbdProd (η η' : ℕ) : SDistr ℤ :=
  (cbd η).bind fun x => (cbd η').bind fun y => SDistr.pure (x * y)

/-- The law over `ℤ` of one coefficient of the decryption noise `e · r + e₂ − s · e₁` at
rank `k`: `a + z − b` with `a ← sumIID (cbdProd η₁ η₁) (k * 256)`, `z ← cbd η₂` and
`b ← sumIID (cbdProd η₁ η₂) (k * 256)` independent. -/
noncomputable def noiseCoeffLaw (k η₁ η₂ : ℕ) : SDistr ℤ :=
  (sumIID (cbdProd η₁ η₁) (k * 256)).bind fun a =>
    (cbd η₂).bind fun z =>
      (sumIID (cbdProd η₁ η₂) (k * 256)).bind fun b => SDistr.pure (a + z - b)

/-! ## Pushforward lemmas -/

/-- A bind along a two-argument map factors through the law of that map. -/
theorem bind_of_pushforward₂ {α β γ δ : Type} {d₁ : SDistr α} {d₂ : SDistr β}
    {f : α → β → γ} {d' : SDistr γ}
    (h : d₁.bind (fun x => d₂.bind fun y => SDistr.pure (f x y)) = d') (g : γ → SDistr δ) :
    d₁.bind (fun x => d₂.bind fun y => g (f x y)) = d'.bind g := by
  rw [← h]
  simp only [SDistr.bind_assoc, SDistr.pure_bind]

/-- The sum of a function `g` of the coordinates of a uniform `P : Fin n → α` has the
law `sumIID d n`, where `d` is the law of `g` under a uniform argument. -/
theorem uniform_sum_law {α : Type} [Fintype α] [Nonempty α] (g : α → ℤ) (d : SDistr ℤ)
    (hg : (SDistr.uniform α).bind (fun a => SDistr.pure (g a)) = d) :
    ∀ n : ℕ, (SDistr.uniform (Fin n → α)).bind (fun P => SDistr.pure (∑ t, g (P t))) =
      sumIID d n
  | 0 => by
    rw [uniform_of_subsingleton (fun t : Fin 0 => t.elim0), SDistr.pure_bind]
    simp [sumIID]
  | n + 1 => by
    rw [← SDistr.uniform_bind_equiv_comp (Fin.consEquiv fun _ : Fin (n + 1) => α),
      ← SDistr.uniform_nested_eq_prod]
    simp only [SDistr.bind_assoc, SDistr.pure_bind]
    have hc : ∀ (a : α) (f : Fin n → α),
        ∑ t, g ((Fin.consEquiv fun _ : Fin (n + 1) => α) (a, f) t) = g a + ∑ t, g (f t) :=
      fun a f => by
        change ∑ t, g ((Fin.cons a f : Fin (n + 1) → α) t) = _
        rw [Fin.sum_univ_succ]
        simp
    simp only [hc]
    rw [sumIID,
      ← bind_of_pushforward hg (fun x => (sumIID d n).bind fun b => SDistr.pure (x + b))]
    congr 1
    funext a
    exact bind_of_pushforward (uniform_sum_law g d hg n) (fun b => SDistr.pure (g a + b))

/-- `uniform_sum_law` over a finite index type. -/
theorem uniform_sum_law_fintype {α ι : Type} [Fintype α] [Nonempty α] [Fintype ι]
    [DecidableEq ι] (g : α → ℤ) (d : SDistr ℤ)
    (hg : (SDistr.uniform α).bind (fun a => SDistr.pure (g a)) = d) :
    (SDistr.uniform (ι → α)).bind (fun P => SDistr.pure (∑ t, g (P t))) =
      sumIID d (Fintype.card ι) := by
  rw [← uniform_sum_law g d hg (Fintype.card ι),
    ← SDistr.uniform_bind_equiv_comp ((Fintype.equivFin ι).arrowCongr (Equiv.refl α))]
  congr 1
  funext P
  congr 1
  exact (Equiv.sum_comp (Fintype.equivFin ι).symm (fun t => g (P t))).symm

/-! ## Windows -/

/-- The window vectors of rank `k` at parameter `η`. -/
abbrev WinVec (k η : ℕ) : Type := Fin k → Fin 256 → Win η

/-- The dot product of two window vectors: the sum of the products of the window
values. -/
def wDot {k η η' : ℕ} (X : WinVec k η) (Y : WinVec k η') : ℤ :=
  ∑ j, ∑ l, windowVal (X j l) * windowVal (Y j l)

/-- The law of the product of the values of two independent uniform windows. -/
theorem uniform_windowVal_mul (η η' : ℕ) :
    (SDistr.uniform (Win η × Win η')).bind
        (fun w => SDistr.pure (windowVal w.1 * windowVal w.2)) = cbdProd η η' := by
  rw [← SDistr.uniform_nested_eq_prod]
  simp only [SDistr.bind_assoc, SDistr.pure_bind]
  rw [bind_of_pushforward (uniform_windowVal η)
    (fun x => (SDistr.uniform (Win η')).bind fun w' => SDistr.pure (x * windowVal w'))]
  unfold cbdProd
  congr 1
  funext x
  exact bind_of_pushforward (uniform_windowVal η') (fun y => SDistr.pure (x * y))

/-- The window dot product of two independent uniform window vectors has the law
`sumIID (cbdProd η η') (k * 256)`. -/
theorem uniform_wDot (k η η' : ℕ) :
    (SDistr.uniform (WinVec k η)).bind
        (fun X => (SDistr.uniform (WinVec k η')).bind fun Y => SDistr.pure (wDot X Y)) =
      sumIID (cbdProd η η') (k * 256) := by
  let pairE : (Fin k × Fin 256 → Win η × Win η') ≃ WinVec k η × WinVec k η' :=
    { toFun := fun F => (fun j l => (F (j, l)).1, fun j l => (F (j, l)).2)
      invFun := fun p q => (p.1 q.1 q.2, p.2 q.1 q.2)
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hcard : Fintype.card (Fin k × Fin 256) = k * 256 := by simp
  rw [← hcard, ← uniform_sum_law_fintype (fun w : Win η × Win η' => windowVal w.1 * windowVal w.2)
    _ (uniform_windowVal_mul η η'), ← SDistr.uniform_bind_equiv_comp pairE.symm,
    ← SDistr.uniform_nested_eq_prod]
  simp only [SDistr.bind_assoc, SDistr.pure_bind]
  congr 1
  funext X
  congr 1
  funext Y
  congr 1
  simp only [wDot, ← Finset.sum_product', Finset.univ_product_univ]
  rfl

/-- The value of coordinate `i` of a uniform window function has the law `cbd η`. -/
theorem uniform_eval_windowVal (η : ℕ) (i : Fin 256) :
    (SDistr.uniform (Fin 256 → Win η)).bind (fun Z => SDistr.pure (windowVal (Z i))) =
      cbd η := by
  rw [← SDistr.uniform_bind_equiv_comp (Equiv.funSplitAt i (Win η)).symm,
    ← SDistr.uniform_nested_eq_prod]
  simp only [SDistr.bind_assoc, SDistr.pure_bind, Equiv.funSplitAt_symm_apply, dite_true,
    SDistr.uniform_bind_const]
  exact uniform_windowVal η

/-! ## The reindexing involution -/

/-- Swap the two halves of a window when `b` holds. -/
def flipWin {η : ℕ} (b : Bool) (w : Win η) : Win η := if b then w.swap else w

/-- Swapping the halves of a window negates its value. -/
theorem windowVal_flipWin {η : ℕ} (b : Bool) (w : Win η) :
    windowVal (flipWin b w) = if b then -windowVal w else windowVal w := by
  cases b <;> simp [flipWin, windowVal]

/-- The window vector `Y` reindexed for coefficient `i` of a negacyclic product:
coordinate `l` is the window `i − l` of `Y`, with its halves swapped when `l > i`. -/
def reidx {k η : ℕ} (i : Fin 256) (Y : WinVec k η) : WinVec k η :=
  fun j l => flipWin (decide (i.val < l.val)) (Y j (i - l))

/-- The reindexing for coefficient `i` is an involution. -/
theorem reidx_involutive {k η : ℕ} (i : Fin 256) :
    Function.Involutive (reidx (k := k) (η := η) i) := by
  intro Y
  funext j l
  have h1 : i - (i - l) = l := sub_sub_cancel i l
  have h2 : decide (i.val < (i - l).val) = decide (i.val < l.val) := by
    simp only [decide_eq_decide, Fin.val_sub]
    omega
  simp only [reidx, h1, h2]
  cases decide (i.val < l.val) <;> simp [flipWin]

/-! ## The coefficient as a function of the windows -/

/-- The windows of a vector of PRF blocks. -/
def wvec {k : ℕ} (η : ℕ) (x : PrfVecBlock k η) : WinVec k η := fun j => windowMap η (x j)

/-- Coefficient `i` of the dot product of two sampled vectors is the window dot product
of the windows of the first and the reindexed windows of the second. -/
theorem vecDot_sampleVec_apply {k η η' : ℕ} (x : PrfVecBlock k η) (y : PrfVecBlock k η')
    (i : Fin 256) :
    vecDot (sampleVec k η x) (sampleVec k η' y) i =
      Zq3329.fromInt (wDot (wvec η x) (reidx i (wvec η' y))) := by
  simp only [vecDot, Finset.sum_apply, ringMul,
    CatCrypt.Crypto.Lattice.SignedNegacyclicConv.signedNegaConv, sampleVec, samplePoly_eq, wDot,
    reidx, wvec, windowVal_flipWin, Zq3329.fromInt, Int.cast_sum, Int.cast_mul]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
  by_cases h : l.val ≤ i.val <;> simp [h] <;> grind

/-- The window form of the coins. -/
abbrev WCoins (k η₁ η₂ : ℕ) : Type :=
  (WinVec k η₁ × WinVec k η₁) × ((Fin 256 → Win η₂) × (WinVec k η₁ × WinVec k η₂))

instance (k η₁ η₂ : ℕ) : Fintype (WCoins k η₁ η₂) :=
  @instFintypeProd _ _ inferInstance (@instFintypeProd _ _ inferInstance inferInstance)

/-- The window value of a window form of the coins at coefficient `i`. -/
def wNoise {k η₁ η₂ : ℕ} (i : Fin 256) (w : WCoins k η₁ η₂) : ℤ :=
  wDot w.1.1 w.1.2 + windowVal (w.2.1 i) - wDot w.2.2.1 w.2.2.2

/-- The windows of a PRF block, as an equivalence. -/
noncomputable def blockEquiv (η : ℕ) (hη : 0 < η) : PrfBlock η ≃ (Fin 256 → Win η) :=
  Equiv.ofBijective _ (windowMap_bijective η hη)

/-- The windows of a vector of PRF blocks, as an equivalence. -/
noncomputable def vecEquiv (k η : ℕ) (hη : 0 < η) : PrfVecBlock k η ≃ WinVec k η :=
  Equiv.piCongrRight fun _ => blockEquiv η hη

/-- The coins in window form at coefficient `i`: the windows of `e`, `r`, `e₂`, `s`,
`e₁`, with those of `r` and `e₁` reindexed for coefficient `i`. -/
noncomputable def coinsEquiv (k η₁ η₂ : ℕ) (hη₁ : 0 < η₁) (hη₂ : 0 < η₂) (i : Fin 256) :
    Coins k η₁ η₂ ≃ WCoins k η₁ η₂ where
  toFun c := ((vecEquiv k η₁ hη₁ c.1.2, reidx i (vecEquiv k η₁ hη₁ c.2.1)),
    (blockEquiv η₂ hη₂ c.2.2.2, (vecEquiv k η₁ hη₁ c.1.1, reidx i (vecEquiv k η₂ hη₂ c.2.2.1))))
  invFun w := (((vecEquiv k η₁ hη₁).symm w.2.2.1, (vecEquiv k η₁ hη₁).symm w.1.1),
    ((vecEquiv k η₁ hη₁).symm (reidx i w.1.2),
      (vecEquiv k η₂ hη₂).symm (reidx i w.2.2.2), (blockEquiv η₂ hη₂).symm w.2.1))
  left_inv c := by
    simp [reidx_involutive i _]
  right_inv w := by
    simp [reidx_involutive i _]

/-- Coefficient `i` of the decryption noise of the coins is the window value of their
window form, reduced modulo `3329`. -/
theorem coinNoise_apply_eq (k η₁ η₂ : ℕ) (hη₁ : 0 < η₁) (hη₂ : 0 < η₂) (i : Fin 256)
    (c : Coins k η₁ η₂) :
    coinNoise c i = Zq3329.fromInt (wNoise i (coinsEquiv k η₁ η₂ hη₁ hη₂ i c)) := by
  simp only [coinNoise, Pi.add_apply, Pi.sub_apply, vecDot_sampleVec_apply, samplePoly_eq,
    wNoise, Zq3329.fromInt, Int.cast_add, Int.cast_sub]
  rfl

/-! ## The law of one coefficient -/

/-- **The law of one noise coefficient.** Under uniform key-generation and encryption
coins, coefficient `i` of the decryption noise `e · r + e₂ − s · e₁` has the law
`noiseCoeffLaw k η₁ η₂` reduced modulo `3329`. -/
theorem coinNoise_law (k η₁ η₂ : ℕ) (hη₁ : 0 < η₁) (hη₂ : 0 < η₂) (i : Fin 256) :
    (SDistr.uniform (Coins k η₁ η₂)).bind (fun c => SDistr.pure (coinNoise c i)) =
      (noiseCoeffLaw k η₁ η₂).bind fun z => SDistr.pure (Zq3329.fromInt z) := by
  simp only [coinNoise_apply_eq k η₁ η₂ hη₁ hη₂ i]
  rw [SDistr.uniform_bind_equiv_comp (coinsEquiv k η₁ η₂ hη₁ hη₂ i)
      (fun w => SDistr.pure (Zq3329.fromInt (wNoise i w))),
    ← SDistr.uniform_nested_eq_prod, ← SDistr.uniform_nested_eq_prod (WinVec k η₁),
    ← SDistr.uniform_nested_eq_prod (Fin 256 → Win η₂),
    ← SDistr.uniform_nested_eq_prod (WinVec k η₁) (WinVec k η₂)]
  simp only [SDistr.bind_assoc, SDistr.pure_bind, wNoise]
  calc _ = (sumIID (cbdProd η₁ η₁) (k * 256)).bind fun a =>
        (SDistr.uniform (Fin 256 → Win η₂)).bind fun Z =>
          (SDistr.uniform (WinVec k η₁)).bind fun U =>
            (SDistr.uniform (WinVec k η₂)).bind fun V =>
              SDistr.pure (Zq3329.fromInt (a + windowVal (Z i) - wDot U V)) :=
        bind_of_pushforward₂ (uniform_wDot k η₁ η₁) _
    _ = (sumIID (cbdProd η₁ η₁) (k * 256)).bind fun a => (cbd η₂).bind fun z =>
          (SDistr.uniform (WinVec k η₁)).bind fun U =>
            (SDistr.uniform (WinVec k η₂)).bind fun V =>
              SDistr.pure (Zq3329.fromInt (a + z - wDot U V)) := by
        congr 1
        funext a
        exact bind_of_pushforward (uniform_eval_windowVal η₂ i) fun z =>
          (SDistr.uniform (WinVec k η₁)).bind fun U =>
            (SDistr.uniform (WinVec k η₂)).bind fun V =>
              SDistr.pure (Zq3329.fromInt (a + z - wDot U V))
    _ = (sumIID (cbdProd η₁ η₁) (k * 256)).bind fun a => (cbd η₂).bind fun z =>
          (sumIID (cbdProd η₁ η₂) (k * 256)).bind fun b =>
            SDistr.pure (Zq3329.fromInt (a + z - b)) := by
        congr 1
        funext a
        congr 1
        funext z
        exact bind_of_pushforward₂ (uniform_wDot k η₁ η₂) fun b =>
          SDistr.pure (Zq3329.fromInt (a + z - b))
    _ = _ := by simp only [noiseCoeffLaw, SDistr.bind_assoc, SDistr.pure_bind]

end CatCrypt.Crypto.MLKEM.MLKEMRankInstance
