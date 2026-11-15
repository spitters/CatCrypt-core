/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.KVAC.MacNHelpAGMLemmas

/-!
# `MAC_n` in the algebraic group model: the exact simulation of `reductionAlg`

The second part of the security proof of `MAC_n` with the helper oracle for algebraic
adversaries (`CatCrypt.Crypto.KVAC.MacNHelpAGM`).

## Evaluation of list polynomials

With the ring structure `expCommRing` on the exponents, `peval` is a ring homomorphism on list
polynomials (`peval_padd`, `peval_pmul`, …), and on the `D`-DL challenge
`ch = (g, g^χ, …, g^{χ^D})` the element `elemOf ch c` of a polynomial of degree at most `D` is
`g^{c(χ)}` (`elemOf_kDLChallenge`). The polynomial `macPoly` evaluates to the helper equation
`helpV` of `macN` at the parameters `g^γ` and the key `kp(χ)` (`evP_macPoly`).

## The exact simulation

`simOL` is the oracle `simO` of `reductionAlg` that also logs, for each MAC query, the
polynomials of the attributes and of `U`, `V` and the tag value `t`.
`run_helpOracle_eq_simOL`: for a generator `g ≠ 1`, an adversary with at most `m` MAC queries
and a challenge of degree `D ≥ e + m + 2` over a start state of degree at most `e + 1`, the run
of `toAdv` against the helper oracle of `macN` at the parameters `g^γ` and the key `kp(χ)` is
the run of the algebraic adversary against `simOL`, with the basis, the forgery and the MAC
log evaluated at `χ`. `simO_run_eq` is its projection to the output: the run against
`simO` composed with evaluation is the run of `toAdv` against `helpOracle`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.KVAC.MacNHelpAGM

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Assumptions.KDL
open CatCryptCore.Examples.CyclicGroupDDH CatCrypt.Examples.OT AlgMac AlgMac.MacN

variable {G : Type} [CGR : CyclicGroupRing G]

attribute [local instance] expCommRing

/-! ## The exponent ring -/

/-- Unfolding lemma of `expCommRing`: exponent addition is its addition. -/
theorem expAdd_eq (a b : CGR.Exp) : CGR.expAdd a b = a + b := rfl

/-- Unfolding lemma of `expCommRing`: exponent multiplication is its multiplication. -/
theorem expMul_eq (a b : CGR.Exp) : CGR.expMul a b = a * b := rfl

/-- Unfolding lemma of `expCommRing`: exponent negation is its negation. -/
theorem expNeg_eq (a : CGR.Exp) : CGR.expNeg a = -a := rfl

/-- Unfolding lemma of `expCommRing`: the zero exponent is its zero. -/
theorem expZero_eq : (CGR.expZero : CGR.Exp) = 0 := rfl

/-- Unfolding lemma of `expCommRing`: `expOne` is its unit. -/
theorem expOne_eq : (expOne : CGR.Exp) = 1 := rfl

/-- `g^a` for the generator `g`. -/
local notation "gp" => CyclicGroup.elemPow (CyclicGroup.gen (G := G))

/-- `x^(a + b) = x^a x^b`. -/
theorem elemPow_add' (x : G) (a b : CGR.Exp) :
    CyclicGroup.elemPow x (a + b) = CGR.mul (CyclicGroup.elemPow x a) (CyclicGroup.elemPow x b) :=
  CyclicGroupRing.elemPow_add x a b

/-- `(g^a)^b = g^(a b)`. -/
theorem elemPow_elemPow (x : G) (a b : CGR.Exp) :
    CyclicGroup.elemPow (CyclicGroup.elemPow x a) b = CyclicGroup.elemPow x (a * b) :=
  (CyclicGroupRing.elemPow_mul x a b).symm

/-- `x^(-a) = (x^a)⁻¹`. -/
theorem elemPow_neg' (x : G) (a : CGR.Exp) :
    CyclicGroup.elemPow x (-a) = CGR.inv (CyclicGroup.elemPow x a) :=
  CyclicGroupRing.elemPow_neg x a

/-- `x^0 = 1`. -/
theorem elemPow_zero' (x : G) : CyclicGroup.elemPow x 0 = CGR.one :=
  CyclicGroupRing.elemPow_zero x

/-- `x^1 = x`. -/
theorem elemPow_one' (x : G) : CyclicGroup.elemPow x 1 = x := by
  obtain ⟨e, rfl⟩ := CGR.pow_bij.2 x
  rw [CyclicGroup.elemPow_pow]
  exact congrArg CGR.pow (expMul_expOne e)

/-- The product of a list of powers of `x` is the power of the sum. -/
theorem gprod_map_elemPow (x : G) (l : List CGR.Exp) :
    gprod (l.map (CyclicGroup.elemPow x)) = CyclicGroup.elemPow x l.sum := by
  induction l with
  | nil => simp [gprod, elemPow_zero']
  | cons a l ih =>
    simp only [List.map_cons, List.sum_cons, elemPow_add', ← ih]
    rfl

/-! ## Evaluation of list polynomials -/

/-- Unfolding lemma of `peval` at the empty list. -/
@[simp] theorem peval_nil (x : CGR.Exp) : peval ([] : Poly G) x = 0 := rfl

/-- Unfolding lemma of `peval` at a cons (Horner's rule). -/
@[simp] theorem peval_cons (a : CGR.Exp) (p : Poly G) (x : CGR.Exp) :
    peval (a :: p) x = a + x * peval p x := rfl

/-- Evaluation of a sum. -/
theorem peval_padd (p q : Poly G) (x : CGR.Exp) : peval (padd p q) x = peval p x + peval q x := by
  induction p generalizing q with
  | nil => simp [padd]
  | cons a p ih =>
    cases q with
    | nil => simp [padd]
    | cons b q =>
      simp only [padd, peval_cons, expAdd_eq, ih]
      ring

/-- Evaluation of a scalar multiple. -/
theorem peval_pscale (c : CGR.Exp) (p : Poly G) (x : CGR.Exp) :
    peval (pscale c p) x = c * peval p x := by
  induction p with
  | nil => simp [pscale]
  | cons a p ih =>
    simp only [pscale, List.map_cons, peval_cons, expMul_eq] at ih ⊢
    rw [ih]
    ring

/-- Evaluation of a negation. -/
theorem peval_pneg (p : Poly G) (x : CGR.Exp) : peval (pneg p) x = -peval p x := by
  induction p with
  | nil => simp [pneg]
  | cons a p ih =>
    simp only [pneg, List.map_cons, peval_cons, expNeg_eq] at ih ⊢
    rw [ih]
    ring

/-- Evaluation of a product. -/
theorem peval_pmul (p q : Poly G) (x : CGR.Exp) : peval (pmul p q) x = peval p x * peval q x := by
  induction p with
  | nil => simp [pmul]
  | cons a p ih =>
    rw [pmul, peval_padd, peval_pscale, peval_cons, peval_cons, ih, expZero_eq]
    ring

/-- Evaluation of a sum of a list of polynomials. -/
theorem peval_psum (l : List (Poly G)) (x : CGR.Exp) :
    peval (psum l) x = (l.map (peval · x)).sum := by
  induction l with
  | nil => simp [psum]
  | cons p l ih =>
    simp only [psum, List.foldr_cons, List.map_cons, List.sum_cons] at ih ⊢
    rw [peval_padd, ih]

/-- The dot product `Σ_i a_i c_i` of two lists, truncated to the shorter. -/
noncomputable def expDot : List CGR.Exp → List CGR.Exp → CGR.Exp
  | a :: l, c :: r => a * c + expDot l r
  | _, _ => 0

/-- Evaluation of the polynomial of a representation. -/
theorem peval_polyRep (P : List (Poly G)) (c : Rep G) (x : CGR.Exp) :
    peval (polyRep P c) x = expDot (P.map (peval · x)) c := by
  induction P generalizing c with
  | nil => cases c <;> simp [polyRep, psum, peval, expDot, expZero_eq]
  | cons p P ih =>
    cases c with
    | nil => simp [polyRep, psum, peval, expDot, expZero_eq]
    | cons a c =>
      have := ih c
      simp only [polyRep, psum, List.zipWith_cons_cons, List.foldr_cons] at this ⊢
      rw [peval_padd, peval_pscale, this, List.map_cons, expDot]
      ring

/-- The product `Π_i (x^{a_i})^{c_i}` is `x^{Σ_i a_i c_i}`. -/
theorem gprod_zipWith_elemPow (x : G) :
    ∀ (l c : List CGR.Exp),
      gprod (List.zipWith CyclicGroup.elemPow (l.map (CyclicGroup.elemPow x)) c) =
        CyclicGroup.elemPow x (expDot l c)
  | [], _ => by simp [gprod, expDot, elemPow_zero']
  | _ :: _, [] => by simp [gprod, expDot, elemPow_zero']
  | a :: l, c :: r => by
    have ih := gprod_zipWith_elemPow x l r
    simp only [List.map_cons, List.zipWith_cons_cons, expDot, elemPow_add', ← ih,
      elemPow_elemPow]
    rfl

/-- The value `g^{c(χ)}` of a list polynomial `c` at `χ`. -/
noncomputable def evP (χ : CGR.Exp) (c : Poly G) : G := gp (peval c χ)

/-- A representation over evaluated polynomials evaluates to the polynomial of the
representation. -/
theorem evalRep_map_evP (χ : CGR.Exp) (P : List (Poly G)) (c : Rep G) :
    evalRep G (P.map (evP χ)) c = evP χ (polyRep P c) := by
  rw [evalRep, evP, peval_polyRep, ← gprod_zipWith_elemPow, List.map_map]
  rfl

/-- The challenge powers `χ^s, …, χ^{s + L - 1}` against a polynomial of length at most `L`. -/
theorem expDot_range' (χ : CGR.Exp) :
    ∀ (p : Poly G) (s L : ℕ), p.length ≤ L →
      expDot ((List.range' s L).map (expPow χ)) p = expPow χ s * peval p χ
  | [], s, L, _ => by cases L <;> simp [expDot, peval, expZero_eq, List.range'_succ]
  | a :: p, s, L, h => by
    obtain ⟨L, rfl⟩ : ∃ L', L = L' + 1 := ⟨L - 1, by simp at h; omega⟩
    have ih := expDot_range' χ p (s + 1) L (by simp at h; omega)
    rw [List.range'_succ, List.map_cons, expDot, ih]
    simp only [peval, List.foldr_cons, expPow, expAdd_eq, expMul_eq]
    ring

/-- **The challenge.** On `(g, g^χ, …, g^{χ^D})`, a polynomial of degree at most `D` gives
`g^{c(χ)}`. -/
theorem elemOf_kDLChallenge (D : ℕ) (χ : CGR.Exp) (c : Poly G) (hc : c.length ≤ D + 1) :
    elemOf (kDLChallenge G D χ) c = evP χ c := by
  have hf : (fun i => gp (expPow χ i)) = gp ∘ expPow χ := rfl
  rw [elemOf, kDLChallenge, hf, ← List.map_map, gprod_zipWith_elemPow, List.range_eq_range',
    expDot_range' χ c 0 (D + 1) hc, evP, expPow, expOne_eq, one_mul]

/-- For a generator `g ≠ 1`, `g^a = 1` only at `a = 0`. -/
theorem gp_eq_one_iff (hgen : CGR.gen ≠ CGR.one) (a : CGR.Exp) : gp a = CGR.one ↔ a = 0 := by
  rw [← elemPow_zero' CGR.gen]
  exact (elemPow_gen_bijective hgen).1.eq_iff

/-- **Vanishing test.** The test of `simO` on `Z - R` answers whether `g^{Z(χ)} = g^{R(χ)}`. -/
theorem vanishes_padd_pneg (hgen : CGR.gen ≠ CGR.one) [DecidableEq G] (D : ℕ) (χ : CGR.Exp)
    (pZ pR : Poly G) (hZ : pZ.length ≤ D + 1) (hR : pR.length ≤ D + 1) :
    vanishes (kDLChallenge G D χ) (padd pZ (pneg pR)) = decide (evP χ pZ = evP χ pR) := by
  have hl : (padd pZ (pneg pR)).length ≤ D + 1 := by
    rw [length_padd, length_pneg]
    omega
  rw [vanishes, elemOf_kDLChallenge D χ _ hl, decide_eq_decide, evP, gp_eq_one_iff hgen,
    peval_padd, peval_pneg, evP, evP, (elemPow_gen_bijective hgen).1.eq_iff, add_neg_eq_zero]

/-! ## The key and the MAC polynomial at `χ` -/

variable {n : ℕ}

/-- The key `kp(χ)`: the key polynomials evaluated at `χ`. -/
noncomputable def keyAt (kp : KeyPolys G n) (χ : CGR.Exp) : MacN.Key G n :=
  (peval kp.w χ, peval kp.w' χ, peval kp.x0 χ, peval kp.x1 χ, fun i => peval (kp.y i) χ)

/-- The attribute product `Π_i (g^{a_i})^{y_i}` is `g^{Σ_i a_i y_i}`. -/
theorem attrProd_gp (a y : Fin n → CGR.Exp) :
    attrProd (fun i => gp (a i)) y = gp (∑ i, a i * y i) := by
  rw [attrProd, ← List.sum_ofFn, ← gprod_map_elemPow, List.map_ofFn]
  congr 1
  exact List.ofFn_inj.mpr (funext fun i => elemPow_elemPow _ _ _)

/-- **The MAC polynomial.** At the parameters `g^γ` and the key `kp(χ)`, the helper equation of
`macN` at elements `g^{A0(χ)}, g^{A1(χ)}, g^{A_i(χ)}` is `g^{macPoly(χ)}`. -/
theorem evP_macPoly (χ : CGR.Exp) (γ : ParExp G n) (kp : KeyPolys G n) (pA0 pA1 : Poly G)
    (pA : Fin n → Poly G) :
    evP χ (macPoly γ.1 kp pA0 pA1 pA) =
      helpV (parOf γ) (keyAt kp χ) (evP χ pA0) (evP χ pA1) fun i => evP χ (pA i) := by
  simp only [evP, helpV, bigW, parOf, keyAt, gw, w, x0, x1, y]
  rw [attrProd_gp]
  simp only [elemPow_elemPow, ← elemPow_add', macPoly, peval_padd, peval_pscale, peval_pmul,
    peval_psum, List.map_ofFn]
  congr 1
  rw [List.sum_ofFn]
  simp only [Function.comp_apply, peval_pmul]
  grind

/-- **The starting basis.** The polynomials of `basisPolys0` evaluate to the generator, the
parameters `g^γ` and the issuer parameters of the key `kp(χ)`. -/
theorem map_evP_basisPolys0 (χ : CGR.Exp) (γ : ParExp G n) (kp : KeyPolys G n) :
    (basisPolys0 expOne γ kp).map (evP χ) = basis0 (parOf γ) (iparams (parOf γ) (keyAt kp χ)) := by
  have h1 : ∀ c : CGR.Exp, evP χ [c] = gp c := fun c => by simp [evP]
  simp only [basisPolys0, basis0, List.map_append, List.map_cons, List.map_nil, List.map_ofFn,
    Function.comp_def, h1, parOf, iparams, bigW, gw, gw', gx0, gx1, gV, gy, keyAt, w, w', x0, x1,
    y, attrProd_gp, elemPow_elemPow, ← elemPow_neg', ← elemPow_add', expOne_eq, elemPow_one']
  simp only [evP, peval_padd, peval_pscale, peval_pneg, peval_psum, List.map_ofFn,
    Function.comp_def, peval_cons, peval_nil, List.sum_ofFn, gm, mul_zero, add_zero]

/-! ## The oracle with the MAC log -/

variable [DecidableEq G]

variable (G) in
/-- A symbolic entry of the MAC log: the attribute polynomials, `t`, and the polynomials of `U`
and `V`. -/
abbrev SymEntry (n : ℕ) := (Fin n → Poly G) × CGR.Exp × Poly G × Poly G

/-- The entry of the MAC log of `macN` denoted by a symbolic entry at `χ`. -/
noncomputable def evEntry (χ : CGR.Exp) (e : SymEntry G n) : (Fin n → G) × CGR.Exp × G × G :=
  (fun i => evP χ (e.1 i), e.2.1, evP χ e.2.2.1, evP χ e.2.2.2)

/-- **The oracle `simO` with the MAC log.** As `simO`, and a MAC query also logs the attribute
polynomials, `t` and the polynomials of `U` and `V`. -/
noncomputable def simOL (ch : List G) (γw : CGR.Exp) (kp : KeyPolys G n)
    (s : List (Poly G) × List (SymEntry G n)) :
    SymQ G n → PMF (Ans G × (List (Poly G) × List (SymEntry G n)))
  | .inl M =>
      (PMF.uniformFintype (CGR.Exp × CGR.Exp × CGR.Exp)).map fun r =>
        let pU : Poly G := [r.2.1, r.2.2]
        let pM : Fin n → Poly G := fun i => polyRep s.1 (M i)
        let pV := macPoly γw kp pU (pscale r.1 pU) pM
        (.inl (r.1, elemOf ch pU, elemOf ch pV), (s.1 ++ [pU, pV], (pM, r.1, pU, pV) :: s.2))
  | .inr q => (simO ch γw kp s.1 (.inr q)).map fun x => (x.1, (x.2, s.2))

/-- `simOL` without its log is `simO`. -/
theorem simOL_map_fst (ch : List G) (γw : CGR.Exp) (kp : KeyPolys G n)
    (s : List (Poly G) × List (SymEntry G n)) (d : SymQ G n) :
    (simOL ch γw kp s d).map (Prod.map id Prod.fst) = simO ch γw kp s.1 d := by
  rcases d with M | q
  · simp only [simOL, simO, PMF.map_comp]
    rfl
  · simp only [simOL, PMF.map_comp]
    exact PMF.map_id _

omit [DecidableEq G] in
/-- **The MAC coins.** For `g ≠ 1`, `(t, g^{a + b χ})` with uniform `t, a, b` is uniform. -/
theorem uniform_macCoins (hgen : CGR.gen ≠ CGR.one) (χ : CGR.Exp) :
    (PMF.uniformFintype (CGR.Exp × CGR.Exp × CGR.Exp)).map
      (fun r => (r.1, evP χ [r.2.1, r.2.2])) = PMF.uniformFintype (CGR.Exp × G) := by
  let e : CGR.Exp ≃ G := Equiv.ofBijective _ (elemPow_gen_bijective hgen)
  have hev : ∀ a b : CGR.Exp, evP χ [a, b] = e (a + χ * b) := fun a b => by
    simp only [evP, peval_cons, peval_nil, e, Equiv.ofBijective_apply]
    congr 1
    ring
  let E : CGR.Exp × CGR.Exp × CGR.Exp ≃ (CGR.Exp × G) × CGR.Exp :=
    { toFun := fun r => ((r.1, evP χ [r.2.1, r.2.2]), r.2.2)
      invFun := fun w => (w.1.1, e.symm w.1.2 - χ * w.2, w.2)
      left_inv := fun r => by
        obtain ⟨t, a, b⟩ := r
        simp only [hev, Equiv.symm_apply_apply, Prod.mk.injEq, true_and, and_true]
        ring
      right_inv := fun w => by
        obtain ⟨⟨t, U⟩, b⟩ := w
        simp only [hev, sub_add_cancel, Equiv.apply_symm_apply] }
  rw [show (fun r : CGR.Exp × CGR.Exp × CGR.Exp => (r.1, evP χ [r.2.1, r.2.2])) =
    Prod.fst ∘ E from rfl, ← PMF.map_comp, PMF.uniformFintype_map_equiv, PMF.map_uniform_fst]

omit [DecidableEq G] in
/-- The value of a scalar multiple is a power of the value. -/
theorem evP_pscale (χ c : CGR.Exp) (p : Poly G) :
    evP χ (pscale c p) = CyclicGroup.elemPow (evP χ p) c := by
  rw [evP, evP, elemPow_elemPow, peval_pscale, mul_comm]

omit [DecidableEq G] in
/-- An attribute vector over evaluated polynomials evaluates to the attribute polynomials. -/
theorem evalMsg_map_evP (χ : CGR.Exp) (P : List (Poly G)) (M : SymMsg G n) :
    evalMsg (P.map (evP χ)) M = fun i => evP χ (polyRep P (M i)) :=
  funext fun i => evalRep_map_evP χ P (M i)

omit [DecidableEq G] in
/-- At `(U, U^t, M)` the MAC polynomial evaluates to the tag component `V` of `macN`. -/
theorem evP_macPoly_macV (χ t : CGR.Exp) (γ : ParExp G n) (kp : KeyPolys G n) (pU : Poly G)
    (pM : Fin n → Poly G) :
    evP χ (macPoly γ.1 kp pU (pscale t pU) pM) =
      macV (parOf γ) (keyAt kp χ) (fun i => evP χ (pM i)) t (evP χ pU) := by
  rw [evP_macPoly, evP_pscale, helpV_eq_macV]

variable [DecidableEq CGR.Exp]

/-- A MAC query to the helper oracle of `macN`: uniform coins `(t, U)`, the tag
`(t, U, macV M t U)`, logged. -/
theorem helpOracle_inl (par : MacN.Par G n) (key : MacN.Key G n) (L : (macN G n).Log)
    (Mv : Fin n → G) :
    (macN G n).helpOracle par key L (.inl Mv) =
      (PMF.uniformFintype (CGR.Exp × G)).map fun r =>
        ((.inl (r.1, r.2, macV par key Mv r.1 r.2) : (macN G n).HelpAns),
          ((Mv, (r.1, r.2, macV par key Mv r.1 r.2)) :: L : (macN G n).Log)) := by
  simp only [AlgMac.helpOracle, AlgMac.macStep, PMF.map_comp]
  rfl

/-- **Exact simulation with the MAC log.** For a generator `g ≠ 1`, an adversary with at most
`m` MAC queries, a start state of polynomials of degree at most `e + 1` and a challenge of
degree `D ≥ e + m + 2`: the run of `toAdv` against the helper oracle of `macN` at the
parameters `g^γ` and the key `kp(χ)` is the run of the algebraic adversary against `simOL`,
with the forgery evaluated over the final basis and the MAC log evaluated at `χ`. -/
theorem run_helpOracle_eq_simOL (hgen : CGR.gen ≠ CGR.one) (D : ℕ) (χ : CGR.Exp)
    (γ : ParExp G n) (kp : KeyPolys G n) (hkp : kp.Lin) :
    ∀ (A : OracleAdv (SymQ G n) (Ans G) (SymOut G n)) (m e : ℕ) (P : List (Poly G))
      (Ls : List (SymEntry G n)), A.IsQueryBoundBy macCost m →
      (∀ p ∈ P, p.length ≤ e + 2) → e + m + 2 ≤ D →
      OracleAdv.run ((macN G n).helpOracle (parOf γ) (keyAt kp χ))
          (toAdv (P.map (evP χ)) A) (Ls.map (evEntry χ)) =
        (OracleAdv.run (simOL (kDLChallenge G D χ) γ.1 kp) A (P, Ls)).map fun y =>
          ((evalMsg (y.2.1.map (evP χ)) y.1.1, evalTag (y.2.1.map (evP χ)) y.1.2),
            y.2.2.map (evEntry χ)) := by
  intro A
  induction A with
  | ret o =>
    intro m e P Ls _ _ _
    simp only [toAdv, OracleAdv.run_ret, PMF.pure_map]
    rfl
  | rand p k ih =>
    intro m e P Ls hA hP hD
    simp only [toAdv, OracleAdv.run_rand, PMF.map_bind]
    exact congrArg _ (funext fun b => ih b m e P Ls (hA b) hP hD)
  | query d k ih =>
    intro m e P Ls hA hP hD
    obtain ⟨hc, hk⟩ := hA
    have hPl : ∀ c : Rep G, (polyRep P c).length ≤ e + 2 := fun c =>
      length_polyRep_le P c _ hP
    rcases d with M | q | q
    · have hm : 1 ≤ m := hc
      rw [toAdv, OracleAdv.run_query, evalQ, helpOracle_inl, ← uniform_macCoins hgen χ,
        PMF.map_comp, PMF.bind_map, OracleAdv.run_query, simOL, PMF.bind_map, PMF.map_bind]
      refine congrArg _ (funext fun r => ?_)
      obtain ⟨t, a, b⟩ := r
      simp only [Function.comp_apply]
      have hU := elemOf_kDLChallenge D χ [a, b]
        (by simp only [List.length_cons, List.length_nil]; omega)
      have hVl := length_macPoly_le γ.1 kp hkp [a, b] (pscale t [a, b])
        (fun i => polyRep P (M i)) (e + 1) (by simp) (by rw [length_pscale]; simp)
        fun i => hPl (M i)
      have hV := elemOf_kDLChallenge D χ _ (by omega : (macPoly γ.1 kp [a, b] (pscale t [a, b])
        (fun i => polyRep P (M i))).length ≤ D + 1)
      have hVm := evP_macPoly_macV χ t γ kp [a, b] (fun i => polyRep P (M i))
      rw [← evalMsg_map_evP] at hVm
      rw [← hVm, hU, hV]
      have hP' : ∀ p ∈ P ++ [[a, b], macPoly γ.1 kp [a, b] (pscale t [a, b])
          (fun i => polyRep P (M i))], p.length ≤ (e + 1) + 2 := by
        intro p hp
        simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with hp | rfl | rfl
        · have := hP p hp
          omega
        · simp
        · omega
      have h := ih (.inl (t, evP χ [a, b], evP χ (macPoly γ.1 kp [a, b] (pscale t [a, b])
        (fun i => polyRep P (M i))))) (m - 1) (e + 1) _ ((fun i => polyRep P (M i), t, [a, b],
        macPoly γ.1 kp [a, b] (pscale t [a, b]) (fun i => polyRep P (M i))) :: Ls) (hk _) hP'
        (by omega)
      simp only [List.map_append, List.map_cons, List.map_nil] at h
      rw [evalMsg_map_evP]
      exact h
    · have hk' : ∀ r, (k r).IsQueryBoundBy macCost m := fun r => by
        simpa only [macCost, Nat.sub_zero] using hk r
      have hl := length_macPoly_le γ.1 kp hkp (polyRep P q.2.2.1)
        (pscale q.2.1 (polyRep P q.2.2.1)) (fun i => polyRep P (q.1 i)) (e + 1)
        (by have := hPl q.2.2.1; omega) (by rw [length_pscale]; have := hPl q.2.2.1; omega)
        fun i => by have := hPl (q.1 i); omega
      have hv := vanishes_padd_pneg hgen D χ (polyRep P q.2.2.2) _
        (by have := hPl q.2.2.2; omega) (by omega : (macPoly γ.1 kp (polyRep P q.2.2.1)
          (pscale q.2.1 (polyRep P q.2.2.1)) (fun i => polyRep P (q.1 i))).length ≤ D + 1)
      rw [evP_macPoly_macV] at hv
      rw [toAdv, OracleAdv.run_query, evalQ, OracleAdv.run_query, simOL, simO]
      simp only [AlgMac.helpOracle, PMF.pure_bind, PMF.pure_map]
      rw [hv]
      have hver : (macN G n).verify (parOf γ) (keyAt kp χ) (evalMsg (P.map (evP χ)) q.1)
          (evalTag (P.map (evP χ)) q.2) = decide (evP χ (polyRep P q.2.2.2) =
            macV (parOf γ) (keyAt kp χ) (fun i => evP χ (polyRep P (q.1 i))) q.2.1
              (evP χ (polyRep P q.2.2.1))) := by
        simp only [macN, evalTag, evalMsg_map_evP, evalRep_map_evP]
      rw [hver]
      exact ih _ m e P Ls (hk' _) hP hD
    · have hk' : ∀ r, (k r).IsQueryBoundBy macCost m := fun r => by
        simpa only [macCost, Nat.sub_zero] using hk r
      have hl := length_macPoly_le γ.1 kp hkp (polyRep P q.1) (polyRep P q.2.1)
        (fun i => polyRep P (q.2.2.1 i)) (e + 1) (by have := hPl q.1; omega)
        (by have := hPl q.2.1; omega) fun i => by have := hPl (q.2.2.1 i); omega
      have hv := vanishes_padd_pneg hgen D χ (polyRep P q.2.2.2) _
        (by have := hPl q.2.2.2; omega) (by omega : (macPoly γ.1 kp (polyRep P q.1)
          (polyRep P q.2.1) (fun i => polyRep P (q.2.2.1 i))).length ≤ D + 1)
      rw [evP_macPoly] at hv
      rw [toAdv, OracleAdv.run_query, evalQ, OracleAdv.run_query, simOL, simO]
      simp only [AlgMac.helpOracle, PMF.pure_bind, PMF.pure_map]
      rw [hv]
      have hhelp : (macN G n).help (parOf γ) (keyAt kp χ) (evalRep G (P.map (evP χ)) q.1,
          evalRep G (P.map (evP χ)) q.2.1, evalMsg (P.map (evP χ)) q.2.2.1,
          evalRep G (P.map (evP χ)) q.2.2.2) = decide (evP χ (polyRep P q.2.2.2) =
            helpV (parOf γ) (keyAt kp χ) (evP χ (polyRep P q.1)) (evP χ (polyRep P q.2.1))
              (fun i => evP χ (polyRep P (q.2.2.1 i)))) := by
        simp only [macN, evalMsg_map_evP, evalRep_map_evP]
      rw [hhelp]
      exact ih _ m e P Ls (hk' _) hP hD

/-- **Exact simulation (`simO_run_eq`).** For a generator `g ≠ 1`, an adversary with at most
`m` MAC queries, a start state of degree at most `e + 1` and a challenge of degree
`D ≥ e + m + 2`: the run of the algebraic adversary against `simO`, with the forgery evaluated
over the evaluated final state, is the output of the run of `toAdv` against the helper oracle
of `macN` at the parameters `g^γ` and the key `kp(χ)`. -/
theorem simO_run_eq (hgen : CGR.gen ≠ CGR.one) (D : ℕ) (χ : CGR.Exp) (γ : ParExp G n)
    (kp : KeyPolys G n) (hkp : kp.Lin) (A : OracleAdv (SymQ G n) (Ans G) (SymOut G n))
    (m e : ℕ) (P : List (Poly G)) (hA : A.IsQueryBoundBy macCost m)
    (hP : ∀ p ∈ P, p.length ≤ e + 2) (hD : e + m + 2 ≤ D) :
    (OracleAdv.run ((macN G n).helpOracle (parOf γ) (keyAt kp χ))
        (toAdv (P.map (evP χ)) A) []).map Prod.fst =
      (OracleAdv.run (simO (kDLChallenge G D χ) γ.1 kp) A P).map fun y =>
        (evalMsg (y.2.map (evP χ)) y.1.1, evalTag (y.2.map (evP χ)) y.1.2) := by
  have h := run_helpOracle_eq_simOL hgen D χ γ kp hkp A m e P [] hA hP hD
  refine (congrArg (PMF.map Prod.fst) h).trans ?_
  have hs := OracleAdv.run_map_state (simOL (kDLChallenge G D χ) γ.1 kp) _ Prod.fst
    (fun s d => simOL_map_fst _ _ _ s d) A (P, [])
  rw [← hs]
  refine (PMF.map_comp _ _ _).trans ?_
  rw [PMF.map_comp]
  rfl

end CatCrypt.Crypto.KVAC.MacNHelpAGM
