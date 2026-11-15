/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.KVAC.MacNHelpAGM
public import Mathlib.Algebra.Polynomial.Roots

/-!
# Discrete logarithm and `k`-DL over `CyclicGroupRing`

The discrete-logarithm assumptions of the algebraic-group-model proof of `MAC_n`
(`CatCrypt.Crypto.KVAC.MacNHelpAGM`), over a prime-order cyclic group `G` with exponent ring
`CGR.Exp` (`CyclicGroupRing G`), and the root count of list polynomials over the exponent ring.

## Games

* `KDL_Game D B`: sample `χ`, give `B` the list `(g, g^χ, g^{χ^2}, …, g^{χ^D})`
  (`kDLChallenge D χ`), and win iff `B` outputs `χ` (FKL18, Definition 2.4, the `q`-DLog
  problem). `KDL_Advantage D B` is its winning probability.
* `DL_Game B`: the `1`-DL game, with the adversary given the entry `g^χ`; `DL_Advantage B` is
  its winning probability.

The adversaries are `PMF`-valued, as the reductions `reductionZ` and `reductionAlg` of
`MacNHelpAGM`, and each game is the `liftPMF` of a distribution on `Bool`, as
`AlgMac.forgeGame`.

## Exponent ring

* `expOne`: the unit of `CGR.Exp`, obtained from the bijectivity of multiplication by a nonzero
  exponent (`CyclicGroupRing.expMul_bij`); `expMul_expOne` is its law.
* `expCommRing`: the commutative ring of exponents, a `CommRing` structure on `CGR.Exp` built
  from the class laws (not an instance; it is installed with `letI` where needed);
  `expIsDomain` makes it a domain when it is nontrivial.

## Polynomials and roots

A polynomial in `MacNHelpAGM` is a list of coefficients, constant term first (`Poly G`).

* `peval p x`: evaluation by Horner's rule.
* `toPolynomial p`: the Mathlib polynomial of `p` over `expCommRing`; `eval_toPolynomial`
  relates the evaluations and `coeff_toPolynomial` the coefficients.
* `PolyNonzero p`: some coefficient is nonzero.
* `card_roots_le`: a nonzero list polynomial with at most `D + 1` coefficients has at most `D`
  roots (from `Polynomial.card_roots'`).
* `RootFinder`: a root-finding algorithm, listing every root of a nonzero polynomial.

The gap-DL game is not stated: the bound of the `MAC_n` proof has no gap-DL term, since its
reduction answers helper queries from the polynomials of the elements.

## References

* G. Fuchsbauer, E. Kiltz, J. Loss, *The Algebraic Group Model and its Applications*,
  CRYPTO 2018, Definition 2.4. <https://eprint.iacr.org/2017/620>
* M. Orrù, *Revisiting Keyed-Verification Anonymous Credentials*, 2024, Theorem 5.1.
  <https://eprint.iacr.org/2024/1552>
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Assumptions.KDL

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCryptCore.Examples.CyclicGroupDDH CatCrypt.Examples.OT
open CatCrypt.Crypto.KVAC.MacNHelpAGM (Poly)
open scoped ENNReal

variable {G : Type} [CGR : CyclicGroupRing G]

/-! ## The unit of the exponent ring -/

open Classical in
/-- The unit of the exponent ring: for a nonzero `d`, the preimage of `d` under multiplication
by `d`; the zero exponent when every exponent is zero. -/
noncomputable def expOne : CGR.Exp :=
  if h : ∃ d : CGR.Exp, d ≠ CGR.expZero then
    ((CGR.expMul_bij h.choose h.choose_spec).2 h.choose).choose
  else CGR.expZero

/-- `expOne` is a right unit of exponent multiplication. -/
theorem expMul_expOne (a : CGR.Exp) : CGR.expMul a expOne = a := by
  unfold expOne
  split
  · rename_i h
    have hu := ((CGR.expMul_bij h.choose h.choose_spec).2 h.choose).choose_spec
    apply (CGR.expMul_bij h.choose h.choose_spec).1
    rw [← CGR.expMul_assoc, CGR.expMul_comm' h.choose a, CGR.expMul_assoc, hu,
      CGR.expMul_comm']
  · rename_i h
    simp_all

/-- `expOne` is a left unit of exponent multiplication. -/
theorem expOne_expMul (a : CGR.Exp) : CGR.expMul expOne a = a := by
  rw [CGR.expMul_comm', expMul_expOne]

/-! ## The commutative ring of exponents -/

/-- The commutative ring structure of `CGR.Exp` given by `expAdd`, `expZero`, `expNeg`,
`expMul` and `expOne`. -/
noncomputable abbrev expCommRing : CommRing CGR.Exp :=
  letI : Zero CGR.Exp := ⟨CGR.expZero⟩
  letI : Add CGR.Exp := ⟨CGR.expAdd⟩
  letI : Neg CGR.Exp := ⟨CGR.expNeg⟩
  letI : Mul CGR.Exp := ⟨CGR.expMul⟩
  letI : One CGR.Exp := ⟨expOne⟩
  { add_assoc := CGR.expAdd_assoc
    zero_add := CyclicGroupRing.expZero_add
    add_zero := CGR.expAdd_zero
    add_comm := CGR.expAdd_comm
    neg_add_cancel := fun a => by
      change CGR.expAdd (CGR.expNeg a) a = CGR.expZero
      rw [CGR.expAdd_comm, CGR.expAdd_neg]
    mul_assoc := CGR.expMul_assoc
    one_mul := expOne_expMul
    mul_one := expMul_expOne
    zero_mul := CyclicGroupRing.expMul_zero
    mul_zero := CyclicGroupRing.expZero_mul
    left_distrib := CGR.expMul_add
    right_distrib := CyclicGroupRing.expAdd_mul
    mul_comm := CGR.expMul_comm'
    nsmul := nsmulRec
    zsmul := zsmulRec }

/-- A nontrivial exponent ring is a domain: multiplication by a nonzero exponent is
injective. -/
theorem expIsDomain [Nontrivial CGR.Exp] : @IsDomain CGR.Exp expCommRing.toSemiring := by
  let := expCommRing (G := G)
  refine @NoZeroDivisors.to_isDomain CGR.Exp _ _ ⟨fun {a b} hab => ?_⟩
  by_cases ha : a = 0
  · exact Or.inl ha
  · right
    apply (CGR.expMul_bij a ha).1
    change CGR.expMul a b = CGR.expMul a CGR.expZero
    rw [CyclicGroupRing.expZero_mul]
    exact hab

/-! ## Powers and the challenge -/

/-- The power `χ^i` of an exponent. -/
noncomputable def expPow (χ : CGR.Exp) : ℕ → CGR.Exp
  | 0 => expOne
  | i + 1 => CGR.expMul χ (expPow χ i)

variable (G) in
/-- The `D`-DL challenge `(g, g^χ, g^{χ^2}, …, g^{χ^D})`, a list of length `D + 1`. -/
noncomputable def kDLChallenge (D : ℕ) (χ : CGR.Exp) : List G :=
  (List.range (D + 1)).map fun i => CyclicGroup.elemPow CGR.gen (expPow χ i)

/-- The entry `1` of the challenge is `g^χ`. -/
theorem kDLChallenge_getD_one (D : ℕ) (χ : CGR.Exp) (d : G) :
    (kDLChallenge G (D + 1) χ).getD 1 d = CyclicGroup.elemPow CGR.gen χ := by
  simp [kDLChallenge, expPow, expMul_expOne]

/-! ## Games -/

section Games

variable [DecidableEq CGR.Exp]

variable (G) in
/-- **The `D`-DL game (FKL18, Definition 2.4).** Sample `χ`, run `B` on
`kDLChallenge G D χ` and return whether its output is `χ`. -/
noncomputable def KDL_Game (D : ℕ) (B : List G → PMF CGR.Exp) : SPComp Bool :=
  liftPMF ((PMF.uniformFintype CGR.Exp).bind fun χ =>
    (B (kDLChallenge G D χ)).map fun y => decide (y = χ))

variable (G) in
/-- **`D`-DL advantage.** The probability that `B` finds `χ` from `(g, g^χ, …, g^{χ^D})`. -/
noncomputable def KDL_Advantage (D : ℕ) (B : List G → PMF CGR.Exp) : ℝ≥0∞ :=
  prTrue (KDL_Game G D B) Heap.empty

/-- **The DL game.** The `1`-DL game with the adversary given the entry `g^χ`. -/
noncomputable def DL_Game (B : G → PMF CGR.Exp) : SPComp Bool :=
  KDL_Game G 1 fun ch => B (ch.getD 1 CGR.one)

/-- **DL advantage.** The probability that `B` finds `χ` from `g^χ`. -/
noncomputable def DL_Advantage (B : G → PMF CGR.Exp) : ℝ≥0∞ :=
  prTrue (DL_Game B) Heap.empty

/-- The DL game samples `χ`, runs `B` on `g^χ` and returns whether its output is `χ`. -/
theorem DL_Game_eq (B : G → PMF CGR.Exp) :
    DL_Game B = liftPMF ((PMF.uniformFintype CGR.Exp).bind fun χ =>
      (B (CyclicGroup.elemPow CGR.gen χ)).map fun y => decide (y = χ)) := by
  simp only [DL_Game, KDL_Game, kDLChallenge_getD_one]

end Games

/-! ## List polynomials -/

/-- Evaluation of a list polynomial (constant term first) by Horner's rule. -/
def peval (p : Poly G) (x : CGR.Exp) : CGR.Exp :=
  p.foldr (fun a acc => CGR.expAdd a (CGR.expMul x acc)) CGR.expZero

/-- A list polynomial is nonzero when one of its coefficients is nonzero. -/
def PolyNonzero (p : Poly G) : Prop := ∃ a ∈ p, a ≠ CGR.expZero

/-- The Mathlib polynomial over `expCommRing` with the coefficients of `p`. -/
noncomputable def toPolynomial : Poly G → @Polynomial CGR.Exp expCommRing.toSemiring
  | [] => letI := expCommRing (G := G); 0
  | a :: p => letI := expCommRing (G := G); Polynomial.C a + Polynomial.X * toPolynomial p

/-- Evaluation of `toPolynomial p` is evaluation of `p`. -/
theorem eval_toPolynomial (p : Poly G) (x : CGR.Exp) :
    letI := expCommRing (G := G); (toPolynomial p).eval x = peval p x := by
  let := expCommRing (G := G)
  induction p with
  | nil => simp [toPolynomial, peval]; rfl
  | cons a p ih =>
    simp only [toPolynomial, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul,
      Polynomial.eval_X, ih]
    rfl

/-- The coefficients of `toPolynomial p` are the entries of `p`. -/
theorem coeff_toPolynomial (p : Poly G) (i : ℕ) :
    letI := expCommRing (G := G); (toPolynomial p).coeff i = p.getD i CGR.expZero := by
  let := expCommRing (G := G)
  induction p generalizing i with
  | nil => simp [toPolynomial]; rfl
  | cons a p ih =>
    cases i with
    | zero => simp [toPolynomial]
    | succ i => simp [toPolynomial, Polynomial.coeff_X_mul, ih]

/-- **Root count.** A nonzero list polynomial with at most `D + 1` coefficients has at most
`D` roots. -/
theorem card_roots_le [DecidableEq CGR.Exp] (p : Poly G) (D : ℕ) (hp : PolyNonzero p)
    (hlen : p.length ≤ D + 1) :
    (Finset.univ.filter fun r => peval p r = CGR.expZero).card ≤ D := by
  let := expCommRing (G := G)
  obtain ⟨a, ha, ha0⟩ := hp
  have : Nontrivial CGR.Exp := ⟨⟨a, CGR.expZero, ha0⟩⟩
  have := expIsDomain (G := G)
  have hne : toPolynomial p ≠ 0 := by
    intro h
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    have hc := coeff_toPolynomial p i
    rw [h, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi] at hc
    exact ha0 hc.symm
  have hdeg : (toPolynomial p).natDegree ≤ D := by
    rw [Polynomial.natDegree_le_iff_coeff_eq_zero]
    intro N hN
    rw [coeff_toPolynomial, List.getD_eq_getElem?_getD,
      List.getElem?_eq_none (by omega : p.length ≤ N)]
    rfl
  calc (Finset.univ.filter fun r => peval p r = CGR.expZero).card
      ≤ (toPolynomial p).roots.toFinset.card := by
        apply Finset.card_le_card
        intro r hr
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hr
        rw [Multiset.mem_toFinset, Polynomial.mem_roots hne, Polynomial.IsRoot,
          eval_toPolynomial]
        exact hr
    _ ≤ (toPolynomial p).roots.card := Multiset.toFinset_card_le _
    _ ≤ (toPolynomial p).natDegree := Polynomial.card_roots' _
    _ ≤ D := hdeg

variable (G) in
/-- **A root-finding algorithm** for list polynomials over the exponent ring: `roots p` lists
every root of a nonzero polynomial `p`. -/
structure RootFinder where
  /-- The candidate roots of a polynomial. -/
  roots : Poly G → List CGR.Exp
  /-- Every root of a nonzero polynomial is listed. -/
  complete : ∀ p, PolyNonzero p → ∀ r, peval p r = CGR.expZero → r ∈ roots p

end CatCrypt.Crypto.Assumptions.KDL
