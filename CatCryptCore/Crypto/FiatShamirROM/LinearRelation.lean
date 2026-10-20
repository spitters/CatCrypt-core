/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.FiatShamirROM.Game
public import CatCryptCore.Examples.GroupParam
public import CatCryptCore.ForMathlib.PMFUniform

/-!
# The Σ-protocol for a linear relation

A linear relation over a prime-order group `gp` in the shape of the `LinearRelation`
of draft-irtf-cfrg-sigma-protocols-03 §3: a list of group elements and `m`
equations, each the index of its image element and a list of terms
`(scalar index, element index)`. The linear map sends a vector `w` of `n` scalars to
the vector whose entry `i` is the product of `elements[k]^(w[j])` over the terms
`(j, k)` of equation `i`; a witness for the relation is a `w` with `map w = image`.

The Σ-protocol `linearSigma gp n m toRel gen` proves knowledge of a witness for the
relation `toRel s` of a statement `s`: the commitment is `map r` for uniform nonces
`r`, the response `z = r + c·w`, the verifier checks `map z = a · image^c`
componentwise, the simulator answers `(map z · image^(−c), z)` on a uniform `z`, and
the extractor is `(z₁ − z₂)/(c₁ − c₂)` per scalar.

## Main definitions

* `GroupParam.scalarCommRing` — the commutative ring of the scalars of `gp`
* `GroupParam.dlog` — the discrete logarithm to the generator
* `LinearEquation`, `LinearRelation` — linear relations, with `map`, `image`,
  `Holds`, `IndexValid`, `column`, `simCommit` and `ValidateInstance`, the predicates of
  draft-03 §3.5 for a relation whose element `0` is the generator
* `LinearRelation.and` — AND composition by concatenation
* `linearSigma` — the Σ-protocol for a family of linear relations
* `linearBatchVerify`, `linearCompactVerify` — the verifiers of the batchable proofs
  `(a, z)` and of the compact proofs `(c, z)` for a challenge function `H`
* `dlogRelation`, `dleqRelation`, `pedersenRelation`, `representationRelation`,
  `elgamalRelation` — discrete logarithm, DLEQ (Chaum–Pedersen), Pedersen opening,
  representation (Okamoto) and ElGamal plaintext knowledge, with their Σ-protocols
  `dlogSigma`, `dleqSigma`, `pedersenSigma`, `representationSigma`, `elgamalSigma`

## Main results

* `linearSigma_complete`, `linearSigma_specialSound`, `linearSigma_perfectHVZK` (for a
  generator supported on the relation), `linearSigma_uniqueResp` (for injective maps)
* `LinearRelation.map_and`, `LinearRelation.image_and`, `LinearRelation.holds_and_iff`,
  `LinearRelation.indexValid_and`, `LinearRelation.map_and_injective` — the map, image,
  witnesses, index ranges and injectivity of an AND composition are those of its parts
* `LinearRelation.validateInstance_and` — the AND composition of valid relations is valid
  when the generator of the second occurs in one of its equations
* `linearSigma_verify_iff` — a transcript verifies exactly when its commitment is
  the one recomputed by the simulator
* `linearSigma_compactVerify_iff`, `linearSigma_batchVerify_iff` — the compact
  verifier accepts `(c, z)` exactly when `(c, z)` is the compression of a proof the
  batchable verifier accepts
* `dlogRelation_holds_iff` and its analogues — the witnesses of each instance
* `dlogSigma_complete`, `dlogSigma_specialSound`, `dlogSigma_perfectHVZK`,
  `dlogSigma_uniqueResp`, `dleqSigma_uniqueResp`, `elgamalSigma_uniqueResp`
* `dlogSigma_verify_iff` — on constant vectors the verifier of `dlogSigma` is the
  Schnorr verification equation

## References

* M. Orrù, C. Yun, *Interactive Sigma Proofs*, draft-irtf-cfrg-sigma-protocols-03.
* R. Cramer, I. Damgård, B. Schoenmakers, *Proofs of partial knowledge and
  simplified design of witness hiding protocols*, CRYPTO 1994.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Examples.GroupParam

variable (gp : GroupParam)

/-- The commutative ring of the scalars of `gp`, with the operations of `gp`. -/
@[reducible] def scalarCommRing : CommRing gp.Scalar where
  add := gp.scalarAdd
  add_assoc := gp.scalarAdd_assoc
  zero := gp.scalarZero
  zero_add := gp.scalarZero_add
  add_zero := gp.scalarAdd_zero
  nsmul := @nsmulRec _ ⟨gp.scalarZero⟩ ⟨gp.scalarAdd⟩
  nsmul_zero _ := rfl
  nsmul_succ _ _ := rfl
  neg := gp.scalarNeg
  sub := gp.scalarSub
  sub_eq_add_neg := gp.scalarSub_eq
  zsmul := @zsmulRec _ ⟨gp.scalarZero⟩ ⟨gp.scalarAdd⟩ ⟨gp.scalarNeg⟩
    (@nsmulRec _ ⟨gp.scalarZero⟩ ⟨gp.scalarAdd⟩)
  zsmul_zero' _ := rfl
  zsmul_succ' _ _ := rfl
  zsmul_neg' _ _ := rfl
  neg_add_cancel := gp.scalarNeg_add
  add_comm := gp.scalarAdd_comm
  mul := gp.scalarMul
  left_distrib := gp.scalarMul_add
  right_distrib := gp.scalarAdd_mul
  zero_mul := gp.scalarZero_mul
  mul_zero := gp.scalarMul_zero
  mul_assoc := gp.scalarMul_assoc
  one := gp.scalarOne
  one_mul a := (gp.scalarMul_comm _ _).trans (gp.scalarMul_one a)
  mul_one := gp.scalarMul_one
  mul_comm := gp.scalarMul_comm

/-- The discrete logarithm of a group element to the generator. -/
noncomputable def dlog (h : gp.G) : gp.Scalar := Classical.choose (gp.exp_surj h)

theorem exp_dlog (h : gp.G) : gp.exp (gp.dlog h) = h := Classical.choose_spec (gp.exp_surj h)

theorem dlog_exp (s : gp.Scalar) : gp.dlog (gp.exp s) = s := gp.exp_inj _ _ (gp.exp_dlog _)

theorem groupExp_eq_exp (h : gp.G) (e : gp.Scalar) :
    gp.groupExp h e = gp.exp (gp.scalarMul (gp.dlog h) e) := by
  have h' := gp.groupExp_exp (gp.dlog h) e
  rwa [gp.exp_dlog] at h'

theorem groupMul_eq_exp (a b : gp.G) :
    gp.groupMul a b = gp.exp (gp.scalarAdd (gp.dlog a) (gp.dlog b)) := by
  rw [gp.exp_add, gp.exp_dlog, gp.exp_dlog]

theorem groupInv_eq_exp (a : gp.G) : gp.groupInv a = gp.exp (gp.scalarNeg (gp.dlog a)) := by
  have h := gp.groupInv_groupExp a gp.scalarOne
  rwa [gp.groupExp_one, groupExp_eq_exp, scalarMul_neg, gp.scalarMul_one] at h

theorem dlog_generator : gp.dlog gp.generator = gp.scalarOne :=
  gp.exp_inj _ _ (by rw [exp_dlog, gp.groupExp_generator, gp.groupExp_one])

theorem exp_inj_iff (a b : gp.Scalar) : gp.exp a = gp.exp b ↔ a = b :=
  ⟨gp.exp_inj a b, congrArg gp.exp⟩

section Ring

attribute [local instance] scalarCommRing

theorem scalarAdd_eq_add (a b : gp.Scalar) : gp.scalarAdd a b = a + b := rfl

theorem scalarMul_eq_mul (a b : gp.Scalar) : gp.scalarMul a b = a * b := rfl

theorem scalarSub_eq_sub (a b : gp.Scalar) : gp.scalarSub a b = a - b := rfl

theorem scalarNeg_eq_neg (a : gp.Scalar) : gp.scalarNeg a = -a := rfl

theorem scalarZero_eq_zero : gp.scalarZero = 0 := rfl

end Ring

end CatCrypt.Examples.GroupParam

namespace CatCrypt.Crypto.FiatShamirROM

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Examples
open scoped ENNReal

/-! ## Linear relations -/

/-- One equation of a linear relation: the index of its image element and its terms,
each a pair `(scalar index, element index)`. -/
structure LinearEquation where
  /-- The index of the image element. -/
  lhs : ℕ
  /-- The terms `(scalar index, element index)`. -/
  terms : List (ℕ × ℕ)
deriving DecidableEq

/-- The equation with scalar indices shifted by `dn` and element indices by `dk`. -/
def LinearEquation.shift (dn dk : ℕ) (e : LinearEquation) : LinearEquation :=
  ⟨e.lhs + dk, e.terms.map fun t => (t.1 + dn, t.2 + dk)⟩

/-- A linear relation over `gp` with `n` scalars and `m` equations. -/
structure LinearRelation (gp : GroupParam) (n m : ℕ) where
  /-- The group elements. -/
  elements : List gp.G
  /-- The equations. -/
  equations : Fin m → LinearEquation

/-- The entry `j` of a scalar vector, zero out of range. -/
def vecGet {gp : GroupParam} {n : ℕ} (w : Fin n → gp.Scalar) (j : ℕ) : gp.Scalar :=
  if h : j < n then w ⟨j, h⟩ else gp.scalarZero

namespace LinearRelation

variable {gp : GroupParam} {n m : ℕ} (x : LinearRelation gp n m)

/-- The group element of index `k`, the identity out of range. -/
def elem (k : ℕ) : gp.G := x.elements.getD k gp.identity

/-- The linear map: entry `i` is the product of `elem k ^ w[j]` over the terms
`(j, k)` of equation `i`. -/
def map (w : Fin n → gp.Scalar) : Fin m → gp.G := fun i =>
  ((x.equations i).terms.map fun t => gp.groupExp (x.elem t.2) (vecGet w t.1)).foldr
    gp.groupMul gp.identity

/-- The image: entry `i` is the image element of equation `i`. -/
def image : Fin m → gp.G := fun i => x.elem (x.equations i).lhs

/-- `w` is a witness: `map w = image`. -/
def Holds (w : Fin n → gp.Scalar) : Prop := x.map w = x.image

instance (w : Fin n → gp.Scalar) : Decidable (x.Holds w) :=
  inferInstanceAs (Decidable (x.map w = x.image))

/-- Every index of the relation is in range: image and element indices below the
number of elements, scalar indices below `n`. -/
def IndexValid : Prop :=
  ∀ i, (x.equations i).lhs < x.elements.length ∧
    ∀ t ∈ (x.equations i).terms, t.1 < n ∧ t.2 < x.elements.length

instance : Decidable x.IndexValid := by
  unfold IndexValid; infer_instance

/-- The entry of column `j` of the matrix of the linear map in row `i`: the product of
the elements `elem k` over the terms `(j, k)` of equation `i`. -/
def column (j : ℕ) (i : Fin m) : gp.G :=
  (((x.equations i).terms.filter fun t => t.1 == j).map fun t => x.elem t.2).foldr
    gp.groupMul gp.identity

/-- The predicates of `ValidateInstance` of draft-irtf-cfrg-sigma-protocols-03 §3.5 for a
relation whose element `0` is the generator, in the order of the draft's checks: there is
an equation (check 1); every equation has a term (check 2); the indices are in range
(check 4); every element other than the generator occurs in an equation (check 5); every
scalar index below `n` occurs in a term (check 6); element `0` is the generator
(check 7); no element (check 8), no image entry (check 9) and no column of the matrix of
the linear map (check 10) is the identity. Check 3 bounds the counts of an encoding by
`2^32 − 1` and has no counterpart here. -/
structure ValidateInstance : Prop where
  equations_pos : 0 < m
  terms_ne_nil : ∀ i, (x.equations i).terms ≠ []
  indexValid : x.IndexValid
  element_used : ∀ k < x.elements.length, k ≠ 0 →
    ∃ i, (x.equations i).lhs = k ∨ ∃ t ∈ (x.equations i).terms, t.2 = k
  scalar_used : ∀ j < n, ∃ i, ∃ t ∈ (x.equations i).terms, t.1 = j
  head_generator : x.elements.head? = some gp.generator
  elements_ne_identity : ∀ g ∈ x.elements, g ≠ gp.identity
  image_ne_identity : ∀ i, x.image i ≠ gp.identity
  column_ne_identity : ∀ j < n, ∃ i, x.column j i ≠ gp.identity

instance : Decidable x.ValidateInstance :=
  decidable_of_iff (0 < m ∧ (∀ i, (x.equations i).terms ≠ []) ∧ x.IndexValid ∧
      (∀ k < x.elements.length, k ≠ 0 →
        ∃ i, (x.equations i).lhs = k ∨ ∃ t ∈ (x.equations i).terms, t.2 = k) ∧
      (∀ j < n, ∃ i, ∃ t ∈ (x.equations i).terms, t.1 = j) ∧
      x.elements.head? = some gp.generator ∧ (∀ g ∈ x.elements, g ≠ gp.identity) ∧
      (∀ i, x.image i ≠ gp.identity) ∧ (∀ j < n, ∃ i, x.column j i ≠ gp.identity))
    ⟨fun ⟨a, b, c, d, e, f, g, h, k⟩ => ⟨a, b, c, d, e, f, g, h, k⟩,
      fun ⟨a, b, c, d, e, f, g, h, k⟩ => ⟨a, b, c, d, e, f, g, h, k⟩⟩

/-- The commitment for which `(a, c, z)` verifies: `map z · image^(−c)`. -/
def simCommit (c : gp.Scalar) (z : Fin n → gp.Scalar) : Fin m → gp.G := fun i =>
  gp.groupMul (x.map z i) (gp.groupInv (gp.groupExp (x.image i) c))

/-- The discrete logarithm of `map w`, entry by entry. -/
noncomputable def lin (w : Fin n → gp.Scalar) (i : Fin m) : gp.Scalar :=
  ((x.equations i).terms.map fun t => gp.scalarMul (gp.dlog (x.elem t.2)) (vecGet w t.1)).foldr
    gp.scalarAdd gp.scalarZero

theorem map_eq_exp (w : Fin n → gp.Scalar) (i : Fin m) : x.map w i = gp.exp (x.lin w i) := by
  unfold map lin
  induction (x.equations i).terms with
  | nil => exact gp.exp_zero.symm
  | cons t ts ih =>
    simp only [List.map_cons, List.foldr_cons]
    rw [ih, gp.exp_add, GroupParam.groupExp_eq_exp]

attribute [local instance] GroupParam.scalarCommRing

theorem vecGet_add_mul (r w : Fin n → gp.Scalar) (c : gp.Scalar) (j : ℕ) :
    vecGet (fun j => gp.scalarAdd (r j) (gp.scalarMul c (w j))) j =
      gp.scalarAdd (vecGet r j) (gp.scalarMul c (vecGet w j)) := by
  unfold vecGet
  split
  · rfl
  · simp only [GroupParam.scalarAdd_eq_add, GroupParam.scalarMul_eq_mul,
      GroupParam.scalarZero_eq_zero]
    ring

theorem lin_add_mul (r w : Fin n → gp.Scalar) (c : gp.Scalar) (i : Fin m) :
    x.lin (fun j => gp.scalarAdd (r j) (gp.scalarMul c (w j))) i =
      gp.scalarAdd (x.lin r i) (gp.scalarMul c (x.lin w i)) := by
  unfold lin
  induction (x.equations i).terms with
  | nil =>
    simp only [List.map_nil, List.foldr_nil, GroupParam.scalarAdd_eq_add,
      GroupParam.scalarMul_eq_mul, GroupParam.scalarZero_eq_zero]
    ring
  | cons t ts ih =>
    simp only [List.map_cons, List.foldr_cons] at ih ⊢
    rw [ih, vecGet_add_mul]
    simp only [GroupParam.scalarAdd_eq_add, GroupParam.scalarMul_eq_mul]
    ring

theorem lin_mul_sub (u z z' : Fin n → gp.Scalar) (d : gp.Scalar)
    (hu : ∀ j, u j * d = z j - z' j) (i : Fin m) :
    x.lin u i * d = x.lin z i - x.lin z' i := by
  have hv : ∀ k, vecGet u k * d = vecGet z k - vecGet z' k := by
    intro k
    unfold vecGet
    split
    · exact hu _
    · simp only [GroupParam.scalarZero_eq_zero]
      ring
  unfold lin
  induction (x.equations i).terms with
  | nil =>
    simp only [List.map_nil, List.foldr_nil, GroupParam.scalarZero_eq_zero]
    ring
  | cons t ts ih =>
    simp only [List.map_cons, List.foldr_cons, GroupParam.scalarAdd_eq_add,
      GroupParam.scalarMul_eq_mul] at ih ⊢
    linear_combination gp.dlog (x.elem t.2) * hv t.1 + ih

end LinearRelation

/-! ## The Σ-protocol -/

section Protocol

variable (gp : GroupParam) (n m : ℕ) {S : Type} (toRel : S → LinearRelation gp n m)
  (gen : PMF (S × (Fin n → gp.Scalar)))

/-- The Σ-protocol for the linear relations `toRel s`, with generator `gen`. -/
noncomputable def linearSigma : Sigma where
  Stmt := S
  Wit := Fin n → gp.Scalar
  Com := Fin m → gp.G
  Ch := gp.Scalar
  Resp := Fin n → gp.Scalar
  Rand := Fin n → gp.Scalar
  SimRand := Fin n → gp.Scalar
  inhWit := ⟨fun _ => gp.scalarZero⟩
  rel s w := (toRel s).Holds w
  gen := gen
  commit s _ r := (toRel s).map r
  respond _ w r c j := gp.scalarAdd (r j) (gp.scalarMul c (w j))
  verify s a c z :=
    decide ((toRel s).map z = fun i => gp.groupMul (a i) (gp.groupExp ((toRel s).image i) c))
  simulate s c z := ((toRel s).simCommit c z, z)
  extract _ _ c z c' z' j := gp.scalarDiv (gp.scalarSub (z j) (z' j)) (gp.scalarSub c c')

variable {gp n m}

attribute [local instance] GroupParam.scalarCommRing

theorem linearSigma_verify_iff (s : S) (a : Fin m → gp.G) (c : gp.Scalar)
    (z : Fin n → gp.Scalar) :
    (linearSigma gp n m toRel gen).verify s a c z = true ↔ a = (toRel s).simCommit c z := by
  simp only [linearSigma, decide_eq_true_iff, funext_iff, LinearRelation.simCommit]
  refine forall_congr' fun i => ?_
  rw [← gp.exp_dlog (a i)]
  simp only [LinearRelation.map_eq_exp, GroupParam.groupMul_eq_exp,
    GroupParam.groupExp_eq_exp, GroupParam.groupInv_eq_exp, GroupParam.dlog_exp,
    GroupParam.exp_inj_iff, GroupParam.scalarAdd_eq_add, GroupParam.scalarMul_eq_mul,
    GroupParam.scalarNeg_eq_neg]
  constructor <;> intro h <;> linear_combination -h

/-- The simulated commitment on the response `r + c·w` for a witness `w` is the
honest commitment `map r`. -/
theorem simCommit_respond (x : LinearRelation gp n m) (w r : Fin n → gp.Scalar)
    (hw : x.Holds w) (c : gp.Scalar) :
    x.simCommit c (fun j => gp.scalarAdd (r j) (gp.scalarMul c (w j))) = x.map r := by
  funext i
  have hi : x.image i = x.map w i := (congrFun hw i).symm
  simp only [LinearRelation.simCommit, hi, LinearRelation.map_eq_exp,
    LinearRelation.lin_add_mul]
  simp only [GroupParam.groupMul_eq_exp, GroupParam.groupExp_eq_exp,
    GroupParam.groupInv_eq_exp, GroupParam.dlog_exp, GroupParam.exp_inj_iff,
    GroupParam.scalarAdd_eq_add, GroupParam.scalarMul_eq_mul, GroupParam.scalarNeg_eq_neg]
  ring

theorem linearSigma_complete : (linearSigma gp n m toRel gen).Complete := by
  intro s w hw r c
  exact (linearSigma_verify_iff toRel gen s _ c _).mpr (simCommit_respond (toRel s) w r hw c).symm

theorem linearSigma_specialSound : (linearSigma gp n m toRel gen).SpecialSound := by
  intro (s : S) (a : Fin m → gp.G) (c : gp.Scalar) (z : Fin n → gp.Scalar) (c' : gp.Scalar)
    (z' : Fin n → gp.Scalar) h h' hne
  have e := ((linearSigma_verify_iff toRel gen s a c z).mp h).symm.trans
    ((linearSigma_verify_iff toRel gen s a c' z').mp h')
  have hd : gp.scalarSub c c' ≠ gp.scalarZero := gp.scalarSub_ne_zero c c' hne
  funext i
  have ei := congrFun e i
  simp only [LinearRelation.simCommit, LinearRelation.map_eq_exp, GroupParam.groupMul_eq_exp,
    GroupParam.groupExp_eq_exp, GroupParam.groupInv_eq_exp, GroupParam.dlog_exp,
    GroupParam.exp_inj_iff] at ei
  change (toRel s).map (fun j => gp.scalarDiv (gp.scalarSub (z j) (z' j))
    (gp.scalarSub c c')) i = (toRel s).image i
  rw [LinearRelation.map_eq_exp, ← gp.exp_dlog ((toRel s).image i), GroupParam.exp_inj_iff]
  have hl := (toRel s).lin_mul_sub _ z z' (gp.scalarSub c c')
    (fun j => gp.div_mul_cancel _ _ hd) i
  rw [← gp.mul_div_cancel ((toRel s).lin _ i) _ hd,
    ← gp.mul_div_cancel (gp.dlog ((toRel s).image i)) _ hd]
  congr 1
  simp only [GroupParam.scalarAdd_eq_add, GroupParam.scalarMul_eq_mul,
    GroupParam.scalarNeg_eq_neg, GroupParam.scalarSub_eq_sub] at ei hl ⊢
  linear_combination hl + ei

theorem linearSigma_perfectHVZK
    (hgen : ∀ s w, (s, w) ∈ gen.support → (toRel s).Holds w) :
    (linearSigma gp n m toRel gen).PerfectHVZK := by
  intro s w hsw c
  have hw := hgen s w hsw
  let e : (Fin n → gp.Scalar) ≃ (Fin n → gp.Scalar) :=
    { toFun := fun r j => gp.scalarAdd (r j) (gp.scalarMul c (w j))
      invFun := fun z j => gp.scalarSub (z j) (gp.scalarMul c (w j))
      left_inv := fun r => by
        funext j
        simp only [GroupParam.scalarAdd_eq_add, GroupParam.scalarSub_eq_sub]
        ring
      right_inv := fun z => by
        funext j
        simp only [GroupParam.scalarAdd_eq_add, GroupParam.scalarSub_eq_sub]
        ring }
  change (PMF.uniformOfFintype (Fin n → gp.Scalar)).map
      (fun r => ((toRel s).map r, fun j => gp.scalarAdd (r j) (gp.scalarMul c (w j)))) =
    (PMF.uniformOfFintype (Fin n → gp.Scalar)).map (fun z => ((toRel s).simCommit c z, z))
  conv_rhs => rw [← PMF.uniformOfFintype_map_equiv e, PMF.map_comp]
  congr 1
  funext r
  simp only [Function.comp_apply]
  exact Prod.ext (simCommit_respond (toRel s) w r hw c).symm rfl

theorem linearSigma_uniqueResp (hinj : ∀ s, Function.Injective (toRel s).map) :
    (linearSigma gp n m toRel gen).UniqueResp := by
  intro s a c z z' h h'
  simp only [linearSigma, decide_eq_true_iff] at h h'
  exact hinj s (h.trans h'.symm)

/-- The verifier of a batchable proof `(a, z)` for the challenge function `H`: the
transcript `(a, H s a, z)` verifies. -/
noncomputable def linearBatchVerify (H : S → (Fin m → gp.G) → gp.Scalar) (s : S)
    (a : Fin m → gp.G) (z : Fin n → gp.Scalar) : Bool :=
  (linearSigma gp n m toRel gen).verify s a (H s a) z

/-- The verifier of a compact proof `(c, z)` for the challenge function `H`: the
challenge is `H` of the commitment recomputed by the simulator. -/
noncomputable def linearCompactVerify (H : S → (Fin m → gp.G) → gp.Scalar) (s : S)
    (c : gp.Scalar) (z : Fin n → gp.Scalar) : Bool :=
  decide (H s ((toRel s).simCommit c z) = c)

/-- The compact verifier accepts `(c, z)` exactly when `(c, z)` is the compression
`(H s a, z)` of a proof `(a, z)` that the batchable verifier accepts. -/
theorem linearSigma_compactVerify_iff (H : S → (Fin m → gp.G) → gp.Scalar) (s : S)
    (c : gp.Scalar) (z : Fin n → gp.Scalar) :
    linearCompactVerify toRel H s c z = true ↔
      ∃ a, linearBatchVerify toRel gen H s a z = true ∧ H s a = c := by
  simp only [linearCompactVerify, linearBatchVerify, decide_eq_true_iff,
    linearSigma_verify_iff]
  constructor
  · intro h
    exact ⟨_, by rw [h], h⟩
  · rintro ⟨a, ha, rfl⟩
    rw [← ha]

/-- A batchable proof `(a, z)` is accepted exactly when its compression
`(H s a, z)` is accepted and `a` is the commitment the simulator recomputes from it. -/
theorem linearSigma_batchVerify_iff (H : S → (Fin m → gp.G) → gp.Scalar) (s : S)
    (a : Fin m → gp.G) (z : Fin n → gp.Scalar) :
    linearBatchVerify toRel gen H s a z = true ↔
      linearCompactVerify toRel H s (H s a) z = true ∧ a = (toRel s).simCommit (H s a) z := by
  simp only [linearCompactVerify, linearBatchVerify, decide_eq_true_iff,
    linearSigma_verify_iff]
  constructor
  · intro h
    exact ⟨by rw [← h], h⟩
  · exact fun h => h.2

end Protocol

/-! ## AND composition -/

namespace LinearRelation

variable {gp : GroupParam} {n₁ n₂ m₁ m₂ : ℕ} (x₁ : LinearRelation gp n₁ m₁)
  (x₂ : LinearRelation gp n₂ m₂)

/-- The AND composition: the elements of `x₂` follow those of `x₁`, its scalars
follow those of `x₁`, and its equations, with indices shifted, follow those of
`x₁`. -/
def and : LinearRelation gp (n₁ + n₂) (m₁ + m₂) where
  elements := x₁.elements ++ x₂.elements
  equations := Fin.append x₁.equations fun i => (x₂.equations i).shift n₁ x₁.elements.length

theorem equations_and_left (i : Fin m₁) :
    (x₁.and x₂).equations (Fin.castAdd m₂ i) = x₁.equations i :=
  Fin.append_left x₁.equations (fun i => (x₂.equations i).shift n₁ x₁.elements.length) i

theorem equations_and_right (i : Fin m₂) :
    (x₁.and x₂).equations (Fin.natAdd m₁ i) = (x₂.equations i).shift n₁ x₁.elements.length :=
  Fin.append_right x₁.equations (fun i => (x₂.equations i).shift n₁ x₁.elements.length) i

theorem elem_and_left (k : ℕ) (hk : k < x₁.elements.length) :
    (x₁.and x₂).elem k = x₁.elem k := by
  simp only [elem, and, List.getD_eq_getElem?_getD, List.getElem?_append_left hk]

theorem elem_and_right (k : ℕ) : (x₁.and x₂).elem (k + x₁.elements.length) = x₂.elem k := by
  simp [elem, and, List.getD_eq_getElem?_getD, List.getElem?_append_right]

theorem vecGet_append_left (w₁ : Fin n₁ → gp.Scalar) (w₂ : Fin n₂ → gp.Scalar) (j : ℕ)
    (hj : j < n₁) : vecGet (Fin.append w₁ w₂) j = vecGet w₁ j := by
  simp only [vecGet, dif_pos hj, Nat.lt_add_right n₂ hj]
  exact Fin.append_left w₁ w₂ ⟨j, hj⟩

theorem vecGet_append_right (w₁ : Fin n₁ → gp.Scalar) (w₂ : Fin n₂ → gp.Scalar) (j : ℕ) :
    vecGet (Fin.append w₁ w₂) (j + n₁) = vecGet w₂ j := by
  unfold vecGet
  by_cases hj : j < n₂
  · rw [dif_pos (by omega), dif_pos hj]
    have e : (⟨j + n₁, by omega⟩ : Fin (n₁ + n₂)) = Fin.natAdd n₁ ⟨j, hj⟩ :=
      Fin.ext (Nat.add_comm _ _)
    rw [e, Fin.append_right]
  · rw [dif_neg (by omega), dif_neg hj]

variable {x₁ x₂}

/-- The map of an AND composition on concatenated witnesses is the concatenation of
the maps. -/
theorem map_and (h₁ : x₁.IndexValid) (w₁ : Fin n₁ → gp.Scalar)
    (w₂ : Fin n₂ → gp.Scalar) :
    (x₁.and x₂).map (Fin.append w₁ w₂) = Fin.append (x₁.map w₁) (x₂.map w₂) := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp only [map, equations_and_left, Fin.append_left]
    congr 1
    refine List.map_congr_left fun t ht => ?_
    obtain ⟨hs, hk⟩ := (h₁ i).2 t ht
    rw [elem_and_left x₁ x₂ _ hk, vecGet_append_left _ _ _ hs]
  · simp only [map, equations_and_right, LinearEquation.shift, List.map_map, Fin.append_right]
    congr 1
    refine List.map_congr_left fun t _ => ?_
    simp only [Function.comp_apply, elem_and_right, vecGet_append_right]

/-- The image of an AND composition is the concatenation of the images. -/
theorem image_and (h₁ : x₁.IndexValid) :
    (x₁.and x₂).image = Fin.append x₁.image x₂.image := by
  funext i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · simp only [image, equations_and_left, Fin.append_left]
    exact elem_and_left x₁ x₂ _ (h₁ i).1
  · simp only [image, equations_and_right, LinearEquation.shift, Fin.append_right]
    exact elem_and_right x₁ x₂ _

/-- A concatenated witness is a witness for an AND composition exactly when its
parts are witnesses for the parts. -/
theorem holds_and_iff (h₁ : x₁.IndexValid) (w₁ : Fin n₁ → gp.Scalar)
    (w₂ : Fin n₂ → gp.Scalar) :
    (x₁.and x₂).Holds (Fin.append w₁ w₂) ↔ x₁.Holds w₁ ∧ x₂.Holds w₂ := by
  unfold Holds
  rw [map_and h₁, image_and h₁]
  exact ⟨fun h => ⟨funext fun i => by simpa using congrFun h (Fin.castAdd _ i),
    funext fun i => by simpa using congrFun h (Fin.natAdd _ i)⟩, fun h => by rw [h.1, h.2]⟩

/-- The AND composition of relations whose indices are in range has its indices in
range. -/
theorem indexValid_and (h₁ : x₁.IndexValid) (h₂ : x₂.IndexValid) : (x₁.and x₂).IndexValid := by
  have hlen : (x₁.and x₂).elements.length = x₁.elements.length + x₂.elements.length :=
    List.length_append
  intro i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · rw [equations_and_left]
    obtain ⟨hl, ht⟩ := h₁ i
    refine ⟨by omega, fun t h => ?_⟩
    obtain ⟨a, b⟩ := ht t h
    omega
  · rw [equations_and_right]
    obtain ⟨hl, ht⟩ := h₂ i
    refine ⟨by simp only [LinearEquation.shift]; omega, fun t h => ?_⟩
    simp only [LinearEquation.shift, List.mem_map] at h
    obtain ⟨t', ht', rfl⟩ := h
    obtain ⟨a, b⟩ := ht t' ht'
    exact ⟨by omega, by omega⟩

/-- A column entry of an AND composition in a row of `x₁` is the entry of `x₁`. -/
theorem column_and_left (h₁ : x₁.IndexValid) (j : ℕ) (i : Fin m₁) :
    (x₁.and x₂).column j (Fin.castAdd m₂ i) = x₁.column j i := by
  simp only [column, equations_and_left]
  congr 1
  refine List.map_congr_left fun t ht => ?_
  exact elem_and_left x₁ x₂ _ ((h₁ i).2 t (List.mem_of_mem_filter ht)).2

/-- A column entry of an AND composition in column `j + n₁` and a row of `x₂` is the
entry of `x₂` in column `j`. -/
theorem column_and_right (j : ℕ) (i : Fin m₂) :
    (x₁.and x₂).column (j + n₁) (Fin.natAdd m₁ i) = x₂.column j i := by
  simp only [column, equations_and_right, LinearEquation.shift, List.filter_map, List.map_map]
  congr 1
  simp only [Function.comp_def, elem_and_right]
  congr 1
  exact List.filter_congr fun t _ => by simp

/-- The AND composition of valid relations is valid when the generator of `x₂`, its
element `0`, occurs in an equation of `x₂`. -/
theorem validateInstance_and (h₁ : x₁.ValidateInstance) (h₂ : x₂.ValidateInstance)
    (h₂g : ∃ i, (x₂.equations i).lhs = 0 ∨ ∃ t ∈ (x₂.equations i).terms, t.2 = 0) :
    (x₁.and x₂).ValidateInstance where
  equations_pos := by have := h₁.equations_pos; omega
  terms_ne_nil i := by
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [equations_and_left]; exact h₁.terms_ne_nil i
    · rw [equations_and_right]
      simpa [LinearEquation.shift] using h₂.terms_ne_nil i
  indexValid := indexValid_and h₁.indexValid h₂.indexValid
  element_used k hk hk0 := by
    simp only [and, List.length_append] at hk
    by_cases hk1 : k < x₁.elements.length
    · obtain ⟨i, hi⟩ := h₁.element_used k hk1 hk0
      exact ⟨Fin.castAdd m₂ i, by rw [equations_and_left]; exact hi⟩
    · obtain ⟨k', rfl⟩ : ∃ k', k = k' + x₁.elements.length := ⟨k - x₁.elements.length, by omega⟩
      obtain ⟨i, hi⟩ : ∃ i, (x₂.equations i).lhs = k' ∨ ∃ t ∈ (x₂.equations i).terms, t.2 = k' := by
        by_cases hk' : k' = 0
        · exact hk' ▸ h₂g
        · exact h₂.element_used k' (by omega) hk'
      refine ⟨Fin.natAdd m₁ i, ?_⟩
      rw [equations_and_right]
      simp only [LinearEquation.shift, List.mem_map]
      rcases hi with hi | ⟨t, ht, hte⟩
      · exact Or.inl (by omega)
      · exact Or.inr ⟨_, ⟨t, ht, rfl⟩, by simp [hte]⟩
  scalar_used j hj := by
    by_cases hj1 : j < n₁
    · obtain ⟨i, hi⟩ := h₁.scalar_used j hj1
      exact ⟨Fin.castAdd m₂ i, by rw [equations_and_left]; exact hi⟩
    · obtain ⟨i, t, ht, hte⟩ := h₂.scalar_used (j - n₁) (by omega)
      refine ⟨Fin.natAdd m₁ i, ?_⟩
      rw [equations_and_right]
      simp only [LinearEquation.shift, List.mem_map]
      exact ⟨_, ⟨t, ht, rfl⟩, by simp only; omega⟩
  head_generator := by
    have h := h₁.head_generator
    cases hx : x₁.elements with
    | nil => simp [hx] at h
    | cons a l => simp_all [and]
  elements_ne_identity g hg := by
    simp only [and, List.mem_append] at hg
    rcases hg with hg | hg
    exacts [h₁.elements_ne_identity g hg, h₂.elements_ne_identity g hg]
  image_ne_identity i := by
    rw [image_and h₁.indexValid]
    refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [Fin.append_left]; exact h₁.image_ne_identity i
    · rw [Fin.append_right]; exact h₂.image_ne_identity i
  column_ne_identity j hj := by
    by_cases hj1 : j < n₁
    · obtain ⟨i, hi⟩ := h₁.column_ne_identity j hj1
      exact ⟨Fin.castAdd m₂ i, by rw [column_and_left h₁.indexValid]; exact hi⟩
    · obtain ⟨i, hi⟩ := h₂.column_ne_identity (j - n₁) (by omega)
      refine ⟨Fin.natAdd m₁ i, ?_⟩
      have e : j = (j - n₁) + n₁ := by omega
      rw [e, column_and_right]
      exact hi

/-- The map of an AND composition of relations with injective maps is injective. -/
theorem map_and_injective (h₁ : x₁.IndexValid) (hi₁ : Function.Injective x₁.map)
    (hi₂ : Function.Injective x₂.map) : Function.Injective (x₁.and x₂).map := by
  intro w w' h
  have hw := Fin.append_castAdd_natAdd (f := w)
  have hw' := Fin.append_castAdd_natAdd (f := w')
  rw [← hw, ← hw', map_and h₁, map_and h₁] at h
  have e₁ := hi₁ (funext fun i => by simpa using congrFun h (Fin.castAdd _ i))
  have e₂ := hi₂ (funext fun i => by simpa using congrFun h (Fin.natAdd _ i))
  rw [← hw, ← hw', e₁, e₂]

end LinearRelation

/-! ## Instances -/

section Instances

variable (gp : GroupParam)

/-- The discrete-logarithm relation `pk = g^w₀`: elements `[g, pk]`. -/
def dlogRelation (pk : gp.G) : LinearRelation gp 1 1 :=
  ⟨[gp.generator, pk], fun _ => ⟨1, [(0, 0)]⟩⟩

/-- The DLEQ (Chaum–Pedersen) relation `u = g^w₀ ∧ v = h^w₀`: elements `[g, h, u, v]`. -/
def dleqRelation (h u v : gp.G) : LinearRelation gp 1 2 :=
  ⟨[gp.generator, h, u, v], ![⟨2, [(0, 0)]⟩, ⟨3, [(0, 1)]⟩]⟩

/-- The Pedersen opening relation `C = g^w₀ · h^w₁`: elements `[g, h, C]`. -/
def pedersenRelation (h C : gp.G) : LinearRelation gp 2 1 :=
  ⟨[gp.generator, h, C], fun _ => ⟨2, [(0, 0), (1, 1)]⟩⟩

/-- The representation (Okamoto) relation `y = ∏ⱼ gⱼ^wⱼ`: elements `[g₀, …, g_{k−1}, y]`. -/
def representationRelation {k : ℕ} (gs : Fin k → gp.G) (y : gp.G) : LinearRelation gp k 1 :=
  ⟨List.ofFn gs ++ [y], fun _ => ⟨k, List.ofFn fun j : Fin k => (j.val, j.val)⟩⟩

/-- The ElGamal plaintext-knowledge relation for the ciphertext `(C₁, C₂)` under `pk`,
plaintext exponent `w₀` and randomness `w₁`: `C₁ = g^w₁ ∧ C₂ = g^w₀ · pk^w₁`; elements
`[g, pk, C₁, C₂]`. -/
def elgamalRelation (pk C₁ C₂ : gp.G) : LinearRelation gp 2 2 :=
  ⟨[gp.generator, pk, C₁, C₂], ![⟨2, [(1, 0)]⟩, ⟨3, [(0, 0), (1, 1)]⟩]⟩

variable {gp}

attribute [local instance] GroupParam.scalarCommRing

theorem dlogRelation_holds_iff (pk : gp.G) (w : Fin 1 → gp.Scalar) :
    (dlogRelation gp pk).Holds w ↔ gp.exp (w 0) = pk := by
  simp [LinearRelation.Holds, funext_iff, LinearRelation.map, LinearRelation.image,
    LinearRelation.elem, dlogRelation, vecGet, gp.groupMul_identity, gp.groupExp_generator]

theorem dleqRelation_holds_iff (h u v : gp.G) (w : Fin 1 → gp.Scalar) :
    (dleqRelation gp h u v).Holds w ↔ gp.exp (w 0) = u ∧ gp.groupExp h (w 0) = v := by
  simp [LinearRelation.Holds, funext_iff, Fin.forall_fin_two, LinearRelation.map,
    LinearRelation.image, LinearRelation.elem, dleqRelation, vecGet, gp.groupMul_identity,
    gp.groupExp_generator]

theorem pedersenRelation_holds_iff (h C : gp.G) (w : Fin 2 → gp.Scalar) :
    (pedersenRelation gp h C).Holds w ↔ gp.groupMul (gp.exp (w 0)) (gp.groupExp h (w 1)) = C := by
  simp [LinearRelation.Holds, funext_iff, LinearRelation.map, LinearRelation.image,
    LinearRelation.elem, pedersenRelation, vecGet, gp.groupMul_identity, gp.groupExp_generator]

theorem representationRelation_holds_iff {k : ℕ} (gs : Fin k → gp.G) (y : gp.G)
    (w : Fin k → gp.Scalar) :
    (representationRelation gp gs y).Holds w ↔
      (List.ofFn fun j => gp.groupExp (gs j) (w j)).foldr gp.groupMul gp.identity = y := by
  simp [LinearRelation.Holds, funext_iff, LinearRelation.map, LinearRelation.image,
    LinearRelation.elem, representationRelation, vecGet, List.map_ofFn, Function.comp_def,
    List.getD_eq_getElem?_getD]

theorem elgamalRelation_holds_iff (pk C₁ C₂ : gp.G) (w : Fin 2 → gp.Scalar) :
    (elgamalRelation gp pk C₁ C₂).Holds w ↔
      gp.exp (w 1) = C₁ ∧ gp.groupMul (gp.exp (w 0)) (gp.groupExp pk (w 1)) = C₂ := by
  simp [LinearRelation.Holds, funext_iff, Fin.forall_fin_two, LinearRelation.map,
    LinearRelation.image, LinearRelation.elem, elgamalRelation, vecGet, gp.groupMul_identity,
    gp.groupExp_generator]

theorem dlogRelation_map_injective (pk : gp.G) : Function.Injective (dlogRelation gp pk).map := by
  intro w w' h
  have h0 := congrFun h 0
  simp [LinearRelation.map, LinearRelation.elem, dlogRelation, vecGet, gp.groupMul_identity,
    ← gp.groupExp_generator] at h0
  funext j
  fin_cases j
  exact gp.exp_inj _ _ h0

theorem dleqRelation_map_injective (h u v : gp.G) :
    Function.Injective (dleqRelation gp h u v).map := by
  intro w w' hw
  have h0 := congrFun hw 0
  simp [LinearRelation.map, LinearRelation.elem, dleqRelation, vecGet, gp.groupMul_identity,
    ← gp.groupExp_generator] at h0
  funext j
  fin_cases j
  exact gp.exp_inj _ _ h0

theorem elgamalRelation_map_injective (pk C₁ C₂ : gp.G) :
    Function.Injective (elgamalRelation gp pk C₁ C₂).map := by
  intro w w' h
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  simp [LinearRelation.map, LinearRelation.elem, elgamalRelation, vecGet, gp.groupMul_identity,
    ← gp.groupExp_generator] at h0 h1
  have e1 := gp.exp_inj _ _ h0
  rw [e1, GroupParam.groupMul_eq_exp, GroupParam.groupMul_eq_exp, GroupParam.exp_inj_iff,
    GroupParam.dlog_exp, GroupParam.dlog_exp, GroupParam.scalarAdd_eq_add,
    GroupParam.scalarAdd_eq_add] at h1
  have e0 := add_right_cancel h1
  funext j
  fin_cases j
  exacts [e0, e1]

variable (gp)

/-- The Schnorr Σ-protocol as the linear Σ-protocol of `dlogRelation`, with uniform
key generation. -/
noncomputable def dlogSigma : Sigma :=
  linearSigma gp 1 1 (dlogRelation gp)
    ((PMF.uniformOfFintype (Fin 1 → gp.Scalar)).map fun w => (gp.exp (w 0), w))

theorem dlogSigma_complete : (dlogSigma gp).Complete := linearSigma_complete _ _

theorem dlogSigma_specialSound : (dlogSigma gp).SpecialSound := linearSigma_specialSound _ _

theorem dlogSigma_perfectHVZK : (dlogSigma gp).PerfectHVZK := by
  refine linearSigma_perfectHVZK _ _ fun s w hsw => ?_
  rw [PMF.support_map] at hsw
  obtain ⟨w', _, hw⟩ := hsw
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj hw
  exact (dlogRelation_holds_iff _ _).mpr rfl

theorem dlogSigma_uniqueResp : (dlogSigma gp).UniqueResp :=
  linearSigma_uniqueResp _ _ dlogRelation_map_injective

variable {gp} in
/-- The linear map of `dlogRelation gp pk` is `w ↦ g^w₀`. -/
theorem dlogRelation_map (pk : gp.G) (w : Fin 1 → gp.Scalar) :
    (dlogRelation gp pk).map w = fun _ => gp.exp (w 0) := by
  funext i
  simp [LinearRelation.map, LinearRelation.elem, dlogRelation, vecGet, gp.groupMul_identity,
    gp.groupExp_generator]

variable {gp} in
/-- On constant vectors, the verifier of `dlogSigma` is the Schnorr verification
equation `g^z = a · pk^e`. -/
theorem dlogSigma_verify_iff (pk a : gp.G) (e z : gp.Scalar) :
    (dlogSigma gp).verify pk (fun _ => a) e (fun _ => z) = true ↔
      gp.exp z = gp.groupMul a (gp.groupExp pk e) := by
  change decide ((dlogRelation gp pk).map (fun _ => z) =
    fun i => gp.groupMul a (gp.groupExp ((dlogRelation gp pk).image i) e)) = true ↔ _
  rw [dlogRelation_map, decide_eq_true_iff]
  simp [funext_iff, LinearRelation.image, LinearRelation.elem, dlogRelation]

/-- The DLEQ (Chaum–Pedersen) Σ-protocol on statements `(h, u, v)`. -/
noncomputable def dleqSigma (gen : PMF ((gp.G × gp.G × gp.G) × (Fin 1 → gp.Scalar))) : Sigma :=
  linearSigma gp 1 2 (fun s => dleqRelation gp s.1 s.2.1 s.2.2) gen

theorem dleqSigma_uniqueResp (gen : PMF ((gp.G × gp.G × gp.G) × (Fin 1 → gp.Scalar))) :
    (dleqSigma gp gen).UniqueResp :=
  linearSigma_uniqueResp _ _ fun s => dleqRelation_map_injective s.1 s.2.1 s.2.2

/-- The ElGamal plaintext-knowledge Σ-protocol on statements `(pk, C₁, C₂)`. -/
noncomputable def elgamalSigma (gen : PMF ((gp.G × gp.G × gp.G) × (Fin 2 → gp.Scalar))) :
    Sigma :=
  linearSigma gp 2 2 (fun s => elgamalRelation gp s.1 s.2.1 s.2.2) gen

theorem elgamalSigma_uniqueResp (gen : PMF ((gp.G × gp.G × gp.G) × (Fin 2 → gp.Scalar))) :
    (elgamalSigma gp gen).UniqueResp :=
  linearSigma_uniqueResp _ _ fun s => elgamalRelation_map_injective s.1 s.2.1 s.2.2

/-- The Pedersen-opening Σ-protocol on statements `(h, C)`. -/
noncomputable def pedersenSigma (gen : PMF ((gp.G × gp.G) × (Fin 2 → gp.Scalar))) : Sigma :=
  linearSigma gp 2 1 (fun s => pedersenRelation gp s.1 s.2) gen

/-- The representation (Okamoto) Σ-protocol on statements `(g₀, …, g_{k−1}, y)`. -/
noncomputable def representationSigma {k : ℕ}
    (gen : PMF (((Fin k → gp.G) × gp.G) × (Fin k → gp.Scalar))) : Sigma :=
  linearSigma gp k 1 (fun s => representationRelation gp s.1 s.2) gen

end Instances

end CatCrypt.Crypto.FiatShamirROM
