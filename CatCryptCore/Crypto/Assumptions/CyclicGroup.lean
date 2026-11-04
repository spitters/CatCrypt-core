/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Advantage
public import CatCryptCore.Crypto.CryptoWord

/-!
# Shared Cyclic Group Abstraction

Unified `CyclicGroupDef` structure used by ElGamal, Schnorr, Pedersen, SimplestOT,
OPRF, OVN, FROST, and other DH-based protocols.

## Design

Individual group/ring operations are stored as fields. Notation instances are
declared immediately, and all axioms use standard notation (`*`, `+`, `⁻¹`, `-`).
`CommGroup` and `CommRing` instances are derived, with `⁻¹` definitionally
equal to `ginv` (not `zpow (-1)`).
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal

namespace CatCrypt.Crypto

/-- A prime-order cyclic group with generator. -/
structure CyclicGroupDef where
  G : Type
  S : Type
  -- Group operations (notation via instances below)
  gmul : G → G → G
  gone : G
  ginv : G → G
  -- Scalar operations
  sadd : S → S → S
  smul : S → S → S
  sneg : S → S
  szero : S
  sone : S
  -- Finiteness / decidability / sampling
  [finG : Fintype G]
  [finS : Fintype S]
  [neG : Nonempty G]
  [neS : Nonempty S]
  [decG : DecidableEq G]
  [decS : DecidableEq S]
  [sampleG : SampleableType G]
  [sampleS : SampleableType S]
  -- Generator and exponentiation
  gen : G
  exp : S → G
  groupExp : G → S → G
  -- Group axioms (stated with raw ops; `CommGroup` instance proves notation form)
  gmul_assoc : ∀ a b c, gmul (gmul a b) c = gmul a (gmul b c)
  gmul_comm : ∀ a b, gmul a b = gmul b a
  gone_gmul : ∀ a, gmul gone a = a
  gmul_ginv : ∀ a, gmul a (ginv a) = gone
  -- Scalar axioms
  sadd_assoc : ∀ a b c, sadd (sadd a b) c = sadd a (sadd b c)
  sadd_comm : ∀ a b, sadd a b = sadd b a
  szero_sadd : ∀ a, sadd szero a = a
  sadd_sneg : ∀ a, sadd a (sneg a) = szero
  smul_assoc : ∀ a b c, smul (smul a b) c = smul a (smul b c)
  smul_comm : ∀ a b, smul a b = smul b a
  sone_smul : ∀ a, smul sone a = a
  szero_smul : ∀ a, smul szero a = szero
  sadd_smul : ∀ a b c, smul (sadd a b) c = sadd (smul a c) (smul b c)
  -- Exponentiation axioms
  exp_add : ∀ a b, exp (sadd a b) = gmul (exp a) (exp b)
  exp_zero : exp szero = gone
  exp_bijective : Function.Bijective exp
  groupExp_gen : ∀ a, exp a = groupExp gen a
  groupExp_mul : ∀ w e, groupExp (exp w) e = exp (smul w e)
  groupExp_add : ∀ h a b, groupExp h (sadd a b) = gmul (groupExp h a) (groupExp h b)
  groupExp_one : ∀ h, groupExp h sone = h
  groupExp_zero : ∀ h, groupExp h szero = gone

attribute [instance] CyclicGroupDef.finG CyclicGroupDef.finS
  CyclicGroupDef.neG CyclicGroupDef.neS
  CyclicGroupDef.decG CyclicGroupDef.decS
  CyclicGroupDef.sampleG CyclicGroupDef.sampleS

namespace CyclicGroupDef

variable (cg : CyclicGroupDef)

/-! ## Notation instances -/

instance : Mul cg.G := ⟨cg.gmul⟩
instance : One cg.G := ⟨cg.gone⟩
instance : Inv cg.G := ⟨cg.ginv⟩
instance : Add cg.S := ⟨cg.sadd⟩
instance : Mul cg.S := ⟨cg.smul⟩
instance : Neg cg.S := ⟨cg.sneg⟩
instance : Zero cg.S := ⟨cg.szero⟩
instance : One cg.S := ⟨cg.sone⟩

/-! ## CommGroup instance on G -/

-- Helper: mul_one from comm + one_mul
theorem gmul_gone' (a : cg.G) : cg.gmul a cg.gone = a := by
  rw [cg.gmul_comm]; exact cg.gone_gmul a
theorem ginv_gmul (a : cg.G) : cg.gmul (cg.ginv a) a = cg.gone := by
  rw [cg.gmul_comm]; exact cg.gmul_ginv a

instance instCommGroupG : CommGroup cg.G where
  mul_assoc := cg.gmul_assoc
  mul_comm := cg.gmul_comm
  one_mul := cg.gone_gmul
  mul_one := cg.gmul_gone'
  inv_mul_cancel := cg.ginv_gmul

/-! ## CommRing instance on S -/

-- Helpers for CommRing
theorem sadd_szero' (a : cg.S) : cg.sadd a cg.szero = a := by
  rw [cg.sadd_comm]; exact cg.szero_sadd a
theorem sneg_sadd (a : cg.S) : cg.sadd (cg.sneg a) a = cg.szero := by
  rw [cg.sadd_comm]; exact cg.sadd_sneg a
theorem smul_sone' (a : cg.S) : cg.smul a cg.sone = a := by
  rw [cg.smul_comm]; exact cg.sone_smul a
theorem smul_szero' (a : cg.S) : cg.smul a cg.szero = cg.szero := by
  rw [cg.smul_comm]; exact cg.szero_smul a
theorem smul_sadd (a b c : cg.S) :
    cg.smul a (cg.sadd b c) = cg.sadd (cg.smul a b) (cg.smul a c) := by
  rw [cg.smul_comm, cg.sadd_smul, cg.smul_comm b, cg.smul_comm c]

instance instCommRingS : CommRing cg.S where
  add_assoc := cg.sadd_assoc
  add_comm := cg.sadd_comm
  zero_add := cg.szero_sadd
  add_zero := cg.sadd_szero'
  neg_add_cancel := cg.sneg_sadd
  mul_assoc := cg.smul_assoc
  mul_comm := cg.smul_comm
  one_mul := cg.sone_smul
  mul_one := cg.smul_sone'
  zero_mul := cg.szero_smul
  mul_zero := cg.smul_szero'
  left_distrib := cg.smul_sadd
  right_distrib := cg.sadd_smul
  nsmul := nsmulRec
  zsmul := zsmulRec

/-! ## Normalization lemmas

These bridge the gap between raw field accessors (`cg.smul`, `cg.sadd`)
and notation (`*`, `+`). Without them, `ring`/`group` can't close goals
that mix raw and notation forms. -/

@[simp] theorem smul_eq_mul (a b : cg.S) : cg.smul a b = a * b := rfl
@[simp] theorem sadd_eq_add (a b : cg.S) : cg.sadd a b = a + b := rfl
@[simp] theorem sneg_eq_neg (a : cg.S) : cg.sneg a = -a := rfl
@[simp] theorem szero_eq_zero : cg.szero = (0 : cg.S) := rfl
@[simp] theorem sone_eq_one : cg.sone = (1 : cg.S) := rfl
@[simp] theorem gmul_eq_mul (a b : cg.G) : cg.gmul a b = a * b := rfl
@[simp] theorem gone_eq_one : cg.gone = (1 : cg.G) := rfl
@[simp] theorem ginv_eq_inv (a : cg.G) : cg.ginv a = a⁻¹ := rfl

/-! ## Exponentiation simp lemmas -/

@[simp] theorem exp_add' (a b : cg.S) :
    cg.exp (a + b) = cg.exp a * cg.exp b :=
  cg.exp_add a b

@[simp] theorem exp_zero' : cg.exp (0 : cg.S) = (1 : cg.G) :=
  cg.exp_zero

@[simp] theorem exp_neg (a : cg.S) :
    cg.exp (-a) = (cg.exp a)⁻¹ := by
  have h : cg.exp a * cg.exp (-a) = 1 := by
    rw [← cg.exp_add', add_neg_cancel, cg.exp_zero']
  exact (inv_eq_of_mul_eq_one_right h).symm

theorem exp_injective : Function.Injective cg.exp := cg.exp_bijective.1
theorem exp_surjective : Function.Surjective cg.exp := cg.exp_bijective.2

/-- The equivalence between scalars and group elements. -/
noncomputable def expEquiv : cg.S ≃ cg.G :=
  Equiv.ofBijective cg.exp cg.exp_bijective

/-! ## exp_simp tactic

Normalizes `cg.exp` arguments using `ring`, analogous to EasyCrypt's `algebra`.
Handles: `groupExp_mul`, `exp_add'`, `exp_zero'`, `exp_neg`, raw field normalization.
Then tries `ring` on remaining scalar goals and `group` on group goals. -/

/-- Simp set for normalizing exponentiation. -/
@[simp] theorem groupExp_mul' (w e : cg.S) :
    cg.groupExp (cg.exp w) e = cg.exp (w * e) :=
  cg.groupExp_mul w e

@[simp] theorem groupExp_add' (h : cg.G) (a b : cg.S) :
    cg.groupExp h (a + b) = cg.groupExp h a * cg.groupExp h b :=
  cg.groupExp_add h a b

@[simp] theorem groupExp_one' (h : cg.G) : cg.groupExp h 1 = h :=
  cg.groupExp_one h

@[simp] theorem groupExp_zero' (h : cg.G) : cg.groupExp h 0 = (1 : cg.G) :=
  cg.groupExp_zero h

/-! ## DDH Games -/

noncomputable def DDH_real : SPComp (cg.G × cg.G × cg.G) :=
  SPComp.bind (SPComp.sample cg.S) fun a =>
  SPComp.bind (SPComp.sample cg.S) fun b =>
  SPComp.pure (cg.exp a, cg.exp b, cg.exp (a * b))

noncomputable def DDH_ideal : SPComp (cg.G × cg.G × cg.G) :=
  SPComp.bind (SPComp.sample cg.S) fun a =>
  SPComp.bind (SPComp.sample cg.S) fun b =>
  SPComp.bind (SPComp.sample cg.S) fun c =>
  SPComp.pure (cg.exp a, cg.exp b, cg.exp c)

noncomputable def DDH_Advantage (D : cg.G × cg.G × cg.G → SPComp Bool) : ℝ≥0∞ :=
  AdvantageA cg.DDH_real cg.DDH_ideal D

end CyclicGroupDef

end CatCrypt.Crypto
