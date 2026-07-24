/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Examples.SigmaProtocol
import CatCryptCore.Examples.GroupParam
import CatCryptCore.Crypto.UC

/-!
# Chaum-Pedersen Protocol: Equality of Discrete Logarithms

The Chaum-Pedersen protocol is a Sigma protocol for proving equality of discrete
logarithms. Given generators `g` and `h` of a cyclic group of prime order,
the prover demonstrates knowledge of `x` such that `u = g^x` AND `v = h^x`,
thereby proving that `u` and `v` share the same discrete logarithm with respect
to `g` and `h` respectively, without revealing the exponent.

## Protocol

- **Statement**: `(g, h, u, v)` where `u = groupExp g x` and `v = groupExp h x`
- **Witness**: `x` (the common exponent)
- **Relation**: `R((g,h,u,v), x) <=> u = groupExp g x /\ v = groupExp h x`
- **Commit**: Sample random `r`, send `(a1, a2) = (groupExp g r, groupExp h r)`
- **Challenge**: Random scalar `e`
- **Response**: `z = r + e*x`
- **Verify**: `groupExp g z = groupMul a1 (groupExp u e)` AND
              `groupExp h z = groupMul a2 (groupExp v e)`
- **Simulate**: Sample `z`, compute
              `a1 = groupMul (groupExp g z) (groupInv (groupExp u e))`,
              `a2 = groupMul (groupExp h z) (groupInv (groupExp v e))`
- **Extract**: From two transcripts `(a, e, z)` and `(a, e', z')`,
              extract `x = (z-z')/(e-e')`

## Security properties

* `chaumPedersen_complete` -- completeness
* `chaumPedersen_SHVZK_visible` -- special honest-verifier zero-knowledge (given challenge)
* `chaumPedersen_special_soundness` -- special soundness (witness extraction)
* `chaumPedersen_uc_secure` -- UC security at eps = 0

## References

* [Chaum & Pedersen, Wallet Databases with Observers, CRYPTO 1992]
* [Damgard, On Sigma Protocols]
-/

set_option autoImplicit false

namespace CatCryptCore.Examples.ChaumPedersen

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Examples.SigmaProtocol
open CatCrypt.Examples
open CatCrypt.Relational
open scoped ENNReal

/-! ## Chaum-Pedersen Protocol Types -/

variable (gp : GroupParam)

/-- Chaum-Pedersen statement: `(g, h, u, v)`. -/
abbrev CPStatement := gp.G × gp.G × gp.G × gp.G

/-- Chaum-Pedersen witness: the common exponent `x`. -/
abbrev CPWitness := gp.Scalar

/-- Chaum-Pedersen commitment message: `(r, groupExp g r, groupExp h r)`. -/
abbrev CPMessage := gp.Scalar × gp.G × gp.G

/-- Chaum-Pedersen challenge: a random scalar. -/
abbrev CPChallenge := gp.Scalar

/-- Chaum-Pedersen response: `z = r + e*x`. -/
abbrev CPResponse := gp.Scalar

/-! ## Chaum-Pedersen Relation -/

/-- The equality-of-discrete-logs relation:
    `R((g, h, u, v), x) <=> u = groupExp g x /\ v = groupExp h x`. -/
def cpRelation (stmt : CPStatement gp) (w : CPWitness gp) : Prop :=
  stmt.2.2.1 = gp.groupExp stmt.1 w ∧ stmt.2.2.2 = gp.groupExp stmt.2.1 w

/-! ## Chaum-Pedersen Protocol Algorithms -/

/-- Chaum-Pedersen commitment: sample random `r`, return `(r, groupExp g r, groupExp h r)`. -/
noncomputable def cpCommit (stmt : CPStatement gp) (_w : CPWitness gp) :
    SPComp (CPMessage gp) := do
  let r ← SPComp.sample gp.Scalar
  SPComp.pure (r, gp.groupExp stmt.1 r, gp.groupExp stmt.2.1 r)

/-- Chaum-Pedersen response: compute `z = r + e*x`. -/
noncomputable def cpRespond (_stmt : CPStatement gp) (w : CPWitness gp)
    (msg : CPMessage gp) (e : CPChallenge gp) : SPComp (CPResponse gp) :=
  SPComp.pure (gp.scalarAdd msg.1 (gp.scalarMul e w))

/-- Chaum-Pedersen verification. -/
def cpVerify (stmt : CPStatement gp) (msg : CPMessage gp)
    (e : CPChallenge gp) (z : CPResponse gp) : Bool :=
  (gp.groupExp stmt.1 z == gp.groupMul msg.2.1 (gp.groupExp stmt.2.2.1 e)) &&
  (gp.groupExp stmt.2.1 z == gp.groupMul msg.2.2 (gp.groupExp stmt.2.2.2 e))

/-- Chaum-Pedersen simulator. -/
noncomputable def cpSimulate (stmt : CPStatement gp) (e : CPChallenge gp) :
    SPComp (CPMessage gp × CPResponse gp) := do
  let z ← SPComp.sample gp.Scalar
  let a1 := gp.groupMul (gp.groupExp stmt.1 z) (gp.groupInv (gp.groupExp stmt.2.2.1 e))
  let a2 := gp.groupMul (gp.groupExp stmt.2.1 z) (gp.groupInv (gp.groupExp stmt.2.2.2 e))
  SPComp.pure ((z, a1, a2), z)

/-- Chaum-Pedersen extractor. -/
def cpExtractor (_stmt : CPStatement gp) (_msg : CPMessage gp)
    (e : CPChallenge gp) (e' : CPChallenge gp)
    (z : CPResponse gp) (z' : CPResponse gp) : Option (CPWitness gp) :=
  if e == e' then none
  else some (gp.scalarDiv (gp.scalarSub z z') (gp.scalarSub e e'))

/-! ## Sigma Protocol Instance -/

/-- Chaum-Pedersen identification as a Sigma protocol. -/
noncomputable def chaumPedersenSigma : SigmaProtocol where
  Statement := CPStatement gp
  Witness := CPWitness gp
  Message := CPMessage gp
  Challenge := CPChallenge gp
  Response := CPResponse gp
  finChallenge := gp.finScalar
  neChallenge := gp.neScalar
  relation := cpRelation gp
  commit := cpCommit gp
  respond := cpRespond gp
  verify := cpVerify gp
  simulate := cpSimulate gp

/-! ## Visible Transcript Equality -/

/-- Visible transcript equality for Chaum-Pedersen: compares only the externally
    visible parts `(a1, a2, e, z)`, excluding the internal randomness `r`. -/
def cpVisibleTranscriptEq (t₁ t₂ : Transcript (chaumPedersenSigma gp)) : Prop :=
  t₁.message.2.1 = t₂.message.2.1 ∧
  t₁.message.2.2 = t₂.message.2.2 ∧
  t₁.challenge = t₂.challenge ∧
  t₁.response = t₂.response

/-! ## Helper lemmas -/

/-- groupExp distributes: `groupExp g (scalarAdd a b) = groupMul (groupExp g a) (groupExp g b)`. -/
private theorem groupExp_add_gen (g : gp.G) (a b : gp.Scalar) :
    gp.groupExp g (gp.scalarAdd a b) = gp.groupMul (gp.groupExp g a) (gp.groupExp g b) :=
  gp.groupExp_add g a b

/-- groupInv of groupExp: `groupInv (groupExp g e) = groupExp g (scalarNeg e)`. -/
private theorem groupInv_groupExp_gen (g : gp.G) (e : gp.Scalar) :
    gp.groupInv (gp.groupExp g e) = gp.groupExp g (gp.scalarNeg e) :=
  gp.groupInv_groupExp g e

/-- groupExp composed: `groupExp (groupExp g w) e = groupExp g (scalarMul w e)`.
    Proved via `exp_surj` + `groupExp_exp` + `scalarMul_assoc`. -/
private theorem groupExp_groupExp_gen (g : gp.G) (w e : gp.Scalar) :
    gp.groupExp (gp.groupExp g w) e = gp.groupExp g (gp.scalarMul w e) := by
  obtain ⟨k, hk⟩ := gp.exp_surj g
  rw [← hk, gp.groupExp_exp, gp.groupExp_exp, gp.groupExp_exp]
  congr 1
  exact gp.scalarMul_assoc k w e

/-! ## Completeness -/

/-- Completeness for Chaum-Pedersen: honest execution always verifies. -/
theorem chaumPedersen_complete (stmt : CPStatement gp) (w : CPWitness gp)
    (hrel : cpRelation gp stmt w) (r : gp.Scalar) (e : CPChallenge gp) :
    let msg : CPMessage gp := (r, gp.groupExp stmt.1 r, gp.groupExp stmt.2.1 r)
    let z := gp.scalarAdd r (gp.scalarMul e w)
    cpVerify gp stmt msg e z = true := by
  simp only [cpVerify]
  obtain ⟨hu, hv⟩ := hrel
  apply Bool.and_eq_true_iff.mpr
  constructor
  · rw [beq_eq_decide, decide_eq_true_eq]
    rw [hu, groupExp_add_gen]
    congr 1; rw [gp.scalarMul_comm]; exact (groupExp_groupExp_gen gp stmt.1 w e).symm
  · rw [beq_eq_decide, decide_eq_true_eq]
    rw [hv, groupExp_add_gen]
    congr 1; rw [gp.scalarMul_comm]; exact (groupExp_groupExp_gen gp stmt.2.1 w e).symm

/-! ## Commitment recovery lemma -/

/-- The key algebraic identity: `groupExp g r = groupMul (groupExp g z) (groupInv (groupExp u e))`
    when `u = groupExp g w` and `z = r + e*w`. -/
private theorem commitment_recovery (g : gp.G) (u : gp.G) (w r z e : gp.Scalar)
    (hu : u = gp.groupExp g w) (hz : z = gp.scalarAdd r (gp.scalarMul e w)) :
    gp.groupExp g r =
    gp.groupMul (gp.groupExp g z) (gp.groupInv (gp.groupExp u e)) := by
  rw [hu, groupExp_groupExp_gen, groupInv_groupExp_gen gp g]
  rw [← groupExp_add_gen]
  rw [hz]
  congr 1
  rw [gp.scalarMul_comm e w]
  rw [gp.scalarAdd_assoc, gp.scalarAdd_neg, gp.scalarAdd_zero]

/-! ## Cancellation helper for special soundness -/

/-- Cancellation: `(ka + t1) + (-ka + -t2) = t1 + (-t2)`. -/
private theorem cancel_add_neg (ka t1 t2 : gp.Scalar) :
    gp.scalarAdd (gp.scalarAdd ka t1) (gp.scalarAdd (gp.scalarNeg ka) (gp.scalarNeg t2)) =
    gp.scalarAdd t1 (gp.scalarNeg t2) := by
  calc gp.scalarAdd (gp.scalarAdd ka t1)
          (gp.scalarAdd (gp.scalarNeg ka) (gp.scalarNeg t2))
      = gp.scalarAdd ka (gp.scalarAdd t1
          (gp.scalarAdd (gp.scalarNeg ka) (gp.scalarNeg t2))) := by
        rw [gp.scalarAdd_assoc]
    _ = gp.scalarAdd ka (gp.scalarAdd (gp.scalarAdd t1 (gp.scalarNeg ka))
          (gp.scalarNeg t2)) := by
        congr 1; rw [gp.scalarAdd_assoc]
    _ = gp.scalarAdd ka (gp.scalarAdd (gp.scalarAdd (gp.scalarNeg ka) t1)
          (gp.scalarNeg t2)) := by
        congr 2; rw [gp.scalarAdd_comm]
    _ = gp.scalarAdd ka (gp.scalarAdd (gp.scalarNeg ka) (gp.scalarAdd t1
          (gp.scalarNeg t2))) := by
        congr 1; rw [gp.scalarAdd_assoc]
    _ = gp.scalarAdd (gp.scalarAdd ka (gp.scalarNeg ka)) (gp.scalarAdd t1
          (gp.scalarNeg t2)) := by
        rw [gp.scalarAdd_assoc]
    _ = gp.scalarAdd gp.scalarZero (gp.scalarAdd t1 (gp.scalarNeg t2)) := by
        rw [gp.scalarAdd_neg]
    _ = gp.scalarAdd t1 (gp.scalarNeg t2) := by
        rw [gp.scalarZero_add]

/-- Division distributes: `scalarDiv (scalarMul k x) y = scalarMul k (scalarDiv x y)`. -/
private theorem scalarMul_div (k x y : gp.Scalar) (hy : y ≠ gp.scalarZero) :
    gp.scalarDiv (gp.scalarMul k x) y = gp.scalarMul k (gp.scalarDiv x y) := by
  apply gp.exp_inj
  have hlhs : gp.scalarMul (gp.scalarDiv (gp.scalarMul k x) y) y = gp.scalarMul k x :=
    gp.div_mul_cancel _ _ hy
  have hrhs : gp.scalarMul (gp.scalarMul k (gp.scalarDiv x y)) y = gp.scalarMul k x := by
    rw [gp.scalarMul_assoc, gp.div_mul_cancel _ _ hy]
  calc gp.exp (gp.scalarDiv (gp.scalarMul k x) y)
      = gp.exp (gp.scalarDiv (gp.scalarMul (gp.scalarMul k (gp.scalarDiv x y)) y) y) := by
        rw [hrhs]
    _ = gp.exp (gp.scalarMul k (gp.scalarDiv x y)) := by
        rw [gp.mul_div_cancel _ _ hy]

/-! ## SHVZK -/

/-- SHVZK for Chaum-Pedersen (given challenge): the visible parts of real and
    simulated transcripts are identical. -/
theorem chaumPedersen_SHVZK_visible :
    ∀ stmt w e, (chaumPedersenSigma gp).relation stmt w →
    rHoare
      (fun _ _ => True)
      (realTranscript (chaumPedersenSigma gp) stmt w e)
      (simulatedTranscript (chaumPedersenSigma gp) stmt e)
      (fun t₁ _ t₂ _ => cpVisibleTranscriptEq gp t₁ t₂) := by
  intro stmt w e hrel
  intro h₁ h₂ _
  unfold realTranscript simulatedTranscript
  simp only [chaumPedersenSigma, cpCommit, cpRespond, cpSimulate]
  simp only [SPComp.monad_bind_eq]
  ssprove_distr_simp
  let bij : gp.Scalar ≃ gp.Scalar := {
    toFun := fun r => gp.scalarAdd r (gp.scalarMul e w)
    invFun := fun z => gp.scalarSub z (gp.scalarMul e w)
    left_inv := fun r => by
      show gp.scalarSub (gp.scalarAdd r (gp.scalarMul e w)) (gp.scalarMul e w) = r
      rw [gp.scalarSub_eq, gp.scalarAdd_assoc, gp.scalarAdd_neg, gp.scalarAdd_zero]
    right_inv := fun z => by
      show gp.scalarAdd (gp.scalarSub z (gp.scalarMul e w)) (gp.scalarMul e w) = z
      rw [gp.scalarSub_eq, gp.scalarAdd_assoc, gp.scalarNeg_add, gp.scalarAdd_zero]
  }
  have hBij := liftR_uniform_bij bij
  apply liftR_bind hBij
  intro r z hrz
  apply liftR_pure
  -- Goal: cpVisibleTranscriptEq gp (real transcript) (sim transcript)
  obtain ⟨hu, hv⟩ := hrel
  have hz : z = gp.scalarAdd r (gp.scalarMul e w) := hrz.symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact commitment_recovery gp stmt.1 stmt.2.2.1 w r z e hu hz
  · exact commitment_recovery gp stmt.2.1 stmt.2.2.2 w r z e hv hz
  · rfl
  · exact hrz

/-! ## Special Soundness -/

/-- Special soundness for Chaum-Pedersen. -/
theorem chaumPedersen_special_soundness : SpecialSoundness (chaumPedersenSigma gp) := by
  use fun stmt tt => cpExtractor gp stmt tt.message tt.challenge₁ tt.challenge₂
                      tt.response₁ tt.response₂ |>.getD gp.scalarZero
  intro stmt tt
  simp only [chaumPedersenSigma, cpRelation, cpExtractor]
  have hne : tt.challenge₁ ≠ tt.challenge₂ := tt.diff
  simp only [beq_eq_decide, decide_eq_true_eq]

  set w := gp.scalarDiv (gp.scalarSub tt.response₁ tt.response₂)
            (gp.scalarSub tt.challenge₁ tt.challenge₂)
  set z1 := tt.response₁
  set z2 := tt.response₂
  set e1 := tt.challenge₁
  set e2 := tt.challenge₂

  -- Extract accepting equations
  have hacc1 := tt.accept₁
  have hacc2 := tt.accept₂
  simp only [chaumPedersenSigma, cpVerify] at hacc1 hacc2
  have hacc1_split := Bool.and_eq_true_iff.mp hacc1
  have hacc2_split := Bool.and_eq_true_iff.mp hacc2
  have hacc1_g := beq_iff_eq.mp hacc1_split.1
  have hacc1_h := beq_iff_eq.mp hacc1_split.2
  have hacc2_g := beq_iff_eq.mp hacc2_split.1
  have hacc2_h := beq_iff_eq.mp hacc2_split.2

  -- Get scalar representations for all elements via exp_surj
  obtain ⟨kg, hkg⟩ := gp.exp_surj stmt.1
  obtain ⟨kh, hkh⟩ := gp.exp_surj stmt.2.1
  obtain ⟨ku, hku⟩ := gp.exp_surj stmt.2.2.1
  obtain ⟨kv, hkv⟩ := gp.exp_surj stmt.2.2.2
  obtain ⟨ka1, hka1⟩ := gp.exp_surj tt.message.2.1
  obtain ⟨ka2, hka2⟩ := gp.exp_surj tt.message.2.2

  -- groupExp in terms of exp
  have hge_g : ∀ s, gp.groupExp stmt.1 s = gp.exp (gp.scalarMul kg s) := by
    intro s; rw [← hkg]; exact gp.groupExp_exp kg s
  have hge_h : ∀ s, gp.groupExp stmt.2.1 s = gp.exp (gp.scalarMul kh s) := by
    intro s; rw [← hkh]; exact gp.groupExp_exp kh s
  have hge_u : ∀ s, gp.groupExp stmt.2.2.1 s = gp.exp (gp.scalarMul ku s) := by
    intro s; rw [← hku]; exact gp.groupExp_exp ku s
  have hge_v : ∀ s, gp.groupExp stmt.2.2.2 s = gp.exp (gp.scalarMul kv s) := by
    intro s; rw [← hkv]; exact gp.groupExp_exp kv s

  -- Rewrite accepting equations into exp form via calc
  have hinj1_g : gp.scalarMul kg z1 = gp.scalarAdd ka1 (gp.scalarMul ku e1) := by
    apply gp.exp_inj
    calc gp.exp (gp.scalarMul kg z1)
        = gp.groupExp stmt.1 z1 := (hge_g z1).symm
      _ = gp.groupMul tt.message.2.1 (gp.groupExp stmt.2.2.1 e1) := hacc1_g
      _ = gp.groupMul (gp.exp ka1) (gp.exp (gp.scalarMul ku e1)) := by
          rw [← hka1, ← hge_u]
      _ = gp.exp (gp.scalarAdd ka1 (gp.scalarMul ku e1)) := (gp.exp_add _ _).symm
  have hinj2_g : gp.scalarMul kg z2 = gp.scalarAdd ka1 (gp.scalarMul ku e2) := by
    apply gp.exp_inj
    calc gp.exp (gp.scalarMul kg z2)
        = gp.groupExp stmt.1 z2 := (hge_g z2).symm
      _ = gp.groupMul tt.message.2.1 (gp.groupExp stmt.2.2.1 e2) := hacc2_g
      _ = gp.groupMul (gp.exp ka1) (gp.exp (gp.scalarMul ku e2)) := by
          rw [← hka1, ← hge_u]
      _ = gp.exp (gp.scalarAdd ka1 (gp.scalarMul ku e2)) := (gp.exp_add _ _).symm
  have hinj1_h : gp.scalarMul kh z1 = gp.scalarAdd ka2 (gp.scalarMul kv e1) := by
    apply gp.exp_inj
    calc gp.exp (gp.scalarMul kh z1)
        = gp.groupExp stmt.2.1 z1 := (hge_h z1).symm
      _ = gp.groupMul tt.message.2.2 (gp.groupExp stmt.2.2.2 e1) := hacc1_h
      _ = gp.groupMul (gp.exp ka2) (gp.exp (gp.scalarMul kv e1)) := by
          rw [← hka2, ← hge_v]
      _ = gp.exp (gp.scalarAdd ka2 (gp.scalarMul kv e1)) := (gp.exp_add _ _).symm
  have hinj2_h : gp.scalarMul kh z2 = gp.scalarAdd ka2 (gp.scalarMul kv e2) := by
    apply gp.exp_inj
    calc gp.exp (gp.scalarMul kh z2)
        = gp.groupExp stmt.2.1 z2 := (hge_h z2).symm
      _ = gp.groupMul tt.message.2.2 (gp.groupExp stmt.2.2.2 e2) := hacc2_h
      _ = gp.groupMul (gp.exp ka2) (gp.exp (gp.scalarMul kv e2)) := by
          rw [← hka2, ← hge_v]
      _ = gp.exp (gp.scalarAdd ka2 (gp.scalarMul kv e2)) := (gp.exp_add _ _).symm

  -- Compute kg * (z1 - z2) = ku * (e1 - e2) for the g-side
  have hg_diff : gp.scalarMul kg (gp.scalarSub z1 z2) =
      gp.scalarMul ku (gp.scalarSub e1 e2) := by
    rw [gp.scalarSub_eq, gp.scalarMul_add, gp.scalarSub_eq, gp.scalarMul_add]
    rw [scalarMul_neg gp, scalarMul_neg gp, hinj1_g, hinj2_g, gp.scalarNeg_add_distrib]
    exact cancel_add_neg gp ka1 (gp.scalarMul ku e1) (gp.scalarMul ku e2)

  -- Compute kh * (z1 - z2) = kv * (e1 - e2) for the h-side
  have hh_diff : gp.scalarMul kh (gp.scalarSub z1 z2) =
      gp.scalarMul kv (gp.scalarSub e1 e2) := by
    rw [gp.scalarSub_eq, gp.scalarMul_add, gp.scalarSub_eq, gp.scalarMul_add]
    rw [scalarMul_neg gp, scalarMul_neg gp, hinj1_h, hinj2_h, gp.scalarNeg_add_distrib]
    exact cancel_add_neg gp ka2 (gp.scalarMul kv e1) (gp.scalarMul kv e2)

  have he_ne : gp.scalarSub e1 e2 ≠ gp.scalarZero := gp.scalarSub_ne_zero e1 e2 hne

  -- Extract ku = kg * w via mul_div_cancel
  have hku_eq : ku = gp.scalarMul kg w := by
    apply gp.exp_inj
    calc gp.exp ku
        = gp.exp (gp.scalarDiv (gp.scalarMul ku (gp.scalarSub e1 e2))
            (gp.scalarSub e1 e2)) := by rw [gp.mul_div_cancel _ _ he_ne]
      _ = gp.exp (gp.scalarDiv (gp.scalarMul kg (gp.scalarSub z1 z2))
            (gp.scalarSub e1 e2)) := by rw [← hg_diff]
      _ = gp.exp (gp.scalarMul kg (gp.scalarDiv (gp.scalarSub z1 z2)
            (gp.scalarSub e1 e2))) := by
          congr 1; exact scalarMul_div gp kg _ _ he_ne

  -- Extract kv = kh * w via mul_div_cancel
  have hkv_eq : kv = gp.scalarMul kh w := by
    apply gp.exp_inj
    calc gp.exp kv
        = gp.exp (gp.scalarDiv (gp.scalarMul kv (gp.scalarSub e1 e2))
            (gp.scalarSub e1 e2)) := by rw [gp.mul_div_cancel _ _ he_ne]
      _ = gp.exp (gp.scalarDiv (gp.scalarMul kh (gp.scalarSub z1 z2))
            (gp.scalarSub e1 e2)) := by rw [← hh_diff]
      _ = gp.exp (gp.scalarMul kh (gp.scalarDiv (gp.scalarSub z1 z2)
            (gp.scalarSub e1 e2))) := by
          congr 1; exact scalarMul_div gp kh _ _ he_ne

  refine ⟨?_, ?_⟩ <;> (split_ifs with heq; · exact absurd heq hne) <;>
    simp only [Option.getD_some]
  · -- u = groupExp g w
    rw [← hku, ← hkg, gp.groupExp_exp, hku_eq]
  · -- v = groupExp h w
    rw [← hkv, ← hkh, gp.groupExp_exp, hkv_eq]

/-! ## Visible Transcript and UC Security

The internal `CPMessage` includes the randomness `r` for threading between
`commit` and `respond`. The visible transcript (what the adversary sees) projects
out `r`, keeping only the group elements `(a1, a2)`, the challenge `e`, and
the response `z`. UC security is stated over these visible transcripts. -/

/-- Visible Chaum-Pedersen transcript: `(a1, a2, challenge, response)`. -/
abbrev CPVisibleTranscript := gp.G × gp.G × gp.Scalar × gp.Scalar

/-- Project a full transcript to its visible parts. -/
def projectTranscript (t : Transcript (chaumPedersenSigma gp)) : CPVisibleTranscript gp :=
  (t.message.2.1, t.message.2.2, t.challenge, t.response)

/-- Real visible transcript computation. -/
noncomputable def cpRealVisible (stmt : CPStatement gp) (w : CPWitness gp) :
    SPComp (CPVisibleTranscript gp) :=
  SPComp.map (projectTranscript gp) (realTranscriptSampled (chaumPedersenSigma gp) stmt w)

/-- Simulated visible transcript computation. -/
noncomputable def cpSimVisible (stmt : CPStatement gp) :
    SPComp (CPVisibleTranscript gp) :=
  SPComp.map (projectTranscript gp) (simulatedTranscriptSampled (chaumPedersenSigma gp) stmt)

/-- UC specification for visible Chaum-Pedersen transcripts. -/
def cpSpec (V : Type) : UCSpec :=
  ⟨CPStatement gp, Unit, CPVisibleTranscript gp,
   CPVisibleTranscript gp, V⟩

/-- Real Chaum-Pedersen protocol (visible output). -/
noncomputable def cpReal (stmt : CPStatement gp) (w : CPWitness gp) :
    SPComp (Unit ⊕ CPVisibleTranscript gp) :=
  SPComp.map Sum.inr (cpRealVisible gp stmt w)

/-- Ideal Chaum-Pedersen functionality (visible output). -/
noncomputable def cpIdeal (stmt : CPStatement gp) :
    SPComp (Unit ⊕ CPVisibleTranscript gp) :=
  SPComp.map Sum.inr (cpSimVisible gp stmt)

/-- The real and simulated visible transcript computations are equal.

    After projecting out the internal randomness `r`, the bijection
    `r ↦ z = r + e*w` shows that the visible parts `(g^r, h^r, e, z)` of
    the real transcript and `(g^z * u^{-e}, h^z * v^{-e}, e, z)` of the
    simulated transcript have the same distribution, since both visible
    commitments equal `g^r` (resp. `h^r`) when `u = g^w`, `v = h^w`. -/
theorem cp_real_vis_eq_sim (stmt : CPStatement gp) (w : CPWitness gp)
    (hrel : cpRelation gp stmt w) :
    cpRealVisible gp stmt w = cpSimVisible gp stmt := by
  obtain ⟨hu, hv⟩ := hrel
  funext heap
  simp only [cpRealVisible, cpSimVisible, SPComp.map]
  unfold realTranscriptSampled simulatedTranscriptSampled
  simp only [chaumPedersenSigma, cpCommit, cpRespond, cpSimulate]
  simp only [SPComp.monad_bind_eq]
  ssprove_distr_simp
  -- Simplify the projectTranscript layer: normalize pure → SDistr.pure then apply pure_bind
  simp only [SPComp.monad_pure_eq, SPComp.pure_def, SDistr.pure_bind, projectTranscript]
  -- Swap the order of sampling on the LHS
  rw [SDistr.bind_comm]
  congr 1; funext e
  -- Use bijection r -> z = r + e*w
  let bij : gp.Scalar ≃ gp.Scalar := {
    toFun := fun r => gp.scalarAdd r (gp.scalarMul e w)
    invFun := fun z => gp.scalarSub z (gp.scalarMul e w)
    left_inv := fun r => by
      show gp.scalarSub (gp.scalarAdd r (gp.scalarMul e w)) (gp.scalarMul e w) = r
      rw [gp.scalarSub_eq, gp.scalarAdd_assoc, gp.scalarAdd_neg, gp.scalarAdd_zero]
    right_inv := fun z => by
      show gp.scalarAdd (gp.scalarSub z (gp.scalarMul e w)) (gp.scalarMul e w) = z
      rw [gp.scalarSub_eq, gp.scalarAdd_assoc, gp.scalarNeg_add, gp.scalarAdd_zero]
  }
  -- Define the RHS continuation (visible transcript from sim)
  let g_cont : gp.Scalar → SDistr (CPVisibleTranscript gp × Heap) :=
    fun z => SDistr.pure
      ((gp.groupMul (gp.groupExp stmt.1 z) (gp.groupInv (gp.groupExp stmt.2.2.1 e)),
        gp.groupMul (gp.groupExp stmt.2.1 z) (gp.groupInv (gp.groupExp stmt.2.2.2 e)),
        e, z), heap)
  -- Show the real visible continuation equals g_cont ∘ bij
  have hcont : ∀ r, SDistr.pure
      (((gp.groupExp stmt.1 r, gp.groupExp stmt.2.1 r, e,
         gp.scalarAdd r (gp.scalarMul e w)) : CPVisibleTranscript gp), heap) =
    g_cont (bij r) := by
    intro r
    show SDistr.pure _ = SDistr.pure _
    congr 1; congr 1
    exact Prod.ext
      (commitment_recovery gp stmt.1 stmt.2.2.1 w r (bij r) e hu rfl)
      (Prod.ext
        (commitment_recovery gp stmt.2.1 stmt.2.2.2 w r (bij r) e hv rfl)
        rfl)
  have step1 : (SDistr.uniform gp.Scalar).bind
      (fun r => SDistr.pure
        (((gp.groupExp stmt.1 r, gp.groupExp stmt.2.1 r, e,
           gp.scalarAdd r (gp.scalarMul e w)) : CPVisibleTranscript gp), heap)) =
      (SDistr.uniform gp.Scalar).bind (fun r => g_cont (bij r)) := by
    congr 1; funext r; exact hcont r
  rw [step1]
  exact SDistr.uniform_bind_equiv_comp bij g_cont

/-- The Chaum-Pedersen protocol is perfectly UC-secure: `UCEmulates 0`. -/
theorem chaumPedersen_uc_secure (V : Type) (stmt : CPStatement gp) (w : CPWitness gp)
    (hrel : cpRelation gp stmt w) :
    UCEmulates 0 (cpSpec gp V) (fun _ => cpReal gp stmt w) (fun _ => cpIdeal gp stmt) := by
  apply UCEmulates_of_sdist
  simp only [cpReal, cpIdeal, SPComp.map]
  rw [cp_real_vis_eq_sim gp stmt w hrel]
  exact le_of_eq (sdist_self _)

end CatCryptCore.Examples.ChaumPedersen
