/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Assumptions.CyclicGroup
public import CatCryptCore.Crypto.Assumptions.DDH
public import CatCryptCore.Crypto.Assumptions.GapDH
public import CatCryptCore.Examples.Sigma
public import CatCryptCore.Tactics.Auto
public import CatCryptCore.Tactics.Sim

/-!
# Schnorr Sigma Protocol (v2 -- shared infrastructure)

Schnorr over `CyclicGroupDef`, with the `exp_simp` and `rHoare` tactics:
completeness and SHVZK (given and internal challenge) of the identification
protocol, and the signing and verification algorithms. Special soundness with
the extractor `(z₁ - z₂)/(e₁ - e₂)` is `FiatShamirROM.schnorrSigma_specialSound`
and the EUF-CMA bound in the random-oracle model is
`FiatShamirROM.schnorr_fs_rom_eufcma`, both over a `GroupParam`.
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Relational CatCrypt.Tactics
open CatCrypt.Examples.Sigma
open scoped ENNReal

namespace CatCrypt.Examples.Schnorr_v2

variable (cg : CyclicGroupDef)

/-! ## Schnorr Protocol Definitions -/

/-- The discrete log relation: R(h, w) iff h = g^w. -/
def dlRelation (h : cg.G) (w : cg.S) : Prop := h = cg.exp w

/-- Schnorr commitment: sample r, return (r, g^r). -/
noncomputable def schnorrCommit (_h : cg.G) (_w : cg.S) : SPComp (cg.S × cg.G) := do
  let r ← SPComp.sample cg.S
  SPComp.pure (r, cg.exp r)

/-- Schnorr response: z = r + e*w. -/
noncomputable def schnorrRespond (_h : cg.G) (w : cg.S)
    (ra : cg.S × cg.G) (e : cg.S) : SPComp cg.S :=
  SPComp.pure (ra.1 + e * w)

/-- Schnorr verification: check g^z = a * h^e. -/
def schnorrVerify (h : cg.G) (ra : cg.S × cg.G)
    (e : cg.S) (z : cg.S) : Bool :=
  cg.exp z == ra.2 * cg.groupExp h e

/-- Schnorr simulator: sample z, compute a = g^z * h^{-e}. -/
noncomputable def schnorrSimulate (h : cg.G) (e : cg.S) :
    SPComp ((cg.S × cg.G) × cg.S) := do
  let z ← SPComp.sample cg.S
  let a := cg.exp z * (cg.groupExp h e)⁻¹
  SPComp.pure ((z, a), z)

/-! ## Sigma Protocol Instance -/

@[implicit_reducible]
noncomputable def schnorrSigma : SigmaProtocol where
  Statement := cg.G
  Witness := cg.S
  Message := cg.S × cg.G
  Challenge := cg.S
  Response := cg.S
  finChallenge := cg.finS
  neChallenge := cg.neS
  relation := dlRelation cg
  commit := schnorrCommit cg
  respond := schnorrRespond cg
  verify := schnorrVerify cg
  simulate := schnorrSimulate cg

def visibleTranscriptEq (t₁ t₂ : Transcript (schnorrSigma cg)) : Prop :=
  t₁.message.2 = t₂.message.2 ∧ t₁.challenge = t₂.challenge ∧ t₁.response = t₂.response

theorem schnorr_complete (h : cg.G) (w : cg.S) (hrel : dlRelation cg h w)
    (r e : cg.S) : schnorrVerify cg h (r, cg.exp r) e (r + e * w) = true := by
  simp only [schnorrVerify, beq_eq_decide, decide_eq_true_eq]; rw [hrel]; exp_simp

/-! ## SHVZK -/

def shvzkBij (e w : cg.S) : cg.S ≃ cg.S :=
  ⟨(· + e * w), (· - e * w), fun r => by ring, fun z => by ring⟩

theorem schnorr_SHVZK_visible : ∀ (x : cg.G) (w e : cg.S), dlRelation cg x w →
    rHoare
      (fun _ _ => True)
      (realTranscriptGiven (schnorrSigma cg) x w e)
      (simulatedTranscriptGiven (schnorrSigma cg) x e)
      (fun t₁ _ t₂ _ => visibleTranscriptEq cg t₁ t₂) := by
  intro x w e hrel
  unfold realTranscriptGiven simulatedTranscriptGiven
  simp only [schnorrSigma, schnorrCommit, schnorrRespond, schnorrSimulate]
  ssprove_code_simpl
  apply rHoare_bij_step (shvzkBij cg e w); intro r
  apply rHoare_ret; intro h₁ h₂ _
  simp only [visibleTranscriptEq, shvzkBij, Equiv.coe_fn_mk, dlRelation] at hrel ⊢
  rw [hrel]; refine ⟨?_, by trivial, by trivial⟩
  simp only [cg.groupExp_mul', cg.exp_add']; group

theorem schnorr_SHVZK : ∀ x w, (schnorrSigma cg).relation x w →
    rHoare
      (fun _ _ => True)
      (realTranscript (schnorrSigma cg) x w)
      (simulatedTranscript (schnorrSigma cg) x)
      (fun t₁ _ t₂ _ => visibleTranscriptEq cg t₁ t₂) := by
  intro (x : cg.G) (w : cg.S) hrel
  unfold realTranscript simulatedTranscript
  simp only [schnorrSigma, schnorrCommit, schnorrRespond, schnorrSimulate]
  ssprove_code_simpl
  -- Swap sampling order on LHS to align with RHS
  ssprove_swap_samples_lhs 1
  -- Couple challenges via identity, then commitment/response via bijection
  apply rHoare_same_step; intro ch
  apply rHoare_bij_step (shvzkBij cg ch w); intro r
  apply rHoare_ret; intro h₁ h₂ _
  simp only [visibleTranscriptEq, shvzkBij, Equiv.coe_fn_mk, schnorrSigma, dlRelation] at hrel ⊢
  rw [hrel]; refine ⟨?_, trivial, trivial⟩
  simp only [cg.groupExp_mul', cg.exp_add']; group

/-! ## Signatures -/

structure SchnorrSignature where
  commitment : cg.G
  response : cg.S

noncomputable def schnorrSign {MsgType : Type}
    (hash : cg.G → MsgType → cg.S) (w : cg.S) (m : MsgType) :
    SPComp (SchnorrSignature cg) := do
  let r ← SPComp.sample cg.S
  let a := cg.exp r; let e := hash a m
  SPComp.pure ⟨a, r + e * w⟩

def schnorrVerifySig {MsgType : Type}
    (hash : cg.G → MsgType → cg.S) (pk : cg.G) (m : MsgType)
    (sig : SchnorrSignature cg) : Bool :=
  cg.exp sig.response == sig.commitment * cg.groupExp pk (hash sig.commitment m)

end CatCrypt.Examples.Schnorr_v2
