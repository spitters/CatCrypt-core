/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.FiatShamirROM.LinearRelation
public import CatCryptCore.Crypto.FiatShamirROM.DuplexSpongeNIZK
public import CatCryptCore.Crypto.Ristretto255.Param
public import CatCryptCore.Crypto.ZK.LinearSigmaUC

/-!
# The poksho statements of Signal's zkgroup as linear relations

libsignal's `poksho` proves knowledge of scalars satisfying a statement, a list of
equations built by `Statement::add(lhs, &[(scalar, point)])`, each meaning
`lhs = Σ scalar · point`. Every name is an opaque string whose value the caller supplies
(`"D2-J1"`, `"-G_j1"`, `"-zt"` and `"0"` are names of points or scalars the caller
computes; `"G"` is poksho's base point). A statement with an assignment of its point
names is therefore a `LinearRelation` of draft-irtf-cfrg-sigma-protocols-03 directly:
the elements are the values of the point names in order of first appearance, the
scalar indices are the scalar names in order of first appearance, and each equation
indexes into these lists.

This module states poksho's statements as data (`PokshoStatement`), their translation
`PokshoStatement.toRelation` to a core linear relation, its meaning by name lookup, the
six statements of zkgroup (libsignal v0.105.2) and the usernames proof, and the
Σ-protocol `PokshoStatement.sigma` over ristretto255 with its security properties.

## Main definitions

* `PokshoEquation`, `PokshoStatement` — poksho's statements in string form.
* `PokshoStatement.toRelation` — the linear relation of a statement at an assignment
  of its point names.
* `PokshoStatement.sigma` — the Σ-protocol `linearSigma` over ristretto255 for the
  relations of a statement, with statements the point assignments.
* `profileKeyCredentialRequestProof`, `expiringProfileKeyCredentialIssuanceProof`,
  `receiptCredentialIssuanceProof`, `expiringProfileKeyCredentialPresentationProof`,
  `receiptCredentialPresentationProof`, `usernameProof` — the statements.

## Main results

* `PokshoStatement.toRelation_holds_iff` — a scalar vector is a witness for the
  relation exactly when every equation `lhs = Σ scalar · point` holds, with each scalar
  name read at its index in the scalar vector.
* `PokshoStatement.toRelation_holds_witness_iff` — the witness built from an
  assignment of the scalar names satisfies the relation exactly when every equation
  holds under the two assignments, poksho's semantics.
* `PokshoStatement.sigma_complete`, `sigma_specialSound`, `sigma_perfectHVZK` — the
  Σ-protocol of every statement is complete, specially sound and perfectly HVZK.
* `PokshoStatement.sigma_ksExtractProb_ge`, `sigma_zkReal_le_zkSim`,
  `sigma_dsKsExtractProb_ge`, `sigma_dsZkReal_le_zkSim` — knowledge soundness and zero
  knowledge of its strong Fiat–Shamir proofs in the random-oracle model and of its
  duplex-sponge proofs.
* `PokshoStatement.sigma_uc_zk_secure` — honest-verifier UC zero knowledge of the
  interactive protocol at error 0.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Signal.Zkgroup

open CatCrypt.Examples CatCrypt.Crypto.FiatShamirROM CatCrypt.Crypto.Ristretto255
open CatCrypt.Crypto.FiatShamirROM.DuplexSponge
open scoped ENNReal

/-- One `Statement::add(lhs, rhs)` call of poksho: the left-hand point name and the
right-hand terms `(scalar name, point name)`. -/
structure PokshoEquation where
  /-- The name of the left-hand point. -/
  lhs : String
  /-- The terms `(scalar name, point name)`. -/
  terms : List (String × String)
deriving DecidableEq, Repr

/-- A poksho statement: its equations, in the order of the `add` calls. -/
structure PokshoStatement where
  /-- The equations. -/
  equations : List PokshoEquation
deriving DecidableEq, Repr

namespace PokshoEquation

variable {gp : GroupParam}

/-- The right-hand side `Σ scalar s · point p` over the terms `(s, p)` of an equation,
written multiplicatively as in `GroupParam`: the product of `point p ^ scalar s`. -/
def rhs (scalar : String → gp.Scalar) (point : String → gp.G) (e : PokshoEquation) :
    gp.G :=
  (e.terms.map fun t => gp.groupExp (point t.2) (scalar t.1)).foldr gp.groupMul gp.identity

/-- The linear equation of `e`: each name replaced by its index in the list of scalar
names or of point names. -/
def toLinear (scalarNames pointNames : List String) (e : PokshoEquation) : LinearEquation :=
  ⟨pointNames.idxOf e.lhs, e.terms.map fun t => (scalarNames.idxOf t.1, pointNames.idxOf t.2)⟩

end PokshoEquation

namespace PokshoStatement

variable (st : PokshoStatement) {gp : GroupParam}

/-- The scalar names of a statement, in order of first appearance. -/
def scalarNames : List String :=
  (st.equations.flatMap fun e => e.terms.map Prod.fst).eraseDups

/-- The point names of a statement, in order of first appearance (left-hand side before
the terms of each equation). -/
def pointNames : List String :=
  (st.equations.flatMap fun e => e.lhs :: e.terms.map Prod.snd).eraseDups

/-- The linear relation of a statement at an assignment `point` of its point names:
the elements are the values of the point names, and equation `i` is equation `i` of the
statement with every name replaced by its index. -/
def toRelation (point : String → gp.G) :
    LinearRelation gp st.scalarNames.length st.equations.length where
  elements := st.pointNames.map point
  equations i := st.equations[i].toLinear st.scalarNames st.pointNames

/-- The value of the scalar name `s` in a scalar vector: its entry at the index of `s`. -/
def scalarValue (w : Fin st.scalarNames.length → gp.Scalar) (s : String) : gp.Scalar :=
  vecGet w (st.scalarNames.idxOf s)

/-- The scalar vector of an assignment of the scalar names. -/
def witness (scalar : String → gp.Scalar) : Fin st.scalarNames.length → gp.Scalar :=
  fun j => scalar st.scalarNames[j]

theorem lhs_mem_pointNames {e : PokshoEquation} (he : e ∈ st.equations) :
    e.lhs ∈ st.pointNames := by
  simp only [pointNames, List.mem_eraseDups, List.mem_flatMap]
  exact ⟨e, he, List.mem_cons_self⟩

theorem point_mem_pointNames {e : PokshoEquation} (he : e ∈ st.equations)
    {t : String × String} (ht : t ∈ e.terms) : t.2 ∈ st.pointNames := by
  simp only [pointNames, List.mem_eraseDups, List.mem_flatMap]
  exact ⟨e, he, List.mem_cons_of_mem _ (List.mem_map_of_mem ht)⟩

theorem scalar_mem_scalarNames {e : PokshoEquation} (he : e ∈ st.equations)
    {t : String × String} (ht : t ∈ e.terms) : t.1 ∈ st.scalarNames := by
  simp only [scalarNames, List.mem_eraseDups, List.mem_flatMap]
  exact ⟨e, he, List.mem_map_of_mem ht⟩

theorem toRelation_elem_idxOf (point : String → gp.G) {p : String}
    (hp : p ∈ st.pointNames) : (st.toRelation point).elem (st.pointNames.idxOf p) = point p := by
  simp [LinearRelation.elem, toRelation, List.getD_eq_getElem?_getD, List.idxOf_lt_length_iff,
    hp]

theorem toRelation_map_apply (point : String → gp.G)
    (w : Fin st.scalarNames.length → gp.Scalar) (i : Fin st.equations.length) :
    (st.toRelation point).map w i = st.equations[i].rhs (st.scalarValue w) point := by
  simp only [toRelation, LinearRelation.map, PokshoEquation.rhs, PokshoEquation.toLinear,
    List.map_map]
  congr 1
  refine List.map_congr_left fun t ht => ?_
  simp only [Function.comp_apply, scalarValue]
  rw [← toRelation_elem_idxOf st point (st.point_mem_pointNames (List.getElem_mem _) ht)]
  rfl

theorem toRelation_image_apply (point : String → gp.G) (i : Fin st.equations.length) :
    (st.toRelation point).image i = point st.equations[i].lhs :=
  st.toRelation_elem_idxOf point (st.lhs_mem_pointNames (List.getElem_mem _))

/-- **Meaning of the relation of a statement.** A scalar vector `w` is a witness for the
relation at the point assignment `point` exactly when every equation
`lhs = Σ scalar · point` holds, with each scalar name `s` read as `w` at the index of
`s` among the scalar names. -/
theorem toRelation_holds_iff (point : String → gp.G)
    (w : Fin st.scalarNames.length → gp.Scalar) :
    (st.toRelation point).Holds w ↔
      ∀ e ∈ st.equations, point e.lhs = e.rhs (st.scalarValue w) point := by
  simp only [LinearRelation.Holds, funext_iff, toRelation_map_apply, toRelation_image_apply]
  constructor
  · intro h e he
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
    exact (h ⟨i, hi⟩).symm
  · intro h i
    exact (h _ (List.getElem_mem _)).symm

theorem scalarValue_witness (scalar : String → gp.Scalar) {s : String}
    (hs : s ∈ st.scalarNames) : st.scalarValue (st.witness scalar) s = scalar s := by
  simp only [scalarValue, vecGet, witness, List.idxOf_lt_length_iff.mpr hs, dite_true]
  exact congrArg scalar (List.getElem_idxOf _)

/-- **poksho's semantics.** The scalar vector of an assignment `scalar` of the scalar
names is a witness for the relation at the point assignment `point` exactly when every
equation `lhs = Σ scalar · point` of the statement holds under the two assignments. -/
theorem toRelation_holds_witness_iff (point : String → gp.G) (scalar : String → gp.Scalar) :
    (st.toRelation point).Holds (st.witness scalar) ↔
      ∀ e ∈ st.equations, point e.lhs = e.rhs scalar point := by
  rw [toRelation_holds_iff]
  refine forall₂_congr fun e he => ?_
  have hrhs : e.rhs (st.scalarValue (st.witness scalar)) point = e.rhs scalar point := by
    simp only [PokshoEquation.rhs]
    congr 1
    refine List.map_congr_left fun t ht => ?_
    rw [st.scalarValue_witness scalar (st.scalar_mem_scalarNames he ht)]
  rw [hrhs]

/-! ## The Σ-protocol over ristretto255 -/

variable (gen : PMF ((String → RistrettoParam.G) × (Fin st.scalarNames.length →
  RistrettoParam.Scalar)))

/-- The Σ-protocol of a poksho statement over ristretto255: `linearSigma` for the
relations `st.toRelation point`, whose statements are the assignments `point` of the
point names and whose witnesses are the scalar vectors. -/
noncomputable def sigma : Sigma :=
  linearSigma RistrettoParam st.scalarNames.length st.equations.length st.toRelation gen

variable {st}

/-- The Σ-protocol of a poksho statement is complete. -/
theorem sigma_complete : (st.sigma gen).Complete :=
  linearSigma_complete _ gen

/-- The Σ-protocol of a poksho statement is specially sound. -/
theorem sigma_specialSound : (st.sigma gen).SpecialSound :=
  linearSigma_specialSound _ gen

/-- The Σ-protocol of a poksho statement is perfectly HVZK when its generator samples
pairs of the relation. -/
theorem sigma_perfectHVZK
    (hgen : ∀ s w, (s, w) ∈ gen.support → (st.toRelation s).Holds w) :
    (st.sigma gen).PerfectHVZK :=
  linearSigma_perfectHVZK _ gen hgen

/-- The Σ-protocol of a poksho statement has perfect HVZK at every pair of the
relation. -/
theorem sigma_statHVZKAt (s : String → RistrettoParam.G)
    (w : Fin st.scalarNames.length → RistrettoParam.Scalar) (hw : (st.toRelation s).Holds w) :
    (st.sigma gen).StatHVZKAt s w 0 :=
  linearSigma_statHVZKAt s w hw

open Classical in
/-- **Knowledge soundness of the strong Fiat–Shamir proofs of a poksho statement.** For
every adversary `A` with at most `qH` random-oracle queries, with `ε = ksAdvantage A`,
`ε·(ε/(qH + 1) − 1/|Scalar|) ≤ ksExtractProb A`. -/
theorem sigma_ksExtractProb_ge {Sid : Type} [DecidableEq Sid] {qH : ℕ}
    (A : KSAdversary (st.sigma gen) Sid qH) :
    ksAdvantage A * (ksAdvantage A / ((qH + 1 : ℕ) : ℝ≥0∞) -
        1 / Fintype.card RistrettoParam.Scalar) ≤
      ksExtractProb A :=
  linearSigma_ksExtractProb_ge A

open Classical in
/-- **Zero knowledge of the strong Fiat–Shamir proofs of a poksho statement.** For a
commitment bound `γ` at every pair of the relation and every distinguisher with at most
`qH` random-oracle and `qP` proving queries, `zkReal D ≤ zkSim D + qP·(qH + qP)·γ`. -/
theorem sigma_zkReal_le_zkSim {Sid : Type} [DecidableEq Sid] {γ : ℝ≥0∞}
    (hγ : ∀ s w, (st.toRelation s).Holds w → (st.sigma gen).CommitBoundAt s w γ)
    {qH qP : ℕ} (D : ZKDistinguisher (st.sigma gen) Sid qH qP) :
    zkReal D ≤ zkSim D + ((qP * (qH + qP) : ℕ) : ℝ≥0∞) * γ :=
  linearSigma_zkReal_le_zkSim hγ D

open Classical in
/-- **Knowledge soundness of the duplex-sponge proofs of a poksho statement.** For
prefix-free encodings and a challenge decoding with the minorant `(1 − β)·uniform`, every
adversary with at most `qH` oracle queries satisfies, with
`ε = dsKsAdvantage A − (qH + 1)·β`, `ε·(ε/(qH + 1) − 1/|Scalar|) ≤ ksExtractProb A`. -/
theorem sigma_dsKsExtractProb_ge (Dp : DSParams (st.sigma gen))
    (hX : PrefixFree Dp.encX) (hA : PrefixFree Dp.encA) {β : ℝ≥0∞}
    (hβ : ∀ c, (1 - β) * PMF.uniformFintype RistrettoParam.Scalar c ≤
      (PMF.uniformFintype (Fin Dp.L → UInt8)).map Dp.decB c)
    {qH : ℕ} (A : KSAdversary (st.sigma gen) SessionId qH) :
    (dsKsAdvantage Dp A - (qH + 1 : ℕ) * β) *
        ((dsKsAdvantage Dp A - (qH + 1 : ℕ) * β) / ((qH + 1 : ℕ) : ℝ≥0∞) -
          1 / Fintype.card RistrettoParam.Scalar) ≤
      ksExtractProb A :=
  dsKsExtractProb_ge Dp (sigma_specialSound gen) hX hA hβ A

open Classical in
/-- **Zero knowledge of the duplex-sponge proofs of a poksho statement.** For a
commitment bound `γ` at every pair of the relation and every distinguisher with at most
`qH` random-oracle and `qP` proving queries against the transform with byte challenges,
`zkReal D ≤ zkSim D + qP·(qH + qP)·γ`. -/
theorem sigma_dsZkReal_le_zkSim (Dp : DSParams (st.sigma gen)) {γ : ℝ≥0∞}
    (hγ : ∀ s w, (st.toRelation s).Holds w → (st.sigma gen).CommitBoundAt s w γ)
    {qH qP : ℕ} (Dz : ZKDistinguisher Dp.sigmaBytes SessionId qH qP) :
    zkReal Dz ≤ zkSim Dz + ((qP * (qH + qP) : ℕ) : ℝ≥0∞) * γ := by
  simpa using dsZkReal_le_zkSim Dp (δ := 0) (fun s w hw => sigma_statHVZKAt gen s w hw) hγ Dz

/-- **Honest-verifier UC zero knowledge of the Σ-protocol of a poksho statement at
`ε = 0`.**

* Ideal functionality `sigma_ideal`: on input `(point, w)` with
  `(st.toRelation point).Holds w` it outputs the statement `point`; otherwise it aborts.
* Real world `sigma_real`: the honest prover commits, the verifier samples the challenge
  uniformly, the prover responds, and the environment sees the statement and the
  transcript.
* Simulator `sigma_uc_sim`: on `point` it samples the challenge and runs the simulator of
  `linearSigma`, without the witness.

The verifier is honest; the non-interactive proofs are covered by
`sigma_zkReal_le_zkSim` and `sigma_dsZkReal_le_zkSim`. (genuine UC) -/
theorem sigma_uc_zk_secure (V : Type) :
    UCEmulates 0 (ZK.SigmaUCZK.sigmaUCZKSpec (st.sigma gen).toSigmaProtocol V)
      (ZK.SigmaUCZK.sigma_real (st.sigma gen).toSigmaProtocol)
      (ZK.SigmaUCZK.sigma_ideal (st.sigma gen).toSigmaProtocol) :=
  linearSigma_uc_zk_secure _ gen V

end PokshoStatement

/-! ## The statements of zkgroup and usernames (libsignal v0.105.2) -/

/-- The statement of `ProfileKeyCredentialRequestProof::get_poksho_statement` in
`rust/zkgroup/src/crypto/proofs.rs`. -/
def profileKeyCredentialRequestProof : PokshoStatement :=
  ⟨[⟨"Y", [("y", "G")]⟩,
    ⟨"D1", [("r1", "G")]⟩,
    ⟨"E1", [("r2", "G")]⟩,
    ⟨"J3", [("j3", "G_j3")]⟩,
    ⟨"D2-J1", [("r1", "Y"), ("j3", "-G_j1")]⟩,
    ⟨"E2-J2", [("r2", "Y"), ("j3", "-G_j2")]⟩]⟩

/-- The statement of `ExpiringProfileKeyCredentialIssuanceProof::get_poksho_statement`
in `rust/zkgroup/src/crypto/proofs.rs`. -/
def expiringProfileKeyCredentialIssuanceProof : PokshoStatement :=
  ⟨[⟨"C_W", [("w", "G_w"), ("wprime", "G_wprime")]⟩,
    ⟨"G_V-I", [("x0", "G_x0"), ("x1", "G_x1"), ("y1", "G_y1"), ("y2", "G_y2"),
      ("y3", "G_y3"), ("y4", "G_y4"), ("y5", "G_y5")]⟩,
    ⟨"S1", [("y3", "D1"), ("y4", "E1"), ("rprime", "G")]⟩,
    ⟨"S2", [("y3", "D2"), ("y4", "E2"), ("rprime", "Y"), ("w", "G_w"), ("x0", "U"),
      ("x1", "tU"), ("y1", "M1"), ("y2", "M2"), ("y5", "M5")]⟩]⟩

/-- The statement of `ReceiptCredentialIssuanceProof::get_poksho_statement` in
`rust/zkgroup/src/crypto/proofs.rs`. -/
def receiptCredentialIssuanceProof : PokshoStatement :=
  ⟨[⟨"C_W", [("w", "G_w"), ("wprime", "G_wprime")]⟩,
    ⟨"G_V-I", [("x0", "G_x0"), ("x1", "G_x1"), ("y1", "G_y1"), ("y2", "G_y2")]⟩,
    ⟨"S1", [("y2", "D1"), ("rprime", "G")]⟩,
    ⟨"S2", [("y2", "D2"), ("rprime", "Y"), ("w", "G_w"), ("x0", "U"), ("x1", "tU"),
      ("y1", "M1")]⟩]⟩

/-- The statement of `ExpiringProfileKeyCredentialPresentationProof::get_poksho_statement`
in `rust/zkgroup/src/crypto/proofs.rs`. zkgroup sets `z0 = -z·t`, `z1 = -z·a1` and
`z2 = -z·b1`. -/
def expiringProfileKeyCredentialPresentationProof : PokshoStatement :=
  ⟨[⟨"Z", [("z", "I")]⟩,
    ⟨"C_x1", [("t", "C_x0"), ("z0", "G_x0"), ("z", "G_x1")]⟩,
    ⟨"A+B", [("a1", "G_a1"), ("a2", "G_a2"), ("b1", "G_b1"), ("b2", "G_b2")]⟩,
    ⟨"C_y2-E_A2", [("z", "G_y2"), ("a2", "-E_A1")]⟩,
    ⟨"E_A1", [("a1", "C_y1"), ("z1", "G_y1")]⟩,
    ⟨"C_y4-E_B2", [("z", "G_y4"), ("b2", "-E_B1")]⟩,
    ⟨"E_B1", [("b1", "C_y3"), ("z2", "G_y3")]⟩,
    ⟨"0", [("z1", "I"), ("a1", "Z")]⟩,
    ⟨"0", [("z2", "I"), ("b1", "Z")]⟩,
    ⟨"C_y5", [("z", "G_y5")]⟩]⟩

/-- The statement of `ReceiptCredentialPresentationProof::get_poksho_statement` in
`rust/zkgroup/src/crypto/proofs.rs`. zkgroup sets `-zt` to `-z·t`. -/
def receiptCredentialPresentationProof : PokshoStatement :=
  ⟨[⟨"Z", [("z", "I")]⟩,
    ⟨"C_x1", [("t", "C_x0"), ("-zt", "G_x0"), ("z", "G_x1")]⟩,
    ⟨"C_y1", [("z", "G_y1")]⟩,
    ⟨"C_y2", [("z", "G_y2")]⟩]⟩

/-- The statement `PROOF_STATEMENT` of `Username::proof` in
`rust/usernames/src/username.rs`; poksho's message is the compressed username hash. -/
def usernameProof : PokshoStatement :=
  ⟨[⟨"username_hash", [("username_sha_scalar", "G1"), ("nickname_scalar", "G2"),
      ("discriminator_scalar", "G3")]⟩]⟩

/-! The scalar variables of each statement, in the order of the witness vector. -/

example : profileKeyCredentialRequestProof.scalarNames = ["y", "r1", "r2", "j3"] := by
  decide

example : expiringProfileKeyCredentialIssuanceProof.scalarNames =
    ["w", "wprime", "x0", "x1", "y1", "y2", "y3", "y4", "y5", "rprime"] := by
  decide

example : receiptCredentialIssuanceProof.scalarNames =
    ["w", "wprime", "x0", "x1", "y1", "y2", "rprime"] := by
  decide

example : expiringProfileKeyCredentialPresentationProof.scalarNames =
    ["z", "t", "z0", "a1", "a2", "b1", "b2", "z1", "z2"] := by
  decide

example : receiptCredentialPresentationProof.scalarNames = ["z", "t", "-zt"] := by
  decide

example : usernameProof.scalarNames =
    ["username_sha_scalar", "nickname_scalar", "discriminator_scalar"] := by
  decide

end CatCrypt.Crypto.Signal.Zkgroup
