/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.SaltedHashSign

/-!
# The preimage-sampling game of salted hash-and-sign

The preimage-sampling game of a `SaltedPSF` on a finite set of points `P` is a decision game
between two instance laws. An instance is a public key and a table that holds, at every point,
a target and a preimage of it. The key pair is drawn from `keygen`, the target at every point
is uniform, and the preimage at every point is drawn independently from the signer's law
`preW` (world `false`) or from the simulator's law `simW`, the domain law conditioned on the
target (world `true`). The targets have the same law in both worlds.

The reduction `B_psQ` reads an instance on the points `Msg × Salt`, draws uniform salts, sets
the oracle to the table of targets and answers each signing entry with the preimage at its
salted point, or with a signing failure when the entry repeats a salt of its message. It uses
neither the secret key nor the domain sampler. Its acceptance probability in world `true` is
the game `condGame` after hop A (`psInst_true_B_psQ`); in world `false` it is within
`k (T - 1) / card Salt` of the EUF-CMA advantage (`absDiff_qeufcma_psInst_false_le`). Hop A in
the preimage-sampling form follows (`saltedPSF_hopCondPS`).

Routes I and II with the preimage-sampling game chain this hop with hops B and C and the
terminal steps of `SaltedHashSign`: their bounds are those of `saltedPSF_qeufcma_le_inv` and
`saltedPSF_qeufcma_le_coll` with `k · condDist` replaced by the preimage-sampling advantage of
`B_psQ`. That advantage is at most `k · condDist + 2 k (T - 1) / card Salt`
(`psAdv_B_psQ_le`), so these bounds imply the statistical ones up to one more salt-collision
term.

## Main definitions

* `SaltedPSF.psLaw`, `psTabW`, `psTab`, `psInst` — the preimage law of a world, the weight and
  the law of a table of targets and preimages, and the instance law of the game
* `SaltedPSF.psAdv` — the preimage-sampling advantage of a quantum distinguisher without
  oracle access
* `SaltedPSF.psOracle` — the oracle table of the targets of an instance
* `SaltedPSF.B_psQ` — the preimage-sampling reduction

## Main results

* `SaltedPSF.sdExp_psInst` — the expectation over the instances as a finite sum
* `SaltedPSF.qStdAcc_B_psQ` — the acceptance probability of `B_psQ` at an instance
* `SaltedPSF.sum_ptTab_eq` — uniform oracles and per-entry samplers of a target law give the
  simulated signing table the law that a uniform target table and per-point preimages give it
* `SaltedPSF.psInst_true_B_psQ` — world `true` of `B_psQ` is `condGame`
* `SaltedPSF.absDiff_qeufcma_psInst_false_le` — world `false` of `B_psQ` is within
  `k (T - 1) / card Salt` of the EUF-CMA advantage
* `SaltedPSF.saltedPSF_hopCondPS` — hop A with the preimage-sampling game
* `SaltedPSF.psAdv_B_psQ_le` — the statistical bound of the preimage-sampling advantage of
  `B_psQ`
* `SaltedPSF.saltedPSF_qeufcma_le_inv_ps`, `SaltedPSF.saltedPSF_qeufcma_le_coll_ps` — routes I
  and II with the preimage-sampling game
* `SaltedPSF.saltTerms_le` — the two salt terms of route I at `T = 2^20` and an `s`-bit salt
  are at most `(k + 1) 2^(20 - s)`
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal
open CatCrypt.Quantum CatCrypt.Prob

noncomputable section

namespace CatCrypt.Quantum.QROM

namespace SaltedPSF

variable {Msg Salt PK SK Sig Tgt : Type} (S : SaltedPSF Msg Salt PK SK Sig Tgt)

/-! ## The game -/

section Game

variable [Fintype Sig] [DecidableEq Sig] [Fintype Tgt] [DecidableEq Tgt]

/-- The per-target preimage law of world `b`: the signer's law `preW` (`b = false`) or the
    simulator's law `simW`, the domain law conditioned on the target (`b = true`). -/
def psLaw (b : Bool) (ks : PK × SK) (θ : Tgt) : Option Sig → ℝ≥0∞ :=
  if b then S.simW ks.1 θ else S.preW ks.2 θ

omit [Fintype Tgt] in
/-- The preimage law of a world has mass one. -/
theorem sum_psLaw (b : Bool) (ks : PK × SK) (θ : Tgt) : ∑ o, S.psLaw b ks θ o = 1 := by
  cases b
  · simp only [psLaw, Bool.false_eq_true, ↓reduceIte, S.sum_preW]
  · simp only [psLaw, ↓reduceIte, S.sum_simW]

variable (P : Type) [Fintype P] [DecidableEq P] [Nonempty Tgt]

/-- The weight of a table of targets and preimages on the points `P` in world `b`: at every
    point, independently, a uniform target and a preimage of it from `psLaw b`. -/
def psTabW (b : Bool) (ks : PK × SK) (t : P → Tgt × Option Sig) : ℝ≥0∞ :=
  ∏ x, (Fintype.card Tgt : ℝ≥0∞)⁻¹ * S.psLaw b ks (t x).1 (t x).2

/-- The weights of the tables of a world have mass one. -/
theorem sum_psTabW (b : Bool) (ks : PK × SK) : ∑ t, S.psTabW P b ks t = 1 := by
  have h : ∀ _x : P, ∑ p : Tgt × Option Sig,
      (Fintype.card Tgt : ℝ≥0∞)⁻¹ * S.psLaw b ks p.1 p.2 = 1 := fun _ => by
    rw [Fintype.sum_prod_type]
    simp only [← Finset.mul_sum, S.sum_psLaw, mul_one, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul]
    exact ENNReal.mul_inv_cancel (by simp) (ENNReal.natCast_ne_top _)
  unfold psTabW
  exact sum_prod_eq_one (ι := P) (β := Tgt × Option Sig) _ h

/-- The law of a table of targets and preimages on the points `P` in world `b`. -/
def psTab (b : Bool) (ks : PK × SK) : PMF (P → Tgt × Option Sig) :=
  PMF.ofFintype (S.psTabW P b ks) (S.sum_psTabW P b ks)

/-- The instance law of the preimage-sampling game on the points `P` in world `b`: a key pair
    from `keygen` and a table of targets and preimages from `psTab b`. The instance is the
    public key and the table. -/
def psInst (b : Bool) : SDistr (PK × (P → Tgt × Option Sig)) :=
  SDistr.bind (S.keygen.map some) fun ks => (S.psTab P b ks).map fun t => some (ks.1, t)

/-- The preimage-sampling advantage of a quantum distinguisher without oracle access: its
    distinguishing advantage between the instance laws of the two worlds. -/
def psAdv {P : Type} [Fintype P] [DecidableEq P] {ι : Type} [Fintype ι] {m n w : ℕ}
    [NeZero n] (B : QStdDist ι (PK × (P → Tgt × Option Sig)) m n w) : ℝ≥0∞ :=
  qDistAdv (S.psInst P false) (S.psInst P true) B

/-- The expectation over the instances of the preimage-sampling game. -/
theorem sdExp_psInst [Fintype PK] [Fintype SK] (b : Bool)
    (φ : PK × (P → Tgt × Option Sig) → ℝ≥0∞) :
    sdExp (S.psInst P b) φ = ∑ ks, S.keygen ks * ∑ t, S.psTabW P b ks t * φ (ks.1, t) := by
  classical
  unfold psInst
  rw [sdExp_sdBind]
  simp only [sdExp, PMF.map_apply, tsum_fintype, Option.some.injEq, Finset.sum_ite_eq,
    Finset.mem_univ, ite_true, psTab, PMF.ofFintype_apply]
  refine Finset.sum_congr rfl fun ks _ => ?_
  congr 1
  simp only [Finset.sum_mul, ite_mul, zero_mul]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ite_true]

end Game

/-! ## The reduction -/

section Reduction

variable [Fintype Sig] [DecidableEq Sig] [Fintype Tgt] [DecidableEq Tgt] [DecidableEq Salt]
  {m n w q k c a T : ℕ} [Fintype Msg] [DecidableEq Msg] [Fintype Salt] [Nonempty Salt]
  [NeZero n] [NeZero c]

/-- The oracle table of the targets of a table of targets and preimages on `Msg × Salt`. -/
def psOracle (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n)
    (t : Msg × Salt → Tgt × Option Sig) : Fin m → Fin n :=
  fun x => eY (t (eX.symm x)).1

/-- The preimage-sampling reduction: on the public key and the table of targets and
    preimages, with uniform salts, the adversary run against the simulated signing table that
    answers each entry with the preimage at its salted point (a failure at every entry that
    repeats a salt), with the oracle the table of targets and the final projector of the
    forgery test, the oracle absorbed. It uses no secret key and no domain sampler. -/
def B_psQ (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c)
    (eA : Option (Salt × Sig) ≃ Fin a) (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig)) :
    QStdDist (Msg × Fin T → Salt) (PK × (Msg × Salt → Tgt × Option Sig)) m n (ancW c k w) :=
  fun x r => absorbOracle
    ((toQAdv (A.run x.1) (simTab eQ eA (hashOf eX eY (psOracle eX eY x.2))
        (ansTab (Tgt := Tgt) r fun y => (x.2 (y.1, r y)).2))).withFinalB
      fun i => forgeTest S.toQROMSig eY eQ A x.1 i
        (psOracle eX eY x.2 (forgePoint S.toQROMSig eX A x.1 i)))
    (psOracle eX eY x.2)

omit [Fintype Sig] [DecidableEq Sig] [Fintype Tgt] in
/-- The acceptance probability of `B_psQ` at an instance: the average over uniform salts of
    the winning probability of `forgeGen` at the oracle of the targets and the simulated
    signing table of the preimages at the salted points. -/
theorem qStdAcc_B_psQ (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c)
    (eA : Option (Salt × Sig) ≃ Fin a) (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig))
    (pk : PK) (t : Msg × Salt → Tgt × Option Sig) :
    qStdAcc (S.B_psQ eX eY eQ eA A) (pk, t) =
      ∑ r : Msg × Fin T → Salt, (∏ _y : Msg × Fin T, (Fintype.card Salt : ℝ≥0∞)⁻¹) *
        prOutMRGen (S.forgeGen eX eY eQ A pk (psOracle eX eY t)) (psOracle eX eY t)
          (simTab eQ eA (hashOf eX eY (psOracle eX eY t))
            (ansTab (Tgt := Tgt) r fun y => (t (y.1, r y)).2)) := by
  have hR : ∏ _y : Msg × Fin T, (Fintype.card Salt : ℝ≥0∞)⁻¹ =
      (Fintype.card (Msg × Fin T → Salt) : ℝ≥0∞)⁻¹ := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fun, Nat.cast_pow, ENNReal.inv_pow]
  unfold qStdAcc
  rw [hR]
  refine Finset.sum_congr rfl fun r _ => ?_
  unfold B_psQ prOut0
  rw [prOut_absorbOracle, prOut_withFinalB_toQAdv_eq]
  rfl

omit [Fintype Sig] [DecidableEq Sig] [Fintype Tgt] [DecidableEq Tgt] [Fintype Msg]
  [DecidableEq Msg] [Fintype Salt] [Nonempty Salt] [NeZero n] [NeZero c] in
/-- The simulated signing table of salts and samplers reads each sampler only at the target of
    its salted point. -/
theorem simTab_eq_ansTab (eQ : Msg × Fin T ≃ Fin c) (eA : Option (Salt × Sig) ≃ Fin a)
    (h : Msg × Salt → Tgt) (r : Msg × Fin T → Salt) (κ : Msg × Fin T → Tgt → Option Sig) :
    simTab eQ eA h (fun y => (r y, κ y)) =
      simTab eQ eA h (ansTab r fun y => κ y (h (y.1, r y))) := by
  funext i
  simp only [simTab, collides, honestTab, ansTab]
  rfl

omit [DecidableEq Sig] [Fintype Tgt] [DecidableEq Tgt] [Nonempty Salt] [NeZero n]
  [NeZero c] in
/-- Reindexing the answers of the entries by the salted points, for a function `F` of the
    simulated signing table: the entries that repeat no salt have distinct salted points, and
    only their answers are read. -/
theorem sum_ans_eq_sum_ptTab (eQ : Msg × Fin T ≃ Fin c) (eA : Option (Salt × Sig) ≃ Fin a)
    (h : Msg × Salt → Tgt) (ν : Tgt → Option Sig → ℝ≥0∞) (hν : ∀ θ, ∑ o, ν θ o = 1)
    (r : Msg × Fin T → Salt) (F : (Fin c → Fin a) → ℝ≥0∞) :
    ∑ o : Msg × Fin T → Option Sig, (∏ y, ν (h (y.1, r y)) (o y)) *
        F (simTab eQ eA h (ansTab r o)) =
      ∑ o : Msg × Salt → Option Sig, (∏ x, ν (h x) (o x)) *
        F (simTab eQ eA h (ansTab r fun y => o (y.1, r y))) := by
  let N : Finset (Msg × Fin T) :=
    Finset.univ.filter fun y => collides (fun y => (r y, ())) y = false
  have hinj : Set.InjOn (fun y : Msg × Fin T => (y.1, r y)) N := by
    intro y hy y' hy' he
    simp only [N, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hy hy'
    obtain ⟨h1, h2⟩ := Prod.mk.inj he
    have hc : ∀ z z' : Msg × Fin T, z.1 = z'.1 → r z = r z' → z.2 < z'.2 →
        collides (fun y => (r y, ())) z' = true := fun z z' e1 e2 hlt => by
      simp only [collides, decide_eq_true_eq]
      refine ⟨z.2, hlt, ?_⟩
      rw [show ((z'.1, z.2) : Msg × Fin T) = z from Prod.ext e1.symm rfl, e2]
    rcases lt_trichotomy y.2 y'.2 with hlt | heq | hgt
    · simp [hc y y' h1 h2 hlt] at hy'
    · exact Prod.ext h1 heq
    · simp [hc y' y h1.symm h2.symm hgt] at hy
  refine sum_prod_comp_eq_of_injOn (fun y => (y.1, r y)) N hinj (fun x => ν (h x))
    (fun x => hν _) (fun o => F (simTab eQ eA h (ansTab r o))) ?_
  intro o o' hoo
  congr 1
  funext i
  simp only [simTab, collides_congr (ansTab r o) (fun y => (r y, ())) (fun _ => rfl),
    collides_congr (ansTab r o') (fun y => (r y, ())) (fun _ => rfl)]
  split_ifs with hcol
  · rfl
  · simp only [honestTab, ansTab]
    rw [hoo _ (by simp [N, hcol])]

omit [DecidableEq Sig] [Nonempty Salt] [NeZero n] [NeZero c] in
/-- The tables of the simulated world, reindexed by the salted points: a uniform oracle and,
    at every entry, a uniform salt and a sampler whose values at the targets are independent of
    law `ν`, give a function `F` of the oracle and the simulated signing table the law that a
    uniform target and a preimage of law `ν` at every point, and uniform salts, give it at the
    oracle of the targets and the table answering each entry with the preimage at its salted
    point. -/
theorem sum_ptTab_eq (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n)
    (eQ : Msg × Fin T ≃ Fin c) (eA : Option (Salt × Sig) ≃ Fin a)
    (ν : Tgt → Option Sig → ℝ≥0∞) (hν : ∀ θ, ∑ o, ν θ o = 1)
    (F : (Fin m → Fin n) → (Fin c → Fin a) → ℝ≥0∞) :
    ∑ H : Fin m → Fin n, (Fintype.card (Fin m → Fin n) : ℝ≥0∞)⁻¹ *
      ∑ v : Msg × Fin T → Salt × (Tgt → Option Sig),
        (∏ y, (Fintype.card Salt : ℝ≥0∞)⁻¹ * ∏ θ, ν θ ((v y).2 θ)) *
          F H (simTab eQ eA (hashOf eX eY H) v) =
      ∑ t : Msg × Salt → Tgt × Option Sig,
        (∏ x, (Fintype.card Tgt : ℝ≥0∞)⁻¹ * ν (t x).1 (t x).2) *
          ∑ r : Msg × Fin T → Salt, (∏ _y : Msg × Fin T, (Fintype.card Salt : ℝ≥0∞)⁻¹) *
            F (psOracle eX eY t) (simTab eQ eA (hashOf eX eY (psOracle eX eY t))
              (ansTab r fun y => (t (y.1, r y)).2)) := by
  classical
  have hcT : (Fintype.card Tgt : ℝ≥0∞) = n := by
    rw [Fintype.card_congr eY, Fintype.card_fin]
  have hcH : (Fintype.card (Fin m → Fin n) : ℝ≥0∞)⁻¹ =
      ∏ _x : Msg × Salt, (Fintype.card Tgt : ℝ≥0∞)⁻¹ := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_congr eX, Fintype.card_fun,
      Fintype.card_fin, Fintype.card_fin, hcT, Nat.cast_pow, ENNReal.inv_pow]
  have hA : ∀ H : Fin m → Fin n,
      ∑ v : Msg × Fin T → Salt × (Tgt → Option Sig),
        (∏ y, (Fintype.card Salt : ℝ≥0∞)⁻¹ * ∏ θ, ν θ ((v y).2 θ)) *
          F H (simTab eQ eA (hashOf eX eY H) v) =
      ∑ r : Msg × Fin T → Salt, (∏ _y : Msg × Fin T, (Fintype.card Salt : ℝ≥0∞)⁻¹) *
        ∑ o : Msg × Salt → Option Sig, (∏ x, ν (hashOf eX eY H x) (o x)) *
          F H (simTab eQ eA (hashOf eX eY H) (ansTab r fun y => o (y.1, r y))) := by
    intro H
    rw [← (Equiv.arrowProdEquivProdArrow (Msg × Fin T) (fun _ => Salt)
        (fun _ => Tgt → Option Sig)).symm.sum_comp, Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun r _ => ?_
    simp only [Equiv.arrowProdEquivProdArrow, Equiv.coe_fn_symm_mk, Finset.prod_mul_distrib,
      mul_assoc, ← Finset.mul_sum]
    congr 1
    rw [← sum_ans_eq_sum_ptTab eQ eA (hashOf eX eY H) ν hν r (F H)]
    simp only [simTab_eq_ansTab]
    have hpi := sum_pi_comp_eq (ι := Msg × Fin T) (α := Tgt → Option Sig) (β := Option Sig)
      (γ := Option Sig) (fun _ κ => ∏ θ, ν θ (κ θ))
      (fun y o => ν (hashOf eX eY H (y.1, r y)) o) (fun y κ => κ (hashOf eX eY H (y.1, r y)))
      (fun _ o => o) (fun _ g => sum_prod_eval (fun θ => ν θ) _ hν g)
      (fun o => F H (simTab eQ eA (hashOf eX eY H) (ansTab r o)))
    exact hpi
  have he : ∀ (H : Fin m → Fin n) (o : Msg × Salt → Option Sig),
      psOracle eX eY (fun x => (hashOf eX eY H x, o x)) = H := fun H o =>
    funext fun i => by simp [psOracle, hashOf]
  let e : (Fin m → Fin n) × (Msg × Salt → Option Sig) ≃ (Msg × Salt → Tgt × Option Sig) :=
    { toFun := fun p x => (hashOf eX eY p.1 x, p.2 x)
      invFun := fun t => (psOracle eX eY t, fun x => (t x).2)
      left_inv := fun p => Prod.ext (he p.1 p.2) rfl
      right_inv := fun t => funext fun x => by simp [hashOf, psOracle] }
  rw [← e.sum_comp, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun H _ => ?_
  rw [hA H]
  simp only [e, Equiv.coe_fn_mk, he, Finset.prod_mul_distrib, ← hcH]
  simp only [Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun o _ => Finset.sum_congr rfl fun r _ => by ring

omit [DecidableEq Salt] [Fintype Msg] [DecidableEq Msg] [Nonempty Salt] [NeZero n]
  [NeZero c] in
/-- A uniform salt and an honest conditional sampler: a test of the salt has the probability it
    has for the salt alone. -/
theorem sum_salt_samplerW (sk : SK) (Q : Salt → Prop) [DecidablePred Q] :
    ∑ x : Salt × (Tgt → Option Sig),
        (Fintype.card Salt : ℝ≥0∞)⁻¹ * S.samplerW sk x.2 * (if Q x.1 then 1 else 0) =
      ∑ r, (Fintype.card Salt : ℝ≥0∞)⁻¹ * (if Q r then 1 else 0) := by
  have h1 : ∑ κ, S.samplerW sk κ = 1 :=
    sum_prod_eq_one (fun θ => S.preW sk θ) (S.sum_preW sk)
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun r _ => ?_
  calc _ = ∑ κ, ((Fintype.card Salt : ℝ≥0∞)⁻¹ * if Q r then 1 else 0) * S.samplerW sk κ :=
        Finset.sum_congr rfl fun κ _ => by ring
    _ = _ := by rw [← Finset.mul_sum, h1, mul_one]

/-! ## The two worlds -/

variable [Fintype PK] [Fintype SK] [Nonempty Tgt]

/-- World `true` of `B_psQ` is the game after hop A: its acceptance probability on the instances
    with the simulator's preimages is `condGame`. -/
theorem psInst_true_B_psQ (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n)
    (eQ : Msg × Fin T ≃ Fin c) (eA : Option (Salt × Sig) ≃ Fin a)
    (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig)) :
    sdExp (S.psInst (Msg × Salt) true) (qStdAcc (S.B_psQ eX eY eQ eA A)) =
      S.condGame eX eY eQ eA A := by
  rw [S.sdExp_psInst]
  unfold condGame
  refine Finset.sum_congr rfl fun ks _ => ?_
  congr 1
  unfold condGameAt
  simp only [simSamplerW]
  rw [sum_ptTab_eq eX eY eQ eA (S.simW ks.1) (S.sum_simW ks.1)
    fun H tab => prOutMRGen (S.forgeGen eX eY eQ A ks.1 H) H tab]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [S.qStdAcc_B_psQ]
  simp only [psTabW, psLaw, ↓reduceIte]

omit [Fintype PK] [Fintype SK] [Nonempty Tgt] in
/-- World `false` of `B_psQ` at one key pair: the winning probability of the EUF-CMA game and
    the acceptance probability of `B_psQ` on the instances with the signer's preimages differ by
    at most `k (T - 1) / card Salt`. -/
theorem absDiff_prForge_psInst_false_le (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n)
    (eQ : Msg × Fin T ≃ Fin c) (eA : Option (Salt × Sig) ≃ Fin a)
    (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig)) (ks : PK × SK) :
    absDiff (∑ R : Msg × Fin T → Salt × S.PCoins,
        (Fintype.card (Msg × Fin T → Salt × S.PCoins) : ℝ≥0∞)⁻¹ *
          ∑ H : Fin m → Fin n, (Fintype.card (Fin m → Fin n) : ℝ≥0∞)⁻¹ *
            prForge S.toQROMSig eX eY eQ eA A ks H R)
      (∑ t, S.psTabW (Msg × Salt) false ks t * qStdAcc (S.B_psQ eX eY eQ eA A) (ks.1, t)) ≤
      k * (((T - 1 : ℕ) : ℝ≥0∞) * (Fintype.card Salt : ℝ≥0∞)⁻¹) := by
  classical
  have hsplit : ∀ G : (Fin m → Fin n) → (Msg × Fin T → Salt × (Tgt → Option Sig)) → ℝ≥0∞,
      ∑ H : Fin m → Fin n, (Fintype.card (Fin m → Fin n) : ℝ≥0∞)⁻¹ *
        ∑ u : Msg × Fin T → Salt × (Tgt → Option Sig),
          (∏ y, (Fintype.card Salt : ℝ≥0∞)⁻¹ * S.samplerW ks.2 (u y).2) * G H u =
      ∑ ω : (Fin m → Fin n) × (Msg × Fin T → Salt × (Tgt → Option Sig)),
        ((Fintype.card (Fin m → Fin n) : ℝ≥0∞)⁻¹ *
          ∏ y, (Fintype.card Salt : ℝ≥0∞)⁻¹ * S.samplerW ks.2 (ω.2 y).2) * G ω.1 ω.2 := by
    intro G
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl fun H _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun u _ => by ring
  have hG0 : (∑ R : Msg × Fin T → Salt × S.PCoins,
        (Fintype.card (Msg × Fin T → Salt × S.PCoins) : ℝ≥0∞)⁻¹ *
          ∑ H : Fin m → Fin n, (Fintype.card (Fin m → Fin n) : ℝ≥0∞)⁻¹ *
            prForge S.toQROMSig eX eY eQ eA A ks H R) =
      ∑ ω : (Fin m → Fin n) × (Msg × Fin T → Salt × (Tgt → Option Sig)),
        ((Fintype.card (Fin m → Fin n) : ℝ≥0∞)⁻¹ *
          ∏ y, (Fintype.card Salt : ℝ≥0∞)⁻¹ * S.samplerW ks.2 (ω.2 y).2) *
          prOutMRGen (S.forgeGen eX eY eQ A ks.1 ω.1) ω.1
            (honestTab eQ eA (hashOf eX eY ω.1) ω.2) := by
    rw [← hsplit fun H u => prOutMRGen (S.forgeGen eX eY eQ A ks.1 H) H
      (honestTab eQ eA (hashOf eX eY H) u)]
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun H _ => ?_
    have h1 := S.sum_signTab_eq_sum_honestTab eQ eA ks.2 (hashOf eX eY H)
      (fun tab => prOutMRGen (S.forgeGen eX eY eQ A ks.1 H) H tab)
    simp only [← Finset.mul_sum]
    rw [← h1, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun R _ => ?_
    rw [show prForge S.toQROMSig eX eY eQ eA A ks H R =
        prOutMRGen (S.forgeGen eX eY eQ A ks.1 H) H
          (signTab S.toQROMSig eQ eA ks.2 (hashOf eX eY H) R) from
      prOut_withFinalB_toQAdv_eq _ _ _ H]
    ring
  have hG1 : (∑ t, S.psTabW (Msg × Salt) false ks t *
        qStdAcc (S.B_psQ eX eY eQ eA A) (ks.1, t)) =
      ∑ ω : (Fin m → Fin n) × (Msg × Fin T → Salt × (Tgt → Option Sig)),
        ((Fintype.card (Fin m → Fin n) : ℝ≥0∞)⁻¹ *
          ∏ y, (Fintype.card Salt : ℝ≥0∞)⁻¹ * S.samplerW ks.2 (ω.2 y).2) *
          prOutMRGen (S.forgeGen eX eY eQ A ks.1 ω.1) ω.1
            (simTab eQ eA (hashOf eX eY ω.1) ω.2) := by
    rw [← hsplit fun H u => prOutMRGen (S.forgeGen eX eY eQ A ks.1 H) H
      (simTab eQ eA (hashOf eX eY H) u)]
    simp only [samplerW]
    rw [sum_ptTab_eq eX eY eQ eA (S.preW ks.2) (S.sum_preW ks.2)
      fun H tab => prOutMRGen (S.forgeGen eX eY eQ A ks.1 H) H tab]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [S.qStdAcc_B_psQ]
    simp only [psTabW, psLaw, Bool.false_eq_true, ↓reduceIte]
  set μ : (Fin m → Fin n) × (Msg × Fin T → Salt × (Tgt → Option Sig)) → ℝ≥0∞ := fun ω =>
    (Fintype.card (Fin m → Fin n) : ℝ≥0∞)⁻¹ *
      ∏ y, (Fintype.card Salt : ℝ≥0∞)⁻¹ * S.samplerW ks.2 (ω.2 y).2 with hμdef
  set lam : ℝ≥0∞ := ((T - 1 : ℕ) : ℝ≥0∞) * (Fintype.card Salt : ℝ≥0∞)⁻¹ with hlamdef
  have hwmass : ∀ _y : Msg × Fin T, ∑ x : Salt × (Tgt → Option Sig),
      (Fintype.card Salt : ℝ≥0∞)⁻¹ * S.samplerW ks.2 x.2 = 1 := fun _ => by
    have h := S.sum_salt_samplerW ks.2 fun _ => True
    simp only [↓reduceIte, mul_one, Finset.sum_const, Finset.card_univ, nsmul_eq_mul] at h
    rw [h, ENNReal.mul_inv_cancel (by simp) (ENNReal.natCast_ne_top _)]
  have hμ : ∑ ω, μ ω ≤ 1 := by
    have hu : ∑ u : Msg × Fin T → Salt × (Tgt → Option Sig),
        ∏ y, (Fintype.card Salt : ℝ≥0∞)⁻¹ * S.samplerW ks.2 (u y).2 = 1 :=
      sum_prod_eq_one (ι := Msg × Fin T) (β := Salt × (Tgt → Option Sig)) _ hwmass
    have h := hsplit fun _ _ => 1
    simp only [mul_one, hu] at h
    have h2 : ∑ ω, μ ω =
        ∑ _H : Fin m → Fin n, (Fintype.card (Fin m → Fin n) : ℝ≥0∞)⁻¹ := by
      rw [h]
    have hn := NeZero.ne n
    rw [h2, Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ENNReal.mul_inv_cancel (by simp [hn]) (ENNReal.natCast_ne_top _)]
  set E : (Fin m → Fin n) × (Msg × Fin T → Salt × (Tgt → Option Sig)) → Finset (Fin c) :=
    fun ω => Finset.univ.filter fun i => collides ω.2 (eQ.symm i) = true with hE
  have hf : ∀ ω i, i ∉ E ω → simTab eQ eA (hashOf eX eY ω.1) ω.2 i =
      honestTab eQ eA (hashOf eX eY ω.1) ω.2 i := by
    intro ω i hi
    simp only [hE, Finset.mem_filter, Finset.mem_univ, true_and, Bool.not_eq_true] at hi
    simp only [simTab, hi, Bool.false_eq_true, ↓reduceIte]
  have hloc : ∀ (H : Fin m → Fin n) u x i i', i' ≠ i →
      honestTab eQ eA (hashOf eX eY H) (Function.update u (eQ.symm i) x) i' =
        honestTab eQ eA (hashOf eX eY H) u i' := by
    intro H u x i i' hi'
    have hne : eQ.symm i' ≠ eQ.symm i := fun h => hi' (eQ.symm.injective h)
    simp only [honestTab, Function.update_of_ne hne]
  have hlam : ∀ (j : Fin m → Fin n) (i : Fin c) (h₀ : Fin m → Fin n) (g : Fin c → Fin a),
      ∑ ω, μ ω * (if ω.1 = j ∧ ω.1 = h₀ ∧ ∀ i', i' ≠ i →
          honestTab eQ eA (hashOf eX eY ω.1) ω.2 i' = g i' then 1 else 0) *
          (if i ∈ E ω then 1 else 0) ≤
        lam * ∑ ω, μ ω * (if ω.1 = j ∧ ω.1 = h₀ ∧ ∀ i', i' ≠ i →
          honestTab eQ eA (hashOf eX eY ω.1) ω.2 i' = g i' then 1 else 0) := by
    intro j i h₀ g
    set y₀ := eQ.symm i with hy₀
    have hcol : ∀ (u : Msg × Fin T → Salt × (Tgt → Option Sig)) x,
        collides (Function.update u y₀ x) y₀ =
        decide (∃ τ : Fin T, τ < y₀.2 ∧ (u (y₀.1, τ)).1 = x.1) := by
      intro u x
      have hne : ∀ τ : Fin T, τ < y₀.2 → (y₀.1, τ) ≠ y₀ := fun τ hτ h =>
        (ne_of_lt hτ) (congrArg Prod.snd h)
      simp only [collides, Function.update_self, decide_eq_decide]
      exact exists_congr fun τ => and_congr_right fun hτ => by
        rw [Function.update_of_ne (hne τ hτ)]
    rw [Fintype.sum_prod_type, Fintype.sum_prod_type, Finset.mul_sum]
    refine Finset.sum_le_sum fun H _ => ?_
    have scale : ∀ Φ β : (Msg × Fin T → Salt × (Tgt → Option Sig)) → ℝ≥0∞,
        ∑ u, (∏ y, (Fintype.card Salt : ℝ≥0∞)⁻¹ * S.samplerW ks.2 (u y).2) * Φ u * β u ≤
          lam * ∑ u, (∏ y, (Fintype.card Salt : ℝ≥0∞)⁻¹ * S.samplerW ks.2 (u y).2) * Φ u →
        ∑ u, μ (H, u) * Φ u * β u ≤ lam * ∑ u, μ (H, u) * Φ u := by
      intro Φ β hk
      have e1 : ∑ u, μ (H, u) * Φ u * β u = (Fintype.card (Fin m → Fin n) : ℝ≥0∞)⁻¹ *
          ∑ u, (∏ y, (Fintype.card Salt : ℝ≥0∞)⁻¹ * S.samplerW ks.2 (u y).2) * Φ u * β u := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun u _ => by simp only [hμdef]; ring
      have e2 : ∑ u, μ (H, u) * Φ u = (Fintype.card (Fin m → Fin n) : ℝ≥0∞)⁻¹ *
          ∑ u, (∏ y, (Fintype.card Salt : ℝ≥0∞)⁻¹ * S.samplerW ks.2 (u y).2) * Φ u := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun u _ => by simp only [hμdef]; ring
      rw [e1, e2, mul_left_comm]
      gcongr
    refine scale _ _ (sum_prod_mul_le_of_coord (ι := Msg × Fin T)
      (α := Salt × (Tgt → Option Sig))
      (fun _ x => (Fintype.card Salt : ℝ≥0∞)⁻¹ * S.samplerW ks.2 x.2) y₀ _ _ lam ?_ ?_)
    · intro u x
      have hiff : (∀ i', i' ≠ i → honestTab eQ eA (hashOf eX eY H)
            (Function.update u y₀ x) i' = g i') ↔
          (∀ i', i' ≠ i → honestTab eQ eA (hashOf eX eY H) u i' = g i') :=
        forall_congr' fun i' => imp_congr_right fun hi' => by rw [hloc H u x i i' hi']
      simp only [hiff]
    · intro u
      rw [hwmass y₀, mul_one]
      have hE' : ∀ x, (if i ∈ E (H, Function.update u y₀ x) then (1 : ℝ≥0∞) else 0) =
          if ∃ τ : Fin T, τ < y₀.2 ∧ (u (y₀.1, τ)).1 = x.1 then 1 else 0 := by
        intro x
        simp only [hE, Finset.mem_filter, Finset.mem_univ, true_and, ← hy₀, hcol,
          decide_eq_true_eq]
      simp only [hE']
      rw [S.sum_salt_samplerW ks.2 fun r => ∃ τ : Fin T, τ < y₀.2 ∧ (u (y₀.1, τ)).1 = r]
      exact sum_salt_collide_le y₀.2 fun τ => (u (y₀.1, τ)).1
  rw [hG0, hG1]
  exact rounds_upto_bad_local_dep (S.forgeGen eX eY eQ A ks.1) Prod.fst Prod.fst
    (fun ω => honestTab eQ eA (hashOf eX eY ω.1) ω.2)
    (fun ω => simTab eQ eA (hashOf eX eY ω.1) ω.2) E μ lam hμ hf hlam

/-- World `false` of `B_psQ`: the EUF-CMA advantage and the acceptance probability of `B_psQ` on
    the instances with the signer's preimages differ by at most `k (T - 1) / card Salt`. -/
theorem absDiff_qeufcma_psInst_false_le (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n)
    (eQ : Msg × Fin T ≃ Fin c) (eA : Option (Salt × Sig) ≃ Fin a)
    (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig)) :
    absDiff (qEUFCMAAdvantage S.toQROMSig eX eY eQ eA A)
      (sdExp (S.psInst (Msg × Salt) false) (qStdAcc (S.B_psQ eX eY eQ eA A))) ≤
      k * (((T - 1 : ℕ) : ℝ≥0∞) * (Fintype.card Salt : ℝ≥0∞)⁻¹) := by
  have hkey : ∑ ks, S.keygen ks = 1 := by
    rw [← tsum_fintype (L := SummationFilter.unconditional (PK × SK))]
    exact S.keygen.tsum_coe
  unfold qEUFCMAAdvantage
  rw [S.sdExp_psInst]
  refine (absDiff_sum_le _ _).trans ?_
  calc ∑ ks, absDiff (S.keygen ks * _) (S.keygen ks * _)
      ≤ ∑ ks, S.keygen ks *
          (k * (((T - 1 : ℕ) : ℝ≥0∞) * (Fintype.card Salt : ℝ≥0∞)⁻¹)) :=
        Finset.sum_le_sum fun ks _ => (absDiff_mul_left_le _ _ _).trans
          (by gcongr; exact S.absDiff_prForge_psInst_false_le eX eY eQ eA A ks)
    _ = _ := by rw [← Finset.sum_mul, hkey, one_mul]

/-- Hop A with the preimage-sampling game: the EUF-CMA advantage is at most the winning
    probability with the simulator's conditional samplers (`condGame`), plus the
    preimage-sampling advantage of `B_psQ` and the salt-collision term
    `k (T - 1) / card Salt`. -/
theorem saltedPSF_hopCondPS (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n)
    (eQ : Msg × Fin T ≃ Fin c) (eA : Option (Salt × Sig) ≃ Fin a)
    (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig)) :
    qEUFCMAAdvantage S.toQROMSig eX eY eQ eA A ≤
      S.condGame eX eY eQ eA A + S.psAdv (S.B_psQ eX eY eQ eA A) +
        k * (((T - 1 : ℕ) : ℝ≥0∞) * (Fintype.card Salt : ℝ≥0∞)⁻¹) := by
  have h1 := tsub_le_iff_left.mp
    ((le_sup_left).trans (S.absDiff_qeufcma_psInst_false_le eX eY eQ eA A))
  have h2 : sdExp (S.psInst (Msg × Salt) false) (qStdAcc (S.B_psQ eX eY eQ eA A)) ≤
      S.condGame eX eY eQ eA A + S.psAdv (S.B_psQ eX eY eQ eA A) := by
    rw [← S.psInst_true_B_psQ eX eY eQ eA A]
    exact tsub_le_iff_left.mp le_sup_left
  exact h1.trans (by gcongr)

/-- The statistical bound of the preimage-sampling advantage of `B_psQ`: it is at most
    `k · condDist + 2 k (T - 1) / card Salt`. -/
theorem psAdv_B_psQ_le (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n)
    (eQ : Msg × Fin T ≃ Fin c) (eA : Option (Salt × Sig) ≃ Fin a)
    (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig)) :
    S.psAdv (S.B_psQ eX eY eQ eA A) ≤
      k * S.condDist + 2 * k * (((T - 1 : ℕ) : ℝ≥0∞) * (Fintype.card Salt : ℝ≥0∞)⁻¹) := by
  have h0 := S.absDiff_qeufcma_psInst_false_le eX eY eQ eA A
  have h1 := S.saltedPSF_hopCond eX eY eQ eA A
  unfold psAdv qDistAdv
  rw [S.psInst_true_B_psQ eX eY eQ eA A]
  refine (absDiff_triangle _ (qEUFCMAAdvantage S.toQROMSig eX eY eQ eA A) _).trans ?_
  rw [absDiff_comm] at h0
  calc _ ≤ k * (((T - 1 : ℕ) : ℝ≥0∞) * (Fintype.card Salt : ℝ≥0∞)⁻¹) +
        k * (S.condDist + ((T - 1 : ℕ) : ℝ≥0∞) * (Fintype.card Salt : ℝ≥0∞)⁻¹) :=
        add_le_add h0 h1
    _ = _ := by ring

end Reduction

/-! ## The chains of hops with the preimage-sampling game -/

section Chains

variable [Fintype Sig] [DecidableEq Sig] [Fintype Tgt] [DecidableEq Tgt] [DecidableEq Salt]
  {m n w q k c a T : ℕ} [Fintype Msg] [DecidableEq Msg] [Fintype Salt] [Nonempty Salt]
  [NeZero m] [NeZero n] [NeZero c] [Fintype PK] [Fintype SK]

/-- Route I with the preimage-sampling game: the EUF-CMA advantage of salted hash-and-sign is
    at most `(2 Q + 1)²` times the inversion advantage of `B_invQ`, `Q = flatQ q k q`, plus the
    preimage-sampling advantage of `B_psQ` and `k (T - 1) / card Salt` (hop A),
    `4 (Q + 2 (k + 1)) domDist^(1/2)` (hop B) and `T / card Salt` (hop C). -/
theorem saltedPSF_qeufcma_le_inv_ps [Nonempty Tgt] (eX : Msg × Salt ≃ Fin m)
    (eY : Tgt ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c) (eA : Option (Salt × Sig) ≃ Fin a)
    (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig)) :
    qEUFCMAAdvantage S.toQROMSig eX eY eQ eA A ≤
      ((2 * flatQ q k q + 1 : ℕ) : ℝ≥0∞) ^ 2 *
          qSearchAdv S.invGame (S.B_invQ eX eY eQ eA A) (invOut A) +
        S.psAdv (S.B_psQ eX eY eQ eA A) +
        k * (((T - 1 : ℕ) : ℝ≥0∞) * (Fintype.card Salt : ℝ≥0∞)⁻¹) +
        4 * ((flatQ q k q + 2 * (k + 1) : ℕ) : ℝ≥0∞) * S.domDist ^ (1 / 2 : ℝ) +
        (T : ℝ≥0∞) * (Fintype.card Salt : ℝ≥0∞)⁻¹ := by
  have h1 := S.saltedPSF_hopCondPS eX eY eQ eA A
  have h2 := S.saltedPSF_offGraph eX eY eQ eA A
  have h3 := tsub_le_iff_left.mp ((le_sup_left).trans (S.saltedPSF_hopImage eX eY eQ eA A))
  have h4 := S.domGame_le_inv eX eY eQ eA A
  rw [S.imgGame_eq_domGame] at h3
  calc qEUFCMAAdvantage S.toQROMSig eX eY eQ eA A
      ≤ S.condGame eX eY eQ eA A + S.psAdv (S.B_psQ eX eY eQ eA A) +
          k * (((T - 1 : ℕ) : ℝ≥0∞) * (Fintype.card Salt : ℝ≥0∞)⁻¹) := h1
    _ ≤ ((((2 * flatQ q k q + 1 : ℕ) : ℝ≥0∞) ^ 2 *
            qSearchAdv S.invGame (S.B_invQ eX eY eQ eA A) (invOut A) +
          4 * ((flatQ q k q + 2 * (k + 1) : ℕ) : ℝ≥0∞) * S.domDist ^ (1 / 2 : ℝ)) +
          (T : ℝ≥0∞) * (Fintype.card Salt : ℝ≥0∞)⁻¹) + S.psAdv (S.B_psQ eX eY eQ eA A) +
          k * (((T - 1 : ℕ) : ℝ≥0∞) * (Fintype.card Salt : ℝ≥0∞)⁻¹) := by
        gcongr
        exact h2.trans (by gcongr; exact h3.trans (by gcongr))
    _ = _ := by ring

variable [Nonempty Sig]

/-- Route II with the preimage-sampling game: the EUF-CMA advantage of salted hash-and-sign is
    at most the collision advantage of `B_collQ` plus `preMass`, the preimage-sampling
    advantage of `B_psQ` and `k (T - 1) / card Salt` (hop A) and
    `4 (flatQ q k q + 2 (k + 1)) domDist^(1/2)` (hop B at every point), when domain samples are
    short. -/
theorem saltedPSF_qeufcma_le_coll_ps [Nonempty Tgt]
    (hshort : ∀ pk d, S.short pk (S.sampleDom pk d) = true)
    (eX : Msg × Salt ≃ Fin m) (eY : Tgt ≃ Fin n) (eQ : Msg × Fin T ≃ Fin c)
    (eA : Option (Salt × Sig) ≃ Fin a) (A : QSigAdv m n w q k c a T Msg PK (Salt × Sig)) :
    qEUFCMAAdvantage S.toQROMSig eX eY eQ eA A ≤
      qSearchAdv S.collGame (S.B_collQ eX eY eQ eA A) (collOut A) + S.preMass +
        S.psAdv (S.B_psQ eX eY eQ eA A) +
        k * (((T - 1 : ℕ) : ℝ≥0∞) * (Fintype.card Salt : ℝ≥0∞)⁻¹) +
        4 * ((flatQ q k q + 2 * (k + 1) : ℕ) : ℝ≥0∞) * S.domDist ^ (1 / 2 : ℝ) := by
  have h1 := S.saltedPSF_hopCondPS eX eY eQ eA A
  have h2 := tsub_le_iff_left.mp ((le_sup_left).trans (S.saltedPSF_hopAll eX eY eQ eA A))
  have h3 := S.domAllGame_le_coll hshort eX eY eQ eA A
  rw [← S.allGame_eq_domAllGame] at h3
  calc qEUFCMAAdvantage S.toQROMSig eX eY eQ eA A
      ≤ S.condGame eX eY eQ eA A + S.psAdv (S.B_psQ eX eY eQ eA A) +
          k * (((T - 1 : ℕ) : ℝ≥0∞) * (Fintype.card Salt : ℝ≥0∞)⁻¹) := h1
    _ ≤ ((S.preMass + qSearchAdv S.collGame (S.B_collQ eX eY eQ eA A) (collOut A)) +
          4 * ((flatQ q k q + 2 * (k + 1) : ℕ) : ℝ≥0∞) * S.domDist ^ (1 / 2 : ℝ)) +
          S.psAdv (S.B_psQ eX eY eQ eA A) +
          k * (((T - 1 : ℕ) : ℝ≥0∞) * (Fintype.card Salt : ℝ≥0∞)⁻¹) := by
        gcongr
        exact h2.trans (by gcongr)
    _ = _ := by ring

end Chains

/-- The salt terms of route I at `T = 2^20` and an `s`-bit salt: the salt-collision term of
    hop A and the term of hop C are together at most `(k + 1) 2^(20 - s)`. -/
theorem saltTerms_le (k s : ℕ) (hs : 20 ≤ s) :
    (k : ℝ≥0∞) * (((2 ^ 20 - 1 : ℕ) : ℝ≥0∞) * ((2 ^ s : ℕ) : ℝ≥0∞)⁻¹) +
        ((2 ^ 20 : ℕ) : ℝ≥0∞) * ((2 ^ s : ℕ) : ℝ≥0∞)⁻¹ ≤
      (k + 1 : ℝ≥0∞) * 2⁻¹ ^ (s - 20) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hs
  have he : ((2 ^ 20 : ℕ) : ℝ≥0∞) * ((2 ^ (20 + d) : ℕ) : ℝ≥0∞)⁻¹ = 2⁻¹ ^ (20 + d - 20) := by
    rw [Nat.add_sub_cancel_left, pow_add, Nat.cast_mul,
      ENNReal.mul_inv (Or.inl (by simp)) (Or.inl (by simp)), ← mul_assoc,
      ENNReal.mul_inv_cancel (by simp) (by simp), one_mul, Nat.cast_pow, Nat.cast_ofNat,
      ENNReal.inv_pow]
  have hle : ((2 ^ 20 - 1 : ℕ) : ℝ≥0∞) * ((2 ^ (20 + d) : ℕ) : ℝ≥0∞)⁻¹ ≤
      ((2 ^ 20 : ℕ) : ℝ≥0∞) * ((2 ^ (20 + d) : ℕ) : ℝ≥0∞)⁻¹ := by
    gcongr
    omega
  rw [he] at hle ⊢
  calc _ ≤ (k : ℝ≥0∞) * 2⁻¹ ^ (20 + d - 20) + 2⁻¹ ^ (20 + d - 20) := by gcongr
    _ = _ := by ring

end SaltedPSF

end CatCrypt.Quantum.QROM
