/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Examples.PKE.OneToMany

/-!
# Multi-Instance → Single-Instance Reduction (Case Study 2)

This file implements Case Study 2 from "Mechanizing Nested Hybrid Arguments"
(Larsen & Schurmann, CSF 2025): reducing multi-instance CPA$ security to
single-instance (many-time) CPA$ security using a second layer of SLIDE.

## Main Results

* `MI_hybrid` - Hybrid game indexed by instance switch position
* `MI_slideAdv` - SLIDE adversary for the instance dimension
* `MI_step_eq` - Per-step: `Adv(MI_hybrid i, MI_hybrid (i+1)) = MT_CPA_Advantage`
* `Adv_MI_MT_CPA` - Main: `Adv(MI, A) ≤ n * ε` where n = number of instances
* `Adv_MI_MT_CPA_nested` - Composed: `Adv(MI, A) ≤ n * q * ε_OT`

## References

* [Larsen & Schurmann, Mechanizing Nested Hybrid Arguments, CSF 2025, §4.2]
-/

namespace CatCrypt.Examples.PKE.MultiInstance

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Relational
open CatCrypt.Crypto.HybridArgument
open CatCrypt.Examples.PKE CatCrypt.Examples.PKE.OneToMany
open scoped ENNReal

variable (P : PKEScheme)

/-- Default public key (for out-of-bounds access via `List.getD`). -/
noncomputable def defPK : P.PK := Classical.arbitrary P.PK

/-! ## Multi-Instance Hybrid Game -/

/-- Multi-instance hybrid loop with position counter `j` and threshold `i`.
    When `j < i`: use MT_CPA_ideal (random ciphertexts).
    When `j ≥ i`: use MT_CPA_real (encrypted ciphertexts). -/
noncomputable def MI_hybridLoop (pks : List P.PK) (i : ℕ) :
    ℕ → List (List P.M) → SPComp (List (List P.C))
  | _, [] => SPComp.pure []
  | j, m :: ms => do
    let cs ← if j < i then MT_CPA_ideal P m
              else MT_CPA_real P (pks.getD j (defPK P)) m
    let rest ← MI_hybridLoop pks i (j + 1) ms
    SPComp.pure (cs :: rest)

/-- Multi-instance hybrid game: first `i` instances ideal, rest real. -/
noncomputable def MI_hybrid (pks : List P.PK) (msgs : List (List P.M)) (i : ℕ) :
    SPComp (List (List P.C)) :=
  MI_hybridLoop P pks i 0 msgs

/-- Multi-instance advantage. -/
noncomputable def MI_Advantage (pks : List P.PK) (msgs : List (List P.M))
    (A : List (List P.C) → SPComp Bool) : ℝ≥0∞ :=
  AdvantageA (MI_hybrid P pks msgs 0) (MI_hybrid P pks msgs msgs.length) A

/-! ## Prefix/Suffix Helpers -/

/-- Sample `n` instances as ideal (random) ciphertexts. -/
private noncomputable def MI_sampleN :
    ℕ → List (List P.M) → SPComp (List (List P.C))
  | 0, _ => SPComp.pure []
  | _ + 1, [] => SPComp.pure []
  | _ + 1, m :: ms => do
    let cs ← MT_CPA_ideal P m
    let rest ← MI_sampleN ‹_› ms
    SPComp.pure (cs :: rest)

/-- Encrypt instances under their keys (all real), starting at position `j`. -/
private noncomputable def MI_encList (pks : List P.PK) :
    ℕ → List (List P.M) → SPComp (List (List P.C))
  | _, [] => SPComp.pure []
  | j, m :: ms => do
    let cs ← MT_CPA_real P (pks.getD j (defPK P)) m
    let rest ← MI_encList pks (j + 1) ms
    SPComp.pure (cs :: rest)

/-! ## Boundary Conditions -/

private theorem MI_hybridLoop_zero_eq (pks : List P.PK) (j : ℕ) (msgs : List (List P.M)) :
    MI_hybridLoop P pks 0 j msgs = MI_encList P pks j msgs := by
  induction msgs generalizing j with
  | nil => simp [MI_hybridLoop, MI_encList]
  | cons m ms ih =>
    simp only [MI_hybridLoop, Nat.not_lt_zero, ↓reduceIte, MI_encList, SPComp.monad_bind_eq, ih]

private theorem MI_hybridLoop_full_eq (pks : List P.PK) (j : ℕ) (msgs : List (List P.M))
    {thresh : ℕ} (hi : j + msgs.length ≤ thresh) :
    MI_hybridLoop P pks thresh j msgs = MI_sampleN P msgs.length msgs := by
  induction msgs generalizing j with
  | nil => simp [MI_hybridLoop, MI_sampleN]
  | cons m ms ih =>
    simp only [MI_hybridLoop, MI_sampleN, SPComp.monad_bind_eq]
    have hlen : (m :: ms).length = ms.length + 1 := rfl
    have : j < thresh := by omega
    simp only [this, ↓reduceIte]
    simp_rw [ih (j + 1) (by omega)]

theorem MI_hybrid_length (pks : List P.PK) (msgs : List (List P.M)) :
    MI_hybrid P pks msgs msgs.length = MI_sampleN P msgs.length msgs :=
  MI_hybridLoop_full_eq P pks 0 msgs (by omega)

/-- When threshold ≤ position, MI_hybridLoop encrypts everything. -/
private theorem MI_hybridLoop_suffix_eq (pks : List P.PK) (i j : ℕ)
    (msgs : List (List P.M)) (hj : i ≤ j) :
    MI_hybridLoop P pks i j msgs = MI_encList P pks j msgs := by
  induction msgs generalizing j with
  | nil => simp [MI_hybridLoop, MI_encList]
  | cons m ms ih =>
    simp only [MI_hybridLoop, MI_encList]
    have : ¬(j < i) := by omega
    simp only [this, ↓reduceIte, SPComp.monad_bind_eq]
    simp_rw [ih (j + 1) (by omega)]

/-! ## IsPure Lemmas -/

private theorem MI_sampleN_isPure (hP : P.IsPure) :
    ∀ (n : ℕ) (msgs : List (List P.M)), SPComp.IsPure (MI_sampleN P n msgs)
  | 0, _ => SPComp.pure_isPure []
  | _ + 1, [] => SPComp.pure_isPure []
  | n + 1, m :: ms => by
    simp only [MI_sampleN, SPComp.monad_bind_eq]
    exact SPComp.bind_isPure (MT_CPA_ideal_isPure P hP m) (fun cs =>
      SPComp.bind_isPure (MI_sampleN_isPure hP n ms) (fun rest =>
        SPComp.pure_isPure (cs :: rest)))

private theorem MI_encList_isPure (hP : P.IsPure) (pks : List P.PK) :
    ∀ (j : ℕ) (msgs : List (List P.M)), SPComp.IsPure (MI_encList P pks j msgs)
  | _, [] => SPComp.pure_isPure []
  | j, m :: ms => by
    simp only [MI_encList, SPComp.monad_bind_eq]
    exact SPComp.bind_isPure (MT_CPA_real_isPure P hP _ m) (fun cs =>
      SPComp.bind_isPure (MI_encList_isPure hP pks (j + 1) ms) (fun rest =>
        SPComp.pure_isPure (cs :: rest)))

/-! ## Decomposition Lemmas

    We decompose `MI_hybridLoop pks (j + k) j msgs` as:
    prefix (k ideal instances) + core (at position j + k) + suffix (real instances).

    The generalized form over `(j, k)` avoids the "shift" trick, which fails
    when public keys are indexed by position (`pks.getD j`). Instead, the IH
    works because `(j+1) + k = j + (k+1)` preserves the `pks.getD` index. -/

/-- Generalized decomposition with real core at position `j + k`. -/
private theorem MI_hybridLoop_decomp_real_gen (pks : List P.PK) :
    ∀ (j k : ℕ) (msgs : List (List P.M)) (_hk : k < msgs.length),
    MI_hybridLoop P pks (j + k) j msgs =
    (MI_sampleN P k msgs).bind fun pre =>
    (MT_CPA_real P (pks.getD (j + k) (defPK P)) (msgs.getD k [])).bind fun cs =>
    (MI_encList P pks (j + k + 1) (msgs.drop (k + 1))).bind fun suf =>
    SPComp.pure (pre ++ [cs] ++ suf)
  | j, 0, m :: ms, _ => by
    simp only [Nat.add_zero, MI_hybridLoop, Nat.lt_irrefl, ↓reduceIte, SPComp.monad_bind_eq,
               MI_sampleN, SPComp.pure_bind, List.getD_cons_zero, List.drop]
    simp only [MI_hybridLoop_suffix_eq P pks j (j + 1) ms (by omega),
      List.nil_append, List.cons_append]
  | j, k + 1, m :: ms, hk => by
    have hlt : j < j + (k + 1) := by omega
    simp only [MI_hybridLoop, hlt, ↓reduceIte, SPComp.monad_bind_eq]
    have hms : k < ms.length := by simp at hk; omega
    rw [show j + (k + 1) = (j + 1) + k from by omega]
    simp_rw [MI_hybridLoop_decomp_real_gen pks (j + 1) k ms hms]
    simp only [SPComp.bind_assoc, SPComp.pure_bind]
    conv_rhs =>
      rw [MI_sampleN]; simp only [SPComp.monad_bind_eq, SPComp.bind_assoc, SPComp.pure_bind]
    simp only [List.getD_cons_succ, List.drop_succ_cons]
    congr 1

/-- Generalized decomposition with ideal core at position `j + k`. -/
private theorem MI_hybridLoop_decomp_ideal_gen (pks : List P.PK) :
    ∀ (j k : ℕ) (msgs : List (List P.M)) (_hk : k < msgs.length),
    MI_hybridLoop P pks (j + k + 1) j msgs =
    (MI_sampleN P k msgs).bind fun pre =>
    (MT_CPA_ideal P (msgs.getD k [])).bind fun cs =>
    (MI_encList P pks (j + k + 1) (msgs.drop (k + 1))).bind fun suf =>
    SPComp.pure (pre ++ [cs] ++ suf)
  | j, 0, m :: ms, _ => by
    simp only [Nat.add_zero, MI_hybridLoop, show j < j + 0 + 1 from by omega,
               ↓reduceIte, SPComp.monad_bind_eq,
               MI_sampleN, SPComp.pure_bind, List.getD_cons_zero, List.drop]
    simp only [MI_hybridLoop_suffix_eq P pks (j + 1) (j + 1) ms (by omega),
      List.nil_append, List.cons_append]
  | j, k + 1, m :: ms, hk => by
    have hlt : j < j + (k + 1) + 1 := by omega
    simp only [MI_hybridLoop, hlt, ↓reduceIte, SPComp.monad_bind_eq]
    have hms : k < ms.length := by simp at hk; omega
    rw [show j + (k + 1) + 1 = (j + 1) + k + 1 from by omega]
    simp_rw [MI_hybridLoop_decomp_ideal_gen pks (j + 1) k ms hms]
    simp only [SPComp.bind_assoc, SPComp.pure_bind]
    conv_rhs =>
      rw [MI_sampleN]; simp only [SPComp.monad_bind_eq, SPComp.bind_assoc, SPComp.pure_bind]
    simp only [List.getD_cons_succ, List.drop_succ_cons]
    congr 1

/-- Decomposition with real core, specialized to position 0. -/
private theorem MI_hybridLoop_decomp_real (pks : List P.PK) (i : ℕ) (msgs : List (List P.M))
    (hi : i < msgs.length) :
    MI_hybridLoop P pks i 0 msgs =
    (MI_sampleN P i msgs).bind fun pre =>
    (MT_CPA_real P (pks.getD i (defPK P)) (msgs.getD i [])).bind fun cs =>
    (MI_encList P pks (i + 1) (msgs.drop (i + 1))).bind fun suf =>
    SPComp.pure (pre ++ [cs] ++ suf) := by
  simpa only [Nat.zero_add] using MI_hybridLoop_decomp_real_gen P pks 0 i msgs hi

/-- Decomposition with ideal core, specialized to position 0. -/
private theorem MI_hybridLoop_decomp_ideal (pks : List P.PK) (i : ℕ) (msgs : List (List P.M))
    (hi : i < msgs.length) :
    MI_hybridLoop P pks (i + 1) 0 msgs =
    (MI_sampleN P i msgs).bind fun pre =>
    (MT_CPA_ideal P (msgs.getD i [])).bind fun cs =>
    (MI_encList P pks (i + 1) (msgs.drop (i + 1))).bind fun suf =>
    SPComp.pure (pre ++ [cs] ++ suf) := by
  simpa only [Nat.zero_add] using MI_hybridLoop_decomp_ideal_gen P pks 0 i msgs hi

/-! ## The SLIDE Adversary (Instance Dimension) -/

/-- SLIDE adversary for the instance dimension: embeds a single instance's
    ciphertext list into the multi-instance context. -/
noncomputable def MI_slideAdv (pks : List P.PK) (msgs : List (List P.M)) (i : ℕ)
    (A : List (List P.C) → SPComp Bool) (cs : List P.C) : SPComp Bool := do
  let pre ← MI_sampleN P (min i msgs.length) msgs
  let suf ← MI_encList P pks (i + 1) (msgs.drop (i + 1))
  A (pre ++ [cs] ++ suf)

/-! ## Per-Step Advantage Bound -/

/-- **Per-step advantage equality**: adjacent MI hybrids differ by one MT-CPA$ query. -/
theorem MI_step_eq (pks : List P.PK) (msgs : List (List P.M)) (i : ℕ) (hi : i < msgs.length)
    (A : List (List P.C) → SPComp Bool) (hP : P.IsPure) :
    AdvantageA (MI_hybrid P pks msgs i) (MI_hybrid P pks msgs (i + 1)) A =
    MT_CPA_Advantage P (pks.getD i (defPK P)) (msgs.getD i [])
      (MI_slideAdv P pks msgs i A) := by
  unfold MI_hybrid MT_CPA_Advantage AdvantageA
  rw [MI_hybridLoop_decomp_real P pks i msgs hi,
      MI_hybridLoop_decomp_ideal P pks i msgs hi]
  have hmin : min i msgs.length = i := by omega
  have heq_real :
      ((MI_sampleN P i msgs).bind fun pre =>
       (MT_CPA_real P (pks.getD i (defPK P)) (msgs.getD i [])).bind fun cs =>
       (MI_encList P pks (i + 1) (msgs.drop (i + 1))).bind fun suf =>
       SPComp.pure (pre ++ [cs] ++ suf)).bind A =
      (MT_CPA_real P (pks.getD i (defPK P)) (msgs.getD i [])).bind
        (MI_slideAdv P pks msgs i A) := by
    simp only [SPComp.bind_assoc, SPComp.pure_bind]
    rw [SPComp.isPure_bind_comm (MI_sampleN P i msgs)
        (MT_CPA_real P (pks.getD i (defPK P)) (msgs.getD i []))
        (fun pre cs => (MI_encList P pks (i + 1) (msgs.drop (i + 1))).bind fun suf =>
          A (pre ++ [cs] ++ suf))
        (MI_sampleN_isPure P hP i msgs)
        (MT_CPA_real_isPure P hP _ (msgs.getD i []))]
    congr 1; funext cs
    simp only [MI_slideAdv, hmin, SPComp.monad_bind_eq]
  have heq_ideal :
      ((MI_sampleN P i msgs).bind fun pre =>
       (MT_CPA_ideal P (msgs.getD i [])).bind fun cs =>
       (MI_encList P pks (i + 1) (msgs.drop (i + 1))).bind fun suf =>
       SPComp.pure (pre ++ [cs] ++ suf)).bind A =
      (MT_CPA_ideal P (msgs.getD i [])).bind
        (MI_slideAdv P pks msgs i A) := by
    simp only [SPComp.bind_assoc, SPComp.pure_bind]
    rw [SPComp.isPure_bind_comm (MI_sampleN P i msgs)
        (MT_CPA_ideal P (msgs.getD i []))
        (fun pre cs => (MI_encList P pks (i + 1) (msgs.drop (i + 1))).bind fun suf =>
          A (pre ++ [cs] ++ suf))
        (MI_sampleN_isPure P hP i msgs)
        (MT_CPA_ideal_isPure P hP (msgs.getD i []))]
    congr 1; funext cs
    simp only [MI_slideAdv, hmin, SPComp.monad_bind_eq]
  show Advantage _ _ = Advantage _ _
  rw [heq_real, heq_ideal]

/-- Per-step advantage bound (≤ version). -/
theorem MI_step_bound (pks : List P.PK) (msgs : List (List P.M)) (i : ℕ) (hi : i < msgs.length)
    (A : List (List P.C) → SPComp Bool) (hP : P.IsPure) :
    AdvantageA (MI_hybrid P pks msgs i) (MI_hybrid P pks msgs (i + 1)) A ≤
    MT_CPA_Advantage P (pks.getD i (defPK P)) (msgs.getD i [])
      (MI_slideAdv P pks msgs i A) :=
  (MI_step_eq P pks msgs i hi A hP).le

/-! ## Main Reduction Theorems -/

/-- **Multi-instance to single-instance reduction** (CSF 2025, Case Study 2). -/
theorem Adv_MI_MT_CPA (pks : List P.PK) (msgs : List (List P.M)) (ε : ℝ≥0∞)
    (A : List (List P.C) → SPComp Bool) (hP : P.IsPure)
    (hMT : ∀ i, i < msgs.length →
      MT_CPA_Advantage P (pks.getD i (defPK P)) (msgs.getD i [])
        (MI_slideAdv P pks msgs i A) ≤ ε) :
    MI_Advantage P pks msgs A ≤ msgs.length * ε := by
  unfold MI_Advantage
  apply advantage_hybrid_uniform (MI_hybrid P pks msgs) A msgs.length ε
  intro i hi
  calc AdvantageA (MI_hybrid P pks msgs i) (MI_hybrid P pks msgs (i + 1)) A
      ≤ MT_CPA_Advantage P (pks.getD i (defPK P)) (msgs.getD i [])
          (MI_slideAdv P pks msgs i A) :=
        MI_step_bound P pks msgs i hi A hP
    _ ≤ ε := hMT i hi

/-- **Alternative: MI-CPA bound with explicit per-step hypothesis**. -/
theorem Adv_MI_direct (pks : List P.PK) (msgs : List (List P.M)) (ε : ℝ≥0∞)
    (A : List (List P.C) → SPComp Bool)
    (hstep : ∀ i, i < msgs.length →
      AdvantageA (MI_hybrid P pks msgs i) (MI_hybrid P pks msgs (i + 1)) A ≤ ε) :
    MI_Advantage P pks msgs A ≤ msgs.length * ε := by
  unfold MI_Advantage
  exact advantage_hybrid_uniform (MI_hybrid P pks msgs) A msgs.length ε hstep

/-- **Nested hybrid composition** (CSF 2025, combining Cases 1 & 2). -/
theorem Adv_MI_MT_CPA_nested (pks : List P.PK) (msgs : List (List P.M))
    (q : ℕ) (ε : ℝ≥0∞)
    (A : List (List P.C) → SPComp Bool) (hP : P.IsPure)
    (hMT : ∀ i, i < msgs.length →
      MT_CPA_Advantage P (pks.getD i (defPK P)) (msgs.getD i [])
        (MI_slideAdv P pks msgs i A) ≤ q * ε) :
    MI_Advantage P pks msgs A ≤ msgs.length * q * ε := by
  calc MI_Advantage P pks msgs A ≤ msgs.length * (q * ε) :=
        Adv_MI_MT_CPA P pks msgs (q * ε) A hP hMT
    _ = msgs.length * q * ε := by ring

end CatCrypt.Examples.PKE.MultiInstance
