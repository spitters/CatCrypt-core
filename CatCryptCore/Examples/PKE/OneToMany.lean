/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
import CatCryptCore.Examples.PKE.Scheme

/-!
# Many-Time → One-Time CPA$ Reduction via SLIDE

This file implements Case Study 1 from "Mechanizing Nested Hybrid Arguments"
(Larsen & Schurmann, CSF 2025): reducing many-time CPA$ security to
one-time CPA$ security using the SLIDE construction.

## Main Results

* `dHybrid` - Decomposed hybrid game (equivalent to `hybrid_game` from Scheme)
* `dHybrid_zero` - Boundary: game 0 = MT_CPA_real
* `dHybrid_length` - Boundary: game n = MT_CPA_ideal
* `dHybrid_step_bound` - Per-step advantage ≤ OT-CPA$ advantage
* `Adv_MT_CPA_OT` - Main: `Adv(MT_CPA, A) ≤ q * max Adv(OT_CPA)`

## SLIDE Construction (Fig. 9)

The SLIDE oracle for hybrid index `i`:
- Query j < i: return random ciphertext (ideal)
- Query j = i: forward to single-instance oracle (real or ideal)
- Query j > i: encrypt the real message (real)

Adjacent hybrids differ only at position i: one encrypts, the other samples
random. This difference is exactly one OT-CPA$ query.

## References

* [Larsen & Schurmann, Mechanizing Nested Hybrid Arguments, CSF 2025, §4.1]
-/

namespace CatCrypt.Examples.PKE.OneToMany

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Relational
open CatCrypt.Crypto.HybridArgument
open CatCrypt.Examples.PKE
open scoped ENNReal

variable (P : PKEScheme)

/-! ## Decomposed Hybrid Game

    We define `dHybrid` as an alias for `hybrid_game` from Scheme.lean.
    The `hybrid_game` uses recursive `hybridLoop` with a position counter,
    which avoids the need for `LawfulMonad` instances. -/

/-- Decomposed hybrid game: first `i` positions get random ciphertexts,
    remaining positions get real encryptions.

    Equivalent to `hybrid_game` from Scheme.lean. -/
noncomputable def dHybrid (pk : P.PK) (msgs : List P.M) (i : ℕ) :
    SPComp (List P.C) :=
  hybrid_game P pk msgs i

/-! ## Boundary Conditions -/

/-- Boundary: dHybrid at 0 = all encrypted (real game). -/
theorem dHybrid_zero (pk : P.PK) (msgs : List P.M) :
    dHybrid P pk msgs 0 = MT_CPA_real P pk msgs :=
  hybrid_game_zero P pk msgs

/-- Boundary: dHybrid at length = all random (ideal game). -/
theorem dHybrid_length (pk : P.PK) (msgs : List P.M) :
    dHybrid P pk msgs msgs.length = MT_CPA_ideal P msgs :=
  hybrid_game_length P pk msgs

/-! ## Recursive Helpers

    These avoid `List.mapM` (which requires `LawfulMonad` for lemmas)
    by defining the prefix/suffix computations recursively. -/

/-- Sample `n` random ciphertexts. -/
private noncomputable def sampleN : ℕ → SPComp (List P.C)
  | 0 => SPComp.pure []
  | n + 1 => do
    let c ← P.sampleCip
    let cs ← sampleN n
    SPComp.pure (c :: cs)

/-- Encrypt a list of messages under a public key. -/
private noncomputable def encList (pk : P.PK) : List P.M → SPComp (List P.C)
  | [] => SPComp.pure []
  | m :: ms => do
    let c ← P.enc pk m
    let cs ← encList pk ms
    SPComp.pure (c :: cs)

/-! ## Structural helpers for hybridLoop -/

/-- Shifting both threshold and position by 1 is a no-op. -/
private theorem hybridLoop_shift (pk : P.PK) (i j : ℕ) (msgs : List P.M) :
    hybridLoop P pk (i + 1) (j + 1) msgs = hybridLoop P pk i j msgs := by
  induction msgs generalizing j with
  | nil => simp [hybridLoop]
  | cons m ms ih =>
    simp only [hybridLoop, Nat.add_lt_add_iff_right]
    by_cases hji : j < i <;>
      simp only [hji, ↓reduceIte, SPComp.monad_bind_eq] <;>
      (congr 1; funext c; congr 1; exact ih (j + 1))

/-- When threshold ≤ position, hybridLoop encrypts everything = encList. -/
private theorem hybridLoop_suffix_eq_encList (pk : P.PK) (i j : ℕ) (msgs : List P.M)
    (hj : i ≤ j) :
    hybridLoop P pk i j msgs = encList P pk msgs := by
  induction msgs generalizing j with
  | nil => simp [hybridLoop, encList]
  | cons m ms ih =>
    simp only [hybridLoop, encList]
    have : ¬(j < i) := by omega
    simp only [this, ↓reduceIte, SPComp.monad_bind_eq]
    congr 1; funext c; congr 1; exact ih (j + 1) (by omega)

/-! ## IsPure helpers -/

private theorem sampleN_isPure (hP : P.IsPure) : ∀ n, SPComp.IsPure (sampleN P n)
  | 0 => SPComp.pure_isPure []
  | n + 1 => by
    exact SPComp.bind_isPure hP.sampleCip_isPure fun c =>
      SPComp.bind_isPure (sampleN_isPure hP n) fun cs => SPComp.pure_isPure (c :: cs)

private theorem encList_isPure (hP : P.IsPure) (pk : P.PK) :
    ∀ ms, SPComp.IsPure (encList P pk ms)
  | [] => SPComp.pure_isPure []
  | m :: ms => by
    exact SPComp.bind_isPure (hP.enc_isPure pk m) fun c =>
      SPComp.bind_isPure (encList_isPure hP pk ms) fun cs => SPComp.pure_isPure (c :: cs)

/-! ## Decomposition Lemmas

    These show that `hybridLoop` decomposes as: sample prefix + core + encrypt suffix.
    Proved by induction on `i` (the switch position), using `hybridLoop_shift` to
    reduce the successor case to the base case on the tail of the message list. -/

private theorem hybridLoop_decomp_enc (pk : P.PK) :
    ∀ (i : ℕ) (msgs : List P.M) (hi : i < msgs.length),
    hybridLoop P pk i 0 msgs =
    (sampleN P i).bind fun pre =>
    (P.enc pk msgs[i]).bind fun c =>
    (encList P pk (msgs.drop (i + 1))).bind fun suf =>
    SPComp.pure (pre ++ [c] ++ suf)
  | 0, m :: ms, _ => by
    simp only [hybridLoop, Nat.not_lt_zero, ↓reduceIte, SPComp.monad_bind_eq,
               sampleN, SPComp.pure_bind, List.getElem_cons_zero, List.drop, List.nil_append]
    congr 1; funext c; rw [hybridLoop_suffix_eq_encList P pk 0 1 ms (by omega)]; rfl
  | i + 1, m :: ms, hi => by
    simp only [hybridLoop, Nat.zero_lt_succ, ↓reduceIte, SPComp.monad_bind_eq]
    conv_lhs => arg 2; ext c0; arg 1; rw [hybridLoop_shift]
    have hms : i < ms.length := by simp at hi; omega
    simp_rw [hybridLoop_decomp_enc pk i ms hms]
    simp only [SPComp.bind_assoc, SPComp.pure_bind]
    conv_rhs =>
      rw [sampleN]; simp only [SPComp.monad_bind_eq, SPComp.bind_assoc, SPComp.pure_bind]
    rfl

private theorem hybridLoop_decomp_samp (pk : P.PK) :
    ∀ (i : ℕ) (msgs : List P.M) (_hi : i < msgs.length),
    hybridLoop P pk (i + 1) 0 msgs =
    (sampleN P i).bind fun pre =>
    P.sampleCip.bind fun c =>
    (encList P pk (msgs.drop (i + 1))).bind fun suf =>
    SPComp.pure (pre ++ [c] ++ suf)
  | 0, m :: ms, _ => by
    simp only [hybridLoop, Nat.zero_lt_succ, ↓reduceIte, SPComp.monad_bind_eq,
               sampleN, SPComp.pure_bind, List.drop, List.nil_append]
    congr 1; funext c; rw [hybridLoop_suffix_eq_encList P pk 1 1 ms (by omega)]; rfl
  | i + 1, m :: ms, _hi => by
    simp only [hybridLoop, show (0 : ℕ) < i + 2 from by omega, ↓reduceIte, SPComp.monad_bind_eq]
    conv_lhs => arg 2; ext c0; arg 1; rw [show i + 2 = (i + 1) + 1 from by omega, hybridLoop_shift]
    have hms : i < ms.length := by simp at _hi; omega
    simp_rw [hybridLoop_decomp_samp pk i ms hms]
    simp only [SPComp.bind_assoc, SPComp.pure_bind]
    conv_rhs =>
      rw [sampleN]; simp only [SPComp.monad_bind_eq, SPComp.bind_assoc, SPComp.pure_bind]
    rfl

/-! ## The SLIDE Adversary

    The "context" adversary: given a single ciphertext at position i,
    fills in the prefix with random ciphertexts and suffix with real
    encryptions, then runs the original adversary on the assembled list. -/

/-- SLIDE adversary: embeds a single ciphertext into the full list context.

    Samples `min i msgs.length` random prefix ciphertexts,
    encrypts suffix messages from position `i + 1` onward. -/
noncomputable def slideAdv (pk : P.PK) (msgs : List P.M) (i : ℕ)
    (A : List P.C → SPComp Bool) (c : P.C) : SPComp Bool := do
  let pre ← sampleN P (min i msgs.length)
  let suf ← encList P pk (msgs.drop (i + 1))
  A (pre ++ [c] ++ suf)

/-! ## Per-Step Advantage Bound -/

/-- **Per-step advantage equality**: adjacent hybrid advantage = OT-CPA$ advantage.

    Theorem 4 (CSF 2025). Equality is established by decomposing both hybrids and
    commuting the prefix past the core operation using `P.IsPure`. -/
theorem dHybrid_step_eq (pk : P.PK) (msgs : List P.M) (i : ℕ) (hi : i < msgs.length)
    (A : List P.C → SPComp Bool) (hP : P.IsPure) :
    AdvantageA (dHybrid P pk msgs i) (dHybrid P pk msgs (i + 1)) A =
    OT_CPA_Advantage P pk msgs[i] (slideAdv P pk msgs i A) := by
  unfold dHybrid hybrid_game OT_CPA_Advantage OT_CPA_real OT_CPA_ideal AdvantageA
  rw [hybridLoop_decomp_enc P pk i msgs hi, hybridLoop_decomp_samp P pk i msgs hi]
  have hmin : min i msgs.length = i := by omega
  have heq_enc : ((sampleN P i).bind fun pre => (P.enc pk msgs[i]).bind fun c =>
      (encList P pk (msgs.drop (i + 1))).bind fun suf =>
      SPComp.pure (pre ++ [c] ++ suf)).bind A =
    (P.enc pk msgs[i]).bind (slideAdv P pk msgs i A) := by
    simp only [SPComp.bind_assoc, SPComp.pure_bind]
    rw [SPComp.isPure_bind_comm (sampleN P i) (P.enc pk msgs[i])
      (fun pre c => (encList P pk (msgs.drop (i + 1))).bind fun suf => A (pre ++ [c] ++ suf))
      (sampleN_isPure P hP i) (hP.enc_isPure pk msgs[i])]
    congr 1; funext c
    simp only [slideAdv, hmin, SPComp.monad_bind_eq]
  have heq_samp : ((sampleN P i).bind fun pre => P.sampleCip.bind fun c =>
      (encList P pk (msgs.drop (i + 1))).bind fun suf =>
      SPComp.pure (pre ++ [c] ++ suf)).bind A =
    P.sampleCip.bind (slideAdv P pk msgs i A) := by
    simp only [SPComp.bind_assoc, SPComp.pure_bind]
    rw [SPComp.isPure_bind_comm (sampleN P i) P.sampleCip
      (fun pre c => (encList P pk (msgs.drop (i + 1))).bind fun suf => A (pre ++ [c] ++ suf))
      (sampleN_isPure P hP i) hP.sampleCip_isPure]
    congr 1; funext c
    simp only [slideAdv, hmin, SPComp.monad_bind_eq]
  show Advantage _ _ = Advantage _ _
  rw [heq_enc, heq_samp]

/-- **Per-step advantage reduction**: adjacent hybrid advantage ≤ OT-CPA$ advantage.

    Requires `P.IsPure` to commute the prefix sampling past enc/sampleCip. -/
theorem dHybrid_step_bound (pk : P.PK) (msgs : List P.M) (i : ℕ) (hi : i < msgs.length)
    (A : List P.C → SPComp Bool) (hP : P.IsPure) :
    AdvantageA (dHybrid P pk msgs i) (dHybrid P pk msgs (i + 1)) A ≤
    OT_CPA_Advantage P pk msgs[i] (slideAdv P pk msgs i A) :=
  (dHybrid_step_eq P pk msgs i hi A hP).le

/-- `dHybrid_step_bound` follows from `dHybrid_step_eq`. -/
theorem dHybrid_step_bound' (pk : P.PK) (msgs : List P.M) (i : ℕ) (hi : i < msgs.length)
    (A : List P.C → SPComp Bool) (hP : P.IsPure) :
    AdvantageA (dHybrid P pk msgs i) (dHybrid P pk msgs (i + 1)) A ≤
    OT_CPA_Advantage P pk msgs[i] (slideAdv P pk msgs i A) :=
  (dHybrid_step_eq P pk msgs i hi A hP).le

/-! ## Main Reduction Theorems -/

/-- **Many-time to one-time CPA$ reduction** (CSF 2025, Theorem 1).

    `Adv(MT_CPA, A) ≤ q * max_i OT_CPA_Advantage(m_i, slideAdv_i)`

    Requires `P.IsPure` for the per-step decomposition. -/
theorem Adv_MT_CPA_OT (pk : P.PK) (msgs : List P.M) (ε : ℝ≥0∞)
    (A : List P.C → SPComp Bool) (hP : P.IsPure)
    (hOT : ∀ i (hi : i < msgs.length),
      OT_CPA_Advantage P pk msgs[i] (slideAdv P pk msgs i A) ≤ ε) :
    MT_CPA_Advantage P pk msgs A ≤ msgs.length * ε := by
  unfold MT_CPA_Advantage
  rw [← dHybrid_zero P pk msgs, ← dHybrid_length P pk msgs]
  apply advantage_hybrid_uniform (dHybrid P pk msgs) A msgs.length ε
  intro i hi
  calc AdvantageA (dHybrid P pk msgs i) (dHybrid P pk msgs (i + 1)) A
      ≤ OT_CPA_Advantage P pk msgs[i] (slideAdv P pk msgs i A) :=
        dHybrid_step_bound P pk msgs i hi A hP
    _ ≤ ε := hOT i hi

/-- **Alternative: MT-CPA bound with explicit per-step hypothesis**.

    This version takes the per-step bound directly as a hypothesis,
    without requiring it to be bounded by OT-CPA.
    Useful when the step bound comes from a different source. -/
theorem Adv_MT_CPA_direct (pk : P.PK) (msgs : List P.M) (ε : ℝ≥0∞)
    (A : List P.C → SPComp Bool)
    (hstep : ∀ i, i < msgs.length →
      AdvantageA (dHybrid P pk msgs i) (dHybrid P pk msgs (i + 1)) A ≤ ε) :
    MT_CPA_Advantage P pk msgs A ≤ msgs.length * ε := by
  unfold MT_CPA_Advantage
  rw [← dHybrid_zero P pk msgs, ← dHybrid_length P pk msgs]
  exact advantage_hybrid_uniform (dHybrid P pk msgs) A msgs.length ε hstep

/-- **Perfect security for many-time CPA$**: when all hybrid steps are
    perfectly indistinguishable, the advantage is 0. -/
theorem MT_CPA_perfect (pk : P.PK) (msgs : List P.M)
    (hperf : ∀ i, i < msgs.length →
      rHoare eqPre (dHybrid P pk msgs i) (dHybrid P pk msgs (i + 1)) eqPost)
    (A : List P.C → SPComp Bool) :
    MT_CPA_Advantage P pk msgs A = 0 := by
  unfold MT_CPA_Advantage
  rw [← dHybrid_zero P pk msgs, ← dHybrid_length P pk msgs]
  exact advantage_hybrid_zero (dHybrid P pk msgs) msgs.length hperf A

end CatCrypt.Examples.PKE.OneToMany
