/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.MLKEM.MLWE
public import CatCryptCore.Crypto.MLKEM.Infrastructure.FEL

/-!
# Basic MLWE-PKE: CPA Security from MLWE

This file defines the basic MLWE-based PKE scheme and proves its IND-CPA security
reduces to the MLWE assumption via a 2-hop argument, for adversaries whose guess
stage receives neither the public key nor a state. The game for two-stage
adversaries with state, `CPA_Adv_st`, and its bound `main_theorem_st` are in
`MLWE_PKE_Stateful`; they supersede `CPA_Game`, `CPA_Adv` and `main_theorem`
here.

Ports `MLWE_PKE_Basic.ec` from `formosa-crypto/formosa-mlkem`.

## Proof structure

```
CPA(BASIC, A)
    = MLWE(B1).main(false)           [hop1_left]
    → MLWE(B1).main(true)             [MLWE assumption]
    = CPA(BASIC1, A)                  [hop1_right]
    = MLWE_Ext(B2_ext).main(false)   [hop2_left]
    → MLWE_Ext(B2_ext).main(true)     [MLWE_Ext assumption]
    = CPA(BASIC2, A)                  [hop2_right]
    = 1/2                              [BASIC2 is independent of b]
```

The second hop uses an *extended* MLWE game (`MLWE_Ext_Game`) that produces
both a vector and scalar challenge sharing the same secret. This avoids the
correlation issue with the standard MLWE game (where the adversary cannot
compute `⟨t, r⟩` from the MLWE challenge `A^T·r+e1` without knowing `r`).

## Correctness

`correctness_le_corrWorst` bounds the adversarial correctness game by the
worst-case decryption-failure probability `corrWorst`. It replaces
`correctness_theorem`, whose hypothesis was its conclusion.

## References

* EasyCrypt source: `formosa-crypto/formosa-mlkem/proof/security/MLWE_PKE_Basic.ec`
-/

@[expose] public section

open CatCrypt.Prob
open scoped ENNReal

namespace CatCrypt.Crypto.MLKEM.MLWE_PKE_Basic

/-! ## Scheme Parameters -/

/-- Parameters for the basic MLWE-PKE scheme.

    Extends `MLWE.Params` with plaintext encoding/decoding and scalar distributions.
    Uniform distributions are derived from `SDistr.uniform` via `Fintype`/`Nonempty`. -/
structure Params extends MLWE.Params where
  /-- Plaintext type -/
  PT : Type
  [finPT : Fintype PT]
  [nePT : Nonempty PT]
  [decPT : DecidableEq PT]
  [finR : Fintype R]
  [neR : Nonempty R]
  /-- Short vector distribution of the encryption noise `e₁`, drawn independently
      of the distribution `dshort_vec` of `s`, `e` and `r`. -/
  dshort_vec2 : SDistr Vec
  /-- Short ring element distribution (noise) -/
  dshort_R : SDistr R
  /-- Encode plaintext as ring element -/
  m_encode : PT → R
  /-- Decode ring element to plaintext -/
  m_decode : R → PT
  /-- Matrix transpose is an involution (needed for transpose-uniform). -/
  mat_transpose_involutive : Function.Involutive mat_transpose
  /-- Ring addition by a constant is bijective (needed for shift-uniform). -/
  ring_add_right_bijective : ∀ c : R, Function.Bijective (fun v => ring_add v c)

attribute [instance] Params.finPT Params.nePT Params.decPT Params.finR Params.neR

variable (P : Params)

-- Forward Fintype/Nonempty instances from MLWE.Params through extends
instance : Fintype P.Mat := MLWE.Params.finMat P.toParams
instance : Nonempty P.Mat := MLWE.Params.neMat P.toParams
instance : Fintype P.Vec := MLWE.Params.finVec P.toParams
instance : Nonempty P.Vec := MLWE.Params.neVec P.toParams

/-! ## Type Abbreviations -/

/-- Ciphertext type: (vector, ring element). -/
abbrev CT := P.Vec × P.R

/-- Public key type: (matrix, vector). -/
abbrev PK := P.Mat × P.Vec

/-- Secret key type: vector. -/
abbrev SK := P.Vec

/-! ## The Basic MLWE PKE Scheme -/

/-- Key generation: `A ← uniform`, `s,e ← short`, `pk = (A, A*s+e)`, `sk = s`. -/
noncomputable def kg : SDistr (PK P × SK P) := do
  let A ← SDistr.uniform P.Mat
  let s ← P.dshort_vec
  let e ← P.dshort_vec
  let t := P.vec_add (P.mat_vec_mul A s) e
  SDistr.pure ((A, t), s)

/-- Encryption: `r ← short`, `e1 ← short2`, `e2 ← short_R`, `u = A^T*r+e1`,
    `v = t·r+e2+encode(m)`. -/
noncomputable def enc (pk : PK P) (m : P.PT) : SDistr (CT P) := do
  let (A, t) := pk
  let r ← P.dshort_vec
  let e1 ← P.dshort_vec2
  let e2 ← P.dshort_R
  let u := P.vec_add (P.mat_vec_mul (P.mat_transpose A) r) e1
  let v := P.ring_add (P.ring_add (P.vec_dot t r) e2) (P.m_encode m)
  SDistr.pure (u, v)

/-- Decryption: `v - s·u`, then decode. -/
noncomputable def dec (sk : SK P) (c : CT P) : SDistr (Option P.PT) := do
  let (u, v) := c
  let noisy_m := P.ring_sub v (P.vec_dot sk u)
  SDistr.pure (some (P.m_decode noisy_m))

/-! ## Security Games -/

/-- IND-CPA game for the basic MLWE-PKE against an adversary whose guess stage
    receives neither the public key nor a state.

    Superseded by `MLWE_PKE_Stateful.CPA_Game_st`, the game for a two-stage
    adversary with state; this game is its case `St := Unit`
    (`MLWE_PKE_Stateful.CPA_Game_eq_CPA_Game_st`).

    EasyCrypt: `PKE.CPA(MLWE_PKE_BASIC, A).main()`.
    The adversary `choose` picks two messages, `guess` distinguishes. -/
@[deprecated "use MLWE_PKE_Stateful.CPA_Game_st, the two-stage game with state \
  (MLWE_PKE_Stateful.CPA_Game_eq_CPA_Game_st)" (since := "2026-10-21")]
noncomputable def CPA_Game
    (choose : PK P → SDistr (P.PT × P.PT))
    (guess : CT P → SDistr Bool) (b : Bool) : SDistr Bool := do
  let (pk, _sk) ← kg P
  let (m0, m1) ← choose pk
  let c ← enc P pk (if b then m1 else m0)
  guess c

set_option linter.deprecated false in
/-- IND-CPA advantage against an adversary whose guess stage receives neither
    the public key nor a state. Superseded by `MLWE_PKE_Stateful.CPA_Adv_st`
    (`MLWE_PKE_Stateful.CPA_Adv_eq_CPA_Adv_st`). -/
@[deprecated "use MLWE_PKE_Stateful.CPA_Adv_st, the advantage in the two-stage game with \
  state (MLWE_PKE_Stateful.CPA_Adv_eq_CPA_Adv_st)" (since := "2026-10-21")]
noncomputable def CPA_Adv
    (choose : PK P → SDistr (P.PT × P.PT))
    (guess : CT P → SDistr Bool) : ℝ≥0∞ :=
  absDiff (prTrue (CPA_Game P choose guess true))
          (prTrue (CPA_Game P choose guess false))

/-- Game BASIC1: public key has uniform `t` (not `A*s+e`). After first hop. -/
noncomputable def CPA_BASIC1
    (choose : PK P → SDistr (P.PT × P.PT))
    (guess : CT P → SDistr Bool) (b : Bool) : SDistr Bool := do
  let A ← SDistr.uniform P.Mat
  let t ← SDistr.uniform P.Vec
  let pk : PK P := (A, t)
  let (m0, m1) ← choose pk
  let c ← enc P pk (if b then m1 else m0)
  guess c

/-- Game BASIC2: both pk and ciphertext are uniform. Independent of `b`. -/
noncomputable def CPA_BASIC2
    (choose : PK P → SDistr (P.PT × P.PT))
    (guess : CT P → SDistr Bool) (_b : Bool) : SDistr Bool := do
  let A ← SDistr.uniform P.Mat
  let t ← SDistr.uniform P.Vec
  let pk : PK P := (A, t)
  let (_m0, _m1) ← choose pk
  let u ← SDistr.uniform P.Vec
  let v ← SDistr.uniform P.R
  guess (u, v)

/-- Correctness game: adversary finds a message that causes decryption failure. -/
noncomputable def Correctness_Game
    (find : PK P → SK P → SDistr P.PT) : SDistr Bool := do
  let (pk, sk) ← kg P
  let m ← find pk sk
  let c ← enc P pk m
  let m' ← dec P sk c
  SDistr.pure (m' ≠ some m)

/-! ## MLWE Reduction Adversaries -/

/-- B1: MLWE adversary for the first hop (key generation).

    Given MLWE challenge `(A, t)`, uses it as the public key and fixed bit `b`.
    If `t = A*s+e` (real), this is CPA(b). If `t ← uniform` (ideal), this is BASIC1(b).

    EasyCrypt: `B1(A)` (internalizes `b`, but we parameterize for cleaner hop proofs). -/
noncomputable def B1
    (choose : PK P → SDistr (P.PT × P.PT))
    (guess : CT P → SDistr Bool) (b : Bool)
    (A : P.Mat) (t : P.Vec) : SDistr Bool := do
  let pk : PK P := (A, t)
  let (m0, m1) ← choose pk
  let c ← enc P pk (if b then m1 else m0)
  guess c

/-- Extended MLWE game producing both vector and scalar challenges.

    In the real case (`b = false`), the challenges share the same secret `r`:
    `u = A^T·r + e1`, `v = ⟨t, r⟩ + e2`.
    In the ideal case (`b = true`), both `u` and `v` are uniform.

    This is module-LWE at a `(k+1) × k` matrix (the matrix `A^T` augmented with
    the row vector `t`), with the secret `r` and the errors `e1`, `e2` drawn
    from the scheme's noise distributions. It is a separate assumption from the
    key-generation instance `MLWE.Game`; no reduction between the two is proved
    here. -/
noncomputable def MLWE_Ext_Game
    (adv : P.Mat → P.Vec → P.Vec → P.R → SDistr Bool)
    (b : Bool) : SDistr Bool := do
  let A ← SDistr.uniform P.Mat
  let t ← SDistr.uniform P.Vec
  if b then do
    let u ← SDistr.uniform P.Vec
    let v ← SDistr.uniform P.R
    adv A t u v
  else do
    let r ← P.dshort_vec
    let e1 ← P.dshort_vec2
    let e2 ← P.dshort_R
    let u := P.vec_add (P.mat_vec_mul (P.mat_transpose A) r) e1
    let v := P.ring_add (P.vec_dot t r) e2
    adv A t u v

/-- Extended MLWE advantage: distinguishing probability between real and ideal. -/
noncomputable def MLWE_Ext_advantage
    (adv : P.Mat → P.Vec → P.Vec → P.R → SDistr Bool) : ℝ≥0∞ :=
  absDiff (prTrue (MLWE_Ext_Game P adv false)) (prTrue (MLWE_Ext_Game P adv true))

/-- B2_ext: adversary for the extended MLWE game (second hop).

    Given `(A, t, u, v_base)` from the extended MLWE challenge, computes the
    message-dependent part of the ciphertext: `v = v_base + encode(m)`.

    In the real case (`v_base = ⟨t, r⟩ + e2`), the output matches BASIC1.
    In the ideal case (`v_base ← uniform`), `v = uniform + encode(m)` is still
    uniform by shift invariance, matching BASIC2.

    EasyCrypt: `B2(A)` (adapted to the extended MLWE formulation). -/
noncomputable def B2_ext
    (choose : PK P → SDistr (P.PT × P.PT))
    (guess : CT P → SDistr Bool) (b : Bool)
    (A : P.Mat) (t : P.Vec) (u : P.Vec) (v_base : P.R) : SDistr Bool := do
  let pk : PK P := (A, t)
  let (m0, m1) ← choose pk
  let m := if b then m1 else m0
  let v := P.ring_add v_base (P.m_encode m)
  guess (u, v)

/-! ## Helper Lemmas for Monadic Rewriting -/

/-- `SDistr.bind_comm` in do-notation form (syntactic bridge for `rw`). -/
theorem do_bind_comm {α β γ : Type} (m1 : SDistr α) (m2 : SDistr β)
    {f : α → β → SDistr γ} :
    (do let a ← m1; let b ← m2; f a b) = (do let b ← m2; let a ← m1; f a b) :=
  SDistr.bind_comm m1 m2 f

/-- Shift-invariance of uniform distribution: `ring_add · c` is a bijection. -/
theorem do_uniform_shift {α : Type} (c : P.R) (f : P.R → SDistr α) :
    (do let v ← SDistr.uniform P.R; f (P.ring_add v c)) = (do let v ← SDistr.uniform P.R; f v) := by
  exact SDistr.uniform_bind_equiv_comp (Equiv.ofBijective _ (P.ring_add_right_bijective c)) f

/-- Symmetry of absDiff. -/
lemma absDiff_comm' (a b : ℝ≥0∞) : absDiff a b = absDiff b a := by
  simp [absDiff, max_comm]

/-- Four-point triangle inequality for absDiff. -/
lemma absDiff_chain₄ (a b c d e : ℝ≥0∞) :
    absDiff a e ≤ absDiff a b + absDiff b c + absDiff c d + absDiff d e := by
  calc absDiff a e
      ≤ absDiff a d + absDiff d e := Infrastructure.absDiff_triangle a d e
    _ ≤ (absDiff a b + absDiff b d) + absDiff d e := by
        gcongr; exact Infrastructure.absDiff_triangle a b d
    _ ≤ (absDiff a b + (absDiff b c + absDiff c d)) + absDiff d e := by
        gcongr; exact Infrastructure.absDiff_triangle b c d
    _ = absDiff a b + absDiff b c + absDiff c d + absDiff d e := by ring

/-! ## Game-Hopping Lemmas -/

set_option linter.deprecated false in
/-- Hop 1, left: CPA game with bit `b` = MLWE(B1 b) with real samples.

    Both sides unfold to: `do A ← duni_mat; s ← dshort; e ← dshort;
    let t := A*s+e; (m0,m1) ← choose (A,t); c ← enc (A,t) (if b then m1 else m0); guess c`.

    Proved by monad laws (`bind_assoc`, `pure_bind`): unfold definitions,
    fold `SDistr.pure` into `pure`, reduce `if false then … else …`, and
    reassociate binds to obtain syntactically identical programs.

    EasyCrypt: `hop1_left` (proved by `byequiv`). -/
theorem hop1_left (choose : PK P → SDistr (P.PT × P.PT))
    (guess : CT P → SDistr Bool) (b : Bool) :
    CPA_Game P choose guess b =
    MLWE.Game P.toParams (B1 P choose guess b) false := by
  have pure_fold : ∀ (α : Type) (a : α), SDistr.pure a = (pure a : SDistr α) :=
    fun _ _ => rfl
  simp only [CPA_Game, kg, MLWE.Game, B1, pure_fold]
  simp [bind_assoc]

/-- Hop 1, right: MLWE(B1 b) with ideal samples = BASIC1 game.

    Both sides: `do A ← duni_mat; t ← duni_vec;
    (m0,m1) ← choose (A,t); c ← enc (A,t) (if b then m1 else m0); guess c`.

    Proved by monad laws: unfold definitions, reduce `if true then … else …`,
    and both sides are syntactically identical monadic programs.

    EasyCrypt: `hop1_right` (proved by `byequiv`). -/
theorem hop1_right (choose : PK P → SDistr (P.PT × P.PT))
    (guess : CT P → SDistr Bool) (b : Bool) :
    MLWE.Game P.toParams (B1 P choose guess b) true =
    CPA_BASIC1 P choose guess b := by
  simp only [MLWE.Game, B1, CPA_BASIC1]
  simp

/-- Hop 2, left: BASIC1 game = MLWE_Ext(B2_ext) with real samples.

    Both sides unfold to the same monadic program after commuting independent
    samplings: `choose (A, t)` does not depend on `r, e1, e2`, so their
    sampling order can be swapped via `SDistr.bind_comm`.

    EasyCrypt: `hop2_left` (proved by `byequiv`). -/
theorem hop2_left (choose : PK P → SDistr (P.PT × P.PT))
    (guess : CT P → SDistr Bool) (b : Bool) :
    CPA_BASIC1 P choose guess b =
    MLWE_Ext_Game P (B2_ext P choose guess b) false := by
  have pure_fold : ∀ (α : Type) (a : α), SDistr.pure a = (pure a : SDistr α) :=
    fun _ _ => rfl
  simp only [CPA_BASIC1, enc, MLWE_Ext_Game, B2_ext, pure_fold]
  simp [bind_assoc]
  -- Both sides identical except choose(A,t) comes before vs after 3 dshort samplings.
  -- Commute choose past dshort_vec, dshort_vec2, dshort_R using do_bind_comm.
  conv_lhs =>
    enter [2]; ext A; enter [2]; ext t
    rw [do_bind_comm (choose (A, t)) P.dshort_vec]
    enter [2]; ext r
    rw [do_bind_comm (choose (A, t)) P.dshort_vec2]
    enter [2]; ext e1
    rw [do_bind_comm (choose (A, t)) P.dshort_R]

/-- Hop 2, right: MLWE_Ext(B2_ext) with ideal samples = BASIC2 game.

    When the extended MLWE challenge is ideal (`v_base ← uniform`),
    `v = v_base + encode(m)` is still uniform by `uniform_shift`, so
    the message vanishes and the ciphertext is independent of `b`.
    Independent samplings are commuted via `SDistr.bind_comm`.

    EasyCrypt: `hop2_right` (proved by `byequiv`). -/
theorem hop2_right (choose : PK P → SDistr (P.PT × P.PT))
    (guess : CT P → SDistr Bool) (b : Bool) :
    MLWE_Ext_Game P (B2_ext P choose guess b) true =
    CPA_BASIC2 P choose guess b := by
  simp only [MLWE_Ext_Game, B2_ext, CPA_BASIC2]
  simp
  -- LHS: ...duni_vec >>= u => duni_R >>= v => choose >>= p => guess(u, ring_add v (m_encode ...))
  -- RHS: ...choose >>= p => duni_vec >>= u => duni_R >>= v => guess(u, v)
  -- Step 1: Inside duni_vec body, swap duni_R and choose
  conv_lhs =>
    enter [2]; ext A; enter [2]; ext t; enter [2]; ext u
    rw [do_bind_comm (SDistr.uniform P.R) (choose (A, t))]
  -- Step 2: Swap uniform Vec and choose
  conv_lhs =>
    enter [2]; ext A; enter [2]; ext t
    rw [do_bind_comm (SDistr.uniform P.Vec) (choose (A, t))]
  -- Step 3: Use uniform_shift to absorb ring_add v (m_encode ...)
  conv_lhs =>
    enter [2]; ext A; enter [2]; ext t; enter [2]; ext p; enter [2]; ext u
    rw [do_uniform_shift P (P.m_encode (if b = true then p.2 else p.1))
        (fun v => guess (u, v))]

/-! ## Main Security Theorem -/

/-- BASIC2 is independent of the challenge bit: both sides are identical
    (the ciphertext is uniformly random regardless of b). -/
theorem basic2_independent (choose : PK P → SDistr (P.PT × P.PT))
    (guess : CT P → SDistr Bool) (b : Bool) :
    CPA_BASIC2 P choose guess b = CPA_BASIC2 P choose guess false := by
  simp only [CPA_BASIC2]

set_option linter.deprecated false in
/-- Main theorem: CPA advantage bounded by two MLWE + two extended MLWE advantages.

    The proof chains four game hops via the triangle inequality:
    ```
    CPA(T) = MLWE(B1t,f) —ε₁— MLWE(B1t,t) = BASIC1(T) = MLWE_Ext(B2t,f)
         —ε₂— MLWE_Ext(B2t,t) = BASIC2(T) = BASIC2(F) = MLWE_Ext(B2f,t)
         —ε₃— MLWE_Ext(B2f,f) = BASIC1(F) = MLWE(B1f,t) —ε₄— MLWE(B1f,f) = CPA(F)
    ```

    All equalities (`=`) are now proved: `hop1_left`, `hop1_right`,
    `hop2_left`, `hop2_right`, and `basic2_independent`. The gaps (`—εᵢ—`)
    are the four advantages (two standard MLWE for B1, two extended MLWE
    for B2_ext). No hypotheses remain.

    Superseded by `MLWE_PKE_Stateful.main_theorem_st`, the same bound for a
    two-stage adversary with state.

    EasyCrypt: `main_theorem`. -/
@[deprecated "use MLWE_PKE_Stateful.main_theorem_st, the bound for a two-stage adversary \
  with state; MLWE_PKE_Stateful.main_theorem_of_st restates this bound" (since := "2026-10-21")]
theorem main_theorem (choose : PK P → SDistr (P.PT × P.PT))
    (guess : CT P → SDistr Bool) :
    CPA_Adv P choose guess ≤
      MLWE.advantage P.toParams (B1 P choose guess true) +
      MLWE_Ext_advantage P (B2_ext P choose guess true) +
      MLWE_Ext_advantage P (B2_ext P choose guess false) +
      MLWE.advantage P.toParams (B1 P choose guess false) := by
  -- Equality chain: intermediate games are equal (via hop lemmas)
  have eq1 : MLWE.Game P.toParams (B1 P choose guess true) true =
      MLWE_Ext_Game P (B2_ext P choose guess true) false :=
    (hop1_right P choose guess true).trans (hop2_left P choose guess true)
  have eq2 : MLWE_Ext_Game P (B2_ext P choose guess true) true =
      MLWE_Ext_Game P (B2_ext P choose guess false) true :=
    (hop2_right P choose guess true).trans
      ((basic2_independent P choose guess true).trans (hop2_right P choose guess false).symm)
  have eq3 : MLWE_Ext_Game P (B2_ext P choose guess false) false =
      MLWE.Game P.toParams (B1 P choose guess false) true :=
    (hop2_left P choose guess false).symm.trans (hop1_right P choose guess false).symm
  -- CPA_Adv → absDiff of MLWE games (via hop1_left)
  unfold CPA_Adv
  rw [hop1_left P choose guess true, hop1_left P choose guess false]
  -- Apply 4-point triangle inequality through the game chain
  apply le_trans (absDiff_chain₄
    (prTrue (MLWE.Game P.toParams (B1 P choose guess true) false))
    (prTrue (MLWE.Game P.toParams (B1 P choose guess true) true))
    (prTrue (MLWE_Ext_Game P (B2_ext P choose guess true) true))
    (prTrue (MLWE_Ext_Game P (B2_ext P choose guess false) false))
    (prTrue (MLWE.Game P.toParams (B1 P choose guess false) false)))
  -- Bound each gap by the corresponding advantage
  apply add_le_add (add_le_add (add_le_add ?_ ?_) ?_) ?_
  · -- |MLWE(B1t,f) - MLWE(B1t,t)| ≤ MLWE.advantage(B1t): definitional
    exact le_rfl
  · -- |MLWE(B1t,t) - MLWE_Ext(B2t,t)| ≤ MLWE_Ext_advantage(B2t)
    -- Rewrite MLWE(B1t,t) = MLWE_Ext(B2t,f) via eq1
    rw [congr_arg prTrue eq1]; exact le_rfl
  · -- |MLWE_Ext(B2t,t) - MLWE_Ext(B2f,f)| ≤ MLWE_Ext_advantage(B2f)
    -- Rewrite B2t,t = B2f,t via eq2, giving absDiff(B2f,t)(B2f,f) = comm of advantage
    rw [congr_arg prTrue eq2]; exact le_of_eq (absDiff_comm' _ _)
  · -- |MLWE_Ext(B2f,f) - MLWE(B1f,f)| ≤ MLWE.advantage(B1f)
    -- Rewrite B2f,f = MLWE(B1f,t) via eq3, giving absDiff(B1f,t)(B1f,f) = comm of advantage
    rw [congr_arg prTrue eq3]; exact le_of_eq (absDiff_comm' _ _)

/-! ## Correctness -/

/-- Decryption-failure probability of an honest encryption of `m` under the
    key pair `k`. -/
noncomputable def failProb (k : PK P × SK P) (m : P.PT) : ℝ≥0∞ :=
  prTrue (do
    let c ← enc P k.1 m
    let m' ← dec P k.2 c
    SDistr.pure (decide (m' ≠ some m)))

/-- Worst-case decryption-failure probability over all key pairs and messages. -/
noncomputable def corrWorst : ℝ≥0∞ :=
  ⨆ (k : PK P × SK P) (m : P.PT), failProb P k m

/-- The probability of a value after `bind` is at most the supremum of that
    probability over the bound values. -/
theorem _root_.CatCrypt.Prob.SDistr.bind_apply_some_le_iSup {α β : Type} (d : SDistr α)
    (f : α → SDistr β) (b : β) :
    (d.bind f) (some b) ≤ ⨆ a, f a (some b) := by
  simp only [SDistr.bind, PMF.bind_apply]
  calc ∑' oa, d oa * (match oa with | some a => f a | none => SDistr.fail) (some b)
      ≤ ∑' oa, d oa * ⨆ a, f a (some b) := ENNReal.tsum_le_tsum fun oa => by
        cases oa with
        | none => simp [SDistr.fail]
        | some a => exact mul_le_mul_right (le_iSup (fun a => f a (some b)) a) _
    _ = ⨆ a, f a (some b) := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- **Correctness.** The adversarial correctness game, in which `find` chooses
    the message from both keys, fails with probability at most the worst-case
    decryption-failure probability `corrWorst`.

    EasyCrypt: `correctness_theorem` takes the bound as a hypothesis; this
    statement bounds the game by `corrWorst` for every `find`. -/
theorem correctness_le_corrWorst (find : PK P → SK P → SDistr P.PT) :
    prTrue (Correctness_Game P find) ≤ corrWorst P := by
  unfold Correctness_Game prTrue
  refine (SDistr.bind_apply_some_le_iSup _ _ _).trans (iSup_le fun k => ?_)
  obtain ⟨pk, sk⟩ := k
  refine (SDistr.bind_apply_some_le_iSup _ _ _).trans (iSup_le fun m => ?_)
  exact le_iSup₂_of_le (f := fun k m => failProb P k m) (pk, sk) m le_rfl

end CatCrypt.Crypto.MLKEM.MLWE_PKE_Basic
