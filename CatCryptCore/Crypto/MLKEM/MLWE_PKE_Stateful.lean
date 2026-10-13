/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.MLKEM.MLWE_PKE_Basic

/-!
# Basic MLWE-PKE: CPA security against two-stage adversaries

The IND-CPA game of `MLWE_PKE_Basic` takes a stateless adversary: `choose`
returns the two messages and `guess` sees only the ciphertext. This file states
the same game for a two-stage adversary whose `choose` also returns a state
`st : St` that is handed to `guess`, with the message convention of
`PKE.Games.indcpaGame` (`m0` is encrypted when `b = true`), and proves the
same bound: four game hops through the standard and extended MLWE games. The
hops rewrite only the challenger's sampling, so the adversary's state threads
through every game unchanged.

The stateless bound of `MLWE_PKE_Basic.main_theorem` is re-derived from the
stateful one at `St := Unit` (`main_theorem_of_st`).

## Main definitions

* `CPA_Game_st`, `CPA_Adv_st` — the IND-CPA game and advantage for a two-stage
  adversary.
* `CPA_BASIC1_st`, `CPA_BASIC2_st` — the intermediate games with uniform public
  key, and with uniform public key and ciphertext.
* `B1_st`, `B2_ext_st` — the MLWE and extended-MLWE reductions.
* `liftChoose` — a stateless `choose` as a two-stage one with state `Unit`.

## Main results

* `main_theorem_st` — the CPA advantage of a two-stage adversary is bounded by
  the two MLWE advantages of `B1_st` and the two extended MLWE advantages of
  `B2_ext_st`.
* `main_theorem_of_st` — the bound of `MLWE_PKE_Basic.main_theorem`, derived
  from `main_theorem_st` at `St := Unit`.
-/

@[expose] public section

open CatCrypt.Prob
open scoped ENNReal

namespace CatCrypt.Crypto.MLKEM.MLWE_PKE_Stateful

open MLWE_PKE_Basic

variable (P : MLWE_PKE_Basic.Params)

/-! ## Security games -/

/-- IND-CPA game for the basic MLWE-PKE against a two-stage adversary.

    `choose` returns two messages and a state; `guess` receives the state and
    the ciphertext. `m0` is encrypted when `b = true`, the convention of
    `PKE.Games.indcpaGame`. -/
noncomputable def CPA_Game_st {St : Type}
    (choose : PK P → SDistr (P.PT × P.PT × St))
    (guess : St → CT P → SDistr Bool) (b : Bool) : SDistr Bool := do
  let (pk, _sk) ← kg P
  let (m0, m1, st) ← choose pk
  let c ← enc P pk (if b then m0 else m1)
  guess st c

/-- IND-CPA advantage of a two-stage adversary. -/
noncomputable def CPA_Adv_st {St : Type}
    (choose : PK P → SDistr (P.PT × P.PT × St))
    (guess : St → CT P → SDistr Bool) : ℝ≥0∞ :=
  absDiff (prTrue (CPA_Game_st P choose guess true))
          (prTrue (CPA_Game_st P choose guess false))

/-- Game BASIC1 for a two-stage adversary: the public key has uniform `t`. -/
noncomputable def CPA_BASIC1_st {St : Type}
    (choose : PK P → SDistr (P.PT × P.PT × St))
    (guess : St → CT P → SDistr Bool) (b : Bool) : SDistr Bool := do
  let A ← SDistr.uniform P.Mat
  let t ← SDistr.uniform P.Vec
  let pk : PK P := (A, t)
  let (m0, m1, st) ← choose pk
  let c ← enc P pk (if b then m0 else m1)
  guess st c

/-- Game BASIC2 for a two-stage adversary: public key and ciphertext are
    uniform, so the game does not depend on `b`. -/
noncomputable def CPA_BASIC2_st {St : Type}
    (choose : PK P → SDistr (P.PT × P.PT × St))
    (guess : St → CT P → SDistr Bool) (_b : Bool) : SDistr Bool := do
  let A ← SDistr.uniform P.Mat
  let t ← SDistr.uniform P.Vec
  let pk : PK P := (A, t)
  let (_m0, _m1, st) ← choose pk
  let u ← SDistr.uniform P.Vec
  let v ← SDistr.uniform P.R
  guess st (u, v)

/-! ## Reductions -/

/-- MLWE adversary for the first hop: the challenge `(A, t)` is the public key,
    the bit `b` is fixed, and the state of `choose` is handed to `guess`. -/
noncomputable def B1_st {St : Type}
    (choose : PK P → SDistr (P.PT × P.PT × St))
    (guess : St → CT P → SDistr Bool) (b : Bool)
    (A : P.Mat) (t : P.Vec) : SDistr Bool := do
  let pk : PK P := (A, t)
  let (m0, m1, st) ← choose pk
  let c ← enc P pk (if b then m0 else m1)
  guess st c

/-- Extended-MLWE adversary for the second hop: given `(A, t, u, v_base)`, the
    ciphertext is `(u, v_base + encode m)` and the state of `choose` is handed
    to `guess`. -/
noncomputable def B2_ext_st {St : Type}
    (choose : PK P → SDistr (P.PT × P.PT × St))
    (guess : St → CT P → SDistr Bool) (b : Bool)
    (A : P.Mat) (t : P.Vec) (u : P.Vec) (v_base : P.R) : SDistr Bool := do
  let pk : PK P := (A, t)
  let (m0, m1, st) ← choose pk
  let m := if b then m0 else m1
  let v := P.ring_add v_base (P.m_encode m)
  guess st (u, v)

/-! ## Game hops -/

/-- Hop 1, left: the CPA game with bit `b` is the MLWE game of `B1_st b` with
    real samples. -/
theorem hop1_left_st {St : Type}
    (choose : PK P → SDistr (P.PT × P.PT × St))
    (guess : St → CT P → SDistr Bool) (b : Bool) :
    CPA_Game_st P choose guess b =
    MLWE.Game P.toParams (B1_st P choose guess b) false := by
  have pure_fold : ∀ (α : Type) (a : α), SDistr.pure a = (pure a : SDistr α) :=
    fun _ _ => rfl
  simp only [CPA_Game_st, kg, MLWE.Game, B1_st, pure_fold]
  simp [bind_assoc]

/-- Hop 1, right: the MLWE game of `B1_st b` with ideal samples is BASIC1. -/
theorem hop1_right_st {St : Type}
    (choose : PK P → SDistr (P.PT × P.PT × St))
    (guess : St → CT P → SDistr Bool) (b : Bool) :
    MLWE.Game P.toParams (B1_st P choose guess b) true =
    CPA_BASIC1_st P choose guess b := by
  simp only [MLWE.Game, B1_st, CPA_BASIC1_st]
  simp

/-- Hop 2, left: BASIC1 is the extended MLWE game of `B2_ext_st b` with real
    samples. `choose (A, t)` is independent of `r, e1, e2`, so the samplings
    commute. -/
theorem hop2_left_st {St : Type}
    (choose : PK P → SDistr (P.PT × P.PT × St))
    (guess : St → CT P → SDistr Bool) (b : Bool) :
    CPA_BASIC1_st P choose guess b =
    MLWE_Ext_Game P (B2_ext_st P choose guess b) false := by
  have pure_fold : ∀ (α : Type) (a : α), SDistr.pure a = (pure a : SDistr α) :=
    fun _ _ => rfl
  simp only [CPA_BASIC1_st, enc, MLWE_Ext_Game, B2_ext_st, pure_fold]
  simp [bind_assoc]
  conv_lhs =>
    enter [2]; ext A; enter [2]; ext t
    rw [do_bind_comm (choose (A, t)) P.dshort_vec]
    enter [2]; ext r
    rw [do_bind_comm (choose (A, t)) P.dshort_vec2]
    enter [2]; ext e1
    rw [do_bind_comm (choose (A, t)) P.dshort_R]

/-- Hop 2, right: the extended MLWE game of `B2_ext_st b` with ideal samples is
    BASIC2. The uniform `v_base` absorbs `encode m` by shift invariance. -/
theorem hop2_right_st {St : Type}
    (choose : PK P → SDistr (P.PT × P.PT × St))
    (guess : St → CT P → SDistr Bool) (b : Bool) :
    MLWE_Ext_Game P (B2_ext_st P choose guess b) true =
    CPA_BASIC2_st P choose guess b := by
  simp only [MLWE_Ext_Game, B2_ext_st, CPA_BASIC2_st]
  simp
  conv_lhs =>
    enter [2]; ext A; enter [2]; ext t; enter [2]; ext u
    rw [do_bind_comm (SDistr.uniform P.R) (choose (A, t))]
  conv_lhs =>
    enter [2]; ext A; enter [2]; ext t
    rw [do_bind_comm (SDistr.uniform P.Vec) (choose (A, t))]
  conv_lhs =>
    enter [2]; ext A; enter [2]; ext t; enter [2]; ext p; enter [2]; ext u
    rw [do_uniform_shift P (P.m_encode (if b = true then p.1 else p.2.1))
        (fun v => guess p.2.2 (u, v))]

/-- BASIC2 does not depend on the challenge bit. -/
theorem basic2_independent_st {St : Type}
    (choose : PK P → SDistr (P.PT × P.PT × St))
    (guess : St → CT P → SDistr Bool) (b : Bool) :
    CPA_BASIC2_st P choose guess b = CPA_BASIC2_st P choose guess false := by
  simp only [CPA_BASIC2_st]

/-! ## Main theorem -/

/-- The CPA advantage of a two-stage adversary is bounded by two MLWE
    advantages of `B1_st` and two extended MLWE advantages of `B2_ext_st`,
    through the chain

    ```
    CPA(T) = MLWE(B1t,f) —ε₁— MLWE(B1t,t) = BASIC1(T) = MLWE_Ext(B2t,f)
         —ε₂— MLWE_Ext(B2t,t) = BASIC2(T) = BASIC2(F) = MLWE_Ext(B2f,t)
         —ε₃— MLWE_Ext(B2f,f) = BASIC1(F) = MLWE(B1f,t) —ε₄— MLWE(B1f,f) = CPA(F)
    ``` -/
theorem main_theorem_st {St : Type}
    (choose : PK P → SDistr (P.PT × P.PT × St))
    (guess : St → CT P → SDistr Bool) :
    CPA_Adv_st P choose guess ≤
      MLWE.advantage P.toParams (B1_st P choose guess true) +
      MLWE_Ext_advantage P (B2_ext_st P choose guess true) +
      MLWE_Ext_advantage P (B2_ext_st P choose guess false) +
      MLWE.advantage P.toParams (B1_st P choose guess false) := by
  have eq1 : MLWE.Game P.toParams (B1_st P choose guess true) true =
      MLWE_Ext_Game P (B2_ext_st P choose guess true) false :=
    (hop1_right_st P choose guess true).trans (hop2_left_st P choose guess true)
  have eq2 : MLWE_Ext_Game P (B2_ext_st P choose guess true) true =
      MLWE_Ext_Game P (B2_ext_st P choose guess false) true :=
    (hop2_right_st P choose guess true).trans
      ((basic2_independent_st P choose guess true).trans
        (hop2_right_st P choose guess false).symm)
  have eq3 : MLWE_Ext_Game P (B2_ext_st P choose guess false) false =
      MLWE.Game P.toParams (B1_st P choose guess false) true :=
    (hop2_left_st P choose guess false).symm.trans (hop1_right_st P choose guess false).symm
  unfold CPA_Adv_st
  rw [hop1_left_st P choose guess true, hop1_left_st P choose guess false]
  apply le_trans (absDiff_chain₄
    (prTrue (MLWE.Game P.toParams (B1_st P choose guess true) false))
    (prTrue (MLWE.Game P.toParams (B1_st P choose guess true) true))
    (prTrue (MLWE_Ext_Game P (B2_ext_st P choose guess true) true))
    (prTrue (MLWE_Ext_Game P (B2_ext_st P choose guess false) false))
    (prTrue (MLWE.Game P.toParams (B1_st P choose guess false) false)))
  apply add_le_add (add_le_add (add_le_add ?_ ?_) ?_) ?_
  · exact le_rfl
  · rw [congr_arg prTrue eq1]; exact le_rfl
  · rw [congr_arg prTrue eq2]; exact le_of_eq (absDiff_comm' _ _)
  · rw [congr_arg prTrue eq3]; exact le_of_eq (absDiff_comm' _ _)

/-! ## The stateless bound as an instance -/

/-- A stateless `choose` as a two-stage one with state `Unit`. -/
noncomputable def liftChoose (choose : PK P → SDistr (P.PT × P.PT)) (pk : PK P) :
    SDistr (P.PT × P.PT × Unit) := do
  let (m0, m1) ← choose pk
  pure (m0, m1, ())

/-- The stateless `B1` at bit `b` is `B1_st` of the lifted adversary at bit `!b`:
    the two games encrypt opposite messages. -/
theorem B1_eq_B1_st (choose : PK P → SDistr (P.PT × P.PT))
    (guess : CT P → SDistr Bool) (b : Bool) :
    B1 P choose guess b = B1_st P (liftChoose P choose) (fun _ => guess) (!b) := by
  funext A t
  simp only [B1, B1_st, liftChoose, bind_assoc, pure_bind]
  cases b <;> simp

/-- The stateless `B2_ext` at bit `b` is `B2_ext_st` of the lifted adversary at
    bit `!b`. -/
theorem B2_ext_eq_B2_ext_st (choose : PK P → SDistr (P.PT × P.PT))
    (guess : CT P → SDistr Bool) (b : Bool) :
    B2_ext P choose guess b =
      B2_ext_st P (liftChoose P choose) (fun _ => guess) (!b) := by
  funext A t u v
  simp only [B2_ext, B2_ext_st, liftChoose, bind_assoc, pure_bind]
  cases b <;> simp

/-- The stateless CPA game at bit `b` is the two-stage game of the lifted
    adversary at bit `!b`. -/
theorem CPA_Game_eq_CPA_Game_st (choose : PK P → SDistr (P.PT × P.PT))
    (guess : CT P → SDistr Bool) (b : Bool) :
    CPA_Game P choose guess b =
      CPA_Game_st P (liftChoose P choose) (fun _ => guess) (!b) := by
  simp only [CPA_Game, CPA_Game_st, liftChoose, bind_assoc, pure_bind]
  cases b <;> simp

/-- The stateless CPA advantage is the two-stage advantage of the lifted
    adversary; the message-convention swap is absorbed by the symmetry of
    `absDiff`. -/
theorem CPA_Adv_eq_CPA_Adv_st (choose : PK P → SDistr (P.PT × P.PT))
    (guess : CT P → SDistr Bool) :
    CPA_Adv P choose guess = CPA_Adv_st P (liftChoose P choose) (fun _ => guess) := by
  simp only [CPA_Adv, CPA_Adv_st, CPA_Game_eq_CPA_Game_st, Bool.not_true, Bool.not_false]
  exact absDiff_comm' _ _

/-- The bound of `MLWE_PKE_Basic.main_theorem`, derived from `main_theorem_st`
    at `St := Unit`. -/
theorem main_theorem_of_st (choose : PK P → SDistr (P.PT × P.PT))
    (guess : CT P → SDistr Bool) :
    CPA_Adv P choose guess ≤
      MLWE.advantage P.toParams (B1 P choose guess true) +
      MLWE_Ext_advantage P (B2_ext P choose guess true) +
      MLWE_Ext_advantage P (B2_ext P choose guess false) +
      MLWE.advantage P.toParams (B1 P choose guess false) := by
  rw [CPA_Adv_eq_CPA_Adv_st, B1_eq_B1_st, B1_eq_B1_st, B2_ext_eq_B2_ext_st,
    B2_ext_eq_B2_ext_st]
  simp only [Bool.not_true, Bool.not_false]
  have h := main_theorem_st P (liftChoose P choose) (fun _ => guess)
  calc CPA_Adv_st P (liftChoose P choose) (fun _ => guess)
      ≤ _ := h
    _ = _ := by ring

end CatCrypt.Crypto.MLKEM.MLWE_PKE_Stateful
