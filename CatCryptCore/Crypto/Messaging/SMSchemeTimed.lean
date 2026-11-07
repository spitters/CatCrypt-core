/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.SMScheme

/-!
# Running time of the relabelled adversaries of the secure-messaging schemes

The transfer lemmas of `CatCryptCore.Crypto.Messaging.SMScheme` turn an adversary of the game
over a scheme into an adversary of the game over another scheme (`SMSchemeAdv.comap`, along a
simulation) or of `sm_corrupt_game` (`SMSchemeAdv.toSM`, at the ACD construction); the
adaptive games use the same relabelling of the oracle tree. Each relabels the answers of the
oracle tree by `OracleAdv.mapQueryAnswer id`. Its costed form is
`OracleAdv.Timed.mapQueryAnswer` with the query relabelling at cost zero and the answer
relabelling at a cost `u`; this file proves that the costed form erases to the relabelled tree
and that, for a costed tree of time `T` with at most `q` queries and answer relabellings of
cost at most `u₀`, its time is at most `T + q * u₀`.

## Main results

* `SMSchemeAdv.comap_play_timed` — the costed play of `A.comap encP encC encL`
* `SMSchemeAdv.toSM_play_timed` — the costed play of `A.toSM`
* `smRelabel_play_timed` — the costed relabelled tree, which the adaptive games use
-/

set_option autoImplicit false

@[expose] public section

namespace CatCrypt.Crypto.Messaging

open CatCrypt.Crypto

variable {Pub Ct Leak Pub' Ct' Leak' W : Type}

/-- **Time of the relabelled tree.** For a costed tree `Â` of time `T` with at most `q` queries,
relabelling its answers by `e` at cost at most `u₀` gives a costed tree erasing to the
relabelled tree, of time at most `T + q * u₀`. -/
theorem smRelabel_play_timed {R R' : Type} (e : R → R') (u : R → ℕ) {u₀ : ℕ}
    (hu : ∀ r, u r ≤ u₀) (Â : OracleAdv.Timed (SMQuery W) R' Bool) {T q : ℕ}
    (hT : Â.TimeBound T) (hq : Â.erase.IsQueryBound q) :
    (OracleAdv.Timed.mapQueryAnswer id (fun _ => 0) e u Â).erase =
        Â.erase.mapQueryAnswer id e ∧
      (OracleAdv.Timed.mapQueryAnswer id (fun _ => 0) e u Â).TimeBound (T + q * u₀) := by
  refine ⟨OracleAdv.Timed.erase_mapQueryAnswer _ _ _ _ _, ?_⟩
  have h := OracleAdv.Timed.timeBound_mapQueryAnswer (id : SMQuery W → SMQuery W)
    (fun _ => 0) e u (t₀ := 0) (fun _ => le_refl 0) hu hT hq
  simpa only [Nat.zero_add] using h

/-- **Time of `A.comap`.** For a costed tree `Â` of time `T` with at most `q` queries that
erases to the play of `A` at the challenge epoch `t` and the encoded public value `encP T₀`,
the costed relabelling at cost at most `u₀` per answer erases to the play of
`A.comap encP encC encL` and has time at most `T + q * u₀`. -/
theorem SMSchemeAdv.comap_play_timed (encP : Pub → Pub') (encC : Ct → Ct')
    (encL : Leak → Leak') (u : SMSchemeAns Pub Ct Leak → ℕ) {u₀ : ℕ} (hu : ∀ r, u r ≤ u₀)
    (A : SMSchemeAdv Pub' W Ct' Leak') (t : ℕ) (T₀ : Pub)
    (Â : OracleAdv.Timed (SMQuery W) (SMSchemeAns Pub' Ct' Leak') Bool)
    (hÂ : Â.erase = A.play t (encP T₀)) {T q : ℕ} (hT : Â.TimeBound T)
    (hq : Â.erase.IsQueryBound q) :
    (OracleAdv.Timed.mapQueryAnswer id (fun _ => 0) (SMSchemeAns.map encP encC encL) u
        Â).erase = (A.comap encP encC encL).play t T₀ ∧
      (OracleAdv.Timed.mapQueryAnswer id (fun _ => 0) (SMSchemeAns.map encP encC encL) u
        Â).TimeBound (T + q * u₀) := by
  obtain ⟨h1, h2⟩ := smRelabel_play_timed (SMSchemeAns.map encP encC encL) u hu Â hT hq
  exact ⟨h1.trans (by rw [hÂ]; rfl), h2⟩

variable {Sc Msg RK Sa : Type}

/-- **Time of `A.toSM`.** For a costed tree `Â` of time `T` with at most `q` queries that
erases to the play of `A` at `t` and `T₀`, the costed relabelling at cost at most `u₀` per
answer erases to the play of `A.toSM` and has time at most `T + q * u₀`. -/
theorem SMSchemeAdv.toSM_play_timed (u : SMAns Sc Msg RK Sa Ct → ℕ) {u₀ : ℕ}
    (hu : ∀ r, u r ≤ u₀) (A : SMSchemeAdv Msg W Ct (SMPartySt Sc RK Sa)) (t : ℕ) (T₀ : Msg)
    (Â : OracleAdv.Timed (SMQuery W) (SMSchemeAns Msg Ct (SMPartySt Sc RK Sa)) Bool)
    (hÂ : Â.erase = A.play t T₀) {T q : ℕ} (hT : Â.TimeBound T)
    (hq : Â.erase.IsQueryBound q) :
    (OracleAdv.Timed.mapQueryAnswer id (fun _ => 0) SMAns.toScheme u Â).erase =
        A.toSM.play t T₀ ∧
      (OracleAdv.Timed.mapQueryAnswer id (fun _ => 0) SMAns.toScheme u Â).TimeBound
        (T + q * u₀) := by
  obtain ⟨h1, h2⟩ := smRelabel_play_timed SMAns.toScheme u hu Â hT hq
  exact ⟨h1.trans (by rw [hÂ]; rfl), h2⟩

end CatCrypt.Crypto.Messaging
