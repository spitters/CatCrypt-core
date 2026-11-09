/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.TripleRatchetCorrupt
import CatCryptCore.Tactics.AutoDispatchExt

/-!
# The KEM CKA with state corruption, from KEM-CPA security

The CKA `kemCKA KEM` of Alwen, Coretti and Dodis (§4.1) in the CKA game with state corruption
and randomness leakage `cka_corrupt_game`. A party state `(pk, sk)` holds the last
encapsulation key of the peer and the own last decapsulation key; a send encapsulates under
`pk` and replaces `sk` by a fresh decapsulation key, a receive stores the fresh encapsulation key
and keeps `sk`.

## KEM with explicit randomness

The leakage oracle returns the randomness of a send, so the game needs the randomness of the
KEM: `KEMCoins KEM Rg Re` gives the key generation `kgenR : Rg → PK × SK` and the encapsulation
`encapR : PK → Re → K × E` as functions of their randomness; `KEMCoins.Sound` states that the
algorithms of `KEM` draw a uniform randomness and run them, and `KEMCoins.Correct` that
decapsulation inverts encapsulation under generated keys. The randomness of a send of `kemCKA`
is then a pair in `Re × Rg` (`kemCKACoins`).

## The reduction

With the challenge epoch `t*` announced first, the reduction `kemCorruptRed A` receives the
KEM-CPA challenge `(pk*, ek*, k*)`. It embeds `pk*` as the fresh encapsulation key of the send of
epoch `t* - 1` (the public value of the initialisation when `t* = 1`), stores a decapsulation
key of its own in its place, answers the challenge with the encapsulation `ek*` and the key
`k*`, and runs every other epoch with keys it generates. The game never reveals the decapsulation
key of `pk*`: it is held by the receiver of the challenge from epoch `t* - 1` to epoch `t*` (and
by both parties at the start when `t* = 1`), where the corruption gate with `1 ≤ ΔFS` and
`2 ≤ ΔPCS` refuses the corruption, and the leakage gate with `2 ≤ ΔPCS` refuses the leakage of
the send of epoch `t* - 1`. A receive does not use the decapsulation key to update the state.

The proof runs in probability mass functions: each oracle computation of the game is a lifted
distribution of the step `kemStepOf` on a draw of the randomness and a uniform key
(`kemCKA_oracle_eq`); two eager hops draw the randomness of the send of epoch `t* - 1` and of the
challenge in advance (`OracleAdv.run_nf_eq_eager`); the eager game and the simulator give equal
outputs under the simulation relation `KEMRel` (`kemRel_step`).

## Main definitions

* `kemInitP` — the initial distribution of `kemCKA`
* `kemStepOf`, `kemEagerStepOf`, `kemSimStepOf` — the steps of the game, of the eager game and
  of the simulator
* `kemHidden`, `KEMRel` — the hidden window of the embedded decapsulation key and the simulation
  relation
* `kemCorruptSimImplOf`, `kemCorruptTreeOf`, `kemCorruptRed` — the KEM-CPA reduction

## Main results

* `kemCKA_corrupt_advantage_eq_cpa` — for every adversary `A` and delays `1 ≤ ΔFS`,
  `2 ≤ ΔPCS`, the CKA corruption advantage of `kemCKA KEM` equals the KEM-CPA advantage of
  `kemCorruptRed ΔFS ΔPCS A`
* `kemCKA_corrupt_advantage_le` — the same as an upper bound
* `tripleRatchet_corruptAdvantage_le_kem` — the triple ratchet over `dhCKA G` and `kemCKA KEM`
  with the delays `ΔFS = ΔPCS = 2`: its advantage is at most DDH, KEM-CPA, PRF-PRNG and FS-AEAD
  advantages of explicit reductions

## References

* J. Alwen, S. Coretti, Y. Dodis, *The Double Ratchet: Security Notions, Proofs, and
  Modularization for the Signal Protocol*, EUROCRYPT 2019, §4.1
* Y. Dodis, D. Jost, S. Katsumata, T. Prest, R. Schmidt, *Triple Ratchet: A Bandwidth Efficient
  Hybrid-Secure Signal Protocol*, EUROCRYPT 2025
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Messaging

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Assumptions
  CatCrypt.Crypto.PRPPRF CatCryptCore.Examples.CyclicGroupDDH CatCrypt.Examples.KEMDEM
open scoped ENNReal

/-! ## The initial distribution and the correctness relation -/

section Coins

variable {PK SK K E Rg Re : Type}

variable [Fintype Rg] [Nonempty Rg] [Fintype Re] [Nonempty Re]

/-- The initial distribution of `kemCKA`: a generated key pair is the public value and both
initial states. -/
noncomputable def kemInitP (KEM : KEMScheme PK SK K E) [KEMCoins KEM Rg Re] :
    PMF ((Option E × PK) × (PK × SK) × (PK × SK)) :=
  (PMF.uniformFintype Rg).map fun r =>
    ((none, (KEMCoins.kgenR (KEM := KEM) r).1), KEMCoins.kgenR (KEM := KEM) r,
      KEMCoins.kgenR (KEM := KEM) r)

/-- The initialisation of `kemCKA` of a sound KEM is the lift of `kemInitP`. -/
theorem kemCKA_init_eq [Inhabited K] (KEM : KEMScheme PK SK K E) [KEMCoins KEM Rg Re]
    (hS : KEMCoins.Sound KEM) : (kemCKA KEM).init = liftPMF (kemInitP KEM) := by
  unfold kemCKA kemInitP
  dsimp only
  rw [hS.1]
  simp only [sample_eq_liftPMF, liftPMF_bind_pure, PMF.map_comp]
  rfl

/-- The correctness relation of `kemCKA`: the encapsulation key held by the sender and the
decapsulation key held by the receiver are a generated key pair. -/
def kemCKARel (KEM : KEMScheme PK SK K E) [KEMCoins KEM Rg Re] (s r : PK × SK) : Prop :=
  ∃ rg, s.1 = (KEMCoins.kgenR (KEM := KEM) rg).1 ∧ r.2 = (KEMCoins.kgenR (KEM := KEM) rg).2

omit [Fintype Rg] [Nonempty Rg] [Fintype Re] [Nonempty Re] in
/-- **Correctness of `kemCKA`** of a correct KEM along `kemCKARel`. -/
theorem kemCKA_ckaCorrect [Inhabited K] (KEM : KEMScheme PK SK K E) [KEMCoins KEM Rg Re]
    (hC : KEMCoins.Correct KEM) : CKACorrect (kemCKA KEM) (kemCKARel KEM) where
  key s r x h := by
    obtain ⟨rg, h1, h2⟩ := h
    simp only [kemCKACoins_sendR, kemSendOf]
    change KEM.decap r.2 _ = _
    rw [h1, h2]
    exact hC rg x.1
  next s r x _ := ⟨x.2, rfl, rfl⟩

omit [Fintype Re] [Nonempty Re] in
/-- The initial states of `kemCKA` are related by `kemCKARel`. -/
theorem kemInitP_rel (KEM : KEMScheme PK SK K E) [KEMCoins KEM Rg Re] :
    ∀ i ∈ (kemInitP KEM).support, kemCKARel KEM i.2.1 i.2.2 := by
  intro i hi
  simp only [kemInitP, PMF.support_map, Set.mem_image] at hi
  obtain ⟨r, -, rfl⟩ := hi
  exact ⟨r, rfl, rfl⟩

end Coins

/-! ## The steps of the game, of the eager game and of the simulator -/

section Steps

variable {PK SK K E Rg Re : Type}

/-- The step of the oracle of the corruption game of `kemCKA` with the key generation `kg` and
the encapsulation `en`, on the drawn randomness `e.1` of a send and the drawn key `e.2` (the
uniform challenge key of the ideal game). -/
def kemStepOf (kg : Rg → PK × SK) (en : PK → Re → K × E) (ΔFS ΔPCS t : ℕ) (ideal : Bool)
    (s : CKAGameSt (PK × SK) (Option E × PK)) (q : CKAQuery) (e : (Re × Rg) × K) :
    CKAAns (PK × SK) (Option E × PK) K (Re × Rg) × CKAGameSt (PK × SK) (Option E × PK) :=
  match q with
  | .send p =>
    if s.canSend p then
      (.out (kemSendOf kg en (s.st p) e.1).2.1 (kemSendOf kg en (s.st p) e.1).2.2,
        s.sent p (kemSendOf kg en (s.st p) e.1).1 (kemSendOf kg en (s.st p) e.1).2.1)
    else (.none, s)
  | .recv p => if s.canRecv p then (.none, s.recvd p (s.msg.2, (s.st p).2)) else (.none, s)
  | .chall p =>
    if s.canSend p && s.t p + 1 == t then
      (.out (kemSendOf kg en (s.st p) e.1).2.1
          (if ideal then e.2 else (kemSendOf kg en (s.st p) e.1).2.2),
        s.sent p (kemSendOf kg en (s.st p) e.1).1 (kemSendOf kg en (s.st p) e.1).2.1)
    else (.none, s)
  | .corrupt p => (if ckaAllowCorr ΔFS ΔPCS t s p then .state (s.st p) else .none, s)
  | .sendLeak p =>
    if ckaAllowLeak ΔPCS t s p then
      (.leak (kemSendOf kg en (s.st p) e.1).2.1 (kemSendOf kg en (s.st p) e.1).2.2 e.1,
        s.sent p (kemSendOf kg en (s.st p) e.1).1 (kemSendOf kg en (s.st p) e.1).2.1)
    else (.none, s)

/-- **The step of the simulator** with the KEM-CPA challenge `(pk, ek, kc)` and its own
randomness `ra` and `rb`: as `kemStepOf`, except that the send of epoch `t - 1` sends `pk` as
fresh encapsulation key, encapsulating with `ra`, and that the challenge has the encapsulation
`ek`, the key `kc` and the fresh key pair of `rb`. The decapsulation key stored for the send of
epoch `t - 1` is the drawn one, which the game never reveals. -/
def kemSimStepOf (kg : Rg → PK × SK) (en : PK → Re → K × E) (ΔFS ΔPCS t : ℕ) (pk : PK) (ek : E)
    (kc : K) (ra : Re) (rb : Rg) (s : CKAGameSt (PK × SK) (Option E × PK)) (q : CKAQuery)
    (e : (Re × Rg) × K) :
    CKAAns (PK × SK) (Option E × PK) K (Re × Rg) × CKAGameSt (PK × SK) (Option E × PK) :=
  match q with
  | .send p =>
    if s.canSend p then
      if s.t p + 2 == t then
        (.out (some (en (s.st p).1 ra).2, pk) (en (s.st p).1 ra).1,
          s.sent p ((s.st p).1, (kg e.1.2).2) (some (en (s.st p).1 ra).2, pk))
      else
        (.out (kemSendOf kg en (s.st p) e.1).2.1 (kemSendOf kg en (s.st p) e.1).2.2,
          s.sent p (kemSendOf kg en (s.st p) e.1).1 (kemSendOf kg en (s.st p) e.1).2.1)
    else (.none, s)
  | .recv p => if s.canRecv p then (.none, s.recvd p (s.msg.2, (s.st p).2)) else (.none, s)
  | .chall p =>
    if s.canSend p then
      if s.t p + 1 == t then
        (.out (some ek, (kg rb).1) kc, s.sent p ((s.st p).1, (kg rb).2) (some ek, (kg rb).1))
      else (.none, s)
    else (.none, s)
  | .corrupt p => (if ckaAllowCorr ΔFS ΔPCS t s p then .state (s.st p) else .none, s)
  | .sendLeak p =>
    if ckaAllowLeak ΔPCS t s p then
      (.leak (kemSendOf kg en (s.st p) e.1).2.1 (kemSendOf kg en (s.st p) e.1).2.2 e.1,
        s.sent p (kemSendOf kg en (s.st p) e.1).1 (kemSendOf kg en (s.st p) e.1).2.1)
    else (.none, s)

/-- The step of the eager game: the send of epoch `t - 1` uses the draw `va`, the challenge the
draw `vb`. -/
def kemEagerStepOf (kg : Rg → PK × SK) (en : PK → Re → K × E) (ΔFS ΔPCS t : ℕ) (ideal : Bool)
    (va vb : (Re × Rg) × K) : CKAGameSt (PK × SK) (Option E × PK) → CKAQuery →
      (Re × Rg) × K →
      CKAAns (PK × SK) (Option E × PK) K (Re × Rg) × CKAGameSt (PK × SK) (Option E × PK) :=
  OracleAdv.eagerStep (OracleAdv.eagerStep (kemStepOf kg en ΔFS ΔPCS t ideal) (dhCritA t) va)
    (dhCritB t) vb

/-- The steps of the KEM game do not decrease the counters. -/
theorem kemStepOf_t_le (kg : Rg → PK × SK) (en : PK → Re → K × E) (ΔFS ΔPCS t : ℕ)
    (ideal : Bool) (s : CKAGameSt (PK × SK) (Option E × PK)) (q : CKAQuery) (e : (Re × Rg) × K)
    (r : CKAParty) : s.t r ≤ (kemStepOf kg en ΔFS ΔPCS t ideal s q e).2.t r := by
  cases q with
  | send p =>
    simp only [kemStepOf]; split
    · exact CKAGameSt.le_sent _ _ _ _ _
    · exact le_refl _
  | recv p =>
    simp only [kemStepOf]; split
    · exact CKAGameSt.le_recvd _ _ _ _
    · exact le_refl _
  | chall p =>
    simp only [kemStepOf]; split
    · exact CKAGameSt.le_sent _ _ _ _ _
    · exact le_refl _
  | corrupt p => exact le_refl _
  | sendLeak p =>
    simp only [kemStepOf]; split
    · exact CKAGameSt.le_sent _ _ _ _ _
    · exact le_refl _

/-- The steps of the KEM game keep the states after the send of epoch `t - 1`. -/
theorem kemDoneA_step (kg : Rg → PK × SK) (en : PK → Re → K × E) (ΔFS ΔPCS t : ℕ)
    (ideal : Bool) (s : CKAGameSt (PK × SK) (Option E × PK)) (q : CKAQuery) (e : (Re × Rg) × K)
    (h : dhDoneA t s) : dhDoneA t (kemStepOf kg en ΔFS ΔPCS t ideal s q e).2 := by
  have := kemStepOf_t_le kg en ΔFS ΔPCS t ideal s q e .A
  have := kemStepOf_t_le kg en ΔFS ΔPCS t ideal s q e .B
  unfold dhDoneA at *; omega

/-- The steps of the KEM game keep the states after the challenge. -/
theorem kemDoneB_step (kg : Rg → PK × SK) (en : PK → Re → K × E) (ΔFS ΔPCS t : ℕ)
    (ideal : Bool) (s : CKAGameSt (PK × SK) (Option E × PK)) (q : CKAQuery) (e : (Re × Rg) × K)
    (h : dhDoneB t s) : dhDoneB t (kemStepOf kg en ΔFS ΔPCS t ideal s q e).2 := by
  have := kemStepOf_t_le kg en ΔFS ΔPCS t ideal s q e .A
  have := kemStepOf_t_le kg en ΔFS ΔPCS t ideal s q e .B
  unfold dhDoneB at *; omega

/-- The send of epoch `t - 1` leads to the states after it. -/
theorem kemDoneA_crit (kg : Rg → PK × SK) (en : PK → Re → K × E) (ΔFS ΔPCS t : ℕ)
    (ideal : Bool) (s : CKAGameSt (PK × SK) (Option E × PK)) (q : CKAQuery) (e : (Re × Rg) × K)
    (h : dhCritA t s q = true) : dhDoneA t (kemStepOf kg en ΔFS ΔPCS t ideal s q e).2 := by
  cases q with
  | send p =>
    simp only [dhCritA, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hc, ht⟩ := h
    simp only [kemStepOf, hc, ite_true]
    have hs := CKAGameSt.sum_t s p
    have hAB := ((CKAGameSt.canSend_iff s p).1 hc).1
    have h1 := CKAGameSt.t_eq_of_eq hAB p
    have := CKAGameSt.sum_sent s p (kemSendOf kg en (s.st p) e.1).1
      (kemSendOf kg en (s.st p) e.1).2.1
    unfold dhDoneA; omega
  | _ => simp [dhCritA] at h

/-- The challenge of the game after the first eager hop leads to the states after it. -/
theorem kemDoneB_crit (kg : Rg → PK × SK) (en : PK → Re → K × E) (ΔFS ΔPCS t : ℕ)
    (ideal : Bool) (va : (Re × Rg) × K) (s : CKAGameSt (PK × SK) (Option E × PK)) (q : CKAQuery)
    (e : (Re × Rg) × K) (h : dhCritB t s q = true) :
    dhDoneB t (OracleAdv.eagerStep (kemStepOf kg en ΔFS ΔPCS t ideal) (dhCritA t) va
      s q e).2 := by
  cases q with
  | chall p =>
    simp only [dhCritB, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hc, ht⟩ := h
    simp only [OracleAdv.eagerStep, dhCritA, Bool.false_eq_true, ite_false, kemStepOf, hc, ht,
      beq_self_eq_true, Bool.and_self, ite_true]
    have hs := CKAGameSt.sum_t s p
    have hAB := ((CKAGameSt.canSend_iff s p).1 hc).1
    have h1 := CKAGameSt.t_eq_of_eq hAB p
    have := CKAGameSt.sum_sent s p (kemSendOf kg en (s.st p) e.1).1
      (kemSendOf kg en (s.st p) e.1).2.1
    unfold dhDoneB; omega
  | _ => simp [dhCritB] at h

/-- The steps of the game after the first eager hop keep the states after the challenge. -/
theorem kemDoneB_eager (kg : Rg → PK × SK) (en : PK → Re → K × E) (ΔFS ΔPCS t : ℕ)
    (ideal : Bool) (va : (Re × Rg) × K) (s : CKAGameSt (PK × SK) (Option E × PK)) (q : CKAQuery)
    (e : (Re × Rg) × K) (h : dhDoneB t s) :
    dhDoneB t (OracleAdv.eagerStep (kemStepOf kg en ΔFS ΔPCS t ideal) (dhCritA t) va
      s q e).2 := by
  obtain ⟨e', he⟩ := OracleAdv.eagerStep_exists (kemStepOf kg en ΔFS ΔPCS t ideal)
    (dhCritA t) va s q e
  rw [he]
  exact kemDoneB_step kg en ΔFS ΔPCS t ideal s q e' h

end Steps

/-! ## The game as a probability mass function -/

section Game

variable {PK SK K E Rg Re α : Type} [Fintype Rg] [Nonempty Rg] [Fintype Re] [Nonempty Re]
  [Fintype K] [Nonempty K]

/-- The uniform draw of the randomness of a send and of a key, as three independent draws. -/
theorem kemDraw_bind {β : Type} (f : (Re × Rg) × K → PMF β) :
    (PMF.uniformFintype ((Re × Rg) × K)).bind f =
      (PMF.uniformFintype Re).bind fun re => (PMF.uniformFintype Rg).bind fun rg =>
        (PMF.uniformFintype K).bind fun u => f ((re, rg), u) := by
  simp only [PMF.uniform_prod_eq_bind, PMF.bind_bind, PMF.bind_map, Function.comp_def]

/-- A function of the key-generation randomness of the draw only sees a uniform draw. -/
theorem kemDraw_bind_rg {β : Type} (f : Rg → PMF β) :
    (PMF.uniformFintype ((Re × Rg) × K)).bind (fun v => f v.1.2) =
      (PMF.uniformFintype Rg).bind f := by
  rw [kemDraw_bind]
  simp only [PMF.bind_const]

/-- **The oracle of `kemCKA` in normal form.** Each oracle distribution of the game of
`kemCKA KEM` is the distribution of the step `kemStepOf` on a uniform draw. -/
theorem kemCKA_oracleP_eq [Inhabited K] (KEM : KEMScheme PK SK K E) [KEMCoins KEM Rg Re]
    (ΔFS ΔPCS t : ℕ) (ideal : Bool) (s : CKAGameSt (PK × SK) (Option E × PK)) (q : CKAQuery) :
    ckaOracleP (kemCKA KEM) ΔFS ΔPCS t ideal s q =
      (PMF.uniformFintype ((Re × Rg) × K)).map (kemStepOf (KEMCoins.kgenR (KEM := KEM))
        (KEMCoins.encapR (KEM := KEM)) ΔFS ΔPCS t ideal s q) := by
  rw [← PMF.bind_pure_comp, kemDraw_bind]
  cases ideal <;> cases q <;> simp only [ckaOracleP, kemStepOf, Function.comp_apply] <;> split <;>
    simp [PMF.bind_const, PMF.uniform_prod_eq_bind, PMF.bind_map,
      Function.comp_def] <;> rfl

/-- The distribution of the output of the game of `kemCKA` with the key generation `kg`, the
encapsulation `en` and the challenge epoch `t`: an initial key pair `kg x₀`, then the run of the
oracle in normal form with the step `kemStepOf`. -/
noncomputable def kemCKAGamePMFOf (kg : Rg → PK × SK) (en : PK → Re → K × E) (ΔFS ΔPCS t : ℕ)
    (ideal : Bool)
    (play : Option E × PK → OracleAdv CKAQuery (CKAAns (PK × SK) (Option E × PK) K (Re × Rg)) α) :
    PMF α :=
  (PMF.uniformFintype Rg).bind fun x₀ =>
    (OracleAdv.run (OracleAdv.nfOracle (PMF.uniformFintype ((Re × Rg) × K))
      (kemStepOf kg en ΔFS ΔPCS t ideal)) (play (none, (kg x₀).1))
      (CKAGameSt.init (none, (kg x₀).1) (kg x₀) (kg x₀))).map Prod.fst

/-- The corruption game of `kemCKA` of a sound KEM is the lifted distribution `kemCKAGamePMFOf`
after the choice of the challenge epoch. -/
theorem kemCKA_game_eq [Inhabited K] (KEM : KEMScheme PK SK K E) [KEMCoins KEM Rg Re]
    (hS : KEMCoins.Sound KEM) (ΔFS ΔPCS : ℕ) (ideal : Bool)
    (A : CKACorruptAdv (PK × SK) (Option E × PK) K (Re × Rg) α) :
    cka_corrupt_game (kemCKA KEM) ΔFS ΔPCS ideal A =
      liftPMF (A.tStar.bind fun t => kemCKAGamePMFOf (KEMCoins.kgenR (KEM := KEM))
        (KEMCoins.encapR (KEM := KEM)) ΔFS ΔPCS t ideal (A.play t)) := by
  rw [cka_corrupt_game_eq_liftPMF _ (kemCKACoins_sound KEM hS) _ (kemCKA_init_eq KEM hS)]
  have hO : ckaOracleP (kemCKA KEM) ΔFS ΔPCS = fun t ideal =>
      OracleAdv.nfOracle (PMF.uniformFintype ((Re × Rg) × K))
        (kemStepOf (KEMCoins.kgenR (KEM := KEM)) (KEMCoins.encapR (KEM := KEM)) ΔFS ΔPCS t
          ideal) := by
    funext t ideal s q
    exact kemCKA_oracleP_eq KEM ΔFS ΔPCS t ideal s q
  simp only [hO, kemInitP, PMF.bind_map, kemCKAGamePMFOf]
  rfl

/-- The two eager hops: the draws of the send of epoch `t - 1` and of the challenge are drawn
in advance. -/
theorem run_kemStep_eager (kg : Rg → PK × SK) (en : PK → Re → K × E) (ΔFS ΔPCS t : ℕ)
    (ideal : Bool)
    (A : OracleAdv CKAQuery (CKAAns (PK × SK) (Option E × PK) K (Re × Rg)) α)
    (s : CKAGameSt (PK × SK) (Option E × PK)) :
    OracleAdv.run (OracleAdv.nfOracle (PMF.uniformFintype ((Re × Rg) × K))
        (kemStepOf kg en ΔFS ΔPCS t ideal)) A s =
      (PMF.uniformFintype ((Re × Rg) × K)).bind fun va =>
        (PMF.uniformFintype ((Re × Rg) × K)).bind fun vb =>
          OracleAdv.run (OracleAdv.nfOracle (PMF.uniformFintype ((Re × Rg) × K))
            (kemEagerStepOf kg en ΔFS ΔPCS t ideal va vb)) A s := by
  rw [OracleAdv.run_nf_eq_eager _ _ (dhCritA t) (dhDoneA t)
    (kemDoneA_crit _ _ _ _ _ _) (kemDoneA_step _ _ _ _ _ _) (dhDoneA_noCrit t)]
  congr 1; funext va
  exact OracleAdv.run_nf_eq_eager _ _ (dhCritB t) (dhDoneB t)
    (kemDoneB_crit _ _ _ _ _ _ va) (kemDoneB_eager _ _ _ _ _ _ va) (dhDoneB_noCrit t) A s

/-- The game of `kemCKA` as the eager game, with the initial key pair `kg (dhX0 t va.1.2 x₀)`:
at the challenge epoch `1` the key pair of the draw of the send of epoch `0`. -/
theorem kemCKAGamePMFOf_eager (kg : Rg → PK × SK) (en : PK → Re → K × E) (ΔFS ΔPCS t : ℕ)
    (ideal : Bool)
    (play : Option E × PK → OracleAdv CKAQuery (CKAAns (PK × SK) (Option E × PK) K (Re × Rg)) α) :
    kemCKAGamePMFOf kg en ΔFS ΔPCS t ideal play =
      (PMF.uniformFintype Rg).bind fun x₀ => (PMF.uniformFintype ((Re × Rg) × K)).bind fun va =>
        (PMF.uniformFintype ((Re × Rg) × K)).bind fun vb =>
          (OracleAdv.run (OracleAdv.nfOracle (PMF.uniformFintype ((Re × Rg) × K))
            (kemEagerStepOf kg en ΔFS ΔPCS t ideal va vb))
            (play (none, (kg (dhX0 t va.1.2 x₀)).1))
            (CKAGameSt.init (none, (kg (dhX0 t va.1.2 x₀)).1) (kg (dhX0 t va.1.2 x₀))
              (kg (dhX0 t va.1.2 x₀)))).map Prod.fst := by
  unfold kemCKAGamePMFOf
  by_cases ht : t = 1
  · subst ht
    have hA : ∀ va : (Re × Rg) × K,
        OracleAdv.eagerStep (kemStepOf kg en ΔFS ΔPCS 1 ideal) (dhCritA 1) va =
          kemStepOf kg en ΔFS ΔPCS 1 ideal := by
      intro va; funext s q e
      simp only [OracleAdv.eagerStep, dhCritA_one, Bool.false_eq_true, ite_false]
    simp only [kemEagerStepOf, hA, dhX0, ite_true, PMF.bind_const]
    rw [kemDraw_bind_rg (fun x₀ => (PMF.uniformFintype ((Re × Rg) × K)).bind fun vb =>
      (OracleAdv.run (OracleAdv.nfOracle (PMF.uniformFintype ((Re × Rg) × K))
        (OracleAdv.eagerStep (kemStepOf kg en ΔFS ΔPCS 1 ideal) (dhCritB 1) vb))
        (play (none, (kg x₀).1)) (CKAGameSt.init (none, (kg x₀).1) (kg x₀) (kg x₀))).map
          Prod.fst)]
    congr 1; funext x₀
    rw [OracleAdv.run_nf_eq_eager _ _ (dhCritB 1) (dhDoneB 1)
      (fun s q e h => by
        have := kemDoneB_crit kg en ΔFS ΔPCS 1 ideal (Classical.arbitrary _) s q e h
        rwa [hA] at this)
      (kemDoneB_step _ _ _ _ _ _) (dhDoneB_noCrit 1), PMF.map_bind]
  · simp only [dhX0, ht, ite_false, run_kemStep_eager, PMF.map_bind]

end Game

/-! ## The simulation relation -/

/-- The decapsulation key of party `p` is not determined by the view of the simulator: the
receiver `(ckaSender t).other` of the challenge holds the embedded key from epoch `t - 1` to
epoch `t`, and at the challenge epoch `1` the challenged party holds it before its first send. -/
def kemHidden {St Msg : Type} (t : ℕ) (s : CKAGameSt St Msg) (p : CKAParty) : Prop :=
  if p = ckaSender t then t = 1 ∧ s.t p = 0 else t - 1 ≤ s.t p ∧ s.t p ≤ t

/-- A send of `p` does not change the hidden window of another party. -/
theorem kemHidden_sent_of_ne {St Msg : Type} (t : ℕ) (s : CKAGameSt St Msg) {p q : CKAParty}
    (hq : q ≠ p) (x : St) (T : Msg) : kemHidden t (s.sent p x T) q ↔ kemHidden t s q := by
  simp only [kemHidden, CKAGameSt.sent_t, hq, ite_false]

/-- A receive of `p` does not change the hidden window of another party. -/
theorem kemHidden_recvd_of_ne {St Msg : Type} (t : ℕ) (s : CKAGameSt St Msg) {p q : CKAParty}
    (hq : q ≠ p) (x : St) : kemHidden t (s.recvd p x) q ↔ kemHidden t s q := by
  simp only [kemHidden, CKAGameSt.recvd_t, hq, ite_false]

/-- A party that the gates with `1 ≤ ΔFS` and `2 ≤ ΔPCS` allow to corrupt is outside its
hidden window. -/
theorem not_kemHidden_of_allowCorr {St Msg : Type} {ΔFS ΔPCS t : ℕ} {s : CKAGameSt St Msg}
    {p : CKAParty} (hFS : 1 ≤ ΔFS) (hPCS : 2 ≤ ΔPCS) (h : ckaAllowCorr ΔFS ΔPCS t s p = true) :
    ¬ kemHidden t s p := by
  intro hh
  have hp : s.t p ≤ max (s.t .A) (s.t .B) := by
    cases p
    · exact le_max_left _ _
    · exact le_max_right _ _
  simp only [ckaAllowCorr, Bool.or_eq_true, decide_eq_true_eq] at h
  unfold kemHidden at hh
  split at hh <;> omega

section Rel

variable {PK SK K E : Type}

/-- **The simulation relation** with the embedded encapsulation key `pkA`, between a state `s`
of the eager game and a state `σ` of the simulator: equal counters, messages and encapsulation
keys, and equal decapsulation keys outside the hidden window; and the invariants of the eager
game: the counters are equal or the last sender is one epoch ahead, the message of epoch
`t - 1` in transit carries `pkA`, and the challenged party holds `pkA` before the challenge. -/
structure KEMRel (pkA : PK) (t : ℕ) (s σ : CKAGameSt (PK × SK) (Option E × PK)) : Prop where
  /-- Equal counters. -/
  t_eq : s.t = σ.t
  /-- Equal messages in transit. -/
  msg_eq : s.msg = σ.msg
  /-- Equal encapsulation keys. -/
  h_eq : ∀ p, (s.st p).1 = (σ.st p).1
  /-- Equal decapsulation keys outside the hidden window. -/
  y_eq : ∀ p, ¬ kemHidden t s p → (s.st p).2 = (σ.st p).2
  /-- The counters are equal or the last sender is one epoch ahead. -/
  shape : s.t .A = s.t .B ∨ ∃ p, s.t p = s.t p.other + 1 ∧ ckaSender (s.t p) = p
  /-- The message of epoch `t - 1` in transit carries `pkA`. -/
  inv_msg : s.t (ckaSender t).other = t - 1 → s.t (ckaSender t) + 2 = t → s.msg.2 = pkA
  /-- The challenged party holds `pkA` before the challenge. -/
  inv_Q : 1 ≤ t → s.t (ckaSender t) = t - 1 → s.t (ckaSender t).other = t - 1 →
    (s.st (ckaSender t)).1 = pkA

namespace KEMRel

variable {pkA : PK} {t : ℕ} {s σ : CKAGameSt (PK × SK) (Option E × PK)}

/-- The simulation relation after a send of party `p` to the states `x` (eager game) and `x'`
(simulator) with the message `T`. -/
theorem sent (h : KEMRel pkA t s σ) {p : CKAParty} (hc : s.canSend p = true) (x x' : PK × SK)
    (T : Option E × PK) (hx : x.1 = x'.1) (hy : ¬ kemHidden t (s.sent p x T) p → x.2 = x'.2)
    (hT : p = (ckaSender t).other → s.t p + 2 = t → T.2 = pkA) :
    KEMRel pkA t (s.sent p x T) (σ.sent p x' T) := by
  rw [CKAGameSt.canSend_iff] at hc
  obtain ⟨hAB, hp⟩ := hc
  have htp : s.t p = s.t .A := CKAGameSt.t_eq_of_eq hAB p
  have hto : s.t p.other = s.t .A := CKAGameSt.t_other_eq_of_eq hAB p
  refine ⟨?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
  · funext q
    simp only [CKAGameSt.sent_t, h.t_eq]
  · intro q
    simp only [CKAGameSt.sent_st]
    split
    · exact hx
    · exact h.h_eq q
  · intro q hq
    by_cases hqp : q = p
    · subst hqp
      simp only [CKAGameSt.sent_st, ite_true]
      exact hy hq
    · simp only [CKAGameSt.sent_st, hqp, ite_false]
      exact h.y_eq q ((not_congr (kemHidden_sent_of_ne t s hqp _ _)).1 hq)
  · right
    refine ⟨p, ?_, ?_⟩
    · simp only [CKAGameSt.sent_t, ite_true, CKAParty.other_ne, ite_false]
      omega
    · simp only [CKAGameSt.sent_t, ite_true, htp, hp]
  · intro h1 h2
    simp only [CKAGameSt.sent_msg]
    rcases CKAParty.eq_or_eq_other p (ckaSender t) with hP | hP
    · exfalso
      rw [← hP] at h1 h2
      simp only [CKAGameSt.sent_t, ite_true, CKAParty.other_ne, ite_false] at h1 h2
      omega
    · have hQ : ckaSender t = p.other := by rw [hP, CKAParty.other_other]
      rw [hQ] at h1 h2
      simp only [CKAGameSt.sent_t, CKAParty.other_other, ite_true, CKAParty.other_ne,
        ite_false] at h1 h2
      exact hT hP (by omega)
  · intro _ h1 h2
    exfalso
    rcases CKAParty.eq_or_eq_other p (ckaSender t) with hP | hP
    · rw [← hP] at h1 h2
      simp only [CKAGameSt.sent_t, ite_true, CKAParty.other_ne, ite_false] at h1 h2
      omega
    · have hQ : ckaSender t = p.other := by rw [hP, CKAParty.other_other]
      rw [hQ] at h1 h2
      simp only [CKAGameSt.sent_t, CKAParty.other_other, ite_true, CKAParty.other_ne,
        ite_false] at h1 h2
      omega

/-- The simulation relation after a receive of party `p`. -/
theorem recvd (h : KEMRel pkA t s σ) {p : CKAParty} (hc : s.canRecv p = true) :
    KEMRel pkA t (s.recvd p (s.msg.2, (s.st p).2)) (σ.recvd p (σ.msg.2, (σ.st p).2)) := by
  rw [CKAGameSt.canRecv_iff] at hc
  have hahead : ckaSender (s.t p.other) = p.other := by
    rcases h.shape with hAB | ⟨q, hq1, hq2⟩
    · exfalso
      have h1 := CKAGameSt.t_eq_of_eq hAB p
      have h2 := CKAGameSt.t_other_eq_of_eq hAB p
      omega
    · by_cases hqp : q = p
      · subst hqp; omega
      · have hqo : q = p.other := (CKAParty.eq_or_eq_other q p).resolve_left hqp
        subst hqo; exact hq2
  have hsnd : ckaSender (s.t p + 1) = p.other := by rw [hc]; exact hahead
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · funext q
    simp only [CKAGameSt.recvd_t, h.t_eq]
  · simp only [CKAGameSt.recvd_msg, h.msg_eq]
  · intro q
    simp only [CKAGameSt.recvd_st]
    split
    · rw [h.msg_eq]
    · exact h.h_eq q
  · intro q hq
    by_cases hqp : q = p
    · subst hqp
      simp only [CKAGameSt.recvd_st, ite_true]
      refine h.y_eq _ fun hh => hq ?_
      unfold kemHidden at hh ⊢
      simp only [CKAGameSt.recvd_t, ite_true]
      by_cases hS : q = ckaSender t
      · rw [ite_eq_left hS] at hh
        exfalso
        obtain ⟨h1, h2⟩ := hh
        rw [h2, Nat.zero_add] at hsnd
        rw [h1] at hS
        rw [← hS] at hsnd
        exact CKAParty.ne_other _ hsnd
      · rw [ite_eq_right hS] at hh ⊢
        refine ⟨by omega, ?_⟩
        by_contra hlt
        have heq : s.t q = t := by omega
        have hq' : q = (ckaSender t).other :=
          (CKAParty.eq_or_eq_other q (ckaSender t)).resolve_left hS
        rw [heq, ckaSender_succ, ← hq'] at hsnd
        exact CKAParty.ne_other _ hsnd
    · simp only [CKAGameSt.recvd_st, hqp, ite_false]
      exact h.y_eq q ((not_congr (kemHidden_recvd_of_ne t s hqp _)).1 hq)
  · left
    cases p <;> simp only [CKAGameSt.recvd_t, ite_true, reduceCtorEq, ite_false] <;>
      simp only [CKAParty.other] at hc <;> omega
  · intro h1 h2
    exfalso
    rcases CKAParty.eq_or_eq_other p (ckaSender t) with hP | hP
    · rw [← hP] at h1 h2
      simp only [CKAGameSt.recvd_t, ite_true, CKAParty.other_ne, ite_false] at h1 h2
      omega
    · have hQ : ckaSender t = p.other := by rw [hP, CKAParty.other_other]
      rw [hQ] at h1 h2
      simp only [CKAGameSt.recvd_t, CKAParty.other_other, ite_true, CKAParty.other_ne,
        ite_false] at h1 h2
      omega
  · intro h0 h1 h2
    rcases CKAParty.eq_or_eq_other p (ckaSender t) with hP | hP
    · have hm := h.inv_msg
      rw [← hP] at h1 h2 hm ⊢
      simp only [CKAGameSt.recvd_t, CKAGameSt.recvd_st, ite_true, CKAParty.other_ne,
        ite_false] at h1 h2 ⊢
      exact hm h2 (by omega)
    · exfalso
      have hQ : ckaSender t = p.other := by rw [hP, CKAParty.other_other]
      rw [hQ] at h1 h2
      simp only [CKAGameSt.recvd_t, CKAParty.other_other, ite_true, CKAParty.other_ne,
        ite_false] at h1 h2
      have ht : t = s.t p + 1 + 1 := by omega
      rw [ht, ckaSender_succ, hsnd, CKAParty.other_other] at hQ
      exact CKAParty.ne_other _ hQ

end KEMRel

variable {Rg Re : Type}

/-- **The simulation step.** Let `1 ≤ ΔFS` and `2 ≤ ΔPCS`. From related states, the eager game
with the draws `va` and `vb` and the simulator with the KEM-CPA challenge of the key pair
`kg va.1.2` and the encapsulation randomness `vb.1.1`, the randomness `va.1.1` and `vb.1.2`, and
the key `vb.2` in the ideal game, give equal answers and related states. -/
theorem kemRel_step (kg : Rg → PK × SK) (en : PK → Re → K × E) {ΔFS ΔPCS : ℕ} (hFS : 1 ≤ ΔFS)
    (hPCS : 2 ≤ ΔPCS) (t : ℕ) (ideal : Bool) (va vb : (Re × Rg) × K)
    (s σ : CKAGameSt (PK × SK) (Option E × PK)) (h : KEMRel (kg va.1.2).1 t s σ) (q : CKAQuery)
    (e : (Re × Rg) × K) :
    (kemEagerStepOf kg en ΔFS ΔPCS t ideal va vb s q e).1 =
        (kemSimStepOf kg en ΔFS ΔPCS t (kg va.1.2).1 (en (kg va.1.2).1 vb.1.1).2
          (if ideal then vb.2 else (en (kg va.1.2).1 vb.1.1).1) va.1.1 vb.1.2 σ q e).1 ∧
      KEMRel (kg va.1.2).1 t (kemEagerStepOf kg en ΔFS ΔPCS t ideal va vb s q e).2
        (kemSimStepOf kg en ΔFS ΔPCS t (kg va.1.2).1 (en (kg va.1.2).1 vb.1.1).2
          (if ideal then vb.2 else (en (kg va.1.2).1 vb.1.1).1) va.1.1 vb.1.2 σ q e).2 := by
  have hcs := CKAGameSt.canSend_eq_of_t h.t_eq
  have hcr := CKAGameSt.canRecv_eq_of_t h.t_eq
  have hco := CKAGameSt.allowCorr_eq_of_t h.t_eq
  have hcl := CKAGameSt.allowLeak_eq_of_t h.t_eq
  have hσt : σ.t = s.t := h.t_eq.symm
  cases q with
  | send p =>
    simp only [kemEagerStepOf, OracleAdv.eagerStep, dhCritA, dhCritB, Bool.false_eq_true,
      ite_false, kemStepOf, kemSimStepOf, hcs, hσt]
    rcases (Bool.eq_false_or_eq_true (s.canSend p)).symm with hc | hc
    · simp only [hc, ite_false, Bool.false_eq_true]; exact ⟨by simp, by simpa using h⟩
    · simp only [hc, ite_true, Bool.true_and]
      obtain ⟨hAB, hp⟩ := (CKAGameSt.canSend_iff s p).1 hc
      have htp := CKAGameSt.t_eq_of_eq hAB p
      by_cases ht2 : s.t p + 2 = t
      · simp only [ht2, beq_self_eq_true, ite_true, kemSendOf, ← h.h_eq p]
        have hP : ckaSender t = p.other := by
          rw [← ht2, show s.t p + 2 = s.t .A + 1 + 1 by omega, ckaSender_succ, hp]
        refine ⟨trivial, h.sent hc _ _ _ rfl ?_ fun _ _ => rfl⟩
        intro hh; exfalso; apply hh
        unfold kemHidden
        rw [ite_eq_right (by rw [hP]; exact CKAParty.ne_other p)]
        simp only [CKAGameSt.sent_t, ite_true]
        omega
      · have hne : (s.t p + 2 == t) = false := by simpa using ht2
        simp only [hne, Bool.false_eq_true, ite_false, kemSendOf, ← h.h_eq p]
        exact ⟨trivial, h.sent hc _ _ _ rfl (fun _ => rfl) fun _ h2 => absurd h2 ht2⟩
  | recv p =>
    simp only [kemEagerStepOf, OracleAdv.eagerStep, dhCritA, dhCritB, Bool.false_eq_true,
      ite_false, kemStepOf, kemSimStepOf, hcr]
    rcases (Bool.eq_false_or_eq_true (s.canRecv p)).symm with hc | hc
    · simp only [hc, ite_false, Bool.false_eq_true]; exact ⟨trivial, h⟩
    · simp only [hc, ite_true]; exact ⟨trivial, h.recvd hc⟩
  | chall p =>
    simp only [kemEagerStepOf, OracleAdv.eagerStep, dhCritA, dhCritB, Bool.false_eq_true,
      ite_false, kemStepOf, kemSimStepOf, hcs, hσt]
    rcases (Bool.eq_false_or_eq_true (s.canSend p && s.t p + 1 == t)).symm with hcb | hcb
    · rcases (Bool.eq_false_or_eq_true (s.canSend p)).symm with hc | hc
      · simp only [hc, Bool.false_and, ite_false, Bool.false_eq_true]; exact ⟨trivial, h⟩
      · have ht : (s.t p + 1 == t) = false := by simpa [hc] using hcb
        simp only [hc, ht, Bool.and_false, ite_true, ite_false, Bool.false_eq_true]
        exact ⟨trivial, h⟩
    · have hcb' := hcb
      simp only [Bool.and_eq_true] at hcb'
      simp only [hcb'.1, hcb'.2, Bool.and_self, ite_true]
      simp only [Bool.and_eq_true, beq_iff_eq] at hcb
      obtain ⟨hc, ht1⟩ := hcb
      obtain ⟨hAB, hp⟩ := (CKAGameSt.canSend_iff s p).1 hc
      have htp := CKAGameSt.t_eq_of_eq hAB p
      have hto := CKAGameSt.t_other_eq_of_eq hAB p
      have hP : ckaSender t = p := by rw [← ht1, htp, hp]
      have hpk : (s.st p).1 = (kg va.1.2).1 := by
        have := h.inv_Q (by omega) (by rw [hP]; omega) (by rw [hP]; omega)
        rwa [hP] at this
      have hpk' : (σ.st p).1 = (kg va.1.2).1 := by rw [← h.h_eq p, hpk]
      simp only [kemSendOf, hpk, hpk']
      refine ⟨by cases ideal <;> trivial, h.sent hc _ _ _ rfl (fun _ => rfl) ?_⟩
      intro hpP
      exfalso
      rw [hP] at hpP
      exact CKAParty.ne_other p hpP
  | corrupt p =>
    simp only [kemEagerStepOf, OracleAdv.eagerStep, dhCritA, dhCritB, Bool.false_eq_true,
      ite_false, kemStepOf, kemSimStepOf, hco]
    rcases (Bool.eq_false_or_eq_true (ckaAllowCorr ΔFS ΔPCS t s p)).symm with hg | hg
    · simp only [hg, ite_false, Bool.false_eq_true]; exact ⟨trivial, h⟩
    · simp only [hg, ite_true]
      refine ⟨?_, h⟩
      rw [Prod.ext (h.h_eq p) (h.y_eq p (not_kemHidden_of_allowCorr hFS hPCS hg))]
  | sendLeak p =>
    simp only [kemEagerStepOf, OracleAdv.eagerStep, dhCritA, dhCritB, Bool.false_eq_true,
      ite_false, kemStepOf, kemSimStepOf, hcl]
    rcases (Bool.eq_false_or_eq_true (ckaAllowLeak ΔPCS t s p)).symm with hl | hl
    · simp only [hl, ite_false, Bool.false_eq_true]; exact ⟨trivial, h⟩
    · simp only [hl, ite_true, kemSendOf, ← h.h_eq p]
      simp only [ckaAllowLeak, Bool.and_eq_true, decide_eq_true_eq] at hl
      obtain ⟨hc, ht3⟩ := hl
      exact ⟨trivial, h.sent hc _ _ _ rfl (fun _ => rfl) fun _ h2 => by omega⟩

/-- The initial states of the eager game and of the simulator are related. -/
theorem kemRel_init (kg : Rg → PK × SK) (t : ℕ) (a x₀ : Rg) :
    KEMRel (E := E) (kg a).1 t
      (CKAGameSt.init (none, (kg (dhX0 t a x₀)).1) (kg (dhX0 t a x₀)) (kg (dhX0 t a x₀)))
      (CKAGameSt.init (none, (kg (dhX0 t a x₀)).1) ((kg (dhX0 t a x₀)).1, (kg x₀).2)
        ((kg (dhX0 t a x₀)).1, (kg x₀).2)) := by
  refine ⟨rfl, rfl, fun p => by cases p <;> rfl, ?_, Or.inl rfl, ?_, ?_⟩
  · intro p hp
    by_cases ht : t = 1
    · exfalso; apply hp
      subst ht
      unfold kemHidden
      cases p <;> simp [CKAGameSt.init, ckaSender]
    · cases p <;> simp [CKAGameSt.init, dhX0, ht]
  · intro h1 h2
    have : (CKAGameSt.init (none, (kg (dhX0 t a x₀)).1) (kg (dhX0 t a x₀))
        (kg (dhX0 t a x₀)) : CKAGameSt (PK × SK) (Option E × PK)).t = fun _ => 0 := rfl
    rw [this] at h1 h2
    dsimp only at h1 h2
    omega
  · intro h0 h1 _
    have : (CKAGameSt.init (none, (kg (dhX0 t a x₀)).1) (kg (dhX0 t a x₀))
        (kg (dhX0 t a x₀)) : CKAGameSt (PK × SK) (Option E × PK)).t = fun _ => 0 := rfl
    rw [this] at h1
    dsimp only at h1
    have ht : t = 1 := by omega
    subst ht
    simp [CKAGameSt.init, ckaSender, dhX0]

end Rel

/-! ## The reduction -/

section Red

variable {PK SK K E Rg Re α : Type} [Fintype Rg] [Nonempty Rg] [Fintype Re] [Nonempty Re]
  [Fintype K] [Nonempty K]

/-- The simulator answers a query by drawing the randomness of a send and a key and running the
simulation step. -/
noncomputable def kemCorruptSimImplOf (kg : Rg → PK × SK) (en : PK → Re → K × E)
    (ΔFS ΔPCS t : ℕ) (pk : PK) (ek : E) (kc : K) (ra : Re) (rb : Rg)
    (σ : CKAGameSt (PK × SK) (Option E × PK)) (q : CKAQuery) :
    OracleAdv Empty Unit
      (CKAAns (PK × SK) (Option E × PK) K (Re × Rg) × CKAGameSt (PK × SK) (Option E × PK)) :=
  .rand (PMF.uniformFintype ((Re × Rg) × K)) fun e =>
    .ret (kemSimStepOf kg en ΔFS ΔPCS t pk ek kc ra rb σ q e)

/-- **The KEM-CPA reduction** as an oracle tree without queries. On the challenge
`y = (pk, ek, kc)` it draws the challenge epoch `t` of the adversary, an initial key-generation
randomness `x₀` and the randomness `ra` and `rb`; the public value of the initialisation is `pk`
if `t = 1` and the encapsulation key of `x₀` otherwise; it runs the adversary against the
simulator `kemCorruptSimImplOf` and returns its output. -/
noncomputable def kemCorruptTreeOf (kg : Rg → PK × SK) (en : PK → Re → K × E) (ΔFS ΔPCS : ℕ)
    (tStar : PMF ℕ)
    (play : ℕ → Option E × PK →
      OracleAdv CKAQuery (CKAAns (PK × SK) (Option E × PK) K (Re × Rg)) α)
    (y : PK × E × K) : OracleAdv Empty Unit α :=
  .rand tStar fun t =>
    .rand (PMF.uniformFintype Rg) fun x₀ =>
      .rand (PMF.uniformFintype Re) fun ra =>
        .rand (PMF.uniformFintype Rg) fun rb =>
          (OracleAdv.simulate (kemCorruptSimImplOf kg en ΔFS ΔPCS t y.1 y.2.1 y.2.2 ra rb)
            (play t (none, if t = 1 then y.1 else (kg x₀).1))
            (CKAGameSt.init (none, if t = 1 then y.1 else (kg x₀).1)
              (if t = 1 then y.1 else (kg x₀).1, (kg x₀).2)
              (if t = 1 then y.1 else (kg x₀).1, (kg x₀).2))).bind fun r => .ret r.1

/-- **The KEM-CPA reduction** `kemCorruptRed KEM ΔFS ΔPCS A`: the tree `kemCorruptTreeOf` with
the algorithms of the KEM, run as a distribution. -/
noncomputable def kemCorruptRed (KEM : KEMScheme PK SK K E) [KEMCoins KEM Rg Re]
    (ΔFS ΔPCS : ℕ) (A : CKACorruptAdv (PK × SK) (Option E × PK) K (Re × Rg) Bool) :
    PK × E × K → SPComp Bool := fun y =>
  liftPMF ((OracleAdv.run emptyOracle (kemCorruptTreeOf (KEMCoins.kgenR (KEM := KEM))
    (KEMCoins.encapR (KEM := KEM)) ΔFS ΔPCS A.tStar A.play y) ()).map Prod.fst)

/-- The run of the reduction tree is the run of the adversary against the simulation step. -/
theorem kemCorruptTreeOf_run (kg : Rg → PK × SK) (en : PK → Re → K × E) (ΔFS ΔPCS : ℕ)
    (tStar : PMF ℕ)
    (play : ℕ → Option E × PK →
      OracleAdv CKAQuery (CKAAns (PK × SK) (Option E × PK) K (Re × Rg)) α)
    (y : PK × E × K) :
    (OracleAdv.run emptyOracle (kemCorruptTreeOf kg en ΔFS ΔPCS tStar play y) ()).map
        Prod.fst =
      tStar.bind fun t => (PMF.uniformFintype Rg).bind fun x₀ =>
        (PMF.uniformFintype Re).bind fun ra => (PMF.uniformFintype Rg).bind fun rb =>
          (OracleAdv.run (OracleAdv.nfOracle (PMF.uniformFintype ((Re × Rg) × K))
            (kemSimStepOf kg en ΔFS ΔPCS t y.1 y.2.1 y.2.2 ra rb))
            (play t (none, if t = 1 then y.1 else (kg x₀).1))
            (CKAGameSt.init (none, if t = 1 then y.1 else (kg x₀).1)
              (if t = 1 then y.1 else (kg x₀).1, (kg x₀).2)
              (if t = 1 then y.1 else (kg x₀).1, (kg x₀).2))).map Prod.fst := by
  unfold kemCorruptTreeOf
  simp only [OracleAdv.run_rand, PMF.map_bind]
  congr 1; funext t; congr 1; funext x₀; congr 1; funext ra; congr 1; funext rb
  rw [OracleAdv.run_simulate_fst]
  have hsim : OracleAdv.simOracle (kemCorruptSimImplOf kg en ΔFS ΔPCS t y.1 y.2.1 y.2.2 ra rb)
      emptyOracle = OracleAdv.nfOracle (PMF.uniformFintype ((Re × Rg) × K)) (fun σu q e =>
        ((kemSimStepOf kg en ΔFS ΔPCS t y.1 y.2.1 y.2.2 ra rb σu.1 q e).1,
          ((kemSimStepOf kg en ΔFS ΔPCS t y.1 y.2.1 y.2.2 ra rb σu.1 q e).2, ()))) := by
    funext σu q
    simp only [OracleAdv.simOracle, kemCorruptSimImplOf, OracleAdv.run_rand, OracleAdv.run_ret,
      OracleAdv.nfOracle, ← PMF.bind_pure_comp, Function.comp_def, PMF.bind_bind,
      PMF.pure_bind]
  rw [hsim]
  exact OracleAdv.run_nf_map_fst_eq_of_rel _ _ _ (fun σu σ => σu.1 = σ)
    (fun σu σ h q e => by subst h; exact ⟨rfl, rfl⟩) _ _ _ rfl

/-- **The eager game is the simulation**, for the delays `1 ≤ ΔFS`, `2 ≤ ΔPCS`. -/
theorem kemCKA_eager_eq_sim (kg : Rg → PK × SK) (en : PK → Re → K × E) {ΔFS ΔPCS : ℕ}
    (hFS : 1 ≤ ΔFS) (hPCS : 2 ≤ ΔPCS) (t : ℕ) (ideal : Bool) (va vb : (Re × Rg) × K) (x₀ : Rg)
    (play : Option E × PK → OracleAdv CKAQuery (CKAAns (PK × SK) (Option E × PK) K (Re × Rg)) α) :
    (OracleAdv.run (OracleAdv.nfOracle (PMF.uniformFintype ((Re × Rg) × K))
        (kemEagerStepOf kg en ΔFS ΔPCS t ideal va vb))
        (play (none, (kg (dhX0 t va.1.2 x₀)).1))
        (CKAGameSt.init (none, (kg (dhX0 t va.1.2 x₀)).1) (kg (dhX0 t va.1.2 x₀))
          (kg (dhX0 t va.1.2 x₀)))).map Prod.fst =
      (OracleAdv.run (OracleAdv.nfOracle (PMF.uniformFintype ((Re × Rg) × K))
        (kemSimStepOf kg en ΔFS ΔPCS t (kg va.1.2).1 (en (kg va.1.2).1 vb.1.1).2
          (if ideal then vb.2 else (en (kg va.1.2).1 vb.1.1).1) va.1.1 vb.1.2))
        (play (none, (kg (dhX0 t va.1.2 x₀)).1))
        (CKAGameSt.init (none, (kg (dhX0 t va.1.2 x₀)).1) ((kg (dhX0 t va.1.2 x₀)).1, (kg x₀).2)
          ((kg (dhX0 t va.1.2 x₀)).1, (kg x₀).2))).map Prod.fst :=
  OracleAdv.run_nf_map_fst_eq_of_rel _ _ _ (KEMRel (kg va.1.2).1 t)
    (fun s σ h q e => kemRel_step kg en hFS hPCS t ideal va vb s σ h q e) _ _ _
    (kemRel_init kg t va.1.2 x₀)

omit [Fintype Rg] [Nonempty Rg] in
/-- The encapsulation key of the initial key pair of the eager game. -/
theorem kg_dhX0_fst (kg : Rg → PK × SK) (t : ℕ) (a x₀ : Rg) :
    (kg (dhX0 t a x₀)).1 = if t = 1 then (kg a).1 else (kg x₀).1 := by
  unfold dhX0; split <;> rfl

/-- A draw under three draws is drawn first. -/
theorem kem_bind_pull3 {X A B β : Type} (τ : PMF ℕ) (μx : PMF X) (μa : PMF A) (μg : PMF B)
    (G : ℕ → X → A → B → PMF β) :
    (τ.bind fun t => μx.bind fun x => μa.bind fun a => μg.bind fun g => G t x a g) =
      μg.bind fun g => τ.bind fun t => μx.bind fun x => μa.bind fun a => G t x a g := by
  refine (congrArg _ (funext fun t => congrArg _ (funext fun x =>
    PMF.bind_comm μa μg (G t x)))).trans ?_
  refine (congrArg _ (funext fun t => PMF.bind_comm μx μg _)).trans ?_
  exact PMF.bind_comm τ μg _

/-- Reordering of the draws of the real game. -/
theorem kem_bind_reorder {X A B C D β : Type} (τ : PMF ℕ) (μx : PMF X) (μa : PMF A)
    (μg : PMF B) (μe : PMF C) (μb : PMF D) (F : ℕ → X → A → B → C → D → PMF β) :
    (τ.bind fun t => μx.bind fun x => μa.bind fun a => μg.bind fun g => μe.bind fun e =>
      μb.bind fun b => F t x a g e b) =
      μg.bind fun g => μe.bind fun e => τ.bind fun t => μx.bind fun x => μa.bind fun a =>
        μb.bind fun b => F t x a g e b := by
  refine (kem_bind_pull3 τ μx μa μg
    (fun t x a g => μe.bind fun e => μb.bind fun b => F t x a g e b)).trans ?_
  refine congrArg _ (funext fun g => ?_)
  exact kem_bind_pull3 τ μx μa μe (fun t x a e => μb.bind fun b => F t x a g e b)

/-- Reordering of the draws of the ideal game. -/
theorem kem_bind_reorder_ideal {X A B C D U β : Type} (τ : PMF ℕ) (μx : PMF X) (μa : PMF A)
    (μg : PMF B) (μe : PMF C) (μb : PMF D) (μu : PMF U)
    (F : ℕ → X → A → B → C → D → U → PMF β) :
    (τ.bind fun t => μx.bind fun x => μa.bind fun a => μg.bind fun g => μe.bind fun e =>
      μb.bind fun b => μu.bind fun u => F t x a g e b u) =
      μg.bind fun g => μe.bind fun e => μu.bind fun u => τ.bind fun t => μx.bind fun x =>
        μa.bind fun a => μb.bind fun b => F t x a g e b u := by
  refine (kem_bind_pull3 τ μx μa μg (fun t x a g => μe.bind fun e => μb.bind fun b =>
    μu.bind fun u => F t x a g e b u)).trans ?_
  refine congrArg _ (funext fun g => ?_)
  refine (kem_bind_pull3 τ μx μa μe (fun t x a e => μb.bind fun b =>
    μu.bind fun u => F t x a g e b u)).trans ?_
  refine congrArg _ (funext fun e => ?_)
  refine (congrArg _ (funext fun t => congrArg _ (funext fun x => congrArg _ (funext fun a =>
    PMF.bind_comm μb μu (fun b u => F t x a g e b u))))).trans ?_
  exact kem_bind_pull3 τ μx μa μu (fun t x a u => μb.bind fun b => F t x a g e b u)

/-- The real game of `kemCKA` with the delays `1 ≤ ΔFS`, `2 ≤ ΔPCS`, as a distribution, is the
real KEM-CPA distribution followed by the reduction tree. -/
theorem kemCKAGamePMFOf_real (kg : Rg → PK × SK) (en : PK → Re → K × E) {ΔFS ΔPCS : ℕ}
    (hFS : 1 ≤ ΔFS) (hPCS : 2 ≤ ΔPCS) (tStar : PMF ℕ)
    (play : ℕ → Option E × PK →
      OracleAdv CKAQuery (CKAAns (PK × SK) (Option E × PK) K (Re × Rg)) α) :
    (tStar.bind fun t => kemCKAGamePMFOf kg en ΔFS ΔPCS t false (play t)) =
      ((PMF.uniformFintype Rg).bind fun rg => (PMF.uniformFintype Re).bind fun re =>
        PMF.pure ((kg rg).1, (en (kg rg).1 re).2, (en (kg rg).1 re).1)).bind fun y =>
          (OracleAdv.run emptyOracle (kemCorruptTreeOf kg en ΔFS ΔPCS tStar play y) ()).map
            Prod.fst := by
  simp only [kemCKAGamePMFOf_eager, kemCKA_eager_eq_sim kg en hFS hPCS]
  simp only [kemCorruptTreeOf_run, PMF.bind_bind, PMF.pure_bind, kg_dhX0_fst, kemDraw_bind,
    PMF.bind_const, Bool.false_eq_true, ite_false]
  exact kem_bind_reorder _ _ _ _ _ _ _

/-- The ideal game of `kemCKA` with the delays `1 ≤ ΔFS`, `2 ≤ ΔPCS`, as a distribution, is the
ideal KEM-CPA distribution followed by the reduction tree. -/
theorem kemCKAGamePMFOf_ideal (kg : Rg → PK × SK) (en : PK → Re → K × E) {ΔFS ΔPCS : ℕ}
    (hFS : 1 ≤ ΔFS) (hPCS : 2 ≤ ΔPCS) (tStar : PMF ℕ)
    (play : ℕ → Option E × PK →
      OracleAdv CKAQuery (CKAAns (PK × SK) (Option E × PK) K (Re × Rg)) α) :
    (tStar.bind fun t => kemCKAGamePMFOf kg en ΔFS ΔPCS t true (play t)) =
      ((PMF.uniformFintype Rg).bind fun rg => (PMF.uniformFintype Re).bind fun re =>
        (PMF.uniformFintype K).bind fun u => PMF.pure ((kg rg).1, (en (kg rg).1 re).2, u)).bind
          fun y =>
          (OracleAdv.run emptyOracle (kemCorruptTreeOf kg en ΔFS ΔPCS tStar play y) ()).map
            Prod.fst := by
  simp only [kemCKAGamePMFOf_eager, kemCKA_eager_eq_sim kg en hFS hPCS]
  simp only [kemCorruptTreeOf_run, PMF.bind_bind, PMF.pure_bind, kg_dhX0_fst, kemDraw_bind,
    PMF.bind_const, ite_true]
  exact kem_bind_reorder_ideal _ _ _ _ _ _ _ _

end Red

/-! ## The bound -/

section Bound

variable {PK SK K E Rg Re : Type} [Fintype Rg] [Nonempty Rg] [Fintype Re] [Nonempty Re]
  [Fintype K] [Nonempty K] [Inhabited K]

omit [Fintype K] [Nonempty K] [Inhabited K] in
/-- The real KEM-CPA game of a sound KEM as a lifted distribution. -/
theorem KEM_CPA_real_eq_liftPMF (KEM : KEMScheme PK SK K E) [KEMCoins KEM Rg Re]
    (hS : KEMCoins.Sound KEM) :
    KEM_CPA_real KEM = liftPMF ((PMF.uniformFintype Rg).bind fun rg =>
      (PMF.uniformFintype Re).bind fun re =>
        PMF.pure ((KEMCoins.kgenR (KEM := KEM) rg).1,
          (KEMCoins.encapR (KEM := KEM) (KEMCoins.kgenR (KEM := KEM) rg).1 re).2,
          (KEMCoins.encapR (KEM := KEM) (KEMCoins.kgenR (KEM := KEM) rg).1 re).1)) := by
  simp only [KEM_CPA_real, SPComp.monad_bind_eq, SPComp.monad_pure_eq, hS.1, hS.2,
    sample_eq_liftPMF, liftPMF_pure, liftPMF_bind_liftPMF,
    PMF.bind_bind, PMF.pure_bind]

omit [Inhabited K] in
/-- The ideal KEM-CPA game of a sound KEM as a lifted distribution. -/
theorem KEM_CPA_ideal_eq_liftPMF (KEM : KEMScheme PK SK K E) [KEMCoins KEM Rg Re]
    (hS : KEMCoins.Sound KEM) :
    KEM_CPA_ideal KEM = liftPMF ((PMF.uniformFintype Rg).bind fun rg =>
      (PMF.uniformFintype Re).bind fun re => (PMF.uniformFintype K).bind fun u =>
        PMF.pure ((KEMCoins.kgenR (KEM := KEM) rg).1,
          (KEMCoins.encapR (KEM := KEM) (KEMCoins.kgenR (KEM := KEM) rg).1 re).2, u)) := by
  simp only [KEM_CPA_ideal, SPComp.monad_bind_eq, SPComp.monad_pure_eq, hS.1, hS.2,
    sample_eq_liftPMF, liftPMF_pure, liftPMF_bind_liftPMF,
    PMF.bind_bind, PMF.pure_bind]

/-- **CKA security of `kemCKA` with state corruption and randomness leakage.** For a sound KEM
with explicit randomness, the delays `1 ≤ ΔFS`, `2 ≤ ΔPCS` and every adversary `A`, the
corruption advantage of `kemCKA KEM` equals the KEM-CPA advantage of the reduction
`kemCorruptRed KEM ΔFS ΔPCS A`. -/
theorem kemCKA_corrupt_advantage_eq_cpa (KEM : KEMScheme PK SK K E) [KEMCoins KEM Rg Re]
    (hS : KEMCoins.Sound KEM) {ΔFS ΔPCS : ℕ} (hFS : 1 ≤ ΔFS) (hPCS : 2 ≤ ΔPCS)
    (A : CKACorruptAdv (PK × SK) (Option E × PK) K (Re × Rg) Bool) :
    CKA_Corrupt_Advantage (kemCKA KEM) ΔFS ΔPCS A =
      KEM_CPA_Advantage KEM (kemCorruptRed KEM ΔFS ΔPCS A) := by
  unfold CKA_Corrupt_Advantage KEM_CPA_Advantage AdvantageA cka_corrupt_real cka_corrupt_ideal
    kemCorruptRed
  rw [kemCKA_game_eq KEM hS, kemCKA_game_eq KEM hS, kemCKAGamePMFOf_real _ _ hFS hPCS,
    kemCKAGamePMFOf_ideal _ _ hFS hPCS, KEM_CPA_real_eq_liftPMF KEM hS,
    KEM_CPA_ideal_eq_liftPMF KEM hS]
  simp only [liftPMF_bind_liftPMF]

/-- **CKA security of `kemCKA` with state corruption and randomness leakage**, as a bound: the
corruption advantage with `1 ≤ ΔFS`, `2 ≤ ΔPCS` is at most the KEM-CPA advantage of
`kemCorruptRed KEM ΔFS ΔPCS A`. -/
theorem kemCKA_corrupt_advantage_le (KEM : KEMScheme PK SK K E) [KEMCoins KEM Rg Re]
    (hS : KEMCoins.Sound KEM) {ΔFS ΔPCS : ℕ} (hFS : 1 ≤ ΔFS) (hPCS : 2 ≤ ΔPCS)
    (A : CKACorruptAdv (PK × SK) (Option E × PK) K (Re × Rg) Bool) :
    CKA_Corrupt_Advantage (kemCKA KEM) ΔFS ΔPCS A ≤
      KEM_CPA_Advantage KEM (kemCorruptRed KEM ΔFS ΔPCS A) :=
  le_of_eq (kemCKA_corrupt_advantage_eq_cpa KEM hS hFS hPCS A)

variable (G : Type) [CG : CyclicGroup G] [DecidableEq G] {RK Sa W Ct : Type} [DecidableEq K]
  [SampleableType W] [SampleableType Ct] [Fintype RK] [Nonempty RK] [DecidableEq RK] [Fintype Sa]
  [Nonempty Sa]

/-- **The triple ratchet with state corruption, from DDH, KEM-CPA, PRF-PRNG and FS-AEAD.** Let
`KEM` be a sound and correct KEM with explicit randomness. For every adversary `A` against the
double ratchet `acdSM (prodCKA (dhCKA G) (kemCKA KEM)) R Gc D` with the delays
`ΔFS = ΔPCS = 2`, the advantage is at most, for the two challenge modes `b`, the DDH advantage of
`ckaCorruptDDHRed (prodCorruptRed₁ (kemCKA KEM) (kemInitP KEM) 2 (smcCKARed R Gc D b A.toSM))`,
the KEM-CPA advantage of
`kemCorruptRed KEM 2 2 (prodCorruptRed₂ (dhCKA G) (dhInitP G) 2 (smcCKARed R Gc D b A.toSM))` and
the PRF-PRNG advantages of the root KDF `R`, plus the FS-AEAD advantage with corruption of `Gc`
and `D`. -/
theorem tripleRatchet_corruptAdvantage_le_kem (KEM : KEMScheme PK SK K E) [KEMCoins KEM Rg Re]
    (hS : KEMCoins.Sound KEM) (hC : KEMCoins.Correct KEM)
    (R : PRGDef (RK × (G × K)) (RK × Sa)) (Gc : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (A : SMSchemeAdv (G × (Option E × PK)) W Ct (SMPartySt ((G × CG.Exp) × (PK × SK)) RK Sa)) :
    (acdSM (prodCKA (dhCKA G) (kemCKA KEM)) R Gc D).corruptAdvantage 2 2 A ≤
      ∑ b : Bool, (DDH_Advantage G (ckaCorruptDDHRed
          (prodCorruptRed₁ (kemCKA KEM) (kemInitP KEM) 2 (smcCKARed R Gc D b A.toSM))) +
        KEM_CPA_Advantage KEM (kemCorruptRed KEM 2 2
          (prodCorruptRed₂ (dhCKA G) (dhInitP G) 2 (smcCKARed R Gc D b A.toSM)))) +
        ∑ b : Bool, PRFPRNG_Advantage R (smcRootRed (prodCKA (dhCKA G) (kemCKA KEM)) R Gc D 2 2 b
          (prodInitP (dhInitP G) (kemInitP KEM)) A.toSM) +
        FSAEAD_Corrupt_Advantage Gc D (smcFSRed (prodCKA (dhCKA G) (kemCKA KEM)) R Gc D 2 2
          (prodInitP (dhInitP G) (kemInitP KEM)) A.toSM) := by
  refine (tripleRatchet_corruptAdvantage_le G KEM (kemCKACoins_sound KEM hS)
    (kemCKA_ckaCorrect KEM hC) (kemInitP KEM) (kemCKA_init_eq KEM hS) (kemInitP_rel KEM) R Gc D
    A).trans ?_
  gcongr with b _
  exact kemCKA_corrupt_advantage_le KEM hS (by norm_num) le_rfl _

end Bound

end CatCrypt.Crypto.Messaging
