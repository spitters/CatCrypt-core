/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.SMScheme
public import CatCryptCore.Crypto.Messaging.KEMCKA
public import CatCryptCore.Crypto.Messaging.SignalStackSM
import CatCryptCore.Tactics.AutoDispatchExt

/-!
# The triple ratchet with state corruption

The triple ratchet of Dodis, Jost, Katsumata, Prest and Schmidt (EUROCRYPT 2025) is the double
ratchet of Alwen, Coretti and Dodis over the product `prodCKA C₁ C₂` of two CKA schemes: the
Diffie–Hellman CKA `dhCKA G` and the KEM CKA `kemCKA KEM`. This file states its confidentiality
with state corruption and randomness leakage as an instance of the corruption game over the ACD
construction `acdSM` (`CatCryptCore.Crypto.Messaging.SMScheme`).

## The product CKA with explicit randomness

The randomness of a send of the product is a pair: `prodCKACoins` sends in each component with
its own component of the randomness. The product is sound (`prodCKACoins_sound`), correct along
the product of the correctness relations (`prodCKA_correct`), and its initialisation is the lift
of the product `prodInitP` of the initial distributions (`prodCKA_init_eq`).

## The corruption game of the product

In the CKA game with corruption of `prodCKA C₁ C₂` (`cka_corrupt_game`) both components share
the epoch counters, so every gate of the game (sending, receiving, the challenge, the corruption
and the leakage gate) is the same gate on each component. The hybrid game `prodHybGame` runs the
product oracle `prodOracleP` with a separate challenge mode for each component of the key. The
reduction `prodCorruptRed₁` plays the game of `C₁`: it forwards each query to its oracle and runs
`C₂` itself with the real key; `prodCorruptRed₂` plays the game of `C₂` and runs `C₁` itself with
a uniform challenge key. The real game of the product is the real game of `C₁` against
`prodCorruptRed₁`; the ideal game of `C₁` against it is the real game of `C₂` against
`prodCorruptRed₂`; the ideal game of `C₂` against it is the ideal game of the product.

## Main definitions

* `prodCKACoins`, `prodInitP` — the explicit randomness and the initial distribution of the
  product
* `CKAGameSt.fstSt`, `CKAGameSt.sndSt` — the game states of the components
* `prodOracleP`, `prodHybGame` — the oracle and the hybrid games of the product
* `prodSimImpl₁`, `prodSimImpl₂`, `prodCorruptTree₁`, `prodCorruptTree₂` — the simulators and
  the oracle trees of the reductions
* `prodCorruptRed₁`, `prodCorruptRed₂` — the reductions of the product to its components
* `dhCKARel` — the correctness relation of `dhCKA`

## Main results

* `prodCKA_corrupt_advantage_le` — for every adversary `A`, the CKA corruption advantage of
  `prodCKA C₁ C₂` is at most that of `C₁` at `prodCorruptRed₁ C₂ initP₂ ΔPCS A` plus that of `C₂`
  at `prodCorruptRed₂ C₁ initP₁ ΔPCS A`, with the same delays
* `acdSM_prod_corruptAdvantage_le` — for every adversary `A` against `acdSM (prodCKA C₁ C₂) R Gc D`
  and `2 ≤ ΔFS`, `1 ≤ ΔPCS`, the advantage is at most the CKA corruption advantages of the two
  components at the product reductions of the reductions `smcCKARed R Gc D b A.toSM`, the
  PRF-PRNG advantages of `R` and the FS-AEAD advantage with corruption of `Gc` and `D`
* `tripleRatchet_corruptAdvantage_le` — the triple ratchet over `dhCKA G` and `kemCKA KEM` with the
  delays `ΔFS = ΔPCS = 2`: the Diffie–Hellman terms are DDH advantages of the reductions
  `ckaCorruptDDHRed (prodCorruptRed₁ …)`, the KEM terms CKA corruption advantages of
  `kemCKA KEM`
* `prodCKA_pureNF`, `kemCKA_pureNF` — the product and the KEM CKA neither touch the heap nor
  fail when their components do not
* `tripleRatchet_realizes_FSM` — the Signal stack over the triple ratchet realizes `F_SM` behind
  the simulator `scSim G` (`signal_stack_realizes_FSM_acd` at the product CKA)

## References

* Y. Dodis, D. Jost, S. Katsumata, T. Prest, R. Schmidt, *Triple Ratchet: A Bandwidth
  Efficient Hybrid-Secure Signal Protocol*, EUROCRYPT 2025
* J. Alwen, S. Coretti, Y. Dodis, *The Double Ratchet: Security Notions, Proofs, and
  Modularization for the Signal Protocol*, EUROCRYPT 2019
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Messaging

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Assumptions
  CatCrypt.Crypto.PRPPRF CatCryptCore.Examples.CyclicGroupDDH CatCrypt.Examples.KEMDEM
open scoped ENNReal

/-! ## The product CKA with explicit randomness -/

section ProdCoins

variable {S₁ M₁ K₁ R₁ S₂ M₂ K₂ R₂ : Type}

/-- The sending algorithm of the product with explicit randomness: each component sends with its
component of the randomness. -/
noncomputable instance prodCKACoins (C₁ : CKADef S₁ M₁ K₁) (C₂ : CKADef S₂ M₂ K₂)
    [CKACoins C₁ R₁] [CKACoins C₂ R₂] : CKACoins (prodCKA C₁ C₂) (R₁ × R₂) where
  sendR s r :=
    (((CKACoins.sendR (C := C₁) s.1 r.1).1, (CKACoins.sendR (C := C₂) s.2 r.2).1),
      ((CKACoins.sendR (C := C₁) s.1 r.1).2.1, (CKACoins.sendR (C := C₂) s.2 r.2).2.1),
      ((CKACoins.sendR (C := C₁) s.1 r.1).2.2, (CKACoins.sendR (C := C₂) s.2 r.2).2.2))

/-- The unfolding of the explicit-randomness sending algorithm of the product. -/
@[simp] theorem prodCKACoins_sendR (C₁ : CKADef S₁ M₁ K₁) (C₂ : CKADef S₂ M₂ K₂)
    [CKACoins C₁ R₁] [CKACoins C₂ R₂] (s : S₁ × S₂) (r : R₁ × R₂) :
    CKACoins.sendR (C := prodCKA C₁ C₂) s r =
      (((CKACoins.sendR (C := C₁) s.1 r.1).1, (CKACoins.sendR (C := C₂) s.2 r.2).1),
        ((CKACoins.sendR (C := C₁) s.1 r.1).2.1, (CKACoins.sendR (C := C₂) s.2 r.2).2.1),
        ((CKACoins.sendR (C := C₁) s.1 r.1).2.2, (CKACoins.sendR (C := C₂) s.2 r.2).2.2)) :=
  rfl

/-- The explicit-randomness sending algorithm of the product of sound CKA schemes is sound. -/
theorem prodCKACoins_sound (C₁ : CKADef S₁ M₁ K₁) (C₂ : CKADef S₂ M₂ K₂) [CKACoins C₁ R₁]
    [CKACoins C₂ R₂] [Fintype R₁] [Nonempty R₁] [Fintype R₂] [Nonempty R₂]
    (h₁ : CKACoins.Sound C₁) (h₂ : CKACoins.Sound C₂) : CKACoins.Sound (prodCKA C₁ C₂) := by
  intro s
  unfold prodCKA
  dsimp only
  rw [h₁, h₂]
  simp only [SPComp.sample_prod_eq, SPComp.bind_assoc, SPComp.pure_bind]
  rfl

/-- **Correctness of the product** along the product of the correctness relations. -/
theorem prodCKA_correct {C₁ : CKADef S₁ M₁ K₁} {C₂ : CKADef S₂ M₂ K₂} [CKACoins C₁ R₁]
    [CKACoins C₂ R₂] {J₁ : S₁ → S₁ → Prop} {J₂ : S₂ → S₂ → Prop} (h₁ : CKACorrect C₁ J₁)
    (h₂ : CKACorrect C₂ J₂) :
    CKACorrect (prodCKA C₁ C₂) (fun s r => J₁ s.1 r.1 ∧ J₂ s.2 r.2) where
  key s r x h := Prod.ext (h₁.key s.1 r.1 x.1 h.1) (h₂.key s.2 r.2 x.2 h.2)
  next s r x h := ⟨h₁.next s.1 r.1 x.1 h.1, h₂.next s.2 r.2 x.2 h.2⟩

/-- The initial distribution of the product: the initial distributions of the components,
independently. -/
noncomputable def prodInitP (initP₁ : PMF (M₁ × S₁ × S₁)) (initP₂ : PMF (M₂ × S₂ × S₂)) :
    PMF ((M₁ × M₂) × (S₁ × S₂) × (S₁ × S₂)) :=
  initP₁.bind fun i₁ => initP₂.bind fun i₂ =>
    PMF.pure ((i₁.1, i₂.1), (i₁.2.1, i₂.2.1), (i₁.2.2, i₂.2.2))

/-- The initialisation of the product is the lift of `prodInitP`. -/
theorem prodCKA_init_eq (C₁ : CKADef S₁ M₁ K₁) (C₂ : CKADef S₂ M₂ K₂)
    (initP₁ : PMF (M₁ × S₁ × S₁)) (initP₂ : PMF (M₂ × S₂ × S₂))
    (h₁ : C₁.init = liftPMF initP₁) (h₂ : C₂.init = liftPMF initP₂) :
    (prodCKA C₁ C₂).init = liftPMF (prodInitP initP₁ initP₂) := by
  unfold prodCKA prodInitP
  dsimp only
  rw [h₁, h₂]
  grind [liftPMF_pure, liftPMF_bind_liftPMF]

/-- The initial states of the product are related by the product of relations that relate the
initial states of the components. -/
theorem prodInitP_rel {initP₁ : PMF (M₁ × S₁ × S₁)} {initP₂ : PMF (M₂ × S₂ × S₂)}
    {J₁ : S₁ → S₁ → Prop} {J₂ : S₂ → S₂ → Prop} (h₁ : ∀ i ∈ initP₁.support, J₁ i.2.1 i.2.2)
    (h₂ : ∀ i ∈ initP₂.support, J₂ i.2.1 i.2.2) :
    ∀ i ∈ (prodInitP initP₁ initP₂).support, J₁ i.2.1.1 i.2.2.1 ∧ J₂ i.2.1.2 i.2.2.2 := by
  intro i hi
  rw [prodInitP, PMF.mem_support_bind_iff] at hi
  obtain ⟨i₁, hi₁, hi⟩ := hi
  rw [PMF.mem_support_bind_iff] at hi
  obtain ⟨i₂, hi₂, hi⟩ := hi
  rw [PMF.mem_support_pure_iff] at hi
  subst hi
  exact ⟨h₁ i₁ hi₁, h₂ i₂ hi₂⟩

end ProdCoins

/-! ## The game states of the components -/

namespace CKAGameSt

variable {S₁ M₁ S₂ M₂ : Type}

/-- The game state of the first component of a product game state. -/
def fstSt (s : CKAGameSt (S₁ × S₂) (M₁ × M₂)) : CKAGameSt S₁ M₁ :=
  ⟨fun p => (s.st p).1, s.t, s.msg.1⟩

/-- The game state of the second component of a product game state. -/
def sndSt (s : CKAGameSt (S₁ × S₂) (M₁ × M₂)) : CKAGameSt S₂ M₂ :=
  ⟨fun p => (s.st p).2, s.t, s.msg.2⟩

theorem fstSt_sent (s : CKAGameSt (S₁ × S₂) (M₁ × M₂)) (p : CKAParty) (x : S₁ × S₂)
    (T : M₁ × M₂) : fstSt (s.sent p x T) = (fstSt s).sent p x.1 T.1 := by
  simp only [fstSt, sent, mk.injEq, and_true]
  funext q
  by_cases h : q = p <;> simp [Function.update, h]

theorem sndSt_sent (s : CKAGameSt (S₁ × S₂) (M₁ × M₂)) (p : CKAParty) (x : S₁ × S₂)
    (T : M₁ × M₂) : sndSt (s.sent p x T) = (sndSt s).sent p x.2 T.2 := by
  simp only [sndSt, sent, mk.injEq, and_true]
  funext q
  by_cases h : q = p <;> simp [Function.update, h]

theorem fstSt_recvd (s : CKAGameSt (S₁ × S₂) (M₁ × M₂)) (p : CKAParty) (x : S₁ × S₂) :
    fstSt (s.recvd p x) = (fstSt s).recvd p x.1 := by
  simp only [fstSt, recvd, mk.injEq, and_true]
  funext q
  by_cases h : q = p <;> simp [Function.update, h]

theorem sndSt_recvd (s : CKAGameSt (S₁ × S₂) (M₁ × M₂)) (p : CKAParty) (x : S₁ × S₂) :
    sndSt (s.recvd p x) = (sndSt s).recvd p x.2 := by
  simp only [sndSt, recvd, mk.injEq, and_true]
  funext q
  by_cases h : q = p <;> simp [Function.update, h]

theorem fstSt_init (pub : M₁ × M₂) (sA sB : S₁ × S₂) :
    fstSt (init pub sA sB) = init pub.1 sA.1 sB.1 := by
  simp only [fstSt, init, mk.injEq, and_true]
  funext p
  cases p <;> rfl

theorem sndSt_init (pub : M₁ × M₂) (sA sB : S₁ × S₂) :
    sndSt (init pub sA sB) = init pub.2 sA.2 sB.2 := by
  simp only [sndSt, init, mk.injEq, and_true]
  funext p
  cases p <;> rfl

@[simp] theorem fstSt_t (s : CKAGameSt (S₁ × S₂) (M₁ × M₂)) : (fstSt s).t = s.t := rfl

@[simp] theorem sndSt_t (s : CKAGameSt (S₁ × S₂) (M₁ × M₂)) : (sndSt s).t = s.t := rfl

@[simp] theorem fstSt_st (s : CKAGameSt (S₁ × S₂) (M₁ × M₂)) (p : CKAParty) :
    (fstSt s).st p = (s.st p).1 := rfl

@[simp] theorem sndSt_st (s : CKAGameSt (S₁ × S₂) (M₁ × M₂)) (p : CKAParty) :
    (sndSt s).st p = (s.st p).2 := rfl

@[simp] theorem fstSt_msg (s : CKAGameSt (S₁ × S₂) (M₁ × M₂)) : (fstSt s).msg = s.msg.1 := rfl

@[simp] theorem sndSt_msg (s : CKAGameSt (S₁ × S₂) (M₁ × M₂)) : (sndSt s).msg = s.msg.2 := rfl

end CKAGameSt

/-! ## The corruption game of the product -/

section ProdGame

variable {S₁ M₁ K₁ R₁ S₂ M₂ K₂ R₂ : Type} [Fintype K₁] [Nonempty K₁] [Fintype K₂]
  [Nonempty K₂] [Fintype R₁] [Nonempty R₁] [Fintype R₂] [Nonempty R₂]

/-- The oracle of the CKA corruption game of the product with the challenge mode `i₁` for the
first and `i₂` for the second component of the challenge key. -/
noncomputable def prodOracleP (C₁ : CKADef S₁ M₁ K₁) (C₂ : CKADef S₂ M₂ K₂) [CKACoins C₁ R₁]
    [CKACoins C₂ R₂] (ΔFS ΔPCS t : ℕ) (i₁ i₂ : Bool) (s : CKAGameSt (S₁ × S₂) (M₁ × M₂)) :
    CKAQuery → PMF (CKAAns (S₁ × S₂) (M₁ × M₂) (K₁ × K₂) (R₁ × R₂) ×
      CKAGameSt (S₁ × S₂) (M₁ × M₂))
  | .send p =>
    if s.canSend p then
      (PMF.uniformFintype R₁).bind fun r₁ => (PMF.uniformFintype R₂).bind fun r₂ =>
        PMF.pure (.out (CKACoins.sendR (C := prodCKA C₁ C₂) (s.st p) (r₁, r₂)).2.1
          (CKACoins.sendR (C := prodCKA C₁ C₂) (s.st p) (r₁, r₂)).2.2,
          s.sent p (CKACoins.sendR (C := prodCKA C₁ C₂) (s.st p) (r₁, r₂)).1
            (CKACoins.sendR (C := prodCKA C₁ C₂) (s.st p) (r₁, r₂)).2.1)
    else PMF.pure (.none, s)
  | .recv p =>
    PMF.pure (if s.canRecv p then (.none, s.recvd p ((prodCKA C₁ C₂).recv (s.st p) s.msg).1)
      else (.none, s))
  | .chall p =>
    if s.canSend p && s.t p + 1 == t then
      (PMF.uniformFintype R₁).bind fun r₁ =>
        (if i₁ then PMF.uniformFintype K₁
          else PMF.pure (CKACoins.sendR (C := C₁) (s.st p).1 r₁).2.2).bind fun k₁ =>
        (PMF.uniformFintype R₂).bind fun r₂ =>
        (if i₂ then PMF.uniformFintype K₂
          else PMF.pure (CKACoins.sendR (C := C₂) (s.st p).2 r₂).2.2).bind fun k₂ =>
          PMF.pure (.out (CKACoins.sendR (C := prodCKA C₁ C₂) (s.st p) (r₁, r₂)).2.1 (k₁, k₂),
            s.sent p (CKACoins.sendR (C := prodCKA C₁ C₂) (s.st p) (r₁, r₂)).1
              (CKACoins.sendR (C := prodCKA C₁ C₂) (s.st p) (r₁, r₂)).2.1)
    else PMF.pure (.none, s)
  | .corrupt p =>
    PMF.pure (if ckaAllowCorr ΔFS ΔPCS t s p then .state (s.st p) else .none, s)
  | .sendLeak p =>
    if ckaAllowLeak ΔPCS t s p then
      (PMF.uniformFintype R₁).bind fun r₁ => (PMF.uniformFintype R₂).bind fun r₂ =>
        PMF.pure (.leak (CKACoins.sendR (C := prodCKA C₁ C₂) (s.st p) (r₁, r₂)).2.1
          (CKACoins.sendR (C := prodCKA C₁ C₂) (s.st p) (r₁, r₂)).2.2 (r₁, r₂),
          s.sent p (CKACoins.sendR (C := prodCKA C₁ C₂) (s.st p) (r₁, r₂)).1
            (CKACoins.sendR (C := prodCKA C₁ C₂) (s.st p) (r₁, r₂)).2.1)
    else PMF.pure (.none, s)

/-- The oracle of the CKA corruption game of the product with the challenge mode `b` is the
product oracle with the challenge mode `b` for both components. -/
theorem ckaOracleP_prod (C₁ : CKADef S₁ M₁ K₁) (C₂ : CKADef S₂ M₂ K₂) [CKACoins C₁ R₁]
    [CKACoins C₂ R₂] (ΔFS ΔPCS t : ℕ) (b : Bool) :
    ckaOracleP (prodCKA C₁ C₂) ΔFS ΔPCS t b = prodOracleP C₁ C₂ ΔFS ΔPCS t b b := by
  funext s q
  cases q with
  | send p =>
    simp only [ckaOracleP, prodOracleP, PMF.uniform_prod_eq_bind, PMF.bind_bind, PMF.bind_map,
      Function.comp_def]
  | recv p => rfl
  | chall p =>
    simp only [ckaOracleP, prodOracleP]
    split
    · cases b
      · simp only [PMF.uniform_prod_eq_bind, PMF.bind_bind, PMF.bind_map, Function.comp_def,
          Bool.false_eq_true, ite_false, PMF.pure_bind]
        rfl
      · simp only [PMF.uniform_prod_eq_bind, PMF.bind_bind, PMF.bind_map, Function.comp_def,
          ite_true]
        refine congrArg _ (funext fun r₁ => ?_)
        exact PMF.bind_comm _ _ _
    · rfl
  | corrupt p => rfl
  | sendLeak p =>
    simp only [ckaOracleP, prodOracleP, PMF.uniform_prod_eq_bind, PMF.bind_bind, PMF.bind_map,
      Function.comp_def]

/-- The hybrid game of the product with the challenge modes `i₁` and `i₂` of the components. -/
noncomputable def prodHybGame (C₁ : CKADef S₁ M₁ K₁) (C₂ : CKADef S₂ M₂ K₂) [CKACoins C₁ R₁]
    [CKACoins C₂ R₂] (ΔFS ΔPCS : ℕ) (initP₁ : PMF (M₁ × S₁ × S₁)) (initP₂ : PMF (M₂ × S₂ × S₂))
    (i₁ i₂ : Bool) (A : CKACorruptAdv (S₁ × S₂) (M₁ × M₂) (K₁ × K₂) (R₁ × R₂) Bool) :
    SPComp Bool :=
  liftPMF (A.tStar.bind fun t => (prodInitP initP₁ initP₂).bind fun i =>
    (OracleAdv.run (prodOracleP C₁ C₂ ΔFS ΔPCS t i₁ i₂) (A.play t i.1)
      (CKAGameSt.init i.1 i.2.1 i.2.2)).map Prod.fst)

/-- The CKA corruption game of the product with the challenge mode `b` is the hybrid game with
the challenge mode `b` for both components. -/
theorem prodCKA_corrupt_game_eq (C₁ : CKADef S₁ M₁ K₁) (C₂ : CKADef S₂ M₂ K₂) [CKACoins C₁ R₁]
    [CKACoins C₂ R₂] (hS₁ : CKACoins.Sound C₁) (hS₂ : CKACoins.Sound C₂)
    (initP₁ : PMF (M₁ × S₁ × S₁)) (initP₂ : PMF (M₂ × S₂ × S₂))
    (h₁ : C₁.init = liftPMF initP₁) (h₂ : C₂.init = liftPMF initP₂) (ΔFS ΔPCS : ℕ) (b : Bool)
    (A : CKACorruptAdv (S₁ × S₂) (M₁ × M₂) (K₁ × K₂) (R₁ × R₂) Bool) :
    cka_corrupt_game (prodCKA C₁ C₂) ΔFS ΔPCS b A =
      prodHybGame C₁ C₂ ΔFS ΔPCS initP₁ initP₂ b b A := by
  rw [cka_corrupt_game_eq_liftPMF _ (prodCKACoins_sound C₁ C₂ hS₁ hS₂) _
    (prodCKA_init_eq C₁ C₂ initP₁ initP₂ h₁ h₂)]
  simp only [ckaOracleP_prod, prodHybGame]

/-! ### The reduction to the first component -/

/-- The simulator of the reduction to the first component with the challenge epoch `t`: the
queries go to the oracle of the first component, and the reduction runs the second component
`C₂` with the real key on its own game state. -/
noncomputable def prodSimImpl₁ (C₂ : CKADef S₂ M₂ K₂) [CKACoins C₂ R₂] (ΔPCS t : ℕ)
    (σ : CKAGameSt S₂ M₂) (q : CKAQuery) :
    OracleAdv CKAQuery (CKAAns S₁ M₁ K₁ R₁)
      (CKAAns (S₁ × S₂) (M₁ × M₂) (K₁ × K₂) (R₁ × R₂) × CKAGameSt S₂ M₂) :=
  match q with
  | .send p =>
    if σ.canSend p then
      .query (.send p) fun a =>
        match a with
        | .out T₁ k₁ => .rand (PMF.uniformFintype R₂) fun r₂ =>
          .ret (.out (T₁, (CKACoins.sendR (C := C₂) (σ.st p) r₂).2.1)
            (k₁, (CKACoins.sendR (C := C₂) (σ.st p) r₂).2.2),
            σ.sent p (CKACoins.sendR (C := C₂) (σ.st p) r₂).1
              (CKACoins.sendR (C := C₂) (σ.st p) r₂).2.1)
        | _ => .ret (.none, σ)
    else .ret (.none, σ)
  | .recv p =>
    if σ.canRecv p then
      .query (.recv p) fun _ => .ret (.none, σ.recvd p (C₂.recv (σ.st p) σ.msg).1)
    else .ret (.none, σ)
  | .chall p =>
    if σ.canSend p && σ.t p + 1 == t then
      .query (.chall p) fun a =>
        match a with
        | .out T₁ k₁ => .rand (PMF.uniformFintype R₂) fun r₂ =>
          .ret (.out (T₁, (CKACoins.sendR (C := C₂) (σ.st p) r₂).2.1)
            (k₁, (CKACoins.sendR (C := C₂) (σ.st p) r₂).2.2),
            σ.sent p (CKACoins.sendR (C := C₂) (σ.st p) r₂).1
              (CKACoins.sendR (C := C₂) (σ.st p) r₂).2.1)
        | _ => .ret (.none, σ)
    else .ret (.none, σ)
  | .corrupt p =>
    .query (.corrupt p) fun a =>
      match a with
      | .state x₁ => .ret (.state (x₁, σ.st p), σ)
      | _ => .ret (.none, σ)
  | .sendLeak p =>
    if ckaAllowLeak ΔPCS t σ p then
      .query (.sendLeak p) fun a =>
        match a with
        | .leak T₁ k₁ r₁ => .rand (PMF.uniformFintype R₂) fun r₂ =>
          .ret (.leak (T₁, (CKACoins.sendR (C := C₂) (σ.st p) r₂).2.1)
            (k₁, (CKACoins.sendR (C := C₂) (σ.st p) r₂).2.2) (r₁, r₂),
            σ.sent p (CKACoins.sendR (C := C₂) (σ.st p) r₂).1
              (CKACoins.sendR (C := C₂) (σ.st p) r₂).2.1)
        | _ => .ret (.none, σ)
    else .ret (.none, σ)

/-- The oracle tree of the reduction to the first component: on the challenge epoch `t` and the
public value `pub₁` of the first component, it draws the initialisation of `C₂` and runs the
adversary against the simulator `prodSimImpl₁`. -/
noncomputable def prodCorruptTree₁ (C₂ : CKADef S₂ M₂ K₂) [CKACoins C₂ R₂]
    (initP₂ : PMF (M₂ × S₂ × S₂)) (ΔPCS : ℕ)
    (play : ℕ → M₁ × M₂ →
      OracleAdv CKAQuery (CKAAns (S₁ × S₂) (M₁ × M₂) (K₁ × K₂) (R₁ × R₂)) Bool)
    (t : ℕ) (pub₁ : M₁) : OracleAdv CKAQuery (CKAAns S₁ M₁ K₁ R₁) Bool :=
  .rand initP₂ fun i₂ =>
    (OracleAdv.simulate (prodSimImpl₁ C₂ ΔPCS t) (play t (pub₁, i₂.1))
      (CKAGameSt.init i₂.1 i₂.2.1 i₂.2.2)).bind fun r => .ret r.1

/-- **The reduction to the first component**: the CKA corruption adversary against `C₁` that
keeps the challenge epoch of `A` and plays `prodCorruptTree₁`. -/
noncomputable def prodCorruptRed₁ (C₂ : CKADef S₂ M₂ K₂) [CKACoins C₂ R₂]
    (initP₂ : PMF (M₂ × S₂ × S₂)) (ΔPCS : ℕ)
    (A : CKACorruptAdv (S₁ × S₂) (M₁ × M₂) (K₁ × K₂) (R₁ × R₂) Bool) :
    CKACorruptAdv S₁ M₁ K₁ R₁ Bool where
  tStar := A.tStar
  play := prodCorruptTree₁ C₂ initP₂ ΔPCS A.play

/-- The state of the reduction to the first component and of the game of `C₁` that a product
game state corresponds to. -/
def prodEmb₁ (s : CKAGameSt (S₁ × S₂) (M₁ × M₂)) : CKAGameSt S₂ M₂ × CKAGameSt S₁ M₁ :=
  (s.sndSt, s.fstSt)

/-- **The simulator of the first reduction is the hybrid oracle.** Each call of the product
oracle with the challenge modes `idealK` and real, mapped to the states of the reduction and of
the game of `C₁`, is the call of `prodSimImpl₁` against the oracle of `C₁` with the challenge mode
`idealK`. -/
theorem prodSim₁_step (C₁ : CKADef S₁ M₁ K₁) (C₂ : CKADef S₂ M₂ K₂) [CKACoins C₁ R₁]
    [CKACoins C₂ R₂] (ΔFS ΔPCS t : ℕ) (idealK : Bool) (s : CKAGameSt (S₁ × S₂) (M₁ × M₂))
    (q : CKAQuery) :
    (prodOracleP C₁ C₂ ΔFS ΔPCS t idealK false s q).map (Prod.map id prodEmb₁) =
      OracleAdv.simOracle (prodSimImpl₁ C₂ ΔPCS t) (ckaOracleP C₁ ΔFS ΔPCS t idealK)
        (prodEmb₁ s) q := by
  have e₁ : ∀ p, (CKAGameSt.fstSt s).canSend p = s.canSend p :=
    CKAGameSt.canSend_eq_of_t rfl
  have e₂ : ∀ p, (CKAGameSt.sndSt s).canSend p = s.canSend p :=
    CKAGameSt.canSend_eq_of_t rfl
  have r₁ : ∀ p, (CKAGameSt.fstSt s).canRecv p = s.canRecv p :=
    CKAGameSt.canRecv_eq_of_t rfl
  have r₂ : ∀ p, (CKAGameSt.sndSt s).canRecv p = s.canRecv p :=
    CKAGameSt.canRecv_eq_of_t rfl
  have l₁ : ∀ p, ckaAllowLeak ΔPCS t (CKAGameSt.fstSt s) p = ckaAllowLeak ΔPCS t s p :=
    CKAGameSt.allowLeak_eq_of_t rfl ΔPCS t
  have l₂ : ∀ p, ckaAllowLeak ΔPCS t (CKAGameSt.sndSt s) p = ckaAllowLeak ΔPCS t s p :=
    CKAGameSt.allowLeak_eq_of_t rfl ΔPCS t
  have c₁ : ∀ p, ckaAllowCorr ΔFS ΔPCS t (CKAGameSt.fstSt s) p = ckaAllowCorr ΔFS ΔPCS t s p :=
    CKAGameSt.allowCorr_eq_of_t rfl ΔFS ΔPCS t
  cases q with
  | send p =>
    by_cases h : s.canSend p = true <;>
      simp [prodOracleP, OracleAdv.simOracle, prodEmb₁, prodSimImpl₁, ckaOracleP, h, e₁, e₂,
        PMF.map_bind, PMF.pure_map, CKAGameSt.fstSt_sent, CKAGameSt.sndSt_sent]
  | recv p =>
    by_cases h : s.canRecv p = true <;>
      simp [prodOracleP, OracleAdv.simOracle, prodEmb₁, prodSimImpl₁, ckaOracleP, h, r₁, r₂,
        PMF.pure_map, CKAGameSt.fstSt_recvd, CKAGameSt.sndSt_recvd, prodCKA]
  | chall p =>
    by_cases h : (s.canSend p && s.t p + 1 == t) = true <;> cases idealK <;>
      simp [prodOracleP, OracleAdv.simOracle, prodEmb₁, prodSimImpl₁, ckaOracleP, h, e₁, e₂,
        PMF.map_bind, PMF.pure_map, CKAGameSt.fstSt_sent, CKAGameSt.sndSt_sent]
  | corrupt p =>
    by_cases h : ckaAllowCorr ΔFS ΔPCS t s p = true <;>
      simp [prodOracleP, OracleAdv.simOracle, prodEmb₁, prodSimImpl₁, ckaOracleP, h, c₁,
        PMF.pure_map]
  | sendLeak p =>
    by_cases h : ckaAllowLeak ΔPCS t s p = true <;>
      simp [prodOracleP, OracleAdv.simOracle, prodEmb₁, prodSimImpl₁, ckaOracleP, h, l₁, l₂,
        PMF.map_bind, PMF.pure_map, CKAGameSt.fstSt_sent, CKAGameSt.sndSt_sent]

/-- **The first hop.** The CKA corruption game of `C₁` with the challenge mode `idealK` against
`prodCorruptRed₁` is the hybrid game with the challenge mode `idealK` for the first and the real
key for the second component. -/
theorem prodCorruptRed₁_game_eq (C₁ : CKADef S₁ M₁ K₁) (C₂ : CKADef S₂ M₂ K₂) [CKACoins C₁ R₁]
    [CKACoins C₂ R₂] (hS₁ : CKACoins.Sound C₁) (initP₁ : PMF (M₁ × S₁ × S₁))
    (initP₂ : PMF (M₂ × S₂ × S₂)) (h₁ : C₁.init = liftPMF initP₁) (ΔFS ΔPCS : ℕ)
    (idealK : Bool) (A : CKACorruptAdv (S₁ × S₂) (M₁ × M₂) (K₁ × K₂) (R₁ × R₂) Bool) :
    cka_corrupt_game C₁ ΔFS ΔPCS idealK (prodCorruptRed₁ C₂ initP₂ ΔPCS A) =
      prodHybGame C₁ C₂ ΔFS ΔPCS initP₁ initP₂ idealK false A := by
  rw [cka_corrupt_game_eq_liftPMF C₁ hS₁ initP₁ h₁]
  unfold prodHybGame
  congr 1
  refine congrArg _ (funext fun t => ?_)
  simp only [prodInitP, PMF.bind_bind, PMF.pure_bind]
  refine congrArg _ (funext fun i₁ => ?_)
  simp only [prodCorruptRed₁, prodCorruptTree₁, OracleAdv.run_rand, PMF.map_bind]
  refine congrArg _ (funext fun i₂ => ?_)
  rw [OracleAdv.run_simulate_fst]
  have he : prodEmb₁ (CKAGameSt.init (i₁.1, i₂.1) (i₁.2.1, i₂.2.1) (i₁.2.2, i₂.2.2)) =
      (CKAGameSt.init i₂.1 i₂.2.1 i₂.2.2, CKAGameSt.init i₁.1 i₁.2.1 i₁.2.2) := by
    simp only [prodEmb₁, CKAGameSt.fstSt_init, CKAGameSt.sndSt_init]
  rw [← he, ← OracleAdv.run_map_state _ _ prodEmb₁ (prodSim₁_step C₁ C₂ ΔFS ΔPCS t idealK),
    PMF.map_comp]
  rfl

/-! ### The reduction to the second component -/

/-- The simulator of the reduction to the second component with the challenge epoch `t`: the
queries go to the oracle of the second component, and the reduction runs the first component
`C₁` with a uniform challenge key on its own game state. -/
noncomputable def prodSimImpl₂ (C₁ : CKADef S₁ M₁ K₁) [CKACoins C₁ R₁] (ΔPCS t : ℕ)
    (σ : CKAGameSt S₁ M₁) (q : CKAQuery) :
    OracleAdv CKAQuery (CKAAns S₂ M₂ K₂ R₂)
      (CKAAns (S₁ × S₂) (M₁ × M₂) (K₁ × K₂) (R₁ × R₂) × CKAGameSt S₁ M₁) :=
  match q with
  | .send p =>
    if σ.canSend p then
      .rand (PMF.uniformFintype R₁) fun r₁ =>
        .query (.send p) fun a =>
          match a with
          | .out T₂ k₂ =>
            .ret (.out ((CKACoins.sendR (C := C₁) (σ.st p) r₁).2.1, T₂)
              ((CKACoins.sendR (C := C₁) (σ.st p) r₁).2.2, k₂),
              σ.sent p (CKACoins.sendR (C := C₁) (σ.st p) r₁).1
                (CKACoins.sendR (C := C₁) (σ.st p) r₁).2.1)
          | _ => .ret (.none, σ)
    else .ret (.none, σ)
  | .recv p =>
    if σ.canRecv p then
      .query (.recv p) fun _ => .ret (.none, σ.recvd p (C₁.recv (σ.st p) σ.msg).1)
    else .ret (.none, σ)
  | .chall p =>
    if σ.canSend p && σ.t p + 1 == t then
      .rand (PMF.uniformFintype R₁) fun r₁ => .rand (PMF.uniformFintype K₁) fun k₁ =>
        .query (.chall p) fun a =>
          match a with
          | .out T₂ k₂ =>
            .ret (.out ((CKACoins.sendR (C := C₁) (σ.st p) r₁).2.1, T₂) (k₁, k₂),
              σ.sent p (CKACoins.sendR (C := C₁) (σ.st p) r₁).1
                (CKACoins.sendR (C := C₁) (σ.st p) r₁).2.1)
          | _ => .ret (.none, σ)
    else .ret (.none, σ)
  | .corrupt p =>
    .query (.corrupt p) fun a =>
      match a with
      | .state x₂ => .ret (.state (σ.st p, x₂), σ)
      | _ => .ret (.none, σ)
  | .sendLeak p =>
    if ckaAllowLeak ΔPCS t σ p then
      .rand (PMF.uniformFintype R₁) fun r₁ =>
        .query (.sendLeak p) fun a =>
          match a with
          | .leak T₂ k₂ r₂ =>
            .ret (.leak ((CKACoins.sendR (C := C₁) (σ.st p) r₁).2.1, T₂)
              ((CKACoins.sendR (C := C₁) (σ.st p) r₁).2.2, k₂) (r₁, r₂),
              σ.sent p (CKACoins.sendR (C := C₁) (σ.st p) r₁).1
                (CKACoins.sendR (C := C₁) (σ.st p) r₁).2.1)
          | _ => .ret (.none, σ)
    else .ret (.none, σ)

/-- The oracle tree of the reduction to the second component: on the challenge epoch `t` and the
public value `pub₂` of the second component, it draws the initialisation of `C₁` and runs the
adversary against the simulator `prodSimImpl₂`. -/
noncomputable def prodCorruptTree₂ (C₁ : CKADef S₁ M₁ K₁) [CKACoins C₁ R₁]
    (initP₁ : PMF (M₁ × S₁ × S₁)) (ΔPCS : ℕ)
    (play : ℕ → M₁ × M₂ →
      OracleAdv CKAQuery (CKAAns (S₁ × S₂) (M₁ × M₂) (K₁ × K₂) (R₁ × R₂)) Bool)
    (t : ℕ) (pub₂ : M₂) : OracleAdv CKAQuery (CKAAns S₂ M₂ K₂ R₂) Bool :=
  .rand initP₁ fun i₁ =>
    (OracleAdv.simulate (prodSimImpl₂ C₁ ΔPCS t) (play t (i₁.1, pub₂))
      (CKAGameSt.init i₁.1 i₁.2.1 i₁.2.2)).bind fun r => .ret r.1

/-- **The reduction to the second component**: the CKA corruption adversary against `C₂` that
keeps the challenge epoch of `A` and plays `prodCorruptTree₂`. -/
noncomputable def prodCorruptRed₂ (C₁ : CKADef S₁ M₁ K₁) [CKACoins C₁ R₁]
    (initP₁ : PMF (M₁ × S₁ × S₁)) (ΔPCS : ℕ)
    (A : CKACorruptAdv (S₁ × S₂) (M₁ × M₂) (K₁ × K₂) (R₁ × R₂) Bool) :
    CKACorruptAdv S₂ M₂ K₂ R₂ Bool where
  tStar := A.tStar
  play := prodCorruptTree₂ C₁ initP₁ ΔPCS A.play

/-- The state of the reduction to the second component and of the game of `C₂` that a product
game state corresponds to. -/
def prodEmb₂ (s : CKAGameSt (S₁ × S₂) (M₁ × M₂)) : CKAGameSt S₁ M₁ × CKAGameSt S₂ M₂ :=
  (s.fstSt, s.sndSt)

/-- **The simulator of the second reduction is the hybrid oracle.** Each call of the product
oracle with the uniform key for the first and the challenge mode `idealK` for the second
component, mapped to the states of the reduction and of the game of `C₂`, is the call of
`prodSimImpl₂` against the oracle of `C₂` with the challenge mode `idealK`. -/
theorem prodSim₂_step (C₁ : CKADef S₁ M₁ K₁) (C₂ : CKADef S₂ M₂ K₂) [CKACoins C₁ R₁]
    [CKACoins C₂ R₂] (ΔFS ΔPCS t : ℕ) (idealK : Bool) (s : CKAGameSt (S₁ × S₂) (M₁ × M₂))
    (q : CKAQuery) :
    (prodOracleP C₁ C₂ ΔFS ΔPCS t true idealK s q).map (Prod.map id prodEmb₂) =
      OracleAdv.simOracle (prodSimImpl₂ C₁ ΔPCS t) (ckaOracleP C₂ ΔFS ΔPCS t idealK)
        (prodEmb₂ s) q := by
  have e₁ : ∀ p, (CKAGameSt.fstSt s).canSend p = s.canSend p :=
    CKAGameSt.canSend_eq_of_t rfl
  have e₂ : ∀ p, (CKAGameSt.sndSt s).canSend p = s.canSend p :=
    CKAGameSt.canSend_eq_of_t rfl
  have r₁ : ∀ p, (CKAGameSt.fstSt s).canRecv p = s.canRecv p :=
    CKAGameSt.canRecv_eq_of_t rfl
  have r₂ : ∀ p, (CKAGameSt.sndSt s).canRecv p = s.canRecv p :=
    CKAGameSt.canRecv_eq_of_t rfl
  have l₁ : ∀ p, ckaAllowLeak ΔPCS t (CKAGameSt.fstSt s) p = ckaAllowLeak ΔPCS t s p :=
    CKAGameSt.allowLeak_eq_of_t rfl ΔPCS t
  have l₂ : ∀ p, ckaAllowLeak ΔPCS t (CKAGameSt.sndSt s) p = ckaAllowLeak ΔPCS t s p :=
    CKAGameSt.allowLeak_eq_of_t rfl ΔPCS t
  have c₂ : ∀ p, ckaAllowCorr ΔFS ΔPCS t (CKAGameSt.sndSt s) p = ckaAllowCorr ΔFS ΔPCS t s p :=
    CKAGameSt.allowCorr_eq_of_t rfl ΔFS ΔPCS t
  cases q with
  | send p =>
    by_cases h : s.canSend p = true <;>
      simp [prodOracleP, OracleAdv.simOracle, prodEmb₂, prodSimImpl₂, ckaOracleP, h, e₁, e₂,
        PMF.map_bind, PMF.pure_map, CKAGameSt.fstSt_sent, CKAGameSt.sndSt_sent]
  | recv p =>
    by_cases h : s.canRecv p = true <;>
      simp [prodOracleP, OracleAdv.simOracle, prodEmb₂, prodSimImpl₂, ckaOracleP, h, r₁, r₂,
        PMF.pure_map, CKAGameSt.fstSt_recvd, CKAGameSt.sndSt_recvd, prodCKA]
  | chall p =>
    by_cases h : (s.canSend p && s.t p + 1 == t) = true <;> cases idealK <;>
      simp [prodOracleP, OracleAdv.simOracle, prodEmb₂, prodSimImpl₂, ckaOracleP, h, e₁, e₂,
        PMF.map_bind, PMF.pure_map, CKAGameSt.fstSt_sent, CKAGameSt.sndSt_sent]
  | corrupt p =>
    by_cases h : ckaAllowCorr ΔFS ΔPCS t s p = true <;>
      simp [prodOracleP, OracleAdv.simOracle, prodEmb₂, prodSimImpl₂, ckaOracleP, h, c₂,
        PMF.pure_map]
  | sendLeak p =>
    by_cases h : ckaAllowLeak ΔPCS t s p = true <;>
      simp [prodOracleP, OracleAdv.simOracle, prodEmb₂, prodSimImpl₂, ckaOracleP, h, l₁, l₂,
        PMF.map_bind, PMF.pure_map, CKAGameSt.fstSt_sent, CKAGameSt.sndSt_sent]

/-- **The second hop.** The CKA corruption game of `C₂` with the challenge mode `idealK` against
`prodCorruptRed₂` is the hybrid game with the uniform key for the first and the challenge mode
`idealK` for the second component. -/
theorem prodCorruptRed₂_game_eq (C₁ : CKADef S₁ M₁ K₁) (C₂ : CKADef S₂ M₂ K₂) [CKACoins C₁ R₁]
    [CKACoins C₂ R₂] (hS₂ : CKACoins.Sound C₂) (initP₁ : PMF (M₁ × S₁ × S₁))
    (initP₂ : PMF (M₂ × S₂ × S₂)) (h₂ : C₂.init = liftPMF initP₂) (ΔFS ΔPCS : ℕ)
    (idealK : Bool) (A : CKACorruptAdv (S₁ × S₂) (M₁ × M₂) (K₁ × K₂) (R₁ × R₂) Bool) :
    cka_corrupt_game C₂ ΔFS ΔPCS idealK (prodCorruptRed₂ C₁ initP₁ ΔPCS A) =
      prodHybGame C₁ C₂ ΔFS ΔPCS initP₁ initP₂ true idealK A := by
  rw [cka_corrupt_game_eq_liftPMF C₂ hS₂ initP₂ h₂]
  unfold prodHybGame
  congr 1
  refine congrArg _ (funext fun t => ?_)
  simp only [prodInitP, PMF.bind_bind, PMF.pure_bind]
  rw [PMF.bind_comm initP₁ initP₂]
  refine congrArg _ (funext fun i₂ => ?_)
  simp only [prodCorruptRed₂, prodCorruptTree₂, OracleAdv.run_rand, PMF.map_bind]
  refine congrArg _ (funext fun i₁ => ?_)
  rw [OracleAdv.run_simulate_fst]
  have he : prodEmb₂ (CKAGameSt.init (i₁.1, i₂.1) (i₁.2.1, i₂.2.1) (i₁.2.2, i₂.2.2)) =
      (CKAGameSt.init i₁.1 i₁.2.1 i₁.2.2, CKAGameSt.init i₂.1 i₂.2.1 i₂.2.2) := by
    simp only [prodEmb₂, CKAGameSt.fstSt_init, CKAGameSt.sndSt_init]
  rw [← he, ← OracleAdv.run_map_state _ _ prodEmb₂ (prodSim₂_step C₁ C₂ ΔFS ΔPCS t idealK),
    PMF.map_comp]
  rfl

/-! ### The bound -/

/-- **CKA security with state corruption of the product.** For CKA schemes `C₁` and `C₂` with
sound explicit-randomness sending algorithms and initialisations that are the lifts of `initP₁`
and `initP₂`, for every adversary `A` and all delays `ΔFS`, `ΔPCS`, the CKA corruption advantage
of `prodCKA C₁ C₂` is at most the CKA corruption advantage of `C₁` at `prodCorruptRed₁ C₂ initP₂
ΔPCS A` plus that of `C₂` at `prodCorruptRed₂ C₁ initP₁ ΔPCS A`. -/
theorem prodCKA_corrupt_advantage_le (C₁ : CKADef S₁ M₁ K₁) (C₂ : CKADef S₂ M₂ K₂)
    [CKACoins C₁ R₁] [CKACoins C₂ R₂] (hS₁ : CKACoins.Sound C₁) (hS₂ : CKACoins.Sound C₂)
    (initP₁ : PMF (M₁ × S₁ × S₁)) (initP₂ : PMF (M₂ × S₂ × S₂))
    (h₁ : C₁.init = liftPMF initP₁) (h₂ : C₂.init = liftPMF initP₂) (ΔFS ΔPCS : ℕ)
    (A : CKACorruptAdv (S₁ × S₂) (M₁ × M₂) (K₁ × K₂) (R₁ × R₂) Bool) :
    CKA_Corrupt_Advantage (prodCKA C₁ C₂) ΔFS ΔPCS A ≤
      CKA_Corrupt_Advantage C₁ ΔFS ΔPCS (prodCorruptRed₁ C₂ initP₂ ΔPCS A) +
        CKA_Corrupt_Advantage C₂ ΔFS ΔPCS (prodCorruptRed₂ C₁ initP₁ ΔPCS A) := by
  unfold CKA_Corrupt_Advantage cka_corrupt_real cka_corrupt_ideal
  rw [prodCKA_corrupt_game_eq C₁ C₂ hS₁ hS₂ initP₁ initP₂ h₁ h₂,
    prodCKA_corrupt_game_eq C₁ C₂ hS₁ hS₂ initP₁ initP₂ h₁ h₂,
    prodCorruptRed₁_game_eq C₁ C₂ hS₁ initP₁ initP₂ h₁, prodCorruptRed₁_game_eq C₁ C₂ hS₁ initP₁
      initP₂ h₁, prodCorruptRed₂_game_eq C₁ C₂ hS₂ initP₁ initP₂ h₂,
    prodCorruptRed₂_game_eq C₁ C₂ hS₂ initP₁ initP₂ h₂]
  exact advantage_triangle _ _ _

end ProdGame

/-! ## The double ratchet over the product CKA -/

section ACDProd

variable {S₁ M₁ K₁ R₁ S₂ M₂ K₂ R₂ RK Sa W Ct : Type} [Fintype K₁] [Nonempty K₁] [Fintype K₂]
  [Nonempty K₂] [Fintype R₁] [Nonempty R₁] [Fintype R₂] [Nonempty R₂] [DecidableEq K₁]
  [DecidableEq K₂] [SampleableType W] [SampleableType Ct] [Fintype RK] [Nonempty RK]
  [DecidableEq RK] [Fintype Sa] [Nonempty Sa]

/-- **Secure messaging with corruption over the product CKA.** For CKA schemes `C₁` and `C₂` with
sound explicit-randomness sending algorithms, correct along `J₁` and `J₂`, with initialisations
that are the lifts of `initP₁` and `initP₂` and related initial states, and `2 ≤ ΔFS`,
`1 ≤ ΔPCS`, for every adversary `A` against `acdSM (prodCKA C₁ C₂) R Gc D` the advantage is at
most, for the two challenge modes `b`, the CKA corruption advantages of `C₁` at
`prodCorruptRed₁` and of `C₂` at `prodCorruptRed₂` of the CKA reduction `smcCKARed R Gc D b A.toSM`
and the PRF-PRNG advantages of `R`, plus the FS-AEAD advantage with corruption of `Gc` and
`D`. -/
theorem acdSM_prod_corruptAdvantage_le (C₁ : CKADef S₁ M₁ K₁) (C₂ : CKADef S₂ M₂ K₂)
    [CKACoins C₁ R₁] [CKACoins C₂ R₂] (hS₁ : CKACoins.Sound C₁) (hS₂ : CKACoins.Sound C₂)
    {J₁ : S₁ → S₁ → Prop} {J₂ : S₂ → S₂ → Prop} (hJ₁ : CKACorrect C₁ J₁)
    (hJ₂ : CKACorrect C₂ J₂) (initP₁ : PMF (M₁ × S₁ × S₁)) (initP₂ : PMF (M₂ × S₂ × S₂))
    (h₁ : C₁.init = liftPMF initP₁) (h₂ : C₂.init = liftPMF initP₂)
    (hJi₁ : ∀ i ∈ initP₁.support, J₁ i.2.1 i.2.2) (hJi₂ : ∀ i ∈ initP₂.support, J₂ i.2.1 i.2.2)
    (R : PRGDef (RK × (K₁ × K₂)) (RK × Sa)) (Gc : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    {ΔFS ΔPCS : ℕ} (hFS : 2 ≤ ΔFS) (hPCS : 1 ≤ ΔPCS)
    (A : SMSchemeAdv (M₁ × M₂) W Ct (SMPartySt (S₁ × S₂) RK Sa)) :
    (acdSM (prodCKA C₁ C₂) R Gc D).corruptAdvantage ΔFS ΔPCS A ≤
      ∑ b : Bool, (CKA_Corrupt_Advantage C₁ ΔFS ΔPCS
          (prodCorruptRed₁ C₂ initP₂ ΔPCS (smcCKARed R Gc D b A.toSM)) +
        CKA_Corrupt_Advantage C₂ ΔFS ΔPCS
          (prodCorruptRed₂ C₁ initP₁ ΔPCS (smcCKARed R Gc D b A.toSM))) +
        ∑ b : Bool, PRFPRNG_Advantage R (smcRootRed (prodCKA C₁ C₂) R Gc D ΔFS ΔPCS b
          (prodInitP initP₁ initP₂) A.toSM) +
        FSAEAD_Corrupt_Advantage Gc D (smcFSRed (prodCKA C₁ C₂) R Gc D ΔFS ΔPCS
          (prodInitP initP₁ initP₂) A.toSM) := by
  refine (acdSM_corruptAdvantage_le (prodCKA C₁ C₂) (prodCKACoins_sound C₁ C₂ hS₁ hS₂)
    (prodCKA_correct hJ₁ hJ₂) (prodInitP initP₁ initP₂) (prodCKA_init_eq C₁ C₂ initP₁ initP₂ h₁ h₂)
    (prodInitP_rel hJi₁ hJi₂) R Gc D hFS hPCS A).trans ?_
  gcongr with b _
  exact prodCKA_corrupt_advantage_le C₁ C₂ hS₁ hS₂ initP₁ initP₂ h₁ h₂ ΔFS ΔPCS _

end ACDProd

/-! ## The triple ratchet -/

section Triple

variable (G : Type) [CG : CyclicGroup G]

/-- The correctness relation of `dhCKA`: the public value held by the next sender is the public
value of the exponent of the next receiver. -/
def dhCKARel (s r : G × CG.Exp) : Prop := s.1 = CG.pow r.2

/-- **Correctness of `dhCKA`** along `dhCKARel`. -/
theorem dhCKA_ckaCorrect : CKACorrect (dhCKA G) (dhCKARel G) where
  key s r x h := by
    simp only [dhCKA, CKACoins.sendR]
    rw [show s.1 = CG.pow r.2 from h]
    exact elemPow_pow_comm x r.2
  next _ _ _ _ := rfl

/-- The initial states of `dhCKA` are related by `dhCKARel`. -/
theorem dhInitP_rel : ∀ i ∈ (dhInitP G).support, dhCKARel G i.2.1 i.2.2 := by
  intro i hi
  simp only [dhInitP, PMF.support_map, Set.mem_image] at hi
  obtain ⟨x, -, rfl⟩ := hi
  rfl

variable [DecidableEq G] {PK SK K E Rk RK Sa W Ct : Type} [Fintype K] [Nonempty K] [Inhabited K]
  [DecidableEq K] [Fintype Rk] [Nonempty Rk] [SampleableType W] [SampleableType Ct] [Fintype RK]
  [Nonempty RK] [DecidableEq RK] [Fintype Sa] [Nonempty Sa]

/-- **The triple ratchet with state corruption.** Let `KEM` be a KEM whose CKA `kemCKA KEM` has a
sound explicit-randomness sending algorithm with randomness `Rk`, is correct along `J`, and has an
initialisation that is the lift of `initP` with related initial states. For every adversary `A`
against the double ratchet `acdSM (prodCKA (dhCKA G) (kemCKA KEM)) R Gc D` with the delays
`ΔFS = ΔPCS = 2`, the advantage is at most, for the two challenge modes `b`, the DDH advantage of
`ckaCorruptDDHRed (prodCorruptRed₁ (kemCKA KEM) initP 2 (smcCKARed R Gc D b A.toSM))`, the CKA
corruption advantage of `kemCKA KEM` at `prodCorruptRed₂ (dhCKA G) (dhInitP G) 2
(smcCKARed R Gc D b A.toSM)` and the PRF-PRNG advantages of the root KDF `R`, plus the FS-AEAD
advantage with corruption of `Gc` and `D`. -/
theorem tripleRatchet_corruptAdvantage_le (KEM : KEMScheme PK SK K E)
    [CKACoins (kemCKA KEM) Rk] (hS : CKACoins.Sound (kemCKA KEM))
    {J : PK × SK → PK × SK → Prop} (hJ : CKACorrect (kemCKA KEM) J)
    (initP : PMF ((Option E × PK) × (PK × SK) × (PK × SK)))
    (hinit : (kemCKA KEM).init = liftPMF initP) (hJi : ∀ i ∈ initP.support, J i.2.1 i.2.2)
    (R : PRGDef (RK × (G × K)) (RK × Sa)) (Gc : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (A : SMSchemeAdv (G × (Option E × PK)) W Ct (SMPartySt ((G × CG.Exp) × (PK × SK)) RK Sa)) :
    (acdSM (prodCKA (dhCKA G) (kemCKA KEM)) R Gc D).corruptAdvantage 2 2 A ≤
      ∑ b : Bool, (DDH_Advantage G (ckaCorruptDDHRed
          (prodCorruptRed₁ (kemCKA KEM) initP 2 (smcCKARed R Gc D b A.toSM))) +
        CKA_Corrupt_Advantage (kemCKA KEM) 2 2
          (prodCorruptRed₂ (dhCKA G) (dhInitP G) 2 (smcCKARed R Gc D b A.toSM))) +
        ∑ b : Bool, PRFPRNG_Advantage R (smcRootRed (prodCKA (dhCKA G) (kemCKA KEM)) R Gc D 2 2 b
          (prodInitP (dhInitP G) initP) A.toSM) +
        FSAEAD_Corrupt_Advantage Gc D (smcFSRed (prodCKA (dhCKA G) (kemCKA KEM)) R Gc D 2 2
          (prodInitP (dhInitP G) initP) A.toSM) := by
  refine (acdSM_prod_corruptAdvantage_le (dhCKA G) (kemCKA KEM) (dhCKACoins_sound G) hS
    (dhCKA_ckaCorrect G) hJ (dhInitP G) initP (dhCKA_init_eq G) hinit (dhInitP_rel G) hJi R Gc D
    (le_refl 2) (by norm_num) A).trans ?_
  gcongr with b _
  exact dhCKA_corrupt_advantage_le (G := G) _

end Triple

/-! ## The Signal stack over the triple ratchet -/

section FSM

open CatCrypt.Crypto.PAKE.CPaceSquare CatCrypt.Crypto.Messaging.SignalStack
  CatCrypt.Crypto.Messaging.SignalStackSM CatCrypt.Crypto.UCConcrete
  CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.FAKE CatCrypt.Crypto.AKE.X3DHSquare
  CatCrypt.Crypto.AKE.X3DHSquareGDH CatCrypt.Crypto.Messaging.SignalStackUC
  CatCrypt.Crypto.PAKE.DHExtract

variable {S₁ M₁ K₁ S₂ M₂ K₂ : Type}

/-- The product of CKA schemes that neither touch the heap nor fail neither touches the heap
nor fails. -/
theorem prodCKA_pureNF {C₁ : CKADef S₁ M₁ K₁} {C₂ : CKADef S₂ M₂ K₂} (h₁ : CKAPureNF C₁)
    (h₂ : CKAPureNF C₂) : CKAPureNF (prodCKA C₁ C₂) := by
  refine ⟨?_, fun s => ?_⟩ <;> simp only [prodCKA]
  · exact h₁.1.bind fun _ => h₂.1.bind fun _ => pureNF_pure _
  · exact (h₁.2 s.1).bind fun _ => (h₂.2 s.2).bind fun _ => pureNF_pure _

/-- The KEM CKA of a KEM whose key generation and encapsulation neither touch the heap nor fail
neither touches the heap nor fails. -/
theorem kemCKA_pureNF {PK SK K E : Type} [Inhabited K] (KEM : KEMScheme PK SK K E)
    (hk : PureNF KEM.kgen) (he : ∀ pk, PureNF (KEM.encap pk)) : CKAPureNF (kemCKA KEM) := by
  refine ⟨?_, fun s => ?_⟩ <;> simp only [kemCKA]
  · exact hk.bind fun _ => pureNF_pure _
  · exact (he s.1).bind fun _ => hk.bind fun _ => pureNF_pure _

variable {S W : Type} [Field S] [Fintype S] [SampleableType W] (G : DHGroup S W)
  (Gc : Type) [CyclicGroup Gc] {PK SK K E Rk RK Sa Wd Ct V : Type} [Inhabited K] [Fintype Rk]
  [Nonempty Rk] [SampleableType Wd] [SampleableType Ct] [Fintype RK] [Nonempty RK] [Inhabited RK]

/-- **The Signal stack over the triple ratchet realizes secure messaging with corruption**
(genuine UC): `signal_stack_realizes_FSM_acd` at the product `prodCKA (dhCKA Gc) (kemCKA KEM)`,
for a KEM whose key generation and encapsulation neither touch the heap nor fail. The ideal
functionality is `F_SM` over `acdSM (prodCKA (dhCKA Gc) (kemCKA KEM)) R Ch D` keyed through
`acdIni`, the real world is X3DH followed by the ratchet layer over the same scheme with the
session key as the first root key, the simulator is `scSim G`, and the bound is `fsmBound`. -/
theorem tripleRatchet_realizes_FSM (P : Finset PartyId) (KEM : KEMScheme PK SK K E)
    [CKACoins (kemCKA KEM) Rk] (hk : PureNF KEM.kgen) (he : ∀ pk, PureNF (KEM.encap pk))
    (R : PRGDef (RK × (Gc × K)) (RK × Sa)) (Ch : PRGDef Sa (Wd × Sa)) (D : AEADDef Wd Ct)
    (Sch : (Gc × (Option E × PK)) → OracleAdv (SMQuery Wd)
      (SMSchemeAns (Gc × (Option E × PK)) Ct
        (SMPartySt ((Gc × CyclicGroup.Exp Gc) × (PK × SK)) RK Sa)) V)
    (t n ΔFS ΔPCS : ℕ) :
    RealizesSim ((x3dhReal (K := RK) G).seq
        (smCorruptLayer (acdSM (prodCKA (dhCKA Gc) (kemCKA KEM)) R Ch D)
          (acdIni (prodCKA (dhCKA Gc) (kemCKA KEM))) Sch t n ΔFS ΔPCS))
      (F_SM (acdSM (prodCKA (dhCKA Gc) (kemCKA KEM)) R Ch D)
        (acdIni (prodCKA (dhCKA Gc) (kemCKA KEM))) Sch t n ΔFS ΔPCS) (scSim G)
      (fsmBound G P (acdSM (prodCKA (dhCKA Gc) (kemCKA KEM)) R Ch D)
        (acdIni (prodCKA (dhCKA Gc) (kemCKA KEM)))
        (acdIni_pureNF (prodCKA_pureNF (dhCKA_pureNF Gc) (kemCKA_pureNF KEM hk he)).1) Sch t n
        ΔFS ΔPCS) :=
  signal_stack_realizes_FSM_acd G P (prodCKA (dhCKA Gc) (kemCKA KEM))
    (prodCKA_pureNF (dhCKA_pureNF Gc) (kemCKA_pureNF KEM hk he)) R Ch D Sch t n ΔFS ΔPCS

end FSM

end CatCrypt.Crypto.Messaging
