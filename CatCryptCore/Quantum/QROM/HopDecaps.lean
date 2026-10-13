/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.KEMQuantumGame
public import CatCryptCore.Quantum.QROM.HopDecapsBijection
public import CatCryptCore.Quantum.QROM.QAdvGame

/-!
# The decapsulation hop: answering decapsulation queries from the `G`-table

In the quantum IND-CCA game of `Quantum/QROM/KEMQuantumGame.lean` the classical
rounds are answered by `kemDecaps`, which reads the secret key through
`decapsFixed`. This module replaces that function by one that reads the key off
the `G`-table: a ciphertext `c` is answered with the key part of the table at a
message whose ciphertext under the table's coins is `c`, and with the rejection
key of `J` when there is no such message. The lookup uses the public key and the
`G`-table only.

The two functions coincide on an input whose `G`-table has no decryption
failure: the ciphertext map is then injective, so the lookup returns the key of
the message the decryption map recovers, which is the answer of the real
decapsulation.

## Main definitions

* `simKeyAt enc T c` — the key of a message whose ciphertext under the coins of
  the table `T` is `c`, and `none` when there is no such message
* `kemTab i` — the key-and-coin table of an input: the `G`-table at the hash of
  the public key
* `kemGood i` — the messages whose ciphertext under the coins of `kemTab i`
  decrypts back to them
* `decapsSim i` — the simulated classical function of the rounds: `simKeyAt` with
  the rejection key of `J`, the challenge ciphertext answered as `decapsOracle`
  answers it
* `prWinKEMSim A b` — the winning probability with the simulated rounds

## Main results

* `simKeyAt_encOf`, `simKeyAt_eq_none_of_not_mem_range` — the lookup at the
  ciphertext of a message, under injectivity, and off the ciphertexts
* `simKeyAt_eq_keyAt_of_good` — when every message is good the lookup agrees
  with `keyAt`, which reads the decryption map
* `keyAt_getD_eq_decapsFixed` — `keyAt` with the rejection key of `J` as default
  is `decapsFixed`
* `decapsSim_eq_of_good` — the simulated and the real classical functions
  coincide on a failure-free input
* `prOutMR_eq_of_good` — the two runs have the same output probability there
* `hopD` — `|prWinKEM − prWinKEMSim|` is at most the weight of the inputs with a
  decryption failure
* `hopD_le_delta` — the union bound `|M| · δ` over the messages: the failure
  event is bounded message by message and the bounds are added

## References

* [Hofheinz, Hövelmanns, Kiltz — A Modular Analysis of the Fujisaki–Okamoto
  Transformation, TCC 2017], §4.2
* [Jiang, Zhang, Chen, Wang, Ma — IND-CCA-Secure Key Encapsulation Mechanism in
  the Quantum Random Oracle Model, Revisited, CRYPTO 2018]
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal
open CatCrypt.Quantum
open CatCrypt.Crypto.PKE.Games (Scheme)

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## The lookup by ciphertext -/

section Lookup

variable {M C Key Coin : Type}

open scoped Classical in
/-- The key stored at a ciphertext by a key-and-coin table alone: the key part of
the table at a message whose ciphertext under the table's coins is `c`, and
`none` when there is no such message. -/
def simKeyAt (enc : M → Coin → C) (T : M → Key × Coin) (c : C) : Option Key :=
  if h : ∃ m, encOf enc T m = c then some (T h.choose).1 else none

open scoped Classical in
/-- At the ciphertext of a message the lookup returns that message's key, when
the ciphertext map is injective. -/
theorem simKeyAt_encOf {enc : M → Coin → C} {T : M → Key × Coin}
    (hinj : Function.Injective (encOf enc T)) (m : M) :
    simKeyAt enc T (encOf enc T m) = some (T m).1 := by
  have hex : ∃ m', encOf enc T m' = encOf enc T m := ⟨m, rfl⟩
  rw [simKeyAt, dif_pos hex, hinj hex.choose_spec]

open scoped Classical in
/-- Off the ciphertexts of the messages no key is stored. -/
theorem simKeyAt_eq_none_of_not_mem_range {enc : M → Coin → C} {T : M → Key × Coin}
    {c : C} (hc : ¬ ∃ m, encOf enc T m = c) : simKeyAt enc T c = none := by
  rw [simKeyAt, dif_neg hc]

variable [Fintype M] [DecidableEq M] [Fintype C] [DecidableEq C]
variable [Fintype Key] [DecidableEq Key] [Fintype Coin] [DecidableEq Coin]

omit [Fintype C] [Fintype Key] [DecidableEq Key] [Fintype Coin] [DecidableEq Coin] in
/-- When every message is good the table lookup agrees with the lookup that
reads the decryption map. -/
theorem simKeyAt_eq_keyAt_of_good (enc : M → Coin → C) (dec : C → Option M)
    (T : M → Key × Coin) (h : ∀ m, m ∈ Good enc dec (coinsOf T)) (c : C) :
    simKeyAt enc T c = keyAt enc dec T c := by
  have hinj : Function.Injective (encOf enc T) :=
    encAt_injective_of_good_eq_univ enc dec (coinsOf T) (Finset.eq_univ_iff_forall.mpr h)
  by_cases hc : ∃ m, encOf enc T m = c
  · obtain ⟨m, rfl⟩ := hc
    rw [simKeyAt_encOf hinj, keyAt_encOf (h m)]
  · rw [simKeyAt_eq_none_of_not_mem_range hc,
      keyAt_eq_none_of_not_mem_image fun hmem => hc ?_]
    obtain ⟨m, _, hm⟩ := Finset.mem_image.1 hmem
    exact ⟨m, hm⟩

end Lookup

/-! ## The simulated decapsulation function -/

section Sim

variable {m₁ m₂ n w q k c a : ℕ} {PK SK M C R K Hash Z : Type} [Fintype PK] [Fintype SK]
  [Fintype M] [DecidableEq M] [Nonempty M] [Fintype Z] [Nonempty Z] [Fintype K] [DecidableEq K]
  [Nonempty K] [Fintype R] [DecidableEq R] [Nonempty R] [Fintype C] [DecidableEq C]
  (P : Scheme PK SK M C R) (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁)
  (eJ : (Z × C) ≃ Fin m₂) (eKR : (K × R) ≃ Fin n) (eC : C ≃ Fin c) (eKa : K ≃ Fin a)

/-- The key-and-coin table of an input: the `G`-table at the hash of the public
key. -/
def kemTab (i : KEMInput PK SK Z M K m₁ m₂ n) : M → K × R :=
  fun m => kemG eG eKR i (m, hpk i.1.1)

/-- The messages whose ciphertext under the coins of the `G`-table decrypts back
to them. -/
def kemGood (i : KEMInput PK SK Z M K m₁ m₂ n) : Finset M :=
  Good (P.enc i.1.1) (P.dec i.1.2) (coinsOf (kemTab hpk eG eKR i))

omit [Fintype PK] [Fintype SK] [Fintype M] [DecidableEq M] [Nonempty M] [Fintype Z] [Nonempty Z]
  [Fintype K] [DecidableEq K] [Nonempty K] [Fintype R] [DecidableEq R] [Nonempty R] [Fintype C] in
/-- `keyAt` with the rejection key of `J` as default is the decapsulation of
`fips203 P hpk` at the input's oracle functions. -/
theorem keyAt_getD_eq_decapsFixed (i : KEMInput PK SK Z M K m₁ m₂ n) (c' : C) :
    (keyAt (P.enc i.1.1) (P.dec i.1.2) (kemTab hpk eG eKR i) c').getD
        (kemJ eJ eKR i (i.2.1, c')) =
      decapsFixed P hpk (kemG eG eKR i) (kemJ eJ eKR i) (i.1.2, i.1.1, i.2.1) c' := by
  simp only [keyAt, decapsFixed, encOf, encAt, coinsOf, kemTab]
  cases P.dec i.1.2 c' with
  | none => simp
  | some m =>
    by_cases he : P.enc i.1.1 m (kemG eG eKR i (m, hpk i.1.1)).2 = c' <;> simp [he]

/-- The simulated classical function of the rounds: the key read off the
`G`-table at a message with the queried ciphertext, the rejection key of `J`
when there is none, and a fixed key at the challenge ciphertext. -/
def decapsSim (i : KEMInput PK SK Z M K m₁ m₂ n) : Fin c → Fin a :=
  fun x => if eC.symm x = kemChal P hpk eG eKR i then eKa (Classical.arbitrary K)
    else eKa ((simKeyAt (P.enc i.1.1) (kemTab hpk eG eKR i) (eC.symm x)).getD
      (kemJ eJ eKR i (i.2.1, eC.symm x)))

omit [Fintype PK] [Fintype SK] [Nonempty M] [Fintype Z] [Nonempty Z] [Fintype K] [DecidableEq K]
  [Fintype R] [DecidableEq R] [Nonempty R] [Fintype C] in
/-- On an input whose `G`-table has no decryption failure the simulated and the
real classical functions of the rounds coincide. -/
theorem decapsSim_eq_of_good (i : KEMInput PK SK Z M K m₁ m₂ n)
    (h : ∀ m, m ∈ kemGood P hpk eG eKR i) :
    decapsSim P hpk eG eJ eKR eC eKa i = kemDecaps P hpk eG eJ eKR eC eKa i := by
  funext x
  simp only [decapsSim, kemDecaps, decapsOracle]
  by_cases hx : eC.symm x = kemChal P hpk eG eKR i
  · rw [if_pos hx, if_pos hx]
  · rw [if_neg hx, if_neg hx,
      simKeyAt_eq_keyAt_of_good (P.enc i.1.1) (P.dec i.1.2) (kemTab hpk eG eKR i) h,
      keyAt_getD_eq_decapsFixed]

variable [NeZero n]

omit [Fintype PK] [Fintype SK] [Nonempty M] [Fintype Z] [Nonempty Z] [Fintype K] [DecidableEq K]
  [Fintype R] [DecidableEq R] [Nonempty R] [Fintype C] in
/-- The two runs have the same output probability on a failure-free input. -/
theorem prOutMR_eq_of_good (A : QAdvMR (m₁ + m₂) n (2 * w) q k c a)
    (i : KEMInput PK SK Z M K m₁ m₂ n) (h : ∀ m, m ∈ kemGood P hpk eG eKR i) :
    prOutMR A (kemOracle i) (decapsSim P hpk eG eJ eKR eC eKa i) =
      prOutMR A (kemOracle i) (kemDecaps P hpk eG eJ eKR eC eKa i) := by
  rw [decapsSim_eq_of_good P hpk eG eJ eKR eC eKa i h]

/-- The probability that `A` outputs `1` in the game with bit `b` when the
classical rounds are answered by the simulated function. -/
def prWinKEMSim (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool) : ℝ≥0∞ :=
  ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i *
    prOutMR (A.run i.1.1 (kemChal P hpk eG eKR i) (kemKey hpk eG eKR i b)) (kemOracle i)
      (decapsSim P hpk eG eJ eKR eC eKa i)

omit [Nonempty M] [Nonempty Z] [DecidableEq K] [Fintype R] [DecidableEq R] [Nonempty R]
  [Fintype C] in
/-- The decapsulation hop: the two games differ by at most the weight of the
inputs whose `G`-table has a decryption failure. -/
theorem hopD (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool) :
    absDiff (prWinKEM P hpk eG eJ eKR eC eKa A b) (prWinKEMSim P hpk eG eJ eKR eC eKa A b) ≤
      ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i *
        (if ∀ m, m ∈ kemGood P hpk eG eKR i then 0 else 1) := by
  refine le_trans (absDiff_sum_le _ _) (Finset.sum_le_sum fun i _ => ?_)
  refine le_trans (absDiff_mul_left_le _ _ _) ?_
  gcongr
  by_cases hg : ∀ m, m ∈ kemGood P hpk eG eKR i
  · rw [if_pos hg, decapsSim_eq_of_good P hpk eG eJ eKR eC eKa i hg]
    exact le_of_eq (absDiff_self _)
  · rw [if_neg hg]
    exact absDiff_le_iff.mpr ⟨le_trans (prOutMR_le_one _ _ _) le_add_self,
      le_trans (prOutMR_le_one _ _ _) le_add_self⟩

omit [Nonempty M] [Nonempty Z] [DecidableEq K] [Fintype R] [DecidableEq R] [Nonempty R]
  [Fintype C] in
/-- The union bound over the messages: a per-message failure bound `δ` gives
`|M| · δ` for the decapsulation hop. -/
theorem hopD_le_delta (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool) (δ : ℝ≥0∞)
    (hδ : ∀ m : M, ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i *
        (if m ∈ kemGood P hpk eG eKR i then 0 else 1) ≤ δ) :
    absDiff (prWinKEM P hpk eG eJ eKR eC eKa A b) (prWinKEMSim P hpk eG eJ eKR eC eKa A b) ≤
      (Fintype.card M : ℝ≥0∞) * δ := by
  refine le_trans (hopD P hpk eG eJ eKR eC eKa A b) ?_
  calc ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i *
        (if ∀ m, m ∈ kemGood P hpk eG eKR i then 0 else 1)
      ≤ ∑ i : KEMInput PK SK Z M K m₁ m₂ n, ∑ m : M, kemSample P i *
          (if m ∈ kemGood P hpk eG eKR i then 0 else 1) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [← Finset.mul_sum]
        gcongr
        by_cases hg : ∀ m, m ∈ kemGood P hpk eG eKR i
        · rw [if_pos hg]; exact zero_le
        · rw [if_neg hg]
          obtain ⟨m₀, hm₀⟩ := not_forall.mp hg
          calc (1 : ℝ≥0∞) = (if m₀ ∈ kemGood P hpk eG eKR i then 0 else 1) := (if_neg hm₀).symm
            _ ≤ ∑ m : M, (if m ∈ kemGood P hpk eG eKR i then (0 : ℝ≥0∞) else 1) :=
                Finset.single_le_sum
                  (f := fun m => if m ∈ kemGood P hpk eG eKR i then (0 : ℝ≥0∞) else 1)
                  (fun m _ => zero_le) (Finset.mem_univ m₀)
    _ = ∑ m : M, ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i *
          (if m ∈ kemGood P hpk eG eKR i then 0 else 1) := Finset.sum_comm
    _ ≤ ∑ _m : M, δ := Finset.sum_le_sum fun m _ => hδ m
    _ = (Fintype.card M : ℝ≥0∞) * δ := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end Sim

end CatCrypt.Quantum.QROM
