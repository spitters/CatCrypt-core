/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.HopDecaps

/-!
# The key of a message as a random function of its ciphertext

The hop of Saito–Xagawa–Yamakawa and Jiang–Zhang–Chen–Wang–Ma on the quantum
IND-CCA game of `Quantum/QROM/KEMQuantumGame.lean`: on the public-key slice of
the `G`-table the key part `G(m, hpk pk).1` is replaced by `Hq c` for an
independent uniform function `Hq : C → K`, where `c` is the encryption of `m`
under the coin part `G(m, hpk pk).2`. The coin part is kept.

On a table whose ciphertext map is injective on the slice, exchanging the key
part at each slice point with the value of `Hq` at its ciphertext is an
involution of the pair (table, `Hq`). The uniform weight on pairs is invariant
under it, so the hopped table is uniform, and jointly with it the values of `Hq`
off the ciphertexts of the slice are uniform and independent.

## Main definitions

* `coinCt e ε g` — the ciphertext map `x ↦ e x r` of a table `g : X → V`, with
  `r` the coin part of `g x`
* `SliceInj S e ε g` — the ciphertext map is injective on the slice `S`
* `keyHop S e ε Hq g` — the table with its key part on `S` replaced by `Hq` at
  the ciphertext
* `keySwapCt S e ε` — the involution of pairs (table, `Hq`) exchanging key parts
  on `S` with the values of `Hq` at the ciphertexts
* `offImage S e ε g Hq` — `Hq` restricted to the ciphertexts outside the image
  of the slice
* `mergeOn T Hq r`, `restrictOn T Hq` — `Hq` on `T` and `r` off `T`, and `Hq`
  restricted to `T`
* `decapsHq eC eKa H cstar` — decapsulation answering every ciphertext other
  than `cstar` by the table `H`
* `kemSlice`, `kemEncAt`, `kemInj` — the slice `{(m, hpk pk)}`, the encryption
  at a slice point, and the injectivity condition at an input
* `inputH i Hq`, `kemOracleH i Hq`, `decapsH i Hq` — the hopped input, its
  merged oracle and its simulated decapsulation
* `prWinKEMH A b` — the winning probability of the hopped game

## Main results

* `keySwapCt_involutive`, `sum_keySwapCt` — the exchange is an involution and
  preserves sums over pairs
* `sum_keyHop` — the relabelling: over injective tables the pair
  (`keyHop Hq g`, `offImage g Hq`) has the law of (`g`, `offImage g Hq`)
* `kemInj_iff` — the injectivity condition is injectivity of the ciphertext
  map of `kemTab i`
* `kemKey_inputH_true`, `kemChal_inputH` — the hopped challenge key is
  `Hq c*`, the challenge ciphertext is unchanged
* `decapsH_apply`, `decapsH_of_encOf` — off `c*` a decapsulation answer is
  `Hq c` on the ciphertexts of the slice and the rejection key of `J` elsewhere
* `decapsH_eq_decapsHq` — the hopped decapsulation is `decapsHq` at the table
  `mergeOn (image) Hq J(z, ·)`
* `sum_mergeOn` — for independent uniform `Hq` and `r`, (`Hq` on `T`,
  `mergeOn T Hq r`) has the law of (`Hq` on `T`, `Hq`)
* `hopH` — `|prWinKEMH − prWinKEMSim|` is at most the weight of the inputs
  whose ciphertext map is not injective
* `hopH_cost_le` — that weight is at most the decryption-failure weight of
  `hopD`

## The hopped decapsulation

The hop `hopH` is stated against `prWinKEMSim` of `Quantum/QROM/HopDecaps.lean`. By
`decapsH_eq_decapsHq` the hopped decapsulation is `decapsHq` at the table that
is `Hq` on the image of the slice and `J(z, ·)` off it; `decapsHq` reads that
table and `c*` only. The image is read off the coin table at every message, and
`J(z, ·)` is part of the oracle the adversary queries in this game. By
`sum_mergeOn` the merged table has the law of `Hq` when the rejection table is
an independent uniform table read nowhere else, and by `sum_keyHop` `Hq` off
the image is independent of the hopped oracle table.

## References

* [Saito, Xagawa, Yamakawa — Tightly-Secure Key-Encapsulation Mechanism in the
  Quantum Random Oracle Model, EUROCRYPT 2018]
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

/-! ## The relabelling of a key table by ciphertexts -/

section Relabel

variable {X V K R C : Type} (S : X → Prop) [DecidablePred S] (e : X → R → C) (ε : V ≃ K × R)

/-- The ciphertext map of a table: `x ↦ e x r` with `r` the coin part of `g x`. -/
def coinCt (g : X → V) (x : X) : C := e x (ε (g x)).2

/-- The ciphertext map of `g` is injective on the slice `S`. -/
def SliceInj (g : X → V) : Prop :=
  ∀ x y, S x → S y → coinCt e ε g x = coinCt e ε g y → x = y

/-- The table with its key part on the slice `S` replaced by `Hq` at the
ciphertext, the coin part kept. -/
def keyHop (Hq : C → K) (g : X → V) : X → V :=
  fun x => if S x then ε.symm (Hq (coinCt e ε g x), (ε (g x)).2) else g x

theorem coinCt_keyHop (Hq : C → K) (g : X → V) :
    coinCt e ε (keyHop S e ε Hq g) = coinCt e ε g := by
  funext x
  unfold coinCt keyHop
  split_ifs <;> simp

theorem sliceInj_keyHop (Hq : C → K) (g : X → V) :
    SliceInj S e ε (keyHop S e ε Hq g) ↔ SliceInj S e ε g := by
  unfold SliceInj
  rw [coinCt_keyHop]

open scoped Classical in
/-- The exchange of the key parts of a table on the slice with the values of
`Hq` at their ciphertexts, when the ciphertext map is injective on the slice;
the identity otherwise. -/
def keySwapCt (p : (X → V) × (C → K)) : (X → V) × (C → K) :=
  if SliceInj S e ε p.1 then
    (keyHop S e ε p.2 p.1, fun y =>
      if h : ∃ x, S x ∧ coinCt e ε p.1 x = y then (ε (p.1 h.choose)).1 else p.2 y)
  else p

open scoped Classical in
/-- The values of `Hq` at the ciphertexts outside the image of the slice. -/
def offImage (g : X → V) (Hq : C → K) (y : C) : Option K :=
  if ∃ x, S x ∧ coinCt e ε g x = y then none else some (Hq y)

open scoped Classical in
theorem keySwapCt_of_inj {p : (X → V) × (C → K)} (h : SliceInj S e ε p.1) :
    keySwapCt S e ε p = (keyHop S e ε p.2 p.1, fun y =>
      if h : ∃ x, S x ∧ coinCt e ε p.1 x = y then (ε (p.1 h.choose)).1 else p.2 y) := by
  rw [keySwapCt, if_pos h]

theorem keySwapCt_of_not_inj {p : (X → V) × (C → K)} (h : ¬ SliceInj S e ε p.1) :
    keySwapCt S e ε p = p := by
  rw [keySwapCt, if_neg h]

/-- The exchange is an involution. -/
theorem keySwapCt_involutive : Function.Involutive (keySwapCt S e ε) := by
  classical
  rintro ⟨g, Hq⟩
  by_cases hinj : SliceInj S e ε g
  · rw [keySwapCt_of_inj S e ε (p := (g, Hq)) hinj]
    have hinj' : SliceInj S e ε (keyHop S e ε Hq g) := (sliceInj_keyHop S e ε Hq g).2 hinj
    rw [keySwapCt_of_inj S e ε hinj']
    simp only [coinCt_keyHop]
    refine Prod.ext (funext fun x => ?_) (funext fun y => ?_)
    · dsimp only
      by_cases hx : S x
      · have hex : ∃ x', S x' ∧ coinCt e ε g x' = coinCt e ε g x := ⟨x, hx, rfl⟩
        have hch : hex.choose = x := hinj _ _ hex.choose_spec.1 hx hex.choose_spec.2
        simp only [keyHop, if_pos hx, coinCt_keyHop, dif_pos hex, hch, Equiv.apply_symm_apply]
        simp
      · simp only [keyHop, if_neg hx]
    · dsimp only
      by_cases hy : ∃ x, S x ∧ coinCt e ε g x = y
      · rw [dif_pos hy]
        simp only [keyHop, if_pos hy.choose_spec.1, Equiv.apply_symm_apply, hy.choose_spec.2]
      · rw [dif_neg hy, dif_neg hy]
  · rw [keySwapCt_of_not_inj S e ε (p := (g, Hq)) hinj,
      keySwapCt_of_not_inj S e ε (p := (g, Hq)) hinj]

variable [Fintype X] [DecidableEq X] [Fintype V] [Fintype C] [DecidableEq C] [Fintype K]

/-- A sum over pairs (table, `Hq`) is unchanged by the exchange. -/
theorem sum_keySwapCt (G : (X → V) × (C → K) → ℝ≥0∞) :
    ∑ p, G (keySwapCt S e ε p) = ∑ p, G p :=
  Fintype.sum_equiv ((keySwapCt_involutive S e ε).toPerm _) _ _ fun _ => rfl

omit [Fintype X] [DecidableEq X] [Fintype V] [Fintype C] [DecidableEq C] [Fintype K] in
theorem offImage_keySwapCt {p : (X → V) × (C → K)} (h : SliceInj S e ε p.1) :
    offImage S e ε (keySwapCt S e ε p).1 (keySwapCt S e ε p).2 = offImage S e ε p.1 p.2 := by
  classical
  rw [keySwapCt_of_inj S e ε h]
  funext y
  simp only [offImage, coinCt_keyHop]
  by_cases hy : ∃ x, S x ∧ coinCt e ε p.1 x = y
  · rw [if_pos hy, if_pos hy]
  · rw [if_neg hy, if_neg hy, dif_neg hy]

open scoped Classical in
/-- The relabelling: over the tables whose ciphertext map is injective on the
slice, the hopped table together with `Hq` off the image of the slice has the
law of the table together with `Hq` off the image, the table and `Hq` drawn
independently. -/
theorem sum_keyHop (F : (X → V) → (C → Option K) → ℝ≥0∞) :
    ∑ g : X → V, ∑ Hq : C → K,
        (if SliceInj S e ε g then F (keyHop S e ε Hq g) (offImage S e ε g Hq) else 0) =
      ∑ g : X → V, ∑ Hq : C → K,
        (if SliceInj S e ε g then F g (offImage S e ε g Hq) else 0) := by
  rw [← Fintype.sum_prod_type', ← Fintype.sum_prod_type']
  rw [← sum_keySwapCt S e ε (fun p =>
    if SliceInj S e ε p.1 then F p.1 (offImage S e ε p.1 p.2) else 0)]
  refine Finset.sum_congr rfl fun p _ => ?_
  by_cases h : SliceInj S e ε p.1
  · have h' : SliceInj S e ε (keySwapCt S e ε p).1 := by
      rw [keySwapCt_of_inj S e ε h]; exact (sliceInj_keyHop S e ε _ _).2 h
    rw [if_pos h, if_pos h', offImage_keySwapCt S e ε h, keySwapCt_of_inj S e ε h]
  · rw [if_neg h, keySwapCt_of_not_inj S e ε h, if_neg h]

end Relabel

/-! ## Merging the rejection table into `Hq` -/

section Merge

variable {C K : Type} [Fintype C] [DecidableEq C] [Fintype K] (T : C → Prop) [DecidablePred T]

/-- `Hq` on `T` and `r` off `T`. -/
def mergeOn (Hq r : C → K) (y : C) : K := if T y then Hq y else r y

/-- `Hq` restricted to `T`. -/
def restrictOn (Hq : C → K) (y : C) : Option K := if T y then some (Hq y) else none

omit [Fintype C] [DecidableEq C] [Fintype K] in
/-- Exchanging `Hq` and `r` off `T` is an involution of pairs of tables. -/
theorem mergeSwap_involutive :
    Function.Involutive fun p : (C → K) × (C → K) => (mergeOn T p.1 p.2, mergeOn T p.2 p.1) := by
  rintro ⟨Hq, r⟩
  refine Prod.ext (funext fun y => ?_) (funext fun y => ?_) <;>
    by_cases hy : T y <;> simp [mergeOn, hy]

/-- For independent uniform `Hq` and `r`, the pair (`Hq` on `T`, `Hq` on `T` and
`r` off `T`) has the law of (`Hq` on `T`, `Hq`). -/
theorem sum_mergeOn (F : (C → Option K) → (C → K) → ℝ≥0∞) :
    ∑ Hq : C → K, ∑ r : C → K, F (restrictOn T Hq) (mergeOn T Hq r) =
      ∑ Hq : C → K, ∑ _r : C → K, F (restrictOn T Hq) Hq := by
  rw [← Fintype.sum_prod_type' (f := fun Hq r => F (restrictOn T Hq) (mergeOn T Hq r)),
    ← Fintype.sum_prod_type' (f := fun Hq (_ : C → K) => F (restrictOn T Hq) Hq)]
  refine Fintype.sum_equiv ((mergeSwap_involutive T).toPerm _) _ _ fun p => ?_
  change _ = F (restrictOn T (mergeOn T p.1 p.2)) (mergeOn T p.1 p.2)
  congr 1
  funext y
  by_cases hy : T y <;> simp [restrictOn, mergeOn, hy]

end Merge

/-! ## The hopped input of the KEM game -/

section Input

variable {m₁ m₂ n : ℕ} {PK SK M C R K Hash Z : Type} [DecidableEq Hash]
  (P : Scheme PK SK M C R) (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁) (eKR : (K × R) ≃ Fin n)

/-- The public-key slice of the `G`-table: the points `(m, hpk pk)`. -/
def kemSlice (pk : PK) (y : Fin m₁) : Prop := (eG.symm y).2 = hpk pk

instance (pk : PK) : DecidablePred (kemSlice hpk eG pk) :=
  fun y => inferInstanceAs (Decidable ((eG.symm y).2 = hpk pk))

omit [DecidableEq Hash] in
/-- The encryption at a point of the `G`-table: the message of the point
encrypted under `pk` with the coin `r`. -/
def kemEncAt (pk : PK) (y : Fin m₁) (r : R) : C := P.enc pk (eG.symm y).1 r

/-- The ciphertext map of the `G`-table of an input is injective on the
public-key slice. -/
def kemInj (i : KEMInput PK SK Z M K m₁ m₂ n) : Prop :=
  SliceInj (kemSlice hpk eG i.1.1) (kemEncAt P eG i.1.1) eKR.symm i.2.2.2.2.1

/-- The hopped input: the key part of the `G`-table on the public-key slice is
`Hq` at the ciphertext of the point, everything else is kept. -/
def inputH (i : KEMInput PK SK Z M K m₁ m₂ n) (Hq : C → K) : KEMInput PK SK Z M K m₁ m₂ n :=
  (i.1, i.2.1, i.2.2.1, i.2.2.2.1,
    keyHop (kemSlice hpk eG i.1.1) (kemEncAt P eG i.1.1) eKR.symm Hq i.2.2.2.2.1, i.2.2.2.2.2)

/-- The merged oracle of the hopped input. -/
def kemOracleH (i : KEMInput PK SK Z M K m₁ m₂ n) (Hq : C → K) : Fin (m₁ + m₂) → Fin n :=
  kemOracle (inputH P hpk eG eKR i Hq)

theorem kemTab_inputH (i : KEMInput PK SK Z M K m₁ m₂ n) (Hq : C → K) (m : M) :
    kemTab hpk eG eKR (inputH P hpk eG eKR i Hq) m =
      (Hq (encOf (P.enc i.1.1) (kemTab hpk eG eKR i) m), (kemTab hpk eG eKR i m).2) := by
  simp [kemTab, kemG, inputH, keyHop, kemSlice, coinCt, kemEncAt, encOf, encAt, coinsOf]

theorem encOf_inputH (i : KEMInput PK SK Z M K m₁ m₂ n) (Hq : C → K) :
    encOf (P.enc i.1.1) (kemTab hpk eG eKR (inputH P hpk eG eKR i Hq)) =
      encOf (P.enc i.1.1) (kemTab hpk eG eKR i) := by
  funext m
  simp only [encOf, encAt, coinsOf, kemTab_inputH]

/-- The merged oracle of the hopped input carries `Hq` at the ciphertext of `m`
as the key part at `(m, hpk pk)`. -/
theorem kemOracleH_castAdd (i : KEMInput PK SK Z M K m₁ m₂ n) (Hq : C → K) (m : M) :
    eKR.symm (kemOracleH P hpk eG eKR i Hq (Fin.castAdd m₂ (eG (m, hpk i.1.1)))) =
      (Hq (encOf (P.enc i.1.1) (kemTab hpk eG eKR i) m), (kemTab hpk eG eKR i m).2) := by
  rw [← kemTab_inputH]
  simp [kemOracleH, kemOracle, kemTab, kemG, inputH]

/-- The challenge ciphertext is unchanged by the hop. -/
theorem kemChal_inputH (i : KEMInput PK SK Z M K m₁ m₂ n) (Hq : C → K) :
    kemChal P hpk eG eKR (inputH P hpk eG eKR i Hq) = kemChal P hpk eG eKR i :=
  congrFun (encOf_inputH P hpk eG eKR i Hq) i.2.2.1

/-- The encapsulated challenge key of the hopped input is `Hq` at the challenge
ciphertext. -/
theorem kemKey_inputH_true (i : KEMInput PK SK Z M K m₁ m₂ n) (Hq : C → K) :
    kemKey hpk eG eKR (inputH P hpk eG eKR i Hq) true = Hq (kemChal P hpk eG eKR i) :=
  congrArg Prod.fst (kemTab_inputH P hpk eG eKR i Hq i.2.2.1)

open scoped Classical in
/-- The ciphertext lookup at the hopped table returns `Hq c` at every ciphertext
of a message and nothing elsewhere. -/
theorem simKeyAt_inputH (i : KEMInput PK SK Z M K m₁ m₂ n) (Hq : C → K) (c' : C) :
    simKeyAt (P.enc i.1.1) (kemTab hpk eG eKR (inputH P hpk eG eKR i Hq)) c' =
      if ∃ m, encOf (P.enc i.1.1) (kemTab hpk eG eKR i) m = c' then some (Hq c') else none := by
  unfold simKeyAt
  by_cases h : ∃ m, encOf (P.enc i.1.1) (kemTab hpk eG eKR i) m = c'
  · have h' : ∃ m, encOf (P.enc i.1.1) (kemTab hpk eG eKR (inputH P hpk eG eKR i Hq)) m = c' := by
      rwa [encOf_inputH]
    have hc : encOf (P.enc i.1.1) (kemTab hpk eG eKR i) h'.choose = c' :=
      (congrFun (encOf_inputH P hpk eG eKR i Hq) h'.choose).symm.trans h'.choose_spec
    rw [dif_pos h', if_pos h, kemTab_inputH, hc]
  · have h' : ¬ ∃ m, encOf (P.enc i.1.1) (kemTab hpk eG eKR (inputH P hpk eG eKR i Hq)) m = c' := by
      rwa [encOf_inputH]
    rw [dif_neg h', if_neg h]

omit [DecidableEq Hash] in
/-- The ciphertext map is injective on the slice exactly when the ciphertext map
of `kemTab i` is injective. -/
theorem kemInj_iff [DecidableEq Hash] (i : KEMInput PK SK Z M K m₁ m₂ n) :
    kemInj P hpk eG eKR i ↔ Function.Injective (encOf (P.enc i.1.1) (kemTab hpk eG eKR i)) := by
  have hct : ∀ m, coinCt (kemEncAt P eG i.1.1) eKR.symm i.2.2.2.2.1 (eG (m, hpk i.1.1)) =
      encOf (P.enc i.1.1) (kemTab hpk eG eKR i) m := fun m => by
    simp [coinCt, kemEncAt, encOf, encAt, coinsOf, kemTab, kemG]
  constructor
  · intro h m m' hmm
    have := h (eG (m, hpk i.1.1)) (eG (m', hpk i.1.1)) (by simp [kemSlice])
      (by simp [kemSlice]) (by rw [hct, hct]; exact hmm)
    exact congrArg Prod.fst (eG.injective this)
  · intro h x y hx hy hxy
    have ex : x = eG ((eG.symm x).1, hpk i.1.1) := by
      rw [← hx, Prod.mk.eta, Equiv.apply_symm_apply]
    have ey : y = eG ((eG.symm y).1, hpk i.1.1) := by
      rw [← hy, Prod.mk.eta, Equiv.apply_symm_apply]
    rw [ex, ey, hct, hct] at hxy
    rw [ex, ey, h hxy]

theorem kemInj_inputH (i : KEMInput PK SK Z M K m₁ m₂ n) (Hq : C → K) :
    kemInj P hpk eG eKR (inputH P hpk eG eKR i Hq) ↔ kemInj P hpk eG eKR i :=
  sliceInj_keyHop _ _ _ Hq _

/-- The exchange `keySwapCt` on the `G`-table of an input and `Hq`, at the slice
of the input's public key. -/
def kemSwapH (p : KEMInput PK SK Z M K m₁ m₂ n × (C → K)) :
    KEMInput PK SK Z M K m₁ m₂ n × (C → K) :=
  ((p.1.1, p.1.2.1, p.1.2.2.1, p.1.2.2.2.1,
      (keySwapCt (kemSlice hpk eG p.1.1.1) (kemEncAt P eG p.1.1.1) eKR.symm
        (p.1.2.2.2.2.1, p.2)).1, p.1.2.2.2.2.2),
    (keySwapCt (kemSlice hpk eG p.1.1.1) (kemEncAt P eG p.1.1.1) eKR.symm
        (p.1.2.2.2.2.1, p.2)).2)

theorem kemSwapH_involutive : Function.Involutive (kemSwapH P hpk eG eKR (Z := Z) (m₂ := m₂)) := by
  rintro ⟨⟨ks, z, m, kf, g, j⟩, Hq⟩
  simp only [kemSwapH, Prod.mk.eta, keySwapCt_involutive _ _ _ (g, Hq)]

theorem kemSwapH_fst_of_inj {i : KEMInput PK SK Z M K m₁ m₂ n} (Hq : C → K)
    (h : kemInj P hpk eG eKR i) : (kemSwapH P hpk eG eKR (i, Hq)).1 = inputH P hpk eG eKR i Hq := by
  simp only [kemSwapH, keySwapCt_of_inj _ _ _ (p := (i.2.2.2.2.1, Hq)) h, inputH]

theorem kemInj_kemSwapH (p : KEMInput PK SK Z M K m₁ m₂ n × (C → K)) :
    kemInj P hpk eG eKR (kemSwapH P hpk eG eKR p).1 ↔ kemInj P hpk eG eKR p.1 := by
  by_cases h : kemInj P hpk eG eKR p.1
  · rw [show p = (p.1, p.2) from rfl, kemSwapH_fst_of_inj P hpk eG eKR p.2 h, kemInj_inputH]
  · have he : keySwapCt (kemSlice hpk eG p.1.1.1) (kemEncAt P eG p.1.1.1) eKR.symm
        (p.1.2.2.2.2.1, p.2) = (p.1.2.2.2.2.1, p.2) := keySwapCt_of_not_inj _ _ _ h
    simp only [kemSwapH, he]

variable [Fintype PK] [Fintype SK] [Fintype M] [Fintype Z] [Fintype K] [Fintype C] [DecidableEq C]

open scoped Classical in
/-- The relabelling on the KEM input: over the inputs whose ciphertext map is
injective, the hopped input under an independent uniform `Hq` has the law of
the input. -/
theorem sum_inputH (Φ : KEMInput PK SK Z M K m₁ m₂ n → ℝ≥0∞) :
    ∑ i : KEMInput PK SK Z M K m₁ m₂ n, ∑ Hq : C → K,
        kemSample P i * (if kemInj P hpk eG eKR i then Φ (inputH P hpk eG eKR i Hq) else 0) =
      ∑ i : KEMInput PK SK Z M K m₁ m₂ n, ∑ _Hq : C → K,
        kemSample P i * (if kemInj P hpk eG eKR i then Φ i else 0) := by
  classical
  rw [← Fintype.sum_prod_type' (f := fun i Hq =>
      kemSample P i * (if kemInj P hpk eG eKR i then Φ (inputH P hpk eG eKR i Hq) else 0)),
    ← Fintype.sum_prod_type' (f := fun i (_ : C → K) =>
      kemSample P i * (if kemInj P hpk eG eKR i then Φ i else 0))]
  refine Fintype.sum_equiv ((kemSwapH_involutive P hpk eG eKR).toPerm _) _ _ fun p => ?_
  change _ = kemSample P (kemSwapH P hpk eG eKR p).1 *
    (if kemInj P hpk eG eKR (kemSwapH P hpk eG eKR p).1 then Φ (kemSwapH P hpk eG eKR p).1 else 0)
  have hw : kemSample P (kemSwapH P hpk eG eKR p).1 = kemSample P p.1 := rfl
  rw [hw]
  by_cases h : kemInj P hpk eG eKR p.1
  · rw [if_pos h, if_pos ((kemInj_kemSwapH P hpk eG eKR p).2 h),
      show p = (p.1, p.2) from rfl, kemSwapH_fst_of_inj P hpk eG eKR p.2 h]
  · rw [if_neg h, if_neg (fun h' => h ((kemInj_kemSwapH P hpk eG eKR p).1 h'))]

end Input

/-! ## The hopped game -/

section Game

variable {m₁ m₂ n w q k c a : ℕ} {PK SK M C R K Hash Z : Type} [DecidableEq Hash] [Nonempty K]
  [DecidableEq C] (P : Scheme PK SK M C R) (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁)
  (eJ : (Z × C) ≃ Fin m₂) (eKR : (K × R) ≃ Fin n) (eC : C ≃ Fin c) (eKa : K ≃ Fin a)

/-- The simulated decapsulation of the hopped input. -/
def decapsH (i : KEMInput PK SK Z M K m₁ m₂ n) (Hq : C → K) : Fin c → Fin a :=
  decapsSim P hpk eG eJ eKR eC eKa (inputH P hpk eG eKR i Hq)

open scoped Classical in
/-- Off the challenge ciphertext, the hopped decapsulation answers `Hq c` at a
ciphertext of a message and the rejection key of `J` elsewhere. -/
theorem decapsH_apply (i : KEMInput PK SK Z M K m₁ m₂ n) (Hq : C → K) (x : Fin c)
    (hx : eC.symm x ≠ kemChal P hpk eG eKR i) :
    decapsH P hpk eG eJ eKR eC eKa i Hq x =
      eKa ((if ∃ m, encOf (P.enc i.1.1) (kemTab hpk eG eKR i) m = eC.symm x then
        some (Hq (eC.symm x)) else none).getD (kemJ eJ eKR i (i.2.1, eC.symm x))) := by
  simp only [decapsH, decapsSim]
  rw [kemChal_inputH, if_neg hx]
  change eKa ((simKeyAt (P.enc i.1.1) (kemTab hpk eG eKR (inputH P hpk eG eKR i Hq))
    (eC.symm x)).getD (kemJ eJ eKR i (i.2.1, eC.symm x))) = _
  rw [simKeyAt_inputH]

/-- At a ciphertext of a message other than the challenge ciphertext, the hopped
decapsulation answers `Hq` at that ciphertext. -/
theorem decapsH_of_encOf (i : KEMInput PK SK Z M K m₁ m₂ n) (Hq : C → K) (m : M)
    (hm : encOf (P.enc i.1.1) (kemTab hpk eG eKR i) m ≠ kemChal P hpk eG eKR i) :
    decapsH P hpk eG eJ eKR eC eKa i Hq (eC (encOf (P.enc i.1.1) (kemTab hpk eG eKR i) m)) =
      eKa (Hq (encOf (P.enc i.1.1) (kemTab hpk eG eKR i) m)) := by
  classical
  rw [decapsH_apply P hpk eG eJ eKR eC eKa i Hq _ (by simpa using hm)]
  simp

omit [DecidableEq Hash] in
/-- The decapsulation function that answers every ciphertext other than `cstar`
by the table `H`: it reads `H` and `cstar` only. -/
def decapsHq (H : C → K) (cstar : C) : Fin c → Fin a :=
  fun x => if eC.symm x = cstar then eKa (Classical.arbitrary K) else eKa (H (eC.symm x))

open scoped Classical in
/-- The hopped decapsulation is `decapsHq` at the table that is `Hq` on the
ciphertexts of the messages and the rejection table `J(z, ·)` elsewhere. -/
theorem decapsH_eq_decapsHq (i : KEMInput PK SK Z M K m₁ m₂ n) (Hq : C → K) :
    decapsH P hpk eG eJ eKR eC eKa i Hq =
      decapsHq eC eKa (mergeOn (fun y => ∃ m, encOf (P.enc i.1.1) (kemTab hpk eG eKR i) m = y)
        Hq (fun y => kemJ eJ eKR i (i.2.1, y))) (kemChal P hpk eG eKR i) := by
  funext x
  by_cases hx : eC.symm x = kemChal P hpk eG eKR i
  · simp only [decapsH, decapsSim, decapsHq, kemChal_inputH, if_pos hx]
  · rw [decapsH_apply P hpk eG eJ eKR eC eKa i Hq x hx]
    simp only [decapsHq, if_neg hx, mergeOn]
    split_ifs <;> rfl

variable [Fintype PK] [Fintype SK] [Fintype M] [Fintype Z] [Fintype K] [Fintype C] [NeZero n]

/-- The probability that `A` outputs `1` in the hopped game with bit `b`: the
input and an independent uniform `Hq : C → K` are drawn, and the game with
simulated decapsulation is run on the hopped input. -/
def prWinKEMH (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool) : ℝ≥0∞ :=
  ∑ i : KEMInput PK SK Z M K m₁ m₂ n, ∑ Hq : C → K,
    kemSample P i * (Fintype.card (C → K) : ℝ≥0∞)⁻¹ *
      prOutMR (A.run i.1.1 (kemChal P hpk eG eKR (inputH P hpk eG eKR i Hq))
        (kemKey hpk eG eKR (inputH P hpk eG eKR i Hq) b)) (kemOracleH P hpk eG eKR i Hq)
        (decapsH P hpk eG eJ eKR eC eKa i Hq)

open scoped Classical in
/-- The hop to keys drawn from ciphertexts: the hopped game and the game with
simulated decapsulation differ by at most the weight of the inputs whose
ciphertext map is not injective. -/
theorem hopH (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool) :
    absDiff (prWinKEMH P hpk eG eJ eKR eC eKa A b) (prWinKEMSim P hpk eG eJ eKR eC eKa A b) ≤
      ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i *
        (if Function.Injective (encOf (P.enc i.1.1) (kemTab hpk eG eKR i)) then 0 else 1) := by
  set κ : ℝ≥0∞ := (Fintype.card (C → K) : ℝ≥0∞)⁻¹ with hκ
  have hκsum : ∀ t : ℝ≥0∞, ∑ _Hq : C → K, κ * t = t := by
    intro t
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, hκ,
      ENNReal.mul_inv_cancel (by exact_mod_cast Fintype.card_ne_zero) (ENNReal.natCast_ne_top _),
      one_mul]
  set Φ : KEMInput PK SK Z M K m₁ m₂ n → ℝ≥0∞ := fun j =>
    prOutMR (A.run j.1.1 (kemChal P hpk eG eKR j) (kemKey hpk eG eKR j b)) (kemOracle j)
      (decapsSim P hpk eG eJ eKR eC eKa j) with hΦ
  set I : KEMInput PK SK Z M K m₁ m₂ n → Prop := kemInj P hpk eG eKR with hI
  have hcost : ∀ i : KEMInput PK SK Z M K m₁ m₂ n,
      (if Function.Injective (encOf (P.enc i.1.1) (kemTab hpk eG eKR i)) then (0 : ℝ≥0∞) else 1) =
        if I i then 0 else 1 := fun i => by
    rw [hI]; exact if_congr (kemInj_iff P hpk eG eKR i).symm rfl rfl
  simp only [hcost]
  set D := ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * (if I i then 0 else 1)
  have hsplit : ∀ (p : Prop) [Decidable p] (x : ℝ≥0∞),
      x = (if p then x else 0) + (if p then 0 else x) := by
    intro p _ x; split_ifs <;> simp
  set A0 := ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * (if I i then Φ i else 0)
  have hH : prWinKEMH P hpk eG eJ eKR eC eKa A b =
      A0 + ∑ i : KEMInput PK SK Z M K m₁ m₂ n, ∑ Hq : C → K,
        kemSample P i * (if I i then 0 else κ * Φ (inputH P hpk eG eKR i Hq)) := by
    have hA := sum_inputH P hpk eG eKR (fun j => κ * Φ j)
    have hA' : ∑ i : KEMInput PK SK Z M K m₁ m₂ n, ∑ _Hq : C → K,
        kemSample P i * (if I i then κ * Φ i else 0) = A0 := by
      refine Finset.sum_congr rfl fun i _ => ?_
      have : kemSample P i * (if I i then κ * Φ i else 0) =
          κ * (kemSample P i * (if I i then Φ i else 0)) := by
        split_ifs <;> ring
      rw [Finset.sum_congr rfl fun (_ : C → K) _ => this, hκsum]
    rw [← hA', ← hA, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun Hq _ => ?_
    rw [← mul_add, ← hsplit, mul_assoc]
    rfl
  have hS : prWinKEMSim P hpk eG eJ eKR eC eKa A b =
      A0 + ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * (if I i then 0 else Φ i) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_add, ← hsplit]
  have hB1 : ∑ i : KEMInput PK SK Z M K m₁ m₂ n, ∑ Hq : C → K,
      kemSample P i * (if I i then 0 else κ * Φ (inputH P hpk eG eKR i Hq)) ≤ D := by
    refine Finset.sum_le_sum fun i _ => ?_
    calc ∑ Hq : C → K, kemSample P i * (if I i then 0 else κ * Φ (inputH P hpk eG eKR i Hq))
        ≤ ∑ _Hq : C → K, κ * (kemSample P i * (if I i then 0 else 1)) := by
          refine Finset.sum_le_sum fun Hq _ => ?_
          split_ifs
          · simp
          · rw [mul_one, mul_left_comm]
            gcongr
            exact mul_le_of_le_one_right' (prOutMR_le_one _ _ _)
      _ = kemSample P i * (if I i then 0 else 1) := hκsum _
  have hB2 : ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i * (if I i then 0 else Φ i) ≤ D := by
    refine Finset.sum_le_sum fun i _ => ?_
    split_ifs
    · simp
    · gcongr; exact prOutMR_le_one _ _ _
  rw [hH, hS]
  refine absDiff_le_iff.mpr ⟨?_, ?_⟩
  · calc _ ≤ A0 + D := add_le_add le_rfl hB1
      _ ≤ _ := by rw [add_assoc]; exact add_le_add le_rfl le_add_self
  · calc _ ≤ A0 + D := add_le_add le_rfl hB2
      _ ≤ _ := by rw [add_assoc]; exact add_le_add le_rfl le_add_self

omit [DecidableEq Hash] [Nonempty K] [Fintype PK] [Fintype SK] [Fintype Z] [Fintype K]
  [Fintype C] [NeZero n] in
open scoped Classical in
/-- The cost of `hopH` is at most the decryption-failure weight of `hopD`. -/
theorem hopH_cost_le (i : KEMInput PK SK Z M K m₁ m₂ n) :
    (if Function.Injective (encOf (P.enc i.1.1) (kemTab hpk eG eKR i)) then (0 : ℝ≥0∞) else 1) ≤
      if ∀ m, m ∈ kemGood P hpk eG eKR i then 0 else 1 := by
  by_cases hg : ∀ m, m ∈ kemGood P hpk eG eKR i
  · have hinj : Function.Injective (encOf (P.enc i.1.1) (kemTab hpk eG eKR i)) :=
      encAt_injective_of_good_eq_univ (P.enc i.1.1) (P.dec i.1.2) _
        (Finset.eq_univ_iff_forall.mpr hg)
    rw [if_pos hinj, if_pos hg]
  · rw [if_neg hg]
    split_ifs <;> simp

end Game

end CatCrypt.Quantum.QROM
