/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.ENNReal.Basic
public import Mathlib.Logic.Equiv.Basic

/-!
# Re-indexing a key table by ciphertexts

The change of oracle variables of the U-step of the Fujisaki–Okamoto
transformation: a key table indexed by messages is carried to a key table
indexed by the ciphertexts of those messages. The map sending a message to its
ciphertext under a fixed coin table is injective on the messages the decryption
map recovers from their own ciphertext, so on that part it induces a bijection
of key tables, and the uniform average over key tables is unchanged.

## Main definitions

* `coinsOf T` — the coin component of a key-and-coin table `T : M → Key × Coin`
* `encAt enc r m` — the ciphertext `enc m (r m)` of `m` under the coin table `r`
* `encOf enc T m` — the ciphertext map induced by a key-and-coin table
* `Good enc dec r` — the messages `m` with `dec (encAt enc r m) = some m`
* `keyAt enc dec T c` — the key stored at the ciphertext `c`: `some (T m).1` when
  `dec c = some m` and `m` has ciphertext `c`, and `none` otherwise
* `goodToCt enc dec r` — the ciphertext map as a map from the good messages to
  their ciphertexts
* `goodCtEquiv enc dec r` — that map as an `Equiv`
* `keyTabEquiv enc dec r` — the induced bijection between key tables indexed by
  good messages and key tables indexed by their ciphertexts

## Main results

* `encAt_injOn_good`, `encOf_injOn_good` — the ciphertext map is injective on
  the good messages
* `encAt_injective_of_good_eq_univ` — the failure-free case: when every message
  is good the ciphertext map is injective
* `keyAt_encOf` — at the ciphertext of a good message the stored key is that
  message's key
* `keyAt_eq_none_of_not_mem_image` — off the ciphertexts of the good messages no
  key is stored
* `goodToCt_bijective` — the ciphertext map is a bijection from the good
  messages onto their image
* `sum_reindex_keyTab` — a sum over key tables is unchanged by precomposition
  with a permutation of the messages
* `sum_reindex_goodKeyTab` — a sum over key tables indexed by good messages is
  the sum over key tables indexed by their ciphertexts
* `prob_not_good_le` — the weight of the messages outside `Good` is the
  correctness error of the scheme

## Use

The statements are over an abstract encryption map `enc` and partial inverse
`dec`, so they apply to the classical and the quantum game alike. `HopDecaps`
applies them to the decapsulation hop.

## References

* [Saito, Xagawa, Yamakawa — Tightly-Secure Key-Encapsulation Mechanism in the
  Quantum Random Oracle Model, EUROCRYPT 2018]
* [Jiang, Zhang, Chen, Wang, Ma — IND-CCA-Secure Key Encapsulation Mechanism in
  the Quantum Random Oracle Model, Revisited, CRYPTO 2018]
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal

namespace CatCrypt.Quantum.QROM

section ChangeOfVariables

variable {M C Key Coin : Type}
variable [Fintype M] [DecidableEq M] [Fintype C] [DecidableEq C]
variable [Fintype Key] [DecidableEq Key] [Fintype Coin] [DecidableEq Coin]

/-- The coin component of a key-and-coin table. -/
def coinsOf (T : M → Key × Coin) : M → Coin := fun m => (T m).2

/-- The ciphertext of the message `m` under the coin table `r`. -/
def encAt (enc : M → Coin → C) (r : M → Coin) (m : M) : C := enc m (r m)

/-- The ciphertext map induced by a key-and-coin table. -/
def encOf (enc : M → Coin → C) (T : M → Key × Coin) (m : M) : C :=
  encAt enc (coinsOf T) m

omit [Fintype M] [DecidableEq M] [Fintype C] [DecidableEq C] [Fintype Key]
  [DecidableEq Key] [Fintype Coin] [DecidableEq Coin] in
theorem encOf_eq (enc : M → Coin → C) (T : M → Key × Coin) :
    encOf enc T = encAt enc (coinsOf T) := rfl

/-- The messages that the partial inverse `dec` recovers from their own
ciphertext under the coin table `r`. -/
def Good (enc : M → Coin → C) (dec : C → Option M) (r : M → Coin) : Finset M :=
  Finset.univ.filter fun m => dec (encAt enc r m) = some m

omit [Fintype C] [DecidableEq C] [Fintype Coin] [DecidableEq Coin] in
theorem mem_good_iff (enc : M → Coin → C) (dec : C → Option M) (r : M → Coin)
    (m : M) : m ∈ Good enc dec r ↔ dec (encAt enc r m) = some m := by
  simp [Good]

/-! ### Injectivity on the good messages -/

omit [Fintype C] [DecidableEq C] [Fintype Coin] [DecidableEq Coin] in
/-- The ciphertext map is injective on the messages the decryption map recovers
from their own ciphertext. -/
theorem encAt_injOn_good (enc : M → Coin → C) (dec : C → Option M)
    (r : M → Coin) : Set.InjOn (encAt enc r) (Good enc dec r : Set M) := by
  intro m hm m' hm' h
  rw [Finset.mem_coe, mem_good_iff] at hm hm'
  have : some m = some m' := by rw [← hm, h, hm']
  exact Option.some_injective _ this

omit [Fintype C] [DecidableEq C] [Fintype Key] [DecidableEq Key] [Fintype Coin]
  [DecidableEq Coin] in
/-- The ciphertext map of a key-and-coin table is injective on the good
messages. -/
theorem encOf_injOn_good (enc : M → Coin → C) (dec : C → Option M)
    (T : M → Key × Coin) :
    Set.InjOn (encOf enc T) (Good enc dec (coinsOf T) : Set M) :=
  encAt_injOn_good enc dec (coinsOf T)

omit [Fintype C] [DecidableEq C] [Fintype Coin] [DecidableEq Coin] in
/-- When every message is good the ciphertext map is injective. -/
theorem encAt_injective_of_good_eq_univ (enc : M → Coin → C)
    (dec : C → Option M) (r : M → Coin) (h : Good enc dec r = Finset.univ) :
    Function.Injective (encAt enc r) := fun a b hab =>
  encAt_injOn_good enc dec r (by simp [h]) (by simp [h]) hab

/-! ### The key table indexed by ciphertexts -/

/-- The key stored at a ciphertext: the key of the message the decryption map
returns, when that message has the given ciphertext. -/
def keyAt (enc : M → Coin → C) (dec : C → Option M) (T : M → Key × Coin)
    (c : C) : Option Key :=
  (dec c).bind fun m => if encOf enc T m = c then some (T m).1 else none

omit [Fintype C] [Fintype Key] [DecidableEq Key] [Fintype Coin]
  [DecidableEq Coin] in
/-- At the ciphertext of a good message the stored key is that message's key. -/
theorem keyAt_encOf {enc : M → Coin → C} {dec : C → Option M}
    {T : M → Key × Coin} {m : M} (hm : m ∈ Good enc dec (coinsOf T)) :
    keyAt enc dec T (encOf enc T m) = some (T m).1 := by
  have h : dec (encOf enc T m) = some m := (mem_good_iff enc dec _ m).1 hm
  simp [keyAt, h]

omit [Fintype C] [Fintype Key] [DecidableEq Key] [Fintype Coin]
  [DecidableEq Coin] in
/-- Off the ciphertexts of the good messages no key is stored. -/
theorem keyAt_eq_none_of_not_mem_image {enc : M → Coin → C}
    {dec : C → Option M} {T : M → Key × Coin} {c : C}
    (hc : c ∉ (Good enc dec (coinsOf T)).image (encOf enc T)) :
    keyAt enc dec T c = none := by
  unfold keyAt
  cases hd : dec c with
  | none => simp
  | some m =>
    simp only [Option.bind_some]
    by_cases h : encOf enc T m = c
    · exact absurd (Finset.mem_image.2
        ⟨m, (mem_good_iff enc dec _ m).2 (by rw [encOf_eq] at h; rw [h]; exact hd), h⟩) hc
    · simp [h]

/-! ### The bijection of key tables -/

/-- The ciphertext map as a map from the good messages to their ciphertexts. -/
def goodToCt (enc : M → Coin → C) (dec : C → Option M) (r : M → Coin)
    (m : {m : M // m ∈ Good enc dec r}) :
    {c : C // c ∈ (Good enc dec r).image (encAt enc r)} :=
  ⟨encAt enc r m.1, Finset.mem_image_of_mem _ m.2⟩

omit [Fintype C] [Fintype Coin] [DecidableEq Coin] in
/-- The ciphertext map is a bijection from the good messages onto their
image. -/
theorem goodToCt_bijective (enc : M → Coin → C) (dec : C → Option M)
    (r : M → Coin) : Function.Bijective (goodToCt enc dec r) := by
  constructor
  · intro a b h
    exact Subtype.ext (encAt_injOn_good enc dec r (Finset.mem_coe.2 a.2)
      (Finset.mem_coe.2 b.2) (congrArg Subtype.val h))
  · rintro ⟨c, hc⟩
    obtain ⟨m, hm, hmc⟩ := Finset.mem_image.1 hc
    exact ⟨⟨m, hm⟩, Subtype.ext hmc⟩

/-- The ciphertext map as a bijection from the good messages onto their
image. -/
noncomputable def goodCtEquiv (enc : M → Coin → C) (dec : C → Option M)
    (r : M → Coin) :
    {m : M // m ∈ Good enc dec r} ≃
      {c : C // c ∈ (Good enc dec r).image (encAt enc r)} :=
  Equiv.ofBijective _ (goodToCt_bijective enc dec r)

/-- Key tables indexed by the good messages and key tables indexed by their
ciphertexts are in bijection. -/
noncomputable def keyTabEquiv (enc : M → Coin → C) (dec : C → Option M)
    (r : M → Coin) :
    ({m : M // m ∈ Good enc dec r} → Key) ≃
      ({c : C // c ∈ (Good enc dec r).image (encAt enc r)} → Key) :=
  Equiv.arrowCongr (goodCtEquiv enc dec r) (Equiv.refl Key)

omit [DecidableEq Key] in
/-- A sum over key tables is unchanged by precomposition with a permutation of
the messages. -/
theorem sum_reindex_keyTab (σ : M ≃ M) (F : (M → Key) → ℝ≥0∞) :
    ∑ k : M → Key, F k = ∑ k : M → Key, F (k ∘ σ) :=
  (Fintype.sum_equiv (Equiv.arrowCongr σ.symm (Equiv.refl Key))
    (fun k => F (k ∘ σ)) F fun _ => rfl).symm

omit [Fintype C] [DecidableEq Key] [Fintype Coin] [DecidableEq Coin] in
/-- A sum over key tables indexed by the good messages is the sum over key
tables indexed by their ciphertexts. -/
theorem sum_reindex_goodKeyTab (enc : M → Coin → C) (dec : C → Option M)
    (r : M → Coin)
    (F : ({c : C // c ∈ (Good enc dec r).image (encAt enc r)} → Key) → ℝ≥0∞) :
    ∑ k : {m : M // m ∈ Good enc dec r} → Key, F (keyTabEquiv enc dec r k)
      = ∑ k' : {c : C // c ∈ (Good enc dec r).image (encAt enc r)} → Key, F k' :=
  Equiv.sum_comp (keyTabEquiv enc dec r) F

/-! ### The weight of the failure set -/

omit [Fintype C] [DecidableEq C] [DecidableEq Key] [DecidableEq Coin] in
/-- The weight of the messages outside `Good` is the weight of the messages the
decryption map does not recover from their own ciphertext. -/
theorem prob_not_good_le (enc : M → Coin → C) (dec : C → Option M)
    (μ : (M → Key × Coin) → ℝ≥0∞) (δ : ℝ≥0∞)
    (hδ : ∀ m : M, ∑ T : M → Key × Coin,
        μ T * (if dec (encOf enc T m) = some m then 0 else 1) ≤ δ) :
    ∀ m : M, ∑ T : M → Key × Coin,
      μ T * (if m ∈ Good enc dec (coinsOf T) then 0 else 1) ≤ δ := by
  intro m
  refine le_trans (le_of_eq (Finset.sum_congr rfl fun T _ => ?_)) (hδ m)
  exact congrArg (μ T * ·) (if_congr (by rw [mem_good_iff, encOf_eq]) rfl rfl)

end ChangeOfVariables

end CatCrypt.Quantum.QROM
