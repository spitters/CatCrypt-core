/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.MLKEM.MLKEM512Params

/-!
# The law of the FIPS 203 centered-binomial sampler

## Main definitions

* `bitOf`, `bitB` — the bit of a byte list at a global little-endian bit index
* `countOnes` — the number of `true` entries of a Boolean vector
* `Win`, `windowOf`, `windowVal`, `windowMap` — the two `η`-bit halves that FIPS 203
  Algorithm 8 reads for one coefficient, their centered-binomial value, and the 256
  windows of a PRF block

## Main results

* `bitsLE_getD` — a defaulted read of `Sampler.bitsLE` is `bitOf`
* `cbdCoeff_eq_windowVal` — the coefficient of Algorithm 8 is the value of its window
* `uniform_pi` — a uniform function on `Fin n` is `n` independent uniform draws
* `uniform_countOnes` — the weight of a uniform Boolean vector of length `n` has the
  law `CatCrypt.NonUniform.binom n`
* `uniform_windowVal` — the value of a uniform window has the law
  `CatCrypt.NonUniform.cbd η`
* `replicateFin_map` — a componentwise map of an independent product is the product
  of the mapped law
* `windowMap_bijective` — the 256 windows of a PRF block determine it and exhaust the
  window space
* `samplerIsCbd` — `MLKEM512Instance.SamplerIsCbd η` for every `η > 0`
* `samplerIsCbd_two`, `samplerIsCbd_three` — the same at the two ML-KEM parameters

## Scope

`samplerIsCbd` holds for every positive `η`; at `η = 0` the window indexing divides
by zero and the statement is not covered. Nothing is left open at `η = 2` and
`η = 3`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.MLKEM.SamplerCbd

open CatCrypt.Crypto.MLKEM CatCrypt.Util

/-! ## Bit access on a byte list -/

/-- The bit of a byte list at global little-endian bit index `k`: bit `k % 8` of
byte `k / 8`, with `0` past the end of the list. -/
def bitOf (l : List UInt8) (k : Nat) : Nat :=
  ((l.getD (k / 8) 0).toNat >>> (k % 8)) &&& 1

/-- A defaulted read of `Sampler.bitsLE` is the bit at that global index. -/
theorem bitsLE_getD (l : List UInt8) (k : Nat) :
    (Sampler.bitsLE l).getD k 0 = bitOf l k := by
  induction l generalizing k with
  | nil => simp [Sampler.bitsLE, bitOf, List.getD]
  | cons b rest ih =>
    have hsplit : Sampler.bitsLE (b :: rest) =
        ((List.range 8).map (fun j => (b.toNat >>> j) &&& 1)) ++ Sampler.bitsLE rest := by
      simp [Sampler.bitsLE]
    have hlen : ((List.range 8).map (fun j => (b.toNat >>> j) &&& 1)).length = 8 := by simp
    rw [hsplit]
    by_cases hk : k < 8
    · have h8 : k / 8 = 0 := Nat.div_eq_of_lt hk
      have hm : k % 8 = k := Nat.mod_eq_of_lt hk
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_append_left (by omega : k < ((List.range 8).map
          (fun j => (b.toNat >>> j) &&& 1)).length)]
      simp [bitOf, h8, hm, hk]
    · have hge : 8 ≤ k := by omega
      have hd : (k - 8) / 8 = k / 8 - 1 := by omega
      have hmm : (k - 8) % 8 = k % 8 := by omega
      have hpos : 0 < k / 8 := by omega
      rw [List.getD_eq_getElem?_getD,
        List.getElem?_append_right (by omega : ((List.range 8).map
          (fun j => (b.toNat >>> j) &&& 1)).length ≤ k), hlen,
        ← List.getD_eq_getElem?_getD, ih]
      unfold bitOf
      rw [hd, hmm]
      congr 2
      rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD]
      obtain ⟨m, hm'⟩ : ∃ m, k / 8 = m + 1 := ⟨k / 8 - 1, by omega⟩
      rw [hm']
      simp

/-- The bit of a byte list at global little-endian bit index `k`, as a `Bool`. -/
def bitB (l : List UInt8) (k : Nat) : Bool :=
  Nat.testBit (l.getD (k / 8) 0).toNat (k % 8)

theorem shift_and_one (x j : Nat) :
    (x >>> j) &&& 1 = if Nat.testBit x j then 1 else 0 := by
  rcases Nat.mod_two_eq_zero_or_one (x >>> j) with h | h <;>
    simp [Nat.testBit, Nat.and_one_is_mod, h]

theorem bitOf_eq (l : List UInt8) (k : Nat) :
    bitOf l k = if bitB l k then 1 else 0 := by
  rw [bitOf, bitB, shift_and_one]

/-! ## Windows -/

/-- The number of `true` entries of a Boolean vector. -/
def countOnes {n : Nat} (w : Fin n → Bool) : Nat := ∑ j, if w j then 1 else 0

/-- The centered-binomial value of a window: the count of the first half minus the
count of the second half. -/
def windowVal {η : Nat} (w : (Fin η → Bool) × (Fin η → Bool)) : Int :=
  (countOnes w.1 : Int) - (countOnes w.2 : Int)

/-- The two halves of the bit window that FIPS 203 Algorithm 8 reads for the
coefficient of index `i`. -/
def windowOf (η : Nat) (l : List UInt8) (i : Nat) : (Fin η → Bool) × (Fin η → Bool) :=
  (fun j => bitB l (2 * η * i + j.val), fun j => bitB l (2 * η * i + η + j.val))

theorem list_range_map_sum (f : Nat → Nat) (n : Nat) :
    ((List.range n).map f).sum = ∑ j ∈ Finset.range n, f j := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]
    simp

theorem sumBits_eq_countOnes (l : List UInt8) (start len : Nat) :
    Sampler.sumBits (Sampler.bitsLE l) start len
      = countOnes (fun j : Fin len => bitB l (start + j.val)) := by
  rw [Sampler.sumBits, list_range_map_sum, countOnes,
    Fin.sum_univ_eq_sum_range (fun j => if bitB l (start + j) then 1 else 0) len]
  exact Finset.sum_congr rfl fun j _ => by rw [bitsLE_getD, bitOf_eq]

theorem cbdCoeff_eq_windowVal (η : Nat) (l : List UInt8) (i : Nat) :
    Sampler.cbdCoeff η (Sampler.bitsLE l) i = windowVal (windowOf η l i) := by
  simp [Sampler.cbdCoeff, windowVal, windowOf, sumBits_eq_countOnes]

/-! ## Uniform distributions on function types -/

open CatCrypt.Prob CatCrypt.NonUniform

/-- On a type with one element the uniform distribution is the point mass. -/
theorem uniform_of_subsingleton {β : Type} [Fintype β] [Nonempty β] [Subsingleton β]
    (b : β) : SDistr.uniform β = SDistr.pure b := by
  have hcard : Fintype.card β = 1 :=
    Fintype.card_eq_one_iff.mpr ⟨b, fun a => Subsingleton.elim a b⟩
  apply PMF.ext
  intro o
  cases o with
  | none => rw [SDistr.uniform_apply_none]; simp [SDistr.pure]
  | some a =>
    rw [SDistr.uniform_apply_some, hcard]
    simp [SDistr.pure, Subsingleton.elim a b]

/-- The uniform distribution on `Fin n → α` is `n` independent uniform draws. -/
theorem uniform_pi (α : Type) [Fintype α] [Nonempty α] :
    ∀ n : Nat, SDistr.uniform (Fin n → α) = replicateFin n (SDistr.uniform α)
  | 0 => by
    rw [replicateFin, piFin_zero]
    exact uniform_of_subsingleton _
  | n + 1 => by
    have ih := uniform_pi α n
    have happ : ∀ p : α × (Fin n → α),
        Fin.consEquiv (fun _ : Fin (n + 1) => α) p = Fin.cons p.1 p.2 := fun _ => rfl
    calc SDistr.uniform (Fin (n + 1) → α)
        = (SDistr.uniform (α × (Fin n → α))).bind
            (fun p => SDistr.pure (Fin.consEquiv (fun _ : Fin (n + 1) => α) p)) :=
          (SDistr.uniform_bind_bij _).symm
      _ = replicateFin (n + 1) (SDistr.uniform α) := by
          rw [← SDistr.uniform_nested_eq_prod, replicateFin, piFin_succ, ← replicateFin, ← ih]
          simp only [SDistr.bind_assoc, SDistr.pure_bind, happ]

/-! ## One window -/

theorem countOnes_cons {n : Nat} (a : Bool) (f : Fin n → Bool) :
    countOnes (Fin.cons a f : Fin (n + 1) → Bool)
      = (if a then 1 else 0) + countOnes f := by
  rw [countOnes, countOnes, Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]

/-- The number of ones in a uniform Boolean vector of length `n` is distributed as
`binom n`. -/
theorem uniform_countOnes :
    ∀ n : Nat, (SDistr.uniform (Fin n → Bool)).bind (fun w => SDistr.pure (countOnes w))
      = binom n
  | 0 => by
    rw [uniform_of_subsingleton (fun i : Fin 0 => i.elim0), SDistr.pure_bind, binom_zero]
    simp [countOnes]
  | n + 1 => by
    have ih := uniform_countOnes n
    rw [uniform_pi, replicateFin, piFin_succ, ← replicateFin, ← uniform_pi]
    rw [binom_succ]
    simp only [SDistr.bind_assoc, SDistr.pure_bind, countOnes_cons]
    have step : ∀ a : Bool,
        ((SDistr.uniform (Fin n → Bool)).bind fun f =>
            SDistr.pure ((if a then 1 else 0) + countOnes f))
          = (binom n).bind fun k => SDistr.pure ((if a then 1 else 0) + k) := fun a => by
      rw [← ih, SDistr.bind_assoc]
      simp only [SDistr.pure_bind]
    have hac : ∀ (a : Bool) (k : Nat),
        (if a = true then 1 else 0) + k = k + (if a = true then 1 else 0) :=
      fun _ _ => Nat.add_comm _ _
    simp only [step]
    simp only [hac]
    exact SDistr.bind_comm (SDistr.uniform Bool) (binom n)
      (fun a k => SDistr.pure (k + (if a = true then 1 else 0)))

/-- A bind along a map factors through the law of that map. -/
theorem bind_of_pushforward {α β γ : Type*} {d : SDistr α} {h : α → β} {d' : SDistr β}
    (hd : d.bind (fun x => SDistr.pure (h x)) = d') (g : β → SDistr γ) :
    d.bind (fun x => g (h x)) = d'.bind g := by
  rw [← hd, SDistr.bind_assoc]
  simp only [SDistr.pure_bind]

/-- The centered-binomial value of a uniform window has the law `cbd η`. -/
theorem uniform_windowVal (η : Nat) :
    (SDistr.uniform ((Fin η → Bool) × (Fin η → Bool))).bind
        (fun w => SDistr.pure (windowVal w)) = cbd η := by
  have inner : ∀ x : Nat,
      ((SDistr.uniform (Fin η → Bool)).bind fun v =>
          SDistr.pure ((x : Int) - (countOnes v : Int)))
        = (binom η).bind fun b => SDistr.pure ((x : Int) - (b : Int)) :=
    fun x => bind_of_pushforward (uniform_countOnes η)
      (fun k => SDistr.pure ((x : Int) - (k : Int)))
  calc (SDistr.uniform ((Fin η → Bool) × (Fin η → Bool))).bind
        (fun w => SDistr.pure (windowVal w))
      = (SDistr.uniform (Fin η → Bool)).bind fun u =>
          (SDistr.uniform (Fin η → Bool)).bind fun v =>
            SDistr.pure ((countOnes u : Int) - (countOnes v : Int)) := by
        rw [← SDistr.uniform_nested_eq_prod]
        simp only [SDistr.bind_assoc, SDistr.pure_bind, windowVal]
    _ = (SDistr.uniform (Fin η → Bool)).bind fun u =>
          (binom η).bind fun b => SDistr.pure ((countOnes u : Int) - (b : Int)) := by
        simp only [inner]
    _ = (binom η).bind fun a =>
          (binom η).bind fun b => SDistr.pure ((a : Int) - (b : Int)) :=
        bind_of_pushforward (uniform_countOnes η)
          (fun k => (binom η).bind fun b => SDistr.pure ((k : Int) - (b : Int)))
    _ = cbd η := rfl

/-! ## Independent products -/

theorem comp_cons {α β : Type*} {n : Nat} (g : α → β) (a : α) (f : Fin n → α) :
    (fun i => g ((Fin.cons a f : Fin (n + 1) → α) i))
      = (Fin.cons (g a) (fun i => g (f i)) : Fin (n + 1) → β) := by
  funext i
  refine Fin.cases ?_ ?_ i <;> simp

theorem replicateFin_zero' {α : Type*} (d : SDistr α) :
    replicateFin 0 d = SDistr.pure (fun i => i.elim0) := rfl

theorem replicateFin_succ' {α : Type*} (n : Nat) (d : SDistr α) :
    replicateFin (n + 1) d
      = d.bind fun a => (replicateFin n d).bind fun f =>
          SDistr.pure (Fin.cons a f : Fin (n + 1) → α) := rfl

/-- Mapping each component of an independent product is the product of the mapped
distribution. -/
theorem replicateFin_map {α β : Type*} (d : SDistr α) (g : α → β) :
    ∀ n : Nat, (replicateFin n d).bind (fun W => SDistr.pure (fun i => g (W i)))
      = replicateFin n (d.bind fun x => SDistr.pure (g x))
  | 0 => by
    rw [replicateFin_zero', replicateFin_zero', SDistr.pure_bind]
    exact congrArg SDistr.pure (funext fun i => i.elim0)
  | n + 1 => by
    have ih := replicateFin_map d g n
    rw [replicateFin_succ', replicateFin_succ']
    simp only [SDistr.bind_assoc, SDistr.pure_bind, comp_cons]
    have inner : ∀ a : α,
        ((replicateFin n d).bind fun f =>
            SDistr.pure (Fin.cons (g a) (fun i => g (f i)) : Fin (n + 1) → β))
          = (replicateFin n (d.bind fun x => SDistr.pure (g x))).bind fun f =>
              SDistr.pure (Fin.cons (g a) f : Fin (n + 1) → β) := fun a => by
      rw [← ih, SDistr.bind_assoc]
      simp only [SDistr.pure_bind]
    simp only [inner]

/-! ## The window decomposition of a PRF block -/

/-- The bit window of one coefficient: two `η`-bit halves. -/
abbrev Win (η : Nat) : Type := (Fin η → Bool) × (Fin η → Bool)

/-- The 256 bit windows of a PRF block. -/
def windowMap (η : Nat) (b : MLKEM512Instance.PrfBlock η) : Fin 256 → Win η :=
  fun i => windowOf η (List.ofFn b) i.val

theorem bitB_ofFn (η : Nat) (b : MLKEM512Instance.PrfBlock η) (m p : Nat)
    (hm : m < 64 * η) (hp : p < 8) :
    bitB (List.ofFn b) (8 * m + p) = Nat.testBit (b ⟨m, hm⟩).toNat p := by
  have hd : (8 * m + p) / 8 = m := by omega
  have hr : (8 * m + p) % 8 = p := by omega
  rw [bitB, hd, hr]
  congr 2
  simp [List.getD_eq_getElem?_getD, hm]

theorem card_uint8 : Fintype.card UInt8 = 256 :=
  (Fintype.card_congr
      ((Equiv.ofBijective UInt8.toBitVec
          ⟨fun _ _ h => UInt8.toBitVec_inj.mp h, fun b => ⟨UInt8.ofBitVec b, rfl⟩⟩).trans
        (Equiv.ofBijective BitVec.toFin
          ⟨fun _ _ h => BitVec.toFin_inj.mp h, fun i => ⟨BitVec.ofFin i, rfl⟩⟩))).trans
    (Fintype.card_fin _)

/-- The windows of a PRF block determine every bit of the block. -/
theorem windowMap_bits (η : Nat) (hη : 0 < η) (b b' : MLKEM512Instance.PrfBlock η)
    (hbb : windowMap η b = windowMap η b') (k : Nat) (hk : k < 512 * η) :
    bitB (List.ofFn b) k = bitB (List.ofFn b') k := by
  have h2 : 0 < 2 * η := by omega
  have hi : k / (2 * η) < 256 := by
    rw [Nat.div_lt_iff_lt_mul h2]; omega
  have hkey : 2 * η * (k / (2 * η)) + k % (2 * η) = k := by
    rw [Nat.mul_comm 2 η, Nat.mul_comm η 2]
    exact Nat.div_add_mod k (2 * η)
  have hr : k % (2 * η) < 2 * η := Nat.mod_lt _ h2
  have hcomp := congrFun hbb ⟨k / (2 * η), hi⟩
  by_cases hlt : k % (2 * η) < η
  · have h1 := congrFun (congrArg Prod.fst hcomp) ⟨k % (2 * η), hlt⟩
    simpa [windowMap, windowOf, hkey] using h1
  · have hj : k % (2 * η) - η < η := by omega
    have h1 := congrFun (congrArg Prod.snd hcomp) ⟨k % (2 * η) - η, hj⟩
    have hsum : 2 * η * (k / (2 * η)) + η + (k % (2 * η) - η) = k := by omega
    simpa [windowMap, windowOf, hsum] using h1

theorem windowMap_injective (η : Nat) (hη : 0 < η) :
    Function.Injective (windowMap η) := by
  intro b b' hbb
  funext m
  have htoNat : (b m).toNat = (b' m).toNat := by
    apply Nat.eq_of_testBit_eq
    intro p
    by_cases hp : p < 8
    · have hk : 8 * m.val + p < 512 * η := by omega
      have := windowMap_bits η hη b b' hbb (8 * m.val + p) hk
      rwa [bitB_ofFn η b m.val p m.isLt hp, bitB_ofFn η b' m.val p m.isLt hp] at this
    · have hpow : (256 : Nat) ≤ 2 ^ p := by
        calc (256 : Nat) = 2 ^ 8 := by norm_num
          _ ≤ 2 ^ p := Nat.pow_le_pow_right (by norm_num) (by omega)
      have hb : (b m).toNat < 2 ^ p := lt_of_lt_of_le (b m).toNat_lt_size hpow
      have hb' : (b' m).toNat < 2 ^ p := lt_of_lt_of_le (b' m).toNat_lt_size hpow
      rw [Nat.testBit_lt_two_pow hb, Nat.testBit_lt_two_pow hb']
  exact UInt8.toNat_inj.mp htoNat

theorem card_window_eq (η : Nat) :
    Fintype.card (MLKEM512Instance.PrfBlock η) = Fintype.card (Fin 256 → Win η) := by
  have h : (256 : Nat) ^ (64 * η) = (2 ^ η * 2 ^ η) ^ 256 := by
    have hexp : (2 : Nat) ^ (8 * (64 * η)) = 2 ^ ((η + η) * 256) := by
      congr 1
      ring
    calc (256 : Nat) ^ (64 * η) = (2 ^ 8) ^ (64 * η) := by norm_num
      _ = 2 ^ (8 * (64 * η)) := by rw [← pow_mul]
      _ = 2 ^ ((η + η) * 256) := hexp
      _ = (2 ^ (η + η)) ^ 256 := by rw [← pow_mul]
      _ = (2 ^ η * 2 ^ η) ^ 256 := by rw [pow_add]
  simpa [Fintype.card_fun, card_uint8, Fintype.card_prod, Fintype.card_bool,
    Fintype.card_fin] using h

theorem windowMap_bijective (η : Nat) (hη : 0 < η) : Function.Bijective (windowMap η) :=
  (Fintype.bijective_iff_injective_and_card _).mpr
    ⟨windowMap_injective η hη, card_window_eq η⟩

/-- A uniform PRF block has uniform windows. -/
theorem uniform_windowMap (η : Nat) (hη : 0 < η) :
    (SDistr.uniform (MLKEM512Instance.PrfBlock η)).bind
        (fun b => SDistr.pure (windowMap η b))
      = SDistr.uniform (Fin 256 → Win η) :=
  SDistr.uniform_bind_bij (Equiv.ofBijective _ (windowMap_bijective η hη))

theorem samplePoly_eq (η : Nat) (b : MLKEM512Instance.PrfBlock η) :
    MLKEM512Instance.samplePoly η b
      = fun i => Zq3329.fromInt (windowVal (windowMap η b i)) := by
  funext i
  simp only [MLKEM512Instance.samplePoly, Sampler.sampleCBD_eta, windowMap]
  exact congrArg Zq3329.fromInt (cbdCoeff_eq_windowVal η (List.ofFn b) i.val)

/-- The law of the FIPS 203 centered-binomial sampler on a uniform PRF block is the
256-fold independent product of `CatCrypt.NonUniform.cbd η`, for every positive
`η`. -/
theorem samplerIsCbd (η : Nat) (hη : 0 < η) : MLKEM512Instance.SamplerIsCbd η := by
  show MLKEM512Instance.dshortPoly η = _
  rw [MLKEM512Instance.dshortPoly]
  calc (SDistr.uniform (MLKEM512Instance.PrfBlock η)).bind
        (fun b => SDistr.pure (MLKEM512Instance.samplePoly η b))
      = (SDistr.uniform (MLKEM512Instance.PrfBlock η)).bind
          (fun b => SDistr.pure (fun i => Zq3329.fromInt (windowVal (windowMap η b i)))) := by
        simp only [samplePoly_eq]
    _ = (SDistr.uniform (Fin 256 → Win η)).bind
          (fun W => SDistr.pure (fun i => Zq3329.fromInt (windowVal (W i)))) :=
        bind_of_pushforward (uniform_windowMap η hη)
          (fun W => SDistr.pure (fun i => Zq3329.fromInt (windowVal (W i))))
    _ = replicateFin 256 ((SDistr.uniform (Win η)).bind
          (fun w => SDistr.pure (Zq3329.fromInt (windowVal w)))) := by
        rw [uniform_pi]
        exact replicateFin_map _ (fun w => Zq3329.fromInt (windowVal w)) 256
    _ = replicateFin 256 ((cbd η).bind (fun c => SDistr.pure (Zq3329.fromInt c))) := by
        rw [bind_of_pushforward (uniform_windowVal η)
          (fun c => SDistr.pure (Zq3329.fromInt c))]
    _ = (replicateFin 256 (cbd η)).bind
          (fun c => SDistr.pure (fun i => Zq3329.fromInt (c i))) :=
        (replicateFin_map (cbd η) (fun c => Zq3329.fromInt c) 256).symm

/-- `SamplerIsCbd` at the two ML-KEM noise parameters. -/
theorem samplerIsCbd_two : MLKEM512Instance.SamplerIsCbd 2 := samplerIsCbd 2 (by norm_num)

theorem samplerIsCbd_three : MLKEM512Instance.SamplerIsCbd 3 := samplerIsCbd 3 (by norm_num)

end CatCrypt.Crypto.MLKEM.SamplerCbd
