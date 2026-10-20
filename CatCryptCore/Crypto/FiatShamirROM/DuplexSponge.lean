/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.ForMathlib.PMFMod
public import CatCryptCore.ForMathlib.PMFUniform
public import CatCryptCore.Crypto.MLKEM.XOFMatrix

/-!
# The duplex-sponge interface and the encodings of draft-irtf-cfrg-fiat-shamir-03

The byte-level objects of the duplex-sponge Fiat–Shamir transform of
draft-irtf-cfrg-fiat-shamir-03, with a sponge given abstractly by its output stream
`xof s i` (the byte at position `i` of the extendable output on the absorbed string
`s`).

* **Sponge (§3.2).** The state is the absorbed string and the position of the reader.
  `init R sid` absorbs the 32-byte session identifier padded with zeros to the rate
  `R`; `absorb x` appends `x` and resets the reader when `x` is non-empty; `squeeze n`
  reads the next `n` bytes of the output on the absorbed string.
* **Session identifiers (§5.1).** `deriveSessionID` squeezes 32 bytes after absorbing
  the tag into the sponge initialised with the label
  `"irtf-cfrg-fiat-shamir/session-id"`.
* **Transcripts (§3.2).** The challenge after the instance `x` and the prover message
  `a` is read from the output on
  `session_id ‖ zeros(R − 32) ‖ encode(x) ‖ encode(a)`.
* **Challenges (§4.2.2).** `decodeUint M buf = LE2IP(buf) mod M` on `Ns + 16` bytes,
  where `256^Ns ≥ M`.
* **Serialization (§6).** `LE(x, n)` and `LE2IP`, the codecs of unsigned integers,
  field elements and variable-length strings, and the parse of a whole NARG string.

## Main definitions

* `le2ip`, `leBytes` — little-endian bytes to integer and integer to `n` bytes
* `SpongeState`, `init`, `absorb`, `squeeze`, `deriveSessionID`
* `PrefixFree`, `SessionId`, `absorbedTranscript`
* `decodeUint`, `decodeUintDist`, `decodeField`, `decodeFieldDist`
* `Codec`, `Codec.parseAll`, `uintCodec`, `Codec.vec`, `varLenCodec`

## Main results

* `absorb_absorb` — two consecutive absorbs are one absorb of the concatenation
* `squeeze_squeeze` — squeezing `n` then `m` bytes reads the `n + m` bytes of one squeeze
* `squeeze_absorb_init` — the bytes squeezed after absorbing `x` are the first bytes of
  the output on `sid ‖ zeros(R − 32) ‖ x`
* `length_deriveSessionID`, `prefixFree_sessionId`, `PrefixFree.append`,
  `prefixFree_absorbedTranscript`, `absorbedTranscript_injective` — the absorbed string
  of a transcript is a prefix-free (so injective) encoding when the instance and message
  encodings are prefix-free
* `tvDist_decodeUintDist_le`, `tvDist_decodeUintDist_le_two_pow` — the statistical
  distance of `LE2IP mod M` on `L` uniform bytes from uniform on `[0, M)` is at most
  `M / 256^L`, at most `2^-128` for `L = Ns + 16`
* `tvDist_decodeFieldDist_le` — the same coordinatewise for `m` coordinates, `m·M/256^L`
* `Codec.parseAll_eq_some_iff`, `Codec.parseAll_append_eq_none`,
  `Codec.prefixFree_ser` — a whole-string parse accepts exactly the serializations, so it
  rejects every string with trailing bytes, and serializations are prefix-free
* `uintCodec`, `Codec.vec`, `varLenCodec` — `DeserializeUint`, `DeserializeField` and
  `DeserializeVarLenString` invert `SerializeUint`, `SerializeField` and
  `SerializeVarLenString`

## References

* M. Orrù, *Fiat-Shamir transformation*, draft-irtf-cfrg-fiat-shamir-03.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.FiatShamirROM.DuplexSponge

open CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal

/-- Byte strings. -/
abbrev Bytes := List UInt8

/-! ## Little-endian integers -/

/-- `LE2IP`: the integer with the little-endian bytes `l`. -/
def le2ip (l : Bytes) : ℕ := Nat.ofDigits 256 (l.map UInt8.toNat)

/-- `LE(x, n)`: the `n` little-endian bytes of `x` modulo `256^n`. -/
def leBytes : ℕ → ℕ → Bytes
  | _, 0 => []
  | x, n + 1 => UInt8.ofNat (x % 256) :: leBytes (x / 256) n

@[simp] theorem le2ip_nil : le2ip [] = 0 := rfl

theorem le2ip_cons (a : UInt8) (l : Bytes) : le2ip (a :: l) = a.toNat + 256 * le2ip l := by
  simp [le2ip, Nat.ofDigits_cons]

@[simp] theorem length_leBytes (x n : ℕ) : (leBytes x n).length = n := by
  induction n generalizing x <;> simp [leBytes, *]

theorem le2ip_leBytes (x n : ℕ) : le2ip (leBytes x n) = x % 256 ^ n := by
  induction n generalizing x with
  | zero => rw [leBytes, pow_zero, Nat.mod_one]; rfl
  | succ n ih =>
    rw [leBytes, le2ip_cons, ih, pow_succ', Nat.mod_mul]
    simp

theorem leBytes_le2ip (l : Bytes) : leBytes (le2ip l) l.length = l := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    have ha := a.toNat_lt
    rw [List.length_cons, leBytes, le2ip_cons]
    have h1 : (a.toNat + 256 * le2ip l) % 256 = a.toNat := by omega
    have h2 : (a.toNat + 256 * le2ip l) / 256 = le2ip l := by omega
    rw [h1, h2, ih, UInt8.ofNat_toNat]

theorem le2ip_lt (l : Bytes) : le2ip l < 256 ^ l.length := by
  induction l with
  | nil => simp
  | cons a l ih =>
    have ha := a.toNat_lt
    rw [le2ip_cons, List.length_cons, pow_succ]
    omega

theorem le2ip_ofFn {L : ℕ} (b : Fin L → UInt8) :
    le2ip (List.ofFn b) = ∑ i, (b i).toNat * 256 ^ (i : ℕ) := by
  induction L with
  | zero => simp
  | succ L ih =>
    rw [List.ofFn_succ, le2ip_cons, ih, Fin.sum_univ_succ, Finset.mul_sum]
    simp only [Fin.val_zero, pow_zero, mul_one, Fin.val_succ, pow_succ]
    congr 1
    refine Finset.sum_congr rfl fun i _ => by ring

/-! ## The duplex sponge -/

/-- The state of the duplex sponge: the absorbed string and the position of the reader
in the output on it. -/
structure SpongeState where
  /-- The absorbed string. -/
  absorbed : Bytes
  /-- The number of output bytes read since the last non-empty absorb. -/
  pos : ℕ

/-- `Init(session_id)`: the session identifier padded with zeros to the rate `R`. -/
def init (R : ℕ) (sid : Bytes) : SpongeState := ⟨sid ++ List.replicate (R - 32) 0, 0⟩

/-- `Absorb(x)`: a non-empty `x` is appended and the reader reset; the empty string
changes nothing. -/
def absorb (x : Bytes) (s : SpongeState) : SpongeState :=
  if x = [] then s else ⟨s.absorbed ++ x, 0⟩

/-- `Squeeze(n)`: the next `n` bytes of the output `xof` on the absorbed string. -/
def squeeze (xof : Bytes → ℕ → UInt8) (n : ℕ) (s : SpongeState) : Bytes × SpongeState :=
  (List.ofFn fun i : Fin n => xof s.absorbed (s.pos + i), ⟨s.absorbed, s.pos + n⟩)

@[simp] theorem absorb_nil (s : SpongeState) : absorb [] s = s := by simp [absorb]

/-- **Absorb associativity.** Absorbing `x` and then `y` is absorbing `x ++ y`. -/
theorem absorb_absorb (x y : Bytes) (s : SpongeState) :
    absorb y (absorb x s) = absorb (x ++ y) s := by
  by_cases hx : x = [] <;> by_cases hy : y = [] <;> simp [absorb, hx, hy]

/-- **Squeeze continuation.** Squeezing `n` bytes and then `m` bytes reads the bytes of
one squeeze of `n + m` bytes and ends in the same state. -/
theorem squeeze_squeeze (xof : Bytes → ℕ → UInt8) (n m : ℕ) (s : SpongeState) :
    (squeeze xof n s).1 ++ (squeeze xof m (squeeze xof n s).2).1 = (squeeze xof (n + m) s).1 ∧
      (squeeze xof m (squeeze xof n s).2).2 = (squeeze xof (n + m) s).2 := by
  refine ⟨?_, by simp [squeeze, add_assoc]⟩
  simp only [squeeze, List.ofFn_add]
  congr 1
  refine List.ofFn_inj.mpr (funext fun i => ?_)
  simp [add_assoc]

/-- The state after absorbing `x` from `init R sid` has the absorbed string
`sid ‖ zeros(R − 32) ‖ x` and the reader at the start. -/
theorem absorb_init (R : ℕ) (sid x : Bytes) :
    absorb x (init R sid) = ⟨sid ++ List.replicate (R - 32) 0 ++ x, 0⟩ := by
  by_cases hx : x = [] <;> simp [absorb, init, hx]

/-- The `n` bytes squeezed after absorbing `x` from `init R sid` are the first `n`
bytes of the output on `sid ‖ zeros(R − 32) ‖ x`: a function of the absorbed string. -/
theorem squeeze_absorb_init (xof : Bytes → ℕ → UInt8) (R n : ℕ) (sid x : Bytes) :
    (squeeze xof n (absorb x (init R sid))).1 =
      List.ofFn fun i : Fin n => xof (sid ++ List.replicate (R - 32) 0 ++ x) i := by
  simp [absorb_init, squeeze]

/-! ## Session identifiers and prefix-free encodings -/

/-- The label of the sponge of `DeriveSessionID`, `"irtf-cfrg-fiat-shamir/session-id"`. -/
def sessionIdLabel : Bytes := "irtf-cfrg-fiat-shamir/session-id".toUTF8.toList

/-- `DeriveSessionID(tag)`: the 32 bytes squeezed after absorbing `tag` into the sponge
initialised with `sessionIdLabel`. -/
def deriveSessionID (xof : Bytes → ℕ → UInt8) (R : ℕ) (tag : Bytes) : Bytes :=
  (squeeze xof 32 (absorb tag (init R sessionIdLabel))).1

theorem length_deriveSessionID (xof : Bytes → ℕ → UInt8) (R : ℕ) (tag : Bytes) :
    (deriveSessionID xof R tag).length = 32 := by
  simp [deriveSessionID, squeeze]

/-- A prefix-free encoding: an encoding that is a prefix of another is the same
value's. -/
def PrefixFree {α : Type*} (enc : α → Bytes) : Prop :=
  ∀ a b, enc a <+: enc b → a = b

theorem PrefixFree.injective {α : Type*} {enc : α → Bytes} (h : PrefixFree enc) :
    Function.Injective enc := fun a b hab => h a b (hab ▸ List.prefix_refl _)

/-- An injective encoding of fixed length is prefix-free. -/
theorem prefixFree_of_length {α : Type*} {enc : α → Bytes} (n : ℕ)
    (hn : ∀ a, (enc a).length = n) (hinj : Function.Injective enc) : PrefixFree enc :=
  fun a b h => hinj (h.eq_of_length (by rw [hn, hn]))

/-- The concatenation of two prefix-free encodings is prefix-free. -/
theorem PrefixFree.append {α β : Type*} {e₁ : α → Bytes} {e₂ : β → Bytes}
    (h₁ : PrefixFree e₁) (h₂ : PrefixFree e₂) :
    PrefixFree fun p : α × β => e₁ p.1 ++ e₂ p.2 := by
  rintro ⟨a, b⟩ ⟨a', b'⟩ h
  have ha : e₁ a <+: e₁ a' ++ e₂ b' := (List.prefix_append _ _).trans h
  have ha' : e₁ a' <+: e₁ a' ++ e₂ b' := List.prefix_append _ _
  have hea : a = a' := by
    rcases le_total (e₁ a).length (e₁ a').length with hl | hl
    · exact h₁ a a' (List.prefix_of_prefix_length_le ha ha' hl)
    · exact (h₁ a' a (List.prefix_of_prefix_length_le ha' ha hl)).symm
  subst hea
  exact Prod.ext rfl (h₂ b b' ((List.prefix_append_right_inj _).mp h))

/-- Session identifiers: strings of 32 bytes, the outputs of `deriveSessionID`. -/
abbrev SessionId := {b : Bytes // b.length = 32}

/-- The session identifier derived from `tag`. -/
def deriveSessionId (xof : Bytes → ℕ → UInt8) (R : ℕ) (tag : Bytes) : SessionId :=
  ⟨deriveSessionID xof R tag, length_deriveSessionID xof R tag⟩

/-- Session identifiers, encoded as their 32 bytes, are prefix-free. -/
theorem prefixFree_sessionId : PrefixFree fun s : SessionId => s.val :=
  prefixFree_of_length 32 (fun s => s.2) Subtype.val_injective

/-- The absorbed string of the transcript `(sid, x, a)`:
`sid ‖ zeros(R − 32) ‖ encode(x) ‖ encode(a)`. -/
def absorbedTranscript {X A : Type*} (R : ℕ) (encX : X → Bytes) (encA : A → Bytes)
    (k : SessionId × X × A) : Bytes :=
  k.1.val ++ List.replicate (R - 32) 0 ++ encX k.2.1 ++ encA k.2.2

/-- **Prefix-free transcripts.** For prefix-free instance and prover-message encodings,
the absorbed strings of transcripts are prefix-free. -/
theorem prefixFree_absorbedTranscript {X A : Type*} (R : ℕ) {encX : X → Bytes}
    {encA : A → Bytes} (hX : PrefixFree encX) (hA : PrefixFree encA) :
    PrefixFree (absorbedTranscript R encX encA) := by
  have h1 : PrefixFree fun s : SessionId => s.val ++ List.replicate (R - 32) (0 : UInt8) :=
    prefixFree_of_length (32 + (R - 32)) (fun s => by simp [s.2])
      (fun s t h => Subtype.ext (List.append_cancel_right h))
  have h := h1.append (hX.append hA)
  intro k k' hk
  exact h k k' (by simpa [absorbedTranscript, List.append_assoc] using hk)

/-- Distinct transcripts have distinct absorbed strings. -/
theorem absorbedTranscript_injective {X A : Type*} (R : ℕ) {encX : X → Bytes}
    {encA : A → Bytes} (hX : PrefixFree encX) (hA : PrefixFree encA) :
    Function.Injective (absorbedTranscript R encX encA) :=
  (prefixFree_absorbedTranscript R hX hA).injective

/-! ## Decoding challenges -/

/-- `DecodeUint(buf) = LE2IP(buf) mod M`. -/
def decodeUint (M : ℕ) [NeZero M] (buf : Bytes) : Fin M :=
  ⟨le2ip buf % M, Nat.mod_lt _ (NeZero.pos M)⟩

/-- The distribution of `DecodeUint` on `L` uniform bytes. -/
noncomputable def decodeUintDist (M L : ℕ) [NeZero M] : PMF (Fin M) :=
  (PMF.uniformOfFintype (Fin L → UInt8)).map fun b => decodeUint M (List.ofFn b)

/-- `L` bytes as an integer below `256^L`, little-endian. -/
def bytesEquivFin (L : ℕ) : (Fin L → UInt8) ≃ Fin (256 ^ L) :=
  (Equiv.piCongrRight fun _ =>
    (⟨UInt8.toFin, UInt8.ofFin, fun _ => rfl, fun _ => rfl⟩ : UInt8 ≃ Fin 256)).trans
    finFunctionFinEquiv

theorem val_bytesEquivFin {L : ℕ} (b : Fin L → UInt8) :
    (bytesEquivFin L b : ℕ) = le2ip (List.ofFn b) := by
  rw [le2ip_ofFn, bytesEquivFin, Equiv.trans_apply, finFunctionFinEquiv_apply]
  rfl

/-- `DecodeUint` on uniform bytes is the reduction modulo `M` of a uniform value below
`256^L`. -/
theorem decodeUintDist_eq (M L : ℕ) [NeZero M] :
    decodeUintDist M L = (PMF.uniformOfFintype (Fin (256 ^ L))).map (Fin.modTo _ M) := by
  have h : (fun b => decodeUint M (List.ofFn b)) = Fin.modTo _ M ∘ bytesEquivFin L := by
    funext b
    ext
    simp [decodeUint, Fin.modTo, val_bytesEquivFin]
  rw [decodeUintDist, h, ← PMF.map_comp, PMF.uniformOfFintype_map_equiv]

/-- The minorant of `DecodeUint` on `L` uniform bytes: mass at least
`(1 − M/256^L)·(1/M)` on every value. -/
theorem one_sub_mul_uniform_le_decodeUintDist (M L : ℕ) [NeZero M] (r : Fin M) :
    (1 - (M : ℝ≥0∞) / (256 ^ L : ℕ)) * PMF.uniformOfFintype (Fin M) r ≤ decodeUintDist M L r := by
  have : NeZero (256 ^ L) := ⟨by positivity⟩
  rw [decodeUintDist_eq]
  exact PMF.one_sub_mul_uniform_le_map_mod (256 ^ L) M r

theorem map_some_apply_some {α : Type} (p : PMF α) (a : α) : (p.map some) (some a) = p a := by
  rw [PMF.map_apply, tsum_eq_single a fun b hb => by simp [Ne.symm hb]]
  simp

/-- **The bias of `DecodeUint`.** The statistical distance of `LE2IP mod M` on `L`
uniform bytes from the uniform distribution on `[0, M)` is at most `M / 256^L`. -/
theorem tvDist_decodeUintDist_le (M L : ℕ) [NeZero M] :
    tvDist ((decodeUintDist M L).map some) (SDistr.uniform (Fin M)) ≤
      (M : ℝ≥0∞) / (256 ^ L : ℕ) := by
  refine iSup₂_le fun f hf => ?_
  have hmin : ∀ a, (1 - (M : ℝ≥0∞) / (256 ^ L : ℕ)) * SDistr.uniform (Fin M) (some a) ≤
      (decodeUintDist M L).map some (some a) := fun a => by
    rw [SDistr.uniform, map_some_apply_some, map_some_apply_some]
    exact one_sub_mul_uniform_le_decodeUintDist M L a
  have h := MLKEM.XOFMatrix.tsum_le_add_of_minorant ((decodeUintDist M L).map some)
    (SDistr.uniform (Fin M)) _ (MLKEM.XOFMatrix.minorant_option _ _ hmin) f hf
  exact sup_le (tsub_le_iff_left.mpr h.1) (tsub_le_iff_left.mpr h.2)

/-- **The bias of `DecodeUint` at `Ns + 16` bytes.** For `M ≤ 256^Ns`, the statistical
distance of `LE2IP mod M` on `Ns + 16` uniform bytes from uniform on `[0, M)` is at
most `2^-128`. -/
theorem tvDist_decodeUintDist_le_two_pow (M Ns : ℕ) [NeZero M] (hM : M ≤ 256 ^ Ns) :
    tvDist ((decodeUintDist M (Ns + 16)).map some) (SDistr.uniform (Fin M)) ≤
      ((2 : ℝ≥0∞) ^ 128)⁻¹ := by
  refine (tvDist_decodeUintDist_le M _).trans ?_
  have hx : ((256 ^ Ns : ℕ) : ℝ≥0∞) ≠ 0 := by simp
  have hx' : ((256 ^ Ns : ℕ) : ℝ≥0∞) ≠ ⊤ := by simp
  calc (M : ℝ≥0∞) / (256 ^ (Ns + 16) : ℕ)
      ≤ ((256 ^ Ns : ℕ) : ℝ≥0∞) / (256 ^ (Ns + 16) : ℕ) := by gcongr
    _ = ((256 ^ Ns : ℕ) : ℝ≥0∞) / ((256 ^ Ns : ℕ) * (256 ^ 16 : ℕ)) := by
        rw [pow_add, Nat.cast_mul]
    _ = ((256 ^ 16 : ℕ) : ℝ≥0∞)⁻¹ := by
        rw [div_eq_mul_inv, ENNReal.mul_inv (Or.inl hx) (Or.inl hx'), ← mul_assoc,
          ENNReal.mul_inv_cancel hx hx', one_mul]
    _ = ((2 : ℝ≥0∞) ^ 128)⁻¹ := by norm_num

/-- `DecodeField` on `m` chunks of `L` bytes: each coordinate is `DecodeUint` of its
chunk. -/
def decodeField (M : ℕ) [NeZero M] {m L : ℕ} (b : Fin m → Fin L → UInt8) : Fin m → Fin M :=
  fun i => decodeUint M (List.ofFn (b i))

/-- The distribution of `DecodeField` on `m` uniform chunks of `L` bytes. -/
noncomputable def decodeFieldDist (M L m : ℕ) [NeZero M] : PMF (Fin m → Fin M) :=
  (PMF.uniformOfFintype (Fin m → Fin L → UInt8)).map (decodeField M)

/-- The minorant of `DecodeField`: mass at least `(1 − m·M/256^L)` times the uniform
mass on every value. -/
theorem one_sub_mul_uniform_le_decodeFieldDist (M L m : ℕ) [NeZero M] (o : Fin m → Fin M) :
    (1 - (m : ℝ≥0∞) * ((M : ℝ≥0∞) / (256 ^ L : ℕ))) * PMF.uniformOfFintype (Fin m → Fin M) o ≤
      decodeFieldDist M L m o := by
  have hU : PMF.uniformOfFintype (Fin m → Fin M) o = ∏ i, PMF.uniformOfFintype (Fin M) (o i) := by
    simp [PMF.uniformOfFintype_apply, Finset.prod_const, ENNReal.inv_pow]
  calc (1 - (m : ℝ≥0∞) * ((M : ℝ≥0∞) / (256 ^ L : ℕ))) * PMF.uniformOfFintype (Fin m → Fin M) o
      ≤ (1 - (M : ℝ≥0∞) / (256 ^ L : ℕ)) ^ m * ∏ i, PMF.uniformOfFintype (Fin M) (o i) := by
        rw [hU]
        gcongr
        exact ENNReal.one_sub_mul_le_pow _ m
    _ = ∏ i, (1 - (M : ℝ≥0∞) / (256 ^ L : ℕ)) * PMF.uniformOfFintype (Fin M) (o i) := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ ≤ ∏ i, decodeUintDist M L (o i) :=
        Finset.prod_le_prod' fun i _ => one_sub_mul_uniform_le_decodeUintDist M L (o i)
    _ = decodeFieldDist M L m o :=
        (PMF.map_uniform_pi_apply (fun _ b => decodeUint M (List.ofFn b)) o).symm

/-- **The bias of `DecodeField`.** The statistical distance of `DecodeField` on `m`
uniform chunks of `L` bytes from the uniform distribution on `[0, M)^m` is at most
`m·M/256^L`. -/
theorem tvDist_decodeFieldDist_le (M L m : ℕ) [NeZero M] :
    tvDist ((decodeFieldDist M L m).map some) (SDistr.uniform (Fin m → Fin M)) ≤
      (m : ℝ≥0∞) * ((M : ℝ≥0∞) / (256 ^ L : ℕ)) := by
  refine iSup₂_le fun f hf => ?_
  have hmin : ∀ a, (1 - (m : ℝ≥0∞) * ((M : ℝ≥0∞) / (256 ^ L : ℕ))) *
      SDistr.uniform (Fin m → Fin M) (some a) ≤ (decodeFieldDist M L m).map some (some a) :=
    fun a => by
      rw [SDistr.uniform, map_some_apply_some, map_some_apply_some]
      exact one_sub_mul_uniform_le_decodeFieldDist M L m a
  have h := MLKEM.XOFMatrix.tsum_le_add_of_minorant ((decodeFieldDist M L m).map some)
    (SDistr.uniform (Fin m → Fin M)) _ (MLKEM.XOFMatrix.minorant_option _ _ hmin) f hf
  exact sup_le (tsub_le_iff_left.mpr h.1) (tsub_le_iff_left.mpr h.2)

/-! ## Serialization -/

/-- A serialization with its deserialization on the valid values: deserializing a
serialization followed by any bytes returns the value and the bytes, and every
successful deserialization reads a serialization of a valid value. -/
structure Codec (α : Type*) where
  /-- The valid values. -/
  valid : α → Prop
  /-- The serialization. -/
  ser : α → Bytes
  /-- The deserialization: a value and the remaining bytes. -/
  de : Bytes → Option (α × Bytes)
  /-- Deserializing a serialization. -/
  de_ser : ∀ v r, valid v → de (ser v ++ r) = some (v, r)
  /-- A successful deserialization reads a serialization of a valid value. -/
  ser_de : ∀ s v r, de s = some (v, r) → valid v ∧ s = ser v ++ r

namespace Codec

variable {α : Type*} (C : Codec α)

/-- The parse of a whole string: the value when the deserialization consumes every
byte, and nothing otherwise (a verifier fails on remaining bytes). -/
def parseAll (s : Bytes) : Option α :=
  match C.de s with
  | some (v, []) => some v
  | _ => none

/-- A whole-string parse accepts exactly the serializations of valid values. -/
theorem parseAll_eq_some_iff (s : Bytes) (v : α) :
    C.parseAll s = some v ↔ C.valid v ∧ s = C.ser v := by
  unfold parseAll
  constructor
  · intro h
    rcases hde : C.de s with _ | ⟨v', _ | ⟨b, r⟩⟩ <;> rw [hde] at h
    · simp at h
    · obtain ⟨hv, hs⟩ := C.ser_de s v' [] hde
      simp only [Option.some.injEq] at h
      subst h
      exact ⟨hv, by simpa using hs⟩
    · simp at h
  · rintro ⟨hv, rfl⟩
    have h := C.de_ser v [] hv
    rw [List.append_nil] at h
    rw [h]

/-- **Trailing bytes are rejected.** The whole-string parse of a serialization followed
by a non-empty string fails. -/
theorem parseAll_append_eq_none {v : α} (hv : C.valid v) {t : Bytes} (ht : t ≠ []) :
    C.parseAll (C.ser v ++ t) = none := by
  unfold parseAll
  rw [C.de_ser v t hv]
  rcases t with _ | ⟨b, t⟩
  · exact absurd rfl ht
  · rfl

/-- Serializations of valid values are prefix-free. -/
theorem prefixFree_ser : PrefixFree fun v : {v // C.valid v} => C.ser v.1 := by
  rintro ⟨a, ha⟩ ⟨b, hb⟩ ⟨t, ht⟩
  simp only at ht
  have h1 := C.de_ser a t ha
  have h2 := C.de_ser b [] hb
  rw [List.append_nil, ← ht, h1] at h2
  simp only [Option.some.injEq, Prod.mk.injEq] at h2
  exact Subtype.ext h2.1

/-- The deserialization of `m` values in sequence. -/
def deVec : ℕ → Bytes → Option (List α × Bytes)
  | 0, s => some ([], s)
  | m + 1, s =>
    match C.de s with
    | none => none
    | some (v, r) =>
      match deVec m r with
      | none => none
      | some (vs, r') => some (v :: vs, r')

theorem deVec_ser (m : ℕ) (l : List α) (hl : l.length = m) (hv : ∀ x ∈ l, C.valid x)
    (r : Bytes) : C.deVec m ((l.map C.ser).flatten ++ r) = some (l, r) := by
  induction m generalizing l with
  | zero =>
    rw [List.length_eq_zero_iff] at hl
    subst hl
    rfl
  | succ m ih =>
    rcases l with _ | ⟨x, xs⟩
    · simp at hl
    · rw [List.map_cons, List.flatten_cons, List.append_assoc, deVec,
        C.de_ser x _ (hv x List.mem_cons_self)]
      simp only
      rw [ih xs (by simpa using hl) (fun y hy => hv y (List.mem_cons_of_mem _ hy))]

theorem ser_deVec (m : ℕ) (s : Bytes) (vs : List α) (r : Bytes)
    (h : C.deVec m s = some (vs, r)) :
    (vs.length = m ∧ ∀ x ∈ vs, C.valid x) ∧ s = (vs.map C.ser).flatten ++ r := by
  induction m generalizing s vs r with
  | zero =>
    simp only [deVec, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    simp
  | succ m ih =>
    rw [deVec] at h
    rcases hde : C.de s with _ | ⟨v, r₁⟩ <;> rw [hde] at h
    · simp at h
    · simp only at h
      rcases hrec : C.deVec m r₁ with _ | ⟨vs', r'⟩ <;> rw [hrec] at h
      · simp at h
      · simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨hv, hs⟩ := C.ser_de s v r₁ hde
        obtain ⟨⟨hl, hvs⟩, hr⟩ := ih r₁ vs' r' hrec
        refine ⟨⟨by simp [hl], fun x hx => ?_⟩, ?_⟩
        · rcases List.mem_cons.mp hx with rfl | hx
          · exact hv
          · exact hvs x hx
        · rw [hs, hr]
          simp

/-- The codec of `m` values in sequence. -/
def vec (m : ℕ) : Codec (List α) where
  valid l := l.length = m ∧ ∀ x ∈ l, C.valid x
  ser l := (l.map C.ser).flatten
  de := C.deVec m
  de_ser v r hv := C.deVec_ser m v hv.1 hv.2 r
  ser_de s v r h := C.ser_deVec m s v r h

end Codec

/-- `SerializeUint`/`DeserializeUint`: `x < M` as `LE(x, Ns)`, for `M ≤ 256^Ns`. -/
def uintCodec (Ns M : ℕ) (hM : M ≤ 256 ^ Ns) : Codec ℕ where
  valid x := x < M
  ser x := leBytes x Ns
  de input :=
    if input.length < Ns then none
    else if M ≤ le2ip (input.take Ns) then none
    else some (le2ip (input.take Ns), input.drop Ns)
  de_ser x r hx := by
    have hx' : x < 256 ^ Ns := lt_of_lt_of_le hx hM
    have ht : (leBytes x Ns ++ r).take Ns = leBytes x Ns :=
      List.take_left' (length_leBytes x Ns)
    have hd : (leBytes x Ns ++ r).drop Ns = r := List.drop_left' (length_leBytes x Ns)
    simp only [ht, hd, le2ip_leBytes, Nat.mod_eq_of_lt hx', List.length_append,
      length_leBytes]
    simp [not_le.mpr hx]
  ser_de s x r h := by
    split_ifs at h with h1 h2
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    refine ⟨not_le.mp h2, ?_⟩
    have hl : (s.take Ns).length = Ns := by simp; omega
    have he := leBytes_le2ip (s.take Ns)
    rw [hl] at he
    rw [he, List.take_append_drop]

/-- `SerializeField`/`DeserializeField`: `m` coordinates modulo `p`, each as
`SerializeUint`. -/
def fieldCodec (Ns p m : ℕ) (hp : p ≤ 256 ^ Ns) : Codec (List ℕ) :=
  (uintCodec Ns p hp).vec m

/-- `SerializeVarLenString`/`DeserializeVarLenString`: a string shorter than `2^32`
as `LE(len, 4) ‖ s`. -/
def varLenCodec : Codec Bytes where
  valid s := s.length < 2 ^ 32
  ser s := leBytes s.length 4 ++ s
  de input :=
    if input.length < 4 then none
    else if (input.drop 4).length < le2ip (input.take 4) then none
    else some ((input.drop 4).take (le2ip (input.take 4)),
      (input.drop 4).drop (le2ip (input.take 4)))
  de_ser s r hs := by
    have hs' : s.length < 256 ^ 4 := by simpa using hs
    have ht : (leBytes s.length 4 ++ s ++ r).take 4 = leBytes s.length 4 := by
      rw [List.append_assoc]; exact List.take_left' (length_leBytes _ 4)
    have hd : (leBytes s.length 4 ++ s ++ r).drop 4 = s ++ r := by
      rw [List.append_assoc]; exact List.drop_left' (length_leBytes _ 4)
    simp only [ht, hd, le2ip_leBytes, Nat.mod_eq_of_lt hs', List.length_append,
      length_leBytes, List.take_left', List.drop_left']
    simp
    omega
  ser_de input v r h := by
    split_ifs at h with h1 h2
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    have hl4 : (input.take 4).length = 4 := by simp; omega
    have hN : ((input.drop 4).take (le2ip (input.take 4))).length = le2ip (input.take 4) := by
      rw [List.length_take]; omega
    have hlt := le2ip_lt (input.take 4)
    rw [hl4] at hlt
    refine ⟨by rw [hN]; simpa using hlt, ?_⟩
    have he := leBytes_le2ip (input.take 4)
    rw [hl4] at he
    rw [hN, he, List.append_assoc, List.take_append_drop, List.take_append_drop]

end CatCrypt.Crypto.FiatShamirROM.DuplexSponge
