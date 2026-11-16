/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.KEM.MlkemFo.Extraction.MlkemFo_haxpipe
public import CatCryptCore.Crypto.KEM.FIPS203Security
public import CatCryptCore.Crypto.ExtractedAlgebra
public import HaxLean.FoldRange

/-!
# ML-KEM FO SurfaceDeps: the extracted ML-KEM transform computes `fips203`

`MlkemFo` is the haxpipeT extraction of the Rust crate `mlkem-fo-hax`, the
Fujisaki–Okamoto layer of ML-KEM-768 (FIPS 203, Algorithms 16–18) over the operations of
`MlkemFoDeps`: K-PKE key generation, encryption and decryption, the hashes `H`, `G`, `J`
and the ciphertext comparison, all over byte arrays `Array Int`. Below, these operations
are interpreted by an abstract public-key encryption scheme `P : Scheme PK SK M C R`, a
public-key hash `hpk` and the two oracle functions `g`, `j`, through encodings of the
typed values (`FoCodecs`), and the extracted `keygen`, `encaps` and `decaps` are shown to
compute `fips203 P hpk`.

The decapsulation key built by the extracted `keygen` is the concatenation
`dk_pke ‖ ek ‖ H(ek) ‖ z` (`keygen_layout`), and the copy loops of the extracted `decaps`
read the four parts back (`decaps_layout`).

`extFO` is the KEM in the two-oracle random-oracle model whose algorithms are the
extracted functions: key generation runs the extracted `keygen` on a uniform seed and a
uniform `z`; encapsulation and decapsulation query `G` and `J` at the points the
extracted code passes to `g` and `j`, and return the output of the extracted `encaps` and
`decaps` run with the oracle answers in the fields `g` and `j` (`withRO`). Decapsulation
runs the extracted `decaps` with two distinct values in the field `j`; the two outputs
agree exactly when the re-encryption check accepts, and `J` is queried otherwise. The
IND-CCA game of `extFO` is the IND-CCA game of `fips203 P hpk`, so the bound of
`fips203_indcca` holds for it.

## Main definitions

* `FoCodecs` — encodings of keys, messages, ciphertexts, coins, shared keys, hashes,
  seeds as byte arrays, with the byte lengths of the crate
* `PkeHom` — the K-PKE operations, `H` and `ct_eq` of an instance interpret `P`, `hpk`
* `FoHom` — in addition, the fields `g` and `j` interpret the oracle functions `g`, `j`
* `dkOf` — the decapsulation key `dk_pke ‖ ek ‖ H(ek) ‖ z`
* `withRO I gv jv` — the instance `I` with the constant answers `gv`, `jv` in `g`, `j`
* `extFO` — the KEM whose algorithms are the extracted functions

## Main results

* `keygen_layout`, `decaps_layout` — the copy loops build and parse `dkOf`
* `keygen_enc`, `encaps_enc`, `decaps_enc` — the extracted functions compute key
  generation, encapsulation and decapsulation of `fips203 P hpk` against `fixedRO2 g j`
* `extFO_keygen`, `extFO_encaps`, `extFO_decaps` — the algorithms of `extFO` against those
  of `fips203 P hpk`
* `rom2INDCCAGame_extFO`, `extFO_indcca_eq` — the IND-CCA game and advantage of `extFO`
  are those of `fips203 P hpk`
* `extFO_indcca` — the bound of `fips203_indcca` for `extFO`
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.KEM.MlkemFo.SurfaceDeps

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.PKE.Games CatCrypt.Crypto.KEM.Games CatCrypt.Crypto.KEM.FIPS203
open CatCrypt.Crypto.Extracted (Codec)
open scoped ENNReal

/-! ## Copy loops -/

/-- The loop writing `src i` at position `pos i = off + i` for `0 ≤ i < n` keeps the size
of the array, writes `src (j - off)` at every position `off ≤ j < off + n` in bounds, and
keeps the other entries. -/
theorem foldRange_write (pos src : Int → Int) (off n : Int) (hpos : ∀ i, pos i = off + i)
    (hoff : 0 ≤ off) (hn : 0 ≤ n) (acc : Array Int) :
    (Hax.foldRange 0 n acc fun i r => Hax.array_update r (pos i) (src i)).size = acc.size ∧
      ∀ j : Nat, (Hax.foldRange 0 n acc fun i r => Hax.array_update r (pos i) (src i))[j]? =
        if off ≤ j ∧ (j : Int) < off + n ∧ j < acc.size then some (src (j - off))
        else acc[j]? := by
  refine Hax.foldRange_induct (P := fun (i : Int) (r : Array Int) => r.size = acc.size ∧
      ∀ j : Nat, r[j]? = if off ≤ j ∧ (j : Int) < off + i ∧ j < acc.size then
        some (src (j - off)) else acc[j]?) hn ?_ ?_
  · exact ⟨rfl, fun j => by grind⟩
  · intro i a hi0 hin ⟨hs, ha⟩
    grind [Hax.array_update, Array.size_set]

/-- `Hax.index` at an in-bounds position is the optional read `getElem?`. -/
theorem some_index (a : Array Int) (k : Int) (n : Nat) (hk : k = n) (h : n < a.size) :
    some (Hax.index a k) = a[n]? := by
  subst hk
  rw [Hax.index_natCast a n h, Array.getElem?_eq_getElem h]

/-- The decapsulation key `dk_pke ‖ ek ‖ H(ek) ‖ z` as one byte array. -/
def layout (a b c d : Array Int) : Array Int := a ++ b ++ c ++ d

/-- The copy loops of the extracted `keygen` build `dk_pke ‖ ek ‖ H(ek) ‖ z`, when the
four parts have 1152, 1184, 32 and 32 bytes. -/
theorem keygen_layout [MlkemFo.MlkemFoDeps] (d z : Array Int)
    (h1 : (MlkemFo.MlkemFoDeps.kpke_keygen d).1.size = 1184)
    (h2 : (MlkemFo.MlkemFoDeps.kpke_keygen d).2.size = 1152)
    (h3 : (MlkemFo.MlkemFoDeps.h (MlkemFo.MlkemFoDeps.kpke_keygen d).1).size = 32)
    (h4 : z.size = 32) :
    MlkemFo.keygen d z = ((MlkemFo.MlkemFoDeps.kpke_keygen d).1,
      layout (MlkemFo.MlkemFoDeps.kpke_keygen d).2 (MlkemFo.MlkemFoDeps.kpke_keygen d).1
        (MlkemFo.MlkemFoDeps.h (MlkemFo.MlkemFoDeps.kpke_keygen d).1) z) := by
  unfold MlkemFo.keygen
  generalize MlkemFo.MlkemFoDeps.kpke_keygen d = p at *
  obtain ⟨ek, dkp⟩ := p
  simp only [MlkemFo.DK_PKE_BYTES, MlkemFo.EK_BYTES, MlkemFo.SEED_BYTES,
    MlkemFo.DK_EK_OFFSET, MlkemFo.DK_H_OFFSET, MlkemFo.DK_Z_OFFSET, Hax.add] at *
  refine Prod.ext rfl (Array.ext_getElem? fun j => ?_)
  have e1 := fun acc => foldRange_write (fun i => i) (fun i => Hax.index dkp i) 0 1152
    (fun i => by simp) le_rfl (by norm_num) acc
  have e2 := fun acc => foldRange_write (fun i => 1152 + i) (fun i => Hax.index ek i) 1152 1184
    (fun _ => rfl) (by norm_num) (by norm_num) acc
  have e3 := fun acc => foldRange_write (fun i => 1152 + 1184 + i)
    (fun i => Hax.index (MlkemFo.h ek) i) (1152 + 1184) 32 (fun _ => rfl) (by norm_num)
    (by norm_num) acc
  have e4 := fun acc => foldRange_write (fun i => 1152 + 1184 + 32 + i)
    (fun i => Hax.index z i) (1152 + 1184 + 32) 32 (fun _ => rfl) (by norm_num)
    (by norm_num) acc
  have hrep : (Hax.repeat_ (0 : Int) 2400).size = 2400 := by grind
  dsimp only at e1 e2 e3 e4 ⊢
  simp only [(e4 _).2, (e3 _).1, (e3 _).2, (e2 _).1, (e2 _).2, (e1 _).1, (e1 _).2, hrep]
  clear e1 e2 e3 e4
  generalize Hax.repeat_ (0 : Int) 2400 = R at *
  simp only [layout, Array.getElem?_append, Array.size_append, h1, h2, h3]
  split_ifs <;> first
    | (exfalso; omega)
    | exact some_index _ _ _ (by omega) (by omega)
    | exact (Array.getElem?_eq_none (by omega)).trans (Array.getElem?_eq_none (by omega)).symm

/-- The loop copying `src i` into position `i` of a zero array of size `n` returns `part`,
when `part` has `n` entries and `src i` is entry `i` of `part`. -/
theorem foldRange_read (src : Int → Int) (n : Int) (part : Array Int)
    (hs : (part.size : Int) = n) (hsrc : ∀ i : Nat, i < part.size → some (src i) = part[i]?) :
    (Hax.foldRange 0 n (Hax.repeat_ 0 n) fun i r => Hax.array_update r i (src i)) = part := by
  obtain ⟨s, e⟩ := foldRange_write (fun i => i) src 0 n (fun i => by simp) le_rfl (by omega)
    (Hax.repeat_ 0 n)
  have hrep : (Hax.repeat_ (0 : Int) n).size = part.size := by
    simp only [Hax.repeat_, List.size_toArray, List.length_replicate]; omega
  generalize Hax.repeat_ (0 : Int) n = R at *
  refine Array.ext_getElem? fun j => ?_
  rw [e j]
  split_ifs with h
  · simpa using hsrc j (by omega)
  · exact (Array.getElem?_eq_none (by omega)).trans (Array.getElem?_eq_none (by omega)).symm

/-- The copy loops of the extracted `decaps` read the four parts of
`dk_pke ‖ ek ‖ H(ek) ‖ z` back: decapsulation of `ct` under this key decrypts with
`dk_pke`, derives `(K', r')` from `G` at the stored hash, re-encrypts under `ek` and
returns `K'` when `ct_eq` accepts and `J(z, ct)` otherwise. -/
theorem decaps_layout [MlkemFo.MlkemFoDeps] (a b c d ct : Array Int) (ha : a.size = 1152)
    (hb : b.size = 1184) (hc : c.size = 32) (hd : d.size = 32) :
    MlkemFo.decaps (layout a b c d) ct =
      if MlkemFo.MlkemFoDeps.ct_eq ct (MlkemFo.MlkemFoDeps.kpke_encrypt b
          (MlkemFo.MlkemFoDeps.kpke_decrypt a ct)
          (MlkemFo.MlkemFoDeps.g (MlkemFo.MlkemFoDeps.kpke_decrypt a ct) c).2) then
        (MlkemFo.MlkemFoDeps.g (MlkemFo.MlkemFoDeps.kpke_decrypt a ct) c).1
      else MlkemFo.MlkemFoDeps.j d ct := by
  have hL : ∀ (off : Nat) (part : Array Int) (i : Nat), i < part.size →
      (∀ k : Nat, k < part.size → (layout a b c d)[off + k]? = part[k]?) →
      some (Hax.index (layout a b c d) ((off : Int) + i)) = part[i]? := by
    intro off part i hi hpart
    have := hpart i hi
    rw [Array.getElem?_eq_getElem hi] at this
    rw [some_index _ _ (off + i) (by omega) (Array.getElem?_eq_some_iff.1 this).1, hpart i hi]
  have p1 := foldRange_read (fun i => Hax.index (layout a b c d) i) 1152 a (by omega)
    (fun i hi => by simpa using hL 0 a i hi (fun k hk => by
      simp only [layout, Array.getElem?_append, Array.size_append, ha, hb, hc]; grind))
  have p2 := foldRange_read (fun i => Hax.index (layout a b c d) (1152 + i)) 1184 b
    (by omega) (fun i hi => by simpa using hL 1152 b i hi (fun k hk => by
      simp only [layout, Array.getElem?_append, Array.size_append, ha, hb, hc]; grind))
  have p3 := foldRange_read (fun i => Hax.index (layout a b c d) (1152 + 1184 + i)) 32 c
    (by omega) (fun i hi => by simpa using hL 2336 c i hi (fun k hk => by
      simp only [layout, Array.getElem?_append, Array.size_append, ha, hb, hc]; grind))
  have p4 := foldRange_read (fun i => Hax.index (layout a b c d) (1152 + 1184 + 32 + i)) 32 d
    (by omega) (fun i hi => by simpa using hL 2368 d i hi (fun k hk => by
      simp only [layout, Array.getElem?_append, Array.size_append, ha, hb, hc]; grind))
  simp only [MlkemFo.decaps, MlkemFo.DK_PKE_BYTES, MlkemFo.EK_BYTES, MlkemFo.SEED_BYTES,
    MlkemFo.DK_EK_OFFSET, MlkemFo.DK_H_OFFSET, MlkemFo.DK_Z_OFFSET, Hax.add]
  simp only [p1, p2, p3, p4]

/-- The first 1152 bytes of `dk_pke ‖ ek ‖ H(ek) ‖ z` are `dk_pke`. -/
theorem layout_extract_dkPke (a b c d : Array Int) (ha : a.size = 1152) :
    (layout a b c d).extract 0 1152 = a := by
  unfold layout; simp_all

/-- Bytes 2336 to 2368 of `dk_pke ‖ ek ‖ H(ek) ‖ z` are the stored hash. -/
theorem layout_extract_hash (a b c d : Array Int) (ha : a.size = 1152) (hb : b.size = 1184)
    (hc : c.size = 32) : (layout a b c d).extract 2336 2368 = c := by
  unfold layout
  simp only [Array.extract_append, Array.size_append, ha, hb, hc]
  rw [Array.extract_eq_empty_of_le (by omega), Array.extract_eq_empty_of_le (by omega)]
  simp [hc]

/-- Bytes 2368 to 2400 of `dk_pke ‖ ek ‖ H(ek) ‖ z` are the seed `z`. -/
theorem layout_extract_z (a b c d : Array Int) (ha : a.size = 1152) (hb : b.size = 1184)
    (hc : c.size = 32) (hd : d.size = 32) : (layout a b c d).extract 2368 2400 = d := by
  unfold layout
  simp only [Array.extract_append, Array.size_append, ha, hb, hc]
  rw [Array.extract_eq_empty_of_le (by omega), Array.extract_eq_empty_of_le (by omega),
    Array.extract_eq_empty_of_le (by omega)]
  simp [hd]

/-! ## Encodings and the interpretation -/

variable {PK SK M C R K Hash Z D : Type}

/-- Encodings of the typed values of `fips203` as the byte arrays of the crate: public
keys (1184 bytes), K-PKE secret keys (1152 bytes), messages, ciphertexts, coins, shared
keys, public-key hashes (32 bytes), rejection seeds (32 bytes) and key-generation
seeds. -/
structure FoCodecs (PK SK M C R K Hash Z D : Type) where
  /-- Public keys. -/
  pk : Codec PK (Array Int)
  /-- K-PKE secret keys. -/
  sk : SK → Array Int
  /-- Messages. -/
  msg : Codec M (Array Int)
  /-- Ciphertexts. -/
  ct : Codec C (Array Int)
  /-- Encryption coins. -/
  coins : R → Array Int
  /-- Shared keys. -/
  key : Codec K (Array Int)
  /-- Public-key hashes. -/
  hash : Codec Hash (Array Int)
  /-- Rejection seeds. -/
  seedZ : Codec Z (Array Int)
  /-- Key-generation seeds. -/
  seed : D → Array Int
  pk_size : ∀ x, (pk.enc x).size = 1184
  sk_size : ∀ x, (sk x).size = 1152
  hash_size : ∀ x, (hash.enc x).size = 32
  z_size : ∀ x, (seedZ.enc x).size = 32

/-- The decapsulation key `dk_pke ‖ ek ‖ H(ek) ‖ z` of the key pair `(pk, sk)` and the
seed `z`, with `H(ek) = hpk pk`. -/
def FoCodecs.dkOf (E : FoCodecs PK SK M C R K Hash Z D) (hpk : PK → Hash) (sk : SK) (pk : PK)
    (z : Z) : Array Int :=
  layout (E.sk sk) (E.pk.enc pk) (E.hash.enc (hpk pk)) (E.seedZ.enc z)

variable [DecidableEq C]

/-- The K-PKE operations, `H` and `ct_eq` of the instance `I` interpret the scheme `P` and
the hash `hpk` at the encodings `E`: key generation of `P` is the image of a deterministic
`kg` on a uniform seed, and `kpke_keygen` computes `kg`; `h` computes `hpk`;
`kpke_encrypt` computes `P.enc`; on every key pair of `kg`, `P` decrypts every ciphertext
and `kpke_decrypt` computes the decryption; `ct_eq` decides equality of encoded
ciphertexts. -/
structure PkeHom (I : MlkemFo.MlkemFoDeps) [Fintype D] [Nonempty D] (P : Scheme PK SK M C R)
    (hpk : PK → Hash) (kg : D → PK × SK) (E : FoCodecs PK SK M C R K Hash Z D) : Prop where
  keygen_eq : P.keygen = (PMF.uniformFintype D).map kg
  kpke_keygen_enc : ∀ d, I.kpke_keygen (E.seed d) = (E.pk.enc (kg d).1, E.sk (kg d).2)
  h_enc : ∀ pk, I.h (E.pk.enc pk) = E.hash.enc (hpk pk)
  encrypt_enc : ∀ pk m r,
    I.kpke_encrypt (E.pk.enc pk) (E.msg.enc m) (E.coins r) = E.ct.enc (P.enc pk m r)
  decrypt_enc : ∀ d c, ∃ m, P.dec (kg d).2 c = some m ∧
    I.kpke_decrypt (E.sk (kg d).2) (E.ct.enc c) = E.msg.enc m
  ct_eq_enc : ∀ c c', I.ct_eq (E.ct.enc c) (E.ct.enc c') = decide (c = c')

/-- `PkeHom` together with the interpretation of the fields `g` and `j` of `I` by the
oracle functions `g` and `j`. -/
structure FoHom (I : MlkemFo.MlkemFoDeps) [Fintype D] [Nonempty D] (P : Scheme PK SK M C R)
    (hpk : PK → Hash) (kg : D → PK × SK) (E : FoCodecs PK SK M C R K Hash Z D)
    (g : M × Hash → K × R) (j : Z × C → K) : Prop extends PkeHom I P hpk kg E where
  g_enc : ∀ m x, I.g (E.msg.enc m) (E.hash.enc x) = (E.key.enc (g (m, x)).1, E.coins (g (m, x)).2)
  j_enc : ∀ z c, I.j (E.seedZ.enc z) (E.ct.enc c) = E.key.enc (j (z, c))

variable [Fintype D] [Nonempty D] {I : MlkemFo.MlkemFoDeps} {P : Scheme PK SK M C R}
  {hpk : PK → Hash} {kg : D → PK × SK} {E : FoCodecs PK SK M C R K Hash Z D}

/-- The extracted `keygen` on the encoded seeds returns the encoded public key of `kg d`
and the decapsulation key `dkOf`. -/
theorem keygen_enc (hH : PkeHom I P hpk kg E) (d : D) (z : Z) :
    @MlkemFo.keygen I (E.seed d) (E.seedZ.enc z) =
      (E.pk.enc (kg d).1, E.dkOf hpk (kg d).2 (kg d).1 z) := by
  rw [@keygen_layout I _ _ (by rw [hH.kpke_keygen_enc]; exact E.pk_size _)
    (by rw [hH.kpke_keygen_enc]; exact E.sk_size _)
    (by rw [hH.kpke_keygen_enc, hH.h_enc]; exact E.hash_size _) (E.z_size _)]
  simp only [hH.kpke_keygen_enc, hH.h_enc, FoCodecs.dkOf]

/-- The extracted `decaps` on `dkOf` decrypts to the message `m` of `P` and returns the
key of `g` at `(m, hpk pk)` when the re-encryption under the coins of `g` is the
ciphertext, and the value of `j` at `(z, c)` otherwise. -/
theorem decaps_dkOf (hH : PkeHom I P hpk kg E) (I' : MlkemFo.MlkemFoDeps)
    (hdec : I'.kpke_decrypt = I.kpke_decrypt) (henc : I'.kpke_encrypt = I.kpke_encrypt)
    (hct : I'.ct_eq = I.ct_eq) (d : D) (z : Z) (c : C) :
    ∃ m, P.dec (kg d).2 c = some m ∧
      @MlkemFo.decaps I' (E.dkOf hpk (kg d).2 (kg d).1 z) (E.ct.enc c) =
        if I.ct_eq (E.ct.enc c) (I.kpke_encrypt (E.pk.enc (kg d).1) (E.msg.enc m)
            (I'.g (E.msg.enc m) (E.hash.enc (hpk (kg d).1))).2) then
          (I'.g (E.msg.enc m) (E.hash.enc (hpk (kg d).1))).1
        else I'.j (E.seedZ.enc z) (E.ct.enc c) := by
  obtain ⟨m, hm, hd⟩ := hH.decrypt_enc d c
  refine ⟨m, hm, ?_⟩
  rw [FoCodecs.dkOf, @decaps_layout I' _ _ _ _ _ (E.sk_size _) (E.pk_size _) (E.hash_size _)
    (E.z_size _)]
  simp only [hdec, henc, hct, hd]

/-- `I` with the constant answers `gv` and `jv` in the fields `g` and `j`. -/
@[instance_reducible]
def withRO (I : MlkemFo.MlkemFoDeps) (gv : Array Int × Array Int) (jv : Array Int) :
    MlkemFo.MlkemFoDeps :=
  { I with g := fun _ _ => gv, j := fun _ _ => jv }

section WithRO

variable (I : MlkemFo.MlkemFoDeps) (gv : Array Int × Array Int) (jv : Array Int)

/-- Unfolding lemma of `withRO`: the field `g` answers `gv`. -/
@[simp] theorem withRO_g (a b : Array Int) : (withRO I gv jv).g a b = gv := rfl
/-- Unfolding lemma of `withRO`: the field `j` answers `jv`. -/
@[simp] theorem withRO_j (a b : Array Int) : (withRO I gv jv).j a b = jv := rfl
/-- Unfolding lemma of `withRO`: encryption is that of `I`. -/
@[simp] theorem withRO_kpke_encrypt : (withRO I gv jv).kpke_encrypt = I.kpke_encrypt := rfl
/-- Unfolding lemma of `withRO`: decryption is that of `I`. -/
@[simp] theorem withRO_kpke_decrypt : (withRO I gv jv).kpke_decrypt = I.kpke_decrypt := rfl
/-- Unfolding lemma of `withRO`: the ciphertext comparison is that of `I`. -/
@[simp] theorem withRO_ct_eq : (withRO I gv jv).ct_eq = I.ct_eq := rfl
/-- Unfolding lemma of `withRO`: the hash `h` is that of `I`. -/
@[simp] theorem withRO_h : (withRO I gv jv).h = I.h := rfl

end WithRO

/-! ## The extracted functions against fixed oracles -/

section Fixed

variable [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] [Nonempty R] [Nonempty K]
  {g : M × Hash → K × R} {j : Z × C → K}

omit [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] [Nonempty R] [Nonempty K] in
/-- The extracted `encaps` on the encoded public key and message returns the encoded key
and ciphertext of `fips203`'s encapsulation of `m` against `fixedRO2 g j`
(`run_encaps_fixed`): `(g (m, hpk pk)).1` and `P.enc pk m (g (m, hpk pk)).2`. -/
theorem encaps_enc (hF : FoHom I P hpk kg E g j) (pk : PK) (m : M) :
    @MlkemFo.encaps I (E.pk.enc pk) (E.msg.enc m) =
      (E.key.enc (g (m, hpk pk)).1, E.ct.enc (P.enc pk m (g (m, hpk pk)).2)) := by
  simp only [MlkemFo.encaps, hF.h_enc, hF.g_enc, hF.encrypt_enc]

/-- The extracted `decaps` on the key `dkOf` of the key pair `kg d` and the seed `z`
returns the encoding of the key that `fips203`'s decapsulation of `c` returns against
`fixedRO2 g j`. -/
theorem decaps_enc (hF : FoHom I P hpk kg E g j) (d : D) (z : Z) (c : C) :
    ∃ k, @MlkemFo.decaps I (E.dkOf hpk (kg d).2 (kg d).1 z) (E.ct.enc c) = E.key.enc k ∧
      OracleAdv.run (fixedRO2 g j) ((fips203 P hpk).decaps ((kg d).2, (kg d).1, z) c) () =
        PMF.pure (some k, ()) := by
  obtain ⟨m, hm, hd⟩ := decaps_dkOf hF.toPkeHom I rfl rfl rfl d z c
  rw [hd, hF.g_enc, hF.encrypt_enc, hF.ct_eq_enc, hF.j_enc]
  by_cases he : P.enc (kg d).1 m (g (m, hpk (kg d).1)).2 = c
  · refine ⟨(g (m, hpk (kg d).1)).1, by simp [he], ?_⟩
    simp [fips203, hm, he, OracleAdv.run_bind, PMF.pure_bind]
  · refine ⟨j (z, c), by simp [Ne.symm he], ?_⟩
    simp [fips203, hm, he, OracleAdv.run_bind, PMF.pure_bind]

end Fixed

/-! ## The KEM of the extracted functions -/

section ROM

variable [Fintype M] [Nonempty M] [Fintype Z] [Nonempty Z] [Nonempty R] [Nonempty K]
  [Nonempty PK] [Nonempty Hash] [Nonempty C]

variable (I E) in
/-- The KEM in the two-oracle random-oracle model whose algorithms are the extracted
functions. Key generation runs the extracted `keygen` on a uniform seed and a uniform `z`
and decodes the public key; the secret key is the decapsulation key `dk`. Encapsulation of
`m` queries `G` at `(m, H(ek))` and runs the extracted `encaps` with the answer in the
field `g`. Decapsulation of `c` under `dk` queries `G` at the decryption of `c` under the
first 1152 bytes of `dk` and the hash in bytes 2336 to 2368, and runs the extracted
`decaps` with the answer in the field `g` and two distinct values in the field `j`; when
the two outputs agree it returns them, otherwise it queries `J` at the seed in bytes 2368
to 2400 and `c`, and returns the extracted `decaps` run with that answer in the field
`j`. -/
noncomputable def extFO : ROM2Scheme PK (Array Int) K C (M × Hash) (K × R) (Z × C) K where
  keygen := (PMF.uniformFintype D).bind fun d => (PMF.uniformFintype Z).map fun z =>
    (E.pk.decD (@MlkemFo.keygen I (E.seed d) (E.seedZ.enc z)).1,
      (@MlkemFo.keygen I (E.seed d) (E.seedZ.enc z)).2)
  encaps pk := .rand (PMF.uniformFintype M) fun m =>
    (gQ (Z := Z) (C := C) (m, E.hash.decD (I.h (E.pk.enc pk)))).bind fun kr =>
      let kc := @MlkemFo.encaps (withRO I (E.key.enc kr.1, E.coins kr.2) #[]) (E.pk.enc pk)
        (E.msg.enc m)
      .ret (E.key.decD kc.1, E.ct.decD kc.2)
  decaps dk c :=
    (gQ (Z := Z) (C := C) (E.msg.decD (I.kpke_decrypt (dk.extract 0 1152) (E.ct.enc c)),
        E.hash.decD (dk.extract 2336 2368))).bind fun kr =>
      let run := fun jv => @MlkemFo.decaps (withRO I (E.key.enc kr.1, E.coins kr.2) jv) dk
        (E.ct.enc c)
      if run #[0] = run #[1] then .ret (some (E.key.decD (run #[0])))
      else (jQ (M := M) (Hash := Hash) (R := R) (E.seedZ.decD (dk.extract 2368 2400), c)).bind
        fun k => .ret (some (E.key.decD (run (E.key.enc k))))

/-- Key generation of `extFO` draws the seed of `kg` and `z`, and returns the public key of
`kg d` and `dkOf`. -/
theorem extFO_keygen (hH : PkeHom I P hpk kg E) :
    (extFO I E).keygen = (PMF.uniformFintype D).bind fun d =>
      (PMF.uniformFintype Z).map fun z => ((kg d).1, E.dkOf hpk (kg d).2 (kg d).1 z) := by
  simp only [extFO, keygen_enc hH, Codec.decD_enc]

omit [Nonempty PK] [Nonempty Hash] [Nonempty C] in
/-- Key generation of `fips203 P hpk` over the seed of `kg`. -/
theorem fips203_keygen (hH : PkeHom I P hpk kg E) :
    (fips203 (K := K) P hpk).keygen = (PMF.uniformFintype D).bind fun d =>
      (PMF.uniformFintype Z).map fun z => ((kg d).1, ((kg d).2, (kg d).1, z)) := by
  simp only [fips203, hH.keygen_eq, PMF.bind_map]
  rfl

/-- Encapsulation of `extFO` is encapsulation of `fips203 P hpk`. -/
theorem extFO_encaps (hH : PkeHom I P hpk kg E) (pk : PK) :
    (extFO I E).encaps pk = (fips203 (K := K) P hpk).encaps pk := by
  simp only [extFO, fips203, hH.h_enc, Codec.decD_enc, MlkemFo.encaps, withRO_g, withRO_h,
    withRO_kpke_encrypt, hH.encrypt_enc]

/-- Decapsulation of `extFO` under `dkOf` is decapsulation of `fips203 P hpk` under the
secret key `(sk, pk, z)`, for every key pair `(pk, sk)` of `kg`. -/
theorem extFO_decaps (hH : PkeHom I P hpk kg E) (d : D) (z : Z) (c : C) :
    (extFO I E).decaps (E.dkOf hpk (kg d).2 (kg d).1 z) c =
      (fips203 P hpk).decaps ((kg d).2, (kg d).1, z) c := by
  obtain ⟨m, hm, hd⟩ := hH.decrypt_enc d c
  have hrun : ∀ (kr : K × R) (jv : Array Int),
      @MlkemFo.decaps (withRO I (E.key.enc kr.1, E.coins kr.2) jv)
          (E.dkOf hpk (kg d).2 (kg d).1 z) (E.ct.enc c) =
        if P.enc (kg d).1 m kr.2 = c then E.key.enc kr.1 else jv := by
    intro kr jv
    obtain ⟨m', hm', hd'⟩ := decaps_dkOf hH (withRO I (E.key.enc kr.1, E.coins kr.2) jv)
      rfl rfl rfl d z c
    rw [hm] at hm'
    cases hm'
    rw [hd']
    simp only [withRO_g, withRO_j, hH.encrypt_enc, hH.ct_eq_enc]
    by_cases he : P.enc (kg d).1 m kr.2 = c <;> simp [he, Ne.symm]
  simp only [FoCodecs.dkOf] at hrun ⊢
  simp only [extFO, fips203, hm, layout_extract_dkPke _ _ _ _ (E.sk_size _),
    layout_extract_hash _ _ _ _ (E.sk_size _) (E.pk_size _) (E.hash_size _),
    layout_extract_z _ _ _ _ (E.sk_size _) (E.pk_size _) (E.hash_size _) (E.z_size _), hd,
    Codec.decD_enc, hrun]
  congr 1
  funext kr
  by_cases he : P.enc (kg d).1 m kr.2 = c <;> simp [he]

variable [DecidableEq M] [DecidableEq Hash] [DecidableEq Z] [Fintype R] [Fintype K]

/-- **The IND-CCA game of the extracted functions is that of `fips203`.** For every
adversary `A` and bit `b`, the IND-CCA experiment of `extFO I E` is the IND-CCA experiment
of `fips203 P hpk`, when the K-PKE operations, `H` and `ct_eq` of `I` interpret `P` and
`hpk`. -/
theorem rom2INDCCAGame_extFO (hH : PkeHom I P hpk kg E) {qRO qD : ℕ}
    (A : ROM2INDCCAAdversary PK K C (M × Hash) (K × R) (Z × C) K qRO qD) (b : Bool) :
    rom2INDCCAGame (extFO I E) A b = rom2INDCCAGame (fips203 P hpk) A b := by
  have horacle : ∀ (d : D) (z : Z) (cstar : C),
      rom2CCAOracle (extFO I E) (E.dkOf hpk (kg d).2 (kg d).1 z) cstar =
        rom2CCAOracle (fips203 P hpk) ((kg d).2, (kg d).1, z) cstar := by
    intro d z cstar
    funext T q
    cases q with
    | inl q => rfl
    | inr c => simp only [rom2CCAOracle, extFO_decaps hH]
  unfold rom2INDCCAGame
  rw [extFO_keygen hH, fips203_keygen hH]
  simp only [PMF.bind_bind, PMF.bind_map, Function.comp_def, extFO_encaps hH, horacle]

/-- The IND-CCA advantage of `extFO I E` is `fips203INDCCAAdvantage P hpk`. -/
theorem extFO_indcca_eq (hH : PkeHom I P hpk kg E) {qRO qD : ℕ}
    (B : ROM2INDCCAAdversary PK K C (M × Hash) (K × R) (Z × C) K qRO qD) :
    rom2INDCCAAdvantage (extFO I E) B = fips203INDCCAAdvantage P hpk B := by
  simp only [rom2INDCCAAdvantage, fips203INDCCAAdvantage, rom2INDCCAGame_extFO hH]

/-- **IND-CCA security of the extracted ML-KEM transform in the random-oracle model.**
For every IND-CCA adversary `B` against `extFO I E`, the KEM whose algorithms are the
extracted `keygen`, `encaps` and `decaps`, asking at most `qRO` random-oracle queries, the
bound of `fips203_indcca` holds with the reductions `redROM P hpk B` against the one-wayness
of `P`, when the K-PKE operations, `H` and `ct_eq` of `I` interpret `P` and `hpk`
(`PkeHom`). -/
theorem extFO_indcca (hH : PkeHom I P hpk kg E) {qRO qD : ℕ}
    (B : ROM2INDCCAAdversary PK K C (M × Hash) (K × R) (Z × C) K qRO qD) :
    rom2INDCCAAdvantage (extFO I E) B ≤
      owcpaAdvantage P (PKE.FOTransformT.tReductionC P (redROM P hpk B)) +
        ((qRO + qRO + 1 : ℕ) : ℝ≥0∞) * P.corrWorst + P.corrErr +
        ((qRO + qRO + 1 : ℕ) : ℝ≥0∞) *
          owcpaAdvantage P (PKE.FOTransformT.tReductionD P (redROM P hpk B) (qRO + qRO)) +
        (qRO : ℝ≥0∞) / Fintype.card Z + P.corrErr := by
  rw [extFO_indcca_eq hH]
  exact fips203_indcca P hpk B

end ROM

end CatCrypt.Crypto.KEM.MlkemFo.SurfaceDeps
