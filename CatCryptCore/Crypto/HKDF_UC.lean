/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UC
public import CatCryptCore.Crypto.SDist
public import CatCryptCore.Crypto.Advantage
public import CatCryptCore.Crypto.CryptoWord
public import CatCryptCore.Relational.Rules
public import CatCryptCore.Tactics.Triangle
public import CatCryptCore.Crypto.UCConcrete
public import CatCryptCore.Crypto.UCDSL

/-!
# UC Security of HKDF (Extract-then-Expand)

This file models HKDF as a composition of two PRFs:
- **Extract**: `salt × ikm → prk` (salt is the PRF key)
- **Expand**: `prk × info → okm` (prk is the PRF key)

The composed HKDF game:
```
hkdf(ikm, info) = Expand(Extract(salt, ikm), info)    where salt ← random
```

Security bound via 2-step game hop (triangle through "random PRK"), for every
distinguisher `A`:
```
HKDF_Advantage H ikm info A
  ≤ Extract_Advantage H ikm (hkdfExtractReduction H info A) + Expand_Advantage H info A
```
Both component games are one-shot: the distinguisher receives one output.

This is the standard HKDF security argument from [Krawczyk 2010].

## Main definitions

* `HKDFDef` — HKDF scheme (extract + expand functions)
* `hkdf_real` — real game: Extract then Expand with random salt
* `hkdf_mid` — intermediate game: Expand with random PRK
* `hkdf_ideal` — ideal game: random output

## Main results

* `hkdf_advantage_bound` — `HKDF_Advantage H ikm info A ≤ hkdfBound H (ikm, info) A`
* `hkdf_distC` — concrete distance of the HKDF games
* `hkdf_uc_secure` — concrete UC emulation with bound `gameUCBound (hkdfBound H)`

## References

* [Krawczyk, 2010 — Cryptographic Extraction and Key Derivation: The HKDF Scheme]
* [RFC 5869 — HMAC-based Extract-and-Expand Key Derivation Function]
-/

@[expose] public section

namespace CatCrypt.Crypto.HKDF_UC

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Relational
open scoped ENNReal

variable {W : Type} [SampleableType W]

/-! ## HKDF Definition -/

/-- Abstract HKDF scheme: Extract (salt-keyed PRF) + Expand (PRK-keyed PRF),
parametric over `SampleableType W`.
- `extract salt ikm` = HKDF-Extract: derive pseudorandom key from salt + IKM
- `expand prk info` = HKDF-Expand: derive output keying material from PRK + info -/
structure HKDFDef (W : Type) [SampleableType W] where
  extract : W → W → W
  expand  : W → W → W

/-! ## Component Games -/

/-- Extract real game: sample random salt, compute prk = extract(salt, ikm). -/
noncomputable def extract_real (H : HKDFDef W) (ikm : W) : SPComp W :=
  SPComp.bind (SPComp.sample W) (fun salt => SPComp.pure (H.extract salt ikm))

/-- Extract ideal game: sample random PRK directly. -/
noncomputable def extract_ideal : SPComp W :=
  SPComp.sample W

/-- Expand real game: sample random PRK, compute okm = expand(prk, info). -/
noncomputable def expand_real (H : HKDFDef W) (info : W) : SPComp W :=
  SPComp.bind (SPComp.sample W) (fun prk => SPComp.pure (H.expand prk info))

/-- Expand ideal game: sample random OKM directly. -/
noncomputable def expand_ideal : SPComp W :=
  SPComp.sample W

/-! ## Advantage Definitions -/

/-- Extract advantage: distinguishing Extract(salt, ikm) from random. -/
noncomputable def Extract_Advantage (H : HKDFDef W) (ikm : W)
    (A : W → SPComp Bool) : ENNReal :=
  AdvantageA (extract_real H ikm) extract_ideal A

/-- Expand advantage: distinguishing Expand(prk, info) from random. -/
noncomputable def Expand_Advantage (H : HKDFDef W) (info : W)
    (A : W → SPComp Bool) : ENNReal :=
  AdvantageA (expand_real H info) expand_ideal A

/-! ## Non-Standard HKDF Advantage Variants

### Extract_IKM_Advantage (Dual PRF)

Randomizes the IKM (second argument) instead of the salt (first argument).
This is the "dual PRF" property: HMAC acts as a PRF when keyed by either argument.

**Standard reference**: Krawczyk 2010, *Cryptographic Extraction and Key Derivation:
The HKDF Scheme*, Theorem 2. Also: Bellare 2006, *New Proofs for NMAC and HMAC*.

**Usage**: HPKE (all modes), EDHOC (all methods). Well-founded in the literature.

### Expand_Composed_Advantage (KDM-PRF)

The info argument depends on the PRK via `f : W → W`. Standard PRF security
does NOT imply KDM-PRF security in general; it holds in the ROM/ICM.

**Literature**: Black-Rogaway-Shrimpton 2003 (KDM for encryption); no standard
reference for KDM-PRF specifically.

### Expand_Composed_Leak_Advantage (KDM-PRF + Key Leakage)

Combines KDM with PRK leakage: outputs `(expand(prk, f(prk)), prk)` as a pair.
Non-standard; no reduction from standard Expand is known.

**Literature**: Dodis et al. 2010 (leakage resilience); Dziembowski-Pietrzak 2008.

**Usage**: EDHOC (needed: the suffix accesses `prk_4e3m` for AEAD).
Not needed by HPKE (info is a fixed constant, standard `Expand_Advantage` suffices). -/

/-- Extract with random IKM: sample random IKM, compute prk = extract(salt, ikm). -/
noncomputable def extract_ikm_real (H : HKDFDef W) (salt : W) : SPComp W :=
  SPComp.bind (SPComp.sample W) (fun ikm => SPComp.pure (H.extract salt ikm))

/-- Extract-IKM advantage: distinguishing Extract(salt, random_ikm) from random.
This is the "dual" of `Extract_Advantage` where the IKM is randomized. -/
noncomputable def Extract_IKM_Advantage (H : HKDFDef W) (salt : W)
    (A : W → SPComp Bool) : ENNReal :=
  AdvantageA (extract_ikm_real H salt) extract_ideal A

/-- Expand with key-dependent info: sample random PRK, compute okm = expand(prk, f(prk)). -/
noncomputable def expand_composed_real (H : HKDFDef W) (f : W → W) : SPComp W :=
  SPComp.bind (SPComp.sample W) (fun prk => SPComp.pure (H.expand prk (f prk)))

/-- Expand-Composed advantage: distinguishing Expand(prk, f(prk)) from random
where both the PRK is random and info depends on PRK via `f`. -/
noncomputable def Expand_Composed_Advantage (H : HKDFDef W) (f : W → W)
    (A : W → SPComp Bool) : ENNReal :=
  AdvantageA (expand_composed_real H f) expand_ideal A

/-- Expand with key-dependent info, leaking the PRK: sample random PRK,
output `(expand(prk, f(prk)), prk)` as a pair.

This variant is needed in the EDHOC hybrid argument where replacing
`prk_out` with random requires the suffix to still access `prk_4e3m`
for computing AEAD ciphertexts. -/
noncomputable def expand_composed_leak_real (H : HKDFDef W)
    (f : W → W) : SPComp (W × W) :=
  SPComp.bind (SPComp.sample W) (fun prk =>
    SPComp.pure (H.expand prk (f prk), prk))

/-- Expand-Composed-Leak ideal game: sample independent random pair. -/
noncomputable def expand_composed_leak_ideal : SPComp (W × W) :=
  SPComp.sample (W × W)

/-- Expand-Composed-Leak advantage: distinguishing `(Expand(prk, f(prk)), prk)` from
random pair, where PRK is random and info depends on PRK via `f`. -/
noncomputable def Expand_Composed_Leak_Advantage (H : HKDFDef W) (f : W → W)
    (A : W × W → SPComp Bool) : ENNReal :=
  AdvantageA (expand_composed_leak_real H f) expand_composed_leak_ideal A

/-! ## Composed HKDF Games -/

/-- HKDF real game: Extract then Expand with random salt.
    `hkdf_real(ikm, info) = Expand(Extract(salt, ikm), info)` where `salt ← random`. -/
noncomputable def hkdf_real (H : HKDFDef W) (ikm info : W) : SPComp W :=
  SPComp.bind (SPComp.sample W) (fun salt =>
    SPComp.pure (H.expand (H.extract salt ikm) info))

/-- HKDF mid game: the Expand real game, the intermediate game where the Extract output is
replaced by a uniform key. -/
noncomputable abbrev hkdf_mid (H : HKDFDef W) (info : W) : SPComp W :=
  expand_real H info

/-- HKDF ideal game: the Expand ideal game, a uniform output. -/
noncomputable abbrev hkdf_ideal : SPComp W :=
  expand_ideal

/-- HKDF advantage: distinguishing real from ideal. -/
noncomputable def HKDF_Advantage (H : HKDFDef W) (ikm info : W)
    (A : W → SPComp Bool) : ENNReal :=
  AdvantageA (hkdf_real H ikm info) hkdf_ideal A

/-! ## Heap independence -/

open CatCrypt.Crypto.UCConcrete

instance extract_real_pureGame (H : HKDFDef W) : PureGame (extract_real H) :=
  ⟨fun _ => SPComp.bind_isPure (SPComp.sample_isPure _) fun _ => SPComp.pure_isPure _⟩

instance extract_ideal_pureGame {hon : Type} :
    PureGame (fun _ : hon => (extract_ideal : SPComp W)) :=
  ⟨fun _ => SPComp.sample_isPure _⟩

instance expand_real_pureGame (H : HKDFDef W) : PureGame (expand_real H) :=
  ⟨fun _ => SPComp.bind_isPure (SPComp.sample_isPure _) fun _ => SPComp.pure_isPure _⟩

instance expand_ideal_pureGame {hon : Type} :
    PureGame (fun _ : hon => (expand_ideal : SPComp W)) :=
  ⟨fun _ => SPComp.sample_isPure _⟩

instance extract_ikm_real_pureGame (H : HKDFDef W) : PureGame (extract_ikm_real H) :=
  ⟨fun _ => SPComp.bind_isPure (SPComp.sample_isPure _) fun _ => SPComp.pure_isPure _⟩

instance expand_composed_real_pureGame (H : HKDFDef W) :
    PureGame (expand_composed_real H) :=
  ⟨fun _ => SPComp.bind_isPure (SPComp.sample_isPure _) fun _ => SPComp.pure_isPure _⟩

instance expand_composed_leak_real_pureGame (H : HKDFDef W) :
    PureGame (expand_composed_leak_real H) :=
  ⟨fun _ => SPComp.bind_isPure (SPComp.sample_isPure _) fun _ => SPComp.pure_isPure _⟩

instance expand_composed_leak_ideal_pureGame {hon : Type} :
    PureGame (fun _ : hon => (expand_composed_leak_ideal : SPComp (W × W))) :=
  ⟨fun _ => SPComp.sample_isPure _⟩

instance hkdf_real_pureGame (H : HKDFDef W) :
    PureGame (fun i : W × W => hkdf_real H i.1 i.2) :=
  ⟨fun _ => SPComp.bind_isPure (SPComp.sample_isPure _) fun _ => SPComp.pure_isPure _⟩

/-! ## Key Decomposition Lemmas -/

/-- The HKDF real game decomposes as: Extract then (pure ∘ expand). -/
theorem hkdf_real_eq_bind (H : HKDFDef W) (ikm info : W) :
    hkdf_real H ikm info =
    SPComp.bind (extract_real H ikm) (fun prk => SPComp.pure (H.expand prk info)) := by
  unfold hkdf_real extract_real
  simp only [SPComp.bind_assoc, SPComp.pure_bind]

/-- The HKDF mid game decomposes as: random PRK then (pure ∘ expand). -/
theorem hkdf_mid_eq_bind (H : HKDFDef W) (info : W) :
    hkdf_mid H info =
    SPComp.bind extract_ideal (fun prk => SPComp.pure (H.expand prk info)) := by
  rfl

/-! ## Security Theorem -/

/-- Extract reduction: runs the HKDF distinguisher `A` once on
`expand prk info`, where `prk` is the Extract challenge. -/
noncomputable def hkdfExtractReduction (H : HKDFDef W) (info : W) (A : W → SPComp Bool) :
    W → SPComp Bool :=
  fun prk => SPComp.bind (SPComp.pure (H.expand prk info)) A

/-- Concrete HKDF bound at input `(ikm, info)` for the distinguisher `A`: the
Extract advantage of `hkdfExtractReduction H info A` plus the Expand advantage
of `A`. -/
noncomputable def hkdfBound (H : HKDFDef W) : W × W → (W → SPComp Bool) → ENNReal :=
  fun i A => Extract_Advantage H i.1 (hkdfExtractReduction H i.2 A) + Expand_Advantage H i.2 A

/-- **HKDF 2-step security bound**: for every distinguisher `A`, the HKDF
advantage is at most the Extract advantage of `hkdfExtractReduction H info A`
plus the Expand advantage of `A`. -/
theorem hkdf_advantage_bound (H : HKDFDef W) (ikm info : W)
    (A : W → SPComp Bool) :
    HKDF_Advantage H ikm info A ≤ hkdfBound H (ikm, info) A := by
  unfold HKDF_Advantage hkdfBound
  -- Triangle inequality through hkdf_mid
  calc AdvantageA (hkdf_real H ikm info) hkdf_ideal A
    _ ≤ AdvantageA (hkdf_real H ikm info) (hkdf_mid H info) A +
        AdvantageA (hkdf_mid H info) hkdf_ideal A :=
        advantageA_triangle _ _ _ A
    _ = Extract_Advantage H ikm (hkdfExtractReduction H info A) +
        Expand_Advantage H info A := by
      -- Step 1: real → mid is the Extract advantage of the reduction
      rw [hkdf_real_eq_bind, hkdf_mid_eq_bind,
        advantage_factorization (fun prk => SPComp.pure (H.expand prk info))]
      rfl

/-! ## UC Specification -/

/-- UC specification for HKDF security.
    - `hon = W × W` (IKM × info)
    - `out = Unit` (no honest output)
    - `leak = sim_if = W` (derived key)
    - `view = V` (adversary-chosen output type) -/
abbrev hkdfSpec (W : Type) [SampleableType W] (V : Type) : UCSpec :=
  UCDSL.UCSpec.ofGame (W × W) W V

/-! ## UC Real and Ideal Protocols -/

/-- Real protocol: HKDF with random salt.
    Output goes through the `.inr` (leak/adversary) channel. -/
noncomputable abbrev hkdfReal (H : HKDFDef W) : W × W → SPComp (Unit ⊕ W) :=
  UCDSL.UCProtocol.ofGame fun i : W × W => hkdf_real H i.1 i.2

/-- Ideal protocol: random output key.
    Output goes through the `.inr` (leak/adversary) channel. -/
noncomputable abbrev hkdfIdeal : W × W → SPComp (Unit ⊕ W) :=
  UCDSL.UCProtocol.ofGame fun _ : W × W => (hkdf_ideal : SPComp W)

/-! ## Concrete distance -/

/-- Concrete distance of the HKDF games: every environment `Z` distinguishes
them with gap at most `hkdfBound H` at its input and its distinguisher with the
heap fixed to `Z.heap`. -/
theorem hkdf_distC (H : HKDFDef W) :
    DistC (fun i : W × W => hkdf_real H i.1 i.2) (fun _ => hkdf_ideal)
      (fun Z => hkdfBound H Z.input (fixHeap Z.heap Z.dist)) :=
  DistC_of_isPure_advantageA PureGame.isPure PureGame.isPure
    (fun i D => hkdf_advantage_bound H i.1 i.2 D)

/-! ## Main UC Theorem -/

/-- Every distinguisher `D` separates the HKDF games at `(ikm, info)` by at most
`hkdfBound H (ikm, info) D` (`hkdf_advantage_bound`). -/
instance hkdf_gameAdvBoundC (H : HKDFDef W) :
    GameAdvBoundC (fun i : W × W => hkdf_real H i.1 i.2) (fun _ => (hkdf_ideal : SPComp W))
      (hkdfBound H) :=
  ⟨fun i D => hkdf_advantage_bound H i.1 i.2 D⟩

/-- **HKDF concrete UC emulation.** For adversary `A` and environment `Z`, the gap is at
most the Extract advantage of `hkdfExtractReduction` plus the Expand advantage, both at the
distinguisher `envReduction A Z` and the environment's input `(ikm, info)`: the two-step
argument of [Krawczyk 2010]. -/
theorem hkdf_uc_secure (H : HKDFDef W) (V : Type) :
    UCEmulatesCSim (hkdfSpec W V) (hkdfReal H) hkdfIdeal id
      (gameUCBound (hkdfBound H)) :=
  UCFromGameC.uc

end CatCrypt.Crypto.HKDF_UC
