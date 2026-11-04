/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.SDist
public import CatCryptCore.Crypto.CryptoWord
public import CatCryptCore.Crypto.HybridArgument

/-!
# Epoch hybrid for the multi-epoch ratchet chain

The per-distinguisher bound between the computational n-epoch ratchet chain and the idealized
chain: for every initial heap and every distinguisher `D`, the gap is at most the sum over the
epochs `i < n` of the advantage of an explicit reduction against the per-epoch secret sampler
and the advantage of an explicit reduction against the root-key stretch.

## The two chains

Both chains are the fold `ratchetChain` over the corruption schedule `bs : List Bool`, the
instance of the generic epoch fold `HybridArgument.epochFold` with the root as the explicit
state, parametric over two per-epoch samplers:

* `cka : Unit → SPComp W` — the per-epoch CKA secret. Idealized: a uniform
  `SPComp.sample W` (`ckaIdeal`). Computational: any sampler.
* `stretch : W × W → SPComp W` — the root-key stretch combining the current root with the
  fresh secret. Idealized: the pure abstract KDF `stretchIdeal kdf` (a perfect KDF).
  Computational: any sampler family.

The schedule bit only selects what the view records per epoch (the whole new root at a
corrupted epoch, the epoch key at a clean one); the computation is schedule-independent. Per
epoch the idealized chain draws a uniform fresh secret `r`, updates the root to `kdf rk r` and
records `cond b (kdf rk r) (out (kdf rk r))`.

## Main definitions

* `ratchetChain` — the schedule fold, parametric over both samplers
* `ckaIdeal`, `stretchIdeal` — the idealized samplers (uniform secret, pure KDF)

## Main results

* `ratchet_chain_advantage_le` — the instance of `HybridArgument.epochFold_advantage_le` for
  the chain with the samplers `cka`, `prg` against the chain with the idealized samplers
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Signal.RatchetChainHybrid

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.HybridArgument

open scoped ENNReal

/-! ## The ratchet chain -/

variable {W : Type}

/-- The n-epoch ratchet fold, parametric over the per-epoch CKA sampler
    and the root-key stretch: `epochFold` with the root as the explicit
    state. Per epoch: draw the fresh secret `r`, stretch the current root
    `rk` with `r` into the next root `k`, record the view entry (`k` itself
    at a corrupted epoch, `out k` at a clean one), recurse on `k`. -/
noncomputable def ratchetChain (cka : Unit → SPComp W)
    (stretch : W × W → SPComp W) (out : W → W) :
    List Bool → W → SPComp (List W) :=
  epochFold SPComp.pure SPComp.pure out cka stretch

@[simp] theorem ratchetChain_nil (cka : Unit → SPComp W)
    (stretch : W × W → SPComp W) (out : W → W) (rk : W) :
    ratchetChain cka stretch out [] rk = SPComp.pure [] := rfl

theorem ratchetChain_cons (cka : Unit → SPComp W)
    (stretch : W × W → SPComp W) (out : W → W) (b : Bool) (bs : List Bool)
    (rk : W) :
    ratchetChain cka stretch out (b :: bs) rk =
      (SPComp.bind (cka ()) fun r =>
       SPComp.bind (stretch (rk, r)) fun k =>
       SPComp.bind (ratchetChain cka stretch out bs k) fun ks =>
       SPComp.pure (cond b k (out k) :: ks)) := by
  simp only [ratchetChain, epochFold, SPComp.pure_bind]

/-! ## The idealized samplers -/

/-- Idealized per-epoch CKA secret: a fresh uniform sample. -/
noncomputable def ckaIdeal (W : Type) [SampleableType W] : Unit → SPComp W :=
  fun _ => SPComp.sample W

/-- Idealized root-key stretch: the pure abstract KDF (a perfect stretch). -/
noncomputable def stretchIdeal (kdf : W → W → W) : W × W → SPComp W :=
  fun p => SPComp.pure (kdf p.1 p.2)

/-! ## The epoch hybrid -/

/-- **Epoch hybrid, per distinguisher.** From every initial heap `h₀` and
    initial root `rk`, every distinguisher `D` of the chain with the samplers `cka` and `prg`
    and the chain with the idealized samplers `ckaIdeal W` and `stretchIdeal kdf` has gap at
    most the sum over the epochs `i < n` of the advantage of `secHybRed … i` against `cka`
    (versus `ckaIdeal W`) and the advantage of `stretchHybRed … i` against `prg` (versus
    `stretchIdeal kdf`). The instance of `epochFold_advantage_le` at the root carried as the
    fold state. -/
theorem ratchet_chain_advantage_le [SampleableType W]
    (cka : Unit → SPComp W) (prg : W × W → SPComp W)
    (kdf : W → W → W) (out : W → W) (bs : List Bool) (rk : W) (h₀ : Heap)
    (D : List W → SPComp Bool) :
    absDiff (prTrue (SPComp.bind (ratchetChain cka prg out bs rk) D) h₀)
        (prTrue (SPComp.bind (ratchetChain (ckaIdeal W) (stretchIdeal kdf) out bs rk) D) h₀) ≤
      epochFoldBound SPComp.pure SPComp.pure out cka prg (ckaIdeal W)
        (stretchIdeal kdf) bs rk h₀ D :=
  epochFold_advantage_le SPComp.pure SPComp.pure out cka prg (ckaIdeal W)
    (stretchIdeal kdf) bs rk h₀ D

end CatCrypt.Crypto.Signal.RatchetChainHybrid
