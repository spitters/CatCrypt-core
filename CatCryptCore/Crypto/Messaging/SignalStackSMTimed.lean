/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.SignalStackSM

/-!
# Running time of the reduction of the Signal stack to the corruption game

Time certificate for the reduction `smHopRed` of `CatCryptCore.Crypto.Messaging.SignalStackSM`.

The reduction `smHopRed M ini Sch t n ΔFS ΔPCS i j Z` is the `j`-th hybrid of the
multi-challenge adversary `smHopAdv Sch t (hopRed i Z)`. Its costed form `smHopRed.timed` is the
costed hybrid reduction `SMSchemeAdv.hybPlayTimed` applied to the costed tree `smHopPlay.timed`
of a costed schedule, with the cost `DCost` of the output bit of `hopRed i Z` and the step cost
`u` of the handler as parameters. It erases to the play of `smHopRed` at the erased schedule
(`smHopRed.erase_timed`), and for a schedule of time `tS` with at most `q` queries and an output
bit of cost at most `tD` it takes time at most `1 + SchCost T₀ + tS + tD + 7 + q * (u + 2)`
(`smHopRed.stepTimeBound_timed`).

No module imports this file.

## Main results

* `smHopRed.timed` — the costed form of the reduction
* `smHopRed.erase_timed` — its erasure is the play of `smHopRed`
* `smHopRed.stepTimeBound_timed` — its time bound
-/

set_option autoImplicit false

@[expose] public section

namespace CatCrypt.Crypto.Messaging.SignalStackSM

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Messaging
open CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.FAKE
open CatCrypt.Crypto.Messaging.SignalStackUC
open OracleAdv.Timed

variable {K Sst Pub Rand Wd Ct Leak V : Type} [Fintype Rand] [Nonempty Rand] [Fintype K]
  [Nonempty K] [Inhabited K]

/-- **The costed reduction `smHopRed`**: the costed `j`-th hybrid, at the handler step cost `u`,
of the costed tree of `smHopPlay` over the costed schedule `Sch` and the distinguisher
`hopRed i Z` of the views of the erased schedule, whose output bit at `v` costs `DCost v`. -/
noncomputable def smHopRed.timed (M : SMScheme Sst Pub Rand Wd Ct Leak)
    (ini : K → SPComp (Pub × Sst × Sst))
    (Sch : Pub → OracleAdv.Timed (SMQuery Wd) (SMSchemeAns Pub Ct Leak) V) (SchCost : Pub → ℕ)
    (DCost : V → ℕ) (t n ΔFS ΔPCS i j u : ℕ) {ζ : Type}
    (Z : Env (Strat ζ (HEv ⊕ AEv K) (HOut V ⊕ AOut)) ζ) (T₀ : Pub) :
    ℕ × OracleAdv.Timed (SMQuery Wd) (SMSchemeAns Pub Ct Leak) Bool :=
  let D := hopRed (smRealView M ini (fun a => (Sch a).erase) t n ΔFS ΔPCS)
    (smIdealView M ini (fun a => (Sch a).erase) t n ΔFS ΔPCS) i Z
  delay (smHopPlay.timed Sch SchCost D DCost T₀).1
    (SMSchemeAdv.hybPlayTimed M t n j u (smHopPlay.timed Sch SchCost D DCost T₀).2)

/-- **Erasure of the costed reduction.** The costed form of `smHopRed` erases to the play, at
the challenge epoch `t` and the public value `T₀`, of `smHopRed` over the erased schedule. -/
theorem smHopRed.erase_timed (M : SMScheme Sst Pub Rand Wd Ct Leak)
    (ini : K → SPComp (Pub × Sst × Sst))
    (Sch : Pub → OracleAdv.Timed (SMQuery Wd) (SMSchemeAns Pub Ct Leak) V) (SchCost : Pub → ℕ)
    (DCost : V → ℕ) (t n ΔFS ΔPCS i j u : ℕ) {ζ : Type}
    (Z : Env (Strat ζ (HEv ⊕ AEv K) (HOut V ⊕ AOut)) ζ) (T₀ : Pub) :
    (smHopRed.timed M ini Sch SchCost DCost t n ΔFS ΔPCS i j u Z T₀).2.erase =
      (smHopRed M ini (fun a => (Sch a).erase) t n ΔFS ΔPCS i j Z).play t T₀ := by
  simp only [smHopRed.timed, delay, SMSchemeAdv.hybPlayTimed, erase_bind,
    erase_simulate, smHybImplTimed, erase_ofAdv, smHopPlay.erase_timed]
  rfl

/-- **Time of the costed reduction.** For a costed schedule `Sch` whose tree at `T₀` takes time
at most `tS` and asks at most `q` queries, and an output bit of `hopRed i Z` of cost at most
`tD` on every view, the costed form of `smHopRed` takes time at most
`1 + SchCost T₀ + tS + tD + 7 + q * (u + 2)`. -/
theorem smHopRed.stepTimeBound_timed (M : SMScheme Sst Pub Rand Wd Ct Leak)
    (ini : K → SPComp (Pub × Sst × Sst))
    (Sch : Pub → OracleAdv.Timed (SMQuery Wd) (SMSchemeAns Pub Ct Leak) V) (SchCost : Pub → ℕ)
    (DCost : V → ℕ) (t n ΔFS ΔPCS i j u : ℕ) {ζ : Type}
    (Z : Env (Strat ζ (HEv ⊕ AEv K) (HOut V ⊕ AOut)) ζ) (T₀ : Pub) {tS tD q : ℕ}
    (hS : (Sch T₀).TimeBound tS) (hD : ∀ v, DCost v ≤ tD)
    (hq : (Sch T₀).erase.IsQueryBound q) :
    StepTimeBound (smHopRed.timed M ini Sch SchCost DCost t n ΔFS ΔPCS i j u Z T₀)
      (1 + SchCost T₀ + (tS + (tD + 7)) + q * (u + 2)) := by
  unfold smHopRed.timed
  exact (smHopRed.timeBound_timed M Sch SchCost _ DCost t n j u T₀ hS hD hq).2

end CatCrypt.Crypto.Messaging.SignalStackSM
