/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.FiatShamirROM.NIZK
public import CatCryptCore.Container.DNCert

/-!
# The forking extractor of the strong Fiat–Shamir transform as a Diller–Nahm composite

The time bound `ksExtractor.timeBound_timed` of `CatCryptCore.Crypto.FiatShamirROM.NIZK` is the
time of a composite of two costed functions with use counts (`Container.Clocked`): the
extractor, which uses the adversary with the challenger's query twice and calls the
special-soundness extractor once at cost `tExt`, after the adversary with the challenger's
query run against the random oracle, which uses the adversary once at the cost of the
challenger's query and of the `qH + 1` oracle steps, each at most `tH + tF + 1`. By
`Clocked.time_comp`, the price of the composite Diller–Nahm morphism at the time `T` of the
adversary is `tExt + 2 * (1 + (tH + tF + 1) * (qH + 1) + T)`.

## Main definitions

* `ksExtractor.clock` — the extractor: two uses, cost `tExt`
* `ksWithVerify.clock` — the adversary with the challenger's query against the oracle: one use,
  cost `1 + (tH + tF + 1) * (qH + 1)`

## Main results

* `ksExtractor.timeBound_clocked` — the costed extractor runs in the time of the composite of
  the two clocks at the time of the adversary
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.FiatShamirROM

open CatCrypt.Container CatCrypt.Crypto CatCrypt.Crypto.OracleForking

/-- The clock of the forking extractor: the adversary with the challenger's query is used twice,
and the special-soundness extractor is called once at cost `tExt`. -/
def ksExtractor.clock (tExt : ℕ) : Clocked Unit Unit where
  fn _ := ()
  uses _ := 2
  cost _ := tExt

/-- The clock of the adversary with the challenger's query run against the random oracle with
step cost `tH` and fork decision cost `tF`: the adversary is used once, and the challenger's
query and the `qH + 1` oracle steps cost `1 + (tH + tF + 1) * (qH + 1)`. -/
def ksWithVerify.clock (tH tF qH : ℕ) : Clocked Unit Unit where
  fn _ := ()
  uses _ := 1
  cost _ := 1 + (tH + tF + 1) * (qH + 1)

section Knowledge

variable {P : Sigma} {Sid : Type} [DecidableEq Sid] [DecidableEq P.Stmt]

/-- **Time of the forking extractor as a composite.** With `A'` of time `T` and at most `qH`
queries, the costed extractor runs in the time of `Clocked.comp (ksExtractor.clock tExt)
(ksWithVerify.clock tH tF qH)` at `T`: two uses of the adversary with the challenger's query,
each at its own cost and the time of `A'`, and the special-soundness extractor once. -/
theorem ksExtractor.timeBound_clocked {qH : ℕ} (A : KSAdversary P Sid qH)
    {A' : OracleAdv.Timed (P.NizkInput Sid) P.Ch (Sid × P.Stmt × P.NizkProof)}
    (hA : A'.erase = A.run) (tH tF tExt : ℕ) {T : ℕ} (hT : A'.TimeBound T) :
    OracleAdv.Timed.StepTimeBound (ksExtractor.timed tH tF tExt A')
      ((Clocked.comp (ksExtractor.clock tExt) (ksWithVerify.clock tH tF qH)).time T ()) := by
  refine (ksExtractor.timeBound_timed A hA tH tF tExt hT).mono (le_of_eq ?_)
  rw [Clocked.time_comp]
  simp only [Clocked.time, ksExtractor.clock, ksWithVerify.clock]
  ring

end Knowledge

end CatCrypt.Crypto.FiatShamirROM
