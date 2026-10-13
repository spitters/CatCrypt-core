/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Advantage
public import CatCryptCore.Examples.GroupParam

/-!
# The discrete-logarithm game over `GroupParam`

The adversary receives `h = g^w` for a uniform scalar `w` and wins when it returns
some `w'` with `g^w' = h`.

## Main definitions

* `GroupParam.dlGame gp B` — the discrete-logarithm game
* `GroupParam.DL_Advantage gp B` — the probability that `B` wins it
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal

namespace CatCrypt.Examples.GroupParam

variable (gp : GroupParam)

/-- The discrete-logarithm game: sample `w`, give `h = g^w` to the adversary, and
accept its output `w'` when `g^w' = h`. -/
noncomputable def dlGame (adversary : gp.G → SPComp gp.Scalar) : SPComp Bool := do
  let w ← SPComp.sample gp.Scalar
  let h := gp.exp w
  let w' ← adversary h
  SPComp.pure (gp.exp w' == h)

/-- The probability that the adversary wins the discrete-logarithm game. -/
noncomputable def DL_Advantage (adversary : gp.G → SPComp gp.Scalar) : ℝ≥0∞ :=
  prTrue (gp.dlGame adversary) Heap.empty

end CatCrypt.Examples.GroupParam
