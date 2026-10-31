/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.CryptoWord
public import CatCryptCore.Crypto.PRPPRFSwitching

/-!
# Circular correlation robustness

A function `H : W → ℕ → W` on labels with an XOR operation `xor`, unit `zero` and least
significant bit `lsb` is circular correlation robust when no adversary distinguishes the oracle

  `O_Δ (x, j, b) = H (x ⊕ Δ) j ⊕ (if b then Δ else zero)`

for a uniform offset `Δ` with `lsb Δ = true` from a random function of `(x, j, b)`. The offset
is `r` if `lsb r` and `r ⊕ one` otherwise, for a uniform label `r`.

The adversary is an adaptive oracle adversary (`OracleAdv`). A query `(x, j, b)` after a
recorded query `(x, j, ¬ b)` is illegal (`ccrIllegal`): in the real world the two answers XOR to
`Δ`. Both oracles answer an illegal query with `zero` and do not record it, so the advantage is
defined for every adversary and the legality condition of the definition is a property of the
game. `H` is a parameter; no random oracle enters.

## Main definitions

* `ccrIllegal` — the query conflicts with a recorded query in its bit
* `ccrRealOracle`, `ccrIdealOracle` — the oracle `O_Δ` and the lazily sampled random function,
  both answering illegal queries with `zero`
* `ccrReal`, `ccrIdeal` — the two games
* `ccrAdvantage` — the circular correlation robustness advantage

## Main results

* `ccrRealOracle_of_legal`, `ccrIdealOracle_of_legal` — the oracles on a legal query

## References

* S. G. Choi, J. Katz, R. Kumaresan, H.-S. Zhou, *On the Security of the "Free-XOR"
  Technique*, TCC 2012, Definition 2
* S. Zahur, M. Rosulek, D. Evans, *Two Halves Make a Whole*, EUROCRYPT 2015, Definition 1
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Assumptions

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.PRPPRF
open scoped ENNReal

variable {W : Type} [SampleableType W]

/-- A circular correlation robustness adversary: an adaptive oracle adversary with queries
`(x, j, b)` and label answers. -/
abbrev CCRAdversary (W : Type) := OracleAdv (W × ℕ × Bool) W Bool

/-- The query `q = (x, j, b)` is illegal after the recorded queries `t`: some recorded query
is `(x, j, b')` with `b' ≠ b`. -/
def ccrIllegal (t : List (W × ℕ × Bool)) (q : W × ℕ × Bool) : Bool :=
  t.any fun e => decide (e.1 = q.1 ∧ e.2.1 = q.2.1 ∧ e.2.2 ≠ q.2.2)

/-- The real oracle under the offset `Δ`, with the legal queries as state: a legal query
`(x, j, b)` is answered `H (x ⊕ Δ) j ⊕ (if b then Δ else zero)` and recorded; an illegal query
is answered `zero`. -/
noncomputable def ccrRealOracle (xor : W → W → W) (zero : W) (H : W → ℕ → W) (Δ : W)
    (t : List (W × ℕ × Bool)) (q : W × ℕ × Bool) : PMF (W × List (W × ℕ × Bool)) :=
  if ccrIllegal t q then PMF.pure (zero, t)
  else PMF.pure (xor (H (xor q.1 Δ) q.2.1) (if q.2.2 then Δ else zero), q :: t)

/-- The ideal oracle, with the lazy-sampling table as state: a legal query is answered by the
lazily sampled random function `rfOracle`; an illegal query is answered `zero`. -/
noncomputable def ccrIdealOracle (zero : W) (t : List ((W × ℕ × Bool) × W))
    (q : W × ℕ × Bool) : PMF (W × List ((W × ℕ × Bool) × W)) :=
  if ccrIllegal (t.map Prod.fst) q then PMF.pure (zero, t) else rfOracle t q

/-- The real game: sample a label `r`, take the offset `Δ = r` if `lsb r` and `r ⊕ one`
otherwise, and run `B` against `ccrRealOracle` under `Δ`. -/
noncomputable def ccrReal (xor : W → W → W) (zero one : W) (lsb : W → Bool) (H : W → ℕ → W)
    (B : CCRAdversary W) : SPComp Bool :=
  liftPMF ((PMF.uniformFintype W).bind fun r =>
    (OracleAdv.run (ccrRealOracle xor zero H (if lsb r then r else xor r one)) B []).map
      Prod.fst)

/-- The ideal game: run `B` against the lazily sampled random function from the empty
table. -/
noncomputable def ccrIdeal (zero : W) (B : CCRAdversary W) : SPComp Bool :=
  liftPMF ((OracleAdv.run (ccrIdealOracle zero) B []).map Prod.fst)

/-- The circular correlation robustness advantage of `B` against `H`. -/
noncomputable def ccrAdvantage (xor : W → W → W) (zero one : W) (lsb : W → Bool)
    (H : W → ℕ → W) (B : CCRAdversary W) : ℝ≥0∞ :=
  Advantage (ccrReal xor zero one lsb H B) (ccrIdeal zero B)

/-- On a legal query the real oracle answers `H (x ⊕ Δ) j ⊕ (if b then Δ else zero)` and
records the query. -/
theorem ccrRealOracle_of_legal (xor : W → W → W) (zero : W) (H : W → ℕ → W) (Δ : W)
    {t : List (W × ℕ × Bool)} {q : W × ℕ × Bool} (hq : ccrIllegal t q = false) :
    ccrRealOracle xor zero H Δ t q =
      PMF.pure (xor (H (xor q.1 Δ) q.2.1) (if q.2.2 then Δ else zero), q :: t) := by
  simp only [ccrRealOracle, hq, Bool.false_eq_true, ↓reduceIte]

/-- On a legal query the ideal oracle is the lazily sampled random function. -/
theorem ccrIdealOracle_of_legal (zero : W) {t : List ((W × ℕ × Bool) × W)}
    {q : W × ℕ × Bool} (hq : ccrIllegal (t.map Prod.fst) q = false) :
    ccrIdealOracle zero t q = rfOracle t q := by
  simp only [ccrIdealOracle, hq, Bool.false_eq_true, ↓reduceIte]

end CatCrypt.Crypto.Assumptions
