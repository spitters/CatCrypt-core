/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.RecordRounds
public import CatCryptCore.Quantum.QROM.KEMAdvDilate

/-!
# The single-run adversary of a general multi-round adversary

A general multi-round adversary `B : QAdvMRGen m n w q k c a` has local operations that are
trace-preserving completely positive maps. Its single-run adversary `B.toQAdv f` at the round
table `f` is the single-run adversary `toQAdv (dilate B) f` of its unitary dilation: every local
operation is replaced by a unitary on an ancilla (`dilate`), and the `k` rounds are run as
deferred measurements, round `j` copying its outcome into ancilla `j` of the work register
`ancW c k (w * dilDim m n w q k)` (`flatten`). It makes `flatQ q k q` oracle queries.

## Main definitions

* `QAdvMRGen.toQAdv B f` — the single-run adversary of `B` at the round table `f`

## Main results

* `QAdvMRGen.prOut_toQAdv` — `B.toQAdv f` accepts with the probability `prOutMRGen B H f`
* `QAdvMRGen.prOut_withFinalB_toQAdv` — a diagonal final test `G` of `B.toQAdv f`, which may
  read the round outcomes from the ancillas, accepts with the probability of the general
  adversary `recordGen (dilate B) G`, whose rounds are classical rounds of `f`

The semi-classical probabilities `prOutNoFind` and `prFind` of `toQAdv (dilate B) f` are those
of `B` by `prOutNoFindMRGen_eq_toQAdv` and `prFindMRGen_eq_toQAdv` (`RoundOracle`).
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace CatCrypt.Quantum.QROM

variable {m n w q k c a : ℕ} [NeZero c]

/-- The single-run adversary of a general multi-round adversary `B` at the round table `f`:
    the unitary dilation of `B` with its `k` rounds deferred into the ancillas of the work
    register, with `flatQ q k q` oracle queries. -/
def QAdvMRGen.toQAdv (B : QAdvMRGen m n w q k c a) (f : Fin c → Fin a) :
    QAdv m n (ancW c k (w * dilDim m n w q k)) (flatQ q k q) :=
  CatCrypt.Quantum.QROM.toQAdv (dilate B) f

variable [NeZero n]

/-- The single-run adversary of `B` accepts with the probability of `B`. -/
theorem QAdvMRGen.prOut_toQAdv (B : QAdvMRGen m n w q k c a) (f : Fin c → Fin a)
    (H : Fin m → Fin n) : prOut (B.toQAdv f) H = prOutMRGen B H f :=
  (prOutMR_eq (dilate B) H f).symm.trans (prOutMR_dilate B H f)

/-- A diagonal final test `G` of the single-run adversary of `B` accepts with the probability
    of the general adversary that records the round outcomes of the dilation of `B` in the
    ancillas, measures its rounds and has the final projector `diagB G`. -/
theorem QAdvMRGen.prOut_withFinalB_toQAdv (B : QAdvMRGen m n w q k c a) (f : Fin c → Fin a)
    (G : Fin (m * n * ancW c k (w * dilDim m n w q k)) → Bool) (H : Fin m → Fin n) :
    prOut ((B.toQAdv f).withFinalB G) H = prOutMRGen (recordGen (dilate B) G) H f :=
  prOut_withFinalB_toQAdv_eq (dilate B) f G H

end CatCrypt.Quantum.QROM
