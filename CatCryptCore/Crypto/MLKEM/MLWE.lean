/-
Copyright (c) 2024 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.MLKEM.PKE_ROM
public import CatCryptCore.Crypto.PRPPRFSwitching

/-!
# Module Learning With Errors (MLWE) Assumption

This file formalizes the MLWE assumption used in the ML-KEM security proof.
Ports the core definitions from `MLWE.ec` in `formosa-crypto/formosa-mlkem`.

## Design

The algebra is **fully abstract**: we work with abstract types `Vec`, `Mat`, `R`
with abstract operations. No concrete `Rq = Zq[X]/(X^n+1)` is needed for the
security proof. The distributions are also abstract (axiomatized).

## Main definitions

* `MLWE.Params` — MLWE parameters (types, distributions, operations)
* `MLWE.Game` — the basic MLWE distinguishing game
* `MLWE_H.Params` — hashed MLWE variant parameters
* `MLWE_H.Game` — MLWE game with hashed matrix

## References

* EasyCrypt source: `formosa-crypto/formosa-mlkem/proof/security/MLWE.ec`
-/

@[expose] public section

open CatCrypt.Prob
open scoped ENNReal

namespace CatCrypt.Crypto.MLKEM

/-! ## MLWE Game -/

namespace MLWE

/-- Fully abstract MLWE parameters.

    All types and operations are abstract.  Uniform distributions are derived
    from `SDistr.uniform` via `Fintype`/`Nonempty` instances, not passed as fields.

    EasyCrypt: `R`, `vector`, `matrix` abstract types with `duni`, `dshort` distributions
    and `( * )`, `(+)`, `trmx` operations. -/
structure Params where
  /-- The base ring element type -/
  R : Type
  /-- Vector type (abstract, morally `R^k`) -/
  Vec : Type
  /-- Matrix type (abstract, morally `R^{k×k}`) -/
  Mat : Type
  [decR : DecidableEq R]
  [decVec : DecidableEq Vec]
  [finMat : Fintype Mat]
  [neMat : Nonempty Mat]
  [finVec : Fintype Vec]
  [neVec : Nonempty Vec]
  /-- Short (noise) vector distribution -/
  dshort_vec : SDistr Vec
  /-- Matrix-vector multiplication: `A * s` -/
  mat_vec_mul : Mat → Vec → Vec
  /-- Matrix transpose: `A^T` -/
  mat_transpose : Mat → Mat
  /-- Vector addition: `u + e` -/
  vec_add : Vec → Vec → Vec
  /-- Vector dot product: `s · u` producing a ring element -/
  vec_dot : Vec → Vec → R
  /-- Ring element addition -/
  ring_add : R → R → R
  /-- Ring element subtraction -/
  ring_sub : R → R → R

attribute [instance] Params.decR Params.decVec Params.finMat Params.neMat Params.finVec Params.neVec

/-- The MLWE distinguishing game.

    EasyCrypt: `MLWE(Adv).main(b)`.
    - `b = false` (real): adversary sees `(A, A*s + e)` where `s, e ← dshort`
    - `b = true` (ideal): adversary sees `(A, u)` where `u ← duni`

    The adversary outputs a guess bit. -/
noncomputable def Game (P : Params)
    (adv : P.Mat → P.Vec → SDistr Bool)
    (b : Bool) : SDistr Bool := do
  let A ← SDistr.uniform P.Mat
  if b then do
    let u ← SDistr.uniform P.Vec
    adv A u
  else do
    let s ← P.dshort_vec
    let e ← P.dshort_vec
    let t := P.vec_add (P.mat_vec_mul A s) e
    adv A t

/-- MLWE advantage: distinguishing probability between real and ideal.

    EasyCrypt: `|Pr[MLWE(Adv).main(false)] - Pr[MLWE(Adv).main(true)]|` -/
noncomputable def advantage (P : Params)
    (adv : P.Mat → P.Vec → SDistr Bool) : ℝ≥0∞ :=
  absDiff (prTrue (Game P adv false)) (prTrue (Game P adv true))

end MLWE

/-! ## Hashed MLWE Variant -/

namespace MLWE_H

/-- MLWE with hashed matrix: the matrix A is derived from a seed via hash H.

    EasyCrypt: `MLWE_H(Adv).main(tr, b)`.
    The `tr` flag controls whether the matrix is transposed.
    This variant is used in `MLWE_PKE_Hash.ec` where key generation
    samples a seed and derives the matrix via a hash function. -/
structure Params extends MLWE.Params where
  /-- Seed type -/
  Seed : Type
  /-- Seed distribution -/
  dseed : SDistr Seed
  /-- Hash function: seed → matrix -/
  hash : Seed → Mat

/-- MLWE_H game with hashed and optionally transposed matrix.

    EasyCrypt: `MLWE_H(Adv).main(tr, b)`.
    - `tr = false`: A = H(sd), `tr = true`: A = H(sd)^T
    - `b = false`: real (A*s+e), `b = true`: ideal (uniform) -/
noncomputable def Game (P : Params)
    (adv : P.Seed → P.Vec → SDistr Bool)
    (tr : Bool) (b : Bool) : SDistr Bool := do
  let sd ← P.dseed
  let A := if tr then P.mat_transpose (P.hash sd) else P.hash sd
  if b then do
    let u ← SDistr.uniform P.Vec
    adv sd u
  else do
    let s ← P.dshort_vec
    let e ← P.dshort_vec
    let t := P.vec_add (P.mat_vec_mul A s) e
    adv sd t

/-- MLWE_H advantage with transpose flag.

    EasyCrypt: `|Pr[MLWE_H(Adv).main(tr,false)] - Pr[MLWE_H(Adv).main(tr,true)]|` -/
noncomputable def advantage (P : Params)
    (adv : P.Seed → P.Vec → SDistr Bool) (tr : Bool) : ℝ≥0∞ :=
  absDiff (prTrue (Game P adv tr false)) (prTrue (Game P adv tr true))

end MLWE_H

/-! ## PRG Indistinguishability -/

/-- PRG (Fixed-Length PRG) indistinguishability definition.

    EasyCrypt: `FLPRG.eca` (42 LOC).
    A PRG stretches a seed into a longer output.
    Security: output is indistinguishable from uniform. -/
structure PRG_Params where
  /-- Seed type -/
  Seed : Type
  /-- Output type -/
  Output : Type
  /-- Seed distribution -/
  dseed : SDistr Seed
  /-- Uniform output distribution -/
  dout : SDistr Output
  /-- The PRG function -/
  prg : Seed → Output

/-- PRG indistinguishability game.
    - `b = false` (real): output = PRG(seed)
    - `b = true` (ideal): output = uniform -/
noncomputable def PRG_Game (P : PRG_Params) (adv : P.Output → SDistr Bool)
    (b : Bool) : SDistr Bool := do
  if b then do
    let out ← P.dout
    adv out
  else do
    let seed ← P.dseed
    adv (P.prg seed)

/-- PRG advantage. -/
noncomputable def PRG_advantage (P : PRG_Params) (adv : P.Output → SDistr Bool) : ℝ≥0∞ :=
  absDiff (prTrue (PRG_Game P adv false)) (prTrue (PRG_Game P adv true))

/-! ## PRF Indistinguishability -/

/-- PRF parameters for ML-KEM (used in FO_UU for implicit rejection).

    EasyCrypt: `PRF` clone in `FO_UU.ec`. -/
structure PRF_Params where
  /-- Key type -/
  Key : Type
  /-- Input type -/
  Input : Type
  /-- Output type -/
  Output : Type
  [decInput : DecidableEq Input]
  [decOutput : DecidableEq Output]
  [finOutput : Fintype Output]
  [neOutput : Nonempty Output]
  /-- Key distribution -/
  dkey : SDistr Key
  /-- The PRF function -/
  prf : Key → Input → Output

attribute [instance] PRF_Params.decInput PRF_Params.decOutput PRF_Params.finOutput
  PRF_Params.neOutput

/-- PRF IND game for an adaptive oracle adversary.
    - `b = false` (real): the oracle is `prf k` for `k ← dkey`
    - `b = true` (ideal): the oracle is a lazily sampled random function with
      uniform values (`PRPPRF.rfOracle`): a repeated query receives the
      recorded answer. -/
noncomputable def PRF_IND_Game (P : PRF_Params)
    (adv : OracleAdv P.Input P.Output Bool) (b : Bool) : SDistr Bool :=
  if b then
    (OracleAdv.run PRPPRF.rfOracle adv []).map fun x => some x.1
  else
    P.dkey.bind fun k =>
      (OracleAdv.run (PRPPRF.keyedOracle P.prf k) adv ()).map fun x => some x.1

/-- PRF advantage. -/
noncomputable def PRF_advantage (P : PRF_Params)
    (adv : OracleAdv P.Input P.Output Bool) : ℝ≥0∞ :=
  absDiff (prTrue (PRF_IND_Game P adv false)) (prTrue (PRF_IND_Game P adv true))

end CatCrypt.Crypto.MLKEM
