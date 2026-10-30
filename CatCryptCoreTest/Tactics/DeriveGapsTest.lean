/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveTimeBound
public import CatCryptCore.Tactics.StdCosts
public import CatCryptCore.Category.ProtBicatReactive
public import CatCryptCore.Crypto.UCTransparentMultiTimed
public import CatCryptCore.Crypto.UCGlobalSquare
public import CatCryptCore.Crypto.UCOracleGame
public import CatCryptCore.Crypto.UCRoundHybrid
public import CatCryptCore.Crypto.Signatures.FSigReduction

/-!
# Tests of the derive tactics on simulators and reductions of the UC layer

Costed forms, erasure theorems and time theorems derived by `derive_reduction` and
`derive_time_bound` for declarations of the UC layer:

* the `resume` and `finish` steps of the one-call leak simulator `simWrap`, whose costed trees
  bind a costed tree to a continuation returning at zero cost
  (`(A.bind fun y => (0, ret (h y))).1` in the arithmetic leaves of `time_bound`);
* the simulator `gSimHybrid`, a tensor of a tensor, whose inner `Sum.elim` dispatch lies below
  a bind of the outer one;
* the environment reductions `OProt.reduce` and `FSigSys.forgeReduce`, which run the
  computation field `Z.obs z o` of a strategy on a heap (`Z.obs z o h`);
* the session reduction `sessReduction`, whose session oracles are selected by an `if` on
  `j < i` that unfolds to a `Bool.casesOn` applied to further arguments.
-/

@[expose] public section

set_option autoImplicit false

derive_reduction CatCrypt.Crypto.UCTransparent.simWrap
derive_time_bound CatCrypt.Crypto.UCTransparent.simWrap.resume.tree
derive_time_bound CatCrypt.Crypto.UCTransparent.simWrap.finish.tree

derive_reduction CatCrypt.Crypto.UCTransparent.gSimHybrid

derive_reduction CatCrypt.Crypto.UCTransparent.OProt.reduce

derive_reduction CatCrypt.Crypto.Signatures.FSigSys.forgeReduce

namespace CatCrypt.Crypto.UCTransparent.KeyedGame

derive_reduction sessReduction

end CatCrypt.Crypto.UCTransparent.KeyedGame

namespace CatCrypt.Tactics.DeriveGapsTest

open CatCrypt.Crypto CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.Signatures

/-- The costed form of `gSimHybrid` over a costed simulator binder erases to `gSimHybrid`. -/
example {σS EA OA EA' OA' : Type} (EH OH EG OG : Type) (S : MultiHybrid σS EA OA EA' OA')
    (start : σS → EA → CatCrypt.Core.SPTree.Timed (σS × (EA' ⊕ OA))) (startCost : σS → EA → ℕ)
    (resume : σS → OA' → CatCrypt.Core.SPTree.Timed (σS × (EA' ⊕ OA)))
    (resumeCost : σS → OA' → ℕ) (finish : σS → OA' → CatCrypt.Core.SPTree.Timed (σS × OA))
    (finishCost : σS → OA' → ℕ)
    (h₁ : ∀ s e, (start s e).erase.compile = S.start s e)
    (h₂ : ∀ s o, (resume s o).erase.compile = S.resume s o)
    (h₃ : ∀ s o, (finish s o).erase.compile = S.finish s o) :
    (gSimHybrid.timed EH OH EG OG S start startCost resume resumeCost finish finishCost).Erases
      (gSimHybrid EH OH EG OG S) :=
  gSimHybrid.erase_timed EH OH EG OG S start startCost resume resumeCost finish finishCost
    h₁ h₂ h₃

/-- The costed form of `OProt.reduce` takes the cost companions of `dist`, `Z.next`,
`P.step` and `Z.obs`, and erases to `OProt.reduce`. -/
example {τ E O Q A ζ : Type} (P : OProt τ E O Q A) (Z : Strat ζ E O)
    (dist : ζ → CatCrypt.Core.SPComp Bool) (distCost : ζ → ℕ) (n : ℕ) (z : ζ) (t : τ)
    (h : CatCrypt.Core.Heap) (nextCost : ζ → ℕ) (stepCost : τ → E → ℕ)
    (obsCost : ζ → O → ℕ) :
    (OProt.reduce.timed P Z dist distCost n z t h nextCost stepCost obsCost).2.erase =
      P.reduce Z dist n z t h :=
  OProt.reduce.erase_timed P Z dist distCost n z t h nextCost stepCost obsCost

/-- The costed form of the forger `forgeReduce` takes the cost companions of `Z.next`,
`Z.obs` and the verifier, and erases to `forgeReduce`. -/
example {Msg PK SK Sig ζ : Type} [DecidableEq Msg] [DecidableEq PK] [Inhabited Msg]
    [Inhabited Sig] (S : PSigScheme Msg PK SK Sig)
    (Z : Strat ζ (FSigSys.SigEv Msg PK Sig ⊕ Unit) (FSigSys.SigOut PK Sig ⊕ Unit)) (pk : PK)
    (n : ℕ) (z : ζ) (st : FSigSys.ForgeSt Msg Sig) (h : CatCrypt.Core.Heap)
    (nextCost : ζ → ℕ) (obsCost : ζ → FSigSys.SigOut PK Sig ⊕ Unit → ℕ)
    (verifyCost : PK → Msg → Sig → ℕ) :
    (FSigSys.forgeReduce.timed S Z pk n z st h nextCost obsCost verifyCost).2.erase =
      FSigSys.forgeReduce S Z pk n z st h :=
  FSigSys.forgeReduce.erase_timed S Z pk n z st h nextCost obsCost verifyCost

/-- The costed form of the session reduction `sessReduction` takes the cost companions of
the oracles of the two games, and erases to `sessReduction`. -/
example {Q A : Type} (G₀ G₁ : KeyedGame Q A) (i : ℕ) (B : OracleAdv.Timed (ℕ × Q) A Bool)
    (c₀ : G₀.Key → G₀.State → Q → ℕ) (c₁ : G₁.Key → G₁.State → Q → ℕ) :
    (KeyedGame.sessReduction.timed G₀ G₁ i B c₀ c₁).2.erase = G₀.sessReduction G₁ i B.erase :=
  KeyedGame.sessReduction.erase_timed G₀ G₁ i B c₀ c₁

end CatCrypt.Tactics.DeriveGapsTest
