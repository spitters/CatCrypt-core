/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OracleAdversaryFree
public import CatCryptCore.Crypto.OracleSubst
public import PolyFun.PFunctor.Handler.Stateful

/-!
# Substitution and simulation of oracle adversaries as free-monad interpretation

Along `OracleAdv.toFreeM : OracleAdv D R α → FreeM (AdvSig D R) α`:

* `OracleAdv.toFreeM_bind` — `bind` is `FreeM.bind`
* `OracleAdv.toFreeM_subst` — `subst impl` is `FreeM.liftM` by the free handler
  `substHandler impl : Handler (FreeM (AdvSig D' R')) (AdvSig D R)`
* `OracleAdv.toFreeM_simulate` — `simulate impl` is `Handler.Stateful.run` of the stateful
  handler `simHandler impl : Handler.Stateful (FreeM (AdvSig D' R')) S (AdvSig D R)`
* `OracleAdv.isQueryBoundBy_iff_wpFold_charge`,
  `OracleAdv.isQueryBound_iff_wpFold_charge` — a query bound is the bound on the worst-case
  charge fold of the adversary's tree
-/

@[expose] public section

namespace CatCrypt.Crypto

open PFunctor

namespace OracleAdv

variable {D R D' R' α β : Type}

/-- The tree of `A.bind f` is the free-monad bind of the tree of `A` with the trees of `f`. -/
theorem toFreeM_bind (A : OracleAdv D R α) (f : α → OracleAdv D R β) :
    toFreeM (A.bind f) = (toFreeM A).bind fun a => toFreeM (f a) := by
  induction A with
  | ret a => rfl
  | rand p k ih => simp only [bind, toFreeM, ih]; rfl
  | query d k ih => simp only [bind, toFreeM, ih]; rfl

/-- The free handler of `subst impl`: a sampling node is reissued, a query `d` is the tree
of `impl d`. -/
def substHandler (impl : D → OracleAdv D' R' R) : Handler (FreeM (AdvSig D' R')) (AdvSig D R)
  | .rand β p => FreeM.lift (P := AdvSig D' R') (.rand β p)
  | .query d => toFreeM (impl d)

/-- The tree of `subst impl A` is the interpretation of the tree of `A` by
`substHandler impl`. -/
theorem toFreeM_subst (impl : D → OracleAdv D' R' R) (A : OracleAdv D R α) :
    toFreeM (subst impl A) = (toFreeM A).liftM (substHandler impl) := by
  induction A with
  | ret a => rfl
  | rand p k ih => simp only [subst_rand, toFreeM, ih]; rfl
  | query d k ih => simp only [subst_query, toFreeM_bind, toFreeM, ih]; rfl

/-- The stateful handler of `simulate impl`: a sampling node is reissued and keeps the
state, a query `d` from state `s` is the tree of `impl s d`. -/
def simHandler {S : Type} (impl : S → D → OracleAdv D' R' (R × S)) :
    Handler.Stateful (FreeM (AdvSig D' R')) S (AdvSig D R)
  | .rand β p => StateT.lift (FreeM.lift (P := AdvSig D' R') (.rand β p))
  | .query d => fun s => toFreeM (impl s d)

/-- The tree of `simulate impl A s` is the run of the tree of `A` from state `s` through the
stateful handler `simHandler impl`. -/
theorem toFreeM_simulate {S : Type} (impl : S → D → OracleAdv D' R' (R × S))
    (A : OracleAdv D R α) (s : S) :
    toFreeM (simulate impl A s) = (simHandler impl).run (toFreeM A) s := by
  induction A generalizing s with
  | ret a => rfl
  | rand p k ih => simp only [simulate, toFreeM, ih]; rfl
  | query d k ih => simp only [simulate, toFreeM_bind, toFreeM, ih]; rfl

/-- The weighted query bound `n` is the bound `n` on the worst-case charge fold of the tree,
charging `cost d` at a query `d` and `0` at a sampling node. -/
theorem isQueryBoundBy_iff_wpFold_charge (cost : D → ℕ) (A : OracleAdv D R α) (n : ℕ) :
    A.IsQueryBoundBy cost n ↔
      FreeM.wpFold (OpSpec.charge fun a => ((AdvSig.posCost cost a : ℕ) : ℕ∞)) (toFreeM A)
        (fun _ => 0) ≤ n := by
  rw [isQueryBoundBy_iff_isRollBound, FreeM.isRollBound_iff_wpFold_charge]

/-- The query bound `q` is the bound `q` on the worst-case charge fold of the tree, charging
`1` at a query and `0` at a sampling node. -/
theorem isQueryBound_iff_wpFold_charge (A : OracleAdv D R α) (q : ℕ) :
    A.IsQueryBound q ↔
      FreeM.wpFold (OpSpec.charge fun a => ((AdvSig.posCost (fun _ => 1) a : ℕ) : ℕ∞))
        (toFreeM A) (fun _ => 0) ≤ q := by
  rw [isQueryBound_iff_isRollBound, FreeM.isRollBound_iff_wpFold_charge]

end OracleAdv

end CatCrypt.Crypto
