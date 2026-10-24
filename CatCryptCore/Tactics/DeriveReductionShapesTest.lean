/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveTimeBound
public import CatCryptCore.Crypto.Signatures.EUFCMA

/-!
# Tests of `derive_reduction` on three reduction shapes

* `letRed`: a continuation `postL k t` whose definition returns a function after a chain of
  `let`s, applied to the result of a computation (the shape of `opaqueL2Reduction`);
* `injRed`: a reduction into the structure `EUFCMAAdversary` whose data field `run`, an oracle
  program, calls a handler binder (the shape of `fido2InjectReduction`);
* `sigRedM`: a reduction `ℕ → OracleAdv ℕ Bool (Bool × ℕ)` over an oracle adversary, through
  `OracleAdv.simulate` (the shape of `sigReduction`).

Each is derived by `derive_reduction`, its compile or erasure theorem is pinned by an
`example`, and its costed form has a time theorem.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Tactics.DeriveReductionShapesTest

open CatCrypt.Core

/-! ## A `let` chain returning a function -/

/-- The output step after the bit `t`: two `let`s of data, then a function of the pair. -/
noncomputable def postL (k : ℕ) (t : Bool) : ℕ × ℕ → SPComp (ℕ × ℕ) :=
  let s₁ := k + 1
  let s₂ := if t then s₁ * 2 else s₁
  fun ⟨a, b⟩ => SPComp.pure (a + s₂, b)

/-- The adversary `A`, then the core `core`, then `postL` at the bit of `A`. -/
noncomputable def letRed (k : ℕ) (A : SPComp Bool) (core : SPComp (ℕ × ℕ)) :
    SPComp (ℕ × ℕ) :=
  SPComp.bind A fun t => SPComp.bind core (postL k t)

derive_reduction letRed

example (k : ℕ) (A : SPTree Bool) (core : SPTree (ℕ × ℕ)) :
    (letRed.tree k A core).compile = letRed k A.compile core.compile :=
  letRed.compile_tree k A core

derive_time_bound letRed.tree

/-! ## A handler called in a data field -/

open CatCrypt.Crypto (OracleProg)
open CatCrypt.Crypto.Signatures (EUFCMAAdversary)

derive_timed_structure EUFCMAAdversary

/-- The forger that runs `pre`, calls the handler at `true`, and queries the signing oracle at
the answer plus the public key. -/
noncomputable def injRed (handler : ∀ b : Bool, SPComp (cond b ℕ Unit)) (pre : SPComp Unit) :
    EUFCMAAdversary ℕ ℕ ℕ ℕ where
  run pk := .lift pre fun _ => .lift (handler true) fun (n : ℕ) =>
    .query (n + pk) fun σ => .pure (n, σ)

derive_reduction injRed

example (handler : (b : Bool) → SPTree.Timed (cond b ℕ Unit)) (handlerCost : Bool → ℕ)
    (pre : SPTree.Timed Unit) :
    (injRed.timed handler handlerCost pre).Erases
      (injRed (fun b => (handler b).erase.compile) pre.erase.compile) :=
  injRed.erase_timed handler handlerCost pre

/-- The time bound of `EUFCMAAdversary.Timed`, which has no tree or computation field. -/
theorem injRed.timeBound_timed (handler : (b : Bool) → SPTree.Timed (cond b ℕ Unit))
    (handlerCost : Bool → ℕ) (pre : SPTree.Timed Unit) :
    (injRed.timed handler handlerCost pre).TimeBound :=
  trivial

/-! ## A function into oracle trees -/

open CatCrypt.Crypto (OracleAdv)

/-- The oracle implementation: forward the query `d + 1` and keep the state. -/
noncomputable def implM (s : Unit) (d : ℕ) : OracleAdv ℕ Bool (Bool × Unit) :=
  .query (d + 1) fun r => .ret (r, s)

/-- On the public key `pk`: a uniform bit, then `A` at `pk` or `0` under `implM`, and the
answer paired with `pk`. -/
noncomputable def sigRedM (A : ℕ → OracleAdv ℕ Bool Bool) :
    ℕ → OracleAdv ℕ Bool (Bool × ℕ) :=
  fun pk =>
    .rand (PMF.uniformFintype Bool) fun b =>
      OracleAdv.bind (OracleAdv.simulate implM (A (if b then pk else 0)) ())
        fun x => .ret (x.1, pk)

derive_reduction sigRedM

example (A : ℕ → OracleAdv.Timed ℕ Bool Bool) (ACost : ℕ → ℕ) (pk : ℕ) :
    (sigRedM.timed A ACost pk).2.erase = sigRedM (fun a => (A a).erase) pk :=
  sigRedM.erase_timed A ACost pk

open CatCrypt.Crypto.OracleAdv.Timed in
/-- One step of the costed `implM`: its step cost, one unit of delay and one query. -/
theorem implM.timeBound_timed (s : Unit) (d : ℕ) :
    StepTimeBound (OracleAdv.Timed.delay 1 (implM.timed s d)) 3 := by
  simp [implM.timed, delay, StepTimeBound, TimeBound]

open CatCrypt.Crypto.OracleAdv.Timed in
/-- For `A` of time `T` with at most `q` queries and cost companion at most `a`, the costed
`sigRedM` runs within `a + T + 3q + 3`. -/
theorem sigRedM.timeBound_timed (A : ℕ → OracleAdv.Timed ℕ Bool Bool) (ACost : ℕ → ℕ)
    {T q a : ℕ} (hA : ∀ x, (A x).TimeBound T) (hq : ∀ x, (A x).erase.IsQueryBound q)
    (ha : ∀ x, ACost x ≤ a) (pk : ℕ) :
    StepTimeBound (sigRedM.timed A ACost pk) (a + T + q * 3 + 3) := by
  simp only [sigRedM.timed]
  refine ⟨Nat.zero_le _, ?_⟩
  rw [Nat.sub_zero, timeBound_rand_iff]
  refine ⟨by omega, fun b => ?_⟩
  have hs := timeBound_simulate _ implM.timeBound_timed (hA (if b = true then pk else 0))
    (hq (if b = true then pk else 0)) ()
  have hb := timeBound_bind hs.2 (n := 0)
    (f := fun x => (0, OracleAdv.Timed.ret (x.1, pk))) fun _ => ⟨le_rfl, trivial⟩
  have hc := ha (if b = true then pk else 0)
  have h1 := hs.1
  have h2 := hb.1
  refine ⟨by simp only [ite_self] at h2 ⊢; omega, hb.2.mono ?_⟩
  simp only [ite_self]
  omega

end CatCrypt.Tactics.DeriveReductionShapesTest
