/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Tactics.AutoOracleRun
public import CatCryptCore.Crypto.Messaging.SMCorruptPrekey
public import CatCryptCore.Crypto.Messaging.FSAEADCorrupt

/-!
# Tests of the `catcrypt_auto` arms for equalities of oracle runs

Statements about runs of oracle adversaries, closed by `catcrypt_auto` with the shapes of
`CatCryptCore.Tactics.AutoOracleRun`. The first group restates the run lemmas at local
hypotheses; the second restates hand uses of `OracleAdv.run_eq_run_of_inv` in the
secure-messaging proofs.

* After the critical step, the eager oracle is the lazy one (`OracleAdv.run_eager_of_done`,
  `OracleAdv.run_nf_eager_of_done`); the invariant is read from the hypothesis on the start
  state.
* An invariant kept by every call holds along the support of a run
  (`OracleAdv.run_support_inv`), with the invariant read from the goal.
* A value drawn at its first use (`OracleAdv.run_eq_bind_eager`), by
  `OracleAdv.run_eq_bind_run_of_trigger` with the predicates taken from the context.
* Identical until bad, through state maps (`OracleAdv.run_map_eq_off_bad`).
* Two keyed games whose oracles agree, everywhere or on an invariant, accept with the same
  probability (`KeyedGame.accept_eq_of_kernel`).
* Runs read through maps that are equal only propositionally, from start states equal by a
  hypothesis; a run drawn at a first triggering call read through a map on both sides; an
  invariant given as the argument of `oracle_run_eq with N` or `catcrypt_auto [N]`.
* The challenge epoch `0` admits no challenge (`SM_Corrupt_Advantage_le_split`, `have h0`): the
  invariant `smSndInv` is a definition argument, the runs are read through `PMF.map Prod.fst`.
* The ideal and the fresh oracle of the FS-AEAD reduction give the same run
  (`fsFin_true_eq`): the invariant is a term argument, used by the `"*"` arm.
-/

set_option autoImplicit false

section Generic

open CatCrypt.Crypto

variable {S D R α : Type}

/-- After the critical step, the oracle with the value drawn in advance is the lazy one
(`OracleAdv.run_eager_of_done`). -/
example (O : S → D → PMF (R × S)) (Ov : S → D → PMF (R × S))
    (c : S → D → Bool) (hnc : ∀ s d, c s d = false → Ov s d = O s d) (N : S → Prop)
    (h2 : ∀ s d, N s → ∀ x ∈ (O s d).support, N x.2) (h3 : ∀ s d, N s → c s d = false)
    (A : OracleAdv D R α) (s : S) (hs : N s) : OracleAdv.run Ov A s = OracleAdv.run O A s := by
  catcrypt_auto

/-- An invariant kept by every call holds along the support of a run. -/
example (O : S → D → PMF (R × S)) (N : S → Prop)
    (h2 : ∀ s d x, N s → x ∈ (O s d).support → N x.2)
    (A : OracleAdv D R α) (s : S) (hs : N s) :
    ∀ z ∈ (OracleAdv.run O A s).support, N z.2 := by
  catcrypt_auto

-- The candidate predicates of `oracle_run_trigger` and their premises exceed the default
-- budget of the arm.
set_option catcrypt_auto.maxHeartbeats 50000 in
/-- A value drawn at its first use (`OracleAdv.run_eq_bind_eager`). -/
example {V : Type} (O : S → D → PMF (R × S)) (Ov : V → S → D → PMF (R × S))
    (μ : PMF V) (c : S → D → Bool)
    (hc : ∀ s d, c s d = true → O s d = μ.bind fun v => Ov v s d)
    (hnc : ∀ v s d, c s d = false → Ov v s d = O s d) (N : S → Prop)
    (h1 : ∀ v s d, c s d = true → ∀ x ∈ (Ov v s d).support, N x.2)
    (h2 : ∀ s d, N s → ∀ x ∈ (O s d).support, N x.2) (h3 : ∀ s d, N s → c s d = false)
    (A : OracleAdv D R α) (s : S) :
    OracleAdv.run O A s = μ.bind fun v => OracleAdv.run (Ov v) A s := by
  catcrypt_auto

/-- Identical until bad, through state maps, at one outcome. -/
example {T : Type} (O₁ O₂ : S → D → PMF (R × S)) (f₁ f₂ : S → T) (bad : T → Bool)
    (hmono₁ : ∀ s d, bad (f₁ s) = true → ∀ z ∈ (O₁ s d).support, bad (f₁ z.2) = true)
    (hmono₂ : ∀ s d, bad (f₂ s) = true → ∀ z ∈ (O₂ s d).support, bad (f₂ z.2) = true)
    (hstep : ∀ s₁ s₂ d, f₁ s₁ = f₂ s₂ → bad (f₁ s₁) = false → ∀ (r : R) (u : T),
      bad u = false →
        (O₁ s₁ d).map (Prod.map id f₁) (r, u) = (O₂ s₂ d).map (Prod.map id f₂) (r, u))
    (A : OracleAdv D R α) (s₁ s₂ : S) (hf : f₁ s₁ = f₂ s₂) (a : α) (t : T)
    (ht : bad t = false) :
    (OracleAdv.run O₁ A s₁).map (Prod.map id f₁) (a, t) =
      (OracleAdv.run O₂ A s₂).map (Prod.map id f₂) (a, t) := by
  catcrypt_auto

/-- A keyed game and the game with an oracle agreeing with it accept with the same
probability. -/
example {Q B : Type} (G : UCTransparent.KeyedGame Q B)
    (O' : G.Key → G.State → Q → PMF (B × G.State)) (h : ∀ k s q, O' k s q = G.oracle k s q)
    (A : OracleAdv Q B Bool) :
    G.accept A = ({ G with oracle := O' } : UCTransparent.KeyedGame Q B).accept A := by
  catcrypt_auto

-- The failing invariant candidates and their premises exceed the default budget of the arm.
set_option catcrypt_auto.maxHeartbeats 50000 in
/-- Two runs read through propositionally equal maps from equal start states: the map
congruence of `oracle_run_eq` leaves `f = g` and `s' = s`. -/
example {β : Type} (O O' : S → D → PMF (R × S)) (f g : α × S → β) (hfg : ∀ z, f z = g z)
    (N : S → Prop) (hN : ∀ s d, N s → ∀ x ∈ (O s d).support, N x.2)
    (hO : ∀ s d, N s → O' s d = O s d) (A : OracleAdv D R α) (s s' : S) (hs : N s)
    (h : s' = s) :
    PMF.map f (OracleAdv.run O' A s') = PMF.map g (OracleAdv.run O A s) := by
  catcrypt_auto

-- The candidate predicates of `oracle_run_trigger` and their premises exceed the default
-- budget of the arm.
set_option catcrypt_auto.maxHeartbeats 50000 in
/-- A value drawn at its first use, read through a map on both sides: the map inside the
`PMF.bind` is moved outside it before `OracleAdv.run_eq_bind_run_of_trigger`. -/
example {V β : Type} (O : S → D → PMF (R × S)) (Ov : V → S → D → PMF (R × S))
    (μ : PMF V) (c : S → D → Bool)
    (hc : ∀ s d, c s d = true → O s d = μ.bind fun v => Ov v s d)
    (hnc : ∀ v s d, c s d = false → Ov v s d = O s d) (N : S → Prop)
    (h1 : ∀ v s d, c s d = true → ∀ x ∈ (Ov v s d).support, N x.2)
    (h2 : ∀ s d, N s → ∀ x ∈ (O s d).support, N x.2) (h3 : ∀ s d, N s → c s d = false)
    (f : α × S → β) (A : OracleAdv D R α) (s : S) :
    PMF.map f (OracleAdv.run O A s) =
      μ.bind fun v => PMF.map f (OracleAdv.run (Ov v) A s) := by
  catcrypt_auto

/-- An invariant that no hypothesis states about the start state, given to `oracle_run_eq`. -/
example (O O' : ℕ → D → PMF (R × ℕ)) (hN : ∀ s d, 0 < s → ∀ x ∈ (O s d).support, 0 < x.2)
    (hO : ∀ s d, 0 < s → O' s d = O s d) (A : OracleAdv D R α) :
    OracleAdv.run O' A 1 = OracleAdv.run O A 1 := by
  oracle_run_eq with fun s => 0 < s

/-- The same invariant as a term argument of `catcrypt_auto`. -/
example (O O' : ℕ → D → PMF (R × ℕ)) (hN : ∀ s d, 0 < s → ∀ x ∈ (O s d).support, 0 < x.2)
    (hO : ∀ s d, 0 < s → O' s d = O s d) (A : OracleAdv D R α) :
    OracleAdv.run O' A 1 = OracleAdv.run O A 1 := by
  catcrypt_auto [fun s : ℕ => 0 < s]

/-- A keyed game and a game whose oracle agrees with it on an invariant `V` of the states
accept with the same probability (`KeyedGame.accept_eq_of_kernel` at the invariant `V`). -/
example {Q B : Type} (G : UCTransparent.KeyedGame Q B) (V : G.State → Prop) (hV : V G.init)
    (hinv : ∀ k s q, V s → ∀ x ∈ (G.oracle k s q).support, V x.2)
    (O' : G.Key → G.State → Q → PMF (B × G.State))
    (h : ∀ k s q, V s → O' k s q = G.oracle k s q) (A : OracleAdv Q B Bool) :
    G.accept A = ({ G with oracle := O' } : UCTransparent.KeyedGame Q B).accept A := by
  catcrypt_auto

end Generic

namespace CatCrypt.Crypto.Messaging

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Assumptions

section NF

variable {S D R E α : Type}

/-- After the critical step, the eager oracle is the lazy one
(`OracleAdv.run_nf_eager_of_done`). -/
example (μ : PMF E) (δ : S → D → E → R × S) (c : S → D → Bool)
    (N : S → Prop) (h2 : ∀ s d e, N s → N (δ s d e).2) (h3 : ∀ s d, N s → c s d = false)
    (v : E) (A : OracleAdv D R α) (s : S) (hs : N s) :
    OracleAdv.run (OracleAdv.nfOracle μ (OracleAdv.eagerStep δ c v)) A s =
      OracleAdv.run (OracleAdv.nfOracle μ δ) A s := by
  catcrypt_auto [OracleAdv.nfOracle, OracleAdv.eagerStep]

end NF

section Split

variable {Sc Msg Key Rand RK Sa W Ct : Type} [Fintype Rand] [Nonempty Rand] [SampleableType W]
  [SampleableType Ct] [Fintype RK] [Nonempty RK]

/-- The challenge epoch `0` admits no challenge (`SM_Corrupt_Advantage_le_split`, `h0`). -/
example (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS : ℕ) (A : SMCorruptAdv Sc Msg RK Sa W Ct) :
    ∀ i rk, (OracleAdv.run (smOracleOf C R G D ΔFS ΔPCS 0 false (realRoot R))
      (A.play 0 i.1) (smInit (Sa := Sa) i rk)).map Prod.fst =
      (OracleAdv.run (smOracleOf C R G D ΔFS ΔPCS 0 true (realRoot R))
        (A.play 0 i.1) (smInit i rk)).map Prod.fst := by
  catcrypt_auto [smSndInv, smOracleOf_sndInv, smOracleOf_zero_ideal]

end Split

section FSAEAD

variable {Sa W Ct AD : Type} [SampleableType W] [SampleableType Ct] [Fintype Sa] [Nonempty Sa]
  [DecidableEq AD]

/-- The ideal and the fresh oracle of the FS-AEAD reduction give the same run
(`fsFin_true_eq`), with the invariant of the proof as a term argument. -/
example (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct AD)
    (A : OracleAdv (FSQuery W AD) (FSAns Sa Ct) Bool)
    (hO : ∀ s d, (fun s : FSLzSt Sa × List ((W × AD) × Ct) => s.1.done = false → s.2 = []) s →
      OracleAdv.simOracle (fsCorrAEADImpl G D) aeadIdealOracle s d =
        OracleAdv.simOracle (fsCorrAEADImpl G D) fsFreshOracle s d)
    (hN : ∀ s d,
      (fun s : FSLzSt Sa × List ((W × AD) × Ct) => s.1.done = false → s.2 = []) s →
      ∀ x ∈ (OracleAdv.simOracle (fsCorrAEADImpl G D) fsFreshOracle s d).support,
        (fun s : FSLzSt Sa × List ((W × AD) × Ct) => s.1.done = false → s.2 = []) x.2) :
    OracleAdv.run (OracleAdv.simOracle (fsCorrAEADImpl G D) aeadIdealOracle) A (fsLzInit, []) =
      OracleAdv.run (OracleAdv.simOracle (fsCorrAEADImpl G D) fsFreshOracle) A
        (fsLzInit, []) := by
  catcrypt_auto [fun s : FSLzSt Sa × List ((W × AD) × Ct) => s.1.done = false → s.2 = []]

end FSAEAD

end CatCrypt.Crypto.Messaging
