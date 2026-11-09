/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.SMAuth
import CatCryptCore.Tactics.AutoDispatchExt

/-!
# The root-key hop of the forgery event at an epoch

The second hop of the forgery event at the epoch `k` of the authenticity game over the ACD
construction `acdAuthSM C R G D`. After the CKA hop (`acdAuthSM_truncGame_le_cka`) the root step
at the opening of the epoch `k` is the root KDF `R` on a uniform key (`unifKeyRoot R`). The
PRF-PRNG reduction `smAuthRootRed` replaces it by a uniform root output (`unifRoot`): it runs the
adversary against the simulator `smAuthRootImpl`, which keeps the full state of the truncated
hybrid and asks the root step at the opening of the epoch `k` to the `prf` oracle of the
PRF-PRNG game.

## Main results

* `smRootImplAt_step_real`, `smRootImplAt_step_ideal`, `smRootImplAt_step_noncrit` — the
  simulator of the root step at the epoch `k` against the PRF-PRNG oracles
* `smAuthRoot_step_real`, `smAuthRoot_step_ideal` — the simulator of the truncated hybrid
  against the PRF-PRNG oracles
* `smAuthHop_run_eager` — the uniform key of the root step at the epoch `k` drawn in advance
* `smAuthRoot_real_eq`, `smAuthRoot_ideal_eq` — the two PRF-PRNG games of `smAuthRootRed` are
  the truncated hybrids with the root steps `unifKeyRoot R` and `unifRoot` at the epoch `k`
* `smAuthHopGame_le_root`, `acdAuthSM_truncGame_le_root` — the root hop, and the CKA hop
  followed by the root hop, ending in the game `smAuthRootIdealGame`
-/

set_option autoImplicit false

@[expose] public section

namespace CatCrypt.Crypto.Messaging

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Assumptions
open scoped ENNReal

section RootRed

variable {Sc Msg Key Rand RK Sa W Ct : Type} [Fintype Rand] [Nonempty Rand] [SampleableType W]
  [SampleableType Ct] [DecidableEq W] [DecidableEq Ct]

/-- The simulator of the root hop with the root step at the opening of the epoch `k` asked to
the `prf` oracle of the PRF-PRNG game, and the challenge and corruption gates of the challenge
epoch `t`. -/
noncomputable def smRootImplAt (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t k : ℕ) (s : SMSt Sc Msg RK Sa) (q : SMQuery W) :
    OracleAdv (PPQuery RK Key) (RK × Sa) (SMAns Sc Msg RK Sa Ct × SMSt Sc Msg RK Sa) :=
  match q with
  | .ratchet p => smRootRatchet C R k s p
  | .recv p => smRootRecv C s p
  | .send p m => smFullSend G D s p m
  | .chall p m => smFullChall G D t false s p m
  | .corrupt p => smFullCorr ΔFS ΔPCS t s p

/-- A query of the truncated hybrid in the simulator of the root hop: a query of the corruption
game is answered by `smRootImplAt` and logged, and by a rejection when the epoch `k` leaves the
safe epochs; a delivery is answered from the log and by a decryption under a key of the
receiving chain, and the flag of a forgery is raised. -/
noncomputable def smAuthRootStep (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t k : ℕ) (σ : (SMSt Sc Msg RK Sa × SMAuthAux W Ct) × Bool) :
    SMAuthQuery W Ct → OracleAdv (PPQuery RK Key) (RK × Sa)
      (SMAuthAns Msg Ct (SMPartySt Sc RK Sa) W × ((SMSt Sc Msg RK Sa × SMAuthAux W Ct) × Bool))
  | .sm q => (smRootImplAt C R G D ΔFS ΔPCS t k σ.1.1 q).bind fun y =>
      if (σ.1.2.upd (ckaShadow σ.1.1.ck) q y.1.toScheme).safe ΔFS ΔPCS k then
        .ret (.sm y.1.toScheme, ((y.2, σ.1.2.upd (ckaShadow σ.1.1.ck) q y.1.toScheme), σ.2))
      else .ret (.dec none, ((y.2, σ.1.2.upd (ckaShadow σ.1.1.ck) q y.1.toScheme), σ.2))
  | .deliver p j ad c => .ret
      (.dec (acdDeliverAns G D ΔFS ΔPCS k (ckaShadow σ.1.1.ck) σ.1.1.loc σ.1.2 p j ad c),
        (σ.1, σ.2 || acdDeliverBad G D ΔFS ΔPCS k (ckaShadow σ.1.1.ck) σ.1.1.loc σ.1.2 p j ad c))

/-- **The simulator of the root hop of the forgery event at the epoch `k`**: `smAuthRootStep`
while the epoch `k` is safe, a rejection otherwise. Its state is the state of the truncated
hybrid `smAuthHopOracle`. -/
noncomputable def smAuthRootImpl (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t k : ℕ) (σ : (SMSt Sc Msg RK Sa × SMAuthAux W Ct) × Bool) (d : SMAuthQuery W Ct) :
    OracleAdv (PPQuery RK Key) (RK × Sa)
      (SMAuthAns Msg Ct (SMPartySt Sc RK Sa) W × ((SMSt Sc Msg RK Sa × SMAuthAux W Ct) × Bool)) :=
  if σ.1.2.safe ΔFS ΔPCS k then smAuthRootStep C R G D ΔFS ΔPCS t k σ d
  else .ret (.dec none, σ)

/-- The PRF-PRNG reduction of the forgery event at the epoch `k` as an oracle tree: it draws the
challenge epoch `t` of the authenticity adversary from `tStar`, the CKA initialisation from
`initP` and a uniform root key, runs the adversary against the simulator `smAuthRootImpl` and
outputs the flag of a forgery. -/
noncomputable def smAuthRootTree (C : CKADef Sc Msg Key) [CKACoins C Rand] [Fintype RK]
    [Nonempty RK] (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS k : ℕ) (initP : PMF (Msg × Sc × Sc)) (tStar : PMF ℕ)
    (play : ℕ → Msg → OracleAdv (SMAuthQuery W Ct) (SMAuthAns Msg Ct (SMPartySt Sc RK Sa) W) Bool) :
    OracleAdv (PPQuery RK Key) (RK × Sa) Bool :=
  .rand tStar fun t => .rand initP fun i => .rand (PMF.uniformFintype RK) fun rk =>
    (OracleAdv.simulate (smAuthRootImpl C R G D ΔFS ΔPCS t k) (play t i.1)
      ((smInit (Sa := Sa) i rk, SMAuthAux.init), false)).bind fun r => .ret r.2.2

/-- **The PRF-PRNG reduction of the forgery event at the epoch `k`**: the tree `smAuthRootTree`
at the challenge-epoch distribution and the interaction of `A`. -/
noncomputable def smAuthRootRed (C : CKADef Sc Msg Key) [CKACoins C Rand] [Fintype RK]
    [Nonempty RK] (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS k : ℕ) (initP : PMF (Msg × Sc × Sc)) (A : SMAuthAdv Msg W Ct (SMPartySt Sc RK Sa)) :
    OracleAdv (PPQuery RK Key) (RK × Sa) Bool :=
  smAuthRootTree C R G D ΔFS ΔPCS k initP A.tStar A.play

/-- The opening of the epoch `k` in the truncated hybrid: a ratchet query from a state with the
epoch `k` safe that opens the epoch `k`. -/
def smAuthRootCrit (ΔFS ΔPCS k : ℕ) (s : (SMSt Sc Msg RK Sa × SMAuthAux W Ct) × Bool) :
    SMAuthQuery W Ct → Bool
  | .sm q => s.1.2.safe ΔFS ΔPCS k && smCrit k s.1.1 q
  | .deliver _ _ _ _ => false

end RootRed

/-! ## The simulator against the PRF-PRNG oracles -/

section RootSim

variable {Sc Msg Key Rand RK Sa W Ct : Type} [Fintype Rand] [Nonempty Rand] [SampleableType W]
  [SampleableType Ct] [DecidableEq W] [DecidableEq Ct]

/-- A query of the corruption game in the simulator of the root hop, from a safe state, is the
query of `smRootImplAt`, logged, with the rejection of the transitions into an unsafe state. -/
theorem smAuthRootImpl_simOracle (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t k : ℕ) {U : Type} (O' : U → PPQuery RK Key → PMF ((RK × Sa) × U))
    (σ : (SMSt Sc Msg RK Sa × SMAuthAux W Ct) × Bool) (u : U) (q : SMQuery W)
    (hs : σ.1.2.safe ΔFS ΔPCS k = true) :
    OracleAdv.simOracle (smAuthRootImpl C R G D ΔFS ΔPCS t k) O' (σ, u) (.sm q) =
      (OracleAdv.simOracle (smRootImplAt C R G D ΔFS ΔPCS t k) O' (σ.1.1, u) q).map fun y =>
        ((smAuthCut ΔFS ΔPCS k (.sm y.1.toScheme,
            ((y.2.1, σ.1.2.upd (ckaShadow σ.1.1.ck) q y.1.toScheme), σ.2))).1,
          ((smAuthCut ΔFS ΔPCS k (.sm y.1.toScheme,
            ((y.2.1, σ.1.2.upd (ckaShadow σ.1.1.ck) q y.1.toScheme), σ.2))).2, y.2.2)) := by
  simp only [OracleAdv.simOracle, smAuthRootImpl, hs, ite_true, smAuthRootStep,
    OracleAdv.run_bind, PMF.map, PMF.bind_bind, PMF.pure_bind,
    Function.comp_def]
  refine congrArg _ (funext fun a => ?_)
  by_cases h : (σ.1.2.upd (ckaShadow σ.1.1.ck) q a.1.1.toScheme).safe ΔFS ΔPCS k = true
  · simp [h, smAuthCut, PMF.pure_bind]
  · simp [h, smAuthCut, PMF.pure_bind]

omit [DecidableEq W] [DecidableEq Ct] in
/-- Away from the opening of the epoch `k`, the simulator `smRootImplAt` asks no query and
answers as the oracle `smOracleOfAt` with any root step at the epoch `k`. -/
theorem smRootImplAt_step_noncrit (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t k : ℕ) (root : RK → Key → PMF (RK × Sa)) {U : Type}
    (O' : U → PPQuery RK Key → PMF ((RK × Sa) × U)) (s : SMSt Sc Msg RK Sa) (u : U)
    (q : SMQuery W) (hc : smCrit k s q = false) :
    OracleAdv.simOracle (smRootImplAt C R G D ΔFS ΔPCS t k) O' (s, u) q =
      (smOracleOfAt C R G D ΔFS ΔPCS t k false root s q).map fun y => (y.1, (y.2, u)) := by
  cases q with
  | ratchet p => exact smRoot_step_noncrit C R G D ΔFS ΔPCS k false root O' s u (.ratchet p) hc
  | recv p => exact smRoot_step_noncrit C R G D ΔFS ΔPCS t false root O' s u (.recv p) rfl
  | send p m => exact smRoot_step_noncrit C R G D ΔFS ΔPCS t false root O' s u (.send p m) rfl
  | chall p m => exact smRoot_step_noncrit C R G D ΔFS ΔPCS t false root O' s u (.chall p m) rfl
  | corrupt p => exact smRoot_step_noncrit C R G D ΔFS ΔPCS t false root O' s u (.corrupt p) rfl

variable [Fintype RK] [Nonempty RK] [Fintype Sa] [Nonempty Sa] [DecidableEq RK] [DecidableEq Key]

omit [DecidableEq W] [DecidableEq Ct] in
/-- **The simulator of the root step at the epoch `k` against the real PRF-PRNG game.** With the
hidden input `key`, each call of `smOracleOfAt` with the root step `fixedKeyRoot R key` at the
epoch `k`, with the PRF-PRNG state attached, is the call of `smRootImplAt` against the real
PRF-PRNG oracle. -/
theorem smRootImplAt_step_real (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t k : ℕ) (rk' : RK) (key : Key) (s : SMSt Sc Msg RK Sa) (q : SMQuery W) :
    (smOracleOfAt C R G D ΔFS ΔPCS t k false (fixedKeyRoot R key) s q).map
        (Prod.map id fun s => (s, (⟨rk', key, [], []⟩ : PPSt RK Key (RK × Sa)))) =
      OracleAdv.simOracle (smRootImplAt C R G D ΔFS ΔPCS t k)
        (ppOracle (rootFn R) false false) (s, ⟨rk', key, [], []⟩) q := by
  cases q with
  | ratchet p => exact smRoot_step_real C R G D ΔFS ΔPCS k false rk' key s (.ratchet p)
  | recv p => exact smRoot_step_real C R G D ΔFS ΔPCS t false rk' key s (.recv p)
  | send p m => exact smRoot_step_real C R G D ΔFS ΔPCS t false rk' key s (.send p m)
  | chall p m => exact smRoot_step_real C R G D ΔFS ΔPCS t false rk' key s (.chall p m)
  | corrupt p => exact smRoot_step_real C R G D ΔFS ΔPCS t false rk' key s (.corrupt p)

omit [DecidableEq W] [DecidableEq Ct] in
/-- **The simulator of the root step at the epoch `k` against the ideal PRF-PRNG game.** From a
state whose table of the `prf` oracle is empty unless the epoch `k` has been opened, each call of
`smRootImplAt` against the ideal PRF-PRNG oracle, with the PRF-PRNG state dropped, is the call
of `smOracleOfAt` with a uniform root output at the epoch `k`. -/
theorem smRootImplAt_step_ideal (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t k : ℕ) (s : SMSt Sc Msg RK Sa) (u : PPSt RK Key (RK × Sa))
    (hu : u.tR = [] ∨ smOpened k s) (q : SMQuery W) :
    (OracleAdv.simOracle (smRootImplAt C R G D ΔFS ΔPCS t k)
        (ppOracle (rootFn R) true true) (s, u) q).map (Prod.map id Prod.fst) =
      smOracleOfAt C R G D ΔFS ΔPCS t k false unifRoot s q := by
  cases q with
  | ratchet p => exact smRoot_step_ideal C R G D ΔFS ΔPCS k false s u hu (.ratchet p)
  | recv p =>
    rw [smRootImplAt_step_noncrit C R G D ΔFS ΔPCS t k unifRoot _ s u (.recv p) rfl,
      PMF.map_comp]
    exact PMF.map_id _
  | send p m =>
    rw [smRootImplAt_step_noncrit C R G D ΔFS ΔPCS t k unifRoot _ s u (.send p m) rfl,
      PMF.map_comp]
    exact PMF.map_id _
  | chall p m =>
    rw [smRootImplAt_step_noncrit C R G D ΔFS ΔPCS t k unifRoot _ s u (.chall p m) rfl,
      PMF.map_comp]
    exact PMF.map_id _
  | corrupt p =>
    rw [smRootImplAt_step_noncrit C R G D ΔFS ΔPCS t k unifRoot _ s u (.corrupt p) rfl,
      PMF.map_comp]
    exact PMF.map_id _

end RootSim

/-! ## The truncated hybrid and the opening of the epoch `k` -/

section HopOpen

variable {Sc Msg Key Rand RK Sa W Ct : Type} [Fintype Rand] [Nonempty Rand] [SampleableType W]
  [SampleableType Ct] [DecidableEq W] [DecidableEq Ct]

omit [DecidableEq W] [DecidableEq Ct] in
/-- Every call of `smOracleOfAt` keeps the epoch `k` opened. -/
theorem smOracleOfAt_opened (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t k : ℕ) (ideal : Bool) (root : RK → Key → PMF (RK × Sa))
    (s : SMSt Sc Msg RK Sa) (q : SMQuery W) (hs : smOpened k s) (x)
    (hx : x ∈ (smOracleOfAt C R G D ΔFS ΔPCS t k ideal root s q).support) :
    smOpened k x.2 := by
  have hm : ∀ P, s.ck.t P ≤ x.2.ck.t P := by
    cases q with
    | ratchet p => exact smOracleOf_t_mono C R G D ΔFS ΔPCS k ideal root s (.ratchet p) x hx
    | recv p => exact smOracleOf_t_mono C R G D ΔFS ΔPCS t ideal root s (.recv p) x hx
    | send p m => exact smOracleOf_t_mono C R G D ΔFS ΔPCS t ideal root s (.send p m) x hx
    | chall p m => exact smOracleOf_t_mono C R G D ΔFS ΔPCS t ideal root s (.chall p m) x hx
    | corrupt p => exact smOracleOf_t_mono C R G D ΔFS ΔPCS t ideal root s (.corrupt p) x hx
  rcases hs with h | h
  · exact Or.inl (h.trans (hm .A))
  · exact Or.inr (h.trans (hm .B))

/-- The secure-messaging states reached by a call of the truncated hybrid: the state of the
call, at a delivery or from an unsafe state, or a state reached by `smOracleOfAt` at a query of
the corruption game from a safe state. -/
theorem smAuthHopOracle_support (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t k : ℕ) (root : RK → Key → PMF (RK × Sa))
    (s : (SMSt Sc Msg RK Sa × SMAuthAux W Ct) × Bool) (d : SMAuthQuery W Ct) (x)
    (hx : x ∈ (smAuthHopOracle C R G D ΔFS ΔPCS t k root s d).support) :
    (x.2.1.1 = s.1.1 ∧ ∀ q, d = .sm q → s.1.2.safe ΔFS ΔPCS k = false) ∨
      ∃ q y, d = .sm q ∧ y ∈ (smOracleOfAt C R G D ΔFS ΔPCS t k false root s.1.1 q).support ∧
        x.2.1.1 = y.2 := by
  simp only [smAuthHopOracle, PMF.support_map, Set.mem_image] at hx
  obtain ⟨z, hz, rfl⟩ := hx
  have hz2 : (smAuthCut ΔFS ΔPCS k z).2 = z.2 := by
    unfold smAuthCut
    split <;> rfl
  rw [hz2]
  split at hz
  · cases d with
    | sm q =>
      simp only [smAuthHopStep, PMF.support_map, Set.mem_image] at hz
      obtain ⟨w, hw, rfl⟩ := hz
      exact Or.inr ⟨q, w, rfl, hw, rfl⟩
    | deliver p j ad c =>
      simp only [smAuthHopStep, PMF.support_pure, Set.mem_singleton_iff] at hz
      subst hz
      exact Or.inl ⟨rfl, fun q h => nomatch h⟩
  · rename_i h
    simp only [PMF.support_pure, Set.mem_singleton_iff] at hz
    subst hz
    exact Or.inl ⟨rfl, fun _ _ => by simpa using h⟩

/-- Every call of the truncated hybrid keeps the epoch `k` opened. -/
theorem smAuthHopOracle_opened (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t k : ℕ) (root : RK → Key → PMF (RK × Sa))
    (s : (SMSt Sc Msg RK Sa × SMAuthAux W Ct) × Bool) (d : SMAuthQuery W Ct)
    (hs : smOpened k s.1.1) (x)
    (hx : x ∈ (smAuthHopOracle C R G D ΔFS ΔPCS t k root s d).support) : smOpened k x.2.1.1 := by
  rcases smAuthHopOracle_support C R G D ΔFS ΔPCS t k root s d x hx with ⟨h, -⟩ | ⟨q, y, -, hy, h⟩
  · rw [h]; exact hs
  · rw [h]; exact smOracleOfAt_opened C R G D ΔFS ΔPCS t k false root s.1.1 q hs y hy

/-- The opening of the epoch `k` in the truncated hybrid leads to a state with the epoch `k`
opened. -/
theorem smAuthHopOracle_opened_of_crit (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t k : ℕ) (root : RK → Key → PMF (RK × Sa))
    (s : (SMSt Sc Msg RK Sa × SMAuthAux W Ct) × Bool) (d : SMAuthQuery W Ct)
    (hc : smAuthRootCrit ΔFS ΔPCS k s d = true) (x)
    (hx : x ∈ (smAuthHopOracle C R G D ΔFS ΔPCS t k root s d).support) : smOpened k x.2.1.1 := by
  rcases smAuthHopOracle_support C R G D ΔFS ΔPCS t k root s d x hx with
    ⟨-, h⟩ | ⟨q, y, rfl, hy, h⟩
  · cases d with
    | sm q =>
      simp only [smAuthRootCrit, Bool.and_eq_true] at hc
      simp [h q rfl] at hc
    | deliver p j ad c => simp [smAuthRootCrit] at hc
  · simp only [smAuthRootCrit, Bool.and_eq_true] at hc
    rw [h]
    cases q with
    | ratchet p =>
      exact smOracleOf_opened_of_crit C R G D ΔFS ΔPCS k false root s.1.1 (.ratchet p) hc.2 y hy
    | _ => simp [smCrit] at hc

/-- Away from the opening of the epoch `k`, the truncated hybrid does not depend on the root
step at the epoch `k`. -/
theorem smAuthHopOracle_root_congr (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t k : ℕ) (root root' : RK → Key → PMF (RK × Sa))
    (s : (SMSt Sc Msg RK Sa × SMAuthAux W Ct) × Bool) (d : SMAuthQuery W Ct)
    (hc : smAuthRootCrit ΔFS ΔPCS k s d = false) :
    smAuthHopOracle C R G D ΔFS ΔPCS t k root s d =
      smAuthHopOracle C R G D ΔFS ΔPCS t k root' s d := by
  by_cases hs : s.1.2.safe ΔFS ΔPCS k = true
  · cases d with
    | sm q =>
      have hq : smCrit k s.1.1 q = false := by simpa [smAuthRootCrit, hs] using hc
      have he : smOracleOfAt C R G D ΔFS ΔPCS t k false root s.1.1 q =
          smOracleOfAt C R G D ΔFS ΔPCS t k false root' s.1.1 q := by
        cases q with
        | ratchet p =>
          exact smOracleOf_root_congr C R G D ΔFS ΔPCS k false root root' s.1.1 (.ratchet p) hq
        | _ => rfl
      simp only [smAuthHopOracle, hs, ite_true, smAuthHopStep, he]
    | deliver p j ad c => rfl
  · simp only [smAuthHopOracle, hs, Bool.false_eq_true, ite_false]

end HopOpen

/-! ## The simulator of the truncated hybrid against the PRF-PRNG oracles -/

section HopSim

variable {Sc Msg Key Rand RK Sa W Ct : Type} [Fintype Rand] [Nonempty Rand] [SampleableType W]
  [SampleableType Ct] [DecidableEq W] [DecidableEq Ct]

/-- Away from the opening of the epoch `k`, the simulator of the root hop asks no query and
answers as the truncated hybrid with any root step at the epoch `k`. -/
theorem smAuthRoot_step_noncrit (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t k : ℕ) (root : RK → Key → PMF (RK × Sa)) {U : Type}
    (O' : U → PPQuery RK Key → PMF ((RK × Sa) × U))
    (σ : (SMSt Sc Msg RK Sa × SMAuthAux W Ct) × Bool) (u : U) (d : SMAuthQuery W Ct)
    (hc : smAuthRootCrit ΔFS ΔPCS k σ d = false) :
    OracleAdv.simOracle (smAuthRootImpl C R G D ΔFS ΔPCS t k) O' (σ, u) d =
      (smAuthHopOracle C R G D ΔFS ΔPCS t k root σ d).map fun z => (z.1, (z.2, u)) := by
  by_cases hs : σ.1.2.safe ΔFS ΔPCS k = true
  · cases d with
    | sm q =>
      have hq : smCrit k σ.1.1 q = false := by simpa [smAuthRootCrit, hs] using hc
      rw [smAuthRootImpl_simOracle C R G D ΔFS ΔPCS t k O' σ u q hs,
        smRootImplAt_step_noncrit C R G D ΔFS ΔPCS t k root O' σ.1.1 u q hq]
      simp only [smAuthHopOracle, hs, ite_true, smAuthHopStep, PMF.map_comp]
      rfl
    | deliver p j ad c =>
      simp [OracleAdv.simOracle, smAuthRootImpl, smAuthRootStep, smAuthHopOracle, smAuthHopStep,
        hs, PMF.pure_map, smAuthCut]
  · simp [OracleAdv.simOracle, smAuthRootImpl, smAuthHopOracle, hs, PMF.pure_map, smAuthCut]

variable [Fintype RK] [Nonempty RK] [Fintype Sa] [Nonempty Sa] [DecidableEq RK] [DecidableEq Key]

/-- **The simulator of the root hop against the real PRF-PRNG game.** With the hidden input
`key`, each call of the truncated hybrid with the root step `fixedKeyRoot R key` at the epoch
`k`, with the PRF-PRNG state attached, is the call of `smAuthRootImpl` against the real
PRF-PRNG oracle. -/
theorem smAuthRoot_step_real (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t k : ℕ) (rk' : RK) (key : Key) (σ : (SMSt Sc Msg RK Sa × SMAuthAux W Ct) × Bool)
    (d : SMAuthQuery W Ct) :
    (smAuthHopOracle C R G D ΔFS ΔPCS t k (fixedKeyRoot R key) σ d).map
        (Prod.map id fun s => (s, (⟨rk', key, [], []⟩ : PPSt RK Key (RK × Sa)))) =
      OracleAdv.simOracle (smAuthRootImpl C R G D ΔFS ΔPCS t k)
        (ppOracle (rootFn R) false false) (σ, ⟨rk', key, [], []⟩) d := by
  by_cases hs : σ.1.2.safe ΔFS ΔPCS k = true
  · cases d with
    | sm q =>
      rw [smAuthRootImpl_simOracle C R G D ΔFS ΔPCS t k _ σ _ q hs,
        ← smRootImplAt_step_real C R G D ΔFS ΔPCS t k rk' key σ.1.1 q]
      simp only [smAuthHopOracle, hs, ite_true, smAuthHopStep, PMF.map_comp]
      rfl
    | deliver p j ad c =>
      simp [OracleAdv.simOracle, smAuthRootImpl, smAuthRootStep, smAuthHopOracle, smAuthHopStep,
        hs, PMF.pure_map, smAuthCut]
  · simp [OracleAdv.simOracle, smAuthRootImpl, smAuthHopOracle, hs, PMF.pure_map, smAuthCut]

/-- **The simulator of the root hop against the ideal PRF-PRNG game.** From a state whose table
of the `prf` oracle is empty unless the epoch `k` has been opened, each call of
`smAuthRootImpl` against the ideal PRF-PRNG oracle, with the PRF-PRNG state dropped, is the call
of the truncated hybrid with a uniform root output at the epoch `k`. -/
theorem smAuthRoot_step_ideal (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t k : ℕ) (σ : (SMSt Sc Msg RK Sa × SMAuthAux W Ct) × Bool)
    (u : PPSt RK Key (RK × Sa)) (hu : u.tR = [] ∨ smOpened k σ.1.1) (d : SMAuthQuery W Ct) :
    (OracleAdv.simOracle (smAuthRootImpl C R G D ΔFS ΔPCS t k)
        (ppOracle (rootFn R) true true) (σ, u) d).map (Prod.map id Prod.fst) =
      smAuthHopOracle C R G D ΔFS ΔPCS t k unifRoot σ d := by
  by_cases hs : σ.1.2.safe ΔFS ΔPCS k = true
  · cases d with
    | sm q =>
      rw [smAuthRootImpl_simOracle C R G D ΔFS ΔPCS t k _ σ u q hs, PMF.map_comp]
      simp only [smAuthHopOracle, hs, ite_true, smAuthHopStep]
      rw [← smRootImplAt_step_ideal C R G D ΔFS ΔPCS t k σ.1.1 u hu q]
      simp only [PMF.map_comp]
      rfl
    | deliver p j ad c =>
      simp [OracleAdv.simOracle, smAuthRootImpl, smAuthRootStep, smAuthHopOracle, smAuthHopStep,
        hs, PMF.pure_map, smAuthCut]
  · simp [OracleAdv.simOracle, smAuthRootImpl, smAuthHopOracle, hs, PMF.pure_map, smAuthCut]

/-- The simulator of the root hop against the ideal PRF-PRNG game keeps the invariant of
`smAuthRoot_step_ideal`: the table of the `prf` oracle is empty unless the epoch `k` has been
opened. -/
theorem smAuthRoot_inv_ideal (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t k : ℕ) (σ : (SMSt Sc Msg RK Sa × SMAuthAux W Ct) × Bool)
    (u : PPSt RK Key (RK × Sa)) (hu : u.tR = [] ∨ smOpened k σ.1.1) (d : SMAuthQuery W Ct) :
    ∀ y ∈ (OracleAdv.simOracle (smAuthRootImpl C R G D ΔFS ΔPCS t k)
        (ppOracle (rootFn R) true true) (σ, u) d).support,
      y.2.2.tR = [] ∨ smOpened k y.2.1.1.1 := by
  intro y hy
  by_cases hc : smAuthRootCrit ΔFS ΔPCS k σ d = true
  · have hm : (y.1, y.2.1) ∈ (smAuthHopOracle C R G D ΔFS ΔPCS t k unifRoot σ d).support := by
      rw [← smAuthRoot_step_ideal C R G D ΔFS ΔPCS t k σ u hu d, PMF.support_map]
      exact ⟨y, hy, rfl⟩
    exact Or.inr (smAuthHopOracle_opened_of_crit C R G D ΔFS ΔPCS t k unifRoot σ d hc _ hm)
  · rw [smAuthRoot_step_noncrit C R G D ΔFS ΔPCS t k unifRoot _ σ u d (by simpa using hc)]
      at hy
    simp only [PMF.support_map, Set.mem_image] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    rcases hu with h | h
    · exact Or.inl h
    · exact Or.inr (smAuthHopOracle_opened C R G D ΔFS ΔPCS t k unifRoot σ d h z hz)

end HopSim

/-! ## The root hop of the forgery event -/

section RootHop

variable {Sc Msg Key Rand RK Sa W Ct : Type} [Fintype Rand] [Nonempty Rand] [SampleableType W]
  [SampleableType Ct] [DecidableEq W] [DecidableEq Ct] [Fintype RK] [Nonempty RK] [Fintype Key]
  [Nonempty Key]

omit [Fintype RK] [Nonempty RK] in
/-- **Eager sampling of the key of the root step at the epoch `k`.** The run of the truncated
hybrid with the root KDF on a uniform key at the epoch `k` is the run with the key drawn in
advance. -/
theorem smAuthHop_run_eager (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS t k : ℕ) {α : Type}
    (A : OracleAdv (SMAuthQuery W Ct) (SMAuthAns Msg Ct (SMPartySt Sc RK Sa) W) α)
    (s : (SMSt Sc Msg RK Sa × SMAuthAux W Ct) × Bool) :
    OracleAdv.run (smAuthHopOracle C R G D ΔFS ΔPCS t k (unifKeyRoot R)) A s =
      (PMF.uniformFintype Key).bind fun key =>
        OracleAdv.run (smAuthHopOracle C R G D ΔFS ΔPCS t k (fixedKeyRoot R key)) A s := by
  refine OracleAdv.run_eq_bind_eager _ _ (PMF.uniformFintype Key) (smAuthRootCrit ΔFS ΔPCS k)
    ?_ ?_ (fun s => smOpened k s.1.1) ?_ ?_ ?_ A s
  · intro s d hc
    cases d with
    | sm q =>
      simp only [smAuthRootCrit, Bool.and_eq_true] at hc
      cases q with
      | ratchet p =>
        have hroot : ∀ rk I, unifKeyRoot R rk I =
            (PMF.uniformFintype Key).bind fun v => fixedKeyRoot R v rk I := fun _ _ => rfl
        have hq := hc.2
        simp only [smCrit, Bool.and_eq_true] at hq
        have h : smOracleOfAt C R G D ΔFS ΔPCS t k false (unifKeyRoot R) s.1.1 (.ratchet p) =
            (PMF.uniformFintype Key).bind fun v =>
              smOracleOfAt C R G D ΔFS ΔPCS t k false (fixedKeyRoot R v) s.1.1 (.ratchet p) := by
          simp only [smOracleOfAt, smOracleOf, hq.1, hq.2, ite_true, hroot, PMF.bind_bind]
          exact PMF.bind_comm _ _ _
        simp only [smAuthHopOracle, hc.1, ite_true, smAuthHopStep, h, PMF.map_bind]
      | _ => simp [smCrit] at hc
    | deliver p j ad c => simp [smAuthRootCrit] at hc
  · intro v s d hc
    exact smAuthHopOracle_root_congr C R G D ΔFS ΔPCS t k _ _ s d hc
  · intro v s d hc x hx
    exact smAuthHopOracle_opened_of_crit C R G D ΔFS ΔPCS t k _ s d hc x hx
  · intro s d hs x hx
    exact smAuthHopOracle_opened C R G D ΔFS ΔPCS t k _ s d hs x hx
  · intro s d hs
    cases d with
    | sm q => simp [smAuthRootCrit, smCrit_of_opened k s.1.1 hs q]
    | deliver p j ad c => rfl

omit [Fintype Key] [Nonempty Key] in
/-- Running the PRF-PRNG reduction of the forgery event against an oracle is running the
adversary against the composed oracle from the drawn initial state, with the flag of a forgery
as output. -/
theorem smAuthRootRed_run (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS k : ℕ) (initP : PMF (Msg × Sc × Sc)) (A : SMAuthAdv Msg W Ct (SMPartySt Sc RK Sa))
    {U : Type} (O' : U → PPQuery RK Key → PMF ((RK × Sa) × U)) (u : U) :
    (OracleAdv.run O' (smAuthRootRed C R G D ΔFS ΔPCS k initP A) u).map Prod.fst =
      A.tStar.bind fun t => initP.bind fun i => (PMF.uniformFintype RK).bind fun rk =>
        (OracleAdv.run (OracleAdv.simOracle (smAuthRootImpl C R G D ΔFS ΔPCS t k) O')
          (A.play t i.1) (((smInit i rk, SMAuthAux.init), false), u)).map fun x => x.2.1.2 := by
  simp only [smAuthRootRed, smAuthRootTree, OracleAdv.run_rand, PMF.map_bind]
  refine congrArg _ (funext fun t => congrArg _ (funext fun i =>
    congrArg _ (funext fun rk => ?_)))
  rw [OracleAdv.run_bind, OracleAdv.run_simulate]
  simp [PMF.map_bind, PMF.bind_map, Function.comp_def, PMF.pure_map]
  rfl

variable [Fintype Sa] [Nonempty Sa] [DecidableEq RK] [DecidableEq Key]

omit [Fintype Key] [Nonempty Key] [Fintype Sa] [Nonempty Sa] [DecidableEq RK] [DecidableEq Key] in
/-- The truncated hybrid as the lift of a distribution: the challenge epoch, the CKA
initialisation, the root key and the run. -/
theorem smAuthHopGame_eq_liftPMF (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (initP : PMF (Msg × Sc × Sc)) (hinit : C.init = liftPMF initP)
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS k : ℕ) (root : RK → Key → PMF (RK × Sa))
    (A : SMAuthAdv Msg W Ct (SMPartySt Sc RK Sa)) :
    smAuthHopGame C R G D ΔFS ΔPCS k root A =
      liftPMF (A.tStar.bind fun t => initP.bind fun i => (PMF.uniformFintype RK).bind fun rk =>
        (OracleAdv.run (smAuthHopOracle C R G D ΔFS ΔPCS t k root) (A.play t i.1)
          ((smInit i rk, SMAuthAux.init), false)).map fun x => x.2.2) := by
  simp only [smAuthHopGame, hinit, sample_eq_liftPMF, liftPMF_bind_liftPMF]

/-- **The real side of the root hop.** The real PRF-PRNG game of `smAuthRootRed` is the
truncated hybrid with the root KDF on a uniform key at the epoch `k`. -/
theorem smAuthRoot_real_eq (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (initP : PMF (Msg × Sc × Sc)) (hinit : C.init = liftPMF initP)
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS k : ℕ) (A : SMAuthAdv Msg W Ct (SMPartySt Sc RK Sa)) :
    pp_game (rootFn R) false false (smAuthRootRed C R G D ΔFS ΔPCS k initP A) =
      smAuthHopGame C R G D ΔFS ΔPCS k (unifKeyRoot R) A := by
  rw [smAuthHopGame_eq_liftPMF C initP hinit]
  unfold pp_game
  congr 1
  have h1 : ∀ (rk' : RK) (key : Key),
      (OracleAdv.run (ppOracle (rootFn R) false false)
        (smAuthRootRed C R G D ΔFS ΔPCS k initP A) ⟨rk', key, [], []⟩).map Prod.fst =
      A.tStar.bind fun t => initP.bind fun i => (PMF.uniformFintype RK).bind fun rk =>
        (OracleAdv.run (smAuthHopOracle C R G D ΔFS ΔPCS t k (fixedKeyRoot R key))
          (A.play t i.1) ((smInit i rk, SMAuthAux.init), false)).map fun x => x.2.2 := by
    intro rk' key
    rw [smAuthRootRed_run]
    refine congrArg _ (funext fun t => congrArg _ (funext fun i =>
      congrArg _ (funext fun rk => ?_)))
    rw [← OracleAdv.run_map_state _ _ (fun s => (s, (⟨rk', key, [], []⟩ : PPSt RK Key (RK × Sa))))
      (smAuthRoot_step_real C R G D ΔFS ΔPCS t k rk' key), PMF.map_comp]
    rfl
  simp only [h1, PMF.bind_const]
  have h2 : ∀ (t : ℕ) (i : Msg × Sc × Sc) (rk : RK),
      (OracleAdv.run (smAuthHopOracle C R G D ΔFS ΔPCS t k (unifKeyRoot R)) (A.play t i.1)
        ((smInit i rk, SMAuthAux.init), false)).map (fun x => x.2.2) =
      (PMF.uniformFintype Key).bind fun key =>
        (OracleAdv.run (smAuthHopOracle C R G D ΔFS ΔPCS t k (fixedKeyRoot R key))
          (A.play t i.1) ((smInit i rk, SMAuthAux.init), false)).map fun x => x.2.2 := by
    intro t i rk
    rw [smAuthHop_run_eager, PMF.map_bind]
  simp only [h2, PMF.bind_comm (PMF.uniformFintype Key)]

/-- **The ideal side of the root hop.** The ideal PRF-PRNG game of `smAuthRootRed` is the
truncated hybrid with a uniform root output at the epoch `k`. -/
theorem smAuthRoot_ideal_eq (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (initP : PMF (Msg × Sc × Sc)) (hinit : C.init = liftPMF initP)
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS k : ℕ) (A : SMAuthAdv Msg W Ct (SMPartySt Sc RK Sa)) :
    pp_game (rootFn R) true true (smAuthRootRed C R G D ΔFS ΔPCS k initP A) =
      smAuthHopGame C R G D ΔFS ΔPCS k unifRoot A := by
  rw [smAuthHopGame_eq_liftPMF C initP hinit]
  unfold pp_game
  congr 1
  have h1 : ∀ (rk' : RK) (key : Key),
      (OracleAdv.run (ppOracle (rootFn R) true true)
        (smAuthRootRed C R G D ΔFS ΔPCS k initP A) ⟨rk', key, [], []⟩).map Prod.fst =
      A.tStar.bind fun t => initP.bind fun i => (PMF.uniformFintype RK).bind fun rk =>
        (OracleAdv.run (smAuthHopOracle C R G D ΔFS ΔPCS t k unifRoot)
          (A.play t i.1) ((smInit i rk, SMAuthAux.init), false)).map fun x => x.2.2 := by
    intro rk' key
    rw [smAuthRootRed_run]
    refine congrArg _ (funext fun t => congrArg _ (funext fun i =>
      congrArg _ (funext fun rk => ?_)))
    have h := OracleAdv.run_map_state_inv _ (smAuthHopOracle C R G D ΔFS ΔPCS t k unifRoot)
      Prod.fst (fun x => x.2.tR = [] ∨ smOpened k x.1.1.1)
      (fun x d hx => smAuthRoot_inv_ideal C R G D ΔFS ΔPCS t k x.1 x.2 hx d)
      (fun x d hx => smAuthRoot_step_ideal C R G D ΔFS ΔPCS t k x.1 x.2 hx d) (A.play t i.1)
      (((smInit i rk, SMAuthAux.init), false), (⟨rk', key, [], []⟩ : PPSt RK Key (RK × Sa)))
      (Or.inl rfl)
    refine Eq.trans ?_ (congrArg (PMF.map fun x => x.2.2) h)
    rw [PMF.map_comp]
    rfl
  simp only [h1, PMF.bind_const]

/-- **The game after the root hop of the forgery event at the epoch `k`**: the truncated hybrid
with a uniform root output at the opening of the epoch `k`, whose receiving chain of the epoch
`k` starts from a uniform state. The FS-AEAD integrity hop starts from it. -/
noncomputable def smAuthRootIdealGame (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS k : ℕ) (A : SMAuthAdv Msg W Ct (SMPartySt Sc RK Sa)) : SPComp Bool :=
  smAuthHopGame C R G D ΔFS ΔPCS k unifRoot A

/-- **The root hop of the forgery event at the epoch `k`.** For an initialisation that is the
lift of `initP`, the probability of a forgery at the epoch `k` in the truncated hybrid with the
root KDF on a uniform key at the epoch `k` is at most the PRF-PRNG advantage of `R` at the
reduction `smAuthRootRed C R G D ΔFS ΔPCS k initP A` plus the probability of a forgery in
`smAuthRootIdealGame`. -/
theorem smAuthHopGame_le_root (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (initP : PMF (Msg × Sc × Sc)) (hinit : C.init = liftPMF initP)
    (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ΔFS ΔPCS k : ℕ) (A : SMAuthAdv Msg W Ct (SMPartySt Sc RK Sa)) :
    prTrue (smAuthHopGame C R G D ΔFS ΔPCS k (unifKeyRoot R) A) Heap.empty ≤
      PRFPRNG_Advantage R (smAuthRootRed C R G D ΔFS ΔPCS k initP A) +
        prTrue (smAuthRootIdealGame C R G D ΔFS ΔPCS k A) Heap.empty := by
  unfold smAuthRootIdealGame
  rw [← smAuthRoot_real_eq C initP hinit, ← smAuthRoot_ideal_eq C initP hinit]
  unfold PRFPRNG_Advantage Advantage
  exact le_tsub_add.trans (add_le_add le_sup_left le_rfl)

/-- **The CKA and root hops of the forgery event at the epoch `k`.** For a CKA correct along `J`
with a sound explicit-randomness sending algorithm, an initialisation that is the lift of
`initP` and initial states related by `J`, the probability of a forgery at the epoch `k` in the
truncated game over `acdAuthSM C R G D` is at most the CKA corruption advantage of
`smAuthCKARed R G D ΔFS ΔPCS k A`, plus the PRF-PRNG advantage of `R` at
`smAuthRootRed C R G D ΔFS ΔPCS k initP A`, plus the probability of a forgery in
`smAuthRootIdealGame`. -/
theorem acdAuthSM_truncGame_le_root (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (hS : CKACoins.Sound C) {J : Sc → Sc → Prop} (hJ : CKACorrect C J)
    (initP : PMF (Msg × Sc × Sc)) (hinit : C.init = liftPMF initP)
    (hJi : ∀ i ∈ initP.support, J i.2.1 i.2.2) (R : PRGDef (RK × Key) (RK × Sa))
    (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (ΔFS ΔPCS k : ℕ)
    (A : SMAuthAdv Msg W Ct (SMPartySt Sc RK Sa)) :
    prTrue (smAuthTruncGame (acdAuthSM C R G D) ΔFS ΔPCS k A) Heap.empty ≤
      CKA_Corrupt_Advantage C ΔFS ΔPCS (smAuthCKARed R G D ΔFS ΔPCS k A) +
        PRFPRNG_Advantage R (smAuthRootRed C R G D ΔFS ΔPCS k initP A) +
        prTrue (smAuthRootIdealGame C R G D ΔFS ΔPCS k A) Heap.empty := by
  refine (acdAuthSM_truncGame_le_cka C hS hJ initP hinit hJi R G D ΔFS ΔPCS k A).trans ?_
  rw [add_assoc]
  exact add_le_add le_rfl (smAuthHopGame_le_root C initP hinit R G D ΔFS ΔPCS k A)

end RootHop

end CatCrypt.Crypto.Messaging
