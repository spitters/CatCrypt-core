/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.SignalStackSM
public import CatCryptCore.Crypto.Messaging.CKAPrekey

/-!
# The responder gate and the efficient form of the ratchet at the signed-prekey pair

The scheme `M.gateB` is the scheme `M` whose party states carry a flag: the party has opened an
epoch. The first sender `A` starts with the flag set, the first receiver `B` without it; opening an
epoch sets it, and a corruption of a party whose flag is not set is answered with `none`. At the
signed-prekey pair of Signal's ratchet initialisation, the state of `B` before its first opening
holds the prekey secret, and the gate refuses its corruption.

The gate is a scheme transformer: a simulation of schemes passes to the gated schemes
(`SMScheme.Sim.gateB`), and the corruption game over `M.gateB` is the game over `M` against the
adversary `A.gateB`, which tracks the openings of `B` from the answers and answers a refused
corruption itself (`smSchemeGame_gateB`).

The CKA `dhCKAPre decE d` is the Diffie–Hellman CKA started from the public value `d` alone: its
initialisation draws the secret key `x₁` of the first epoch, the first sender holds `x₁` and sends
`g ^ decE x₁` with the key `d ^ decE x₁`, and the first receiver holds the message and the key of
the first epoch. Under the gate, the session view of the double ratchet at the signed-prekey pair
`dhPairInit decE x₀` is the session view of the double ratchet over `dhCKAPre decE (g ^ decE x₀)`,
with the corruption answers relabelled by `dhPreOpen` (`smSessView_pair_eq_pre`). The latter is
computed from the public value `g ^ decE x₀` alone. The proof draws the key of the first epoch at
the initialisation (`OracleAdv.run_eager`) and uses `(g ^ x₁) ^ x₀ = (g ^ x₀) ^ x₁`
(`elemPow_pow_comm`).

## Main definitions

* `SMScheme.gateB`, `gateIni`, `SMSchemeAdv.gateB` — the gate on schemes, keyed initialisations
  and adversaries
* `DHPreSt`, `dhCKAPre`, `dhCKAPreCoins`, `dhPreOpen` — the Diffie–Hellman CKA from a public
  value with the first key drawn at the initialisation
* `acdIniPair` — the keyed initialisation of the ACD construction at a given initial pair

## Main results

* `SMScheme.Sim.gateB` — simulations pass to the gated schemes
* `smSchemeGame_gateB` — the game over a gated scheme as a game over the scheme
* `smSessView_pair_eq_pre` — the gated session view at the signed-prekey pair is the gated
  session view of the efficient form
-/

set_option autoImplicit false

@[expose] public section

namespace CatCrypt.Crypto.Messaging

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCryptCore.Examples.CyclicGroupDDH
open CatCrypt.Crypto.Messaging.SignalStackSM CatCrypt.Crypto.Assumptions CatCrypt.Crypto.PRPPRF
open scoped ENNReal

/-! ## The gate -/

/-- The opening flag of party `p` when the flag of `B` is `b`: `A` has always opened an epoch
(it is the first sender), `B` has opened one when `b` holds. -/
def gateFlag : CKAParty → Bool → Bool
  | .A, _ => true
  | .B, b => b

section Gate

variable {St Pub Rand W Ct Leak : Type}

/-- The initial pair of the gated scheme: `A` with the opening flag set, `B` without it. -/
def gateInit (i : Pub × St × St) : Pub × (St × Bool) × (St × Bool) :=
  (i.1, (i.2.1, true), (i.2.2, false))

/-- **The responder gate.** The party states of `M.gateB` carry the flag that the party has
opened an epoch; `A` starts with it, `B` without it, and opening an epoch sets it. A corruption
of a party with the flag is answered by the corruption answer of `M`, and of a party without it
by `none`. -/
noncomputable def SMScheme.gateB (M : SMScheme St Pub Rand W Ct Leak) :
    SMScheme (St × Bool) Pub Rand W Ct (Option Leak) where
  init := SPComp.bind M.init fun i => SPComp.pure (gateInit i)
  ratchet x r := (((M.ratchet x.1 r).1, true), (M.ratchet x.1 r).2)
  recv x T := (M.recv x.1 T, x.2)
  send x m := (M.send x.1 m).map fun y => ((y.1, x.2), y.2)
  expose x := if x.2 then some (M.expose x.1) else none
  idealCt := M.idealCt

/-- The gated keyed initialisation: the initial pair of `ini k` with the opening flags of
`gateInit`. -/
noncomputable def gateIni {K : Type} (ini : K → SPComp (Pub × St × St)) (k : K) :
    SPComp (Pub × (St × Bool) × (St × Bool)) :=
  SPComp.bind (ini k) fun i => SPComp.pure (gateInit i)

/-- The game state over `M.gateB` of the game state `s` over `M` when the flag of `B` is `b`. -/
def SMSchemeSt.gate (s : SMSchemeSt St Pub) (b : Bool) : SMSchemeSt (St × Bool) Pub :=
  ⟨⟨fun p => (s.ck.st p, gateFlag p b), s.ck.t, s.ck.msg⟩, s.done⟩

/-- The answer over `M.gateB` to the query `q` with the answer `a` over `M`, when the flag of
`B` is `b`: a corruption answer of a party without the flag becomes `none`, every other answer
is kept. -/
def gateAns (b : Bool) (q : SMQuery W) (a : SMSchemeAns Pub Ct Leak) :
    SMSchemeAns Pub Ct (Option Leak) :=
  a.map id id fun σ =>
    match q with
    | .corrupt p => if gateFlag p b then some σ else none
    | _ => some σ

/-- The flag of `B` after the query `q` with the answer `a`: set by an epoch opened by `B`. -/
def gateNext (b : Bool) (q : SMQuery W) (a : SMSchemeAns Pub Ct Leak) : Bool :=
  match q, a with
  | .ratchet .B, .msg _ => true
  | _, _ => b

/-- An adversary against `M.gateB` as an adversary against `M`, from the flag `b` of `B`: it
tracks the epochs opened by `B` and replaces the corruption answer of a party without the flag
by `none`. -/
def gateAdv {α : Type} :
    Bool → OracleAdv (SMQuery W) (SMSchemeAns Pub Ct (Option Leak)) α →
      OracleAdv (SMQuery W) (SMSchemeAns Pub Ct Leak) α
  | _, .ret a => .ret a
  | b, .rand p k => .rand p fun x => gateAdv b (k x)
  | b, .query d k => .query d fun a => gateAdv (gateNext b d a) (k (gateAns b d a))

/-- **The gated adversary**: an adversary against `M.gateB` as an adversary against `M`. -/
def SMSchemeAdv.gateB (A : SMSchemeAdv Pub W Ct (Option Leak)) : SMSchemeAdv Pub W Ct Leak where
  tStar := A.tStar
  play t T := gateAdv false (A.play t T)

theorem SMSchemeSt.init_gateInit (i : Pub × St × St) :
    SMSchemeSt.init (gateInit i) = (SMSchemeSt.init i).gate false := by
  simp only [SMSchemeSt.init, gateInit, SMSchemeSt.gate, CKAGameSt.init]
  congr 2
  funext p
  cases p <;> rfl

theorem SMSchemeSt.gate_sent (s : SMSchemeSt St Pub) (b : Bool) (p : CKAParty) (x : St)
    (T : Pub) (d : Bool) :
    (⟨(s.gate b).ck.sent p (x, true) T, d⟩ : SMSchemeSt (St × Bool) Pub) =
      (⟨s.ck.sent p x T, d⟩ : SMSchemeSt St Pub).gate
        (gateNext b (.ratchet p : SMQuery W) (.msg T : SMSchemeAns Pub Ct Leak)) := by
  simp only [SMSchemeSt.gate, CKAGameSt.sent, SMSchemeSt.mk.injEq, and_true]
  congr 1
  funext q
  cases p <;> cases q <;> simp [Function.update, gateFlag, gateNext]

theorem SMSchemeSt.gate_recvd (s : SMSchemeSt St Pub) (b : Bool) (p : CKAParty) (y : St)
    (d : Bool) :
    (⟨(s.gate b).ck.recvd p (y, gateFlag p b), d⟩ : SMSchemeSt (St × Bool) Pub) =
      (⟨s.ck.recvd p y, d⟩ : SMSchemeSt St Pub).gate b := by
  simp only [SMSchemeSt.gate, CKAGameSt.recvd, SMSchemeSt.mk.injEq, and_true]
  congr 1
  funext q
  cases p <;> cases q <;> simp [Function.update]

theorem SMSchemeSt.gate_upd (s : SMSchemeSt St Pub) (b : Bool) (p : CKAParty) (y : St)
    (d : Bool) : (s.gate b).upd p (y, gateFlag p b) d = (s.upd p y d).gate b := by
  simp only [SMSchemeSt.gate, SMSchemeSt.upd, SMSchemeSt.mk.injEq, and_true]
  congr 1
  funext q
  cases p <;> cases q <;> simp [Function.update]

variable [Fintype Rand] [Nonempty Rand]

/-- **A call of the oracle over a gated scheme** is the call over the scheme with the answer
gated and the flag of `B` advanced. -/
theorem smSchemeOracle_gateB (M : SMScheme St Pub Rand W Ct Leak) (ΔFS ΔPCS t : ℕ)
    (ideal : Bool) (s : SMSchemeSt St Pub) (b : Bool) (q : SMQuery W) :
    smSchemeOracle M.gateB ΔFS ΔPCS t ideal (s.gate b) q =
      (smSchemeOracle M ΔFS ΔPCS t ideal s q).map fun y =>
        (gateAns b q y.1, y.2.gate (gateNext b q y.1)) := by
  have hst : ∀ p, (s.gate b).ck.st p = (s.ck.st p, gateFlag p b) := fun _ => rfl
  have hcs : ∀ p, (s.gate b).ck.canSend p = s.ck.canSend p := fun _ => rfl
  have hcr : ∀ p, (s.gate b).ck.canRecv p = s.ck.canRecv p := fun _ => rfl
  have hT : (s.gate b).ck.t = s.ck.t := rfl
  have hd : (s.gate b).done = s.done := rfl
  have hac : ∀ p, ckaAllowCorr ΔFS ΔPCS t (s.gate b).ck p = ckaAllowCorr ΔFS ΔPCS t s.ck p :=
    fun _ => rfl
  cases q with
  | ratchet p =>
    simp only [smSchemeOracle, hcs, hd]
    by_cases hc : s.ck.canSend p = true
    · simp only [hc, ite_true, PMF.map_bind, PMF.pure_map, hst, SMScheme.gateB]
      refine congrArg _ (funext fun r => ?_)
      rw [SMSchemeSt.gate_sent (W := W) (Ct := Ct) (Leak := Leak)]
      rfl
    · simp only [hc, Bool.false_eq_true, ite_false, PMF.pure_map]
      cases p <;> rfl
  | recv p =>
    simp only [smSchemeOracle, hcr, hd]
    by_cases hc : s.ck.canRecv p = true
    · simp only [hc, ite_true, PMF.pure_map, hst, SMScheme.gateB]
      rw [← SMSchemeSt.gate_recvd]
      rfl
    · simp only [hc, Bool.false_eq_true, ite_false, PMF.pure_map]
      rfl
  | send p m =>
    simp only [smSchemeOracle, hT, hd]
    by_cases hc : (ckaSender (s.ck.t p) == p) = true
    · simp only [hc, ite_true, hst, SMScheme.gateB]
      cases h : M.send (s.ck.st p) m with
      | none => simp only [Option.map_none, PMF.pure_map]; rfl
      | some y =>
        simp only [Option.map_some, PMF.pure_map, SMSchemeSt.gate_upd]
        rfl
    · simp only [hc, Bool.false_eq_true, ite_false, PMF.pure_map]
      rfl
  | chall p m =>
    simp only [smSchemeOracle, hT, hd]
    by_cases hc : (!s.done && (ckaSender (s.ck.t p) == p) && (s.ck.t p == t)) = true
    · simp only [hc, ite_true, hst, SMScheme.gateB]
      cases h : M.send (s.ck.st p) m with
      | none => simp only [Option.map_none, PMF.pure_map]; rfl
      | some y =>
        simp only [Option.map_some, PMF.map_bind, PMF.pure_map, SMSchemeSt.gate_upd]
        rfl
    · simp only [hc, Bool.false_eq_true, ite_false, PMF.pure_map]
      rfl
  | corrupt p =>
    simp only [smSchemeOracle, hac, PMF.pure_map]
    by_cases hc : ckaAllowCorr ΔFS ΔPCS t s.ck p = true
    · simp only [hc, ite_true, hst, SMScheme.gateB, gateAns, gateNext, SMSchemeAns.map]
    · simp only [hc, Bool.false_eq_true, ite_false]
      rfl

/-- A run against the oracle over a gated scheme is the run of the gated adversary against the
oracle over the scheme. -/
theorem run_smSchemeOracle_gateB {α : Type} (M : SMScheme St Pub Rand W Ct Leak)
    (ΔFS ΔPCS t : ℕ) (ideal : Bool)
    (A : OracleAdv (SMQuery W) (SMSchemeAns Pub Ct (Option Leak)) α) (s : SMSchemeSt St Pub)
    (b : Bool) :
    (OracleAdv.run (smSchemeOracle M.gateB ΔFS ΔPCS t ideal) A (s.gate b)).map Prod.fst =
      (OracleAdv.run (smSchemeOracle M ΔFS ΔPCS t ideal) (gateAdv b A) s).map Prod.fst := by
  induction A generalizing s b with
  | ret a => simp only [gateAdv, OracleAdv.run_ret, PMF.pure_map]
  | rand p k ih => simp only [gateAdv, OracleAdv.run_rand, PMF.map_bind, ih]
  | query d k ih =>
    simp only [gateAdv, OracleAdv.run_query, PMF.map_bind, smSchemeOracle_gateB, PMF.bind_map]
    exact congrArg _ (funext fun y => ih _ _ _)

/-- **The corruption game over a gated scheme** is the corruption game over the scheme against
the gated adversary. -/
theorem smSchemeGame_gateB (M : SMScheme St Pub Rand W Ct Leak) (ΔFS ΔPCS : ℕ) (ideal : Bool)
    (A : SMSchemeAdv Pub W Ct (Option Leak)) :
    smCorruptGame M.gateB ΔFS ΔPCS ideal A = smCorruptGame M ΔFS ΔPCS ideal A.gateB := by
  simp only [smCorruptGame, SMScheme.gateB, SPComp.bind_assoc, SPComp.pure_bind,
    SMSchemeAdv.gateB]
  refine congrArg _ (funext fun t => congrArg _ (funext fun i => congrArg _ ?_))
  rw [SMSchemeSt.init_gateInit]
  exact run_smSchemeOracle_gateB M ΔFS ΔPCS t ideal _ _ false

end Gate

section GateSim

variable {St Pub Rand W Ct Leak St' Pub' Ct' Leak' : Type}

/-- **Simulations pass to the gated schemes**, along the relation of the states with equal
flags, with the corruption answers encoded under `some`. -/
theorem SMScheme.Sim.gateB {M' : SMScheme St' Pub' Rand W Ct' Leak'}
    {M : SMScheme St Pub Rand W Ct Leak} {ρ : St' → St → Prop} {encP : Pub → Pub'}
    {encC : Ct → Ct'} {encL : Leak → Leak'} {encI : St → St'}
    (h : M'.Sim M ρ encP encC encL encI) :
    M'.gateB.Sim M.gateB (fun x' x => ρ x'.1 x.1 ∧ x'.2 = x.2) encP encC (Option.map encL)
      (fun x => (encI x.1, x.2)) where
  init := by
    simp only [SMScheme.gateB, h.init, SPComp.bind_assoc, SPComp.pure_bind]
    rfl
  init_rel x := ⟨h.init_rel x.1, rfl⟩
  ratchet x' x r hx := ⟨⟨(h.ratchet _ _ r hx.1).1, rfl⟩, (h.ratchet _ _ r hx.1).2⟩
  recv x' x T hx := ⟨h.recv _ _ T hx.1, hx.2⟩
  send x' x m hx := by
    have hr := h.send x'.1 x.1 m hx.1
    simp only [SMScheme.gateB]
    cases h1 : M'.send x'.1 m <;> cases h2 : M.send x.1 m <;> rw [h1, h2] at hr <;> cases hr
    · exact Option.Rel.none
    · rename_i y' y hy
      exact Option.Rel.some ⟨⟨hy.1, hx.2⟩, hy.2⟩
  expose x' x hx := by
    simp only [SMScheme.gateB, hx.2]
    cases x.2 <;> simp [h.expose _ _ hx.1]
  idealCt := h.idealCt

end GateSim

/-! ## Mapping the party states of the multi-challenge game -/

section MapSt

variable {St St' Pub Rand W Ct Leak Leak' : Type}

/-- The game state `s` with the party states mapped by `g`. -/
def SMSchemeSt.mapSt (g : St → St') (s : SMSchemeSt St Pub) : SMSchemeSt St' Pub :=
  ⟨⟨fun p => g (s.ck.st p), s.ck.t, s.ck.msg⟩, s.done⟩

theorem SMSchemeSt.mapSt_sent (g : St → St') (s : SMSchemeSt St Pub) (p : CKAParty) (x : St)
    (T : Pub) (d : Bool) :
    (⟨s.ck.sent p x T, d⟩ : SMSchemeSt St Pub).mapSt g = ⟨(s.mapSt g).ck.sent p (g x) T, d⟩ := by
  simp only [SMSchemeSt.mapSt, CKAGameSt.sent, SMSchemeSt.mk.injEq, and_true]
  congr 1
  funext q
  by_cases hq : q = p
  · subst hq; simp
  · simp [Function.update_of_ne hq]

theorem SMSchemeSt.mapSt_recvd (g : St → St') (s : SMSchemeSt St Pub) (p : CKAParty) (x : St)
    (d : Bool) :
    (⟨s.ck.recvd p x, d⟩ : SMSchemeSt St Pub).mapSt g = ⟨(s.mapSt g).ck.recvd p (g x), d⟩ := by
  simp only [SMSchemeSt.mapSt, CKAGameSt.recvd, SMSchemeSt.mk.injEq, and_true]
  congr 1
  funext q
  by_cases hq : q = p
  · subst hq; simp
  · simp [Function.update_of_ne hq]

theorem SMSchemeSt.mapSt_upd (g : St → St') (s : SMSchemeSt St Pub) (p : CKAParty) (x : St)
    (d : Bool) : (s.upd p x d).mapSt g = (s.mapSt g).upd p (g x) d := by
  simp only [SMSchemeSt.mapSt, SMSchemeSt.upd, SMSchemeSt.mk.injEq, and_true]
  congr 1
  funext q
  by_cases hq : q = p
  · subst hq; simp
  · simp [Function.update_of_ne hq]

variable [Fintype Rand] [Nonempty Rand]

/-- **A call of the multi-challenge oracle along a map of party states.** If, at the state `s`,
the scheme `M'` on the mapped party states opens the epoch of the query on the same randomness,
receives the public value in transit, sends and answers corruptions as `M` does, with the party
states mapped by `g` and the corruption answers by `e`, the call of the oracle over `M'` at the
mapped state is the call over `M` with the answer and the state mapped. -/
theorem smMultiOracle_mapSt (M : SMScheme St Pub Rand W Ct Leak)
    (M' : SMScheme St' Pub Rand W Ct Leak') (g : St → St') (e : Leak → Leak')
    (ΔFS ΔPCS t n : ℕ) (mode : ℕ → Bool) (s : SMSchemeSt St Pub) (c : ℕ) (q : SMQuery W)
    (hrat : ∀ p, q = .ratchet p → s.ck.canSend p = true → ∀ r,
      M'.ratchet (g (s.ck.st p)) r = (g (M.ratchet (s.ck.st p) r).1, (M.ratchet (s.ck.st p) r).2))
    (hrecv : ∀ p, q = .recv p → s.ck.canRecv p = true →
      M'.recv (g (s.ck.st p)) s.ck.msg = g (M.recv (s.ck.st p) s.ck.msg))
    (hsend : ∀ x m, M'.send (g x) m = (M.send x m).map fun y => (g y.1, y.2))
    (hexp : ∀ p, M'.expose (g (s.ck.st p)) = e (M.expose (s.ck.st p)))
    (hideal : M'.idealCt = M.idealCt) :
    (smMultiOracle M ΔFS ΔPCS t n mode (s, c) q).map
        (fun y => (y.1.map id id e, (y.2.1.mapSt g, y.2.2))) =
      smMultiOracle M' ΔFS ΔPCS t n mode (s.mapSt g, c) q := by
  have hst : ∀ p, (s.mapSt g).ck.st p = g (s.ck.st p) := fun _ => rfl
  have hcs : ∀ p, (s.mapSt g).ck.canSend p = s.ck.canSend p := fun _ => rfl
  have hcr : ∀ p, (s.mapSt g).ck.canRecv p = s.ck.canRecv p := fun _ => rfl
  have hT : (s.mapSt g).ck.t = s.ck.t := rfl
  have hm : (s.mapSt g).ck.msg = s.ck.msg := rfl
  have hd : (s.mapSt g).done = s.done := rfl
  have hac : ∀ p, ckaAllowCorr ΔFS ΔPCS t (s.mapSt g).ck p = ckaAllowCorr ΔFS ΔPCS t s.ck p :=
    fun _ => rfl
  cases q with
  | ratchet p =>
    simp only [smMultiOracle, smSchemeOracle, hcs, hd, hst, PMF.map_comp]
    by_cases hc : s.ck.canSend p = true
    · simp only [hc, ite_true, PMF.map_bind, PMF.pure_map]
      refine congrArg _ (funext fun r => ?_)
      rw [hrat p rfl hc r]
      simp only [Function.comp_apply, SMSchemeSt.mapSt_sent]
      rfl
    · simp only [hc, Bool.false_eq_true, ite_false, PMF.pure_map]
      rfl
  | recv p =>
    simp only [smMultiOracle, smSchemeOracle, hcr, hd, hst, hm, PMF.map_comp]
    by_cases hc : s.ck.canRecv p = true
    · simp only [hc, ite_true, PMF.pure_map, hrecv p rfl hc]
      simp only [Function.comp_apply, SMSchemeSt.mapSt_recvd]
      rfl
    · simp only [hc, Bool.false_eq_true, ite_false, PMF.pure_map]
      rfl
  | send p m =>
    simp only [smMultiOracle, smSchemeOracle, hT, hd, hst, PMF.map_comp, hsend]
    by_cases hc : (ckaSender (s.ck.t p) == p) = true
    · simp only [hc, ite_true]
      cases h : M.send (s.ck.st p) m with
      | none => simp only [Option.map_none, PMF.pure_map]; rfl
      | some y =>
        simp only [Option.map_some, PMF.pure_map, Function.comp_apply, SMSchemeSt.mapSt_upd]
        rfl
    · simp only [hc, Bool.false_eq_true, ite_false, PMF.pure_map]
      rfl
  | chall p m =>
    simp only [smMultiOracle, hT, hst, hsend, hideal]
    by_cases hc : c < n ∧ ckaSender (s.ck.t p) = p ∧ s.ck.t p = t
    · simp only [ite_eq_left hc]
      cases h : M.send (s.ck.st p) m with
      | none => simp only [Option.map_none, PMF.pure_map]; rfl
      | some y =>
        simp only [Option.map_some, PMF.map_bind, PMF.pure_map, SMSchemeSt.mapSt_upd, hd]
        rfl
    · simp only [ite_eq_right hc, PMF.pure_map]
      rfl
  | corrupt p =>
    simp only [smMultiOracle, smSchemeOracle, hac, PMF.pure_map, hst, hexp]
    by_cases hc : ckaAllowCorr ΔFS ΔPCS t s.ck p = true
    · simp only [hc, ite_true]
      rfl
    · simp only [hc, Bool.false_eq_true, ite_false]
      rfl

end MapSt

/-! ## The first epoch of `A` on randomness drawn in advance -/

section Eager

variable {St Pub Rand W Ct Leak : Type} [Fintype Rand] [Nonempty Rand]

/-- The query `q` at the game state `s` is the first epoch opened by `A`. -/
def firstOpenA (s : SMSchemeSt St Pub) : SMQuery W → Bool
  | .ratchet .A => s.ck.canSend .A && s.ck.t .A == 0
  | _ => false

/-- The oracle of the multi-challenge game over `M` in which the first epoch opened by `A` runs
on the randomness `r`. -/
noncomputable def smMultiOracleFirstA (M : SMScheme St Pub Rand W Ct Leak) (ΔFS ΔPCS t n : ℕ)
    (mode : ℕ → Bool) (r : Rand) (x : SMSchemeSt St Pub × ℕ) (q : SMQuery W) :
    PMF (SMSchemeAns Pub Ct Leak × (SMSchemeSt St Pub × ℕ)) :=
  if firstOpenA x.1 q then
    PMF.pure (.msg (M.ratchet (x.1.ck.st .A) r).2,
      (⟨x.1.ck.sent .A (M.ratchet (x.1.ck.st .A) r).1 (M.ratchet (x.1.ck.st .A) r).2,
        x.1.done⟩, x.2))
  else smMultiOracle M ΔFS ΔPCS t n mode x q

/-- The epoch counters do not decrease along a call of the multi-challenge oracle. -/
theorem smMultiOracle_t_le (M : SMScheme St Pub Rand W Ct Leak) (ΔFS ΔPCS t n : ℕ)
    (mode : ℕ → Bool) (x : SMSchemeSt St Pub × ℕ) (q : SMQuery W) :
    ∀ y ∈ (smMultiOracle M ΔFS ΔPCS t n mode x q).support, ∀ p, x.1.ck.t p ≤ y.2.1.ck.t p := by
  intro y hy p
  cases q with
  | ratchet p' =>
    simp only [smMultiOracle, smSchemeOracle] at hy
    split_ifs at hy
    · simp only [PMF.support_map, PMF.support_bind, PMF.support_uniformFintype, Set.top_eq_univ,
        Set.mem_univ, PMF.support_pure, Set.iUnion_true, Set.iUnion_singleton_eq_range,
        Set.mem_image, Set.mem_range, exists_exists_eq_and] at hy
      obtain ⟨r, rfl⟩ := hy
      simp only [CKAGameSt.sent, Function.update_apply]
      split_ifs with h
      · subst h; omega
      · exact le_rfl
    · simp only [PMF.support_map, PMF.support_pure, Set.image_singleton, Prod.mk.eta,
        Set.mem_singleton_iff] at hy
      subst hy
      exact le_rfl
  | recv p' =>
    simp only [smMultiOracle, smSchemeOracle] at hy
    grind only [PMF.mem_support_iff, PMF.mem_support_map_iff, PMF.coe_ne_zero, PMF.pure_map,
      PMF.mem_support_pure_iff, CKAGameSt.recvd_t]
  | send p' m =>
    simp only [smMultiOracle, smSchemeOracle] at hy
    aesop
  | chall p' m =>
    simp only [smMultiOracle] at hy
    aesop
  | corrupt p' =>
    simp only [smMultiOracle, smSchemeOracle, PMF.pure_map, PMF.support_pure,
      Set.mem_singleton_iff] at hy
    subst hy
    exact le_rfl

/-- **The first epoch of `A` on randomness drawn in advance.** From a state at which `A` has
opened no epoch, a run against the multi-challenge oracle is the run against the oracle whose
first epoch of `A` runs on a uniform randomness drawn before the run. -/
theorem run_smMultiOracle_eager {α : Type} (M : SMScheme St Pub Rand W Ct Leak)
    (ΔFS ΔPCS t n : ℕ) (mode : ℕ → Bool)
    (A : OracleAdv (SMQuery W) (SMSchemeAns Pub Ct Leak) α) (x : SMSchemeSt St Pub × ℕ)
    (hx : x.1.ck.t .A = 0) :
    OracleAdv.run (smMultiOracle M ΔFS ΔPCS t n mode) A x =
      (PMF.uniformFintype Rand).bind fun r =>
        OracleAdv.run (smMultiOracleFirstA M ΔFS ΔPCS t n mode r) A x := by
  refine OracleAdv.run_eq_bind_run_of_trigger _ _ _ (fun y => y.1.ck.t .A = 0)
    (fun y q => firstOpenA y.1 q = true) (fun _ y => y.1.ck.t .A ≠ 0) ?_ ?_ ?_ ?_ ?_ ?_ A x hx
  · intro y q _ hc
    rcases q with ⟨_ | _⟩ | _ | _ | _ | _
    · have hcs : y.1.ck.canSend .A = true := by
        simp only [firstOpenA, Bool.and_eq_true] at hc
        exact hc.1
      simp only [smMultiOracleFirstA, hc, ite_true, smMultiOracle, smSchemeOracle, hcs,
        PMF.map_bind, PMF.pure_map]
    all_goals simp [firstOpenA] at hc
  · intro r y q _ hc
    simp only [smMultiOracleFirstA, hc, Bool.false_eq_true, ite_false]
  · intro y q _ _ z _
    exact (em _).imp id fun h _ => h
  · intro r y q _ hc z hz
    rcases q with ⟨_ | _⟩ | _ | _ | _ | _
    · simp only [smMultiOracleFirstA, hc, ite_true, PMF.support_pure,
        Set.mem_singleton_iff] at hz
      subst hz
      simp [CKAGameSt.sent]
    all_goals simp [firstOpenA] at hc
  · intro r y q hy z hz
    have := smMultiOracle_t_le M ΔFS ΔPCS t n mode y q z hz .A
    omega
  · intro r y q hy
    have hc : firstOpenA y.1 q = false := by
      cases q with
      | ratchet p => cases p <;> simp [firstOpenA, hy]
      | _ => rfl
    simp only [smMultiOracleFirstA, hc, Bool.false_eq_true, ite_false]

end Eager

/-! ## The Diffie–Hellman CKA from a public value -/

/-- The party states of `dhCKAPre`. -/
inductive DHPreSt (G Sk : Type) where
  /-- The state `(h, y)` of `dhCKAOf`: the peer's last public value and the own secret key. -/
  | std (h : G) (y : Sk)
  /-- The first sender before its first epoch: the public value `h` of the initialisation and
  the secret key `x` of the first epoch, drawn at the initialisation. -/
  | pendA (h : G) (x : Sk)
  /-- The first receiver before its first receive: the message `T` and the key `k` of the first
  epoch. -/
  | pendB (T k : G)
  /-- The first receiver after its first receive and before its first epoch: the received
  message `h`. -/
  | heldB (h : G)

/-- The party state `x` with its CKA state mapped by `f`. -/
def SMPartySt.mapCk {Sc Sc' RK Sa : Type} (f : Sc → Sc') (x : SMPartySt Sc RK Sa) :
    SMPartySt Sc' RK Sa :=
  ⟨f x.ck, x.rk, x.snd, x.rcv⟩

section DHPre

variable {G : Type} [CG : CyclicGroup G] {Sk : Type}

/-- The sending algorithm of `dhCKAPre` with explicit randomness `r`: a party in the state
`pendA h x` sends with the key `x` drawn at the initialisation, every other party with `r`. -/
noncomputable def dhPreSendR (decE : Sk → CG.Exp) : DHPreSt G Sk → Sk → DHPreSt G Sk × G × G
  | .std h _, r => (.std h r, CG.pow (decE r), CyclicGroup.elemPow h (decE r))
  | .pendA h x, _ => (.std h x, CG.pow (decE x), CyclicGroup.elemPow h (decE x))
  | .pendB T _, r => (.std T r, CG.pow (decE r), CyclicGroup.elemPow T (decE r))
  | .heldB h, r => (.std h r, CG.pow (decE r), CyclicGroup.elemPow h (decE r))

/-- The receiving algorithm of `dhCKAPre`: a party in the state `pendB T k` derives the stored
key `k`; a party in the state `std h y` derives `T ^ decE y`. -/
noncomputable def dhPreRecv (decE : Sk → CG.Exp) : DHPreSt G Sk → G → DHPreSt G Sk × G
  | .std _ y, T => (.std T y, CyclicGroup.elemPow T (decE y))
  | .pendA _ x, T => (.std T x, CyclicGroup.elemPow T (decE x))
  | .pendB _ k, T => (.heldB T, k)
  | .heldB h, T => (.heldB T, h)

variable [Fintype Sk] [Nonempty Sk]

/-- **The Diffie–Hellman CKA from the public value `d`.** The initialisation draws the secret
key `x₁` of the first epoch; the first sender holds `d` and `x₁`, the first receiver holds the
message `g ^ decE x₁` and the key `d ^ decE x₁` of the first epoch. Sending draws a key and
runs `dhPreSendR`; receiving runs `dhPreRecv`. -/
noncomputable def dhCKAPre (decE : Sk → CG.Exp) (d : G) : CKADef (DHPreSt G Sk) G G where
  init := SPComp.bind (SPComp.sample Sk) fun x =>
    SPComp.pure (d, .pendA d x, .pendB (CG.pow (decE x)) (CyclicGroup.elemPow d (decE x)))
  send s := SPComp.bind (SPComp.sample Sk) fun r => SPComp.pure (dhPreSendR decE s r)
  recv := dhPreRecv decE

/-- The sending algorithm of `dhCKAPre` with its key as explicit randomness. -/
noncomputable instance dhCKAPreCoins (decE : Sk → CG.Exp) (d : G) :
    CKACoins (dhCKAPre decE d) Sk where
  sendR := dhPreSendR decE

/-- The explicit-randomness sending algorithm of `dhCKAPre` is its sending algorithm. -/
theorem dhCKAPreCoins_sound (decE : Sk → CG.Exp) (d : G) : CKACoins.Sound (dhCKAPre decE d) :=
  fun _ => rfl

variable [Inhabited Sk]

/-- The corruption answer of a state of `dhCKAPre` read as a state of `dhCKAOf`: the public value
and the secret key of `std`, the default key for the other states. -/
def dhPreOpen : DHPreSt G Sk → G × Sk
  | .std h y => (h, y)
  | .pendA h _ => (h, default)
  | .pendB T _ => (T, default)
  | .heldB h => (h, default)

/-- The state of `dhCKAOf` at the signed-prekey pair of the key `x₀` that a state of `dhCKAPre`
stands for: the first receiver holds `x₀` until its first epoch. -/
def dhPreForget (decE : Sk → CG.Exp) (x₀ : Sk) : DHPreSt G Sk → G × Sk
  | .std h y => (h, y)
  | .pendA h _ => (h, default)
  | .pendB _ _ => (CG.pow (decE x₀), x₀)
  | .heldB h => (h, x₀)

end DHPre

section ACDPair

variable {Sc Msg Key RK Sa : Type}

/-- **The keyed initialisation of the ACD construction at the initial pair `i`.** -/
noncomputable def acdIniPair (C : CKADef Sc Msg Key) (i : Msg × Sc × Sc) (rk : RK) :
    SPComp (Msg × SMPartySt Sc RK Sa × SMPartySt Sc RK Sa) :=
  SignalStackSM.acdIni (C.atInit i) rk

end ACDPair

/-! ## The ACD construction along a map of CKA states -/

section ACDMap

variable {Sc Sc' Msg Key Rand RK Sa W Ct : Type} [SampleableType W] [SampleableType Ct]
  [Fintype RK] [Nonempty RK]

/-- The gated party state with its CKA state mapped by `f`. -/
def gateMapCk (f : Sc → Sc') (x : SMPartySt Sc RK Sa × Bool) : SMPartySt Sc' RK Sa × Bool :=
  (x.1.mapCk f, x.2)

theorem gateB_acdSM_send_mapCk (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (C' : CKADef Sc' Msg Key) [CKACoins C' Rand] (R : PRGDef (RK × Key) (RK × Sa))
    (F : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (f : Sc → Sc') (x : SMPartySt Sc RK Sa × Bool)
    (m : W × W) :
    (acdSM C' R F D).gateB.send (gateMapCk f x) m =
      ((acdSM C R F D).gateB.send x m).map fun y => (gateMapCk f y.1, y.2) := by
  obtain ⟨⟨ck, rk, snd, rcv⟩, b⟩ := x
  cases snd <;> rfl

theorem gateB_acdSM_ratchet_mapCk (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (C' : CKADef Sc' Msg Key) [CKACoins C' Rand] (R : PRGDef (RK × Key) (RK × Sa))
    (F : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (f : Sc → Sc') (x : SMPartySt Sc RK Sa × Bool)
    (r : Rand) (r' : Rand)
    (h : CKACoins.sendR (C := C') (f x.1.ck) r' =
      (f (CKACoins.sendR (C := C) x.1.ck r).1, (CKACoins.sendR (C := C) x.1.ck r).2)) :
    (acdSM C' R F D).gateB.ratchet (gateMapCk f x) r' =
      (gateMapCk f ((acdSM C R F D).gateB.ratchet x r).1,
        ((acdSM C R F D).gateB.ratchet x r).2) := by
  simp only [SMScheme.gateB, acdSM, gateMapCk, SMPartySt.mapCk, h]

theorem gateB_acdSM_recv_mapCk (C : CKADef Sc Msg Key) [CKACoins C Rand]
    (C' : CKADef Sc' Msg Key) [CKACoins C' Rand] (R : PRGDef (RK × Key) (RK × Sa))
    (F : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (f : Sc → Sc') (x : SMPartySt Sc RK Sa × Bool)
    (T : Msg) (h : C'.recv (f x.1.ck) T = (f (C.recv x.1.ck T).1, (C.recv x.1.ck T).2)) :
    (acdSM C' R F D).gateB.recv (gateMapCk f x) T =
      gateMapCk f ((acdSM C R F D).gateB.recv x T) := by
  simp only [SMScheme.gateB, acdSM, gateMapCk, SMPartySt.mapCk, h]

end ACDMap

/-! ## The session view at the signed-prekey pair -/

section PairEqPre

variable {G : Type} [CG : CyclicGroup G] {Sk : Type} [Fintype Sk] [Nonempty Sk] [Inhabited Sk]
  {RK Sa W Ct : Type} [SampleableType W] [SampleableType Ct] [Fintype RK] [Nonempty RK]

/-- The sender of epoch `e` is `B` exactly at the even epochs. -/
theorem ckaSender_eq_B_iff (e : ℕ) : ckaSender e = .B ↔ e % 2 = 0 := by
  unfold ckaSender
  split <;> simp_all

/-- The sender of epoch `e` is `A` exactly at the odd epochs. -/
theorem ckaSender_eq_A_iff (e : ℕ) : ckaSender e = .A ↔ e % 2 = 1 := by
  unfold ckaSender
  split <;> simp_all

/-- The invariant of the game over the gated double ratchet of `dhCKAPre decE (g ^ decE x₀)`
with the first key `x₁`: reachable counters; `A` holds `pendA` before its first epoch and a
`std` state after it; `B` holds `pendB` with the message and key of the first epoch before its
first receive, a `heldB` state between its first receive and its first epoch, and a `std` state
after it; the flag of `B` is set only after its first epoch; the message in transit before the
first receive of `B` is the message of the first epoch. -/
structure DHPreInv (decE : Sk → CG.Exp) (x₀ x₁ : Sk)
    (s : SMSchemeSt (SMPartySt (DHPreSt G Sk) RK Sa × Bool) G) : Prop where
  /-- The counters are reachable. -/
  reach : ckaReach s.ck
  /-- `A` before its first epoch. -/
  a0 : s.ck.t .A = 0 → (s.ck.st .A).1.ck = .pendA (CG.pow (decE x₀)) x₁
  /-- `A` after its first epoch. -/
  aS : s.ck.t .A ≠ 0 → ∃ h y, (s.ck.st .A).1.ck = .std h y
  /-- `B` before its first receive. -/
  b0 : s.ck.t .B = 0 → (s.ck.st .B).1.ck =
    .pendB (CG.pow (decE x₁)) (CyclicGroup.elemPow (CG.pow (decE x₀)) (decE x₁))
  /-- `B` between its first receive and its first epoch. -/
  b1 : s.ck.t .B = 1 → ∃ h, (s.ck.st .B).1.ck = .heldB h
  /-- `B` after its first epoch. -/
  bS : 2 ≤ s.ck.t .B → ∃ h y, (s.ck.st .B).1.ck = .std h y
  /-- The flag of `B` is set only after its first epoch. -/
  flag : (s.ck.st .B).2 = true → 2 ≤ s.ck.t .B
  /-- The message in transit before the first receive of `B`. -/
  msg : s.ck.t .B = 0 → s.ck.t .A = 1 → s.ck.msg = CG.pow (decE x₁)

omit [Fintype Sk] [Nonempty Sk] [Inhabited Sk] [Fintype RK] [Nonempty RK] in
/-- The invariant passes to a state with the same counters, message in transit, CKA states and
flags. -/
theorem DHPreInv.congr {decE : Sk → CG.Exp} {x₀ x₁ : Sk}
    {s s' : SMSchemeSt (SMPartySt (DHPreSt G Sk) RK Sa × Bool) G}
    (hs : DHPreInv decE x₀ x₁ s) (ht : s'.ck.t = s.ck.t) (hm : s'.ck.msg = s.ck.msg)
    (hck : ∀ p, (s'.ck.st p).1.ck = (s.ck.st p).1.ck) (hb : ∀ p, (s'.ck.st p).2 = (s.ck.st p).2) :
    DHPreInv decE x₀ x₁ s' := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hs
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [ckaReach, ht, hm, hck, hb] at * <;> assumption

omit [Inhabited Sk] in
/-- The invariant `DHPreInv` is kept by every call of the multi-challenge oracle. -/
theorem dhPreInv_step (decE : Sk → CG.Exp) (R : PRGDef (RK × G) (RK × Sa))
    (F : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (x₀ x₁ : Sk) (ΔFS ΔPCS t n : ℕ)
    (mode : ℕ → Bool)
    (s : SMSchemeSt (SMPartySt (DHPreSt G Sk) RK Sa × Bool) G × ℕ) (q : SMQuery W)
    (hs : DHPreInv decE x₀ x₁ s.1) :
    ∀ y ∈ (smMultiOracle (acdSM (dhCKAPre decE (CG.pow (decE x₀))) R F D).gateB ΔFS ΔPCS t n
      mode s q).support, DHPreInv decE x₀ x₁ y.2.1 := by
  intro y hy
  obtain ⟨s, c⟩ := s
  dsimp only at hs
  have hstd : ∀ c r, ∃ h y, (dhPreSendR decE c r).1 = DHPreSt.std (G := G) h y := by
    intro c r
    cases c <;> exact ⟨_, _, rfl⟩
  have hsend : ∀ (x : SMPartySt (DHPreSt G Sk) RK Sa × Bool) m z,
      (acdSM (dhCKAPre decE (CG.pow (decE x₀))) R F D).gateB.send x m = some z →
      z.1.1.ck = x.1.ck ∧ z.1.2 = x.2 := by
    rintro ⟨⟨ck, rk, snd, rcv⟩, b⟩ m z hz
    cases snd with
    | none => simp [SMScheme.gateB, acdSM] at hz
    | some sa =>
      simp only [SMScheme.gateB, acdSM, Option.map_some, Option.some.injEq] at hz
      subst hz
      exact ⟨rfl, rfl⟩
  have hupd : ∀ p (z : SMPartySt (DHPreSt G Sk) RK Sa × Bool) d,
      z.1.ck = (s.ck.st p).1.ck → z.2 = (s.ck.st p).2 → DHPreInv decE x₀ x₁ (s.upd p z d) := by
    intro p z d h1 h2
    refine hs.congr rfl rfl (fun q => ?_) (fun q => ?_) <;> by_cases hq : q = p <;>
      simp [SMSchemeSt.upd, hq, h1, h2]
  rcases q with ⟨_ | _⟩ | ⟨_ | _⟩ | ⟨p, m⟩ | ⟨p, m⟩ | p
  · simp only [smMultiOracle, smSchemeOracle] at hy
    split_ifs at hy with hc
    · simp only [PMF.support_map, PMF.support_bind, PMF.support_uniformFintype, Set.top_eq_univ,
        Set.mem_univ, PMF.support_pure, Set.iUnion_true, Set.iUnion_singleton_eq_range,
        Set.mem_image, Set.mem_range, exists_exists_eq_and] at hy
      obtain ⟨r, rfl⟩ := hy
      obtain ⟨h, y', hy'⟩ := hstd (s.ck.st .A).1.ck r
      have e1 : ((acdSM (dhCKAPre decE (CG.pow (decE x₀))) R F D).gateB.ratchet
          (s.ck.st .A) r).1.1.ck = (dhPreSendR decE (s.ck.st .A).1.ck r).1 := rfl
      have e2 : ((acdSM (dhCKAPre decE (CG.pow (decE x₀))) R F D).gateB.ratchet
          (s.ck.st .A) r).2 = (dhPreSendR decE (s.ck.st .A).1.ck r).2.1 := rfl
      refine ⟨ckaReach_sent hc _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro h0
        simp [CKAGameSt.sent] at h0
      · intro _
        exact ⟨h, y', by simpa [CKAGameSt.sent, e1] using hy'⟩
      · intro h0
        simpa [CKAGameSt.sent] using hs.b0 (by simpa [CKAGameSt.sent] using h0)
      · intro h0
        simpa [CKAGameSt.sent] using hs.b1 (by simpa [CKAGameSt.sent] using h0)
      · intro h0
        simpa [CKAGameSt.sent] using hs.bS (by simpa [CKAGameSt.sent] using h0)
      · intro hb
        simpa [CKAGameSt.sent] using hs.flag (by simpa [CKAGameSt.sent] using hb)
      · intro _ ha
        have ha0 : s.ck.t .A = 0 := by simpa [CKAGameSt.sent] using ha
        simp only [CKAGameSt.sent, e2, hs.a0 ha0]
        rfl
    · simp only [PMF.support_map, PMF.support_pure, Set.image_singleton,
        Set.mem_singleton_iff] at hy
      subst hy
      exact hs
  · simp only [smMultiOracle, smSchemeOracle] at hy
    split_ifs at hy with hc
    · simp only [PMF.support_map, PMF.support_bind, PMF.support_uniformFintype, Set.top_eq_univ,
        Set.mem_univ, PMF.support_pure, Set.iUnion_true, Set.iUnion_singleton_eq_range,
        Set.mem_image, Set.mem_range, exists_exists_eq_and] at hy
      obtain ⟨r, rfl⟩ := hy
      obtain ⟨h, y', hy'⟩ := hstd (s.ck.st .B).1.ck r
      have e1 : ((acdSM (dhCKAPre decE (CG.pow (decE x₀))) R F D).gateB.ratchet
          (s.ck.st .B) r).1.1.ck = (dhPreSendR decE (s.ck.st .B).1.ck r).1 := rfl
      have hsp := ckaSend_spec hc
      have hodd := (ckaSender_eq_B_iff _).1 hsp.2
      refine ⟨ckaReach_sent hc _ _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro h0
        simpa [CKAGameSt.sent] using hs.a0 (by simpa [CKAGameSt.sent] using h0)
      · intro h0
        simpa [CKAGameSt.sent] using hs.aS (by simpa [CKAGameSt.sent] using h0)
      · intro h0
        simp [CKAGameSt.sent] at h0
      · intro h0
        simp only [CKAGameSt.sent, Function.update_self] at h0
        omega
      · intro _
        exact ⟨h, y', by simpa [CKAGameSt.sent, e1] using hy'⟩
      · intro _
        simp only [CKAGameSt.sent, Function.update_self]
        omega
      · intro h0
        simp [CKAGameSt.sent] at h0
    · simp only [PMF.support_map, PMF.support_pure, Set.image_singleton,
        Set.mem_singleton_iff] at hy
      subst hy
      exact hs
  · simp only [smMultiOracle, smSchemeOracle] at hy
    split_ifs at hy with hc
    · simp only [PMF.support_map, PMF.support_pure, Set.image_singleton,
        Set.mem_singleton_iff] at hy
      subst hy
      obtain ⟨h1, h2⟩ := ckaReach_recv hs.reach hc
      simp only [CKAParty.other_A] at h1 h2
      have he := (ckaSender_eq_B_iff _).1 h2
      obtain ⟨h, y', hck⟩ := hs.aS (by omega)
      have e1 : ((acdSM (dhCKAPre decE (CG.pow (decE x₀))) R F D).gateB.recv (s.ck.st .A)
          s.ck.msg).1.ck = (dhPreRecv decE (s.ck.st .A).1.ck s.ck.msg).1 := rfl
      refine ⟨ckaReach_recvd hc _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro h0
        simp [CKAGameSt.recvd] at h0
      · intro _
        exact ⟨s.ck.msg, y', by simp [CKAGameSt.recvd, e1, hck, dhPreRecv]⟩
      · intro h0
        simpa [CKAGameSt.recvd] using hs.b0 (by simpa [CKAGameSt.recvd] using h0)
      · intro h0
        simpa [CKAGameSt.recvd] using hs.b1 (by simpa [CKAGameSt.recvd] using h0)
      · intro h0
        simpa [CKAGameSt.recvd] using hs.bS (by simpa [CKAGameSt.recvd] using h0)
      · intro hb
        simpa [CKAGameSt.recvd] using hs.flag (by simpa [CKAGameSt.recvd] using hb)
      · intro hb _
        simp only [CKAGameSt.recvd, ne_eq, reduceCtorEq, not_false_eq_true,
          Function.update_of_ne] at hb
        omega
    · simp only [PMF.support_map, PMF.support_pure, Set.image_singleton,
        Set.mem_singleton_iff] at hy
      subst hy
      exact hs
  · simp only [smMultiOracle, smSchemeOracle] at hy
    split_ifs at hy with hc
    · simp only [PMF.support_map, PMF.support_pure, Set.image_singleton,
        Set.mem_singleton_iff] at hy
      subst hy
      obtain ⟨h1, h2⟩ := ckaReach_recv hs.reach hc
      simp only [CKAParty.other_B] at h1 h2
      have ho := (ckaSender_eq_A_iff _).1 h2
      have e1 : ((acdSM (dhCKAPre decE (CG.pow (decE x₀))) R F D).gateB.recv (s.ck.st .B)
          s.ck.msg).1.ck = (dhPreRecv decE (s.ck.st .B).1.ck s.ck.msg).1 := rfl
      refine ⟨ckaReach_recvd hc _, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · intro h0
        simpa [CKAGameSt.recvd] using hs.a0 (by simpa [CKAGameSt.recvd] using h0)
      · intro h0
        simpa [CKAGameSt.recvd] using hs.aS (by simpa [CKAGameSt.recvd] using h0)
      · intro h0
        simp [CKAGameSt.recvd] at h0
      · intro h0
        have hb0 : s.ck.t .B = 0 := by
          simp only [CKAGameSt.recvd, Function.update_self] at h0
          omega
        exact ⟨s.ck.msg, by simp [CKAGameSt.recvd, e1, hs.b0 hb0, dhPreRecv]⟩
      · intro h0
        have hb2 : 2 ≤ s.ck.t .B := by
          simp only [CKAGameSt.recvd, Function.update_self] at h0
          omega
        obtain ⟨h, y', hck⟩ := hs.bS hb2
        exact ⟨s.ck.msg, y', by simp [CKAGameSt.recvd, e1, hck, dhPreRecv]⟩
      · intro hb
        have e2 : ((acdSM (dhCKAPre decE (CG.pow (decE x₀))) R F D).gateB.recv (s.ck.st .B)
            s.ck.msg).2 = (s.ck.st .B).2 := rfl
        have := hs.flag (by simpa [CKAGameSt.recvd, e2] using hb)
        simp only [CKAGameSt.recvd, Function.update_self]
        omega
      · intro h0
        simp [CKAGameSt.recvd] at h0
    · simp only [PMF.support_map, PMF.support_pure, Set.image_singleton,
        Set.mem_singleton_iff] at hy
      subst hy
      exact hs
  · simp only [smMultiOracle, smSchemeOracle] at hy
    grind only [PMF.mem_support_map_iff, PMF.mem_support_iff, PMF.pure_apply_of_ne, PMF.pure_map,
      PMF.mem_support_pure_iff]
  · simp only [smMultiOracle] at hy
    by_cases hc : c < n ∧ ckaSender (s.ck.t p) = p ∧ s.ck.t p = t
    · simp only [ite_eq_left hc] at hy
      cases hz : (acdSM (dhCKAPre decE (CG.pow (decE x₀))) R F D).gateB.send (s.ck.st p) m with
      | none =>
        rw [hz] at hy
        simp only [PMF.support_pure, Set.mem_singleton_iff] at hy
        subst hy
        exact hs
      | some z =>
        rw [hz, PMF.mem_support_bind_iff] at hy
        obtain ⟨_, -, hy⟩ := hy
        rw [PMF.mem_support_pure_iff] at hy
        subst hy
        exact hupd p z.1 s.done (hsend _ _ _ hz).1 (hsend _ _ _ hz).2
    · simp only [ite_eq_right hc, PMF.mem_support_pure_iff] at hy
      subst hy
      exact hs
  · simp only [smMultiOracle, smSchemeOracle, PMF.pure_map, PMF.support_pure,
      Set.mem_singleton_iff] at hy
    subst hy
    exact hs

/-- **A call of the oracle of the efficient form along the forgetful map.** From a state of the
invariant, a call of the multi-challenge oracle over the gated double ratchet of
`dhCKAPre decE (g ^ decE x₀)`, with the answers relabelled by `dhPreOpen` and the states mapped
by `dhPreForget decE x₀`, is the call of the oracle over the gated double ratchet at the
signed-prekey pair whose first epoch of `A` runs on `x₁`. -/
theorem dhPre_oracle_map (decE : Sk → CG.Exp) (R : PRGDef (RK × G) (RK × Sa))
    (F : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) (x₀ x₁ : Sk) (ΔFS ΔPCS t n : ℕ)
    (mode : ℕ → Bool) (s : SMSchemeSt (SMPartySt (DHPreSt G Sk) RK Sa × Bool) G) (c : ℕ)
    (q : SMQuery W) (hs : DHPreInv decE x₀ x₁ s) :
    (smMultiOracle (acdSM (dhCKAPre decE (CG.pow (decE x₀))) R F D).gateB ΔFS ΔPCS t n mode
        (s, c) q).map (fun y =>
          (y.1.map id id (Option.map (SMPartySt.mapCk dhPreOpen)),
            (y.2.1.mapSt (gateMapCk (dhPreForget decE x₀)), y.2.2))) =
      smMultiOracleFirstA (acdSM ((dhCKAOf G decE).atInit (dhPairInit decE x₀)) R F D).gateB
        ΔFS ΔPCS t n mode x₁ (s.mapSt (gateMapCk (dhPreForget decE x₀)), c) q := by
  have hf : firstOpenA (s.mapSt (gateMapCk (dhPreForget decE x₀))) q = firstOpenA s q := by
    rcases q with ⟨_ | _⟩ | _ | _ | _ | _ <;> rfl
  unfold smMultiOracleFirstA
  rw [hf]
  by_cases hq : firstOpenA s q = true
  · simp only [hq, ite_true]
    rcases q with ⟨_ | _⟩ | _ | _ | _ | _
    · have h2 : s.ck.canSend .A = true ∧ s.ck.t .A = 0 := by simpa [firstOpenA] using hq
      have hA := hs.a0 h2.2
      have hr : ∀ r, (acdSM (dhCKAPre decE (CG.pow (decE x₀))) R F D).gateB.ratchet
          (s.ck.st .A) r =
          (acdSM (dhCKAPre decE (CG.pow (decE x₀))) R F D).gateB.ratchet (s.ck.st .A) x₁ := by
        intro r
        simp only [SMScheme.gateB, acdSM, hA]
        rfl
      simp only [smMultiOracle, smSchemeOracle, h2.1, ite_true, hr, PMF.bind_const,
        PMF.pure_map]
      have hk := gateB_acdSM_ratchet_mapCk (dhCKAPre decE (CG.pow (decE x₀)))
        ((dhCKAOf G decE).atInit (dhPairInit decE x₀)) R F D (dhPreForget decE x₀)
        (s.ck.st .A) x₁ x₁ (by rw [hA]; rfl)
      have hst : (s.mapSt (gateMapCk (dhPreForget decE x₀))).ck.st .A =
          gateMapCk (dhPreForget decE x₀) (s.ck.st .A) := rfl
      rw [hst, hk, SMSchemeSt.mapSt_sent]
      rfl
    all_goals simp [firstOpenA] at hq
  · simp only [hq, Bool.false_eq_true, ite_false]
    refine smMultiOracle_mapSt _ _ _ _ ΔFS ΔPCS t n mode s c _ ?_ ?_ ?_ ?_ rfl
    · intro p hqp hc r
      subst hqp
      have hck : (∃ h y, (s.ck.st p).1.ck = .std h y) ∨ ∃ h, (s.ck.st p).1.ck = .heldB h := by
        cases p with
        | A =>
          refine Or.inl (hs.aS fun h0 => ?_)
          simp [firstOpenA, hc, h0] at hq
        | B =>
          have h1 := (ckaSender_eq_B_iff _).1 (ckaSend_spec hc).2
          rcases (by omega : s.ck.t .B = 1 ∨ 2 ≤ s.ck.t .B) with h | h
          · exact Or.inr (hs.b1 h)
          · exact Or.inl (hs.bS h)
      refine gateB_acdSM_ratchet_mapCk _ _ R F D _ _ r r ?_
      rcases hck with ⟨h, y, hc'⟩ | ⟨h, hc'⟩ <;> rw [hc'] <;> rfl
    · intro p hqp hc
      subst hqp
      refine gateB_acdSM_recv_mapCk _ _ R F D _ _ _ ?_
      obtain ⟨h1, h2⟩ := ckaReach_recv hs.reach hc
      cases p with
      | A =>
        simp only [CKAParty.other_A] at h1 h2
        have he := (ckaSender_eq_B_iff _).1 h2
        obtain ⟨h, y, hc'⟩ := hs.aS (by omega)
        rw [hc']
        rfl
      | B =>
        simp only [CKAParty.other_B] at h1 h2
        have ho := (ckaSender_eq_A_iff _).1 h2
        rcases Nat.eq_zero_or_pos (s.ck.t .B) with h0 | hpos
        · rw [hs.b0 h0, hs.msg h0 (by omega)]
          exact Prod.ext rfl (elemPow_pow_comm _ _)
        · obtain ⟨h, y, hc'⟩ := hs.bS (by omega)
          rw [hc']
          rfl
    · exact gateB_acdSM_send_mapCk _ _ R F D _
    · intro p
      have hck : (s.ck.st p).2 = true →
          dhPreForget decE x₀ (s.ck.st p).1.ck = dhPreOpen (s.ck.st p).1.ck := by
        intro hb
        cases p with
        | A =>
          by_cases h0 : s.ck.t .A = 0
          · rw [hs.a0 h0]; rfl
          · obtain ⟨h, y, hc'⟩ := hs.aS h0
            rw [hc']; rfl
        | B =>
          obtain ⟨h, y, hc'⟩ := hs.bS (hs.flag hb)
          rw [hc']; rfl
      simp only [SMScheme.gateB, gateMapCk]
      cases hb : (s.ck.st p).2
      · rfl
      · simp only [ite_true, Option.map_some]
        simp only [acdSM, id, SMPartySt.mapCk, hck hb]

/-- **The gated session view at the signed-prekey pair is the gated session view of the
efficient form.** For the signed-prekey pair `dhPairInit decE x₀`, the session view of the gated
double ratchet of `(dhCKAOf G decE).atInit (dhPairInit decE x₀)` under the schedule `Sch` equals
the session view of the gated double ratchet of `dhCKAPre decE (g ^ decE x₀)` under `Sch` with
the corruption answers read through `dhPreOpen`. -/
theorem smSessView_pair_eq_pre (decE : Sk → CG.Exp) (R : PRGDef (RK × G) (RK × Sa))
    (F : PRGDef Sa (W × Sa)) (D : AEADDef W Ct) {V : Type}
    (Sch : G → OracleAdv (SMQuery W) (SMSchemeAns G Ct (Option (SMPartySt (G × Sk) RK Sa))) V)
    (t n ΔFS ΔPCS : ℕ) (mode : ℕ → Bool) (x₀ : Sk) (k : RK) :
    smSessView (acdSM ((dhCKAOf G decE).atInit (dhPairInit decE x₀)) R F D).gateB
        (gateIni (acdIniPair (Sa := Sa) (dhCKAOf G decE) (dhPairInit decE x₀)))
        Sch t n ΔFS ΔPCS mode k =
      smSessView (acdSM (dhCKAPre decE (CG.pow (decE x₀))) R F D).gateB
        (gateIni (acdIni (Sa := Sa) (dhCKAPre decE (CG.pow (decE x₀)))))
        (fun T => (Sch T).mapQueryAnswer id
          (SMSchemeAns.map id id (Option.map (SMPartySt.mapCk dhPreOpen))))
        t n ΔFS ΔPCS mode k := by
  have hL : acdIniPair (Sa := Sa) (dhCKAOf G decE) (dhPairInit decE x₀) k =
      SPComp.pure (CG.pow (decE x₀), (⟨(CG.pow (decE x₀), default), k, none, none⟩ :
        SMPartySt (G × Sk) RK Sa), ⟨(CG.pow (decE x₀), x₀), k, none, none⟩) := by
    simp only [acdIniPair, acdIni, CKADef.atInit, SPComp.pure_bind]
    rfl
  have hR : acdIni (Sa := Sa) (dhCKAPre decE (CG.pow (decE x₀))) k =
      SPComp.bind (SPComp.sample Sk) fun x => SPComp.pure (CG.pow (decE x₀),
        (⟨.pendA (CG.pow (decE x₀)) x, k, none, none⟩ : SMPartySt (DHPreSt G Sk) RK Sa),
        ⟨.pendB (CG.pow (decE x)) (CyclicGroup.elemPow (CG.pow (decE x₀)) (decE x)), k, none,
          none⟩) := by
    simp only [acdIni, dhCKAPre, SPComp.bind_assoc, SPComp.pure_bind]
  simp only [smSessView, gateIni, hL, hR, SPComp.bind_assoc, SPComp.pure_bind]
  rw [sample_eq_liftPMF, liftPMF_bind_liftPMF]
  congr 1
  rw [run_smMultiOracle_eager _ _ _ _ _ _ _ _ rfl, PMF.map_bind]
  refine congrArg _ (funext fun x₁ => ?_)
  have hinit : SMSchemeSt.init (gateInit (CG.pow (decE x₀),
        (⟨(CG.pow (decE x₀), default), k, none, none⟩ : SMPartySt (G × Sk) RK Sa),
        (⟨(CG.pow (decE x₀), x₀), k, none, none⟩ : SMPartySt (G × Sk) RK Sa))) =
      (SMSchemeSt.init (gateInit (CG.pow (decE x₀),
        (⟨.pendA (CG.pow (decE x₀)) x₁, k, none, none⟩ : SMPartySt (DHPreSt G Sk) RK Sa),
        (⟨.pendB (CG.pow (decE x₁)) (CyclicGroup.elemPow (CG.pow (decE x₀)) (decE x₁)), k, none,
          none⟩ : SMPartySt (DHPreSt G Sk) RK Sa)))).mapSt (gateMapCk (dhPreForget decE x₀)) := by
    simp only [SMSchemeSt.init, SMSchemeSt.mapSt, CKAGameSt.init, SMSchemeSt.mk.injEq, and_true]
    congr 1
    funext p
    cases p <;> rfl
  have hinv : DHPreInv decE x₀ x₁ (SMSchemeSt.init (gateInit (CG.pow (decE x₀),
        (⟨.pendA (CG.pow (decE x₀)) x₁, k, none, none⟩ : SMPartySt (DHPreSt G Sk) RK Sa),
        (⟨.pendB (CG.pow (decE x₁)) (CyclicGroup.elemPow (CG.pow (decE x₀)) (decE x₁)), k, none,
          none⟩ : SMPartySt (DHPreSt G Sk) RK Sa)))) := by
    refine ⟨ckaReach_init _ _ _, fun _ => rfl, fun h => absurd rfl h, fun _ => rfl, ?_, ?_, ?_,
      ?_⟩ <;> intros <;> simp_all [SMSchemeSt.init, CKAGameSt.init, gateInit]
  rw [hinit]
  exact OracleAdv.run_map_fst_mapQueryAnswer_of_map_state_inv _ _ _
    (fun y => (y.1.mapSt (gateMapCk (dhPreForget decE x₀)), y.2))
    (fun y => DHPreInv decE x₀ x₁ y.1)
    (fun s d hs y hy => dhPreInv_step decE R F D x₀ x₁ ΔFS ΔPCS t n mode s d hs y hy)
    (fun s d hs => dhPre_oracle_map decE R F D x₀ x₁ ΔFS ΔPCS t n mode s.1 s.2 d hs)
    _ (_, 0) hinv

end PairEqPre

end CatCrypt.Crypto.Messaging
