/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Assumptions.AEAD
public import CatCryptCore.Crypto.Assumptions.OWF
public import CatCryptCore.Crypto.OracleSimulation
public import CatCryptCore.Crypto.OracleAdversaryStateMap
public import CatCryptCore.Crypto.AKE.TLSSquare
public import CatCryptCore.ForMathlib.PMFUniform
public import CatCryptCore.Tactics.TimeCertTry
import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DeriveReduction.Basic
public import CatCryptCore.Tactics.DeriveTimeBound.Basic

/-!
# The TLS 1.3 record layer as a view of the session key

The record layer of TLS 1.3 (RFC 8446 §5) protects the application data of a session under the
traffic keys of its two directions. This module states the record layer as a view of the session
key `TKey Sec` of the TLS square (`TLSSquare.lean`), the quadruple of the client and server
application traffic secrets, the exporter secret and the resumption secret, and bounds the
distance between the real view and an ideal view by a pseudorandom-generator advantage and two
authenticated-encryption advantages.

**The schedule.** A record schedule `Sch : OracleAdv (RecQ Pt Ct) (RecA Pt Ct) V` asks to
protect a plaintext in a direction (`RecQ.send`) and to deliver a ciphertext to the reader of a
direction (`RecQ.recv`), and returns a view in `V`. Each direction keeps a write sequence number
and a read sequence number.

**The real view.** `recRealView D tk nce hd L Sch k` derives the write key and IV of each
direction from the client and server application traffic secrets of `k` (`tk`, RFC 8446 §7.3);
the record of sequence number `i` of a direction is sealed and opened by the AEAD scheme `D` at
the nonce `nce iv i` and the header `hd`, which form the associated data `N × Hd` of the
deterministic authenticated-encryption game. Sequence numbers from `L` on are refused (rekey or
close, RFC 8446 §5.3). A reader advances its sequence number on a record it accepts.

**The ideal view.** `recIdealView L Sch` answers every protection query with a uniform
ciphertext and a reader accepts exactly the ciphertext sent at its position.

**The bound.** For a nonce function injective below `L`, the advantage of a distinguisher between
the real view under a uniform session key and the ideal view is at most the PRG advantage of the
traffic-key derivation `tkPRG tk` against `recPrgRed`, plus the authenticated-encryption
advantages (`AEAD_CCA_Advantage`) of `D` against `recAeadRed … .c2s` and `recAeadRed … .s2c`
(`advantageA_rec_le`). The hops: the traffic keys become uniform (PRG); the client-to-server
direction is answered by the ideal oracles of the AEAD game, whose answers at distinct nonces
are the ideal direction (`dirIdeal_map`); then the server-to-client direction.

## Main definitions

* `Dir`, `RecQ`, `RecA`: directions, queries and answers of a record schedule.
* `recRealView`, `recIdealView`: the real and the ideal view.
* `tkPRG`: the traffic-key derivation of both directions as a generator.
* `recPrgRed`, `recAeadRed`: the reductions to the PRG game and to the AEAD game.
* `recBound`: the bound.

## Main results

* `recViews_pureNF`: both views neither touch the heap nor fail.
* `advantageA_rec_le`: the record hop.

## References

* RFC 8446, *The Transport Layer Security (TLS) Protocol Version 1.3*, §5 and §7.3.
* P. Rogaway, T. Shrimpton, *A provable-security treatment of the key-wrap problem*,
  EUROCRYPT 2006.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.AKE.RecordView

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Assumptions
open CatCrypt.Crypto.PAKE.CPaceSquare (PureNF)
open CatCrypt.Crypto.AKE.TLSSquare (TKey)
open scoped ENNReal

/-! ## Queries of a record schedule -/

/-- The two directions of a TLS connection: client to server and server to client. -/
inductive Dir where
  | c2s
  | s2c
  deriving DecidableEq

/-- Queries of a record schedule: protect `pt` in direction `d`; deliver `ct` to the reader of
direction `d`. -/
inductive RecQ (Pt Ct : Type) where
  | send (d : Dir) (pt : Pt)
  | recv (d : Dir) (ct : Ct)

/-- Answers of a record schedule: a ciphertext, or the plaintext option of a delivery (`none`
for a rejected record and for a refused query). -/
inductive RecA (Pt Ct : Type) where
  | ct (c : Ct)
  | pt (o : Option Pt)

variable {Pt Ct : Type}

/-- The direction of a query. -/
def RecQ.dir : RecQ Pt Ct → Dir
  | .send d _ => d
  | .recv d _ => d

/-- The body of a query: the plaintext of a protection query, the ciphertext of a delivery. -/
def RecQ.body : RecQ Pt Ct → Pt ⊕ Ct
  | .send _ pt => .inl pt
  | .recv _ ct => .inr ct

/-- The oracle of a record schedule from one oracle per direction: a query is answered by the
oracle of its direction on its body. -/
noncomputable def recOracle {Sc Ss : Type} (Oc : Sc → Pt ⊕ Ct → PMF (RecA Pt Ct × Sc))
    (Os : Ss → Pt ⊕ Ct → PMF (RecA Pt Ct × Ss)) (s : Sc × Ss) (q : RecQ Pt Ct) :
    PMF (RecA Pt Ct × (Sc × Ss)) :=
  match q.dir with
  | .c2s => (Oc s.1 q.body).map fun x => (x.1, (x.2, s.2))
  | .s2c => (Os s.2 q.body).map fun x => (x.1, (s.1, x.2))

/-! ## One direction -/

section Direction

variable {N Hd : Type}

/-- The answer to a sealing query at the sequence numbers `s`. -/
def sealAns (s : ℕ × ℕ) : AEAD_CCA_Answer Pt Ct → RecA Pt Ct × (ℕ × ℕ)
  | .inl c => (.ct c, (s.1 + 1, s.2))
  | .inr _ => (.pt none, s)

/-- The answer to an opening query at the sequence numbers `s`: the reader advances on a record
it accepts. -/
def openAns (s : ℕ × ℕ) : AEAD_CCA_Answer Pt Ct → RecA Pt Ct × (ℕ × ℕ)
  | .inr o => (.pt o, (s.1, if o.isSome then s.2 + 1 else s.2))
  | .inl _ => (.pt none, s)

/-- One direction over the queries of the AEAD game, at the IV `iv` and the write and read
sequence numbers `s`: the record of sequence number `i < L` is sealed and opened at the
associated data `(nce iv i, hd)`; sequence numbers from `L` on are refused. -/
def dirProg (nce : N → ℕ → N) (hd : Hd) (L : ℕ) (iv : N) (s : ℕ × ℕ) :
    Pt ⊕ Ct → OracleAdv (AEAD_CCA_Query Pt Ct (N × Hd)) (AEAD_CCA_Answer Pt Ct)
      (RecA Pt Ct × (ℕ × ℕ))
  | .inl pt =>
    if s.1 < L then .query (.inl (pt, (nce iv s.1, hd))) fun r => .ret (sealAns s r)
    else .ret (.pt none, s)
  | .inr ct =>
    if s.2 < L then .query (.inr (ct, (nce iv s.2, hd))) fun r => .ret (openAns s r)
    else .ret (.pt none, s)

variable [SampleableType Pt] {Kt : Type}

/-- The real direction under the write key and IV `kiv`. -/
noncomputable def dirReal (D : AEADDef Pt Ct (N × Hd) Kt) (nce : N → ℕ → N) (hd : Hd) (L : ℕ)
    (kiv : Kt × N) :
    (ℕ × ℕ) × Unit → Pt ⊕ Ct → PMF (RecA Pt Ct × ((ℕ × ℕ) × Unit)) :=
  OracleAdv.simOracle (dirProg nce hd L kiv.2) (aeadRealOracle D kiv.1)

/-- The plaintext of the ciphertext `ct` sent at the position `j`, in a log of sent records
`((position, plaintext), ciphertext)`. -/
def idealOpen [DecidableEq Ct] (log : List ((ℕ × Pt) × Ct)) (j : ℕ) (ct : Ct) : Option Pt :=
  (log.find? fun e => decide (e.2 = ct ∧ e.1.1 = j)).map fun e => e.1.2

/-- The ideal direction: a protection query at a position below `L` is answered by a uniform
ciphertext, recorded in the log; a reader at a position below `L` accepts exactly a ciphertext
sent at its position. -/
noncomputable def dirIdeal [SampleableType Ct] (L : ℕ) (s : (ℕ × ℕ) × List ((ℕ × Pt) × Ct)) :
    Pt ⊕ Ct → PMF (RecA Pt Ct × ((ℕ × ℕ) × List ((ℕ × Pt) × Ct)))
  | .inl pt =>
    if s.1.1 < L then
      (PMF.uniformFintype Ct).map fun c => (.ct c, ((s.1.1 + 1, s.1.2), ((s.1.1, pt), c) :: s.2))
    else PMF.pure (.pt none, s)
  | .inr ct =>
    if s.1.2 < L then
      PMF.pure (.pt (idealOpen s.2 s.1.2 ct),
        ((s.1.1, if (idealOpen s.2 s.1.2 ct).isSome then s.1.2 + 1 else s.1.2), s.2))
    else PMF.pure (.pt none, s)

end Direction

/-! ## The views -/

section Views

variable {Pt Ct N Hd Kt Sec V : Type} [SampleableType Pt] [SampleableType Ct] [SampleableType N]
  [SampleableType Kt] [Fintype Sec] [Nonempty Sec] [DecidableEq Hd]

/-- The view of the schedule `Sch` under the write keys and IVs `kk` of both directions. -/
noncomputable def recViewAt (D : AEADDef Pt Ct (N × Hd) Kt) (nce : N → ℕ → N) (hd : Hd)
    (L : ℕ) (Sch : OracleAdv (RecQ Pt Ct) (RecA Pt Ct) V) (kk : (Kt × N) × (Kt × N)) : PMF V :=
  (OracleAdv.run (recOracle (dirReal D nce hd L kk.1) (dirReal D nce hd L kk.2)) Sch
    (((0, 0), ()), ((0, 0), ()))).map Prod.fst

/-- The key schedule of the record keys of both directions as a generator: the write key and IV
of each direction from its application traffic secret. -/
def tkPRG (tk : Sec → Kt × N) : PRGDef (Sec × Sec) ((Kt × N) × (Kt × N)) :=
  ⟨fun p => (tk p.1, tk p.2)⟩

/-- **The real view** of the schedule `Sch` at the session key `(cats, sats, ems, rms)`: the write
keys and IVs `tk cats`, `tk sats`; the record of sequence number `i` of a direction is sealed and
opened at the nonce `nce iv i` and the header `hd`; sequence numbers from `L` on are refused
(rekey or close, RFC 8446 §5.3). -/
noncomputable def recRealView (D : AEADDef Pt Ct (N × Hd) Kt) (tk : Sec → Kt × N)
    (nce : N → ℕ → N) (hd : Hd) (L : ℕ) (Sch : OracleAdv (RecQ Pt Ct) (RecA Pt Ct) V)
    (k : TKey Sec) : SPComp V :=
  liftPMF (recViewAt D nce hd L Sch ((tkPRG tk).stretch (k.1, k.2.1)))

/-- **The ideal view**: uniform ciphertexts; a reader accepts exactly the ciphertext sent at its
position. -/
noncomputable def recIdealView (L : ℕ) (Sch : OracleAdv (RecQ Pt Ct) (RecA Pt Ct) V) :
    SPComp V :=
  liftPMF ((OracleAdv.run (recOracle (dirIdeal L) (dirIdeal L)) Sch
    (((0, 0), []), ((0, 0), []))).map Prod.fst)

omit [SampleableType N] [SampleableType Kt] [Fintype Sec] [Nonempty Sec] [DecidableEq Hd] in
/-- Both views neither touch the heap nor fail. -/
theorem recViews_pureNF (D : AEADDef Pt Ct (N × Hd) Kt) (tk : Sec → Kt × N)
    (nce : N → ℕ → N) (hd : Hd) (L : ℕ) (Sch : OracleAdv (RecQ Pt Ct) (RecA Pt Ct) V) :
    (∀ k, PureNF (recRealView D tk nce hd L Sch k)) ∧
      PureNF (recIdealView (Pt := Pt) (Ct := Ct) L Sch) :=
  ⟨fun _ => ⟨liftPMF_isPure _, liftPMF_noFail _⟩, ⟨liftPMF_isPure _, liftPMF_noFail _⟩⟩

end Views

/-! ## The reductions -/

section Reductions

variable {Pt Ct N Hd Kt V : Type} [SampleableType Pt] [SampleableType Ct] [SampleableType N]
  [SampleableType Kt] [DecidableEq Hd]

/-- The simulator program that forwards the client-to-server direction through `P` and answers
the server-to-client direction by the oracle `O`. -/
def fwdC {Q R Sc Ss : Type} (P : Sc → Pt ⊕ Ct → OracleAdv Q R (RecA Pt Ct × Sc))
    (O : Ss → Pt ⊕ Ct → PMF (RecA Pt Ct × Ss)) (s : Sc × Ss) (q : RecQ Pt Ct) :
    OracleAdv Q R (RecA Pt Ct × (Sc × Ss)) :=
  match q.dir with
  | .c2s => (P s.1 q.body).bind fun x => .ret (x.1, (x.2, s.2))
  | .s2c => .rand (O s.2 q.body) fun x => .ret (x.1, (s.1, x.2))

/-- The simulator program that answers the client-to-server direction by the oracle `O` and
forwards the server-to-client direction through `P`. -/
def fwdS {Q R Sc Ss : Type} (O : Sc → Pt ⊕ Ct → PMF (RecA Pt Ct × Sc))
    (P : Ss → Pt ⊕ Ct → OracleAdv Q R (RecA Pt Ct × Ss)) (s : Sc × Ss) (q : RecQ Pt Ct) :
    OracleAdv Q R (RecA Pt Ct × (Sc × Ss)) :=
  match q.dir with
  | .c2s => .rand (O s.1 q.body) fun x => .ret (x.1, (x.2, s.2))
  | .s2c => (P s.2 q.body).bind fun x => .ret (x.1, (s.1, x.2))

/-- **The reduction to the PRG game**: the output bit of `Adist` on the view of the schedule
under the given write keys and IVs. -/
noncomputable def recPrgRed (D : AEADDef Pt Ct (N × Hd) Kt) (nce : N → ℕ → N) (hd : Hd)
    (L : ℕ) (Sch : OracleAdv (RecQ Pt Ct) (RecA Pt Ct) V) (Adist : V → SPComp Bool) :
    PRG_Adversary ((Kt × N) × (Kt × N)) :=
  fun kk => SPComp.bind (liftPMF (recViewAt D nce hd L Sch kk)) Adist

/-- **The reduction to the AEAD game** in the direction `d`. For `.c2s`: a uniform IV of the
client-to-server direction and a uniform key and IV of the server-to-client direction, the
client-to-server records sealed and opened by the challenger, the server-to-client records by
the real direction. For `.s2c`: a uniform IV of the server-to-client direction, the
client-to-server direction ideal, the server-to-client records sealed and opened by the
challenger. The output is the bit of `Adist` on the view. -/
noncomputable def recAeadRed (D : AEADDef Pt Ct (N × Hd) Kt) (nce : N → ℕ → N) (hd : Hd)
    (L : ℕ) (Sch : OracleAdv (RecQ Pt Ct) (RecA Pt Ct) V) (d : Dir) (Adist : V → SPComp Bool) :
    AEAD_CCA_Adversary Pt Ct (N × Hd) :=
  match d with
  | .c2s =>
    .rand (PMF.uniformFintype N) fun ivc => .rand (PMF.uniformFintype (Kt × N)) fun ks =>
      (OracleAdv.simulate (fwdC (dirProg nce hd L ivc) (dirReal D nce hd L ks)) Sch
        ((0, 0), ((0, 0), ()))).bind fun x => .rand (outBool Adist x.1) .ret
  | .s2c =>
    .rand (PMF.uniformFintype N) fun ivs =>
      (OracleAdv.simulate (fwdS (dirIdeal L) (dirProg nce hd L ivs)) Sch
        (((0, 0), []), (0, 0))).bind fun x => .rand (outBool Adist x.1) .ret

/-- **The bound of the record hop**: the PRG advantage of the traffic-key derivation and the
AEAD advantage of each direction. -/
noncomputable def recBound {Sec : Type} [Fintype Sec] [Nonempty Sec]
    (D : AEADDef Pt Ct (N × Hd) Kt) (tk : Sec → Kt × N) (nce : N → ℕ → N) (hd : Hd) (L : ℕ)
    (Sch : OracleAdv (RecQ Pt Ct) (RecA Pt Ct) V) (Adist : V → SPComp Bool) : ℝ≥0∞ :=
  PRG_Advantage (tkPRG tk) (recPrgRed D nce hd L Sch Adist) +
    AEAD_CCA_Advantage D (recAeadRed D nce hd L Sch .c2s Adist) +
    AEAD_CCA_Advantage D (recAeadRed D nce hd L Sch .s2c Adist)

end Reductions

/-! ## Distributions -/

section Lemmas

/-- A uniform sample of a product is a uniform sample of each component. -/
theorem uniform_prod_bind {A B β : Type} [Fintype A] [Nonempty A] [Fintype B] [Nonempty B]
    (F : A × B → PMF β) :
    (PMF.uniformFintype (A × B)).bind F =
      (PMF.uniformFintype A).bind fun a => (PMF.uniformFintype B).bind fun b => F (a, b) := by
  rw [PMF.uniform_prod_eq_bind, PMF.bind_bind]
  simp only [PMF.bind_map]
  rfl

/-- The output bit of a lifted distribution followed by a distinguisher. -/
theorem outBool_liftPMF_bind {α β : Type} (p : α → PMF β) (A : β → SPComp Bool) (a : α) :
    outBool (fun a => SPComp.bind (liftPMF (p a)) A) a = (p a).bind (outBool A) := by
  simp only [outBool, liftPMF_bind_apply, PMF.map_bind]
  rfl

/-- The run of a simulated adversary followed by a coin of its output is the run of the
adversary against the composite oracle followed by that coin. -/
theorem run_simulate_rand_fst {D R D' R' S U α : Type}
    (impl : S → D → OracleAdv D' R' (R × S)) (O' : U → D' → PMF (R' × U))
    (A : OracleAdv D R α) (p : α → PMF Bool) (s : S) (u : U) :
    (OracleAdv.run O' ((OracleAdv.simulate impl A s).bind fun x => .rand (p x.1) .ret) u).map
        Prod.fst =
      (OracleAdv.run (OracleAdv.simOracle impl O') A (s, u)).bind fun x => p x.1 := by
  rw [OracleAdv.run_bind, OracleAdv.run_simulate]
  simp [PMF.map_bind, PMF.bind_map, Function.comp_def, PMF.pure_map]

/-- A state map does not change a continuation on the output. -/
theorem map_state_bind_fst {α S S' β : Type} (r : PMF (α × S)) (f : S → S')
    (k : α → PMF β) : (r.map (Prod.map id f)).bind (fun x => k x.1) = r.bind fun x => k x.1 := by
  simp [PMF.bind_map, Function.comp_def]

end Lemmas

/-! ## State maps of the simulators -/

section Hops

variable {Pt Ct N Hd : Type}

/-- The composite oracle of `fwdC P O` against `O'` is the record oracle of `P` against `O'` and
of `O`, up to the order of the states. -/
theorem simOracle_fwdC {Q R Sc Ss U : Type} (P : Sc → Pt ⊕ Ct → OracleAdv Q R (RecA Pt Ct × Sc))
    (O : Ss → Pt ⊕ Ct → PMF (RecA Pt Ct × Ss)) (O' : U → Q → PMF (R × U))
    (s : (Sc × Ss) × U) (q : RecQ Pt Ct) :
    (OracleAdv.simOracle (fwdC P O) O' s q).map (Prod.map id fun t => ((t.1.1, t.2), t.1.2)) =
      recOracle (OracleAdv.simOracle P O') O ((s.1.1, s.2), s.1.2) q := by
  rcases q with ⟨d, x⟩ | ⟨d, x⟩ <;> cases d <;>
    simp [fwdC, recOracle, RecQ.dir, RecQ.body, OracleAdv.simOracle, OracleAdv.run_bind,
      PMF.map_bind, Function.comp_def, PMF.pure_map, PMF.map_comp] <;> rfl

/-- The composite oracle of `fwdS O P` against `O'` is the record oracle of `O` and of `P`
against `O'`, up to the order of the states. -/
theorem simOracle_fwdS {Q R Sc Ss U : Type} (O : Sc → Pt ⊕ Ct → PMF (RecA Pt Ct × Sc))
    (P : Ss → Pt ⊕ Ct → OracleAdv Q R (RecA Pt Ct × Ss)) (O' : U → Q → PMF (R × U))
    (s : (Sc × Ss) × U) (q : RecQ Pt Ct) :
    (OracleAdv.simOracle (fwdS O P) O' s q).map (Prod.map id fun t => (t.1.1, (t.1.2, t.2))) =
      recOracle O (OracleAdv.simOracle P O') (s.1.1, (s.1.2, s.2)) q := by
  rcases q with ⟨d, x⟩ | ⟨d, x⟩ <;> cases d <;>
    simp [fwdS, recOracle, RecQ.dir, RecQ.body, OracleAdv.simOracle, OracleAdv.run_bind,
      PMF.map_bind, Function.comp_def, PMF.pure_map, PMF.map_comp] <;> rfl

/-- A run of the simulator `fwdC P O` against `O'`, followed by a coin of the view. -/
theorem run_fwdC {Q R Sc Ss U α : Type} (P : Sc → Pt ⊕ Ct → OracleAdv Q R (RecA Pt Ct × Sc))
    (O : Ss → Pt ⊕ Ct → PMF (RecA Pt Ct × Ss)) (O' : U → Q → PMF (R × U))
    (A : OracleAdv (RecQ Pt Ct) (RecA Pt Ct) α) (p : α → PMF Bool) (sc : Sc) (ss : Ss) (u : U) :
    (OracleAdv.run O' ((OracleAdv.simulate (fwdC P O) A (sc, ss)).bind
        fun x => .rand (p x.1) .ret) u).map Prod.fst =
      (OracleAdv.run (recOracle (OracleAdv.simOracle P O') O) A ((sc, u), ss)).bind
        fun x => p x.1 := by
  rw [run_simulate_rand_fst, ← map_state_bind_fst _ (fun t => ((t.1.1, t.2), t.1.2)),
    OracleAdv.run_map_state _ _ _ (simOracle_fwdC P O O')]

/-- A run of the simulator `fwdS O P` against `O'`, followed by a coin of the view. -/
theorem run_fwdS {Q R Sc Ss U α : Type} (O : Sc → Pt ⊕ Ct → PMF (RecA Pt Ct × Sc))
    (P : Ss → Pt ⊕ Ct → OracleAdv Q R (RecA Pt Ct × Ss)) (O' : U → Q → PMF (R × U))
    (A : OracleAdv (RecQ Pt Ct) (RecA Pt Ct) α) (p : α → PMF Bool) (sc : Sc) (ss : Ss) (u : U) :
    (OracleAdv.run O' ((OracleAdv.simulate (fwdS O P) A (sc, ss)).bind
        fun x => .rand (p x.1) .ret) u).map Prod.fst =
      (OracleAdv.run (recOracle O (OracleAdv.simOracle P O')) A (sc, (ss, u))).bind
        fun x => p x.1 := by
  rw [run_simulate_rand_fst, ← map_state_bind_fst _ (fun t => (t.1.1, (t.1.2, t.2))),
    OracleAdv.run_map_state _ _ _ (simOracle_fwdS O P O')]

/-- A state map of the client-to-server oracle under an invariant is a state map of the record
oracle. -/
theorem recOracle_map_c {Sc Sc' Ss : Type} (Oc : Sc → Pt ⊕ Ct → PMF (RecA Pt Ct × Sc))
    (Oc' : Sc' → Pt ⊕ Ct → PMF (RecA Pt Ct × Sc')) (Os : Ss → Pt ⊕ Ct → PMF (RecA Pt Ct × Ss))
    (f : Sc → Sc') (I : Sc → Prop)
    (h : ∀ s x, I s → (Oc s x).map (Prod.map id f) = Oc' (f s) x)
    (s : Sc × Ss) (q : RecQ Pt Ct) (hs : I s.1) :
    (recOracle Oc Os s q).map (Prod.map id (Prod.map f id)) =
      recOracle Oc' Os (f s.1, s.2) q := by
  rcases q with ⟨d, x⟩ | ⟨d, x⟩ <;> cases d <;>
    simp [recOracle, RecQ.dir, RecQ.body, ← h _ _ hs, PMF.map_comp, Function.comp_def]

/-- A state map of the server-to-client oracle under an invariant is a state map of the record
oracle. -/
theorem recOracle_map_s {Sc Ss Ss' : Type} (Oc : Sc → Pt ⊕ Ct → PMF (RecA Pt Ct × Sc))
    (Os : Ss → Pt ⊕ Ct → PMF (RecA Pt Ct × Ss)) (Os' : Ss' → Pt ⊕ Ct → PMF (RecA Pt Ct × Ss'))
    (f : Ss → Ss') (I : Ss → Prop)
    (h : ∀ s x, I s → (Os s x).map (Prod.map id f) = Os' (f s) x)
    (s : Sc × Ss) (q : RecQ Pt Ct) (hs : I s.2) :
    (recOracle Oc Os s q).map (Prod.map id (Prod.map id f)) =
      recOracle Oc Os' (s.1, f s.2) q := by
  rcases q with ⟨d, x⟩ | ⟨d, x⟩ <;> cases d <;>
    simp [recOracle, RecQ.dir, RecQ.body, ← h _ _ hs, PMF.map_comp, Function.comp_def]

/-- An invariant of the client-to-server oracle is an invariant of the record oracle. -/
theorem recOracle_inv_c {Sc Ss : Type} (Oc : Sc → Pt ⊕ Ct → PMF (RecA Pt Ct × Sc))
    (Os : Ss → Pt ⊕ Ct → PMF (RecA Pt Ct × Ss)) (I : Sc → Prop)
    (h : ∀ s x, I s → ∀ y ∈ (Oc s x).support, I y.2)
    (s : Sc × Ss) (q : RecQ Pt Ct) (hs : I s.1) :
    ∀ y ∈ (recOracle Oc Os s q).support, I y.2.1 := by
  rcases q with ⟨d, x⟩ | ⟨d, x⟩ <;> cases d <;>
    simp only [recOracle, RecQ.dir, RecQ.body, PMF.support_map, Set.mem_image] <;>
    rintro _ ⟨y, hy, rfl⟩ <;> first | exact h _ _ hs y hy | exact hs

/-- An invariant of the server-to-client oracle is an invariant of the record oracle. -/
theorem recOracle_inv_s {Sc Ss : Type} (Oc : Sc → Pt ⊕ Ct → PMF (RecA Pt Ct × Sc))
    (Os : Ss → Pt ⊕ Ct → PMF (RecA Pt Ct × Ss)) (I : Ss → Prop)
    (h : ∀ s x, I s → ∀ y ∈ (Os s x).support, I y.2)
    (s : Sc × Ss) (q : RecQ Pt Ct) (hs : I s.2) :
    ∀ y ∈ (recOracle Oc Os s q).support, I y.2.2 := by
  rcases q with ⟨d, x⟩ | ⟨d, x⟩ <;> cases d <;>
    simp only [recOracle, RecQ.dir, RecQ.body, PMF.support_map, Set.mem_image] <;>
    rintro _ ⟨y, hy, rfl⟩ <;> first | exact h _ _ hs y hy | exact hs

/-! ## The ideal direction is the AEAD game at distinct nonces -/

variable [SampleableType Pt] [SampleableType Ct] [SampleableType N] [DecidableEq Hd]

/-- An entry of the log of the ideal direction as an entry of the log of the AEAD game. -/
def logEntry (nce : N → ℕ → N) (hd : Hd) (iv : N) (e : (ℕ × Pt) × Ct) :
    (Pt × (N × Hd)) × Ct :=
  ((e.1.2, (nce iv e.1.1, hd)), e.2)

/-- The state of the ideal direction as a state of the direction over the AEAD game. -/
def idealToAead (nce : N → ℕ → N) (hd : Hd) (iv : N) (s : (ℕ × ℕ) × List ((ℕ × Pt) × Ct)) :
    (ℕ × ℕ) × List ((Pt × (N × Hd)) × Ct) :=
  (s.1, s.2.map (logEntry nce hd iv))

/-- The invariant of the ideal direction: every logged position is below the write sequence
number and below `L`. -/
def IdealInv (L : ℕ) (s : (ℕ × ℕ) × List ((ℕ × Pt) × Ct)) : Prop :=
  ∀ e ∈ s.2, e.1.1 < s.1.1 ∧ e.1.1 < L

omit [SampleableType Ct] in
/-- At a fresh position below `L`, the log of the AEAD game has no entry for the sealing query. -/
theorem lookup_logEntry_eq_none {nce : N → ℕ → N} {L : ℕ} {iv : N}
    (hn : Set.InjOn (nce iv) (Set.Iio L)) (hd : Hd) (pt : Pt) (log : List ((ℕ × Pt) × Ct))
    {i : ℕ} (hi : i < L) (h : ∀ e ∈ log, e.1.1 < i) :
    (log.map (logEntry nce hd iv)).lookup (pt, (nce iv i, hd)) = none := by
  induction log with
  | nil => rfl
  | cons e log ih =>
    have hne : nce iv i ≠ nce iv e.1.1 := fun h' =>
      Nat.ne_of_lt (h e List.mem_cons_self)
        (hn (show e.1.1 < L by have := h e List.mem_cons_self; omega) hi h'.symm)
    grind [List.lookup, logEntry]

omit [SampleableType Pt] in
/-- At a position below `L`, decryption from the log of the AEAD game is the ideal opening. -/
theorem aeadLogDecrypt_logEntry {nce : N → ℕ → N} {L : ℕ} {iv : N}
    (hn : Set.InjOn (nce iv) (Set.Iio L)) (hd : Hd) (ct : Ct) (log : List ((ℕ × Pt) × Ct))
    {j : ℕ} (hj : j < L) (h : ∀ e ∈ log, e.1.1 < L) :
    aeadLogDecrypt (log.map (logEntry nce hd iv)) ct (nce iv j, hd) = idealOpen log j ct := by
  induction log with
  | nil => rfl
  | cons e log ih =>
    have hiff : nce iv e.1.1 = nce iv j ↔ e.1.1 = j :=
      ⟨fun h' => hn (h e List.mem_cons_self) hj h', fun h' => h' ▸ rfl⟩
    have ih' := ih fun e' he' => h e' (List.mem_cons_of_mem _ he')
    simp only [aeadLogDecrypt, idealOpen, List.map_cons, List.find?_cons, logEntry] at ih' ⊢
    grind

omit [SampleableType Pt] in
/-- The ideal direction keeps its invariant. -/
theorem dirIdeal_inv (L : ℕ) (s : (ℕ × ℕ) × List ((ℕ × Pt) × Ct)) (x : Pt ⊕ Ct)
    (hs : IdealInv L s) : ∀ y ∈ (dirIdeal L s x).support, IdealInv L y.2 := by
  obtain ⟨⟨i, j⟩, log⟩ := s
  rcases x with pt | ct
  · by_cases hi : i < L
    · simp only [dirIdeal, hi, ite_true, PMF.support_map, Set.mem_image]
      rintro _ ⟨c, -, rfl⟩ e he
      simp only [List.mem_cons] at he
      rcases he with rfl | he
      · exact ⟨Nat.lt_succ_self _, hi⟩
      · exact ⟨Nat.lt_succ_of_lt (hs e he).1, (hs e he).2⟩
    · simp only [dirIdeal, hi, ite_false, PMF.support_pure, Set.mem_singleton_iff]
      rintro _ rfl
      exact hs
  · by_cases hj : j < L
    · simp only [dirIdeal, hj, ite_true, PMF.support_pure, Set.mem_singleton_iff]
      rintro _ rfl
      exact hs
    · simp only [dirIdeal, hj, ite_false, PMF.support_pure, Set.mem_singleton_iff]
      rintro _ rfl
      exact hs

/-- **The ideal direction is the direction over the ideal AEAD oracles** at a nonce function
injective below `L`: every query is fresh, so a sealing query is answered by a uniform
ciphertext, and an opening query at a position accepts exactly the ciphertext sent there. -/
theorem dirIdeal_map {nce : N → ℕ → N} {L : ℕ} {iv : N} (hn : Set.InjOn (nce iv) (Set.Iio L))
    (hd : Hd) (s : (ℕ × ℕ) × List ((ℕ × Pt) × Ct)) (x : Pt ⊕ Ct) (hs : IdealInv L s) :
    (dirIdeal L s x).map (Prod.map id (idealToAead nce hd iv)) =
      OracleAdv.simOracle (dirProg nce hd L iv) aeadIdealOracle (idealToAead nce hd iv s) x := by
  obtain ⟨⟨i, j⟩, log⟩ := s
  rcases x with pt | ct
  · by_cases hi : i < L
    · have hl := lookup_logEntry_eq_none hn hd pt log hi fun e he => (hs e he).1
      simp [dirIdeal, dirProg, idealToAead, hi, OracleAdv.simOracle, aeadIdealOracle, hl,
        PMF.map_comp, Function.comp_def, sealAns, logEntry, PMF.bind_map, PMF.map_bind,
        PMF.pure_map]
      rfl
    · simp [dirIdeal, dirProg, idealToAead, hi, OracleAdv.simOracle, PMF.pure_map]
  · by_cases hj : j < L
    · have hl := aeadLogDecrypt_logEntry hn hd ct log hj fun e he => (hs e he).2
      simp [dirIdeal, dirProg, idealToAead, hj, OracleAdv.simOracle, aeadIdealOracle, hl,
        openAns, PMF.pure_map]
    · simp [dirIdeal, dirProg, idealToAead, hj, OracleAdv.simOracle, PMF.pure_map]

end Hops

/-! ## The record hop -/

section Hop

variable {Pt Ct N Hd Kt Sec V : Type} [SampleableType Pt] [SampleableType Ct] [SampleableType N]
  [SampleableType Kt] [Fintype Sec] [Nonempty Sec] [DecidableEq Hd]

/-- **The record hop.** For a nonce function injective below `L` at every IV, the advantage of a
distinguisher between the real view of the schedule under a uniform session key and the ideal
view is at most the PRG advantage of the traffic-key derivation and the AEAD advantage of each
direction. -/
theorem advantageA_rec_le (D : AEADDef Pt Ct (N × Hd) Kt) (tk : Sec → Kt × N)
    (nce : N → ℕ → N) (hd : Hd) (L : ℕ) (Sch : OracleAdv (RecQ Pt Ct) (RecA Pt Ct) V)
    (hn : ∀ iv, Set.InjOn (nce iv) (Set.Iio L)) (Adist : V → SPComp Bool) :
    AdvantageA (SPComp.bind (SPComp.sample (TKey Sec)) (recRealView D tk nce hd L Sch))
        (recIdealView L Sch) Adist ≤ recBound D tk nce hd L Sch Adist := by
  have hreal : prTrue (SPComp.bind (SPComp.bind (SPComp.sample (TKey Sec))
      (recRealView D tk nce hd L Sch)) Adist) Heap.empty =
      ((PMF.uniformFintype (Sec × Sec)).bind fun p =>
        (recViewAt D nce hd L Sch ((tkPRG tk).stretch p)).bind (outBool Adist)) true := by
    unfold recRealView
    rw [sample_eq_liftPMF, liftPMF_bind_liftPMF, prTrue_liftPMF_bind, PMF.bind_bind]
    simp only [TKey, uniform_prod_bind, PMF.bind_const]
  have hprg : prTrue (SPComp.bind (prg_real (tkPRG tk)) (recPrgRed D nce hd L Sch Adist))
      Heap.empty = ((PMF.uniformFintype (Sec × Sec)).bind fun p =>
        (recViewAt D nce hd L Sch ((tkPRG tk).stretch p)).bind (outBool Adist)) true := by
    have e : prg_real (tkPRG (N := N) tk) =
        liftPMF ((PMF.uniformFintype (Sec × Sec)).map (tkPRG tk).stretch) := by
      rw [← liftPMF_bind_pure, ← sample_eq_liftPMF]
      rfl
    rw [e, prTrue_liftPMF_bind, PMF.bind_map]
    unfold recPrgRed
    simp only [Function.comp_def, outBool_liftPMF_bind]
  have hideal1 : prTrue (SPComp.bind prg_ideal (recPrgRed D nce hd L Sch Adist)) Heap.empty =
      ((PMF.uniformFintype ((Kt × N) × (Kt × N))).bind fun kk =>
        (recViewAt D nce hd L Sch kk).bind (outBool Adist)) true := by
    rw [prg_ideal, sample_eq_liftPMF, prTrue_liftPMF_bind]
    unfold recPrgRed
    congr 2
    funext kk
    exact outBool_liftPMF_bind _ _ kk
  have haeadC : prTrue (AEAD_CCA_Game_Real D (recAeadRed D nce hd L Sch .c2s Adist))
      Heap.empty = ((PMF.uniformFintype ((Kt × N) × (Kt × N))).bind fun kk =>
        (recViewAt D nce hd L Sch kk).bind (outBool Adist)) true := by
    rw [AEAD_CCA_Game_Real, prTrue_liftPMF]
    simp only [recAeadRed, OracleAdv.run_rand, PMF.map_bind, run_fwdC, recViewAt, PMF.bind_map,
      Function.comp_def, uniform_prod_bind]
    rfl
  have hC : ∀ (ivc : N) (ks : Kt × N),
      (OracleAdv.run (recOracle (OracleAdv.simOracle (dirProg nce hd L ivc) aeadIdealOracle)
        (dirReal D nce hd L ks)) Sch (((0, 0), []), ((0, 0), ()))).bind
          (fun x => outBool Adist x.1) =
      (OracleAdv.run (recOracle (dirIdeal L) (dirReal D nce hd L ks)) Sch
        (((0, 0), []), ((0, 0), ()))).bind (fun x => outBool Adist x.1) := by
    intro ivc ks
    have hm := OracleAdv.run_map_state_of_inv (recOracle (dirIdeal L) (dirReal D nce hd L ks))
      (recOracle (OracleAdv.simOracle (dirProg nce hd L ivc) aeadIdealOracle)
        (dirReal D nce hd L ks)) (Prod.map (idealToAead nce hd ivc) id)
      (fun s => IdealInv L s.1)
      (fun s q hs => recOracle_inv_c _ _ _ (fun s x hs => dirIdeal_inv L s x hs) s q hs)
      (fun s q hs => recOracle_map_c _ _ _ _ _ (fun s x hs => dirIdeal_map (hn ivc) hd s x hs)
        s q hs) Sch (((0, 0), []), ((0, 0), ())) (by simp [IdealInv])
    calc _ = ((OracleAdv.run (recOracle (dirIdeal L) (dirReal D nce hd L ks)) Sch
          (((0, 0), []), ((0, 0), ()))).map
            (Prod.map id (Prod.map (idealToAead nce hd ivc) id))).bind
              (fun x => outBool Adist x.1) := by rw [hm]; rfl
      _ = _ := map_state_bind_fst _ _ _
  have hidealC : prTrue (AEAD_CCA_Game_Ideal (recAeadRed D nce hd L Sch .c2s Adist))
      Heap.empty = ((PMF.uniformFintype (Kt × N)).bind fun ks =>
        (OracleAdv.run (recOracle (dirIdeal L) (dirReal D nce hd L ks)) Sch
          (((0, 0), []), ((0, 0), ()))).bind fun x => outBool Adist x.1) true := by
    rw [AEAD_CCA_Game_Ideal, prTrue_liftPMF]
    simp only [recAeadRed, OracleAdv.run_rand, PMF.map_bind, run_fwdC, hC, PMF.bind_const]
  have hrealS : prTrue (AEAD_CCA_Game_Real D (recAeadRed D nce hd L Sch .s2c Adist))
      Heap.empty = ((PMF.uniformFintype (Kt × N)).bind fun ks =>
        (OracleAdv.run (recOracle (dirIdeal L) (dirReal D nce hd L ks)) Sch
          (((0, 0), []), ((0, 0), ()))).bind fun x => outBool Adist x.1) true := by
    rw [AEAD_CCA_Game_Real, prTrue_liftPMF]
    simp only [recAeadRed, OracleAdv.run_rand, PMF.map_bind, run_fwdS, uniform_prod_bind]
    rfl
  have hS : ∀ ivs : N,
      (OracleAdv.run (recOracle (dirIdeal L)
        (OracleAdv.simOracle (dirProg nce hd L ivs) aeadIdealOracle)) Sch
          (((0, 0), []), ((0, 0), []))).bind (fun x => outBool Adist x.1) =
      (OracleAdv.run (recOracle (dirIdeal (Pt := Pt) (Ct := Ct) L) (dirIdeal L)) Sch
        (((0, 0), []), ((0, 0), []))).bind (fun x => outBool Adist x.1) := by
    intro ivs
    have hm := OracleAdv.run_map_state_of_inv (recOracle (dirIdeal L) (dirIdeal L))
      (recOracle (dirIdeal L) (OracleAdv.simOracle (dirProg nce hd L ivs) aeadIdealOracle))
      (Prod.map id (idealToAead nce hd ivs)) (fun s => IdealInv L s.2)
      (fun s q hs => recOracle_inv_s _ _ _ (fun s x hs => dirIdeal_inv L s x hs) s q hs)
      (fun s q hs => recOracle_map_s _ _ _ _ _ (fun s x hs => dirIdeal_map (hn ivs) hd s x hs)
        s q hs) Sch (((0, 0), []), ((0, 0), [])) (by simp [IdealInv])
    calc _ = ((OracleAdv.run (recOracle (dirIdeal L) (dirIdeal L)) Sch
          (((0, 0), []), ((0, 0), []))).map
            (Prod.map id (Prod.map id (idealToAead nce hd ivs)))).bind
              (fun x => outBool Adist x.1) := by rw [hm]; rfl
      _ = _ := map_state_bind_fst _ _ _
  have hidealS : prTrue (AEAD_CCA_Game_Ideal (recAeadRed D nce hd L Sch .s2c Adist))
      Heap.empty = ((OracleAdv.run (recOracle (dirIdeal (Pt := Pt) (Ct := Ct) L) (dirIdeal L)) Sch
        (((0, 0), []), ((0, 0), []))).bind fun x => outBool Adist x.1) true := by
    rw [AEAD_CCA_Game_Ideal, prTrue_liftPMF]
    simp only [recAeadRed, OracleAdv.run_rand, PMF.map_bind, run_fwdS, hS, PMF.bind_const]
  have hidealV : prTrue (SPComp.bind (recIdealView L Sch) Adist) Heap.empty =
      ((OracleAdv.run (recOracle (dirIdeal (Pt := Pt) (Ct := Ct) L) (dirIdeal L)) Sch
        (((0, 0), []), ((0, 0), []))).bind fun x => outBool Adist x.1) true := by
    rw [recIdealView, prTrue_liftPMF_bind, PMF.bind_map]
    rfl
  simp only [AdvantageA, recBound, PRG_Advantage, AEAD_CCA_Advantage]
  refine (advantage_triangle _ (SPComp.bind prg_ideal (recPrgRed D nce hd L Sch Adist)) _).trans ?_
  rw [add_assoc]
  refine add_le_add (le_of_eq ?_) ((advantage_triangle _
    (AEAD_CCA_Game_Ideal (recAeadRed D nce hd L Sch .c2s Adist)) _).trans (le_of_eq ?_))
  · simp only [Advantage, hreal, hprg]
  · simp only [Advantage, hideal1, haeadC, hidealC, hrealS, hidealS, hidealV]

end Hop

/-! ## Time certificates of the reductions -/

time_cert_try derive_reduction recAeadRed

time_cert_try derive_reduction recPrgRed

end CatCrypt.Crypto.AKE.RecordView
