/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.KEMAdvDilate
public import CatCryptCore.Quantum.QROM.MultiRound
public import CatCryptCore.Quantum.QROM.O2HTheorem

/-!
# One-way to hiding for adversaries with general local operations

The semi-classical one-way-to-hiding bound
`|Pr[out = 1] − Pr[out = 1 ∧ ¬Find]| ≤ 2 √(q' · Pr[Find])` for a multi-round
adversary `A : QAdvMRGen m n w q k c a`, whose local operations are arbitrary
trace-preserving completely positive maps (complete Kraus families) and whose
initial state is any density matrix, with `q' = flatQ q k q = (k + 1) q` the
total query count of `A`.

The semi-classical run of a general adversary replaces every oracle call by the
semi-classical oracle `scOracleQ H S` and returns the output bit and the `Find`
flag; on a unitary adversary it is `runSCMR` (`runSCMRGen_toGen`). The dilation
`dilate A` of `KEMAdvDilate` replaces each local operation by a unitary on a
fresh ancilla; every step relates the semi-classical runs of the two adversaries
by `DilatesQ`, so the dilated unitary adversary has the probabilities of every
event of `(output, Find)` that `A` has. The single-run embedding `toQAdv` of the
dilated adversary then carries the three probabilities (`prOutMR_eq`,
`prOutNoFindMR_eq`, `prFindMR_eq`), and `o2h_semiclassical_mixed` applies.

## Main definitions

* `scChainG`, `mrChainSCG` — the semi-classical chain and multi-round chain
  with arbitrary `Unit` instruments as local operations
* `runSCMRGen`, `prSCMRGen` — the semi-classical run of a general adversary
  and the probability of an event of `(output, Find)`
* `prOutNoFindMRGen`, `prFindMRGen` — `Pr[out = 1 ∧ ¬Find]` and `Pr[Find]`

## Main results

* `liftsQ_scChainG`, `liftsQ_mrChainSCG`, `dilatesQ_scChainG`,
  `dilatesQ_mrChainSCG_head`, `dilatesQ_mrChainSCG_tail` — the lifting and
  dilation relations pass through the semi-classical chains
* `prOutNoFindMRGen_toGen`, `prFindMRGen_toGen` — on a unitary adversary the
  two probabilities are `prOutNoFindMR` and `prFindMR`
* `prSCMRGen_of_dilatesQ`, `QAdvMRK.prSCMRGen_dilL` — a dilation step preserves
  the probability of every event of `(output, Find)`
* `prSCMRGen_dilate` — `dilate A` has the probability of every event of
  `(output, Find)` that `A` has
* `o2h_semiclassical_gen` — the semi-classical one-way-to-hiding bound for a
  general multi-round adversary
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Matrix CatCrypt.Quantum CatCrypt.Quantum.TensorProduct CatCrypt.Quantum.UnitaryChannel
  CatCrypt.Quantum.Stinespring

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## Semi-classical chains with general local operations -/

section Chain

variable {d c a q : ℕ}

/-- `U₀ ; O ; U₁ ; … ; O ; U_q` for `Unit` instruments `U i` and a `Bool`
oracle `O`, returning the disjunction of the oracle outcomes. -/
def scChainG (O : QComp d Bool) :
    (q : ℕ) → (Fin (q + 1) → QComp d Unit) → QComp d Bool
  | 0, U => QComp.qbind (U 0) fun _ => QComp.qpure false
  | q + 1, U =>
    QComp.qbind (U 0) fun _ => QComp.qbind O fun b =>
      QComp.qbind (scChainG O q (Fin.tail U)) fun b' => QComp.qpure (b || b')

/-- `head ; (round ; segment)ᵏ` over a `Bool` oracle with general local
operations, returning the disjunction of the oracle outcomes. -/
def mrChainSCG (O : QComp d Bool) (f : Fin c → Fin a) :
    (k : ℕ) → (q₀ : ℕ) → (Fin (q₀ + 1) → QComp d Unit) →
      (Fin k → Fin (q + 1) → QComp d Unit) → (Fin k → ClassicalRound d c a) → QComp d Bool
  | 0, q₀, head, _, _ => scChainG O q₀ head
  | k + 1, q₀, head, tail, R =>
    QComp.qbind (scChainG O q₀ head) fun b => QComp.qbind (roundU (R 0) f) fun _ =>
      QComp.qbind (mrChainSCG O f k q (tail 0) (Fin.tail tail) (Fin.tail R)) fun b' =>
        QComp.qpure (b || b')

theorem scChain_eq_scChainG (O : QComp d Bool) :
    ∀ (q : ℕ) (U : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ),
      scChain O q U = scChainG O q (unitaryChannel ∘ U)
  | 0, _ => rfl
  | q + 1, U => by
    rw [scChain, scChainG, scChain_eq_scChainG O q (Fin.tail U)]
    rfl

theorem mrChainSC_eq_mrChainSCG (O : QComp d Bool) (f : Fin c → Fin a) :
    ∀ (k q₀ : ℕ) (head : Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ)
      (tail : Fin k → Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ)
      (R : Fin k → ClassicalRound d c a),
      mrChainSC O f k q₀ head tail R =
        mrChainSCG O f k q₀ (unitaryChannel ∘ head) (fun j => unitaryChannel ∘ tail j) R
  | 0, q₀, head, _, _ => scChain_eq_scChainG O q₀ head
  | k + 1, q₀, head, tail, R => by
    rw [mrChainSC, mrChainSCG, scChain_eq_scChainG O q₀ head,
      mrChainSC_eq_mrChainSCG O f k q (tail 0) (Fin.tail tail) (Fin.tail R)]
    rfl

variable {r D : ℕ}

theorem liftsQ_scChainG (e : Fin (d * r) ≃ Fin D) {O : QComp d Bool} {O' : QComp D Bool}
    (hO : LiftsQ e O O') :
    ∀ (q : ℕ) (U : Fin (q + 1) → QComp d Unit) (U' : Fin (q + 1) → QComp D Unit),
      (∀ i, LiftsQ e (U i) (U' i)) → LiftsQ e (scChainG O q U) (scChainG O' q U')
  | 0, _, _, hU => liftsQ_qbind e (hU 0) fun _ => liftsQ_qpure e _
  | q + 1, U, U', hU =>
    liftsQ_qbind e (hU 0) fun _ => liftsQ_qbind e hO fun _ =>
      liftsQ_qbind e (liftsQ_scChainG e hO q (Fin.tail U) (Fin.tail U') fun i => hU i.succ)
        fun _ => liftsQ_qpure e _

theorem liftsQ_mrChainSCG (e : Fin (d * r) ≃ Fin D) {O : QComp d Bool} {O' : QComp D Bool}
    (hO : LiftsQ e O O') (f : Fin c → Fin a) :
    ∀ (k q₀ : ℕ) (head : Fin (q₀ + 1) → QComp d Unit) (head' : Fin (q₀ + 1) → QComp D Unit)
      (tail : Fin k → Fin (q + 1) → QComp d Unit) (tail' : Fin k → Fin (q + 1) → QComp D Unit)
      (R : Fin k → ClassicalRound d c a) (R' : Fin k → ClassicalRound D c a),
      (∀ i, LiftsQ e (head i) (head' i)) → (∀ j i, LiftsQ e (tail j i) (tail' j i)) →
      (∀ j, LiftsQ e (roundU (R j) f) (roundU (R' j) f)) →
      LiftsQ e (mrChainSCG O f k q₀ head tail R) (mrChainSCG O' f k q₀ head' tail' R')
  | 0, q₀, head, head', _, _, _, _, hh, _, _ => liftsQ_scChainG e hO q₀ head head' hh
  | k + 1, q₀, head, head', tail, tail', R, R', hh, ht, hR =>
    liftsQ_qbind e (liftsQ_scChainG e hO q₀ head head' hh) fun _ =>
      liftsQ_qbind e (hR 0) fun _ =>
        liftsQ_qbind e (liftsQ_mrChainSCG e hO f k q (tail 0) (tail' 0) (Fin.tail tail)
          (Fin.tail tail') (Fin.tail R) (Fin.tail R') (ht 0) (fun j => ht j.succ)
          fun j => hR j.succ) fun _ => liftsQ_qpure e _

variable [NeZero r]

/-- A semi-classical chain whose operation at `p` dilates and whose other
operations lift is a dilation. -/
theorem dilatesQ_scChainG (e : Fin (d * r) ≃ Fin D) {O : QComp d Bool} {O' : QComp D Bool}
    (hO : LiftsQ e O O') :
    ∀ (q : ℕ) (U : Fin (q + 1) → QComp d Unit) (U' : Fin (q + 1) → QComp D Unit)
      (p : Fin (q + 1)), DilatesQ e (U p) (U' p) → (∀ i, i ≠ p → LiftsQ e (U i) (U' i)) →
      DilatesQ e (scChainG O q U) (scChainG O' q U')
  | 0, _, _, p, hp, _ => by
    rw [Fin.fin_one_eq_zero p] at hp
    exact dilatesQ_qbind_liftsQ hp fun _ => liftsQ_qpure e _
  | q + 1, U, U', p, hp, hU => by
    induction p using Fin.cases with
    | zero =>
      exact dilatesQ_qbind_liftsQ hp fun _ => liftsQ_qbind e hO fun _ =>
        liftsQ_qbind e (liftsQ_scChainG e hO q (Fin.tail U) (Fin.tail U') fun i =>
          hU i.succ (Fin.succ_ne_zero i)) fun _ => liftsQ_qpure e _
    | succ p =>
      exact liftsQ_qbind_dilatesQ (hU 0 (Fin.succ_ne_zero p).symm) fun _ =>
        liftsQ_qbind_dilatesQ hO fun _ =>
          dilatesQ_qbind_liftsQ (dilatesQ_scChainG e hO q (Fin.tail U) (Fin.tail U') p hp
            fun i hi => hU i.succ fun h => hi (Fin.succ_injective _ h)) fun _ =>
              liftsQ_qpure e _

/-- A multi-round semi-classical chain whose head operation at `p` dilates and
whose other operations and rounds lift is a dilation. -/
theorem dilatesQ_mrChainSCG_head (e : Fin (d * r) ≃ Fin D) {O : QComp d Bool}
    {O' : QComp D Bool} (hO : LiftsQ e O O') (f : Fin c → Fin a) (k q₀ : ℕ)
    (head : Fin (q₀ + 1) → QComp d Unit) (head' : Fin (q₀ + 1) → QComp D Unit)
    (tail : Fin k → Fin (q + 1) → QComp d Unit) (tail' : Fin k → Fin (q + 1) → QComp D Unit)
    (R : Fin k → ClassicalRound d c a) (R' : Fin k → ClassicalRound D c a) (p : Fin (q₀ + 1))
    (hp : DilatesQ e (head p) (head' p)) (hh : ∀ i, i ≠ p → LiftsQ e (head i) (head' i))
    (ht : ∀ j i, LiftsQ e (tail j i) (tail' j i))
    (hR : ∀ j, LiftsQ e (roundU (R j) f) (roundU (R' j) f)) :
    DilatesQ e (mrChainSCG O f k q₀ head tail R) (mrChainSCG O' f k q₀ head' tail' R') := by
  cases k with
  | zero => exact dilatesQ_scChainG e hO q₀ head head' p hp hh
  | succ k =>
    exact dilatesQ_qbind_liftsQ (dilatesQ_scChainG e hO q₀ head head' p hp hh) fun _ =>
      liftsQ_qbind e (hR 0) fun _ =>
        liftsQ_qbind e (liftsQ_mrChainSCG e hO f k q (tail 0) (tail' 0) (Fin.tail tail)
          (Fin.tail tail') (Fin.tail R) (Fin.tail R') (ht 0) (fun j => ht j.succ)
          fun j => hR j.succ) fun _ => liftsQ_qpure e _

/-- A multi-round semi-classical chain whose tail operation at `(j, i)` dilates
and whose other operations and rounds lift is a dilation. -/
theorem dilatesQ_mrChainSCG_tail (e : Fin (d * r) ≃ Fin D) {O : QComp d Bool}
    {O' : QComp D Bool} (hO : LiftsQ e O O') (f : Fin c → Fin a) :
    ∀ (k q₀ : ℕ) (head : Fin (q₀ + 1) → QComp d Unit) (head' : Fin (q₀ + 1) → QComp D Unit)
      (tail : Fin k → Fin (q + 1) → QComp d Unit) (tail' : Fin k → Fin (q + 1) → QComp D Unit)
      (R : Fin k → ClassicalRound d c a) (R' : Fin k → ClassicalRound D c a)
      (j : Fin k) (i : Fin (q + 1)), DilatesQ e (tail j i) (tail' j i) →
      (∀ j' i', (j', i') ≠ (j, i) → LiftsQ e (tail j' i') (tail' j' i')) →
      (∀ i, LiftsQ e (head i) (head' i)) → (∀ j, LiftsQ e (roundU (R j) f) (roundU (R' j) f)) →
      DilatesQ e (mrChainSCG O f k q₀ head tail R) (mrChainSCG O' f k q₀ head' tail' R')
  | 0, _, _, _, _, _, _, _, j, _, _, _, _, _ => j.elim0
  | k + 1, q₀, head, head', tail, tail', R, R', j, i, hp, ht, hh, hR => by
    refine liftsQ_qbind_dilatesQ (liftsQ_scChainG e hO q₀ head head' hh) fun _ =>
      liftsQ_qbind_dilatesQ (hR 0) fun _ => dilatesQ_qbind_liftsQ ?_ fun _ => liftsQ_qpure e _
    induction j using Fin.cases with
    | zero =>
      exact dilatesQ_mrChainSCG_head e hO f k q (tail 0) (tail' 0) (Fin.tail tail)
        (Fin.tail tail') (Fin.tail R) (Fin.tail R') i hp
        (fun i' hi => ht 0 i' fun h => hi (congrArg Prod.snd h))
        (fun j' i' => ht j'.succ i' fun h => Fin.succ_ne_zero j' (congrArg Prod.fst h))
        fun j => hR j.succ
    | succ j =>
      exact dilatesQ_mrChainSCG_tail e hO f k q (tail 0) (tail' 0) (Fin.tail tail)
        (Fin.tail tail') (Fin.tail R) (Fin.tail R') j i hp
        (fun j' i' h => ht j'.succ i' fun h' =>
          h (Prod.ext (Fin.succ_injective _ (Prod.mk.inj h').1) (Prod.mk.inj h').2))
        (fun i' => ht 0 i' fun h => Fin.succ_ne_zero j (congrArg Prod.fst h).symm)
        fun j => hR j.succ

end Chain

/-! ## Semi-classical runs of general and unitary adversaries -/

section Run

variable {m n w q k c a : ℕ} [NeZero n]

/-- The semi-classical run of a general adversary: `scOracleQ H S` in place of
the oracle, returning `(output, Find)`. -/
def runSCMRGen (A : QAdvMRGen m n w q k c a) (H : Fin m → Fin n) (f : Fin c → Fin a)
    (S : Finset (Fin m)) : QComp (m * n * w) (Bool × Bool) :=
  QComp.qbind (mrChainSCG (scOracleQ m n w H S) f k q (fun i => (A.seg 0 i).toQComp)
    (fun j i => (Fin.tail A.seg j i).toQComp) A.rounds) fun fl =>
      QComp.qbind A.measure fun out => QComp.qpure (out, fl)

/-- The probability of the event `g` of `(output, Find)` in the semi-classical
run of a general adversary. -/
def prSCMRGen (A : QAdvMRGen m n w q k c a) (H : Fin m → Fin n) (f : Fin c → Fin a)
    (S : Finset (Fin m)) (g : Bool × Bool → Bool) : ℝ≥0∞ :=
  prTrue_Q (QComp.qbind (runSCMRGen A H f S) fun p => QComp.qpure (g p)) A.init

/-- `Pr[out = 1 ∧ ¬Find]` for a general adversary. -/
def prOutNoFindMRGen (A : QAdvMRGen m n w q k c a) (H : Fin m → Fin n) (f : Fin c → Fin a)
    (S : Finset (Fin m)) : ℝ≥0∞ :=
  prSCMRGen A H f S fun p => p.1 && !p.2

/-- `Pr[Find]` for a general adversary. -/
def prFindMRGen (A : QAdvMRGen m n w q k c a) (H : Fin m → Fin n) (f : Fin c → Fin a)
    (S : Finset (Fin m)) : ℝ≥0∞ :=
  prSCMRGen A H f S fun p => p.2

/-- On a unitary adversary the semi-classical run is `runSCMR`. -/
theorem runSCMRGen_toGen (A : QAdvMR m n w q k c a) (H : Fin m → Fin n) (f : Fin c → Fin a)
    (S : Finset (Fin m)) : runSCMRGen A.toGen H f S = runSCMR A H f S := by
  unfold runSCMRGen runSCMR
  rw [mrChainSC_eq_mrChainSCG]
  rfl

theorem prOutNoFindMRGen_toGen (A : QAdvMR m n w q k c a) (H : Fin m → Fin n)
    (f : Fin c → Fin a) (S : Finset (Fin m)) :
    prOutNoFindMRGen A.toGen H f S = prOutNoFindMR A H f S := by
  unfold prOutNoFindMRGen prSCMRGen prOutNoFindMR
  rw [runSCMRGen_toGen]
  rfl

theorem prFindMRGen_toGen (A : QAdvMR m n w q k c a) (H : Fin m → Fin n)
    (f : Fin c → Fin a) (S : Finset (Fin m)) :
    prFindMRGen A.toGen H f S = prFindMR A H f S := by
  unfold prFindMRGen prSCMRGen prFindMR
  rw [runSCMRGen_toGen]
  rfl

theorem prSCMRGen_castMR {w₁ w₂ : ℕ} (h : w₁ = w₂) (A : QAdvMR m n w₁ q k c a)
    (H : Fin m → Fin n) (f : Fin c → Fin a) (S : Finset (Fin m)) (g : Bool × Bool → Bool) :
    prSCMRGen (castMR h A).toGen H f S g = prSCMRGen A.toGen H f S g := by
  subst h
  rfl

end Run

/-! ## Dilation steps preserve the semi-classical probabilities -/

section GenStep

variable {m n W W' D q k c a : ℕ}

theorem liftsQ_scOracleQ_padE [NeZero n] (hW : W * D = W') (H : Fin m → Fin n)
    (S : Finset (Fin m)) :
    LiftsQ (padE m n hW) (scOracleQ m n W H S) (scOracleQ m n W' H S) := by
  subst hW
  exact liftsQ_scOracleQ H S

variable [NeZero n]

/-- A general adversary whose operation at `p` dilates the one of `B`, whose
other operations, rounds and final projector are lifts of those of `B`, and
whose initial state is `ρ ⊗ |0⟩⟨0|` for the initial state `ρ` of `B`, has the
probability of every event of `(output, Find)` that `B` has. -/
theorem prSCMRGen_of_dilatesQ [NeZero D] (hW : W * D = W') (B : QAdvMRGen m n W q k c a)
    (B' : QAdvMRGen m n W' q k c a) (p : Fin (k + 1) × Fin (q + 1))
    (hp : DilatesQ (padE m n hW) (B.seg p.1 p.2).toQComp (B'.seg p.1 p.2).toQComp)
    (hseg : ∀ j i, (j, i) ≠ p → LiftsQ (padE m n hW) (B.seg j i).toQComp (B'.seg j i).toQComp)
    (hR : ∀ j, B'.rounds j = liftRA (padE m n hW) (B.rounds j))
    (hfin : B'.final = kr (padE m n hW) B.final 1)
    (hinit : B'.init.val = kr (padE m n hW) B.init.val (ancProj 0)) (H : Fin m → Fin n)
    (f : Fin c → Fin a) (S : Finset (Fin m)) (g : Bool × Bool → Bool) :
    prSCMRGen B' H f S g = prSCMRGen B H f S g := by
  have hRL : ∀ j, LiftsQ (padE m n hW) (roundU (B.rounds j) f) (roundU (B'.rounds j) f) :=
    fun j => by rw [hR]; exact liftsQ_roundU_liftRA _ _ f
  have hO := liftsQ_scOracleQ_padE hW H S
  have hC : DilatesQ (padE m n hW)
      (mrChainSCG (scOracleQ m n W H S) f k q (fun i => (B.seg 0 i).toQComp)
        (fun j i => (Fin.tail B.seg j i).toQComp) B.rounds)
      (mrChainSCG (scOracleQ m n W' H S) f k q (fun i => (B'.seg 0 i).toQComp)
        (fun j i => (Fin.tail B'.seg j i).toQComp) B'.rounds) := by
    obtain ⟨j, i⟩ := p
    induction j using Fin.cases with
    | zero =>
      exact dilatesQ_mrChainSCG_head _ hO f k q _ _ _ _ _ _ i hp
        (fun i' hi => hseg 0 i' fun h => hi (congrArg Prod.snd h))
        (fun j i' => hseg j.succ i' fun h => Fin.succ_ne_zero j (congrArg Prod.fst h)) hRL
    | succ j =>
      exact dilatesQ_mrChainSCG_tail _ hO f k q _ _ _ _ _ _ j i hp
        (fun j' i' h => hseg j'.succ i' fun h' =>
          h (Prod.ext (Fin.succ_injective _ (Prod.mk.inj h').1) (Prod.mk.inj h').2))
        (fun i' => hseg 0 i' fun h => Fin.succ_ne_zero j (congrArg Prod.fst h).symm) hRL
  have hD : DilatesQ (padE m n hW)
      (QComp.qbind (runSCMRGen B H f S) fun p => QComp.qpure (g p))
      (QComp.qbind (runSCMRGen B' H f S) fun p => QComp.qpure (g p)) :=
    dilatesQ_qbind_liftsQ (dilatesQ_qbind_liftsQ hC fun _ =>
      liftsQ_qbind _ (liftsQ_measProj_of_eq _ _ _ hfin _ _ _ _) fun _ => liftsQ_qpure _ _)
      fun _ => liftsQ_qpure _ _
  unfold prSCMRGen prTrue_Q
  rw [hinit, hD.trace_branch]

namespace QAdvMRK

variable {r : ℕ}

theorem prSCMRGen_step [NeZero r] (hW : W * r = W') (p : Fin (k + 1) × Fin (q + 1))
    (B : QAdvMRK m n W r q k c a) (H : Fin m → Fin n) (f : Fin c → Fin a)
    (S : Finset (Fin m)) (g : Bool × Bool → Bool) :
    prSCMRGen (B.step hW p).toGen H f S g = prSCMRGen B.toGen H f S g := by
  refine prSCMRGen_of_dilatesQ hW B.toGen (B.step hW p).toGen p ?_ (fun j i h => ?_)
    (fun _ => rfl) rfl rfl H f S g
  · show DilatesQ _ (B.op p.1 p.2).toCP.toQComp
      (if (p.1, p.2) = p then _ else _ : KOp _ r).toCP.toQComp
    rw [if_pos rfl]
    exact KOp.dilatesQ_dil _ _
  · show LiftsQ _ (B.op j i).toCP.toQComp (if (j, i) = p then _ else _ : KOp _ r).toCP.toQComp
    rw [if_neg h]
    exact KOp.liftsQ_lift _ _

theorem prSCMRGen_dilL [NeZero r] (g : ℕ → ℕ) (hg : ∀ t, g t * r = g (t + 1))
    (B : QAdvMRK m n (g 0) r q k c a) (H : Fin m → Fin n) (f : Fin c → Fin a)
    (S : Finset (Fin m)) (ev : Bool × Bool → Bool) :
    ∀ l, prSCMRGen (B.dilL g hg l).toGen H f S ev = prSCMRGen B.toGen H f S ev
  | [] => rfl
  | p :: l => (prSCMRGen_step _ p _ H f S ev).trans (prSCMRGen_dilL g hg B H f S ev l)

theorem prSCMRGen_toMR (B : QAdvMRK m n W r q k c a) (h : ∀ j i, (B.op j i).isLeft = true)
    (H : Fin m → Fin n) (f : Fin c → Fin a) (S : Finset (Fin m)) (g : Bool × Bool → Bool) :
    prSCMRGen B.toMR.toGen H f S g = prSCMRGen B.toGen H f S g := by
  rw [toGen_toMR B h]

end QAdvMRK

end GenStep

/-! ## The dilated adversary -/

section Dilate

variable {m n w q k c a : ℕ} [NeZero n]

/-- The dilated adversary has the probability of every event of
`(output, Find)` that `A` has, in every oracle, every set `S` and every round
function. -/
theorem prSCMRGen_dilate (A : QAdvMRGen m n w q k c a) (H : Fin m → Fin n)
    (f : Fin c → Fin a) (S : Finset (Fin m)) (g : Bool × Bool → Bool) :
    prSCMRGen (dilate A).toGen H f S g = prSCMRGen A H f S g := by
  have := neZero_of_densityMatrix A.init
  rw [dilate, prSCMRGen_castMR]
  exact (QAdvMRK.prSCMRGen_toMR _
    (fun j i => QAdvMRK.isLeft_dilL _ _ _ _ (j, i) (mem_segPos _)) H f S g).trans
      ((QAdvMRK.prSCMRGen_dilL _ _ _ H f S g _).trans
        (congrArg (prSCMRGen · H f S g) (QAdvMRK.toGen_ofGen A)))

end Dilate

/-! ## One-way to hiding for general adversaries -/

section O2H

variable {m n w q k c a : ℕ} [NeZero n] [NeZero c]

/-- The semi-classical one-way-to-hiding bound for a multi-round adversary
whose local operations are arbitrary trace-preserving completely positive maps
and whose initial state is any density matrix:
`|Pr[out = 1] − Pr[out = 1 ∧ ¬Find]| ≤ 2 √(q' · Pr[Find])`, with
`q' = flatQ q k q = (k + 1) q` the total query count of `A`.

References: Ambainis, Hamburg, Unruh, "Quantum security proofs using
semi-classical oracles", CRYPTO 2019, ePrint 2018/904, Theorem 1. -/
theorem o2h_semiclassical_gen (A : QAdvMRGen m n w q k c a) (H : Fin m → Fin n)
    (f : Fin c → Fin a) (S : Finset (Fin m)) :
    absDiff (prOutMRGen A H f) (prOutNoFindMRGen A H f S) ≤
      2 * ((flatQ q k q : ℝ≥0∞) * prFindMRGen A H f S) ^ (1 / 2 : ℝ) := by
  have h := o2h_semiclassical_mixed (toQAdv (dilate A) f) H S
  rw [← prOutMR_eq, ← prOutNoFindMR_eq, ← prFindMR_eq, prOutMR_dilate,
    ← prOutNoFindMRGen_toGen, ← prFindMRGen_toGen] at h
  unfold prOutNoFindMRGen prFindMRGen at h ⊢
  rwa [prSCMRGen_dilate, prSCMRGen_dilate] at h

end O2H

end CatCrypt.Quantum.QROM
