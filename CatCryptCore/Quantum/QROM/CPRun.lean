/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.CPCompMonad
public import CatCryptCore.Quantum.QROM.QOwcpaAuxMeasured
public import CatCryptCore.Quantum.QROM.KEMQuantumGame

@[expose] public section

set_option autoImplicit false

/-!
# QROM adversary runs are completely positive

Every branch of every QROM adversary run is a completely positive map. The
building blocks (unitary channels, the projective measurements `measProj`, the
oracles `oracleQ` and `scOracleQ`, the rounds `roundQ` and `roundU`) are
conjugations or Kleisli composites of conjugations; the chains are proved
completely positive by induction, using that Kleisli composition preserves
complete positivity (`qbind_branch_isCPMap`).

Each run is then packaged as a `CPComp` whose underlying instrument is the run
itself (`toQComp_cpRun`), and the output probabilities of the QROM
development are `CPComp.prTrue` of these packages.

## Main results

* `oracleChain_branch_isCPMap`, `scChain_branch_isCPMap`,
  `mrChain_branch_isCPMap`, `mrChainSC_branch_isCPMap`,
  `mrPrefix_branch_isCPMap`, `mrPrefixU_branch_isCPMap`: the chains over a
  completely positive oracle are completely positive
* `run_branch_isCPMap`, `runSC_branch_isCPMap`, `runMR_branch_isCPMap`,
  `runSCMR_branch_isCPMap`: the adversary runs are completely positive
* `cpRun`, `cpRunSC`, `cpRunMR`, `cpRunSCMR`, `cpPrefixRunMR`: the runs as
  `CPComp`s
* `prOut_eq_prTrue`, `prOutSC_eq_prTrue`, `prFind_eq_prTrue`,
  `prOutMR_eq_prTrue`, `prFindMR_eq_prTrue`, `prOutPrefixMR_eq_prTrue`,
  `prWinKEM_eq_sum_prTrue`: the output probabilities as `CPComp.prTrue`
-/

open scoped Matrix ComplexOrder ENNReal
open Matrix CatCrypt.Quantum CatCrypt.Quantum.UnitaryChannel

noncomputable section

namespace CatCrypt.Quantum.QROM

open CatCrypt.Crypto.UCMonad.DiamondDominates (qbind_branch_isCPMap)

/-! ## Building blocks -/

section Blocks

variable {d c a : ℕ}

/-- Every branch of a unitary channel is completely positive. -/
theorem unitaryChannel_branch_isCPMap (U : Matrix.unitaryGroup (Fin d) ℂ) (u : Unit) :
    IsCPMap ((unitaryChannel U).branch u) :=
  (CPComp.unitary U).branch_cp u

/-- Every branch of the measurement `{P, 1 - P}` is completely positive. -/
theorem measProj_branch_isCPMap (P : Matrix (Fin d) (Fin d) ℂ) (hH : Pᴴ = P)
    (hI : P * P = P) (b : Bool) : IsCPMap ((measProj P hH hI).branch b) :=
  Measurement.measureOps_branch_isCPMap _ b

/-- Every branch of a round instrument is completely positive. -/
theorem roundQ_branch_isCPMap (R : ClassicalRound d c a) (f : Fin c → Fin a) (y : Fin c) :
    IsCPMap ((roundQ R f).branch y) :=
  Measurement.measureOps_branch_isCPMap _ y

/-- The round with its outcome discarded is completely positive. -/
theorem roundU_branch_isCPMap (R : ClassicalRound d c a) (f : Fin c → Fin a) (u : Unit) :
    IsCPMap ((roundU R f).branch u) :=
  qbind_branch_isCPMap _ _ (roundQ_branch_isCPMap R f) (fun _ => qpure_branch_isCPMap ()) u

end Blocks

section Oracles

variable (m n w : ℕ) [NeZero n]

/-- The standard oracle is completely positive. -/
theorem oracleQ_branch_isCPMap (H : Fin m → Fin n) (u : Unit) :
    IsCPMap ((oracleQ m n w H).branch u) :=
  unitaryChannel_branch_isCPMap _ u

/-- Every branch of the semi-classical oracle is completely positive. -/
theorem scOracleQ_branch_isCPMap (H : Fin m → Fin n) (S : Finset (Fin m)) (b : Bool) :
    IsCPMap ((scOracleQ m n w H S).branch b) :=
  qbind_branch_isCPMap _ _ (measProj_branch_isCPMap _ _ _)
    (fun b' => qbind_branch_isCPMap _ _ (oracleQ_branch_isCPMap m n w H)
      fun _ => qpure_branch_isCPMap b') b

end Oracles

/-! ## Chains -/

section Chains

variable {d c a q : ℕ}

/-- The chain `U₀ ; O ; … ; O ; U_q` over a completely positive oracle is
completely positive. -/
theorem oracleChain_branch_isCPMap (O : QComp d Unit) (hO : ∀ u, IsCPMap (O.branch u)) :
    ∀ (q : ℕ) (U : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) (u : Unit),
      IsCPMap ((oracleChain O q U).branch u)
  | 0, U, u => unitaryChannel_branch_isCPMap (U 0) u
  | q + 1, U, u =>
    qbind_branch_isCPMap _ _ (unitaryChannel_branch_isCPMap (U 0))
      (fun _ => qbind_branch_isCPMap _ _ hO
        fun _ => oracleChain_branch_isCPMap O hO q (Fin.tail U)) u

/-- Every branch of the chain over a completely positive `Bool`-valued oracle
is completely positive. -/
theorem scChain_branch_isCPMap (O : QComp d Bool) (hO : ∀ b, IsCPMap (O.branch b)) :
    ∀ (q : ℕ) (U : Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ) (b : Bool),
      IsCPMap ((scChain O q U).branch b)
  | 0, U, b =>
    qbind_branch_isCPMap _ _ (unitaryChannel_branch_isCPMap (U 0))
      (fun _ => qpure_branch_isCPMap false) b
  | q + 1, U, b =>
    qbind_branch_isCPMap _ _ (unitaryChannel_branch_isCPMap (U 0))
      (fun _ => qbind_branch_isCPMap _ _ hO
        fun b₀ => qbind_branch_isCPMap _ _ (scChain_branch_isCPMap O hO q (Fin.tail U))
          fun f => qpure_branch_isCPMap (b₀ || f)) b

/-- The multi-round chain over a completely positive oracle is completely
positive. -/
theorem mrChain_branch_isCPMap (O : QComp d Unit) (hO : ∀ u, IsCPMap (O.branch u))
    (f : Fin c → Fin a) :
    ∀ (k q₀ : ℕ) (head : Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ)
      (tail : Fin k → Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ)
      (R : Fin k → ClassicalRound d c a) (u : Unit),
      IsCPMap ((mrChain O f k q₀ head tail R).branch u)
  | 0, q₀, head, _, _, u => oracleChain_branch_isCPMap O hO q₀ head u
  | k + 1, q₀, head, tail, R, u =>
    qbind_branch_isCPMap _ _ (oracleChain_branch_isCPMap O hO q₀ head)
      (fun _ => qbind_branch_isCPMap _ _ (roundU_branch_isCPMap (R 0) f)
        fun _ => mrChain_branch_isCPMap O hO f k q (tail 0) (Fin.tail tail) (Fin.tail R)) u

/-- Every branch of the multi-round chain over a completely positive
`Bool`-valued oracle is completely positive. -/
theorem mrChainSC_branch_isCPMap (O : QComp d Bool) (hO : ∀ b, IsCPMap (O.branch b))
    (f : Fin c → Fin a) :
    ∀ (k q₀ : ℕ) (head : Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ)
      (tail : Fin k → Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ)
      (R : Fin k → ClassicalRound d c a) (b : Bool),
      IsCPMap ((mrChainSC O f k q₀ head tail R).branch b)
  | 0, q₀, head, _, _, b => scChain_branch_isCPMap O hO q₀ head b
  | k + 1, q₀, head, tail, R, b =>
    qbind_branch_isCPMap _ _ (scChain_branch_isCPMap O hO q₀ head)
      (fun b₀ => qbind_branch_isCPMap _ _ (roundU_branch_isCPMap (R 0) f)
        fun _ => qbind_branch_isCPMap _ _
          (mrChainSC_branch_isCPMap O hO f k q (tail 0) (Fin.tail tail) (Fin.tail R))
          fun b' => qpure_branch_isCPMap (b₀ || b')) b

/-- Every branch of the cut multi-round chain over a completely positive
`Bool`-valued oracle is completely positive. -/
theorem mrPrefix_branch_isCPMap (O : QComp d Bool) (hO : ∀ b, IsCPMap (O.branch b))
    (f : Fin c → Fin a) :
    ∀ (k q₀ : ℕ) (head : Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ)
      (tail : Fin k → Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ)
      (R : Fin k → ClassicalRound d c a) (j : Fin (flatQ q k q₀)) (b : Bool),
      IsCPMap ((mrPrefix O f k q₀ head tail R j).branch b)
  | 0, _, head, _, _, j, b => scChain_branch_isCPMap O hO j _ b
  | k + 1, q₀, head, tail, R, j, b => by
    rw [mrPrefix]
    split
    · exact scChain_branch_isCPMap O hO j _ b
    · exact qbind_branch_isCPMap _ _ (scChain_branch_isCPMap O hO q₀ head)
        (fun b₀ => qbind_branch_isCPMap _ _ (roundU_branch_isCPMap (R 0) f)
          fun _ => qbind_branch_isCPMap _ _
            (mrPrefix_branch_isCPMap O hO f k q (tail 0) (Fin.tail tail) (Fin.tail R) _)
            fun b' => qpure_branch_isCPMap (b₀ || b')) b

/-- The cut multi-round chain over a completely positive oracle is completely
positive. -/
theorem mrPrefixU_branch_isCPMap (O : QComp d Unit) (hO : ∀ u, IsCPMap (O.branch u))
    (f : Fin c → Fin a) :
    ∀ (k q₀ : ℕ) (head : Fin (q₀ + 1) → Matrix.unitaryGroup (Fin d) ℂ)
      (tail : Fin k → Fin (q + 1) → Matrix.unitaryGroup (Fin d) ℂ)
      (R : Fin k → ClassicalRound d c a) (j : Fin (flatQ q k q₀)) (u : Unit),
      IsCPMap ((mrPrefixU O f k q₀ head tail R j).branch u)
  | 0, _, head, _, _, j, u => oracleChain_branch_isCPMap O hO j _ u
  | k + 1, q₀, head, tail, R, j, u => by
    rw [mrPrefixU]
    split
    · exact oracleChain_branch_isCPMap O hO j _ u
    · exact qbind_branch_isCPMap _ _ (oracleChain_branch_isCPMap O hO q₀ head)
        (fun _ => qbind_branch_isCPMap _ _ (roundU_branch_isCPMap (R 0) f)
          fun _ => mrPrefixU_branch_isCPMap O hO f k q (tail 0) (Fin.tail tail)
            (Fin.tail R) _) u

end Chains

/-! ## Single-run adversaries -/

section Run

variable {m n w q : ℕ} [NeZero n]

omit [NeZero n] in
/-- Every branch of the final measurement of an adversary is completely
positive. -/
theorem QAdv.measure_branch_isCPMap (A : QAdv m n w q) (b : Bool) :
    IsCPMap (A.measure.branch b) :=
  measProj_branch_isCPMap _ _ _ b

/-- Every branch of the standard run is completely positive. -/
theorem run_branch_isCPMap (A : QAdv m n w q) (H : Fin m → Fin n) (b : Bool) :
    IsCPMap ((run A H).branch b) :=
  qbind_branch_isCPMap _ _
    (oracleChain_branch_isCPMap _ (oracleQ_branch_isCPMap m n w H) q A.U)
    (fun _ => A.measure_branch_isCPMap) b

/-- Every branch of the semi-classical run is completely positive. -/
theorem runSC_branch_isCPMap (A : QAdv m n w q) (H : Fin m → Fin n) (S : Finset (Fin m))
    (p : Bool × Bool) : IsCPMap ((runSC A H S).branch p) :=
  qbind_branch_isCPMap _ _
    (scChain_branch_isCPMap _ (scOracleQ_branch_isCPMap m n w H S) q A.U)
    (fun fl => qbind_branch_isCPMap _ _ A.measure_branch_isCPMap
      fun out => qpure_branch_isCPMap (out, fl)) p

/-- The standard run as a completely positive instrument. -/
def cpRun (A : QAdv m n w q) (H : Fin m → Fin n) : CPComp (m * n * w) Bool :=
  CPComp.mk' (run A H) (run_branch_isCPMap A H)

/-- The semi-classical run as a completely positive instrument. -/
def cpRunSC (A : QAdv m n w q) (H : Fin m → Fin n) (S : Finset (Fin m)) :
    CPComp (m * n * w) (Bool × Bool) :=
  CPComp.mk' (runSC A H S) (runSC_branch_isCPMap A H S)

@[simp]
theorem toQComp_cpRun (A : QAdv m n w q) (H : Fin m → Fin n) :
    (cpRun A H).toQComp = run A H :=
  CPComp.toQComp_mk' _ _

@[simp]
theorem toQComp_cpRunSC (A : QAdv m n w q) (H : Fin m → Fin n) (S : Finset (Fin m)) :
    (cpRunSC A H S).toQComp = runSC A H S :=
  CPComp.toQComp_mk' _ _

/-- `prOut` is the acceptance probability of `cpRun`. -/
theorem prOut_eq_prTrue (A : QAdv m n w q) (H : Fin m → Fin n) :
    prOut A H = (cpRun A H).prTrue A.init := rfl

/-- `prOutSC` is the acceptance probability of the output bit of `cpRunSC`. -/
theorem prOutSC_eq_prTrue (A : QAdv m n w q) (H : Fin m → Fin n) (S : Finset (Fin m)) :
    prOutSC A H S = (cpRunSC A H S >>= fun p => pure p.1).prTrue A.init := by
  simp only [CPComp.prTrue_def, CPComp.toQComp_bind, CPComp.toQComp_pure, toQComp_cpRunSC]
  rfl

/-- `prFind` is the acceptance probability of the find bit of `cpRunSC`. -/
theorem prFind_eq_prTrue (A : QAdv m n w q) (H : Fin m → Fin n) (S : Finset (Fin m)) :
    prFind A H S = (cpRunSC A H S >>= fun p => pure p.2).prTrue A.init := by
  simp only [CPComp.prTrue_def, CPComp.toQComp_bind, CPComp.toQComp_pure, toQComp_cpRunSC]
  rfl

end Run

/-! ## Multi-round adversaries -/

section MR

variable {m n w q k c a : ℕ} [NeZero n]

omit [NeZero n] in
/-- Every branch of the final measurement of a multi-round adversary is
completely positive. -/
theorem QAdvMR.measure_branch_isCPMap (A : QAdvMR m n w q k c a) (b : Bool) :
    IsCPMap (A.measure.branch b) :=
  measProj_branch_isCPMap _ _ _ b

/-- Every branch of the standard multi-round run is completely positive. -/
theorem runMR_branch_isCPMap (A : QAdvMR m n w q k c a) (H : Fin m → Fin n)
    (f : Fin c → Fin a) (b : Bool) : IsCPMap ((runMR A H f).branch b) :=
  qbind_branch_isCPMap _ _
    (mrChain_branch_isCPMap _ (oracleQ_branch_isCPMap m n w H) f k q _ _ _)
    (fun _ => A.measure_branch_isCPMap) b

/-- Every branch of the semi-classical multi-round run is completely
positive. -/
theorem runSCMR_branch_isCPMap (A : QAdvMR m n w q k c a) (H : Fin m → Fin n)
    (f : Fin c → Fin a) (S : Finset (Fin m)) (p : Bool × Bool) :
    IsCPMap ((runSCMR A H f S).branch p) :=
  qbind_branch_isCPMap _ _
    (mrChainSC_branch_isCPMap _ (scOracleQ_branch_isCPMap m n w H S) f k q _ _ _)
    (fun fl => qbind_branch_isCPMap _ _ A.measure_branch_isCPMap
      fun out => qpure_branch_isCPMap (out, fl)) p

/-- Every branch of the multi-round run cut after flat index `j` and followed
by the measurement `{Π_S, 1 - Π_S}` is completely positive. -/
theorem prefixRunMR_branch_isCPMap (A : QAdvMR m n w q k c a) (H : Fin m → Fin n)
    (f : Fin c → Fin a) (S : Finset (Fin m)) (j : Fin (flatQ q k q)) (b : Bool) :
    IsCPMap ((QComp.qbind
      (mrPrefixU (oracleQ m n w H) f k q (A.seg 0) (Fin.tail A.seg) A.rounds j)
      fun _ => measProj (projS m n w S) (projS_conjTranspose m n w S)
        (projS_mul_self m n w S)).branch b) :=
  qbind_branch_isCPMap _ _
    (mrPrefixU_branch_isCPMap _ (oracleQ_branch_isCPMap m n w H) f k q _ _ _ j)
    (fun _ => measProj_branch_isCPMap _ _ _) b

/-- The standard multi-round run as a completely positive instrument. -/
def cpRunMR (A : QAdvMR m n w q k c a) (H : Fin m → Fin n) (f : Fin c → Fin a) :
    CPComp (m * n * w) Bool :=
  CPComp.mk' (runMR A H f) (runMR_branch_isCPMap A H f)

/-- The semi-classical multi-round run as a completely positive instrument. -/
def cpRunSCMR (A : QAdvMR m n w q k c a) (H : Fin m → Fin n) (f : Fin c → Fin a)
    (S : Finset (Fin m)) : CPComp (m * n * w) (Bool × Bool) :=
  CPComp.mk' (runSCMR A H f S) (runSCMR_branch_isCPMap A H f S)

/-- The cut multi-round run followed by `{Π_S, 1 - Π_S}` as a completely
positive instrument. -/
def cpPrefixRunMR (A : QAdvMR m n w q k c a) (H : Fin m → Fin n) (f : Fin c → Fin a)
    (S : Finset (Fin m)) (j : Fin (flatQ q k q)) : CPComp (m * n * w) Bool :=
  CPComp.mk' (QComp.qbind
    (mrPrefixU (oracleQ m n w H) f k q (A.seg 0) (Fin.tail A.seg) A.rounds j)
    fun _ => measProj (projS m n w S) (projS_conjTranspose m n w S) (projS_mul_self m n w S))
    (prefixRunMR_branch_isCPMap A H f S j)

@[simp]
theorem toQComp_cpRunMR (A : QAdvMR m n w q k c a) (H : Fin m → Fin n) (f : Fin c → Fin a) :
    (cpRunMR A H f).toQComp = runMR A H f :=
  CPComp.toQComp_mk' _ _

@[simp]
theorem toQComp_cpRunSCMR (A : QAdvMR m n w q k c a) (H : Fin m → Fin n)
    (f : Fin c → Fin a) (S : Finset (Fin m)) :
    (cpRunSCMR A H f S).toQComp = runSCMR A H f S :=
  CPComp.toQComp_mk' _ _

/-- `prOutMR` is the acceptance probability of `cpRunMR`. -/
theorem prOutMR_eq_prTrue (A : QAdvMR m n w q k c a) (H : Fin m → Fin n)
    (f : Fin c → Fin a) : prOutMR A H f = (cpRunMR A H f).prTrue A.init := rfl

/-- `prFindMR` is the acceptance probability of the find bit of `cpRunSCMR`. -/
theorem prFindMR_eq_prTrue (A : QAdvMR m n w q k c a) (H : Fin m → Fin n)
    (f : Fin c → Fin a) (S : Finset (Fin m)) :
    prFindMR A H f S = (cpRunSCMR A H f S >>= fun p => pure p.2).prTrue A.init := by
  simp only [CPComp.prTrue_def, CPComp.toQComp_bind, CPComp.toQComp_pure, toQComp_cpRunSCMR]
  rfl

/-- `prOutPrefixMR` is the acceptance probability of `cpPrefixRunMR`. -/
theorem prOutPrefixMR_eq_prTrue (A : QAdvMR m n w q k c a) (H : Fin m → Fin n)
    (f : Fin c → Fin a) (S : Finset (Fin m)) (j : Fin (flatQ q k q)) :
    prOutPrefixMR A H f S j = (cpPrefixRunMR A H f S j).prTrue A.init := rfl

end MR

/-! ## The KEM game -/

section KEM

open CatCrypt.Crypto.PKE.Games (Scheme)

variable {m₁ m₂ n w q k c a : ℕ} {PK SK M C R K Hash Z : Type} [Fintype PK] [Fintype SK]
  [Fintype M] [Fintype Z] [Fintype K] [Nonempty K] [DecidableEq C] (P : Scheme PK SK M C R) (hpk : PK → Hash) (eG : (M × Hash) ≃ Fin m₁)
  (eJ : (Z × C) ≃ Fin m₂) (eKR : (K × R) ≃ Fin n) (eC : C ≃ Fin c) (eKa : K ≃ Fin a)
  [NeZero n]

/-- The KEM IND-CCA winning probability is the `kemSample`-weighted sum of the
acceptance probabilities of the completely positive multi-round runs. -/
theorem prWinKEM_eq_sum_prTrue (A : KEMQAdv m₁ m₂ n w q k c a PK C K) (b : Bool) :
    prWinKEM P hpk eG eJ eKR eC eKa A b =
      ∑ i : KEMInput PK SK Z M K m₁ m₂ n, kemSample P i *
        (cpRunMR (A.run i.1.1 (kemChal P hpk eG eKR i) (kemKey hpk eG eKR i b)) (kemOracle i)
          (kemDecaps P hpk eG eJ eKR eC eKa i)).prTrue
          (A.run i.1.1 (kemChal P hpk eG eKR i) (kemKey hpk eG eKR i b)).init := rfl

end KEM

end CatCrypt.Quantum.QROM

end
