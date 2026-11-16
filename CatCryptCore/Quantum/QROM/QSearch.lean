/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.PolyOracle
public import CatCryptCore.Quantum.QROM.FiatShamirSigma

/-!
# Quantum adversaries against classical decision and search games

A quantum algorithm without oracle access (`QStdDist`) attacks a classical game whose instance
is sampled from an `SDistr`.

* `qDistAdv D₀ D₁ E` — the advantage of the distinguisher `E` between the sample
  distributions `D₀` and `D₁`; `qMLWE` is its value at `mlweSample`
* `SearchGame` — an instance distribution and a winning relation
* `qSearchAdv G B out` — the probability that the algorithm `B`, followed by the measurement
  of the answer `out k` of the basis state `k` of its register, wins `G`
-/

@[expose] public section

set_option autoImplicit false

open scoped ENNReal

namespace CatCrypt.Quantum.QROM

open CatCrypt.Quantum CatCrypt.Prob

variable {m n w : ℕ} [NeZero n]

/-- The advantage of a quantum distinguisher without oracle access between two sample
distributions: `|Pr[1 | D₀] - Pr[1 | D₁]|`. -/
noncomputable def qDistAdv {X ι : Type} [Fintype ι] (D₀ D₁ : SDistr X)
    (E : QStdDist ι X m n w) : ℝ≥0∞ :=
  absDiff (sdExp D₀ (qStdAcc E)) (sdExp D₁ (qStdAcc E))

/-- A classical search game: an instance distribution and a winning relation. -/
structure SearchGame (X Y : Type) where
  /-- The distribution of instances. -/
  gen : SDistr X
  /-- The winning relation between an instance and an answer. -/
  win : X → Y → Bool

/-- The success probability of a quantum algorithm without oracle access that measures an
answer from its register: on the instance `x` and coins `i`, the algorithm `B x i` is run and
the basis state `k` of its register is read as the answer `out k`; the algorithm wins when
`G.win x (out k)` holds. The coins are uniform. -/
noncomputable def qSearchAdv {X Y ι : Type} [Fintype ι] (G : SearchGame X Y)
    (B : X → ι → QAdv m n w 0) (out : Fin (m * n * w) → Y) : ℝ≥0∞ :=
  sdExp G.gen fun x =>
    ∑ i : ι, (Fintype.card ι : ℝ≥0∞)⁻¹ *
      prOut0
        { U := (B x i).U
          init := (B x i).init
          final := diagB fun k => G.win x (out k)
          final_conjTranspose := diagB_conjTranspose _
          final_mul_self := diagB_mul_self _ }

end CatCrypt.Quantum.QROM
