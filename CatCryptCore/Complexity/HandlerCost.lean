/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Deep.Package
public import CatCryptCore.Quantum.QROM.FindToGuessGeneral

/-!
# Handler costs of circuits and packages

A circuit-valued or package-valued adversary is priced as a program run by a handler: one
unit (or a stated weight) per gate, and per oracle call one unit plus the cost of the handler
that answers the call. Replacing the oracle by a handler program substitutes the handler's
cost for each call.

## Circuits of the quantum layer

The quantum adversary `QAdv m n w q` of the QROM files is the chain
`U₀ ; O ; U₁ ; ⋯ ; O ; U_q` of unitary matrices between `q` oracle calls. Its costed mirror
`QAdv.Timed S q` over a gate set `S` (gates with a unitary denotation and a weight) replaces
each unitary `U_j` by a word of gates; `QAdv.Timed.Erases A' A` states that the word `j`
multiplies out to `U_j` and that the initial state and the final projector agree. The time of
a run with handler cost `h` is `QAdv.Timed.time A' h = Σ_j cost (gates j) + q * (1 + h)`.

Absorbing the oracle into the chain (`absorbOracle`) is the substitution of a handler word
`v` implementing the oracle unitary for each call: the mirror `QAdv.Timed.absorb A' v` makes no
call and has time `Σ_j cost (gates j) + q * cost v` (`time_absorb`).

## Packages

`RawCode.TimeLE h c n` states that the code `c` of a package runs in at most `n` units when a
call to the import `op` is priced `1 + h op`: one unit for each `sample`, `get` and `put`,
nothing for `ret` and `fail`, and times add under `bind`. Code containing `embed` has no
derivable bound, since an embedded `SPComp` has no syntax to price. `DeepPackage.TimeBound p h
T` bounds the code of every export. Linking `p₁` with `p₂` substitutes the code of `p₂` for the
calls of `p₁`: if every export of `p₂` runs within `h op` under the handler cost `h₂`, the
linked package keeps the bound `T` under `h₂` (`DeepPackage.timeBound_link`).

## Rule for `derive_timed_structure`

A field `f : X₁ → ⋯ → Xₖ → QAdv m n w q` is mirrored as
`f : X₁ → ⋯ → Xₖ → QAdv.Timed S q` with the cost companion `fCost : X₁ → ⋯ → Xₖ → ℕ` (the
classical cost of computing the circuit from the arguments), the gate set `S` becoming a
parameter of the mirror and the handler cost `h` a parameter of `TimeBound`. Its erasure is
`QAdv.Timed.Erases (A'.f ys) (A.f ys)` and its time bound is
`A'.fCost ys + (A'.f ys).time h ≤ T_f` at every `ys`.

A field `f : X₁ → ⋯ → Xₖ → DeepPackage` is kept as data, with a handler cost
`h_f : ℕ → ℕ` as a parameter of `TimeBound`, whose conjunct is
`DeepPackage.TimeBound (A'.f ys) h_f T_f` at every `ys`. A field of code type `RawCode β` is
bounded by `RawCode.TimeLE h_f (A'.f ys) T_f`.

`derive_timed_structure` recognises these kinds by name: a field whose result type has head
`H` is of circuit kind when `H.handlerGateSet` exists (with `H.handlerMirror`,
`H.handlerErases` and `H.handlerTime`), and of bounded kind when `H.handlerBound` exists. The
registrations of `QAdv`, `DeepPackage` and `RawCode` are the last section of this file.

## Main definitions

* `GateSet d` — gates with a unitary denotation on `Fin d` and a weight
* `GateSet.eval`, `GateSet.cost` — the unitary and the cost of a word of gates
* `QAdv.Timed S q`, `QAdv.Timed.Erases`, `QAdv.Timed.time` — costed circuit adversaries
* `QAdv.Timed.absorb` — the costed form of `absorbOracle`
* `RawCode.TimeLE h c n` — the time of package code under a handler cost
* `DeepPackage.TimeBound p h T` — the time of every export of a package
* `QAdv.handlerGateSet`, `QAdv.handlerMirror`, `QAdv.handlerErases`, `QAdv.handlerTime`,
  `DeepPackage.handlerBound`, `RawCode.handlerBound` — the handler kinds read by
  `derive_timed_structure`

## Main results

* `GateSet.eval_append`, `GateSet.cost_append` — sequential composition multiplies the
  unitaries and adds the costs
* `QAdv.Timed.erases_absorb`, `QAdv.Timed.time_absorb`, `QAdv.Timed.time_absorb_le` — oracle
  absorption: erasure, and time `Σ_j cost (gates j) + q * cost v`
* `RawCode.TimeLE.bind'`, `RawCode.TimeLE.mono` — times add under `bind`
* `RawCode.TimeLE.substOracle` — handler substitution replaces each call by its handler
* `DeepPackage.timeBound_link` — the time of a linked package
-/

@[expose] public section

set_option autoImplicit false

noncomputable section

namespace CatCrypt.Complexity.HandlerCost

open CatCrypt.Quantum CatCrypt.Quantum.QROM

/-! ## Gate sets and words -/

/-- A gate set on the register `Fin d`: gates, the unitary of each gate and its weight. -/
structure GateSet (d : ℕ) where
  /-- The gates. -/
  G : Type
  /-- The unitary of a gate. -/
  den : G → Matrix.unitaryGroup (Fin d) ℂ
  /-- The cost of a gate. -/
  weight : G → ℕ

namespace GateSet

variable {d : ℕ} (S : GateSet d)

/-- The unitary of a word of gates, in matrix-product order: the last gate of the word acts
first. -/
def eval (l : List S.G) : Matrix.unitaryGroup (Fin d) ℂ := (l.map S.den).prod

/-- The cost of a word of gates: the sum of the weights. -/
def cost (l : List S.G) : ℕ := (l.map S.weight).sum

/-- Sequential composition multiplies the unitaries. -/
theorem eval_append (l₁ l₂ : List S.G) : S.eval (l₁ ++ l₂) = S.eval l₁ * S.eval l₂ := by
  simp [eval, List.map_append, List.prod_append]

/-- Sequential composition adds the costs. -/
theorem cost_append (l₁ l₂ : List S.G) : S.cost (l₁ ++ l₂) = S.cost l₁ + S.cost l₂ := by
  simp [cost, List.map_append, List.sum_append]

end GateSet

/-! ## Costed circuit adversaries -/

/-- The words of the chain of a `q`-query adversary with each oracle call replaced by the
handler word `v`: `W_q v W_{q-1} ⋯ v W_0` in matrix-product order. -/
def absorbWord {G : Type} (v : List G) : (q : ℕ) → (Fin (q + 1) → List G) → List G
  | 0, W => W 0
  | q + 1, W => absorbWord v q (Fin.tail W) ++ v ++ W 0

section QAdvTimed

variable {m n w : ℕ}

/-- The costed mirror of `QAdv m n w q` over the gate set `S`: a word of gates for each
unitary of the chain, the initial state and the final projector. -/
structure QAdv.Timed (S : GateSet (m * n * w)) (q : ℕ) where
  /-- The word of gates of the unitary `U_j`. -/
  gates : Fin (q + 1) → List S.G
  /-- The initial state. -/
  init : DensityMatrix (m * n * w)
  /-- The projector of the final measurement. -/
  final : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ

namespace QAdv.Timed

variable {S : GateSet (m * n * w)} {q : ℕ}

/-- `A'` erases to `A`: each word multiplies out to the unitary of `A`, and the initial state
and the final projector agree. -/
def Erases (A' : QAdv.Timed S q) (A : QAdv m n w q) : Prop :=
  (∀ j, S.eval (A'.gates j) = A.U j) ∧ A'.init = A.init ∧ A'.final = A.final

/-- The cost of the gates of the chain. -/
def gateTime (A' : QAdv.Timed S q) : ℕ := ∑ j, S.cost (A'.gates j)

/-- The time of a run in which each oracle call costs one unit plus the handler cost `h`. -/
def time (A' : QAdv.Timed S q) (h : ℕ) : ℕ := A'.gateTime + q * (1 + h)

/-- The costed form of `absorbOracle`: the handler word `v` in place of each oracle call. -/
def absorb (A' : QAdv.Timed S q) (v : List S.G) : QAdv.Timed S 0 where
  gates _ := absorbWord v q A'.gates
  init := A'.init
  final := A'.final

/-- The absorbed word multiplies out to `absorbU` when each word multiplies out to its
unitary and the handler word to the oracle unitary. -/
theorem eval_absorbWord [NeZero n] (G : Fin m → Fin n) (v : List S.G)
    (hv : S.eval v = oracleU m n w G) (q : ℕ) (W : Fin (q + 1) → List S.G)
    (U : Fin (q + 1) → Matrix.unitaryGroup (Fin (m * n * w)) ℂ)
    (hW : ∀ j, S.eval (W j) = U j) :
    S.eval (absorbWord v q W) = absorbU G q U := by
  induction q with
  | zero => simpa only [absorbWord, absorbU] using hW 0
  | succ q ih =>
    rw [absorbWord, absorbU, S.eval_append, S.eval_append,
      ih (Fin.tail W) (Fin.tail U) (fun j => hW j.succ), hv, hW 0]

/-- The cost of the absorbed word: the words of the chain and the handler word per call. -/
theorem cost_absorbWord (v : List S.G) (q : ℕ) (W : Fin (q + 1) → List S.G) :
    S.cost (absorbWord v q W) = (∑ j, S.cost (W j)) + q * S.cost v := by
  induction q with
  | zero => simp [absorbWord]
  | succ q ih =>
    simp only [absorbWord, S.cost_append, ih, Fin.sum_univ_succ (n := q + 1), Fin.tail]
    ring

/-- Absorption commutes with erasure, when the handler word implements the oracle unitary. -/
theorem erases_absorb [NeZero n] {A' : QAdv.Timed S q} {A : QAdv m n w q}
    (hA : A'.Erases A) (G : Fin m → Fin n) {v : List S.G} (hv : S.eval v = oracleU m n w G) :
    (A'.absorb v).Erases (absorbOracle A G) :=
  ⟨fun _ => eval_absorbWord G v hv q A'.gates A.U hA.1, hA.2.1, hA.2.2⟩

/-- **Handler substitution.** The absorbed circuit makes no call; its time is the gate time of
the chain plus the cost of the handler word per call. -/
theorem time_absorb (A' : QAdv.Timed S q) (v : List S.G) (h : ℕ) :
    (A'.absorb v).time h = A'.gateTime + q * S.cost v := by
  simp [time, gateTime, absorb, cost_absorbWord]

/-- A handler word of cost at most `1 + h` keeps the time of a run with handler cost `h`. -/
theorem time_absorb_le (A' : QAdv.Timed S q) {v : List S.G} {h : ℕ} (hv : S.cost v ≤ 1 + h)
    (h' : ℕ) : (A'.absorb v).time h' ≤ A'.time h := by
  rw [time_absorb, time]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left q hv) _

end QAdv.Timed

end QAdvTimed

end CatCrypt.Complexity.HandlerCost

/-! ## Package code -/

namespace CatCrypt.Deep

universe u

/-- `TimeLE h c n`: the code `c` runs in at most `n` units when a call to `op` costs
`1 + h op`, each `sample`, `get` and `put` one unit, and `ret` and `fail` nothing. -/
inductive RawCode.TimeLE (h : ℕ → ℕ) : {α : Type u} → RawCode α → ℕ → Prop where
  | ret {α : Type u} (a : α) (n : ℕ) : RawCode.TimeLE h (.ret a) n
  | bind {α β : Type u} {c : RawCode α} {k : α → RawCode β} {m n : ℕ}
      (hc : RawCode.TimeLE h c m) (hk : ∀ a, RawCode.TimeLE h (k a) n) :
      RawCode.TimeLE h (.bind c k) (m + n)
  | sample (T : Type u) [Fintype T] [Nonempty T] {n : ℕ} (hn : 1 ≤ n) :
      RawCode.TimeLE h (.sample T) n
  | get (ℓ : CatCrypt.Core.Location) {n : ℕ} (hn : 1 ≤ n) : RawCode.TimeLE h (.get ℓ) n
  | put (ℓ : CatCrypt.Core.Location) (v : ℓ.ty) {n : ℕ} (hn : 1 ≤ n) :
      RawCode.TimeLE h (.put ℓ v) n
  | fail {α : Type u} (n : ℕ) : RawCode.TimeLE h (@RawCode.fail α) n
  | oracleCall (op : ℕ) (dom codom : Type u) (x : dom) {n : ℕ} (hn : 1 + h op ≤ n) :
      RawCode.TimeLE h (.oracleCall op dom codom x) n

namespace RawCode.TimeLE

variable {h : ℕ → ℕ}

/-- A time bound holds at every larger time. -/
theorem mono {α : Type u} {c : RawCode α} {m n : ℕ} (hc : RawCode.TimeLE h c m) (hmn : m ≤ n) :
    RawCode.TimeLE h c n := by
  induction hc generalizing n with
  | ret a _ => exact .ret a n
  | @bind _ _ _ _ m₁ n₁ hc hk ihc _ =>
    have e : n - n₁ + n₁ = n := Nat.sub_add_cancel (by omega)
    exact e ▸ .bind (ihc (by omega)) hk
  | sample T hn => exact .sample T (by omega)
  | get ℓ hn => exact .get ℓ (by omega)
  | put ℓ v hn => exact .put ℓ v (by omega)
  | fail _ => exact .fail n
  | oracleCall op dom codom x hn => exact .oracleCall op dom codom x (by omega)

/-- Times add under sequencing. -/
theorem bind' {α β : Type u} {c : RawCode α} {k : α → RawCode β} {m n T : ℕ}
    (hc : RawCode.TimeLE h c m) (hk : ∀ a, RawCode.TimeLE h (k a) n) (hT : m + n ≤ T) :
    RawCode.TimeLE h (.bind c k) T :=
  (bind hc hk).mono hT

/-- **Handler substitution.** If every call to `op` is answered by code of time at most `h op`
under the handler cost `h'`, then substituting the answers keeps the bound. -/
theorem substOracle {h' : ℕ → ℕ} {α : Type u} {c : RawCode α} {n : ℕ}
    (hc : RawCode.TimeLE h c n) (env : ℕ → ∀ (dom codom : Type u), dom → RawCode codom)
    (henv : ∀ op dom codom x, RawCode.TimeLE h' (env op dom codom x) (h op)) :
    RawCode.TimeLE h' (c.substOracle env) n := by
  induction hc with
  | ret a n => exact .ret a n
  | bind _ _ ihc ihk => exact .bind ihc ihk
  | sample T hn => exact .sample T hn
  | get ℓ hn => exact .get ℓ hn
  | put ℓ v hn => exact .put ℓ v hn
  | fail n => exact .fail n
  | oracleCall op dom codom x hn => exact (henv op dom codom x).mono (by omega)

end RawCode.TimeLE

/-- Every export of `p` runs in at most `T` units under the handler cost `h`. -/
def DeepPackage.TimeBound (p : DeepPackage.{u}) (h : ℕ → ℕ) (T : ℕ) : Prop :=
  ∀ op dom codom (hmem : (op, dom, codom) ∈ p.exports.ops) (x : dom),
    RawCode.TimeLE h (p.impl op dom codom hmem x).code T

/-- **Time of a linked package.** If `p₁` runs within `T` when a call to `op` costs `1 + h op`,
and every export `op` of `p₂` runs within `h op` under `h₂`, then `link p₁ p₂` runs within `T`
under `h₂`. -/
theorem DeepPackage.timeBound_link {p₁ p₂ : DeepPackage.{u}} {h h₂ : ℕ → ℕ} {T : ℕ}
    (h₁ : p₁.TimeBound h T)
    (hp₂ : ∀ op dom codom (hmem : (op, dom, codom) ∈ p₂.exports.ops) (x : dom),
      RawCode.TimeLE h₂ (p₂.impl op dom codom hmem x).code (h op)) :
    (DeepPackage.link p₁ p₂).TimeBound h₂ T := by
  intro op dom codom hmem x
  refine (h₁ op dom codom hmem x).substOracle _ fun op' dom' codom' x' => ?_
  dsimp only
  by_cases hm : (op', dom', codom') ∈ p₂.exports.ops
  · rw [dif_pos hm]; exact hp₂ op' dom' codom' hm x'
  · rw [dif_neg hm]; exact .fail _

end CatCrypt.Deep

/-! ### Handler kinds for `derive_timed_structure` -/

namespace CatCrypt.Quantum.QROM

open CatCrypt.Complexity.HandlerCost

/-- The gate set of the costed mirror of a circuit `QAdv m n w q`. -/
@[reducible] def QAdv.handlerGateSet (m n w _q : ℕ) : Type 1 := GateSet (m * n * w)

/-- The costed mirror of a circuit `QAdv m n w q` over the gate set `S`. -/
@[reducible] def QAdv.handlerMirror (m n w q : ℕ) (S : QAdv.handlerGateSet m n w q) : Type :=
  QAdv.Timed S q

/-- The erasure of a costed circuit. -/
@[reducible] def QAdv.handlerErases {m n w q : ℕ} {S : GateSet (m * n * w)}
    (A' : QAdv.Timed S q) (A : QAdv m n w q) : Prop :=
  A'.Erases A

/-- The time of a run of a costed circuit under the handler cost `h` per oracle call. -/
@[reducible] def QAdv.handlerTime {m n w q : ℕ} {S : GateSet (m * n * w)}
    (A' : QAdv.Timed S q) (h : ℕ) : ℕ :=
  A'.time h

end CatCrypt.Quantum.QROM

namespace CatCrypt.Deep

universe u

/-- The time bound of a package under the handler cost `h`. -/
@[reducible] def DeepPackage.handlerBound (p : DeepPackage.{u}) (h : ℕ → ℕ) (T : ℕ) : Prop :=
  p.TimeBound h T

/-- The time bound of package code under the handler cost `h`. -/
@[reducible] def RawCode.handlerBound {β : Type u} (c : RawCode β) (h : ℕ → ℕ) (T : ℕ) :
    Prop :=
  RawCode.TimeLE h c T

end CatCrypt.Deep
