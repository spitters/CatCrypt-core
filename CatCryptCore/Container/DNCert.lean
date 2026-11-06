/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.ForMathlib.PFunctorChargeVec
public import CatCryptCore.Container.DillerNahm
public import CatCryptCore.Crypto.OracleProfile
public import CatCryptCore.Core.SPTreeTimedFree
public import CatCryptCore.Crypto.OracleAdversaryFree
public import CatCryptCore.Crypto.Signatures.OracleProgTimedFree

/-!
# Use bounds of tick trees as Diller–Nahm morphisms

A program calling resources `ι` (a clock tick, adversaries, oracles, certified callees) has a use
bound `u : ι → ℕ∞`: the vector charge fold of its tree, at a charge counting each operation in
the resource it uses, is at most `u`. Read as a morphism of the Diller–Nahm category (Moss and
von Glehn, *Dialectica models of type theory*, LICS 2018, §8), a data token of the program
demands `u i` tokens of resource `i`. Interpreting the calls of a program through a handler whose
call of resource `i` has use bound `d i` gives the use bound `∑ i, u i • d i`, which is the
multiset bind of the two demands (`demandLens_comp`), and at the two resources `{call, tick}` the
composition law `n = n₂ * n₁`, `c = c₂ + n₂ * c₁` of `Clocked.toDN_comp`.

An open tick tree over `P + C` has the operations `P` of a costed tree and calls `C` of resources
`κ`. The costed tree of a program at concrete resources is the open tree interpreted by the call
handler `callHandler impl`; its time is at most the tick component of the use bound plus the use
count of each resource times the time of its implementation.

## Main definitions

* `CatCrypt.Container.UseBound` — the vector charge fold bound of a tree
* `CatCrypt.Container.callHandler` — the handler keeping `P` and running the implementation of
  each call
* `CatCrypt.Container.openCharge`, `CatCrypt.Container.openAllows` — the vector charge and the
  allowed answers of an open tick tree, with the tick at `none` and resource `i` at `some i`
* `CatCrypt.Container.Clocked.useVec`, `CatCrypt.Container.Clocked.callDemand` — the use vector of
  a costed function with use counts, and the demand of a call implemented by it
* `CatCrypt.Container.Clocked.time` — the time of one use of the output when one use of the
  input takes time `T`: `cost + uses * T`

## Main results

* `CatCrypt.Container.useBound_liftM` — the composition rule: use bounds compose by
  `∑ i, u i • d i`
* `CatCrypt.Container.useBound_liftM_eq_demandLens` — the composite bound at natural-number
  vectors is the count of the composite of the demand lenses
* `CatCrypt.Container.useBound_liftM_clocked`, `CatCrypt.Container.Clocked.useVec_comp_eq_count`
  — the composition rule at `{call, tick}` is `Clocked.comp`, whose counts are those of the
  composite Diller–Nahm morphism
* `CatCrypt.Container.Clocked.time_eq_price`, `CatCrypt.Container.Clocked.time_comp` — the time is
  the price of a data token of the Diller–Nahm morphism, and the time of a composite is the time
  of the consumer at the time of the producer (`DNLens.price_comp`); the rewinding extractors
  (`ForkingLemma.forkAlg.clock`, `FiatShamirROM.ksExtractor.clock`) are priced this way
* `CatCrypt.Container.wpFold_liftM_callHandler_le` — the price of a use bound bounds the charge
  fold of the interpreted open tree
* `SPTree.Timed.timeBound_of_useBound`, `OracleAdv.Timed.timeBound_of_useBound`,
  `OracleProg.Timed.timeBound_of_useBound` and their step forms — a use bound of an open tree
  whose interpretation is the tick tree of a costed tree gives its time bound
-/

@[expose] public section

set_option autoImplicit false

universe uA uA₂ uB

open PFunctor PFunctor.FreeM
open scoped BigOperators

namespace CatCrypt.Container

/-! ## Use bounds -/

section UseBound

variable {P : PFunctor.{uA, uB}} {ι : Type*} {α : Type uB}

/-- The use bound `u` of a tree at the vector charge `c`: over the answers allowed by `allows`,
the charge fold of `x` is at most `u` in each resource. -/
def UseBound (c : P.A → ι → ℕ∞) (allows : (a : P.A) → P.B a → Prop) (x : FreeM P α)
    (u : ι → ℕ∞) : Prop :=
  wpFold (OpSpec.chargeUnder c allows) x (fun _ => 0) ≤ u

/-- A use bound is the family of its component bounds, each a scalar charge fold bound. -/
theorem useBound_iff (c : P.A → ι → ℕ∞) (allows : (a : P.A) → P.B a → Prop) (x : FreeM P α)
    (u : ι → ℕ∞) :
    UseBound c allows x u ↔
      ∀ i, wpFold (OpSpec.chargeUnder (fun a => c a i) allows) x (fun _ => 0) ≤ u i :=
  FreeM.wpFold_chargeUnder_pi_le_iff c allows x _ u

/-- A natural-number use bound `u : ι →₀ ℕ` enters by casting each component. -/
theorem useBound_natCast_iff (c : P.A → ι → ℕ∞) (allows : (a : P.A) → P.B a → Prop)
    (x : FreeM P α) (u : ι →₀ ℕ) :
    UseBound c allows x (fun i => (u i : ℕ∞)) ↔
      ∀ i, wpFold (OpSpec.chargeUnder (fun a => c a i) allows) x (fun _ => 0) ≤ u i :=
  useBound_iff c allows x _

/-- A use bound is monotone in the bound. -/
theorem UseBound.mono {c : P.A → ι → ℕ∞} {allows : (a : P.A) → P.B a → Prop} {x : FreeM P α}
    {u v : ι → ℕ∞} (h : UseBound c allows x u) (huv : u ≤ v) : UseBound c allows x v :=
  le_trans h huv

end UseBound

/-! ## Monotonicity of the charge fold in the charge -/

section Mono

variable {P : PFunctor.{uA, uB}}

/-- The charge fold is monotone in the charge. -/
theorem wpFold_chargeUnder_le_of_le {X : Type*} {c c' : P.A → ℕ∞} (hc : ∀ a, c a ≤ c' a)
    (allows : (a : P.A) → P.B a → Prop) (x : FreeM P X) (post : X → ℕ∞) :
    wpFold (OpSpec.chargeUnder c allows) x post ≤ wpFold (OpSpec.chargeUnder c' allows) x post := by
  induction x with
  | pure r => exact le_rfl
  | lift_bind a r ih =>
    change c a + ⨆ b, ⨆ (_ : allows a b), wpFold (OpSpec.chargeUnder c allows) (r b) post ≤
      c' a + ⨆ b, ⨆ (_ : allows a b), wpFold (OpSpec.chargeUnder c' allows) (r b) post
    exact add_le_add (hc a) (iSup₂_mono fun b _ => ih b)

/-- Every tree satisfies the trivial postcondition under the demonic fold. -/
theorem wpFold_demonicUnder_true {X : Type*} (allows : (a : P.A) → P.B a → Prop)
    (x : FreeM P X) : wpFold (OpSpec.demonicUnder allows) x (fun _ => True) := by
  induction x with
  | pure r => trivial
  | lift_bind a r ih => exact fun b _ => ih b

end Mono

/-! ## The composition rule -/

section Composition

variable {P : PFunctor.{uA, uB}} {Q : PFunctor.{uA₂, uB}} {ι ι' : Type*} {α : Type uB}

/-- **The composition rule.** If `x` has use bound `u` over `ι` read under `allowsP`, and the
handler at `a` has use bound `∑ i, c a i • d i` over `ι'`, where `d i` is the use vector of one
call of resource `i`, then `x.liftM h` has use bound `∑ i, u i • d i`. Every return of the handler
allowed by `allows` must satisfy `allowsP`. -/
theorem useBound_liftM [Fintype ι] {c : P.A → ι → ℕ∞} {allowsP : (a : P.A) → P.B a → Prop}
    {c' : Q.A → ι' → ℕ∞} {allows : (a : Q.A) → Q.B a → Prop} {x : FreeM P α} {u : ι → ℕ∞}
    {h : (a : P.A) → FreeM Q (P.B a)} {d : ι → ι' → ℕ∞} (hx : UseBound c allowsP x u)
    (hh : ∀ a, UseBound c' allows (h a) (∑ i, c a i • d i))
    (hdem : ∀ a, wpFold (OpSpec.demonicUnder allows) (h a) (allowsP a)) :
    UseBound c' allows (x.liftM h) (∑ i, u i • d i) := by
  rw [useBound_iff]
  intro j
  have hcj : ∀ a, wpFold (OpSpec.chargeUnder (fun q => c' q j) allows) (h a) (fun _ => 0) ≤
      ∑ i, d i j * c a i := by
    intro a
    have := (useBound_iff _ _ _ _).1 (hh a) j
    simpa [Finset.sum_apply, mul_comm] using this
  calc wpFold (OpSpec.chargeUnder (fun q => c' q j) allows) (x.liftM h) (fun _ => 0)
      ≤ wpFold (OpSpec.chargeUnder (fun a => wpFold (OpSpec.chargeUnder (fun q => c' q j) allows)
          (h a) fun _ => 0) allowsP) x (fun _ => 0) :=
        FreeM.wpFold_chargeUnder_liftM_le _ allows allowsP h hdem x
    _ ≤ wpFold (OpSpec.chargeUnder (fun a => ∑ i, d i j * c a i) allowsP) x (fun _ => 0) :=
        wpFold_chargeUnder_le_of_le hcj allowsP x _
    _ ≤ ∑ i, d i j * u i := FreeM.wpFold_chargeUnder_price_le c allowsP (fun i => d i j) hx
    _ = (∑ i, u i • d i) j := by simp [Finset.sum_apply, mul_comm]

/-- The composite use bound at natural-number vectors `u` and `d i` is the count of the
composite of the demand lenses: the demand of `u` followed by the demand `d i` of each resource
`i` is the multiset bind `(toMultiset u).bind (toMultiset ∘ d)`. -/
theorem useBound_liftM_eq_demandLens {ι₀ ι₀' : Type} [Fintype ι₀] [DecidableEq ι₀']
    (u : ι₀ →₀ ℕ) (d : ι₀ → ι₀' →₀ ℕ) (j : ι₀') :
    (∑ i, (u i : ℕ∞) • fun j => (d i j : ℕ∞)) j =
      ((((Crypto.OracleAdv.demandLens fun _ : PUnit.{1} => Finsupp.toMultiset u).comp
        (Crypto.OracleAdv.demandLens (Finsupp.toMultiset ∘ d))).toFunB PUnit.unit
          PUnit.unit).count j : ℕ∞) := by
  classical
  rw [Crypto.OracleAdv.demandLens_comp]
  simp only [Crypto.OracleAdv.demandLens, Multiset.count_bind, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul, Function.comp_apply, Finsupp.count_toMultiset]
  rw [Finset.sum_multiset_map_count, Finsupp.toFinset_toMultiset]
  simp only [Finsupp.count_toMultiset, nsmul_eq_mul, Nat.cast_sum, Nat.cast_mul]
  exact (Finset.sum_subset (Finset.subset_univ _) fun i _ hi => by
    simp [Finsupp.notMem_support_iff.1 hi]).symm

/-! ### Two resources: the clocked case -/

namespace Clocked

variable {X : Type*} {Y : Type*} {Z : Type*}

/-- The use vector of a costed function with use counts at `a`: the uses at `false`, a data
token, and the cost at `true`, a clock tick. -/
def useVec (h : Clocked X Y) (a : X) : Bool → ℕ∞
  | false => h.uses a
  | true => h.cost a

/-- The demand of one call of a resource implemented by `f` at `a`: a call demands the use vector
of `f`, and a tick demands one tick. -/
def callDemand (f : Clocked X Y) (a : X) : Bool → Bool → ℕ∞
  | false => f.useVec a
  | true => Pi.single true 1

/-- The use vector is the count of the tokens demanded by a data token of the Diller–Nahm
morphism. -/
theorem useVec_eq_count (h : Clocked X Y) (a : X) (b : Bool) :
    h.useVec a b = (((toDN h).toFunB a false).count b : ℕ∞) := by
  cases b <;> simp [useVec, count_false_toDN, count_true_toDN]

/-- The composite of the use vectors is the use vector of `Clocked.comp`. -/
theorem sum_smul_callDemand (g : Clocked Y Z) (f : Clocked X Y) (a : X) :
    ∑ i, g.useVec (f.fn a) i • f.callDemand a i = (comp g f).useVec a := by
  funext b
  cases b <;> simp [useVec, callDemand, comp, mul_comm]

/-- The use vector of a composite is the count of the composite Diller–Nahm morphism. -/
theorem useVec_comp_eq_count (g : Clocked Y Z) (f : Clocked X Y) (a : X) (b : Bool) :
    (comp g f).useVec a b =
      (((DNLens.comp (toDN g) (toDN f)).toFunB a false).count b : ℕ∞) := by
  rw [useVec_eq_count, toDN_comp]

/-- The time of one use of the output of `h` at `a` when one use of the input takes time `T`:
the cost plus the uses times `T`. -/
def time (h : Clocked X Y) (T : ℕ) (a : X) : ℕ :=
  h.cost a + h.uses a * T

/-- The price of the tokens of `clockPos X` at which a data token costs `T` and a clock tick
costs one unit. -/
def timePrice (T : ℕ) : ∀ _ : X, Bool → ℕ :=
  fun _ b => bif b then 1 else T

/-- The time is the price of a data token of the Diller–Nahm morphism at `timePrice T`. -/
theorem time_eq_price (h : Clocked X Y) (T : ℕ) (a : X) :
    h.time T a = (toDN h).price (timePrice T) a false := by
  rw [price_toDN]
  simp only [time, timePrice, Bool.cond_false, Bool.cond_true, mul_one]
  omega

/-- A tick of the Diller–Nahm morphism costs one unit at `timePrice T`. -/
theorem price_toDN_true (h : Clocked X Y) (T : ℕ) (a : X) :
    (toDN h).price (timePrice T) a true = 1 := by
  simp [DNLens.price, toDN, clockBack, timePrice]

/-- **The time of a composite.** One use of the output of `comp g f` takes the time of `g` at
`f.fn a` when one use of its input takes the time of `f` at `a`: the price of the composite
Diller–Nahm morphism is the price under `g` of the price under `f` (`DNLens.price_comp`). -/
theorem time_comp (g : Clocked Y Z) (f : Clocked X Y) (T : ℕ) (a : X) :
    (comp g f).time T a = g.time (f.time T a) (f.fn a) := by
  have h1 := price_toDN_true f T a
  rw [time_eq_price, toDN_comp, DNLens.price_comp, time_eq_price f]
  change ((clockBack (g.uses (f.fn a)) (g.cost (f.fn a)) false).map _).sum = _
  simp [clockBack, time, Multiset.map_nsmul, Multiset.sum_nsmul, h1]
  omega

/-- The time is monotone in the time of a use of the input. -/
theorem time_mono (h : Clocked X Y) {T T' : ℕ} (hT : T ≤ T') (a : X) :
    h.time T a ≤ h.time T' a :=
  Nat.add_le_add_left (Nat.mul_le_mul_left _ hT) _

end Clocked

/-- **The composition rule at `{call, tick}`.** If `x` uses its resource `g.uses` times at cost
`g.cost` at `f.fn a`, and each operation of `x` is interpreted with the demand of `f` at `a` per
call, then `x.liftM h` has the use vector of `Clocked.comp g f` at `a`: uses `n₂ * n₁`, cost
`c₂ + n₂ * c₁`. -/
theorem useBound_liftM_clocked {X Y Z : Type*} {c : P.A → Bool → ℕ∞}
    {allowsP : (a : P.A) → P.B a → Prop} {c' : Q.A → Bool → ℕ∞}
    {allows : (a : Q.A) → Q.B a → Prop} {x : FreeM P α} {h : (a : P.A) → FreeM Q (P.B a)}
    (g : Clocked Y Z) (f : Clocked X Y) (a₀ : X)
    (hx : UseBound c allowsP x (g.useVec (f.fn a₀)))
    (hh : ∀ a, UseBound c' allows (h a) (∑ i, c a i • f.callDemand a₀ i))
    (hdem : ∀ a, wpFold (OpSpec.demonicUnder allows) (h a) (allowsP a)) :
    UseBound c' allows (x.liftM h) ((Clocked.comp g f).useVec a₀) := by
  rw [← Clocked.sum_smul_callDemand]
  exact useBound_liftM hx hh hdem

end Composition

/-! ## Open tick trees and the call handler -/

section Open

variable {P : PFunctor.{uA, uB}} {C : PFunctor.{uA, uB}} {κ : Type*} {α : Type uB}

/-- The call handler: an operation of `P` is kept, a call `c` runs its implementation
`impl c`. -/
def callHandler (impl : (c : C.A) → FreeM P (C.B c)) : Handler (FreeM P) (P + C) :=
  Handler.sum (Handler.id P) impl

/-- The vector charge of an open tick tree: an operation `a` of `P` charges `tc a` ticks, at
`none`, and a call `c` charges one use of its resource `ρ c`, at `some (ρ c)`. -/
def openCharge [DecidableEq κ] (tc : P.A → ℕ) (ρ : C.A → κ) :
    (P + C).A → Option κ → ℕ∞
  | .inl a => Pi.single none (tc a : ℕ∞)
  | .inr c => Pi.single (some (ρ c)) 1

/-- The allowed answers of an open tick tree: those of `allows` at an operation of `P`, every
answer at a call. -/
def openAllows (allows : (a : P.A) → P.B a → Prop) : (a : (P + C).A) → (P + C).B a → Prop
  | .inl a, b => allows a b
  | .inr _, _ => True

/-- **The price of a use bound.** If the open tree `x` has use bound `u`, and the implementation
of each call `c` has charge fold at most `T (ρ c)`, then the interpreted tree has charge fold at
most `u none + ∑ i, T i * u (some i)`. -/
theorem wpFold_liftM_callHandler_le [Fintype κ] [DecidableEq κ] (tc : P.A → ℕ) (ρ : C.A → κ)
    (allows : (a : P.A) → P.B a → Prop) {x : FreeM (P + C) α} {u : Option κ → ℕ∞}
    (hx : UseBound (openCharge tc ρ) (openAllows allows) x u)
    (impl : (c : C.A) → FreeM P (C.B c)) (T : κ → ℕ∞)
    (himpl : ∀ c, wpFold (OpSpec.chargeUnder (fun a => (tc a : ℕ∞)) allows) (impl c)
      (fun _ => 0) ≤ T (ρ c)) :
    wpFold (OpSpec.chargeUnder (fun a => (tc a : ℕ∞)) allows) (x.liftM (callHandler impl))
        (fun _ => 0) ≤ u none + ∑ i, T i * u (some i) := by
  let p : Option κ → ℕ∞ := fun j => j.elim 1 T
  have hdem : ∀ a, wpFold (OpSpec.demonicUnder allows) (callHandler impl a)
      (openAllows allows a) := by
    rintro (a | c)
    · exact fun b hb => hb
    · exact wpFold_demonicUnder_true allows _
  have hcost : ∀ a, wpFold (OpSpec.chargeUnder (fun a => (tc a : ℕ∞)) allows)
      (callHandler impl a) (fun _ => 0) ≤ ∑ j, p j * openCharge tc ρ a j := by
    rintro (a | c)
    · simp [callHandler, openCharge, Fintype.sum_option, p, Handler.id]
    · simpa [callHandler, openCharge, p, Pi.single_apply] using himpl c
  calc wpFold (OpSpec.chargeUnder (fun a => (tc a : ℕ∞)) allows) (x.liftM (callHandler impl))
        (fun _ => 0)
      ≤ wpFold (OpSpec.chargeUnder (fun a => wpFold (OpSpec.chargeUnder
          (fun a => (tc a : ℕ∞)) allows) (callHandler impl a) fun _ => 0) (openAllows allows))
          x (fun _ => 0) :=
        FreeM.wpFold_chargeUnder_liftM_le _ allows _ _ hdem x
    _ ≤ wpFold (OpSpec.chargeUnder (fun a => ∑ j, p j * openCharge tc ρ a j)
          (openAllows allows)) x (fun _ => 0) :=
        wpFold_chargeUnder_le_of_le hcost _ x _
    _ ≤ ∑ j, p j * u j := FreeM.wpFold_chargeUnder_price_le _ _ p hx
    _ = u none + ∑ i, T i * u (some i) := by simp [p, Fintype.sum_option]

end Open

end CatCrypt.Container

/-! ## Time bounds from use bounds, per kind -/

open CatCrypt.Container

namespace CatCrypt.Core.SPTree.Timed

variable {α : Type} {C : PFunctor.{1, 0}} {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- **Time bound of a costed tree from a use bound.** If the tick tree of `s` is the open tree
`x` interpreted by the call handler of `impl`, `x` has use bound `u`, and the implementation of
each call of resource `i` has charge fold at most `T i`, then `s` takes time at most
`u none + ∑ i, u (some i) * T i`. -/
theorem timeBound_of_useBound (ρ : C.A → κ) (s : SPTree.Timed α) (x : FreeM (SPSigT + C) α)
    (impl : (c : C.A) → FreeM SPSigT (C.B c))
    (hs : toFreeMT s = x.liftM (callHandler impl)) (u : Option κ → ℕ) (T : κ → ℕ)
    (hx : UseBound (openCharge tickCost ρ) (openAllows spAllows) x fun j => u j)
    (himpl : ∀ c, wpFold (OpSpec.chargeUnder (fun a => ((tickCost a : ℕ) : ℕ∞)) spAllows)
      (impl c) (fun _ => 0) ≤ T (ρ c)) :
    s.TimeBound (u none + ∑ i, u (some i) * T i) := by
  rw [timeBound_iff_wpFold_chargeUnder, hs]
  refine (wpFold_liftM_callHandler_le tickCost ρ spAllows hx impl (fun i => T i) himpl).trans ?_
  push_cast
  simp [mul_comm]

/-- **Step time bound of a costed tree from a use bound**: the step-prefixed form of
`timeBound_of_useBound`. -/
theorem le_and_timeBound_of_useBound (ρ : C.A → κ) (y : ℕ × SPTree.Timed α)
    (x : FreeM (SPSigT + C) α) (impl : (c : C.A) → FreeM SPSigT (C.B c))
    (hs : stepToFreeMT y = x.liftM (callHandler impl)) (u : Option κ → ℕ) (T : κ → ℕ)
    (hx : UseBound (openCharge tickCost ρ) (openAllows spAllows) x fun j => u j)
    (himpl : ∀ c, wpFold (OpSpec.chargeUnder (fun a => ((tickCost a : ℕ) : ℕ∞)) spAllows)
      (impl c) (fun _ => 0) ≤ T (ρ c)) :
    y.1 ≤ u none + ∑ i, u (some i) * T i ∧
      y.2.TimeBound (u none + ∑ i, u (some i) * T i - y.1) := by
  rw [le_and_timeBound_iff_wpFold_chargeUnder, hs]
  refine (wpFold_liftM_callHandler_le tickCost ρ spAllows hx impl (fun i => T i) himpl).trans ?_
  push_cast
  simp [mul_comm]

end CatCrypt.Core.SPTree.Timed

namespace CatCrypt.Crypto.OracleAdv.Timed

variable {D R α : Type} {C : PFunctor.{1, 0}} {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- **Time bound of a costed adversary from a use bound.** If the tick tree of `A` is the open
tree `x` interpreted by the call handler of `impl`, `x` has use bound `u`, and the implementation
of each call of resource `i` has charge fold at most `T i`, then `A` takes time at most
`u none + ∑ i, u (some i) * T i`. -/
theorem timeBound_of_useBound (ρ : C.A → κ) (A : Timed D R α) (x : FreeM (AdvSigT D R + C) α)
    (impl : (c : C.A) → FreeM (AdvSigT D R) (C.B c))
    (hs : toFreeMT A = x.liftM (callHandler impl)) (u : Option κ → ℕ) (T : κ → ℕ)
    (hx : UseBound (openCharge tickCost ρ) (openAllows fun _ _ => True) x fun j => u j)
    (himpl : ∀ c, wpFold (OpSpec.chargeUnder (fun a => ((tickCost a : ℕ) : ℕ∞))
      fun _ _ => True) (impl c) (fun _ => 0) ≤ T (ρ c)) :
    A.TimeBound (u none + ∑ i, u (some i) * T i) := by
  rw [timeBound_iff_wpFold_chargeUnder, hs]
  refine (wpFold_liftM_callHandler_le tickCost ρ _ hx impl (fun i => T i) himpl).trans ?_
  push_cast
  simp [mul_comm]

/-- **Step time bound of a costed adversary from a use bound**: the step-prefixed form of
`timeBound_of_useBound`. -/
theorem stepTimeBound_of_useBound (ρ : C.A → κ) (y : ℕ × Timed D R α)
    (x : FreeM (AdvSigT D R + C) α) (impl : (c : C.A) → FreeM (AdvSigT D R) (C.B c))
    (hs : stepToFreeMT y = x.liftM (callHandler impl)) (u : Option κ → ℕ) (T : κ → ℕ)
    (hx : UseBound (openCharge tickCost ρ) (openAllows fun _ _ => True) x fun j => u j)
    (himpl : ∀ c, wpFold (OpSpec.chargeUnder (fun a => ((tickCost a : ℕ) : ℕ∞))
      fun _ _ => True) (impl c) (fun _ => 0) ≤ T (ρ c)) :
    StepTimeBound y (u none + ∑ i, u (some i) * T i) := by
  rw [stepTimeBound_iff_wpFold_chargeUnder, hs]
  refine (wpFold_liftM_callHandler_le tickCost ρ _ hx impl (fun i => T i) himpl).trans ?_
  push_cast
  simp [mul_comm]

end CatCrypt.Crypto.OracleAdv.Timed

namespace CatCrypt.Crypto.OracleProg.Timed

variable {I O α : Type} {C : PFunctor.{1, 0}} {κ : Type*} [Fintype κ] [DecidableEq κ]

/-- **Time bound of a costed oracle program from a use bound.** If the tick tree of `p` is the
open tree `x` interpreted by the call handler of `impl`, `x` has use bound `u`, and the
implementation of each call of resource `i` has charge fold at most `T i`, then `p` takes time
at most `u none + ∑ i, u (some i) * T i`. -/
theorem timeBound_of_useBound (ρ : C.A → κ) (p : Timed I O α) (x : FreeM (SigT I O + C) α)
    (impl : (c : C.A) → FreeM (SigT I O) (C.B c))
    (hs : toFreeMT p = x.liftM (callHandler impl)) (u : Option κ → ℕ) (T : κ → ℕ)
    (hx : UseBound (openCharge tickCost ρ) (openAllows fun _ _ => True) x fun j => u j)
    (himpl : ∀ c, wpFold (OpSpec.chargeUnder (fun a => ((tickCost a : ℕ) : ℕ∞))
      fun _ _ => True) (impl c) (fun _ => 0) ≤ T (ρ c)) :
    p.TimeBound (u none + ∑ i, u (some i) * T i) := by
  rw [timeBound_iff_wpFold_charge, ← OpSpec.chargeUnder_true, hs]
  refine (wpFold_liftM_callHandler_le tickCost ρ _ hx impl (fun i => T i) himpl).trans ?_
  push_cast
  simp [mul_comm]

/-- **Step time bound of a costed oracle program from a use bound**: the step-prefixed form of
`timeBound_of_useBound`. -/
theorem stepTimeBound_of_useBound (ρ : C.A → κ) (y : ℕ × Timed I O α)
    (x : FreeM (SigT I O + C) α) (impl : (c : C.A) → FreeM (SigT I O) (C.B c))
    (hs : stepToFreeMT y = x.liftM (callHandler impl)) (u : Option κ → ℕ) (T : κ → ℕ)
    (hx : UseBound (openCharge tickCost ρ) (openAllows fun _ _ => True) x fun j => u j)
    (himpl : ∀ c, wpFold (OpSpec.chargeUnder (fun a => ((tickCost a : ℕ) : ℕ∞))
      fun _ _ => True) (impl c) (fun _ => 0) ≤ T (ρ c)) :
    StepTimeBound y (u none + ∑ i, u (some i) * T i) := by
  rw [stepTimeBound_iff_wpFold_chargeUnder, hs]
  refine (wpFold_liftM_callHandler_le tickCost ρ _ hx impl (fun i => T i) himpl).trans ?_
  push_cast
  simp [mul_comm]

end CatCrypt.Crypto.OracleProg.Timed
