/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.SMAuth

/-!
# Running time of the reduction of authenticity to the corruption game

The time certificate of the reduction `smAuthRed` of
`CatCryptCore.Crypto.Messaging.SMAuth`. The reduction is the oracle tree `smAuthRed.tree` with
the interaction of the adversary as a parameter; its costed form is derived by `derive_timed`,
and `smAuthRed.compile_tree` states that the erased costed tree is the reduction at a costed
interaction erasing to the adversary's.

The simulator `smAuthImpl` keeps the log of the honest ciphertexts and the list of the answered
corruptions. A simulated query counts the entries of the log of one epoch, searches the log or
tests every corruption, so its cost is linear in their lengths. The potential of the
certificate is the bound `smAuthCostInv i`: after `i` queries the log and the list of
corruptions have at most `i` entries and the cost companions of the epoch counters are at most
`1 + 3 i`. The `i`-th simulated query then costs at most `40 i + 60` (`smAuthImpl.timed_bound`),
and for an adversary of time `T` with at most `q` queries and call cost at most `a` the
reduction has time at most `T + ∑_{j < q} (40 j + 60) + a + 4` (`smAuthRed.timeBound_timed`), a
polynomial of degree two in `q`.

No module imports this file.

## Main results

* `smAuthRed.tree`, `smAuthRed.compile_tree` — the reduction as an oracle tree and the erasure
  of its costed form
* `smAuthImpl.timed_bound` — the time of a simulated query under the potential
* `smAuthRed.timeBound_timed` — the time of the reduction
-/

set_option autoImplicit false

@[expose] public section

namespace CatCrypt.Crypto.Messaging

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto

section Red

variable {Pub W Ct Leak : Type} [DecidableEq W] [DecidableEq Ct]

/-- The oracle tree of the reduction `smAuthRed` at the challenge epoch `t` and the public value
`pub`, for the interaction `play` of the authenticity adversary. -/
def smAuthRed.tree (ΔFS ΔPCS : ℕ)
    (play : ℕ → Pub → OracleAdv (SMAuthQuery W Ct) (SMAuthAns Pub Ct Leak W) Bool) (t : ℕ)
    (pub : Pub) : OracleAdv (SMQuery W) (SMSchemeAns Pub Ct Leak) Bool :=
  (OracleAdv.simulate (smAuthImpl ΔFS ΔPCS) (play t pub)
    (CKAGameSt.init () () (), SMAuthAux.init)).bind fun r => .ret r.1

derive_timed smAuthRed.tree

/-- The derived costed tree of `smAuthRed`, at a costed interaction `play` that erases to the
interaction of `A`, erases to the interaction of the reduction. -/
theorem smAuthRed.compile_tree (ΔFS ΔPCS : ℕ) (A : SMAuthAdv Pub W Ct Leak)
    (play : ℕ → Pub → OracleAdv.Timed (SMAuthQuery W Ct) (SMAuthAns Pub Ct Leak W) Bool)
    (playCost : ℕ → Pub → ℕ) (hplay : ∀ t g, (play t g).erase = A.play t g) (t : ℕ)
    (pub : Pub) :
    (smAuthRed.tree.timed ΔFS ΔPCS play playCost t pub).2.erase =
      (smAuthRed ΔFS ΔPCS A).play t pub := by
  rw [smAuthRed.tree.erase_timed]
  have h : (fun t g => (play t g).erase) = A.play := funext fun t => funext (hplay t)
  rw [h]
  rfl

/-- `List.all` with a test of cost at most `k` costs at most `k + 5` per element and one
more. -/
private theorem all_timedCost_le {α : Type} (l : List α) (p : α → Bool) (pCost : α → ℕ)
    {k : ℕ} (hp : ∀ a, pCost a ≤ k) : List.all.timedCost l p pCost ≤ (k + 5) * l.length + 1 := by
  induction l with
  | nil => simp [List.all.timedCost.eq_1]
  | cons a l ih =>
    rw [List.all.timedCost.eq_2, List.length_cons, Nat.mul_succ]
    have := hp a
    omega

omit [DecidableEq W] [DecidableEq Ct] in
/-- A query of the corruption game adds at most one entry to the log and at most one
corruption to the bookkeeping. -/
theorem SMAuthAux.upd_length (x : SMAuthAux W Ct) (sh : CKAGameSt Unit Unit) (q : SMQuery W)
    (a : SMSchemeAns Pub Ct Leak) :
    (x.upd sh q a).log.length ≤ x.log.length + 1 ∧
      (x.upd sh q a).corrs.length ≤ x.corrs.length + 1 := by
  cases q <;> cases a <;> grind [SMAuthAux.upd, SMAuthAux.record]

/-- The bound on a costed state of the simulator `smAuthImpl` after at most `i` queries: the
cost companions of the epoch counters are at most `1 + 3 i`, and the log and the list of
corruptions have at most `i` entries. -/
def smAuthCostInv (i : ℕ)
    (ŝ : (((CKAParty → Unit) × (CKAParty → ℕ)) × ((CKAParty → ℕ) × (CKAParty → ℕ)) × Unit) ×
      SMAuthAux W Ct) : Prop :=
  (∀ p, ŝ.1.1.2 p ≤ 1 + 3 * i) ∧ (∀ p, ŝ.1.2.1.2 p ≤ 1 + 3 * i) ∧ ŝ.2.log.length ≤ i ∧
    ŝ.2.corrs.length ≤ i

/-- The time of the `i`-th simulated query of `smAuthRed`: the companions of the counters, the
search of the log and the test of the corruptions, each linear in `i`. -/
def smAuthQueryTime (i : ℕ) : ℕ := 40 * i + 60

/-- **Time of a query of the simulator of `smAuthRed`.** From a costed state satisfying
`smAuthCostInv i`, the costed simulator answers in time at most `smAuthQueryTime i` and returns
states satisfying `smAuthCostInv (i + 1)`. -/
theorem smAuthImpl.timed_bound (ΔFS ΔPCS i : ℕ)
    (ŝ : (((CKAParty → Unit) × (CKAParty → ℕ)) × ((CKAParty → ℕ) × (CKAParty → ℕ)) × Unit) ×
      SMAuthAux W Ct) (d : SMAuthQuery W Ct) (hinv : smAuthCostInv i ŝ) :
    OracleAdv.Timed.StepTimeBound (OracleAdv.Timed.delay 1
        (smAuthImpl.timed (Pub := Pub) (Leak := Leak) ΔFS ΔPCS
          ({ st := ŝ.1.1.1, t := ŝ.1.2.1.1, msg := ŝ.1.2.2 }, ŝ.2) d ŝ.1))
        (smAuthQueryTime i) ∧
      OracleAdv.Timed.AllRet (fun y => smAuthCostInv (i + 1) y.2)
        (OracleAdv.Timed.delay 1 (smAuthImpl.timed (Pub := Pub) (Leak := Leak) ΔFS ΔPCS
          ({ st := ŝ.1.1.1, t := ŝ.1.2.1.1, msg := ŝ.1.2.2 }, ŝ.2) d ŝ.1)).2 := by
  obtain ⟨h1, h2, h3, h4⟩ := hinv
  unfold smAuthCostInv smAuthQueryTime
  cases d with
  | sm q =>
    have hc := fun pr : SMLogEntry W Ct → Bool => List.countP.timedCost_le pr
      (fun _ => 1) (k := 1) (fun _ => le_rfl) ŝ.2.log
    have hu := fun a => SMAuthAux.upd_length (Pub := Pub) (Leak := Leak) ŝ.2
      { st := ŝ.1.1.1, t := ŝ.1.2.1.1, msg := ŝ.1.2.2 } q a
    cases q <;>
      simp only [smAuthImpl.timed, OracleAdv.Timed.delay, OracleAdv.Timed.StepTimeBound,
        OracleAdv.Timed.TimeBound, OracleAdv.Timed.AllRet] <;>
      repeat' (first | trivial | apply And.intro | intro _ | split |
        dsimp only [OracleAdv.Timed.StepTimeBound, OracleAdv.Timed.TimeBound,
          OracleAdv.Timed.AllRet] | grind)
  | deliver p j ad c =>
    have hf := fun pr : SMLogEntry W Ct → Bool => List.find?.timedCost_le pr (fun _ => 1)
      (k := 1) (fun _ => le_rfl) ŝ.2.log
    have ha := all_timedCost_le ŝ.2.corrs
      (fun c => ckaAllowCorr ΔFS ΔPCS (ŝ.1.2.1.1 p) c.2 c.1) (fun _ => 11) (k := 11)
      (fun _ => le_rfl)
    simp only [smAuthImpl.timed, OracleAdv.Timed.delay, OracleAdv.Timed.StepTimeBound,
      OracleAdv.Timed.TimeBound, OracleAdv.Timed.AllRet]
    repeat' (first | trivial | apply And.intro | intro _ | split | grind)

/-- **Time of `smAuthRed`.** For a costed interaction of time at most `T`, at most `q` queries
and call cost at most `a`, the derived costed tree of `smAuthRed` has time at most
`T + ∑_{j < q} (40 j + 60) + a + 4`: the `j`-th simulated query searches a log and a list of
corruptions of at most `j` entries each. -/
theorem smAuthRed.timeBound_timed (ΔFS ΔPCS : ℕ)
    (play : ℕ → Pub → OracleAdv.Timed (SMAuthQuery W Ct) (SMAuthAns Pub Ct Leak W) Bool)
    (playCost : ℕ → Pub → ℕ) (t : ℕ) (pub : Pub) {T q a : ℕ}
    (hA : ∀ t g, (play t g).TimeBound T) (hq : ∀ t g, (play t g).erase.IsQueryBound q)
    (ha : ∀ t g, playCost t g ≤ a) :
    OracleAdv.Timed.StepTimeBound (smAuthRed.tree.timed ΔFS ΔPCS play playCost t pub)
      (T + ∑ j ∈ Finset.range q, smAuthQueryTime j + a + 4) := by
  unfold smAuthRed.tree.timed
  have := ha t pub
  have hx := OracleAdv.Timed.timeBound_simulateHat_inv
    (fun y => (({ st := y.1.1.1, t := y.1.2.1.1, msg := y.1.2.2 } : CKAGameSt Unit Unit), y.2))
    (fun y : CKAGameSt Unit Unit × SMAuthAux W Ct =>
      (((fun a => y.1.st a, fun _ => 0), (fun a => y.1.t a, fun _ => 0), y.1.msg), y.2)) _
    (fun i ŝ => smAuthCostInv i ŝ) smAuthQueryTime
    (fun i ŝ d h => smAuthImpl.timed_bound (Pub := Pub) (Leak := Leak) ΔFS ΔPCS i ŝ d h)
    (hA t pub) (hq t pub) 0
    (((fun p => match p with | .A => () | .B => (), fun _ => 1), (fun _ => 0, fun _ => 0), ()),
      SMAuthAux.init) ⟨fun p => by cases p <;> simp, fun _ => by simp,
        by simp [SMAuthAux.init], by simp [SMAuthAux.init]⟩
  simp only [Nat.zero_add] at hx
  refine (OracleAdv.Timed.stepTimeBound_delay
    (OracleAdv.Timed.timeBound_bind (n := 0) hx.2
      (f := fun r => (0, OracleAdv.Timed.ret r.1)) fun _ => ⟨le_refl _, trivial⟩)).mono ?_
  have := hx.1
  grind

end Red

end CatCrypt.Crypto.Messaging
