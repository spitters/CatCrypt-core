/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.SMID
public import CatCryptCore.Tactics.DeriveReduction
import CatCryptCore.Tactics.DeriveTimeBound
public import CatCryptCore.Tactics.StdCostsMem

/-!
# Running time of the reduction of immediate decryption

The time certificate of the reduction `smIDRed` of `CatCryptCore.Crypto.Messaging.SMID`. The
reduction is the oracle tree `smIDRed.tree` of the simulation of the interaction of the
adversary by `smIDImpl`; its costed form is derived by `derive_timed`, and
`smIDRed.compile_tree` states that the erasure of the costed tree is the reduction.

A simulated query scans the bookkeeping `SMIDAux`: the log of the honest ciphertexts, the
opened epochs, and the answered corruptions with their recorded positions. The potential is
`smIDCostInv i`: the companion of the epoch counters is at most `3 i`, the log, the list of
corruptions and each recorded list of positions have at most `i` entries, and at most `i + 1`
epochs are opened. The `i`-th query costs at most `smIDQueryTime c i`
(`smIDImpl.timed_bound`), so for an adversary of time `T` with at most `q` queries the
reduction has time at most `T + ∑_{i < q} smIDQueryTime c i + c + 3`
(`smIDRed.tree.timeBound_timed`): the time of the `i`-th query is quadratic in `i`, so the sum
is a polynomial of degree three in `q`.

No module imports this file.

## Main results

* `smIDRed.tree`, `smIDRed.compile_tree` — the reduction as an oracle tree and the erasure of
  its costed form
* `smIDImpl.timed_bound` — the time of a simulated query under the potential
* `smIDRed.tree.timeBound_timed` — the time of the reduction
-/

set_option autoImplicit false

@[expose] public section

namespace CatCrypt.Crypto.Messaging

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto

section Time

variable {St Pub Rand W Ct Leak Hdr K W₀ Pub₀ Leak₀ : Type}
  [DecidableEq Pub] [DecidableEq W] [DecidableEq Hdr] [DecidableEq Ct]

/-- The oracle tree of `smIDRed` for the interaction `play` of the adversary at the base public
value `pub`. -/
def smIDRed.tree (M : SMIDScheme St Pub Rand W Ct Leak Hdr K)
    (V : SMIDView W Pub Hdr Ct Leak W₀ Pub₀ Leak₀) (ΔFS ΔPCS : ℕ) (pub : Pub₀)
    (play : OracleAdv (SMIDQuery W Hdr Ct) (SMIDAns Pub Hdr Ct Leak W) Bool) :
    OracleAdv (SMQuery W₀) (SMSchemeAns Pub₀ Ct Leak₀) Bool :=
  (OracleAdv.simulate (smIDImpl M V ΔFS ΔPCS) play
    (CKAGameSt.init () () (), SMIDAux.init (V.pubInit pub))).bind fun r => .ret r.1

derive_timed smIDRed.tree

/-- The derived costed tree of `smIDRed`, at the challenge-epoch distribution of `A` and a costed
interaction `play` that erases to the interaction of `A`, erases to the reduction. -/
theorem smIDRed.compile_tree (M : SMIDScheme St Pub Rand W Ct Leak Hdr K)
    (V : SMIDView W Pub Hdr Ct Leak W₀ Pub₀ Leak₀) (ΔFS ΔPCS : ℕ) (A : SMIDAdv Pub W Hdr Ct Leak)
    (t : ℕ) (pub : Pub₀)
    (play : OracleAdv.Timed (SMIDQuery W Hdr Ct) (SMIDAns Pub Hdr Ct Leak W) Bool)
    (hplay : play.erase = A.play t (V.pubInit pub)) (pubInitCost : Pub₀ → ℕ)
    (msgCost : Hdr → W × W → ℕ)
    (hdrCost : SMIDAux W Pub Hdr Ct → CKAGameSt Unit Unit → CKAParty → ℕ)
    (pubCost : SMIDAux W Pub Hdr Ct → CKAGameSt Unit Unit → CKAParty → Pub₀ → ℕ)
    (leakCost : SMIDAux W Pub Hdr Ct → CKAGameSt Unit Unit → CKAParty → Leak₀ → ℕ)
    (hdrPosCost hdrPubCost : Hdr → ℕ)
    (rkeyOkCost : SMIDAux W Pub Hdr Ct → CKAGameSt Unit Unit → CKAParty → Hdr → ℕ) :
    (smIDRed.tree.timed M V ΔFS ΔPCS pub play pubInitCost msgCost hdrCost pubCost leakCost
      hdrPosCost hdrPubCost rkeyOkCost).2.erase = (smIDRed M V ΔFS ΔPCS A).play t pub := by
  rw [smIDRed.tree.erase_timed, hplay]
  rfl

/-- The bound on a costed state of the simulator `smIDImpl` after at most `i` queries: the
companion of the epoch counters is at most `3 i`, the log and the list of corruptions have at
most `i` entries, every recorded list of positions has at most `i` entries, and at most `i + 1`
epochs are opened. -/
def smIDCostInv (i : ℕ) (tc : CKAParty → ℕ) (x : SMIDAux W Pub Hdr Ct) : Prop :=
  (∀ a, tc a ≤ 3 * i) ∧ x.log.length ≤ i ∧ x.corrs.length ≤ i ∧
    (∀ c ∈ x.corrs, c.2.2.length ≤ i) ∧ x.pubs.length ≤ i + 1

omit [DecidableEq Pub] [DecidableEq W] [DecidableEq Hdr] [DecidableEq Ct] in
/-- The bookkeeping after a query grows by at most one entry in each list. -/
theorem SMIDAux.upd_inv {Leak' : Type} (pos : Hdr → ℕ) (x : SMIDAux W Pub Hdr Ct)
    (sh : CKAGameSt Unit Unit) (q : SMQuery W) (a : SMSchemeAns Pub (Hdr × Ct) Leak') (i : ℕ)
    (h : smIDCostInv i (fun _ => 0) x) :
    smIDCostInv (i + 1) (fun _ => 0) (x.upd pos sh q a) := by
  obtain ⟨-, h1, h2, h3, h4⟩ := h
  have hp : (x.pending sh q.party).length ≤ x.log.length := by
    simp only [SMIDAux.pending, List.length_map]
    exact List.length_filter_le _ _
  refine ⟨fun _ => Nat.zero_le _, ?_⟩
  cases q <;> cases a <;>
    simp_all [SMIDAux.upd, SMIDAux.record, SMQuery.party] <;> grind

/-- The answer of the delivery and the bookkeeping after it. -/
theorem smIDLogDeliver_inv (M : SMIDScheme St Pub Rand W Ct Leak Hdr K)
    (V : SMIDView W Pub Hdr Ct Leak W₀ Pub₀ Leak₀) (ΔFS ΔPCS : ℕ)
    (σ : CKAGameSt Unit Unit × SMIDAux W Pub Hdr Ct) (p : CKAParty) (h : Hdr) (ad : W) (c : Ct)
    (i : ℕ) (hi : smIDCostInv i (fun _ => 0) σ.2) :
    smIDCostInv (i + 1) (fun _ => 0) (smIDLogDeliver M V ΔFS ΔPCS σ p h ad c).2.2 := by
  obtain ⟨-, h1, h2, h3, h4⟩ := hi
  refine ⟨fun _ => Nat.zero_le _, ?_⟩
  unfold smIDLogDeliver
  split <;> try split
  all_goals try split
  all_goals simp only [SMIDAux.mark, List.length_map]
  all_goals exact ⟨by omega, by omega, fun c hc => by have := h3 c hc; omega, by omega⟩

/-- The bound on the time of the `i`-th simulated query of `smIDRed`, for cost parameters of at
most `c`. -/
def smIDQueryTime (c i : ℕ) : ℕ := 20 * c + 300 + 300 * i + 100 * (i * i)

/-- **Time of a query of `smIDImpl`.** From a costed state with the companion of the epoch
counters at most `3 i`, a log, a list of corruptions and a list of opened epochs of at most `i`
entries (`smIDCostInv`), the costed simulator answers a query in time at most
`smIDQueryTime c i` and returns states satisfying `smIDCostInv (i + 1)`. -/
theorem smIDImpl.timed_bound (M : SMIDScheme St Pub Rand W Ct Leak Hdr K)
    (V : SMIDView W Pub Hdr Ct Leak W₀ Pub₀ Leak₀) (ΔFS ΔPCS : ℕ)
    (σ : CKAGameSt Unit Unit × SMIDAux W Pub Hdr Ct)
    (σc : ((CKAParty → Unit) × (CKAParty → ℕ)) × ((CKAParty → ℕ) × (CKAParty → ℕ)) × Unit)
    (d : SMIDQuery W Hdr Ct) (msgCost : Hdr → W × W → ℕ)
    (hdrCost : SMIDAux W Pub Hdr Ct → CKAGameSt Unit Unit → CKAParty → ℕ)
    (pubCost : SMIDAux W Pub Hdr Ct → CKAGameSt Unit Unit → CKAParty → Pub₀ → ℕ)
    (leakCost : SMIDAux W Pub Hdr Ct → CKAGameSt Unit Unit → CKAParty → Leak₀ → ℕ)
    (hdrPosCost hdrPubCost : Hdr → ℕ)
    (rkeyOkCost : SMIDAux W Pub Hdr Ct → CKAGameSt Unit Unit → CKAParty → Hdr → ℕ) {c : ℕ}
    (hm : ∀ h x, msgCost h x ≤ c) (hh : ∀ x s p, hdrCost x s p ≤ c)
    (hu : ∀ x s p a, pubCost x s p a ≤ c)
    (hl : ∀ x s p a, leakCost x s p a ≤ c) (hp : ∀ h, hdrPosCost h ≤ c)
    (hb : ∀ h, hdrPubCost h ≤ c) (hr : ∀ x s p h, rkeyOkCost x s p h ≤ c) (i : ℕ)
    (hinv : smIDCostInv i σc.2.1.2 σ.2) :
    OracleAdv.Timed.StepTimeBound
        (OracleAdv.Timed.delay 1 (smIDImpl.timed M V ΔFS ΔPCS σ d msgCost hdrCost pubCost leakCost
          σc hdrPosCost hdrPubCost rkeyOkCost)) (smIDQueryTime c i) ∧
      OracleAdv.Timed.AllRet (fun y => smIDCostInv (i + 1) y.2.1.2.1.2 y.2.2)
        (smIDImpl.timed M V ΔFS ΔPCS σ d msgCost hdrCost pubCost leakCost σc hdrPosCost
          hdrPubCost rkeyOkCost).2 := by
  obtain ⟨ht, h1, h2, h3, h4⟩ := hinv
  have hz : smIDCostInv i (fun _ => 0) σ.2 := ⟨fun _ => Nat.zero_le _, h1, h2, h3, h4⟩
  cases d with
  | sm q =>
    have hg := List.all.timedCost_le_mem σ.2.log
      (fun l => l.delivered || ckaSender l.e == q.party || decide (smRecvEpoch σ.1 q.party ≤ l.e))
      (fun l => 7 + (3 + (1 + (1 + σc.2.1.2 q.party + 2) +
        if ckaSender (σ.1.t q.party) = q.party then 2 + σc.2.1.2 q.party
        else 1 + σc.2.1.2 q.party) + 1)) (k := 17 + 6 * i) (fun l _ => by
          have := ht q.party
          split <;> omega)
    cases q
    all_goals simp only [smIDImpl.timed, OracleAdv.Timed.delay, OracleAdv.Timed.StepTimeBound,
      OracleAdv.Timed.TimeBound, OracleAdv.Timed.AllRet, smIDQueryTime, smIDGate, SMQuery.party,
      SMQuery.mapMsg, ↓reduceIte]
    · rename_i p
      have := ht p.other
      have := ht p
      have := ht CKAParty.A
      have := ht CKAParty.B
      refine ⟨⟨by grind, by grind, fun r => ⟨?_, trivial⟩⟩, fun r => ?_⟩
      · cases r <;> simp only [SMSchemeAns.withHdr, SMSchemeAns.map] <;> grind
      · refine ⟨?_, (SMIDAux.upd_inv _ _ _ _ _ i hz).2⟩
        intro a
        split <;> grind
    · rename_i p
      have := ht p.other
      have := ht p
      refine ⟨⟨by grind, by grind, fun r => ⟨?_, trivial⟩⟩, fun r => ?_⟩
      · cases r <;> grind
      · refine ⟨?_, (SMIDAux.upd_inv _ _ _ _ _ i hz).2⟩
        intro a
        split <;> grind
    · rename_i p m
      have := ht p
      refine ⟨⟨by grind, by grind, fun r => ⟨?_, trivial⟩⟩, fun r => ?_⟩
      · cases r <;> simp only [SMSchemeAns.withHdr, SMSchemeAns.map] <;> grind
      · exact ⟨fun a => by have := ht a; omega, (SMIDAux.upd_inv _ _ _ _ _ i hz).2⟩
    · rename_i p m
      have := ht p
      refine ⟨⟨by grind, by grind, fun r => ⟨?_, trivial⟩⟩, fun r => ?_⟩
      · cases r <;> simp only [SMSchemeAns.withHdr, SMSchemeAns.map] <;> grind
      · exact ⟨fun a => by have := ht a; omega, (SMIDAux.upd_inv _ _ _ _ _ i hz).2⟩
    · rename_i p
      simp only [SMQuery.party] at hg
      have hpend := List.filter.timedCost_le
        (fun l : SMIDLogEntry W Hdr Ct => !l.delivered && ckaSender l.e != p &&
          l.e == smRecvEpoch σ.1 p)
        (fun l => 12 + (3 + (1 + (1 + σc.2.1.2 p + 2) +
          if ckaSender (σ.1.t p) = p then 2 + σc.2.1.2 p else 1 + σc.2.1.2 p) + 1))
        (k := 22 + 6 * i) (fun l => by have := ht p; split <;> omega) σ.2.log
      have hlen := List.length_filter_le (fun l : SMIDLogEntry W Hdr Ct => !l.delivered &&
        ckaSender l.e != p && l.e == smRecvEpoch σ.1 p) σ.2.log
      have hmap := List.map.timedCost_le (fun l : SMIDLogEntry W Hdr Ct => (l.e, l.j))
        (fun _ => 0) (k := 0) (fun _ => le_rfl) (List.filter (fun l : SMIDLogEntry W Hdr Ct =>
          !l.delivered && ckaSender l.e != p && l.e == smRecvEpoch σ.1 p) σ.2.log)
      have hA := Nat.mul_le_mul_left (17 + 6 * i + 5) h1
      have hB := Nat.mul_le_mul_left (22 + 6 * i + 4) h1
      have hC := Nat.mul_le_mul_left (0 + 3) (hlen.trans h1)
      have := ht p
      by_cases hs : σ.2.storeClear σ.1 p = true
      · simp only [hs, ↓reduceIte]
        refine ⟨⟨by grind, by grind, fun r => ⟨?_, trivial⟩⟩, fun r => ?_⟩
        · cases r <;> simp only [SMSchemeAns.withHdr, SMSchemeAns.map] <;> grind
        · exact ⟨fun a => by have := ht a; grind, (SMIDAux.upd_inv _ _ _ _ _ i hz).2⟩
      · simp only [hs]
        refine ⟨⟨by grind, trivial⟩, fun a => by have := ht a; grind, by grind, by grind,
          fun c hc => by have := h3 c hc; grind, by grind⟩
  | deliver p h ad c' =>
    have hfp := List.find?.timedCost_le
      (fun q : ℕ × Pub => decide (q.2 = M.hdrPub h) && decide (q.1 ≤ σ.1.t p) &&
        ckaSender q.1 != p)
      (fun q => 1 + (2 + (2 + σc.2.1.2 p + 1) + 8)) (k := 14 + 3 * i)
      (fun _ => by have := ht p; omega) σ.2.pubs
    simp only [smIDImpl.timed, OracleAdv.Timed.delay, OracleAdv.Timed.StepTimeBound,
      OracleAdv.Timed.TimeBound, OracleAdv.Timed.AllRet, smIDQueryTime, and_true]
    refine ⟨?_, ?_⟩
    · have hA := Nat.mul_le_mul_left (14 + 3 * i + 4) h4
      have := hb h
      have := hp h
      have := hr σ.2 σ.1 p h
      split
      · grind
      · rename_i e he
        have hall := List.all.timedCost_le_mem σ.2.corrs
          (fun c => ckaAllowCorr ΔFS ΔPCS e c.2.1 c.1 &&
            (c.1 != p || decide ((e, M.hdrPos h) ∉ c.2.2)))
          (fun c => 12 + (5 + (2 + List.elem.timedCost (e, M.hdrPos h) c.2.2 + 1) + 1))
          (k := 22 + 4 * i) (fun c hc => by
            have := List.elem.timedCost_le (e, M.hdrPos h) c.2.2
            have := h3 c hc
            omega)
        have hB := Nat.mul_le_mul_left (22 + 4 * i + 5) h2
        have hfind := List.find?.timedCost_le (SMIDLogEntry.isMatch e h ad c') (fun _ => 15)
          (k := 15) (fun _ => le_rfl) σ.2.log
        have hmap := List.map.timedCost_le (fun l : SMIDLogEntry W Hdr Ct =>
          if SMIDLogEntry.isMatch e h ad c' l = true then { l with delivered := true } else l)
          (fun _ => 16) (k := 16) (fun _ => le_rfl) σ.2.log
        have hC := Nat.mul_le_mul_left 19 h1
        have hD := Nat.mul_le_mul_left (16 + 4) h1
        split
        · split
          · grind
          · grind
        · grind
    · grind only [smIDLogDeliver_inv]

/-- `smIDCostInv` on a costed simulator state: the companion of the epoch counters and the
bookkeeping. -/
def smIDStInv (i : ℕ)
    (ŝ : (((CKAParty → Unit) × (CKAParty → ℕ)) × ((CKAParty → ℕ) × (CKAParty → ℕ)) × Unit) ×
      SMIDAux W Pub Hdr Ct) : Prop :=
  smIDCostInv i ŝ.1.2.1.2 ŝ.2

omit [DecidableEq Pub] [DecidableEq W] [DecidableEq Hdr] [DecidableEq Ct] in
/-- Every oracle tree has the query bound `0` at the zero charge. -/
theorem smID_isQueryBoundBy_zero {D' R' α : Type} (A : OracleAdv D' R' α) :
    A.IsQueryBoundBy (fun _ => 0) 0 := by
  induction A with
  | ret a => trivial
  | rand p k ih => exact ih
  | query d k ih => exact ⟨le_rfl, ih⟩

/-- **Time of `smIDRed`.** For a costed interaction of time at most `T` with at most `q` queries,
and cost parameters of at most `c`, the derived costed tree of the reduction has time at most
`T + ∑_{i < q} smIDQueryTime c i + c + 3`, a polynomial of degree three in `q`: the bookkeeping
the simulator scans has at most one entry more per query, and the time of the `i`-th query is
quadratic in `i`. -/
theorem smIDRed.tree.timeBound_timed (M : SMIDScheme St Pub Rand W Ct Leak Hdr K)
    (V : SMIDView W Pub Hdr Ct Leak W₀ Pub₀ Leak₀) (ΔFS ΔPCS : ℕ) (pub : Pub₀)
    (play : OracleAdv.Timed (SMIDQuery W Hdr Ct) (SMIDAns Pub Hdr Ct Leak W) Bool)
    (pubInitCost : Pub₀ → ℕ) (msgCost : Hdr → W × W → ℕ)
    (hdrCost : SMIDAux W Pub Hdr Ct → CKAGameSt Unit Unit → CKAParty → ℕ)
    (pubCost : SMIDAux W Pub Hdr Ct → CKAGameSt Unit Unit → CKAParty → Pub₀ → ℕ)
    (leakCost : SMIDAux W Pub Hdr Ct → CKAGameSt Unit Unit → CKAParty → Leak₀ → ℕ)
    (hdrPosCost hdrPubCost : Hdr → ℕ)
    (rkeyOkCost : SMIDAux W Pub Hdr Ct → CKAGameSt Unit Unit → CKAParty → Hdr → ℕ) {T q c : ℕ}
    (hA : play.TimeBound T) (hq : play.erase.IsQueryBound q) (hi : ∀ a, pubInitCost a ≤ c)
    (hm : ∀ h x, msgCost h x ≤ c) (hh : ∀ x s p, hdrCost x s p ≤ c)
    (hu : ∀ x s p a, pubCost x s p a ≤ c)
    (hl : ∀ x s p a, leakCost x s p a ≤ c) (hp : ∀ h, hdrPosCost h ≤ c)
    (hb : ∀ h, hdrPubCost h ≤ c) (hr : ∀ x s p h, rkeyOkCost x s p h ≤ c) :
    OracleAdv.Timed.StepTimeBound
      (smIDRed.tree.timed M V ΔFS ΔPCS pub play pubInitCost msgCost hdrCost pubCost leakCost
        hdrPosCost hdrPubCost rkeyOkCost)
      (T + ∑ i ∈ Finset.range q, smIDQueryTime c i + c + 3) := by
  unfold smIDRed.tree.timed OracleAdv.Timed.simulateHat
  refine (OracleAdv.Timed.stepTimeBound_delay_add_bind (c := 3 + pubInitCost pub)
    (m := T + ∑ i ∈ Finset.range q, smIDQueryTime c i) (n := 0) ?_ ?_).mono ?_
  · refine (OracleAdv.Timed.timeBound_simulate_inv_of_isQueryBoundBy _ (fun _ => 0)
      (smIDQueryTime c) (smIDStInv (Pub := Pub) (W := W) (Hdr := Hdr) (Ct := Ct))
      (fun i ŝ d h => ?_) hA (smID_isQueryBoundBy_zero _) hq 0 _ ?_).mono ?_
    · obtain ⟨h1, h2⟩ := smIDImpl.timed_bound M V ΔFS ΔPCS
        ({ st := ŝ.1.1.1, t := ŝ.1.2.1.1, msg := ŝ.1.2.2 }, ŝ.2) ŝ.1 d msgCost hdrCost pubCost
        leakCost hdrPosCost hdrPubCost rkeyOkCost hm hh hu hl hp hb hr i h
      exact ⟨by simpa using h1, h2⟩
    · simp [smIDStInv, smIDCostInv, SMIDAux.init]
    · simp only [Nat.zero_add, Nat.add_zero, le_refl]
  · exact fun _ => ⟨le_rfl, trivial⟩
  · have := hi pub
    simp only [Nat.add_zero]
    grind

end Time

end CatCrypt.Crypto.Messaging
