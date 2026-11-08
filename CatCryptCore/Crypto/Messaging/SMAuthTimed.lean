/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.SMAuth
public import CatCryptCore.Crypto.Messaging.SMCorruptTimed
public import CatCryptCore.Crypto.FiatShamirROM.Timed
public import CatCryptCore.Crypto.OracleAdversaryPotential
import CatCryptCore.Tactics.DeriveTimed

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

The CKA reduction `smAuthCKARed` of the forgery event runs the adversary against the simulator
`smAuthCKAImpl`, which forwards a query of the corruption game to the CKA simulator and logs it,
or answers a delivery from the log and by a decryption under a key of the receiving chain. The
potential is `smAuthCKACostInv i`: the cost companions of the CKA simulator are at most
`1 + 3 i`, and the log and the list of corruptions have at most `i` entries. A delivery at the
position `j` of the chain walks it `j` steps twice, so its step handles data of the size of the
event: the `i`-th query costs at most `2 (g + 4) j + smAuthCKAQueryTime r g e dd i`
(`smAuthCKAImpl.timed_bound`). For an adversary of time `T` with at most `q` queries whose
delivery positions sum to at most `J`, the reduction has time at most
`T + 2 (g + 4) J + ∑_{j < q} smAuthCKAQueryTime r g e dd j + a + 7`
(`smAuthCKARed.timeBound_timed`).

No module imports this file.

## Main results

* `smAuthRed.tree`, `smAuthRed.compile_tree` — the reduction as an oracle tree and the erasure
  of its costed form
* `smAuthImpl.timed_bound` — the time of a simulated query under the potential
* `smAuthRed.timeBound_timed` — the time of the reduction
* `smAuthCKARed.tree`, `smAuthCKARed.compile_tree` — the CKA reduction of the forgery event as an
  oracle tree and the erasure of its costed form
* `smCKAImplAt.timed_bound`, `smAuthCKAFwd.timed_bound` — the time of a query of the CKA
  simulator with the gates of the challenge epoch, and of a forwarded and logged query
* `smAuthCKAImpl.timed_bound` — the time of a simulated query, with the walk of the receiving
  chain charged to the delivery position `smAuthDeliverIdx`
* `smAuthCKARed.timeBound_timed` — the time of the CKA reduction of the forgery event
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

section AuthCKATime

open CatCrypt.Crypto.Assumptions

variable {Sc Msg Key Rand RK Sa W Ct : Type} [SampleableType W] [SampleableType Ct]
  [DecidableEq W] [DecidableEq Ct] [Fintype RK] [Nonempty RK]

/-- The oracle tree of the CKA reduction `smAuthCKARed` at the CKA challenge epoch `k` and the
public value `pub`, for the challenge-epoch distribution `tStar` and the interaction `play` of
the authenticity adversary. -/
noncomputable def smAuthCKARed.tree (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa))
    (D : AEADDef W Ct) (ΔFS ΔPCS : ℕ) (tStar : PMF ℕ)
    (play : ℕ → Msg → OracleAdv (SMAuthQuery W Ct) (SMAuthAns Msg Ct (SMPartySt Sc RK Sa) W) Bool)
    (k : ℕ) (pub : Msg) : OracleAdv CKAQuery (CKAAns Sc Msg Key Rand) Bool :=
  smAuthCKATree R G D ΔFS ΔPCS tStar play k pub

derive_timed smAuthCKARed.tree

/-- The derived costed tree of `smAuthCKARed`, at a costed interaction `play` that erases to the
interaction of `A`, erases to the interaction of the CKA reduction. -/
theorem smAuthCKARed.compile_tree (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa))
    (D : AEADDef W Ct) (ΔFS ΔPCS k : ℕ) (A : SMAuthAdv Msg W Ct (SMPartySt Sc RK Sa))
    (play : ℕ → Msg → OracleAdv.Timed (SMAuthQuery W Ct) (SMAuthAns Msg Ct (SMPartySt Sc RK Sa) W)
      Bool)
    (playCost : ℕ → Msg → ℕ) (hplay : ∀ t g, (play t g).erase = A.play t g) (pub : Msg)
    (rCost : RK × Key → ℕ) (eCost : W → W → W → ℕ) (gCost : Sa → ℕ)
    (dCost : W → Ct → W → ℕ) :
    (smAuthCKARed.tree.timed (Key := Key) (Rand := Rand) R G D ΔFS ΔPCS A.tStar play playCost k
        pub rCost eCost gCost dCost).2.erase =
      (smAuthCKARed R G D ΔFS ΔPCS k A).play k pub := by
  rw [smAuthCKARed.tree.erase_timed]
  have h : (fun t g => (play t g).erase) = A.play := funext fun t => funext (hplay t)
  rw [h]
  rfl

/-- `j` iterations of a function of cost at most `c` cost at most `(c + 3) j + 1`. -/
private theorem iterate_timedCost_le {α : Type} (f : α → α) (fCost : α → ℕ) {c : ℕ}
    (hf : ∀ a, fCost a ≤ c) (j : ℕ) :
    ∀ s, Nat.iterate.timedCost f fCost j s ≤ (c + 3) * j + 1 := by
  induction j with
  | zero => intro s; simp [Nat.iterate.timedCost]
  | succ j ih =>
    intro s
    have := ih (f s); have := hf s
    simp only [Nat.iterate.timedCost]
    rw [Nat.mul_succ]; omega

/-- The bound on a costed state of the simulator `smAuthCKAImpl` after at most `i` queries: the
cost companions of the CKA simulator are at most `1 + 3 i` (`smCKACostInv`), and the log and the
list of corruptions have at most `i` entries. -/
def smAuthCKACostInv (i : ℕ)
    (ŝ : (((((CKAParty → RK) × (CKAParty → ℕ)) × ((CKAParty → Option Sa) × (CKAParty → ℕ)) ×
      ((CKAParty → Option Sa) × (CKAParty → ℕ)) × Option (RK × Sa) × Bool) ×
      ((CKAParty → Unit) × (CKAParty → ℕ)) × ((CKAParty → ℕ) × (CKAParty → ℕ)) × Unit) ×
      SMAuthAux W Ct) × Bool) : Prop :=
  smCKACostInv (1 + 3 * i) ŝ.1.1.1 ŝ.1.1.2 ∧ ŝ.1.2.log.length ≤ i ∧ ŝ.1.2.corrs.length ≤ i

omit [DecidableEq W] [DecidableEq Ct] [Fintype RK] [Nonempty RK] in
/-- **Time of a query of `smCKAImplAt`.** From a costed state with companions at most `1 + 3 i`,
the costed simulator answers in time at most `smCKAQueryTime r g e (1 + 3 i) + 3 (1 + 3 i) + 13`
and returns states with companions at most `1 + 3 (i + 1)`. -/
theorem smCKAImplAt.timed_bound (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa))
    (D : AEADDef W Ct) (ΔFS ΔPCS t k : ℕ) (ideal : Bool) (σ : SMLoc RK Sa × CKAGameSt Unit Unit)
    (q : SMQuery W) (rCost : RK × Key → ℕ) (eCost : W → W → W → ℕ) (gCost : Sa → ℕ)
    {r g e : ℕ} (hr : ∀ x, rCost x ≤ r) (he : ∀ k m a, eCost k m a ≤ e) (hg : ∀ s, gCost s ≤ g)
    (i : ℕ) (fh sh) (hinv : smCKACostInv (1 + 3 * i) fh sh) :
    OracleAdv.Timed.StepTimeBound
        (smCKAImplAt.timed (Sc := Sc) (Msg := Msg) (Rand := Rand) R G D ΔFS ΔPCS t k ideal σ q
          rCost fh sh eCost gCost) (smCKAQueryTime r g e (1 + 3 * i) + 3 * (1 + 3 * i) + 13) ∧
      OracleAdv.Timed.AllRet (fun y => smCKACostInv (1 + 3 * (i + 1)) y.2.1 y.2.2)
        (smCKAImplAt.timed (Sc := Sc) (Msg := Msg) (Rand := Rand) R G D ΔFS ΔPCS t k ideal σ q
          rCost fh sh eCost gCost).2 := by
  have hk := smCKAImplOf.timed_bound (Sc := Sc) (Msg := Msg) (Rand := Rand) R G D k ideal σ q
    rCost eCost gCost hr he hg i fh sh hinv
  have ht := smCKAImplOf.timed_bound (Sc := Sc) (Msg := Msg) (Rand := Rand) R G D t ideal σ q
    rCost eCost gCost hr he hg i fh sh hinv
  obtain ⟨h1, h2, h3, h4, h5⟩ := hinv
  cases q with
  | corrupt p =>
    simp only [smCKAImplAt.timed]
    split
    · have := h5 p; have := h5 .A; have := h5 .B
      exact ⟨(OracleAdv.Timed.stepTimeBound_delay (OracleAdv.Timed.stepTimeBound_delay
        hk.1)).mono (by omega), hk.2⟩
    · have := h5 p; have := h5 .A; have := h5 .B
      simp only [OracleAdv.Timed.delay, OracleAdv.Timed.StepTimeBound,
        OracleAdv.Timed.TimeBound, OracleAdv.Timed.AllRet, smCKACostInv]
      grind
  | chall p m =>
    simp only [smCKAImplAt.timed]
    exact ⟨(OracleAdv.Timed.stepTimeBound_delay ht.1).mono (by omega), ht.2⟩
  | ratchet p =>
    simp only [smCKAImplAt.timed]
    exact ⟨(OracleAdv.Timed.stepTimeBound_delay hk.1).mono (by omega), hk.2⟩
  | recv p =>
    simp only [smCKAImplAt.timed]
    exact ⟨(OracleAdv.Timed.stepTimeBound_delay hk.1).mono (by omega), hk.2⟩
  | send p m =>
    simp only [smCKAImplAt.timed]
    exact ⟨(OracleAdv.Timed.stepTimeBound_delay hk.1).mono (by omega), hk.2⟩

/-- The time of a query forwarded by `smAuthCKAFwd` from a state after `i` queries. -/
def smAuthCKAFwdTime (r g e i : ℕ) : ℕ := smCKAQueryTime r g e (1 + 3 * i) + 18 * i + 40

omit [DecidableEq W] [DecidableEq Ct] [Fintype RK] [Nonempty RK] in
/-- **Time of a forwarded query.** From a costed state with companions at most `1 + 3 i`, a log
and a list of corruptions of at most `i` entries, `smAuthCKAFwd` answers in time at most
`smAuthCKAFwdTime r g e i` and returns states satisfying `smAuthCKACostInv (i + 1)`. -/
theorem smAuthCKAFwd.timed_bound (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa))
    (D : AEADDef W Ct) (ΔFS ΔPCS t k : ℕ)
    (σ : ((SMLoc RK Sa × CKAGameSt Unit Unit) × SMAuthAux W Ct) × Bool) (q : SMQuery W)
    (rCost : RK × Key → ℕ) (eCost : W → W → W → ℕ) (gCost : Sa → ℕ)
    {r g e : ℕ} (hr : ∀ x, rCost x ≤ r) (he : ∀ k m a, eCost k m a ≤ e) (hg : ∀ s, gCost s ≤ g)
    (i : ℕ) (fh sh) (tCost : CKAParty → ℕ) (hinv : smCKACostInv (1 + 3 * i) fh sh)
    (ht : ∀ p, tCost p ≤ 1 + 3 * i) (hl : σ.1.2.log.length ≤ i) (hc : σ.1.2.corrs.length ≤ i) :
    OracleAdv.Timed.StepTimeBound
        (smAuthCKAFwd.timed (Sc := Sc) (Msg := Msg) (Rand := Rand) R G D ΔFS ΔPCS t k σ q rCost
          fh sh eCost gCost tCost) (smAuthCKAFwdTime r g e i) ∧
      OracleAdv.Timed.AllRet (fun y => smAuthCKACostInv (i + 1) y.2)
        (smAuthCKAFwd.timed (Sc := Sc) (Msg := Msg) (Rand := Rand) R G D ΔFS ΔPCS t k σ q rCost
          fh sh eCost gCost tCost).2 := by
  obtain ⟨hs, ha⟩ := smCKAImplAt.timed_bound (Sc := Sc) (Msg := Msg) (Rand := Rand) R G D ΔFS
    ΔPCS t k false σ.1.1 q rCost eCost gCost hr he hg i fh sh hinv
  have hcp := fun pr : SMLogEntry W Ct → Bool => List.countP.timedCost_le pr
    (fun _ => 1) (k := 1) (fun _ => le_rfl) σ.1.2.log
  have hu := fun a => SMAuthAux.upd_length (Pub := Msg) (Leak := SMPartySt Sc RK Sa) σ.1.2
    σ.1.1.2 q a
  unfold smAuthCKAFwd.timed smAuthCKAFwdTime
  refine ⟨(OracleAdv.Timed.stepTimeBound_delay_add_bind (c := 1) (n := 9 * i + 13) hs
    fun x => ?_).mono ?_, OracleAdv.Timed.allRet_bind ha fun x hx => ?_⟩
  · refine ⟨?_, trivial⟩
    split <;> grind
  · omega
  · change smAuthCKACostInv _ _
    exact ⟨hx, (hu _).1.trans (by omega), (hu _).2.trans (by omega)⟩

/-- The position in the receiving chain of a delivery query, and `0` at every other query: the
charge of the queries whose answers walk the chain of the receiver. -/
def smAuthDeliverIdx : SMAuthQuery W Ct → ℕ
  | .deliver _ j _ _ => j
  | .sm _ => 0

/-- The time of the `i`-th simulated query of `smAuthCKARed` apart from the walk of the
receiving chain: a forwarded query, the search of the log and the tests of the corruptions,
with decryptions of cost at most `d`. -/
def smAuthCKAQueryTime (r g e d i : ℕ) : ℕ :=
  smCKAQueryTime r g e (1 + 3 * i) + 120 * i + 2 * g + 2 * d + 250

omit [Fintype RK] [Nonempty RK] in
/-- **Time of a query of the simulator of `smAuthCKARed`.** From a costed state with companions
at most `1 + 3 i`, a log and a list of corruptions of at most `i` entries, the costed simulator
`smAuthCKAImpl` answers the query `d` in time at most
`2 (g + 4) · smAuthDeliverIdx d + smAuthCKAQueryTime r g e dd i` and returns states satisfying
`smAuthCKACostInv (i + 1)`. -/
theorem smAuthCKAImpl.timed_bound (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa))
    (D : AEADDef W Ct) (ΔFS ΔPCS t k : ℕ)
    (σ : ((SMLoc RK Sa × CKAGameSt Unit Unit) × SMAuthAux W Ct) × Bool) (d : SMAuthQuery W Ct)
    (rCost : RK × Key → ℕ) (eCost : W → W → W → ℕ) (gCost : Sa → ℕ) (dCost : W → Ct → W → ℕ)
    {r g e dd : ℕ} (hr : ∀ x, rCost x ≤ r) (he : ∀ k m a, eCost k m a ≤ e)
    (hg : ∀ s, gCost s ≤ g) (hd : ∀ k c a, dCost k c a ≤ dd)
    (i : ℕ) (fh sh) (x : SMAuthAux W Ct) (hinv : smCKACostInv (1 + 3 * i) fh sh)
    (hl : σ.1.2.log.length ≤ i) (hc : σ.1.2.corrs.length ≤ i) :
    OracleAdv.Timed.StepTimeBound (OracleAdv.Timed.delay 1
        (smAuthCKAImpl.timed (Sc := Sc) (Msg := Msg) (Rand := Rand) R G D ΔFS ΔPCS t k σ d rCost
          fh sh eCost gCost sh.2.1.2 ((fh, sh), x) dCost))
        (2 * (g + 4) * smAuthDeliverIdx d + smAuthCKAQueryTime r g e dd i) ∧
      OracleAdv.Timed.AllRet (fun y => smAuthCKACostInv (i + 1) y.2)
        (smAuthCKAImpl.timed (Sc := Sc) (Msg := Msg) (Rand := Rand) R G D ΔFS ΔPCS t k σ d rCost
          fh sh eCost gCost sh.2.1.2 ((fh, sh), x) dCost).2 := by
  have hall := all_timedCost_le σ.1.2.corrs (fun c => ckaAllowCorr ΔFS ΔPCS k c.2 c.1)
    (fun _ => 11) (k := 11) (fun _ => le_rfl)
  have hfw := fun q => smAuthCKAFwd.timed_bound (Sc := Sc) (Msg := Msg) (Rand := Rand) R G D
    ΔFS ΔPCS t k σ q rCost eCost gCost hr he hg i fh sh sh.2.1.2 hinv hinv.2.2.2.2 hl hc
  obtain ⟨h1, h2, h3, h4, h5⟩ := hinv
  unfold smAuthCKAImpl.timed
  split
  · cases d with
    | sm q =>
      cases q with
      | corrupt p =>
        dsimp only
        split
        · have := h5 p; have := h5 .A; have := h5 .B
          refine ⟨(OracleAdv.Timed.stepTimeBound_delay (OracleAdv.Timed.stepTimeBound_delay
            (OracleAdv.Timed.stepTimeBound_delay (OracleAdv.Timed.stepTimeBound_delay
              (n := 0) ?_)))).mono (by
                simp only [smAuthDeliverIdx, smAuthCKAQueryTime]; omega), ?_⟩
          · exact ⟨Nat.zero_le _, trivial⟩
          exact ⟨⟨fun q => by grind, fun q => by grind, fun q => by grind, fun q => by grind,
            fun q => by grind⟩, by grind, by simp only [List.length_cons]; omega⟩
        · have := h5 p; have := h5 .A; have := h5 .B
          exact ⟨(OracleAdv.Timed.stepTimeBound_delay (OracleAdv.Timed.stepTimeBound_delay
            (OracleAdv.Timed.stepTimeBound_delay (OracleAdv.Timed.stepTimeBound_delay
              (OracleAdv.Timed.stepTimeBound_delay (hfw _).1))))).mono (by
                simp only [smAuthDeliverIdx, smAuthCKAQueryTime, smAuthCKAFwdTime]; omega),
            (hfw _).2⟩
      | _ =>
        exact ⟨(OracleAdv.Timed.stepTimeBound_delay (OracleAdv.Timed.stepTimeBound_delay
          (OracleAdv.Timed.stepTimeBound_delay (OracleAdv.Timed.stepTimeBound_delay
            (hfw _).1)))).mono (by
              simp only [smAuthDeliverIdx, smAuthCKAQueryTime, smAuthCKAFwdTime]; omega),
          (hfw _).2⟩
    | deliver p j ad c =>
      have hall' := all_timedCost_le σ.1.2.corrs
        (fun c => ckaAllowCorr ΔFS ΔPCS (σ.1.1.2.t p) c.2 c.1) (fun _ => 11) (k := 11)
        (fun _ => le_rfl)
      have hfind := List.find?.timedCost_le
        (fun l : SMLogEntry W Ct => decide (l.e = σ.1.1.2.t p ∧ l.j = j ∧ l.ad = ad ∧ l.ct = c))
        (fun _ => 1) (k := 1) (fun _ => le_rfl) σ.1.2.log
      have hit := iterate_timedCost_le (fun s => (G.stretch s).2) (fun s => 1 + gCost s)
        (c := g + 1) (fun s => by have := hg s; omega) j
      have hp5 := h5 p
      have hp3 := h3 p
      refine ⟨(OracleAdv.Timed.stepTimeBound_delay (OracleAdv.Timed.stepTimeBound_delay
        (OracleAdv.Timed.stepTimeBound_delay
          (n := 2 * ((g + 4) * j) + 100 * i + 2 * g + 2 * dd + 100) ?_))).mono ?_, ?_⟩
      · refine ⟨?_, trivial⟩
        dsimp only
        rcases hrcv : σ.1.1.1.rcv p with _ | a
        · simp only
          repeat' split
          all_goals omega
        · have := hit a
          have := hg ((fun s => (G.stretch s).2)^[j] a)
          have := hd (chainKey G a j) c ad
          simp only
          rw [show g + 1 + 3 = g + 4 by omega] at *
          generalize (g + 4) * j = M at *
          repeat' split
          all_goals omega
      · simp only [smAuthDeliverIdx, smAuthCKAQueryTime]
        rw [Nat.mul_assoc]
        omega
      · change smAuthCKACostInv (i + 1) _
        exact ⟨⟨fun q => by grind, fun q => by grind, fun q => by grind, fun q => by grind,
          fun q => by grind⟩, by grind, by grind⟩
  · simp only [OracleAdv.Timed.delay, OracleAdv.Timed.StepTimeBound,
      OracleAdv.Timed.TimeBound, OracleAdv.Timed.AllRet, smAuthCKACostInv, smCKACostInv]
    grind [smAuthCKAQueryTime]

omit [SampleableType W] [SampleableType Ct] [DecidableEq W] [DecidableEq Ct] [Fintype RK]
  [Nonempty RK] in
/-- The time of a tree that draws `x` from `μ` at the step cost `c x` and then runs a
step-prefixed tree `S x` of time at most `B`, returning a function `f` of its output. -/
private theorem timeBound_rand_cost_bind_ret {D R X β γ : Type} (μ : PMF X) (c : X → ℕ)
    (S : X → ℕ × OracleAdv.Timed D R β) (f : β → γ) {K B : ℕ} (hc : ∀ x, c x ≤ K)
    (hS : ∀ x, OracleAdv.Timed.StepTimeBound (S x) B) :
    OracleAdv.Timed.StepTimeBound (0, OracleAdv.Timed.rand μ
      (fun x => c x + (S x).1 + ((S x).2.bind fun r => (0, OracleAdv.Timed.ret (f r))).1)
      fun x => ((S x).2.bind fun r => (0, OracleAdv.Timed.ret (f r))).2) (K + B + 1) := by
  refine ⟨Nat.zero_le _, by dsimp only; omega, fun x => ?_⟩
  obtain ⟨h1, h2⟩ := hS x
  obtain ⟨h3, h4⟩ := OracleAdv.Timed.timeBound_bind (n := 0) h2
    (f := fun r => (0, OracleAdv.Timed.ret (f r))) fun _ => ⟨le_refl _, trivial⟩
  have := hc x
  refine ⟨by dsimp only; omega, h4.mono ?_⟩
  dsimp only; omega

/-- **Time of `smAuthCKARed`.** For a costed interaction of time at most `T`, at most `q`
queries, deliveries whose positions in the receiving chain sum to at most `J` on every path, and
call cost at most `a`, root steps of cost at most `r`, chain steps of cost at most `g`,
encryptions of cost at most `e` and decryptions of cost at most `dd`, the derived costed tree of
`smAuthCKARed` has time at most `T + 2 (g + 4) J + ∑_{j < q} smAuthCKAQueryTime r g e dd j + a + 7`.
A delivery at the position `j` walks the receiving chain `j` steps twice, which is the term in
`J`; the other costs of the `j`-th query are linear in `j`. -/
theorem smAuthCKARed.timeBound_timed (R : PRGDef (RK × Key) (RK × Sa)) (G : PRGDef Sa (W × Sa))
    (D : AEADDef W Ct) (ΔFS ΔPCS : ℕ) (tStar : PMF ℕ)
    (play : ℕ → Msg → OracleAdv.Timed (SMAuthQuery W Ct) (SMAuthAns Msg Ct (SMPartySt Sc RK Sa) W)
      Bool)
    (playCost : ℕ → Msg → ℕ) (k : ℕ) (pub : Msg) (rCost : RK × Key → ℕ)
    (eCost : W → W → W → ℕ) (gCost : Sa → ℕ) (dCost : W → Ct → W → ℕ) {T q J a r g e dd : ℕ}
    (hA : ∀ t g, (play t g).TimeBound T) (hq : ∀ t g, (play t g).erase.IsQueryBound q)
    (hJ : ∀ t g, (play t g).erase.IsQueryBoundBy smAuthDeliverIdx J)
    (ha : ∀ t g, playCost t g ≤ a) (hr : ∀ x, rCost x ≤ r) (he : ∀ k m a, eCost k m a ≤ e)
    (hg : ∀ s, gCost s ≤ g) (hd : ∀ k c a, dCost k c a ≤ dd) :
    OracleAdv.Timed.StepTimeBound
      (smAuthCKARed.tree.timed (Key := Key) (Rand := Rand) R G D ΔFS ΔPCS tStar play playCost k
        pub rCost eCost gCost dCost)
      (T + 2 * (g + 4) * J + ∑ j ∈ Finset.range q, smAuthCKAQueryTime r g e dd j + a + 7) := by
  unfold smAuthCKARed.tree.timed smAuthCKATree.timed
  refine (OracleAdv.Timed.stepTimeBound_delay (timeBound_rand_zero _ _ fun t =>
    timeBound_rand_cost_bind_ret (K := 4 + a)
      (B := T + 2 * (g + 4) * J + ∑ j ∈ Finset.range q, smAuthCKAQueryTime r g e dd j) _ _ _ _
      (fun _ => by have := ha t pub; omega) fun rk => ?_)).mono (by omega)
  unfold OracleAdv.Timed.simulateHat
  refine (OracleAdv.Timed.timeBound_simulate_inv_of_isQueryBoundBy _
    (fun d => 2 * (g + 4) * smAuthDeliverIdx d) (smAuthCKAQueryTime r g e dd)
    (fun i ŝ => smAuthCKACostInv i ŝ)
    (fun i ŝ d h => smAuthCKAImpl.timed_bound (Sc := Sc) (Msg := Msg) (Rand := Rand) R G D ΔFS
      ΔPCS t k _ d rCost eCost gCost dCost hr he hg hd i ŝ.1.1.1 ŝ.1.1.2 ŝ.1.2 h.1 h.2.1 h.2.2)
    (hA t pub) ((hJ t pub).mul_left _) (hq t pub) 0 _ ?_).mono ?_
  · simp [smAuthCKACostInv, smCKACostInv, SMAuthAux.init]
  · simp only [Nat.zero_add, le_refl]

end AuthCKATime

end CatCrypt.Crypto.Messaging
