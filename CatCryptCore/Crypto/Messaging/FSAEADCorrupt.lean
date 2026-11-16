/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.SMCorrupt
public import CatCryptCore.Crypto.OracleAdversaryEager
public import CatCryptCore.Crypto.KDFLazyEager
public import CatCryptCore.Crypto.HybridArgument

/-!
# FS-AEAD with corruption from PRG and AEAD security

The FS-AEAD game with corruption `fsaead_corrupt_game` (Alwen, Coretti and Dodis, §4.3) gives
the adversary encryptions under the keys of the chain of the generator `G : PRGDef Sa (W × Sa)`
from a uniform state, one challenge (real or uniform ciphertext) at an adaptively chosen
position, and the current state of the chain on corruption; a challenge after a corruption is
refused, and a corruption after the challenge is answered.

The proof runs the game against a lazy oracle (`fsStepOracle`), whose state `FSLzSt` holds the
current state of the chain as an option: `none` is a uniform state that the adversary has not
seen. The hybrid `i` (`fsHybStep G i`) answers the steps of the chain at the positions below `i`
from a state not seen by uniform keys, and keeps the state unseen; the other steps run `G`. The
hybrid `0` is the game (`fsaead_corrupt_game_eq`). The hybrids `i` and `i + 1` differ at the
step of the position `i` from an unseen state, which is `G` of a uniform seed in the first and a
uniform pair in the second; the PRG reduction `fsCorrPRGRed` embeds its challenge there
(`fsHyb_eq_prgReal`, `fsHyb_succ_eq_prgIdeal`). For an adversary with at most `q` encryption and
challenge queries, the hybrid `q` answers every step from an unseen state by a uniform key
(`fsHyb_eq_fsFin`), so the challenge key is uniform and used once, and the AEAD reduction
`fsCorrAEADRed` asks the challenge as its encryption query (`fsFin_false_eq`,
`fsFin_true_eq`). The challenge position is not guessed.

## Main definitions

* `FSLzSt`, `fsStepOracle` — the lazy FS-AEAD oracle with given steps of the chain
* `fsHybStep`, `fsHyb` — the hybrids over the positions of the chain
* `fsCorrPRGRed` — the PRG reduction of the position `i`
* `fsCorrAEADImpl`, `fsCorrAEADRed` — the AEAD reduction
* `fsCost` — the cost of a query: `1` for encryptions and challenges, `0` for corruptions

## Main results

* `fsaead_corrupt_advantage_le` — for every adversary `B` with at most `q` encryption and
  challenge queries, the FS-AEAD advantage with corruption is at most the PRG advantages of
  `fsCorrPRGRed G D b i B` for `i < q` and both challenge bits `b`, plus the AEAD advantage of
  `fsCorrAEADRed G D B`

## References

* J. Alwen, S. Coretti, Y. Dodis, *The Double Ratchet: Security Notions, Proofs, and
  Modularization for the Signal Protocol*, EUROCRYPT 2019, §4.3
-/

set_option autoImplicit false

@[expose] public section

namespace CatCrypt.Crypto.Messaging

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Assumptions
open scoped ENNReal

/-! ## The lazy oracle -/

section Lazy

variable {Sa W Ct AD : Type} [SampleableType W] [SampleableType Ct] [Fintype Sa] [Nonempty Sa]

/-- The state of the lazy FS-AEAD oracle: the current state of the chain (`none` for a uniform
state that the adversary has not seen), the position of the next key, and the flags of the
challenge and of the corruption. -/
structure FSLzSt (Sa : Type) where
  /-- The current state of the chain; `none` is a uniform state not seen by the adversary. -/
  cur : Option Sa
  /-- The position of the next key of the chain. -/
  pos : ℕ
  /-- The challenge has been asked. -/
  done : Bool
  /-- The sender has been corrupted. -/
  corr : Bool

/-- The initial state of the lazy oracle: an unseen uniform state at position `0`. -/
def fsLzInit : FSLzSt Sa := ⟨none, 0, false, false⟩

/-- The distribution of the current state: uniform for `none`. -/
noncomputable def fsCurDist : Option Sa → PMF Sa
  | none => PMF.uniformFintype Sa
  | some s => PMF.pure s

/-- A step of the generator `G` from the current state. -/
noncomputable def fsGStep (G : PRGDef Sa (W × Sa)) (h : FSLzSt Sa) : PMF (W × FSLzSt Sa) :=
  (fsCurDist h.cur).map fun s =>
    ((G.stretch s).1, { h with cur := some (G.stretch s).2, pos := h.pos + 1 })

/-- An ideal step: a uniform key, and the next state unseen. -/
noncomputable def fsUStep (h : FSLzSt Sa) : PMF (W × FSLzSt Sa) :=
  (PMF.uniformFintype W).map fun k => (k, { h with cur := none, pos := h.pos + 1 })

/-- The step of the hybrid `i`: ideal from an unseen state at a position below `i`, a step of
`G` otherwise. -/
noncomputable def fsHybStep (G : PRGDef Sa (W × Sa)) (i : ℕ) (h : FSLzSt Sa) :
    PMF (W × FSLzSt Sa) :=
  if h.cur.isNone && decide (h.pos < i) then fsUStep h else fsGStep G h

/-- The step of the PRG reduction of the position `i` with the challenge `y`: from an unseen
state at the position `i` the key `y.1` and the next state `y.2`; the step of the hybrid `i`
otherwise. -/
noncomputable def fsRedStep (G : PRGDef Sa (W × Sa)) (i : ℕ) (y : W × Sa) (h : FSLzSt Sa) :
    PMF (W × FSLzSt Sa) :=
  if h.cur.isNone && h.pos == i then PMF.pure (y.1, { h with cur := some y.2, pos := h.pos + 1 })
  else fsHybStep G i h

/-- The step of the PRG reduction of the position `i` at a uniform challenge. -/
noncomputable def fsHybStepU (G : PRGDef Sa (W × Sa)) (i : ℕ) (h : FSLzSt Sa) :
    PMF (W × FSLzSt Sa) :=
  (PMF.uniformFintype (W × Sa)).bind fun y => fsRedStep G i y h

/-- The encryption step of the final hybrid: ideal from an unseen state, `G` otherwise. -/
noncomputable def fsFinStep (G : PRGDef Sa (W × Sa)) (h : FSLzSt Sa) : PMF (W × FSLzSt Sa) :=
  if h.cur.isNone then fsUStep h else fsGStep G h

/-- The step with the fixed key `key` and the next state unseen. -/
noncomputable def fsFixStep (key : W) (h : FSLzSt Sa) : PMF (W × FSLzSt Sa) :=
  PMF.pure (key, { h with cur := none, pos := h.pos + 1 })

/-- The lazy FS-AEAD oracle with the encryption step `stE` and the challenge step `stC`: `enc m`
encrypts under the key of `stE`; `chall m`, once and before a corruption, gives the challenge
ciphertext under the key of `stC`; `corrupt` draws the current state and reveals it. -/
noncomputable def fsStepOracle (D : AEADDef W Ct AD) (ideal : Bool)
    (stE stC : FSLzSt Sa → PMF (W × FSLzSt Sa)) (h : FSLzSt Sa) :
    FSQuery W AD → PMF (FSAns Sa Ct × FSLzSt Sa)
  | .enc m => (stE h).map fun x => (.ct (D.encrypt x.1 m.1 m.2), x.2)
  | .chall m =>
    if !h.done && !h.corr then
      (stC h).bind fun x => (challCt D ideal x.1 m).map fun c => (.ct c, { x.2 with done := true })
    else PMF.pure (.none, h)
  | .corrupt => (fsCurDist h.cur).map fun s => (.state s, { h with cur := some s, corr := true })

/-- The output distribution of the hybrid `i`. -/
noncomputable def fsHyb (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct AD) (ideal : Bool) (i : ℕ)
    (A : OracleAdv (FSQuery W AD) (FSAns Sa Ct) Bool) : PMF Bool :=
  (OracleAdv.run (fsStepOracle D ideal (fsHybStep G i) (fsHybStep G i)) A fsLzInit).map
    Prod.fst

/-- The output distribution of the final hybrid: every step from an unseen state and every
challenge has a uniform key. -/
noncomputable def fsFin (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct AD) (ideal : Bool)
    (A : OracleAdv (FSQuery W AD) (FSAns Sa Ct) Bool) : PMF Bool :=
  (OracleAdv.run (fsStepOracle D ideal (fsFinStep G) fsUStep) A fsLzInit).map Prod.fst

/-- The cost of a query: `1` for encryptions and challenges, `0` for corruptions. -/
def fsCost : FSQuery W AD → ℕ
  | .enc _ => 1
  | .chall _ => 1
  | .corrupt => 0

/-- The state with the current state of the chain drawn when the position is at least `n`. -/
noncomputable def fsLift (n : ℕ) (h : FSLzSt Sa) : PMF (FSLzSt Sa) :=
  if n ≤ h.pos then (fsCurDist h.cur).map fun s => { h with cur := some s } else PMF.pure h

end Lazy

/-! ## The reductions -/

section Red

variable {Sa W Ct AD : Type} [SampleableType W] [SampleableType Ct] [Fintype Sa] [Nonempty Sa]

/-- **The PRG reduction of the position `i`.** On the challenge `y` of the PRG game it runs `A`
against the lazy oracle whose step at the position `i` from an unseen state is `y`. -/
noncomputable def fsCorrPRGRed (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct AD) (ideal : Bool)
    (i : ℕ) (A : OracleAdv (FSQuery W AD) (FSAns Sa Ct) Bool) : PRG_Adversary (W × Sa) :=
  fun y => liftPMF ((OracleAdv.run (fsStepOracle D ideal (fsRedStep G i y) (fsRedStep G i y))
    A fsLzInit).map Prod.fst)

/-- The simulator of the AEAD reduction: encryptions and corruptions as in the final hybrid,
and the challenge as the encryption query of the authenticated-encryption game. -/
noncomputable def fsCorrAEADImpl (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct AD)
    (h : FSLzSt Sa) : FSQuery W AD →
      OracleAdv (AEAD_CCA_Query W Ct AD) (AEAD_CCA_Answer W Ct) (FSAns Sa Ct × FSLzSt Sa)
  | .enc m => .rand (fsFinStep G h) fun x => .ret (.ct (D.encrypt x.1 m.1 m.2), x.2)
  | .chall m =>
    if !h.done && !h.corr then
      .query (.inl m) fun a => match a with
        | .inl c => .ret (.ct c, { h with cur := none, pos := h.pos + 1, done := true })
        | .inr _ => .ret (.none, h)
    else .ret (.none, h)
  | .corrupt =>
    .rand (fsCurDist h.cur) fun s => .ret (.state s, { h with cur := some s, corr := true })

/-- **The AEAD reduction**: `A` run against `fsCorrAEADImpl`. -/
noncomputable def fsCorrAEADRed (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct AD)
    (A : OracleAdv (FSQuery W AD) (FSAns Sa Ct) Bool) : AEAD_CCA_Adversary W Ct AD :=
  (OracleAdv.simulate (fsCorrAEADImpl G D) A fsLzInit).bind fun x => .ret x.1

/-- The authenticated-encryption oracles that answer every encryption query by a fresh uniform
ciphertext, with the log `((pt, ad), ct)` as state; decryption answers from the log. On an
empty log it answers the first encryption query as `aeadIdealOracle`. -/
noncomputable def fsFreshOracle [DecidableEq AD] (log : List ((W × AD) × Ct)) :
    AEAD_CCA_Query W Ct AD → PMF (AEAD_CCA_Answer W Ct × List ((W × AD) × Ct))
  | .inl (pt, ad) => (PMF.uniformFintype Ct).map fun ct => (.inl ct, ((pt, ad), ct) :: log)
  | .inr (ct, ad) => PMF.pure (.inr (aeadLogDecrypt log ct ad), log)

end Red

/-! ## The hops -/

section Hops

variable {Sa W Ct AD : Type} [SampleableType W] [SampleableType Ct] [Fintype Sa] [Nonempty Sa]

omit [SampleableType W] in
/-- A seen current state is kept by `fsLift`. -/
theorem fsLift_of_some (n : ℕ) (h : FSLzSt Sa) (s : Sa) (hs : h.cur = some s) :
    fsLift n h = PMF.pure h := by
  cases h
  simp_all [fsLift, fsCurDist, PMF.pure_map]

omit [SampleableType W] in
/-- `fsLift` changes the current state only. -/
theorem fsLift_support (n : ℕ) (h h' : FSLzSt Sa) (hh : h' ∈ (fsLift n h).support) :
    h'.done = h.done ∧ h'.corr = h.corr ∧ h'.pos = h.pos := by
  unfold fsLift at hh
  split_ifs at hh
  · obtain ⟨s, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hh
    exact ⟨rfl, rfl, rfl⟩
  · rw [PMF.mem_support_pure_iff] at hh
    subst hh
    exact ⟨rfl, rfl, rfl⟩

omit [SampleableType W] in
/-- `fsLift` commutes with setting the challenge flag. -/
theorem fsLift_done (n : ℕ) (h : FSLzSt Sa) :
    fsLift n { h with done := true } = (fsLift n h).map fun h' => { h' with done := true } := by
  unfold fsLift
  split_ifs <;> simp [PMF.map_comp, Function.comp_def, PMF.pure_map]

/-- **Lifting along the lazy oracle.** If the steps of two lazy oracles are related by
`fsLift n`, so are their runs. -/
theorem fsStepOracle_lift (D : AEADDef W Ct AD) (ideal : Bool) (n : ℕ)
    (stE stC stE' stC' : FSLzSt Sa → PMF (W × FSLzSt Sa))
    (hE : ∀ h, (fsLift n h).bind stE' =
      (stE h).bind fun x => (fsLift n x.2).map fun h' => (x.1, h'))
    (hC : ∀ h, (fsLift n h).bind stC' =
      (stC h).bind fun x => (fsLift n x.2).map fun h' => (x.1, h'))
    (A : OracleAdv (FSQuery W AD) (FSAns Sa Ct) Bool) (h : FSLzSt Sa) :
    ((fsLift n h).bind fun h' => (OracleAdv.run (fsStepOracle D ideal stE' stC') A h').map
      Prod.fst) = (OracleAdv.run (fsStepOracle D ideal stE stC) A h).map Prod.fst := by
  refine OracleAdv.run_map_fst_eq_of_kernel _ _ (fsLift n) (fun _ => True) (fun h d _ => ?_)
    (fun _ _ _ _ _ => trivial) A h trivial
  cases d with
  | enc m =>
    simp only [fsStepOracle]
    rw [← PMF.map_bind, hE h, PMF.map_bind, PMF.bind_map]
    simp [PMF.map_comp, Function.comp_def]
  | chall m =>
    rw [PMF.bind_congr_support (fsLift n h) _ (fun s' =>
      if !h.done && !h.corr then (stC' s').bind fun x => (challCt D ideal x.1 m).map
        fun c => (FSAns.ct c, { x.2 with done := true }) else PMF.pure (.none, s'))
      fun s' hs' => by simp [fsStepOracle, (fsLift_support n h s' hs').1,
        (fsLift_support n h s' hs').2.1]]
    by_cases hc : (!h.done && !h.corr) = true
    · simp only [hc, ite_true, fsStepOracle]
      rw [← PMF.bind_bind, hC h, PMF.bind_bind, PMF.bind_bind]
      refine congrArg _ (funext fun x => ?_)
      rw [PMF.bind_map, PMF.bind_map]
      simp only [Function.comp_def, fsLift_done]
      simp only [PMF.map, PMF.bind_bind, PMF.pure_bind, Function.comp_def]
      exact PMF.bind_comm _ _ _
    · simp only [hc, fsStepOracle, Bool.false_eq_true, ite_false, PMF.pure_bind]
      rfl
  | corrupt =>
    rcases h with ⟨_ | c, p, dn, co⟩ <;> by_cases hn : n ≤ p <;>
      simp [fsStepOracle, fsLift, hn, Function.comp_def, fsCurDist, PMF.map]

/-- The game is the hybrid `0`. -/
theorem fsaead_corrupt_game_eq (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct AD) (ideal : Bool)
    (A : OracleAdv (FSQuery W AD) (FSAns Sa Ct) Bool) :
    fsaead_corrupt_game G D ideal A = liftPMF (fsHyb G D ideal 0 A) := by
  have h0 : fsHybStep (W := W) G 0 = fsGStep G := funext fun h => by simp [fsHybStep]
  have hA : ∀ sa : Sa, (OracleAdv.run (fsOracle G D ideal) A ⟨sa, sa, false, false⟩).map
      Prod.fst = (OracleAdv.run (fsStepOracle D ideal (fsHybStep G 0) (fsHybStep G 0)) A
        ⟨some sa, 0, false, false⟩).map Prod.fst := fun sa => by
    have := OracleAdv.run_map_fst_eq_of_kernel
      (fsStepOracle D ideal (fsHybStep G 0) (fsHybStep G 0)) (fsOracle G D ideal)
      (fun h => (fsCurDist h.cur).map fun s => (⟨s, sa, h.done, h.corr⟩ : FSSt Sa))
      (fun _ => True) (fun h d _ => ?_) (fun _ _ _ _ _ => trivial) A ⟨some sa, 0, false, false⟩
      trivial
    · simpa [fsCurDist, PMF.pure_map] using this
    · rw [h0]
      rcases h with ⟨_ | c, p, _ | _, _ | _⟩ <;> cases d <;>
        simp [fsStepOracle, fsOracle, fsGStep, fsCurDist, PMF.map, Function.comp_def]
  have hB := fsStepOracle_lift D ideal 0 (fsHybStep G 0) (fsHybStep G 0) (fsHybStep G 0)
    (fsHybStep G 0) (fun h => ?_) (fun h => ?_) A fsLzInit
  · rw [fsaead_corrupt_game, fsHyb, ← hB]
    simp [fsLift, fsLzInit, fsCurDist, hA, PMF.bind_map, Function.comp_def]
  all_goals
    rw [h0]
    rcases h with ⟨_ | c, p, dn, co⟩ <;>
      simp [fsLift, fsGStep, fsCurDist, PMF.map, Function.comp_def]

/-- The queries that run a step of the chain from an unseen state at the position `i`. -/
def fsUses (i : ℕ) (h : FSLzSt Sa) : FSQuery W AD → Prop
  | .enc _ => h.cur = none ∧ h.pos = i
  | .chall _ => h.cur = none ∧ h.pos = i ∧ (!h.done && !h.corr) = true
  | .corrupt => False

/-- The lazy oracle with steps that advance the position never moves the position back. -/
theorem fsStepOracle_pos_le (D : AEADDef W Ct AD) (ideal : Bool)
    (st : FSLzSt Sa → PMF (W × FSLzSt Sa))
    (hst : ∀ h, ∀ x ∈ (st h).support, x.2.pos = h.pos + 1) (h : FSLzSt Sa) (d : FSQuery W AD)
    (z : FSAns Sa Ct × FSLzSt Sa) (hz : z ∈ (fsStepOracle D ideal st st h d).support) :
    h.pos ≤ z.2.pos := by
  cases d with
  | enc m =>
    obtain ⟨x, hx, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hz
    have := hst h x hx
    simp only
    omega
  | chall m =>
    simp only [fsStepOracle] at hz
    split_ifs at hz
    · obtain ⟨x, hx, hz⟩ := (PMF.mem_support_bind_iff _ _ _).1 hz
      obtain ⟨c, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hz
      have := hst h x hx
      simp only
      omega
    · rw [PMF.mem_support_pure_iff] at hz
      subst hz
      exact le_rfl
  | corrupt =>
    obtain ⟨s, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hz
    exact le_rfl

/-- **Eager draw of the step at the position `i`.** Let the steps `st₂ y` agree with `st` except
from an unseen state at the position `i`, where `st` is `st₂ y` for `y` drawn from `ν`. From a
state at a position at most `i`, a run against the lazy oracle of `st` is the run against the
lazy oracle of `st₂ y` for `y` drawn from `ν` first. -/
theorem fsStepOracle_eager {Y : Type} (D : AEADDef W Ct AD) (ideal : Bool) (i : ℕ) (ν : PMF Y)
    (st : FSLzSt Sa → PMF (W × FSLzSt Sa)) (st₂ : Y → FSLzSt Sa → PMF (W × FSLzSt Sa))
    (hno : ∀ y h, ¬ (h.cur = none ∧ h.pos = i) → st₂ y h = st h)
    (huse : ∀ h, h.cur = none → h.pos = i → st h = ν.bind fun y => st₂ y h)
    (hst : ∀ h, ∀ x ∈ (st h).support, x.2.pos = h.pos + 1)
    (hst₂ : ∀ y h, ∀ x ∈ (st₂ y h).support, x.2.pos = h.pos + 1)
    (A : OracleAdv (FSQuery W AD) (FSAns Sa Ct) Bool) (h : FSLzSt Sa) (hh : h.pos ≤ i) :
    (OracleAdv.run (fsStepOracle D ideal st st) A h).map Prod.fst =
      ν.bind fun y => (OracleAdv.run (fsStepOracle D ideal (st₂ y) (st₂ y)) A h).map
        Prod.fst := by
  rw [OracleAdv.run_eager ν _ (fun y => fsStepOracle D ideal (st₂ y) (st₂ y))
    (fun h => h.pos ≤ i) (fsUses i) ?_ ?_ ?_ ?_ ?_ A h hh, PMF.map_bind]
  · intro y h d hu
    cases d with
    | enc m =>
      simp only [fsStepOracle, hno y h hu]
    | chall m =>
      by_cases hc : (!h.done && !h.corr) = true
      · have hu' : ¬ (h.cur = none ∧ h.pos = i) := fun h' => hu ⟨h'.1, h'.2, hc⟩
        simp only [fsStepOracle, hno y h hu']
      · simp only [fsStepOracle, hc, Bool.false_eq_true, ite_false]
    | corrupt => rfl
  · intro h d _ hu
    cases d with
    | enc m =>
      simp only [fsStepOracle, huse h hu.1 hu.2, PMF.map_bind]
    | chall m =>
      simp only [fsStepOracle, hu.2.2, ite_true, huse h hu.1 hu.2.1, PMF.bind_bind]
    | corrupt => exact hu.elim
  · intro y h d _ hu z hz
    simp only [not_le]
    cases d with
    | enc m =>
      obtain ⟨x, hx, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hz
      have := hst₂ y h x hx
      have := hu.2
      simp only
      omega
    | chall m =>
      simp only [fsStepOracle, hu.2.2, ite_true] at hz
      obtain ⟨x, hx, hz⟩ := (PMF.mem_support_bind_iff _ _ _).1 hz
      obtain ⟨c, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hz
      have := hst₂ y h x hx
      have := hu.2.1
      simp only
      omega
    | corrupt => exact hu.elim
  · intro h d hh z hz
    have := fsStepOracle_pos_le D ideal st hst h d z hz
    omega
  · intro h d hh hu
    cases d <;> simp_all [fsUses]

omit [SampleableType W] in
/-- A step of `G` advances the position. -/
theorem fsGStep_pos (G : PRGDef Sa (W × Sa)) (h : FSLzSt Sa) :
    ∀ x ∈ (fsGStep G h).support, x.2.pos = h.pos + 1 := fun x hx => by
  obtain ⟨s, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hx
  rfl

omit [Fintype Sa] [Nonempty Sa] in
/-- An ideal step advances the position. -/
theorem fsUStep_pos (h : FSLzSt Sa) : ∀ x ∈ (fsUStep (W := W) h).support, x.2.pos = h.pos + 1 :=
  fun x hx => by
  obtain ⟨s, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hx
  rfl

/-- A step of the hybrid advances the position. -/
theorem fsHybStep_pos (G : PRGDef Sa (W × Sa)) (i : ℕ) (h : FSLzSt Sa) :
    ∀ x ∈ (fsHybStep G i h).support, x.2.pos = h.pos + 1 := fun x hx => by
  unfold fsHybStep at hx
  split_ifs at hx
  · exact fsUStep_pos h x hx
  · exact fsGStep_pos G h x hx

/-- A step of the PRG reduction advances the position. -/
theorem fsRedStep_pos (G : PRGDef Sa (W × Sa)) (i : ℕ) (y : W × Sa) (h : FSLzSt Sa) :
    ∀ x ∈ (fsRedStep G i y h).support, x.2.pos = h.pos + 1 := fun x hx => by
  unfold fsRedStep at hx
  split_ifs at hx
  · rw [PMF.mem_support_pure_iff] at hx
    subst hx
    rfl
  · exact fsHybStep_pos G i h x hx

/-- Off the step at the position `i` from an unseen state, the step of the PRG reduction is the
step of the hybrid `i`. -/
theorem fsRedStep_of_not (G : PRGDef Sa (W × Sa)) (i : ℕ) (y : W × Sa) (h : FSLzSt Sa)
    (hh : ¬ (h.cur = none ∧ h.pos = i)) : fsRedStep G i y h = fsHybStep G i h := by
  unfold fsRedStep
  split_ifs with h'
  · exfalso
    apply hh
    cases hc : h.cur <;> simp_all
  · rfl

/-- The hybrid `i` is the PRG reduction of the position `i` at a real challenge. -/
theorem fsHyb_eq_prgReal (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct AD) (ideal : Bool) (i : ℕ)
    (A : OracleAdv (FSQuery W AD) (FSAns Sa Ct) Bool) :
    fsHyb G D ideal i A = (PMF.uniformFintype Sa).bind fun s =>
      (OracleAdv.run (fsStepOracle D ideal (fsRedStep G i (G.stretch s))
        (fsRedStep G i (G.stretch s))) A fsLzInit).map Prod.fst := by
  rw [fsHyb, fsStepOracle_eager D ideal i ((PMF.uniformFintype Sa).map G.stretch)
    (fsHybStep G i) (fsRedStep G i) (fun y h hh => fsRedStep_of_not G i y h hh) ?_
    (fsHybStep_pos G i) (fsRedStep_pos G i) A fsLzInit (Nat.zero_le _), PMF.bind_map]
  · rfl
  · intro h hc hp
    simp [fsHybStep, fsRedStep, fsGStep, hc, hp, fsCurDist, PMF.map, Function.comp_def]

/-- The hybrid `i + 1` is the PRG reduction of the position `i` at a uniform challenge. -/
theorem fsHyb_succ_eq_prgIdeal (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct AD) (ideal : Bool)
    (i : ℕ) (A : OracleAdv (FSQuery W AD) (FSAns Sa Ct) Bool) :
    fsHyb G D ideal (i + 1) A = (PMF.uniformFintype (W × Sa)).bind fun y =>
      (OracleAdv.run (fsStepOracle D ideal (fsRedStep G i y) (fsRedStep G i y)) A
        fsLzInit).map Prod.fst := by
  have hoff : ∀ h : FSLzSt Sa, ¬ (h.cur = none ∧ h.pos = i) →
      fsHybStepU G i h = fsHybStep G i h := fun h hh => by
    simp [fsHybStepU, fsRedStep_of_not G i _ h hh]
  have hst : ∀ h : FSLzSt Sa, ∀ x ∈ (fsHybStepU G i h).support, x.2.pos = h.pos + 1 :=
    fun h x hx => by
      obtain ⟨y, -, hy⟩ := (PMF.mem_support_bind_iff _ _ _).1 hx
      exact fsRedStep_pos G i y h x hy
  have hlift := fsStepOracle_lift D ideal (i + 1) (fsHybStep G (i + 1)) (fsHybStep G (i + 1))
    (fsHybStepU G i) (fsHybStepU G i) (fun h => ?_) (fun h => ?_) A fsLzInit
  · rw [fsHyb, ← hlift, show fsLift (i + 1) (fsLzInit : FSLzSt Sa) = PMF.pure fsLzInit by
      simp [fsLift, fsLzInit], PMF.pure_bind, fsStepOracle_eager D ideal i
      (PMF.uniformFintype (W × Sa)) (fsHybStepU G i) (fsRedStep G i)
      (fun y h hh => (fsRedStep_of_not G i y h hh).trans (hoff h hh).symm) (fun h _ _ => rfl) hst
      (fsRedStep_pos G i) A fsLzInit (Nat.zero_le _)]
  all_goals
    rcases h with ⟨_ | c, p, dn, co⟩
    · rcases lt_trichotomy p i with hp | rfl | hp
      · rw [show fsLift (i + 1) (⟨none, p, dn, co⟩ : FSLzSt Sa) = PMF.pure ⟨none, p, dn, co⟩ by
          simp [fsLift]; omega, PMF.pure_bind, hoff ⟨none, p, dn, co⟩ (by simp; omega)]
        simp [fsLift, fsHybStep, fsUStep, hp, show ¬ i ≤ p by omega,
          PMF.map, Function.comp_def, show p < i + 1 by omega]
      · rw [show fsLift (p + 1) (⟨none, p, dn, co⟩ : FSLzSt Sa) = PMF.pure ⟨none, p, dn, co⟩ by
          simp [fsLift], PMF.pure_bind]
        simp [fsLift, fsHybStepU, fsRedStep, fsHybStep, fsUStep, fsCurDist,
          PMF.uniform_prod_eq_bind, PMF.map, Function.comp_def, PMF.bind_bind]
      · rw [show fsLift (i + 1) ⟨none, p, dn, co⟩ = (PMF.uniformFintype Sa).map fun s =>
          (⟨some s, p, dn, co⟩ : FSLzSt Sa) by simp [fsLift, fsCurDist, show i + 1 ≤ p by omega]]
        simp [fsLift, fsHybStepU, fsRedStep, fsHybStep, fsGStep, fsCurDist, PMF.map,
          Function.comp_def, show ¬ p < i by omega, show ¬ p < i + 1 by omega, PMF.bind_bind]
    · rw [fsLift_of_some _ _ c rfl, PMF.pure_bind, hoff ⟨some c, p, dn, co⟩ (by simp)]
      simp [fsLift, fsHybStep, fsGStep, fsCurDist, PMF.map, Function.comp_def]

/-- A hybrid step is the PRG game of `fsCorrPRGRed`. -/
theorem advantage_fsHyb_succ (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct AD) (ideal : Bool)
    (i : ℕ) (A : OracleAdv (FSQuery W AD) (FSAns Sa Ct) Bool) :
    Advantage (liftPMF (fsHyb G D ideal i A)) (liftPMF (fsHyb G D ideal (i + 1) A)) =
      PRG_Advantage G (fsCorrPRGRed G D ideal i A) := by
  unfold PRG_Advantage AdvantageA
  rw [fsHyb_eq_prgReal, fsHyb_succ_eq_prgIdeal, ← liftPMF_bind_liftPMF, ← liftPMF_bind_liftPMF,
    ← sample_eq_liftPMF, ← sample_eq_liftPMF]
  simp only [prg_real, prg_ideal, SPComp.monad_bind_eq, SPComp.bind_assoc, SPComp.pure_bind]
  rfl

/-- Below the position `q`, the step of the hybrid `q` is the encryption step of the final
hybrid. -/
theorem fsHybStep_eq_fsFinStep (G : PRGDef Sa (W × Sa)) (q : ℕ) (h : FSLzSt Sa) (hq : h.pos < q) :
    fsHybStep G q h = fsFinStep G h := by
  unfold fsHybStep fsFinStep
  cases h.cur <;> simp [hq]

/-- A call of the final hybrid advances the position by the cost of the query, and keeps the
current state unseen until a corruption. -/
theorem fsFin_support (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct AD) (ideal : Bool)
    (h : FSLzSt Sa) (d : FSQuery W AD) (hinv : h.cur.isSome → h.corr = true)
    (z : FSAns Sa Ct × FSLzSt Sa)
    (hz : z ∈ (fsStepOracle D ideal (fsFinStep G) fsUStep h d).support) :
    (z.2.pos = h.pos + fsCost d ∨ z.2 = h) ∧ (z.2.cur.isSome → z.2.corr = true) := by
  have hU : ∀ x ∈ (fsUStep (W := W) h).support,
      x.2.pos = h.pos + 1 ∧ x.2.cur = none ∧ x.2.corr = h.corr := fun x hx => by
    obtain ⟨k, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hx
    exact ⟨rfl, rfl, rfl⟩
  have hF : ∀ x ∈ (fsFinStep G h).support,
      x.2.pos = h.pos + 1 ∧ (x.2.cur.isSome → x.2.corr = true) := fun x hx => by
    unfold fsFinStep at hx
    split_ifs at hx with hc
    · obtain ⟨h1, h2, -⟩ := hU x hx
      simp [h1, h2]
    · obtain ⟨s, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hx
      exact ⟨rfl, fun _ => hinv (by grind only [Option.isNone_eq_false_iff])⟩
  cases d with
  | enc m =>
    obtain ⟨x, hx, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hz
    exact ⟨Or.inl (hF x hx).1, (hF x hx).2⟩
  | chall m =>
    simp only [fsStepOracle] at hz
    split_ifs at hz
    · obtain ⟨x, hx, hz⟩ := (PMF.mem_support_bind_iff _ _ _).1 hz
      obtain ⟨c, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hz
      obtain ⟨h1, h2, -⟩ := hU x hx
      simp [h1, h2, fsCost]
    · rw [PMF.mem_support_pure_iff] at hz
      subst hz
      exact ⟨Or.inr rfl, hinv⟩
  | corrupt =>
    obtain ⟨s, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hz
    simp [fsCost]

/-- **Runs of the hybrid `q` and the final hybrid.** From a state at a position `p` whose current
state is seen only after a corruption, an adversary with encryption and challenge queries of
total cost at most `n`, with `p + n ≤ q`, has the same runs against both oracles. -/
theorem fsHyb_run_eq_fsFin (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct AD) (ideal : Bool)
    (q : ℕ) (A : OracleAdv (FSQuery W AD) (FSAns Sa Ct) Bool) (n : ℕ) (h : FSLzSt Sa)
    (hA : A.IsQueryBoundBy fsCost n) (hn : h.pos + n ≤ q) (hinv : h.cur.isSome → h.corr = true) :
    OracleAdv.run (fsStepOracle D ideal (fsHybStep G q) (fsHybStep G q)) A h =
      OracleAdv.run (fsStepOracle D ideal (fsFinStep G) fsUStep) A h := by
  induction A generalizing n h with
  | ret a => rfl
  | rand p k ih =>
    simp only [OracleAdv.run_rand]
    exact congrArg _ (funext fun b => ih b n h (hA b) hn hinv)
  | query d k ih =>
    obtain ⟨hc, hk⟩ := hA
    have heq : fsStepOracle D ideal (fsHybStep G q) (fsHybStep G q) h d =
        fsStepOracle D ideal (fsFinStep G) fsUStep h d := by
      cases d with
      | enc m =>
        simp only [fsCost] at hc
        simp only [fsStepOracle, fsHybStep_eq_fsFinStep G q h (by omega)]
      | chall m =>
        simp only [fsCost] at hc
        by_cases hd : (!h.done && !h.corr) = true
        · have hnone : h.cur = none := by
            cases hcur : h.cur
            · rfl
            · simp_all
          simp only [fsStepOracle, hd, ite_true, fsHybStep, hnone, Option.isNone_none,
            Bool.true_and, show h.pos < q by omega, decide_true, ite_true]
        · simp only [fsStepOracle, hd, Bool.false_eq_true, ite_false]
      | corrupt => rfl
    simp only [OracleAdv.run_query]
    rw [heq]
    refine PMF.bind_congr_support _ _ _ fun z hz => ih z.1 (n - fsCost d) z.2 (hk z.1) ?_ ?_
    · rcases (fsFin_support G D ideal h d hinv z hz).1 with h1 | h1
      · rw [h1]
        omega
      · rw [h1]
        omega
    · exact (fsFin_support G D ideal h d hinv z hz).2

/-- For an adversary with at most `q` encryption and challenge queries, the hybrid `q` is the
final hybrid. -/
theorem fsHyb_eq_fsFin (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct AD) (ideal : Bool) (q : ℕ)
    (A : OracleAdv (FSQuery W AD) (FSAns Sa Ct) Bool) (hA : A.IsQueryBoundBy fsCost q) :
    fsHyb G D ideal q A = fsFin G D ideal A := by
  unfold fsHyb fsFin
  rw [fsHyb_run_eq_fsFin G D ideal q A q fsLzInit hA (by simp [fsLzInit]) (by simp [fsLzInit])]

/-- The real final hybrid is the real authenticated-encryption game of `fsCorrAEADRed`. -/
theorem fsFin_false_eq (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct AD)
    (A : OracleAdv (FSQuery W AD) (FSAns Sa Ct) Bool) :
    liftPMF (fsFin G D false A) = AEAD_CCA_Game_Real D (fsCorrAEADRed G D A) := by
  have hE := OracleAdv.run_eager (PMF.uniformFintype W)
    (fsStepOracle D false (fsFinStep G) fsUStep)
    (fun key => fsStepOracle D false (fsFinStep G) (fsFixStep key))
    (fun h : FSLzSt Sa => h.done = false)
    (fun h d => match d with
      | .chall _ => (!h.done && !h.corr) = true
      | _ => False) ?_ ?_ ?_ ?_ ?_ A fsLzInit rfl
  · have hK : ∀ key : W, (OracleAdv.run (fsStepOracle D false (fsFinStep G) (fsFixStep key)) A
        fsLzInit).map Prod.fst =
        (OracleAdv.run (aeadRealOracle D key) (fsCorrAEADRed G D A) ()).map Prod.fst := by
      intro key
      rw [fsCorrAEADRed, OracleAdv.run_simulate_fst, ← OracleAdv.run_map_state
        (OracleAdv.simOracle (fsCorrAEADImpl G D) (aeadRealOracle D key)) _ Prod.fst ?_ A
        (fsLzInit, ()), PMF.map_comp]
      · rfl
      · rintro ⟨h, u⟩ d
        cases d with
        | enc m =>
          simp [OracleAdv.simOracle, fsCorrAEADImpl, fsStepOracle, Function.comp_def, PMF.map]
        | chall m =>
          obtain ⟨pt, ad⟩ := m
          by_cases hc : (!h.done && !h.corr) = true <;>
            simp [OracleAdv.simOracle, fsCorrAEADImpl, fsStepOracle, hc, aeadRealOracle,
              fsFixStep, challCt, Function.comp_def, PMF.map]
        | corrupt =>
          simp [OracleAdv.simOracle, fsCorrAEADImpl, fsStepOracle, Function.comp_def, PMF.map]
    unfold fsFin AEAD_CCA_Game_Real
    rw [hE, PMF.map_bind]
    simp only [hK]
  · intro key h d hu
    cases d with
    | enc m => rfl
    | chall m =>
      simp only at hu
      simp [fsStepOracle, hu]
    | corrupt => rfl
  · intro h d _ hu
    cases d with
    | enc m => exact hu.elim
    | chall m =>
      simp only at hu
      simp [fsStepOracle, hu, fsUStep, fsFixStep, PMF.bind_map, Function.comp_def]
    | corrupt => exact hu.elim
  · intro key h d _ hu z hz
    cases d with
    | enc m => exact hu.elim
    | chall m =>
      simp only at hu
      simp only [fsStepOracle, hu, ite_true, fsFixStep, PMF.pure_bind] at hz
      obtain ⟨c, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hz
      simp
    | corrupt => exact hu.elim
  · intro h d hh z hz
    cases d with
    | enc m =>
      obtain ⟨x, hx, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hz
      unfold fsFinStep at hx
      split_ifs at hx
      · obtain ⟨k, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hx
        exact hh
      · obtain ⟨s, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hx
        exact hh
    | chall m =>
      simp only [fsStepOracle] at hz
      split_ifs at hz
      · obtain ⟨x, -, hz⟩ := (PMF.mem_support_bind_iff _ _ _).1 hz
        obtain ⟨c, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hz
        simp
      · rw [PMF.mem_support_pure_iff] at hz
        subst hz
        exact hh
    | corrupt =>
      obtain ⟨s, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hz
      exact hh
  · intro h d hh hu
    cases d <;> simp_all

/-- The ideal final hybrid is the ideal authenticated-encryption game of `fsCorrAEADRed`. -/
theorem fsFin_true_eq (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct AD) [DecidableEq AD]
    (A : OracleAdv (FSQuery W AD) (FSAns Sa Ct) Bool) :
    liftPMF (fsFin G D true A) = AEAD_CCA_Game_Ideal (fsCorrAEADRed G D A) := by
  let N : FSLzSt Sa × List ((W × AD) × Ct) → Prop := fun s => s.1.done = false → s.2 = []
  have hO : ∀ s d, N s →
      OracleAdv.simOracle (fsCorrAEADImpl G D) aeadIdealOracle s d =
        OracleAdv.simOracle (fsCorrAEADImpl G D) fsFreshOracle s d := by
    rintro ⟨h, log⟩ d hs
    cases d with
    | enc m => rfl
    | chall m =>
      obtain ⟨pt, ad⟩ := m
      by_cases hc : (!h.done && !h.corr) = true
      · have hl : log = [] := hs (by simp_all)
        subst hl
        simp [OracleAdv.simOracle, fsCorrAEADImpl, hc, aeadIdealOracle, fsFreshOracle,
          Function.comp_def]
      · simp [OracleAdv.simOracle, fsCorrAEADImpl, hc]
    | corrupt => rfl
  have hN : ∀ s d, N s → ∀ x ∈ (OracleAdv.simOracle (fsCorrAEADImpl G D) fsFreshOracle s d).support,
      N x.2 := by
    rintro ⟨h, log⟩ d hs x hx
    cases d with
    | enc m =>
      simp only [OracleAdv.simOracle, PMF.map, fsCorrAEADImpl, OracleAdv.run_rand,
        OracleAdv.run_ret, Function.comp_def, PMF.bind_bind, PMF.pure_bind, PMF.support_bind,
        PMF.mem_support_iff, ne_eq, PMF.support_pure, Set.mem_iUnion, Set.mem_singleton_iff,
        exists_prop, Prod.exists] at hx
      obtain ⟨a, b, hab, rfl⟩ := hx
      have hm : (a, b) ∈ (fsFinStep G h).support := hab
      have hb : b.done = h.done := by
        unfold fsFinStep at hm
        split_ifs at hm
        · obtain ⟨k, -, he⟩ := (PMF.mem_support_map_iff _ _ _).1 hm
          simp only [Prod.mk.injEq] at he
          rw [← he.2]
        · obtain ⟨s, -, he⟩ := (PMF.mem_support_map_iff _ _ _).1 hm
          simp only [Prod.mk.injEq] at he
          rw [← he.2]
      exact fun hd => hs (hb ▸ hd)
    | chall m =>
      obtain ⟨pt, ad⟩ := m
      by_cases hc : (!h.done && !h.corr) = true <;>
        simp only [OracleAdv.simOracle, PMF.map, fsCorrAEADImpl, hc, Bool.false_eq_true,
          ↓reduceIte, OracleAdv.run_query, fsFreshOracle, Function.comp_def, PMF.bind_bind,
          PMF.pure_bind, OracleAdv.run_ret, PMF.support_bind, PMF.support_uniformFintype,
          Set.top_eq_univ, Set.mem_univ, PMF.support_pure, Set.iUnion_true,
          Set.iUnion_singleton_eq_range, Set.mem_range, Set.mem_singleton_iff] at hx
      · grind
      · subst hx
        exact hs
    | corrupt =>
      simp [OracleAdv.simOracle, fsCorrAEADImpl, Function.comp_def, PMF.map] at hx
      grind
  have hmap : ∀ s d, (OracleAdv.simOracle (fsCorrAEADImpl G D) fsFreshOracle s d).map
      (Prod.map id Prod.fst) = fsStepOracle D true (fsFinStep G) fsUStep s.1 d := by
    rintro ⟨h, log⟩ d
    cases d with
    | enc m =>
      simp [OracleAdv.simOracle, fsCorrAEADImpl, fsStepOracle, Function.comp_def, PMF.map]
    | chall m =>
      obtain ⟨pt, ad⟩ := m
      by_cases hc : (!h.done && !h.corr) = true <;>
        simp [OracleAdv.simOracle, fsCorrAEADImpl, fsStepOracle, hc, fsFreshOracle, fsUStep,
          challCt, Function.comp_def, PMF.map]
    | corrupt =>
      simp [OracleAdv.simOracle, fsCorrAEADImpl, fsStepOracle, Function.comp_def, PMF.map]
  unfold fsFin AEAD_CCA_Game_Ideal
  rw [fsCorrAEADRed, OracleAdv.run_simulate_fst, OracleAdv.run_eq_run_of_inv _ _ N hN hO A
    (fsLzInit, []) (fun _ => rfl), ← OracleAdv.run_map_state _ _ Prod.fst hmap A (fsLzInit, []),
    PMF.map_comp]
  rfl

/-- **FS-AEAD with corruption from PRG and AEAD security.** For every adversary `B` with at most
`q` encryption and challenge queries, the FS-AEAD advantage with corruption is at most the PRG
advantages of the reductions `fsCorrPRGRed G D b i B` at the positions `i < q`, for the real
(`b = false`) and the ideal (`b = true`) challenge, plus the authenticated-encryption advantage
of the reduction `fsCorrAEADRed G D B`. -/
theorem fsaead_corrupt_advantage_le (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct AD)
    [DecidableEq AD] (q : ℕ) (B : OracleAdv (FSQuery W AD) (FSAns Sa Ct) Bool)
    (hB : B.IsQueryBoundBy fsCost q) :
    FSAEAD_Corrupt_Advantage G D B ≤
      ∑ i ∈ Finset.range q, PRG_Advantage G (fsCorrPRGRed G D false i B) +
        ∑ i ∈ Finset.range q, PRG_Advantage G (fsCorrPRGRed G D true i B) +
          AEAD_CCA_Advantage D (fsCorrAEADRed G D B) := by
  have hb : ∀ b, Advantage (liftPMF (fsHyb G D b 0 B)) (liftPMF (fsHyb G D b q B)) ≤
      ∑ i ∈ Finset.range q, PRG_Advantage G (fsCorrPRGRed G D b i B) := fun b => by
    refine (HybridArgument.advantage_hybrid_dep_bool (fun i => liftPMF (fsHyb G D b i B)) q).trans
      (le_of_eq (Finset.sum_congr rfl fun i _ => advantage_fsHyb_succ G D b i B))
  have hf : AEAD_CCA_Advantage D (fsCorrAEADRed G D B) =
      Advantage (liftPMF (fsHyb G D false q B)) (liftPMF (fsHyb G D true q B)) := by
    rw [fsHyb_eq_fsFin G D false q B hB, fsHyb_eq_fsFin G D true q B hB, fsFin_false_eq,
      fsFin_true_eq]
    rfl
  unfold FSAEAD_Corrupt_Advantage
  rw [fsaead_corrupt_game_eq, fsaead_corrupt_game_eq, hf]
  calc _ ≤ Advantage (liftPMF (fsHyb G D false 0 B)) (liftPMF (fsHyb G D false q B)) +
        Advantage (liftPMF (fsHyb G D false q B)) (liftPMF (fsHyb G D true 0 B)) :=
          advantage_triangle _ _ _
    _ ≤ Advantage (liftPMF (fsHyb G D false 0 B)) (liftPMF (fsHyb G D false q B)) +
        (Advantage (liftPMF (fsHyb G D false q B)) (liftPMF (fsHyb G D true q B)) +
          Advantage (liftPMF (fsHyb G D true q B)) (liftPMF (fsHyb G D true 0 B))) := by
          gcongr; exact advantage_triangle _ _ _
    _ ≤ _ := by
      rw [Advantage_sym (liftPMF (fsHyb G D true q B))]
      have h1 := hb false
      have h2 := hb true
      sum_atoms_le

end Hops

end CatCrypt.Crypto.Messaging
