/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.PAKE.CPaceBound

/-!
# Explicit bounds for the bad events of the CPace square

`cpace_realizesSim` (`CatCryptCore.Crypto.PAKE.CPaceBound`) bounds the CPace square at the
environment `Z` by `cpaceBadBound G B`, a sum of the probabilities of five bad-event experiments of
the joint world at the oracle adversary `B = OProt.oracle.reduction Z`. This file bounds the
experiments for an oracle adversary with at most `q` queries
(`UCTransparent.OProt.isQueryBound_oracle_reduction` gives `q = Z.input.rounds`).

## A bad flag along a potential

`OracleAdv.run_flagWhen_le_potential`: if every call either decreases a potential `Φ` and is bad
with probability at most `Ψ s · ε`, or is not bad and does not increase `Φ`, and every call
increases `Ψ` by at most `c`, then an adversary with at most `n` queries sets the flag with
probability at most `Φ s₀ · (Ψ s₀ + c n) · ε`.

## The frame of a step

A step of the simulated world changes the secrets and the session information of the simulator
only at a new session (`simWorldD_zs`), keeps the queried passwords, and adds at most one entry
to the table of `H2` and to the programmed inputs (`simWorldD_cands_h2`); a step of the real
world adds at most one entry to its table of `H2` (`realDet_h2`).

## Main results

* `collStepExp_le`: the new-message collision experiment has probability at most `12 q / |S|`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.OracleAdv

open CatCrypt.Core CatCrypt.Prob
open scoped ENNReal

variable {D R α σ : Type}

/-- The probability of an event under a distribution, as a sum of indicator weights. -/
theorem toOuterMeasure_eq_tsum_ite (p : PMF σ) (P : σ → Prop) [DecidablePred P] :
    p.toOuterMeasure {x | P x} = ∑' x, p x * (if P x then 1 else 0) := by
  rw [PMF.toOuterMeasure_apply]
  refine tsum_congr fun x => ?_
  by_cases h : P x <;> simp [Set.indicator, h]

/-- **A bad flag along a potential.** Let every call either decrease the potential `Φ` by at
least one and make a bad transition with probability at most `Ψ s * ε`, or make no bad transition
and not increase `Φ`, and let every call increase `Ψ` by at most `c`. An adversary with at most
`n` queries started at `s` with `Ψ s + c * n ≤ M` sets the flag with probability at most
`Φ s * (M * ε)`. -/
theorem run_flagWhen_le_potential (O : σ → D → PMF (R × σ))
    (bad : σ → D → R × σ → Prop)
    [∀ s d x, Decidable (bad s d x)] (Φ Ψ : σ → ℕ) (c M : ℕ) (ε : ℝ≥0∞)
    (hΨ : ∀ s d, ∀ x ∈ (O s d).support, Ψ x.2 ≤ Ψ s + c)
    (hstep : ∀ s d, ((∀ x ∈ (O s d).support, Φ x.2 + 1 ≤ Φ s) ∧
        (O s d).toOuterMeasure {x | bad s d x} ≤ Ψ s * ε) ∨
      ∀ x ∈ (O s d).support, ¬ bad s d x ∧ Φ x.2 ≤ Φ s)
    (A : OracleAdv D R α) (n : ℕ) (hA : A.IsQueryBound n) (s : σ) (hs : Ψ s + c * n ≤ M) :
    (run (flagWhen bad O) A (s, false)).toOuterMeasure {y | y.2.2 = true} ≤
      Φ s * (M * ε) := by
  induction A generalizing s n with
  | ret a => simp [PMF.toOuterMeasure_pure_apply]
  | rand p k ih =>
    rw [run_rand, PMF.toOuterMeasure_bind_apply]
    calc _ ≤ ∑' b, p b * (Φ s * (M * ε)) :=
          ENNReal.tsum_le_tsum fun b => by gcongr; exact ih b n (hA b) s hs
      _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  | query d k ih =>
    cases n with
    | zero => exact hA.elim
    | succ n =>
    rw [run_query, flagWhen, PMF.bind_map, PMF.toOuterMeasure_bind_apply]
    have hIH : ∀ x ∈ (O s d).support,
        (run (flagWhen bad O) (k x.1) (x.2, false)).toOuterMeasure {y | y.2.2 = true} ≤
          Φ x.2 * (M * ε) := fun x hx =>
      ih x.1 n (hA x.1) x.2 (by have := hΨ s d x hx; rw [Nat.mul_succ] at hs; omega)
    have hΨs : (Ψ s : ℝ≥0∞) ≤ M := by exact_mod_cast (Nat.le_add_right _ _).trans hs
    rcases hstep s d with ⟨hdec, hbad⟩ | hnone
    · obtain ⟨x₀, hx₀⟩ := (O s d).support_nonempty
      have hΦ : 1 ≤ Φ s := (Nat.le_add_left 1 _).trans (hdec x₀ hx₀)
      calc _ ≤ ∑' x, O s d x *
            ((if bad s d x then 1 else 0) + ((Φ s - 1 : ℕ) * (M * ε))) := by
            refine ENNReal.tsum_le_tsum fun x => ?_
            by_cases hx : x ∈ (O s d).support
            · gcongr
              by_cases hb : bad s d x
              · simp only [Function.comp_apply, hb, decide_true, Bool.false_or, ite_true]
                exact ((MeasureTheory.measure_mono (Set.subset_univ _)).trans_eq
                  ((PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr (Set.subset_univ _))).trans
                  le_self_add
              · simp only [Function.comp_apply, hb, decide_false, Bool.false_or, ite_false,
                  zero_add]
                refine (hIH x hx).trans ?_
                gcongr
                have := hdec x hx
                exact_mod_cast (by omega : Φ x.2 ≤ Φ s - 1)
            · simp [(PMF.apply_eq_zero_iff _ _).2 hx]
        _ = (O s d).toOuterMeasure {x | bad s d x} + (Φ s - 1 : ℕ) * (M * ε) := by
            simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul,
              toOuterMeasure_eq_tsum_ite]
        _ ≤ M * ε + (Φ s - 1 : ℕ) * (M * ε) := by gcongr; exact hbad.trans (by gcongr)
        _ = Φ s * (M * ε) := by
            obtain ⟨m, hm⟩ : ∃ m, Φ s = m + 1 := ⟨Φ s - 1, by omega⟩
            rw [hm, Nat.add_sub_cancel]
            push_cast
            ring
    · calc _ ≤ ∑' x, O s d x * (Φ s * (M * ε)) := by
            refine ENNReal.tsum_le_tsum fun x => ?_
            by_cases hx : x ∈ (O s d).support
            · gcongr
              simp only [Function.comp_apply, (hnone x hx).1, decide_false, Bool.false_or]
              refine (hIH x hx).trans ?_
              gcongr
              exact_mod_cast (hnone x hx).2
            · simp [(PMF.apply_eq_zero_iff _ _).2 hx]
        _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

end CatCrypt.Crypto.OracleAdv

namespace CatCrypt.Crypto.PAKE.CPaceBadReductions

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Relational
open CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCTransparent CatCrypt.Crypto.UCTransparent.FPAKE
open CatCrypt.Crypto.PAKE.DHExtract CatCrypt.Crypto.PAKE.CPaceSquare
open CatCrypt.Crypto.PAKE.CPaceHops CatCrypt.Crypto.PAKE.CPaceBad CatCrypt.NonUniform
open CatCrypt.Crypto.OracleGameUpToBad CatCrypt.Crypto.PAKE.CPaceBound
open scoped ENNReal

/-! ## The frame of a step of the simulated world -/

section Frame

variable {S W Pw K : Type} [Field S] (G : DHGroup S W)

/-- **The growth of the simulator core**: the secrets, the session information and the table of
`H1` are unchanged, the queried passwords are kept, and the table of `H2` gains at most one
entry. -/
structure CoreGrow (c c' : SimCore S W Pw K) : Prop where
  zs : c'.zs = c.zs
  info : c'.info = c.info
  td : c'.td = c.td
  cands : ∀ pw ∈ c.cands, pw ∈ c'.cands
  h2 : c'.h2 = c.h2 ∨ ∃ e, c'.h2 = e :: c.h2

theorem CoreGrow.of_eq {c c' : SimCore S W Pw K} (hzs : c'.zs = c.zs) (hinfo : c'.info = c.info)
    (htd : c'.td = c.td) (hc : c'.cands = c.cands) (hh : c'.h2 = c.h2) : CoreGrow c c' :=
  ⟨hzs, hinfo, htd, fun _ h => hc ▸ h, Or.inl hh⟩

theorem sendCore_grow [DecidableEq W] [Inhabited K] (td : Pw → Sˣ) (c : SimCore S W Pw K)
    (pid : PartyId) (m : W) :
    CoreGrow c (sendCore G td c pid m).1 := by
  unfold sendCore
  split
  · split
    · split
      · exact CoreGrow.of_eq rfl rfl rfl rfl rfl
      · dsimp only
        split <;> exact CoreGrow.of_eq rfl rfl rfl rfl rfl
    · exact CoreGrow.of_eq rfl rfl rfl rfl rfl
  · exact CoreGrow.of_eq rfl rfl rfl rfl rfl

theorem h2CoreD_grow [DecidableEq W] (td : Pw → Sˣ) (c : SimCore S W Pw K) (x : Inp W) (k : K) :
    CoreGrow c (h2CoreD G td c x k).1 := by
  unfold h2CoreD
  split
  · exact CoreGrow.of_eq rfl rfl rfl rfl rfl
  · exact ⟨rfl, rfl, rfl, fun _ h => h, Or.inr ⟨_, rfl⟩⟩

theorem advCoreD_grow [DecidableEq W] [DecidableEq Pw] [Inhabited K] (td : Pw → Sˣ)
    (c : SimCore S W Pw K) (a : RAEv Pw W) (k : K) :
    CoreGrow c (advCoreD G td c a k).1 := by
  cases a with
  | idle => exact CoreGrow.of_eq rfl rfl rfl rfl rfl
  | poll => exact CoreGrow.of_eq rfl rfl rfl rfl rfl
  | msg pid => exact CoreGrow.of_eq rfl rfl rfl rfl rfl
  | h1 pw =>
    refine ⟨rfl, rfl, rfl, fun p hp => ?_, Or.inl rfl⟩
    simp only [advCoreD]
    split_ifs <;> simp [hp]
  | h2 x =>
    simp only [advCoreD]
    split
    · exact CoreGrow.of_eq rfl rfl rfl rfl rfl
    · exact h2CoreD_grow G td c x k
  | send pid m => exact sendCore_grow G td c pid m

/-- The start of an activation on an adversary event grows the core and keeps the programmed
inputs. -/
theorem simStartD_inr [DecidableEq W] [DecidableEq Pw] [Inhabited K] (td : Pw → Sˣ)
    (s : SimSt S W Pw K) (a : RAEv Pw W) (r : S × K) :
    CoreGrow s.1 (simStartD G td s (.inr a) r).1.1 ∧ (simStartD G td s (.inr a) r).1.2 = s.2 := by
  cases a with
  | h2 x =>
    simp only [simStartD]
    split
    · exact ⟨CoreGrow.of_eq rfl rfl rfl rfl rfl, rfl⟩
    · exact ⟨advCoreD_grow G td s.1 _ r.2, rfl⟩
  | _ => exact ⟨advCoreD_grow G td s.1 _ r.2, rfl⟩

/-- The start of an activation on an honest event is `honStepD`. -/
theorem simStartD_inl [DecidableEq W] [DecidableEq Pw] [Inhabited K] (td : Pw → Sˣ)
    (s : SimSt S W Pw K) (h : LeHEv Pw) (r : S × K) :
    (simStartD G td s (.inl h) r).1 = (honStepD s.1 (honPub h) r.1, s.2) := rfl

/-- The end of an activation changes only the phase of the simulator core and adds at most one
programmed input. -/
theorem drive1D_frame [DecidableEq Pw] [Inhabited K] (s : SimSt S W Pw K) (d : Dec Pw W K)
    (t : St Pw K) (k : K × K) :
    { (drive1D fStepD simResumeV simAnswer s d t k).1.1 with phase := s.1.phase } = s.1 ∧
      ((drive1D fStepD simResumeV simAnswer s d t k).1.2 = s.2 ∨
        ∃ e, (drive1D fStepD simResumeV simAnswer s d t k).1.2 = e :: s.2) := by
  obtain ⟨⟨td, cands, info, zs, keyed, pend, h2, phase⟩, pr⟩ := s
  rcases d with g | o
  · cases phase <;> simp [drive1D, simResumeV, simAnswer]
  · simp [drive1D]

/-- **The frame of a step of the simulated world**: the core after the step is the core after
the start of the activation up to its phase, and the step adds at most one programmed input. -/
theorem simWorldD_frame [Fintype S] [DecidableEq S] [DecidableEq W] [Fintype Pw]
    [DecidableEq Pw] [Fintype K] [Nonempty K] [Inhabited K] (td : Pw → Sˣ)
    (t : SimSt S W Pw K × St Pw K) (e : OEv Pw W) (r : (S × K) × K × K) :
    (simWorldD G td t e r).1.1.1.zs = (simStartD G td t.1 e r.1).1.1.zs ∧
      (simWorldD G td t e r).1.1.1.info = (simStartD G td t.1 e r.1).1.1.info ∧
      (simWorldD G td t e r).1.1.1.cands = (simStartD G td t.1 e r.1).1.1.cands ∧
      (simWorldD G td t e r).1.1.1.h2 = (simStartD G td t.1 e r.1).1.1.h2 ∧
      ((simWorldD G td t e r).1.1.2 = (simStartD G td t.1 e r.1).1.2 ∨
        ∃ x, (simWorldD G td t e r).1.1.2 = x :: (simStartD G td t.1 e r.1).1.2) := by
  simp only [simWorldD]
  obtain ⟨h₁, h₂⟩ :=
    drive1D_frame (simStartD G td t.1 e r.1).1 (simStartD G td t.1 e r.1).2 t.2 r.2
  refine ⟨?_, ?_, ?_, ?_, h₂⟩
  · simpa using congrArg SimCore.zs h₁
  · simpa using congrArg SimCore.info h₁
  · simpa using congrArg SimCore.cands h₁
  · simpa using congrArg SimCore.h2 h₁

/-- `honStepD` keeps the queried passwords and the table of `H2`. -/
theorem honStepD_cands_h2 (c : SimCore S W Pw K)
    (o : Option (PartyId × PartyId × PartyId × Role))
    (z : S) : (honStepD c o z).cands = c.cands ∧ (honStepD c o z).h2 = c.h2 := by
  rcases o with _ | ⟨sid, pid, peer, role⟩
  · exact ⟨rfl, rfl⟩
  · simp only [honStepD, honCoreD]
    split_ifs <;> exact ⟨rfl, rfl⟩

/-- **The core grows along a step of the simulated world**, apart from the secrets and the
session information of a new session. -/
theorem simWorldD_cands_h2 [Fintype S] [DecidableEq S] [DecidableEq W] [Fintype Pw]
    [DecidableEq Pw] [Fintype K] [Nonempty K] [Inhabited K] (td : Pw → Sˣ)
    (t : SimSt S W Pw K × St Pw K) (e : OEv Pw W) (r : (S × K) × K × K) :
    (∀ pw ∈ t.1.1.cands, pw ∈ (simWorldD G td t e r).1.1.1.cands) ∧
      ((simWorldD G td t e r).1.1.1.h2 = t.1.1.h2 ∨
        ∃ x, (simWorldD G td t e r).1.1.1.h2 = x :: t.1.1.h2) ∧
      ((simWorldD G td t e r).1.1.2 = t.1.2 ∨
        ∃ x, (simWorldD G td t e r).1.1.2 = x :: t.1.2) := by
  obtain ⟨-, -, hc, hh, hp⟩ := simWorldD_frame G td t e r
  rw [hc, hh]
  rcases e with h | a
  · rw [simStartD_inl] at hp ⊢
    obtain ⟨h₁, h₂⟩ := honStepD_cands_h2 t.1.1 (honPub h) r.1.1
    exact ⟨fun pw hpw => h₁ ▸ hpw, Or.inl h₂, hp⟩
  · obtain ⟨hg, hq⟩ := simStartD_inr G td t.1 a r.1
    rw [hq] at hp
    exact ⟨hg.cands, hg.h2, hp⟩

/-- The secrets after a step of the simulated world. -/
theorem simWorldD_zs [Fintype S] [DecidableEq S] [DecidableEq W] [Fintype Pw]
    [DecidableEq Pw] [Fintype K] [Nonempty K] [Inhabited K] (td : Pw → Sˣ)
    (t : SimSt S W Pw K × St Pw K) (e : OEv Pw W) (r : (S × K) × K × K) :
    (simWorldD G td t e r).1.1.1.zs = (match e with
      | .inl h => (honStepD t.1.1 (honPub h) r.1.1).zs
      | .inr _ => t.1.1.zs) ∧
    (simWorldD G td t e r).1.1.1.info = (match e with
      | .inl h => (honStepD t.1.1 (honPub h) r.1.1).info
      | .inr _ => t.1.1.info) := by
  obtain ⟨hz, hi, -⟩ := simWorldD_frame G td t e r
  rw [hz, hi]
  rcases e with h | a
  · rw [simStartD_inl]
    exact ⟨rfl, rfl⟩
  · exact ⟨(simStartD_inr G td t.1 a r.1).1.zs, (simStartD_inr G td t.1 a r.1).1.info⟩

/-- A step of the real world adds at most one entry to the table of `H2`. -/
theorem realDet_h2 [Fintype S] [DecidableEq S] [DecidableEq W] [Fintype Pw] [DecidableEq Pw]
    [Fintype K] [Nonempty K] (td : Pw → Sˣ) (s : RSt S W Pw K) (e : OEv Pw W) (r : S × K) :
    (realDet G td s e r).2.h2 = s.h2 ∨ ∃ x, (realDet G td s e r).2.h2 = x :: s.h2 := by
  have hro : ∀ (tb : List (Inp W × K)) (x : Inp W) (k : K),
      (roDet tb x k).2 = tb ∨ ∃ y, (roDet tb x k).2 = y :: tb := by
    intro tb x k
    unfold roDet
    split
    · exact Or.inl rfl
    · exact Or.inr ⟨_, rfl⟩
  rcases e with (⟨sid, pid, peer, role, pw⟩ | ⟨sid, pid⟩) |
    (_ | _ | pid | pw | x | ⟨pid, m⟩)
  · simp only [realDet]
    split_ifs <;> exact Or.inl rfl
  all_goals try exact Or.inl rfl
  · exact hro _ _ _
  · simp only [realDet]
    split
    · split_ifs
      · exact hro _ _ _
      · exact Or.inl rfl
    · exact Or.inl rfl

end Frame

/-! ## The new-message collision -/

section Collision

variable {S W Pw K : Type} [Field S] (G : DHGroup S W)

/-- Twice the number of inputs of `H2` in the real and the simulated tables: a bound on the
number of messages in them. -/
def msgCount (s : JS S W Pw K) : ℕ := 2 * (s.2.h2.length + s.1.1.1.h2.length + s.1.1.2.length)

/-- The number of protocol parties of the session `0` without a record in the simulator. -/
def freshCount (c : SimCore S W Pw K) : ℕ :=
  (if c.info 0 = none then 1 else 0) + (if c.info 1 = none then 1 else 0)

theorem mem_map_fst_of_lookup {α β : Type} [DecidableEq α] {l : List (α × β)} {a : α}
    (h : (l.lookup a).isSome) : a ∈ l.map Prod.fst := by
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.1 h
  exact List.mem_map.2 ⟨(a, b), mem_of_lookup hb, rfl⟩

/-- **A uniform secret gives a message of the tables** with probability at most
`msgCount s / |S|`. -/
theorem uniform_inMsgs_le [Fintype S] [DecidableEq W] [Nonempty S] (s : JS S W Pw K) :
    (PMF.uniformFintype S).toOuterMeasure {z | InMsgs s (G.pub z)} ≤
      msgCount s * (Fintype.card S : ℝ≥0∞)⁻¹ := by
  classical
  let L : List W := (s.2.h2.map Prod.fst ++ s.1.1.1.h2.map Prod.fst ++ s.1.1.2.map Prod.fst).flatMap
    fun x => [x.2.1, x.2.2.1]
  have hmem : ∀ z, InMsgs s (G.pub z) → G.pub z ∈ L := by
    rintro z ⟨x, hx, hw⟩
    have hxL : x ∈ s.2.h2.map Prod.fst ++ s.1.1.1.h2.map Prod.fst ++ s.1.1.2.map Prod.fst := by
      rcases hx with hx | hx
      · simp [mem_map_fst_of_lookup hx]
      · unfold InDom simLk at hx
        split at hx
        · next k hk => simp [mem_map_fst_of_lookup (by simp [hk] : (s.1.1.2.lookup x).isSome)]
        · simp [mem_map_fst_of_lookup hx]
    exact List.mem_flatMap.2 ⟨x, hxL, by rcases hw with h | h <;> simp [h]⟩
  have h2 : ∀ l : List (Inp W × K),
      (l.map fun x => ([x.1.2.1, x.1.2.2.1] : List W).length).sum = 2 * l.length := by
    intro l
    induction l with
    | nil => rfl
    | cons a l ih =>
      rw [List.map_cons, List.sum_cons, ih, List.length_cons]
      simp only [List.length_cons, List.length_nil]
      ring
  have hlen : L.length = msgCount s := by
    simp only [L, msgCount, List.length_flatMap, List.map_append, List.sum_append, List.map_map,
      Function.comp_def, h2]
    ring
  rw [PMF.toOuterMeasure_uniformFintype_apply, div_eq_mul_inv]
  gcongr
  have hc : Fintype.card {z | InMsgs s (G.pub z)} ≤ L.toFinset.card := by
    refine (Fintype.card_le_of_injective
      (fun z => (⟨G.pub z.1, List.mem_toFinset.2 (hmem z.1 z.2)⟩ : L.toFinset))
      fun a b h => Subtype.ext (G.pub.injective (congrArg Subtype.val h))).trans_eq
      (Fintype.card_coe _)
  exact_mod_cast hc.trans ((List.toFinset_card_le L).trans hlen.le)

/-- `honStepD` on a new session of a protocol party without a record: the party gets its
record and, if active, its secret. -/
theorem honStepD_new (c : SimCore S W Pw K) {sid pid peer : PartyId} {role : Role} (z : S)
    (h : sid = 0 ∧ pid ≤ 1 ∧ c.info pid = none) :
    (honStepD c (some (sid, pid, peer, role)) z).info =
        Function.update c.info pid (some (peer, role)) ∧
      (honStepD c (some (sid, pid, peer, role)) z).zs =
        if Active sid pid peer = true then Function.update c.zs pid (some z) else c.zs := by
  simp only [honStepD, honCoreD, h, and_self, ↓reduceIte]
  split_ifs <;> exact ⟨rfl, rfl⟩

/-- `honStepD` on any other event keeps the records and secrets. -/
theorem honStepD_old (c : SimCore S W Pw K) (o : Option (PartyId × PartyId × PartyId × Role))
    (z : S) (h : ∀ sid pid peer role, o = some (sid, pid, peer, role) →
      ¬ (sid = 0 ∧ pid ≤ 1 ∧ c.info pid = none)) :
    (honStepD c o z).info = c.info ∧ (honStepD c o z).zs = c.zs := by
  rcases o with _ | ⟨sid, pid, peer, role⟩
  · exact ⟨rfl, rfl⟩
  · have hn := h sid pid peer role rfl
    simp [honStepD, honCoreD, hn]

theorem freshCount_update {c : SimCore S W Pw K} {pid : PartyId} (hp : pid ≤ 1)
    (hn : c.info pid = none) (v : PartyId × Role) (info : PartyId → Option (PartyId × Role))
    (hi : info = Function.update c.info pid (some v)) :
    (if info 0 = none then 1 else 0) + (if info 1 = none then 1 else 0) + 1 ≤ freshCount c := by
  subst hi
  unfold freshCount
  interval_cases pid <;> simp [Function.update, hn]

/-- The step of the joint world as the image of a draw. -/
theorem mem_support_jointSim [Fintype S] [DecidableEq W] [DecidableEq Pw] [Fintype K]
    [Nonempty K] [Inhabited K] {td : Pw → Sˣ} {s : JSt S W Pw K} {e : OEv Pw W}
    {x : OOut W K × JSt S W Pw K} (hx : x ∈ (jointSim G td s e).support) :
    ∃ r, x.2.1 = ((simWorldD G td (setTd td s.1.1) e r).1,
      (realDet G td s.1.2 e (cpl G td s.1.1 e r)).2) := by
  simp only [jointSim, PMF.support_map, Set.mem_image] at hx
  obtain ⟨r, -, rfl⟩ := hx
  exact ⟨r, rfl⟩

variable [Fintype S] [DecidableEq S] [DecidableEq W] [Fintype Pw] [DecidableEq Pw] [Fintype K]
  [Nonempty K] [Inhabited K]

/-- **The new-message collision experiment.** For an oracle adversary with at most `q`
queries, a new party's message occurs in an earlier input of `H2` with probability at most
`12 q / |S|`: two parties draw a secret, and the tables hold at most `3 q` inputs. -/
theorem collStepExp_le (B : OracleAdv (OEv Pw W) (OOut W K) Bool) (q : ℕ)
    (hB : B.IsQueryBound q) :
    collStepExp G B true ≤ 12 * q * (Fintype.card S : ℝ≥0∞)⁻¹ := by
  classical
  have hinner : ∀ td : Pw → Sˣ,
      (OracleAdv.run (OracleAdv.flagWhen (fun s _ x => CollStep G s.1 x.2.1) (jointSim G td)) B
        (jointInit G, false)).toOuterMeasure {y | y.2.2 = true} ≤
      12 * q * (Fintype.card S : ℝ≥0∞)⁻¹ := by
    intro td
    have hΨ : ∀ (s : JSt S W Pw K) (e : OEv Pw W), ∀ x ∈ (jointSim G td s e).support,
        msgCount x.2.1 ≤ msgCount s.1 + 6 := by
      intro s e x hx
      obtain ⟨r, hr⟩ := mem_support_jointSim G hx
      obtain ⟨-, hh, hp⟩ := simWorldD_cands_h2 G td (setTd td s.1.1) e r
      have hR := realDet_h2 G td s.1.2 e (cpl G td s.1.1 e r)
      simp only [msgCount, hr]
      have e1 : (setTd td s.1.1).1.1.h2 = s.1.1.1.1.h2 := rfl
      have e2 : (setTd td s.1.1).1.2 = s.1.1.1.2 := rfl
      rw [e1] at hh
      rw [e2] at hp
      rcases hh with hh | ⟨_, hh⟩ <;> rcases hp with hp | ⟨_, hp⟩ <;>
        rcases hR with hR | ⟨_, hR⟩ <;> simp only [hh, hp, hR, List.length_cons] <;> omega
    have hstep : ∀ (s : JSt S W Pw K) (e : OEv Pw W),
        ((∀ x ∈ (jointSim G td s e).support,
            freshCount x.2.1.1.1.1 + 1 ≤ freshCount s.1.1.1.1) ∧
          (jointSim G td s e).toOuterMeasure {x | CollStep G s.1 x.2.1} ≤
            msgCount s.1 * (Fintype.card S : ℝ≥0∞)⁻¹) ∨
        ∀ x ∈ (jointSim G td s e).support, ¬ CollStep G s.1 x.2.1 ∧
          freshCount x.2.1.1.1.1 ≤ freshCount s.1.1.1.1 := by
      intro s e
      by_cases hc : ∃ sid pid peer role pw, e = .inl (.newSession sid pid peer role pw) ∧
          sid = 0 ∧ pid ≤ 1 ∧ s.1.1.1.1.info pid = none
      · obtain ⟨sid, pid, peer, role, pw, rfl, hc⟩ := hc
        have hnew : ∀ r : (S × K) × K × K,
            (simWorldD G td (setTd td s.1.1) (.inl (.newSession sid pid peer role pw)) r).1.1.1.info
              = Function.update s.1.1.1.1.info pid (some (peer, role)) ∧
            (simWorldD G td (setTd td s.1.1) (.inl (.newSession sid pid peer role pw)) r).1.1.1.zs
              = if Active sid pid peer = true then Function.update s.1.1.1.1.zs pid (some r.1.1)
                else s.1.1.1.1.zs := by
          intro r
          obtain ⟨hz, hi⟩ := simWorldD_zs G td (setTd td s.1.1)
            (.inl (.newSession sid pid peer role pw)) r
          rw [hz, hi]
          exact honStepD_new ({ s.1.1.1.1 with td := some td }) r.1.1 hc
        left
        refine ⟨fun x hx => ?_, ?_⟩
        · obtain ⟨r, hr⟩ := mem_support_jointSim G hx
          rw [hr]
          exact freshCount_update hc.2.1 hc.2.2 _ _ (hnew r).1
        · rw [jointSim, PMF.toOuterMeasure_map_apply]
          refine (MeasureTheory.measure_mono
            (μ := (PMF.uniformFintype ((S × K) × K × K)).toOuterMeasure)
            (t := {r | InMsgs s.1 (G.pub r.1.1)}) ?_).trans ?_
          · intro r hr
            obtain ⟨pid', z, h0, h1, hm⟩ := hr
            simp only [jointD] at h1
            rw [(hnew r).2] at h1
            have hz : z = r.1.1 := by
              split_ifs at h1
              · by_cases hp : pid' = pid
                · subst hp
                  simpa using h1.symm
                · rw [Function.update_of_ne hp, h0] at h1
                  exact absurd h1 (by simp)
              · rw [h0] at h1
                exact absurd h1 (by simp)
            subst hz
            exact hm
          · have hu : (PMF.uniformFintype ((S × K) × K × K)).map (fun r => r.1.1) =
                PMF.uniformFintype S := by
              rw [show (fun r : (S × K) × K × K => r.1.1) = Prod.fst ∘ Prod.fst from rfl,
                ← PMF.map_comp, PMF.map_uniform_fst, PMF.map_uniform_fst]
            calc _ = ((PMF.uniformFintype ((S × K) × K × K)).map (fun r => r.1.1)).toOuterMeasure
                  {z | InMsgs s.1 (G.pub z)} := by rw [PMF.toOuterMeasure_map_apply]; rfl
              _ ≤ _ := by rw [hu]; exact uniform_inMsgs_le G s.1
      · right
        intro x hx
        obtain ⟨r, hr⟩ := mem_support_jointSim G hx
        obtain ⟨hz, hi⟩ := simWorldD_zs G td (setTd td s.1.1) e r
        have hold : (simWorldD G td (setTd td s.1.1) e r).1.1.1.info = s.1.1.1.1.info ∧
            (simWorldD G td (setTd td s.1.1) e r).1.1.1.zs = s.1.1.1.1.zs := by
          rw [hz, hi]
          rcases e with h | a
          · refine honStepD_old _ _ _ fun sid pid peer role ho hcond => hc ?_
            rcases h with ⟨sid', pid', peer', role', pw'⟩ | ⟨sid', pid'⟩
            · simp only [honPub, Option.some.injEq, Prod.mk.injEq] at ho
              obtain ⟨rfl, rfl, rfl, rfl⟩ := ho
              exact ⟨_, _, _, _, pw', rfl, hcond⟩
            · simp [honPub] at ho
          · exact ⟨rfl, rfl⟩
        rw [hr]
        refine ⟨fun ⟨pid', z, h0, h1, _⟩ => ?_, le_of_eq (by simp [freshCount, hold.1])⟩
        rw [hold.2, h0] at h1
        exact absurd h1 (by simp)
    have h := OracleAdv.run_flagWhen_le_potential (jointSim G td)
      (fun s _ x => CollStep G s.1 x.2.1) (fun s => freshCount s.1.1.1.1) (fun s => msgCount s.1)
      6 (6 * q) (Fintype.card S : ℝ≥0∞)⁻¹ hΨ hstep B q hB (jointInit G)
      (by simp [msgCount, jointInit, simProt])
    refine h.trans (le_of_eq ?_)
    simp only [freshCount, jointInit, simProt]
    push_cast
    ring
  unfold collStepExp flagExp
  rw [PMF.bind_apply]
  calc _ ≤ ∑' td : Pw → Sˣ, PMF.uniformFintype (Pw → Sˣ) td *
        (12 * q * (Fintype.card S : ℝ≥0∞)⁻¹) := by
        refine ENNReal.tsum_le_tsum fun td => ?_
        gcongr
        exact (flagExp_inner_apply G td (fun _ s s' => CollStep G s s') B).trans_le (hinner td)
    _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

end Collision

end CatCrypt.Crypto.PAKE.CPaceBadReductions
