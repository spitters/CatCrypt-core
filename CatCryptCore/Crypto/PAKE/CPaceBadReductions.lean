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

/-- **A monotone bad state at the end.** If a state predicate `P` is kept by every call, the flag
of `P` is set with at most the probability that the final state satisfies `P`. -/
theorem run_flagWhen_le_final (O : σ → D → PMF (R × σ)) (P : σ → Prop) [DecidablePred P]
    (hmono : ∀ s d, P s → ∀ x ∈ (O s d).support, P x.2) (A : OracleAdv D R α) (s : σ) :
    (run (flagWhen (fun _ _ x => P x.2) O) A (s, false)).toOuterMeasure {y | y.2.2 = true} ≤
      (run O A s).toOuterMeasure {y | P y.2} := by
  rw [← run_flagWhen_map (fun _ _ x => P x.2) O A s false, PMF.toOuterMeasure_map_apply]
  refine PMF.toOuterMeasure_mono _ fun y hy => ?_
  have h := run_support_inv (flagWhen (fun _ _ x => P x.2) O) (fun st => st.2 = true → P st.1)
    (fun st d x hst hx => by
      simp only [flagWhen, PMF.support_map, Set.mem_image] at hx
      obtain ⟨x₀, hx₀, rfl⟩ := hx
      intro hf
      by_cases hp : P x₀.2
      · exact hp
      · cases hb : st.2
        · simp [hb, hp] at hf
        · exact hmono st.1 d (hst hb) x₀ hx₀) A (s, false) (fun h => by cases h) y hy.2
  exact h hy.1

/-- The probability of an event under the image of a distribution. -/
theorem toOuterMeasure_eq_of_map_eq {β γ : Type} {p : PMF β} {q : PMF γ} {f : β → γ}
    (h : p.map f = q) (A : Set γ) : p.toOuterMeasure (f ⁻¹' A) = q.toOuterMeasure A := by
  rw [← h, PMF.toOuterMeasure_map_apply]

/-- A map of the inner oracle state that commutes with the inner oracle commutes with the
composite oracle of a simulator. -/
theorem simOracle_map_inner {D' R' S U U' : Type} (impl : S → D → OracleAdv D' R' (R × S))
    (O' : U → D' → PMF (R' × U)) (O'' : U' → D' → PMF (R' × U')) (g : U → U')
    (hO : ∀ u q, (O' u q).map (Prod.map id g) = O'' (g u) q) (s : S) (u : U) (d : D) :
    (simOracle impl O' (s, u) d).map (Prod.map id (Prod.map id g)) =
      simOracle impl O'' (s, g u) d := by
  simp only [simOracle, PMF.map_comp, ← run_map_state O' O'' g hO (impl s d) u]
  rfl

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

/-- A new party draws a secret `z` with `Q s z`, at the state `s` before the step. -/
def NewSecret (Q : JS S W Pw K → S → Prop) (s s' : JS S W Pw K) : Prop :=
  ∃ pid z, s.1.1.1.zs pid = none ∧ s'.1.1.1.zs pid = some z ∧ Q s z

open Classical in
/-- **A new secret in a set of small probability.** Let a uniform secret satisfy `Q s` with
probability at most `Ψ s · ε`, and let a step of the joint world increase `Ψ` by at most `c`.
For
an oracle adversary with at most `q` queries, a new party draws a secret with `Q` with
probability at most `2 (Ψ s₀ + c q) ε`: two parties draw a secret. -/
theorem run_flag_newSecret_le (td : Pw → Sˣ) (Q : JS S W Pw K → S → Prop)
    (Ψ : JS S W Pw K → ℕ) (c : ℕ) (ε : ℝ≥0∞)
    (hΨ : ∀ (s : JSt S W Pw K) (e : OEv Pw W), ∀ x ∈ (jointSim G td s e).support,
      Ψ x.2.1 ≤ Ψ s.1 + c)
    (hQ : ∀ s, (PMF.uniformFintype S).toOuterMeasure {z | Q s z} ≤ Ψ s * ε)
    (B : OracleAdv (OEv Pw W) (OOut W K) Bool) (q : ℕ) (hB : B.IsQueryBound q) :
    (OracleAdv.run (OracleAdv.flagWhen (fun s (_ : OEv Pw W) x => NewSecret Q s.1 x.2.1)
      (jointSim G td)) B (jointInit G, false)).toOuterMeasure {y | y.2.2 = true} ≤
      2 * ((Ψ (jointInit G).1 + c * q) * ε) := by
  classical
  have hstep : ∀ (s : JSt S W Pw K) (e : OEv Pw W),
      ((∀ x ∈ (jointSim G td s e).support,
          freshCount x.2.1.1.1.1 + 1 ≤ freshCount s.1.1.1.1) ∧
        (jointSim G td s e).toOuterMeasure {x | NewSecret Q s.1 x.2.1} ≤ Ψ s.1 * ε) ∨
      ∀ x ∈ (jointSim G td s e).support, ¬ NewSecret Q s.1 x.2.1 ∧
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
          (t := {r | Q s.1 r.1.1}) ?_).trans ?_
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
                {z | Q s.1 z} := by rw [PMF.toOuterMeasure_map_apply]; rfl
            _ ≤ _ := by rw [hu]; exact hQ s.1
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
    (fun s _ x => NewSecret Q s.1 x.2.1) (fun s => freshCount s.1.1.1.1) (fun s => Ψ s.1)
    c (Ψ (jointInit G).1 + c * q) ε hΨ hstep B q hB (jointInit G) le_rfl
  refine h.trans (le_of_eq ?_)
  simp only [freshCount, jointInit, simProt]
  push_cast
  ring

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
    have h := run_flag_newSecret_le G td (fun s z => InMsgs s (G.pub z)) msgCount 6
      (Fintype.card S : ℝ≥0∞)⁻¹ hΨ (uniform_inMsgs_le G) B q hB
    refine h.trans (le_of_eq ?_)
    simp only [msgCount, jointInit, simProt]
    simp only [List.length_nil, add_zero, mul_zero, Nat.cast_ofNat]
    ring
  unfold collStepExp flagExp
  rw [PMF.bind_apply]
  calc _ ≤ ∑' td : Pw → Sˣ, PMF.uniformFintype (Pw → Sˣ) td *
        (12 * q * (Fintype.card S : ℝ≥0∞)⁻¹) := by
        refine ENNReal.tsum_le_tsum fun td => ?_
        gcongr
        exact (flagExp_inner_apply G td (fun _ s s' => CollStep G s s') B).trans_le (hinner td)
    _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

open Classical in
/-- **A new party draws the secret zero** with probability at most `2 / |S|`. -/
theorem run_flag_newZero_le (td : Pw → Sˣ) (B : OracleAdv (OEv Pw W) (OOut W K) Bool) (q : ℕ)
    (hB : B.IsQueryBound q) :
    (OracleAdv.run (OracleAdv.flagWhen (fun s (_ : OEv Pw W) x =>
      NewSecret (fun _ z => z = (0 : S)) s.1 x.2.1) (jointSim G td)) B
        (jointInit G, false)).toOuterMeasure {y | y.2.2 = true} ≤
      2 * (Fintype.card S : ℝ≥0∞)⁻¹ := by
  classical
  have hQ : ∀ s : JS S W Pw K, (PMF.uniformFintype S).toOuterMeasure {z | z = (0 : S)} ≤
      ((fun _ => 1 : JS S W Pw K → ℕ) s : ℝ≥0∞) * (Fintype.card S : ℝ≥0∞)⁻¹ := by
    intro s
    rw [PMF.toOuterMeasure_uniformFintype_apply, div_eq_mul_inv]
    gcongr
    exact Fintype.card_le_one_iff.mpr fun a b =>
      Subtype.ext ((show a.1 = 0 from a.2).trans (show b.1 = 0 from b.2).symm)
  have h := run_flag_newSecret_le G td (fun _ z => z = (0 : S)) (fun _ => 1) 0
    (Fintype.card S : ℝ≥0∞)⁻¹ (fun _ _ _ _ => le_rfl) hQ B q hB
  simpa using h

end Collision

/-! ## The step of the simulated world as the image of a draw -/

section IdealStep

variable {S W Pw K : Type} [Field S] [Fintype S] [DecidableEq S] [DecidableEq W]
  [Fintype Pw] [DecidableEq Pw] [Fintype K] [Nonempty K] [Inhabited K] (G : DHGroup S W)

/-- **The step of the simulated world with the table `td` of `H1` in place**, as the image of a
uniform draw under `simWorldD`. -/
noncomputable def idealStep (td : Pw → Sˣ) (t : SimSt S W Pw K × St Pw K) (e : OEv Pw W) :
    PMF (OOut W K × (SimSt S W Pw K × St Pw K)) :=
  (PMF.uniformFintype ((S × K) × K × K)).map fun r =>
    (CPaceHops.simWorldD G td (setTd td t) e r).swap

/-- The initial state of the simulated world. -/
noncomputable def hInit : SimSt S W Pw K × St Pw K := ((simProt G).init, initSt)

/-- The oracle of `idealGame G` is `idealStep G`. -/
theorem idealGame_oracle_eq_idealStep (td : Pw → Sˣ) :
    (idealGame G (Pw := Pw) (K := K)).oracle td = idealStep G td :=
  funext fun t => funext fun e => idealGame_oracle_eq G td t e

end IdealStep

/-! ## The simulated world with handles

The simulator uses the secret `z` of a party only through its message `g^z` and the CPace match
test of `z`. The simulated world with handles stores a handle `u` in place of the secret, computes
the message from the handle, and asks the match test, and `H1`, as oracle queries. A reduction
answers the queries from its challenge; at the ideal answers `hAns` of a family of bijections
`zOf pid`, the run is the run of the simulated world with the secrets `zOf pid u`
(`simOracle_hImpl`). -/

section Handles

/-- A query of the simulated world with handles: `H1` at a password, or the match test of the
party `pid` with handle `u` of the key `k` for the peer message `peer` and the password `pw`. -/
abbrev HQ (S W Pw : Type) := Pw ⊕ (PartyId × S × Pw × W × W)

/-- An answer: a generator, or the bit of a match test. -/
abbrev HA (W : Type) := W ⊕ Bool

/-- The bit of an answer. -/
def ansBit {W : Type} : HA W → Bool
  | .inr b => b
  | .inl _ => false

/-- The generator of an answer, and `d` for a bit. -/
def ansGen {W : Type} (d : W) : HA W → W
  | .inl Y => Y
  | .inr _ => d

variable {S W Pw K : Type} [Field S] (G : DHGroup S W)

/-- The extraction of the party `pid` with handle `u` for the peer message `peer` and the key
`k`: the first candidate whose match test is answered positively. -/
def extractO (pid : PartyId) (u : S) (peer k : W) :
    List Pw → OracleAdv (HQ S W Pw) (HA W) (Option Pw)
  | [] => .ret none
  | pw :: rest => .query (.inr (pid, u, pw, peer, k)) fun a =>
    bif ansBit a then .ret (some pw) else extractO pid u peer k rest

/-- `extractAt` with a handle. -/
def extractAtO (cands : List Pw) (u : S) (pid : PartyId) (x : Inp W) :
    OracleAdv (HQ S W Pw) (HA W) (Option Pw) :=
  extractO pid u (if pid = 0 then x.2.2.1 else x.2.1) x.2.2.2 cands

variable [DecidableEq W]

/-- `lateAt` with handles. -/
def lateAtO (c : SimCore S W Pw K) (x : Inp W) (pid : PartyId) :
    OracleAdv (HQ S W Pw) (HA W) (Option Pw) :=
  match c.pend pid, c.zs pid with
  | some T, some u => if x.tr = T then extractAtO c.cands u pid x else .ret none
  | _, _ => .ret none

/-- `lateTarget` with handles. -/
def lateTargetO (c : SimCore S W Pw K) (x : Inp W) :
    OracleAdv (HQ S W Pw) (HA W) (Option (PartyId × Pw)) :=
  (lateAtO c x 0).bind fun o => match o with
    | some pw => .ret (some (0, pw))
    | none => (lateAtO c x 1).bind fun o' => .ret (o'.map fun pw => (1, pw))

/-- `findMatch` with a handle, over the entries `l` of the table of `H2`. -/
def findMatchO (cands : List Pw) (u : S) (pid : PartyId) (T : Role × W × W) :
    List (Inp W × K) → OracleAdv (HQ S W Pw) (HA W) (Option (Pw × K))
  | [] => .ret none
  | e :: rest =>
    if e.1.tr = T then (extractAtO cands u pid e.1).bind fun o => match o with
      | some pw => .ret (some (pw, e.2))
      | none => findMatchO cands u pid T rest
    else findMatchO cands u pid T rest

variable [Inhabited K]

/-- `sendCore` with handles and the message function `msgF`. -/
def sendCoreO (msgF : PartyId → S → W) (c : SimCore S W Pw K) (pid : PartyId) (m : W) :
    OracleAdv (HQ S W Pw) (HA W) (SimCore S W Pw K × Dec Pw W K) :=
  match c.zs pid, c.info pid with
  | some u, some (_, role) =>
    if c.keyed pid = false ∧ m ≠ G.pub 0 then
      if (c.zs (1 - pid)).map (msgF (1 - pid)) = some m then
        .ret ({ c with keyed := Function.update c.keyed pid true, phase := .done },
          sCall (.newKey 0 pid default))
      else
        (findMatchO c.cands u pid (h2Inp pid role (msgF pid u) m m).tr c.h2).bind fun fm =>
          match fm with
          | some (pw, k) =>
            .ret ({ c with keyed := Function.update c.keyed pid true, phase := .key pid k },
              sCall (.testPwd 0 pid pw))
          | none =>
            .ret ({ c with
                    keyed := Function.update c.keyed pid true
                    phase := .key pid default
                    pend := Function.update c.pend pid
                      (some (h2Inp pid role (msgF pid u) m m).tr) },
              sCall (.registerTest 0 pid))
    else .ret ({ c with phase := .rest }, sOut .ack)
  | _, _ => .ret ({ c with phase := .rest }, sOut .ack)

/-- `h2CoreD` with handles. -/
def h2CoreO (c : SimCore S W Pw K) (x : Inp W) (k : K) :
    OracleAdv (HQ S W Pw) (HA W) (SimCore S W Pw K × Dec Pw W K) :=
  (lateTargetO c x).bind fun lt => match lt with
    | some (pid, pw) =>
      .ret ({ c with pend := Function.update c.pend pid none, phase := .late x },
        sCall (.lateTestPwd 0 pid pw))
    | none => .ret ({ c with h2 := (x, k) :: c.h2, phase := .rest }, sOut (.hash k))

variable [DecidableEq Pw]

/-- `advCoreD` with handles: `H1` is a query. -/
def advCoreO (msgF : PartyId → S → W) (c : SimCore S W Pw K) (a : RAEv Pw W) (k : K) :
    OracleAdv (HQ S W Pw) (HA W) (SimCore S W Pw K × Dec Pw W K) :=
  match a with
  | .idle => .ret ({ c with phase := .rest }, sOut .ack)
  | .poll => .ret ({ c with phase := .fwd }, sCall .poll)
  | .msg pid => .ret ({ c with phase := .rest }, sOut (.msg ((c.zs pid).map (msgF pid))))
  | .h1 pw => .query (.inl pw) fun ans =>
    .ret ({ c with cands := if pw ∈ c.cands then c.cands else c.cands ++ [pw], phase := .rest },
      sOut (.gen (ansGen (G.pub 0) ans)))
  | .h2 x =>
    match c.h2.lookup x with
    | some k' => .ret ({ c with phase := .rest }, sOut (.hash k'))
    | none => h2CoreO c x k
  | .send pid m => sendCoreO G msgF c pid m

/-- `simStartD` with handles: a new party stores the drawn value as its handle. -/
def simStartO (msgF : PartyId → S → W) (s : SimSt S W Pw K) (e : OEv Pw W) (r : S × K) :
    OracleAdv (HQ S W Pw) (HA W) (SimSt S W Pw K × Dec Pw W K) :=
  match e with
  | .inl h => .ret ((honStepD s.1 (honPub h) r.1, s.2), .inl (.inl h))
  | .inr (.h2 x) =>
    match s.2.lookup x with
    | some k => .ret (({ s.1 with phase := .rest }, s.2), sOut (.hash k))
    | none => (advCoreO G msgF s.1 (.h2 x) r.2).bind fun p => .ret ((p.1, s.2), p.2)
  | .inr a => (advCoreO G msgF s.1 a r.2).bind fun p => .ret ((p.1, s.2), p.2)

variable [Fintype S] [Fintype K] [Nonempty K]

/-- **The simulated world with handles**: one uniform draw, the start of the simulator with
handles, and the end of the activation with `F_lePAKE` as in `simWorldD`. -/
noncomputable def hImpl (msgF : PartyId → S → W) (t : SimSt S W Pw K × St Pw K)
    (e : OEv Pw W) :
    OracleAdv (HQ S W Pw) (HA W) (OOut W K × (SimSt S W Pw K × St Pw K)) :=
  .rand (PMF.uniformFintype ((S × K) × K × K)) fun r =>
    (simStartO G msgF t.1 e r.1).bind fun st =>
      .ret ((drive1D fStepD simResumeV simAnswer st.1 st.2 t.2 r.2).2.2,
        ((drive1D fStepD simResumeV simAnswer st.1 st.2 t.2 r.2).1,
          (drive1D fStepD simResumeV simAnswer st.1 st.2 t.2 r.2).2.1))

end Handles

/-! ### The ideal answers -/

section Ideal

variable {S W Pw K : Type} [Field S] [DecidableEq W] (G : DHGroup S W)
  (zOf : PartyId → S → S) (td : Pw → Sˣ)

/-- **The ideal answers** for the bijections `zOf pid` and the table `td` of `H1`: `H1` answers
`g^{td pw}`, and the match test of the party `pid` with handle `u` is the CPace match test of
the secret `zOf pid u`. -/
def hAns : HQ S W Pw → HA W
  | .inl pw => .inl (G.pub (td pw))
  | .inr (pid, u, pw, peer, k) => .inr ((kit G td).matchTest (zOf pid u) peer k pw)

/-- The oracle of the ideal answers. -/
noncomputable def hOracle (_ : Unit) (q : HQ S W Pw) : PMF (HA W × Unit) :=
  PMF.pure (hAns G zOf td q, ())

/-- The core of the simulated world of a core with handles: the secrets `zOf pid u` and the
table `td` of `H1`. -/
def reconC (c : SimCore S W Pw K) : SimCore S W Pw K :=
  { c with td := some td, zs := fun pid => (c.zs pid).map (zOf pid) }

theorem run_hOracle_extractO (pid : PartyId) (u : S) (peer k : W) (cands : List Pw) :
    OracleAdv.run (hOracle G zOf td) (extractO pid u peer k cands) () =
      PMF.pure ((kit G td).extract (zOf pid u) cands peer k, ()) := by
  induction cands with
  | nil => simp [extractO, DHExtractKit.extract]
  | cons pw rest ih =>
    simp only [extractO, OracleAdv.run_query, hOracle, PMF.pure_bind, hAns, ansBit]
    cases h : (kit G td).matchTest (zOf pid u) peer k pw
    · simp [ih, DHExtractKit.extract, h]
    · simp [DHExtractKit.extract, h]

theorem run_hOracle_extractAtO (cands : List Pw) (u : S) (pid : PartyId) (x : Inp W) :
    OracleAdv.run (hOracle G zOf td) (extractAtO cands u pid x) () =
      PMF.pure (extractAt G td cands (zOf pid u) pid x, ()) :=
  run_hOracle_extractO G zOf td _ _ _ _ _

theorem run_hOracle_findMatchO (cands : List Pw) (u : S) (pid : PartyId) (T : Role × W × W)
    (l : List (Inp W × K)) :
    OracleAdv.run (hOracle G zOf td) (findMatchO cands u pid T l) () =
      PMF.pure (l.findSome? (fun e => if e.1.tr = T then
        (extractAt G td cands (zOf pid u) pid e.1).map fun pw => (pw, e.2) else none), ()) := by
  induction l with
  | nil => simp [findMatchO]
  | cons e rest ih =>
    by_cases hT : e.1.tr = T
    · simp only [findMatchO, hT, ite_true, OracleAdv.run_bind, run_hOracle_extractAtO,
        PMF.pure_bind, List.findSome?_cons]
      cases extractAt G td cands (zOf pid u) pid e.1 <;> simp [ih]
    · simp [findMatchO, hT, ih]

theorem run_hOracle_lateAtO (c : SimCore S W Pw K) (x : Inp W) (pid : PartyId) :
    OracleAdv.run (hOracle G zOf td) (lateAtO c x pid) () =
      PMF.pure (lateAt G td (reconC zOf td c) x pid, ()) := by
  unfold lateAtO lateAt reconC
  dsimp only
  cases hp : c.pend pid <;> cases hz : c.zs pid <;> simp
  split_ifs <;> simp [run_hOracle_extractAtO]

theorem run_hOracle_lateTargetO (c : SimCore S W Pw K) (x : Inp W) :
    OracleAdv.run (hOracle G zOf td) (lateTargetO c x) () =
      PMF.pure (lateTarget G td (reconC zOf td c) x, ()) := by
  unfold lateTargetO lateTarget
  rw [OracleAdv.run_bind, run_hOracle_lateAtO, PMF.pure_bind]
  cases lateAt G td (reconC zOf td c) x 0
  · simp [OracleAdv.run_bind, run_hOracle_lateAtO]
  · simp

variable [Inhabited K] (msgF : PartyId → S → W)
  (hmsg : ∀ pid u, msgF pid u = G.pub (zOf pid u))
include hmsg

theorem run_hOracle_sendCoreO (c : SimCore S W Pw K) (pid : PartyId) (m : W) :
    (OracleAdv.run (hOracle G zOf td) (sendCoreO G msgF c pid m) ()).map
        (fun x => (reconC zOf td x.1.1, x.1.2)) =
      PMF.pure (sendCore G td (reconC zOf td c) pid m) := by
  have hm : ∀ p, (c.zs p).map (msgF p) = ((c.zs p).map (zOf p)).map G.pub := fun p => by
    rw [Option.map_map]
    exact congrArg (fun f => (c.zs p).map f) (funext (hmsg p))
  unfold sendCoreO sendCore
  cases hz : c.zs pid with
  | none => simp [reconC, hz, PMF.pure_map]
  | some u =>
    cases hi : c.info pid with
    | none => simp [reconC, hz, hi, PMF.pure_map]
    | some pr =>
      obtain ⟨peer, role⟩ := pr
      simp only [reconC, hz, hi, Option.map_some]
      simp only [← hm (1 - pid), ← hmsg pid u]
      split_ifs with h₁ h₂
      · simp [PMF.pure_map]
      · rw [OracleAdv.run_bind, run_hOracle_findMatchO, PMF.pure_bind]
        simp only [findMatch]
        cases List.findSome? (fun e => if e.1.tr = (h2Inp pid role (msgF pid u) m m).tr then
          Option.map (fun pw => (pw, e.2)) (extractAt G td c.cands (zOf pid u) pid e.1)
          else none) c.h2 with
        | none => simp [PMF.pure_map]
        | some p => obtain ⟨pw, k⟩ := p; simp [PMF.pure_map]
      · simp [PMF.pure_map]

omit [Inhabited K] hmsg in
theorem run_hOracle_h2CoreO (c : SimCore S W Pw K) (x : Inp W) (k : K) :
    (OracleAdv.run (hOracle G zOf td) (h2CoreO c x k) ()).map
        (fun x => (reconC zOf td x.1.1, x.1.2)) =
      PMF.pure (h2CoreD G td (reconC zOf td c) x k) := by
  unfold h2CoreO h2CoreD
  rw [OracleAdv.run_bind, run_hOracle_lateTargetO, PMF.pure_bind]
  cases lateTarget G td (reconC zOf td c) x with
  | none => simp [reconC, PMF.pure_map]
  | some p => obtain ⟨pid, pw⟩ := p; simp [reconC, PMF.pure_map]

variable [DecidableEq Pw]

theorem run_hOracle_advCoreO (c : SimCore S W Pw K) (a : RAEv Pw W) (k : K) :
    (OracleAdv.run (hOracle G zOf td) (advCoreO G msgF c a k) ()).map
        (fun x => (reconC zOf td x.1.1, x.1.2)) =
      PMF.pure (advCoreD G td (reconC zOf td c) a k) := by
  cases a with
  | idle => simp [advCoreO, advCoreD, reconC, PMF.pure_map]
  | poll => simp [advCoreO, advCoreD, reconC, PMF.pure_map]
  | msg pid =>
    have hm : (c.zs pid).map (msgF pid) = ((c.zs pid).map (zOf pid)).map G.pub := by
      rw [Option.map_map]
      exact congrArg (fun f => (c.zs pid).map f) (funext (hmsg pid))
    simp [advCoreO, advCoreD, reconC, PMF.pure_map, hm]
  | h1 pw => simp [advCoreO, advCoreD, reconC, PMF.pure_map, hOracle, hAns, ansGen]; rfl
  | h2 x =>
    simp only [advCoreO, advCoreD]
    have hl : (reconC zOf td c).h2 = c.h2 := rfl
    rw [hl]
    cases c.h2.lookup x with
    | some k' => simp [reconC, PMF.pure_map]
    | none => exact run_hOracle_h2CoreO G zOf td c x k
  | send pid m => exact run_hOracle_sendCoreO G zOf td msgF hmsg c pid m

/-- The secret of a new party from the drawn handle. -/
def zMapE : OEv Pw W → S → S
  | .inl (.newSession _ pid _ _ _) => zOf pid
  | _ => id

omit [DecidableEq W] [Inhabited K] [DecidableEq Pw] hmsg in
theorem reconC_honStepD (c : SimCore S W Pw K) (h : LeHEv Pw) (z : S) :
    reconC zOf td (honStepD c (honPub h) z) =
      honStepD (reconC zOf td c) (honPub h) (zMapE (W := W) zOf (.inl h) z) := by
  rcases h with ⟨sid, pid, peer, role, pw⟩ | ⟨sid, pid⟩
  · show reconC zOf td { honCoreD c sid pid peer role z with phase := .fwd } =
      { honCoreD (reconC zOf td c) sid pid peer role (zOf pid z) with phase := .fwd }
    unfold honCoreD
    have hi : (reconC zOf td c).info = c.info := rfl
    rw [hi]
    split_ifs
    · simp only [reconC]
      congr 1
      funext p
      by_cases hp : p = pid
      · subst hp; simp
      · simp [Function.update_of_ne hp]
    · rfl
    · rfl
  · rfl

omit [Field S] [DecidableEq W] [Inhabited K] [DecidableEq Pw] hmsg in
/-- A bind whose continuation is a point mass at a function of a map with a point mass value. -/
theorem bind_pure_of_map {α β γ : Type} (p : PMF α) (F₀ : α → β) (k : β → γ) (v : β)
    (h : p.map F₀ = PMF.pure v) : (p.bind fun a => PMF.pure (k (F₀ a))) = PMF.pure (k v) := by
  rw [show (fun a => PMF.pure (k (F₀ a))) = PMF.pure ∘ (k ∘ F₀) from rfl,
    PMF.bind_pure_comp,
    ← PMF.map_comp, h, PMF.pure_map]

theorem run_hOracle_simStartO (s : SimSt S W Pw K) (e : OEv Pw W) (r : S × K) :
    (OracleAdv.run (hOracle G zOf td) (simStartO G msgF s e r) ()).map
        (fun x => ((reconC zOf td x.1.1.1, x.1.1.2), x.1.2)) =
      PMF.pure (simStartD G td (reconC zOf td s.1, s.2) e (zMapE zOf e r.1, r.2)) := by
  rcases e with h | a
  · simp only [simStartO, OracleAdv.run_ret, PMF.pure_map, simStartD, simCoreD]
    rw [reconC_honStepD]
  · have hadv := run_hOracle_advCoreO G zOf td msgF hmsg s.1 a r.2
    cases a
    case h2 x =>
      simp only [simStartO, simStartD]
      cases hs : s.2.lookup x with
      | some k => simp [reconC, PMF.pure_map]
      | none =>
        simp only [OracleAdv.run_bind, OracleAdv.run_ret, PMF.map_bind, PMF.pure_map]
        exact bind_pure_of_map _
          (fun a : (SimCore S W Pw K × Dec Pw W K) × Unit => (reconC zOf td a.1.1, a.1.2))
          (fun y => ((y.1, s.2), y.2)) _ hadv
    all_goals
      simp only [simStartO, simStartD, simCoreD, OracleAdv.run_bind, OracleAdv.run_ret,
        PMF.map_bind, PMF.pure_map]
      exact bind_pure_of_map _
        (fun a : (SimCore S W Pw K × Dec Pw W K) × Unit => (reconC zOf td a.1.1, a.1.2))
        (fun y => ((y.1, s.2), y.2)) _ hadv

omit [DecidableEq W] hmsg in
/-- The end of an activation commutes with the reconstruction of the core. -/
theorem drive1D_reconC (st : SimSt S W Pw K) (d : Dec Pw W K) (t : St Pw K) (k : K × K) :
    drive1D fStepD simResumeV simAnswer (reconC zOf td st.1, st.2) d t k =
      ((reconC zOf td (drive1D fStepD simResumeV simAnswer st d t k).1.1,
        (drive1D fStepD simResumeV simAnswer st d t k).1.2),
        (drive1D fStepD simResumeV simAnswer st d t k).2.1,
        (drive1D fStepD simResumeV simAnswer st d t k).2.2) := by
  obtain ⟨⟨td', cands, info, zs, keyed, pend, h2, phase⟩, pr⟩ := st
  rcases d with g | o
  · cases phase <;> simp [drive1D, simResumeV, simAnswer, reconC]
  · simp [drive1D]

/-- The state of the simulated world of a state with handles. -/
def reconW (t : SimSt S W Pw K × St Pw K) : SimSt S W Pw K × St Pw K :=
  ((reconC zOf td t.1.1, t.1.2), t.2)

/-- The draw of the simulated world from the draw of the simulated world with handles. -/
def drawMap (e : OEv Pw W) (r : (S × K) × K × K) : (S × K) × K × K :=
  ((zMapE (W := W) zOf e r.1.1, r.1.2), r.2)

theorem run_hOracle_hStep [Fintype S] [Fintype K] [Nonempty K] (t : SimSt S W Pw K × St Pw K)
    (e : OEv Pw W) (r : (S × K) × K × K) :
    (OracleAdv.run (hOracle G zOf td) ((simStartO G msgF t.1 e r.1).bind fun st =>
      .ret ((drive1D fStepD simResumeV simAnswer st.1 st.2 t.2 r.2).2.2,
        ((drive1D fStepD simResumeV simAnswer st.1 st.2 t.2 r.2).1,
          (drive1D fStepD simResumeV simAnswer st.1 st.2 t.2 r.2).2.1))) ()).map
        (fun x => (x.1.1, reconW zOf td x.1.2)) =
      PMF.pure (simWorldD G td (reconW zOf td t) e (drawMap zOf e r)).swap := by
  rw [OracleAdv.run_bind, PMF.map_bind]
  simp only [OracleAdv.run_ret, PMF.pure_map]
  have h := bind_pure_of_map _
    (fun x : (SimSt S W Pw K × Dec Pw W K) × Unit => ((reconC zOf td x.1.1.1, x.1.1.2), x.1.2))
    (fun y => ((drive1D fStepD simResumeV simAnswer y.1 y.2 t.2 r.2).2.2,
      ((drive1D fStepD simResumeV simAnswer y.1 y.2 t.2 r.2).1,
        (drive1D fStepD simResumeV simAnswer y.1 y.2 t.2 r.2).2.1)))
    _ (run_hOracle_simStartO G zOf td msgF hmsg t.1 e r.1)
  refine Eq.trans ?_ h
  refine congrArg _ (funext fun x => ?_)
  rw [drive1D_reconC]
  rfl

/-- **The simulated world with handles at the ideal answers.** For bijections `zOf pid`, a step
of `hImpl` against the ideal answers, with the reconstructed state, is the step of the simulated
world with the table of `H1` as the key. -/
theorem simOracle_hImpl [Fintype S] [DecidableEq S] [Fintype Pw] [Fintype K] [Nonempty K]
    (zE : PartyId → S ≃ S)
    (hzE : ∀ p, ⇑(zE p) = zOf p) (t : SimSt S W Pw K × St Pw K) (e : OEv Pw W) :
    (OracleAdv.simOracle (hImpl G msgF) (hOracle G zOf td) (t, ()) e).map
        (fun y => (y.1, reconW zOf td y.2.1)) =
      idealStep G td (reconW zOf td t) e := by
  unfold idealStep
  have hset : setTd td (reconW zOf td t) = reconW zOf td t := rfl
  rw [hset]
  have hd : (PMF.uniformFintype ((S × K) × K × K)).map (drawMap zOf e) =
      PMF.uniformFintype ((S × K) × K × K) := by
    let φ : S ≃ S := match e with
      | .inl (.newSession _ pid _ _ _) => zE pid
      | _ => Equiv.refl S
    have hφ : ∀ z, φ z = zMapE (W := W) zOf e z := by
      intro z
      rcases e with (⟨_, pid, _, _, _⟩ | _) | _ <;> simp [φ, zMapE, hzE]
    have : drawMap zOf e = (φ.prodCongr (Equiv.refl K)).prodCongr (Equiv.refl (K × K)) := by
      funext r
      obtain ⟨⟨a, b⟩, c⟩ := r
      simp only [drawMap, Equiv.prodCongr_apply, Equiv.coe_refl, Prod.map_apply, id, hφ]
    rw [this, PMF.uniformFintype_map_equiv]
  simp only [OracleAdv.simOracle, hImpl, OracleAdv.run_rand, PMF.map_bind, PMF.map_comp]
  calc _ = (PMF.uniformFintype ((S × K) × K × K)).bind fun r =>
        PMF.pure (simWorldD G td (reconW zOf td t) e (drawMap zOf e r)).swap := by
        refine congrArg _ (funext fun r => ?_)
        rw [← run_hOracle_hStep G zOf td msgF hmsg t e r]
        rfl
    _ = ((PMF.uniformFintype ((S × K) × K × K)).map (drawMap zOf e)).map fun r =>
        (simWorldD G td (reconW zOf td t) e r).swap := by
        rw [PMF.map_comp]
        exact PMF.bind_pure_comp _ _
    _ = _ := by rw [hd]

/-- **Runs of the simulated world with handles at the ideal answers** are runs of the simulated
world with the table of `H1` as the key, from the reconstructed state. -/
theorem run_hImpl [Fintype S] [DecidableEq S] [Fintype Pw] [Fintype K] [Nonempty K] {α : Type}
    (zE : PartyId → S ≃ S) (hzE : ∀ p, ⇑(zE p) = zOf p) (B : OracleAdv (OEv Pw W) (OOut W K) α)
    (t₀ : SimSt S W Pw K × St Pw K) :
    (OracleAdv.run (OracleAdv.simOracle (hImpl G msgF) (hOracle G zOf td)) B (t₀, ())).map
        (Prod.map id fun y => reconW zOf td y.1) =
      OracleAdv.run (idealStep G td) B (reconW zOf td t₀) :=
  OracleAdv.run_map_state _ _ (fun y => reconW zOf td y.1)
    (fun y e => by
      obtain ⟨t, ⟨⟩⟩ := y
      exact simOracle_hImpl G zOf td msgF hmsg zE hzE t e) B (t₀, ())

end Ideal

/-! ## From the joint world to the simulated world with handles -/

section Transport

variable {S W Pw K : Type} [Field S] [Fintype S] [DecidableEq S] [DecidableEq W]
  [Fintype Pw] [DecidableEq Pw] [Fintype K] [Nonempty K] [Inhabited K] (G : DHGroup S W)

/-- The secret of a party is set only for a protocol party with a record. -/
def ZsInv (c : SimCore S W Pw K) : Prop := ∀ pid, (c.info pid = none ∨ 1 < pid) → c.zs pid = none

omit [Fintype S] [DecidableEq S] [DecidableEq W] [Fintype Pw] [DecidableEq Pw] [Fintype K]
  [Nonempty K] [Inhabited K] in
theorem ZsInv.honStepD {c : SimCore S W Pw K} (hc : ZsInv c)
    (o : Option (PartyId × PartyId × PartyId × Role)) (z : S) : ZsInv (honStepD c o z) := by
  intro p hp
  rcases o with _ | ⟨sid, pid, peer, role⟩
  · exact hc p hp
  · by_cases hcond : sid = 0 ∧ pid ≤ 1 ∧ c.info pid = none
    · obtain ⟨hi, hz⟩ := honStepD_new c (peer := peer) (role := role) z hcond
      rw [hi] at hp
      rw [hz]
      by_cases hpp : p = pid
      · subst hpp
        simp only [Function.update_self, reduceCtorEq, false_or] at hp
        obtain ⟨-, hle, -⟩ := hcond
        exact absurd hle (Nat.not_le.mpr hp)
      · rw [Function.update_of_ne hpp] at hp
        split_ifs
        · rw [Function.update_of_ne hpp]; exact hc p hp
        · exact hc p hp
    · obtain ⟨hi, hz⟩ := honStepD_old c (some (sid, pid, peer, role)) z (by
        intro a b d e h; simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl, rfl⟩ := h; exact hcond)
      rw [hi] at hp
      rw [hz]
      exact hc p hp

theorem ZsInv.simWorldD {t : SimSt S W Pw K × St Pw K} (ht : ZsInv t.1.1) (td : Pw → Sˣ)
    (e : OEv Pw W) (r : (S × K) × K × K) : ZsInv (CPaceHops.simWorldD G td t e r).1.1.1 := by
  obtain ⟨hz, hi⟩ := simWorldD_zs G td t e r
  intro p hp
  rw [hz]
  rw [hi] at hp
  rcases e with h | a
  · exact ht.honStepD (honPub h) r.1.1 p hp
  · exact ht p hp

omit [Fintype S] [DecidableEq S] [Fintype Pw] [Fintype K] [Nonempty K] in
/-- A step of the simulated world keeps the table of `H1` of the core. -/
theorem simWorldD_td (td : Pw → Sˣ) (t : SimSt S W Pw K × St Pw K) (e : OEv Pw W)
    (r : (S × K) × K × K) : (CPaceHops.simWorldD G td t e r).1.1.1.td = t.1.1.td := by
  have h₁ := (drive1D_frame (simStartD G td t.1 e r.1).1 (simStartD G td t.1 e r.1).2 t.2 r.2).1
  have h₂ : (CPaceHops.simWorldD G td t e r).1.1.1.td = (simStartD G td t.1 e r.1).1.1.td := by
    simp only [CPaceHops.simWorldD]
    simpa using congrArg SimCore.td h₁
  rw [h₂]
  rcases e with h | a
  · rw [simStartD_inl]
    rcases h with ⟨sid, pid, peer, role, pw⟩ | ⟨sid, pid⟩
    · simp only [honPub, honStepD, honCoreD]
      split_ifs <;> rfl
    · rfl
  · exact (simStartD_inr G td t.1 a r.1).1.td

open Classical in
/-- **From the joint world to the simulated world.** A bad flag of the joint world that reads
only the state of the simulated world is set with the probability of the flag of the simulated
world with the table of `H1` as the key. -/
theorem jointSim_flag_eq (td : Pw → Sˣ) (P : SimSt S W Pw K × St Pw K → Prop)
    (B : OracleAdv (OEv Pw W) (OOut W K) Bool) :
    (OracleAdv.run (OracleAdv.flagWhen (fun _ _ x => P x.2.1.1) (jointSim G td)) B
        (jointInit G, false)).toOuterMeasure {y | y.2.2 = true} =
      (OracleAdv.run (OracleAdv.flagWhen (fun _ _ x => P x.2) (idealStep G td)) B
        (hInit G, false)).toOuterMeasure {y | y.2.2 = true} := by
  have h := OracleAdv.run_map_state (OracleAdv.flagWhen (fun _ _ x => P x.2.1.1) (jointSim G td))
    (OracleAdv.flagWhen (fun _ _ x => P x.2) (idealStep G td))
    (fun y : JSt S W Pw K × Bool => (y.1.1.1, y.2)) (fun y e => by
      simp only [OracleAdv.flagWhen, PMF.map_comp]
      rw [← idealGame_oracle_eq_idealStep, ← jointSim_map G td y.1 e, PMF.map_comp]
      rfl) B (jointInit G, false)
  have hi : ((jointInit G (S := S) (W := W) (Pw := Pw) (K := K), false).1.1.1,
      (jointInit G (S := S) (W := W) (Pw := Pw) (K := K), false).2) = (hInit G, false) := rfl
  rw [hi] at h
  calc _ = ((OracleAdv.run (OracleAdv.flagWhen (fun _ _ x => P x.2.1.1) (jointSim G td)) B
        (jointInit G, false)).map
          (Prod.map id fun y : JSt S W Pw K × Bool => (y.1.1.1, y.2))).toOuterMeasure
          {y | y.2.2 = true} := by rw [PMF.toOuterMeasure_map_apply]; rfl
    _ = _ := congrArg (fun p => PMF.toOuterMeasure p {y | y.2.2 = true}) h

omit [Fintype S] [DecidableEq S] [DecidableEq W] [Fintype Pw] [DecidableEq Pw] [Fintype K]
  [Nonempty K] [Inhabited K] in
theorem setTd_of_td (td : Pw → Sˣ) (t : SimSt S W Pw K × St Pw K) (h : t.1.1.td = some td) :
    setTd td t = t := by
  obtain ⟨⟨⟨td', cands, info, zs, keyed, pend, h2, phase⟩, pr⟩, st⟩ := t
  simp only at h
  subst h
  rfl

omit [DecidableEq S] [Fintype Pw] in
/-- The simulated world with the table of `H1` as the key does not read the table of its core. -/
theorem run_idealStep_setTd {α : Type} (td : Pw → Sˣ) (B : OracleAdv (OEv Pw W) (OOut W K) α)
    (t : SimSt S W Pw K × St Pw K) :
    (OracleAdv.run (idealStep G td) B t).map (Prod.map id (setTd td)) =
      OracleAdv.run (idealStep G td) B (setTd td t) := by
  refine OracleAdv.run_map_state _ _ _ (fun s e => ?_) B t
  simp only [idealStep, PMF.map_comp]
  have hss : setTd td (setTd td s) = setTd td s := rfl
  rw [hss]
  refine congrArg _ (funext fun r => ?_)
  have htd := simWorldD_td G td (setTd td s) e r
  show PMF.pure (Prod.map id (setTd td) (CPaceHops.simWorldD G td (setTd td s) e r).swap) =
    PMF.pure (CPaceHops.simWorldD G td (setTd td s) e r).swap
  congr 1
  exact Prod.ext rfl (setTd_of_td td _ htd)

omit [Fintype S] [DecidableEq S] [DecidableEq W] [Fintype Pw] [DecidableEq Pw] [Fintype K]
  [Nonempty K] [Inhabited K] in
theorem lookup_isSome_cons {α β : Type} [DecidableEq α] {l : List (α × β)} {x : α} (e : α × β)
    (h : (l.lookup x).isSome) : ((e :: l).lookup x).isSome := by
  obtain ⟨a, b⟩ := e
  by_cases hx : x = a
  · subst hx; simp
  · rwa [lookup_cons_ne hx]

omit [Fintype S] [DecidableEq S] [Fintype Pw] [DecidableEq Pw] [Fintype K] [Nonempty K]
  [Inhabited K] in
theorem inDom_grow {s s' : SimSt S W Pw K} (hp : s'.2 = s.2 ∨ ∃ e, s'.2 = e :: s.2)
    (hh : s'.1.h2 = s.1.h2 ∨ ∃ e, s'.1.h2 = e :: s.1.h2) (x : Inp W) (h : InDom s x) :
    InDom s' x := by
  unfold InDom simLk at h ⊢
  cases hs : s.2.lookup x with
  | some k =>
    have : (s'.2.lookup x).isSome := by
      rcases hp with hp | ⟨e, hp⟩ <;> rw [hp]
      · simp [hs]
      · exact lookup_isSome_cons e (by simp [hs])
    obtain ⟨k', hk'⟩ := Option.isSome_iff_exists.1 this
    simp [hk']
  | none =>
    rw [hs] at h
    have hh' : (s'.1.h2.lookup x).isSome := by
      rcases hh with hh | ⟨e, hh⟩ <;> rw [hh]
      · exact h
      · exact lookup_isSome_cons e h
    split <;> simp_all

/-- **The frame of a step of the simulated world**: the invariant `ZsInv` is kept, the secrets
and the session information are kept once set, and the queried passwords and the inputs of `H2`
are kept. -/
theorem simWorldD_step_frame (td : Pw → Sˣ) (t : SimSt S W Pw K × St Pw K) (ht : ZsInv t.1.1)
    (e : OEv Pw W) (r : (S × K) × K × K) :
    ZsInv (CPaceHops.simWorldD G td (setTd td t) e r).1.1.1 ∧
      (∀ pid z, t.1.1.zs pid = some z →
        (CPaceHops.simWorldD G td (setTd td t) e r).1.1.1.zs pid = some z) ∧
      (∀ pid v, t.1.1.info pid = some v →
        (CPaceHops.simWorldD G td (setTd td t) e r).1.1.1.info pid = some v) ∧
      (∀ pw ∈ t.1.1.cands, pw ∈ (CPaceHops.simWorldD G td (setTd td t) e r).1.1.1.cands) ∧
      (∀ y, InDom t.1 y → InDom (CPaceHops.simWorldD G td (setTd td t) e r).1.1 y) := by
  have ht' : ZsInv (setTd td t).1.1 := ht
  obtain ⟨hz, hi⟩ := simWorldD_zs G td (setTd td t) e r
  obtain ⟨hc, hh, hp⟩ := simWorldD_cands_h2 G td (setTd td t) e r
  refine ⟨ht'.simWorldD G td e r, ?_, ?_, hc, inDom_grow hp hh⟩
  · intro pid z hpz
    rw [hz]
    rcases e with h | a
    · rcases h with ⟨sid, p, peer, role, pw⟩ | ⟨sid, p⟩
      · show (honStepD (setTd td t).1.1 (some (sid, p, peer, role)) r.1.1).zs pid = some z
        by_cases hcond : sid = 0 ∧ p ≤ 1 ∧ (setTd td t).1.1.info p = none
        · rw [(honStepD_new _ (peer := peer) (role := role) r.1.1 hcond).2]
          have hne : pid ≠ p := fun hpp => by
            subst hpp
            have := ht pid (Or.inl hcond.2.2)
            simp_all [setTd]
          split_ifs <;> simp [Function.update_of_ne hne, setTd, hpz]
        · rw [(honStepD_old _ (some (sid, p, peer, role)) r.1.1 (by
            intro a b c d h; simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl, rfl⟩ := h; exact hcond)).2]
          exact hpz
      · exact hpz
    · exact hpz
  · intro pid v hpv
    rw [hi]
    rcases e with h | a
    · rcases h with ⟨sid, p, peer, role, pw⟩ | ⟨sid, p⟩
      · show (honStepD (setTd td t).1.1 (some (sid, p, peer, role)) r.1.1).info pid = some v
        by_cases hcond : sid = 0 ∧ p ≤ 1 ∧ (setTd td t).1.1.info p = none
        · rw [(honStepD_new _ (peer := peer) (role := role) r.1.1 hcond).1]
          have hne : pid ≠ p := fun hpp => by
            subst hpp
            have := hcond.2.2
            simp_all [setTd]
          simp [Function.update_of_ne hne, setTd, hpv]
        · rw [(honStepD_old _ (some (sid, p, peer, role)) r.1.1 (by
            intro a b c d h; simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl, rfl, rfl⟩ := h; exact hcond)).1]
          exact hpv
      · exact hpv
    · exact hpv

/-- The frame of a step of the simulated world with the table of `H1` as the key. -/
theorem ideal_step_frame (td : Pw → Sˣ) (t : SimSt S W Pw K × St Pw K) (ht : ZsInv t.1.1)
    (e : OEv Pw W) (x : OOut W K × (SimSt S W Pw K × St Pw K))
    (hx : x ∈ (idealStep G td t e).support) :
    ZsInv x.2.1.1 ∧ (∀ pid z, t.1.1.zs pid = some z → x.2.1.1.zs pid = some z) ∧
      (∀ pid v, t.1.1.info pid = some v → x.2.1.1.info pid = some v) ∧
      (∀ pw ∈ t.1.1.cands, pw ∈ x.2.1.1.cands) ∧ (∀ y, InDom t.1 y → InDom x.2.1 y) := by
  obtain ⟨r, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).1 hx
  exact simWorldD_step_frame G td t ht e r

/-- The frame of a step of the joint world, for its simulated part. -/
theorem joint_step_frame (td : Pw → Sˣ) (s : JSt S W Pw K) (ht : ZsInv s.1.1.1.1)
    (e : OEv Pw W) (x : OOut W K × JSt S W Pw K) (hx : x ∈ (jointSim G td s e).support) :
    ZsInv x.2.1.1.1.1 ∧ (∀ pid z, s.1.1.1.1.zs pid = some z → x.2.1.1.1.1.zs pid = some z) ∧
      (∀ pid v, s.1.1.1.1.info pid = some v → x.2.1.1.1.1.info pid = some v) ∧
      (∀ pw ∈ s.1.1.1.1.cands, pw ∈ x.2.1.1.1.1.cands) ∧
      (∀ y, InDom s.1.1.1 y → InDom x.2.1.1.1 y) := by
  obtain ⟨r, hr⟩ := mem_support_jointSim G hx
  rw [hr]
  exact simWorldD_step_frame G td s.1.1 ht e r

end Transport

/-! ## The double-match experiment -/

section DM

variable {S W Pw K : Type} [Field S] [Fintype S] [DecidableEq S] [DecidableEq W]
  [Fintype Pw] [DecidableEq Pw] [Fintype K] [Nonempty K] [Inhabited K] (G : DHGroup S W)

/-- **A double match on queried passwords** for a protocol party with a secret other than zero. -/
def DMc (td : Pw → Sˣ) (s : SimSt S W Pw K) : Prop :=
  ∃ pid x₁ x₂ pw₁ pw₂ z, pid ≤ 1 ∧ s.1.zs pid = some z ∧ z ≠ 0 ∧ InDom s x₁ ∧ InDom s x₂ ∧
    x₁.tr = x₂.tr ∧ pw₁ ≠ pw₂ ∧ pw₁ ∈ s.1.cands ∧ pw₂ ∈ s.1.cands ∧
    Matches G td s.1 pid pw₁ x₁ ∧ Matches G td s.1 pid pw₂ x₂

/-- A party has the secret zero. -/
def Z0 (s : SimSt S W Pw K) : Prop := ∃ pid, s.1.zs pid = some 0

omit [Fintype S] [DecidableEq S] [Fintype Pw] [Fintype K] [Nonempty K] [Inhabited K] in
/-- **A double match splits**: on queried passwords with a secret other than zero, or on an
unqueried password, or with the secret zero. -/
theorem dm_split (td : Pw → Sˣ) (s : SimSt S W Pw K) (hI : ZsInv s.1) (h : DMst G td s) :
    DMc G td s ∨ UQst G td s ∨ Z0 s := by
  obtain ⟨pid, x₁, x₂, pw₁, pw₂, h₁, h₂, htr, hne, hm₁, hm₂⟩ := h
  obtain ⟨z, peer, role, hz, -⟩ := id hm₁
  have hpid : pid ≤ 1 := by
    by_contra hp
    have := hI pid (Or.inr (Nat.lt_of_not_le hp))
    rw [hz] at this
    exact absurd this (by simp)
  by_cases hz0 : z = 0
  · exact Or.inr (Or.inr ⟨pid, hz0 ▸ hz⟩)
  by_cases hc₁ : pw₁ ∈ s.1.cands
  · by_cases hc₂ : pw₂ ∈ s.1.cands
    · exact Or.inl ⟨pid, x₁, x₂, pw₁, pw₂, z, hpid, hz, hz0, h₁, h₂, htr, hne, hc₁, hc₂, hm₁, hm₂⟩
    · exact Or.inr (Or.inl ⟨pid, x₂, pw₂, h₂, hc₂, hm₂⟩)
  · exact Or.inr (Or.inl ⟨pid, x₁, pw₁, h₁, hc₁, hm₁⟩)

omit [Fintype S] [DecidableEq S] [Fintype Pw] [DecidableEq Pw] [Fintype K] [Nonempty K]
  [Inhabited K] in
theorem matches_stable (td : Pw → Sˣ) {c c' : SimCore S W Pw K}
    (hz : ∀ pid z, c.zs pid = some z → c'.zs pid = some z)
    (hi : ∀ pid v, c.info pid = some v → c'.info pid = some v) {pid : PartyId} {pw : Pw}
    {x : Inp W} (h : Matches G td c pid pw x) : Matches G td c' pid pw x := by
  obtain ⟨z, peer, role, h₁, h₂, h₃, h₄⟩ := h
  exact ⟨z, peer, role, hz pid z h₁, hi pid _ h₂, h₃, h₄⟩

omit [Fintype S] [DecidableEq S] [Fintype Pw] [DecidableEq Pw] [Fintype K] [Nonempty K]
  [Inhabited K] in
theorem DMc_stable (td : Pw → Sˣ) {s s' : SimSt S W Pw K}
    (hz : ∀ pid z, s.1.zs pid = some z → s'.1.zs pid = some z)
    (hi : ∀ pid v, s.1.info pid = some v → s'.1.info pid = some v)
    (hc : ∀ pw ∈ s.1.cands, pw ∈ s'.1.cands) (hd : ∀ y, InDom s y → InDom s' y)
    (h : DMc G td s) : DMc G td s' := by
  obtain ⟨pid, x₁, x₂, pw₁, pw₂, z, hp, hzs, hz0, h₁, h₂, htr, hne, hc₁, hc₂, hm₁, hm₂⟩ := h
  exact ⟨pid, x₁, x₂, pw₁, pw₂, z, hp, hz pid z hzs, hz0, hd _ h₁, hd _ h₂, htr, hne, hc _ hc₁,
    hc _ hc₂, matches_stable G td hz hi hm₁, matches_stable G td hz hi hm₂⟩

theorem zsInv_jointInit : ZsInv (jointInit G (S := S) (W := W) (Pw := Pw) (K := K)).1.1.1.1 :=
  fun _ _ => rfl

open Classical in
/-- **The double-match flag splits** into the flags of a double match on queried passwords, of an
unqueried match, and of a zero secret. -/
theorem dm_flag_split (td : Pw → Sˣ) (B : OracleAdv (OEv Pw W) (OOut W K) Bool) :
    (OracleAdv.run (OracleAdv.flagWhen (fun _ _ x => DMst G td x.2.1.1.1) (jointSim G td)) B
        (jointInit G, false)).toOuterMeasure {y | y.2.2 = true} ≤
      (OracleAdv.run (OracleAdv.flagWhen (fun _ _ x => DMc G td x.2.1.1.1) (jointSim G td)) B
        (jointInit G, false)).toOuterMeasure {y | y.2.2 = true} +
      (OracleAdv.run (OracleAdv.flagWhen (fun _ _ x => UQst G td x.2.1.1.1) (jointSim G td)) B
        (jointInit G, false)).toOuterMeasure {y | y.2.2 = true} +
      (OracleAdv.run (OracleAdv.flagWhen (fun _ _ x => Z0 x.2.1.1.1) (jointSim G td)) B
        (jointInit G, false)).toOuterMeasure {y | y.2.2 = true} := by
  have h₁ := OracleAdv.run_flagWhen_le_of_inv (jointSim G td)
    (fun _ _ x => DMst G td x.2.1.1.1)
    (fun _ _ x => DMc G td x.2.1.1.1 ∨ (UQst G td x.2.1.1.1 ∨ Z0 x.2.1.1.1))
    (fun s => ZsInv s.1.1.1.1) (fun s e hs x hx => by
      have hI := (joint_step_frame G td s hs e x hx).1
      by_cases hd : DMst G td x.2.1.1.1
      · exact Or.inl (dm_split G td _ hI hd)
      · exact Or.inr ⟨hd, hI⟩) B (jointInit G) (zsInv_jointInit G)
  have h₂ := OracleAdv.run_flagWhen_or_le (jointSim G td) (fun _ _ x => DMc G td x.2.1.1.1)
    (fun _ _ x => UQst G td x.2.1.1.1 ∨ Z0 x.2.1.1.1) B (jointInit G)
  have h₃ := OracleAdv.run_flagWhen_or_le (jointSim G td) (fun _ _ x => UQst G td x.2.1.1.1)
    (fun _ _ x => Z0 x.2.1.1.1) B (jointInit G)
  rw [add_assoc]
  exact h₁.trans (h₂.trans (add_le_add_right h₃ _))

open Classical in
/-- **A zero secret** is set with probability at most `2 / |S|`. -/
theorem z0_flag_le (td : Pw → Sˣ) (B : OracleAdv (OEv Pw W) (OOut W K) Bool) (q : ℕ)
    (hB : B.IsQueryBound q) :
    (OracleAdv.run (OracleAdv.flagWhen (fun _ _ x => Z0 x.2.1.1.1) (jointSim G td)) B
        (jointInit G, false)).toOuterMeasure {y | y.2.2 = true} ≤
      2 * (Fintype.card S : ℝ≥0∞)⁻¹ := by
  refine (OracleAdv.run_flagWhen_le_of_inv (jointSim G td) (fun _ _ x => Z0 x.2.1.1.1)
    (fun s _ x => NewSecret (fun _ z => z = (0 : S)) s.1 x.2.1)
    (fun s => ZsInv s.1.1.1.1 ∧ ¬ Z0 s.1.1.1) (fun s e hs x hx => ?_) B (jointInit G)
    ⟨zsInv_jointInit G, fun ⟨_, h⟩ => by simp [jointInit, simProt] at h⟩).trans
    (run_flag_newZero_le G td B q hB)
  obtain ⟨hI, hz, -⟩ := joint_step_frame G td s hs.1 e x hx
  by_cases h0 : Z0 x.2.1.1.1
  · left
    obtain ⟨pid, hpid⟩ := h0
    cases hsz : s.1.1.1.1.zs pid with
    | none => exact ⟨pid, 0, hsz, hpid, rfl⟩
    | some z =>
      have := hz pid z hsz
      rw [hpid] at this
      cases this
      exact absurd ⟨pid, hsz⟩ hs.2
  · exact Or.inr ⟨h0, hI, h0⟩

/-! ### The reduction to the CPace experiment -/

omit [Fintype S] [DecidableEq S] [Fintype Pw] [DecidableEq Pw] [Fintype K] [Nonempty K]
  [Inhabited K] in
/-- **A match test of a scaled secret** is a match test of the CPace experiment: the key `k` for
the secret `x u` passes iff `k^{1/u}` passes for `x`. -/
theorem kit_matchTest_scale (td : Pw → Sˣ) (x u : S) (hu : u ≠ 0) (peer k : W) (pw : Pw) :
    (kit G td).matchTest (x * u) peer k pw =
      CPaceH1.matchTest G (G.pub x) (G.pub (td pw)) (pw, peer, G.exp k u⁻¹) := by
  have ht : (td pw : S) ≠ 0 := (td pw).ne_zero
  rw [Bool.eq_iff_iff, kit, cpace_matchTest_iff]
  simp only [CPaceH1.matchTest, decide_eq_true_eq]
  refine and_congr_right fun _ => ?_
  simp only [DHGroup.cdhIn, DHGroup.exp_eq, DHGroup.dlog_pub]
  conv_lhs => rw [← G.pub_dlog k]
  rw [G.pub.injective.eq_iff, G.pub.injective.eq_iff]
  constructor
  · intro h; rw [h]; field_simp
  · intro h
    have := congrArg (· * u) h
    rw [mul_assoc, inv_mul_cancel₀ hu, mul_one] at this
    rw [this]; ring

omit [Fintype S] [DecidableEq S] [Fintype Pw] [DecidableEq Pw] [Fintype K] [Nonempty K]
  [Inhabited K] in
/-- A match test of the secret zero passes iff the peer message is not the identity and the key
is the identity. -/
theorem kit_matchTest_zero (td : Pw → Sˣ) (peer k : W) (pw : Pw) :
    (kit G td).matchTest 0 peer k pw = decide (peer ≠ G.pub 0 ∧ k = G.pub 0) := by
  rw [Bool.eq_iff_iff, kit, cpace_matchTest_iff]
  simp only [decide_eq_true_eq, DHGroup.cdhIn, DHGroup.exp_eq, DHGroup.dlog_pub, mul_zero,
    zero_mul]

/-- The message of a party with handle `u` in the double-match reduction: `X^u`. -/
def msgDM (X : W) (_ : PartyId) (u : S) : W := G.exp X u

/-- **The translation of the double-match reduction**: `H1` is forwarded, and the match test of a
party with handle `u ≠ 0` for the key `k` is the match query `(pw, peer, k^{1/u})` of the CPace
experiment; for `u = 0` it is answered directly. -/
def dmTrans (_ : Unit) : HQ S W Pw →
    OracleAdv (CPaceH1.Query W Pw) (CPaceH1.Answer W) (HA W × Unit)
  | .inl pw => .query (.inl pw) fun a => .ret (a, ())
  | .inr (_, u, pw, peer, k) =>
    if u = 0 then .ret (.inr (decide (peer ≠ G.pub 0 ∧ k = G.pub 0)), ())
    else .query (.inr (pw, peer, G.exp k u⁻¹)) fun a => .ret (a, ())

/-- The match queries of the final sweep: every input of the simulator's tables, for each party
of the session `0` with a handle and each queried password. -/
def sweepQ (s : SimSt S W Pw K) : List (HQ S W Pw) :=
  (s.2.map Prod.fst ++ s.1.h2.map Prod.fst).flatMap fun x =>
    ([0, 1] : List PartyId).flatMap fun pid =>
      match s.1.zs pid with
      | some u => s.1.cands.map fun pw => .inr (pid, u, pw, peerMsg pid x, x.2.2.2)
      | none => []

/-- Asks the queries of a list in order. -/
def queryAll : List (HQ S W Pw) → OracleAdv (HQ S W Pw) (HA W) Unit
  | [] => .ret ()
  | q :: l => .query q fun _ => queryAll l

/-- **The double-match adversary of the CPace experiment.** On the simulated message `X` it runs
the oracle adversary `B` against the simulated world with handles, a party with handle `u` sending
`X^u`, then asks the match tests of the final sweep, all translated by `dmTrans`. -/
noncomputable def dmAdv (B : OracleAdv (OEv Pw W) (OOut W K) Bool) :
    CPaceH1.CPaceAdversary W Pw Unit := fun X =>
  (OracleAdv.simulate (dmTrans G)
    ((OracleAdv.simulate (hImpl G (msgDM G X)) B (hInit G)).bind fun p =>
      queryAll (sweepQ p.2.1)) ()).bind fun _ => .ret ()

/-- The log of the CPace experiment after a translated query. -/
def dmLog (x : S) (td : Pw → Sˣ) : HQ S W Pw → CPaceH1.MatchLog W Pw → CPaceH1.MatchLog W Pw
  | .inl _, log => log
  | .inr (_, u, pw, peer, k), log =>
    if u = 0 then log
    else if CPaceH1.matchTest G (G.pub x) (G.pub (td pw)) (pw, peer, G.exp k u⁻¹) then
      (pw, peer, G.exp k u⁻¹) :: log else log

omit [Fintype S] [Fintype Pw] [DecidableEq Pw] [Fintype K] [Nonempty K] [Inhabited K] in
/-- **The translation answers with the ideal answers** of the bijections `u ↦ x u`. -/
theorem simOracle_dmTrans (x : S) (td : Pw → Sˣ) (log : CPaceH1.MatchLog W Pw) (q : HQ S W Pw) :
    OracleAdv.simOracle (dmTrans G)
        (CPaceH1.eagerOracle CPaceH1.Query.pw (CPaceH1.cpaceStep G (G.pub x)) td) ((), log) q =
      PMF.pure (hAns G (fun _ u => x * u) td q, ((), dmLog G x td q log)) := by
  rcases q with pw | ⟨pid, u, pw, peer, k⟩
  · simp [OracleAdv.simOracle, dmTrans, CPaceH1.eagerOracle, CPaceH1.cpaceStep,
      CPaceH1.Query.pw, hAns, dmLog, PMF.pure_map]
  · by_cases hu : u = 0
    · subst hu
      simp [OracleAdv.simOracle, dmTrans, hAns, dmLog, PMF.pure_map, kit_matchTest_zero]
    · simp [OracleAdv.simOracle, dmTrans, CPaceH1.eagerOracle, CPaceH1.cpaceStep,
        CPaceH1.Query.pw, hAns, dmLog, PMF.pure_map, hu, kit_matchTest_scale G td x u hu]
      rfl

omit [Fintype S] [Fintype Pw] [DecidableEq Pw] [Fintype K] [Nonempty K] [Inhabited K] in
theorem run_queryAll_dm (x : S) (td : Pw → Sˣ) (l : List (HQ S W Pw))
    (log : CPaceH1.MatchLog W Pw) :
    OracleAdv.run (OracleAdv.simOracle (dmTrans G)
        (CPaceH1.eagerOracle CPaceH1.Query.pw (CPaceH1.cpaceStep G (G.pub x)) td))
      (queryAll l) ((), log) =
      PMF.pure ((), ((), l.foldl (fun lg q => dmLog G x td q lg) log)) := by
  induction l generalizing log with
  | nil => rfl
  | cons q l ih => simp [queryAll, simOracle_dmTrans, ih]

omit [Fintype S] [DecidableEq S] [DecidableEq W] [Fintype Pw] [DecidableEq Pw] [Fintype K]
  [Nonempty K] [Inhabited K] in
theorem mem_foldl_dmLog [DecidableEq S] [DecidableEq W] (x : S) (td : Pw → Sˣ)
    (l : List (HQ S W Pw)) (log : CPaceH1.MatchLog W Pw) (m : Pw × W × W) (hm : m ∈ log) :
    m ∈ l.foldl (fun lg q => dmLog G x td q lg) log := by
  induction l generalizing log with
  | nil => exact hm
  | cons q l ih =>
    refine ih _ ?_
    rcases q with pw | ⟨pid, u, pw, peer, k⟩
    · exact hm
    · simp only [dmLog]
      split_ifs <;> simp [hm]

omit [Fintype S] [DecidableEq S] [DecidableEq W] [Fintype Pw] [DecidableEq Pw] [Fintype K]
  [Nonempty K] [Inhabited K] in
/-- **A logged sweep query.** A translated match query of a handle other than zero that matches
is in the final log. -/
theorem logged_of_mem [DecidableEq S] [DecidableEq W] (x : S) (td : Pw → Sˣ)
    (l : List (HQ S W Pw)) (log : CPaceH1.MatchLog W Pw) {pid : PartyId} {u : S} {pw : Pw}
    {peer k : W} (hq : .inr (pid, u, pw, peer, k) ∈ l) (hu : u ≠ 0)
    (hm : CPaceH1.matchTest G (G.pub x) (G.pub (td pw)) (pw, peer, G.exp k u⁻¹) = true) :
    (pw, peer, G.exp k u⁻¹) ∈ l.foldl (fun lg q => dmLog G x td q lg) log := by
  induction l generalizing log with
  | nil => simp at hq
  | cons q l ih =>
    rcases List.mem_cons.1 hq with rfl | hq
    · refine mem_foldl_dmLog G x td l _ _ ?_
      simp [dmLog, hu, hm]
    · exact ih _ hq

omit [Fintype S] [Fintype Pw] [DecidableEq Pw] [Fintype K] [Nonempty K] [Inhabited K] in
/-- **The sweep finds a double match.** A double match on queried passwords with a secret other
than zero, in the simulated world of a state with handles, is a double match of the log after the
sweep. -/
theorem doubleMatch_of_DMc (x : S) (td : Pw → Sˣ) (w : SimSt S W Pw K × St Pw K)
    (log : CPaceH1.MatchLog W Pw) (h : DMc G td (reconW (fun _ u => x * u) td w).1) :
    CPaceH1.DoubleMatch ((sweepQ w.1).foldl (fun lg q => dmLog G x td q lg) log) := by
  obtain ⟨pid, x₁, x₂, pw₁, pw₂, z, hp, hzs, hz0, h₁, h₂, htr, hne, hc₁, hc₂, hm₁, hm₂⟩ := h
  have hzs' : (w.1.1.zs pid).map (fun u => x * u) = some z := hzs
  obtain ⟨u, hu, rfl⟩ := Option.map_eq_some_iff.1 hzs'
  have hu0 : u ≠ 0 := fun h0 => hz0 (by simp [h0])
  have hpid : pid ∈ ([0, 1] : List PartyId) := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hp with rfl | rfl <;> simp
  have key : ∀ y, InDom (reconW (fun _ u => x * u) td w).1 y →
      y ∈ w.1.2.map Prod.fst ++ w.1.1.h2.map Prod.fst := by
    intro y hy
    unfold InDom simLk at hy
    cases hk : w.1.2.lookup y with
    | some k => exact List.mem_append_left _ (mem_map_fst_of_lookup (by simp [hk]))
    | none =>
      have hk' : (reconW (fun _ u => x * u) td w).1.2.lookup y = none := hk
      rw [hk'] at hy
      exact List.mem_append_right _ (mem_map_fst_of_lookup hy)
  have logged : ∀ pw y, pw ∈ w.1.1.cands → InDom (reconW (fun _ u => x * u) td w).1 y →
      Matches G td (reconW (fun _ u => x * u) td w).1.1 pid pw y →
      (pw, peerMsg pid y, G.exp y.2.2.2 u⁻¹) ∈
        (sweepQ w.1).foldl (fun lg q => dmLog G x td q lg) log := by
    intro pw y hc hy hm
    obtain ⟨z', peer, role, hz', -, -, hmt⟩ := hm
    have hz'' : (w.1.1.zs pid).map (fun u => x * u) = some z' := hz'
    rw [hu] at hz''
    simp only [Option.map_some, Option.some.injEq] at hz''
    subst hz''
    refine logged_of_mem G x td _ log (pid := pid) ?_ hu0
      ((kit_matchTest_scale G td x u hu0 _ _ pw).symm.trans hmt)
    refine List.mem_flatMap.2 ⟨y, key y hy, List.mem_flatMap.2 ⟨pid, hpid, ?_⟩⟩
    rw [hu]
    exact List.mem_map.2 ⟨pw, hc, rfl⟩
  exact ⟨_, logged pw₁ x₁ hc₁ h₁ hm₁, _, logged pw₂ x₂ hc₂ h₂ hm₂, peerMsg_eq_of_tr htr, hne⟩

omit [Fintype S] [Fintype Pw] [DecidableEq Pw] [Fintype K] [Nonempty K] [Inhabited K] in
theorem simOracle_dmTrans_proj (x : S) (td : Pw → Sˣ) (u : Unit × CPaceH1.MatchLog W Pw)
    (q : HQ S W Pw) :
    (OracleAdv.simOracle (dmTrans G)
        (CPaceH1.eagerOracle CPaceH1.Query.pw (CPaceH1.cpaceStep G (G.pub x)) td) u q).map
        (Prod.map id fun _ => ()) =
      hOracle G (fun _ u => x * u) td ((fun _ => ()) u) q := by
  obtain ⟨⟨⟩, log⟩ := u
  rw [simOracle_dmTrans]
  simp [PMF.pure_map, hOracle]

omit [Fintype Pw] in
/-- **Forgetting the log of the CPace experiment**: the simulated world with handles over the
translation runs as over the ideal answers. -/
theorem run_dm_proj {α : Type} (x : S) (td : Pw → Sˣ) (msgF : PartyId → S → W)
    (B : OracleAdv (OEv Pw W) (OOut W K) α) (w : SimSt S W Pw K × St Pw K)
    (log : CPaceH1.MatchLog W Pw) :
    (OracleAdv.run (OracleAdv.simOracle (hImpl G msgF) (OracleAdv.simOracle (dmTrans G)
        (CPaceH1.eagerOracle CPaceH1.Query.pw (CPaceH1.cpaceStep G (G.pub x)) td))) B
        (w, ((), log))).map (Prod.map id (Prod.map id fun _ => ())) =
      OracleAdv.run (OracleAdv.simOracle (hImpl G msgF) (hOracle G (fun _ u => x * u) td)) B
        (w, ()) :=
  OracleAdv.run_map_state _ _ (Prod.map id fun _ => ()) (fun st e =>
    OracleAdv.simOracle_map_inner _ _ _ (fun _ => ()) (simOracle_dmTrans_proj G x td) st.1 st.2 e)
    B (w, ((), log))

/-- **The run of the double-match adversary**: its final log is the log of the sweep after the run
of `B` against the simulated world with handles over the translation. -/
theorem run_dmAdv (x : S) (td : Pw → Sˣ) (B : OracleAdv (OEv Pw W) (OOut W K) Bool) :
    OracleAdv.run (CPaceH1.eagerOracle CPaceH1.Query.pw (CPaceH1.cpaceStep G (G.pub x)) td)
        (dmAdv G B (G.pub x)) [] =
      (OracleAdv.run (OracleAdv.simOracle (hImpl G (msgDM G (G.pub x)))
        (OracleAdv.simOracle (dmTrans G)
          (CPaceH1.eagerOracle CPaceH1.Query.pw (CPaceH1.cpaceStep G (G.pub x)) td))) B
        (hInit G, ((), []))).map fun z =>
          ((), (sweepQ z.2.1.1).foldl (fun lg q => dmLog G x td q lg) z.2.2.2) := by
  simp only [dmAdv, OracleAdv.run_bind, OracleAdv.run_simulate, OracleAdv.run_ret,
    PMF.map_bind]
  simp only [PMF.bind_map, Function.comp_def, PMF.bind_bind]
  rw [← PMF.bind_pure_comp]
  refine congrArg _ (funext fun z => ?_)
  obtain ⟨b, w, ⟨⟩, log⟩ := z
  simp [run_queryAll_dm]

/-- **The simulated world against the double-match adversary.** For `x ≠ 0`, a double match on
queried passwords with a secret other than zero at the end of the simulated world has at most the
probability of a double match of the CPace experiment against `dmAdv G B` on `g^x`. -/
theorem dm_ideal_le_eager (x : S) (hx : x ≠ 0) (td : Pw → Sˣ)
    (B : OracleAdv (OEv Pw W) (OOut W K) Bool) :
    (OracleAdv.run (idealStep G td) B (setTd td (hInit G))).toOuterMeasure
        {y | DMc G td y.2.1} ≤
      ((OracleAdv.run (CPaceH1.eagerOracle CPaceH1.Query.pw (CPaceH1.cpaceStep G (G.pub x)) td)
        (dmAdv G B (G.pub x)) []).map fun y => decide (CPaceH1.DoubleMatch y.2)) true := by
  classical
  have hmsg : ∀ pid u, msgDM G (G.pub x) pid u = G.pub ((fun _ u => x * u) pid u) :=
    fun _ u => G.exp_pub x u
  have hT := run_hImpl G (fun _ u => x * u) td (msgDM G (G.pub x)) hmsg
    (fun _ => Equiv.mulLeft₀ x hx) (fun _ => rfl) B (hInit G)
  have hinit : reconW (fun _ u => x * u) td (hInit G (S := S) (W := W) (Pw := Pw) (K := K)) =
      setTd td (hInit G) := rfl
  rw [hinit] at hT
  have e1 := OracleAdv.toOuterMeasure_eq_of_map_eq hT {y | DMc G td y.2.1}
  have e2 := OracleAdv.toOuterMeasure_eq_of_map_eq
    (run_dm_proj G x td (msgDM G (G.pub x)) B (hInit G) [])
    ((Prod.map id fun y => reconW (fun _ u => x * u) td y.1) ⁻¹' {y | DMc G td y.2.1})
  rw [← e1, ← e2, run_dmAdv, PMF.map_comp, ← PMF.toOuterMeasure_apply_singleton,
    PMF.toOuterMeasure_map_apply]
  refine PMF.toOuterMeasure_mono _ fun z hz => ?_
  simp only [Set.mem_preimage, Function.comp_apply, Set.mem_singleton_iff,
    decide_eq_true_eq] at hz ⊢
  exact doubleMatch_of_DMc G x td z.2.1 z.2.2.2 hz.1

open Classical in
/-- The double match on queried passwords with a secret other than zero, in the joint world, is
bounded by its probability at the end of the simulated world. -/
theorem dmc_flag_le (td : Pw → Sˣ) (B : OracleAdv (OEv Pw W) (OOut W K) Bool) :
    (OracleAdv.run (OracleAdv.flagWhen (fun _ _ x => DMc G td x.2.1.1.1) (jointSim G td)) B
        (jointInit G, false)).toOuterMeasure {y | y.2.2 = true} ≤
      (OracleAdv.run (idealStep G td) B (setTd td (hInit G))).toOuterMeasure
        {y | DMc G td y.2.1} := by
  rw [jointSim_flag_eq G td (fun y => DMc G td y.1) B]
  have h₁ := OracleAdv.run_flagWhen_le_of_inv (idealStep G td) (fun _ _ x => DMc G td x.2.1)
    (fun _ _ x => DMc G td x.2.1 ∧ ZsInv x.2.1.1) (fun t => ZsInv t.1.1)
    (fun t e ht x hx => by
      have hI := (ideal_step_frame G td t ht e x hx).1
      by_cases hd : DMc G td x.2.1
      · exact Or.inl ⟨hd, hI⟩
      · exact Or.inr ⟨hd, hI⟩) B (hInit G) (fun _ _ => rfl)
  have h₂ := OracleAdv.run_flagWhen_le_final (idealStep G td)
    (fun y => DMc G td y.1 ∧ ZsInv y.1.1) (fun t e ht x hx => by
      obtain ⟨hI, hz, hi, hc, hd⟩ := ideal_step_frame G td t ht.2 e x hx
      exact ⟨DMc_stable G td hz hi hc hd ht.1, hI⟩) B (hInit G)
  refine h₁.trans (h₂.trans ?_)
  rw [← run_idealStep_setTd G td B (hInit G), PMF.toOuterMeasure_map_apply]
  exact PMF.toOuterMeasure_mono _ fun y hy => hy.1.1

/-- **The double-match experiment.** For an oracle adversary `B` with at most `q` queries, the
probability of a double match is at most twice the success probability of the strong SDH
reduction of the double-match adversary `dmAdv G B`, plus the probability of an unqueried match and
`3 / |S|`. -/
theorem dmExp_le [Inhabited Pw] (B : OracleAdv (OEv Pw W) (OOut W K) Bool) (q : ℕ)
    (hB : B.IsQueryBound q) :
    dmExp G B true ≤ 2 * ssdhGame G (ssdhReduction G (CPaceH1.matchWrap (dmAdv G B))) true +
      uqExp G B true + 3 * (Fintype.card S : ℝ≥0∞)⁻¹ := by
  classical
  set ε : ℝ≥0∞ := (Fintype.card S : ℝ≥0∞)⁻¹
  set Q : (Pw → Sˣ) → ℝ≥0∞ := fun td =>
    (OracleAdv.run (idealStep G td) B (setTd td (hInit G))).toOuterMeasure {y | DMc G td y.2.1}
  have hinner : ∀ td : Pw → Sˣ,
      ((OracleAdv.run (OracleAdv.flagWhen (fun s _ x => DMst G td x.2.1.1.1) (jointSim G td)) B
        (jointInit G, false)).map fun y => y.2.2) true ≤
      Q td + ((OracleAdv.run (OracleAdv.flagWhen (fun s _ x => UQst G td x.2.1.1.1)
        (jointSim G td)) B (jointInit G, false)).map fun y => y.2.2) true + 2 * ε := by
    intro td
    rw [flagExp_inner_apply G td (fun td _ s' => DMst G td s'.1.1) B,
      flagExp_inner_apply G td (fun td _ s' => UQst G td s'.1.1) B]
    exact (dm_flag_split G td B).trans (add_le_add (add_le_add (dmc_flag_le G td B) le_rfl)
      (z0_flag_le G td B q hB))
  have hQ : ∑' td : Pw → Sˣ, PMF.uniformFintype (Pw → Sˣ) td * Q td ≤
      CPaceH1.eagerGame G (dmAdv G B) true + ε := by
    have hsplit : ∑' td : Pw → Sˣ, PMF.uniformFintype (Pw → Sˣ) td * Q td =
        ∑' z : S, PMF.uniformFintype S z *
          ∑' td : Pw → Sˣ, PMF.uniformFintype (Pw → Sˣ) td * Q td := by
      rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    rw [hsplit, CPaceH1.eagerGame, PMF.bind_apply]
    calc _ ≤ ∑' z : S, (PMF.uniformFintype S z * (if z = 0 then 1 else 0) +
          PMF.uniformFintype S z * ((PMF.uniformFintype (Pw → Sˣ)).bind fun td =>
            (OracleAdv.run (CPaceH1.eagerOracle CPaceH1.Query.pw
              (CPaceH1.cpaceStep G (G.pub z)) td) (dmAdv G B (G.pub z)) []).map
              fun y => decide (CPaceH1.DoubleMatch y.2)) true) := by
          refine ENNReal.tsum_le_tsum fun z => ?_
          rw [← mul_add]
          gcongr
          by_cases hz : z = 0
          · simp only [hz, ↓reduceIte]
            refine le_add_right ?_
            calc _ ≤ ∑' td : Pw → Sˣ, PMF.uniformFintype (Pw → Sˣ) td * 1 :=
                  ENNReal.tsum_le_tsum fun td => by
                    gcongr
                    exact (MeasureTheory.measure_mono (Set.subset_univ _)).trans_eq
                      ((PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr (Set.subset_univ _))
              _ = 1 := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
          · simp only [hz, ↓reduceIte, zero_add, PMF.bind_apply]
            exact ENNReal.tsum_le_tsum fun td => by gcongr; exact dm_ideal_le_eager G z hz td B
      _ = ε + _ := by
          rw [ENNReal.tsum_add]
          congr 1
          rw [tsum_eq_single 0 fun z hz => by simp [hz]]
          simp [ε]
      _ = _ := add_comm _ _
  have hE : CPaceH1.eagerGame G (dmAdv G B) true ≤
      2 * ssdhGame G (ssdhReduction G (CPaceH1.matchWrap (dmAdv G B))) true := by
    rw [← CPaceH1.lazyGame_eq_eagerGame]
    exact CPaceH1.lazyGame_le_ssdhGame G _
  unfold dmExp uqExp flagExp
  rw [PMF.bind_apply, PMF.bind_apply]
  calc _ ≤ ∑' td : Pw → Sˣ, (PMF.uniformFintype (Pw → Sˣ) td * Q td +
        PMF.uniformFintype (Pw → Sˣ) td *
          ((OracleAdv.run (OracleAdv.flagWhen (fun s _ x => UQst G td x.2.1.1.1)
            (jointSim G td)) B (jointInit G, false)).map fun y => y.2.2) true +
        PMF.uniformFintype (Pw → Sˣ) td * (2 * ε)) := by
        refine ENNReal.tsum_le_tsum fun td => ?_
        rw [← mul_add, ← mul_add]
        gcongr
        exact hinner td
    _ = ∑' td : Pw → Sˣ, PMF.uniformFintype (Pw → Sˣ) td * Q td +
        ∑' td : Pw → Sˣ, PMF.uniformFintype (Pw → Sˣ) td *
          ((OracleAdv.run (OracleAdv.flagWhen (fun s _ x => UQst G td x.2.1.1.1)
            (jointSim G td)) B (jointInit G, false)).map fun y => y.2.2) true + 2 * ε := by
        rw [ENNReal.tsum_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    _ ≤ (2 * ssdhGame G (ssdhReduction G (CPaceH1.matchWrap (dmAdv G B))) true + ε) +
        ∑' td : Pw → Sˣ, PMF.uniformFintype (Pw → Sˣ) td *
          ((OracleAdv.run (OracleAdv.flagWhen (fun s _ x => UQst G td x.2.1.1.1)
            (jointSim G td)) B (jointInit G, false)).map fun y => y.2.2) true + 2 * ε := by
        gcongr
        exact hQ.trans (add_le_add hE le_rfl)
    _ = _ := by ring

end DM

end CatCrypt.Crypto.PAKE.CPaceBadReductions
