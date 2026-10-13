/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.PKE.Games
public import CatCryptCore.Crypto.Constructions.ECBCPRFFlag

/-!
# The T-transform of Hofheinz–Hövelmanns–Kiltz in the random-oracle model

For a public-key encryption scheme `P` with messages `M` and coins `R` and a random
oracle `G : M → R`, `tTransform P = T[P, G]` encrypts deterministically,
`Enc(pk, m; G(m))`, and decrypts `c` to `m = Dec(sk, c)` only when re-encryption
gives `c`. Its OW-PCA game in the random-oracle model (`PKE.Games.romOWPCAGame`)
gives the adversary the public key, the challenge, the random oracle and a
plaintext-checking oracle, all sharing one lazily sampled table.

## Main definitions

* `tTransform` — the transform
* `tReductionC B`, `tReductionD B` — the OW-CPA adversaries against `P` built from
  an OW-PCA adversary `B` against `tTransform P`
* `extDist T`, `keyedRO f` — a uniform function agreeing with a table, and the
  random oracle answered by a function

## Main results

* `run_roOracle_map_fst_eq`, `run_simOracle_roOracle_eq` — lazy and eager sampling
  of the random oracle give the same output distribution
* `tTransform_owpca_of_total` — for every OW-PCA adversary `B` asking at most `n`
  queries in total,
  `romOWPCAAdvantage (tTransform P) B ≤ owcpaAdvantage P (tReductionC P B) +
  (n + 1)·P.corrWorst + P.corrErr + (n + 1)·owcpaAdvantage P (tReductionD P B n)`
* `tTransform_owpca` — the same with `n = qG + qP` for `qG` random-oracle and `qP`
  plaintext-checking queries

## Proof outline

1. The random oracle is sampled eagerly (`game_eq_eager`).
2. Plaintext-checking answers `[Dec(sk, c) = m ∧ Enc(pk, m; G(m)) = c]` are replaced by
   re-encryption `[Enc(pk, m; G(m)) = c]`; the runs agree until a point with
   problematic coins (`Dec(sk, Enc(pk, m; G(m))) ≠ m`) is read (`real_le_sim`).
3. The challenge coins `G(m*)` are replaced by independent coins; the runs agree
   until the oracle is read at `m*` (`challenge_hop`).
4. With independent coins, success without a problematic read means the output
   decrypts the challenge, which is the success of `tReductionC`; problematic reads
   cost `(n + 1)·δ` (`lazy_bad_le`); a read at `m*` is caught by `tReductionD`,
   which guesses a logged point, except when the challenge fails to decrypt
   (`query_le_D`).

## References

* D. Hofheinz, K. Hövelmanns, E. Kiltz, *A Modular Analysis of the
  Fujisaki–Okamoto Transformation*, TCC 2017, ePrint 2017/604, Theorem 3.1.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.PKE.FOTransformT

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.PRPPRF
open CatCrypt.Crypto.PKE.Games
open CatCrypt.Crypto.Constructions.ECBCPRF (uniform_bind_update toOuterMeasure_flag_eq
  toOuterMeasure_le_add_flag toOuterMeasure_eq_of_subset_false toOuterMeasure_add_compl
  run_support_rel)
open scoped ENNReal

/-! ## Lazy and eager random oracles -/

section LazyEager

variable {M R : Type} [Fintype M] [DecidableEq M] [Fintype R] [Nonempty R]

/-- The function `f` completed by the table `T`: `T m` where defined, `f m` elsewhere. -/
def complete (T : M → Option R) (f : M → R) : M → R := fun m => (T m).getD (f m)

/-- A uniform function agreeing with the table `T` where it is defined. -/
noncomputable def extDist (T : M → Option R) : PMF (M → R) :=
  (PMF.uniformOfFintype (M → R)).map (complete T)

/-- The random oracle answered by the function `f`, without state. -/
noncomputable def keyedRO (f : M → R) (_ : Unit) (m : M) : PMF (R × Unit) := PMF.pure (f m, ())

omit [Fintype M] [Fintype R] [Nonempty R] in
theorem complete_update (T : M → Option R) (m : M) (r : R) (g : M → R) (hT : T m = none) :
    complete (Function.update T m (some r)) g = complete T (Function.update g m r) := by
  funext m'
  by_cases h : m' = m
  · subst h; simp [complete, hT]
  · simp [complete, Function.update_of_ne h]

theorem extDist_map_pair (T : M → Option R) (m : M) (hT : T m = none) :
    (extDist T).map (fun f => (f m, f)) =
      (PMF.uniformOfFintype R).bind fun r =>
        (extDist (Function.update T m (some r))).map fun f => (r, f) := by
  classical
  simp only [extDist, PMF.map_comp, Function.comp_def]
  conv_lhs => rw [← uniform_bind_update m]
  rw [PMF.map_bind]
  simp only [PMF.map_comp, Function.comp_def]
  have h : ∀ (g : M → R) (r : R), (complete T (Function.update g m r) m,
      complete T (Function.update g m r)) = (r, complete (Function.update T m (some r)) g) := by
    intro g r
    rw [complete_update T m r g hT]
    simp [complete, hT]
  simp only [h, PMF.map]
  exact PMF.bind_comm _ _ _

/-- **Lazy and eager sampling.** A run against the lazily sampled random oracle from
the table `T` has the output distribution of a run against `keyedRO f` for a
function `f` drawn from `extDist T`. -/
theorem run_roOracle_map_fst_eq {β : Type} (B : OracleAdv M R β) (T : M → Option R) :
    (OracleAdv.run roOracle B T).map Prod.fst =
      (extDist T).bind fun f => (OracleAdv.run (keyedRO f) B ()).map Prod.fst := by
  induction B generalizing T with
  | ret b => simp [PMF.pure_map]
  | rand p k ih =>
    simp only [OracleAdv.run_rand, PMF.map_bind, ih]
    exact PMF.bind_comm _ _ _
  | query m k ih =>
    simp only [OracleAdv.run_query, keyedRO, PMF.pure_bind, PMF.map_bind]
    cases hT : T m with
    | some h =>
      simp only [roOracle, hT, PMF.pure_bind, ih]
      simp only [extDist, PMF.bind_map, Function.comp_def, complete, hT, Option.getD_some]
    | none =>
      simp only [roOracle, hT, PMF.bind_map, Function.comp_def, ih]
      have hp := extDist_map_pair T m hT
      calc _ = (PMF.uniformOfFintype R).bind fun r =>
            ((extDist (Function.update T m (some r))).map fun f => (r, f)).bind fun x =>
              (OracleAdv.run (keyedRO x.2) (k x.1) ()).map Prod.fst := by
            simp only [PMF.bind_map, Function.comp_def]
        _ = ((extDist T).map fun f => (f m, f)).bind fun x =>
              (OracleAdv.run (keyedRO x.2) (k x.1) ()).map Prod.fst := by
            rw [hp, PMF.bind_bind]
        _ = _ := by simp only [PMF.bind_map, Function.comp_def]

/-- Lazy and eager sampling for a simulated adversary: the output and final
simulator state of a run against `simOracle prog roOracle` from the table `T` are
those of a run against `simOracle prog (keyedRO f)` for `f ← extDist T`. -/
theorem run_simOracle_roOracle_eq {D A σ α : Type} (prog : σ → D → OracleAdv M R (A × σ))
    (W : OracleAdv D A α) (s : σ) (T : M → Option R) :
    (OracleAdv.run (OracleAdv.simOracle prog roOracle) W (s, T)).map (fun x => (x.1, x.2.1)) =
      (extDist T).bind fun f =>
        (OracleAdv.run (OracleAdv.simOracle prog (keyedRO f)) W (s, ())).map
          (fun x => (x.1, x.2.1)) := by
  have h₁ := OracleAdv.run_simulate prog roOracle W s T
  have h₂ : ∀ f, OracleAdv.run (keyedRO f) (OracleAdv.simulate prog W s) () =
      _ := fun f => OracleAdv.run_simulate prog (keyedRO f) W s ()
  have e₁ : (OracleAdv.run (OracleAdv.simOracle prog roOracle) W (s, T)).map
      (fun x => (x.1, x.2.1)) =
      (OracleAdv.run roOracle (OracleAdv.simulate prog W s) T).map Prod.fst := by
    rw [h₁, PMF.map_comp]; rfl
  have e₂ : ∀ f, (OracleAdv.run (OracleAdv.simOracle prog (keyedRO f)) W (s, ())).map
      (fun x => (x.1, x.2.1)) =
      (OracleAdv.run (keyedRO f) (OracleAdv.simulate prog W s) ()).map Prod.fst := by
    intro f; rw [h₂, PMF.map_comp]; rfl
  simp only [e₁, e₂]
  exact run_roOracle_map_fst_eq _ T

theorem extDist_empty : extDist (emptyTable : M → Option R) = PMF.uniformOfFintype (M → R) := by
  have : complete (emptyTable : M → Option R) = id := by
    funext g m; simp [complete, emptyTable]
  rw [extDist, this, PMF.map_id]

end LazyEager

/-! ## The transform and the reductions -/

variable {PK SK M C R : Type} [Fintype M] [Nonempty M] [DecidableEq M] [DecidableEq C]
  [Fintype R] [Nonempty R]

/-- The transform `T[P, G]`: encryption `Enc(pk, m; G(m))`; decryption of `c` returns
`m = Dec(sk, c)` when `Enc(pk, m; G(m)) = c` and rejects otherwise. The secret key
includes the public key. -/
noncomputable def tTransform (P : Scheme PK SK M C R) : ROMScheme PK (PK × SK) M C M R where
  keygen := P.keygen.map fun ks => (ks.1, (ks.1, ks.2))
  enc pk m := .query m fun r => .ret (P.enc pk m r)
  dec sk c := match P.dec sk.2 c with
    | none => .ret none
    | some m => .query m fun r => .ret (if P.enc sk.1 m r = c then some m else none)

variable (P : Scheme PK SK M C R)

/-- The simulated oracle of the reductions as a program on the random oracle: a
random-oracle query is forwarded, and a plaintext-checking query `(m, c)` is
answered by re-encryption, `[Enc(pk, m; G(m)) = c]`. The simulator state is the log
of messages at which the random oracle was read, most recent first. -/
noncomputable def progLog (pk : PK) (log : List M) :
    M ⊕ (M × C) → OracleAdv M R ((R ⊕ Bool) × List M)
  | .inl m => .query m fun r => .ret (.inl r, m :: log)
  | .inr q => .query q.1 fun r => .ret (.inr (decide (P.enc pk q.1 r = q.2)), q.1 :: log)

/-- The adversary followed by the challenger's plaintext-checking query on its
output; the result is the output and the answer. -/
def withCheck {qG qP : ℕ} (B : ROMOWPCAAdversary PK M C M R qG qP) (pk : PK) (c : C) :
    OracleAdv (M ⊕ (M × C)) (R ⊕ Bool) (M × Bool) :=
  (B.run pk c).bind fun m' => .query (.inr (m', c)) fun a => .ret (m', a.elim (fun _ => false) id)

/-- The OW-CPA adversary that runs `B` once on `(pk, c*)`, answering random-oracle
queries with a lazily sampled table and plaintext-checking queries `(m, c)` with
`[Enc(pk, m; G(m)) = c]`, and outputs the message output by `B`. -/
noncomputable def tReductionC {qG qP : ℕ} (B : ROMOWPCAAdversary PK M C M R qG qP) :
    PK → C → PMF M := fun pk c =>
  (OracleAdv.run (OracleAdv.simOracle (progLog P pk) roOracle) (B.run pk c) ([], emptyTable)).map
    Prod.fst

/-- The OW-CPA adversary that runs `B` once on `(pk, c*)` as `tReductionC` does,
followed by the check of its output, and outputs the entry at a uniform index below
`n + 1` of the log of messages at which the random oracle was read (the output of
`B` when the index is beyond the log). -/
noncomputable def tReductionD {qG qP : ℕ} (B : ROMOWPCAAdversary PK M C M R qG qP) (n : ℕ) :
    PK → C → PMF M := fun pk c =>
  (OracleAdv.run (OracleAdv.simOracle (progLog P pk) roOracle) (withCheck B pk c)
    ([], emptyTable)).bind fun x =>
      (PMF.uniformOfFintype (Fin (n + 1))).map fun i => x.2.1.getD i x.1.1

/-! ## The experiment as a run against the random oracle -/

section Unfold

/-- The oracle of the OW-PCA experiment of `tTransform P` as a program on the random
oracle: a random-oracle query is forwarded, a plaintext-checking query runs the
decryption program of `tTransform P`. -/
noncomputable def progReal (ks : PK × SK) (u : Unit) :
    M ⊕ (M × C) → OracleAdv M R ((R ⊕ Bool) × Unit)
  | .inl m => .query m fun r => .ret (.inl r, u)
  | .inr q => ((tTransform P).dec (ks.1, ks.2) q.2).bind fun z => .ret (.inr (decide (z = some q.1)), u)

/-- The OW-PCA experiment of `tTransform P` for the key pair `ks` and the challenge
message `m`, as an adversary on the combined oracle: the challenger's random-oracle
query at `m`, then the adversary on the challenge, then the check of its output. -/
def fullRun {qG qP : ℕ} (B : ROMOWPCAAdversary PK M C M R qG qP) (pk : PK) (m : M) :
    OracleAdv (M ⊕ (M × C)) (R ⊕ Bool) (M × Bool) :=
  .query (.inl m) fun a => a.elim (fun r => withCheck B pk (P.enc pk m r)) fun _ => .ret (m, false)

omit [Fintype M] [Nonempty M] in
theorem romPcaOracle_eq (ks : PK × SK) (T : M → Option R) (d : M ⊕ (M × C)) :
    ((OracleAdv.simOracle (progReal P ks) roOracle) ((), T) d).map (Prod.map id Prod.snd) =
      romPcaOracle (tTransform P) (ks.1, ks.2) T d := by
  cases d with
  | inl m =>
    simp only [OracleAdv.simOracle, progReal, romPcaOracle, OracleAdv.run_query, OracleAdv.run_ret,
      PMF.map_bind, PMF.pure_map]
    rfl
  | inr q =>
    simp only [OracleAdv.simOracle, progReal, romPcaOracle, OracleAdv.run_bind, OracleAdv.run_ret,
      PMF.map_bind, PMF.pure_map]
    rfl

theorem romOWPCAGame_eq {qG qP : ℕ} (B : ROMOWPCAAdversary PK M C M R qG qP) :
    romOWPCAGame (tTransform P) B = P.keygen.bind fun ks => (PMF.uniformOfFintype M).bind fun m =>
      (OracleAdv.run (OracleAdv.simOracle (progReal P ks) roOracle) (fullRun P B ks.1 m)
        ((), emptyTable)).map fun x => x.1.2 := by
  have hB : ∀ (ks : PK × SK) (c : C) (T : M → Option R),
      OracleAdv.run (romPcaOracle (tTransform P) (ks.1, ks.2)) (B.run ks.1 c) T =
        (OracleAdv.run (OracleAdv.simOracle (progReal P ks) roOracle) (B.run ks.1 c) ((), T)).map
          (Prod.map id Prod.snd) := fun ks c T =>
    (OracleAdv.run_map_state _ _ Prod.snd (fun s d => romPcaOracle_eq P ks s.2 d) _ ((), T)).symm
  rw [romOWPCAGame, show (tTransform P).keygen = P.keygen.map fun ks => (ks.1, (ks.1, ks.2)) from rfl,
    PMF.bind_map]
  refine congrArg _ (funext fun ks => congrArg _ (funext fun m => ?_))
  simp only [hB, show ∀ pk m', (tTransform P).enc pk m' =
    .query m' fun r => .ret (P.enc pk m' r) from fun _ _ => rfl]
  simp only [fullRun, withCheck, OracleAdv.run_query, OracleAdv.run_ret, OracleAdv.run_bind,
    OracleAdv.simOracle, progReal, PMF.bind_bind, PMF.map_bind, PMF.pure_bind, PMF.bind_map,
    Function.comp_def, Sum.elim_inl, PMF.pure_map, Sum.elim_inr, id]
  rfl

end Unfold

/-! ## Eager oracles -/

section Eager

omit [Fintype M] [Nonempty M] [DecidableEq M] [DecidableEq C] [Fintype R] [Nonempty R] in
/-- **Identical until bad, on events.** For distributions that agree on every
outcome with the flag cleared, the probability of an event under the first is at
most its probability under the second plus the flag probability. -/
theorem toOuterMeasure_le_add_flag_set {α σ : Type} (p₁ p₂ : PMF (α × (σ × Bool)))
    (h : ∀ a t, p₁ (a, (t, false)) = p₂ (a, (t, false))) (S : Set (α × (σ × Bool))) :
    p₁.toOuterMeasure S ≤ p₂.toOuterMeasure S + p₂.toOuterMeasure {x | x.2.2 = true} := by
  refine (MeasureTheory.measure_le_inter_add_sdiff p₁.toOuterMeasure S
    {x | x.2.2 = false}).trans (add_le_add ?_ ?_)
  · rw [toOuterMeasure_eq_of_subset_false p₁ p₂ h _ fun x hx => hx.2]
    exact MeasureTheory.measure_mono Set.inter_subset_left
  · rw [← toOuterMeasure_flag_eq p₁ p₂ h]
    refine MeasureTheory.measure_mono fun x hx => ?_
    simpa using hx.2

omit [Fintype M] [Nonempty M] [DecidableEq M] [DecidableEq C] [Fintype R] [Nonempty R] in
/-- For distributions that agree on every outcome with the flag cleared, an event of
the first is at most the event or the flag under the second. -/
theorem toOuterMeasure_le_or_flag {α σ : Type} (p₁ p₂ : PMF (α × (σ × Bool)))
    (h : ∀ a t, p₁ (a, (t, false)) = p₂ (a, (t, false))) (S : Set (α × (σ × Bool))) :
    p₁.toOuterMeasure S ≤ p₂.toOuterMeasure {x | x ∈ S ∨ x.2.2 = true} := by
  simp only [PMF.toOuterMeasure_apply]
  have hsplit : ∀ (p : PMF (α × (σ × Bool))) (U : Set (α × (σ × Bool))),
      ∑' x, U.indicator p x = ∑' x, {x | x ∈ U ∧ x.2.2 = false}.indicator p x +
        ∑' x, {x | x ∈ U ∧ x.2.2 = true}.indicator p x := by
    intro p U
    rw [← ENNReal.tsum_add]
    refine tsum_congr fun x => ?_
    obtain ⟨a, t, b⟩ := x
    cases b <;> by_cases hx : (a, t, false) ∈ U <;> by_cases hx' : (a, t, true) ∈ U <;>
      simp [Set.indicator, hx, hx']
  rw [hsplit p₁ S, hsplit p₂ {x | x ∈ S ∨ x.2.2 = true}]
  refine add_le_add ?_ ?_
  · refine le_of_eq (tsum_congr fun x => ?_)
    obtain ⟨a, t, b⟩ := x
    cases b
    · by_cases hx : (a, t, false) ∈ S <;> simp [Set.indicator, h, hx]
    · simp [Set.indicator]
  · calc ∑' x, {x | x ∈ S ∧ x.2.2 = true}.indicator p₁ x
        ≤ p₁.toOuterMeasure {x | x.2.2 = true} := by
          rw [PMF.toOuterMeasure_apply]
          exact ENNReal.tsum_le_tsum fun x =>
            Set.indicator_le_indicator_of_subset (fun x hx => hx.2) (fun _ => bot_le) x
      _ = p₂.toOuterMeasure {x | x.2.2 = true} := toOuterMeasure_flag_eq p₁ p₂ h
      _ = _ := by
          rw [PMF.toOuterMeasure_apply]
          refine tsum_congr fun x => ?_
          obtain ⟨a, t, b⟩ := x
          cases b <;> simp [Set.indicator]

/-- The eager oracle for the function `f` with ghost state: a random-oracle query
`m` returns `f m`, a plaintext-checking query `q` returns `ans q (f q.1)`, and each
query updates the ghost state with `upd` at the point read and its value. -/
noncomputable def eO {G : Type} (ans : M × C → R → Bool) (upd : M → R → G → G) (f : M → R)
    (g : G) : M ⊕ (M × C) → PMF ((R ⊕ Bool) × G)
  | .inl m => PMF.pure (.inl (f m), upd m (f m) g)
  | .inr q => PMF.pure (.inr (ans q (f q.1)), upd q.1 (f q.1) g)

/-- The plaintext-checking answer of the experiment. -/
def ansReal (ks : PK × SK) (q : M × C) (r : R) : Bool :=
  decide (P.dec ks.2 q.2 = some q.1 ∧ P.enc ks.1 q.1 r = q.2)

/-- The plaintext-checking answer by re-encryption. -/
def ansSim (pk : PK) (q : M × C) (r : R) : Bool := decide (P.enc pk q.1 r = q.2)

/-- The coins `r` are problematic for `m`: encrypting `m` with them does not decrypt to `m`. -/
def prob (ks : PK × SK) (m : M) (r : R) : Bool := decide (P.dec ks.2 (P.enc ks.1 m r) ≠ some m)

/-- The ghost update recording a problematic read and a read at `m*`. -/
def ghostUpd (ks : PK × SK) (mstar : M) (m : M) (r : R) (g : Bool × Bool) : Bool × Bool :=
  (g.1 || prob P ks m r, g.2 || decide (m = mstar))

omit [Fintype M] [Nonempty M] [Fintype R] [Nonempty R] in
theorem simOracle_progReal_keyed (ks : PK × SK) (f : M → R) (s : Unit × Unit)
    (d : M ⊕ (M × C)) :
    (OracleAdv.simOracle (progReal P ks) (keyedRO f) s d).map (Prod.map id fun _ => ()) =
      eO (ansReal P ks) (fun _ _ u => u) f () d := by
  cases d with
  | inl m => simp [OracleAdv.simOracle, progReal, keyedRO, eO, PMF.pure_map]
  | inr q =>
    obtain ⟨m, c⟩ := q
    simp only [OracleAdv.simOracle, progReal, tTransform, OracleAdv.run_bind, eO, ansReal]
    cases hd : P.dec ks.2 c with
    | none => simp [PMF.pure_map]
    | some m₀ =>
      simp only [OracleAdv.run_query, OracleAdv.run_ret, keyedRO, PMF.pure_bind, PMF.pure_map]
      by_cases hm : m₀ = m
      · subst hm; by_cases he : P.enc ks.1 m₀ (f m₀) = c <;> simp [he]
      · by_cases he : P.enc ks.1 m₀ (f m₀) = c <;> simp [he, hm]

omit [Nonempty M] in
/-- The experiment with the random oracle sampled eagerly. -/
theorem game_eq_eager {qG qP : ℕ} (B : ROMOWPCAAdversary PK M C M R qG qP) (ks : PK × SK)
    (m : M) :
    (OracleAdv.run (OracleAdv.simOracle (progReal P ks) roOracle) (fullRun P B ks.1 m)
        ((), emptyTable)).map (fun x => x.1.2) =
      (PMF.uniformOfFintype (M → R)).bind fun f =>
        (OracleAdv.run (eO (ansReal P ks) (fun _ _ u => u) f) (withCheck B ks.1 (P.enc ks.1 m (f m)))
          ()).map fun x => x.1.2 := by
  have h := run_simOracle_roOracle_eq (progReal P ks) (fullRun P B ks.1 m) () emptyTable
  rw [show (fun x : (M × Bool) × (Unit × (M → Option R)) => x.1.2) =
    (fun y : (M × Bool) × Unit => y.1.2) ∘ (fun x => (x.1, x.2.1)) from rfl, ← PMF.map_comp, h,
    extDist_empty, PMF.map_bind]
  refine congrArg _ (funext fun f => ?_)
  have h₂ := OracleAdv.run_map_state _ _ (fun _ => ()) (fun s d => simOracle_progReal_keyed P ks f s d)
    (fullRun P B ks.1 m) ((), ())
  rw [PMF.map_comp]
  rw [show ((fun y : (M × Bool) × Unit => y.1.2) ∘ fun x : (M × Bool) × (Unit × Unit) =>
    (x.1, x.2.1)) = (fun y : (M × Bool) × Unit => y.1.2) ∘ Prod.map id (fun _ => ()) from rfl,
    ← PMF.map_comp, h₂]
  simp [fullRun, eO, PMF.pure_bind]

/-- The ghost update recording a problematic read, with a trivial ghost component. -/
def badUpd (ks : PK × SK) (m : M) (r : R) (g : Unit × Bool) : Unit × Bool :=
  ((), g.2 || prob P ks m r)

omit [Fintype M] [Nonempty M] [DecidableEq C] [Fintype R] [Nonempty R] in
theorem eO_badUpd_true_false {ans : M × C → R → Bool} (ks : PK × SK) (f : M → R) (u : Unit)
    (d : M ⊕ (M × C)) (a : R ⊕ Bool) (u' : Unit) :
    eO ans (badUpd P ks) f (u, true) d (a, (u', false)) = 0 := by
  cases d <;> simp [eO, badUpd, PMF.pure_apply]

omit [Fintype M] [Nonempty M] [Fintype R] [Nonempty R] in
theorem eO_badUpd_false_eq (ks : PK × SK) (f : M → R) (s : Unit × Bool) (d : M ⊕ (M × C))
    (a : R ⊕ Bool) (u' : Unit) :
    eO (ansReal P ks) (badUpd P ks) f s d (a, (u', false)) =
      eO (ansSim P ks.1) (badUpd P ks) f s d (a, (u', false)) := by
  cases d with
  | inl m => rfl
  | inr q =>
    simp only [eO, PMF.pure_apply, badUpd, Prod.mk.injEq]
    by_cases hp : prob P ks q.1 (f q.1) = true
    · simp [hp]
    · have hp' : P.dec ks.2 (P.enc ks.1 q.1 (f q.1)) = some q.1 := by
        simpa [prob] using hp
      have hans : ansReal P ks q (f q.1) = ansSim P ks.1 q (f q.1) := by
        simp only [ansReal, ansSim]
        by_cases he : P.enc ks.1 q.1 (f q.1) = q.2
        · rw [he] at hp'; simp [he, hp']
        · simp [he]
      rw [hans]

omit [Fintype M] [Nonempty M] [Fintype R] [Nonempty R] in
/-- **Re-encryption hop.** For a fixed function `f`, the experiment's success
probability is at most the probability that the run with plaintext-checking queries
answered by re-encryption succeeds or reads a problematic point. -/
theorem real_le_sim {qG qP : ℕ} (B : ROMOWPCAAdversary PK M C M R qG qP) (ks : PK × SK)
    (mstar : M) (f : M → R) (c : C) :
    ((OracleAdv.run (eO (ansReal P ks) (fun _ _ u => u) f) (withCheck B ks.1 c) ()).map
      fun x => x.1.2).toOuterMeasure {b | b = true} ≤
    (OracleAdv.run (eO (ansSim P ks.1) (ghostUpd P ks mstar) f) (withCheck B ks.1 c)
      (false, false)).toOuterMeasure {x | x.1.2 = true ∨ x.2.1 = true} := by
  have e₁ := OracleAdv.run_map_state (eO (ansReal P ks) (badUpd P ks) f)
    (eO (ansReal P ks) (fun _ _ u => u) f) (fun _ => ())
    (fun s d => by cases d <;> simp [eO, PMF.pure_map]) (withCheck B ks.1 c) ((), false)
  have e₂ := OracleAdv.run_map_state (eO (ansSim P ks.1) (ghostUpd P ks mstar) f)
    (eO (ansSim P ks.1) (badUpd P ks) f) (fun g => ((), g.1))
    (fun s d => by cases d <;> simp [eO, PMF.pure_map, ghostUpd, badUpd]) (withCheck B ks.1 c)
    (false, false)
  rw [← e₁, PMF.map_comp, PMF.toOuterMeasure_map_apply]
  have hle := toOuterMeasure_le_or_flag
    (OracleAdv.run (eO (ansReal P ks) (badUpd P ks) f) (withCheck B ks.1 c) ((), false))
    (OracleAdv.run (eO (ansSim P ks.1) (badUpd P ks) f) (withCheck B ks.1 c) ((), false))
    (fun a t => OracleAdv.run_apply_flag_false_eq _ _ (eO_badUpd_true_false P ks f)
      (eO_badUpd_true_false P ks f) (fun s d r t' => eO_badUpd_false_eq P ks f s d r t') _ _ a t)
    {x | x.1.2 = true}
  refine (le_of_eq_of_le ?_ hle).trans (le_of_eq ?_)
  · rfl
  · rw [show ((), false) = (fun g : Bool × Bool => ((), g.1)) (false, false) from rfl, ← e₂,
      PMF.toOuterMeasure_map_apply]
    rfl

omit [Fintype M] [Nonempty M] [Fintype R] [Nonempty R] in
theorem eO_ghost_true_false (ks : PK × SK) (mstar : M) (f : M → R) (b : Bool)
    (d : M ⊕ (M × C)) (a : R ⊕ Bool) (b' : Bool) :
    eO (ansSim P ks.1) (ghostUpd P ks mstar) f (b, true) d (a, (b', false)) = 0 := by
  cases d <;> simp [eO, ghostUpd, PMF.pure_apply]

omit [Fintype M] [Nonempty M] [Fintype R] [Nonempty R] in
theorem eO_ghost_update_false_eq (ks : PK × SK) (mstar : M) (f : M → R) (r : R)
    (s : Bool × Bool) (d : M ⊕ (M × C)) (a : R ⊕ Bool) (b' : Bool) :
    eO (ansSim P ks.1) (ghostUpd P ks mstar) (Function.update f mstar r) s d (a, (b', false)) =
      eO (ansSim P ks.1) (ghostUpd P ks mstar) f s d (a, (b', false)) := by
  cases d with
  | inl m =>
    by_cases hm : m = mstar
    · subst hm; simp [eO, ghostUpd, PMF.pure_apply]
    · simp [eO, Function.update_of_ne hm]
  | inr q =>
    by_cases hm : q.1 = mstar
    · simp [eO, ghostUpd, PMF.pure_apply, hm]
    · simp [eO, Function.update_of_ne hm]

omit [Nonempty M] in
/-- **Challenge-point hop.** Averaged over `f`, the event of the run on the challenge
`Enc(pk, m*; f(m*))` has probability at most that of the run on `Enc(pk, m*; r)` for
independent uniform `r`, plus the probability that the latter reads the random
oracle at `m*`. -/
theorem challenge_hop {qG qP : ℕ} (B : ROMOWPCAAdversary PK M C M R qG qP) (ks : PK × SK)
    (mstar : M) (S : Set ((M × Bool) × (Bool × Bool))) :
    ∑' f, PMF.uniformOfFintype (M → R) f *
      (OracleAdv.run (eO (ansSim P ks.1) (ghostUpd P ks mstar) f)
        (withCheck B ks.1 (P.enc ks.1 mstar (f mstar))) (false, false)).toOuterMeasure S ≤
    ∑' f, PMF.uniformOfFintype (M → R) f * ∑' r, PMF.uniformOfFintype R r *
      ((OracleAdv.run (eO (ansSim P ks.1) (ghostUpd P ks mstar) f)
        (withCheck B ks.1 (P.enc ks.1 mstar r)) (false, false)).toOuterMeasure S +
      (OracleAdv.run (eO (ansSim P ks.1) (ghostUpd P ks mstar) f)
        (withCheck B ks.1 (P.enc ks.1 mstar r)) (false, false)).toOuterMeasure
          {x | x.2.2 = true}) := by
  classical
  set F : (M → R) → ℝ≥0∞ := fun f =>
    (OracleAdv.run (eO (ansSim P ks.1) (ghostUpd P ks mstar) f)
      (withCheck B ks.1 (P.enc ks.1 mstar (f mstar))) (false, false)).toOuterMeasure S
  have hu : ∑' f, PMF.uniformOfFintype (M → R) f * F f =
      ∑' f, PMF.uniformOfFintype (M → R) f * ∑' r, PMF.uniformOfFintype R r *
        F (Function.update f mstar r) := by
    have h := uniform_bind_update (D := M) (R := R) mstar
    conv_lhs => rw [← h]
    simp only [PMF.bind_apply, PMF.map_apply, ← ENNReal.tsum_mul_right, ← ENNReal.tsum_mul_left]
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun f => ?_
    rw [ENNReal.tsum_comm]
    refine tsum_congr fun r => ?_
    rw [tsum_eq_single (Function.update f mstar r)]
    · simp only [if_true]; ring
    · intro g hg; simp [hg]
  rw [hu]
  refine ENNReal.tsum_le_tsum fun f => mul_le_mul_right (ENNReal.tsum_le_tsum fun r =>
    mul_le_mul_right ?_ _) _
  simp only [F, Function.update_self]
  exact toOuterMeasure_le_add_flag_set _ _
    (fun a t => OracleAdv.run_apply_flag_false_eq _ _ (eO_ghost_true_false P ks mstar _)
      (eO_ghost_true_false P ks mstar _)
      (fun s d x b' => eO_ghost_update_false_eq P ks mstar f r s d x b') _ _ a t) S

omit [Fintype M] [Nonempty M] [Fintype R] [Nonempty R] in
/-- On every outcome of the run with re-encryption answers whose check succeeds and
which reads no problematic point, the output decrypts the challenge. -/
theorem dec_of_mem_support {qG qP : ℕ} (B : ROMOWPCAAdversary PK M C M R qG qP)
    (ks : PK × SK) (mstar : M) (f : M → R) (c : C) (g : Bool × Bool)
    (y : (M × Bool) × (Bool × Bool))
    (hy : y ∈ (OracleAdv.run (eO (ansSim P ks.1) (ghostUpd P ks mstar) f)
      (withCheck B ks.1 c) g).support) (h₁ : y.1.2 = true) (h₂ : y.2.1 = false) :
    P.dec ks.2 c = some y.1.1 := by
  simp only [withCheck, OracleAdv.run_bind, PMF.mem_support_bind_iff, OracleAdv.run_query,
    OracleAdv.run_ret, eO, PMF.pure_bind, PMF.support_pure, Set.mem_singleton_iff] at hy
  obtain ⟨x, -, rfl⟩ := hy
  simp only [Sum.elim_inr, id, ansSim, ghostUpd, Bool.or_eq_false_iff, decide_eq_true_eq] at h₁ h₂
  have hp : P.dec ks.2 (P.enc ks.1 x.1 (f x.1)) = some x.1 := by simpa [prob] using h₂.2
  rw [← h₁]; exact hp

omit [Fintype M] [Nonempty M] [Fintype R] [Nonempty R] in
/-- The success-or-problematic event is at most decryption of the challenge to the
output plus a problematic read. -/
theorem event_le {qG qP : ℕ} (B : ROMOWPCAAdversary PK M C M R qG qP)
    (ks : PK × SK) (mstar : M) (f : M → R) (c : C) :
    (OracleAdv.run (eO (ansSim P ks.1) (ghostUpd P ks mstar) f) (withCheck B ks.1 c)
      (false, false)).toOuterMeasure {x | x.1.2 = true ∨ x.2.1 = true} ≤
    (OracleAdv.run (eO (ansSim P ks.1) (ghostUpd P ks mstar) f) (withCheck B ks.1 c)
      (false, false)).toOuterMeasure {x | P.dec ks.2 c = some x.1.1} +
    (OracleAdv.run (eO (ansSim P ks.1) (ghostUpd P ks mstar) f) (withCheck B ks.1 c)
      (false, false)).toOuterMeasure {x | x.2.1 = true} := by
  refine (PMF.toOuterMeasure_mono _ ?_).trans (MeasureTheory.measure_union_le _ _)
  rintro y ⟨hy, hs⟩
  by_cases hb : y.2.1 = true
  · exact Or.inr hb
  · rcases hy with h | h
    · exact Or.inl (dec_of_mem_support P B ks mstar f c _ y hs h (by simpa using hb))
    · exact absurd h hb

end Eager

/-! ## Back to lazy sampling -/

section Lazy

omit [Fintype M] [Nonempty M] [DecidableEq M] [DecidableEq C] [Fintype R] [Nonempty R] in
theorem run_eO_forget {G G' α : Type} (ans : M × C → R → Bool) (upd : M → R → G → G)
    (upd' : M → R → G' → G') (φ : G → G') (hφ : ∀ m r g, φ (upd m r g) = upd' m r (φ g))
    (f : M → R) (A : OracleAdv (M ⊕ (M × C)) (R ⊕ Bool) α) (g : G) :
    (OracleAdv.run (eO ans upd f) A g).map (Prod.map id φ) = OracleAdv.run (eO ans upd' f) A (φ g) :=
  OracleAdv.run_map_state _ _ φ (fun s d => by cases d <;> simp [eO, PMF.pure_map, hφ]) A g

omit [Fintype M] [Nonempty M] [DecidableEq M] [Fintype R] [Nonempty R] in
/-- The eager form of the simulation program `progLog`. -/
theorem simOracle_progLog_keyed (pk : PK) (f : M → R) (s : List M × Unit) (d : M ⊕ (M × C)) :
    (OracleAdv.simOracle (progLog P pk) (keyedRO f) s d).map (Prod.map id Prod.fst) =
      eO (ansSim P pk) (fun m _ l => m :: l) f s.1 d := by
  cases d <;> simp [OracleAdv.simOracle, progLog, keyedRO, eO, ansSim, PMF.pure_map]

omit [Nonempty M] in
/-- A lazily simulated run has the output and final log of the eager runs averaged
over a uniform function. -/
theorem lazy_log_eq {α : Type} (pk : PK) (A : OracleAdv (M ⊕ (M × C)) (R ⊕ Bool) α) :
    (OracleAdv.run (OracleAdv.simOracle (progLog P pk) roOracle) A ([], emptyTable)).map
      (fun x => (x.1, x.2.1)) =
    (PMF.uniformOfFintype (M → R)).bind fun f =>
      OracleAdv.run (eO (ansSim P pk) (fun m _ l => m :: l) f) A [] := by
  rw [run_simOracle_roOracle_eq, extDist_empty]
  refine congrArg _ (funext fun f => ?_)
  have h := OracleAdv.run_map_state _ _ Prod.fst (fun s d => simOracle_progLog_keyed P pk f s d) A
    ([], ())
  rw [← h]
  rfl

omit [Nonempty M] in
theorem tReductionC_eq {qG qP : ℕ} (B : ROMOWPCAAdversary PK M C M R qG qP) (pk : PK) (c : C) :
    tReductionC P B pk c = (PMF.uniformOfFintype (M → R)).bind fun f =>
      (OracleAdv.run (eO (ansSim P pk) (fun _ _ u => u) f) (B.run pk c) ()).map Prod.fst := by
  unfold tReductionC
  rw [show (Prod.fst : M × (List M × (M → Option R)) → M) =
    Prod.fst ∘ (fun x => (x.1, x.2.1)) from rfl, ← PMF.map_comp, lazy_log_eq, PMF.map_bind]
  refine congrArg _ (funext fun f => ?_)
  rw [← run_eO_forget (ansSim P pk) (fun m _ l => m :: l) (fun _ _ u => u) (fun _ => ())
    (fun _ _ _ => rfl), PMF.map_comp]
  rfl

omit [Fintype M] [Nonempty M] [Fintype R] [Nonempty R] in
theorem ghost_map_output {qG qP : ℕ} (B : ROMOWPCAAdversary PK M C M R qG qP) (ks : PK × SK)
    (mstar : M) (f : M → R) (c : C) :
    (OracleAdv.run (eO (ansSim P ks.1) (ghostUpd P ks mstar) f) (withCheck B ks.1 c)
      (false, false)).map (fun x => x.1.1) =
    (OracleAdv.run (eO (ansSim P ks.1) (fun _ _ u => u) f) (B.run ks.1 c) ()).map Prod.fst := by
  rw [← run_eO_forget (ansSim P ks.1) (ghostUpd P ks mstar) (fun _ _ u => u) (fun _ => ())
    (fun _ _ _ => rfl) f (B.run ks.1 c), PMF.map_comp]
  simp only [withCheck, OracleAdv.run_bind, OracleAdv.run_query, OracleAdv.run_ret, eO,
    PMF.pure_bind, PMF.map_bind, PMF.pure_map]
  rfl

/-- The eager oracle with only the problematic-read flag. -/
def badOnly (ks : PK × SK) (m : M) (r : R) (b : Bool) : Bool := b || prob P ks m r

/-- The lazy program with the problematic-read flag. -/
noncomputable def progBad (ks : PK × SK) (b : Bool) :
    M ⊕ (M × C) → OracleAdv M R ((R ⊕ Bool) × Bool)
  | .inl m => .query m fun r => .ret (.inl r, badOnly P ks m r b)
  | .inr q => .query q.1 fun r => .ret (.inr (ansSim P ks.1 q r), badOnly P ks q.1 r b)

omit [Fintype M] [Nonempty M] [Fintype R] [Nonempty R] in
theorem simOracle_progBad_keyed (ks : PK × SK) (f : M → R) (s : Bool × Unit)
    (d : M ⊕ (M × C)) :
    (OracleAdv.simOracle (progBad P ks) (keyedRO f) s d).map (Prod.map id Prod.fst) =
      eO (ansSim P ks.1) (badOnly P ks) f s.1 d := by
  cases d <;> simp [OracleAdv.simOracle, progBad, keyedRO, eO, PMF.pure_map]

/-- The table holds only coins that are not problematic. -/
def GoodTable (ks : PK × SK) (T : M → Option R) : Prop := ∀ m r, T m = some r → prob P ks m r = false

/-- The largest decryption-failure probability over messages for the key pair. -/
noncomputable def worst (ks : PK × SK) : ℝ≥0∞ := ⨆ m, P.failProb ks.1 ks.2 m

omit [Fintype M] [Nonempty M] in
/-- **Problematic reads.** From a table holding no problematic coins, a lazily
sampled run with at most `n` queries reads problematic coins with probability at
most `n` times the largest failure probability. -/
theorem lazy_bad_le {α : Type} (ks : PK × SK) (A : OracleAdv (M ⊕ (M × C)) (R ⊕ Bool) α) (n : ℕ)
    (hA : A.IsQueryBoundBy (fun _ => 1) n) (T : M → Option R) (hT : GoodTable P ks T) :
    (OracleAdv.run (OracleAdv.simOracle (progBad P ks) roOracle) A (false, T)).toOuterMeasure
      {x | x.2.1 = true} ≤ n * worst P ks := by
  induction A generalizing n T with
  | ret a => simp [PMF.toOuterMeasure_pure_apply]
  | rand p k ih =>
    rw [OracleAdv.run_rand, PMF.toOuterMeasure_bind_apply]
    calc _ ≤ ∑' b, p b * (n * worst P ks) := ENNReal.tsum_le_tsum fun b =>
          mul_le_mul_right (ih b n (hA b) T hT) _
      _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  | query d k ih =>
    obtain ⟨hle, hk⟩ := hA
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by simp only at hle; omega⟩
    simp only [Nat.add_sub_cancel] at hk
    set pt : M := d.elim id Prod.fst
    set ans : R → R ⊕ Bool := fun r => d.elim (fun _ => .inl r) (fun q => .inr (ansSim P ks.1 q r))
    have hstep : OracleAdv.simOracle (progBad P ks) roOracle (false, T) d =
        (roOracle T pt).map fun x => (ans x.1, (badOnly P ks pt x.1 false, x.2)) := by
      cases d <;> simp only [OracleAdv.simOracle, progBad, OracleAdv.run_query, OracleAdv.run_ret,
        PMF.map_bind, PMF.pure_map] <;> rfl
    rw [OracleAdv.run_query, hstep, PMF.bind_map]
    cases hTp : T pt with
    | some r =>
      have hr : badOnly P ks pt r false = false := by simp [badOnly, hT pt r hTp]
      have hro : roOracle T pt = PMF.pure (r, T) := by simp [roOracle, hTp]
      rw [hro, PMF.pure_bind]
      simp only [Function.comp_apply, hr]
      refine (ih _ n' (hk _) T hT).trans ?_
      gcongr; simp
    | none =>
      have hro : roOracle T pt =
          (PMF.uniformOfFintype R).map fun r => (r, Function.update T pt (some r)) := by
        simp [roOracle, hTp]
      rw [hro, PMF.bind_map, PMF.toOuterMeasure_bind_apply]
      have hterm : ∀ r, (OracleAdv.run (OracleAdv.simOracle (progBad P ks) roOracle) (k (ans r))
          (badOnly P ks pt r false, Function.update T pt (some r))).toOuterMeasure
            {x | x.2.1 = true} ≤
          (if prob P ks pt r = true then 1 else 0) + n' * worst P ks := by
        intro r
        by_cases hp : prob P ks pt r = true
        · simp only [hp, if_true]
          exact (le_self_add.trans_eq (toOuterMeasure_add_compl _ _)).trans le_self_add
        · have hb : badOnly P ks pt r false = false := by simp [badOnly, hp]
          simp only [hp, hb, Bool.false_eq_true, if_false, zero_add]
          refine ih _ n' (hk _) _ fun m' r' h' => ?_
          by_cases hm : m' = pt
          · subst hm; simp at h'; subst h'; simpa using hp
          · rw [Function.update_of_ne hm] at h'; exact hT m' r' h'
      calc ∑' r, PMF.uniformOfFintype R r * _
          ≤ ∑' r, PMF.uniformOfFintype R r *
              ((if prob P ks pt r = true then 1 else 0) + n' * worst P ks) :=
            ENNReal.tsum_le_tsum fun r => mul_le_mul_right (hterm r) _
        _ = P.failProb ks.1 ks.2 pt + n' * worst P ks := by
            simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
            congr 1
            rw [Scheme.failProb, PMF.toOuterMeasure_apply]
            refine tsum_congr fun r => ?_
            by_cases hp : prob P ks pt r = true
            · have : P.dec ks.2 (P.enc ks.1 pt r) ≠ some pt := by simpa [prob] using hp
              simp [hp, Set.indicator, this]
            · have : P.dec ks.2 (P.enc ks.1 pt r) = some pt := by simpa [prob] using hp
              simp [hp, Set.indicator, this]
        _ ≤ worst P ks + n' * worst P ks := by gcongr; exact le_iSup (P.failProb ks.1 ks.2) pt
        _ = _ := by push_cast; ring

omit [Fintype M] [Nonempty M] [DecidableEq M] [DecidableEq C] [Fintype R] [Nonempty R] in
theorem isQueryBoundBy_total {qG qP : ℕ} (B : ROMOWPCAAdversary PK M C M R qG qP) (pk : PK)
    (c : C) : (B.run pk c).IsQueryBoundBy (fun _ => 1) (qG + qP) := by
  have h := (B.isQueryBoundG pk c).add (B.isQueryBoundP pk c)
  have hc : (fun d : M ⊕ (M × C) => Sum.elim (fun _ => 1) (fun _ => 0) d +
      Sum.elim (fun _ => 0) (fun _ => 1) d) = fun _ => 1 := by
    funext d; cases d <;> rfl
  rwa [hc] at h

omit [Fintype M] [Nonempty M] [DecidableEq M] [DecidableEq C] [Fintype R] [Nonempty R] in
theorem isQueryBoundBy_withCheck {qG qP : ℕ} (B : ROMOWPCAAdversary PK M C M R qG qP) (n : ℕ)
    (hB : ∀ pk c, (B.run pk c).IsQueryBoundBy (fun _ => 1) n) (pk : PK) (c : C) :
    (withCheck B pk c).IsQueryBoundBy (fun _ => 1) (n + 1) :=
  OracleAdv.isQueryBoundBy_bind (hB pk c) fun _ => ⟨le_rfl, fun _ => trivial⟩

omit [Nonempty M] in
/-- The problematic-read probability, averaged over a uniform function, is the
problematic-read probability of the lazily sampled run. -/
theorem eager_bad_eq {qG qP : ℕ} (B : ROMOWPCAAdversary PK M C M R qG qP) (ks : PK × SK)
    (mstar : M) (c : C) :
    ∑' f, PMF.uniformOfFintype (M → R) f *
      (OracleAdv.run (eO (ansSim P ks.1) (ghostUpd P ks mstar) f) (withCheck B ks.1 c)
        (false, false)).toOuterMeasure {x | x.2.1 = true} =
    (OracleAdv.run (OracleAdv.simOracle (progBad P ks) roOracle) (withCheck B ks.1 c)
      (false, emptyTable)).toOuterMeasure {x | x.2.1 = true} := by
  have h := run_simOracle_roOracle_eq (progBad P ks) (withCheck B ks.1 c) false emptyTable
  rw [extDist_empty] at h
  have e : (OracleAdv.run (OracleAdv.simOracle (progBad P ks) roOracle) (withCheck B ks.1 c)
      (false, emptyTable)).toOuterMeasure {x | x.2.1 = true} =
      ((OracleAdv.run (OracleAdv.simOracle (progBad P ks) roOracle) (withCheck B ks.1 c)
        (false, emptyTable)).map (fun x => (x.1, x.2.1))).toOuterMeasure {x | x.2 = true} := by
    rw [PMF.toOuterMeasure_map_apply]; rfl
  rw [e, h, PMF.toOuterMeasure_bind_apply]
  refine tsum_congr fun f => congrArg _ ?_
  have h₁ := OracleAdv.run_map_state (OracleAdv.simOracle (progBad P ks) (keyedRO f))
    (eO (ansSim P ks.1) (badOnly P ks) f) Prod.fst (fun s d => simOracle_progBad_keyed P ks f s d)
    (withCheck B ks.1 c) (false, ())
  have h₂ := run_eO_forget (ansSim P ks.1) (ghostUpd P ks mstar) (badOnly P ks) Prod.fst
    (fun _ _ _ => rfl) f (withCheck B ks.1 c) (false, false)
  rw [show (fun x : (M × Bool) × (Bool × Unit) => (x.1, x.2.1)) = Prod.map id Prod.fst from rfl, h₁,
    ← h₂, PMF.toOuterMeasure_map_apply]
  rfl

omit [Nonempty M] in
/-- The probability of reading the random oracle at `m*`, averaged over a uniform
function, is the probability that `m*` is in the log of the lazily sampled run. -/
theorem eager_query_eq {qG qP : ℕ} (B : ROMOWPCAAdversary PK M C M R qG qP) (ks : PK × SK)
    (mstar : M) (c : C) :
    ∑' f, PMF.uniformOfFintype (M → R) f *
      (OracleAdv.run (eO (ansSim P ks.1) (ghostUpd P ks mstar) f) (withCheck B ks.1 c)
        (false, false)).toOuterMeasure {x | x.2.2 = true} =
    (OracleAdv.run (OracleAdv.simOracle (progLog P ks.1) roOracle) (withCheck B ks.1 c)
      ([], emptyTable)).toOuterMeasure {x | mstar ∈ x.2.1} := by
  have h := lazy_log_eq P ks.1 (withCheck B ks.1 c)
  have e : (OracleAdv.run (OracleAdv.simOracle (progLog P ks.1) roOracle) (withCheck B ks.1 c)
      ([], emptyTable)).toOuterMeasure {x | mstar ∈ x.2.1} =
      ((OracleAdv.run (OracleAdv.simOracle (progLog P ks.1) roOracle) (withCheck B ks.1 c)
        ([], emptyTable)).map (fun x => (x.1, x.2.1))).toOuterMeasure {x | mstar ∈ x.2} := by
    rw [PMF.toOuterMeasure_map_apply]; rfl
  rw [e, h, PMF.toOuterMeasure_bind_apply]
  refine tsum_congr fun f => congrArg _ ?_
  have h₁ := run_eO_forget (ansSim P ks.1) (ghostUpd P ks mstar)
    (fun m _ q => q || decide (m = mstar)) Prod.snd (fun _ _ _ => rfl) f (withCheck B ks.1 c)
    (false, false)
  have h₂ := run_eO_forget (ansSim P ks.1) (fun m _ l => m :: l)
    (fun m _ q => q || decide (m = mstar)) (fun l => decide (mstar ∈ l))
    (fun m _ l => by simp [List.mem_cons, eq_comm, Bool.or_comm]) f (withCheck B ks.1 c) []
  have e₁ : (OracleAdv.run (eO (ansSim P ks.1) (ghostUpd P ks mstar) f) (withCheck B ks.1 c)
      (false, false)).toOuterMeasure {x | x.2.2 = true} =
      ((OracleAdv.run (eO (ansSim P ks.1) (ghostUpd P ks mstar) f) (withCheck B ks.1 c)
        (false, false)).map (Prod.map id Prod.snd)).toOuterMeasure {x | x.2 = true} := by
    rw [PMF.toOuterMeasure_map_apply]; rfl
  have e₂ : (OracleAdv.run (eO (ansSim P ks.1) (fun m _ l => m :: l) f) (withCheck B ks.1 c)
      []).toOuterMeasure {x | mstar ∈ x.2} =
      ((OracleAdv.run (eO (ansSim P ks.1) (fun m _ l => m :: l) f) (withCheck B ks.1 c)
        []).map (Prod.map id fun l => decide (mstar ∈ l))).toOuterMeasure {x | x.2 = true} := by
    rw [PMF.toOuterMeasure_map_apply]; congr 1; ext x; simp
  rw [e₁, e₂, h₁, h₂]
  rfl

omit [Fintype M] [Nonempty M] in
theorem length_log_le {α : Type} (pk : PK) (A : OracleAdv (M ⊕ (M × C)) (R ⊕ Bool) α) (n : ℕ)
    (hA : A.IsQueryBoundBy (fun _ => 1) n) (l : List M) (T : M → Option R)
    (y : α × (List M × (M → Option R)))
    (hy : y ∈ (OracleAdv.run (OracleAdv.simOracle (progLog P pk) roOracle) A (l, T)).support) :
    y.2.1.length ≤ l.length + n := by
  induction A generalizing n l T with
  | ret a =>
    simp only [OracleAdv.run_ret, PMF.support_pure, Set.mem_singleton_iff] at hy
    subst hy; simp
  | rand p k ih =>
    simp only [OracleAdv.run_rand, PMF.mem_support_bind_iff] at hy
    obtain ⟨b, -, hy⟩ := hy
    exact ih b n (hA b) l T hy
  | query d k ih =>
    simp only [OracleAdv.run_query, PMF.mem_support_bind_iff] at hy
    obtain ⟨x, hx, hy⟩ := hy
    obtain ⟨hle, hk⟩ := hA
    have hlen : x.2.1.length = l.length + 1 := by
      cases d with
      | inl m =>
        simp only [OracleAdv.simOracle, progLog, OracleAdv.run_query, OracleAdv.run_ret,
          PMF.support_map, PMF.mem_support_bind_iff, PMF.support_pure, Set.mem_image,
          Set.mem_singleton_iff] at hx
        obtain ⟨z, ⟨w, -, rfl⟩, rfl⟩ := hx; simp
      | inr q =>
        simp only [OracleAdv.simOracle, progLog, OracleAdv.run_query, OracleAdv.run_ret,
          PMF.support_map, PMF.mem_support_bind_iff, PMF.support_pure, Set.mem_image,
          Set.mem_singleton_iff] at hx
        obtain ⟨z, ⟨w, -, rfl⟩, rfl⟩ := hx; simp
    have := ih x.1 (n - 1) (hk x.1) x.2.1 x.2.2 hy
    simp only at hle
    omega

omit [Nonempty M] in
/-- **Guessing a logged point.** When `c` decrypts to `m*`, the probability that `m*`
is in the log of the simulation is at most `n + 1` times the success probability of
`tReductionD`, for an adversary asking at most `n` queries. -/
theorem query_le_D {qG qP : ℕ} (B : ROMOWPCAAdversary PK M C M R qG qP) (n : ℕ)
    (hB : ∀ pk c, (B.run pk c).IsQueryBoundBy (fun _ => 1) n) (ks : PK × SK)
    (mstar : M) (c : C) (hdec : P.dec ks.2 c = some mstar) :
    (OracleAdv.run (OracleAdv.simOracle (progLog P ks.1) roOracle) (withCheck B ks.1 c)
      ([], emptyTable)).toOuterMeasure {x | mstar ∈ x.2.1} ≤
    ((n + 1 : ℕ) : ℝ≥0∞) *
      (tReductionD P B n ks.1 c).toOuterMeasure {m | P.dec ks.2 c = some m} := by
  set p := OracleAdv.run (OracleAdv.simOracle (progLog P ks.1) roOracle) (withCheck B ks.1 c)
    ([], emptyTable)
  unfold tReductionD
  rw [PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_apply, ← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hx : mstar ∈ x.2.1
  swap
  · simp [Set.indicator, hx]
  by_cases hp : p x = 0
  · simp [Set.indicator, hp]
  have hlen := length_log_le P ks.1 _ _ (isQueryBoundBy_withCheck B n hB ks.1 c) [] emptyTable x
    ((PMF.mem_support_iff _ _).mpr hp)
  simp only [List.length_nil, zero_add] at hlen
  obtain ⟨i, hi, hxi⟩ := List.getElem_of_mem hx
  have hL : i < n + 1 := lt_of_lt_of_le hi hlen
  simp only [Set.indicator, Set.mem_ofPred_eq, hx, if_true]
  calc p x = ((n + 1 : ℕ) : ℝ≥0∞) * (((n + 1 : ℕ) : ℝ≥0∞)⁻¹ * p x) := by
        rw [← mul_assoc, ENNReal.mul_inv_cancel (by simp) (ENNReal.natCast_ne_top _), one_mul]
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left ?_ bot_le
        rw [mul_comm]
        refine mul_le_mul_of_nonneg_left ?_ bot_le
        rw [PMF.toOuterMeasure_map_apply]
        change _ ≤ ((PMF.uniformOfFintype (Fin (n + 1))).bind fun a =>
          PMF.pure (a : ℕ)).toOuterMeasure _
        rw [PMF.toOuterMeasure_bind_apply]
        refine le_trans (le_of_eq ?_) (ENNReal.le_tsum ⟨i, hL⟩)
        rw [PMF.toOuterMeasure_pure_apply, if_pos]
        · simp
        · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, hxi, hdec]

end Lazy

/-! ## The theorem -/

section Main

omit [Fintype M] [Nonempty M] [DecidableEq M] [DecidableEq C] [Fintype R] [Nonempty R] in
theorem tsum_mul_comm' {α β : Type} (p : α → ℝ≥0∞) (q : β → ℝ≥0∞) (F : α → β → ℝ≥0∞) :
    ∑' a, p a * ∑' b, q b * F a b = ∑' b, q b * ∑' a, p a * F a b := by
  simp only [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  exact tsum_congr fun b => tsum_congr fun a => by ring

/-- The indicator of a decryption failure: `0` when `Dec(sk, c) = m`, `1` otherwise. -/
noncomputable def failInd (sk : SK) (m : M) (c : C) : ℝ≥0∞ :=
  if P.dec sk c = some m then 0 else 1

omit [DecidableEq C] in
theorem corrErr_eq :
    P.corrErr = ∑' ks, P.keygen ks * ∑' m, PMF.uniformOfFintype M m *
      ∑' r, PMF.uniformOfFintype R r * failInd P ks.2 m (P.enc ks.1 m r) := by
  unfold Scheme.corrErr Scheme.failProb
  refine tsum_congr fun ks => congrArg _ (tsum_congr fun m => congrArg _ ?_)
  rw [PMF.toOuterMeasure_apply]
  refine tsum_congr fun r => ?_
  by_cases h : P.dec ks.2 (P.enc ks.1 m r) = some m <;> simp [Set.indicator, h, failInd]

omit [Fintype M] [Nonempty M] [DecidableEq M] [DecidableEq C] [Fintype R] [Nonempty R] in
theorem prTrue_pmfGame_eq (p : PMF Bool) :
    prTrue (pmfGame p) Heap.empty = p.toOuterMeasure {b | b = true} := by
  have h := prTrue_pmfGame_map p id Heap.empty
  rwa [PMF.map_id] at h

omit [DecidableEq C] in
theorem owcpaAdvantage_eq (A : PK → C → PMF M) :
    owcpaAdvantage P A = ∑' ks, P.keygen ks * ∑' m, PMF.uniformOfFintype M m *
      ∑' r, PMF.uniformOfFintype R r *
        (A ks.1 (P.enc ks.1 m r)).toOuterMeasure {m' | P.dec ks.2 (P.enc ks.1 m r) = some m'} := by
  rw [owcpaAdvantage, prTrue_pmfGame_eq, owcpaGame]
  simp only [PMF.toOuterMeasure_bind_apply, Scheme.encDist, PMF.bind_map, Function.comp_def,
    PMF.toOuterMeasure_map_apply]
  refine tsum_congr fun ks => congrArg _ (tsum_congr fun m => congrArg _
    (tsum_congr fun r => congrArg _ ?_))
  congr 1
  ext m'
  simp [Scheme.pco]

/-- The run with re-encryption answers and ghost flags on the challenge `c`. -/
noncomputable def ghRun {qG qP : ℕ} (B : ROMOWPCAAdversary PK M C M R qG qP) (ks : PK × SK)
    (mstar : M) (f : M → R) (c : C) : PMF ((M × Bool) × (Bool × Bool)) :=
  OracleAdv.run (eO (ansSim P ks.1) (ghostUpd P ks mstar) f) (withCheck B ks.1 c) (false, false)

omit [Nonempty M] in
theorem game_le_chain {qG qP : ℕ} (B : ROMOWPCAAdversary PK M C M R qG qP) (ks : PK × SK)
    (mstar : M) :
    ((OracleAdv.run (OracleAdv.simOracle (progReal P ks) roOracle) (fullRun P B ks.1 mstar)
      ((), emptyTable)).map fun x => x.1.2).toOuterMeasure {b | b = true} ≤
    ∑' r, PMF.uniformOfFintype R r *
      (∑' f, PMF.uniformOfFintype (M → R) f * (ghRun P B ks mstar f (P.enc ks.1 mstar r)).toOuterMeasure
          {x | P.dec ks.2 (P.enc ks.1 mstar r) = some x.1.1} +
        ∑' f, PMF.uniformOfFintype (M → R) f *
          (ghRun P B ks mstar f (P.enc ks.1 mstar r)).toOuterMeasure {x | x.2.1 = true} +
        ∑' f, PMF.uniformOfFintype (M → R) f *
          (ghRun P B ks mstar f (P.enc ks.1 mstar r)).toOuterMeasure {x | x.2.2 = true}) := by
  rw [game_eq_eager, PMF.toOuterMeasure_bind_apply]
  have h1 := fun f => real_le_sim P B ks mstar f (P.enc ks.1 mstar (f mstar))
  have h2 := challenge_hop P B ks mstar {x | x.1.2 = true ∨ x.2.1 = true}
  have h3 : ∀ f r, (ghRun P B ks mstar f (P.enc ks.1 mstar r)).toOuterMeasure
      {x | x.1.2 = true ∨ x.2.1 = true} ≤
      (ghRun P B ks mstar f (P.enc ks.1 mstar r)).toOuterMeasure
        {x | P.dec ks.2 (P.enc ks.1 mstar r) = some x.1.1} +
      (ghRun P B ks mstar f (P.enc ks.1 mstar r)).toOuterMeasure {x | x.2.1 = true} :=
    fun f r => event_le P B ks mstar f _
  refine (ENNReal.tsum_le_tsum fun f => mul_le_mul_right (h1 f) _).trans (h2.trans ?_)
  refine (ENNReal.tsum_le_tsum fun f => mul_le_mul_right (ENNReal.tsum_le_tsum fun r =>
    mul_le_mul_right (add_le_add (h3 f r) le_rfl) _) _).trans (le_of_eq ?_)
  rw [tsum_mul_comm']
  simp only [mul_add, ENNReal.tsum_add]
  rfl

omit [Nonempty M] in
theorem sumC_eq {qG qP : ℕ} (B : ROMOWPCAAdversary PK M C M R qG qP) (ks : PK × SK)
    (mstar : M) (c : C) :
    ∑' f, PMF.uniformOfFintype (M → R) f * (ghRun P B ks mstar f c).toOuterMeasure
      {x | P.dec ks.2 c = some x.1.1} =
    (tReductionC P B ks.1 c).toOuterMeasure {m' | P.dec ks.2 c = some m'} := by
  rw [tReductionC_eq, PMF.toOuterMeasure_bind_apply]
  refine tsum_congr fun f => congrArg _ ?_
  rw [← ghost_map_output P B ks mstar f c, PMF.toOuterMeasure_map_apply]
  rfl

omit [Nonempty M] in
theorem sumBad_le {qG qP : ℕ} (B : ROMOWPCAAdversary PK M C M R qG qP) (n : ℕ)
    (hB : ∀ pk c, (B.run pk c).IsQueryBoundBy (fun _ => 1) n) (ks : PK × SK)
    (mstar : M) (c : C) :
    ∑' f, PMF.uniformOfFintype (M → R) f * (ghRun P B ks mstar f c).toOuterMeasure
      {x | x.2.1 = true} ≤ ((n + 1 : ℕ) : ℝ≥0∞) * worst P ks := by
  unfold ghRun
  rw [eager_bad_eq]
  exact lazy_bad_le P ks _ _ (isQueryBoundBy_withCheck B n hB ks.1 c) emptyTable
    (fun m r h => by simp [emptyTable] at h)

omit [Nonempty M] in
theorem sumQuery_le {qG qP : ℕ} (B : ROMOWPCAAdversary PK M C M R qG qP) (n : ℕ)
    (hB : ∀ pk c, (B.run pk c).IsQueryBoundBy (fun _ => 1) n) (ks : PK × SK)
    (mstar : M) (c : C) :
    ∑' f, PMF.uniformOfFintype (M → R) f * (ghRun P B ks mstar f c).toOuterMeasure
      {x | x.2.2 = true} ≤
    failInd P ks.2 mstar c + ((n + 1 : ℕ) : ℝ≥0∞) *
      (tReductionD P B n ks.1 c).toOuterMeasure {m' | P.dec ks.2 c = some m'} := by
  unfold ghRun
  rw [eager_query_eq]
  by_cases hdec : P.dec ks.2 c = some mstar
  · exact (query_le_D P B n hB ks mstar c hdec).trans le_add_self
  · simp only [failInd, hdec, if_false]
    exact (le_self_add.trans_eq (toOuterMeasure_add_compl _ _)).trans le_self_add

omit [Nonempty M] in
/-- **Per key pair and challenge message.** -/
theorem game_le {qG qP : ℕ} (B : ROMOWPCAAdversary PK M C M R qG qP) (n : ℕ)
    (hB : ∀ pk c, (B.run pk c).IsQueryBoundBy (fun _ => 1) n) (ks : PK × SK) (mstar : M) :
    ((OracleAdv.run (OracleAdv.simOracle (progReal P ks) roOracle) (fullRun P B ks.1 mstar)
      ((), emptyTable)).map fun x => x.1.2).toOuterMeasure {b | b = true} ≤
    ∑' r, PMF.uniformOfFintype R r *
      ((tReductionC P B ks.1 (P.enc ks.1 mstar r)).toOuterMeasure
          {m' | P.dec ks.2 (P.enc ks.1 mstar r) = some m'} +
        ((n + 1 : ℕ) : ℝ≥0∞) * worst P ks + failInd P ks.2 mstar (P.enc ks.1 mstar r) +
        ((n + 1 : ℕ) : ℝ≥0∞) * (tReductionD P B n ks.1 (P.enc ks.1 mstar r)).toOuterMeasure
          {m' | P.dec ks.2 (P.enc ks.1 mstar r) = some m'}) := by
  refine (game_le_chain P B ks mstar).trans (ENNReal.tsum_le_tsum fun r =>
    mul_le_mul_right ?_ _)
  refine (add_le_add (add_le_add (le_of_eq (sumC_eq P B ks mstar _))
    (sumBad_le P B n hB ks mstar _)) (sumQuery_le P B n hB ks mstar _)).trans (le_of_eq ?_)
  ring

/-- **T is OW-PCA secure in the random-oracle model, total query bound.** For every
public-key encryption scheme `P` and every OW-PCA adversary `B` against
`tTransform P` asking at most `n` queries in total (random-oracle and
plaintext-checking),

`romOWPCAAdvantage (tTransform P) B ≤ owcpaAdvantage P (tReductionC P B) +
  (n + 1)·δ + P.corrErr + (n + 1)·owcpaAdvantage P (tReductionD P B n)`

with `δ = P.corrWorst` the correctness error and `P.corrErr ≤ δ`. -/
theorem tTransform_owpca_of_total {qG qP : ℕ} (B : ROMOWPCAAdversary PK M C M R qG qP) (n : ℕ)
    (hB : ∀ pk c, (B.run pk c).IsQueryBoundBy (fun _ => 1) n) :
    romOWPCAAdvantage (tTransform P) B ≤
      owcpaAdvantage P (tReductionC P B) + ((n + 1 : ℕ) : ℝ≥0∞) * P.corrWorst +
        P.corrErr + ((n + 1 : ℕ) : ℝ≥0∞) * owcpaAdvantage P (tReductionD P B n) := by
  rw [romOWPCAAdvantage, prTrue_pmfGame_eq, romOWPCAGame_eq, PMF.toOuterMeasure_bind_apply]
  simp only [PMF.toOuterMeasure_bind_apply]
  calc _ ≤ ∑' ks, P.keygen ks * ∑' m, PMF.uniformOfFintype M m * ∑' r, PMF.uniformOfFintype R r *
          ((tReductionC P B ks.1 (P.enc ks.1 m r)).toOuterMeasure
              {m' | P.dec ks.2 (P.enc ks.1 m r) = some m'} +
            ((n + 1 : ℕ) : ℝ≥0∞) * worst P ks + failInd P ks.2 m (P.enc ks.1 m r) +
            ((n + 1 : ℕ) : ℝ≥0∞) * (tReductionD P B n ks.1 (P.enc ks.1 m r)).toOuterMeasure
              {m' | P.dec ks.2 (P.enc ks.1 m r) = some m'}) :=
        ENNReal.tsum_le_tsum fun ks => mul_le_mul_right (ENNReal.tsum_le_tsum fun m =>
          mul_le_mul_right (game_le P B n hB ks m) _) _
    _ = _ := by
        simp only [mul_add, ENNReal.tsum_add]
        rw [owcpaAdvantage_eq, owcpaAdvantage_eq, corrErr_eq, Scheme.corrWorst]
        simp only [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
        congr 1
        · congr 1
          · congr 1
            rw [← ENNReal.tsum_mul_left]
            refine tsum_congr fun ks => ?_
            simp only [worst]; ring
        · simp only [← ENNReal.tsum_mul_left]
          exact tsum_congr fun ks => tsum_congr fun m => tsum_congr fun r => by ring

/-- **T is OW-PCA secure in the random-oracle model** (Hofheinz–Hövelmanns–Kiltz,
Theorem 3.1, plaintext-checking part). For every public-key encryption scheme `P`
and every OW-PCA adversary `B` against `tTransform P` asking at most `qG`
random-oracle queries and `qP` plaintext-checking queries,

`romOWPCAAdvantage (tTransform P) B ≤ owcpaAdvantage P (tReductionC P B) +
  (qG + qP + 1)·δ + P.corrErr + (qG + qP + 1)·owcpaAdvantage P (tReductionD P B (qG + qP))`

with `δ = P.corrWorst` the correctness error and `P.corrErr ≤ δ`. Both reductions run
`B` once with a lazily sampled random oracle and answer plaintext-checking queries
by re-encryption. -/
theorem tTransform_owpca {qG qP : ℕ} (B : ROMOWPCAAdversary PK M C M R qG qP) :
    romOWPCAAdvantage (tTransform P) B ≤
      owcpaAdvantage P (tReductionC P B) + ((qG + qP + 1 : ℕ) : ℝ≥0∞) * P.corrWorst +
        P.corrErr + ((qG + qP + 1 : ℕ) : ℝ≥0∞) * owcpaAdvantage P (tReductionD P B (qG + qP)) :=
  tTransform_owpca_of_total P B (qG + qP) (isQueryBoundBy_total B)

end Main

end CatCrypt.Crypto.PKE.FOTransformT
