/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.KEM.FOTransformU
public import CatCryptCore.Crypto.PKE.FOTransformT

/-!
# The Fujisaki–Okamoto transform with implicit rejection in the random-oracle model

`foNotBot P = FO⊥̸[P, G, H] = U⊥̸[T[P, G], H]` for a public-key encryption scheme `P`
with messages `M`, ciphertexts `C` and coins `R`, and two random oracles
`G : M → R` and `H : M × C → K`. Encapsulation samples `m`, sets
`c = Enc(pk, m; G(m))` and returns `K = H(m, c)`. Decapsulation of `c` returns
`H(m, c)` when `m = Dec(sk, c)` re-encrypts to `c`, and `H(s, c)` otherwise. The
IND-CCA game is `KEM.Games.rom2INDCCAGame`: both oracles are sampled lazily and
shared by the challenger, decapsulation and the adversary.

## Main definitions

* `foNotBot` — the transform
* `uRedROM B` — the OW-PCA adversary against `tTransform P` built from an IND-CCA
  adversary `B`
* `fixedT P f`, `absorb f B` — `T[P, f]` for a fixed function `f` and `B` with its
  queries to `G` answered by `f`

## Main results

* `foNotBot_indcca` — for every IND-CCA adversary `B` with at most `qRO` queries to the
  random oracles,
  `rom2INDCCAAdvantage (foNotBot P) B ≤ owcpaAdvantage P (tReductionC P (uRedROM B)) +
  (qRO + 1)·δ + P.corrErr + (qRO + 1)·owcpaAdvantage P (tReductionD P (uRedROM B) qRO) +
  qRO/|M| + P.corrErr`
* `foNotBot_indcca_of_indcpa` — the same bound with each OW-CPA term replaced by an
  IND-CPA term via `PKE.Games.owcpa_le_indcpa`

## Proof outline

1. `G` is sampled eagerly and `H` stays lazy (`run_rom2CCA_eq_fixed`, `foGame_eq`): the
   experiment is the average over a uniform `f` of the IND-CCA experiment of
   `uNotBot (fixedT P f)` against `absorb f B`.
2. The advantage of the average is at most the average of the advantages
   (`advantage_bind_le`), and `FOTransformU.uNotBot_indcca` bounds each.
3. The average of the OW-PCA advantages of `uReduction (absorb f B)` against
   `fixedT P f` is the OW-PCA advantage of `uRedROM B` against `tTransform P`
   (`owpca_eq`), and the average correctness error of `fixedT P f` is `P.corrErr`
   (`corrErr_fixedT`).
4. `PKE.FOTransformT.tTransform_owpca_of_total` bounds the OW-PCA advantage of
   `uRedROM B`, which asks at most `qRO` queries.

## The model

The game `rom2INDCCAGame` is the classical random-oracle model: the adversary
queries `G` and `H` on classical inputs, and `qRO` bounds the number of these
queries.

## References

* D. Hofheinz, K. Hövelmanns, E. Kiltz, *A Modular Analysis of the
  Fujisaki–Okamoto Transformation*, TCC 2017, ePrint 2017/604, Section 3.3.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.KEM.FOTransform

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.PRPPRF
open CatCrypt.Crypto.PKE.Games CatCrypt.Crypto.KEM.Games
open CatCrypt.Crypto.PKE.FOTransformT (keyedRO extDist run_simOracle_roOracle_eq
  extDist_map_pair extDist_empty tTransform tReductionC tReductionD tTransform_owpca_of_total)
open CatCrypt.Crypto.KEM.FOTransformU (uNotBot uReduction uNotBot_indcca)
open scoped ENNReal

variable {PK SK M C R K : Type} [Fintype R] [Nonempty R] [Fintype M] [Nonempty M]
  [DecidableEq M] [DecidableEq C] [Fintype K] [Nonempty K]

/-! ## The transform -/

/-- A query to `G` at `m`, as a program on the two random oracles. -/
noncomputable def gQ (m : M) : OracleAdv (M ⊕ (M × C)) (R ⊕ K) R :=
  .query (.inl m) fun a => .ret (a.elim id fun _ => Classical.arbitrary R)

/-- A query to `H` at `q`, as a program on the two random oracles. -/
noncomputable def hQ (q : M × C) : OracleAdv (M ⊕ (M × C)) (R ⊕ K) K :=
  .query (.inr q) fun a => .ret (a.elim (fun _ => Classical.arbitrary K) id)

/-- The Fujisaki–Okamoto KEM `FO⊥̸[P, G, H]` with implicit rejection. The secret key
is `((pk, sk), s)` with `s` uniform in `M`. -/
noncomputable def foNotBot (P : Scheme PK SK M C R) :
    ROM2Scheme PK ((PK × SK) × M) K C M R (M × C) K where
  keygen := P.keygen.bind fun ks =>
    (PMF.uniformOfFintype M).map fun s => (ks.1, ((ks.1, ks.2), s))
  encaps pk := .rand (PMF.uniformOfFintype M) fun m => (gQ m).bind fun r =>
    (hQ (m, P.enc pk m r)).bind fun k => .ret (k, P.enc pk m r)
  decaps sk c := match P.dec sk.1.2 c with
    | none => (hQ (sk.2, c)).bind fun k => .ret (some k)
    | some m => (gQ m).bind fun r =>
        if P.enc sk.1.1 m r = c then (hQ (m, c)).bind fun k => .ret (some k)
        else (hQ (sk.2, c)).bind fun k => .ret (some k)

/-- The transform `T[P, f]` for a fixed function `f : M → R`, as a public-key
encryption scheme without coins. -/
noncomputable def fixedT (P : Scheme PK SK M C R) (f : M → R) : Scheme PK (PK × SK) M C Unit where
  keygen := P.keygen.map fun ks => (ks.1, (ks.1, ks.2))
  enc pk m _ := P.enc pk m (f m)
  dec sk c := match P.dec sk.2 c with
    | none => none
    | some m => if P.enc sk.1 m (f m) = c then some m else none

/-- The adversary `B` with its queries to `G` answered by `f`. -/
noncomputable def absImpl (f : M → R) (u : Unit) :
    (M ⊕ (M × C)) ⊕ C → OracleAdv ((M × C) ⊕ C) (K ⊕ Option K) (((R ⊕ K) ⊕ Option K) × Unit)
  | .inl (.inl m) => .ret (.inl (.inl (f m)), u)
  | .inl (.inr q) => .query (.inl q) fun a => .ret (.inl (.inr (a.elim id fun _ => Classical.arbitrary K)), u)
  | .inr c => .query (.inr c) fun a => .ret (.inr (a.elim (fun _ => none) id), u)

/-- The IND-CCA adversary against `uNotBot (fixedT P f)` that runs `B` with its
queries to `G` answered by `f` and its other queries forwarded. -/
noncomputable def absorb (f : M → R) {qRO qD : ℕ}
    (B : ROM2INDCCAAdversary PK K C M R (M × C) K qRO qD) :
    ROMINDCCAAdversary PK K C (M × C) K qRO qD where
  run pk c k := (OracleAdv.simulate (absImpl f) (B.run pk c k) ()).bind fun x => .ret x.1
  isQueryBoundH pk c k := by
    have h := OracleAdv.isQueryBoundBy_simulate (absImpl (C := C) (K := K) f)
      (Sum.elim (fun _ => 1) fun _ => 0) (Sum.elim (fun _ => 1) fun _ => 0)
      (fun u d => by
        rcases d with (m | q) | c
        · trivial
        · exact ⟨le_rfl, fun _ => trivial⟩
        · exact ⟨le_rfl, fun _ => trivial⟩) (B.isQueryBoundRO pk c k) ()
    simpa using OracleAdv.isQueryBoundBy_bind h (b := 0)
      (f := fun x : Bool × Unit => OracleAdv.ret x.1) fun _ => trivial
  isQueryBoundD pk c k := by
    have h := OracleAdv.isQueryBoundBy_simulate (absImpl (C := C) (K := K) f)
      (Sum.elim (fun _ => 0) fun _ => 1) (Sum.elim (fun _ => 0) fun _ => 1)
      (fun u d => by
        rcases d with (m | q) | c
        · trivial
        · exact ⟨le_rfl, fun _ => trivial⟩
        · exact ⟨le_rfl, fun _ => trivial⟩) (B.isQueryBoundD pk c k) ()
    simpa using OracleAdv.isQueryBoundBy_bind h (b := 0)
      (f := fun x : Bool × Unit => OracleAdv.ret x.1) fun _ => trivial

/-! ## The oracle `H` as simulator state -/

section Split

/-- The two random oracles as a program on `G`, with the table of `H` as simulator
state: queries to `H` are sampled lazily by the program itself. -/
noncomputable def progH (TH : M × C → Option K) :
    M ⊕ (M × C) → OracleAdv M R ((R ⊕ K) × (M × C → Option K))
  | .inl m => .query m fun r => .ret (.inl r, TH)
  | .inr q => match TH q with
    | some k => .ret (.inr k, TH)
    | none => .rand (PMF.uniformOfFintype K) fun k => .ret (.inr k, Function.update TH q (some k))

omit [Fintype M] [Nonempty M] in
theorem simOracle_progH (TH : M × C → Option K) (TG : M → Option R) (d : M ⊕ (M × C)) :
    (OracleAdv.simOracle progH roOracle (TH, TG) d).map (Prod.map id Prod.swap) =
      ro2Oracle (TG, TH) d := by
  cases d with
  | inl m =>
    simp only [OracleAdv.simOracle, progH, ro2Oracle, OracleAdv.run_query, OracleAdv.run_ret,
      PMF.map_bind, PMF.pure_map]
    rfl
  | inr q =>
    cases h : TH q with
    | some k => simp [OracleAdv.simOracle, progH, ro2Oracle, roOracle, h, PMF.pure_map]
    | none =>
      simp only [OracleAdv.simOracle, progH, ro2Oracle, roOracle, h, OracleAdv.run_rand,
        OracleAdv.run_ret, PMF.map_bind, PMF.pure_map, PMF.map_comp]
      rfl

omit [Fintype M] [Nonempty M] in
theorem run_ro2_eq {α : Type} (A : OracleAdv (M ⊕ (M × C)) (R ⊕ K) α) (TG : M → Option R)
    (TH : M × C → Option K) :
    OracleAdv.run ro2Oracle A (TG, TH) =
      (OracleAdv.run (OracleAdv.simOracle progH roOracle) A (TH, TG)).map (Prod.map id Prod.swap) :=
  (OracleAdv.run_map_state _ _ Prod.swap (fun s d => simOracle_progH s.1 s.2 d) A (TH, TG)).symm

/-- The IND-CCA oracle of `foNotBot P` as a program on the two random oracles. -/
noncomputable def ccaImpl (P : Scheme PK SK M C R) (sk : (PK × SK) × M) (cstar : C) (u : Unit) :
    (M ⊕ (M × C)) ⊕ C → OracleAdv (M ⊕ (M × C)) (R ⊕ K) (((R ⊕ K) ⊕ Option K) × Unit)
  | .inl d => .query d fun a => .ret (.inl a, u)
  | .inr c => if c = cstar then .ret (.inr none, u) else
      ((foNotBot P).decaps sk c).bind fun o => .ret (.inr o, u)

theorem run_rom2CCAOracle_eq {α : Type} (P : Scheme PK SK M C R) (sk : (PK × SK) × M) (cstar : C)
    (A : OracleAdv ((M ⊕ (M × C)) ⊕ C) ((R ⊕ K) ⊕ Option K) α)
    (T : (M → Option R) × (M × C → Option K)) :
    (OracleAdv.run (rom2CCAOracle (foNotBot P) sk cstar) A T).map Prod.fst =
      (OracleAdv.run ro2Oracle (OracleAdv.simulate (ccaImpl P sk cstar) A ()) T).map
        (fun x => x.1.1) := by
  have h := OracleAdv.run_map_state (OracleAdv.simOracle (ccaImpl P sk cstar) ro2Oracle)
    (rom2CCAOracle (foNotBot P) sk cstar) Prod.snd (fun s d => by
      cases d with
      | inl d =>
        simp only [OracleAdv.simOracle, ccaImpl, rom2CCAOracle, OracleAdv.run_query,
          OracleAdv.run_ret, PMF.map_bind, PMF.pure_map]
        rfl
      | inr c =>
        simp only [OracleAdv.simOracle, ccaImpl, rom2CCAOracle]
        split_ifs
        · simp [PMF.pure_map]
        · simp only [OracleAdv.run_bind, OracleAdv.run_ret, PMF.map_bind, PMF.pure_map]
          rfl) A ((), T)
  rw [OracleAdv.run_simulate, PMF.map_comp, ← h, PMF.map_comp]
  rfl

end Split

/-! ## Fixing `G` -/

section Fixed

/-- The oracle `H` sampled lazily with `G` answered by `f`. -/
noncomputable abbrev hfOracle (f : M → R) :=
  OracleAdv.simOracle (progH (C := C) (K := K)) (keyedRO f)

omit [Fintype R] [Nonempty R] [Fintype M] [Nonempty M] in
theorem hfOracle_inl (f : M → R) (TH : M × C → Option K) (u : Unit) (m : M) :
    hfOracle f (TH, u) (.inl m) = PMF.pure (.inl (f m), (TH, ())) := by
  simp [OracleAdv.simOracle, progH, keyedRO, PMF.pure_map]

omit [Fintype R] [Nonempty R] [Fintype M] [Nonempty M] in
theorem hfOracle_inr (f : M → R) (TH : M × C → Option K) (u : Unit) (q : M × C) :
    hfOracle f (TH, u) (.inr q) = (roOracle TH q).map fun x => (.inr x.1, (x.2, ())) := by
  cases h : TH q with
  | some k => simp [OracleAdv.simOracle, progH, roOracle, h, PMF.pure_map]
  | none =>
    simp only [OracleAdv.simOracle, progH, roOracle, h, OracleAdv.run_rand, OracleAdv.run_ret,
      PMF.map_bind, PMF.pure_map, PMF.map_comp]
    rfl

omit [Fintype R] in
/-- With `G` answered by `f`, one step of the IND-CCA oracle of `foNotBot P` is one step
of the IND-CCA oracle of `uNotBot (fixedT P f)` on the adversary with queries to `G`
absorbed. -/
theorem step_eq (P : Scheme PK SK M C R) (f : M → R) (sk : PK × SK) (s : M) (cstar : C)
    (TH : M × C → Option K) (d : (M ⊕ (M × C)) ⊕ C) :
    (OracleAdv.simOracle (ccaImpl P ((sk.1, sk.2), s) cstar) (hfOracle f) ((), (TH, ())) d).map
        (Prod.map id fun y => ((), y.2.1)) =
      OracleAdv.simOracle (absImpl f) (romCCAOracle (uNotBot (fixedT P f)) ((sk.1, sk.2), s) cstar)
        ((), TH) d := by
  rcases d with (m | q) | c
  · simp [OracleAdv.simOracle, ccaImpl, absImpl, hfOracle_inl, PMF.pure_map]
  · simp only [OracleAdv.simOracle, ccaImpl, absImpl, OracleAdv.run_query, OracleAdv.run_ret,
      hfOracle_inr, romCCAOracle, PMF.bind_map, PMF.map_bind, PMF.pure_map, Function.comp_def]
    rfl
  · by_cases hc : c = cstar
    · subst hc
      simp [OracleAdv.simOracle, ccaImpl, absImpl, romCCAOracle, PMF.pure_map]
    · simp only [OracleAdv.simOracle, ccaImpl, absImpl, hc, if_false, OracleAdv.run_query,
        OracleAdv.run_ret, OracleAdv.run_bind, romCCAOracle, uNotBot, FOTransformU.decIdx,
        PMF.map_bind, PMF.pure_map]
      cases hd : P.dec sk.2 c with
      | none =>
        simp only [foNotBot, fixedT, hd, hQ, OracleAdv.run_bind, OracleAdv.run_query,
          OracleAdv.run_ret, hfOracle_inr, PMF.bind_map,
          Function.comp_def, PMF.pure_bind, Option.getD_none, PMF.bind_bind, Sum.elim_inr, id]
        rfl
      | some m =>
        by_cases he : P.enc sk.1 m (f m) = c
        · simp only [foNotBot, fixedT, hd, he, gQ, hQ, if_true, OracleAdv.run_bind,
            OracleAdv.run_query, OracleAdv.run_ret, hfOracle_inl, hfOracle_inr, PMF.bind_map,
            Function.comp_def, PMF.pure_bind, Option.getD_some,
            Sum.elim_inl, id, PMF.bind_bind, Sum.elim_inr]
          rfl
        · simp only [foNotBot, fixedT, hd, he, gQ, hQ, if_false, OracleAdv.run_bind,
            OracleAdv.run_query, OracleAdv.run_ret, hfOracle_inl, hfOracle_inr, PMF.bind_map,
            Function.comp_def, PMF.pure_bind, Option.getD_none,
            Sum.elim_inl, id, PMF.bind_bind, Sum.elim_inr]
          rfl

omit [Fintype R] in
theorem run_fixed_eq (P : Scheme PK SK M C R) (f : M → R) (sk : PK × SK) (s : M) (cstar : C)
    (TH : M × C → Option K) (A : OracleAdv ((M ⊕ (M × C)) ⊕ C) ((R ⊕ K) ⊕ Option K) Bool) :
    (OracleAdv.run (hfOracle f) (OracleAdv.simulate (ccaImpl P ((sk.1, sk.2), s) cstar) A ())
        (TH, ())).map (fun x => x.1.1) =
      (OracleAdv.run (romCCAOracle (uNotBot (fixedT P f)) ((sk.1, sk.2), s) cstar)
        ((OracleAdv.simulate (absImpl f) A ()).bind fun x => .ret x.1) TH).map Prod.fst := by
  have h := OracleAdv.run_map_state _ _ (fun y : Unit × ((M × C → Option K) × Unit) => ((), y.2.1))
    (fun s' d => by
      obtain ⟨u, TH', u'⟩ := s'
      exact step_eq P f sk s cstar TH' d) A ((), (TH, ()))
  rw [OracleAdv.run_simulate, OracleAdv.run_bind, OracleAdv.run_simulate, PMF.map_comp, PMF.bind_map]
  simp only [OracleAdv.run_ret, Function.comp_def]
  rw [← h, PMF.bind_map]
  simp only [PMF.map_bind, PMF.pure_map, Function.comp_def]
  rfl

/-- A run of the IND-CCA oracle of `foNotBot P` from tables `(TG, TH)` has the output
distribution of runs of the IND-CCA oracle of `uNotBot (fixedT P f)` on the absorbed
adversary, for `f` uniform and agreeing with `TG`. -/
theorem run_rom2CCA_eq_fixed (P : Scheme PK SK M C R) (sk : PK × SK) (s : M) (cstar : C)
    (A : OracleAdv ((M ⊕ (M × C)) ⊕ C) ((R ⊕ K) ⊕ Option K) Bool)
    (TG : M → Option R) (TH : M × C → Option K) :
    (OracleAdv.run (rom2CCAOracle (foNotBot P) ((sk.1, sk.2), s) cstar) A (TG, TH)).map Prod.fst =
      (extDist TG).bind fun f =>
        (OracleAdv.run (romCCAOracle (uNotBot (fixedT P f)) ((sk.1, sk.2), s) cstar)
          ((OracleAdv.simulate (absImpl f) A ()).bind fun x => .ret x.1) TH).map Prod.fst := by
  rw [run_rom2CCAOracle_eq, run_ro2_eq, PMF.map_comp]
  have h := run_simOracle_roOracle_eq (progH (C := C) (K := K))
    (OracleAdv.simulate (ccaImpl P ((sk.1, sk.2), s) cstar) A ()) TH TG
  rw [show ((fun x : (Bool × Unit) × ((M → Option R) × (M × C → Option K)) => x.1.1) ∘
      Prod.map id Prod.swap) = (fun y : (Bool × Unit) × (M × C → Option K) => y.1.1) ∘
      (fun x => (x.1, x.2.1)) from rfl, ← PMF.map_comp, h, PMF.map_bind]
  refine congrArg _ (funext fun f => ?_)
  rw [PMF.map_comp]
  exact run_fixed_eq P f sk s cstar TH A

end Fixed

/-! ## The experiment with `G` fixed -/

section Games

/-- The IND-CCA experiment of `uNotBot (fixedT P f)` against the absorbed adversary,
unfolded. -/
noncomputable def fixedGame (P : Scheme PK SK M C R) {qRO qD : ℕ}
    (B : ROM2INDCCAAdversary PK K C M R (M × C) K qRO qD) (b : Bool) (f : M → R) : PMF Bool :=
  P.keygen.bind fun ks => (PMF.uniformOfFintype M).bind fun s =>
    (PMF.uniformOfFintype M).bind fun m => (PMF.uniformOfFintype K).bind fun k₀ =>
      (PMF.uniformOfFintype K).bind fun k₁ =>
        (OracleAdv.run (romCCAOracle (uNotBot (fixedT P f)) ((ks.1, ks.2), s) (P.enc ks.1 m (f m)))
          ((absorb f B).run ks.1 (P.enc ks.1 m (f m)) (if b then k₀ else k₁))
          (Function.update emptyTable (m, P.enc ks.1 m (f m)) (some k₀))).map Prod.fst

omit [Fintype R] [Nonempty R] in
theorem uGame_eq (P : Scheme PK SK M C R) {qRO qD : ℕ}
    (B : ROM2INDCCAAdversary PK K C M R (M × C) K qRO qD) (b : Bool) (f : M → R) :
    romINDCCAGame (uNotBot (fixedT P f)) (absorb f B) b = fixedGame P B b f := by
  simp only [romINDCCAGame, uNotBot, fixedT, fixedGame, PMF.bind_bind, PMF.bind_map,
    Function.comp_def, OracleAdv.run_rand, OracleAdv.run_query, OracleAdv.run_ret, roOracle,
    emptyTable, PMF.pure_bind]
  simp only [PMF.bind_const]

theorem foGame_eq (P : Scheme PK SK M C R) {qRO qD : ℕ}
    (B : ROM2INDCCAAdversary PK K C M R (M × C) K qRO qD) (b : Bool) :
    rom2INDCCAGame (foNotBot P) B b = (PMF.uniformOfFintype (M → R)).bind (fixedGame P B b) := by
  have hk : (foNotBot (K := K) P).keygen = P.keygen.bind fun ks =>
      (PMF.uniformOfFintype M).map fun s => (ks.1, ((ks.1, ks.2), s)) := rfl
  have he : ∀ pk, (foNotBot (K := K) P).encaps pk = .rand (PMF.uniformOfFintype M) fun m =>
      (gQ m).bind fun r => (hQ (m, P.enc pk m r)).bind fun k => .ret (k, P.enc pk m r) :=
    fun _ => rfl
  have hempty : ∀ (m : M), (emptyTable : M → Option R) m = none := fun _ => rfl
  have hempty' : ∀ (q : M × C), (emptyTable : M × C → Option K) q = none := fun _ => rfl
  simp only [rom2INDCCAGame, hk, he, gQ, hQ, PMF.bind_bind, PMF.bind_map,
    Function.comp_def, OracleAdv.run_rand, OracleAdv.run_query, OracleAdv.run_ret,
    OracleAdv.run_bind, ro2Oracle, roOracle, hempty, hempty', PMF.pure_bind,
    Sum.elim_inl, Sum.elim_inr, id]
  simp only [run_rom2CCA_eq_fixed]
  rw [show (PMF.uniformOfFintype (M → R)).bind (fixedGame P B b) =
    (PMF.uniformOfFintype (M → R)).bind fun f => fixedGame P B b f from rfl]
  simp only [fixedGame]
  rw [PMF.bind_comm (PMF.uniformOfFintype (M → R)) P.keygen]
  refine congrArg _ (funext fun ks => ?_)
  rw [PMF.bind_comm (PMF.uniformOfFintype (M → R)) (PMF.uniformOfFintype M)]
  refine congrArg _ (funext fun s => ?_)
  rw [PMF.bind_comm (PMF.uniformOfFintype (M → R)) (PMF.uniformOfFintype M)]
  refine congrArg _ (funext fun m => ?_)
  have hcomm : ∀ r : R, ((PMF.uniformOfFintype K).bind fun k₀ => (PMF.uniformOfFintype K).bind
      fun k₁ => (extDist (Function.update (emptyTable : M → Option R) m (some r))).bind fun f =>
        (OracleAdv.run (romCCAOracle (uNotBot (fixedT P f)) ((ks.1, ks.2), s) (P.enc ks.1 m r))
          ((OracleAdv.simulate (absImpl f) (B.run ks.1 (P.enc ks.1 m r)
            (if b = true then k₀ else k₁)) ()).bind fun x => .ret x.1)
          (Function.update emptyTable (m, P.enc ks.1 m r) (some k₀))).map Prod.fst) =
      (extDist (Function.update (emptyTable : M → Option R) m (some r))).bind fun f =>
        (PMF.uniformOfFintype K).bind fun k₀ => (PMF.uniformOfFintype K).bind fun k₁ =>
        (OracleAdv.run (romCCAOracle (uNotBot (fixedT P f)) ((ks.1, ks.2), s) (P.enc ks.1 m r))
          ((OracleAdv.simulate (absImpl f) (B.run ks.1 (P.enc ks.1 m r)
            (if b = true then k₀ else k₁)) ()).bind fun x => .ret x.1)
          (Function.update emptyTable (m, P.enc ks.1 m r) (some k₀))).map Prod.fst := by
    intro r
    conv_lhs => arg 2; ext k₀; rw [PMF.bind_comm (PMF.uniformOfFintype K)]
    rw [PMF.bind_comm (PMF.uniformOfFintype K)]
  simp only [hcomm]
  have hp := extDist_map_pair (emptyTable : M → Option R) m rfl
  rw [extDist_empty] at hp
  have hbind := congrArg (fun p => PMF.bind p fun x : R × (M → R) =>
    (PMF.uniformOfFintype K).bind fun k₀ => (PMF.uniformOfFintype K).bind fun k₁ =>
      (OracleAdv.run (romCCAOracle (uNotBot (fixedT P x.2)) ((ks.1, ks.2), s) (P.enc ks.1 m x.1))
        ((OracleAdv.simulate (absImpl x.2) (B.run ks.1 (P.enc ks.1 m x.1)
          (if b = true then k₀ else k₁)) ()).bind fun y => .ret y.1)
        (Function.update emptyTable (m, P.enc ks.1 m x.1) (some k₀))).map Prod.fst) hp
  simp only [PMF.bind_map, PMF.bind_bind, Function.comp_def] at hbind
  exact hbind.symm

omit [Fintype R] [Nonempty R] [Fintype M] [Nonempty M] [DecidableEq M] [DecidableEq C]
  [Fintype K] [Nonempty K] in
theorem prTrue_pmfGame_true (p : PMF Bool) : prTrue (pmfGame p) Heap.empty = p true := by
  have h := prTrue_pmfGame_map p id Heap.empty
  rw [PMF.map_id] at h
  rw [h, PMF.toOuterMeasure_apply, tsum_eq_single true fun b hb => by simp [Set.indicator, hb]]
  simp [Set.indicator]

omit [Fintype R] [Nonempty R] [Fintype M] [Nonempty M] [DecidableEq M] [DecidableEq C]
  [Fintype K] [Nonempty K] in
/-- The advantage between two mixtures is at most the mixture of the advantages. -/
theorem advantage_bind_le {ι : Type} (w : PMF ι) (g₁ g₀ : ι → PMF Bool) :
    Advantage (pmfGame (w.bind g₁)) (pmfGame (w.bind g₀)) ≤
      ∑' i, w i * Advantage (pmfGame (g₁ i)) (pmfGame (g₀ i)) := by
  simp only [Advantage, prTrue_pmfGame_true, PMF.bind_apply]
  have key : ∀ (a b : ι → ℝ≥0∞), ∑' i, w i * a i - ∑' i, w i * b i ≤
      ∑' i, w i * ((a i - b i) ⊔ (b i - a i)) := by
    intro a b
    rw [tsub_le_iff_left, ← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun i => ?_
    rw [← mul_add]
    gcongr
    calc a i ≤ (a i - b i) + b i := le_tsub_add
      _ ≤ _ := by rw [add_comm]; gcongr; exact le_sup_left
  refine max_le (key _ _) ((key _ _).trans (le_of_eq (tsum_congr fun i => by rw [max_comm])))

theorem foAdvantage_le (P : Scheme PK SK M C R) {qRO qD : ℕ}
    (B : ROM2INDCCAAdversary PK K C M R (M × C) K qRO qD) :
    rom2INDCCAAdvantage (foNotBot P) B ≤ ∑' f, PMF.uniformOfFintype (M → R) f *
      romINDCCAAdvantage (uNotBot (fixedT P f)) (absorb f B) := by
  unfold rom2INDCCAAdvantage romINDCCAAdvantage
  simp only [foGame_eq, uGame_eq]
  exact advantage_bind_le _ _ _

omit [Nonempty M] [DecidableEq C] [Fintype K] [Nonempty K] in
theorem tsum_uniform_eval (m : M) (F : R → ℝ≥0∞) :
    ∑' f, PMF.uniformOfFintype (M → R) f * F (f m) = ∑' r, PMF.uniformOfFintype R r * F r := by
  have hmap : (PMF.uniformOfFintype (M → R)).map (fun f => f m) = PMF.uniformOfFintype R := by
    conv_lhs => rw [← Constructions.ECBCPRF.uniform_bind_update (D := M) (R := R) m]
    simp only [PMF.map_bind, PMF.map_comp, Function.comp_def, Function.update_self]
    rw [show (fun x : R => x) = id from rfl, PMF.map_id]
    exact PMF.bind_const _ _
  rw [← FOTransformU.tsum_map_mul, hmap]

omit [Fintype R] [Nonempty R] [Fintype M] [Nonempty M] in
theorem failProb_fixedT (P : Scheme PK SK M C R) (f : M → R) (pk : PK) (sk : SK) (m : M) :
    (fixedT P f).failProb pk (pk, sk) m =
      PKE.FOTransformT.failInd P sk m (P.enc pk m (f m)) := by
  rw [Scheme.failProb, PMF.toOuterMeasure_apply, tsum_eq_single () fun u hu => absurd rfl hu]
  simp only [fixedT, PKE.FOTransformT.failInd, Set.indicator, Set.mem_ofPred_eq,
    PMF.uniformOfFintype_apply, Fintype.card_unit, Nat.cast_one, inv_one]
  cases hd : P.dec sk (P.enc pk m (f m)) with
  | none => simp
  | some m₀ =>
    by_cases hm : m₀ = m
    · subst hm; simp
    · by_cases he : P.enc pk m₀ (f m₀) = P.enc pk m (f m) <;> simp [he, hm]

theorem corrErr_fixedT (P : Scheme PK SK M C R) :
    ∑' f, PMF.uniformOfFintype (M → R) f * (fixedT P f).corrErr = P.corrErr := by
  rw [PKE.FOTransformT.corrErr_eq]
  have h : ∀ f, (fixedT P f).corrErr = ∑' ks, P.keygen ks * ∑' m, PMF.uniformOfFintype M m *
      PKE.FOTransformT.failInd P ks.2 m (P.enc ks.1 m (f m)) := by
    intro f
    rw [PKE.Games.Scheme.corrErr, show (fixedT P f).keygen = P.keygen.map fun ks => (ks.1, (ks.1, ks.2))
      from rfl, FOTransformU.tsum_map_mul]
    simp only [failProb_fixedT]
  simp only [h]
  rw [FOTransformU.tsum_mul_comm]
  refine tsum_congr fun ks => congrArg _ ?_
  rw [FOTransformU.tsum_mul_comm]
  refine tsum_congr fun m => congrArg _ ?_
  exact tsum_uniform_eval m fun r => PKE.FOTransformT.failInd P ks.2 m (P.enc ks.1 m r)

end Games

/-! ## The OW-PCA reduction against `T[P, G]` -/

section Reduction

open CatCrypt.Crypto.KEM.FOTransformU (SimState simImpl isQueryBound_simImpl)

/-- A program with plaintext-checking queries, as a program with random-oracle and
plaintext-checking queries. -/
def liftP {α : Type} : OracleAdv (M × C) Bool α → OracleAdv (M ⊕ (M × C)) (R ⊕ Bool) α
  | .ret a => .ret a
  | .rand p k => .rand p fun b => liftP (k b)
  | .query q k => .query (.inr q) fun a => liftP (k (a.elim (fun _ => false) id))

omit [Fintype R] [Nonempty R] [Fintype M] [Nonempty M] [DecidableEq M] [DecidableEq C] in
theorem isQueryBoundBy_liftP {α : Type} (cost : M ⊕ (M × C) → ℕ) (hc : ∀ q, cost (.inr q) ≤ 1)
    {A : OracleAdv (M × C) Bool α} {n : ℕ} (hA : A.IsQueryBound n) :
    (liftP (R := R) A).IsQueryBoundBy cost n := by
  induction A generalizing n with
  | ret a => trivial
  | rand p k ih => exact fun b => ih b (hA b)
  | query q k ih =>
    cases n with
    | zero => exact hA.elim
    | succ n =>
      refine ⟨(hc q).trans (Nat.le_add_left 1 n), fun a => ?_⟩
      exact (ih _ (hA _)).mono (by have := hc q; omega)

/-- The simulation of `B`'s oracles by the OW-PCA adversary against `T[P, G]`: queries
to `G` are forwarded, queries to `H` and decapsulation queries are answered as in
`FOTransformU.simImpl`, with plaintext-checking queries forwarded. -/
noncomputable def simImplFO (cstar : C) (kstar : K) (st : SimState M C K) :
    (M ⊕ (M × C)) ⊕ C →
      OracleAdv (M ⊕ (M × C)) (R ⊕ Bool) (((R ⊕ K) ⊕ Option K) × SimState M C K)
  | .inl (.inl m) => .query (.inl m) fun a =>
      .ret (.inl (.inl (a.elim id fun _ => Classical.arbitrary R)), st)
  | .inl (.inr q) => (liftP (simImpl cstar kstar st (.inl q))).bind fun x =>
      .ret (.inl (.inr (x.1.elim id fun _ => Classical.arbitrary K)), x.2)
  | .inr c => (liftP (simImpl cstar kstar st (.inr c))).bind fun x =>
      .ret (.inr (x.1.elim (fun _ => none) id), x.2)

omit [Fintype R] [Fintype M] [Nonempty M] in
theorem isQueryBoundBy_simImplFO (cost : M ⊕ (M × C) → ℕ) (hc₁ : ∀ m, cost (.inl m) ≤ 1)
    (hc₂ : ∀ q, cost (.inr q) ≤ 1) (cstar : C) (kstar : K) (st : SimState M C K)
    (d : (M ⊕ (M × C)) ⊕ C) :
    (simImplFO (R := R) cstar kstar st d).IsQueryBoundBy cost
      (Sum.elim (fun _ => 1) (fun _ => 0) d) := by
  rcases d with (m | q) | c
  · exact ⟨hc₁ m, fun _ => trivial⟩
  · have h := OracleAdv.isQueryBoundBy_bind (isQueryBoundBy_liftP (R := R) cost hc₂
      (isQueryBound_simImpl cstar kstar st (.inl q))) (b := 0)
      (f := fun x : (K ⊕ Option K) × SimState M C K =>
        (OracleAdv.ret (.inl (.inr (x.1.elim id fun _ => Classical.arbitrary K)), x.2) :
          OracleAdv (M ⊕ (M × C)) (R ⊕ Bool) (((R ⊕ K) ⊕ Option K) × SimState M C K)))
      fun _ => trivial
    exact h
  · have h := OracleAdv.isQueryBoundBy_bind (isQueryBoundBy_liftP (R := R) cost hc₂
      (isQueryBound_simImpl cstar kstar st (.inr c))) (b := 0)
      (f := fun x : (K ⊕ Option K) × SimState M C K =>
        (OracleAdv.ret (.inr (x.1.elim (fun _ => none) id), x.2) :
          OracleAdv (M ⊕ (M × C)) (R ⊕ Bool) (((R ⊕ K) ⊕ Option K) × SimState M C K)))
      fun _ => trivial
    exact h

/-- The run of the OW-PCA adversary against `T[P, G]` built from `B`. -/
noncomputable def uRedRun {qRO qD : ℕ} (B : ROM2INDCCAAdversary PK K C M R (M × C) K qRO qD)
    (pk : PK) (c : C) : OracleAdv (M ⊕ (M × C)) (R ⊕ Bool) M :=
  .rand (PMF.uniformOfFintype K) fun kstar =>
    (OracleAdv.simulate (simImplFO c kstar) (B.run pk c kstar) SimState.init).bind
      fun x => .ret (x.2.found.getD (Classical.arbitrary M))

omit [Fintype R] [Fintype M] in
theorem isQueryBoundBy_uRedRun {qRO qD : ℕ} (B : ROM2INDCCAAdversary PK K C M R (M × C) K qRO qD)
    (cost : M ⊕ (M × C) → ℕ) (hc₁ : ∀ m, cost (.inl m) ≤ 1) (hc₂ : ∀ q, cost (.inr q) ≤ 1)
    (pk : PK) (c : C) : (uRedRun B pk c).IsQueryBoundBy cost qRO := by
  intro kstar
  have h := OracleAdv.isQueryBoundBy_bind (OracleAdv.isQueryBoundBy_simulate _ _ cost
    (isQueryBoundBy_simImplFO cost hc₁ hc₂ c kstar) (B.isQueryBoundRO pk c kstar) SimState.init)
    (b := 0) (f := fun x : Bool × SimState M C K =>
      (OracleAdv.ret (x.2.found.getD (Classical.arbitrary M)) :
        OracleAdv (M ⊕ (M × C)) (R ⊕ Bool) M)) fun _ => trivial
  simpa using h

/-- The OW-PCA adversary against `tTransform P` built from an IND-CCA adversary `B`
against `foNotBot P`. It samples a key `k*`, runs `B` once on `(pk, c*, k*)`,
forwards `B`'s queries to `G`, answers each query to `H` with one plaintext-checking
query (as `FOTransformU.uReduction` does), answers decapsulation queries from its
table, and outputs a message found to decrypt `c*`. It asks at most `qRO` queries in
total. -/
noncomputable def uRedROM {qRO qD : ℕ} (B : ROM2INDCCAAdversary PK K C M R (M × C) K qRO qD) :
    ROMOWPCAAdversary PK M C M R qRO qRO where
  run := uRedRun B
  isQueryBoundG := isQueryBoundBy_uRedRun B _ (fun _ => le_rfl) (fun _ => Nat.zero_le _)
  isQueryBoundP := isQueryBoundBy_uRedRun B _ (fun _ => Nat.zero_le _) (fun _ => le_rfl)

open CatCrypt.Crypto.PKE.FOTransformT (eO ansReal)

omit [Fintype R] [Nonempty R] [Fintype M] [Nonempty M] in
theorem ansReal_eq_pco (P : Scheme PK SK M C R) (f : M → R) (ks : PK × SK) (q : M × C) :
    ansReal P ks q (f q.1) = (fixedT P f).pco (ks.1, ks.2) q.1 q.2 := by
  obtain ⟨m, c⟩ := q
  simp only [ansReal, Scheme.pco, fixedT]
  refine decide_eq_decide.mpr ?_
  cases hd : P.dec ks.2 c with
  | none => simp
  | some m₀ =>
    by_cases hm : m₀ = m
    · subst hm; by_cases he : P.enc ks.1 m₀ (f m₀) = c <;> simp [he]
    · by_cases he : P.enc ks.1 m₀ (f m₀) = c <;> simp [he, hm]

omit [Fintype R] [Nonempty R] [Fintype M] [Nonempty M] in
theorem run_liftP {α : Type} (P : Scheme PK SK M C R) (f : M → R) (ks : PK × SK)
    (A : OracleAdv (M × C) Bool α) :
    OracleAdv.run (eO (ansReal P ks) (fun _ _ u => u) f) (liftP A) () =
      OracleAdv.run (pcoOracle (fixedT P f) (ks.1, ks.2)) A () := by
  induction A with
  | ret a => rfl
  | rand p k ih => simp only [liftP, OracleAdv.run_rand, ih]
  | query q k ih =>
    simp only [liftP, OracleAdv.run_query, eO, pcoOracle, PMF.pure_bind, Sum.elim_inr, id,
      ansReal_eq_pco]
    exact ih _

omit [Fintype R] [Fintype M] [Nonempty M] in
theorem step_red_eq (P : Scheme PK SK M C R) (f : M → R) (ks : PK × SK) (cstar : C) (kstar : K)
    (st : SimState M C K) (d : (M ⊕ (M × C)) ⊕ C) :
    OracleAdv.simOracle (simImplFO cstar kstar) (eO (ansReal P ks) (fun _ _ u => u) f) (st, ()) d =
      (OracleAdv.simOracle (absImpl f)
        (OracleAdv.simOracle (simImpl cstar kstar) (pcoOracle (fixedT P f) (ks.1, ks.2)))
          ((), (st, ())) d).map (Prod.map id fun y => (y.2.1, ())) := by
  rcases d with (m | q) | c
  · simp [OracleAdv.simOracle, simImplFO, absImpl, eO, PMF.pure_map]
  · simp only [OracleAdv.simOracle, simImplFO, absImpl, OracleAdv.run_bind, OracleAdv.run_query,
      OracleAdv.run_ret, run_liftP, PMF.map_bind, PMF.bind_map, PMF.pure_map,
      Function.comp_def]
    rfl
  · simp only [OracleAdv.simOracle, simImplFO, absImpl, OracleAdv.run_bind, OracleAdv.run_query,
      OracleAdv.run_ret, run_liftP, PMF.map_bind, PMF.bind_map, PMF.pure_map,
      Function.comp_def]
    rfl

omit [Fintype R] [Fintype M] in
theorem run_uRed_eq (P : Scheme PK SK M C R) (f : M → R) (ks : PK × SK) (c : C) {qRO qD : ℕ}
    (B : ROM2INDCCAAdversary PK K C M R (M × C) K qRO qD) :
    (OracleAdv.run (eO (ansReal P ks) (fun _ _ u => u) f) (uRedRun B ks.1 c) ()).map Prod.fst =
      (OracleAdv.run (pcoOracle (fixedT P f) (ks.1, ks.2))
        ((uReduction (absorb f B)).run ks.1 c) ()).map Prod.fst := by
  simp only [uRedRun, uReduction, absorb, OracleAdv.run_rand, PMF.map_bind]
  refine congrArg _ (funext fun kstar => ?_)
  have h := OracleAdv.run_map_state _ _ (fun y : Unit × (SimState M C K × Unit) => (y.2.1, ()))
    (fun s d => (step_red_eq P f ks c kstar s.2.1 d).symm) (B.run ks.1 c kstar)
    ((), (SimState.init, ()))
  simp only [OracleAdv.simulate_bind, OracleAdv.simulate, OracleAdv.run_bind,
    OracleAdv.run_simulate, OracleAdv.run_ret, PMF.bind_map, PMF.map_bind, PMF.pure_map,
    Function.comp_def, PMF.bind_bind, PMF.pure_bind]
  rw [← h]
  simp only [PMF.bind_map, Function.comp_def]
  rfl

/-- The success of the OW-PCA experiment of `uReduction (absorb f B)` against
`fixedT P f`, for a key pair and challenge message. -/
noncomputable def owpcaInner (P : Scheme PK SK M C R) {qRO qD : ℕ}
    (B : ROM2INDCCAAdversary PK K C M R (M × C) K qRO qD) (ks : PK × SK) (m : M) (f : M → R) :
    PMF Bool :=
  (OracleAdv.run (pcoOracle (fixedT P f) (ks.1, ks.2))
    ((uReduction (absorb f B)).run ks.1 (P.enc ks.1 m (f m))) ()).map fun x =>
      (fixedT P f).pco (ks.1, ks.2) x.1 (P.enc ks.1 m (f m))

omit [Fintype R] [Nonempty R] in
theorem owpcaGame_fixedT (P : Scheme PK SK M C R) {qRO qD : ℕ}
    (B : ROM2INDCCAAdversary PK K C M R (M × C) K qRO qD) (f : M → R) :
    owpcaGame (fixedT P f) (uReduction (absorb f B)) = P.keygen.bind fun ks =>
      (PMF.uniformOfFintype M).bind fun m => owpcaInner P B ks m f := by
  simp only [owpcaGame, Scheme.encDist, PMF.bind_map, Function.comp_def, owpcaInner]
  rw [show (fixedT P f).keygen = P.keygen.map fun ks => (ks.1, (ks.1, ks.2)) from rfl, PMF.bind_map]
  have hU : PMF.uniformOfFintype Unit = PMF.pure () := by ext u; simp
  simp only [Function.comp_def, hU, PMF.pure_bind]
  rfl

theorem romOWPCAGame_uRedROM (P : Scheme PK SK M C R) {qRO qD : ℕ}
    (B : ROM2INDCCAAdversary PK K C M R (M × C) K qRO qD) :
    romOWPCAGame (tTransform P) (uRedROM B) = P.keygen.bind fun ks =>
      (PMF.uniformOfFintype M).bind fun m => (PMF.uniformOfFintype (M → R)).bind fun f =>
        owpcaInner P B ks m f := by
  rw [PKE.FOTransformT.romOWPCAGame_eq]
  refine congrArg _ (funext fun ks => congrArg _ (funext fun m => ?_))
  rw [PKE.FOTransformT.game_eq_eager]
  refine congrArg _ (funext fun f => ?_)
  simp only [PKE.FOTransformT.withCheck, OracleAdv.run_bind, OracleAdv.run_query, OracleAdv.run_ret,
    eO, PMF.pure_bind, PMF.map_bind, PMF.pure_map, Sum.elim_inr, id]
  have h := run_uRed_eq P f ks (P.enc ks.1 m (f m)) B
  have hans : ∀ (m' : M) (c' : C), ansReal P ks (m', c') (f m') = (fixedT P f).pco (ks.1, ks.2) m' c' :=
    fun m' c' => ansReal_eq_pco P f ks (m', c')
  have h2 := congrArg (PMF.map fun m' => (fixedT P f).pco (ks.1, ks.2) m' (P.enc ks.1 m (f m))) h
  simp only [PMF.map_comp, Function.comp_def] at h2
  unfold owpcaInner
  simp only [hans]
  rw [← h2, PMF.map]
  rfl

theorem owpca_eq (P : Scheme PK SK M C R) {qRO qD : ℕ}
    (B : ROM2INDCCAAdversary PK K C M R (M × C) K qRO qD) :
    romOWPCAAdvantage (tTransform P) (uRedROM B) =
      ∑' f, PMF.uniformOfFintype (M → R) f * owpcaAdvantage (fixedT P f) (uReduction (absorb f B)) := by
  simp only [romOWPCAAdvantage, owpcaAdvantage, PKE.FOTransformT.prTrue_pmfGame_eq,
    romOWPCAGame_uRedROM, owpcaGame_fixedT]
  rw [← PMF.toOuterMeasure_bind_apply, PMF.bind_comm (PMF.uniformOfFintype (M → R)) P.keygen]
  refine congrArg (fun p : PMF Bool => p.toOuterMeasure _) (congrArg _ (funext fun ks => ?_))
  exact (PMF.bind_comm _ _ _).symm

end Reduction

/-! ## The theorem -/

/-- **FO⊥̸ is IND-CCA secure in the random-oracle model** (Hofheinz–Hövelmanns–Kiltz,
Theorems 3.1 and 3.4 composed). For every public-key encryption scheme `P` and every
IND-CCA adversary `B` against `foNotBot P` asking at most `qRO` queries to the random
oracles `G` and `H` together,

`rom2INDCCAAdvantage (foNotBot P) B ≤ owcpaAdvantage P (tReductionC P (uRedROM B)) +
  (qRO + 1)·δ + P.corrErr + (qRO + 1)·owcpaAdvantage P (tReductionD P (uRedROM B) qRO) +
  qRO/|M| + P.corrErr`

with `δ = P.corrWorst` the correctness error and `P.corrErr ≤ δ`. The reductions are
explicit: `uRedROM B` runs `B` once and asks at most `qRO` queries; `tReductionC` and
`tReductionD` run it once with a lazily sampled `G` and re-encryption answers. The
advantage is the distance between the real-key and random-key experiments. The
statement is in the classical random-oracle model; it says nothing about quantum
adversaries with superposition access to `G` and `H`. -/
theorem foNotBot_indcca (P : Scheme PK SK M C R) {qRO qD : ℕ}
    (B : ROM2INDCCAAdversary PK K C M R (M × C) K qRO qD) :
    rom2INDCCAAdvantage (foNotBot P) B ≤
      owcpaAdvantage P (tReductionC P (uRedROM B)) + ((qRO + 1 : ℕ) : ℝ≥0∞) * P.corrWorst +
        P.corrErr + ((qRO + 1 : ℕ) : ℝ≥0∞) * owcpaAdvantage P (tReductionD P (uRedROM B) qRO) +
        (qRO : ℝ≥0∞) / Fintype.card M + P.corrErr := by
  have hB : ∀ pk c, ((uRedROM B).run pk c).IsQueryBoundBy (fun _ => 1) qRO :=
    isQueryBoundBy_uRedRun B _ (fun _ => le_rfl) (fun _ => le_rfl)
  calc rom2INDCCAAdvantage (foNotBot P) B
      ≤ ∑' f, PMF.uniformOfFintype (M → R) f *
          romINDCCAAdvantage (uNotBot (fixedT P f)) (absorb f B) := foAdvantage_le P B
    _ ≤ ∑' f, PMF.uniformOfFintype (M → R) f *
          (owpcaAdvantage (fixedT P f) (uReduction (absorb f B)) +
            (qRO : ℝ≥0∞) / Fintype.card M + (fixedT P f).corrErr) :=
        ENNReal.tsum_le_tsum fun f => mul_le_mul_right (uNotBot_indcca (fixedT P f) (absorb f B)) _
    _ = romOWPCAAdvantage (tTransform P) (uRedROM B) + (qRO : ℝ≥0∞) / Fintype.card M +
          P.corrErr := by
        simp only [mul_add, ENNReal.tsum_add, ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul,
          owpca_eq, corrErr_fixedT]
    _ ≤ _ := by
        gcongr
        exact tTransform_owpca_of_total P (uRedROM B) qRO hB

/-- **FO⊥̸ is IND-CCA secure from IND-CPA in the random-oracle model.** For every
public-key encryption scheme `P` and every IND-CCA adversary `B` against `foNotBot P`
asking at most `qRO` random-oracle queries, with `C' = tReductionC P (uRedROM B)`
and `D' = tReductionD P (uRedROM B) qRO`,

`rom2INDCCAAdvantage (foNotBot P) B ≤
  (indcpaAdvantage P (owToIndcpa C') + 1/|M| + P.corrErr) + (qRO + 1)·δ + P.corrErr +
  (qRO + 1)·(indcpaAdvantage P (owToIndcpa D') + 1/|M| + P.corrErr) + qRO/|M| + P.corrErr`.

The IND-CPA advantage is the distance between the two challenge bits. -/
theorem foNotBot_indcca_of_indcpa (P : Scheme PK SK M C R) {qRO qD : ℕ}
    (B : ROM2INDCCAAdversary PK K C M R (M × C) K qRO qD) :
    rom2INDCCAAdvantage (foNotBot P) B ≤
      (indcpaAdvantage P (owToIndcpa (tReductionC P (uRedROM B))) +
          (Fintype.card M : ℝ≥0∞)⁻¹ + P.corrErr) +
        ((qRO + 1 : ℕ) : ℝ≥0∞) * P.corrWorst + P.corrErr +
        ((qRO + 1 : ℕ) : ℝ≥0∞) * (indcpaAdvantage P (owToIndcpa (tReductionD P (uRedROM B) qRO)) +
          (Fintype.card M : ℝ≥0∞)⁻¹ + P.corrErr) +
        (qRO : ℝ≥0∞) / Fintype.card M + P.corrErr := by
  refine (foNotBot_indcca P B).trans ?_
  gcongr
  · exact owcpa_le_indcpa P _
  · exact owcpa_le_indcpa P _

end CatCrypt.Crypto.KEM.FOTransform
