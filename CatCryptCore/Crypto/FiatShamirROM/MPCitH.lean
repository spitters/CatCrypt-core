/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.FiatShamirROM.StraightLineCls
public import CatCryptCore.Crypto.FiatShamirROM.Timed
public import CatCryptCore.Core.SPTreeTimedOps
public import CatCryptCore.Crypto.FiatShamirROM.Verification
public import CatCryptCore.Crypto.UCConcrete
public import CatCryptCore.Crypto.NomPkgBridge
public import CatCryptCore.ForMathlib.PMFUniform

/-!
# MPC-in-the-head signatures in the random-oracle model

The Fiat–Shamir signatures of an MPC-in-the-head proof with all-but-one opening (Ishai,
Kushilevitz, Ostrovsky, Sahai, STOC 2007; Katz, Kolesnikov, Wang, CCS 2018), as an
instance `Params.protocol` of `FiatShamirROM.Protocol`, and their EUF-CMA security in the
random-oracle model from the one-wayness of the key map, by straight-line extraction
from the random-oracle log.

An MPC decomposition (`Decomp`) of a map `F : X → Y` with `K + 1` parties computes the
views of the parties of one repetition from the preimage `x` and a uniform tape;
`check y c a` is the verifier's test on the views `a i` of the opened parties
`c.succAbove i` (all parties except `c`), including the reconstruction of the output
`y`; `recon y v` reconstructs a preimage from the views of all parties; `sim y c`
simulates the views of the opened parties. Its properties are correctness
(`Decomp.Correct`), `(K + 1)`-special soundness (`Decomp.Sound`: views of all parties
every `K` of which pass the test reconstruct a preimage) and perfect `K`-privacy
(`Decomp.Private`). Key generation samples the preimage from the distribution
`Decomp.gen`, and the one-wayness game (`Decomp.owfGame`) is the game of `F` over it.

A signing attempt on `m` for `(y, x)` with `y = F x` runs `T` repetitions. The party `p`
of repetition `j` has a uniform salt `salt (j, p)`; its commitment is the random-oracle
value at the point `(j, p, salt (j, p), view)`. The challenge is the random-oracle value
at `(y, m, C)`, where `C j p` is the digest of the commitment of the party `p` of
repetition `j`. The random oracle answers every point with a value in
`Dig × (Fin T → Fin (K + 1))`; a commitment reads the digest and the challenge reads the
vector of hidden parties. The attempt has `T(K + 1) + 1` entries, all programmed: the
commitment entries of the opened parties and the challenge entry are public, the
commitment entry of the hidden party `c_j` is hidden. The signature carries the
challenge vector, the opened salts and views and the digest of the hidden commitment of
each repetition. The verifier reads the points of the `TK` opened commitments and the
challenge point, and checks the challenge vector and the opened views.

The straight-line extractor reads, for the digests `C` of the forgery's challenge point,
the committed views of all parties of each repetition from the random-oracle log and
reconstructs a preimage from views every `K` of which pass the test. A fresh commitment
digest is bad when it is a digest already present in the log, and a fresh challenge
vector is bad when, without consistent committed views of all parties, each of its
components can be answered; since a repetition without such views has a hidden party
that cannot be answered, a uniform challenge vector is bad with probability at most
`(K/(K + 1))^T`.

## Main definitions

* `Decomp` — an MPC decomposition with all-but-one opening, with `Decomp.Correct`,
  `Decomp.Sound`, `Decomp.Private`, and the one-wayness game `Decomp.owfGame` and
  advantage `Decomp.owfAdvantage` of `F`
* `Params` — the decomposition, the number of repetitions `T`, salts and digests
* `Params.protocol` — the Fiat–Shamir protocol of the MPC-in-the-head proof
* `Params.classes`, `Params.gammaCls` — the commitment and challenge key classes and the
  class-wise key bound `(T(K + 1)·2/|Salt|, 1/|Dig|)`
* `Params.Bad`, `Params.epsCls`, `Params.ext`, `Params.logExtractor` — the bad answers,
  their bounds `((T(K + 1) + 1)·N/|Dig|, (K/(K + 1))^T)`, the extractor and the class-wise
  log extractor
* `Params.inverter` — the inverter: one run of the instrumented simulated game and the
  extractor
* `Params.logExtractor.timed`, `Params.inverter.timed` — the costed extractor (one step of
  cost `tExt`) and the costed inverter (the costed verified run of `FiatShamirROM/Timed.lean`)
* `Params.statTerm` — the statistical terms of the bound
* `forgeReal`, `forgeIdeal` — the verification games of a forger of a Fiat–Shamir
  protocol: its EUF-CMA game, and the game that rejects every forgery

## Main results

* `Params.verify_honest`, `Params.vkey_honest` — completeness
* `Params.statHVZKAt` — statistical HVZK with distance `0` from perfect `K`-privacy
* `Params.keyBoundClsAt` — the class-wise key bound
* `Params.inv_of_reach`, `Params.ext_sound` — the invariant of the reachable states of
  the instrumented game and the soundness of the extractor
* `Params.eufcma_le_raw` — `fiatShamir_rom_eufcma_slCls` instantiated
* `Params.eufcma_le` — for every forger `A`,
  `eufcmaAdvantage A ≤ owfAdvantage F (inverter A) + statTerm qH qS`
* `Params.logExtractor.erase_timed`, `Params.inverter.run_erase_timed` — the costed forms
  erase to the extractor and the inverter
* `Params.logExtractor.timeBound_timed`, `Params.inverter.timeBound_timed` — their times:
  `tExt`, and `T + (tV + V(tV + 1)) + ((tH + 1)(qH + V) + (tS + 1)qS) + tOut` for a
  costed forger of time `T`

A distinguisher on the verification games has advantage at most the EUF-CMA advantage
(`FiatShamirROM.advantageA_eufcmaGame_le`, in `FiatShamirROM/Verification.lean`).

## References

* Y. Ishai, E. Kushilevitz, R. Ostrovsky, A. Sahai, *Zero-knowledge from secure
  multiparty computation*, STOC 2007.
* J. Katz, V. Kolesnikov, X. Wang, *Improved non-interactive zero knowledge with
  applications to post-quantum signatures*, CCS 2018.
* M. Chase, D. Derler, S. Goldfeder, C. Orlandi, S. Ramacher, C. Rechberger,
  D. Slamanig, G. Zaverucha, *Post-quantum zero-knowledge and signatures from
  symmetric-key primitives*, CCS 2017.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.FiatShamirROM.MPCitH

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.FiatShamirROM
open CatCrypt.Crypto.OracleForking
open scoped ENNReal

/-! ## Uniform distributions on products and function spaces -/

export PMF (uniform_prod_eq_bind map_some_apply bind_map_true_le)
open PMF (tsum_mul_comp_eq_map map_uniform_prod_fst_congr tsum_bind_mul map_uniform_apply
  map_uniform_pi_apply map_uniform_pi_congr tsum_map_guess_le uniform_prod_fst_apply
  uniform_prod_snd_apply uniform_mem_list_le uniform_box_le)

/-! ## MPC decompositions with all-but-one opening -/

/-- An MPC decomposition of a map `F : X → Y` with `K + 1` parties and all-but-one
opening: the key distribution, the views of the parties of one repetition from the
preimage and a uniform tape, the verifier's test on the views of the opened parties
`c.succAbove i` for the hidden party `c`, the reconstruction of a preimage from the
views of all parties, and the simulator of the opened views. -/
structure Decomp : Type 1 where
  /-- Preimages (secret keys). -/
  X : Type
  /-- Images (public keys). -/
  Y : Type
  [neX : Nonempty X]
  [decY : DecidableEq Y]
  /-- The key distribution of the preimage. -/
  gen : PMF X
  /-- The map. -/
  F : X → Y
  /-- The number of opened parties; the parties are `Fin (K + 1)`. -/
  K : ℕ
  /-- Views of a party. -/
  View : Type
  [decView : DecidableEq View]
  /-- Tapes of one repetition. -/
  Tape : Type
  [finTape : Fintype Tape]
  [neTape : Nonempty Tape]
  /-- Simulator tapes of one repetition. -/
  SimTape : Type
  [finSimTape : Fintype SimTape]
  [neSimTape : Nonempty SimTape]
  /-- The views of the parties from the preimage and the tape. -/
  views : X → Tape → Fin (K + 1) → View
  /-- The verifier's test, for the image and the hidden party `c`, on the views of the
  opened parties `c.succAbove i`. -/
  check : Y → Fin (K + 1) → (Fin K → View) → Bool
  /-- The reconstruction of a preimage from the views of all parties. -/
  recon : Y → (Fin (K + 1) → View) → X
  /-- The simulated views of the opened parties `c.succAbove i` for the image. -/
  sim : Y → Fin (K + 1) → SimTape → Fin K → View

namespace Decomp

/-- The one-wayness game of `D.F` against an inverter `B`: sample a preimage `x` from the
key distribution, run `B` on `D.F x`, and check that its output is a preimage of
`D.F x`. -/
noncomputable def owfGame (D : Decomp) [DecidableEq D.Y] (B : D.Y → PMF D.X) : SPComp Bool :=
  liftPMF (D.gen.bind fun x => (B (D.F x)).map fun x' => decide (D.F x' = D.F x))

/-- The one-wayness advantage of the inverter `B` against `D.F`. -/
noncomputable def owfAdvantage (D : Decomp) [DecidableEq D.Y] (B : D.Y → PMF D.X) : ℝ≥0∞ :=
  prTrue (D.owfGame B) Heap.empty

end Decomp

attribute [instance] Decomp.neX Decomp.decY Decomp.decView Decomp.finTape Decomp.neTape
  Decomp.finSimTape Decomp.neSimTape

namespace Decomp

variable (D : Decomp)

/-- **Correctness.** For every hidden party, the honest views of the opened parties pass
the test for the image of the preimage. -/
def Correct : Prop :=
  ∀ x t c, D.check (D.F x) c (fun i => D.views x t (c.succAbove i)) = true

/-- **`(K + 1)`-special soundness.** Views of all parties whose opened views pass the
test for `y` for every hidden party reconstruct a preimage of `y`. -/
def Sound : Prop :=
  ∀ y (v : Fin (D.K + 1) → D.View), (∀ c, D.check y c (fun i => v (c.succAbove i)) = true) →
    D.F (D.recon y v) = y

/-- **Perfect `K`-privacy.** For every preimage `x` and hidden party `c`, the honest views
of the opened parties on a uniform tape have the distribution of the simulated views for
`F x` on a uniform simulator tape. -/
def Private : Prop :=
  ∀ x c, (PMF.uniformOfFintype D.Tape).map (fun t i => D.views x t (c.succAbove i)) =
    (PMF.uniformOfFintype D.SimTape).map (D.sim (D.F x) c)

end Decomp

/-! ## Parameters and the protocol -/

/-- The parameters of the MPC-in-the-head signature: a decomposition, the number of
repetitions, the salts of the commitments and the digests. -/
structure Params : Type 1 where
  /-- The decomposition. -/
  D : Decomp
  /-- The number of parallel repetitions. -/
  T : ℕ
  /-- Commitment salts. -/
  Salt : Type
  /-- Commitment digests. -/
  Dig : Type
  [finSalt : Fintype Salt]
  [neSalt : Nonempty Salt]
  [decSalt : DecidableEq Salt]
  [finDig : Fintype Dig]
  [neDig : Nonempty Dig]
  [decDig : DecidableEq Dig]

attribute [instance] Params.finSalt Params.neSalt Params.decSalt Params.finDig Params.neDig
  Params.decDig

namespace Params

variable (P : Params) (M : Type) [DecidableEq M]

/-- Random-oracle values: a digest and a vector of hidden parties. -/
abbrev Ch := P.Dig × (Fin P.T → Fin (P.D.K + 1))

/-- Commitment points: repetition, party, salt and view. -/
abbrev CKey := Fin P.T × Fin (P.D.K + 1) × P.Salt × P.D.View

/-- Random-oracle points: commitment points and challenge points `(y, m, C)`. -/
abbrev Key := P.CKey ⊕ (P.D.Y × M × (Fin P.T → Fin (P.D.K + 1) → P.Dig))

instance : DecidableEq P.D.View := P.D.decView
instance : DecidableEq P.D.Y := P.D.decY

instance : DecidableEq (P.D.Y × M × (Fin P.T → Fin (P.D.K + 1) → P.Dig)) := inferInstance

instance : DecidableEq (P.Key M) := @instDecidableEqSum _ _ inferInstance inferInstance

/-- The opened salts and views of one repetition, indexed by the opened parties. -/
abbrev Opened := Fin P.D.K → P.Salt × P.D.View

/-- Signatures: the challenge vector, and for each repetition the opened salts and
views and the digest of the hidden commitment. -/
abbrev Sig := (Fin P.T → Fin (P.D.K + 1)) × (Fin P.T → P.Opened × P.Dig)

/-- Signing randomness: the tapes of the repetitions and the salts of the parties. -/
abbrev Rand := (Fin P.T → P.D.Tape) × (Fin P.T × Fin (P.D.K + 1) → P.Salt)

/-- Simulator randomness: the simulator tapes and the salts. -/
abbrev SimRand := (Fin P.T → P.D.SimTape) × (Fin P.T × Fin (P.D.K + 1) → P.Salt)

/-- A fixed view. -/
noncomputable def dView : P.D.View :=
  P.D.views (Classical.arbitrary _) (Classical.arbitrary _) 0

/-- A fixed salt and view, the entry of the hidden party in a reconstruction from opened
data. -/
noncomputable def dflt : P.Salt × P.D.View := (Classical.arbitrary _, P.dView)

/-- The commitment `(j, p)` of an entry, or nothing for the challenge entry. -/
def kind : Fin (P.T * (P.D.K + 1) + 1) → Option (Fin P.T × Fin (P.D.K + 1)) :=
  Fin.lastCases none fun i => some (finProdFinEquiv.symm i)

/-- The entry of the commitment of the party `p` of repetition `j`. -/
def cIdx (j : Fin P.T) (p : Fin (P.D.K + 1)) : Fin (P.T * (P.D.K + 1) + 1) :=
  (finProdFinEquiv (j, p)).castSucc

@[simp] theorem kind_last : P.kind (Fin.last _) = none := by
  simp [kind]

@[simp] theorem kind_cIdx (j : Fin P.T) (p : Fin (P.D.K + 1)) :
    P.kind (P.cIdx j p) = some (j, p) := by
  unfold kind cIdx
  rw [Fin.lastCases_castSucc, Equiv.symm_apply_apply]

theorem cIdx_lt_last (j : Fin P.T) (p : Fin (P.D.K + 1)) : P.cIdx j p < Fin.last _ :=
  Fin.castSucc_lt_last _

theorem cIdx_ne_last (j : Fin P.T) (p : Fin (P.D.K + 1)) : P.cIdx j p ≠ Fin.last _ :=
  (P.cIdx_lt_last j p).ne

theorem eq_of_kind_eq {i i' : Fin (P.T * (P.D.K + 1) + 1)} (h : P.kind i = P.kind i') :
    i = i' := by
  induction i using Fin.lastCases with
  | last =>
    induction i' using Fin.lastCases with
    | last => rfl
    | cast i' => simp [kind] at h
  | cast i =>
    induction i' using Fin.lastCases with
    | last => simp [kind] at h
    | cast i' =>
      simp only [kind, Fin.lastCases_castSucc, Option.some.injEq] at h
      rw [finProdFinEquiv.symm.injective h]

theorem kind_eq_some {i : Fin (P.T * (P.D.K + 1) + 1)} {j : Fin P.T} {p : Fin (P.D.K + 1)}
    (h : P.kind i = some (j, p)) : i = P.cIdx j p :=
  P.eq_of_kind_eq (by rw [h, kind_cIdx])

theorem kind_eq_none {i : Fin (P.T * (P.D.K + 1) + 1)} (h : P.kind i = none) :
    i = Fin.last _ :=
  P.eq_of_kind_eq (by rw [h, kind_last])

/-- The challenge vector of the values of an attempt. -/
def chalOf (v : Fin (P.T * (P.D.K + 1) + 1) → P.Ch) : Fin P.T → Fin (P.D.K + 1) :=
  (v (Fin.last _)).2

/-- The digests of the commitments of the values of an attempt. -/
def digMat (v : Fin (P.T * (P.D.K + 1) + 1) → P.Ch) : Fin P.T → Fin (P.D.K + 1) → P.Dig :=
  fun j p => (v (P.cIdx j p)).1

/-- The entry `i` is public: a commitment of an opened party, or the challenge. -/
def pubOf (v : Fin (P.T * (P.D.K + 1) + 1) → P.Ch) (i : Fin (P.T * (P.D.K + 1) + 1)) :
    Bool :=
  match P.kind i with
  | some (j, p) => decide (p ≠ P.chalOf v j)
  | none => true

/-- The point of the entry `i` for the image `y`, the message `m`, the salts and views
`vf` and the values `v`. -/
def keyOf (y : P.D.Y) (m : M) (vf : Fin P.T → Fin (P.D.K + 1) → P.Salt × P.D.View)
    (v : Fin (P.T * (P.D.K + 1) + 1) → P.Ch) (i : Fin (P.T * (P.D.K + 1) + 1)) : P.Key M :=
  match P.kind i with
  | some (j, p) => .inl (j, p, (vf j p).1, (vf j p).2)
  | none => .inr (y, m, P.digMat v)

/-- The signature for the values `v` and the salts and views `vf`. -/
def sigOf (v : Fin (P.T * (P.D.K + 1) + 1) → P.Ch)
    (vf : Fin P.T → Fin (P.D.K + 1) → P.Salt × P.D.View) : P.Sig :=
  (P.chalOf v, fun j => (fun i => vf j ((P.chalOf v j).succAbove i),
    P.digMat v j (P.chalOf v j)))

/-- The honest salts and views for the preimage `w` and the randomness `r`. -/
def vfR (w : P.D.X) (r : P.Rand) : Fin P.T → Fin (P.D.K + 1) → P.Salt × P.D.View :=
  fun j p => (r.2 (j, p), P.D.views w (r.1 j) p)

/-- The simulated salts and views for the challenge vector `c`: the simulated views at the
opened parties and the fixed view at the hidden party. -/
noncomputable def vfS (y : P.D.Y) (c : Fin P.T → Fin (P.D.K + 1)) (s : P.SimRand) :
    Fin P.T → Fin (P.D.K + 1) → P.Salt × P.D.View :=
  fun j p => (s.2 (j, p),
    Fin.insertNth (α := fun _ => P.D.View) (c j) P.dView (P.D.sim y (c j) (s.1 j)) p)

/-- The position of the opened commitment `(j, i)` among the values the verifier reads. -/
def oIdx (j : Fin P.T) (i : Fin P.D.K) : ℕ := (finProdFinEquiv (j, i)).val

theorem oIdx_lt (j : Fin P.T) (i : Fin P.D.K) : P.oIdx j i < P.T * P.D.K :=
  (finProdFinEquiv (j, i)).isLt

/-- The digests of the commitments that the verifier reads for the signature `σ` from
the values `vs`: the read digests at the opened parties and the hidden digest of the
signature at the hidden party. -/
def vmat (σ : P.Sig) (vs : List P.Ch) : Fin P.T → Fin (P.D.K + 1) → P.Dig := fun j =>
  Fin.insertNth (α := fun _ => P.Dig) (σ.1 j) (σ.2 j).2
    (fun i => ((vs[P.oIdx j i]?).map Prod.fst).getD (σ.2 j).2)

/-- The next point the verifier reads after the values `vs`: the commitments of the
opened parties, in the order of `finProdFinEquiv`, and the challenge point. -/
def vkey (y : P.D.Y) (m : M) (σ : P.Sig) (vs : List P.Ch) : P.Key M :=
  if h : vs.length < P.T * P.D.K then
    .inl ((finProdFinEquiv.symm ⟨vs.length, h⟩).1,
      (σ.1 (finProdFinEquiv.symm ⟨vs.length, h⟩).1).succAbove
        (finProdFinEquiv.symm ⟨vs.length, h⟩).2,
      ((σ.2 (finProdFinEquiv.symm ⟨vs.length, h⟩).1).1
        (finProdFinEquiv.symm ⟨vs.length, h⟩).2).1,
      ((σ.2 (finProdFinEquiv.symm ⟨vs.length, h⟩).1).1
        (finProdFinEquiv.symm ⟨vs.length, h⟩).2).2)
  else .inr (y, m, P.vmat σ vs)

/-- The verifier on the values read: the challenge value carries the challenge vector
of the signature, and the opened views of every repetition pass the test. -/
def verify (y : P.D.Y) (σ : P.Sig) (vs : List P.Ch) : Bool :=
  (match vs[P.T * P.D.K]? with
    | some c => decide (c.2 = σ.1)
    | none => false) &&
    decide (∀ j, P.D.check y (σ.1 j) (fun i => ((σ.2 j).1 i).2) = true)

/-- **The Fiat–Shamir protocol of the MPC-in-the-head proof.** Key generation samples a
preimage `x` from the key distribution and outputs `(F x, x)`. An attempt has the
`T(K + 1)` commitment entries and the challenge entry, all programmed; the simulator
answers the challenge vector of the values with the simulated views of the opened
parties. -/
@[reducible] noncomputable def protocol : Protocol where
  Stmt := P.D.Y
  Wit := P.D.X
  Msg := M
  Key := P.Key M
  Ch := P.Ch
  Sig := P.Sig
  Rand := P.Rand
  SimRand := P.SimRand
  gen := P.D.gen.map fun x => (P.D.F x, x)
  μ := P.T * (P.D.K + 1) + 1
  key x w m r v i := P.keyOf M x m (P.vfR w r) v i
  key_causal x w m r v v' i h := by
    induction i using Fin.lastCases with
    | last =>
      have hd : P.digMat v = P.digMat v' := funext fun j => funext fun p => by
        simp only [digMat]; rw [h _ (P.cIdx_lt_last j p)]
      simp only [keyOf, kind_last, hd]
    | cast i => simp [keyOf, kind]
  key_inj x w m r v i i' h := by
    apply P.eq_of_kind_eq
    unfold keyOf at h
    cases hi : P.kind i <;> cases hi' : P.kind i' <;> simp_all [Prod.ext_iff]
  pub _ _ _ _ v i := P.pubOf v i
  sign _ w _ r v := some (P.sigOf v (P.vfR w r))
  simulate y m v s :=
    (((List.finRange (P.T * (P.D.K + 1) + 1)).filter (P.pubOf v)).map fun i =>
        (P.keyOf M y m (P.vfS y (P.chalOf v) s) v i, v i),
      some (P.sigOf v (P.vfS y (P.chalOf v) s)))
  V := P.T * P.D.K + 1
  vkey := P.vkey M
  verify y _ σ vs := P.verify y σ vs

/-! ## Completeness -/

/-- The values that the verifier reads for an honest attempt with the values `v`: the
values of the commitments of the opened parties, then the value of the challenge. -/
def honestVals (v : Fin (P.T * (P.D.K + 1) + 1) → P.Ch) : List P.Ch :=
  List.ofFn (fun q : Fin (P.T * P.D.K) => v (P.cIdx (finProdFinEquiv.symm q).1
    ((P.chalOf v (finProdFinEquiv.symm q).1).succAbove (finProdFinEquiv.symm q).2))) ++
    [v (Fin.last _)]

omit [DecidableEq M] in
/-- The points that the verifier reads for an honest signature are the points of the
public entries of the attempt: the opened commitments, then the challenge point. -/
theorem vkey_honest (x : P.D.Y) (w : P.D.X) (m : M) (r : P.Rand)
    (v : Fin (P.T * (P.D.K + 1) + 1) → P.Ch) (k : ℕ) (hk : k < P.T * P.D.K + 1) :
    P.vkey M x m (P.sigOf v (P.vfR w r)) ((P.honestVals v).take k) =
      P.keyOf M x m (P.vfR w r) v
        (if h : k < P.T * P.D.K then P.cIdx (finProdFinEquiv.symm ⟨k, h⟩).1
          ((P.chalOf v (finProdFinEquiv.symm ⟨k, h⟩).1).succAbove
            (finProdFinEquiv.symm ⟨k, h⟩).2)
        else Fin.last _) := by
  have hlen : ((P.honestVals v).take k).length = k := by
    simp [honestVals]; omega
  unfold vkey
  rw [hlen]
  split_ifs with h1
  · simp [keyOf, sigOf, vfR]
  · simp only [keyOf, kind_last, Sum.inr.injEq, Prod.mk.injEq, true_and]
    have hk' : k = P.T * P.D.K := by omega
    subst hk'
    funext j p
    rcases eq_or_ne p (P.chalOf v j) with rfl | hp
    · simp [vmat, sigOf, Fin.insertNth_apply_same]
    · obtain ⟨i, rfl⟩ := Fin.exists_succAbove_eq hp
      have hi : (List.take (P.T * P.D.K) (P.honestVals v))[P.oIdx j i]? =
          some (v (P.cIdx j ((P.chalOf v j).succAbove i))) := by
        rw [honestVals, List.take_left' (by simp), List.getElem?_ofFn,
          dif_pos (P.oIdx_lt j i)]
        simp only [oIdx, Fin.eta, Equiv.symm_apply_apply]
      simp only [vmat, sigOf, Fin.insertNth_apply_succAbove, hi]
      rfl

/-- **Completeness.** For a correct decomposition, the verifier accepts an honest
signature on the values of the points it reads. -/
theorem verify_honest (hC : P.D.Correct) (w : P.D.X) (r : P.Rand)
    (v : Fin (P.T * (P.D.K + 1) + 1) → P.Ch) :
    P.verify (P.D.F w) (P.sigOf v (P.vfR w r)) (P.honestVals v) = true := by
  have hlast : (P.honestVals v)[P.T * P.D.K]? = some (v (Fin.last _)) := by
    simp [honestVals]
  simp only [verify, hlast, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨rfl, fun j => hC w (r.1 j) (P.chalOf v j)⟩

/-! ## Statistical HVZK -/

/-- The opened salts and views of the salts and views `vf` for the challenge vector
`c`. -/
def openOf (vf : Fin P.T → Fin (P.D.K + 1) → P.Salt × P.D.View)
    (c : Fin P.T → Fin (P.D.K + 1)) : Fin P.T → P.Opened :=
  fun j i => vf j ((c j).succAbove i)

/-- The salts and views of the opened parties from the opened data `o`, with the fixed
entry at the hidden party. -/
noncomputable def vfO (c : Fin P.T → Fin (P.D.K + 1)) (o : Fin P.T → P.Opened) :
    Fin P.T → Fin (P.D.K + 1) → P.Salt × P.D.View :=
  fun j => Fin.insertNth (α := fun _ => P.Salt × P.D.View) (c j) P.dflt (o j)

omit [DecidableEq M] in
theorem keyOf_of_pub {y : P.D.Y} {m : M}
    (vf : Fin P.T → Fin (P.D.K + 1) → P.Salt × P.D.View)
    {v : Fin (P.T * (P.D.K + 1) + 1) → P.Ch} {i : Fin (P.T * (P.D.K + 1) + 1)}
    (h : P.pubOf v i = true) :
    P.keyOf M y m vf v i =
      P.keyOf M y m (P.vfO (P.chalOf v) (P.openOf vf (P.chalOf v))) v i := by
  unfold pubOf at h
  unfold keyOf
  split
  · next j p hk =>
    rw [hk] at h
    simp only [decide_eq_true_eq] at h
    obtain ⟨i', rfl⟩ := Fin.exists_succAbove_eq h
    simp [vfO, openOf, Fin.insertNth_apply_succAbove]
  · rfl

theorem sigOf_eq (v : Fin (P.T * (P.D.K + 1) + 1) → P.Ch)
    (vf : Fin P.T → Fin (P.D.K + 1) → P.Salt × P.D.View) :
    P.sigOf v vf = P.sigOf v (P.vfO (P.chalOf v) (P.openOf vf (P.chalOf v))) := by
  simp [sigOf, vfO, openOf, Fin.insertNth_apply_succAbove]

/-- The trace of an attempt from the opened data `o`. -/
noncomputable def traceOf (y : P.D.Y) (m : M) (v : Fin (P.T * (P.D.K + 1) + 1) → P.Ch)
    (o : Fin P.T → P.Opened) : (P.protocol M).Trace :=
  ([], (((List.finRange (P.T * (P.D.K + 1) + 1)).filter (P.pubOf v)).map fun i =>
      (P.keyOf M y m (P.vfO (P.chalOf v) o) v i, v i),
    some (P.sigOf v (P.vfO (P.chalOf v) o))))

theorem trace_eq (x : P.D.Y) (w : P.D.X) (m : M) (r : P.Rand)
    (v : Fin (P.T * (P.D.K + 1) + 1) → P.Ch) :
    (P.protocol M).trace x w m r v =
      P.traceOf M x m v (P.openOf (P.vfR w r) (P.chalOf v)) := by
  simp only [Protocol.trace, Protocol.view, Protocol.evEntries_of_ev_false (G := P.protocol M)
    (fun _ => rfl), traceOf, Protocol.pubEntries, Protocol.entries]
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · simp only [Bool.not_false, Bool.true_and]
    refine List.map_congr_left fun i hi => ?_
    rw [P.keyOf_of_pub M _ (List.of_mem_filter hi)]
  · exact congrArg some (P.sigOf_eq v _)

theorem simTrace_eq (look : P.Key M → Option P.Ch) (x : P.D.Y) (m : M)
    (e : Fin (P.T * (P.D.K + 1) + 1) → P.Ch) (s : P.SimRand) :
    (P.protocol M).simTrace look x m e s =
      P.traceOf M x m e (P.openOf (P.vfS x (P.chalOf e) s) (P.chalOf e)) := by
  rw [Protocol.simTrace_of_simKey_none (G := P.protocol M) (fun _ _ => rfl)]
  simp only [traceOf]
  refine Prod.ext rfl (Prod.ext ?_ ?_)
  · refine List.map_congr_left fun i hi => ?_
    rw [P.keyOf_of_pub M _ (List.of_mem_filter hi)]
  · exact congrArg some (P.sigOf_eq e _)

/-- By perfect `K`-privacy, the opened data of an honest attempt on uniform randomness
has the distribution of the simulated opened data on uniform simulator randomness. -/
theorem open_dist (hP : P.D.Private) (w : P.D.X) (c : Fin P.T → Fin (P.D.K + 1)) :
    (PMF.uniformOfFintype P.Rand).map (fun r => P.openOf (P.vfR w r) c) =
      (PMF.uniformOfFintype P.SimRand).map
        (fun s => P.openOf (P.vfS (P.D.F w) c s) c) := by
  let H : (Fin P.T → Fin P.D.K → P.D.View) × (Fin P.T × Fin (P.D.K + 1) → P.Salt) →
      Fin P.T → P.Opened :=
    fun q j i => (q.2 (j, (c j).succAbove i), q.1 j i)
  have hR : (fun r : P.Rand => P.openOf (P.vfR w r) c) =
      H ∘ fun r => ((fun j i => P.D.views w (r.1 j) ((c j).succAbove i)), r.2) := by
    funext r; rfl
  have hS : (fun s : P.SimRand => P.openOf (P.vfS (P.D.F w) c s) c) =
      H ∘ fun s => ((fun j => P.D.sim (P.D.F w) (c j) (s.1 j)), s.2) := by
    funext s j i
    simp [H, openOf, vfS, Fin.insertNth_apply_succAbove]
  rw [hR, hS, ← PMF.map_comp, ← PMF.map_comp]
  congr 1
  refine map_uniform_prod_fst_congr (f := fun τ : Fin P.T → P.D.Tape => fun j i =>
    P.D.views w (τ j) ((c j).succAbove i))
    (g := fun τ : Fin P.T → P.D.SimTape => fun j => P.D.sim (P.D.F w) (c j) (τ j)) ?_
  exact map_uniform_pi_congr (fun j t i => P.D.views w t ((c j).succAbove i))
    (fun j t => P.D.sim (P.D.F w) (c j) t) fun j => hP w (c j)

/-- **Statistical HVZK with distance `0`** at every pair, from perfect `K`-privacy of the
decomposition. -/
theorem statHVZKAt (hP : P.D.Private) (w : P.D.X) :
    (P.protocol M).StatHVZKAt (P.D.F w) w 0 := by
  intro m look g _
  rw [add_zero]
  refine ENNReal.tsum_le_tsum fun e => mul_le_mul' le_rfl ?_
  simp only [Protocol.vals_of_ev_false (G := P.protocol M) (fun _ => rfl)]
  calc _ ≤ ∑' r, PMF.uniformOfFintype P.Rand r *
        g ((P.protocol M).trace (P.D.F w) w m r e) := by
        refine ENNReal.tsum_le_tsum fun r => mul_le_mul' le_rfl ?_
        split_ifs <;> simp
    _ = ∑' r, PMF.uniformOfFintype P.Rand r *
          g (P.traceOf M (P.D.F w) m e (P.openOf (P.vfR w r) (P.chalOf e))) := by
        simp only [trace_eq]
    _ = ∑' s, PMF.uniformOfFintype P.SimRand s *
          g (P.traceOf M (P.D.F w) m e
            (P.openOf (P.vfS (P.D.F w) (P.chalOf e) s) (P.chalOf e))) := by
        rw [tsum_mul_comp_eq_map _ (fun r => P.openOf (P.vfR w r) (P.chalOf e))
            (fun o => g (P.traceOf M (P.D.F w) m e o)),
          tsum_mul_comp_eq_map _
            (fun s => P.openOf (P.vfS (P.D.F w) (P.chalOf e) s) (P.chalOf e))
            (fun o => g (P.traceOf M (P.D.F w) m e o)), open_dist P hP]
    _ = _ := by simp only [simTrace_eq]

/-! ## Key classes and the key bound -/

/-- The key classes: commitment points (`false`) and challenge points (`true`). -/
def classes : (P.protocol M).Classes where
  ι := Bool
  cls k := k.isRight
  ecls i := (P.kind i).isNone
  key_cls x w m r v i := by
    change (P.keyOf M x m (P.vfR w r) v i).isRight = (P.kind i).isNone
    unfold keyOf
    split <;> simp_all
  vcls j := decide (P.T * P.D.K ≤ j.val)
  vkey_cls x m σ vs h := by
    change (P.vkey M x m σ vs).isRight = decide (P.T * P.D.K ≤ vs.length)
    unfold vkey
    split_ifs <;> simp <;> omega

/-- Averaging over the salt of the party `jp`: a guess from `q r` that does not depend
on that salt hits a point that determines it with probability at most `1/|Salt|`. -/
theorem salt_guess_le {Kt : Type} (jp : Fin P.T × Fin (P.D.K + 1)) (q : P.Rand → PMF Kt)
    (k : P.Rand → Kt) (hq : ∀ (r : P.Rand) s, q (r.1, Function.update r.2 jp s) = q r)
    (hk : ∀ (r : P.Rand) s s', k (r.1, Function.update r.2 jp s) =
      k (r.1, Function.update r.2 jp s') → s = s') :
    ∑' r, PMF.uniformOfFintype P.Rand r * q r (k r) ≤ (Fintype.card P.Salt : ℝ≥0∞)⁻¹ := by
  rw [uniform_prod_eq_bind, tsum_bind_mul]
  calc _ ≤ ∑' τ, PMF.uniformOfFintype (Fin P.T → P.D.Tape) τ *
        (Fintype.card P.Salt : ℝ≥0∞)⁻¹ := by
        refine ENNReal.tsum_le_tsum fun τ => mul_le_mul' le_rfl ?_
        rw [← tsum_mul_comp_eq_map, ← Constructions.ECBCPRF.uniform_bind_update jp,
          tsum_bind_mul]
        calc _ ≤ ∑' σ, PMF.uniformOfFintype (Fin P.T × Fin (P.D.K + 1) → P.Salt) σ *
              (Fintype.card P.Salt : ℝ≥0∞)⁻¹ := by
              refine ENNReal.tsum_le_tsum fun σ => mul_le_mul' le_rfl ?_
              rw [← tsum_mul_comp_eq_map]
              simp only [PMF.uniformOfFintype_apply, ENNReal.tsum_mul_left]
              refine mul_le_of_le_one_right' ?_
              calc ∑' s, q (τ, Function.update σ jp s) (k (τ, Function.update σ jp s))
                  = ∑' s, q (τ, σ) (k (τ, Function.update σ jp s)) := by
                    refine tsum_congr fun s => ?_
                    rw [hq (τ, σ) s]
                _ ≤ ∑' y, q (τ, σ) y :=
                    ENNReal.tsum_comp_le_tsum_of_injective (fun s s' h => hk (τ, σ) s s' h) _
                _ = 1 := PMF.tsum_coe _
          _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
    _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- The class-wise key bound: `T(K + 1)·2/|Salt|` for the commitment points and `1/|Dig|`
for the challenge point. -/
noncomputable def gammaCls : Bool → ℝ≥0∞
  | false => ((P.T * (P.D.K + 1) : ℕ) : ℝ≥0∞) * (2 * (Fintype.card P.Salt : ℝ≥0∞)⁻¹)
  | true => (Fintype.card P.Dig : ℝ≥0∞)⁻¹

omit [DecidableEq M] in
theorem key_cIdx (x : P.D.Y) (w : P.D.X) (m : M) (r : P.Rand)
    (v : Fin (P.T * (P.D.K + 1) + 1) → P.Ch) (j : Fin P.T) (p : Fin (P.D.K + 1)) :
    P.keyOf M x m (P.vfR w r) v (P.cIdx j p) =
      .inl (j, p, r.2 (j, p), P.D.views w (r.1 j) p) := by
  simp [keyOf, vfR]

/-- The guess of the point of the commitment entry `(j, p)` of an attempt hits it with
probability at most `2/|Salt|`. -/
theorem commit_guess_le (x : P.D.Y) (w : P.D.X) (m : M) (look : P.Key M → Option P.Ch)
    (Q : (P.protocol M).Trace → PMF (P.Key M)) (e : Fin (P.T * (P.D.K + 1) + 1) → P.Ch)
    (j : Fin P.T) (p : Fin (P.D.K + 1)) :
    ∑' r, PMF.uniformOfFintype P.Rand r *
      Q ((P.protocol M).guessView look x w m r e (P.cIdx j p))
        ((P.protocol M).key x w m r e (P.cIdx j p)) ≤
      2 * (Fintype.card P.Salt : ℝ≥0∞)⁻¹ := by
  have hk : ∀ (r : P.Rand) s s', (P.protocol M).key x w m (r.1, Function.update r.2 (j, p) s) e
      (P.cIdx j p) = (P.protocol M).key x w m (r.1, Function.update r.2 (j, p) s') e
      (P.cIdx j p) → s = s' := by
    intro r s s' h
    simp only [key_cIdx, Function.update_self, Sum.inl.injEq, Prod.mk.injEq] at h
    exact h.2.2.1
  have h0 := P.salt_guess_le (j, p) (fun _ => Q ([], [], none))
    (fun r => (P.protocol M).key x w m r e (P.cIdx j p)) (fun _ _ => rfl) hk
  simp only [Protocol.guessView, Protocol.vals_of_ev_false (G := P.protocol M) (fun _ => rfl)]
  by_cases hp : P.pubOf e (P.cIdx j p) = true
  · simp only [hp, Bool.true_or, if_true]
    exact h0.trans (le_mul_of_one_le_left' (by norm_num))
  · have htr := P.salt_guess_le (j, p) (fun r => Q ((P.protocol M).trace x w m r e))
      (fun r => (P.protocol M).key x w m r e (P.cIdx j p)) ?_ hk
    · calc _ ≤ ∑' r, PMF.uniformOfFintype P.Rand r *
            (Q ([], [], none) ((P.protocol M).key x w m r e (P.cIdx j p)) +
              Q ((P.protocol M).trace x w m r e) ((P.protocol M).key x w m r e (P.cIdx j p))) := by
            refine ENNReal.tsum_le_tsum fun r => mul_le_mul' le_rfl ?_
            split_ifs
            · exact le_self_add
            · exact le_add_self
        _ = ∑' r, PMF.uniformOfFintype P.Rand r *
              Q ([], [], none) ((P.protocol M).key x w m r e (P.cIdx j p)) +
            ∑' r, PMF.uniformOfFintype P.Rand r *
              Q ((P.protocol M).trace x w m r e) ((P.protocol M).key x w m r e (P.cIdx j p)) := by
            simp only [mul_add]; exact ENNReal.tsum_add
        _ ≤ _ := by rw [two_mul]; exact add_le_add h0 htr
    · intro r s
      simp only [trace_eq]
      have hc : p = P.chalOf e j := by
        simp only [pubOf, kind_cIdx, decide_eq_true_eq, not_not] at hp
        simpa using hp
      subst hc
      congr 2
      funext j' i
      simp only [openOf, vfR]
      rw [Function.update_of_ne]
      intro h
      simp only [Prod.mk.injEq] at h
      obtain ⟨rfl, h⟩ := h
      exact Fin.succAbove_ne _ _ h

theorem card_commit_le :
    (Finset.univ.filter fun i : Fin (P.T * (P.D.K + 1) + 1) => (P.kind i).isNone = false).card ≤
      P.T * (P.D.K + 1) := by
  have hsub : (Finset.univ.filter fun i : Fin (P.T * (P.D.K + 1) + 1) =>
      (P.kind i).isNone = false) ⊆ Finset.univ.erase (Fin.last _) := by
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    refine Finset.mem_erase.mpr ⟨fun h => ?_, Finset.mem_univ _⟩
    rw [h, kind_last] at hi
    simp at hi
  refine (Finset.card_le_card hsub).trans ?_
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  omega

/-- **Class-wise key bound** at every pair: `T(K + 1)·2/|Salt|` for the commitment points
and `1/|Dig|` for the challenge point, for `T > 0`. -/
theorem keyBoundClsAt (hT : 0 < P.T) (x : P.D.Y) (w : P.D.X) :
    (P.protocol M).KeyBoundClsAt (P.classes M) x w P.gammaCls := by
  intro c m look Q
  change Bool at c
  cases c with
  | false =>
    calc _ ≤ ∑' e, PMF.uniformOfFintype (Fin (P.T * (P.D.K + 1) + 1) → P.Ch) e *
          P.gammaCls false := by
          refine ENNReal.tsum_le_tsum fun e => mul_le_mul' le_rfl ?_
          simp only [Protocol.vals_of_ev_false (G := P.protocol M) (fun _ => rfl)]
          rw [tsum_fintype]
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          calc _ ≤ ∑ i ∈ Finset.univ.filter (fun i : Fin (P.T * (P.D.K + 1) + 1) =>
                (P.kind i).isNone = false), 2 * (Fintype.card P.Salt : ℝ≥0∞)⁻¹ := by
                refine Finset.sum_le_sum fun i hi => ?_
                simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
                change (P.kind i).isNone = false at hi
                obtain ⟨⟨j, p⟩, hjp⟩ := Option.isSome_iff_exists.mp (by simpa using hi)
                rw [P.kind_eq_some hjp, ← tsum_fintype (L := SummationFilter.unconditional _)]
                refine le_trans ?_ (P.commit_guess_le M x w m look Q e j p)
                refine ENNReal.tsum_le_tsum fun r => mul_le_mul' le_rfl ?_
                split_ifs <;> simp
            _ ≤ _ := by
                rw [Finset.sum_const, nsmul_eq_mul]
                simp only [gammaCls]
                gcongr
                exact_mod_cast P.card_commit_le
      _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
  | true =>
    simp only [Protocol.vals_of_ev_false (G := P.protocol M) (fun _ => rfl)]
    calc _ ≤ ∑' e, PMF.uniformOfFintype (Fin (P.T * (P.D.K + 1) + 1) → P.Ch) e *
          Q ([], [], none) (Sum.inr (x, m, P.digMat e)) := by
          refine ENNReal.tsum_le_tsum fun e => mul_le_mul' le_rfl ?_
          calc _ ≤ ∑' r, PMF.uniformOfFintype P.Rand r *
                Q ([], [], none) (Sum.inr (x, m, P.digMat e)) := by
                refine ENNReal.tsum_le_tsum fun r => mul_le_mul' le_rfl ?_
                rw [Finset.sum_eq_single_of_mem (Fin.last _) ?h1 ?h2]
                case h1 =>
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
                  change (P.kind _).isNone = true; simp
                case h2 =>
                  intro b hb hne
                  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hb
                  have hb' : (P.kind b).isNone = true := hb
                  exact absurd (P.kind_eq_none (Option.isNone_iff_eq_none.mp hb')) hne
                simp only [Protocol.guessView,
                  Protocol.vals_of_ev_false (G := P.protocol M) (fun _ => rfl)]
                have hpub : P.pubOf e (Fin.last _) = true := by simp [pubOf]
                have hkey : P.keyOf M x m (P.vfR w r) e (Fin.last _) =
                    Sum.inr (x, m, P.digMat e) := by simp [keyOf]
                simp only [hpub, hkey, Bool.true_or, if_true]
                split_ifs <;> simp
            _ = _ := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]
      _ ≤ _ := by
          refine tsum_map_guess_le _ (fun e => (Sum.inr (x, m, P.digMat e) : P.Key M)) _ ?_
          intro k
          let j0 : Fin P.T := ⟨0, hT⟩
          rcases k with k | ⟨y, m', C⟩
          · simp
          · calc _ ≤ (PMF.uniformOfFintype (Fin (P.T * (P.D.K + 1) + 1) → P.Ch)).toOuterMeasure
                  {e | (fun c : P.Ch => decide (c.1 = C j0 0)) (e (P.cIdx j0 0)) = true} := by
                  refine MeasureTheory.measure_mono fun e he => ?_
                  simp only [Set.mem_ofPred_eq, Sum.inr.injEq, Prod.mk.injEq] at he
                  simp only [Set.mem_ofPred_eq, decide_eq_true_eq, ← he.2.2]
                  rfl
              _ ≤ _ := by
                  refine uniform_pi_le_of_update_invariant (P.cIdx j0 0) (fun _ => ())
                    (fun _ _ => rfl) (fun _ (c : P.Ch) => decide (c.1 = C j0 0)) fun _ => ?_
                  have hset : {c : P.Ch | decide (c.1 = C j0 0) = true} =
                      {c : P.Ch | c.1 ∈ ({C j0 0} : Set P.Dig)} := by
                    ext c; simp
                  rw [hset, uniform_prod_fst_apply, PMF.toOuterMeasure_uniformOfFintype_apply]
                  simp [gammaCls]

/-! ## The straight-line extractor -/

/-- The visible entries of the tables: the hash entries and the programmed entries. -/
def ents (t : (P.protocol M).Tables) : List (P.Key M × P.Ch) := t.hash ++ t.prog

/-- The digests carried by an entry: the digest of a commitment entry, and the digests
in the point of a challenge entry. -/
def entDigs : P.Key M × P.Ch → List P.Dig
  | (.inl _, c) => [c.1]
  | (.inr (_, _, C), _) => List.ofFn fun q : Fin (P.T * (P.D.K + 1)) =>
      C (finProdFinEquiv.symm q).1 (finProdFinEquiv.symm q).2

/-- The digests carried by the visible entries of the tables. -/
def digs (t : (P.protocol M).Tables) : List P.Dig := (P.ents M t).flatMap (P.entDigs M)

/-- The view `v` of the party `p` of repetition `j` has a visible commitment entry with
digest `d`. -/
def InPre (t : (P.protocol M).Tables) (j : Fin P.T) (p : Fin (P.D.K + 1)) (d : P.Dig)
    (v : P.D.View) : Prop :=
  ∃ s c, (Sum.inl (j, p, s, v), c) ∈ P.ents M t ∧ c.1 = d

/-- The visible commitment entries with equal repetition, party and digest have equal
views. -/
def Uniq (t : (P.protocol M).Tables) : Prop :=
  ∀ j p d v v', P.InPre M t j p d v → P.InPre M t j p d v' → v = v'

/-- The views `v` of repetition `j` have visible commitment entries with the digests
`C j` and pass the test for `y` at every hidden party. -/
def ExtAt (t : (P.protocol M).Tables) (y : P.D.Y) (C : Fin P.T → Fin (P.D.K + 1) → P.Dig)
    (j : Fin P.T) (v : Fin (P.D.K + 1) → P.D.View) : Prop :=
  (∀ p, P.InPre M t j p (C j p) (v p)) ∧ ∀ c, P.D.check y c (fun i => v (c.succAbove i)) = true

/-- Some repetition of the digests `C` has committed views of all parties passing the
tests. -/
def Ext (t : (P.protocol M).Tables) (y : P.D.Y) (C : Fin P.T → Fin (P.D.K + 1) → P.Dig) :
    Prop :=
  ∃ j v, P.ExtAt M t y C j v

/-- The hidden party `ch` of repetition `j` of the digests `C` can be answered from the
visible commitment entries. -/
def Good (t : (P.protocol M).Tables) (y : P.D.Y) (C : Fin P.T → Fin (P.D.K + 1) → P.Dig)
    (j : Fin P.T) (ch : Fin (P.D.K + 1)) : Prop :=
  ∃ a : Fin P.D.K → P.D.View,
    (∀ i, P.InPre M t j (ch.succAbove i) (C j (ch.succAbove i)) (a i)) ∧
      P.D.check y ch a = true

open Classical in
/-- The bad answers: a commitment digest that is a digest of a visible entry, and a
challenge vector whose every component can be answered for digests without consistent
committed views of all parties, on tables with unique commitment views. -/
noncomputable def Bad (_x : P.D.Y) (t : (P.protocol M).Tables) : P.Key M → P.Ch → Bool
  | .inl _, c => decide (c.1 ∈ P.digs M t)
  | .inr (y, _, C), c => decide (P.Uniq M t ∧ ¬ P.Ext M t y C ∧ ∀ j, P.Good M t y C j (c.2 j))

/-- On tables with unique commitment views and without consistent committed views of all
parties, every repetition has a hidden party that cannot be answered, for at least two
parties. -/
theorem exists_not_good (hK : 0 < P.D.K) {t : (P.protocol M).Tables} {y : P.D.Y}
    {C : Fin P.T → Fin (P.D.K + 1) → P.Dig} (hU : P.Uniq M t) (hE : ¬ P.Ext M t y C)
    (j : Fin P.T) : ∃ ch, ¬ P.Good M t y C j ch := by
  by_contra hall
  push Not at hall
  have hv : ∀ p, ∃ w, P.InPre M t j p (C j p) w := by
    intro p
    have hne : (if p = 0 then Fin.last P.D.K else 0) ≠ p := by
      split_ifs with h
      · rw [h]; exact Fin.ext_iff.not.mpr (by simp; omega)
      · exact Ne.symm h
    obtain ⟨i, hi⟩ := Fin.exists_succAbove_eq hne.symm
    obtain ⟨a, ha, -⟩ := hall (if p = 0 then Fin.last P.D.K else 0)
    exact ⟨a i, hi ▸ ha i⟩
  choose v hv using hv
  refine hE ⟨j, v, hv, fun c => ?_⟩
  obtain ⟨a, ha, hc⟩ := hall c
  have : (fun i => v (c.succAbove i)) = a :=
    funext fun i => hU j _ _ _ _ (hv _) (ha i)
  rw [this]
  exact hc

/-- The bad-answer bounds: `(T(K + 1) + 1)·N/|Dig|` for a commitment digest and
`(K/(K + 1))^T` for a challenge vector. -/
noncomputable def epsCls (N : ℕ) : Bool → ℝ≥0∞
  | false => (((P.T * (P.D.K + 1) + 1) * N : ℕ) : ℝ≥0∞) * (Fintype.card P.Dig : ℝ≥0∞)⁻¹
  | true => (P.D.K : ℝ≥0∞) ^ P.T / ((P.D.K : ℝ≥0∞) + 1) ^ P.T

omit [DecidableEq M] in
theorem length_entDigs_le (e : P.Key M × P.Ch) :
    (P.entDigs M e).length ≤ P.T * (P.D.K + 1) + 1 := by
  rcases e with ⟨k | ⟨y, m', C⟩, c⟩ <;> simp [entDigs]

theorem length_digs_le (t : (P.protocol M).Tables) :
    (P.digs M t).length ≤ (P.T * (P.D.K + 1) + 1) * t.size := by
  unfold digs
  rw [List.length_flatMap]
  calc ((P.ents M t).map fun e => (P.entDigs M e).length).sum
      ≤ ((P.ents M t).map fun _ => P.T * (P.D.K + 1) + 1).sum :=
        List.sum_le_sum fun e _ => P.length_entDigs_le M e
    _ = (P.ents M t).length * (P.T * (P.D.K + 1) + 1) := by simp
    _ ≤ (P.T * (P.D.K + 1) + 1) * t.size := by
        rw [mul_comm]
        gcongr
        simp [ents, Protocol.Tables.size]
        omega

theorem digs_mem_le (t : (P.protocol M).Tables) {N : ℕ} (ht : t.size ≤ N) :
    (PMF.uniformOfFintype P.Ch).toOuterMeasure {c | decide (c.1 ∈ P.digs M t) = true} ≤
      P.epsCls N false := by
  have hset : {c : P.Ch | decide (c.1 ∈ P.digs M t) = true} =
      {c : P.Ch | c.1 ∈ {d | d ∈ P.digs M t}} := by
    ext c; simp
  rw [hset, uniform_prod_fst_apply]
  refine (uniform_mem_list_le _).trans ?_
  simp only [epsCls]
  gcongr
  exact (P.length_digs_le M t).trans (Nat.mul_le_mul_left _ ht)

theorem bad_inl_le (x : P.D.Y) (t : (P.protocol M).Tables) {N : ℕ} (ht : t.size ≤ N)
    (k : P.CKey) :
    (PMF.uniformOfFintype P.Ch).toOuterMeasure {c | P.Bad M x t (.inl k) c = true} ≤
      P.epsCls N false :=
  P.digs_mem_le M t ht

theorem bad_inr_le (hK : 0 < P.D.K) (x : P.D.Y) (t : (P.protocol M).Tables) (y : P.D.Y)
    (m' : M) (C : Fin P.T → Fin (P.D.K + 1) → P.Dig) :
    (PMF.uniformOfFintype P.Ch).toOuterMeasure {c | P.Bad M x t (.inr (y, m', C)) c = true} ≤
      P.epsCls 0 true := by
  classical
  by_cases h : P.Uniq M t ∧ ¬ P.Ext M t y C
  · let S : Fin P.T → Finset (Fin (P.D.K + 1)) := fun j =>
      Finset.univ.filter fun ch => P.Good M t y C j ch
    have hS : ∀ j, S j ≠ Finset.univ := by
      intro j hj
      obtain ⟨ch, hch⟩ := P.exists_not_good M hK h.1 h.2 j
      have : ch ∈ S j := hj ▸ Finset.mem_univ ch
      simp [S] at this
      exact hch this
    calc _ ≤ (PMF.uniformOfFintype P.Ch).toOuterMeasure {c | c.2 ∈ {f | ∀ j, f j ∈ S j}} := by
          refine MeasureTheory.measure_mono fun c hc => ?_
          simp only [Bad, decide_eq_true_eq, Set.mem_ofPred_eq] at hc
          simp [S, hc.2.2]
      _ ≤ _ := by
          rw [uniform_prod_snd_apply]
          exact uniform_box_le P.T P.D.K S hS
  · have : {c : P.Ch | P.Bad M x t (.inr (y, m', C)) c = true} = ∅ := by
      ext c
      simp only [Bad, decide_eq_true_eq, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h' => h ⟨h'.1, h'.2.1⟩
    rw [this, MeasureTheory.measure_empty]
    exact zero_le

/-- The programmed entries of a simulated attempt contain a bad answer with probability
at most `T(K + 1)·(T(K + 1) + 1)·N/|Dig| + (K/(K + 1))^T`. -/
theorem simBad_le (hK : 0 < P.D.K) (x : P.D.Y) (t : (P.protocol M).Tables) (m : M) {N : ℕ}
    (ht : t.size ≤ N) :
    (sampleVec (P.protocol M) fun e (s : P.SimRand) =>
      ((P.protocol M).simTrace t.lookup x m e s).2.1.any fun p =>
        P.Bad M x (hashAll t ((P.protocol M).simTrace t.lookup x m e s).1) p.1 p.2).toOuterMeasure
        {c | c = true} ≤
      ((P.T * (P.D.K + 1) : ℕ) : ℝ≥0∞) * P.epsCls N false + P.epsCls N true := by
  refine sampleVec_le_of_forall _ fun s => ?_
  simp only [simTrace_eq, traceOf, hashAll_nil (G := P.protocol M)]
  calc _ ≤ (PMF.uniformOfFintype (Fin (P.T * (P.D.K + 1) + 1) → P.Ch)).toOuterMeasure
        (⋃ i, {e | P.Bad M x t (P.keyOf M x m (P.vfO (P.chalOf e)
          (P.openOf (P.vfS x (P.chalOf e) s) (P.chalOf e))) e i) (e i) = true}) := by
        refine MeasureTheory.measure_mono fun e he => ?_
        simp only [Set.mem_ofPred_eq, List.any_eq_true, List.mem_map, List.mem_filter] at he
        obtain ⟨_, ⟨i, _, rfl⟩, h⟩ := he
        exact Set.mem_iUnion.mpr ⟨i, h⟩
    _ ≤ ∑ i, (PMF.uniformOfFintype (Fin (P.T * (P.D.K + 1) + 1) → P.Ch)).toOuterMeasure
        {e | P.Bad M x t (P.keyOf M x m (P.vfO (P.chalOf e)
          (P.openOf (P.vfS x (P.chalOf e) s) (P.chalOf e))) e i) (e i) = true} :=
        MeasureTheory.measure_iUnion_fintype_le _ _
    _ ≤ _ := by
        rw [Fin.sum_univ_castSucc]
        gcongr
        · calc _ ≤ ∑ _i : Fin (P.T * (P.D.K + 1)), P.epsCls N false := by
                refine Finset.sum_le_sum fun i _ => ?_
                have hk : ∀ e : Fin (P.T * (P.D.K + 1) + 1) → P.Ch, P.Bad M x t
                    (P.keyOf M x m (P.vfO (P.chalOf e) (P.openOf (P.vfS x (P.chalOf e) s)
                      (P.chalOf e))) e i.castSucc)
                    (e i.castSucc) = decide ((e i.castSucc).1 ∈ P.digs M t) := by
                  intro e; simp [keyOf, kind, Bad]
                simp only [hk]
                refine uniform_pi_le_of_update_invariant i.castSucc (fun _ => ()) (fun _ _ => rfl)
                  (fun _ (c : P.Ch) => decide (c.1 ∈ P.digs M t)) fun _ => P.digs_mem_le M t ht
            _ = _ := by simp
        · have hk : ∀ e : Fin (P.T * (P.D.K + 1) + 1) → P.Ch, P.Bad M x t (P.keyOf M x m (P.vfO
              (P.chalOf e) (P.openOf (P.vfS x (P.chalOf e) s) (P.chalOf e))) e (Fin.last _))
              (e (Fin.last _)) = P.Bad M x t (.inr (x, m, P.digMat e)) (e (Fin.last _)) := by
            intro e; simp [keyOf]
          simp only [hk]
          refine uniform_pi_le_of_update_invariant (Fin.last _) P.digMat (fun e c => ?_)
            (fun z (c : P.Ch) => P.Bad M x t (.inr (x, m, z)) c)
            fun z => (P.bad_inr_le M hK x t x m z).trans_eq rfl
          funext j p
          simp [digMat, Function.update_of_ne (P.cIdx_ne_last j p)]

/-! ## The invariant of the instrumented game -/

/-- The invariant of the reachable tables without the extraction flag: unique commitment
views; every challenge hash entry has consistent committed views of all parties in some
repetition or a component of its challenge vector that cannot be answered; every
programmed challenge entry is on a signed message. -/
def Inv (t : (P.protocol M).Tables) : Prop :=
  P.Uniq M t ∧
  (∀ y m' C c, (Sum.inr (y, m', C), c) ∈ t.hash →
    P.Ext M t y C ∨ ∃ j, ¬ P.Good M t y C j (c.2 j)) ∧
  (∀ y m' C c, (Sum.inr (y, m', C), c) ∈ t.prog → m' ∈ t.signed)

theorem inv_empty : P.Inv M Protocol.Tables.empty := by
  simp [Inv, Uniq, InPre, ents, Protocol.Tables.empty]

theorem mem_digs_of_inPre {t : (P.protocol M).Tables} {j : Fin P.T} {p : Fin (P.D.K + 1)}
    {d : P.Dig} {v : P.D.View} (h : P.InPre M t j p d v) : d ∈ P.digs M t := by
  obtain ⟨s, c, hm, rfl⟩ := h
  exact List.mem_flatMap.mpr ⟨_, hm, by simp [entDigs]⟩

theorem mem_digs_of_chal {t : (P.protocol M).Tables} {y : P.D.Y} {m' : M}
    {C : Fin P.T → Fin (P.D.K + 1) → P.Dig} {c : P.Ch}
    (h : (Sum.inr (y, m', C), c) ∈ P.ents M t) (j : Fin P.T) (p : Fin (P.D.K + 1)) :
    C j p ∈ P.digs M t := by
  refine List.mem_flatMap.mpr ⟨_, h, ?_⟩
  simp only [entDigs, List.mem_ofFn]
  exact ⟨finProdFinEquiv (j, p), by simp⟩

theorem inPre_mono {t t' : (P.protocol M).Tables} (hold : ∀ e ∈ P.ents M t, e ∈ P.ents M t')
    {j : Fin P.T} {p : Fin (P.D.K + 1)} {d : P.Dig} {v : P.D.View} (h : P.InPre M t j p d v) :
    P.InPre M t' j p d v := by
  obtain ⟨s, c, hm, hd⟩ := h
  exact ⟨s, c, hold _ hm, hd⟩

theorem ext_mono {t t' : (P.protocol M).Tables} (hold : ∀ e ∈ P.ents M t, e ∈ P.ents M t')
    {y : P.D.Y} {C : Fin P.T → Fin (P.D.K + 1) → P.Dig} (h : P.Ext M t y C) :
    P.Ext M t' y C := by
  obtain ⟨j, v, hv, hc⟩ := h
  exact ⟨j, v, fun p => P.inPre_mono M hold (hv p), hc⟩

/-- New commitment entries whose digests are not digests of `t` give no new committed view
for a digest of `t`. -/
theorem inPre_of_new {t t' : (P.protocol M).Tables}
    (hnew : ∀ k c, (Sum.inl k, c) ∈ P.ents M t' → (Sum.inl k, c) ∉ P.ents M t →
      c.1 ∉ P.digs M t)
    {j : Fin P.T} {p : Fin (P.D.K + 1)} {d : P.Dig} {v : P.D.View} (h : P.InPre M t' j p d v)
    (hd : d ∈ P.digs M t) : P.InPre M t j p d v := by
  obtain ⟨s, c, hm, rfl⟩ := h
  by_cases ho : (Sum.inl (j, p, s, v), c) ∈ P.ents M t
  · exact ⟨s, c, ho, rfl⟩
  · exact absurd hd (hnew _ c hm ho)

/-- **Extension of the invariant.** Tables that keep the visible entries, whose new
commitment entries carry digests that are not digests of `t` and have one view for each
repetition and party, whose new challenge hash entries satisfy the challenge condition and
whose programmed challenge entries are on signed messages satisfy the invariant. -/
theorem inv_extend {t t' : (P.protocol M).Tables} (hI : P.Inv M t)
    (hold : ∀ e ∈ P.ents M t, e ∈ P.ents M t')
    (hnew : ∀ k c, (Sum.inl k, c) ∈ P.ents M t' → (Sum.inl k, c) ∉ P.ents M t →
      c.1 ∉ P.digs M t)
    (hsame : ∀ j p s s' v v' c c', (Sum.inl (j, p, s, v), c) ∈ P.ents M t' →
      (Sum.inl (j, p, s', v'), c') ∈ P.ents M t' → (Sum.inl (j, p, s, v), c) ∉ P.ents M t →
      (Sum.inl (j, p, s', v'), c') ∉ P.ents M t → v = v')
    (hhash : ∀ y m' C c, (Sum.inr (y, m', C), c) ∈ t'.hash →
      (Sum.inr (y, m', C), c) ∈ t.hash ∨ P.Ext M t' y C ∨ ∃ j, ¬ P.Good M t' y C j (c.2 j))
    (hprog : ∀ y m' C c, (Sum.inr (y, m', C), c) ∈ t'.prog → m' ∈ t'.signed) :
    P.Inv M t' := by
  refine ⟨?_, ?_, hprog⟩
  · intro j p d v v' h1 h2
    obtain ⟨s, c, hm, hd⟩ := h1
    obtain ⟨s', c', hm', hd'⟩ := h2
    by_cases o1 : (Sum.inl (j, p, s, v), c) ∈ P.ents M t <;>
      by_cases o2 : (Sum.inl (j, p, s', v'), c') ∈ P.ents M t
    · exact hI.1 j p d v v' ⟨s, c, o1, hd⟩ ⟨s', c', o2, hd'⟩
    · exact absurd (hd' ▸ P.mem_digs_of_inPre M ⟨s, c, o1, hd⟩) (hnew _ c' hm' o2)
    · exact absurd (hd ▸ P.mem_digs_of_inPre M ⟨s', c', o2, hd'⟩) (hnew _ c hm o1)
    · exact hsame j p s s' v v' c c' hm hm' o1 o2
  · intro y m' C c hmem
    rcases hhash y m' C c hmem with hold' | hnew'
    · have hC := P.mem_digs_of_chal M (List.mem_append_left _ hold')
      rcases hI.2.1 y m' C c hold' with hE | ⟨j, hj⟩
      · exact Or.inl (P.ext_mono M hold hE)
      · exact Or.inr ⟨j, fun ⟨a, ha, hc⟩ =>
          hj ⟨a, fun i => P.inPre_of_new M hnew (ha i) (hC j _), hc⟩⟩
    · exact hnew'

omit [DecidableEq M] in
theorem keyOf_eq_inl {y : P.D.Y} {m : M}
    {vf : Fin P.T → Fin (P.D.K + 1) → P.Salt × P.D.View}
    {v : Fin (P.T * (P.D.K + 1) + 1) → P.Ch} {i : Fin (P.T * (P.D.K + 1) + 1)} {j : Fin P.T}
    {p : Fin (P.D.K + 1)} {s : P.Salt} {w : P.D.View}
    (h : P.keyOf M y m vf v i = .inl (j, p, s, w)) :
    P.kind i = some (j, p) ∧ vf j p = (s, w) := by
  unfold keyOf at h
  split at h
  · next j' p' hk =>
    simp only [Sum.inl.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, h1, h2⟩ := h
    exact ⟨hk, Prod.ext h1 h2⟩
  · simp at h

omit [DecidableEq M] in
theorem keyOf_eq_inr {y : P.D.Y} {m : M}
    {vf : Fin P.T → Fin (P.D.K + 1) → P.Salt × P.D.View}
    {v : Fin (P.T * (P.D.K + 1) + 1) → P.Ch} {i : Fin (P.T * (P.D.K + 1) + 1)} {y' : P.D.Y}
    {m' : M} {C : Fin P.T → Fin (P.D.K + 1) → P.Dig}
    (h : P.keyOf M y m vf v i = .inr (y', m', C)) : m' = m := by
  unfold keyOf at h
  split at h
  · simp at h
  · simp only [Sum.inr.injEq, Prod.mk.injEq] at h
    exact h.2.1.symm

theorem mem_ents_hash {t : (P.protocol M).Tables} {q e : P.Key M × P.Ch} :
    e ∈ P.ents M { t with hash := t.hash ++ [q] } ↔ e ∈ P.ents M t ∨ e = q := by
  simp only [ents, List.mem_append, List.mem_singleton]
  tauto

/-- A fresh commitment answer that is not bad keeps the invariant. -/
theorem inv_hash_inl {x : P.D.Y} {t : (P.protocol M).Tables} (hI : P.Inv M t) (k : P.CKey)
    (c : P.Ch) (hbad : P.Bad M x t (.inl k) c = false) :
    P.Inv M { t with hash := t.hash ++ [(.inl k, c)] } := by
  simp only [Bad, decide_eq_false_iff_not] at hbad
  refine P.inv_extend M hI (fun e he => P.mem_ents_hash M |>.mpr (Or.inl he)) ?_ ?_ ?_ hI.2.2
  · intro k' c' hm ho
    rcases (P.mem_ents_hash M).mp hm with h | h
    · exact absurd h ho
    · simp only [Prod.mk.injEq, Sum.inl.injEq] at h
      rw [h.2]; exact hbad
  · intro j p s s' v v' c₁ c₂ h1 h2 o1 o2
    rcases (P.mem_ents_hash M).mp h1 with h1 | h1
    · exact absurd h1 o1
    rcases (P.mem_ents_hash M).mp h2 with h2 | h2
    · exact absurd h2 o2
    rw [← h2] at h1
    simp only [Prod.mk.injEq, Sum.inl.injEq] at h1
    exact h1.1.2.2.2
  · intro y m' C c' hm
    simp only [List.mem_append, List.mem_singleton, Prod.mk.injEq, reduceCtorEq, false_and,
      or_false] at hm
    exact Or.inl hm

/-- A fresh challenge answer that is not bad keeps the invariant. -/
theorem inv_hash_inr {x : P.D.Y} {t : (P.protocol M).Tables} (hI : P.Inv M t) (y : P.D.Y)
    (m' : M) (C : Fin P.T → Fin (P.D.K + 1) → P.Dig) (c : P.Ch)
    (hbad : P.Bad M x t (.inr (y, m', C)) c = false) :
    P.Inv M { t with hash := t.hash ++ [(.inr (y, m', C), c)] } := by
  simp only [Bad, decide_eq_false_iff_not] at hbad
  have hinl : ∀ k c', (Sum.inl k, c') ∈ P.ents M { t with hash := t.hash ++
      [(.inr (y, m', C), c)] } → (Sum.inl k, c') ∈ P.ents M t := by
    intro k c' hm
    rcases (P.mem_ents_hash M).mp hm with h | h
    · exact h
    · simp at h
  have hpre : ∀ j p d v, P.InPre M { t with hash := t.hash ++ [(.inr (y, m', C), c)] } j p d v →
      P.InPre M t j p d v := by
    rintro j p d v ⟨s, c', hm, hd⟩
    exact ⟨s, c', hinl _ _ hm, hd⟩
  refine P.inv_extend M hI (fun e he => P.mem_ents_hash M |>.mpr (Or.inl he))
    (fun k c' hm ho => absurd (hinl k c' hm) ho)
    (fun _ _ _ _ _ _ _ _ h1 _ o1 _ => absurd (hinl _ _ h1) o1) ?_ hI.2.2
  intro y' m'' C' c' hm
  simp only [List.mem_append, List.mem_singleton] at hm
  rcases hm with hm | hm
  · exact Or.inl hm
  · simp only [Prod.mk.injEq, Sum.inr.injEq] at hm
    obtain ⟨⟨hy, -, hC⟩, hc⟩ := hm
    rw [hy, hC, hc]
    right
    by_cases hE : P.Ext M t y C
    · exact Or.inl (P.ext_mono M (fun e he => P.mem_ents_hash M |>.mpr (Or.inl he)) hE)
    · have : ¬ ∀ j, P.Good M t y C j (c.2 j) := fun h => hbad ⟨hI.1, hE, h⟩
      push Not at this
      obtain ⟨j, hj⟩ := this
      exact Or.inr ⟨j, fun ⟨a, ha, hc⟩ => hj ⟨a, fun i => hpre _ _ _ _ (ha i), hc⟩⟩

/-- A simulated signing attempt whose programmed entries are not bad keeps the
invariant. -/
theorem inv_sign {x : P.D.Y} {t : (P.protocol M).Tables} (hI : P.Inv M t) (b : Bool) (m : M)
    (vf : Fin P.T → Fin (P.D.K + 1) → P.Salt × P.D.View)
    (e : Fin (P.T * (P.D.K + 1) + 1) → P.Ch)
    (hbad : ∀ q ∈ ((List.finRange (P.T * (P.D.K + 1) + 1)).filter (P.pubOf e)).map
      (fun i => (P.keyOf M x m vf e i, e i)), P.Bad M x t q.1 q.2 = false) :
    P.Inv M { (programAll t b (((List.finRange (P.T * (P.D.K + 1) + 1)).filter (P.pubOf e)).map
      (fun i => (P.keyOf M x m vf e i, e i)))).1 with signed := t.signed ++ [m] } := by
  set L := ((List.finRange (P.T * (P.D.K + 1) + 1)).filter (P.pubOf e)).map
    (fun i => (P.keyOf M x m vf e i, e i)) with hL
  obtain ⟨hh, -, -, hpre, hsub⟩ := programAll_tables t b L
  have hents : ∀ q, q ∈ P.ents M { (programAll t b L).1 with signed := t.signed ++ [m] } →
      q ∈ P.ents M t ∨ q ∈ L := by
    intro q hq
    simp only [ents, List.mem_append] at hq ⊢
    rcases hq with hq | hq
    · rw [hh] at hq; exact Or.inl (Or.inl hq)
    · rcases hsub q hq with h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
  have hmemL : ∀ q ∈ L, ∃ i, q = (P.keyOf M x m vf e i, e i) := by
    intro q hq
    simp only [hL, List.mem_map, List.mem_filter] at hq
    obtain ⟨i, _, rfl⟩ := hq
    exact ⟨i, rfl⟩
  refine P.inv_extend M hI ?_ ?_ ?_ ?_ ?_
  · intro q hq
    simp only [ents, List.mem_append] at hq ⊢
    rcases hq with hq | hq
    · left; rw [hh]; exact hq
    · right; exact hpre.subset hq
  · intro k c hm ho
    rcases hents _ hm with h | h
    · exact absurd h ho
    · have := hbad _ h
      simpa [Bad] using this
  · intro j p s s' v v' c c' h1 h2 o1 o2
    rcases hents _ h1 with h1 | h1
    · exact absurd h1 o1
    rcases hents _ h2 with h2 | h2
    · exact absurd h2 o2
    obtain ⟨i, hi⟩ := hmemL _ h1
    obtain ⟨i', hi'⟩ := hmemL _ h2
    simp only [Prod.mk.injEq] at hi hi'
    obtain ⟨hk1, hv1⟩ := P.keyOf_eq_inl M hi.1.symm
    obtain ⟨hk2, hv2⟩ := P.keyOf_eq_inl M hi'.1.symm
    rw [hv1] at hv2
    simp only [Prod.mk.injEq] at hv2
    exact hv2.2
  · intro y m' C c hm
    left
    simpa [hh] using hm
  · intro y m' C c hm
    simp only [List.mem_append, List.mem_singleton]
    rcases hsub _ hm with h | h
    · exact Or.inl (hI.2.2 y m' C c h)
    · obtain ⟨i, hi⟩ := hmemL _ h
      simp only [Prod.mk.injEq] at hi
      exact Or.inr (P.keyOf_eq_inr M hi.1.symm)

/-- The reachable states of the instrumented game without the extraction flag satisfy the
invariant. -/
theorem inv_of_reach {N : ℕ} {x : P.D.Y} {s : SLState (P.protocol M)}
    (h : SLReach N (P.Bad M) x s) (hf : s.2 = false) : P.Inv M s.1.1 := by
  induction h with
  | empty => exact P.inv_empty M
  | step s d o hs hsz ho ih =>
    obtain ⟨⟨t, b⟩, β⟩ := s
    cases d with
    | inl k =>
      simp only [toOracle, slStep, slHashStep] at ho
      split at ho
      · simp only [Step.toPMF, PMF.support_pure, Set.mem_singleton_iff] at ho
        subst ho
        exact ih hf
      · simp only [Step.toPMF, PMF.support_map, Set.mem_image] at ho
        obtain ⟨c, -, rfl⟩ := ho
        simp only [Bool.or_eq_false_iff, Bool.and_eq_false_iff, decide_eq_false_iff_not] at hf
        have hbad : P.Bad M x t k c = false := hf.2.resolve_left (not_not.mpr hsz)
        have hI := ih hf.1
        rcases k with k | ⟨y, m', C⟩
        · exact P.inv_hash_inl M hI k c hbad
        · exact P.inv_hash_inr M hI y m' C c hbad
    | inr m =>
      simp only [toOracle, slStep, Step.toPMF] at ho
      obtain ⟨e, s', rfl⟩ := mem_support_sampleVec ho
      simp only [slSignOut, Bool.or_eq_false_iff, Bool.and_eq_false_iff,
        decide_eq_false_iff_not] at hf
      have hI := ih hf.1.1
      have hany := hf.2.resolve_left (not_not.mpr hsz)
      simp only [simTrace_eq, traceOf, hashAll_nil (G := P.protocol M), List.any_eq_false,
        Bool.not_eq_true] at hany
      simp only [slSignOut, simSignOut, traceOut, programOut, simTrace_eq, traceOf,
        hashAll_nil (G := P.protocol M)]
      exact P.inv_sign M hI b m _ e hany

/-! ## Soundness of the extractor -/

theorem mem_ents_of_lookup {t : (P.protocol M).Tables} {k : P.Key M} {c : P.Ch}
    (h : t.lookup k = some c) : (k, c) ∈ P.ents M t := by
  unfold Protocol.Tables.lookup at h
  simp only [ents, List.mem_append]
  cases hp : lookupIn t.prog k with
  | some c' =>
    rw [hp] at h
    simp only [Option.some_or, Option.some.injEq] at h
    exact Or.inr (h ▸ mem_of_lookupIn_eq_some hp)
  | none =>
    rw [hp, Option.none_or] at h
    exact Or.inl (mem_of_lookupIn_eq_some h)

open Classical in
/-- The preimage reconstructed from consistent committed views of all parties of some
repetition of the digests `C`, if there are such views. -/
noncomputable def extFrom (t : (P.protocol M).Tables) (y : P.D.Y)
    (C : Fin P.T → Fin (P.D.K + 1) → P.Dig) : P.D.X :=
  if h : P.Ext M t y C then P.D.recon y (Classical.choose (Classical.choose_spec h))
  else Classical.arbitrary _

theorem extFrom_spec (hS : P.D.Sound) {t : (P.protocol M).Tables} {y : P.D.Y}
    {C : Fin P.T → Fin (P.D.K + 1) → P.Dig} (h : P.Ext M t y C) :
    P.D.F (P.extFrom M t y C) = y := by
  unfold extFrom
  rw [dif_pos h]
  exact hS y _ (Classical.choose_spec (Classical.choose_spec h)).2

/-- **The straight-line extractor.** It reads the verifier's values of the forgery from the
tables and reconstructs a preimage from the committed views of the digests of its
challenge point. -/
noncomputable def ext (x : P.D.Y) (t : (P.protocol M).Tables) (f : (P.protocol M).Forgery) :
    P.D.X :=
  match verifyVals t.lookup x f.1 f.2 (P.T * P.D.K + 1) [] with
  | some vs => P.extFrom M t x (P.vmat f.2 (vs.take (P.T * P.D.K)))
  | none => Classical.arbitrary _

omit [DecidableEq M] in
theorem vkey_open {y : P.D.Y} {m : M} {σ : P.Sig} {vs : List P.Ch} (j : Fin P.T)
    (i : Fin P.D.K) (h : vs.length = P.oIdx j i) :
    P.vkey M y m σ vs = .inl (j, (σ.1 j).succAbove i, ((σ.2 j).1 i).1, ((σ.2 j).1 i).2) := by
  unfold vkey
  have hlt : vs.length < P.T * P.D.K := h ▸ P.oIdx_lt j i
  rw [dif_pos hlt]
  have hji : finProdFinEquiv.symm (⟨vs.length, hlt⟩ : Fin (P.T * P.D.K)) = (j, i) := by
    rw [Equiv.symm_apply_eq]; exact Fin.ext h
  rw [hji]

omit [DecidableEq M] in
theorem vkey_chal {y : P.D.Y} {m : M} {σ : P.Sig} {vs : List P.Ch}
    (h : vs.length = P.T * P.D.K) : P.vkey M y m σ vs = .inr (y, m, P.vmat σ vs) := by
  unfold vkey
  rw [dif_neg (by omega)]

/-- **Soundness of the extractor.** At a reachable state without the extraction flag, a
winning forgery gives a preimage of the statement. -/
theorem ext_sound (hS : P.D.Sound) {N : ℕ} (x : P.D.Y) (s : SLState (P.protocol M))
    (f : (P.protocol M).Forgery) (hr : SLReach N (P.Bad M) x s) (hf : s.2 = false)
    (hw : wins x (f, s.1) = true) : P.D.F (P.ext M x s.1.1 f) = x := by
  have hI := P.inv_of_reach M hr hf
  obtain ⟨m, σ⟩ := f
  unfold wins at hw
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hw
  obtain ⟨hsig, hv⟩ := hw
  split at hv
  · next vs hvv =>
    obtain ⟨rest, hvs, hlen, hlook⟩ := verifyVals_spec _ x m σ _ [] vs hvv
    simp only [List.nil_append] at hvs hlook
    subst vs
    change rest.length = P.T * P.D.K + 1 at hlen
    change P.verify x σ rest = true at hv
    simp only [verify, Bool.and_eq_true, decide_eq_true_eq] at hv
    obtain ⟨hc, hchk⟩ := hv
    have hT2 : P.T * P.D.K < rest.length := by omega
    have hcl := hlook (P.T * P.D.K) hT2
    change s.1.1.lookup (P.vkey M x m σ _) = _ at hcl
    rw [P.vkey_chal M (by simp; omega)] at hcl
    rw [List.getElem?_eq_getElem hT2] at hc
    simp only [decide_eq_true_eq] at hc
    set Cm := P.vmat σ (rest.take (P.T * P.D.K)) with hCm
    have hhash : (Sum.inr (x, m, Cm), rest[P.T * P.D.K]) ∈ s.1.1.hash := by
      unfold Protocol.Tables.lookup at hcl
      cases hp : lookupIn s.1.1.prog (Sum.inr (x, m, Cm)) with
      | some c' =>
        have := hI.2.2 _ _ _ _ (mem_of_lookupIn_eq_some hp)
        simp [this] at hsig
      | none =>
        rw [hp, Option.none_or] at hcl
        exact mem_of_lookupIn_eq_some hcl
    have hgood : ∀ j, P.Good M s.1.1 x Cm j (σ.1 j) := by
      intro j
      refine ⟨fun i => ((σ.2 j).1 i).2, fun i => ?_, hchk j⟩
      have hj1 : P.oIdx j i < rest.length := by have := P.oIdx_lt j i; omega
      have h1 := hlook (P.oIdx j i) hj1
      change s.1.1.lookup (P.vkey M x m σ _) = _ at h1
      rw [P.vkey_open M j i (by simp; have := P.oIdx_lt j i; omega)] at h1
      refine ⟨((σ.2 j).1 i).1, _, P.mem_ents_of_lookup M h1, ?_⟩
      simp [hCm, vmat, Fin.insertNth_apply_succAbove, P.oIdx_lt j i,
        List.getElem?_eq_getElem hj1]
    rcases hI.2.1 _ _ _ _ hhash with hE | ⟨j, hj⟩
    · unfold ext
      simp only
      rw [hvv]
      exact P.extFrom_spec M hS hE
    · exact absurd (hc ▸ hgood j) hj
  · simp at hv

/-- **The class-wise log extractor of the MPC-in-the-head proof** for the relation
`F w = y` on tables with at most `N` entries: the bad answers have probability at most
`(T(K + 1) + 1)·N/|Dig|` at a commitment point and `(K/(K + 1))^T` at a challenge point,
and the programmed entries of a simulated attempt contain one with probability at most
`T(K + 1)·(T(K + 1) + 1)·N/|Dig| + (K/(K + 1))^T`. -/
noncomputable def logExtractor (hS : P.D.Sound) (hK : 0 < P.D.K) (N : ℕ) :
    (P.protocol M).LogExtractorCls (fun y w => P.D.F w = y) N (P.classes M) (P.epsCls N)
      (((P.T * (P.D.K + 1) : ℕ) : ℝ≥0∞) * P.epsCls N false + P.epsCls N true) where
  ext := P.ext M
  Bad := P.Bad M
  simKey_cls _ _ _ _ _ _ h := by simp at h
  bad_le x t k ht := by
    rcases k with k | ⟨y, m', C⟩
    · exact P.bad_inl_le M x t ht k
    · exact P.bad_inr_le M hK x t y m' C
  simBad_le x t m ht := P.simBad_le M hK x t m ht
  sound x s f hr hf _ hw := P.ext_sound M hS x s f hr hf hw

/-- The costed extractor of `logExtractor`: the extraction `P.ext M x t f` as one step of
cost `tExt`. -/
noncomputable def logExtractor.timed (tExt : ℕ) (x : P.D.Y) (t : (P.protocol M).Tables)
    (f : (P.protocol M).Forgery) : ℕ × SPTree.Timed P.D.X :=
  (tExt, .ret (P.ext M x t f))

/-- The costed extractor erases and compiles to the extractor of `logExtractor`. -/
theorem logExtractor.erase_timed (hS : P.D.Sound) (hK : 0 < P.D.K) (N tExt : ℕ) (x : P.D.Y)
    (t : (P.protocol M).Tables) (f : (P.protocol M).Forgery) :
    (logExtractor.timed P M tExt x t f).2.erase.compile =
      SPComp.pure ((P.logExtractor M hS hK N).ext x t f) := by
  rw [logExtractor.timed, SPTree.Timed.erase_ret, SPTree.compile_ret]
  rfl

/-- **Time of the costed extractor**: `tExt`. -/
theorem logExtractor.timeBound_timed (tExt : ℕ) (x : P.D.Y) (t : (P.protocol M).Tables)
    (f : (P.protocol M).Forgery) :
    SPTree.Timed.stepTime (logExtractor.timed P M tExt x t f) = tExt := by
  rw [logExtractor.timed, SPTree.Timed.stepTime, SPTree.Timed.time_ret, Nat.add_zero]

/-- The simulated traces have at most `T(K + 1) + 1` entries. -/
theorem simTrace_length_le (look : P.Key M → Option P.Ch) (x : P.D.Y) (m : M)
    (e : Fin (P.T * (P.D.K + 1) + 1) → P.Ch) (s : P.SimRand) :
    ((P.protocol M).simTrace look x m e s).1.length +
      ((P.protocol M).simTrace look x m e s).2.1.length ≤ (P.protocol M).μ := by
  rw [simTrace_eq]
  simp only [traceOf, List.length_nil, zero_add, List.length_map]
  exact (List.length_filter_le _ _).trans (by simp)

/-- The number of table entries of a run with `qH` hash and `qS` signing queries, the
verifier's queries included. -/
def tableBound (qH qS : ℕ) : ℕ := qH + (P.T * P.D.K + 1) + (P.T * (P.D.K + 1) + 1) * qS

/-- **EUF-CMA of the MPC-in-the-head signature by straight-line extraction**, in the form
of `fiatShamir_rom_eufcma_slCls`: for a sound and `K`-private decomposition with `K > 0`,
`T > 0`, and every adversary `A` with at most `qH` hash and `qS` signing queries, the
EUF-CMA advantage is at most the relation advantage of the inverter
`slReductionCls (logExtractor hS hK N) A` plus the extraction and signing-hop terms, for
`N = tableBound qH qS`. -/
theorem eufcma_le_raw (hS : P.D.Sound) (hP : P.D.Private) (hK : 0 < P.D.K) (hT : 0 < P.T)
    {qH qS : ℕ} (A : (P.protocol M).Adversary qH qS) :
    eufcmaAdvantage A ≤
      (P.protocol M).relAdvantage (fun y w => P.D.F w = y)
        (slReductionCls (P.logExtractor M hS hK (P.tableBound qH qS)) A) +
      (∑ c, ((qH + (P.classes M).Vc c + (P.classes M).μe c * qS : ℕ) : ℝ≥0∞) *
          P.epsCls (P.tableBound qH qS) c +
        qS * (((P.T * (P.D.K + 1) : ℕ) : ℝ≥0∞) * P.epsCls (P.tableBound qH qS) false +
          P.epsCls (P.tableBound qH qS) true)) +
      ∑' xw, (P.protocol M).gen xw * (qS * 0 +
        ∑ c, ((qS * (qH + (P.classes M).Vc c + (P.classes M).μc c * qS) : ℕ) : ℝ≥0∞) *
          P.gammaCls c) :=
  fiatShamir_rom_eufcma_slCls (P.logExtractor M hS hK _) le_rfl (P.simTrace_length_le M)
    (δ := fun _ => 0) (Γ := fun _ => P.gammaCls)
    (fun xw hxw => by
      obtain ⟨w, -, rfl⟩ := (PMF.mem_support_map_iff _ _ _).mp hxw
      exact P.statHVZKAt M hP w)
    (fun xw _ => P.keyBoundClsAt M hT xw.1 xw.2) A (fun _ => qH)
    (fun x c => (A.isQueryBound x).isQueryBoundBy_left
      (fun k => by simp only [Protocol.Classes.hashCost, Sum.elim_inl]; split_ifs <;> simp)
      fun _ => rfl)

/-! ## The bound -/

/-- The relation advantage of the key relation is the one-wayness advantage of `F`. -/
theorem relAdvantage_eq_owfAdvantage (B : P.D.Y → PMF P.D.X) :
    (P.protocol M).relAdvantage (fun y w => P.D.F w = y) B = P.D.owfAdvantage B := by
  unfold Protocol.relAdvantage Protocol.relGame Decomp.owfAdvantage Decomp.owfGame
  simp only [PMF.bind_map, Function.comp_def]
  congr 3
  funext x
  congr 1
  funext x'
  exact decide_eq_decide.mpr Iff.rfl

/-- **The inverter of the MPC-in-the-head signature.** On the statement `y`, it runs the
forger once in the instrumented simulated game and returns the preimage that the
straight-line extractor reconstructs from the committed views in the random-oracle
log. -/
noncomputable def inverter {qH qS : ℕ} (A : (P.protocol M).Adversary qH qS) :
    P.D.Y → PMF P.D.X :=
  fun x => (OracleAdv.run (toOracle (slStep (P.tableBound qH qS) (P.Bad M) x))
    (withVerify x (A.run x)) ((Protocol.Tables.empty, false), false)).map
      fun y => P.ext M x y.2.1.1 y.1

/-- The inverter is the class-wise straight-line reduction of the log extractor. -/
theorem inverter_eq (hS : P.D.Sound) (hK : 0 < P.D.K) {qH qS : ℕ}
    (A : (P.protocol M).Adversary qH qS) :
    P.inverter M A = slReductionCls (P.logExtractor M hS hK (P.tableBound qH qS)) A := rfl

/-- The costed inverter on the statement `x`: the costed verified run of `A' x` in the
instrumented simulated game, at step cost `tH` per hash and `tS` per signing query and `tV`
per verifier step, followed by the extraction at cost `tOut`. -/
noncomputable def inverter.timed (qH qS tV tH tS tOut : ℕ)
    (A' : P.D.Y → OracleAdv.Timed (P.protocol M).Query (P.protocol M).Answer
      (P.protocol M).Forgery) (x : P.D.Y) : ℕ × OracleAdv.Timed Empty Empty P.D.X :=
  timedRun tV tOut (toOracle (slStep (P.tableBound qH qS) (P.Bad M) x))
    (Sum.elim (fun _ => tH) fun _ => tS) ((Protocol.Tables.empty, false), false)
    (fun y => P.ext M x y.2.1.1 y.1) x (A' x)

/-- Under any oracle, the costed inverter has the output distribution of `inverter A`. -/
theorem inverter.run_erase_timed {qH qS : ℕ} (A : (P.protocol M).Adversary qH qS)
    (A' : P.D.Y → OracleAdv.Timed (P.protocol M).Query (P.protocol M).Answer
      (P.protocol M).Forgery)
    (hA : ∀ x, (A' x).erase = A.run x) (tV tH tS tOut : ℕ) {U : Type}
    (O' : U → Empty → PMF (Empty × U)) (u : U) (x : P.D.Y) :
    (OracleAdv.run O' (inverter.timed P M qH qS tV tH tS tOut A' x).2.erase u).map
      Prod.fst = P.inverter M A x := by
  rw [inverter.timed, timedRun.run_erase, hA]
  rfl

/-- **Time of the costed inverter.** With `A'` of time `T`, the costed inverter has time
at most `T + (tV + V * (tV + 1)) + ((tH + 1) * (qH + V) + (tS + 1) * qS) + tOut`. -/
theorem inverter.timeBound_timed {qH qS : ℕ} (A : (P.protocol M).Adversary qH qS)
    {A' : P.D.Y → OracleAdv.Timed (P.protocol M).Query (P.protocol M).Answer
      (P.protocol M).Forgery}
    (hA : ∀ x, (A' x).erase = A.run x) (tV tH tS tOut : ℕ) {T : ℕ}
    (hT : ∀ x, (A' x).TimeBound T) (x : P.D.Y) :
    OracleAdv.Timed.StepTimeBound (inverter.timed P M qH qS tV tH tS tOut A' x)
      (T + (tV + (P.protocol M).V * (tV + 1)) +
        ((tH + 1) * (qH + (P.protocol M).V) + (tS + 1) * qS) + tOut) := by
  have hq : IsQueryBound₂ (A' x).erase qH qS := by
    rw [hA]; exact A.isQueryBound x
  exact timedRun.timeBound (G := P.protocol M) tV tOut
    (toOracle (slStep (P.tableBound qH qS) (P.Bad M) x)) (Sum.elim (fun _ => tH) fun _ => tS)
    ((Protocol.Tables.empty, false), false) (fun y => P.ext M x y.2.1.1 y.1) x
    (tH := tH) (tS := tS) (fun _ => le_rfl) (hT x) hq

/-- The statistical terms of the bound for `qH` hash and `qS` signing queries, with
`N = tableBound qH qS`, `ε_C = (T(K + 1) + 1)·N/|Dig|`, `ε_H = (K/(K + 1))^T`,
`Γ_C = T(K + 1)·2/|Salt|` and `Γ_H = 1/|Dig|`:
`(qH + 1)·ε_H + (qH + TK)·ε_C + qS·(T(K + 1)·ε_C + ε_H)
  + qS·(qH + 1 + qS)·Γ_H + qS·(qH + TK + T(K + 1)·qS)·Γ_C`. -/
noncomputable def statTerm (qH qS : ℕ) : ℝ≥0∞ :=
  ((qH + 1 : ℕ) : ℝ≥0∞) * P.epsCls (P.tableBound qH qS) true +
    ((qH + P.T * P.D.K : ℕ) : ℝ≥0∞) * P.epsCls (P.tableBound qH qS) false +
    qS * (((P.T * (P.D.K + 1) : ℕ) : ℝ≥0∞) * P.epsCls (P.tableBound qH qS) false +
      P.epsCls (P.tableBound qH qS) true) +
    (((qS * (qH + 1 + 1 * qS)) : ℕ) * P.gammaCls true +
      ((qS * (qH + P.T * P.D.K + P.T * (P.D.K + 1) * qS) : ℕ) : ℝ≥0∞) * P.gammaCls false)

theorem classes_μe (c : Bool) : (P.classes M).μe c = 0 := by
  simp [Protocol.Classes.μe]

theorem classes_Vc_false : (P.classes M).Vc false ≤ P.T * P.D.K := by
  unfold Protocol.Classes.Vc
  refine (Finset.card_le_card (t := Finset.univ.erase (Fin.last _)) ?_).trans ?_
  · intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    change decide (P.T * P.D.K ≤ j.val) = false at hj
    refine Finset.mem_erase.mpr ⟨fun h => ?_, Finset.mem_univ _⟩
    rw [h] at hj
    simp at hj
  · rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    omega

theorem classes_Vc_true : (P.classes M).Vc true ≤ 1 := by
  unfold Protocol.Classes.Vc
  refine Finset.card_le_one.mpr fun a ha b hb => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  change decide (P.T * P.D.K ≤ a.val) = true at ha
  change decide (P.T * P.D.K ≤ b.val) = true at hb
  simp only [decide_eq_true_eq] at ha hb
  ext; have := a.isLt; have := b.isLt; omega

theorem classes_μc_false : (P.classes M).μc false ≤ P.T * (P.D.K + 1) := by
  unfold Protocol.Classes.μc
  refine (Finset.card_le_card (t := Finset.univ.erase (Fin.last _)) ?_).trans ?_
  · intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    change (P.kind i).isNone = false at hi
    refine Finset.mem_erase.mpr ⟨fun h => ?_, Finset.mem_univ _⟩
    rw [h, kind_last] at hi
    simp at hi
  · rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    omega

theorem sum_classes (f : (P.classes M).ι → ℝ≥0∞) : ∑ c, f c = f true + f false :=
  Fintype.sum_bool f

theorem classes_μc_true : (P.classes M).μc true ≤ 1 := by
  unfold Protocol.Classes.μc
  refine Finset.card_le_one.mpr fun a ha b hb => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha hb
  change (P.kind a).isNone = true at ha
  change (P.kind b).isNone = true at hb
  rw [P.kind_eq_none (Option.isNone_iff_eq_none.mp ha),
    P.kind_eq_none (Option.isNone_iff_eq_none.mp hb)]

/-- **EUF-CMA of MPC-in-the-head signatures in the random-oracle model.** For a sound and
perfectly `K`-private decomposition of `F` with `K + 1 ≥ 2` parties, `T > 0` repetitions,
and every adversary `A` with at most `qH` hash and `qS` signing queries,

`eufcmaAdvantage A ≤ owfAdvantage F (inverter A) + statTerm qH qS`,

where `inverter A` runs `A` once in the instrumented simulated game and reconstructs a
preimage from the committed views in the random-oracle log, without rewinding. -/
theorem eufcma_le (hS : P.D.Sound) (hP : P.D.Private) (hK : 0 < P.D.K) (hT : 0 < P.T)
    {qH qS : ℕ} (A : (P.protocol M).Adversary qH qS) :
    eufcmaAdvantage A ≤ P.D.owfAdvantage (P.inverter M A) + P.statTerm qH qS := by
  refine (P.eufcma_le_raw M hS hP hK hT A).trans ?_
  rw [P.relAdvantage_eq_owfAdvantage M, mul_zero, zero_add]
  simp only [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul, sum_classes, classes_μe,
    zero_mul, add_zero]
  rw [add_assoc]
  unfold statTerm
  have h1 := P.classes_Vc_false M
  have h2 := P.classes_Vc_true M
  have h3 := P.classes_μc_false M
  have h4 := P.classes_μc_true M
  change P.D.owfAdvantage (P.inverter M A) + _ ≤ _
  gcongr

end Params

/-! ## The verification games of a forger -/

section Games

open CatCrypt.Crypto.UCConcrete

/-- The real verification game of the forger `A` of a Fiat–Shamir protocol: its EUF-CMA
game in the random-oracle model. -/
noncomputable def forgeReal {G : Protocol} {qH qS : ℕ} (A : G.Adversary qH qS) :
    Unit → SPComp Bool :=
  fun _ => eufcmaGame A

/-- The ideal verification game: every forgery is rejected. -/
noncomputable def forgeIdeal : Unit → SPComp Bool :=
  fun _ => SPComp.pure false

/-- The real verification game is heap-independent. -/
instance forgeReal_pureGame {G : Protocol} {qH qS : ℕ} (A : G.Adversary qH qS) :
    PureGame (forgeReal A) :=
  ⟨fun _ => liftPMF_isPure _⟩

/-- The ideal verification game is heap-independent. -/
instance forgeIdeal_pureGame : PureGame forgeIdeal :=
  ⟨fun _ => SPComp.pure_isPure false⟩

end Games

end CatCrypt.Crypto.FiatShamirROM.MPCitH
