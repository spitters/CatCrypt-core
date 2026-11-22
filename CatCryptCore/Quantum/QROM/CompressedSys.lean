/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Quantum.QROM.AdaptiveModel
public import CatCryptCore.Quantum.QROM.CompressedOracleLocal
public import CatCryptCore.Quantum.QOTPReactive
public import CatCryptCore.Quantum.QRealizesInvariant

/-!
# The compressed oracle as a quantum reactive system

The compressed challenger `cmpSys s₀ sig` holds the database of Zhandry's compressed oracle
(CRYPTO 2019) in its private register `Fin ((n + 1) ^ m)`, started at the empty database. A
query applies the per-query compressed oracle `cmpLocalU`. A round with message `y` runs the
signer program `sig s y` of the classical state `s`, a program `RWProg` over two internal
operations on the database: `read x` decompresses the entry `x`, measures it in the
computational basis and compresses it again; `write x v` decompresses the entry `x`, sets it
to `v` and compresses it again.

The classical challenger `chalRW s₀ sig H` runs the same signer against the function `H`,
which it keeps in its classical state: `read x` returns `H x` and `write x v` replaces `H` by
`H[x ↦ v]`.

## Main definitions

* `RWProg`, `RWProg.run`, `RWProg.ops` — signer programs over `read` and `write`, their run
  against a function, and their number of operations
* `readK`, `writeK` — the Kraus operators of `read` and `write` on the database register
* `cmpSys`, `chalRW` — the compressed challenger and the classical challenger
* `purSys` — the challenger on the decompressed database
* `dbLe N` — the databases with at most `N` non-`⊥` entries

## Main results

* `read_weight_le`, `write_weight_le` — the Kraus operators of `read` and `write` add at most
  one non-`⊥` database entry
* `cmpSys_weight_le` — after `k` activations, each a query or a round whose program has at
  most `b` operations, a state supported on the databases with at most `N` non-`⊥` entries is
  supported on the databases with at most `N + k * max 1 b` such entries
* `qloop_decConj` — the run against `cmpSys` is the run against `purSys` conjugated by the
  decompression of the database
* `qloop_purSys_dephComm` — the run against `purSys` commutes with dephasing the database
* `qloop_sim`, `qview_chalRW` — a system that keeps a classical value in a basis state of its
  register is simulated by a classical system; `purSys` from the database of `H` is `chalRW H`
* `qview_cmpSys_eq_sample`, `view_cmpSys_eq_avg` — the view of an environment against the
  compressed challenger is the view against the classical challenger for a uniformly random
  function `H`

## References

* [Zhandry — How to Record Quantum Queries, and Applications to Quantum
  Indifferentiability, CRYPTO 2019]
* [Barbosa, Barthe, Doczkal, Don, Fehr, Grégoire, Huang, Hülsing, Lee, Wu — Fixing and
  Mechanizing the Security Proof of Fiat-Shamir with Aborts and Dilithium, CRYPTO 2023, ePrint
  2023/246],
  properties (1) and (2) of the compressed oracle with reprogramming
-/

@[expose] public section

set_option autoImplicit false

open scoped Matrix ComplexOrder ENNReal
open Matrix CatCrypt.Quantum CatCrypt.Quantum.UnitaryChannel
open _root_.Quantum CatCrypt.Quantum.ReactiveUC
open CatCrypt.Quantum.OpenSystem (frameLeft frameLeft_branch frameLeft_bind frameLeft_pure)
open CatCrypt.Quantum.QOTPReactive (unitaryOp frame_frameLeft_bind_comm discardOp
  frameLeft_unitaryOp_bind_discardOp)

noncomputable section

namespace CatCrypt.Quantum.QROM

/-! ## Kraus measurements on a product register -/

section Kraus

variable {L X : Type} [Fintype L] [DecidableEq L]
variable {ι : Type} [Fintype ι]

/-- The operator `1_L ⊗ K` on `L × X`. -/
def liftL (L : Type) [DecidableEq L] (K : Matrix X X ℂ) : Matrix (L × X) (L × X) ℂ :=
  Matrix.of fun x y => if x.1 = y.1 then K x.2 y.2 else 0

omit [Fintype L] in
/-- Unfolding lemma of `liftL`. -/
theorem liftL_apply (K : Matrix X X ℂ) (x y : L × X) :
    liftL L K x y = if x.1 = y.1 then K x.2 y.2 else 0 := rfl

theorem liftL_conjTranspose_mul [Fintype X] (K M : Matrix X X ℂ) :
    (liftL L K)ᴴ * liftL L M = liftL L (Kᴴ * M) := by
  ext x y
  simp only [Matrix.mul_apply, conjTranspose_apply, liftL_apply, Fintype.sum_prod_type]
  simp [apply_ite (starRingEnd ℂ), ite_mul, Finset.sum_ite_eq', eq_comm]

theorem liftL_mul [Fintype X] (K M : Matrix X X ℂ) :
    liftL L K * liftL L M = liftL L (K * M) := by
  ext x y
  simp only [Matrix.mul_apply, liftL_apply, Fintype.sum_prod_type]
  simp_all

omit [Fintype L] in
theorem liftL_conjTranspose (K : Matrix X X ℂ) : (liftL L K)ᴴ = liftL L Kᴴ := by
  ext x y
  simp only [conjTranspose_apply, liftL_apply]
  grind

omit [Fintype L] in
theorem liftL_one [DecidableEq X] : liftL L (1 : Matrix X X ℂ) = 1 := by
  ext x y
  simp only [liftL_apply, Matrix.one_apply, Prod.ext_iff]
  grind

omit [Fintype L] in
theorem liftL_sum (K : ι → Matrix X X ℂ) : ∑ i, liftL L (K i) = liftL L (∑ i, K i) := by
  ext x y
  simp only [Matrix.sum_apply, liftL_apply]
  by_cases h : x.1 = y.1 <;> simp [h]

variable [Fintype X] [DecidableEq X]

theorem liftL_complete (K : ι → Matrix X X ℂ) (hK : ∑ i, (K i)ᴴ * K i = 1) :
    ∑ i, (liftL L (K i))ᴴ * liftL L (K i) = 1 := by
  simp only [liftL_conjTranspose_mul, liftL_sum, hK, liftL_one]

/-- A Kraus measurement placed on the right factor is the Kraus measurement of the operators
`1_L ⊗ K i`. -/
theorem frameLeft_ofKraus (K : ι → Matrix X X ℂ) (hK : ∑ i, (K i)ᴴ * K i = 1) :
    frameLeft (SubInstrument.ofKraus K hK) L =
      SubInstrument.ofKraus (fun i => liftL L (K i)) (liftL_complete K hK) := by
  refine DSubInstrument.ext <| funext fun i => LinearMap.ext fun ρ => ?_
  ext x y
  simp only [frameLeft_branch, MatrixMap.amplifyLeft_apply, DSubInstrument.branch_ofKraus_apply,
    MatrixMap.conj_apply, Matrix.mul_apply, conjTranspose_apply, liftL_apply, submatrix_apply,
    Fintype.sum_prod_type]
  simp [ite_mul, apply_ite star, mul_ite, Finset.sum_ite_eq]

/-- The branch of a subinstrument with one outcome followed by `Y ()`. -/
theorem bind_unit_branch_apply {A B C : Type} [Fintype A] [Fintype B] [Fintype C] {α : Type}
    (q : SubInstrument A B Unit) (Y : Unit → SubInstrument B C α) (a : α) (ρ : Matrix A A ℂ) :
    (q.bind Y).branch a ρ = (Y ()).branch a (q.branch () ρ) := by
  rw [SubInstrument.bind, DSubInstrument.branch_bind_apply_univ]
  simp

/-- The branch of `Y` followed by a subinstrument with one outcome that returns the outcome
of `Y`. -/
theorem bind_unit_pure_branch_apply {A B C : Type} [Fintype A] [Fintype B] [Fintype C]
    {α : Type} (Y : SubInstrument A B α) (q : SubInstrument B C Unit) (a : α)
    (ρ : Matrix A A ℂ) :
    (Y.bind fun b => q.bind fun _ => SubInstrument.pure b).branch a ρ =
      q.branch () (Y.branch a ρ) := by
  classical
  rw [SubInstrument.bind, DSubInstrument.branch_bind_apply]
  rw [tsum_eq_single a fun i hi => by
      rw [bind_unit_branch_apply, SubInstrument.branch_pure_of_ne (Ne.symm hi)]; rfl,
    bind_unit_branch_apply, SubInstrument.branch_pure_self]
  rfl

/-- The composite of a unitary, a Kraus measurement and a unitary is the Kraus measurement of
the conjugated operators. -/
theorem unitaryOp_bind_ofKraus_bind (A : Matrix X X ℂ) (hA : Aᴴ * A = 1)
    (K : ι → Matrix X X ℂ) (hK : ∑ i, (K i)ᴴ * K i = 1) (B : Matrix X X ℂ) (hB : Bᴴ * B = 1)
    (h : ∑ i, (B * K i * A)ᴴ * (B * K i * A) = 1) :
    (unitaryOp A hA).bind (fun _ => (SubInstrument.ofKraus K hK).bind fun i =>
      (unitaryOp B hB).bind fun _ => SubInstrument.pure i) =
      SubInstrument.ofKraus (fun i => B * K i * A) h := by
  refine DSubInstrument.ext <| funext fun i => LinearMap.ext fun ρ => ?_
  rw [bind_unit_branch_apply, bind_unit_pure_branch_apply]
  simp only [unitaryOp, DSubInstrument.branch_ofKraus_apply, MatrixMap.conj_apply,
    conjTranspose_mul, Matrix.mul_assoc]

/-- The completeness relation of conjugated Kraus operators. -/
theorem conj_complete (A : Matrix X X ℂ) (hA : Aᴴ * A = 1) (K : ι → Matrix X X ℂ)
    (hK : ∑ i, (K i)ᴴ * K i = 1) (B : Matrix X X ℂ) (hB : Bᴴ * B = 1) :
    ∑ i, (B * K i * A)ᴴ * (B * K i * A) = 1 := by
  have : ∀ i, (B * K i * A)ᴴ * (B * K i * A) = Aᴴ * ((K i)ᴴ * K i) * A := fun i => by
    simp only [conjTranspose_mul, Matrix.mul_assoc]
    rw [← Matrix.mul_assoc Bᴴ B, hB, Matrix.one_mul]
  simp only [this, ← Finset.sum_mul, ← Finset.mul_sum, hK, Matrix.mul_one, hA]

end Kraus

/-! ## Dephasing a register -/

section Dephase

variable {L X : Type} [Fintype L] [DecidableEq L] [Fintype X] [DecidableEq X]

theorem single_complete : ∑ r : X, (Matrix.single r r (1 : ℂ))ᴴ * Matrix.single r r 1 = 1 := by
  ext x y
  simp only [Matrix.sum_apply, Matrix.mul_apply, conjTranspose_apply, single_apply,
    Matrix.one_apply]
  simp [ite_and, eq_comm]

/-- Dephasing of the register `X` in its basis: the measurement of the basis state with the
outcome discarded. -/
def dephase (X : Type) [Fintype X] [DecidableEq X] : SubInstrument X X Unit :=
  (SubInstrument.ofKraus (fun r : X => Matrix.single r r (1 : ℂ)) single_complete).bind
    fun _ => SubInstrument.pure ()

theorem dephase_branch_apply (ρ : Matrix X X ℂ) (x y : X) :
    (dephase X).branch () ρ x y = if x = y then ρ x x else 0 := by
  rw [dephase, SubInstrument.bind, DSubInstrument.branch_bind_apply_univ]
  simp [Matrix.sum_apply, single_apply]
  simp [ite_and, eq_comm]

omit [DecidableEq L] in
/-- Dephasing of the right factor of `L × X`, entrywise. -/
theorem frameLeft_dephase_apply (ρ : Matrix (L × X) (L × X) ℂ) (x y : L × X) :
    (frameLeft (dephase X) L).branch () ρ x y = if x.2 = y.2 then ρ x y else 0 := by
  rw [frameLeft_branch, MatrixMap.amplifyLeft_apply, dephase_branch_apply]
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  simp only [submatrix_apply]
  split_ifs with h <;> simp_all

/-- The subinstrument `Y` on `L × X` **commutes with dephasing** the right factor. -/
def DephComm (L X : Type) [Fintype L] [DecidableEq L] [Fintype X] [DecidableEq X] {α : Type}
    (Y : SubInstrument (L × X) (L × X) α) : Prop :=
  (frameLeft (dephase X) L).bind (fun _ => Y) =
    Y.bind fun a => (frameLeft (dephase X) L).bind fun _ => SubInstrument.pure a

theorem DephComm.pure {α : Type} (a : α) :
    DephComm L X (SubInstrument.pure a : SubInstrument (L × X) (L × X) α) := by
  simp only [DephComm, SubInstrument.pure_bind]

theorem DephComm.bind {α β : Type} {Y : SubInstrument (L × X) (L × X) α}
    {f : α → SubInstrument (L × X) (L × X) β} (hY : DephComm L X Y)
    (hf : ∀ a, DephComm L X (f a)) : DephComm L X (Y.bind f) := by
  unfold DephComm at *
  rw [← SubInstrument.bind_assoc, hY, SubInstrument.bind_assoc]
  simp only [SubInstrument.bind_assoc, SubInstrument.pure_bind, hf]

theorem dephComm_frame {α : Type} (W : SubInstrument L L α) : DephComm L X (W.frame X) := by
  have h := frame_frameLeft_bind_comm W (dephase X) fun a _ => SubInstrument.pure a
  unfold DephComm
  simp only [SubInstrument.bind_pure] at h
  exact h.symm

/-- A Kraus measurement whose operators relate basis states of the right factor by a partial
bijection commutes with dephasing the right factor. -/
theorem dephComm_ofKraus {ι : Type} [Fintype ι] (K : ι → Matrix (L × X) (L × X) ℂ)
    (hK : ∑ i, (K i)ᴴ * K i = 1)
    (hb : ∀ i x y u v, K i x u ≠ 0 → K i y v ≠ 0 → (x.2 = y.2 ↔ u.2 = v.2)) :
    DephComm L X (SubInstrument.ofKraus K hK) := by
  refine DSubInstrument.ext <| funext fun i => LinearMap.ext fun ρ => ?_
  rw [bind_unit_branch_apply, bind_unit_pure_branch_apply]
  ext x y
  simp only [DSubInstrument.branch_ofKraus_apply, MatrixMap.conj_apply, frameLeft_dephase_apply,
    Matrix.mul_apply, conjTranspose_apply, Finset.sum_mul]
  split_ifs with h
  · refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
    by_cases hk : K i x k = 0
    · simp [hk]
    by_cases hj : K i y j = 0
    · simp [hj]
    rw [ite_eq_left ((hb i x y k j hk hj).mp h)]
  · refine Finset.sum_eq_zero fun j _ => Finset.sum_eq_zero fun k _ => ?_
    by_cases hk : K i x k = 0
    · simp [hk]
    by_cases hj : K i y j = 0
    · simp [hj]
    rw [ite_eq_right fun hkj => h ((hb i x y k j hk hj).mpr hkj)]
    simp

end Dephase

/-! ## Supports -/

section Supp

variable {A B : Type} [Fintype A] [Fintype B]

theorem MapsSupp.bind' {C : Type} [Fintype C] {α β : Type} {s : SubInstrument A B α}
    {k : α → SubInstrument B C β} {S : Set A} {S' : α → Set B} {S'' : β → Set C}
    (hs : MapsSupp s S S') (hk : ∀ a, MapsSupp (k a) (S' a) S'') :
    MapsSupp (s.bind k) S S'' := by
  intro c M hM x y hxy
  rw [SubInstrument.bind, DSubInstrument.branch_bind_apply] at hxy
  by_cases hsum : Summable fun a => (k a).branch c (s.branch a M)
  · rw [Matrix.tsum_apply_apply hsum] at hxy
    by_contra hc
    refine hxy ?_
    have h0 : ∀ a, (k a).branch c (s.branch a M) x y = 0 := fun a => by
      by_contra ha
      exact hc (hk a c _ (hs a M hM) x y ha)
    simp [h0]
  · rw [tsum_eq_zero_of_not_summable hsum] at hxy
    exact absurd rfl hxy

theorem mapsSupp_pure {α : Type} (a : α) (S : Set A) :
    MapsSupp (SubInstrument.pure a : SubInstrument A A α) S fun _ => S := by
  intro b M hM x y hxy
  classical
  by_cases h : b = a
  · subst h
    rw [SubInstrument.branch_pure_self] at hxy
    exact hM x y hxy
  · rw [SubInstrument.branch_pure_of_ne h] at hxy
    exact absurd rfl hxy

theorem mapsSupp_ofKraus [DecidableEq A] {ι : Type} [Fintype ι] (K : ι → Matrix A A ℂ)
    (hK : ∑ i, (K i)ᴴ * K i = 1) (S : Set A) (S' : ι → Set A)
    (h : ∀ i x u, K i x u ≠ 0 → u ∈ S → x ∈ S' i) :
    MapsSupp (SubInstrument.ofKraus K hK) S S' := by
  intro i M hM x y hxy
  rw [DSubInstrument.branch_ofKraus_apply, MatrixMap.conj_apply, Matrix.mul_apply] at hxy
  obtain ⟨j, -, hj⟩ := Finset.exists_ne_zero_of_sum_ne_zero hxy
  have hj1 := left_ne_zero_of_mul hj
  have hj2 := right_ne_zero_of_mul hj
  rw [Matrix.mul_apply] at hj1
  obtain ⟨u, -, hu⟩ := Finset.exists_ne_zero_of_sum_ne_zero hj1
  have hMu := hM u j (right_ne_zero_of_mul hu)
  rw [conjTranspose_apply] at hj2
  exact ⟨h i x u (left_ne_zero_of_mul hu) hMu.1,
    h i y j (fun h0 => hj2 (by simp [h0])) hMu.2⟩

end Supp

/-! ## Operations on the database register -/

section Db

variable {m n : ℕ}

theorem decompDB_conjTranspose : (decompDB m n)ᴴ = decompDB m n := by
  rw [decompDB_eq_dbOp, dbOp_conjTranspose]
  simp only [decompEntry_conjTranspose]

theorem decompDB_mul_self [NeZero n] : decompDB m n * decompDB m n = 1 := by
  have h := decompDB_mul_conjTranspose m n
  rwa [decompDB_conjTranspose] at h

theorem decompDB_conjTranspose_mul_self [NeZero n] : (decompDB m n)ᴴ * decompDB m n = 1 := by
  rw [decompDB_conjTranspose, decompDB_mul_self]

/-- Conjugating an operator on the entry `x` by the decompression of the database
decompresses the entry `x` alone. -/
theorem decompDB_mul_dbOp_update_mul [NeZero n] (x : Fin m)
    (Z : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    decompDB m n * dbOp m n (Function.update 1 x Z) * decompDB m n =
      dbOp m n (Function.update 1 x (decompEntry n * Z * decompEntry n)) := by
  rw [decompDB_eq_dbOp, dbOp_mul, dbOp_mul]
  congr 1
  funext x'
  by_cases hx : x' = x
  · subst hx; simp
  · simp [Function.update_of_ne hx, decompEntry_mul_self]

theorem dbOp_update_conjTranspose_mul (x : Fin m)
    (Z W : Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) :
    (dbOp m n (Function.update 1 x Z))ᴴ * dbOp m n (Function.update 1 x W) =
      dbOp m n (Function.update 1 x (Zᴴ * W)) := by
  rw [dbOp_conjTranspose, dbOp_mul]
  congr 1
  funext x'
  by_cases hx : x' = x
  · subst hx; simp
  · simp [Function.update_of_ne hx]

/-- The database index `k` with the entry `x` replaced by `a`. -/
def dbSet (k : Fin ((n + 1) ^ m)) (x : Fin m) (a : Fin (n + 1)) : Fin ((n + 1) ^ m) :=
  dbIndex m n (Function.update ((dbIndex m n).symm k) x a)

/-- The entries of the operator `|a⟩⟨b|` on the entry `x`. -/
theorem dbOp_update_single_apply (x : Fin m) (a b : Fin (n + 1)) (i j : Fin ((n + 1) ^ m)) :
    dbOp m n (Function.update 1 x (Matrix.single a b 1)) i j =
      if (dbIndex m n).symm j x = b ∧ i = dbSet j x a then 1 else 0 := by
  rw [dbOp_apply]
  split_ifs with h
  · obtain ⟨hb, rfl⟩ := h
    refine Finset.prod_eq_one fun x' _ => ?_
    by_cases hx : x' = x
    · subst hx; simp [dbSet, hb]
    · simp [dbSet, Function.update_of_ne hx]
  · by_cases hx : (dbIndex m n).symm i x = a ∧ (dbIndex m n).symm j x = b
    · have : ∃ x', x' ≠ x ∧ (dbIndex m n).symm i x' ≠ (dbIndex m n).symm j x' := by
        by_contra hc
        push Not at hc
        refine h ⟨hx.2, (Equiv.symm_apply_eq _).mp (funext fun x' => ?_)⟩
        by_cases hx' : x' = x
        · subst hx'; simp [hx.1]
        · rw [Function.update_of_ne hx']; exact hc x' hx'
      obtain ⟨x', hx', hne⟩ := this
      exact Finset.prod_eq_zero (Finset.mem_univ x') (by
        rw [Function.update_of_ne hx', Pi.one_apply, Matrix.one_apply, ite_eq_right hne])
    · exact Finset.prod_eq_zero (Finset.mem_univ x) (by
        rw [Function.update_self, single_apply, ite_eq_right fun h' => hx ⟨h'.1.symm, h'.2.symm⟩])

/-- The Kraus operator of the decompressed read of the entry `x` with outcome `c`: the
projector onto the databases whose entry `x` is `c`. -/
def readP (x : Fin m) (c : Fin (n + 1)) : Matrix (Fin ((n + 1) ^ m)) (Fin ((n + 1) ^ m)) ℂ :=
  dbOp m n (Function.update 1 x (Matrix.single c c 1))

/-- The Kraus operator of the decompressed write of `v` at the entry `x` on the old value
`u`: the operator `|v⟩⟨u|` on the entry `x`. -/
def writeP (x : Fin m) (v : Fin n) (u : Fin (n + 1)) :
    Matrix (Fin ((n + 1) ^ m)) (Fin ((n + 1) ^ m)) ℂ :=
  dbOp m n (Function.update 1 x (Matrix.single v.castSucc u 1))

theorem readP_complete (x : Fin m) : ∑ c, (readP (n := n) x c)ᴴ * readP x c = 1 := by
  simp only [readP, dbOp_update_conjTranspose_mul]
  simp only [conjTranspose_single, star_one, single_mul_single_same, mul_one,
    dbOp_update_single]
  rw [Finset.sum_comm]
  simp only [Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  exact sum_single_diag_one

theorem writeP_complete (x : Fin m) (v : Fin n) :
    ∑ u, (writeP x v u)ᴴ * writeP x v u = 1 := by
  simp only [writeP, dbOp_update_conjTranspose_mul, conjTranspose_single, star_one,
    single_mul_single_same, mul_one]
  simpa only [readP, dbOp_update_conjTranspose_mul, conjTranspose_single, star_one,
    single_mul_single_same, mul_one] using readP_complete (n := n) x

variable [NeZero n]

/-- The Kraus operator of `read x` with outcome `c`: decompress the entry `x`, project onto
the value `c`, compress. -/
def readK (x : Fin m) (c : Fin (n + 1)) : Matrix (Fin ((n + 1) ^ m)) (Fin ((n + 1) ^ m)) ℂ :=
  decompDB m n * readP x c * decompDB m n

/-- The Kraus operator of `write x v` on the old value `u`: decompress the entry `x`, move the
value `u` to `v`, compress. -/
def writeK (x : Fin m) (v : Fin n) (u : Fin (n + 1)) :
    Matrix (Fin ((n + 1) ^ m)) (Fin ((n + 1) ^ m)) ℂ :=
  decompDB m n * writeP x v u * decompDB m n

theorem readK_complete (x : Fin m) : ∑ c, (readK (n := n) x c)ᴴ * readK x c = 1 :=
  conj_complete _ decompDB_conjTranspose_mul_self _ (readP_complete x) _
    decompDB_conjTranspose_mul_self

theorem writeK_complete (x : Fin m) (v : Fin n) : ∑ u, (writeK x v u)ᴴ * writeK x v u = 1 :=
  conj_complete _ decompDB_conjTranspose_mul_self _ (writeP_complete x v) _
    decompDB_conjTranspose_mul_self

/-- **Weight bound of `read`.** A Kraus operator of `read x` adds at most one non-`⊥`
database entry. -/
theorem read_weight_le (d : ℕ) (x : Fin m) (c : Fin (n + 1)) :
    WeightBound (m := m) (n := n)
      (TensorProduct.kronecker (1 : Matrix (Fin d) (Fin d) ℂ) (readK x c)) 1 :=
  weightBound_kronecker _ _ 1 fun a b hab => dbWeight_le_of_dbOp_update x _ a b (by
    rwa [readK, readP, decompDB_mul_dbOp_update_mul] at hab)

/-- **Weight bound of `write`.** A Kraus operator of `write x v` adds at most one non-`⊥`
database entry. -/
theorem write_weight_le (d : ℕ) (x : Fin m) (v : Fin n) (u : Fin (n + 1)) :
    WeightBound (m := m) (n := n)
      (TensorProduct.kronecker (1 : Matrix (Fin d) (Fin d) ℂ) (writeK x v u)) 1 :=
  weightBound_kronecker _ _ 1 fun a b hab => dbWeight_le_of_dbOp_update x _ a b (by
    rwa [writeK, writeP, decompDB_mul_dbOp_update_mul] at hab)

/-- The operation `read x` on the database register, with the measured value as outcome. -/
def readOp (x : Fin m) :
    SubInstrument (Fin ((n + 1) ^ m)) (Fin ((n + 1) ^ m)) (Fin (n + 1)) :=
  SubInstrument.ofKraus (readK x) (readK_complete x)

/-- The operation `write x v` on the database register. -/
def writeOp (x : Fin m) (v : Fin n) :
    SubInstrument (Fin ((n + 1) ^ m)) (Fin ((n + 1) ^ m)) Unit :=
  (SubInstrument.ofKraus (writeK x v) (writeK_complete x v)).bind fun _ => SubInstrument.pure ()

/-- The decompressed read: the measurement of the entry `x`. -/
def readOpP (x : Fin m) :
    SubInstrument (Fin ((n + 1) ^ m)) (Fin ((n + 1) ^ m)) (Fin (n + 1)) :=
  SubInstrument.ofKraus (readP x) (readP_complete x)

/-- The decompressed write: the entry `x` is set to `v`. -/
def writeOpP (x : Fin m) (v : Fin n) :
    SubInstrument (Fin ((n + 1) ^ m)) (Fin ((n + 1) ^ m)) Unit :=
  (SubInstrument.ofKraus (writeP x v) (writeP_complete x v)).bind fun _ => SubInstrument.pure ()

end Db

/-! ## Signer programs -/

/-- A program over the random oracle with the operations `read x`, which returns a value of
the oracle at `x`, and `write x v`, which reprograms the oracle at `x` to `v`. -/
inductive RWProg (m n : ℕ) (α : Type) where
  /-- Return `a`. -/
  | ret (a : α)
  /-- Read the oracle at `x`, continue with the value. -/
  | read (x : Fin m) (k : Fin n → RWProg m n α)
  /-- Reprogram the oracle at `x` to `v`, continue. -/
  | write (x : Fin m) (v : Fin n) (k : RWProg m n α)

namespace RWProg

variable {m n : ℕ} {α : Type}

/-- The run of a program against the function `H`: the result and the reprogrammed
function. -/
def run : RWProg m n α → (Fin m → Fin n) → α × (Fin m → Fin n)
  | ret a, H => (a, H)
  | read x k, H => (k (H x)).run H
  | write x v k, H => k.run (Function.update H x v)

/-- The largest number of operations on a path of the program. -/
def ops : RWProg m n α → ℕ
  | ret _ => 0
  | read _ k => Finset.univ.sup (fun v => (k v).ops) + 1
  | write _ _ k => k.ops + 1

/-- The run of a program on a register with the operations `rd` and `wr`; the value of
`read x` is the measured entry, `⊥` read as `0`. -/
def exec [NeZero n] {Y : Type} [Fintype Y] (rd : Fin m → SubInstrument Y Y (Fin (n + 1)))
    (wr : Fin m → Fin n → SubInstrument Y Y Unit) : RWProg m n α → SubInstrument Y Y α
  | ret a => SubInstrument.pure a
  | read x k => (rd x).bind fun c => (k (truncEntry n c)).exec rd wr
  | write x v k => (wr x v).bind fun _ => k.exec rd wr

end RWProg

/-! ## Unitaries and relabelling as Kraus measurements -/

section Relabel

/-- A unitary channel is the Kraus measurement of its unitary. -/
theorem unitary_eq_ofKraus {k : ℕ} (U : Matrix.unitaryGroup (Fin k) ℂ) :
    CPComp.unitary U = SubInstrument.ofKraus (fun _ : Unit => (U : Matrix (Fin k) (Fin k) ℂ))
      (by simp [← star_eq_conjTranspose, Matrix.mem_unitaryGroup_iff'.mp U.prop]) := by
  refine DSubInstrument.ext <| funext fun _ => LinearMap.ext fun ρ => ?_
  simp [CPComp.unitary, unitaryChannel, conjugate_apply]

theorem submatrix_complete {X Y ι : Type} [Fintype X] [DecidableEq X] [Fintype Y]
    [DecidableEq Y] [Fintype ι] (e : X ≃ Y) (K : ι → Matrix X X ℂ)
    (hK : ∑ i, (K i)ᴴ * K i = 1) :
    ∑ i, ((K i).submatrix e.symm e.symm)ᴴ * (K i).submatrix e.symm e.symm = 1 := by
  simp only [conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
  rw [show (∑ i, ((K i)ᴴ * K i).submatrix e.symm e.symm) =
      (∑ i, (K i)ᴴ * K i).submatrix e.symm e.symm by ext; simp [Matrix.sum_apply],
    hK, submatrix_one_equiv]

/-- Relabelling a Kraus measurement relabels its operators. -/
theorem relabel_ofKraus {X Y ι : Type} [Fintype X] [DecidableEq X] [Fintype Y]
    [DecidableEq Y] [Fintype ι] (e : X ≃ Y) (K : ι → Matrix X X ℂ)
    (hK : ∑ i, (K i)ᴴ * K i = 1) :
    relabel e (SubInstrument.ofKraus K hK) =
      SubInstrument.ofKraus (fun i => (K i).submatrix e.symm e.symm)
        (submatrix_complete e K hK) := by
  refine DSubInstrument.ext <| funext fun i => LinearMap.ext fun ρ => ?_
  rw [relabel_branch, reindexMap_apply]
  simp only [DSubInstrument.branch_ofKraus_apply, MatrixMap.conj_apply]
  rw [← Matrix.submatrix_mul_equiv _ _ _ e.symm, ← Matrix.submatrix_mul_equiv _ _ _ e.symm,
    conjTranspose_submatrix]
  simp

end Relabel

/-! ## The challengers -/

section Sys

variable {m n w c a : ℕ} [NeZero n] {σ : Type}

/-- The step of a challenger whose private register holds a database: a query applies `Q`; a
round with message `y` runs the signer program `sig s y` with the operations `rd` and `wr` on
the database register. -/
def rwStep (Q : SubInstrument (Fin (m * n * w) × Fin ((n + 1) ^ m))
      (Fin (m * n * w) × Fin ((n + 1) ^ m)) Unit)
    (rd : Fin m → SubInstrument (Fin ((n + 1) ^ m)) (Fin ((n + 1) ^ m)) (Fin (n + 1)))
    (wr : Fin m → Fin n → SubInstrument (Fin ((n + 1) ^ m)) (Fin ((n + 1) ^ m)) Unit)
    (sig : σ → Fin c → RWProg m n (σ × Fin a)) (s : σ) :
    QROMEvent c → SubInstrument (Fin (m * n * w) × Fin ((n + 1) ^ m))
      (Fin (m * n * w) × Fin ((n + 1) ^ m)) (σ × QROMOut a)
  | .query => Q.bind fun _ => SubInstrument.pure (s, .done)
  | .round y => ((sig s y).exec (fun x => frameLeft (rd x) (Fin (m * n * w)))
      (fun x v => frameLeft (wr x v) (Fin (m * n * w)))).bind fun r =>
        SubInstrument.pure (r.1, .answer r.2)

variable (m n w) in
/-- The per-query compressed oracle `cmpLocalU` on the product register. -/
def cmpQuery : SubInstrument (Fin (m * n * w) × Fin ((n + 1) ^ m))
    (Fin (m * n * w) × Fin ((n + 1) ^ m)) Unit :=
  relabel (TensorProduct.finProdEquiv (m * n * w) ((n + 1) ^ m)).symm
    (CPComp.unitary (cmpLocalU m n w))

variable (m n w) in
/-- The standard oracle `stdDbU` on the database register, on the product register. -/
def stdQuery : SubInstrument (Fin (m * n * w) × Fin ((n + 1) ^ m))
    (Fin (m * n * w) × Fin ((n + 1) ^ m)) Unit :=
  relabel (TensorProduct.finProdEquiv (m * n * w) ((n + 1) ^ m)).symm
    (CPComp.unitary (stdDbU m n w))

/-- **The compressed challenger.** The private register holds the database of the compressed
oracle, started at the empty database; a query applies `cmpLocalU`; a round runs the signer
program with `readOp` and `writeOp`. -/
def cmpSys (s₀ : σ) (sig : σ → Fin c → RWProg m n (σ × Fin a)) :
    QSys (Fin ((n + 1) ^ m)) σ (QROMEvent c) (QROMOut a) (m * n * w) where
  init := s₀
  initReg := dbEmptyIdx m n
  step := rwStep (cmpQuery m n w) readOp writeOp sig

/-- The challenger on the decompressed database: a query applies `stdDbU`; a round runs the
signer program with the measurement and the setting of an entry. -/
def purSys (s₀ : σ) (sig : σ → Fin c → RWProg m n (σ × Fin a)) :
    QSys (Fin ((n + 1) ^ m)) σ (QROMEvent c) (QROMOut a) (m * n * w) where
  init := s₀
  initReg := dbEmptyIdx m n
  step := rwStep (stdQuery m n w) readOpP writeOpP sig

/-- **The classical challenger** of the signer `sig` and the function `H`: its state holds the
signer state and the function; a query applies the standard oracle of the function, and a
round runs the signer program against the function and keeps the reprogrammed function. -/
def chalRW (s₀ : σ) (sig : σ → Fin c → RWProg m n (σ × Fin a)) (H : Fin m → Fin n) :
    QSys Unit (σ × (Fin m → Fin n)) (QROMEvent c) (QROMOut a) (m * n * w) :=
  chal (s₀, H) (fun t => t.2) (fun t y => ((sig t.1 y).run t.2).1.2)
    (fun t y => (((sig t.1 y).run t.2).1.1, ((sig t.1 y).run t.2).2))

end Sys

/-! ## The weight of the database -/

section Weight

variable {m n w c a : ℕ} [NeZero n] {σ ζ : Type}

variable (m n) in
/-- The databases with at most `N` non-`⊥` entries. -/
def dbLe (N : ℕ) : Set (Fin ((n + 1) ^ m)) := {k | dbWeight (m := m) (n := n) k ≤ N}

omit [NeZero n] in
theorem dbLe_mono {N N' : ℕ} (h : N ≤ N') : dbLe m n N ⊆ dbLe m n N' :=
  fun _ hk => le_trans hk h

theorem MapsSupp.mono_right {A B α : Type} [Fintype A] [Fintype B] {s : SubInstrument A B α}
    {S : Set A} {S' T : α → Set B} (h : MapsSupp s S S') (hT : ∀ b, S' b ⊆ T b) :
    MapsSupp s S T :=
  fun b M hM => (h b M hM).mono (hT b)

omit [NeZero n] in
/-- A Kraus measurement on the database register whose operators add at most `s` non-`⊥`
entries maps the databases with at most `N` such entries to those with at most `N + s`. -/
theorem mapsSupp_frameLeft_ofKraus {d : ℕ} {ι : Type} [Fintype ι]
    (K : ι → Matrix (Fin ((n + 1) ^ m)) (Fin ((n + 1) ^ m)) ℂ) (hK : ∑ i, (K i)ᴴ * K i = 1)
    (s : ℕ) (hw : ∀ i x u, K i x u ≠ 0 →
      dbWeight (m := m) (n := n) x ≤ dbWeight (m := m) (n := n) u + s) (N : ℕ) :
    MapsSupp (frameLeft (SubInstrument.ofKraus K hK) (Fin d)) (Prod.snd ⁻¹' dbLe m n N)
      (fun _ => Prod.snd ⁻¹' dbLe m n (N + s)) := by
  rw [frameLeft_ofKraus]
  refine mapsSupp_ofKraus _ _ _ _ fun i x u hxu hu => ?_
  rw [liftL_apply] at hxu
  split_ifs at hxu
  · have h1 := hw i _ _ hxu
    have h2 : dbWeight (m := m) (n := n) u.2 ≤ N := hu
    change dbWeight (m := m) (n := n) x.2 ≤ N + s
    omega
  · exact absurd rfl hxu

theorem readK_weight (x : Fin m) (c : Fin (n + 1)) (i j : Fin ((n + 1) ^ m))
    (h : readK x c i j ≠ 0) :
    dbWeight (m := m) (n := n) i ≤ dbWeight (m := m) (n := n) j + 1 :=
  dbWeight_le_of_dbOp_update x _ i j (by rwa [readK, readP, decompDB_mul_dbOp_update_mul] at h)

theorem writeK_weight (x : Fin m) (v : Fin n) (u : Fin (n + 1)) (i j : Fin ((n + 1) ^ m))
    (h : writeK x v u i j ≠ 0) :
    dbWeight (m := m) (n := n) i ≤ dbWeight (m := m) (n := n) j + 1 :=
  dbWeight_le_of_dbOp_update x _ i j (by rwa [writeK, writeP, decompDB_mul_dbOp_update_mul] at h)

theorem readOp_mapsSupp {d : ℕ} (x : Fin m) (N : ℕ) :
    MapsSupp (frameLeft (readOp (n := n) x) (Fin d)) (Prod.snd ⁻¹' dbLe m n N)
      (fun _ => Prod.snd ⁻¹' dbLe m n (N + 1)) :=
  mapsSupp_frameLeft_ofKraus _ (readK_complete x) 1 (readK_weight x) N

theorem writeOp_mapsSupp {d : ℕ} (x : Fin m) (v : Fin n) (N : ℕ) :
    MapsSupp (frameLeft (writeOp x v) (Fin d)) (Prod.snd ⁻¹' dbLe m n N)
      (fun _ => Prod.snd ⁻¹' dbLe m n (N + 1)) := by
  rw [writeOp, frameLeft_bind]
  simp only [frameLeft_pure]
  exact MapsSupp.bind' (mapsSupp_frameLeft_ofKraus _ (writeK_complete x v) 1
    (writeK_weight x v) N) fun _ => mapsSupp_pure _ _

theorem cmpQuery_mapsSupp (N : ℕ) :
    MapsSupp (cmpQuery m n w) (Prod.snd ⁻¹' dbLe m n N)
      (fun _ => Prod.snd ⁻¹' dbLe m n (N + 1)) := by
  rw [cmpQuery, unitary_eq_ofKraus, relabel_ofKraus]
  refine mapsSupp_ofKraus _ _ _ _ fun _ x u hxu hu => ?_
  rw [submatrix_apply, Equiv.symm_symm] at hxu
  have h := cmpLocal_weightBound (m := m) (n := n) (w := w) _ _ hxu
  simp only [totWeight, Equiv.symm_apply_apply] at h
  have h2 : dbWeight (m := m) (n := n) u.2 ≤ N := hu
  change dbWeight (m := m) (n := n) x.2 ≤ N + 1
  omega

theorem exec_mapsSupp {α : Type} (p : RWProg m n α) (N : ℕ) :
    MapsSupp (p.exec (fun x => frameLeft (readOp x) (Fin (m * n * w)))
        (fun x v => frameLeft (writeOp x v) (Fin (m * n * w))))
      (Prod.snd ⁻¹' dbLe m n N) (fun _ => Prod.snd ⁻¹' dbLe m n (N + p.ops)) := by
  induction p generalizing N with
  | ret a => exact mapsSupp_pure a _
  | read x k ih =>
    rw [RWProg.exec]
    refine MapsSupp.bind' (readOp_mapsSupp x N) fun c =>
      MapsSupp.mono_right (ih (truncEntry n c) (N + 1)) fun _ =>
        Set.preimage_mono (dbLe_mono ?_)
    have := Finset.le_sup (f := fun v => (k v).ops) (Finset.mem_univ (truncEntry n c))
    simp only [RWProg.ops]
    omega
  | write x v k ih =>
    rw [RWProg.exec]
    refine MapsSupp.bind' (writeOp_mapsSupp x v N) fun _ =>
      MapsSupp.mono_right (ih (N + 1)) fun _ => Set.preimage_mono (dbLe_mono ?_)
    simp only [RWProg.ops]
    omega

theorem cmpSys_step_mapsSupp (s₀ : σ) (sig : σ → Fin c → RWProg m n (σ × Fin a)) (b : ℕ)
    (hb : ∀ s y, (sig s y).ops ≤ b) (s : σ) (e : QROMEvent c) (N : ℕ) :
    MapsSupp ((cmpSys (w := w) s₀ sig).step s e) (Prod.snd ⁻¹' dbLe m n N)
      (fun _ => Prod.snd ⁻¹' dbLe m n (N + max 1 b)) := by
  cases e with
  | query =>
    exact MapsSupp.mono_right (MapsSupp.bind' (cmpQuery_mapsSupp N) fun _ => mapsSupp_pure _ _)
      fun _ => Set.preimage_mono (dbLe_mono (by omega))
  | round y =>
    have := hb s y
    exact MapsSupp.mono_right
      (MapsSupp.bind' (exec_mapsSupp (sig s y) N) fun _ => mapsSupp_pure _ _)
      fun _ => Set.preimage_mono (dbLe_mono (by omega))

/-- **Weight bound of the compressed challenger.** After `k` activations, each a query or a
round whose signer program has at most `b` operations, a state supported on the databases with
at most `N` non-`⊥` entries is supported on the databases with at most `N + k * max 1 b`. -/
theorem cmpSys_weight_le (s₀ : σ) (sig : σ → Fin c → RWProg m n (σ × Fin a)) (b : ℕ)
    (hb : ∀ s y, (sig s y).ops ≤ b) (Z : QStrat ζ (QROMEvent c) (QROMOut a) (m * n * w)) :
    ∀ (k N : ℕ) (q : ζ × σ), MapsSupp (qloop (cmpSys (w := w) s₀ sig) Z k q)
      (Prod.snd ⁻¹' dbLe m n N) (fun _ => Prod.snd ⁻¹' dbLe m n (N + k * max 1 b)) := by
  intro k
  induction k with
  | zero =>
    intro N q
    rw [qloop]
    exact MapsSupp.mono_right (mapsSupp_pure q _) fun _ => by simp
  | succ k ih =>
    intro N q
    rw [qloop]
    refine MapsSupp.mono_right (MapsSupp.bind' (mapsSupp_frame_snd _ _) fun e =>
      MapsSupp.bind' (cmpSys_step_mapsSupp s₀ sig b hb q.2 e.2 N) fun p =>
        MapsSupp.bind' (mapsSupp_frame_snd _ _) fun z => ih (N + max 1 b) (z, p.1))
      fun _ => Set.preimage_mono (dbLe_mono ?_)
    exact le_of_eq (by ring)

/-- From the empty database, after `k` activations as in `cmpSys_weight_le`, the state is
supported on the databases with at most `k * max 1 b` non-`⊥` entries. -/
theorem cmpSys_run_weight_le (s₀ : σ) (sig : σ → Fin c → RWProg m n (σ × Fin a)) (b : ℕ)
    (hb : ∀ s y, (sig s y).ops ≤ b) (Z : QStrat ζ (QROMEvent c) (QROMOut a) (m * n * w))
    (k : ℕ) (q : ζ × σ) :
    MapsSupp ((appendBasis (dbEmptyIdx m n)).bind fun _ =>
        qloop (cmpSys (w := w) s₀ sig) Z k q) Set.univ
      (fun _ => Prod.snd ⁻¹' dbLe m n (k * max 1 b)) := by
  refine MapsSupp.bind' (MapsSupp.mono_right (mapsSupp_appendBasis _ _) fun _ => ?_) fun _ =>
    MapsSupp.mono_right (cmpSys_weight_le s₀ sig b hb Z k 0 q) fun _ => by simp
  intro x hx
  change dbWeight (m := m) (n := n) x.2 ≤ 0
  rw [hx.2, dbWeight_dbEmptyIdx]

end Weight

/-! ## Decompression of the database register -/

section Conj

variable {m n w c a : ℕ} [NeZero n] {σ ζ : Type}

theorem unitaryOp_bind_self {X : Type} [Fintype X] [DecidableEq X] (U : Matrix X X ℂ)
    (hU : Uᴴ * U = 1) (hh : Uᴴ = U) :
    (unitaryOp U hU).bind (fun _ => unitaryOp U hU) = SubInstrument.pure () := by
  refine DSubInstrument.ext <| funext fun u => LinearMap.ext fun ρ => ?_
  rw [bind_unit_branch_apply]
  cases u
  have h2 : U * U = 1 := by rw [hh] at hU; exact hU
  simp only [unitaryOp, DSubInstrument.branch_ofKraus_apply, MatrixMap.conj_apply,
    SubInstrument.branch_pure_self, LinearMap.id_apply, hh]
  simp only [← Matrix.mul_assoc, h2, Matrix.one_mul]
  simp only [Matrix.mul_assoc, h2, Matrix.mul_one]

variable (m n w) in
/-- Decompression of the database register, on the product register. -/
abbrev decompL : SubInstrument (Fin (m * n * w) × Fin ((n + 1) ^ m))
    (Fin (m * n * w) × Fin ((n + 1) ^ m)) Unit :=
  frameLeft (unitaryOp (decompDB m n) decompDB_conjTranspose_mul_self) (Fin (m * n * w))

theorem decompL_bind_decompL {C β : Type} [Fintype C]
    (f : Unit → SubInstrument (Fin (m * n * w) × Fin ((n + 1) ^ m)) C β) :
    (decompL m n w).bind (fun _ => (decompL m n w).bind f) = f () := by
  rw [← SubInstrument.bind_assoc, decompL, ← frameLeft_bind,
    unitaryOp_bind_self _ _ decompDB_conjTranspose, frameLeft_pure, SubInstrument.pure_bind]

/-- The subinstrument `Y'` is `Y` conjugated by the decompression of the database. -/
def DecConj {α : Type} (Y Y' : SubInstrument (Fin (m * n * w) × Fin ((n + 1) ^ m))
    (Fin (m * n * w) × Fin ((n + 1) ^ m)) α) : Prop :=
  Y' = (decompL m n w).bind fun _ => Y.bind fun r => (decompL m n w).bind fun _ =>
    SubInstrument.pure r

theorem decConj_pure {α : Type} (r : α) :
    DecConj (m := m) (n := n) (w := w) (SubInstrument.pure r) (SubInstrument.pure r) := by
  simp only [DecConj, SubInstrument.pure_bind, decompL_bind_decompL]

theorem DecConj.bind {α β : Type}
    {Y Y' : SubInstrument (Fin (m * n * w) × Fin ((n + 1) ^ m))
      (Fin (m * n * w) × Fin ((n + 1) ^ m)) α}
    {f f' : α → SubInstrument (Fin (m * n * w) × Fin ((n + 1) ^ m))
      (Fin (m * n * w) × Fin ((n + 1) ^ m)) β}
    (hY : DecConj Y Y') (hf : ∀ r, DecConj (f r) (f' r)) :
    DecConj (Y.bind f) (Y'.bind f') := by
  unfold DecConj at *
  simp only [hY, hf, SubInstrument.bind_assoc, SubInstrument.pure_bind, decompL_bind_decompL]

theorem readOp_decConj (x : Fin m) :
    DecConj (m := m) (n := n) (w := w) (frameLeft (readOpP x) _) (frameLeft (readOp x) _) := by
  have h : readOp (n := n) x = (unitaryOp (decompDB m n) decompDB_conjTranspose_mul_self).bind
      fun _ => (readOpP x).bind fun c =>
        (unitaryOp (decompDB m n) decompDB_conjTranspose_mul_self).bind fun _ =>
          SubInstrument.pure c :=
    (unitaryOp_bind_ofKraus_bind _ _ _ (readP_complete x) _ _ (readK_complete x)).symm
  rw [DecConj, h]
  simp only [frameLeft_bind, frameLeft_pure]

theorem writeOp_decConj (x : Fin m) (v : Fin n) :
    DecConj (m := m) (n := n) (w := w) (frameLeft (writeOpP x v) _)
      (frameLeft (writeOp x v) _) := by
  have h : SubInstrument.ofKraus (writeK x v) (writeK_complete x v) =
      (unitaryOp (decompDB m n) decompDB_conjTranspose_mul_self).bind
        fun _ => (SubInstrument.ofKraus (writeP x v) (writeP_complete x v)).bind fun c =>
          (unitaryOp (decompDB m n) decompDB_conjTranspose_mul_self).bind fun _ =>
            SubInstrument.pure c :=
    (unitaryOp_bind_ofKraus_bind _ _ _ (writeP_complete x v) _ _ (writeK_complete x v)).symm
  rw [DecConj, writeOp, writeOpP, h]
  simp only [frameLeft_bind, frameLeft_pure, SubInstrument.bind_assoc, SubInstrument.pure_bind]

theorem exec_decConj {α : Type} (p : RWProg m n α) :
    DecConj (m := m) (n := n) (w := w)
      (p.exec (fun x => frameLeft (readOpP x) _) (fun x v => frameLeft (writeOpP x v) _))
      (p.exec (fun x => frameLeft (readOp x) _) (fun x v => frameLeft (writeOp x v) _)) := by
  induction p with
  | ret r => exact decConj_pure r
  | read x k ih => exact DecConj.bind (readOp_decConj x) fun c => ih (truncEntry n c)
  | write x v k ih => exact DecConj.bind (writeOp_decConj x v) fun _ => ih

variable (m n w) in
/-- The standard oracle on the decompressed database as an operator on the product
register. -/
def stdMat : Matrix (Fin (m * n * w) × Fin ((n + 1) ^ m))
    (Fin (m * n * w) × Fin ((n + 1) ^ m)) ℂ :=
  (stdDbU m n w : Matrix _ _ ℂ).submatrix (TensorProduct.finProdEquiv _ _)
    (TensorProduct.finProdEquiv _ _)

theorem stdMat_apply (x y : Fin (m * n * w) × Fin ((n + 1) ^ m)) :
    stdMat m n w x y =
      if x.2 = y.2 then (oracleU m n w (dbFun m n x.2) : Matrix _ _ ℂ) x.1 y.1 else 0 := by
  simp only [stdMat, submatrix_apply, stdDbU, tableOracleU, blockU_val, Matrix.sum_apply,
    TensorProduct.kronecker_apply, Equiv.symm_apply_apply, single_apply]
  rw [Finset.sum_eq_single x.2 (fun k _ hk => by simp [hk]) (by simp)]
  by_cases h : x.2 = y.2 <;> simp [h]

theorem ofKraus_congr {X ι : Type} [Fintype X] [DecidableEq X] [Fintype ι]
    {K K' : ι → Matrix X X ℂ} (h : K = K') (hK : ∑ i, (K i)ᴴ * K i = 1)
    (hK' : ∑ i, (K' i)ᴴ * K' i = 1) :
    SubInstrument.ofKraus K hK = SubInstrument.ofKraus K' hK' := by
  subst h; rfl

theorem stdMat_complete : ∑ _ : Unit, (stdMat m n w)ᴴ * stdMat m n w = 1 := by
  have hU := Matrix.mem_unitaryGroup_iff'.mp (stdDbU m n w).prop
  rw [star_eq_conjTranspose] at hU
  rw [Fintype.sum_unique, stdMat, conjTranspose_submatrix, Matrix.submatrix_mul_equiv, hU,
    submatrix_one_equiv]

theorem stdQuery_eq :
    stdQuery m n w = SubInstrument.ofKraus (fun _ : Unit => stdMat m n w) stdMat_complete := by
  rw [stdQuery, unitary_eq_ofKraus, relabel_ofKraus]
  exact ofKraus_congr (funext fun _ => by rw [Equiv.symm_symm]; rfl) _ _

theorem frameLeft_unitaryOp {L X : Type} [Fintype L] [DecidableEq L] [Fintype X]
    [DecidableEq X] (U : Matrix X X ℂ) (hU : Uᴴ * U = 1) :
    frameLeft (unitaryOp U hU) L =
      unitaryOp (liftL L U) (by rw [liftL_conjTranspose_mul, hU, liftL_one]) :=
  frameLeft_ofKraus _ (by simpa using hU)

theorem liftL_decompDB_unitary :
    (liftL (Fin (m * n * w)) (decompDB m n))ᴴ * liftL (Fin (m * n * w)) (decompDB m n) = 1 := by
  rw [liftL_conjTranspose_mul, decompDB_conjTranspose_mul_self, liftL_one]

theorem liftL_decompDB_eq :
    liftL (Fin (m * n * w)) (decompDB m n) =
      (decompU m n w : Matrix _ _ ℂ).submatrix (TensorProduct.finProdEquiv _ _)
        (TensorProduct.finProdEquiv _ _) := by
  ext x y
  simp only [liftL_apply, decompU, oneKronU_val, submatrix_apply, TensorProduct.kronecker_apply,
    Equiv.symm_apply_apply, Matrix.one_apply]
  split_ifs <;> simp [decompDBU]

theorem cmpMat_eq :
    (cmpLocalU m n w : Matrix _ _ ℂ).submatrix (TensorProduct.finProdEquiv _ _)
        (TensorProduct.finProdEquiv _ _) =
      liftL (Fin (m * n * w)) (decompDB m n) * stdMat m n w *
        liftL (Fin (m * n * w)) (decompDB m n) := by
  rw [cmpLocalU_eq_cmpOracleU, cmpOracleU, Submonoid.coe_mul, Submonoid.coe_mul,
    Unitary.coe_star, star_eq_conjTranspose,
    ← Matrix.submatrix_mul_equiv _ _ _ (TensorProduct.finProdEquiv _ _),
    ← Matrix.submatrix_mul_equiv _ _ _ (TensorProduct.finProdEquiv _ _),
    ← conjTranspose_submatrix, ← liftL_decompDB_eq, liftL_conjTranspose, decompDB_conjTranspose]
  rfl

theorem query_decConj :
    DecConj (m := m) (n := n) (w := w) (stdQuery m n w) (cmpQuery m n w) := by
  rw [DecConj, stdQuery_eq, decompL, frameLeft_unitaryOp,
    unitaryOp_bind_ofKraus_bind _ liftL_decompDB_unitary _ _ _ liftL_decompDB_unitary
      (conj_complete _ liftL_decompDB_unitary _ stdMat_complete _ liftL_decompDB_unitary),
    cmpQuery, unitary_eq_ofKraus, relabel_ofKraus]
  exact ofKraus_congr (funext fun _ => cmpMat_eq) _ _

theorem decConj_frame {α : Type} (W : SubInstrument (Fin (m * n * w)) (Fin (m * n * w)) α) :
    DecConj (m := m) (n := n) (w := w) (W.frame _) (W.frame _) := by
  simp only [DecConj, frame_frameLeft_bind_comm, decompL_bind_decompL, SubInstrument.bind_pure]

theorem step_decConj (s₀ : σ) (sig : σ → Fin c → RWProg m n (σ × Fin a)) (s : σ)
    (e : QROMEvent c) :
    DecConj ((purSys (w := w) s₀ sig).step s e) ((cmpSys (w := w) s₀ sig).step s e) := by
  cases e with
  | query => exact DecConj.bind query_decConj fun _ => decConj_pure _
  | round y => exact DecConj.bind (exec_decConj (sig s y)) fun _ => decConj_pure _

theorem qloop_decConj (s₀ : σ) (sig : σ → Fin c → RWProg m n (σ × Fin a))
    (Z : QStrat ζ (QROMEvent c) (QROMOut a) (m * n * w)) :
    ∀ (k : ℕ) (q : ζ × σ),
      DecConj (qloop (purSys (w := w) s₀ sig) Z k q) (qloop (cmpSys (w := w) s₀ sig) Z k q) := by
  intro k
  induction k with
  | zero => intro q; exact decConj_pure q
  | succ k ih =>
    intro q
    rw [qloop, qloop]
    exact DecConj.bind (decConj_frame _) fun e => DecConj.bind (step_decConj s₀ sig q.2 e.2)
      fun p => DecConj.bind (decConj_frame _) fun z => ih (z, p.1)

end Conj

/-! ## The decompressed challenger commutes with dephasing -/

section Deph

variable {m n w c a : ℕ} [NeZero n] {σ ζ : Type}

omit [NeZero n] in
theorem readP_ne_zero (x : Fin m) (c : Fin (n + 1)) (i j : Fin ((n + 1) ^ m))
    (h : readP x c i j ≠ 0) : i = j := by
  rw [readP, dbOp_update_single_apply] at h
  split_ifs at h with h'
  · rw [h'.2, dbSet, ← h'.1, Function.update_eq_self, Equiv.apply_symm_apply]
  · exact absurd rfl h

omit [NeZero n] in
theorem writeP_ne_zero (x : Fin m) (v : Fin n) (u : Fin (n + 1)) (i j : Fin ((n + 1) ^ m))
    (h : writeP x v u i j ≠ 0) : (dbIndex m n).symm j x = u ∧ i = dbSet j x v.castSucc := by
  rw [writeP, dbOp_update_single_apply] at h
  split_ifs at h with h'
  · exact h'
  · exact absurd rfl h

omit [NeZero n] in
theorem dbSet_inj {j j' : Fin ((n + 1) ^ m)} {x : Fin m} {b : Fin (n + 1)}
    (hj : (dbIndex m n).symm j x = (dbIndex m n).symm j' x)
    (h : dbSet j x b = dbSet j' x b) : j = j' := by
  have h2 := congrArg (dbIndex m n).symm h
  simp only [dbSet, Equiv.symm_apply_apply] at h2
  refine (dbIndex m n).symm.injective (funext fun x' => ?_)
  by_cases hx : x' = x
  · subst hx; exact hj
  · simpa [Function.update_of_ne hx] using congrFun h2 x'

omit [NeZero n] in
theorem dephComm_liftL {ι : Type} [Fintype ι]
    (K : ι → Matrix (Fin ((n + 1) ^ m)) (Fin ((n + 1) ^ m)) ℂ) (hK : ∑ i, (K i)ᴴ * K i = 1)
    (hb : ∀ i p q u v, K i p u ≠ 0 → K i q v ≠ 0 → (p = q ↔ u = v)) :
    DephComm (Fin (m * n * w)) _ (frameLeft (SubInstrument.ofKraus K hK) (Fin (m * n * w))) := by
  rw [frameLeft_ofKraus]
  refine dephComm_ofKraus _ _ fun i x y u v hxu hyv => ?_
  rw [liftL_apply] at hxu hyv
  split_ifs at hxu hyv
  · exact hb i _ _ _ _ hxu hyv
  all_goals simp_all

omit [NeZero n] in
theorem readOpP_dephComm (x : Fin m) :
    DephComm (Fin (m * n * w)) _ (frameLeft (readOpP (n := n) x) (Fin (m * n * w))) :=
  dephComm_liftL _ (readP_complete x) fun i p q u v h1 h2 => by
    rw [readP_ne_zero x i p u h1, readP_ne_zero x i q v h2]

omit [NeZero n] in
theorem writeOpP_dephComm (x : Fin m) (v : Fin n) :
    DephComm (Fin (m * n * w)) _ (frameLeft (writeOpP x v) (Fin (m * n * w))) := by
  rw [writeOpP, frameLeft_bind]
  simp only [frameLeft_pure]
  refine DephComm.bind (dephComm_liftL _ _ fun i p q j j' h1 h2 => ?_) fun _ => DephComm.pure _
  obtain ⟨h1a, rfl⟩ := writeP_ne_zero x v i p j h1
  obtain ⟨h2a, rfl⟩ := writeP_ne_zero x v i q j' h2
  exact ⟨dbSet_inj (h1a.trans h2a.symm), fun h => h ▸ rfl⟩

theorem stdQuery_dephComm : DephComm (Fin (m * n * w)) _ (stdQuery m n w) := by
  rw [stdQuery_eq]
  refine dephComm_ofKraus _ _ fun _ x y u v hxu hyv => ?_
  rw [stdMat_apply] at hxu hyv
  split_ifs at hxu hyv with h1 h2
  · rw [h1, h2]
  all_goals simp_all

theorem exec_dephComm {α : Type} (p : RWProg m n α) :
    DephComm (Fin (m * n * w)) _
      (p.exec (fun x => frameLeft (readOpP x) _) (fun x v => frameLeft (writeOpP x v) _)) := by
  induction p with
  | ret r => exact DephComm.pure r
  | read x k ih => exact DephComm.bind (readOpP_dephComm x) fun c => ih (truncEntry n c)
  | write x v k ih => exact DephComm.bind (writeOpP_dephComm x v) fun _ => ih

theorem qloop_purSys_dephComm (s₀ : σ) (sig : σ → Fin c → RWProg m n (σ × Fin a))
    (Z : QStrat ζ (QROMEvent c) (QROMOut a) (m * n * w)) :
    ∀ (k : ℕ) (q : ζ × σ),
      DephComm (Fin (m * n * w)) _ (qloop (purSys (w := w) s₀ sig) Z k q) := by
  intro k
  induction k with
  | zero => intro q; exact DephComm.pure q
  | succ k ih =>
    intro q
    rw [qloop]
    refine DephComm.bind (dephComm_frame _) fun e => ?_
    refine DephComm.bind ?_ fun p => DephComm.bind (dephComm_frame _) fun z => ih (z, p.1)
    rcases e with ⟨z', _ | y⟩
    · exact DephComm.bind stdQuery_dephComm fun _ => DephComm.pure _
    · exact DephComm.bind (exec_dephComm _) fun _ => DephComm.pure _

end Deph

/-! ## The decompressed challenger from a basis state is the classical challenger -/

section Sim

variable {m n w c a : ℕ} [NeZero n] {σ ζ : Type}

/-- An appended basis state of `R` is kept by an operation on the other factor. -/
theorem appendBasis_bind_frame {A R C α β : Type} [Fintype A] [DecidableEq A] [Fintype R]
    [DecidableEq R] [Fintype C] (r : R) (W : SubInstrument A A α)
    (f : α → SubInstrument (A × R) C β) :
    (appendBasis r).bind (fun _ => (W.frame R).bind f) =
      W.bind fun x => (appendBasis r).bind fun _ => f x := by
  have key : ∀ x (ρ : Matrix A A ℂ), (W.frame R).branch x ((appendBasis r).branch () ρ) =
      (appendBasis r).branch () (W.branch x ρ) := by
    intro x ρ
    ext p q
    rw [DSubInstrument.branch_frame_apply, MatrixMap.amplify_apply, appendBasis_branch_apply]
    by_cases h : p.2 = r ∧ q.2 = r
    · rw [ite_eq_left h]
      have h1 : ((appendBasis r).branch () ρ).submatrix (·, p.2) (·, q.2) = ρ := by
        ext u v; simp [appendBasis_branch_apply, h]
      rw [h1]
    · rw [ite_eq_right h]
      have h0 : ((appendBasis r).branch () ρ).submatrix (·, p.2) (·, q.2) = 0 := by
        ext u v; simp [appendBasis_branch_apply, h]
      rw [h0, map_zero]
      rfl
  refine DSubInstrument.ext <| funext fun b => LinearMap.ext fun ρ => ?_
  rw [bind_unit_branch_apply, SubInstrument.bind, DSubInstrument.branch_bind_apply,
    SubInstrument.bind, DSubInstrument.branch_bind_apply]
  refine tsum_congr fun x => ?_
  rw [key, bind_unit_branch_apply]

/-- Preparing a basis state and discarding it. -/
theorem appendBasis_bind_discardRight {A R C β : Type} [Fintype A] [DecidableEq A]
    [Fintype R] [DecidableEq R] [Fintype C] (r : R) (f : R → SubInstrument A C β) :
    (appendBasis r).bind (fun _ => discardRight.bind f) = f r := by
  refine DSubInstrument.ext <| funext fun b => LinearMap.ext fun ρ => ?_
  rw [bind_unit_branch_apply, SubInstrument.bind, DSubInstrument.branch_bind_apply,
    tsum_eq_single r]
  · congr 1
    ext u v
    rw [discardRight_branch_apply, submatrix_apply, appendBasis_branch_apply]
    simp
  · intro k hk
    have h0 : (discardRight (A := A)).branch k ((appendBasis r).branch () ρ) = 0 := by
      ext u v
      rw [discardRight_branch_apply, submatrix_apply, appendBasis_branch_apply]
      simp [hk]
    rw [h0, map_zero]

theorem relabel_prodPUnit_frame {L α : Type} [Fintype L] (W : SubInstrument L L α) :
    relabel (Equiv.prodPUnit L) (W.frame Unit) = W := by
  rw [frame_unit, relabel_relabel, Equiv.symm_trans_self, relabel_refl]

/-- **Simulation of a system by a classical system.** If from the basis state `enc u` each
step of `S` at `π u` is the step of the classical system `C` at `u` followed by the basis
state `enc` of the new state, then so is the joint run with every environment. -/
theorem qloop_sim {R υ τ E O : Type} [Fintype R] [DecidableEq R] {d : ℕ}
    (S : QSys R τ E O d) (C : QSys Unit υ E O d) (Z : QStrat ζ E O d) (enc : υ → R)
    (π : υ → τ)
    (hstep : ∀ u e, (appendBasis (enc u)).bind (fun _ => S.step (π u) e) =
      (relabel (Equiv.prodPUnit (Fin d)) (C.step u e)).bind fun p =>
        (appendBasis (enc p.1)).bind fun _ => SubInstrument.pure (π p.1, p.2)) :
    ∀ (k : ℕ) (z : ζ) (u : υ), (appendBasis (enc u)).bind (fun _ => qloop S Z k (z, π u)) =
      (relabel (Equiv.prodPUnit (Fin d)) (qloop C Z k (z, u))).bind fun q =>
        (appendBasis (enc q.2)).bind fun _ => SubInstrument.pure (q.1, π q.2) := by
  intro k
  induction k with
  | zero =>
    intro z u
    simp only [qloop, relabel_pure, SubInstrument.pure_bind]
  | succ k ih =>
    intro z u
    rw [qloop, qloop]
    simp only [relabel_bind, relabel_prodPUnit_frame, SubInstrument.bind_assoc]
    rw [appendBasis_bind_frame]
    refine congrArg (SubInstrument.bind _) (funext fun e => ?_)
    rw [← SubInstrument.bind_assoc, hstep, SubInstrument.bind_assoc]
    refine congrArg (SubInstrument.bind _) (funext fun p => ?_)
    rw [SubInstrument.bind_assoc, SubInstrument.pure_bind, appendBasis_bind_frame]
    refine congrArg (SubInstrument.bind _) (funext fun z' => ?_)
    exact ih z' p.1

variable (m n) in
/-- The database of the function `H`: every entry holds a value. -/
def dbOf (H : Fin m → Fin n) : Fin ((n + 1) ^ m) := dbIndex m n fun x => (H x).castSucc

omit [NeZero n] in
theorem dbOp_single_mul_single (x : Fin m) (a b : Fin (n + 1)) (D : Fin ((n + 1) ^ m)) :
    dbOp m n (Function.update 1 x (Matrix.single a b 1)) * Matrix.single D D 1 =
      if (dbIndex m n).symm D x = b then Matrix.single (dbSet D x a) D 1 else 0 := by
  ext i j
  rw [Matrix.mul_apply, Finset.sum_eq_single D (fun k _ hk => by simp [Ne.symm hk])
    (by simp), dbOp_update_single_apply]
  by_cases h : (dbIndex m n).symm D x = b <;> by_cases hi : i = dbSet D x a <;>
    simp [h, hi, single_apply, eq_comm]

theorem mul_single_mul_conjTranspose {X : Type} [Fintype X] [DecidableEq X]
    (K : Matrix X X ℂ) (D : X) :
    K * Matrix.single D D 1 * Kᴴ = (K * Matrix.single D D 1) * (K * Matrix.single D D 1)ᴴ := by
  rw [conjTranspose_mul, conjTranspose_single, star_one, Matrix.mul_assoc, Matrix.mul_assoc K,
    ← Matrix.mul_assoc (Matrix.single D D 1) (Matrix.single D D 1), single_mul_single_same,
    mul_one]

omit [NeZero n] in
theorem single_mul_conjTranspose_single {i j : Fin ((n + 1) ^ m)} :
    Matrix.single i j (1 : ℂ) * (Matrix.single i j 1)ᴴ = Matrix.single i i 1 := by
  rw [conjTranspose_single, star_one, single_mul_single_same, mul_one]

omit [NeZero n] in
theorem readP_conj_dbOf (H : Fin m → Fin n) (x : Fin m) (i : Fin (n + 1)) :
    readP x i * Matrix.single (dbOf m n H) (dbOf m n H) 1 * (readP x i)ᴴ =
      if i = (H x).castSucc then Matrix.single (dbOf m n H) (dbOf m n H) 1 else 0 := by
  rw [mul_single_mul_conjTranspose, readP, dbOp_single_mul_single]
  have hD : (dbIndex m n).symm (dbOf m n H) x = (H x).castSucc := by simp [dbOf]
  have hS : dbSet (dbOf m n H) x (H x).castSucc = dbOf m n H := by
    rw [dbSet, ← hD, Function.update_eq_self, Equiv.apply_symm_apply]
  by_cases h : i = (H x).castSucc
  · subst h
    rw [ite_eq_left hD, ite_eq_left rfl, hS, single_mul_conjTranspose_single]
  · rw [ite_eq_right (fun h' => h (hD ▸ h').symm), ite_eq_right h, zero_mul]

omit [NeZero n] in
theorem writeP_conj_dbOf (H : Fin m → Fin n) (x : Fin m) (v : Fin n) (i : Fin (n + 1)) :
    writeP x v i * Matrix.single (dbOf m n H) (dbOf m n H) 1 * (writeP x v i)ᴴ =
      if i = (H x).castSucc then
        Matrix.single (dbOf m n (Function.update H x v)) (dbOf m n (Function.update H x v)) 1
      else 0 := by
  rw [mul_single_mul_conjTranspose, writeP, dbOp_single_mul_single]
  have hD : (dbIndex m n).symm (dbOf m n H) x = (H x).castSucc := by simp [dbOf]
  have hS : dbSet (dbOf m n H) x v.castSucc = dbOf m n (Function.update H x v) := by
    rw [dbSet, dbOf, dbOf, Equiv.symm_apply_apply]
    congr 1
    funext x'
    by_cases hx : x' = x
    · subst hx; simp
    · simp [Function.update_of_ne hx]
  by_cases h : i = (H x).castSucc
  · subst h
    rw [ite_eq_left hD, ite_eq_left rfl, hS, single_mul_conjTranspose_single]
  · rw [ite_eq_right (fun h' => h (hD ▸ h').symm), ite_eq_right h, zero_mul]

/-- A Kraus measurement of the right factor on a basis state that each operator but the one of
`i₀` annihilates and that the operator of `i₀` moves to the basis state `D'`. -/
theorem appendBasis_frameLeft_ofKraus {L X ι β C : Type} [Fintype L] [DecidableEq L]
    [Fintype X] [DecidableEq X] [Fintype ι] [DecidableEq ι] [Fintype C] (K : ι → Matrix X X ℂ)
    (hK : ∑ i, (K i)ᴴ * K i = 1) (D D' : X) (i₀ : ι)
    (hKD : ∀ i, K i * Matrix.single D D 1 * (K i)ᴴ =
      if i = i₀ then Matrix.single D' D' 1 else 0)
    (g : ι → SubInstrument (L × X) C β) :
    (appendBasis D).bind (fun _ => (frameLeft (SubInstrument.ofKraus K hK) L).bind g) =
      (appendBasis D').bind fun _ => g i₀ := by
  have key : ∀ i (ρ : Matrix L L ℂ),
      (frameLeft (SubInstrument.ofKraus K hK) L).branch i ((appendBasis D).branch () ρ) =
        if i = i₀ then (appendBasis D').branch () ρ else 0 := by
    intro i ρ
    ext x y
    rw [frameLeft_branch, MatrixMap.amplifyLeft_apply, DSubInstrument.branch_ofKraus_apply,
      MatrixMap.conj_apply]
    have hs : ((appendBasis D).branch () ρ).submatrix (x.1, ·) (y.1, ·) =
        ρ x.1 y.1 • Matrix.single D D 1 := by
      ext u v
      rw [submatrix_apply, appendBasis_branch_apply]
      simp only [Matrix.smul_apply, single_apply, smul_eq_mul]
      split_ifs <;> grind
    rw [hs, Matrix.mul_smul, Matrix.smul_mul, hKD]
    by_cases h : i = i₀
    · simp [h, appendBasis_branch_apply, single_apply, eq_comm]
    · simp [h]
  refine DSubInstrument.ext <| funext fun b => LinearMap.ext fun ρ => ?_
  rw [bind_unit_branch_apply, bind_unit_branch_apply, SubInstrument.bind,
    DSubInstrument.branch_bind_apply]
  simp only [key]
  rw [tsum_eq_single i₀ fun i hi => by simp [hi]]
  simp

theorem appendBasis_exec_purSys {α β C : Type} [Fintype C] (p : RWProg m n α)
    (H : Fin m → Fin n)
    (g : α → SubInstrument (Fin (m * n * w) × Fin ((n + 1) ^ m)) C β) :
    (appendBasis (dbOf m n H)).bind (fun _ =>
      (p.exec (fun x => frameLeft (readOpP x) _) (fun x v => frameLeft (writeOpP x v) _)).bind
        g) =
      (appendBasis (dbOf m n (p.run H).2)).bind fun _ => g (p.run H).1 := by
  induction p generalizing H with
  | ret r => simp only [RWProg.exec, RWProg.run, SubInstrument.pure_bind]
  | read x k ih =>
    rw [RWProg.exec, SubInstrument.bind_assoc, readOpP,
      appendBasis_frameLeft_ofKraus _ _ _ _ _ (readP_conj_dbOf H x)]
    simp only [truncEntry_castSucc, RWProg.run]
    exact ih (H x) H
  | write x v k ih =>
    rw [RWProg.exec, SubInstrument.bind_assoc, writeOpP, frameLeft_bind, SubInstrument.bind_assoc,
      appendBasis_frameLeft_ofKraus _ _ _ _ _ (writeP_conj_dbOf H x v)]
    simp only [frameLeft_pure, SubInstrument.pure_bind, RWProg.run]
    exact ih _

theorem stdQuery_branch_appendBasis (D : Fin ((n + 1) ^ m))
    (ρ : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ) :
    (stdQuery m n w).branch () ((appendBasis D).branch () ρ) =
      (appendBasis D).branch () ((CPComp.unitary (oracleU m n w (dbFun m n D))).branch () ρ) := by
  rw [stdQuery_eq, unitary_eq_ofKraus]
  ext x y
  simp only [DSubInstrument.branch_ofKraus_apply, MatrixMap.conj_apply, Matrix.mul_apply,
    conjTranspose_apply, stdMat_apply, appendBasis_branch_apply, Fintype.sum_prod_type]
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  by_cases hx : x2 = D <;> by_cases hy : y2 = D <;>
    simp [hx, hy, ite_mul, mul_ite, apply_ite star, Finset.sum_ite_eq, Finset.sum_ite_eq',
      ite_and]

theorem appendBasis_stdQuery {β C : Type} [Fintype C] (D : Fin ((n + 1) ^ m))
    (g : Unit → SubInstrument (Fin (m * n * w) × Fin ((n + 1) ^ m)) C β) :
    (appendBasis D).bind (fun _ => (stdQuery m n w).bind g) =
      (CPComp.unitary (oracleU m n w (dbFun m n D))).bind fun _ =>
        (appendBasis D).bind fun _ => g () := by
  refine DSubInstrument.ext <| funext fun b => LinearMap.ext fun ρ => ?_
  rw [bind_unit_branch_apply, bind_unit_branch_apply, stdQuery_branch_appendBasis,
    bind_unit_branch_apply, bind_unit_branch_apply]

theorem dbFun_dbOf (H : Fin m → Fin n) : dbFun m n (dbOf m n H) = H := by
  funext x
  simp [dbFun, dbOf, truncEntry_castSucc]

theorem purSys_step_sim (s₀ : σ) (sig : σ → Fin c → RWProg m n (σ × Fin a))
    (u : σ × (Fin m → Fin n)) (e : QROMEvent c) :
    (appendBasis (dbOf m n u.2)).bind (fun _ => (purSys (w := w) s₀ sig).step u.1 e) =
      (relabel (Equiv.prodPUnit (Fin (m * n * w))) ((chalRW (w := w) s₀ sig u.2).step u e)).bind
        fun p => (appendBasis (dbOf m n p.1.2)).bind fun _ =>
          SubInstrument.pure (p.1.1, p.2) := by
  have hC : relabel (Equiv.prodPUnit (Fin (m * n * w)))
      ((chalRW (w := w) s₀ sig u.2).step u e) = chalStep (fun t => t.2)
        (fun t y => ((sig t.1 y).run t.2).1.2)
        (fun t y => (((sig t.1 y).run t.2).1.1, ((sig t.1 y).run t.2).2)) u e := by
    rw [chalRW, chal, relabel_relabel, Equiv.symm_trans_self, relabel_refl]
  rw [hC]
  cases e with
  | query =>
    change (appendBasis _).bind (fun _ => (stdQuery m n w).bind fun _ =>
      SubInstrument.pure (u.1, QROMOut.done)) = _
    rw [appendBasis_stdQuery, dbFun_dbOf]
    simp only [chalStep, CPComp.qbind, CPComp.qpure, SubInstrument.bind_assoc,
      SubInstrument.pure_bind]
  | round y =>
    change (appendBasis _).bind (fun _ => (RWProg.exec _ _ (sig u.1 y)).bind fun r =>
      SubInstrument.pure (r.1, QROMOut.answer r.2)) = _
    rw [appendBasis_exec_purSys]
    simp only [chalStep, CPComp.qpure, SubInstrument.pure_bind]

theorem qview_chalRW (s₀ : σ) (sig : σ → Fin c → RWProg m n (σ × Fin a)) (H : Fin m → Fin n)
    (Z : QStrat ζ (QROMEvent c) (QROMOut a) (m * n * w)) :
    qview (chalRW (w := w) s₀ sig H) Z =
      (appendBasis (dbOf m n H)).bind fun _ =>
        (qloop (purSys (w := w) s₀ sig) Z Z.rounds (Z.init, s₀)).bind fun q =>
          discardRight.bind fun _ => SubInstrument.pure q.1 := by
  have hsim := qloop_sim (purSys (w := w) s₀ sig) (chalRW (w := w) s₀ sig H) Z
    (fun u => dbOf m n u.2) Prod.fst (fun u e => purSys_step_sim s₀ sig u e) Z.rounds Z.init
    (s₀, H)
  have h2 := congrArg (fun X => X.bind fun q => discardRight.bind fun _ =>
    SubInstrument.pure (A := Fin (m * n * w)) q.1) hsim
  simp only [SubInstrument.bind_assoc, SubInstrument.pure_bind,
    appendBasis_bind_discardRight] at h2
  have h3 := appendBasis_unit_discard (relabel (Equiv.prodPUnit (Fin (m * n * w)))
    (qloop (chalRW (w := w) s₀ sig H) Z Z.rounds (Z.init, (s₀, H))))
    (fun q => SubInstrument.pure q.1)
  rw [relabel_relabel, Equiv.self_trans_symm, relabel_refl] at h3
  rw [h2, ← h3]
  rfl

end Sim

/-! ## The view against the compressed challenger -/

section View

variable {m n w c a : ℕ} [NeZero n] {σ ζ : Type}

theorem decompL_bind_discardRight {C β : Type} [Fintype C]
    (g : SubInstrument (Fin (m * n * w)) C β) :
    (decompL m n w).bind (fun _ => discardRight.bind fun _ => g) =
      discardRight.bind fun _ => g := by
  have h : (discardRight (A := Fin (m * n * w)) (H := Fin ((n + 1) ^ m))).bind (fun _ => g) =
      discardOp.bind fun _ => g := by
    simp only [discardOp, SubInstrument.bind_assoc, SubInstrument.pure_bind]
  rw [h, decompL]
  exact frameLeft_unitaryOp_bind_discardOp _ _ _

/-- Dephasing the right factor before discarding it changes nothing. -/
theorem dephase_bind_discardRight {L X C β : Type} [Fintype L] [DecidableEq L] [Fintype X]
    [DecidableEq X] [Fintype C] (g : SubInstrument L C β) :
    (frameLeft (dephase X) L).bind (fun _ => discardRight.bind fun _ => g) =
      discardRight.bind fun _ => g := by
  refine DSubInstrument.ext <| funext fun b => LinearMap.ext fun ρ => ?_
  rw [bind_unit_branch_apply, SubInstrument.bind, DSubInstrument.branch_bind_apply,
    DSubInstrument.branch_bind_apply]
  refine tsum_congr fun r => congrArg _ ?_
  ext u v
  rw [discardRight_branch_apply, discardRight_branch_apply, submatrix_apply, submatrix_apply,
    frameLeft_dephase_apply, ite_eq_left rfl]

/-- Dephasing is measuring the register in its basis and preparing the measured state. -/
theorem frameLeft_dephase_eq {L X : Type} [Fintype L] [DecidableEq L] [Fintype X]
    [DecidableEq X] :
    frameLeft (dephase X) L = discardRight.bind fun r => appendBasis r := by
  refine DSubInstrument.ext <| funext fun u => LinearMap.ext fun ρ => ?_
  cases u
  rw [SubInstrument.bind, DSubInstrument.branch_bind_apply_univ]
  ext x y
  simp only [LinearMap.coe_sum, LinearMap.coe_comp, Finset.sum_apply, Function.comp_apply,
    Finset.sum_matrix_entry, frameLeft_dephase_apply, appendBasis_branch_apply,
    discardRight_branch_apply, submatrix_apply]
  obtain ⟨x1, x2⟩ := x
  obtain ⟨y1, y2⟩ := y
  rw [Finset.sum_eq_single x2 (fun k _ hk => by simp [Ne.symm hk]) (by simp)]
  by_cases h : x2 = y2
  · simp [h]
  · simp [h, Ne.symm h]

omit [NeZero n] in
theorem dbOf_injective : Function.Injective (dbOf m n) := fun H H' h => by
  have h2 := congrArg (dbIndex m n).symm h
  simp only [dbOf, Equiv.symm_apply_apply] at h2
  funext x
  exact Fin.castSucc_injective _ (congrFun h2 x)

omit [NeZero n] in
/-- The squared amplitude of a database in the decompressed empty database. -/
theorem decompDB_empty_weight (r : Fin ((n + 1) ^ m)) :
    decompDB m n r (dbEmptyIdx m n) * star (decompDB m n r (dbEmptyIdx m n)) =
      ((∏ x, (if (((dbIndex m n).symm r x : Fin (n + 1)) : ℕ) < n then (n : ℝ)⁻¹ else 0) : ℝ) :
        ℂ) := by
  rw [decompDB_apply_empty, star_prod, ← Finset.prod_mul_distrib]
  simp only [entryUniform_mul_star]
  rw [← Complex.ofReal_prod]

omit [NeZero n] in
theorem decompDB_empty_weight_dbOf (H : Fin m → Fin n) :
    decompDB m n (dbOf m n H) (dbEmptyIdx m n) * star (decompDB m n (dbOf m n H) (dbEmptyIdx m n)) =
      ((((n : ℝ) ^ m)⁻¹ : ℝ) : ℂ) := by
  rw [decompDB_empty_weight]
  simp [dbOf]

omit [NeZero n] in
theorem decompDB_empty_weight_of_not_mem (r : Fin ((n + 1) ^ m))
    (hr : r ∉ Finset.univ.image (dbOf m n)) :
    decompDB m n r (dbEmptyIdx m n) * star (decompDB m n r (dbEmptyIdx m n)) = 0 := by
  rw [decompDB_empty_weight]
  have : ∃ x, ¬ (((dbIndex m n).symm r x : Fin (n + 1)) : ℕ) < n := by
    by_contra hc
    push Not at hc
    refine hr (Finset.mem_image.mpr ⟨fun x => ⟨_, hc x⟩, Finset.mem_univ _, ?_⟩)
    simp only [dbOf]
    rw [← Equiv.eq_symm_apply]
    funext x
    rfl
  obtain ⟨x, hx⟩ := this
  rw [Finset.prod_eq_zero (Finset.mem_univ x) (by rw [ite_eq_right hx]), Complex.ofReal_zero]

/-- Decompressing the empty database and measuring it scales the state by the squared amplitude. -/
theorem discardRight_decompL_appendBasis (r : Fin ((n + 1) ^ m))
    (ρ : Matrix (Fin (m * n * w)) (Fin (m * n * w)) ℂ) :
    (discardRight (A := Fin (m * n * w))).branch r
        ((decompL m n w).branch () ((appendBasis (dbEmptyIdx m n)).branch () ρ)) =
      (decompDB m n r (dbEmptyIdx m n) * star (decompDB m n r (dbEmptyIdx m n))) • ρ := by
  ext i j
  rw [discardRight_branch_apply, submatrix_apply, decompL, frameLeft_branch,
    MatrixMap.amplifyLeft_apply]
  simp only [unitaryOp, DSubInstrument.branch_ofKraus_apply, MatrixMap.conj_apply, Matrix.mul_apply,
    conjTranspose_apply, submatrix_apply, appendBasis_branch_apply, Matrix.smul_apply,
    smul_eq_mul]
  simp only [ite_and, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, ite_true,
    ite_mul, zero_mul]
  ring

/-- Unfolding lemma of the branches of `CPComp.sample`. -/
theorem sample_branch_apply {d : ℕ} {α : Type} (μ : Prob.SDistr α) (x : α)
    (ρ : Matrix (Fin d) (Fin d) ℂ) :
    (CPComp.sample μ).branch x ρ = (((μ (some x)).toReal : ℝ) : ℂ) • ρ :=
  rfl

/-- Preparing the empty database, decompressing it and measuring it samples a uniformly random
function. -/
theorem appendBasis_decompL_discardRight {C β : Type} [Fintype C]
    (f : Fin ((n + 1) ^ m) → SubInstrument (Fin (m * n * w)) C β) :
    (appendBasis (dbEmptyIdx m n)).bind (fun _ => (decompL m n w).bind fun _ =>
      discardRight.bind f) =
      (CPComp.sample (Prob.SDistr.uniform (Fin m → Fin n))).bind fun H => f (dbOf m n H) := by
  refine DSubInstrument.ext <| funext fun b => LinearMap.ext fun ρ => ?_
  rw [bind_unit_branch_apply, bind_unit_branch_apply, SubInstrument.bind,
    DSubInstrument.branch_bind_apply, SubInstrument.bind, DSubInstrument.branch_bind_apply,
    tsum_fintype, tsum_fintype]
  simp only [discardRight_decompL_appendBasis, sample_branch_apply]
  rw [← Finset.sum_subset (Finset.subset_univ (Finset.univ.image (dbOf m n))) (fun r _ hr => by
    rw [decompDB_empty_weight_of_not_mem r hr, zero_smul, map_zero]),
    Finset.sum_image fun H _ H' _ h => dbOf_injective h]
  refine Finset.sum_congr rfl fun H _ => ?_
  rw [decompDB_empty_weight_dbOf, Prob.SDistr.uniform_apply_some]
  simp [ENNReal.toReal_inv]

/-- **The compressed challenger samples a random function.** The view of an environment
against the compressed challenger is the view against the classical challenger of a uniformly
random function. -/
theorem qview_cmpSys_eq_sample (s₀ : σ) (sig : σ → Fin c → RWProg m n (σ × Fin a))
    (Z : QStrat ζ (QROMEvent c) (QROMOut a) (m * n * w)) :
    qview (cmpSys (w := w) s₀ sig) Z =
      (CPComp.sample (Prob.SDistr.uniform (Fin m → Fin n))).bind fun H =>
        qview (chalRW (w := w) s₀ sig H) Z := by
  simp only [qview_chalRW]
  rw [← appendBasis_decompL_discardRight (w := w) (fun r => (appendBasis r).bind fun _ =>
    (qloop (purSys (w := w) s₀ sig) Z Z.rounds (Z.init, s₀)).bind fun q =>
      discardRight.bind fun _ => SubInstrument.pure q.1)]
  have hD := qloop_purSys_dephComm (w := w) s₀ sig Z Z.rounds (Z.init, s₀)
  unfold DephComm at hD
  have hY : ((qloop (purSys (w := w) s₀ sig) Z Z.rounds (Z.init, s₀)).bind fun q =>
        discardRight.bind fun _ => SubInstrument.pure q.1) =
      (frameLeft (dephase (Fin ((n + 1) ^ m))) (Fin (m * n * w))).bind fun _ =>
        (qloop (purSys (w := w) s₀ sig) Z Z.rounds (Z.init, s₀)).bind fun q =>
          discardRight.bind fun _ => SubInstrument.pure q.1 := by
    calc _ = (qloop (purSys (w := w) s₀ sig) Z Z.rounds (Z.init, s₀)).bind (fun q =>
          (frameLeft (dephase (Fin ((n + 1) ^ m))) (Fin (m * n * w))).bind fun _ =>
            discardRight.bind fun _ => SubInstrument.pure q.1) := by
          simp only [dephase_bind_discardRight]
      _ = _ := by
          rw [← SubInstrument.bind_assoc, hD]
          simp only [SubInstrument.bind_assoc, SubInstrument.pure_bind]
  unfold qview
  change (appendBasis (dbEmptyIdx m n)).bind (fun _ =>
    (qloop (cmpSys (w := w) s₀ sig) Z Z.rounds (Z.init, s₀)).bind fun q =>
      discardRight.bind fun _ => SubInstrument.pure q.1) = _
  rw [qloop_decConj s₀ sig Z Z.rounds (Z.init, s₀)]
  simp only [SubInstrument.bind_assoc, SubInstrument.pure_bind, decompL_bind_discardRight]
  conv_lhs => rw [hY, frameLeft_dephase_eq]
  simp only [SubInstrument.bind_assoc]

/-- **The compressed oracle with reprogramming.** The acceptance probability of an
environment against the compressed challenger is the average, over a uniformly random
function `H`, of its acceptance probability against the classical challenger of `H`. -/
theorem view_cmpSys_eq_avg (s₀ : σ) (sig : σ → Fin c → RWProg m n (σ × Fin a))
    (G : QStratAcc ζ (QROMEvent c) (QROMOut a) (m * n * w)) :
    viewAcc (cmpSys (w := w) s₀ sig) G =
      ∑ H : Fin m → Fin n, ((n : ℝ≥0∞) ^ m)⁻¹ * viewAcc (chalRW (w := w) s₀ sig H) G := by
  have h := CPComp.prTrue_sample_uniform_bind (d := m * n * w) (α := Fin m → Fin n)
    (fun H => CPComp.qbind (qview (chalRW (w := w) s₀ sig H) G.strat) G.post) G.init
  simp only [Fintype.card_fun, Fintype.card_fin, Nat.cast_pow] at h
  unfold viewAcc
  rw [qview_cmpSys_eq_sample, ← h]
  simp only [CPComp.qbind, CPComp.bind_eq_qbind, SubInstrument.bind_assoc]

end View

end CatCrypt.Quantum.QROM
