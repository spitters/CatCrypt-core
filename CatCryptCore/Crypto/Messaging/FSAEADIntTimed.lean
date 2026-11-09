/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.FSAEADInt
public import CatCryptCore.Crypto.OracleAdversaryPotential
public import CatCryptCore.Tactics.DeriveReduction
public import CatCryptCore.Tactics.DerivePMF
import CatCryptCore.Tactics.DeriveTimed
import CatCryptCore.Tactics.DeriveTimeBound

/-!
# Running time of the FS-AEAD integrity reductions

The time certificates of the FS-PRG distinguisher `fsIntPost`, the AEAD reduction `fsIntRed`
and its simulator `fsIntRedImpl` of `CatCryptCore.Crypto.Messaging.FSAEADInt`. The costed forms
and their erasure theorems are derived by `derive_timed` and `derive_reduction`.

A simulated query does not have a constant cost: an encryption reads the length of the log, a
decryption at the challenge position searches the log, and the key at a position `p` from the
number of outputs of the generator on walks the key chain `p` steps. The certificates bound the
time with the potential `s.1.log.length ≤ i` before the `i`-th query
(`OracleAdv.Timed.timeBound_simulate_inv_of_isQueryBoundBy`): the `i`-th query costs at most
`(g + 4) · fsIntDecPos d + fsIntQueryTime e dd g N i`, linear in `i` and in the position of a
decryption. For an adversary of time `T` with at most `q` queries whose decryption positions sum
to at most `J`, the time is `T + (g + 4) J + ∑_{i < q} fsIntQueryTime e dd g N i` plus a
constant, a polynomial of degree two in `q`.

No module imports this file.

## Main results

* `fsKeyOf_cost_le` — the cost of the key function at a position
* `fsIntPost.pmfStep.timed_bound`, `fsIntRedImpl.timed_bound` — the time of a simulated query
  under the potential
* `fsIntPost.timeBound_timed` — the time of the FS-PRG distinguisher
* `fsIntRed.timeBound_timed` — the time of the AEAD reduction
-/

set_option autoImplicit false

@[expose] public section

namespace CatCrypt.Crypto.Messaging

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.Assumptions

derive_timed fsIntRedImpl

derive_timed fsIntPost

derive_reduction fsIntRed (adv := A)

/-- `List.length` costs at most three per element and one more. -/
private theorem length_timedCost_le {α : Type} (l : List α) :
    List.length.timedCost l ≤ 3 * l.length + 1 := by
  induction l with
  | nil => simp [List.length.timedCost.eq_1]
  | cons a l ih => rw [List.length.timedCost.eq_2, List.length_cons]; omega

/-- `List.get` at the index `i` costs at most `2 i + 2`. -/
private theorem get_timedCost_le {α : Type} (l : List α) (i : Fin l.length) :
    List.get.timedCost l i ≤ 2 * i.val + 2 := by
  induction l with
  | nil => exact i.elim0
  | cons a l ih =>
    rcases i with ⟨_ | i, h⟩
    · rw [List.get.timedCost.eq_1]; omega
    · have := ih ⟨i, by simpa using h⟩
      rw [List.get.timedCost.eq_2]; dsimp only at this ⊢; omega

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

/-- The loop of `Fin.foldr` with a step of cost at most `k` costs at most `(k + 3) i + 1` on
`i` remaining steps. -/
private theorem foldr_loop_timedCost_le {α : Type} (n : ℕ) (f : Fin n → α → α)
    (fCost : Fin n → α → ℕ) {k : ℕ} (hf : ∀ i a, fCost i a ≤ k) (i : ℕ) :
    ∀ (h : i ≤ n) (a : α), Fin.foldr.loop.timedCost n f fCost i h a ≤ (k + 3) * i + 1 := by
  induction i with
  | zero => intro h a; simp [Fin.foldr.loop.timedCost]
  | succ i ih =>
    intro h a
    rw [Fin.foldr.loop.timedCost.eq_2]
    have := ih (by omega) (f ⟨i, h⟩ a)
    have := hf ⟨i, h⟩ a
    rw [Nat.mul_succ]; omega

section Time

variable {Sa W Ct : Type} [SampleableType W] [DecidableEq W] [DecidableEq Ct]

/-- The position of a decryption query, and zero for the other queries: the length of the walk
of the key chain that the query may need. -/
def fsIntDecPos : FSIntQuery W Ct → ℕ
  | .dec j _ _ => j
  | _ => 0

/-- The bound on the time of the `i`-th simulated query of the reductions of FS-AEAD integrity,
apart from the walk of the key chain to a decryption position, for encryptions of cost at most
`e`, decryptions of cost at most `dd`, generator steps of cost at most `g` and `N` outputs of
the generator. -/
def fsIntQueryTime (e dd g N i : ℕ) : ℕ :=
  4 * e + dd + 4 * ((g + 4) * i) + 30 * i + 50 * N + 4 * g + 200

omit [SampleableType W] [DecidableEq W] in
/-- The cost of the key function `fsKeyOf G ks sN` at the position `j`: a lookup in the outputs
`ks` below their length, a walk of the chain from `sN` above it. -/
theorem fsKeyOf_cost_le (G : PRGDef Sa (W × Sa)) (ks : List W) (sN : Sa)
    (stretchCost : Sa → ℕ) {g : ℕ} (hg : ∀ s, stretchCost s ≤ g) (j : ℕ) :
    1 + List.length.timedCost ks + (if h : j < ks.length then
        1 + List.get.timedCost ks ⟨j, h⟩ else
        1 + (2 + List.length.timedCost ks +
          (1 + (stretchCost ((fun s => (G.stretch s).2)^[j - ks.length] sN) +
            (1 + Nat.iterate.timedCost (fun s => (G.stretch s).2) (fun s => 1 + stretchCost s)
              (j - ks.length) sN))))) ≤
      6 * ks.length + (g + 4) * j + g + 12 := by
  have hl := length_timedCost_le ks
  have hm := Nat.mul_le_mul_left (g + 4) (Nat.sub_le j ks.length)
  split
  · next h =>
    have := get_timedCost_le ks ⟨j, h⟩
    dsimp only at this
    have : j ≤ (g + 4) * j := Nat.le_mul_of_pos_left j (by omega)
    omega
  · have := iterate_timedCost_le (fun s => (G.stretch s).2) (fun s => 1 + stretchCost s)
      (c := g + 1) (fun s => by have := hg s; omega) (j - ks.length) sN
    have := hg ((fun s => (G.stretch s).2)^[j - ks.length] sN)
    rw [show g + 1 + 3 = g + 4 by omega] at *
    omega

/-- **Time of a query of the simulator of `fsIntPost`.** From a state whose log has at most `i`
entries, a query `d` takes time at most `(g + 4) · fsIntDecPos d + fsIntQueryTime e dd g L i`,
`L` the number of outputs of the generator, and the log of the new state has at most `i + 1`
entries. -/
theorem fsIntPost.pmfStep.timed_bound (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (ks : List W × Sa) (s : FSIntSt Unit W Ct × Bool) (d : FSIntQuery W Ct)
    (encryptCost : W → W → W → ℕ) (stretchCost : Sa → ℕ) (decryptCost : W → Ct → W → ℕ)
    {e dd g : ℕ} (he : ∀ k m a, encryptCost k m a ≤ e) (hd : ∀ k c a, decryptCost k c a ≤ dd)
    (hg : ∀ s, stretchCost s ≤ g) (i : ℕ) (hi : s.1.log.length ≤ i) :
    OracleAdv.Timed.StepTimeBound (OracleAdv.Timed.delay 1
        (fsIntPost.pmfStep.timed G D ks s d encryptCost stretchCost decryptCost))
        ((g + 4) * fsIntDecPos d + fsIntQueryTime e dd g ks.1.length i) ∧
      OracleAdv.Timed.AllRet (fun y => y.2.1.log.length ≤ i + 1)
        (OracleAdv.Timed.delay 1
          (fsIntPost.pmfStep.timed G D ks s d encryptCost stretchCost decryptCost)).2 := by
  have hK := fsKeyOf_cost_le G ks.1 ks.2 stretchCost hg
  have hl := length_timedCost_le s.1.log
  have hm := Nat.mul_le_mul_left (g + 4) hi
  cases d with
  | enc m =>
    have := hK s.1.log.length
    have := he (fsKeyOf G ks.1 ks.2 s.1.log.length) m.1 m.2
    simp only [fsIntPost.pmfStep.timed, OracleAdv.Timed.delay, OracleAdv.Timed.bind,
      OracleAdv.Timed.StepTimeBound, OracleAdv.Timed.TimeBound, OracleAdv.Timed.AllRet,
      fsIntDecPos, fsIntQueryTime, fsKeyStep, List.length_cons, and_true]
    omega
  | dec j ad c =>
    have := hK j
    have := hd (fsKeyOf G ks.1 ks.2 j) c ad
    simp only [fsIntPost.pmfStep.timed, OracleAdv.Timed.delay, OracleAdv.Timed.bind,
      OracleAdv.Timed.StepTimeBound, OracleAdv.Timed.TimeBound, OracleAdv.Timed.AllRet,
      fsIntDecPos, fsIntQueryTime, fsKeyStep, and_true]
    split <;> omega
  | corrupt =>
    simp only [fsIntPost.pmfStep.timed, OracleAdv.Timed.delay, OracleAdv.Timed.bind,
      OracleAdv.Timed.StepTimeBound, OracleAdv.Timed.TimeBound, OracleAdv.Timed.AllRet,
      fsIntDecPos, fsIntQueryTime, fsKeyStep, and_true, Nat.mul_zero]
    omega

/-- **Time of `fsIntPost`.** For a costed adversary of time at most `T`, at most `q` queries and
decryption positions that sum to at most `J` on every path, encryptions of cost at most `e`,
decryptions of cost at most `dd` and generator steps of cost at most `g`, the costed
distinguisher on the outputs `ks.1` has time at most
`T + (g + 4) J + ∑_{i < q} fsIntQueryTime e dd g |ks.1| i + 1`. The potential of the simulation
is the length of the log, at most `i` before the `i`-th query. -/
theorem fsIntPost.timeBound_timed (G : PRGDef Sa (W × Sa)) (D : AEADDef W Ct)
    (A : OracleAdv.Timed (FSIntQuery W Ct) (FSIntAns Sa Ct W) Bool) (ks : List W × Sa)
    (encryptCost : W → W → W → ℕ) (stretchCost : Sa → ℕ) (decryptCost : W → Ct → W → ℕ)
    {T q J e dd g : ℕ} (hA : A.TimeBound T) (hq : A.erase.IsQueryBound q)
    (hJ : A.erase.IsQueryBoundBy fsIntDecPos J) (he : ∀ k m a, encryptCost k m a ≤ e)
    (hd : ∀ k c a, decryptCost k c a ≤ dd) (hg : ∀ s, stretchCost s ≤ g) :
    OracleAdv.Timed.StepTimeBound (fsIntPost.timed G D A ks encryptCost stretchCost decryptCost)
      (T + (g + 4) * J + ∑ i ∈ Finset.range q, fsIntQueryTime e dd g ks.1.length i + 1) := by
  have hS := OracleAdv.Timed.timeBound_simulate_inv_of_isQueryBoundBy
    (fun s d => OracleAdv.Timed.delay 1
      (fsIntPost.pmfStep.timed G D ks s d encryptCost stretchCost decryptCost))
    (fun d => (g + 4) * fsIntDecPos d) (fsIntQueryTime e dd g ks.1.length)
    (fun i s => s.1.log.length ≤ i)
    (fun i s d h => fsIntPost.pmfStep.timed_bound G D ks s d encryptCost stretchCost
      decryptCost he hd hg i h)
    hA (hJ.mul_left _) hq 0 (fsKeyInit, false) (by simp [fsKeyInit])
  simp only [Nat.zero_add] at hS
  obtain ⟨h1, h2⟩ := hS
  have hb := OracleAdv.Timed.timeBound_bind (n := 0) h2
    (f := fun x => (0, OracleAdv.Timed.ret x.2.2)) fun _ => ⟨le_refl _, trivial⟩
  unfold fsIntPost.timed fsIntPost.pmfTree.timed
  exact (OracleAdv.Timed.stepTimeBound_delay hb).mono (by omega)

/-- **Time of a query of `fsIntRedImpl`.** For a key function whose cost at the position `p` is
at most `κ + (g + 4) p`, from a state whose log has at most `i` entries, a query `d` takes time
at most `(g + 4) · fsIntDecPos d + 4 e + dd + 4 κ + 4 (g + 4) i + 30 i + 40`, and the log of
the new state has at most `i + 1` entries. -/
theorem fsIntRedImpl.timed_bound (D : AEADDef W Ct) (j : ℕ) (k : ℕ → W) (kCost : ℕ → ℕ)
    (s : FSIntSt Unit W Ct × Bool) (d : FSIntQuery W Ct) (encryptCost : W → W → W → ℕ)
    (decryptCost : W → Ct → W → ℕ) {e dd g κ : ℕ} (he : ∀ k m a, encryptCost k m a ≤ e)
    (hd : ∀ k c a, decryptCost k c a ≤ dd) (hk : ∀ p, kCost p ≤ κ + (g + 4) * p) (i : ℕ)
    (hi : s.1.log.length ≤ i) :
    OracleAdv.Timed.StepTimeBound
        (fsIntRedImpl.timed (Sa := Sa) D j k kCost s d encryptCost decryptCost)
        ((g + 4) * fsIntDecPos d +
          (4 * e + dd + 4 * κ + 4 * ((g + 4) * i) + 30 * i + 40)) ∧
      OracleAdv.Timed.AllRet (fun y => y.2.1.log.length ≤ i + 1)
        (fsIntRedImpl.timed (Sa := Sa) D j k kCost s d encryptCost decryptCost).2 := by
  have hl := length_timedCost_le s.1.log
  have hm := Nat.mul_le_mul_left (g + 4) hi
  cases d with
  | enc m =>
    have := hk s.1.log.length
    have := he (k s.1.log.length) m.1 m.2
    simp only [fsIntRedImpl.timed, OracleAdv.Timed.delay, OracleAdv.Timed.StepTimeBound,
      fsIntDecPos, Nat.mul_zero]
    split
    · simp only [OracleAdv.Timed.TimeBound, OracleAdv.Timed.AllRet]
      refine ⟨⟨by omega, by omega, fun a => ?_⟩, fun a => ?_⟩
      · cases a <;> simp only [OracleAdv.Timed.TimeBound, and_true] <;> omega
      · cases a <;> simp only [OracleAdv.Timed.AllRet, List.length_cons] <;> omega
    · simp only [OracleAdv.Timed.TimeBound, OracleAdv.Timed.AllRet, fsKeyStep,
        List.length_cons, and_true]
      omega
  | dec i' ad c =>
    have := hk i'
    have := hd (k i') c ad
    have := List.find?.timedCost_le (fun l : ℕ × W × W × Ct =>
      decide (l.1 = j ∧ l.2.2.1 = ad ∧ l.2.2.2 = c)) (fun _ => 1) (k := 1) (fun _ => le_rfl)
      s.1.log
    simp only [fsIntRedImpl.timed, OracleAdv.Timed.delay, OracleAdv.Timed.StepTimeBound,
      fsIntDecPos]
    split
    · simp only [OracleAdv.Timed.TimeBound, OracleAdv.Timed.AllRet]
      refine ⟨⟨by omega, by omega, fun a => ?_⟩, fun a => ?_⟩
      · cases a <;> simp only [OracleAdv.Timed.TimeBound, and_true] <;> omega
      · cases a <;> simp only [OracleAdv.Timed.AllRet] <;> omega
    · simp only [OracleAdv.Timed.TimeBound, OracleAdv.Timed.AllRet, and_true]
      split <;> omega
  | corrupt =>
    simp only [fsIntRedImpl.timed, OracleAdv.Timed.delay, OracleAdv.Timed.StepTimeBound,
      OracleAdv.Timed.TimeBound, OracleAdv.Timed.AllRet, fsIntDecPos, and_true, Nat.mul_zero]
    omega

/-- The bound of `fsIntRedImpl.timed_bound` with a step cost `c` in front of the query. -/
private theorem fsIntRedImpl.timed_bound_delay (D : AEADDef W Ct) (j : ℕ) (k : ℕ → W)
    (kCost : ℕ → ℕ) (s : FSIntSt Unit W Ct × Bool) (d : FSIntQuery W Ct)
    (encryptCost : W → W → W → ℕ) (decryptCost : W → Ct → W → ℕ) {e dd g κ c M : ℕ}
    (he : ∀ k m a, encryptCost k m a ≤ e) (hd : ∀ k c a, decryptCost k c a ≤ dd)
    (hk : ∀ p, kCost p ≤ κ + (g + 4) * p) (i : ℕ) (hi : s.1.log.length ≤ i)
    (hM : c + (4 * e + dd + 4 * κ + 4 * ((g + 4) * i) + 30 * i + 40) ≤ M) :
    OracleAdv.Timed.StepTimeBound (OracleAdv.Timed.delay c
        (fsIntRedImpl.timed (Sa := Sa) D j k kCost s d encryptCost decryptCost))
        ((g + 4) * fsIntDecPos d + M) ∧
      OracleAdv.Timed.AllRet (fun y => y.2.1.log.length ≤ i + 1)
        (OracleAdv.Timed.delay c
          (fsIntRedImpl.timed (Sa := Sa) D j k kCost s d encryptCost decryptCost)).2 := by
  obtain ⟨h1, h2⟩ := fsIntRedImpl.timed_bound (Sa := Sa) D j k kCost s d encryptCost
    decryptCost he hd hk i hi
  exact ⟨(OracleAdv.Timed.stepTimeBound_delay h1).mono (by omega), h2⟩

omit [SampleableType W] [DecidableEq W] [DecidableEq Ct] in
/-- A tree that runs a step-prefixed tree `S` of time at most `B` and returns a function of its
output, at one step more, has time at most `B + 1`. -/
private theorem stepTimeBound_one_bind_ret {D R β γ : Type} (S : ℕ × OracleAdv.Timed D R β)
    (f : β → γ) {B M : ℕ} (hS : OracleAdv.Timed.StepTimeBound S B) (hM : B + 1 ≤ M) :
    1 + S.1 + (S.2.bind fun x => (0, OracleAdv.Timed.ret (f x))).1 ≤ M ∧
      (S.2.bind fun x => (0, OracleAdv.Timed.ret (f x))).2.TimeBound
        (M - (1 + S.1 + (S.2.bind fun x => (0, OracleAdv.Timed.ret (f x))).1)) := by
  obtain ⟨h1, h2⟩ := hS
  obtain ⟨h3, h4⟩ := OracleAdv.Timed.timeBound_bind (n := 0) h2
    (f := fun x => (0, OracleAdv.Timed.ret (f x))) fun _ => ⟨le_refl _, trivial⟩
  exact ⟨by omega, h4.mono (by omega)⟩

/-- **Time of `fsIntRed`.** For a costed adversary of time at most `T`, at most `q` queries and
decryption positions that sum to at most `J` on every path, encryptions of cost at most `e`,
decryptions of cost at most `dd` and generator steps of cost at most `g`, the costed AEAD
reduction with `N` uniform outputs has time at most
`T + (g + 4) J + ∑_{i < q} fsIntQueryTime e dd g N i + 3`. The potential of the simulation is
the length of the log, at most `i` before the `i`-th query. -/
theorem fsIntRed.timeBound_timed [Fintype Sa] [Nonempty Sa] (G : PRGDef Sa (W × Sa))
    (D : AEADDef W Ct) (N j : ℕ) (A : OracleAdv.Timed (FSIntQuery W Ct) (FSIntAns Sa Ct W) Bool)
    (stretchCost : Sa → ℕ) (encryptCost : W → W → W → ℕ) (decryptCost : W → Ct → W → ℕ)
    {T q J e dd g : ℕ} (hA : A.TimeBound T) (hq : A.erase.IsQueryBound q)
    (hJ : A.erase.IsQueryBoundBy fsIntDecPos J) (he : ∀ k m a, encryptCost k m a ≤ e)
    (hd : ∀ k c a, decryptCost k c a ≤ dd) (hg : ∀ s, stretchCost s ≤ g) :
    OracleAdv.Timed.StepTimeBound (fsIntRed.timed G D N j A stretchCost encryptCost decryptCost)
      (T + (g + 4) * J + ∑ i ∈ Finset.range q, fsIntQueryTime e dd g N i + 3) := by
  unfold fsIntRed.timed
  refine ⟨Nat.zero_le _, ?_⟩
  simp only [OracleAdv.Timed.TimeBound, Nat.sub_zero]
  refine ⟨by omega, fun v => ⟨Nat.zero_le _, by omega, fun sN => ?_⟩⟩
  have hF := foldr_loop_timedCost_le N (fun x1 x2 => v x1 :: x2) (fun _ _ => 1) (k := 1)
    (fun _ _ => le_rfl) N le_rfl []
  have hlen : (List.ofFn v).length = N := List.length_ofFn
  refine stepTimeBound_one_bind_ret _ _
    (B := T + (g + 4) * J + ∑ i ∈ Finset.range q, fsIntQueryTime e dd g N i) ?_ (by omega)
  refine (OracleAdv.Timed.timeBound_simulate_inv_of_isQueryBoundBy _
    (fun d => (g + 4) * fsIntDecPos d) (fsIntQueryTime e dd g N)
    (fun i s => s.1.log.length ≤ i) (fun i s d h => ?_) hA (hJ.mul_left _) hq 0
    (fsKeyInit, false) (by simp [fsKeyInit])).mono (by simp only [Nat.zero_add, le_refl])
  refine fsIntRedImpl.timed_bound_delay D j _ _ s d encryptCost decryptCost
    (κ := 10 * N + g + 18) he hd (fun p => ?_) i h ?_
  · have := fsKeyOf_cost_le G (List.ofFn v) sN stretchCost hg p
    omega
  · simp only [fsIntQueryTime]
    omega

end Time

end CatCrypt.Crypto.Messaging
