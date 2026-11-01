/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Party.QProg
public import CatCryptCore.Tactics.ScottInduction
public import CatCryptCore.Quantum.SubInstrumentOrder

/-!
# Weakest preconditions of quantum party programs

A program logic for one activation of a quantum party program `Party.QProg R E O α`. A
postcondition is an effect on the register `R` for every outcome of the activation, the pair of
the residual program and the output (`V : QProg R E O α × O → Matrix R R ℂ`). A precondition is
given by its expectation functional: the weakest precondition of a program at `V`,
`QProg.wp p e V`, maps a state `ρ` to the expected value of `V` after the activation of `p` on
the event `e` from `ρ`, the pairing `tr (wp(V) ρ)` of the Heisenberg dual of the activation. It
is defined by recursion on the program, phase by phase (`QProg.wpEmit`, `QProg.wpAwait`): an
operation `opN q k` sums the weakest preconditions of the continuations over the branches of the
subinstrument `q`, a `send` reads the postcondition, and a return in the await phase continues
with the precondition of the restart.

The expectation of a family of effects after a subinstrument is `QProg.expect`, valued in
`ℝ≥0∞` so that the sums over the countably many outcomes of a subinstrument need no summability
side condition. Partial correctness `QProg.PCorrect P c Q` bounds the expected violation of the
postcondition `Q` by the violation `1 - P` of the precondition: failure and divergence count as
success.

The unbounded loop activation `QProg.loopActω body` is the supremum of the iterates of the
one-step unfolding `QProg.loopFun body` (an iteration that returns before receiving restarts in
the same activation); the step of the loop system `QProg.loopQSys body s₀` is its second iterate.
The loop rule of partial correctness is proved by Scott induction along these iterates.

Search words: weakest precondition, quantum party, program logic, frame rule, loop rule,
invariant, partial correctness, Scott induction, expectation of an effect, subinstrument.

## Main definitions

* `QProg.expect c V ρ`: the expected value of the effects `V` after the subinstrument `c`.
* `QProg.wpEmit`, `QProg.wpAwait`: the weakest preconditions of the two phases of an
  activation.
* `QProg.wpStep`, `QProg.wp`: the weakest precondition of an activation, with a restart and
  without one.
* `QProg.PCorrect`: partial correctness of a subinstrument.
* `QProg.loopFun`, `QProg.loopActω`: the one-step unfolding and the unbounded activation of a
  loop.

## Main results

* `QProg.expect_bind`: the expectation after a sequencing is the expectation of the
  continuations.
* `QProg.wpEmit_eq_expect`, `QProg.wpAwait_eq_expect`, `QProg.wpStep_eq_expect`,
  `QProg.wp_eq_expect_act`: soundness, the weakest precondition is the expectation after the
  denotation of the activation (`QProg.emitK`, `QProg.awaitK`, `QProg.stepWith`, `QProg.act`).
* `QProg.wpEmit_bind`, `QProg.wpAwait_bind`: the bind rule.
* `QProg.wp_frameR`, `QProg.wp_frameL`: the frame rule, a program framed on one factor of the
  register leaves the effect on the other factor untouched.
* `QProg.loopActω_pcorrect`, `QProg.loopQSys_pcorrect`: the loop rule of partial correctness
  from an invariant.
* `QProg.qotpReal_done_ignored`: in the real world of the reactive quantum one-time pad, an
  activation at the phase `done` outputs `ignored` with certainty, up to failure.
-/

@[expose] public section

set_option autoImplicit false

open scoped ComplexOrder Topology Kronecker ENNReal
open Filter OmegaCompletePartialOrder

noncomputable section

namespace CatCrypt.Crypto.Party

open CatCrypt.Core _root_.Quantum CatCrypt.Quantum.ReactiveUC

namespace QProg

variable {R : Type} [Fintype R] {E O α β σ X Y : Type}

/-! ## Expectations of effects after a subinstrument -/

/-- The trace pairing of two Hermitian matrices is real. -/
theorem trace_mul_im_eq_zero {A B : Matrix R R ℂ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    (A * B).trace.im = 0 := by
  have h : star (A * B).trace = (A * B).trace := by
    rw [← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul, hA.eq, hB.eq,
      Matrix.trace_mul_comm]
  exact Complex.conj_eq_iff_im.1 h

/-- The expected value of the effects `V` (one per outcome) after the subinstrument `c` from the
state `ρ`: the sum over the outcomes `x` of `tr (V x · c.branch x ρ)`. -/
def expect (c : SubInstrument R R X) (V : X → Matrix R R ℂ) (ρ : Matrix R R ℂ) : ℝ≥0∞ :=
  ∑' x, ENNReal.ofReal ((V x * c.branch x ρ).trace.re)

/-- The expectation after `pure x` is the pairing of `V x` with the state. -/
theorem expect_pure (x : X) (V : X → Matrix R R ℂ) (ρ : Matrix R R ℂ) :
    expect (SubInstrument.pure x) V ρ = ENNReal.ofReal ((V x * ρ).trace.re) := by
  classical
  rw [expect, tsum_eq_single x fun y hy => by simp [SubInstrument.branch_pure_of_ne hy]]
  simp

/-- The expectation after a failure is zero. -/
theorem expect_fail (V : X → Matrix R R ℂ) (ρ : Matrix R R ℂ) :
    expect (SubInstrument.fail : SubInstrument R R X) V ρ = 0 := by
  simp [expect, DSubInstrument.branch_fail]

/-- **Sequencing**: the expectation after `q.bind k` is the sum over the outcomes of `q` of the
expectations after the continuations. -/
theorem expect_bind {q : SubInstrument R R X} {k : X → SubInstrument R R Y}
    {V : Y → Matrix R R ℂ} (hV : ∀ y, (V y).PosSemidef) {ρ : Matrix R R ℂ}
    (hρ : ρ.PosSemidef) :
    expect (q.bind k) V ρ = ∑' x, expect (k x) V (q.branch x ρ) := by
  have hterm : ∀ y, ENNReal.ofReal ((V y * (q.bind k).branch y ρ).trace.re) =
      ∑' x, ENNReal.ofReal ((V y * (k x).branch y (q.branch x ρ)).trace.re) := by
    intro y
    have h1 : HasSum (fun x => (V y * (k x).branch y (q.branch x ρ)).trace.re)
        (V y * (q.bind k).branch y ρ).trace.re := by
      rw [DSubInstrument.branch_bind_apply]
      let g : Matrix R R ℂ →+ ℝ := AddMonoidHom.mk' (fun M => (V y * M).trace.re)
        fun a b => by simp [Matrix.mul_add, Matrix.trace_add]
      exact (SubInstrument.summable_bind_apply q k y ρ).hasSum.map g
        (Complex.continuous_re.comp (continuous_const.mul continuous_id).matrix_trace)
    rw [← h1.tsum_eq, ENNReal.ofReal_tsum_of_nonneg (fun x => (hV y).trace_mul_re_nonneg
      (DSubInstrument.posSemidef_branch_apply (k x) y
        (DSubInstrument.posSemidef_branch_apply q x hρ))) h1.summable]
  simp only [expect, hterm]
  exact ENNReal.tsum_comm

/-- An upper bound of the expectations after the elements of a chain bounds the expectation
after its supremum. -/
theorem expect_ωSup_le (c : Chain (SubInstrument R R X)) (V : X → Matrix R R ℂ)
    (ρ : Matrix R R ℂ) {b : ℝ≥0∞} (h : ∀ n, expect (c n) V ρ ≤ b) :
    expect (ωSup c) V ρ ≤ b := by
  rw [expect, ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  have hlim : Tendsto (fun n => ∑ x ∈ s, ENNReal.ofReal ((V x * (c n).branch x ρ).trace.re))
      atTop (𝓝 (∑ x ∈ s, ENNReal.ofReal ((V x * (ωSup c).branch x ρ).trace.re))) := by
    refine tendsto_finsetSum _ fun x _ => ?_
    have hc : Continuous fun M : Matrix R R ℂ => ENNReal.ofReal ((V x * M).trace.re) :=
      ENNReal.continuous_ofReal.comp (by fun_prop)
    exact (hc.tendsto _).comp (SubInstrument.tendsto_branch_ωSup c x ρ)
  exact le_of_tendsto' hlim fun n => (ENNReal.sum_le_tsum s).trans (h n)

/-! ## The weakest precondition of an activation -/

/-- The weakest precondition of the emit phase: at a `send o p` the precondition `s o p`, at a
return the precondition `r`, at an operation the sum over its branches, and zero at a receive
and at a failure. -/
def wpEmit (s : O → QProg R E O α → Matrix R R ℂ → ℝ≥0∞) (r : α → Matrix R R ℂ → ℝ≥0∞) :
    QProg R E O α → Matrix R R ℂ → ℝ≥0∞
  | .ret a => r a
  | .recv _ => 0
  | .send o p => s o p
  | .opN q k => fun ρ => ∑' n, wpEmit s r (k n) (q.branch n ρ)
  | .fail => 0

/-- The weakest precondition of the await phase on the event `e`: at a return the precondition
`rA`, at a receive the emit phase of the continuation at `e`, at an operation the sum over its
branches, and zero at a send and at a failure. -/
def wpAwait (e : E) (s : O → QProg R E O α → Matrix R R ℂ → ℝ≥0∞)
    (rA rE : α → Matrix R R ℂ → ℝ≥0∞) : QProg R E O α → Matrix R R ℂ → ℝ≥0∞
  | .ret a => rA a
  | .recv k => wpEmit s rE (k e)
  | .send _ _ => 0
  | .opN q k => fun ρ => ∑' n, wpAwait e s rA rE (k n) (q.branch n ρ)
  | .fail => 0

/-- The postcondition at the end of an activation, read at the output `o` and the residual
program `t`. -/
def post (V : QProg R E O α × O → Matrix R R ℂ) (o : O) (t : QProg R E O α)
    (ρ : Matrix R R ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal ((V (t, o) * ρ).trace.re)

/-- The weakest precondition of an activation of `p` on `e` at the postcondition `V`, where a
return of `a` in the await phase continues with the precondition `W a e`. -/
def wpStep (W : α → E → Matrix R R ℂ → ℝ≥0∞) (p : QProg R E O α) (e : E)
    (V : QProg R E O α × O → Matrix R R ℂ) : Matrix R R ℂ → ℝ≥0∞ :=
  wpAwait e (post V) (fun a => W a e) 0 p

/-- The weakest precondition of an activation of `p` on `e` at the postcondition `V`: a return
in the await phase fails. -/
def wp (p : QProg R E O α) (e : E) (V : QProg R E O α × O → Matrix R R ℂ) :
    Matrix R R ℂ → ℝ≥0∞ :=
  wpStep 0 p e V

/-- **Soundness of the emit phase**: the weakest precondition is the expectation after the
emit phase. -/
theorem wpEmit_eq_expect (s : O → QProg R E O α → SubInstrument R R X)
    (r : α → SubInstrument R R X) {V : X → Matrix R R ℂ} (hV : ∀ x, (V x).PosSemidef)
    (p : QProg R E O α) {ρ : Matrix R R ℂ} (hρ : ρ.PosSemidef) :
    wpEmit (fun o q => expect (s o q) V) (fun a => expect (r a) V) p ρ =
      expect (emitK s r p) V ρ := by
  induction p generalizing ρ with
  | ret a => rfl
  | recv k => simp [wpEmit, expect_fail]
  | send o p => rfl
  | opN q k ih =>
    rw [emitK_opN, expect_bind hV hρ]
    exact tsum_congr fun n => ih n (DSubInstrument.posSemidef_branch_apply _ _ hρ)
  | fail => simp [wpEmit, expect_fail]

/-- **Soundness of the await phase**: the weakest precondition is the expectation after the
await phase. -/
theorem wpAwait_eq_expect (e : E) (s : O → QProg R E O α → SubInstrument R R X)
    (rA rE : α → SubInstrument R R X) {V : X → Matrix R R ℂ} (hV : ∀ x, (V x).PosSemidef)
    (p : QProg R E O α) {ρ : Matrix R R ℂ} (hρ : ρ.PosSemidef) :
    wpAwait e (fun o q => expect (s o q) V) (fun a => expect (rA a) V)
        (fun a => expect (rE a) V) p ρ =
      expect (awaitK e s rA rE p) V ρ := by
  induction p generalizing ρ with
  | ret a => rfl
  | recv k => exact wpEmit_eq_expect s rE hV (k e) hρ
  | send o p => simp [wpAwait, expect_fail]
  | opN q k ih =>
    rw [awaitK_opN, expect_bind hV hρ]
    exact tsum_congr fun n => ih n (DSubInstrument.posSemidef_branch_apply _ _ hρ)
  | fail => simp [wpAwait, expect_fail]

/-- **Soundness of an activation with restart**: the weakest precondition is the expectation
after `stepWith`. -/
theorem wpStep_eq_expect (restart : α → E → SubInstrument R R (QProg R E O α × O))
    {V : QProg R E O α × O → Matrix R R ℂ} (hV : ∀ x, (V x).PosSemidef) (p : QProg R E O α)
    (e : E) {ρ : Matrix R R ℂ} (hρ : ρ.PosSemidef) :
    wpStep (fun a e => expect (restart a e) V) p e V ρ = expect (stepWith restart p e) V ρ := by
  have hs : (post V : O → QProg R E O α → Matrix R R ℂ → ℝ≥0∞) =
      fun o q => expect (SubInstrument.pure (q, o)) V := by
    funext o q ρ
    simp [post, expect_pure]
  have h0 : (0 : α → Matrix R R ℂ → ℝ≥0∞) =
      fun _ => expect (SubInstrument.fail : SubInstrument R R (QProg R E O α × O)) V := by
    funext a ρ
    simp [expect_fail]
  rw [stepWith_def, wpStep, hs, h0]
  exact wpAwait_eq_expect e _ _ _ hV p hρ

/-- **Soundness of an activation**: the weakest precondition is the expectation after
`act`. -/
theorem wp_eq_expect_act {V : QProg R E O α × O → Matrix R R ℂ} (hV : ∀ x, (V x).PosSemidef)
    (p : QProg R E O α) (e : E) {ρ : Matrix R R ℂ} (hρ : ρ.PosSemidef) :
    wp p e V ρ = expect (act p e) V ρ := by
  have h0 : (0 : α → E → Matrix R R ℂ → ℝ≥0∞) =
      fun _ _ => expect (SubInstrument.fail : SubInstrument R R (QProg R E O α × O)) V := by
    funext a e ρ
    simp [expect_fail]
  rw [act_def, wp, h0]
  exact wpStep_eq_expect _ hV p e hρ

/-! ## The bind rule -/

/-- **Bind rule** of the emit phase: a return of `p` continues with the weakest precondition of
`f`. -/
theorem wpEmit_bind (s : O → QProg R E O β → Matrix R R ℂ → ℝ≥0∞)
    (r : β → Matrix R R ℂ → ℝ≥0∞) (p : QProg R E O α) (f : α → QProg R E O β) :
    wpEmit s r (ProgE.bind p f) =
      wpEmit (fun o q => s o (ProgE.bind q f)) (fun a => wpEmit s r (f a)) p := by
  induction p with
  | opN q k ih => simp only [ProgE.bind, wpEmit, ih]
  | _ => rfl

/-- **Bind rule** of the await phase: a return of `p` continues with the weakest precondition of
`f`, in the await phase or in the emit phase. -/
theorem wpAwait_bind (e : E) (s : O → QProg R E O β → Matrix R R ℂ → ℝ≥0∞)
    (rA rE : β → Matrix R R ℂ → ℝ≥0∞) (p : QProg R E O α) (f : α → QProg R E O β) :
    wpAwait e s rA rE (ProgE.bind p f) =
      wpAwait e (fun o q => s o (ProgE.bind q f)) (fun a => wpAwait e s rA rE (f a))
        (fun a => wpEmit s rE (f a)) p := by
  induction p with
  | recv k => simp only [ProgE.bind, wpAwait, wpEmit_bind]
  | opN q k ih => simp only [ProgE.bind, wpAwait, ih]
  | _ => rfl

/-! ## The frame rule -/

section Frame

variable {M N : Type} [Fintype M] [Fintype N]

/-- The expectation of `V ⊗ F` after a subinstrument framed on the left factor, from a product
state, is the expectation of `V` times the pairing of `F` with the right factor. -/
theorem expect_frame (c : SubInstrument M M X) {V : X → Matrix M M ℂ}
    (hV : ∀ x, (V x).PosSemidef) {F : Matrix N N ℂ} (hF : F.PosSemidef) {ρ : Matrix M M ℂ}
    {τ : Matrix N N ℂ} (hρ : ρ.PosSemidef) (hτ : τ.PosSemidef) :
    expect (c.frame N) (fun x => V x ⊗ₖ F) (ρ ⊗ₖ τ) =
      expect c V ρ * ENNReal.ofReal ((F * τ).trace.re) := by
  rw [expect, expect, ← ENNReal.tsum_mul_right]
  refine tsum_congr fun x => ?_
  rw [DSubInstrument.branch_frame_apply, _root_.Quantum.MatrixMap.amplify_kronecker,
    ← Matrix.mul_kronecker_mul, Matrix.trace_kronecker, Complex.mul_re,
    trace_mul_im_eq_zero hF.isHermitian hτ.isHermitian, mul_zero, sub_zero,
    ENNReal.ofReal_mul ((hV x).trace_mul_re_nonneg
      (DSubInstrument.posSemidef_branch_apply _ _ hρ))]

/-- The expectation of `F ⊗ V` after a subinstrument framed on the right factor, from a product
state, is the pairing of `F` with the left factor times the expectation of `V`. -/
theorem expect_frameLeft (c : SubInstrument N N X) {V : X → Matrix N N ℂ}
    {F : Matrix M M ℂ} (hF : F.PosSemidef) {ρ : Matrix M M ℂ}
    (τ : Matrix N N ℂ) (hρ : ρ.PosSemidef) :
    expect (CatCrypt.Quantum.OpenSystem.frameLeft c M) (fun x => F ⊗ₖ V x) (ρ ⊗ₖ τ) =
      ENNReal.ofReal ((F * ρ).trace.re) * expect c V τ := by
  rw [expect, expect, ← ENNReal.tsum_mul_left]
  refine tsum_congr fun x => ?_
  change ENNReal.ofReal (((F ⊗ₖ V x) * (c.branch x).amplifyLeft M (ρ ⊗ₖ τ)).trace.re) = _
  rw [_root_.Quantum.MatrixMap.amplifyLeft_kronecker,
    ← Matrix.mul_kronecker_mul, Matrix.trace_kronecker, Complex.mul_re,
    trace_mul_im_eq_zero hF.isHermitian hρ.isHermitian, zero_mul, sub_zero,
    ENNReal.ofReal_mul (hF.trace_mul_re_nonneg hρ)]

/-- **Frame rule** on the left factor: the weakest precondition of the framed program `p.frameR
N` at a postcondition `V ⊗ F`, from a product state, is the weakest precondition of `p` at `V`
times the pairing of `F` with the right factor, which `p` leaves untouched. -/
theorem wp_frameR (p : QProg M E O α) (e : E) {V : QProg M E O α × O → Matrix M M ℂ}
    (hV : ∀ x, (V x).PosSemidef) {W : QProg (M × N) E O α × O → Matrix (M × N) (M × N) ℂ}
    (hW : ∀ x, (W x).PosSemidef) {F : Matrix N N ℂ} (hF : F.PosSemidef)
    (hWV : ∀ t o, W (t.frameR N, o) = V (t, o) ⊗ₖ F) {ρ : Matrix M M ℂ} {τ : Matrix N N ℂ}
    (hρ : ρ.PosSemidef) (hτ : τ.PosSemidef) :
    wp (p.frameR N) e W (ρ ⊗ₖ τ) = wp p e V ρ * ENNReal.ofReal ((F * τ).trace.re) := by
  rw [wp_eq_expect_act hW _ _ (hρ.kronecker hτ), act_frameR, expect_bind hW (hρ.kronecker hτ),
    wp_eq_expect_act hV _ _ hρ, ← expect_frame _ hV hF hρ hτ]
  simp only [expect_pure, hWV]
  rfl

/-- **Frame rule** on the right factor: the weakest precondition of the framed program
`p.frameL M` at a postcondition `F ⊗ V`, from a product state, is the pairing of `F` with the
left factor, which `p` leaves untouched, times the weakest precondition of `p` at `V`. -/
theorem wp_frameL (p : QProg N E O α) (e : E) {V : QProg N E O α × O → Matrix N N ℂ}
    (hV : ∀ x, (V x).PosSemidef) {W : QProg (M × N) E O α × O → Matrix (M × N) (M × N) ℂ}
    (hW : ∀ x, (W x).PosSemidef) {F : Matrix M M ℂ} (hF : F.PosSemidef)
    (hWV : ∀ t o, W (t.frameL M, o) = F ⊗ₖ V (t, o)) {ρ : Matrix M M ℂ} {τ : Matrix N N ℂ}
    (hρ : ρ.PosSemidef) (hτ : τ.PosSemidef) :
    wp (p.frameL M) e W (ρ ⊗ₖ τ) = ENNReal.ofReal ((F * ρ).trace.re) * wp p e V τ := by
  rw [wp_eq_expect_act hW _ _ (hρ.kronecker hτ), act_frameL, expect_bind hW (hρ.kronecker hτ),
    wp_eq_expect_act hV _ _ hτ, ← expect_frameLeft _ hF τ hρ]
  simp only [expect_pure, hWV]
  rfl

end Frame

/-! ## Bounds by the trace -/

/-- A sum over the branches of a subinstrument of functionals bounded by the trace is bounded by
the trace. -/
theorem tsum_le_trace (q : SubInstrument R R ℕ) {W : ℕ → Matrix R R ℂ → ℝ≥0∞}
    (hW : ∀ n ρ, ρ.PosSemidef → W n ρ ≤ ENNReal.ofReal ρ.trace.re) {ρ : Matrix R R ℂ}
    (hρ : ρ.PosSemidef) : ∑' n, W n (q.branch n ρ) ≤ ENNReal.ofReal ρ.trace.re := by
  calc ∑' n, W n (q.branch n ρ)
      ≤ ∑' n, ENNReal.ofReal (q.branch n ρ).trace.re :=
        ENNReal.tsum_le_tsum fun n => hW n _ (DSubInstrument.posSemidef_branch_apply q n hρ)
    _ = ENNReal.ofReal (∑' n, (q.branch n ρ).trace.re) :=
        (ENNReal.ofReal_tsum_of_nonneg
          (fun n => DSubInstrument.trace_re_branch_apply_nonneg q n hρ)
          (q.isCPTNIFamily.summable_trace_re_apply hρ)).symm
    _ ≤ ENNReal.ofReal ρ.trace.re := ENNReal.ofReal_le_ofReal (q.tsum_trace_re_le hρ)

/-- The weakest precondition of the emit phase at preconditions bounded by the trace is bounded
by the trace. -/
theorem wpEmit_le_trace {s : O → QProg R E O α → Matrix R R ℂ → ℝ≥0∞}
    {r : α → Matrix R R ℂ → ℝ≥0∞}
    (hs : ∀ o q ρ, ρ.PosSemidef → s o q ρ ≤ ENNReal.ofReal ρ.trace.re)
    (hr : ∀ a ρ, ρ.PosSemidef → r a ρ ≤ ENNReal.ofReal ρ.trace.re) (p : QProg R E O α)
    {ρ : Matrix R R ℂ} (hρ : ρ.PosSemidef) : wpEmit s r p ρ ≤ ENNReal.ofReal ρ.trace.re := by
  induction p generalizing ρ with
  | ret a => exact hr a ρ hρ
  | recv k => exact bot_le
  | send o p => exact hs o p ρ hρ
  | opN q k ih => exact tsum_le_trace q (fun n _ h => ih n h) hρ
  | fail => exact bot_le

/-- The weakest precondition of the await phase at preconditions bounded by the trace is bounded
by the trace. -/
theorem wpAwait_le_trace {e : E} {s : O → QProg R E O α → Matrix R R ℂ → ℝ≥0∞}
    {rA rE : α → Matrix R R ℂ → ℝ≥0∞}
    (hs : ∀ o q ρ, ρ.PosSemidef → s o q ρ ≤ ENNReal.ofReal ρ.trace.re)
    (hA : ∀ a ρ, ρ.PosSemidef → rA a ρ ≤ ENNReal.ofReal ρ.trace.re)
    (hE : ∀ a ρ, ρ.PosSemidef → rE a ρ ≤ ENNReal.ofReal ρ.trace.re) (p : QProg R E O α)
    {ρ : Matrix R R ℂ} (hρ : ρ.PosSemidef) :
    wpAwait e s rA rE p ρ ≤ ENNReal.ofReal ρ.trace.re := by
  induction p generalizing ρ with
  | ret a => exact hA a ρ hρ
  | recv k => exact wpEmit_le_trace hs hE (k e) hρ
  | send o p => exact bot_le
  | opN q k ih => exact tsum_le_trace q (fun n _ h => ih n h) hρ
  | fail => exact bot_le

/-! ## The unbounded loop activation -/

/-- The failing subinstrument is below every subinstrument in Selinger's order. -/
theorem fail_le (c : SubInstrument R R X) : (SubInstrument.fail : SubInstrument R R X) ≤ c :=
  SubInstrument.le_def.2 fun a => by
    simpa [DSubInstrument.branch_fail] using c.isCP_branch a

/-- The await phase is monotone in the subinstrument it continues with at a return. -/
theorem awaitK_mono (e : E) (s : O → QProg R E O α → SubInstrument R R X)
    {rA rA' : α → SubInstrument R R X} (rE : α → SubInstrument R R X) (h : rA ≤ rA')
    (p : QProg R E O α) : awaitK e s rA rE p ≤ awaitK e s rA' rE p := by
  induction p with
  | ret a => exact h a
  | opN q k ih => exact SubInstrument.bind_mono_right q fun n => ih n
  | _ => exact le_rfl

/-- The weakest precondition of the await phase is monotone, on positive semidefinite states, in
the precondition at a return. -/
theorem wpAwait_mono (e : E) (s : O → QProg R E O α → Matrix R R ℂ → ℝ≥0∞)
    {rA rA' : α → Matrix R R ℂ → ℝ≥0∞} (rE : α → Matrix R R ℂ → ℝ≥0∞)
    (h : ∀ a ρ, ρ.PosSemidef → rA a ρ ≤ rA' a ρ) (p : QProg R E O α) {ρ : Matrix R R ℂ}
    (hρ : ρ.PosSemidef) : wpAwait e s rA rE p ρ ≤ wpAwait e s rA' rE p ρ := by
  induction p generalizing ρ with
  | ret a => exact h a ρ hρ
  | opN q k ih =>
    exact ENNReal.tsum_le_tsum fun n => ih n (DSubInstrument.posSemidef_branch_apply _ _ hρ)
  | _ => exact le_rfl

/-- One unfolding of the unbounded loop activation of `body`: an activation of the residual
program that continues, at a return of `s` before the receive, with the activation `h` of
`body s`. -/
def loopFun (body : σ → QProg R E O σ) :
    (QProg R E O σ → E → SubInstrument R R (QProg R E O σ × O)) →o
      (QProg R E O σ → E → SubInstrument R R (QProg R E O σ × O)) where
  toFun h t e := stepWith (fun s e => h (body s) e) t e
  monotone' _ _ hh t e := awaitK_mono e _ _ (fun s => hh (body s) e) t

/-- The unbounded loop activation of `body`: the supremum of the iterates of `loopFun body`
from the failing activation. -/
def loopActω (body : σ → QProg R E O σ) :
    QProg R E O σ → E → SubInstrument R R (QProg R E O σ × O) :=
  ωSup (fixedPoints.iterateChain (loopFun body) (fun _ _ => SubInstrument.fail)
    fun _ _ => fail_le _)

/-- The step of the loop system is below the unbounded loop activation. -/
theorem loopQSys_step_le_loopActω (body : σ → QProg R E O σ) (s₀ : σ) :
    (loopQSys body s₀).step ≤ loopActω body :=
  le_ωSup (fixedPoints.iterateChain (loopFun body) (fun _ _ => SubInstrument.fail)
    fun _ _ => fail_le _) 2

/-! ## Partial correctness and the loop rule -/

section Loop

variable [DecidableEq R]

/-- Partial correctness of the subinstrument `c` from the precondition `P` to the postcondition
`Q`: on every state, the expected violation `1 - Q` of the postcondition is at most the
violation `1 - P` of the precondition. Failure and divergence count as success. -/
def PCorrect (P : Matrix R R ℂ) (c : SubInstrument R R X) (Q : X → Matrix R R ℂ) : Prop :=
  ∀ ρ : Matrix R R ℂ, ρ.PosSemidef →
    expect c (fun x => 1 - Q x) ρ ≤ ENNReal.ofReal (((1 - P) * ρ).trace.re)

/-- One unfolding preserves partial correctness from the invariant `J`, when the weakest
precondition of an activation that restarts with the invariant of `body s` is bounded by the
invariant. -/
theorem loopFun_pcorrect (body : σ → QProg R E O σ) (J : QProg R E O σ → Matrix R R ℂ)
    (Q : QProg R E O σ × O → Matrix R R ℂ) (hQ : ∀ x, (1 - Q x).PosSemidef)
    (hbody : ∀ t e ρ, ρ.PosSemidef →
      wpStep (fun s _ ρ' => ENNReal.ofReal (((1 - J (body s)) * ρ').trace.re)) t e
          (fun x => 1 - Q x) ρ ≤ ENNReal.ofReal (((1 - J t) * ρ).trace.re))
    (h : QProg R E O σ → E → SubInstrument R R (QProg R E O σ × O))
    (hh : ∀ t e, PCorrect (J t) (h t e) Q) (t : QProg R E O σ) (e : E) :
    PCorrect (J t) (loopFun body h t e) Q := by
  intro ρ hρ
  change expect (stepWith (fun s e => h (body s) e) t e) _ ρ ≤ _
  rw [← wpStep_eq_expect _ hQ t e hρ]
  exact (wpAwait_mono e _ _ (fun s ρ' hρ' => hh (body s) e ρ' hρ') t hρ).trans (hbody t e ρ hρ)

/-- **Loop rule** of partial correctness: when the weakest precondition of an activation of
each residual program `t`, restarting at a return of `s` with the invariant of `body s`, is
bounded by the invariant `J t`, every unbounded loop activation is partially correct from the
invariant. -/
theorem loopActω_pcorrect (body : σ → QProg R E O σ) (J : QProg R E O σ → Matrix R R ℂ)
    (Q : QProg R E O σ × O → Matrix R R ℂ) (hQ : ∀ x, (1 - Q x).PosSemidef)
    (hbody : ∀ t e ρ, ρ.PosSemidef →
      wpStep (fun s _ ρ' => ENNReal.ofReal (((1 - J (body s)) * ρ').trace.re)) t e
          (fun x => 1 - Q x) ρ ≤ ENNReal.ofReal (((1 - J t) * ρ).trace.re))
    (t : QProg R E O σ) (e : E) :
    PCorrect (J t) (loopActω body t e) Q := by
  revert t e
  unfold loopActω
  scott_induction
  case hP =>
    intro c hc t e ρ hρ
    exact expect_ωSup_le ((c.map (Pi.evalOrderHom t)).map (Pi.evalOrderHom e)) _ ρ
      fun n => hc n t e ρ hρ
  case h0 =>
    intro t e ρ _
    rw [expect_fail]
    exact bot_le
  case hstep =>
    exact fun h hh => loopFun_pcorrect body J Q hQ hbody h hh

/-- **Loop rule** for the loop system: under the hypotheses of `loopActω_pcorrect`, every step
of `loopQSys body s₀` is partially correct from the invariant. -/
theorem loopQSys_pcorrect (body : σ → QProg R E O σ) (s₀ : σ)
    (J : QProg R E O σ → Matrix R R ℂ)
    (Q : QProg R E O σ × O → Matrix R R ℂ) (hQ : ∀ x, (1 - Q x).PosSemidef)
    (hbody : ∀ t e ρ, ρ.PosSemidef →
      wpStep (fun s _ ρ' => ENNReal.ofReal (((1 - J (body s)) * ρ').trace.re)) t e
          (fun x => 1 - Q x) ρ ≤ ENNReal.ofReal (((1 - J t) * ρ).trace.re))
    (t : QProg R E O σ) (e : E) :
    PCorrect (J t) ((loopQSys body s₀).step t e) Q := by
  have h0 : ∀ (t : QProg R E O σ) (_ : E), PCorrect (J t)
      (SubInstrument.fail : SubInstrument R R (QProg R E O σ × O)) Q := by
    intro t _ ρ _
    rw [expect_fail]
    exact bot_le
  exact loopFun_pcorrect body J Q hQ hbody _
    (loopFun_pcorrect body J Q hQ hbody (fun _ _ => SubInstrument.fail) h0) t e

end Loop

/-! ## Example: the phase `done` of the reactive quantum one-time pad -/

open CatCrypt.Quantum.QOTPReactive

/-- In the loop of `qotpRealBody n`, an activation at the phase `done` outputs `ignored` with
certainty, up to failure: the expected indicator of any other output is zero. The proof applies
the loop rule with the invariant `1` on the residual programs `ret done` and
`qotpRealBody n done` and `0` elsewhere. -/
theorem qotpReal_done_ignored {n : ℕ} (s₀ : Phase n) (e : Event)
    {ρ : Matrix (Reg n × Reg n) (Reg n × Reg n) ℂ} (hρ : ρ.PosSemidef) :
    expect ((loopQSys (qotpRealBody n) s₀).step (.ret .done) e)
      (fun x => if x.2 = .ignored then 0 else 1) ρ = 0 := by
  classical
  have hd : qotpRealBody n .done = .recv fun _ => .send .ignored (.ret .done) := rfl
  let J : QProg (Reg n × Reg n) Event Out (Phase n) → Matrix (Reg n × Reg n) (Reg n × Reg n) ℂ :=
    fun t => if t = .ret .done ∨ t = qotpRealBody n .done then 1 else 0
  let Q : QProg (Reg n × Reg n) Event Out (Phase n) × Out →
      Matrix (Reg n × Reg n) (Reg n × Reg n) ℂ :=
    fun x => if x.2 = .ignored then 1 else 0
  have hQ : ∀ x, (1 - Q x).PosSemidef := by
    intro x
    by_cases h : x.2 = .ignored <;> simp [Q, h, Matrix.PosSemidef.one, Matrix.PosSemidef.zero]
  have hV : (fun x : QProg (Reg n × Reg n) Event Out (Phase n) × Out =>
      (if x.2 = .ignored then 0 else 1 : Matrix (Reg n × Reg n) (Reg n × Reg n) ℂ)) =
      fun x => 1 - Q x := by
    funext x
    by_cases h : x.2 = .ignored <;> simp [Q, h]
  have hbody : ∀ t e ρ, ρ.PosSemidef →
      wpStep (fun s _ ρ' => ENNReal.ofReal (((1 - J (qotpRealBody n s)) * ρ').trace.re)) t e
          (fun x => 1 - Q x) ρ ≤ ENNReal.ofReal (((1 - J t) * ρ).trace.re) := by
    intro t e ρ hρ
    by_cases h1 : t = .ret .done
    · subst h1
      simp [wpStep, wpAwait, J]
    by_cases h2 : t = qotpRealBody n .done
    · subst h2
      rw [hd]
      simp [wpStep, wpAwait, wpEmit, post, Q]
    · have hJ : J t = 0 := by simp [J, h1, h2]
      rw [hJ, sub_zero, one_mul]
      refine wpAwait_le_trace (fun o q ρ' _ => ?_) (fun s ρ' _ => ?_) (fun _ _ _ => bot_le) t hρ
      · by_cases h : o = .ignored <;> simp [post, Q, h]
      · by_cases h : qotpRealBody n s = .ret .done ∨ qotpRealBody n s = qotpRealBody n .done <;>
          simp [J, h]
  have h := loopQSys_pcorrect (qotpRealBody n) s₀ J Q hQ hbody (.ret .done) e ρ hρ
  rw [hV]
  simpa [J] using h

end QProg

end CatCrypt.Crypto.Party
