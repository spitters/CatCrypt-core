/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Party.StoreHybrid
public import CatCryptCore.Tactics.BindSwap
public import CatCryptCore.Tactics.DeriveReduction
import CatCryptCore.Tactics.AutoDispatchExt

/-!
# The hybrid over activations with a secret carried state

A secret-state system carries, besides a public state `P`, a secret key `K` that the
environment never sees. An activation on command `c` takes the carried key, or a fresh key
drawn from the distribution `ι` when none is carried yet, runs the keyed step `gen c k`, which
returns a result `a` and the next key, updates the public state and outputs by `upd c p a`,
and carries the next key. This is the shape of a symmetric ratchet: the chain key is carried
from one activation to the next, and each activation stretches it.

The fresh system runs at command `c` the ideal result `ideal c` and carries no key. The two
are related by the one-step games of the commands: the real step game `stepReal ι gen c` draws
a fresh key from `ι` and runs `gen c` on it, and the ideal step game `stepIdeal ι ideal c`
runs `ideal c` and draws the next key afresh from `ι`. For a pseudorandom generator stretched
from a uniform seed these are the stretch games: the real side outputs the next state, the
ideal side a uniform one.

The hybrid number `k` runs the first `k` activations fresh and the remaining ones with the
carried key, from the key drawn afresh at activation `k`. Hybrids `k` and `k + 1` differ at
activation `k` by the step game of its command: in hybrid `k` it is the real step game, in
hybrid `k + 1` the ideal one followed by the carried key of the ideal step game; a fresh draw
from `ι` at activation `k` carried to activation `k + 1` is a fresh draw at activation `k + 1`
when `ι` is heap-independent and of mass one (`secretLoop_lazy`). The distinguisher of the
step game is the explicit reduction `secretStepReduction`: it writes the result of the step
game into the public state and the output, carries its key, and runs the remainder of the run
(`secretRest`). The bound of an activation is the supremum over the values reached before it
(environment state, command, public state, flag) and over the heap of the one-step bound of
the command at that reduction (`secretTerm`).

## Main definitions

* `secretKeyOf`: the carried key, or a fresh draw.
* `secretSys`, `freshSys`: the system with the carried key and the fresh system.
* `stepReal`, `stepIdeal`: the one-step games of a command.
* `secretHyb`, `secretPrefix`: the hybrids and their common prefix.
* `secretRest`, `secretStepReduction`: the remainder of a run and the reduction of one
  activation.
* `secretTerm`, `secretBound`: the bound of one activation and its sum over the rounds.

## Main results

* `secretLoop_lazy`: a fresh key carried into the remainder of a run is drawn at its first
  use.
* `secretHyb_step_le`, `secretHyb_le`: consecutive hybrids differ by the bound of one
  activation; hybrids `0` and `m` by the sum of the first `m`.
* `realizes_secretSys`: per-command concrete distances between the step games give a
  realization of the fresh system by the secret-state system.
* `secretStepReduction.tree.timeBound_timed`: the time of the reduction of one activation.

Search words: hybrid over activations, secret state, carried key, chain key, symmetric
ratchet, PRG stretch, lazy sampling, reactive hybrid.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Party

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCTransparent
open scoped ENNReal

variable {C P K A O ζ : Type}

/-- The key of an activation: the carried key, or a fresh draw from `ι` when none is
carried. -/
noncomputable def secretKeyOf (ι : SPComp K) : Option K → SPComp K
  | none => ι
  | some k => SPComp.pure k

/-- **The secret-state system**: on command `c` from public state `p` it takes the key of the
activation, runs `gen c` on it, outputs and updates the public state by `upd c p` on the
result, and carries the next key. -/
noncomputable def secretSys (p₀ : P) (ι : SPComp K) (gen : C → K → SPComp (A × K))
    (upd : C → P → A → P × O) : Sys (P × Option K) C O where
  init := (p₀, none)
  step st c := SPComp.bind (secretKeyOf ι st.2) fun k => SPComp.bind (gen c k) fun r =>
    SPComp.pure (((upd c st.1 r.1).1, some r.2), (upd c st.1 r.1).2)

/-- **The fresh system**: on command `c` from public state `p` it runs `ideal c` and outputs
and updates the public state by `upd c p` on the result. -/
noncomputable def freshSys (p₀ : P) (ideal : C → SPComp A) (upd : C → P → A → P × O) :
    Sys P C O where
  init := p₀
  step p c := SPComp.bind (ideal c) fun a => SPComp.pure (upd c p a)

/-- The real step game of command `c`: a fresh key from `ι`, then `gen c`. -/
noncomputable def stepReal (ι : SPComp K) (gen : C → K → SPComp (A × K)) (c : C) :
    Unit → SPComp (A × K) :=
  fun _ => SPComp.bind ι (gen c)

/-- The ideal step game of command `c`: `ideal c`, and a fresh next key from `ι`. -/
noncomputable def stepIdeal (ι : SPComp K) (ideal : C → SPComp A) (c : C) :
    Unit → SPComp (A × K) :=
  fun _ => SPComp.bind (ideal c) fun a => SPComp.bind ι fun k => SPComp.pure (a, k)

/-- The hybrid of a run of `n` rounds of `Z`: the first `k` activations run the fresh system,
the remaining `n - k` the secret-state system from no carried key. -/
noncomputable def secretHyb (p₀ : P) (ι : SPComp K) (gen : C → K → SPComp (A × K))
    (ideal : C → SPComp A) (upd : C → P → A → P × O) (Z : Strat ζ C O) (n k : ℕ) :
    SPComp (ζ × (P × Option K) × Bool) :=
  SPComp.bind (loop (freshSys p₀ ideal upd) (fun _ => false) Z k (Z.init, p₀, false))
    fun c => loop (secretSys p₀ ι gen upd) (fun _ => false) Z (n - k) (c.1, (c.2.1, none), c.2.2)

/-- The common prefix of hybrids `k` and `k + 1`: `k` fresh activations, then the
environment's choice of the next command, with the public state and flag reached. -/
noncomputable def secretPrefix (p₀ : P) (ideal : C → SPComp A) (upd : C → P → A → P × O)
    (Z : Strat ζ C O) (k : ℕ) : SPComp (ζ × C × P × Bool) :=
  SPComp.bind (loop (freshSys p₀ ideal upd) (fun _ => false) Z k (Z.init, p₀, false)) fun c =>
    SPComp.bind (Z.next c.1) fun a => SPComp.pure (a.1, a.2, c.2.1, c.2.2)

/-- The remainder of a run after an activation with public state `t.1`, output `t.2.1` and
carried key `t.2.2`: the environment in state `z` observes the output, `j` activations of the
secret-state system run, and `D` is applied to the final environment state. -/
noncomputable def secretRest (p₀ : P) (ι : SPComp K) (gen : C → K → SPComp (A × K))
    (upd : C → P → A → P × O) (Z : Strat ζ C O) (D : ζ → SPComp Bool) (j : ℕ) (z : ζ)
    (fl : Bool) (t : P × O × K) : SPComp Bool :=
  SPComp.bind (Z.obs z t.2.1) fun z' =>
    SPComp.bind (loop (secretSys p₀ ι gen upd) (fun _ => false) Z j (z', (t.1, some t.2.2), fl))
      fun q => D q.1

/-- **The reduction of one activation** on command `c` from public state `p`: from the result
`r.1` and key `r.2` of the step game it computes the public state and the output by `upd`
and runs the distinguisher `B` of the remainder on them with the key. -/
noncomputable def secretStepReduction (upd : C → P → A → P × O) (c : C) (p : P)
    (B : P × O × K → SPComp Bool) : A × K → SPComp Bool :=
  fun r => B ((upd c p r.1).1, (upd c p r.1).2, r.2)

derive_reduction secretStepReduction

/-- The bound of one activation followed by `j` activations of the secret-state system: the
supremum, over the environment state, command, public state and flag reached before it and
over the heap, of the one-step bound of the command at the reduction `secretStepReduction`
of the remainder. -/
noncomputable def secretTerm (p₀ : P) (ι : SPComp K) (gen : C → K → SPComp (A × K))
    (upd : C → P → A → P × O) (b : C → Env Unit (A × K) → ℝ≥0∞) (Z : Strat ζ C O)
    (D : ζ → SPComp Bool) (j : ℕ) : ℝ≥0∞ :=
  ⨆ (y : ζ × C × P × Bool) (h : Heap),
    b y.2.1 ⟨(), h, secretStepReduction upd y.2.1 y.2.2.1
      (secretRest p₀ ι gen upd Z D j y.1 y.2.2.2)⟩

/-- The realization bound: the sum over the rounds `k` of the bound of activation `k`
followed by the remaining `rounds - (k + 1)` activations. -/
noncomputable def secretBound (p₀ : P) (ι : SPComp K) (gen : C → K → SPComp (A × K))
    (upd : C → P → A → P × O) (b : C → Env Unit (A × K) → ℝ≥0∞) (ζ : Type)
    (Z : Env (Strat ζ C O) ζ) : ℝ≥0∞ :=
  ∑ k ∈ Finset.range Z.input.rounds,
    secretTerm p₀ ι gen upd b Z.input Z.dist (Z.input.rounds - (k + 1))

section Hybrid

variable (p₀ : P) {ι : SPComp K} (gen : C → K → SPComp (A × K)) (ideal : C → SPComp A)
  (upd : C → P → A → P × O)

/-- **Lazy drawing of the carried key**: a key drawn from `ι` and carried into `j` further
activations of the secret-state system is, for the final environment state, a key drawn at
its first use. -/
theorem secretLoop_lazy (hι : SPComp.IsPure ι) (hl : ∀ h, SDistr.mass (ι h) = 1)
    (Z : Strat ζ C O) (D : ζ → SPComp Bool) (j : ℕ) (z : ζ) (p : P) (fl : Bool) :
    SPComp.bind ι (fun k =>
        SPComp.bind (loop (secretSys p₀ ι gen upd) (fun _ => false) Z j (z, (p, some k), fl))
          fun q => D q.1) =
      SPComp.bind (loop (secretSys p₀ ι gen upd) (fun _ => false) Z j (z, (p, none), fl))
        fun q => D q.1 := by
  cases j with
  | zero =>
    simp only [loop, SPComp.pure_bind]
    exact SPComp.isPure_bind_discard ι _ hι hl
  | succ j =>
    simp only [loop, SPComp.bind_assoc]
    rw [SPComp.isPure_bind_comm_left ι (Z.next z) _ hι]
    congr 1
    funext a
    simp only [secretSys, secretKeyOf, SPComp.pure_bind, SPComp.bind_assoc]

/-- The hybrid `k` with `j + 1` activations after the first `k`, followed by `D`: the
prefix, the real step game, and the reduction of the remainder. -/
theorem secretHyb_split_left (Z : Strat ζ C O) (D : ζ → SPComp Bool) (n k : ℕ) (hk : k < n) :
    SPComp.bind (SPComp.map Prod.fst (secretHyb p₀ ι gen ideal upd Z n k)) D =
      SPComp.bind (secretPrefix p₀ ideal upd Z k) fun y =>
        SPComp.bind (stepReal ι gen y.2.1 ())
          (secretStepReduction upd y.2.1 y.2.2.1
            (secretRest p₀ ι gen upd Z D (n - (k + 1)) y.1 y.2.2.2)) := by
  have hn : n - k = (n - (k + 1)) + 1 := by omega
  simp only [secretHyb, hn, loop, secretPrefix, stepReal, SPComp.map, SPComp.bind_assoc,
    SPComp.pure_bind, Bool.or_false]
  congr 1; funext c; congr 1; funext a
  simp only [secretSys, secretKeyOf, SPComp.bind_assoc, SPComp.pure_bind]
  rfl

/-- The hybrid `k + 1` followed by `D`: the prefix, the ideal step game, and the reduction of
the remainder. -/
theorem secretHyb_split_right (hι : SPComp.IsPure ι) (hl : ∀ h, SDistr.mass (ι h) = 1)
    (Z : Strat ζ C O) (D : ζ → SPComp Bool) (n k : ℕ) :
    SPComp.bind (SPComp.map Prod.fst (secretHyb p₀ ι gen ideal upd Z n (k + 1))) D =
      SPComp.bind (secretPrefix p₀ ideal upd Z k) fun y =>
        SPComp.bind (stepIdeal ι ideal y.2.1 ())
          (secretStepReduction upd y.2.1 y.2.2.1
            (secretRest p₀ ι gen upd Z D (n - (k + 1)) y.1 y.2.2.2)) := by
  simp only [secretHyb]
  rw [MultiHybrid.loop_add _ _ _ k 1]
  simp only [loop, secretPrefix, freshSys, stepIdeal, secretStepReduction, secretRest,
    SPComp.map, SPComp.bind_assoc, SPComp.pure_bind, Bool.or_false]
  congr 1; funext c; congr 1; funext a; congr 1; funext r
  rw [SPComp.isPure_bind_comm_left ι (Z.obs a.1 (upd a.2 c.2.1 r).2) _ hι]
  congr 1; funext z
  exact (secretLoop_lazy p₀ gen upd hι hl Z D _ z _ _).symm

/-- Consecutive hybrids differ by at most the bound of the activation where they differ. -/
theorem secretHyb_step_le (hι : SPComp.IsPure ι) (hl : ∀ h, SDistr.mass (ι h) = 1)
    {b : C → Env Unit (A × K) → ℝ≥0∞}
    (h : ∀ c, DistC (stepReal ι gen c) (stepIdeal ι ideal c) (b c))
    (Z : Strat ζ C O) (D : ζ → SPComp Bool) (h₀ : Heap) (n k : ℕ) (hk : k < n) :
    absDiff
      (prTrue (SPComp.bind (SPComp.map Prod.fst (secretHyb p₀ ι gen ideal upd Z n k)) D) h₀)
      (prTrue (SPComp.bind (SPComp.map Prod.fst
        (secretHyb p₀ ι gen ideal upd Z n (k + 1))) D) h₀) ≤
      secretTerm p₀ ι gen upd b Z D (n - (k + 1)) := by
  rw [secretHyb_split_left p₀ gen ideal upd Z D n k hk,
    secretHyb_split_right p₀ gen ideal upd hι hl Z D n k]
  have hg : DistC
      (fun y : ζ × C × P × Bool => SPComp.bind (stepReal ι gen y.2.1 ())
        (secretStepReduction upd y.2.1 y.2.2.1
          (secretRest p₀ ι gen upd Z D (n - (k + 1)) y.1 y.2.2.2)))
      (fun y => SPComp.bind (stepIdeal ι ideal y.2.1 ())
        (secretStepReduction upd y.2.1 y.2.2.1
          (secretRest p₀ ι gen upd Z D (n - (k + 1)) y.1 y.2.2.2)))
      (fun W => b W.input.2.1 ⟨(), W.heap, fun r => SPComp.bind
        (secretStepReduction upd W.input.2.1 W.input.2.2.1
          (secretRest p₀ ι gen upd Z D (n - (k + 1)) W.input.1 W.input.2.2.2) r) W.dist⟩) :=
    fun W => by
      simpa only [Env.gap, SPComp.bind_assoc] using
        h W.input.2.1 ⟨(), W.heap, fun r => SPComp.bind
          (secretStepReduction upd W.input.2.1 W.input.2.2.1
            (secretRest p₀ ι gen upd Z D (n - (k + 1)) W.input.1 W.input.2.2.2) r) W.dist⟩
  have hc := DistC.comp_left (fun _ : Unit => secretPrefix p₀ ideal upd Z k) hg
    ⟨(), h₀, SPComp.pure⟩
  simp only [Env.gap, SPComp.bind_pure] at hc
  exact hc

/-- The hybrid argument: hybrids `0` and `m` differ by at most the sum of the bounds of the
first `m` activations. -/
theorem secretHyb_le (hι : SPComp.IsPure ι) (hl : ∀ h, SDistr.mass (ι h) = 1)
    {b : C → Env Unit (A × K) → ℝ≥0∞}
    (h : ∀ c, DistC (stepReal ι gen c) (stepIdeal ι ideal c) (b c))
    (Z : Strat ζ C O) (D : ζ → SPComp Bool) (h₀ : Heap) (n : ℕ) :
    ∀ m, m ≤ n →
      absDiff (prTrue (SPComp.bind (SPComp.map Prod.fst
          (secretHyb p₀ ι gen ideal upd Z n 0)) D) h₀)
        (prTrue (SPComp.bind (SPComp.map Prod.fst
          (secretHyb p₀ ι gen ideal upd Z n m)) D) h₀) ≤
        ∑ k ∈ Finset.range m, secretTerm p₀ ι gen upd b Z D (n - (k + 1)) := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    rw [Finset.sum_range_succ]
    exact (absDiff_triangle _ _ _).trans
      (add_le_add (ih (by omega))
        (secretHyb_step_le p₀ gen ideal upd hι hl h Z D h₀ n m (by omega)))

/-- The hybrid with no fresh activation is the run of the secret-state system. -/
theorem secretHyb_zero (Z : Strat ζ C O) :
    secretHyb p₀ ι gen ideal upd Z Z.rounds 0 =
      run (secretSys p₀ ι gen upd) (fun _ => false) Z := by
  simp only [secretHyb, run, loop, Nat.sub_zero, SPComp.pure_bind]
  rfl

/-- The hybrid with every activation fresh is the run of the fresh system, with no key. -/
theorem secretHyb_self (Z : Strat ζ C O) :
    SPComp.map Prod.fst (secretHyb p₀ ι gen ideal upd Z Z.rounds Z.rounds) =
      view (freshSys p₀ ideal upd) Z := by
  simp only [secretHyb, view, run, Nat.sub_self, loop, SPComp.map, SPComp.bind_assoc,
    SPComp.pure_bind]
  rfl

/-- **The hybrid over activations with a secret carried state.** Per-command concrete
distances `b c` between the real and ideal step games give a realization of the fresh system
by the secret-state system, with bound the sum over the rounds of the one-step bounds at the
reductions `secretStepReduction` of the activations (`secretBound`). The key distribution `ι`
is heap-independent and of mass one. -/
theorem realizes_secretSys (hι : SPComp.IsPure ι) (hl : ∀ h, SDistr.mass (ι h) = 1)
    {b : C → Env Unit (A × K) → ℝ≥0∞}
    (h : ∀ c, DistC (stepReal ι gen c) (stepIdeal ι ideal c) (b c)) :
    Realizes (secretSys p₀ ι gen upd) (freshSys p₀ ideal upd)
      (secretBound p₀ ι gen upd b) := by
  intro ζ Z
  obtain ⟨Zs, h₀, D⟩ := Z
  have hle := secretHyb_le p₀ gen ideal upd hι hl h Zs D h₀ Zs.rounds Zs.rounds le_rfl
  rw [secretHyb_zero, secretHyb_self] at hle
  simpa only [Env.gap, view, secretBound] using hle

end Hybrid

/-- **Time of the reduction of one activation**: two evaluations of the update (cost at most
`u` each), three units of bookkeeping, and one call of the distinguisher of the remainder
(time at most `T`, cost companion at most `d`). -/
theorem secretStepReduction.tree.timeBound_timed (upd : C → P → A → P × O)
    (updCost : C → P → A → ℕ) (c : C) (p : P) (B : P × O × K → SPTree.Timed Bool)
    (BCost : P × O × K → ℕ) (r : A × K) {T d u : ℕ} (hB : ∀ t, (B t).time ≤ T)
    (hBc : ∀ t, BCost t ≤ d) (hu : ∀ a, updCost c p a ≤ u) :
    SPTree.Timed.stepTime (secretStepReduction.tree.timed upd updCost c p B BCost r) ≤
      T + d + 2 * u + 3 := by
  have h1 := hB ((upd c p r.1).1, (upd c p r.1).2, r.2)
  have h2 := hBc ((upd c p r.1).1, (upd c p r.1).2, r.2)
  have h3 := hu r.1
  simp only [secretStepReduction.tree.timed, SPTree.Timed.stepTime]
  omega

end CatCrypt.Crypto.Party
