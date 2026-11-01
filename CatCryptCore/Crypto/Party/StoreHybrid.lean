/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCTransparentMulti
public import CatCryptCore.Crypto.UCOneShot
public import CatCryptCore.Crypto.UCConcrete
public import CatCryptCore.Crypto.Party.Call

/-!
# The store system and the hybrid over activations

A store system holds a store `X → V` of per-handle values. An activation is a command `c`;
it reads the protocol input `S.read c st` from the store `st`, runs the one-shot protocol
`π c` on it, writes the result back (`S.write`) and outputs `S.out c r` to the environment.
A reactive functionality whose every activation runs a one-shot protocol on a store is of this
form; the store system turns one-shot games into a reactive statement.

The lifting theorem replaces the per-command protocols `π₁ c` by `π₂ c` one activation at a
time (a hybrid over activations). The hybrid number `k` runs the first `k` activations with
`π₂` and the remaining ones with `π₁`; consecutive hybrids differ in one activation, whose gap
is bounded by the one-shot bound of the command run there. The one-shot environment of that
activation has the protocol input read from the store, and its distinguisher observes the
output, runs the remaining activations with `π₁` and applies the outer distinguisher. Its
environment state, command, store and initial heap are those reached after the first `k`
activations; the bound takes the supremum over these values (`storeTerm`). The ideal
per-command protocols carry the simulators: for `π₂ c = idealOf (F c) (s c)` the ideal store
system runs the simulator `s c` of the command at each activation.

The no-failure guard `MultiHybrid.guardNF` of a computation that never fails is the
computation; the lemmas `guardNF_pure`, `guardNF_bind_pure`, `guardNF_sample_pure` and
`guardNF_sample2_pure` state this for the activations of party programs over a store.

## Main definitions

* `StoreIface` — initial store, read, write-back and output maps of a store system.
* `storeSys S π` — the store system running the one-shot protocol `π c` on command `c`.
* `storeHyb` — the hybrid with `k` activations of `π₂` followed by activations of `π₁`.
* `storeCont` — the remainder of a run after one activation, as a distinguisher.
* `storeTerm`, `storeBound` — the bound of one activation and its sum over the rounds.
* `probeStrat`, `probeEnv` — the one-round strategy on a one-shot system that reads off a
  one-shot environment.

## Main results

* `distC_of_realizes_oneShot` — a realization between one-shot systems gives a concrete
  distance between the one-shot protocols, with bound at `probeEnv`.
* `realizes_storeSys_of_distC` — per-command concrete distances `b c` give a realization of
  `storeSys S π₂` by `storeSys S π₁` with bound `storeBound S b π₁`.
* `realizes_storeSys` — the same from per-command realizations between one-shot systems.
* `realizes_storeSys_of_ucEmulatesCSim` — per-command `UCEmulatesCSim` statements with
  straight-line simulators `simOf (s c)` give a realization of the store system whose
  command `c` runs `idealOf (F c) (s c)`.
* `storeHyb_step_le`, `storeHyb_le` — consecutive hybrids differ by the bound of one
  activation; hybrids `0` and `m` by the sum of the first `m`.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent.MultiHybrid

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto

/-- `guardNF` of a point mass is the point mass. -/
theorem guardNF_pure {β : Type} (x d : β) : guardNF (SPComp.pure x) d = SPComp.pure x :=
  guardNF_of_noFail d (SPComp.pure_noFail x)

/-- `guardNF` of a computation that never fails followed by a point mass is the computation. -/
theorem guardNF_bind_pure {α β : Type} {c : SPComp α} (hc : SPComp.NoFail c) (f : α → β)
    (d : β) :
    guardNF (SPComp.bind c fun a => SPComp.pure (f a)) d =
      SPComp.bind c fun a => SPComp.pure (f a) :=
  guardNF_of_noFail d (Assumptions.SPComp.bind_noFail hc fun a => SPComp.pure_noFail (f a))

/-- `guardNF` of a uniform sample followed by a point mass is the computation. -/
theorem guardNF_sample_pure {α β : Type} [Fintype α] [Nonempty α] (f : α → β) (d : β) :
    guardNF (SPComp.bind (SPComp.sample α) fun a => SPComp.pure (f a)) d =
      SPComp.bind (SPComp.sample α) fun a => SPComp.pure (f a) :=
  guardNF_bind_pure Assumptions.SPComp.sample_noFail f d

/-- `guardNF` of two uniform samples followed by a point mass is the computation. -/
theorem guardNF_sample2_pure {α β : Type} [Fintype α] [Nonempty α] (f : α → α → β) (d : β) :
    guardNF (SPComp.bind (SPComp.sample α) fun a =>
        SPComp.bind (SPComp.sample α) fun a' => SPComp.pure (f a a')) d =
      SPComp.bind (SPComp.sample α) fun a =>
        SPComp.bind (SPComp.sample α) fun a' => SPComp.pure (f a a') :=
  guardNF_of_noFail d
    (Assumptions.SPComp.bind_noFail Assumptions.SPComp.sample_noFail fun _ =>
      Assumptions.SPComp.bind_noFail Assumptions.SPComp.sample_noFail fun _ =>
        SPComp.pure_noFail _)

end CatCrypt.Crypto.UCTransparent.MultiHybrid

namespace CatCrypt.Core.SPComp

open CatCrypt.Prob

/-- Sampling a uniform element and discarding it is the continuation. -/
theorem sample_bind_const {α β : Type} [Fintype α] [Nonempty α] (k : SPComp β) :
    SPComp.bind (SPComp.sample α) (fun _ => k) = k := by
  funext h
  simp only [SPComp.bind, SPComp.sample, SDistr.bind_assoc, SDistr.pure_bind]
  exact SDistr.uniform_bind_const _

end CatCrypt.Core.SPComp

namespace CatCrypt.Crypto.Party

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open CatCrypt.Crypto.UCConcrete CatCrypt.Crypto.UCTransparent
open scoped ENNReal

/-! ## Recovering a one-shot distance from a one-shot realization -/

section Probe

variable {hon α : Type}

/-- The one-round strategy on a one-shot system that activates it with input `x` and keeps
    the output. -/
noncomputable def probeStrat (x : hon) : Strat (Option (Option α)) hon (Option α) where
  rounds := 1
  init := none
  next z := SPComp.pure (z, x)
  obs _ o := SPComp.pure (some o)
  next_noFail _ := SPComp.pure_noFail _
  obs_noFail _ _ := SPComp.pure_noFail _

/-- The distinguisher of `probeStrat`: `D` on a kept result, `false` otherwise. -/
noncomputable def probeDist (D : α → SPComp Bool) : Option (Option α) → SPComp Bool
  | some (some r) => D r
  | _ => SPComp.pure false

/-- The environment of a one-shot system that reads off the one-shot environment `W`. -/
noncomputable def probeEnv (W : Env hon α) : Env (Strat (Option (Option α)) hon (Option α))
    (Option (Option α)) :=
  ⟨probeStrat W.input, W.heap, probeDist W.dist⟩

/-- The view of a one-shot system against `probeStrat x` is the result of `π x`. -/
theorem view_oneShot_probe (π : hon → SPComp α) (x : hon) :
    view (Sys.oneShot π) (probeStrat x) =
      SPComp.bind (π x) fun r => SPComp.pure (some (some r)) := by
  rw [view_oneShot_succ π (probeStrat x) 0 rfl]
  simp only [probeStrat, Strat.idle, SPComp.pure_bind, SPComp.bind_pure]

/-- A realization between one-shot systems with bound `B` gives a concrete distance
    between the one-shot protocols, with bound `B` at the probing environment. -/
theorem distC_of_realizes_oneShot {π₁ π₂ : hon → SPComp α}
    {B : (ζ : Type) → Env (Strat ζ hon (Option α)) ζ → ℝ≥0∞}
    (h : Realizes (Sys.oneShot π₁) (Sys.oneShot π₂) B) :
    DistC π₁ π₂ fun W => B (Option (Option α)) (probeEnv W) := by
  intro W
  have hW := h _ (probeEnv W)
  simp only [Env.gap, probeEnv, view_oneShot_probe, SPComp.bind_assoc, SPComp.pure_bind,
    probeDist] at hW
  exact hW

end Probe

/-! ## The store system -/

/-- The interface of a store system with commands `C`, handles `X`, values `V`, protocol
    inputs `H`, protocol results `A` and outputs `O`. -/
structure StoreIface (C X V H A O : Type) where
  /-- The initial store. -/
  init : X → V
  /-- The protocol input of a command, read from the store. -/
  read : C → (X → V) → H
  /-- The store after a command with protocol result `r`. -/
  write : C → A → (X → V) → X → V
  /-- The output of a command with protocol result `r`. -/
  out : C → A → O

variable {C X V H A O ζ : Type}

/-- The store system of the per-command one-shot protocols `π`: on command `c` it runs
    `π c` on the values `c` reads, writes the result back and outputs it. -/
noncomputable def storeSys (S : StoreIface C X V H A O) (π : C → H → SPComp A) :
    Sys (X → V) C O where
  init := S.init
  step st c := SPComp.bind (π c (S.read c st)) fun r => SPComp.pure (S.write c r st, S.out c r)

/-- An activation of `storeSys S π` runs `π` on the input read from the store (unfolding
    lemma). -/
@[simp] theorem storeSys_step (S : StoreIface C X V H A O) (π : C → H → SPComp A)
    (st : X → V) (c : C) :
    (storeSys S π).step st c =
      SPComp.bind (π c (S.read c st)) fun r => SPComp.pure (S.write c r st, S.out c r) :=
  rfl

/-- `storeSys S π` starts from the initial store of `S` (unfolding lemma). -/
@[simp] theorem storeSys_init (S : StoreIface C X V H A O) (π : C → H → SPComp A) :
    (storeSys S π).init = S.init :=
  rfl

/-- The hybrid of a run of `n` rounds of `Z`: the first `k` activations run `π₂`, the
    remaining `n - k` run `π₁`. -/
noncomputable def storeHyb (S : StoreIface C X V H A O) (π₁ π₂ : C → H → SPComp A)
    (Z : Strat ζ C O) (n k : ℕ) : SPComp (ζ × (X → V) × Bool) :=
  SPComp.bind (loop (storeSys S π₂) (fun _ => false) Z k (Z.init, S.init, false))
    fun c => loop (storeSys S π₁) (fun _ => false) Z (n - k) c

/-- The remainder of a run after an activation, as a distinguisher of its protocol result
    `r`: from the environment state `y.1` after its choice of command `y.2.1`, the store
    `y.2.2.1` and the flag `y.2.2.2`, the environment observes the output, `j` further
    activations run `π`, and `D` is applied to the final environment state. -/
noncomputable def storeCont (S : StoreIface C X V H A O) (π : C → H → SPComp A)
    (Z : Strat ζ C O) (D : ζ → SPComp Bool) (j : ℕ) (y : ζ × C × (X → V) × Bool) (r : A) :
    SPComp Bool :=
  SPComp.bind (Z.obs y.1 (S.out y.2.1 r)) fun z =>
    SPComp.bind (loop (storeSys S π) (fun _ => false) Z j (z, S.write y.2.1 r y.2.2.1, y.2.2.2))
      fun q => D q.1

/-- The bound of one activation followed by `j` activations of `π₁`: the supremum, over the
    environment state, command, store and flag reached before it and over the heap, of the
    one-shot bound of the command at the one-shot environment of the activation. The
    supremum is over values; the strategy `Z` and distinguisher `D` are fixed. -/
noncomputable def storeTerm (S : StoreIface C X V H A O) (b : C → Env H A → ℝ≥0∞)
    (π₁ : C → H → SPComp A) (Z : Strat ζ C O) (D : ζ → SPComp Bool) (j : ℕ) : ℝ≥0∞ :=
  ⨆ (y : ζ × C × (X → V) × Bool) (h : Heap),
    b y.2.1 ⟨S.read y.2.1 y.2.2.1, h, storeCont S π₁ Z D j y⟩

/-- The realization bound of the store system: the sum over the rounds `k` of the bound of
    activation `k` followed by the remaining `rounds - (k + 1)` activations. -/
noncomputable def storeBound (S : StoreIface C X V H A O) (b : C → Env H A → ℝ≥0∞)
    (π₁ : C → H → SPComp A) (ζ : Type) (Z : Env (Strat ζ C O) ζ) : ℝ≥0∞ :=
  ∑ k ∈ Finset.range Z.input.rounds,
    storeTerm S b π₁ Z.input Z.dist (Z.input.rounds - (k + 1))

/-- The hybrid with no activation of `π₂` is the run of `storeSys S π₁`. -/
theorem storeHyb_zero (S : StoreIface C X V H A O) (π₁ π₂ : C → H → SPComp A)
    (Z : Strat ζ C O) :
    storeHyb S π₁ π₂ Z Z.rounds 0 = run (storeSys S π₁) (fun _ => false) Z := by
  simp only [storeHyb, run, loop, Nat.sub_zero, SPComp.pure_bind, storeSys_init]

/-- The hybrid with every activation of `π₂` is the run of `storeSys S π₂`. -/
theorem storeHyb_self (S : StoreIface C X V H A O) (π₁ π₂ : C → H → SPComp A)
    (Z : Strat ζ C O) :
    storeHyb S π₁ π₂ Z Z.rounds Z.rounds = run (storeSys S π₂) (fun _ => false) Z := by
  simp only [storeHyb, run, Nat.sub_self, loop, SPComp.bind_pure, storeSys_init]

/-- The common prefix of hybrids `k` and `k + 1`: `k` activations of `π₂`, then the
    environment's choice of the next command, with the store and flag reached. -/
noncomputable def storePrefix (S : StoreIface C X V H A O) (π₂ : C → H → SPComp A)
    (Z : Strat ζ C O) (k : ℕ) : SPComp (ζ × C × (X → V) × Bool) :=
  SPComp.bind (loop (storeSys S π₂) (fun _ => false) Z k (Z.init, S.init, false)) fun c =>
    SPComp.bind (Z.next c.1) fun a => SPComp.pure (a.1, a.2, c.2.1, c.2.2)

/-- The hybrid `k` with `j + 1` activations after the first `k`, followed by `D`: the
    prefix, one activation of `π₁`, and the remainder. -/
theorem storeHyb_split_left (S : StoreIface C X V H A O) (π₁ π₂ : C → H → SPComp A)
    (Z : Strat ζ C O) (D : ζ → SPComp Bool) (n k : ℕ) (hk : k < n) :
    SPComp.bind (SPComp.map Prod.fst (storeHyb S π₁ π₂ Z n k)) D =
      SPComp.bind (storePrefix S π₂ Z k) fun y =>
        SPComp.bind (π₁ y.2.1 (S.read y.2.1 y.2.2.1)) (storeCont S π₁ Z D (n - (k + 1)) y) := by
  have hn : n - k = (n - (k + 1)) + 1 := by omega
  simp only [storeHyb, hn, loop, storePrefix, storeSys_step, SPComp.map,
    SPComp.bind_assoc, SPComp.pure_bind, Bool.or_false]
  rfl

/-- The hybrid `k + 1` followed by `D`: the prefix, one activation of `π₂`, and the
    remainder with `π₁`. -/
theorem storeHyb_split_right (S : StoreIface C X V H A O) (π₁ π₂ : C → H → SPComp A)
    (Z : Strat ζ C O) (D : ζ → SPComp Bool) (n k : ℕ) :
    SPComp.bind (SPComp.map Prod.fst (storeHyb S π₁ π₂ Z n (k + 1))) D =
      SPComp.bind (storePrefix S π₂ Z k) fun y =>
        SPComp.bind (π₂ y.2.1 (S.read y.2.1 y.2.2.1)) (storeCont S π₁ Z D (n - (k + 1)) y) := by
  simp only [storeHyb]
  rw [MultiHybrid.loop_add _ _ _ k 1]
  simp only [loop, storePrefix, storeSys_step, SPComp.map, SPComp.bind_assoc,
    SPComp.pure_bind, Bool.or_false]
  rfl

/-- Consecutive hybrids differ by at most the bound of the activation where they differ. -/
theorem storeHyb_step_le (S : StoreIface C X V H A O) {π₁ π₂ : C → H → SPComp A}
    {b : C → Env H A → ℝ≥0∞} (h : ∀ c, DistC (π₁ c) (π₂ c) (b c)) (Z : Strat ζ C O)
    (D : ζ → SPComp Bool) (h₀ : Heap) (n k : ℕ) (hk : k < n) :
    absDiff (prTrue (SPComp.bind (SPComp.map Prod.fst (storeHyb S π₁ π₂ Z n k)) D) h₀)
      (prTrue (SPComp.bind (SPComp.map Prod.fst (storeHyb S π₁ π₂ Z n (k + 1))) D) h₀) ≤
      storeTerm S b π₁ Z D (n - (k + 1)) := by
  rw [storeHyb_split_left S π₁ π₂ Z D n k hk, storeHyb_split_right S π₁ π₂ Z D n k]
  have hg : DistC
      (fun y => SPComp.bind (π₁ y.2.1 (S.read y.2.1 y.2.2.1)) (storeCont S π₁ Z D (n - (k + 1)) y))
      (fun y => SPComp.bind (π₂ y.2.1 (S.read y.2.1 y.2.2.1)) (storeCont S π₁ Z D (n - (k + 1)) y))
      (fun W => b W.input.2.1 ⟨S.read W.input.2.1 W.input.2.2.1, W.heap,
        fun r => SPComp.bind (storeCont S π₁ Z D (n - (k + 1)) W.input r) W.dist⟩) := fun W => by
    simpa only [Env.gap, SPComp.bind_assoc] using
      h W.input.2.1 ⟨S.read W.input.2.1 W.input.2.2.1, W.heap,
        fun r => SPComp.bind (storeCont S π₁ Z D (n - (k + 1)) W.input r) W.dist⟩
  have hc := DistC.comp_left (fun _ : Unit => storePrefix S π₂ Z k) hg ⟨(), h₀, SPComp.pure⟩
  simp only [Env.gap, SPComp.bind_pure] at hc
  exact hc

/-- The hybrid argument: hybrids `0` and `m` differ by at most the sum of the bounds of
    the first `m` activations. -/
theorem storeHyb_le (S : StoreIface C X V H A O) {π₁ π₂ : C → H → SPComp A}
    {b : C → Env H A → ℝ≥0∞} (h : ∀ c, DistC (π₁ c) (π₂ c) (b c)) (Z : Strat ζ C O)
    (D : ζ → SPComp Bool) (h₀ : Heap) (n : ℕ) :
    ∀ m, m ≤ n →
      absDiff (prTrue (SPComp.bind (SPComp.map Prod.fst (storeHyb S π₁ π₂ Z n 0)) D) h₀)
        (prTrue (SPComp.bind (SPComp.map Prod.fst (storeHyb S π₁ π₂ Z n m)) D) h₀) ≤
        ∑ k ∈ Finset.range m, storeTerm S b π₁ Z D (n - (k + 1)) := by
  intro m
  induction m with
  | zero => intro _; simp
  | succ m ih =>
    intro hm
    rw [Finset.sum_range_succ]
    exact (absDiff_triangle _ _ _).trans
      (add_le_add (ih (by omega)) (storeHyb_step_le S h Z D h₀ n m (by omega)))

/-- Per-command concrete distances `b c` between `π₁ c` and `π₂ c` give a realization of
    `storeSys S π₂` by `storeSys S π₁`, with bound the sum over the rounds of the one-shot
    bounds at the activations (`storeBound`). -/
theorem realizes_storeSys_of_distC (S : StoreIface C X V H A O) {π₁ π₂ : C → H → SPComp A}
    {b : C → Env H A → ℝ≥0∞} (h : ∀ c, DistC (π₁ c) (π₂ c) (b c)) :
    Realizes (storeSys S π₁) (storeSys S π₂) (storeBound S b π₁) := by
  intro ζ Z
  obtain ⟨Zs, h₀, D⟩ := Z
  have hle := storeHyb_le S h Zs D h₀ Zs.rounds Zs.rounds le_rfl
  rw [storeHyb_zero, storeHyb_self] at hle
  simpa only [Env.gap, view, storeBound] using hle

/-- Per-command realizations between one-shot systems with bounds `B c` give a realization
    of `storeSys S π₂` by `storeSys S π₁`; the one-shot bound of command `c` is `B c` at the
    probing environment. -/
theorem realizes_storeSys (S : StoreIface C X V H A O) {π₁ π₂ : C → H → SPComp A}
    {B : C → (ζ : Type) → Env (Strat ζ H (Option A)) ζ → ℝ≥0∞}
    (h : ∀ c, Realizes (Sys.oneShot (π₁ c)) (Sys.oneShot (π₂ c)) (B c)) :
    Realizes (storeSys S π₁) (storeSys S π₂)
      (storeBound S (fun c W => B c (Option (Option A)) (probeEnv W)) π₁) :=
  realizes_storeSys_of_distC S fun c => distC_of_realizes_oneShot (h c)

/-- Per-command concrete UC emulations of `F c` by `π c` with straight-line simulators
    `simOf (s c)` give a realization of the store system whose command `c` runs the ideal
    functionality `F c` followed by the simulator `s c`; the one-shot bound of command `c`
    is the UC bound at the dummy adversary `SPComp.pure`. -/
theorem realizes_storeSys_of_ucEmulatesCSim {out sim_if leak : Type}
    (S : StoreIface C X V H (out ⊕ leak) O) {π : C → H → SPComp (out ⊕ leak)}
    {F : C → H → SPComp (out ⊕ sim_if)} {s : C → sim_if → SPComp leak}
    {bound : C → (leak → SPComp leak) → Env H (out ⊕ leak) → ℝ≥0∞}
    (h : ∀ c, UCEmulatesCSim ⟨H, out, leak, sim_if, leak⟩ (π c) (F c) (simOf (s c)) (bound c)) :
    Realizes (storeSys S π) (storeSys S fun c => idealOf (F c) (s c))
      (storeBound S (fun c => bound c SPComp.pure) π) :=
  realizes_storeSys_of_distC S fun c Z => by
    simpa [Env.gap, idealOf] using h c SPComp.pure Z

/-- The store bound of per-command bounds `0` is `0`. -/
@[simp] theorem storeBound_zero (S : StoreIface C X V H A O) (π₁ : C → H → SPComp A)
    (ζ : Type) (Z : Env (Strat ζ C O) ζ) :
    storeBound S (fun _ _ => 0) π₁ ζ Z = 0 := by
  simp [storeBound, storeTerm]

end CatCrypt.Crypto.Party
