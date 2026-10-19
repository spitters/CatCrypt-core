/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OracleCollision
public import CatCryptCore.Consensus.UC.ChainEnv
public import CatCryptCore.Consensus.UC.StackEnv
public import CatCryptCore.Consensus.PoSNSB.Prob.ROM
public import CatCryptCore.Consensus.PoSNSB.Prob.Uniform
public import CatCryptCore.Consensus.PoSNSB.Prob.Erasure
public import CatCryptCore.Consensus.PoSNSB.Prob.Script

@[expose] public section
set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The environment-driven PoS-NSB execution as an oracle program

In the random-oracle model the adversary family and the tree types of the honest tree chain
access the hash function only through oracle queries. An oracle adversary family
`OF : OAdvFamily X S` has, for every index `x : X`, baking and receiving actions that are oracle
adversaries and receive the leader string and the verification keys, but not the hash function;
`OF.toAdvFamily` evaluates them against the hash function of the public information. A family of
uniform tree types `UT` gives the tree family `TreeFamily.ofUniform UT`.

For an environment `Z`, the hash program `hashProgE` is one oracle adversary over the block
domain that runs the kernel of `Z` from its heap against the protocol driven by the environment
of `CatCryptCore.Consensus.UC.ChainEnv`, for a protocol with uniform tree types and the family
`OF.toAdvFamily`. It keeps the hash-free state of the execution (`XSt`) and a table of oracle
answers: it queries the encoding of the genesis block, each phase entry before phase `K` runs the
phase `hPhase` of `CatCryptCore.Consensus.PoSNSB.Prob.ROM` of the extended log with the adversary
`OF.atO (scriptOfD x₀ log)`, each hash input of the environment is a query, the views given to
the environment are computed from the table, and after the last activation the remaining phases
up to `K` of the final log run. The output is the final log and the final state and table, or
`none` when a step of the environment fails.

## Main definitions

* `OAdvFamily`, `OAdvFamily.atO`, `OAdvFamily.toAdvFamily`, `OAdvFamily.Bounded` — oracle
  adversary families, the oracle adversary along a sequence of indices, the evaluated family and
  the query and output bound
* `TreeFamily.ofUniform` — the tree family of a family of uniform tree types
* `phaseO`, `phasesO`, `viewO`, `hEv`, `hLoop` — the steps of the hash program
* `hashProgE` — the hash program of an environment

## Main results

* `OAdvFamily.toAdvFamily_at` — the evaluated family along `σ` is the evaluated oracle adversary
  along `σ`
* `isQueryBound_hashProgE` — for a family with `Bounded qc m`, the hash program asks at most
  `1 + Z.input.rounds + K * (|IP| * (qc + m + 1))` queries
* `run_hashProgE_map` — for a family without sampling (`OAdvFamily.NoRand`), the final log of
  the hash program run against `logOracle f` has the distribution of `finalLog` for the seed
  with oracle `f`
* `encB_mem_hashProgE` — the final state of the hash program embeds into phase `K` of the
  execution of its final log, and the encodings of the genesis block and of the history of that
  phase are among the logged queries
* `OAdvFamily.toAdvFamily_derand`, `OAdvFamily.noRand_derand`, `OAdvFamily.Bounded.derand` —
  resolving the sampling of a family keeps its evaluation and its bounds and removes sampling
* `collFinderE_advantage_rom_le` — for a family with `Bounded qc m` and every environment `Z`,
  the collision finder `collFinderE … Z` against `HashScheme.randomFun` has advantage at most
  `qT (qT - 1) / 2 / |Hash|` with `qT = 1 + Z.input.rounds + K * (|IP| * (qc + m + 1))`
* `posFailE_rom_le`, `pos_nsb_securityE_rom`, `chain_realizesE_rom`, `stack_realizesE_rom` —
  the failure bound, the security of PoS-NSB against an environment and the realizations of
  `F_Chain` and `F_FinTree` with that birthday bound in place of the collision advantage
-/

namespace CatCrypt.Crypto.OracleAdv

/-! ## Oracle programs without sampling -/

variable {D R α β : Type}

/-- A bind of programs without `rand` nodes has no `rand` node. -/
theorem NoRand.bind {A : OracleAdv D R α} {g : α → OracleAdv D R β} (hA : A.NoRand)
    (hg : ∀ a, (g a).NoRand) : (A.bind g).NoRand := by
  induction A with
  | ret a => exact hg a
  | rand p k ih => exact hA.elim
  | query d k ih => exact fun r => ih r (hA r)

/-- Running `A.bind g` against `logOracle f`, for `A` without `rand` nodes, runs `g` on the
output of `evalOn f A` from the log extended by its queries. -/
theorem run_logOracle_bind (f : D → R) {A : OracleAdv D R α} (hA : A.NoRand)
    (g : α → OracleAdv D R β) (l : List D) :
    run (logOracle f) (A.bind g) l =
      run (logOracle f) (g (evalOn f A).1) (l ++ (evalOn f A).2) := by
  rw [run_bind, run_logOracle_eq_evalOn f hA, PMF.pure_bind]

/-- The program `A` with every `rand p` node resolved at `p.support_nonempty.some`, the choice
of `evalOn`. -/
noncomputable def derand : OracleAdv D R α → OracleAdv D R α
  | ret a => ret a
  | rand p k => derand (k p.support_nonempty.some)
  | query d k => query d fun r => derand (k r)

theorem noRand_derand (A : OracleAdv D R α) : A.derand.NoRand := by
  induction A with
  | ret a => trivial
  | rand p k ih => exact ih _
  | query d k ih => exact fun r => ih r

theorem evalOn_derand (f : D → R) (A : OracleAdv D R α) : evalOn f A.derand = evalOn f A := by
  induction A with
  | ret a => rfl
  | rand p k ih => exact ih _
  | query d k ih => simp only [derand, evalOn_query, ih]

theorem IsQueryBound.derand {A : OracleAdv D R α} {q : ℕ} (hA : A.IsQueryBound q) :
    A.derand.IsQueryBound q := by
  induction A generalizing q with
  | ret a => trivial
  | rand p k ih => exact ih _ (hA _)
  | query d k ih =>
    cases q with
    | zero => exact hA.elim
    | succ q => exact fun r => ih r (hA r)

end CatCrypt.Crypto.OracleAdv

namespace CatCryptCore.Consensus.PoSNSB

open Parameters BlockParameters Corruption Execution
open CatCrypt.Crypto CatCrypt.Crypto.Signatures

/-! ## Oracle adversary families -/

section OAdvFamily

variable {Tx Hash : Type} {np n Hz : ℕ} {PK Sig : Type}

/-- A family of oracle adversaries with state `S` indexed by `X`: a start state, and for every
index `x` the action when a corrupt party bakes and when it receives messages. The actions
receive the leader string and the verification keys, and query the hash function as an
oracle with queries in `BlockDom` and answers in `Hash`. -/
structure OAdvFamily (X S : Type) (Tx Hash : Type) (np n Hz : ℕ) (PK Sig : Type) where
  /-- The initial state. -/
  st0 : S
  /-- The action of index `x` when a corrupt party bakes. -/
  bake : X → (Fin n → Option (Fin np)) × (Fin np → PK) → Slot → History Tx Hash (Fin np) →
    List (Block Tx Hash (Fin np) × Sig) → MessagePool Tx Hash (Fin np) → S →
      OracleAdv (BlockDom Tx Hash np Hz) Hash (AdvOut Tx Hash np Sig × S)
  /-- The action of index `x` when a corrupt party receives messages. -/
  rcv : X → (Fin n → Option (Fin np)) × (Fin np → PK) → Messages Tx Hash (Fin np) → Slot →
    History Tx Hash (Fin np) → List (Block Tx Hash (Fin np) × Sig) →
      MessagePool Tx Hash (Fin np) → S →
        OracleAdv (BlockDom Tx Hash np Hz) Hash (AdvOut Tx Hash np Sig × S)

namespace OAdvFamily

variable {X S : Type}

/-- The oracle adversary of the family `OF` along the indices `σ`: a call of phase `i` is
answered by the action of index `σ i`. -/
@[reducible] def atO (OF : OAdvFamily X S Tx Hash np n Hz PK Sig) (σ : ℕ → X) :
    OAdversary Tx Hash np n Hz PK Sig where
  AdvState := S
  st0 := OF.st0
  bake pub sl hist tbl mb s :=
    OF.bake (σ (callIdx (⟨none, sl, hist, mb, ()⟩ : CallInput Tx Hash np Unit))) pub sl hist tbl mb s
  rcv pub ms sl hist tbl mb s :=
    OF.rcv (σ (callIdx (⟨some ms, sl, hist, mb, ()⟩ : CallInput Tx Hash np Unit))) pub ms sl
      hist tbl mb s

/-- The adversary family whose actions evaluate the oracle actions of `OF` against the hash
function of the public information. -/
@[reducible] noncomputable def toAdvFamily (OF : OAdvFamily X S Tx Hash np n Hz PK Sig) :
    AdvFamily X S Tx Hash np n Hz PK Sig where
  st0 := OF.st0
  bake x pub sl hist tbl mb s := ((OF.bake x (pub.1, pub.2.2) sl hist tbl mb s).evalOn pub.2.1).1
  rcv x pub ms sl hist tbl mb s :=
    ((OF.rcv x (pub.1, pub.2.2) ms sl hist tbl mb s).evalOn pub.2.1).1

/-- The evaluated family along `σ` is the evaluated oracle adversary along `σ`. -/
theorem toAdvFamily_at (OF : OAdvFamily X S Tx Hash np n Hz PK Sig) (σ : ℕ → X) :
    OF.toAdvFamily.at σ = (OF.atO σ).toAdversary := rfl

/-- Along every sequence of indices, every call of the oracle adversary of `OF` asks at most
`qc` oracle queries and every call of its evaluation outputs at most `m` messages. -/
def Bounded (OF : OAdvFamily X S Tx Hash np n Hz PK Sig) (qc m : ℕ) : Prop :=
  ∀ σ : ℕ → X, (OF.atO σ).Bounded qc m

/-- No action of `OF` samples: every oracle program of the family is free of `rand` nodes. -/
def NoRand (OF : OAdvFamily X S Tx Hash np n Hz PK Sig) : Prop :=
  (∀ x pub sl hist tbl mb s, (OF.bake x pub sl hist tbl mb s).NoRand) ∧
    ∀ x pub ms sl hist tbl mb s, (OF.rcv x pub ms sl hist tbl mb s).NoRand

/-- The family `OF` with every action resolved by `OracleAdv.derand`. -/
noncomputable def derand (OF : OAdvFamily X S Tx Hash np n Hz PK Sig) :
    OAdvFamily X S Tx Hash np n Hz PK Sig where
  st0 := OF.st0
  bake x pub sl hist tbl mb s := (OF.bake x pub sl hist tbl mb s).derand
  rcv x pub ms sl hist tbl mb s := (OF.rcv x pub ms sl hist tbl mb s).derand

theorem noRand_derand (OF : OAdvFamily X S Tx Hash np n Hz PK Sig) : OF.derand.NoRand :=
  ⟨fun _ _ _ _ _ _ _ => OracleAdv.noRand_derand _, fun _ _ _ _ _ _ _ _ => OracleAdv.noRand_derand _⟩

/-- Resolving the sampling of `OF` does not change the evaluated family. -/
theorem toAdvFamily_derand (OF : OAdvFamily X S Tx Hash np n Hz PK Sig) :
    OF.derand.toAdvFamily = OF.toAdvFamily := by
  simp only [toAdvFamily, derand, OracleAdv.evalOn_derand]

theorem atO_derand_toAdversary (OF : OAdvFamily X S Tx Hash np n Hz PK Sig) (σ : ℕ → X) :
    (OF.derand.atO σ).toAdversary = (OF.atO σ).toAdversary := by
  simp only [OAdversary.toAdversary, atO, derand, OracleAdv.evalOn_derand]

theorem Bounded.derand {OF : OAdvFamily X S Tx Hash np n Hz PK Sig} {qc m : ℕ}
    (h : OF.Bounded qc m) : OF.derand.Bounded qc m := fun σ =>
  ⟨⟨fun _ _ _ _ _ _ => ((h σ).1.1 _ _ _ _ _ _).derand,
    fun _ _ _ _ _ _ _ => ((h σ).1.2 _ _ _ _ _ _ _).derand⟩,
    atO_derand_toAdversary OF σ ▸ (h σ).2⟩

end OAdvFamily

end OAdvFamily

/-! ## Tree families of uniform tree types -/

section TreeFamilyUniform

variable {Tx Hash : Type} [DecidableEq Tx] [DecidableEq Hash] {np : ℕ} [Corruption (Fin np)]
  {n Hz : ℕ}

/-- The tree family of a family of uniform tree types: for the leader string `L` and the oracle
`f`, the tree type of `UT L` over the block hash `b ↦ f (encB Hz b)`. -/
def TreeFamily.ofUniform {P : Protocol Tx Hash np n Hz}
    (UT : (L : Fin n → Option (Fin np)) →
      @UTreeType Tx Hash (Fin np) (leaderParams P.IP P.h0 L) P.GB) : TreeFamily P :=
  fun L f => @UTreeType.at Tx Hash (Fin np) (leaderParams P.IP P.h0 L) P.GB (UT L)
    (fun b => f (encB Hz b))

end TreeFamilyUniform

/-! ## Phases of the hash program without sampling -/

section NoRandPhase

variable {Tx Hash : Type} [DecidableEq Tx] [DecidableEq Hash] {np : ℕ} [Corruption (Fin np)]
  {n Hz : ℕ} {PK SK Sig : Type}
  (Sch : PSigScheme (Block Tx Hash (Fin np)) PK SK Sig) [Sch.Deterministic]
  (IP : List (Fin np)) (h0 : Fin np) (GB : Block Tx Hash (Fin np))
  (U : (L : Fin n → Option (Fin np)) → Fin np →
    @UTreeType Tx Hash (Fin np) (leaderParams IP h0 L) GB)
  (txSel : Slot → Fin np → Tx) (L : Fin n → Option (Fin np)) (ks : Fin np → PK × SK)
  (A : OAdversary Tx Hash np n Hz PK Sig) (m : ℕ)

theorem noRand_logBlocks (bs : List (Block Tx Hash (Fin np)))
    (tbl : BlockDom Tx Hash np Hz → Hash) : (logBlocks bs tbl).NoRand := by
  induction bs generalizing tbl with
  | nil => trivial
  | cons b bs ih => exact fun _ => ih _

theorem noRand_hFold {S : Type} {step : Fin np → S → OracleAdv (BlockDom Tx Hash np Hz) Hash S}
    (h : ∀ p s, (step p s).NoRand) (l : List (Fin np)) (s : S) : (hFold step l s).NoRand := by
  induction l with
  | nil => trivial
  | cons p ps ih => exact ih.bind fun _ => h _ _

/-- For an oracle adversary whose actions do not sample, a phase of the hash program does not
sample. -/
theorem noRand_hPhase (hb : ∀ pub sl hist tbl mb st, (A.bake pub sl hist tbl mb st).NoRand)
    (hr : ∀ pub ms sl hist tbl mb st, (A.rcv pub ms sl hist tbl mb st).NoRand)
    (s : HState IP h0 GB U L A) : (hPhase Sch IP h0 GB U txSel L ks A m s).NoRand := by
  have hR : ∀ p s, (hRcv Sch IP h0 GB U L ks A m p s).NoRand := by
    intro p s
    unfold hRcv
    split
    · split
      · trivial
      · exact (hr _ _ _ _ _ _ _).bind fun _ => (noRand_logBlocks _ _).bind fun _ => trivial
    · trivial
  have hB : ∀ p s, (hBake Sch IP h0 GB U txSel L ks A m p s).NoRand := by
    intro p s
    unfold hBake
    split
    · split
      · split
        · exact fun _ => trivial
        · trivial
      · exact (hb _ _ _ _ _ _).bind fun _ => (noRand_logBlocks _ _).bind fun _ => trivial
    · trivial
  unfold hPhase
  split
  · exact (noRand_hFold hR _ _).bind fun _ => trivial
  · exact (noRand_hFold hB _ _).bind fun _ => trivial
  · trivial

end NoRandPhase

end CatCryptCore.Consensus.PoSNSB

namespace CatCryptCore.Consensus.UC.ChainEnv

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open CatCrypt.Crypto.UCTransparent CatCrypt.NonUniform
open CatCryptCore.Consensus.UC.FTree CatCryptCore.Consensus.UC.Chain
open CatCrypt.Crypto.Signatures CatCrypt.Crypto.Assumptions
open PoSNSB Parameters BlockParameters Corruption Execution ClockNet

/-! ## The hash program of an environment -/

section HashProgE

variable {Tx Hash : Type} [DecidableEq Tx] [DecidableEq Hash] {np : ℕ} [Corruption (Fin np)]
  {n Hz : ℕ} {PK SK Sig : Type}
  (Sch : PSigScheme (Block Tx Hash (Fin np)) PK SK Sig) [Sch.Deterministic]
  (IP : List (Fin np)) (h0 : Fin np) (GB : Block Tx Hash (Fin np))
  (U : (L : Fin n → Option (Fin np)) → Fin np →
    @UTreeType Tx Hash (Fin np) (leaderParams IP h0 L) GB)
  (UT : (L : Fin n → Option (Fin np)) → @UTreeType Tx Hash (Fin np) (leaderParams IP h0 L) GB)
  {X S : Type} (OF : OAdvFamily X S Tx Hash np n Hz PK Sig) (x₀ : X) (dt : Slot → Fin np → Tx)
  (L : Fin n → Option (Fin np)) (ks : Fin np → PK × SK) (m K Δ : ℕ)

variable (Hz S) in
/-- The states of the hash program: a hash-free state with adversary states `S` and a table of
oracle answers. -/
abbrev HStE :=
  XSt Tx Hash np (fun p => @UTreeType.T Tx Hash (Fin np) (leaderParams IP h0 L) GB (U L p)) S ×
    (BlockDom Tx Hash np Hz → Hash)

/-- The phase of the hash program after the log `log`: `hPhase` with the honest transactions
`txOf dt log` and the oracle adversary `OF.atO (scriptOfD x₀ log)`. -/
def phaseO (log : List (LogEvOf X Tx Hash np Hz)) (s : HStE Hz IP h0 GB U S L) :
    OracleAdv (BlockDom Tx Hash np Hz) Hash (HStE Hz IP h0 GB U S L) :=
  hPhase Sch IP h0 GB U (txOf dt log) L ks (OF.atO (scriptOfD x₀ log)) m s

/-- `k` phases of the hash program after the log `log`. -/
def phasesO (log : List (LogEvOf X Tx Hash np Hz)) :
    ℕ → HStE Hz IP h0 GB U S L → OracleAdv (BlockDom Tx Hash np Hz) Hash (HStE Hz IP h0 GB U S L)
  | 0, s => .ret s
  | k + 1, s => (phasesO log k s).bind (phaseO Sch IP h0 GB U OF x₀ dt L ks m log)

/-- The view after a phase that reaches the state `s`, from the view `v` of the previous phase:
`vNext` for the seed whose oracle is the table of `s`, at the embedding of the hash-free state
of `s` over the table. -/
noncomputable def viewO (v : TreeView (Option (Fin np)) (Block Tx Hash (Fin np))) (s : HStE Hz IP h0 GB U S L) :
    TreeView (Option (Fin np)) (Block Tx Hash (Fin np)) :=
  vNext (Protocol.ofUniform (Hz := Hz) IP h0 GB U dt) (TreeFamily.ofUniform UT) (uSeed L ks s.2) v
    (emb IP h0 GB U dt L ks (OF.toAdvFamily.at fun _ => x₀) s.2 s.1)

/-- The hash program's step on the input `e` after the log `log` with `j` phase entries, the
view `v` and the state `s`, continued by `k` on the next view, the next state and the leakage:
a phase entry before phase `K` runs the phase of the extended log; a hash input queries the
oracle, records the answer in the table and leaks it; the other inputs keep the view and the
state. -/
noncomputable def hEv {β : Type} (log : List (LogEvOf X Tx Hash np Hz)) (j : ℕ)
    (v : TreeView (Option (Fin np)) (Block Tx Hash (Fin np))) (s : HStE Hz IP h0 GB U S L)
    (e : EnvEv Tx Hash np Hz X)
    (k : TreeView (Option (Fin np)) (Block Tx Hash (Fin np)) → HStE Hz IP h0 GB U S L →
      Option Hash → OracleAdv (BlockDom Tx Hash np Hz) Hash β) :
    OracleAdv (BlockDom Tx Hash np Hz) Hash β :=
  match e with
  | .inr (.step x) =>
    if j < K then
      (phaseO Sch IP h0 GB U OF x₀ dt L ks m (log ++ [.inr (.step x)]) s).bind fun s' =>
        k (viewO IP h0 GB U UT OF x₀ dt L ks v s') s' none
    else k v s none
  | .inr (.hash d) => .query d fun r => k v (s.1, Function.update s.2 d r) (some r)
  | .inl _ => k v s none

/-- **The loop of the hash program.** With `r` activations left, from the state `z` of the
kernel of the environment `Z` at the heap `h`, the log `log` with `j` phase entries, the view
`v`, the state `q` of the clock and network and the state `s`: draw the next input `e` of `Z`,
run the step `hEv`, give `Z` the clock output, the view and the leakage, and continue. After
the last activation it runs the remaining phases up to `K` of the final log and returns the
final log and state; it returns `none` when a step of `Z` fails. -/
noncomputable def hLoop {ζ : Type} (Z : Strat ζ (EnvEv Tx Hash np Hz X) (EnvOut Tx Hash np)) :
    ℕ → ζ → Heap → List (LogEvOf X Tx Hash np Hz) → ℕ →
      TreeView (Option (Fin np)) (Block Tx Hash (Fin np)) → CNS → HStE Hz IP h0 GB U S L →
        OracleAdv (BlockDom Tx Hash np Hz) Hash
          (Option (List (LogEvOf X Tx Hash np Hz) × HStE Hz IP h0 GB U S L))
  | 0, _, _, log, j, _, _, s =>
    (phasesO Sch IP h0 GB U OF x₀ dt L ks m log (K - j) s).bind fun s' => .ret (some (log, s'))
  | r + 1, z, h, log, j, v, q, s =>
    .rand (Z.next z h) fun o => match o with
      | none => .ret none
      | some ((z₁, e), h₁) =>
        hEv Sch IP h0 GB U UT OF x₀ dt L ks m K log j v s e fun v' s' lk =>
          .rand (Z.obs z₁ (((cnNext Δ q (reqJ j e)).2.1, v'), lk) h₁) fun o' =>
            match o' with
            | none => .ret none
            | some (z₂, h₂) =>
              hLoop Z r z₂ h₂ (log ++ [e]) (phaseNext j e) v' (cnNext Δ q (reqJ j e)).1 s'

/-- **The hash program of an environment.** It queries the encoding of the genesis block, whose
answer initialises the table, and runs the loop `hLoop` from the kernel of `Z` at its heap, the
empty log, the initial view, the initial state of the ideal clock and network and the hash-free
initial state. -/
noncomputable def hashProgE {ζ : Type}
    (Z : Env (Strat ζ (EnvEv Tx Hash np Hz X) (EnvOut Tx Hash np)) ζ) :
    OracleAdv (BlockDom Tx Hash np Hz) Hash
      (Option (List (LogEvOf X Tx Hash np Hz) × HStE Hz IP h0 GB U S L)) :=
  .query (encB Hz GB) fun r =>
    hLoop Sch IP h0 GB U UT OF x₀ dt L ks m K Δ Z.input Z.input.rounds Z.input.init Z.heap [] 0
      (viewO IP h0 GB U UT OF x₀ dt L ks initView
        (PoSNSB.x₀ IP h0 GB U L (OF.toAdvFamily.at fun _ => x₀), fun _ => r))
      (ideal (clockNetF (M := Unit) H₁ Δ) (clockNet H₁ Δ).proto).init
      (PoSNSB.x₀ IP h0 GB U L (OF.toAdvFamily.at fun _ => x₀), fun _ => r)

/-! ### The views computed from the table -/

/-- **Locality of the views.** At a state whose table agrees with `f` at the genesis block and at
the blocks of the trees, the view `viewO` is `vNext` for the seed with oracle `f` at the
embedding over `f` of the hash-free state, for every transaction selection and every sequence of
indices. -/
theorem viewO_eq_vNext (f : BlockDom Tx Hash np Hz → Hash) (txSel : Slot → Fin np → Tx)
    (σ : ℕ → X) (v : TreeView (Option (Fin np)) (Block Tx Hash (Fin np)))
    (s : HStE Hz IP h0 GB U S L) (hGB : s.2 (encB Hz GB) = f (encB Hz GB))
    (hloc : ∀ p t, s.1.trees p = some t →
      ∀ b ∈ @UTreeType.allBlocks Tx Hash (Fin np) (leaderParams IP h0 L) GB (U L p) t,
        s.2 (encB Hz b) = f (encB Hz b)) :
    viewO IP h0 GB U UT OF x₀ dt L ks v s =
      vNext (Protocol.ofUniform (Hz := Hz) IP h0 GB U dt) (TreeFamily.ofUniform UT)
        (uSeed L ks f) v (emb IP h0 GB U txSel L ks (OF.toAdvFamily.at σ) f s.1) := by
  have hpos : ∀ o, posOf (Protocol.ofUniform (Hz := Hz) IP h0 GB U dt) (TreeFamily.ofUniform UT)
      (uSeed L ks s.2) (emb IP h0 GB U dt L ks (OF.toAdvFamily.at fun _ => x₀) s.2 s.1) o =
      posOf (Protocol.ofUniform (Hz := Hz) IP h0 GB U dt) (TreeFamily.ofUniform UT)
        (uSeed L ks f) (emb IP h0 GB U txSel L ks (OF.toAdvFamily.at σ) f s.1) o := by
    let _ := leaderParams IP h0 L
    intro o
    cases o with
    | none =>
      unfold posOf honest_tree_chain
      dsimp only
      refine ((UT L).bestChain_local (fun b => s.2 (encB Hz b)) (fun b => f (encB Hz b)) _ _
        ?_).trans ?_
      · let _ : BlockParameters Tx Hash (Fin np) := ⟨GB, fun b => s.2 (encB Hz b)⟩
        intro b hb
        unfold honest_tree at hb
        rcases List.mem_cons.1 ((all_build ((TreeFamily.ofUniform
          (P := Protocol.ofUniform (Hz := Hz) IP h0 GB U dt) UT) L s.2) _ b).1 hb) with h | hb
        · rw [h]
          exact hGB
        · obtain ⟨_, hl, hbl⟩ := List.mem_flatten.1 hb
          obtain ⟨p, -, rfl⟩ := List.mem_map.1 hl
          simp only [blocks, emb] at hbl
          cases ht : s.1.trees p with
          | none => rw [ht] at hbl; cases hbl
          | some t =>
            rw [ht] at hbl
            exact hloc p t ht b hbl
      · unfold honest_tree build_tree
        congr 2
        exact congrArg List.flatten (List.map_congr_left fun p _ => by
          simp only [blocks, emb]
          cases s.1.trees p <;> rfl)
    | some p =>
      dsimp only [posOf, emb]
      cases ht : s.1.trees p with
      | none => rfl
      | some t => exact (U L p).bestChain_local _ _ _ t (hloc p t ht)
  unfold viewO vNext
  congr 1
  · funext o
    rw [hpos]
  · funext o
    exact hpos o

/-! ### The evaluation of the hash program -/

section Eval

variable (f : BlockDom Tx Hash np Hz → Hash)

/-- The invariant of the hash program against the oracle `f` after the log `log` with `j` phase
entries, the view `v`, the state `s` and the logged queries `l`: `v` is the view of the log after
`j` phases, the hash-free state embeds over `f` into the state of its execution after `min j K`
phases, the table satisfies the invariant `HInv`, and the encodings of the genesis block and of
the blocks of the history are logged. -/
def HInvE (log : List (LogEvOf X Tx Hash np Hz)) (j : ℕ)
    (v : TreeView (Option (Fin np)) (Block Tx Hash (Fin np))) (s : HStE Hz IP h0 GB U S L)
    (l : List (BlockDom Tx Hash np Hz)) : Prop :=
  j = (steps log).length ∧
    v = viewE (Protocol.ofUniform (Hz := Hz) IP h0 GB U dt) Sch OF.toAdvFamily x₀ dt
      (TreeFamily.ofUniform UT) K (uSeed L ks f) log j ∧
    emb IP h0 GB U (txOf dt log) L ks (OF.toAdvFamily.at (scriptOfD x₀ log)) f s.1 =
      sTrace Sch ((Protocol.ofUniform (Hz := Hz) IP h0 GB U dt).withTx (txOf dt log))
        (uSeed L ks f) (OF.toAdvFamily.at (scriptOfD x₀ log)) false (min j K) ∧
    HInv IP h0 GB U L (OF.atO (scriptOfD x₀ log)) f s.1 s.2 ∧
    ∀ b ∈ GB :: s.1.history.map get_block, encB Hz b ∈ l

omit [Sch.Deterministic] in
/-- The embedding of a hash-free state does not depend on the transaction selection and on the
indices of the family. -/
theorem emb_congr (t t' : Slot → Fin np → Tx) (σ σ' : ℕ → X)
    (x : XS IP h0 GB U L (OF.toAdvFamily.at σ)) :
    emb IP h0 GB U t L ks (OF.toAdvFamily.at σ) f x =
      emb IP h0 GB U t' L ks (OF.toAdvFamily.at σ') f x := rfl

/-- **The incremental execution over the hash-free states.** If the hash-free state `xs`
embeds into phase `j` of the execution of a log with at least `j` phase entries, its hash-free
phase for an extension of the log embeds into phase `j + 1` of the execution of the
extension. -/
theorem emb_xPhase_snoc {log : List (LogEvOf X Tx Hash np Hz)} {j : ℕ}
    (hj : j ≤ (steps log).length) (l : List (LogEvOf X Tx Hash np Hz))
    (xs : XS IP h0 GB U L (OF.toAdvFamily.at (scriptOfD x₀ log)))
    (hN : emb IP h0 GB U (txOf dt log) L ks (OF.toAdvFamily.at (scriptOfD x₀ log)) f xs =
      sTrace Sch ((Protocol.ofUniform (Hz := Hz) IP h0 GB U dt).withTx (txOf dt log))
        (uSeed L ks f) (OF.toAdvFamily.at (scriptOfD x₀ log)) false j) :
    emb IP h0 GB U (txOf dt (log ++ l)) L ks (OF.toAdvFamily.at (scriptOfD x₀ (log ++ l))) f
        (xPhase Sch IP h0 GB U (txOf dt (log ++ l)) L ks
          (OF.toAdvFamily.at (scriptOfD x₀ (log ++ l))) false f xs) =
      sTrace Sch ((Protocol.ofUniform (Hz := Hz) IP h0 GB U dt).withTx (txOf dt (log ++ l)))
        (uSeed L ks f) (OF.toAdvFamily.at (scriptOfD x₀ (log ++ l))) false (j + 1) := by
  rw [← sPhase_emb, sTrace_snoc_step Sch (Protocol.ofUniform (Hz := Hz) IP h0 GB U dt)
    (uSeed L ks f) OF.toAdvFamily false x₀ dt hj l]
  exact congrArg _ ((emb_congr IP h0 GB U OF L ks f _ _ _ _ xs).trans hN)

omit [Sch.Deterministic] in
/-- `HInv` does not depend on the oracle adversary beyond its state type. -/
theorem hInv_congr {σ σ' : ℕ → X} {x : XS IP h0 GB U L (OF.atO σ).toAdversary}
    {tbl : BlockDom Tx Hash np Hz → Hash} (h : HInv IP h0 GB U L (OF.atO σ) f x tbl) :
    HInv IP h0 GB U L (OF.atO σ') f x tbl :=
  ⟨⟨h.hist.buff, h.hist.state⟩, h.tbl⟩

/-- An input that is not a phase entry, or a phase entry from phase `K` on, keeps the
invariant on the extended log when the state keeps its hash-free part, its table agrees with
`f` where the old one did, and the logged queries extend the old ones. -/
theorem hInvE_append {log : List (LogEvOf X Tx Hash np Hz)} {j : ℕ}
    {v : TreeView (Option (Fin np)) (Block Tx Hash (Fin np))} {s : HStE Hz IP h0 GB U S L}
    {l : List (BlockDom Tx Hash np Hz)}
    (hI : HInvE Sch IP h0 GB U UT OF x₀ dt L ks K f log j v s l)
    (e : EnvEv Tx Hash np Hz X) (he : stepOf e = none ∨ (∃ x, e = .inr (.step x)) ∧ K ≤ j)
    (tbl : BlockDom Tx Hash np Hz → Hash)
    (htbl : ∀ b ∈ GB :: s.1.history.map get_block, tbl (encB Hz b) = f (encB Hz b))
    (l' : List (BlockDom Tx Hash np Hz)) (hl : l ⊆ l') :
    HInvE Sch IP h0 GB U UT OF x₀ dt L ks K f (log ++ [e]) (phaseNext j e) v (s.1, tbl) l' := by
  obtain ⟨hjl, hv, hN, hH, hQ⟩ := hI
  have hmj : min j K ≤ (steps log).length := by omega
  have hmin : min (phaseNext j e) K = min j K := by
    rcases he with he | ⟨⟨x, rfl⟩, hKj⟩
    · rw [phaseNext_of_stepOf_none j e he]
    · simp only [phaseNext]; omega
  refine ⟨?_, ?_, ?_, ⟨⟨hH.hist.buff, hH.hist.state⟩, htbl⟩, fun b hb => hl (hQ b hb)⟩
  · rcases he with he | ⟨⟨x, rfl⟩, -⟩
    · rw [phaseNext_of_stepOf_none j e he]
      simp [hjl, steps, he]
    · simp [hjl, phaseNext, steps, stepOf]
  · rcases he with he | ⟨⟨x, rfl⟩, hKj⟩
    · rw [phaseNext_of_stepOf_none j e he, hv,
        viewE_append (Protocol.ofUniform (Hz := Hz) IP h0 GB U dt) Sch OF.toAdvFamily x₀ dt
          (TreeFamily.ofUniform UT) K (uSeed L ks f) hjl.le]
    · rw [hv]
      exact (viewE_succ_of_le (Protocol.ofUniform (Hz := Hz) IP h0 GB U dt) Sch OF.toAdvFamily
        x₀ dt (TreeFamily.ofUniform UT) K (uSeed L ks f) hKj hjl.le _).symm
  · rw [hmin]
    exact hN.trans (sTrace_append_of_le Sch (Protocol.ofUniform (Hz := Hz) IP h0 GB U dt)
      (uSeed L ks f) OF.toAdvFamily false x₀ dt hmj [e] _ le_rfl).symm

/-- **A step of the hash program against `logOracle f`.** From a state with the invariant, the
run of the step `hEv` on the input `e` is the run of its continuation on a view, a state and a
log of queries with the invariant for the extended log, and on the leakage `leakOf` of the seed
with oracle `f`. -/
theorem run_hEv (hOF : OF.NoRand) (hm : ∀ σ, (OF.atO σ).toAdversary.OutputBound m) {β : Type}
    {log : List (LogEvOf X Tx Hash np Hz)} {j : ℕ}
    {v : TreeView (Option (Fin np)) (Block Tx Hash (Fin np))} {s : HStE Hz IP h0 GB U S L}
    {l : List (BlockDom Tx Hash np Hz)}
    (hI : HInvE Sch IP h0 GB U UT OF x₀ dt L ks K f log j v s l) (e : EnvEv Tx Hash np Hz X)
    (k : TreeView (Option (Fin np)) (Block Tx Hash (Fin np)) → HStE Hz IP h0 GB U S L →
      Option Hash → OracleAdv (BlockDom Tx Hash np Hz) Hash β) :
    ∃ v' s' l', OracleAdv.run (OracleAdv.logOracle f)
        (hEv Sch IP h0 GB U UT OF x₀ dt L ks m K log j v s e k) l =
      OracleAdv.run (OracleAdv.logOracle f) (k v' s' (leakOf (uSeed L ks f) e)) l' ∧
      HInvE Sch IP h0 GB U UT OF x₀ dt L ks K f (log ++ [e]) (phaseNext j e) v' s' l' := by
  rcases e with tx | (x | d)
  · exact ⟨v, (s.1, s.2), l, rfl, hInvE_append Sch IP h0 GB U UT OF x₀ dt L ks K f hI _
      (Or.inl rfl) s.2 hI.2.2.2.1.tbl l (List.Subset.refl _)⟩
  · by_cases hjK : j < K
    · obtain ⟨xs, tbl⟩ := s
      obtain ⟨hjl, hv, hN, hH, hQ⟩ := hI
      rw [min_eq_left hjK.le] at hN
      subst hv
      have ho : xs.exec_order = IP := by
        have := (histBound_sTrace Sch
          ((Protocol.ofUniform (Hz := Hz) IP h0 GB U dt).withTx (txOf dt log))
          (OF.toAdvFamily.at (scriptOfD x₀ log)) (uSeed L ks f) (hm _) j).1
        rw [← hN] at this
        exact this
      obtain ⟨p1, p2, p3⟩ := hPhase_spec Sch IP h0 GB U (txOf dt (log ++ [.inr (.step x)])) L ks
        (OF.atO (scriptOfD x₀ (log ++ [.inr (.step x)]))) m (hm _) f xs tbl
        (hInv_congr IP h0 GB U OF L f hH) ho
      have key := emb_xPhase_snoc Sch IP h0 GB U OF x₀ dt L ks f hjl.le [.inr (.step x)] xs hN
      refine ⟨viewO IP h0 GB U UT OF x₀ dt L ks (viewE (Protocol.ofUniform (Hz := Hz) IP h0 GB U dt)
          Sch OF.toAdvFamily x₀ dt (TreeFamily.ofUniform UT) K (uSeed L ks f) log j)
          (OracleAdv.evalOn f (hPhase Sch IP h0 GB U (txOf dt (log ++ [.inr (.step x)])) L ks
            (OF.atO (scriptOfD x₀ (log ++ [.inr (.step x)]))) m (xs, tbl))).1,
        (OracleAdv.evalOn f (hPhase Sch IP h0 GB U (txOf dt (log ++ [.inr (.step x)])) L ks
            (OF.atO (scriptOfD x₀ (log ++ [.inr (.step x)]))) m (xs, tbl))).1,
        l ++ (OracleAdv.evalOn f (hPhase Sch IP h0 GB U (txOf dt (log ++ [.inr (.step x)])) L ks
            (OF.atO (scriptOfD x₀ (log ++ [.inr (.step x)]))) m (xs, tbl))).2, ?_, ?_⟩
      rotate_left
      · have key' : emb IP h0 GB U (txOf dt (log ++ [.inr (.step x)])) L ks
            (OF.toAdvFamily.at (scriptOfD x₀ (log ++ [.inr (.step x)]))) f
            (OracleAdv.evalOn f (hPhase Sch IP h0 GB U (txOf dt (log ++ [.inr (.step x)])) L ks
              (OF.atO (scriptOfD x₀ (log ++ [.inr (.step x)]))) m (xs, tbl))).1.1 =
            sTrace Sch ((Protocol.ofUniform (Hz := Hz) IP h0 GB U dt).withTx
              (txOf dt (log ++ [.inr (.step x)]))) (uSeed L ks f)
              (OF.toAdvFamily.at (scriptOfD x₀ (log ++ [.inr (.step x)]))) false (j + 1) := by
          rw [p1]
          exact key
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · simp [hjl, phaseNext, steps, stepOf]
        · rw [viewO_eq_vNext IP h0 GB U UT OF x₀ dt L ks f (txOf dt (log ++ [.inr (.step x)]))
            (scriptOfD x₀ (log ++ [.inr (.step x)])) _ _ (p2.tbl GB List.mem_cons_self)
            fun p t ht b hb => p2.tbl b (p2.hist.state p t (p1 ▸ ht) b hb)]
          exact (congrArg _ key').trans (viewE_succ (Protocol.ofUniform (Hz := Hz) IP h0 GB U dt)
            Sch OF.toAdvFamily x₀ dt (TreeFamily.ofUniform UT) K (uSeed L ks f) hjK hjl.le
            [.inr (.step x)]).symm
        · show _ = sTrace _ _ _ _ _ (min (j + 1) K)
          rw [min_eq_left hjK]
          exact key'
        · rw [p1]
          exact p2
        · intro b hb
          rw [p1] at hb
          rcases List.mem_cons.1 hb with rfl | hb
          · exact List.mem_append_left _ (hQ _ List.mem_cons_self)
          · rcases p3 b hb with hb | hb
            · exact List.mem_append_left _ (hQ b (List.mem_cons_of_mem _ hb))
            · exact List.mem_append_right _ hb
      · simp only [hEv, if_pos hjK]
        exact OracleAdv.run_logOracle_bind f (noRand_hPhase Sch IP h0 GB U _ L ks _ m
          (fun _ _ _ _ _ _ => hOF.1 _ _ _ _ _ _ _) (fun _ _ _ _ _ _ _ => hOF.2 _ _ _ _ _ _ _ _)
          _) _ l
    · refine ⟨v, (s.1, s.2), l, ?_, hInvE_append Sch IP h0 GB U UT OF x₀ dt L ks K f hI _
        (Or.inr ⟨⟨x, rfl⟩, not_lt.1 hjK⟩) s.2 hI.2.2.2.1.tbl l (List.Subset.refl _)⟩
      simp only [hEv, if_neg hjK]
      rfl
  · refine ⟨v, (s.1, Function.update s.2 d (f d)), l ++ [d], ?_,
      hInvE_append Sch IP h0 GB U UT OF x₀ dt L ks K f hI _ (Or.inl rfl) _ (fun b hb => ?_) _
        (List.subset_append_left _ _)⟩
    · simp only [hEv, OracleAdv.run_query, OracleAdv.logOracle, PMF.pure_bind]
      rfl
    · by_cases h : encB Hz b = d
      · rw [h, Function.update_self]
      · rw [Function.update_of_ne h]
        exact hI.2.2.2.1.tbl b hb

/-- **The loop of the hash program against `logOracle f`.** Let `t` be a state of `chainSimω`
for the seed with oracle `f`, whose seed is unset or this seed, and let the view, the state and
the logged queries of the hash program satisfy the invariant for the log of `t`. Then the final
logs of the remaining `r` activations of `Z` from `t` and of the loop `hLoop` from the same log,
number of phase entries and clock state have the same distribution, a failed step of `Z` giving
`none` on both sides. -/
theorem run_hLoop_map (hOF : OF.NoRand) (hm : ∀ σ, (OF.atO σ).toAdversary.OutputBound m)
    {ζ : Type} (Z : Strat ζ (EnvEv Tx Hash np Hz X) (EnvOut Tx Hash np)) (r : ℕ) :
    ∀ (z : ζ) (h : Heap) (t : SimStE Tx Hash np n Hz PK SK X) (b : Bool)
      (v : TreeView (Option (Fin np)) (Block Tx Hash (Fin np))) (s : HStE Hz IP h0 GB U S L)
      (l : List (BlockDom Tx Hash np Hz)),
      t.1.1.getD (uSeed L ks f) = uSeed L ks f →
      HInvE Sch IP h0 GB U UT OF x₀ dt L ks K f t.1.2.1 t.1.2.2.1 v s l →
      (OracleAdv.run (OracleAdv.logOracle f)
          (hLoop Sch IP h0 GB U UT OF x₀ dt L ks m K Δ Z r z h t.1.2.1 t.1.2.2.1 v t.2 s) l).map
          (fun o => o.1.map Prod.fst) =
        (loop (chainSimω (Protocol.ofUniform (Hz := Hz) IP h0 GB U dt) Sch OF.toAdvFamily x₀ dt
          (TreeFamily.ofUniform UT) K Δ (uSeed L ks f)) (fun _ => false) Z r (z, t, b) h).map
          (Option.map fun c => c.1.2.1.1.2.1) := by
  induction r with
  | zero =>
    intro z h t b v s l _ _
    simp only [hLoop, OracleAdv.run_bind, OracleAdv.run_ret, PMF.map_bind, PMF.pure_map,
      PMF.bind_const, loop, SPComp.pure, SDistr.pure, Option.map_some]
  | succ r ih =>
    intro z h t b v s l hseed hI
    simp only [hLoop, loop, OracleAdv.run_rand, PMF.map_bind, SPComp.bind, SDistr.bind]
    congr 1
    funext o
    rcases o with _ | ⟨⟨z₁, e⟩, h₁⟩
    · rw [OracleAdv.run_ret, PMF.pure_map, SDistr.fail, PMF.pure_map]
      rfl
    · dsimp only
      obtain ⟨v', s', l', hrun, hI'⟩ := run_hEv Sch IP h0 GB U UT OF x₀ dt L ks m K f hOF hm hI e
        fun v' s' lk => .rand (Z.obs z₁ (((cnNext Δ t.2 (reqJ t.1.2.2.1 e)).2.1, v'), lk) h₁)
          fun o' => match o' with
            | none => .ret none
            | some (z₂, h₂) =>
              hLoop Sch IP h0 GB U UT OF x₀ dt L ks m K Δ Z r z₂ h₂ (t.1.2.1 ++ [e])
                (phaseNext t.1.2.2.1 e) v' (cnNext Δ t.2 (reqJ t.1.2.2.1 e)).1 s'
      rw [hrun, chainSimω_step_eq, hseed]
      simp only [SPComp.pure, SDistr.pure, PMF.pure_bind, pstNext, ← hI'.2.1,
        OracleAdv.run_rand, PMF.map_bind]
      congr 1
      funext o'
      rcases o' with _ | ⟨z₂, h₂⟩
      · rw [OracleAdv.run_ret, PMF.pure_map, SDistr.fail, PMF.pure_map]
        rfl
      · exact ih z₂ h₂ ((some (uSeed L ks f), t.1.2.1 ++ [e], phaseNext t.1.2.2.1 e, v',
          leakOf (uSeed L ks f) e), (cnNext Δ t.2 (reqJ t.1.2.2.1 e)).1) (b || false) v' s' l'
          rfl hI'

theorem noRand_phasesO (hOF : OF.NoRand) (log : List (LogEvOf X Tx Hash np Hz)) (k : ℕ)
    (s : HStE Hz IP h0 GB U S L) : (phasesO Sch IP h0 GB U OF x₀ dt L ks m log k s).NoRand := by
  induction k with
  | zero => trivial
  | succ k ih =>
    exact ih.bind fun _ => noRand_hPhase Sch IP h0 GB U _ L ks _ m
      (fun _ _ _ _ _ _ => hOF.1 _ _ _ _ _ _ _) (fun _ _ _ _ _ _ _ => hOF.2 _ _ _ _ _ _ _ _) _

/-- **The remaining phases.** From a state whose hash-free part embeds over `f` into phase `i`
of the execution of the log `log`, with the invariant `HInv` and the encodings of the genesis
block and of the history among the queries `l`, the evaluation of `k` phases of the hash program
embeds into phase `i + k`, keeps the invariant, and the encodings of the genesis block and of the
history are among `l` and the queries of the evaluation. -/
theorem evalOn_phasesO (hm : ∀ σ, (OF.atO σ).toAdversary.OutputBound m)
    (log : List (LogEvOf X Tx Hash np Hz)) (k : ℕ) :
    ∀ (i : ℕ) (s : HStE Hz IP h0 GB U S L) (l : List (BlockDom Tx Hash np Hz)),
      emb IP h0 GB U (txOf dt log) L ks (OF.toAdvFamily.at (scriptOfD x₀ log)) f s.1 =
        sTrace Sch ((Protocol.ofUniform (Hz := Hz) IP h0 GB U dt).withTx (txOf dt log))
          (uSeed L ks f) (OF.toAdvFamily.at (scriptOfD x₀ log)) false i →
      HInv IP h0 GB U L (OF.atO (scriptOfD x₀ log)) f s.1 s.2 →
      (∀ b ∈ GB :: s.1.history.map get_block, encB Hz b ∈ l) →
      emb IP h0 GB U (txOf dt log) L ks (OF.toAdvFamily.at (scriptOfD x₀ log)) f
          (OracleAdv.evalOn f (phasesO Sch IP h0 GB U OF x₀ dt L ks m log k s)).1.1 =
        sTrace Sch ((Protocol.ofUniform (Hz := Hz) IP h0 GB U dt).withTx (txOf dt log))
          (uSeed L ks f) (OF.toAdvFamily.at (scriptOfD x₀ log)) false (i + k) ∧
      HInv IP h0 GB U L (OF.atO (scriptOfD x₀ log)) f
          (OracleAdv.evalOn f (phasesO Sch IP h0 GB U OF x₀ dt L ks m log k s)).1.1
          (OracleAdv.evalOn f (phasesO Sch IP h0 GB U OF x₀ dt L ks m log k s)).1.2 ∧
      ∀ b ∈ GB :: (OracleAdv.evalOn f
          (phasesO Sch IP h0 GB U OF x₀ dt L ks m log k s)).1.1.history.map get_block,
        encB Hz b ∈ l ++ (OracleAdv.evalOn f (phasesO Sch IP h0 GB U OF x₀ dt L ks m log k s)).2 := by
  induction k with
  | zero =>
    intro i s l hN hH hQ
    exact ⟨hN, hH, fun b hb => List.mem_append_left _ (hQ b hb)⟩
  | succ k ih =>
    intro i s l hN hH hQ
    obtain ⟨h1, h2, h3⟩ := ih i s l hN hH hQ
    simp only [phasesO, phaseO, OracleAdv.evalOn_bind]
    generalize OracleAdv.evalOn f (phasesO Sch IP h0 GB U OF x₀ dt L ks m log k s) = Y
      at h1 h2 h3 ⊢
    obtain ⟨⟨y, tb⟩, Q⟩ := Y
    dsimp only at h1 h2 h3 ⊢
    have ho : y.exec_order = IP := by
      have := (histBound_sTrace Sch
        ((Protocol.ofUniform (Hz := Hz) IP h0 GB U dt).withTx (txOf dt log))
        (OF.toAdvFamily.at (scriptOfD x₀ log)) (uSeed L ks f) (hm _) (i + k)).1
      rw [← h1] at this
      exact this
    obtain ⟨p1, p2, p3⟩ := hPhase_spec Sch IP h0 GB U (txOf dt log) L ks
      (OF.atO (scriptOfD x₀ log)) m (hm _) f y tb h2 ho
    suffices key : ∀ W : HStE Hz IP h0 GB U S L × List (BlockDom Tx Hash np Hz),
        W = OracleAdv.evalOn f (hPhase Sch IP h0 GB U (txOf dt log) L ks
          (OF.atO (scriptOfD x₀ log)) m (y, tb)) →
        emb IP h0 GB U (txOf dt log) L ks (OF.toAdvFamily.at (scriptOfD x₀ log)) f W.1.1 =
          sTrace Sch ((Protocol.ofUniform (Hz := Hz) IP h0 GB U dt).withTx (txOf dt log))
            (uSeed L ks f) (OF.toAdvFamily.at (scriptOfD x₀ log)) false (i + (k + 1)) ∧
        HInv IP h0 GB U L (OF.atO (scriptOfD x₀ log)) f W.1.1 W.1.2 ∧
        ∀ b ∈ GB :: W.1.1.history.map get_block, encB Hz b ∈ l ++ (Q ++ W.2) from key _ rfl
    intro W hW
    rw [← hW] at p1 p2 p3
    obtain ⟨⟨y', tb'⟩, Q'⟩ := W
    dsimp only at p1 p2 p3 ⊢
    subst p1
    refine ⟨?_, p2, ?_⟩
    · rw [← Nat.add_assoc, sTrace_succ, ← h1]
      exact (sPhase_emb Sch IP h0 GB U (txOf dt log) L ks
        (OF.toAdvFamily.at (scriptOfD x₀ log)) false f _).symm
    · intro b hb
      rw [← List.append_assoc]
      rcases List.mem_cons.1 hb with rfl | hb
      · exact List.mem_append_left _ (h3 _ List.mem_cons_self)
      · rcases p3 b hb with hb | hb
        · exact List.mem_append_left _ (h3 b (List.mem_cons_of_mem _ hb))
        · exact List.mem_append_right _ hb

/-- **The final state of the loop.** From a state with the invariant, every outcome of the run
of the loop `hLoop` against `logOracle f` that returns a final log `fl` and a state `s'` has the
hash-free part of `s'` embedding over `f` into phase `K` of the execution of `fl`, and the
encodings of the genesis block and of every block of its history among the logged queries. -/
theorem run_hLoop_support (hOF : OF.NoRand) (hm : ∀ σ, (OF.atO σ).toAdversary.OutputBound m)
    {ζ : Type} (Z : Strat ζ (EnvEv Tx Hash np Hz X) (EnvOut Tx Hash np)) (r : ℕ) :
    ∀ (z : ζ) (h : Heap) (log : List (LogEvOf X Tx Hash np Hz)) (j : ℕ)
      (v : TreeView (Option (Fin np)) (Block Tx Hash (Fin np))) (q : CNS)
      (s : HStE Hz IP h0 GB U S L) (l : List (BlockDom Tx Hash np Hz)),
      HInvE Sch IP h0 GB U UT OF x₀ dt L ks K f log j v s l →
      ∀ o ∈ (OracleAdv.run (OracleAdv.logOracle f)
          (hLoop Sch IP h0 GB U UT OF x₀ dt L ks m K Δ Z r z h log j v q s) l).support,
      ∀ fl s', o.1 = some (fl, s') →
        emb IP h0 GB U (txOf dt fl) L ks (OF.toAdvFamily.at (scriptOfD x₀ fl)) f s'.1 =
          sTrace Sch ((Protocol.ofUniform (Hz := Hz) IP h0 GB U dt).withTx (txOf dt fl))
            (uSeed L ks f) (OF.toAdvFamily.at (scriptOfD x₀ fl)) false K ∧
        ∀ b ∈ GB :: s'.1.history.map get_block, encB Hz b ∈ o.2 := by
  induction r with
  | zero =>
    intro z h log j v q s l hI o ho fl s' hos
    rw [hLoop, OracleAdv.run_logOracle_bind f
      (noRand_phasesO Sch IP h0 GB U OF x₀ dt L ks m hOF log _ s), OracleAdv.run_ret,
      PMF.support_pure, Set.mem_singleton_iff] at ho
    subst ho
    simp only [Option.some.injEq, Prod.mk.injEq] at hos
    obtain ⟨rfl, rfl⟩ := hos
    obtain ⟨h1, -, h3⟩ := evalOn_phasesO Sch IP h0 GB U OF x₀ dt L ks m f hm log (K - j)
      (min j K) s l hI.2.2.1 hI.2.2.2.1 hI.2.2.2.2
    rw [show min j K + (K - j) = K by omega] at h1
    exact ⟨h1, h3⟩
  | succ r ih =>
    intro z h log j v q s l hI o ho fl s' hos
    simp only [hLoop, OracleAdv.run_rand, PMF.mem_support_bind_iff] at ho
    obtain ⟨a, -, ho⟩ := ho
    rcases a with _ | ⟨⟨z₁, e⟩, h₁⟩
    · rw [OracleAdv.run_ret, PMF.support_pure, Set.mem_singleton_iff] at ho
      subst ho
      cases hos
    · obtain ⟨v', s'', l', hrun, hI'⟩ := run_hEv Sch IP h0 GB U UT OF x₀ dt L ks m K f hOF hm hI e
        fun v' s' lk => .rand (Z.obs z₁ (((cnNext Δ q (reqJ j e)).2.1, v'), lk) h₁)
          fun o' => match o' with
            | none => .ret none
            | some (z₂, h₂) =>
              hLoop Sch IP h0 GB U UT OF x₀ dt L ks m K Δ Z r z₂ h₂ (log ++ [e])
                (phaseNext j e) v' (cnNext Δ q (reqJ j e)).1 s'
      dsimp only at ho
      rw [hrun, OracleAdv.run_rand, PMF.mem_support_bind_iff] at ho
      obtain ⟨a', -, ho⟩ := ho
      rcases a' with _ | ⟨z₂, h₂⟩
      · rw [OracleAdv.run_ret, PMF.support_pure, Set.mem_singleton_iff] at ho
        subst ho
        cases hos
      · exact ih z₂ h₂ _ _ _ _ _ _ hI' o ho fl s' hos

/-- After the query of the genesis block, the initial view, state and log of queries of the hash
program satisfy the invariant for the empty log. -/
theorem hInvE_init :
    HInvE Sch IP h0 GB U UT OF x₀ dt L ks K f [] 0
      (viewO IP h0 GB U UT OF x₀ dt L ks initView
        (PoSNSB.x₀ IP h0 GB U L (OF.toAdvFamily.at fun _ => x₀), fun _ => f (encB Hz GB)))
      (PoSNSB.x₀ IP h0 GB U L (OF.toAdvFamily.at fun _ => x₀), fun _ => f (encB Hz GB))
      [encB Hz GB] := by
  have hx := hInv_x₀ Sch IP h0 GB U (txOf dt ([] : List (LogEvOf X Tx Hash np Hz))) L ks
    (OF.atO (scriptOfD x₀ ([] : List (LogEvOf X Tx Hash np Hz)))) f
  refine ⟨rfl, ?_, ?_, hx, fun b hb => ?_⟩
  · rw [viewO_eq_vNext IP h0 GB U UT OF x₀ dt L ks f
      (txOf dt ([] : List (LogEvOf X Tx Hash np Hz)))
      (scriptOfD x₀ ([] : List (LogEvOf X Tx Hash np Hz))) _ _ rfl
      fun p t ht b hb => hx.tbl b (hx.hist.state p t ht b hb)]
    exact (congrArg _ (N0_eq_emb Sch IP h0 GB U (txOf dt ([] : List (LogEvOf X Tx Hash np Hz)))
      L ks (OF.toAdvFamily.at (scriptOfD x₀ ([] : List (LogEvOf X Tx Hash np Hz)))) false
      f).symm).trans
      (viewE_zero (Protocol.ofUniform (Hz := Hz) IP h0 GB U dt) Sch OF.toAdvFamily x₀ dt
        (TreeFamily.ofUniform UT) K (uSeed L ks f) []).symm
  · rw [Nat.zero_min]
    exact (N0_eq_emb Sch IP h0 GB U (txOf dt ([] : List (LogEvOf X Tx Hash np Hz))) L ks
      (OF.toAdvFamily.at (scriptOfD x₀ ([] : List (LogEvOf X Tx Hash np Hz)))) false f).symm
  · have : b = GB := by simpa [PoSNSB.x₀] using hb
    rw [this]
    exact List.mem_singleton_self _

/-- **The evaluation of the hash program of an environment.** For an oracle adversary family
whose actions do not sample and whose evaluated calls output at most `m` messages, the final log
returned by the hash program `hashProgE` run against `logOracle f` from the empty log has the
distribution of the final log `finalLog` of the run of the environment `Z` from its heap against
`chainSimω` for the protocol with uniform tree types `U` and transaction selection `dt`, the
family `OF.toAdvFamily`, the tree family `TreeFamily.ofUniform UT` and the seed with leader
string `L`, oracle `f` and key pairs `ks`. -/
theorem run_hashProgE_map (hOF : OF.NoRand) (hm : ∀ σ, (OF.atO σ).toAdversary.OutputBound m)
    {ζ : Type} (Z : Env (Strat ζ (EnvEv Tx Hash np Hz X) (EnvOut Tx Hash np)) ζ) :
    (OracleAdv.run (OracleAdv.logOracle f) (hashProgE Sch IP h0 GB U UT OF x₀ dt L ks m K Δ Z)
        []).map (fun o => o.1.map Prod.fst) =
      (finalLog (Protocol.ofUniform (Hz := Hz) IP h0 GB U dt) Sch OF.toAdvFamily x₀ dt
        (TreeFamily.ofUniform UT) K Δ (uSeed L ks f) Z.input Z.heap).map
        (Option.map Prod.fst) := by
  rw [hashProgE, OracleAdv.run_query, OracleAdv.logOracle, PMF.pure_bind]
  refine (run_hLoop_map Sch IP h0 GB U UT OF x₀ dt L ks m K Δ f hOF hm Z.input Z.input.rounds
    Z.input.init Z.heap (chainSimω (Protocol.ofUniform (Hz := Hz) IP h0 GB U dt) Sch
      OF.toAdvFamily x₀ dt (TreeFamily.ofUniform UT) K Δ (uSeed L ks f)).init false _ _ _ rfl
    (hInvE_init Sch IP h0 GB U UT OF x₀ dt L ks K f)).trans ?_
  simp only [finalLog, run, SPComp.map, SPComp.bind, SPComp.pure, SDistr.bind, SDistr.pure,
    PMF.map_bind]
  rw [← PMF.bind_pure_comp]
  congr 1
  funext o
  rcases o with _ | ⟨c, h'⟩
  · simp only [Function.comp_apply, Option.map_none, SDistr.fail, PMF.pure_map]
  · simp only [Function.comp_apply, Option.map_some, PMF.pure_map]

/-- **The hash program of an environment logs the history.** For an oracle adversary family
whose actions do not sample and whose evaluated calls output at most `m` messages, every outcome
of the run of `hashProgE` against `logOracle f` from the empty log that returns the final log
`fl` and the state `s` has the hash-free part of `s` embedding over `f` into phase `K` of the
execution of `fl` with the family `OF.toAdvFamily`, and logs the encoding of every block of the
genesis block and the history of that phase. -/
theorem encB_mem_hashProgE (hOF : OF.NoRand) (hm : ∀ σ, (OF.atO σ).toAdversary.OutputBound m)
    {ζ : Type} (Z : Env (Strat ζ (EnvEv Tx Hash np Hz X) (EnvOut Tx Hash np)) ζ)
    (o : Option (List (LogEvOf X Tx Hash np Hz) × HStE Hz IP h0 GB U S L) ×
      List (BlockDom Tx Hash np Hz))
    (ho : o ∈ (OracleAdv.run (OracleAdv.logOracle f)
      (hashProgE Sch IP h0 GB U UT OF x₀ dt L ks m K Δ Z) []).support)
    (fl : List (LogEvOf X Tx Hash np Hz)) (s : HStE Hz IP h0 GB U S L)
    (hos : o.1 = some (fl, s)) :
    emb IP h0 GB U (txOf dt fl) L ks (OF.toAdvFamily.at (scriptOfD x₀ fl)) f s.1 =
        sTrace Sch ((Protocol.ofUniform (Hz := Hz) IP h0 GB U dt).withTx (txOf dt fl))
          (uSeed L ks f) (OF.toAdvFamily.at (scriptOfD x₀ fl)) false K ∧
      letI := leaderParams IP h0 L
      letI : BlockParameters Tx Hash (Fin np) := ⟨GB, fun b => f (encB Hz b)⟩
      ∀ b ∈ block_hist_gb (sTrace Sch ((Protocol.ofUniform (Hz := Hz) IP h0 GB U dt).withTx
          (txOf dt fl)) (uSeed L ks f) (OF.toAdvFamily.at (scriptOfD x₀ fl)) false K),
        encB Hz b ∈ o.2 := by
  rw [hashProgE, OracleAdv.run_query, OracleAdv.logOracle, PMF.pure_bind] at ho
  obtain ⟨h1, h2⟩ := run_hLoop_support Sch IP h0 GB U UT OF x₀ dt L ks m K Δ f hOF hm Z.input
    Z.input.rounds Z.input.init Z.heap [] 0 _ _ _ _
    (hInvE_init Sch IP h0 GB U UT OF x₀ dt L ks K f) o ho fl s hos
  refine ⟨h1, ?_⟩
  rw [← h1]
  exact h2

end Eval

/-! ### The query bound -/

section Bound

variable {qc : ℕ}

theorem isQueryBound_phaseO (hOF : OF.Bounded qc m) (log : List (LogEvOf X Tx Hash np Hz))
    (s : HStE Hz IP h0 GB U S L) :
    (phaseO Sch IP h0 GB U OF x₀ dt L ks m log s).IsQueryBound (IP.length * (qc + m + 1)) :=
  isQueryBound_hPhase Sch IP h0 GB U (txOf dt log) L ks (OF.atO (scriptOfD x₀ log)) m
    (hOF _).1.1 (hOF _).1.2 s

theorem isQueryBound_phasesO (hOF : OF.Bounded qc m) (log : List (LogEvOf X Tx Hash np Hz))
    (k : ℕ) (s : HStE Hz IP h0 GB U S L) :
    (phasesO Sch IP h0 GB U OF x₀ dt L ks m log k s).IsQueryBound
      (k * (IP.length * (qc + m + 1))) := by
  induction k with
  | zero => trivial
  | succ k ih =>
    refine (OracleAdv.isQueryBound_bind ih
      (isQueryBound_phaseO Sch IP h0 GB U OF x₀ dt L ks m hOF log)).mono (le_of_eq ?_)
    ring

theorem isQueryBound_hEv (hOF : OF.Bounded qc m) {β : Type}
    (log : List (LogEvOf X Tx Hash np Hz)) (j : ℕ)
    (v : TreeView (Option (Fin np)) (Block Tx Hash (Fin np))) (s : HStE Hz IP h0 GB U S L)
    (e : EnvEv Tx Hash np Hz X)
    {k : TreeView (Option (Fin np)) (Block Tx Hash (Fin np)) → HStE Hz IP h0 GB U S L →
      Option Hash → OracleAdv (BlockDom Tx Hash np Hz) Hash β} {N : ℕ}
    (hk : ∀ v s lk, (k v s lk).IsQueryBound (N + (K - phaseNext j e) * (IP.length * (qc + m + 1)))) :
    (hEv Sch IP h0 GB U UT OF x₀ dt L ks m K log j v s e k).IsQueryBound
      (N + 1 + (K - j) * (IP.length * (qc + m + 1))) := by
  rcases e with e | (x | d)
  · exact (hk _ _ _).mono (by simp [phaseNext])
  · simp only [hEv]
    split
    · next hj =>
      refine (OracleAdv.isQueryBound_bind
        (isQueryBound_phaseO Sch IP h0 GB U OF x₀ dt L ks m hOF _ s)
        fun s' => hk _ _ _).mono ?_
      simp only [phaseNext]
      obtain ⟨t, ht⟩ : ∃ t, K - j = t + 1 := ⟨K - j - 1, by omega⟩
      rw [ht, show K - (j + 1) = t by omega]
      nlinarith
    · next hj =>
      refine (hk _ _ _).mono ?_
      simp only [phaseNext]
      rw [show K - (j + 1) = 0 by omega, show K - j = 0 by omega]
      omega
  · exact OracleAdv.IsQueryBound.mono (m := N + (K - j) * (IP.length * (qc + m + 1)) + 1)
      (fun r => (hk _ _ _).mono (by simp [phaseNext])) (by omega)

theorem isQueryBound_hLoop (hOF : OF.Bounded qc m) {ζ : Type}
    (Z : Strat ζ (EnvEv Tx Hash np Hz X) (EnvOut Tx Hash np)) (r : ℕ) :
    ∀ z h log j v q s,
      (hLoop Sch IP h0 GB U UT OF x₀ dt L ks m K Δ Z r z h log j v q s).IsQueryBound
        (r + (K - j) * (IP.length * (qc + m + 1))) := by
  induction r with
  | zero =>
    intro z h log j v q s
    exact (OracleAdv.isQueryBound_bind (n := 0)
      (isQueryBound_phasesO Sch IP h0 GB U OF x₀ dt L ks m hOF log (K - j) s)
      fun _ => by trivial).mono (by omega)
  | succ r ih =>
    intro z h log j v q s o
    rcases o with _ | ⟨⟨z₁, e⟩, h₁⟩
    · trivial
    · refine isQueryBound_hEv Sch IP h0 GB U UT OF x₀ dt L ks m K hOF log j v s e
        fun v' s' lk o' => ?_
      rcases o' with _ | ⟨z₂, h₂⟩
      · trivial
      · exact ih _ _ _ _ _ _ _

/-- **The query bound of the hash program of an environment.** For an oracle adversary family
whose calls ask at most `qc` queries and output at most `m` messages, the hash program asks at
most `1 + Z.input.rounds + K * (|IP| * (qc + m + 1))` queries: the genesis block, at most one
query per hash input of the environment, and at most `|IP| * (qc + m + 1)` queries in each of at
most `K` phases. -/
theorem isQueryBound_hashProgE (hOF : OF.Bounded qc m) {ζ : Type}
    (Z : Env (Strat ζ (EnvEv Tx Hash np Hz X) (EnvOut Tx Hash np)) ζ) :
    (hashProgE Sch IP h0 GB U UT OF x₀ dt L ks m K Δ Z).IsQueryBound
      (1 + Z.input.rounds + K * (IP.length * (qc + m + 1))) := by
  refine OracleAdv.IsQueryBound.mono
    (m := Z.input.rounds + (K - 0) * (IP.length * (qc + m + 1)) + 1)
    (fun r => isQueryBound_hLoop Sch IP h0 GB U UT OF x₀ dt L ks m K Δ hOF Z.input _ _ _ _ _ _ _
      _) (by rw [Nat.sub_zero]; omega)

end Bound

end HashProgE

/-! ## The collision term in the random-oracle model -/

section ROMBound

open scoped ENNReal

variable {Tx Hash : Type} [DecidableEq Tx] [DecidableEq Hash] {np : ℕ} [Corruption (Fin np)]
  {n Hz : ℕ} {PK SK Sig : Type}
  (Sch : PSigScheme (Block Tx Hash (Fin np)) PK SK Sig) [Sch.Deterministic]
  (IP : List (Fin np)) (h0 : Fin np) (GB : Block Tx Hash (Fin np))
  (U : (L : Fin n → Option (Fin np)) → Fin np →
    @UTreeType Tx Hash (Fin np) (leaderParams IP h0 L) GB)
  (UT : (L : Fin n → Option (Fin np)) → @UTreeType Tx Hash (Fin np) (leaderParams IP h0 L) GB)
  {X S : Type} (OF : OAdvFamily X S Tx Hash np n Hz PK Sig) (x₀ : X) (dt : Slot → Fin np → Tx)
  [Fintype Tx] [Fintype Hash] [Nonempty Hash]

/-- The collision term of `collFinderE_advantage_rom_le` for an oracle adversary family whose
actions do not sample. -/
theorem collFinderE_advantage_rom_le_of_noRand {qc m : ℕ} (hnr : OF.NoRand)
    (hOF : OF.Bounded qc m) (μ : PMF (Option (Fin np))) (W K Δ : ℕ) {ζ : Type}
    (Z : Env (Strat ζ (EnvEv Tx Hash np Hz X) (EnvOut Tx Hash np)) ζ) :
    CR_Search_Advantage (HashScheme.randomFun (BlockDom Tx Hash np Hz) Hash)
        (collFinderE (Protocol.ofUniform (Hz := Hz) IP h0 GB U dt) Sch OF.toAdvFamily x₀ dt
          (TreeFamily.ofUniform UT) (HashScheme.randomFun (BlockDom Tx Hash np Hz) Hash)
          (HashScheme.Codec.id _) μ W K Δ Z) ≤
      (((1 + Z.input.rounds + K * (IP.length * (qc + m + 1))) *
          (1 + Z.input.rounds + K * (IP.length * (qc + m + 1)) - 1) / 2 : ℕ) : ℝ≥0∞) /
        Fintype.card Hash := by
  have hm : ∀ σ, (OF.atO σ).toAdversary.OutputBound m := fun σ => (hOF σ).2
  have hq : ∀ c : (Fin n → Option (Fin np)) × (Fin np → PK × SK),
      (OracleAdv.collisionGame (hashProgE Sch IP h0 GB U UT OF x₀ dt c.1 c.2 m K Δ Z)).toOuterMeasure
        {p | OracleAdv.QueryCollision p.1 p.2.2} ≤
      (((1 + Z.input.rounds + K * (IP.length * (qc + m + 1))) *
          (1 + Z.input.rounds + K * (IP.length * (qc + m + 1)) - 1) / 2 : ℕ) : ℝ≥0∞) /
        Fintype.card Hash := fun c =>
    OracleAdv.prob_oracleCollision_le _ _
      (isQueryBound_hashProgE Sch IP h0 GB U UT OF x₀ dt c.1 c.2 m K Δ hOF Z)
  unfold CR_Search_Advantage CR_Search_Game collFinderE collFinderG
  rw [show SPComp.sample (HashScheme.randomFun (BlockDom Tx Hash np Hz) Hash).Key =
    sampleFrom (ofPMF (PMF.uniformOfFintype _)) from rfl]
  simp only [SPComp.monad_bind_eq, SPComp.bind_assoc, SPComp.pure_bind]
  rw [prTrue_bind_sampleFrom]
  simp_rw [prTrue_bind_sampleFrom, ofPMF_apply_some]
  have hkey : ∀ (f : BlockDom Tx Hash np Hz → Hash)
      (c : (Fin n → Option (Fin np)) × (Fin np → PK × SK))
      (g : List (LogEvOf X Tx Hash np Hz) → Bool),
      (∀ o ∈ (OracleAdv.run (OracleAdv.logOracle f)
          (hashProgE Sch IP h0 GB U UT OF x₀ dt c.1 c.2 m K Δ Z) []).support,
        ∀ fl s, o.1 = some (fl, s) → g fl = true → OracleAdv.QueryCollision f o.2) →
      prTrue (SPComp.bind (SPComp.atHeap Z.heap
          (finalLog (Protocol.ofUniform (Hz := Hz) IP h0 GB U dt) Sch OF.toAdvFamily x₀ dt
            (TreeFamily.ofUniform UT) K Δ (uSeed c.1 c.2 f) Z.input))
          fun log => SPComp.pure (g log)) Heap.empty ≤
        (OracleAdv.run (OracleAdv.logOracle f)
          (hashProgE Sch IP h0 GB U UT OF x₀ dt c.1 c.2 m K Δ Z) []).toOuterMeasure
          {o | OracleAdv.QueryCollision f o.2} := by
    intro f c g hg
    have hmap := run_hashProgE_map Sch IP h0 GB U UT OF x₀ dt c.1 c.2 m K Δ f hnr hm Z
    calc _ = ((finalLog (Protocol.ofUniform (Hz := Hz) IP h0 GB U dt) Sch OF.toAdvFamily x₀ dt
            (TreeFamily.ofUniform UT) K Δ (uSeed c.1 c.2 f) Z.input Z.heap).map
              (Option.map Prod.fst)).toOuterMeasure {x | ∃ fl, x = some fl ∧ g fl = true} := by
          rw [prTrue_bind_atHeap, ForkingLemma.prTrue_bind_eq_weighted,
            PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_apply]
          refine tsum_congr fun p => ?_
          rcases p with _ | ⟨log, h'⟩
          · simp
          · dsimp only
            rw [ForkingLemma.prTrue_pure_bool]
            by_cases hgl : g log = true <;> simp [Set.indicator, hgl]
      _ = _ := by rw [← hmap]
      _ ≤ _ := by
          rw [PMF.toOuterMeasure_map_apply]
          refine PMF.toOuterMeasure_mono _ ?_
          rintro o ⟨⟨fl, hfl, hgfl⟩, ho⟩
          dsimp only at hfl
          rcases ho1 : o.1 with _ | ⟨fl', s⟩
          · rw [ho1] at hfl; cases hfl
          · rw [ho1] at hfl
            cases hfl
            exact hg o ho _ s ho1 hgfl
  have hwin : ∀ (f : BlockDom Tx Hash np Hz → Hash)
      (c : (Fin n → Option (Fin np)) × (Fin np → PK × SK)),
      ∀ o ∈ (OracleAdv.run (OracleAdv.logOracle f)
          (hashProgE Sch IP h0 GB U UT OF x₀ dt c.1 c.2 m K Δ Z) []).support,
        ∀ fl s, o.1 = some (fl, s) →
          coinsCollision (collFind Sch
            ((Protocol.ofUniform (Hz := Hz) IP h0 GB U dt).withTx (txOf dt fl))
            (OF.toAdvFamily.at (scriptOfD x₀ fl))
            (HashScheme.randomFun (BlockDom Tx Hash np Hz) Hash) (HashScheme.Codec.id _) K)
            f c = true → OracleAdv.QueryCollision f o.2 := by
    intro f c o ho fl s hos hc
    have hmem := (encB_mem_hashProgE Sch IP h0 GB U UT OF x₀ dt c.1 c.2 m K Δ f hnr hm Z o ho
      fl s hos).2
    simp only [coinsCollision, decide_eq_true_eq] at hc
    obtain ⟨hh, hne⟩ := hc
    cases hp : collPair Sch ((Protocol.ofUniform (Hz := Hz) IP h0 GB U dt).withTx (txOf dt fl))
        (OF.toAdvFamily.at (scriptOfD x₀ fl))
        (⟨c.1, (HashScheme.Codec.id
          (HashScheme.randomFun (BlockDom Tx Hash np Hz) Hash)).hashOn f, c.2⟩ :
            Seed Tx Hash np n Hz PK SK) K with
    | none =>
      simp only [collFind, hp] at hne
      exact absurd rfl hne
    | some bb =>
      obtain ⟨b, b'⟩ := bb
      obtain ⟨hb, hb', -, -⟩ := findColl_some hp
      simp only [collFind, hp] at hne hh
      exact ⟨_, hmem b hb, _, hmem b' hb', hne, hh⟩
  refine le_trans (ENNReal.tsum_le_tsum fun f => mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun c =>
    mul_le_mul' le_rfl (hkey f c _ (hwin f c)))) ?_
  simp_rw [← ENNReal.tsum_mul_left]
  rw [ENNReal.tsum_comm]
  refine le_trans (ENNReal.tsum_le_tsum fun c => le_of_eq ?_)
    ((ENNReal.tsum_le_tsum fun c => mul_le_mul'
      (le_refl (collCoins Sch (Protocol.ofUniform (Hz := Hz) IP h0 GB U dt) μ W c)) (hq c)).trans
      ?_)
  · rw [OracleAdv.collisionGame, PMF.toOuterMeasure_bind_apply, ← ENNReal.tsum_mul_left]
    refine tsum_congr fun f => ?_
    rw [PMF.toOuterMeasure_map_apply, mul_left_comm]
    rfl
  · rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

/-- **The collision term against an environment in the random-oracle model.** For a protocol
with uniform tree types `U`, the tree family of uniform tree types `UT`, an oracle adversary
family `OF` whose calls ask at most `qc` queries and output at most `m` messages, and every
environment `Z`, the collision finder `collFinderE … Z` of the family `OF.toAdvFamily` against
the random function `HashScheme.randomFun` with the identity codec has collision-search
advantage at most the birthday bound `qT (qT - 1) / 2 / |Hash|` with
`qT = 1 + Z.input.rounds + K (|IP| (qc + m + 1))`, the query bound of the hash program
`hashProgE`. -/
theorem collFinderE_advantage_rom_le {qc m : ℕ} (hOF : OF.Bounded qc m)
    (μ : PMF (Option (Fin np))) (W K Δ : ℕ) {ζ : Type}
    (Z : Env (Strat ζ (EnvEv Tx Hash np Hz X) (EnvOut Tx Hash np)) ζ) :
    CR_Search_Advantage (HashScheme.randomFun (BlockDom Tx Hash np Hz) Hash)
        (collFinderE (Protocol.ofUniform (Hz := Hz) IP h0 GB U dt) Sch OF.toAdvFamily x₀ dt
          (TreeFamily.ofUniform UT) (HashScheme.randomFun (BlockDom Tx Hash np Hz) Hash)
          (HashScheme.Codec.id _) μ W K Δ Z) ≤
      (((1 + Z.input.rounds + K * (IP.length * (qc + m + 1))) *
          (1 + Z.input.rounds + K * (IP.length * (qc + m + 1)) - 1) / 2 : ℕ) : ℝ≥0∞) /
        Fintype.card Hash := by
  rw [← OF.toAdvFamily_derand]
  exact collFinderE_advantage_rom_le_of_noRand Sch IP h0 GB U UT OF.derand x₀ dt
    OF.noRand_derand hOF.derand μ W K Δ Z

/-- **The failure bound against an environment in the random-oracle model.** For the protocol
with uniform tree types, the tree family `TreeFamily.ofUniform UT` and an oracle adversary
family `OF` with `OF.Bounded qc m`, the failure bound `posFailE … Z` of the family
`OF.toAdvFamily` against `HashScheme.randomFun` with the identity codec is at most
`slotBound (kindLaw μ) n d w ε + qT (qT - 1) / 2 / |Hash| +
∑ᵢ eufcmaAdvantage Sch.toSigScheme (toEUFAdversary (forgerE … Z i))` with
`qT = 1 + Z.input.rounds + K (|IP| (qc + m + 1))`. -/
theorem posFailE_rom_le {qc m : ℕ} (hOF : OF.Bounded qc m) (μ : PMF (Option (Fin np)))
    (W K Δ d w : ℕ) (ε : ℝ) {ζ : Type}
    (Z : Env (Strat ζ (EnvEv Tx Hash np Hz X) (EnvOut Tx Hash np)) ζ) :
    posFailE (Protocol.ofUniform (Hz := Hz) IP h0 GB U dt) Sch OF.toAdvFamily x₀ dt
        (TreeFamily.ofUniform UT) (HashScheme.randomFun (BlockDom Tx Hash np Hz) Hash)
        (HashScheme.Codec.id _) μ W K Δ d w ε Z ≤
      slotBound (kindLaw μ) n d w ε +
        (((1 + Z.input.rounds + K * (IP.length * (qc + m + 1))) *
          (1 + Z.input.rounds + K * (IP.length * (qc + m + 1)) - 1) / 2 : ℕ) : ℝ≥0∞) /
          Fintype.card Hash +
        ∑ i : Fin np, eufcmaAdvantage Sch.toSigScheme
          (toEUFAdversary (forgerE (Protocol.ofUniform (Hz := Hz) IP h0 GB U dt) Sch
            OF.toAdvFamily x₀ dt (TreeFamily.ofUniform UT)
            (HashScheme.randomFun (BlockDom Tx Hash np Hz) Hash) (HashScheme.Codec.id _) μ W K Δ
            Z i)) :=
  add_le_add_left (add_le_add_right
    (collFinderE_advantage_rom_le Sch IP h0 GB U UT OF x₀ dt hOF μ W K Δ Z) _) _

open Classical in
/-- **Security of PoS-NSB against an environment in the random-oracle model.** For the protocol
with uniform tree types `U`, the tree family `TreeFamily.ofUniform UT`, an oracle adversary
family `OF` whose calls ask at most `qc` queries and output at most `m` messages, the random
function `HashScheme.randomFun` with the identity codec and the hypotheses of
`pos_nsb_securityE`, the probability that chain growth, chain quality, common prefix or the
honest tip fails for the first `K` phases of the execution of the final log of the run of the
environment `Z` against `chainSimω` is at most `slotBound (kindLaw μ) n d w ε +
qT (qT - 1) / 2 / |Hash| + ∑ᵢ eufcmaAdvantage Sch.toSigScheme (toEUFAdversary (forgerE … Z i))`
with `qT = 1 + Z.input.rounds + K (|IP| (qc + m + 1))`. -/
theorem pos_nsb_securityE_rom {qc m : ℕ} (hOF : OF.Bounded qc m)
    (hP : ProtocolHyp (Protocol.ofUniform (Hz := Hz) IP h0 GB U dt))
    (hTree : (TreeFamily.ofUniform (P := Protocol.ofUniform (Hz := Hz) IP h0 GB U dt) UT).Longest)
    (μ : PMF (Option (Fin np))) (W K Δ d w : ℕ) (ε : ℝ)
    (hwd : w ≤ d) (hWn : W + d ≤ n) (hn : K + 2 ≤ n) (hHz : K + 1 ≤ Hz)
    (hε : 0 ≤ ε) (hγ : 2 * pA (kindLaw μ) ≤ pH (kindLaw μ))
    (hw : (w : ℝ) ≤ d * (pH (kindLaw μ) - pA (kindLaw μ)))
    (h3 : (3 : ℝ) ≤ d * (pH (kindLaw μ) - 2 * pA (kindLaw μ))) {ζ : Type}
    (Z : Env (Strat ζ (EnvEv Tx Hash np Hz X) (EnvOut Tx Hash np)) ζ) :
    ∑' ω, seedDist Sch (HashScheme.randomFun (BlockDom Tx Hash np Hz) Hash)
        (HashScheme.Codec.id _) μ h0 W n ω *
        prFinal (chainSimω (Protocol.ofUniform (Hz := Hz) IP h0 GB U dt) Sch OF.toAdvFamily x₀ dt
            (TreeFamily.ofUniform UT) K Δ ω)
          (fun t => decide (¬GoodE (Protocol.ofUniform (Hz := Hz) IP h0 GB U dt) Sch
            OF.toAdvFamily x₀ dt (TreeFamily.ofUniform UT) (kindLaw μ) K d w ε ω t.1.2.1)) Z ≤
      slotBound (kindLaw μ) n d w ε +
        (((1 + Z.input.rounds + K * (IP.length * (qc + m + 1))) *
          (1 + Z.input.rounds + K * (IP.length * (qc + m + 1)) - 1) / 2 : ℕ) : ℝ≥0∞) /
          Fintype.card Hash +
        ∑ i : Fin np, eufcmaAdvantage Sch.toSigScheme
          (toEUFAdversary (forgerE (Protocol.ofUniform (Hz := Hz) IP h0 GB U dt) Sch
            OF.toAdvFamily x₀ dt (TreeFamily.ofUniform UT)
            (HashScheme.randomFun (BlockDom Tx Hash np Hz) Hash) (HashScheme.Codec.id _) μ W K Δ
            Z i)) :=
  (pos_nsb_securityE _ Sch _ x₀ dt _ _ _ hP hTree μ W K Δ d w ε hwd hWn hn hHz hε hγ hw h3
    Z).trans (posFailE_rom_le Sch IP h0 GB U UT OF x₀ dt hOF μ W K Δ d w ε Z)

/-- **PoS-NSB driven by an environment realizes `F_Chain` in the random-oracle model.** Under
the hypotheses of `chain_realizesE`, for the protocol with uniform tree types `U`, the tree
family `TreeFamily.ofUniform UT`, an oracle adversary family `OF` with `OF.Bounded qc m` and
the random function `HashScheme.randomFun` with the identity codec, every environment `Z` has
advantage at most `slotBound (kindLaw μ) n d w ε + qT (qT - 1) / 2 / |Hash| +
∑ᵢ eufcmaAdvantage Sch.toSigScheme (toEUFAdversary (forgerE … Z i))` with
`qT = 1 + Z.input.rounds + K (|IP| (qc + m + 1))`. -/
theorem chain_realizesE_rom {qc m : ℕ} (hOF : OF.Bounded qc m)
    (hP : ProtocolHyp (Protocol.ofUniform (Hz := Hz) IP h0 GB U dt))
    (hTree : (TreeFamily.ofUniform (P := Protocol.ofUniform (Hz := Hz) IP h0 GB U dt) UT).Longest)
    (μ : PMF (Option (Fin np))) (W K d w : ℕ) (ε : ℝ) (Δ : ℕ)
    (hwd : w ≤ d) (hWn : W + d ≤ n) (hn : K + 2 ≤ n) (hHz : K + 1 ≤ Hz)
    (hε : 0 ≤ ε) (hγ : 2 * pA (kindLaw μ) ≤ pH (kindLaw μ))
    (hw : (w : ℝ) ≤ d * (pH (kindLaw μ) - pA (kindLaw μ)))
    (h3 : (3 : ℝ) ≤ d * (pH (kindLaw μ) - 2 * pA (kindLaw μ)))
    (hGB : GB.sl = 0) (hw4 : K + 1 < d + 2 ∨ 4 ≤ w) :
    RealizesBound (chainRealE (Protocol.ofUniform (Hz := Hz) IP h0 GB U dt) Sch OF.toAdvFamily
        x₀ dt (TreeFamily.ofUniform UT) (HashScheme.randomFun (BlockDom Tx Hash np Hz) Hash)
        (HashScheme.Codec.id _) K μ W Δ)
      (ideal (chainFE (Protocol.ofUniform (Hz := Hz) IP h0 GB U dt) Δ (kindLaw μ) d w ε)
        (chainSimE (Protocol.ofUniform (Hz := Hz) IP h0 GB U dt) Sch OF.toAdvFamily x₀ dt
          (TreeFamily.ofUniform UT) (HashScheme.randomFun (BlockDom Tx Hash np Hz) Hash)
          (HashScheme.Codec.id _) K μ W Δ))
      (fun _ Z => slotBound (kindLaw μ) n d w ε +
        (((1 + Z.input.rounds + K * (IP.length * (qc + m + 1))) *
          (1 + Z.input.rounds + K * (IP.length * (qc + m + 1)) - 1) / 2 : ℕ) : ℝ≥0∞) /
          Fintype.card Hash +
        ∑ i : Fin np, eufcmaAdvantage Sch.toSigScheme
          (toEUFAdversary (forgerE (Protocol.ofUniform (Hz := Hz) IP h0 GB U dt) Sch
            OF.toAdvFamily x₀ dt (TreeFamily.ofUniform UT)
            (HashScheme.randomFun (BlockDom Tx Hash np Hz) Hash) (HashScheme.Codec.id _) μ W K Δ
            Z i))) :=
  (chain_realizesE _ Sch _ x₀ dt _ _ _ hP hTree μ W K d w ε Δ hwd hWn hn hHz hε hγ hw h3 hGB
    hw4).mono fun _ Z => posFailE_rom_le Sch IP h0 GB U UT OF x₀ dt hOF μ W K Δ d w ε Z

open CatCryptCore.Consensus.UC.Stack CatCryptCore.Consensus.Finality FFG
  CatCryptCore.Consensus.UC.FFGGadget in
/-- **FFG over PoS-NSB driven by an environment realizes `F_FinTree` in the random-oracle
model.** Under the hypotheses of `stack_realizesE`, for the protocol with uniform tree types
`U`, the tree family `TreeFamily.ofUniform UT`, an oracle adversary family `OF` with
`OF.Bounded qc m` and the random function `HashScheme.randomFun` with the identity codec, every
environment `Z` of the stack has advantage at most `slotBound (kindLaw μ) n d w ε +
qT (qT - 1) / 2 / |Hash| + ∑ᵢ eufcmaAdvantage Sch.toSigScheme (toEUFAdversary (forgerE … Z' i))`
at the environment `Z' = (stackHybridE …).reduceEnv Z` of the PoS-NSB layer, with
`qT = 1 + Z'.input.rounds + K (|IP| (qc + m + 1))`. -/
theorem stack_realizesE_rom {qc m : ℕ} (hOF : OF.Bounded qc m)
    (hP : ProtocolHyp (Protocol.ofUniform (Hz := Hz) IP h0 GB U dt))
    (hTree : (TreeFamily.ofUniform (P := Protocol.ofUniform (Hz := Hz) IP h0 GB U dt) UT).Longest)
    (μ : PMF (Option (Fin np))) (W K d w : ℕ) (ε : ℝ) (Δ : ℕ)
    (c : Cfg (Option (Fin np)) (Block Tx Hash (Fin np)))
    (exF : TreeView (Option (Fin np)) (Block Tx Hash (Fin np)))
    (hwd : w ≤ d) (hWn : W + d ≤ n) (hn : K + 2 ≤ n) (hHz : K + 1 ≤ Hz)
    (hε : 0 ≤ ε) (hγ : 2 * pA (kindLaw μ) ≤ pH (kindLaw μ))
    (hw : (w : ℝ) ≤ d * (pH (kindLaw μ) - pA (kindLaw μ)))
    (h3 : (3 : ℝ) ≤ d * (pH (kindLaw μ) - 2 * pA (kindLaw μ)))
    (hGB : GB.sl = 0) (hw4 : K + 1 < d + 2 ∨ 4 ≤ w)
    (hT : c.T = slotTree (Protocol.ofUniform (Hz := Hz) IP h0 GB U dt))
    (hsl : c.slot = Block.sl) (hH : ∀ o, o ∈ c.H ↔ honestP o)
    (hcut : c.cut = slotCut Block.sl d) (hΔ : 1 ≤ c.Δ) (hE : 1 ≤ c.E) (hv₀ : c.v₀ ∈ c.H)
    (hstart : c.start = 2 * c.E + (d + 2) + d)
    (hA : 3 * stake c.w (Finset.univ \ c.H) < totalStake c.w) :
    RealizesBound (stackRealE (Protocol.ofUniform (Hz := Hz) IP h0 GB U dt) Sch OF.toAdvFamily
        x₀ dt (TreeFamily.ofUniform UT) (HashScheme.randomFun (BlockDom Tx Hash np Hz) Hash)
        (HashScheme.Codec.id _) c K μ W Δ exF)
      (ideal (stackFE (Protocol.ofUniform (Hz := Hz) IP h0 GB U dt) Sch OF.toAdvFamily x₀ dt
          (TreeFamily.ofUniform UT) (HashScheme.randomFun (BlockDom Tx Hash np Hz) Hash)
          (HashScheme.Codec.id _) μ W K d w ε Δ c exF)
        (stackSimE (Protocol.ofUniform (Hz := Hz) IP h0 GB U dt) Sch OF.toAdvFamily x₀ dt
          (TreeFamily.ofUniform UT) (HashScheme.randomFun (BlockDom Tx Hash np Hz) Hash)
          (HashScheme.Codec.id _) μ W K d w ε Δ c exF))
      (fun _ Z =>
        let Z' := (stackHybridE (Protocol.ofUniform (Hz := Hz) IP h0 GB U dt) Sch OF.toAdvFamily
          x₀ dt (TreeFamily.ofUniform UT) (HashScheme.randomFun (BlockDom Tx Hash np Hz) Hash)
          (HashScheme.Codec.id _) c K μ W Δ exF).reduceEnv Z
        slotBound (kindLaw μ) n d w ε +
          (((1 + Z'.input.rounds + K * (IP.length * (qc + m + 1))) *
            (1 + Z'.input.rounds + K * (IP.length * (qc + m + 1)) - 1) / 2 : ℕ) : ℝ≥0∞) /
            Fintype.card Hash +
          ∑ i : Fin np, eufcmaAdvantage Sch.toSigScheme
            (toEUFAdversary (forgerE (Protocol.ofUniform (Hz := Hz) IP h0 GB U dt) Sch
              OF.toAdvFamily x₀ dt (TreeFamily.ofUniform UT)
              (HashScheme.randomFun (BlockDom Tx Hash np Hz) Hash) (HashScheme.Codec.id _) μ W K
              Δ Z' i))) :=
  (stack_realizesE _ Sch _ x₀ dt _ _ _ μ W K d w ε Δ c exF hP hTree hwd hWn hn hHz hε hγ hw h3
    hGB hw4 hT hsl hH hcut hΔ hE hv₀ hstart hA).mono fun _ _ =>
      posFailE_rom_le Sch IP h0 GB U UT OF x₀ dt hOF μ W K Δ d w ε _

end ROMBound

end CatCryptCore.Consensus.UC.ChainEnv
