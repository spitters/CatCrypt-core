/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OracleCollision
public import CatCryptCore.Consensus.UC.ChainEnv
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
-/

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

end CatCryptCore.Consensus.UC.ChainEnv
