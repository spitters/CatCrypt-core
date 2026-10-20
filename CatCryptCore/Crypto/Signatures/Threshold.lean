/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Signatures.EUFCMAPMF
public import CatCryptCore.Crypto.OracleAdversaryTimed
public import CatCryptCore.Crypto.SDist

/-!
# Threshold signatures: EUF-CMA from single-signer EUF-CMA

A threshold signature scheme (`ThresholdSigScheme`) over `n` parties generates a group
public key and one key share per party; its signing protocol returns the messages of the
honest parties seen by the adversary and a combined signature. Its EUF-CMA game
(`thresholdGame`) gives the adversary the public key and the shares of a corruption set
`C`, and answers signing queries by the protocol.

A share simulator (`ShareSimulator`) relative to a single-signer scheme `S` draws the
corrupted shares from the public key alone and the honest parties' messages from a
single-signer signature; a coupling of the key material states that the simulated keys
have the real distribution, and each simulated signing answer is at statistical distance
at most `δ` from the protocol's. The reduction `thresholdRed` runs the threshold
adversary against the single-signer signing oracle and simulates the honest parties.

## Main definitions

* `ThresholdSigScheme`, `ThresholdAdversary`, `thresholdGame`, `thresholdAdvantage`
* `ShareSimulator`, `ShareSimulatable` — share simulation at per-signature distance `δ`
* `thresholdRed` — the reduction to single-signer EUF-CMA
* `thresholdRed.timed` — its costed form over a costed adversary

## Main results

* `OracleProg.absDiff_runWith_le` — replacing the oracle of a program with at most `n`
  queries by one at distance `δ` changes the probability of `true` by at most `n * δ`
* `thresholdAdvantage_le` — `thresholdAdvantage T A ≤ eufcmaAdvantage S (thresholdRed sim A) + q * δ`
* `thresholdAdvantage_le_of_simulatable` — the same bound for every corruption set of
  fewer than `t` parties
* `thresholdRed.erase_timed`, `thresholdRed.timeBound_timed` — the costed reduction erases
  to the reduction and has time at most `1 + tK + T + q * (tV + 1)`

## References

* Gennaro, Jarecki, Krawczyk, Rabin — *Secure Distributed Key Generation for
  Discrete-Log Based Cryptosystems*, J. Cryptology 2007 (simulatability of threshold
  signing).
* Bellare, Crites, Komlo, Maller, Tessaro, Zhu — *Better than Advertised Security for
  Non-Interactive Threshold Signatures*, CRYPTO 2022.
-/

@[expose] public section

set_option autoImplicit false

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal

namespace CatCrypt.Crypto

namespace OracleProg

variable {I O L α : Type}

/-- Logging the answers of two oracles does not increase their distance. -/
theorem sdist_logging_le (o₁ o₂ : I → SPComp O) :
    sdist (logging o₁) (logging o₂) ≤ sdist o₁ o₂ := by
  refine iSup_le fun D => iSup_le fun i => iSup_le fun h₀ => ?_
  simp only [logging, SPComp.bind_assoc, SPComp.pure_bind]
  exact le_iSup₂_of_le (fun o => D (o, [(i, o)])) i (le_iSup_of_le h₀ le_rfl)

/-- **Oracle replacement.** Running a program with at most `n` queries against two
oracles at distance at most `δ`, followed by a common continuation, changes the
probability of `true` by at most `n * δ`. -/
theorem absDiff_runWith_le (o₁ o₂ : I → SPComp (O × List L)) {δ : ℝ≥0∞}
    (hδ : sdist o₁ o₂ ≤ δ) (p : OracleProg I O α) (n : ℕ)
    (hp : QueryCostLe (fun _ => 1) p n) (D : α × List L → SPComp Bool) (h₀ : Heap) :
    absDiff (prTrue (SPComp.bind (p.runWith o₁) D) h₀)
      (prTrue (SPComp.bind (p.runWith o₂) D) h₀) ≤ n * δ := by
  induction p generalizing n D h₀ with
  | pure a => simp
  | query i k ih =>
    obtain ⟨hle, hk⟩ := hp
    simp only [runWith_query, SPComp.bind_assoc, SPComp.pure_bind]
    calc _ ≤ absDiff (prTrue (SPComp.bind (o₁ i) fun ol =>
              SPComp.bind ((k ol.1).runWith o₁) fun al => D (al.1, ol.2 ++ al.2)) h₀)
            (prTrue (SPComp.bind (o₁ i) fun ol =>
              SPComp.bind ((k ol.1).runWith o₂) fun al => D (al.1, ol.2 ++ al.2)) h₀) +
          absDiff (prTrue (SPComp.bind (o₁ i) fun ol =>
              SPComp.bind ((k ol.1).runWith o₂) fun al => D (al.1, ol.2 ++ al.2)) h₀)
            (prTrue (SPComp.bind (o₂ i) fun ol =>
              SPComp.bind ((k ol.1).runWith o₂) fun al => D (al.1, ol.2 ++ al.2)) h₀) :=
          absDiff_triangle _ _ _
      _ ≤ ((n - 1 : ℕ) : ℝ≥0∞) * δ + δ := by
          gcongr
          · exact absDiff_bind_common _ _ _ _ _ fun ol h' =>
              ih ol.1 (n - 1) (hk ol.1) (fun al => D (al.1, ol.2 ++ al.2)) h'
          · refine le_trans ?_ hδ
            unfold sdist
            apply le_iSup₂_of_le (fun ol => SPComp.bind ((k ol.1).runWith o₂) fun al =>
              D (al.1, ol.2 ++ al.2)) i
            exact le_iSup_of_le h₀ le_rfl
      _ = n * δ := by
          have h1 : 1 ≤ n := hle
          rw [← add_one_mul, ← Nat.cast_add_one, Nat.sub_add_cancel h1]
  | lift c k ih =>
    simp only [runWith_lift, SPComp.bind_assoc]
    exact absDiff_bind_common _ _ _ _ _ fun b h' => ih b n (hp b) D h'

end OracleProg

namespace OracleAdv

variable {D R α : Type}

/-- An adversary with at most `q` queries is an oracle program whose queries, at
cost one each, sum to at most `q`. -/
theorem queryCostLe_toProg {A : OracleAdv D R α} {q : ℕ} (h : A.IsQueryBound q) :
    QueryCostLe (fun _ => 1) A.toProg q := by
  induction A generalizing q with
  | ret a => trivial
  | rand p k ih => exact fun b => ih b (h b)
  | query d k ih =>
    cases q with
    | zero => exact h.elim
    | succ q => exact ⟨by simp, fun r => by simpa using ih r (h r)⟩

end OracleAdv

end CatCrypt.Crypto

namespace CatCrypt.Crypto.Signatures

variable {n : ℕ} {Msg PK SK Share View Sig St : Type}

/-! ## Threshold signature schemes and their EUF-CMA game -/

/-- A threshold signature scheme over `n` parties with threshold `t`: key generation
outputs the group public key and one share per party; signing a message from the
shares returns the messages of the honest parties seen by the adversary (`View`) and
the combined signature; verification is a check on the group public key. -/
structure ThresholdSigScheme (n : ℕ) (Msg PK Share View Sig : Type) where
  /-- Signing threshold. -/
  t : ℕ
  /-- Key generation: group public key and the share of each party. -/
  keygen : SPComp (PK × (Fin n → Share))
  /-- Signing protocol: the honest parties' messages and the combined signature. -/
  sign : (Fin n → Share) → Msg → SPComp (View × Sig)
  /-- Verification under the group public key. -/
  verify : PK → Msg → Sig → Bool

/-- A threshold EUF-CMA adversary corrupting the parties in `C`: given the group public
key and the shares of the corrupted parties, an adaptive oracle program whose signing
queries are answered by the signing protocol (its view and combined signature), and
which outputs a candidate forgery. -/
structure ThresholdAdversary (C : Finset (Fin n)) (Msg PK Share View Sig : Type) :
    Type 1 where
  /-- The adversary's program on the public key and the corrupted shares. -/
  run : PK → (C → Share) → OracleAdv Msg (View × Sig) (Msg × Sig)

/-- Threshold EUF-CMA game: generate the key and the shares, run the adversary on the
public key and the corrupted shares with the logged signing protocol as oracle; the
adversary wins if the forgery verifies on a message it did not query. -/
noncomputable def thresholdGame [DecidableEq Msg] {C : Finset (Fin n)}
    (T : ThresholdSigScheme n Msg PK Share View Sig)
    (A : ThresholdAdversary C Msg PK Share View Sig) : SPComp Bool :=
  SPComp.bind T.keygen fun ks =>
    SPComp.bind ((A.run ks.1 fun i => ks.2 i).toProg.runLog (T.sign ks.2)) fun out =>
      SPComp.pure (T.verify ks.1 out.1.1 out.1.2 && !(out.2.map Prod.fst).contains out.1.1)

/-- Threshold EUF-CMA advantage: the probability that the adversary forges. -/
noncomputable def thresholdAdvantage [DecidableEq Msg] {C : Finset (Fin n)}
    (T : ThresholdSigScheme n Msg PK Share View Sig)
    (A : ThresholdAdversary C Msg PK Share View Sig) : ℝ≥0∞ :=
  prTrue (thresholdGame T A) Heap.empty

/-! ## Share simulators -/

/-- Simulated signing: a signature of the single-signer scheme on `m` under `sk`,
together with a view drawn by `simView` from the simulator state, the message and the
signature. -/
noncomputable def simSign (S : SigScheme Msg PK SK Sig) (simView : St → Msg → Sig → PMF View)
    (sk : SK) (st : St) (m : Msg) : SPComp (View × Sig) :=
  SPComp.bind (S.sign sk m) fun σ =>
    SPComp.bind (liftPMF (simView st m σ)) fun v => SPComp.pure (v, σ)

/-- A share simulator of the threshold scheme `T` for the corruption set `C` relative
to the single-signer scheme `S`, at per-signature distance `δ`.

* `simKey` draws, from the public key alone, the corrupted shares and a simulator state;
  `simView` draws the honest parties' messages from the state, the message and its
  signature.
* `couple` is a joint distribution of key material: its public key and shares have the
  distribution of `T.keygen` (`couple_real`), and its key pair, corrupted shares and
  state have the distribution of `S.keygen` followed by `simKey` (`couple_sim`).
* For every key material, the signing protocol on its shares is at statistical distance
  at most `δ` from simulated signing with its secret key and state (`sign_close`).
* The threshold verifier is the single-signer verifier (`verify_eq`). -/
structure ShareSimulator (T : ThresholdSigScheme n Msg PK Share View Sig)
    (S : SigScheme Msg PK SK Sig) (C : Finset (Fin n)) (δ : ℝ≥0∞) : Type 1 where
  /-- Simulator state. -/
  State : Type
  /-- Corrupted shares and simulator state from the public key. -/
  simKey : PK → PMF ((C → Share) × State)
  /-- Honest parties' messages from the state, the message and the signature. -/
  simView : State → Msg → Sig → PMF View
  /-- Coupled key material. -/
  Key : Type
  /-- Joint distribution of the key material. -/
  couple : SPComp Key
  /-- Public key of the key material. -/
  pk : Key → PK
  /-- Single-signer secret key of the key material. -/
  sk : Key → SK
  /-- Shares of the key material. -/
  shares : Key → Fin n → Share
  /-- Simulator state of the key material. -/
  state : Key → State
  /-- The public key and shares have the distribution of the threshold key generation. -/
  couple_real : SPComp.bind couple (fun k => SPComp.pure (pk k, shares k)) = T.keygen
  /-- The key pair, corrupted shares and state have the distribution of single-signer
  key generation followed by `simKey`. -/
  couple_sim : SPComp.bind couple (fun k =>
      SPComp.pure ((pk k, sk k), ((fun i : C => shares k i), state k))) =
    SPComp.bind S.keygen fun ks => SPComp.bind (liftPMF (simKey ks.1)) fun x => SPComp.pure (ks, x)
  /-- Signing on the shares is `δ`-close to simulated signing. -/
  sign_close : ∀ k, sdist (T.sign (shares k)) (simSign S simView (sk k) (state k)) ≤ δ
  /-- The threshold verifier is the single-signer verifier. -/
  verify_eq : T.verify = S.verify

/-! ## The reduction -/

/-- The adversary `A` with each signing answer `σ` to a query `m` extended by a view
drawn from `simView st m σ`. -/
noncomputable def simAnswers (simView : St → Msg → Sig → PMF View) (st : St) {α : Type} :
    OracleAdv Msg (View × Sig) α → OracleAdv Msg Sig α
  | .ret a => .ret a
  | .rand p k => .rand p fun b => simAnswers simView st (k b)
  | .query m k => .query m fun σ => .rand (simView st m σ) fun v => simAnswers simView st (k (v, σ))

/-- **Reduction from threshold to single-signer EUF-CMA.** On the public key, draw the
corrupted shares and a state from `simKey`, then run the threshold adversary,
forwarding each signing query to the single-signer oracle and adding a simulated view
to its answer; output the adversary's forgery. -/
noncomputable def thresholdRed {T : ThresholdSigScheme n Msg PK Share View Sig}
    {S : SigScheme Msg PK SK Sig} {C : Finset (Fin n)} {δ : ℝ≥0∞}
    (sim : ShareSimulator T S C δ) (A : ThresholdAdversary C Msg PK Share View Sig) :
    EUFCMAAdversary Msg PK SK Sig :=
  toEUFAdversary fun pk =>
    .rand (sim.simKey pk) fun x => simAnswers sim.simView x.2 (A.run pk x.1)

/-- Running the simulated-answer adversary against the logged single-signer oracle is
running the adversary against simulated signing, logging the message and signature. -/
theorem runWith_simAnswers (S : SigScheme Msg PK SK Sig) (simView : St → Msg → Sig → PMF View)
    (sk : SK) (st : St) {α : Type} (A : OracleAdv Msg (View × Sig) α) :
    (simAnswers simView st A).toProg.runWith (OracleProg.logging (S.sign sk)) =
      A.toProg.runWith fun m =>
        SPComp.bind (simSign S simView sk st m) fun o => SPComp.pure (o, [(m, o.2)]) := by
  induction A with
  | ret a => rfl
  | rand p k ih =>
    simp only [simAnswers, OracleAdv.toProg, OracleProg.runWith_lift, ih]
  | query m k ih =>
    simp only [simAnswers, OracleAdv.toProg, OracleProg.runWith_query, OracleProg.runWith_lift,
      OracleProg.logging, simSign, SPComp.bind_assoc, SPComp.pure_bind, ih]

/-- **Threshold EUF-CMA from single-signer EUF-CMA.** For a share simulator at
per-signature distance `δ` and an adversary corrupting the parties in `C` with at most
`q` signing queries, the threshold EUF-CMA advantage is at most the single-signer
EUF-CMA advantage of `thresholdRed sim A` plus `q * δ`. -/
theorem thresholdAdvantage_le [DecidableEq Msg]
    {T : ThresholdSigScheme n Msg PK Share View Sig} {S : SigScheme Msg PK SK Sig}
    {C : Finset (Fin n)} {δ : ℝ≥0∞} (sim : ShareSimulator T S C δ)
    (A : ThresholdAdversary C Msg PK Share View Sig) (q : ℕ)
    (hq : ∀ pk cs, (A.run pk cs).IsQueryBound q) :
    thresholdAdvantage T A ≤ eufcmaAdvantage S (thresholdRed sim A) + q * δ := by
  have hreal : thresholdGame T A = SPComp.bind sim.couple fun k =>
      SPComp.bind ((A.run (sim.pk k) fun i => sim.shares k i).toProg.runWith
        (OracleProg.logging (T.sign (sim.shares k)))) fun out =>
          SPComp.pure (S.verify (sim.pk k) out.1.1 out.1.2 &&
            !(out.2.map Prod.fst).contains out.1.1) := by
    unfold thresholdGame
    rw [← sim.couple_real, SPComp.bind_assoc]
    simp only [SPComp.pure_bind, sim.verify_eq, OracleProg.runLog]
  have hmid : eufcmaGame S (thresholdRed sim A) = SPComp.bind sim.couple fun k =>
      SPComp.bind ((A.run (sim.pk k) fun i => sim.shares k i).toProg.runWith
        (OracleProg.logging (simSign S sim.simView (sim.sk k) (sim.state k)))) fun out =>
          SPComp.pure (S.verify (sim.pk k) out.1.1 out.1.2 &&
            !(out.2.map Prod.fst).contains out.1.1) := by
    have hlog : ∀ k, (A.run (sim.pk k) fun i => sim.shares k i).toProg.runWith
        (fun m => SPComp.bind (simSign S sim.simView (sim.sk k) (sim.state k) m) fun o =>
          SPComp.pure (o, [(m, o.2)])) =
        SPComp.bind ((A.run (sim.pk k) fun i => sim.shares k i).toProg.runWith
          (OracleProg.logging (simSign S sim.simView (sim.sk k) (sim.state k)))) fun al =>
            SPComp.pure (al.1, al.2.map fun e => (e.1, e.2.2)) := by
      intro k
      rw [← OracleProg.runWith_mapLog]
      simp only [OracleProg.logging, SPComp.bind_assoc, SPComp.pure_bind, List.map_cons,
        List.map_nil]
    have hc := congrArg (fun c => SPComp.bind c fun y : (PK × SK) × ((C → Share) × sim.State) =>
      SPComp.bind ((A.run y.1.1 y.2.1).toProg.runWith
        (fun m => SPComp.bind (simSign S sim.simView y.1.2 y.2.2 m) fun o =>
          SPComp.pure (o, [(m, o.2)]))) fun out =>
        SPComp.pure (S.verify y.1.1 out.1.1 out.1.2 && !(out.2.map Prod.fst).contains out.1.1))
      sim.couple_sim
    simp only [SPComp.bind_assoc, SPComp.pure_bind] at hc
    unfold eufcmaGame thresholdRed toEUFAdversary
    simp only [OracleAdv.toProg, OracleProg.runLog, OracleProg.runWith_lift, runWith_simAnswers,
      SPComp.bind_assoc]
    rw [← hc]
    simp only [hlog, SPComp.bind_assoc, SPComp.pure_bind, List.map_map]
    rfl
  unfold thresholdAdvantage eufcmaAdvantage
  rw [hreal, hmid]
  refine le_add_of_absDiff_le (absDiff_bind_common _ _ _ _ _ fun k h => ?_)
  exact OracleProg.absDiff_runWith_le _ _
    ((OracleProg.sdist_logging_le _ _).trans (sim.sign_close k)) _ q
    (OracleAdv.queryCostLe_toProg (hq _ _)) _ h

/-- Share simulability of a threshold scheme relative to a single-signer scheme: a share
simulator at per-signature distance `δ` for every corruption set of fewer than `t`
parties. -/
structure ShareSimulatable (T : ThresholdSigScheme n Msg PK Share View Sig)
    (S : SigScheme Msg PK SK Sig) (δ : ℝ≥0∞) : Type 1 where
  /-- The share simulator of each corruption set of fewer than `t` parties. -/
  sim : ∀ C : Finset (Fin n), C.card < T.t → ShareSimulator T S C δ

/-- **Threshold EUF-CMA against at most `t − 1` corruptions.** For a share-simulatable
scheme and an adversary corrupting a set `C` of fewer than `t` parties with at most `q`
signing queries, the threshold EUF-CMA advantage is at most the single-signer EUF-CMA
advantage of `thresholdRed` plus `q * δ`. -/
theorem thresholdAdvantage_le_of_simulatable [DecidableEq Msg]
    {T : ThresholdSigScheme n Msg PK Share View Sig} {S : SigScheme Msg PK SK Sig}
    {δ : ℝ≥0∞} (h : ShareSimulatable T S δ) {C : Finset (Fin n)} (hC : C.card < T.t)
    (A : ThresholdAdversary C Msg PK Share View Sig) (q : ℕ)
    (hq : ∀ pk cs, (A.run pk cs).IsQueryBound q) :
    thresholdAdvantage T A ≤ eufcmaAdvantage S (thresholdRed (h.sim C hC) A) + q * δ :=
  thresholdAdvantage_le (h.sim C hC) A q hq

/-! ## Running time of the reduction -/

/-- Costed form of `simAnswers`: each query is followed by one `rand` node drawing the
view, whose continuation is charged `tV` more than the adversary's own step. -/
def simAnswersTimed (simView : St → Msg → Sig → PMF View) (tV : ℕ) (st : St) {α : Type} :
    OracleAdv.Timed Msg (View × Sig) α → OracleAdv.Timed Msg Sig α
  | .ret a => .ret a
  | .rand p c k => .rand p c fun b => simAnswersTimed simView tV st (k b)
  | .query m c k => .query m (fun _ => 0) fun σ =>
      .rand (simView st m σ) (fun v => tV + c (v, σ)) fun v =>
        simAnswersTimed simView tV st (k (v, σ))

theorem simAnswersTimed_erase (simView : St → Msg → Sig → PMF View) (tV : ℕ) (st : St)
    {α : Type} (A : OracleAdv.Timed Msg (View × Sig) α) :
    (simAnswersTimed simView tV st A).erase = simAnswers simView st A.erase := by
  induction A with
  | ret a => rfl
  | rand p c k ih => simp only [simAnswersTimed, OracleAdv.Timed.erase, simAnswers, ih]
  | query m c k ih => simp only [simAnswersTimed, OracleAdv.Timed.erase, simAnswers, ih]

/-- An adversary of time `T` with at most `q` queries gives a simulated-answer adversary
of time at most `T + q * (tV + 1)`. -/
theorem simAnswersTimed_timeBound (simView : St → Msg → Sig → PMF View) (tV : ℕ) (st : St)
    {α : Type} {A : OracleAdv.Timed Msg (View × Sig) α} {T q : ℕ} (hA : A.TimeBound T)
    (hq : A.erase.IsQueryBound q) :
    (simAnswersTimed simView tV st A).TimeBound (T + q * (tV + 1)) := by
  induction A generalizing T q with
  | ret a => trivial
  | rand p c k ih =>
    have h1 := hA.1
    refine ⟨by omega, fun b => ?_⟩
    have h2 := (hA.2 b).1
    have h3 := ih b (hA.2 b).2 (hq b)
    generalize q * (tV + 1) = Q at h3 ⊢
    exact ⟨by omega, h3.mono (by omega)⟩
  | query m c k ih =>
    cases q with
    | zero => exact (hq : False).elim
    | succ q =>
      have h1 := hA.1
      have hmul : (q + 1) * (tV + 1) = q * (tV + 1) + (tV + 1) := by ring
      rw [hmul]
      refine ⟨by omega, fun σ => ⟨Nat.zero_le _, by dsimp only; omega, fun v => ?_⟩⟩
      have h2 := (hA.2 (v, σ)).1
      have h3 := ih (v, σ) (hA.2 (v, σ)).2 (hq (v, σ))
      dsimp only
      generalize q * (tV + 1) = Q at h3 ⊢
      exact ⟨by omega, h3.mono (by omega)⟩

/-- The costed reduction from a costed adversary `A'`: one `rand` node drawing the
corrupted shares and the state, its continuation charged `tK`, then the costed
simulated-answer adversary. -/
noncomputable def thresholdRed.timed {T : ThresholdSigScheme n Msg PK Share View Sig}
    {S : SigScheme Msg PK SK Sig} {C : Finset (Fin n)} {δ : ℝ≥0∞}
    (sim : ShareSimulator T S C δ) (tK tV : ℕ)
    (A' : PK → (C → Share) → OracleAdv.Timed Msg (View × Sig) (Msg × Sig)) (pk : PK) :
    ℕ × OracleAdv.Timed Msg Sig (Msg × Sig) :=
  (0, .rand (sim.simKey pk) (fun _ => tK) fun x => simAnswersTimed sim.simView tV x.2 (A' pk x.1))

/-- Erasing the costs of the costed reduction gives the reduction. -/
theorem thresholdRed.erase_timed {T : ThresholdSigScheme n Msg PK Share View Sig}
    {S : SigScheme Msg PK SK Sig} {C : Finset (Fin n)} {δ : ℝ≥0∞}
    (sim : ShareSimulator T S C δ) (A : ThresholdAdversary C Msg PK Share View Sig)
    (A' : PK → (C → Share) → OracleAdv.Timed Msg (View × Sig) (Msg × Sig))
    (hA : ∀ pk cs, (A' pk cs).erase = A.run pk cs) (tK tV : ℕ) (pk : PK) :
    (thresholdRed.timed sim tK tV A' pk).2.erase.toProg = (thresholdRed sim A).run pk := by
  simp only [thresholdRed.timed, thresholdRed, toEUFAdversary, OracleAdv.Timed.erase,
    simAnswersTimed_erase, hA]

/-- **Time of the reduction.** With `A'` of time at most `T` and at most `q` queries,
the costed reduction has time at most `1 + tK + T + q * (tV + 1)`: the key simulation
node and its step `tK`, the adversary, and per query one view node and its step `tV`. -/
theorem thresholdRed.timeBound_timed {T : ThresholdSigScheme n Msg PK Share View Sig}
    {S : SigScheme Msg PK SK Sig} {C : Finset (Fin n)} {δ : ℝ≥0∞}
    (sim : ShareSimulator T S C δ) (tK tV : ℕ)
    {A' : PK → (C → Share) → OracleAdv.Timed Msg (View × Sig) (Msg × Sig)} {TA q : ℕ}
    (hT : ∀ pk cs, (A' pk cs).TimeBound TA) (hq : ∀ pk cs, (A' pk cs).erase.IsQueryBound q)
    (pk : PK) :
    OracleAdv.Timed.StepTimeBound (thresholdRed.timed sim tK tV A' pk)
      (1 + tK + TA + q * (tV + 1)) := by
  dsimp only [thresholdRed.timed, OracleAdv.Timed.StepTimeBound]
  refine ⟨Nat.zero_le _, by omega, fun x => ⟨by dsimp only; omega, ?_⟩⟩
  dsimp only
  exact (simAnswersTimed_timeBound sim.simView tV x.2 (hT pk x.1) (hq pk x.1)).mono
    (by omega)

end CatCrypt.Crypto.Signatures

