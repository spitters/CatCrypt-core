/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Constructions.ECBCPRF
public import CatCryptCore.ForMathlib.PMFSupport
public import CatCryptCore.ForMathlib.PMFUniform
public import CatCryptCore.Crypto.OracleQueryVec
public import CatCryptCore.Tactics.QueryBound

/-!
# Nonce-based AEAD: games and the stream-cipher-plus-one-time-MAC construction

A nonce-based AEAD scheme encrypts a message `M` of blocks under a key `K`, a
nonce `N` and associated data `AD` to a ciphertext of blocks and a tag. The
construction `StreamMAC` underlying ChaCha20-Poly1305 and AES-GCM uses a keyed
function `prf : K → N × ℕ → Blk`:

* the ciphertext block `i ≥ 1` is `mᵢ ⊕ prf K (N, i)`;
* the one-time key is `otk (prf K (N, 0)) = (hk, s)`, and the tag is
  `hash hk AD C + s`, with `hash` an `ε`-almost-Δ-universal hash
  (`IsAlmostDeltaUniversal`).

## Games

The adversary is an adaptive `OracleAdv` (core `OracleAdversary.lean`) with
encryption queries `(N, AD, M)`. The challenger samples the key, keeps the log
of answered queries, and refuses (answers `none`) a query whose nonce is in the
log or whose message has more than `ℓ` blocks, so every answered query uses a
fresh nonce.

* `INDCPA_Advantage S ℓ A` — real-or-random: real encryptions against uniform
  ciphertext blocks with a uniform tag.
* `INTCTXT_Advantage S ℓ A` — the probability that the final output
  `(N, AD, C, T)` of `A` is not in the log, has at most `ℓ` blocks and carries
  the correct tag.

## Reductions

* `cpaReduction S ℓ A`, `authReduction S ℓ A` — PRF distinguishers running `A`
  once and answering every encryption query by querying their oracle at
  `(N, 0), …, (N, |M|)`; `authReduction` queries `(N, 0)` once more to check the
  forgery. With `A` asking at most `q` queries they ask at most `q(ℓ+1)` and
  `q(ℓ+1) + 1` queries.

## Main results

* `indcpa_advantage_eq` — `INDCPA_Advantage S ℓ A = PRF_q_Advantage S.prf (cpaReduction S ℓ A)`
* `intctxt_advantage_le` — `INTCTXT_Advantage S ℓ A ≤
  PRF_q_Advantage S.prf (authReduction S ℓ A) + ε + 1/|T|` for an `ε`-almost-Δ-universal hash
* `indcpa_advantage_le_prp`, `intctxt_advantage_le_prp` — the same bounds over a
  PRP advantage with the switching term of `PRF_q_Advantage_le`

## Proof

The real games are the real PRF games of the reductions (`cpaRealGame_eq`,
`intctxtGame_eq`). Against the lazy random function, every oracle query of the
reductions is fresh, so the run maps to a run against `hkOracle`, which answers
with uniform ciphertext blocks and a uniform tag and records a uniform hash key
per answered query that the answers do not depend on (`run_simOracle_map`). The
tag check of a forgery is then a function of the recorded hash keys; averaged
over them, a forgery on a logged nonce with different `(AD, C)` verifies with
probability at most `ε`, and one on a fresh nonce with probability `1/|T|`
(`hkOracle_forge_le`).
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.AEAD.NonceBased

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.PRPPRF
open CatCrypt.Crypto.Constructions.ECBCPRF
open scoped ENNReal

/-! ## Probability helpers -/

section Helpers

/-- A uniform list of `n` elements. -/
noncomputable def unifList (α : Type) [Fintype α] [Nonempty α] : ℕ → PMF (List α)
  | 0 => PMF.pure []
  | n + 1 => (PMF.uniformFintype α).bind fun a => (unifList α n).map (a :: ·)

theorem find?_zip_map {α β : Type} (l : List α) (g : α → β) (P : α → Bool) :
    (l.zip (l.map g)).find? (fun p => P p.1) = (l.find? P).map fun e => (e, g e) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    grind

/-- A bind is bounded at `b` by a bound on every continuation from the support. -/
theorem bind_apply_le_of_support {α β : Type} (p : PMF α) (f : α → PMF β) (b : β) (c : ℝ≥0∞)
    (h : ∀ a ∈ p.support, f a b ≤ c) : p.bind f b ≤ c := by
  rw [PMF.bind_apply]
  calc ∑' a, p a * f a b ≤ ∑' a, p a * c := ENNReal.tsum_le_tsum fun a => by
        by_cases ha : a ∈ p.support
        · exact mul_le_mul_right (h a ha) _
        · simp [(PMF.apply_eq_zero_iff p a).mpr ha]
    _ = c := by rw [ENNReal.tsum_mul_right, PMF.tsum_coe, one_mul]

theorem length_of_mem_support_unifList {α : Type} [Fintype α] [Nonempty α] (n : ℕ)
    (l : List α) (hl : l ∈ (unifList α n).support) : l.length = n := by
  induction n generalizing l with
  | zero => simpa [unifList] using hl
  | succ n ih =>
    simp only [unifList, PMF.mem_support_bind_iff, PMF.support_map, Set.mem_image] at hl
    obtain ⟨a, -, l', hl', rfl⟩ := hl
    simp [ih l' hl']

/-- A uniform hash key and mask give a tag equal to a fixed value with probability
`1/|T|`. -/
theorem uniform_tag_apply {HK T : Type} [Fintype HK] [Nonempty HK] [AddCommGroup T] [Fintype T]
    [Nonempty T] [DecidableEq T] (h : HK → T) (t : T) :
    ((PMF.uniformFintype (HK × T)).map fun q => decide (t = h q.1 + q.2)) true =
      (Fintype.card T : ℝ≥0∞)⁻¹ := by
  rw [PMF.uniform_prod_eq_bind, PMF.map_bind]
  have hinner : ∀ a : HK, ((PMF.uniformFintype T).map fun b => (a, b)).map
      (fun q : HK × T => decide (t = h q.1 + q.2)) =
      (PMF.uniformFintype T).map fun b => decide (t = b) := by
    intro a
    let e : T ≃ T := ⟨fun b => h a + b, fun b => b - h a, fun b => by simp, fun b => by simp⟩
    conv_rhs => rw [← PMF.uniformFintype_map_equiv e, PMF.map_comp]
    rw [PMF.map_comp]
    rfl
  simp only [hinner, PMF.bind_const, PMF.map_apply]
  rw [tsum_eq_single t fun b hb => by simp [Ne.symm hb]]
  simp [PMF.uniformFintype_apply]

end Helpers

/-! ## Invariants and state maps of oracle runs -/

namespace OracleAdv

variable {D D₀ R R₀ α : Type}

/-- A map `f` of oracle states that commutes with every oracle call from states
satisfying an invariant preserved by the oracle commutes with every run from
such a state. -/
theorem run_map_state_of_inv {S S' : Type} (O : S → D → PMF (R × S))
    (O' : S' → D → PMF (R × S')) (f : S → S') (Inv : S → Prop)
    (hinv : ∀ s d x, Inv s → x ∈ (O s d).support → Inv x.2)
    (hO : ∀ s d, Inv s → (O s d).map (Prod.map id f) = O' (f s) d)
    (A : CatCrypt.Crypto.OracleAdv D R α) (s : S) (hs : Inv s) :
    (CatCrypt.Crypto.OracleAdv.run O A s).map (Prod.map id f) =
      CatCrypt.Crypto.OracleAdv.run O' A (f s) := by
  induction A generalizing s with
  | ret a => simp [PMF.pure_map]
  | rand p k ih =>
    simp only [CatCrypt.Crypto.OracleAdv.run_rand, PMF.map_bind, ih _ s hs]
  | query d k ih =>
    simp only [CatCrypt.Crypto.OracleAdv.run_query, PMF.map_bind]
    rw [← hO s d hs, PMF.bind_map]
    exact PMF.bind_congr_support _ _ _ fun x hx => ih x.1 x.2 (hinv s d x hs hx)

end OracleAdv

/-! ## The construction -/

section Construction

variable {K N AD Blk HK T : Type}

/-- `hash : HK → AD → List Blk → T` is `ε`-almost-Δ-universal on inputs of at most
`ℓ` blocks: for two distinct inputs and every difference `δ`, a uniform hash key
gives `hash hk a₁ - hash hk a₂ = δ` with probability at most `ε`. -/
def IsAlmostDeltaUniversal [Fintype HK] [Nonempty HK] [AddCommGroup T] (ℓ : ℕ)
    (hash : HK → AD → List Blk → T) (ε : ℝ≥0∞) : Prop :=
  ∀ a₁ a₂ : AD × List Blk, a₁ ≠ a₂ → a₁.2.length ≤ ℓ → a₂.2.length ≤ ℓ → ∀ δ : T,
    (PMF.uniformFintype HK).toOuterMeasure {hk | hash hk a₁.1 a₁.2 - hash hk a₂.1 a₂.2 = δ} ≤ ε

/-- The stream-cipher-plus-one-time-MAC AEAD construction: a keyed function `prf`
on nonce–counter pairs, a one-time-key derivation `otk` whose image of a uniform
block is uniform, and a hash `hash`. -/
structure StreamMAC (K N AD Blk HK T : Type) [CryptoWord Blk] [Fintype HK] [Nonempty HK]
    [Fintype T] [Nonempty T] where
  /-- The keyed function on nonce–counter pairs. -/
  prf : K → N × ℕ → Blk
  /-- The hash key and the tag mask derived from a block. -/
  otk : Blk → HK × T
  /-- The hash on associated data and ciphertext blocks. -/
  hash : HK → AD → List Blk → T
  /-- A uniform block gives a uniform hash key and an independent uniform mask. -/
  otk_uniform : (PMF.uniformFintype Blk).map otk = PMF.uniformFintype (HK × T)

variable [CryptoWord Blk] [Fintype HK] [Nonempty HK] [AddCommGroup T] [Fintype T] [Nonempty T]

/-- XOR of the blocks of `ms` with the keystream `f i, f (i+1), …`. -/
def keystreamXor (f : ℕ → Blk) : ℕ → List Blk → List Blk
  | _, [] => []
  | i, m :: ms => CryptoWord.wxor m (f i) :: keystreamXor f (i + 1) ms

theorem length_keystreamXor (f : ℕ → Blk) (i : ℕ) (m : List Blk) :
    (keystreamXor f i m).length = m.length := by
  induction m generalizing i with
  | nil => rfl
  | cons x ms ih => simp [keystreamXor, ih]

namespace StreamMAC

variable (S : StreamMAC K N AD Blk HK T)

/-- The tag of `(ad, c)` under the one-time key derived from the block `u`. -/
def tagOf (u : Blk) (ad : AD) (c : List Blk) : T :=
  S.hash (S.otk u).1 ad c + (S.otk u).2

/-- Encryption: the ciphertext blocks `mᵢ ⊕ prf k (n, i)` for `i ≥ 1` and the tag
under the one-time key derived from `prf k (n, 0)`. -/
def encrypt (k : K) (n : N) (ad : AD) (m : List Blk) : List Blk × T :=
  let c := keystreamXor (fun i => S.prf k (n, i)) 1 m
  (c, S.tagOf (S.prf k (n, 0)) ad c)

/-- Decryption: the plaintext blocks when the tag verifies, `none` otherwise. -/
def decrypt [DecidableEq T] (k : K) (n : N) (ad : AD) (c : List Blk) (t : T) :
    Option (List Blk) :=
  if t = S.tagOf (S.prf k (n, 0)) ad c then some (keystreamXor (fun i => S.prf k (n, i)) 1 c)
  else none

omit [Fintype HK] [Nonempty HK] [Fintype T] [Nonempty T] in
theorem keystreamXor_keystreamXor (f : ℕ → Blk) (i : ℕ) (m : List Blk) :
    keystreamXor f i (keystreamXor f i m) = m := by
  induction m generalizing i with
  | nil => rfl
  | cons x ms ih => simp [keystreamXor, ih, CryptoWord.wxor_cancel]

/-- Decryption inverts encryption. -/
theorem decrypt_encrypt [DecidableEq T] (k : K) (n : N) (ad : AD) (m : List Blk) :
    S.decrypt k n ad (S.encrypt k n ad m).1 (S.encrypt k n ad m).2 = some m := by
  simp [decrypt, encrypt, keystreamXor_keystreamXor]

end StreamMAC

end Construction

/-! ## Games -/

section Games

variable {K N AD Blk HK T : Type} [Fintype K] [Nonempty K] [DecidableEq N] [DecidableEq AD]
  [CryptoWord Blk] [Fintype HK] [Nonempty HK] [AddCommGroup T] [Fintype T] [Nonempty T]
  [DecidableEq T]

/-- A log entry: nonce, associated data, ciphertext blocks and tag. -/
abbrev Entry (N AD Blk T : Type) : Type := N × AD × List Blk × T

/-- An encryption query: nonce, associated data and message blocks. -/
abbrev EncQuery (N AD Blk : Type) : Type := N × AD × List Blk

/-- An encryption answer: ciphertext blocks and tag, or `none` for a refused query. -/
abbrev EncAnswer (Blk T : Type) : Type := Option (List Blk × T)

/-- A query is refused when its nonce is in the log or its message has more than `ℓ`
blocks. -/
def Refused (ℓ : ℕ) (log : List (Entry N AD Blk T)) (d : EncQuery N AD Blk) : Prop :=
  d.1 ∈ log.map Prod.fst ∨ ℓ < d.2.2.length

instance (ℓ : ℕ) (log : List (Entry N AD Blk T)) (d : EncQuery N AD Blk) :
    Decidable (Refused ℓ log d) := by
  unfold Refused; infer_instance

/-- The real encryption oracle under key `k` with the log as state. -/
noncomputable def realOracle (S : StreamMAC K N AD Blk HK T) (ℓ : ℕ) (k : K)
    (log : List (Entry N AD Blk T)) (d : EncQuery N AD Blk) :
    PMF (EncAnswer Blk T × List (Entry N AD Blk T)) :=
  PMF.pure <| if Refused ℓ log d then (none, log) else
    let e := S.encrypt k d.1 d.2.1 d.2.2
    (some e, (d.1, d.2.1, e.1, e.2) :: log)

/-- The random encryption oracle: uniform ciphertext blocks and a uniform tag for
every answered query, with the log as state. -/
noncomputable def idealOracle (ℓ : ℕ) (log : List (Entry N AD Blk T))
    (d : EncQuery N AD Blk) : PMF (EncAnswer Blk T × List (Entry N AD Blk T)) :=
  if Refused ℓ log d then PMF.pure (none, log) else
    (unifList Blk d.2.2.length).bind fun c => (PMF.uniformFintype T).map fun t =>
      (some (c, t), (d.1, d.2.1, c, t) :: log)

/-- Real IND-CPA game: sample a key, then run `A` against the real oracle. -/
noncomputable def cpaRealGame (S : StreamMAC K N AD Blk HK T) (ℓ : ℕ)
    (A : OracleAdv (EncQuery N AD Blk) (EncAnswer Blk T) Bool) : SPComp Bool :=
  liftPMF ((PMF.uniformFintype K).bind fun k =>
    (OracleAdv.run (realOracle S ℓ k) A []).map Prod.fst)

/-- Random IND-CPA game: run `A` against the random oracle. -/
noncomputable def cpaIdealGame (ℓ : ℕ)
    (A : OracleAdv (EncQuery N AD Blk) (EncAnswer Blk T) Bool) : SPComp Bool :=
  liftPMF ((OracleAdv.run (idealOracle ℓ) A []).map Prod.fst)

/-- Real-or-random IND-CPA advantage of a nonce-respecting adversary `A` against
`S` on messages of at most `ℓ` blocks. -/
noncomputable def INDCPA_Advantage (S : StreamMAC K N AD Blk HK T) (ℓ : ℕ)
    (A : OracleAdv (EncQuery N AD Blk) (EncAnswer Blk T) Bool) : ℝ≥0∞ :=
  Advantage (cpaRealGame S ℓ A) (cpaIdealGame ℓ A)

/-- The forgery `fg` wins against key `k` and log `log`: it is not in the log, has
at most `ℓ` blocks, and its tag verifies. -/
def forges (S : StreamMAC K N AD Blk HK T) (ℓ : ℕ) (k : K) (fg : Entry N AD Blk T)
    (log : List (Entry N AD Blk T)) : Bool :=
  if fg ∈ log ∨ ℓ < fg.2.2.1.length then false
  else decide (fg.2.2.2 = S.tagOf (S.prf k (fg.1, 0)) fg.2.1 fg.2.2.1)

/-- INT-CTXT game: sample a key, run `A` against the real oracle, and check its
output forgery against the final log. -/
noncomputable def intctxtGame (S : StreamMAC K N AD Blk HK T) (ℓ : ℕ)
    (A : OracleAdv (EncQuery N AD Blk) (EncAnswer Blk T) (Entry N AD Blk T)) : SPComp Bool :=
  liftPMF ((PMF.uniformFintype K).bind fun k =>
    (OracleAdv.run (realOracle S ℓ k) A []).map fun x => forges S ℓ k x.1 x.2)

/-- INT-CTXT advantage: the probability that `A` outputs a valid new ciphertext. -/
noncomputable def INTCTXT_Advantage (S : StreamMAC K N AD Blk HK T) (ℓ : ℕ)
    (A : OracleAdv (EncQuery N AD Blk) (EncAnswer Blk T) (Entry N AD Blk T)) : ℝ≥0∞ :=
  prTrue (intctxtGame S ℓ A) Heap.empty

/-! ## Reductions -/

/-- Compute the ciphertext blocks of `ms` by querying the oracle at `(n, i), (n, i+1), …`
and continue with `g` on them. -/
def encBlocksAdv {X : Type} (n : N) (g : List Blk → OracleAdv (N × ℕ) Blk X) :
    ℕ → List Blk → OracleAdv (N × ℕ) Blk X
  | _, [] => g []
  | i, m :: ms => .query (n, i) fun u =>
      encBlocksAdv n (fun cs => g (CryptoWord.wxor m u :: cs)) (i + 1) ms

/-- The simulation of one encryption query with the log as simulator state:
refuse as the challenger does, otherwise query the oracle at `(n, 1), …, (n, |M|)`
for the ciphertext and at `(n, 0)` for the one-time key. -/
def encImpl (S : StreamMAC K N AD Blk HK T) (ℓ : ℕ) (log : List (Entry N AD Blk T))
    (d : EncQuery N AD Blk) :
    OracleAdv (N × ℕ) Blk (EncAnswer Blk T × List (Entry N AD Blk T)) :=
  if Refused ℓ log d then .ret (none, log) else
    encBlocksAdv d.1 (fun c => .query (d.1, 0) fun u =>
      .ret (some (c, S.tagOf u d.2.1 c), (d.1, d.2.1, c, S.tagOf u d.2.1 c) :: log)) 1 d.2.2

/-- **Reduction** from IND-CPA to the PRF games of `S.prf`: run `A` once, answering
each encryption query with `encImpl` (at most `ℓ + 1` oracle queries each), and
output the output of `A`. -/
def cpaReduction (S : StreamMAC K N AD Blk HK T) (ℓ : ℕ)
    (A : OracleAdv (EncQuery N AD Blk) (EncAnswer Blk T) Bool) : OracleAdv (N × ℕ) Blk Bool :=
  OracleAdv.bind (OracleAdv.simulate (encImpl S ℓ) A []) fun x => .ret x.1

/-- The forgery check with oracle access to the one-time key block: reject a
logged or overlong forgery, otherwise query `(n, 0)` and compare tags. -/
def forgeCheckAdv (S : StreamMAC K N AD Blk HK T) (ℓ : ℕ)
    (x : Entry N AD Blk T × List (Entry N AD Blk T)) : OracleAdv (N × ℕ) Blk Bool :=
  if x.1 ∈ x.2 ∨ ℓ < x.1.2.2.1.length then .ret false else
    .query (x.1.1, 0) fun u => .ret (decide (x.1.2.2.2 = S.tagOf u x.1.2.1 x.1.2.2.1))

/-- **Reduction** from INT-CTXT to the PRF games of `S.prf`: run `A` once, answering
each encryption query with `encImpl`, then check its forgery with one more query. -/
def authReduction (S : StreamMAC K N AD Blk HK T) (ℓ : ℕ)
    (A : OracleAdv (EncQuery N AD Blk) (EncAnswer Blk T) (Entry N AD Blk T)) :
    OracleAdv (N × ℕ) Blk Bool :=
  OracleAdv.bind (OracleAdv.simulate (encImpl S ℓ) A []) (forgeCheckAdv S ℓ)

/-! ## The real games are the real PRF games of the reductions -/

omit [Fintype K] [Nonempty K] [DecidableEq N] [DecidableEq AD] [Fintype HK] [Nonempty HK]
  [AddCommGroup T] [Fintype T] [Nonempty T] [DecidableEq T] in
theorem run_keyed_encBlocksAdv {X : Type} (F : K → N × ℕ → Blk) (k : K) (n : N)
    (g : List Blk → OracleAdv (N × ℕ) Blk X) (i : ℕ) (ms : List Blk) :
    OracleAdv.run (keyedOracle F k) (encBlocksAdv n g i ms) () =
      OracleAdv.run (keyedOracle F k) (g (keystreamXor (fun j => F k (n, j)) i ms)) () := by
  induction ms generalizing g i with
  | nil => rfl
  | cons m ms ih =>
    simp only [encBlocksAdv, OracleAdv.run_query, keyedOracle, PMF.pure_bind, ih]
    rfl

omit [Fintype K] [Nonempty K] [DecidableEq AD] [DecidableEq T] in
theorem simOracle_keyed (S : StreamMAC K N AD Blk HK T) (ℓ : ℕ) (k : K)
    (log : List (Entry N AD Blk T)) (d : EncQuery N AD Blk) :
    (realOracle S ℓ k log d).map (Prod.map id fun l => (l, ())) =
      OracleAdv.simOracle (encImpl S ℓ) (keyedOracle S.prf k) (log, ()) d := by
  unfold OracleAdv.simOracle encImpl realOracle
  split_ifs <;>
    simp [run_keyed_encBlocksAdv, keyedOracle, PMF.pure_map, StreamMAC.encrypt]

omit [Fintype K] [Nonempty K] [DecidableEq AD] [DecidableEq T] in
theorem run_keyed_simulateState {α : Type} (S : StreamMAC K N AD Blk HK T) (ℓ : ℕ) (k : K)
    (A : OracleAdv (EncQuery N AD Blk) (EncAnswer Blk T) α) :
    OracleAdv.run (keyedOracle S.prf k) (OracleAdv.simulate (encImpl S ℓ) A []) () =
      (OracleAdv.run (realOracle S ℓ k) A []).map fun x => (x, ()) := by
  rw [OracleAdv.run_simulate, ← OracleAdv.run_map_state (realOracle S ℓ k) _
    (fun l => (l, ())) (fun s d => simOracle_keyed S ℓ k s d) A [], PMF.map_comp]
  rfl

omit [DecidableEq AD] [DecidableEq T] in
/-- The real IND-CPA game is the real PRF game of `S.prf` against `cpaReduction S ℓ A`. -/
theorem cpaRealGame_eq (S : StreamMAC K N AD Blk HK T) (ℓ : ℕ)
    (A : OracleAdv (EncQuery N AD Blk) (EncAnswer Blk T) Bool) :
    cpaRealGame S ℓ A = realGame S.prf (cpaReduction S ℓ A) := by
  unfold cpaRealGame realGame cpaReduction
  congr 1
  refine congrArg _ (funext fun k => ?_)
  rw [OracleAdv.run_bind, run_keyed_simulateState, PMF.bind_map, PMF.map_bind]
  simp [PMF.pure_map]
  rfl

/-- The INT-CTXT game is the real PRF game of `S.prf` against `authReduction S ℓ A`. -/
theorem intctxtGame_eq (S : StreamMAC K N AD Blk HK T) (ℓ : ℕ)
    (A : OracleAdv (EncQuery N AD Blk) (EncAnswer Blk T) (Entry N AD Blk T)) :
    intctxtGame S ℓ A = realGame S.prf (authReduction S ℓ A) := by
  unfold intctxtGame realGame authReduction
  congr 1
  refine congrArg _ (funext fun k => ?_)
  rw [OracleAdv.run_bind, run_keyed_simulateState, PMF.bind_map, PMF.map_bind,
    ← PMF.bind_pure_comp]
  congr 1
  funext x
  simp only [Function.comp_apply]
  unfold forgeCheckAdv forges
  split_ifs <;> simp [keyedOracle, PMF.pure_map]

end Games

/-! ## Runs against the lazy random function -/

section Ideal

variable {K N AD Blk HK T : Type} [DecidableEq N] [DecidableEq AD]
  [CryptoWord Blk] [Fintype HK] [Nonempty HK] [AddCommGroup T] [Fintype T] [Nonempty T]
  [DecidableEq T]

/-- The table of the lazy random function after recording `us` at
`(n, i), (n, i+1), …`. -/
def extTable (n : N) : ℕ → List Blk → List ((N × ℕ) × Blk) → List ((N × ℕ) × Blk)
  | _, [], t => t
  | i, u :: us, t => extTable n (i + 1) us (((n, i), u) :: t)

/-- Blockwise XOR of two lists, truncated to the shorter one. -/
def xorBlocks : List Blk → List Blk → List Blk
  | m :: ms, u :: us => CryptoWord.wxor m u :: xorBlocks ms us
  | _, _ => []

/-- Lookup in a lazy-sampling table, with the equality test of `rfOracle`. -/
abbrev tableLookup {Blk : Type} (p : N × ℕ) (t : List ((N × ℕ) × Blk)) : Option Blk :=
  @List.lookup (N × ℕ) Blk instBEqOfDecidableEq p t

omit [DecidableEq AD] [CryptoWord Blk] [Fintype HK] [Nonempty HK] [AddCommGroup T] [Fintype T]
  [Nonempty T] [DecidableEq T] in
theorem lookup_cons_ne {Blk : Type} (p q : N × ℕ) (u : Blk) (t : List ((N × ℕ) × Blk))
    (h : p ≠ q) : tableLookup p ((q, u) :: t) = tableLookup p t := by
  grind

omit [DecidableEq AD] [CryptoWord Blk] [Fintype HK] [Nonempty HK] [AddCommGroup T] [Fintype T]
  [Nonempty T] [DecidableEq T] in
theorem lookup_cons_self {Blk : Type} (p : N × ℕ) (u : Blk) (t : List ((N × ℕ) × Blk)) :
    tableLookup p ((p, u) :: t) = some u := by
  simp [tableLookup]

omit [DecidableEq AD] [Fintype HK] [Nonempty HK] [AddCommGroup T] [Fintype T] [Nonempty T]
  [DecidableEq T] in
theorem rfOracle_of_lookup_none (t : List ((N × ℕ) × Blk)) (p : N × ℕ)
    (h : tableLookup p t = none) :
    rfOracle t p = (PMF.uniformFintype Blk).map fun r => (r, (p, r) :: t) := by
  unfold tableLookup at h; unfold rfOracle; rw [h]

omit [DecidableEq AD] [Fintype HK] [Nonempty HK] [AddCommGroup T] [Fintype T] [Nonempty T]
  [DecidableEq T] in
theorem rfOracle_of_lookup_some (t : List ((N × ℕ) × Blk)) (p : N × ℕ) (u : Blk)
    (h : tableLookup p t = some u) : rfOracle t p = PMF.pure (u, t) := by
  unfold tableLookup at h; unfold rfOracle; rw [h]

omit [DecidableEq AD] [CryptoWord Blk] [Fintype HK] [Nonempty HK] [AddCommGroup T] [Fintype T]
  [Nonempty T] [DecidableEq T] in
theorem lookup_extTable {Blk : Type} (n : N) (i : ℕ) (us : List Blk)
    (t : List ((N × ℕ) × Blk)) (p : N × ℕ) (hp : p.1 ≠ n ∨ p.2 < i) :
    tableLookup p (extTable n i us t) = tableLookup p t := by
  induction us generalizing i t with
  | nil => rfl
  | cons u us ih =>
    rw [extTable, ih (i + 1) _ (hp.imp id fun h => by omega), lookup_cons_ne]
    rintro rfl
    rcases hp with h | h
    · exact h rfl
    · exact lt_irrefl _ h

omit [DecidableEq N] [DecidableEq AD] [Fintype HK] [Nonempty HK] [AddCommGroup T] [Fintype T]
  [Nonempty T] [DecidableEq T] in
theorem map_xorBlocks_unifList (ms : List Blk) :
    (unifList Blk ms.length).map (xorBlocks ms) = unifList Blk ms.length := by
  induction ms with
  | nil => simp [unifList, PMF.pure_map, xorBlocks]
  | cons m ms ih =>
    let e : Blk ≃ Blk := ⟨fun u => CryptoWord.wxor m u, fun u => CryptoWord.wxor m u,
      CryptoWord.wxor_left_cancel m, CryptoWord.wxor_left_cancel m⟩
    have he : (PMF.uniformFintype Blk).map (fun u => CryptoWord.wxor m u) =
        PMF.uniformFintype Blk := PMF.uniformFintype_map_equiv e
    simp only [List.length_cons, unifList, PMF.map_bind, PMF.map_comp]
    have : ∀ u, (unifList Blk ms.length).map (xorBlocks (m :: ms) ∘ (u :: ·)) =
        ((unifList Blk ms.length).map (xorBlocks ms)).map (CryptoWord.wxor m u :: ·) := by
      intro u; rw [PMF.map_comp]; rfl
    simp only [this, ih]
    conv_rhs => rw [← he, PMF.bind_map]
    rfl

omit [DecidableEq AD] [Fintype HK] [Nonempty HK] [AddCommGroup T] [Fintype T] [Nonempty T]
  [DecidableEq T] in
theorem run_rf_encBlocksAdv {X : Type} (n : N) (g : List Blk → OracleAdv (N × ℕ) Blk X)
    (i : ℕ) (ms : List Blk) (t : List ((N × ℕ) × Blk))
    (hfresh : ∀ j, i ≤ j → tableLookup (n, j) t = none) :
    OracleAdv.run rfOracle (encBlocksAdv n g i ms) t =
      (unifList Blk ms.length).bind fun us =>
        OracleAdv.run rfOracle (g (xorBlocks ms us)) (extTable n i us t) := by
  induction ms generalizing g i t with
  | nil => simp [encBlocksAdv, unifList, xorBlocks, extTable]
  | cons m ms ih =>
    simp only [encBlocksAdv, OracleAdv.run_query, rfOracle_of_lookup_none t _ (hfresh i le_rfl),
      PMF.bind_map, Function.comp_def, List.length_cons, unifList, PMF.bind_bind]
    refine congrArg _ (funext fun u => ?_)
    rw [ih _ (i + 1) _ fun j hj => by
      rw [lookup_cons_ne _ _ _ _ (by intro h; simp at h; omega)]; exact hfresh j (by omega)]
    rfl

/-- The oracle answering every answered query with uniform ciphertext blocks and a
uniform tag, and recording a uniform hash key per answered query next to the log. -/
noncomputable def hkOracle (HK : Type) [Fintype HK] [Nonempty HK] (ℓ : ℕ)
    (s : List (Entry N AD Blk T) × List HK) (d : EncQuery N AD Blk) :
    PMF (EncAnswer Blk T × (List (Entry N AD Blk T) × List HK)) :=
  if Refused ℓ s.1 d then PMF.pure (none, s) else
    (unifList Blk d.2.2.length).bind fun c => (PMF.uniformFintype (HK × T)).map fun p =>
      (some (c, p.2), ((d.1, d.2.1, c, p.2) :: s.1, p.1 :: s.2))

omit [DecidableEq AD] [AddCommGroup T] [DecidableEq T] in
theorem hkOracle_map_fst (ℓ : ℕ) (s : List (Entry N AD Blk T) × List HK)
    (d : EncQuery N AD Blk) :
    (hkOracle HK ℓ s d).map (Prod.map id Prod.fst) = idealOracle ℓ s.1 d := by
  unfold hkOracle idealOracle
  split_ifs
  · simp [PMF.pure_map]
  · simp only [PMF.map_bind, PMF.map_comp, PMF.uniform_prod_eq_bind]
    refine congrArg _ (funext fun c => ?_)
    simp only [Function.comp_def, Prod.map, id, PMF.bind_const]

/-- The hash keys recorded for the log entries: the hash key derived from the table
entry at `(n, 0)` for each entry with nonce `n`. -/
def hkMap (S : StreamMAC K N AD Blk HK T)
    (st : List (Entry N AD Blk T) × List ((N × ℕ) × Blk)) :
    List (Entry N AD Blk T) × List HK :=
  (st.1, st.1.map fun e => (S.otk ((tableLookup (e.1, 0) st.2).getD default)).1)

/-- The table has no entry at a nonce outside the log, and every log entry carries
the tag under the one-time key recorded at its nonce. -/
def SimInv (S : StreamMAC K N AD Blk HK T)
    (st : List (Entry N AD Blk T) × List ((N × ℕ) × Blk)) : Prop :=
  (∀ n j, n ∉ st.1.map Prod.fst → tableLookup (n, j) st.2 = none) ∧
    ∀ e ∈ st.1, ∃ u, tableLookup (e.1, 0) st.2 = some u ∧ e.2.2.2 = S.tagOf u e.2.1 e.2.2.1

omit [DecidableEq AD] [DecidableEq T] in
theorem run_rf_encImpl (S : StreamMAC K N AD Blk HK T) (ℓ : ℕ)
    (st : List (Entry N AD Blk T) × List ((N × ℕ) × Blk)) (d : EncQuery N AD Blk)
    (hs : SimInv S st) (hr : ¬ Refused ℓ st.1 d) :
    OracleAdv.run rfOracle (encImpl S ℓ st.1 d) st.2 =
      (unifList Blk d.2.2.length).bind fun us => (PMF.uniformFintype Blk).map fun u =>
        ((some (xorBlocks d.2.2 us, S.tagOf u d.2.1 (xorBlocks d.2.2 us)),
          (d.1, d.2.1, xorBlocks d.2.2 us, S.tagOf u d.2.1 (xorBlocks d.2.2 us)) :: st.1),
          ((d.1, 0), u) :: extTable d.1 1 us st.2) := by
  have hn : d.1 ∉ st.1.map Prod.fst := fun h => hr (Or.inl h)
  unfold encImpl
  rw [ite_eq_right hr, run_rf_encBlocksAdv _ _ _ _ _ fun j _ => hs.1 _ _ hn]
  refine congrArg _ (funext fun us => ?_)
  have hl : tableLookup (d.1, 0) (extTable d.1 1 us st.2) = none := by
    rw [lookup_extTable d.1 1 us st.2 (d.1, 0) (Or.inr Nat.zero_lt_one), hs.1 _ _ hn]
  simp only [OracleAdv.run_query, rfOracle_of_lookup_none _ _ hl, PMF.bind_map, Function.comp_def,
    OracleAdv.run_ret]
  rw [← PMF.bind_pure_comp]
  rfl

omit [DecidableEq N] [DecidableEq AD] [DecidableEq T] in
/-- The hash key and the tag of `(ad, c)` derived from a uniform block are uniform. -/
theorem map_otk_tagOf (S : StreamMAC K N AD Blk HK T) (ad : AD) (c : List Blk) :
    (PMF.uniformFintype Blk).map (fun u => ((S.otk u).1, S.tagOf u ad c)) =
      PMF.uniformFintype (HK × T) := by
  let e : HK × T ≃ HK × T :=
    ⟨fun p => (p.1, S.hash p.1 ad c + p.2), fun p => (p.1, p.2 - S.hash p.1 ad c),
      fun p => by simp, fun p => by simp⟩
  have he : (fun u => ((S.otk u).1, S.tagOf u ad c)) = e ∘ S.otk := rfl
  rw [he, ← PMF.map_comp, S.otk_uniform, PMF.uniformFintype_map_equiv]

omit [DecidableEq AD] [DecidableEq T] in
theorem simInv_nil (S : StreamMAC K N AD Blk HK T) : SimInv S ([], []) :=
  ⟨fun _ _ _ => rfl, fun _ h => by simp at h⟩

omit [DecidableEq AD] [AddCommGroup T] [DecidableEq T] in
theorem hkMap_step (S : StreamMAC K N AD Blk HK T) (ℓ : ℕ)
    (st : List (Entry N AD Blk T) × List ((N × ℕ) × Blk)) (d : EncQuery N AD Blk)
    (hr : ¬ Refused ℓ st.1 d) (us : List Blk) (u : Blk) (c : List Blk) (t : T) :
    hkMap S ((d.1, d.2.1, c, t) :: st.1, ((d.1, 0), u) :: extTable d.1 1 us st.2) =
      ((d.1, d.2.1, c, t) :: st.1, (S.otk u).1 :: (hkMap S st).2) := by
  have hn : d.1 ∉ st.1.map Prod.fst := fun h => hr (Or.inl h)
  simp only [hkMap, List.map_cons, lookup_cons_self, Option.getD_some, Prod.mk.injEq,
    List.cons.injEq, true_and]
  refine List.map_congr_left fun e he => ?_
  have hne : e.1 ≠ d.1 := fun h => hn (h ▸ List.mem_map_of_mem he)
  rw [lookup_cons_ne _ _ _ _ (by simp [hne]), lookup_extTable _ _ _ _ _ (Or.inl hne)]

omit [DecidableEq AD] [DecidableEq T] in
theorem simInv_step (S : StreamMAC K N AD Blk HK T) (ℓ : ℕ)
    (st : List (Entry N AD Blk T) × List ((N × ℕ) × Blk)) (d : EncQuery N AD Blk)
    (x : EncAnswer Blk T × (List (Entry N AD Blk T) × List ((N × ℕ) × Blk)))
    (hs : SimInv S st) (hx : x ∈ (OracleAdv.simOracle (encImpl S ℓ) rfOracle st d).support) :
    SimInv S x.2 := by
  by_cases hr : Refused ℓ st.1 d
  · simp only [OracleAdv.simOracle, encImpl, ite_eq_left hr, OracleAdv.run_ret, PMF.pure_map,
      PMF.support_pure, Set.mem_singleton_iff] at hx
    subst hx; exact hs
  · have hn : d.1 ∉ st.1.map Prod.fst := fun h => hr (Or.inl h)
    rw [OracleAdv.simOracle, run_rf_encImpl S ℓ st d hs hr] at hx
    simp only [PMF.map_bind, PMF.map_comp, PMF.mem_support_bind_iff, PMF.support_map,
      Set.mem_image] at hx
    obtain ⟨us, -, u, -, rfl⟩ := hx
    refine ⟨fun n j hn' => ?_, fun e he => ?_⟩
    · have hne : n ≠ d.1 := fun h => hn' (by simp [h])
      simp only [Function.comp_apply]
      rw [lookup_cons_ne _ _ _ _ (by simp [hne]), lookup_extTable _ _ _ _ _ (Or.inl hne)]
      exact hs.1 n j fun h => hn' (by simp [h])
    · simp only [Function.comp_apply, List.mem_cons] at he
      rcases he with rfl | he
      · exact ⟨u, lookup_cons_self _ _ _, rfl⟩
      · have hne : e.1 ≠ d.1 := fun h => hn (h ▸ List.mem_map_of_mem he)
        obtain ⟨u', hu', ht⟩ := hs.2 e he
        refine ⟨u', ?_, ht⟩
        simp only [Function.comp_apply]
        rw [lookup_cons_ne _ _ _ _ (by simp [hne]), lookup_extTable _ _ _ _ _ (Or.inl hne), hu']

omit [DecidableEq AD] [DecidableEq T] in
/-- Against the lazy random function, one simulated encryption query maps to one
query of `hkOracle`. -/
theorem simOracle_rf_map (S : StreamMAC K N AD Blk HK T) (ℓ : ℕ)
    (st : List (Entry N AD Blk T) × List ((N × ℕ) × Blk)) (d : EncQuery N AD Blk)
    (hs : SimInv S st) :
    (OracleAdv.simOracle (encImpl S ℓ) rfOracle st d).map (Prod.map id (hkMap S)) =
      hkOracle HK ℓ (hkMap S st) d := by
  by_cases hr : Refused ℓ st.1 d
  · simp [OracleAdv.simOracle, encImpl, hkOracle, hkMap, hr, PMF.pure_map]
  · rw [OracleAdv.simOracle, run_rf_encImpl S ℓ st d hs hr]
    have hr' : ¬ Refused ℓ (hkMap S st).1 d := hr
    rw [hkOracle, ite_eq_right hr']
    conv_rhs => rw [← map_xorBlocks_unifList d.2.2, PMF.bind_map]
    simp only [PMF.map_bind, PMF.map_comp]
    refine congrArg _ (funext fun us => ?_)
    rw [← map_otk_tagOf S d.2.1 (xorBlocks d.2.2 us)]
    simp only [Function.comp_apply, PMF.map_comp]
    refine congrArg (PMF.map · _) (funext fun u => ?_)
    simp only [Function.comp_apply, Prod.map, id, hkMap_step S ℓ st d hr]
    rfl

omit [DecidableEq AD] [DecidableEq T] in
/-- Against the lazy random function, the run of `A` with simulated encryption
queries maps to the run of `A` against `hkOracle`. -/
theorem run_simOracle_map {α : Type} (S : StreamMAC K N AD Blk HK T) (ℓ : ℕ)
    (A : OracleAdv (EncQuery N AD Blk) (EncAnswer Blk T) α) :
    (OracleAdv.run (OracleAdv.simOracle (encImpl S ℓ) rfOracle) A ([], [])).map
        (Prod.map id (hkMap S)) =
      OracleAdv.run (hkOracle HK ℓ) A ([], []) :=
  OracleAdv.run_map_state_of_inv _ _ (hkMap S) (SimInv S)
    (fun st d x hs hx => simInv_step S ℓ st d x hs hx) (fun st d hs => simOracle_rf_map S ℓ st d hs)
    A ([], []) (simInv_nil S)

omit [DecidableEq AD] [DecidableEq T] in
/-- The random IND-CPA game is the random-function PRF game against
`cpaReduction S ℓ A`. -/
theorem cpaIdealGame_eq (S : StreamMAC K N AD Blk HK T) (ℓ : ℕ)
    (A : OracleAdv (EncQuery N AD Blk) (EncAnswer Blk T) Bool) :
    cpaIdealGame ℓ A = rfGame (cpaReduction S ℓ A) := by
  unfold cpaIdealGame rfGame cpaReduction
  congr 1
  rw [OracleAdv.run_bind, OracleAdv.run_simulate, PMF.bind_map, PMF.map_bind]
  simp only [Function.comp_def, OracleAdv.run_ret, PMF.pure_map]
  change _ = (OracleAdv.run _ A ([], [])).bind (PMF.pure ∘ Prod.fst)
  rw [PMF.bind_pure_comp]
  have h1 := run_simOracle_map S ℓ A
  have h2 := CatCrypt.Crypto.OracleAdv.run_map_state (hkOracle HK ℓ) (idealOracle ℓ) Prod.fst
    (hkOracle_map_fst ℓ) A ([], [])
  rw [← h2, ← h1, PMF.map_comp, PMF.map_comp]
  rfl

/-! ### The forgery check against `hkOracle` -/

/-- The tag check of the forgery `fg` against a log with recorded hash keys: for a
logged nonce, the tag under the recorded hash key and the mask determined by the
logged tag; for a fresh nonce, the tag under a uniform hash key and mask. -/
noncomputable def tagCheck (S : StreamMAC K N AD Blk HK T) (fg : Entry N AD Blk T)
    (s : List (Entry N AD Blk T) × List HK) : PMF Bool :=
  match (s.1.zip s.2).find? (fun p => decide (p.1.1 = fg.1)) with
  | some p => PMF.pure (decide (fg.2.2.2 =
      S.hash p.2 fg.2.1 fg.2.2.1 + (p.1.2.2.2 - S.hash p.2 p.1.2.1 p.1.2.2.1)))
  | none => (PMF.uniformFintype (HK × T)).map fun q =>
      decide (fg.2.2.2 = S.hash q.1 fg.2.1 fg.2.2.1 + q.2)

/-- The forgery check against a log with recorded hash keys. -/
noncomputable def hkForge (S : StreamMAC K N AD Blk HK T) (ℓ : ℕ)
    (x : Entry N AD Blk T × (List (Entry N AD Blk T) × List HK)) : PMF Bool :=
  if x.1 ∈ x.2.1 ∨ ℓ < x.1.2.2.1.length then PMF.pure false else tagCheck S x.1 x.2

theorem forgeCheck_rf (S : StreamMAC K N AD Blk HK T) (ℓ : ℕ) (fg : Entry N AD Blk T)
    (st : List (Entry N AD Blk T) × List ((N × ℕ) × Blk)) (hs : SimInv S st) :
    (OracleAdv.run rfOracle (forgeCheckAdv S ℓ (fg, st.1)) st.2).map Prod.fst =
      hkForge S ℓ (fg, hkMap S st) := by
  unfold forgeCheckAdv hkForge
  by_cases hc : fg ∈ st.1 ∨ ℓ < fg.2.2.1.length
  · have hc' : fg ∈ (hkMap S st).1 ∨ ℓ < fg.2.2.1.length := hc
    simp only [ite_eq_left hc, ite_eq_left hc', OracleAdv.run_ret, PMF.pure_map]
  · have hc' : ¬ (fg ∈ (hkMap S st).1 ∨ ℓ < fg.2.2.1.length) := hc
    rw [ite_eq_right hc, ite_eq_right hc', tagCheck]
    simp only [OracleAdv.run_query, hkMap]
    rw [find?_zip_map st.1 _ (fun e => decide (e.1 = fg.1))]
    cases hl : tableLookup (fg.1, 0) st.2 with
    | some u =>
      have hmem : fg.1 ∈ st.1.map Prod.fst := by
        by_contra h; rw [hs.1 _ _ h] at hl; cases hl
      cases hf : st.1.find? (fun e => decide (e.1 = fg.1)) with
      | none =>
        grind
      | some e =>
        have he := List.mem_of_find?_eq_some hf
        have hen : e.1 = fg.1 := by simpa using List.find?_some hf
        obtain ⟨u', hu', ht⟩ := hs.2 e he
        rw [hen, hl] at hu'
        cases hu'
        simp only [rfOracle_of_lookup_some _ _ _ hl, PMF.pure_bind, OracleAdv.run_ret,
          PMF.pure_map, Option.map_some, hen, hl, Option.getD_some, ht, StreamMAC.tagOf,
          add_sub_cancel_left]
        rfl
    | none =>
      have hf : st.1.find? (fun e => decide (e.1 = fg.1)) = none := by
        refine List.find?_eq_none.mpr fun e he hen => ?_
        obtain ⟨u', hu', -⟩ := hs.2 e he
        rw [show e.1 = fg.1 by simpa using hen, hl] at hu'
        cases hu'
      simp only [rfOracle_of_lookup_none _ _ hl, PMF.bind_map, Function.comp_def,
        OracleAdv.run_ret, hf, Option.map_none]
      rw [PMF.map_bind]
      simp only [PMF.pure_map]
      change (PMF.uniformFintype Blk).bind
        (PMF.pure ∘ fun x => decide (fg.2.2.2 = S.tagOf x fg.2.1 fg.2.2.1)) = _
      rw [PMF.bind_pure_comp, ← S.otk_uniform, PMF.map_comp]
      rfl

/-- The random-function PRF game against `authReduction S ℓ A` is the forgery check
after the run of `A` against `hkOracle`. -/
theorem prTrue_rfGame_authReduction (S : StreamMAC K N AD Blk HK T) (ℓ : ℕ)
    (A : OracleAdv (EncQuery N AD Blk) (EncAnswer Blk T) (Entry N AD Blk T)) :
    prTrue (rfGame (authReduction S ℓ A)) Heap.empty =
      ((OracleAdv.run (hkOracle HK ℓ) A ([], [])).bind (hkForge S ℓ)) true := by
  rw [rfGame, prTrue_liftPMF]
  suffices h : (OracleAdv.run rfOracle (authReduction S ℓ A) []).map Prod.fst =
      (OracleAdv.run (hkOracle HK ℓ) A ([], [])).bind (hkForge S ℓ) by rw [h]
  unfold authReduction
  rw [OracleAdv.run_bind, OracleAdv.run_simulate, PMF.bind_map, PMF.map_bind,
    ← run_simOracle_map S ℓ A, PMF.bind_map]
  refine PMF.bind_congr_support _ _ _ fun y hy => ?_
  exact forgeCheck_rf S ℓ y.1 y.2 (OracleAdv.run_support_inv _ (SimInv S)
    (fun st d x hs hx => simInv_step S ℓ st d x hs hx) A ([], []) (simInv_nil S) y hy)

/-- Averaged over the recorded hash keys, the tag check of a forgery that is not in
the log and has at most `ℓ` blocks succeeds with probability at most `ε + 1/|T|`. -/
theorem tagCheck_le (S : StreamMAC K N AD Blk HK T) (ℓ : ℕ) (ε : ℝ≥0∞)
    (hH : IsAlmostDeltaUniversal ℓ S.hash ε) (fg : Entry N AD Blk T)
    (hlen : fg.2.2.1.length ≤ ℓ) (log : List (Entry N AD Blk T)) (hfg : fg ∉ log)
    (hlog : ∀ e ∈ log, e.2.2.1.length ≤ ℓ) :
    ((unifList HK log.length).bind fun hs => tagCheck S fg (log, hs)) true ≤
      ε + (Fintype.card T : ℝ≥0∞)⁻¹ := by
  induction log with
  | nil =>
    simp only [List.length_nil, unifList, PMF.pure_bind, tagCheck, List.zip_nil_left,
      List.find?_nil]
    exact (uniform_tag_apply (fun hk => S.hash hk fg.2.1 fg.2.2.1) fg.2.2.2).le.trans le_add_self
  | cons e log ih =>
    simp only [List.length_cons, unifList, PMF.bind_bind, PMF.bind_map, Function.comp_def]
    by_cases he : e.1 = fg.1
    · have hstep : ∀ hk : HK, ((unifList HK log.length).bind fun hs =>
          tagCheck S fg (e :: log, hk :: hs)) = PMF.pure (decide (fg.2.2.2 =
            S.hash hk fg.2.1 fg.2.2.1 + (e.2.2.2 - S.hash hk e.2.1 e.2.2.1))) := by
        intro hk
        simp [tagCheck, List.zip_cons_cons, he]
      simp only [hstep]
      change ((PMF.uniformFintype HK).bind (PMF.pure ∘ fun hk => decide (fg.2.2.2 =
        S.hash hk fg.2.1 fg.2.2.1 + (e.2.2.2 - S.hash hk e.2.1 e.2.2.1)))) true ≤ _
      rw [PMF.bind_pure_comp]
      refine le_trans ?_ le_self_add
      by_cases hsame : (fg.2.1, fg.2.2.1) = (e.2.1, e.2.2.1)
      · simp only [Prod.mk.injEq] at hsame
        have hne : fg.2.2.2 ≠ e.2.2.2 := fun ht => hfg (by
          have : fg = e := Prod.ext he.symm (Prod.ext hsame.1 (Prod.ext hsame.2 ht))
          simp [this])
        simp [PMF.map_apply, hsame.1, hsame.2, hne]
      · refine le_trans ?_ (hH (fg.2.1, fg.2.2.1) (e.2.1, e.2.2.1) hsame hlen
          (hlog e (by simp)) (fg.2.2.2 - e.2.2.2))
        rw [PMF.map_apply, PMF.toOuterMeasure_apply]
        refine ENNReal.tsum_le_tsum fun hk => ?_
        by_cases hP : fg.2.2.2 = S.hash hk fg.2.1 fg.2.2.1 +
            (e.2.2.2 - S.hash hk e.2.1 e.2.2.1)
        · have hmem : hk ∈ {hk | S.hash hk fg.2.1 fg.2.2.1 - S.hash hk e.2.1 e.2.2.1 =
              fg.2.2.2 - e.2.2.2} := by
            change _ = _
            rw [hP]; abel
          rw [ite_eq_left (by simp [hP]), Set.indicator_of_mem hmem]
        · simp_all
    · have hstep : ∀ hk : HK, ((unifList HK log.length).bind fun hs =>
          tagCheck S fg (e :: log, hk :: hs)) =
            (unifList HK log.length).bind fun hs => tagCheck S fg (log, hs) := by
        intro hk
        refine congrArg _ (funext fun hs => ?_)
        simp [tagCheck, List.zip_cons_cons, he]
      simp only [hstep, PMF.bind_const]
      exact ih (fun h => hfg (List.mem_cons_of_mem e h)) fun e' he' => hlog e' (by simp [he'])

/-- Against `hkOracle`, started from a log whose hash keys are uniform, the forgery
of `A` passes the check with probability at most `ε + 1/|T|`. -/
theorem hkOracle_forge_le (S : StreamMAC K N AD Blk HK T) (ℓ : ℕ) (ε : ℝ≥0∞)
    (hH : IsAlmostDeltaUniversal ℓ S.hash ε)
    (A : OracleAdv (EncQuery N AD Blk) (EncAnswer Blk T) (Entry N AD Blk T))
    (log : List (Entry N AD Blk T)) (hlog : ∀ e ∈ log, e.2.2.1.length ≤ ℓ) :
    ((unifList HK log.length).bind fun hs =>
      (OracleAdv.run (hkOracle HK ℓ) A (log, hs)).bind (hkForge S ℓ)) true ≤
        ε + (Fintype.card T : ℝ≥0∞)⁻¹ := by
  induction A generalizing log with
  | ret a =>
    simp only [OracleAdv.run_ret, PMF.pure_bind]
    unfold hkForge
    by_cases hc : a ∈ log ∨ ℓ < a.2.2.1.length
    · simp [hc]
    · simp only [hc, ite_false]
      push Not at hc
      exact tagCheck_le S ℓ ε hH a hc.2 log hc.1 hlog
  | rand p k ih =>
    simp only [OracleAdv.run_rand, PMF.bind_bind]
    rw [PMF.bind_comm]
    exact bind_apply_le_of_support _ _ _ _ fun b _ => ih b log hlog
  | query d k ih =>
    simp only [OracleAdv.run_query, PMF.bind_bind]
    by_cases hr : Refused ℓ log d
    · simp only [hkOracle, hr, ite_true, PMF.pure_bind]
      exact ih none log hlog
    · simp only [hkOracle, hr, ite_false, PMF.bind_bind, PMF.bind_map, Function.comp_def]
      rw [PMF.bind_comm]
      refine bind_apply_le_of_support _ _ _ _ fun c hc => ?_
      have hclen := length_of_mem_support_unifList _ c hc
      simp only [PMF.uniform_prod_eq_bind, PMF.bind_bind, PMF.bind_map, Function.comp_def]
      rw [PMF.bind_comm]
      simp only [PMF.bind_comm (unifList HK log.length) (PMF.uniformFintype T)]
      rw [PMF.bind_comm]
      refine bind_apply_le_of_support _ _ _ _ fun t _ => ?_
      have hih := ih (some (c, t)) ((d.1, d.2.1, c, t) :: log) fun e he => by
        rcases List.mem_cons.mp he with rfl | he
        · simp only [hclen]; exact not_lt.mp fun h => hr (Or.inr h)
        · exact hlog e he
      simpa only [List.length_cons, unifList, PMF.bind_bind, PMF.bind_map,
        Function.comp_def] using hih

end Ideal

/-! ## Security bounds -/

section Bounds

variable {K N AD Blk HK T : Type} [Fintype K] [Nonempty K] [DecidableEq N] [DecidableEq AD]
  [CryptoWord Blk] [Fintype HK] [Nonempty HK] [AddCommGroup T] [Fintype T] [Nonempty T]
  [DecidableEq T]

omit [Fintype K] [Nonempty K] [DecidableEq N] [DecidableEq AD] [Fintype HK] [Nonempty HK]
  [AddCommGroup T] [Fintype T] [Nonempty T] [DecidableEq T] in
theorem isQueryBound_encBlocksAdv {X : Type} (n : N) (g : List Blk → OracleAdv (N × ℕ) Blk X)
    (c : ℕ) (hg : ∀ cs, (g cs).IsQueryBound c) (i : ℕ) (ms : List Blk) :
    (encBlocksAdv n g i ms).IsQueryBound (ms.length + c) := by
  induction ms generalizing g i <;> query_bound

omit [Fintype K] [Nonempty K] [DecidableEq AD] [DecidableEq T] in
@[query_fold] theorem isQueryBound_encImpl (S : StreamMAC K N AD Blk HK T) (ℓ : ℕ)
    (log : List (Entry N AD Blk T)) (d : EncQuery N AD Blk) :
    (encImpl S ℓ log d).IsQueryBound (ℓ + 1) := by
  have hl : ¬ Refused ℓ log d → d.2.2.length ≤ ℓ := by grind [Refused]
  have hb := isQueryBound_encBlocksAdv d.1 (fun c => .query (d.1, 0) fun u =>
    .ret (some (c, S.tagOf u d.2.1 c), (d.1, d.2.1, c, S.tagOf u d.2.1 c) :: log)) 1
    (fun _ => by query_bound) 1 d.2.2
  query_bound

omit [Fintype K] [Nonempty K] [DecidableEq AD] [DecidableEq T] in
/-- With `A` asking at most `q` encryption queries, `cpaReduction S ℓ A` asks at most
`q(ℓ+1)` oracle queries. -/
theorem isQueryBound_cpaReduction (S : StreamMAC K N AD Blk HK T) (ℓ : ℕ)
    {A : OracleAdv (EncQuery N AD Blk) (EncAnswer Blk T) Bool} {q : ℕ}
    (hA : A.IsQueryBound q) : (cpaReduction S ℓ A).IsQueryBound (q * (ℓ + 1)) := by
  query_bound

omit [Fintype K] [Nonempty K] in
/-- With `A` asking at most `q` encryption queries, `authReduction S ℓ A` asks at
most `q(ℓ+1) + 1` oracle queries. -/
theorem isQueryBound_authReduction (S : StreamMAC K N AD Blk HK T) (ℓ : ℕ)
    {A : OracleAdv (EncQuery N AD Blk) (EncAnswer Blk T) (Entry N AD Blk T)} {q : ℕ}
    (hA : A.IsQueryBound q) : (authReduction S ℓ A).IsQueryBound (q * (ℓ + 1) + 1) := by
  query_bound

omit [DecidableEq AD] [DecidableEq T] in
/-- **IND-CPA of the stream-cipher-plus-one-time-MAC construction.** For every
nonce-respecting adversary `A` (enforced by the challenger), the real-or-random
advantage equals the PRF advantage of `S.prf` against the explicit reduction
`cpaReduction S ℓ A`, which runs `A` once and asks at most `q(ℓ+1)` queries when `A`
asks at most `q`. -/
theorem indcpa_advantage_eq (S : StreamMAC K N AD Blk HK T) (ℓ : ℕ)
    (A : OracleAdv (EncQuery N AD Blk) (EncAnswer Blk T) Bool) :
    INDCPA_Advantage S ℓ A = PRF_q_Advantage S.prf (cpaReduction S ℓ A) := by
  rw [INDCPA_Advantage, PRF_q_Advantage, cpaRealGame_eq, cpaIdealGame_eq S]

/-- **INT-CTXT of the stream-cipher-plus-one-time-MAC construction.** For an
`ε`-almost-Δ-universal hash and every adversary `A`, the probability of a valid new
ciphertext is at most the PRF advantage of `S.prf` against the explicit reduction
`authReduction S ℓ A` plus `ε + 1/|T|`. -/
theorem intctxt_advantage_le (S : StreamMAC K N AD Blk HK T) (ℓ : ℕ) (ε : ℝ≥0∞)
    (hH : IsAlmostDeltaUniversal ℓ S.hash ε)
    (A : OracleAdv (EncQuery N AD Blk) (EncAnswer Blk T) (Entry N AD Blk T)) :
    INTCTXT_Advantage S ℓ A ≤
      PRF_q_Advantage S.prf (authReduction S ℓ A) + (ε + (Fintype.card T : ℝ≥0∞)⁻¹) := by
  have hideal : prTrue (rfGame (authReduction S ℓ A)) Heap.empty ≤
      ε + (Fintype.card T : ℝ≥0∞)⁻¹ := by
    rw [prTrue_rfGame_authReduction]
    simpa [unifList] using hkOracle_forge_le S ℓ ε hH A [] (by simp)
  rw [INTCTXT_Advantage, intctxtGame_eq, PRF_q_Advantage, Advantage]
  calc prTrue (realGame S.prf (authReduction S ℓ A)) Heap.empty
      ≤ prTrue (realGame S.prf (authReduction S ℓ A)) Heap.empty -
          prTrue (rfGame (authReduction S ℓ A)) Heap.empty +
          prTrue (rfGame (authReduction S ℓ A)) Heap.empty := le_tsub_add
    _ ≤ _ := add_le_add le_sup_left hideal

omit [DecidableEq AD] [DecidableEq T] in
/-- **IND-CPA over a PRP** (the AES-GCM form): for `A` asking at most `q` queries,
the advantage is at most the PRP advantage of `S.prf` against `cpaReduction S ℓ A`
plus the switching term for `q(ℓ+1)` queries. -/
theorem indcpa_advantage_le_prp (S : StreamMAC K N AD Blk HK T) (ℓ : ℕ)
    (A : OracleAdv (EncQuery N AD Blk) (EncAnswer Blk T) Bool) (q : ℕ) (hA : A.IsQueryBound q) :
    INDCPA_Advantage S ℓ A ≤ PRP_q_Advantage S.prf (cpaReduction S ℓ A) +
      ↑(q * (ℓ + 1) * (q * (ℓ + 1) - 1) / 2) / ↑(Fintype.card Blk) := by
  rw [indcpa_advantage_eq]
  exact PRF_q_Advantage_le _ _ _ (isQueryBound_cpaReduction S ℓ hA)

/-- **INT-CTXT over a PRP** (the AES-GCM form): for `A` asking at most `q` queries,
the forgery probability is at most the PRP advantage of `S.prf` against
`authReduction S ℓ A`, the switching term for `q(ℓ+1) + 1` queries, and `ε + 1/|T|`. -/
theorem intctxt_advantage_le_prp (S : StreamMAC K N AD Blk HK T) (ℓ : ℕ) (ε : ℝ≥0∞)
    (hH : IsAlmostDeltaUniversal ℓ S.hash ε)
    (A : OracleAdv (EncQuery N AD Blk) (EncAnswer Blk T) (Entry N AD Blk T)) (q : ℕ)
    (hA : A.IsQueryBound q) :
    INTCTXT_Advantage S ℓ A ≤ PRP_q_Advantage S.prf (authReduction S ℓ A) +
      ↑((q * (ℓ + 1) + 1) * (q * (ℓ + 1) + 1 - 1) / 2) / ↑(Fintype.card Blk) +
      (ε + (Fintype.card T : ℝ≥0∞)⁻¹) :=
  (intctxt_advantage_le S ℓ ε hH A).trans
    (add_le_add_left (PRF_q_Advantage_le _ _ _ (isQueryBound_authReduction S ℓ hA)) _)

end Bounds

end CatCrypt.Crypto.AEAD.NonceBased
