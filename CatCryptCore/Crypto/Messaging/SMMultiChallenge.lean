/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.Messaging.SMScheme
public import CatCryptCore.Crypto.OracleAdversaryTimed
public import CatCryptCore.Crypto.HybridArgument

/-!
# The multi-challenge corruption game over a secure-messaging scheme

The corruption game `smCorruptGame` of `CatCryptCore.Crypto.Messaging.SMScheme` answers one
challenge, in the challenge epoch `t` chosen by the adversary. The multi-challenge game
`smMultiGame M ΔFS ΔPCS n mode A` answers up to `n` challenges, every one in the epoch `t` and
under the corruption gates of `smCorruptGame`; the `c`-th answered challenge is the ideal
ciphertext `M.idealCt` when `mode c` holds and the real ciphertext otherwise. The advantage
`SMScheme.multiAdvantage` compares the real mode (no challenge ideal) with the ideal mode (every
challenge ideal).

**Hybrid.** The game at the mode `hybMode i b` (the challenges before the `i`-th ideal, the
`i`-th ideal when `b` holds) is the single-challenge game at `b` against the adversary
`A.hyb M n i` (`smCorruptGame_hyb`). That adversary runs `A` and answers its challenges with
queries of its own (`smHybImpl`): before the `i`-th, a send query whose ciphertext it replaces
by a draw from `M.idealCt`; the `i`-th, its own challenge query; after it, a send query. To
decide which challenge queries the game answers, it keeps a copy of the epoch counters of the
parties, which are a function of the queries and their answers. The `n` hybrids give
`multiAdvantage_le`:

`M.multiAdvantage ΔFS ΔPCS n A ≤ ∑ i < n, M.corruptAdvantage ΔFS ΔPCS (A.hyb M n i)`.

The statement is over the record `SMScheme`: a scheme `M'` that simulates `M`
(`SMScheme.Sim`) has the bound with the single-challenge advantages of `M` at the encoded
adversaries (`SMScheme.Sim.multiAdvantage_le`).

## Main definitions

* `smMultiOracle`, `smMultiGame`, `SMScheme.multiAdvantage` — the multi-challenge game
* `hybMode`, `smHybImpl`, `SMSchemeAdv.hyb` — the hybrids and the reduction
* `smHybImplTimed`, `SMSchemeAdv.hybPlayTimed` — the costed reduction

## Main results

* `smCorruptGame_hyb` — the single-challenge game against `A.hyb M n i` is a hybrid
* `SMScheme.multiAdvantage_le` — the hybrid bound
* `SMScheme.Sim.multiAdvantage_le` — the bound along a simulation of schemes
* `SMSchemeAdv.hybPlayTimed_time` — the costed hybrid reduction erases to the play of
  `A.hyb M n i` and, for a costed adversary of time `T` with at most `q` queries, takes time
  at most `T + q * (u + 2)` at the step cost `u` of the handler
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.Messaging

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal

section Game

variable {St Pub Rand W Ct Leak : Type} [Fintype Rand] [Nonempty Rand]

/-- **The oracle of the multi-challenge game** over the scheme `M`, with the challenge epoch `t`,
at most `n` answered challenges and the mode `mode`: the state of the single-challenge game and
the number of answered challenges. A challenge in the epoch `t` is answered while fewer than `n`
were answered, by the ideal ciphertext when `mode` holds at its index; the other queries are
those of `smSchemeOracle`. -/
noncomputable def smMultiOracle (M : SMScheme St Pub Rand W Ct Leak) (ΔFS ΔPCS t n : ℕ)
    (mode : ℕ → Bool) (x : SMSchemeSt St Pub × ℕ) :
    SMQuery W → PMF (SMSchemeAns Pub Ct Leak × (SMSchemeSt St Pub × ℕ))
  | .ratchet p =>
    (smSchemeOracle M ΔFS ΔPCS t false x.1 (.ratchet p)).map fun y => (y.1, (y.2, x.2))
  | .recv p =>
    (smSchemeOracle M ΔFS ΔPCS t false x.1 (.recv p)).map fun y => (y.1, (y.2, x.2))
  | .send p m =>
    (smSchemeOracle M ΔFS ΔPCS t false x.1 (.send p m)).map fun y => (y.1, (y.2, x.2))
  | .corrupt p =>
    (smSchemeOracle M ΔFS ΔPCS t false x.1 (.corrupt p)).map fun y => (y.1, (y.2, x.2))
  | .chall p m =>
    if x.2 < n ∧ ckaSender (x.1.ck.t p) = p ∧ x.1.ck.t p = t then
      match M.send (x.1.ck.st p) m with
      | some y =>
        (if mode x.2 then M.idealCt else PMF.pure y.2).bind fun c =>
          PMF.pure (.ct c, (x.1.upd p y.1 x.1.done, x.2 + 1))
      | none => PMF.pure (.none, x)
    else PMF.pure (.none, x)

/-- **The multi-challenge corruption game over a scheme.** -/
noncomputable def smMultiGame (M : SMScheme St Pub Rand W Ct Leak) (ΔFS ΔPCS n : ℕ)
    (mode : ℕ → Bool) (A : SMSchemeAdv Pub W Ct Leak) : SPComp Bool :=
  SPComp.bind (liftPMF A.tStar) fun t =>
    SPComp.bind M.init fun i =>
      liftPMF ((OracleAdv.run (smMultiOracle M ΔFS ΔPCS t n mode) (A.play t i.1)
        (SMSchemeSt.init i, 0)).map Prod.fst)

/-- **The advantage in the multi-challenge game**: real against ideal challenges. -/
noncomputable def SMScheme.multiAdvantage (M : SMScheme St Pub Rand W Ct Leak)
    (ΔFS ΔPCS n : ℕ) (A : SMSchemeAdv Pub W Ct Leak) : ℝ≥0∞ :=
  Advantage (smMultiGame M ΔFS ΔPCS n (fun _ => false) A)
    (smMultiGame M ΔFS ΔPCS n (fun _ => true) A)

end Game

/-! ## The hybrids and the reduction -/

/-- The mode of the `i`-th hybrid: the challenges before the `i`-th are ideal, and the `i`-th
when `b` holds. -/
def hybMode (i : ℕ) (b : Bool) (c : ℕ) : Bool := decide (c < i) || (b && decide (c = i))

/-- Opening an epoch is allowed at the counters `g`. -/
def ghostSend (g : CKAParty → ℕ) (p : CKAParty) : Bool :=
  g .A == g .B && ckaSender (g .A + 1) == p

/-- Receiving is allowed at the counters `g`. -/
def ghostRecv (g : CKAParty → ℕ) (p : CKAParty) : Bool := g p + 1 == g p.other

/-- The counters after the party `p` stepped when `b` holds. -/
def ghostStep (g : CKAParty → ℕ) (p : CKAParty) (b : Bool) : CKAParty → ℕ :=
  if b then Function.update g p (g p + 1) else g

/-- The number of answered challenges after the answer `a`. -/
def countAns {Pub Ct Leak : Type} (a : SMSchemeAns Pub Ct Leak) (c : ℕ) : ℕ :=
  match a with
  | .ct _ => c + 1
  | _ => c

section Reduction

variable {St Pub Rand W Ct Leak : Type}

/-- **The query handler of the `i`-th hybrid reduction**, with state the copy of the epoch
counters and the number of answered challenges. A challenge that the multi-challenge game would
answer is asked as a send query before the `i`-th (its ciphertext replaced by a draw from
`M.idealCt`), as a challenge query at the `i`-th, and as a send query after it; the other
queries are forwarded. -/
noncomputable def smHybImpl (M : SMScheme St Pub Rand W Ct Leak) (t n i : ℕ)
    (σ : (CKAParty → ℕ) × ℕ) :
    SMQuery W → OracleAdv (SMQuery W) (SMSchemeAns Pub Ct Leak)
      (SMSchemeAns Pub Ct Leak × ((CKAParty → ℕ) × ℕ))
  | .ratchet p => .query (.ratchet p) fun a => .ret (a, (ghostStep σ.1 p (ghostSend σ.1 p), σ.2))
  | .recv p => .query (.recv p) fun a => .ret (a, (ghostStep σ.1 p (ghostRecv σ.1 p), σ.2))
  | .send p m => .query (.send p m) fun a => .ret (a, σ)
  | .corrupt p => .query (.corrupt p) fun a => .ret (a, σ)
  | .chall p m =>
    if σ.2 < n ∧ ckaSender (σ.1 p) = p ∧ σ.1 p = t then
      if σ.2 < i then
        .query (.send p m) fun a => match a with
          | .ct _ => .rand M.idealCt fun c => .ret (.ct c, (σ.1, σ.2 + 1))
          | a => .ret (a, σ)
      else if σ.2 = i then .query (.chall p m) fun a => .ret (a, (σ.1, countAns a σ.2))
      else .query (.send p m) fun a => .ret (a, (σ.1, countAns a σ.2))
    else .ret (.none, σ)

/-- **The `i`-th hybrid reduction**: `A` with its queries answered by `smHybImpl`, from the
counters `0` and no answered challenge. -/
noncomputable def SMSchemeAdv.hyb (M : SMScheme St Pub Rand W Ct Leak) (n i : ℕ)
    (A : SMSchemeAdv Pub W Ct Leak) : SMSchemeAdv Pub W Ct Leak where
  tStar := A.tStar
  play t T := (OracleAdv.simulate (smHybImpl M t n i) (A.play t T) (fun _ => 0, 0)).bind
    fun x => .ret x.1

end Reduction

section Hybrid

private theorem mapQueryAnswer_id_id {D R α : Type} (A : OracleAdv D R α) :
    A.mapQueryAnswer id id = A := by
  induction A with
  | ret a => rfl
  | rand p k ih => simp only [OracleAdv.mapQueryAnswer, ih]
  | query d k ih => simp only [OracleAdv.mapQueryAnswer, id_eq, ih]

variable {St Pub Rand W Ct Leak : Type} [Fintype Rand] [Nonempty Rand]

/-- The invariant of the reduction: the copy of the counters is exact, and the challenge of the
single-challenge game was asked when more than `i` challenges were answered. -/
def HybInv (i : ℕ) (x : ((CKAParty → ℕ) × ℕ) × SMSchemeSt St Pub) : Prop :=
  x.1.1 = x.2.ck.t ∧ x.2.done = decide (i < x.1.2)

/-- The state of the multi-challenge game seen by the reduction. -/
def hybState (x : ((CKAParty → ℕ) × ℕ) × SMSchemeSt St Pub) : SMSchemeSt St Pub × ℕ :=
  (⟨x.2.ck, false⟩, x.1.2)

theorem smHyb_inv (M : SMScheme St Pub Rand W Ct Leak) (ΔFS ΔPCS t n i : ℕ) (b : Bool)
    (x : ((CKAParty → ℕ) × ℕ) × SMSchemeSt St Pub) (d : SMQuery W) (hx : HybInv i x) :
    ∀ y ∈ (OracleAdv.simOracle (smHybImpl M t n i) (smSchemeOracle M ΔFS ΔPCS t b) x
      d).support, HybInv i y.2 := by
  obtain ⟨⟨g, c⟩, s⟩ := x
  obtain ⟨hg, hd⟩ := hx
  dsimp only at hg hd
  subst hg
  intro y hy
  cases d with
  | ratchet p =>
    simp only [OracleAdv.simOracle, smHybImpl, OracleAdv.run_query, OracleAdv.run_ret,
      smSchemeOracle, PMF.support_map, Set.mem_image] at hy
    by_cases h : s.ck.canSend p = true <;> simp [h] at hy <;>
      obtain ⟨_, _, rfl⟩ := hy <;> simp [HybInv, hd, ghostStep, ghostSend, CKAGameSt.sent] <;>
      simpa [CKAGameSt.canSend] using h
  | recv p =>
    simp only [OracleAdv.simOracle, smHybImpl, OracleAdv.run_query, OracleAdv.run_ret,
      smSchemeOracle, PMF.support_map, Set.mem_image] at hy
    by_cases h : s.ck.canRecv p = true <;> simp [h] at hy <;>
      obtain ⟨_, _, rfl⟩ := hy <;> simp [HybInv, hd, ghostStep, ghostRecv, CKAGameSt.recvd] <;>
      simpa [CKAGameSt.canRecv] using h
  | send p m =>
    simp only [OracleAdv.simOracle, smHybImpl, OracleAdv.run_query, OracleAdv.run_ret,
      smSchemeOracle, PMF.support_map, Set.mem_image] at hy
    by_cases h : (ckaSender (s.ck.t p) == p) = true
    · cases hs : M.send (s.ck.st p) m <;> simp [h, hs] at hy <;>
        obtain ⟨_, _, rfl⟩ := hy <;> simp [HybInv, hd, SMSchemeSt.upd]
    · simp [h] at hy
      obtain ⟨_, _, rfl⟩ := hy
      simp [HybInv, hd]
  | corrupt p =>
    simp only [OracleAdv.simOracle, smHybImpl, OracleAdv.run_query, OracleAdv.run_ret,
      smSchemeOracle, PMF.support_map, Set.mem_image] at hy
    simp at hy
    obtain ⟨_, _, rfl⟩ := hy
    simp [HybInv, hd]
  | chall p m =>
    simp only [OracleAdv.simOracle, smHybImpl] at hy
    by_cases hc : c < n ∧ ckaSender (s.ck.t p) = p ∧ s.ck.t p = t
    · simp only [eq_true hc, ite_true] at hy
      obtain ⟨-, hsend, ht⟩ := hc
      rcases lt_trichotomy c i with hci | rfl | hci
      · simp only [hci, ite_true, OracleAdv.run_query, smSchemeOracle, hsend, beq_self_eq_true]
          at hy
        cases hs : M.send (s.ck.st p) m <;>
          simp [hs] at hy <;>
          (try subst hy) <;> (try obtain ⟨_, _, rfl⟩ := hy) <;>
          simp [HybInv, SMSchemeSt.upd, hd, Nat.not_lt.2 hci.le, Nat.not_le.2 hci]
      · have hd' : s.done = false := by simpa using hd
        simp only [lt_irrefl, ite_false, ite_true, OracleAdv.run_query, smSchemeOracle,
          ht, hd', beq_self_eq_true, Bool.not_false] at hy
        have hsend' : ckaSender t = p := ht ▸ hsend
        cases hs : M.send (s.ck.st p) m <;> cases b <;>
          simp [hs, hsend'] at hy <;>
          (try subst hy) <;> (try obtain ⟨_, _, rfl⟩ := hy) <;>
          simp [HybInv, SMSchemeSt.upd, hd, countAns]
      · have h1 : ¬ c < i := by omega
        have h2 : c ≠ i := by omega
        simp only [h1, h2, ite_false, OracleAdv.run_query, smSchemeOracle, hsend,
          beq_self_eq_true, ite_true] at hy
        cases hs : M.send (s.ck.st p) m <;>
          simp [hs] at hy <;>
          (try subst hy) <;>
          simp [HybInv, SMSchemeSt.upd, hd, countAns, hci, hci.le]
    · simp [hc] at hy
      obtain ⟨_, _, rfl⟩ := hy
      simp [HybInv, hd]

theorem smHyb_step (M : SMScheme St Pub Rand W Ct Leak) (ΔFS ΔPCS t n i : ℕ) (b : Bool)
    (x : ((CKAParty → ℕ) × ℕ) × SMSchemeSt St Pub) (d : SMQuery W) (hx : HybInv i x) :
    (OracleAdv.simOracle (smHybImpl M t n i) (smSchemeOracle M ΔFS ΔPCS t b) x d).map
        (fun y => (id y.1, hybState y.2)) =
      smMultiOracle M ΔFS ΔPCS t n (hybMode i b) (hybState x) d := by
  obtain ⟨⟨g, c⟩, s⟩ := x
  obtain ⟨hg, hd⟩ := hx
  dsimp only at hg hd
  subst hg
  cases d with
  | ratchet p =>
    simp only [OracleAdv.simOracle, smHybImpl, OracleAdv.run_query, OracleAdv.run_ret,
      smMultiOracle, smSchemeOracle, hybState, PMF.map_bind, PMF.pure_map,
      id]
    by_cases h : s.ck.canSend p = true <;> simp [h, PMF.map_bind, PMF.pure_map]
  | recv p =>
    simp only [OracleAdv.simOracle, smHybImpl, OracleAdv.run_query, OracleAdv.run_ret,
      smMultiOracle, smSchemeOracle, hybState, PMF.map_bind, PMF.pure_map,
      id]
    by_cases h : s.ck.canRecv p = true <;> simp [h, PMF.pure_map]
  | send p m =>
    simp only [OracleAdv.simOracle, smHybImpl, OracleAdv.run_query, OracleAdv.run_ret,
      smMultiOracle, smSchemeOracle, hybState, PMF.map_bind, PMF.pure_map,
      id]
    by_cases h : (ckaSender (s.ck.t p) == p) = true
    · cases hs : M.send (s.ck.st p) m <;>
        simp [h, PMF.pure_map, SMSchemeSt.upd]
    · simp [h, PMF.pure_map]
  | corrupt p =>
    simp only [OracleAdv.simOracle, smHybImpl, OracleAdv.run_query, OracleAdv.run_ret,
      smMultiOracle, smSchemeOracle, hybState, PMF.map_bind, PMF.pure_map,
      id]
    exact PMF.pure_bind _ _
  | chall p m =>
    simp only [OracleAdv.simOracle, smHybImpl, smMultiOracle, hybState]
    by_cases hc : c < n ∧ ckaSender (s.ck.t p) = p ∧ s.ck.t p = t
    · simp only [eq_true hc, ite_true]
      obtain ⟨-, hsend, ht⟩ := hc
      rcases lt_trichotomy c i with hci | rfl | hci
      · have hm : hybMode i b c = true := by simp [hybMode, hci]
        simp only [hci, ite_true, hm, OracleAdv.run_query, smSchemeOracle, hsend, beq_self_eq_true]
        cases hs : M.send (s.ck.st p) m with
        | none => simp [PMF.pure_map]
        | some y => simp [PMF.map_bind, PMF.pure_map, SMSchemeSt.upd]
      · have hd' : s.done = false := by simpa using hd
        have hm : hybMode c b c = b := by simp [hybMode]
        simp only [lt_irrefl, ite_false, ite_true, hm, OracleAdv.run_query, smSchemeOracle,
          ht, hd', beq_self_eq_true, Bool.not_false, Bool.true_and]
        cases hs : M.send (s.ck.st p) m with
        | none => simp [PMF.pure_map, countAns]
        | some y =>
          have hsend' : ckaSender t = p := ht ▸ hsend
          cases b <;> simp [hsend', PMF.map_bind, PMF.pure_map, SMSchemeSt.upd, countAns]
      · have h1 : ¬ c < i := by omega
        have h2 : c ≠ i := by omega
        have hm : hybMode i b c = false := by simp [hybMode, h1, h2]
        simp only [h1, h2, ite_false, hm, OracleAdv.run_query, smSchemeOracle, hsend,
          beq_self_eq_true, ite_true]
        cases hs : M.send (s.ck.st p) m with
        | none => simp [PMF.pure_map, countAns]
        | some y => simp [PMF.pure_map, SMSchemeSt.upd, countAns]
    · simp [hc, PMF.pure_map]

/-- **The single-challenge game against the hybrid reduction is a hybrid.** -/
theorem smCorruptGame_hyb (M : SMScheme St Pub Rand W Ct Leak) (ΔFS ΔPCS n i : ℕ) (b : Bool)
    (A : SMSchemeAdv Pub W Ct Leak) :
    smCorruptGame M ΔFS ΔPCS b (A.hyb M n i) = smMultiGame M ΔFS ΔPCS n (hybMode i b) A := by
  simp only [smCorruptGame, smMultiGame, SMSchemeAdv.hyb]
  refine congrArg _ (funext fun t => congrArg _ (funext fun s₀ => congrArg _ ?_))
  rw [OracleAdv.run_simulate_fst]
  have h := OracleAdv.run_map_fst_mapQueryAnswer_of_map_state_inv
    (OracleAdv.simOracle (smHybImpl M t n i) (smSchemeOracle M ΔFS ΔPCS t b))
    (smMultiOracle M ΔFS ΔPCS t n (hybMode i b)) id hybState (HybInv i)
    (fun x d hx => smHyb_inv M ΔFS ΔPCS t n i b x d hx)
    (fun x d hx => smHyb_step M ΔFS ΔPCS t n i b x d hx) (A.play t s₀.1)
    ((fun _ => 0, 0), SMSchemeSt.init s₀) ⟨rfl, rfl⟩
  rw [mapQueryAnswer_id_id] at h
  exact h.symm

theorem hybMode_zero : hybMode 0 false = fun _ => false := by
  funext c; simp [hybMode]

theorem hybMode_true (i : ℕ) : hybMode i true = hybMode (i + 1) false := by
  funext c
  unfold hybMode
  by_cases h1 : c < i <;> by_cases h2 : c = i <;> by_cases h3 : c < i + 1 <;> simp_all <;> omega

/-- The mode is read only below the cap: the game at `hybMode n false` is the ideal game. -/
theorem smMultiGame_hybMode_cap (M : SMScheme St Pub Rand W Ct Leak) (ΔFS ΔPCS n : ℕ)
    (A : SMSchemeAdv Pub W Ct Leak) :
    smMultiGame M ΔFS ΔPCS n (hybMode n false) A =
      smMultiGame M ΔFS ΔPCS n (fun _ => true) A := by
  have h : ∀ t, smMultiOracle (W := W) M ΔFS ΔPCS t n (hybMode n false) =
      smMultiOracle M ΔFS ΔPCS t n (fun _ => true) := by
    intro t
    funext x d
    cases d with
    | chall p m =>
      by_cases hc : x.2 < n ∧ ckaSender (x.1.ck.t p) = p ∧ x.1.ck.t p = t
      · have hm : hybMode n false x.2 = true := by simp [hybMode, hc.1]
        simp only [smMultiOracle, ite_eq_left hc, hm, ite_true]
      · simp only [smMultiOracle, ite_eq_right hc]
    | _ => rfl
  simp only [smMultiGame, h]

/-- **The multi-challenge game from the single-challenge game.** -/
theorem SMScheme.multiAdvantage_le (M : SMScheme St Pub Rand W Ct Leak) (ΔFS ΔPCS n : ℕ)
    (A : SMSchemeAdv Pub W Ct Leak) :
    M.multiAdvantage ΔFS ΔPCS n A ≤
      ∑ i ∈ Finset.range n, M.corruptAdvantage ΔFS ΔPCS (A.hyb M n i) := by
  have h := HybridArgument.advantage_hybrid_dep_bool
    (fun i => smMultiGame M ΔFS ΔPCS n (hybMode i false) A) n
  simp only [hybMode_zero, smMultiGame_hybMode_cap] at h
  refine h.trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
  rw [SMScheme.corruptAdvantage, smCorruptGame_hyb, smCorruptGame_hyb, hybMode_true]

/-- **The multi-challenge game along a simulation of schemes.** If `M'` simulates `M`, the
multi-challenge advantage over `M'` is at most the sum of the single-challenge advantages over
`M` of the hybrid reductions with the answers encoded. -/
theorem SMScheme.Sim.multiAdvantage_le {St' Pub' Ct' Leak' : Type}
    {M' : SMScheme St' Pub' Rand W Ct' Leak'} {M : SMScheme St Pub Rand W Ct Leak}
    {ρ : St' → St → Prop} {encP : Pub → Pub'} {encC : Ct → Ct'} {encL : Leak → Leak'}
    {encI : St → St'} (h : M'.Sim M ρ encP encC encL encI) (ΔFS ΔPCS n : ℕ)
    (A : SMSchemeAdv Pub' W Ct' Leak') :
    M'.multiAdvantage ΔFS ΔPCS n A ≤
      ∑ i ∈ Finset.range n,
        M.corruptAdvantage ΔFS ΔPCS ((A.hyb M' n i).comap encP encC encL) := by
  refine (M'.multiAdvantage_le ΔFS ΔPCS n A).trans (le_of_eq ?_)
  exact Finset.sum_congr rfl fun i _ => h.corruptAdvantage_eq ΔFS ΔPCS _

end Hybrid

/-! ## Running time of the hybrid reduction -/

section Timed

variable {St Pub Rand W Ct Leak : Type}

/-- The costed query handler of the hybrid reduction: the update of the copy of the counters
and the tests at the step cost `u`, then the program of `smHybImpl`. -/
noncomputable def smHybImplTimed (M : SMScheme St Pub Rand W Ct Leak) (t n i u : ℕ)
    (σ : (CKAParty → ℕ) × ℕ) (d : SMQuery W) :
    ℕ × OracleAdv.Timed (SMQuery W) (SMSchemeAns Pub Ct Leak)
      (SMSchemeAns Pub Ct Leak × ((CKAParty → ℕ) × ℕ)) :=
  (u, OracleAdv.Timed.ofAdv (smHybImpl M t n i σ d))

/-- Every program of the costed handler takes time at most `u + 2`. -/
theorem smHybImplTimed_time (M : SMScheme St Pub Rand W Ct Leak) (t n i u : ℕ)
    (σ : (CKAParty → ℕ) × ℕ) (d : SMQuery W) :
    OracleAdv.Timed.StepTimeBound (smHybImplTimed M t n i u σ d) (u + 2) := by
  refine ⟨by simp [smHybImplTimed], ?_⟩
  rw [show u + 2 - (smHybImplTimed M t n i u σ d).1 = 2 by simp [smHybImplTimed]]
  cases d with
  | chall p m =>
    simp only [smHybImplTimed, smHybImpl]
    split_ifs
    · refine ⟨by omega, fun r => ?_⟩
      cases r <;> simp [OracleAdv.Timed.ofAdv, OracleAdv.Timed.TimeBound]
    · exact ⟨by omega, fun r => by simp [OracleAdv.Timed.ofAdv, OracleAdv.Timed.TimeBound]⟩
    · exact ⟨by omega, fun r => by simp [OracleAdv.Timed.ofAdv, OracleAdv.Timed.TimeBound]⟩
    · trivial
  | _ => exact ⟨by omega, fun r => by simp [OracleAdv.Timed.ofAdv, OracleAdv.Timed.TimeBound]⟩

/-- **The costed hybrid reduction**: the costed adversary `Â` simulated by the costed
handler, its output kept. -/
noncomputable def SMSchemeAdv.hybPlayTimed (M : SMScheme St Pub Rand W Ct Leak) (t n i u : ℕ)
    (Â : OracleAdv.Timed (SMQuery W) (SMSchemeAns Pub Ct Leak) Bool) :
    ℕ × OracleAdv.Timed (SMQuery W) (SMSchemeAns Pub Ct Leak) Bool :=
  let x := OracleAdv.Timed.simulate (smHybImplTimed M t n i u) Â (fun _ => 0, 0)
  OracleAdv.Timed.delay x.1 (x.2.bind fun y => (0, .ret y.1))

/-- **Time of the hybrid reduction.** For a costed tree `Â` of time `T` with at most `q`
queries that erases to the play of `A` at the challenge epoch `t` and the public value `T₀`,
the costed hybrid reduction erases to the play of `A.hyb M n i` and has time at most
`T + q * (u + 2)`. -/
theorem SMSchemeAdv.hybPlayTimed_time (M : SMScheme St Pub Rand W Ct Leak) (n i u : ℕ)
    (A : SMSchemeAdv Pub W Ct Leak) (t : ℕ) (T₀ : Pub)
    (Â : OracleAdv.Timed (SMQuery W) (SMSchemeAns Pub Ct Leak) Bool)
    (hÂ : Â.erase = A.play t T₀) {T q : ℕ} (hT : Â.TimeBound T)
    (hq : Â.erase.IsQueryBound q) :
    (SMSchemeAdv.hybPlayTimed M t n i u Â).2.erase = (A.hyb M n i).play t T₀ ∧
      OracleAdv.Timed.StepTimeBound (SMSchemeAdv.hybPlayTimed M t n i u Â) (T + q * (u + 2)) := by
  have hx := OracleAdv.Timed.timeBound_simulate (smHybImplTimed M t n i u)
    (fun σ d => smHybImplTimed_time M t n i u σ d) hT hq (fun _ => 0, 0)
  refine ⟨?_, ?_⟩
  · simp only [SMSchemeAdv.hybPlayTimed, OracleAdv.Timed.delay, OracleAdv.Timed.erase_bind,
      OracleAdv.Timed.erase_simulate, smHybImplTimed, OracleAdv.Timed.erase_ofAdv, hÂ,
      SMSchemeAdv.hyb]
    rfl
  · have hb := OracleAdv.Timed.timeBound_bind (n := 0) hx.2
      (f := fun y => (0, (.ret y.1 : OracleAdv.Timed (SMQuery W) (SMSchemeAns Pub Ct Leak) Bool)))
      fun _ => ⟨le_rfl, trivial⟩
    have hd := OracleAdv.Timed.stepTimeBound_delay (c := (OracleAdv.Timed.simulate
      (smHybImplTimed M t n i u) Â (fun _ => 0, 0)).1) hb
    refine hd.mono ?_
    have := hx.1
    omega

end Timed

end CatCrypt.Crypto.Messaging
