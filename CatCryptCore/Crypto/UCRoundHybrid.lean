/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.UCTransparentMulti
public import CatCryptCore.Crypto.UCOracleGame

/-!
# Hybrid arguments over systems and over sessions

A chain of systems `H 0, H 1, …` in which each `H i` realizes `H (i + 1)` with bound `b i`
gives `H 0` realizing `H n` with bound `∑_{i<n} b i` (`Realizes.hybrid`). When the number of
hops is the number of rounds of the environment, the chain ends at `H Z.rounds`, which an
endpoint bound relates to a fixed system (`Realizes.hybrid_rounds`).

The session form instantiates the chain for protocols whose activations query a family of
independent sessions of one oracle game. A query `(j, q)` asks session `j`; each session samples
its key at its first query. In the hybrid world `i` (`KeyedGame.hybGame G₀ G₁ i`) the sessions
`j < i` run the game `G₁` and the sessions `j ≥ i` run `G₀`, so `hybGame G₀ G₁ 0` is the
multi-session real world. The worlds `i` and `i + 1` differ in session `i` only, and their
distance at an adversary `B` is the advantage between `G₀` and `G₁` of the reduction
`KeyedGame.sessReduction G₀ G₁ i B`, which simulates every session other than `i` and forwards
the queries of session `i` to its own oracle.

## Main definitions

* `KeyedGame.multiOracle orc` — the oracle that answers a query `(j, q)` by the session oracle
  `orc j` on the state of session `j`; `KeyedGame.multiGame orc s₀` — its game.
* `KeyedGame.sessRed orc i s₀ B` — the adversary `B` with every session other than `i` simulated
  and session `i` forwarded.
* `KeyedGame.realSess`, `KeyedGame.idealSess` — a session of `G₀`, of `G₁`, keyed lazily.
* `KeyedGame.hybGame G₀ G₁ i`, `KeyedGame.sessReduction G₀ G₁ i` — the hybrid world `i` and the
  reduction of hop `i`.

## Main results

* `Realizes.hybrid`, `Realizes.hybrid_rounds` — hybrid arguments for realization.
* `KeyedGame.accept_multiGame` — the acceptance probability of `B` in the multi-session game is
  the acceptance probability of `sessRed orc i s₀ B` in the game of session `i`.
* `KeyedGame.advantage_hybGame` — the advantage of `B` between the hybrid worlds `i` and `i + 1`
  is the advantage of `sessReduction G₀ G₁ i B` between `G₀` and `G₁`.
* `Realizes.ofSession`, `Realizes.sessions`, `Realizes.sessions_rounds` — the system of a
  protocol over the hybrid world `0` realizes the system over the world `n`, with bound
  `∑_{i<n}` of the advantages of the session reductions of its environment reduction.
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.UCTransparent

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Crypto.UCConcrete
open scoped ENNReal

/-! ## Hybrid chains of systems -/

section Chain

variable {E O : Type} {τ : ℕ → Type}

/-- **Hybrid argument for systems.** If each `H i` with `i < n` realizes `H (i + 1)` with bound
`b i`, then `H 0` realizes `H n` with bound `∑_{i<n} b i`. -/
theorem Realizes.hybrid (H : (i : ℕ) → Sys (τ i) E O)
    (b : ℕ → (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞) :
    ∀ n, (∀ i < n, Realizes (H i) (H (i + 1)) (b i)) →
      Realizes (H 0) (H n) fun ζ Z => ∑ i ∈ Finset.range n, b i ζ Z := by
  intro n
  induction n with
  | zero => intro _ ζ Z; simp [Env.gap]
  | succ n ih =>
    intro h ζ Z
    have h1 := (ih fun i hi => h i (by omega)).trans (h n (by omega))
    simpa [Finset.sum_range_succ] using h1 ζ Z

/-- **Round-indexed hybrid argument.** If each `H i` realizes `H (i + 1)` with bound `b i`, and
`H` at the number of rounds of `Z` is at distance at most `c ζ Z` from `I`, then `H 0` realizes
`I` with bound `∑_{i<Z.rounds} b i + c`. -/
theorem Realizes.hybrid_rounds {υ : Type} (H : (i : ℕ) → Sys (τ i) E O) (I : Sys υ E O)
    (b : ℕ → (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞)
    (c : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞)
    (h : ∀ i, Realizes (H i) (H (i + 1)) (b i))
    (hend : ∀ (ζ : Type) (Z : Env (Strat ζ E O) ζ), adv (H Z.input.rounds) I Z ≤ c ζ Z) :
    Realizes (H 0) I fun ζ Z => ∑ i ∈ Finset.range Z.input.rounds, b i ζ Z + c ζ Z := by
  intro ζ Z
  have h1 := Realizes.hybrid H b Z.input.rounds (fun i _ => h i) ζ Z
  exact le_trans (absDiff_triangle _
    (prTrue (SPComp.bind (view (H Z.input.rounds) Z.input) Z.dist) Z.heap) _)
    (add_le_add h1 (hend ζ Z))

end Chain

/-! ## Multi-session games -/

namespace KeyedGame

variable {Q A S : Type}

/-- The oracle of a family of sessions: the query `(j, q)` is answered by the session oracle
`orc j` on the state of session `j`, which it updates. -/
noncomputable def multiOracle (orc : ℕ → S → Q → PMF (A × S)) (m : ℕ → S) (d : ℕ × Q) :
    PMF (A × (ℕ → S)) :=
  (orc d.1 (m d.1) d.2).map fun x => (x.1, Function.update m d.1 x.2)

/-- The multi-session game of the session oracles `orc`, every session starting in `s₀`. -/
noncomputable def multiGame (orc : ℕ → S → Q → PMF (A × S)) (s₀ : S) : KeyedGame (ℕ × Q) A where
  Key := Unit
  State := ℕ → S
  keyDist := PMF.pure ()
  oracle _ := multiOracle orc
  init _ := s₀

/-- The simulation of the sessions other than `i`: a query of session `i` is forwarded to the
oracle, and any other query is answered by `multiOracle orc` on the simulated states. -/
noncomputable def sessImpl (orc : ℕ → S → Q → PMF (A × S)) (i : ℕ) (m : ℕ → S) (d : ℕ × Q) :
    OracleAdv Q A (A × (ℕ → S)) :=
  if d.1 = i then .query d.2 fun a => .ret (a, m) else .rand (multiOracle orc m d) .ret

/-- The reduction to session `i`: the adversary `B` of the multi-session game with the sessions
other than `i` simulated from the states `s₀` and session `i` forwarded to the oracle. -/
noncomputable def sessRed (orc : ℕ → S → Q → PMF (A × S)) (i : ℕ) (s₀ : S)
    (B : OracleAdv (ℕ × Q) A Bool) : OracleAdv Q A Bool :=
  (OracleAdv.simulate (sessImpl orc i) B fun _ => s₀).bind fun x => .ret x.1

/-- The simulation of the sessions other than `i` reads the session oracles other than `i`
only. -/
theorem sessImpl_congr {orc orc' : ℕ → S → Q → PMF (A × S)} {i : ℕ}
    (h : ∀ j, j ≠ i → orc j = orc' j) : sessImpl orc i = sessImpl orc' i := by
  funext m d
  by_cases hd : d.1 = i
  · simp [sessImpl, hd]
  · simp [sessImpl, multiOracle, hd, h d.1 hd]

/-- The reduction to session `i` reads the session oracles other than `i` only. -/
theorem sessRed_congr {orc orc' : ℕ → S → Q → PMF (A × S)} {i : ℕ}
    (h : ∀ j, j ≠ i → orc j = orc' j) (s₀ : S) : sessRed orc i s₀ = sessRed orc' i s₀ := by
  funext B
  simp only [sessRed, sessImpl_congr h]

section Slot

variable (orc : ℕ → S → Q → PMF (A × S)) (i : ℕ) (G : KeyedGame Q A)
  (emb : G.Key → G.State → S)

/-- With the key `k` and state `t` of session `i` embedded into the multi-session state, the
multi-session oracle and the simulation of the other sessions against the oracle of `G` with
key `k` give the same output. -/
theorem run_multiOracle_emb
    (hemb : ∀ k t q, orc i (emb k t) q = (G.oracle k t q).map fun x => (x.1, emb k x.2))
    (k : G.Key) (B : OracleAdv (ℕ × Q) A Bool) :
    ∀ (m : ℕ → S) (t : G.State),
      (OracleAdv.run (multiOracle orc) B (Function.update m i (emb k t))).map Prod.fst =
        (OracleAdv.run (OracleAdv.simOracle (sessImpl orc i) (G.oracle k)) B (m, t)).map
          Prod.fst := by
  induction B with
  | ret a => intro m t; simp [PMF.pure_map]
  | rand p c ih =>
    intro m t
    simp only [OracleAdv.run_rand, PMF.map_bind]
    exact congrArg _ (funext fun x => ih x m t)
  | query d c ih =>
    intro m t
    obtain ⟨j, q⟩ := d
    by_cases hj : j = i
    · subst hj
      simp [multiOracle, OracleAdv.simOracle, sessImpl, hemb, PMF.map_bind, PMF.bind_map,
        Function.comp_def, ih]
    · simp only [OracleAdv.run_query, multiOracle, OracleAdv.simOracle, sessImpl, hj,
        ↓reduceIte, OracleAdv.run_rand, OracleAdv.run_ret, PMF.map_bind, PMF.bind_map,
        PMF.bind_bind, PMF.pure_map, PMF.pure_bind, Function.comp_def,
        Function.update_of_ne hj]
      refine congrArg _ (funext fun x => ?_)
      rw [Function.update_comm (Ne.symm hj)]
      exact ih x.1 _ t

/-- Lazy sampling of session `i`: when session `i` is in its initial state `s₀`, from which a
query samples the key of `G` and continues from the embedded initial state, the output of a run
is the average over the key of the runs from the embedded initial state. -/
theorem run_multiOracle_lazy (s₀ : S)
    (hfresh : ∀ q, orc i s₀ q = G.keyDist.bind fun k => orc i (emb k G.init) q)
    (B : OracleAdv (ℕ × Q) A Bool) :
    ∀ m : ℕ → S, m i = s₀ →
      (OracleAdv.run (multiOracle orc) B m).map Prod.fst =
        G.keyDist.bind fun k =>
          (OracleAdv.run (multiOracle orc) B (Function.update m i (emb k G.init))).map
            Prod.fst := by
  induction B with
  | ret a => intro m _; simp [PMF.pure_map]
  | rand p c ih =>
    intro m hm
    simp only [OracleAdv.run_rand, PMF.map_bind]
    rw [PMF.bind_comm]
    exact congrArg _ (funext fun x => ih x m hm)
  | query d c ih =>
    intro m hm
    obtain ⟨j, q⟩ := d
    by_cases hj : j = i
    · subst hj
      simp only [OracleAdv.run_query, multiOracle, PMF.map_bind, PMF.bind_map, hm, hfresh,
        PMF.bind_bind, Function.update_self, Function.update_idem, Function.comp_def]
    · have h1 : ∀ x : A × S,
          (OracleAdv.run (multiOracle orc) (c x.1) (Function.update m j x.2)).map Prod.fst =
            G.keyDist.bind fun k => (OracleAdv.run (multiOracle orc) (c x.1)
              (Function.update (Function.update m j x.2) i (emb k G.init))).map Prod.fst :=
        fun x => ih x.1 _ (by rw [Function.update_of_ne (Ne.symm hj)]; exact hm)
      simp only [OracleAdv.run_query, multiOracle, PMF.map_bind, PMF.bind_map,
        Function.comp_def, Function.update_of_ne hj, h1]
      refine (PMF.bind_comm _ _ _).trans
        (congrArg _ (funext fun k => congrArg _ (funext fun x => ?_)))
      rw [Function.update_comm (Ne.symm hj)]

/-- **The multi-session game and one session.** The acceptance probability of `B` in the
multi-session game is the acceptance probability of `sessRed orc i s₀ B` in the game `G` of
session `i`. -/
theorem accept_multiGame (s₀ : S)
    (hfresh : ∀ q, orc i s₀ q = G.keyDist.bind fun k => orc i (emb k G.init) q)
    (hemb : ∀ k t q, orc i (emb k t) q = (G.oracle k t q).map fun x => (x.1, emb k x.2))
    (B : OracleAdv (ℕ × Q) A Bool) :
    (multiGame orc s₀).accept B = G.accept (sessRed orc i s₀ B) := by
  simp only [accept, multiGame, PMF.pure_bind, sessRed, OracleAdv.run_simulate_fst]
  rw [run_multiOracle_lazy orc i G emb s₀ hfresh B _ rfl]
  congr 1
  exact congrArg _ (funext fun k => run_multiOracle_emb orc i G emb hemb k B _ _)

end Slot

/-! ## The session hybrid -/

section Hybrid

variable (G₀ G₁ : KeyedGame Q A)

/-- The state of a session: the key and state of `G₀` once sampled, and of `G₁`. -/
abbrev SessSt : Type := Option (G₀.Key × G₀.State) × Option (G₁.Key × G₁.State)

/-- The oracle of `G` on a lazily keyed state: with no state, the key is sampled and the oracle
runs from the initial state. -/
noncomputable def lazyOracle (G : KeyedGame Q A) :
    Option (G.Key × G.State) → Q → PMF (A × (G.Key × G.State))
  | none, q => G.keyDist.bind fun k => (G.oracle k G.init q).map fun x => (x.1, (k, x.2))
  | some (k, t), q => (G.oracle k t q).map fun x => (x.1, (k, x.2))

/-- A session of `G₀`, keyed lazily. -/
noncomputable def realSess (s : SessSt G₀ G₁) (q : Q) : PMF (A × SessSt G₀ G₁) :=
  (G₀.lazyOracle s.1 q).map fun x => (x.1, (some x.2, s.2))

/-- A session of `G₁`, keyed lazily. -/
noncomputable def idealSess (s : SessSt G₀ G₁) (q : Q) : PMF (A × SessSt G₀ G₁) :=
  (G₁.lazyOracle s.2 q).map fun x => (x.1, (s.1, some x.2))

/-- The session oracles of the hybrid world `i`: `G₁` for the sessions `j < i`, `G₀` for the
others. -/
noncomputable def hybOrc (i j : ℕ) : SessSt G₀ G₁ → Q → PMF (A × SessSt G₀ G₁) :=
  if j < i then idealSess G₀ G₁ else realSess G₀ G₁

/-- The hybrid world `i`: the multi-session game in which the sessions `j < i` run `G₁` and the
others run `G₀`. -/
noncomputable def hybGame (i : ℕ) : KeyedGame (ℕ × Q) A :=
  multiGame (hybOrc G₀ G₁ i) (none, none)

/-- The reduction of hop `i`: the adversary `B` of the multi-session game with the sessions
`j < i` simulated by `G₁`, the sessions `j > i` simulated by `G₀`, and session `i` forwarded
to the oracle. -/
noncomputable def sessReduction (i : ℕ) (B : OracleAdv (ℕ × Q) A Bool) : OracleAdv Q A Bool :=
  sessRed (hybOrc G₀ G₁ i) i (none, none) B

/-- **One session hop.** The advantage of `B` between the hybrid worlds `i` and `i + 1` is the
advantage of `sessReduction G₀ G₁ i B` between `G₀` and `G₁`. -/
theorem advantage_hybGame (i : ℕ) (B : OracleAdv (ℕ × Q) A Bool) :
    advantage (hybGame G₀ G₁ i) (hybGame G₀ G₁ (i + 1)) B =
      advantage G₀ G₁ (sessReduction G₀ G₁ i B) := by
  have h₀ : (hybGame G₀ G₁ i).accept B = G₀.accept (sessReduction G₀ G₁ i B) :=
    accept_multiGame (hybOrc G₀ G₁ i) i G₀ (fun k t => (some (k, t), none)) (none, none)
      (fun q => by simp [hybOrc, realSess, lazyOracle, PMF.map_bind])
      (fun k t q => by simp [hybOrc, realSess, lazyOracle, PMF.map_comp, Function.comp_def]) B
  have h₁ : (hybGame G₀ G₁ (i + 1)).accept B = G₁.accept (sessReduction G₀ G₁ i B) := by
    rw [sessReduction, sessRed_congr (orc' := hybOrc G₀ G₁ (i + 1)) (fun j hj => by
      simp only [hybOrc]; congr 1; grind)]
    exact accept_multiGame (hybOrc G₀ G₁ (i + 1)) i G₁ (fun k t => (none, some (k, t)))
      (none, none)
      (fun q => by simp [hybOrc, idealSess, lazyOracle, PMF.map_bind])
      (fun k t q => by simp [hybOrc, idealSess, lazyOracle, PMF.map_comp, Function.comp_def]) B
  rw [advantage, advantage, h₀, h₁]

end Hybrid

end KeyedGame

section Sessions

variable {τ E O Q A : Type}

/-- **Realization of one session hop.** The system of `P` over the hybrid world `i` realizes the
system over the world `i + 1` with bound, at `Z`, the advantage between `G₀` and `G₁` of the
session reduction `sessReduction G₀ G₁ i (P.reduction Z)`. -/
theorem Realizes.ofSession (P : OProt τ E O (ℕ × Q) A) (G₀ G₁ : KeyedGame Q A) (i : ℕ) :
    Realizes (P.sys (KeyedGame.hybGame G₀ G₁ i)) (P.sys (KeyedGame.hybGame G₀ G₁ (i + 1)))
      fun _ Z => KeyedGame.advantage G₀ G₁
        (KeyedGame.sessReduction G₀ G₁ i (P.reduction Z)) := by
  have h := Realizes.ofOracleGame P (KeyedGame.hybGame G₀ G₁ i)
    (KeyedGame.hybGame G₀ G₁ (i + 1))
  simpa only [KeyedGame.advantage_hybGame] using h

/-- **Session hybrid.** The system of `P` over the multi-session real world realizes the system
over the hybrid world `n`, in which the first `n` sessions run `G₁`, with bound
`∑_{i<n} advantage G₀ G₁ (sessReduction G₀ G₁ i (P.reduction Z))`. -/
theorem Realizes.sessions (P : OProt τ E O (ℕ × Q) A) (G₀ G₁ : KeyedGame Q A) (n : ℕ) :
    Realizes (P.sys (KeyedGame.hybGame G₀ G₁ 0)) (P.sys (KeyedGame.hybGame G₀ G₁ n))
      fun _ Z => ∑ i ∈ Finset.range n, KeyedGame.advantage G₀ G₁
        (KeyedGame.sessReduction G₀ G₁ i (P.reduction Z)) :=
  Realizes.hybrid (fun i => P.sys (KeyedGame.hybGame G₀ G₁ i))
    (fun i _ Z => KeyedGame.advantage G₀ G₁ (KeyedGame.sessReduction G₀ G₁ i (P.reduction Z)))
    n fun i _ => Realizes.ofSession P G₀ G₁ i

/-- **Round-indexed session hybrid.** If the system of `P` over the hybrid world at the number
of rounds of `Z` is at distance at most `c ζ Z` from `I`, then the system of `P` over the
multi-session real world realizes `I` with bound
`∑_{i<Z.rounds} advantage G₀ G₁ (sessReduction G₀ G₁ i (P.reduction Z)) + c ζ Z`. -/
theorem Realizes.sessions_rounds {υ : Type} (P : OProt τ E O (ℕ × Q) A)
    (G₀ G₁ : KeyedGame Q A) (I : Sys υ E O) (c : (ζ : Type) → Env (Strat ζ E O) ζ → ℝ≥0∞)
    (hend : ∀ (ζ : Type) (Z : Env (Strat ζ E O) ζ),
      adv (P.sys (KeyedGame.hybGame G₀ G₁ Z.input.rounds)) I Z ≤ c ζ Z) :
    Realizes (P.sys (KeyedGame.hybGame G₀ G₁ 0)) I fun ζ Z =>
      ∑ i ∈ Finset.range Z.input.rounds, KeyedGame.advantage G₀ G₁
        (KeyedGame.sessReduction G₀ G₁ i (P.reduction Z)) + c ζ Z :=
  Realizes.hybrid_rounds (fun i => P.sys (KeyedGame.hybGame G₀ G₁ i)) I
    (fun i _ Z => KeyedGame.advantage G₀ G₁ (KeyedGame.sessReduction G₀ G₁ i (P.reduction Z)))
    c (fun i => Realizes.ofSession P G₀ G₁ i) hend

end Sessions

end CatCrypt.Crypto.UCTransparent
