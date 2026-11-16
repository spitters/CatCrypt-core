/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OracleForkingLemma
public import CatCryptCore.Crypto.SchnorrForking
public import CatCryptCore.Crypto.PRPPRFSwitching
public import CatCryptCore.Crypto.FiatShamirROM.Schnorr

/-!
# EUF-CMA security of Schnorr signatures in the random-oracle model: the game

The EUF-CMA game for Schnorr signatures over a `GroupParam` with the hash
function `H : G × M → Scalar` modelled as a random oracle. The adversary is an
adaptive oracle adversary (`OracleAdv`) with hash queries `inl (a, m)` and
signing queries `inr m`, making at most `qH` hash queries and `qS` signing
queries on every path (`IsQueryBound₂`).

The challenger keeps the oracle state `Tables × Bool`:

* `hash` — the random-oracle entries created by hash queries, in creation order;
* `prog` — the random-oracle entries created by signing queries;
* `signed` — the messages submitted to the signing oracle;
* the flag — set when a signing query needs the oracle value at a point that is
  already defined.

A hash query returns the recorded value of its point or samples a fresh uniform
value and records it. The real signing oracle samples `r` and `e`, defines
`H(g^r, m) := e` and answers `(g^r, r + e·sk)`; when the point is already
defined it sets the flag. At the end the challenger queries `H(a*, m*)` for the
forgery `(m*, (a*, z*))` and the adversary wins when `g^z* = a* · pk^H(a*, m*)`
and `m*` was never signed.

This game is the generic Fiat–Shamir game `FiatShamirROM.eufcmaGame` at
`FiatShamirROM.schnorrSigma gp` (`FiatShamirROM.eufcmaAdvantage_toGeneric`), and
its bound is the generic Fiat–Shamir theorem (`SchnorrROM.schnorr_rom_eufcma`).

## Main definitions

* `Adversary gp M qH qS` — EUF-CMA adversaries with at most `qH` hash and `qS`
  signing queries on every path (`OracleForking.IsQueryBound₂`)
* `realStep sk` — the real oracle
* `eufcmaGame A`, `eufcmaAdvantage A` — the EUF-CMA game and advantage

## Main results

* `prTrue_gameDist` — the advantage in a game built by `gameDist` as an average
  over secret keys
-/

@[expose] public section

set_option autoImplicit false

namespace CatCrypt.Crypto.SchnorrROM

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto CatCrypt.Examples.Schnorr
open CatCrypt.Crypto.OracleForking CatCrypt.Crypto.SchnorrForking
open scoped ENNReal

export CatCrypt.Crypto.OracleForking (IsQueryBound₂)

variable (gp : GroupParam) (M : Type) [DecidableEq M]

/-! ## Oracle state -/

/-- A query: `inl (a, m)` asks the random oracle at `(a, m)`, `inr m` asks for a
signature on `m`. -/
abbrev Query := (gp.G × M) ⊕ M

/-- An answer: `inl e` for a hash query, `inr (a, z)` for a signing query. -/
abbrev Answer := gp.Scalar ⊕ (gp.G × gp.Scalar)

/-- A forgery `(m, (a, z))`. -/
abbrev Forgery := M × (gp.G × gp.Scalar)

/-- The challenger's tables. -/
structure Tables where
  /-- Random-oracle entries created by hash queries, oldest first. -/
  hash : List ((gp.G × M) × gp.Scalar)
  /-- Random-oracle entries created by signing queries, oldest first. -/
  prog : List ((gp.G × M) × gp.Scalar)
  /-- Messages submitted to the signing oracle. -/
  signed : List M

variable {gp M}

/-- The empty tables. -/
def Tables.empty : Tables gp M := ⟨[], [], []⟩

/-- Position of the first entry at point `k`. -/
def findKey (l : List ((gp.G × M) × gp.Scalar)) (k : gp.G × M) : Option ℕ :=
  l.findIdx? fun p => decide (p.1 = k)

/-- Value of the first entry at point `k`. -/
def lookupIn (l : List ((gp.G × M) × gp.Scalar)) (k : gp.G × M) : Option gp.Scalar :=
  (findKey l k).bind fun i => l[i]?.map Prod.snd

/-- The random-oracle value at `k`, if defined. -/
def Tables.lookup (t : Tables gp M) (k : gp.G × M) : Option gp.Scalar :=
  (lookupIn t.prog k).or (lookupIn t.hash k)

/-! ## Oracles -/

/-- A hash query: the recorded value, or a fresh uniform value recorded in `hash`. -/
noncomputable def hashStep (t : Tables gp M) (b : Bool) (k : gp.G × M) :
    Step (Answer gp) (Tables gp M × Bool) gp.Scalar :=
  match t.lookup k with
  | some e => .plain (PMF.pure (.inl e, (t, b)))
  | none => .fresh fun e => (.inl e, ({ t with hash := t.hash ++ [(k, e)] }, b))

/-- The real signing oracle on `m` with secret key `sk`, from the sampled pair
`(r, e)`: commitment `g^r`, oracle value `H(g^r, m) := e`, response `r + e·sk`.
If `H(g^r, m)` is already defined, the recorded value is used and the flag is
set. -/
def realSignOut (sk : gp.Scalar) (t : Tables gp M) (b : Bool) (m : M) (r e : gp.Scalar) :
    Answer gp × (Tables gp M × Bool) :=
  match t.lookup (gp.exp r, m) with
  | some e' => (.inr (gp.exp r, gp.scalarAdd r (gp.scalarMul e' sk)),
      ({ t with signed := t.signed ++ [m] }, true))
  | none => (.inr (gp.exp r, gp.scalarAdd r (gp.scalarMul e sk)),
      ({ t with prog := t.prog ++ [((gp.exp r, m), e)], signed := t.signed ++ [m] }, b))

/-- Two independent uniform scalars mapped by `F`. -/
noncomputable def sample₂ {β : Type} (F : gp.Scalar → gp.Scalar → β) : PMF β :=
  (PMF.uniformFintype gp.Scalar).bind fun x =>
    (PMF.uniformFintype gp.Scalar).map fun y => F x y

/-- The real oracle with secret key `sk`. -/
noncomputable def realStep (sk : gp.Scalar) (s : Tables gp M × Bool) :
    Query gp M → Step (Answer gp) (Tables gp M × Bool) gp.Scalar
  | .inl k => hashStep s.1 s.2 k
  | .inr m => .plain (sample₂ (realSignOut sk s.1 s.2 m))

/-! ## Adversaries and games -/

variable (gp M) in
/-- An EUF-CMA adversary in the random-oracle model: on the public key, an
adaptive oracle adversary outputting a forgery with at most `qH` hash queries
and `qS` signing queries. -/
structure Adversary (qH qS : ℕ) : Type 1 where
  /-- The adversary on public key `pk`. -/
  run : gp.G → OracleAdv (Query gp M) (Answer gp) (Forgery gp M)
  /-- The query bounds. -/
  isQueryBound : ∀ pk, IsQueryBound₂ (run pk) qH qS

/-- The adversary followed by the challenger's hash query on the forgery point. -/
def withVerify : OracleAdv (Query gp M) (Answer gp) (Forgery gp M) →
    OracleAdv (Query gp M) (Answer gp) (Forgery gp M)
  | .ret (m, a, z) => .query (.inl (a, m)) fun _ => .ret (m, a, z)
  | .rand p k => .rand p fun b => withVerify (k b)
  | .query d k => .query d fun r => withVerify (k r)

/-- The winning condition on the final forgery and tables: the message was never
signed and `g^z = a · pk^H(a, m)`. -/
def wins (pk : gp.G) (y : Forgery gp M × (Tables gp M × Bool)) : Bool :=
  !(y.2.1.signed.contains y.1.1) &&
    match y.2.1.lookup (y.1.2.1, y.1.1) with
    | some e => schnorrVerifyROM gp pk y.1.2.1 e y.1.2.2
    | none => false

/-- The distribution of the EUF-CMA experiment against the oracle family `O`
indexed by the secret key. -/
noncomputable def gameDist (O : gp.Scalar → Tables gp M × Bool → Query gp M →
    Step (Answer gp) (Tables gp M × Bool) gp.Scalar) {qH qS : ℕ} (A : Adversary gp M qH qS) :
    PMF Bool :=
  (PMF.uniformFintype gp.Scalar).bind fun sk =>
    (OracleAdv.run (toOracle (O sk)) (withVerify (A.run (gp.exp sk)))
      (Tables.empty, false)).map (wins (gp.exp sk))

/-- The EUF-CMA game in the random-oracle model. -/
noncomputable def eufcmaGame {qH qS : ℕ} (A : Adversary gp M qH qS) : SPComp Bool :=
  liftPMF (gameDist realStep A)

/-- The EUF-CMA advantage in the random-oracle model. -/
noncomputable def eufcmaAdvantage {qH qS : ℕ} (A : Adversary gp M qH qS) : ℝ≥0∞ :=
  prTrue (eufcmaGame A) Heap.empty

/-! ## Sampling and the advantage as an average -/

omit [DecidableEq M] in
theorem sample₂_bind {β γ : Type} (F : gp.Scalar → gp.Scalar → β) (g : β → PMF γ) :
    (sample₂ F).bind g = (PMF.uniformFintype gp.Scalar).bind fun x =>
      (PMF.uniformFintype gp.Scalar).bind fun y => g (F x y) := by
  simp only [sample₂, PMF.bind_bind, PMF.bind_map, Function.comp_def]

/-- The advantage in a game built by `gameDist` as an average over secret keys. -/
theorem prTrue_gameDist (O : gp.Scalar → Tables gp M × Bool → Query gp M →
    Step (Answer gp) (Tables gp M × Bool) gp.Scalar) {qH qS : ℕ} (A : Adversary gp M qH qS) :
    prTrue (liftPMF (gameDist O A)) Heap.empty =
      ∑' sk, PMF.uniformFintype gp.Scalar sk *
        (OracleAdv.run (toOracle (O sk)) (withVerify (A.run (gp.exp sk)))
          (Tables.empty, false)).toOuterMeasure {y | wins (gp.exp sk) y = true} := by
  rw [prTrue_liftPMF_toOuterMeasure]
  simp only [gameDist, PMF.toOuterMeasure_bind_apply, PMF.toOuterMeasure_map_apply]
  rfl

end CatCrypt.Crypto.SchnorrROM
