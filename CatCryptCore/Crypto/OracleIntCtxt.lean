/-
Copyright (c) 2026 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.OracleSimulation
public import CatCryptCore.ForMathlib.PMFUniform

/-!
# The multi-key INT-CTXT game of a symmetric encryption with explicit randomness

A symmetric encryption `SEncScheme` with explicit randomness, `enc κ ρ m` and
`dec κ c : Option M`, and its multi-key ciphertext-integrity game as an oracle game. The
adversary queries `IcQuery.enc i j m` (encrypt `m` under the key `κ i` with the randomness
`ρ j`) and `IcQuery.dec i c` (decrypt `c` under `κ i`); the oracle state `IcRec` is the list of
the ciphertexts produced, with their key index, and the flag of a successful decryption at a
ciphertext not produced under its key index.

## Main definitions

* `SEncScheme`, `IcQuery`, `IcAns`, `IcRec` — the scheme, the queries, the answers and the
  oracle state.
* `icStep`, `icOracle` — one query of the oracle at the keys `κ` and the randomness `ρ`, and
  the oracle as a deterministic probabilistic oracle.
* `IntCtxt_Advantage Sch B` — the probability that the flag is set at the end of the run of
  `B`, over uniform keys `κ : I → K` and uniform randomness `ρ : J → R`.
-/

@[expose] public section

namespace CatCrypt.Crypto.IntCtxt

open CatCrypt.Crypto
open scoped ENNReal

/-- A symmetric encryption with explicit randomness: `enc κ ρ m` under the key `κ` with the
randomness `ρ`, and `dec κ c`, `none` on failure. -/
structure SEncScheme (K R M Ct : Type) where
  /-- Encryption. -/
  enc : K → R → M → Ct
  /-- Decryption. -/
  dec : K → Ct → Option M

/-- Queries of the INT-CTXT game: an encryption of `m` under the key index `i` with the
randomness index `j`, and a decryption of `c` under the key index `i`. -/
inductive IcQuery (I J M Ct : Type) where
  /-- Encryption query. -/
  | enc (i : I) (j : J) (m : M)
  /-- Decryption query. -/
  | dec (i : I) (c : Ct)

/-- Answers of the INT-CTXT game: a ciphertext, or a decryption. -/
abbrev IcAns (M Ct : Type) := Ct ⊕ Option M

/-- The state of the INT-CTXT oracle: the ciphertexts produced, with their key index, and the
flag of a successful decryption at a ciphertext not produced under its key index. -/
abbrev IcRec (I Ct : Type) := List (I × Ct) × Bool

variable {K R M Ct I J : Type}

open Classical in
/-- One query to the INT-CTXT oracle at the keys `κ` and the randomness `ρ`. -/
noncomputable def icStep (Sch : SEncScheme K R M Ct) (κ : I → K) (ρ : J → R)
    (s : IcRec I Ct) : IcQuery I J M Ct → IcAns M Ct × IcRec I Ct
  | .enc i j m => (.inl (Sch.enc (κ i) (ρ j) m), ((i, Sch.enc (κ i) (ρ j) m) :: s.1, s.2))
  | .dec i c => (.inr (Sch.dec (κ i) c),
      (s.1, s.2 || (decide ((i, c) ∉ s.1) && (Sch.dec (κ i) c).isSome)))

/-- The INT-CTXT oracle at the keys `κ` and the randomness `ρ`. -/
noncomputable def icOracle (Sch : SEncScheme K R M Ct) (κ : I → K) (ρ : J → R)
    (s : IcRec I Ct) (q : IcQuery I J M Ct) : PMF (IcAns M Ct × IcRec I Ct) :=
  PMF.pure (icStep Sch κ ρ s q)

/-- **The multi-key INT-CTXT advantage** of an adversary `B` with encryption and decryption
queries: uniform keys `κ : I → K` and randomness `ρ : J → R`, and the probability that some
decryption query succeeds at a ciphertext that no encryption query under its key index
produced. -/
noncomputable def IntCtxt_Advantage [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
    [Fintype K] [Nonempty K] [Fintype R] [Nonempty R] (Sch : SEncScheme K R M Ct)
    (B : OracleAdv (IcQuery I J M Ct) (IcAns M Ct) Bool) : ℝ≥0∞ :=
  ((PMF.uniformFintype (I → K)).bind fun κ => (PMF.uniformFintype (J → R)).bind fun ρ =>
    (OracleAdv.run (icOracle Sch κ ρ) B ([], false)).map fun x => x.2.2) true

end CatCrypt.Crypto.IntCtxt
