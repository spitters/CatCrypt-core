/-
Copyright (c) 2025 CatCrypt Contributors. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: CatCrypt Contributors
-/
module

public import CatCryptCore.Crypto.CryptoWord

/-!
# Gap Diffie-Hellman (GapDH) Assumption

This file defines the gap Diffie–Hellman problem parametrically over any
`SampleableType W`.

## GapDH Game

The adversary receives two public keys `X = pub_a`, `Y = pub_b` and oracle
access to the decision Diffie–Hellman predicate `(X', Y', Z') ↦ decide
(Z' = cdh X' Y')`. It outputs a group element `Z` and wins when
`Z = cdh X Y` (Okamoto–Pointcheval 2001, Def. 5). The oracle is a
deterministic function of its query, so it is given to the adversary as a
function `W → W → W → Bool`.

`GapDHDef` carries the Diffie–Hellman function `cdh` on public keys, which the
oracle evaluates, and the key-agreement function `dh priv pub` used by
protocols. The structure records no relation between them; an instance over a
group with generator `g` sets `cdh (g^a) (g^b) = g^(ab)` and
`dh a (g^b) = g^(ab)`.

## Main definitions

* `GapDHDef` — key generation, key agreement `dh` and the function `cdh`
* `ddhOracle` — the decision Diffie–Hellman oracle of `cdh`
* `GapDH_Game` — the search game with oracle access
* `GapDH_Advantage` — the probability that the adversary outputs `cdh X Y`

## Usage in WireGuard

WireGuard uses 4 DH operations (X25519), each contributing one `ε_gdh`:
1. DH(e_I, s_R) — initiator ephemeral × responder static
2. DH(s_I, s_R) — static-static
3. DH(e_R, e_I) — ephemeral-ephemeral
4. DH(e_R, s_I) — responder ephemeral × initiator static

**Relationship to other assumptions:** a CDH adversary is a GapDH adversary
that ignores its oracle, so GapDH hardness implies CDH hardness. DDH hardness
does not imply GapDH hardness: in groups with an efficient DDH test (pairing
groups), DDH is easy while GapDH can be hard.

**Equivalent formalizations:**
- CryptoVerif: `GDH(G, Z, g, exp, exp', mult)` macro (used in WireGuard proof)

## References

* Okamoto, Pointcheval. *The Gap-Problems: A New Class of Problems for the
  Security of Cryptographic Schemes.* PKC 2001, Def. 5.
* Lipp, Blanchet, Bhargavan. *A Mechanised Cryptographic Proof of the
  WireGuard Virtual Private Network Protocol.* EuroS&P 2019.
-/

@[expose] public section

namespace CatCrypt.Crypto.Assumptions

open CatCrypt.Core CatCrypt.Prob CatCrypt.Crypto
open scoped ENNReal

variable {W : Type} [SampleableType W]

/-! ## GapDH Definition -/

/-- Abstract gap Diffie–Hellman group, parametric over `SampleableType W`.

- `dh priv pub` models the DH key agreement operation
- `cdh X Y` is the Diffie–Hellman function on public keys, evaluated by the
  decision oracle and defining the winning condition
- `keygen` samples a key pair `(private, public)` -/
structure GapDHDef (W : Type) [SampleableType W] where
  /-- DH key agreement: `dh(private_key, public_key)` → shared_secret.
  Models X25519 scalar multiplication. -/
  dh : W → W → W
  /-- Diffie–Hellman function on public keys: `cdh (g^a) (g^b) = g^(ab)`. -/
  cdh : W → W → W
  /-- Key generation: produces `(private_key, public_key)`.
  Models X25519 key generation. -/
  keygen : SPComp (W × W)
  /-- Key generation is heap-independent. -/
  keygen_isPure : SPComp.IsPure keygen

/-! ## GapDH Game -/

/-- The decision Diffie–Hellman oracle of `G`: `(X, Y, Z) ↦ decide (Z = cdh X Y)`. -/
def ddhOracle (G : GapDHDef W) (X Y Z : W) : Bool :=
  decide (Z = G.cdh X Y)

/-- GapDH adversary: given the decision oracle and two public keys, output a
candidate for their Diffie–Hellman value. -/
abbrev GapDH_Adversary (W : Type) := (W → W → W → Bool) → W → W → SPComp W

/-- GapDH game: sample two key pairs, run the adversary on the public keys
with the decision oracle, and return whether its output is `cdh pub_a pub_b`. -/
noncomputable def GapDH_Game (G : GapDHDef W) (A : GapDH_Adversary W) : SPComp Bool := do
  let ⟨_a, pub_a⟩ ← G.keygen
  let ⟨_b, pub_b⟩ ← G.keygen
  let Z ← A (ddhOracle G) pub_a pub_b
  pure (decide (Z = G.cdh pub_a pub_b))

/-- GapDH advantage: the probability that `A` outputs the Diffie–Hellman value
of the two public keys. -/
noncomputable def GapDH_Advantage (G : GapDHDef W) (A : GapDH_Adversary W) : ℝ≥0∞ :=
  prTrue (GapDH_Game G A) Heap.empty

/-! ## IsPure Proof -/

theorem GapDH_Game_isPure (G : GapDHDef W) (A : GapDH_Adversary W)
    (hA : ∀ x y, SPComp.IsPure (A (ddhOracle G) x y)) :
    SPComp.IsPure (GapDH_Game G A) := by
  unfold GapDH_Game
  apply SPComp.bind_isPure G.keygen_isPure; intro ⟨_a, pub_a⟩
  apply SPComp.bind_isPure G.keygen_isPure; intro ⟨_b, pub_b⟩
  apply SPComp.bind_isPure (hA pub_a pub_b); intro Z
  exact SPComp.pure_isPure _

end CatCrypt.Crypto.Assumptions
