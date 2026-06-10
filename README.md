# CatCrypt Core

The core of CatCrypt: machine-checked foundations for game-based
cryptographic security proofs in Lean 4 — sub-distributions, a
stateful-probabilistic program monad, probabilistic relational Hoare
logic, state-separated packages, proof automation, forking lemmas, and
Montgomery-curve mathematics.

For the design lineage and related work, see [DESIGN.md](DESIGN.md).

This is the **minimal-basis release**. The universal-composability theory,
concurrent UC, quantum verification, the verified compilation pipeline, and
the full catalogue of concrete protocols live in separate, larger
distributions.

## Contents

| Layer | Modules |
|---|---|
| Probability | `Prob/*` — sub-distributions, couplings, support, birthday bound, Schwartz–Zippel |
| Core | `Core/*` — typed heap, `SPComp` stateful-probabilistic monad, `SPTree` syntactic trees |
| Relational | `Relational/*` — pRHL judgment, sync/frame/reorder rules |
| Package | `Package/*` — interface-based package algebra |
| Category | `Category/*` — Kleisli of SPComp, family bicategory, cocartesian / affine structure |
| Deep embedding | `Deep/*` — syntactic package calculus with semantic evaluation, `SPComp` → `RawCode` reflection |
| Bridge | `Bridge/*` — deep-to-shallow semantic bridge |
| Tactics | `Tactics/*` — pRHL automation (sync, invariant, WP/SP, ProofFrog, lazy sampling, remember/forget, triangle chaining, …) |
| Crypto foundation | `Crypto/{Game,Advantage,SDist,SecurityDefs,Encryption,HybridArgument,NomAdvantage}.lean` |
| Forking | `Crypto/ForkingLemma.lean`, `Crypto/GeneralForkingLemma.lean` — Pointcheval–Stern and Bellare–Neven |
| Assumptions | `Crypto/Assumptions/*` — DDH, CDH, GapDH, DL, t-SDH, q-SDH, CoCDH, ODH, CR, OWF, PRP, RSA, AEAD, MAC |
| VCVio bridge | `Crypto/Bridges/VCVioBridge/{Monad,State,Linking,Relational}.lean` + examples |
| Arklib interface | `Crypto/Bridges/ArkLibTypes.lean` — `ArgumentSoundness`, `KnowledgeSoundness` + reduction composition |
| Curve math | `Crypto/KeyAgreement/{MontgomeryLadder,MontgomeryAsWeierstrass,MontgomeryXOnly,Curve25519}.lean` |

## Build

Requires [elan](https://github.com/leanprover/elan). The pinned toolchain is
`leanprover/lean4:v4.29.1` (see `lean-toolchain`).

```
lake exe cache get    # optional: pull mathlib cache
lake build
```

A full cold build compiles Mathlib + VCVio + CatCrypt-core in roughly an hour;
with a warm cache, CatCrypt-core itself builds in a few minutes.

## Dependencies

Pinned in `lakefile.lean` and `lake-manifest.json`:

- [Mathlib](https://github.com/leanprover-community/mathlib4) `v4.29.1`
- [VCVio](https://github.com/Verified-zkEVM/VCV-io) `v4.29.0` (used by `Bridges/VCVioBridge/*`)

## Trust edges

The library contains no `sorry`. The single declared axiom is:

- `curve25519Prime_prime` (`Crypto/KeyAgreement/Curve25519.lean`) — primality
  of `2²⁵⁵ − 19`. Standard trust edge (fiat-crypto, AUCurves).

In addition, `MontgomeryXOnly.MontyCurveGroup` is a typeclass hypothesis (not
a global axiom): the Montgomery group law is taken as a parameter, and the
Weierstrass transport in `MontgomeryAsWeierstrass.lean` is the intended
discharge. The PRP/PRF switching theorem is not formalised; bounds that
involve it (`Crypto/Assumptions/PRP.lean`) carry the birthday term
explicitly in their statements.

## Relation to SSProve

The program logic, package algebra, and the `ssprove_*` tactic family port
the design of [SSProve](https://github.com/SSProve/ssprove), the Coq/Rocq
framework for modular cryptographic proofs:

> P. G. Haselwarter, E. Rivas, A. Van Muylder, T. Winterhalter, C. Abate,
> N. Sidorenco, C. Hriţcu, K. Maillard, B. Spitters.
> *SSProve: A Foundational Framework for Modular Cryptographic Proofs in Coq.*
> ACM Transactions on Programming Languages and Systems 45(3), 2023.
> [doi:10.1145/3594735](https://doi.org/10.1145/3594735)

## Citing

See `CITATION.cff`. The accompanying paper:

> B. Spitters. *CatCrypt: From Rust to Cryptographic Security in Lean.*
> Cryptology ePrint Archive, Paper 2026/604.
> <https://eprint.iacr.org/2026/604.pdf>

## License

MIT. See `LICENSE`.
