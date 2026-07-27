# CatCrypt Core

> 🚧 **Under active development.** CatCrypt is still evolving rapidly — APIs,
> module organization, and dependencies may change between releases.

The core of CatCrypt: machine-checked foundations for game-based
cryptographic security proofs in Lean 4 — sub-distributions, a
stateful-probabilistic program monad, probabilistic relational Hoare
logic, state-separated packages, proof automation, forking lemmas, and
Montgomery-curve mathematics.

📖 **Documentation:** [hosted API reference](https://spitters.github.io/CatCrypt-core/) ·
[design & influences](DESIGN.md)

This is the **minimal-basis release**. The universal-composability theory,
concurrent UC, quantum verification, the verified compilation pipeline, and
the full catalogue of concrete protocols live in separate, larger
distributions.

Module names live under the `CatCryptCore.*` root (single entry point:
`import CatCryptCore`), so the library coexists with any package that has its
own `CatCrypt.*` module tree. Declared *namespaces* are `CatCrypt.*`:
`open CatCrypt.Core`, `CatCrypt.Core.SPComp`, etc. Paths in the table below
are relative to `CatCryptCore/`.

## Contents

| Layer | Modules |
|---|---|
| Probability | `Prob/*` — sub-distributions, couplings, support, birthday bound, Schwartz–Zippel |
| Core | `Core/*` — typed heap (finite- and countable-typed locations), `SPComp` stateful-probabilistic monad, `SPTree` syntactic trees |
| Relational | `Relational/*` — pRHL judgment, sync/frame/reorder rules |
| Non-uniform | `NonUniform/*` — sampling from an arbitrary sub-distribution, conditioning, products, the unbounded `while` loop and its pHL / pRHL rules |
| Package | `Package/*` — interface-based package algebra |
| Category | `Category/*` — Kleisli of SPComp, family bicategory, cocartesian / affine structure |
| Deep embedding | `Deep/*` — syntactic package calculus with semantic evaluation, `SPComp` → `RawCode` reflection |
| Bridge | `Bridge/*` — deep-to-shallow semantic bridge |
| Tactics | `Tactics/*` — pRHL automation (sync, invariant, WP/SP, ProofFrog, lazy sampling, remember/forget, triangle chaining, …) |
| Crypto foundation | `Crypto/{Game,Advantage,SDist,SecurityDefs,Encryption,HybridArgument,NomAdvantage}.lean` |
| Forking | `Crypto/ForkingLemma.lean`, `Crypto/GeneralForkingLemma.lean` — Pointcheval–Stern and Bellare–Neven |
| Up-to-bad | `Crypto/BadEvent.lean` — identical-until-bad / fundamental lemma of game-playing, bad-event union bounds, hybrid + up-to-bad, and lazy/eager sampling (`Tactics/UpToBad.lean` drives it) |
| Assumptions | `Crypto/Assumptions/*` — DDH, CDH, GapDH, DL, t-SDH, q-SDH, CoCDH, ODH, CR, OWF, PRP, RSA, AEAD, MAC |
| Curve math | `Crypto/KeyAgreement/{MontgomeryLadder,MontgomeryAsWeierstrass,MontgomeryXOnly,Curve25519}.lean` |

## Build

See [BUILDING.md](BUILDING.md) for building the library and the documentation.

## Dependencies

Pinned in `lakefile.lean` and `lake-manifest.json`:

- [Mathlib](https://github.com/leanprover-community/mathlib4) `v4.30.0`
- [nominal-lean](https://github.com/spitters/nominal-lean) — the nominal-sets layer (`Nominal/`)

## Documentation

- **API reference:** [doc-gen4](https://spitters.github.io/CatCrypt-core/)
- **Design and influences:** [DESIGN.md](DESIGN.md) ·
  **Changelog:** [CHANGELOG.md](CHANGELOG.md) ·
  **Contributing:** [CONTRIBUTING.md](CONTRIBUTING.md)

To build the manual or the API reference locally, see [BUILDING.md](BUILDING.md).

## Relation to SSProve

The program logic, package algebra, and the `ssprove_*` tactic family port
the design of [SSProve](https://github.com/SSProve/ssprove), the Coq/Rocq
framework for modular cryptographic proofs:

> P. G. Haselwarter, E. Rivas, A. Van Muylder, T. Winterhalter, C. Abate,
> N. Sidorenco, C. Hriţcu, K. Maillard, B. Spitters.
> *SSProve: A Foundational Framework for Modular Cryptographic Proofs in Coq.*
> ACM Transactions on Programming Languages and Systems 45(3), 2023.
> [doi:10.1145/3594735](https://doi.org/10.1145/3594735)

## Related projects

- [hax-lean](https://github.com/spitters/hax-lean) — a partially verified version
  of [hax](https://github.com/hacspec/hax), a tool for high-assurance translation of
  a large subset of Rust into formal languages.

## Citing

See `CITATION.cff`. The accompanying paper:

> B. Spitters. *CatCrypt: From Rust to Cryptographic Security in Lean.*
> Cryptology ePrint Archive, Paper 2026/604.
> <https://eprint.iacr.org/2026/604.pdf>

## License

MIT. See `LICENSE`.
