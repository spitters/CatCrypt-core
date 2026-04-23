# CatCrypt Core

A Lean 4 port of the SSP program-logic and package-algebra stack, with native
forking lemmas, an Arklib-compatible soundness interface, a VCVio interop
bridge, classical Montgomery-curve mathematics, and a verified
RustCmd → Jasmin compilation pipeline.

This is the **minimal-basis release**. The universal-composability theory,
concurrent UC, quantum verification, libjade industrial bridge, and the full
catalogue of concrete protocols live in a separate, larger distribution.

## Contents

| Layer | Modules |
|---|---|
| Probability | `Prob/*` — sub-distributions, couplings, support, birthday bound, Schwartz–Zippel |
| Core | `Core/*` — typed heap, `SPComp` stateful-probabilistic monad, `SPTree` syntactic trees |
| Relational | `Relational/*` — pRHL judgment, sync/frame/reorder rules |
| Package | `Package/*` — interface-based package algebra |
| Category | `Category/*` — Kleisli of SPComp, family bicategory, cocartesian / affine structure |
| Deep embedding | `Deep/*` — syntactic package calculus with semantic evaluation |
| Bridge | `Bridge/*` — deep-to-shallow semantic bridge |
| Tactics | `Tactics/*` — pRHL automation (sync, invariant, WP/SP, ProofFrog, lazy sampling, …) |
| Crypto foundation | `Crypto/{Game,Advantage,SDist,SecurityDefs,Encryption,HybridArgument,NomAdvantage}.lean` |
| Forking | `Crypto/ForkingLemma.lean`, `Crypto/GeneralForkingLemma.lean` — Pointcheval–Stern and Bellare–Neven, axiom-free |
| Assumptions | `Crypto/Assumptions/*` — DDH, CDH, GapDH, DL, t-SDH, q-SDH, CoCDH, ODH, CR, OWF, PRP, RSA, AEAD, MAC |
| VCVio bridge | `Crypto/Bridges/VCVioBridge/{Monad,State,Linking,Relational}.lean` + examples |
| Arklib interface | `Crypto/Bridges/ArkLibTypes.lean` — `ArgumentSoundness`, `KnowledgeSoundness` + reduction composition |
| Curve math | `Crypto/KeyAgreement/{MontgomeryLadder,MontgomeryAsWeierstrass,MontgomeryXOnly,Curve25519}.lean` |
| Rust → Jasmin | `Crypto/Jasmin/{RustCmd,RustCmdBorrowCheck,RustCmdToJasmin,JasminAST,…,ISA}.lean` + `Passes/{ConstantFold,NopElim,DeadCode}.lean`, demoed on `ChaCha20QR.lean` |

## Build

Requires [elan](https://github.com/leanprover/elan). The pinned toolchain is
`leanprover/lean4:v4.28.0` (see `lean-toolchain`).

```
lake exe cache get    # optional: pull mathlib cache
lake build
```

A full cold build compiles Mathlib + VCVio + CatCrypt-core in roughly an hour;
with a warm cache, CatCrypt-core itself builds in under a minute.

## Dependencies

Pinned in `lakefile.lean` and `lake-manifest.json`:

- [Mathlib](https://github.com/leanprover-community/mathlib4) `v4.28.0`
- [VCVio](https://github.com/Verified-zkEVM/VCV-io) `master` (used by `Bridges/VCVioBridge/*`)
- [Duper](https://github.com/leanprover-community/duper) `v4.28.0`, [lean-auto](https://github.com/leanprover-community/lean-auto) `v4.28.0-hammer`, [lean-smt](https://github.com/dhsorens/lean-smt) `dhsorens/4_28_0-update` — hammer tools used by some proofs

## Trust edges

The minimal basis is `sorry`-free. Documented axioms:

- `Curve25519.curve25519Prime_prime` — primality of `2²⁵⁵ − 19`. Standard trust
  edge (fiat-crypto, AUCurves).
- `MontgomeryXOnly.MontyCurveGroup` — the Montgomery group law is taken as a
  hypothesis; the Weierstrass transport in `MontgomeryAsWeierstrass.lean` is
  the intended discharge.
- `JasminISA.compilerCorrect` (per-ISA) — the Jasmin backend (linearize →
  register alloc → assembly) is axiomatized per ISA. Intended to be
  instantiated against external semantics (LNSym for AArch64, Sail-Lean for
  RISC-V; x86 remains trusted).

## License

MIT. See `LICENSE`.
