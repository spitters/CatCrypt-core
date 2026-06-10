# Changelog

## v0.2.0 — 2026-06-10

- Toolchain: Lean 4.29.1, Mathlib `v4.29.1`, VCVio `v4.29.0`, Duper `v4.29.0`,
  lean-auto `v4.29.0-hammer` (was Lean 4.28.0 across the board).
- The Rust → Jasmin compiler pipeline (`Crypto/Jasmin/`,
  `Crypto/SecureCompilation/`) moved out of the minimal basis into a separate
  project. With it go the per-ISA compiler-correctness axioms and all
  `native_decide` uses.
- Removed the unused `PRP_PRF_Switching` axiom: its statement did not express
  the switching lemma. The birthday-term bound definition remains.
- Fixed the `Crypto.NomAdvantage` build failure on Lean 4.29 (explicit
  universe annotations on the universe-monomorphic `NomPackage`).
- New modules: `Tactics/{SumCases, SPNormalize, Remember, Triangle,
  CryptoAuto}` and `Deep/Reflect` (an `SPComp` → `RawCode` reifier).
- Added `CITATION.cff`, `CHANGELOG.md`, `CONTRIBUTING.md`, and a CI workflow
  with sorry/axiom guards.

## v0.1.0 — 2026-04-23

- Initial minimal-basis release (Lean 4.28.0).
