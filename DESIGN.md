# Design and influences

> **Note.** This document was machine-generated (from a survey of the
> library's module docstrings and their references) and lightly curated.
> It may contain errors or omissions; the module docstrings and the cited
> works are authoritative.

CatCrypt Core is a Lean 4 library for game-based cryptographic security
proofs in the state-separating style. This note records where its design
comes from, and what it adds over those sources.

## Main influences

### SSProve — the architectural backbone

The package algebra (`Package/`), the pRHL judgment and rule set
(`Relational/`), the heap/location discipline (`Core/`), and the
`ssprove_*` tactic family port the design of
[SSProve](https://github.com/SSProve/ssprove) (Haselwarter, Rivas,
Van Muylder, Winterhalter, Abate, Sidorenco, Hriţcu, Maillard, Spitters,
*SSProve: A Foundational Framework for Modular Cryptographic Proofs in
Coq*, TOPLAS 45(3), 2023, [doi:10.1145/3594735](https://doi.org/10.1145/3594735)).
Many module docstrings cite the specific Rocq source file they port
(`theories/Crypt/package/pkg_rhl.v`, …).

The nominal-package layer (`Nominal/`, parts of `Deep/`) follows
*Nominal SSProve* (Benton et al.,
[ePrint 2025/598](https://eprint.iacr.org/2025/598)), with Pitts'
*Nominal Sets* as the underlying mathematics (atoms, finite
permutations, name abstraction).

Behind both stands the state-separating-proofs paradigm itself:
Brzuska, Delignat-Lavaud, Fournet, Kohbrok, Kohlweiss, *State Separation
for Code-Based Game-Playing Proofs*, ASIACRYPT 2018
([ePrint 2018/306](https://eprint.iacr.org/2018/306)).

### EasyCrypt — the proof-mode discipline and the unary layer

The EasyCrypt-style proof verbs are deliberately mirrored:
`ssprove_proc`, `ssprove_wp`, `ssprove_sp`, `ssprove_sim`,
`ssprove_auto_ec`, `ssprove_rnd_{lhs,rhs}`. The unary logic in `Unary/`
(probabilistic Hoare logic, lossless reasoning, the failure-event lemma,
query bounds) follows EasyCrypt's, and the assumption files in
`Crypto/Assumptions/` carry cross-validation tables against named
EasyCrypt theories (`DDH.ec`, `PRP.eca`, …). Behind EasyCrypt, several
docstrings cite CertiCrypt (Barthe, Grégoire, Zanella Béguelin) for the
origins of pRHL, coupling/support reasoning, and the failure-event lemma.

### ProofFrog — game-simplification automation

The mechanical game-simplification passes —
`ssprove_dead_code`, `ssprove_copy_propagate`, `ssprove_contract_all`,
`ssprove_canonicalize` — port the rewrite passes of the ProofFrog tool
into verified tactics.

### Further influences

- **Cho–Jacobs effectus theory** — `Category/Effectus.lean`; the
  categorical-probability reading of the package algebra.
- **VCVio** ([Verified-zkEVM/VCV-io](https://github.com/Verified-zkEVM/VCV-io)) —
  interop target of `Crypto/Bridges/VCVioBridge/`; the `ssprove_crypto`
  driver in `Tactics/CryptoAuto.lean` borrows its `qvcgen` ergonomics.
- **ArkLib** — `Crypto/Bridges/ArkLibTypes.lean` mirrors its
  argument/knowledge-soundness vocabulary for interoperability.
- **Pointcheval–Stern** and **Bellare–Neven** — the two forking lemmas
  (`Crypto/ForkingLemma.lean`, `Crypto/GeneralForkingLemma.lean`).
- **Boneh–Shoup** and **Katz–Lindell** — the textbook game definitions
  the assumption files are checked against.
- **Mathlib** — the mathematical substrate: `PMF`, `ENNReal`, and the
  Weierstrass-curve machinery targeted by the Montgomery transport.

## What is new here

1. **Foundational re-basing on Mathlib probability.** `SPComp α` is
   `Heap → SDistr (α × Heap)` with `SDistr α = PMF (Option α)`: every
   game, advantage, and bound grounds in Mathlib's measure-theoretic
   `PMF`. (SSProve carries its own probability development in Rocq;
   EasyCrypt's ambient logic is trusted rather than foundational.)

2. **A dual shallow/deep architecture with a proven bridge.** SSProve is
   free-monad (deep) throughout. CatCrypt Core provides both a shallow
   monad — where Mathlib automation applies directly — and a deep
   `RawCode`/`DeepPackage` calculus — where induction over syntax works —
   connected by a verified semantic bridge (`Bridge/`, `Deep/Bridge.lean`)
   and an elaboration-time reflector (`rawCode%`, `Deep/Reflect.lean`).

3. **A categorical package layer.** Kleisli categories of `PMF` and
   `SPComp`, the `Fam`/`PkgFam` bicategory of packages, and
   cocartesian/affine/effectus structure (`Category/`) — treating the
   package algebra as a structured category, and connecting it to
   categorical probability, has no counterpart in SSProve, EasyCrypt, or
   ProofFrog.

4. **EasyCrypt's proof-mode UX on SSProve's foundations.** Each source
   has half: EasyCrypt the tactic ergonomics without foundational
   semantics, SSProve the semantics without the tactic breadth. The
   tactic suite here implements the EasyCrypt verbs, lazy/eager
   sampling, remember/forget, and advantage triangle-chaining on top of
   the foundational pRHL.

5. **ProofFrog passes as verified tactics.** ProofFrog itself is an
   unverified pre-processor; here each simplification is a theorem-backed
   tactic over `SPComp`.

6. **Cross-framework interop as a first-class artifact.** The VCVio
   bridge (distribution, state, linking, and relational-advantage
   layers) and the ArkLib-compatible soundness interface make
   independent Lean cryptography stacks mutually usable.

7. **Forking lemmas over this substrate.** Pointcheval–Stern and
   Bellare–Neven general forking proved directly over the
   `SPComp`/`PMF` stack.

8. **The Montgomery-to-Weierstrass transport.** X-only ladder
   correctness stated against an abstract `MontyCurveGroup` and intended
   to be discharged via Mathlib's Weierstrass group law
   (`Crypto/KeyAgreement/MontgomeryAsWeierstrass.lean`) — a different
   artifact from field-arithmetic correctness à la fiat-crypto.
