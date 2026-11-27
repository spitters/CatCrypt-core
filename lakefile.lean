import Lake
open Lake DSL

package catcryptCore where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]
  -- `-E <kind>` reports Lean messages of that kind as errors. `hasSorry` is the
  -- kind Lean attaches to a declaration whose proof term reaches `sorryAx`, so
  -- building this package refuses such a declaration and no separate step has to
  -- read the build's output. The word in a comment, a docstring or a string
  -- literal carries no such message; a declaration reaching `sorryAx` through a
  -- tactic carries one even though the word appears nowhere in its source.
  moreLeanArgs := #["-E", "hasSorry"]

@[default_target]
lean_lib CatCryptCore where
  -- Module root `CatCryptCore.*` (a distinct root from the CatCrypt dev
  -- monorepo, so downstream packages can require this library without a
  -- module-name collision). Declared namespaces remain `CatCrypt.*`.
  -- `.andSubmodules` includes the umbrella module `CatCryptCore` itself (not
  -- only its submodules). The umbrella and the example aggregator
  -- `CatCryptCore.Examples` are the lib's root modules, so doc-gen4's
  -- `CatCryptCore:docs` library facet documents them and, transitively, the
  -- library and its examples; `import CatCryptCore` does not load the examples.
  roots := #[`CatCryptCore, `CatCryptCore.Examples]
  globs := #[.andSubmodules `CatCryptCore]

-- Test modules of the tactics and of the complexity layer. No module of
-- `CatCryptCore` imports them; `lake build CatCryptCoreTest` builds them.
lean_lib CatCryptCoreTest where
  globs := #[.submodules `CatCryptCoreTest]

-- Pinned to a revision of nominal-lean's master. A path-require of
-- the sibling builds locally but breaks CI, which has no sibling checkout.
require nominalLean from git
  "https://github.com/spitters/nominal-lean" @ "53116542dd6806bd9f9c0d36cf69ed275ce0d765"

-- hax-lean: the runtime and typed AST of haxpipeT extractions (`HaxLean.Runtime`) and the
-- fold lemmas (`HaxLean.FoldRange`), which the extraction bridges read.
require «hax-lean» from git
  "https://github.com/spitters/hax-lean.git" @ "master"

-- QuantumFoundations: the quantum-information library shared with VCVio; `CPComp` is its
-- `SubInstrument` on `Fin d`. Pinned to a commit of `main`.
require QuantumFoundations from git
  "https://github.com/lean-crypto-foundations/QuantumFoundations" @
    "5ecbeec205ce3e9e4a5b7cb900c181884856ba19"

-- PolyFun: polynomial functors, the free monad `PFunctor.FreeM` (from cslib), roll bounds
-- and the charge fold; `SPTree` and `OracleAdv` are related to `FreeM` by equivalences.
-- Pinned to the revision VCVio uses.
require PolyFun from git
  "https://github.com/Verified-zkEVM/PolyFun" @ "528b3b1fda285487e55704409bd1b058dc18fcad"

-- iris-lean, required by the IrisBridge modules; the same tag as nominal-lean requires.
require iris from git
  "https://github.com/spitters/iris-catcrypt" @ "v4.36.0-catcrypt.1" / "Iris"

-- refinement-wp: the refinement weakest precondition `wrp` over `Std.WP`, which
-- `Refinement/RRelWRP.lean` relates to `RRelPT`.
require «refinement-wp» from git
  "https://github.com/spitters/refinement-wp" @ "7f631d54c0adfef89cb0cf9cea92a199c7343e14"

-- mathlib LAST so its proofwidgets/aesop versions win on conflicts;
-- this is required for `lake exe cache get` to find oleans.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.36.0"