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

-- Pinned to the module-system port on spitters/nominal-lean. A path-require of
-- the sibling builds locally but breaks CI, which has no sibling checkout.
require nominalLean from git
  "https://github.com/spitters/nominal-lean" @ "lean-upgrade-4.35"

-- hax-lean: the runtime and typed AST of haxpipeT extractions (`HaxLean.Runtime`), which the
-- extraction bridges and the fold lemmas of `CatCryptCore.Hax.FoldRange` read.
require «hax-lean» from git
  "https://github.com/spitters/hax-lean.git" @ "lean-upgrade-4.35"

-- QuantumFoundations: the quantum-information library shared with VCVio; `CPComp` is its
-- `SubInstrument` on `Fin d`. Pinned to a commit of `main`.
require QuantumFoundations from git
  "https://github.com/lean-crypto-foundations/QuantumFoundations" @
    "901aaab7967ceecd2240d0b38bbde7cf3e2c14ac"

-- PolyFun: polynomial functors, the free monad `PFunctor.FreeM` (from cslib), roll bounds
-- and the charge fold; `SPTree` and `OracleAdv` are related to `FreeM` by equivalences.
-- Pinned to the revision VCVio uses.
require PolyFun from git
  "https://github.com/Verified-zkEVM/PolyFun" @ "ef4c157b3c6775fb55864303d96f9b400428d5f0"

-- mathlib LAST so its proofwidgets/aesop versions win on conflicts;
-- this is required for `lake exe cache get` to find oleans.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.35.0"
