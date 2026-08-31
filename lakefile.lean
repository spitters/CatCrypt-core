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
  -- only its submodules). The umbrella is the lib's root module, so doc-gen4's
  -- `CatCryptCore:docs` library facet documents it and, transitively, the
  -- whole library; with a strict-`submodules` glob the root is filtered out
  -- and the facet sees 0 root modules.
  globs := #[.andSubmodules `CatCryptCore]

-- 4.32 upgrade, temporary: path-require the sibling until its bump commit is
-- pushed to spitters/nominal-lean; then repin the git SHA here.
require nominalLean from "../nominal-lean"

-- mathlib LAST so its proofwidgets/aesop versions win on conflicts;
-- this is required for `lake exe cache get` to find oleans.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.32.0"
