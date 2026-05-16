import Lake
open Lake DSL

package catcryptCore where
  leanOptions := #[
    ⟨`pp.unicode.fun, true⟩,
    ⟨`autoImplicit, false⟩
  ]

@[default_target]
lean_lib CatCrypt where
  globs := #[.submodules `CatCrypt]

-- lean-smt: dhsorens fork has no 4.29 branch yet (2026-05-16). Drop if lake
-- update fails — no code in CatCrypt-core imports Smt.
require smt from git
  "https://github.com/dhsorens/lean-smt.git" @ "dhsorens/4_28_0-update"

require auto from git
  "https://github.com/leanprover-community/lean-auto.git" @ "v4.29.0-hammer"

require Duper from git
  "https://github.com/leanprover-community/duper.git" @ "v4.29.0"

require VCVio from git
  "https://github.com/Verified-zkEVM/VCV-io" @ "v4.29.0"

-- mathlib LAST so its proofwidgets/aesop versions win on conflicts;
-- this is required for `lake exe cache get` to find oleans.
require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.29.1"
