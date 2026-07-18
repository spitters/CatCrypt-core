# Building

## The library

Requires [elan](https://github.com/leanprover/elan). The pinned toolchain is
`leanprover/lean4:v4.30.0` (see `lean-toolchain`).

```
lake exe cache get    # optional: pull the Mathlib olean cache
lake build
```

A full cold build compiles Mathlib + CatCrypt-core in roughly an hour; with a
warm cache, CatCrypt-core itself builds in a few minutes.

## The documentation

Both documentation builds live in their own packages, so neither the verso nor the
doc-gen4 toolchain becomes a dependency of code that `require`s the library.

**Manual** (`docs/`, verso) — a narrative guide to the layers and a worked reading
of the key declarations:

```
cd docs && lake update && lake build && lake exe core-manual --output _out
```

Open `docs/_out/html-single/index.html` (a single self-contained page).

**API reference** (`docbuild/`, doc-gen4) — per-declaration HTML for every module
of the library:

```
cd docbuild && lake update && lake exe cache get && lake build CatCryptCore:docs
```

Output in `docbuild/.lake/build/doc/` (open `index.html`). The library's
`.andSubmodules` glob makes the `CatCryptCore` umbrella module the doc root, so the
facet documents the umbrella and, transitively, every module in its import tree.
The hosted copy at <https://spitters.github.io/CatCrypt-core/> is this build,
published by `.github/workflows/docs.yml`.
