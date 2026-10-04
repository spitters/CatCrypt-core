# Building

## The library

Requires [elan](https://github.com/leanprover/elan), which installs the toolchain
named in `lean-toolchain`.

```
lake exe cache get    # optional: pull the Mathlib olean cache
lake build
```

A full cold build compiles Mathlib + CatCrypt-core in roughly an hour; with a
warm cache, CatCrypt-core itself builds in a few minutes.

## The documentation

The manual and the API reference build in their own packages, so neither the verso
nor the doc-gen4 toolchain becomes a dependency of code that `require`s the library.
The blueprint needs no Lean build.

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

**Blueprint** (`blueprint/`, [leanblueprint](https://github.com/PatrickMassot/leanblueprint))
— the informal statements of the foundation layers and of every worked scheme in
`CatCryptCore/Examples/`, each linked to its Lean declaration, with a dependency graph.
It requires Python, Graphviz (with its development headers, for `pygraphviz`) and
leanblueprint, which brings plastex:

```
pip install leanblueprint          # or: pipx install leanblueprint
bash blueprint/build_web.sh
```

Output in `blueprint/web/` (open `index.html`; the graph is
`dep_graph_document.html`). The script also writes `blueprint/lean_decls`, the list of
declarations in the sources, against which every `\lean{...}` reference in
`blueprint/src/chapters/` can be checked. When the API reference has been built in
`docbuild/`, it is linked at `blueprint/web/api/` so that declaration links resolve
locally.

## The hosted site

`.github/workflows/docs.yml` runs on a published release or on demand. It builds the
API reference and the blueprint and publishes them as one GitHub Pages site:

- API reference: <https://spitters.github.io/CatCrypt-core/>
- Blueprint: <https://spitters.github.io/CatCrypt-core/blueprint/>
- Dependency graph: <https://spitters.github.io/CatCrypt-core/blueprint/dep_graph_document.html>

The blueprint job sets `BLUEPRINT_API_BASE=..`, so its declaration links point at the
API reference one level up, and fails if a `\lean{...}` reference names no
declaration.
