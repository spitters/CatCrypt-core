#!/bin/bash
# Build the web version of the blueprint with plastex and the leanblueprint
# plugins. Output: blueprint/web/ (index.html, dep_graph_document.html).
set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"

# Locate plastex and the leanblueprint plastex Packages. Both come from
# `pip install leanblueprint` (or a pipx venv with leanblueprint injected); the
# Packages directory is resolved through the interpreter that runs plastex, so
# no absolute path is checked in. `PLASTEX` and `LEANBLUEPRINT_PACKAGES` override
# the discovery.
PLASTEX="${PLASTEX:-$(command -v plastex)}"
PLASTEX_PY="$(head -1 "$(readlink -f "$PLASTEX")" | sed 's/^#!//')"
if [ -z "${LEANBLUEPRINT_PACKAGES:-}" ]; then
  # Unquoted: the shebang may be `/usr/bin/env python3`.
  LEANBLUEPRINT_PACKAGES="$($PLASTEX_PY -c \
    'import os, leanblueprint; print(os.path.join(os.path.dirname(leanblueprint.__file__), "Packages"))')"
fi

cd "$SCRIPT_DIR/src"

# plastex .cfg has no environment expansion: materialize a local config from the
# committed template (the generated file is git-ignored).
sed "s|@LEANBLUEPRINT_PACKAGES@|$LEANBLUEPRINT_PACKAGES|" \
  "$SCRIPT_DIR/plastex.cfg" > "$SCRIPT_DIR/plastex.local.cfg"

"$PLASTEX" -c ../plastex.local.cfg web.tex

# Move output to blueprint/web/
rm -rf "$SCRIPT_DIR/web"
mv "$SCRIPT_DIR/src/web" "$SCRIPT_DIR/web"

# Inject extra CSS into all HTML files
if [ -f "$SCRIPT_DIR/extra_styles.css" ]; then
  cp "$SCRIPT_DIR/extra_styles.css" "$SCRIPT_DIR/web/styles/extra_styles.css"
  # Add stylesheet link after blueprint.css in every HTML file
  find "$SCRIPT_DIR/web" -name '*.html' -exec sed -i \
    's|styles/blueprint.css" />|styles/blueprint.css" />\n<link rel="stylesheet" href="styles/extra_styles.css" />|' {} +
  echo "Injected extra_styles.css into HTML files"
fi

# Generate declaration index and search page
if [ -x "$(command -v python3)" ]; then
  python3 "$SCRIPT_DIR/../scripts/gen_decl_index.py"
  # Inject each declaration's Lean signature into the node HTML (hover tooltip +
  # inline code block), so the formal statement is on the node, not 3 clicks away.
  python3 "$SCRIPT_DIR/../scripts/inject_lean_sigs.py"
  python3 "$SCRIPT_DIR/../scripts/blueprint_graphs.py" 2>/dev/null || true
  if [ -f "$SCRIPT_DIR/find_template/index.html" ]; then
    cp "$SCRIPT_DIR/find_template/index.html" "$SCRIPT_DIR/web/find/index.html"
    echo "Copied find/index.html"
  fi
fi

# Declaration links point at `api/` (see `\dochome` in src/web.tex). Locally the
# doc-gen4 output is mounted there. When the blueprint is published beside the
# API reference, set BLUEPRINT_API_BASE to the reference's location relative to
# the blueprint (`..` when the blueprint is served from `<site>/blueprint/`).
if [ -n "${BLUEPRINT_API_BASE:-}" ]; then
  find "$SCRIPT_DIR/web" -name '*.html' -exec sed -i \
    "s|href=\"api/|href=\"$BLUEPRINT_API_BASE/|g" {} +
  echo "Declaration links rewritten to $BLUEPRINT_API_BASE/"
else
  DOCGEN="$SCRIPT_DIR/../docbuild/.lake/build/doc"
  if [ -d "$DOCGEN" ]; then
    ln -sfn "$DOCGEN" "$SCRIPT_DIR/web/api"
    echo "Mounted doc-gen4 at web/api/"
  fi
fi

echo "Blueprint web built successfully in $SCRIPT_DIR/web/"
