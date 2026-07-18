#!/bin/bash
# Build blueprint web version using the leanblueprint venv's plastex
# This ensures the blueprint and depgraph plugins are found correctly.
set -e

SCRIPT_DIR="$(cd "$(dirname "$0")" && pwd)"
VENV_DIR="$(dirname "$(dirname "$(readlink -f "$(which leanblueprint)")")")"

cd "$SCRIPT_DIR/src"

# leanblueprint's plastex Packages ship in the `plastex` pipx venv. Resolve the
# path from $HOME (portable) and materialize a local config from the committed
# template, so no absolute personal path is checked in (plastex .cfg has no env
# expansion). The generated config is git-ignored / regenerated each build.
PLASTEX_SITE="$HOME/.local/share/pipx/venvs/plastex/lib/python3.12/site-packages"
LEANBLUEPRINT_PACKAGES="$PLASTEX_SITE/leanblueprint/Packages"
sed "s|@LEANBLUEPRINT_PACKAGES@|$LEANBLUEPRINT_PACKAGES|" \
  "$SCRIPT_DIR/plastex.cfg" > "$SCRIPT_DIR/plastex.local.cfg"

# Use the plastex from the leanblueprint venv to ensure plugin compatibility.
# Add the plastex venv to PYTHONPATH so leanblueprint's Packages are found.
PYTHONPATH="$PLASTEX_SITE:${PYTHONPATH:-}" \
  "$VENV_DIR/bin/plastex" -c ../plastex.local.cfg web.tex

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

# Mount the doc-gen4 API under web/api/ so the two-column Lean links resolve
# locally (the GitHub repo is private / on a non-main branch, so blob URLs 404).
DOCGEN="$SCRIPT_DIR/../docbuild/.lake/build/doc"
if [ -d "$DOCGEN" ]; then
  ln -sfn "$DOCGEN" "$SCRIPT_DIR/web/api"
  echo "Mounted doc-gen4 at web/api/"
fi

echo "Blueprint web built successfully in $SCRIPT_DIR/web/"
