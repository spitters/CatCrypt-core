#!/usr/bin/env python3
"""Two-column blueprint nodes: informal LaTeX (left) | formal Lean (right).

leanblueprint hides the Lean declarations in a click-to-open modal linked to a
`find/#doc/...` search anchor that never shows the definition. This post-build
pass instead wraps each node's informal statement and its Lean signature(s) into
two real columns (a flex row), and links each declaration to the co-served
doc-gen4 page (`api/<module>.html#<decl>`) — the GitHub source cannot be linked
(the repo is private and on a non-`main` branch). Signatures and module paths
come from `web/find/decl_index.json` (produced by gen_decl_index.py).
"""
import html
import json
import os
import re

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
WEB = os.path.join(ROOT, "blueprint", "web")
INDEX = os.path.join(WEB, "find", "decl_index.json")

idx = json.load(open(INDEX, encoding="utf-8"))

CONTENT_OPEN = re.compile(
    r'(<div class="(?:definition|theorem|lemma|proposition|corollary)_thmcontent">)'
)
NAME_IN = re.compile(r'class="lean_decl"[^>]*>([^<]+)</a>')
LEANLINK = re.compile(r'<a\s+href="[^"]*"\s+class="lean_decl"[^>]*>([^<]+)</a>')


def docgen_url(info):
    # CatCryptCore/Prob/SDistr.lean -> api/CatCryptCore/Prob/SDistr.html
    return "api/" + info["file"][:-5] + ".html"


def prettify(sig):
    """Mathlib-style layout for a long signature: each top-level binder on its own
    line, and the conclusion (the depth-0 `:`) on its own indented line, mimicking
    display math. Short signatures are left on one line."""
    if len(sig) <= 72:
        return sig
    out = []
    depth = 0
    for ch in sig:
        if depth == 0 and ch in "({[":
            if out and not out[-1].endswith("\n    "):
                out.append("\n    ")
            out.append(ch)
            depth += 1
        elif depth == 0 and ch == ":":
            out.append("\n    :")
        elif ch in "([{⟨":
            out.append(ch)
            depth += 1
        elif ch in ")]}⟩":
            out.append(ch)
            depth -= 1
        else:
            out.append(ch)
    return "".join(out)


def relink(m):
    name = m.group(1).strip()
    info = idx.get(name)
    if not info:
        return m.group(0)
    tip = html.escape(info.get("sig", ""), quote=True)
    return (f'<a href="{docgen_url(info)}#{name}" class="lean_decl" '
            f'title="{tip}" target="_blank">{name}</a>')


def lean_col(names):
    rows = []
    for name in names:
        name = name.strip()
        info = idx.get(name)
        if not info or not info.get("sig"):
            continue
        sig = info["sig"]
        code = prettify(sig)
        # For a definition the type is a locator; its body is the content. Show
        # the body when it is short enough to preview (the linked API page has
        # the full definition for anything longer).
        body = info.get("body", "")
        if info.get("kind") in ("def", "abbrev", "instance") and body \
                and len(sig) + len(body) <= 240:
            code = code + "\n    := " + body
        rows.append(
            f'<div class="lean-sig">'
            f'<a class="lean-sig-name" href="{docgen_url(info)}#{name}" target="_blank">{name}</a>'
            f'<code>{html.escape(code)}</code></div>'
        )
    if not rows:
        return ""
    return ('<div class="lean-col"><div class="lean-col-head">Lean</div>'
            + "".join(rows) + "</div>")


def find_close(body):
    """Index range of the </div> that closes this thmcontent (balanced)."""
    depth = 1
    for m in re.finditer(r"<div\b|</div>", body):
        if m.group(0).startswith("<div"):
            depth += 1
        else:
            depth -= 1
            if depth == 0:
                return m.start(), m.end()
    return None


count = 0
for dp, _, fns in os.walk(WEB):
    for fn in fns:
        if not fn.endswith(".html"):
            continue
        p = os.path.join(dp, fn)
        s = open(p, encoding="utf-8").read()
        s = LEANLINK.sub(relink, s)  # links -> doc-gen4 source pages

        parts = CONTENT_OPEN.split(s)
        out = [parts[0]]
        touched = 0
        for i in range(1, len(parts), 2):
            open_tag = parts[i]
            body = parts[i + 1] if i + 1 < len(parts) else ""
            names = NAME_IN.findall(parts[i - 1])  # this node's modal precedes its content
            col = lean_col(names)
            close = find_close(body)
            if col and close:
                cs, _ = close
                out.append(open_tag + '<div class="latex-col">' + body[:cs]
                           + "</div>" + col + body[cs:])
                touched += 1
            else:
                out.append(open_tag + body)
        if touched:
            open(p, "w", encoding="utf-8").write("".join(out))
            count += touched
print(f"inject_lean_sigs: two-column layout added to {count} nodes")
