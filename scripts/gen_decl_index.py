#!/usr/bin/env python3
"""Generate lean_decls and a declaration→file:line index for the blueprint.

Scans CatCrypt/**/*.lean for public theorem/def/lemma/class/structure/instance
declarations and outputs:
  1. blueprint/lean_decls — one declaration per line
  2. blueprint/web/find/decl_index.json — {decl_name: {file, line, kind, url, doc}}

The `doc` field carries the declaration's immediately-preceding `/-- … -/`
docstring (flattened, truncated). This makes the static index **concept
grep-able without a Lean build**: e.g. `grep -i pippenger decl_index.json`
surfaces `bucketMsm_eq_msm` even though its name never says "Pippenger". It is
the no-build complement to `CatCrypt.Tactic.EnvSearch.#docFind` (which searches
the same docstrings over the live elaborated environment). Capability
descriptions in this project live in docstrings, so name/type search alone
keeps causing rediscovery of work that already exists.
"""

import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SCAN_DIRS = ["CatCryptCore"]
GITHUB_BASE = "https://github.com/spitters/CatCrypt-core/blob/main"

# Match public declarations (not indented = top-level, not private)
DECL_RE = re.compile(
    r'^(?:noncomputable\s+)?(?:protected\s+)?'
    r'(theorem|def|lemma|class|structure|abbrev|instance|axiom|opaque)\s+'
    r'([A-Za-z_][\w.\']*)',
    re.MULTILINE
)

# Detect namespace blocks
NS_OPEN_RE = re.compile(r'^namespace\s+([\w.]+)', re.MULTILINE)
NS_CLOSE_RE = re.compile(r'^end\s+([\w.]+)', re.MULTILINE)
SECTION_RE = re.compile(r'^section\s+(\w+)', re.MULTILINE)
SECTION_END_RE = re.compile(r'^end\s+(\w+)', re.MULTILINE)

# A `/-- … -/` docstring block (non-greedy, spans lines).
DOCSTRING_BLOCK_RE = re.compile(r'/--(.*?)-/', re.DOTALL)
# Lines allowed to sit between a docstring and the declaration it documents.
_INTERVENING = ('@[', 'set_option', 'private', 'protected', 'noncomputable',
                'scoped', 'local', 'unsafe', 'partial')


def preceding_docstring(content, decl_start, maxlen=240):
    """Return the flattened `/-- … -/` docstring immediately preceding the
    declaration whose keyword starts at `decl_start`, or '' if there is none.
    Skips intervening blank / attribute / modifier / `set_option … in` lines."""
    lines = content[:decl_start].split('\n')
    # Walk back over the decl-line prefix + any attribute/modifier/blank lines.
    j = len(lines) - 2
    while j >= 0:
        s = lines[j].strip()
        if s == '' or any(s.startswith(p) for p in _INTERVENING) or s.endswith(' in'):
            j -= 1
            continue
        break
    if j < 0 or not lines[j].rstrip().endswith('-/'):
        return ''
    # Find the line that opens this docstring block.
    start = j
    while start >= 0 and '/--' not in lines[start]:
        start -= 1
    if start < 0:
        return ''
    m = DOCSTRING_BLOCK_RE.search('\n'.join(lines[start:j + 1]))
    if not m:
        return ''
    doc = ' '.join(m.group(1).split())
    return doc[:maxlen]

def extract_declarations(filepath, relpath):
    """Extract all public declarations from a Lean file."""
    with open(filepath, 'r') as f:
        content = f.read()
        lines = content.split('\n')

    decls = []
    # Track namespace stack by line
    ns_stack = []

    # Build a line→namespace mapping
    line_ns = {}
    for i, line in enumerate(lines):
        # Check namespace open
        m = re.match(r'^namespace\s+([\w.]+)', line)
        if m:
            ns_stack.append(m.group(1))
        # Check namespace close
        m = re.match(r'^end\s+([\w.]+)', line)
        if m and ns_stack and ns_stack[-1] == m.group(1):
            ns_stack.pop()
        line_ns[i] = '.'.join(ns_stack) if ns_stack else ''

    # Skip private declarations
    for m in DECL_RE.finditer(content):
        # Check if preceded by 'private' on same line
        line_start = content.rfind('\n', 0, m.start()) + 1
        prefix = content[line_start:m.start()]
        if 'private' in prefix:
            continue

        kind = m.group(1)
        name = m.group(2)
        lineno = content[:m.start()].count('\n') + 1

        # Get namespace at this line
        ns = line_ns.get(lineno - 1, '')

        # Build fully qualified name
        if ns and not name.startswith(ns):
            fqn = f"{ns}.{name}"
        else:
            fqn = name

        decls.append({
            'name': fqn,
            'kind': kind,
            'file': relpath,
            'line': lineno,
            'doc': preceding_docstring(content, m.start()),
            'sig': signature_of(content, m.start()),
            'body': (body_of(content, m.start())
                     if kind in ('def', 'abbrev', 'instance') else ''),
        })

    return decls


def signature_of(content, decl_start, maxlen=400):
    """Extract the declaration's Lean signature: from the keyword through the
    type, stopping at the top-level `:=` body, a `where`, or a blank line."""
    window = content[decl_start:decl_start + 1600]
    depth = 0
    end = len(window)
    i = 0
    while i < len(window) - 1:
        c = window[i]
        if c in '([{⟨':
            depth += 1
        elif c in ')]}⟩':
            depth -= 1
        elif depth == 0 and window[i:i + 2] == ':=':
            end = i
            break
        i += 1
    sig = window[:end]
    for cut in ('\n\n', ' where', '\nwhere'):
        j = sig.find(cut)
        if j != -1:
            sig = sig[:j]
    sig = re.sub(r'\s+', ' ', sig).strip()
    if len(sig) > maxlen:
        sig = sig[:maxlen] + ' …'
    return sig


# Line that starts a new top-level construct (ends a definition body): a
# top-level declaration keyword, or a `/- … -/` / `/-- … -/` / `/-! … -/` block.
_BODY_END_RE = re.compile(
    r'^\s*(?:@\[[^\]]*\]\s*|noncomputable |protected |private |scoped |local |'
    r'unsafe |partial |set_option |attribute )*'
    r'(?:theorem|def|lemma|class|structure|abbrev|instance|axiom|opaque|'
    r'end|namespace|section|open|variable)\b'
    r'|^\s*/-'
)
# A top-level `where` keyword (structure-instance syntax has no `:=` body).
_WHERE_RE = re.compile(r'(?<![\w\'])where(?![\w\'])')
_FIELD_RE = re.compile(r'([A-Za-z_]\w*)\s*:=\s*(.*)')


def _is_boiler(v):
    """A field value that carries no information: a synthesized typeclass
    instance (`inferInstance`, `haveI …`, a short `⟨…⟩`) or a tactic block."""
    v = v.strip()
    return (not v or 'inferInstance' in v
            or v.startswith(('by ', 'haveI', 'letI'))
            or bool(re.fullmatch(r'⟨.{0,24}⟩', v)))


def _where_fields(text, maxlen):
    """Render the behavioral fields of a `where`-syntax structure instance,
    dropping typeclass boilerplate (`inferInstance`, `⟨…⟩`, `by …`). Turns
    `def BoolOTP : EncScheme where …` into `encrypt := k ⊕ m; decrypt := …`."""
    fields = []
    cur = None
    blank = 0
    for k, ln in enumerate(text.split('\n')):
        if k > 0 and ln[:1] not in (' ', '\t', '') and _BODY_END_RE.match(ln):
            break
        s = ln.strip()
        if s == '':
            blank += 1
            if blank >= 2:
                break
            continue
        blank = 0
        m = _FIELD_RE.match(s)
        if m:
            if cur:
                fields.append(cur)
            cur = [m.group(1), m.group(2)]
        elif cur:
            cur[1] = (cur[1] + ' ' + s).strip()
    if cur:
        fields.append(cur)
    kept = [f'{n} := {v.strip()}' for n, v in fields if not _is_boiler(v)]
    body = ' '.join('; '.join(kept).split())
    if len(body) > maxlen:
        body = body[:maxlen] + ' …'
    return body


def body_of(content, decl_start, maxlen=320):
    """For a `def`/`abbrev`/`instance`, extract the value, which is what carries
    meaning (`BoolOTP : EncScheme` is a locator; its content is `k ⊕ m`). For a
    `:=` body, that is the RHS; for a `where`-syntax structure instance, the
    behavioral fields (see `_where_fields`). Returns '' for a `by` tactic block
    (previews as noise) or a `structure`/`class`/`axiom` (no value)."""
    window = content[decl_start:decl_start + 2600]
    depth = 0
    i = 0
    asgn = -1
    while i < len(window) - 1:
        c = window[i]
        if c in '([{⟨':
            depth += 1
        elif c in ')]}⟩':
            depth -= 1
        elif depth == 0:
            if window[i:i + 2] == ':=':
                asgn = i
                break
            # A top-level `where` before any `:=` ⇒ structure-instance syntax.
            if window[i] == 'w' and _WHERE_RE.match(window, i):
                return _where_fields(window[i + 5:], maxlen)
        i += 1
    if asgn == -1:
        return ''
    rest_lines = window[asgn + 2:].split('\n')
    body_lines = []
    blank = 0
    for k, ln in enumerate(rest_lines):
        if k > 0 and ln[:1] not in (' ', '\t', '') and _BODY_END_RE.match(ln):
            break
        if ln.strip() == '':
            blank += 1
            if blank >= 2:
                break
        else:
            blank = 0
        body_lines.append(ln)
    body = ' '.join(' '.join(body_lines).split())
    if body.startswith('by ') or body == 'by':
        return ''
    if len(body) > maxlen:
        body = body[:maxlen] + ' …'
    return body


def main():
    all_decls = []

    for scan_dir in SCAN_DIRS:
        base = os.path.join(ROOT, scan_dir)
        for dirpath, _, filenames in os.walk(base):
            for fn in sorted(filenames):
                if not fn.endswith('.lean'):
                    continue
                filepath = os.path.join(dirpath, fn)
                relpath = os.path.relpath(filepath, ROOT)
                decls = extract_declarations(filepath, relpath)
                all_decls.extend(decls)

    # Sort by name
    all_decls.sort(key=lambda d: d['name'])

    # Remove duplicates (same name)
    seen = set()
    unique = []
    for d in all_decls:
        if d['name'] not in seen:
            seen.add(d['name'])
            unique.append(d)
    all_decls = unique

    # Write lean_decls
    decls_path = os.path.join(ROOT, 'blueprint', 'lean_decls')
    with open(decls_path, 'w') as f:
        for d in all_decls:
            f.write(d['name'] + '\n')

    # Write JSON index
    index_dir = os.path.join(ROOT, 'blueprint', 'web', 'find')
    os.makedirs(index_dir, exist_ok=True)
    index_path = os.path.join(index_dir, 'decl_index.json')
    index = {}
    for d in all_decls:
        entry = {
            'file': d['file'],
            'line': d['line'],
            'kind': d['kind'],
            'sig': d['sig'],
            'doc': d['doc'],
            'url': f"{GITHUB_BASE}/{d['file']}#L{d['line']}"
        }
        if d.get('body'):
            entry['body'] = d['body']
        index[d['name']] = entry
    with open(index_path, 'w') as f:
        json.dump(index, f, indent=1)

    print(f"Generated {len(all_decls)} declarations")
    print(f"  lean_decls: {decls_path}")
    print(f"  decl_index.json: {index_path}")

    # Stats by kind
    kinds = {}
    for d in all_decls:
        kinds[d['kind']] = kinds.get(d['kind'], 0) + 1
    for k, v in sorted(kinds.items(), key=lambda x: -x[1]):
        print(f"  {k}: {v}")


if __name__ == '__main__':
    main()
