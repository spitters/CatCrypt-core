#!/usr/bin/env bash
#
# Headline witness gate.
#
# A headline theorem can be true because its hypotheses cannot hold, or because
# its bound is at least 1. Its witness is a declaration that applies it at
# concrete parameters with every hypothesis discharged and, for a bound, proves
# the bound below 1; for a conclusion with an existential body, frame map or
# simulator, the witness is a function of the compiled bytes or a definition.
# A computational bound keeps the advantages of its reductions as terms: its
# witness proves the remainder, the sum of the terms that are not an adversary's
# advantage, below 1.
#
# scripts/headline-witness.tsv has one row per theorem that the public documents
# of the repository name, in the columns
#
#   declaration  role  kind  witness
#
#   declaration  the qualified name
#   role         headline, or cited: named as a lemma, corollary of a listed
#                property or explanation of a hypothesis, without witness
#   kind         bound (the witness also proves the bound below 1) or statement
#   witness      the qualified name of the witness, or -
#
# scripts/headline-witness-missing.txt records the headlines without a witness,
# most important first, under a line `count=N`. The list may shrink and never
# grow. A line `undeclared NAME` records a name that the documents present as
# a headline and that no declaration has.
#
# The documents:
#   catcrypt-compiler  HEADLINES.md. The names of the table and those that open
#                      a paragraph or a list item are headlines; every other
#                      theorem it names has a row of either role.
#   CatCrypt-core      the `Main results` columns of JoyOfCrypto.md and the
#                      table of CatCryptCore/Crypto/MLKEM/QROM.md section 1 are
#                      headlines; every theorem that README.md names has a row.
#
# The gate fails on
#   - a theorem of these documents without a row, or a headline among them
#     recorded as cited;
#   - a headline of the documents that no declaration of the tree has, unless
#     it is recorded as undeclared;
#   - a row whose declaration or witness does not exist;
#   - a witness that is the headline itself, whose text does not name the
#     headline, that contains `sorry` or, for a bound, states no `< 1`;
#   - a headline without witness outside the recorded list, a recorded one that
#     has a witness or no headline row, and a list longer than its count.
#
# It reads text and loads no Lean. It cannot see whether a witness elaborates
# (the build does), whether it discharges every hypothesis, whether its
# parameters are concrete, or whether the term below 1 is the bound.
#
# In the development repository it checks the sibling checkouts of the two
# repositories that have a registry.
#
# Usage:
#   scripts/headline-witness-gate.sh            # check
#   scripts/headline-witness-gate.sh --list     # every documented theorem and its row
#   scripts/headline-witness-gate.sh --root DIR # check the repository at DIR
# Test: scripts/test_headline_witness_gate.sh
set -uo pipefail

HERE="$(cd "$(dirname "$0")" && pwd)"
exec python3 - "$HERE" "$@" <<'PY'
import importlib.util
import os
import re
import subprocess
import sys

here, args = sys.argv[1], sys.argv[2:]
sys.dont_write_bytecode = True
spec = importlib.util.spec_from_file_location(
    'lean_text', os.path.join(here, 'unbounded-hardness-shapes.py'))
lean = importlib.util.module_from_spec(spec)
spec.loader.exec_module(lean)

NAME = re.compile(r"(?:[^\W\d][\w'!?]*\.)*[^\W\d][\w'!?]*")
THEOREM = ('theorem', 'lemma')
REGISTRY = 'scripts/headline-witness.tsv'
MISSING = 'scripts/headline-witness-missing.txt'


def flavour(root):
    if os.path.isdir(os.path.join(root, 'CatCryptCore')):
        return 'core'
    # The development repository has a HEADLINES.md of its own, and no HaxAscent.
    if os.path.isfile(os.path.join(root, 'HEADLINES.md')) and os.path.isdir(os.path.join(root, 'HaxAscent')):
        return 'compiler'
    return None


def lean_files(root, kind):
    tops = ('CatCryptCore',) if kind == 'core' else ('CatCrypt', 'HaxAscent')
    if os.path.exists(os.path.join(root, '.git')):
        out = subprocess.run(['git', '-C', root, 'ls-files', '--'] + [t + '/*.lean' for t in tops],
                             capture_output=True, text=True, check=True).stdout
        return out.splitlines()
    found = []
    for top in tops:
        for base, _, names in os.walk(os.path.join(root, top)):
            found += [os.path.relpath(os.path.join(base, n), root) for n in names if n.endswith('.lean')]
    return sorted(found)


DECLARED = re.compile(rb'(?:theorem|lemma|def|abbrev|structure|class|instance|inductive|axiom'
                      rb'|opaque)[ \t\n]+([^\s:({\[]+)')


class Index:
    """The declarations of a tree that have one of the wanted last components."""

    def __init__(self, root, kind, wanted):
        self.by_short = {}
        wanted = {w.encode() for w in wanted}
        for path in lean_files(root, kind):
            raw = lean.read(os.path.join(root, path))
            # Only a file that declares a wanted name is read as Lean.
            if wanted.isdisjoint(n.rsplit(b'.', 1)[-1] for n in DECLARED.findall(raw)):
                continue
            text = lean.strip_comments(raw.decode('utf-8', 'replace'))
            for d in lean.declarations(text):
                if not d.name:
                    continue
                d.path = path
                if d.name.startswith('_root_.'):
                    d.full = d.name[len('_root_.'):]
                else:
                    d.full = f'{d.namespace}.{d.name}' if d.namespace else d.name
                self.by_short.setdefault(d.short, []).append(d)

    def named(self, full):
        return [d for d in self.by_short.get(full.rsplit('.', 1)[-1], []) if d.full == full]

    def resolve(self, written, paths=()):
        """The declarations a written name may denote, narrowed by the paths beside it."""
        short = written.rsplit('.', 1)[-1]
        hits = [d for d in self.by_short.get(short, [])
                if d.full == written or d.full.endswith('.' + written)]
        if not hits and '.' in written:
            # The qualifier of a document may be the module of the theorem.
            module = '/' + written.rsplit('.', 2)[-2] + '.lean'
            hits = [d for d in self.by_short.get(short, []) if d.path.endswith(module)]
        if len(hits) > 1 and paths:
            near = [d for d in hits if any(p in d.path for p in paths)]
            hits = near or hits
        return hits


def code_spans(text):
    return [s.strip() for s in re.findall(r'`([^`\n]+)`', text)]


def names_in(text):
    return [s for s in code_spans(text) if NAME.fullmatch(s)]


def cells(line):
    return [c.strip() for c in re.split(r'(?<!\\)\|', line.strip())[1:-1]]


def read_text(root, rel):
    try:
        with open(os.path.join(root, rel), encoding='utf-8') as f:
            return f.read()
    except OSError:
        return None


def compiler_names(text):
    """(written name, path hints, opens an entry) of HEADLINES.md."""
    out = []
    for block in re.split(r'\n[ \t]*\n|\n(?=- )', text):
        first = block.lstrip('\n')
        paths = [s.strip('`') for s in re.findall(r'`[\w/]+\.lean`', block)]
        lead = []
        if first.startswith('|'):
            for line in first.splitlines():
                row = cells(line)
                if len(row) == 2:
                    lead += [n for link in re.findall(r'\[([^\]]+)\]', row[1]) for n in names_in(link)]
        else:
            m = re.match(r'(?:- )?(`[^`\n]+`(?:(?:,| and|, and)\s+`[^`\n]+`)*)', first)
            if m:
                lead = names_in(m.group(1))
        out += [(n, paths, True) for n in lead]
        out += [(n, paths, False) for n in names_in(block) if n not in lead]
    return out


def core_names(root):
    out = []
    joy = read_text(root, 'JoyOfCrypto.md') or ''
    columns = None
    for line in joy.splitlines():
        if not line.startswith('|'):
            columns = None
            continue
        row = cells(line)
        if columns is None:
            columns = row
        elif 'Main results' in columns and 'Module' in columns and len(row) == len(columns):
            paths = [f'/{m.rstrip("*")}' if m.endswith('/*') else f'/{m}.lean'
                     for m in code_spans(row[columns.index('Module')])]
            out += [(n, paths, True) for n in names_in(row[columns.index('Main results')])]
    qrom = read_text(root, 'CatCryptCore/Crypto/MLKEM/QROM.md') or ''
    m = re.search(r'^## 1\. .*?(?=^## |\Z)', qrom, re.M | re.S)
    for line in (m.group(0).splitlines() if m else ()):
        if line.startswith('| [`'):
            out += [(n, ['/MLKEM/'], True) for n in names_in(cells(line)[0])]
    for line in (read_text(root, 'README.md') or '').splitlines():
        paths = re.findall(r'CatCryptCore/[\w/]+\.lean', line)
        out += [(n, paths, False) for n in names_in(line)]
    return out


def check(root, kind, listing):
    label = os.path.basename(os.path.abspath(root))
    errors = []
    registry, missing = read_text(root, REGISTRY), read_text(root, MISSING)
    if kind == 'compiler':
        cited = compiler_names(read_text(root, 'HEADLINES.md') or '')
    else:
        cited = core_names(root)
    wanted = {written.rsplit('.', 1)[-1] for written, _, _ in cited}
    for line in (registry or '').splitlines():
        f = line.split('\t')
        if len(f) == 4 and not line.startswith('#'):
            wanted |= {f[0].rsplit('.', 1)[-1], f[3].rsplit('.', 1)[-1]}
    index = Index(root, kind, wanted)

    documented = {}
    undeclared = set()
    for written, paths, lead in cited:
        hits = index.resolve(written, paths)
        if lead and not hits:
            undeclared.add(written)
        # An operation (`bind`) is no theorem of that name in some namespace.
        if not lead and '.' not in written and '_' not in written and len({d.full for d in hits}) > 1:
            continue
        for d in hits:
            if d.kind in THEOREM:
                documented[d.full] = documented.get(d.full, False) or lead
    if not documented:
        errors.append('the documents name no theorem; the extraction or the documents changed')

    rows = {}
    if registry is None:
        errors.append(f'{REGISTRY} is missing')
    for line in (registry or '').splitlines():
        if not line.strip() or line.startswith('#'):
            continue
        f = line.split('\t')
        if len(f) != 4 or f[1] not in ('headline', 'cited') or f[2] not in ('bound', 'statement'):
            errors.append(f'malformed row: {line}')
        elif f[0] in rows:
            errors.append(f'two rows for {f[0]}')
        else:
            rows[f[0]] = f[1:]

    if listing:
        for full in sorted(set(documented) | set(rows)):
            place = 'headline' if documented.get(full) else 'named' if full in documented else '-'
            row = rows.get(full, ['-', '-', '-'])
            print('\t'.join([label, full, place] + row))
        return 0

    recorded, count = [], None
    if missing is None:
        errors.append(f'{MISSING} is missing')
    for line in (missing or '').splitlines():
        s = line.strip()
        if re.fullmatch(r'count=\d+', s):
            count = int(s[6:])
        elif s and not s.startswith('#'):
            recorded.append(s)
    if missing is not None:
        if count is None:
            errors.append(f'{MISSING} has no count line')
        elif len(recorded) > count:
            errors.append(f'the recorded list of missing witnesses grew ({count} -> {len(recorded)})')
        if len(recorded) != len(set(recorded)):
            errors.append(f'{MISSING} repeats a name')

    for full, lead in sorted(documented.items()):
        if full not in rows:
            errors.append(f'{full} is not registered: add its row to {REGISTRY}, with its witness')
        elif lead and rows[full][0] != 'headline':
            errors.append(f'{full} is a headline of the documents and is registered as cited')

    with_witness = headlines = 0
    for full, (role, claim, witness) in rows.items():
        decls = index.named(full)
        if not decls:
            errors.append(f'registered {full} is no declaration of the tree')
        if role != 'headline':
            continue
        headlines += 1
        if witness == '-':
            if full not in recorded:
                errors.append(f'{full} has no witness and is not in {MISSING}')
            continue
        with_witness += 1
        if full in recorded:
            errors.append(f'{full} has a witness: remove it from {MISSING} and lower the count')
        found = index.named(witness)
        if not found:
            errors.append(f'the witness {witness} of {full} is no declaration of the tree')
        elif witness == full:
            errors.append(f'{full} is registered as its own witness')
        else:
            text = found[0].text
            short = full.rsplit('.', 1)[-1]
            if not re.search(r"(?<![\w'])%s(?![\w'])" % re.escape(short), text):
                errors.append(f'the witness {witness} does not name {short}')
            if re.search(r'(?<![\w.])sorry(?!\w)', text):
                errors.append(f'the witness {witness} is not proved')
            if claim == 'bound' and not re.search(r'<\s*\(?1(?![\w.])', found[0].sig):
                errors.append(f'the witness {witness} of the bound {full} states no `< 1`')
    for written in sorted(undeclared):
        if f'undeclared {written}' not in recorded:
            errors.append(f'the documents name the headline {written}, which is no declaration of the tree')
    for full in recorded:
        if full.startswith('undeclared '):
            if full[len('undeclared '):] not in undeclared:
                errors.append(f'{MISSING} records {full}, which the documents no longer name or which is declared')
        elif full not in rows or rows[full][0] != 'headline':
            errors.append(f'{MISSING} records {full}, which is no registered headline')

    for e in errors:
        print(f'FAIL ({label}): {e}')
    print(f'headline-witness ({label}): {headlines} headlines, {with_witness} with a witness, '
          f'{len(recorded)} recorded as missing, {len(errors)} errors')
    return 1 if errors else 0


listing = '--list' in args
if '--root' in args:
    at = args.index('--root') + 1
    roots = [args[at]] if at < len(args) else []
    if not roots or not flavour(roots[0]):
        sys.exit('headline-witness: --root needs a checkout of core or the compiler')
else:
    own = os.path.dirname(here)
    if flavour(own):
        roots = [own]
    else:
        roots = []
        for name in ('CatCrypt-core', 'catcrypt-compiler'):
            root = os.path.join(os.path.dirname(own), name)
            if flavour(root) and os.path.isfile(os.path.join(root, REGISTRY)):
                roots.append(root)
            else:
                print(f'headline-witness ({name}): skipped, no checkout with a registry')
rc = 0
for root in roots:
    rc |= check(root, flavour(root), listing)
sys.exit(rc)
PY
