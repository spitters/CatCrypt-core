#!/usr/bin/env python3
"""Statement shapes that empty a security theorem: the token rules of the categories
`point_mass`, `point_mass_use`, `same_body`, `free_witness` and `returned_arg` of
scripts/unbounded-hardness-ratchet.sh, which documents and runs them.

The input is `repo<TAB>path` lines, the output `category:path:line:declaration`, with the
category prefixed by `core_` or `compiler_` for a file of that repository. Lean is read as
text with comments removed; nothing is elaborated and no definition of another file is
unfolded.
"""
import re
import sys

MODIFIERS = (r'(?:(?=[plmnsu])(?:private|protected|public|noncomputable|partial|unsafe|nonrec'
             r'|scoped|local|meta)[ \t]+)*')
BOUNDARY = re.compile(
    r'^[ \t]*(?=[@acdeilmnopstu])(?:@\[[^\]\n]*\][ \t\n]*)*' + MODIFIERS + r'(?=[acdeilost])(?:'
    r'(theorem|lemma|def|abbrev|structure|class|instance|example|inductive|axiom|opaque)'
    r'(?=[ \t\n])[ \t\n]*([^\s:({\[⦃]*)|section\b)'
    r'|^(?=[#aeimnosuv])(?:namespace|end|open|variable|set_option|attribute|mutual|notation|syntax'
    r'|macro|export|universe|import|#\w+)\b', re.M)
IMPORT = re.compile(rb'^(?:(?:public|private|meta)[ \t]+)*import[ \t]+(?:all[ \t]+)?(\S+)', re.M)
COMMENT_START = re.compile(r'/-|--')
BLOCK_EDGE = re.compile(r'/-|-/')
TOKEN = re.compile(r":=|=>|←|[()\[\]{}⟨⟩⦃⦄]|[^\W\d][\w'.!?]*|\.[^\W\d][\w'.!?]*|\d+|\S")
OPEN = set('([{⟨⦃')
CLOSE = set(')]}⟩⦄')
PAIR_START = re.compile(r'[(\[{⟨⦃)\]}⟩⦄:|]|\blet\b|\bwhere\b')

# A comparison of two games, by the last component of its name.
COMPARE = re.compile(r'^(?:Advantage\w*|\w*Advantage|[sk]dist\w*|\w*[SK]dist\w*|DistC'
                     r'|UCEmulates\w*|absDiff)$')
UNIFORM = {'sample', 'uniform', 'uniformOfFintype', 'uniformSample', 'sampleUniform', 'duni',
           'duniform'}
RUN_PREDICATE = {'RunSafe': (0, 1), 'AccessIn': (1, 2), 'StoreIn': (1, 2), 'LoadIn': (1, 2)}
COMPARE_HINT = re.compile(r'Advantage|dist|UCEmulates|absDiff|DistC')
KEYWORDS = {'fun', 'let', 'do', 'if', 'then', 'else', 'match', 'with', 'in', 'by'}
IDEAL = re.compile(r'ideal', re.I)
RUN_HEAD = re.compile(r"(?<![\w'])(%s)(?![\w'])" % '|'.join(RUN_PREDICATE))
REFL = re.compile(r"(?:by )?(?:exact )?(?:fun [\w ]+ => )?(?:rfl|\.rfl|Eq\.refl(?: \S+)?"
                  r"|le_rfl|le_refl(?: \S+)?|HEq\.rfl|Iff\.rfl)$")


def strip_comments(text):
    """`text` without block and line comments, with every newline kept."""
    out = []
    pos = 0
    while True:
        m = COMMENT_START.search(text, pos)
        if not m:
            out.append(text[pos:])
            return ''.join(out)
        out.append(text[pos:m.start()])
        if m.group() == '--':
            pos = text.find('\n', m.end())
            if pos < 0:
                return ''.join(out)
            continue
        depth, at = 1, m.end()
        while depth:
            e = BLOCK_EDGE.search(text, at)
            if not e:
                at = len(text)
                break
            depth += 1 if e.group() == '/-' else -1
            at = e.end()
        out.append('\n' * text.count('\n', m.start(), at))
        pos = at


def split_signature(text):
    """Signature and body, at the first `:=`, `where` or match arm at bracket depth 0."""
    depth = lets = 0
    for m in PAIR_START.finditer(text):
        s, i = m.group(), m.start()
        if s in OPEN:
            depth += 1
        elif s in CLOSE:
            depth = max(0, depth - 1)
        elif depth:
            continue
        elif s == 'let':
            lets += 1
        elif s == 'where':
            return text[:i], text[m.end():]
        elif s == ':' and text.startswith(':=', i):
            if lets:
                lets -= 1
            else:
                return text[:i], text[i + 2:]
        elif s == '|':
            start = text.rfind('\n', 0, i) + 1
            if start and not text[start:i].strip():
                end = text.find('\n', i)
                if '=>' in text[i:len(text) if end < 0 else end]:
                    return text[:i], text[i:]
    return text, ''


def conclusion_at(sig):
    """Position after the colon that begins the conclusion of a signature, or None."""
    depth = 0
    for m in PAIR_START.finditer(sig):
        s = m.group()
        if s in OPEN:
            depth += 1
        elif s in CLOSE:
            depth = max(0, depth - 1)
        elif s == ':' and not depth:
            return m.end()
    return None


class Decl:
    def __init__(self, kind, name, namespace, line, text):
        self.kind, self.name, self.namespace, self.line, self.text = kind, name, namespace, line, text
        self._parts = None

    @property
    def parts(self):
        if self._parts is None:
            # The text after the declaration's name.
            self._parts = split_signature(self.text)
        return self._parts

    sig = property(lambda self: self.parts[0])
    body = property(lambda self: self.parts[1])
    short = property(lambda self: self.name.rsplit('.', 1)[-1])


def declarations(text):
    marks = list(BOUNDARY.finditer(text))
    decls = []
    scope = []
    line = 1
    pos = 0
    for i, m in enumerate(marks):
        line += text.count('\n', pos, m.start())
        pos = m.start()
        end = marks[i + 1].start() if i + 1 < len(marks) else len(text)
        if not m.group(1):
            words = text[m.start():end].lstrip().split('\n', 1)[0].split()
            if words[0] == 'namespace':
                scope += words[1].split('.') if len(words) > 1 else ['']
            elif 'section' in words[:5]:
                at = words.index('section') + 1
                scope += [''] * (len(words[at].split('.')) if at < len(words) else 1)
            elif words[0] == 'mutual':
                scope.append('')
            elif words[0] == 'end' and scope:
                del scope[-(len(words[1].split('.')) if len(words) > 1 else 1):]
            continue
        keyword_line = line + text.count('\n', m.start(), m.start(1))
        decls.append(Decl(m.group(1), m.group(2), '.'.join(s for s in scope if s),
                          keyword_line, text[m.end():end]))
    return decls


def arguments(text, pos, limit=12):
    """Argument terms of an application whose head ends at `pos`, and the position after them."""
    args = []
    depth = start = 0
    end = pos
    for m in TOKEN.finditer(text, pos):
        s = m.group()
        if s in OPEN:
            if not depth:
                start = m.start()
            depth += 1
        elif s in CLOSE:
            if not depth:
                break
            depth -= 1
            if not depth:
                args.append(text[start:m.end()])
                end = m.end()
        elif depth:
            continue
        elif s in KEYWORDS or not (s[0].isalnum() or s[0] == '_' or (s[0] == '.' and len(s) > 1)):
            break
        else:
            args.append(s)
            end = m.end()
        if len(args) >= limit:
            break
    return args, end


def unwrap(term):
    """A term without outer parentheses, type ascription, leading `fun` or `do`."""
    t = ' '.join(term.split())
    while True:
        before = t
        m = re.match(r'(?:fun|λ) [^=]*=> ?|\| [^=|]*=> ?|do ', t)
        if m:
            t = t[m.end():]
        if t.startswith('(') and t.endswith(')'):
            depth = 0
            colon = None
            for i, c in enumerate(t):
                if c in OPEN:
                    depth += 1
                elif c in CLOSE:
                    depth -= 1
                    if not depth and i < len(t) - 1:
                        break
                elif c == ':' and depth == 1 and colon is None and not t.startswith(':=', i):
                    colon = i
            else:
                t = t[1:colon if colon else -1].strip()
        if t == before:
            return t


def distribution(term, defs, depth=0):
    """'point' for a point mass, 'uniform' for one uniform sample, else None."""
    t = unwrap(term)
    first = TOKEN.match(t)
    if not first:
        return None
    head = first.group().rsplit('.', 1)[-1]
    args, end = arguments(t, first.end())
    if t[end:].strip():
        # `pure $ x` and `return x + y` are point masses; a bind or a second statement is not.
        if head in ('pure', 'return') and not re.search(r'←|=>|>>=|\blet\b|\bdo\b', t):
            return 'point'
        return None
    if head in ('pure', 'return') and args:
        return 'point'
    if head in UNIFORM and len(args) <= 1:
        return 'uniform'
    if head == 'liftSDistr' and len(args) == 1 and depth < 4:
        return distribution(args[0], defs, depth + 1)
    if depth < 4 and len(defs.get(head, ())) == 1:
        return distribution(defs[head][0].body, defs, depth + 1)
    return None


def compared_pairs(text):
    """The adjacent argument pairs of the comparisons in `text`, with the comparison's name."""
    done = 0
    for hint in COMPARE_HINT.finditer(text):
        a = hint.start()
        if a < done:
            continue
        while a > 0 and (text[a - 1].isalnum() or text[a - 1] in "_'."):
            a -= 1
        word = TOKEN.match(text, a)
        if not word:
            continue
        done = word.end()
        head = word.group().rsplit('.', 1)[-1]
        if COMPARE.match(head):
            args, _ = arguments(text, done)
            for j in range(len(args) - 1):
                yield head, j, args[j], args[j + 1]


def point_mass(decls, defs):
    for d in decls:
        if not COMPARE_HINT.search(d.text):
            continue
        if d.kind in ('def', 'abbrev', 'structure', 'class'):
            text = d.text
        elif d.kind in ('theorem', 'lemma', 'instance', 'example', 'axiom'):
            text = d.sig
        else:
            continue
        for _, _, a, b in compared_pairs(text):
            ka = distribution(a, defs)
            if ka and {ka, distribution(b, defs)} == {'point', 'uniform'}:
                yield d
                break


def same_body(decls):
    flat = lambda s: ' '.join(s.split())
    defs = [d for d in decls if d.kind in ('def', 'abbrev') and d.name]
    by_name = {}
    for d in defs:
        by_name.setdefault(d.name.lower(), []).append(d)
    found = set()
    for d in defs:
        if IDEAL.search(d.name):
            reals = by_name.get(IDEAL.sub('real', d.name).lower(), [])
            reals = [r for r in reals if r.namespace == d.namespace] or (reals if len(reals) == 1 else [])
            if reals:
                body, real = flat(d.body), reals[0]
                alias = real.short in body and re.fullmatch(
                    r"(?:(?:fun|λ) [\w' ]+ => )?(?:[\w']+\.)*" + re.escape(real.short)
                    + r"(?: [\w'.]+| \([^()]*\))*", body)
                recursion = body
                if d.short in body:
                    recursion = re.sub(r'\b%s\b' % re.escape(d.short), real.short, body)
                if body and (recursion == flat(real.body) or alias):
                    found.add(d)
                    yield d
                    continue
        # An advantage defined by comparing a game with itself.
        if d not in found and 'Advantage' in d.name + d.text:
            for head, j, a, b in compared_pairs(d.body):
                if j == 0 and 'Advantage' in head + d.name and a not in ('_',) \
                        and flat(a) == flat(b) and not a.isdigit():
                    yield d
                    break


def binder_names(text, quantifier):
    """(name, position after the binder) for every binder of `quantifier` in `text`."""
    for m in re.finditer(quantifier, text):
        depth = 0
        typed = {}
        i = m.end()
        names = []
        for t in TOKEN.finditer(text, i):
            s = t.group()
            if not depth and s in (',', '=>'):
                for n in names:
                    yield n, t.end()
                break
            if s in OPEN:
                depth += 1
                typed[depth] = False
            elif s in CLOSE:
                depth -= 1
                if depth < 0:
                    break
            elif s in (':', '∈'):
                typed[depth] = True
            elif not typed.get(depth) and re.match(r'[^\W\d]', s):
                names.append(s)


def tied(var, text, free):
    """Whether an equation or membership of `text` determines `var` from terms free of `free`."""
    v = re.escape(var)
    end = r"(?![\w'])"
    sides = []
    for m in re.finditer(r"=\s*(?:\.|Option\.)?some\s*(?:%s%s|[(⟨][^()⟨⟩=]*(?<![\w'])%s%s)"
                         % (v, end, v, end), text):
        sides.append(re.split(r'[∧→,∨↔:]', text[:m.start()])[-1])
    for m in re.finditer(r"(?:^|[∧→,∨↔(])\s*%s\s*(?:=|∈)([^∧→,∨↔]*)" % v, text):
        sides.append(m.group(1))
    for m in re.finditer(r"=\s*%s\s*(?=$|[∧→,∨↔)])" % v, text):
        sides.append(re.split(r'[∧→,∨↔:]', text[:m.start()])[-1])
    for side in sides:
        ids = {t.split('.')[0] for t in re.findall(r"[^\W\d][\w'.]*", side)}
        if side.strip() and not ids & free:
            return True
    return False


def free_witness(decls):
    for d in decls:
        if '∃' not in d.text:
            continue
        if d.kind in ('theorem', 'lemma', 'axiom', 'instance', 'example'):
            text = d.sig
        elif d.kind in ('def', 'abbrev', 'structure', 'class', 'inductive'):
            text = d.text
        else:
            continue
        if '∃' not in text or not any(p in text for p in RUN_PREDICATE):
            continue
        bound = list(binder_names(text, '∃'))
        free = {n for n, _ in bound}
        for head in RUN_HEAD.finditer(text):
            start = head.start()
            positions = RUN_PREDICATE[head.group(1)]
            args, _ = arguments(text, head.end(), 4)
            roots = []
            for p in positions:
                if p < len(args):
                    roots += [t.split('.')[0] for t in re.findall(r"[^\W\d][\w'.]*", args[p])]
            if any(v == n and at <= start and not tied(v, text, free)
                   for v in roots for n, at in bound):
                yield d
                break


def leaves(term):
    """The components of nested anonymous constructors."""
    t = term.strip()
    if not (t.startswith('⟨') and t.endswith('⟩')):
        return [t]
    parts, depth, start = [], 0, 1
    for i in range(1, len(t) - 1):
        if t[i] in OPEN:
            depth += 1
        elif t[i] in CLOSE:
            depth -= 1
            if depth < 0:
                return [t]
        elif t[i] == ',' and not depth:
            parts.append(t[start:i])
            start = i + 1
    parts.append(t[start:-1])
    return [x for p in parts for x in leaves(p)]


def returned_arg(decls, variables):
    for d in decls:
        if d.kind not in ('theorem', 'lemma') or '∃' not in d.text or '∃' not in d.sig:
            continue
        at = conclusion_at(d.sig)
        if at is None or '∃' not in d.sig[at:]:
            continue
        head, concl = d.sig[:at - 1], d.sig[at:]
        names = set(variables)
        for group in re.findall(r'[({⦃]([^:(){}⦃⦄]+):', head):
            names.update(group.split())
        names.update(n for n, _ in binder_names(concl.split('∃', 1)[0], '∀'))
        proof = '; '.join(' '.join(x.split()) for x in d.body.split('\n') if x.strip())
        while True:
            m = re.match(r"(?:by|exact|refine)\b[ ;]*|(?:fun|λ) ([\w' ]+)=>[ ;]*"
                         r"|intros? ([\w' ]+);[ ;]*", proof)
            if not m:
                break
            names.update((m.group(1) or m.group(2) or '').split())
            proof = proof[m.end():]
        m = re.fullmatch(r"(?:use|exists) ([\w', ]+?)(?:; (?:exact )?(.+))?", proof)
        if m:
            witnesses = [w.strip() for w in m.group(1).split(',')]
            proofs = [m.group(2) or 'rfl']
        else:
            m = re.fullmatch(r"(⟨.*⟩)(?:; (?:exact )?(.+))?", proof)
            if not m:
                continue
            parts = [p.strip() for p in leaves(m.group(1))]
            witnesses = []
            while parts and parts[0] in names:
                witnesses.append(parts.pop(0))
            proofs = [m.group(2) if p == '?_' and m.group(2) else p for p in parts]
        if witnesses and proofs and all(w in names for w in witnesses) \
                and all(REFL.match(p.strip()) for p in proofs):
            yield d


def module_of(path):
    return re.sub(r'^(?:\.\./[^/]+/)?', '', path)[:-len('.lean')].replace('/', '.')


def read(path):
    try:
        with open(path, 'rb') as f:
            return f.read()
    except OSError:
        return b''


RUN_BYTES = [p.encode() for p in RUN_PREDICATE]
COMPARE_BYTES = [b'Advantage', b'dist', b'UCEmulates', b'absDiff', b'DistC']


def main():
    fixture = '--fixture' in sys.argv[1:]
    files = [ln.rstrip('\n').split('\t', 1) for ln in sys.stdin if '\t' in ln]
    sites = []
    pm_defs = {}

    def emit(repo, cat, path, d):
        prefix = repo + '_' if repo in ('core', 'compiler') else ''
        sites.append(f"{prefix}{cat}:{path}:{d.line}:{d.name or '(' + d.kind + ')'}")

    imported = {}
    for repo, path in files:
        raw = read(path)
        # The imports stand in the head of a file.
        imported[path] = set(IMPORT.findall(raw[:32768]))
        ex = '∃'.encode() in raw
        run = ex and any(p in raw for p in RUN_BYTES)
        ret = ex and (b'rfl' in raw or b'refl' in raw or b'exists ' in raw or b'use ' in raw)
        compare = any(p in raw for p in COMPARE_BYTES)
        mass = compare and (b'pure' in raw or b'return' in raw) \
            and (b'ample' in raw or b'uniform' in raw or b'duni' in raw)
        twin = b'deal' in raw or b'DEAL' in raw or b'Advantage' in raw
        if not (run or ret or mass or twin):
            continue
        text = strip_comments(raw.decode('utf-8', 'replace'))
        decls = declarations(text)
        if mass:
            defs = {}
            for d in decls:
                if d.kind in ('def', 'abbrev') and d.name:
                    defs.setdefault(d.short, []).append(d)
            for d in point_mass(decls, defs):
                emit(repo, 'point_mass', path, d)
                if d.kind in ('def', 'abbrev'):
                    pm_defs.setdefault(d.short, set()).add((module_of(path), d.line))
        if twin:
            for d in same_body(decls):
                emit(repo, 'same_body', path, d)
        if run:
            for d in free_witness(decls):
                emit(repo, 'free_witness', path, d)
        if ret:
            variables = set()
            for line in re.findall(r'^variable\b(.*)$', text, re.M):
                for group in re.findall(r'[({⦃]([^:(){}⦃⦄]+):', line):
                    variables.update(group.split())
            for d in returned_arg(decls, variables):
                emit(repo, 'returned_arg', path, d)

    if pm_defs:
        # A statement over such a definition, in its file or in a file that imports it.
        for repo, path in files:
            visible = imported[path] | {module_of(path).encode()}
            names = [n for n, where in pm_defs.items()
                     if any(m.encode() in visible for m, _ in where)]
            if not names:
                continue
            raw = read(path)
            if not any(n.encode() in raw for n in names):
                continue
            source = raw.decode('utf-8', 'replace')
            word = re.compile(r"(?<![\w'])(?:%s)(?![\w'])" % '|'.join(map(re.escape, names)))
            for d in declarations(strip_comments(source)):
                if d.kind in ('theorem', 'lemma', 'structure', 'class', 'axiom', 'instance') \
                        and word.search(d.sig + (d.body if d.kind in ('structure', 'class') else '')):
                    emit(repo, 'point_mass_use', path, d)

    for s in sites:
        if fixture:
            cat, _, line, _ = s.split(':', 3)
            print(f'{cat}:{line}')
        else:
            print(s)


if __name__ == '__main__':
    main()
