#!/usr/bin/env python3
"""Alternative blueprint graph views (the single leanblueprint graph is too dense
at ~200 nodes). Parses the chapter .tex for label -> chapter and the \\uses edges,
then emits two Graphviz views:

  1. overview.svg  — one node per chapter, aggregated inter-chapter dependencies
                     (the 30,000-ft architecture: ~8 nodes).
  2. clustered.svg — every node, but grouped into per-chapter cluster boxes with a
                     hierarchical `dot` layout instead of a force-directed hairball.

Also writes per-chapter subgraphs (chNN.svg). Run after the blueprint is built.
"""
import os
import re
import subprocess

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CH = os.path.join(ROOT, "blueprint", "src", "chapters")
OUT = os.path.join(ROOT, "blueprint", "web", "graphs")
os.makedirs(OUT, exist_ok=True)

BLOCK = re.compile(
    r"\\begin\{(definition|theorem|lemma|proposition|corollary)\}(?:\[([^\]]*)\])?(.*?)\\end\{\1\}",
    re.DOTALL,
)
LABEL = re.compile(r"\\label\{([^}]+)\}")
USES = re.compile(r"\\uses\{([^}]+)\}")

PALETTE = ["#e8f0fe", "#e6f4ea", "#fef7e0", "#fce8e6", "#f3e8fd",
           "#e0f7fa", "#fff0e6", "#eef2f4"]

chapters = []           # [(chapter_title, [ (label, node_title, [dep,...]) ]) ]
label_chapter = {}      # label -> chapter index

for fn in sorted(os.listdir(CH)):
    if not fn.endswith(".tex"):
        continue
    src = open(os.path.join(CH, fn), encoding="utf-8").read()
    ct = re.search(r"\\chapter\{([^}]*)\}", src)
    title = ct.group(1) if ct else fn
    nodes = []
    ci = len(chapters)
    for m in BLOCK.finditer(src):
        body = m.group(3)
        lab = LABEL.search(body)
        if not lab:
            continue
        label = lab.group(1)
        node_title = (m.group(2) or label).strip()
        deps = []
        for u in USES.finditer(body):
            deps += [d.strip() for d in u.group(1).split(",") if d.strip()]
        nodes.append((label, node_title, deps))
        label_chapter[label] = ci
    chapters.append((title, nodes))


def esc(s):
    return s.replace("&", "and").replace('"', "'").replace("\\", "")


# ---- 1. chapter overview -------------------------------------------------
lines = ['digraph overview {', '  rankdir=LR; node [shape=box style="filled,rounded" '
         'fontname="Helvetica" fontsize=11];', '  edge [color="#888888"];']
inter = {}
for ci, (title, nodes) in enumerate(chapters):
    for _, _, deps in nodes:
        for d in deps:
            dj = label_chapter.get(d)
            if dj is not None and dj != ci:
                inter[(ci, dj)] = inter.get((ci, dj), 0) + 1
for ci, (title, nodes) in enumerate(chapters):
    lines.append(f'  c{ci} [label="{esc(title)}\\n({len(nodes)} results)" '
                 f'fillcolor="{PALETTE[ci % len(PALETTE)]}"];')
for (ci, dj), w in inter.items():
    lines.append(f'  c{ci} -> c{dj} [penwidth={min(1+w/3,5):.1f} label="{w}"];')
lines.append("}")
open(os.path.join(OUT, "overview.dot"), "w").write("\n".join(lines))

# ---- 2. clustered full graph --------------------------------------------
lines = ['digraph clustered {', '  compound=true; rankdir=LR;',
         '  node [shape=box style=filled fontname="Helvetica" fontsize=9];',
         '  edge [color="#bbbbbb" arrowsize=0.6];']
for ci, (title, nodes) in enumerate(chapters):
    lines.append(f'  subgraph cluster_{ci} {{ label="{esc(title)}"; '
                 f'style="filled,rounded"; color="#cccccc"; '
                 f'fillcolor="{PALETTE[ci % len(PALETTE)]}";')
    for label, node_title, _ in nodes:
        lines.append(f'    "{label}" [label="{esc(node_title)[:34]}"];')
    lines.append("  }")
for ci, (title, nodes) in enumerate(chapters):
    for label, _, deps in nodes:
        for d in deps:
            if d in label_chapter:
                lines.append(f'  "{d}" -> "{label}";')
lines.append("}")
open(os.path.join(OUT, "clustered.dot"), "w").write("\n".join(lines))

# render
for name in ("overview", "clustered"):
    dot = os.path.join(OUT, name + ".dot")
    svg = os.path.join(OUT, name + ".svg")
    subprocess.run(["dot", "-Tsvg", dot, "-o", svg], check=True)
    print(f"wrote {svg}")

# simple index
idx = ('<!doctype html><meta charset=utf-8><title>Blueprint graph views</title>'
       '<style>body{font-family:Helvetica;margin:2em;max-width:70em}'
       'h2{margin-top:1.5em}img{max-width:100%;border:1px solid #ccc}</style>'
       '<h1>CatCrypt Core blueprint — graph views</h1>'
       '<p>Alternatives to the dense force-directed graph.</p>'
       '<h2>Chapter overview</h2><p>One node per chapter; edge labels count '
       'cross-chapter dependencies.</p><img src="overview.svg">'
       '<h2>Clustered (all results, grouped by chapter)</h2>'
       '<img src="clustered.svg">')
open(os.path.join(OUT, "index.html"), "w").write(idx)
print(f"wrote {os.path.join(OUT, 'index.html')}")
