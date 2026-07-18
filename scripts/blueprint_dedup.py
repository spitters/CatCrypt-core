#!/usr/bin/env python3
"""Remove duplicate blueprint nodes (same \\lean target authored in two chapters).

Canonical ownership: couplings/liftR live in ch02 (Probability); the Relational
advantage results live in ch04. Strip the duplicate \\begin..\\end blocks from the
non-owning chapter, matching a block by the \\lean{} target it carries.
"""
import re, sys, os

CH = os.path.join(os.path.dirname(__file__), "..", "blueprint", "src", "chapters")

# (file, {lean targets whose block to remove from that file})
JOBS = [
    ("ch04_relational.tex", {
        "CatCrypt.Prob.Coupling", "CatCrypt.Prob.Coupling.satisfies",
        "CatCrypt.Prob.liftR", "CatCrypt.Prob.liftR_bind", "CatCrypt.Prob.liftR_pure",
        "CatCrypt.Prob.liftR_refl", "CatCrypt.Prob.liftR_uniform_bij",
    }),
    ("ch03_advantage.tex", {
        "CatCrypt.Relational.advantage_factorization",
        "CatCrypt.Relational.advantage_symm",
        "CatCrypt.Crypto.advantage_zero_of_rHoare",
    }),
]

BLOCK = re.compile(r"\\begin\{(definition|theorem|lemma|proposition|corollary)\}.*?\\end\{\1\}", re.DOTALL)

for fname, targets in JOBS:
    path = os.path.join(CH, fname)
    src = open(path).read()
    removed = []
    def repl(m):
        block = m.group(0)
        leans = re.findall(r"\\lean\{([^}]*)\}", block)
        names = {n.strip() for group in leans for n in group.split(",")}
        if names & targets:
            removed.append(names & targets)
            return ""  # drop the block
        return block
    out = BLOCK.sub(repl, src)
    # collapse the blank gap left behind
    out = re.sub(r"\n{3,}", "\n\n", out)
    open(path, "w").write(out)
    print(f"{fname}: removed {len(removed)} duplicate node(s): {sorted(t for s in removed for t in s)}")
