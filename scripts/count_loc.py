#!/usr/bin/env python3
"""Measure the size table of the paper on this artifact.

Counting method, as stated in Sec. 6.2: lines of Lean code excluding blank lines and
comments (line comments and block comments, nested); theorems are `theorem` and `lemma`
declarations (with optional attribute and `private`/`protected`/`noncomputable` modifiers).

Usage: python3 scripts/count_loc.py [ZFLean]   (from the repository root)
"""
import glob, os, re, sys

COMPONENTS = [
    ("Relational calculus", ["Functions"]),
    ("Embeddings, isomorphisms", ["Embeddings", "Isomorphisms"]),
    ("Naturals, set-level recursion", ["Naturals", "Recursion"]),
    ("Integers, integer division", ["Integers"]),
    ("Booleans, sums, quotients, rationals", ["Booleans", "Sum", "Quotient", "Rationals"]),
    ("Transfer tactic, lemma sets, examples", ["Transfer", "TransferAlgebra", "Examples"]),
    ("Core glue and automation", ["Basic", "Def", "Tactics"]),
    ("Case study: semantics of IMP", ["Imp"]),
]

THM = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*(?:theorem|lemma)\b', re.M)


def strip_block_comments(src):
    out, i, depth, n = [], 0, 0, len(src)
    while i < n:
        if src.startswith('/-', i):
            depth += 1; i += 2; continue
        if depth > 0 and src.startswith('-/', i):
            depth -= 1; i += 2; continue
        if depth > 0:
            out.append('\n' if src[i] == '\n' else ' '); i += 1; continue
        out.append(src[i]); i += 1
    return ''.join(out)


def count(path):
    text = strip_block_comments(open(path, encoding='utf-8').read())
    loc = sum(1 for line in text.split('\n') if line.strip() and not line.strip().startswith('--'))
    return loc, len(THM.findall(text))


def main():
    root = sys.argv[1] if len(sys.argv) > 1 else os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', 'ZFLean')
    per_file = {os.path.splitext(os.path.basename(f))[0]: count(f)
                for f in glob.glob(os.path.join(root, '*.lean'))}
    # the case study is a separate target, kept apart from the library as a client of it
    per_file['Imp'] = count(os.path.join(root, '..', 'casestudy', 'Imp.lean'))
    seen, tot = set(), [0, 0]
    for name, files in COMPONENTS:
        loc = sum(per_file[f][0] for f in files); thm = sum(per_file[f][1] for f in files)
        seen.update(files); tot[0] += loc; tot[1] += thm
        print(f"{name:40s} {loc:6,d} {thm:5d}")
    print(f"{'Total':40s} {tot[0]:6,d} {tot[1]:5d}")
    rest = sorted(set(per_file) - seen)
    if rest:
        print("\nNot assigned to a component:", ', '.join(rest))


if __name__ == '__main__':
    main()
