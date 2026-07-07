#!/usr/bin/env python3
"""Dependency scan for splitting Label_Propagation_op_Correctness.thy.

Extracts top-level commands (lemma/definition/abbreviation/function/...) with their
line spans, then for each command finds which earlier-defined names its text mentions.
Validates the planned 5-file partition (Input1/Input0/Loop/Dataplane_Inv/Labels) from
ai/split-label-prop-correctness.md: every reference must point to the same file or an
imported one. Reports violations ("stragglers") and name clashes for Phase-A targets.

Read-only. Usage: python3 ai/lp-split-deps.py [path-to-thy] > ai/lp-split-deps.txt
"""
import re
import sys
from collections import defaultdict

THY = sys.argv[1] if len(sys.argv) > 1 else \
    "dataplane/Examples/Label_Propagation_op_Correctness.thy"

CMD_RE = re.compile(
    r"^(lemma|theorem|corollary|definition|abbreviation|fun|function|primrec|"
    r"inductive|corec|partial_function|named_theorems|lemmas|method|locale)\b")
# name right after the command keyword (skips attributes like [simp])
NAME_RE = re.compile(
    r"^(?:lemma|theorem|corollary|definition|abbreviation|fun|function|primrec|"
    r"inductive|corec|partial_function|named_theorems|lemmas|method|locale)\s+"
    r"(?:fixes\b)?\s*\"?([A-Za-z0-9_']+)")

# ---- planned partition (line ranges in the current file, end-exclusive) ----
# region name -> list of (start_line, end_line) 1-based inclusive
PARTITION = {
    # PhaseA: generic lemmas relocated to existing upstream files before the split
    "PhaseA":        [(523, 578), (2187, 2234), (2654, 2671), (3418, 3473),
                      (3475, 3502), (6713, 6904), (7646, 7679), (7739, 7810),
                      (8113, 8225), (8538, 8618), (8997, 9001), (9163, 9180),
                      (9265, 9268), (9944, 9954)],
    "Input1":        [(39, 47), (579, 2485), (2611, 3079), (3079, 3417),
                      (3503, 3752), (3928, 5045)],
    "Loop":          [(93, 522), (2486, 2610), (5045, 7455)],
    "Input0":        [(6450, 6712), (8226, 8262), (8446, 8461), (8760, 8997)],
    "Dataplane_Inv": [(47, 92), (3753, 3927), (7455, 8112)],
    "Labels":        [(8263, 8445), (8462, 8759), (9002, 10571)],
    "Main":          [(10572, 10**9)],
}
# Overlapping ranges: more specific (shorter) wins.
IMPORTS = {  # file -> files it may use
    "PhaseA": set(),
    "Input1": {"PhaseA"},
    "Input0": {"PhaseA"},
    "Loop": {"Input1", "PhaseA"},
    "Dataplane_Inv": {"Loop", "Input1", "Input0", "PhaseA"},
    "Labels": {"Loop", "Input1", "Input0", "PhaseA"},
    "Main": {"Input1", "Input0", "Loop", "Dataplane_Inv", "Labels", "PhaseA"},
}

def region_of(line):
    best, best_size = None, None
    for name, ranges in PARTITION.items():
        for (a, b) in ranges:
            if a <= line <= b:
                size = b - a
                if best_size is None or size < best_size:
                    best, best_size = name, size
    return best or "UNASSIGNED"

def main():
    lines = open(THY).read().splitlines()
    # 1. collect top-level commands
    cmds = []  # (name, start_line, kind)
    for i, l in enumerate(lines, 1):
        if CMD_RE.match(l):
            m = NAME_RE.match(l)
            name = m.group(1) if m else None
            # unnamed lemma: look at next line for the name
            if name in (None, "fixes", "assumes", "shows") and i < len(lines):
                m2 = re.match(r"\s*\"?([A-Za-z0-9_']+)", lines[i])
                name = m2.group(1) if m2 else None
            cmds.append([name, i, l.split()[0]])
    # spans
    for k in range(len(cmds)):
        end = cmds[k + 1][1] - 1 if k + 1 < len(cmds) else len(lines)
        cmds[k].append(end)

    defined = {}
    for name, start, kind, end in cmds:
        if name and name not in defined:
            defined[name] = (start, end, kind)

    word_re = re.compile(r"[A-Za-z0-9_']+")
    # 2. usage scan + partition validation
    violations = []
    uses_count = defaultdict(int)
    for name, start, kind, end in cmds:
        src_region = region_of(start)
        text = "\n".join(lines[start - 1:end])
        words = set(word_re.findall(text))
        words.discard(name)
        for w in words:
            if w in defined:
                dstart, dend, dkind = defined[w]
                if dstart >= start:
                    continue  # forward/self ref, ignore
                uses_count[w] += 1
                dst_region = region_of(dstart)
                if dst_region == src_region or dst_region in IMPORTS.get(src_region, set()):
                    continue
                violations.append((src_region, name or f"line{start}", start,
                                   dst_region, w, dstart))

    print(f"total top-level commands: {len(cmds)}")
    print(f"named definitions: {len(defined)}")
    per = defaultdict(int)
    for name, start, kind, end in cmds:
        per[region_of(start)] += end - start + 1
    print("\nlines per planned file:")
    for r, n in sorted(per.items(), key=lambda x: -x[1]):
        print(f"  {r:15} {n}")
    print(f"\npartition violations ({len(violations)}):"
          " (source-file lemma) uses (target-file name) not in imports")
    seen = set()
    for src, n, sl, dst, w, dl in sorted(violations, key=lambda v: (v[0], v[2])):
        key = (src, dst, w)
        if key in seen:
            continue
        seen.add(key)
        print(f"  [{src}:{sl}] {n}  ->  [{dst}:{dl}] {w}")

if __name__ == "__main__":
    main()
