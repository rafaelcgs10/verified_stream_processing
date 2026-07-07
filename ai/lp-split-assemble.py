#!/usr/bin/env python3
"""Assemble the Phase-B split files for Label_Propagation_op_Correctness.thy.

Builds a name->target map from the pre-Phase-A version of the file (whose line
numbers the validated partition in lp-split-deps.py refers to), then walks the
CURRENT file's prerequisite region (everything between the header and
`lemma label_propagation_correctness`) and appends each top-level command's text
to its target block. Section headers and comments attach to the following command.

Outputs block files into the scratchpad directory. Read-only w.r.t. the repo.
"""
import re
import subprocess
import sys

sys.path.insert(0, "ai")
REPO = "."
CUR = "dataplane/Examples/Label_Propagation/Label_Propagation_op_Correctness.thy"
OLD_COMMIT = "cbc1e18"  # folder move commit: original layout, Isar_Explore removed
OUT = sys.argv[1] if len(sys.argv) > 1 else "/tmp/lp_split"

# partition over the OLD file (validated by lp-split-deps.py, 0 violations)
PARTITION = {
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

CMD_RE = re.compile(
    r"^(lemma|theorem|corollary|definition|abbreviation|fun|function|primrec|"
    r"inductive|corec|partial_function|named_theorems|lemmas|method|locale|"
    r"termination|declare)\b")
NAME_RE = re.compile(
    r"^(?:lemma|theorem|corollary|definition|abbreviation|fun|function|primrec|"
    r"inductive|corec|partial_function|named_theorems|lemmas|method|locale)\s+"
    r"(?:fixes\b)?\s*\"?([A-Za-z0-9_']+)")


def commands(lines):
    """Return list of (name_or_None, kind, start, end) 1-based inclusive."""
    cmds = []
    for i, l in enumerate(lines, 1):
        if CMD_RE.match(l):
            m = NAME_RE.match(l)
            name = m.group(1) if m else None
            if name in (None, "fixes", "assumes", "shows") and i < len(lines):
                m2 = re.match(r"\s*\"?([A-Za-z0-9_']+)", lines[i])
                name = m2.group(1) if m2 else None
            cmds.append([name, l.split()[0], i, None])
    for k in range(len(cmds)):
        cmds[k][3] = cmds[k + 1][2] - 1 if k + 1 < len(cmds) else len(lines)
    return cmds


def region_of(line):
    best, best_size = None, None
    for name, ranges in PARTITION.items():
        for (a, b) in ranges:
            if a <= line <= b:
                size = b - a
                if best_size is None or size < best_size:
                    best, best_size = name, size
    return best or "UNASSIGNED"


OVERRIDES = {
    # stragglers whose old positions fell into overlapping PhaseA ranges
    "ocaps_1_label_prop_input1_step_state_empty": "Input1",
    "label_prop_collected_edge_payloads_image_eq": "Loop",
    "dataplane_tracker_inv_buffer_balance_aux": "Dataplane_Inv",
    "label_prop_edge_batch_all_vertices": "Labels",
    "label_prop_label_batch_all_vertices": "Labels",
    "label_prop_edge_batch_cc_of_all_edges": "Labels",
    "label_prop_covered_inv": "Labels",
    "min_label_record_update_le": "Labels",
}


def main():
    old = subprocess.run(["git", "show", f"{OLD_COMMIT}:{CUR}"],
                         capture_output=True, text=True, cwd=REPO).stdout.splitlines()
    cur = open(f"{REPO}/{CUR}").read().splitlines()

    # name -> target from OLD file. keep first occurrence.
    target = {}
    firstline_pos = {}  # exact first-line text -> old line (for anonymous cmds)
    for name, kind, s, e in commands(old):
        if name and name not in target:
            target[name] = region_of(s)
        firstline_pos.setdefault(old[s - 1], s)
    target.update(OVERRIDES)

    # walk current file
    main_start = next(i for i, l in enumerate(cur, 1)
                      if l.startswith("lemma label_propagation_correctness"))
    begin_line = next(i for i, l in enumerate(cur, 1) if l.strip() == "begin")

    blocks = {k: [] for k in PARTITION if k not in ("PhaseA", "Main")}
    unassigned = []
    cur_cmds = [c for c in commands(cur)
                if begin_line < c[2] < main_start]
    prev_end = begin_line
    for name, kind, s, e in cur_cmds:
        if kind in ("declare", "termination"):
            # anonymous: map by exact first-line text in the old file
            pos = firstline_pos.get(cur[s - 1])
            tgt = region_of(pos) if pos else "UNASSIGNED"
        else:
            tgt = target.get(name, "UNASSIGNED")
        if tgt in ("PhaseA", "Main", "UNASSIGNED", None):
            unassigned.append((name, kind, s, tgt))
            tgt = "Input1"  # safe default: everything imports Input1's ancestors
        # attach preceding comment/section lines (between prev command end and s)
        text = cur[s - 1:min(e, main_start - 1)]
        blocks[tgt].append("\n".join(text))
        prev_end = e

    import os
    os.makedirs(OUT, exist_ok=True)
    for tgt, chunks in blocks.items():
        with open(f"{OUT}/{tgt}.body", "w") as f:
            f.write("\n\n".join(chunks) + "\n")
        print(f"{tgt:14} {sum(c.count(chr(10)) + 1 for c in chunks):6} lines,"
              f" {len(chunks):4} commands")
    print(f"prerequisite region: {begin_line + 1}..{main_start - 1}")
    print(f"unassigned ({len(unassigned)}):")
    for u in unassigned[:20]:
        print("   ", u)


if __name__ == "__main__":
    main()
