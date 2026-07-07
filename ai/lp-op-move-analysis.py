#!/usr/bin/env python3
"""Which lemmas of Label_Propagation_op.thy can move into existing downstream files?

For every top-level lemma, compute which files reference it. A lemma may move to
Input0 iff all its users are in {Input0, Dataplane_Inv, Labels, main}; to Input1
iff users are in {Input1, Loop, Input0, Dataplane_Inv, Labels, main}. Internal
users (later lemmas in Label_Propagation_op itself) or users in Extras pin it.
Definitions never move. Read-only.
"""
import re

D = "dataplane/Examples/Label_Propagation"
LP = f"{D}/Label_Propagation_op.thy"
FILES = {
    "LP_op": LP,
    "Extras": f"{D}/Label_Propagation_op_Correctness_Extras.thy",
    "Input1": f"{D}/Input1.thy",
    "Input0": f"{D}/Input0.thy",
    "Loop": f"{D}/Loop.thy",
    "Dataplane_Inv": f"{D}/Dataplane_Inv.thy",
    "Labels": f"{D}/Labels.thy",
    "main": f"{D}/Label_Propagation_op_Correctness.thy",
}
OK_INPUT0 = {"Input0", "Dataplane_Inv", "Labels", "main"}
OK_INPUT1 = OK_INPUT0 | {"Input1", "Loop"}

CMD_RE = re.compile(r"^(lemma|lemmas|definition|abbreviation|fun|function|record)\b")
NAME_RE = re.compile(r"^(?:lemma|lemmas)\s+([A-Za-z0-9_']+)")

lp = open(LP).read().splitlines()
cmds = []
for i, l in enumerate(lp, 1):
    if CMD_RE.match(l):
        m = NAME_RE.match(l)
        cmds.append([m.group(1) if m else None, i, l.split()[0]])
for k in range(len(cmds)):
    cmds[k].append(cmds[k + 1][1] - 1 if k + 1 < len(cmds) else len(lp))

texts = {k: open(v).read() for k, v in FILES.items()}
word = lambda t: set(re.findall(r"[A-Za-z0-9_']+", t))
file_words = {k: word(t) for k, t in texts.items()}

results = {"Input0": [], "Input1": [], "pinned": []}
for name, s, kind, e in cmds:
    if not name or kind != "lemma":
        continue
    body = "\n".join(lp[s - 1:e])
    topic = None
    if "label_prop_input0" in body:
        topic = "Input0"
    elif "label_prop_input1" in body:
        topic = "Input1"
    if not topic:
        continue
    users = set()
    # internal users: occurrences in LP_op outside own span
    rest = "\n".join(lp[:s - 1] + lp[e:])
    if re.search(rf"\b{re.escape(name)}\b", rest):
        users.add("LP_op")
    for k in FILES:
        if k == "LP_op":
            continue
        if name in file_words[k]:
            users.add(k)
    ok = OK_INPUT0 if topic == "Input0" else OK_INPUT1
    if users <= ok:
        results[topic].append((s, e, name, sorted(users)))
    else:
        results["pinned"].append((s, e, name, topic, sorted(users)))

for tgt in ("Input0", "Input1"):
    tot = sum(e - s + 1 for s, e, *_ in results[tgt])
    print(f"=== movable to {tgt}: {len(results[tgt])} lemmas, ~{tot} lines")
    for s, e, name, users in results[tgt]:
        print(f"  {s:5}-{e:5} {name}  users={users}")
print(f"=== pinned: {len(results['pinned'])}")
for s, e, name, topic, users in results["pinned"]:
    print(f"  {s:5}-{e:5} {name} [{topic}] users={users}")
