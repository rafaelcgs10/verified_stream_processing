# Tasks

The general task is to help prove `sorry`s/`oops` in this Isabelle/HOL project.

## Task 1: Sketch a proof for the final part of `dataplane_tracker_inv_produces_drops`

**File:** `Correctness/Produces.thy`

We are almost done with the lemma `dataplane_tracker_inv_produces_drops`. The main remaining piece is the second-to-last conjunction of `dataplane_tracker_inv`.

### Context

- We are proving that `dataplane_tracker_inv` is preserved when an operator produces data and drops capabilities. We have already proved this invariant for the case when an operator consumes data (see `Correctness/Consumes.thy`) and when an operator reports its progress (see `Correctness/Progress.thy`).

- The second-to-last conjunction, `extract_prog_changes_above_impl_inv`, states that operators can report their progress and cause changes of multiplicities independently. The operator state of operator `nid` is updated in two ways: fields related to what was produced, and fields related to what was dropped. Our hope is that production and dropping of capabilities only require that the operator holds capabilities for the relevant timestamps. Hopefully there are no further requirements, but this should be verified.

- When proving `extract_prog_changes_above_impl_inv`, `auto` at line 569 of `Produces.thy` produces two main subgoals. Recall the definition quantifies over `nid` and `xs` with `nid ∉ set xs`:
  1. **Subgoal 1** (line 570, `for nid not in xs`): The quantified operator is the updated operator `nid` itself, so `nid ∉ set xs` -- the updates are not yet reported in the multiplicities. This has been proved by induction (lines 570--723).
  2. **Subgoal 2** (line 724, `for nid' not in xs`): The quantified operator is some other `nid'` (with `nid' ∉ set xs`). Whether the updated operator `nid` is in `xs` or not is unknown, so the proof splits on `cases "nid ∈ set xs"` at line 728. The case where `nid ∈ set xs` (meaning `nid`'s updates, including drops, are part of the change of multiplicities) is where the proof is incomplete (`oops` at line 730). **This is our main task.**

### The `produ_consu_inter_supported` invariant

The invariant `produ_consu_inter_supported` (defined in `General.thy`, line 78) is critical for proving `extract_prog_changes_above_impl_inv`. It describes how the buffers (`consu`, `inter`, `produ`) relate to each other and to the control plane. Its three conjuncts state:

1. **produ supported:** Every entry `(p, t, m)` in `produ (os nid)` is supported by either a positive pointstamp count at `Loc nid (Src p)` in the control plane (`c_pts c`), or by a matching positive entry in `inter (os nid)`.
2. **consu supported:** Every entry `(p, t, m)` in `consu (os nid)` is supported by a positive count at `Loc nid (Trg p)` in the control plane plus the zmultiset of timestamps from productions by upstream operators connected to `(nid, p)`.
3. **inter supported:** Every entry `(p, t, m)` in `inter (os nid)` is supported by either a pointstamp `t' <= t` at `Loc nid (Src p)`, or by a consumption entry in `consu (os nid)` combined with a summary path.

### Intuition for completing Task 1

- The main goal is to show `frontier_less_equal` at the proof state. This requires exhibiting a timestamp in the control plane, after the change of multiplicities (including those from operator `nid`), that is less than or equal to `t`. The key fact about `t` is that it comes from the unreported progress of some operator `nid'`. The multiplicities from `nid` include `drops`, which may entirely remove `t` at `nid`'s locations.

- The intuition for why the lemma should hold: thanks to `produ_consu_inter_supported`, we can find a location *different from* `nid` that still has timestamp `t` (or one below it) after the change of multiplicities.

### Open question

`produ_consu_inter_supported` establishes that `nid'`'s buffer entries are supported by `c_pts c` (the pre-change configuration). However, after `change_multiplicities` includes `nid`'s `extract_progress` -- which contains drops as negative multiplicity entries -- the pointstamps at `Loc nid (Src p)` may decrease. The core question is: **can we always find support at a location other than `nid`'s source ports, or do we need an additional argument?** This is the main point to be resolved.

### Proof sketch (work in progress)

#### Key structural facts

1. Since `nid' ∉ set xs` and `nid ∈ set xs`, we have `nid' ≠ nid`. Therefore `extract_progress nid'` is unchanged by the update to `os(nid := ...)` -- the entries `(l, t, m)` we need to show `frontier_less_equal` for are the same as in the old invariant.

2. The lemma `change_multiplicities_extract_prog_updates` (General.thy:1031) decomposes the updated change of multiplicities: `change_multiplicities su (extract_prog xs nt os_updated) c` equals `change_multiplicities su (extract_prog xs nt os @ produ_additions @ drop_entries) c`. Here:
   - `produ_additions` are positive multiplicity entries at downstream `Trg` ports (from `produs`).
   - `drop_entries` are entries `(Loc nid (Src p), t, -1)` at `nid`'s `Src` ports (from `drops`).

3. `take_step (CM l t m)` only modifies `c_pts` at location `l` by adding `m` to the count of `t`. It does not propagate. So the drops only affect `c_pts` at `Loc nid (Src p)`, and the productions only affect `c_pts` at downstream `Trg` ports. All other locations' `c_pts` are unchanged between `c_old` and `c_new`.

#### Antichain ordering

The empty antichain is the *top* element. Removing pointstamps (negative multiplicities) makes frontiers *larger* in the ordering, which is *bad* for `frontier_less_equal` -- fewer elements means it's harder to find a witness `t' ≤ t`.

#### Key lemmas

- **`frontier_less_equal_ifrontierI`** (Timely_Infrastructure.thy:1840): Given `frontier_less_equal (frontier (c_pts c l)) t` and a path from `l` to `l'` with weight `t'`, concludes `frontier_less_equal (ifrontier su (-+-) c l') (t + t')`. This lets us lift pointstamp support at a specific location to `frontier_less_equal` of the ifrontier.

- **`frontier_less_equal_ifrontierE`** (Timely_Infrastructure.thy:1892): Decomposes `frontier_less_equal (ifrontier ...) t` into a witness location `l`, path weight `s`, and base timestamp `t'` such that `frontier_less_equal (frontier (c_pts c l)) t'` and `t = t' + s`.

#### Proposed approach

For each entry `(l, t, m)` from `extract_progress nid'`, use `produ_consu_inter_supported` to find a supporting pointstamp at a location belonging to `nid'` (not `nid`). Since `nid' ≠ nid`, the `c_pts` at `nid'`'s locations are unaffected by the drops (fact 3 above). Then use `frontier_less_equal_ifrontierI` to lift this support to `frontier_less_equal (ifrontier su (+) c_new l) t`.

#### Remaining question

The support from `produ_consu_inter_supported` is in terms of `c_pts c` (the base configuration, before any `change_multiplicities`). The goal requires `frontier_less_equal` with respect to `c_new` (after `change_multiplicities` with the full `extract_prog xs`). We need to verify that the supporting pointstamps at `nid'`'s locations survive the full `change_multiplicities` -- not just the additional drop/produ entries, but also the entries from all other operators in `xs`.

#### Current proof state (line 755 of Produces.thy)

After unfolding and decomposition, the goal at line 755 is:

```
frontier_less_equal 
  (ifrontier (summ sg) (-+-) c_new (Loc nid' (Trg p'))) 
  (t' -+- s)
```

with key assumptions:
- `(p', t' -+- s, m) ∈ set (consu (os nid'))` -- a consumption entry of `nid'`
- `s ∈_A graph.path_weight (summ sg) (Loc nid (Src p)) (Loc nid' (Trg p'))` -- a path from `nid`'s Src to `nid'`'s Trg
- `ft ∈_A frontier (c_pts c (Loc nid (Src p)) + zmset(inter entries of nid for port p))` -- witness at `nid`'s Src port
- `ft ≤ t'`

The witness location `Loc nid (Src p)` is affected by drops. We need to find an alternative witness.

#### Backtracking via `produ_consu_inter_supported`

The three conjuncts of `produ_consu_inter_supported` form a backward chain through the graph:
- `consu (os n) (p, t, m)` → support at `Loc n (Trg p)` in `c_pts c` + upstream `produ`
- `produ (os n) (p, t, m)` → support at `Loc n (Src p)` in `c_pts c`, or by `inter (os n)`
- `inter (os n) (p, t, m)` → support at `Loc n (Src p)` for `t' ≤ t` in `c_pts c`, or by `consu (os n)` + summary

Starting from the consumption entry `(p', t' -+- s, m) ∈ set (consu (os nid'))`, this chain can be followed backwards:

1. From `consu (os nid')` → support at `Loc nid' (Trg p')` in `c_pts c` + upstream `produ`. The location `Loc nid' (Trg p')` is safe (not `Loc nid (Src _)`). If support comes from `c_pts c` directly, we're done.
2. If support comes from upstream `produ` of some `nid_up`: if `nid_up ≠ nid`, then `Loc nid_up (Src p_up)` is safe. Done.
3. If `nid_up = nid`, we reach `Loc nid (Src p_up)` — this is affected by drops. We continue via conjunct 1 → conjunct 3 (inter) → conjunct 2 (consu of `nid`) → support at `Loc nid (Trg p_c)` + upstream `produ`.
4. `Loc nid (Trg p_c)` is safe (drops only affect `Loc nid (Src _)`, not `Loc nid (Trg _)`). If support comes from `c_pts c` directly, we're done. Otherwise, upstream produ may route back to `Loc nid (Src _)`, and we recurse.

Each full cycle (Src → inter → consu → upstream produ → Src) traces a non-trivial path backwards in the dataflow graph. Since the graph has no zero-weight cycles, the chain must eventually terminate at `c_pts c` at a location that is NOT `Loc nid (Src _)`.

#### Proposed auxiliary lemma

```isabelle
lemma backtrack_to_non_Src_nid:
  assumes "produ_consu_inter_supported nt os c"
  and "dataflow_topology su (-+-)"
  and "graph_summar_nt su nt os"
  and "zcount (c_pts c (Loc nid (Src p))) t > 0 
       ∨ (∃ m' > 0. (p, t, m') ∈ set (inter (os nid)))"
  shows "∃ l t_base s_path. 
           (∀ p'. l ≠ Loc nid (Src p')) ∧
           zcount (c_pts c l) t_base > 0 ∧
           s_path ∈_A graph.path_weight su l (Loc nid (Src p)) ∧
           t_base -+- s_path ≤ t"
```

This says: any support at `Loc nid (Src p)` (direct or via inter) can be traced back to a location that is NOT one of `nid`'s `Src` ports. The proof would use induction on path length with the graph's acyclicity providing termination.

#### How the auxiliary lemma completes the proof

Given the proof state at line 755:
1. Apply `backtrack_to_non_Src_nid` to find `l`, `t_base`, `s_path` with `l ≠ Loc nid (Src _)`.
2. Compose `s_path` (from `l` to `Loc nid (Src p)`) with `s` (from `Loc nid (Src p)` to `Loc nid' (Trg p')`) to get a path from `l` to `Loc nid' (Trg p')`.
3. Since `l ≠ Loc nid (Src _)`, the count `zcount (c_pts c l) t_base > 0` is preserved in `c_new` (drops only affect `Loc nid (Src _)` ports; at other locations, `c_pts c_new l ≥ c_pts c l` since only non-negative changes are applied).
4. Use `frontier_less_equal_ifrontierI` with location `l`, timestamp `t_base`, and the composed path to conclude `frontier_less_equal (ifrontier su (-+-) c_new (Loc nid' (Trg p'))) (t_base -+- s_path -+- s)`.
5. Since `t_base -+- s_path ≤ t'` (from the auxiliary lemma and `ft ≤ t'`) and `t' -+- s` is the target, we need `t_base -+- s_path -+- s ≤ t' -+- s`, which follows from monotonicity of `-+-`.

#### Issues with the first attempt (`backtrack_consu_to_non_nid`, line 760)

The first attempt at the auxiliary lemma (line 760 of `Produces.thy`) used induction on a specific path from `Loc nid (Src p)` to `Loc nid' lp`. This approach fails because:

1. **Port jumping:** Conjunct 3 of `produ_consu_inter_supported` gives a consu entry `(p''', t''', _) ∈ consu (os nid)` with `intsum` summary from port `p'''` to port `p'`. But `p'''` might differ from the port `p''` on the induction path. The backward chain can jump to a different port than the one we're inducting over.

2. **Recursion requires `nid' = nid`:** When backtracking reaches `Loc nid (Src p_up)`, the chain goes through `inter → consu` of `nid` itself. To recurse, we need to apply the lemma with the starting operator being `nid`. But the lemma assumed `nid ≠ nid'`, preventing this recursive call.

#### Revised approach: lexicographic induction on `(t, S)`

Instead of inducting on a path, we use well-founded induction on the pair `(t, S)` with lexicographic ordering `{(x,y). x < y} <*lex*> finite_psubset`:

- **`t`** is the current timestamp. Each backward step through `inter → consu → upstream produ` may decrease `t` (when the intsum weight is positive).
- **`S :: 'p set`** is the set of Src ports of `nid` that we are still "allowed to visit" at timestamp `t`. When backtracking visits `Loc nid (Src p')` at the same timestamp `t`, we remove `p'` from `S` and recurse with `(t, S - {p'})`.

Well-foundedness: `wf_lex_prod[OF wf_less wf_finite_psubset]`.

Termination argument:
- If the backward step decreases `t` (intsum weight > 0): `(t', S') <_lex (t, S)` since `t' < t`.
- If `t` stays the same (intsum weight = 0): we visit a new Src port `p'`, so `S - {p'} ⊂ S`, giving `(t, S - {p'}) <_lex (t, S)`.
- If `t` stays the same and `p' ∉ S`: we've already visited this port at this timestamp, implying a zero-weight cycle — contradicting graph acyclicity.

**Key design decisions:**

1. The lemma should NOT assume `nid ≠ nid'`. The recursion needs to handle the case where the starting consu/inter entry is at `nid` itself (when backtracking from an upstream produ of `nid` reaches `consu (os nid)`).

2. `S` appears as a parameter in the lemma. When `nid' = nid` and `lp = Src p'`, we need `p' ∈ S` as an assumption (so that `S - {p'} ⊂ S`). When `nid' ≠ nid`, `S` is irrelevant.

3. The initial call uses `S = UNIV :: 'p set`, which is finite since `'p :: enum`.

4. The conclusion uses `is_Src (port l) ⟶ node l ≠ nid` (not `node l ≠ nid`), because only `Loc nid (Src _)` ports are affected by drops. `Loc nid (Trg _)` ports are safe.
