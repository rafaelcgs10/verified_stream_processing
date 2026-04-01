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
