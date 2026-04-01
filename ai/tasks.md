# Tasks

The general task is to help prove `sorry`s/`oops` in this Isabelle/HOL project.

## Task 1: `Help sketching a proof of the final part of dataplane_tracker_inv_produces_drops`

**File:** `Correctness/Produces.thy`

Note: this text still is a draft. We want to iterate over it to fill with more details, and polish the writing.

We are almost done with the lemma `dataplane_tracker_inv_produces_drops`, the main thing left is the second last conjunction in `dataplane_tracker_inv`.

**Context:**
- We are proving the invariant `dataplane_tracker_inv` for the case when an operator produces some data, and drop some capabilities. We are have proved this invariant for the case when the operator consumes some data (see `Correctness/Consumes.thy`) and when the operator reports its progress (see `Correctness/Progress.thy`).
- This second last conjunction (`extract_prog_changes_above_impl_inv`) defines how that the operators can report their progress, and cause change of multiplicities independently.
Notice that we have a few updates in the operator state of the operator `nid`: we update fields related to was produced, and we update things related to what was dropped. Our hope is that production and drop of capabilities only have as requirement that the operator has the capabilities for the timestamp that it is producing, and dropping. Hopefully, there are no more requirements, but this should be better discussed and checked. 
- When proving `extract_prog_changes_above_impl_inv` we get two main subgoals (see `auto` in line 569 in file `Correctness/Produces.thy`). The first one fixes the updates of the operator `nid` as not being reported yet, and it was already proved by induction; whereares the second subgoal has the updates of the operator `nid` as part of the change of multiplicities. This is our main task now.

***Intuition on how to complete task 1***
- The invariant `produ_consu_inter_supported` is critical for proving `extract_prog_changes_above_impl_inv` because it explain how the buffers (`consu`, `inter`, `produ`) are related to each other, and how they are related to the control plane.
- Our main goal here is to show the `frontier_less_equal` at the proof state. This basically asks to show the existence of some timestamp in the control plane, after the change of multiplicities (including the one from the operator `nid`), that is smaller or equal to `t`. The main thing we know about `t` is that it is the unreported progress of the operator `nid'`. The change of multiplicities in `nid` has the `drops`, which may completely remove `t` from there.
- The intuition on why this lemma should hold is that thanks to `produ_consu_inter_supported` we can find a different location than `nid` that has the timestamp `t` after the change of multiplicities. But this is not totally clear is the main point to be discussed if it is true or not.
