# Plan: split Label_Propagation_op_Correctness.thy for parallel checking

Goal: `Label_Propagation_op_Correctness.thy` is 19,616 lines and checks sequentially.
The main lemma `label_propagation_correctness` starts at line **10573** and its proof runs
to ~19415 (~8.8k lines); the final `Correctness` section (19416–19616) derives the
consequences. Everything before 10573 (~10.5k lines) is prerequisite material that can be
distributed over multiple theory files so Isabelle/PIDE checks them **in parallel**.

Status: PLAN ONLY — no moves before user approval. Line numbers refer to the file as of
2026-07-07 (branch `dataplane`, after commit 8d6133f).

## Current structure (line map of the prerequisite region)

| Lines | Content | Key names |
|---|---|---|
| 1–40 | header, imports, `declare` block (simp del / if_cong / cin.rep_eq) | |
| 41–94 | 4 small intro lemmas | `input_ocaps_inv_label_prop_label_record_updateI`, `propagated_ifrontier_exit_scopeI`, `dataplane_tracker_inv_channel_*` |
| 95–523 | loop_op/comp_op Tau-simulation | `loop_move_all_data`, `loop_label_prop_input1` |
| 524–761 | `CONSUMES` abbrev + `label_prop_input1_loop_updates` def + projection lemmas | |
| 762–2031 | input-1 batch facts: frame facts, member/non-empty destructors, label minima, labels_inv/stable preservation | `label_prop_input1_step_batch_*`, `min_label_*`, `labels_inv_*`, `labels_stable_*` |
| 2032–2486 | measure decrease | `labels_measure_*`, `sum_list_strict_mono_ex1`, `label_prop_input1_loop_updates_sum_measure_decrease_if_label_output_nonempty` (2419) |
| 2487–2611 | Tau-simulation for input1 loop updates | `loop_move_all_data_label_prop_input1[_updates]` |
| 2612–3079 | frame / produced-progress / operational normal forms for `label_prop_input1_loop_updates` | `ocaps_*`, `*_os2`, `*_label_batched` |
| 3080–3418 | dataplane invariant transfer | `dataplane_tracker_inv_outpu_then_fold_consumes`, `…_produces_drop*` |
| 3419–3473 | `op_state_base` def + simp lemmas (used ~200× incl. main proof) | |
| 3474–5045 | capability bookkeeping + dataplane preservation for input-1/input-0 batches and one-step loop update; extension, raw-summary, msgs_inv | `dataplane_tracker_inv_label_prop_input[01]_*`, `label_prop_input1_loop_updates_preserves_dataplane_tracker_inv[_corrected]`, `…_msgs_invI` |
| 5046–5283 | `loop_updates` **function + termination** (uses measure lemma 2419), `loop_updates_intsum_corrected`, `loop_updates_cbufs_cleared`, `loop_updates_msgs_invI` | |
| 5284–5490 | operational simulation for `loop_updates` | `step_tau_pow_loop_updates[_alt]`, `loop_op_label_propagation_op_increment_op` |
| 5491–7455 | frame & produced-progress facts for `loop_updates` (~2000 lines); embeds generic stream/ccs/myprod lemmas (6714–7070) | `*_fst_snd_loop_updates*`, `set_icoll_*`, `ccs_*`, `myprod_le_*`, `label_prop_collected_edge_payloads_*`, `loop_updates_extension` |
| 7456–7589 | dataplane invariant preservation for `loop_updates` | `loop_updates_preserves_dataplane_tracker_inv` |
| 7590–8113 | progress comparison | `loop_updates_final_dataplane_tracker_inv_for_progress`, `CM_equiv_*`, `extract_prog_*`, `dataplane_buffer_consu_produ_balance`, `buff_sim_aux` |
| 8114–9180 | `wf_label_prop_updates` simp set + mono lemmas, `label_prop_upd_inv_loop_updatesI`, `labels_inv_loop_updates_allI`, edge/label-batch cc_of lemmas, output1-shift lemmas, `exit_scope_ifrontier_L1T0_le_L1T1_empty_loop` | |
| 9181–10572 | `label_prop_covered_inv` def + preservation through batches / input1 loop updates / `loop_updates` | `label_prop_covered_inv_*`, `violated_edge_*`, `min_label_edge_record_update_*` |
| 10573–19415 | **main lemma** `label_propagation_correctness` | stays |
| 19416–19616 | final `Correctness` section | stays |

Verified cross-cluster independence (grep probes):
- labels region (8114–9180) does NOT use progress lemmas (7590–8113);
- dataplane transfer (3080–3418) does NOT use input1-loop-updates frame facts (2612–3079);
- covered region (9181–10572) uses labels-region lemmas (`wf_label_prop_updates_*_step_stateI`) → Covered must import Labels;
- progress region uses `loop_updates_preserves_dataplane_tracker_inv` (7642) → Progress imports Dataplane_Loop;
- simulation base (95–523) uses NO input1 batch facts — only Extras-level material;
- dataplane region does NOT use measure/termination lemmas.

## Phase A — relocate generic lemmas to existing files

These lemmas don't mention label-prop-specific notions and already "have a home".
Lemmas move **verbatim, keeping their `[simp]`/`[cong]` attributes** (user decision):
insert at the new place, delete at the old place. If a newly-global simp breaks another
consumer of the target file (e.g. `Batch_op_Correctness`), we fix that consumer as part
of the same batch.

| Target file | Lemmas (current lines) |
|---|---|
| `ListUtils.thy` | `sum_list_strict_mono_ex1` (2188), `fold_min_Min` (8613), `fold_min_le_base` (9945), `fold_min_le_mem` (9950), `map_filter_append` (7805) |
| `MyMisc.thy` | `isl_projl_eq` (9266), `Field_Un_converse` (6842), `lfinite_lfilter_mono` (6733) |
| `MyProduct_Instances.thy` | `myprod_le_iff_myfst_le_if_mysnd_zero` (6872), `myfst_le_if_myprod_le_mysnd_zero` (6882), `myprod_le_if_myfst_le_mysnd_zero` (6892) |
| `ZmsetUtils.thy` | `zmset_filter_eq_if_c_pts_change_multiplicities_eq` (7647) |
| `Examples/Label_Propagation/Wcc.thy` (after B-pre move) | `ccs_eq_if_undirected_Field` (6847), `ccs_eq_if_undirected` (6856), `ccs_Un_symmetric_edge_image` (6865), `neighbors_reachable` (8603), `reachable_subset` (8608) |
| `Timely_Operator_State.thy` | `ocaps_drop_caps_port_disjoint` (9164), `ocaps_release_caps_empty_inputs` (2655), `produces_Nil` (7661) |
| `Correctness/General.thy` | `op_state_base` def + its `[simp]` lemmas (3419–3473, minus `op_state_base_CONSUMES`), `cap_times_filter_single_port_subset` (3476), `input_ocaps_inv_empty_inputsI` (5202), `dataplane_tracker_inv_channel_ifrontierD` (67), `dataplane_tracker_inv_channel_propagated_exit_scopeI` (75) |
| `Correctness/Consumes.thy` | `CONSUMES` abbrev (528), `CONSUMES_CONSUMES` (530), `op_state_base_CONSUMES` (3458), `input_ocaps_inv_CONSUMES` (3555), `ocaps_CONSUMES_other_port` (3561) |
| `Correctness/Produces.thy` | `produced_oputs_caps_from_produs` (3489), `produced_oputs_produs_zmset` (3496) |
| `Timely_Progress.thy` (defines `CM_equiv`) or `Correctness/Progress.thy` | `CM_equiv_empty_filter_notin` (7666), `CM_equiv_trans` (7671), `CM_equiv_append` (7740), `extract_prog_two_12` (7655), `filter_extract_progress_outside` (7771), `filter_extract_progress_Trg` (8024), `filter_extract_progress_Src` (8063), `extract_prog_three_fold` (8093) |
| `Correctness/Timely_Collections.thy` (defines `icoll`) | `set_icoll_llist_of` (6714), `set_icoll_llist_of_map_Data_pair` (6721), `set_icoll_lshift` (6727), `set_icoll_lsetI` (6746), `ts_lsetE` (6760), `ts_lsetI` (6773), `ts_ldropnD` (6782), `icoll_empty_if_no_data_le` (6795), `set_icoll_ltaken_ldropn` (6803), `set_icoll_ltaken_if_no_ldropn_data_le` (6813), `timely_input_stream_ldropn_no_data_le_if_not_frontier_less_equal` (6823) |
| `Propagation_Properties.thy` | `propagated_ifrontier_exit_scopeI` (48), `frontier_less_equal_pluss_le` (8998), `frontier_less_equal_exit_scope_myfst_le` (9658) |
| `Examples/Label_Propagation/Label_Propagation_op.thy` | `min_label_le_label` (9178), `min_label_mono_time` (787), `all_edges_sym` (1592), `finite_all_vertices` (2085), `finite_edge_vertices_all_edges` (2089), `all_vertices_add_caps` (8551), `wf_label_prop_updates_*` pure record-update simps (8114–8225, the `[simp]` frame lemmas + `_cong`, `_subset`, `_Un`, `_os_mono`), `label_prop_edge_batch_in_timestamps` (8539), `label_prop_label_batch_in_timestamps` (8545) |
| `Examples/Label_Propagation/Label_Propagation_op_Correctness_Extras.thy` | `exit_scope_ifrontier_L1T0_le_L1T1_empty_loop` (9002) — needs the raw_summary path-weight table |

Risks / mitigations for Phase A:
- Widely-imported targets (`Timely_Operator_State`, `Correctness/*`, `Label_Propagation_op`)
  are also imported by `Batch_op_Correctness.thy` (260 KB) and others. Since attributes
  are kept, a newly-global simp may break/slow those consumers → after each batch, wait
  for the checker (~5 min), inspect diagnostics of the affected downstream files, and fix.
- Proofs were developed under this file's header declares (`if_cong[cong]`,
  `cin.rep_eq` flip, several `simp del`). A moved proof may need small `supply`/`using`
  fixes in its new home. Fix case-by-case.
- Check for name clashes in the target file before each move.

## Phase B-pre — new folder `dataplane/Examples/Label_Propagation/`

Everything strictly about label-propagation correctness moves into a new folder, which
also removes the need for any name prefix on the new files. Done as the **first execution
step** (before Phase 0/A), since it causes one unavoidable full recheck and all later
work then happens in the final location.

Files moved there (`git mv`, keeping their names):
- `Label_Propagation_op.thy`
- `Label_Propagation_op_Correctness_Extras.thy`
- `Label_Propagation_op_Correctness.thy`
- `Wcc.thy` (recommended: its only importer is `Label_Propagation_op.thy`, and it defines
  the label-propagation spec notions `labels_inv`/`labels_stable`/`labels_measure`/`cc_of`;
  also disambiguates from the unrelated `dataplane/Wcc.thy`) — user may veto, then imports
  use `"../Wcc"` instead.

Nothing else in the repo imports these three files (verified by grep), so import-path
fixes are confined to the moved files themselves:
- `Label_Propagation_op.thy`: `Wcc` stays plain (if moved) or becomes `"../Wcc"`;
  session-qualified `Dataplane.*` imports unchanged.
- `…_Extras.thy`: `Ooo_Input_op`/`Increment_op`/`Set_op` → `"../Ooo_Input_op"` etc.;
  `"../Correctness/General"` → `"../../Correctness/General"`.
- `…_Correctness.thy`: same pattern; `"../../Isar_Explore"` → `"../../../Isar_Explore"`;
  `"HOL-ex.Sketch_and_Explore"` and `Dataplane.*` unchanged.

## Phase B — new theory files (5 topic files)

All in `dataplane/Examples/Label_Propagation/`, plain names (the folder provides the
context): `Input1.thy`, `Input0.thy`, `Loop.thy`, `Dataplane_Inv.thy`, `Labels.thy`.
(`Dataplane_Inv` rather than `Dataplane` to avoid clashing with the session name.)
Each file is about one independent topic. The header `declare` block (current lines
28–34) is **appended to `Label_Propagation_op_Correctness_Extras.thy`** (already imported
by everything here; theory-level `declare` is inherited by importers), so no extra "Base"
file is needed.
The four intro lemmas at 41–94 go with their topics (two `dataplane_tracker_inv_channel_*`
→ Phase A / `Dataplane_Inv`; `input_ocaps_inv_label_prop_label_record_updateI` →
`Input1`; `propagated_ifrontier_exit_scopeI` → Phase A).

```
   Label_Propagation_op, Correctness/*, …_Extras(+declares)   (existing)
            │                          │
      Input1              Input0        (parallel roots)
            │                          │
      Loop                     │
            │      \                   │
   Dataplane_Inv  Labels   │   (parallel; both also import Input0)
            \             │           /
        Label_Propagation_op_Correctness   (main lemma 10573–end)
```

### `Input1.thy` — processing data arriving on input 1  (~2400 lines)
Imports: `Label_Propagation_op_Correctness_Extras` (+ the op/Correctness imports).
- 524–761: `CONSUMES` leftovers, **`label_prop_input1_loop_updates` definition** + projection lemmas
- 762–2031: input-1 batch facts — frame facts, batch member/non-empty destructors
  (`label_prop_input1_step_batch_*`, `label_prop_label/neighbor_batch_*`), label minima
  (`min_label_*`), `labels_inv`/`labels_stable`/`label_prop_upd_inv`/`wf_label_prop_updates`
  preservation for `label_prop_input1_step_state` and `label_prop_input1_batched`
- 2032–2486: measure decrease (`labels_measure_*`,
  `label_prop_input1_loop_updates_sum_measure_decrease_if_label_output_nonempty`)
  and `labels_inv`/`labels_stable` for `label_prop_input1_loop_updates`
- 2612–3079: frame, produced-progress, and operational normal forms for
  `label_prop_input1_loop_updates` (`ocaps_*`, `*_os2`, `*_label_batched`, `produ_*`)
- 41–47: `input_ocaps_inv_label_prop_label_record_updateI`

### `Input0.thy` — processing data arriving on input 0 (graph edges)  (~550 lines)
Imports: `Label_Propagation_op_Correctness_Extras` (+ the op/Correctness imports).
Sibling of Input1 — no dependency between them.
- 6451–6713: `label_prop_input0_step_state` / `label_prop_input0_batched` facts
  (`input_0_fst_label_prop_input0_batched_empty`, `filter_*_out_neq`,
  `outpu_0_fst_label_prop_input0_batched`, `all_edges_eq_graph_entries`,
  `all_edges_label_prop_input0_step_state_eq`, `all_edges_fst_label_prop_input0_batched_*`)
- 8227–8263: `wf_label_prop_updates_label_prop_input0_step_state_monoI`,
  `wf_label_prop_updates_fst_label_prop_input0_batched_monoI`
- 8447–8462: `labels_inv_fst_label_prop_input0_batched_input_allI`
- 8762–8997: `wf_label_prop_updates_label_prop_input0_step_state_output1_shiftI`,
  `wf_label_prop_updates_fst_label_prop_input0_batched_output1_shiftI`

### `Loop.thy` — the `loop_updates` recursion and loop-level simulation  (~2350 lines)
Imports: `Input1` (termination needs the measure lemma; msgs_inv chain).
- 95–523: `loop_move_all_data`, `loop_label_prop_input1` (loop_op/comp_op Tau simulation)
- 2487–2611: `loop_move_all_data_label_prop_input1[_updates]`
- 5046–5283: **`loop_updates` function + termination**, `loop_updates.simps[simp del]`,
  `loop_updates_intsum_corrected`, `loop_updates_cbufs_cleared`, `loop_updates_msgs_invI`
- 5284–5490: `step_tau_pow_loop_updates[_alt]`, `loop_op_label_propagation_op_increment_op`
- 5491–7455 (minus 6451–6713 → Input0, minus Phase-A generics): frame & produced-progress
  facts for `loop_updates` (`*_fst_snd_loop_updates*`, `ocaps_*`, `outpu_*`, `input_*`,
  `initia_*`, `en2_*`, `all_edges_*`, `timestamps_*`), `input_ocaps_inv_snd_snd_loop_updates2`,
  `loop_updates_extension`, `label_prop_collected_edge_payloads_*`

### `Dataplane_Inv.thy` — dataplane tracker invariant & progress comparison  (~2450 lines)
Imports: `Loop`, `Input0`.
- 67–94: `dataplane_tracker_inv_channel_*` intro lemmas (if not relocated in Phase A)
- 3080–3418: dataplane invariant transfer (`dataplane_tracker_inv_outpu_then_fold_consumes`,
  `…_produces_drops_dropcaps_shape`, `…_produces_drop`)
- 3474–3752: capability bookkeeping for input-1 batches (`label_prop_input1_step_batch_caps`,
  `input_ocaps_inv_*`, `dataplane_tracker_inv_label_prop_input1_step_state/_batched`)
- 3753–3928: same for input-0 batches (`label_prop_input0_step_batch_caps`,
  `dataplane_tracker_inv_label_prop_input0_step_state/_batched`)
- 3929–5045: one-step + full preservation for `label_prop_input1_loop_updates`
  (`…_preserves_dataplane_tracker_inv[_corrected]`, `…_corrected_os`, extension &
  raw-summary lemmas, `input_ocaps_inv_label_prop_input1_loop_updates_*`,
  `label_prop_upd_inv_label_prop_input1_loop_updatesI`, `…_msgs_invI`)
- 7456–7589: `loop_updates_preserves_dataplane_tracker_inv`
- 7590–8113: progress comparison (`loop_updates_final_dataplane_tracker_inv_for_progress`,
  `CM_equiv`/`extract_prog` leftovers not relocated in Phase A,
  `dataplane_buffer_consu_produ_balance`, `dataplane_tracker_inv_buffer_balance`, `buff_sim_aux`)

### `Labels.thy` — label invariants & the covered invariant  (~2250 lines)
Imports: `Loop`, `Input0`.  Sibling of Dataplane — verified no
dependency on the dataplane-preservation lemmas.
- 8114–8226: `wf_label_prop_updates` record-update simp set (unless relocated to
  `Label_Propagation_op` in Phase A), `_cong`, `_subset`, `_Un`, `_os_mono`
- 8264–8446: `wf_label_prop_updates` mono lemmas for input1/loop,
  `label_prop_upd_inv_loop_updatesI`
- 8463–9180: `labels_inv_loop_updates_allI`, edge/label-batch `cc_of` lemmas,
  `label_prop_edge_batch_all_vertices`, `exit_scope_ifrontier_L1T0_le_L1T1_empty_loop`
  (unless moved to Extras in Phase A)
- 9181–10572: **`label_prop_covered_inv` definition** + all preservation lemmas
  (`violated_edge_*`, `min_label_edge_record_update_*`, `label_prop_covered_inv_*`
  through batches, `label_prop_input1_loop_updates`, and `loop_updates`)

### Shrunk `Label_Propagation_op_Correctness.thy`  (~9100 lines)
Imports: `Dataplane_Inv`, `Labels` (+ `Sketch_and_Explore`, `Isar_Explore`).
- 10573–19415: `label_propagation_correctness` (untouched)
- 19416–19616: final `Correctness` section (untouched)

Notes:
- Hard dependency edges verified by grep: measure lemma (2419) → `loop_updates`
  termination; `wf_label_prop_updates_*_step_stateI` (labels region) → covered proofs;
  `loop_updates_preserves_dataplane_tracker_inv` (7456) → progress lemma 7642.
- Whether `Loop` needs `Input0` is decided by the Phase-0 scan (if its
  frame-facts region references `label_prop_input0_*`, add the import — Input0 is a root,
  so no cycle risk).
- Parallelism: Input1 ∥ Input0, then Dataplane ∥ Labels; critical path
  Input1 → Loop → Labels → main. The main file remains the wall-clock bottleneck
  (~46% of today's line count); a possible **later** phase is factoring the big `have`
  blocks of the main proof into standalone lemmas — out of scope for this split.

## Phase 0 — RESULTS (scan done 2026-07-07, ai/lp-split-deps.py, 0 violations)

The scripted scan validated a **refined** partition (line ranges in ai/lp-split-deps.py
are authoritative; sizes: Main 9044, Input1 4021, Loop 2434, Labels 1667, PhaseA 1193,
Dataplane_Inv 665, Input0 552):
- **Input1 absorbs** the dataplane-transfer lemmas (3080–3417), input-1 caps bookkeeping
  (3503–3752) and the one-step `label_prop_input1_loop_updates` preservation block
  (3928–5045, incl. `…_msgs_invI`, `…_intsum_corrected`, `…_extension`,
  `input_ocaps_inv_…_os2`, `label_prop_upd_inv_…I`, `labels_inv_…_allI`) — all needed
  by `Loop`'s `loop_updates_*` lemmas.
- **Dataplane_Inv shrinks** to: intro lemmas 47–92, input-0 batch preservation
  (3753–3927), `loop_updates` preservation + progress comparison (7455–8112).
- **Phase A additionally** takes the `CONSUMES` field-projection simps (523–578) →
  `Correctness/Consumes.thy` (generic) / `Label_Propagation_op.thy` (label-prop fields);
  the `wf_label_prop_updates` record-update simp set (8113–8225) MUST go to
  `Label_Propagation_op.thy` (both Input0 and Labels need it).
- **Name clash**: `all_vertices_add_caps` already exists in `Label_Propagation_op.thy`
  → delete from the big file (verify duplicate) instead of moving.

## Phase 0 — scripted dependency map (before any move)

Before the first move, generate a per-lemma dependency report:
1. Extract all top-level command names + line spans (regex on `^lemma|^definition|…`).
2. For each lemma, scan its text for occurrences of earlier-defined names → adjacency list.
3. Validate the partition above: every edge must go from an earlier/imported file to a
   later one. Reassign stragglers (a lemma placed by section but used across clusters gets
   promoted to the earliest file that needs it).
4. Check name clashes for every Phase-A relocation target.
Store the script + report under `ai/` (e.g. `ai/lp-split-deps.py`, `ai/lp-split-deps.txt`).

## Execution protocol (incremental, keep-green)

- One move-batch at a time; after each batch everything must still check. User confirms
  in jEdit before the next batch (per `ai/pair-proving.md`).
- Lemmas move **verbatim** (attributes like `[simp]` included): insert at the new place
  first, then delete at the old place.
- After each batch: **wait ~5 minutes** for the checker to make progress (background
  sleep / `get_processing_status` polling), then `get_diagnostics` on the touched files
  and every affected downstream file, and **fix whatever broke** before moving on.
- Edit `.thy` files only via `mcp__isabelle__write_file`; new files via MCP save/write.
  Cutting a region from the big file invalidates everything after the cut — that recheck
  is unavoidable per peel; peels are ordered top-of-file-first so each peel's content is
  itself already checked in its new location before the main file is cut.
- Order:
  1. Phase B-pre: create `Examples/Label_Propagation/`, `git mv` the three (four with
     Wcc) files, fix their import paths, wait ~5 min, fix breakage; commit.
  2. Phase 0 (script, no edits).
  3. Phase A in batches per target file, leaf-most targets first (ListUtils, MyMisc,
     MyProduct_Instances, ZmsetUtils, Wcc), then Timely_*/Correctness/*, then
     Label_Propagation_op / Extras. After each batch: wait ~5 min, check target file +
     big file + downstream consumers (`Batch_op_Correctness` etc.), fix breakage.
  4. Append the header `declare` block (lines 28–34) to
     `Label_Propagation_op_Correctness_Extras.thy`.
  5. Phase B peels in dependency order: `Input1`, `Input0`,
     `Loop`, `Dataplane_Inv`, `Labels`. Each peel: create the new
     file (with imports), wait for it to check, then remove the region(s) from the main
     file and add the import, wait ~5 min, fix breakage.
  6. Final cleanup: prune now-unused imports of the main file; commit.
- The in-progress sorries inside the main proof (see memory
  `wcc-set-spec-op-subgoal-continuation`, ~line 14802) are untouched: the split never
  edits the region ≥ 10573 except the import list.
