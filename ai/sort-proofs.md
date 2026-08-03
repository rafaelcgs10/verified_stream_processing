Your task is to improve the organization of the dataplane folder.
We need a good big plan for it:
First, make a sort of dependency tree of the folder.
The main two files that we want working in the end are the two
examples: Label_Propagation_op_Correctness.thy and Batch_op_Correctness.thy.
These are the two files that need to always check after any sorting of code.

I think the better strategy for the plan is to start from the more root files (e.g. files that are the base theory, and important by others). For example,
the files with the name starting with Timely_ prefix are things that
are related to the Timely Dataflow infrastructure formalization. These probable
should be even in a separated folder.
So it can be very nice to move things to separate folder if it makes the organization
more clean.

Another point to this organization is to have a things inside of files also organized.
So it is not only organization between files, but within the files themselves.
For that, you will group the lemmas and definitions by similarity (e.g. they are related).
Create isabelle sections with short text descriptions of the lemmas and definitions in the section.

There are two main goals for this dataplane folder sorting:
1. Improve overall organization, so things are in places that make sense.
2. Improve the parallelism of the isabelle checker by having things split into separate file that can be check in parallel. Overall, improving the dependency tree structure so things can be check faster.

So for now, I just want you to come up with a plan on how to organize the dataplane
folder. Study the dependencies of those two mentioned files, and make sure that
the sorting plan can keep things working.
I will review your plan and ask you to write it down here, so we
can keep track of the progress of the plan during its execution.


Important for the plan execution:
Move all lemmas at once, and use the MCP connection to check if the edit was successful.
Keep checking if things are still working after the move. In particular,
if those two files still check completely.

---

# The Sorting Plan (approved 2026-07-31)

## Verified dependency facts

- 57 .thy files, ~50K lines. LP-correctness closure: 49 files.
  Batch-correctness closure: 40 files. Shared: 38.
- Layering today: Lib roots (ListUtils, ZmsetUtils, CsetUtils, Locations,
  Zero_Cyc_Check, AntichainOrder, MyProduct_Instances, Numeral_Conversion,
  MyMisc, DataplaneUtils, Bots)
  -> Timely_Base / Timely_Operator_State (both re-import the same 9 base
  files + same 8 externals, a duplicated hub)
  -> Timely_Tree_Compile -> Timely_Propagation_Exec -> Timely_Progress
  -> {Timely_Builder_Op, Timely_Dataflow_Op, Timely_Ifrontier,
  Propagation_Properties, Timely_Stream}
  -> Correctness/General -> 8 sibling Correctness files (good fan-out)
  -> Examples. LP chain: Label_Propagation_op -> Extras -> Input1 ->
  {Input0, Loop} -> {Labels, Dataplane_Inv} -> LP_op_Correctness.
- Critical path bottleneck: Input1.thy (4,575 lines) imports the operator,
  all of Correctness/, and Extras; everything after it waits.
- Duplicate name: top-level Wcc.thy (dead) clashes with
  Examples/Label_Propagation/Wcc.thy (live).
- Unreachable from both examples (11): top-level Wcc.thy, Isar_Explore.thy
  (+ 3 .ML files), Examples/Scratch_Not_Labels_Stable.thy, and standalone
  examples Accumulator, Collatz, Branch_op, Concat_op, Tmap_op, Source_op,
  Ooo_Input_op_Correctness, Increment_op_Correctness.
- ROOT's Dataplane session declares no dataplane theories; checking is
  jEdit-driven via imports.

## Target folder layout

```
dataplane/
  Lib/            general-purpose libraries, no Timely deps
    ListUtils  CsetUtils  ZmsetUtils  DataplaneUtils  MyMisc
    MyProduct_Instances  Numeral_Conversion  Locations  Bots
    AntichainOrder  Zero_Cyc_Check  Operators_Utils  SimulationProofMethods
  Timely/         Timely Dataflow infrastructure
    Timely_Base  Timely_Operator_State  Timely_Stream  Timely_Progress
    Timely_Propagation_Exec  Timely_Tree_Compile  Timely_Builder_Op
    Timely_Dataflow_Op  Timely_Ifrontier  Timely_Infrastructure
    LList_Haskell_Setup  Propagation_Properties
  Correctness/    unchanged (incl. Timely_Collections)
  Examples/       unchanged layout (Label_Propagation/ subfolder stays)
  Tools/          Isar_Explore.thy  ir.ML  ml_repl.ML  tcp_handler.ML
  Attic/          top-level Wcc.thy (dup), Scratch_Not_Labels_Stable.thy,
                  all *.thy~ backups
```

Import style after moves: bare names within a folder, quoted relative paths
across folders. No Dataplane.X session-qualified imports.

## Dependency-tree improvements (parallelism)

1. Deduplicate the base hub: Timely_Operator_State imports just Timely_Base.
2. Dissolve the folder-level cycle found during phase 2+3:
   propagation_extras/Executable.thy imports dataplane/Lib/Locations while
   dataplane imports propagation_extras. Fix by moving Executable.thy and
   Termination.thy into dataplane/Lib/ (Termination has only external
   imports). Rewrite: AntichainOrder / ZmsetUtils / Zero_Cyc_Check refer to
   bare Executable, Timely_Base to "../Lib/Executable" and
   "../Lib/Termination", Executable's Locations import becomes bare.
   The ROOT session Propagation_Extras stays (it lists only
   Progress_Tracking theories; the folder keeps existing).
3. Import trims, one at a time, each verified by MCP before keeping
   (e.g. Input1's SimulationProofMethods / Propagation_Properties if unused,
   Init's AntichainOrder which comes via General).
4. Stretch goal (separate decision later): split Input1.thy along its
   sections so Input0 and Loop can start earlier.

## Within-file organization (sections with short text blurbs)

Priority order, edits via MCP write_file str_replace, whole groups at once:

1. Correctness/Produces.thy: graph-path lemmas / backtracks / produces-drops
   invariant / clean_input + singletons / release_caps + add_caps.
2. Correctness/Consumes.thy: channel + capability facts /
   extract_prog_changes / main invariant lemmas.
3. Lib/AntichainOrder.thy: order instances / supremum + frontier /
   exit_scope / equality + finiteness.
4. Examples/Label_Propagation/Label_Propagation_op.thy: record + graph
   utilities / operator logic / label_prop_upd_inv by field.
5. Timely/Timely_Operator_State.thy: record defs / primitive ops /
   simp-lemma groups per record.
6. Examples/Set_op.thy: operator def / step intro rules / wfinished+wtraced.
7. Examples/Label_Propagation/Input0.thy: frame facts / state updates.
8. Small utility files: 2-4 sections each.
   Models: Input1.thy, Correctness/General.thy, Wcc.thy, Loop.thy.

Misplaced-lemma moves (with the sectioning pass, one group at a time):
- MyMisc.thy graph/path_weight lemmas -> Zero_Cyc_Check.thy.
- DataplaneUtils.thy generic list/product lemmas -> ListUtils.thy /
  MyProduct_Instances.thy.

## Verification protocol (every batch)

1. get_processing_status on both example files until fully_processed with
   error_count 0. MCP results are hints; final say is jEdit.
2. Commit with a phase-labeled message after every successful batch.
3. Update the Progress section below.

# Progress

- [x] Phase 0 - baseline: plan written here, both examples check, commit.
      (Both files fully processed, 0 errors, after the ghc_setup restart.)
- [x] Phase 1 - attic + tools: moved top-level Wcc.thy and
      Scratch_Not_Labels_Stable.thy to Attic/, Isar_Explore + 3 ML files to
      Tools/, swept 61 *.thy~ backups into Attic/backups/. Gate green
      (LP 14284 + Batch 7770 commands, 0 errors). GHC spot check passed
      (value [GHC] at Batch_op.thy:110 returns the expected trace).
- [x] Phase 2+3 (combined to avoid double reprocessing) - moved 13 files to
      Lib/ and 12 to Timely/, rewrote all import headers to relative paths,
      dedup Timely_Operator_State -> Timely_Base. Found and fixed on the
      way: Executable.thy imported "../dataplane/Locations", now
      "../dataplane/Lib/Locations". Gate green (LP 14284 + Batch 7770 +
      Executable 513 commands, 0 errors).
- [x] Phase 4 - dissolved the propagation_extras <-> dataplane folder
      cycle: Executable.thy and Termination.thy moved into dataplane/Lib/,
      five referencing headers rewritten. Gate green (LP 14284 + Batch 7770
      + Executable 513 commands, 0 errors).
- [x] Phase 5 - import trims: removed 48 redundant import edges across 16
      files (semantic no-ops, verified by closure computation) plus the
      unused SimulationProofMethods import in Input1, which drops that
      theory from the LP chain. Timely_Base's deliberate hub list kept.
      Input1 18 -> 8 imports, Batch_op_Correctness 17 -> 9. Gate green
      (LP 14284 + Batch 7770 commands, 0 errors, full recheck ~6 min).
- [ ] Phase 6 - sectioning + lemma moves, file by file per priority list.
      Check + commit per file batch.
      - [x] 6a Produces (6 sections) + Consumes (3). Gate green.
      - [x] 6b AntichainOrder (7) + ZmsetUtils, ListUtils, CsetUtils,
            Locations (2-7 each). Gate green.
      - [x] 6c Label_Propagation_op (7) + Timely_Operator_State (4) +
            Set_op (6) + Input0 (4). Gate green.
      - [x] 6d small Correctness files + Timely_Stream (3) +
            Zero_Cyc_Check (3) + Batch_op_Correctness subsections (4).
            Gate green.
      - [x] 6e lemma moves: MyMisc path block -> AntichainOrder (first
            tried Zero_Cyc_Check, but the proofs cite
            in_antichain_from_list and two Automatic_Refinement.Misc
            artifacts: the oo notation, now inlined, and list_e_eq_lel,
            replaced by a local singleton_eq_append_conv),
            DataplaneUtils prod-defaults -> MyProduct_Instances,
            cfilter_cinsert -> CsetUtils, sections for both donors.
            Also opened and checked the eight off-chain example files
            that no gate had covered.
- [-] Phase 7 - split Input1.thy: DEFERRED by user decision
      (2026-07-31). Not worth it now; revisit if LP-chain check times
      become a bottleneck. Sketch: Input1 splits along its top-level
      sections into batch facts (518-2683) / invariant transfer +
      base-state projection (2684-4371) / loop_updates function (4372+),
      after computing which facts Input0 and Loop actually cite.

# Phase 8 - refined sorting of the Timely folder (approved 2026-07-31)

Principle: Timely/ holds the Timely Dataflow infrastructure only.

1. Move out:
   - LList_Haskell_Setup.thy -> Lib/ (code-extraction setup, zero Timely
     identifiers; imports become Coinductive.Coinductive_List + CsetUtils).
     Fix importers Set_op, Batch_op, Collatz.
   - Timely_Stream.thy -> dataplane/ top level (orthogonal stream
     formalization, name kept). Fix importers Correctness/General,
     Correctness/Timely_Collections, Examples/Ooo_Input_op.
2. Delete (to Attic/):
   - Timely_Base.thy (empty aggregator; import list inlined into
     Operator_State and, for now verbatim, into Tree_Compile).
   - Timely_Infrastructure.thy (empty stub, only spurious importer was
     LList_Haskell_Setup; its intended content is item 4).
3. Rename, dropping the Timely_ prefix (theory headers renamed too):
   Operator_State, Progress_Extraction (bare Progress would clash with
   Correctness/Progress), Propagation_Exec, Tree_Compile, Builder_Op,
   Dataflow_Op, Ifrontier. Propagation_Properties unchanged. Also update
   the two qualified references Timely_Operator_State.intsum_add_caps in
   Label_Propagation_op_Correctness.thy (lines ~1595, ~1881).
4. Consolidate state-law simp/intro lemmas into Operator_State's
   "Frame and Simp Rules" section. Confirmed movers: produ_release_caps
   (Extras), intsum_CONSUMES (Label_Propagation_op), the FIXME lemma at
   Labels.thy:320. Non-movers: anything whose subject is min_label,
   all_edges, labels_inv, label_prop_upd_inv, vertices, timestamps,
   graph, outputs_at_target, dataplane_tracker_inv. Execution rescans
   with a strict filter (every constant resolves in Operator_State) and
   MCP-verifies each mover.
5. Batch B extras: trim Tree_Compile's inlined import list down to what
   it uses, MCP-verified. ATTEMPTED AND REVERTED: the file uses
   Zero_Cyc_Check constants and its downstream (Propagation_Exec and
   further) relied on the transitive externals (map_entry, ccompare
   instances, while_option, the oo notation). A future trim needs a
   real used-constants analysis per file, not name grepping.

## Phase 8 progress

- [x] Batch A: moves + deletions + renames + import and qualified-ref
      fixups done, committed as efa63eb. Fixed on the way:
      LList_Haskell_Setup used is_None from
      Automatic_Refinement.Autoref_Bindings_HOL (reached only
      accidentally via Zero_Cyc_Check -> DFS_Framework); inlined as
      (%r. r ~= None). Gate green: LP 14284 + Batch 7786 + LList 144 +
      all eight off-chain files fully processed. value [GHC] failures
      in Batch_op (2) and Collatz (2) tolerated per user instruction,
      pending an isabelle ghc_setup rerun.
- [x] Batch B: committed as 1918ada. intsum_CONSUMES and de1_CONSUMES
      moved into Operator_State's Consolidated State Laws subsection,
      the redundant produ_release_caps copy in the correctness extras
      deleted (Operator_State already had it), stale FIXME in Labels
      removed, Tree_Compile trim reverted (item 5 above). At commit
      time Operator_State, Tree_Compile, and Propagation_Exec were
      fully processed with zero errors and the two example chains were
      mid-recheck. The gate then completed GREEN: LP 14284 and
      Batch 7779 commands fully processed, zero errors. Phase 8 done.

## Phase 9: leftover lemma moves

- [x] Set_op FIXME resolved: the eight generic weak-step lemmas at the
      top of Examples/Set_op.thy (wsteps_step_tau, wfinished_step_taus,
      wsteps_append, step_tau_wtraced, step_taus_wtraced,
      wsteps_not_finished_wtraced, wsteps_wtraced,
      wtraced_not_LNil_not_wfinished) moved to Lib/Operators_Utils.thy
      under a new "Weak Step and Weak Trace Laws" section (before the
      simulation material). All their constants and cited facts come
      from Nondeterministic_Dataflow.Operator, which Operators_Utils
      already imports. Set_op's leading section retitled to "The Set
      Operator". Note the moved rules are simp/intro, so importers of
      Operators_Utils (Builder_Op, Dataflow_Op) now see them. Gate
      GREEN: LP 14284 + Batch 7779 + Set_op 2203 + Operators_Utils
      1828 commands fully processed, zero errors.

## Phase 10: Timely refinement round 2 (approved plan)

User constraint: NO text blocks — prose is restricted to section
titles only. This also means REMOVING the text blocks added in
earlier phases to the Timely files.

- Batch C (sectioning, titles only):
  - Delete all 12 text blocks in Timely files (Dataflow_Op,
    Operator_State x6, Progress_Extraction, Propagation_Exec,
    Tree_Compile x2).
  - Propagation_Properties: section "Invariant Preservation Under PR
    take_step" before first lemma, "Termination of propagate_all"
    before propagate_all_terminates, retitle existing section to
    "Invariant Preservation Under CM take_step".
  - Progress_Extraction: retitle top section to "Progress
    Extraction" (the wrapper lives in Dataflow_Op); subsections
    "Laws of change_multiplicities" / "CM_equiv Congruence" /
    "Filtering extract_progress".
  - Tree_Compile: subsections "Compiling Trees to Operators" /
    "Compiling Trees to Summary Graphs" / "Structural Properties of
    Compiled Graphs" / "Summary Notation".
  - Propagation_Exec: subsections "take_step and propagate_all" /
    "Executable Minimum Selection" / "Laws of take_step" /
    "Display Utilities".
  - Dataflow_Op: sections "Compilation Entry Points" (before
    init_conf) and "Optimized Dataflow Operator" (before get_nid).
  - Builder_Op: subsection "The Notifier Operator" before
    notifier_op.
  - Ifrontier: retitle "Lemmas for ifrontier" to "Implied Frontiers
    Under change_multiplicities".
- Batch A (lemma moves; all cited facts verified to resolve at the
  targets):
  - class_linorder_lt_of_comp + linorder_order_ccompare:
    Propagation_Exec -> Lib/MyProduct_Instances (home of the
    order_ccompare class).
  - frontier_less_equal_pluss_le: Propagation_Properties ->
    Lib/AntichainOrder (near frontier_less_equal_le_trans).
  - frontier_less_equal_exit_scope_myfst_le: Propagation_Properties
    -> Lib/Bots (next to frontier_less_equal_exit_scope).
  - step_tau_pow_map_op: Dataflow_Op -> Lib/Operators_Utils (near
    steps_map_op).
  - take_step_PR_preserves_c_pts[simp]: Propagation_Properties ->
    Propagation_Exec (Laws of take_step; used by
    Correctness/Propagates).
  - sum_zmset (Ifrontier -> ZmsetUtils) SKIPPED: would need
    generalizing over the -+- notation.
- Batch B (riskiest, own gate + revert plan): trim Builder_Op's
  import Progress_Extraction -> Operator_State. Builder_Op and all
  six of its importers (Label_Propagation_op, Tmap_op, Concat_op,
  Branch_op, Increment_op, Ooo_Input_op) reference nothing from the
  Tree_Compile -> Propagation_Exec -> Progress_Extraction chain
  (grep-verified). Unblocks them from waiting on that chain. Same
  failure shape as the reverted Tree_Compile trim, so: MCP-verify
  Builder_Op + all importers incl. off-chain examples, revert on
  errors.

### Phase 10 progress

- [x] Batch C: 30 edits applied (12 text blocks deleted, 16 titles
      inserted, 3 retitles). Gate GREEN: LP 14284 + Batch 7779 fully
      processed, all 8 Timely files error-free.
- [x] Batch A: all five moves applied. Gate GREEN: LP 14284 + Batch
      7779 fully processed; MyProduct_Instances, AntichainOrder,
      Bots, Operators_Utils, Propagation_Exec,
      Propagation_Properties, Dataflow_Op, Correctness/Propagates
      all error-free.
- [ ] Batch B

## Operational notes for continuing this work

- Isabelle MCP: the harness-level mcp tools may be missing; a working
  fallback is piping JSON-RPC to
  python3 /home/rafael/Documents/AutoCorrode/iq/iq_bridge.py
  (helper: /home/rafael/.claude/jobs/03116bc3/tmp/iq.sh, usage
  "iq.sh <tool> <json-args>"; authenticate token MY_TOKEN is
  handled inside). Key tools: get_processing_status {path},
  get_diagnostics {scope:file, path, severity:error}, open_file,
  write_file (str_replace/insert/line; file must be open in jEdit;
  pass wait_until_processed:false or slow proofs hang the call),
  save_file, read_file (mode "Line"/"Search"), get_command_info
  (mode line, start_line/end_line).
- Gate protocol: after every batch, poll get_processing_status on the
  two example files until fully_processed with error_count 0; also
  check the eight off-chain Examples files (Collatz, Branch_op,
  Concat_op, Tmap_op, Source_op, Accumulator,
  Increment_op_Correctness, Ooo_Input_op_Correctness) - jEdit parks
  unfocused buffers, so force them with open_file followed by
  get_command_info on the last line with wait_until_processed:true.
- Known tolerated errors: value [GHC] commands in Examples/Batch_op.thy
  (2) and Examples/Collatz.thy (2) fail until the user reruns
  isabelle ghc_setup. Everything else must be error-free.
- File moves/renames need an Isabelle/jEdit RESTART by the user (ask
  them); buffer-level edits via write_file do not.
- The Poly/ML heap degrades after hours of reprocessing (seen at
  26 GB, GC stalls where zero commands finish for 12+ min). Remedy:
  ask the user to restart Isabelle; a fresh instance rechecks the
  full chain in ~20 min.
- Editing rules: pair-proving.md in this folder applies (edit .thy
  via MCP write_file, keep MCP timeouts short, the user's jEdit check
  is the final say). Isabelle theory names must be unique across the
  whole session (folders do not namespace them).
- Remaining open items: Phase 7 (Input1 split) is deferred, see
  above; the Dataplane ROOT session entry is still malformed/empty
  (optional fix). The Set_op FIXME is resolved (Phase 9).
