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
2. Import trims, one at a time, each verified by MCP before keeping
   (e.g. Input1's SimulationProofMethods / Propagation_Properties if unused,
   Init's AntichainOrder which comes via General).
3. Stretch goal (separate decision later): split Input1.thy along its
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

- [ ] Phase 0 - baseline: plan written here, both examples check, commit.
- [ ] Phase 1 - attic + tools: move dead files to Attic/, Isar_Explore + ML
      files to Tools/, sweep *.thy~ backups. Check, commit.
- [ ] Phase 2 - Lib/: move 13 library files, fix imports. Check, commit.
- [ ] Phase 3 - Timely/: move 12 infrastructure files, fix imports,
      dedup Timely_Operator_State -> Timely_Base. Check, commit.
- [ ] Phase 4 - import trims, one at a time, MCP-verified. Check, commit.
- [ ] Phase 5 - sectioning + lemma moves, file by file per priority list.
      Check + commit per file batch.
- [ ] Phase 6 (optional, needs user decision) - split Input1.thy.
