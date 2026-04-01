# Key Definitions, Types, and Lemmas

This is a glossary of the most important types, records, definitions, and lemmas in the project, organized by layer.

---

## Layer 1: Nondeterministic Dataflow (`nondeterministic_dataflow/`)

### Core Operator Model (`Operator.thy`)

| Name | Kind | Line | Description |
|------|------|------|-------------|
| `op` | codatatype | ~83 | The core operator type: `Read chan (val => op) \| Write chan val op \| Choice op op \| Silent op`. A coinductive labeled transition system for nondeterministic I/O. |
| `wstep` | inductive | ~120 | Weak step relation: allows zero or more Silent steps before a visible Read/Write action. |
| `bisim` | coinductive | ~200 | Strong bisimulation equivalence between operators (infix `~`). |
| `wbisim` | coinductive | ~350 | Weak bisimulation equivalence (allows silent steps). |
| `traced` | coinductive | ~500 | Trace relation: coinductive predicate for observable behavior sequences. |
| `finished` | coinductive | ~550 | Termination predicate for operators that reach a final state. |
| `sim` | definition | ~180 | Simulation relation: one direction of bisimulation. |
| `bisim_cong` | inductive | ~230 | Congruence closure for bisimulation up-to reasoning. Includes constructors `bc_base`, `bc_bisim`, `bc_refl`, `bc_sym`, `bc_trans`, `bc_Read`, `bc_Write`, `bc_Silent`, `bc_Choice`. |
| `bisim_coinduct_upto` | lemma | ~280 | Up-to coinduction principle for bisimulation. The primary coinduction technique used in equivalence proofs. |

### Buffer and Composition Operators (`BNA_Operators.thy`)

| Name | Kind | Line | Description |
|------|------|------|-------------|
| `BENQ` | definition | ~30 | Buffer enqueue: adds a value to a channel buffer. |
| `BHD` | definition | ~40 | Buffer head: reads front element from a channel buffer. |
| `BTL` | definition | ~50 | Buffer tail: removes front element from a channel buffer. |
| `BULK_BENQ` | definition | ~60 | Bulk enqueue: enqueues multiple values at once. |
| `comp_op` | corec | ~150 | Parallel composition of two operators with internal channel wiring and buffering. The fundamental composition from Network Algebra. |
| `pcomp_op` | corec | ~400 | Partial composition variant. |
| `scomp_op` | corec | ~450 | Sequential composition variant. |

---

## Layer 2: Propagation Extras (`propagation_extras/`)

### Executable Propagation (`Executable.thy`)

| Name | Kind | Line | Description |
|------|------|------|-------------|
| `executable_propagate` | definition | ~50 | Executable version of the propagation step, connecting the AFP Progress_Tracking formalization to executable code. |
| Various code lemmas | lemma | ~100+ | Lemmas establishing correspondence between abstract propagation and executable code. |

### Termination Proof (`Termination.thy`)

| Name | Kind | Line | Description |
|------|------|------|-------------|
| `neg_order` | definition | ~250 | Termination measure: lexicographic triple `(future_fuel c, measure_sum c, total_work_repro c)`. |
| `future_fuel` | definition | ~200 | Component 1: counts implications above active work items. Decreases when new active work appears. |
| `measure_sum` | definition | ~220 | Component 2: sum of `weight` over locations with negative work. Decreases when negative work is consumed. |
| `total_work_repro` | definition | ~230 | Component 3: multiset ordering based on work items that are "reproductive" (not yet dominated by implications). |
| `propagation_termination` | lemma | ~2100 | **Main result**: `next_propagate c c' ==> inv_imps_work_sum c ==> inv_implications_nonneg c ==> neg_order c > neg_order c'`. Proves that each propagation step strictly decreases the measure. |

All definitions and proofs are within `context dataflow_topology`.

---

## Layer 3: Dataplane (`dataplane/`)

### Ports and Locations (`Locations.thy`)

| Name | Kind | Line | Description |
|------|------|------|-------------|
| `port` | datatype | ~20 | `Src p \| Trg p` -- distinguishes source (output) and target (input) ports of an operator. |
| `location` | datatype | ~30 | `Loc node port` -- a location in the dataflow graph, combining a node identifier with a port. |

### Timestamp Product Type (`MyProduct_Instances.thy`)

| Name | Kind | Line | Description |
|------|------|------|-------------|
| `myprod` | datatype | ~15 | Custom product type with explicit `zero`, `plus`, `order` instances for timestamp lattices used in Timely Dataflow. |

### Event Streams (`Timely_Stream.thy`)

| Name | Kind | Line | Description |
|------|------|------|-------------|
| `event` | datatype | ~20 | `Data t d \| Drop t \| Mint t` -- timestamped events: data delivery, capability drops, and capability mints. |
| `timely_monotone` | coinductive | ~50 | Coinductive predicate ensuring event streams respect capability multiset tracking (capabilities are minted before use and dropped correctly). |

### Antichain Ordering (`AntichainOrder.thy`)

| Name | Kind | Line | Description |
|------|------|------|-------------|
| Key definitions | various | throughout | Connects AFP `Progress_Tracking.Antichain` with the dataplane, providing antichain-based partial order for timestamps and frontier reasoning. |

### Core Infrastructure (`Timely_Infrastructure.thy`, ~1785 lines)

| Name | Kind | Line | Description |
|------|------|------|-------------|
| `subgraph` | record | ~50 | Record containing the dataflow subgraph topology: `summ` (summary function), `nxt` (next function), `pt_tr` (progress tracker state). |
| `operator_state` | record | ~80 | Tracks operator state: `consu` (consumed deltas), `inter` (internal deltas), `produ` (produced deltas), `input`/`outpu` (I/O buffers), `ocaps` (outstanding capabilities), `front` (frontier). These correspond to internal buffers in Rust Timely Dataflow. |
| `extract_progress` | definition | ~200 | Extracts progress information from operator_state buffers (consu, inter, produ) for reporting to the progress tracking algorithm. |
| `extract_prog` | definition | ~220 | Applies extract_progress across all operators to compute aggregate changelist. |
| `propagate_all` | definition | ~650 | While-loop propagation using `while_option`: repeatedly takes propagation steps until worklists are empty. `propagate_all su c = while_option (\<lambda>c. \<not> worklists_empty c) (take_step su (the (mymin ...))) c`. |
| `propagate_all_terminates` | lemma | ~677 | States that `propagate_all` never returns `None` (i.e., the loop always terminates). Uses `wf_rel_while_option_Some` with `inv_image {(x,y). x < y} neg_order`. |
| `dataflow_op` | corec | ~750 | The main corecursive definition bridging data plane operators with control plane. Handles Read/Write/Choice/Silent transitions, including the `Write Inl Inl` case for progress reporting. |
| `timely_dataflow` | definition | ~1700 | Top-level composition of a timely dataflow graph from operators, topology, and initial state. |
| `enum_dataflow_topology` | locale | ~670 | Used in `propagate_all_terminates`. Extends `dataflow_topology` from AFP with enumeration. |

### Utility Files

| File | Key Contents |
|------|-------------|
| `DataplaneUtils.thy` | Utility lemmas for operator composition, buffer reasoning, zmultiset arithmetic. Imports `Operator`, `BNA_Operators`, `Executable`, `Zero_Cyc_Check`, `Locations`. |
| `Operators_Utils.thy` | Operator-specific utilities, writes corecursion helpers. Imports `Operator`, `DataplaneUtils`. |
| `Zero_Cyc_Check.thy` | Zero-cycle checking via DFS (uses AFP `DFS_Framework`). Verifies acyclicity conditions on the dataflow graph needed for termination. |

---

## Correctness Layer (`dataplane/Correctness/`)

### Invariant Definitions (`General.thy`, ~1638 lines)

| Name | Kind | Line | Description |
|------|------|------|-------------|
| `dataplane_tracker_inv` | definition | ~900 | **Main invariant** connecting data plane with control plane. An existentially quantified conjunction of ~13 sub-invariants (see below). |
| `c_pts_inv` | definition | ~400 | Pointstamp consistency: relates the concrete pointstamps to the abstract configuration. |
| `Src_caps_inv` | definition | ~450 | Source capability invariant: outstanding capabilities at source ports are consistent with operator state. |
| `Trg_caps_inv` | definition | ~500 | Target capability invariant: outstanding capabilities at target ports are consistent with channel buffers. |
| `front_inv` | definition | ~550 | Frontier invariant: operator frontiers are consistent with the propagation state. |
| `imp_front_inv` | definition | ~600 | Implication frontier invariant: frontier respects summary-induced implications. |
| `chnls_imp_front_inv` | definition | ~620 | Channel implication frontier invariant: channel contents respect frontier implications. |
| `change_deltas_inv` | definition | ~650 | Delta consistency: consu/inter/produ deltas are well-formed. |
| `propagation_inv` | definition | ~700 | Propagation algorithm state invariant (from AFP Progress_Tracking). |
| `extract_prog_changes_above_impl_inv` | definition | ~750 | **Hardest sub-invariant**: states that operators can report their progress independently; changes are above the implications. |
| `produ_consu_inter_supported` | definition | ~800 | Produced/consumed/internal changes are supported by existing capabilities. |

### Completed Proofs

| File | Lemma | Description |
|------|-------|-------------|
| `Consumes.thy` (~1173 lines) | `consumes_preserves_inv` | `dataplane_tracker_inv` is preserved when an operator consumes data (consu buffer increases). Fully proved. |
| `Progress.thy` (~377 lines) | `progress_preserves_inv` | `dataplane_tracker_inv` is preserved when an operator reports progress (buffers flushed, multiplicities change). Fully proved. |
| `Produces.thy` (~961 lines) | `produces_preserves_inv` | `dataplane_tracker_inv` is preserved when an operator produces data. Partially proved. |
