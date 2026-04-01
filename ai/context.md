# Project Context

This project formalizes [Timely Dataflow](https://timelydataflow.github.io/timely-dataflow/) in Isabelle/HOL and verifies algorithms for this framework. We use asynchronous nondeterministic dataflows as the base model for Timely Dataflow operators and graphs.

**References:**
- Timely Dataflow tutorial: https://timelydataflow.github.io/timely-dataflow/ (local: `/home/rafael/Documents/timely-dataflow/mdbook`)
- Rust implementation: https://github.com/TimelyDataflow/timely-dataflow (local: `/home/rafael/Documents/timely-dataflow`)

## Correspondence with Rust

The Isabelle/HOL formalization models parts of the Timely Dataflow infrastructure. The correspondence is not one-to-one (Rust and Isabelle/HOL are very different), but there are meaningful similarities. In particular, operators have internal buffers tracking outstanding capability changes not yet reported to the progress tracking algorithm. In Rust these are called *consumeds*, *produceds*, and *internals*; in our formalization they are the fields `consu`, `inter`, and `produ` of the `operator_state` record.

The core infrastructure is in `Timely_Infrastructure.thy` -- see the comments there.

## Progress Reporting

An important operator behavior is *reporting progress*: the `operator_state` buffers (`consu`, `inter`, `produ`) are flushed, and their information is sent to the propagation algorithm, causing changes of multiplicities. This is handled by the `extract_progress` definition and the `Write Inl Inl` case in `dataflow_op`, which calls `change_multiplicities`, which in turn uses `take_step`.

An important reference: https://timelydataflow.github.io/timely-dataflow/chapter_5/chapter_5_2.html#maintaining-capabilities

## Verification Examples

The **Examples** folder contains dataflow graph verification examples. Verification is done via equivalence proofs (weak bisimilarity of operators) between the Timely Dataflow program and an operator `set_spec_op` that produces the expected output as a set of elements.

## Correctness Invariants

An important part of the proof is connecting the data plane with the control plane (progress tracking). The `Correctness/` folder contains the invariants for our correctness proof:

- **`General.thy`** -- Defines the invariants. The main one is `dataplane_tracker_inv`, which connects the data plane with the control plane. The most challenging sub-invariant is `extract_prog_changes_above_impl_inv`, stating that operators can report their progress independently.
- **`Consumes.thy`** -- Proves invariant preservation when an operator consumes data (increasing the `consu` buffer). *Complete.*
- **`Progress.thy`** -- Proves invariant preservation when an operator reports progress, causing multiplicity changes in the control plane. *Complete.*
- **`Produces.thy`** -- Proves invariant preservation when an operator produces data and drops capabilities. *Partially complete.*
