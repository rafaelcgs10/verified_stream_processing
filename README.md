# Verifying Timely Dataflow Programs in Isabelle/HOL

This repository contains the Isabelle/HOL formalization accompanying the PhD
thesis *Verifying Timely Dataflow Programs in Isabelle/HOL*. It covers the
nondeterministic asynchronous dataflow operators, the Timely Dataflow data
plane and its integration with progress tracking, the reasoning infrastructure
for proving programs correct, and the verified case studies.

The names of types, constants and lemmas are the same in the thesis and in the
theories below.

## Requirements

The formalization is checked with **Isabelle2025-2** and the matching release of
the **Archive of Formal Proofs** (AFP). Building it needs about 24 GB of
memory (the ML process alone peaks around 16 GB) and about 9 GB of disk for
Isabelle, the AFP, and the Haskell toolchain.

0. **OS packages.** On a minimal Linux system (for example a fresh Ubuntu
   container), install the following before anything else:

   ```
   apt-get install curl unzip ca-certificates fontconfig xz-utils make \
     build-essential libgmp-dev libnuma-dev libncurses-dev zlib1g-dev
   ```

   Without `fontconfig`, `isabelle build` aborts immediately with
   `Fontconfig head is null`. Without `xz-utils`, `make`, and a C compiler,
   the `isabelle ghc_setup` step below fails. Regular desktop installations
   usually have all of these already.

1. **Isabelle2025-2**, from <https://isabelle.in.tum.de/>.
   Installation instructions for every platform are part of the official
   tutorial: <https://isabelle.in.tum.de/installation.html>.
   After installing, make the `isabelle` executable available on your `PATH`,
   for example by adding the `bin` directory of the installation to it.
   The download server is reachable over IPv6 only. From an IPv4-only network
   (for example a default Docker bridge), download the same archive from an
   official mirror such as
   <https://proofcraft.systems/isabelle/dist/Isabelle2025-2_linux.tar.gz>.

2. **The AFP release for Isabelle2025-2**, from
   <https://www.isa-afp.org/download/>. Register it as an Isabelle component by
   following <https://www.isa-afp.org/help/>, which amounts to

   ```
   isabelle components -u /path/to/afp/thys
   ```

   Installing the complete AFP is recommended. The build uses the entries
   `Coinductive`, `Progress_Tracking`, `DFS_Framework`, `Containers`,
   `Collections`, `Automatic_Refinement` and `Refine_Monadic`, and these pull in
   further AFP entries of their own.

3. **The GHC component**, set up once with

   ```
   isabelle ghc_setup
   ```

   This step is **required**, not optional: several theories evaluate the
   generated code with `value [GHC]`, and the build fails without it. The
   command downloads a Haskell toolchain and needs network access on first use.

## Building

From the root of this repository, check the whole formalization with

```
isabelle build -d . -v Dataplane
```

This builds the session `Nondeterministic_Dataflow`, which contains the
operator model and the algebra tables, and then `Dataplane`, which checks
every remaining theory, including all the case studies. Expect about half an
hour on a recent machine with enough memory, and a few hours on a slower one.
On a slow or containerized machine, pass `-o timeout_scale=2` if a session
times out.

To browse the formalization interactively instead, open it in Isabelle/jEdit
with the session preloaded:

```
isabelle jedit -d . -R Dataplane
```

Then use *File > Open* to look at any theory, for instance
`dataplane/Examples/Weakly_Connected_Components/Label_Propagation_Op_Correctness.thy`.
Loading a theory for the first time replays its proofs, which takes a while for
the larger case studies.

## Structure

| Directory | Content |
|---|---|
| `nondeterministic_dataflow/` | the nondeterministic asynchronous dataflow operators, together with `table_1/`, `table_2/` and `table_3/`, the proofs of the algebra axioms |
| `dataplane/Timely_Stream.thy` | events, timestamped streams, and their monotonicity properties |
| `dataplane/Lib/` | general purpose libraries, timestamps, antichains, locations, executability |
| `dataplane/Timely/` | the Timely Dataflow data plane: operator states, the dataflow operator, the progress tracker, and the compilation of dataflow trees |
| `dataplane/Correctness/` | the reusable correctness infrastructure: progress, capabilities, collections, and the simulation proof methods |
| `dataplane/Common_Operators/` | reusable operators such as the out-of-order input operator, the increment operator, and the set specification operator |
| `dataplane/Examples/Batch/` | the batch operator and its correctness proof |
| `dataplane/Examples/Collatz/` | the Collatz program, an example with a loop |
| `dataplane/Examples/Weakly_Connected_Components/` | the weakly connected components case study: the label propagation operator, its correctness proof, and an imperative version of the same algorithm verified with the Isabelle Refinement Framework |

The main results are the weak bisimilarity correctness lemmas
`correctness` in `Examples/Batch/Batch_Op_Correctness.thy` and in
`Examples/Weakly_Connected_Components/Label_Propagation_Op_Correctness.thy`.

## License

The formalization is distributed under the terms of the `LICENSE` file in this
repository.
