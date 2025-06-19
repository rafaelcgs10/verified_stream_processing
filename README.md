# Nondeterministic Asynchronous Dataflow in Isabelle/HOL
This is the artifact accompanying the paper:
Nondeterministic Asynchronous Dataflow in Isabelle/HOL

### How To Run?
It works with Isabelle 2025, which can be downloaded here:

[https://isabelle.in.tum.de/website-Isabelle2025/](https://isabelle.in.tum.de/website-Isabelle2025/)

More instalation instructions can be found here:

[https://isabelle.in.tum.de/website-Isabelle2025/installation.html](https://isabelle.in.tum.de/website-Isabelle2025/installation.html)

After installing Isabelle, you must also obtain the Archive of Formal Proofs (AFP) version 2025 here:

[https://www.isa-afp.org/release/afp-current.tar.gz](https://www.isa-afp.org/release/afp-current.tar.gz)

Setup the AFP following the instructions:

[https://www.isa-afp.org/help/](https://www.isa-afp.org/help/)

Last, run the following command to setup Isabelle with GHC:

```
isabelle ghc_setup
```

Assuming that Isabelle with GHC and AFP are installed, then one can open this project with


```
isabelle jedit -d ~/path_to_this_folder -R Nondeterministic_Dataflow
```

or

```
isabelle build -d ~/path_to_this_folder -v Nondeterministic_Dataflow
```

Warning: this build process can take up to 20 minutes on a fast laptop.

The organization of this repository is the following:

``` shell
├── Operator.thy: The operator codatatype, strong and weak bisimilarity, and traces
├── BNA_Operators.thy: The operators from nondeterministic asynchronous dataflow networks
├── table_1: Axioms related to identity, sequential/parallel composition, loop, and transposition
├── table_2: Axioms related to equality test, copy, source, and sink
├── table_3: Axioms related to merge, split, source and, sink
├── CSet_LList_Impl.thy: Implementation of countable sets as lazy lists
├── Cset_Setup.thy: Auxiliary countable set setup
├── Defaults.thy: Defaults type class
├── Lifted.thy: Typedef setup that lifts the codatatype operator
├── Lifted_Table_1.thy: Lifting of table 1
├── Lifted_Table_2.thy: Lifting of table 2
├── Lifted_Table_3.thy: Lifting of table 3
└── Eval.thy: Evaluation of traces of some operators
```
