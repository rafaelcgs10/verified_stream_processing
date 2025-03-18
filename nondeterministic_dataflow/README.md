# Nondeterministic Asynchronous Dataflow in Isabelle/HOL
This is the artifact accompanying the paper:
Nondeterministic Asynchronous Dataflow in Isabelle/HOL

### How To Run?
The artifact contains the formalization of Nondeterministic Asynchronous Dataflow in Isabelle/HOL.

It works with Isabelle 2024, which can be downloaded here:

[https://isabelle.in.tum.de/website-Isabelle2024/](https://isabelle.in.tum.de/website-Isabelle2024/)

More instalation instructions can be found here:

[https://isabelle.in.tum.de/website-Isabelle2024/installation.html](https://isabelle.in.tum.de/website-Isabelle2024/installation.html)

After installing Isabelle, you must also obtain the Archive of Formal Proofs (AFP) version 2024 here:

[https://foss.heptapod.net/isa-afp/afp-devel/-/tree/Isabelle2024?ref_type=tags](https://foss.heptapod.net/isa-afp/afp-devel/-/tree/Isabelle2024?ref_type=tags)

Setup the AFP following the instructions:

[https://www.isa-afp.org/help/](https://www.isa-afp.org/help/)

Assuming that Isabelle and AFP are installed, then one can open this project with

```
isabelle jedit -d ~/path_to_this_folder -R Nondeterministic_Dataflow
```

or

```
isabelle build -d ~/path_to_this_folder -v Nondeterministic_Dataflow
```