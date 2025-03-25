# Nondeterministic Asynchronous Dataflow in Isabelle/HOL
This is the artifact accompanying the paper:
Nondeterministic Asynchronous Dataflow in Isabelle/HOL

### How To Run?
It works with Isabelle 2025, which can be downloaded here:

[https://isabelle.in.tum.de/website-Isabelle2025/](https://isabelle.in.tum.de/website-Isabelle2025/)

More instalation instructions can be found here:

[https://isabelle.in.tum.de/website-Isabelle2025/installation.html](https://isabelle.in.tum.de/website-Isabelle2024/installation.html)

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