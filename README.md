# Verified-Time-Aware-Stream-Processing
This is the artifact accompanying the paper:
Verified Time-Aware Stream Processing

### How To Run?
The artifact contains the formalization of Time-Aware-Stream-Processing, and the verification of operators.

It works with Isabelle 2023, which can be downloaded here:

[https://isabelle.in.tum.de/website-Isabelle2023/](https://isabelle.in.tum.de/website-Isabelle2023/)

More instalation instructions can be found here:

[https://isabelle.in.tum.de/website-Isabelle2023/installation.html](https://isabelle.in.tum.de/website-Isabelle2023/installation.html)

After installing Isabelle, you must also obtain the Archive of Formal Proofs (AFP) version 2023 here:

[https://foss.heptapod.net/isa-afp/afp-devel/-/tree/Isabelle2023?ref_type=tags](https://foss.heptapod.net/isa-afp/afp-devel/-/tree/Isabelle2023?ref_type=tags)

Setup the AFP following the instructions:

[https://www.isa-afp.org/help/](https://www.isa-afp.org/help/)

Assuming that Isabelle and AFP are installed, then one can open this project with

```
isabelle jedit -d ~/path_to_this_folder -R Stream_Processing
```

or

```
isabelle build -d ~/path_to_this_folder -v Stream_Processing
```