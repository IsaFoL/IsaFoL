# A Modular Formalization of Superposition in Isabelle/HOL

This formalization is compatible with Isabelle2023 and requires the Archive of Formal Proofs.
Instructions to install Isabelle are available at https://isabelle.in.tum.de/installation.html.
Instruction to install the AFP are available at https://www.isa-afp.org/help.

Note that the formalization is also compatible with isabelle-devel and afp-devel.

The best place to start exploring the formalization is the ROOT file: the main results were
split into different theories listed there. You can start exploring with the following command:

    $ isabelle jedit ROOT

This will open the jEdit-based Isabelle environment and CTRL+clicking on a theory name will
open it.

You can build (i.e. verify) the formalization with the following command:

    $ isabelle build -D .
