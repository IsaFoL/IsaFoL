# Formalization of Weidenbach's _Automated Reasoning―The Art of Generic Problem Solving_ #

[This directory](https://bitbucket.org/isafol/isafol/src/master/Weidenbach_Book/) contains an ongoing Isabelle formalization of Christoph Weidenbach's forthcoming book _Automated Reasoning―The Art of Generic Problem Solving_.

This branch contains the version of the development related to the paper A Verified SAT Solver with Two Watched Literals Using Imperative HOL (submitted to ITP 2017).

## Execution ##
1. [Isabelle2016-1](http://isabelle.in.tum.de/website-Isabelle2016-1/) is required to process the files
2. The [Archive Of Formal Proofs](https://www.isa-afp.org) is needed for the Refinement Framework. Please refer to the [installation instructions](https://www.isa-afp.org/using.shtml).
3. To process all the theory files, simply load ``Weidenbach_Book.thy'' in Isabelle2016-1.


## Testing the code ##

The generated code can be found in `code/IntInf` (infinite integer) or `code/Native`.

If [MLton](http://mlton.org) is in your path, you can compile the code with `make'.

A CNF is included in the repository. It takes less than 15 seconds to answer `UNSAT`. The program can be run with:

    ./full_SAT_Trail ../eq.atree.braun.7.unsat.cnf

