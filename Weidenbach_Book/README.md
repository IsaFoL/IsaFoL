# Formalization of Weidenbach's _Automated Reasoning―The Art of Generic Problem Solving_ #

[This directory](https://bitbucket.org/jasmin_blanchette/isafol/src/master/Weidenbach_Book/)
contains an ongoing Isabelle formalization of Christoph Weidenbach's
forthcoming book _Automated Reasoning―The Art of Generic Problem Solving_.

## Authors ##

* [Mathias Fleury](mailto:mathias.fleury shtrudel mpi-inf.mpg.de)
* [Jasmin Christian Blanchette](mailto:jasmin.blanchette shtrudel inria.fr)

## Additional Collaborators ##

* [Dmitriy Traytel](mailto:traytel shtrudel inf.ethz.ch)
* [Christoph Weidenbach](mailto:weidenbach shtrudel mpi-inf.mpg.de)

## Publications ##

* [A Verified SAT Solver Framework with Learn, Forget, Restart, and Incrementality](http://people.mpi-inf.mpg.de/~jblanche/sat.pdf).
  J. C. Blanchette, M. Fleury, and C. Weidenbach. Submitted draft.

* [Formalisation of Ground Inference Systems in a Proof Assistant](http://www.mpi-inf.mpg.de/fileadmin/inf/rg1/Documents/fleury_master_thesis.pdf).
  M. Fleury.
  M.Sc. thesis, École normale supérieure Rennes, 2015.

## Execution ##

A recent version of Isabelle is necessary to process the theory files (e.g.,
[Isabelle2016-RC2](http://isabelle.in.tum.de/website-Isabelle2016-RC2)).

To process all the theory files, simply load ```Weidenbach_Book.thy```.

## Documentation ##

A recent version of the theory files is also available as [a PDF document](https://bitbucket.org/jasmin_blanchette/isafol/src/master/Weidenbach_Book/output/document.pdf). 

The draft [A Verified SAT Solver Framework](http://people.mpi-inf.mpg.de/~jblanche/sat.pdf) refers to theorems in the formalization.
The following table establishes a correspondence between the two sources.

Paper                            Theory file   Theorem name
---------------------------------------------------------------------
Theorem 1 (dpllNOT_sound)        DPLL_NOT      dpll\<sym\>N\<sym\>

The Standard ML code produced by the SAT solver can be viewed by moving the cursor to the ```export_code``` line
in ```CDCL_W_Implementation.thy```.

## Status ##

Our partial implementation of two watched literals is located in ```CDCL_Two_Watched_Literals.thy```.
