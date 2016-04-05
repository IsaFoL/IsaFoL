# Formalization of Weidenbach's _Automated Reasoning―The Art of Generic Problem Solving_ #

[This directory](https://bitbucket.org/jasmin_blanchette/isafol/src/master/Weidenbach_Book/) contains an ongoing Isabelle formalization of Christoph Weidenbach's forthcoming book _Automated Reasoning―The Art of Generic Problem Solving_.

## Organisation of the Development ##
* The branch [master]() contains the latest development and is based on Isabelle's repository version.
* The branch IJCAR2016 contains the version of the development related to the paper.

## Documentation ##

A recent version of the documentation the theory files is also available as [here](http://people.mpi-inf.mpg.de/~mfleury/IsaFoL/current/Weidenbach_Book).

## Authors ##

* [Mathias Fleury](mailto:mathias.fleury shtrudel mpi-inf.mpg.de)
* [Jasmin Christian Blanchette](mailto:jasmin.blanchette shtrudel inria.fr)

## Additional Collaborators ##

* [Dmitriy Traytel](mailto:traytel shtrudel inf.ethz.ch)
* [Christoph Weidenbach](mailto:weidenbach shtrudel mpi-inf.mpg.de)

## Publications ##

* [A Verified SAT Solver Framework with Learn, Forget, Restart, and Incrementality](http://people.mpi-inf.mpg.de/~jblanche/sat.pdf).
  J. C. Blanchette, M. Fleury, and C. Weidenbach.
  In Olivetti, N., Tiwari, A. (eds.) 8th International Joint Conference on Automated Reasoning (IJCAR 2016), LNCS, Springer, 2016.

* [Formalisation of Ground Inference Systems in a Proof Assistant](http://www.mpi-inf.mpg.de/fileadmin/inf/rg1/Documents/fleury_master_thesis.pdf).
  M. Fleury.
  M.Sc. thesis, École normale supérieure Rennes, 2015.


## IJCAR 2016 ##

First switch to the correct branch using git checkout.

### Execution ###

[Isabelle2016](http://isabelle.in.tum.de/website-Isabelle2016) is required to run the development.

To process all the theory files, simply load ```Weidenbach_Book.thy```.

### Documentation ###

The documentation is available available [here](http://people.mpi-inf.mpg.de/~mfleury/IsaFoL/IJCAR2016/Weidenbach_Book) (the 
[outline](http://people.mpi-inf.mpg.de/~mfleury/IsaFoL/IJCAR2016/Weidenbach_Book/outline.pdf) contains the definitions and theorems, but the proofs are skipped).

The paper [A Verified SAT Solver Framework](http://people.mpi-inf.mpg.de/~jblanche/sat.pdf) refers to theorems in the formalization. The following table establishes a correspondence between the two sources.

    Paper        Theory file           Theorem name
    -----------------------------------------------------------------------------------------------------
    Theorem 1    CDCL_NOT              wf_dpll_bj
    Theorem 2    CDCL_NOT              full_dpll_backjump_final_state_from_init_state
    Lemma 3      DPLL_NOT              backtrack_is_backjump
    Theorem 4    DPLL_NOT              dpll_conclusive_state_correctness
    Theorem 5    CDCL_NOT              wf_cdcl\<^sub>N\<^sub>O\<^sub>T_no_learn_and_forget_infinite_chain
    Theorem 6    CDCL_W                full_cdcl\<^sub>W_stgy_final_state_conclusive_from_init_state
    Theorem 7    CDCL_W_Termination    cdcl\<^sub>W_stgy_distinct_mset_clauses
    Theorem 8    CDCL_W_Incremental    incremental_conclusive_state

The Standard ML code produced by the SAT solver can be viewed by moving the cursor to the ```export_code``` line in ```CDCL_W_Implementation.thy```.
