# Formalization of Weidenbach's _Automated Reasoning―The Art of Generic Problem Solving_ #

[This directory](https://bitbucket.org/isafol/isafol/src/master/Weidenbach_Book/) contains an ongoing Isabelle formalization of Christoph Weidenbach's forthcoming book _Automated Reasoning―The Art of Generic Problem Solving_.
The relevant part of the book can be found [here](http://people.mpi-inf.mpg.de/~mfleury/paper/Weidenback_Book_CDCL.pdf)

## Organisation of the Development ##

* The branch [master](https://bitbucket.org/isafol/isafol/src/master/Weidenbach_Book/) contains the latest development and is based on Isabelle's repository version.
* The branch [IJCAR2016](https://bitbucket.org/isafol/isafol/src/IJCAR2016/Weidenbach_Book/) contains the version of the development related to the paper. Please refer to [this page](https://bitbucket.org/isafol/isafol/src/IJCAR2016/Weidenbach_Book/Readme.md).

## Documentation ##

A recent version of the documentation the theory files is also available [here](http://people.mpi-inf.mpg.de/~mfleury/IsaFoL/current/Weidenbach_Book).

## Authors ##

* [Mathias Fleury](mailto:mathias.fleury shtrudel mpi-inf.mpg.de)
* [Jasmin Christian Blanchette](mailto:j.c.blanchette shtrudel vu.nl>)
* [Peter Lammich](mailto:lammich shtrudel in.tum.de)


## Additional Collaborators ##

* [Dmitriy Traytel](mailto:traytel shtrudel inf.ethz.ch)
* [Christoph Weidenbach](mailto:weidenbach shtrudel mpi-inf.mpg.de)


## Publications ##

* [A verified SAT solver framework with learn, forget, restart, and incrementality](http://matryoshka.gforge.inria.fr/pubs/sat_sister.pdf)
  J. C. Blanchette, M. Fleury, and C. Weidenbach.
  In Sierra, C. (ed.) 26th International Joint Conference on Artificial Intelligence (IJCAI-17), pp. 4786–4790, ijcai.org, 2017. 

* [A Verified SAT Solver Framework with Learn, Forget, Restart, and Incrementality](http://people.mpi-inf.mpg.de/~jblanche/sat.pdf).
  J. C. Blanchette, M. Fleury, and C. Weidenbach.
  In Olivetti, N., Tiwari, A. (eds.) 8th International Joint Conference on Automated Reasoning (IJCAR 2016), LNCS, Springer, 2016.

* [Formalisation of Ground Inference Systems in a Proof Assistant](http://www.mpi-inf.mpg.de/fileadmin/inf/rg1/Documents/fleury_master_thesis.pdf).
  M. Fleury.
  M.Sc. thesis, École normale supérieure Rennes, 2015.

## Execution ##

* Please install [Isabelle2017](http://isabelle.in.tum.de) is needed to process the files.
* Install the [Archive of Formal proofs](https://www.isa-afp.org/using.html) as mentionned
* To process all the theory files, clone the repository and load ``CDCL_Two_Watched_Literals_List_Watched_Init_Trail_Code.thy``, using:
   ``/path/to/isabelle jedit -d . -l CDCL CDCL_Two_Watched_Literals_List_Watched_Init_Trail_Code.thy``
   (``-d .`` ensures that Isabelle knows about the sessions of this formalisation, and ``-l CDCL`` means that we build the formalisation on top of CDCL)


## Names Correspondance and Publications

* 


* A Verified SAT Solver Framework with Learn, Forget, Restart, and Incrementality, submitted to JAR


|Paper                    |  Theory file                      |   Isabelle name
|-------------------------|-----------------------------------|---------------------------------------------------------------------
|'v literal               |   ``../lib/Clausal_Logic``        |  ``'a literal``
|``('v, cls) ann_literal``|  ``Partial_Annotated_Clausal_Logic`` | ``('v, 'w, 'mark) annotated_lit``  [1]
|``DPLL_NOT+BJ``          |  ``CDCL_NOT``                     | ``dpll_bj``
|Theorem 1                |  ``CDCL_NOT``                     |   ``wf_dpll_bj``
|Theorem 2                |  ``CDCL_NOT``                     |   ``full_dpll_backjump_final_state_from_init_state``
|Lemma 3                  |  ``DPLL_NOT``                     |   ``backtrack_is_backjump``
|Theorem 4                |  ``DPLL_NOT``                     |   ``dpll_conclusive_state_correctness``
|``cdcl_NOT``             |  ``CDCL_NOT``                     |   ``CDCL\<^sub>N\<^sub>O\<^sub>T``
|Theorem 5                |  ``CDCL_NOT``                     |   ``wf_cdcl\<^sub>N\<^sub>O\<^sub>T_no_learn_and_forget_infinite_chain``
| ``restartT``            |  ``CDCL_NOT``                     |   ``CDCL\<^sub>N\<^sub>O\<^sub>T_raw_restart`` [2]
| ``DPLL_W``              |  ``DPLL_W``                       |   ``DPLL\<^sub>W``
|Theorem 6                |  ``DPLL_W``                       |   ``wf_dpll\<^sub>W``
|Theorem 7                |  ``DPLL_W``                       |   ``dpll\<^sub>W_conclusive_state_correctness``
|Theorem 8                |  ``DPLL_W``                       |   ``dpll\<^sub>W_dpll\<^sub>N\<^sub>O\<^sub>T``
|``CDCL_W``               |  ``CDCL_W``                       |   ``CDCL\<^sub>W`` [3]
|``cdcl_W+stgy``          |  ``CDCL_W``                       |   ``cdcl<^sub>W_s``
|Theorem 9                |  ``CDCL_W``                       |   ``full_cdcl\<^sub>W_stgy_final_state_conclusive_from_init_state``
|Theorem 10               |  ``CDCL_W_Termination``           |   ``cdcl\<^sub>W_stgy_distinct_mset_clauses``
|``cdcl_W_merge``         |  ``CDCL_W_Merge``                 |   ``cdcl<^sub>W_merge``
|``cdcl_W_merge+stgy``    |  ``CDCL_W_Merge``                 |   ``cdcl<^sub>W_s'``
|``CDCL_W+stgy_restartL`` |  ``CDCL_W_Restart``               |   ``cdcl\<^sub>W_merge_with_restart``
|Equivalence of Sect. 4.4 |  ``CDCL_W_Merge``                 |   ``full_cdcl\<^sub>W_stgy_iff_full_cdcl\<^sub>W_s'``
|``CDCL_W+stgy+incr``     |  ``CDCL_W_Incremental``           |   ``incremental_cdcl\<^sub>W``
|Theorem 11               |  ``CDCL_W_Incremental``           |   ``incremental_conclusive_state``
| Naive implementation    |  ``CDCL_W_Implementation``        |
| Theorem 12              |  ``CDCL_Two_Watched_Literals_Transition_System`` |  ``cdcl_twl_stgy_twl_struct_invs``
|Theorem 13               | ``CDCL_Two_Watched_Literals_Transition_System`` | ``full_cdcl_twl_stgy_cdclW_stgy``
|``propagate_conflict_update_ignore``|``CDCL_Two_Watched_Literals_Algorithm``| ``unit_propagation_inner_loop_body``	
|Theorem 14               | ``CDCL_Two_Watched_Literals_Transition_System`` | ``cdcl_twl_stgy_prog_spec``
|Theorem 15               | ``CDCL_Two_Watched_Literals_List_Watched_Init_Trail_Code`` | ``IsaSAT_code_full_correctness``
|``plarity_list_pair``    | ``CDCL_Two_Watched_Literals_List_Watched_Trail_Code`` | `` polarity``
|``trail_list_pair_trail_ref`` | ``CDCL_Two_Watched_Literals_List_Watched_Trail_Code`` | ``trailt_ref``
|``lit_assn``             |``CDCL_Two_Watched_Literals_List_Watched_Domain``|``unat_lit_assn``
|``trail_list_pair_assn`` | ``CDCL_Two_Watched_Literals_List_Watched_Trail_Code`` | ``trail_conc``
|``polarity_code`` correctness |``CDCL_Two_Watched_Literals_List_Watched_Trail_Code`` | ``polarity_code_valued_refine_code`` [4]

[1] More precisely, the type synonym ``('v, 'mark) ann_lit`` corresponds to what
is defined in the paper. ``('v, 'w, 'mark) annotated_lit`` is slightly more
general: It is not necessarily a literal that is decided or propagated.

[2] the locale is parametrised by the relation ``CDCL\<^sub>N\<^sub>O\<^sub>T``,
even if it no clear from the name.

[3] where ``Jump`` of the paper is named ``Backtrack`` (following Weidenbach's book)

[4] the refinement of the trail contains more information. It for example include the current level of the state.
