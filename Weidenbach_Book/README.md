# Formalization of Weidenbach's _Automated Reasoning―The Art of Generic Problem Solving_ #

[This directory](https://bitbucket.org/isafol/isafol/src/master/Weidenbach_Book/) contains an ongoing Isabelle formalization of Christoph Weidenbach's forthcoming book _Automated Reasoning―The Art of Generic Problem Solving_.
The relevant part of the book can be found [online](http://people.mpi-inf.mpg.de/~mfleury/paper/Weidenback_Book_CDCL.pdf).


## Organisation of the Development ##

* The branch [master](https://bitbucket.org/isafol/isafol/src/master/Weidenbach_Book/) contains the latest development and is based on Isabelle version 2018.
* The branch [IJCAR2016](https://bitbucket.org/isafol/isafol/src/IJCAR2016/Weidenbach_Book/) contains the version of the development related to the paper. Please refer to [this page](https://bitbucket.org/isafol/isafol/src/IJCAR2016/Weidenbach_Book/Readme.md).


## Documentation ##

A recent version of the documentation the theory files is also available [online](http://people.mpi-inf.mpg.de/~mfleury/IsaFoL/current/Weidenbach_Book).


## Authors ##

* [Mathias Fleury](mailto:mathias.fleury shtrudel mpi-inf.mpg.de)
* [Jasmin Christian Blanchette](mailto:j.c.blanchette shtrudel vu.nl>)
* [Peter Lammich](mailto:lammich shtrudel in.tum.de)


## Additional Collaborators ##

* [Dmitriy Traytel](mailto:traytel shtrudel inf.ethz.ch)
* [Christoph Weidenbach](mailto:weidenbach shtrudel mpi-inf.mpg.de)


## Publications ##

* [A verified SAT solver with watched literals using Imperative HOL](http://matryoshka.gforge.inria.fr/pubs/sat_2wl_paper.pdf).
  M. Fleury, J. C. Blanchette, and P. Lammich.
  In Andronick, J., Felty, A. (eds.) 7th ACM SIGPLAN International Conference on Certified Programs and Proofs (CPP 2018).

* [A verified SAT solver framework with learn, forget, restart, and incrementality](http://matryoshka.gforge.inria.fr/pubs/sat_sister.pdf)
  J. C. Blanchette, M. Fleury, and C. Weidenbach.
  In Sierra, C. (ed.) 26th International Joint Conference on Artificial Intelligence (IJCAI-17), pp. 4786–4790, ijcai.org, 2017.

* [A verified SAT solver framework with learn, forget, restart, and incrementality](http://people.mpi-inf.mpg.de/~jblanche/sat.pdf).
  J. C. Blanchette, M. Fleury, and C. Weidenbach.
  In Olivetti, N., Tiwari, A. (eds.) 8th International Joint Conference on Automated Reasoning (IJCAR 2016), LNCS, Springer, 2016.

* [Formalisation of Ground Inference Systems in a Proof Assistant](http://www.mpi-inf.mpg.de/fileadmin/inf/rg1/Documents/fleury_master_thesis.pdf).
  M. Fleury.
  M.Sc. thesis, École normale supérieure Rennes, 2015.


## Execution of the Formalisation ##

* Please install [Isabelle2018](http://isabelle.in.tum.de).
* Install the [Archive of Formal proofs](https://www.isa-afp.org/using.html) as mentioned.
* To process all the theory files, clone the repository and load ``IsaSAT.thy``, using
   ``/path/to/isabelle jedit -d . -l CDCL IsaSAT.thy``
   (``-d .`` ensures that Isabelle knows about the sessions of this formalisation, and ``-l CDCL`` means that we build the formalisation on top of CDCL).
  The whole compilation will take around 30 minutes.


## The SAT solver IsaSAT ##

The code of the SAT solver is in the ``code`` folder. To run it:
  * download [MLton](http://mlton.org);
  * compile IsaSAT with ``make`` or ``make MLTON=/path/to/mlton`` (if MLton is not in the $PATH);
  * run the solver with ``./IsaSAT <cnf-file>``. Use the options "--model" to output the model (if the clauses are statifiable)
    and "--stat" to print some statistics on the run.


## Names Correspondance and Publications

### A Verified SAT Solver Framework including Optimization and Partial Valuations ###

Version: commit 05aba9aa532589f4313009626dca346babc5a16c

| Paper                   | Theory file                      | Isabelle name                                                             |
|-------------------------|----------------------------------|---------------------------------------------------------------------------|
| Lemma 2                 | ``CDCL_W_Optimal_Model``         | ``wf_cdcl_bnb2``   (termination) and                                      |
|                         |                                  | ``full_cdcl_bnb_stgy_no_conflicting_clss_unsat``                          |
| Theorem 3               | ``CDCL_W_Optimal_Model``         | ``full_cdcl_bnb_stgy_no_conflicting_clause_from_init_state``              |
| Lemma 4                 | ``CDCL_W_Optimal_Model``         | Directly formalized with Improve+                                         |
| ``interpretation CDCL`` | ``CDCL_W_Abstract_State``        | the interpreatation are named ``cdcl\<^sub>W_restart_mset``               |
| is_improving            | ``CDCL_W_Optimal_Model``         | ``definition is_improving_int`` (line 2176)                               |
| T_N(O)                  | ``CDCL_W_Optimal_Model``         | ``definition conflicting_clauses`` (line 2198)                            |
| Isabelle Lemma 5        | ``CDCL_W_Optimal_Model``         | ``entails_conflicting_clauses_if_le``                                     |
| ``penc``                | ``CDCL_W_Partial_Encoding``      | ``penc``                                                                  |
| Lemma 6                 | ``CDCL_W_Partial_Encoding``      | ``penc_ent_upostp``  and ``penc_ent_postp``                               |
| Lemma 7                 | ``CDCL_W_Partial_Encoding``      | ``full_encoding_OCDCL_correctness``                                       |
| Lemma 8                 | ``CDCL_W_Partial_Encoding``      | Inlined in the proof of ``no_step_cdcl_bnb_r_stgy_no_step_cdcl_bnb_stgy`` |
| Lemma 9 (ongoing)       | ``CDCL_W_Partial_Optimal_Model`` | ongoing                                                                          |

### A Verified SAT Solver with Watched Literals Using Imperative HOL CPP 18 ###

Version: commit 678b79ae5e865b9cc21081adb091e5baaa802c0b

|Paper                       |  Theory file                                |   Isabelle name
|----------------------------|---------------------------------------------|---------------------------------------------------------------------
|``'v lit``                  |   ``../lib/Clausal_Logic``                  |  ``'a literal``
|``CDCL_W``                  |  ``CDCL_W``                                 |   ``CDCL\<^sub>W``
|``cdcl_W+stgy``             |  ``CDCL_W``                                 |   ``cdcl<^sub>W_s``
|Theorem 2.1                 |  ``CDCL_W``                                 | ``full_cdcl\<^sub>W_stgy_final_state_conclusive_from_init_state``
|Theorem 3.1                 |  ``Watched_Literals_Transition_System`` | ``cdcl_twl_stgy_twl_struct_invs``
|Theorem 3.2                 | ``Watched_Literals_Transition_System``  | ``full_cdcl_twl_stgy_cdclW_stgy``
|``PCUI_algo``               | ``Watched_Literals_Algorithm``          | ``unit_propagation_inner_loop_body``
|Theorem 4.2                 | ``Watched_Literals_Transition_System``  | ``cdcl_twl_stgy_prog_spec``
|``PCUI_list``               | ``Watched_Literals_List``               |  ``unit_propagation_inner_loop_body_l``
|``PCUI_wlist``              | ``Watched_Literals_Watch_List``         | ``unit_propagation_inner_loop_body_wl``
|Theorem 7.1                 | ``IsaSAT``                                  | ``IsaSAT_code_full_correctness``
| VMTF                       | ``Watched_Literals_VMTF``               |  ``l_vmtf``
|``find_next_undef``         | ``Watched_Literals_VMTF``               |  ``find_next_undef``
|``conflict_is_empty_lookup``| ``IsaSAT_Lookup_Conflict``                  | ``conflict_assn_is_empty``


### A Verified SAT Solver Framework with Learn, Forget, Restart, and Incrementality ###

Version: commit 678b79ae5e865b9cc21081adb091e5baaa802c0b

|Paper                                |  Theory file                                |   Isabelle name
|-------------------------------------|---------------------------------------------|---------------------------------------------------------------------
|'v literal                           |   ``../lib/Clausal_Logic``                  |  ``'a literal``
|``('v, cls) ann_literal``            |  ``Partial_Annotated_Clausal_Logic``        | ``('v, 'w, 'mark) annotated_lit``  [1]
|``DPLL_NOT+BJ``                      |  ``CDCL_NOT``                               | ``dpll_bj``
|Theorem 1                            |  ``CDCL_NOT``                               |   ``wf_dpll_bj``
|Theorem 2                            |  ``CDCL_NOT``                               |   ``full_dpll_backjump_final_state_from_init_state``
|Lemma 3                              |  ``DPLL_NOT``                               |   ``backtrack_is_backjump``
|Theorem 4                            |  ``DPLL_NOT``                               |   ``dpll_conclusive_state_correctness``
|``cdcl_NOT``                         |  ``CDCL_NOT``                               |   ``CDCL\<^sub>N\<^sub>O\<^sub>T``
|Theorem 5                            |  ``CDCL_NOT``                               |   ``wf_cdcl\<^sub>N\<^sub>O\<^sub>T_no_learn_and_forget_infinite_chain``
| ``restartT``                        |  ``CDCL_NOT``                               |   ``CDCL\<^sub>N\<^sub>O\<^sub>T_raw_restart`` [2]
| ``DPLL_W``                          |  ``DPLL_W``                                 |   ``DPLL\<^sub>W``
|Theorem 6                            |  ``DPLL_W``                                 |   ``wf_dpll\<^sub>W``
|Theorem 7                            |  ``DPLL_W``                                 |   ``dpll\<^sub>W_conclusive_state_correctness``
|Theorem 8                            |  ``DPLL_W``                                 |   ``dpll\<^sub>W_dpll\<^sub>N\<^sub>O\<^sub>T``
|``CDCL_W``                           |  ``CDCL_W``                                 |   ``CDCL\<^sub>W`` [3]
|``cdcl_W+stgy``                      |  ``CDCL_W``                                 |   ``cdcl\<^sub>W_s``
|Theorem 9                            |  ``CDCL_W``                                 |   ``full_cdcl\<^sub>W_stgy_final_state_conclusive_from_init_state``
|Theorem 10                           |  ``CDCL_W_Termination``                     |   ``cdcl\<^sub>W_stgy_distinct_mset_clauses``
|``cdcl_W_merge``                     |  ``CDCL_W_Merge``                           |   ``cdcl<^sub>W_merge``
|``cdcl_W_merge+stgy``                |  ``CDCL_W_Merge``                           |   ``cdcl<^sub>W_s'``
|``CDCL_W+stgy_restartL``             |  ``CDCL_W_Restart``                         |   ``cdcl\<^sub>W_merge_with_restart``
|Equivalence of Sect. 4.4             |  ``CDCL_W_Merge``                           |   ``full_cdcl\<^sub>W_stgy_iff_full_cdcl\<^sub>W_s'``
|``CDCL_W+stgy+incr``                 |  ``CDCL_W_Incremental``                     |   ``incremental_cdcl\<^sub>W``
|Theorem 11                           |  ``CDCL_W_Incremental``                     |   ``incremental_conclusive_state``
| Naive implementation                |  ``CDCL_W_Implementation``                  |
| Theorem 12                          |  ``Watched_Literals_Transition_System`` |  ``cdcl_twl_stgy_twl_struct_invs``
|Theorem 13                           |  ``Watched_Literals_Transition_System`` | ``full_cdcl_twl_stgy_cdclW_stgy``
|``propagate_conflict_update_ignore`` |  ``Watched_Literals_Algorithm``         | ``unit_propagation_inner_loop_body``
|Theorem 14                           |  ``Watched_Literals_Transition_System`` | ``cdcl_twl_stgy_prog_spec``
|Theorem 15                           |  ``IsaSAT``                                 | ``IsaSAT_code_full_correctness``
|``polarity_list_pair``               |  ``IsaSAT_Trail``                           | `` polarity_pol``
|``trail_list_pair_trail_ref``        |  ``IsaSAT_Trail``                           | ``trail_pol``
|``lit_assn``                         |  ``Watched_Literals_Watch_List_Domain`` |``unat_lit_assn``
|``trail_list_pair_assn``             |  ``IsaSAT_Trail``                           | ``trail_pol_assn``
|``polarity_code`` correctness        |  ``IsaSAT_Trail``                           | ``polarity_pol_code_polarity_refine_code`` [4]

[1] More precisely, the type synonym ``('v, 'mark) ann_lit`` corresponds to what
is defined in the paper. ``('v, 'w, 'mark) annotated_lit`` is slightly more
general: It is not necessarily a literal that is decided or propagated.

[2] the locale is parametrised by the relation ``CDCL\<^sub>N\<^sub>O\<^sub>T``,
even if it no clear from the name.

[3] where ``Jump`` of the paper is named ``Backtrack`` (following Weidenbach's book)

[4] the refinement of the trail contains more information. It for example include the current level of the state.
