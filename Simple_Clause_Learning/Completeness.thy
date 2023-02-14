theory Completeness
  imports
    Correct_Termination
    Termination
begin

theorem (in scl) completeness_wrt_bound:
  fixes N \<beta> gnd_N gnd_N_lt_\<beta>
  defines
    "gnd_N \<equiv> grounding_of_clss (fset N)" and
    "gnd_N_lt_\<beta> \<equiv> {C \<in> gnd_N. \<forall>L \<in># C. atm_of L \<prec>\<^sub>B \<beta>}"
  assumes unsat: "\<not> satisfiable gnd_N_lt_\<beta>"
  shows "\<exists>S. (regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S \<and>
    (\<nexists>S'. regular_scl N \<beta> S S') \<and>
    (\<exists>\<gamma>. state_conflict S = Some ({#}, \<gamma>))"
proof -
  obtain S where
    run: "(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S" and
    no_more_step: "(\<nexists>S'. regular_scl N \<beta> S S')"
    using regular_scl_terminates[THEN ex_trans_min_element_if_wfp_on, of initial_state]
    by (metis (no_types, opaque_lifting) conversep_iff mem_Collect_eq rtranclp.rtrancl_into_rtrancl
        rtranclp.rtrancl_refl)
  
  moreover have "\<exists>\<gamma>. state_conflict S = Some ({#}, \<gamma>)"
    using unsat correct_termination_regular_scl_run[OF run no_more_step]
    by (simp add: gnd_N_lt_\<beta>_def gnd_N_def)

  ultimately show ?thesis
    by metis
qed

end