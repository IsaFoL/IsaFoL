theory Completeness
  imports
    Correct_Termination
    Termination
    "Functional_Ordered_Resolution_Prover.IsaFoR_Term"
begin

theorem (in scl) completeness_wrt_bound:
  fixes N \<beta> gnd_N gnd_N_lt_\<beta>
  defines
    "gnd_N \<equiv> grounding_of_clss (fset N)" and
    "gnd_N_lt_\<beta> \<equiv> {C \<in> gnd_N. \<forall>L \<in># C. (\<prec>\<^sub>B)\<^sup>=\<^sup>= (atm_of L) \<beta>}"
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


locale compact_scl = scl renaming_vars "(<) :: ('f :: weighted, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool"
  for renaming_vars :: "'v set \<Rightarrow> 'v \<Rightarrow> 'v"
begin

theorem completeness:
  fixes N
  defines "gnd_N \<equiv> grounding_of_clss (fset N)"
  assumes unsat: "\<not> satisfiable gnd_N"
  shows "\<exists>\<beta> S. (regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S \<and>
    (\<nexists>S'. regular_scl N \<beta> S S') \<and>
    (\<exists>\<gamma>. state_conflict S = Some ({#}, \<gamma>))"
proof -
  from unsat obtain gnd_N' where
    "gnd_N' \<subseteq> gnd_N" and "finite gnd_N'" and "\<not> satisfiable gnd_N'"
    using clausal_logic_compact[of gnd_N] by metis

  have "gnd_N' \<noteq> {}"
    using \<open>\<not> satisfiable gnd_N'\<close> by force

  obtain C where C_in: "C \<in> gnd_N'" and C_min: "\<forall>x\<in>gnd_N'. x \<le> C"
    using finite_has_maximal[OF \<open>finite gnd_N'\<close> \<open>gnd_N' \<noteq> {}\<close>] by force

  show ?thesis
  proof (cases C)
    case empty
    let ?S = "([], {||}, Some ({#}, Var))"

    show ?thesis
    proof (intro exI conjI)
      have "{#} |\<in>| N"
        using C_in \<open>gnd_N' \<subseteq> gnd_N\<close>
        unfolding empty gnd_N_def
        by (smt (verit, del_insts) Simple_Clause_Learning.grounding_of_clss_def
            Simple_Clause_Learning.subst_cls_empty_iff UN_E mem_Collect_eq notin_fset subset_iff
            substitution_ops.grounding_of_cls_def)
      hence "conflict N undefined initial_state ?S"
        by (auto intro: conflictI)
      hence "regular_scl N undefined initial_state ?S"
        by simp
      thus "(regular_scl N undefined)\<^sup>*\<^sup>* initial_state ?S"
        by auto
    next
      show "\<nexists>S'. regular_scl N undefined ?S S'"
        using no_more_step_if_conflict_mempty scl_if_regular state_conflict_simp state_trail_simp
        by blast
    next
      show "state_conflict ?S = Some ({#}, Var)"
        by simp
    qed
  next
    case (add x C')
    then obtain L where "L \<in># C" and L_min: "\<forall>x\<in>#C. x \<le> L"
      using Multiset.bex_greatest_element[of C]
      by (metis empty_not_add_mset order_refl totalp_on_le transp_on_le)

    from L_min C_min have "\<forall>D\<in>gnd_N'. \<forall>K\<in>#D. atm_of K \<le> atm_of L"
      by (meson dual_order.trans ex_gt_imp_less_multiset leq_imp_less_eq_atm_of
          verit_comp_simplify1(3))
    hence "gnd_N' \<subseteq> {D \<in> gnd_N. \<forall>K \<in># D. (atm_of K) \<le> (atm_of L)}"
      using \<open>gnd_N' \<subseteq> gnd_N\<close> subset_Collect_iff by auto
    hence "\<not> satisfiable {D \<in> gnd_N. \<forall>K \<in># D. (atm_of K) \<le> (atm_of L)}"
      using \<open>\<not> satisfiable gnd_N'\<close>
      by (meson satisfiable_antimono)
    hence "\<not> satisfiable {D \<in> gnd_N. \<forall>K \<in># D. (<)\<^sup>=\<^sup>= (atm_of K) (atm_of L)}"
      by (smt (verit, best) Collect_cong leI nless_le strict_reflclp_conv sup2I1 sup2I2)
    thus ?thesis
      using completeness_wrt_bound[of N, folded gnd_N_def]
      by blast
  qed
qed

end