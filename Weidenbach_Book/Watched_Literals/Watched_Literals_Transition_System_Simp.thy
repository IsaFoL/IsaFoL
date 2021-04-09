theory Watched_Literals_Transition_System_Simp
imports
  Watched_Literals_Transition_System_Reduce
  Watched_Literals_Transition_System_Restart
begin


context twl_restart
begin

theorem wf_cdcl_twl_stgy_restart:
  \<open>wf {(T, S :: 'v twl_st_restart). twl_restart_inv S \<and> cdcl_twl_stgy_restart S T}\<close> (is \<open>wf ?S\<close>)
proof -
  have \<open>?S \<subseteq>
    {((S', T', U', m', n', g'), (S, T, U, m, n, g)).
        pcdcl_stgy_restart_inv (pstate\<^sub>W_of S, pstate\<^sub>W_of T, pstate\<^sub>W_of U, m, n, g) \<and>
        pcdcl_stgy_restart (pstate\<^sub>W_of S, pstate\<^sub>W_of T, pstate\<^sub>W_of U, m, n, g)
           (pstate\<^sub>W_of S', pstate\<^sub>W_of T', pstate\<^sub>W_of U', m', n', g')} \<union>
    {((S', T', U', m', n', g'), (S, T, U, m, n, g)).
        pcdcl_stgy_restart_inv (pstate\<^sub>W_of S, pstate\<^sub>W_of T, pstate\<^sub>W_of U, m, n, g) \<and>
        S = S' \<and> T = T' \<and> m = m' \<and> n = n' \<and> g = g' \<and>
      pstate\<^sub>W_of U = pstate\<^sub>W_of U' \<and> (literals_to_update_measure U', literals_to_update_measure U)
      \<in> lexn less_than 2}\<close> (is \<open>_ \<subseteq> ?A \<union> ?B\<close>)
    by (auto dest!: cdcl_twl_stgy_cdcl\<^sub>W_stgy_restart2 simp: twl_restart_inv_def)
  moreover have \<open>wf (?A \<union> ?B)\<close>
    apply (rule wf_union_compatible)
    subgoal
      by (rule wf_subset[OF wf_if_measure_f[OF wf_pcdcl_twl_stgy_restart],
        of _ \<open>\<lambda>(S, T, U, m, g). (pstate\<^sub>W_of S, pstate\<^sub>W_of T, pstate\<^sub>W_of U, m, g)\<close>]) auto
    subgoal
      by (rule wf_subset[OF wf_if_measure_f[OF ],
        of \<open>(lexn less_than 2)\<close>  _ \<open>\<lambda>(S, T, U, m, g). literals_to_update_measure (U)\<close>])
        (auto intro!: wf_lexn)
    subgoal
      by auto
    done
  ultimately show ?thesis
    by (blast intro: wf_subset)
qed

end


context twl_restart_ops
begin

lemma cdcl_twl_stgy_size_get_all_learned:
  \<open>cdcl_twl_stgy S T \<Longrightarrow> size (get_all_learned_clss S) \<le> size (get_all_learned_clss T)\<close>
  by (induction rule: cdcl_twl_stgy.induct)
   (auto simp: cdcl_twl_cp.simps cdcl_twl_o.simps update_clauses.simps
    dest: multi_member_split)

lemma rtranclp_cdcl_twl_stgy_size_get_all_learned:
  \<open>cdcl_twl_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> size (get_all_learned_clss S) \<le> size (get_all_learned_clss T)\<close>
  by (induction rule: rtranclp_induct)
    (auto dest!: cdcl_twl_stgy_size_get_all_learned)

(*TODO Move*)
lemma (in -) wf_trancl_iff: \<open>wf (r\<^sup>+) \<longleftrightarrow> wf r\<close>
  by (auto intro!: wf_subset[of \<open>r\<^sup>+\<close> r] simp: wf_trancl)

lemma (in -) tranclp_inv_tranclp:
  assumes \<open>\<And>S T. R S T \<Longrightarrow> P S \<Longrightarrow> P T\<close>
  shows
    \<open>{(T, S). R S T \<and> P S}\<^sup>+ = {(T, S). R\<^sup>+\<^sup>+ S T \<and> P S}\<close>
proof -
  have H: \<open>R\<^sup>+\<^sup>+ S T \<Longrightarrow> P S \<Longrightarrow> P T\<close> for S T
    by (induction rule: tranclp_induct)
      (auto dest: assms)
  show ?thesis
    apply (rule; rule; clarify)
    unfolding mem_Collect_eq in_pair_collect_simp
    subgoal for a b
      by (induction rule: trancl_induct) auto
    subgoal for b x
      apply (induction rule: tranclp_induct)
      subgoal for b
        by auto
      subgoal for e f
        by (rule trancl_into_trancl2[of f e])
          (use H[of x e] in auto)
      done
    done
qed

definition partial_conclusive_TWL_run :: \<open>'v twl_st \<Rightarrow> (bool \<times> 'v twl_st) nres\<close> where
  \<open>partial_conclusive_TWL_run S = SPEC(\<lambda>(b, T). \<exists>R1 R2 m m\<^sub>0 n\<^sub>0.
       cdcl_twl_stgy_restart\<^sup>*\<^sup>* (S, S, S, m\<^sub>0, n\<^sub>0, True) (R1, R2, T, m) \<and> (\<not>b \<longrightarrow> final_twl_state T))\<close>

definition partial_conclusive_TWL_run2
  :: \<open>nat \<Rightarrow> nat \<Rightarrow> 'v twl_st \<Rightarrow> 'v twl_st \<Rightarrow> 'v twl_st \<Rightarrow> (bool \<times> 'v twl_st) nres\<close>
where
  \<open>partial_conclusive_TWL_run2  m\<^sub>0 n\<^sub>0 S\<^sub>0 T\<^sub>0 U\<^sub>0 = SPEC(\<lambda>(b, T). \<exists>R1 R2 m.
       cdcl_twl_stgy_restart\<^sup>*\<^sup>* (S\<^sub>0, T\<^sub>0, U\<^sub>0, m\<^sub>0, n\<^sub>0, True) (R1, R2, T, m) \<and> (\<not>b \<longrightarrow> final_twl_state T))\<close>

definition conclusive_TWL_run :: \<open>'v twl_st \<Rightarrow> 'v twl_st nres\<close> where
  \<open>conclusive_TWL_run S = SPEC(\<lambda>T. (\<exists>R1 R2 m m\<^sub>0 n\<^sub>0.
       cdcl_twl_stgy_restart\<^sup>*\<^sup>* (S, S, S, m\<^sub>0, n\<^sub>0, True) (R1, R2, T, m) \<and> final_twl_state T))\<close>

definition conclusive_TWL_run2 :: \<open>nat \<Rightarrow> nat \<Rightarrow> 'v twl_st \<Rightarrow> 'v twl_st \<Rightarrow> 'v twl_st \<Rightarrow> 'v twl_st nres\<close> where
  \<open>conclusive_TWL_run2 m\<^sub>0 n\<^sub>0 S\<^sub>0 T\<^sub>0 U\<^sub>0 = SPEC(\<lambda>T. (\<exists>R1 R2 m.
       cdcl_twl_stgy_restart\<^sup>*\<^sup>* (S\<^sub>0, T\<^sub>0, U\<^sub>0, m\<^sub>0, n\<^sub>0, True) (R1, R2, T, m) \<and> final_twl_state T))\<close>
end

end