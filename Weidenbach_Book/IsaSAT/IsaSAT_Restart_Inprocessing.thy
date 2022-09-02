(*TODO Rename to IsaSAT_Inprocessing*)
theory IsaSAT_Restart_Inprocessing
  imports IsaSAT_Setup
   IsaSAT_Simplify_Units
    Watched_Literals.Watched_Literals_Watch_List_Inprocessing
    More_Refinement_Libs.WB_More_Refinement_Loops
    IsaSAT_Restart
    IsaSAT_Simplify_Binaries
    IsaSAT_Simplify_Pure_Literals
    IsaSAT_Simplify_Forward_Subsumption
begin

definition isa_pure_literal_elimination_round_wl where
  \<open>isa_pure_literal_elimination_round_wl S\<^sub>0 = do {
    ASSERT (isa_pure_literal_elimination_round_wl_pre S\<^sub>0);
    S \<leftarrow> isa_simplify_clauses_with_units_st_wl2 S\<^sub>0;
    ASSERT (length (get_clauses_wl_heur S) = length (get_clauses_wl_heur S\<^sub>0));
    ASSERT (learned_clss_count S \<le> learned_clss_count S\<^sub>0);
    if get_conflict_wl_is_None_heur S
    then do {
     (abort, occs) \<leftarrow> isa_pure_literal_count_occs_wl S;
      if \<not>abort then isa_pure_literal_deletion_wl occs S
      else RETURN (0, S)}
    else RETURN (0, S)
}\<close>

lemma isa_simplify_clauses_with_unit_st2_isa_simplify_clauses_with_unit_wl:
  assumes \<open>(S,S') \<in> twl_st_heur_restart_ana' r u\<close>
  shows
    \<open>isa_simplify_clauses_with_units_st_wl2 S \<le> \<Down> (twl_st_heur_restart_ana' r u) (simplify_clauses_with_units_st_wl S')\<close>
  apply (rule order_trans)
    defer
  apply (rule ref_two_step')
  apply (rule simplify_clauses_with_units_st_wl2_simplify_clauses_with_units_st_wl[unfolded Down_id_eq, of _ S'])
  subgoal by auto
  subgoal
    apply (rule isa_simplify_clauses_with_units_st2_simplify_clauses_with_units_st2[THEN order_trans, of _ S'])
    apply (rule assms)
    subgoal using assms by auto
    done
  done


lemma isa_pure_literal_elimination_round_wl_pure_literal_elimination_round_wl:
  assumes S\<^sub>0T: \<open>(S\<^sub>0, T) \<in> twl_st_heur_restart_ana' r u\<close>
  shows \<open>isa_pure_literal_elimination_round_wl S\<^sub>0 \<le>\<Down>{((_, U), V). (U,V)\<in>twl_st_heur_restart_ana' r u} (pure_literal_elimination_round_wl T)\<close>
proof -
  show ?thesis
    unfolding isa_pure_literal_elimination_round_wl_def pure_literal_elimination_round_wl_def
    apply (refine_rcg isa_pure_literal_deletion_wl_pure_literal_deletion_wl[where r=r and u=\<open>learned_clss_count S\<^sub>0\<close>]
      isa_pure_literal_count_occs_wl_pure_literal_count_occs_wl[where r=r and u=\<open>learned_clss_count S\<^sub>0\<close>]
      isa_simplify_clauses_with_unit_st2_isa_simplify_clauses_with_unit_wl[where r=r and u=\<open>learned_clss_count S\<^sub>0\<close>])
    subgoal using assms unfolding isa_pure_literal_elimination_round_wl_pre_def by fast
    subgoal using assms by (auto simp: twl_st_heur_restart_ana_def)
    subgoal using assms by (auto simp: twl_st_heur_restart_ana_def)
    subgoal using assms by (auto simp: twl_st_heur_restart_ana_def)
    subgoal
      by (subst get_conflict_wl_is_None_heur_get_conflict_wl_is_None_ana[THEN fref_to_Down_unRET_Id])
        (use assms in \<open>auto simp: get_conflict_wl_is_None_def\<close>)
    subgoal by auto
    apply (rule order_trans[OF ])
    apply (rule isa_pure_literal_deletion_wl_pure_literal_deletion_wl[where r=r and u=\<open>learned_clss_count S\<^sub>0\<close>])
    prefer 3
    apply (rule conc_fun_R_mono)
    subgoal using assms by auto
    subgoal by auto
    subgoal by auto
    subgoal using assms by auto
    subgoal using assms by auto
    done
qed


definition isa_pure_literal_elimination_wl_pre :: \<open>_\<close> where
  \<open>isa_pure_literal_elimination_wl_pre S = (\<exists>T u r.
    (S, T) \<in> twl_st_heur_restart_ana' r u \<and> pure_literal_elimination_wl_pre T)\<close>

definition isa_pure_literal_elimination_wl_inv :: \<open>_\<close> where
  \<open>isa_pure_literal_elimination_wl_inv S max_rounds = (\<lambda>(T,m,abort). \<exists>S' T' u r.
  (S, S') \<in> twl_st_heur_restart_ana' r u \<and>
  (T, T') \<in> twl_st_heur_restart_ana' r u \<and> pure_literal_elimination_wl_inv S' max_rounds (T', m, abort))\<close>

definition isa_pure_literal_elimination_wl :: \<open>isasat \<Rightarrow> isasat nres\<close> where
  \<open>isa_pure_literal_elimination_wl S\<^sub>0 = do {
    ASSERT (isa_pure_literal_elimination_wl_pre S\<^sub>0);
     max_rounds \<leftarrow> RETURN (3::nat);
    (S, _, _) \<leftarrow> WHILE\<^sub>T\<^bsup>isa_pure_literal_elimination_wl_inv S\<^sub>0 max_rounds\<^esup> (\<lambda>(S, m, abort). m < max_rounds \<and> \<not>abort)
     (\<lambda>(S, m, abort). do {
         ASSERT (m \<le> max_rounds);
         ASSERT (length (get_clauses_wl_heur S) = length (get_clauses_wl_heur S\<^sub>0));
         ASSERT (learned_clss_count S \<le> learned_clss_count S\<^sub>0);
         (elim, S) \<leftarrow> isa_pure_literal_elimination_round_wl S;
         abort \<leftarrow> RETURN (elim > 0);
         RETURN (S, m+1, abort)
       })
    (S\<^sub>0, 0, False);
   RETURN S
  }\<close>


lemma isa_pure_literal_elimination_wl_pure_literal_elimination_wl:
  assumes \<open>(S, S') \<in> twl_st_heur_restart_ana' r u\<close>
  shows \<open>isa_pure_literal_elimination_wl S \<le>\<Down>(twl_st_heur_restart_ana' r u) (pure_literal_elimination_wl S')\<close>
proof -
  have [refine]: \<open>RETURN (3::nat) \<le> \<Down> {(a,b). a = b} (RES UNIV)\<close>
    \<open>RETURN (0 < x1d) \<le> \<Down> bool_rel (RES UNIV)\<close> for x1d
    by (auto simp: RETURN_RES_refine)
  have [refine]: \<open>((S, 0, False), S', 0, False) \<in> twl_st_heur_restart_ana' r (learned_clss_count S) \<times>\<^sub>r Id \<times>\<^sub>r Id\<close>
    using assms by auto
  show ?thesis
    unfolding isa_pure_literal_elimination_wl_def pure_literal_elimination_wl_def
    apply (refine_vcg isa_pure_literal_elimination_round_wl_pure_literal_elimination_round_wl[where r=r and u=\<open>learned_clss_count S\<close>])
    subgoal using assms unfolding isa_pure_literal_elimination_wl_pre_def by fast
    subgoal for max_rounds max_roundsa x x'
      using assms unfolding isa_pure_literal_elimination_wl_inv_def case_prod_beta prod_rel_fst_snd_iff
      by (rule_tac x=S' in exI, rule_tac x=\<open>fst x'\<close> in exI) auto
    subgoal by auto
    subgoal by auto
    subgoal using assms by (auto simp: twl_st_heur_restart_ana_def)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal using assms by auto
    done
qed

end
