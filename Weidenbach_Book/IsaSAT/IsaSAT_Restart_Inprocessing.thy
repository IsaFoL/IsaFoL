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
    IsaSAT_Restart_Inprocessing_Defs
begin

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

lemma isa_pure_literal_eliminate:
  assumes \<open>(S, S') \<in> twl_st_heur_restart_ana' r u\<close>
  shows \<open>isa_pure_literal_eliminate S \<le>\<Down>(twl_st_heur_restart_ana' r u) (pure_literal_eliminate_wl S')\<close>
proof -
  have [refine]: \<open>RETURN (should_inprocess_st S) ≤ ⇓ bool_rel (pure_literal_eliminate_wl_needed S')\<close>
    unfolding pure_literal_eliminate_wl_needed_def by auto
  show ?thesis
    unfolding isa_pure_literal_eliminate_def pure_literal_eliminate_wl_def
    by (refine_vcg isa_pure_literal_elimination_wl_pure_literal_elimination_wl)
     (use assms in auto)
qed

end
