theory CDCL_W_Incremental_Basic
  imports CDCL_W_Implementation
       "HOL-Library.Code_Target_Numeral"
begin

subsection \<open>List-based CDCL Clause Addition Function\<close>

text \<open>What follows is a very simple way to add clauses prior to, or after a run of the
      CDCL procedure. The function is basic in the sense that it neglects several optimizations
      to provide an easy to implement, easy to use interface in which clauses can gradually be
      introduced. The tradeoff here was made to accomodate the desired functionality while having
      to inflict zero changes to any other file, most notably @{file CDCL_W.thy} and 
      @{file CDCL_W_Implementation.thy}.\<close>
                                         
subsubsection \<open>The function\<close>

text\<open>There are several design choices here related to the tradeoff:

  1. Learned clauses are moved into the set of irredundant clauses, together with the clauses to add
  2. The conflict position D is reset back to None

This is to fulfill the reachability invariant of the \<^verbatim>\<open>cdcl\<^sub>W_restart_state_inv_from_init_state\<close> 
typedef. Moving U is not an issue, as these are redundant clauses and the basic solver never
utilizes the forget rule. Resetting the conflict should not be an issue, as a user is able to
query the result after each run, before deciding to add more new clauses. Rediscovering unsat will
eventually likely also happen through propagations, which makes it not that inefficient.\<close>
fun cdcl\<^sub>W_add_clauses :: \<open>'v cdcl\<^sub>W_restart_state_inv_st \<Rightarrow> 'v literal list list \<Rightarrow> 'v cdcl\<^sub>W_restart_state_inv_st\<close> where
  \<open>cdcl\<^sub>W_add_clauses (M, N, U, D) clss = ([], N @ U @ map remdups clss, [], None)\<close>

definition cdcl\<^sub>W_add_clauses_nat :: \<open>nat cdcl\<^sub>W_restart_state_inv_from_init_state 
                           \<Rightarrow> nat literal list list 
                           \<Rightarrow> nat cdcl\<^sub>W_restart_state_inv_from_init_state\<close> where
  \<open>cdcl\<^sub>W_add_clauses_nat S clss = state_from_init_state_of (cdcl\<^sub>W_add_clauses (rough_state_from_init_state_of S) clss)\<close>

paragraph \<open>Lemmas for code generation\<close>
lemma cdcl\<^sub>W_add_clauses_preserves_all_struct_inv:
  assumes \<open>cdcl\<^sub>W_all_struct_inv (toS S)\<close>
  shows \<open>cdcl\<^sub>W_all_struct_inv (toS (cdcl\<^sub>W_add_clauses S clss))\<close>
  using assms unfolding cdcl\<^sub>W_all_struct_inv_def
  by (cases S; auto simp: no_strange_atm_def 
                          distinct_cdcl\<^sub>W_state_def 
                          distinct_mset_set_def)

lemma add_clauses_code[code abstract]:
  \<open>rough_state_from_init_state_of (cdcl\<^sub>W_add_clauses_nat S clss) 
    = cdcl\<^sub>W_add_clauses (rough_state_from_init_state_of S) clss\<close>
  unfolding cdcl\<^sub>W_add_clauses_nat_def
  apply (rule state_from_init_state_of_inverse; auto)
  subgoal
  proof (cases \<open>(rough_state_from_init_state_of S)\<close>)
    have inv: \<open>cdcl\<^sub>W_all_struct_inv (toS (rough_state_from_init_state_of S))\<close>
      using rough_state_from_init_state_of[of \<open>S\<close>] by auto
    then show ?thesis 
      using cdcl\<^sub>W_add_clauses_preserves_all_struct_inv[of \<open>(rough_state_from_init_state_of S)\<close>] 
      by auto
  qed
  subgoal
    by (cases \<open>(rough_state_from_init_state_of S)\<close>) auto
  done

subsubsection \<open>Correctness Theorem\<close>

lemma remdups_eq: \<open>(\<forall>ys \<in> set xs. distinct ys) \<Longrightarrow> xs = map remdups xs\<close>
  by (simp add: map_idI)

lemma unsatisfiable_remove_entailed: 
  \<open>unsatisfiable (A \<union> B \<union> C) \<Longrightarrow> A \<Turnstile>ps B \<Longrightarrow> unsatisfiable (A \<union> C)\<close>
  unfolding satisfiable_def true_clss_clss_def apply auto
  by (metis total_over_m_consistent_extension total_over_m_union true_clss_union_increase) 

text \<open>Performing a run after adding clauses should give us a SAT / UNSAT result about the original
      clauses plus the newly added ones\<close>
theorem DPLL_tot_correct_inc:
  assumes
    A1: \<open>rough_state_from_init_state_of S = (M0, N0, U0, D0)\<close> and
    A2: \<open>rough_state_from_init_state_of (do_all_cdcl\<^sub>W_stgy (cdcl\<^sub>W_add_clauses_nat S clss)) = T\<close> and
    A3: \<open>(M1, N1, U1, D1) = toS T\<close>
  shows \<open>(D1 \<noteq> Some {#} \<and> satisfiable (set (map mset N0) \<union> set (map mset clss))) 
            \<or> (D1 = Some {#} \<and> (unsatisfiable (set (map mset N0) \<union> set (map mset clss))))\<close>
proof -
  have \<open>cdcl\<^sub>W_all_struct_inv (toS (rough_state_from_init_state_of S))\<close>
    using rough_state_from_init_state_of rough_state_of by auto
  then have H1: \<open>(\<forall>ys \<in> set N0. distinct ys) \<and> (\<forall>ys \<in> set U0. distinct ys) \<and> (\<forall>ys \<in> set (map remdups clss). distinct ys)\<close>
    using A1 by (auto simp: cdcl\<^sub>W_all_struct_inv_def distinct_cdcl\<^sub>W_state_def distinct_mset_set_def)
  obtain M' N' U' D' where 
    H2: \<open>(M', N', U', D') = rough_state_from_init_state_of (cdcl\<^sub>W_add_clauses_nat S clss)\<close> and
    H3: \<open>M' = [] \<and> N' = N0 @ U0 @ map remdups clss \<and> U' = [] \<and> D' = None\<close>                   
    using A1 add_clauses_code by (cases \<open>rough_state_from_init_state_of (cdcl\<^sub>W_add_clauses_nat S clss)\<close>) auto
  have H4: \<open>(set (map mset N')) = (set (map mset N0)) \<union> (set (map mset U0)) \<union> (set (map mset (map remdups clss)))\<close> 
    using H3 by auto
  have sat_preserve: \<open>satisfiable (set (map mset N')) \<Longrightarrow> satisfiable (set (map mset N0) \<union> set (map mset clss))\<close>
    by (metis (no_types, lifting) H4 list.map_comp list.set_map satisfiable_carac true_clss_union
        true_raw_init_clss_remdups) 
  have reach_restart: \<open>cdcl\<^sub>W_restart\<^sup>*\<^sup>* (S0_cdcl\<^sub>W_restart (raw_init_clss (toS (rough_state_from_init_state_of S)))) (toS (rough_state_from_init_state_of S))\<close>
    using rough_state_from_init_state_of[of S] rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W_restart by blast
  have learned_is_entailed: \<open>cdcl\<^sub>W_learned_clauses_entailed_by_init (toS (rough_state_from_init_state_of S))\<close>
    using rtranclp_cdcl\<^sub>W_learned_clauses_entailed[OF reach_restart] by auto
  then have \<open>set (map mset N0) \<Turnstile>ps set (map mset U0)\<close>
    using A1 by (auto simp: cdcl\<^sub>W_learned_clauses_entailed_by_init_def)
  then have unsat_preserve: \<open>unsatisfiable (set (map mset N')) \<Longrightarrow> unsatisfiable (set (map mset N0) \<union> set (map mset clss))\<close>
    using unsatisfiable_remove_entailed[of \<open>set (map mset N0)\<close> \<open>set (map mset U0)\<close> \<open>set (map mset (map remdups clss))\<close>]
      by (metis (no_types, lifting) H1 H4 image_Un list.map_comp list.set_map remdups_eq satisfiable_mset_remdups(1))
  have state_equal: \<open>rough_state_from_init_state_of (do_all_cdcl\<^sub>W_stgy (state_from_init_state_of ([], map remdups N', [], None))) = T\<close>
     by (metis A2 H1 H2 H3 Un_iff add_clauses_code cdcl\<^sub>W_add_clauses_nat_def map_idI remdups_id_iff_distinct set_append) 
  have final: \<open>(D1 \<noteq> Some {#} \<and> satisfiable (set (map mset N')))
                \<or> (D1 = Some {#} \<and> (unsatisfiable (set (map mset N'))))\<close>
    using DPLL_tot_correct[OF state_equal A3] by auto
  then show ?thesis 
    using sat_preserve unsat_preserve by auto
qed

paragraph \<open>Code Generation\<close>
export_code do_all_cdcl\<^sub>W_stgy_nat Pos Neg natural_of_nat nat_of_integer init_state_init_state_of
  integer_of_int int_of_integer cdcl\<^sub>W_add_clauses_nat
  in SML
  module_name SAT_Solver
  file_prefix "Functional_Solver_Incremental_Basic"

end