(* Title: Correctness and Termination of DP Algorithm
    Author: Katharina Wagner
*)
theory dpAlgorithm
  imports Entailment_Definition.Partial_Herbrand_Interpretation
begin


lemma false_in_unsat:
  \<open>{#} \<in># N \<Longrightarrow>unsatisfiable (set_mset N)\<close>
  by (auto simp: satisfiable_def dest!: multi_member_split)

definition resolve_on :: "'v literal \<Rightarrow> 'v clause \<Rightarrow> 'v clause \<Rightarrow> 'v clause" where
  "resolve_on L C D = (remove1_mset L C) + remove1_mset (-L) D" 

definition resolve_all_on  :: "'v literal \<Rightarrow> 'v clauses \<Rightarrow> 'v clauses" where
  "resolve_all_on L N = remdups_mset `# ({#resolve_on L C D. (C, D) \<in># filter_mset (\<lambda>C. L \<in># C) N \<times># filter_mset (\<lambda>C. -L \<in># C) N#} +
    {#C \<in>#N. L \<notin>#C \<and> -L \<notin># C#})"

lemma resolve_all_on_no_lit:
  assumes \<open>atm_of L \<notin> atms_of_ms (set_mset A)\<close>
  shows \<open>resolve_all_on L A = remdups_mset `# A\<close>
proof -
  have [simp]: \<open>filter_mset ((\<in>#) L) A = {#}\<close> \<open>filter_mset ((\<in>#) (- L)) A = {#}\<close>
    using assms
    by (auto simp: resolve_all_on_def atms_of_ms_def filter_mset_empty_conv
        dest!: multi_member_split intro!: image_mset_cong2)
  have [simp]: \<open>{#C \<in># A. L \<notin># C \<and> - L \<notin># C#} = A\<close>
    using assms
    by (metis \<open>filter_mset ((\<in>#) (- L)) A = {#}\<close> \<open>filter_mset ((\<in>#) L) A = {#}\<close> 
        add_0 filter_filter_mset multiset_partition)
  show ?thesis
    by (auto simp: resolve_all_on_def atms_of_ms_def filter_mset_empty_conv
        dest!: multi_member_split cong: image_mset_cong2)
qed  


lemma resolve_all_on_distrib_no_lit:
  "atm_of L \<notin> atms_of_ms (set_mset A) \<Longrightarrow> resolve_all_on L (A + B) = remdups_mset `# A + resolve_all_on L B"
  by (subst resolve_all_on_no_lit[of L A, symmetric])
   (auto simp: resolve_all_on_def atms_of_ms_def filter_mset_empty_conv
      dest!: multi_member_split)

inductive DP_eins :: \<open>'v clauses \<Rightarrow> 'v clauses \<Rightarrow> bool\<close> where
  "DP_eins N {# C\<in>#resolve_all_on L N. \<not>tautology C#}"
if \<open>atm_of L \<in> atms_of_ms (set_mset N)\<close>

lemma entails_resolve_all_on[simp]:
  assumes "total_over_m I (set_mset N)" and "(\<forall>C. C \<in># N \<longrightarrow> \<not>tautology C)" and "(\<forall>C. C \<in># N \<longrightarrow> distinct_mset C)" and " consistent_interp I"
    and IN: "I \<Turnstile>m N"
  shows "I \<Turnstile>m {# C\<in>#resolve_all_on L N. \<not>tautology C#}"
proof -
  have "\<forall>C. C \<in># N \<longrightarrow> I \<Turnstile> C " and "\<forall>L C D. C \<in># N \<and> D \<in># N \<longrightarrow> (I \<Turnstile> C \<and> I \<Turnstile> D) \<longrightarrow> I \<Turnstile> resolve_on L C D"
    using IN
    apply (simp add: true_cls_mset_def)
    by (metis \<open>consistent_interp I\<close> consistent_interp_def diff_zero insert_DiffM minus_notin_trivial resolve_on_def true_cls_add_mset true_cls_union) 
  hence"\<forall>C. C \<in># {#C \<in>#N. L \<notin>#C \<and> -L \<notin># C#} \<longrightarrow> I \<Turnstile> C" and 
    "\<forall>L. atm_of L \<in> atms_of_ms (set_mset N) \<longrightarrow> I \<Turnstile>m  resolve_all_on L N" and
    "\<forall>C. C \<in># {#resolve_on L C D. (C, D) \<in># filter_mset (\<lambda>C. L \<in># C) N \<times># filter_mset (\<lambda>C. -L \<in># C) N#} \<longrightarrow> I \<Turnstile> C"
    using assms
    by (auto simp: resolve_all_on_def)
  hence "\<forall>C. C \<in># {#resolve_on L C D. (C, D) \<in># filter_mset (\<lambda>C. L \<in># C) N \<times># filter_mset (\<lambda>C. -L \<in># C) N#} + {#C \<in>#N. L \<notin>#C \<and> -L \<notin># C#} \<longrightarrow> I \<Turnstile> C" 
    by auto
  hence "\<forall>C. C \<in># resolve_all_on L N \<longrightarrow> I \<Turnstile> C"
    by (auto simp add: resolve_all_on_def) 
  hence "I \<Turnstile>m {# C\<in>#resolve_all_on L N. \<not>tautology C#}"
    by (simp add: true_cls_mset_def)
  then show ?thesis using \<open>I \<Turnstile>m N\<close> by auto
qed

lemma either_model_of_all_pos_or_model_of_all_neg[simp]:
  assumes
    taut: "(\<And>C. C \<in>#  N \<longrightarrow> \<not>tautology C)" and
    "I \<Turnstile>m resolve_all_on L N"
  shows "(\<forall>C \<in>#N. L \<in># C \<longrightarrow> I \<Turnstile> C - {#L#}) \<or> (\<forall>C \<in>#N. -L \<in># C \<longrightarrow> I \<Turnstile> C - {#-L#})"
proof (rule ccontr)
  assume "\<not>?thesis "
  then obtain C D where
    C: "C \<in># N" "\<not>I \<Turnstile> C - {#L#}" "L\<in>#C"  and
    D: "D \<in># N" "\<not>I \<Turnstile> D - {#-L#}" "-L\<in>#D"  by blast
  let ?C = \<open>C - {#L#}\<close>
  let ?D = \<open>D - {#-L#}\<close>
  have [simp]: \<open>D \<noteq> C\<close> \<open>- L \<notin># C\<close> \<open>L\<notin>#D\<close> 
    using C D taut[of C] taut[of D] by (auto dest!: multi_member_split simp: tautology_add_mset
        add_mset_eq_add_mset)
  have \<open>?C + ?D \<in># {#resolve_on L C D. (C, D) \<in># filter_mset (\<lambda>C. L \<in># C) N \<times># filter_mset (\<lambda>C. -L \<in># C) N#}\<close>
    using C D multi_member_split[of C N] multi_member_split[of D N]
    by (auto dest!: multi_member_split[of D]
        simp: add_mset_eq_add_mset Times_insert_right conj_disj_distribR
        Collect_disj_eq Collect_conv_if resolve_on_def
        add_mset_commute)
  then have \<open>remdups_mset (?C + ?D) \<in># resolve_all_on L N\<close>
    unfolding resolve_all_on_def apply -
    by (rule image_msetI) (auto simp: resolve_all_on_def)
  hence "I \<Turnstile> remdups_mset (?C + ?D)"
    by (meson assms(2) true_cls_mset_def)
  then show False
    using \<open>\<not>I\<Turnstile> C - {#L#}\<close> \<open>\<not>I \<Turnstile> D - {#-L#}\<close> by auto
qed

lemma hilfebackcase2:
  assumes "(\<forall>C. C \<in>#  N \<longrightarrow> \<not>tautology C)" and "(\<forall>C. C \<in>#  N \<longrightarrow> distinct_mset C)" and 
    "I \<Turnstile>m resolve_all_on L N" and "\<not>(I - {L, -L})\<union> {L}\<Turnstile>m {#C \<in>#N. -L \<in># C \<and> L \<notin>#C#}"
  shows "(I - {L, -L})\<union> {-L}\<Turnstile>m{#C \<in>#N. L \<in># C \<and> -L \<notin>#C#}"
proof -
  have "(\<not>(\<forall>C \<in>#N. -L \<in># C \<longrightarrow> I \<Turnstile> C - {#-L#}))"
    using assms 
    by (force simp: true_cls_def true_cls_mset_def dest!: multi_member_split)
  then have "\<forall>C\<in>#N. L \<in># C \<longrightarrow> I \<Turnstile> C - {#L#}"
    using either_model_of_all_pos_or_model_of_all_neg[of N I L]
    using assms(1) assms by blast
  then show ?thesis
    using assms unfolding true_cls_def
    by (force simp: true_cls_def true_cls_mset_def  dest!: multi_member_split)
qed

lemma noch_eine_hilfe[simp]:
  assumes "atm_of L \<in> atms_of_ms (set_mset N)" and "I \<Turnstile>m ({# C\<in>#resolve_all_on L N. \<not>tautology C#})" and "consistent_interp I" and " total_over_m I (set_mset ({# C\<in>#resolve_all_on L N. \<not>tautology C#}))"
 and "(\<forall>C. C \<in>#  N \<longrightarrow> distinct_mset C)"  and "(\<forall>C. C \<in>#  N \<longrightarrow> \<not>tautology C)"
  obtains I' where "I' \<Turnstile>m  resolve_all_on L N" and "consistent_interp I'" and " total_over_m I' (set_mset (resolve_all_on L N))"
proof-
  let ?I' = "I \<union> (Pos ` {A.  A\<in> atms_of_ms (set_mset {# C\<in>#resolve_all_on L N. tautology C#}) \<and>  A\<notin> atm_of ` I})"
  have "\<not>(\<exists>M. M\<in>?I' \<and> -M\<in>?I')"
    apply auto
    using assms(3) consistent_interp_def apply blast
    apply (metis image_iff literal.sel(2))
    by (metis atm_of_uminus image_iff literal.sel(1))
  hence consI': "consistent_interp ?I'" and  "\<forall>C\<in>#resolve_all_on L N. tautology C \<longrightarrow> (\<exists>A. A\<in>#C \<and> -A\<in>#C)" 
    apply (meson consistent_interp_def) using tautology_decomp' by blast    
  hence "\<forall>C\<in>#resolve_all_on L N. tautology C \<longrightarrow> (\<exists>A. A\<in>#C  \<and>  A\<in>?I')" 
    apply simp
    by (smt (verit, ccfv_threshold) atm_of_in_atm_of_set_in_uminus imageI in_implies_atm_of_on_atms_of_ms literal.sel(1) mem_Collect_eq tautology_decomp')
  hence  "\<forall>C\<in>#resolve_all_on L N. tautology C \<longrightarrow> (\<exists>A. A\<in>#C  \<and>  A\<in>?I')\<longrightarrow> ?I' \<Turnstile> C" 
    apply simp by (meson Un_iff true_cls_def true_lit_def)
  hence  "\<forall>C\<in>#resolve_all_on L N. tautology C \<longrightarrow>?I' \<Turnstile> C"
    apply simp
    using \<open>\<forall>C\<in>#resolve_all_on L N. tautology C \<longrightarrow> (\<exists>A. A \<in># C \<and> A \<in> ?I') \<longrightarrow>?I' \<Turnstile> C\<close>
 \<open>\<forall>C\<in>#resolve_all_on L N. tautology C \<longrightarrow> (\<exists>A. A \<in># C \<and> A \<in> I \<union> Pos ` {A \<in> atms_of_ms (set_mset (filter_mset tautology (resolve_all_on L N))). A \<notin> atm_of ` I})\<close> by auto
  hence "?I' \<Turnstile>m ({# C\<in>#resolve_all_on L N. tautology C#})" and "?I' \<Turnstile>m ({# C\<in>#resolve_all_on L N. \<not>tautology C#})"
    using true_cls_mset_def assms(2) by fastforce+
  hence I'_LN: "?I' \<Turnstile>m  resolve_all_on L N" and tot: "total_over_m ?I' (set_mset ({# C\<in>#resolve_all_on L N. \<not>tautology C#}))"
    apply (metis (no_types, lifting) mem_Collect_eq set_mset_filter true_cls_mset_def)
    apply simp using total_union using assms(4)
    by auto
  hence  "(\<forall>l\<in> atms_of_ms (set_mset ({# C\<in>#resolve_all_on L N. tautology C#})). Pos l \<in> ?I' \<or> Neg l \<in> ?I')"
    using atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set by fastforce 
  hence "total_over_m ?I' (set_mset ({# C\<in>#resolve_all_on L N. tautology C#}))" 
    by (meson total_over_m_def total_over_set_def)
  hence "total_over_m ?I' (set_mset ({# C\<in>#resolve_all_on L N. \<not>tautology C#} + {# C\<in>#resolve_all_on L N. tautology C#}))"
    by (metis (no_types) tot set_mset_union total_over_m_union)
  hence "total_over_m ?I' (set_mset (resolve_all_on L N))"
    by force
  then show ?thesis
    using that consI' I'_LN by blast
qed

lemma entails_resolve_all_on_back[simp]:
  assumes 
    "total_over_m I (set_mset (resolve_all_on L N))" and "(\<forall>C. C \<in>#  N \<longrightarrow> \<not>tautology C)" and "(\<forall>C. C \<in>#  N \<longrightarrow> distinct_mset C)" and
    " consistent_interp I" and "atm_of L \<in> atms_of_ms (set_mset N)" and "I \<Turnstile>m resolve_all_on L N"
  obtains I' where "consistent_interp I'" and "I' \<Turnstile>m N"
proof (cases "(I - {L, -L})\<union> {L}\<Turnstile>m {#C \<in>#N. -L \<in># C \<and> L \<notin>#C#}")
  case True
  let ?I' = "(I - {L, -L}) \<union> {L}"
  assume "(I - {L, -L})\<union> {L}\<Turnstile>m {#C \<in>#N. -L \<in># C \<and> L \<notin>#C#}"
  hence "\<forall>C. C \<in># resolve_all_on L N \<longrightarrow> I \<Turnstile>C"
    using assms by (simp add: true_cls_mset_def)
  hence "\<forall>C. C \<in># remdups_mset `#({#resolve_on L C D. (C, D) \<in># filter_mset (\<lambda>C. L \<in># C) N \<times># filter_mset (\<lambda>C. -L \<in># C) N#} + {#C \<in>#N. L \<notin>#C \<and> -L \<notin># C#}) \<longrightarrow> I \<Turnstile> C"
    by (simp add: resolve_all_on_def)
  hence "\<forall>C. C \<in># remdups_mset `#({#resolve_on L C D. (C, D) \<in># filter_mset (\<lambda>C. L \<in># C) N \<times># filter_mset (\<lambda>C. -L \<in># C) N#}) \<longrightarrow> I \<Turnstile> C" and "\<forall>C. C \<in># {#C \<in>#N. L \<notin>#C \<and> -L \<notin># C#} \<longrightarrow> I \<Turnstile> C"
    by auto
  hence"\<forall>C. C \<in># {#C \<in>#N. L \<notin>#C \<and> -L \<notin># C#} \<longrightarrow> I \<Turnstile> C" and "\<forall>C. C \<in># {#resolve_on L C D. (C, D) \<in># filter_mset (\<lambda>C. L \<in># C) N \<times># filter_mset (\<lambda>C. -L \<in># C) N#} \<longrightarrow> I \<Turnstile> C"
    apply blast
    using \<open>\<forall>C. C \<in># remdups_mset `# {#resolve_on L C D. (C, D) \<in># filter_mset ((\<in>#) L) N \<times># filter_mset ((\<in>#) (- L)) N#} \<longrightarrow> I \<Turnstile> C\<close> by fastforce
  hence"\<forall>C. C \<in># {#C \<in>#N. L \<notin>#C \<and> -L \<notin># C#} \<longrightarrow> ?I' \<Turnstile> C" and "\<forall>C. C \<in>#{#C \<in>#N. L \<in># C \<and> -L \<notin>#C#} \<longrightarrow>?I' \<Turnstile> C" and "\<forall>C. C \<in># {#C \<in>#N. L \<notin>#C \<and> -L \<in># C#} \<longrightarrow> ?I' \<Turnstile> C"
    apply (smt (verit, best) Diff_empty Diff_insert0 Diff_insert2 Un_insert_right insert_Diff insert_commute mem_Collect_eq set_mset_filter sup_bot.right_neutral true_cls.entail_union true_cls_not_in_remove)
    using assms
    using true_cls_def apply fastforce
    by (metis (no_types, lifting) True filter_mset_cong0 true_cls_mset_def)
  hence "?I' \<Turnstile>m N" and  "consistent_interp ?I'"
    apply (smt (verit, ccfv_threshold) Un_insert_right insertCI mem_Collect_eq set_mset_filter true_cls_def true_cls_mset_def true_lit_def) using assms
    by (metis Diff_iff Diff_subset Un_insert_right consistent_interp_insert_iff consistent_interp_subset insertCI sup_bot.right_neutral) 
  then show ?thesis
    using that by blast
next
  case False
  let ?I' = "(I - {L, -L}) \<union> {-L}"
  assume "\<not>(I - {L, -L})\<union> {L}\<Turnstile>m {#C \<in>#N. -L \<in># C \<and> L \<notin>#C#}"
  hence  "\<forall>C. C \<in># resolve_all_on L N \<longrightarrow> I \<Turnstile>C"
    using assms by (simp add: true_cls_mset_def)
  hence "\<forall>C. C \<in># remdups_mset `#({#resolve_on L C D. (C, D) \<in># filter_mset (\<lambda>C. L \<in># C) N \<times># filter_mset (\<lambda>C. -L \<in># C) N#} + {#C \<in>#N. L \<notin>#C \<and> -L \<notin># C#}) \<longrightarrow> I \<Turnstile> C"
    by (simp add: resolve_all_on_def)
  hence "\<forall>C. C \<in># remdups_mset `#({#resolve_on L C D. (C, D) \<in># filter_mset (\<lambda>C. L \<in># C) N \<times># filter_mset (\<lambda>C. -L \<in># C) N#}) \<longrightarrow> I \<Turnstile> C" and "\<forall>C. C \<in># {#C \<in>#N. L \<notin>#C \<and> -L \<notin># C#} \<longrightarrow> I \<Turnstile> C"
    by auto
  hence"\<forall>C. C \<in># {#C \<in>#N. L \<notin>#C \<and> -L \<notin># C#} \<longrightarrow> I \<Turnstile> C" and "\<forall>C. C \<in># {#resolve_on L C D. (C, D) \<in># filter_mset (\<lambda>C. L \<in># C) N \<times># filter_mset (\<lambda>C. -L \<in># C) N#} \<longrightarrow> I \<Turnstile> C"
    apply blast
    using \<open>\<forall>C. C \<in># remdups_mset `# {#resolve_on L C D. (C, D) \<in># filter_mset ((\<in>#) L) N \<times># filter_mset ((\<in>#) (- L)) N#} \<longrightarrow> I \<Turnstile> C\<close> by fastforce
  hence"\<forall>C. C \<in># {#C \<in>#N. L \<notin>#C \<and> -L \<notin># C#} \<longrightarrow> ?I' \<Turnstile> C"  and "\<forall>C. C \<in># {#C \<in>#N. L \<notin>#C \<and> -L \<in># C#} \<longrightarrow> ?I' \<Turnstile> C"and "\<forall>C. C \<in>#{#C \<in>#N. L \<in># C \<and> -L \<notin>#C#} \<longrightarrow>?I' \<Turnstile> C"
    apply (smt (verit) Diff_empty Diff_insert0 Un_commute assms(4) consistent_interp_def insert_Diff insert_is_Un mem_Collect_eq set_mset_filter true_cls.entail_union true_cls_not_in_remove)
    using true_cls_def apply fastforce
    using assms using hilfebackcase2
    by (metis (mono_tags, lifting) False true_cls_mset_def)
  hence "?I' \<Turnstile>m N" and  "consistent_interp ?I'"
    apply (smt (verit, ccfv_threshold) Un_insert_right insertCI mem_Collect_eq set_mset_filter true_cls_def true_cls_mset_def true_lit_def) using assms
    by (metis DiffE consistent_interp_def consistent_interp_insert_iff inf_sup_aci(5) insertI1 insert_is_Un uminus_of_uminus_id)
  then show ?thesis
    using that by blast 
qed

lemma DP_eins_satisfiable_iff:
  assumes
    "DP_eins N N'" and "\<forall>C. C\<in># N \<longrightarrow> distinct_mset C" and "\<forall>C. C\<in># N \<longrightarrow> \<not>tautology C" and "\<forall>C. C\<in># N' \<longrightarrow> \<not>tautology C"
  shows
    \<open>satisfiable (set_mset N) \<longleftrightarrow> satisfiable (set_mset N')\<close>
proof
  assume "satisfiable (set_mset N)"
  hence  "\<exists>I. I \<Turnstile>s (set_mset N)  \<and> consistent_interp I \<and> total_over_m I (set_mset N)"
    by (simp add: satisfiable_def)
  then obtain I where "I \<Turnstile>s (set_mset N)  \<and> consistent_interp I \<and> total_over_m I (set_mset N)" and "I \<Turnstile>m N" and "\<forall> L. atm_of L \<in> atms_of_ms (set_mset N) \<longrightarrow> I \<Turnstile>m  {# C\<in>#resolve_all_on L N. \<not>tautology C#}" 
    using entails_resolve_all_on using assms by blast 
  hence "\<exists>I. I \<Turnstile>s (set_mset N') \<and> consistent_interp I \<and> total_over_m I (set_mset N')" using assms
    by (metis DP_eins.cases satisfiable_carac' satisfiable_def true_clss_set_mset)
  then obtain I where "I \<Turnstile>s (set_mset N') \<and> consistent_interp I \<and> total_over_m I (set_mset N')" 
    by auto
  then show "satisfiable (set_mset N')" by auto
next
  assume "satisfiable (set_mset N')" 
  hence  "\<exists>I. I \<Turnstile>s (set_mset N')  \<and> consistent_interp I \<and> total_over_m I (set_mset N')"
    by (simp add: satisfiable_def)
  then obtain I L where I: "I \<Turnstile>s (set_mset N')  \<and> consistent_interp I \<and> total_over_m I (set_mset N')"  and IN': "I \<Turnstile>m N'" and
    L: " atm_of L \<in> atms_of_ms (set_mset N) \<longrightarrow> N' = {# C\<in>#resolve_all_on L N. \<not>tautology C#}"
    using assms apply auto using assms
    by (metis DP_eins.cases)
  hence  "atm_of L \<in> atms_of_ms (set_mset N) \<longrightarrow> N' = {# C\<in>#resolve_all_on L N. \<not>tautology C#}" and
    "atm_of L \<in> atms_of_ms (set_mset N) \<longrightarrow> I \<Turnstile>s (set_mset ({# C\<in>#resolve_all_on L N. \<not>tautology C#}))  \<and> consistent_interp I \<and> total_over_m I (set_mset ({# C\<in>#resolve_all_on L N. \<not>tautology C#}))"  
    and "atm_of L \<in> atms_of_ms (set_mset N) \<longrightarrow> I \<Turnstile>m ({# C\<in>#resolve_all_on L N. \<not>tautology C#})"
    apply blast
    using \<open>I \<Turnstile>s set_mset N' \<and> consistent_interp I \<and> total_over_m I (set_mset N')\<close> \<open>atm_of L \<in> atms_of_ms (set_mset N) \<longrightarrow> N' = {#C \<in># resolve_all_on L N. \<not> tautology C#}\<close> apply blast
    using \<open>I \<Turnstile>m N'\<close> \<open>atm_of L \<in> atms_of_ms (set_mset N) \<longrightarrow> N' = {#C \<in># resolve_all_on L N. \<not> tautology C#}\<close> by blast 
  hence "atm_of L \<in> atms_of_ms (set_mset N) \<longrightarrow> I \<Turnstile>m ({# C\<in>#resolve_all_on L N. \<not>tautology C#})  \<and> consistent_interp I \<and> total_over_m I (set_mset ({# C\<in>#resolve_all_on L N. \<not>tautology C#}))" 
    using assms
    by blast
  hence "\<exists>I. atm_of L \<in> atms_of_ms (set_mset N) \<longrightarrow> I \<Turnstile>m  resolve_all_on L N \<and> consistent_interp I \<and> total_over_m I (set_mset (resolve_all_on L N))" using noch_eine_hilfe
    by (metis assms(2) assms(3))
  then obtain I where "atm_of L \<in> atms_of_ms (set_mset N) \<longrightarrow> (I \<Turnstile>m resolve_all_on L N) \<and> consistent_interp I \<and> total_over_m I (set_mset (resolve_all_on L N))"
    by auto
  hence  "\<exists>I. I \<Turnstile>m  N \<and> consistent_interp I \<and> total_over_m I (set_mset N)" using assms using  entails_resolve_all_on_back
    by (metis (no_types, lifting) I DP_eins.cases  consistent_true_clss_ext_satisfiable noch_eine_hilfe satisfiable_def true_cls_mset_true_clss_iff(2) true_clss_imp_true_cls_ext)
  then obtain I where "I \<Turnstile>s (set_mset N) \<and> consistent_interp I \<and> total_over_m I (set_mset N)"
    by auto
  then show "satisfiable (set_mset N)"
    by auto
qed

lemma DP_eins_distinct:
  assumes \<open>DP_eins N N'\<close> "\<forall>C. C\<in># N \<longrightarrow> distinct_mset C"
  shows \<open>\<forall>C. C\<in># N' \<longrightarrow> distinct_mset C\<close>
  using assms by (induction rule: DP_eins.induct) (auto simp: resolve_all_on_def)

lemma rtranclp_DP_eins_distinct:
  assumes \<open>DP_eins\<^sup>*\<^sup>* N N'\<close> "\<forall>C. C\<in># N \<longrightarrow> distinct_mset C"
  shows \<open>\<forall>C. C\<in># N' \<longrightarrow> distinct_mset C\<close>
  using assms by (induction rule: rtranclp_induct) (auto simp: DP_eins_distinct)

lemma DP_eins_tauto:
  assumes \<open>DP_eins N N'\<close> "\<forall>C. C\<in># N \<longrightarrow> \<not>tautology C"
  shows "\<forall>C. C\<in># N' \<longrightarrow> \<not>tautology C"
  using assms by (induction rule: DP_eins.induct) (auto simp: resolve_all_on_def)

lemma rtranclp_DP_eins_tauto:
  assumes \<open>DP_eins\<^sup>*\<^sup>* N N'\<close> "\<forall>C. C\<in># N \<longrightarrow> \<not>tautology C"
  shows "\<forall>C. C\<in># N' \<longrightarrow> \<not>tautology C"
  using assms by (induction rule: rtranclp_induct) (auto simp: DP_eins_tauto)

lemma rtranclp_DP_eins_satisfiable_iff:
  assumes \<open>DP_eins\<^sup>*\<^sup>* N N'\<close> "\<forall>C. C\<in># N \<longrightarrow> distinct_mset C" and "\<forall>C. C\<in># N \<longrightarrow> \<not>tautology C"
  shows
    \<open>satisfiable (set_mset N) \<longleftrightarrow> satisfiable (set_mset N')\<close>
  using assms rtranclp_DP_eins_tauto[OF assms(1,3)] rtranclp_DP_eins_distinct[OF assms(1,2)]
  apply (induction rule: rtranclp_induct)
  apply (auto simp: DP_eins_satisfiable_iff DP_eins_distinct DP_eins_tauto)
  apply (metis rtranclp_DP_eins_distinct rtranclp_DP_eins_tauto)
  by (metis rtranclp_DP_eins_distinct rtranclp_DP_eins_tauto)

theorem DP_eins_empty:
  assumes \<open>DP_eins\<^sup>*\<^sup>* N N'\<close> and "\<forall>C. C\<in># N \<longrightarrow> distinct_mset C" and "\<forall>C. C\<in># N \<longrightarrow> \<not>tautology C" and \<open>{#} \<in># N'\<close>
  shows \<open>unsatisfiable (set_mset N)\<close>
  using rtranclp_DP_eins_satisfiable_iff[OF assms(1)] assms(2)
  by (simp add: assms(3) assms(4) false_in_unsat)

lemma atms_of_ms_remdups_mset[simp]: \<open>atms_of_ms (remdups_mset ` A) = atms_of_ms (A)\<close>
  by (auto simp: atms_of_ms_def)

theorem wf_DP_eins:
  shows "wf {(N', N). DP_eins N N' \<and> (\<forall>C. C\<in># N \<longrightarrow> distinct_mset C \<and> \<not>tautology C)}" (is \<open>wf ?R\<close>)
proof (rule wf_subset[OF wf_measure[of "\<lambda>N. card (atms_of_ms (set_mset N))"]], standard)
  let ?f = "(\<lambda>N. card (atms_of_ms (set_mset N)))"
  fix e
  assume "e \<in> ?R"
  hence "\<exists> N N'. e = (N', N) \<and> DP_eins N N' \<and> (\<forall>C. C\<in># N \<longrightarrow> distinct_mset C \<and> \<not>tautology C)" by auto
  then obtain N N' where "e = (N', N) \<and> DP_eins N N' \<and> (\<forall>C. C\<in># N \<longrightarrow> distinct_mset C \<and> \<not>tautology C)"
    by auto
  hence "\<exists>L. atm_of L \<in> atms_of_ms (set_mset N)" and 
    e: "e = (N', N) \<and> DP_eins N N' \<and> (\<forall>C. C\<in># N \<longrightarrow> distinct_mset C \<and> \<not>tautology C)"
    apply (meson DP_eins.cases)
    using \<open>e = (N', N) \<and> DP_eins N N' \<and> (\<forall>C. C \<in># N \<longrightarrow> distinct_mset C \<and> \<not> tautology C)\<close> by blast
  then obtain L where P:"atm_of L \<in> atms_of_ms (set_mset N)" and
    Q:"e = (N', N) \<and> DP_eins N N' \<and> (\<forall>C. C\<in># N \<longrightarrow> distinct_mset C \<and> \<not>tautology C)" and 
    R: "N' = {#C \<in># resolve_all_on L N. \<not> tautology C#}" 
    apply auto
    by (metis DP_eins.cases)
  have "atm_of L \<notin> atms_of_ms (set_mset{#C \<in># resolve_all_on L N. \<not> tautology C#})"
    using e
    unfolding resolve_on_def
    apply (auto simp: resolve_all_on_def atms_of_ms_def resolve_on_def add_mset_eq_add_mset 
        tautology_add_mset atm_of_notin_atms_of_iff all_conj_distrib
        dest!: multi_member_split[of L] multi_member_split[of "-L"] multi_member_split[of _ N])
    apply (metis tautology_add_mset uminus_of_uminus_id union_iff union_single_eq_member) 
    apply (metis distinct_mset_add_mset union_iff union_single_eq_member)
    done
  hence S: "atm_of L \<notin> atms_of_ms (set_mset N')"
    by (auto simp: R)
  hence"\<forall>M. atm_of M \<in> atms_of_ms (set_mset ({#C \<in>#N. L \<notin>#C \<and> -L \<notin># C#})) \<longrightarrow>  atm_of M \<in> atms_of_ms (set_mset N)" 
    and"\<forall>M. atm_of M \<in> atms_of_ms (set_mset {#resolve_on L C D. (C, D) \<in># filter_mset (\<lambda>C. L \<in># C) N \<times># filter_mset (\<lambda>C. -L \<in># C) N#}) \<longrightarrow>  atm_of M \<in> atms_of_ms (set_mset N)"  using R
     apply (meson atms_of_ms_mono multiset_filter_subset set_mset_mono subset_iff)
    using resolve_on_def apply (auto simp: atms_of_ms_def resolve_on_def
        dest!: multi_member_split)
    by (metis atm_of_uminus atms_of_add_mset insert_iff insert_noteq_member)
  hence "\<forall>M. atm_of M \<in> atms_of_ms (set_mset ({#C \<in>#N. L \<notin>#C \<and> -L \<notin># C#})) \<longrightarrow>  atm_of M \<in> atms_of_ms (set_mset N)
 \<and> (\<forall>M. atm_of M \<in> atms_of_ms (set_mset {#resolve_on L C D. (C, D) \<in># filter_mset (\<lambda>C. L \<in># C) N \<times># filter_mset (\<lambda>C. -L \<in># C) N#}) \<longrightarrow>  atm_of M \<in> atms_of_ms (set_mset N))"
    by blast
  hence "\<forall>M. atm_of M \<in> atms_of_ms (set_mset (({#C \<in>#N. L \<notin>#C \<and> -L \<notin># C#} + {#resolve_on L C D. (C, D) \<in># filter_mset (\<lambda>C. L \<in># C) N \<times># filter_mset (\<lambda>C. -L \<in># C) N#}))) \<longrightarrow>  atm_of M \<in> atms_of_ms (set_mset N)"
    by (simp add: \<open>\<forall>M. atm_of M \<in> atms_of_ms (set_mset {#resolve_on L C D. (C, D) \<in># filter_mset ((\<in>#) L) N \<times># filter_mset ((\<in>#) (- L)) N#}) \<longrightarrow> atm_of M \<in> atms_of_ms (set_mset N)\<close>) 
  hence "\<forall>M. atm_of M \<in> atms_of_ms (set_mset (remdups_mset `#({#C \<in>#N. L \<notin>#C \<and> -L \<notin># C#} + {#resolve_on L C D. (C, D) \<in># filter_mset (\<lambda>C. L \<in># C) N \<times># filter_mset (\<lambda>C. -L \<in># C) N#}))) \<longrightarrow>  atm_of M \<in> atms_of_ms (set_mset N)"
    by (metis (mono_tags, lifting) atms_of_ms_remdups_mset multiset.set_map)
  hence "\<forall>M. atm_of M \<in> atms_of_ms (set_mset (resolve_all_on L N))\<longrightarrow>  atm_of M \<in> atms_of_ms (set_mset N)" using resolve_all_on_def
    by (metis union_commute) 
  hence "\<forall>M. atm_of M \<in> atms_of_ms (set_mset ({#C \<in># resolve_all_on L N. \<not> tautology C#} + {#C \<in># resolve_all_on L N.  tautology C#}))\<longrightarrow>  atm_of M \<in> atms_of_ms (set_mset N)"
    by simp
  hence "\<forall>M. atm_of M \<in> atms_of_ms (set_mset ({#C \<in># resolve_all_on L N. \<not> tautology C#}))\<longrightarrow>  atm_of M \<in> atms_of_ms (set_mset N)"
    by (metis Un_iff atms_of_ms_union set_mset_union)
  hence U:"\<forall>M. atm_of M \<in> atms_of_ms (set_mset N') \<longrightarrow>  atm_of M \<in> atms_of_ms (set_mset N)"
    using R by auto[1]
  have "card(atms_of_ms (set_mset N')) < card(atms_of_ms (set_mset N))" 
    apply (rule psubset_card_mono)
     apply auto[]
    apply (subst psubset_eq)
    using P S
    by (metis U literal.sel(1) subsetI) 
  hence "?f N' < ?f N"
    by blast
  then show "e \<in> measure (\<lambda>N. card (atms_of_ms (set_mset N)))"
    by (simp add: \<open>e = (N', N) \<and> DP_eins N N' \<and> (\<forall>C. C \<in># N \<longrightarrow> distinct_mset C \<and> \<not> tautology C)\<close>)
qed


end