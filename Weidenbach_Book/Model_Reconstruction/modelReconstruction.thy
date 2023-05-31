(* Title: Model Reconstruction
    Author: Katharina Wagner
*)
theory modelReconstruction
  imports Entailment_Definition.Partial_Herbrand_Interpretation
    Entailment_Definition.Partial_Annotated_Herbrand_Interpretation
    dpAlgorithm
begin


datatype 'a stack_step =
  is_elim: Elimination (elim_lit: "'a literal") (pos_occ: "'a clauses") (neg_occs:"'a clauses") |
  is_tauto: Tautology (tauto_on: "'a literal") (tauto_clause: "'a clause")

lemma stack_step_list_induct:
  \<open>P [] \<Longrightarrow> (\<And>a b c x2. P x2 \<Longrightarrow> P (Elimination a b c # x2)) \<Longrightarrow> 
   (\<And>a b x2. P x2 \<Longrightarrow> P (Tautology a b # x2)) \<Longrightarrow> 
   P list\<close>
  apply (induction list)
   apply auto
  apply (case_tac a)
   apply auto
  done

type_synonym 'a stack = "'a stack_step list"

inductive res_stack :: "'v clauses \<times> 'v stack \<Rightarrow> 'v clauses \<times> 'v stack \<Rightarrow> bool" where
  "res_stack (N, S) ({# C\<in>#resolve_all_on L N. \<not>tautology C#}, S @ Elimination L {#C\<in>#N.  L\<in>#C#} {#C\<in>#N. -L\<in>#C#} # T)"
if "atm_of L \<in> atms_of_ms (set_mset N)" 
  "tauto_clause `# mset T =  {# C\<in>#resolve_all_on L N. tautology C#}" 
  "\<forall>s\<in>set T. is_tauto s \<and> tauto_on s \<in># tauto_clause s \<and> -tauto_on s \<in># tauto_clause s"

lemmas [intro] = res_stack.intros

fun infer_from_step :: "'v stack_step \<Rightarrow> 'v partial_interp \<Rightarrow> 'v partial_interp " where
  "infer_from_step (Elimination L ps ns) I = (if I \<Turnstile>m ps + ns then I else (if I \<Turnstile>m ps then I \<union> {-L} else I \<union> {L}))" |
  "infer_from_step (Tautology L C) I = (if I \<Turnstile> C then I else I \<union> {L})"

abbreviation inter_from_stack :: "'v stack_step list \<Rightarrow> 'v partial_interp \<Rightarrow> 'v partial_interp" where
  "inter_from_stack xs I \<equiv> foldr infer_from_step xs I" 

lemmas res_stack_induct =
  res_stack.induct[split_format(complete)]

lemma equivalence_dp_stack_1:
  assumes "DP_eins N N'"
  shows "\<exists>S'. res_stack (N, S) (N', S')"
  using assms
proof (induction rule: DP_eins.induct)
  case (1 L N) note L = this(1)
  define NN where "NN = {# C\<in>#resolve_all_on L N. tautology C#}"
  have  "\<forall>C. C \<in># {# C\<in>#resolve_all_on L N. tautology C#} \<longrightarrow> (\<exists>M. M\<in>#C \<and> -M \<in># C)" using tautology_exists_Pos_Neg
    by (simp add: tautology_decomp') 
  hence "\<forall>C. C \<in># {# C\<in>#resolve_all_on L N. tautology C#}  \<longrightarrow> (\<exists>M. M\<in>#C \<and> -M \<in># C  \<and> is_tauto (Tautology (M) (C)))"
    using is_tauto_def by blast
  hence "\<forall>C. C \<in># {# C\<in>#resolve_all_on L N. tautology C#}  \<longrightarrow> (\<exists>M. M\<in>#C \<and> -M \<in># C  \<and> is_tauto (Tautology (M) (C)) \<and> tauto_on (Tautology (M) (C)) \<in># tauto_clause (Tautology (M) (C))
 \<and> -tauto_on (Tautology (M) (C)) \<in># tauto_clause (Tautology (M) (C)))"
    by auto
  hence "\<exists>T. tauto_clause `# mset T = {# C\<in>#resolve_all_on L N. tautology C#} \<and> (\<forall>s\<in>set T. is_tauto s \<and> tauto_on s \<in># tauto_clause s \<and> -tauto_on s \<in># tauto_clause s)"
    unfolding NN_def[symmetric]
    apply (induction "NN")
     apply auto[]
    apply (auto simp add: all_conj_distrib)
    apply (rule_tac x= "Tautology M x # T" in exI)
    apply auto
    done
  then obtain T where E: "tauto_clause `# mset T =  {# C\<in>#resolve_all_on L N. tautology C#}" and
    F: "(\<forall>s\<in>set T. is_tauto s \<and> tauto_on s \<in># tauto_clause s \<and> -tauto_on s \<in># tauto_clause s)"
    by auto
  let ?S' = "S @ Elimination L {#C\<in># N.  L\<in>#C#} {#C\<in>#N. -L\<in>#C#} # T" 
  have C: "DP_eins N {# C\<in>#resolve_all_on L N. \<not>tautology C#}" using assms(1)
    using DP_eins.intros L by blast
  have "res_stack (N, S) ({# C\<in>#resolve_all_on L N. \<not>tautology C#}, ?S')" using E F L
    by (auto intro!: res_stack.intros)
  hence "\<exists>S'. res_stack (N, S) ({# C\<in>#resolve_all_on L N. \<not>tautology C#}, S')" 
    by blast
  then show ?case
    by blast
qed

lemma equivalence_dp_stack_2:
  "res_stack (N, S) (N', S') \<Longrightarrow> DP_eins N N'"
  by (induction rule: res_stack_induct)
    (auto simp: DP_eins.intros)

lemma resolved_atm_notin_resolved_clauses:
  assumes 
    "\<forall>C. C\<in># N \<longrightarrow> distinct_mset C" and " \<forall>C. C\<in># N \<longrightarrow>  \<not>tautology C"
  shows
    "atm_of L \<notin> atms_of_ms(set_mset({# C\<in>#resolve_all_on L N. \<not>tautology C#}))" 
  unfolding resolve_on_def
  apply (auto simp: resolve_all_on_def atms_of_ms_def resolve_on_def add_mset_eq_add_mset 
      tautology_add_mset atm_of_notin_atms_of_iff all_conj_distrib
      dest!: multi_member_split[of L] multi_member_split[of "-L"] multi_member_split[of _ N])
  using assms
   apply (metis Un_iff distinct_mset_add_mset member_add_mset set_mset_union tautology_add_mset uminus_of_uminus_id) 
  using assms by (metis add_mset_add_single is_mset_set_add member_add_mset tautology_add_mset union_iff)

lemma resolved_atm_notin_resolved_clauses2:
  assumes 
    "\<forall>C. C\<in># N \<longrightarrow> distinct_mset C" and " \<forall>C. C\<in># N \<longrightarrow>  \<not>tautology C"
  shows "atm_of L \<notin> atms_of_ms(set_mset({# C\<in>#resolve_all_on L N. tautology C#}))"
  unfolding resolve_on_def
  apply (auto simp: resolve_all_on_def atms_of_ms_def resolve_on_def add_mset_eq_add_mset 
      tautology_add_mset atm_of_notin_atms_of_iff all_conj_distrib
      dest!: multi_member_split[of L] multi_member_split[of "-L"] multi_member_split[of _ N])
  using assms apply (meson tautology_add_mset union_single_eq_member)
  using assms(1) apply auto[1]
         apply (metis Un_iff assms(1) assms(2) distinct_mset_add_mset member_add_mset set_mset_union tautology_add_mset uminus_of_uminus_id)
        apply (metis assms(2) tautology_add_mset union_single_eq_member)
       apply (metis Un_iff assms(1) assms(2) distinct_mset_add_mset member_add_mset set_mset_union tautology_add_mset)
      apply (metis assms(2) tautology_add_mset union_single_eq_member)
     apply (metis assms(2) member_add_mset tautology_add_mset)
    apply (metis assms(1) assms(2) distinct_mset_add_mset member_add_mset tautology_add_mset union_iff)
   apply (metis assms(2) tautology_add_mset union_single_eq_member)
  by (metis assms(1) assms(2) distinct_mset_add_mset member_add_mset tautology_add_mset union_iff)

lemma interp_is_cons: 
  assumes "res_stack (N, S) (N', S')" and "\<forall>C. C\<in># N \<longrightarrow> distinct_mset C" and "\<forall>C. C\<in># N \<longrightarrow>  \<not>tautology C" and
    "I  \<Turnstile>m N'" and "atm_of ` I \<subseteq> atms_of_mm N'" and "consistent_interp I"
  shows "consistent_interp (inter_from_stack (drop (length S) S') I)"
  using assms 
proof (induction rule: res_stack_induct)
  case (1 L N T S) note L = this(1) and T = this(2, 3) and dist_no_tauto = this(4,5) and I = this(6-)
  have "res_stack (N, S) ({# C\<in>#resolve_all_on L N. \<not>tautology C#}, S @ [Elimination L {#C\<in># N.  L\<in>#C#} {#C\<in>#N. -L\<in>#C#}] @ T)" 
    using assms(1) L T by auto 
  have "atm_of L \<notin> atms_of_ms(set_mset({# C\<in>#resolve_all_on L N. \<not>tautology C#}))" using resolved_atm_notin_resolved_clauses 1
    by blast 
  hence V:"L \<notin> I \<and> -L \<notin> I" using I
    by (meson atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set subsetD) 
  have K: "consistent_interp (inter_from_stack T I)"
    using I T(2)
    by (induction T)
      (auto simp: is_tauto_def consistent_interp_insert_iff true_cls_def)
  have J:"atm_of L \<notin> atms_of_ms(set_mset(tauto_clause `# mset T))" using T resolved_atm_notin_resolved_clauses2
    using dist_no_tauto(1) dist_no_tauto(2) by auto 
  hence Z:"\<not>(\<exists>s\<in>set T. is_tauto s \<and> (L = tauto_on s))" using T
    by (metis imageI in_implies_atm_of_on_atms_of_ms set_image_mset set_mset_mset) 
  have X: "\<not>(\<exists>s\<in>set T. is_tauto s \<and> (-L = tauto_on s))" using T J
    by (metis imageI in_implies_atm_of_on_atms_of_ms set_image_mset set_mset_mset uminus_of_uminus_id) 
  have B: "(atm_of L \<notin> atms_of_ms(set_mset(tauto_clause `# mset T)) \<and> L \<notin> I \<and> -L \<notin> I \<and> 
      (\<forall>s\<in>set T. is_tauto s \<and> (-L \<noteq> tauto_on s) \<and> (L \<noteq> tauto_on s))) \<Longrightarrow> (- L) \<notin> (inter_from_stack T I)" 
    using resolved_atm_notin_resolved_clauses2[OF dist_no_tauto]
    by (induction T rule: stack_step_list_induct) auto
  have D: "(atm_of L \<notin> atms_of_ms(set_mset(tauto_clause `# mset T)) \<and> L \<notin> I \<and> -L \<notin> I \<and> (\<forall>s\<in>set T. is_tauto s \<and> (-L \<noteq> tauto_on s) \<and> (L \<noteq> tauto_on s))) \<longrightarrow> L \<notin> (inter_from_stack T I)"
    using resolved_atm_notin_resolved_clauses2[OF dist_no_tauto]
    by (induction T rule: stack_step_list_induct) auto
  have M: \<open>(- L) \<notin> (inter_from_stack T I)\<close>
    using V T X Z B resolved_atm_notin_resolved_clauses2[OF dist_no_tauto]
    by (induction T) auto
  have P: "L \<notin> (inter_from_stack T I)"  
    using V T X Z D resolved_atm_notin_resolved_clauses2[OF dist_no_tauto]
    by (induction T) (auto simp: split: if_splits dest!: filter_mset_eq_add_msetD')
  have "consistent_interp (inter_from_stack (drop (length S) (S @ [Elimination L {#C\<in># N.  L\<in>#C#} {#C\<in>#N. -L\<in>#C#}] @ T)) I)"
    using T(2) M P K
    by auto
  then show ?case
    by auto
qed

lemma interpr_is_extension: 
  shows "I \<subseteq> (inter_from_stack (drop (length S) S') I)"
proof - 
  have "\<exists> I'. inter_from_stack xs  I = I'\<union> I " for xs
    by (induction xs rule: stack_step_list_induct)
      auto
  hence "I \<subseteq> (inter_from_stack (drop (length S) S') I)"
    by blast
  then show ?thesis by auto
qed

lemma res_stack_distinct:
  assumes "res_stack (N, S) (N', S')" and"\<forall>C. C\<in># N  \<longrightarrow> distinct_mset C"
  shows \<open>\<forall>C. C\<in># N' \<longrightarrow> distinct_mset C\<close>
  using assms by (induction rule: res_stack_induct) (auto simp: resolve_all_on_def)

lemma rtranclp_res_stack_distinct:
  assumes "res_stack\<^sup>*\<^sup>* (N, S) (N', S')" and "\<forall>C. C\<in># N \<longrightarrow> distinct_mset C"
  shows \<open>\<forall>C. C\<in># N' \<longrightarrow> distinct_mset C\<close>
  using assms apply (induction rule: rtranclp_induct2)
   apply (auto intro: res_stack_distinct)
  by (metis res_stack_distinct)

lemma res_stack_tauto:
  assumes "res_stack (N, S) (N', S')" and "\<forall>C. C\<in># N \<longrightarrow> \<not>tautology C"
  shows "\<forall>C. C\<in># N' \<longrightarrow> \<not>tautology C"
  using assms by (induction rule: res_stack_induct) (auto simp: resolve_all_on_def)

lemma rtranclp_res_stack_tauto:
  assumes "res_stack\<^sup>*\<^sup>* (N, S) (N', S')" and "\<forall>C. C\<in># N \<longrightarrow> \<not>tautology C"
  shows "\<forall>C. C\<in># N' \<longrightarrow> \<not>tautology C"
  using assms apply (induction rule: rtranclp_induct2)
  by(auto simp: res_stack_tauto)

lemma interpr_sat_all_2:
  assumes "res_stack (N, S) (N', S')" and N: "\<forall>C. C\<in># N  \<longrightarrow> distinct_mset C" and  "\<forall>C. C\<in># N  \<longrightarrow>  \<not>tautology C" and
    I: "I  \<Turnstile>m N'" and "atm_of ` I \<subseteq> atms_of_mm N'" 
  shows "(inter_from_stack (drop (length S) S') I) \<Turnstile>m N"
  using assms(1)
proof (cases)
  case (1 L T) note N' = this(1) and S' = this(2) and L = this(3) and T = this(4-5)
  have C:"I \<subseteq> (inter_from_stack (drop (length S) S') I)" using interpr_is_extension assms
    by blast
  have XX: "s \<in> set T \<Longrightarrow>(\<forall>s\<in>set T. is_tauto s \<and> tauto_on s \<in># tauto_clause s) \<Longrightarrow> inter_from_stack T I \<Turnstile> tauto_clause s" for s
    apply (induction T arbitrary: s I rule: stack_step_list_induct)
    subgoal by auto
    subgoal by auto
    subgoal by (force simp: true_cls_def)
    done
  hence "\<forall>s\<in>set T. inter_from_stack T I \<Turnstile> tauto_clause s"  
    using T unfolding S' by auto
  then have I_T: \<open>inter_from_stack T I \<Turnstile>m {#C \<in># resolve_all_on L N. \<not> tautology C#}\<close>
    \<open>inter_from_stack T I \<Turnstile>m {#C \<in># resolve_all_on L N. tautology C#}\<close>
    using T assms(4) C
     apply (auto simp: true_cls_mset_def N' dest!: multi_member_split intro: true_cls_mono_set_mset_l)
     apply (metis Ex_list_of_length drop0 interpr_is_extension true_cls_mono_set_mset_l)
    by (metis set_mset_mset true_cls_mset_add_mset true_cls_mset_image_mset)
  have X: \<open>\<And>C. C \<in># N \<longrightarrow> \<not> tautology C\<close>
    using N' assms(1) assms(3) res_stack_tauto by blast
  have I_N': \<open>inter_from_stack T I \<Turnstile>m resolve_all_on L N\<close>
    using I_T unfolding S' by (metis true_cls_mset_union union_filter_mset_complement)
  show ?thesis
  proof (cases \<open>inter_from_stack T I \<Turnstile>m filter_mset ((\<in>#) L) N\<close>)
    assume all_T: \<open>inter_from_stack T I \<Turnstile>m filter_mset ((\<in>#) L) N\<close>
    let ?I = \<open>insert (- L) (inter_from_stack T I)\<close>
    have \<open>?I \<Turnstile>m filter_mset ((\<in>#) L) N\<close>
      using all_T by (simp add: true_cls_mset_def)
    moreover have \<open>?I \<Turnstile>m filter_mset ((\<in>#) (-L)) N\<close>
      using all_T by (auto simp: true_cls_mset_def dest!: multi_member_split)
    moreover have \<open>?I \<Turnstile>m filter_mset (\<lambda>C. L \<notin># C \<and> -L \<notin># C) N\<close>
      using I_N' N unfolding N' apply (auto simp: resolve_all_on_def true_cls_mset_def dest!: multi_member_split)
      by (metis (mono_tags, lifting) Un_iff image_eqI mem_Collect_eq true_cls_insert_l true_cls_remdups_mset)
    ultimately show ?thesis
      using all_T  unfolding S' N' apply auto
      apply (smt (verit) insert_iff mem_Collect_eq set_mset_filter true_cls_def true_cls_mset_def true_lit_def)
      apply (smt (verit, ccfv_SIG) mem_Collect_eq set_mset_filter true_cls_mset_def) 
      done
  next
    assume all_T: \<open>\<not>inter_from_stack T I \<Turnstile>m filter_mset ((\<in>#) L) N\<close>
    then have \<open>\<not>(\<forall>C\<in>#N. L \<in># C \<longrightarrow> inter_from_stack T I \<Turnstile> remove1_mset L C)\<close>
      by (auto simp: true_cls_mset_def dest!: multi_member_split)
    then have false: \<open>(\<forall>C\<in>#N. - L \<in># C \<longrightarrow> inter_from_stack T I \<Turnstile> remove1_mset (- L) C)\<close>
      using either_model_of_all_pos_or_model_of_all_neg[of N "inter_from_stack T I" L, OF X I_N']  N I
      unfolding N'
      by auto
    let ?I = \<open>insert (L) (inter_from_stack T I)\<close>
    have all_T: \<open>inter_from_stack T I \<Turnstile>m filter_mset ((\<in>#) (-L)) N\<close>
      using false by (auto simp: true_cls_mset_def dest!: multi_member_split)
    then have \<open>?I \<Turnstile>m filter_mset ((\<in>#) (-L)) N\<close>
      by (simp add: true_cls_mset_def)
    moreover have \<open>?I \<Turnstile>m filter_mset ((\<in>#) (L)) N\<close>
      using false by (auto simp: true_cls_mset_def dest!: multi_member_split)
    moreover have \<open>?I \<Turnstile>m filter_mset (\<lambda>C. L \<notin># C \<and> -L \<notin># C) N\<close>
      using I_N' N unfolding N' apply (auto simp: resolve_all_on_def true_cls_mset_def dest!: multi_member_split)
      by (metis (mono_tags, lifting) Un_iff image_eqI mem_Collect_eq true_cls_insert_l true_cls_remdups_mset)
    ultimately show ?thesis
      using all_T unfolding S' N' apply auto
       apply (smt (verit, ccfv_threshold) filter_mset_add_mset insertE mset_add true_cls_def true_cls_insert_l
          true_cls_mset_add_mset true_cls_mset_def true_lit_def)+
      done
  qed
qed


lemma atm_inter_from_stack_sup:
  \<open>atm_of ` (inter_from_stack xs I) \<subseteq> atm_of ` I \<union> atm_of ` (\<lambda>x. case x of Tautology L _ \<Rightarrow> L | Elimination L _ _ \<Rightarrow> L) ` set xs\<close>
  by (induction xs)
    (auto split: stack_step.splits)

lemma interpr_sat_all:
  assumes "res_stack\<^sup>*\<^sup>* (N, S) (N', S')" and"\<forall>C. C\<in># N  \<longrightarrow> distinct_mset C" and "\<forall>C. C\<in># N  \<longrightarrow>  \<not>tautology C" and
    "I  \<Turnstile>m N'" and "atm_of ` I \<subseteq> atms_of_mm N'" 
  shows "(inter_from_stack (drop (length S) S') I) \<Turnstile>m N"
  using assms 
proof (induction arbitrary: I rule: rtranclp_induct2)
  case refl
  have A: "I  \<Turnstile>m N" 
    using assms  using refl.prems(3) by blast
  have  "atms_of(mset_set I) \<subseteq> atms_of_mm N" using assms(5)
    by (metis atms_of_def atms_of_empty empty_subsetI finite_set_mset_mset_set mset_set.infinite refl.prems(4))
  have "I \<subseteq> (inter_from_stack (drop (length S) S') I)" using interpr_is_extension assms
    by blast
  hence B: "(inter_from_stack (drop (length S) S') I) \<Turnstile>m N" using A
    by (meson true_cls_mset_true_clss_iff(2) true_clss_mono_left)
  then show ?case using assms apply auto
    using A by blast
next
  case (step N' S' N'' S'' I) note A1 = this(1) and A2 = this(2) and A6 = this(6, 7) and A4 = this(4, 5) and IH = this(3) and I = this(7)
  have AA: "res_stack\<^sup>*\<^sup>* (N, S) (N'', S'')" using assms(1)
    using step.hyps(1) step.hyps(2) by auto
  obtain L T where 
    "res_stack (N', S') ({# C\<in>#resolve_all_on L N'. \<not>tautology C#}, S' @ [Elimination L {#C\<in># N'.  L\<in>#C#} {#C\<in>#N'. -L\<in>#C#}] @ T)" and
    S'': "S'' = S' @ [Elimination L {#C\<in># N'.  L\<in>#C#} {#C\<in>#N'. -L\<in>#C#}] @ T" and
    N'': "N'' = {# C\<in>#resolve_all_on L N'. \<not>tautology C#}" and
    L:"atm_of L \<in> atms_of_ms (set_mset N')" and
    T: "tauto_clause `# mset T =  {# C\<in>#resolve_all_on L N'. tautology C#}" 
      "(\<forall>s\<in>set T. is_tauto s \<and> tauto_on s \<in># tauto_clause s \<and> -tauto_on s \<in># tauto_clause s)" 
    using step(2)
    by (auto simp: res_stack.simps)
  have "length S' \<ge> length S"
    using A1 by (induction rule: rtranclp_induct2) (auto simp: res_stack.simps)
  have dist:"\<forall>C. C\<in># N'  \<longrightarrow> distinct_mset C" and taut:"\<forall>C. C\<in># N'  \<longrightarrow>  \<not>tautology C" 
    using A1 rtranclp_res_stack_distinct A4
     apply blast using rtranclp_res_stack_tauto A1 A4 by blast
  have sat:"(inter_from_stack (drop (length S') S'') I) \<Turnstile>m N'"
    using dist taut A2 A6 interpr_sat_all_2
    by metis
  have \<open>atms_of_mm N'' \<subseteq> atms_of_mm N'\<close>
    unfolding N'' 
    apply (auto simp: atms_of_ms_def resolve_all_on_def resolve_on_def atms_of_def
        dest: multi_member_split)
    apply (meson imageI in_diffD)
    apply (meson imageI in_diffD)
    done
  moreover have \<open>atm_of ` (\<lambda>x. case x of Elimination L x xa \<Rightarrow> L | Tautology L x \<Rightarrow> L) ` set T \<subseteq> atms_of_mm N'\<close>
    using T
    apply (auto dest!: split_list filter_mset_eq_add_msetD in_diffD
        simp: eq_commute[of "add_mset _ _" "filter_mset _ _"] is_tauto_def)
    apply (auto simp: resolve_all_on_def resolve_on_def atm_of_notin_atms_of_iff
        dest: in_diffD multi_member_split[of _ N'])
    apply (meson diff_subset_eq_self in_implies_atm_of_on_atms_of_ms mset_subset_eqD)+
    done
  ultimately have sub:"atm_of ` (inter_from_stack (drop (length S') S'') I) \<subseteq> atms_of_mm N'" 
    using L atm_inter_from_stack_sup[of T I] I
    unfolding S'' 
    apply (auto split: if_splits dest: )
    apply (frule in_set_image_subsetD[of _ "inter_from_stack _ _"])
    apply assumption
    apply auto
    done
  have \<open>inter_from_stack (drop (length S) S') (inter_from_stack ([Elimination L {#C\<in># N'.  L\<in>#C#} {#C\<in>#N'. -L\<in>#C#}] @ T) I) \<Turnstile>m N\<close>
    apply (rule IH)
    using assms apply ((solves auto)+)[2]
    using S'' S'' sat apply force
    using S'' sub by auto
  then show ?case
    by (simp add: S'' \<open>length S \<le> length S'\<close>)
qed

lemma interp_is_cons_mult: 
  assumes "res_stack\<^sup>*\<^sup>* (N, S) (N', S')" and  "\<forall>C. C\<in># N  \<longrightarrow>  distinct_mset C" and "\<forall>C. C\<in># N  \<longrightarrow>  \<not>tautology C"  and
    "I  \<Turnstile>m N'" and "consistent_interp I" and "atm_of ` I \<subseteq> atms_of_mm N'"
  shows "consistent_interp (inter_from_stack (drop (length S) S') I)"
  using assms
proof (induction arbitrary: I rule: rtranclp_induct2)
  case refl
  then show ?case by (auto intro: interp_is_cons)
next
  case (step N' S' N'' S'') note A1 = this(1) and A2 = this(2) and A5 = this(6, 8) and A3 = this(3, 4) and
    I= this(7,8) and IH=this(3)
  obtain L T where 
    "res_stack (N', S') ({# C\<in>#resolve_all_on L N'. \<not>tautology C#}, S' @ [Elimination L {#C\<in># N'.  L\<in>#C#} {#C\<in>#N'. -L\<in>#C#}] @ T)" and
    S'': "S'' = S' @ [Elimination L {#C\<in># N'.  L\<in>#C#} {#C\<in>#N'. -L\<in>#C#}] @ T" and
    N'': "N'' = {# C\<in>#resolve_all_on L N'. \<not>tautology C#}" and
    L:"atm_of L \<in> atms_of_ms (set_mset N')" and
    T: "tauto_clause `# mset T =  {# C\<in>#resolve_all_on L N'. tautology C#}"
    "(\<forall>s\<in>set T. is_tauto s \<and> tauto_on s \<in># tauto_clause s \<and> -tauto_on s \<in># tauto_clause s)" 
    using step(2)
    by (auto simp: res_stack.simps)
  let ?J = \<open>inter_from_stack (drop (length S') S'') I\<close>
  have N'_dist_tauto: \<open> \<forall>C. C \<in># N' \<longrightarrow> distinct_mset C\<close> \<open> \<forall>C. C \<in># N' \<longrightarrow> \<not> tautology C\<close>
    using A1 rtranclp_res_stack_distinct step.prems(1,2) apply blast
    using A1 rtranclp_res_stack_tauto step.prems(2) by blast
  have L_N'': \<open>atm_of L \<notin> atms_of_mm N''\<close>
    by (metis A1 N'' resolved_atm_notin_resolved_clauses rtranclp_res_stack_distinct 
        rtranclp_res_stack_tauto step.prems(1) step.prems(2))
  have \<open>atms_of_mm N'' \<subseteq> atms_of_mm N'\<close>
    unfolding N'' 
    apply (auto simp: atms_of_ms_def resolve_all_on_def resolve_on_def atms_of_def
        dest: multi_member_split in_diffD dest!: multi_member_split[of "_ :: _ clause"])
    apply (metis filter_mset_eq_add_msetD' in_diffD rev_image_eqI)+
    done
  moreover have \<open>atm_of ` (\<lambda>x. case x of Elimination L x xa \<Rightarrow> L | Tautology L x \<Rightarrow> L) ` set T \<subseteq> atms_of_mm N'\<close>
    using T
    apply (auto dest!: split_list filter_mset_eq_add_msetD in_diffD
        simp: eq_commute[of "add_mset _ _" "filter_mset _ _"] is_tauto_def)
    apply (auto simp: resolve_all_on_def resolve_on_def dest: in_diffD multi_member_split)
    apply (fast dest: in_implies_atm_of_on_atms_of_ms in_diffD)+
    done
  ultimately have sub:"atm_of ` (inter_from_stack (drop (length S') S'') I) \<subseteq> atms_of_mm N'" 
    using L atm_inter_from_stack_sup[of T I] I
    unfolding S'' 
    apply (auto split: if_splits dest: )
    apply (frule in_set_image_subsetD[of _ "inter_from_stack _ _"])
    apply assumption
    apply auto
    done
  have T2: \<open>\<forall>s\<in>set T. tauto_clause s \<in># resolve_all_on L N'\<close>
    using T apply auto
    by (metis filter_mset_eq_add_msetD' image_mset_add_mset in_multiset_in_set multi_member_split) 
  then have \<open>consistent_interp (inter_from_stack T I)\<close>
    using T(2) I by (induction T rule: stack_step_list_induct)
      (auto simp: consistent_interp_insert_iff true_cls_def)
  moreover have \<open>L \<notin> inter_from_stack T I \<and> -L \<notin> inter_from_stack T I\<close>
  proof -
    have \<open>L \<notin> I\<close> \<open>-L \<notin> I\<close>
      using I L_N'' by auto
    then show \<open>L \<notin> inter_from_stack T I \<and> -L \<notin> inter_from_stack T I\<close>
      using T(2) T2 I resolved_atm_notin_resolved_clauses2[of N' L, OF N'_dist_tauto]
      by (induction T rule: stack_step_list_induct)
        (auto simp: consistent_interp_insert_iff true_cls_def in_implies_atm_of_on_atms_of_ms 
          dest: multi_member_split)
  qed
  ultimately have cons:"consistent_interp (inter_from_stack (drop (length S') S'') I)"
    unfolding S'' by (auto simp: consistent_interp_insert_iff)
  moreover have \<open>?J \<Turnstile>m N'\<close>
    using interpr_sat_all[OF _ N'_dist_tauto step(6,8), of S' S''] step(2) by auto
  moreover have \<open>length S \<le> length S'\<close>
    using step(1) by (induction rule: rtranclp_induct2) (auto simp: res_stack.simps)
  ultimately show ?case
    using step(2,4-) sub
    unfolding S'' by (auto simp del: infer_from_step.simps intro!: IH)
qed

lemma interpr_sat_all_final:
  assumes "res_stack\<^sup>*\<^sup>*  (N, []) ({#}, S')" and "\<forall>C. C\<in># N  \<longrightarrow> distinct_mset C" and "\<forall>C. C\<in># N  \<longrightarrow> \<not>tautology C"
  shows "(inter_from_stack S' {})  \<Turnstile>m N"
  using interpr_sat_all[OF assms, of "{}"] by auto

end