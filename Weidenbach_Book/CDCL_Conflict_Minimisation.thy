theory CDCL_Conflict_Minimisation
  imports Watched_Literals_Watch_List_Domain WB_More_Refinement
  IsaSAT_Trail
begin

no_notation Ref.update ("_ := _" 62)

declare cdcl\<^sub>W_restart_mset_state[simp]

type_synonym out_learned = \<open>nat clause_l\<close>

type_synonym out_learned_assn = \<open>uint32 array_list\<close>

abbreviation out_learned_assn :: \<open>out_learned \<Rightarrow> out_learned_assn \<Rightarrow> assn\<close> where
  \<open>out_learned_assn \<equiv> arl_assn unat_lit_assn\<close>

definition out_learned :: \<open>(nat, nat) ann_lits \<Rightarrow> nat clause option \<Rightarrow> out_learned \<Rightarrow> bool\<close> where
  \<open>out_learned M D out \<longleftrightarrow>
     out \<noteq> [] \<and>
     (D = None \<longrightarrow> length out = 1) \<and>
     (D \<noteq> None \<longrightarrow> mset (tl out) = filter_mset (\<lambda>L. get_level M L < count_decided M) (the D))\<close>

definition out_learned_confl :: \<open>(nat, nat) ann_lits \<Rightarrow> nat clause option \<Rightarrow> out_learned \<Rightarrow> bool\<close> where
  \<open>out_learned_confl M D out \<longleftrightarrow>
     out \<noteq> [] \<and> (D \<noteq> None \<and> mset out = the D)\<close>

lemma out_learned_Cons_None[simp]:
  \<open>out_learned (L # aa) None ao \<longleftrightarrow> out_learned aa None ao\<close>
  by (auto simp: out_learned_def)

lemma out_learned_tl_None[simp]:
  \<open>out_learned (tl aa) None ao \<longleftrightarrow> out_learned aa None ao\<close>
  by (auto simp: out_learned_def)

definition index_in_trail :: \<open>('v, 'a) ann_lits \<Rightarrow> 'v literal \<Rightarrow> nat\<close> where
  \<open>index_in_trail M L = index (map (atm_of o lit_of) (rev M)) (atm_of L)\<close>

lemma Propagated_in_trail_entailed:
  assumes
    invs: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (M, N, U, D)\<close> and
    in_trail: \<open>Propagated L C \<in> set M\<close>
  shows
    \<open>M \<Turnstile>as CNot (remove1_mset L C)\<close> and \<open>L \<in># C\<close> and \<open>N + U \<Turnstile>pm C\<close> and
    \<open>K \<in># remove1_mset L C \<Longrightarrow> index_in_trail M K < index_in_trail M L\<close>
proof -
  obtain M2 M1 where
    M: \<open>M = M2 @ Propagated L C # M1\<close>
    using split_list[OF in_trail] by metis
  have \<open>a @ Propagated L mark # b = trail (M, N, U, D) \<longrightarrow>
       b \<Turnstile>as CNot (remove1_mset L mark) \<and> L \<in># mark\<close> for L mark a b
    using invs
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
    by fast
  then have L_E: \<open>L \<in># C\<close> and M1_E: \<open>M1 \<Turnstile>as CNot (remove1_mset L C)\<close>
    unfolding M by force+
  then have M_E: \<open>M \<Turnstile>as CNot (remove1_mset L C)\<close>
    unfolding M by (simp add: true_annots_append_l)
  show \<open>M \<Turnstile>as CNot (remove1_mset L C)\<close> and \<open>L \<in># C\<close>
    using L_E M_E by fast+
  have \<open>set (get_all_mark_of_propagated (trail (M, N, U, D)))
    \<subseteq> set_mset (cdcl\<^sub>W_restart_mset.clauses (M, N, U, D))\<close>
    using invs
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
       cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def
    by fast
  then have \<open>C \<in># N + U\<close>
    using in_trail cdcl\<^sub>W_restart_mset.in_get_all_mark_of_propagated_in_trail[of C M]
    by (auto simp: clauses_def)
  then show \<open>N + U \<Turnstile>pm C\<close> by auto

  have n_d: \<open>no_dup M\<close>
    using invs
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by auto
  show \<open>index_in_trail M K < index_in_trail M L\<close> if K_C: \<open>K \<in># remove1_mset L C\<close>
  proof -
    have
      KL: \<open>atm_of K \<noteq> atm_of L\<close> and
      uK_M1: \<open>-K \<in> lits_of_l M1\<close> and
      L: \<open>L \<notin> lit_of ` (set M2 \<union> set M1)\<close> \<open>-L \<notin> lit_of ` (set M2 \<union> set M1)\<close>
      using M1_E K_C n_d unfolding M true_annots_true_cls_def_iff_negation_in_model
      by (auto dest!: multi_member_split simp: atm_of_eq_atm_of lits_of_def uminus_lit_swap
          Decided_Propagated_in_iff_in_lits_of_l)
    have L_M1: \<open>atm_of L \<notin> (atm_of \<circ> lit_of) ` set M1\<close>
      using L by (auto simp: image_Un atm_of_eq_atm_of)
    have K_M1: \<open>atm_of K \<in> (atm_of \<circ> lit_of) ` set M1\<close>
      using uK_M1 by (auto simp: lits_of_def image_image comp_def uminus_lit_swap)
    show ?thesis
      using KL L_M1 K_M1 unfolding index_in_trail_def M by (auto simp: index_append)
  qed
qed

inductive minimize_conflict_support :: \<open>('v, 'v clause) ann_lits \<Rightarrow> 'v clause \<Rightarrow> 'v clause \<Rightarrow> bool\<close>
  for M where
resolve_propa:
  \<open>minimize_conflict_support M (add_mset (-L) C) (C + remove1_mset L E)\<close>
  if \<open>Propagated L E \<in> set M\<close> |
remdups: \<open>minimize_conflict_support M (add_mset L C) C\<close>


lemma index_in_trail_uminus[simp]: \<open>index_in_trail M (-L) = index_in_trail M L\<close>
  by (auto simp: index_in_trail_def)

definition minimize_conflict_support_mes :: \<open>('v, 'v clause) ann_lits \<Rightarrow> 'v clause \<Rightarrow> nat multiset\<close>
where
  \<open>minimize_conflict_support_mes M C = index_in_trail M `# C\<close>

context
  fixes M :: \<open>('v, 'v clause) ann_lits\<close> and N U :: \<open>'v clauses\<close> and
    D :: \<open>'v clause option\<close>
  assumes invs: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (M, N, U, D)\<close>
begin

private lemma
   no_dup: \<open>no_dup M\<close> and
   consistent: \<open>consistent_interp (lits_of_l M)\<close>
  using invs unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
  cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
  by simp_all

lemma minimize_conflict_support_entailed_trail:
  assumes \<open>minimize_conflict_support M C E\<close> and \<open>M \<Turnstile>as CNot C\<close>
  shows \<open>M \<Turnstile>as CNot E\<close>
  using assms
proof (induction rule: minimize_conflict_support.induct)
  case (resolve_propa L E C) note in_trail = this(1) and M_C = this(2)
  then show ?case
    using Propagated_in_trail_entailed[OF invs in_trail] by (auto dest!: multi_member_split)
next
  case (remdups L C)
  then show ?case
    by auto
qed

lemma rtranclp_minimize_conflict_support_entailed_trail:
  assumes \<open>(minimize_conflict_support M)\<^sup>*\<^sup>* C E\<close> and \<open>M \<Turnstile>as CNot C\<close>
  shows \<open>M \<Turnstile>as CNot E\<close>
  using assms apply (induction rule: rtranclp_induct)
  subgoal by fast
  subgoal using minimize_conflict_support_entailed_trail by fast
  done

lemma minimize_conflict_support_mes:
  assumes \<open>minimize_conflict_support M C E\<close>
  shows \<open>minimize_conflict_support_mes M E < minimize_conflict_support_mes M C\<close>
  using assms unfolding minimize_conflict_support_mes_def
proof (induction rule: minimize_conflict_support.induct)
  case (resolve_propa L E C) note in_trail = this
  let ?f = \<open>\<lambda>xa. index (map (\<lambda>a. atm_of (lit_of a)) (rev M)) xa\<close>
  have \<open>?f (atm_of x) < ?f (atm_of L)\<close> if x: \<open>x \<in># remove1_mset L E\<close> for x
  proof -
    obtain M2 M1 where
      M: \<open>M = M2 @ Propagated L E # M1\<close>
      using split_list[OF in_trail] by metis
    have \<open>a @ Propagated L mark # b = trail (M, N, U, D) \<longrightarrow>
       b \<Turnstile>as CNot (remove1_mset L mark) \<and> L \<in># mark\<close> for L mark a b
      using invs
      unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
      by fast
    then have L_E: \<open>L \<in># E\<close> and M_E: \<open>M1 \<Turnstile>as CNot (remove1_mset L E)\<close>
      unfolding M by force+
    then have \<open>-x \<in> lits_of_l M1\<close>
      using x unfolding true_annots_true_cls_def_iff_negation_in_model by auto
    then have \<open>?f (atm_of x) < length M1\<close>
      using no_dup
      by (auto simp: M lits_of_def index_append Decided_Propagated_in_iff_in_lits_of_l
          uminus_lit_swap)
    moreover have \<open>?f (atm_of L) = length M1\<close>
      using no_dup unfolding M by (auto simp: index_append Decided_Propagated_in_iff_in_lits_of_l
          atm_of_eq_atm_of lits_of_def)
    ultimately show ?thesis by auto
  qed

  then show ?case by (auto simp: comp_def index_in_trail_def)
next
  case (remdups L C)
  then show ?case by auto
qed

lemma wf_minimize_conflict_support:
  shows \<open>wf {(C', C). minimize_conflict_support M C C'}\<close>
  apply (rule wf_if_measure_in_wf[of \<open>{(C', C). C' < C}\<close> _ \<open>minimize_conflict_support_mes M\<close>])
  subgoal using wf .
  subgoal using minimize_conflict_support_mes by auto
  done
end

lemma conflict_minimize_step:
  assumes
    \<open>NU \<Turnstile>p add_mset L C\<close> and
    \<open>NU \<Turnstile>p add_mset (-L) D\<close> and
    \<open>\<And>K'. K' \<in># C \<Longrightarrow> NU \<Turnstile>p add_mset (-K') D\<close>
  shows \<open>NU \<Turnstile>p D\<close>
proof -
  have \<open>NU \<Turnstile>p D + C\<close>
    using assms(1,2) true_clss_cls_or_true_clss_cls_or_not_true_clss_cls_or by blast
  then show ?thesis
    using assms(3)
  proof (induction C)
    case empty
    then show ?case
      using true_clss_cls_in true_clss_cls_or_true_clss_cls_or_not_true_clss_cls_or by fastforce
  next
    case (add x C) note IH =this(1) and NU_DC = this(2) and entailed = this(3)
    have \<open>NU \<Turnstile>p D + C + D\<close>
      using entailed[of x] NU_DC
        true_clss_cls_or_true_clss_cls_or_not_true_clss_cls_or[of NU \<open>-x\<close> \<open>D + C\<close> D]
      by auto
    then have \<open>NU \<Turnstile>p D + C\<close>
      by (metis add.comm_neutral diff_add_zero sup_subset_mset_def true_clss_cls_sup_iff_add)
    from IH[OF this] entailed show ?case by auto
  qed
qed

definition filter_to_poslev where
  \<open>filter_to_poslev M L D = filter_mset (\<lambda>K. index_in_trail M K < index_in_trail M L) D\<close>

lemma filter_to_poslev_uminus[simp]:
  \<open>filter_to_poslev M (-L) D = filter_to_poslev M L D\<close>
  by (auto simp: filter_to_poslev_def)

lemma filter_to_poslev_empty[simp]:
  \<open>filter_to_poslev M L {#} = {#}\<close>
  by (auto simp: filter_to_poslev_def)

lemma filter_to_poslev_mono:
  \<open>index_in_trail M K' \<le> index_in_trail M L \<Longrightarrow>
   filter_to_poslev M K' D \<subseteq># filter_to_poslev M L D\<close>
  unfolding filter_to_poslev_def
  by (auto simp: multiset_filter_mono2)

lemma filter_to_poslev_mono_entailement:
  \<open>index_in_trail M K' \<le> index_in_trail M L \<Longrightarrow>
   NU \<Turnstile>p filter_to_poslev M K' D \<Longrightarrow> NU \<Turnstile>p filter_to_poslev M L D\<close>
  by (metis (full_types) filter_to_poslev_mono subset_mset.le_iff_add true_clss_cls_mono_r)

lemma filter_to_poslev_mono_entailement_add_mset:
  \<open>index_in_trail M K' \<le> index_in_trail M L \<Longrightarrow>
   NU \<Turnstile>p add_mset J (filter_to_poslev M K' D) \<Longrightarrow> NU \<Turnstile>p add_mset J (filter_to_poslev M L D)\<close>
  by (metis filter_to_poslev_mono mset_subset_eq_add_mset_cancel subset_mset.le_iff_add
      true_clss_cls_mono_r)

lemma conflict_minimize_intermediate_step:
  assumes
    \<open>NU \<Turnstile>p add_mset L C\<close> and
    K'_C: \<open>\<And>K'. K' \<in># C \<Longrightarrow> NU \<Turnstile>p add_mset (-K') D \<or> K' \<in># D\<close>
  shows \<open>NU \<Turnstile>p add_mset L D\<close>
proof -
  have \<open>NU \<Turnstile>p add_mset L C + D\<close>
    using assms(1) true_clss_cls_mono_r by blast
  then show ?thesis
    using assms(2)
  proof (induction C)
    case empty
    then show ?case
      using true_clss_cls_in true_clss_cls_or_true_clss_cls_or_not_true_clss_cls_or by fastforce
  next
    case (add x C) note IH =this(1) and NU_DC = this(2) and entailed = this(3)

    have 1: \<open>NU \<Turnstile>p add_mset x (add_mset L (D + C))\<close>
      using NU_DC by (auto simp: add_mset_commute ac_simps)
    moreover have \<open>x \<in># D \<Longrightarrow> NU \<Turnstile>p add_mset L (D + C + D)\<close>
      using 1 apply (auto dest!: multi_member_split)(* TODO Proof *)
      by (metis (no_types, hide_lams) ab_semigroup_add_class.add.commute true_clss_cls_mono_r'
          union_mset_add_mset_right)
    ultimately have \<open>NU \<Turnstile>p add_mset L (D + C + D)\<close>
      using entailed[of x] NU_DC
        true_clss_cls_or_true_clss_cls_or_not_true_clss_cls_or[of NU \<open>-x\<close> \<open>add_mset L D + C\<close> D]
      by auto
    moreover have \<open>remdups_mset (add_mset L (D + C + D)) = remdups_mset (add_mset L (C + D))\<close>
      by (auto simp: remdups_mset_def)
    ultimately have \<open>NU \<Turnstile>p add_mset L C + D\<close>
      apply (subst  true_clss_cls_remdups_mset[symmetric])
      apply (subst (asm) true_clss_cls_remdups_mset[symmetric])
      by simp
    from IH[OF this] entailed show ?case by auto
  qed
qed

lemma conflict_minimize_intermediate_step_filter_to_poslev:
  assumes
    lev_K_L: \<open>\<And>K'. K' \<in># C \<Longrightarrow> index_in_trail M K' < index_in_trail M L\<close> and
    NU_LC: \<open>NU \<Turnstile>p add_mset L C\<close> and
    K'_C: \<open>\<And>K'. K' \<in># C \<Longrightarrow> NU \<Turnstile>p add_mset (-K') (filter_to_poslev M L D) \<or>
     K' \<in># filter_to_poslev M L D\<close>
  shows \<open>NU \<Turnstile>p add_mset L (filter_to_poslev M L D)\<close>
proof -
  have C_entailed: \<open>K' \<in># C \<Longrightarrow> NU \<Turnstile>p add_mset (-K') (filter_to_poslev M L D) \<or>
   K' \<in># filter_to_poslev M L D\<close> for K'
    using filter_to_poslev_mono[of M K' L D] lev_K_L[of K'] K'_C[of K']
      true_clss_cls_mono_r[of _ \<open> add_mset (- K') (filter_to_poslev M K' D)\<close> ]
    by (auto simp: mset_subset_eq_exists_conv)
  show ?thesis
    using conflict_minimize_intermediate_step[OF NU_LC C_entailed]  by fast
qed

datatype minimize_status = SEEN_FAILED | SEEN_REMOVABLE | SEEN_UNKNOWN

instance minimize_status :: heap
proof standard
  let ?f = \<open>\<lambda>s. case s of SEEN_FAILED \<Rightarrow> (0 :: nat) | SEEN_REMOVABLE \<Rightarrow> 1 | SEEN_UNKNOWN \<Rightarrow> 2\<close>
  have \<open>inj ?f\<close>
    by (auto simp: inj_def split: minimize_status.splits)
  then show \<open>\<exists>to_nat. inj (to_nat :: minimize_status \<Rightarrow> nat)\<close>
    by blast
qed

instantiation minimize_status :: default
begin
  definition default_minimize_status where
    \<open>default_minimize_status = SEEN_UNKNOWN\<close>

instance by standard
end

type_synonym 'v conflict_min_analyse = \<open>('v literal \<times> 'v clause) list\<close>
type_synonym 'v conflict_min_cach = \<open>'v \<Rightarrow> minimize_status\<close>

definition get_literal_and_remove_of_analyse
   :: \<open>'v conflict_min_analyse \<Rightarrow> ('v literal \<times> 'v conflict_min_analyse) nres\<close> where
  \<open>get_literal_and_remove_of_analyse analyse =
    SPEC(\<lambda>(L, ana). L \<in># snd (hd analyse) \<and> tl ana = tl analyse \<and> ana \<noteq> [] \<and>
         hd ana = (fst (hd analyse), snd (hd (analyse)) - {#L#}))\<close>

definition mark_failed_lits
  :: \<open>_ \<Rightarrow> 'v conflict_min_analyse \<Rightarrow> 'v conflict_min_cach \<Rightarrow> 'v conflict_min_cach nres\<close>
where
  \<open>mark_failed_lits NU analyse cach = SPEC(\<lambda>cach'.
     (\<forall>L. cach' L = SEEN_REMOVABLE \<longrightarrow> cach L = SEEN_REMOVABLE))\<close>


definition conflict_min_analysis_inv
  :: \<open>('v, 'a) ann_lits \<Rightarrow> 'v conflict_min_cach \<Rightarrow> 'v clauses \<Rightarrow> 'v clause \<Rightarrow> bool\<close>
where
  \<open>conflict_min_analysis_inv M cach NU D \<longleftrightarrow>
    (\<forall>L. -L \<in> lits_of_l M \<longrightarrow> cach (atm_of L) = SEEN_REMOVABLE \<longrightarrow>
      set_mset NU \<Turnstile>p add_mset (-L) (filter_to_poslev M L D))\<close>

lemma conflict_min_analysis_inv_update_removable:
  \<open>no_dup M \<Longrightarrow> -L \<in> lits_of_l M \<Longrightarrow>
      conflict_min_analysis_inv M (cach(atm_of L := SEEN_REMOVABLE)) NU D \<longleftrightarrow>
      conflict_min_analysis_inv M cach NU D \<and> set_mset NU \<Turnstile>p add_mset (-L) (filter_to_poslev M L D)\<close>
  by (auto simp: conflict_min_analysis_inv_def atm_of_eq_atm_of dest: no_dup_consistentD)


lemma conflict_min_analysis_inv_update_failed:
  \<open>conflict_min_analysis_inv M cach NU D \<Longrightarrow>
   conflict_min_analysis_inv M (cach(L := SEEN_FAILED)) NU D\<close>
  by (auto simp: conflict_min_analysis_inv_def)

fun conflict_min_analysis_stack
  :: \<open>('v, 'a) ann_lits \<Rightarrow> 'v clauses \<Rightarrow> 'v clause \<Rightarrow> 'v conflict_min_analyse \<Rightarrow> bool\<close>
where
  \<open>conflict_min_analysis_stack M NU D [] \<longleftrightarrow> True\<close> |
  \<open>conflict_min_analysis_stack M NU D ((L, E) # []) \<longleftrightarrow> True\<close> |
  \<open>conflict_min_analysis_stack M NU D ((L, E) # (L', E') # analyse) \<longleftrightarrow>
     (\<exists>C. set_mset NU \<Turnstile>p add_mset (-L') C \<and>
       (\<forall>K\<in>#C-add_mset L E'. set_mset NU \<Turnstile>p (filter_to_poslev M L' D) + {#-K#} \<or>
           K \<in># filter_to_poslev M L' D) \<and>
       (\<forall>K\<in>#C. index_in_trail M K < index_in_trail M L') \<and>
       E' \<subseteq># C) \<and>
     -L' \<in> lits_of_l M \<and>
     index_in_trail M L < index_in_trail M L' \<and>
     conflict_min_analysis_stack M NU D ((L', E') # analyse)\<close>

lemma conflict_min_analysis_stack_change_hd:
  \<open>conflict_min_analysis_stack M NU D ((L, E) # ana) \<Longrightarrow>
     conflict_min_analysis_stack M NU D ((L, E') # ana)\<close>
  by (cases ana, auto)

fun conflict_min_analysis_stack_hd
  :: \<open>('v, 'a) ann_lits \<Rightarrow> 'v clauses \<Rightarrow> 'v clause \<Rightarrow> 'v conflict_min_analyse \<Rightarrow> bool\<close>
where
  \<open>conflict_min_analysis_stack_hd M NU D [] \<longleftrightarrow> True\<close> |
  \<open>conflict_min_analysis_stack_hd M NU D ((L, E) # _) \<longleftrightarrow>
     (\<exists>C. set_mset NU \<Turnstile>p add_mset (-L) C \<and>
     (\<forall>K\<in>#C. index_in_trail M K < index_in_trail M L) \<and> E \<subseteq># C \<and> -L \<in> lits_of_l M \<and>
     (\<forall>K\<in>#C-E. set_mset NU \<Turnstile>p (filter_to_poslev M L D) + {#-K#} \<or> K \<in># filter_to_poslev M L D))\<close>

lemma conflict_min_analysis_stack_tl:
  \<open>conflict_min_analysis_stack M NU D analyse \<Longrightarrow> conflict_min_analysis_stack M NU D (tl analyse)\<close>
  by (cases \<open>(M, NU, D, analyse)\<close> rule: conflict_min_analysis_stack.cases) auto

definition lit_redundant_inv
  :: \<open>('v, 'v clause) ann_lits \<Rightarrow> 'v clauses \<Rightarrow> 'v clause \<Rightarrow> 'v conflict_min_analyse \<Rightarrow>
        'v conflict_min_cach \<times> 'v conflict_min_analyse \<times> bool \<Rightarrow> bool\<close> where
  \<open>lit_redundant_inv M NU D init_analyse = (\<lambda>(cach, analyse, b).
           conflict_min_analysis_inv M cach NU D \<and>
           (analyse \<noteq> [] \<longrightarrow> fst (hd init_analyse) = fst (last analyse)) \<and>
           (analyse = [] \<longrightarrow> b \<longrightarrow> cach (atm_of (fst (hd init_analyse))) = SEEN_REMOVABLE) \<and>
           conflict_min_analysis_stack M NU D analyse \<and>
           conflict_min_analysis_stack_hd M NU D analyse)\<close>

definition lit_redundant_rec :: \<open>('v, 'v clause) ann_lits \<Rightarrow> 'v clauses \<Rightarrow> 'v clause \<Rightarrow>
     'v conflict_min_cach \<Rightarrow> 'v conflict_min_analyse \<Rightarrow>
      ('v conflict_min_cach \<times> 'v conflict_min_analyse \<times> bool) nres\<close>
where
  \<open>lit_redundant_rec M NU D cach analysis =
      WHILE\<^sub>T
        (\<lambda>(cach, analyse, b). analyse \<noteq> [])
        (\<lambda>(cach, analyse, b). do {
            ASSERT(analyse \<noteq> []);
            ASSERT(-fst (hd analyse) \<in> lits_of_l M);
            if snd (hd analyse) = {#}
            then
               RETURN(cach (atm_of (fst (hd analyse)) := SEEN_REMOVABLE), tl analyse, True)
            else do {
               (L, analyse) \<leftarrow> get_literal_and_remove_of_analyse analyse;
               ASSERT(-L \<in> lits_of_l M);
               b \<leftarrow> RES UNIV;
               if (get_level M L = 0 \<or> cach (atm_of L) = SEEN_REMOVABLE \<or> L \<in># D)
               then RETURN (cach, analyse, False)
               else if b \<or> cach (atm_of L) = SEEN_FAILED
               then do {
                  cach \<leftarrow> mark_failed_lits NU analyse cach;
                  RETURN (cach, [], False)
               }
               else do {
                  C \<leftarrow> get_propagation_reason M (-L);
                  case C of
                    Some C \<Rightarrow> RETURN (cach, (L, C - {#-L#}) # analyse, False)
                  | None \<Rightarrow> do {
                      cach \<leftarrow> mark_failed_lits NU analyse cach;
                      RETURN (cach, [], False)
                  }
              }
          }
        })
       (cach, analysis, False)\<close>

definition lit_redundant_rec_spec where
  \<open>lit_redundant_rec_spec M NU D L =
    SPEC(\<lambda>(cach, analysis, b). (b \<longrightarrow> NU \<Turnstile>pm add_mset (-L) (filter_to_poslev M L D)) \<and>
     conflict_min_analysis_inv M cach NU D)\<close>

lemma lit_redundant_rec_spec:
  fixes L :: \<open>'v literal\<close>
  assumes invs: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (M, N + NE, U + UE, D')\<close>
  assumes
    init_analysis: \<open>init_analysis = [(L, C)]\<close> and
    in_trail: \<open>Propagated (-L) (add_mset (-L) C) \<in> set M\<close> and
    \<open>conflict_min_analysis_inv M cach (N + NE + U + UE) D\<close> and
    L_D: \<open>L \<in># D\<close> and
    M_D: \<open>M \<Turnstile>as CNot D\<close>
  shows
    \<open>lit_redundant_rec M (N + U) D cach init_analysis \<le>
      lit_redundant_rec_spec M (N + U + NE + UE) D L\<close>
proof -
  let ?N = \<open>N + NE + U + UE\<close>
  obtain M2 M1 where
    M: \<open>M = M2 @ Propagated (- L) (add_mset (- L) C) # M1\<close>
    using split_list[OF in_trail] by (auto 5 5)
  have \<open>a @ Propagated L mark # b = trail (M, N + NE, U + UE, D') \<longrightarrow>
       b \<Turnstile>as CNot (remove1_mset L mark) \<and> L \<in># mark\<close> for L mark a b
    using invs
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
       cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
    by fast
  then have \<open>M1 \<Turnstile>as CNot C\<close>
    by (force simp: M)
  then have M_C: \<open>M \<Turnstile>as CNot C\<close>
    unfolding M by (simp add: true_annots_append_l)
  have \<open>set (get_all_mark_of_propagated (trail (M, N + NE, U + UE, D')))
    \<subseteq> set_mset (cdcl\<^sub>W_restart_mset.clauses (M, N + NE, U + UE, D'))\<close>
    using invs
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
       cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def
    by fast
  then have \<open>add_mset (-L) C \<in># ?N\<close>
    using in_trail cdcl\<^sub>W_restart_mset.in_get_all_mark_of_propagated_in_trail[of \<open>add_mset (-L) C\<close> M]
    by (auto simp: clauses_def)
  then have NU_C: \<open>?N \<Turnstile>pm add_mset (- L) C\<close>
    by auto
  have n_d: \<open>no_dup M\<close>
    using invs
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
       cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by auto

  let ?f = \<open>\<lambda>analysis. fold_mset (op +) D (snd `# mset analysis)\<close>
  define I' where
    \<open>I' = (\<lambda>(cach :: 'v conflict_min_cach, analysis :: 'v conflict_min_analyse, b::bool).
        lit_redundant_inv M ?N D init_analysis (cach, analysis, b) \<and> M \<Turnstile>as CNot (?f analysis))\<close>
  define R where
    \<open>R = {((cach :: 'v conflict_min_cach, analysis :: 'v conflict_min_analyse, b::bool),
           (cach' :: 'v conflict_min_cach, analysis' :: 'v conflict_min_analyse, b' :: bool)).
           (analysis' \<noteq> [] \<and> (minimize_conflict_support M) (?f analysis') (?f analysis)) \<or>
           (analysis' \<noteq> [] \<and> analysis = tl analysis' \<and> snd (hd analysis') = {#}) \<or>
           (analysis' \<noteq> [] \<and> analysis = [])}\<close>
  have wf_R: \<open>wf R\<close>
  proof -
    have R: \<open>R =
              {((cach, analysis, b), (cach', analysis', b')).
                 analysis' \<noteq> [] \<and>analysis = []} \<union>
              ({((cach, analysis, b), (cach', analysis', b')).
                  analysis' \<noteq> [] \<and> (minimize_conflict_support M) (?f analysis') (?f analysis)} \<union>
              {((cach, analysis, b), (cach', analysis', b')).
                  analysis' \<noteq> [] \<and> analysis = tl analysis' \<and> snd (hd analysis') = {#}})\<close>
      (is \<open>_ = ?end \<union> (?Min \<union> ?ana)\<close>)
      unfolding R_def by auto
    have 1: \<open>wf {((cach:: 'v conflict_min_cach, analysis:: 'v conflict_min_analyse, b::bool),
         (cach':: 'v conflict_min_cach, analysis':: 'v conflict_min_analyse, b'::bool)).
       length analysis < length analysis'}\<close>
      using wf_if_measure_f[of \<open>measure length\<close>, of \<open>\<lambda>(_, xs, _). xs\<close>] apply auto
      apply (rule subst[of _ _ wf])
       prefer 2 apply assumption
      apply auto
      done

    have 2: \<open>wf {(C', C).minimize_conflict_support M C C'}\<close>
      by (rule wf_minimize_conflict_support[OF invs])
    from wf_if_measure_f[OF this, of ?f]
    have 2: \<open>wf {(C', C). minimize_conflict_support M (?f C) (?f C')}\<close>
      by auto
    from wf_fst_wf_pair[OF this, where 'b = bool]
    have \<open>wf {((analysis':: 'v conflict_min_analyse, _ :: bool),
               (analysis:: 'v conflict_min_analyse,  _:: bool)).
            (minimize_conflict_support M) (?f analysis) (?f analysis')}\<close>
      by blast
    from wf_snd_wf_pair[OF this, where 'b = \<open>'v conflict_min_cach\<close>]
    have \<open>wf {((M' :: 'v conflict_min_cach, N'), Ma, N).
      (case N' of
       (analysis' :: 'v conflict_min_analyse, _ :: bool) \<Rightarrow>
         \<lambda>(analysis, _).
            minimize_conflict_support M (fold_mset op + D (snd `# mset analysis))
              (fold_mset op + D (snd `# mset analysis'))) N}\<close>
      by blast
    then have wf_Min: \<open>wf ?Min\<close>
      apply (rule wf_subset)
      by auto
    have wf_ana: \<open>wf ?ana\<close>
      by (rule wf_subset[OF 1])  auto
    have wf: \<open>wf (?Min \<union> ?ana)\<close>
      apply (rule wf_union_compatible)
      subgoal by (rule wf_Min)
      subgoal by (rule wf_ana)
      subgoal by (auto elim!: neq_NilE)
      done
    have wf_end: \<open>wf ?end\<close>
    proof (rule ccontr)
      assume \<open>\<not> ?thesis\<close>
      then obtain f where f: \<open>(f (Suc i), f i) \<in> ?end\<close> for i
        unfolding wf_iff_no_infinite_down_chain by auto
      have \<open>fst (snd (f (Suc 0))) = []\<close>
        using f[of 0] by auto
      moreover have \<open>fst (snd (f (Suc 0))) \<noteq> []\<close>
        using f[of 1] by auto
      ultimately show False by blast
    qed
    show ?thesis
      unfolding R
      apply (rule wf_Un)
      subgoal by (rule wf_end)
      subgoal by (rule wf)
      subgoal by auto
      done
  qed
  have uL_M: \<open>- L \<in> lits_of_l M\<close>
    using in_trail by (force simp: lits_of_def)
  then have init_I: \<open>lit_redundant_inv M ?N D init_analysis (cach, init_analysis, False)\<close>
    using assms NU_C  Propagated_in_trail_entailed[OF invs in_trail]
    unfolding lit_redundant_inv_def
    by (auto simp: ac_simps)

  have \<open>(minimize_conflict_support M) D (remove1_mset L (C + D))\<close>
    using minimize_conflict_support.resolve_propa[OF in_trail, of \<open>remove1_mset L D\<close>] L_D
    by (auto simp: ac_simps)

  then have init_I': \<open>I' (cach, init_analysis, False)\<close>
    using M_D L_D M_C init_I unfolding I'_def by (auto simp: init_analysis)

  have hd_M: \<open>- fst (hd analyse) \<in> lits_of_l M\<close>
    if
      inv_I': \<open>I' s\<close> and
      s: \<open>s = (cach, s')\<close> \<open>s' = (analyse, ba)\<close> and
      nempty: \<open>analyse \<noteq> []\<close>
    for analyse s s' ba cach
  proof -
    have
      cach: \<open>conflict_min_analysis_inv M cach ?N D\<close> and
      ana: \<open>conflict_min_analysis_stack M ?N D analyse\<close> and
      stack: \<open>conflict_min_analysis_stack M ?N D analyse\<close> and
      stack_hd: \<open>conflict_min_analysis_stack_hd M ?N D analyse\<close> and
      last_analysis: \<open>analyse \<noteq> [] \<longrightarrow> fst (last analyse) = fst (hd init_analysis)\<close> and
      b: \<open>analyse = [] \<longrightarrow> ba \<longrightarrow> cach (atm_of (fst (hd init_analysis))) = SEEN_REMOVABLE\<close>
      using inv_I' unfolding lit_redundant_inv_def s I'_def by auto
    show ?thesis
      using stack_hd nempty by (cases analyse) auto
  qed

  have all_removed: \<open>lit_redundant_inv M ?N D init_analysis
       (cach(atm_of (fst (hd analysis)) := SEEN_REMOVABLE), tl analysis, True)\<close> (is ?I) and
     all_removed_I': \<open>I' (cach(atm_of (fst (hd analysis)) := SEEN_REMOVABLE), tl analysis, True)\<close>
       (is ?I')
    if
      inv_I': \<open>I' s\<close>
      \<open>case s of (cach, analyse, b) \<Rightarrow> analyse \<noteq> []\<close> and
      s: \<open>s = (cach, s')\<close>
         \<open>s' = (analysis, b)\<close> and
      nemtpy_stack: \<open>analysis \<noteq> []\<close> and
      finished: \<open>snd (hd analysis) = {#}\<close>
    for s cach s' analysis b
  proof -
    obtain L ana' where analysis: \<open>analysis = (L, {#}) # ana'\<close>
      using nemtpy_stack finished by (cases analysis)  auto
    have
      cach: \<open>conflict_min_analysis_inv M cach ?N D\<close> and
      ana: \<open>conflict_min_analysis_stack M ?N D analysis\<close> and
      stack: \<open>conflict_min_analysis_stack M ?N D analysis\<close> and
      stack_hd: \<open>conflict_min_analysis_stack_hd M ?N D analysis\<close> and
      last_analysis: \<open>analysis \<noteq> [] \<longrightarrow> fst (last analysis) = fst (hd init_analysis)\<close> and
      b: \<open>analysis = [] \<longrightarrow> b \<longrightarrow> cach (atm_of (fst (hd init_analysis))) = SEEN_REMOVABLE\<close>
      using inv_I' unfolding lit_redundant_inv_def s I'_def by auto
    obtain C where
       NU_C: \<open>?N \<Turnstile>pm add_mset (-L) C\<close> and
       IH: \<open>\<And>K. K \<in># C \<Longrightarrow> ?N \<Turnstile>pm add_mset (-K) (filter_to_poslev M L D) \<or>
         K \<in># filter_to_poslev M L D\<close> and
       index_K: \<open>K\<in>#C \<Longrightarrow> index_in_trail M K < index_in_trail M L\<close> and
       L_M: \<open>-L \<in> lits_of_l M\<close> for K
      using stack_hd unfolding analysis by auto

    have NU_D: \<open>?N \<Turnstile>pm add_mset (- fst (hd analysis)) (filter_to_poslev M (fst (hd analysis)) D)\<close>
      using conflict_minimize_intermediate_step_filter_to_poslev[OF _ NU_C _, simplified, OF index_K]
        IH
      unfolding analysis by auto
    have ana': \<open>conflict_min_analysis_stack M ?N D (tl analysis)\<close>
      using ana by (auto simp: conflict_min_analysis_stack_tl)
    have \<open>-fst (hd analysis) \<in> lits_of_l M\<close>
      using L_M by (auto simp: analysis I'_def s ana)
    then have cach':
      \<open>conflict_min_analysis_inv M (cach(atm_of (fst (hd analysis)) := SEEN_REMOVABLE)) ?N D\<close>
      using NU_D n_d by (auto simp: conflict_min_analysis_inv_update_removable cach)
    have stack_hd': \<open>conflict_min_analysis_stack_hd M ?N D ana'\<close>
    proof (cases \<open>ana' = []\<close>)
      case True
      then show ?thesis by auto
    next
      case False
      then obtain L' C' ana'' where ana'': \<open>ana' = (L', C') # ana''\<close>
        by (cases ana'; cases \<open>hd ana'\<close>) auto
      then obtain E' where
         NU_E': \<open>?N \<Turnstile>pm add_mset (- L') E'\<close> and
         \<open>\<forall>K\<in>#E' - add_mset L C'. ?N \<Turnstile>pm add_mset (- K) (filter_to_poslev M L' D) \<or>
           K \<in># filter_to_poslev M L' D\<close> and
         index_C': \<open>\<forall>K\<in>#E'. index_in_trail M K < index_in_trail M L'\<close> and
         index_L'_L: \<open>index_in_trail M L < index_in_trail M L'\<close> and
         C'_E': \<open>C' \<subseteq># E'\<close> and
         uL'_M: \<open>- L' \<in> lits_of_l M\<close>
         using stack by (auto simp: analysis ana'')
       moreover have \<open>?N \<Turnstile>pm add_mset (- L) (filter_to_poslev M L D)\<close>
         using NU_D analysis by auto
       moreover have \<open>K \<in># E' - C' \<Longrightarrow> K \<in># E' - add_mset L C' \<or> K = L\<close> for K
         by (cases \<open>L \<in># E'\<close>)
           (fastforce simp: minus_notin_trivial dest!: multi_member_split[of L]
             dest: in_remove1_msetI)+
       moreover have \<open>K \<in># E' - C' \<Longrightarrow> index_in_trail M K \<le> index_in_trail M L'\<close> for K
         by (meson in_diffD index_C' less_or_eq_imp_le)
       ultimately have \<open>K \<in># E' - C' \<Longrightarrow> ?N \<Turnstile>pm add_mset (- K) (filter_to_poslev M L' D) \<or>
             K \<in># filter_to_poslev M L' D\<close> for K
         using filter_to_poslev_mono_entailement_add_mset[of M K L']
           filter_to_poslev_mono[of M L L']
         by fastforce
       then show ?thesis
         using NU_E' uL'_M index_C' C'_E' unfolding ana'' by (auto intro!: exI[of _ E'])
    qed

    have \<open>fst (hd init_analysis) = fst (last (tl analysis))\<close> if \<open>tl analysis \<noteq> []\<close>
      using last_analysis tl_last[symmetric, OF that] that unfolding ana' by auto
    then show ?I
      using ana' cach' last_analysis stack_hd' unfolding lit_redundant_inv_def
      by (auto simp: analysis)
    then show ?I'
      using inv_I' unfolding I'_def s by (auto simp: analysis)
  qed
  have all_removed_R:
      \<open>((cach(atm_of (fst (hd analyse)) := SEEN_REMOVABLE), tl analyse, True), s) \<in> R\<close>
    if
      s: \<open>s = (cach, s')\<close> \<open>s' = (analyse, b)\<close> and
      nempty: \<open>analyse \<noteq> []\<close> and
      finished: \<open>snd (hd analyse) = {#}\<close>
    for s cach s' analyse b
    using nempty finished unfolding R_def s by auto
  have
    seen_removable_inv: \<open>lit_redundant_inv M ?N D init_analysis (cach, ana, False)\<close> (is ?I) and
    seen_removable_I': \<open>I' (cach, ana, False)\<close> (is ?I') and
    seen_removable_R: \<open>((cach, ana, False), s) \<in> R\<close> (is ?R)
    if
      inv_I': \<open>I' s\<close> and
      cond: \<open>case s of (cach, analyse, b) \<Rightarrow> analyse \<noteq> []\<close> and
      s: \<open>s = (cach, s')\<close> \<open>s' = (analyse, b)\<close> \<open>x = (L, ana)\<close> and
      nemtpy_stack: \<open>analyse \<noteq> []\<close> and
      \<open>snd (hd analyse) \<noteq> {#}\<close> and
      next_lit: \<open>case x of
        (L, ana) \<Rightarrow> L \<in># snd (hd analyse) \<and> tl ana = tl analyse \<and> ana \<noteq> [] \<and>
          hd ana = (fst (hd analyse), remove1_mset L (snd (hd analyse)))\<close> and
      lev0_removable: \<open>get_level M L = 0 \<or> cach (atm_of L) = SEEN_REMOVABLE \<or> L \<in># D\<close>
    for s cach s' analyse b x L ana
  proof -
    obtain K C ana' where analysis: \<open>analyse = (K, C) # ana'\<close>
      using nemtpy_stack by (cases analyse) auto
    have ana': \<open>ana = (K, remove1_mset L C) # ana'\<close> and L_C: \<open>L \<in># C\<close>
      using next_lit unfolding s by (cases ana; auto simp: analysis)+
    have
      cach: \<open>conflict_min_analysis_inv M cach (?N) D\<close> and
      ana: \<open>conflict_min_analysis_stack M ?N D analyse\<close> and
      stack: \<open>conflict_min_analysis_stack M ?N D analyse\<close> and
      stack_hd: \<open>conflict_min_analysis_stack_hd M ?N D analyse\<close> and
      last_analysis: \<open>analyse \<noteq> [] \<longrightarrow> fst (last analyse) = fst (hd init_analysis)\<close> and
      b: \<open>analyse = [] \<longrightarrow> b \<longrightarrow> cach (atm_of (fst (hd init_analysis))) = SEEN_REMOVABLE\<close>
      using inv_I' unfolding lit_redundant_inv_def s I'_def by auto

    have last_analysis': \<open>ana \<noteq> [] \<Longrightarrow> fst (hd init_analysis) = fst (last ana)\<close>
      using last_analysis next_lit unfolding analysis s
      by (cases ana) (auto split: if_splits)
    have uL_M: \<open>-L \<in> lits_of_l M\<close>
      using inv_I' L_C unfolding analysis ana s I'_def
      by (auto dest!: multi_member_split)
    have uK_M: \<open>- K \<in> lits_of_l M\<close>
      using stack_hd unfolding analysis by auto
    consider
      (lev0) \<open>get_level M L = 0\<close> |
      (Removable) \<open>cach (atm_of L) = SEEN_REMOVABLE\<close> |
      (in_D) \<open>L \<in># D\<close>
      using lev0_removable by fast
    then have H: \<open>\<exists>CK. ?N \<Turnstile>pm add_mset (- K) CK \<and>
           (\<forall>Ka\<in>#CK - remove1_mset L C. ?N \<Turnstile>pm  (filter_to_poslev M K D) + {#- Ka#} \<or>
             Ka \<in># filter_to_poslev M K D) \<and>
           (\<forall>Ka\<in>#CK. index_in_trail M Ka < index_in_trail M K) \<and>
           remove1_mset L C \<subseteq># CK\<close>
      (is \<open>\<exists>C. ?P C\<close>)
    proof cases
      case Removable
      then have L: \<open>?N \<Turnstile>pm add_mset (- L) (filter_to_poslev M L D)\<close>
        using cach uL_M unfolding conflict_min_analysis_inv_def by auto
      obtain CK where
        \<open>?N \<Turnstile>pm add_mset (- K) CK\<close> and
        \<open>\<forall>K'\<in>#CK - C. ?N \<Turnstile>pm (filter_to_poslev M K D) + {#- K'#} \<or> K' \<in># filter_to_poslev M K D\<close> and
        index_CK: \<open>\<forall>Ka\<in>#CK. index_in_trail M Ka < index_in_trail M K\<close> and
        C_CK: \<open>C \<subseteq># CK\<close>
        using stack_hd unfolding analysis by auto
      moreover have \<open>remove1_mset L C \<subseteq># CK\<close>
        using C_CK by (meson diff_subset_eq_self subset_mset.dual_order.trans)
      moreover have \<open>index_in_trail M L < index_in_trail M K\<close>
        using index_CK C_CK L_C unfolding analysis ana' by auto
      moreover have index_CK': \<open>\<forall>Ka\<in>#CK. index_in_trail M Ka \<le> index_in_trail M K\<close>
        using index_CK by auto
      ultimately have \<open>?P CK\<close>
         using filter_to_poslev_mono_entailement_add_mset[of M _ _]
           filter_to_poslev_mono[of M K L]
         using L L_C C_CK by (auto simp: minus_remove1_mset_if)
      then show ?thesis by blast
    next
      assume lev0: \<open>get_level M L = 0\<close>
      have \<open>M \<Turnstile>as CNot (?f analyse)\<close>
        using inv_I' unfolding I'_def s by auto
      then have \<open>-L \<in> lits_of_l M\<close>
        using next_lit unfolding analysis s by (auto dest: multi_member_split)
      then have \<open>?N \<Turnstile>pm {#-L#}\<close>
        using lev0 cdcl\<^sub>W_restart_mset.literals_of_level0_entailed[OF invs, of \<open>-L\<close>]
        by (auto simp: clauses_def ac_simps)
      moreover obtain CK where
        \<open>?N \<Turnstile>pm add_mset (- K) CK\<close> and
        \<open>\<forall>K'\<in>#CK - C. ?N \<Turnstile>pm (filter_to_poslev M K D) + {#- K'#} \<or> K' \<in># filter_to_poslev M K D\<close> and
        \<open>\<forall>Ka\<in>#CK. index_in_trail M Ka < index_in_trail M K\<close> and
        C_CK: \<open>C \<subseteq># CK\<close>
        using stack_hd unfolding analysis by auto
      moreover have \<open>remove1_mset L C \<subseteq># CK\<close>
        using C_CK by (meson diff_subset_eq_self subset_mset.order_trans)
      ultimately have \<open>?P CK\<close>
        by (auto simp: minus_remove1_mset_if intro: conflict_minimize_intermediate_step)
      then show ?thesis by blast
    next
      case in_D
      obtain CK where
        \<open>?N \<Turnstile>pm add_mset (- K) CK\<close> and
        \<open>\<forall>Ka\<in>#CK - C. ?N \<Turnstile>pm (filter_to_poslev M K D) + {#- Ka#} \<or> Ka \<in># filter_to_poslev M K D\<close> and
        index_CK: \<open>\<forall>Ka\<in>#CK. index_in_trail M Ka < index_in_trail M K\<close> and
        C_CK: \<open>C \<subseteq># CK\<close>
        using stack_hd unfolding analysis by auto
      moreover have \<open>remove1_mset L C \<subseteq># CK\<close>
        using C_CK by (meson diff_subset_eq_self subset_mset.order_trans)
      moreover have \<open>L \<in># filter_to_poslev M K D\<close>
        using in_D L_C index_CK C_CK by (fastforce simp: filter_to_poslev_def)

      ultimately have \<open>?P CK\<close>
        using in_D
         using filter_to_poslev_mono_entailement_add_mset[of M L K]
         by (auto simp: minus_remove1_mset_if dest!:
             intro: conflict_minimize_intermediate_step)
      then show ?thesis by blast
    qed note H = this
    have stack': \<open>conflict_min_analysis_stack M ?N D ana\<close>
      using stack unfolding ana' analysis by (cases ana') auto
    have stack_hd': \<open>conflict_min_analysis_stack_hd M ?N D ana\<close>
      using H uL_M uK_M unfolding ana' by auto

    show ?I
      using last_analysis' cach stack' stack_hd' unfolding lit_redundant_inv_def s
      by auto
    have \<open>M \<Turnstile>as CNot (?f ana)\<close>
      using inv_I' unfolding I'_def s ana analysis ana'
      by (cases \<open>L \<in># C\<close>) (auto dest!: multi_member_split)
    then show ?I'
      using inv_I' \<open>?I\<close> unfolding I'_def s by auto

    show ?R
      using next_lit
      unfolding R_def s by (auto simp: ana' analysis dest!: multi_member_split
          intro: minimize_conflict_support.intros)
  qed
  have
    failed_I: \<open>lit_redundant_inv M ?N D init_analysis
       (cach', [], False)\<close> (is ?I) and
    failed_I': \<open>I' (cach', [], False)\<close> (is ?I') and
    failed_R: \<open>((cach', [], False), s) \<in> R\<close> (is ?R)
    if
      inv_I': \<open>I' s\<close> and
      cond: \<open>case s of (cach, analyse, b) \<Rightarrow> analyse \<noteq> []\<close> and
      s: \<open>s = (cach, s')\<close> \<open>s' = (analyse, b)\<close> and
      nempty: \<open>analyse \<noteq> []\<close> and
      \<open>snd (hd analyse) \<noteq> {#}\<close> and
      \<open>case x of (L, ana) \<Rightarrow> L \<in># snd (hd analyse) \<and> tl ana = tl analyse \<and>
        ana \<noteq> [] \<and> hd ana = (fst (hd analyse), remove1_mset L (snd (hd analyse)))\<close> and
      \<open>x = (L, ana)\<close> and
      \<open>\<not> (get_level M L = 0 \<or> cach (atm_of L) = SEEN_REMOVABLE \<or> L \<in># D)\<close> and
      cach_update: \<open>\<forall>L. cach' L = SEEN_REMOVABLE \<longrightarrow> cach L = SEEN_REMOVABLE\<close>
    for s cach s' analyse b x L ana E cach'
  proof -
    have
      cach: \<open>conflict_min_analysis_inv M cach ?N D\<close> and
      ana: \<open>conflict_min_analysis_stack M ?N D analyse\<close> and
      stack: \<open>conflict_min_analysis_stack M ?N D analyse\<close> and
      last_analysis: \<open>analyse \<noteq> [] \<longrightarrow> fst (last analyse) = fst (hd init_analysis)\<close> and
      b: \<open>analyse = [] \<longrightarrow> b \<longrightarrow> cach (atm_of (fst (hd init_analysis))) = SEEN_REMOVABLE\<close>
      using inv_I' unfolding lit_redundant_inv_def s I'_def by auto
    have \<open>conflict_min_analysis_inv M cach' ?N D\<close>
      using cach cach_update by (auto simp: conflict_min_analysis_inv_def)
    moreover have \<open>conflict_min_analysis_stack M ?N D []\<close>
      by simp
    ultimately show ?I
      unfolding lit_redundant_inv_def by simp
    then show ?I'
      using M_D unfolding I'_def by auto
    show ?R
      using nempty unfolding R_def s by auto
  qed
  have is_propagation_inv: \<open>lit_redundant_inv M ?N D init_analysis
       (cach, (L, remove1_mset (-L) E') # ana, False)\<close> (is ?I) and
    is_propagation_I': \<open>I' (cach, (L, remove1_mset (-L) E') # ana, False)\<close> (is ?I') and
    is_propagation_R: \<open>((cach, (L, remove1_mset (-L) E') # ana, False), s) \<in> R\<close> (is ?R)
    if
      inv_I': \<open>I' s\<close> and
      \<open>case s of (cach, analyse, b) \<Rightarrow> analyse \<noteq> []\<close> and
      s: \<open>s = (cach, s')\<close> \<open>s' = (analyse, b)\<close> \<open>x = (L, ana)\<close> and
      nemtpy_stack: \<open>analyse \<noteq> []\<close> and
      \<open>snd (hd analyse) \<noteq> {#}\<close> and
      next_lit: \<open>case x of (L, ana) \<Rightarrow>
       L \<in># snd (hd analyse) \<and>
       tl ana = tl analyse \<and>
       ana \<noteq> [] \<and>
       hd ana =
       (fst (hd analyse),
        remove1_mset L (snd (hd analyse)))\<close> and
      \<open>\<not> (get_level M L = 0 \<or> cach (atm_of L) = SEEN_REMOVABLE \<or> L \<in># D)\<close> and
      E: \<open>E \<noteq> None \<longrightarrow> Propagated (- L) (the E) \<in> set M\<close> \<open>E = Some E'\<close>
    for s cach s' analyse b x L ana E E'
  proof -
    obtain K C ana' where analysis: \<open>analyse = (K, C) # ana'\<close>
      using nemtpy_stack by (cases analyse) auto
    have ana': \<open>ana = (K, remove1_mset L C) # ana'\<close>
      using next_lit unfolding s by (cases ana) (auto simp: analysis)
    have
      cach: \<open>conflict_min_analysis_inv M cach ?N D\<close> and
      ana: \<open>conflict_min_analysis_stack M ?N D analyse\<close> and
      stack: \<open>conflict_min_analysis_stack M ?N D analyse\<close> and
      stack_hd: \<open>conflict_min_analysis_stack_hd M ?N D analyse\<close> and
      last_analysis: \<open>analyse \<noteq> [] \<longrightarrow> fst (last analyse) = fst (hd init_analysis)\<close> and
      b: \<open>analyse = [] \<longrightarrow> b \<longrightarrow> cach (atm_of (fst (hd init_analysis))) = SEEN_REMOVABLE\<close>
      using inv_I' unfolding lit_redundant_inv_def s I'_def by auto
    have
      NU_E: \<open>?N \<Turnstile>pm add_mset (- L) (remove1_mset (-L) E')\<close> and
      uL_E: \<open>-L \<in># E'\<close> and
      M_E': \<open>M \<Turnstile>as CNot (remove1_mset (- L) E')\<close> and
      lev_E': \<open>K \<in># remove1_mset (- L) E' \<Longrightarrow> index_in_trail M K < index_in_trail M (- L)\<close> for K
      using Propagated_in_trail_entailed[OF invs, of \<open>-L\<close> E'] E by (auto simp: ac_simps)
    have uL_M: \<open>- L \<in> lits_of_l M\<close>
      using next_lit inv_I' unfolding s analysis I'_def by (auto dest!: multi_member_split)
    obtain C' where
      \<open>?N \<Turnstile>pm add_mset (- K) C'\<close> and
      \<open>\<forall>Ka\<in>#C'. index_in_trail M Ka < index_in_trail M K\<close> and
      \<open>C \<subseteq># C'\<close> and
      \<open>\<forall>Ka\<in>#C' - C.
        ?N \<Turnstile>pm add_mset (- Ka) (filter_to_poslev M K D) \<or>
        Ka \<in># filter_to_poslev M K D\<close> and
      uK_M: \<open>- K \<in> lits_of_l M\<close>
      using stack_hd
      unfolding s ana'[symmetric]
      by (auto simp: analysis ana' conflict_min_analysis_stack_change_hd)

    then have \<open>conflict_min_analysis_stack M ?N D ((L, remove1_mset (-L) E') # ana)\<close>
      using stack E next_lit NU_E uL_E (* stack_hd *)
        filter_to_poslev_mono_entailement_add_mset[of M _ _ \<open>set_mset ?N\<close> _ D]
        filter_to_poslev_mono[of M ]
      unfolding s ana'[symmetric]
      by (auto simp: analysis ana' conflict_min_analysis_stack_change_hd)
    moreover have \<open>conflict_min_analysis_stack_hd M ?N D ((L, remove1_mset (- L) E') # ana)\<close>
      using NU_E lev_E' uL_M by (auto intro!:exI[of _ \<open>remove1_mset (- L) E'\<close>])
    moreover have \<open>fst (hd init_analysis) = fst (last ((L, remove1_mset (- L) E') # ana))\<close>
      using last_analysis unfolding analysis ana' by auto
    ultimately show ?I
      using cach b unfolding lit_redundant_inv_def analysis by auto

    then show ?I'
      using M_E' inv_I' unfolding I'_def s ana analysis ana' by (auto simp: true_annot_CNot_diff)

    have \<open>L \<in># C\<close> and in_trail: \<open>Propagated (- L) (the E) \<in> set M\<close> and E: \<open>the E = E'\<close>
      using next_lit E by (auto simp: analysis ana' s)
    then obtain E'' C' where
      E': \<open>E' = add_mset (-L) E''\<close> and
      C: \<open>C = add_mset L C'\<close>
      using uL_E by (blast dest: multi_member_split)

    have \<open>minimize_conflict_support M (C + fold_mset op + D (snd `# mset ana'))
           (remove1_mset (- L) E' + (remove1_mset L C + fold_mset op + D (snd `# mset ana')))\<close>
      using minimize_conflict_support.resolve_propa[OF in_trail,
        of \<open>C' + fold_mset op + D (snd `# mset ana')\<close>]
      unfolding C E' E
      by (auto simp: ac_simps)

    then show ?R
      using nemtpy_stack unfolding s analysis ana' by (auto simp: R_def
          intro: resolve_propa)
  qed
  show ?thesis
    unfolding lit_redundant_rec_def lit_redundant_rec_spec_def mark_failed_lits_def
      get_literal_and_remove_of_analyse_def get_propagation_reason_def
    apply (refine_vcg WHILET_rule[where R = R and I = I'])
      -- \<open>Well foundedness\<close>
    subgoal by (rule wf_R)
    subgoal by (rule init_I')
    subgoal by simp
      -- \<open>Assertion:\<close>
    subgoal by (rule hd_M)
        -- \<open>We finished one stage:\<close>
    subgoal by (rule all_removed_I')
    subgoal by (rule all_removed_R)
      -- \<open>Assertion:\<close>
    subgoal for s cach s' analyse ba
      by (cases \<open>analyse\<close>) (auto simp: I'_def dest!: multi_member_split)
        -- \<open>Cached or level 0:\<close>
    subgoal by (rule seen_removable_I')
    subgoal by (rule seen_removable_R)
        -- \<open>Failed:\<close>
    subgoal by (rule failed_I')
    subgoal by (rule failed_R)
    subgoal by (rule failed_I')
    subgoal by (rule failed_R)
        -- \<open>The literal was propagated:\<close>
    subgoal by (rule is_propagation_I')
    subgoal by (rule is_propagation_R)
        -- \<open>End of Loop invariant:\<close>
    subgoal
      using uL_M by (auto simp: lit_redundant_inv_def conflict_min_analysis_inv_def init_analysis
          I'_def ac_simps)
    subgoal by (auto simp: lit_redundant_inv_def conflict_min_analysis_inv_def init_analysis
          I'_def ac_simps)
    done
qed

definition literal_redundant_spec where
  \<open>literal_redundant_spec M NU D L =
    SPEC(\<lambda>(cach, analysis, b). (b \<longrightarrow> NU \<Turnstile>pm add_mset (-L) (filter_to_poslev M L D)) \<and>
     conflict_min_analysis_inv M cach NU D)\<close>

definition literal_redundant where
  \<open>literal_redundant M NU D cach L = do {
     ASSERT(-L \<in> lits_of_l M);
     if get_level M L = 0 \<or> cach (atm_of L) = SEEN_REMOVABLE
     then RETURN (cach, [], True)
     else if cach (atm_of L) = SEEN_FAILED
     then RETURN (cach, [], False)
     else do {
       C \<leftarrow> get_propagation_reason M (-L);
       case C of
         Some C \<Rightarrow> lit_redundant_rec M NU D cach [(L, C - {#-L#})]
       | None \<Rightarrow> do {
           RETURN (cach, [], False)
     }
    }
  }\<close>

lemma true_clss_cls_add_self: \<open>NU \<Turnstile>p D' + D' \<longleftrightarrow> NU \<Turnstile>p D'\<close>
  by (metis subset_mset.sup_idem true_clss_cls_sup_iff_add)

lemma true_clss_cls_add_add_mset_self: \<open>NU \<Turnstile>p add_mset L (D' + D') \<longleftrightarrow> NU \<Turnstile>p add_mset L D'\<close>
  using true_clss_cls_add_self true_clss_cls_mono_r by fastforce


lemma filter_to_poslev_remove1:
  \<open>filter_to_poslev M L (remove1_mset K D) =
      (if index_in_trail M K \<le> index_in_trail M L then remove1_mset K (filter_to_poslev M L D)
   else filter_to_poslev M L D)\<close>
  unfolding filter_to_poslev_def
  by (auto simp: multiset_filter_mono2)


lemma filter_to_poslev_add_mset:
  \<open>filter_to_poslev M L (add_mset K D) =
      (if index_in_trail M K < index_in_trail M L then add_mset K (filter_to_poslev M L D)
   else filter_to_poslev M L D)\<close>
  unfolding filter_to_poslev_def
  by (auto simp: multiset_filter_mono2)

lemma filter_to_poslev_conflict_min_analysis_inv:
  assumes
    L_D: \<open>L \<in># D\<close> and
    NU_uLD: \<open>N+U \<Turnstile>pm add_mset (-L) (filter_to_poslev M L D)\<close> and
    inv: \<open>conflict_min_analysis_inv M cach (N + U) D\<close>
  shows \<open>conflict_min_analysis_inv M cach (N + U) (remove1_mset L D)\<close>
  unfolding conflict_min_analysis_inv_def
proof (intro allI impI)
  fix K
  assume \<open>-K \<in> lits_of_l M\<close> and \<open>cach (atm_of K) = SEEN_REMOVABLE\<close>
  then have K: \<open>N + U \<Turnstile>pm add_mset (- K) (filter_to_poslev M K D)\<close>
    using inv unfolding conflict_min_analysis_inv_def by blast
  obtain D' where D: \<open>D = add_mset L D'\<close>
    using multi_member_split[OF L_D] by blast
  have \<open>N + U \<Turnstile>pm add_mset (- K) (filter_to_poslev M K D')\<close>
  proof (cases \<open>index_in_trail M L < index_in_trail M K\<close>)
    case True
    then have \<open>N + U \<Turnstile>pm add_mset (- K) (add_mset L (filter_to_poslev M K D'))\<close>
      using K by (auto simp: filter_to_poslev_add_mset D)
    then have 1: \<open>N + U \<Turnstile>pm add_mset L (add_mset (-K) (filter_to_poslev M K D'))\<close>
      by (simp add: add_mset_commute)
    have H: \<open>index_in_trail M L \<le> index_in_trail M K\<close>
      using True by simp
    have 2: \<open>N+U \<Turnstile>pm add_mset (-L) (filter_to_poslev M K D')\<close>
      using filter_to_poslev_mono_entailement_add_mset[OF H] NU_uLD
      by (metis (no_types, hide_lams) D NU_uLD filter_to_poslev_add_mset
          order_less_irrefl)
    show ?thesis
      using true_clss_cls_or_true_clss_cls_or_not_true_clss_cls_or[OF 2 1]
      by (auto simp: true_clss_cls_add_add_mset_self)
  next
    case False
    then show ?thesis using K by (auto simp: filter_to_poslev_add_mset D split: if_splits)
  qed
  then show \<open>N + U \<Turnstile>pm add_mset (- K) (filter_to_poslev M K (remove1_mset L D))\<close>
    by (simp add: D)
qed

lemma can_filter_to_poslev_can_remove:
  assumes
    L_D: \<open>L \<in># D\<close> and
    \<open>M \<Turnstile>as CNot D\<close> and
    NU_D: \<open>NU \<Turnstile>pm D\<close> and
    NU_uLD: \<open>NU \<Turnstile>pm add_mset (-L) (filter_to_poslev M L D)\<close>
  shows \<open>NU \<Turnstile>pm remove1_mset L D\<close>
proof -
  obtain D' where
    D: \<open>D = add_mset L D'\<close>
    using multi_member_split[OF L_D] by blast
  then have \<open>filter_to_poslev M L D \<subseteq># D'\<close>
    by (auto simp: filter_to_poslev_def)
  then have \<open>NU \<Turnstile>pm add_mset (-L) D'\<close>
    using NU_uLD true_clss_cls_mono_r[of _ \<open> add_mset (- L) (filter_to_poslev M (-L) D)\<close> ]
    by (auto simp: mset_subset_eq_exists_conv)
  from true_clss_cls_or_true_clss_cls_or_not_true_clss_cls_or[OF this, of D']
  show \<open>NU \<Turnstile>pm remove1_mset L D\<close>
    using NU_D by (auto simp: D true_clss_cls_add_self)
qed

lemma literal_redundant_spec:
  fixes L :: \<open>'v literal\<close>
  assumes invs: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv (M, N + NE, U + UE, D')\<close>
  assumes
    inv: \<open>conflict_min_analysis_inv M cach (N + NE + U + UE) D\<close> and
    L_D: \<open>L \<in># D\<close> and
    M_D: \<open>M \<Turnstile>as CNot D\<close>
  shows
    \<open>literal_redundant M (N + U) D cach L \<le> literal_redundant_spec M (N + U + NE + UE) D L\<close>
proof -
  have lit_redundant_rec: \<open>lit_redundant_rec M (N + U) D cach [(L, remove1_mset (- L) E')]
      \<le> literal_redundant_spec M (N + U + NE + UE) D L\<close>
    if
      E: \<open>E \<noteq> None \<longrightarrow> Propagated (- L) (the E) \<in> set M\<close> and
      E': \<open>E = Some E'\<close>
    for E E'
  proof -
    have
      [simp]: \<open>-L \<in># E'\<close> and
      in_trail: \<open>Propagated (- L) (add_mset (-L) (remove1_mset (-L) E')) \<in> set M\<close>
      using Propagated_in_trail_entailed[OF invs, of \<open>-L\<close> E'] E E'
      by auto
    have H: \<open>lit_redundant_rec_spec M (N + U + NE + UE) D L \<le>
       literal_redundant_spec M (N + U + NE + UE) D L\<close>
      by (auto simp: lit_redundant_rec_spec_def literal_redundant_spec_def ac_simps)
    show ?thesis
      apply (rule order.trans)
       apply (rule lit_redundant_rec_spec[OF invs _ in_trail])
      subgoal ..
      subgoal by (rule inv)
      subgoal using assms by fast
      subgoal by (rule M_D)
      subgoal unfolding literal_redundant_spec_def[symmetric] by (rule H)
      done
  qed

  have uL_M: \<open>-L \<in> lits_of_l M\<close>
    using L_D M_D by (auto dest!: multi_member_split)
  show ?thesis
    unfolding literal_redundant_def get_propagation_reason_def literal_redundant_spec_def
    apply (refine_vcg)
    subgoal using uL_M .
    subgoal
      using inv uL_M cdcl\<^sub>W_restart_mset.literals_of_level0_entailed[OF invs, of \<open>-L\<close>]
        true_clss_cls_mono_r'
      by (fastforce simp: mark_failed_lits_def conflict_min_analysis_inv_def
          clauses_def ac_simps)
    subgoal using inv by (auto simp: ac_simps)
    subgoal by auto
    subgoal using inv by (auto simp: ac_simps)
    subgoal using inv by (auto simp: mark_failed_lits_def conflict_min_analysis_inv_def)
    subgoal using inv by (auto simp: mark_failed_lits_def conflict_min_analysis_inv_def ac_simps)
    subgoal for E E'
      unfolding literal_redundant_spec_def[symmetric]
      by (rule lit_redundant_rec)
    done
qed

definition set_all_to_list where
  \<open>set_all_to_list e ys = do {
     S \<leftarrow> WHILE\<^bsup>\<lambda>(i, xs). i \<le> length xs \<and> (\<forall>x \<in> set (take i xs). x = e) \<and> length xs = length ys\<^esup>
       (\<lambda>(i, xs). i < length xs)
       (\<lambda>(i, xs). do {
         ASSERT(i < length xs);
         RETURN(i+1, xs[i := e])
        })
       (0, ys);
    RETURN (snd S)
    }\<close>

lemma
  \<open>set_all_to_list e ys \<le> SPEC(\<lambda>xs. length xs = length ys \<and> (\<forall>x \<in> set xs. x = e))\<close>
  unfolding set_all_to_list_def
  apply (refine_vcg)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by (auto simp: take_Suc_conv_app_nth list_update_append)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  done

definition get_literal_and_remove_of_analyse_wl
   :: \<open>'v clause_l \<Rightarrow> (nat \<times> nat) list \<Rightarrow> 'v literal \<times> (nat \<times> nat) list\<close> where
  \<open>get_literal_and_remove_of_analyse_wl C analyse =
    (let (i, j) = last analyse in
     (C ! j, analyse[length analyse - 1 := (i, j + 1)]))\<close>


definition mark_failed_lits_wl
where
  \<open>mark_failed_lits_wl NU analyse cach = SPEC(\<lambda>cach'.
     (\<forall>L. cach' L = SEEN_REMOVABLE \<longrightarrow> cach L = SEEN_REMOVABLE))\<close>


definition lit_redundant_rec_wl_ref where
  \<open>lit_redundant_rec_wl_ref NU analyse \<longleftrightarrow>
       (\<forall>(i, j) \<in> set analyse. j \<le> length (NU ! i) \<and> i < length NU \<and> j \<ge> 1 \<and> i > 0)\<close>

definition lit_redundant_rec_wl_inv where
  \<open>lit_redundant_rec_wl_inv M NU D = (\<lambda>(cach, analyse, b). lit_redundant_rec_wl_ref NU analyse)\<close>

context isasat_input_ops
begin

definition (in -) lit_redundant_rec_wl :: \<open>('v, nat) ann_lits \<Rightarrow> 'v clauses_l \<Rightarrow> 'v clause \<Rightarrow>
     _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow>
      (_ \<times> _ \<times> bool) nres\<close>
where
  \<open>lit_redundant_rec_wl M NU D cach analysis _ =
      WHILE\<^sub>T\<^bsup>lit_redundant_rec_wl_inv M NU D\<^esup>
        (\<lambda>(cach, analyse, b). analyse \<noteq> [])
        (\<lambda>(cach, analyse, b). do {
            ASSERT(analyse \<noteq> []);
            ASSERT(fst (last analyse) < length NU);
            let C = NU ! fst (last analyse);
            ASSERT(length C \<ge> 1);
            let i = snd (last analyse);
            ASSERT(C!0 \<in> lits_of_l M);
            if i \<ge> length C
            then
               RETURN(cach (atm_of (C ! 0) := SEEN_REMOVABLE), butlast analyse, True)
            else do {
               let (L, analyse) = get_literal_and_remove_of_analyse_wl C analyse;
               ASSERT(-L \<in> lits_of_l M);
               b \<leftarrow> RES (UNIV);
               if (get_level M L = 0 \<or> cach (atm_of L) = SEEN_REMOVABLE \<or> L \<in># D)
               then RETURN (cach, analyse, False)
               else if b \<or> cach (atm_of L) = SEEN_FAILED
               then do {
                  cach \<leftarrow> mark_failed_lits_wl NU analyse cach;
                  RETURN (cach, [], False)
               }
               else do {
                  C \<leftarrow> get_propagation_reason M (-L);
                  case C of
                    Some C \<Rightarrow> RETURN (cach, analyse @ [(C, 1)], False)
                  | None \<Rightarrow> do {
                      cach \<leftarrow> mark_failed_lits_wl NU analyse cach;
                      RETURN (cach, [], False)
                  }
              }
          }
        })
       (cach, analysis, False)\<close>

fun convert_analysis_l where
  \<open>convert_analysis_l NU (i, j) = (-NU ! i ! 0, mset (drop j (NU ! i)))\<close>

definition convert_analysis_list where
  \<open>convert_analysis_list NU analyse = map (convert_analysis_l NU) (rev analyse)\<close>

lemma convert_analysis_list_empty[simp]:
  \<open>convert_analysis_list NU [] = []\<close>
  \<open>convert_analysis_list NU a = [] \<longleftrightarrow> a = []\<close>
  by (auto simp: convert_analysis_list_def)

lemma lit_redundant_rec_wl:
  fixes S :: \<open>nat twl_st_wl\<close> and NU M analyse
  defines
    [simp]: \<open>S' \<equiv> st_l_of_wl None S\<close> and
    [simp]: \<open>S'' \<equiv> twl_st_of_wl None S\<close> and
    [simp]: \<open>S''' \<equiv> state\<^sub>W_of (twl_st_of_wl None S)\<close>
  defines
    \<open>M \<equiv> get_trail_wl S\<close> and
    M': \<open>M' \<equiv> trail S'''\<close> and
    NU: \<open>NU \<equiv> get_clauses_wl S\<close> and
    NU': \<open>NU' \<equiv> mset `# mset (tl NU)\<close> and
    \<open>analyse' \<equiv> convert_analysis_list NU analyse\<close>
  assumes
    bounds_init: \<open>lit_redundant_rec_wl_ref NU analyse\<close> and
    struct_invs: \<open>twl_struct_invs S''\<close> and
    add_inv: \<open>twl_list_invs S'\<close>
  shows
    \<open>lit_redundant_rec_wl M NU D cach analyse lbv \<le> \<Down>
       (Id \<times>\<^sub>r {(analyse, analyse'). analyse' = convert_analysis_list NU analyse \<and>
          lit_redundant_rec_wl_ref NU analyse} \<times>\<^sub>r bool_rel)
       (lit_redundant_rec M' NU' D cach analyse')\<close>
   (is \<open>_ \<le> \<Down> (_ \<times>\<^sub>r ?A \<times>\<^sub>r _) _\<close> is \<open>_ \<le> \<Down> ?R _\<close>)
proof -
  obtain u D' NE UE Q W where
    S: \<open>S = (M, NU, u, D', NE, UE, Q, W)\<close>
    using M_def NU by (cases S) auto
  have M'_def: \<open>M' = convert_lits_l NU M\<close>
    using NU unfolding M' by (auto simp: S)
  have [simp]: \<open>lits_of_l M' = lits_of_l M\<close>
    unfolding M'_def by auto
  have [simp]: \<open>fst (convert_analysis_l NU x) = -NU ! (fst x) ! 0\<close> for x
    by (cases x) auto
  have [simp]: \<open>snd (convert_analysis_l NU x) = mset (drop (snd x) (NU ! fst x))\<close> for x
    by (cases x) auto

  have
    no_smaller_propa: \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa S'''\<close> and
    struct_invs: \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv S'''\<close>
    using struct_invs unfolding twl_struct_invs_def S''_def S'''_def[symmetric]
    by fast+
  have annots: \<open>set (get_all_mark_of_propagated (trail S''')) \<subseteq>
     set_mset (cdcl\<^sub>W_restart_mset.clauses S''')\<close>
    using struct_invs
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
       cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def
    by fast
  have n_d: \<open>no_dup M\<close>
    using struct_invs unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by (auto simp: S)
  then have n_d': \<open>no_dup M'\<close>
    unfolding M'_def by (auto simp: S)

  have get_literal_and_remove_of_analyse_wl: \<open>RETURN
       (get_literal_and_remove_of_analyse_wl (NU ! fst (last x1c)) x1c)
      \<le> \<Down> (Id \<times>\<^sub>r ?A) (get_literal_and_remove_of_analyse x1a)\<close>
    if
      xx': \<open>(x, x') \<in> ?R\<close> and
      s: \<open>x2 = (x1a, x2a)\<close>
        \<open>x' = (x1, x2)\<close>
        \<open>x2b = (x1c, x2c)\<close>
        \<open>x = (x1b, x2b)\<close> and
        \<open>x1a \<noteq> []\<close> and
      x1c: \<open>x1c \<noteq> []\<close> and
      length: \<open>\<not> length (NU ! fst (last x1c)) \<le> snd (last x1c)\<close>
    for x x' x1 x2 x1a x2a x1b x2b x1c x2c
  proof -
    have [simp]: \<open>length list = Suc x2 \<Longrightarrow>
       tl (rev (map f (list[x2 := aa])) @ ls) =
       tl (rev (map f list)) @ ls\<close>
      for list x2 aa f ls
      by (cases list rule: rev_cases) auto
    have [simp]: \<open>length list = Suc x2 \<Longrightarrow>
       hd (rev (map f (list[x2 := aa])) @ ls) = f aa\<close>
      for list x2 aa f ls
      by (cases list rule: rev_cases) auto
    have \<open>last x1c = (a, b) \<Longrightarrow> b \<le> length (NU ! a)\<close> for aa ba list a b
      using xx' x1c length unfolding s convert_analysis_list_def
      by (cases x1c rule: rev_cases) auto
    then show ?thesis
      supply convert_analysis_list_def[simp] hd_rev[simp] last_map[simp] rev_map[symmetric, simp]
      using x1c xx' length
      using Cons_nth_drop_Suc[of \<open>snd (last x1c)\<close> \<open>NU ! fst (last x1c)\<close>, symmetric]
      unfolding s lit_redundant_rec_wl_ref_def
      by (cases x1c; cases \<open>last x1c\<close>)
         (auto 5 5 simp: get_literal_and_remove_of_analyse_wl_def (* in_set_drop_conv_nth *)
          get_literal_and_remove_of_analyse_def convert_analysis_list_def
          map_butlast[symmetric] rev_append
          intro!: RETURN_SPEC_refine elim!: neq_Nil_revE split: if_splits nat.splits
          elim!: in_set_upd_cases)
  qed
  have get_propagation_reason: \<open>get_propagation_reason M (-x1e)
      \<le> \<Down> (\<langle>{(C', C).  C = mset (NU ! C') \<and> C' \<noteq> 0 \<and> Propagated (- x1e) (mset (NU!C')) \<in> set M'
                \<and> Propagated (- x1e) C' \<in> set M \<and> C' < length NU}\<rangle>
              option_rel)
          (get_propagation_reason M' (-x1d))\<close>
    (is \<open>_ \<le> \<Down> (\<langle>?get_propagation_reason\<rangle>option_rel) _\<close>)
    if
      \<open>(x, x') \<in> ?R\<close> and
      \<open>case x of (cach, analyse, b) \<Rightarrow> analyse \<noteq> []\<close> and
      \<open>case x' of (cach, analyse, b) \<Rightarrow> analyse \<noteq> []\<close> and
      s: \<open>x2 = (x1a, x2a)\<close> \<open>x' = (x1, x2)\<close> \<open>x2b = (x1c, x2c)\<close> \<open>x = (x1b, x2b)\<close>
         \<open>x'a = (x1d, x2d)\<close> and
      \<open>x1a \<noteq> []\<close> and
      \<open>- fst (hd x1a) \<in> lits_of_l M'\<close> and
      \<open>x1c \<noteq> []\<close> and
      \<open>NU ! fst (last x1c) ! 0 \<in> lits_of_l M\<close> and
      \<open>\<not> length (NU ! fst (last x1c)) \<le> snd (last x1c)\<close> and
      \<open>snd (hd x1a) \<noteq> {#}\<close> and
      H: \<open>(get_literal_and_remove_of_analyse_wl (NU ! fst (last x1c)) x1c, x'a) \<in> Id \<times>\<^sub>f ?A\<close>
         \<open>get_literal_and_remove_of_analyse_wl (NU ! fst (last x1c)) x1c = (x1e, x2e)\<close> and
      \<open>- x1d \<in> lits_of_l M'\<close> and
      ux1e_M: \<open>- x1e \<in> lits_of_l M\<close> and
      \<open>\<not> (get_level M x1e = 0 \<or> x1b (atm_of x1e) = SEEN_REMOVABLE \<or> x1e \<in># D)\<close> and
      cond: \<open>\<not> (get_level M' x1d = 0 \<or> x1 (atm_of x1d) = SEEN_REMOVABLE \<or> x1d \<in># D)\<close>
    for x x' x1 x2 x1a x2a x1b x2b x1c x2c x1e x1d x'a x2d x2e
  proof -
    have [simp]: \<open>x1d = x1e\<close>
      using s H by auto
    have
      \<open>Propagated (- x1d) (mset (NU ! a)) \<in> set M'\<close> (is ?propa) and
      \<open>a \<noteq> 0\<close> (is ?a) and
      \<open>a < length NU\<close> (is ?L)
      if \<open>Propagated (-x1e) a \<in> set M\<close>
      for a
    proof -
      have [simp]: \<open>a \<noteq> 0\<close>
      proof
        assume [simp]: \<open>a = 0\<close>
        have H: \<open>\<not> M \<Turnstile>as CNot D\<close>
          if \<open>trail S''' = M' @ Decided K # M\<close> and
            \<open>D + {#L#} \<in># cdcl\<^sub>W_restart_mset.clauses S'''\<close>
            \<open>undefined_lit M L\<close> for M K M' D L
          using no_smaller_propa that unfolding cdcl\<^sub>W_restart_mset.no_smaller_propa_def by blast
        have x1d_M': \<open>Propagated (- x1d) {#-x1d#} \<in> set M'\<close>
          using that by (auto simp: M'_def dest!: split_list)

        then have x1d_clss:  \<open>{#-x1d#} \<in># cdcl\<^sub>W_restart_mset.clauses S'''\<close>
          using annots by (auto simp: S M'_def[symmetric] clauses_def mset_take_mset_drop_mset
              dest!: split_list)
        have \<open>no_dup M'\<close>
          using n_d unfolding M'_def by auto
        then have count_M': \<open>count_decided M' \<ge> 1\<close>
          using x1d_M' cond by (auto dest!: split_list)
        have \<open>get_level M (-x1d) = 0\<close>
        proof (rule ccontr)
          assume lev: \<open>\<not> ?thesis\<close>
          then have lev': \<open>0 < get_level M' x1e\<close>
            unfolding M'_def by auto
          obtain M2 K M1 where
            M': \<open>M' = M2 @ Decided K # M1\<close> and
            lev_K: \<open>get_level M K = Suc 0\<close>
            using le_count_decided_decomp[OF n_d, of 0] count_M' unfolding M'_def by auto
          have lev_K: \<open>get_level M' K = Suc 0\<close>
            using lev_K unfolding M'_def by auto
          have \<open>defined_lit M' x1d\<close>
            using ux1e_M by (simp add: Decided_Propagated_in_iff_in_lits_of_l)
          then have \<open>undefined_lit M1 x1d\<close>
            using lev' n_d' lev_K  Suc_count_decided_gt_get_level[of M1]
            unfolding M_def
            by (auto simp: S clauses_def mset_take_mset_drop_mset' M'_def[symmetric] defined_lit_cons
                M' defined_lit_append atm_of_eq_atm_of get_level_cons_if
                dest: defined_lit_no_dupD split: if_splits)
          then show False
            using H[of _ _ _ \<open>{#}\<close> \<open>-x1d\<close>] x1d_clss
            by (auto simp: S clauses_def mset_take_mset_drop_mset' M'_def[symmetric] M')
        qed
        then show False using cond unfolding M'_def by auto
      qed
      show ?propa and ?a
        using that by (auto simp: M'_def dest!: split_list)
      show ?L
        using that add_inv unfolding twl_list_invs_def
        by (auto simp: S)
    qed
    then show ?thesis
      apply (auto simp: get_propagation_reason_def refine_rel_defs intro!: RES_refine)
      apply (case_tac s)
      by auto
  qed
  have resolve: \<open>((x1b, x2e @ [(xb, 1)], False), x1, (x1d, remove1_mset (- x1d) x'c) # x2d, False)
      \<in> Id \<times>\<^sub>r ?A \<times>\<^sub>r bool_rel\<close>
    if
      xx': \<open>(x, x') \<in> Id \<times>\<^sub>r ?A \<times>\<^sub>r bool_rel\<close> and
      s: \<open>x2 = (x1a, x2a)\<close> \<open>x' = (x1, x2)\<close> \<open>x2b = (x1c, x2c)\<close> \<open>x = (x1b, x2b)\<close>
         \<open>x'a = (x1d, x2d)\<close> and
      get_literal_and_remove_of_analyse_wl:
        \<open>(get_literal_and_remove_of_analyse_wl (NU ! fst (last x1c)) x1c, x'a) \<in> Id \<times>\<^sub>f ?A\<close> and
      get_lit:
        \<open>get_literal_and_remove_of_analyse_wl (NU ! fst (last x1c)) x1c = (x1e, x2e)\<close> and
      xb_x'c: \<open>(xb, x'c) \<in> (?get_propagation_reason x1e)\<close>
    for x x2 x1a x2a x2b x1c x2c x'a x1d x2d x1e x2e xb x'c x' x1b x1
  proof -
    have [simp]: \<open>mset (tl C) = remove1_mset (C!0) (mset C)\<close> for C
      by (cases C) auto
    have \<open>x1d = x1e\<close>
      using s get_literal_and_remove_of_analyse_wl
      unfolding get_lit convert_analysis_list_def
      by auto
    then have [simp]: \<open>x1d = -NU ! xb ! 0\<close> \<open>NU ! xb \<noteq> []\<close>
      using add_inv xb_x'c unfolding twl_list_invs_def by (fastforce simp: S)+
    show ?thesis
      using s xx' get_literal_and_remove_of_analyse_wl xb_x'c
      unfolding get_lit convert_analysis_list_def lit_redundant_rec_wl_ref_def
      by (auto simp: drop_Suc)
  qed
  have mark_failed_lits_wl: \<open>mark_failed_lits_wl NU x2e x1b \<le> \<Down> Id (mark_failed_lits NU' x2d x1)\<close>
    if
      \<open>(x, x') \<in> ?R\<close> and
      \<open>x' = (x1, x2)\<close> and
      \<open>x = (x1b, x2b)\<close>
    for x x' x2e x1b x1 x2 x2b x2d
    using that unfolding mark_failed_lits_wl_def mark_failed_lits_def by auto
  have wl_inv: \<open>lit_redundant_rec_wl_inv M NU D x'\<close> if \<open>(x', x) \<in> ?R\<close> for x x'
    using that unfolding lit_redundant_rec_wl_inv_def
    by (cases x, cases x') auto
  show ?thesis
    supply convert_analysis_list_def[simp] hd_rev[simp] last_map[simp] rev_map[symmetric, simp]
    unfolding lit_redundant_rec_wl_def lit_redundant_rec_def WHILET_def
    apply (rewrite at \<open>let _ = _ ! _ in _\<close> Let_def)
    apply (rewrite at \<open>let _ = snd _ in _\<close> Let_def)
    apply refine_rcg
    subgoal using bounds_init unfolding analyse'_def by auto
    subgoal for x x'
      by (cases x, cases x')
        (auto simp: lit_redundant_rec_wl_inv_def lit_redundant_rec_wl_ref_def)
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: lit_redundant_rec_wl_inv_def lit_redundant_rec_wl_ref_def
       elim!: neq_Nil_revE)
    subgoal by (auto simp: lit_redundant_rec_wl_inv_def lit_redundant_rec_wl_ref_def
       elim!: neq_Nil_revE)
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: map_butlast rev_butlast_is_tl_rev lit_redundant_rec_wl_ref_def
          dest: in_set_butlastD)
            apply (rule get_literal_and_remove_of_analyse_wl; assumption)
    subgoal by auto
    subgoal by (auto simp add: M'_def)
    subgoal by auto
    subgoal by (auto simp add: M'_def)
      apply (rule mark_failed_lits_wl; assumption)
    subgoal by (auto simp: lit_redundant_rec_wl_ref_def)
        apply (rule get_propagation_reason; assumption?)
       apply assumption
      apply (rule mark_failed_lits_wl; assumption)
    subgoal by (auto simp: lit_redundant_rec_wl_ref_def)
    subgoal by (rule resolve)
    done
qed


definition literal_redundant_wl where
  \<open>literal_redundant_wl M NU D cach L lbd = do {
     ASSERT(-L \<in> lits_of_l M);
     if get_level M L = 0 \<or> cach (atm_of L) = SEEN_REMOVABLE
     then RETURN (cach, [], True)
     else if cach (atm_of L) = SEEN_FAILED
     then RETURN (cach, [], False)
     else do {
       C \<leftarrow> get_propagation_reason M (-L);
       case C of
         Some C \<Rightarrow> lit_redundant_rec_wl M NU D cach [(C, 1)] lbd
       | None \<Rightarrow> do {
           RETURN (cach, [], False)
       }
     }
  }\<close>

lemma literal_redundant_wl_literal_redundant:
  fixes S :: \<open>nat twl_st_wl\<close> and NU M
  defines
    [simp]: \<open>S' \<equiv> st_l_of_wl None S\<close> and
    [simp]: \<open>S'' \<equiv> twl_st_of_wl None S\<close> and
    [simp]: \<open>S''' \<equiv> state\<^sub>W_of (twl_st_of_wl None S)\<close>
  defines
    \<open>M \<equiv> get_trail_wl S\<close> and
    M': \<open>M' \<equiv> trail S'''\<close> and
    NU: \<open>NU \<equiv> get_clauses_wl S\<close> and
    NU': \<open>NU' \<equiv> mset `# mset (tl NU)\<close>
  assumes
    struct_invs: \<open>twl_struct_invs S''\<close> and
    add_inv: \<open>twl_list_invs S'\<close> and
    L_D: \<open>L \<in># D\<close> and
    M_D: \<open>M \<Turnstile>as CNot D\<close>
  shows
    \<open>literal_redundant_wl M NU D cach L lbd \<le> \<Down>
       (Id \<times>\<^sub>r {(analyse, analyse'). analyse' = convert_analysis_list NU analyse \<and>
          (\<forall>(i, j)\<in> set analyse. j \<le> length (NU!i) \<and> i < length NU \<and> j \<ge> 1 \<and> i > 0)} \<times>\<^sub>r bool_rel)
       (literal_redundant M' NU' D cach L)\<close>
   (is \<open>_ \<le> \<Down> (_ \<times>\<^sub>r ?A \<times>\<^sub>r _) _\<close> is \<open>_ \<le> \<Down> ?R _\<close>)
proof -
  obtain u D' NE UE Q W where
    S: \<open>S = (M, NU, u, D', NE, UE, Q, W)\<close>
    using M_def NU by (cases S) auto
  have M'_def: \<open>M' = convert_lits_l NU M\<close>
    using NU unfolding M' by (auto simp: S)
  have [simp]: \<open>lits_of_l M' = lits_of_l M\<close>
    unfolding M'_def by auto
  have
    no_smaller_propa: \<open>cdcl\<^sub>W_restart_mset.no_smaller_propa S'''\<close> and
    struct_invs': \<open>cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv S'''\<close>
    using struct_invs unfolding twl_struct_invs_def S''_def S'''_def[symmetric]
    by fast+
  have annots: \<open>set (get_all_mark_of_propagated (trail S''')) \<subseteq>
     set_mset (cdcl\<^sub>W_restart_mset.clauses S''')\<close>
    using struct_invs'
    unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
       cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_learned_clause_def
    by fast
  have n_d: \<open>no_dup M\<close>
    using struct_invs' unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
      cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_M_level_inv_def
    by (auto simp: S)
  then have n_d': \<open>no_dup M'\<close>
    unfolding M'_def by (auto simp: S)
  have uL_M: \<open>-L \<in> lits_of_l M\<close>
    using L_D M_D by (auto dest!: multi_member_split)
  have H: \<open>lit_redundant_rec_wl M NU D cach analyse lbd
  \<le> \<Down> ?R (lit_redundant_rec M' NU' D cach analyse')\<close>
    if \<open>analyse' = convert_analysis_list NU analyse\<close> and
       \<open>\<forall>(i, j)\<in>set analyse. j \<le> length (NU ! i) \<and> i < length NU \<and> j \<ge> 1 \<and> i > 0\<close>
     for analyse analyse'
  using lit_redundant_rec_wl[of S analyse D cach, unfolded S'''_def[symmetric],
      unfolded S'_def[symmetric] S''_def[symmetric]
      M_def[symmetric] M'[symmetric] NU[symmetric] NU'[symmetric], OF _ struct_invs add_inv]
    that by (auto simp: lit_redundant_rec_wl_ref_def)
   have get_propagation_reason: \<open>get_propagation_reason M (-L)
      \<le> \<Down> (\<langle>{(C', C).  C = mset (NU ! C') \<and> C' \<noteq> 0 \<and> Propagated (-L) (mset (NU!C')) \<in> set M'
                \<and> Propagated (-L) C' \<in> set M}\<rangle>
              option_rel)
          (get_propagation_reason M' (-L))\<close>
    (is \<open>_ \<le> \<Down> (\<langle>?get_propagation_reason\<rangle>option_rel) _\<close> is ?G1) and
     propagated_L: \<open>Propagated (-L) a \<in> set M \<Longrightarrow> a \<noteq> 0 \<and> Propagated (- L) (mset (NU ! a)) \<in> set M'\<close>
    (is \<open>?H2 \<Longrightarrow> ?G2\<close>)
    if
      lev0_rem: \<open>\<not> (get_level M' L = 0 \<or> cach (atm_of L) = SEEN_REMOVABLE)\<close> and
      ux1e_M: \<open>- L \<in> lits_of_l M\<close>
    for a
   proof -
     have \<open>Propagated (- L) (mset (NU ! a)) \<in> set M'\<close> (is ?propa) and
       \<open>a \<noteq> 0\<close> (is ?a)
       if \<open>Propagated (-L) a \<in> set M\<close>
       for a
     proof -
       have [simp]: \<open>a \<noteq> 0\<close>
       proof
         assume [simp]: \<open>a = 0\<close>
         have H: \<open>\<not> M \<Turnstile>as CNot D\<close>
           if \<open>trail S''' = M' @ Decided K # M\<close> and
             \<open>D + {#L#} \<in># cdcl\<^sub>W_restart_mset.clauses S'''\<close>
             \<open>undefined_lit M L\<close> for M K M' D L
           using no_smaller_propa that unfolding cdcl\<^sub>W_restart_mset.no_smaller_propa_def by blast
         have x1d_M': \<open>Propagated (- L) {#-L#} \<in> set M'\<close>
           using that by (auto simp: M'_def dest!: split_list)

         then have x1d_clss:  \<open>{#-L#} \<in># cdcl\<^sub>W_restart_mset.clauses S'''\<close>
           using annots by (auto simp: S M'_def[symmetric] clauses_def mset_take_mset_drop_mset
               dest!: split_list)
         have \<open>no_dup M'\<close>
           using n_d unfolding M'_def by auto
         then have count_M': \<open>count_decided M' \<ge> 1\<close>
           using x1d_M' lev0_rem by (auto dest!: split_list)
         have \<open>get_level M (-L) = 0\<close>
         proof (rule ccontr)
           assume lev: \<open>\<not> ?thesis\<close>
           then have lev': \<open>0 < get_level M' L\<close>
             unfolding M'_def by auto
           obtain M2 K M1 where
             M': \<open>M' = M2 @ Decided K # M1\<close> and
             lev_K: \<open>get_level M K = Suc 0\<close>
             using le_count_decided_decomp[OF n_d, of 0] count_M' unfolding M'_def by auto
           have lev_K: \<open>get_level M' K = Suc 0\<close>
             using lev_K unfolding M'_def by auto
           have \<open>defined_lit M' L\<close>
             using ux1e_M by (simp add: Decided_Propagated_in_iff_in_lits_of_l)
           then have \<open>undefined_lit M1 L\<close>
             using lev' n_d' lev_K  Suc_count_decided_gt_get_level[of M1]
             unfolding M_def
             by (auto simp: S clauses_def mset_take_mset_drop_mset' M'_def[symmetric]
                 defined_lit_cons M' defined_lit_append atm_of_eq_atm_of get_level_cons_if
                 dest: defined_lit_no_dupD split: if_splits)
           then show False
             using H[of _ _ _ \<open>{#}\<close> \<open>-L\<close>] x1d_clss
             by (auto simp: S clauses_def mset_take_mset_drop_mset' M'_def[symmetric] M')
         qed
         then show False using lev0_rem unfolding M'_def by auto
       qed
       show ?propa and ?a
         using that by (auto simp: M'_def dest!: split_list)
     qed note H = this
     show \<open>?H2 \<Longrightarrow> ?G2\<close>
       using H by auto
     show ?G1
       using H
       apply (auto simp: get_propagation_reason_def refine_rel_defs
           get_propagation_reason_def intro!: RES_refine)
       apply (case_tac s)
       by auto
   qed

  have [simp]: \<open>mset (tl C) = remove1_mset (C!0) (mset C)\<close> for C
    by (cases C) auto
  have [simp]: \<open>NU ! C ! 0 = -L\<close> if
    in_trail: \<open>Propagated (- L) C \<in> set M\<close> and
    lev: \<open>\<not> (get_level M' L = 0 \<or> cach (atm_of L) = SEEN_REMOVABLE)\<close>
  for C
    using add_inv that propagated_L[OF lev _ in_trail] uL_M
    by (auto simp: S twl_list_invs_def)
  have [dest]: \<open>C \<noteq> {#}\<close> if \<open>Propagated (- L) C \<in> set M'\<close> for C
  proof -
    have \<open>a @ Propagated L mark # b = trail S''' \<Longrightarrow> b \<Turnstile>as CNot (remove1_mset L mark) \<and> L \<in># mark\<close>
      for L mark a b
      using struct_invs' unfolding cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_all_struct_inv_def
        cdcl\<^sub>W_restart_mset.cdcl\<^sub>W_conflicting_def
      by fast
    then show ?thesis
      using that by (fastforce simp: S M'_def[symmetric] dest!: split_list)
  qed
  have [simp]: \<open>Propagated (- L) C \<in> set M \<Longrightarrow> C < length NU\<close> for C
    using add_inv by (auto simp: S twl_list_invs_def)

  show ?thesis
    unfolding literal_redundant_wl_def literal_redundant_def
    apply (refine_rcg H get_propagation_reason)
    subgoal by (simp add: M'_def)
    subgoal by (simp add: M'_def)
    subgoal by simp
    subgoal by simp
    subgoal by simp
    apply (assumption)
    subgoal by auto
    subgoal for x x' C x'a by (auto simp: convert_analysis_list_def drop_Suc)
    subgoal by auto
    done
qed

abbreviation (in -) minimize_status_rel where
  \<open>minimize_status_rel \<equiv> Id :: (minimize_status \<times> minimize_status) set\<close>

abbreviation (in -) minimize_status_assn where
  \<open>minimize_status_assn \<equiv> (id_assn :: minimize_status\<Rightarrow> _)\<close>

lemma (in -) SEEN_REMOVABLE[sepref_fr_rules]:
  \<open>(uncurry0 (return SEEN_REMOVABLE),uncurry0 (RETURN SEEN_REMOVABLE)) \<in>
     unit_assn\<^sup>k \<rightarrow>\<^sub>a minimize_status_assn\<close>
  by (sepref_to_hoare) sep_auto

lemma (in -) SEEN_FAILED[sepref_fr_rules]:
  \<open>(uncurry0 (return SEEN_FAILED),uncurry0 (RETURN SEEN_FAILED)) \<in>
     unit_assn\<^sup>k \<rightarrow>\<^sub>a minimize_status_assn\<close>
  by (sepref_to_hoare) sep_auto

lemma (in -) SEEN_UNKNOWN[sepref_fr_rules]:
  \<open>(uncurry0 (return SEEN_UNKNOWN),uncurry0 (RETURN SEEN_UNKNOWN)) \<in>
     unit_assn\<^sup>k \<rightarrow>\<^sub>a minimize_status_assn\<close>
  by (sepref_to_hoare) sep_auto

definition cach_refinement_list :: \<open>(minimize_status list \<times> (nat conflict_min_cach)) set\<close> where
  \<open>cach_refinement_list = \<langle>Id\<rangle>map_fun_rel {(a, a'). a = a' \<and> a \<in># \<A>\<^sub>i\<^sub>n}\<close>

definition cach_refinement_nonull
  :: \<open>((minimize_status list \<times> nat list) \<times> minimize_status list) set\<close>
where
  \<open>cach_refinement_nonull = {((cach, support), cach'). cach = cach' \<and>
       (\<forall>L < length cach. cach ! L \<noteq> SEEN_UNKNOWN \<longrightarrow> L \<in> set support) \<and>
       (\<forall>L \<in> set support. L < length cach)}\<close>

definition cach_refinement
  :: \<open>((minimize_status list \<times> nat list) \<times> (nat conflict_min_cach)) set\<close>
where
  \<open>cach_refinement = cach_refinement_nonull O cach_refinement_list\<close>

lemma cach_refinement_alt_def:
  \<open>cach_refinement = {((cach, support), cach').
       (\<forall>L < length cach. cach ! L \<noteq> SEEN_UNKNOWN \<longrightarrow> L \<in> set support) \<and>
       (\<forall>L \<in> set support. L < length cach) \<and>
       (\<forall>L \<in># \<A>\<^sub>i\<^sub>n. L < length cach \<and> cach ! L = cach' L)}\<close>
  unfolding cach_refinement_def cach_refinement_nonull_def cach_refinement_list_def
  by (auto simp: map_fun_rel_def)

abbreviation (in -) cach_refinement_l_assn where
  \<open>cach_refinement_l_assn \<equiv> array_assn minimize_status_assn *a arl_assn uint32_nat_assn\<close>

definition cach_refinement_assn where
  \<open>cach_refinement_assn = hr_comp cach_refinement_l_assn cach_refinement\<close>

lemma in_cach_refinement_alt_def:
  \<open>((cach, support), cach') \<in> cach_refinement \<longleftrightarrow>
     (cach, cach') \<in> cach_refinement_list \<and>
     (\<forall>L<length cach. cach ! L \<noteq> SEEN_UNKNOWN \<longrightarrow> L \<in> set support) \<and>
      (\<forall>L \<in> set support. L < length cach)\<close>
  by (auto simp: cach_refinement_def cach_refinement_nonull_def cach_refinement_list_def)

type_synonym (in -) conflict_min_cach_l = \<open>minimize_status list \<times> nat list\<close>

definition (in -) conflict_min_cach :: \<open>nat conflict_min_cach \<Rightarrow> nat \<Rightarrow> minimize_status\<close> where
  [simp]: \<open>conflict_min_cach cach L = cach L\<close>

definition (in -) conflict_min_cach_l :: \<open>conflict_min_cach_l \<Rightarrow> nat \<Rightarrow> minimize_status nres\<close> where
  \<open>conflict_min_cach_l = (\<lambda>(cach, sup) L. do {
     ASSERT(L < length cach);
     RETURN (cach ! L)
   })\<close>

sepref_definition (in -) conflict_min_cach_l_code
  is \<open>uncurry conflict_min_cach_l\<close>
  :: \<open>cach_refinement_l_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a minimize_status_assn\<close>
  unfolding conflict_min_cach_l_def
  by sepref

lemma nth_conflict_min_cach:
  \<open>(uncurry conflict_min_cach_l, uncurry (RETURN oo conflict_min_cach)) \<in>
     [\<lambda>(cach, L). L \<in># \<A>\<^sub>i\<^sub>n]\<^sub>f cach_refinement \<times>\<^sub>r nat_rel \<rightarrow> \<langle>minimize_status_rel\<rangle>nres_rel\<close>
  by (intro frefI nres_relI) (auto simp: cach_refinement_def map_fun_rel_def
      cach_refinement_nonull_def cach_refinement_list_def conflict_min_cach_l_def)

lemma conflict_min_cach_hnr[sepref_fr_rules]:
  \<open>(uncurry conflict_min_cach_l_code, uncurry (RETURN \<circ>\<circ> conflict_min_cach))
   \<in> [\<lambda>(a, b). b \<in># \<A>\<^sub>i\<^sub>n]\<^sub>a cach_refinement_assn\<^sup>k *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> minimize_status_assn\<close>
  using conflict_min_cach_l_code.refine[FCOMP nth_conflict_min_cach,
     unfolded cach_refinement_assn_def[symmetric]] .

definition (in -) conflict_min_cach_set_failed
   :: \<open>nat conflict_min_cach \<Rightarrow> nat \<Rightarrow> nat conflict_min_cach\<close>
where
  [simp]: \<open>conflict_min_cach_set_failed cach L = cach(L := SEEN_FAILED)\<close>

definition (in -) conflict_min_cach_set_failed_l
  :: \<open>conflict_min_cach_l \<Rightarrow> nat \<Rightarrow> conflict_min_cach_l nres\<close>
where
  \<open>conflict_min_cach_set_failed_l = (\<lambda>(cach, sup) L. do {
     ASSERT(L < length cach);
     RETURN (cach[L := SEEN_FAILED], sup @ [L])
   })\<close>

lemma conflict_min_cach_set_failed:
  \<open>(uncurry conflict_min_cach_set_failed_l, uncurry (RETURN oo conflict_min_cach_set_failed)) \<in>
     [\<lambda>(cach, L). L \<in># \<A>\<^sub>i\<^sub>n]\<^sub>f cach_refinement \<times>\<^sub>r nat_rel \<rightarrow> \<langle>cach_refinement\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
     (auto simp: cach_refinement_alt_def map_fun_rel_def cach_refinement_list_def
      conflict_min_cach_set_failed_l_def)


sepref_definition (in -) conflict_min_cach_set_failed_l_code
  is \<open>uncurry conflict_min_cach_set_failed_l\<close>
  :: \<open>cach_refinement_l_assn\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a cach_refinement_l_assn\<close>
  supply arl_append_hnr[sepref_fr_rules]
  unfolding conflict_min_cach_set_failed_l_def
  by sepref

lemma conflict_min_cach_set_failed_hnr[sepref_fr_rules]:
   \<open>(uncurry conflict_min_cach_set_failed_l_code,
        uncurry (RETURN \<circ>\<circ> conflict_min_cach_set_failed))
    \<in> [\<lambda>(a, b). b \<in># \<A>\<^sub>i\<^sub>n]\<^sub>a cach_refinement_assn\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> cach_refinement_assn\<close>
  using conflict_min_cach_set_failed_l_code.refine[FCOMP conflict_min_cach_set_failed,
    unfolded cach_refinement_assn_def[symmetric]] .

definition (in -) conflict_min_cach_set_removable
  :: \<open>nat conflict_min_cach \<Rightarrow> nat \<Rightarrow> nat conflict_min_cach\<close>
where
  [simp]: \<open>conflict_min_cach_set_removable cach L = cach(L:= SEEN_REMOVABLE)\<close>

definition (in -) conflict_min_cach_set_removable_l
  :: \<open>conflict_min_cach_l \<Rightarrow> nat \<Rightarrow> conflict_min_cach_l nres\<close>
where
  \<open>conflict_min_cach_set_removable_l = (\<lambda>(cach, sup) L. do {
     ASSERT(L < length cach);
     RETURN (cach[L := SEEN_REMOVABLE], sup @ [L])
   })\<close>

sepref_definition (in -) conflict_min_cach_set_removable_l_code
  is \<open>uncurry conflict_min_cach_set_removable_l\<close>
  :: \<open>cach_refinement_l_assn\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow>\<^sub>a cach_refinement_l_assn\<close>
  supply arl_append_hnr[sepref_fr_rules]
  unfolding conflict_min_cach_set_removable_l_def
  by sepref

lemma conflict_min_cach_set_removable:
  \<open>(uncurry conflict_min_cach_set_removable_l,
    uncurry (RETURN oo conflict_min_cach_set_removable)) \<in>
     [\<lambda>(cach, L). L \<in># \<A>\<^sub>i\<^sub>n]\<^sub>f cach_refinement \<times>\<^sub>r nat_rel \<rightarrow> \<langle>cach_refinement\<rangle>nres_rel\<close>
  by (intro frefI nres_relI)
     (auto simp: cach_refinement_alt_def map_fun_rel_def  cach_refinement_list_def
      conflict_min_cach_set_removable_l_def)

lemma conflict_min_cach_set_removable_hnr[sepref_fr_rules]:
   \<open>(uncurry conflict_min_cach_set_removable_l_code,
        uncurry (RETURN \<circ>\<circ> conflict_min_cach_set_removable))
    \<in> [\<lambda>(a, b). b \<in># \<A>\<^sub>i\<^sub>n]\<^sub>a cach_refinement_assn\<^sup>d *\<^sub>a uint32_nat_assn\<^sup>k \<rightarrow> cach_refinement_assn\<close>
  using conflict_min_cach_set_removable_l_code.refine[FCOMP conflict_min_cach_set_removable,
    unfolded cach_refinement_assn_def[symmetric]] .

definition mark_failed_lits_stack_inv where
  \<open>mark_failed_lits_stack_inv NU analyse = (\<lambda>(j, cach).
       (\<forall>(i, j) \<in> set analyse. j \<le> length (NU ! i) \<and> i < length NU \<and> j \<ge> 1 \<and> i > 0))\<close>


definition (in isasat_input_ops) mark_failed_lits_stack where
  \<open>mark_failed_lits_stack NU analyse cach = do {
    ( _, cach) \<leftarrow> WHILE\<^sub>T\<^bsup>mark_failed_lits_stack_inv NU analyse\<^esup>
      (\<lambda>(i, cach). i < length analyse)
      (\<lambda>(i, cach). do {
        ASSERT(i < length analyse);
        let (cls_idx, idx) = analyse ! i;
        ASSERT(atm_of (NU ! cls_idx ! (idx - 1)) \<in># \<A>\<^sub>i\<^sub>n);
        RETURN (i+1, cach (atm_of (NU ! cls_idx ! (idx - 1)) := SEEN_FAILED))
      })
      (0, cach);
   RETURN cach
   }\<close>

lemma literals_are_in_\<L>\<^sub>i\<^sub>n_mm_in_\<L>\<^sub>a\<^sub>l\<^sub>l_tl:
  assumes
    N1: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_mm (mset `# mset (tl xs))\<close> and \<open>xs \<noteq> []\<close> and
    i_xs: \<open>i < length xs\<close> and j_xs: \<open>j < length (xs ! i)\<close> \<open>i > 0\<close>
  shows \<open>xs ! i ! j \<in># \<L>\<^sub>a\<^sub>l\<^sub>l\<close>
  using literals_are_in_\<L>\<^sub>i\<^sub>n_mm_in_\<L>\<^sub>a\<^sub>l\<^sub>l[of \<open>tl xs\<close> \<open>i - 1\<close> j] assms
  by (cases xs) auto

lemma mark_failed_lits_stack_mark_failed_lits_wl:
  shows
    \<open>(uncurry2 mark_failed_lits_stack, uncurry2 mark_failed_lits_wl) \<in>
       [\<lambda>((NU, analyse), cach). literals_are_in_\<L>\<^sub>i\<^sub>n_mm (mset `# mset (tl NU)) \<and>
          mark_failed_lits_stack_inv NU analyse (0::nat, cach)]\<^sub>f
       Id \<times>\<^sub>f Id \<times>\<^sub>f Id \<rightarrow> \<langle>Id\<rangle>nres_rel\<close>
proof -
  have \<open>mark_failed_lits_stack NU analyse cach \<le> (mark_failed_lits_wl NU analyse cach)\<close>
    if
      NU_\<L>\<^sub>i\<^sub>n: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n_mm (mset `# mset (tl NU))\<close> and
      init: \<open>mark_failed_lits_stack_inv NU analyse (0::nat, cach)\<close>
    for NU analyse cach
  proof -
    define I where
      \<open>I = (\<lambda>(i :: nat, cach'). (\<forall>L. cach' L = SEEN_REMOVABLE \<longrightarrow> cach L = SEEN_REMOVABLE))\<close>
    have valid_atm: \<open>atm_of (NU ! cls_idx ! (idx - 1)) \<in># \<A>\<^sub>i\<^sub>n\<close>
      if
        \<open>mark_failed_lits_stack_inv NU analyse s\<close> and
        \<open>I s\<close> and
        \<open>case s of (i, cach) \<Rightarrow> i < length analyse\<close> and
        \<open>s = (i, cach)\<close> and
        i: \<open>i < length analyse\<close> and
        \<open>analyse ! i = (cls_idx, idx)\<close>
      for s i cach cls_idx idx
    proof -
      have [iff]: \<open>(\<forall>a b. (a, b) \<notin> set analyse) \<longleftrightarrow> False\<close>
        using i by (cases analyse) auto
      show ?thesis
        unfolding in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_in_atms_of_iff[symmetric] atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n[symmetric]
        apply (rule literals_are_in_\<L>\<^sub>i\<^sub>n_mm_in_\<L>\<^sub>a\<^sub>l\<^sub>l_tl)
        using NU_\<L>\<^sub>i\<^sub>n that  nth_mem[of i analyse]
        by (auto simp: mark_failed_lits_stack_inv_def I_def)
    qed
    show ?thesis
      unfolding mark_failed_lits_stack_def mark_failed_lits_wl_def
      apply (refine_vcg WHILEIT_rule_stronger_inv[where R = \<open>measure (\<lambda>(i, _). length analyse -i)\<close>
         and I' = I])
      subgoal by auto
      subgoal by (rule init)
      subgoal unfolding I_def by auto
      subgoal by auto
      subgoal for s i cach cls_idx idx
        by (rule valid_atm)
      subgoal unfolding mark_failed_lits_stack_inv_def by auto
      subgoal unfolding I_def by auto
      subgoal by auto
      subgoal unfolding I_def by auto
      done
  qed
  then show ?thesis
    by (intro frefI nres_relI) auto
qed

end

end
