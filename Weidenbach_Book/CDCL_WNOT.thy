theory CDCL_WNOT
imports CDCL_W_Termination CDCL_NOT
begin

section \<open>Link between Weidenbach's and NOT's CDCL\<close>
subsection \<open>Inclusion of the states\<close>
declare upt.simps(2)[simp del]
sledgehammer_params[verbose]

context cdcl_cw_ops
begin
abbreviation skip_or_resolve :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
"skip_or_resolve \<equiv> (\<lambda>S T. skip S T \<or> resolve S T)"

lemma rtranclp_cdcl_bj_skip_or_resolve_backtrack:
  assumes "cdcl_bj\<^sup>*\<^sup>* S U"
  shows "skip_or_resolve\<^sup>*\<^sup>* S U \<or> (\<exists>T. skip_or_resolve\<^sup>*\<^sup>* S T \<and> backtrack T U)"
  using assms
proof (induction)
  case base
  then show ?case by simp
next
  case (step U V) note st = this(1) and bj = this(2) and IH = this(3)
  consider
      (SU) "S = U"
    | (SUp) "cdcl_bj\<^sup>+\<^sup>+ S U"
    using st unfolding rtranclp_unfold by blast
  then show ?case
    proof cases
      case SUp
      have "skip_or_resolve\<^sup>*\<^sup>* S U"
        using bj IH by (fastforce simp: tranclp_unfold_end cdcl_bj.simps state_eq_def
          simp del: state_simp)
      then show ?thesis
        using bj by (metis (no_types, lifting) cdcl_bj.cases rtranclp.simps)
    next
      case SU
      then show ?thesis
        using bj by (metis (no_types, lifting) cdcl_bj.cases rtranclp.simps)
    qed
qed

lemma rtranclp_skip_or_resolve_rtranclp_cdcl:
  "skip_or_resolve\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl\<^sup>*\<^sup>* S T"
  by (induction rule: rtranclp_induct) (auto dest!: cdcl_bj.intros cdcl.intros cdcl_o.intros)

abbreviation backjump_l_cond :: " 'v literal multiset \<Rightarrow> 'v literal \<Rightarrow> 'st \<Rightarrow> bool" where
"backjump_l_cond \<equiv> \<lambda>C L S. True"

definition inv\<^sub>N\<^sub>O\<^sub>T :: "'st \<Rightarrow> bool" where
"inv\<^sub>N\<^sub>O\<^sub>T \<equiv> \<lambda>S. no_dup (trail S)"

declare inv\<^sub>N\<^sub>O\<^sub>T_def[simp]
end

fun convert_trail_from_W ::
  "('v,  'lvl, 'v literal multiset) marked_lit list
    \<Rightarrow> ('v, dpll_marked_level, unit) marked_lit list"  where
"convert_trail_from_W [] = []" |
"convert_trail_from_W (Propagated L _ # M) = Propagated L () # convert_trail_from_W M" |
"convert_trail_from_W (Marked L _ # M) = Marked L Level # convert_trail_from_W M"

lemma atm_convert_trail_from_W[simp]:
  "(\<lambda>l. atm_of (lit_of l)) ` set (convert_trail_from_W xs) = (\<lambda>l. atm_of (lit_of l)) ` set xs"
  by (induction rule: marked_lit_list_induct) simp_all

lemma no_dup_convert_from_W[simp]:
  "no_dup (convert_trail_from_W M) \<longleftrightarrow> no_dup M"
  by (induction rule: marked_lit_list_induct) simp_all

lemma lits_of_convert_trail_from_W[simp]:
  "lits_of (convert_trail_from_W M) = lits_of M"
  by (induction rule: marked_lit_list_induct) simp_all

lemma convert_trail_from_W_true_annots[simp]:
  "convert_trail_from_W M \<Turnstile>as C \<longleftrightarrow> M \<Turnstile>as C"
  by (auto simp: true_annots_true_cls)

lemma defined_lit_convert_trail_from_W[simp]:
  "defined_lit L (convert_trail_from_W S) \<longleftrightarrow> defined_lit L S"
  by (auto simp: defined_lit_map)

lemma convert_trail_from_W_append[simp]:
  "convert_trail_from_W (M @ M') = convert_trail_from_W M @ convert_trail_from_W M'"
  by (induction M rule: marked_lit_list_induct) simp_all

lemma length_convert_trail_from_W[simp]:
  "length (convert_trail_from_W W) = length W"
  by (induction W rule: convert_trail_from_W.induct) auto

lemma convert_trail_from_W_nil_iff[simp]: "convert_trail_from_W S = [] \<longleftrightarrow> S = []"
  by (induction S rule: convert_trail_from_W.induct) auto

text \<open>The values @{term "0::nat"} and @{term "{#}"} do not matter.\<close>
fun convert_marked_lit_from_NOT where
"convert_marked_lit_from_NOT (Propagated L _) = Propagated L {#}" |
"convert_marked_lit_from_NOT (Marked L _) = Marked L 0"

fun convert_trail_from_NOT ::
  "('v, dpll_marked_level, unit) marked_lit list
    \<Rightarrow> ('v,  nat, 'v literal multiset) marked_lit list"  where
"convert_trail_from_NOT [] = []" |
"convert_trail_from_NOT (L # M) = convert_marked_lit_from_NOT L # convert_trail_from_NOT M"

lemma convert_trail_from_W_from_NOT[simp]:
  "convert_trail_from_W (convert_trail_from_NOT M) = M"
  by (induction rule: marked_lit_list_induct) auto

lemma convert_trail_from_W_cons_convert_lit_from_NOT[simp]:
  "convert_trail_from_W (convert_marked_lit_from_NOT L # M) = L # convert_trail_from_W M"
  by (cases L) auto

lemma convert_trail_from_W_tl[simp]:
  "convert_trail_from_W (tl M) = tl (convert_trail_from_W M)"
  by (induction rule: convert_trail_from_W.induct) simp_all

lemma length_convert_trail_from_NOT[simp]:
  "length (convert_trail_from_NOT W) = length W"
  by (induction W rule: convert_trail_from_NOT.induct) auto

abbreviation trail\<^sub>N\<^sub>O\<^sub>T where
"trail\<^sub>N\<^sub>O\<^sub>T \<equiv> convert_trail_from_W o fst"

sublocale cw_state \<subseteq> dpll_state "convert_trail_from_W o trail" clauses
  "\<lambda>L S. cons_trail (convert_marked_lit_from_NOT L) S"
  "\<lambda>S. tl_trail S"
  "\<lambda>C S. add_learned_cls C S"
  "\<lambda>C S. remove_cls C S"
  by unfold_locales auto

(*
  Here there are some linorder-sort issues.
  sublocale cdcl_cw_ops \<subseteq> cdcl\<^sub>N\<^sub>O\<^sub>T_with_backtrack_and_restarts trail clauses update_trail
  (* update_cls: *)"\<lambda>C S. add_init_cls C (update_learned_clss {} S)"
  (* propagate conditions: *) "\<lambda>_ S. conflicting S = C_True" "\<lambda>C L S. backjump_l_cond C L S
    \<and> distinct_mset (C + {#L#}) \<and> \<not>tautology (C + {#L#})" *)

sublocale cdcl_cw_ops \<subseteq> cdcl\<^sub>N\<^sub>O\<^sub>T_merge_bj_learn_ops "convert_trail_from_W o trail" clauses
  "\<lambda>L S. cons_trail (convert_marked_lit_from_NOT L) S"
  "\<lambda>S. tl_trail S"
  "\<lambda>C S. add_learned_cls C S"
  "\<lambda>C S. remove_cls C S"
  (* propagate conditions: *)"\<lambda>_ _. True"
  (* backjump conditions: *) "\<lambda>_ S. conflicting S = C_True" "\<lambda>C L S. backjump_l_cond C L S
    \<and> distinct_mset (C + {#L#}) \<and> \<not>tautology (C + {#L#})"
  by unfold_locales

sublocale cdcl_cw_ops \<subseteq> cdcl\<^sub>N\<^sub>O\<^sub>T_merge_bj_learn_proxy  "convert_trail_from_W o trail" clauses
  "\<lambda>L S. cons_trail (convert_marked_lit_from_NOT L) S"
  "\<lambda>S. tl_trail S"
  "\<lambda>C S. add_learned_cls C S"
  "\<lambda>C S. remove_cls C S"
  "\<lambda>_ _. True"
  "\<lambda>_ S. conflicting S = C_True" backjump_l_cond inv\<^sub>N\<^sub>O\<^sub>T
proof (unfold_locales, goal_cases)
  case 2
  then show ?case using cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_no_dup_inv by auto
next
  case (1 C' S C F' K d F L)
  moreover
    let ?C' = "remdups_mset C'"
    have "L \<notin># C'"
      using \<open>F \<Turnstile>as CNot C'\<close> \<open>undefined_lit L F\<close> Marked_Propagated_in_iff_in_lits_of
      in_CNot_implies_uminus(2) by blast
    then have "distinct_mset (?C' + {#L#})"
      by (metis count_mset_set(3) distinct_mset_remdups_mset distinct_mset_single_add
        less_irrefl_nat mem_set_mset_iff remdups_mset_def)
  moreover
    have "no_dup F"
      using \<open>inv\<^sub>N\<^sub>O\<^sub>T S\<close> \<open>(convert_trail_from_W \<circ> trail) S = F' @ Marked K d # F\<close>
      unfolding inv\<^sub>N\<^sub>O\<^sub>T_def
      by (smt comp_apply distinct.simps(2) distinct_append list.simps(9) map_append
        no_dup_convert_from_W)
    then have "consistent_interp (lits_of F)"
      using distinctconsistent_interp by blast
    then have "\<not> tautology (C')"
      using \<open>F \<Turnstile>as CNot C'\<close> consistent_CNot_not_tautology true_annots_true_cls by blast
    then have "\<not> tautology (?C' + {#L#})"
      using \<open>F \<Turnstile>as CNot C'\<close> \<open>undefined_lit L F\<close> by (metis  CNot_remdups_mset
        Marked_Propagated_in_iff_in_lits_of add.commute in_CNot_uminus tautology_add_single
        tautology_remdups_mset true_annot_singleton true_annots_def)
  show ?case
    proof -
      have f2: "no_dup ((convert_trail_from_W \<circ> trail) S)"
        using \<open>inv\<^sub>N\<^sub>O\<^sub>T S\<close> unfolding inv\<^sub>N\<^sub>O\<^sub>T_def by simp
      have f3: "atm_of L \<in> atms_of_mu (clauses S)
        \<union> atm_of ` lits_of ((convert_trail_from_W \<circ> trail) S)"
        using \<open>(convert_trail_from_W \<circ> trail) S = F' @ Marked K d # F\<close>
        \<open>atm_of L \<in> atms_of_mu (clauses S) \<union> atm_of ` lits_of (F' @ Marked K d # F)\<close> by presburger
      have f4: "clauses S \<Turnstile>pm remdups_mset C' + {#L#}"
        by (metis (no_types) \<open>L \<notin># C'\<close> \<open>clauses S \<Turnstile>pm C' + {#L#}\<close> remdups_mset_singleton_sum(2)
          true_clss_cls_remdups_mset union_commute)
      have "F \<Turnstile>as CNot (remdups_mset C')"
        by (simp add: \<open>F \<Turnstile>as CNot C'\<close>)
      then show ?thesis
        using f4 f3 f2 \<open>\<not> tautology (remdups_mset C' + {#L#})\<close> backjump_l.intros calculation(2-5,9)
        state_eq\<^sub>N\<^sub>O\<^sub>T_ref by blast
    qed
qed

sublocale cdcl_cw_ops \<subseteq> cdcl\<^sub>N\<^sub>O\<^sub>T_merge_bj_learn_proxy2  "convert_trail_from_W o trail" clauses
  "\<lambda>L S. cons_trail (convert_marked_lit_from_NOT L) S"
  "\<lambda>S. tl_trail S"
  "\<lambda>C S. add_learned_cls C S"
  "\<lambda>C S. remove_cls C S" "\<lambda>_ _. True"  inv\<^sub>N\<^sub>O\<^sub>T
  "\<lambda>_ S. conflicting S = C_True" backjump_l_cond
  by unfold_locales

sublocale cdcl_cw_ops \<subseteq> cdcl\<^sub>N\<^sub>O\<^sub>T_merge_bj_learn "convert_trail_from_W o trail" clauses
  "\<lambda>L S. cons_trail (convert_marked_lit_from_NOT L) S"
  "\<lambda>S. tl_trail S"
  "\<lambda>C S. add_learned_cls C S"
  "\<lambda>C S. remove_cls C S" "\<lambda>_ _. True"  inv\<^sub>N\<^sub>O\<^sub>T
  "\<lambda>_ S. conflicting S = C_True" backjump_l_cond
  apply unfold_locales
   using dpll\<^sub>N\<^sub>O\<^sub>T_bj_no_dup apply simp
  using cdcl\<^sub>N\<^sub>O\<^sub>T.simps cdcl\<^sub>N\<^sub>O\<^sub>T_no_dup by auto

context cdcl_cw_ops
begin
text \<open>Notations are lost while proving locale inclusion:\<close>
notation state_eq\<^sub>N\<^sub>O\<^sub>T (infix "\<sim>\<^sub>N\<^sub>O\<^sub>T" 50)

subsection \<open>More lemmas conflict--propagate and backjumping\<close>
subsubsection \<open>Termination\<close>

lemma cdcl_cp_normalized_element_all_inv:
  assumes inv: "cdcl_all_struct_inv S"
  obtains T where "full cdcl_cp S T"
  using assms cdcl_cp_normalized_element unfolding cdcl_all_struct_inv_def by blast

lemma cdcl_bj_measure:
  assumes "cdcl_bj S T"
  shows "length (trail S) + (if conflicting S = C_True then 0 else 1)
    > length (trail T) +  (if conflicting T = C_True then 0 else 1)"
  using assms by (induction rule: cdcl_bj.induct) (fastforce dest:arg_cong[of _ _ length])+

lemma cdcl_bj_wf:
  "wf {(b,a). cdcl_bj a b}"
  apply (rule wfP_if_measure[of "\<lambda>_. True"
      _ "\<lambda>T. length (trail T) +  (if conflicting T = C_True then 0 else 1)", simplified])
  using cdcl_bj_measure by blast

lemma rtranclp_skip_state_decomp:
  assumes "skip\<^sup>*\<^sup>* S T"
  shows
    "\<exists>M. trail S = M @ trail T \<and> (\<forall>m\<in>set M. \<not>is_marked m)" and
    "T \<sim> delete_trail_and_rebuild (trail T) S"
  using assms by (induction rule: rtranclp_induct) (auto simp del: state_simp simp: state_eq_def)+

subsubsection \<open>More backjumping\<close>
paragraph \<open>Backjumping after skipping or jump directly\<close>
lemma rtranclp_skip_backtrack_backtrack:
  assumes
    "skip\<^sup>*\<^sup>* S T" and
    "backtrack T W" and
    "cdcl_all_struct_inv S"
  shows "backtrack S W"
  using assms
proof induction
  case base
  thus ?case by simp
next
  case (step T V) note st = this(1) and skip = this(2) and IH = this(3) and bt = this(4) and
    inv = this(5)
  obtain M N k M1 M2 K i D L U where
    V: "state V = (M, N, U, k, C_Clause (D + {#L#}))" and
    W: "state W = (Propagated L (D + {#L#}) # M1, N, {#D + {#L#}#} + U,
      get_maximum_level D M, C_True)" and
    decomp: "(Marked K (i+1) # M1, M2) \<in> set (get_all_marked_decomposition M)" and
    lev_l: "get_level L M = k" and
    lev_l_D: "get_level L M = get_maximum_level (D+{#L#}) M" and
    i: "i = get_maximum_level D M"
    using bt by auto
  let ?D = "(D + {#L#})"
  obtain L' C' where
    T: "state T = (Propagated L' C' # M, N, U, k, C_Clause ?D)" and
    "V \<sim> tl_trail T" and
    "-L' \<notin># ?D" and
    "?D \<noteq> {#}"
    using skip V by force

  let ?M =  "Propagated L' C' # M"
  have "cdcl\<^sup>*\<^sup>* S T" using bj cdcl_bj.skip mono_rtranclp[of skip cdcl S T] other st by meson
  hence inv': "cdcl_all_struct_inv T"
    using rtranclp_cdcl_all_struct_inv_inv inv by blast
  have M_lev: "cdcl_M_level_inv T" using inv' unfolding cdcl_all_struct_inv_def by auto
  hence n_d': "no_dup ?M"
    using T unfolding cdcl_M_level_inv_def by auto

  have "k > 0"
    using decomp M_lev T unfolding cdcl_M_level_inv_def by auto
  hence "atm_of L \<in> atm_of ` lits_of M"
    using lev_l get_rev_level_ge_0_atm_of_in by fastforce
  hence L_L': "atm_of L \<noteq> atm_of L'"
    using n_d' unfolding lits_of_def by auto
  have L'_M: "atm_of L' \<notin> atm_of ` lits_of M"
    using n_d' unfolding lits_of_def by auto
  have "?M \<Turnstile>as CNot ?D"
    using inv' T unfolding cdcl_conflicting_def cdcl_all_struct_inv_def by auto
  hence "L' \<notin># ?D"
    using L_L' L'_M unfolding true_annots_def by (auto simp add: true_annot_def true_cls_def
      atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set Ball_mset_def
      split: split_if_asm)
  have [simp]: "trail (reduce_trail_to M1 T) = M1"
    by (smt One_nat_def Pair_inject
       T decomp diff_less in_get_all_marked_decomposition_trail_update_trail length_greater_0_conv
       length_tl lessI list.sel(2) list.sel(3) reduce_trail_to_length_ne
       trail_reduce_trail_to_length_le trail_tl_trail)
  have "skip\<^sup>*\<^sup>* S V"
    using st skip by auto
  have [simp]: "init_clss S = N" and [simp]: "learned_clss S = U"
    using rtranclp_skip_state_decomp[OF \<open>skip\<^sup>*\<^sup>* S V\<close>] V
    by (auto simp del: state_simp simp: state_eq_def)
  hence W_S: "W \<sim> cons_trail (Propagated L (D + {#L#})) (reduce_trail_to M1
  (add_learned_cls (D + {#L#}) (update_backtrack_lvl i (update_conflicting C_True T))))"
    using W i T by (auto simp del: state_simp simp: state_eq_def)

  obtain M2' where
    "(Marked K (i+1) # M1, M2') \<in> set (get_all_marked_decomposition ?M)"
    using decomp by (cases "hd (get_all_marked_decomposition M)",
      cases "get_all_marked_decomposition M") auto
  moreover
    from L_L'
    have "get_level L ?M = k"
    using lev_l \<open>-L' \<notin># ?D\<close> by (auto split: split_if_asm)
  moreover
    have "atm_of L' \<notin> atms_of D"
      using \<open>L' \<notin># ?D\<close> \<open>-L' \<notin># ?D\<close> by (simp add: atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set
        atms_of_def)
    hence "get_level L ?M = get_maximum_level (D+{#L#}) ?M"
      using lev_l_D L_L' by simp
  moreover have "i = get_maximum_level D ?M"
    using i \<open>atm_of L' \<notin> atms_of D\<close> by auto
  moreover

  ultimately have "backtrack T W"
    using T(1) W_S by blast
  thus ?thesis using IH inv by blast
qed

lemma fst_get_all_marked_decomposition_prepend_not_marked:
  assumes "\<forall>m\<in>set MS. \<not> is_marked m"
  shows "set (map fst (get_all_marked_decomposition M))
    = set (map fst (get_all_marked_decomposition (MS @ M)))"
    using assms apply (induction MS rule: marked_lit_list_induct)
    apply auto[2]
    by (case_tac "get_all_marked_decomposition (xs @ M)") simp_all

text \<open>See also @{thm rtranclp_skip_backtrack_backtrack}\<close>
lemma rtranclp_skip_backtrack_backtrack_end:
  assumes
    skip: "skip\<^sup>*\<^sup>* S T" and
    bt: "backtrack S W" and
    inv: "cdcl_all_struct_inv S"
  shows "backtrack T W"
  using assms
proof -
  obtain M N k M1 M2 K i D L U where
    S: "state S = (M, N, U, k, C_Clause (D + {#L#}))" and
    W: "state W = (Propagated L ( (D + {#L#})) # M1, N, {#D + {#L#}#} + U,
       get_maximum_level D M, C_True)"
  and
    decomp: "(Marked K (i+1) # M1, M2) \<in> set (get_all_marked_decomposition M)" and
    lev_l: "get_level L M = k" and
    lev_l_D: "get_level L M = get_maximum_level (D+{#L#}) M" and
    i: "i = get_maximum_level D M"
    using bt by auto
  let ?D = "(D + {#L#})"

  (* M\<^sub>T is a proxy to allow auto to unfold T*)
  obtain MS M\<^sub>T where M: "M = MS @ M\<^sub>T" and M\<^sub>T: "M\<^sub>T = trail T" and nm: "\<forall>m\<in>set MS. \<not>is_marked m"
    using rtranclp_skip_state_decomp(1)[OF skip] S by auto
  have T: "state T = (M\<^sub>T, N, U, k, C_Clause ?D)"
    using M\<^sub>T rtranclp_skip_state_decomp(2) skip S
    by (metis backtrack_lvl_append_trail backtrack_lvl_update_trial conflicting_append_trail
      conflicting_update_trial delete_trail_and_rebuild.simps init_clss_append_trail
      init_clss_update_trial learned_clss_append_trail learned_clss_update_trial old.prod.inject
      state_eq_backtrack_lvl state_eq_conflicting state_eq_init_clss state_eq_learned_clss)
  have "cdcl_all_struct_inv T"
    apply (rule rtranclp_cdcl_all_struct_inv_inv[OF _ inv])
    using bj cdcl_bj.skip local.skip other rtranclp_mono[of skip cdcl] by blast
  hence "M\<^sub>T \<Turnstile>as CNot ?D"
    unfolding cdcl_all_struct_inv_def cdcl_conflicting_def using T by blast
  have "\<forall>L\<in>#?D. atm_of L \<in> atm_of ` lits_of M\<^sub>T"
    proof -
      have f1: "\<And>l. \<not> M\<^sub>T \<Turnstile>a {#- l#} \<or> atm_of l \<in> atm_of ` lits_of M\<^sub>T"
        by (simp add: atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set in_lit_of_true_annot
          lits_of_def)
      have "\<And>l. l \<notin># D \<or> - l \<in> lits_of M\<^sub>T"
        using \<open>M\<^sub>T \<Turnstile>as CNot (D + {#L#})\<close> multi_member_split by fastforce
      thus ?thesis
        using f1 by (meson \<open>M\<^sub>T \<Turnstile>as CNot (D + {#L#})\<close> ball_msetI true_annots_CNot_all_atms_defined)
    qed
  moreover have "no_dup M"
    using inv S unfolding cdcl_all_struct_inv_def cdcl_M_level_inv_def by auto
  ultimately have "\<forall>L\<in>#?D. atm_of L \<notin> atm_of ` lits_of MS"
    unfolding M unfolding lits_of_def by auto
  hence H: "\<And>L. L\<in>#?D \<Longrightarrow> get_level L M  = get_level L M\<^sub>T"
    unfolding M by (fastforce simp: lits_of_def)
  have [simp]: "get_maximum_level ?D M = get_maximum_level ?D M\<^sub>T"
    by (metis \<open>M\<^sub>T \<Turnstile>as CNot (D + {#L#})\<close>  M nm ball_msetI true_annots_CNot_all_atms_defined
      get_maximum_level_skip_un_marked_not_present)

  have lev_l': "get_level L M\<^sub>T = k"
    using lev_l by (auto simp: H)
  have [simp]:"trail (reduce_trail_to M1 T) = M1"
    using T decomp M nm by (smt M\<^sub>T append_assoc beginning_not_marked_invert
      get_all_marked_decomposition_exists_prepend reduce_trail_to_trail_tl_trail_decomp)
  have W: "W \<sim> cons_trail (Propagated L (D + {#L#})) (reduce_trail_to M1
    (add_learned_cls (D + {#L#}) (update_backtrack_lvl i (update_conflicting C_True T))))"
    using W T i decomp by (auto simp del: state_simp simp: state_eq_def)

  have lev_l_D': "get_level L M\<^sub>T = get_maximum_level (D+{#L#}) M\<^sub>T"
    using lev_l_D by (auto simp: H)
  have [simp]: "get_maximum_level D M = get_maximum_level D M\<^sub>T"
    proof -
      have "\<And>ms m. \<not> (ms::('v, nat, 'v literal multiset) marked_lit list) \<Turnstile>as CNot m
          \<or> (\<forall>l\<in>#m. atm_of l \<in> atm_of ` lits_of ms)"
        by (simp add: atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set in_CNot_implies_uminus(2))
      then have "\<forall>l\<in>#D. atm_of l \<in> atm_of ` lits_of M\<^sub>T"
        using \<open>M\<^sub>T \<Turnstile>as CNot (D + {#L#})\<close> by auto
      then show ?thesis
        by (metis M get_maximum_level_skip_un_marked_not_present nm)
    qed
  hence i': "i = get_maximum_level D M\<^sub>T"
    using i by auto
  have "Marked K (i + 1) # M1 \<in> set (map fst (get_all_marked_decomposition M))"
    using Set.imageI[OF decomp, of fst] by auto
  hence "Marked K (i + 1) # M1 \<in> set (map fst (get_all_marked_decomposition M\<^sub>T))"
    using fst_get_all_marked_decomposition_prepend_not_marked[OF nm] unfolding M  by auto
  then obtain M2' where decomp':"(Marked K (i+1) # M1, M2') \<in> set (get_all_marked_decomposition M\<^sub>T)"
    by auto
  thus "backtrack T W"
    using backtrack.intros[OF T decomp' lev_l'] lev_l_D' i' W by force
qed


lemma cdcl_bj_decomp_resolve_skip_and_bj:
  assumes "cdcl_bj\<^sup>*\<^sup>* S T"
  shows "(skip_or_resolve\<^sup>*\<^sup>* S T
    \<or> (\<exists>U. skip_or_resolve\<^sup>*\<^sup>* S U \<and> backtrack U T))"
  using assms
proof induction
  case base
  thus ?case by simp
next
  case (step T U) note st = this(1) and bj = this(2) and IH = this(3)
  have IH: "skip_or_resolve\<^sup>*\<^sup>* S T"
    proof -
      { assume "(\<exists>U. skip_or_resolve\<^sup>*\<^sup>* S U \<and> backtrack U T)"
        then obtain V where
          "backtrack V T"
          by blast
        with bj have False by induction fastforce+
      }
      thus ?thesis using IH by blast
    qed
  show ?case
    using bj
    proof (cases rule: cdcl_bj.cases)
      case backtrack
      thus ?thesis using IH by blast
    qed (metis (no_types, lifting) IH rtranclp.simps)+
qed

lemma resolve_skip_deterministic:
  "resolve S T \<Longrightarrow> skip S U \<Longrightarrow> False"
  by fastforce

lemma backtrack_unique:
  assumes
    bt_T: "backtrack S T" and
    bt_U: "backtrack S U" and
    inv: "cdcl_all_struct_inv S"
  shows "T \<sim> U"
proof -
  obtain M N U' k D L i K M1 M2 where
    S: "state S = (M, N, U', k, C_Clause (D + {#L#}))" and
    decomp: "(Marked K (i+1) # M1, M2) \<in> set (get_all_marked_decomposition M)" and
    "get_level L M = k" and
    "get_level L M = get_maximum_level (D+{#L#}) M" and
    "get_maximum_level D M = i" and
    T: "state T = (Propagated L ( (D+{#L#})) # M1 , N, {#D + {#L#}#} + U', i, C_True)"
    using bt_T by auto

  obtain  D' L' i' K' M1' M2' where
    S': "state S = (M, N, U', k, C_Clause (D' + {#L'#}))" and
    decomp': "(Marked K' (i'+1) # M1', M2') \<in> set (get_all_marked_decomposition M)" and
    "get_level L' M = k" and
    "get_level L' M = get_maximum_level (D'+{#L'#}) M" and
    "get_maximum_level D' M = i'" and
    U: "state U = (Propagated L' ((D'+{#L'#})) # M1', N, {#D' + {#L'#}#} +U', i', C_True)"
    using bt_U S by fastforce
  obtain c where M: "M = c @ M2 @ Marked K (i + 1) # M1"
    using decomp by auto
  obtain c' where M': "M = c' @ M2' @ Marked K' (i' + 1) # M1'"
    using decomp' by auto
  have marked: "get_all_levels_of_marked M = rev [1..<1+k]"
    using inv S unfolding cdcl_all_struct_inv_def cdcl_M_level_inv_def by auto
  hence "i < k"
    unfolding M
    by (force simp add: rev_swap[symmetric] dest!: arg_cong[of _ _ set])

  have [simp]: "L = L'"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      hence "L' \<in># D"
        using S unfolding S' by (fastforce simp: multiset_eq_iff split: split_if_asm)
      hence "get_maximum_level D M \<ge> k"
        using \<open>get_level L' M = k\<close> get_maximum_level_ge_get_level by blast
      thus False using \<open>get_maximum_level D M = i\<close> \<open>i < k\<close> by auto
    qed
  hence [simp]: "D = D'"
    using S S' by auto
  have [simp]: "i=i'" using \<open>get_maximum_level D' M = i'\<close> \<open>get_maximum_level D M = i\<close> by auto

  text \<open>Automation in a step later...\<close>
  have H: "\<And>a A B. insert a A = B \<Longrightarrow> a : B"
    by blast
  have "get_all_levels_of_marked (c@M2) = rev [i+2..<1+k]" and
    "get_all_levels_of_marked (c'@M2') = rev [i+2..<1+k]"
    using marked unfolding M
    using marked unfolding M'
    unfolding rev_swap[symmetric] by (auto dest: append_cons_eq_upt_length_i_end)
  from arg_cong[OF this(1), of set] arg_cong[OF this(2), of set]
  have
    "dropWhile (\<lambda>L. \<not>is_marked L \<or> level_of L \<noteq> Suc i) (c @ M2) = []" and
    "dropWhile (\<lambda>L. \<not>is_marked L \<or> level_of L \<noteq> Suc i) (c' @ M2') = []"
      unfolding dropWhile_eq_Nil_conv Ball_def
      by (intro allI; case_tac x; auto dest!: H simp add: in_set_conv_decomp)+

  hence "M1 = M1'"
    using arg_cong[OF M, of "dropWhile (\<lambda>L. \<not>is_marked L \<or> level_of L \<noteq> Suc i)"]
    unfolding M' by auto
  thus ?thesis using T U by (auto simp del: state_simp simp: state_eq_def)
qed

lemma if_can_apply_backtrack_no_more_resolve:
  assumes
    skip: "skip\<^sup>*\<^sup>* S U" and
    bt: "backtrack S T" and
    inv: "cdcl_all_struct_inv S"
  shows "\<not>resolve U V"
proof (rule ccontr)
  assume resolve: "\<not>\<not>resolve U V"

  obtain L C M N U' k D where
    U: "state U = (Propagated L ( (C + {#L#})) # M, N, U', k, C_Clause (D + {#-L#}))"and
    "get_maximum_level D (Propagated L ( (C + {#L#})) # M) = k" and
    "state V = (M, N, U', k, C_Clause (remdups_mset (D + C)))"
    using resolve by auto

  have
    S: "init_clss S = N"
       "learned_clss S = U'"
       "backtrack_lvl S = k"
       "conflicting S = C_Clause (D + {#-L#})"
    using rtranclp_skip_state_decomp(2)[OF skip] U by (auto simp del: state_simp simp: state_eq_def)
  obtain M\<^sub>0 where
    tr_S: "trail S = M\<^sub>0 @ trail U" and
    nm: "\<forall>m\<in>set M\<^sub>0. \<not>is_marked m"
    using rtranclp_skip_state_decomp[OF skip] by blast

  obtain M' D' L' i K M1 M2 where
    S': "state S = (M', N, U', k, C_Clause (D' + {#L'#}))"  and
    decomp: "(Marked K (i+1) # M1, M2) \<in> set (get_all_marked_decomposition M')" and
    "get_level L' M' = k" and
    "get_level L' M' = get_maximum_level (D'+{#L'#}) M'" and
    "get_maximum_level D' M' = i" and
    T: "state T = (Propagated L' ( (D'+{#L'#})) # M1 , N, {#D' + {#L'#}#}+U', i, C_True)"
    using bt S apply (cases S) by auto
  obtain c where M: "M' = c @ M2 @ Marked K (i + 1) # M1"
    using get_all_marked_decomposition_exists_prepend[OF decomp] by auto
  have marked: "get_all_levels_of_marked M' = rev [1..<1+k]"
    using inv S' unfolding cdcl_all_struct_inv_def cdcl_M_level_inv_def by auto
  hence "i < k"
    unfolding M by (force simp add: rev_swap[symmetric] dest!: arg_cong[of _ _ set])

  have DD': "D' + {#L'#} = D + {#-L#}"
    using S S' by auto
  have [simp]: "L' = -L"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      hence "-L \<in># D'"
        using DD' by (metis add_diff_cancel_right' diff_single_trivial diff_union_swap
          multi_self_add_other_not_self)
      moreover
        have M': "M' = M\<^sub>0 @ Propagated L ( (C + {#L#})) # M"
          using tr_S U S S' by (auto simp: lits_of_def)
        have "no_dup M'"
           using inv U S' unfolding cdcl_all_struct_inv_def cdcl_M_level_inv_def by auto
        have atm_L_notin_M: "atm_of L \<notin> atm_of ` (lits_of M)"
          using \<open>no_dup M'\<close> M' U S S' by (auto simp: lits_of_def)
        have "get_all_levels_of_marked M' = rev [1..<1+k]"
          using inv U S' unfolding cdcl_all_struct_inv_def cdcl_M_level_inv_def by auto
        hence "get_all_levels_of_marked M = rev [1..<1+k]"
          using nm M' S' U by (simp add: get_all_levels_of_marked_no_marked)
        hence get_lev_L:
          "get_level L (Propagated L ( (C + {#L#})) # M) = k"
          using get_level_get_rev_level_get_all_levels_of_marked[OF atm_L_notin_M,
            of "[Propagated L ((C + {#L#}))]"] by simp
        have "atm_of L \<notin> atm_of ` (lits_of (rev M\<^sub>0))"
          using \<open>no_dup M'\<close> M' U S' by (auto simp: lits_of_def)
        hence "get_level L M' = k"
          using get_rev_level_notin_end[of L "rev M\<^sub>0" 0
            "rev M @ Propagated L ( (C + {#L#})) # []"]
          using tr_S get_lev_L M' U S' by (simp add:nm lits_of_def)
      ultimately have "get_maximum_level D' M' \<ge> k"
        by (metis get_maximum_level_ge_get_level get_rev_level_uminus)
      thus False
        using \<open>i < k\<close> unfolding \<open>get_maximum_level D' M' = i\<close> by auto
    qed
  have [simp]: "D = D'" using DD' by auto
  have "cdcl\<^sup>*\<^sup>* S U"
    using bj cdcl_bj.skip local.skip mono_rtranclp[of skip cdcl S U] other by meson
  hence "cdcl_all_struct_inv U"
    using inv rtranclp_cdcl_all_struct_inv_inv by blast
  hence "Propagated L ( (C + {#L#})) # M \<Turnstile>as CNot (D' + {#L'#})"
    using cdcl_all_struct_inv_def cdcl_conflicting_def U by auto
  hence "\<forall>L'\<in>#D. atm_of L' \<in> atm_of ` lits_of (Propagated L ( (C + {#L#})) # M)"
    by (metis CNot_plus CNot_singleton Un_insert_right \<open>D = D'\<close> true_annots_insert ball_msetI
      atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set  in_CNot_implies_uminus(2)
      sup_bot.comm_neutral)
  hence "get_maximum_level D M' = k"
     using tr_S nm U S'
       get_maximum_level_skip_un_marked_not_present[of D "
         Propagated L ( (C + {#L#})) # M" M\<^sub>0]
     unfolding  \<open>get_maximum_level D (Propagated L ( (C + {#L#})) # M) = k\<close>
     unfolding \<open>D = D'\<close>
     by simp
  show False
    using \<open>get_maximum_level D' M' = i\<close> \<open>get_maximum_level D M' = k\<close> \<open>i < k\<close> by auto
qed

lemma if_can_apply_resolve_no_more_backtrack:
  assumes
    skip: "skip\<^sup>*\<^sup>* S U" and
    resolve: "resolve S T" and
    inv: "cdcl_all_struct_inv S"
  shows "\<not>backtrack U V"
  using assms
  by (meson if_can_apply_backtrack_no_more_resolve rtranclp.rtrancl_refl
    rtranclp_skip_backtrack_backtrack)

lemma if_can_apply_backtrack_skip_or_resolve_is_skip:
  assumes
    bt: "backtrack S T" and
    skip: "skip_or_resolve\<^sup>*\<^sup>* S U" and
    inv: "cdcl_all_struct_inv S"
  shows "skip\<^sup>*\<^sup>* S U"
  using assms(2,3,1)
  by induction (simp_all add: if_can_apply_backtrack_no_more_resolve)

lemma cdcl_bj_bj_decomp:
  assumes "cdcl_bj\<^sup>*\<^sup>* S W" and "cdcl_all_struct_inv S"
  shows
    "(\<exists>T U V. (\<lambda>S T. skip_or_resolve S T \<and> no_step backtrack S)\<^sup>*\<^sup>* S T
        \<and> (\<lambda>T U. resolve T U \<and> no_step backtrack T) T U
        \<and> skip\<^sup>*\<^sup>* U V  \<and> backtrack V W)
    \<or> (\<exists>T U. (\<lambda>S T. skip_or_resolve S T \<and> no_step backtrack S)\<^sup>*\<^sup>* S T
        \<and> (\<lambda>T U. resolve T U \<and> no_step backtrack T) T U \<and> skip\<^sup>*\<^sup>* U W)
    \<or> (\<exists>T. skip\<^sup>*\<^sup>* S T  \<and> backtrack T W)
    \<or> skip\<^sup>*\<^sup>* S W" (is "?RB S W \<or> ?R S W \<or> ?SB S W \<or> ?S S W")
  using assms
proof induction
  case base
  thus ?case by simp
next
  case (step W X) note st = this(1) and bj = this(2) and IH = this(3)[OF this(4)] and inv = this(4)
  have "\<not>?RB S W" and "\<not>?SB S W"
    using bj by (fastforce simp: cdcl_bj.simps)+
  hence IH: "?R S W \<or> ?S S W" using IH by blast

  have "cdcl\<^sup>*\<^sup>* S W" by (metis cdcl_o.bj mono_rtranclp other st)
  hence inv_W: "cdcl_all_struct_inv W" by (simp add: rtranclp_cdcl_all_struct_inv_inv step.prems)
  consider
      (BT) X' where "backtrack W X'"
    | (skip) "no_step backtrack W" and "skip W X"
    | (resolve) "no_step backtrack W" and "resolve W X"
    using bj cdcl_bj.cases by meson
  then show ?case
    proof cases
      case (BT X')
      then consider
          (bt) "backtrack W X"
        | (sk) "skip W X"
        using bj if_can_apply_backtrack_no_more_resolve[of W W X' X] inv_W cdcl_bj.cases by fast
      then show ?thesis
        proof cases
          case bt
          then show ?thesis using IH by auto
        next
          case sk
          then show ?thesis using IH by (meson rtranclp_trans r_into_rtranclp)
        qed
    next
      case skip
      thus ?thesis using IH  by (meson rtranclp.rtrancl_into_rtrancl)
    next
      case resolve note no_bt = this(1) and res = this(2)
      consider
          (RS) T U where
            "(\<lambda>S T. skip_or_resolve S T \<and> no_step backtrack S)\<^sup>*\<^sup>* S T" and
            "resolve T U" and
            "no_step backtrack T" and
            "skip\<^sup>*\<^sup>* U W"
        | (S)  "skip\<^sup>*\<^sup>* S W"
        using IH by auto
      thus ?thesis
        proof cases
          case (RS T U)
          have "cdcl\<^sup>*\<^sup>* S T"
            using  RS(1) cdcl_bj.resolve cdcl_o.bj  other skip
            mono_rtranclp[of " (\<lambda>S T. skip_or_resolve S T \<and> no_step backtrack S)" cdcl S T]
            by meson
          hence "cdcl_all_struct_inv U"
            by (meson RS(2) cdcl_all_struct_inv_inv cdcl_bj.resolve cdcl_o.bj other
              rtranclp_cdcl_all_struct_inv_inv step.prems)
          { fix U'
            assume "skip\<^sup>*\<^sup>* U U'" and "skip\<^sup>*\<^sup>* U' W"
            have "cdcl_all_struct_inv U'"
              using \<open>cdcl_all_struct_inv U\<close> \<open>skip\<^sup>*\<^sup>* U U'\<close> rtranclp_cdcl_all_struct_inv_inv
                 cdcl_o.bj rtranclp_mono[of skip cdcl] other skip by blast
            hence "no_step backtrack U'"
              using if_can_apply_backtrack_no_more_resolve[OF \<open>skip\<^sup>*\<^sup>* U' W\<close> ] res by blast
          }
          with \<open>skip\<^sup>*\<^sup>* U W\<close>
          have "(\<lambda>S T. skip_or_resolve S T \<and> no_step backtrack S)\<^sup>*\<^sup>* U W"
             proof induction
               case base
               thus ?case by simp
             next
               case (step V W) note st = this(1) and skip = this(2) and IH = this(3) and H = this(4)
               have "\<And>U'. skip\<^sup>*\<^sup>* U' V \<Longrightarrow> skip\<^sup>*\<^sup>* U' W"
                 using skip by auto
               hence "(\<lambda>S T. skip_or_resolve S T \<and> no_step backtrack S)\<^sup>*\<^sup>* U V"
                 using IH H by blast
               moreover have "(\<lambda>S T. skip_or_resolve S T \<and> no_step backtrack S)\<^sup>*\<^sup>* V W"
                 (* adding the \<^sup>*\<^sup>* here makes the ?case easier to find *)
                 by (simp add: local.skip r_into_rtranclp st step.prems)
               ultimately show ?case by simp
             qed
          thus ?thesis
            proof -
              have f1: "\<forall>p pa pb pc. \<not> p (pa) pb \<or> \<not> p\<^sup>*\<^sup>* pb pc \<or> p\<^sup>*\<^sup>* pa pc"
                by (meson converse_rtranclp_into_rtranclp)
              have "skip_or_resolve T U \<and> no_step backtrack T"
                using RS(2) RS(3) by force
              hence "(\<lambda>p pa. skip_or_resolve p pa \<and> no_step backtrack p)\<^sup>*\<^sup>* T W"
                proof -
                  have "(\<exists>vr19 vr16 vr17 vr18. vr19 (vr16::'st) vr17 \<and> vr19\<^sup>*\<^sup>* vr17 vr18
                       \<and> \<not> vr19\<^sup>*\<^sup>* vr16 vr18)
                    \<or> \<not> (skip_or_resolve T U \<and> no_step backtrack T)
                    \<or> \<not> (\<lambda>uu uua. skip_or_resolve uu uua \<and> no_step backtrack uu)\<^sup>*\<^sup>* U W
                    \<or> (\<lambda>uu uua. skip_or_resolve uu uua \<and> no_step backtrack uu)\<^sup>*\<^sup>* T W"
                    by force
                  then show ?thesis
                    by (metis (no_types) \<open>(\<lambda>S T. skip_or_resolve S T \<and> no_step backtrack S)\<^sup>*\<^sup>* U W\<close>
                      \<open>skip_or_resolve T U \<and> no_step backtrack T\<close> f1)
                qed
              hence "(\<lambda>p pa. skip_or_resolve p pa \<and> no_step backtrack p)\<^sup>*\<^sup>* S W"
                using RS(1) by force
              thus ?thesis
                using no_bt res by blast
            qed
        next
          case S
          { fix U'
            assume "skip\<^sup>*\<^sup>* S U'" and "skip\<^sup>*\<^sup>* U' W"
            hence "cdcl\<^sup>*\<^sup>* S U'"
              using mono_rtranclp[of skip cdcl S U'] by (simp add: cdcl_o.bj other skip)
            hence "cdcl_all_struct_inv U'"
              by (metis (no_types, hide_lams) \<open>cdcl_all_struct_inv S\<close> rtranclp_cdcl_all_struct_inv_inv)
            hence "no_step backtrack U'"
              using if_can_apply_backtrack_no_more_resolve[OF \<open>skip\<^sup>*\<^sup>* U' W\<close> ] res by blast
          }
          with S
          have "(\<lambda>S T. skip_or_resolve S T \<and> no_step backtrack S)\<^sup>*\<^sup>* S W"
             proof induction
               case base
               thus ?case by simp
             next
               case (step V W) note st = this(1) and skip = this(2) and IH = this(3) and H = this(4)
               have "\<And>U'. skip\<^sup>*\<^sup>* U' V \<Longrightarrow> skip\<^sup>*\<^sup>* U' W"
                 using skip by auto
               hence "(\<lambda>S T. skip_or_resolve S T \<and> no_step backtrack S)\<^sup>*\<^sup>* S V"
                 using IH H by blast
               moreover have "(\<lambda>S T. skip_or_resolve S T \<and> no_step backtrack S)\<^sup>*\<^sup>* V W"
                 (* adding the \<^sup>*\<^sup>* here makes the ?case easier to find *)
                 by (simp add: local.skip r_into_rtranclp st step.prems)
               ultimately show ?case by simp
             qed
          thus ?thesis using res no_bt by blast
        qed
    qed
qed

paragraph \<open>Backjumping is confluent\<close>
(* TODO Move *)
lemma cdcl_bj_state_eq_compatible:
  assumes
    "cdcl_bj S T" and
    "S \<sim> S'" and
    "T \<sim> T'"
  shows "cdcl_bj S' T'"
  using assms by (auto simp: cdcl_bj.simps
    intro: skip_state_eq_compatible backtrack_state_eq_compatible resolve_state_eq_compatible)

lemma tranclp_cdcl_bj_state_eq_compatible:
  assumes
    "cdcl_bj\<^sup>+\<^sup>+ S T" and
    "S \<sim> S'" and
    "T \<sim> T'"
  shows "cdcl_bj\<^sup>+\<^sup>+ S' T'"
  using assms apply (induction arbitrary: S' T')
    using cdcl_bj_state_eq_compatible apply blast
  by (metis (full_types) rtranclp_unfold cdcl_bj_state_eq_compatible state_eq_ref
    tranclp_unfold_end)

text \<open>The case distinction is needed, since @{term "T \<sim> V"} does not imply that @{term "R\<^sup>*\<^sup>* T V"}.\<close>
lemma cdcl_bj_strongly_confluent:
   assumes
     "cdcl_bj\<^sup>*\<^sup>* S V" and
     "cdcl_bj\<^sup>*\<^sup>* S T" and
     n_s: "no_step cdcl_bj V" and
     inv: "cdcl_all_struct_inv S"
   shows "T \<sim> V \<or> cdcl_bj\<^sup>*\<^sup>* T V"
   using assms(2)
proof induction
  case base
  thus ?case by (simp add: assms(1))
next
  case (step T U) note st = this(1) and s_o_r = this(2) and IH = this(3)
  consider
       (TV) "T \<sim> V"
     | (bj_TV) "cdcl_bj\<^sup>*\<^sup>* T V"
    using IH by blast
  then show ?case
    proof cases
      case TV
      then show ?thesis
        by (meson backtrack_state_eq_compatible cdcl_bj.simps n_s resolve_state_eq_compatible
          s_o_r skip_state_eq_compatible state_eq_ref)
    next
      case bj_TV
      then obtain U' where
        T_U': "cdcl_bj T U'" and
        "cdcl_bj\<^sup>*\<^sup>* U' V"
        using IH n_s s_o_r by (metis rtranclp_unfold tranclpD)
      have "cdcl\<^sup>*\<^sup>* S T"
        by (metis (no_types, hide_lams) bj mono_rtranclp[of cdcl_bj cdcl] other st)
      hence inv_T: "cdcl_all_struct_inv T"
        by (metis (no_types, hide_lams) inv rtranclp_cdcl_all_struct_inv_inv)

      show ?thesis
        using s_o_r
        proof cases
          case backtrack
          then obtain V0 where "skip\<^sup>*\<^sup>* T V0" and "backtrack V0 V"
            using IH if_can_apply_backtrack_skip_or_resolve_is_skip[OF backtrack _ inv_T]
             cdcl_bj_decomp_resolve_skip_and_bj
            by (meson backtrack_state_eq_compatible backtrack_unique cdcl_bj.backtrack inv_T n_s
              rtranclp_skip_backtrack_backtrack_end)
          then have "cdcl_bj\<^sup>*\<^sup>* T V0" and "cdcl_bj V0 V"
            using rtranclp_mono[of skip cdcl_bj] by blast+
          then show ?thesis
            using \<open>backtrack V0 V\<close> \<open>skip\<^sup>*\<^sup>* T V0\<close> backtrack_unique inv_T local.backtrack
            rtranclp_skip_backtrack_backtrack by auto
        next
          case resolve
          then have "U \<sim> U'"
            by (meson T_U' cdcl_bj.simps if_can_apply_backtrack_no_more_resolve inv_T
              resolve_skip_deterministic resolve_unique rtranclp.rtrancl_refl)
          then show ?thesis
            using \<open>cdcl_bj\<^sup>*\<^sup>* U' V\<close> unfolding rtranclp_unfold by (meson rtranclp_unfold state_eq_ref
              state_eq_sym tranclp_cdcl_bj_state_eq_compatible)
        next
          case skip
          consider
              (sk)  "skip T U'"
            | (bt)  "backtrack T U'"
            using T_U' by (meson cdcl_bj.cases local.skip resolve_skip_deterministic)
          thus ?thesis
            proof cases
              case sk
              thus ?thesis
                 using \<open>cdcl_bj\<^sup>*\<^sup>* U' V\<close> unfolding rtranclp_unfold by (meson skip rtranclp_unfold
                   skip_unique state_eq_ref tranclp_cdcl_bj_state_eq_compatible)
            next
              case bt
              have "skip\<^sup>+\<^sup>+ T U"
                using local.skip by blast
              thus ?thesis
                using bt by (metis \<open>cdcl_bj\<^sup>*\<^sup>* U' V\<close> backtrack inv_T tranclp_unfold_begin
                  rtranclp_skip_backtrack_backtrack_end tranclp_into_rtranclp)
            qed
        qed
    qed
qed


lemma cdcl_bj_unique_normal_form:
  assumes
    ST: "cdcl_bj\<^sup>*\<^sup>* S T" and SU: "cdcl_bj\<^sup>*\<^sup>* S U" and
    n_s_U: "no_step cdcl_bj U" and
    n_s_T: "no_step cdcl_bj T" and
    inv: "cdcl_all_struct_inv S"
  shows "T \<sim> U"
proof -
  have "T \<sim> U \<or> cdcl_bj\<^sup>*\<^sup>* T U"
    using ST SU cdcl_bj_strongly_confluent inv n_s_U by blast
  then show ?thesis
    by (metis (no_types) n_s_T rtranclp_unfold state_eq_ref tranclp_unfold_begin)
qed

lemma full_cdcl_bj_unique_normal_form:
 assumes "full cdcl_bj S T" and "full cdcl_bj S U" and
   inv: "cdcl_all_struct_inv S"
 shows "T \<sim> U"
   using cdcl_bj_unique_normal_form assms unfolding full_def by blast

subsection \<open>CDCL FW\<close>
inductive cdcl_fw_restart :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
fw_r_propagate: "propagate S S' \<Longrightarrow> cdcl_fw_restart S S'" |
fw_r_conflict: "conflict S T \<Longrightarrow> full cdcl_bj T U \<Longrightarrow> cdcl_fw_restart S U" |
fw_r_decide: "decide S S' \<Longrightarrow> cdcl_fw_restart S S'"|
fw_r_rf: "cdcl_rf S S' \<Longrightarrow> cdcl_fw_restart S S'"

lemma cdcl_fw_restart_cdcl:
  assumes "cdcl_fw_restart S T"
  shows "cdcl\<^sup>*\<^sup>* S T"
  using assms
proof induction
  case (fw_r_conflict S T U) note confl = this(1) and bj = this(2)
  have "cdcl S T" using confl by (simp add: cdcl.intros r_into_rtranclp)
  moreover
    have "cdcl_bj\<^sup>*\<^sup>* T U" using bj unfolding full_def by auto
    hence "cdcl\<^sup>*\<^sup>* T U" by (metis cdcl_o.bj mono_rtranclp other)
  ultimately show ?case by auto
qed (simp_all add: cdcl_o.intros cdcl.intros r_into_rtranclp)

lemma cdcl_fw_restart_conflicting_true_or_no_step:
  assumes "cdcl_fw_restart S T"
  shows "conflicting T = C_True \<or> no_step cdcl T"
  using assms
proof induction
  case (fw_r_conflict S T U) note confl = this(1) and n_s = this(2)
  { fix D V
    assume "cdcl U V" and "conflicting U = C_Clause D"
    then have False
      using n_s unfolding full_def
      by (induction rule: cdcl_all_rules_induct) (auto dest!: cdcl_bj.intros )
  }
  thus ?case by (cases "conflicting U") fastforce+
qed (auto simp add: cdcl_rf.simps)

inductive cdcl_fw :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
fw_propagate: "propagate S S' \<Longrightarrow> cdcl_fw S S'" |
fw_conflict: "conflict S T \<Longrightarrow> full cdcl_bj T U \<Longrightarrow> cdcl_fw S U" |
fw_decide: "decide S S' \<Longrightarrow> cdcl_fw S S'"|
fw_forget: "forget S S' \<Longrightarrow> cdcl_fw S S'"

lemma cdcl_fw_cdcl_fw_restart:
  "cdcl_fw S T \<Longrightarrow> cdcl_fw_restart S T"
  by (meson cdcl_fw.cases cdcl_fw_restart.simps forget)

lemma rtranclp_cdcl_fw_tranclp_cdcl_fw_restart:
  "cdcl_fw\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl_fw_restart\<^sup>*\<^sup>* S T"
  using rtranclp_mono[of cdcl_fw cdcl_fw_restart] cdcl_fw_cdcl_fw_restart by blast

lemma cdcl_fw_rtranclp_cdcl:
  "cdcl_fw S T \<Longrightarrow> cdcl\<^sup>*\<^sup>* S T"
  using cdcl_fw_cdcl_fw_restart cdcl_fw_restart_cdcl by blast

lemma rtranclp_cdcl_fw_rtranclp_cdcl:
  "cdcl_fw\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl\<^sup>*\<^sup>* S T"
  using rtranclp_mono[of cdcl_fw "cdcl\<^sup>*\<^sup>*"] cdcl_fw_rtranclp_cdcl by auto

(* TODO Move to top *)
lemmas trail_reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_add_cls\<^sub>N\<^sub>O\<^sub>T_unfolded[simp] =
  trail_reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_add_cls\<^sub>N\<^sub>O\<^sub>T[unfolded o_def]

lemma trail\<^sub>W_eq_reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_eq:
  "trail S = trail T \<Longrightarrow> trail (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S) = trail (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F T)"
proof (induction F S arbitrary: T rule: reduce_trail_to\<^sub>N\<^sub>O\<^sub>T.induct)
  case (1 F S T) note IH = this(1) and tr = this(2)
  then have "[] = convert_trail_from_W (trail S)
    \<or> length F = length (convert_trail_from_W (trail S))
    \<or> trail (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F (tl_trail S)) = trail (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F (tl_trail T))"
    using IH by (metis (no_types) comp_apply trail_tl_trail)
  then show "trail (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S) = trail (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F T)"
    using tr by (metis (no_types) comp_apply reduce_trail_to\<^sub>N\<^sub>O\<^sub>T.elims)
qed

lemma trail_reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_add_learned_cls[simp]:
"trail (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T M (add_learned_cls D S)) = trail (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T M S)"
 by (rule trail\<^sub>W_eq_reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_eq) simp

lemma reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_reduce_trail_convert:
  "reduce_trail_to\<^sub>N\<^sub>O\<^sub>T C S = reduce_trail_to (convert_trail_from_NOT C) S"
  apply (induction C S rule: reduce_trail_to\<^sub>N\<^sub>O\<^sub>T.induct)
  apply (subst reduce_trail_to\<^sub>N\<^sub>O\<^sub>T.simps, subst reduce_trail_to.simps)
  by (auto simp: comp_def)

lemma reduce_trail_to_length:
  "length M = length M' \<Longrightarrow> reduce_trail_to M S = reduce_trail_to M' S"
  apply (induction M S arbitrary:  rule: reduce_trail_to.induct)
  apply (case_tac "trail S \<noteq> [] "; case_tac "length (trail S) \<noteq> length M'"; simp)
  by (simp_all add: reduce_trail_to_length_ne)

lemma cdcl_fw_is_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn:
  assumes
    inv: "cdcl_all_struct_inv S" and
    cdcl:"cdcl_fw S T"
  shows "cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn S T
    \<or> (no_step cdcl_fw T \<and> conflicting T \<noteq> C_True)"
  using cdcl inv
proof induction
  case (fw_propagate S T) note propa = this(1)
  then obtain M N U k L C where
    H: "state S = (M, N, U, k, C_True)"
    "C + {#L#} \<in># clauses S"
    "M \<Turnstile>as CNot C"
    "undefined_lit L (trail S)"
    "T \<sim> cons_trail (Propagated L (C + {#L#})) S"
    using propa by auto
  have "propagate\<^sub>N\<^sub>O\<^sub>T S T"
    apply (rule propagate\<^sub>N\<^sub>O\<^sub>T.propagate\<^sub>N\<^sub>O\<^sub>T[of _ C L])
    using H by (auto simp: state_eq\<^sub>N\<^sub>O\<^sub>T_def state_eq_def clauses_def
      simp del: state_simp\<^sub>N\<^sub>O\<^sub>T state_simp)
  then show ?case
    using cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn.intros(2) by blast
next
  case (fw_decide S T) note dec = this(1) and inv = this(2)
  then obtain L where
    undef_L: "undefined_lit L (trail S)" and
    atm_L: "atm_of L \<in> atms_of_mu (init_clss S)" and
    T: "T \<sim> cons_trail (Marked L (Suc (backtrack_lvl S)))
      (update_backtrack_lvl (Suc (backtrack_lvl S)) S)"
    by auto
  have "decide\<^sub>N\<^sub>O\<^sub>T S T"
    apply (rule decide\<^sub>N\<^sub>O\<^sub>T.decide\<^sub>N\<^sub>O\<^sub>T)
       using undef_L apply simp
     using atm_L inv unfolding cdcl_all_struct_inv_def no_strange_atm_def clauses_def apply auto[]
    using T unfolding state_eq_def state_eq\<^sub>N\<^sub>O\<^sub>T_def by (auto simp: clauses_def)
  then show ?case using cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_decide\<^sub>N\<^sub>O\<^sub>T by blast
next
  case (fw_forget S T) note rf =this(1) and inv = this(2)
  then obtain M N C U k where
     S: "state S = (M, N, {#C#} + U, k, C_True)" and
     "\<not> M \<Turnstile>asm clauses S" and
     "C \<notin> set (get_all_mark_of_propagated (trail S))" and
     C_init: "C \<notin># init_clss S" and
     C_le: "C \<in># learned_clss S" and
     T: "T \<sim> remove_cls C S"
    by auto
  have "init_clss S \<Turnstile>pm C"
    using inv C_le unfolding cdcl_all_struct_inv_def cdcl_learned_clause_def
    by (meson mem_set_mset_iff true_clss_clss_in_imp_true_clss_cls)
  then have S_C: "clauses S - replicate_mset (count (clauses S) C) C \<Turnstile>pm C"
    using C_init C_le unfolding clauses_def by (simp add: Un_Diff)
  moreover have H: "init_clss S + (learned_clss S - replicate_mset (count (learned_clss S) C) C)
    = init_clss S + learned_clss S - replicate_mset (count (learned_clss S) C) C"
    using C_le C_init by (metis clauses_def clauses_remove_cls diff_zero gr0I
      init_clss_remove_cls learned_clss_remove_cls plus_multiset.rep_eq replicate_mset_0
      semiring_normalization_rules(5))
  have "forget\<^sub>N\<^sub>O\<^sub>T S T"
    apply (rule forget\<^sub>N\<^sub>O\<^sub>T.forget\<^sub>N\<^sub>O\<^sub>T)
       using S_C apply blast
      using S apply simp
     using \<open>C \<in># learned_clss S\<close> apply (simp add: clauses_def)
    using T C_le C_init by (auto
      simp: state_eq_def Un_Diff state_eq\<^sub>N\<^sub>O\<^sub>T_def clauses_def ac_simps H
      simp del: state_simp state_simp\<^sub>N\<^sub>O\<^sub>T)
  then show ?case using cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_forget\<^sub>N\<^sub>O\<^sub>T by blast
next
  case (fw_conflict S T U) note confl = this(1) and bj = this(2) and inv = this(3)
  obtain C\<^sub>S where
    confl_T: "conflicting T = C_Clause C\<^sub>S" and
    C\<^sub>S: "C\<^sub>S \<in># clauses S" and
    tr_S_C\<^sub>S: "trail S \<Turnstile>as CNot C\<^sub>S"
    using confl by auto
  consider
      (no_bt) "skip_or_resolve\<^sup>*\<^sup>* T U"
    | (bt) T' where "skip_or_resolve\<^sup>*\<^sup>* T T'" and "backtrack T' U"
    using bj rtranclp_cdcl_bj_skip_or_resolve_backtrack unfolding full_def by meson
  then show ?case
    proof cases
      case no_bt
      then have "conflicting U \<noteq> C_True"
        using confl by (induction rule: rtranclp_induct) auto
      moreover then have "no_step cdcl_fw U"
        by (auto simp: cdcl_fw.simps)
      ultimately show ?thesis by blast
    next
      case bt note s_or_r = this(1) and bt = this(2)
      obtain M1 M2 i D L K where
        confl_T': "conflicting T' = C_Clause (D + {#L#})" and
        M1_M2:"(Marked K (i+1) # M1, M2) \<in> set (get_all_marked_decomposition (trail T'))" and
        "get_level L (trail T') = backtrack_lvl T'" and
        "get_level L (trail T') = get_maximum_level (D+{#L#}) (trail T')" and
        "get_maximum_level D (trail T') = i" and
        U: "U \<sim> cons_trail (Propagated L (D+{#L#}))
                 (reduce_trail_to M1
                      (add_learned_cls (D + {#L#})
                         (update_backtrack_lvl i
                            (update_conflicting C_True T'))))"
        using bt by auto
      have [simp]: "clauses S = clauses T"
        using confl by auto
      have [simp]: "clauses T = clauses T'"
        using s_or_r
        proof (induction)
          case base
          then show ?case by simp
        next
          case (step U V) note st = this(1) and s_o_r = this(2) and IH = this(3)
          have "clauses U = clauses V"
            using s_o_r by auto
          then show ?case using IH by auto
        qed
      have inv_T: "cdcl_all_struct_inv T"
        by (meson cdcl_cp.simps confl inv r_into_rtranclp rtranclp_cdcl_all_struct_inv_inv
          rtranclp_cdcl_cp_rtranclp_cdcl)
      have "cdcl\<^sup>*\<^sup>* T T'"
        using rtranclp_skip_or_resolve_rtranclp_cdcl s_or_r by blast
      have inv_T': "cdcl_all_struct_inv T'"
        using \<open>cdcl\<^sup>*\<^sup>* T T'\<close> inv_T rtranclp_cdcl_all_struct_inv_inv by blast
      have inv_U: "cdcl_all_struct_inv U"
        using cdcl_fw_restart_cdcl confl fw_r_conflict inv local.bj rtranclp_cdcl_all_struct_inv_inv
        by blast
      then have undef_L: "undefined_lit L (tl (trail U))"
        using U unfolding cdcl_all_struct_inv_def cdcl_M_level_inv_def by (auto simp: defined_lit_map)
      have [simp]: "init_clss S = init_clss T'"
        using \<open>cdcl\<^sup>*\<^sup>* T T'\<close> cdcl_init_clss confl by (auto dest!: cdcl_init_clss cdcl.conflict
          rtranclp_cdcl_init_clss)
      then have atm_L: "atm_of L \<in> atms_of_mu (clauses S)"
        using inv_T' confl_T' unfolding cdcl_all_struct_inv_def no_strange_atm_def clauses_def by auto
      obtain M where tr_T: "trail T = M @ trail T'"
        using s_or_r by (induction rule: rtranclp_induct) auto
      obtain M' where
        tr_T': "trail T' = M' @  Marked K (i+1) # tl (trail U)" and
        tr_U: "trail U = Propagated L (D + {#L#}) # tl (trail U)"
        using U M1_M2 by auto
      def M'' \<equiv> "M @ M'"
        have tr_T: "trail S = M'' @  Marked K (i+1) # tl (trail U)"
        using tr_T tr_T' confl unfolding M''_def by auto
      have "init_clss T' + learned_clss S \<Turnstile>pm D + {#L#}"
        using inv_T' confl_T' unfolding cdcl_all_struct_inv_def cdcl_learned_clause_def clauses_def
        by simp
      have "reduce_trail_to (convert_trail_from_NOT (convert_trail_from_W M1)) S =
        reduce_trail_to M1 S"
        by (rule reduce_trail_to_length) simp
      moreover have "trail (reduce_trail_to M1 S) = M1"
        apply (rule reduce_trail_to_skip_beginning[of _ "M @ _ @ M2 @ [Marked K (Suc i)]"])
        using confl M1_M2 \<open>trail T = M @ trail T'\<close>
          apply (auto dest!: get_all_marked_decomposition_exists_prepend
            elim!: conflictE)
          by (rule sym) auto
      ultimately have [simp]: "trail (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T (convert_trail_from_W M1) S) = M1"
        using M1_M2 confl by (auto simp add: reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_reduce_trail_convert)
      have "every_mark_is_a_conflict U"
        using inv_U unfolding cdcl_all_struct_inv_def cdcl_conflicting_def by simp
      then have "tl (trail U) \<Turnstile>as CNot D"
        by (metis add_diff_cancel_left' append_self_conv2 tr_U union_commute)
      have "backjump_l S U"
        apply (rule backjump_l)
                using tr_T apply simp
               using inv unfolding cdcl_all_struct_inv_def cdcl_M_level_inv_def apply simp
               using U M1_M2 confl apply (auto elim!:  simp: state_eq\<^sub>N\<^sub>O\<^sub>T_def
               simp del: state_simp\<^sub>N\<^sub>O\<^sub>T)[]
              using C\<^sub>S apply simp
             using tr_S_C\<^sub>S apply simp
            using defined_lit_convert_trail_from_W undef_L apply fastforce
            using undef_L apply simp
           using atm_L apply simp
          using \<open>init_clss T' + learned_clss S \<Turnstile>pm D + {#L#}\<close> unfolding clauses_def apply simp
         using \<open>tl (trail U) \<Turnstile>as CNot D\<close> inv_T' unfolding cdcl_all_struct_inv_def distinct_cdcl_state_def
         apply simp
        using \<open>tl (trail U) \<Turnstile>as CNot D\<close> inv_T' inv_U U confl_T' unfolding cdcl_all_struct_inv_def distinct_cdcl_state_def
        apply simp_all
        done
      then show ?thesis using cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_backjump_l by fast
    qed
qed

abbreviation cdcl\<^sub>N\<^sub>O\<^sub>T_restart where
"cdcl\<^sub>N\<^sub>O\<^sub>T_restart \<equiv> restart_ops.cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart cdcl\<^sub>N\<^sub>O\<^sub>T restart"

lemma cdcl_fw_restart_is_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_restart_no_step:
  assumes
    inv: "cdcl_all_struct_inv S" and
    cdcl:"cdcl_fw_restart S T"
  shows "cdcl\<^sub>N\<^sub>O\<^sub>T_restart\<^sup>*\<^sup>* S T \<or> (no_step cdcl_fw T \<and> conflicting T \<noteq> C_True)"
proof -
  consider
      (fw) "cdcl_fw S T"
    | (fw_r) "restart S T"
    using cdcl by (meson cdcl_fw_restart.simps cdcl_rf.cases fw_conflict fw_decide fw_forget
      fw_propagate)
  then show ?thesis
    proof cases
      case fw
      then have "cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn S T \<or> (no_step cdcl_fw T \<and> conflicting T \<noteq> C_True)"
        using inv cdcl_fw_is_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn by blast
      moreover have "inv\<^sub>N\<^sub>O\<^sub>T S"
        using inv unfolding cdcl_all_struct_inv_def cdcl_M_level_inv_def by auto
      ultimately show ?thesis
        using cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_is_tranclp_cdcl\<^sub>N\<^sub>O\<^sub>T rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_is_rtranclp_cdcl\<^sub>N\<^sub>O\<^sub>T_and_inv
        rtranclp_mono[of cdcl\<^sub>N\<^sub>O\<^sub>T cdcl\<^sub>N\<^sub>O\<^sub>T_restart]
        by (blast intro: restart_ops.cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart.intros)
    next
      case fw_r
      then show ?thesis by (blast intro: restart_ops.cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart.intros)
    qed
qed

abbreviation \<mu>\<^sub>F\<^sub>W :: "'st \<Rightarrow> nat" where
"\<mu>\<^sub>F\<^sub>W S \<equiv> (if no_step cdcl_fw S then 0 else 1+\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_merged (set_mset (init_clss S)) S)"

lemma cdcl_fw_\<mu>\<^sub>F\<^sub>W_decreasing:
  assumes
    inv: "cdcl_all_struct_inv S" and
    fw: "cdcl_fw S T"
  shows "\<mu>\<^sub>F\<^sub>W T < \<mu>\<^sub>F\<^sub>W S"
proof -
  let ?A = "init_clss S"
  have atm_clauses: "atms_of_mu (clauses S) \<subseteq> atms_of_mu ?A"
    using inv unfolding cdcl_all_struct_inv_def no_strange_atm_def clauses_def by auto
  have atm_trail: "atm_of ` lits_of (trail S) \<subseteq> atms_of_mu ?A"
    using inv unfolding cdcl_all_struct_inv_def no_strange_atm_def clauses_def by auto
  have n_d: "no_dup (trail S)"
    using inv unfolding cdcl_all_struct_inv_def by auto
  have [simp]: "\<not> no_step cdcl_fw S"
    using fw by auto
  have [simp]: "init_clss S = init_clss T"
    by (meson cdcl_fw.simps cdcl_fw_restart.simps cdcl_fw_restart_cdcl cdcl_rf.simps fw
      rtranclp_cdcl_init_clss)
  consider
      (merged) "cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn S T"
    | (n_s) "no_step cdcl_fw T"
    using cdcl_fw_is_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn inv fw by blast
  then show ?thesis
    proof cases
      case merged
      then show ?thesis
        using cdcl\<^sub>N\<^sub>O\<^sub>T_decreasing_measure'[OF _ _ atm_clauses] atm_trail n_d
        by (auto split: split_if)
    next
      case n_s
      then show ?thesis by simp
    qed
qed

lemma wf_cdcl_fw: "wf {(T, S). cdcl_all_struct_inv S \<and> cdcl_fw S T}"
  apply (rule wfP_if_measure[of _ _ "\<mu>\<^sub>F\<^sub>W"])
  using cdcl_fw_\<mu>\<^sub>F\<^sub>W_decreasing by blast

lemma cdcl_all_struct_inv_tranclp_cdcl_fw_tranclp_cdcl_fw_cdcl_all_struct_inv:
  assumes
    inv: "cdcl_all_struct_inv b"
    "cdcl_fw\<^sup>+\<^sup>+ b a"
  shows "(\<lambda>S T. cdcl_all_struct_inv S \<and> cdcl_fw S T)\<^sup>+\<^sup>+ b a"
  using assms(2)
proof induction
  case base
  then show ?case using inv by auto
next
  case (step c d) note st =this(1) and fw = this(2) and IH = this(3)
  have "cdcl_all_struct_inv c"
    using tranclp_into_rtranclp[OF st] cdcl_fw_rtranclp_cdcl
    assms(1) rtranclp_cdcl_all_struct_inv_inv rtranclp_mono[of cdcl_fw "cdcl\<^sup>*\<^sup>*"] by fastforce
  then have "(\<lambda>S T. cdcl_all_struct_inv S \<and> cdcl_fw S T)\<^sup>+\<^sup>+ c d"
    using fw by auto
  then show ?case using IH by auto
qed

lemma wf_tranclp_cdcl_fw: "wf {(T, S). cdcl_all_struct_inv S \<and> cdcl_fw\<^sup>+\<^sup>+ S T}"
  using wf_trancl[OF wf_cdcl_fw]
  apply (rule wf_subset)
  by (auto simp: trancl_set_tranclp
    cdcl_all_struct_inv_tranclp_cdcl_fw_tranclp_cdcl_fw_cdcl_all_struct_inv)

lemma backtrack_is_full1_cdcl_bj:
  assumes bt: "backtrack S T"
  shows "full1 cdcl_bj S T"
proof -
  have "no_step cdcl_bj T"
    using bt by (fastforce simp: cdcl_bj.simps)
  moreover have "cdcl_bj\<^sup>+\<^sup>+ S T"
    using bt by auto
  ultimately show ?thesis unfolding full1_def by blast
qed

lemma rtrancl_cdcl_conflicting_true_cdcl_fw_restart:
  assumes "cdcl\<^sup>*\<^sup>* S V" and "conflicting S = C_True"
  shows "(cdcl_fw_restart\<^sup>*\<^sup>* S V \<and> conflicting V = C_True)
    \<or> (\<exists>T U. cdcl_fw_restart\<^sup>*\<^sup>* S T \<and> conflicting V \<noteq> C_True \<and> conflict T U \<and> cdcl_bj\<^sup>*\<^sup>* U V)"
  using assms
proof induction
  case base
  thus ?case by simp
next
  case (step U V) note st = this(1) and cdcl = this(2) and IH = this(3) and confl[simp] = this(4)
  from cdcl
  show ?case
    proof (cases)
      case propagate
      moreover hence "conflicting U = C_True"
        by auto
      moreover have "conflicting V = C_True"
        using propagate by auto
      ultimately show ?thesis using IH cdcl_fw_restart.fw_r_propagate[of U V] by auto
    next
      case conflict
      moreover hence "conflicting U = C_True"
        by auto
      moreover have "conflicting V \<noteq> C_True"
        using conflict by auto
      ultimately show ?thesis using IH by auto
    next
      case other
      thus ?thesis
        proof cases
          case decide
          moreover hence "conflicting U = C_True"
            by auto
          ultimately show ?thesis using IH cdcl_fw_restart.fw_r_decide[of U V] by auto
        next
          case bj
          moreover {
            assume "skip_or_resolve U V"
            have f1: "cdcl_bj\<^sup>+\<^sup>+ U V"
              by (simp add: local.bj tranclp.r_into_trancl)
            obtain T T' :: 'st where
              f2: "cdcl_fw_restart\<^sup>*\<^sup>* S U
                \<or> cdcl_fw_restart\<^sup>*\<^sup>* S T \<and> conflicting U \<noteq> C_True \<and> conflict T T' \<and> cdcl_bj\<^sup>*\<^sup>* T' U"
              using IH confl by blast
            then have ?thesis
              proof -
                have "conflicting V \<noteq> C_True \<and> conflicting U \<noteq> C_True"
                  using \<open>skip_or_resolve U V\<close> by auto
                then show ?thesis
                  by (metis (no_types) IH confl f1 rtranclp_trans tranclp_into_rtranclp)
              qed
          }
          moreover {
            assume "backtrack U V"
            hence "conflicting U \<noteq> C_True" by auto
            then obtain T T' where
              "cdcl_fw_restart\<^sup>*\<^sup>* S T" and
              "conflicting U \<noteq> C_True" and
              "conflict T T'" and
              "cdcl_bj\<^sup>*\<^sup>* T' U"
              using IH confl by blast
            have "conflicting V = C_True"
              using \<open>backtrack U V\<close> by auto
            have "full cdcl_bj T' V"
              apply (rule rtranclp_fullI[of cdcl_bj T' U V])
                using \<open>cdcl_bj\<^sup>*\<^sup>* T' U\<close> apply fast
              using \<open>backtrack U V\<close> backtrack_is_full1_cdcl_bj unfolding full1_def full_def by blast
            then have ?thesis
              using cdcl_fw_restart.fw_r_conflict[of T T' V] \<open>conflict T T'\<close> \<open>cdcl_fw_restart\<^sup>*\<^sup>* S T\<close>
              \<open>conflicting V = C_True\<close> by auto
          }
          ultimately show ?thesis by (auto simp: cdcl_bj.simps)
      qed
    next
      case rf
      moreover hence "conflicting U = C_True" and "conflicting V = C_True"
        by (auto simp: cdcl_rf.simps)
      ultimately show ?thesis using IH cdcl_fw_restart.fw_r_rf[of U V] by auto
    qed
qed

lemma no_step_cdcl_no_step_cdcl_fw_restart: "no_step cdcl S \<Longrightarrow> no_step cdcl_fw_restart S"
  by (auto simp: cdcl.simps cdcl_fw_restart.simps cdcl_o.simps cdcl_bj.simps)

lemma no_step_cdcl_fw_restart_no_step_cdcl:
  "conflicting S = C_True \<Longrightarrow> no_step cdcl_fw_restart S \<Longrightarrow> no_step cdcl S"
  unfolding cdcl.simps cdcl_fw_restart.simps cdcl_o.simps cdcl_bj.simps
  using wf_exists_normal_form_full[OF cdcl_bj_wf] by force

lemma rtranclp_cdcl_fw_restart_no_step_cdcl_bj:
  assumes
    "cdcl_fw_restart\<^sup>*\<^sup>* S T" and
    "conflicting S = C_True"
  shows "no_step cdcl_bj T"
  using assms
  by (induction rule: rtranclp_induct)
     (fastforce simp: cdcl_bj.simps cdcl_rf.simps cdcl_fw_restart.simps full_def)+

text \<open>If @{term "conflicting  S \<noteq> C_True"}, we cannot say anything.

  Remark that this theorem does  not say anything about well-foundedness: even if you know that one
  relation is well-founded, it only states that the normal forms are shared.
  \<close>
lemma conflicting_true_full_cdcl_iff_full_cdcl_fw:
  assumes confl: "conflicting  S = C_True"
  shows "full cdcl S V \<longleftrightarrow> full cdcl_fw_restart S V"
proof
  assume full: "full cdcl_fw_restart S V"
  hence st: "cdcl\<^sup>*\<^sup>* S V"
    using rtranclp_mono[of cdcl_fw_restart "cdcl\<^sup>*\<^sup>*"] cdcl_fw_restart_cdcl unfolding full_def by auto

  have n_s: "no_step cdcl_fw_restart V"
    using full unfolding full_def by auto
  have n_s_bj: "no_step cdcl_bj V"
    using rtranclp_cdcl_fw_restart_no_step_cdcl_bj confl full unfolding full_def by auto

  have "\<And>S'. conflict V S' \<Longrightarrow> False"
    using n_s n_s_bj wf_exists_normal_form_full[OF cdcl_bj_wf] cdcl_fw_restart.simps by meson
  hence n_s_cdcl: "no_step cdcl V"
    using n_s n_s_bj by (auto simp: cdcl.simps cdcl_o.simps cdcl_fw_restart.simps)
  then show "full cdcl S V" using st unfolding full_def by auto
next
  assume full: "full cdcl S V"
  have "no_step cdcl_fw_restart V"
    using full no_step_cdcl_no_step_cdcl_fw_restart unfolding full_def by blast
  moreover
    consider
        (fw) "cdcl_fw_restart\<^sup>*\<^sup>* S V" and "conflicting V = C_True"
      | (bj) T U where
        "cdcl_fw_restart\<^sup>*\<^sup>* S T" and
        "conflicting V \<noteq> C_True" and
        "conflict T U" and
        "cdcl_bj\<^sup>*\<^sup>* U V"
      using full rtrancl_cdcl_conflicting_true_cdcl_fw_restart confl unfolding full_def by meson
    then have "cdcl_fw_restart\<^sup>*\<^sup>* S V"
      proof cases
        case fw
        thus ?thesis by fast
      next
        case (bj T U)
        have "no_step cdcl_bj V"
          by (meson cdcl_o.bj full full_def other)
        hence "full cdcl_bj U V"
          using \<open> cdcl_bj\<^sup>*\<^sup>* U V\<close> unfolding full_def by auto
        hence "cdcl_fw_restart T V" using \<open>conflict T U\<close> cdcl_fw_restart.fw_r_conflict by blast
        thus ?thesis using \<open>cdcl_fw_restart\<^sup>*\<^sup>* S T\<close> by auto
      qed
  ultimately show "full cdcl_fw_restart S V" unfolding full_def by fast
qed

lemma init_state_true_full_cdcl_iff_full_cdcl_fw:
  shows "full cdcl (init_state N) V \<longleftrightarrow> full cdcl_fw_restart (init_state N) V"
  by (rule conflicting_true_full_cdcl_iff_full_cdcl_fw) simp

subsection \<open>FW with strategy\<close>
subsubsection \<open>The intermediate step\<close>
inductive cdcl_s' :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
conflict': "full1 cdcl_cp S S' \<Longrightarrow> cdcl_s' S S'" |
decide': "decide S S' \<Longrightarrow> no_step cdcl_cp S \<Longrightarrow> full cdcl_cp S' S'' \<Longrightarrow> cdcl_s' S S''" |
bj': "full1 cdcl_bj S S' \<Longrightarrow> no_step cdcl_cp S \<Longrightarrow> full cdcl_cp S' S'' \<Longrightarrow> cdcl_s' S S''"

inductive_cases cdcl_s'E: "cdcl_s' S T"

lemma rtranclp_cdcl_bj_full1_cdclp_cdcl_s:
  "cdcl_bj\<^sup>*\<^sup>* S S' \<Longrightarrow> full cdcl_cp S' S'' \<Longrightarrow> cdcl_s\<^sup>*\<^sup>* S S''"
proof (induction rule: converse_rtranclp_induct)
  case base
  thus ?case by (metis cdcl_s.conflict' full_unfold rtranclp.simps)
next
  case (step T U) note st =this(2) and bj = this(1) and IH = this(3)[OF this(4)]
  have "no_step cdcl_cp T"
    using bj by (auto simp add: cdcl_bj.simps)
  consider
      (U) "U = S'"
    | (U') U' where "cdcl_bj U U'" and "cdcl_bj\<^sup>*\<^sup>* U' S'"
    using st by (metis converse_rtranclpE)
  thus ?case
    proof cases
      case U
      thus ?thesis
        using \<open>no_step cdcl_cp T\<close> cdcl_o.bj local.bj other' step.prems by (meson r_into_rtranclp)
    next
      case U' note U' = this(1)
      have "no_step cdcl_cp U"
        using U' by (fastforce simp: cdcl_cp.simps cdcl_bj.simps)
      hence "full cdcl_cp U U"
        by (simp add: full_unfold)
      hence "cdcl_s T U"
        using \<open>no_step cdcl_cp T\<close> cdcl_s.simps local.bj cdcl_o.bj by meson
      thus ?thesis using IH by auto
    qed
qed

lemma cdcl_s'_is_rtranclp_cdcl_s:
  "cdcl_s' S T \<Longrightarrow> cdcl_s\<^sup>*\<^sup>* S T"
  apply (induction rule: cdcl_s'.induct)
    apply (auto intro: cdcl_s.intros)[]
   apply (meson decide other' r_into_rtranclp)
  by (metis full1_def rtranclp_cdcl_bj_full1_cdclp_cdcl_s tranclp_into_rtranclp)

lemma cdcl_cp_cdcl_bj_bissimulation:
  assumes
    "full cdcl_cp T U" and
    "cdcl_bj\<^sup>*\<^sup>* T T'" and
    "cdcl_all_struct_inv T" and
    "no_step cdcl_bj T'"
  shows "full cdcl_cp T' U
    \<or> (\<exists>U' U''. full cdcl_cp T' U'' \<and> full1 cdcl_bj U U' \<and> full cdcl_cp U' U'' \<and> cdcl_s'\<^sup>*\<^sup>* U U'')"
  using assms(2,1,3,4)
proof (induction rule: rtranclp_induct)
  case base
  thus ?case by blast
next
  case (step T' T'') note st = this(1) and bj = this(2) and IH = this(3)[OF this(4,5)] and
    full = this(4) and inv = this(5)
  have "cdcl\<^sup>*\<^sup>* T T''"
    by (metis (no_types, lifting) cdcl_o.bj local.bj mono_rtranclp[of cdcl_bj cdcl T T''] other st
      rtranclp.rtrancl_into_rtrancl)
  hence inv_T'': "cdcl_all_struct_inv T''"
    using inv rtranclp_cdcl_all_struct_inv_inv by blast
  have "cdcl_bj\<^sup>+\<^sup>+ T T''"
    using local.bj st by auto
  have "full1 cdcl_bj T T''"
    by (metis \<open>cdcl_bj\<^sup>+\<^sup>+ T T''\<close> full1_def step.prems(3))
  hence "T = U"
    proof -
      obtain Z where "cdcl_bj T Z"
          by (meson tranclpD \<open>cdcl_bj\<^sup>+\<^sup>+ T T''\<close>)
      { assume "cdcl_cp\<^sup>+\<^sup>+ T U"
        then obtain Z' where "cdcl_cp T Z'"
          by (meson tranclpD)
        hence False
          using \<open>cdcl_bj T Z\<close> by (fastforce simp: cdcl_bj.simps cdcl_cp.simps)
      }
      thus ?thesis
        using full unfolding full_def rtranclp_unfold by blast
    qed
  obtain U'' where "full cdcl_cp T'' U''"
    using cdcl_cp_normalized_element_all_inv inv_T'' by blast
  moreover hence "cdcl_s\<^sup>*\<^sup>* U U''"
    by (metis \<open>T = U\<close> \<open>cdcl_bj\<^sup>+\<^sup>+ T T''\<close> rtranclp_cdcl_bj_full1_cdclp_cdcl_s rtranclp_unfold)
  moreover have "cdcl_s'\<^sup>*\<^sup>* U U''"
    proof -
      obtain ss :: "'st \<Rightarrow> 'st" where
        f1: "\<forall>x2. (\<exists>v3. cdcl_cp x2 v3) = cdcl_cp x2 (ss x2)"
        by moura
      have "\<not> cdcl_cp U (ss U)"
        by (meson full full_def)
      then show ?thesis
        using f1 by (metis (no_types) \<open>T = U\<close> \<open>full1 cdcl_bj T T''\<close> bj' calculation(1)
          r_into_rtranclp)
    qed
  ultimately show ?case
    using \<open>full1 cdcl_bj T T''\<close> \<open>full cdcl_cp T'' U''\<close> unfolding \<open>T = U\<close> by blast
qed

lemma cdcl_cp_cdcl_bj_bissimulation':
  assumes
    "full cdcl_cp T U" and
    "cdcl_bj\<^sup>*\<^sup>* T T'" and
    "cdcl_all_struct_inv T" and
    "no_step cdcl_bj T'"
  shows "full cdcl_cp T' U
    \<or> (\<exists>U'. full1 cdcl_bj U U' \<and> (\<forall>U''. full cdcl_cp U' U'' \<longrightarrow> full cdcl_cp T' U''
      \<and> cdcl_s'\<^sup>*\<^sup>* U U''))"
  using assms(2,1,3,4)
proof (induction rule: rtranclp_induct)
  case base
  thus ?case by blast
next
  case (step T' T'') note st = this(1) and bj = this(2) and IH = this(3)[OF this(4,5)] and
    full = this(4) and inv = this(5)
  have "cdcl\<^sup>*\<^sup>* T T''"
    by (metis (no_types, lifting) cdcl_o.bj local.bj mono_rtranclp[of cdcl_bj cdcl T T''] other st
      rtranclp.rtrancl_into_rtrancl)
  hence inv_T'': "cdcl_all_struct_inv T''"
    using inv rtranclp_cdcl_all_struct_inv_inv by blast
  have "cdcl_bj\<^sup>+\<^sup>+ T T''"
    using local.bj st by auto
  have "full1 cdcl_bj T T''"
    by (metis \<open>cdcl_bj\<^sup>+\<^sup>+ T T''\<close> full1_def step.prems(3))
  hence "T = U"
    proof -
      obtain Z where "cdcl_bj T Z"
          by (meson tranclpD \<open>cdcl_bj\<^sup>+\<^sup>+ T T''\<close>)
      { assume "cdcl_cp\<^sup>+\<^sup>+ T U"
        then obtain Z' where "cdcl_cp T Z'"
          by (meson tranclpD)
        hence False
          using \<open>cdcl_bj T Z\<close> by (fastforce simp: cdcl_bj.simps cdcl_cp.simps)
      }
      thus ?thesis
        using full unfolding full_def rtranclp_unfold by blast
    qed
  { fix U''
    assume "full cdcl_cp T'' U''"
    moreover hence "cdcl_s\<^sup>*\<^sup>* U U''"
      by (metis \<open>T = U\<close> \<open>cdcl_bj\<^sup>+\<^sup>+ T T''\<close> rtranclp_cdcl_bj_full1_cdclp_cdcl_s rtranclp_unfold)
    moreover have "cdcl_s'\<^sup>*\<^sup>* U U''"
      proof -
        obtain ss :: "'st \<Rightarrow> 'st" where
          f1: "\<forall>x2. (\<exists>v3. cdcl_cp x2 v3) = cdcl_cp x2 (ss x2)"
          by moura
        have "\<not> cdcl_cp U (ss U)"
          by (meson assms(1) full_def)
        then show ?thesis
          using f1 by (metis (no_types) \<open>T = U\<close> \<open>full1 cdcl_bj T T''\<close> bj' calculation(1)
            r_into_rtranclp)
      qed
    ultimately have "full1 cdcl_bj U T''" and " cdcl_s'\<^sup>*\<^sup>* T'' U''"
      using \<open>full1 cdcl_bj T T''\<close> \<open>full cdcl_cp T'' U''\<close> unfolding \<open>T = U\<close>
        apply blast
      by (metis \<open>full cdcl_cp T'' U''\<close> cdcl_s'.simps full_unfold rtranclp.simps)
    }
  then show ?case
    using \<open>full1 cdcl_bj T T''\<close> full bj' unfolding \<open>T = U\<close> full_def by (metis r_into_rtranclp)
qed

lemma
  assumes
    "cdcl_bj S T" and
    "full cdcl_cp T U"
  shows
    "(T = U \<and> (\<exists>U'. full1 cdcl_bj S U' \<and> full cdcl_bj U U'))
    \<or> cdcl_s' S U"
    using assms
proof induction
  case (skip S T)
  obtain U' where "full cdcl_bj T U'"
    using wf_exists_normal_form_full[OF cdcl_bj_wf] by blast
  moreover hence "full1 cdcl_bj S U'"
    proof -
      have f1: "cdcl_bj\<^sup>*\<^sup>* T U' \<and> no_step cdcl_bj U'"
        by (metis (no_types) calculation full_def)
      have "cdcl_bj S T"
        by (simp add: cdcl_bj.skip skip.hyps)
      then show ?thesis
        using f1 by (simp add: full1_def rtranclp_into_tranclp2)
  qed
  moreover
    have "no_step cdcl_cp T"
      using skip(1) by (fastforce simp:cdcl_cp.simps)
    hence "T = U"
      using skip(2) unfolding full_def rtranclp_unfold by (auto dest: tranclpD)
  ultimately show ?case by blast
next
  case (resolve S T)
  obtain U' where "full cdcl_bj T U'"
    using wf_exists_normal_form_full[OF cdcl_bj_wf] by blast
  moreover hence "full1 cdcl_bj S U'"
    proof -
      have f1: "cdcl_bj\<^sup>*\<^sup>* T U' \<and> no_step cdcl_bj U'"
        by (metis (no_types) calculation full_def)
      have "cdcl_bj S T"
        by (simp add: cdcl_bj.resolve resolve.hyps)
      then show ?thesis
        using f1 by (simp add: full1_def rtranclp_into_tranclp2)
    qed
  moreover
    have "no_step cdcl_cp T"
      using resolve(1) by (fastforce simp:cdcl_cp.simps)
    hence "T = U"
      using resolve(2) unfolding full_def rtranclp_unfold by (auto dest: tranclpD)
  ultimately show ?case by blast
next
  case (backtrack S T) note bt = this(1)
  hence "no_step cdcl_bj T"
    by (fastforce simp: cdcl_bj.simps)
  moreover have "cdcl_bj\<^sup>+\<^sup>+ S T"
    using bt by (simp add: cdcl_bj.backtrack tranclp.r_into_trancl)
  ultimately have "full1 cdcl_bj S T"
    unfolding full_def full1_def by simp
  moreover have "no_step cdcl_cp S"
    using backtrack(1) by (fastforce simp: cdcl_cp.simps)
  ultimately show ?case using backtrack(2) cdcl_s'.bj' by blast
qed

lemma cdcl_s_cdcl_s'_connected:
  assumes "cdcl_s S U" and "cdcl_all_struct_inv S"
  shows "cdcl_s' S U
    \<or> (\<exists>U'. full1 cdcl_bj U U' \<and> (\<forall>U''. full cdcl_cp U' U'' \<longrightarrow> cdcl_s' S U'' ))"
  using assms
proof (induction rule: cdcl_s.induct)
  case (conflict' S T)
  hence "cdcl_s' S T"
    using cdcl_s'.conflict' by blast
  thus ?case
    by blast
next
  case (other' S T U) note o = this(1) and n_s = this(2) and full = this(3) and inv = this(4)
  show ?case
    using o
    proof cases
      case decide
      thus ?thesis using cdcl_s'.simps full n_s by blast
    next
      case bj
      have inv_T: "cdcl_all_struct_inv T"
        using cdcl_all_struct_inv_inv o other other'.prems by blast
      consider
          (cp) "full cdcl_cp T U" and "no_step cdcl_bj T"
        | (fbj) T' where "full1 cdcl_bj T T'"
        apply (cases "no_step cdcl_bj T")
         using full apply blast
        using wf_exists_normal_form_full[OF cdcl_bj_wf, of T] by (metis full_unfold)
      thus ?thesis
        proof cases
          case cp
          thus ?thesis
            proof -
              obtain ss :: "'st \<Rightarrow> 'st" where
                f1: "\<forall>s sa sb. (\<not> full1 cdcl_bj s sa \<or> cdcl_cp s (ss s) \<or> \<not> full cdcl_cp sa sb)
                  \<or> cdcl_s' s sb"
                using bj' by moura
              have "full1 cdcl_bj S T"
                by (simp add: cp(2) full1_def local.bj tranclp.r_into_trancl)
              then show ?thesis
                using f1 full n_s by blast
            qed
        next
          case (fbj U')
          hence "full1 cdcl_bj S U'"
            using bj unfolding full1_def by auto
          moreover have "no_step cdcl_cp S"
            using n_s by blast
          moreover have "T = U"
            using full fbj unfolding full1_def full_def rtranclp_unfold
            by (force dest!: tranclpD simp:cdcl_bj.simps)
          ultimately show ?thesis using cdcl_s'.bj'[of S U'] using fbj by blast
        qed
    qed
qed

lemma cdcl_s_cdcl_s'_connected':
  assumes "cdcl_s S U" and "cdcl_all_struct_inv S"
  shows "cdcl_s' S U
    \<or> (\<exists>U' U''. cdcl_s' S U'' \<and> full1 cdcl_bj U U' \<and> full cdcl_cp U' U'')"
  using assms
proof (induction rule: cdcl_s.induct)
  case (conflict' S T)
  hence "cdcl_s' S T"
    using cdcl_s'.conflict' by blast
  thus ?case
    by blast
next
  case (other' S T U) note o = this(1) and n_s = this(2) and full = this(3) and inv = this(4)
  show ?case
    using o
    proof cases
      case decide
      thus ?thesis using cdcl_s'.simps full n_s by blast
    next
      case bj
      obtain T' where T': "full cdcl_bj T T'"
        using wf_exists_normal_form cdcl_bj_wf unfolding full_def by metis
      hence "full cdcl_bj S T'"
        proof -
          have f1: "cdcl_bj\<^sup>*\<^sup>* T T' \<and> no_step cdcl_bj T'"
            by (metis (no_types) T' full_def)
          then have "cdcl_bj\<^sup>*\<^sup>* S T'"
            by (meson converse_rtranclp_into_rtranclp local.bj)
          then show ?thesis
            using f1 by (simp add: full_def)
        qed
      have "cdcl_bj\<^sup>*\<^sup>* T T'"
        using T' unfolding full_def by simp
      have "cdcl_all_struct_inv T"
        using cdcl_all_struct_inv_inv o other other'.prems by blast
      then consider
          (T'U) "full cdcl_cp T' U"
        | (U) U' U'' where
            "full cdcl_cp T' U''" and
            "full1 cdcl_bj U U'" and
            "full cdcl_cp U' U''" and
            "cdcl_s'\<^sup>*\<^sup>* U U''"
        using cdcl_cp_cdcl_bj_bissimulation[OF full \<open>cdcl_bj\<^sup>*\<^sup>* T T'\<close>] T' unfolding full_def
        by blast
      then show ?thesis
        (* a sledgehammer one-liner:
         by (metis \<open>full cdcl_bj S T'\<close> bj' full_unfold local.bj n_s)*)
        proof cases
          case T'U
          thus ?thesis
            by (metis \<open>full cdcl_bj S T'\<close> cdcl_s'.simps full_unfold local.bj n_s)
        next
          case (U U' U'')
          have "cdcl_s' S U''"
            by (metis U(1) \<open>full cdcl_bj S T'\<close> cdcl_s'.simps full_unfold local.bj n_s)
          thus ?thesis using U(2,3) by blast
        qed
    qed
qed

lemma cdcl_s_cdcl_s'_no_step:
  assumes "cdcl_s S U" and "cdcl_all_struct_inv S" and "no_step cdcl_bj U"
  shows "cdcl_s' S U"
  using cdcl_s_cdcl_s'_connected[OF assms(1,2)] assms(3)
  by (metis (no_types, lifting) full1_def tranclpD)

lemma rtranclp_cdcl_s_connected_to_rtranclp_cdcl_s':
  assumes "cdcl_s\<^sup>*\<^sup>* S U"
  shows "cdcl_s'\<^sup>*\<^sup>* S U \<or> (\<exists>T. cdcl_s'\<^sup>*\<^sup>* S T \<and> cdcl_bj\<^sup>+\<^sup>+ T U \<and> conflicting U \<noteq> C_True)"
  using assms
proof induction
  case base
  thus ?case by simp
next
  case (step T V) note st = this(1) and o = this(2) and IH = this(3)
  from o show ?case
    proof cases
      case conflict'
      then have f2: "cdcl_s' T V"
        using cdcl_s'.conflict' by blast
      obtain ss :: 'st where
        f3: "S = T \<or> cdcl_s\<^sup>*\<^sup>* S ss \<and> cdcl_s ss T"
        by (metis (full_types) rtranclp.simps st)
      obtain ssa :: 'st where
        "cdcl_cp T ssa"
        using conflict' by (metis (no_types) full1_def tranclpD)
      then have "S = T"
        using f3 by (metis (no_types) cdcl_s.simps full_def full1_def)
      then show ?thesis
        using f2 by blast
    next
      case (other' U) note o = this(1) and n_s = this(2) and full = this(3)
      thus ?thesis
        using o
        proof (cases rule: cdcl_o_rule_cases)
          case decide
          hence "cdcl_s'\<^sup>*\<^sup>* S T"
            using IH by auto
          thus ?thesis
            by (meson decide decide' full n_s rtranclp.rtrancl_into_rtrancl)
        next
          case backtrack
          consider
              (s') "cdcl_s'\<^sup>*\<^sup>* S T"
            | (bj) S' where "cdcl_s'\<^sup>*\<^sup>* S S'" and "cdcl_bj\<^sup>+\<^sup>+ S' T" and "conflicting T \<noteq> C_True"
            using IH by blast
          thus ?thesis
            proof cases
              case s'
              moreover
                have "full1 cdcl_bj T U"
                   using backtrack_is_full1_cdcl_bj backtrack by blast
                hence "cdcl_s' T V"
                  using full bj' n_s by blast
              ultimately show ?thesis by auto
            next
              case (bj S') note S_S' = this(1) and bj_T = this(2)
              have "no_step cdcl_cp S'"
                using bj_T by (fastforce simp: cdcl_cp.simps cdcl_bj.simps dest!: tranclpD)
              moreover
                have "full1 cdcl_bj T U"
                  using backtrack_is_full1_cdcl_bj backtrack by blast
                hence "full1 cdcl_bj S' U"
                  using bj_T unfolding full1_def by fastforce
              ultimately have "cdcl_s' S' V" using full by (simp add: bj')
              thus ?thesis using S_S' by auto
            qed
        next
          case skip
          hence [simp]: "U = V"
            using full converse_rtranclpE unfolding full_def by fastforce

          consider
              (s') "cdcl_s'\<^sup>*\<^sup>* S T"
            | (bj) S' where "cdcl_s'\<^sup>*\<^sup>* S S'" and "cdcl_bj\<^sup>+\<^sup>+ S' T" and "conflicting T \<noteq> C_True"
            using IH by blast
          thus ?thesis
            proof cases
              case s'
              have "cdcl_bj\<^sup>+\<^sup>+ T V"
                using skip by force
              moreover have "conflicting V \<noteq> C_True"
                using skip by auto
              ultimately show ?thesis using s' by auto
            next
              case (bj S') note S_S' = this(1) and bj_T = this(2)
              have "cdcl_bj\<^sup>+\<^sup>+ S' V"
                using skip bj_T by (metis \<open>U = V\<close> cdcl_bj.skip tranclp.simps)

              moreover have "conflicting V \<noteq> C_True"
                using skip by auto
              ultimately show ?thesis using S_S' by auto
            qed
        next
          case resolve
          hence [simp]: "U = V"
            using full converse_rtranclpE unfolding full_def by fastforce
          consider
              (s') "cdcl_s'\<^sup>*\<^sup>* S T"
            | (bj) S' where "cdcl_s'\<^sup>*\<^sup>* S S'" and "cdcl_bj\<^sup>+\<^sup>+ S' T" and "conflicting T \<noteq> C_True"
            using IH by blast
          thus ?thesis
            proof cases
              case s'
              have "cdcl_bj\<^sup>+\<^sup>+ T V"
                using resolve by force
              moreover have "conflicting V \<noteq> C_True"
                using resolve by auto
              ultimately show ?thesis using s' by auto
            next
              case (bj S') note S_S' = this(1) and bj_T = this(2)
              have "cdcl_bj\<^sup>+\<^sup>+ S' V"
                using resolve  bj_T by (metis \<open>U = V\<close> cdcl_bj.resolve tranclp.simps)
              moreover have "conflicting V \<noteq> C_True"
                using resolve by auto
              ultimately show ?thesis using S_S' by auto
            qed
        qed
    qed
qed

lemma n_step_cdcl_s_iff_no_step_cdcl_cl_cdcl_o:
  assumes inv: "cdcl_all_struct_inv S"
  shows "no_step cdcl_s' S \<longleftrightarrow> no_step cdcl_cp S \<and> no_step cdcl_o S" (is "?S' S \<longleftrightarrow> ?C S \<and> ?O S")
proof
  assume "?C S \<and> ?O S"
  thus "?S' S"
    by (auto simp: cdcl_s'.simps full1_def tranclp_unfold_begin)
next
  assume n_s: "?S' S"
  have "?C S"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then obtain S' where "cdcl_cp S S'"
        by auto
      then obtain T where "full1 cdcl_cp S T"
        using cdcl_cp_normalized_element_all_inv inv by (metis (no_types, lifting) full_unfold)
      thus False using n_s cdcl_s'.conflict' by blast
    qed
  moreover have "?O S"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then obtain S' where "cdcl_o S S'"
        by auto
      then obtain T where "full1 cdcl_cp S' T"
        using cdcl_cp_normalized_element_all_inv inv
        by (meson cdcl_all_struct_inv_def cdcl_s_cdcl_s'_connected' cdcl_then_exists_cdcl_s_step n_s)
      thus False using n_s by (meson \<open>cdcl_o S S'\<close> cdcl_all_struct_inv_def cdcl_s_cdcl_s'_connected'
        cdcl_then_exists_cdcl_s_step inv)
    qed
  ultimately show "?C S \<and> ?O S" by auto
qed

lemma cdcl_s'_tranclp_cdcl:
   "cdcl_s' S S' \<Longrightarrow> cdcl\<^sup>+\<^sup>+ S S'"
proof (induct rule: cdcl_s'.induct)
  case conflict'
  then show ?case
    by (simp add: full1_def tranclp_cdcl_cp_tranclp_cdcl)
next
  case decide'
  then show ?case
    using cdcl_s.simps cdcl_s_tranclp_cdcl by (meson cdcl_o.simps)
next
  case (bj' Sa S'a S'') note a2 = this(1) and a1 = this(2) and n_s = this(3)
  obtain ss :: "'st \<Rightarrow> 'st \<Rightarrow> ('st \<Rightarrow> 'st \<Rightarrow> bool) \<Rightarrow> 'st" where
    "\<forall>x0 x1 x2. (\<exists>v3. x2 x1 v3 \<and> x2\<^sup>*\<^sup>* v3 x0) = (x2 x1 (ss x0 x1 x2) \<and> x2\<^sup>*\<^sup>* (ss x0 x1 x2) x0)"
    by moura
  then have f3: "\<forall>p s sa. \<not> p\<^sup>+\<^sup>+ s sa \<or> p s (ss sa s p) \<and> p\<^sup>*\<^sup>* (ss sa s p) sa"
    by (metis (full_types) tranclpD)
  have "cdcl_bj\<^sup>+\<^sup>+ Sa S'a \<and> no_step cdcl_bj S'a"
    using a2 by (simp add: full1_def)
  then have "cdcl_bj Sa (ss S'a Sa cdcl_bj) \<and> cdcl_bj\<^sup>*\<^sup>* (ss S'a Sa cdcl_bj) S'a"
    using f3 by auto
  then show "cdcl\<^sup>+\<^sup>+ Sa S''"
    using a1 n_s by (meson bj other rtranclp_cdcl_bj_full1_cdclp_cdcl_s rtranclp_cdcl_s_rtranclp_cdcl
      rtranclp_into_tranclp2)
qed


lemma tranclp_cdcl_s'_tranclp_cdcl:
  "cdcl_s'\<^sup>+\<^sup>+ S S' \<Longrightarrow> cdcl\<^sup>+\<^sup>+ S S'"
  apply (induct rule: tranclp.induct)
   using cdcl_s'_tranclp_cdcl apply blast
  by (meson cdcl_s'_tranclp_cdcl tranclp_trans)

lemma rtranclp_cdcl_s'_rtranclp_cdcl:
   "cdcl_s'\<^sup>*\<^sup>* S S' \<Longrightarrow> cdcl\<^sup>*\<^sup>* S S'"
  using rtranclp_unfold[of cdcl_s' S S'] tranclp_cdcl_s'_tranclp_cdcl[of S S'] by auto

lemma full_cdcl_s_iff_full_cdcl_s':
  assumes inv: "cdcl_all_struct_inv S"
  shows "full cdcl_s S T \<longleftrightarrow> full cdcl_s' S T" (is "?S \<longleftrightarrow> ?S'")
proof
  assume ?S'
  hence "cdcl\<^sup>*\<^sup>* S T"
    using rtranclp_cdcl_s'_rtranclp_cdcl[of S T] unfolding full_def by blast
  hence inv': "cdcl_all_struct_inv T"
    using rtranclp_cdcl_all_struct_inv_inv inv by blast
  have "cdcl_s\<^sup>*\<^sup>* S T"
    using \<open>?S'\<close> unfolding full_def
      using cdcl_s'_is_rtranclp_cdcl_s rtranclp_mono[of cdcl_s' "cdcl_s\<^sup>*\<^sup>*"] by auto
  thus ?S
    using \<open>?S'\<close> inv' cdcl_s_cdcl_s'_connected' unfolding full_def by blast
next
  assume ?S
  hence inv_T:"cdcl_all_struct_inv T"
    by (metis assms full_def rtranclp_cdcl_all_struct_inv_inv rtranclp_cdcl_s_rtranclp_cdcl)

  consider
      (s')  "cdcl_s'\<^sup>*\<^sup>* S T"
    | (st) S' where "cdcl_s'\<^sup>*\<^sup>* S S'" and "cdcl_bj\<^sup>+\<^sup>+ S' T" and "conflicting T \<noteq> C_True"
    using rtranclp_cdcl_s_connected_to_rtranclp_cdcl_s'[of S T] using \<open>?S\<close> unfolding full_def
    by blast
  thus ?S'
    proof cases
      case s'
      thus ?thesis
        by (metis \<open>full cdcl_s S T\<close> inv_T cdcl_all_struct_inv_def cdcl_s'.simps cdcl_s.conflict'
          cdcl_then_exists_cdcl_s_step full_def n_step_cdcl_s_iff_no_step_cdcl_cl_cdcl_o)
    next
      case (st S')
      have "full cdcl_cp T T"
        using conflicting_clause_full_cdcl_cp st(3) by blast
      moreover
        have n_s: "no_step cdcl_bj T"
          by (metis \<open>full cdcl_s S T\<close> bj inv_T cdcl_all_struct_inv_def cdcl_then_exists_cdcl_s_step
            full_def)
        hence "full1 cdcl_bj S' T"
          using st(2) unfolding full1_def by blast
      moreover have "no_step cdcl_cp S'"
        using st(2) by (fastforce dest!: tranclpD simp: cdcl_cp.simps cdcl_bj.simps)
      ultimately have "cdcl_s' S' T"
        using cdcl_s'.bj'[of S' T T] by blast
      hence "cdcl_s'\<^sup>*\<^sup>* S T"
        using st(1) by auto
      moreover have "no_step cdcl_s' T"
        using inv_T by (metis \<open>full cdcl_cp T T\<close> \<open>full cdcl_s S T\<close> cdcl_all_struct_inv_def
          cdcl_then_exists_cdcl_s_step full_def n_step_cdcl_s_iff_no_step_cdcl_cl_cdcl_o)
      ultimately show ?thesis
        unfolding full_def by blast
    qed
qed

lemma conflict_step_cdcl_s_step:
  assumes
    "conflict S T"
    "cdcl_all_struct_inv S"
  shows "\<exists>T. cdcl_s S T"
proof -
  obtain U where "full cdcl_cp S U"
    using cdcl_cp_normalized_element_all_inv assms by blast
  then have "full1 cdcl_cp S U"
    by (metis cdcl_cp.conflict' assms(1) full_unfold)
  thus ?thesis using cdcl_s.conflict' by blast
qed

lemma decide_step_cdcl_s_step:
  assumes
    "decide S T"
    "cdcl_all_struct_inv S"
  shows "\<exists>T. cdcl_s S T"
proof -
  obtain U where "full cdcl_cp T U"
    using cdcl_cp_normalized_element_all_inv by (meson assms(1) assms(2) cdcl_all_struct_inv_inv
      cdcl_cp_normalized_element_all_inv decide other)
  thus ?thesis
    by (metis assms cdcl_cp_normalized_element_all_inv cdcl_s.conflict' decide full_unfold other')
qed

lemma rtranclp_cdcl_cp_conflicting_C_Clause:
  "cdcl_cp\<^sup>*\<^sup>* S T \<Longrightarrow> conflicting S = C_Clause D \<Longrightarrow> S = T"
  using rtranclpD tranclpD by fastforce

inductive cdcl_fw_cp :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
conflict'[intro]: "conflict S T \<Longrightarrow> full cdcl_bj T U \<Longrightarrow> cdcl_fw_cp S U" |
propagate'[intro]: "propagate\<^sup>+\<^sup>+ S S' \<Longrightarrow> cdcl_fw_cp S S'"

lemma cdcl_fw_restart_cases[consumes 1, case_names conflict propagate]:
  assumes
    "cdcl_fw_cp S U" and
    "\<And>T. conflict S T \<Longrightarrow> full cdcl_bj T U \<Longrightarrow> P" and
    "propagate\<^sup>+\<^sup>+ S U \<Longrightarrow> P"
  shows "P"
  using assms unfolding cdcl_fw_cp.simps by auto

lemma cdcl_fw_cp_tranclp_cdcl_fw:
  "cdcl_fw_cp S T \<Longrightarrow> cdcl_fw\<^sup>+\<^sup>+ S T"
  apply (induction rule: cdcl_fw_cp.induct)
    using cdcl_fw.simps apply auto[1]
  using tranclp_mono[of propagate cdcl_fw] fw_propagate by blast

lemma rtranclp_cdcl_fw_cp_rtranclp_cdcl:
  "cdcl_fw_cp\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl\<^sup>*\<^sup>* S T"
 apply (induction rule: rtranclp_induct)
  apply simp
 unfolding cdcl_fw_cp.simps by (meson cdcl_fw_restart_cdcl fw_r_conflict
   rtranclp_propagate_is_rtranclp_cdcl rtranclp_trans tranclp_into_rtranclp)

lemma full1_cdcl_bj_no_step_cdcl_bj:
  "full1 cdcl_bj S T \<Longrightarrow> no_step cdcl_cp S"
  by (metis rtranclp_unfold cdcl_cp_conflicting_not_empty conflicting_clause.exhaust full1_def
    rtranclp_cdcl_fw_restart_no_step_cdcl_bj tranclpD)

inductive cdcl_s'_without_decide where
conflict'_without_decide[intro]: "full1 cdcl_cp S S' \<Longrightarrow> cdcl_s'_without_decide S S'" |
bj'_without_decide[intro]: "full1 cdcl_bj S S' \<Longrightarrow> no_step cdcl_cp S \<Longrightarrow> full cdcl_cp S' S''
      \<Longrightarrow> cdcl_s'_without_decide S S''"

lemma rtranclp_cdcl_s'_without_decide_rtranclp_cdcl:
  "cdcl_s'_without_decide\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl\<^sup>*\<^sup>* S T"
  apply (induction rule: rtranclp_induct)
    apply simp
  by (meson cdcl_s'.simps cdcl_s'_tranclp_cdcl cdcl_s'_without_decide.simps
    rtranclp_tranclp_tranclp tranclp_into_rtranclp)

lemma rtranclp_cdcl_s'_without_decide_rtranclp_cdcl_s':
  "cdcl_s'_without_decide\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl_s'\<^sup>*\<^sup>* S T"
proof (induction rule: rtranclp_induct)
  case base
  thus ?case by simp
next
  case (step y z) note a2 = this(2) and a1 = this(3)
  have "cdcl_s' y z"
    using a2 by (metis (no_types) bj' cdcl_s'.conflict' cdcl_s'_without_decide.cases)
  then show "cdcl_s'\<^sup>*\<^sup>* S z"
    using a1 by (meson r_into_rtranclp rtranclp_trans)
qed

lemma rtranclp_cdcl_fw_cp_is_rtranclp_cdcl_s'_without_decide:
  assumes
    "cdcl_fw_cp\<^sup>*\<^sup>* S V"
    "conflicting S = C_True"
  shows
    "(cdcl_s'_without_decide\<^sup>*\<^sup>* S V)
    \<or> (\<exists>T. cdcl_s'_without_decide\<^sup>*\<^sup>* S T \<and> propagate\<^sup>+\<^sup>+ T V)
    \<or> (\<exists>T U. cdcl_s'_without_decide\<^sup>*\<^sup>* S T \<and> full1 cdcl_bj T U \<and> propagate\<^sup>*\<^sup>* U V)"
  using assms
proof (induction rule: rtranclp_induct)
  case base
  thus ?case by simp
next
  case (step U V) note st = this(1) and cp = this(2) and IH = this(3)[OF this(4)]
  from cp show ?case
    proof (cases rule: cdcl_fw_restart_cases)
      case propagate
      thus ?thesis using IH by (meson rtranclp_tranclp_tranclp tranclp_into_rtranclp)
    next
      case (conflict U') note confl = this(1) and bj = this(2)
      have full1_U_U': "full1 cdcl_cp U U'"
        by (simp add: conflict_is_full1_cdcl_cp local.conflict(1))
      consider
          (s') "cdcl_s'_without_decide\<^sup>*\<^sup>* S U"
        | (propa) T' where "cdcl_s'_without_decide\<^sup>*\<^sup>* S T'" and "propagate\<^sup>+\<^sup>+ T' U"
        | (bj_prop) T' T'' where
            "cdcl_s'_without_decide\<^sup>*\<^sup>* S T' " and
            "full1 cdcl_bj T' T''" and
            "propagate\<^sup>*\<^sup>* T'' U"
        using IH by blast
      thus ?thesis
        proof cases
          case s'
          have "cdcl_s'_without_decide U U'"
           using full1_U_U' conflict'_without_decide by blast
          then have "cdcl_s'_without_decide\<^sup>*\<^sup>* S U'"
            using  \<open>cdcl_s'_without_decide\<^sup>*\<^sup>* S U\<close> by auto
          moreover have "U' = V \<or> full1 cdcl_bj U' V"
            using bj by (meson full_unfold)
          ultimately show ?thesis by blast
        next
          case propa note s' = this(1) and T'_U = this(2)
          have "full1 cdcl_cp T' U'"
            using rtranclp_mono[of propagate cdcl_cp] T'_U cdcl_cp.propagate' full1_U_U'
            rtranclp_full1I[of cdcl_cp T'] by (metis (full_types) predicate2D predicate2I
              tranclp_into_rtranclp)
          have "cdcl_s'_without_decide\<^sup>*\<^sup>* S U'"
            using \<open>full1 cdcl_cp T' U'\<close> conflict'_without_decide s' by force
          have "full1 cdcl_bj U' V \<or> V = U'"
            by (metis (lifting) full_unfold local.bj)
          then show ?thesis
            using \<open>cdcl_s'_without_decide\<^sup>*\<^sup>* S U'\<close> by blast
        next
          case bj_prop note s' = this(1) and bj_T' = this(2) and T''_U = this(3)
          have "no_step cdcl_cp T'"
            using bj_T' full1_cdcl_bj_no_step_cdcl_bj by blast
          moreover have "full1 cdcl_cp T'' U'"
            using rtranclp_mono[of propagate cdcl_cp] T''_U cdcl_cp.propagate' full1_U_U'
            rtranclp_full1I[of cdcl_cp T''] by blast
          ultimately have "cdcl_s'_without_decide T' U'"
            using bj'_without_decide[of T' T'' U'] bj_T' by (simp add: full_unfold)
          then have "cdcl_s'_without_decide\<^sup>*\<^sup>* S U'"
            using s' rtranclp.intros(2)[of _ S T' U'] by blast
          then show ?thesis
            by (metis full_unfold local.bj rtranclp.rtrancl_refl)
        qed
    qed
qed


lemma rtranclp_cdcl_s'_without_decide_is_rtranclp_cdcl_fw_cp:
  assumes
    "cdcl_s'_without_decide\<^sup>*\<^sup>* S V" and
    confl: "conflicting S = C_True"
  shows
    "(cdcl_fw_cp\<^sup>*\<^sup>* S V \<and> conflicting V = C_True)
    \<or> (cdcl_fw_cp\<^sup>*\<^sup>* S V \<and> conflicting V \<noteq> C_True \<and> no_step cdcl_cp V \<and> no_step cdcl_bj V)
    \<or> (\<exists>T. cdcl_fw_cp\<^sup>*\<^sup>* S T \<and> conflict T V)"
  using assms(1)
proof (induction)
  case base
  then show ?case using confl by auto
next
  case (step U V) note st = this(1) and s = this(2) and IH = this(3)
  from s show ?case
    proof (cases rule: cdcl_s'_without_decide.cases)
      case conflict'_without_decide
      then have rt: "cdcl_cp\<^sup>+\<^sup>+ U V"  unfolding full1_def by fast
      then have "conflicting U = C_True"
        using tranclp_cdcl_cp_propagate_with_conflict_or_not[of U V]
        conflict by (auto dest!: tranclpD simp: rtranclp_unfold)
      then have "cdcl_fw_cp\<^sup>*\<^sup>* S U" using IH by auto
      consider
          (propa) "propagate\<^sup>+\<^sup>+ U V"
         | (confl') "conflict U V"
         | (propa_confl') U' where "propagate\<^sup>+\<^sup>+ U U'" "conflict U' V"
        using tranclp_cdcl_cp_propagate_with_conflict_or_not[OF rt] unfolding rtranclp_unfold
        by fastforce
      then show ?thesis
        proof cases
          case propa
          then have "cdcl_fw_cp U V"
            by auto
          moreover have "conflicting V = C_True"
            using propa unfolding tranclp_unfold_end by auto
          ultimately show ?thesis using \<open>cdcl_fw_cp\<^sup>*\<^sup>* S U\<close> by force
        next
          case confl'
          then show ?thesis using \<open>cdcl_fw_cp\<^sup>*\<^sup>* S U\<close> by auto
        next
          case propa_confl' note propa = this(1) and confl' = this(2)
          then have "cdcl_fw_cp U U'" by auto
          then have "cdcl_fw_cp\<^sup>*\<^sup>* S U'" using \<open>cdcl_fw_cp\<^sup>*\<^sup>* S U\<close> by auto
          then show ?thesis using \<open>cdcl_fw_cp\<^sup>*\<^sup>* S U\<close> confl' by auto
        qed
    next
      case (bj'_without_decide U') note full_bj = this(1) and cp = this(3)
      then have "conflicting U \<noteq> C_True"
        using full_bj unfolding full1_def by (fastforce dest!: tranclpD simp: cdcl_bj.simps)
      with IH obtain T where
        S_T: "cdcl_fw_cp\<^sup>*\<^sup>* S T" and T_U: "conflict T U"
        using full_bj unfolding full1_def by (blast dest: tranclpD)
      then have "cdcl_fw_cp T U'"
        using cdcl_fw_cp.conflict'[of T U U'] full_bj by (simp add: full_unfold)
      then have S_U': "cdcl_fw_cp\<^sup>*\<^sup>* S U'" using S_T by auto
      consider
          (n_s) "U' = V"
         | (propa) "propagate\<^sup>+\<^sup>+ U' V"
         | (confl') "conflict U' V"
         | (propa_confl') U'' where "propagate\<^sup>+\<^sup>+ U' U''" "conflict U'' V"
        using tranclp_cdcl_cp_propagate_with_conflict_or_not cp
        unfolding rtranclp_unfold full_def by metis
      then show ?thesis
        proof cases
          case propa
          then have "cdcl_fw_cp U' V" by auto
          moreover have "conflicting V = C_True"
            using propa  unfolding tranclp_unfold_end by auto
          ultimately show ?thesis using S_U' by force
        next
          case confl'
          then show ?thesis using S_U' by auto
        next
          case propa_confl' note propa = this(1) and confl = this(2)
          have "cdcl_fw_cp U' U''" using propa by auto
          then show ?thesis using S_U' confl by (meson rtranclp.rtrancl_into_rtrancl)
        next
          case n_s
          thus ?thesis
            using S_U' apply (cases "conflicting V = C_True")
             using full_bj apply simp
            by (metis cp full_def full_unfold full_bj)
        qed
    qed
qed

lemma no_step_cdcl_s'_no_ste_cdcl_fw_cp:
  assumes
    "cdcl_all_struct_inv S"
    "conflicting S = C_True"
    "no_step cdcl_s' S"
  shows "no_step cdcl_fw_cp S"
  using assms apply (auto simp: cdcl_s'.simps cdcl_fw_cp.simps)
    using conflict_is_full1_cdcl_cp apply blast
  using cdcl_cp_normalized_element_all_inv cdcl_cp.propagate' by (metis cdcl_cp.propagate'
    full_unfold tranclpD)

text \<open>The @{term "no_step decide S"} is needed, since @{term "cdcl_fw_cp"} is
  @{term "cdcl_s'"} without @{term decide}.\<close>
lemma conflicting_true_no_step_cdcl_fw_cp_no_step_s'_without_decide:
  assumes
    confl: "conflicting S = C_True" and
    n_s: "no_step cdcl_fw_cp S"
  shows "no_step cdcl_s'_without_decide S"
proof (rule ccontr)
  assume "\<not> no_step cdcl_s'_without_decide S"
  then obtain T where
    cdcl: "cdcl_s'_without_decide S T"
    by auto
  from cdcl show False
    proof cases
      case conflict'_without_decide
      have "no_step propagate S"
        using n_s by blast
      then have "conflict S T"
        using local.conflict' tranclp_cdcl_cp_propagate_with_conflict_or_not[of S T]
        unfolding full1_def by (metis full1_def local.conflict'_without_decide rtranclp_unfold
          tranclp_unfold_begin)
      moreover
        then obtain T' where "full cdcl_bj T T'"
          using wf_exists_normal_form_full[OF cdcl_bj_wf] by blast
      ultimately show False using cdcl_fw_cp.conflict' n_s by meson
    next
      case (bj'_without_decide S')
      then show ?thesis
        using confl unfolding full1_def by (fastforce simp: cdcl_bj.simps dest: tranclpD)
    qed
qed

lemma conflicting_true_no_step_s'_without_decide_no_step_cdcl_fw_cp:
  assumes
    inv: "cdcl_all_struct_inv S" and
    n_s: "no_step cdcl_s'_without_decide S"
  shows "no_step cdcl_fw_cp S"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then obtain T where "cdcl_fw_cp S T"
    by auto
  then show False
    proof cases
      case (conflict' S')
      thus False using n_s conflict'_without_decide conflict_is_full1_cdcl_cp by blast
    next
      case propagate'
      moreover
        have "cdcl_all_struct_inv T"
          using inv by (meson local.propagate' rtranclp_cdcl_all_struct_inv_inv
            rtranclp_propagate_is_rtranclp_cdcl tranclp_into_rtranclp)
        then obtain U where "full cdcl_cp T U"
          using cdcl_cp_normalized_element_all_inv by auto
      ultimately have "full1 cdcl_cp S U"
        using tranclp_full_full1I[of cdcl_cp S T U] cdcl_cp.propagate'
        tranclp_mono[of propagate cdcl_cp] by blast
      thus False using conflict'_without_decide n_s by blast
    qed
qed

lemma no_step_cdcl_fw_cp_no_step_cdcl_cp:
  "no_step cdcl_fw_cp S \<Longrightarrow> no_step cdcl_cp S"
  using wf_exists_normal_form_full[OF cdcl_bj_wf] by (force simp: cdcl_fw_cp.simps
    cdcl_cp.simps)

lemma conflicting_not_true_rtranclp_cdcl_fw_cp_no_step_cdcl_bj:
  assumes
    "conflicting S = C_True" and
    "cdcl_fw_cp\<^sup>*\<^sup>* S T"
  shows "no_step cdcl_bj T"
  using assms(2,1) by (induction)
  (fastforce simp: cdcl_fw_cp.simps full_def tranclp_unfold_end cdcl_bj.simps)+

lemma conflicting_true_full_cdcl_fw_cp_iff_full_cdcl_s'_without_decode:
  assumes
    confl: "conflicting S = C_True" and
    inv: "cdcl_all_struct_inv S"
  shows
    "full cdcl_fw_cp S V \<longleftrightarrow> full cdcl_s'_without_decide S V" (is "?fw \<longleftrightarrow> ?s'")
proof
  assume ?fw
  then have st: "cdcl_fw_cp\<^sup>*\<^sup>* S V" and n_s: "no_step cdcl_fw_cp V"
    unfolding full_def by blast+
  then consider
      (s') "cdcl_s'_without_decide\<^sup>*\<^sup>* S V"
    | (propa) T where "cdcl_s'_without_decide\<^sup>*\<^sup>* S T" and "propagate\<^sup>+\<^sup>+ T V"
    | (bj) T U where "cdcl_s'_without_decide\<^sup>*\<^sup>* S T" and "full1 cdcl_bj T U" and "propagate\<^sup>*\<^sup>* U V"
    using rtranclp_cdcl_fw_cp_is_rtranclp_cdcl_s'_without_decide confl by metis
  hence "cdcl_s'_without_decide\<^sup>*\<^sup>* S V"
    proof cases
      case s'
      thus ?thesis .
    next
      case propa note s' = this(1) and propa = this(2)
      have "no_step cdcl_cp V"
        using no_step_cdcl_fw_cp_no_step_cdcl_cp n_s by blast
      hence "full1 cdcl_cp T V"
        using propa tranclp_mono[of propagate cdcl_cp] "cdcl_cp.propagate'" unfolding full1_def
        by blast
      hence "cdcl_s'_without_decide T V"
        using conflict'_without_decide by blast
      thus ?thesis using s' by auto
    next
      case bj note s' = this(1) and bj = this(2) and propa = this(3)
      have "no_step cdcl_cp V"
        using no_step_cdcl_fw_cp_no_step_cdcl_cp n_s by blast
      then have "full cdcl_cp U V"
        using propa rtranclp_mono[of propagate cdcl_cp] cdcl_cp.propagate' unfolding full_def
        by blast
      moreover have "no_step cdcl_cp T"
        using bj unfolding full1_def by (fastforce dest!: tranclpD simp:cdcl_bj.simps)
      ultimately have "cdcl_s'_without_decide T V"
        using bj'_without_decide[of T U V] bj by blast
      thus ?thesis using s' by auto
    qed
  moreover have "no_step cdcl_s'_without_decide V"
    using conflicting_true_no_step_cdcl_fw_cp_no_step_s'_without_decide n_s
    proof (cases "conflicting V = C_True")
      assume a1: "conflicting V \<noteq> C_True"
      { fix ss :: 'st
        have ff1: "\<forall>s sa. \<not> cdcl_s' s sa \<or> full1 cdcl_cp s sa
          \<or> (\<exists>sb. decide s sb \<and> no_step cdcl_cp s \<and> full cdcl_cp sb sa)
          \<or> (\<exists>sb. full1 cdcl_bj s sb \<and> no_step cdcl_cp s \<and> full cdcl_cp sb sa)"
          by (metis cdcl_s'.cases)
        have ff2: "(\<forall>p s sa. \<not> full1 p (s::'st) sa \<or> p\<^sup>+\<^sup>+ s sa \<and> no_step p sa)
          \<and> (\<forall>p s sa. (\<not> p\<^sup>+\<^sup>+ (s::'st) sa \<or> (\<exists>s. p sa s)) \<or> full1 p s sa)"
          by (meson full1_def)
        obtain ssa :: "('st \<Rightarrow> 'st \<Rightarrow> bool) \<Rightarrow> 'st \<Rightarrow> 'st \<Rightarrow> 'st" where
          ff3: "\<forall>p s sa. \<not> p\<^sup>+\<^sup>+ s sa \<or> p s (ssa p s sa) \<and> p\<^sup>*\<^sup>* (ssa p s sa) sa"
          by (metis (no_types) tranclpD)
        then have a3: "\<not> cdcl_cp\<^sup>+\<^sup>+ V ss"
          using a1 by (metis conflicting_clause_full_cdcl_cp full_def)
        have "\<And>s. \<not> cdcl_bj\<^sup>+\<^sup>+ V s"
          using ff3 a1 by (metis confl st
            conflicting_not_true_rtranclp_cdcl_fw_cp_no_step_cdcl_bj)
        then have "\<not> cdcl_s'_without_decide V ss"
          using ff1 a3 ff2 by (metis cdcl_s'_without_decide.cases)
    }
      then show ?thesis
        by fastforce
    qed (blast)
  ultimately show ?s' unfolding full_def by blast
next
  assume s': ?s'
  then have st: "cdcl_s'_without_decide\<^sup>*\<^sup>* S V" and n_s: "no_step cdcl_s'_without_decide V"
    unfolding full_def by auto
  then have "cdcl\<^sup>*\<^sup>* S V"
    using rtranclp_cdcl_s'_without_decide_rtranclp_cdcl st by blast
  then have inv_V: "cdcl_all_struct_inv V" using inv rtranclp_cdcl_all_struct_inv_inv by blast
  then have n_s_cp_V: "no_step cdcl_cp V"
    using cdcl_cp_normalized_element_all_inv[of V] full_fullI[of cdcl_cp V] n_s
    conflict'_without_decide conflicting_true_no_step_s'_without_decide_no_step_cdcl_fw_cp
    no_step_cdcl_fw_cp_no_step_cdcl_cp by presburger
  have n_s_bj: "no_step cdcl_bj V"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then obtain W where "cdcl_bj V W" by blast
      then obtain W' where "full1 cdcl_bj V W'"
        using wf_exists_normal_form_full[OF cdcl_bj_wf, of W] full_fullI[of cdcl_bj V W]
        by blast
      moreover
        then have "cdcl\<^sup>+\<^sup>+ V W'"
          using tranclp_mono[of cdcl_bj cdcl] cdcl.other cdcl_o.bj unfolding full1_def by blast
        then have "cdcl_all_struct_inv W'"
          by (meson inv_V rtranclp_cdcl_all_struct_inv_inv tranclp_into_rtranclp)
        then obtain X where "full cdcl_cp W' X"
          using cdcl_cp_normalized_element_all_inv by blast
      ultimately show False
        using bj'_without_decide n_s_cp_V n_s by blast
    qed
  from s' consider
      (cp_true) "cdcl_fw_cp\<^sup>*\<^sup>* S V" and "conflicting V = C_True"
    | (cp_false) "cdcl_fw_cp\<^sup>*\<^sup>* S V" and "conflicting V \<noteq> C_True" and "no_step cdcl_cp V" and
         "no_step cdcl_bj V"
    | (cp_confl) T where "cdcl_fw_cp\<^sup>*\<^sup>* S T" "conflict T V"
    using rtranclp_cdcl_s'_without_decide_is_rtranclp_cdcl_fw_cp[of S V] confl
    unfolding full_def by blast
  then have "cdcl_fw_cp\<^sup>*\<^sup>* S V"
    proof cases
      case cp_confl note S_T = this(1) and conf_V = this(2)
      have "full cdcl_bj V V"
        using conf_V n_s_bj unfolding full_def by fast
      then have "cdcl_fw_cp T V"
        using cdcl_fw_cp.conflict' conf_V by auto
      then show ?thesis using S_T by auto
    qed fast+
  moreover
    then have "cdcl\<^sup>*\<^sup>* S V" using rtranclp_cdcl_fw_cp_rtranclp_cdcl by blast
    then have "cdcl_all_struct_inv V"
      using inv rtranclp_cdcl_all_struct_inv_inv by blast
    then have "no_step cdcl_fw_cp V"
      using conflicting_true_no_step_s'_without_decide_no_step_cdcl_fw_cp s'
      unfolding full_def by blast
  ultimately show ?fw unfolding full_def by auto
qed

lemma conflicting_true_full1_cdcl_fw_cp_iff_full1_cdcl_s'_without_decode:
  assumes
    confl: "conflicting S = C_True" and
    inv: "cdcl_all_struct_inv S"
  shows
    "full1 cdcl_fw_cp S V \<longleftrightarrow> full1 cdcl_s'_without_decide S V"
proof -
  have "full cdcl_fw_cp S V = full cdcl_s'_without_decide S V"
    using confl conflicting_true_full_cdcl_fw_cp_iff_full_cdcl_s'_without_decode inv
    by blast
  then show ?thesis unfolding full_unfold full1_def
    by (metis (mono_tags) tranclp_unfold_begin)
qed

lemma conflicting_true_full1_cdcl_fw_cp_imp_full1_cdcl_s'_without_decode:
  assumes
    fw: "full1 cdcl_fw_cp S V" and
    inv: "cdcl_all_struct_inv S"
  shows
    "full1 cdcl_s'_without_decide S V"
proof -
  have "conflicting S = C_True"
    using fw unfolding full1_def by (auto dest!: tranclpD simp: cdcl_fw_cp.simps)
  then show ?thesis
    using conflicting_true_full1_cdcl_fw_cp_iff_full1_cdcl_s'_without_decode fw inv by blast
qed

inductive cdcl_fw_s where
fw_s_cp[intro]: "full1 cdcl_fw_cp S T \<Longrightarrow> cdcl_fw_s S T" |
fw_s_decide[intro]: "decide S T \<Longrightarrow> no_step cdcl_fw_cp S \<Longrightarrow> full cdcl_fw_cp T U
  \<Longrightarrow>  cdcl_fw_s S U"

lemma cdcl_fw_s_tranclp_cdcl_fw:
  assumes fw: "cdcl_fw_s S T"
  shows "cdcl_fw\<^sup>+\<^sup>+ S T"
proof -
  { fix S T
    assume "full1 cdcl_fw_cp S T"
    then have "cdcl_fw\<^sup>+\<^sup>+ S T"
      using tranclp_mono[of cdcl_fw_cp "cdcl_fw\<^sup>+\<^sup>+"] cdcl_fw_cp_tranclp_cdcl_fw unfolding full1_def
      by auto
  } note full1_cdcl_fw_cp_cdcl_fw = this
  show ?thesis
    using fw
    apply (induction rule: cdcl_fw_s.induct)
      using full1_cdcl_fw_cp_cdcl_fw apply simp
    unfolding full_unfold by (auto dest!: full1_cdcl_fw_cp_cdcl_fw fw_decide)
qed

lemma rtranclp_cdcl_fw_s_rtranclp_cdcl_fw:
  assumes fw: "cdcl_fw_s\<^sup>*\<^sup>* S T"
  shows "cdcl_fw\<^sup>*\<^sup>* S T"
  using fw cdcl_fw_s_tranclp_cdcl_fw rtranclp_mono[of cdcl_fw_s "cdcl_fw\<^sup>+\<^sup>+"]
  unfolding tranclp_rtranclp_rtranclp by blast

lemma cdcl_fw_s_rtranclp_cdcl:
  "cdcl_fw_s S T \<Longrightarrow> cdcl\<^sup>*\<^sup>* S T"
  apply (induction rule: cdcl_fw_s.induct)
    using rtranclp_cdcl_fw_cp_rtranclp_cdcl unfolding full1_def
    apply (simp add: tranclp_into_rtranclp)
  using rtranclp_cdcl_fw_cp_rtranclp_cdcl cdcl_o.decide cdcl.other unfolding full_def
  by (meson r_into_rtranclp rtranclp_trans)

lemma rtranclp_cdcl_fw_s_rtranclp_cdcl:
  "cdcl_fw_s\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl\<^sup>*\<^sup>* S T"
  using rtranclp_mono[of cdcl_fw_s "cdcl\<^sup>*\<^sup>*"] cdcl_fw_s_rtranclp_cdcl by auto

inductive cdcl_s'_w :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
conflict': "full1 cdcl_s'_without_decide S S' \<Longrightarrow> cdcl_s'_w S S'" |
decide': "decide S S' \<Longrightarrow> no_step cdcl_s'_without_decide S \<Longrightarrow> full cdcl_s'_without_decide S' S''
  \<Longrightarrow> cdcl_s'_w S S''"

lemma cdcl_s'_w_rtranclp_cdcl:
  "cdcl_s'_w S T \<Longrightarrow> cdcl\<^sup>*\<^sup>* S T"
  apply (induction rule: cdcl_s'_w.induct)
    using rtranclp_cdcl_s'_without_decide_rtranclp_cdcl unfolding full1_def
    apply (simp add: tranclp_into_rtranclp)
  using rtranclp_cdcl_s'_without_decide_rtranclp_cdcl unfolding full_def
  by (meson decide other rtranclp_into_tranclp2 tranclp_into_rtranclp)

lemma rtranclp_cdcl_s'_w_rtranclp_cdcl:
  "cdcl_s'_w\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl\<^sup>*\<^sup>* S T"
  using rtranclp_mono[of cdcl_s'_w "cdcl\<^sup>*\<^sup>*"] cdcl_s'_w_rtranclp_cdcl by auto

lemma no_step_cdcl_cp_no_step_cdcl_s'_without_decide:
  assumes "no_step cdcl_cp S" and "conflicting S = C_True"
  shows "no_step cdcl_s'_without_decide S"
  by (metis assms cdcl_cp.conflict' cdcl_cp.propagate' cdcl_fw_restart_cases tranclpD
    conflicting_true_no_step_cdcl_fw_cp_no_step_s'_without_decide)

lemma no_step_cdcl_cp_no_step_cdcl_fw_restart:
  assumes "no_step cdcl_cp S" and "conflicting S = C_True"
  shows "no_step cdcl_fw_cp S"
  by (metis assms(1) cdcl_cp.conflict' cdcl_cp.propagate' cdcl_fw_restart_cases tranclpD)
lemma after_cdcl_s'_without_decide_no_step_cdcl_cp:
  assumes "cdcl_s'_without_decide S T"
  shows "no_step cdcl_cp T"
  using assms by (induction rule: cdcl_s'_without_decide.induct) (auto simp: full1_def full_def)

lemma no_step_cdcl_s'_without_decide_no_step_cdcl_cp:
  "cdcl_all_struct_inv S \<Longrightarrow> no_step cdcl_s'_without_decide S \<Longrightarrow> no_step cdcl_cp S"
  by (simp add: conflicting_true_no_step_s'_without_decide_no_step_cdcl_fw_cp
    no_step_cdcl_fw_cp_no_step_cdcl_cp)

lemma after_cdcl_s'_w_no_step_cdcl_cp:
  assumes "cdcl_s'_w S T" and "cdcl_all_struct_inv S"
  shows "no_step cdcl_cp T"
  using assms
proof (induction rule: cdcl_s'_w.induct)
  case conflict'
  thus ?case
    by (auto simp: full1_def tranclp_unfold_end after_cdcl_s'_without_decide_no_step_cdcl_cp)
next
  case (decide' S T U)
  moreover
    then have "cdcl\<^sup>*\<^sup>* S U"
      using rtranclp_cdcl_s'_without_decide_rtranclp_cdcl[of T U] cdcl.other[of S T] cdcl_o.decide
      unfolding full_def by auto
    then have "cdcl_all_struct_inv U"
      using decide'.prems rtranclp_cdcl_all_struct_inv_inv by blast
  ultimately show ?case
    using no_step_cdcl_s'_without_decide_no_step_cdcl_cp unfolding full_def by blast
qed

lemma rtranclp_cdcl_s'_w_no_step_cdcl_cp_or_eq:
  assumes "cdcl_s'_w\<^sup>*\<^sup>* S T" and "cdcl_all_struct_inv S"
  shows "S = T \<or> no_step cdcl_cp T"
  using assms
proof (induction rule: rtranclp_induct)
  case base
  then show ?case by simp
next
  case (step T U)
  moreover have "cdcl_all_struct_inv T"
    using rtranclp_cdcl_s'_w_rtranclp_cdcl[of S U] assms(2) rtranclp_cdcl_all_struct_inv_inv
    rtranclp_cdcl_s'_w_rtranclp_cdcl step.hyps(1) by blast
  ultimately show ?case using after_cdcl_s'_w_no_step_cdcl_cp by fast
qed

lemma rtranclp_cdcl_fw_s'_no_step_cdcl_cp_or_eq:
  assumes "cdcl_fw_s\<^sup>*\<^sup>* S T" and "cdcl_all_struct_inv S"
  shows "S = T \<or> no_step cdcl_cp T"
  using assms
proof (induction rule: rtranclp_induct)
  case base
  then show ?case by simp
next
  case (step T U)
  moreover have "cdcl_all_struct_inv T"
    using rtranclp_cdcl_fw_s_rtranclp_cdcl[of S U] assms(2) rtranclp_cdcl_all_struct_inv_inv
    rtranclp_cdcl_s'_w_rtranclp_cdcl step.hyps(1) by (meson rtranclp_cdcl_fw_s_rtranclp_cdcl)
  ultimately show ?case
    using after_cdcl_s'_w_no_step_cdcl_cp by (metis (full_types) cdcl_fw_s.simps full_def
      full1_def no_step_cdcl_fw_cp_no_step_cdcl_cp)
qed

lemma no_step_cdcl_s'_without_decide_no_step_cdcl_bj:
  assumes "no_step cdcl_s'_without_decide S" and inv: "cdcl_all_struct_inv S"
  shows "no_step cdcl_bj S"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then obtain T where S_T: "cdcl_bj S T"
    by auto
  then obtain T' where "full1 cdcl_bj S T'"
    using wf_exists_normal_form_full[OF cdcl_bj_wf, of T] full_fullI by metis
  moreover
    then have "cdcl\<^sup>*\<^sup>* S T'"
      using rtranclp_mono[of cdcl_bj cdcl] cdcl.other cdcl_o.bj tranclp_into_rtranclp[of cdcl_bj]
      unfolding full1_def by (metis (full_types) predicate2D predicate2I)
    then have "cdcl_all_struct_inv T'"
      using inv  rtranclp_cdcl_all_struct_inv_inv by blast
    then obtain U where "full cdcl_cp T' U"
      using cdcl_cp_normalized_element_all_inv by blast
  moreover have "no_step cdcl_cp S"
    using S_T by (auto simp: cdcl_bj.simps)
  ultimately show False
  using assms cdcl_s'_without_decide.intros(2)[of S T' U] by fast
qed

lemma cdcl_s'_w_no_step_cdcl_bj:
  assumes "cdcl_s'_w S T" and "cdcl_all_struct_inv S"
  shows "no_step cdcl_bj T"
  using assms apply induction
    using rtranclp_cdcl_s'_without_decide_rtranclp_cdcl rtranclp_cdcl_all_struct_inv_inv
    no_step_cdcl_s'_without_decide_no_step_cdcl_bj unfolding full1_def
    apply (meson tranclp_into_rtranclp)
  using rtranclp_cdcl_s'_without_decide_rtranclp_cdcl rtranclp_cdcl_all_struct_inv_inv
    no_step_cdcl_s'_without_decide_no_step_cdcl_bj unfolding full_def
  by (meson cdcl_fw_restart_cdcl fw_r_decide)

lemma rtranclp_cdcl_s'_w_no_step_cdcl_bj_or_eq:
  assumes "cdcl_s'_w\<^sup>*\<^sup>* S T" and "cdcl_all_struct_inv S"
  shows "S = T \<or> no_step cdcl_bj T"
  using assms apply induction
    apply simp
  using rtranclp_cdcl_s'_w_rtranclp_cdcl rtranclp_cdcl_all_struct_inv_inv
    cdcl_s'_w_no_step_cdcl_bj by meson

lemma rtranclp_cdcl_s'_no_step_cdcl_s'_without_decide_decomp_into_cdcl_fw:
  assumes
    "cdcl_s'\<^sup>*\<^sup>* R V" and
    "conflicting R = C_True" and
    inv: "cdcl_all_struct_inv R"
  shows "(cdcl_fw_s\<^sup>*\<^sup>* R V \<and> conflicting V = C_True)
  \<or> (cdcl_fw_s\<^sup>*\<^sup>* R V \<and> conflicting V \<noteq> C_True \<and> no_step cdcl_bj V)
  \<or> (\<exists>S T U. cdcl_fw_s\<^sup>*\<^sup>* R S \<and> no_step cdcl_fw_cp S \<and> decide S T
    \<and> cdcl_fw_cp\<^sup>*\<^sup>* T U \<and> conflict U V)
  \<or> (\<exists>S T. cdcl_fw_s\<^sup>*\<^sup>* R S \<and> no_step cdcl_fw_cp S \<and> decide S T
    \<and> cdcl_fw_cp\<^sup>*\<^sup>* T V
      \<and> conflicting V = C_True)
  \<or> (cdcl_fw_cp\<^sup>*\<^sup>* R V \<and> conflicting V = C_True)
  \<or> (\<exists>U. cdcl_fw_cp\<^sup>*\<^sup>* R U \<and> conflict U V)"
  using assms(1,2)
proof induction
  case base
  thus ?case by simp
next
  case (step V W) note st = this(1) and s' = this(2) and IH = this(3)[OF this(4)] and
    n_s_R = this(4)
  from s'
  show ?case
    proof cases
      case conflict'
      consider
         (s') "cdcl_fw_s\<^sup>*\<^sup>* R V"
        | (dec_confl) S T U where "cdcl_fw_s\<^sup>*\<^sup>* R S" and "no_step cdcl_fw_cp S" and
            "decide S T" and "cdcl_fw_cp\<^sup>*\<^sup>* T U" and "conflict U V"
        | (dec) S T where "cdcl_fw_s\<^sup>*\<^sup>* R S" and "no_step cdcl_fw_cp S" and "decide S T" and
            "cdcl_fw_cp\<^sup>*\<^sup>* T V" and "conflicting V = C_True"
        | (cp) "cdcl_fw_cp\<^sup>*\<^sup>* R V"
        | (cp_confl) U where "cdcl_fw_cp\<^sup>*\<^sup>* R U" and "conflict U V"
        using IH by meson
      then show ?thesis
        proof cases
        next
          case s'
          then have "R = V"
            by (metis full1_def inv local.conflict' rtranclp_cdcl_fw_s'_no_step_cdcl_cp_or_eq
              tranclp_unfold_begin)
          consider
              (V_W) "V = W"
            | (propa) "propagate\<^sup>+\<^sup>+ V W" and "conflicting W = C_True"
            | (propa_confl) V' where "propagate\<^sup>*\<^sup>* V V'" and "conflict V' W"
            using tranclp_cdcl_cp_propagate_with_conflict_or_not[of V W] conflict'
            unfolding full_unfold full1_def by blast
          thus ?thesis
            proof cases
              case V_W
              then show ?thesis using \<open>R = V\<close> n_s_R by simp
            next
              case propa
              then show ?thesis using \<open>R = V\<close> by auto
            next
              case propa_confl
              moreover
                then have "cdcl_fw_cp\<^sup>*\<^sup>* V V'"
                  by (metis Nitpick.rtranclp_unfold cdcl_fw_cp.propagate' r_into_rtranclp)
              ultimately show ?thesis using s' \<open>R = V\<close> by blast
            qed
        next
          case dec_confl note _ = this(5)
          then have False using conflict' unfolding full1_def by (auto dest!: tranclpD)
          then show ?thesis by fast
        next
          case dec note T_V = this(4)
          consider
              (propa) "propagate\<^sup>+\<^sup>+ V W" and "conflicting W = C_True"
            | (propa_confl) V' where "propagate\<^sup>*\<^sup>* V V'" and "conflict V' W"
            using tranclp_cdcl_cp_propagate_with_conflict_or_not[of V W] conflict'
            unfolding full1_def by blast
          then show ?thesis (* too many levels of case distinction *)
            proof cases
              case propa
              thus ?thesis by (meson T_V cdcl_fw_cp.propagate' dec rtranclp.rtrancl_into_rtrancl)
            next
              case propa_confl
              hence "cdcl_fw_cp\<^sup>*\<^sup>* T V'"
                using T_V by (metis rtranclp_unfold cdcl_fw_cp.propagate' rtranclp.simps)
              then show ?thesis using dec propa_confl(2) by metis
            qed
        next
          case cp
          consider
              (propa) "propagate\<^sup>+\<^sup>+ V W" and "conflicting W = C_True"
            | (propa_confl) V' where "propagate\<^sup>*\<^sup>* V V'" and "conflict V' W"
            using tranclp_cdcl_cp_propagate_with_conflict_or_not[of V W] conflict'
            unfolding full1_def by blast
          then show ?thesis (* too many levels of case distinction *)
            proof cases
              case propa
              thus ?thesis by (meson cdcl_fw_cp.propagate' cp rtranclp.rtrancl_into_rtrancl)
            next
              case propa_confl
              then show ?thesis using propa_confl(2) by (metis rtranclp_unfold cdcl_fw_cp.propagate'
                cp rtranclp.rtrancl_into_rtrancl)
            qed
        next
          case cp_confl
          then show ?thesis using conflict' unfolding full1_def by (fastforce dest!: tranclpD)
        qed
    next
      case (decide' V')
      then have conf_V: "conflicting V = C_True"
        by auto
      have "no_step cdcl_s'_without_decide V"
        using conf_V local.decide'(2) no_step_cdcl_cp_no_step_cdcl_s'_without_decide by blast
      consider
         (s') "cdcl_fw_s\<^sup>*\<^sup>* R V"
        | (dec_confl) S T U where "cdcl_fw_s\<^sup>*\<^sup>* R S" and "no_step cdcl_fw_cp S" and
            "decide S T" and "cdcl_fw_cp\<^sup>*\<^sup>* T U" and "conflict U V"
        | (dec) S T where "cdcl_fw_s\<^sup>*\<^sup>* R S" and "no_step cdcl_fw_cp S" and "decide S T" and
            "cdcl_fw_cp\<^sup>*\<^sup>* T V" and "conflicting V = C_True"
        | (cp) "cdcl_fw_cp\<^sup>*\<^sup>* R V"
        | (cp_confl) U where "cdcl_fw_cp\<^sup>*\<^sup>* R U" and "conflict U V"
        using IH by meson
      then show ?thesis
        proof cases
          case s'
          have confl_V': "conflicting V' = C_True" using decide'(1) by auto
          have full: "full1 cdcl_cp V' W \<or> (V' = W \<and> no_step cdcl_cp W)"
            using decide'(3) unfolding full_unfold by blast
          consider
              (V'_W) "V' = W"
            | (propa) "propagate\<^sup>+\<^sup>+ V' W" and "conflicting W = C_True"
            | (propa_confl) V'' where "propagate\<^sup>*\<^sup>* V' V''" and "conflict V'' W"
            using tranclp_cdcl_cp_propagate_with_conflict_or_not[of V W] decide'
            by (metis \<open>full1 cdcl_cp V' W \<or> V' = W \<and> no_step cdcl_cp W\<close> full1_def
              tranclp_cdcl_cp_propagate_with_conflict_or_not)
          then show ?thesis (* too many levels of case distinction *)
            proof cases
              case V'_W
              thus ?thesis
                using confl_V' local.decide'(1,2) s' conf_V no_step_cdcl_cp_no_step_cdcl_fw_restart
                by auto
            next
              case propa
              thus ?thesis using local.decide'(1,2) s' by (metis cdcl_fw_cp.simps conf_V
                no_step_cdcl_cp_no_step_cdcl_fw_restart r_into_rtranclp)
            next
              case propa_confl
              hence "cdcl_fw_cp\<^sup>*\<^sup>* V' V''"
                by (metis rtranclp_unfold cdcl_fw_cp.propagate' r_into_rtranclp)
              then show ?thesis
                using local.decide'(1,2) propa_confl(2) s' conf_V
                no_step_cdcl_cp_no_step_cdcl_fw_restart
                by metis
            qed
        next
          case (dec) note s' = this(1) and dec = this(2) and cp = this(3) and ns_cp_T = this(4)
          have "full cdcl_fw_cp T V"
            unfolding full_def by (simp add: conf_V local.decide'(2)
              no_step_cdcl_cp_no_step_cdcl_fw_restart ns_cp_T)
          moreover have "no_step cdcl_fw_cp V"
             by (simp add: conf_V local.decide'(2) no_step_cdcl_cp_no_step_cdcl_fw_restart)
          moreover have "no_step cdcl_fw_cp S"
            by (metis dec)
          ultimately have "cdcl_fw_s S V"
            using cp by blast
          then have "cdcl_fw_s\<^sup>*\<^sup>* R V" using s' by auto
          consider
              (V'_W) "V' = W"
            | (propa) "propagate\<^sup>+\<^sup>+ V' W" and "conflicting W = C_True"
            | (propa_confl) V'' where "propagate\<^sup>*\<^sup>* V' V''" and "conflict V'' W"
            using tranclp_cdcl_cp_propagate_with_conflict_or_not[of V' W] decide'
            unfolding full_unfold full1_def by blast
          then show ?thesis (* too many levels of case distinction *)
            proof cases
              case V'_W
              moreover have "conflicting V' = C_True"
                using decide'(1) by auto
              ultimately show ?thesis
                using \<open>cdcl_fw_s\<^sup>*\<^sup>* R V\<close> decide' \<open>no_step cdcl_fw_cp V\<close> by blast
            next
              case propa
              moreover then have "cdcl_fw_cp V' W"
                by auto
              ultimately show ?thesis
                using \<open>cdcl_fw_s\<^sup>*\<^sup>* R V\<close> decide' \<open>no_step cdcl_fw_cp V\<close>
                by (meson r_into_rtranclp)
            next
              case propa_confl
              moreover then have "cdcl_fw_cp\<^sup>*\<^sup>* V' V''"
                by (metis cdcl_fw_cp.propagate' rtranclp_unfold tranclp_unfold_end)
              ultimately show ?thesis using \<open>cdcl_fw_s\<^sup>*\<^sup>* R V\<close> decide' \<open>no_step cdcl_fw_cp V\<close>
                by (meson r_into_rtranclp)
            qed
        next
          case cp
          have "no_step cdcl_fw_cp V"
            using conf_V local.decide'(2) no_step_cdcl_cp_no_step_cdcl_fw_restart by blast
          then have "full cdcl_fw_cp R V"
            unfolding full_def using cp by fast
          then have "cdcl_fw_s\<^sup>*\<^sup>* R V"
            unfolding full_unfold by auto
          have "full1 cdcl_cp V' W \<or> (V' = W \<and> no_step cdcl_cp W)"
            using decide'(3) unfolding full_unfold by blast

          consider
              (V'_W) "V' = W"
            | (propa) "propagate\<^sup>+\<^sup>+ V' W" and "conflicting W = C_True"
            | (propa_confl) V'' where "propagate\<^sup>*\<^sup>* V' V''" and "conflict V'' W"
            using tranclp_cdcl_cp_propagate_with_conflict_or_not[of V' W] decide'
            unfolding full_unfold full1_def by blast
          then show ?thesis (* too many levels of case distinction *)
          (* copy paste. copy paste, copy paste *)
            proof cases
              case V'_W
              moreover have "conflicting V' = C_True"
                using decide'(1) by auto
              ultimately show ?thesis
                using \<open>cdcl_fw_s\<^sup>*\<^sup>* R V\<close> decide'  \<open>no_step cdcl_fw_cp V\<close> by blast
            next
              case propa
              moreover then have "cdcl_fw_cp V' W"
                by auto
              ultimately show ?thesis using \<open>cdcl_fw_s\<^sup>*\<^sup>* R V\<close> decide' \<open>no_step cdcl_fw_cp V\<close>
                 by (meson r_into_rtranclp)
            next
              case propa_confl
              moreover then have "cdcl_fw_cp\<^sup>*\<^sup>* V' V''"
                by (metis cdcl_fw_cp.propagate' rtranclp_unfold tranclp_unfold_end)
              ultimately show ?thesis using \<open>cdcl_fw_s\<^sup>*\<^sup>* R V\<close> decide' \<open>no_step cdcl_fw_cp V\<close>
                 by (meson r_into_rtranclp)
            qed
        next
          case (dec_confl) (* Oh! a simple case *)
          show ?thesis using conf_V dec_confl(5) by auto
        next
          case cp_confl
          then show ?thesis using decide' by fastforce
      qed
    next
      case (bj' V')
      hence "\<not>no_step cdcl_bj V "
        by (auto dest: tranclpD simp: full1_def)
      then consider
         (s') "cdcl_fw_s\<^sup>*\<^sup>* R V" and "conflicting V = C_True"
        | (dec_confl) S T U where "cdcl_fw_s\<^sup>*\<^sup>* R S" and "no_step cdcl_fw_cp S" and
            "decide S T" and "cdcl_fw_cp\<^sup>*\<^sup>* T U" and "conflict U V"
        | (dec) S T where "cdcl_fw_s\<^sup>*\<^sup>* R S" and "no_step cdcl_fw_cp S" and "decide S T" and
            "cdcl_fw_cp\<^sup>*\<^sup>* T V" and "conflicting V = C_True"
        | (cp) "cdcl_fw_cp\<^sup>*\<^sup>* R V" and "conflicting V = C_True"
        | (cp_confl) U where "cdcl_fw_cp\<^sup>*\<^sup>* R U" and "conflict U V"
        using IH by meson
      then show ?thesis
        proof cases
          case s' note _ =this(2)
          then have False
            using bj'(1) unfolding full1_def by (force dest!: tranclpD simp: cdcl_bj.simps)
          then show ?thesis by fast
        next
          case dec note _ = this(5)
          then have False
            using bj'(1) unfolding full1_def by (force dest!: tranclpD simp: cdcl_bj.simps)
          then show ?thesis by fast
        next
          case dec_confl
          then have "cdcl_fw_cp U V'"
            using bj' cdcl_fw_cp.intros(1)[of U V V'] by (simp add: full_unfold)
          then have "cdcl_fw_cp\<^sup>*\<^sup>* T V'"
            using dec_confl(4) by simp
          consider
              (V'_W) "V' = W"
            | (propa) "propagate\<^sup>+\<^sup>+ V' W" and "conflicting W = C_True"
            | (propa_confl) V'' where "propagate\<^sup>*\<^sup>* V' V''" and "conflict V'' W"
            using tranclp_cdcl_cp_propagate_with_conflict_or_not[of V' W] bj'(3)
            unfolding full_unfold full1_def by blast
          then show ?thesis (* too many levels of case distinction *)
            proof cases
              case V'_W
              then have "no_step cdcl_cp V'"
                using bj'(3) unfolding full_def by auto
              then have "no_step cdcl_fw_cp V'"
                by (metis cdcl_cp.propagate' cdcl_fw_cp.cases tranclpD
                  no_step_cdcl_cp_no_conflict_no_propagate(1) )
              then have "full1 cdcl_fw_cp T V'"
                unfolding full1_def using \<open>cdcl_fw_cp U V'\<close> dec_confl(4) by auto
              then have "full  cdcl_fw_cp T V'"
                by (simp add: full_unfold)
              then have "cdcl_fw_s S V'"
                using dec_confl(3) cdcl_fw_s.fw_s_decide \<open>no_step cdcl_fw_cp S\<close> by blast
              then have "cdcl_fw_s\<^sup>*\<^sup>* R V'"
                using \<open>cdcl_fw_s\<^sup>*\<^sup>* R S\<close> by auto
              show ?thesis
                proof cases
                  assume "conflicting W = C_True"
                  then show ?thesis using \<open>cdcl_fw_s\<^sup>*\<^sup>* R V'\<close> \<open>V' = W\<close> by auto
                next
                  assume "conflicting W \<noteq> C_True"
                  then show ?thesis
                    using \<open>cdcl_fw_s\<^sup>*\<^sup>* R V'\<close> \<open>V' = W\<close> by (metis \<open>cdcl_fw_cp U V'\<close> conflictE
                      conflicting_not_true_rtranclp_cdcl_fw_cp_no_step_cdcl_bj dec_confl(5)
                      r_into_rtranclp)
                qed
            next
              case propa
              moreover then have "cdcl_fw_cp V' W"
                by auto
              ultimately show ?thesis using decide' by (meson \<open>cdcl_fw_cp\<^sup>*\<^sup>* T V'\<close> dec_confl(1-3)
                rtranclp.rtrancl_into_rtrancl)
            next
              case propa_confl
              moreover then have "cdcl_fw_cp\<^sup>*\<^sup>* V' V''"
                by (metis cdcl_fw_cp.propagate' rtranclp_unfold tranclp_unfold_end)
              ultimately show ?thesis by (meson \<open>cdcl_fw_cp\<^sup>*\<^sup>* T V'\<close> dec_confl(1-3) rtranclp_trans)
            qed
        next
          case cp note _ = this(2)
          then show ?thesis using bj'(1)  \<open>\<not> no_step cdcl_bj V\<close>
            conflicting_not_true_rtranclp_cdcl_fw_cp_no_step_cdcl_bj by auto
        next
          case cp_confl
          then have "cdcl_fw_cp U V'" by (simp add: cdcl_fw_cp.conflict' full_unfold local.bj'(1))
          thm bj'
          consider
              (V'_W) "V' = W"
            | (propa) "propagate\<^sup>+\<^sup>+ V' W" and "conflicting W = C_True"
            | (propa_confl) V'' where "propagate\<^sup>*\<^sup>* V' V''" and "conflict V'' W"
            using tranclp_cdcl_cp_propagate_with_conflict_or_not[of V' W] bj'
            unfolding full_unfold full1_def by blast
          then show ?thesis (* too many levels of case distinction *)
          (* copy paste. copy paste, copy paste *)
            proof cases
              case V'_W
              show ?thesis
                proof cases
                  assume "conflicting V' = C_True"
                  then show ?thesis
                    using V'_W \<open>cdcl_fw_cp U V'\<close> cp_confl(1) by force
                next
                  assume confl: "conflicting V' \<noteq> C_True"
                  then have "no_step cdcl_fw_s V'"
                    by (auto simp: cdcl_fw_s.simps full1_def full_def cdcl_fw_cp.simps
                      dest!: tranclpD)
                  have "no_step cdcl_fw_cp V'"
                    using confl by (auto simp: full1_def full_def cdcl_fw_cp.simps
                    dest!: tranclpD)
                  moreover have "cdcl_fw_cp U W"
                    using V'_W \<open>cdcl_fw_cp U V'\<close> by blast
                  ultimately have "full1 cdcl_fw_cp R V'"
                    using cp_confl(1) V'_W unfolding full1_def by auto
                  then have "cdcl_fw_s R V'"
                    by auto
                  moreover have "no_step cdcl_fw_s V'"
                    using confl \<open>no_step cdcl_fw_cp V'\<close> by (auto simp: cdcl_fw_s.simps
                      full1_def dest!: tranclpD)
                  ultimately have "cdcl_fw_s\<^sup>*\<^sup>* R V'" by auto
                  show ?thesis by (metis V'_W \<open>cdcl_fw_cp U V'\<close> \<open>cdcl_fw_s\<^sup>*\<^sup>* R V'\<close>
                    conflicting_not_true_rtranclp_cdcl_fw_cp_no_step_cdcl_bj cp_confl(1)
                    rtranclp.rtrancl_into_rtrancl step.prems)
                qed
            next
              case propa
              moreover then have "cdcl_fw_cp V' W"
                by auto
              ultimately show ?thesis using \<open>cdcl_fw_cp U V'\<close> cp_confl(1) by force
            next
              case propa_confl
              moreover then have "cdcl_fw_cp\<^sup>*\<^sup>* V' V''"
                by (metis cdcl_fw_cp.propagate' rtranclp_unfold tranclp_unfold_end)
              ultimately show ?thesis
                using \<open>cdcl_fw_cp U V'\<close> cp_confl(1) by (metis rtranclp.rtrancl_into_rtrancl
                  rtranclp_trans)
            qed
        qed
    qed
qed

lemma cdcl_fw_s_cases[consumes 1, case_names fw_s_cp fw_s_decide]:
  assumes
    "cdcl_fw_s S U"
    "full1 cdcl_fw_cp S U \<Longrightarrow> P"
    "\<And>T. decide S T \<Longrightarrow> no_step cdcl_fw_cp S \<Longrightarrow> full cdcl_fw_cp T U \<Longrightarrow> P"
  shows "P"
  using assms by (auto simp: cdcl_fw_s.simps)

lemma decide_rtranclp_cdcl_s'_rtranclp_cdcl_s':
  assumes
    dec: "decide S T" and
    "cdcl_s'\<^sup>*\<^sup>* T U" and
    n_s_S: "no_step cdcl_cp S" and
    "no_step cdcl_cp U"
  shows "cdcl_s'\<^sup>*\<^sup>* S U"
  using assms(2,4)
proof induction
  case (step U V) note st =this(1) and s' = this(2) and IH = this(3) and n_s = this(4)
  consider
      (TU) "T = U"
    | (s'_st) T' where "cdcl_s' T T'" and "cdcl_s'\<^sup>*\<^sup>* T' U"
    using st[unfolded rtranclp_unfold] by (auto dest!: tranclpD)
  then show ?case
    proof cases
      case TU
      thus ?thesis
        proof -
          have "\<forall>p s sa. (\<not> p\<^sup>+\<^sup>+ (s::'st) sa \<or> (\<exists>sb. p\<^sup>*\<^sup>* s sb \<and> p sb sa))
            \<and> ((\<forall>sb. \<not> p\<^sup>*\<^sup>* s sb \<or> \<not> p sb sa) \<or> p\<^sup>+\<^sup>+ s sa)"
            by (metis tranclp_unfold_end)
          then obtain ss :: "('st \<Rightarrow> 'st \<Rightarrow> bool) \<Rightarrow> 'st \<Rightarrow> 'st \<Rightarrow> 'st" where
            f2: "\<forall>p s sa. (\<not> p\<^sup>+\<^sup>+ s sa \<or> p\<^sup>*\<^sup>* s (ss p s sa) \<and> p (ss p s sa) sa)
              \<and> ((\<forall>sb. \<not> p\<^sup>*\<^sup>* s sb \<or> \<not> p sb sa) \<or> p\<^sup>+\<^sup>+ s sa)"
            by moura
          have f3: "cdcl_s' T V"
            using TU s' by blast
          moreover
          { assume "\<not> cdcl_s' S T"
            then have "cdcl_s' S V"
              using f3 by (metis (no_types) assms(1,3) cdcl_s'.cases cdcl_s'.decide' full_unfold)
            then have "cdcl_s'\<^sup>+\<^sup>+ S V"
              by blast }
          ultimately have "cdcl_s'\<^sup>+\<^sup>+ S V"
            using f2 by (metis (full_types) rtranclp_unfold)
          then show ?thesis
            by simp
        qed
    next
      case (s'_st T') note s'_T' = this(1) and st = this(2)
      have "cdcl_s'\<^sup>*\<^sup>* S T'"
        using s'_T'
        proof cases
          case conflict'
          then have "cdcl_s' S T'"
             using dec cdcl_s'.decide' n_s_S by (simp add: full_unfold)
          then show ?thesis
             using st by auto
        next
          case (decide' T'')
          then have "cdcl_s' S T"
             using dec cdcl_s'.decide' n_s_S by (simp add: full_unfold)
          then show ?thesis using decide' s'_T' by auto
        next
          case bj'
          then have False
            using dec unfolding full1_def by (fastforce dest!: tranclpD simp: cdcl_bj.simps)
          then show ?thesis by fast
        qed
      then show ?thesis using s' st by auto
    qed
next
  case base
  then have "full cdcl_cp T T"
    by (simp add: full_unfold)
  then show ?case
    using cdcl_s'.simps dec n_s_S by auto
qed

lemma rtranclp_cdcl_fw_s_rtranclp_cdcl_s':
  assumes
    "cdcl_fw_s\<^sup>*\<^sup>* R V" and
    inv: "cdcl_all_struct_inv R"
  shows "cdcl_s'\<^sup>*\<^sup>* R V"
  using assms(1)
proof induction
  case base
  thus ?case by simp
next
  case (step S T) note st = this(1) and fw = this(2) and IH = this(3)
  have "cdcl_all_struct_inv S"
    using inv rtranclp_cdcl_all_struct_inv_inv rtranclp_cdcl_fw_s_rtranclp_cdcl st by blast
  from fw show ?case
    proof (cases rule: cdcl_fw_s_cases)
      case fw_s_cp
      thus ?thesis
        proof -
          assume a1: "full1 cdcl_fw_cp S T"
          obtain ss :: "('st \<Rightarrow> 'st \<Rightarrow> bool) \<Rightarrow> 'st \<Rightarrow> 'st" where
            f2: "\<And>p s sa pa sb sc sd pb se sf. (\<not> full1 p (s::'st) sa \<or> p\<^sup>+\<^sup>+ s sa)
              \<and> (\<not> pa (sb::'st) sc \<or> \<not> full1 pa sd sb) \<and> (\<not> pb\<^sup>+\<^sup>+ se sf \<or> pb sf (ss pb sf)
              \<or> full1 pb se sf)"
            by (metis (no_types) full1_def)
          then have f3: "cdcl_fw_cp\<^sup>+\<^sup>+ S T"
            using a1 by auto
          obtain ssa :: "('st \<Rightarrow> 'st \<Rightarrow> bool) \<Rightarrow> 'st \<Rightarrow> 'st \<Rightarrow> 'st" where
            f4: "\<And>p s sa. \<not> p\<^sup>+\<^sup>+ s sa \<or> p s (ssa p s sa)"
            by (meson tranclp_unfold_begin)
          then have f5: "\<And>s. \<not> full1 cdcl_fw_cp s S"
            using f3 f2 by (metis (full_types))
          have "\<And>s. \<not> full cdcl_fw_cp s S"
            using f4 f3 by (meson full_def)
          then have "S = R"
            using f5 by (metis (no_types) cdcl_fw_s.simps rtranclp_unfold st
              tranclp_unfold_end)
          then show ?thesis
            using f2 a1 by (metis (no_types) \<open>cdcl_all_struct_inv S\<close>
              conflicting_true_full1_cdcl_fw_cp_imp_full1_cdcl_s'_without_decode
              rtranclp_cdcl_s'_without_decide_rtranclp_cdcl_s' rtranclp_unfold)
        qed
    next
      case (fw_s_decide S') note dec = this(1) and n_S = this(2) and full = this(3)
      moreover then have "conflicting S' = C_True"
        by auto
      ultimately have "full cdcl_s'_without_decide S' T"
        by (meson \<open>cdcl_all_struct_inv S\<close> cdcl_fw_restart_cdcl fw_r_decide rtranclp_cdcl_all_struct_inv_inv
          conflicting_true_full_cdcl_fw_cp_iff_full_cdcl_s'_without_decode)
      then have a1: "cdcl_s'\<^sup>*\<^sup>* S' T"
        unfolding full_def by (metis (full_types) rtranclp_cdcl_s'_without_decide_rtranclp_cdcl_s')
      have "cdcl_fw_s\<^sup>*\<^sup>* S T"
        using fw by blast
      then have "cdcl_s'\<^sup>*\<^sup>* S T"
        using decide_rtranclp_cdcl_s'_rtranclp_cdcl_s' a1 by (metis \<open>cdcl_all_struct_inv S\<close> dec
          n_S no_step_cdcl_fw_cp_no_step_cdcl_cp rtranclp_cdcl_fw_s'_no_step_cdcl_cp_or_eq)
      then show ?thesis using IH by auto
    qed
qed

lemma rtranclp_cdcl_fw_s_distinct_mset_clauses:
  assumes invR: "cdcl_all_struct_inv R" and
  st: "cdcl_fw_s\<^sup>*\<^sup>* R S" and
  dist: "distinct_mset (clauses R)" and
  R: "trail R = []"
  shows "distinct_mset (clauses S)"
  using rtranclp_cdcl_s_distinct_mset_clauses[OF invR _ dist R]
  invR st rtranclp_mono[of cdcl_s' "cdcl_s\<^sup>*\<^sup>*"] cdcl_s'_is_rtranclp_cdcl_s
  by (auto dest!: cdcl_s'_is_rtranclp_cdcl_s rtranclp_cdcl_fw_s_rtranclp_cdcl_s')

lemma no_step_cdcl_s'_no_step_cdcl_fw_s:
  assumes
    inv: "cdcl_all_struct_inv R" and s': "no_step cdcl_s' R"
  shows "no_step cdcl_fw_s R"
proof -
  { fix ss :: 'st
    obtain ssa :: "'st \<Rightarrow> 'st \<Rightarrow> 'st" where
      ff1: "\<And>s sa. \<not> cdcl_fw_s s sa \<or> full1 cdcl_fw_cp s sa \<or> decide s (ssa s sa)"
      using cdcl_fw_s.cases by moura
    obtain ssb :: "('st \<Rightarrow> 'st \<Rightarrow> bool) \<Rightarrow> 'st \<Rightarrow> 'st \<Rightarrow> 'st" where
      ff2: "\<And>p s sa. \<not> p\<^sup>+\<^sup>+ s sa \<or> p s (ssb p s sa)"
      by (meson tranclp_unfold_begin)
    obtain ssc :: "'st \<Rightarrow> 'st" where
      ff3: "\<And>s sa sb. (\<not> cdcl_all_struct_inv s \<or> \<not> cdcl_cp s sa \<or> cdcl_s' s (ssc s))
        \<and> (\<not> cdcl_all_struct_inv s \<or> \<not> cdcl_o s sb \<or> cdcl_s' s (ssc s))"
      using n_step_cdcl_s_iff_no_step_cdcl_cl_cdcl_o by moura
    then have ff4: "\<And>s. \<not> cdcl_o R s"
      using s' inv by blast
    have ff5: "\<And>s. \<not> cdcl_cp\<^sup>+\<^sup>+ R s"
      using ff3 ff2 s' by (metis inv)
    have "\<And>s. \<not> cdcl_bj\<^sup>+\<^sup>+ R s"
      using ff4 ff2 by (metis bj)
    then have "\<And>s. \<not> cdcl_s'_without_decide R s"
      using ff5 by (simp add: cdcl_s'_without_decide.simps full1_def)
    then have "\<not> cdcl_s'_without_decide\<^sup>+\<^sup>+ R ss"
      using ff2 by blast
    then have "\<not> cdcl_fw_s R ss"
      using ff4 ff1 by (metis (full_types)  decide full1_def inv
        conflicting_true_full1_cdcl_fw_cp_imp_full1_cdcl_s'_without_decode) }
  then show ?thesis
    by fastforce
qed

lemma wf_cdcl_fw_cp:
  "wf{(T, S). cdcl_all_struct_inv S \<and> cdcl_fw_cp S T}"
  using wf_tranclp_cdcl_fw by (rule wf_subset) (auto simp: cdcl_fw_cp_tranclp_cdcl_fw)

lemma wf_cdcl_fw_s:
  "wf{(T, S). cdcl_all_struct_inv S \<and> cdcl_fw_s S T}"
  using wf_tranclp_cdcl_fw by (rule wf_subset) (auto simp add: cdcl_fw_s_tranclp_cdcl_fw)

lemma cdcl_fw_cp_obtain_normal_form:
  assumes inv: "cdcl_all_struct_inv R"
  obtains S where "full cdcl_fw_cp R S"
proof -
  obtain S where "full (\<lambda>S T. cdcl_all_struct_inv S \<and> cdcl_fw_cp S T) R S"
    using wf_exists_normal_form_full[OF wf_cdcl_fw_cp] by blast
  then have
    st: "(\<lambda>S T. cdcl_all_struct_inv S \<and> cdcl_fw_cp S T)\<^sup>*\<^sup>* R S" and
    n_s: "no_step (\<lambda>S T. cdcl_all_struct_inv S \<and> cdcl_fw_cp S T) S"
    unfolding full_def by blast+
  have "cdcl_fw_cp\<^sup>*\<^sup>* R S"
    using st by induction auto
  moreover
    have "cdcl_all_struct_inv S"
      using st inv
      apply (induction rule: rtranclp_induct)
        apply simp
      by (meson r_into_rtranclp rtranclp_cdcl_all_struct_inv_inv rtranclp_cdcl_fw_cp_rtranclp_cdcl)
    then have "no_step cdcl_fw_cp S"
      using n_s by auto
  ultimately show ?thesis
    using that unfolding full_def by blast
qed

lemma no_step_cdcl_fw_s_no_step_cdcl_s':
  assumes
    inv: "cdcl_all_struct_inv R" and
    confl: "conflicting R = C_True" and
    n_s: "no_step cdcl_fw_s R"
  shows "no_step cdcl_s' R"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then obtain S where "cdcl_s' R S" by auto
  then show False
    proof cases
      case conflict'
      then obtain S' where "full1 cdcl_fw_cp R S'"
        by (metis (full_types) cdcl_fw_cp_obtain_normal_form cdcl_s'_without_decide.simps confl
          conflicting_true_no_step_cdcl_fw_cp_no_step_s'_without_decide full_def full_unfold inv)
      then show False using n_s by blast
    next
      case (decide' R')
      then have "cdcl_all_struct_inv R'"
        using inv cdcl_all_struct_inv_inv cdcl.other cdcl_o.decide by meson
      then obtain R'' where "full cdcl_fw_cp R' R''"
        using cdcl_fw_cp_obtain_normal_form by blast
      moreover have "no_step cdcl_fw_cp R"
        by (simp add: confl local.decide'(2) no_step_cdcl_cp_no_step_cdcl_fw_restart)
      ultimately show False using n_s cdcl_fw_s.intros local.decide'(1) by blast
    next
      case (bj' R')
      then show False using confl no_step_cdcl_cp_no_step_cdcl_s'_without_decide by blast
    qed
qed

lemma rtranclp_cdcl_fw_cp_no_step_cdcl_bj:
  assumes "conflicting R = C_True" and "cdcl_fw_cp\<^sup>*\<^sup>* R S"
  shows "no_step cdcl_bj S"
  using assms conflicting_not_true_rtranclp_cdcl_fw_cp_no_step_cdcl_bj by blast

lemma rtranclp_cdcl_fw_s_no_step_cdcl_bj:
  assumes confl: "conflicting R = C_True" and "cdcl_fw_s\<^sup>*\<^sup>* R S"
  shows "no_step cdcl_bj S"
  using assms(2)
proof induction
  case base
  then show ?case
    using confl by (auto simp: cdcl_bj.simps)[]
next
  case (step S T) note st = this(1) and fw = this(2) and IH = this(3)
  have confl_S: "conflicting S = C_True"
    using fw apply cases
    by (auto simp: full1_def cdcl_fw_cp.simps dest!: tranclpD)
  from fw show ?case
    proof cases
      case fw_s_cp
      then show ?thesis
        using rtranclp_cdcl_fw_cp_no_step_cdcl_bj confl_S
        by (simp add: full1_def tranclp_into_rtranclp)
    next
      case (fw_s_decide S')
      moreover then have "conflicting S' = C_True" by auto
      ultimately show ?thesis
        using conflicting_not_true_rtranclp_cdcl_fw_cp_no_step_cdcl_bj unfolding full_def by fast
    qed
qed

lemma full_cdcl_s'_full_cdcl_fw_restart:
  assumes
    "conflicting R = C_True" and
    inv: "cdcl_all_struct_inv R"
  shows "full cdcl_s' R V \<longleftrightarrow> full cdcl_fw_s R V" (is "?s' \<longleftrightarrow> ?fw")
proof
  assume ?s'
  then have "cdcl_s'\<^sup>*\<^sup>* R V" unfolding full_def by blast
  have "cdcl_all_struct_inv V"
    using \<open>cdcl_s'\<^sup>*\<^sup>* R V\<close> inv rtranclp_cdcl_all_struct_inv_inv rtranclp_cdcl_s'_rtranclp_cdcl by blast
  then have n_s: "no_step cdcl_fw_s V"
    using no_step_cdcl_s'_no_step_cdcl_fw_s by (meson \<open>full cdcl_s' R V\<close> full_def)
  have n_s_bj: "no_step cdcl_bj V"
    by (metis \<open>cdcl_all_struct_inv V\<close> \<open>full cdcl_s' R V\<close> bj full_def
      n_step_cdcl_s_iff_no_step_cdcl_cl_cdcl_o)
  have n_s_cp: "no_step cdcl_fw_cp V"
    proof -
      { fix ss :: 'st
        obtain ssa :: "'st \<Rightarrow> 'st" where
          ff1: "\<forall>s. \<not> cdcl_all_struct_inv s \<or> cdcl_s'_without_decide s (ssa s) \<or> no_step cdcl_fw_cp s"
          using conflicting_true_no_step_s'_without_decide_no_step_cdcl_fw_cp by moura
        have "(\<forall>p s sa. \<not> full p (s::'st) sa \<or> p\<^sup>*\<^sup>* s sa \<and> no_step p sa)" and
          "(\<forall>p s sa. (\<not> p\<^sup>*\<^sup>* (s::'st) sa \<or> (\<exists>s. p sa s)) \<or> full p s sa)"
          by (meson full_def)+
        then have "\<not> cdcl_fw_cp V ss"
          using ff1 by (metis (no_types) \<open>cdcl_all_struct_inv V\<close> \<open>full cdcl_s' R V\<close> cdcl_s'.simps
            cdcl_s'_without_decide.cases) }
      then show ?thesis
        by blast
    qed
  consider
      (fw_no_confl) "cdcl_fw_s\<^sup>*\<^sup>* R V" and "conflicting V = C_True"
    | (fw_confl) "cdcl_fw_s\<^sup>*\<^sup>* R V" and "conflicting V \<noteq> C_True" and "no_step cdcl_bj V"
    | (fw_dec_confl) S T U where "cdcl_fw_s\<^sup>*\<^sup>* R S" and "no_step cdcl_fw_cp S" and
        "decide S T" and "cdcl_fw_cp\<^sup>*\<^sup>* T U" and "conflict U V"
    | (fw_dec_no_confl) S T where "cdcl_fw_s\<^sup>*\<^sup>* R S" and "no_step cdcl_fw_cp S" and
        "decide S T" and "cdcl_fw_cp\<^sup>*\<^sup>* T V" and "conflicting V = C_True"
    | (cp_no_confl) "cdcl_fw_cp\<^sup>*\<^sup>* R V" and "conflicting V = C_True"
    | (cp_confl) U where "cdcl_fw_cp\<^sup>*\<^sup>* R U" and "conflict U V"
    using rtranclp_cdcl_s'_no_step_cdcl_s'_without_decide_decomp_into_cdcl_fw[OF \<open>cdcl_s'\<^sup>*\<^sup>* R V\<close>
      assms] by auto
  then show ?fw
    proof cases
      case fw_no_confl
      then show ?thesis using n_s unfolding full_def by blast
    next
      case fw_confl
      then show ?thesis using n_s unfolding full_def by blast
    next
      case fw_dec_confl
      have "cdcl_fw_cp U V"
        using n_s_bj by (metis cdcl_fw_cp.simps full_unfold fw_dec_confl(5))
      then have "full1 cdcl_fw_cp T V"
        unfolding full1_def by (metis fw_dec_confl(4) n_s_cp tranclp_unfold_end)
      then have "cdcl_fw_s S V" using \<open>decide S T\<close> \<open>no_step cdcl_fw_cp S\<close> by auto
      thus ?thesis using n_s \<open> cdcl_fw_s\<^sup>*\<^sup>* R S\<close> unfolding full_def by auto
    next
      case fw_dec_no_confl
      then have "full cdcl_fw_cp T V"
        using n_s_cp unfolding full_def by blast
      then have "cdcl_fw_s S V" using \<open>decide S T\<close> \<open>no_step cdcl_fw_cp S\<close> by auto
      thus ?thesis using n_s \<open> cdcl_fw_s\<^sup>*\<^sup>* R S\<close> unfolding full_def by auto
    next
      case cp_no_confl
      then have "full cdcl_fw_cp R V"
        by (simp add: full_def n_s_cp)
      then have "R = V \<or> cdcl_fw_s\<^sup>+\<^sup>+ R V"
        by (metis (no_types) full_unfold fw_s_cp rtranclp_unfold tranclp_unfold_end)
      then show ?thesis
        by (simp add: full_def n_s rtranclp_unfold)
    next
      case cp_confl
      have "full cdcl_bj V V"
        using n_s_bj unfolding full_def by blast
      then have "full1 cdcl_fw_cp R V"
        unfolding full1_def by (meson cdcl_fw_cp.conflict' cp_confl(1,2) n_s_cp
          rtranclp_into_tranclp1)
      then show ?thesis using n_s unfolding full_def by auto
    qed
next
  assume ?fw
  then have "cdcl\<^sup>*\<^sup>* R V" using rtranclp_mono[of cdcl_fw_s "cdcl\<^sup>*\<^sup>*"]
    cdcl_fw_s_rtranclp_cdcl unfolding full_def by auto
  then have inv': "cdcl_all_struct_inv V" using inv rtranclp_cdcl_all_struct_inv_inv by blast
  have "cdcl_s'\<^sup>*\<^sup>* R V"
    using \<open>?fw\<close> by (simp add: full_def inv rtranclp_cdcl_fw_s_rtranclp_cdcl_s')
  moreover have "no_step cdcl_s' V"
    proof cases
      assume "conflicting V = C_True"
      then show ?thesis
        by (metis inv' \<open>full cdcl_fw_s R V\<close> full_def
          no_step_cdcl_fw_s_no_step_cdcl_s')
    next
      assume confl_V: "conflicting V \<noteq> C_True"
      then have "no_step cdcl_bj V"
      using rtranclp_cdcl_fw_s_no_step_cdcl_bj by (meson \<open>full cdcl_fw_s R V\<close>
        assms(1) full_def)
      then show ?thesis using confl_V by (fastforce simp: cdcl_s'.simps full1_def cdcl_cp.simps
        dest!: tranclpD)
    qed
  ultimately show ?s' unfolding full_def by blast
qed

lemma full_cdcl_s_full_cdcl_fw:
  assumes
    "conflicting R = C_True" and
    inv: "cdcl_all_struct_inv R"
  shows "full cdcl_s R V \<longleftrightarrow> full cdcl_fw_s R V" (is "?s' \<longleftrightarrow> ?fw")
  by (simp add: assms(1) full_cdcl_s'_full_cdcl_fw_restart full_cdcl_s_iff_full_cdcl_s' inv)

lemma full1_cdcl_fw_s_normal_forms':
  fixes S' :: "'st"
  assumes full: "full cdcl_fw_s (init_state N) S'"
  and no_d: "distinct_mset_mset N"
  shows "(conflicting S' = C_Clause {#} \<and> unsatisfiable (set_mset N))
    \<or> (conflicting S' = C_True \<and> trail S' \<Turnstile>asm N \<and> satisfiable (set_mset N))"
proof -
  have "cdcl_all_struct_inv (init_state N)"
    using no_d unfolding cdcl_all_struct_inv_def by auto
  moreover have "conflicting (init_state N) = C_True"
    by auto
  ultimately show ?thesis
    using full_cdcl_s_normal_forms' full_cdcl_s_full_cdcl_fw full no_d finite by blast
qed

end

subsection \<open>Adding Restarts\<close>
locale cdcl_cw_ops_restart =
  cdcl_cw_ops trail init_clss learned_clss backtrack_lvl conflicting cons_trail tl_trail
   add_init_cls
   add_learned_cls remove_cls update_backtrack_lvl update_conflicting init_state
   restart_state
  for
    trail :: "'st \<Rightarrow> ('v::linorder, nat, 'v clause) marked_lits" and
    init_clss :: "'st \<Rightarrow> 'v clauses" and
    learned_clss :: "'st \<Rightarrow> 'v clauses" and
    backtrack_lvl :: "'st \<Rightarrow> nat" and
    conflicting :: "'st \<Rightarrow>'v clause conflicting_clause" and

    cons_trail :: "('v, nat, 'v clause) marked_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    tl_trail :: "'st \<Rightarrow> 'st" and
    add_init_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    add_learned_cls remove_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_backtrack_lvl :: "nat \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_conflicting :: "'v clause conflicting_clause \<Rightarrow> 'st \<Rightarrow> 'st" and

    init_state :: "'v::linorder clauses \<Rightarrow> 'st" and
    restart_state :: "'st \<Rightarrow> 'st" +
  fixes f :: "nat \<Rightarrow> nat"
  assumes f: "strict_mono f"
begin

text \<open>The condition of the differences of cardinality has to be strict.
  Otherwise, you could be in a strange state, where nothing remains to do, but a restart is done.
  See the proof of well-foundedness.\<close>
inductive cdcl_with_restart\<^sub>C\<^sub>W where
restart_step: "(cdcl_fw_s^^(card (set_mset (learned_clss T)) - card (set_mset (learned_clss S)))) S T
  \<Longrightarrow> card (set_mset (learned_clss T)) - card (set_mset (learned_clss S)) > f n
  \<Longrightarrow> restart T U \<Longrightarrow> cdcl_with_restart\<^sub>C\<^sub>W (S, n) (U, Suc n)" |
restart_full: "full1 cdcl_fw_s S T \<Longrightarrow> cdcl_with_restart\<^sub>C\<^sub>W (S, n) (T, Suc n)"

lemma "cdcl_with_restart\<^sub>C\<^sub>W S T \<Longrightarrow> cdcl_fw_restart\<^sup>*\<^sup>* (fst S) (fst T)"
  by (induction rule: cdcl_with_restart\<^sub>C\<^sub>W.induct)
  (auto dest!: relpowp_imp_rtranclp cdcl_fw_s_tranclp_cdcl_fw tranclp_into_rtranclp
     rtranclp_cdcl_fw_s_rtranclp_cdcl_fw rtranclp_cdcl_fw_tranclp_cdcl_fw_restart fw_r_rf
     cdcl_rf.restart
    simp: full1_def)

lemma cdcl_with_restart\<^sub>C\<^sub>W_rtranclp_cdcl:
  "cdcl_with_restart\<^sub>C\<^sub>W S T \<Longrightarrow> cdcl\<^sup>*\<^sup>* (fst S) (fst T)"
  by (induction rule: cdcl_with_restart\<^sub>C\<^sub>W.induct)
  (auto dest!: relpowp_imp_rtranclp rtranclp_cdcl_fw_s_rtranclp_cdcl cdcl.rf cdcl_rf.restart
      tranclp_into_rtranclp simp: full1_def)

lemma cdcl_with_restart\<^sub>C\<^sub>W_increasing_number:
  "cdcl_with_restart\<^sub>C\<^sub>W S T \<Longrightarrow> snd T = 1 + snd S"
  by (induction rule: cdcl_with_restart\<^sub>C\<^sub>W.induct) auto

lemma "full1 cdcl_fw_s S T \<Longrightarrow> cdcl_with_restart\<^sub>C\<^sub>W (S, n) (T, Suc n)"
  using restart_full by blast

lemma cdcl_all_struct_inv_learned_clss_bound:
  assumes inv: "cdcl_all_struct_inv S"
  shows "set_mset (learned_clss S) \<subseteq> build_all_simple_clss (atms_of_mu (init_clss S))"
proof
  fix C
  assume C: "C \<in> set_mset (learned_clss S)"
  have "distinct_mset C"
    using C inv unfolding cdcl_all_struct_inv_def distinct_cdcl_state_def distinct_mset_set_def by auto
  moreover have "\<not>tautology C"
    using C inv unfolding cdcl_all_struct_inv_def cdcl_learned_clause_def by auto
  moreover
    have "atms_of C \<subseteq> atms_of_mu (learned_clss S)"
      using C by auto
    then have "atms_of C \<subseteq> atms_of_mu (init_clss S)"
    using inv  unfolding cdcl_all_struct_inv_def no_strange_atm_def by force
  moreover have "finite (atms_of_mu (init_clss S))"
    using inv unfolding cdcl_all_struct_inv_def by auto
  ultimately show "C \<in> build_all_simple_clss (atms_of_mu (init_clss S))"
    using distinct_mset_not_tautology_implies_in_build_all_simple_clss build_all_simple_clss_mono
    by blast
qed

lemma strict_mono_ge_id: "strict_mono (g::nat \<Rightarrow> nat) \<Longrightarrow> g n \<ge> n"
  unfolding strict_mono_def apply (induction n, simp)
  by (metis Suc_leI diff_diff_cancel lessI less_imp_diff_less)

lemma strict_mono_local_prop:
  assumes "\<And>i::nat. g (Suc i) > g i"
  shows "strict_mono g"
  unfolding strict_mono_def
proof (intro allI impI)
  fix x y::nat
  assume "x < y"
  then show "g x < g y"
    proof (induction "y -x" arbitrary: x y)
      case 0
      then show ?case by simp
    next
      case (Suc n) note IH = this(1) and n = this(2)
      consider
          (eq) "y = Suc x"
        | (less) y' where "y = Suc y'" and "y' > x"
        using \<open>x < y\<close> Suc_le_D unfolding less_eq_Suc_le by fastforce
      then show ?case
        proof cases
          case eq
          then show ?thesis using assms by simp
        next
          case less
          then have "g x < g y'" using IH[of y' x] n by auto
          then show ?thesis using assms[of y' ] less by auto
        qed
    qed
qed

lemma cdcl_with_restart\<^sub>C\<^sub>W_init_clss:
  "cdcl_with_restart\<^sub>C\<^sub>W S T \<Longrightarrow> init_clss (fst S) = init_clss (fst T)"
  using cdcl_with_restart\<^sub>C\<^sub>W_rtranclp_cdcl rtranclp_cdcl_init_clss by blast

lemma
  "wf {(T, S). cdcl_all_struct_inv (fst S) \<and> cdcl_with_restart\<^sub>C\<^sub>W S T}"
proof (rule ccontr)
  assume "\<not> ?thesis"
    then obtain g where
    g: "\<And>i. cdcl_with_restart\<^sub>C\<^sub>W (g i) (g (Suc i))" and
    inv: "\<And>i. cdcl_all_struct_inv (fst (g i))"
    unfolding wf_iff_no_infinite_down_chain by fast
  { fix i
    have "init_clss (fst (g i)) = init_clss (fst (g 0))"
      apply (induction i)
        apply simp
      using g by (metis cdcl_with_restart\<^sub>C\<^sub>W_init_clss)
    } note init_g = this
  let ?S = "g 0"
  have "finite (atms_of_mu (init_clss (fst ?S)))"
    using inv unfolding cdcl_all_struct_inv_def by auto
  have "\<And>i. snd (g i) < snd (g (i+1))"
    by (metis Suc_eq_plus1 Suc_le_lessD add.commute cdcl_with_restart\<^sub>C\<^sub>W_increasing_number g
      less_or_eq_imp_le)
  then have "strict_mono (snd o g)"
    using strict_mono_local_prop[of "snd o g"] by auto
  then obtain j where j:"snd (g j) > card (build_all_simple_clss (atms_of_mu (init_clss (fst ?S))))"
    using strict_mono_ge_id[of "snd \<circ> g" "1+card (build_all_simple_clss (atms_of_mu (init_clss
      (fst ?S))))"] Suc_le_lessD
    by fastforce
  text \<open>The following does not hold anymore with the non-strict version of
    cardinality in the definition.\<close>
  { fix i
    assume "no_step cdcl_fw_s (fst (g i))"
    with g[of i]
    have False
      proof (induction rule: cdcl_with_restart\<^sub>C\<^sub>W.induct)
        case (restart_step T S n) note H = this(1) and c = this(2) and n_s = this(4)
        obtain S' where "cdcl_fw_s S S'"
          using H c by (metis gr_implies_not0 relpowp_E2)
        then show False using n_s by auto
      next
        case (restart_full S T)
        then show False unfolding full1_def by (auto dest: tranclpD)
      qed
    } note H = this
  obtain m T where
    m: "m = card (set_mset (learned_clss T)) - card (set_mset (learned_clss (fst (g j))))" and
    "m > f (snd (g j))" and
    "restart T (fst (g (j+1)))" and
    cdcl_fw_s: "(cdcl_fw_s ^^ m) (fst (g j)) T"
    using g[of j] H[of "Suc j"] by (force simp: cdcl_with_restart\<^sub>C\<^sub>W.simps full1_def)
  have "cdcl_fw_s\<^sup>*\<^sup>* (fst (g j)) T"
    using cdcl_fw_s relpowp_imp_rtranclp by metis
  then have "cdcl_all_struct_inv T"
    using inv[of j]  rtranclp_cdcl_all_struct_inv_inv rtranclp_cdcl_fw_s_rtranclp_cdcl by blast
  moreover have "card (set_mset (learned_clss T)) - card (set_mset (learned_clss (fst (g j))))
      > card (build_all_simple_clss (atms_of_mu (init_clss (fst ?S))))"
    by (smt Suc_leI \<open>f (snd (g j)) < m\<close> dual_order.trans f j le_less_linear less_imp_le m
      not_less_eq_eq strict_mono_ge_id)
    then have "card (set_mset (learned_clss T))
      > card (build_all_simple_clss (atms_of_mu (init_clss (fst ?S))))"
      by linarith
  moreover
    have "init_clss (fst (g j)) = init_clss T"
      using \<open>cdcl_fw_s\<^sup>*\<^sup>* (fst (g j)) T\<close> rtranclp_cdcl_fw_s_rtranclp_cdcl rtranclp_cdcl_init_clss
      by blast
    then have "init_clss (fst ?S) = init_clss T"
      using init_g[of j] by auto
  ultimately show False
    using cdcl_all_struct_inv_learned_clss_bound by (metis Suc_leI card_mono not_less_eq_eq
      build_all_simple_clss_finite)
qed

lemma cdcl_with_restart\<^sub>C\<^sub>W_distinct_mset_clauses:
  assumes invR: "cdcl_all_struct_inv (fst R)" and
  st: "cdcl_with_restart\<^sub>C\<^sub>W R S" and
  dist: "distinct_mset (clauses (fst R))" and
  R: "trail (fst R) = []"
  shows "distinct_mset (clauses (fst S))"
  using assms(2,1,3,4)
proof (induction)
  case (restart_full S T)
  then show ?case using rtranclp_cdcl_fw_s_distinct_mset_clauses[of S T] unfolding full1_def
    by (auto dest: tranclp_into_rtranclp)
next
  case (restart_step T S n U)
  then have "distinct_mset (clauses T)" using rtranclp_cdcl_fw_s_distinct_mset_clauses[of S T]
    unfolding full1_def by (auto dest: relpowp_imp_rtranclp)
  then show ?case using \<open>restart T U\<close> by (metis clauses_restart distinct_mset_union fstI
    mset_le_exists_conv restart.cases state_eq_clauses)
qed

end

section \<open>Incremental SAT solving\<close>
text \<open>This is a just a very little start\<close>
context cdcl_cw_ops
begin

text \<open>This invariant holds all the invariant related to the strategy. See the structural invariant
    in @{term cdcl_all_struct_inv}\<close>
definition cdcl_s_invariant where
"cdcl_s_invariant S \<longleftrightarrow>
  conflict_is_false_with_level S
  \<and> no_clause_is_false S
  \<and> no_smaller_confl S
  \<and> no_clause_is_false S"

lemma cdcl_s_cdcl_s_invariant:
  assumes
   cdcl: "cdcl_s S T" and
   inv_s: "cdcl_s_invariant S" and
   inv: "cdcl_all_struct_inv S"
  shows
    "cdcl_s_invariant T"
  unfolding cdcl_s_invariant_def cdcl_all_struct_inv_def apply standard
    apply (rule cdcl_s_ex_lit_of_max_level[of S])
    using assms unfolding cdcl_s_invariant_def cdcl_all_struct_inv_def apply auto[7]
  apply standard
    using cdcl cdcl_s_not_non_negated_init_clss apply blast
  apply standard
   apply (rule cdcl_s_no_smaller_confl_inv)
   using assms unfolding cdcl_s_invariant_def cdcl_all_struct_inv_def apply auto[4]
  using cdcl cdcl_s_not_non_negated_init_clss by auto

lemma rtranclp_cdcl_s_cdcl_s_invariant:
  assumes
   cdcl: "cdcl_s\<^sup>*\<^sup>* S T" and
   inv_s: "cdcl_s_invariant S" and
   inv: "cdcl_all_struct_inv S"
  shows
    "cdcl_s_invariant T"
  using assms apply (induction)
    apply simp
  using cdcl_s_cdcl_s_invariant rtranclp_cdcl_all_struct_inv_inv rtranclp_cdcl_s_rtranclp_cdcl
  by blast

lemma rtranclp_cdcl_s'_cdcl_s_invariant:
  assumes
   cdcl: "cdcl_s'\<^sup>*\<^sup>* S T" and
   inv_s: "cdcl_s_invariant S" and
   inv: "cdcl_all_struct_inv S"
  shows
    "cdcl_s_invariant T"
  using cdcl_s'_is_rtranclp_cdcl_s rtranclp_mono[of cdcl_s' "cdcl_s\<^sup>*\<^sup>*"] inv_s inv
    rtranclp_cdcl_s_cdcl_s_invariant cdcl by force

lemma rtranclp_cdcl_s'_cdcl_all_struct_inv:
  assumes
   cdcl: "cdcl_s'\<^sup>*\<^sup>* S T" and
   inv_s: "cdcl_s_invariant S" and
   inv: "cdcl_all_struct_inv S"
  shows
    "cdcl_all_struct_inv T"

  using cdcl_s'_is_rtranclp_cdcl_s rtranclp_mono[of cdcl_s' "cdcl_s\<^sup>*\<^sup>*"] inv_s inv
     cdcl rtranclp_cdcl_all_struct_inv_inv rtranclp_cdcl_s'_rtranclp_cdcl by blast

lemma rtranclp_cdcl_fw_s_cdcl_s_invariant:
  assumes
   cdcl: "cdcl_fw_s\<^sup>*\<^sup>* S T" and
   inv_s: "cdcl_s_invariant S" and
   inv: "cdcl_all_struct_inv S"
  shows
    "cdcl_s_invariant T"
  using rtranclp_cdcl_fw_s_rtranclp_cdcl_s'[OF cdcl] rtranclp_cdcl_s'_cdcl_s_invariant[of S T]
  assms(2,3) by (blast dest: tranclp_into_rtranclp)

lemma rtranclp_cdcl_fw_s_cdcl_all_struct_inv:
  assumes
   cdcl: "cdcl_fw_s\<^sup>*\<^sup>* S T" and
   inv_s: "cdcl_s_invariant S" and
   inv: "cdcl_all_struct_inv S"
  shows
    "cdcl_all_struct_inv T"
  using rtranclp_cdcl_fw_s_rtranclp_cdcl_s'[OF cdcl] rtranclp_cdcl_s'_cdcl_all_struct_inv[of S T]
  assms(2,3) by (blast dest: tranclp_into_rtranclp)

abbreviation decr_bt_lvl where
"decr_bt_lvl S \<equiv> update_backtrack_lvl (backtrack_lvl S - 1) S"

text \<open>When we add a new clause, we reduce the trail until we get to tho first literal included in C.
  Then we can mark the conflict.\<close>
fun cut_trail_wrt_clause where
"cut_trail_wrt_clause C [] S = S" |
"cut_trail_wrt_clause C (Marked L _ # M) S =
  (if -L \<in># C then S
    else cut_trail_wrt_clause C M (decr_bt_lvl (tl_trail S)))" |
"cut_trail_wrt_clause C (Propagated L _ # M) S =
  (if -L \<in># C then S
    else cut_trail_wrt_clause C M (tl_trail S))"

(* TODO missing backtrack update *)
definition add_new_clause_and_update :: "'v literal multiset \<Rightarrow> 'st \<Rightarrow> 'st" where
"add_new_clause_and_update C S =
  (if trail S \<Turnstile>as CNot C
  then update_conflicting (C_Clause C) (add_init_cls C (cut_trail_wrt_clause C (trail S) S))
  else add_init_cls C S)"

thm cut_trail_wrt_clause.induct
lemma init_clss_cut_trail_wrt_clause[simp]:
  "init_clss (cut_trail_wrt_clause C M S) = init_clss S"
  by (induction rule: cut_trail_wrt_clause.induct) auto

lemma learned_clss_cut_trail_wrt_clause[simp]:
  "learned_clss (cut_trail_wrt_clause C M S) = learned_clss S"
  by (induction rule: cut_trail_wrt_clause.induct) auto

lemma conflicting_clss_cut_trail_wrt_clause[simp]:
  "conflicting (cut_trail_wrt_clause C M S) = conflicting S"
  by (induction rule: cut_trail_wrt_clause.induct) auto

 thm cut_trail_wrt_clause.induct
lemma trail_cut_trail_wrt_clause:
  "\<exists>M.  trail S = M @ trail (cut_trail_wrt_clause C (trail S) S)"
proof (induction "trail S" arbitrary:S rule: marked_lit_list_induct)
  case nil
  then show ?case by simp
next
  case (marked L l M) note IH = this(1)[of "decr_bt_lvl (tl_trail S)"] and M = this(2)[symmetric]
  then show ?case using Cons_eq_appendI by fastforce+
next
  case (proped L l M) note IH = this(1)[of " (tl_trail S)"] and M = this(2)[symmetric]
  then show ?case using Cons_eq_appendI by fastforce+
qed

lemma cut_trail_wrt_clause_backtrack_lvl_length_marked:
  assumes
     "backtrack_lvl T = length (get_all_levels_of_marked (trail T))"
  shows
  "backtrack_lvl (cut_trail_wrt_clause C (trail T) T) =
     length (get_all_levels_of_marked (trail (cut_trail_wrt_clause C (trail T) T)))"
  using assms
proof (induction "trail T" arbitrary:T rule: marked_lit_list_induct)
  case nil
  then show ?case by simp
next
  case (marked L l M) note IH = this(1)[of "decr_bt_lvl (tl_trail T)"] and M = this(2)[symmetric]
    and bt = this(3)
  then show ?case by auto
next
  case (proped L l M) note IH = this(1)[of "tl_trail T"] and M = this(2)[symmetric] and bt = this(3)
  then show ?case by auto
qed

lemma cut_trail_wrt_clause_get_all_levels_of_marked:
  assumes "get_all_levels_of_marked (trail T) = rev [Suc 0..<
    Suc (length (get_all_levels_of_marked (trail T)))]"
  shows
    "get_all_levels_of_marked (trail ((cut_trail_wrt_clause C (trail T) T))) = rev [Suc 0..<
    Suc (length (get_all_levels_of_marked (trail  ((cut_trail_wrt_clause C (trail T) T)))))]"
  using assms
proof (induction "trail T" arbitrary:T rule: marked_lit_list_induct)
  case nil
  then show ?case by simp
next
  case (marked L l M) note IH = this(1)[of "decr_bt_lvl (tl_trail T)"] and M = this(2)[symmetric]
    and bt = this(3)
  then show ?case by (cases "count C L = 0") auto
next
  case (proped L l M) note IH = this(1)[of "tl_trail T"] and M = this(2)[symmetric] and bt = this(3)
  then show ?case by (cases "count C L = 0") auto
qed

lemma cut_trail_wrt_clause_CNot_trail:
  assumes "trail T \<Turnstile>as CNot C"
  shows
    "(trail ((cut_trail_wrt_clause C (trail T) T))) \<Turnstile>as CNot C"
  using assms
proof (induction "trail T" arbitrary:T rule: marked_lit_list_induct)
  case nil
  then show ?case by simp
next
  case (marked L l M) note IH = this(1)[of "decr_bt_lvl (tl_trail T)"] and M = this(2)[symmetric]
    and bt = this(3)
    (* TODO less ugly proof *)
  then show ?case apply (cases "count C (-L) = 0")
    apply (auto simp: true_annots_true_cls)
    by (smt CNot_def One_nat_def count_single diff_Suc_1 in_CNot_uminus less_numeral_extra(4)
     marked.prems marked_lit.sel(1) mem_Collect_eq true_annot_def true_annot_lit_of_notin_skip
     true_annots_def true_clss_def zero_less_diff)
next
  case (proped L l M) note IH = this(1)[of "tl_trail T"] and M = this(2)[symmetric] and bt = this(3)
  then show ?case
    (* TODO ugly proof *)
    apply (cases "count C (-L) = 0")
    apply (auto simp: true_annots_true_cls)
    by (smt CNot_def One_nat_def count_single diff_Suc_1 in_CNot_uminus less_numeral_extra(4)
     proped.prems marked_lit.sel(2) mem_Collect_eq true_annot_def true_annot_lit_of_notin_skip
     true_annots_def true_clss_def zero_less_diff)
qed

lemma cut_trail_wrt_clause_hd_trail_in_or_empty_trail:
  "((\<forall>L \<in>#C. -L \<notin> lits_of (trail T)) \<and> trail (cut_trail_wrt_clause C (trail T) T) = [])
    \<or> (-lit_of (hd (trail (cut_trail_wrt_clause C (trail T) T))) \<in># C
       \<and> length (trail (cut_trail_wrt_clause C (trail T) T)) \<ge> 1)"
  using assms
proof (induction "trail T" arbitrary:T rule: marked_lit_list_induct)
  case nil
  then show ?case by simp
next
  case (marked L l M) note IH = this(1)[of "decr_bt_lvl (tl_trail T)"] and M = this(2)[symmetric]
  then show ?case by simp force
next
  case (proped L l M) note IH = this(1)[of "tl_trail T"] and M = this(2)[symmetric]
  then show ?case by simp force
qed

text \<open>We can fully run @{term cdcl_s} or add a clause. Remark that we use @{term cdcl_s} to avoid 
an explicit @{term skip}, @{term resolve}, and @{term backtrack} normalisation. to get rid of the
conflict @{term S} if necessary.\<close>
inductive incremental_cdcl :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S where
add_confl:
  "trail S \<Turnstile>asm init_clss S \<Longrightarrow> distinct_mset C \<Longrightarrow> conflicting S = C_True \<Longrightarrow>
    trail S \<Turnstile>as CNot C \<Longrightarrow> 
    full cdcl_s 
      (update_conflicting (C_Clause C) (add_init_cls C (cut_trail_wrt_clause C (trail S) S))) T \<Longrightarrow> 
    incremental_cdcl S T" |
add_no_confl:
  "trail S \<Turnstile>asm init_clss S \<Longrightarrow> distinct_mset C \<Longrightarrow> conflicting S = C_True \<Longrightarrow> \<not>trail S \<Turnstile>as CNot C
    \<Longrightarrow> incremental_cdcl S (add_init_cls C S)"

inductive add_learned_clss :: "'st \<Rightarrow> 'v clauses \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
add_learned_clss_nil: "add_learned_clss S {#} S" |
add_learned_clss_plus:
  "add_learned_clss S A T \<Longrightarrow> add_learned_clss S ({#x#} + A) (add_learned_cls x T)"
declare add_learned_clss.intros[intro]

lemma Ex_add_learned_clss:
  "\<exists>T. add_learned_clss S A T"
  by (induction A arbitrary: S rule: multiset_induct) (auto simp: union_commute[of _ "{#_#}"])

lemma add_learned_clss_learned_clss:
  assumes "add_learned_clss S U T"
  shows "learned_clss T = U + learned_clss S"
  using assms by (induction rule: add_learned_clss.induct) (simp_all add: ac_simps)

lemma add_learned_clss_trail:
  assumes "add_learned_clss S U T"
  shows "trail T = trail S"
  using assms by (induction rule: add_learned_clss.induct) (simp_all add: ac_simps)

lemma add_learned_clss_init_clss:
  assumes "add_learned_clss S U T"
  shows "init_clss T = init_clss S"
  using assms by (induction rule: add_learned_clss.induct) (simp_all add: ac_simps)

lemma add_learned_clss_conflicting:
  assumes "add_learned_clss S U T"
  shows "conflicting T = conflicting S"
  using assms by (induction rule: add_learned_clss.induct) (simp_all add: ac_simps)

lemma add_learned_clss_backtrack_lvl:
  assumes "add_learned_clss S U T"
  shows "backtrack_lvl T = backtrack_lvl S"
  using assms by (induction rule: add_learned_clss.induct) (simp_all add: ac_simps)

lemma add_learned_clss_init_state_mempty[dest!]:
  "add_learned_clss (init_state N) {#} T \<Longrightarrow> T = init_state N"
  by (cases rule: add_learned_clss.cases) (auto simp: add_learned_clss.cases)

text \<open>For multiset larger that 1 element, there is no way to know in which order the clauses are
  added. But contrary to a definition @{term fold_mset}, there is an element.\<close>
lemma add_learned_clss_init_state_single[dest!]:
  "add_learned_clss (init_state N) {#C#} T \<Longrightarrow> T = add_learned_cls C (init_state N)"
  by (induction  "{#C#}" "T" rule: add_learned_clss.induct)
  (auto simp: add_learned_clss.cases ac_simps union_is_single split: split_if_asm)

thm rtranclp_cdcl_s_no_smaller_confl_inv cdcl_s_normal_forms
lemma cdcl_all_struct_inv_add_new_clause_and_update_cdcl_all_struct_inv:
  assumes
    inv_T: "cdcl_all_struct_inv T" and
    tr_T_N[simp]: "trail T \<Turnstile>asm N" and
    tr_C[simp]: "trail T \<Turnstile>as CNot C" and
    [simp]: "distinct_mset C"
  shows "cdcl_all_struct_inv (add_new_clause_and_update C T)" (is "cdcl_all_struct_inv ?T'")
proof -
  let ?T = "update_conflicting (C_Clause C) (add_init_cls C (cut_trail_wrt_clause C (trail T) T))"
  obtain M where
    M: "trail T = M @ trail (cut_trail_wrt_clause C (trail T) T)"
      using trail_cut_trail_wrt_clause[of T C] by blast
  have H[dest]: "\<And>x. x \<in> lits_of (trail (cut_trail_wrt_clause C (trail T) T)) \<Longrightarrow>
    x \<in> lits_of (trail T)"
    using inv_T arg_cong[OF M, of lits_of] by auto
  have H'[dest]: "\<And>x. x \<in> set (trail (cut_trail_wrt_clause C (trail T) T)) \<Longrightarrow> x \<in> set (trail T)"
    using inv_T arg_cong[OF M, of set] by auto

  have H_proped:"\<And>x. x \<in> set (get_all_mark_of_propagated (trail (cut_trail_wrt_clause C (trail T)
    T))) \<Longrightarrow> x \<in> set (get_all_mark_of_propagated (trail T))"
  using inv_T arg_cong[OF M, of get_all_mark_of_propagated] by auto

  have [simp]: "no_strange_atm ?T"
    using inv_T unfolding cdcl_all_struct_inv_def no_strange_atm_def add_new_clause_and_update_def
    by (auto dest!: H H')

  have M_lev: "cdcl_M_level_inv T"
    using inv_T unfolding cdcl_all_struct_inv_def by blast
  then have "no_dup (M @ trail (cut_trail_wrt_clause C (trail T) T))"
    unfolding cdcl_M_level_inv_def unfolding M[symmetric] by auto
  then have [simp]: "no_dup (trail (cut_trail_wrt_clause C (trail T) T))"
    by auto

  have "consistent_interp (lits_of (M @ trail (cut_trail_wrt_clause C (trail T) T)))"
    using M_lev unfolding cdcl_M_level_inv_def unfolding M[symmetric] by auto
  then have [simp]: "consistent_interp (lits_of (trail (cut_trail_wrt_clause C (trail T) T)))"
    unfolding consistent_interp_def by auto

  have [simp]: "cdcl_M_level_inv ?T"
    unfolding cdcl_M_level_inv_def apply (auto dest: H H'
      simp: M_lev cdcl_M_level_inv_decomp(3) cut_trail_wrt_clause_backtrack_lvl_length_marked)
    using M_lev cut_trail_wrt_clause_get_all_levels_of_marked by (subst arg_cong[OF M]) auto

  have [simp]: "\<And>s. s \<in># learned_clss T \<Longrightarrow> \<not>tautology s"
    using inv_T unfolding cdcl_all_struct_inv_def by auto

  have "distinct_cdcl_state T"
    using inv_T unfolding cdcl_all_struct_inv_def by auto
  then have [simp]: "distinct_cdcl_state ?T"
    unfolding distinct_cdcl_state_def by auto

  have  "cdcl_conflicting T"
    using inv_T unfolding cdcl_all_struct_inv_def by auto
  have "trail ?T \<Turnstile>as CNot C"
     by (simp add: cut_trail_wrt_clause_CNot_trail)
  then have [simp]: "cdcl_conflicting ?T"
    unfolding cdcl_conflicting_def apply simp
    by (metis M \<open>cdcl_conflicting T\<close> append_assoc cdcl_conflicting_decomp(2))

  have decomp_T: "all_decomposition_implies_m (init_clss T) (get_all_marked_decomposition (trail T))"
    using inv_T unfolding cdcl_all_struct_inv_def by auto
  have  "all_decomposition_implies_m  (init_clss ?T)
    (get_all_marked_decomposition (trail ?T))"
    unfolding all_decomposition_implies_def
    proof clarify
      fix a b
      assume "(a, b) \<in> set (get_all_marked_decomposition (trail ?T))"
      from in_get_all_marked_decomposition_in_get_all_marked_decomposition_prepend[OF this]
      obtain b' where
        "(a, b' @ b) \<in>  set (get_all_marked_decomposition (trail T))"
        using M (* TODO tune *) by simp metis
      then have "(\<lambda>a. {#lit_of a#}) ` set a \<union> set_mset (init_clss ?T)
        \<Turnstile>ps (\<lambda>a. {#lit_of a#}) ` set (b @ b')"
        using decomp_T unfolding all_decomposition_implies_def
        (* TODO Tune *)
        apply auto
        by (metis (no_types, lifting) case_prodD set_append sup.commute true_clss_clss_insert_l)

      then show "(\<lambda>a. {#lit_of a#}) ` set a \<union> set_mset (init_clss ?T)
        \<Turnstile>ps (\<lambda>a. {#lit_of a#}) ` set b"
        by (auto simp: image_Un)
    qed

  have [simp]: "cdcl_learned_clause ?T"
    using inv_T unfolding cdcl_all_struct_inv_def cdcl_learned_clause_def
    by (auto dest!: H_proped simp: clauses_def)
  show ?thesis
    using \<open>all_decomposition_implies_m  (init_clss ?T)
    (get_all_marked_decomposition (trail ?T))\<close>
    unfolding cdcl_all_struct_inv_def by (auto simp: add_new_clause_and_update_def)
qed

lemma cdcl_all_struct_inv_add_new_clause_and_update_cdcl_s_inv:
  assumes
    inv_s: "cdcl_s_invariant T" and
    inv: "cdcl_all_struct_inv T" and
    tr_T_N[simp]: "trail T \<Turnstile>asm N" and
    tr_C[simp]: "trail T \<Turnstile>as CNot C" and
    [simp]: "distinct_mset C"
  shows "cdcl_s_invariant (add_new_clause_and_update C T)" (is "cdcl_s_invariant ?T'")
proof -
  have "cdcl_all_struct_inv ?T'"
    using cdcl_all_struct_inv_add_new_clause_and_update_cdcl_all_struct_inv assms by blast
  have "trail (add_new_clause_and_update C T) \<Turnstile>as CNot C"
    by (simp add: add_new_clause_and_update_def cut_trail_wrt_clause_CNot_trail)
  obtain MT where
    MT: "trail T = MT @  trail (cut_trail_wrt_clause C (trail T) T)"
    using trail_cut_trail_wrt_clause by blast
  consider
      (false) "\<forall>L\<in>#C. - L \<notin> lits_of (trail T)" and "trail (cut_trail_wrt_clause C (trail T) T) = []"
    | (not_false) "- lit_of (hd (trail (cut_trail_wrt_clause C (trail T) T))) \<in># C" and
      "1 \<le> length (trail (cut_trail_wrt_clause C (trail T) T))"
    using cut_trail_wrt_clause_hd_trail_in_or_empty_trail[of C T] by auto
  then show ?thesis
    proof cases
      case false note C = this(1) and empty_tr = this(2)
      then have [simp]: "C = {#}"
        by (simp add: in_CNot_implies_uminus(2) multiset_eqI)
      show ?thesis
        using empty_tr unfolding cdcl_s_invariant_def no_smaller_confl_def
        cdcl_all_struct_inv_def by (auto simp: add_new_clause_and_update_def)
    next
      case not_false note C = this(1) and l = this(2)
      let ?L = "- lit_of (hd (trail (cut_trail_wrt_clause C (trail T) T)))"
      have L: "get_level ?L (trail (cut_trail_wrt_clause C (trail T) T))
        = backtrack_lvl (cut_trail_wrt_clause C (trail T) T)"
        using l apply (cases "trail (cut_trail_wrt_clause C (trail T) T)")
        apply auto
       sorry

      have [simp]: "no_smaller_confl (update_conflicting (C_Clause C)
        (add_init_cls C (cut_trail_wrt_clause C (trail T) T)))"
        unfolding no_smaller_confl_def
      proof (clarify, goal_cases)
        case (1 M K i M' D)
        then consider
            (DC) "D = C"
          | (D_T) "D \<in># clauses T"
          by (auto simp: clauses_def split: split_if_asm)
        then show False
          proof cases
            case D_T
            have "no_smaller_confl T"
              using inv_s unfolding cdcl_s_invariant_def by auto
            have "(MT @ M') @ Marked K i # M = trail T "
              using MT 1(1) by auto
            thus False using D_T \<open>no_smaller_confl T\<close> 1(3) unfolding no_smaller_confl_def by blast
          next
            case DC note _[simp] = this
            then have "atm_of (-?L) \<in> atm_of ` (lits_of M)"
              using 1(3) C in_CNot_implies_uminus(2) by blast
            moreover
              have "lit_of (hd (M' @ Marked K i # [])) = -?L"
                using l 1(1)[symmetric] by (cases "trail (cut_trail_wrt_clause C (trail T) T)")
                (auto dest!: arg_cong[of "_ # _" _ hd] simp: hd_append)
              from arg_cong[OF this, of atm_of]
              have "atm_of (-?L) \<in> atm_of ` (lits_of (M' @ Marked K i # []))"
                by (cases " (M' @ Marked K i # [])") auto
            moreover have "no_dup (trail (cut_trail_wrt_clause C (trail T) T))"
              using \<open>cdcl_all_struct_inv ?T'\<close> unfolding cdcl_all_struct_inv_def cdcl_M_level_inv_def
              by (auto simp: add_new_clause_and_update_def)
            ultimately show False
              unfolding 1(1)[symmetric, simplified]
              apply auto
              using Marked_Propagated_in_iff_in_lits_of defined_lit_map apply blast
              by (metis IntI Marked_Propagated_in_iff_in_lits_of defined_lit_map empty_iff)
        qed
      qed
      show ?thesis using L C 
        unfolding cdcl_s_invariant_def
        unfolding cdcl_all_struct_inv_def by (auto simp: add_new_clause_and_update_def)
    qed
qed

lemma full_cdcl_s_inv_normal_form:
  assumes
    full: "full cdcl_s S T" and
    inv_s: "cdcl_s_invariant S" and
    inv: "cdcl_all_struct_inv S"
  shows "conflicting T = C_Clause {#} \<and> unsatisfiable (set_mset (init_clss S)) 
    \<or> conflicting T = C_True \<and> trail T \<Turnstile>asm init_clss S \<and> satisfiable (set_mset (init_clss S))"
proof -
  have "no_step cdcl_s T" 
    using full unfolding full_def by blast
  moreover have "cdcl_all_struct_inv T" and inv_s: "cdcl_s_invariant T"
    apply (metis cdcl_cw_ops.rtranclp_cdcl_s_rtranclp_cdcl cdcl_cw_ops_axioms full full_def inv 
      rtranclp_cdcl_all_struct_inv_inv)
    by (metis full full_def inv inv_s rtranclp_cdcl_s_cdcl_s_invariant)
  ultimately have "conflicting T = C_Clause {#} \<and> unsatisfiable (set_mset (init_clss T)) 
    \<or> conflicting T = C_True \<and> trail T \<Turnstile>asm init_clss T"
    using cdcl_s_normal_forms[of T] full unfolding cdcl_all_struct_inv_def cdcl_s_invariant_def full_def
    by fast
  moreover have "consistent_interp (lits_of (trail T))"
    using \<open>cdcl_all_struct_inv T\<close> unfolding cdcl_all_struct_inv_def cdcl_M_level_inv_def
    by auto
  moreover have "init_clss S = init_clss T"
    by (metis rtranclp_cdcl_s_no_more_init_clss full full_def)
  ultimately show ?thesis
    by (metis satisfiable_carac' true_annot_def true_annots_def true_clss_def)
qed    
  
lemma incremental_cdcl_inv:
  assumes
    inc: "incremental_cdcl S T" and
    inv: "cdcl_all_struct_inv S" and
    s_inv: "cdcl_s_invariant S"
  shows
    "cdcl_all_struct_inv T" and
    "cdcl_s_invariant T"
  using inc 
proof (induction)
  case (add_confl C T)
  let ?T = "(update_conflicting (C_Clause C) (add_init_cls C (cut_trail_wrt_clause C (trail S) S)))"
  have "cdcl_all_struct_inv ?T" and inv_s_T: "cdcl_s_invariant ?T"
    using add_confl.hyps(1,2,4) add_new_clause_and_update_def 
    cdcl_all_struct_inv_add_new_clause_and_update_cdcl_all_struct_inv inv apply auto[1]
    using add_confl.hyps(1,2,4) add_new_clause_and_update_def 
    cdcl_all_struct_inv_add_new_clause_and_update_cdcl_s_inv inv s_inv by auto
  case 1 show ?case
     by (metis add_confl.hyps(1,2,4,5) add_new_clause_and_update_def 
       cdcl_all_struct_inv_add_new_clause_and_update_cdcl_all_struct_inv 
       rtranclp_cdcl_all_struct_inv_inv rtranclp_cdcl_s_rtranclp_cdcl full_def inv)

  case 2  show ?case
    by (metis inv_s_T add_confl.hyps(1,2,4,5) add_new_clause_and_update_def 
      cdcl_all_struct_inv_add_new_clause_and_update_cdcl_all_struct_inv full_def inv 
      rtranclp_cdcl_s_cdcl_s_invariant)
next
  case (add_no_confl C)
  case 1 show ?case sorry
  case 2 show ?case sorry
qed

lemma blocked_induction_with_marked:
  assumes
    n_d: "no_dup (L # M)" and
    nil: "P []" and
    append: "\<And>M L M'. P M \<Longrightarrow> is_marked L \<Longrightarrow> \<forall>m \<in> set M'. \<not>is_marked m \<Longrightarrow> no_dup (L # M' @ M) \<Longrightarrow>
      P (L # M' @ M)" and
    L: "is_marked L"
  shows
    "P (L # M)"
  using n_d L
proof (induction "card {L' \<in> set M. is_marked L'}" arbitrary: L M)
  case 0 note n = this(1) and n_d = this(2) and L = this(3)
  then have "\<forall>m \<in> set M. \<not>is_marked m" by auto
  then show ?case using append[of "[]" L M] L nil n_d by auto
next
  case (Suc n) note IH = this(1) and n = this(2) and n_d = this(3) and L = this(4)
  have "\<exists>L' \<in> set M. is_marked L'"
    proof (rule ccontr)
      assume "\<not>?thesis"
      then have H: "{L' \<in> set M. is_marked L'} = {}"
        by auto
      show False using n unfolding H by auto
    qed
  then obtain L' M' M'' where
    M: "M = M' @ L' # M''" and
    L': "is_marked L'" and
    nm: "\<forall>m\<in>set M'. \<not>is_marked m"
    by (auto elim!: split_list_first_propE)
  have "Suc n = card {L' \<in> set M. is_marked L'}"
    using n .
  moreover have "{L' \<in> set M. is_marked L'} = {L'} \<union> {L' \<in> set M''. is_marked L'}"
    using nm L' n_d unfolding M by auto
  moreover have "L' \<notin> {L' \<in> set M''. is_marked L'}"
    using n_d unfolding M by auto
  ultimately  have "n = card {L'' \<in> set M''. is_marked L''}"
    using n L' by auto
  then have "P (L' # M'')" using IH L' n_d M by auto
  then show ?case using append[of "L' # M''" L M'] nm L n_d unfolding M by blast
qed

lemma trail_bloc_induction:
  assumes
    n_d: "no_dup M" and
    nil: "P []" and
    append: "\<And>M L M'. P M \<Longrightarrow> is_marked L \<Longrightarrow> \<forall>m \<in> set M'. \<not>is_marked m \<Longrightarrow> no_dup (L # M' @ M) \<Longrightarrow>
      P (L # M' @ M)" and
    append_nm: "\<And>M' M''. P M' \<Longrightarrow> M = M'' @  M' \<Longrightarrow> \<forall>m\<in>set M''. \<not>is_marked m \<Longrightarrow> P M"
  shows
    "P M"
proof (cases "{L' \<in> set M. is_marked L'} = {}")
  case True
  then show ?thesis using append_nm[of "[]" M] nil by auto
next
  case False
  then have "\<exists>L' \<in> set M. is_marked L'"
    by auto
  then obtain L' M' M'' where
    M: "M = M' @ L' # M''" and
    L': "is_marked L'" and
    nm: "\<forall>m\<in>set M'. \<not>is_marked m"
    by (auto elim!: split_list_first_propE)
  have "P (L' # M'')"
    apply (rule blocked_induction_with_marked)
       using n_d unfolding M apply simp
      using nil apply simp
     using append apply simp
    using L' by auto
  then show ?thesis
    using append_nm[of _ M'] nm  unfolding M by simp
qed

  (* TODO MOVE ME *)
lemma true_cls_mset_increasing_r[simp]:
  "I \<Turnstile>m CC \<Longrightarrow> I \<union> J \<Turnstile>m CC"
  unfolding true_cls_mset_def by auto

inductive Tcons :: "('v, nat, 'v clause) marked_lits \<Rightarrow>('v, nat, 'v clause) marked_lits \<Rightarrow> bool"
  for M :: "('v, nat, 'v clause) marked_lits" where
"Tcons M []" |
"Tcons M M' \<Longrightarrow> M = M'' @ M' \<Longrightarrow> (\<forall>m \<in> set M''. \<not>is_marked m) \<Longrightarrow> Tcons M (M'' @ M')" |
"Tcons M M' \<Longrightarrow> is_marked L \<Longrightarrow> M = M''' @ L # M'' @ M' \<Longrightarrow> (\<forall>m \<in> set M''. \<not>is_marked m) \<Longrightarrow>
  Tcons M (L # M'' @ M')"

lemma Tcons_same_end: "Tcons M M' \<Longrightarrow> \<exists>M''. M = M'' @ M'"
  by (induction rule: Tcons.induct) auto

end

end
