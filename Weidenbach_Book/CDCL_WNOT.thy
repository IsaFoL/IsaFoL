theory CDCL_WNOT
imports CDCL_NOT CDCL_W_Merge
begin

section \<open>Link between Weidenbach's and NOT's CDCL\<close>
subsection \<open>Inclusion of the states\<close>
declare upt.simps(2)[simp del]

fun convert_ann_lit_from_W where
"convert_ann_lit_from_W (Propagated L _) = Propagated L ()" |
"convert_ann_lit_from_W (Decided L) = Decided L"

abbreviation convert_trail_from_W ::
  "('v, 'mark) ann_lits
    \<Rightarrow> ('v, unit) ann_lits" where
"convert_trail_from_W \<equiv> map convert_ann_lit_from_W"

lemma lits_of_l_convert_trail_from_W[simp]:
  "lits_of_l (convert_trail_from_W M) = lits_of_l M"
  by (induction rule: ann_lit_list_induct) simp_all

lemma lit_of_convert_trail_from_W[simp]:
  "lit_of (convert_ann_lit_from_W L) = lit_of L"
  by (cases L) auto

lemma no_dup_convert_from_W[simp]:
  "no_dup (convert_trail_from_W M) \<longleftrightarrow> no_dup M"
  by (auto simp: comp_def)

lemma convert_trail_from_W_true_annots[simp]:
  "convert_trail_from_W M \<Turnstile>as C \<longleftrightarrow> M \<Turnstile>as C"
  by (auto simp: true_annots_true_cls image_image lits_of_def)

lemma defined_lit_convert_trail_from_W[simp]:
  "defined_lit (convert_trail_from_W S) L \<longleftrightarrow> defined_lit S L"
  by (auto simp: defined_lit_map image_comp)

text \<open>The values @{term "0::nat"} and @{term "{#}"} are dummy values.\<close>
consts dummy_cls :: 'cls
fun convert_ann_lit_from_NOT
  :: "('v, 'mark) ann_lit \<Rightarrow> ('v, 'cls) ann_lit" where
"convert_ann_lit_from_NOT (Propagated L _) = Propagated L dummy_cls" |
"convert_ann_lit_from_NOT (Decided L) = Decided L"

abbreviation convert_trail_from_NOT where
"convert_trail_from_NOT \<equiv> map convert_ann_lit_from_NOT"

lemma undefined_lit_convert_trail_from_NOT[simp]:
  "undefined_lit (convert_trail_from_NOT F) L \<longleftrightarrow> undefined_lit F L"
  by (induction F rule: ann_lit_list_induct) (auto simp: defined_lit_map)

lemma lits_of_l_convert_trail_from_NOT:
  "lits_of_l (convert_trail_from_NOT F) = lits_of_l F"
  by (induction F rule: ann_lit_list_induct) auto

lemma convert_trail_from_W_from_NOT[simp]:
  "convert_trail_from_W (convert_trail_from_NOT M) = M"
  by (induction rule: ann_lit_list_induct) auto

lemma convert_trail_from_W_convert_lit_from_NOT[simp]:
  "convert_ann_lit_from_W (convert_ann_lit_from_NOT L) = L"
  by (cases L) auto

abbreviation trail\<^sub>N\<^sub>O\<^sub>T where
"trail\<^sub>N\<^sub>O\<^sub>T S \<equiv> convert_trail_from_W (fst S)"

lemma undefined_lit_convert_trail_from_W[iff]:
  "undefined_lit (convert_trail_from_W M) L \<longleftrightarrow> undefined_lit M L"
  by (auto simp: defined_lit_map image_comp)

lemma lit_of_convert_ann_lit_from_NOT[iff]:
  "lit_of (convert_ann_lit_from_NOT L) = lit_of L"
  by (cases L) auto

sublocale state\<^sub>W \<subseteq> dpll_state_ops where
  trail = "\<lambda>S. convert_trail_from_W (trail S)" and
  clauses\<^sub>N\<^sub>O\<^sub>T = clauses and
  prepend_trail = "\<lambda>L S. cons_trail (convert_ann_lit_from_NOT L) S" and
  tl_trail = "\<lambda>S. tl_trail S" and
  add_cls\<^sub>N\<^sub>O\<^sub>T = "\<lambda>C S. add_learned_cls C S" and
  remove_cls\<^sub>N\<^sub>O\<^sub>T = "\<lambda>C S. remove_cls C S"
  by unfold_locales

sublocale state\<^sub>W \<subseteq> dpll_state where
  trail = "\<lambda>S. convert_trail_from_W (trail S)" and
  clauses\<^sub>N\<^sub>O\<^sub>T = clauses and
  prepend_trail = "\<lambda>L S. cons_trail (convert_ann_lit_from_NOT L) S" and
  tl_trail = "\<lambda>S. tl_trail S" and
  add_cls\<^sub>N\<^sub>O\<^sub>T = "\<lambda>C S. add_learned_cls C S" and
  remove_cls\<^sub>N\<^sub>O\<^sub>T = "\<lambda>C S. remove_cls C S"
  by unfold_locales (auto simp: map_tl o_def)

context state\<^sub>W
begin
declare state_simp\<^sub>N\<^sub>O\<^sub>T[simp del]
end


subsection \<open>Inclusion of Weidendenbch's CDCL without Strategy\<close>

sublocale conflict_driven_clause_learning\<^sub>W \<subseteq> cdcl\<^sub>N\<^sub>O\<^sub>T_merge_bj_learn_ops where
  trail = "\<lambda>S. convert_trail_from_W (trail S)" and
  clauses\<^sub>N\<^sub>O\<^sub>T = clauses and
  prepend_trail = "\<lambda>L S. cons_trail (convert_ann_lit_from_NOT L) S" and
  tl_trail = "\<lambda>S. tl_trail S" and
  add_cls\<^sub>N\<^sub>O\<^sub>T = "\<lambda>C S. add_learned_cls C S" and
  remove_cls\<^sub>N\<^sub>O\<^sub>T = "\<lambda>C S. remove_cls C S" and
  decide_conds = "\<lambda>_ _. True" and
  propagate_conds = "\<lambda>_ _. True" and
  forget_conds =  "\<lambda>_ S. conflicting S = None" and
  backjump_l_cond = "\<lambda>C C' L' S T. backjump_l_cond C C' L' S T
    \<and> distinct_mset (C' + {#L'#}) \<and> \<not>tautology (C' + {#L'#})"
  by unfold_locales

thm cdcl\<^sub>N\<^sub>O\<^sub>T_merge_bj_learn_proxy.axioms
sublocale conflict_driven_clause_learning\<^sub>W \<subseteq> cdcl\<^sub>N\<^sub>O\<^sub>T_merge_bj_learn_proxy where
  trail = "\<lambda>S. convert_trail_from_W (trail S)" and
  clauses\<^sub>N\<^sub>O\<^sub>T = clauses and
  prepend_trail = "\<lambda>L S. cons_trail (convert_ann_lit_from_NOT L) S" and
  tl_trail = "\<lambda>S. tl_trail S" and
  add_cls\<^sub>N\<^sub>O\<^sub>T = "\<lambda>C S. add_learned_cls C S" and
  remove_cls\<^sub>N\<^sub>O\<^sub>T = "\<lambda>C S. remove_cls C S" and
  decide_conds = "\<lambda>_ _. True" and
  propagate_conds = "\<lambda>_ _. True" and
  forget_conds =  "\<lambda>_ S. conflicting S = None" and
  backjump_l_cond = backjump_l_cond and
  inv = inv\<^sub>N\<^sub>O\<^sub>T
  by unfold_locales

sublocale conflict_driven_clause_learning\<^sub>W \<subseteq> cdcl\<^sub>N\<^sub>O\<^sub>T_merge_bj_learn_proxy2 where
  trail = "\<lambda>S. convert_trail_from_W (trail S)" and
  clauses\<^sub>N\<^sub>O\<^sub>T = clauses and
  prepend_trail = "\<lambda>L S. cons_trail (convert_ann_lit_from_NOT L) S" and
  tl_trail = "\<lambda>S. tl_trail S" and
  add_cls\<^sub>N\<^sub>O\<^sub>T = "\<lambda>C S. add_learned_cls C S" and
  remove_cls\<^sub>N\<^sub>O\<^sub>T = "\<lambda>C S. remove_cls C S" and
  decide_conds = "\<lambda>_ _. True" and
  propagate_conds = "\<lambda>_ _. True" and
  forget_conds =  "\<lambda>_ S. conflicting S = None" and
  backjump_l_cond = backjump_l_cond and
  inv = inv\<^sub>N\<^sub>O\<^sub>T
proof (unfold_locales, goal_cases)
  case 2
  then show ?case using cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_no_dup_inv by (auto simp: comp_def)
next
  case (1 C' S C F' K F L)
  moreover
    let ?C' = "remdups_mset C'"
    have "L \<notin># C'"
      using \<open>F \<Turnstile>as CNot C'\<close> \<open>undefined_lit F L\<close> Decided_Propagated_in_iff_in_lits_of_l
      in_CNot_implies_uminus(2) by fast
    then have "distinct_mset (?C' + {#L#})"
      by (simp add: distinct_mset_single_add)
  moreover
    have "no_dup F"
      using \<open>inv\<^sub>N\<^sub>O\<^sub>T S\<close> \<open>convert_trail_from_W (trail S) = F' @ Decided K # F\<close>
      unfolding inv\<^sub>N\<^sub>O\<^sub>T_def
      by (smt comp_apply distinct.simps(2) distinct_append list.simps(9) map_append
        no_dup_convert_from_W)
    then have "consistent_interp (lits_of_l F)"
      using distinct_consistent_interp by blast
    then have "\<not> tautology C'"
      using \<open>F \<Turnstile>as CNot C'\<close> consistent_CNot_not_tautology true_annots_true_cls by blast
    then have "\<not> tautology (?C' + {#L#})"
      using \<open>F \<Turnstile>as CNot C'\<close> \<open>undefined_lit F L\<close> by (metis CNot_remdups_mset
        Decided_Propagated_in_iff_in_lits_of_l add.commute in_CNot_uminus tautology_add_single
        tautology_remdups_mset true_annot_singleton true_annots_def)
  show ?case
    proof -
      have f2: "no_dup (convert_trail_from_W (trail S))"
        using \<open>inv\<^sub>N\<^sub>O\<^sub>T S\<close> unfolding inv\<^sub>N\<^sub>O\<^sub>T_def by (simp add: o_def)
      have f3: "atm_of L \<in> atms_of_mm (clauses S)
        \<union> atm_of ` lits_of_l (convert_trail_from_W (trail S))"
        using \<open>convert_trail_from_W (trail S) = F' @ Decided K # F\<close>
        \<open>atm_of L \<in> atms_of_mm (clauses S) \<union> atm_of ` lits_of_l (F' @ Decided K # F)\<close> by auto
      have f4: "clauses S \<Turnstile>pm remdups_mset C' + {#L#}"
        by (metis (no_types) \<open>L \<notin># C'\<close> \<open>clauses S \<Turnstile>pm C' + {#L#}\<close> remdups_mset_singleton_sum(2)
          true_clss_cls_remdups_mset union_commute)
      have "F \<Turnstile>as CNot (remdups_mset C')"
        by (simp add: \<open>F \<Turnstile>as CNot C'\<close>)
      have "Ex (backjump_l S)"
        apply standard
        apply (rule backjump_l.intros[OF _ f2, of _ _ _ ])
        using f4 f3 f2 \<open>\<not> tautology (remdups_mset C' + {#L#})\<close>
        calculation(2-5,9) \<open>F \<Turnstile>as CNot (remdups_mset C')\<close>
        state_eq\<^sub>N\<^sub>O\<^sub>T_ref unfolding backjump_l_cond_def by blast+
      then show ?thesis
        by blast
    qed
next
  case (3 L S)
  then show "\<exists>T. decide\<^sub>N\<^sub>O\<^sub>T S T \<or> propagate\<^sub>N\<^sub>O\<^sub>T S T \<or> backjump_l S T"
    using decide\<^sub>N\<^sub>O\<^sub>T.intros[of S L] by auto
qed

sublocale conflict_driven_clause_learning\<^sub>W \<subseteq> cdcl\<^sub>N\<^sub>O\<^sub>T_merge_bj_learn where
  trail = "\<lambda>S. convert_trail_from_W (trail S)" and
  clauses\<^sub>N\<^sub>O\<^sub>T = clauses and
  prepend_trail = "\<lambda>L S. cons_trail (convert_ann_lit_from_NOT L) S" and
  tl_trail = "\<lambda>S. tl_trail S" and
  add_cls\<^sub>N\<^sub>O\<^sub>T = "\<lambda>C S. add_learned_cls C S" and
  remove_cls\<^sub>N\<^sub>O\<^sub>T = "\<lambda>C S. remove_cls C S" and
  decide_conds = "\<lambda>_ _. True" and
  propagate_conds = "\<lambda>_ _. True" and
  forget_conds =  "\<lambda>_ S. conflicting S = None" and
  backjump_l_cond = backjump_l_cond and
  inv = inv\<^sub>N\<^sub>O\<^sub>T
  apply unfold_locales
   using dpll_bj_no_dup apply (simp add: comp_def)
  using cdcl\<^sub>N\<^sub>O\<^sub>T.simps cdcl\<^sub>N\<^sub>O\<^sub>T_no_dup no_dup_convert_from_W unfolding inv\<^sub>N\<^sub>O\<^sub>T_def by blast

context conflict_driven_clause_learning\<^sub>W
begin
text \<open>Notations are lost while proving locale inclusion:\<close>
notation state_eq\<^sub>N\<^sub>O\<^sub>T (infix "\<sim>\<^sub>N\<^sub>O\<^sub>T" 50)

subsection \<open>Additional Lemmas between NOT and W states\<close>
lemma trail\<^sub>W_eq_reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_eq:
  "trail S = trail T \<Longrightarrow> trail (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S) = trail (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F T)"
proof (induction F S arbitrary: T rule: reduce_trail_to\<^sub>N\<^sub>O\<^sub>T.induct)
  case (1 F S T) note IH = this(1) and tr = this(2)
  then have "[] = convert_trail_from_W (trail S)
    \<or> length F = length (convert_trail_from_W (trail S))
    \<or> trail (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F (tl_trail S)) = trail (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F (tl_trail T))"
    using IH by (metis (no_types) trail_tl_trail)
  then show "trail (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F S) = trail (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T F T)"
    using tr by (metis (no_types) reduce_trail_to\<^sub>N\<^sub>O\<^sub>T.elims)
qed

lemma trail_reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_add_learned_cls:
"no_dup (trail S) \<Longrightarrow>
  trail (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T M (add_learned_cls D S)) = trail (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T M S)"
 by (rule trail\<^sub>W_eq_reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_eq) simp

lemma reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_reduce_trail_convert:
  "reduce_trail_to\<^sub>N\<^sub>O\<^sub>T C S = reduce_trail_to (convert_trail_from_NOT C) S"
  apply (induction C S rule: reduce_trail_to\<^sub>N\<^sub>O\<^sub>T.induct)
  apply (subst reduce_trail_to\<^sub>N\<^sub>O\<^sub>T.simps, subst reduce_trail_to.simps)
  by auto

lemma reduce_trail_to_map[simp]:
  "reduce_trail_to (map f M) S = reduce_trail_to M S"
  by (rule reduce_trail_to_length) simp

lemma reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_map[simp]:
  "reduce_trail_to\<^sub>N\<^sub>O\<^sub>T (map f M) S = reduce_trail_to\<^sub>N\<^sub>O\<^sub>T M S"
  by (rule reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_length) simp

lemma skip_or_resolve_state_change:
  assumes "skip_or_resolve\<^sup>*\<^sup>* S T"
  shows
    "\<exists>M. trail S = M @ trail T \<and> (\<forall>m \<in> set M. \<not>is_decided m)"
    "clauses S = clauses T"
    "backtrack_lvl S = backtrack_lvl T"
  using assms
proof (induction rule: rtranclp_induct)
  case base
  case 1 show ?case by simp
  case 2 show ?case by simp
  case 3 show ?case by simp
next
  case (step T U) note st = this(1) and s_o_r = this(2) and IH = this(3) and IH' = this(3-5)

  case 2 show ?case using IH' s_o_r by (auto elim!: rulesE simp: skip_or_resolve.simps)
  case 3 show ?case using IH' s_o_r by (auto elim!: rulesE simp: skip_or_resolve.simps)
  case 1 show ?case
    using s_o_r
    proof cases
      case s_or_r_skip
      then show ?thesis using IH by (auto elim!: rulesE simp: skip_or_resolve.simps)
    next
      case s_or_r_resolve
      then show ?thesis
        using IH by (cases "trail T") (auto elim!: rulesE simp: skip_or_resolve.simps)
    qed
qed


subsection \<open>Inclusion of Weidenbach's CDCL in NOT's CDCL\<close>

text \<open>This lemma shows the inclusion of Weidenbach's CDCL @{const cdcl\<^sub>W_merge} (with merging) in
  NOT's @{const cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn}.\<close>
lemma cdcl\<^sub>W_merge_is_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn:
  assumes
    inv: "cdcl\<^sub>W_all_struct_inv S" and
    cdcl\<^sub>W_restart: "cdcl\<^sub>W_merge S T"
  shows "cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn S T
    \<or> (no_step cdcl\<^sub>W_merge T \<and> conflicting T \<noteq> None)"
  using cdcl\<^sub>W_restart inv
proof induction
  case (fw_propagate S T) note propa = this(1)
  then obtain M N U k L C where
    H: "state S = (M, N, U, k, None)" and
    CL: "C + {#L#} \<in># clauses S" and
    M_C: "M \<Turnstile>as CNot C" and
    undef: "undefined_lit (trail S) L" and
    T: "state T = (Propagated L (C + {#L#}) # M, N, U, k, None)"
    by (auto elim: propagate_high_levelE)
  have "propagate\<^sub>N\<^sub>O\<^sub>T S T"
    using H CL T undef M_C by (auto simp: state_eq\<^sub>N\<^sub>O\<^sub>T_def state_eq_def clauses_def
      simp del: state_simp)
  then show ?case
    using cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn.intros(2) by blast
next
  case (fw_decide S T) note dec = this(1) and inv = this(2)
  then obtain L where
    undef_L: "undefined_lit (trail S) L" and
    atm_L: "atm_of L \<in> atms_of_mm (init_clss S)" and
    T: "T \<sim> cons_trail (Decided L)
      (update_backtrack_lvl (Suc (backtrack_lvl S)) S)"
    by (auto elim: decideE)
  have "decide\<^sub>N\<^sub>O\<^sub>T S T"
    apply (rule decide\<^sub>N\<^sub>O\<^sub>T.decide\<^sub>N\<^sub>O\<^sub>T)
       using undef_L apply simp
     using atm_L inv unfolding cdcl\<^sub>W_all_struct_inv_def no_strange_atm_def clauses_def
       apply auto[]
    using T undef_L unfolding state_eq_def state_eq\<^sub>N\<^sub>O\<^sub>T_def by (auto simp: clauses_def)
  then show ?case using cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_decide\<^sub>N\<^sub>O\<^sub>T by blast
next
  case (fw_forget S T) note rf = this(1) and inv = this(2)
  then obtain C where
     S: "conflicting S = None" and
     C_le: "C \<in># learned_clss S" and
     "\<not>(trail S) \<Turnstile>asm clauses S" and
     "C \<notin> set (get_all_mark_of_propagated (trail S))" and
     C_init: "C \<notin># init_clss S" and
     T: "T \<sim> remove_cls C S"
    by (auto elim: forgetE)
  have "init_clss S \<Turnstile>pm C"
    using inv C_le unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_learned_clause_def clauses_def
    by (meson true_clss_clss_in_imp_true_clss_cls)
  then have S_C: "removeAll_mset C (clauses S) \<Turnstile>pm C"
    using C_init C_le unfolding clauses_def by (auto simp add: Un_Diff ac_simps)
  have "forget\<^sub>N\<^sub>O\<^sub>T S T"
    apply (rule forget\<^sub>N\<^sub>O\<^sub>T.forget\<^sub>N\<^sub>O\<^sub>T)
       using S_C apply blast
      using S apply simp
     using C_init C_le apply (simp add: clauses_def)
    using T C_le C_init by (auto
      simp: state_eq_def Un_Diff state_eq\<^sub>N\<^sub>O\<^sub>T_def clauses_def ac_simps
      simp del: state_simp)
  then show ?case using cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_forget\<^sub>N\<^sub>O\<^sub>T by blast
next
  case (fw_conflict S T U) note confl = this(1) and bj = this(2) and inv = this(3)
  obtain C\<^sub>S CT where
    confl_T: "conflicting T = Some CT" and
    CT: "CT = C\<^sub>S" and
    C\<^sub>S: "C\<^sub>S \<in># clauses S" and
    tr_S_C\<^sub>S: "trail S \<Turnstile>as CNot C\<^sub>S"
    using confl by (elim conflictE) (auto simp del: state_simp simp: state_eq_def)
  have inv_T: "cdcl\<^sub>W_all_struct_inv T"
    using cdcl\<^sub>W_restart.simps cdcl\<^sub>W_all_struct_inv_inv confl inv by blast
  then have "cdcl\<^sub>W_M_level_inv T"
    unfolding cdcl\<^sub>W_all_struct_inv_def by auto
  then consider
      (no_bt) "skip_or_resolve\<^sup>*\<^sup>* T U"
    | (bt) T' where "skip_or_resolve\<^sup>*\<^sup>* T T'" and "backtrack T' U"
    using bj rtranclp_cdcl\<^sub>W_bj_skip_or_resolve_backtrack unfolding full_def by meson
  then show ?case
    proof cases
      case no_bt
      then have "conflicting U \<noteq> None"
        using confl by (induction rule: rtranclp_induct)
        (auto simp del: state_simp simp: skip_or_resolve.simps state_eq_def elim!: rulesE)
      moreover then have "no_step cdcl\<^sub>W_merge U"
        by (auto simp: cdcl\<^sub>W_merge.simps elim: rulesE)
      ultimately show ?thesis by blast
    next
      case bt note s_or_r = this(1) and bt = this(2)
      have "cdcl\<^sub>W_restart\<^sup>*\<^sup>* T T'"
        using s_or_r mono_rtranclp[of skip_or_resolve cdcl\<^sub>W_restart] rtranclp_skip_or_resolve_rtranclp_cdcl\<^sub>W_restart
        by blast
      then have "cdcl\<^sub>W_M_level_inv T'"
        using rtranclp_cdcl\<^sub>W_restart_consistent_inv \<open>cdcl\<^sub>W_M_level_inv T\<close> by blast
      then obtain M1 M2 i D L K where
        confl_T': "conflicting T' = Some D" and
        LD: "L \<in># D" and
        M1_M2:"(Decided K # M1, M2) \<in> set (get_all_ann_decomposition (trail T'))" and
        "get_level (trail T') K = i+1"
        "get_level (trail T') L = backtrack_lvl T'" and
        "get_level (trail T') L = get_maximum_level (trail T') D" and
        "get_maximum_level (trail T') (remove1_mset L D) = i" and
        U: "U \<sim> cons_trail (Propagated L D)
                 (reduce_trail_to M1
                      (add_learned_cls D
                         (update_backtrack_lvl i
                            (update_conflicting None T'))))"
        using bt by (auto elim: backtrackE)
      have [simp]: "clauses S = clauses T"
        using confl by (auto elim: rulesE)
      have [simp]: "clauses T = clauses T'"
        using s_or_r
        proof (induction)
          case base
          then show ?case by simp
        next
          case (step U V) note st = this(1) and s_o_r = this(2) and IH = this(3)
          have "clauses U = clauses V"
            using s_o_r by (auto simp: skip_or_resolve.simps elim: rulesE)
          then show ?case using IH by auto
        qed
      have "cdcl\<^sub>W_restart\<^sup>*\<^sup>* T T'"
        using rtranclp_skip_or_resolve_rtranclp_cdcl\<^sub>W_restart s_or_r by blast
      have inv_T': "cdcl\<^sub>W_all_struct_inv T'"
        using \<open>cdcl\<^sub>W_restart\<^sup>*\<^sup>* T T'\<close> inv_T rtranclp_cdcl\<^sub>W_all_struct_inv_inv by blast
      have inv_U: "cdcl\<^sub>W_all_struct_inv U"
        using cdcl\<^sub>W_merge_restart_cdcl\<^sub>W_restart confl fw_r_conflict inv local.bj
        rtranclp_cdcl\<^sub>W_all_struct_inv_inv by blast

      have [simp]: "init_clss S = init_clss T'"
        using \<open>cdcl\<^sub>W_restart\<^sup>*\<^sup>* T T'\<close> cdcl\<^sub>W_restart_init_clss confl cdcl\<^sub>W_all_struct_inv_def conflict
        inv by (metis rtranclp_cdcl\<^sub>W_restart_init_clss)
      then have atm_L: "atm_of L \<in> atms_of_mm (clauses S)"
        using inv_T' confl_T' LD unfolding cdcl\<^sub>W_all_struct_inv_def no_strange_atm_def
        clauses_def
        by (simp add: atms_of_def image_subset_iff)
      obtain M where tr_T: "trail T = M @ trail T'"
        using s_or_r skip_or_resolve_state_change by meson
      obtain M' where
        tr_T': "trail T' = M' @ Decided K # tl (trail U)" and
        tr_U: "trail U = Propagated L D # tl (trail U)"
        using U M1_M2 inv_T' unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def
        by fastforce
      define M'' where "M'' \<equiv> M @ M'"
      have tr_T: "trail S = M'' @ Decided K # tl (trail U)"
        using tr_T tr_T' confl unfolding M''_def by (auto elim: rulesE)
      have "init_clss T' + learned_clss S \<Turnstile>pm D"
        using inv_T' confl_T' unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_learned_clause_def
        clauses_def by simp
      have "reduce_trail_to (convert_trail_from_NOT (convert_trail_from_W M1)) S =
        reduce_trail_to M1 S"
        by (rule reduce_trail_to_length) simp
      moreover have "trail (reduce_trail_to M1 S) = M1"
        apply (rule reduce_trail_to_skip_beginning[of _ "M @ _ @ M2 @ [Decided K]"])
        using confl M1_M2 \<open>trail T = M @ trail T'\<close>
          apply (auto dest!: get_all_ann_decomposition_exists_prepend
            elim!: conflictE)
          by (rule sym) auto
      ultimately have [simp]: "trail (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T M1 S) = M1"
        using M1_M2 confl by (subst reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_reduce_trail_convert)
        (auto simp: comp_def elim: rulesE)
      have "every_mark_is_a_conflict U"
        using inv_U unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_conflicting_def by simp
      then have U_D: "tl (trail U) \<Turnstile>as CNot (remove1_mset L D)"
        by (metis append_self_conv2 tr_U)
      have undef_L: "undefined_lit (tl (trail U)) L"
        using U M1_M2 inv_U unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def
        by (auto simp: lits_of_def defined_lit_map)
      have "backjump_l S U"
        apply (rule backjump_l[of _ _ _ _ _ L D _ "remove1_mset L D"])
                 using tr_T apply simp
                using inv unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def
                apply (simp add: comp_def)
               using U M1_M2 confl M1_M2 inv_T' inv unfolding cdcl\<^sub>W_all_struct_inv_def
               cdcl\<^sub>W_M_level_inv_def apply (auto simp: state_eq\<^sub>N\<^sub>O\<^sub>T_def
                 trail_reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_add_learned_cls)[]
              using C\<^sub>S apply auto[]
             using tr_S_C\<^sub>S apply simp

            using undef_L apply auto[]
           using atm_L apply (simp add: trail_reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_add_learned_cls)
          using \<open>init_clss T' + learned_clss S \<Turnstile>pm D\<close> LD unfolding clauses_def
          apply simp
         using LD apply simp
        apply (metis U_D convert_trail_from_W_true_annots)
        using inv_T' inv_U U confl_T' undef_L M1_M2 LD unfolding cdcl\<^sub>W_all_struct_inv_def
        distinct_cdcl\<^sub>W_state_def by (simp add: cdcl\<^sub>W_M_level_inv_decomp backjump_l_cond_def)
      then show ?thesis using cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_backjump_l by fast
    qed
qed

abbreviation cdcl\<^sub>N\<^sub>O\<^sub>T_restart where
"cdcl\<^sub>N\<^sub>O\<^sub>T_restart \<equiv> restart_ops.cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart cdcl\<^sub>N\<^sub>O\<^sub>T restart"

lemma cdcl\<^sub>W_merge_restart_is_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_restart_no_step:
  assumes
    inv: "cdcl\<^sub>W_all_struct_inv S" and
    cdcl\<^sub>W_restart:"cdcl\<^sub>W_merge_restart S T"
  shows "cdcl\<^sub>N\<^sub>O\<^sub>T_restart\<^sup>*\<^sup>* S T \<or> (no_step cdcl\<^sub>W_merge T \<and> conflicting T \<noteq> None)"
proof -
  consider
      (fw) "cdcl\<^sub>W_merge S T"
    | (fw_r) "restart S T"
    using cdcl\<^sub>W_restart by (meson cdcl\<^sub>W_merge_restart.simps cdcl\<^sub>W_rf.cases fw_conflict fw_decide fw_forget
      fw_propagate)
  then show ?thesis
    proof cases
      case fw
      then have IH: "cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn S T \<or> (no_step cdcl\<^sub>W_merge T \<and> conflicting T \<noteq> None)"
        using inv cdcl\<^sub>W_merge_is_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn by blast
      have invS: "inv\<^sub>N\<^sub>O\<^sub>T S"
        using inv unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def by auto
      have ff2: "cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>+\<^sup>+ S T \<longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T"
          by (meson tranclp_into_rtranclp)
      have ff3: "no_dup (convert_trail_from_W (trail S))"
        using invS by (simp add: comp_def)
      have "cdcl\<^sub>N\<^sub>O\<^sub>T \<le> cdcl\<^sub>N\<^sub>O\<^sub>T_restart"
        by (auto simp: restart_ops.cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart.simps)
      then show ?thesis
        using ff3 ff2 IH cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_is_tranclp_cdcl\<^sub>N\<^sub>O\<^sub>T
        rtranclp_mono[of cdcl\<^sub>N\<^sub>O\<^sub>T cdcl\<^sub>N\<^sub>O\<^sub>T_restart] invS predicate2D by blast
    next
      case fw_r
      then show ?thesis by (blast intro: restart_ops.cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart.intros)
    qed
qed

abbreviation \<mu>\<^sub>F\<^sub>W :: "'st \<Rightarrow> nat" where
"\<mu>\<^sub>F\<^sub>W S \<equiv> (if no_step cdcl\<^sub>W_merge S then 0 else 1+\<mu>\<^sub>C\<^sub>D\<^sub>C\<^sub>L'_merged (set_mset (init_clss S)) S)"

lemma cdcl\<^sub>W_merge_\<mu>\<^sub>F\<^sub>W_decreasing:
  assumes
    inv: "cdcl\<^sub>W_all_struct_inv S" and
    fw: "cdcl\<^sub>W_merge S T"
  shows "\<mu>\<^sub>F\<^sub>W T < \<mu>\<^sub>F\<^sub>W S"
proof -
  let ?A = "init_clss S"
  have atm_clauses: "atms_of_mm (clauses S) \<subseteq> atms_of_mm ?A"
    using inv unfolding cdcl\<^sub>W_all_struct_inv_def no_strange_atm_def clauses_def by auto
  have atm_trail: "atm_of ` lits_of_l (trail S) \<subseteq> atms_of_mm ?A"
    using inv unfolding cdcl\<^sub>W_all_struct_inv_def no_strange_atm_def clauses_def by auto
  have n_d: "no_dup (trail S)"
    using inv unfolding cdcl\<^sub>W_all_struct_inv_def by (auto simp: cdcl\<^sub>W_M_level_inv_decomp)
  have [simp]: "\<not> no_step cdcl\<^sub>W_merge S"
    using fw by auto
  have [simp]: "init_clss S = init_clss T"
    using cdcl\<^sub>W_merge_restart_cdcl\<^sub>W_restart[of S T] inv rtranclp_cdcl\<^sub>W_restart_init_clss
    unfolding cdcl\<^sub>W_all_struct_inv_def
    by (meson cdcl\<^sub>W_merge.simps cdcl\<^sub>W_merge_restart.simps cdcl\<^sub>W_rf.simps fw)
  consider
      (merged) "cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn S T"
    | (n_s) "no_step cdcl\<^sub>W_merge T"
    using cdcl\<^sub>W_merge_is_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn inv fw by blast
  then show ?thesis
    proof cases
      case merged
      then show ?thesis
        using cdcl\<^sub>N\<^sub>O\<^sub>T_decreasing_measure'[OF _ _ atm_clauses, of T] atm_trail n_d
        by (auto split: if_split simp: comp_def image_image lits_of_def)
    next
      case n_s
      then show ?thesis by simp
    qed
qed

lemma wf_cdcl\<^sub>W_merge: "wf {(T, S). cdcl\<^sub>W_all_struct_inv S \<and> cdcl\<^sub>W_merge S T}"
  apply (rule wfP_if_measure[of _ _ "\<mu>\<^sub>F\<^sub>W"])
  using cdcl\<^sub>W_merge_\<mu>\<^sub>F\<^sub>W_decreasing by blast

lemma tranclp_cdcl\<^sub>W_merge_cdcl\<^sub>W_merge_trancl:
  "{(T, S). cdcl\<^sub>W_all_struct_inv S \<and> cdcl\<^sub>W_merge\<^sup>+\<^sup>+ S T}
  \<subseteq> {(T, S). cdcl\<^sub>W_all_struct_inv S \<and> cdcl\<^sub>W_merge S T}\<^sup>+"
proof -
  have "(T, S) \<in> {(T, S). cdcl\<^sub>W_all_struct_inv S \<and> cdcl\<^sub>W_merge S T}\<^sup>+"
    if inv: "cdcl\<^sub>W_all_struct_inv S" and "cdcl\<^sub>W_merge\<^sup>+\<^sup>+ S T"
    for S T :: 'st
    using that(2)
    proof (induction rule: tranclp_induct)
      case base
      then show ?case using inv by auto
    next
      case (step T U) note st = this(1) and s = this(2) and IH = this(3)
      have "cdcl\<^sub>W_all_struct_inv T"
        using st by (meson inv rtranclp_cdcl\<^sub>W_all_struct_inv_inv
          rtranclp_cdcl\<^sub>W_merge_rtranclp_cdcl\<^sub>W_restart tranclp_into_rtranclp)
      then have "(U, T) \<in> {(T, S). cdcl\<^sub>W_all_struct_inv S \<and> cdcl\<^sub>W_merge S T}\<^sup>+"
        using s by auto
      then show ?case using IH by auto
    qed
  then show ?thesis by auto
qed

lemma wf_tranclp_cdcl\<^sub>W_merge: "wf {(T, S). cdcl\<^sub>W_all_struct_inv S \<and> cdcl\<^sub>W_merge\<^sup>+\<^sup>+ S T}"
  apply (rule wf_subset)
    apply (rule wf_trancl)
    using wf_cdcl\<^sub>W_merge apply simp
  using tranclp_cdcl\<^sub>W_merge_cdcl\<^sub>W_merge_trancl by simp

lemma wf_cdcl\<^sub>W_bj_all_struct: "wf {(T, S). cdcl\<^sub>W_all_struct_inv S \<and> cdcl\<^sub>W_bj S T}"
  apply (rule wfP_if_measure[of "\<lambda>_. True"
      _ "\<lambda>T. length (trail T) + (if conflicting T = None then 0 else 1)", simplified])
  using cdcl\<^sub>W_bj_measure by (simp add: cdcl\<^sub>W_all_struct_inv_def)

lemma cdcl\<^sub>W_conflicting_true_cdcl\<^sub>W_merge_restart:
  assumes "cdcl\<^sub>W S V" and confl: "conflicting S = None"
  shows "(cdcl\<^sub>W_merge S V \<and> conflicting V = None) \<or> (conflicting V \<noteq> None \<and> conflict S V)"
  using assms
proof (induction rule: cdcl\<^sub>W.induct)
  case W_propagate
  then show ?case by (auto intro: cdcl\<^sub>W_merge.intros elim: rulesE)
next
  case (W_conflict S')
  then show ?case by (auto intro: cdcl\<^sub>W_merge.intros elim: rulesE)
next
  case W_other
  then show ?case
    proof cases
      case decide
      then show ?thesis
        by (auto intro: cdcl\<^sub>W_merge.intros elim: rulesE)
    next
      case bj
      then show ?thesis
        using confl by (auto simp: cdcl\<^sub>W_bj.simps elim: rulesE)
  qed
qed

lemma trancl_cdcl\<^sub>W_conflicting_true_cdcl\<^sub>W_merge_restart:
  assumes "cdcl\<^sub>W\<^sup>+\<^sup>+ S V" and inv: "cdcl\<^sub>W_M_level_inv S" and "conflicting S = None"
  shows "(cdcl\<^sub>W_merge\<^sup>+\<^sup>+ S V \<and> conflicting V = None)
    \<or> (\<exists>T U. cdcl\<^sub>W_merge\<^sup>*\<^sup>* S T \<and> conflicting V \<noteq> None \<and> conflict T U \<and> cdcl\<^sub>W_bj\<^sup>*\<^sup>* U V)"
  using assms
proof induction
  case base
  then show ?case using cdcl\<^sub>W_conflicting_true_cdcl\<^sub>W_merge_restart by blast
next
  case (step U V) note st = this(1) and cdcl\<^sub>W = this(2) and IH = this(3)[OF this(4-)] and
    confl[simp] = this(5) and inv = this(4)
  from cdcl\<^sub>W
  show ?case
    proof (cases)
      case W_propagate
      moreover then have "conflicting U = None" and "conflicting V = None"
        by (auto elim: propagateE)
      ultimately show ?thesis using IH cdcl\<^sub>W_merge.fw_propagate[of U V] by auto
    next
      case W_conflict
      moreover then have "conflicting U = None" and "conflicting V \<noteq> None"
        by (auto elim!: conflictE simp del: state_simp simp: state_eq_def)
      moreover then have "cdcl\<^sub>W_merge\<^sup>*\<^sup>* S U"
        using IH by auto
      ultimately show ?thesis using IH by auto
    next
      case W_other
      then show ?thesis
        proof cases
          case decide
          then show ?thesis using IH cdcl\<^sub>W_merge.fw_decide[of U V] by (auto elim: decideE)
        next
          case bj
          moreover {
            assume "skip_or_resolve U V"
            have f1: "cdcl\<^sub>W_bj\<^sup>+\<^sup>+ U V"
              by (simp add: local.bj tranclp.r_into_trancl)
            obtain T T' :: 'st where
              f2: "cdcl\<^sub>W_merge\<^sup>+\<^sup>+ S U
                \<or> cdcl\<^sub>W_merge\<^sup>*\<^sup>* S T \<and> conflicting U \<noteq> None
                  \<and> conflict T T' \<and> cdcl\<^sub>W_bj\<^sup>*\<^sup>* T' U"
              using IH confl by (meson calculation rtranclp.intros(1)
                rtranclp_cdcl\<^sub>W_merge_restart_no_step_cdcl\<^sub>W_bj
                rtranclp_cdcl\<^sub>W_merge_tranclp_cdcl\<^sub>W_merge_restart)
            have "conflicting V \<noteq> None \<and> conflicting U \<noteq> None"
              using \<open>skip_or_resolve U V\<close>
              by (auto simp: skip_or_resolve.simps state_eq_def elim!: skipE resolveE
                simp del: state_simp)
            then have ?thesis
              by (metis (full_types) IH f1 rtranclp_trans tranclp_into_rtranclp)
          }
          moreover {
            assume "backtrack U V"
            then have "conflicting U \<noteq> None" by (auto elim: backtrackE)
            then obtain T T' where
              "cdcl\<^sub>W_merge\<^sup>*\<^sup>* S T" and
              "conflicting U \<noteq> None" and
              "conflict T T'" and
              "cdcl\<^sub>W_bj\<^sup>*\<^sup>* T' U"
              using IH confl by (meson calculation rtranclp.intros(1)
                rtranclp_cdcl\<^sub>W_merge_restart_no_step_cdcl\<^sub>W_bj
                rtranclp_cdcl\<^sub>W_merge_tranclp_cdcl\<^sub>W_merge_restart)
            have invU: "cdcl\<^sub>W_M_level_inv U"
              using inv rtranclp_cdcl\<^sub>W_restart_consistent_inv step.hyps(1)
              by (meson \<open>cdcl\<^sub>W_bj\<^sup>*\<^sup>* T' U\<close> \<open>cdcl\<^sub>W_merge\<^sup>*\<^sup>* S T\<close> \<open>conflict T T'\<close>
                cdcl\<^sub>W_restart_consistent_inv conflict rtranclp_cdcl\<^sub>W_bj_rtranclp_cdcl\<^sub>W_restart
                rtranclp_cdcl\<^sub>W_merge_rtranclp_cdcl\<^sub>W_restart)
            then have "conflicting V = None"
              using \<open>backtrack U V\<close> inv by (auto elim: backtrackE
                simp: cdcl\<^sub>W_M_level_inv_decomp)
            have "full cdcl\<^sub>W_bj T' V"
              apply (rule rtranclp_fullI[of cdcl\<^sub>W_bj T' U V])
                using \<open>cdcl\<^sub>W_bj\<^sup>*\<^sup>* T' U\<close> apply fast
              using \<open>backtrack U V\<close> backtrack_is_full1_cdcl\<^sub>W_bj invU unfolding full1_def full_def
              by blast
            then have ?thesis
              using cdcl\<^sub>W_merge.fw_conflict[of T T' V] \<open>conflict T T'\<close>
              \<open>cdcl\<^sub>W_merge\<^sup>*\<^sup>* S T\<close> \<open>conflicting V = None\<close> by auto
          }
          ultimately show ?thesis by (auto simp: cdcl\<^sub>W_bj.simps)
      qed
    qed
qed

lemma wf_cdcl\<^sub>W: "wf {(T, S). cdcl\<^sub>W_all_struct_inv S \<and> cdcl\<^sub>W S T}"
  unfolding wf_iff_no_infinite_down_chain
proof clarify
  fix f :: "nat \<Rightarrow> 'st"
  assume "\<forall>i. (f (Suc i), f i) \<in> {(T, S). cdcl\<^sub>W_all_struct_inv S \<and> cdcl\<^sub>W S T}"
  then have f: "\<And>i. (f (Suc i), f i) \<in> {(T, S). cdcl\<^sub>W_all_struct_inv S \<and> cdcl\<^sub>W S T}"
    by blast
  {
    fix f :: "nat \<Rightarrow> 'st"
    assume
      f: "(f (Suc i), f i) \<in> {(T, S). cdcl\<^sub>W_all_struct_inv S \<and> cdcl\<^sub>W S T}" and
      confl: "conflicting (f i) \<noteq> None" for i
    have  "(f (Suc i), f i) \<in> {(T, S). cdcl\<^sub>W_all_struct_inv S \<and> cdcl\<^sub>W_bj S T}" for i
      using f[of i] confl[of i] by (auto simp:  cdcl\<^sub>W.simps cdcl\<^sub>W_o.simps cdcl\<^sub>W_rf.simps
        elim!: rulesE)
    then have False
      using wf_cdcl\<^sub>W_bj_all_struct unfolding wf_iff_no_infinite_down_chain by blast
  } note no_infinite_conflict = this

  have st: "cdcl\<^sub>W\<^sup>+\<^sup>+ (f i) (f (Suc (i+j)))" for i j :: nat
    proof (induction j)
      case 0
      then show ?case using f by auto
    next
      case (Suc j)
      then show ?case using f [of "i+j+1"] by auto
    qed
  have st: "i < j \<Longrightarrow> cdcl\<^sub>W\<^sup>+\<^sup>+ (f i) (f j)" for i j :: nat
    using st[of i "j - i - 1"] by auto

  obtain i\<^sub>b where i\<^sub>b: "conflicting (f i\<^sub>b) = None"
    using f no_infinite_conflict by blast

  define i\<^sub>0 where i\<^sub>0: "i\<^sub>0 = Max {i\<^sub>0. \<forall>i < i\<^sub>0. conflicting (f i) \<noteq> None}"
  have "finite {i\<^sub>0. \<forall>i < i\<^sub>0. conflicting (f i) \<noteq> None}"
    proof -
      have "{i\<^sub>0. \<forall>i < i\<^sub>0. conflicting (f i) \<noteq> None} \<subseteq> {0..i\<^sub>b}"
        using i\<^sub>b by (metis (mono_tags, lifting) atLeast0AtMost atMost_iff mem_Collect_eq not_le
          subsetI)
      then show ?thesis
        by (simp add: finite_subset)
    qed
  moreover have "{i\<^sub>0. \<forall>i < i\<^sub>0. conflicting (f i) \<noteq> None} \<noteq> {}"
    by auto
  ultimately  have "i\<^sub>0 \<in> {i\<^sub>0. \<forall>i < i\<^sub>0. conflicting (f i) \<noteq> None}"
    using Max_in[of "{i\<^sub>0. \<forall>i<i\<^sub>0. conflicting (f i) \<noteq> None}"] unfolding i\<^sub>0 by fast
  then have confl_i\<^sub>0: "conflicting (f i\<^sub>0) = None"
    proof -
      have f1: "\<forall>n<i\<^sub>0. conflicting (f n) \<noteq> None"
        using \<open>i\<^sub>0 \<in> {i\<^sub>0. \<forall>i<i\<^sub>0. conflicting (f i) \<noteq> None}\<close> by blast
      have "Suc i\<^sub>0 \<notin> {n. \<forall>na<n. conflicting (f na) \<noteq> None}"
        by (metis (lifting) Max_ge \<open>finite {i\<^sub>0. \<forall>i<i\<^sub>0. conflicting (f i) \<noteq> None}\<close>
          i\<^sub>0 lessI not_le)
      then have "\<exists>n<Suc i\<^sub>0. conflicting (f n) = None"
        by fastforce
      then show "conflicting (f i\<^sub>0) = None"
        using f1 by (metis le_less less_Suc_eq_le)
    qed
  have "\<forall>i < i\<^sub>0. conflicting (f i) \<noteq> None"
    using \<open>i\<^sub>0 \<in> {i\<^sub>0. \<forall>i < i\<^sub>0. conflicting (f i) \<noteq> None}\<close> by blast

  have not_conflicting_none: False if confl: "\<forall>x>i. conflicting (f x) = None" for i :: nat
    proof -
      let ?f = "\<lambda>j. f (i + j+1)"
      have "cdcl\<^sub>W_merge (?f j) (?f (Suc j))" for j :: nat
        using f[of "i+j+1"] confl that by (auto dest!: cdcl\<^sub>W_conflicting_true_cdcl\<^sub>W_merge_restart)
      then have "(?f (Suc j), ?f j) \<in> {(T, S). cdcl\<^sub>W_all_struct_inv S \<and> cdcl\<^sub>W_merge S T}"
        for j :: nat
        using f[of "i+j+1"] by auto
      then show False
        using wf_cdcl\<^sub>W_merge unfolding wf_iff_no_infinite_down_chain by fast
    qed

  have not_conflicting: False if confl: "\<forall>x>i. conflicting (f x) \<noteq> None" for i :: nat
    proof -
      let ?f = "\<lambda>j. f (Suc (i + j))"
      have confl: "conflicting (f x) \<noteq> None" if "x > i" for x :: nat
        using confl that by auto
      have [iff]: "\<not>propagate (?f j) S" "\<not>decide (?f j) S" "\<not>conflict (?f j) S"
        for j :: nat and S :: 'st
        using confl[of "i+j+1"] by (auto elim!: rulesE)
      have [iff]: "\<not> backtrack (f (Suc (i + j))) (f (Suc (Suc (i + j))))" for j :: nat
        using confl[of "i+j+2"] by (auto elim!: rulesE)
      have "cdcl\<^sub>W_bj (?f j) (?f (Suc j))" for j :: nat
        using f[of "i+j+1"] confl that by (auto simp: cdcl\<^sub>W.simps cdcl\<^sub>W_o.simps elim: rulesE)

      then have "(?f (Suc j), ?f j) \<in> {(T, S). cdcl\<^sub>W_all_struct_inv S \<and> cdcl\<^sub>W_bj S T}"
        for j :: nat
        using f[of "i+j+1"] by auto
      then show False
        using wf_cdcl\<^sub>W_bj_all_struct unfolding wf_iff_no_infinite_down_chain by fast
    qed

  then have [simp]: "\<exists>x>i. conflicting (f x) = None" for i :: nat
    by meson
  have "{j. j > i \<and> conflicting (f j) \<noteq> None} \<noteq> {}" for i :: nat
    using not_conflicting_none by (rule ccontr) auto

  define g where g: "g = rec_nat i\<^sub>0 (\<lambda>_ i. LEAST j. j > i \<and> conflicting (f j) = None)"
  have g_0: "g 0 = i\<^sub>0"
    unfolding g by auto
  have g_Suc: "g (Suc i) = (LEAST j. j > g i \<and> conflicting (f j) = None)" for i
    unfolding g by auto
  have g_prop:"g (Suc i) > g i \<and> conflicting (f (g (Suc i))) = None" for i
    proof (cases i)
      case 0
      then show ?thesis
        using LeastI_ex[of "\<lambda>j. j > i\<^sub>0 \<and> conflicting (f j) = None"]
        by (auto simp: g)[]
    next
      case (Suc i')
      then show ?thesis
        apply (subst g_Suc, subst g_Suc)
        using LeastI_ex[of "\<lambda>j. j > g (Suc i') \<and> conflicting (f j) = None"]
        by auto
    qed
  then have g_increasing: "g (Suc i) > g i" for i :: nat by simp
  have confl_f_G[simp]: "conflicting (f (g i)) = None" for i :: nat
    by (cases i) (auto simp: g_prop g_0 confl_i\<^sub>0)
  have [simp]: "cdcl\<^sub>W_M_level_inv (f i)" "cdcl\<^sub>W_all_struct_inv (f i)" for i :: nat
    using f[of i] by (auto simp: cdcl\<^sub>W_all_struct_inv_def)
  let ?fg = "\<lambda>i. (f (g i))"
  have "\<forall>i < Suc j. (f (g (Suc i)), f (g i)) \<in> {(T, S). cdcl\<^sub>W_all_struct_inv S \<and> cdcl\<^sub>W_merge\<^sup>+\<^sup>+ S T}"
    for j :: nat
    proof (induction j)
      case 0
      have "cdcl\<^sub>W\<^sup>+\<^sup>+ (?fg 0) (?fg 1)"
        using g_increasing[of 0] by (simp add: st)
      then show ?case by (auto dest!: trancl_cdcl\<^sub>W_conflicting_true_cdcl\<^sub>W_merge_restart)
    next
      case (Suc j) note IH = this(1)
      let ?i = "g (Suc j)"
      let ?j = "g (Suc (Suc j))"
      have "conflicting (f ?i) = None"
        by auto
      moreover have "cdcl\<^sub>W_all_struct_inv (f ?i)"
        by auto
      ultimately  have "cdcl\<^sub>W\<^sup>+\<^sup>+ (f ?i) (f ?j)"
        using g_increasing by (simp add: st)
      then have "cdcl\<^sub>W_merge\<^sup>+\<^sup>+ (f ?i) (f ?j)"
        by (auto dest!: trancl_cdcl\<^sub>W_conflicting_true_cdcl\<^sub>W_merge_restart)
      then show ?case using IH not_less_less_Suc_eq by auto
    qed
  then have "\<forall>i. (f (g (Suc i)), f (g i)) \<in> {(T, S). cdcl\<^sub>W_all_struct_inv S \<and> cdcl\<^sub>W_merge\<^sup>+\<^sup>+ S T}"
    by blast
  then show False
    using wf_tranclp_cdcl\<^sub>W_merge unfolding wf_iff_no_infinite_down_chain by fast
qed

end

end

