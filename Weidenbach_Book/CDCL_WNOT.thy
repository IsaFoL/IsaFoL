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
  by (auto simp: comp_def no_dup_def)

lemma convert_trail_from_W_true_annots[simp]:
  "convert_trail_from_W M \<Turnstile>as C \<longleftrightarrow> M \<Turnstile>as C"
  by (auto simp: true_annots_true_cls image_image lits_of_def)

lemma defined_lit_convert_trail_from_W[simp]:
  "defined_lit (convert_trail_from_W S) = defined_lit S"
  by (auto simp: defined_lit_map image_comp intro!: ext)

lemma is_decided_convert_trail_from_W[simp]:
  \<open>is_decided (convert_ann_lit_from_W L) = is_decided L\<close>
  by (cases L) auto

lemma count_decided_conver_Trail_from_W[simp]:
  \<open>count_decided (convert_trail_from_W M) = count_decided M\<close>
  unfolding count_decided_def by (auto simp: comp_def)

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
  propagate_conds = "\<lambda>_ _ _. True" and
  forget_conds =  "\<lambda>_ S. conflicting S = None" and
  backjump_l_cond = "\<lambda>C C' L' S T. backjump_l_cond C C' L' S T
    \<and> distinct_mset C' \<and> L' \<notin># C' \<and> \<not>tautology (add_mset L' C')"
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
  propagate_conds = "\<lambda>_ _ _. True" and
  forget_conds =  "\<lambda>_ S. conflicting S = None" and
  backjump_l_cond = backjump_l_cond and
  inv = inv\<^sub>N\<^sub>O\<^sub>T
  by unfold_locales

sublocale conflict_driven_clause_learning\<^sub>W \<subseteq> cdcl\<^sub>N\<^sub>O\<^sub>T_merge_bj_learn where
  trail = "\<lambda>S. convert_trail_from_W (trail S)" and
  clauses\<^sub>N\<^sub>O\<^sub>T = clauses and
  prepend_trail = "\<lambda>L S. cons_trail (convert_ann_lit_from_NOT L) S" and
  tl_trail = "\<lambda>S. tl_trail S" and
  add_cls\<^sub>N\<^sub>O\<^sub>T = "\<lambda>C S. add_learned_cls C S" and
  remove_cls\<^sub>N\<^sub>O\<^sub>T = "\<lambda>C S. remove_cls C S" and
  decide_conds = "\<lambda>_ _. True" and
  propagate_conds = "\<lambda>_ _ _. True" and
  forget_conds =  "\<lambda>_ S. conflicting S = None" and
  backjump_l_cond = backjump_l_cond and
  inv = inv\<^sub>N\<^sub>O\<^sub>T
proof (unfold_locales, goal_cases)
  case 2
  then show ?case using cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_no_dup_inv by (auto simp: comp_def)
next
  case (1 C' S C F' K F L)
    let ?C' = "remdups_mset C'"
    have "L \<notin># C'"
      using \<open>F \<Turnstile>as CNot C'\<close> \<open>undefined_lit F L\<close> Decided_Propagated_in_iff_in_lits_of_l
      in_CNot_implies_uminus(2) by fast
    then have dist: "distinct_mset ?C'" "L \<notin># C'"
      by simp_all

    have "no_dup F"
      using \<open>inv\<^sub>N\<^sub>O\<^sub>T S\<close> \<open>convert_trail_from_W (trail S) = F' @ Decided K # F\<close>
      unfolding inv\<^sub>N\<^sub>O\<^sub>T_def by (metis no_dup_appendD no_dup_cons no_dup_convert_from_W)
    then have "consistent_interp (lits_of_l F)"
      using distinct_consistent_interp by blast
    then have "\<not> tautology C'"
      using \<open>F \<Turnstile>as CNot C'\<close> consistent_CNot_not_tautology true_annots_true_cls by blast
    then have taut: "\<not> tautology (add_mset L ?C')"
      using \<open>F \<Turnstile>as CNot C'\<close> \<open>undefined_lit F L\<close> by (metis CNot_remdups_mset
          Decided_Propagated_in_iff_in_lits_of_l in_CNot_uminus tautology_add_mset
          tautology_remdups_mset true_annot_singleton true_annots_def)

    have f2: "no_dup (convert_trail_from_W (trail S))"
      using \<open>inv\<^sub>N\<^sub>O\<^sub>T S\<close> unfolding inv\<^sub>N\<^sub>O\<^sub>T_def by (simp add: o_def)
    have f3: "atm_of L \<in> atms_of_mm (clauses S)
      \<union> atm_of ` lits_of_l (convert_trail_from_W (trail S))"
      using \<open>convert_trail_from_W (trail S) = F' @ Decided K # F\<close>
        \<open>atm_of L \<in> atms_of_mm (clauses S) \<union> atm_of ` lits_of_l (F' @ Decided K # F)\<close> by auto
    have f4: "clauses S \<Turnstile>pm add_mset L ?C'"
      by (metis "1"(7) dist(2) remdups_mset_singleton_sum true_clss_cls_remdups_mset)
    have "F \<Turnstile>as CNot ?C'"
      by (simp add: \<open>F \<Turnstile>as CNot C'\<close>)
    have "Ex (backjump_l S)"
      apply standard
      apply (rule backjump_l.intros[of _ _ _ _ _ L "add_mset L ?C'" _ ?C'])
      using f4 f3 f2 \<open>\<not> tautology (add_mset L ?C')\<close>
        1 taut dist \<open>F \<Turnstile>as CNot (remdups_mset C')\<close>
        state_eq\<^sub>N\<^sub>O\<^sub>T_ref unfolding backjump_l_cond_def set_mset_remdups_mset by blast+
    then show ?case
      by blast
next
  case (3 L S)
  then show "\<exists>T. decide\<^sub>N\<^sub>O\<^sub>T S T \<or> propagate\<^sub>N\<^sub>O\<^sub>T S T \<or> backjump_l S T"
    using decide\<^sub>N\<^sub>O\<^sub>T.intros[of S L] by auto
qed


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
    "init_clss S = init_clss T"
    "learned_clss S = learned_clss T"
  using assms
proof (induction rule: rtranclp_induct)
  case base
  case 1 show ?case by simp
  case 2 show ?case by simp
  case 3 show ?case by simp
  case 4 show ?case by simp
  case 5 show ?case by simp
next
  case (step T U) note st = this(1) and s_o_r = this(2) and IH = this(3) and IH' = this(3-)

  case 2 show ?case using IH' s_o_r by (auto elim!: rulesE simp: skip_or_resolve.simps)
  case 3 show ?case using IH' s_o_r by (cases \<open>trail T\<close>) (auto elim!: rulesE simp: skip_or_resolve.simps)
  case 1 show ?case
    using s_o_r IH by (cases "trail T") (auto elim!: rulesE simp: skip_or_resolve.simps)
  case 4 show ?case
    using s_o_r IH' by (cases "trail T") (auto elim!: rulesE simp: skip_or_resolve.simps)
  case 5 show ?case
    using s_o_r IH' by (cases "trail T") (auto elim!: rulesE simp: skip_or_resolve.simps)
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
  then obtain M N U L C where
    H: "state_butlast S = (M, N, U, None)" and
    CL: "C + {#L#} \<in># clauses S" and
    M_C: "M \<Turnstile>as CNot C" and
    undef: "undefined_lit (trail S) L" and
    T: "state_butlast T = (Propagated L (C + {#L#}) # M, N, U, None)"
    by (auto elim: propagate_high_levelE)
  have "propagate\<^sub>N\<^sub>O\<^sub>T S T"
    using H CL T undef M_C by (auto simp: state_eq\<^sub>N\<^sub>O\<^sub>T_def clauses_def simp del: state_simp)
  then show ?case
    using cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn.intros(2) by blast
next
  case (fw_decide S T) note dec = this(1) and inv = this(2)
  then obtain L where
    undef_L: "undefined_lit (trail S) L" and
    atm_L: "atm_of L \<in> atms_of_mm (init_clss S)" and
    T: "T \<sim> cons_trail (Decided L) S"
    by (auto elim: decideE)
  have "decide\<^sub>N\<^sub>O\<^sub>T S T"
    apply (rule decide\<^sub>N\<^sub>O\<^sub>T.decide\<^sub>N\<^sub>O\<^sub>T)
       using undef_L apply (simp; fail)
     using atm_L inv apply (auto simp: cdcl\<^sub>W_all_struct_inv_def no_strange_atm_def clauses_def; fail)
    using T undef_L unfolding state_eq\<^sub>N\<^sub>O\<^sub>T_def by (auto simp: clauses_def)
  then show ?case using cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_decide\<^sub>N\<^sub>O\<^sub>T by blast
next
  case (fw_forget S T) note rf = this(1) and inv = this(2)
  then obtain C where
     S: "conflicting S = None" and
     C_le: "C \<in># learned_clss S" and
     "\<not>(trail S) \<Turnstile>asm clauses S" and
     "C \<notin> set (get_all_mark_of_propagated (trail S))" and
     C_init: "C \<notin># init_clss S" and
     T: "T \<sim> remove_cls C S" and
     S_C: \<open>removeAll_mset C (clauses S) \<Turnstile>pm C\<close>
    by (auto elim: forgetE)
  have "forget\<^sub>N\<^sub>O\<^sub>T S T"
    apply (rule forget\<^sub>N\<^sub>O\<^sub>T.forget\<^sub>N\<^sub>O\<^sub>T)
       using S_C apply blast
      using S apply simp
     using C_init C_le apply (simp add: clauses_def)
    using T C_le C_init by (auto simp: Un_Diff state_eq\<^sub>N\<^sub>O\<^sub>T_def clauses_def ac_simps)
  then show ?case using cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_forget\<^sub>N\<^sub>O\<^sub>T by blast
next
  case (fw_conflict S T U) note confl = this(1) and bj = this(2) and inv = this(3)
  obtain C\<^sub>S CT where
    confl_T: "conflicting T = Some CT" and
    CT: "CT = C\<^sub>S" and
    C\<^sub>S: "C\<^sub>S \<in># clauses S" and
    tr_S_C\<^sub>S: "trail S \<Turnstile>as CNot C\<^sub>S"
    using confl by (elim conflictE) auto
  have inv_T: "cdcl\<^sub>W_all_struct_inv T"
    using cdcl\<^sub>W_restart.simps cdcl\<^sub>W_all_struct_inv_inv confl inv by blast
  then have "cdcl\<^sub>W_M_level_inv T"
    unfolding cdcl\<^sub>W_all_struct_inv_def by auto
  then consider
    (no_bt) "skip_or_resolve\<^sup>*\<^sup>* T U" |
    (bt) T' where "skip_or_resolve\<^sup>*\<^sup>* T T'" and "backtrack T' U"
    using bj rtranclp_cdcl\<^sub>W_bj_skip_or_resolve_backtrack unfolding full_def by meson
  then show ?case
  proof cases
    case no_bt
    then have "conflicting U \<noteq> None"
      using confl by (induction rule: rtranclp_induct)
      (auto simp: skip_or_resolve.simps elim!: rulesE)
    moreover then have "no_step cdcl\<^sub>W_merge U"
      by (auto simp: cdcl\<^sub>W_merge.simps elim: rulesE)
    ultimately show ?thesis by blast
  next
    case bt note s_or_r = this(1) and bt = this(2)
    have "cdcl\<^sub>W_restart\<^sup>*\<^sup>* T T'"
      using s_or_r mono_rtranclp[of skip_or_resolve cdcl\<^sub>W_restart]
        rtranclp_skip_or_resolve_rtranclp_cdcl\<^sub>W_restart
      by blast
    then have "cdcl\<^sub>W_M_level_inv T'"
      using rtranclp_cdcl\<^sub>W_restart_consistent_inv \<open>cdcl\<^sub>W_M_level_inv T\<close> by blast
    then obtain M1 M2 i D L K D' where
      confl_T': "conflicting T' = Some (add_mset L D)" and
      M1_M2:"(Decided K # M1, M2) \<in> set (get_all_ann_decomposition (trail T'))" and
      "get_level (trail T') K = i+1"
      "get_level (trail T') L = backtrack_lvl T'" and
      "get_level (trail T') L = get_maximum_level (trail T') (add_mset L D')" and
      "get_maximum_level (trail T') D' = i" and
      U: "U \<sim> cons_trail (Propagated L (add_mset L D'))
               (reduce_trail_to M1
                    (add_learned_cls (add_mset L D')
                      (update_conflicting None T')))" and
      D_D': \<open>D' \<subseteq># D\<close> and
      T'_L_D': \<open>clauses T' \<Turnstile>pm add_mset L D'\<close>
      using bt by (auto elim: backtrackE)
    let ?D' = \<open>add_mset L D'\<close>
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
      using inv_T' confl_T' unfolding cdcl\<^sub>W_all_struct_inv_def no_strange_atm_def
      clauses_def
      by (simp add: atms_of_def image_subset_iff)
    obtain M where tr_T: "trail T = M @ trail T'"
      using s_or_r skip_or_resolve_state_change by meson
    obtain M' where
      tr_T': "trail T' = M' @ Decided K # tl (trail U)" and
      tr_U: "trail U = Propagated L ?D' # tl (trail U)"
      using U M1_M2 inv_T' unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def
      by fastforce
    define M'' where "M'' \<equiv> M @ M'"
    have tr_T: "trail S = M'' @ Decided K # tl (trail U)"
      using tr_T tr_T' confl unfolding M''_def by (auto elim: rulesE)
    have "init_clss T' + learned_clss S \<Turnstile>pm ?D'"
      using inv_T' confl_T' \<open>clauses S = clauses T\<close> \<open>clauses T = clauses T'\<close> T'_L_D'
      unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_learned_clause_def clauses_def by auto
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
    then have U_D: "tl (trail U) \<Turnstile>as CNot D'"
      by (subst tr_U, subst (asm) tr_U) fastforce
    have undef_L: "undefined_lit (tl (trail U)) L"
      using U M1_M2 inv_U unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def
      by (auto simp: lits_of_def defined_lit_map)
    have "backjump_l S U"
      apply (rule backjump_l[of _ _ _ _ _ L ?D' _ "D'"])
               using tr_T apply (simp; fail)
              using U M1_M2 confl M1_M2 inv_T' inv unfolding cdcl\<^sub>W_all_struct_inv_def
              cdcl\<^sub>W_M_level_inv_def apply (auto simp: state_eq\<^sub>N\<^sub>O\<^sub>T_def
                trail_reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_add_learned_cls; fail)[]
            using C\<^sub>S apply (auto; fail)[]
           using tr_S_C\<^sub>S apply (simp; fail)

          using undef_L apply (auto; fail)[]
         using atm_L apply (simp add: trail_reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_add_learned_cls; fail)
        using \<open>init_clss T' + learned_clss S \<Turnstile>pm ?D'\<close> unfolding clauses_def
        apply (simp; fail)
       apply (simp; fail)
      apply (metis U_D convert_trail_from_W_true_annots)
      using inv_T' inv_U U confl_T' undef_L M1_M2 unfolding cdcl\<^sub>W_all_struct_inv_def
      distinct_cdcl\<^sub>W_state_def by (auto simp: cdcl\<^sub>W_M_level_inv_decomp backjump_l_cond_def
          dest: multi_member_split)
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
    (fw) "cdcl\<^sub>W_merge S T" |
    (fw_r) "restart S T"
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
    (merged) "cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn S T"  |
    (n_s) "no_step cdcl\<^sub>W_merge T"
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
    moreover have "conflicting U = None" and "conflicting V = None"
      using W_propagate by (auto elim: propagateE)
    ultimately show ?thesis using IH cdcl\<^sub>W_merge.fw_propagate[of U V] by auto
  next
    case W_conflict
    moreover have confl_U: "conflicting U = None" and confl_V: "conflicting V \<noteq> None"
      using W_conflict by (auto elim!: conflictE)
    moreover have "cdcl\<^sub>W_merge\<^sup>*\<^sup>* S U"
      using IH confl_U by auto
    ultimately show ?thesis using IH by auto
  next
    case W_other
    then show ?thesis
    proof cases
      case decide
      then show ?thesis using IH cdcl\<^sub>W_merge.fw_decide[of U V] by (auto elim: decideE)
    next
      case bj
      then consider
        (s_or_r) "skip_or_resolve U V" |
        (bt) "backtrack U V"
        by (auto simp: cdcl\<^sub>W_bj.simps)
      then show ?thesis
      proof cases
        case s_or_r
        have f1: "cdcl\<^sub>W_bj\<^sup>+\<^sup>+ U V"
          by (simp add: local.bj tranclp.r_into_trancl)
        obtain T T' :: 'st where
          f2: "cdcl\<^sub>W_merge\<^sup>+\<^sup>+ S U
                \<or> cdcl\<^sub>W_merge\<^sup>*\<^sup>* S T \<and> conflicting U \<noteq> None
                  \<and> conflict T T' \<and> cdcl\<^sub>W_bj\<^sup>*\<^sup>* T' U"
          using IH confl by (meson bj rtranclp.intros(1)
              rtranclp_cdcl\<^sub>W_merge_restart_no_step_cdcl\<^sub>W_bj
              rtranclp_cdcl\<^sub>W_merge_tranclp_cdcl\<^sub>W_merge_restart)
        have "conflicting V \<noteq> None \<and> conflicting U \<noteq> None"
          using \<open>skip_or_resolve U V\<close>
          by (auto simp: skip_or_resolve.simps elim!: skipE resolveE)
        then show ?thesis
          by (metis (full_types) IH f1 rtranclp_trans tranclp_into_rtranclp)
      next
        case bt
        then have "conflicting U \<noteq> None" by (auto elim: backtrackE)
        then obtain T T' where
          "cdcl\<^sub>W_merge\<^sup>*\<^sup>* S T" and
          "conflicting U \<noteq> None" and
          "conflict T T'" and
          "cdcl\<^sub>W_bj\<^sup>*\<^sup>* T' U"
          using IH confl by (meson bj rtranclp.intros(1)
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
        then show ?thesis
          using cdcl\<^sub>W_merge.fw_conflict[of T T' V] \<open>conflict T T'\<close>
            \<open>cdcl\<^sub>W_merge\<^sup>*\<^sup>* S T\<close> \<open>conflicting V = None\<close> by auto
      qed
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
    have "(f (Suc i), f i) \<in> {(T, S). cdcl\<^sub>W_all_struct_inv S \<and> cdcl\<^sub>W_bj S T}" for i
      using f[of i] confl[of i] by (auto simp: cdcl\<^sub>W.simps cdcl\<^sub>W_o.simps cdcl\<^sub>W_rf.simps
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
  ultimately have "i\<^sub>0 \<in> {i\<^sub>0. \<forall>i < i\<^sub>0. conflicting (f i) \<noteq> None}"
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
    ultimately have "cdcl\<^sub>W\<^sup>+\<^sup>+ (f ?i) (f ?j)"
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

lemma wf_cdcl\<^sub>W_stgy:
  \<open>wf {(T, S). cdcl\<^sub>W_all_struct_inv S \<and> cdcl\<^sub>W_stgy S T}\<close>
  by (rule wf_subset[OF wf_cdcl\<^sub>W]) (auto dest: cdcl\<^sub>W_stgy_cdcl\<^sub>W)

end


subsection \<open>Inclusion of Weidendenbch's CDCL with Strategy\<close>

context conflict_driven_clause_learning\<^sub>W
begin
abbreviation propagate_conds where
"propagate_conds \<equiv> \<lambda>_. propagate"

abbreviation (input) decide_conds where
"decide_conds S T \<equiv> decide S T \<and> no_step conflict S \<and> no_step propagate S"

abbreviation backjump_l_conds_stgy :: "'v clause \<Rightarrow> 'v clause \<Rightarrow> 'v literal \<Rightarrow> 'st \<Rightarrow> 'st \<Rightarrow> bool" where
"backjump_l_conds_stgy C C' L S V \<equiv>
  (\<exists>T U. conflict S T \<and> full skip_or_resolve T U \<and> conflicting T = Some C \<and>
    mark_of (hd_trail V) = add_mset L C' \<and> backtrack U V)"

abbreviation inv\<^sub>N\<^sub>O\<^sub>T_stgy where
"inv\<^sub>N\<^sub>O\<^sub>T_stgy S \<equiv> conflicting S = None \<and> cdcl\<^sub>W_all_struct_inv S \<and> no_smaller_propa S \<and>
  cdcl\<^sub>W_stgy_invariant S \<and> propagated_clauses_clauses S"

interpretation cdcl\<^sub>W_with_strategy: cdcl\<^sub>N\<^sub>O\<^sub>T_merge_bj_learn_ops where
  trail = "\<lambda>S. convert_trail_from_W (trail S)" and
  clauses\<^sub>N\<^sub>O\<^sub>T = clauses and
  prepend_trail = "\<lambda>L S. cons_trail (convert_ann_lit_from_NOT L) S" and
  tl_trail = "\<lambda>S. tl_trail S" and
  add_cls\<^sub>N\<^sub>O\<^sub>T = "\<lambda>C S. add_learned_cls C S" and
  remove_cls\<^sub>N\<^sub>O\<^sub>T = "\<lambda>C S. remove_cls C S" and
  decide_conds = decide_conds and
  propagate_conds = propagate_conds and
  forget_conds =  "\<lambda>_ _. False" and
  backjump_l_cond = "\<lambda>C C' L' S T. backjump_l_conds_stgy C C' L' S T
    \<and> distinct_mset C' \<and> L' \<notin># C' \<and> \<not>tautology (add_mset L' C')"
  by unfold_locales

interpretation cdcl\<^sub>W_with_strategy: cdcl\<^sub>N\<^sub>O\<^sub>T_merge_bj_learn_proxy where
  trail = "\<lambda>S. convert_trail_from_W (trail S)" and
  clauses\<^sub>N\<^sub>O\<^sub>T = clauses and
  prepend_trail = "\<lambda>L S. cons_trail (convert_ann_lit_from_NOT L) S" and
  tl_trail = "\<lambda>S. tl_trail S" and
  add_cls\<^sub>N\<^sub>O\<^sub>T = "\<lambda>C S. add_learned_cls C S" and
  remove_cls\<^sub>N\<^sub>O\<^sub>T = "\<lambda>C S. remove_cls C S" and
  decide_conds = decide_conds and
  propagate_conds = propagate_conds and
  forget_conds =  "\<lambda>_ _. False" and
  backjump_l_cond = backjump_l_conds_stgy and
  inv = inv\<^sub>N\<^sub>O\<^sub>T_stgy
  by unfold_locales

lemma cdcl\<^sub>W_with_strategy_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_conflict:
  assumes
    "cdcl\<^sub>W_with_strategy.cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn S T"
    "conflicting S = None"
  shows
    "conflicting T = None"
  using assms
  apply (cases rule: cdcl\<^sub>W_with_strategy.cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn.cases;
    elim cdcl\<^sub>W_with_strategy.forget\<^sub>N\<^sub>O\<^sub>TE cdcl\<^sub>W_with_strategy.propagate\<^sub>N\<^sub>O\<^sub>TE
    cdcl\<^sub>W_with_strategy.decide\<^sub>N\<^sub>O\<^sub>TE rulesE
    cdcl\<^sub>W_with_strategy.backjump_lE backjumpE)
  apply (auto elim!: rulesE simp: comp_def)
  done

lemma cdcl\<^sub>W_with_strategy_no_forget\<^sub>N\<^sub>O\<^sub>T[iff]: "cdcl\<^sub>W_with_strategy.forget\<^sub>N\<^sub>O\<^sub>T S T \<longleftrightarrow> False"
  by (auto elim: cdcl\<^sub>W_with_strategy.forget\<^sub>N\<^sub>O\<^sub>TE)

lemma cdcl\<^sub>W_with_strategy_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_cdcl\<^sub>W_stgy:
  assumes
    "cdcl\<^sub>W_with_strategy.cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn S V"
  shows
    "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S V"
  using assms
proof (cases rule: cdcl\<^sub>W_with_strategy.cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn.cases)
  case cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_decide\<^sub>N\<^sub>O\<^sub>T
  then show ?thesis
    apply (elim cdcl\<^sub>W_with_strategy.decide\<^sub>N\<^sub>O\<^sub>TE)
    using cdcl\<^sub>W_stgy.other'[of S V] cdcl\<^sub>W_o.decide[of S V] by blast
next
  case cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_propagate\<^sub>N\<^sub>O\<^sub>T
  then show ?thesis
    using cdcl\<^sub>W_stgy.propagate' by (blast elim: cdcl\<^sub>W_with_strategy.propagate\<^sub>N\<^sub>O\<^sub>TE)
next
  case cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_forget\<^sub>N\<^sub>O\<^sub>T
  then show ?thesis
    by blast
next
  case cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_backjump_l
  then obtain T U where
    confl: "conflict S T" and
    full: "full skip_or_resolve T U" and
    bt: "backtrack U V"
    by (elim cdcl\<^sub>W_with_strategy.backjump_lE) blast
  have "cdcl\<^sub>W_bj\<^sup>*\<^sup>* T U"
    using full mono_rtranclp[of skip_or_resolve cdcl\<^sub>W_bj] unfolding full_def
    by (blast elim: skip_or_resolve.cases)
  moreover have "cdcl\<^sub>W_bj U V" and "no_step cdcl\<^sub>W_bj V"
    using bt by (auto dest: backtrack_no_cdcl\<^sub>W_bj)
  ultimately have "full1 cdcl\<^sub>W_bj T V"
    unfolding full1_def by auto
  then have "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* T V"
    using cdcl\<^sub>W_s'.bj'[of T V] cdcl\<^sub>W_s'_is_rtranclp_cdcl\<^sub>W_stgy[of T V] by blast
  then show ?thesis
    using confl cdcl\<^sub>W_stgy.conflict'[of S T] by auto
qed

lemma rtranclp_transition_function:
  \<open>R\<^sup>*\<^sup>* a b \<Longrightarrow> \<exists>f j. (\<forall>i<j. R (f i) (f (Suc i))) \<and> f 0 = a \<and> f j = b\<close>
proof (induction rule: rtranclp_induct)
  case base
  then show ?case by auto
next
  case (step b c) note st = this(1) and R = this(2) and IH = this(3)
  from IH obtain f j where
    i: \<open>\<forall>i<j. R (f i) (f (Suc i))\<close> and
    a: \<open>f 0 = a\<close> and
    b: \<open>f j = b\<close>
    by auto
  let ?f = \<open>f(Suc j := c)\<close>

  have
    i: \<open>\<forall>i<Suc j. R (?f i) (?f (Suc i))\<close> and
    a: \<open>?f 0 = a\<close> and
    b: \<open>?f (Suc j) = c\<close>
    using i a b R by auto
  then show ?case by blast
qed

lemma cdcl\<^sub>W_bj_cdcl\<^sub>W_stgy: \<open>cdcl\<^sub>W_bj S T \<Longrightarrow> cdcl\<^sub>W_stgy S T\<close>
  by (rule cdcl\<^sub>W_stgy.other') (auto simp: cdcl\<^sub>W_bj.simps cdcl\<^sub>W_o.simps elim!: rulesE)

lemma cdcl\<^sub>W_restart_propagated_clauses_clauses:
  \<open>cdcl\<^sub>W_restart S T \<Longrightarrow> propagated_clauses_clauses S \<Longrightarrow> propagated_clauses_clauses T\<close>
  by (induction rule: cdcl\<^sub>W_restart_all_induct) (auto simp: propagated_clauses_clauses_def
      in_get_all_mark_of_propagated_in_trail simp: state_prop)

lemma rtranclp_cdcl\<^sub>W_restart_propagated_clauses_clauses:
  \<open>cdcl\<^sub>W_restart\<^sup>*\<^sup>* S T \<Longrightarrow> propagated_clauses_clauses S \<Longrightarrow> propagated_clauses_clauses T\<close>
  by (induction rule: rtranclp_induct) (auto simp: cdcl\<^sub>W_restart_propagated_clauses_clauses)

lemma rtranclp_cdcl\<^sub>W_stgy_propagated_clauses_clauses:
  \<open>cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> propagated_clauses_clauses S \<Longrightarrow> propagated_clauses_clauses T\<close>
  using rtranclp_cdcl\<^sub>W_restart_propagated_clauses_clauses[of S T]
    rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W_restart by blast

lemma conflicting_clause_bt_lvl_gt_0_backjump:
  assumes
    inv: \<open>inv\<^sub>N\<^sub>O\<^sub>T_stgy S\<close> and
    C: \<open>C \<in># clauses S\<close> and
    tr_C: \<open>trail S \<Turnstile>as CNot C\<close> and
    bt: \<open>backtrack_lvl S > 0\<close>
  shows \<open>\<exists> T U V. conflict S T \<and> full skip_or_resolve T U \<and> backtrack U V\<close>
proof -
  let ?T = "update_conflicting (Some C) S"
  have confl_S_T: "conflict S ?T"
    using C tr_C inv by (auto intro!: conflict_rule)
  have count: "count_decided (trail S) > 0"
    using inv bt unfolding cdcl\<^sub>W_stgy_invariant_def cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def
    by auto
  have \<open>(\<exists>K M'. trail S = M' @ Decided K # M) \<Longrightarrow> D \<in># clauses S \<Longrightarrow> \<not> M \<Turnstile>as CNot D\<close> for M D
    using inv C tr_C unfolding cdcl\<^sub>W_stgy_invariant_def no_smaller_confl_def
    by auto
  from this[OF _ C ] have C_ne: \<open>C \<noteq> {#}\<close>
    using tr_C bt count by (fastforce simp: filter_empty_conv in_set_conv_decomp count_decided_def
        elim!: is_decided_ex_Decided)

  obtain U where
    U: \<open>full skip_or_resolve ?T U\<close>
    by (meson wf_exists_normal_form_full wf_skip_or_resolve)
  then have s_o_r: "skip_or_resolve\<^sup>*\<^sup>* ?T U"
    unfolding full_def by blast
  then obtain C' where C': \<open>conflicting U = Some C'\<close>
    by (induction rule: rtranclp_induct) (auto simp: skip_or_resolve.simps elim: rulesE)
  have \<open>cdcl\<^sub>W_stgy\<^sup>*\<^sup>* ?T U\<close>
    using s_o_r by induction
      (auto simp: skip_or_resolve.simps dest!: cdcl\<^sub>W_bj.intros cdcl\<^sub>W_bj_cdcl\<^sub>W_stgy)
  then have \<open>cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S U\<close>
    using confl_S_T by (auto dest!: cdcl\<^sub>W_stgy.intros)
  then have
    inv_U: \<open>cdcl\<^sub>W_all_struct_inv U\<close> and
    no_smaller_U: \<open>no_smaller_propa U\<close> and
    inv_stgy_U: \<open>cdcl\<^sub>W_stgy_invariant U\<close>
    using inv rtranclp_cdcl\<^sub>W_stgy_cdcl\<^sub>W_all_struct_inv rtranclp_cdcl\<^sub>W_stgy_no_smaller_propa
    rtranclp_cdcl\<^sub>W_stgy_cdcl\<^sub>W_stgy_invariant by blast+
  show ?thesis
  proof (cases C')
    case (add L D)
    then obtain V where \<open>cdcl\<^sub>W_stgy U V\<close>
      using conflicting_no_false_can_do_step[of U C'] C' inv_U inv_stgy_U
      unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_stgy_invariant_def
      by (auto simp del: conflict_is_false_with_level_def)
    then have \<open>backtrack U V\<close>
      using C' U unfolding full_def
      by (auto simp: cdcl\<^sub>W_stgy.simps cdcl\<^sub>W_o.simps cdcl\<^sub>W_bj.simps elim: rulesE)
    then show ?thesis
      using U confl_S_T by blast
  next
    case [simp]: empty
    obtain f j where
      f_s_o_r: \<open>i<j \<Longrightarrow> skip_or_resolve (f i) (f (Suc i))\<close> and
      f_0: \<open>f 0 = ?T\<close> and
      f_j: \<open>f j = U\<close> for i
      using rtranclp_transition_function[OF s_o_r] by blast
    have j_0: \<open>j \<noteq> 0\<close>
      using C' f_j C_ne f_0 by (cases j) auto

    have bt_lvl_f_l: \<open>backtrack_lvl (f k) = backtrack_lvl (f 0)\<close> if \<open>k \<le> j\<close> for k
      using that
    proof (induction k)
      case 0
      then show ?case by (simp add: f_0)
    next
      case (Suc k)
      then have \<open>backtrack_lvl (f (Suc k)) = backtrack_lvl (f k)\<close>
        apply (cases \<open>k < j\<close>; cases \<open>trail (f k)\<close>)
        using f_s_o_r[of k] apply (auto simp: skip_or_resolve.simps elim!: rulesE)[2]
        by (auto simp: skip_or_resolve.simps elim!: rulesE simp del: local.state_simp)
      then show ?case
        using f_s_o_r[of k] Suc by simp
    qed

    have st_f: \<open>cdcl\<^sub>W_stgy\<^sup>*\<^sup>* ?T (f k)\<close> if \<open>k < j\<close> for k
      using that
    proof (induction k)
      case 0
      then show ?case by (simp add: f_0)
    next
      case (Suc k)
      then show ?case
        apply (cases \<open>k < j\<close>)
        using f_s_o_r[of k] apply (auto simp: skip_or_resolve.simps
            dest!: cdcl\<^sub>W_bj.intros cdcl\<^sub>W_bj_cdcl\<^sub>W_stgy)[]
        using f_s_o_r[of "j - 1"] j_0 by (simp del: local.state_simp)
    qed note st_f_T = this(1)
    have st_f_s_k: \<open>cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S (f k)\<close> if \<open>k < j\<close> for k
      using confl_S_T that st_f_T[of k] by (auto dest!: cdcl\<^sub>W_stgy.intros)
    have f_confl: "conflicting (f k) \<noteq> None" if \<open>k \<le> j\<close> for k
      using that f_s_o_r[of k] f_j C'
      by (auto simp: skip_or_resolve.simps le_eq_less_or_eq elim!: rulesE)
    have \<open>size (the (conflicting (f j))) = 0\<close>
      using f_j C' by simp
    moreover have \<open>size (the (conflicting (f 0))) > 0\<close>
      using C_ne f_0 by (cases C) auto
    then have \<open>\<exists>x\<in>set [0..<Suc j]. 0 < size (the (conflicting (f x)))\<close>
      by force
    ultimately obtain ys l zs where
      \<open>[0..<Suc j] = ys @ l # zs\<close> and
      \<open>0 < size (the (conflicting (f l)))\<close> and
      \<open>\<forall>z\<in>set zs. \<not> 0 < size (the (conflicting (f z)))\<close>
      using split_list_last_prop[of "[0..<Suc j]" "\<lambda>i. size (the (conflicting (f i))) > 0"]
      by blast
    moreover have \<open>l < j\<close>
      by (metis C' Suc_le_lessD \<open>C' = {#}\<close> append1_eq_conv append_cons_eq_upt_length_i_end
          calculation(1) calculation(2) f_j le_eq_less_or_eq neq0_conv option.sel
          size_eq_0_iff_empty upt_Suc)
    ultimately have \<open>size (the (conflicting (f (Suc l)))) = 0\<close>
      by (metis (no_types, hide_lams) \<open>size (the (conflicting (f j))) = 0\<close> append1_eq_conv
          append_cons_eq_upt_length_i_end less_eq_nat.simps(1) list.exhaust list.set_intros(1)
          neq0_conv upt_Suc upt_eq_Cons_conv)
    then have confl_Suc_l: \<open>conflicting (f (Suc l)) = Some {#}\<close>
      using f_confl[of "Suc l"] \<open>l < j\<close>  by (cases \<open>conflicting (f (Suc l))\<close>) auto
    let ?T' = \<open>f l\<close>
    let ?T'' = \<open>f (Suc l)\<close>
    have res: \<open>resolve ?T' ?T''\<close>
      using confl_Suc_l \<open>0 < size (the (conflicting (f l)))\<close> f_s_o_r[of l] \<open>l < j\<close>
      by (auto simp: skip_or_resolve.simps elim: rulesE)
    then have confl_T': \<open>size (the (conflicting (f l))) = 1\<close>
      using confl_Suc_l by (auto elim!: rulesE
          simp: Diff_eq_empty_iff_mset subset_eq_mset_single_iff)

    then have "size (mark_of (hd (trail ?T'))) = 1" and hd_t'_dec:"\<not>is_decided (hd (trail ?T'))"
      and tr_T'_ne: \<open>trail ?T' \<noteq> []\<close>
      using res C' confl_Suc_l
      by (auto elim!: resolveE simp: Diff_eq_empty_iff_mset subset_eq_mset_single_iff)
    then obtain L where L: "mark_of (hd (trail ?T')) = {#L#}"
      by (cases "hd (trail ?T')"; cases "mark_of (hd (trail ?T'))") auto
    have
      inv_f_l: \<open>cdcl\<^sub>W_all_struct_inv (f l)\<close> and
      no_smaller_f_l: \<open>no_smaller_propa (f l)\<close> and
      inv_stgy_f_l: \<open>cdcl\<^sub>W_stgy_invariant (f l)\<close> and
      propa_cls_f_l: \<open>propagated_clauses_clauses (f l)\<close>
      using inv st_f_s_k[OF \<open>l < j\<close>] rtranclp_cdcl\<^sub>W_stgy_cdcl\<^sub>W_all_struct_inv[of S "f l"]
        rtranclp_cdcl\<^sub>W_stgy_no_smaller_propa[of S "f l"]
        rtranclp_cdcl\<^sub>W_stgy_cdcl\<^sub>W_stgy_invariant[of S "f l"]
        rtranclp_cdcl\<^sub>W_stgy_propagated_clauses_clauses
      by blast+

    have hd_T': \<open>hd (trail ?T') = Propagated L {#L#}\<close>
      using inv_f_l L tr_T'_ne hd_t'_dec unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_conflicting_def
      by (cases "trail ?T'"; cases "(hd (trail ?T'))") force+
    let ?D = "mark_of (hd (trail ?T'))"
    have \<open>get_level (trail (f l)) L = 0\<close>
      using propagate_single_literal_clause_get_level_is_0[of "f l" L]
        propa_cls_f_l no_smaller_f_l hd_T' inv_f_l
      unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def
      by (cases \<open>trail (f l)\<close>) auto
    then have \<open>count_decided (trail ?T') = 0\<close>
      using hd_T' by (cases \<open>trail (f l)\<close>) auto
    then have \<open>backtrack_lvl ?T' = 0\<close>
      using inv_f_l unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def
      by auto
    then show ?thesis
      using bt bt_lvl_f_l[of l] \<open>l < j\<close> confl_S_T by (auto simp: f_0 elim: rulesE)
  qed
qed

lemma conflict_full_skip_or_resolve_backtrack_backjump_l:
  assumes
    conf: \<open>conflict S T\<close> and
    full: \<open>full skip_or_resolve T U\<close> and
    bt: \<open>backtrack U V\<close> and
    inv: \<open>cdcl\<^sub>W_all_struct_inv S\<close>
  shows \<open>cdcl\<^sub>W_with_strategy.backjump_l S V\<close>
proof -
  have inv_U: \<open>cdcl\<^sub>W_all_struct_inv U\<close>
    by (metis cdcl\<^sub>W_stgy.conflict' cdcl\<^sub>W_stgy_cdcl\<^sub>W_all_struct_inv
        conf full full_def inv rtranclp_cdcl\<^sub>W_all_struct_inv_inv
        rtranclp_skip_or_resolve_rtranclp_cdcl\<^sub>W_restart)
  then have inv_V: \<open>cdcl\<^sub>W_all_struct_inv V\<close>
    by (metis backtrack bt cdcl\<^sub>W_bj_cdcl\<^sub>W_stgy cdcl\<^sub>W_stgy_cdcl\<^sub>W_all_struct_inv)
  obtain C where
    C_S: \<open>C \<in># clauses S\<close> and
    S_Not_C: \<open>trail S \<Turnstile>as CNot C\<close> and
    tr_T_S: \<open>trail T = trail S\<close> and
    T: \<open>T \<sim> update_conflicting (Some C) S\<close> and
    clss_T_S: \<open>clauses T = clauses S\<close>
    using conf by (auto elim: rulesE)
  have s_o_r: \<open>skip_or_resolve\<^sup>*\<^sup>* T U\<close>
    using full unfolding full_def by blast
  then have
    \<open>\<exists>M. trail T = M @ trail U\<close> and
    bt_T_U: \<open>backtrack_lvl T = backtrack_lvl U\<close> and
    bt_lvl_T_U: \<open>backtrack_lvl T = backtrack_lvl U\<close> and
    clss_T_U: \<open>clauses T = clauses U\<close> and
    init_T_U: \<open>init_clss T = init_clss U\<close> and
    learned_T_U: \<open>learned_clss T = learned_clss U\<close>
    using skip_or_resolve_state_change[of T U] by blast+
  then obtain M where M: \<open>trail T = M @ trail U\<close>
    by blast
  obtain D D' :: "'v clause" and K L :: "'v literal" and
    M1 M2 :: "('v, 'v clause) ann_lit list" and i :: nat where
    confl_D: "conflicting U = Some (add_mset L D)" and
    decomp: "(Decided K # M1, M2) \<in> set (get_all_ann_decomposition (trail U))" and
    lev_L_U: "get_level (trail U) L = backtrack_lvl U" and
    max_D_L_U: "get_level (trail U) L = get_maximum_level (trail U) (add_mset L D')" and
    i: "get_maximum_level (trail U) D' \<equiv> i" and
    lev_K_U: "get_level (trail U) K = i + 1" and
    V: "V \<sim> cons_trail (Propagated L (add_mset L D'))
        (reduce_trail_to M1
          (add_learned_cls (add_mset L D')
            (update_conflicting None U)))" and
    U_L_D': \<open>clauses U \<Turnstile>pm add_mset L D'\<close> and
    D_D': \<open>D' \<subseteq># D\<close>
    using bt by (auto elim!: rulesE)
  let ?D' = \<open>add_mset L D'\<close>
  obtain M' where M': \<open>trail U = M' @ M2 @ Decided K # M1\<close>
    using decomp by auto
  have \<open>clauses V = {#?D'#} + clauses U\<close>
    using V by auto
  moreover have \<open>trail V = (Propagated L ?D') # trail (reduce_trail_to M1 U)\<close>
    using V T M tr_T_S[symmetric] M' clss_T_U[symmetric] unfolding state_eq\<^sub>N\<^sub>O\<^sub>T_def
    by (auto simp del: state_simp dest!: state_simp(1))
  ultimately have V': \<open>V \<sim>\<^sub>N\<^sub>O\<^sub>T
    cons_trail (Propagated L dummy_cls) (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T M1 (add_learned_cls ?D' S))\<close>
    using V T M tr_T_S[symmetric] M' clss_T_U[symmetric] unfolding state_eq\<^sub>N\<^sub>O\<^sub>T_def
    by (auto simp del: state_simp
        simp: trail_reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_drop drop_map drop_tl clss_T_S)
  have \<open>no_dup (trail V)\<close>
    using inv_V V unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def by blast
  then have undef_L: \<open>undefined_lit M1 L\<close>
    using V decomp by (auto simp: defined_lit_map)

  have \<open>atm_of L \<in> atms_of_mm (init_clss V)\<close>
    using inv_V V decomp unfolding cdcl\<^sub>W_all_struct_inv_def no_strange_atm_def by auto
  moreover have init_clss_VU_S: \<open>init_clss V = init_clss S\<close>
    \<open>init_clss U = init_clss S\<close>\<open>learned_clss U = learned_clss S\<close>
    using T V init_T_U learned_T_U by auto
  ultimately have atm_L: \<open>atm_of L \<in> atms_of_mm (clauses S)\<close>
    by (auto simp: clauses_def)



  have \<open>distinct_mset ?D'\<close> and \<open>\<not> tautology ?D'\<close>
     using inv_U confl_D decomp D_D' unfolding cdcl\<^sub>W_all_struct_inv_def distinct_cdcl\<^sub>W_state_def
     apply simp_all
     using inv_V V not_tautology_mono[OF D_D'] distinct_mset_mono[OF D_D']
     unfolding cdcl\<^sub>W_all_struct_inv_def
     apply (auto simp add: tautology_add_mset)
    done
  have \<open>L \<notin># D'\<close>
    using \<open>distinct_mset ?D'\<close> by (auto simp: not_in_iff)
  have bj: \<open>backjump_l_conds_stgy C D' L S V\<close>
    apply (rule exI[of _ T], rule exI[of _ U])
    using \<open>distinct_mset ?D'\<close> \<open>\<not> tautology ?D'\<close> conf full bt confl_D
      \<open>L \<notin># D'\<close> V T
    by (auto)

  have M1_D': "M1 \<Turnstile>as CNot D'"
    using backtrack_M1_CNot_D'[of U D' \<open>i\<close> K M1 M2 L \<open>add_mset L D\<close> V \<open>Propagated L (add_mset L D')\<close>]
      inv_U confl_D decomp lev_L_U max_D_L_U i lev_K_U V U_L_D' D_D'
    unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_conflicting_def cdcl\<^sub>W_M_level_inv_def
    by (auto simp: subset_mset_trans_add_mset)
  show ?thesis
    apply (rule cdcl\<^sub>W_with_strategy.backjump_l.intros[of S _ K
          "convert_trail_from_W M1" _ L _ C D'])
             apply (simp add: tr_T_S[symmetric] M' M; fail)
            using V' apply (simp; fail)
           using C_S apply (simp; fail)
          using S_Not_C apply (simp; fail)
         using undef_L apply (simp; fail)
        using atm_L apply (simp; fail)
       using U_L_D' init_clss_VU_S apply (simp add: clauses_def; fail)
      apply (simp; fail)
     using M1_D' apply (simp; fail)
    using bj \<open>distinct_mset ?D'\<close> \<open>\<not> tautology ?D'\<close> by auto
qed

lemma is_decided_o_convert_ann_lit_from_W[simp]:
  \<open>is_decided o convert_ann_lit_from_W = is_decided\<close>
  apply (rule ext)
  apply (rename_tac x, case_tac x)
  apply (auto simp: comp_def)
  done

lemma cdcl\<^sub>W_with_strategy_propagate\<^sub>N\<^sub>O\<^sub>T_propagate_iff[iff]:
  \<open>cdcl\<^sub>W_with_strategy.propagate\<^sub>N\<^sub>O\<^sub>T S T \<longleftrightarrow> propagate S T\<close> (is "?NOT \<longleftrightarrow> ?W")
proof (rule iffI)
  assume ?NOT
  then show ?W by auto
next
  assume ?W
  then obtain E L where
    \<open>conflicting S = None\<close> and
    E: \<open>E \<in># clauses S\<close> and
    LE: \<open>L \<in># E\<close> and
    tr_E: \<open>trail S \<Turnstile>as CNot (remove1_mset L E)\<close> and
    undef: \<open>undefined_lit (trail S) L\<close> and
    T: \<open>T \<sim> cons_trail (Propagated L E) S\<close>
    by (auto elim!: propagateE)
  show ?NOT
    apply (rule cdcl\<^sub>W_with_strategy.propagate\<^sub>N\<^sub>O\<^sub>T[of L \<open>remove1_mset L E\<close>])
        using LE E apply (simp; fail)
       using tr_E apply (simp; fail)
      using undef apply (simp; fail)
     using \<open>?W\<close> apply (simp; fail)
    using T by (simp add: state_eq\<^sub>N\<^sub>O\<^sub>T_def clauses_def)
qed


interpretation cdcl\<^sub>W_with_strategy: cdcl\<^sub>N\<^sub>O\<^sub>T_merge_bj_learn where
  trail = "\<lambda>S. convert_trail_from_W (trail S)" and
  clauses\<^sub>N\<^sub>O\<^sub>T = clauses and
  prepend_trail = "\<lambda>L S. cons_trail (convert_ann_lit_from_NOT L) S" and
  tl_trail = "\<lambda>S. tl_trail S" and
  add_cls\<^sub>N\<^sub>O\<^sub>T = "\<lambda>C S. add_learned_cls C S" and
  remove_cls\<^sub>N\<^sub>O\<^sub>T = "\<lambda>C S. remove_cls C S" and
  decide_conds = decide_conds and
  propagate_conds = propagate_conds and
  forget_conds =  "\<lambda>_ _. False" and
  backjump_l_cond = backjump_l_conds_stgy and
  inv = inv\<^sub>N\<^sub>O\<^sub>T_stgy
proof (unfold_locales, goal_cases)
  case (2 S T)
  then show ?case
    using cdcl\<^sub>W_with_strategy_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_cdcl\<^sub>W_stgy[of S T]
    cdcl\<^sub>W_with_strategy_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_conflict[of S T]
    rtranclp_cdcl\<^sub>W_stgy_cdcl\<^sub>W_all_struct_inv rtranclp_cdcl\<^sub>W_stgy_no_smaller_propa
    rtranclp_cdcl\<^sub>W_stgy_cdcl\<^sub>W_stgy_invariant rtranclp_cdcl\<^sub>W_stgy_propagated_clauses_clauses
    by blast
next
  case (1 C' S C F' K F L)
  have \<open>count_decided (convert_trail_from_W (trail S)) > 0\<close>
    unfolding \<open>convert_trail_from_W (trail S) = F' @ Decided K # F\<close> by simp
  then have \<open>count_decided (trail S) > 0\<close>
    by simp
  then have \<open>backtrack_lvl S > 0\<close>
    using \<open>inv\<^sub>N\<^sub>O\<^sub>T_stgy S\<close> unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def by auto
  have "\<exists>T U V. conflict S T \<and> full skip_or_resolve T U \<and> backtrack U V"
    apply (rule conflicting_clause_bt_lvl_gt_0_backjump)
       using \<open>inv\<^sub>N\<^sub>O\<^sub>T_stgy S\<close> apply (auto; fail)[]
      using \<open>C \<in># clauses S\<close> apply (simp; fail)
     using \<open>convert_trail_from_W (trail S) \<Turnstile>as CNot C\<close> apply (simp; fail)
    using \<open>backtrack_lvl S > 0\<close> by (simp; fail)
  then show ?case
    using conflict_full_skip_or_resolve_backtrack_backjump_l \<open>inv\<^sub>N\<^sub>O\<^sub>T_stgy S\<close> by blast
next
  case (3 L S) note atm = this(1,2) and inv = this(3) and sat = this(4)
  moreover have \<open>Ex(cdcl\<^sub>W_with_strategy.backjump_l S)\<close> if \<open>conflict S T\<close> for T
  proof -
    have \<open>\<exists>C. C \<in># clauses S \<and> trail S \<Turnstile>as CNot C\<close>
      using that by (auto elim: rulesE)
    then obtain C where \<open>C \<in># clauses S\<close> and \<open>trail S \<Turnstile>as CNot C\<close> by blast
    have \<open>backtrack_lvl S > 0\<close>
    proof (rule ccontr)
      assume \<open>\<not> ?thesis\<close>
      then have \<open>backtrack_lvl S = 0\<close>
        by simp
      then have \<open>count_decided (trail S) = 0\<close>
        using inv unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def by simp
      then have \<open>get_all_ann_decomposition (trail S) = [([], trail S)]\<close>
        by (auto simp: filter_empty_conv no_decision_get_all_ann_decomposition count_decided_0_iff)
      then have \<open>set_mset (clauses S) \<Turnstile>ps unmark_l (trail S)\<close>
        using 3(3) unfolding cdcl\<^sub>W_all_struct_inv_def by auto
      obtain I where
        consistent: \<open>consistent_interp I\<close> and
        I_S: \<open>I \<Turnstile>m clauses S\<close> and
        tot: \<open>total_over_m I (set_mset (clauses S))\<close>
        using sat by (auto simp: satisfiable_def)
      have \<open>total_over_m I (set_mset (clauses S)) \<and> total_over_m I (unmark_l (trail S))\<close>
        using tot inv unfolding cdcl\<^sub>W_all_struct_inv_def no_strange_atm_def
        by (auto simp: clauses_def total_over_set_def total_over_m_def)
      then have \<open>I \<Turnstile>s unmark_l (trail S)\<close>
        using \<open>set_mset (clauses S) \<Turnstile>ps unmark_l (trail S)\<close> consistent I_S
        unfolding true_clss_clss_def clauses_def
        by auto

      have \<open>I \<Turnstile>s CNot C\<close>
        by (meson \<open>trail S \<Turnstile>as CNot C\<close> \<open>I \<Turnstile>s unmark_l (trail S)\<close> set_mp true_annots_true_cls
            true_cls_def true_clss_def true_clss_singleton_lit_of_implies_incl true_lit_def)
      moreover have \<open>I \<Turnstile> C\<close>
        using \<open>C \<in># clauses S\<close> and \<open>I \<Turnstile>m clauses S\<close> unfolding true_cls_mset_def by auto
      ultimately show False
        using consistent consistent_CNot_not by blast
    qed
    then show ?thesis
      using conflicting_clause_bt_lvl_gt_0_backjump[of S C]
        conflict_full_skip_or_resolve_backtrack_backjump_l[of S]
        \<open>C \<in># clauses S\<close> \<open>trail S \<Turnstile>as CNot C\<close> inv by fast
  qed
  moreover {
    have atm: \<open>atms_of_mm (clauses S) = atms_of_mm (init_clss S)\<close>
      using 3(3) unfolding cdcl\<^sub>W_all_struct_inv_def no_strange_atm_def
      by (auto simp: clauses_def)
    have \<open>decide S (cons_trail (Decided L) S)\<close>
      apply (rule decide_rule)
      using 3 by (auto simp: atm) }
  moreover have \<open>cons_trail (Decided L) S \<sim>\<^sub>N\<^sub>O\<^sub>T cons_trail (Decided L) S\<close>
    by (simp add: state_eq\<^sub>N\<^sub>O\<^sub>T_def del: state_simp)
  ultimately show "\<exists>T. cdcl\<^sub>W_with_strategy.decide\<^sub>N\<^sub>O\<^sub>T S T \<or>
    cdcl\<^sub>W_with_strategy.propagate\<^sub>N\<^sub>O\<^sub>T S T \<or>
    cdcl\<^sub>W_with_strategy.backjump_l S T"
    using cdcl\<^sub>W_with_strategy.decide\<^sub>N\<^sub>O\<^sub>T.intros[of S L "cons_trail (Decided L) S"]
    by auto
qed

thm cdcl\<^sub>W_with_strategy.full_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_final_state

end

end
