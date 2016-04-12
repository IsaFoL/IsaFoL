theory CDCL_WNOT
imports CDCL_NOT CDCL_W_Termination CDCL_W_Merge
begin

section \<open>Link between Weidenbach's and NOT's CDCL\<close>
subsection \<open>Inclusion of the states\<close>
declare upt.simps(2)[simp del]

fun convert_ann_lit_from_W where
"convert_ann_lit_from_W (Propagated L _) = Propagated L ()" |
"convert_ann_lit_from_W (Decided L _) = Decided L ()"

abbreviation convert_trail_from_W ::
  "('v,  'lvl, 'a) ann_lit list
    \<Rightarrow> ('v, unit, unit) ann_lit list"  where
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
  :: "('a, 'e, 'b) ann_lit \<Rightarrow> ('a, unit, 'cls) ann_lit"  where
"convert_ann_lit_from_NOT (Propagated L _) = Propagated L dummy_cls" |
"convert_ann_lit_from_NOT (Decided L _) = Decided L ()"

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

sublocale state\<^sub>W \<subseteq> dpll_state_ops
   mset_cls
   mset_clss union_clss in_clss insert_clss remove_from_clss
   "\<lambda>S. convert_trail_from_W (trail S)"
   raw_clauses
   "\<lambda>L S. cons_trail (convert_ann_lit_from_NOT L) S"
   "\<lambda>S. tl_trail S"
   "\<lambda>C S. add_learned_cls C S"
   "\<lambda>C S. remove_cls C S"
   by unfold_locales

context state\<^sub>W
begin
lemma convert_ann_lit_from_W_convert_ann_lit_from_NOT[simp]:
  "convert_ann_lit_from_W (mmset_of_mlit (convert_ann_lit_from_NOT L)) = L"
  by (cases L) auto
end

sublocale state\<^sub>W \<subseteq> dpll_state
   mset_cls
   mset_clss union_clss in_clss insert_clss remove_from_clss
   "\<lambda>S. convert_trail_from_W (trail S)"
   raw_clauses
   "\<lambda>L S. cons_trail (convert_ann_lit_from_NOT L) S"
   "\<lambda>S. tl_trail S"
   "\<lambda>C S. add_learned_cls C S"
   "\<lambda>C S. remove_cls C S"
   by unfold_locales (auto simp: map_tl o_def)



context state\<^sub>W
begin
declare state_simp\<^sub>N\<^sub>O\<^sub>T[simp del]

end

sublocale conflict_driven_clause_learning\<^sub>W \<subseteq> cdcl\<^sub>N\<^sub>O\<^sub>T_merge_bj_learn_ops
  mset_cls
  mset_clss union_clss in_clss insert_clss remove_from_clss
  "\<lambda>S. convert_trail_from_W (trail S)"
  raw_clauses
  "\<lambda>L S. cons_trail (convert_ann_lit_from_NOT L) S"
  "\<lambda>S. tl_trail S"
  "\<lambda>C S. add_learned_cls C S"
  "\<lambda>C S. remove_cls C S"
  (* propagate conditions: *)"\<lambda>_ _. True"
  (* forget conditions: *) "\<lambda>_ S. raw_conflicting S = None"
  "\<lambda>C C' L' S T. backjump_l_cond C C' L' S T
    \<and> distinct_mset (C' + {#L'#}) \<and> \<not>tautology (C' + {#L'#})"
  by unfold_locales

thm cdcl\<^sub>N\<^sub>O\<^sub>T_merge_bj_learn_proxy.axioms
sublocale conflict_driven_clause_learning\<^sub>W \<subseteq> cdcl\<^sub>N\<^sub>O\<^sub>T_merge_bj_learn_proxy
  mset_cls
  mset_clss union_clss in_clss insert_clss remove_from_clss
  "\<lambda>S. convert_trail_from_W (trail S)"
  raw_clauses
  "\<lambda>L S. cons_trail (convert_ann_lit_from_NOT L) S"
  "\<lambda>S. tl_trail S"
  "\<lambda>C S. add_learned_cls C S"
  "\<lambda>C S. remove_cls C S"

  "\<lambda>_ _. True"
  "\<lambda>_ S. raw_conflicting S = None"
  backjump_l_cond
  inv\<^sub>N\<^sub>O\<^sub>T
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
      using \<open>inv\<^sub>N\<^sub>O\<^sub>T S\<close> \<open>convert_trail_from_W (trail S) = F' @ Decided K () # F\<close>
      unfolding inv\<^sub>N\<^sub>O\<^sub>T_def
      by (smt comp_apply distinct.simps(2) distinct_append list.simps(9) map_append
        no_dup_convert_from_W)
    then have "consistent_interp (lits_of_l F)"
      using distinct_consistent_interp by blast
    then have "\<not> tautology (C')"
      using \<open>F \<Turnstile>as CNot C'\<close> consistent_CNot_not_tautology true_annots_true_cls by blast
    then have "\<not> tautology (?C' + {#L#})"
      using \<open>F \<Turnstile>as CNot C'\<close> \<open>undefined_lit F L\<close> by (metis  CNot_remdups_mset
        Decided_Propagated_in_iff_in_lits_of_l add.commute in_CNot_uminus tautology_add_single
        tautology_remdups_mset true_annot_singleton true_annots_def)
  show ?case
    proof -
      have f2: "no_dup (convert_trail_from_W (trail S))"
        using \<open>inv\<^sub>N\<^sub>O\<^sub>T S\<close> unfolding inv\<^sub>N\<^sub>O\<^sub>T_def by (simp add: o_def)
      have f3: "atm_of L \<in> atms_of_mm (clauses S)
        \<union> atm_of ` lits_of_l (convert_trail_from_W (trail S))"
        using \<open>convert_trail_from_W (trail S) = F' @ Decided K () # F\<close>
        \<open>atm_of L \<in> atms_of_mm (clauses S) \<union> atm_of ` lits_of_l (F' @ Decided K () # F)\<close> by auto
      have f4: "clauses S \<Turnstile>pm remdups_mset C' + {#L#}"
        by (metis (no_types) \<open>L \<notin># C'\<close> \<open>clauses S \<Turnstile>pm C' + {#L#}\<close> remdups_mset_singleton_sum(2)
          true_clss_cls_remdups_mset union_commute)
      have "F \<Turnstile>as CNot (remdups_mset C')"
        by (simp add: \<open>F \<Turnstile>as CNot C'\<close>)
      obtain D where D: "mset_cls D = remdups_mset C' + {#L#}"
        using ex_mset_cls by blast
      have "Ex (backjump_l S)"
        apply standard
        apply (rule backjump_l.intros[OF  _ f2, of _ _ _ ])
        using f4 f3 f2 \<open>\<not> tautology (remdups_mset C' + {#L#})\<close>
        calculation(2-5,9) \<open>F \<Turnstile>as CNot (remdups_mset C')\<close>
        state_eq\<^sub>N\<^sub>O\<^sub>T_ref D unfolding backjump_l_cond_def by blast+
      then show ?thesis
        by blast
    qed
qed

sublocale conflict_driven_clause_learning\<^sub>W \<subseteq> cdcl\<^sub>N\<^sub>O\<^sub>T_merge_bj_learn_proxy2  _ _ _ _ _ _
  "\<lambda>S. convert_trail_from_W (trail S)"
  raw_clauses
  "\<lambda>L S. cons_trail (convert_ann_lit_from_NOT L) S"
  "\<lambda>S. tl_trail S"
  "\<lambda>C S. add_learned_cls C S"
  "\<lambda>C S. remove_cls C S"
  "\<lambda>_ _. True"
  "\<lambda>_ S. raw_conflicting S = None"  backjump_l_cond inv\<^sub>N\<^sub>O\<^sub>T
  by unfold_locales

sublocale conflict_driven_clause_learning\<^sub>W \<subseteq> cdcl\<^sub>N\<^sub>O\<^sub>T_merge_bj_learn _ _ _ _ _ _
  "\<lambda>S. convert_trail_from_W (trail S)"
  raw_clauses
  "\<lambda>L S. cons_trail (convert_ann_lit_from_NOT L) S"
  "\<lambda>S. tl_trail S"
  "\<lambda>C S. add_learned_cls C S"
  "\<lambda>C S. remove_cls C S"
  backjump_l_cond
  "\<lambda>_ _. True"
  "\<lambda>_ S. raw_conflicting S = None"  inv\<^sub>N\<^sub>O\<^sub>T
  apply unfold_locales
   using dpll_bj_no_dup apply (simp add: comp_def)
  using cdcl\<^sub>N\<^sub>O\<^sub>T.simps cdcl\<^sub>N\<^sub>O\<^sub>T_no_dup no_dup_convert_from_W  unfolding inv\<^sub>N\<^sub>O\<^sub>T_def by blast

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
        using IH by (cases "trail T") (auto elim!: rulesE simp: skip_or_resolve.simps dest!:
        hd_raw_trail)
    qed
qed

subsection \<open>More lemmas conflict--propagate and backjumping\<close>
subsection \<open>CDCL FW\<close>
lemma cdcl\<^sub>W_merge_is_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn:
  assumes
    inv: "cdcl\<^sub>W_all_struct_inv S" and
    cdcl\<^sub>W:"cdcl\<^sub>W_merge S T"
  shows "cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn S T
    \<or> (no_step cdcl\<^sub>W_merge T \<and> conflicting T \<noteq> None)"
  using cdcl\<^sub>W inv
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
    using H CL T undef M_C by (auto simp: state_eq\<^sub>N\<^sub>O\<^sub>T_def state_eq_def raw_clauses_def
      simp del: state_simp)
  then show ?case
    using cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn.intros(2) by blast
next
  case (fw_decide S T) note dec = this(1) and inv = this(2)
  then obtain L where
    undef_L: "undefined_lit (trail S) L" and
    atm_L: "atm_of L \<in> atms_of_mm (init_clss S)" and
    T: "T \<sim> cons_trail (Decided L ())
      (update_backtrack_lvl (Suc (backtrack_lvl S)) S)"
    by (auto elim: decideE)
  have "decide\<^sub>N\<^sub>O\<^sub>T S T"
    apply (rule decide\<^sub>N\<^sub>O\<^sub>T.decide\<^sub>N\<^sub>O\<^sub>T)
       using undef_L apply simp
     using atm_L inv unfolding cdcl\<^sub>W_all_struct_inv_def no_strange_atm_def raw_clauses_def
       apply auto[]
    using T undef_L unfolding state_eq_def state_eq\<^sub>N\<^sub>O\<^sub>T_def by (auto simp: raw_clauses_def)
  then show ?case using cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_decide\<^sub>N\<^sub>O\<^sub>T by blast
next
  case (fw_forget S T) note rf = this(1) and inv = this(2)
  then obtain C where
     S: "conflicting S = None" and
     C_le: "C !\<in>! raw_learned_clss S" and
     "\<not>(trail S) \<Turnstile>asm clauses S" and
     "mset_cls C \<notin> set (get_all_mark_of_propagated (trail S))" and
     C_init: "mset_cls C \<notin># init_clss S" and
     T: "T \<sim> remove_cls C S"
    by (auto elim: forgetE)
  have "init_clss S \<Turnstile>pm mset_cls C"
    using inv C_le unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_learned_clause_def raw_clauses_def
    by (meson in_clss_mset_clss true_clss_clss_in_imp_true_clss_cls)
  then have S_C: "removeAll_mset (mset_cls C) (clauses S) \<Turnstile>pm mset_cls C"
    using C_init C_le unfolding raw_clauses_def by (auto simp add: Un_Diff ac_simps)
  have "forget\<^sub>N\<^sub>O\<^sub>T S T"
    apply (rule forget\<^sub>N\<^sub>O\<^sub>T.forget\<^sub>N\<^sub>O\<^sub>T)
       using S_C apply blast
      using S apply simp
     using C_init C_le apply (simp add: raw_clauses_def)
    using T C_le C_init by (auto
      simp: state_eq_def Un_Diff state_eq\<^sub>N\<^sub>O\<^sub>T_def raw_clauses_def ac_simps
      simp del: state_simp)
  then show ?case using cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_forget\<^sub>N\<^sub>O\<^sub>T by blast
next
  case (fw_conflict S T U) note confl = this(1) and bj = this(2) and inv = this(3)
  obtain C\<^sub>S CT where
    confl_T: "raw_conflicting T = Some CT" and
    CT: "mset_ccls CT = mset_cls C\<^sub>S" and
    C\<^sub>S: "C\<^sub>S !\<in>! raw_clauses S" and
    tr_S_C\<^sub>S: "trail S \<Turnstile>as CNot (mset_cls C\<^sub>S)"
    using confl by (elim conflictE) (auto simp del: state_simp simp: state_eq_def)
  have "cdcl\<^sub>W_all_struct_inv T"
    using cdcl\<^sub>W.simps cdcl\<^sub>W_all_struct_inv_inv confl inv by blast
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
      have "cdcl\<^sub>W\<^sup>*\<^sup>* T T'"
        using s_or_r mono_rtranclp[of skip_or_resolve cdcl\<^sub>W] rtranclp_skip_or_resolve_rtranclp_cdcl\<^sub>W
        by blast
      then have "cdcl\<^sub>W_M_level_inv T'"
        using rtranclp_cdcl\<^sub>W_consistent_inv \<open>cdcl\<^sub>W_M_level_inv T\<close> by blast
      then obtain M1 M2 i D L K where
        confl_T': "raw_conflicting T' = Some D" and
        LD: "L \<in># mset_ccls D" and
        M1_M2:"(Decided K () # M1, M2) \<in> set (get_all_ann_decomposition (trail T'))" and
        "get_level (trail T') K = i+1"
        "get_level (trail T') L = backtrack_lvl T'" and
        "get_level (trail T') L = get_maximum_level (trail T') (mset_ccls D)" and
        "get_maximum_level (trail T') (mset_ccls (remove_clit L D)) = i" and
        undef_L: "undefined_lit M1 L" and
        U: "U \<sim> cons_trail (Propagated L (cls_of_ccls D))
                 (reduce_trail_to M1
                      (add_learned_cls (cls_of_ccls D)
                         (update_backtrack_lvl i
                            (update_conflicting None T'))))"
        using bt by (auto elim: backtrack_levE)
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
      have inv_T: "cdcl\<^sub>W_all_struct_inv T"
        by (meson cdcl\<^sub>W_cp.simps confl inv r_into_rtranclp rtranclp_cdcl\<^sub>W_all_struct_inv_inv
          rtranclp_cdcl\<^sub>W_cp_rtranclp_cdcl\<^sub>W)
      have "cdcl\<^sub>W\<^sup>*\<^sup>* T T'"
        using rtranclp_skip_or_resolve_rtranclp_cdcl\<^sub>W s_or_r by blast
      have inv_T': "cdcl\<^sub>W_all_struct_inv T'"
        using \<open>cdcl\<^sub>W\<^sup>*\<^sup>* T T'\<close> inv_T rtranclp_cdcl\<^sub>W_all_struct_inv_inv by blast
      have inv_U: "cdcl\<^sub>W_all_struct_inv U"
        using cdcl\<^sub>W_merge_restart_cdcl\<^sub>W confl fw_r_conflict inv local.bj
        rtranclp_cdcl\<^sub>W_all_struct_inv_inv by blast

      have [simp]: "init_clss S = init_clss T'"
        using \<open>cdcl\<^sub>W\<^sup>*\<^sup>* T T'\<close> cdcl\<^sub>W_init_clss confl cdcl\<^sub>W_all_struct_inv_def conflict inv
        by (metis \<open>cdcl\<^sub>W_M_level_inv T\<close> rtranclp_cdcl\<^sub>W_init_clss)
      then have atm_L: "atm_of L \<in> atms_of_mm (clauses S)"
        using inv_T' confl_T' LD unfolding cdcl\<^sub>W_all_struct_inv_def no_strange_atm_def
        raw_clauses_def
        by (simp add: atms_of_def image_subset_iff)
      obtain M where tr_T: "trail T = M @ trail T'"
        using s_or_r skip_or_resolve_state_change by meson
      obtain M' where
        tr_T': "trail T' = M' @  Decided K () # tl (trail U)" and
        tr_U: "trail U = Propagated L (mset_ccls D) # tl (trail U)"
        using U M1_M2 undef_L inv_T' unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def
        by fastforce
      def M'' \<equiv> "M @ M'"
      have tr_T: "trail S = M'' @  Decided K () # tl (trail U)"
        using tr_T tr_T' confl unfolding M''_def by (auto elim: rulesE)
      have "init_clss T' + learned_clss S \<Turnstile>pm mset_ccls D"
        using inv_T' confl_T' unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_learned_clause_def
        raw_clauses_def by simp
      have "reduce_trail_to (convert_trail_from_NOT (convert_trail_from_W M1)) S =
        reduce_trail_to M1 S"
        by (rule reduce_trail_to_length) simp
      moreover have "trail (reduce_trail_to M1 S) = M1"
        apply (rule reduce_trail_to_skip_beginning[of _ "M @ _ @ M2 @ [Decided K ()]"])
        using confl M1_M2 \<open>trail T = M @ trail T'\<close>
          apply (auto dest!: get_all_ann_decomposition_exists_prepend
            elim!: conflictE)
          by (rule sym) auto
      ultimately have [simp]: "trail (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T M1 S) = M1"
        using M1_M2 confl by (subst reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_reduce_trail_convert)
        (auto simp: comp_def elim: rulesE)
      have "every_mark_is_a_conflict U"
        using inv_U unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_conflicting_def by simp
      then have U_D: "tl (trail U) \<Turnstile>as CNot (remove1_mset L (mset_ccls D))"
        by (metis append_self_conv2 tr_U)
      have "backjump_l S U"
        apply (rule backjump_l[of _ _ _ _ _ L "cls_of_ccls D" _ "remove1_mset L (mset_ccls D)"])
                 using tr_T apply simp
                using inv unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def
                apply (simp add: comp_def)
               using U M1_M2 confl undef_L M1_M2 inv_T' inv undef_L unfolding cdcl\<^sub>W_all_struct_inv_def
               cdcl\<^sub>W_M_level_inv_def apply (auto simp: state_eq\<^sub>N\<^sub>O\<^sub>T_def
                 trail_reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_add_learned_cls)[]
              using C\<^sub>S apply auto[]
             using tr_S_C\<^sub>S apply simp

            using U undef_L M1_M2  inv_T' inv unfolding cdcl\<^sub>W_all_struct_inv_def
            cdcl\<^sub>W_M_level_inv_def apply auto[]
           using undef_L atm_L apply (simp add: trail_reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_add_learned_cls)
          using \<open>init_clss T' + learned_clss S \<Turnstile>pm mset_ccls D\<close> LD unfolding raw_clauses_def
          apply simp
         using LD apply simp
        apply (metis U_D convert_trail_from_W_true_annots)
        using  inv_T' inv_U U confl_T' undef_L M1_M2 LD unfolding cdcl\<^sub>W_all_struct_inv_def
        distinct_cdcl\<^sub>W_state_def by (simp add: cdcl\<^sub>W_M_level_inv_decomp backjump_l_cond_def)
      then show ?thesis using cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_backjump_l by fast
    qed
qed

abbreviation cdcl\<^sub>N\<^sub>O\<^sub>T_restart where
"cdcl\<^sub>N\<^sub>O\<^sub>T_restart \<equiv> restart_ops.cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart cdcl\<^sub>N\<^sub>O\<^sub>T restart"

lemma cdcl\<^sub>W_merge_restart_is_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_restart_no_step:
  assumes
    inv: "cdcl\<^sub>W_all_struct_inv S" and
    cdcl\<^sub>W:"cdcl\<^sub>W_merge_restart S T"
  shows "cdcl\<^sub>N\<^sub>O\<^sub>T_restart\<^sup>*\<^sup>* S T \<or> (no_step cdcl\<^sub>W_merge T \<and> conflicting T \<noteq> None)"
proof -
  consider
      (fw) "cdcl\<^sub>W_merge S T"
    | (fw_r) "restart S T"
    using cdcl\<^sub>W by (meson cdcl\<^sub>W_merge_restart.simps cdcl\<^sub>W_rf.cases fw_conflict fw_decide fw_forget
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
    using inv unfolding cdcl\<^sub>W_all_struct_inv_def no_strange_atm_def raw_clauses_def by auto
  have atm_trail: "atm_of ` lits_of_l (trail S) \<subseteq> atms_of_mm ?A"
    using inv unfolding cdcl\<^sub>W_all_struct_inv_def no_strange_atm_def raw_clauses_def by auto
  have n_d: "no_dup (trail S)"
    using inv unfolding cdcl\<^sub>W_all_struct_inv_def by (auto simp: cdcl\<^sub>W_M_level_inv_decomp)
  have [simp]: "\<not> no_step cdcl\<^sub>W_merge S"
    using fw by auto
  have [simp]: "init_clss S = init_clss T"
    using cdcl\<^sub>W_merge_restart_cdcl\<^sub>W[of S T] inv rtranclp_cdcl\<^sub>W_init_clss
    unfolding cdcl\<^sub>W_all_struct_inv_def
    by (meson cdcl\<^sub>W_merge.simps cdcl\<^sub>W_merge_restart.simps  cdcl\<^sub>W_rf.simps fw)
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

sublocale conflict_driven_clause_learning\<^sub>W_termination
  by unfold_locales (simp add: wf_cdcl\<^sub>W_merge)

lemma full_cdcl\<^sub>W_s'_full_cdcl\<^sub>W_merge_restart:
  assumes
    "conflicting R = None" and
    inv: "cdcl\<^sub>W_all_struct_inv R"
  shows "full cdcl\<^sub>W_s' R V \<longleftrightarrow> full cdcl\<^sub>W_merge_stgy R V" (is "?s' \<longleftrightarrow> ?fw")
proof
  assume ?s'
  then have "cdcl\<^sub>W_s'\<^sup>*\<^sup>* R V" unfolding full_def by blast
  have "cdcl\<^sub>W_all_struct_inv V"
    using \<open>cdcl\<^sub>W_s'\<^sup>*\<^sup>* R V\<close> inv rtranclp_cdcl\<^sub>W_all_struct_inv_inv rtranclp_cdcl\<^sub>W_s'_rtranclp_cdcl\<^sub>W
    by blast
  then have n_s: "no_step cdcl\<^sub>W_merge_stgy V"
    using no_step_cdcl\<^sub>W_s'_no_step_cdcl\<^sub>W_merge_stgy by (meson \<open>full cdcl\<^sub>W_s' R V\<close> full_def)
  have n_s_bj: "no_step cdcl\<^sub>W_bj V"
    by (metis \<open>cdcl\<^sub>W_all_struct_inv V\<close> \<open>full cdcl\<^sub>W_s' R V\<close> bj full_def
      n_step_cdcl\<^sub>W_stgy_iff_no_step_cdcl\<^sub>W_cl_cdcl\<^sub>W_o)
  have n_s_cp: "no_step cdcl\<^sub>W_merge_cp V"
    proof -
      { fix ss :: 'st
        obtain ssa :: "'st \<Rightarrow> 'st" where
          ff1: "\<forall>s. \<not> cdcl\<^sub>W_all_struct_inv s \<or> cdcl\<^sub>W_s'_without_decide s (ssa s)
            \<or> no_step cdcl\<^sub>W_merge_cp s"
          using conflicting_true_no_step_s'_without_decide_no_step_cdcl\<^sub>W_merge_cp by moura
        have "(\<forall>p s sa. \<not> full p (s::'st) sa \<or> p\<^sup>*\<^sup>* s sa \<and> no_step p sa)" and
          "(\<forall>p s sa. (\<not> p\<^sup>*\<^sup>* (s::'st) sa \<or> (\<exists>s. p sa s)) \<or> full p s sa)"
          by (meson full_def)+
        then have "\<not> cdcl\<^sub>W_merge_cp V ss"
          using ff1 by (metis (no_types) \<open>cdcl\<^sub>W_all_struct_inv V\<close> \<open>full cdcl\<^sub>W_s' R V\<close> cdcl\<^sub>W_s'.simps
            cdcl\<^sub>W_s'_without_decide.cases) }
      then show ?thesis
        by blast
    qed
  consider
      (fw_no_confl) "cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* R V" and "conflicting V = None"
    | (fw_confl) "cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* R V" and "conflicting V \<noteq> None" and "no_step cdcl\<^sub>W_bj V"
    | (fw_dec_confl) S T U where "cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* R S" and "no_step cdcl\<^sub>W_merge_cp S" and
        "decide S T" and "cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* T U" and "conflict U V"
    | (fw_dec_no_confl) S T where "cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* R S" and "no_step cdcl\<^sub>W_merge_cp S" and
        "decide S T" and "cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* T V" and "conflicting V = None"
    | (cp_no_confl) "cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* R V" and "conflicting V = None"
    | (cp_confl) U where "cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* R U" and "conflict U V"
    using rtranclp_cdcl\<^sub>W_s'_no_step_cdcl\<^sub>W_s'_without_decide_decomp_into_cdcl\<^sub>W_merge[OF
      \<open>cdcl\<^sub>W_s'\<^sup>*\<^sup>* R V\<close> assms] by auto
  then show ?fw
    proof cases
      case fw_no_confl
      then show ?thesis using n_s unfolding full_def by blast
    next
      case fw_confl
      then show ?thesis using n_s unfolding full_def by blast
    next
      case fw_dec_confl
      have "cdcl\<^sub>W_merge_cp U V"
        using n_s_bj by (metis cdcl\<^sub>W_merge_cp.simps full_unfold fw_dec_confl(5))
      then have "full1 cdcl\<^sub>W_merge_cp T V"
        unfolding full1_def by (metis fw_dec_confl(4) n_s_cp tranclp_unfold_end)
      then have "cdcl\<^sub>W_merge_stgy S V" using \<open>decide S T\<close> \<open>no_step cdcl\<^sub>W_merge_cp S\<close> by auto
      then show ?thesis using n_s \<open> cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* R S\<close> unfolding full_def by auto
    next
      case fw_dec_no_confl
      then have "full cdcl\<^sub>W_merge_cp T V"
        using n_s_cp unfolding full_def by blast
      then have "cdcl\<^sub>W_merge_stgy S V" using \<open>decide S T\<close> \<open>no_step cdcl\<^sub>W_merge_cp S\<close> by auto
      then show ?thesis using n_s \<open> cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* R S\<close> unfolding full_def by auto
    next
      case cp_no_confl
      then have "full cdcl\<^sub>W_merge_cp R V"
        by (simp add: full_def n_s_cp)
      then have "R = V \<or> cdcl\<^sub>W_merge_stgy\<^sup>+\<^sup>+ R V"
        using fw_s_cp unfolding full_unfold fw_s_cp
        by (metis (no_types) rtranclp_unfold tranclp_unfold_end)
      then show ?thesis
        by (simp add: full_def n_s rtranclp_unfold)
    next
      case cp_confl
      have "full cdcl\<^sub>W_bj V V"
        using n_s_bj unfolding full_def by blast
      then have "full1 cdcl\<^sub>W_merge_cp R V"
        unfolding full1_def by (meson cdcl\<^sub>W_merge_cp.conflict' cp_confl(1,2) n_s_cp
          rtranclp_into_tranclp1)
      then show ?thesis using n_s unfolding full_def by auto
    qed
next
  assume ?fw
  then have "cdcl\<^sub>W\<^sup>*\<^sup>* R V" using rtranclp_mono[of cdcl\<^sub>W_merge_stgy "cdcl\<^sub>W\<^sup>*\<^sup>*"]
    cdcl\<^sub>W_merge_stgy_rtranclp_cdcl\<^sub>W unfolding full_def by auto
  then have inv': "cdcl\<^sub>W_all_struct_inv V" using inv rtranclp_cdcl\<^sub>W_all_struct_inv_inv by blast
  have "cdcl\<^sub>W_s'\<^sup>*\<^sup>* R V"
    using \<open>?fw\<close> by (simp add: full_def inv rtranclp_cdcl\<^sub>W_merge_stgy_rtranclp_cdcl\<^sub>W_s')
  moreover have "no_step cdcl\<^sub>W_s' V"
    proof cases
      assume "conflicting V = None"
      then show ?thesis
        by (metis inv' \<open>full cdcl\<^sub>W_merge_stgy R V\<close> full_def
          no_step_cdcl\<^sub>W_merge_stgy_no_step_cdcl\<^sub>W_s')
    next
      assume confl_V: "conflicting V \<noteq> None"
      then have "no_step cdcl\<^sub>W_bj V"
      using rtranclp_cdcl\<^sub>W_merge_stgy_no_step_cdcl\<^sub>W_bj by (meson \<open>full cdcl\<^sub>W_merge_stgy R V\<close>
        assms(1) full_def)
      then show ?thesis using confl_V by (fastforce simp: cdcl\<^sub>W_s'.simps full1_def cdcl\<^sub>W_cp.simps
        dest!: tranclpD elim: rulesE)
    qed
  ultimately show ?s' unfolding full_def by blast
qed

lemma full_cdcl\<^sub>W_stgy_full_cdcl\<^sub>W_merge:
  assumes
    "conflicting R = None" and
    inv: "cdcl\<^sub>W_all_struct_inv R"
  shows "full cdcl\<^sub>W_stgy R V \<longleftrightarrow> full cdcl\<^sub>W_merge_stgy R V"
  by (simp add: assms(1) full_cdcl\<^sub>W_s'_full_cdcl\<^sub>W_merge_restart full_cdcl\<^sub>W_stgy_iff_full_cdcl\<^sub>W_s'
    inv)

lemma full_cdcl\<^sub>W_merge_stgy_final_state_conclusive':
  fixes S' :: "'st"
  assumes full: "full cdcl\<^sub>W_merge_stgy (init_state N) S'"
  and no_d: "distinct_mset_mset (mset_clss N)"
  shows "(conflicting S' = Some {#} \<and> unsatisfiable (set_mset (mset_clss N)))
    \<or> (conflicting S' = None \<and> trail S' \<Turnstile>asm mset_clss N \<and> satisfiable (set_mset (mset_clss N)))"
proof -
  have "cdcl\<^sub>W_all_struct_inv (init_state N)"
    using no_d unfolding cdcl\<^sub>W_all_struct_inv_def by auto
  moreover have "conflicting (init_state N) = None"
    by auto
  ultimately show ?thesis
    using full full_cdcl\<^sub>W_stgy_final_state_conclusive_from_init_state
    full_cdcl\<^sub>W_stgy_full_cdcl\<^sub>W_merge no_d by presburger
qed
end

end
