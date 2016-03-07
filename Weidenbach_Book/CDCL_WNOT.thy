theory CDCL_WNOT
imports CDCL_NOT CDCL_W_Termination
begin

section \<open>Link between Weidenbach's and NOT's CDCL\<close>
subsection \<open>Inclusion of the states\<close>
declare upt.simps(2)[simp del]

fun convert_marked_lit_from_W where
"convert_marked_lit_from_W (Propagated L _) = Propagated L ()" |
"convert_marked_lit_from_W (Marked L _) = Marked L ()"

abbreviation convert_trail_from_W ::
  "('v,  'lvl, 'a) marked_lit list
    \<Rightarrow> ('v, unit, unit) marked_lit list"  where
"convert_trail_from_W \<equiv> map convert_marked_lit_from_W"

lemma lits_of_l_convert_trail_from_W[simp]:
  "lits_of_l (convert_trail_from_W M) = lits_of_l M"
  by (induction rule: marked_lit_list_induct) simp_all

lemma lit_of_convert_trail_from_W[simp]:
  "lit_of (convert_marked_lit_from_W L) = lit_of L"
  by (cases L) auto

lemma no_dup_convert_from_W[simp]:
  "no_dup (convert_trail_from_W M) \<longleftrightarrow> no_dup M"
  by (auto simp: comp_def)

lemma convert_trail_from_W_true_annots[simp]:
  "convert_trail_from_W M \<Turnstile>as C \<longleftrightarrow> M \<Turnstile>as C"
  by (auto simp: true_annots_true_cls image_image)

lemma defined_lit_convert_trail_from_W[simp]:
  "defined_lit (convert_trail_from_W S) L \<longleftrightarrow> defined_lit S L"
  by (auto simp: defined_lit_map image_comp)

text \<open>The values @{term "0::nat"} and @{term "{#}"} are dummy values.\<close>
consts dummy_cls :: 'cls
fun convert_marked_lit_from_NOT
  :: "('a, 'e, 'b) marked_lit \<Rightarrow> ('a, nat, 'cls) marked_lit"  where
"convert_marked_lit_from_NOT (Propagated L _) = Propagated L dummy_cls" |
"convert_marked_lit_from_NOT (Marked L _) = Marked L 0"

abbreviation convert_trail_from_NOT where
"convert_trail_from_NOT \<equiv> map convert_marked_lit_from_NOT"

lemma undefined_lit_convert_trail_from_NOT[simp]:
  "undefined_lit (convert_trail_from_NOT F) L \<longleftrightarrow> undefined_lit F L"
  by (induction F rule: marked_lit_list_induct) (auto simp: defined_lit_map)

lemma lits_of_l_convert_trail_from_NOT:
  "lits_of_l (convert_trail_from_NOT F) = lits_of_l F"
  by (induction F rule: marked_lit_list_induct) auto

lemma convert_trail_from_W_from_NOT[simp]:
  "convert_trail_from_W (convert_trail_from_NOT M) = M"
  by (induction rule: marked_lit_list_induct) auto

lemma convert_trail_from_W_convert_lit_from_NOT[simp]:
  "convert_marked_lit_from_W (convert_marked_lit_from_NOT L) = L"
  by (cases L) auto

abbreviation trail\<^sub>N\<^sub>O\<^sub>T where
"trail\<^sub>N\<^sub>O\<^sub>T S \<equiv> convert_trail_from_W (fst S)"

lemma undefined_lit_convert_trail_from_W[iff]:
  "undefined_lit (convert_trail_from_W M) L \<longleftrightarrow> undefined_lit M L"
  by (auto simp: defined_lit_map image_comp)

lemma lit_of_convert_marked_lit_from_NOT[iff]:
  "lit_of (convert_marked_lit_from_NOT L) = lit_of L"
  by (cases L) auto

sublocale state\<^sub>W \<subseteq> dpll_state_ops
   mset_cls union_cls insert_cls remove_lit
   mset_clss union_clss in_clss insert_clss remove_from_clss
   "\<lambda>S. convert_trail_from_W (trail S)"
   raw_clauses
   "\<lambda>L S. cons_trail (convert_marked_lit_from_NOT L) S"
   "\<lambda>S. tl_trail S"
   "\<lambda>C S. add_learned_cls C S"
   "\<lambda>C S. remove_cls C S"
   by unfold_locales

context state\<^sub>W
begin
lemma convert_marked_lit_from_W_convert_marked_lit_from_NOT[simp]:
  "convert_marked_lit_from_W (mmset_of_mlit (convert_marked_lit_from_NOT L)) = L"
  by (cases L) auto
end

sublocale state\<^sub>W \<subseteq> dpll_state
   mset_cls union_cls insert_cls remove_lit
   mset_clss union_clss in_clss insert_clss remove_from_clss
   "\<lambda>S. convert_trail_from_W (trail S)"
   raw_clauses
   "\<lambda>L S. cons_trail (convert_marked_lit_from_NOT L) S"
   "\<lambda>S. tl_trail S"
   "\<lambda>C S. add_learned_cls C S"
   "\<lambda>C S. remove_cls C S"
   by unfold_locales (auto simp: map_tl o_def)

context state\<^sub>W
begin
declare state_simp\<^sub>N\<^sub>O\<^sub>T[simp del]

definition inv\<^sub>N\<^sub>O\<^sub>T :: "'st \<Rightarrow> bool" where
"inv\<^sub>N\<^sub>O\<^sub>T \<equiv> \<lambda>S. no_dup (trail S)"

declare inv\<^sub>N\<^sub>O\<^sub>T_def[simp]

definition backjump_l_cond :: "'v clause \<Rightarrow> 'v clause \<Rightarrow> 'v literal \<Rightarrow> 'st \<Rightarrow> 'st \<Rightarrow> bool"  where
"backjump_l_cond = (\<lambda> _ _ _ _ _. True)"
end

sublocale conflict_driven_clause_learning\<^sub>W \<subseteq> cdcl\<^sub>N\<^sub>O\<^sub>T_merge_bj_learn_ops
  mset_cls union_cls insert_cls remove_lit
  mset_clss union_clss in_clss insert_clss remove_from_clss
  "\<lambda>S. convert_trail_from_W (trail S)"
  raw_clauses
  "\<lambda>L S. cons_trail (convert_marked_lit_from_NOT L) S"
  "\<lambda>S. tl_trail S"
  "\<lambda>C S. add_learned_cls C S"
  "\<lambda>C S. remove_cls C S"
  (* propagate conditions: *)"\<lambda>_ _. True"
  (* forget conditions: *) "\<lambda>_ S. raw_conflicting S = None"
  "\<lambda>C C' L' S T. backjump_l_cond C C' L' S T
    \<and> distinct_mset (C' + {#L'#}) \<and> \<not>tautology (C' + {#L'#})"
  by unfold_locales

context conflict_driven_clause_learning\<^sub>W
begin
declare [[show_abbrevs = false]]
term backjump_l
end

thm cdcl\<^sub>N\<^sub>O\<^sub>T_merge_bj_learn_proxy.axioms
sublocale conflict_driven_clause_learning\<^sub>W \<subseteq> cdcl\<^sub>N\<^sub>O\<^sub>T_merge_bj_learn_proxy
  mset_cls union_cls insert_cls remove_lit
  mset_clss union_clss in_clss insert_clss remove_from_clss
  "\<lambda>S. convert_trail_from_W (trail S)"
  raw_clauses
  "\<lambda>L S. cons_trail (convert_marked_lit_from_NOT L) S"
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
      using \<open>F \<Turnstile>as CNot C'\<close> \<open>undefined_lit F L\<close> Marked_Propagated_in_iff_in_lits_of_l
      in_CNot_implies_uminus(2) by fast
    then have "distinct_mset (?C' + {#L#})"
      by (simp add: distinct_mset_single_add)
  moreover
    have "no_dup F"
      using \<open>inv\<^sub>N\<^sub>O\<^sub>T S\<close> \<open>convert_trail_from_W (trail S) = F' @ Marked K () # F\<close>
      unfolding inv\<^sub>N\<^sub>O\<^sub>T_def
      by (smt comp_apply distinct.simps(2) distinct_append list.simps(9) map_append
        no_dup_convert_from_W)
    then have "consistent_interp (lits_of_l F)"
      using distinct_consistent_interp by blast
    then have "\<not> tautology (C')"
      using \<open>F \<Turnstile>as CNot C'\<close> consistent_CNot_not_tautology true_annots_true_cls by blast
    then have "\<not> tautology (?C' + {#L#})"
      using \<open>F \<Turnstile>as CNot C'\<close> \<open>undefined_lit F L\<close> by (metis  CNot_remdups_mset
        Marked_Propagated_in_iff_in_lits_of_l add.commute in_CNot_uminus tautology_add_single
        tautology_remdups_mset true_annot_singleton true_annots_def)
  show ?case
    proof -
      have f2: "no_dup (convert_trail_from_W (trail S))"
        using \<open>inv\<^sub>N\<^sub>O\<^sub>T S\<close> unfolding inv\<^sub>N\<^sub>O\<^sub>T_def by (simp add: o_def)
      have f3: "atm_of L \<in> atms_of_mm (clauses S)
        \<union> atm_of ` lits_of_l (convert_trail_from_W (trail S))"
        using \<open>convert_trail_from_W (trail S) = F' @ Marked K () # F\<close>
        \<open>atm_of L \<in> atms_of_mm (clauses S) \<union> atm_of ` lits_of_l (F' @ Marked K () # F)\<close> by auto
      have f4: "clauses S \<Turnstile>pm remdups_mset C' + {#L#}"
        by (metis (no_types) \<open>L \<notin># C'\<close> \<open>clauses S \<Turnstile>pm C' + {#L#}\<close> remdups_mset_singleton_sum(2)
          true_clss_cls_remdups_mset union_commute)
      have "F \<Turnstile>as CNot (remdups_mset C')"
        by (simp add: \<open>F \<Turnstile>as CNot C'\<close>)
      show ?thesis sorry
(*       have "Ex (backjump_l S)"
        apply standard
        apply (rule backjump_l.intros[OF  _ f2])
        using f4 f3 f2 \<open>\<not> tautology (remdups_mset C' + {#L#})\<close>
        calculation(2-5,9) \<open>F \<Turnstile>as CNot (remdups_mset C')\<close>
        state_eq\<^sub>N\<^sub>O\<^sub>T_ref unfolding backjump_l_cond_def by auto
      then show ?thesis
        using f4 f3 f2 \<open>\<not> tautology (remdups_mset C' + {#L#})\<close>
        backjump_l.intros[OF  _ f2] calculation(2-5,9)
        state_eq\<^sub>N\<^sub>O\<^sub>T_ref unfolding backjump_l_cond_def by blast
      qed
 *)
  qed
qed

sublocale conflict_driven_clause_learning\<^sub>W \<subseteq> cdcl\<^sub>N\<^sub>O\<^sub>T_merge_bj_learn_proxy2  _ _ _ _ _ _ _ _ _
  "\<lambda>S. convert_trail_from_W (trail S)"
  raw_clauses
  "\<lambda>L S. cons_trail (convert_marked_lit_from_NOT L) S"
  "\<lambda>S. tl_trail S"
  "\<lambda>C S. add_learned_cls C S"
  "\<lambda>C S. remove_cls C S"
  "\<lambda>_ _. True"
  "\<lambda>_ S. raw_conflicting S = None"  backjump_l_cond inv\<^sub>N\<^sub>O\<^sub>T
  by unfold_locales

sublocale conflict_driven_clause_learning\<^sub>W \<subseteq> cdcl\<^sub>N\<^sub>O\<^sub>T_merge_bj_learn _ _ _ _ _ _ _ _ _
  "\<lambda>S. convert_trail_from_W (trail S)"
  raw_clauses
  "\<lambda>L S. cons_trail (convert_marked_lit_from_NOT L) S"
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
    T: "T \<sim> cons_trail (Marked L (Suc (backtrack_lvl S)))
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
  case (fw_forget S T) note rf =this(1) and inv = this(2)
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
        M1_M2:"(Marked K (i+1) # M1, M2) \<in> set (get_all_marked_decomposition (trail T'))" and
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
        using s_or_r
        by (induction rule: rtranclp_induct) (auto simp: skip_or_resolve.simps
          elim!: rulesE)
      obtain M' where
        tr_T': "trail T' = M' @  Marked K (i+1) # tl (trail U)" and
        tr_U: "trail U = Propagated L (mset_ccls D) # tl (trail U)"
        using U M1_M2 undef_L inv_T' unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def
        by fastforce
      def M'' \<equiv> "M @ M'"
      have tr_T: "trail S = M'' @  Marked K (i+1) # tl (trail U)"
        using tr_T tr_T' confl unfolding M''_def by (auto elim: rulesE)
      have "init_clss T' + learned_clss S \<Turnstile>pm mset_ccls D"
        using inv_T' confl_T' unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_learned_clause_def
        raw_clauses_def by simp
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
        using M1_M2 confl
        by (auto simp add: reduce_trail_to\<^sub>N\<^sub>O\<^sub>T_reduce_trail_convert comp_def)
      have "every_mark_is_a_conflict U"
        using inv_U unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_conflicting_def by simp
      then have U_D: "tl (trail U) \<Turnstile>as CNot (remove1_mset L (mset_ccls D))"
        by (metis append_self_conv2 tr_U)
      thm  backjump_l[of _ _ _ _ _ L "cls_of_ccls D" _ "remove1_mset L (mset_ccls D)"]
      have "backjump_l S U"
        apply (rule backjump_l[of _ _ _ _ _ L "cls_of_ccls D" _ "remove1_mset L (mset_ccls D)"])
                 using tr_T apply simp
                using inv unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def
                apply (simp add: comp_def)
               using U M1_M2 confl undef_L M1_M2 inv_T' inv unfolding cdcl\<^sub>W_all_struct_inv_def
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
        using cdcl\<^sub>N\<^sub>O\<^sub>T_decreasing_measure'[OF _ _ atm_clauses] atm_trail n_d
        by (auto split: if_split simp: comp_def)
    next
      case n_s
      then show ?thesis by simp
    qed
qed

lemma wf_cdcl\<^sub>W_merge: "wf {(T, S). cdcl\<^sub>W_all_struct_inv S \<and> cdcl\<^sub>W_merge S T}"
  apply (rule wfP_if_measure[of _ _ "\<mu>\<^sub>F\<^sub>W"])
  using cdcl\<^sub>W_merge_\<mu>\<^sub>F\<^sub>W_decreasing by blast


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
    by (simp add: full full_cdcl\<^sub>W_stgy_final_state_conclusive_from_init_state
      full_cdcl\<^sub>W_stgy_full_cdcl\<^sub>W_merge no_d)
qed

end

subsection \<open>Adding Restarts\<close>
locale cdcl\<^sub>W_restart =
  cdcl\<^sub>W trail init_clss learned_clss backtrack_lvl conflicting cons_trail tl_trail
   add_init_cls
   add_learned_cls remove_cls update_backtrack_lvl update_conflicting init_state
   restart_state
  for
    trail :: "'st \<Rightarrow> ('v, nat, 'v clause) marked_lits" and
    init_clss :: "'st \<Rightarrow> 'v clauses" and
    learned_clss :: "'st \<Rightarrow> 'v clauses" and
    backtrack_lvl :: "'st \<Rightarrow> nat" and
    conflicting :: "'st \<Rightarrow>'v clause option" and

    cons_trail :: "('v, nat, 'v clause) marked_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    tl_trail :: "'st \<Rightarrow> 'st" and
    add_init_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    add_learned_cls remove_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_backtrack_lvl :: "nat \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_conflicting :: "'v clause option \<Rightarrow> 'st \<Rightarrow> 'st" and

    init_state :: "'v clauses \<Rightarrow> 'st" and
    restart_state :: "'st \<Rightarrow> 'st" +
  fixes f :: "nat \<Rightarrow> nat"
  assumes f: "unbounded f"
begin
text \<open>The condition of the differences of cardinality has to be strict.
  Otherwise, you could be in a strange state, where nothing remains to do, but a restart is done.
  See the proof of well-foundedness.\<close>
inductive cdcl\<^sub>W_merge_with_restart where
restart_step:
  "(cdcl\<^sub>W_merge_stgy^^(card (set_mset (learned_clss T)) - card (set_mset (learned_clss S)))) S T
  \<Longrightarrow> card (set_mset (learned_clss T)) - card (set_mset (learned_clss S)) > f n
  \<Longrightarrow> restart T U \<Longrightarrow> cdcl\<^sub>W_merge_with_restart (S, n) (U, Suc n)" |
restart_full: "full1 cdcl\<^sub>W_merge_stgy S T \<Longrightarrow> cdcl\<^sub>W_merge_with_restart (S, n) (T, Suc n)"

lemma "cdcl\<^sub>W_merge_with_restart S T \<Longrightarrow> cdcl\<^sub>W_merge_restart\<^sup>*\<^sup>* (fst S) (fst T)"
  by (induction rule: cdcl\<^sub>W_merge_with_restart.induct)
  (auto dest!: relpowp_imp_rtranclp cdcl\<^sub>W_merge_stgy_tranclp_cdcl\<^sub>W_merge tranclp_into_rtranclp
     rtranclp_cdcl\<^sub>W_merge_stgy_rtranclp_cdcl\<^sub>W_merge rtranclp_cdcl\<^sub>W_merge_tranclp_cdcl\<^sub>W_merge_restart
     fw_r_rf cdcl\<^sub>W_rf.restart
    simp: full1_def)

lemma cdcl\<^sub>W_merge_with_restart_rtranclp_cdcl\<^sub>W:
  "cdcl\<^sub>W_merge_with_restart S T \<Longrightarrow> cdcl\<^sub>W\<^sup>*\<^sup>* (fst S) (fst T)"
  by (induction rule: cdcl\<^sub>W_merge_with_restart.induct)
  (auto dest!: relpowp_imp_rtranclp rtranclp_cdcl\<^sub>W_merge_stgy_rtranclp_cdcl\<^sub>W cdcl\<^sub>W.rf
    cdcl\<^sub>W_rf.restart tranclp_into_rtranclp simp: full1_def)

lemma cdcl\<^sub>W_merge_with_restart_increasing_number:
  "cdcl\<^sub>W_merge_with_restart S T \<Longrightarrow> snd T = 1 + snd S"
  by (induction rule: cdcl\<^sub>W_merge_with_restart.induct) auto

lemma "full1 cdcl\<^sub>W_merge_stgy S T \<Longrightarrow> cdcl\<^sub>W_merge_with_restart (S, n) (T, Suc n)"
  using restart_full by blast

lemma cdcl\<^sub>W_all_struct_inv_learned_clss_bound:
  assumes inv: "cdcl\<^sub>W_all_struct_inv S"
  shows "set_mset (learned_clss S) \<subseteq> simple_clss (atms_of_mm (init_clss S))"
proof
  fix C
  assume C: "C \<in> set_mset (learned_clss S)"
  have "distinct_mset C"
    using C inv unfolding cdcl\<^sub>W_all_struct_inv_def distinct_cdcl\<^sub>W_state_def distinct_mset_set_def
    by auto
  moreover have "\<not>tautology C"
    using C inv unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_learned_clause_def by auto
  moreover
    have "atms_of C \<subseteq> atms_of_mm (learned_clss S)"
      using C by auto
    then have "atms_of C \<subseteq> atms_of_mm (init_clss S)"
    using inv  unfolding cdcl\<^sub>W_all_struct_inv_def no_strange_atm_def by force
  moreover have "finite (atms_of_mm (init_clss S))"
    using inv unfolding cdcl\<^sub>W_all_struct_inv_def by auto
  ultimately show "C \<in> simple_clss (atms_of_mm (init_clss S))"
    using distinct_mset_not_tautology_implies_in_simple_clss simple_clss_mono
    by blast
qed

lemma cdcl\<^sub>W_merge_with_restart_init_clss:
  "cdcl\<^sub>W_merge_with_restart S T \<Longrightarrow> cdcl\<^sub>W_M_level_inv (fst S) \<Longrightarrow>
  init_clss (fst S) = init_clss (fst T)"
  using cdcl\<^sub>W_merge_with_restart_rtranclp_cdcl\<^sub>W rtranclp_cdcl\<^sub>W_init_clss by blast

lemma
  "wf {(T, S). cdcl\<^sub>W_all_struct_inv (fst S) \<and> cdcl\<^sub>W_merge_with_restart S T}"
proof (rule ccontr)
  assume "\<not> ?thesis"
    then obtain g where
    g: "\<And>i. cdcl\<^sub>W_merge_with_restart (g i) (g (Suc i))" and
    inv: "\<And>i. cdcl\<^sub>W_all_struct_inv (fst (g i))"
    unfolding wf_iff_no_infinite_down_chain by fast
  { fix i
    have "init_clss (fst (g i)) = init_clss (fst (g 0))"
      apply (induction i)
        apply simp
      using g inv unfolding cdcl\<^sub>W_all_struct_inv_def by (metis cdcl\<^sub>W_merge_with_restart_init_clss)
    } note init_g = this
  let ?S = "g 0"
  have "finite (atms_of_mm (init_clss (fst ?S)))"
    using inv unfolding cdcl\<^sub>W_all_struct_inv_def by auto
  have snd_g: "\<And>i. snd (g i) = i + snd (g 0)"
    apply (induct_tac i)
      apply simp
    by (metis Suc_eq_plus1_left add_Suc cdcl\<^sub>W_merge_with_restart_increasing_number g)
  then have snd_g_0: "\<And>i. i > 0 \<Longrightarrow> snd (g i) = i + snd (g 0)"
    by blast
  have unbounded_f_g: "unbounded (\<lambda>i. f (snd (g i)))"
    using f unfolding bounded_def by (metis add.commute f less_or_eq_imp_le snd_g
      not_bounded_nat_exists_larger not_le le_iff_add)

  obtain k where
    f_g_k: "f (snd (g k)) > card (simple_clss (atms_of_mm (init_clss (fst ?S))))" and
    "k > card (simple_clss (atms_of_mm (init_clss (fst ?S))))"
    using not_bounded_nat_exists_larger[OF unbounded_f_g] by blast
  text \<open>The following does not hold anymore with the non-strict version of
    cardinality in the definition.\<close>
  { fix i
    assume "no_step cdcl\<^sub>W_merge_stgy (fst (g i))"
    with g[of i]
    have False
      proof (induction rule: cdcl\<^sub>W_merge_with_restart.induct)
        case (restart_step T S n) note H = this(1) and c = this(2) and n_s = this(4)
        obtain S' where "cdcl\<^sub>W_merge_stgy S S'"
          using H c by (metis gr_implies_not0 relpowp_E2)
        then show False using n_s by auto
      next
        case (restart_full S T)
        then show False unfolding full1_def by (auto dest: tranclpD)
      qed
    } note H = this
  obtain m T where
    m: "m = card (set_mset (learned_clss T)) - card (set_mset (learned_clss (fst (g k))))" and
    "m > f (snd (g k))" and
    "restart T (fst (g (k+1)))" and
    cdcl\<^sub>W_merge_stgy: "(cdcl\<^sub>W_merge_stgy ^^ m) (fst (g k)) T"
    using g[of k] H[of "Suc k"] by (force simp: cdcl\<^sub>W_merge_with_restart.simps full1_def)
  have "cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* (fst (g k)) T"
    using cdcl\<^sub>W_merge_stgy relpowp_imp_rtranclp by metis
  then have "cdcl\<^sub>W_all_struct_inv T"
    using inv[of k]  rtranclp_cdcl\<^sub>W_all_struct_inv_inv rtranclp_cdcl\<^sub>W_merge_stgy_rtranclp_cdcl\<^sub>W
    by blast
  moreover have "card (set_mset (learned_clss T)) - card (set_mset (learned_clss (fst (g k))))
      > card (simple_clss (atms_of_mm (init_clss (fst ?S))))"
      unfolding m[symmetric] using \<open>m > f (snd (g k))\<close> f_g_k by linarith
    then have "card (set_mset (learned_clss T))
      > card (simple_clss (atms_of_mm (init_clss (fst ?S))))"
      by linarith
  moreover
    have "init_clss (fst (g k)) = init_clss T"
      using \<open>cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* (fst (g k)) T\<close> rtranclp_cdcl\<^sub>W_merge_stgy_rtranclp_cdcl\<^sub>W
      rtranclp_cdcl\<^sub>W_init_clss inv unfolding cdcl\<^sub>W_all_struct_inv_def by blast
    then have "init_clss (fst ?S) = init_clss T"
      using init_g[of k] by auto
  ultimately show False
    using cdcl\<^sub>W_all_struct_inv_learned_clss_bound
    by (simp add: \<open>finite (atms_of_mm (init_clss (fst (g 0))))\<close> simple_clss_finite
      card_mono leD)
qed

lemma cdcl\<^sub>W_merge_with_restart_distinct_mset_clauses:
  assumes invR: "cdcl\<^sub>W_all_struct_inv (fst R)" and
  st: "cdcl\<^sub>W_merge_with_restart R S" and
  dist: "distinct_mset (clauses (fst R))" and
  R: "trail (fst R) = []"
  shows "distinct_mset (clauses (fst S))"
  using assms(2,1,3,4)
proof (induction)
  case (restart_full S T)
  then show ?case using rtranclp_cdcl\<^sub>W_merge_stgy_distinct_mset_clauses[of S T] unfolding full1_def
    by (auto dest: tranclp_into_rtranclp)
next
  case (restart_step T S n U)
  then have "distinct_mset (clauses T)"
    using rtranclp_cdcl\<^sub>W_merge_stgy_distinct_mset_clauses[of S T] unfolding full1_def
    by (auto dest: relpowp_imp_rtranclp)
  then show ?case using \<open>restart T U\<close> by (metis clauses_restart distinct_mset_union fstI
    mset_le_exists_conv restart.cases state_eq_clauses)
qed

inductive cdcl\<^sub>W_with_restart where
restart_step:
  "(cdcl\<^sub>W_stgy^^(card (set_mset (learned_clss T)) - card (set_mset (learned_clss S)))) S T \<Longrightarrow>
     card (set_mset (learned_clss T)) - card (set_mset (learned_clss S)) > f n \<Longrightarrow>
     restart T U \<Longrightarrow>
   cdcl\<^sub>W_with_restart (S, n) (U, Suc n)" |
restart_full: "full1 cdcl\<^sub>W_stgy S T \<Longrightarrow> cdcl\<^sub>W_with_restart (S, n) (T, Suc n)"

lemma cdcl\<^sub>W_with_restart_rtranclp_cdcl\<^sub>W:
  "cdcl\<^sub>W_with_restart S T \<Longrightarrow> cdcl\<^sub>W\<^sup>*\<^sup>* (fst S) (fst T)"
  apply (induction rule: cdcl\<^sub>W_with_restart.induct)
  by (auto dest!: relpowp_imp_rtranclp  tranclp_into_rtranclp fw_r_rf
     cdcl\<^sub>W_rf.restart rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W cdcl\<^sub>W_merge_restart_cdcl\<^sub>W
    simp: full1_def)

lemma cdcl\<^sub>W_with_restart_increasing_number:
  "cdcl\<^sub>W_with_restart S T \<Longrightarrow> snd T = 1 + snd S"
  by (induction rule: cdcl\<^sub>W_with_restart.induct) auto

lemma "full1 cdcl\<^sub>W_stgy S T \<Longrightarrow> cdcl\<^sub>W_with_restart (S, n) (T, Suc n)"
  using restart_full by blast

lemma cdcl\<^sub>W_with_restart_init_clss:
  "cdcl\<^sub>W_with_restart S T \<Longrightarrow>  cdcl\<^sub>W_M_level_inv (fst S) \<Longrightarrow> init_clss (fst S) = init_clss (fst T)"
  using cdcl\<^sub>W_with_restart_rtranclp_cdcl\<^sub>W rtranclp_cdcl\<^sub>W_init_clss by blast

lemma
  "wf {(T, S). cdcl\<^sub>W_all_struct_inv (fst S) \<and> cdcl\<^sub>W_with_restart S T}"
proof (rule ccontr)
  assume "\<not> ?thesis"
    then obtain g where
    g: "\<And>i. cdcl\<^sub>W_with_restart (g i) (g (Suc i))" and
    inv: "\<And>i. cdcl\<^sub>W_all_struct_inv (fst (g i))"
    unfolding wf_iff_no_infinite_down_chain by fast
  { fix i
    have "init_clss (fst (g i)) = init_clss (fst (g 0))"
      apply (induction i)
        apply simp
      using g inv unfolding cdcl\<^sub>W_all_struct_inv_def by (metis cdcl\<^sub>W_with_restart_init_clss)
    } note init_g = this
  let ?S = "g 0"
  have "finite (atms_of_mm (init_clss (fst ?S)))"
    using inv unfolding cdcl\<^sub>W_all_struct_inv_def by auto
  have snd_g: "\<And>i. snd (g i) = i + snd (g 0)"
    apply (induct_tac i)
      apply simp
    by (metis Suc_eq_plus1_left add_Suc cdcl\<^sub>W_with_restart_increasing_number g)
  then have snd_g_0: "\<And>i. i > 0 \<Longrightarrow> snd (g i) = i + snd (g 0)"
    by blast
  have unbounded_f_g: "unbounded (\<lambda>i. f (snd (g i)))"
    using f unfolding bounded_def by (metis add.commute f less_or_eq_imp_le snd_g
      not_bounded_nat_exists_larger not_le le_iff_add)

  obtain k where
    f_g_k: "f (snd (g k)) > card (simple_clss (atms_of_mm (init_clss (fst ?S))))" and
    "k > card (simple_clss (atms_of_mm (init_clss (fst ?S))))"
    using not_bounded_nat_exists_larger[OF unbounded_f_g] by blast
  text \<open>The following does not hold anymore with the non-strict version of
    cardinality in the definition.\<close>
  { fix i
    assume "no_step cdcl\<^sub>W_stgy (fst (g i))"
    with g[of i]
    have False
      proof (induction rule: cdcl\<^sub>W_with_restart.induct)
        case (restart_step T S n) note H = this(1) and c = this(2) and n_s = this(4)
        obtain S' where "cdcl\<^sub>W_stgy S S'"
          using H c by (metis gr_implies_not0 relpowp_E2)
        then show False using n_s by auto
      next
        case (restart_full S T)
        then show False unfolding full1_def by (auto dest: tranclpD)
      qed
    } note H = this
  obtain m T where
    m: "m = card (set_mset (learned_clss T)) - card (set_mset (learned_clss (fst (g k))))" and
    "m > f (snd (g k))" and
    "restart T (fst (g (k+1)))" and
    cdcl\<^sub>W_merge_stgy: "(cdcl\<^sub>W_stgy ^^ m) (fst (g k)) T"
    using g[of k] H[of "Suc k"] by (force simp: cdcl\<^sub>W_with_restart.simps full1_def)
  have "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (fst (g k)) T"
    using cdcl\<^sub>W_merge_stgy relpowp_imp_rtranclp by metis
  then have "cdcl\<^sub>W_all_struct_inv T"
    using inv[of k]  rtranclp_cdcl\<^sub>W_all_struct_inv_inv rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W by blast
  moreover have "card (set_mset (learned_clss T)) - card (set_mset (learned_clss (fst (g k))))
      > card (simple_clss (atms_of_mm (init_clss (fst ?S))))"
      unfolding m[symmetric] using \<open>m > f (snd (g k))\<close> f_g_k by linarith
    then have "card (set_mset (learned_clss T))
      > card (simple_clss (atms_of_mm (init_clss (fst ?S))))"
      by linarith
  moreover
    have "init_clss (fst (g k)) = init_clss T"
      using \<open>cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (fst (g k)) T\<close> rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W rtranclp_cdcl\<^sub>W_init_clss
      inv unfolding cdcl\<^sub>W_all_struct_inv_def
      by blast
    then have "init_clss (fst ?S) = init_clss T"
      using init_g[of k] by auto
  ultimately show False
    using cdcl\<^sub>W_all_struct_inv_learned_clss_bound
    by (simp add: \<open>finite (atms_of_mm (init_clss (fst (g 0))))\<close> simple_clss_finite
      card_mono leD)
qed

lemma cdcl\<^sub>W_with_restart_distinct_mset_clauses:
  assumes invR: "cdcl\<^sub>W_all_struct_inv (fst R)" and
  st: "cdcl\<^sub>W_with_restart R S" and
  dist: "distinct_mset (clauses (fst R))" and
  R: "trail (fst R) = []"
  shows "distinct_mset (clauses (fst S))"
  using assms(2,1,3,4)
proof (induction)
  case (restart_full S T)
  then show ?case using rtranclp_cdcl\<^sub>W_stgy_distinct_mset_clauses[of S T] unfolding full1_def
    by (auto dest: tranclp_into_rtranclp)
next
  case (restart_step T S n U)
  then have "distinct_mset (clauses T)" using rtranclp_cdcl\<^sub>W_stgy_distinct_mset_clauses[of S T]
    unfolding full1_def by (auto dest: relpowp_imp_rtranclp)
  then show ?case using \<open>restart T U\<close> by (metis clauses_restart distinct_mset_union fstI
    mset_le_exists_conv restart.cases state_eq_clauses)
qed
end

locale luby_sequence =
  fixes ur :: nat (*unit run*)
  assumes "ur > 0"
begin

lemma exists_luby_decomp:
  fixes i ::nat
  shows "\<exists>k::nat. (2 ^ (k - 1) \<le> i \<and> i < 2 ^ k - 1) \<or> i = 2 ^ k - 1"
proof (induction i)
  case 0
  then show ?case
    by (rule exI[of _ 0], simp)
next
  case (Suc n)
  then obtain k where "2 ^ (k - 1) \<le> n \<and> n < 2 ^ k - 1 \<or> n = 2 ^ k - 1"
    by blast
  then consider
      (st_interv) "2 ^ (k - 1) \<le> n" and  "n \<le> 2 ^ k - 2"
    | (end_interv) "2 ^ (k - 1) \<le> n" and "n = 2 ^ k - 2"
    | (pow2) "n = 2 ^ k - 1"
    by linarith
  then show ?case
    proof cases
      case st_interv
      then show ?thesis apply - apply (rule exI[of _ k])
        by (metis (no_types, lifting) One_nat_def Suc_diff_Suc Suc_lessI
          \<open>2 ^ (k - 1) \<le> n \<and> n < 2 ^ k - 1 \<or> n = 2 ^ k - 1\<close> diff_self_eq_0
          dual_order.trans le_SucI le_imp_less_Suc numeral_2_eq_2 one_le_numeral
          one_le_power zero_less_numeral zero_less_power)
    next
      case end_interv
      then show ?thesis apply - apply (rule exI[of _ k]) by auto
    next
      case pow2
      then show ?thesis apply - apply (rule exI[of _ "k+1"]) by auto
    qed
qed

text \<open>Luby sequences are defined by:
   \<^item> @{term "(2::nat)^(k::nat)- 1"}, if @{term "i = 2^k - 1"}
   \<^item> @{term "luby_sequence_core (i - (2::nat)^(k - 1) + 1)"}, if @{term "2^(k - 1) \<le> i"} and
   @{term "i \<le> 2^k - 1"}

Then the sequence is then scaled by a constant unit run (called @{term ur} here), strictly positive.
\<close>
function luby_sequence_core :: "nat \<Rightarrow> nat" where
"luby_sequence_core i =
  (if \<exists>k. i = 2^k - 1
  then 2^((SOME k. i = 2^k - 1) - 1)
  else luby_sequence_core (i - 2^((SOME k. 2^(k-1)\<le> i \<and> i < 2^k - 1) - 1) + 1))"
by auto
termination
proof (relation "less_than", goal_cases)
  case 1
  then show ?case by auto
next
  case (2 i)
  let ?k = "(SOME k. 2 ^ (k - 1) \<le> i \<and> i < 2 ^ k - 1)"
  have "2 ^ (?k - 1) \<le> i \<and> i < 2 ^ ?k - 1"
    apply (rule someI_ex)
    using "2" exists_luby_decomp by blast
  then show ?case
    (* sledgehammer *)
    proof -
      have "\<forall>n na. \<not> (1::nat) \<le> n \<or> 1 \<le> n ^ na"
        by (meson one_le_power)
      then have f1: "(1::nat) \<le> 2 ^ (?k - 1)"
        using one_le_numeral by blast
      have f2: "i - 2 ^ (?k - 1) + 2 ^ (?k - 1) = i"
        using \<open>2 ^ (?k - 1) \<le> i \<and> i < 2 ^ ?k - 1\<close> le_add_diff_inverse2 by blast
      have f3: "2 ^ ?k - 1 \<noteq> Suc 0"
        using f1 \<open>2 ^ (?k - 1) \<le> i \<and> i < 2 ^ ?k - 1\<close> by linarith
      have "2 ^ ?k - (1::nat) \<noteq> 0"
        using \<open>2 ^ (?k - 1) \<le> i \<and> i < 2 ^ ?k - 1\<close> gr_implies_not0 by blast
      then have f4: "2 ^ ?k \<noteq> (1::nat)"
        by linarith
      have f5: "\<forall>n na. if na = 0 then (n::nat) ^ na = 1 else n ^ na = n * n ^ (na - 1)"
        by (simp add: power_eq_if)
      then have "?k \<noteq> 0"
        using f4 by meson
      then have "2 ^ (?k - 1) \<noteq> Suc 0"
        using f5 f3 by presburger
      then have "Suc 0 < 2 ^ (?k - 1)"
        using f1 by linarith
      then show ?thesis
        using f2 less_than_iff by presburger
    qed
qed

declare luby_sequence_core.simps[simp del]

lemma two_pover_n_eq_two_power_n'_eq:
  assumes H: "(2::nat) ^ (k::nat) - 1 = 2 ^ k' - 1"
  shows "k' = k"
proof -
  have "(2::nat) ^ (k::nat) = 2 ^ k'"
    using H by (metis One_nat_def Suc_pred zero_less_numeral zero_less_power)
  then show ?thesis by simp
qed

lemma luby_sequence_core_two_power_minus_one:
  "luby_sequence_core (2^k - 1) = 2^(k-1)" (is "?L = ?K")
proof -
  have decomp: "\<exists>ka. 2 ^ k - 1 = 2 ^ ka - 1"
    by auto
  have "?L = 2^((SOME k'. (2::nat)^k - 1 = 2^k' - 1) - 1)"
    apply (subst luby_sequence_core.simps, subst decomp)
    by simp
  moreover have "(SOME k'. (2::nat)^k - 1 = 2^k' - 1) = k"
    apply (rule some_equality)
      apply simp
      using two_pover_n_eq_two_power_n'_eq by blast
  ultimately show ?thesis by presburger
qed

lemma different_luby_decomposition_false:
  assumes
    H: "2 ^ (k - Suc 0) \<le> i" and
    k': "i < 2 ^ k' - Suc 0" and
    k_k': "k > k'"
  shows "False"
proof -
  have "2 ^ k' - Suc 0 < 2 ^ (k - Suc 0)"
    using k_k' less_eq_Suc_le by auto
  then show ?thesis
    using H k' by linarith
qed

lemma luby_sequence_core_not_two_power_minus_one:
  assumes
    k_i: "2 ^ (k - 1) \<le> i" and
    i_k: "i < 2^ k - 1"
  shows "luby_sequence_core i = luby_sequence_core (i - 2 ^ (k - 1) + 1)"
proof -
  have H: "\<not> (\<exists>ka. i = 2 ^ ka - 1)"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then obtain k'::nat where k': "i = 2 ^ k' - 1" by blast
      have "(2::nat) ^ k' - 1 < 2 ^ k - 1"
        using i_k unfolding k' .
      then have "(2::nat) ^ k' < 2 ^ k"
        by linarith
      then have "k' < k"
        by simp
      have "2 ^ (k - 1) \<le> 2 ^ k' - (1::nat)"
        using k_i unfolding k' .
      then have "(2::nat) ^ (k-1) < 2 ^ k'"
        by (metis Suc_diff_1 not_le not_less_eq zero_less_numeral zero_less_power)
      then have "k-1 < k'"
        by simp

      show False using \<open>k' < k\<close> \<open>k-1 < k'\<close> by linarith
    qed
  have "\<And>k k'. 2 ^ (k - Suc 0) \<le> i \<Longrightarrow> i < 2 ^ k - Suc 0 \<Longrightarrow> 2 ^ (k' - Suc 0) \<le> i \<Longrightarrow>
    i < 2 ^ k' - Suc 0 \<Longrightarrow> k = k'"
    by (meson different_luby_decomposition_false linorder_neqE_nat)
  then have k: "(SOME k. 2 ^ (k - Suc 0) \<le> i \<and> i < 2 ^ k - Suc 0) = k"
    using k_i i_k by auto
  show ?thesis
    apply (subst luby_sequence_core.simps[of i], subst H)
    by (simp add: k)
qed

lemma unbounded_luby_sequence_core: "unbounded luby_sequence_core"
  unfolding bounded_def
proof
  assume "\<exists>b. \<forall>n. luby_sequence_core n \<le> b"
  then obtain b where b: "\<And>n. luby_sequence_core n \<le> b"
    by metis
  have "luby_sequence_core (2^(b+1) - 1) = 2^b"
    using luby_sequence_core_two_power_minus_one[of "b+1"] by simp
  moreover have "(2::nat)^b > b"
    by (induction b) auto
  ultimately show False using b[of "2^(b+1) - 1"] by linarith
qed

abbreviation luby_sequence :: "nat \<Rightarrow> nat" where
"luby_sequence n \<equiv>  ur * luby_sequence_core n"

lemma bounded_luby_sequence: "unbounded luby_sequence"
  using bounded_const_product[of ur] luby_sequence_axioms
  luby_sequence_def unbounded_luby_sequence_core by blast

lemma luby_sequence_core_0: "luby_sequence_core 0 = 1"
proof -
  have 0: "(0::nat) = 2^0-1"
    by auto
  show ?thesis
    by (subst 0, subst luby_sequence_core_two_power_minus_one) simp
qed

lemma "luby_sequence_core n \<ge> 1"
proof (induction n rule: nat_less_induct_case)
  case 0
  then show ?case by (simp add: luby_sequence_core_0)
next
  case (Suc n) note IH = this

  consider
      (interv) k where "2 ^ (k - 1) \<le> Suc n" and "Suc n < 2 ^ k - 1"
    | (pow2)  k where "Suc n = 2 ^ k - Suc 0"
    using exists_luby_decomp[of "Suc n"] by auto

  then show ?case
     proof cases
       case pow2
       show ?thesis
         using luby_sequence_core_two_power_minus_one pow2 by auto
     next
       case interv
       have n: "Suc n - 2 ^ (k - 1) + 1 < Suc n"
         by (metis Suc_1 Suc_eq_plus1 add.commute add_diff_cancel_left' add_less_mono1 gr0I
           interv(1) interv(2) le_add_diff_inverse2 less_Suc_eq not_le power_0 power_one_right
           power_strict_increasing_iff)
       show ?thesis
         apply (subst luby_sequence_core_not_two_power_minus_one[OF interv])
         using IH n by auto
     qed
qed
end

locale luby_sequence_restart =
  luby_sequence ur +
  cdcl\<^sub>W trail init_clss learned_clss backtrack_lvl conflicting cons_trail tl_trail
    add_init_cls
    add_learned_cls remove_cls update_backtrack_lvl update_conflicting init_state
    restart_state
  for
    ur :: nat and
    trail :: "'st \<Rightarrow> ('v, nat, 'v clause) marked_lits" and
    init_clss :: "'st \<Rightarrow> 'v clauses" and
    learned_clss :: "'st \<Rightarrow> 'v clauses" and
    backtrack_lvl :: "'st \<Rightarrow> nat" and
    conflicting :: "'st \<Rightarrow>'v clause option" and
    cons_trail :: "('v, nat, 'v clause) marked_lit \<Rightarrow> 'st \<Rightarrow> 'st" and
    tl_trail :: "'st \<Rightarrow> 'st" and
    add_init_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    add_learned_cls remove_cls :: "'v clause \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_backtrack_lvl :: "nat \<Rightarrow> 'st \<Rightarrow> 'st" and
    update_conflicting :: "'v clause option \<Rightarrow> 'st \<Rightarrow> 'st" and

    init_state :: "'v clauses \<Rightarrow> 'st" and
    restart_state :: "'st \<Rightarrow> 'st"
begin

sublocale cdcl\<^sub>W_restart _ _ _ _ _ _ _ _ _ _ _ _ _ _ luby_sequence
  apply unfold_locales
  using bounded_luby_sequence by blast

end

end
