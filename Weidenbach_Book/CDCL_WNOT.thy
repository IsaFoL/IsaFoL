theory CDCL_WNOT
imports CDCL_W_Termination CDCL_NOT
begin

section \<open>Link between Weidenbach's and NOT's CDCL\<close>
subsection \<open>Inclusion of the states\<close>
declare upt.simps(2)[simp del]
sledgehammer_params[verbose]

context cdcl\<^sub>W_ops
begin

lemma backtrack_levE:
  "backtrack S S' \<Longrightarrow> cdcl\<^sub>W_M_level_inv S \<Longrightarrow>
  (\<And>D L K M1 M2.
    (Marked K (Suc (get_maximum_level D (trail S))) # M1, M2)
      \<in> set (get_all_marked_decomposition (trail S)) \<Longrightarrow>
    get_level L (trail S) = get_maximum_level (D + {#L#}) (trail S) \<Longrightarrow>
    undefined_lit M1 L \<Longrightarrow>
    S' \<sim> cons_trail (Propagated L (D + {#L#}))
      (reduce_trail_to M1 (add_learned_cls (D + {#L#})
        (update_backtrack_lvl (get_maximum_level D (trail S)) (update_conflicting C_True S)))) \<Longrightarrow>
    backtrack_lvl S = get_maximum_level (D + {#L#}) (trail S) \<Longrightarrow>
    conflicting S = C_Clause (D + {#L#}) \<Longrightarrow> P) \<Longrightarrow>
  P"
  using assms by (induction rule: backtrack_induction_lev2) metis

lemma backtrack_no_cdcl\<^sub>W_bj:
  assumes cdcl: "cdcl\<^sub>W_bj T U" and inv: "cdcl\<^sub>W_M_level_inv V"
  shows "\<not>backtrack V T"
  using cdcl inv
  by (induction rule: cdcl\<^sub>W_bj.induct) (force elim!: backtrack_levE[OF _ inv]
    simp: cdcl\<^sub>W_M_level_inv_def)+
  (* SLOW ~2s *) (* TODO faster proof *)

abbreviation skip_or_resolve :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
"skip_or_resolve \<equiv> (\<lambda>S T. skip S T \<or> resolve S T)"

lemma rtranclp_cdcl\<^sub>W_bj_skip_or_resolve_backtrack:
  assumes "cdcl\<^sub>W_bj\<^sup>*\<^sup>* S U" and inv: "cdcl\<^sub>W_M_level_inv S"
  shows "skip_or_resolve\<^sup>*\<^sup>* S U \<or> (\<exists>T. skip_or_resolve\<^sup>*\<^sup>* S T \<and> backtrack T U)"
  using assms
proof (induction)
  case base
  then show ?case by simp
next
  case (step U V) note st = this(1) and bj = this(2) and IH = this(3)[OF this(4)]
  consider
      (SU) "S = U"
    | (SUp) "cdcl\<^sub>W_bj\<^sup>+\<^sup>+ S U"
    using st unfolding rtranclp_unfold by blast
  then show ?case
    proof cases
      case SUp
      have "\<And>T. skip_or_resolve\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl\<^sub>W\<^sup>*\<^sup>* S T"
        using mono_rtranclp[of skip_or_resolve cdcl\<^sub>W] other by blast
      then have "skip_or_resolve\<^sup>*\<^sup>* S U"
        using bj IH inv backtrack_no_cdcl\<^sub>W_bj rtranclp_cdcl\<^sub>W_consistent_inv[OF _ inv] by meson
      then show ?thesis
        using bj by (metis (no_types, lifting) cdcl\<^sub>W_bj.cases rtranclp.simps)
    next
      case SU
      then show ?thesis
        using bj by (metis (no_types, lifting) cdcl\<^sub>W_bj.cases rtranclp.simps)
    qed
qed

lemma rtranclp_skip_or_resolve_rtranclp_cdcl\<^sub>W:
  "skip_or_resolve\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl\<^sub>W\<^sup>*\<^sup>* S T"
  by (induction rule: rtranclp_induct) (auto dest!: cdcl\<^sub>W_bj.intros cdcl\<^sub>W.intros cdcl\<^sub>W_o.intros)

abbreviation backjump_l_cond :: " 'v literal multiset \<Rightarrow> 'v literal \<Rightarrow> 'st \<Rightarrow> bool" where
"backjump_l_cond \<equiv> \<lambda>C L S. True"

definition inv\<^sub>N\<^sub>O\<^sub>T :: "'st \<Rightarrow> bool" where
"inv\<^sub>N\<^sub>O\<^sub>T \<equiv> \<lambda>S. no_dup (trail S)"

declare inv\<^sub>N\<^sub>O\<^sub>T_def[simp]
end

fun convert_trail_from_W ::
  "('v,  'lvl, 'v literal multiset) marked_lit list
    \<Rightarrow> ('v, unit, unit) marked_lit list"  where
"convert_trail_from_W [] = []" |
"convert_trail_from_W (Propagated L _ # M) = Propagated L () # convert_trail_from_W M" |
"convert_trail_from_W (Marked L _ # M) = Marked L () # convert_trail_from_W M"

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
  "defined_lit (convert_trail_from_W S) L \<longleftrightarrow> defined_lit S L"
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
  "('v, unit, unit) marked_lit list
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

lemma undefined_lit_convert_trail_from_W[iff]:
  "undefined_lit (convert_trail_from_W M) L \<longleftrightarrow> undefined_lit M L"
  by (auto simp: defined_lit_map)
lemma lit_of_convert_marked_lit_from_NOT[iff]:
  "lit_of (convert_marked_lit_from_NOT L) = lit_of L"
  by (cases L) auto

sublocale state\<^sub>W \<subseteq> dpll_state "convert_trail_from_W o trail" clauses
  "\<lambda>L S. cons_trail (convert_marked_lit_from_NOT L) S"
  "\<lambda>S. tl_trail S"
  "\<lambda>C S. add_learned_cls C S"
  "\<lambda>C S. remove_cls C S"
  by unfold_locales auto

sublocale cdcl\<^sub>W_ops \<subseteq> cdcl\<^sub>N\<^sub>O\<^sub>T_merge_bj_learn_ops "convert_trail_from_W o trail" clauses
  "\<lambda>L S. cons_trail (convert_marked_lit_from_NOT L) S"
  "\<lambda>S. tl_trail S"
  "\<lambda>C S. add_learned_cls C S"
  "\<lambda>C S. remove_cls C S"
  (* propagate conditions: *)"\<lambda>_ _. True"
  (* backjump conditions: *) "\<lambda>_ S. conflicting S = C_True" "\<lambda>C L S. backjump_l_cond C L S
    \<and> distinct_mset (C + {#L#}) \<and> \<not>tautology (C + {#L#})"
  by unfold_locales

sublocale cdcl\<^sub>W_ops \<subseteq> cdcl\<^sub>N\<^sub>O\<^sub>T_merge_bj_learn_proxy  "convert_trail_from_W o trail" clauses
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
  case (1 C' S C F' K F L)
  moreover
    let ?C' = "remdups_mset C'"
    have "L \<notin># C'"
      using \<open>F \<Turnstile>as CNot C'\<close> \<open>undefined_lit F L\<close> Marked_Propagated_in_iff_in_lits_of
      in_CNot_implies_uminus(2) by blast
    then have "distinct_mset (?C' + {#L#})"
      by (metis count_mset_set(3) distinct_mset_remdups_mset distinct_mset_single_add
        less_irrefl_nat mem_set_mset_iff remdups_mset_def)
  moreover
    have "no_dup F"
      using \<open>inv\<^sub>N\<^sub>O\<^sub>T S\<close> \<open>(convert_trail_from_W \<circ> trail) S = F' @ Marked K () # F\<close>
      unfolding inv\<^sub>N\<^sub>O\<^sub>T_def
      by (smt comp_apply distinct.simps(2) distinct_append list.simps(9) map_append
        no_dup_convert_from_W)
    then have "consistent_interp (lits_of F)"
      using distinctconsistent_interp by blast
    then have "\<not> tautology (C')"
      using \<open>F \<Turnstile>as CNot C'\<close> consistent_CNot_not_tautology true_annots_true_cls by blast
    then have "\<not> tautology (?C' + {#L#})"
      using \<open>F \<Turnstile>as CNot C'\<close> \<open>undefined_lit F L\<close> by (metis  CNot_remdups_mset
        Marked_Propagated_in_iff_in_lits_of add.commute in_CNot_uminus tautology_add_single
        tautology_remdups_mset true_annot_singleton true_annots_def)
  show ?case
    proof -
      have f2: "no_dup ((convert_trail_from_W \<circ> trail) S)"
        using \<open>inv\<^sub>N\<^sub>O\<^sub>T S\<close> unfolding inv\<^sub>N\<^sub>O\<^sub>T_def by simp
      have f3: "atm_of L \<in> atms_of_msu (clauses S)
        \<union> atm_of ` lits_of ((convert_trail_from_W \<circ> trail) S)"
        using \<open>(convert_trail_from_W \<circ> trail) S = F' @ Marked K () # F\<close>
        \<open>atm_of L \<in> atms_of_msu (clauses S) \<union> atm_of ` lits_of (F' @ Marked K () # F)\<close> by presburger
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

sublocale cdcl\<^sub>W_ops \<subseteq> cdcl\<^sub>N\<^sub>O\<^sub>T_merge_bj_learn_proxy2  "convert_trail_from_W o trail" clauses
  "\<lambda>L S. cons_trail (convert_marked_lit_from_NOT L) S"
  "\<lambda>S. tl_trail S"
  "\<lambda>C S. add_learned_cls C S"
  "\<lambda>C S. remove_cls C S" "\<lambda>_ _. True"  inv\<^sub>N\<^sub>O\<^sub>T
  "\<lambda>_ S. conflicting S = C_True" backjump_l_cond
  by unfold_locales

sublocale cdcl\<^sub>W_ops \<subseteq> cdcl\<^sub>N\<^sub>O\<^sub>T_merge_bj_learn "convert_trail_from_W o trail" clauses
  "\<lambda>L S. cons_trail (convert_marked_lit_from_NOT L) S"
  "\<lambda>S. tl_trail S"
  "\<lambda>C S. add_learned_cls C S"
  "\<lambda>C S. remove_cls C S" "\<lambda>_ _. True"  inv\<^sub>N\<^sub>O\<^sub>T
  "\<lambda>_ S. conflicting S = C_True" backjump_l_cond
  apply unfold_locales
   using dpll_bj_no_dup apply simp
  using cdcl\<^sub>N\<^sub>O\<^sub>T.simps cdcl\<^sub>N\<^sub>O\<^sub>T_no_dup by auto

context cdcl\<^sub>W_ops
begin
text \<open>Notations are lost while proving locale inclusion:\<close>
notation state_eq\<^sub>N\<^sub>O\<^sub>T (infix "\<sim>\<^sub>N\<^sub>O\<^sub>T" 50)

subsection \<open>More lemmas conflict--propagate and backjumping\<close>
subsubsection \<open>Termination\<close>

lemma cdcl\<^sub>W_cp_normalized_element_all_inv:
  assumes inv: "cdcl\<^sub>W_all_struct_inv S"
  obtains T where "full cdcl\<^sub>W_cp S T"
  using assms cdcl\<^sub>W_cp_normalized_element unfolding cdcl\<^sub>W_all_struct_inv_def by blast
thm backtrackE

lemma cdcl\<^sub>W_bj_measure:
  assumes "cdcl\<^sub>W_bj S T" and "cdcl\<^sub>W_M_level_inv S"
  shows "length (trail S) + (if conflicting S = C_True then 0 else 1)
    > length (trail T) +  (if conflicting T = C_True then 0 else 1)"
  using assms by (induction rule: cdcl\<^sub>W_bj.induct)
  (fastforce dest:arg_cong[of _ _ length]
    intro: get_all_marked_decomposition_exists_prepend
    elim!: backtrack_levE
    simp: cdcl\<^sub>W_M_level_inv_def)+

lemma wf_cdcl\<^sub>W_bj:
  "wf {(b,a). cdcl\<^sub>W_bj a b \<and> cdcl\<^sub>W_M_level_inv a}"
  apply (rule wfP_if_measure[of "\<lambda>_. True"
      _ "\<lambda>T. length (trail T) + (if conflicting T = C_True then 0 else 1)", simplified])
  using cdcl\<^sub>W_bj_measure by blast

lemma cdcl\<^sub>W_bj_exists_normal_form:
  assumes lev: "cdcl\<^sub>W_M_level_inv S"
  shows "\<exists>T. full cdcl\<^sub>W_bj S T"
proof -
  obtain T where T: "full (\<lambda>a b. cdcl\<^sub>W_bj a b \<and> cdcl\<^sub>W_M_level_inv a) S T"
    using wf_exists_normal_form_full[OF wf_cdcl\<^sub>W_bj] by auto
  then have "cdcl\<^sub>W_bj\<^sup>*\<^sup>* S T"
     by (auto dest: rtranclp_and_rtranclp_left simp: full_def)
  moreover
    then have "cdcl\<^sub>W\<^sup>*\<^sup>* S T"
      using mono_rtranclp[of cdcl\<^sub>W_bj cdcl\<^sub>W] cdcl\<^sub>W.simps by blast
    then have "cdcl\<^sub>W_M_level_inv T"
      using rtranclp_cdcl\<^sub>W_consistent_inv lev by auto
  ultimately show ?thesis using T unfolding full_def by auto
qed

lemma rtranclp_skip_state_decomp:
  assumes "skip\<^sup>*\<^sup>* S T" and "no_dup (trail S)"
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
    "cdcl\<^sub>W_all_struct_inv S"
  shows "backtrack S W"
  using assms
proof induction
  case base
  then show ?case by simp
next
  case (step T V) note st = this(1) and skip = this(2) and IH = this(3) and bt = this(4) and
    inv = this(5)
  have "skip\<^sup>*\<^sup>* S V"
    using st skip by auto
  then have "cdcl\<^sub>W_all_struct_inv V"
    using rtranclp_mono[of skip cdcl\<^sub>W] assms(3) rtranclp_cdcl\<^sub>W_all_struct_inv_inv mono_rtranclp
    by (auto dest!: bj other cdcl\<^sub>W_bj.skip)
  then have "cdcl\<^sub>W_M_level_inv V"
    unfolding cdcl\<^sub>W_all_struct_inv_def by auto
  then obtain N k M1 M2 K D L U i where
    V: "state V = (trail V, N, U, k, C_Clause (D + {#L#}))" and
    W: "state W = (Propagated L (D + {#L#}) # M1, N, {#D + {#L#}#} + U,
      get_maximum_level D (trail V), C_True)" and
    decomp: "(Marked K (Suc i) # M1, M2)
      \<in> set (get_all_marked_decomposition (trail V))" and
    "k = get_maximum_level (D + {#L#}) (trail V)" and
    lev_L: "get_level L (trail V) = k" and
    undef: "undefined_lit M1 L" and
    "W \<sim> cons_trail (Propagated L (D + {#L#}))
      (reduce_trail_to M1 (add_learned_cls (D + {#L#})
        (update_backtrack_lvl (get_maximum_level D (trail V)) (update_conflicting C_True V))))"and
    lev_l_D: "backtrack_lvl V = get_maximum_level (D + {#L#}) (trail V)" and
    "conflicting V = C_Clause (D + {#L#})" and
    i: "i = get_maximum_level D (trail V)"
    using bt by (elim backtrack_levE) (auto simp: cdcl\<^sub>W_M_level_inv_decomp)
  let ?D = "(D + {#L#})"
  obtain L' C' where
    T: "state T = (Propagated L' C' # trail V, N, U, k, C_Clause ?D)" and
    "V \<sim> tl_trail T" and
    "-L' \<notin># ?D" and
    "?D \<noteq> {#}"
    using skip V by force

  let ?M =  "Propagated L' C' # trail V"
  have "cdcl\<^sub>W\<^sup>*\<^sup>* S T" using bj cdcl\<^sub>W_bj.skip mono_rtranclp[of skip cdcl\<^sub>W S T] other st by meson
  then have inv': "cdcl\<^sub>W_all_struct_inv T"
    using rtranclp_cdcl\<^sub>W_all_struct_inv_inv inv by blast
  have M_lev: "cdcl\<^sub>W_M_level_inv T" using inv' unfolding cdcl\<^sub>W_all_struct_inv_def by auto
  then have n_d': "no_dup ?M"
    using T unfolding cdcl\<^sub>W_M_level_inv_def by auto

  have "k > 0"
    using decomp M_lev T V unfolding cdcl\<^sub>W_M_level_inv_def by auto
  then have "atm_of L \<in> atm_of ` lits_of (trail V)"
    using lev_L get_rev_level_ge_0_atm_of_in V by fastforce
  then have L_L': "atm_of L \<noteq> atm_of L'"
    using n_d' unfolding lits_of_def by auto
  have L'_M: "atm_of L' \<notin> atm_of ` lits_of (trail V)"
    using n_d' unfolding lits_of_def by auto
  have "?M \<Turnstile>as CNot ?D"
    using inv' T unfolding cdcl\<^sub>W_conflicting_def cdcl\<^sub>W_all_struct_inv_def by auto
  then have "L' \<notin># ?D"
    using L_L' L'_M unfolding true_annots_def by (auto simp add: true_annot_def true_cls_def
      atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set Ball_mset_def
      split: split_if_asm)
  have [simp]: "trail (reduce_trail_to M1 T) = M1"
    by (metis (mono_tags, lifting) One_nat_def Pair_inject T \<open>V \<sim> tl_trail T\<close> decomp
      diff_less in_get_all_marked_decomposition_trail_update_trail length_greater_0_conv
      length_tl lessI list.distinct(1) reduce_trail_to_length_ne state_eq_trail
      trail_reduce_trail_to_length_le trail_tl_trail)
  have "skip\<^sup>*\<^sup>* S V"
    using st skip by auto
  have "no_dup (trail S)"
    using inv unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def by auto
  then have [simp]: "init_clss S = N" and [simp]: "learned_clss S = U"
    using rtranclp_skip_state_decomp[OF \<open>skip\<^sup>*\<^sup>* S V\<close>] V
    by (auto simp del: state_simp simp: state_eq_def)
  then have W_S: "W \<sim> cons_trail (Propagated L (D + {#L#})) (reduce_trail_to M1
  (add_learned_cls (D + {#L#}) (update_backtrack_lvl i (update_conflicting C_True T))))"
    using W i T undef M_lev by (auto simp del: state_simp simp: state_eq_def cdcl\<^sub>W_M_level_inv_def)

  obtain M2' where
    "(Marked K (i+1) # M1, M2') \<in> set (get_all_marked_decomposition ?M)"
    using decomp V by (cases "hd (get_all_marked_decomposition (trail V))",
      cases "get_all_marked_decomposition (trail V)") auto
  moreover
    from L_L' have "get_level L ?M = k"
      using lev_L \<open>-L' \<notin># ?D\<close> V  by (auto split: split_if_asm)
  moreover
    have "atm_of L' \<notin> atms_of D"
      using \<open>L' \<notin># ?D\<close> \<open>-L' \<notin># ?D\<close> by (simp add: atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set
        atms_of_def)
    then have "get_level L ?M = get_maximum_level (D+{#L#}) ?M"
      using lev_l_D[symmetric] L_L' V lev_L by simp
  moreover have "i = get_maximum_level D ?M"
    using i \<open>atm_of L' \<notin> atms_of D\<close> by auto
  moreover

  ultimately have "backtrack T W"
    using T(1) W_S by blast
  then show ?thesis using IH inv by blast
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
    inv: "cdcl\<^sub>W_all_struct_inv S"
  shows "backtrack T W"
  using assms
proof -
  have M_lev: "cdcl\<^sub>W_M_level_inv S "
    using bt inv unfolding cdcl\<^sub>W_all_struct_inv_def by (auto elim!: backtrack_levE)
  then obtain k M M1 M2 K i D L N U where
    S: "state S = (M, N, U, k, C_Clause (D + {#L#}))" and
    W: "state W = (Propagated L ( (D + {#L#})) # M1, N, {#D + {#L#}#} + U,
       get_maximum_level D M, C_True)" and
    decomp: "(Marked K (i+1) # M1, M2) \<in> set (get_all_marked_decomposition M)" and
    lev_l: "get_level L M = k" and
    lev_l_D: "get_level L M = get_maximum_level (D+{#L#}) M" and
    i: "i = get_maximum_level D M" and
    undef: "undefined_lit M1 L"
    using bt by (elim backtrack_levE) (force simp: cdcl\<^sub>W_M_level_inv_def)+
  let ?D = "(D + {#L#})"

  have [simp]: "no_dup (trail S)"
    using M_lev by (auto simp: cdcl\<^sub>W_M_level_inv_decomp)
  have "cdcl\<^sub>W_all_struct_inv T"
    using mono_rtranclp[of skip cdcl\<^sub>W] by (smt bj cdcl\<^sub>W_bj.skip inv local.skip  other
      rtranclp_cdcl\<^sub>W_all_struct_inv_inv)
  then have [simp]: "no_dup (trail T)"
    unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def by auto
  (* M\<^sub>T is a proxy to allow auto to unfold T*)
  obtain MS M\<^sub>T where M: "M = MS @ M\<^sub>T" and M\<^sub>T: "M\<^sub>T = trail T" and nm: "\<forall>m\<in>set MS. \<not>is_marked m"
    using rtranclp_skip_state_decomp(1)[OF skip] S M_lev by auto
  have T: "state T = (M\<^sub>T, N, U, k, C_Clause ?D)"
    using M\<^sub>T rtranclp_skip_state_decomp(2)[of S T] skip S
    by (auto simp del: state_simp simp: state_eq_def)

  have "cdcl\<^sub>W_all_struct_inv T"
    apply (rule rtranclp_cdcl\<^sub>W_all_struct_inv_inv[OF _ inv])
    using bj cdcl\<^sub>W_bj.skip local.skip other rtranclp_mono[of skip cdcl\<^sub>W] by blast
  then have "M\<^sub>T \<Turnstile>as CNot ?D"
    unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_conflicting_def using T by blast
  have "\<forall>L\<in>#?D. atm_of L \<in> atm_of ` lits_of M\<^sub>T"
    proof -
      have f1: "\<And>l. \<not> M\<^sub>T \<Turnstile>a {#- l#} \<or> atm_of l \<in> atm_of ` lits_of M\<^sub>T"
        by (simp add: atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set in_lit_of_true_annot
          lits_of_def)
      have "\<And>l. l \<notin># D \<or> - l \<in> lits_of M\<^sub>T"
        using \<open>M\<^sub>T \<Turnstile>as CNot (D + {#L#})\<close> multi_member_split by fastforce
      then show ?thesis
        using f1 by (meson \<open>M\<^sub>T \<Turnstile>as CNot (D + {#L#})\<close> ball_msetI true_annots_CNot_all_atms_defined)
    qed
  moreover have "no_dup M"
    using inv S unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def by auto
  ultimately have "\<forall>L\<in>#?D. atm_of L \<notin> atm_of ` lits_of MS"
    unfolding M unfolding lits_of_def by auto
  then have H: "\<And>L. L\<in>#?D \<Longrightarrow> get_level L M  = get_level L M\<^sub>T"
    unfolding M by (fastforce simp: lits_of_def)
  have [simp]: "get_maximum_level ?D M = get_maximum_level ?D M\<^sub>T"
    by (metis \<open>M\<^sub>T \<Turnstile>as CNot (D + {#L#})\<close>  M nm ball_msetI true_annots_CNot_all_atms_defined
      get_maximum_level_skip_un_marked_not_present)

  have lev_l': "get_level L M\<^sub>T = k"
    using lev_l by (auto simp: H)
  have [simp]: "trail (reduce_trail_to M1 T) = M1"
    using T decomp M nm by (smt M\<^sub>T append_assoc beginning_not_marked_invert
      get_all_marked_decomposition_exists_prepend reduce_trail_to_trail_tl_trail_decomp)
  have W: "W \<sim> cons_trail (Propagated L (D + {#L#})) (reduce_trail_to M1
    (add_learned_cls (D + {#L#}) (update_backtrack_lvl i (update_conflicting C_True T))))"
    using W T i decomp undef by (auto simp del: state_simp simp: state_eq_def)

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
  then have i': "i = get_maximum_level D M\<^sub>T"
    using i by auto
  have "Marked K (i + 1) # M1 \<in> set (map fst (get_all_marked_decomposition M))"
    using Set.imageI[OF decomp, of fst] by auto
  then have "Marked K (i + 1) # M1 \<in> set (map fst (get_all_marked_decomposition M\<^sub>T))"
    using fst_get_all_marked_decomposition_prepend_not_marked[OF nm] unfolding M  by auto
  then obtain M2' where decomp':"(Marked K (i+1) # M1, M2') \<in> set (get_all_marked_decomposition M\<^sub>T)"
    by auto
  then show "backtrack T W"
    using backtrack.intros[OF T decomp' lev_l'] lev_l_D' i' W by force
qed

lemma cdcl\<^sub>W_bj_decomp_resolve_skip_and_bj:
  assumes "cdcl\<^sub>W_bj\<^sup>*\<^sup>* S T" and inv: "cdcl\<^sub>W_M_level_inv S"
  shows "(skip_or_resolve\<^sup>*\<^sup>* S T
    \<or> (\<exists>U. skip_or_resolve\<^sup>*\<^sup>* S U \<and> backtrack U T))"
  using assms
proof induction
  case base
  then show ?case by simp
next
  case (step T U) note st = this(1) and bj = this(2) and IH = this(3)
  have IH: "skip_or_resolve\<^sup>*\<^sup>* S T"
    proof -
      { assume "(\<exists>U. skip_or_resolve\<^sup>*\<^sup>* S U \<and> backtrack U T)"
        then obtain V where
          bt: "backtrack V T" and
          "skip_or_resolve\<^sup>*\<^sup>* S V"
          by blast
        have "cdcl\<^sub>W\<^sup>*\<^sup>* S V"
          using \<open>skip_or_resolve\<^sup>*\<^sup>* S V\<close> rtranclp_skip_or_resolve_rtranclp_cdcl\<^sub>W by blast
        then have "cdcl\<^sub>W_M_level_inv V" and "cdcl\<^sub>W_M_level_inv S"
          using rtranclp_cdcl\<^sub>W_consistent_inv inv by blast+
        with bj bt have False using backtrack_no_cdcl\<^sub>W_bj by simp
      }
      then show ?thesis using IH inv by blast
    qed
  show ?case
    using bj
    proof (cases rule: cdcl\<^sub>W_bj.cases)
      case backtrack
      then show ?thesis using IH by blast
    qed (metis (no_types, lifting) IH rtranclp.simps)+
qed

lemma resolve_skip_deterministic:
  "resolve S T \<Longrightarrow> skip S U \<Longrightarrow> False"
  by fastforce

lemma backtrack_unique:
  assumes
    bt_T: "backtrack S T" and
    bt_U: "backtrack S U" and
    inv: "cdcl\<^sub>W_all_struct_inv S"
  shows "T \<sim> U"
proof -
  have lev: "cdcl\<^sub>W_M_level_inv S"
    using inv unfolding cdcl\<^sub>W_all_struct_inv_def by auto
  then obtain M N U' k D L i K M1 M2 where
    S: "state S = (M, N, U', k, C_Clause (D + {#L#}))" and
    decomp: "(Marked K (i+1) # M1, M2) \<in> set (get_all_marked_decomposition M)" and
    "get_level L M = k" and
    "get_level L M = get_maximum_level (D+{#L#}) M" and
    "get_maximum_level D M = i" and
    T: "state T = (Propagated L ( (D+{#L#})) # M1 , N, {#D + {#L#}#} + U', i, C_True)" and
    undef: "undefined_lit M1 L"
    using bt_T by (elim backtrack_levE) (force simp: cdcl\<^sub>W_M_level_inv_def)+

  obtain  D' L' i' K' M1' M2' where
    S': "state S = (M, N, U', k, C_Clause (D' + {#L'#}))" and
    decomp': "(Marked K' (i'+1) # M1', M2') \<in> set (get_all_marked_decomposition M)" and
    "get_level L' M = k" and
    "get_level L' M = get_maximum_level (D'+{#L'#}) M" and
    "get_maximum_level D' M = i'" and
    U: "state U = (Propagated L' ((D'+{#L'#})) # M1', N, {#D' + {#L'#}#} +U', i', C_True)" and
    undef: "undefined_lit M1' L'"
    using bt_U lev S by (elim backtrack_levE) (force simp: cdcl\<^sub>W_M_level_inv_def)+
  obtain c where M: "M = c @ M2 @ Marked K (i + 1) # M1"
    using decomp by auto
  obtain c' where M': "M = c' @ M2' @ Marked K' (i' + 1) # M1'"
    using decomp' by auto
  have marked: "get_all_levels_of_marked M = rev [1..<1+k]"
    using inv S unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def by auto
  then have "i < k"
    unfolding M
    by (force simp add: rev_swap[symmetric] dest!: arg_cong[of _ _ set])

  have [simp]: "L = L'"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then have "L' \<in># D"
        using S unfolding S' by (fastforce simp: multiset_eq_iff split: split_if_asm)
      then have "get_maximum_level D M \<ge> k"
        using \<open>get_level L' M = k\<close> get_maximum_level_ge_get_level by blast
      then show False using \<open>get_maximum_level D M = i\<close> \<open>i < k\<close> by auto
    qed
  then have [simp]: "D = D'"
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

  then have "M1 = M1'"
    using arg_cong[OF M, of "dropWhile (\<lambda>L. \<not>is_marked L \<or> level_of L \<noteq> Suc i)"]
    unfolding M' by auto
  then show ?thesis using T U by (auto simp del: state_simp simp: state_eq_def)
qed

lemma if_can_apply_backtrack_no_more_resolve:
  assumes
    skip: "skip\<^sup>*\<^sup>* S U" and
    bt: "backtrack S T" and
    inv: "cdcl\<^sub>W_all_struct_inv S"
  shows "\<not>resolve U V"
proof (rule ccontr)
  assume resolve: "\<not>\<not>resolve U V"

  obtain L C M N U' k D where
    U: "state U = (Propagated L ( (C + {#L#})) # M, N, U', k, C_Clause (D + {#-L#}))"and
    "get_maximum_level D (Propagated L ( (C + {#L#})) # M) = k" and
    "state V = (M, N, U', k, C_Clause (D #\<union> C))"
    using resolve by auto
  have "cdcl\<^sub>W_all_struct_inv U"
    using mono_rtranclp[of skip cdcl\<^sub>W] by (meson bj cdcl\<^sub>W_bj.skip inv local.skip other
      rtranclp_cdcl\<^sub>W_all_struct_inv_inv)
  then have [iff]: "no_dup (trail S)" "cdcl\<^sub>W_M_level_inv S" and [iff]: "no_dup (trail U)"
    using inv unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def by blast+
  then have
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
    undef: "undefined_lit M1 L'" and
    T: "state T = (Propagated L' (D'+{#L'#}) # M1 , N, {#D' + {#L'#}#}+U', i, C_True)"
    using bt S by (force elim!: backtrack_levE)
  obtain c where M: "M' = c @ M2 @ Marked K (i + 1) # M1"
    using get_all_marked_decomposition_exists_prepend[OF decomp] by auto
  have marked: "get_all_levels_of_marked M' = rev [1..<1+k]"
    using inv S' unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def by auto
  then have "i < k"
    unfolding M by (force simp add: rev_swap[symmetric] dest!: arg_cong[of _ _ set])

  have DD': "D' + {#L'#} = D + {#-L#}"
    using S S' by auto
  have [simp]: "L' = -L"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then have "-L \<in># D'"
        using DD' by (metis add_diff_cancel_right' diff_single_trivial diff_union_swap
          multi_self_add_other_not_self)
      moreover
        have M': "M' = M\<^sub>0 @ Propagated L ( (C + {#L#})) # M"
          using tr_S U S S' by (auto simp: lits_of_def)
        have "no_dup M'"
           using inv U S' unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def by auto
        have atm_L_notin_M: "atm_of L \<notin> atm_of ` (lits_of M)"
          using \<open>no_dup M'\<close> M' U S S' by (auto simp: lits_of_def)
        have "get_all_levels_of_marked M' = rev [1..<1+k]"
          using inv U S' unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def by auto
        then have "get_all_levels_of_marked M = rev [1..<1+k]"
          using nm M' S' U by (simp add: get_all_levels_of_marked_no_marked)
        then have get_lev_L:
          "get_level L (Propagated L ( (C + {#L#})) # M) = k"
          using get_level_get_rev_level_get_all_levels_of_marked[OF atm_L_notin_M,
            of "[Propagated L ((C + {#L#}))]"] by simp
        have "atm_of L \<notin> atm_of ` (lits_of (rev M\<^sub>0))"
          using \<open>no_dup M'\<close> M' U S' by (auto simp: lits_of_def)
        then have "get_level L M' = k"
          using get_rev_level_notin_end[of L "rev M\<^sub>0" 0
            "rev M @ Propagated L ( (C + {#L#})) # []"]
          using tr_S get_lev_L M' U S' by (simp add:nm lits_of_def)
      ultimately have "get_maximum_level D' M' \<ge> k"
        by (metis get_maximum_level_ge_get_level get_rev_level_uminus)
      then show False
        using \<open>i < k\<close> unfolding \<open>get_maximum_level D' M' = i\<close> by auto
    qed
  have [simp]: "D = D'" using DD' by auto
  have "cdcl\<^sub>W\<^sup>*\<^sup>* S U"
    using bj cdcl\<^sub>W_bj.skip local.skip mono_rtranclp[of skip cdcl\<^sub>W S U] other by meson
  then have "cdcl\<^sub>W_all_struct_inv U"
    using inv rtranclp_cdcl\<^sub>W_all_struct_inv_inv by blast
  then have "Propagated L ( (C + {#L#})) # M \<Turnstile>as CNot (D' + {#L'#})"
    using cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_conflicting_def U by auto
  then have "\<forall>L'\<in>#D. atm_of L' \<in> atm_of ` lits_of (Propagated L ( (C + {#L#})) # M)"
    by (metis CNot_plus CNot_singleton Un_insert_right \<open>D = D'\<close> true_annots_insert ball_msetI
      atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set  in_CNot_implies_uminus(2)
      sup_bot.comm_neutral)
  then have "get_maximum_level D M' = k"
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
    inv: "cdcl\<^sub>W_all_struct_inv S"
  shows "\<not>backtrack U V"
  using assms
  by (meson if_can_apply_backtrack_no_more_resolve rtranclp.rtrancl_refl
    rtranclp_skip_backtrack_backtrack)

lemma if_can_apply_backtrack_skip_or_resolve_is_skip:
  assumes
    bt: "backtrack S T" and
    skip: "skip_or_resolve\<^sup>*\<^sup>* S U" and
    inv: "cdcl\<^sub>W_all_struct_inv S"
  shows "skip\<^sup>*\<^sup>* S U"
  using assms(2,3,1)
  by induction (simp_all add: if_can_apply_backtrack_no_more_resolve)

lemma cdcl\<^sub>W_bj_bj_decomp:
  assumes "cdcl\<^sub>W_bj\<^sup>*\<^sup>* S W" and "cdcl\<^sub>W_all_struct_inv S"
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
  then show ?case by simp
next
  case (step W X) note st = this(1) and bj = this(2) and IH = this(3)[OF this(4)] and inv = this(4)

  have "\<not>?RB S W" and "\<not>?SB S W"
    proof (clarify, goal_cases)
      case (1 T U V)
      have "skip_or_resolve\<^sup>*\<^sup>* S T"
        using 1(1) by (auto dest!: rtranclp_and_rtranclp_left)
      then show "False"
        by (metis (no_types, lifting) "1"(2) "1"(4) "1"(5) backtrack_no_cdcl\<^sub>W_bj
          cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_all_struct_inv_inv cdcl\<^sub>W_o.bj local.bj other
          resolve rtranclp_cdcl\<^sub>W_all_struct_inv_inv rtranclp_skip_backtrack_backtrack
          rtranclp_skip_or_resolve_rtranclp_cdcl\<^sub>W step.prems)
    next
      case 2
      then show ?case by (meson assms(2) cdcl\<^sub>W_all_struct_inv_def backtrack_no_cdcl\<^sub>W_bj
        local.bj rtranclp_skip_backtrack_backtrack)
    qed
  then have IH: "?R S W \<or> ?S S W" using IH by blast

  have "cdcl\<^sub>W\<^sup>*\<^sup>* S W" by (metis cdcl\<^sub>W_o.bj mono_rtranclp other st)
  then have inv_W: "cdcl\<^sub>W_all_struct_inv W" by (simp add: rtranclp_cdcl\<^sub>W_all_struct_inv_inv
    step.prems)
  consider
      (BT) X' where "backtrack W X'"
    | (skip) "no_step backtrack W" and "skip W X"
    | (resolve) "no_step backtrack W" and "resolve W X"
    using bj cdcl\<^sub>W_bj.cases by meson
  then show ?case
    proof cases
      case (BT X')
      then consider
          (bt) "backtrack W X"
        | (sk) "skip W X"
        using bj if_can_apply_backtrack_no_more_resolve[of W W X' X] inv_W cdcl\<^sub>W_bj.cases by fast
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
      then show ?thesis using IH  by (meson rtranclp.rtrancl_into_rtrancl)
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
      then show ?thesis
        proof cases
          case (RS T U)
          have "cdcl\<^sub>W\<^sup>*\<^sup>* S T"
            using  RS(1) cdcl\<^sub>W_bj.resolve cdcl\<^sub>W_o.bj  other skip
            mono_rtranclp[of " (\<lambda>S T. skip_or_resolve S T \<and> no_step backtrack S)" cdcl\<^sub>W S T]
            by meson
          then have "cdcl\<^sub>W_all_struct_inv U"
            by (meson RS(2) cdcl\<^sub>W_all_struct_inv_inv cdcl\<^sub>W_bj.resolve cdcl\<^sub>W_o.bj other
              rtranclp_cdcl\<^sub>W_all_struct_inv_inv step.prems)
          { fix U'
            assume "skip\<^sup>*\<^sup>* U U'" and "skip\<^sup>*\<^sup>* U' W"
            have "cdcl\<^sub>W_all_struct_inv U'"
              using \<open>cdcl\<^sub>W_all_struct_inv U\<close> \<open>skip\<^sup>*\<^sup>* U U'\<close> rtranclp_cdcl\<^sub>W_all_struct_inv_inv
                 cdcl\<^sub>W_o.bj rtranclp_mono[of skip cdcl\<^sub>W] other skip by blast
            then have "no_step backtrack U'"
              using if_can_apply_backtrack_no_more_resolve[OF \<open>skip\<^sup>*\<^sup>* U' W\<close> ] res by blast
          }
          with \<open>skip\<^sup>*\<^sup>* U W\<close>
          have "(\<lambda>S T. skip_or_resolve S T \<and> no_step backtrack S)\<^sup>*\<^sup>* U W"
             proof induction
               case base
               then show ?case by simp
             next
               case (step V W) note st = this(1) and skip = this(2) and IH = this(3) and H = this(4)
               have "\<And>U'. skip\<^sup>*\<^sup>* U' V \<Longrightarrow> skip\<^sup>*\<^sup>* U' W"
                 using skip by auto
               then have "(\<lambda>S T. skip_or_resolve S T \<and> no_step backtrack S)\<^sup>*\<^sup>* U V"
                 using IH H by blast
               moreover have "(\<lambda>S T. skip_or_resolve S T \<and> no_step backtrack S)\<^sup>*\<^sup>* V W"
                 (* adding the \<^sup>*\<^sup>* here makes the ?case easier to find *)
                 by (simp add: local.skip r_into_rtranclp st step.prems)
               ultimately show ?case by simp
             qed
          then show ?thesis
            proof -
              have f1: "\<forall>p pa pb pc. \<not> p (pa) pb \<or> \<not> p\<^sup>*\<^sup>* pb pc \<or> p\<^sup>*\<^sup>* pa pc"
                by (meson converse_rtranclp_into_rtranclp)
              have "skip_or_resolve T U \<and> no_step backtrack T"
                using RS(2) RS(3) by force
              then have "(\<lambda>p pa. skip_or_resolve p pa \<and> no_step backtrack p)\<^sup>*\<^sup>* T W"
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
              then have "(\<lambda>p pa. skip_or_resolve p pa \<and> no_step backtrack p)\<^sup>*\<^sup>* S W"
                using RS(1) by force
              then show ?thesis
                using no_bt res by blast
            qed
        next
          case S
          { fix U'
            assume "skip\<^sup>*\<^sup>* S U'" and "skip\<^sup>*\<^sup>* U' W"
            then have "cdcl\<^sub>W\<^sup>*\<^sup>* S U'"
              using mono_rtranclp[of skip cdcl\<^sub>W S U'] by (simp add: cdcl\<^sub>W_o.bj other skip)
            then have "cdcl\<^sub>W_all_struct_inv U'"
              by (metis (no_types, hide_lams) \<open>cdcl\<^sub>W_all_struct_inv S\<close> rtranclp_cdcl\<^sub>W_all_struct_inv_inv)
            then have "no_step backtrack U'"
              using if_can_apply_backtrack_no_more_resolve[OF \<open>skip\<^sup>*\<^sup>* U' W\<close> ] res by blast
          }
          with S
          have "(\<lambda>S T. skip_or_resolve S T \<and> no_step backtrack S)\<^sup>*\<^sup>* S W"
             proof induction
               case base
               then show ?case by simp
             next
               case (step V W) note st = this(1) and skip = this(2) and IH = this(3) and H = this(4)
               have "\<And>U'. skip\<^sup>*\<^sup>* U' V \<Longrightarrow> skip\<^sup>*\<^sup>* U' W"
                 using skip by auto
               then have "(\<lambda>S T. skip_or_resolve S T \<and> no_step backtrack S)\<^sup>*\<^sup>* S V"
                 using IH H by blast
               moreover have "(\<lambda>S T. skip_or_resolve S T \<and> no_step backtrack S)\<^sup>*\<^sup>* V W"
                 (* adding the \<^sup>*\<^sup>* here makes the ?case easier to find *)
                 by (simp add: local.skip r_into_rtranclp st step.prems)
               ultimately show ?case by simp
             qed
          then show ?thesis using res no_bt by blast
        qed
    qed
qed

paragraph \<open>Backjumping is confluent\<close>
(* TODO Move *)
lemma cdcl\<^sub>W_bj_state_eq_compatible:
  assumes
    "cdcl\<^sub>W_bj S T" and "cdcl\<^sub>W_M_level_inv S"
    "S \<sim> S'" and
    "T \<sim> T'"
  shows "cdcl\<^sub>W_bj S' T'"
  using assms
  by induction (auto
    intro: skip_state_eq_compatible backtrack_state_eq_compatible resolve_state_eq_compatible)

lemma tranclp_cdcl\<^sub>W_bj_state_eq_compatible:
  assumes
    "cdcl\<^sub>W_bj\<^sup>+\<^sup>+ S T" and  inv: "cdcl\<^sub>W_M_level_inv S" and
    "S \<sim> S'" and
    "T \<sim> T'"
  shows "cdcl\<^sub>W_bj\<^sup>+\<^sup>+ S' T'"
  using assms
proof (induction arbitrary: S' T')
  case base
  then show ?case
    using cdcl\<^sub>W_bj_state_eq_compatible by blast
next
  case (step T U) note IH = this(3)[OF this(4-5)]
  have "cdcl\<^sub>W\<^sup>+\<^sup>+ S T"
    using tranclp_mono[of cdcl\<^sub>W_bj cdcl\<^sub>W] other step.hyps(1) by blast
  then have "cdcl\<^sub>W_M_level_inv T"
    using inv tranclp_cdcl\<^sub>W_consistent_inv by blast
  then have "cdcl\<^sub>W_bj\<^sup>+\<^sup>+ T T'"
    using \<open>U \<sim> T'\<close> cdcl\<^sub>W_bj_state_eq_compatible[of T U] \<open>cdcl\<^sub>W_bj T U\<close> by auto
  then show ?case
    using IH[of T] by auto
qed

text \<open>The case distinction is needed, since @{term "T \<sim> V"} does not imply that @{term "R\<^sup>*\<^sup>* T V"}.\<close>
lemma cdcl\<^sub>W_bj_strongly_confluent:
   assumes
     "cdcl\<^sub>W_bj\<^sup>*\<^sup>* S V" and
     "cdcl\<^sub>W_bj\<^sup>*\<^sup>* S T" and
     n_s: "no_step cdcl\<^sub>W_bj V" and
     inv: "cdcl\<^sub>W_all_struct_inv S"
   shows "T \<sim> V \<or> cdcl\<^sub>W_bj\<^sup>*\<^sup>* T V"
   using assms(2)
proof induction
  case base
  then show ?case by (simp add: assms(1))
next
  case (step T U) note st = this(1) and s_o_r = this(2) and IH = this(3)
  have "cdcl\<^sub>W\<^sup>*\<^sup>* S T"
    using st mono_rtranclp[of cdcl\<^sub>W_bj cdcl\<^sub>W] other by blast
  then have lev_T: "cdcl\<^sub>W_M_level_inv T"
    using inv rtranclp_cdcl\<^sub>W_consistent_inv[of S T]
    unfolding cdcl\<^sub>W_all_struct_inv_def by auto

  consider
       (TV) "T \<sim> V"
     | (bj_TV) "cdcl\<^sub>W_bj\<^sup>*\<^sup>* T V"
    using IH by blast
  then show ?case
    proof cases
      case TV
      have "no_step cdcl\<^sub>W_bj T"
        using \<open>cdcl\<^sub>W_M_level_inv T\<close> n_s cdcl\<^sub>W_bj_state_eq_compatible[of T _ V] TV by auto
      then show ?thesis
        using s_o_r by auto
    next
      case bj_TV
      then obtain U' where
        T_U': "cdcl\<^sub>W_bj T U'" and
        "cdcl\<^sub>W_bj\<^sup>*\<^sup>* U' V"
        using IH n_s s_o_r by (metis rtranclp_unfold tranclpD)
      have "cdcl\<^sub>W\<^sup>*\<^sup>* S T"
        by (metis (no_types, hide_lams) bj mono_rtranclp[of cdcl\<^sub>W_bj cdcl\<^sub>W] other st)
      then have inv_T: "cdcl\<^sub>W_all_struct_inv T"
        by (metis (no_types, hide_lams) inv rtranclp_cdcl\<^sub>W_all_struct_inv_inv)

      have lev_U: "cdcl\<^sub>W_M_level_inv U"
        using s_o_r cdcl\<^sub>W_consistent_inv lev_T other by blast
      show ?thesis
        using s_o_r
        proof cases
          case backtrack
          then obtain V0 where "skip\<^sup>*\<^sup>* T V0" and "backtrack V0 V"
            using IH if_can_apply_backtrack_skip_or_resolve_is_skip[OF backtrack _ inv_T]
             cdcl\<^sub>W_bj_decomp_resolve_skip_and_bj
             by (meson bj_TV cdcl\<^sub>W_bj.backtrack inv_T lev_T n_s
               rtranclp_skip_backtrack_backtrack_end)
          then have "cdcl\<^sub>W_bj\<^sup>*\<^sup>* T V0" and "cdcl\<^sub>W_bj V0 V"
            using rtranclp_mono[of skip cdcl\<^sub>W_bj] by blast+
          then show ?thesis
            using \<open>backtrack V0 V\<close> \<open>skip\<^sup>*\<^sup>* T V0\<close> backtrack_unique inv_T local.backtrack
            rtranclp_skip_backtrack_backtrack by auto
        next
          case resolve
          then have "U \<sim> U'"
            by (meson T_U' cdcl\<^sub>W_bj.simps if_can_apply_backtrack_no_more_resolve inv_T
              resolve_skip_deterministic resolve_unique rtranclp.rtrancl_refl)
          then show ?thesis
            using \<open>cdcl\<^sub>W_bj\<^sup>*\<^sup>* U' V\<close> unfolding rtranclp_unfold
            by (meson T_U' bj cdcl\<^sub>W_consistent_inv lev_T other state_eq_ref state_eq_sym
              tranclp_cdcl\<^sub>W_bj_state_eq_compatible)
        next
          case skip
          consider
              (sk)  "skip T U'"
            | (bt)  "backtrack T U'"
            using T_U' by (meson cdcl\<^sub>W_bj.cases local.skip resolve_skip_deterministic)
          then show ?thesis
            proof cases
              case sk
              then show ?thesis
                using \<open>cdcl\<^sub>W_bj\<^sup>*\<^sup>* U' V\<close> unfolding rtranclp_unfold
                by (meson T_U' bj cdcl\<^sub>W_all_inv(3) cdcl\<^sub>W_all_struct_inv_def inv_T local.skip other
                  tranclp_cdcl\<^sub>W_bj_state_eq_compatible skip_unique state_eq_ref)
            next
              case bt
              have "skip\<^sup>+\<^sup>+ T U"
                using local.skip by blast
              then show ?thesis
                using bt by (metis \<open>cdcl\<^sub>W_bj\<^sup>*\<^sup>* U' V\<close> backtrack inv_T tranclp_unfold_begin
                  rtranclp_skip_backtrack_backtrack_end tranclp_into_rtranclp)
            qed
        qed
    qed
qed


lemma cdcl\<^sub>W_bj_unique_normal_form:
  assumes
    ST: "cdcl\<^sub>W_bj\<^sup>*\<^sup>* S T" and SU: "cdcl\<^sub>W_bj\<^sup>*\<^sup>* S U" and
    n_s_U: "no_step cdcl\<^sub>W_bj U" and
    n_s_T: "no_step cdcl\<^sub>W_bj T" and
    inv: "cdcl\<^sub>W_all_struct_inv S"
  shows "T \<sim> U"
proof -
  have "T \<sim> U \<or> cdcl\<^sub>W_bj\<^sup>*\<^sup>* T U"
    using ST SU cdcl\<^sub>W_bj_strongly_confluent inv n_s_U by blast
  then show ?thesis
    by (metis (no_types) n_s_T rtranclp_unfold state_eq_ref tranclp_unfold_begin)
qed

lemma full_cdcl\<^sub>W_bj_unique_normal_form:
 assumes "full cdcl\<^sub>W_bj S T" and "full cdcl\<^sub>W_bj S U" and
   inv: "cdcl\<^sub>W_all_struct_inv S"
 shows "T \<sim> U"
   using cdcl\<^sub>W_bj_unique_normal_form assms unfolding full_def by blast

subsection \<open>CDCL FW\<close>
inductive cdcl\<^sub>W_merge_restart :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
fw_r_propagate: "propagate S S' \<Longrightarrow> cdcl\<^sub>W_merge_restart S S'" |
fw_r_conflict: "conflict S T \<Longrightarrow> full cdcl\<^sub>W_bj T U \<Longrightarrow> cdcl\<^sub>W_merge_restart S U" |
fw_r_decide: "decide S S' \<Longrightarrow> cdcl\<^sub>W_merge_restart S S'"|
fw_r_rf: "cdcl\<^sub>W_rf S S' \<Longrightarrow> cdcl\<^sub>W_merge_restart S S'"

lemma cdcl\<^sub>W_merge_restart_cdcl\<^sub>W:
  assumes "cdcl\<^sub>W_merge_restart S T"
  shows "cdcl\<^sub>W\<^sup>*\<^sup>* S T"
  using assms
proof induction
  case (fw_r_conflict S T U) note confl = this(1) and bj = this(2)
  have "cdcl\<^sub>W S T" using confl by (simp add: cdcl\<^sub>W.intros r_into_rtranclp)
  moreover
    have "cdcl\<^sub>W_bj\<^sup>*\<^sup>* T U" using bj unfolding full_def by auto
    then have "cdcl\<^sub>W\<^sup>*\<^sup>* T U" by (metis cdcl\<^sub>W_o.bj mono_rtranclp other)
  ultimately show ?case by auto
qed (simp_all add: cdcl\<^sub>W_o.intros cdcl\<^sub>W.intros r_into_rtranclp)

lemma cdcl\<^sub>W_merge_restart_conflicting_true_or_no_step:
  assumes "cdcl\<^sub>W_merge_restart S T"
  shows "conflicting T = C_True \<or> no_step cdcl\<^sub>W T"
  using assms
proof induction
  case (fw_r_conflict S T U) note confl = this(1) and n_s = this(2)
  { fix D V
    assume "cdcl\<^sub>W U V" and "conflicting U = C_Clause D"
    then have False
      using n_s unfolding full_def
      by (induction rule: cdcl\<^sub>W_all_rules_induct) (auto dest!: cdcl\<^sub>W_bj.intros )
  }
  then show ?case by (cases "conflicting U") fastforce+
qed (auto simp add: cdcl\<^sub>W_rf.simps)

inductive cdcl\<^sub>W_merge :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
fw_propagate: "propagate S S' \<Longrightarrow> cdcl\<^sub>W_merge S S'" |
fw_conflict: "conflict S T \<Longrightarrow> full cdcl\<^sub>W_bj T U \<Longrightarrow> cdcl\<^sub>W_merge S U" |
fw_decide: "decide S S' \<Longrightarrow> cdcl\<^sub>W_merge S S'"|
fw_forget: "forget S S' \<Longrightarrow> cdcl\<^sub>W_merge S S'"

lemma cdcl\<^sub>W_merge_cdcl\<^sub>W_merge_restart:
  "cdcl\<^sub>W_merge S T \<Longrightarrow> cdcl\<^sub>W_merge_restart S T"
  by (meson cdcl\<^sub>W_merge.cases cdcl\<^sub>W_merge_restart.simps forget)

lemma rtranclp_cdcl\<^sub>W_merge_tranclp_cdcl\<^sub>W_merge_restart:
  "cdcl\<^sub>W_merge\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl\<^sub>W_merge_restart\<^sup>*\<^sup>* S T"
  using rtranclp_mono[of cdcl\<^sub>W_merge cdcl\<^sub>W_merge_restart] cdcl\<^sub>W_merge_cdcl\<^sub>W_merge_restart by blast

lemma cdcl\<^sub>W_merge_rtranclp_cdcl\<^sub>W:
  "cdcl\<^sub>W_merge S T \<Longrightarrow> cdcl\<^sub>W\<^sup>*\<^sup>* S T"
  using cdcl\<^sub>W_merge_cdcl\<^sub>W_merge_restart cdcl\<^sub>W_merge_restart_cdcl\<^sub>W by blast

lemma rtranclp_cdcl\<^sub>W_merge_rtranclp_cdcl\<^sub>W:
  "cdcl\<^sub>W_merge\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl\<^sub>W\<^sup>*\<^sup>* S T"
  using rtranclp_mono[of cdcl\<^sub>W_merge "cdcl\<^sub>W\<^sup>*\<^sup>*"] cdcl\<^sub>W_merge_rtranclp_cdcl\<^sub>W by auto

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
"no_dup (trail S) \<Longrightarrow>
  trail (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T M (add_learned_cls D S)) = trail (reduce_trail_to\<^sub>N\<^sub>O\<^sub>T M S)"
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

lemma cdcl\<^sub>W_merge_is_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn:
  assumes
    inv: "cdcl\<^sub>W_all_struct_inv S" and
    cdcl\<^sub>W:"cdcl\<^sub>W_merge S T"
  shows "cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn S T
    \<or> (no_step cdcl\<^sub>W_merge T \<and> conflicting T \<noteq> C_True)"
  using cdcl\<^sub>W inv
proof induction
  case (fw_propagate S T) note propa = this(1)
  then obtain M N U k L C where
    H: "state S = (M, N, U, k, C_True)" and
    CL: "C + {#L#} \<in># clauses S" and
    M_C: "M \<Turnstile>as CNot C" and
    undef: "undefined_lit (trail S) L" and
    T: "T \<sim> cons_trail (Propagated L (C + {#L#})) S"
    using propa by auto
  have "propagate\<^sub>N\<^sub>O\<^sub>T S T"
    apply (rule propagate\<^sub>N\<^sub>O\<^sub>T.propagate\<^sub>N\<^sub>O\<^sub>T[of _ C L])
    using H CL T undef M_C by (auto simp: state_eq\<^sub>N\<^sub>O\<^sub>T_def state_eq_def clauses_def
      simp del: state_simp\<^sub>N\<^sub>O\<^sub>T state_simp)
  then show ?case
    using cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn.intros(2) by blast
next
  case (fw_decide S T) note dec = this(1) and inv = this(2)
  then obtain L where
    undef_L: "undefined_lit (trail S) L" and
    atm_L: "atm_of L \<in> atms_of_msu (init_clss S)" and
    T: "T \<sim> cons_trail (Marked L (Suc (backtrack_lvl S)))
      (update_backtrack_lvl (Suc (backtrack_lvl S)) S)"
    by auto
  have "decide\<^sub>N\<^sub>O\<^sub>T S T"
    apply (rule decide\<^sub>N\<^sub>O\<^sub>T.decide\<^sub>N\<^sub>O\<^sub>T)
       using undef_L apply simp
     using atm_L inv unfolding cdcl\<^sub>W_all_struct_inv_def no_strange_atm_def clauses_def apply auto[]
    using T undef_L unfolding state_eq_def state_eq\<^sub>N\<^sub>O\<^sub>T_def by (auto simp: clauses_def)
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
    using inv C_le unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_learned_clause_def
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
      then have "conflicting U \<noteq> C_True"
        using confl by (induction rule: rtranclp_induct) auto
      moreover then have "no_step cdcl\<^sub>W_merge U"
        by (auto simp: cdcl\<^sub>W_merge.simps)
      ultimately show ?thesis by blast
    next
      case bt note s_or_r = this(1) and bt = this(2)
      have "cdcl\<^sub>W\<^sup>*\<^sup>* T T'"
        using s_or_r mono_rtranclp[of skip_or_resolve cdcl\<^sub>W] rtranclp_skip_or_resolve_rtranclp_cdcl\<^sub>W
        by blast
      then have "cdcl\<^sub>W_M_level_inv T'"
        using rtranclp_cdcl\<^sub>W_consistent_inv \<open>cdcl\<^sub>W_M_level_inv T\<close> by blast
      then obtain M1 M2 i D L K where
        confl_T': "conflicting T' = C_Clause (D + {#L#})" and
        M1_M2:"(Marked K (i+1) # M1, M2) \<in> set (get_all_marked_decomposition (trail T'))" and
        "get_level L (trail T') = backtrack_lvl T'" and
        "get_level L (trail T') = get_maximum_level (D+{#L#}) (trail T')" and
        "get_maximum_level D (trail T') = i" and
        undef_L: "undefined_lit M1 L" and
        U: "U \<sim> cons_trail (Propagated L (D+{#L#}))
                 (reduce_trail_to M1
                      (add_learned_cls (D + {#L#})
                         (update_backtrack_lvl i
                            (update_conflicting C_True T'))))"
        using bt by (auto elim: backtrack_levE)
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
      then have atm_L: "atm_of L \<in> atms_of_msu (clauses S)"
        using inv_T' confl_T' unfolding cdcl\<^sub>W_all_struct_inv_def no_strange_atm_def clauses_def
        by auto
      obtain M where tr_T: "trail T = M @ trail T'"
        using s_or_r by (induction rule: rtranclp_induct) auto
      obtain M' where
        tr_T': "trail T' = M' @  Marked K (i+1) # tl (trail U)" and
        tr_U: "trail U = Propagated L (D + {#L#}) # tl (trail U)"
        using U M1_M2 undef_L inv_T' unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def
        by auto
      def M'' \<equiv> "M @ M'"
        have tr_T: "trail S = M'' @  Marked K (i+1) # tl (trail U)"
        using tr_T tr_T' confl unfolding M''_def by auto
      have "init_clss T' + learned_clss S \<Turnstile>pm D + {#L#}"
        using inv_T' confl_T' unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_learned_clause_def clauses_def
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
        using inv_U unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_conflicting_def by simp
      then have "tl (trail U) \<Turnstile>as CNot D"
        by (metis add_diff_cancel_left' append_self_conv2 tr_U union_commute)
      have "backjump_l S U"
        apply (rule backjump_l[of _ _ _ _ _ L])
                 using tr_T apply simp
                using inv unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def apply simp
               using U M1_M2 confl undef_L M1_M2 inv_T' inv unfolding cdcl\<^sub>W_all_struct_inv_def
               cdcl\<^sub>W_M_level_inv_def apply (auto simp: state_eq\<^sub>N\<^sub>O\<^sub>T_def simp del: state_simp\<^sub>N\<^sub>O\<^sub>T)[]
              using C\<^sub>S apply simp
             using tr_S_C\<^sub>S apply simp

            using U undef_L M1_M2  inv_T' inv unfolding cdcl\<^sub>W_all_struct_inv_def
            cdcl\<^sub>W_M_level_inv_def apply auto[]
           using undef_L atm_L apply simp
          using \<open>init_clss T' + learned_clss S \<Turnstile>pm D + {#L#}\<close> unfolding clauses_def apply simp
         apply (metis \<open>tl (trail U) \<Turnstile>as CNot D\<close> convert_trail_from_W_tl
           convert_trail_from_W_true_annots)
        using  inv_T' inv_U U confl_T' undef_L M1_M2 unfolding cdcl\<^sub>W_all_struct_inv_def
        distinct_cdcl\<^sub>W_state_def by (simp add: cdcl\<^sub>W_M_level_inv_decomp)
      then show ?thesis using cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_backjump_l by fast
    qed
qed

abbreviation cdcl\<^sub>N\<^sub>O\<^sub>T_restart where
"cdcl\<^sub>N\<^sub>O\<^sub>T_restart \<equiv> restart_ops.cdcl\<^sub>N\<^sub>O\<^sub>T_raw_restart cdcl\<^sub>N\<^sub>O\<^sub>T restart"

lemma cdcl\<^sub>W_merge_restart_is_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn_restart_no_step:
  assumes
    inv: "cdcl\<^sub>W_all_struct_inv S" and
    cdcl\<^sub>W:"cdcl\<^sub>W_merge_restart S T"
  shows "cdcl\<^sub>N\<^sub>O\<^sub>T_restart\<^sup>*\<^sup>* S T \<or> (no_step cdcl\<^sub>W_merge T \<and> conflicting T \<noteq> C_True)"
proof -
  consider
      (fw) "cdcl\<^sub>W_merge S T"
    | (fw_r) "restart S T"
    using cdcl\<^sub>W by (meson cdcl\<^sub>W_merge_restart.simps cdcl\<^sub>W_rf.cases fw_conflict fw_decide fw_forget
      fw_propagate)
  then show ?thesis
    proof cases
      case fw
      then have IH: "cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn S T \<or> (no_step cdcl\<^sub>W_merge T \<and> conflicting T \<noteq> C_True)"
        using inv cdcl\<^sub>W_merge_is_cdcl\<^sub>N\<^sub>O\<^sub>T_merged_bj_learn by blast
      have invS: "inv\<^sub>N\<^sub>O\<^sub>T S"
        using inv unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def by auto
      have ff2: "cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>+\<^sup>+ S T \<longrightarrow> cdcl\<^sub>N\<^sub>O\<^sub>T\<^sup>*\<^sup>* S T"
          by (meson tranclp_into_rtranclp)
      have ff3: "no_dup ((convert_trail_from_W \<circ> trail) S)"
        using invS by simp
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
  have atm_clauses: "atms_of_msu (clauses S) \<subseteq> atms_of_msu ?A"
    using inv unfolding cdcl\<^sub>W_all_struct_inv_def no_strange_atm_def clauses_def by auto
  have atm_trail: "atm_of ` lits_of (trail S) \<subseteq> atms_of_msu ?A"
    using inv unfolding cdcl\<^sub>W_all_struct_inv_def no_strange_atm_def clauses_def by auto
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
        by (auto split: split_if)
    next
      case n_s
      then show ?thesis by simp
    qed
qed

lemma wf_cdcl\<^sub>W_merge: "wf {(T, S). cdcl\<^sub>W_all_struct_inv S \<and> cdcl\<^sub>W_merge S T}"
  apply (rule wfP_if_measure[of _ _ "\<mu>\<^sub>F\<^sub>W"])
  using cdcl\<^sub>W_merge_\<mu>\<^sub>F\<^sub>W_decreasing by blast

lemma cdcl\<^sub>W_all_struct_inv_tranclp_cdcl\<^sub>W_merge_tranclp_cdcl\<^sub>W_merge_cdcl\<^sub>W_all_struct_inv:
  assumes
    inv: "cdcl\<^sub>W_all_struct_inv b"
    "cdcl\<^sub>W_merge\<^sup>+\<^sup>+ b a"
  shows "(\<lambda>S T. cdcl\<^sub>W_all_struct_inv S \<and> cdcl\<^sub>W_merge S T)\<^sup>+\<^sup>+ b a"
  using assms(2)
proof induction
  case base
  then show ?case using inv by auto
next
  case (step c d) note st =this(1) and fw = this(2) and IH = this(3)
  have "cdcl\<^sub>W_all_struct_inv c"
    using tranclp_into_rtranclp[OF st] cdcl\<^sub>W_merge_rtranclp_cdcl\<^sub>W
    assms(1) rtranclp_cdcl\<^sub>W_all_struct_inv_inv rtranclp_mono[of cdcl\<^sub>W_merge "cdcl\<^sub>W\<^sup>*\<^sup>*"] by fastforce
  then have "(\<lambda>S T. cdcl\<^sub>W_all_struct_inv S \<and> cdcl\<^sub>W_merge S T)\<^sup>+\<^sup>+ c d"
    using fw by auto
  then show ?case using IH by auto
qed

lemma wf_tranclp_cdcl\<^sub>W_merge: "wf {(T, S). cdcl\<^sub>W_all_struct_inv S \<and> cdcl\<^sub>W_merge\<^sup>+\<^sup>+ S T}"
  using wf_trancl[OF wf_cdcl\<^sub>W_merge]
  apply (rule wf_subset)
  by (auto simp: trancl_set_tranclp
    cdcl\<^sub>W_all_struct_inv_tranclp_cdcl\<^sub>W_merge_tranclp_cdcl\<^sub>W_merge_cdcl\<^sub>W_all_struct_inv)

lemma backtrack_is_full1_cdcl\<^sub>W_bj:
  assumes bt: "backtrack S T" and inv: "cdcl\<^sub>W_M_level_inv S"
  shows "full1 cdcl\<^sub>W_bj S T"
proof -
  have "no_step cdcl\<^sub>W_bj T"
    using bt inv backtrack_no_cdcl\<^sub>W_bj by blast
  moreover have "cdcl\<^sub>W_bj\<^sup>+\<^sup>+ S T"
    using bt by auto
  ultimately show ?thesis unfolding full1_def by blast
qed

lemma rtrancl_cdcl\<^sub>W_conflicting_true_cdcl\<^sub>W_merge_restart:
  assumes "cdcl\<^sub>W\<^sup>*\<^sup>* S V" and inv: "cdcl\<^sub>W_M_level_inv S" and "conflicting S = C_True"
  shows "(cdcl\<^sub>W_merge_restart\<^sup>*\<^sup>* S V \<and> conflicting V = C_True)
    \<or> (\<exists>T U. cdcl\<^sub>W_merge_restart\<^sup>*\<^sup>* S T \<and> conflicting V \<noteq> C_True \<and> conflict T U \<and> cdcl\<^sub>W_bj\<^sup>*\<^sup>* U V)"
  using assms
proof induction
  case base
  then show ?case by simp
next
  case (step U V) note st = this(1) and cdcl\<^sub>W = this(2) and IH = this(3)[OF this(4-)] and
    confl[simp] = this(5) and inv = this(4)
  from cdcl\<^sub>W
  show ?case
    proof (cases)
      case propagate
      moreover then have "conflicting U = C_True"
        by auto
      moreover have "conflicting V = C_True"
        using propagate by auto
      ultimately show ?thesis using IH cdcl\<^sub>W_merge_restart.fw_r_propagate[of U V] by auto
    next
      case conflict
      moreover then have "conflicting U = C_True"
        by auto
      moreover have "conflicting V \<noteq> C_True"
        using conflict by auto
      ultimately show ?thesis using IH by auto
    next
      case other
      then show ?thesis
        proof cases
          case decide
          moreover then have "conflicting U = C_True"
            by auto
          ultimately show ?thesis using IH cdcl\<^sub>W_merge_restart.fw_r_decide[of U V] by auto
        next
          case bj
          moreover {
            assume "skip_or_resolve U V"
            have f1: "cdcl\<^sub>W_bj\<^sup>+\<^sup>+ U V"
              by (simp add: local.bj tranclp.r_into_trancl)
            obtain T T' :: 'st where
              f2: "cdcl\<^sub>W_merge_restart\<^sup>*\<^sup>* S U
                \<or> cdcl\<^sub>W_merge_restart\<^sup>*\<^sup>* S T \<and> conflicting U \<noteq> C_True
                  \<and> conflict T T' \<and> cdcl\<^sub>W_bj\<^sup>*\<^sup>* T' U"
              using IH confl by blast
            then have ?thesis
              proof -
                have "conflicting V \<noteq> C_True \<and> conflicting U \<noteq> C_True"
                  using \<open>skip_or_resolve U V\<close> by auto
                then show ?thesis
                  by (metis (no_types) IH f1 rtranclp_trans tranclp_into_rtranclp)
              qed
          }
          moreover {
            assume "backtrack U V"
            then have "conflicting U \<noteq> C_True" by auto
            then obtain T T' where
              "cdcl\<^sub>W_merge_restart\<^sup>*\<^sup>* S T" and
              "conflicting U \<noteq> C_True" and
              "conflict T T'" and
              "cdcl\<^sub>W_bj\<^sup>*\<^sup>* T' U"
              using IH confl by blast
            have invU: "cdcl\<^sub>W_M_level_inv U"
              using inv rtranclp_cdcl\<^sub>W_consistent_inv step.hyps(1) by blast
            then have "conflicting V = C_True"
              using \<open>backtrack U V\<close> inv by (auto elim: backtrack_levE
                simp: cdcl\<^sub>W_M_level_inv_decomp)
            have "full cdcl\<^sub>W_bj T' V"
              apply (rule rtranclp_fullI[of cdcl\<^sub>W_bj T' U V])
                using \<open>cdcl\<^sub>W_bj\<^sup>*\<^sup>* T' U\<close> apply fast
              using \<open>backtrack U V\<close> backtrack_is_full1_cdcl\<^sub>W_bj invU unfolding full1_def full_def
              by blast
            then have ?thesis
              using cdcl\<^sub>W_merge_restart.fw_r_conflict[of T T' V] \<open>conflict T T'\<close>
              \<open>cdcl\<^sub>W_merge_restart\<^sup>*\<^sup>* S T\<close> \<open>conflicting V = C_True\<close> by auto
          }
          ultimately show ?thesis by (auto simp: cdcl\<^sub>W_bj.simps)
      qed
    next
      case rf
      moreover then have "conflicting U = C_True" and "conflicting V = C_True"
        by (auto simp: cdcl\<^sub>W_rf.simps)
      ultimately show ?thesis using IH cdcl\<^sub>W_merge_restart.fw_r_rf[of U V] by auto
    qed
qed

lemma no_step_cdcl\<^sub>W_no_step_cdcl\<^sub>W_merge_restart: "no_step cdcl\<^sub>W S \<Longrightarrow> no_step cdcl\<^sub>W_merge_restart S"
  by (auto simp: cdcl\<^sub>W.simps cdcl\<^sub>W_merge_restart.simps cdcl\<^sub>W_o.simps cdcl\<^sub>W_bj.simps)

lemma no_step_cdcl\<^sub>W_merge_restart_no_step_cdcl\<^sub>W:
  assumes
    "conflicting S = C_True" and
    "cdcl\<^sub>W_M_level_inv S" and
    "no_step cdcl\<^sub>W_merge_restart S"
  shows "no_step cdcl\<^sub>W S"
proof -
  { fix S'
    assume "conflict S S'"
    then have "cdcl\<^sub>W S S'" using cdcl\<^sub>W.conflict by auto
    then have "cdcl\<^sub>W_M_level_inv S'"
      using assms(2) cdcl\<^sub>W_consistent_inv by blast
    then obtain S'' where "full cdcl\<^sub>W_bj S' S''"
      using cdcl\<^sub>W_bj_exists_normal_form[of S'] by auto
    then have False
      using \<open>conflict S S'\<close> assms(3) fw_r_conflict by blast
  }
  then show ?thesis
    using assms unfolding cdcl\<^sub>W.simps cdcl\<^sub>W_merge_restart.simps cdcl\<^sub>W_o.simps cdcl\<^sub>W_bj.simps
    by fastforce
qed

lemma rtranclp_cdcl\<^sub>W_merge_restart_no_step_cdcl\<^sub>W_bj:
  assumes
    "cdcl\<^sub>W_merge_restart\<^sup>*\<^sup>* S T" and
    "conflicting S = C_True"
  shows "no_step cdcl\<^sub>W_bj T"
  using assms
  by (induction rule: rtranclp_induct)
     (fastforce simp: cdcl\<^sub>W_bj.simps cdcl\<^sub>W_rf.simps cdcl\<^sub>W_merge_restart.simps full_def)+

text \<open>If @{term "conflicting  S \<noteq> C_True"}, we cannot say anything.

  Remark that this theorem does  not say anything about well-foundedness: even if you know that one
  relation is well-founded, it only states that the normal forms are shared.
  \<close>
lemma conflicting_true_full_cdcl\<^sub>W_iff_full_cdcl\<^sub>W_merge:
  assumes confl: "conflicting  S = C_True" and lev: "cdcl\<^sub>W_M_level_inv S"
  shows "full cdcl\<^sub>W S V \<longleftrightarrow> full cdcl\<^sub>W_merge_restart S V"
proof
  assume full: "full cdcl\<^sub>W_merge_restart S V"
  then have st: "cdcl\<^sub>W\<^sup>*\<^sup>* S V"
    using rtranclp_mono[of cdcl\<^sub>W_merge_restart "cdcl\<^sub>W\<^sup>*\<^sup>*"] cdcl\<^sub>W_merge_restart_cdcl\<^sub>W
    unfolding full_def by auto

  have n_s: "no_step cdcl\<^sub>W_merge_restart V"
    using full unfolding full_def by auto
  have n_s_bj: "no_step cdcl\<^sub>W_bj V"
    using rtranclp_cdcl\<^sub>W_merge_restart_no_step_cdcl\<^sub>W_bj confl full unfolding full_def by auto
  have "\<And>S'. conflict V S' \<Longrightarrow> cdcl\<^sub>W_M_level_inv S'"
    using cdcl\<^sub>W.conflict cdcl\<^sub>W_consistent_inv lev rtranclp_cdcl\<^sub>W_consistent_inv st by blast
  then have "\<And>S'. conflict V S' \<Longrightarrow> False"
    using n_s n_s_bj cdcl\<^sub>W_bj_exists_normal_form cdcl\<^sub>W_merge_restart.simps by meson
  then have n_s_cdcl\<^sub>W: "no_step cdcl\<^sub>W V"
    using n_s n_s_bj by (auto simp: cdcl\<^sub>W.simps cdcl\<^sub>W_o.simps cdcl\<^sub>W_merge_restart.simps)
  then show "full cdcl\<^sub>W S V" using st unfolding full_def by auto
next
  assume full: "full cdcl\<^sub>W S V"
  have "no_step cdcl\<^sub>W_merge_restart V"
    using full no_step_cdcl\<^sub>W_no_step_cdcl\<^sub>W_merge_restart unfolding full_def by blast
  moreover
    consider
        (fw) "cdcl\<^sub>W_merge_restart\<^sup>*\<^sup>* S V" and "conflicting V = C_True"
      | (bj) T U where
        "cdcl\<^sub>W_merge_restart\<^sup>*\<^sup>* S T" and
        "conflicting V \<noteq> C_True" and
        "conflict T U" and
        "cdcl\<^sub>W_bj\<^sup>*\<^sup>* U V"
      using full rtrancl_cdcl\<^sub>W_conflicting_true_cdcl\<^sub>W_merge_restart confl lev unfolding full_def
      by meson
    then have "cdcl\<^sub>W_merge_restart\<^sup>*\<^sup>* S V"
      proof cases
        case fw
        then show ?thesis by fast
      next
        case (bj T U)
        have "no_step cdcl\<^sub>W_bj V"
          by (meson cdcl\<^sub>W_o.bj full full_def other)
        then have "full cdcl\<^sub>W_bj U V"
          using \<open> cdcl\<^sub>W_bj\<^sup>*\<^sup>* U V\<close> unfolding full_def by auto
        then have "cdcl\<^sub>W_merge_restart T V"
          using \<open>conflict T U\<close> cdcl\<^sub>W_merge_restart.fw_r_conflict by blast
        then show ?thesis using \<open>cdcl\<^sub>W_merge_restart\<^sup>*\<^sup>* S T\<close> by auto
      qed
  ultimately show "full cdcl\<^sub>W_merge_restart S V" unfolding full_def by fast
qed

lemma init_state_true_full_cdcl\<^sub>W_iff_full_cdcl\<^sub>W_merge:
  shows "full cdcl\<^sub>W (init_state N) V \<longleftrightarrow> full cdcl\<^sub>W_merge_restart (init_state N) V"
  by (rule conflicting_true_full_cdcl\<^sub>W_iff_full_cdcl\<^sub>W_merge) auto

subsection \<open>FW with strategy\<close>
subsubsection \<open>The intermediate step\<close>
inductive cdcl\<^sub>W_s' :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
conflict': "full1 cdcl\<^sub>W_cp S S' \<Longrightarrow> cdcl\<^sub>W_s' S S'" |
decide': "decide S S' \<Longrightarrow> no_step cdcl\<^sub>W_cp S \<Longrightarrow> full cdcl\<^sub>W_cp S' S'' \<Longrightarrow> cdcl\<^sub>W_s' S S''" |
bj': "full1 cdcl\<^sub>W_bj S S' \<Longrightarrow> no_step cdcl\<^sub>W_cp S \<Longrightarrow> full cdcl\<^sub>W_cp S' S'' \<Longrightarrow> cdcl\<^sub>W_s' S S''"

inductive_cases cdcl\<^sub>W_s'E: "cdcl\<^sub>W_s' S T"

lemma rtranclp_cdcl\<^sub>W_bj_full1_cdclp_cdcl\<^sub>W_stgy:
  "cdcl\<^sub>W_bj\<^sup>*\<^sup>* S S' \<Longrightarrow> full cdcl\<^sub>W_cp S' S'' \<Longrightarrow> cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S S''"
proof (induction rule: converse_rtranclp_induct)
  case base
  then show ?case by (metis cdcl\<^sub>W_stgy.conflict' full_unfold rtranclp.simps)
next
  case (step T U) note st =this(2) and bj = this(1) and IH = this(3)[OF this(4)]
  have "no_step cdcl\<^sub>W_cp T"
    using bj by (auto simp add: cdcl\<^sub>W_bj.simps)
  consider
      (U) "U = S'"
    | (U') U' where "cdcl\<^sub>W_bj U U'" and "cdcl\<^sub>W_bj\<^sup>*\<^sup>* U' S'"
    using st by (metis converse_rtranclpE)
  then show ?case
    proof cases
      case U
      then show ?thesis
        using \<open>no_step cdcl\<^sub>W_cp T\<close> cdcl\<^sub>W_o.bj local.bj other' step.prems by (meson r_into_rtranclp)
    next
      case U' note U' = this(1)
      have "no_step cdcl\<^sub>W_cp U"
        using U' by (fastforce simp: cdcl\<^sub>W_cp.simps cdcl\<^sub>W_bj.simps)
      then have "full cdcl\<^sub>W_cp U U"
        by (simp add: full_unfold)
      then have "cdcl\<^sub>W_stgy T U"
        using \<open>no_step cdcl\<^sub>W_cp T\<close> cdcl\<^sub>W_stgy.simps local.bj cdcl\<^sub>W_o.bj by meson
      then show ?thesis using IH by auto
    qed
qed

lemma cdcl\<^sub>W_s'_is_rtranclp_cdcl\<^sub>W_stgy:
  "cdcl\<^sub>W_s' S T \<Longrightarrow> cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S T"
  apply (induction rule: cdcl\<^sub>W_s'.induct)
    apply (auto intro: cdcl\<^sub>W_stgy.intros)[]
   apply (meson decide other' r_into_rtranclp)
  by (metis full1_def rtranclp_cdcl\<^sub>W_bj_full1_cdclp_cdcl\<^sub>W_stgy tranclp_into_rtranclp)

lemma cdcl\<^sub>W_cp_cdcl\<^sub>W_bj_bissimulation:
  assumes
    "full cdcl\<^sub>W_cp T U" and
    "cdcl\<^sub>W_bj\<^sup>*\<^sup>* T T'" and
    "cdcl\<^sub>W_all_struct_inv T" and
    "no_step cdcl\<^sub>W_bj T'"
  shows "full cdcl\<^sub>W_cp T' U
    \<or> (\<exists>U' U''. full cdcl\<^sub>W_cp T' U'' \<and> full1 cdcl\<^sub>W_bj U U' \<and> full cdcl\<^sub>W_cp U' U'' \<and> cdcl\<^sub>W_s'\<^sup>*\<^sup>* U U'')"
  using assms(2,1,3,4)
proof (induction rule: rtranclp_induct)
  case base
  then show ?case by blast
next
  case (step T' T'') note st = this(1) and bj = this(2) and IH = this(3)[OF this(4,5)] and
    full = this(4) and inv = this(5)
  have "cdcl\<^sub>W\<^sup>*\<^sup>* T T''"
    by (metis (no_types, lifting) cdcl\<^sub>W_o.bj local.bj mono_rtranclp[of cdcl\<^sub>W_bj cdcl\<^sub>W T T''] other
      st rtranclp.rtrancl_into_rtrancl)
  then have inv_T'': "cdcl\<^sub>W_all_struct_inv T''"
    using inv rtranclp_cdcl\<^sub>W_all_struct_inv_inv by blast
  have "cdcl\<^sub>W_bj\<^sup>+\<^sup>+ T T''"
    using local.bj st by auto
  have "full1 cdcl\<^sub>W_bj T T''"
    by (metis \<open>cdcl\<^sub>W_bj\<^sup>+\<^sup>+ T T''\<close> full1_def step.prems(3))
  then have "T = U"
    proof -
      obtain Z where "cdcl\<^sub>W_bj T Z"
          by (meson tranclpD \<open>cdcl\<^sub>W_bj\<^sup>+\<^sup>+ T T''\<close>)
      { assume "cdcl\<^sub>W_cp\<^sup>+\<^sup>+ T U"
        then obtain Z' where "cdcl\<^sub>W_cp T Z'"
          by (meson tranclpD)
        then have False
          using \<open>cdcl\<^sub>W_bj T Z\<close> by (fastforce simp: cdcl\<^sub>W_bj.simps cdcl\<^sub>W_cp.simps)
      }
      then show ?thesis
        using full unfolding full_def rtranclp_unfold by blast
    qed
  obtain U'' where "full cdcl\<^sub>W_cp T'' U''"
    using cdcl\<^sub>W_cp_normalized_element_all_inv inv_T'' by blast
  moreover then have "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* U U''"
    by (metis \<open>T = U\<close> \<open>cdcl\<^sub>W_bj\<^sup>+\<^sup>+ T T''\<close> rtranclp_cdcl\<^sub>W_bj_full1_cdclp_cdcl\<^sub>W_stgy rtranclp_unfold)
  moreover have "cdcl\<^sub>W_s'\<^sup>*\<^sup>* U U''"
    proof -
      obtain ss :: "'st \<Rightarrow> 'st" where
        f1: "\<forall>x2. (\<exists>v3. cdcl\<^sub>W_cp x2 v3) = cdcl\<^sub>W_cp x2 (ss x2)"
        by moura
      have "\<not> cdcl\<^sub>W_cp U (ss U)"
        by (meson full full_def)
      then show ?thesis
        using f1 by (metis (no_types) \<open>T = U\<close> \<open>full1 cdcl\<^sub>W_bj T T''\<close> bj' calculation(1)
          r_into_rtranclp)
    qed
  ultimately show ?case
    using \<open>full1 cdcl\<^sub>W_bj T T''\<close> \<open>full cdcl\<^sub>W_cp T'' U''\<close> unfolding \<open>T = U\<close> by blast
qed

lemma cdcl\<^sub>W_cp_cdcl\<^sub>W_bj_bissimulation':
  assumes
    "full cdcl\<^sub>W_cp T U" and
    "cdcl\<^sub>W_bj\<^sup>*\<^sup>* T T'" and
    "cdcl\<^sub>W_all_struct_inv T" and
    "no_step cdcl\<^sub>W_bj T'"
  shows "full cdcl\<^sub>W_cp T' U
    \<or> (\<exists>U'. full1 cdcl\<^sub>W_bj U U' \<and> (\<forall>U''. full cdcl\<^sub>W_cp U' U'' \<longrightarrow> full cdcl\<^sub>W_cp T' U''
      \<and> cdcl\<^sub>W_s'\<^sup>*\<^sup>* U U''))"
  using assms(2,1,3,4)
proof (induction rule: rtranclp_induct)
  case base
  then show ?case by blast
next
  case (step T' T'') note st = this(1) and bj = this(2) and IH = this(3)[OF this(4,5)] and
    full = this(4) and inv = this(5)
  have "cdcl\<^sub>W\<^sup>*\<^sup>* T T''"
    by (metis (no_types, lifting) cdcl\<^sub>W_o.bj local.bj mono_rtranclp[of cdcl\<^sub>W_bj cdcl\<^sub>W T T''] other st
      rtranclp.rtrancl_into_rtrancl)
  then have inv_T'': "cdcl\<^sub>W_all_struct_inv T''"
    using inv rtranclp_cdcl\<^sub>W_all_struct_inv_inv by blast
  have "cdcl\<^sub>W_bj\<^sup>+\<^sup>+ T T''"
    using local.bj st by auto
  have "full1 cdcl\<^sub>W_bj T T''"
    by (metis \<open>cdcl\<^sub>W_bj\<^sup>+\<^sup>+ T T''\<close> full1_def step.prems(3))
  then have "T = U"
    proof -
      obtain Z where "cdcl\<^sub>W_bj T Z"
        by (meson tranclpD \<open>cdcl\<^sub>W_bj\<^sup>+\<^sup>+ T T''\<close>)
      { assume "cdcl\<^sub>W_cp\<^sup>+\<^sup>+ T U"
        then obtain Z' where "cdcl\<^sub>W_cp T Z'"
          by (meson tranclpD)
        then have False
          using \<open>cdcl\<^sub>W_bj T Z\<close> by (fastforce simp: cdcl\<^sub>W_bj.simps cdcl\<^sub>W_cp.simps)
      }
      then show ?thesis
        using full unfolding full_def rtranclp_unfold by blast
    qed
  { fix U''
    assume "full cdcl\<^sub>W_cp T'' U''"
    moreover then have "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* U U''"
      by (metis \<open>T = U\<close> \<open>cdcl\<^sub>W_bj\<^sup>+\<^sup>+ T T''\<close> rtranclp_cdcl\<^sub>W_bj_full1_cdclp_cdcl\<^sub>W_stgy rtranclp_unfold)
    moreover have "cdcl\<^sub>W_s'\<^sup>*\<^sup>* U U''"
      proof -
        obtain ss :: "'st \<Rightarrow> 'st" where
          f1: "\<forall>x2. (\<exists>v3. cdcl\<^sub>W_cp x2 v3) = cdcl\<^sub>W_cp x2 (ss x2)"
          by moura
        have "\<not> cdcl\<^sub>W_cp U (ss U)"
          by (meson assms(1) full_def)
        then show ?thesis
          using f1 by (metis (no_types) \<open>T = U\<close> \<open>full1 cdcl\<^sub>W_bj T T''\<close> bj' calculation(1)
            r_into_rtranclp)
      qed
    ultimately have "full1 cdcl\<^sub>W_bj U T''" and " cdcl\<^sub>W_s'\<^sup>*\<^sup>* T'' U''"
      using \<open>full1 cdcl\<^sub>W_bj T T''\<close> \<open>full cdcl\<^sub>W_cp T'' U''\<close> unfolding \<open>T = U\<close>
        apply blast
      by (metis \<open>full cdcl\<^sub>W_cp T'' U''\<close> cdcl\<^sub>W_s'.simps full_unfold rtranclp.simps)
    }
  then show ?case
    using \<open>full1 cdcl\<^sub>W_bj T T''\<close> full bj' unfolding \<open>T = U\<close> full_def by (metis r_into_rtranclp)
qed

lemma cdcl\<^sub>W_stgy_cdcl\<^sub>W_s'_connected:
  assumes "cdcl\<^sub>W_stgy S U" and "cdcl\<^sub>W_all_struct_inv S"
  shows "cdcl\<^sub>W_s' S U
    \<or> (\<exists>U'. full1 cdcl\<^sub>W_bj U U' \<and> (\<forall>U''. full cdcl\<^sub>W_cp U' U'' \<longrightarrow> cdcl\<^sub>W_s' S U'' ))"
  using assms
proof (induction rule: cdcl\<^sub>W_stgy.induct)
  case (conflict' T)
  then have "cdcl\<^sub>W_s' S T"
    using cdcl\<^sub>W_s'.conflict' by blast
  then show ?case
    by blast
next
  case (other' T U) note o = this(1) and n_s = this(2) and full = this(3) and inv = this(4)
  show ?case
    using o
    proof cases
      case decide
      then show ?thesis using cdcl\<^sub>W_s'.simps full n_s by blast
    next
      case bj
      have inv_T: "cdcl\<^sub>W_all_struct_inv T"
        using cdcl\<^sub>W_all_struct_inv_inv o other other'.prems by blast
      consider
          (cp) "full cdcl\<^sub>W_cp T U" and "no_step cdcl\<^sub>W_bj T"
        | (fbj) T' where "full1 cdcl\<^sub>W_bj T T'"
        apply (cases "no_step cdcl\<^sub>W_bj T")
         using full apply blast
        using cdcl\<^sub>W_bj_exists_normal_form[of T] inv_T unfolding cdcl\<^sub>W_all_struct_inv_def
        by (metis full_unfold)
      then show ?thesis
        proof cases
          case cp
          then show ?thesis
            proof -
              obtain ss :: "'st \<Rightarrow> 'st" where
                f1: "\<forall>s sa sb. (\<not> full1 cdcl\<^sub>W_bj s sa \<or> cdcl\<^sub>W_cp s (ss s) \<or> \<not> full cdcl\<^sub>W_cp sa sb)
                  \<or> cdcl\<^sub>W_s' s sb"
                using bj' by moura
              have "full1 cdcl\<^sub>W_bj S T"
                by (simp add: cp(2) full1_def local.bj tranclp.r_into_trancl)
              then show ?thesis
                using f1 full n_s by blast
            qed
        next
          case (fbj U')
          then have "full1 cdcl\<^sub>W_bj S U'"
            using bj unfolding full1_def by auto
          moreover have "no_step cdcl\<^sub>W_cp S"
            using n_s by blast
          moreover have "T = U"
            using full fbj unfolding full1_def full_def rtranclp_unfold
            by (force dest!: tranclpD simp:cdcl\<^sub>W_bj.simps)
          ultimately show ?thesis using cdcl\<^sub>W_s'.bj'[of S U'] using fbj by blast
        qed
    qed
qed

lemma cdcl\<^sub>W_stgy_cdcl\<^sub>W_s'_connected':
  assumes "cdcl\<^sub>W_stgy S U" and "cdcl\<^sub>W_all_struct_inv S"
  shows "cdcl\<^sub>W_s' S U
    \<or> (\<exists>U' U''. cdcl\<^sub>W_s' S U'' \<and> full1 cdcl\<^sub>W_bj U U' \<and> full cdcl\<^sub>W_cp U' U'')"
  using assms
proof (induction rule: cdcl\<^sub>W_stgy.induct)
  case (conflict' T)
  then have "cdcl\<^sub>W_s' S T"
    using cdcl\<^sub>W_s'.conflict' by blast
  then show ?case
    by blast
next
  case (other' T U) note o = this(1) and n_s = this(2) and full = this(3) and inv = this(4)
  show ?case
    using o
    proof cases
      case decide
      then show ?thesis using cdcl\<^sub>W_s'.simps full n_s by blast
    next
      case bj
      have "cdcl\<^sub>W_all_struct_inv T"
        using cdcl\<^sub>W_all_struct_inv_inv o other other'.prems by blast
      then obtain T' where T': "full cdcl\<^sub>W_bj T T'"
        using cdcl\<^sub>W_bj_exists_normal_form unfolding full_def cdcl\<^sub>W_all_struct_inv_def by metis
      then have "full cdcl\<^sub>W_bj S T'"
        proof -
          have f1: "cdcl\<^sub>W_bj\<^sup>*\<^sup>* T T' \<and> no_step cdcl\<^sub>W_bj T'"
            by (metis (no_types) T' full_def)
          then have "cdcl\<^sub>W_bj\<^sup>*\<^sup>* S T'"
            by (meson converse_rtranclp_into_rtranclp local.bj)
          then show ?thesis
            using f1 by (simp add: full_def)
        qed
      have "cdcl\<^sub>W_bj\<^sup>*\<^sup>* T T'"
        using T' unfolding full_def by simp
      have "cdcl\<^sub>W_all_struct_inv T"
        using cdcl\<^sub>W_all_struct_inv_inv o other other'.prems by blast
      then consider
          (T'U) "full cdcl\<^sub>W_cp T' U"
        | (U) U' U'' where
            "full cdcl\<^sub>W_cp T' U''" and
            "full1 cdcl\<^sub>W_bj U U'" and
            "full cdcl\<^sub>W_cp U' U''" and
            "cdcl\<^sub>W_s'\<^sup>*\<^sup>* U U''"
        using cdcl\<^sub>W_cp_cdcl\<^sub>W_bj_bissimulation[OF full \<open>cdcl\<^sub>W_bj\<^sup>*\<^sup>* T T'\<close>] T' unfolding full_def
        by blast
      then show ?thesis by (metis T' cdcl\<^sub>W_s'.simps full_fullI local.bj n_s)
    qed
qed

lemma cdcl\<^sub>W_stgy_cdcl\<^sub>W_s'_no_step:
  assumes "cdcl\<^sub>W_stgy S U" and "cdcl\<^sub>W_all_struct_inv S" and "no_step cdcl\<^sub>W_bj U"
  shows "cdcl\<^sub>W_s' S U"
  using cdcl\<^sub>W_stgy_cdcl\<^sub>W_s'_connected[OF assms(1,2)] assms(3)
  by (metis (no_types, lifting) full1_def tranclpD)

lemma rtranclp_cdcl\<^sub>W_stgy_connected_to_rtranclp_cdcl\<^sub>W_s':
  assumes "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S U" and inv: "cdcl\<^sub>W_M_level_inv S"
  shows "cdcl\<^sub>W_s'\<^sup>*\<^sup>* S U \<or> (\<exists>T. cdcl\<^sub>W_s'\<^sup>*\<^sup>* S T \<and> cdcl\<^sub>W_bj\<^sup>+\<^sup>+ T U \<and> conflicting U \<noteq> C_True)"
  using assms(1)
proof induction
  case base
  then show ?case by simp
next
  case (step T V) note st = this(1) and o = this(2) and IH = this(3)
  from o show ?case
    proof cases
      case conflict'
      then have f2: "cdcl\<^sub>W_s' T V"
        using cdcl\<^sub>W_s'.conflict' by blast
      obtain ss :: 'st where
        f3: "S = T \<or> cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S ss \<and> cdcl\<^sub>W_stgy ss T"
        by (metis (full_types) rtranclp.simps st)
      obtain ssa :: 'st where
        "cdcl\<^sub>W_cp T ssa"
        using conflict' by (metis (no_types) full1_def tranclpD)
      then have "S = T"
        using f3 by (metis (no_types) cdcl\<^sub>W_stgy.simps full_def full1_def)
      then show ?thesis
        using f2 by blast
    next
      case (other' U) note o = this(1) and n_s = this(2) and full = this(3)
      then show ?thesis
        using o
        proof (cases rule: cdcl\<^sub>W_o_rule_cases)
          case decide
          then have "cdcl\<^sub>W_s'\<^sup>*\<^sup>* S T"
            using IH by auto
          then show ?thesis
            by (meson decide decide' full n_s rtranclp.rtrancl_into_rtrancl)
        next
          case backtrack
          consider
              (s') "cdcl\<^sub>W_s'\<^sup>*\<^sup>* S T"
            | (bj) S' where "cdcl\<^sub>W_s'\<^sup>*\<^sup>* S S'" and "cdcl\<^sub>W_bj\<^sup>+\<^sup>+ S' T" and "conflicting T \<noteq> C_True"
            using IH by blast
          then show ?thesis
            proof cases
              case s'
              moreover
                have "cdcl\<^sub>W_M_level_inv T"
                  using inv local.step(1) rtranclp_cdcl\<^sub>W_stgy_consistent_inv by auto
                then have "full1 cdcl\<^sub>W_bj T U"
                  using backtrack_is_full1_cdcl\<^sub>W_bj backtrack by blast
                then have "cdcl\<^sub>W_s' T V"
                 using full bj' n_s by blast
              ultimately show ?thesis by auto
            next
              case (bj S') note S_S' = this(1) and bj_T = this(2)
              have "no_step cdcl\<^sub>W_cp S'"
                using bj_T by (fastforce simp: cdcl\<^sub>W_cp.simps cdcl\<^sub>W_bj.simps dest!: tranclpD)
              moreover
                have " cdcl\<^sub>W_M_level_inv T"
                  using inv local.step(1) rtranclp_cdcl\<^sub>W_stgy_consistent_inv by auto
                then have "full1 cdcl\<^sub>W_bj T U"
                  using backtrack_is_full1_cdcl\<^sub>W_bj backtrack by blast
                then have "full1 cdcl\<^sub>W_bj S' U"
                  using bj_T unfolding full1_def by fastforce
              ultimately have "cdcl\<^sub>W_s' S' V" using full by (simp add: bj')
              then show ?thesis using S_S' by auto
            qed
        next
          case skip
          then have [simp]: "U = V"
            using full converse_rtranclpE unfolding full_def by fastforce

          consider
              (s') "cdcl\<^sub>W_s'\<^sup>*\<^sup>* S T"
            | (bj) S' where "cdcl\<^sub>W_s'\<^sup>*\<^sup>* S S'" and "cdcl\<^sub>W_bj\<^sup>+\<^sup>+ S' T" and "conflicting T \<noteq> C_True"
            using IH by blast
          then show ?thesis
            proof cases
              case s'
              have "cdcl\<^sub>W_bj\<^sup>+\<^sup>+ T V"
                using skip by force
              moreover have "conflicting V \<noteq> C_True"
                using skip by auto
              ultimately show ?thesis using s' by auto
            next
              case (bj S') note S_S' = this(1) and bj_T = this(2)
              have "cdcl\<^sub>W_bj\<^sup>+\<^sup>+ S' V"
                using skip bj_T by (metis \<open>U = V\<close> cdcl\<^sub>W_bj.skip tranclp.simps)

              moreover have "conflicting V \<noteq> C_True"
                using skip by auto
              ultimately show ?thesis using S_S' by auto
            qed
        next
          case resolve
          then have [simp]: "U = V"
            using full converse_rtranclpE unfolding full_def by fastforce
          consider
              (s') "cdcl\<^sub>W_s'\<^sup>*\<^sup>* S T"
            | (bj) S' where "cdcl\<^sub>W_s'\<^sup>*\<^sup>* S S'" and "cdcl\<^sub>W_bj\<^sup>+\<^sup>+ S' T" and "conflicting T \<noteq> C_True"
            using IH by blast
          then show ?thesis
            proof cases
              case s'
              have "cdcl\<^sub>W_bj\<^sup>+\<^sup>+ T V"
                using resolve by force
              moreover have "conflicting V \<noteq> C_True"
                using resolve by auto
              ultimately show ?thesis using s' by auto
            next
              case (bj S') note S_S' = this(1) and bj_T = this(2)
              have "cdcl\<^sub>W_bj\<^sup>+\<^sup>+ S' V"
                using resolve  bj_T by (metis \<open>U = V\<close> cdcl\<^sub>W_bj.resolve tranclp.simps)
              moreover have "conflicting V \<noteq> C_True"
                using resolve by auto
              ultimately show ?thesis using S_S' by auto
            qed
        qed
    qed
qed

lemma n_step_cdcl\<^sub>W_stgy_iff_no_step_cdcl\<^sub>W_cl_cdcl\<^sub>W_o:
  assumes inv: "cdcl\<^sub>W_all_struct_inv S"
  shows "no_step cdcl\<^sub>W_s' S \<longleftrightarrow> no_step cdcl\<^sub>W_cp S \<and> no_step cdcl\<^sub>W_o S" (is "?S' S \<longleftrightarrow> ?C S \<and> ?O S")
proof
  assume "?C S \<and> ?O S"
  then show "?S' S"
    by (auto simp: cdcl\<^sub>W_s'.simps full1_def tranclp_unfold_begin)
next
  assume n_s: "?S' S"
  have "?C S"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then obtain S' where "cdcl\<^sub>W_cp S S'"
        by auto
      then obtain T where "full1 cdcl\<^sub>W_cp S T"
        using cdcl\<^sub>W_cp_normalized_element_all_inv inv by (metis (no_types, lifting) full_unfold)
      then show False using n_s cdcl\<^sub>W_s'.conflict' by blast
    qed
  moreover have "?O S"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then obtain S' where "cdcl\<^sub>W_o S S'"
        by auto
      then obtain T where "full1 cdcl\<^sub>W_cp S' T"
        using cdcl\<^sub>W_cp_normalized_element_all_inv inv
        by (meson cdcl\<^sub>W_all_struct_inv_def n_s
          cdcl\<^sub>W_stgy_cdcl\<^sub>W_s'_connected' cdcl\<^sub>W_then_exists_cdcl\<^sub>W_stgy_step )
      then show False using n_s by (meson \<open>cdcl\<^sub>W_o S S'\<close> cdcl\<^sub>W_all_struct_inv_def
        cdcl\<^sub>W_stgy_cdcl\<^sub>W_s'_connected' cdcl\<^sub>W_then_exists_cdcl\<^sub>W_stgy_step inv)
    qed
  ultimately show "?C S \<and> ?O S" by auto
qed

lemma cdcl\<^sub>W_s'_tranclp_cdcl\<^sub>W:
   "cdcl\<^sub>W_s' S S' \<Longrightarrow> cdcl\<^sub>W\<^sup>+\<^sup>+ S S'"
proof (induct rule: cdcl\<^sub>W_s'.induct)
  case conflict'
  then show ?case
    by (simp add: full1_def tranclp_cdcl\<^sub>W_cp_tranclp_cdcl\<^sub>W)
next
  case decide'
  then show ?case
    using cdcl\<^sub>W_stgy.simps cdcl\<^sub>W_stgy_tranclp_cdcl\<^sub>W by (meson cdcl\<^sub>W_o.simps)
next
  case (bj' Sa S'a S'') note a2 = this(1) and a1 = this(2) and n_s = this(3)
  obtain ss :: "'st \<Rightarrow> 'st \<Rightarrow> ('st \<Rightarrow> 'st \<Rightarrow> bool) \<Rightarrow> 'st" where
    "\<forall>x0 x1 x2. (\<exists>v3. x2 x1 v3 \<and> x2\<^sup>*\<^sup>* v3 x0) = (x2 x1 (ss x0 x1 x2) \<and> x2\<^sup>*\<^sup>* (ss x0 x1 x2) x0)"
    by moura
  then have f3: "\<forall>p s sa. \<not> p\<^sup>+\<^sup>+ s sa \<or> p s (ss sa s p) \<and> p\<^sup>*\<^sup>* (ss sa s p) sa"
    by (metis (full_types) tranclpD)
  have "cdcl\<^sub>W_bj\<^sup>+\<^sup>+ Sa S'a \<and> no_step cdcl\<^sub>W_bj S'a"
    using a2 by (simp add: full1_def)
  then have "cdcl\<^sub>W_bj Sa (ss S'a Sa cdcl\<^sub>W_bj) \<and> cdcl\<^sub>W_bj\<^sup>*\<^sup>* (ss S'a Sa cdcl\<^sub>W_bj) S'a"
    using f3 by auto
  then show "cdcl\<^sub>W\<^sup>+\<^sup>+ Sa S''"
    using a1 n_s by (meson bj other rtranclp_cdcl\<^sub>W_bj_full1_cdclp_cdcl\<^sub>W_stgy
      rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W rtranclp_into_tranclp2)
qed

lemma tranclp_cdcl\<^sub>W_s'_tranclp_cdcl\<^sub>W:
  "cdcl\<^sub>W_s'\<^sup>+\<^sup>+ S S' \<Longrightarrow> cdcl\<^sub>W\<^sup>+\<^sup>+ S S'"
  apply (induct rule: tranclp.induct)
   using cdcl\<^sub>W_s'_tranclp_cdcl\<^sub>W apply blast
  by (meson cdcl\<^sub>W_s'_tranclp_cdcl\<^sub>W tranclp_trans)

lemma rtranclp_cdcl\<^sub>W_s'_rtranclp_cdcl\<^sub>W:
   "cdcl\<^sub>W_s'\<^sup>*\<^sup>* S S' \<Longrightarrow> cdcl\<^sub>W\<^sup>*\<^sup>* S S'"
  using rtranclp_unfold[of cdcl\<^sub>W_s' S S'] tranclp_cdcl\<^sub>W_s'_tranclp_cdcl\<^sub>W[of S S'] by auto

lemma full_cdcl\<^sub>W_stgy_iff_full_cdcl\<^sub>W_s':
  assumes inv: "cdcl\<^sub>W_all_struct_inv S"
  shows "full cdcl\<^sub>W_stgy S T \<longleftrightarrow> full cdcl\<^sub>W_s' S T" (is "?S \<longleftrightarrow> ?S'")
proof
  assume ?S'
  then have "cdcl\<^sub>W\<^sup>*\<^sup>* S T"
    using rtranclp_cdcl\<^sub>W_s'_rtranclp_cdcl\<^sub>W[of S T] unfolding full_def by blast
  then have inv': "cdcl\<^sub>W_all_struct_inv T"
    using rtranclp_cdcl\<^sub>W_all_struct_inv_inv inv by blast
  have "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S T"
    using \<open>?S'\<close> unfolding full_def
      using cdcl\<^sub>W_s'_is_rtranclp_cdcl\<^sub>W_stgy rtranclp_mono[of cdcl\<^sub>W_s' "cdcl\<^sub>W_stgy\<^sup>*\<^sup>*"] by auto
  then show ?S
    using \<open>?S'\<close> inv' cdcl\<^sub>W_stgy_cdcl\<^sub>W_s'_connected' unfolding full_def by blast
next
  assume ?S
  then have inv_T:"cdcl\<^sub>W_all_struct_inv T"
    by (metis assms full_def rtranclp_cdcl\<^sub>W_all_struct_inv_inv rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W)

  consider
      (s')  "cdcl\<^sub>W_s'\<^sup>*\<^sup>* S T"
    | (st) S' where "cdcl\<^sub>W_s'\<^sup>*\<^sup>* S S'" and "cdcl\<^sub>W_bj\<^sup>+\<^sup>+ S' T" and "conflicting T \<noteq> C_True"
    using rtranclp_cdcl\<^sub>W_stgy_connected_to_rtranclp_cdcl\<^sub>W_s'[of S T] inv \<open>?S\<close>
    unfolding full_def  cdcl\<^sub>W_all_struct_inv_def
    by blast
  then show ?S'
    proof cases
      case s'
      then show ?thesis
        by (metis \<open>full cdcl\<^sub>W_stgy S T\<close> inv_T cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_s'.simps
          cdcl\<^sub>W_stgy.conflict'  cdcl\<^sub>W_then_exists_cdcl\<^sub>W_stgy_step full_def
          n_step_cdcl\<^sub>W_stgy_iff_no_step_cdcl\<^sub>W_cl_cdcl\<^sub>W_o)
    next
      case (st S')
      have "full cdcl\<^sub>W_cp T T"
        using conflicting_clause_full_cdcl\<^sub>W_cp st(3) by blast
      moreover
        have n_s: "no_step cdcl\<^sub>W_bj T"
          by (metis \<open>full cdcl\<^sub>W_stgy S T\<close> bj inv_T cdcl\<^sub>W_all_struct_inv_def
            cdcl\<^sub>W_then_exists_cdcl\<^sub>W_stgy_step full_def)
        then have "full1 cdcl\<^sub>W_bj S' T"
          using st(2) unfolding full1_def by blast
      moreover have "no_step cdcl\<^sub>W_cp S'"
        using st(2) by (fastforce dest!: tranclpD simp: cdcl\<^sub>W_cp.simps cdcl\<^sub>W_bj.simps)
      ultimately have "cdcl\<^sub>W_s' S' T"
        using cdcl\<^sub>W_s'.bj'[of S' T T] by blast
      then have "cdcl\<^sub>W_s'\<^sup>*\<^sup>* S T"
        using st(1) by auto
      moreover have "no_step cdcl\<^sub>W_s' T"
        using inv_T by (metis \<open>full cdcl\<^sub>W_cp T T\<close> \<open>full cdcl\<^sub>W_stgy S T\<close> cdcl\<^sub>W_all_struct_inv_def
          cdcl\<^sub>W_then_exists_cdcl\<^sub>W_stgy_step full_def n_step_cdcl\<^sub>W_stgy_iff_no_step_cdcl\<^sub>W_cl_cdcl\<^sub>W_o)
      ultimately show ?thesis
        unfolding full_def by blast
    qed
qed

lemma conflict_step_cdcl\<^sub>W_stgy_step:
  assumes
    "conflict S T"
    "cdcl\<^sub>W_all_struct_inv S"
  shows "\<exists>T. cdcl\<^sub>W_stgy S T"
proof -
  obtain U where "full cdcl\<^sub>W_cp S U"
    using cdcl\<^sub>W_cp_normalized_element_all_inv assms by blast
  then have "full1 cdcl\<^sub>W_cp S U"
    by (metis cdcl\<^sub>W_cp.conflict' assms(1) full_unfold)
  then show ?thesis using cdcl\<^sub>W_stgy.conflict' by blast
qed

lemma decide_step_cdcl\<^sub>W_stgy_step:
  assumes
    "decide S T"
    "cdcl\<^sub>W_all_struct_inv S"
  shows "\<exists>T. cdcl\<^sub>W_stgy S T"
proof -
  obtain U where "full cdcl\<^sub>W_cp T U"
    using cdcl\<^sub>W_cp_normalized_element_all_inv by (meson assms(1) assms(2) cdcl\<^sub>W_all_struct_inv_inv
      cdcl\<^sub>W_cp_normalized_element_all_inv decide other)
  then show ?thesis
    by (metis assms cdcl\<^sub>W_cp_normalized_element_all_inv cdcl\<^sub>W_stgy.conflict' decide full_unfold
      other')
qed

lemma rtranclp_cdcl\<^sub>W_cp_conflicting_C_Clause:
  "cdcl\<^sub>W_cp\<^sup>*\<^sup>* S T \<Longrightarrow> conflicting S = C_Clause D \<Longrightarrow> S = T"
  using rtranclpD tranclpD by fastforce

inductive cdcl\<^sub>W_merge_cp :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
conflict'[intro]: "conflict S T \<Longrightarrow> full cdcl\<^sub>W_bj T U \<Longrightarrow> cdcl\<^sub>W_merge_cp S U" |
propagate'[intro]: "propagate\<^sup>+\<^sup>+ S S' \<Longrightarrow> cdcl\<^sub>W_merge_cp S S'"

lemma cdcl\<^sub>W_merge_restart_cases[consumes 1, case_names conflict propagate]:
  assumes
    "cdcl\<^sub>W_merge_cp S U" and
    "\<And>T. conflict S T \<Longrightarrow> full cdcl\<^sub>W_bj T U \<Longrightarrow> P" and
    "propagate\<^sup>+\<^sup>+ S U \<Longrightarrow> P"
  shows "P"
  using assms unfolding cdcl\<^sub>W_merge_cp.simps by auto

lemma cdcl\<^sub>W_merge_cp_tranclp_cdcl\<^sub>W_merge:
  "cdcl\<^sub>W_merge_cp S T \<Longrightarrow> cdcl\<^sub>W_merge\<^sup>+\<^sup>+ S T"
  apply (induction rule: cdcl\<^sub>W_merge_cp.induct)
    using cdcl\<^sub>W_merge.simps apply auto[1]
  using tranclp_mono[of propagate cdcl\<^sub>W_merge] fw_propagate by blast

lemma rtranclp_cdcl\<^sub>W_merge_cp_rtranclp_cdcl\<^sub>W:
  "cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl\<^sub>W\<^sup>*\<^sup>* S T"
 apply (induction rule: rtranclp_induct)
  apply simp
 unfolding cdcl\<^sub>W_merge_cp.simps by (meson cdcl\<^sub>W_merge_restart_cdcl\<^sub>W fw_r_conflict
   rtranclp_propagate_is_rtranclp_cdcl\<^sub>W rtranclp_trans tranclp_into_rtranclp)

lemma full1_cdcl\<^sub>W_bj_no_step_cdcl\<^sub>W_bj:
  "full1 cdcl\<^sub>W_bj S T \<Longrightarrow> no_step cdcl\<^sub>W_cp S"
  by (metis rtranclp_unfold cdcl\<^sub>W_cp_conflicting_not_empty conflicting_clause.exhaust full1_def
    rtranclp_cdcl\<^sub>W_merge_restart_no_step_cdcl\<^sub>W_bj tranclpD)

inductive cdcl\<^sub>W_s'_without_decide where
conflict'_without_decide[intro]: "full1 cdcl\<^sub>W_cp S S' \<Longrightarrow> cdcl\<^sub>W_s'_without_decide S S'" |
bj'_without_decide[intro]: "full1 cdcl\<^sub>W_bj S S' \<Longrightarrow> no_step cdcl\<^sub>W_cp S \<Longrightarrow> full cdcl\<^sub>W_cp S' S''
      \<Longrightarrow> cdcl\<^sub>W_s'_without_decide S S''"

lemma rtranclp_cdcl\<^sub>W_s'_without_decide_rtranclp_cdcl\<^sub>W:
  "cdcl\<^sub>W_s'_without_decide\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl\<^sub>W\<^sup>*\<^sup>* S T"
  apply (induction rule: rtranclp_induct)
    apply simp
  by (meson cdcl\<^sub>W_s'.simps cdcl\<^sub>W_s'_tranclp_cdcl\<^sub>W cdcl\<^sub>W_s'_without_decide.simps
    rtranclp_tranclp_tranclp tranclp_into_rtranclp)

lemma rtranclp_cdcl\<^sub>W_s'_without_decide_rtranclp_cdcl\<^sub>W_s':
  "cdcl\<^sub>W_s'_without_decide\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl\<^sub>W_s'\<^sup>*\<^sup>* S T"
proof (induction rule: rtranclp_induct)
  case base
  then show ?case by simp
next
  case (step y z) note a2 = this(2) and a1 = this(3)
  have "cdcl\<^sub>W_s' y z"
    using a2 by (metis (no_types) bj' cdcl\<^sub>W_s'.conflict' cdcl\<^sub>W_s'_without_decide.cases)
  then show "cdcl\<^sub>W_s'\<^sup>*\<^sup>* S z"
    using a1 by (meson r_into_rtranclp rtranclp_trans)
qed

lemma rtranclp_cdcl\<^sub>W_merge_cp_is_rtranclp_cdcl\<^sub>W_s'_without_decide:
  assumes
    "cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* S V"
    "conflicting S = C_True"
  shows
    "(cdcl\<^sub>W_s'_without_decide\<^sup>*\<^sup>* S V)
    \<or> (\<exists>T. cdcl\<^sub>W_s'_without_decide\<^sup>*\<^sup>* S T \<and> propagate\<^sup>+\<^sup>+ T V)
    \<or> (\<exists>T U. cdcl\<^sub>W_s'_without_decide\<^sup>*\<^sup>* S T \<and> full1 cdcl\<^sub>W_bj T U \<and> propagate\<^sup>*\<^sup>* U V)"
  using assms
proof (induction rule: rtranclp_induct)
  case base
  then show ?case by simp
next
  case (step U V) note st = this(1) and cp = this(2) and IH = this(3)[OF this(4)]
  from cp show ?case
    proof (cases rule: cdcl\<^sub>W_merge_restart_cases)
      case propagate
      then show ?thesis using IH by (meson rtranclp_tranclp_tranclp tranclp_into_rtranclp)
    next
      case (conflict U') note confl = this(1) and bj = this(2)
      have full1_U_U': "full1 cdcl\<^sub>W_cp U U'"
        by (simp add: conflict_is_full1_cdcl\<^sub>W_cp local.conflict(1))
      consider
          (s') "cdcl\<^sub>W_s'_without_decide\<^sup>*\<^sup>* S U"
        | (propa) T' where "cdcl\<^sub>W_s'_without_decide\<^sup>*\<^sup>* S T'" and "propagate\<^sup>+\<^sup>+ T' U"
        | (bj_prop) T' T'' where
            "cdcl\<^sub>W_s'_without_decide\<^sup>*\<^sup>* S T' " and
            "full1 cdcl\<^sub>W_bj T' T''" and
            "propagate\<^sup>*\<^sup>* T'' U"
        using IH by blast
      then show ?thesis
        proof cases
          case s'
          have "cdcl\<^sub>W_s'_without_decide U U'"
           using full1_U_U' conflict'_without_decide by blast
          then have "cdcl\<^sub>W_s'_without_decide\<^sup>*\<^sup>* S U'"
            using  \<open>cdcl\<^sub>W_s'_without_decide\<^sup>*\<^sup>* S U\<close> by auto
          moreover have "U' = V \<or> full1 cdcl\<^sub>W_bj U' V"
            using bj by (meson full_unfold)
          ultimately show ?thesis by blast
        next
          case propa note s' = this(1) and T'_U = this(2)
          have "full1 cdcl\<^sub>W_cp T' U'"
            using rtranclp_mono[of propagate cdcl\<^sub>W_cp] T'_U cdcl\<^sub>W_cp.propagate' full1_U_U'
            rtranclp_full1I[of cdcl\<^sub>W_cp T'] by (metis (full_types) predicate2D predicate2I
              tranclp_into_rtranclp)
          have "cdcl\<^sub>W_s'_without_decide\<^sup>*\<^sup>* S U'"
            using \<open>full1 cdcl\<^sub>W_cp T' U'\<close> conflict'_without_decide s' by force
          have "full1 cdcl\<^sub>W_bj U' V \<or> V = U'"
            by (metis (lifting) full_unfold local.bj)
          then show ?thesis
            using \<open>cdcl\<^sub>W_s'_without_decide\<^sup>*\<^sup>* S U'\<close> by blast
        next
          case bj_prop note s' = this(1) and bj_T' = this(2) and T''_U = this(3)
          have "no_step cdcl\<^sub>W_cp T'"
            using bj_T' full1_cdcl\<^sub>W_bj_no_step_cdcl\<^sub>W_bj by blast
          moreover have "full1 cdcl\<^sub>W_cp T'' U'"
            using rtranclp_mono[of propagate cdcl\<^sub>W_cp] T''_U cdcl\<^sub>W_cp.propagate' full1_U_U'
            rtranclp_full1I[of cdcl\<^sub>W_cp T''] by blast
          ultimately have "cdcl\<^sub>W_s'_without_decide T' U'"
            using bj'_without_decide[of T' T'' U'] bj_T' by (simp add: full_unfold)
          then have "cdcl\<^sub>W_s'_without_decide\<^sup>*\<^sup>* S U'"
            using s' rtranclp.intros(2)[of _ S T' U'] by blast
          then show ?thesis
            by (metis full_unfold local.bj rtranclp.rtrancl_refl)
        qed
    qed
qed


lemma rtranclp_cdcl\<^sub>W_s'_without_decide_is_rtranclp_cdcl\<^sub>W_merge_cp:
  assumes
    "cdcl\<^sub>W_s'_without_decide\<^sup>*\<^sup>* S V" and
    confl: "conflicting S = C_True"
  shows
    "(cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* S V \<and> conflicting V = C_True)
    \<or> (cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* S V \<and> conflicting V \<noteq> C_True \<and> no_step cdcl\<^sub>W_cp V \<and> no_step cdcl\<^sub>W_bj V)
    \<or> (\<exists>T. cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* S T \<and> conflict T V)"
  using assms(1)
proof (induction)
  case base
  then show ?case using confl by auto
next
  case (step U V) note st = this(1) and s = this(2) and IH = this(3)
  from s show ?case
    proof (cases rule: cdcl\<^sub>W_s'_without_decide.cases)
      case conflict'_without_decide
      then have rt: "cdcl\<^sub>W_cp\<^sup>+\<^sup>+ U V"  unfolding full1_def by fast
      then have "conflicting U = C_True"
        using tranclp_cdcl\<^sub>W_cp_propagate_with_conflict_or_not[of U V]
        conflict by (auto dest!: tranclpD simp: rtranclp_unfold)
      then have "cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* S U" using IH by auto
      consider
          (propa) "propagate\<^sup>+\<^sup>+ U V"
         | (confl') "conflict U V"
         | (propa_confl') U' where "propagate\<^sup>+\<^sup>+ U U'" "conflict U' V"
        using tranclp_cdcl\<^sub>W_cp_propagate_with_conflict_or_not[OF rt] unfolding rtranclp_unfold
        by fastforce
      then show ?thesis
        proof cases
          case propa
          then have "cdcl\<^sub>W_merge_cp U V"
            by auto
          moreover have "conflicting V = C_True"
            using propa unfolding tranclp_unfold_end by auto
          ultimately show ?thesis using \<open>cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* S U\<close> by force
        next
          case confl'
          then show ?thesis using \<open>cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* S U\<close> by auto
        next
          case propa_confl' note propa = this(1) and confl' = this(2)
          then have "cdcl\<^sub>W_merge_cp U U'" by auto
          then have "cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* S U'" using \<open>cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* S U\<close> by auto
          then show ?thesis using \<open>cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* S U\<close> confl' by auto
        qed
    next
      case (bj'_without_decide U') note full_bj = this(1) and cp = this(3)
      then have "conflicting U \<noteq> C_True"
        using full_bj unfolding full1_def by (fastforce dest!: tranclpD simp: cdcl\<^sub>W_bj.simps)
      with IH obtain T where
        S_T: "cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* S T" and T_U: "conflict T U"
        using full_bj unfolding full1_def by (blast dest: tranclpD)
      then have "cdcl\<^sub>W_merge_cp T U'"
        using cdcl\<^sub>W_merge_cp.conflict'[of T U U'] full_bj by (simp add: full_unfold)
      then have S_U': "cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* S U'" using S_T by auto
      consider
          (n_s) "U' = V"
         | (propa) "propagate\<^sup>+\<^sup>+ U' V"
         | (confl') "conflict U' V"
         | (propa_confl') U'' where "propagate\<^sup>+\<^sup>+ U' U''" "conflict U'' V"
        using tranclp_cdcl\<^sub>W_cp_propagate_with_conflict_or_not cp
        unfolding rtranclp_unfold full_def by metis
      then show ?thesis
        proof cases
          case propa
          then have "cdcl\<^sub>W_merge_cp U' V" by auto
          moreover have "conflicting V = C_True"
            using propa  unfolding tranclp_unfold_end by auto
          ultimately show ?thesis using S_U' by force
        next
          case confl'
          then show ?thesis using S_U' by auto
        next
          case propa_confl' note propa = this(1) and confl = this(2)
          have "cdcl\<^sub>W_merge_cp U' U''" using propa by auto
          then show ?thesis using S_U' confl by (meson rtranclp.rtrancl_into_rtrancl)
        next
          case n_s
          then show ?thesis
            using S_U' apply (cases "conflicting V = C_True")
             using full_bj apply simp
            by (metis cp full_def full_unfold full_bj)
        qed
    qed
qed

lemma no_step_cdcl\<^sub>W_s'_no_ste_cdcl\<^sub>W_merge_cp:
  assumes
    "cdcl\<^sub>W_all_struct_inv S"
    "conflicting S = C_True"
    "no_step cdcl\<^sub>W_s' S"
  shows "no_step cdcl\<^sub>W_merge_cp S"
  using assms apply (auto simp: cdcl\<^sub>W_s'.simps cdcl\<^sub>W_merge_cp.simps)
    using conflict_is_full1_cdcl\<^sub>W_cp apply blast
  using cdcl\<^sub>W_cp_normalized_element_all_inv cdcl\<^sub>W_cp.propagate' by (metis cdcl\<^sub>W_cp.propagate'
    full_unfold tranclpD)

text \<open>The @{term "no_step decide S"} is needed, since @{term "cdcl\<^sub>W_merge_cp"} is
  @{term "cdcl\<^sub>W_s'"} without @{term decide}.\<close>
lemma conflicting_true_no_step_cdcl\<^sub>W_merge_cp_no_step_s'_without_decide:
  assumes
    confl: "conflicting S = C_True" and
    inv: "cdcl\<^sub>W_M_level_inv S" and
    n_s: "no_step cdcl\<^sub>W_merge_cp S"
  shows "no_step cdcl\<^sub>W_s'_without_decide S"
proof (rule ccontr)
  assume "\<not> no_step cdcl\<^sub>W_s'_without_decide S"
  then obtain T where
    cdcl\<^sub>W: "cdcl\<^sub>W_s'_without_decide S T"
    by auto
  then have inv_T: "cdcl\<^sub>W_M_level_inv T"
    using rtranclp_cdcl\<^sub>W_s'_without_decide_rtranclp_cdcl\<^sub>W[of S T]
    rtranclp_cdcl\<^sub>W_consistent_inv inv by blast
  from cdcl\<^sub>W show False
    proof cases
      case conflict'_without_decide
      have "no_step propagate S"
        using n_s by blast
      then have "conflict S T"
        using local.conflict' tranclp_cdcl\<^sub>W_cp_propagate_with_conflict_or_not[of S T]
        unfolding full1_def by (metis full1_def local.conflict'_without_decide rtranclp_unfold
          tranclp_unfold_begin)
      moreover
        then obtain T' where "full cdcl\<^sub>W_bj T T'"
          using cdcl\<^sub>W_bj_exists_normal_form inv_T by blast
      ultimately show False using cdcl\<^sub>W_merge_cp.conflict' n_s by meson
    next
      case (bj'_without_decide S')
      then show ?thesis
        using confl unfolding full1_def by (fastforce simp: cdcl\<^sub>W_bj.simps dest: tranclpD)
    qed
qed

lemma conflicting_true_no_step_s'_without_decide_no_step_cdcl\<^sub>W_merge_cp:
  assumes
    inv: "cdcl\<^sub>W_all_struct_inv S" and
    n_s: "no_step cdcl\<^sub>W_s'_without_decide S"
  shows "no_step cdcl\<^sub>W_merge_cp S"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then obtain T where "cdcl\<^sub>W_merge_cp S T"
    by auto
  then show False
    proof cases
      case (conflict' S')
      then show False using n_s conflict'_without_decide conflict_is_full1_cdcl\<^sub>W_cp by blast
    next
      case propagate'
      moreover
        have "cdcl\<^sub>W_all_struct_inv T"
          using inv by (meson local.propagate' rtranclp_cdcl\<^sub>W_all_struct_inv_inv
            rtranclp_propagate_is_rtranclp_cdcl\<^sub>W tranclp_into_rtranclp)
        then obtain U where "full cdcl\<^sub>W_cp T U"
          using cdcl\<^sub>W_cp_normalized_element_all_inv by auto
      ultimately have "full1 cdcl\<^sub>W_cp S U"
        using tranclp_full_full1I[of cdcl\<^sub>W_cp S T U] cdcl\<^sub>W_cp.propagate'
        tranclp_mono[of propagate cdcl\<^sub>W_cp] by blast
      then show False using conflict'_without_decide n_s by blast
    qed
qed

lemma no_step_cdcl\<^sub>W_merge_cp_no_step_cdcl\<^sub>W_cp:
  "no_step cdcl\<^sub>W_merge_cp S \<Longrightarrow> cdcl\<^sub>W_M_level_inv S \<Longrightarrow> no_step cdcl\<^sub>W_cp S"
  using cdcl\<^sub>W_bj_exists_normal_form cdcl\<^sub>W_consistent_inv[OF cdcl\<^sub>W.conflict, of S]
  by (metis cdcl\<^sub>W_cp.cases cdcl\<^sub>W_merge_cp.simps tranclp.intros(1))

lemma conflicting_not_true_rtranclp_cdcl\<^sub>W_merge_cp_no_step_cdcl\<^sub>W_bj:
  assumes
    "conflicting S = C_True" and
    "cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* S T"
  shows "no_step cdcl\<^sub>W_bj T"
  using assms(2,1) by (induction)
  (fastforce simp: cdcl\<^sub>W_merge_cp.simps full_def tranclp_unfold_end cdcl\<^sub>W_bj.simps)+

lemma conflicting_true_full_cdcl\<^sub>W_merge_cp_iff_full_cdcl\<^sub>W_s'_without_decode:
  assumes
    confl: "conflicting S = C_True" and
    inv: "cdcl\<^sub>W_all_struct_inv S"
  shows
    "full cdcl\<^sub>W_merge_cp S V \<longleftrightarrow> full cdcl\<^sub>W_s'_without_decide S V" (is "?fw \<longleftrightarrow> ?s'")
proof
  assume ?fw
  then have st: "cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* S V" and n_s: "no_step cdcl\<^sub>W_merge_cp V"
    unfolding full_def by blast+
  have inv_V: "cdcl\<^sub>W_all_struct_inv V"
    using rtranclp_cdcl\<^sub>W_merge_cp_rtranclp_cdcl\<^sub>W[of S V] \<open>?fw\<close> unfolding full_def
    by (simp add: inv rtranclp_cdcl\<^sub>W_all_struct_inv_inv)
  consider
      (s') "cdcl\<^sub>W_s'_without_decide\<^sup>*\<^sup>* S V"
    | (propa) T where "cdcl\<^sub>W_s'_without_decide\<^sup>*\<^sup>* S T" and "propagate\<^sup>+\<^sup>+ T V"
    | (bj) T U where "cdcl\<^sub>W_s'_without_decide\<^sup>*\<^sup>* S T" and "full1 cdcl\<^sub>W_bj T U" and "propagate\<^sup>*\<^sup>* U V"
    using rtranclp_cdcl\<^sub>W_merge_cp_is_rtranclp_cdcl\<^sub>W_s'_without_decide confl st n_s by metis
  then have "cdcl\<^sub>W_s'_without_decide\<^sup>*\<^sup>* S V"
    proof cases
      case s'
      then show ?thesis .
    next
      case propa note s' = this(1) and propa = this(2)
      have "no_step cdcl\<^sub>W_cp V"
        using no_step_cdcl\<^sub>W_merge_cp_no_step_cdcl\<^sub>W_cp n_s inv_V
        unfolding cdcl\<^sub>W_all_struct_inv_def by blast
      then have "full1 cdcl\<^sub>W_cp T V"
        using propa tranclp_mono[of propagate cdcl\<^sub>W_cp] "cdcl\<^sub>W_cp.propagate'" unfolding full1_def
        by blast
      then have "cdcl\<^sub>W_s'_without_decide T V"
        using conflict'_without_decide by blast
      then show ?thesis using s' by auto
    next
      case bj note s' = this(1) and bj = this(2) and propa = this(3)
      have "no_step cdcl\<^sub>W_cp V"
        using no_step_cdcl\<^sub>W_merge_cp_no_step_cdcl\<^sub>W_cp n_s inv_V
        unfolding cdcl\<^sub>W_all_struct_inv_def by blast
      then have "full cdcl\<^sub>W_cp U V"
        using propa rtranclp_mono[of propagate cdcl\<^sub>W_cp] cdcl\<^sub>W_cp.propagate' unfolding full_def
        by blast
      moreover have "no_step cdcl\<^sub>W_cp T"
        using bj unfolding full1_def by (fastforce dest!: tranclpD simp:cdcl\<^sub>W_bj.simps)
      ultimately have "cdcl\<^sub>W_s'_without_decide T V"
        using bj'_without_decide[of T U V] bj by blast
      then show ?thesis using s' by auto
    qed
  moreover have "no_step cdcl\<^sub>W_s'_without_decide V"
    proof (cases "conflicting V = C_True")
      case False
      { fix ss :: 'st
        have ff1: "\<forall>s sa. \<not> cdcl\<^sub>W_s' s sa \<or> full1 cdcl\<^sub>W_cp s sa
          \<or> (\<exists>sb. decide s sb \<and> no_step cdcl\<^sub>W_cp s \<and> full cdcl\<^sub>W_cp sb sa)
          \<or> (\<exists>sb. full1 cdcl\<^sub>W_bj s sb \<and> no_step cdcl\<^sub>W_cp s \<and> full cdcl\<^sub>W_cp sb sa)"
          by (metis cdcl\<^sub>W_s'.cases)
        have ff2: "(\<forall>p s sa. \<not> full1 p (s::'st) sa \<or> p\<^sup>+\<^sup>+ s sa \<and> no_step p sa)
          \<and> (\<forall>p s sa. (\<not> p\<^sup>+\<^sup>+ (s::'st) sa \<or> (\<exists>s. p sa s)) \<or> full1 p s sa)"
          by (meson full1_def)
        obtain ssa :: "('st \<Rightarrow> 'st \<Rightarrow> bool) \<Rightarrow> 'st \<Rightarrow> 'st \<Rightarrow> 'st" where
          ff3: "\<forall>p s sa. \<not> p\<^sup>+\<^sup>+ s sa \<or> p s (ssa p s sa) \<and> p\<^sup>*\<^sup>* (ssa p s sa) sa"
          by (metis (no_types) tranclpD)
        then have a3: "\<not> cdcl\<^sub>W_cp\<^sup>+\<^sup>+ V ss"
          using False by (metis conflicting_clause_full_cdcl\<^sub>W_cp full_def)
        have "\<And>s. \<not> cdcl\<^sub>W_bj\<^sup>+\<^sup>+ V s"
          using ff3 False by (metis confl st
            conflicting_not_true_rtranclp_cdcl\<^sub>W_merge_cp_no_step_cdcl\<^sub>W_bj)
        then have "\<not> cdcl\<^sub>W_s'_without_decide V ss"
          using ff1 a3 ff2 by (metis cdcl\<^sub>W_s'_without_decide.cases)
      }
      then show ?thesis
        by fastforce
      next
        case True
        then show ?thesis
          using conflicting_true_no_step_cdcl\<^sub>W_merge_cp_no_step_s'_without_decide n_s inv_V
          unfolding cdcl\<^sub>W_all_struct_inv_def by blast
    qed
  ultimately show ?s' unfolding full_def by blast
next
  assume s': ?s'
  then have st: "cdcl\<^sub>W_s'_without_decide\<^sup>*\<^sup>* S V" and n_s: "no_step cdcl\<^sub>W_s'_without_decide V"
    unfolding full_def by auto
  then have "cdcl\<^sub>W\<^sup>*\<^sup>* S V"
    using rtranclp_cdcl\<^sub>W_s'_without_decide_rtranclp_cdcl\<^sub>W st by blast
  then have inv_V: "cdcl\<^sub>W_all_struct_inv V" using inv rtranclp_cdcl\<^sub>W_all_struct_inv_inv by blast
  then have n_s_cp_V: "no_step cdcl\<^sub>W_cp V"
    using cdcl\<^sub>W_cp_normalized_element_all_inv[of V] full_fullI[of cdcl\<^sub>W_cp V] n_s
    conflict'_without_decide conflicting_true_no_step_s'_without_decide_no_step_cdcl\<^sub>W_merge_cp
    no_step_cdcl\<^sub>W_merge_cp_no_step_cdcl\<^sub>W_cp
    unfolding cdcl\<^sub>W_all_struct_inv_def by presburger
  have n_s_bj: "no_step cdcl\<^sub>W_bj V"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then obtain W where W: "cdcl\<^sub>W_bj V W" by blast
      have "cdcl\<^sub>W_all_struct_inv W"
        using W cdcl\<^sub>W.simps cdcl\<^sub>W_all_struct_inv_inv inv_V by blast
      then obtain W' where "full1 cdcl\<^sub>W_bj V W'"
        using cdcl\<^sub>W_bj_exists_normal_form[of W] full_fullI[of cdcl\<^sub>W_bj V W]  W
        unfolding cdcl\<^sub>W_all_struct_inv_def
        by blast
      moreover
        then have "cdcl\<^sub>W\<^sup>+\<^sup>+ V W'"
          using tranclp_mono[of cdcl\<^sub>W_bj cdcl\<^sub>W] cdcl\<^sub>W.other cdcl\<^sub>W_o.bj unfolding full1_def by blast
        then have "cdcl\<^sub>W_all_struct_inv W'"
          by (meson inv_V rtranclp_cdcl\<^sub>W_all_struct_inv_inv tranclp_into_rtranclp)
        then obtain X where "full cdcl\<^sub>W_cp W' X"
          using cdcl\<^sub>W_cp_normalized_element_all_inv by blast
      ultimately show False
        using bj'_without_decide n_s_cp_V n_s by blast
    qed
  from s' consider
      (cp_true) "cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* S V" and "conflicting V = C_True"
    | (cp_false) "cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* S V" and "conflicting V \<noteq> C_True" and "no_step cdcl\<^sub>W_cp V" and
         "no_step cdcl\<^sub>W_bj V"
    | (cp_confl) T where "cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* S T" "conflict T V"
    using rtranclp_cdcl\<^sub>W_s'_without_decide_is_rtranclp_cdcl\<^sub>W_merge_cp[of S V] confl
    unfolding full_def by blast
  then have "cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* S V"
    proof cases
      case cp_confl note S_T = this(1) and conf_V = this(2)
      have "full cdcl\<^sub>W_bj V V"
        using conf_V n_s_bj unfolding full_def by fast
      then have "cdcl\<^sub>W_merge_cp T V"
        using cdcl\<^sub>W_merge_cp.conflict' conf_V by auto
      then show ?thesis using S_T by auto
    qed fast+
  moreover
    then have "cdcl\<^sub>W\<^sup>*\<^sup>* S V" using rtranclp_cdcl\<^sub>W_merge_cp_rtranclp_cdcl\<^sub>W by blast
    then have "cdcl\<^sub>W_all_struct_inv V"
      using inv rtranclp_cdcl\<^sub>W_all_struct_inv_inv by blast
    then have "no_step cdcl\<^sub>W_merge_cp V"
      using conflicting_true_no_step_s'_without_decide_no_step_cdcl\<^sub>W_merge_cp s'
      unfolding full_def by blast
  ultimately show ?fw unfolding full_def by auto
qed

lemma conflicting_true_full1_cdcl\<^sub>W_merge_cp_iff_full1_cdcl\<^sub>W_s'_without_decode:
  assumes
    confl: "conflicting S = C_True" and
    inv: "cdcl\<^sub>W_all_struct_inv S"
  shows
    "full1 cdcl\<^sub>W_merge_cp S V \<longleftrightarrow> full1 cdcl\<^sub>W_s'_without_decide S V"
proof -
  have "full cdcl\<^sub>W_merge_cp S V = full cdcl\<^sub>W_s'_without_decide S V"
    using confl conflicting_true_full_cdcl\<^sub>W_merge_cp_iff_full_cdcl\<^sub>W_s'_without_decode inv
    by blast
  then show ?thesis unfolding full_unfold full1_def
    by (metis (mono_tags) tranclp_unfold_begin)
qed

lemma conflicting_true_full1_cdcl\<^sub>W_merge_cp_imp_full1_cdcl\<^sub>W_s'_without_decode:
  assumes
    fw: "full1 cdcl\<^sub>W_merge_cp S V" and
    inv: "cdcl\<^sub>W_all_struct_inv S"
  shows
    "full1 cdcl\<^sub>W_s'_without_decide S V"
proof -
  have "conflicting S = C_True"
    using fw unfolding full1_def by (auto dest!: tranclpD simp: cdcl\<^sub>W_merge_cp.simps)
  then show ?thesis
    using conflicting_true_full1_cdcl\<^sub>W_merge_cp_iff_full1_cdcl\<^sub>W_s'_without_decode fw inv by blast
qed

inductive cdcl\<^sub>W_merge_stgy where
fw_s_cp[intro]: "full1 cdcl\<^sub>W_merge_cp S T \<Longrightarrow> cdcl\<^sub>W_merge_stgy S T" |
fw_s_decide[intro]: "decide S T \<Longrightarrow> no_step cdcl\<^sub>W_merge_cp S \<Longrightarrow> full cdcl\<^sub>W_merge_cp T U
  \<Longrightarrow>  cdcl\<^sub>W_merge_stgy S U"

lemma cdcl\<^sub>W_merge_stgy_tranclp_cdcl\<^sub>W_merge:
  assumes fw: "cdcl\<^sub>W_merge_stgy S T"
  shows "cdcl\<^sub>W_merge\<^sup>+\<^sup>+ S T"
proof -
  { fix S T
    assume "full1 cdcl\<^sub>W_merge_cp S T"
    then have "cdcl\<^sub>W_merge\<^sup>+\<^sup>+ S T"
      using tranclp_mono[of cdcl\<^sub>W_merge_cp "cdcl\<^sub>W_merge\<^sup>+\<^sup>+"] cdcl\<^sub>W_merge_cp_tranclp_cdcl\<^sub>W_merge
      unfolding full1_def
      by auto
  } note full1_cdcl\<^sub>W_merge_cp_cdcl\<^sub>W_merge = this
  show ?thesis
    using fw
    apply (induction rule: cdcl\<^sub>W_merge_stgy.induct)
      using full1_cdcl\<^sub>W_merge_cp_cdcl\<^sub>W_merge apply simp
    unfolding full_unfold by (auto dest!: full1_cdcl\<^sub>W_merge_cp_cdcl\<^sub>W_merge fw_decide)
qed

lemma rtranclp_cdcl\<^sub>W_merge_stgy_rtranclp_cdcl\<^sub>W_merge:
  assumes fw: "cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* S T"
  shows "cdcl\<^sub>W_merge\<^sup>*\<^sup>* S T"
  using fw cdcl\<^sub>W_merge_stgy_tranclp_cdcl\<^sub>W_merge rtranclp_mono[of cdcl\<^sub>W_merge_stgy "cdcl\<^sub>W_merge\<^sup>+\<^sup>+"]
  unfolding tranclp_rtranclp_rtranclp by blast

lemma cdcl\<^sub>W_merge_stgy_rtranclp_cdcl\<^sub>W:
  "cdcl\<^sub>W_merge_stgy S T \<Longrightarrow> cdcl\<^sub>W\<^sup>*\<^sup>* S T"
  apply (induction rule: cdcl\<^sub>W_merge_stgy.induct)
    using rtranclp_cdcl\<^sub>W_merge_cp_rtranclp_cdcl\<^sub>W unfolding full1_def
    apply (simp add: tranclp_into_rtranclp)
  using rtranclp_cdcl\<^sub>W_merge_cp_rtranclp_cdcl\<^sub>W cdcl\<^sub>W_o.decide cdcl\<^sub>W.other unfolding full_def
  by (meson r_into_rtranclp rtranclp_trans)

lemma rtranclp_cdcl\<^sub>W_merge_stgy_rtranclp_cdcl\<^sub>W:
  "cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl\<^sub>W\<^sup>*\<^sup>* S T"
  using rtranclp_mono[of cdcl\<^sub>W_merge_stgy "cdcl\<^sub>W\<^sup>*\<^sup>*"] cdcl\<^sub>W_merge_stgy_rtranclp_cdcl\<^sub>W by auto

inductive cdcl\<^sub>W_s'_w :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
conflict': "full1 cdcl\<^sub>W_s'_without_decide S S' \<Longrightarrow> cdcl\<^sub>W_s'_w S S'" |
decide': "decide S S' \<Longrightarrow> no_step cdcl\<^sub>W_s'_without_decide S \<Longrightarrow> full cdcl\<^sub>W_s'_without_decide S' S''
  \<Longrightarrow> cdcl\<^sub>W_s'_w S S''"

lemma cdcl\<^sub>W_s'_w_rtranclp_cdcl\<^sub>W:
  "cdcl\<^sub>W_s'_w S T \<Longrightarrow> cdcl\<^sub>W\<^sup>*\<^sup>* S T"
  apply (induction rule: cdcl\<^sub>W_s'_w.induct)
    using rtranclp_cdcl\<^sub>W_s'_without_decide_rtranclp_cdcl\<^sub>W unfolding full1_def
    apply (simp add: tranclp_into_rtranclp)
  using rtranclp_cdcl\<^sub>W_s'_without_decide_rtranclp_cdcl\<^sub>W unfolding full_def
  by (meson decide other rtranclp_into_tranclp2 tranclp_into_rtranclp)

lemma rtranclp_cdcl\<^sub>W_s'_w_rtranclp_cdcl\<^sub>W:
  "cdcl\<^sub>W_s'_w\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl\<^sub>W\<^sup>*\<^sup>* S T"
  using rtranclp_mono[of cdcl\<^sub>W_s'_w "cdcl\<^sub>W\<^sup>*\<^sup>*"] cdcl\<^sub>W_s'_w_rtranclp_cdcl\<^sub>W by auto

lemma no_step_cdcl\<^sub>W_cp_no_step_cdcl\<^sub>W_s'_without_decide:
  assumes "no_step cdcl\<^sub>W_cp S" and "conflicting S = C_True" and inv: "cdcl\<^sub>W_M_level_inv S"
  shows "no_step cdcl\<^sub>W_s'_without_decide S"
  by (metis assms cdcl\<^sub>W_cp.conflict' cdcl\<^sub>W_cp.propagate' cdcl\<^sub>W_merge_restart_cases tranclpD
    conflicting_true_no_step_cdcl\<^sub>W_merge_cp_no_step_s'_without_decide)

lemma no_step_cdcl\<^sub>W_cp_no_step_cdcl\<^sub>W_merge_restart:
  assumes "no_step cdcl\<^sub>W_cp S" and "conflicting S = C_True"
  shows "no_step cdcl\<^sub>W_merge_cp S"
  by (metis assms(1) cdcl\<^sub>W_cp.conflict' cdcl\<^sub>W_cp.propagate' cdcl\<^sub>W_merge_restart_cases tranclpD)
lemma after_cdcl\<^sub>W_s'_without_decide_no_step_cdcl\<^sub>W_cp:
  assumes "cdcl\<^sub>W_s'_without_decide S T"
  shows "no_step cdcl\<^sub>W_cp T"
  using assms by (induction rule: cdcl\<^sub>W_s'_without_decide.induct) (auto simp: full1_def full_def)

lemma no_step_cdcl\<^sub>W_s'_without_decide_no_step_cdcl\<^sub>W_cp:
  "cdcl\<^sub>W_all_struct_inv S \<Longrightarrow> no_step cdcl\<^sub>W_s'_without_decide S \<Longrightarrow> no_step cdcl\<^sub>W_cp S"
  by (simp add: conflicting_true_no_step_s'_without_decide_no_step_cdcl\<^sub>W_merge_cp
    no_step_cdcl\<^sub>W_merge_cp_no_step_cdcl\<^sub>W_cp cdcl\<^sub>W_all_struct_inv_def)

lemma after_cdcl\<^sub>W_s'_w_no_step_cdcl\<^sub>W_cp:
  assumes "cdcl\<^sub>W_s'_w S T" and "cdcl\<^sub>W_all_struct_inv S"
  shows "no_step cdcl\<^sub>W_cp T"
  using assms
proof (induction rule: cdcl\<^sub>W_s'_w.induct)
  case conflict'
  then show ?case
    by (auto simp: full1_def tranclp_unfold_end after_cdcl\<^sub>W_s'_without_decide_no_step_cdcl\<^sub>W_cp)
next
  case (decide' S T U)
  moreover
    then have "cdcl\<^sub>W\<^sup>*\<^sup>* S U"
      using rtranclp_cdcl\<^sub>W_s'_without_decide_rtranclp_cdcl\<^sub>W[of T U] cdcl\<^sub>W.other[of S T]
      cdcl\<^sub>W_o.decide unfolding full_def by auto
    then have "cdcl\<^sub>W_all_struct_inv U"
      using decide'.prems rtranclp_cdcl\<^sub>W_all_struct_inv_inv by blast
  ultimately show ?case
    using no_step_cdcl\<^sub>W_s'_without_decide_no_step_cdcl\<^sub>W_cp unfolding full_def by blast
qed

lemma rtranclp_cdcl\<^sub>W_s'_w_no_step_cdcl\<^sub>W_cp_or_eq:
  assumes "cdcl\<^sub>W_s'_w\<^sup>*\<^sup>* S T" and "cdcl\<^sub>W_all_struct_inv S"
  shows "S = T \<or> no_step cdcl\<^sub>W_cp T"
  using assms
proof (induction rule: rtranclp_induct)
  case base
  then show ?case by simp
next
  case (step T U)
  moreover have "cdcl\<^sub>W_all_struct_inv T"
    using rtranclp_cdcl\<^sub>W_s'_w_rtranclp_cdcl\<^sub>W[of S U] assms(2) rtranclp_cdcl\<^sub>W_all_struct_inv_inv
    rtranclp_cdcl\<^sub>W_s'_w_rtranclp_cdcl\<^sub>W step.hyps(1) by blast
  ultimately show ?case using after_cdcl\<^sub>W_s'_w_no_step_cdcl\<^sub>W_cp by fast
qed

lemma rtranclp_cdcl\<^sub>W_merge_stgy'_no_step_cdcl\<^sub>W_cp_or_eq:
  assumes "cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* S T" and inv: "cdcl\<^sub>W_all_struct_inv S"
  shows "S = T \<or> no_step cdcl\<^sub>W_cp T"
  using assms
proof (induction rule: rtranclp_induct)
  case base
  then show ?case by simp
next
  case (step T U)
  moreover have "cdcl\<^sub>W_all_struct_inv T"
    using rtranclp_cdcl\<^sub>W_merge_stgy_rtranclp_cdcl\<^sub>W[of S U] assms(2) rtranclp_cdcl\<^sub>W_all_struct_inv_inv
    rtranclp_cdcl\<^sub>W_s'_w_rtranclp_cdcl\<^sub>W step.hyps(1)
    by (meson rtranclp_cdcl\<^sub>W_merge_stgy_rtranclp_cdcl\<^sub>W)
  ultimately show ?case
    using after_cdcl\<^sub>W_s'_w_no_step_cdcl\<^sub>W_cp inv unfolding cdcl\<^sub>W_all_struct_inv_def
    by (metis cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_merge_stgy.simps full1_def full_def
      no_step_cdcl\<^sub>W_merge_cp_no_step_cdcl\<^sub>W_cp rtranclp_cdcl\<^sub>W_all_struct_inv_inv
      rtranclp_cdcl\<^sub>W_merge_stgy_rtranclp_cdcl\<^sub>W tranclp.intros(1) tranclp_into_rtranclp)
qed

lemma no_step_cdcl\<^sub>W_s'_without_decide_no_step_cdcl\<^sub>W_bj:
  assumes "no_step cdcl\<^sub>W_s'_without_decide S" and inv: "cdcl\<^sub>W_all_struct_inv S"
  shows "no_step cdcl\<^sub>W_bj S"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then obtain T where S_T: "cdcl\<^sub>W_bj S T"
    by auto
  have "cdcl\<^sub>W_all_struct_inv T"
    using S_T cdcl\<^sub>W_all_struct_inv_inv inv other by blast
  then obtain T' where "full1 cdcl\<^sub>W_bj S T'"
    using cdcl\<^sub>W_bj_exists_normal_form[of T] full_fullI S_T  unfolding cdcl\<^sub>W_all_struct_inv_def
    by metis
  moreover
    then have "cdcl\<^sub>W\<^sup>*\<^sup>* S T'"
      using rtranclp_mono[of cdcl\<^sub>W_bj cdcl\<^sub>W] cdcl\<^sub>W.other cdcl\<^sub>W_o.bj tranclp_into_rtranclp[of cdcl\<^sub>W_bj]
      unfolding full1_def by (metis (full_types) predicate2D predicate2I)
    then have "cdcl\<^sub>W_all_struct_inv T'"
      using inv  rtranclp_cdcl\<^sub>W_all_struct_inv_inv by blast
    then obtain U where "full cdcl\<^sub>W_cp T' U"
      using cdcl\<^sub>W_cp_normalized_element_all_inv by blast
  moreover have "no_step cdcl\<^sub>W_cp S"
    using S_T by (auto simp: cdcl\<^sub>W_bj.simps)
  ultimately show False
  using assms cdcl\<^sub>W_s'_without_decide.intros(2)[of S T' U] by fast
qed

lemma cdcl\<^sub>W_s'_w_no_step_cdcl\<^sub>W_bj:
  assumes "cdcl\<^sub>W_s'_w S T" and "cdcl\<^sub>W_all_struct_inv S"
  shows "no_step cdcl\<^sub>W_bj T"
  using assms apply induction
    using rtranclp_cdcl\<^sub>W_s'_without_decide_rtranclp_cdcl\<^sub>W rtranclp_cdcl\<^sub>W_all_struct_inv_inv
    no_step_cdcl\<^sub>W_s'_without_decide_no_step_cdcl\<^sub>W_bj unfolding full1_def
    apply (meson tranclp_into_rtranclp)
  using rtranclp_cdcl\<^sub>W_s'_without_decide_rtranclp_cdcl\<^sub>W rtranclp_cdcl\<^sub>W_all_struct_inv_inv
    no_step_cdcl\<^sub>W_s'_without_decide_no_step_cdcl\<^sub>W_bj unfolding full_def
  by (meson cdcl\<^sub>W_merge_restart_cdcl\<^sub>W fw_r_decide)

lemma rtranclp_cdcl\<^sub>W_s'_w_no_step_cdcl\<^sub>W_bj_or_eq:
  assumes "cdcl\<^sub>W_s'_w\<^sup>*\<^sup>* S T" and "cdcl\<^sub>W_all_struct_inv S"
  shows "S = T \<or> no_step cdcl\<^sub>W_bj T"
  using assms apply induction
    apply simp
  using rtranclp_cdcl\<^sub>W_s'_w_rtranclp_cdcl\<^sub>W rtranclp_cdcl\<^sub>W_all_struct_inv_inv
    cdcl\<^sub>W_s'_w_no_step_cdcl\<^sub>W_bj by meson

lemma rtranclp_cdcl\<^sub>W_s'_no_step_cdcl\<^sub>W_s'_without_decide_decomp_into_cdcl\<^sub>W_merge:
  assumes
    "cdcl\<^sub>W_s'\<^sup>*\<^sup>* R V" and
    "conflicting R = C_True" and
    inv: "cdcl\<^sub>W_all_struct_inv R"
  shows "(cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* R V \<and> conflicting V = C_True)
  \<or> (cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* R V \<and> conflicting V \<noteq> C_True \<and> no_step cdcl\<^sub>W_bj V)
  \<or> (\<exists>S T U. cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* R S \<and> no_step cdcl\<^sub>W_merge_cp S \<and> decide S T
    \<and> cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* T U \<and> conflict U V)
  \<or> (\<exists>S T. cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* R S \<and> no_step cdcl\<^sub>W_merge_cp S \<and> decide S T
    \<and> cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* T V
      \<and> conflicting V = C_True)
  \<or> (cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* R V \<and> conflicting V = C_True)
  \<or> (\<exists>U. cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* R U \<and> conflict U V)"
  using assms(1,2)
proof induction
  case base
  then show ?case by simp
next
  case (step V W) note st = this(1) and s' = this(2) and IH = this(3)[OF this(4)] and
    n_s_R = this(4)
  from s'
  show ?case
    proof cases
      case conflict'
      consider
         (s') "cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* R V"
        | (dec_confl) S T U where "cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* R S" and "no_step cdcl\<^sub>W_merge_cp S" and
            "decide S T" and "cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* T U" and "conflict U V"
        | (dec) S T where "cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* R S" and "no_step cdcl\<^sub>W_merge_cp S" and "decide S T"
            and "cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* T V" and "conflicting V = C_True"
        | (cp) "cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* R V"
        | (cp_confl) U where "cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* R U" and "conflict U V"
        using IH by meson
      then show ?thesis
        proof cases
        next
          case s'
          then have "R = V"
            by (metis full1_def inv local.conflict' tranclp_unfold_begin
              rtranclp_cdcl\<^sub>W_merge_stgy'_no_step_cdcl\<^sub>W_cp_or_eq)
          consider
              (V_W) "V = W"
            | (propa) "propagate\<^sup>+\<^sup>+ V W" and "conflicting W = C_True"
            | (propa_confl) V' where "propagate\<^sup>*\<^sup>* V V'" and "conflict V' W"
            using tranclp_cdcl\<^sub>W_cp_propagate_with_conflict_or_not[of V W] conflict'
            unfolding full_unfold full1_def by blast
          then show ?thesis
            proof cases
              case V_W
              then show ?thesis using \<open>R = V\<close> n_s_R by simp
            next
              case propa
              then show ?thesis using \<open>R = V\<close> by auto
            next
              case propa_confl
              moreover
                then have "cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* V V'"
                  by (metis Nitpick.rtranclp_unfold cdcl\<^sub>W_merge_cp.propagate' r_into_rtranclp)
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
            using tranclp_cdcl\<^sub>W_cp_propagate_with_conflict_or_not[of V W] conflict'
            unfolding full1_def by blast
          then show ?thesis (* too many levels of case distinction *)
            proof cases
              case propa
              then show ?thesis
                by (meson T_V cdcl\<^sub>W_merge_cp.propagate' dec rtranclp.rtrancl_into_rtrancl)
            next
              case propa_confl
              then have "cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* T V'"
                using T_V by (metis rtranclp_unfold cdcl\<^sub>W_merge_cp.propagate' rtranclp.simps)
              then show ?thesis using dec propa_confl(2) by metis
            qed
        next
          case cp
          consider
              (propa) "propagate\<^sup>+\<^sup>+ V W" and "conflicting W = C_True"
            | (propa_confl) V' where "propagate\<^sup>*\<^sup>* V V'" and "conflict V' W"
            using tranclp_cdcl\<^sub>W_cp_propagate_with_conflict_or_not[of V W] conflict'
            unfolding full1_def by blast
          then show ?thesis (* too many levels of case distinction *)
            proof cases
              case propa
              then show ?thesis by (meson cdcl\<^sub>W_merge_cp.propagate' cp rtranclp.rtrancl_into_rtrancl)
            next
              case propa_confl
              then show ?thesis
                using propa_confl(2) by (metis rtranclp_unfold cdcl\<^sub>W_merge_cp.propagate'
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
      consider
         (s') "cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* R V"
        | (dec_confl) S T U where "cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* R S" and "no_step cdcl\<^sub>W_merge_cp S" and
            "decide S T" and "cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* T U" and "conflict U V"
        | (dec) S T where "cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* R S" and "no_step cdcl\<^sub>W_merge_cp S" and "decide S T"
             and "cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* T V" and "conflicting V = C_True"
        | (cp) "cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* R V"
        | (cp_confl) U where "cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* R U" and "conflict U V"
        using IH by meson
      then show ?thesis
        proof cases
          case s'
          have confl_V': "conflicting V' = C_True" using decide'(1) by auto
          have full: "full1 cdcl\<^sub>W_cp V' W \<or> (V' = W \<and> no_step cdcl\<^sub>W_cp W)"
            using decide'(3) unfolding full_unfold by blast
          consider
              (V'_W) "V' = W"
            | (propa) "propagate\<^sup>+\<^sup>+ V' W" and "conflicting W = C_True"
            | (propa_confl) V'' where "propagate\<^sup>*\<^sup>* V' V''" and "conflict V'' W"
            using tranclp_cdcl\<^sub>W_cp_propagate_with_conflict_or_not[of V W] decide'
            by (metis \<open>full1 cdcl\<^sub>W_cp V' W \<or> V' = W \<and> no_step cdcl\<^sub>W_cp W\<close> full1_def
              tranclp_cdcl\<^sub>W_cp_propagate_with_conflict_or_not)
          then show ?thesis (* too many levels of case distinction *)
            proof cases
              case V'_W
              then show ?thesis
                using confl_V' local.decide'(1,2) s' conf_V
                no_step_cdcl\<^sub>W_cp_no_step_cdcl\<^sub>W_merge_restart by auto
            next
              case propa
              then show ?thesis using local.decide'(1,2) s' by (metis cdcl\<^sub>W_merge_cp.simps conf_V
                no_step_cdcl\<^sub>W_cp_no_step_cdcl\<^sub>W_merge_restart r_into_rtranclp)
            next
              case propa_confl
              then have "cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* V' V''"
                by (metis rtranclp_unfold cdcl\<^sub>W_merge_cp.propagate' r_into_rtranclp)
              then show ?thesis
                using local.decide'(1,2) propa_confl(2) s' conf_V
                no_step_cdcl\<^sub>W_cp_no_step_cdcl\<^sub>W_merge_restart
                by metis
            qed
        next
          case (dec) note s' = this(1) and dec = this(2) and cp = this(3) and ns_cp_T = this(4)
          have "full cdcl\<^sub>W_merge_cp T V"
            unfolding full_def by (simp add: conf_V local.decide'(2)
              no_step_cdcl\<^sub>W_cp_no_step_cdcl\<^sub>W_merge_restart ns_cp_T)
          moreover have "no_step cdcl\<^sub>W_merge_cp V"
             by (simp add: conf_V local.decide'(2) no_step_cdcl\<^sub>W_cp_no_step_cdcl\<^sub>W_merge_restart)
          moreover have "no_step cdcl\<^sub>W_merge_cp S"
            by (metis dec)
          ultimately have "cdcl\<^sub>W_merge_stgy S V"
            using cp by blast
          then have "cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* R V" using s' by auto
          consider
              (V'_W) "V' = W"
            | (propa) "propagate\<^sup>+\<^sup>+ V' W" and "conflicting W = C_True"
            | (propa_confl) V'' where "propagate\<^sup>*\<^sup>* V' V''" and "conflict V'' W"
            using tranclp_cdcl\<^sub>W_cp_propagate_with_conflict_or_not[of V' W] decide'
            unfolding full_unfold full1_def by blast
          then show ?thesis (* too many levels of case distinction *)
            proof cases
              case V'_W
              moreover have "conflicting V' = C_True"
                using decide'(1) by auto
              ultimately show ?thesis
                using \<open>cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* R V\<close> decide' \<open>no_step cdcl\<^sub>W_merge_cp V\<close> by blast
            next
              case propa
              moreover then have "cdcl\<^sub>W_merge_cp V' W"
                by auto
              ultimately show ?thesis
                using \<open>cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* R V\<close> decide' \<open>no_step cdcl\<^sub>W_merge_cp V\<close>
                by (meson r_into_rtranclp)
            next
              case propa_confl
              moreover then have "cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* V' V''"
                by (metis cdcl\<^sub>W_merge_cp.propagate' rtranclp_unfold tranclp_unfold_end)
              ultimately show ?thesis using \<open>cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* R V\<close> decide'
                \<open>no_step cdcl\<^sub>W_merge_cp V\<close> by (meson r_into_rtranclp)
            qed
        next
          case cp
          have "no_step cdcl\<^sub>W_merge_cp V"
            using conf_V local.decide'(2) no_step_cdcl\<^sub>W_cp_no_step_cdcl\<^sub>W_merge_restart by blast
          then have "full cdcl\<^sub>W_merge_cp R V"
            unfolding full_def using cp by fast
          then have "cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* R V"
            unfolding full_unfold by auto
          have "full1 cdcl\<^sub>W_cp V' W \<or> (V' = W \<and> no_step cdcl\<^sub>W_cp W)"
            using decide'(3) unfolding full_unfold by blast

          consider
              (V'_W) "V' = W"
            | (propa) "propagate\<^sup>+\<^sup>+ V' W" and "conflicting W = C_True"
            | (propa_confl) V'' where "propagate\<^sup>*\<^sup>* V' V''" and "conflict V'' W"
            using tranclp_cdcl\<^sub>W_cp_propagate_with_conflict_or_not[of V' W] decide'
            unfolding full_unfold full1_def by blast
          then show ?thesis (* too many levels of case distinction *)
          (* copy paste. copy paste, copy paste *)
            proof cases
              case V'_W
              moreover have "conflicting V' = C_True"
                using decide'(1) by auto
              ultimately show ?thesis
                using \<open>cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* R V\<close> decide'  \<open>no_step cdcl\<^sub>W_merge_cp V\<close> by blast
            next
              case propa
              moreover then have "cdcl\<^sub>W_merge_cp V' W"
                by auto
              ultimately show ?thesis using \<open>cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* R V\<close> decide'
                \<open>no_step cdcl\<^sub>W_merge_cp V\<close> by (meson r_into_rtranclp)
            next
              case propa_confl
              moreover then have "cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* V' V''"
                by (metis cdcl\<^sub>W_merge_cp.propagate' rtranclp_unfold tranclp_unfold_end)
              ultimately show ?thesis using \<open>cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* R V\<close> decide'
                \<open>no_step cdcl\<^sub>W_merge_cp V\<close> by (meson r_into_rtranclp)
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
      then have "\<not>no_step cdcl\<^sub>W_bj V "
        by (auto dest: tranclpD simp: full1_def)
      then consider
         (s') "cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* R V" and "conflicting V = C_True"
        | (dec_confl) S T U where "cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* R S" and "no_step cdcl\<^sub>W_merge_cp S" and
            "decide S T" and "cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* T U" and "conflict U V"
        | (dec) S T where "cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* R S" and "no_step cdcl\<^sub>W_merge_cp S" and "decide S T"
            and "cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* T V" and "conflicting V = C_True"
        | (cp) "cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* R V" and "conflicting V = C_True"
        | (cp_confl) U where "cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* R U" and "conflict U V"
        using IH by meson
      then show ?thesis
        proof cases
          case s' note _ =this(2)
          then have False
            using bj'(1) unfolding full1_def by (force dest!: tranclpD simp: cdcl\<^sub>W_bj.simps)
          then show ?thesis by fast
        next
          case dec note _ = this(5)
          then have False
            using bj'(1) unfolding full1_def by (force dest!: tranclpD simp: cdcl\<^sub>W_bj.simps)
          then show ?thesis by fast
        next
          case dec_confl
          then have "cdcl\<^sub>W_merge_cp U V'"
            using bj' cdcl\<^sub>W_merge_cp.intros(1)[of U V V'] by (simp add: full_unfold)
          then have "cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* T V'"
            using dec_confl(4) by simp
          consider
              (V'_W) "V' = W"
            | (propa) "propagate\<^sup>+\<^sup>+ V' W" and "conflicting W = C_True"
            | (propa_confl) V'' where "propagate\<^sup>*\<^sup>* V' V''" and "conflict V'' W"
            using tranclp_cdcl\<^sub>W_cp_propagate_with_conflict_or_not[of V' W] bj'(3)
            unfolding full_unfold full1_def by blast
          then show ?thesis (* too many levels of case distinction *)
            proof cases
              case V'_W
              then have "no_step cdcl\<^sub>W_cp V'"
                using bj'(3) unfolding full_def by auto
              then have "no_step cdcl\<^sub>W_merge_cp V'"
                by (metis cdcl\<^sub>W_cp.propagate' cdcl\<^sub>W_merge_cp.cases tranclpD
                  no_step_cdcl\<^sub>W_cp_no_conflict_no_propagate(1) )
              then have "full1 cdcl\<^sub>W_merge_cp T V'"
                unfolding full1_def using \<open>cdcl\<^sub>W_merge_cp U V'\<close> dec_confl(4) by auto
              then have "full  cdcl\<^sub>W_merge_cp T V'"
                by (simp add: full_unfold)
              then have "cdcl\<^sub>W_merge_stgy S V'"
                using dec_confl(3) cdcl\<^sub>W_merge_stgy.fw_s_decide \<open>no_step cdcl\<^sub>W_merge_cp S\<close> by blast
              then have "cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* R V'"
                using \<open>cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* R S\<close> by auto
              show ?thesis
                proof cases
                  assume "conflicting W = C_True"
                  then show ?thesis using \<open>cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* R V'\<close> \<open>V' = W\<close> by auto
                next
                  assume "conflicting W \<noteq> C_True"
                  then show ?thesis
                    using \<open>cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* R V'\<close> \<open>V' = W\<close> by (metis \<open>cdcl\<^sub>W_merge_cp U V'\<close>
                      conflicting_not_true_rtranclp_cdcl\<^sub>W_merge_cp_no_step_cdcl\<^sub>W_bj dec_confl(5)
                      r_into_rtranclp conflictE)
                qed
            next
              case propa
              moreover then have "cdcl\<^sub>W_merge_cp V' W"
                by auto
              ultimately show ?thesis using decide' by (meson \<open>cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* T V'\<close> dec_confl(1-3)
                rtranclp.rtrancl_into_rtrancl)
            next
              case propa_confl
              moreover then have "cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* V' V''"
                by (metis cdcl\<^sub>W_merge_cp.propagate' rtranclp_unfold tranclp_unfold_end)
              ultimately show ?thesis by (meson \<open>cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* T V'\<close> dec_confl(1-3) rtranclp_trans)
            qed
        next
          case cp note _ = this(2)
          then show ?thesis using bj'(1)  \<open>\<not> no_step cdcl\<^sub>W_bj V\<close>
            conflicting_not_true_rtranclp_cdcl\<^sub>W_merge_cp_no_step_cdcl\<^sub>W_bj by auto
        next
          case cp_confl
          then have "cdcl\<^sub>W_merge_cp U V'" by (simp add: cdcl\<^sub>W_merge_cp.conflict' full_unfold
            local.bj'(1))
          consider
              (V'_W) "V' = W"
            | (propa) "propagate\<^sup>+\<^sup>+ V' W" and "conflicting W = C_True"
            | (propa_confl) V'' where "propagate\<^sup>*\<^sup>* V' V''" and "conflict V'' W"
            using tranclp_cdcl\<^sub>W_cp_propagate_with_conflict_or_not[of V' W] bj'
            unfolding full_unfold full1_def by blast
          then show ?thesis (* too many levels of case distinction *)
          (* copy paste. copy paste, copy paste *)
            proof cases
              case V'_W
              show ?thesis
                proof cases
                  assume "conflicting V' = C_True"
                  then show ?thesis
                    using V'_W \<open>cdcl\<^sub>W_merge_cp U V'\<close> cp_confl(1) by force
                next
                  assume confl: "conflicting V' \<noteq> C_True"
                  then have "no_step cdcl\<^sub>W_merge_stgy V'"
                    by (auto simp: cdcl\<^sub>W_merge_stgy.simps full1_def full_def cdcl\<^sub>W_merge_cp.simps
                      dest!: tranclpD)
                  have "no_step cdcl\<^sub>W_merge_cp V'"
                    using confl by (auto simp: full1_def full_def cdcl\<^sub>W_merge_cp.simps
                    dest!: tranclpD)
                  moreover have "cdcl\<^sub>W_merge_cp U W"
                    using V'_W \<open>cdcl\<^sub>W_merge_cp U V'\<close> by blast
                  ultimately have "full1 cdcl\<^sub>W_merge_cp R V'"
                    using cp_confl(1) V'_W unfolding full1_def by auto
                  then have "cdcl\<^sub>W_merge_stgy R V'"
                    by auto
                  moreover have "no_step cdcl\<^sub>W_merge_stgy V'"
                    using confl \<open>no_step cdcl\<^sub>W_merge_cp V'\<close> by (auto simp: cdcl\<^sub>W_merge_stgy.simps
                      full1_def dest!: tranclpD)
                  ultimately have "cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* R V'" by auto
                  show ?thesis by (metis V'_W \<open>cdcl\<^sub>W_merge_cp U V'\<close> \<open>cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* R V'\<close>
                    conflicting_not_true_rtranclp_cdcl\<^sub>W_merge_cp_no_step_cdcl\<^sub>W_bj cp_confl(1)
                    rtranclp.rtrancl_into_rtrancl step.prems)
                qed
            next
              case propa
              moreover then have "cdcl\<^sub>W_merge_cp V' W"
                by auto
              ultimately show ?thesis using \<open>cdcl\<^sub>W_merge_cp U V'\<close> cp_confl(1) by force
            next
              case propa_confl
              moreover then have "cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* V' V''"
                by (metis cdcl\<^sub>W_merge_cp.propagate' rtranclp_unfold tranclp_unfold_end)
              ultimately show ?thesis
                using \<open>cdcl\<^sub>W_merge_cp U V'\<close> cp_confl(1) by (metis rtranclp.rtrancl_into_rtrancl
                  rtranclp_trans)
            qed
        qed
    qed
qed

lemma cdcl\<^sub>W_merge_stgy_cases[consumes 1, case_names fw_s_cp fw_s_decide]:
  assumes
    "cdcl\<^sub>W_merge_stgy S U"
    "full1 cdcl\<^sub>W_merge_cp S U \<Longrightarrow> P"
    "\<And>T. decide S T \<Longrightarrow> no_step cdcl\<^sub>W_merge_cp S \<Longrightarrow> full cdcl\<^sub>W_merge_cp T U \<Longrightarrow> P"
  shows "P"
  using assms by (auto simp: cdcl\<^sub>W_merge_stgy.simps)

lemma decide_rtranclp_cdcl\<^sub>W_s'_rtranclp_cdcl\<^sub>W_s':
  assumes
    dec: "decide S T" and
    "cdcl\<^sub>W_s'\<^sup>*\<^sup>* T U" and
    n_s_S: "no_step cdcl\<^sub>W_cp S" and
    "no_step cdcl\<^sub>W_cp U"
  shows "cdcl\<^sub>W_s'\<^sup>*\<^sup>* S U"
  using assms(2,4)
proof induction
  case (step U V) note st =this(1) and s' = this(2) and IH = this(3) and n_s = this(4)
  consider
      (TU) "T = U"
    | (s'_st) T' where "cdcl\<^sub>W_s' T T'" and "cdcl\<^sub>W_s'\<^sup>*\<^sup>* T' U"
    using st[unfolded rtranclp_unfold] by (auto dest!: tranclpD)
  then show ?case
    proof cases
      case TU
      then show ?thesis
        proof -
          have "\<forall>p s sa. (\<not> p\<^sup>+\<^sup>+ (s::'st) sa \<or> (\<exists>sb. p\<^sup>*\<^sup>* s sb \<and> p sb sa))
            \<and> ((\<forall>sb. \<not> p\<^sup>*\<^sup>* s sb \<or> \<not> p sb sa) \<or> p\<^sup>+\<^sup>+ s sa)"
            by (metis tranclp_unfold_end)
          then obtain ss :: "('st \<Rightarrow> 'st \<Rightarrow> bool) \<Rightarrow> 'st \<Rightarrow> 'st \<Rightarrow> 'st" where
            f2: "\<forall>p s sa. (\<not> p\<^sup>+\<^sup>+ s sa \<or> p\<^sup>*\<^sup>* s (ss p s sa) \<and> p (ss p s sa) sa)
              \<and> ((\<forall>sb. \<not> p\<^sup>*\<^sup>* s sb \<or> \<not> p sb sa) \<or> p\<^sup>+\<^sup>+ s sa)"
            by moura
          have f3: "cdcl\<^sub>W_s' T V"
            using TU s' by blast
          moreover
          { assume "\<not> cdcl\<^sub>W_s' S T"
            then have "cdcl\<^sub>W_s' S V"
              using f3 by (metis (no_types) assms(1,3) cdcl\<^sub>W_s'.cases cdcl\<^sub>W_s'.decide' full_unfold)
            then have "cdcl\<^sub>W_s'\<^sup>+\<^sup>+ S V"
              by blast }
          ultimately have "cdcl\<^sub>W_s'\<^sup>+\<^sup>+ S V"
            using f2 by (metis (full_types) rtranclp_unfold)
          then show ?thesis
            by simp
        qed
    next
      case (s'_st T') note s'_T' = this(1) and st = this(2)
      have "cdcl\<^sub>W_s'\<^sup>*\<^sup>* S T'"
        using s'_T'
        proof cases
          case conflict'
          then have "cdcl\<^sub>W_s' S T'"
             using dec cdcl\<^sub>W_s'.decide' n_s_S by (simp add: full_unfold)
          then show ?thesis
             using st by auto
        next
          case (decide' T'')
          then have "cdcl\<^sub>W_s' S T"
             using dec cdcl\<^sub>W_s'.decide' n_s_S by (simp add: full_unfold)
          then show ?thesis using decide' s'_T' by auto
        next
          case bj'
          then have False
            using dec unfolding full1_def by (fastforce dest!: tranclpD simp: cdcl\<^sub>W_bj.simps)
          then show ?thesis by fast
        qed
      then show ?thesis using s' st by auto
    qed
next
  case base
  then have "full cdcl\<^sub>W_cp T T"
    by (simp add: full_unfold)
  then show ?case
    using cdcl\<^sub>W_s'.simps dec n_s_S by auto
qed

lemma rtranclp_cdcl\<^sub>W_merge_stgy_rtranclp_cdcl\<^sub>W_s':
  assumes
    "cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* R V" and
    inv: "cdcl\<^sub>W_all_struct_inv R"
  shows "cdcl\<^sub>W_s'\<^sup>*\<^sup>* R V"
  using assms(1)
proof induction
  case base
  then show ?case by simp
next
  case (step S T) note st = this(1) and fw = this(2) and IH = this(3)
  have "cdcl\<^sub>W_all_struct_inv S"
    using inv rtranclp_cdcl\<^sub>W_all_struct_inv_inv rtranclp_cdcl\<^sub>W_merge_stgy_rtranclp_cdcl\<^sub>W st by blast
  from fw show ?case
    proof (cases rule: cdcl\<^sub>W_merge_stgy_cases)
      case fw_s_cp
      then show ?thesis
        proof -
          assume a1: "full1 cdcl\<^sub>W_merge_cp S T"
          obtain ss :: "('st \<Rightarrow> 'st \<Rightarrow> bool) \<Rightarrow> 'st \<Rightarrow> 'st" where
            f2: "\<And>p s sa pa sb sc sd pb se sf. (\<not> full1 p (s::'st) sa \<or> p\<^sup>+\<^sup>+ s sa)
              \<and> (\<not> pa (sb::'st) sc \<or> \<not> full1 pa sd sb) \<and> (\<not> pb\<^sup>+\<^sup>+ se sf \<or> pb sf (ss pb sf)
              \<or> full1 pb se sf)"
            by (metis (no_types) full1_def)
          then have f3: "cdcl\<^sub>W_merge_cp\<^sup>+\<^sup>+ S T"
            using a1 by auto
          obtain ssa :: "('st \<Rightarrow> 'st \<Rightarrow> bool) \<Rightarrow> 'st \<Rightarrow> 'st \<Rightarrow> 'st" where
            f4: "\<And>p s sa. \<not> p\<^sup>+\<^sup>+ s sa \<or> p s (ssa p s sa)"
            by (meson tranclp_unfold_begin)
          then have f5: "\<And>s. \<not> full1 cdcl\<^sub>W_merge_cp s S"
            using f3 f2 by (metis (full_types))
          have "\<And>s. \<not> full cdcl\<^sub>W_merge_cp s S"
            using f4 f3 by (meson full_def)
          then have "S = R"
            using f5 by (metis (no_types) cdcl\<^sub>W_merge_stgy.simps rtranclp_unfold st
              tranclp_unfold_end)
          then show ?thesis
            using f2 a1 by (metis (no_types) \<open>cdcl\<^sub>W_all_struct_inv S\<close>
              conflicting_true_full1_cdcl\<^sub>W_merge_cp_imp_full1_cdcl\<^sub>W_s'_without_decode
              rtranclp_cdcl\<^sub>W_s'_without_decide_rtranclp_cdcl\<^sub>W_s' rtranclp_unfold)
        qed
    next
      case (fw_s_decide S') note dec = this(1) and n_S = this(2) and full = this(3)
      moreover then have "conflicting S' = C_True"
        by auto
      ultimately have "full cdcl\<^sub>W_s'_without_decide S' T"
        by (meson \<open>cdcl\<^sub>W_all_struct_inv S\<close> cdcl\<^sub>W_merge_restart_cdcl\<^sub>W fw_r_decide
          rtranclp_cdcl\<^sub>W_all_struct_inv_inv
          conflicting_true_full_cdcl\<^sub>W_merge_cp_iff_full_cdcl\<^sub>W_s'_without_decode)
      then have a1: "cdcl\<^sub>W_s'\<^sup>*\<^sup>* S' T"
        unfolding full_def by (metis (full_types)rtranclp_cdcl\<^sub>W_s'_without_decide_rtranclp_cdcl\<^sub>W_s')
      have "cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* S T"
        using fw by blast
      then have "cdcl\<^sub>W_s'\<^sup>*\<^sup>* S T"
        using decide_rtranclp_cdcl\<^sub>W_s'_rtranclp_cdcl\<^sub>W_s' a1 by (metis \<open>cdcl\<^sub>W_all_struct_inv S\<close> dec
          n_S no_step_cdcl\<^sub>W_merge_cp_no_step_cdcl\<^sub>W_cp cdcl\<^sub>W_all_struct_inv_def
          rtranclp_cdcl\<^sub>W_merge_stgy'_no_step_cdcl\<^sub>W_cp_or_eq)
      then show ?thesis using IH by auto
    qed
qed

lemma rtranclp_cdcl\<^sub>W_merge_stgy_distinct_mset_clauses:
  assumes invR: "cdcl\<^sub>W_all_struct_inv R" and
  st: "cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* R S" and
  dist: "distinct_mset (clauses R)" and
  R: "trail R = []"
  shows "distinct_mset (clauses S)"
  using rtranclp_cdcl\<^sub>W_stgy_distinct_mset_clauses[OF invR _ dist R]
  invR st rtranclp_mono[of cdcl\<^sub>W_s' "cdcl\<^sub>W_stgy\<^sup>*\<^sup>*"] cdcl\<^sub>W_s'_is_rtranclp_cdcl\<^sub>W_stgy
  by (auto dest!: cdcl\<^sub>W_s'_is_rtranclp_cdcl\<^sub>W_stgy rtranclp_cdcl\<^sub>W_merge_stgy_rtranclp_cdcl\<^sub>W_s')

lemma no_step_cdcl\<^sub>W_s'_no_step_cdcl\<^sub>W_merge_stgy:
  assumes
    inv: "cdcl\<^sub>W_all_struct_inv R" and s': "no_step cdcl\<^sub>W_s' R"
  shows "no_step cdcl\<^sub>W_merge_stgy R"
proof -
  { fix ss :: 'st
    obtain ssa :: "'st \<Rightarrow> 'st \<Rightarrow> 'st" where
      ff1: "\<And>s sa. \<not> cdcl\<^sub>W_merge_stgy s sa \<or> full1 cdcl\<^sub>W_merge_cp s sa \<or> decide s (ssa s sa)"
      using cdcl\<^sub>W_merge_stgy.cases by moura
    obtain ssb :: "('st \<Rightarrow> 'st \<Rightarrow> bool) \<Rightarrow> 'st \<Rightarrow> 'st \<Rightarrow> 'st" where
      ff2: "\<And>p s sa. \<not> p\<^sup>+\<^sup>+ s sa \<or> p s (ssb p s sa)"
      by (meson tranclp_unfold_begin)
    obtain ssc :: "'st \<Rightarrow> 'st" where
      ff3: "\<And>s sa sb. (\<not> cdcl\<^sub>W_all_struct_inv s \<or> \<not> cdcl\<^sub>W_cp s sa \<or> cdcl\<^sub>W_s' s (ssc s))
        \<and> (\<not> cdcl\<^sub>W_all_struct_inv s \<or> \<not> cdcl\<^sub>W_o s sb \<or> cdcl\<^sub>W_s' s (ssc s))"
      using n_step_cdcl\<^sub>W_stgy_iff_no_step_cdcl\<^sub>W_cl_cdcl\<^sub>W_o by moura
    then have ff4: "\<And>s. \<not> cdcl\<^sub>W_o R s"
      using s' inv by blast
    have ff5: "\<And>s. \<not> cdcl\<^sub>W_cp\<^sup>+\<^sup>+ R s"
      using ff3 ff2 s' by (metis inv)
    have "\<And>s. \<not> cdcl\<^sub>W_bj\<^sup>+\<^sup>+ R s"
      using ff4 ff2 by (metis bj)
    then have "\<And>s. \<not> cdcl\<^sub>W_s'_without_decide R s"
      using ff5 by (simp add: cdcl\<^sub>W_s'_without_decide.simps full1_def)
    then have "\<not> cdcl\<^sub>W_s'_without_decide\<^sup>+\<^sup>+ R ss"
      using ff2 by blast
    then have "\<not> cdcl\<^sub>W_merge_stgy R ss"
      using ff4 ff1 by (metis (full_types)  decide full1_def inv
        conflicting_true_full1_cdcl\<^sub>W_merge_cp_imp_full1_cdcl\<^sub>W_s'_without_decode) }
  then show ?thesis
    by fastforce
qed

lemma wf_cdcl\<^sub>W_merge_cp:
  "wf{(T, S). cdcl\<^sub>W_all_struct_inv S \<and> cdcl\<^sub>W_merge_cp S T}"
  using wf_tranclp_cdcl\<^sub>W_merge by (rule wf_subset) (auto simp: cdcl\<^sub>W_merge_cp_tranclp_cdcl\<^sub>W_merge)

lemma wf_cdcl\<^sub>W_merge_stgy:
  "wf{(T, S). cdcl\<^sub>W_all_struct_inv S \<and> cdcl\<^sub>W_merge_stgy S T}"
  using wf_tranclp_cdcl\<^sub>W_merge by (rule wf_subset)
  (auto simp add: cdcl\<^sub>W_merge_stgy_tranclp_cdcl\<^sub>W_merge)

lemma cdcl\<^sub>W_merge_cp_obtain_normal_form:
  assumes inv: "cdcl\<^sub>W_all_struct_inv R"
  obtains S where "full cdcl\<^sub>W_merge_cp R S"
proof -
  obtain S where "full (\<lambda>S T. cdcl\<^sub>W_all_struct_inv S \<and> cdcl\<^sub>W_merge_cp S T) R S"
    using wf_exists_normal_form_full[OF wf_cdcl\<^sub>W_merge_cp] by blast
  then have
    st: "(\<lambda>S T. cdcl\<^sub>W_all_struct_inv S \<and> cdcl\<^sub>W_merge_cp S T)\<^sup>*\<^sup>* R S" and
    n_s: "no_step (\<lambda>S T. cdcl\<^sub>W_all_struct_inv S \<and> cdcl\<^sub>W_merge_cp S T) S"
    unfolding full_def by blast+
  have "cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* R S"
    using st by induction auto
  moreover
    have "cdcl\<^sub>W_all_struct_inv S"
      using st inv
      apply (induction rule: rtranclp_induct)
        apply simp
      by (meson r_into_rtranclp rtranclp_cdcl\<^sub>W_all_struct_inv_inv
        rtranclp_cdcl\<^sub>W_merge_cp_rtranclp_cdcl\<^sub>W)
    then have "no_step cdcl\<^sub>W_merge_cp S"
      using n_s by auto
  ultimately show ?thesis
    using that unfolding full_def by blast
qed

lemma no_step_cdcl\<^sub>W_merge_stgy_no_step_cdcl\<^sub>W_s':
  assumes
    inv: "cdcl\<^sub>W_all_struct_inv R" and
    confl: "conflicting R = C_True" and
    n_s: "no_step cdcl\<^sub>W_merge_stgy R"
  shows "no_step cdcl\<^sub>W_s' R"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then obtain S where "cdcl\<^sub>W_s' R S" by auto
  then show False
    proof cases
      case conflict'
      then obtain S' where "full1 cdcl\<^sub>W_merge_cp R S'"
        by (metis (full_types) cdcl\<^sub>W_merge_cp_obtain_normal_form cdcl\<^sub>W_s'_without_decide.simps confl
          conflicting_true_no_step_cdcl\<^sub>W_merge_cp_no_step_s'_without_decide full_def full_unfold inv
          cdcl\<^sub>W_all_struct_inv_def)
      then show False using n_s by blast
    next
      case (decide' R')
      then have "cdcl\<^sub>W_all_struct_inv R'"
        using inv cdcl\<^sub>W_all_struct_inv_inv cdcl\<^sub>W.other cdcl\<^sub>W_o.decide by meson
      then obtain R'' where "full cdcl\<^sub>W_merge_cp R' R''"
        using cdcl\<^sub>W_merge_cp_obtain_normal_form by blast
      moreover have "no_step cdcl\<^sub>W_merge_cp R"
        by (simp add: confl local.decide'(2) no_step_cdcl\<^sub>W_cp_no_step_cdcl\<^sub>W_merge_restart)
      ultimately show False using n_s cdcl\<^sub>W_merge_stgy.intros local.decide'(1) by blast
    next
      case (bj' R')
      then show False
        using confl no_step_cdcl\<^sub>W_cp_no_step_cdcl\<^sub>W_s'_without_decide inv
        unfolding cdcl\<^sub>W_all_struct_inv_def by blast
    qed
qed

lemma rtranclp_cdcl\<^sub>W_merge_cp_no_step_cdcl\<^sub>W_bj:
  assumes "conflicting R = C_True" and "cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* R S"
  shows "no_step cdcl\<^sub>W_bj S"
  using assms conflicting_not_true_rtranclp_cdcl\<^sub>W_merge_cp_no_step_cdcl\<^sub>W_bj by blast

lemma rtranclp_cdcl\<^sub>W_merge_stgy_no_step_cdcl\<^sub>W_bj:
  assumes confl: "conflicting R = C_True" and "cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* R S"
  shows "no_step cdcl\<^sub>W_bj S"
  using assms(2)
proof induction
  case base
  then show ?case
    using confl by (auto simp: cdcl\<^sub>W_bj.simps)[]
next
  case (step S T) note st = this(1) and fw = this(2) and IH = this(3)
  have confl_S: "conflicting S = C_True"
    using fw apply cases
    by (auto simp: full1_def cdcl\<^sub>W_merge_cp.simps dest!: tranclpD)
  from fw show ?case
    proof cases
      case fw_s_cp
      then show ?thesis
        using rtranclp_cdcl\<^sub>W_merge_cp_no_step_cdcl\<^sub>W_bj confl_S
        by (simp add: full1_def tranclp_into_rtranclp)
    next
      case (fw_s_decide S')
      moreover then have "conflicting S' = C_True" by auto
      ultimately show ?thesis
        using conflicting_not_true_rtranclp_cdcl\<^sub>W_merge_cp_no_step_cdcl\<^sub>W_bj
        unfolding full_def by fast
    qed
qed

lemma full_cdcl\<^sub>W_s'_full_cdcl\<^sub>W_merge_restart:
  assumes
    "conflicting R = C_True" and
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
      (fw_no_confl) "cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* R V" and "conflicting V = C_True"
    | (fw_confl) "cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* R V" and "conflicting V \<noteq> C_True" and "no_step cdcl\<^sub>W_bj V"
    | (fw_dec_confl) S T U where "cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* R S" and "no_step cdcl\<^sub>W_merge_cp S" and
        "decide S T" and "cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* T U" and "conflict U V"
    | (fw_dec_no_confl) S T where "cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* R S" and "no_step cdcl\<^sub>W_merge_cp S" and
        "decide S T" and "cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* T V" and "conflicting V = C_True"
    | (cp_no_confl) "cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* R V" and "conflicting V = C_True"
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
        by (metis (no_types) full_unfold fw_s_cp rtranclp_unfold tranclp_unfold_end)
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
      assume "conflicting V = C_True"
      then show ?thesis
        by (metis inv' \<open>full cdcl\<^sub>W_merge_stgy R V\<close> full_def
          no_step_cdcl\<^sub>W_merge_stgy_no_step_cdcl\<^sub>W_s')
    next
      assume confl_V: "conflicting V \<noteq> C_True"
      then have "no_step cdcl\<^sub>W_bj V"
      using rtranclp_cdcl\<^sub>W_merge_stgy_no_step_cdcl\<^sub>W_bj by (meson \<open>full cdcl\<^sub>W_merge_stgy R V\<close>
        assms(1) full_def)
      then show ?thesis using confl_V by (fastforce simp: cdcl\<^sub>W_s'.simps full1_def cdcl\<^sub>W_cp.simps
        dest!: tranclpD)
    qed
  ultimately show ?s' unfolding full_def by blast
qed

lemma full_cdcl\<^sub>W_stgy_full_cdcl\<^sub>W_merge:
  assumes
    "conflicting R = C_True" and
    inv: "cdcl\<^sub>W_all_struct_inv R"
  shows "full cdcl\<^sub>W_stgy R V \<longleftrightarrow> full cdcl\<^sub>W_merge_stgy R V"
  by (simp add: assms(1) full_cdcl\<^sub>W_s'_full_cdcl\<^sub>W_merge_restart full_cdcl\<^sub>W_stgy_iff_full_cdcl\<^sub>W_s'
    inv)

lemma full_cdcl\<^sub>W_merge_stgy_final_state_conclusive':
  fixes S' :: "'st"
  assumes full: "full cdcl\<^sub>W_merge_stgy (init_state N) S'"
  and no_d: "distinct_mset_mset N"
  shows "(conflicting S' = C_Clause {#} \<and> unsatisfiable (set_mset N))
    \<or> (conflicting S' = C_True \<and> trail S' \<Turnstile>asm N \<and> satisfiable (set_mset N))"
proof -
  have "cdcl\<^sub>W_all_struct_inv (init_state N)"
    using no_d unfolding cdcl\<^sub>W_all_struct_inv_def by auto
  moreover have "conflicting (init_state N) = C_True"
    by auto
  ultimately show ?thesis
    by (simp add: full full_cdcl\<^sub>W_stgy_final_state_conclusive_from_init_state
      full_cdcl\<^sub>W_stgy_full_cdcl\<^sub>W_merge no_d)
qed

end

subsection \<open>Adding Restarts\<close>
locale cdcl\<^sub>W_ops_restart =
  cdcl\<^sub>W_ops trail init_clss learned_clss backtrack_lvl conflicting cons_trail tl_trail
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
  shows "set_mset (learned_clss S) \<subseteq> build_all_simple_clss (atms_of_msu (init_clss S))"
proof
  fix C
  assume C: "C \<in> set_mset (learned_clss S)"
  have "distinct_mset C"
    using C inv unfolding cdcl\<^sub>W_all_struct_inv_def distinct_cdcl\<^sub>W_state_def distinct_mset_set_def
    by auto
  moreover have "\<not>tautology C"
    using C inv unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_learned_clause_def by auto
  moreover
    have "atms_of C \<subseteq> atms_of_msu (learned_clss S)"
      using C by auto
    then have "atms_of C \<subseteq> atms_of_msu (init_clss S)"
    using inv  unfolding cdcl\<^sub>W_all_struct_inv_def no_strange_atm_def by force
  moreover have "finite (atms_of_msu (init_clss S))"
    using inv unfolding cdcl\<^sub>W_all_struct_inv_def by auto
  ultimately show "C \<in> build_all_simple_clss (atms_of_msu (init_clss S))"
    using distinct_mset_not_tautology_implies_in_build_all_simple_clss build_all_simple_clss_mono
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
  have "finite (atms_of_msu (init_clss (fst ?S)))"
    using inv unfolding cdcl\<^sub>W_all_struct_inv_def by auto
  have snd_g: "\<And>i. snd (g i) = i + snd (g 0)"
    apply (induct_tac i)
      apply simp
    by (metis Suc_eq_plus1_left add_Suc cdcl\<^sub>W_merge_with_restart_increasing_number g)
  then have snd_g_0: "\<And>i. i > 0 \<Longrightarrow> snd (g i) = i + snd (g 0)"
    by blast
  have unbounded_f_g: "unbounded (\<lambda>i. f (snd (g i)))"
    using f unfolding bounded_def by (metis add.commute f less_or_eq_imp_le snd_g
      not_bounded_nat_exists_larger not_le ordered_cancel_comm_monoid_diff_class.le_iff_add)

  obtain k where
    f_g_k: "f (snd (g k)) > card (build_all_simple_clss (atms_of_msu (init_clss (fst ?S))))" and
    "k > card (build_all_simple_clss (atms_of_msu (init_clss (fst ?S))))"
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
      > card (build_all_simple_clss (atms_of_msu (init_clss (fst ?S))))"
      unfolding m[symmetric] using \<open>m > f (snd (g k))\<close> f_g_k by linarith
    then have "card (set_mset (learned_clss T))
      > card (build_all_simple_clss (atms_of_msu (init_clss (fst ?S))))"
      by linarith
  moreover
    have "init_clss (fst (g k)) = init_clss T"
      using \<open>cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* (fst (g k)) T\<close> rtranclp_cdcl\<^sub>W_merge_stgy_rtranclp_cdcl\<^sub>W
      rtranclp_cdcl\<^sub>W_init_clss inv unfolding cdcl\<^sub>W_all_struct_inv_def by blast
    then have "init_clss (fst ?S) = init_clss T"
      using init_g[of k] by auto
  ultimately show False
    using cdcl\<^sub>W_all_struct_inv_learned_clss_bound by (metis Suc_leI card_mono not_less_eq_eq
      build_all_simple_clss_finite)
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
  have "finite (atms_of_msu (init_clss (fst ?S)))"
    using inv unfolding cdcl\<^sub>W_all_struct_inv_def by auto
  have snd_g: "\<And>i. snd (g i) = i + snd (g 0)"
    apply (induct_tac i)
      apply simp
    by (metis Suc_eq_plus1_left add_Suc cdcl\<^sub>W_with_restart_increasing_number g)
  then have snd_g_0: "\<And>i. i > 0 \<Longrightarrow> snd (g i) = i + snd (g 0)"
    by blast
  have unbounded_f_g: "unbounded (\<lambda>i. f (snd (g i)))"
    using f unfolding bounded_def by (metis add.commute f less_or_eq_imp_le snd_g
      not_bounded_nat_exists_larger not_le ordered_cancel_comm_monoid_diff_class.le_iff_add)

  obtain k where
    f_g_k: "f (snd (g k)) > card (build_all_simple_clss (atms_of_msu (init_clss (fst ?S))))" and
    "k > card (build_all_simple_clss (atms_of_msu (init_clss (fst ?S))))"
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
      > card (build_all_simple_clss (atms_of_msu (init_clss (fst ?S))))"
      unfolding m[symmetric] using \<open>m > f (snd (g k))\<close> f_g_k by linarith
    then have "card (set_mset (learned_clss T))
      > card (build_all_simple_clss (atms_of_msu (init_clss (fst ?S))))"
      by linarith
  moreover
    have "init_clss (fst (g k)) = init_clss T"
      using \<open>cdcl\<^sub>W_stgy\<^sup>*\<^sup>* (fst (g k)) T\<close> rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W rtranclp_cdcl\<^sub>W_init_clss
      inv unfolding cdcl\<^sub>W_all_struct_inv_def
      by blast
    then have "init_clss (fst ?S) = init_clss T"
      using init_g[of k] by auto
  ultimately show False
    using cdcl\<^sub>W_all_struct_inv_learned_clss_bound by (metis Suc_leI card_mono not_less_eq_eq
      build_all_simple_clss_finite)
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
  cdcl\<^sub>W_ops trail init_clss learned_clss backtrack_lvl conflicting cons_trail tl_trail
    add_init_cls
    add_learned_cls remove_cls update_backtrack_lvl update_conflicting init_state
    restart_state
  for
    ur :: nat and
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
    restart_state :: "'st \<Rightarrow> 'st"
begin

sublocale cdcl\<^sub>W_ops_restart _ _ _ _ _ _ _ _ _ _ _ _ _ _ luby_sequence
  apply unfold_locales
  using bounded_luby_sequence by blast

end

end
