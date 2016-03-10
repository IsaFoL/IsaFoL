theory CDCL_W_Merge
imports CDCL_W_Termination
begin

section \<open>Link between Weidenbach's and NOT's CDCL\<close>
subsection \<open>Inclusion of the states\<close>

context conflict_driven_clause_learning\<^sub>W
begin
declare cdcl\<^sub>W.intros[intro] cdcl\<^sub>W_bj.intros[intro] cdcl\<^sub>W_o.intros[intro]

lemma backtrack_no_cdcl\<^sub>W_bj:
  assumes cdcl: "cdcl\<^sub>W_bj T U" and inv: "cdcl\<^sub>W_M_level_inv V"
  shows "\<not>backtrack V T"
  using cdcl inv
  apply (induction rule: cdcl\<^sub>W_bj.induct)
    apply (elim skipE, force elim!: backtrack_levE[OF _ inv] simp: cdcl\<^sub>W_M_level_inv_def)
   apply (elim resolveE, force elim!: backtrack_levE[OF _ inv] simp: cdcl\<^sub>W_M_level_inv_def)
  apply standard
  apply (elim backtrack_levE[OF _ inv], elim backtrackE)
  apply (force simp del: state_simp simp add: state_eq_def cdcl\<^sub>W_M_level_inv_decomp)
  done
 (*  by (force elim!: backtrack_levE[OF _ inv] simp: cdcl\<^sub>W_M_level_inv_def) works too,
 but is much slower (6s vs less than 1s)*)

inductive skip_or_resolve :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
s_or_r_skip[intro]: "skip S T \<Longrightarrow> skip_or_resolve S T" |
s_or_r_resolve[intro]: "resolve S T \<Longrightarrow> skip_or_resolve S T"

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
        using mono_rtranclp[of skip_or_resolve cdcl\<^sub>W]
        by (blast intro: skip_or_resolve.cases)
      then have "skip_or_resolve\<^sup>*\<^sup>* S U"
        using bj IH inv backtrack_no_cdcl\<^sub>W_bj rtranclp_cdcl\<^sub>W_consistent_inv[OF _ inv] by meson
      then show ?thesis
        using bj by (auto simp: cdcl\<^sub>W_bj.simps dest!: skip_or_resolve.intros)
    next
      case SU
      then show ?thesis
        using bj by (auto simp: cdcl\<^sub>W_bj.simps dest!: skip_or_resolve.intros)
    qed
qed

lemma rtranclp_skip_or_resolve_rtranclp_cdcl\<^sub>W:
  "skip_or_resolve\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl\<^sub>W\<^sup>*\<^sup>* S T"
  by (induction rule: rtranclp_induct)
  (auto dest!: cdcl\<^sub>W_bj.intros cdcl\<^sub>W.intros cdcl\<^sub>W_o.intros simp: skip_or_resolve.simps)

definition backjump_l_cond :: "'v clause \<Rightarrow> 'v clause \<Rightarrow> 'v literal \<Rightarrow> 'st \<Rightarrow> 'st \<Rightarrow> bool" where
"backjump_l_cond \<equiv> \<lambda>C C' L' S T. True"

definition inv\<^sub>N\<^sub>O\<^sub>T :: "'st \<Rightarrow> bool" where
"inv\<^sub>N\<^sub>O\<^sub>T \<equiv> \<lambda>S. no_dup (trail S)"

declare inv\<^sub>N\<^sub>O\<^sub>T_def[simp]
end

context conflict_driven_clause_learning\<^sub>W
begin

subsection \<open>More lemmas conflict--propagate and backjumping\<close>
subsubsection \<open>Termination\<close>

lemma cdcl\<^sub>W_cp_normalized_element_all_inv:
  assumes inv: "cdcl\<^sub>W_all_struct_inv S"
  obtains T where "full cdcl\<^sub>W_cp S T"
  using assms cdcl\<^sub>W_cp_normalized_element unfolding cdcl\<^sub>W_all_struct_inv_def by blast
thm backtrackE

lemma cdcl\<^sub>W_bj_measure:
  assumes "cdcl\<^sub>W_bj S T" and "cdcl\<^sub>W_M_level_inv S"
  shows "length (trail S) + (if conflicting S = None then 0 else 1)
    > length (trail T) +  (if conflicting T = None then 0 else 1)"
  using assms by (induction rule: cdcl\<^sub>W_bj.induct)
  (force dest:arg_cong[of _ _ length]
    intro: get_all_marked_decomposition_exists_prepend
    elim!: backtrack_levE skipE resolveE
    simp: cdcl\<^sub>W_M_level_inv_def)+

lemma wf_cdcl\<^sub>W_bj:
  "wf {(b,a). cdcl\<^sub>W_bj a b \<and> cdcl\<^sub>W_M_level_inv a}"
  apply (rule wfP_if_measure[of "\<lambda>_. True"
      _ "\<lambda>T. length (trail T) + (if conflicting T = None then 0 else 1)", simplified])
  using cdcl\<^sub>W_bj_measure by simp

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
      using mono_rtranclp[of cdcl\<^sub>W_bj cdcl\<^sub>W] by blast
    then have "cdcl\<^sub>W_M_level_inv T"
      using rtranclp_cdcl\<^sub>W_consistent_inv lev by auto
  ultimately show ?thesis using T unfolding full_def by auto
qed
lemma rtranclp_skip_state_decomp:
  assumes "skip\<^sup>*\<^sup>* S T" and "no_dup (trail S)"
  shows
    "\<exists>M. trail S = M @ trail T \<and> (\<forall>m\<in>set M. \<not>is_marked m)"
    "init_clss S = init_clss T"
    "learned_clss S = learned_clss T"
    "backtrack_lvl S = backtrack_lvl T"
    "conflicting S = conflicting T"
  using assms by (induction rule: rtranclp_induct)
  (auto simp del: state_simp simp: state_eq_def elim!: skipE)

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
  then obtain K i M1 M2 L D where
    conf: "raw_conflicting V = Some D" and
    LD: "L \<in># mset_ccls D" and
    decomp: "(Marked K (Suc i) # M1, M2) \<in> set (get_all_marked_decomposition (trail V))" and
    lev_L: "get_level (trail V) L = backtrack_lvl V" and
    max: "get_level (trail V) L = get_maximum_level (trail V) (mset_ccls D)" and
    max_D: "get_maximum_level (trail V) (remove1_mset L (mset_ccls D)) \<equiv> i" and
    undef: "undefined_lit M1 L" and
    W: "W \<sim> cons_trail (Propagated L (cls_of_ccls D))
                (reduce_trail_to M1
                  (add_learned_cls (cls_of_ccls D)
                    (update_backtrack_lvl i
                      (update_conflicting None V))))"
  using bt inv by (elim backtrack_levE) metis+
  obtain L' C' M E where
    tr: "trail T = Propagated L' C' # M" and
    raw: "raw_conflicting T = Some E" and
    LE: "-L' \<notin># mset_ccls E" and
    E: "mset_ccls E \<noteq> {#}" and
    V: "V \<sim> tl_trail T"
    using skip by (elim skipE) metis
  let ?M =  "Propagated L' C' # trail V"
  have tr_M: "trail T = ?M"
    using tr V by auto
  have MT: "M = tl (trail T)" and MV: "M = trail V"
    using tr V by auto
  have DE[simp]: "mset_ccls D = mset_ccls E"
    using V conf raw by (auto simp add: state_eq_def simp del: state_simp)
  have "cdcl\<^sub>W\<^sup>*\<^sup>* S T" using bj cdcl\<^sub>W_bj.skip mono_rtranclp[of skip cdcl\<^sub>W S T] other st by meson
  then have inv': "cdcl\<^sub>W_all_struct_inv T"
    using rtranclp_cdcl\<^sub>W_all_struct_inv_inv inv by blast
  have M_lev: "cdcl\<^sub>W_M_level_inv T" using inv' unfolding cdcl\<^sub>W_all_struct_inv_def by auto
  then have n_d': "no_dup ?M"
    using tr_M unfolding cdcl\<^sub>W_M_level_inv_def by auto
  let ?k = "backtrack_lvl T"
  have [simp]:
    "backtrack_lvl V = ?k"
    using V by simp
  have "?k > 0"
    using decomp M_lev V tr unfolding cdcl\<^sub>W_M_level_inv_def by auto
  then have "atm_of L \<in> atm_of ` lits_of_l (trail V)"
    using lev_L get_rev_level_ge_0_atm_of_in[of 0 "rev (trail V)" L]  by auto
  then have L_L': "atm_of L \<noteq> atm_of L'"
    using n_d' unfolding lits_of_def by auto
  have L'_M: "atm_of L' \<notin> atm_of ` lits_of_l (trail V)"
    using n_d' unfolding lits_of_def by auto
  have "?M \<Turnstile>as CNot (mset_ccls D)"
    using inv' raw unfolding cdcl\<^sub>W_conflicting_def cdcl\<^sub>W_all_struct_inv_def tr_M by auto
  then have "L' \<notin># mset_ccls (remove_clit L D)"
    using L_L' L'_M \<open>Propagated L' C' # trail V \<Turnstile>as CNot (mset_ccls D)\<close>
    unfolding true_annots_true_cls true_clss_def
    by (auto simp: uminus_lit_swap atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set dest!: in_diffD)
  have [simp]: "trail (reduce_trail_to M1 T) = M1"
    using decomp undef tr W V by auto
  have "skip\<^sup>*\<^sup>* S V"
    using st skip by auto
  have "no_dup (trail S)"
    using inv unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def by auto
  then have [simp]: "init_clss S = init_clss V" and [simp]: "learned_clss S = learned_clss V"
    using rtranclp_skip_state_decomp[OF \<open>skip\<^sup>*\<^sup>* S V\<close>] V
    by (auto simp del: state_simp simp: state_eq_def)
  then have
    W_S: "W \<sim> cons_trail (Propagated L (cls_of_ccls E)) (reduce_trail_to M1
     (add_learned_cls (cls_of_ccls E) (update_backtrack_lvl i (update_conflicting None T))))"
    using W V undef M_lev decomp tr
    by (auto simp del: state_simp simp: state_eq_def cdcl\<^sub>W_M_level_inv_def)

  obtain M2' where
    decomp': "(Marked K (i+1) # M1, M2') \<in> set (get_all_marked_decomposition (trail T))"
    using decomp V unfolding tr_M by (cases "hd (get_all_marked_decomposition (trail V))",
      cases "get_all_marked_decomposition (trail V)") auto
  moreover
    from L_L' have "get_level ?M L = ?k"
      using lev_L V by (auto split: if_split_asm)
  moreover
    have "atm_of L' \<notin> atms_of (mset_ccls D)"
      by (metis DE LE L_L' \<open>L' \<notin># mset_ccls (remove_clit L D)\<close>  in_remove1_mset_neq remove_clit
        atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set atms_of_def)
    then have "get_level ?M L = get_maximum_level ?M (mset_ccls D)"
      using calculation(2) lev_L max by auto
  moreover
    have "atm_of L' \<notin> atms_of (mset_ccls (remove_clit L D))"
      by (metis DE LE \<open>L' \<notin># mset_ccls (remove_clit L D)\<close>
        atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set atms_of_def in_remove1_mset_neq remove_clit
        in_atms_of_remove1_mset_in_atms_of)
    have "i = get_maximum_level ?M (mset_ccls (remove_clit L D))"
      using max_D  \<open>atm_of L' \<notin> atms_of (mset_ccls (remove_clit L D))\<close> by auto

  ultimately have "backtrack T W"
    apply -
    apply (rule  backtrack_rule[of T _ L K i M1 M2' W, OF raw])
    unfolding tr_M[symmetric]
         using LD apply simp
        apply simp
       apply simp
      apply simp
     apply auto[]
    using W_S  by auto
  then show ?thesis using IH inv by blast
qed

lemma fst_get_all_marked_decomposition_prepend_not_marked:
  assumes "\<forall>m\<in>set MS. \<not> is_marked m"
  shows "set (map fst (get_all_marked_decomposition M))
    = set (map fst (get_all_marked_decomposition (MS @ M)))"
    using assms apply (induction MS rule: marked_lit_list_induct)
    apply auto[2]
    by (rename_tac L m xs; case_tac "get_all_marked_decomposition (xs @ M)") simp_all

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
  then obtain K i M1 M2 L D where
    raw_S: "raw_conflicting S = Some D" and
    LD: "L \<in># mset_ccls D" and
    decomp: "(Marked K (Suc i) # M1, M2) \<in> set (get_all_marked_decomposition (trail S))" and
    lev_l: "get_level (trail S) L = backtrack_lvl S" and
    lev_l_D: "get_level (trail S) L = get_maximum_level (trail S) (mset_ccls D)" and
    i: "get_maximum_level (trail S) (remove1_mset L (mset_ccls D)) \<equiv> i" and
    undef: "undefined_lit M1 L" and
    W: "W \<sim> cons_trail (Propagated L (cls_of_ccls D))
                (reduce_trail_to M1
                  (add_learned_cls (cls_of_ccls D)
                    (update_backtrack_lvl i
                      (update_conflicting None S))))"

    using bt by (elim backtrack_levE)
    (simp_all add: cdcl\<^sub>W_M_level_inv_decomp state_eq_def del: state_simp)
  let ?D = "remove1_mset L (mset_ccls D)"

  have [simp]: "no_dup (trail S)"
    using M_lev by (auto simp: cdcl\<^sub>W_M_level_inv_decomp)
  have "cdcl\<^sub>W_all_struct_inv T"
    using mono_rtranclp[of skip cdcl\<^sub>W] by (smt bj cdcl\<^sub>W_bj.skip inv local.skip  other
      rtranclp_cdcl\<^sub>W_all_struct_inv_inv)
  then have [simp]: "no_dup (trail T)"
    unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def by auto
  (* M\<^sub>T is a proxy to allow auto to unfold T*)
  obtain MS M\<^sub>T where M: "trail S = MS @ M\<^sub>T" and M\<^sub>T: "M\<^sub>T = trail T" and nm: "\<forall>m\<in>set MS. \<not>is_marked m"
    using rtranclp_skip_state_decomp(1)[OF skip] raw_S M_lev by auto
  have T: "state T = (M\<^sub>T, init_clss S, learned_clss S, backtrack_lvl S, Some (mset_ccls D))"
    using M\<^sub>T rtranclp_skip_state_decomp[of S T] skip raw_S
    by (auto simp del: state_simp simp: state_eq_def)

  have "cdcl\<^sub>W_all_struct_inv T"
    apply (rule rtranclp_cdcl\<^sub>W_all_struct_inv_inv[OF _ inv])
    using bj cdcl\<^sub>W_bj.skip local.skip other rtranclp_mono[of skip cdcl\<^sub>W] by blast
  then have "M\<^sub>T \<Turnstile>as CNot (mset_ccls D)"
    unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_conflicting_def using T by blast
  then have "\<forall>L\<in>#mset_ccls D. atm_of L \<in> atm_of ` lits_of_l M\<^sub>T"
    by (meson atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set
      true_annots_true_cls_def_iff_negation_in_model)
  moreover have "no_dup (trail S)"
    using inv unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def by auto
  ultimately have "\<forall>L\<in>#mset_ccls D. atm_of L \<notin> atm_of ` lits_of_l MS"
    unfolding M unfolding lits_of_def by auto
  then have H: "\<And>L. L\<in>#mset_ccls D \<Longrightarrow> get_level (trail S) L  = get_level M\<^sub>T L"
    unfolding M by (fastforce simp: lits_of_def)
  have [simp]: "get_maximum_level (trail S) (mset_ccls D) = get_maximum_level M\<^sub>T (mset_ccls D)"
    by (metis \<open>M\<^sub>T \<Turnstile>as CNot (mset_ccls D)\<close>  M nm true_annots_CNot_all_atms_defined
      get_maximum_level_skip_un_marked_not_present)

  have lev_l': "get_level M\<^sub>T L = backtrack_lvl S"
    using lev_l LD by (auto simp: H)
  have [simp]: "trail (reduce_trail_to M1 T) = M1"
    using T decomp M nm by (smt M\<^sub>T append_assoc beginning_not_marked_invert
      get_all_marked_decomposition_exists_prepend reduce_trail_to_trail_tl_trail_decomp)
  have W: "W \<sim> cons_trail (Propagated L (cls_of_ccls D)) (reduce_trail_to M1
    (add_learned_cls (cls_of_ccls D) (update_backtrack_lvl i (update_conflicting None T))))"
    using W T i decomp undef by (auto simp del: state_simp simp: state_eq_def)
  have lev_l_D': "get_level M\<^sub>T L = get_maximum_level M\<^sub>T (mset_ccls D)"
    using lev_l_D LD by (auto simp: H)
  have [simp]: "get_maximum_level (trail S) ?D = get_maximum_level M\<^sub>T ?D"
    by (smt H get_maximum_level_exists_lit get_maximum_level_ge_get_level in_diffD le_antisym
      not_gr0 not_less)
  then have i': "i = get_maximum_level M\<^sub>T ?D"
    using i by auto
  have "Marked K (i + 1) # M1 \<in> set (map fst (get_all_marked_decomposition (trail S)))"
    using Set.imageI[OF decomp, of fst] by auto
  then have "Marked K (i + 1) # M1 \<in> set (map fst (get_all_marked_decomposition M\<^sub>T))"
    using fst_get_all_marked_decomposition_prepend_not_marked[OF nm] unfolding M  by auto
  then obtain M2' where decomp':"(Marked K (i+1) # M1, M2') \<in> set (get_all_marked_decomposition M\<^sub>T)"
    by auto
  then show "backtrack T W"
    using T decomp' lev_l' lev_l_D' i' W LD undef
    by (auto intro!: backtrack.intros simp del: state_simp simp: state_eq_def)
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
    qed (metis (no_types, lifting) IH rtranclp.simps skip_or_resolve.simps)+
qed

lemma resolve_skip_deterministic:
  "resolve S T \<Longrightarrow> skip S U \<Longrightarrow> False"
  by (auto elim!: skipE resolveE dest: hd_raw_trail)

lemma backtrack_unique:
  assumes
    bt_T: "backtrack S T" and
    bt_U: "backtrack S U" and
    inv: "cdcl\<^sub>W_all_struct_inv S"
  shows "T \<sim> U"
proof -
  have lev: "cdcl\<^sub>W_M_level_inv S"
    using inv unfolding cdcl\<^sub>W_all_struct_inv_def by auto
  then obtain K i M1 M2 L D where
    raw_S: "raw_conflicting S = Some D" and
    LD: "L \<in># mset_ccls D" and
    decomp: "(Marked K (Suc i) # M1, M2) \<in> set (get_all_marked_decomposition (trail S))" and
    lev_l: "get_level (trail S) L = backtrack_lvl S" and
    lev_l_D: "get_level (trail S) L = get_maximum_level (trail S) (mset_ccls D)" and
    i: "get_maximum_level (trail S) (remove1_mset L (mset_ccls D)) \<equiv> i" and
    undef: "undefined_lit M1 L" and
    T: "T \<sim> cons_trail (Propagated L (cls_of_ccls D))
                (reduce_trail_to M1
                  (add_learned_cls (cls_of_ccls D)
                    (update_backtrack_lvl i
                      (update_conflicting None S))))"
    using bt_T by (elim backtrack_levE) (force simp: cdcl\<^sub>W_M_level_inv_def)+


  obtain K' i' M1' M2' L' D' where
    raw_S': "raw_conflicting S = Some D'" and
    LD': "L' \<in># mset_ccls D'" and
    decomp': "(Marked K' (Suc i') # M1', M2') \<in> set (get_all_marked_decomposition (trail S))" and
    lev_l: "get_level (trail S) L' = backtrack_lvl S" and
    lev_l_D: "get_level (trail S) L' = get_maximum_level (trail S) (mset_ccls D')" and
    i': "get_maximum_level (trail S) (remove1_mset L' (mset_ccls D')) \<equiv> i'" and
    undef': "undefined_lit M1' L'" and
    U: "U \<sim> cons_trail (Propagated L' (cls_of_ccls D'))
                (reduce_trail_to M1'
                  (add_learned_cls (cls_of_ccls D')
                    (update_backtrack_lvl i'
                      (update_conflicting None S))))"
    using bt_U lev by (elim backtrack_levE) (force simp: cdcl\<^sub>W_M_level_inv_def)+
  obtain c where M: "trail S = c @ M2 @ Marked K (i + 1) # M1"
    using decomp by auto
  obtain c' where M': "trail S = c' @ M2' @ Marked K' (i' + 1) # M1'"
    using decomp' by auto
  have marked: "get_all_levels_of_marked (trail S) = rev [1..<1+backtrack_lvl S]"
    using inv unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def by auto
  then have "i < backtrack_lvl S"
    unfolding M by (force simp add: rev_swap[symmetric] dest!: arg_cong[of _ _ set])

  have [simp]: "L' = L"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then have "L' \<in># remove1_mset L (mset_ccls D)"
        using raw_S raw_S' LD LD' by (simp add: in_remove1_mset_neq)
      then have "get_maximum_level (trail S) (remove1_mset L (mset_ccls D)) \<ge> backtrack_lvl S"
        using \<open>get_level (trail S) L' = backtrack_lvl S\<close> get_maximum_level_ge_get_level
        by metis
      then show False using i' i  \<open>i < backtrack_lvl S\<close> by auto
    qed
  then have [simp]: "mset_ccls D' = mset_ccls D"
    using raw_S raw_S' by auto
  have [simp]: "i' = i"
    using i i' by auto

  text \<open>Automation in a step later...\<close>
  have H: "\<And>a A B. insert a A = B \<Longrightarrow> a : B"
    by blast
  have "get_all_levels_of_marked (c@M2) = rev [i+2..<1+backtrack_lvl S]" and
    "get_all_levels_of_marked (c'@M2') = rev [i+2..<1+backtrack_lvl S]"
    using marked unfolding M
    using marked unfolding M'
    unfolding rev_swap[symmetric] by (auto dest: append_cons_eq_upt_length_i_end)
  from arg_cong[OF this(1), of set] arg_cong[OF this(2), of set]
  have
    "dropWhile (\<lambda>L. \<not>is_marked L \<or> level_of L \<noteq> Suc i) (c @ M2) = []" and
    "dropWhile (\<lambda>L. \<not>is_marked L \<or> level_of L \<noteq> Suc i) (c' @ M2') = []"
      unfolding dropWhile_eq_Nil_conv Ball_def
      by (intro allI; rename_tac x; case_tac x; auto dest!: H simp add: in_set_conv_decomp)+

  then have [simp]: "M1' = M1"
    using arg_cong[OF M, of "dropWhile (\<lambda>L. \<not>is_marked L \<or> level_of L \<noteq> Suc i)"]
    unfolding M' by auto
  show ?thesis using T U undef inv decomp by (auto simp del: state_simp simp: state_eq_def
    cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_decomp)
qed

lemma if_can_apply_backtrack_no_more_resolve:
  assumes
    skip: "skip\<^sup>*\<^sup>* S U" and
    bt: "backtrack S T" and
    inv: "cdcl\<^sub>W_all_struct_inv S"
  shows "\<not>resolve U V"
proof (rule ccontr)
  assume resolve: "\<not>\<not>resolve U V"

  obtain L E D where
    U: "trail U \<noteq> []" and
    tr_U: "hd_raw_trail U  = Propagated L E" and
    LE: "L \<in># mset_cls E" and
    raw_U: "raw_conflicting U = Some D" and
    LD: "-L \<in># mset_ccls D" and
    "get_maximum_level (trail U) (mset_ccls (remove_clit (-L) D)) = backtrack_lvl U" and
    V: "V \<sim> update_conflicting (Some (union_ccls (remove_clit (-L) D)
      (ccls_of_cls (remove_lit L E))))
      (tl_trail U) "
    using resolve by (auto elim!: resolveE)
  have "cdcl\<^sub>W_all_struct_inv U"
    using mono_rtranclp[of skip cdcl\<^sub>W] by (meson bj cdcl\<^sub>W_bj.skip inv local.skip other
      rtranclp_cdcl\<^sub>W_all_struct_inv_inv)
  then have [iff]: "no_dup (trail S)" "cdcl\<^sub>W_M_level_inv S" and [iff]: "no_dup (trail U)"
    using inv unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def by blast+
  then have
    S: "init_clss U = init_clss S"
       "learned_clss U = learned_clss S"
       "backtrack_lvl U = backtrack_lvl S"
       "conflicting S = Some (mset_ccls D)"
    using rtranclp_skip_state_decomp[OF skip] U raw_U
    by (auto simp del: state_simp simp: state_eq_def)
  obtain M\<^sub>0 where
    tr_S: "trail S = M\<^sub>0 @ trail U" and
    nm: "\<forall>m\<in>set M\<^sub>0. \<not>is_marked m"
    using rtranclp_skip_state_decomp[OF skip] by blast

  obtain K' i' M1' M2' L' D' where
    raw_S': "raw_conflicting S = Some D'" and
    LD': "L' \<in># mset_ccls D'" and
    decomp': "(Marked K' (Suc i') # M1', M2') \<in> set (get_all_marked_decomposition (trail S))" and
    lev_l: "get_level (trail S) L' = backtrack_lvl S" and
    lev_l_D: "get_level (trail S) L' = get_maximum_level (trail S) (mset_ccls D')" and
    i': "get_maximum_level (trail S) (remove1_mset L' (mset_ccls D')) \<equiv> i'" and
    undef': "undefined_lit M1' L'" and
    R: "T \<sim> cons_trail (Propagated L' (cls_of_ccls D'))
                (reduce_trail_to M1'
                  (add_learned_cls (cls_of_ccls D')
                    (update_backtrack_lvl i'
                      (update_conflicting None S))))"
    using bt by (elim backtrack_levE) (fastforce simp: S state_eq_def simp del:state_simp)+
  obtain c where M: "trail S = c @ M2' @ Marked K' (i' + 1) # M1'"
    using get_all_marked_decomposition_exists_prepend[OF decomp'] by auto
  have marked: "get_all_levels_of_marked (trail S) = rev [1..<1+backtrack_lvl S]"
    using inv unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def by auto
  then have "i' < backtrack_lvl S"
    unfolding M by (force simp add: rev_swap[symmetric] dest!: arg_cong[of _ _ set])

  have U: "trail U = Propagated L (mset_cls E) # trail V"
   using tr_S hd_raw_trail[OF U] U S V tr_U by (auto simp: lits_of_def)
  have DD'[simp]: "mset_ccls D' = mset_ccls D"
    using raw_U raw_S' S by auto
  have [simp]: "L' = -L"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then have "-L \<in># remove1_mset L' (mset_ccls D')"
        using DD' LD' LD by (simp add: in_remove1_mset_neq)
      moreover
        have M': "trail S = M\<^sub>0 @ Propagated L (mset_cls E) # trail V"
          using tr_S unfolding U by auto
        have "no_dup (trail S)"
           using inv U unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def by auto
        then have atm_L_notin_M: "atm_of L \<notin> atm_of ` (lits_of_l (trail V))"
          using M' U S by (auto simp: lits_of_def)
        have "get_all_levels_of_marked (trail S) = rev [1..<1+backtrack_lvl S]"
          using inv U unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def by auto
        then have "get_all_levels_of_marked (trail U) = rev [1..<1+backtrack_lvl S]"
          using nm M' U by (simp add: get_all_levels_of_marked_no_marked)
        then have get_lev_L:
          "get_level(Propagated L (mset_cls E) # trail V) L = backtrack_lvl S"
          using get_level_get_rev_level_get_all_levels_of_marked[OF atm_L_notin_M,
            of "[Propagated L (mset_cls E)]"] U  by auto
        have "atm_of L \<notin> atm_of ` (lits_of_l (rev M\<^sub>0))"
          using \<open>no_dup (trail S)\<close> M' by (auto simp: lits_of_def)
        then have "get_level (trail S) L = backtrack_lvl S"
          by (metis M' get_lev_L get_rev_level_notin_end rev_append)
      ultimately
        have "get_maximum_level (trail S) (remove1_mset L' (mset_ccls D')) \<ge> backtrack_lvl S"
          by (metis get_maximum_level_ge_get_level get_rev_level_uminus)
      then show False
        using \<open>i' < backtrack_lvl S\<close>  i' by auto
    qed
  have "cdcl\<^sub>W\<^sup>*\<^sup>* S U"
    using bj cdcl\<^sub>W_bj.skip local.skip mono_rtranclp[of skip cdcl\<^sub>W S U] other by meson
  then have "cdcl\<^sub>W_all_struct_inv U"
    using inv rtranclp_cdcl\<^sub>W_all_struct_inv_inv by blast
  then have "Propagated L (mset_cls E) # trail V \<Turnstile>as CNot (mset_ccls D')"
    using cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_conflicting_def raw_U U by auto
  then have "\<forall>L'\<in># (remove1_mset L' (mset_ccls D')) . atm_of L' \<in> atm_of ` lits_of_l (Propagated L (mset_cls E) # trail U)"
    using U atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set in_CNot_implies_uminus(2)
    by (fastforce dest: in_diffD)
  then have "get_maximum_level (trail S) (remove1_mset L' (mset_ccls D')) = backtrack_lvl S"
     using get_maximum_level_skip_un_marked_not_present[of "remove1_mset L' (mset_ccls D')"
         "trail U" M\<^sub>0] tr_S nm U
      \<open>get_maximum_level (trail U) (mset_ccls (remove_clit (- L) D)) = backtrack_lvl U\<close>
     by (auto simp: S)
  then show False
    using i' \<open>i' < backtrack_lvl S\<close> by auto
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
  by induction (simp_all add: if_can_apply_backtrack_no_more_resolve skip_or_resolve.simps)

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

  have "cdcl\<^sub>W\<^sup>*\<^sup>* S W"  using mono_rtranclp[of cdcl\<^sub>W_bj cdcl\<^sub>W] st by blast
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
            by (meson skip_or_resolve.cases)
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
                 by (simp add: local.skip r_into_rtranclp st step.prems skip_or_resolve.intros)
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
              by (metis (no_types, hide_lams) \<open>cdcl\<^sub>W_all_struct_inv S\<close>
                rtranclp_cdcl\<^sub>W_all_struct_inv_inv)
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
                 by (simp add: local.skip r_into_rtranclp st step.prems skip_or_resolve.intros)
               ultimately show ?case by simp
             qed
          then show ?thesis using res no_bt by blast
        qed
    qed
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
        using \<open>cdcl\<^sub>W_M_level_inv T\<close> n_s cdcl\<^sub>W_bj_state_eq_compatible[of T _ V] TV
        by (meson backtrack_state_eq_compatible cdcl\<^sub>W_bj.simps resolve_state_eq_compatible
          skip_state_eq_compatible state_eq_ref)
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
              have "cdcl\<^sub>W_bj U U'"
                by (meson \<open>skip\<^sup>+\<^sup>+ T U\<close> backtrack bt inv_T rtranclp_skip_backtrack_backtrack_end
                  tranclp_into_rtranclp)
              then have "cdcl\<^sub>W_bj\<^sup>+\<^sup>+ U V"
                using \<open>cdcl\<^sub>W_bj\<^sup>*\<^sup>* U' V\<close> by auto
              then show ?thesis
                by (meson tranclp_into_rtranclp)
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

lemma rtranclp_cdcl\<^sub>W_bj_rtranclp_cdcl\<^sub>W:
  "cdcl\<^sub>W_bj\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl\<^sub>W\<^sup>*\<^sup>* S T"
  using mono_rtranclp[of cdcl\<^sub>W_bj cdcl\<^sub>W] by blast

lemma cdcl\<^sub>W_merge_restart_cdcl\<^sub>W:
  assumes "cdcl\<^sub>W_merge_restart S T"
  shows "cdcl\<^sub>W\<^sup>*\<^sup>* S T"
  using assms
proof induction
  case (fw_r_conflict S T U) note confl = this(1) and bj = this(2)
  have "cdcl\<^sub>W S T" using confl by (simp add: cdcl\<^sub>W.intros r_into_rtranclp)
  moreover
    have "cdcl\<^sub>W_bj\<^sup>*\<^sup>* T U" using bj unfolding full_def by auto
    then have "cdcl\<^sub>W\<^sup>*\<^sup>* T U" using rtranclp_cdcl\<^sub>W_bj_rtranclp_cdcl\<^sub>W by blast
  ultimately show ?case by auto
qed (simp_all add: cdcl\<^sub>W_o.intros cdcl\<^sub>W.intros r_into_rtranclp)

lemma cdcl\<^sub>W_merge_restart_conflicting_true_or_no_step:
  assumes "cdcl\<^sub>W_merge_restart S T"
  shows "conflicting T = None \<or> no_step cdcl\<^sub>W T"
  using assms
proof induction
  case (fw_r_conflict S T U) note confl = this(1) and n_s = this(2)
  { fix D V
    assume "cdcl\<^sub>W U V" and "conflicting U = Some D"
    then have False
      using n_s unfolding full_def
      by (induction rule: cdcl\<^sub>W_all_rules_induct)
        (auto dest!: cdcl\<^sub>W_bj.intros elim: decideE propagateE conflictE forgetE restartE)
  }
  then show ?case by (cases "conflicting U") fastforce+
qed (auto simp add: cdcl\<^sub>W_rf.simps elim: propagateE decideE restartE forgetE)

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

lemmas rulesE =
  skipE resolveE backtrackE propagateE conflictE decideE restartE forgetE

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

lemma backtrack_is_full1_cdcl\<^sub>W_bj:
  assumes bt: "backtrack S T" and inv: "cdcl\<^sub>W_M_level_inv S"
  shows "full1 cdcl\<^sub>W_bj S T"
   using bt inv backtrack_no_cdcl\<^sub>W_bj unfolding full1_def by blast

lemma rtrancl_cdcl\<^sub>W_conflicting_true_cdcl\<^sub>W_merge_restart:
  assumes "cdcl\<^sub>W\<^sup>*\<^sup>* S V" and inv: "cdcl\<^sub>W_M_level_inv S" and "conflicting S = None"
  shows "(cdcl\<^sub>W_merge_restart\<^sup>*\<^sup>* S V \<and> conflicting V = None)
    \<or> (\<exists>T U. cdcl\<^sub>W_merge_restart\<^sup>*\<^sup>* S T \<and> conflicting V \<noteq> None \<and> conflict T U \<and> cdcl\<^sub>W_bj\<^sup>*\<^sup>* U V)"
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
      moreover then have "conflicting U = None" and "conflicting V = None"
        by (auto elim: propagateE)
      ultimately show ?thesis using IH cdcl\<^sub>W_merge_restart.fw_r_propagate[of U V] by auto
    next
      case conflict
      moreover then have "conflicting U = None" and "conflicting V \<noteq> None"
        by (auto elim!: conflictE simp del: state_simp simp: state_eq_def)
      ultimately show ?thesis using IH by auto
    next
      case other
      then show ?thesis
        proof cases
          case decide
          then show ?thesis using IH cdcl\<^sub>W_merge_restart.fw_r_decide[of U V] by (auto elim: decideE)
        next
          case bj
          moreover {
            assume "skip_or_resolve U V"
            have f1: "cdcl\<^sub>W_bj\<^sup>+\<^sup>+ U V"
              by (simp add: local.bj tranclp.r_into_trancl)
            obtain T T' :: 'st where
              f2: "cdcl\<^sub>W_merge_restart\<^sup>*\<^sup>* S U
                \<or> cdcl\<^sub>W_merge_restart\<^sup>*\<^sup>* S T \<and> conflicting U \<noteq> None
                  \<and> conflict T T' \<and> cdcl\<^sub>W_bj\<^sup>*\<^sup>* T' U"
              using IH confl by blast
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
              "cdcl\<^sub>W_merge_restart\<^sup>*\<^sup>* S T" and
              "conflicting U \<noteq> None" and
              "conflict T T'" and
              "cdcl\<^sub>W_bj\<^sup>*\<^sup>* T' U"
              using IH confl by meson
            have invU: "cdcl\<^sub>W_M_level_inv U"
              using inv rtranclp_cdcl\<^sub>W_consistent_inv step.hyps(1) by blast
            then have "conflicting V = None"
              using \<open>backtrack U V\<close> inv by (auto elim: backtrack_levE
                simp: cdcl\<^sub>W_M_level_inv_decomp)
            have "full cdcl\<^sub>W_bj T' V"
              apply (rule rtranclp_fullI[of cdcl\<^sub>W_bj T' U V])
                using \<open>cdcl\<^sub>W_bj\<^sup>*\<^sup>* T' U\<close> apply fast
              using \<open>backtrack U V\<close> backtrack_is_full1_cdcl\<^sub>W_bj invU unfolding full1_def full_def
              by blast
            then have ?thesis
              using cdcl\<^sub>W_merge_restart.fw_r_conflict[of T T' V] \<open>conflict T T'\<close>
              \<open>cdcl\<^sub>W_merge_restart\<^sup>*\<^sup>* S T\<close> \<open>conflicting V = None\<close> by auto
          }
          ultimately show ?thesis by (auto simp: cdcl\<^sub>W_bj.simps)
      qed
    next
      case rf
      moreover then have "conflicting U = None" and "conflicting V = None"
        by (auto simp: cdcl\<^sub>W_rf.simps elim: restartE forgetE)
      ultimately show ?thesis using IH cdcl\<^sub>W_merge_restart.fw_r_rf[of U V] by auto
    qed
qed

lemma no_step_cdcl\<^sub>W_no_step_cdcl\<^sub>W_merge_restart: "no_step cdcl\<^sub>W S \<Longrightarrow> no_step cdcl\<^sub>W_merge_restart S"
  by (auto simp: cdcl\<^sub>W.simps cdcl\<^sub>W_merge_restart.simps cdcl\<^sub>W_o.simps cdcl\<^sub>W_bj.simps)

lemma no_step_cdcl\<^sub>W_merge_restart_no_step_cdcl\<^sub>W:
  assumes
    "conflicting S = None" and
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
    by (auto elim: skipE resolveE backtrackE conflictE decideE restartE)
qed

lemma cdcl\<^sub>W_merge_restart_no_step_cdcl\<^sub>W_bj:
  assumes
    "cdcl\<^sub>W_merge_restart S T"
  shows "no_step cdcl\<^sub>W_bj T"
  using assms
  by (induction rule: cdcl\<^sub>W_merge_restart.induct)
   (force simp: cdcl\<^sub>W_bj.simps cdcl\<^sub>W_rf.simps cdcl\<^sub>W_merge_restart.simps full_def
     elim!: rulesE)+

lemma rtranclp_cdcl\<^sub>W_merge_restart_no_step_cdcl\<^sub>W_bj:
  assumes
    "cdcl\<^sub>W_merge_restart\<^sup>*\<^sup>* S T" and
    "conflicting S = None"
  shows "no_step cdcl\<^sub>W_bj T"
  using assms unfolding rtranclp_unfold
  apply (elim disjE)
   apply (force simp: cdcl\<^sub>W_bj.simps cdcl\<^sub>W_rf.simps elim!: rulesE)
  by (auto simp: tranclp_unfold_end simp: cdcl\<^sub>W_merge_restart_no_step_cdcl\<^sub>W_bj)

text \<open>If @{term "conflicting  S \<noteq> None"}, we cannot say anything.

  Remark that this theorem does  not say anything about well-foundedness: even if you know that one
  relation is well-founded, it only states that the normal forms are shared.
  \<close>
lemma conflicting_true_full_cdcl\<^sub>W_iff_full_cdcl\<^sub>W_merge:
  assumes confl: "conflicting  S = None" and lev: "cdcl\<^sub>W_M_level_inv S"
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
        (fw) "cdcl\<^sub>W_merge_restart\<^sup>*\<^sup>* S V" and "conflicting V = None"
      | (bj) T U where
        "cdcl\<^sub>W_merge_restart\<^sup>*\<^sup>* S T" and
        "conflicting V \<noteq> None" and
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
          using full unfolding full_def by (meson cdcl\<^sub>W_o.bj other)
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
    using bj by (auto simp add: cdcl\<^sub>W_bj.simps cdcl\<^sub>W_cp.simps elim!: rulesE)
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
        using U' by (fastforce simp: cdcl\<^sub>W_cp.simps cdcl\<^sub>W_bj.simps elim: rulesE)
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
    \<or> (\<exists>U' U''. full cdcl\<^sub>W_cp T' U'' \<and> full1 cdcl\<^sub>W_bj U U' \<and> full cdcl\<^sub>W_cp U' U''
      \<and> cdcl\<^sub>W_s'\<^sup>*\<^sup>* U U'')"
  using assms(2,1,3,4)
proof (induction rule: rtranclp_induct)
  case base
  then show ?case by blast
next
  case (step T' T'') note st = this(1) and bj = this(2) and IH = this(3)[OF this(4,5)] and
    full = this(4) and inv = this(5)
  have "cdcl\<^sub>W_bj\<^sup>*\<^sup>* T T''"
    using local.bj st by auto
  then have "cdcl\<^sub>W\<^sup>*\<^sup>* T T''"
    using rtranclp_cdcl\<^sub>W_bj_rtranclp_cdcl\<^sub>W by blast
  then have inv_T'': "cdcl\<^sub>W_all_struct_inv T''"
    using inv rtranclp_cdcl\<^sub>W_all_struct_inv_inv by blast
  have "cdcl\<^sub>W_bj\<^sup>+\<^sup>+ T T''"
    using local.bj st by auto
  have "full1 cdcl\<^sub>W_bj T T''"
    by (metis \<open>cdcl\<^sub>W_bj\<^sup>+\<^sup>+ T T''\<close> full1_def step.prems(3))
  then have "T = U"
    proof -
      obtain Z where "cdcl\<^sub>W_bj T Z"
        using \<open>cdcl\<^sub>W_bj\<^sup>+\<^sup>+ T T''\<close> by (blast dest: tranclpD)
      { assume "cdcl\<^sub>W_cp\<^sup>+\<^sup>+ T U"
        then obtain Z' where "cdcl\<^sub>W_cp T Z'"
          by (meson tranclpD)
        then have False
          using \<open>cdcl\<^sub>W_bj T Z\<close> by (fastforce simp: cdcl\<^sub>W_bj.simps cdcl\<^sub>W_cp.simps
            elim: rulesE)
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
    by (metis local.bj rtranclp.simps rtranclp_cdcl\<^sub>W_bj_rtranclp_cdcl\<^sub>W st)
  then have inv_T'': "cdcl\<^sub>W_all_struct_inv T''"
    using inv rtranclp_cdcl\<^sub>W_all_struct_inv_inv by blast
  have "cdcl\<^sub>W_bj\<^sup>+\<^sup>+ T T''"
    using local.bj st by auto
  have "full1 cdcl\<^sub>W_bj T T''"
    by (metis \<open>cdcl\<^sub>W_bj\<^sup>+\<^sup>+ T T''\<close> full1_def step.prems(3))
  then have "T = U"
    proof -
      obtain Z where "cdcl\<^sub>W_bj T Z"
        using \<open>cdcl\<^sub>W_bj\<^sup>+\<^sup>+ T T''\<close> by (blast dest: tranclpD)
      { assume "cdcl\<^sub>W_cp\<^sup>+\<^sup>+ T U"
        then obtain Z' where "cdcl\<^sub>W_cp T Z'"
          by (meson tranclpD)
        then have False
          using \<open>cdcl\<^sub>W_bj T Z\<close> by (fastforce simp: cdcl\<^sub>W_bj.simps cdcl\<^sub>W_cp.simps elim: rulesE)
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
            by (force dest!: tranclpD simp:cdcl\<^sub>W_bj.simps elim: rulesE)
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
  shows "cdcl\<^sub>W_s'\<^sup>*\<^sup>* S U \<or> (\<exists>T. cdcl\<^sub>W_s'\<^sup>*\<^sup>* S T \<and> cdcl\<^sub>W_bj\<^sup>+\<^sup>+ T U \<and> conflicting U \<noteq> None)"
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
        ssa: "cdcl\<^sub>W_cp T ssa"
        using conflict' by (metis (no_types) full1_def tranclpD)
      have "\<forall>s. \<not> full cdcl\<^sub>W_cp s T"
        by (meson ssa full_def)
      then have "S = T"
        by (metis (full_types) f3 ssa cdcl\<^sub>W_stgy.cases full1_def)
      then show ?thesis
        using f2 by blast
    next
      case (other' U) note o = this(1) and n_s = this(2) and full = this(3)
      then show ?thesis
        using o
        proof (cases rule: cdcl\<^sub>W_o_rule_cases)
          case decide
          then have "cdcl\<^sub>W_s'\<^sup>*\<^sup>* S T"
            using IH by (auto elim: rulesE)
          then show ?thesis
            by (meson decide decide' full n_s rtranclp.rtrancl_into_rtrancl)
        next
          case backtrack
          consider
              (s') "cdcl\<^sub>W_s'\<^sup>*\<^sup>* S T"
            | (bj) S' where "cdcl\<^sub>W_s'\<^sup>*\<^sup>* S S'" and "cdcl\<^sub>W_bj\<^sup>+\<^sup>+ S' T" and "conflicting T \<noteq> None"
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
                using bj_T by (fastforce simp: cdcl\<^sub>W_cp.simps cdcl\<^sub>W_bj.simps dest!: tranclpD
                  elim: rulesE)
              moreover
                have "cdcl\<^sub>W_M_level_inv T"
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
            using full converse_rtranclpE unfolding full_def by (fastforce elim: rulesE)
          then have confl_V: "conflicting V \<noteq> None"
            using skip by (auto elim!: rulesE simp del: state_simp simp: state_eq_def)
          consider
              (s') "cdcl\<^sub>W_s'\<^sup>*\<^sup>* S T"
            | (bj) S' where "cdcl\<^sub>W_s'\<^sup>*\<^sup>* S S'" and "cdcl\<^sub>W_bj\<^sup>+\<^sup>+ S' T" and "conflicting T \<noteq> None"
            using IH by blast
          then show ?thesis
            proof cases
              case s'
              show ?thesis using s' confl_V skip by force
            next
              case (bj S') note S_S' = this(1) and bj_T = this(2)
              have "cdcl\<^sub>W_bj\<^sup>+\<^sup>+ S' V"
                using skip bj_T by (metis \<open>U = V\<close> cdcl\<^sub>W_bj.skip tranclp.simps)
              then show ?thesis using S_S' confl_V by auto
            qed
        next
          case resolve
          then have [simp]: "U = V"
            using full unfolding full_def rtranclp_unfold
            by (auto elim!: rulesE dest!: tranclpD
              simp del: state_simp simp: state_eq_def cdcl\<^sub>W_cp.simps)
          have confl_V: "conflicting V \<noteq> None"
            using resolve by (auto elim!: rulesE simp del: state_simp simp: state_eq_def)

          consider
              (s') "cdcl\<^sub>W_s'\<^sup>*\<^sup>* S T"
            | (bj) S' where "cdcl\<^sub>W_s'\<^sup>*\<^sup>* S S'" and "cdcl\<^sub>W_bj\<^sup>+\<^sup>+ S' T" and "conflicting T \<noteq> None"
            using IH by blast
          then show ?thesis
            proof cases
              case s'
              have "cdcl\<^sub>W_bj\<^sup>+\<^sup>+ T V"
                using resolve by force
              then show ?thesis using s' confl_V by auto
            next
              case (bj S') note S_S' = this(1) and bj_T = this(2)
              have "cdcl\<^sub>W_bj\<^sup>+\<^sup>+ S' V"
                using resolve bj_T by (metis \<open>U = V\<close> cdcl\<^sub>W_bj.resolve tranclp.simps)
              then show ?thesis using confl_V S_S' by auto
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
    | (st) S' where "cdcl\<^sub>W_s'\<^sup>*\<^sup>* S S'" and "cdcl\<^sub>W_bj\<^sup>+\<^sup>+ S' T" and "conflicting T \<noteq> None"
    using rtranclp_cdcl\<^sub>W_stgy_connected_to_rtranclp_cdcl\<^sub>W_s'[of S T] inv \<open>?S\<close>
    unfolding full_def  cdcl\<^sub>W_all_struct_inv_def
    by blast
  then show ?S'
    proof cases
      case s'
      have "no_step cdcl\<^sub>W_s' T"
        using \<open>full cdcl\<^sub>W_stgy S T\<close>  unfolding full_def
        by (meson cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_s'E cdcl\<^sub>W_stgy.conflict'
          cdcl\<^sub>W_then_exists_cdcl\<^sub>W_stgy_step inv_T n_step_cdcl\<^sub>W_stgy_iff_no_step_cdcl\<^sub>W_cl_cdcl\<^sub>W_o)
      then show ?thesis
        using s' unfolding full_def by blast
    next
      case (st S')
      have "full cdcl\<^sub>W_cp T T"
        using option_full_cdcl\<^sub>W_cp st(3) by blast
      moreover
        have n_s: "no_step cdcl\<^sub>W_bj T"
          by (metis \<open>full cdcl\<^sub>W_stgy S T\<close> bj inv_T cdcl\<^sub>W_all_struct_inv_def
            cdcl\<^sub>W_then_exists_cdcl\<^sub>W_stgy_step full_def)
        then have "full1 cdcl\<^sub>W_bj S' T"
          using st(2) unfolding full1_def by blast
      moreover have "no_step cdcl\<^sub>W_cp S'"
        using st(2) by (fastforce dest!: tranclpD simp: cdcl\<^sub>W_cp.simps cdcl\<^sub>W_bj.simps
          elim: rulesE)
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

lemma rtranclp_cdcl\<^sub>W_cp_conflicting_Some:
  "cdcl\<^sub>W_cp\<^sup>*\<^sup>* S T \<Longrightarrow> conflicting S = Some D \<Longrightarrow> S = T"
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
  unfolding full1_def by (metis rtranclp_unfold cdcl\<^sub>W_cp_conflicting_not_empty option.exhaust
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
    "conflicting S = None"
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
    confl: "conflicting S = None"
  shows
    "(cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* S V \<and> conflicting V = None)
    \<or> (cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* S V \<and> conflicting V \<noteq> None \<and> no_step cdcl\<^sub>W_cp V \<and> no_step cdcl\<^sub>W_bj V)
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
      then have "conflicting U = None"
        using tranclp_cdcl\<^sub>W_cp_propagate_with_conflict_or_not[of U V]
        conflict by (auto dest!: tranclpD simp: rtranclp_unfold elim: rulesE)
      then have "cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* S U" using IH by (auto elim: rulesE
        simp del: state_simp simp: state_eq_def)
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
          moreover have "conflicting V = None"
            using propa unfolding tranclp_unfold_end by (auto elim: rulesE)
          ultimately show ?thesis using \<open>cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* S U\<close> by (auto elim!: rulesE
            simp del: state_simp simp: state_eq_def)
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
      then have "conflicting U \<noteq> None"
        using full_bj unfolding full1_def by (fastforce dest!: tranclpD simp: cdcl\<^sub>W_bj.simps
          elim: rulesE)
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
          moreover have "conflicting V = None"
            using propa unfolding tranclp_unfold_end by (auto elim: rulesE)
          ultimately show ?thesis using S_U' by (auto elim: rulesE
            simp del: state_simp simp: state_eq_def)
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
            using S_U' apply (cases "conflicting V = None")
             using full_bj apply simp
            by (metis cp full_def full_unfold full_bj)
        qed
    qed
qed

lemma no_step_cdcl\<^sub>W_s'_no_ste_cdcl\<^sub>W_merge_cp:
  assumes
    "cdcl\<^sub>W_all_struct_inv S"
    "conflicting S = None"
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
    confl: "conflicting S = None" and
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
        using confl unfolding full1_def by (fastforce simp: cdcl\<^sub>W_bj.simps dest: tranclpD
          elim: rulesE)
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
    "conflicting S = None" and
    "cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* S T"
  shows "no_step cdcl\<^sub>W_bj T"
  using assms(2,1) by (induction)
  (fastforce simp: cdcl\<^sub>W_merge_cp.simps full_def tranclp_unfold_end cdcl\<^sub>W_bj.simps
    elim: rulesE)+

lemma conflicting_true_full_cdcl\<^sub>W_merge_cp_iff_full_cdcl\<^sub>W_s'_without_decode:
  assumes
    confl: "conflicting S = None" and
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
        using bj unfolding full1_def by (fastforce dest!: tranclpD simp:cdcl\<^sub>W_bj.simps elim: rulesE)
      ultimately have "cdcl\<^sub>W_s'_without_decide T V"
        using bj'_without_decide[of T U V] bj by blast
      then show ?thesis using s' by auto
    qed
  moreover have "no_step cdcl\<^sub>W_s'_without_decide V"
    proof (cases "conflicting V = None")
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
          using False by (metis option_full_cdcl\<^sub>W_cp full_def)
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
          unfolding cdcl\<^sub>W_all_struct_inv_def by simp
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
      (cp_true) "cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* S V" and "conflicting V = None"
    | (cp_false) "cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* S V" and "conflicting V \<noteq> None" and "no_step cdcl\<^sub>W_cp V" and
         "no_step cdcl\<^sub>W_bj V"
    | (cp_confl) T where "cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* S T" "conflict T V"
    using rtranclp_cdcl\<^sub>W_s'_without_decide_is_rtranclp_cdcl\<^sub>W_merge_cp[of S V] confl
    unfolding full_def by meson
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
    confl: "conflicting S = None" and
    inv: "cdcl\<^sub>W_all_struct_inv S"
  shows
    "full1 cdcl\<^sub>W_merge_cp S V \<longleftrightarrow> full1 cdcl\<^sub>W_s'_without_decide S V"
proof -
  have "full cdcl\<^sub>W_merge_cp S V = full cdcl\<^sub>W_s'_without_decide S V"
    using confl conflicting_true_full_cdcl\<^sub>W_merge_cp_iff_full_cdcl\<^sub>W_s'_without_decode inv
    by simp
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
  have "conflicting S = None"
    using fw unfolding full1_def by (auto dest!: tranclpD simp: cdcl\<^sub>W_merge_cp.simps elim: rulesE)
  then show ?thesis
    using conflicting_true_full1_cdcl\<^sub>W_merge_cp_iff_full1_cdcl\<^sub>W_s'_without_decode fw inv by simp
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

lemma cdcl\<^sub>W_merge_stgy_cases[consumes 1, case_names fw_s_cp fw_s_decide]:
  assumes
    "cdcl\<^sub>W_merge_stgy S U"
    "full1 cdcl\<^sub>W_merge_cp S U \<Longrightarrow> P"
    "\<And>T. decide S T \<Longrightarrow> no_step cdcl\<^sub>W_merge_cp S \<Longrightarrow> full cdcl\<^sub>W_merge_cp T U \<Longrightarrow> P"
  shows "P"
  using assms by (auto simp: cdcl\<^sub>W_merge_stgy.simps)

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
  assumes "no_step cdcl\<^sub>W_cp S" and "conflicting S = None" and inv: "cdcl\<^sub>W_M_level_inv S"
  shows "no_step cdcl\<^sub>W_s'_without_decide S"
  by (metis assms cdcl\<^sub>W_cp.conflict' cdcl\<^sub>W_cp.propagate' cdcl\<^sub>W_merge_restart_cases tranclpD
    conflicting_true_no_step_cdcl\<^sub>W_merge_cp_no_step_s'_without_decide)

lemma no_step_cdcl\<^sub>W_cp_no_step_cdcl\<^sub>W_merge_restart:
  assumes "no_step cdcl\<^sub>W_cp S" and "conflicting S = None"
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
      unfolding full1_def by blast
    then have "cdcl\<^sub>W_all_struct_inv T'"
      using inv  rtranclp_cdcl\<^sub>W_all_struct_inv_inv by blast
    then obtain U where "full cdcl\<^sub>W_cp T' U"
      using cdcl\<^sub>W_cp_normalized_element_all_inv by blast
  moreover have "no_step cdcl\<^sub>W_cp S"
    using S_T by (auto simp: cdcl\<^sub>W_bj.simps elim: rulesE)
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
    "conflicting R = None" and
    inv: "cdcl\<^sub>W_all_struct_inv R"
  shows "(cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* R V \<and> conflicting V = None)
  \<or> (cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* R V \<and> conflicting V \<noteq> None \<and> no_step cdcl\<^sub>W_bj V)
  \<or> (\<exists>S T U. cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* R S \<and> no_step cdcl\<^sub>W_merge_cp S \<and> decide S T
    \<and> cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* T U \<and> conflict U V)
  \<or> (\<exists>S T. cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* R S \<and> no_step cdcl\<^sub>W_merge_cp S \<and> decide S T
    \<and> cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* T V
      \<and> conflicting V = None)
  \<or> (cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* R V \<and> conflicting V = None)
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
            and "cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* T V" and "conflicting V = None"
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
            | (propa) "propagate\<^sup>+\<^sup>+ V W" and "conflicting W = None"
            | (propa_confl) V' where "propagate\<^sup>*\<^sup>* V V'" and "conflict V' W"
            using tranclp_cdcl\<^sub>W_cp_propagate_with_conflict_or_not[of V W] conflict'
            unfolding full_unfold full1_def by meson
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
                  by (metis rtranclp_unfold cdcl\<^sub>W_merge_cp.propagate' r_into_rtranclp)
              ultimately show ?thesis using s' \<open>R = V\<close> by blast
            qed
        next
          case dec_confl note _ = this(5)
          then have False using conflict' unfolding full1_def by (auto dest!: tranclpD elim: rulesE)
          then show ?thesis by fast
        next
          case dec note T_V = this(4)
          consider
              (propa) "propagate\<^sup>+\<^sup>+ V W" and "conflicting W = None"
            | (propa_confl) V' where "propagate\<^sup>*\<^sup>* V V'" and "conflict V' W"
            using tranclp_cdcl\<^sub>W_cp_propagate_with_conflict_or_not[of V W] conflict'
            unfolding full1_def by meson
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
              (propa) "propagate\<^sup>+\<^sup>+ V W" and "conflicting W = None"
            | (propa_confl) V' where "propagate\<^sup>*\<^sup>* V V'" and "conflict V' W"
            using tranclp_cdcl\<^sub>W_cp_propagate_with_conflict_or_not[of V W] conflict'
            unfolding full1_def by meson
          then show ?thesis
            proof cases
              case propa
              then show ?thesis by (meson cdcl\<^sub>W_merge_cp.propagate' cp
                rtranclp.rtrancl_into_rtrancl)
            next
              case propa_confl
              then show ?thesis
                using propa_confl(2) cp
                by (metis (full_types) cdcl\<^sub>W_merge_cp.propagate' rtranclp.rtrancl_into_rtrancl
                  rtranclp_unfold)
            qed
        next
          case cp_confl
          then show ?thesis using conflict' unfolding full1_def by (fastforce dest!: tranclpD
            elim!: rulesE)
        qed
    next
      case (decide' V')
      then have conf_V: "conflicting V = None"
        by (auto elim: rulesE)
      consider
         (s') "cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* R V"
        | (dec_confl) S T U where "cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* R S" and "no_step cdcl\<^sub>W_merge_cp S" and
            "decide S T" and "cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* T U" and "conflict U V"
        | (dec) S T where "cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* R S" and "no_step cdcl\<^sub>W_merge_cp S" and "decide S T"
             and "cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* T V" and "conflicting V = None"
        | (cp) "cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* R V"
        | (cp_confl) U where "cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* R U" and "conflict U V"
        using IH by meson
      then show ?thesis
        proof cases
          case s'
          have confl_V': "conflicting V' = None" using decide'(1) by (auto elim: rulesE)
          have full: "full1 cdcl\<^sub>W_cp V' W \<or> (V' = W \<and> no_step cdcl\<^sub>W_cp W)"
            using decide'(3) unfolding full_unfold by blast
          consider
              (V'_W) "V' = W"
            | (propa) "propagate\<^sup>+\<^sup>+ V' W" and "conflicting W = None"
            | (propa_confl) V'' where "propagate\<^sup>*\<^sup>* V' V''" and "conflict V'' W"
            using tranclp_cdcl\<^sub>W_cp_propagate_with_conflict_or_not[of V W] decide'
            by (metis \<open>full1 cdcl\<^sub>W_cp V' W \<or> V' = W \<and> no_step cdcl\<^sub>W_cp W\<close> full1_def
              tranclp_cdcl\<^sub>W_cp_propagate_with_conflict_or_not)
          then show ?thesis (* too many levels of case distinction *)
            proof cases
              case V'_W
              then show ?thesis
                using confl_V' local.decide'(1,2) s' conf_V
                no_step_cdcl\<^sub>W_cp_no_step_cdcl\<^sub>W_merge_restart[of V] by (auto elim: rulesE)
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
            | (propa) "propagate\<^sup>+\<^sup>+ V' W" and "conflicting W = None"
            | (propa_confl) V'' where "propagate\<^sup>*\<^sup>* V' V''" and "conflict V'' W"
            using tranclp_cdcl\<^sub>W_cp_propagate_with_conflict_or_not[of V' W] decide'
            unfolding full_unfold full1_def by meson
          then show ?thesis (* too many levels of case distinction *)
            proof cases
              case V'_W
              moreover have "conflicting V' = None"
                using decide'(1) by (auto elim: rulesE)
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
            using conf_V local.decide'(2) no_step_cdcl\<^sub>W_cp_no_step_cdcl\<^sub>W_merge_restart by auto
          then have "full cdcl\<^sub>W_merge_cp R V"
            unfolding full_def using cp by fast
          then have "cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* R V"
            unfolding full_unfold by auto
          have "full1 cdcl\<^sub>W_cp V' W \<or> (V' = W \<and> no_step cdcl\<^sub>W_cp W)"
            using decide'(3) unfolding full_unfold by blast

          consider
              (V'_W) "V' = W"
            | (propa) "propagate\<^sup>+\<^sup>+ V' W" and "conflicting W = None"
            | (propa_confl) V'' where "propagate\<^sup>*\<^sup>* V' V''" and "conflict V'' W"
            using tranclp_cdcl\<^sub>W_cp_propagate_with_conflict_or_not[of V' W] decide'
            unfolding full_unfold full1_def by meson
          then show ?thesis (* too many levels of case distinction *)
          (* copy paste. copy paste, copy paste *)
            proof cases
              case V'_W
              moreover have "conflicting V' = None"
                using decide'(1) by (auto elim: rulesE)
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
          show ?thesis using conf_V dec_confl(5) by (auto elim!: rulesE
            simp del: state_simp simp: state_eq_def)
        next
          case cp_confl
          then show ?thesis using decide' apply - by (intro HOL.disjI2) (fastforce elim: rulesE
            simp del: state_simp simp: state_eq_def)
      qed
    next
      case (bj' V')
      then have "\<not>no_step cdcl\<^sub>W_bj V "
        by (auto dest: tranclpD simp: full1_def)
      then consider
         (s') "cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* R V" and "conflicting V = None"
        | (dec_confl) S T U where "cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* R S" and "no_step cdcl\<^sub>W_merge_cp S" and
            "decide S T" and "cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* T U" and "conflict U V"
        | (dec) S T where "cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* R S" and "no_step cdcl\<^sub>W_merge_cp S" and "decide S T"
            and "cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* T V" and "conflicting V = None"
        | (cp) "cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* R V" and "conflicting V = None"
        | (cp_confl) U where "cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* R U" and "conflict U V"
        using IH by meson
      then show ?thesis
        proof cases
          case s' note _ =this(2)
          then have False
            using bj'(1) unfolding full1_def by (force dest!: tranclpD simp: cdcl\<^sub>W_bj.simps
              elim: rulesE)
          then show ?thesis by fast
        next
          case dec note _ = this(5)
          then have False
            using bj'(1) unfolding full1_def by (force dest!: tranclpD simp: cdcl\<^sub>W_bj.simps
              elim: rulesE)
          then show ?thesis by fast
        next
          case dec_confl
          then have "cdcl\<^sub>W_merge_cp U V'"
            using bj' cdcl\<^sub>W_merge_cp.intros(1)[of U V V'] by (simp add: full_unfold)
          then have "cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* T V'"
            using dec_confl(4) by simp
          consider
              (V'_W) "V' = W"
            | (propa) "propagate\<^sup>+\<^sup>+ V' W" and "conflicting W = None"
            | (propa_confl) V'' where "propagate\<^sup>*\<^sup>* V' V''" and "conflict V'' W"
            using tranclp_cdcl\<^sub>W_cp_propagate_with_conflict_or_not[of V' W] bj'(3)
            unfolding full_unfold full1_def by meson
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
                  assume "conflicting W = None"
                  then show ?thesis using \<open>cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* R V'\<close> \<open>V' = W\<close> by auto
                next
                  assume "conflicting W \<noteq> None"
                  then show ?thesis
                    using \<open>cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* R V'\<close> \<open>V' = W\<close> by (metis \<open>cdcl\<^sub>W_merge_cp U V'\<close>
                      conflictE conflicting_not_true_rtranclp_cdcl\<^sub>W_merge_cp_no_step_cdcl\<^sub>W_bj
                      dec_confl(5) map_option_is_None r_into_rtranclp)
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
            | (propa) "propagate\<^sup>+\<^sup>+ V' W" and "conflicting W = None"
            | (propa_confl) V'' where "propagate\<^sup>*\<^sup>* V' V''" and "conflict V'' W"
            using tranclp_cdcl\<^sub>W_cp_propagate_with_conflict_or_not[of V' W] bj'
            unfolding full_unfold full1_def by meson
          then show ?thesis (* too many levels of case distinction *)
          (* copy paste. copy paste, copy paste *)
            proof cases
              case V'_W
              show ?thesis
                proof cases
                  assume "conflicting V' = None"
                  then show ?thesis
                    using V'_W \<open>cdcl\<^sub>W_merge_cp U V'\<close> cp_confl(1) by force
                next
                  assume confl: "conflicting V' \<noteq> None"
                  then have "no_step cdcl\<^sub>W_merge_stgy V'"
                    by (fastforce simp: cdcl\<^sub>W_merge_stgy.simps full1_def full_def
                      cdcl\<^sub>W_merge_cp.simps dest!: tranclpD elim: rulesE)
                  have "no_step cdcl\<^sub>W_merge_cp V'"
                    using confl by (auto simp: full1_def full_def cdcl\<^sub>W_merge_cp.simps
                    dest!: tranclpD elim: rulesE)
                  moreover have "cdcl\<^sub>W_merge_cp U W"
                    using V'_W \<open>cdcl\<^sub>W_merge_cp U V'\<close> by blast
                  ultimately have "full1 cdcl\<^sub>W_merge_cp R V'"
                    using cp_confl(1) V'_W unfolding full1_def by auto
                  then have "cdcl\<^sub>W_merge_stgy R V'"
                    by auto
                  moreover have "no_step cdcl\<^sub>W_merge_stgy V'"
                    using confl \<open>no_step cdcl\<^sub>W_merge_cp V'\<close> by (auto simp: cdcl\<^sub>W_merge_stgy.simps
                      full1_def dest!: tranclpD elim: rulesE)
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
          assume a1: "T = U"
          then have f2: "cdcl\<^sub>W_s' T V"
            using s' by force
          obtain ss :: 'st where
            ss: "cdcl\<^sub>W_s'\<^sup>*\<^sup>* S T \<or> cdcl\<^sub>W_cp T ss"
            using a1 step.IH by blast-
          obtain ssa :: "'st \<Rightarrow> 'st" where
            f3: "\<forall>s sa sb. (\<not> decide s sa \<or> cdcl\<^sub>W_cp s (ssa s) \<or> \<not> full cdcl\<^sub>W_cp sa sb)
              \<or> cdcl\<^sub>W_s' s sb"
            using cdcl\<^sub>W_s'.decide' by moura
          have "\<forall>s sa. \<not> cdcl\<^sub>W_s' s sa \<or> full1 cdcl\<^sub>W_cp s sa \<or>
            (\<exists>sb. decide s sb \<and> no_step cdcl\<^sub>W_cp s \<and> full cdcl\<^sub>W_cp sb sa) \<or>
            (\<exists>sb. full1 cdcl\<^sub>W_bj s sb \<and> no_step cdcl\<^sub>W_cp s \<and> full cdcl\<^sub>W_cp sb sa)"
            by (metis cdcl\<^sub>W_s'E)
          then have "\<exists>s. cdcl\<^sub>W_s'\<^sup>*\<^sup>* S s \<and> cdcl\<^sub>W_s' s V"
            using f3 ss f2 by (metis dec full1_is_full n_s_S rtranclp_unfold)
          then show ?thesis
            by force
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
            using dec unfolding full1_def by (fastforce dest!: tranclpD simp: cdcl\<^sub>W_bj.simps
              elim: rulesE)
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
            using f5 by (metis cdcl\<^sub>W_cp.conflict' cdcl\<^sub>W_cp.propagate' cdcl\<^sub>W_merge_cp.cases f3 f4 inv
              rtranclp_cdcl\<^sub>W_merge_stgy'_no_step_cdcl\<^sub>W_cp_or_eq st)
          then show ?thesis
            using f2 a1 by (metis (no_types) \<open>cdcl\<^sub>W_all_struct_inv S\<close>
              conflicting_true_full1_cdcl\<^sub>W_merge_cp_imp_full1_cdcl\<^sub>W_s'_without_decode
              rtranclp_cdcl\<^sub>W_s'_without_decide_rtranclp_cdcl\<^sub>W_s' rtranclp_unfold)
        qed
    next
      case (fw_s_decide S') note dec = this(1) and n_S = this(2) and full = this(3)
      moreover then have "conflicting S' = None"
        by (auto elim: rulesE)
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
    then have "\<not> full1 cdcl\<^sub>W_s'_without_decide R ss"
      by (simp add: full1_def)
    then have "\<not> cdcl\<^sub>W_merge_stgy R ss"
      using ff4 ff1 conflicting_true_full1_cdcl\<^sub>W_merge_cp_imp_full1_cdcl\<^sub>W_s'_without_decode inv
      by blast }
  then show ?thesis
    by fastforce
qed
end

text \<open>We will discharge the assumption later\<close>
locale conflict_driven_clause_learning\<^sub>W_termination =
  conflict_driven_clause_learning\<^sub>W +
  assumes wf_cdcl\<^sub>W_merge: "wf {(T, S). cdcl\<^sub>W_all_struct_inv S \<and> cdcl\<^sub>W_merge S T}"
begin

lemma wf_tranclp_cdcl\<^sub>W_merge: "wf {(T, S). cdcl\<^sub>W_all_struct_inv S \<and> cdcl\<^sub>W_merge\<^sup>+\<^sup>+ S T}"
  using wf_trancl[OF wf_cdcl\<^sub>W_merge]
  apply (rule wf_subset)
  by (auto simp: trancl_set_tranclp
    cdcl\<^sub>W_all_struct_inv_tranclp_cdcl\<^sub>W_merge_tranclp_cdcl\<^sub>W_merge_cdcl\<^sub>W_all_struct_inv)

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
    confl: "conflicting R = None" and
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
        unfolding cdcl\<^sub>W_all_struct_inv_def by auto
    qed
qed

lemma rtranclp_cdcl\<^sub>W_merge_cp_no_step_cdcl\<^sub>W_bj:
  assumes "conflicting R = None" and "cdcl\<^sub>W_merge_cp\<^sup>*\<^sup>* R S"
  shows "no_step cdcl\<^sub>W_bj S"
  using assms conflicting_not_true_rtranclp_cdcl\<^sub>W_merge_cp_no_step_cdcl\<^sub>W_bj by auto

lemma rtranclp_cdcl\<^sub>W_merge_stgy_no_step_cdcl\<^sub>W_bj:
  assumes confl: "conflicting R = None" and "cdcl\<^sub>W_merge_stgy\<^sup>*\<^sup>* R S"
  shows "no_step cdcl\<^sub>W_bj S"
  using assms(2)
proof induction
  case base
  then show ?case
    using confl by (auto simp: cdcl\<^sub>W_bj.simps elim: rulesE)
next
  case (step S T) note st = this(1) and fw = this(2) and IH = this(3)
  have confl_S: "conflicting S = None"
    using fw apply cases
    by (auto simp: full1_def cdcl\<^sub>W_merge_cp.simps dest!: tranclpD elim: rulesE)
  from fw show ?case
    proof cases
      case fw_s_cp
      then show ?thesis
        using rtranclp_cdcl\<^sub>W_merge_cp_no_step_cdcl\<^sub>W_bj confl_S
        by (simp add: full1_def tranclp_into_rtranclp)
    next
      case (fw_s_decide S')
      moreover then have "conflicting S' = None" by (auto elim: rulesE)
      ultimately show ?thesis
        using conflicting_not_true_rtranclp_cdcl\<^sub>W_merge_cp_no_step_cdcl\<^sub>W_bj
        unfolding full_def by meson
    qed
qed

end

end
