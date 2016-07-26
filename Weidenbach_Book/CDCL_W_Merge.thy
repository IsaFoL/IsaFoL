(* Title: Merging some rules of Weidenbach's CDCL
    Author: Mathias Fleury <mathias.fleury@mpi-inf.mpg.de>
*)

section \<open>Merging backjump rules\<close>

theory CDCL_W_Merge
imports CDCL_W
begin

text \<open>Before showing that Weidenbach's CDCL is included in NOT's CDCL, we need to work on a variant
  of Weidenbach's calculus: NOT's backjump assumes the existence of a clause that is suitable to
  backjump. This clause is obtained in W's CDCL by applying:
    \<^enum> @{term conflict_driven_clause_learning\<^sub>W.conflict} to find the conflict
    \<^enum> the conflict is analysed by repetitive application of
      @{term conflict_driven_clause_learning\<^sub>W.resolve} and
      @{term conflict_driven_clause_learning\<^sub>W.skip},
    \<^enum> finally @{term conflict_driven_clause_learning\<^sub>W.backtrack} is used to backtrack.

  We show that this new calculus has the same final states than Weidenbach's CDCL if the calculus
  starts in a state such that the invariant holds and no conflict has been found yet. The latter
  condition holds for initial states.\<close>

subsection \<open>Inclusion of the states\<close>

context conflict_driven_clause_learning\<^sub>W
begin
declare cdcl\<^sub>W_restart.intros[intro] cdcl\<^sub>W_bj.intros[intro] cdcl\<^sub>W_o.intros[intro]
state_prop [simp del]

lemma backtrack_no_cdcl\<^sub>W_bj:
  assumes cdcl: "cdcl\<^sub>W_bj T U"
  shows "\<not>backtrack V T"
  using cdcl
  apply (induction rule: cdcl\<^sub>W_bj.induct)
    apply (elim skipE, force elim!: backtrackE simp: cdcl\<^sub>W_M_level_inv_def)
   apply (elim resolveE, force elim!: backtrackE simp: cdcl\<^sub>W_M_level_inv_def)
  apply standard
  apply (elim backtrackE)
  apply (force simp add: cdcl\<^sub>W_M_level_inv_decomp)
  done

text \<open>@{term skip_or_resolve} corresponds to the \<^emph>\<open>analyze\<close> function in the code of MiniSAT.\<close>
inductive skip_or_resolve :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
s_or_r_skip[intro]: "skip S T \<Longrightarrow> skip_or_resolve S T" |
s_or_r_resolve[intro]: "resolve S T \<Longrightarrow> skip_or_resolve S T"

lemma rtranclp_cdcl\<^sub>W_bj_skip_or_resolve_backtrack:
  assumes "cdcl\<^sub>W_bj\<^sup>*\<^sup>* S U"
  shows "skip_or_resolve\<^sup>*\<^sup>* S U \<or> (\<exists>T. skip_or_resolve\<^sup>*\<^sup>* S T \<and> backtrack T U)"
  using assms
proof (induction)
  case base
  then show ?case by simp
next
  case (step U V) note st = this(1) and bj = this(2) and IH = this(3)
  consider
      (SU) "S = U"
    | (SUp) "cdcl\<^sub>W_bj\<^sup>+\<^sup>+ S U"
    using st unfolding rtranclp_unfold by blast
  then show ?case
    proof cases
      case SUp
      have "\<And>T. skip_or_resolve\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl\<^sub>W_restart\<^sup>*\<^sup>* S T"
        using mono_rtranclp[of skip_or_resolve cdcl\<^sub>W_restart]
        by (blast intro: skip_or_resolve.cases)
      then have "skip_or_resolve\<^sup>*\<^sup>* S U"
        using bj IH backtrack_no_cdcl\<^sub>W_bj by meson
      then show ?thesis
        using bj by (auto simp: cdcl\<^sub>W_bj.simps dest!: skip_or_resolve.intros)
    next
      case SU
      then show ?thesis
        using bj by (auto simp: cdcl\<^sub>W_bj.simps dest!: skip_or_resolve.intros)
    qed
qed

lemma rtranclp_skip_or_resolve_rtranclp_cdcl\<^sub>W_restart:
  "skip_or_resolve\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl\<^sub>W_restart\<^sup>*\<^sup>* S T"
  by (induction rule: rtranclp_induct)
  (auto dest!: cdcl\<^sub>W_bj.intros cdcl\<^sub>W_restart.intros cdcl\<^sub>W_o.intros simp: skip_or_resolve.simps
    simp del: state_prop)

definition backjump_l_cond :: "'v clause \<Rightarrow> 'v clause \<Rightarrow> 'v literal \<Rightarrow> 'st \<Rightarrow> 'st \<Rightarrow> bool" where
"backjump_l_cond \<equiv> \<lambda>C C' L S T. True"

lemma wf_skip_or_resolve:
  "wf {(T, S). skip_or_resolve S T}"
proof -
  have " skip_or_resolve x y \<Longrightarrow> length (trail y) < length (trail x)" for x y
    by (auto simp: skip_or_resolve.simps elim!: skipE resolveE)
  then show ?thesis
    using wfP_if_measure[of "\<lambda>_. True" skip_or_resolve "\<lambda>S. length (trail S)"]
    by meson
qed

definition inv\<^sub>N\<^sub>O\<^sub>T :: "'st \<Rightarrow> bool" where
"inv\<^sub>N\<^sub>O\<^sub>T \<equiv> \<lambda>S. no_dup (trail S)"

declare inv\<^sub>N\<^sub>O\<^sub>T_def[simp]
end

context conflict_driven_clause_learning\<^sub>W
begin

subsection \<open>More lemmas conflict--propagate and backjumping\<close>
subsubsection \<open>Termination\<close>

lemma cdcl\<^sub>W_bj_measure:
  assumes "cdcl\<^sub>W_bj S T"
  shows "length (trail S) + (if conflicting S = None then 0 else 1)
    > length (trail T) + (if conflicting T = None then 0 else 1)"
  using assms by (induction rule: cdcl\<^sub>W_bj.induct) (force elim!: backtrackE skipE resolveE)+

lemma wf_cdcl\<^sub>W_bj:
  "wf {(b,a). cdcl\<^sub>W_bj a b}"
  apply (rule wfP_if_measure[of "\<lambda>_. True"
      _ "\<lambda>T. length (trail T) + (if conflicting T = None then 0 else 1)", simplified])
  using cdcl\<^sub>W_bj_measure by simp

lemma cdcl\<^sub>W_bj_exists_normal_form:
  shows "\<exists>T. full cdcl\<^sub>W_bj S T"
  using wf_exists_normal_form_full[OF wf_cdcl\<^sub>W_bj] .

lemma rtranclp_skip_state_decomp:
  assumes "skip\<^sup>*\<^sup>* S T"
  shows
    "\<exists>M. trail S = M @ trail T \<and> (\<forall>m\<in>set M. \<not>is_decided m)"
    "init_clss S = init_clss T"
    "learned_clss S = learned_clss T"
    "backtrack_lvl S = backtrack_lvl T"
    "conflicting S = conflicting T"
  using assms by (induction rule: rtranclp_induct) (auto elim!: skipE)


subsubsection \<open>Analysing is confluent\<close>

lemma backtrack_reduce_trail_to_state_eq:
  assumes
    V_T: \<open>V \<sim> tl_trail T\<close> and
    decomp: \<open>(Decided K # M1, M2) \<in> set (get_all_ann_decomposition (trail V))\<close>
  shows \<open>reduce_trail_to M1 (add_learned_cls E (update_backtrack_lvl i (update_conflicting None V)))
    \<sim> reduce_trail_to M1 (add_learned_cls E (update_backtrack_lvl i (update_conflicting None T)))\<close>
proof -
  let ?f = \<open>\<lambda>T. add_learned_cls E (update_backtrack_lvl i (update_conflicting None T))\<close>
  have [simp]: \<open>length (trail T) \<noteq> length M1\<close> \<open>trail T \<noteq> []\<close>
    using decomp V_T by (cases \<open>trail T\<close>; auto)+
  have \<open>reduce_trail_to M1 (?f V) \<sim> reduce_trail_to M1 (?f (tl_trail T))\<close>
    apply (rule reduce_trail_to_state_eq)
    using V_T by (simp_all add: add_learned_cls_state_eq
        update_backtrack_lvl_state_eq update_conflicting_state_eq)
  moreover {
    have \<open>add_learned_cls E (update_backtrack_lvl i (update_conflicting None (tl_trail T))) \<sim>
      tl_trail (add_learned_cls E (update_backtrack_lvl i (update_conflicting None T)))\<close>
      apply (rule state_eq_trans[OF state_eq_sym[THEN iffD1], of
            \<open>add_learned_cls E (update_backtrack_lvl i (tl_trail (update_conflicting None T)))\<close>])
       apply (auto simp: tl_trail_update_conflicting tl_trail_update_backtrack_lvl
          tl_trail_add_learned_cls_commute update_conflicting_state_eq
          update_backtrack_lvl_state_eq add_learned_cls_state_eq
          tl_trail_state_eq; fail)[]
      apply (rule state_eq_trans[OF state_eq_sym[THEN iffD1], of
            \<open>add_learned_cls E (tl_trail (update_backtrack_lvl i (update_conflicting None T)))\<close>])
       apply (auto simp: tl_trail_update_conflicting tl_trail_update_backtrack_lvl
          tl_trail_add_learned_cls_commute update_conflicting_state_eq
          update_backtrack_lvl_state_eq add_learned_cls_state_eq
          tl_trail_state_eq; fail)[]
      apply (rule state_eq_trans[OF state_eq_sym[THEN iffD1], of
            \<open>tl_trail (add_learned_cls E (update_backtrack_lvl i (update_conflicting None T)))\<close>])
       apply (auto simp: tl_trail_update_conflicting tl_trail_update_backtrack_lvl
          tl_trail_add_learned_cls_commute update_conflicting_state_eq
          update_backtrack_lvl_state_eq add_learned_cls_state_eq
          tl_trail_state_eq)
      done
    note _ = reduce_trail_to_state_eq[OF this, of M1 M1]}
  ultimately show \<open>reduce_trail_to M1 (?f V) \<sim> reduce_trail_to M1 (?f T)\<close>
    by (subst (2) reduce_trail_to.simps)
      (auto simp: tl_trail_update_conflicting tl_trail_update_backtrack_lvl
        tl_trail_add_learned_cls_commute intro: state_eq_trans)
qed

lemma rtranclp_skip_backtrack_reduce_trail_to_state_eq:
  assumes
    V_T: \<open>skip\<^sup>*\<^sup>* T V\<close> and
    decomp: \<open>(Decided K # M1, M2) \<in> set (get_all_ann_decomposition (trail V))\<close>
  shows \<open>reduce_trail_to M1 (add_learned_cls E (update_backtrack_lvl i (update_conflicting None T)))
    \<sim> reduce_trail_to M1 (add_learned_cls E (update_backtrack_lvl i (update_conflicting None V)))\<close>
  using V_T decomp
proof (induction arbitrary: M2 rule: rtranclp_induct)
  case base
  then show ?case by auto
next
  case (step U V) note st = this(1) and skip = this(2) and IH = this(3) and decomp = this(4)
  obtain M2' where
    decomp': \<open>(Decided K # M1, M2') \<in> set (get_all_ann_decomposition (trail U))\<close>
    using get_all_ann_decomposition_exists_prepend[OF decomp] skip
    by atomize (auto elim!: rulesE simp del: get_all_ann_decomposition.simps
        simp: Decided_cons_in_get_all_ann_decomposition_append_Decided_cons
        append_Cons[symmetric] append_assoc[symmetric]
        simp del: append_Cons append_assoc)
  show ?case
    using backtrack_reduce_trail_to_state_eq[OF _ decomp, of U E i] skip IH[OF decomp']
    by (auto elim!: skipE simp del: get_all_ann_decomposition.simps intro: state_eq_trans')
qed

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
    using rtranclp_mono[of skip cdcl\<^sub>W_restart] assms(3) rtranclp_cdcl\<^sub>W_all_struct_inv_inv mono_rtranclp
    by (auto dest!: bj other cdcl\<^sub>W_bj.skip)
  then have "cdcl\<^sub>W_M_level_inv V"
    unfolding cdcl\<^sub>W_all_struct_inv_def by auto
  then obtain K i M1 M2 L D where
    conf: "conflicting V = Some D" and
    LD: "L \<in># D" and
    decomp: "(Decided K # M1, M2) \<in> set (get_all_ann_decomposition (trail V))" and
    lev_L: "get_level (trail V) L = backtrack_lvl V" and
    max: "get_level (trail V) L = get_maximum_level (trail V) D" and
    max_D: "get_maximum_level (trail V) (remove1_mset L D) \<equiv> i" and
    lev_k: "get_level (trail V) K = Suc i" and
    W: "W \<sim> cons_trail (Propagated L D)
                (reduce_trail_to M1
                  (add_learned_cls D
                    (update_backtrack_lvl i
                      (update_conflicting None V))))"
  using bt inv by (elim backtrackE) metis+
  obtain L' C' M E where
    tr: "trail T = Propagated L' C' # M" and
    raw: "conflicting T = Some E" and
    LE: "-L' \<notin># E" and
    E: "E \<noteq> {#}" and
    V: "V \<sim> tl_trail T"
    using skip by (elim skipE) metis
  let ?M = "Propagated L' C' # trail V"
  have tr_M: "trail T = ?M"
    using tr V by auto
  have MT: "M = tl (trail T)" and MV: "M = trail V"
    using tr V by auto
  have DE[simp]: "D = E"
    using V conf raw by auto
  have "cdcl\<^sub>W_restart\<^sup>*\<^sup>* S T"
    using bj cdcl\<^sub>W_bj.skip mono_rtranclp[of skip cdcl\<^sub>W_restart S T] other st by meson
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
    using lev_L get_level_ge_0_atm_of_in[of 0 L "trail V"] by auto
  then have L_L': "atm_of L \<noteq> atm_of L'"
    using n_d' unfolding lits_of_def by auto
  have L'_M: "atm_of L' \<notin> atm_of ` lits_of_l (trail V)"
    using n_d' unfolding lits_of_def by auto
  have "?M \<Turnstile>as CNot D"
    using inv' raw unfolding cdcl\<^sub>W_conflicting_def cdcl\<^sub>W_all_struct_inv_def tr_M by auto
  then have "L' \<notin># (remove1_mset L D)"
    using L_L' L'_M \<open>Propagated L' C' # trail V \<Turnstile>as CNot D\<close>
    unfolding true_annots_true_cls true_clss_def
    by (auto simp: uminus_lit_swap atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set dest!: in_diffD)
  have [simp]: "trail (reduce_trail_to M1 T) = M1"
    using decomp tr W V by auto
  have "skip\<^sup>*\<^sup>* S V"
    using st skip by auto
  have "no_dup (trail S)"
    using inv unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def by auto
  then have [simp]: "init_clss S = init_clss V" and [simp]: "learned_clss S = learned_clss V"
    using rtranclp_skip_state_decomp[OF \<open>skip\<^sup>*\<^sup>* S V\<close>] V by auto
  have V_T: \<open>V \<sim> tl_trail T\<close>
    using skip by (auto elim: rulesE)
  have
    W_S: "W \<sim> cons_trail (Propagated L E) (reduce_trail_to M1
     (add_learned_cls E (update_backtrack_lvl i (update_conflicting None T))))"
    apply (rule state_eq_trans[OF W])
    unfolding DE
    apply (rule cons_trail_state_eq)
    apply (rule backtrack_reduce_trail_to_state_eq)
    using V decomp by auto

  obtain M2' where
    decomp': "(Decided K # M1, M2') \<in> set (get_all_ann_decomposition (trail T))"
    using decomp V unfolding tr_M by (cases "hd (get_all_ann_decomposition (trail V))",
      cases "get_all_ann_decomposition (trail V)") auto
  moreover
    from L_L' have "get_level ?M L = ?k"
      using lev_L V by (auto split: if_split_asm)
  moreover
    have "atm_of L' \<notin> atms_of D"
      by (metis DE LE L_L' \<open>L' \<notin># (remove1_mset L D)\<close> in_remove1_mset_neq
        atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set atms_of_def)
    then have "get_level ?M L = get_maximum_level ?M D"
      using calculation(2) lev_L max by auto
  moreover
    have "atm_of L' \<notin> atms_of ((remove1_mset L D))"
      by (metis DE LE \<open>L' \<notin># (remove1_mset L D)\<close>
        atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set atms_of_def in_remove1_mset_neq
        in_atms_of_remove1_mset_in_atms_of)
    have "i = get_maximum_level ?M ((remove1_mset L D))"
      using max_D \<open>atm_of L' \<notin> atms_of ((remove1_mset L D))\<close> by auto
  moreover have "atm_of L' \<noteq> atm_of K"
    using inv' get_all_ann_decomposition_exists_prepend[OF decomp]
    unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def tr MV by auto
  ultimately have "backtrack T W"
    apply -
    apply (rule backtrack_rule[of T _ L K M1 M2' i W, OF raw])
    unfolding tr_M[symmetric]
          using LD apply simp
         apply simp
        apply simp
       apply simp
      apply auto[]
     using W_S lev_k tr MV apply auto[]
    using W_S lev_k apply auto[]
    done
  then show ?thesis using IH inv by blast
qed


text \<open>See also theorem @{thm [source] rtranclp_skip_backtrack_backtrack}\<close>
lemma rtranclp_skip_backtrack_backtrack_end:
  assumes
    skip: "skip\<^sup>*\<^sup>* S T" and
    bt: "backtrack S W" and
    inv: "cdcl\<^sub>W_all_struct_inv S"
  shows "backtrack T W"
  using assms
proof -
  have M_lev: "cdcl\<^sub>W_M_level_inv S "
    using bt inv unfolding cdcl\<^sub>W_all_struct_inv_def by (auto elim!: backtrackE)
  then obtain K i M1 M2 L D where
    S: "conflicting S = Some D" and
    LD: "L \<in># D" and
    decomp: "(Decided K # M1, M2) \<in> set (get_all_ann_decomposition (trail S))" and
    lev_l: "get_level (trail S) L = backtrack_lvl S" and
    lev_l_D: "get_level (trail S) L = get_maximum_level (trail S) D" and
    i: "get_maximum_level (trail S) (remove1_mset L D) \<equiv> i" and
    lev_K: "get_level (trail S) K = Suc i" and
    W: "W \<sim> cons_trail (Propagated L D)
                (reduce_trail_to M1
                  (add_learned_cls D
                    (update_backtrack_lvl i
                      (update_conflicting None S))))"
    using bt by (elim backtrackE) (simp add: cdcl\<^sub>W_M_level_inv_decomp)
  let ?D = "remove1_mset L D"

  have [simp]: "no_dup (trail S)"
    using M_lev by (auto simp: cdcl\<^sub>W_M_level_inv_decomp)
  have "cdcl\<^sub>W_all_struct_inv T"
    using mono_rtranclp[of skip cdcl\<^sub>W_restart] by (smt bj cdcl\<^sub>W_bj.skip inv local.skip other
      rtranclp_cdcl\<^sub>W_all_struct_inv_inv)
  then have [simp]: "no_dup (trail T)"
    unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def by auto
  (* M\<^sub>T is a proxy to allow auto to unfold T*)
  obtain MS M\<^sub>T where M: "trail S = MS @ M\<^sub>T" and M\<^sub>T: "M\<^sub>T = trail T" and nm: "\<forall>m\<in>set MS. \<not>is_decided m"
    using rtranclp_skip_state_decomp(1)[OF skip] S by auto
  have T: "state_butlast T = (M\<^sub>T, init_clss S, learned_clss S, backtrack_lvl S, Some D)"
    using M\<^sub>T rtranclp_skip_state_decomp[of S T] skip S by auto

  have "cdcl\<^sub>W_all_struct_inv T"
    apply (rule rtranclp_cdcl\<^sub>W_all_struct_inv_inv[OF _ inv])
    using bj cdcl\<^sub>W_bj.skip local.skip other rtranclp_mono[of skip cdcl\<^sub>W_restart] by blast
  then have "M\<^sub>T \<Turnstile>as CNot D"
    unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_conflicting_def using T by blast
  then have "\<forall>L\<in>#D. atm_of L \<in> atm_of ` lits_of_l M\<^sub>T"
    by (meson atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set
      true_annots_true_cls_def_iff_negation_in_model)
  moreover have "no_dup (trail S)"
    using inv unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def by auto
  ultimately have "\<forall>L\<in>#D. atm_of L \<notin> atm_of ` lits_of_l MS"
    unfolding M unfolding lits_of_def by auto
  then have H: "\<And>L. L\<in>#D \<Longrightarrow> get_level (trail S) L = get_level M\<^sub>T L"
    unfolding M by (fastforce simp: lits_of_def)
  have [simp]: "get_maximum_level (trail S) D = get_maximum_level M\<^sub>T D"
    using \<open>M\<^sub>T \<Turnstile>as CNot D\<close> M nm \<open>\<forall>L\<in>#D. atm_of L \<notin> atm_of ` lits_of_l MS\<close>
    by (auto simp: get_maximum_level_skip_un_decided_not_present)

  have lev_l': "get_level M\<^sub>T L = backtrack_lvl S"
    using lev_l LD by (auto simp: H)
  have [simp]: "trail (reduce_trail_to M1 T) = M1"
    using T decomp M nm by (smt M\<^sub>T append_assoc beginning_not_decided_invert
      get_all_ann_decomposition_exists_prepend reduce_trail_to_trail_tl_trail_decomp)
  obtain c where c: \<open>M\<^sub>T = c @ Decided K # M1\<close>
    apply atomize
    using nm decomp by (auto dest!: get_all_ann_decomposition_exists_prepend
        simp: M\<^sub>T[symmetric] M append_assoc[symmetric]
        simp del: append_assoc
        dest!: beginning_not_decided_invert)
  obtain c'' where
    c'': \<open>(Decided K # M1, c'') \<in> set (get_all_ann_decomposition (c @ Decided K # M1))\<close>
    using Decided_cons_in_get_all_ann_decomposition_append_Decided_cons[of K M1]  by blast
  have W: "W \<sim> cons_trail (Propagated L D) (reduce_trail_to M1
    (add_learned_cls D (update_backtrack_lvl i (update_conflicting None T))))"
    apply (rule state_eq_trans[OF W])
    apply (rule cons_trail_state_eq)
    apply (rule rtranclp_skip_backtrack_reduce_trail_to_state_eq[of _ _ K M1])
     using skip apply (simp; fail)
    using c'' by (auto simp: M\<^sub>T[symmetric] M c)
  have lev_l_D': "get_level M\<^sub>T L = get_maximum_level M\<^sub>T D"
    using lev_l_D LD by (auto simp: H)
  have [simp]: "get_maximum_level (trail S) ?D = get_maximum_level M\<^sub>T ?D"
    by (smt H get_maximum_level_exists_lit get_maximum_level_ge_get_level in_diffD le_antisym
      not_gr0 not_less)
  then have i': "i = get_maximum_level M\<^sub>T ?D"
    using i by auto
  have "Decided K # M1 \<in> set (map fst (get_all_ann_decomposition (trail S)))"
    using Set.imageI[OF decomp, of fst] by auto
  then have "Decided K # M1 \<in> set (map fst (get_all_ann_decomposition M\<^sub>T))"
    using fst_get_all_ann_decomposition_prepend_not_decided[OF nm] unfolding M by auto
  then obtain M2' where decomp':"(Decided K # M1, M2') \<in> set (get_all_ann_decomposition M\<^sub>T)"
    by auto
  moreover
    have "atm_of K \<notin> atm_of ` lits_of_l MS"
      using \<open>no_dup (trail S)\<close> decomp' unfolding M M\<^sub>T
      by (auto simp: lits_of_def)
    then have "get_level (trail T) K = get_level (trail S) K"
      unfolding M M\<^sub>T by auto
  ultimately show "backtrack T W"
    apply -
    apply (rule backtrack.intros[of T D])
      using T lev_l' lev_l_D' i' W LD lev_K i apply auto[7]
    using T W unfolding i'[symmetric] by auto
qed

lemma cdcl\<^sub>W_bj_decomp_resolve_skip_and_bj:
  assumes "cdcl\<^sub>W_bj\<^sup>*\<^sup>* S T"
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
      { assume "\<exists>U. skip_or_resolve\<^sup>*\<^sup>* S U \<and> backtrack U T"
        then obtain V where
          bt: "backtrack V T" and
          "skip_or_resolve\<^sup>*\<^sup>* S V"
          by blast
        then have "cdcl\<^sub>W_restart\<^sup>*\<^sup>* S V"
          using rtranclp_skip_or_resolve_rtranclp_cdcl\<^sub>W_restart by blast
        with bj bt have False using backtrack_no_cdcl\<^sub>W_bj by simp
      }
      then show ?thesis using IH by blast
    qed
  show ?case
    using bj
    proof (cases rule: cdcl\<^sub>W_bj.cases)
      case backtrack
      then show ?thesis using IH by blast
    qed (metis (no_types, lifting) IH rtranclp.simps skip_or_resolve.simps)+
qed

paragraph \<open>Uniqueness of the jumping\<close>
lemma resolve_skip_deterministic:
  "resolve S T \<Longrightarrow> skip S U \<Longrightarrow> False"
  by (auto elim!: skipE resolveE)

lemma list_same_level_decomp_is_same_decomp:
  assumes M_K: "M = M1 @ Decided K # M2" and M_K': "M = M1' @ Decided K' # M2'" and
  lev_KK': "get_level M K = get_level M K'" and
  n_d: "no_dup M"
  shows "K = K'" and "M1 = M1'" and "M2 = M2'"
proof -
  {
    fix j j' K K' M1 M1' M2 M2'
    assume
      M_K: "M = M1 @ Decided K # M2" and
      M_K': "M = M1' @ Decided K' # M2'" and
      levKK': "get_level M K = get_level M K'" and
      j: "M ! j = Decided K" and j_M: "j < length M" and
      j': "M ! j' = Decided K'" and j'_M: "j' < length M" and
      jj: "j' > j"
    have "j \<ge> length M1"
      proof (rule ccontr)
        assume "\<not> length M1 \<le> j"
        then have "j < length M1"
          by auto
        then have "Decided K \<in> set M1"
          using j unfolding M_K
          by (auto simp: nth_append in_set_conv_nth split: if_splits)
        from Set.imageI[OF this, of "\<lambda>L. atm_of (lit_of L)"]
        show False using n_d unfolding M_K by auto
      qed
    moreover then have "j' - Suc (length M1) < length M2"
      using j'_M jj M_K unfolding M_K' by (metis One_nat_def Suc_eq_plus1 add.left_commute
        le_less_trans length_append less_diff_conv2 list.size(4) not_less not_less_eq)
    ultimately have dec: "Decided K' \<in> set M2"
      using jj j j' j'_M unfolding M_K by (auto simp: nth_append in_set_conv_nth List.nth_Cons')
    obtain xs ys where
      M2: "M2 = xs @ Decided K' # ys"
      using List.split_list[OF dec] by auto
    have [simp]: "atm_of K \<noteq> atm_of K'"
      using n_d unfolding M_K M2 by auto
    have "atm_of K \<notin> atm_of ` lits_of_l M1" and "atm_of K' \<notin> atm_of ` lits_of_l M1" and
    "atm_of K' \<notin> atm_of ` lits_of_l xs"
      using n_d Set.imageI[OF dec, of "\<lambda>L. atm_of (lit_of L)"] unfolding M_K
      using n_d unfolding M_K M2
      by (auto simp: lits_of_def)
    then have False
      using M2 levKK' unfolding M_K by (auto simp: split: if_splits )
  } note H = this
  have "Decided K \<in> set M" and "Decided K' \<in> set M"
     using M_K apply simp
    using M_K' by simp
  then obtain j j' where
    j: "M ! j = Decided K" and j_M: "j < length M" and
    j': "M ! j' = Decided K'" and j'_M: "j' < length M"
      using in_set_conv_nth by metis

  have [simp]: "j = j'" using H[OF M_K M_K' _ j j_M j' j'_M]
    H[OF M_K' M_K _ j' j'_M j j_M] lev_KK' by presburger
  then show KK': "K = K'" using j j' by auto

  have j_M1: "j = length M1"
    proof (rule ccontr)
      assume "j \<noteq> length M1"
      moreover then have "j - Suc (length M1) < length M2 \<or> j < length M1"
        using j_M M_K unfolding M_K' by force
      ultimately have "Decided K \<in> set (M1 @ M2)"
        using j unfolding M_K by (auto simp: nth_append in_set_conv_nth split: if_splits)
      from Set.imageI[OF this, of "\<lambda>L. atm_of (lit_of L)"]
      show False using n_d unfolding M_K by auto
    qed
  have j_M2: "j' = length M1'"
    proof (rule ccontr)
      assume "j' \<noteq> length M1'"
      moreover then have "j' - Suc (length M1') < length M2' \<or> j' < length M1'"
        using j'_M M_K' unfolding M_K by force
      ultimately have "Decided K' \<in> set (M1' @ M2')"
        using j' unfolding M_K' by (auto simp: nth_append in_set_conv_nth split: if_splits)
      from Set.imageI[OF this, of "\<lambda>L. atm_of (lit_of L)"]
      show False using n_d unfolding M_K' by auto
    qed

  show "M1 = M1'" "M2 = M2'"
    using arg_cong[OF M_K, of "take j"] j_M1 arg_cong[OF M_K', of "take j'"] j_M2
    using arg_cong[OF M_K, of "drop (j+1)"] j_M1 arg_cong[OF M_K', of "drop (j'+1)"] j_M2
    by auto
qed

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
    S: "conflicting S = Some D" and
    LD: "L \<in># D" and
    decomp: "(Decided K # M1, M2) \<in> set (get_all_ann_decomposition (trail S))" and
    lev_l: "get_level (trail S) L = backtrack_lvl S" and
    lev_l_D: "get_level (trail S) L = get_maximum_level (trail S) D" and
    i: "get_maximum_level (trail S) (remove1_mset L D) \<equiv> i" and
    lev_K: "get_level (trail S) K = Suc i" and
    T: "T \<sim> cons_trail (Propagated L D)
                (reduce_trail_to M1
                  (add_learned_cls D
                    (update_backtrack_lvl i
                      (update_conflicting None S))))"
    using bt_T by (elim backtrackE) (force simp: cdcl\<^sub>W_M_level_inv_def)+

  obtain K' i' M1' M2' L' D' where
    S': "conflicting S = Some D'" and
    LD': "L' \<in># D'" and
    decomp': "(Decided K' # M1', M2') \<in> set (get_all_ann_decomposition (trail S))" and
    lev_l: "get_level (trail S) L' = backtrack_lvl S" and
    lev_l_D: "get_level (trail S) L' = get_maximum_level (trail S) D'" and
    i': "get_maximum_level (trail S) (remove1_mset L' D') \<equiv> i'" and
    lev_K': "get_level (trail S) K' = Suc i'" and
    U: "U \<sim> cons_trail (Propagated L' D')
                (reduce_trail_to M1'
                  (add_learned_cls D'
                    (update_backtrack_lvl i'
                      (update_conflicting None S))))"
    using bt_U lev by (elim backtrackE) (force simp: cdcl\<^sub>W_M_level_inv_def)+
  obtain c where M: "trail S = c @ M2 @ Decided K # M1"
    using decomp by auto
  obtain c' where M': "trail S = c' @ M2' @ Decided K' # M1'"
    using decomp' by auto
  have n_d: "no_dup (trail S)" and bt: "backtrack_lvl S = count_decided (trail S)"
    using lev unfolding cdcl\<^sub>W_M_level_inv_def by auto
  then have "atm_of K \<notin> atm_of ` lits_of_l (c @ M2)"
    by (auto simp: lits_of_def M)
  then have "i < backtrack_lvl S"
    using lev_K unfolding M bt by (auto simp add: image_Un)

  have [simp]: "L' = L"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then have "L' \<in># remove1_mset L D"
        using S S' LD LD' by (simp add: in_remove1_mset_neq)
      then have "get_maximum_level (trail S) (remove1_mset L D) \<ge> backtrack_lvl S"
        using \<open>get_level (trail S) L' = backtrack_lvl S\<close> get_maximum_level_ge_get_level
        by metis
      then show False using i' i \<open>i < backtrack_lvl S\<close> by auto
    qed
  then have [simp]: "D' = D"
    using S S' by auto
  have [simp]: "i' = i"
    using i i' by auto
  have [simp]: "K = K'" and [simp]: "M1 = M1'"
     apply (rule list_same_level_decomp_is_same_decomp[of "trail S" "c @ M2" K M1
         "c' @ M2'" K' M1'])
     using lev_K lev_K' M M' n_d apply (auto)[4]
    apply (rule list_same_level_decomp_is_same_decomp[of "trail S" "c @ M2" K M1
        "c' @ M2'" K' M1'])
    using lev_K lev_K' M M' n_d apply (auto)[4]
    done
  show ?thesis using T U by (auto simp: intro: state_eq_trans')
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
    tr_U: "hd_trail U = Propagated L E" and
    LE: "L \<in># E" and
    confl_U: "conflicting U = Some D" and
    LD: "-L \<in># D" and
    "get_maximum_level (trail U) ((remove1_mset (-L) D)) = backtrack_lvl U" and
    V: "V \<sim> update_conflicting (Some (resolve_cls L D E)) (tl_trail U) "
    using resolve by (auto elim!: resolveE)
  have inv_U: "cdcl\<^sub>W_all_struct_inv U"
    using mono_rtranclp[of skip cdcl\<^sub>W_restart] by (meson bj cdcl\<^sub>W_bj.skip inv local.skip other
      rtranclp_cdcl\<^sub>W_all_struct_inv_inv)
  then have [iff]: "no_dup (trail S)" "cdcl\<^sub>W_M_level_inv S" and [iff]: "no_dup (trail U)"
    using inv unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def by blast+
  have inv_V: "cdcl\<^sub>W_all_struct_inv V"
    using mono_rtranclp[of resolve cdcl\<^sub>W_restart] inv_U resolve cdcl\<^sub>W_restart.simps cdcl\<^sub>W_all_struct_inv_inv
    cdcl\<^sub>W_bj.resolve cdcl\<^sub>W_o.simps by blast
  have
    S: "init_clss U = init_clss S"
       "learned_clss U = learned_clss S"
       "backtrack_lvl U = backtrack_lvl S"
       "backtrack_lvl V = backtrack_lvl S"
       "conflicting S = Some D"
    using rtranclp_skip_state_decomp[OF skip] U confl_U V by auto
  obtain M\<^sub>0 where
    tr_S: "trail S = M\<^sub>0 @ trail U" and
    nm: "\<forall>m\<in>set M\<^sub>0. \<not>is_decided m"
    using rtranclp_skip_state_decomp[OF skip] by blast

  obtain K' i' M1' M2' L' D' where
    S': "conflicting S = Some D'" and
    LD': "L' \<in># D'" and
    decomp': "(Decided K' # M1', M2') \<in> set (get_all_ann_decomposition (trail S))" and
    lev_l: "get_level (trail S) L' = backtrack_lvl S" and
    lev_l_D: "get_level (trail S) L' = get_maximum_level (trail S) D'" and
    i': "get_maximum_level (trail S) (remove1_mset L' D') \<equiv> i'" and
    lev_K': "get_level (trail S) K' = Suc i'" and
    R: "T \<sim> cons_trail (Propagated L' D')
                (reduce_trail_to M1'
                  (add_learned_cls D'
                    (update_backtrack_lvl i'
                      (update_conflicting None S))))"
    using bt by (elim backtrackE) metis
  obtain c where M: "trail S = c @ M2' @ Decided K' # M1'"
    using get_all_ann_decomposition_exists_prepend[OF decomp'] by auto
  have "i' < backtrack_lvl S"
    using count_decided_ge_get_level[of K' "trail S"] inv
    unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def lev_K'
    by linarith

  have U: "trail U = Propagated L E # trail V"
   using tr_S U S V tr_U \<open>trail U \<noteq> []\<close> by (cases "trail U") (auto simp: lits_of_def)
  have DD'[simp]: "D' = D"
    using U S' S by auto
  have [simp]: "L' = -L"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then have "-L \<in># remove1_mset L' D'"
        using DD' LD' LD by (simp add: in_remove1_mset_neq)
      moreover
        have M': "trail S = M\<^sub>0 @ Propagated L E # trail V"
          using tr_S unfolding U by auto
        have "no_dup (trail S)"
           using inv U unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def by auto
        then have atm_L_notin_M: "atm_of L \<notin> atm_of ` (lits_of_l (trail V))"
          using M' U S by (auto simp: lits_of_def)
        have get_lev_L:
          "get_level(Propagated L E # trail V) L = backtrack_lvl V"
          using inv_V unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_M_level_inv_def by auto
        have "atm_of L \<notin> atm_of ` (lits_of_l (rev M\<^sub>0))"
          using \<open>no_dup (trail S)\<close> M' by (auto simp: lits_of_def)
        then have "get_level (trail S) L = backtrack_lvl S"
          using get_lev_L S unfolding M' by auto
      ultimately
        have "get_maximum_level (trail S) (remove1_mset L' D') \<ge> backtrack_lvl S"
          by (metis get_maximum_level_ge_get_level get_level_uminus)
      then show False
        using \<open>i' < backtrack_lvl S\<close> i' by auto
    qed
  have "cdcl\<^sub>W_restart\<^sup>*\<^sup>* S U"
    using bj cdcl\<^sub>W_bj.skip local.skip mono_rtranclp[of skip cdcl\<^sub>W_restart S U] other by meson
  then have "cdcl\<^sub>W_all_struct_inv U"
    using inv rtranclp_cdcl\<^sub>W_all_struct_inv_inv by blast
  then have "Propagated L E # trail V \<Turnstile>as CNot D'"
    using U confl_U unfolding cdcl\<^sub>W_all_struct_inv_def cdcl\<^sub>W_conflicting_def by auto
  then have "\<forall>L'\<in># (remove1_mset L' D') .
    atm_of L' \<in> atm_of ` lits_of_l (Propagated L E # trail U)"
    using U atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set in_CNot_implies_uminus(2)
    by (fastforce dest: in_diffD)
  then have "\<forall>L'\<in># (remove1_mset L' D') .
    atm_of L' \<notin> atm_of ` lits_of_l M\<^sub>0"
    using \<open>no_dup (trail S)\<close> unfolding tr_S U by (fastforce simp: lits_of_def image_image)
  then have "get_maximum_level (trail S) (remove1_mset L' D') = backtrack_lvl S"
     using get_maximum_level_skip_un_decided_not_present[of "remove1_mset L' D'"
         M\<^sub>0 "trail U"] tr_S nm U
      \<open>get_maximum_level (trail U) ((remove1_mset (- L) D)) = backtrack_lvl U\<close>
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
        \<and> skip\<^sup>*\<^sup>* U V \<and> backtrack V W)
    \<or> (\<exists>T U. (\<lambda>S T. skip_or_resolve S T \<and> no_step backtrack S)\<^sup>*\<^sup>* S T
        \<and> (\<lambda>T U. resolve T U \<and> no_step backtrack T) T U \<and> skip\<^sup>*\<^sup>* U W)
    \<or> (\<exists>T. skip\<^sup>*\<^sup>* S T \<and> backtrack T W)
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
      then show False
        by (metis (no_types, lifting) "1"(5) backtrack_no_cdcl\<^sub>W_bj local.bj)
    next
      case 2
      then show ?case by (metis backtrack_no_cdcl\<^sub>W_bj local.bj)
    qed
  then have IH: "?R S W \<or> ?S S W" using IH by blast

  have "cdcl\<^sub>W_restart\<^sup>*\<^sup>* S W" using mono_rtranclp[of cdcl\<^sub>W_bj cdcl\<^sub>W_restart] st by blast
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
      then show ?thesis using IH by (meson rtranclp.rtrancl_into_rtrancl)
    next
      case resolve note no_bt = this(1) and res = this(2)
      consider
          (RS) T U where
            "(\<lambda>S T. skip_or_resolve S T \<and> no_step backtrack S)\<^sup>*\<^sup>* S T" and
            "resolve T U" and
            "no_step backtrack T" and
            "skip\<^sup>*\<^sup>* U W"
        | (S) "skip\<^sup>*\<^sup>* S W"
        using IH by auto
      then show ?thesis
        proof cases
          case (RS T U)
          have "cdcl\<^sub>W_restart\<^sup>*\<^sup>* S T"
            using RS(1) cdcl\<^sub>W_bj.resolve cdcl\<^sub>W_o.bj other skip
            mono_rtranclp[of " (\<lambda>S T. skip_or_resolve S T \<and> no_step backtrack S)" cdcl\<^sub>W_restart S T]
            by (meson skip_or_resolve.cases)
          then have "cdcl\<^sub>W_all_struct_inv U"
            by (meson RS(2) cdcl\<^sub>W_all_struct_inv_inv cdcl\<^sub>W_bj.resolve cdcl\<^sub>W_o.bj other
              rtranclp_cdcl\<^sub>W_all_struct_inv_inv step.prems)
          { fix U'
            assume "skip\<^sup>*\<^sup>* U U'" and "skip\<^sup>*\<^sup>* U' W"
            have "cdcl\<^sub>W_all_struct_inv U'"
              using \<open>cdcl\<^sub>W_all_struct_inv U\<close> \<open>skip\<^sup>*\<^sup>* U U'\<close> rtranclp_cdcl\<^sub>W_all_struct_inv_inv
                 cdcl\<^sub>W_o.bj rtranclp_mono[of skip cdcl\<^sub>W_restart] other skip by blast
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
            then have "cdcl\<^sub>W_restart\<^sup>*\<^sup>* S U'"
              using mono_rtranclp[of skip cdcl\<^sub>W_restart S U'] by (simp add: cdcl\<^sub>W_o.bj other skip)
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

paragraph \<open>Confluence\<close>
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
  have "cdcl\<^sub>W_restart\<^sup>*\<^sup>* S T"
    using st mono_rtranclp[of cdcl\<^sub>W_bj cdcl\<^sub>W_restart] other by blast
  then have lev_T: "cdcl\<^sub>W_M_level_inv T"
    using inv rtranclp_cdcl\<^sub>W_restart_consistent_inv[of S T]
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
      have "cdcl\<^sub>W_restart\<^sup>*\<^sup>* S T"
        by (metis (no_types, hide_lams) bj mono_rtranclp[of cdcl\<^sub>W_bj cdcl\<^sub>W_restart] other st)
      then have inv_T: "cdcl\<^sub>W_all_struct_inv T"
        by (metis (no_types, hide_lams) inv rtranclp_cdcl\<^sub>W_all_struct_inv_inv)

      have lev_U: "cdcl\<^sub>W_M_level_inv U"
        using s_o_r cdcl\<^sub>W_restart_consistent_inv lev_T other by blast
      show ?thesis
        using s_o_r
        proof cases
          case backtrack
          then obtain V0 where "skip\<^sup>*\<^sup>* T V0" and "backtrack V0 V"
            using IH if_can_apply_backtrack_skip_or_resolve_is_skip[OF backtrack _ inv_T]
             cdcl\<^sub>W_bj_decomp_resolve_skip_and_bj
             by (metis bj_TV cdcl\<^sub>W_bj.backtrack inv_T n_s rtranclp_skip_backtrack_backtrack_end)
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
            by (meson T_U' bj cdcl\<^sub>W_restart_consistent_inv lev_T other state_eq_ref state_eq_sym
              tranclp_cdcl\<^sub>W_bj_state_eq_compatible)
        next
          case skip
          consider
              (sk) "skip T U'"
            | (bt) "backtrack T U'"
            using T_U' by (meson cdcl\<^sub>W_bj.cases local.skip resolve_skip_deterministic)
          then show ?thesis
            proof cases
              case sk
              then show ?thesis
                using \<open>cdcl\<^sub>W_bj\<^sup>*\<^sup>* U' V\<close> unfolding rtranclp_unfold
                by (meson T_U' bj cdcl\<^sub>W_restart_all_inv(3) cdcl\<^sub>W_all_struct_inv_def inv_T local.skip other
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


subsection \<open>CDCL with Merging\<close>

inductive cdcl\<^sub>W_merge_restart :: "'st \<Rightarrow> 'st \<Rightarrow> bool" where
fw_r_propagate: "propagate S S' \<Longrightarrow> cdcl\<^sub>W_merge_restart S S'" |
fw_r_conflict: "conflict S T \<Longrightarrow> full cdcl\<^sub>W_bj T U \<Longrightarrow> cdcl\<^sub>W_merge_restart S U" |
fw_r_decide: "decide S S' \<Longrightarrow> cdcl\<^sub>W_merge_restart S S'"|
fw_r_rf: "cdcl\<^sub>W_rf S S' \<Longrightarrow> cdcl\<^sub>W_merge_restart S S'"

lemma rtranclp_cdcl\<^sub>W_bj_rtranclp_cdcl\<^sub>W_restart:
  "cdcl\<^sub>W_bj\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl\<^sub>W_restart\<^sup>*\<^sup>* S T"
  using mono_rtranclp[of cdcl\<^sub>W_bj cdcl\<^sub>W_restart] by blast

lemma cdcl\<^sub>W_merge_restart_cdcl\<^sub>W_restart:
  assumes "cdcl\<^sub>W_merge_restart S T"
  shows "cdcl\<^sub>W_restart\<^sup>*\<^sup>* S T"
  using assms
proof induction
  case (fw_r_conflict S T U) note confl = this(1) and bj = this(2)
  have "cdcl\<^sub>W_restart S T" using confl by (simp add: cdcl\<^sub>W_restart.intros r_into_rtranclp)
  moreover
    have "cdcl\<^sub>W_bj\<^sup>*\<^sup>* T U" using bj unfolding full_def by auto
    then have "cdcl\<^sub>W_restart\<^sup>*\<^sup>* T U" using rtranclp_cdcl\<^sub>W_bj_rtranclp_cdcl\<^sub>W_restart by blast
  ultimately show ?case by auto
qed (simp_all add: cdcl\<^sub>W_o.intros cdcl\<^sub>W_restart.intros r_into_rtranclp)

lemma cdcl\<^sub>W_merge_restart_conflicting_true_or_no_step:
  assumes "cdcl\<^sub>W_merge_restart S T"
  shows "conflicting T = None \<or> no_step cdcl\<^sub>W_restart T"
  using assms
proof induction
  case (fw_r_conflict S T U) note confl = this(1) and n_s = this(2)
  { fix D V
    assume "cdcl\<^sub>W_restart U V" and "conflicting U = Some D"
    then have False
      using n_s unfolding full_def
      by (induction rule: cdcl\<^sub>W_restart_all_rules_induct)
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

lemma cdcl\<^sub>W_merge_rtranclp_cdcl\<^sub>W_restart:
  "cdcl\<^sub>W_merge S T \<Longrightarrow> cdcl\<^sub>W_restart\<^sup>*\<^sup>* S T"
  using cdcl\<^sub>W_merge_cdcl\<^sub>W_merge_restart cdcl\<^sub>W_merge_restart_cdcl\<^sub>W_restart by blast

lemma rtranclp_cdcl\<^sub>W_merge_rtranclp_cdcl\<^sub>W_restart:
  "cdcl\<^sub>W_merge\<^sup>*\<^sup>* S T \<Longrightarrow> cdcl\<^sub>W_restart\<^sup>*\<^sup>* S T"
  using rtranclp_mono[of cdcl\<^sub>W_merge "cdcl\<^sub>W_restart\<^sup>*\<^sup>*"] cdcl\<^sub>W_merge_rtranclp_cdcl\<^sub>W_restart by auto

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
  case (step c d) note st = this(1) and fw = this(2) and IH = this(3)
  have "cdcl\<^sub>W_all_struct_inv c"
    using tranclp_into_rtranclp[OF st] cdcl\<^sub>W_merge_rtranclp_cdcl\<^sub>W_restart assms(1)
    rtranclp_cdcl\<^sub>W_all_struct_inv_inv rtranclp_mono[of cdcl\<^sub>W_merge "cdcl\<^sub>W_restart\<^sup>*\<^sup>*"] by fastforce
  then have "(\<lambda>S T. cdcl\<^sub>W_all_struct_inv S \<and> cdcl\<^sub>W_merge S T)\<^sup>+\<^sup>+ c d"
    using fw by auto
  then show ?case using IH by auto
qed

lemma backtrack_is_full1_cdcl\<^sub>W_bj:
  assumes bt: "backtrack S T"
  shows "full1 cdcl\<^sub>W_bj S T"
   using bt backtrack_no_cdcl\<^sub>W_bj unfolding full1_def by blast

lemma rtrancl_cdcl\<^sub>W_conflicting_true_cdcl\<^sub>W_merge_restart:
  assumes "cdcl\<^sub>W_restart\<^sup>*\<^sup>* S V" and inv: "cdcl\<^sub>W_M_level_inv S" and "conflicting S = None"
  shows "(cdcl\<^sub>W_merge_restart\<^sup>*\<^sup>* S V \<and> conflicting V = None)
    \<or> (\<exists>T U. cdcl\<^sub>W_merge_restart\<^sup>*\<^sup>* S T \<and> conflicting V \<noteq> None \<and> conflict T U \<and> cdcl\<^sub>W_bj\<^sup>*\<^sup>* U V)"
  using assms
proof induction
  case base
  then show ?case by simp
next
  case (step U V) note st = this(1) and cdcl\<^sub>W_restart = this(2) and IH = this(3)[OF this(4-)] and
    confl[simp] = this(5) and inv = this(4)
  from cdcl\<^sub>W_restart
  show ?case
    proof (cases)
      case propagate
      moreover then have "conflicting U = None" and "conflicting V = None"
        by (auto elim: propagateE)
      ultimately show ?thesis using IH cdcl\<^sub>W_merge_restart.fw_r_propagate[of U V] by auto
    next
      case conflict
      moreover then have "conflicting U = None" and "conflicting V \<noteq> None"
        by (auto elim!: conflictE)
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
              by (auto simp: skip_or_resolve.simps elim!: skipE resolveE)
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
              using inv rtranclp_cdcl\<^sub>W_restart_consistent_inv step.hyps(1) by blast
            then have "conflicting V = None"
              using \<open>backtrack U V\<close> inv by (auto elim: backtrackE
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

lemma no_step_cdcl\<^sub>W_restart_no_step_cdcl\<^sub>W_merge_restart:
  "no_step cdcl\<^sub>W_restart S \<Longrightarrow> no_step cdcl\<^sub>W_merge_restart S"
  by (auto simp: cdcl\<^sub>W_restart.simps cdcl\<^sub>W_merge_restart.simps cdcl\<^sub>W_o.simps cdcl\<^sub>W_bj.simps)

lemma no_step_cdcl\<^sub>W_merge_restart_no_step_cdcl\<^sub>W_restart:
  assumes
    "conflicting S = None" and
    "cdcl\<^sub>W_M_level_inv S" and
    "no_step cdcl\<^sub>W_merge_restart S"
  shows "no_step cdcl\<^sub>W_restart S"
proof -
  { fix S'
    assume "conflict S S'"
    then have "cdcl\<^sub>W_restart S S'" using cdcl\<^sub>W_restart.conflict by auto
    then have "cdcl\<^sub>W_M_level_inv S'"
      using assms(2) cdcl\<^sub>W_restart_consistent_inv by blast
    then obtain S'' where "full cdcl\<^sub>W_bj S' S''"
      using cdcl\<^sub>W_bj_exists_normal_form[of S'] by auto
    then have False
      using \<open>conflict S S'\<close> assms(3) fw_r_conflict by blast
  }
  then show ?thesis
    using assms unfolding cdcl\<^sub>W_restart.simps cdcl\<^sub>W_merge_restart.simps cdcl\<^sub>W_o.simps cdcl\<^sub>W_bj.simps
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

text \<open>If @{term "conflicting S \<noteq> None"}, we cannot say anything.

  Remark that this theorem does not say anything about well-foundedness: even if you know that one
  relation is well-founded, it only states that the normal forms are shared.
  \<close>
lemma conflicting_true_full_cdcl\<^sub>W_restart_iff_full_cdcl\<^sub>W_merge:
  assumes confl: "conflicting S = None" and lev: "cdcl\<^sub>W_M_level_inv S"
  shows "full cdcl\<^sub>W_restart S V \<longleftrightarrow> full cdcl\<^sub>W_merge_restart S V"
proof
  assume full: "full cdcl\<^sub>W_merge_restart S V"
  then have st: "cdcl\<^sub>W_restart\<^sup>*\<^sup>* S V"
    using rtranclp_mono[of cdcl\<^sub>W_merge_restart "cdcl\<^sub>W_restart\<^sup>*\<^sup>*"] cdcl\<^sub>W_merge_restart_cdcl\<^sub>W_restart
    unfolding full_def by auto

  have n_s: "no_step cdcl\<^sub>W_merge_restart V"
    using full unfolding full_def by auto
  have n_s_bj: "no_step cdcl\<^sub>W_bj V"
    using rtranclp_cdcl\<^sub>W_merge_restart_no_step_cdcl\<^sub>W_bj confl full unfolding full_def by auto
  have "\<And>S'. conflict V S' \<Longrightarrow> cdcl\<^sub>W_M_level_inv S'"
    using cdcl\<^sub>W_restart.conflict cdcl\<^sub>W_restart_consistent_inv lev rtranclp_cdcl\<^sub>W_restart_consistent_inv st by blast
  then have "\<And>S'. conflict V S' \<Longrightarrow> False"
    using n_s n_s_bj cdcl\<^sub>W_bj_exists_normal_form cdcl\<^sub>W_merge_restart.simps by meson
  then have n_s_cdcl\<^sub>W_restart: "no_step cdcl\<^sub>W_restart V"
    using n_s n_s_bj by (auto simp: cdcl\<^sub>W_restart.simps cdcl\<^sub>W_o.simps cdcl\<^sub>W_merge_restart.simps)
  then show "full cdcl\<^sub>W_restart S V" using st unfolding full_def by auto
next
  assume full: "full cdcl\<^sub>W_restart S V"
  have "no_step cdcl\<^sub>W_merge_restart V"
    using full no_step_cdcl\<^sub>W_restart_no_step_cdcl\<^sub>W_merge_restart unfolding full_def by blast
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

lemma init_state_true_full_cdcl\<^sub>W_restart_iff_full_cdcl\<^sub>W_merge:
  shows "full cdcl\<^sub>W_restart (init_state N) V \<longleftrightarrow> full cdcl\<^sub>W_merge_restart (init_state N) V"
  by (rule conflicting_true_full_cdcl\<^sub>W_restart_iff_full_cdcl\<^sub>W_merge) auto

subsection \<open>CDCL with Merge and Strategy\<close>
subsubsection \<open>The intermediate step\<close>
inductive cdcl\<^sub>W_s' :: "'st \<Rightarrow> 'st \<Rightarrow> bool" for S :: 'st where
conflict': "conflict S S' \<Longrightarrow> cdcl\<^sub>W_s' S S'" |
propagate': "propagate S S' \<Longrightarrow> cdcl\<^sub>W_s' S S'" |
decide': "no_step conflict S \<Longrightarrow> no_step propagate S \<Longrightarrow> decide S S' \<Longrightarrow> cdcl\<^sub>W_s' S S'" |
bj': "full1 cdcl\<^sub>W_bj S S' \<Longrightarrow> cdcl\<^sub>W_s' S S'"

inductive_cases cdcl\<^sub>W_s'E: "cdcl\<^sub>W_s' S T"

lemma rtranclp_cdcl\<^sub>W_bj_full1_cdclp_cdcl\<^sub>W_stgy:
  "cdcl\<^sub>W_bj\<^sup>*\<^sup>* S S' \<Longrightarrow> cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S S'"
proof (induction rule: converse_rtranclp_induct)
  case base
  then show ?case by simp
next
  case (step T U) note st = this(2) and bj = this(1) and IH = this(3)
  have n_s: "no_step conflict T" "no_step propagate T"
    using bj by (auto simp add: cdcl\<^sub>W_bj.simps elim!: rulesE)
  consider
      (U) "U = S'"
    | (U') U' where "cdcl\<^sub>W_bj U U'" and "cdcl\<^sub>W_bj\<^sup>*\<^sup>* U' S'"
    using st by (metis converse_rtranclpE)
  then show ?case
    proof cases
      case U
      then show ?thesis
        using n_s cdcl\<^sub>W_o.bj local.bj other' by (meson r_into_rtranclp)
    next
      case U' note U' = this(1)
      have "no_step conflict U" "no_step propagate U"
        using U' by (fastforce simp: cdcl\<^sub>W_bj.simps elim!: rulesE)+
      then have "cdcl\<^sub>W_stgy T U"
        using n_s cdcl\<^sub>W_stgy.simps local.bj cdcl\<^sub>W_o.bj by meson
      then show ?thesis using IH by auto
    qed
qed

lemma cdcl\<^sub>W_s'_is_rtranclp_cdcl\<^sub>W_stgy:
  "cdcl\<^sub>W_s' S T \<Longrightarrow> cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S T"
  by (induction rule: cdcl\<^sub>W_s'.induct)
    (auto simp: full1_def
     dest: tranclp_into_rtranclp rtranclp_cdcl\<^sub>W_bj_full1_cdclp_cdcl\<^sub>W_stgy cdcl\<^sub>W_stgy.intros)

lemma cdcl\<^sub>W_stgy_cdcl\<^sub>W_s'_no_step:
  assumes "cdcl\<^sub>W_stgy S U" and "cdcl\<^sub>W_all_struct_inv S" and "no_step cdcl\<^sub>W_bj U"
  shows "cdcl\<^sub>W_s' S U"
  using assms apply (cases rule: cdcl\<^sub>W_stgy.cases)
  using bj'[of S U] by (auto intro: cdcl\<^sub>W_s'.intros simp: cdcl\<^sub>W_o.simps full1_def)

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
      then have "cdcl\<^sub>W_s'\<^sup>*\<^sup>* S T"
        using IH by (auto elim: conflictE)
      moreover have f2: "cdcl\<^sub>W_s'\<^sup>*\<^sup>* T V"
        using cdcl\<^sub>W_s'.conflict' conflict' by blast
      ultimately show ?thesis by auto
    next
      case propagate'
      then have "cdcl\<^sub>W_s'\<^sup>*\<^sup>* S T"
        using IH by (auto elim: propagateE)
      moreover have f2: "cdcl\<^sub>W_s'\<^sup>*\<^sup>* T V"
        using cdcl\<^sub>W_s'.propagate' propagate' by blast
      ultimately show ?thesis by auto
    next
      case other' note o = this(3) and n_s = this(1,2) and full = this(3)
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
                then have "full1 cdcl\<^sub>W_bj T V"
                  using backtrack_is_full1_cdcl\<^sub>W_bj backtrack by blast
                then have "cdcl\<^sub>W_s' T V"
                 using full bj' n_s by blast
              ultimately show ?thesis by auto
            next
              case (bj S') note S_S' = this(1) and bj_T = this(2)
              moreover
                have "cdcl\<^sub>W_M_level_inv T"
                  using inv local.step(1) rtranclp_cdcl\<^sub>W_stgy_consistent_inv by auto
                then have "full1 cdcl\<^sub>W_bj T V"
                  using backtrack_is_full1_cdcl\<^sub>W_bj backtrack by blast
                then have "full1 cdcl\<^sub>W_bj S' V"
                  using bj_T unfolding full1_def by fastforce
              ultimately have "cdcl\<^sub>W_s' S' V" by (simp add: cdcl\<^sub>W_s'.bj')
              then show ?thesis using S_S' by auto
            qed
        next
          case skip
          then have confl_V: "conflicting V \<noteq> None"
            using skip by (auto elim: rulesE)
          have "cdcl\<^sub>W_bj T V"
            using local.skip by blast
          then show ?thesis
            using confl_V step.IH by auto
        next
          case resolve
          have confl_V: "conflicting V \<noteq> None"
            using resolve by (auto elim!: rulesE)
          have "cdcl\<^sub>W_bj T V"
            using local.resolve by blast
          then show ?thesis
            using confl_V step.IH by auto
        qed
    qed
qed

lemma n_step_cdcl\<^sub>W_stgy_iff_no_step_cdcl\<^sub>W_restart_cl_cdcl\<^sub>W_o:
  assumes inv: "cdcl\<^sub>W_all_struct_inv S"
  shows "no_step cdcl\<^sub>W_s' S \<longleftrightarrow> no_step cdcl\<^sub>W_stgy S" (is "?S' S \<longleftrightarrow> ?C S")
proof
  assume "?C S"
  then show "?S' S"
    by (auto simp: cdcl\<^sub>W_s'.simps full1_def tranclp_unfold_begin cdcl\<^sub>W_stgy.simps)
next
  assume n_s: "?S' S"
  then show "?C S"
    by (metis bj' cdcl\<^sub>W_bj_exists_normal_form cdcl\<^sub>W_o.cases cdcl\<^sub>W_s'.intros
      cdcl\<^sub>W_stgy.cases decide' full_unfold)
qed

lemma cdcl\<^sub>W_s'_tranclp_cdcl\<^sub>W_restart:
   assumes "cdcl\<^sub>W_s' S S'" shows "cdcl\<^sub>W_restart\<^sup>+\<^sup>+ S S'"
   using assms
proof (cases rule: cdcl\<^sub>W_s'.cases)
  case conflict'
  then show ?thesis by blast
next
  case propagate'
  then show ?thesis by blast
next
  case decide'
  then show ?thesis
    using cdcl\<^sub>W_stgy.simps cdcl\<^sub>W_stgy_tranclp_cdcl\<^sub>W_restart by (meson cdcl\<^sub>W_o.simps)
next
  case bj'
  then show ?thesis
    by (metis cdcl\<^sub>W_s'.bj' cdcl\<^sub>W_s'_is_rtranclp_cdcl\<^sub>W_stgy full1_def
      rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W_restart rtranclp_unfold tranclp_unfold_begin)
qed

lemma tranclp_cdcl\<^sub>W_s'_tranclp_cdcl\<^sub>W_restart:
  "cdcl\<^sub>W_s'\<^sup>+\<^sup>+ S S' \<Longrightarrow> cdcl\<^sub>W_restart\<^sup>+\<^sup>+ S S'"
  apply (induct rule: tranclp.induct)
   using cdcl\<^sub>W_s'_tranclp_cdcl\<^sub>W_restart apply blast
  by (meson cdcl\<^sub>W_s'_tranclp_cdcl\<^sub>W_restart tranclp_trans)

lemma rtranclp_cdcl\<^sub>W_s'_rtranclp_cdcl\<^sub>W_restart:
   "cdcl\<^sub>W_s'\<^sup>*\<^sup>* S S' \<Longrightarrow> cdcl\<^sub>W_restart\<^sup>*\<^sup>* S S'"
  using rtranclp_unfold[of cdcl\<^sub>W_s' S S'] tranclp_cdcl\<^sub>W_s'_tranclp_cdcl\<^sub>W_restart[of S S'] by auto

lemma full_cdcl\<^sub>W_stgy_iff_full_cdcl\<^sub>W_s':
  assumes inv: "cdcl\<^sub>W_all_struct_inv S"
  shows "full cdcl\<^sub>W_stgy S T \<longleftrightarrow> full cdcl\<^sub>W_s' S T" (is "?S \<longleftrightarrow> ?S'")
proof
  assume ?S'
  then have "cdcl\<^sub>W_restart\<^sup>*\<^sup>* S T"
    using rtranclp_cdcl\<^sub>W_s'_rtranclp_cdcl\<^sub>W_restart[of S T] unfolding full_def by blast
  then have inv': "cdcl\<^sub>W_all_struct_inv T"
    using rtranclp_cdcl\<^sub>W_all_struct_inv_inv inv by blast
  have "cdcl\<^sub>W_stgy\<^sup>*\<^sup>* S T"
    using \<open>?S'\<close> unfolding full_def
      using cdcl\<^sub>W_s'_is_rtranclp_cdcl\<^sub>W_stgy rtranclp_mono[of cdcl\<^sub>W_s' "cdcl\<^sub>W_stgy\<^sup>*\<^sup>*"] by auto
  then show ?S
    using \<open>?S'\<close> inv' n_step_cdcl\<^sub>W_stgy_iff_no_step_cdcl\<^sub>W_restart_cl_cdcl\<^sub>W_o unfolding full_def
    by blast
next
  assume ?S
  then have inv_T: "cdcl\<^sub>W_all_struct_inv T"
    by (metis assms full_def rtranclp_cdcl\<^sub>W_all_struct_inv_inv
      rtranclp_cdcl\<^sub>W_stgy_rtranclp_cdcl\<^sub>W_restart)
  consider
      (s') "cdcl\<^sub>W_s'\<^sup>*\<^sup>* S T"
    | (st) S' where "cdcl\<^sub>W_s'\<^sup>*\<^sup>* S S'" and "cdcl\<^sub>W_bj\<^sup>+\<^sup>+ S' T" and "conflicting T \<noteq> None"
    using rtranclp_cdcl\<^sub>W_stgy_connected_to_rtranclp_cdcl\<^sub>W_s'[of S T] inv \<open>?S\<close>
    unfolding full_def cdcl\<^sub>W_all_struct_inv_def
    by blast
  then show ?S'
    proof cases
      case s'
      then show ?thesis
        using \<open>full cdcl\<^sub>W_stgy S T\<close> unfolding full_def
        by (metis inv_T n_step_cdcl\<^sub>W_stgy_iff_no_step_cdcl\<^sub>W_restart_cl_cdcl\<^sub>W_o)
    next
      case (st S') note st = this(1) and bj = this(2) and confl = this(3)
      have "no_step cdcl\<^sub>W_bj T"
        using \<open>?S\<close> cdcl\<^sub>W_stgy.conflict' cdcl\<^sub>W_stgy.intros(2) other' unfolding full_def by blast
      then have "full1 cdcl\<^sub>W_bj S' T"
        using bj unfolding full1_def by blast
      then have "cdcl\<^sub>W_s' S' T"
        using cdcl\<^sub>W_s'.bj'[of S' T] by blast
      then have "cdcl\<^sub>W_s'\<^sup>*\<^sup>* S T"
        using st(1) by auto
      moreover have "no_step cdcl\<^sub>W_s' T"
        using inv_T \<open>full cdcl\<^sub>W_stgy S T\<close> n_step_cdcl\<^sub>W_stgy_iff_no_step_cdcl\<^sub>W_restart_cl_cdcl\<^sub>W_o
        unfolding full_def  by blast
      ultimately show ?thesis
        unfolding full_def by blast
    qed
qed

end

end