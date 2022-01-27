theory DPLL_W_Optimal_Model
imports
  DPLL_W_BnB
begin

locale dpll\<^sub>W_state_optimal_weight =
  dpll\<^sub>W_state trail clauses
    tl_trail cons_trail state_eq state +
  ocdcl_weight \<rho>
  for
    trail :: \<open>'st \<Rightarrow> 'v  dpll\<^sub>W_ann_lits\<close> and
    clauses :: \<open>'st \<Rightarrow> 'v clauses\<close> and
    tl_trail :: \<open>'st \<Rightarrow> 'st\<close> and
    cons_trail :: \<open>'v  dpll\<^sub>W_ann_lit \<Rightarrow> 'st \<Rightarrow> 'st\<close> and
    state_eq  :: \<open>'st \<Rightarrow> 'st \<Rightarrow> bool\<close> (infix \<open>\<sim>\<close> 50) and
    state :: \<open>'st \<Rightarrow> 'v  dpll\<^sub>W_ann_lits \<times> 'v clauses \<times> 'v clause option \<times> 'b\<close> and
    \<rho> :: \<open>'v clause \<Rightarrow> 'a :: {linorder}\<close> +
  fixes
    update_additional_info :: \<open>'v clause option \<times> 'b \<Rightarrow> 'st \<Rightarrow> 'st\<close>
  assumes
    update_additional_info:
      \<open>state S = (M, N, K) \<Longrightarrow> state (update_additional_info K' S) = (M, N, K')\<close>
begin

definition update_weight_information :: \<open>('v literal, 'v literal, unit) annotated_lits \<Rightarrow> 'st \<Rightarrow> 'st\<close> where
  \<open>update_weight_information M S =
    update_additional_info (Some (lit_of `# mset M), snd (additional_info S)) S\<close>

lemma [simp]:
  \<open>trail (update_weight_information M' S) = trail S\<close>
  \<open>clauses (update_weight_information M' S) = clauses S\<close>
  \<open>clauses (update_additional_info c S) = clauses S\<close>
  \<open>additional_info (update_additional_info (w, oth) S) = (w, oth)\<close>
  using update_additional_info[of S] unfolding update_weight_information_def
  by (auto simp: state)

lemma state_update_weight_information: \<open>state S = (M, N, w, oth) \<Longrightarrow>
       \<exists>w'. state (update_weight_information M' S) = (M, N, w', oth)\<close>
  apply (auto simp: state)
  apply (auto simp: update_weight_information_def)
  done

definition weight where
  \<open>weight S = fst (additional_info S)\<close>

lemma [simp]: \<open>(weight (update_weight_information M' S)) = Some (lit_of `# mset M')\<close>
  unfolding weight_def by (auto simp: update_weight_information_def)

text \<open>

  We test here a slightly different decision. In the CDCL version, we renamed \<^term>\<open>additional_info\<close>
  from the BNB version to avoid collisions. Here instead of renaming, we add the prefix
  \<^text>\<open>bnb.\<close> to every name.

\<close>
sublocale bnb: bnb_ops where
  trail = trail and
  clauses = clauses and
  tl_trail = tl_trail and
  cons_trail = cons_trail and
  state_eq = state_eq and
  state = state and
  weight = weight and
  conflicting_clauses = conflicting_clauses and
  is_improving_int = is_improving_int and
  update_weight_information = update_weight_information
  by unfold_locales


lemma atms_of_mm_conflicting_clss_incl_init_clauses:
  \<open>atms_of_mm (bnb.conflicting_clss S) \<subseteq> atms_of_mm (clauses S)\<close>
  using conflicting_clss_incl_init_clauses[of \<open>clauses S\<close> \<open>weight S\<close>]
  unfolding bnb.conflicting_clss_def
  by auto

lemma is_improving_conflicting_clss_update_weight_information: \<open>bnb.is_improving M M' S \<Longrightarrow>
       bnb.conflicting_clss S \<subseteq># bnb.conflicting_clss (update_weight_information M' S)\<close>
  using is_improving_conflicting_clss_update_weight_information[of M M' \<open>clauses S\<close> \<open>weight S\<close>]
  unfolding bnb.conflicting_clss_def
  by (auto simp: update_weight_information_def weight_def)

lemma conflicting_clss_update_weight_information_in2:
  assumes \<open>bnb.is_improving M M' S\<close>
  shows \<open>negate_ann_lits M' \<in># bnb.conflicting_clss (update_weight_information M' S)\<close>
  using conflicting_clss_update_weight_information_in2[of M M' \<open>clauses S\<close> \<open>weight S\<close>] assms
  unfolding bnb.conflicting_clss_def
  unfolding bnb.conflicting_clss_def
  by (auto simp: update_weight_information_def weight_def)


lemma state_additional_info':
  \<open>state S = (trail S, clauses S, weight S, bnb.additional_info S)\<close>
  unfolding additional_info_def by (cases \<open>state S\<close>; auto simp: state weight_def bnb.additional_info_def)

sublocale bnb: bnb where
  trail = trail and
  clauses = clauses and
  tl_trail = tl_trail and
  cons_trail = cons_trail and
  state_eq = state_eq and
  state = state and
  weight = weight and
  conflicting_clauses = conflicting_clauses and
  is_improving_int = is_improving_int and
  update_weight_information = update_weight_information
  apply unfold_locales
  subgoal by auto
  subgoal by (rule state_eq_sym)
  subgoal by (rule state_eq_trans)
  subgoal by (auto dest!: state_eq_state)
  subgoal by (rule cons_trail)
  subgoal by (rule tl_trail)
  subgoal by (rule state_update_weight_information)
  subgoal by (rule is_improving_conflicting_clss_update_weight_information)
  subgoal by (rule conflicting_clss_update_weight_information_in2; assumption)
  subgoal by (rule atms_of_mm_conflicting_clss_incl_init_clauses)
  subgoal by (rule state_additional_info')
  done

lemma improve_model_still_model:
  assumes
    \<open>bnb.dpll\<^sub>W_bound S T\<close> and
    all_struct: \<open>dpll\<^sub>W_all_inv (bnb.abs_state S)\<close> and
    ent: \<open>set_mset I \<Turnstile>sm clauses S\<close>  \<open>set_mset I \<Turnstile>sm bnb.conflicting_clss S\<close> and
    dist: \<open>distinct_mset I\<close> and
    cons: \<open>consistent_interp (set_mset I)\<close> and
    tot: \<open>atms_of I = atms_of_mm (clauses S)\<close> and
    le: \<open>Found (\<rho> I) < \<rho>' (weight T)\<close>
  shows
    \<open>set_mset I \<Turnstile>sm clauses T \<and> set_mset I \<Turnstile>sm bnb.conflicting_clss T\<close>
  using assms(1)
proof (cases rule: bnb.dpll\<^sub>W_bound.cases)
  case (update_info M M') note imp = this(1) and T = this(2)
  have atm_trail: \<open>atms_of (lit_of `# mset (trail S)) \<subseteq> atms_of_mm (clauses S)\<close> and
       dist2: \<open>distinct_mset (lit_of `# mset (trail S))\<close> and
      taut2: \<open>\<not> tautology (lit_of `# mset (trail S))\<close>
    using all_struct unfolding dpll\<^sub>W_all_inv_def by (auto simp: lits_of_def atms_of_def
      dest: no_dup_distinct no_dup_not_tautology)

  have tot2: \<open>total_over_m (set_mset I) (set_mset (clauses S))\<close>
    using tot[symmetric]
    by (auto simp: total_over_m_def total_over_set_def atm_iff_pos_or_neg_lit)
  have atm_trail: \<open>atms_of (lit_of `# mset M') \<subseteq> atms_of_mm (clauses S)\<close> and
    dist2: \<open>distinct_mset (lit_of `# mset M')\<close> and
    taut2: \<open>\<not> tautology (lit_of `# mset M')\<close>
    using imp by (auto simp: lits_of_def atms_of_def is_improving_int_def
      simple_clss_def)

  have tot2: \<open>total_over_m (set_mset I) (set_mset (clauses S))\<close>
    using tot[symmetric]
    by (auto simp: total_over_m_def total_over_set_def atm_iff_pos_or_neg_lit)
  have
    \<open>set_mset I \<Turnstile>m conflicting_clauses (clauses S) (weight (update_weight_information M' S))\<close>
    using entails_conflicting_clauses_if_le[of I \<open>clauses S\<close> M' M \<open>weight S\<close>]
    using T dist cons tot le imp by auto
  then have \<open>set_mset I \<Turnstile>m bnb.conflicting_clss (update_weight_information M' S)\<close>
    by (auto simp: update_weight_information_def bnb.conflicting_clss_def)
  then show ?thesis
    using ent T by (auto simp: bnb.conflicting_clss_def state)
qed

lemma cdcl_bnb_still_model:
  assumes
    \<open>bnb.dpll\<^sub>W_bnb S T\<close> and
    all_struct: \<open>dpll\<^sub>W_all_inv (bnb.abs_state S)\<close> and
    ent: \<open>set_mset I \<Turnstile>sm clauses S\<close> \<open>set_mset I \<Turnstile>sm bnb.conflicting_clss S\<close> and
    dist: \<open>distinct_mset I\<close> and
    cons: \<open>consistent_interp (set_mset I)\<close> and
    tot: \<open>atms_of I = atms_of_mm (clauses S)\<close>
  shows
    \<open>(set_mset I \<Turnstile>sm clauses T \<and> set_mset I \<Turnstile>sm bnb.conflicting_clss T) \<or> Found (\<rho> I) \<ge> \<rho>' (weight T)\<close>
  using assms
proof (induction rule: bnb.dpll\<^sub>W_bnb.induct)
  case (dpll S T)
  then show ?case using ent by (auto elim!: bnb.dpll\<^sub>W_coreE simp: bnb.state'_def
       dpll_decide.simps dpll_backtrack.simps bnb.backtrack_opt.simps
       dpll_propagate.simps)
next
  case (bnb S T)
  then show ?case
    using improve_model_still_model[of S T I] using assms(2-) by auto
qed

lemma cdcl_bnb_larger_still_larger:
  assumes
    \<open>bnb.dpll\<^sub>W_bnb S T\<close>
  shows \<open>\<rho>' (weight S) \<ge> \<rho>' (weight T)\<close>
  using assms apply (cases rule: bnb.dpll\<^sub>W_bnb.cases)
  by (auto simp: bnb.dpll\<^sub>W_bound.simps is_improving_int_def bnb.dpll\<^sub>W_core_same_weight)

lemma rtranclp_cdcl_bnb_still_model:
  assumes
    st: \<open>bnb.dpll\<^sub>W_bnb\<^sup>*\<^sup>* S T\<close> and
    all_struct: \<open>dpll\<^sub>W_all_inv (bnb.abs_state S)\<close> and
    ent: \<open>(set_mset I \<Turnstile>sm clauses S \<and> set_mset I \<Turnstile>sm bnb.conflicting_clss S) \<or> Found (\<rho> I) \<ge> \<rho>' (weight S)\<close> and
    dist: \<open>distinct_mset I\<close> and
    cons: \<open>consistent_interp (set_mset I)\<close> and
    tot: \<open>atms_of I = atms_of_mm (clauses S)\<close>
  shows
    \<open>(set_mset I \<Turnstile>sm clauses T \<and> set_mset I \<Turnstile>sm bnb.conflicting_clss T) \<or> Found (\<rho> I) \<ge> \<rho>' (weight T)\<close>
  using st
proof (induction rule: rtranclp_induct)
  case base
  then show ?case
    using ent by auto
next
  case (step T U) note star = this(1) and st = this(2) and IH = this(3)
  have 1: \<open>dpll\<^sub>W_all_inv (bnb.abs_state T)\<close>
    using bnb.rtranclp_dpll\<^sub>W_bnb_abs_state_all_inv[OF star all_struct] .
  have 3: \<open>atms_of I = atms_of_mm (clauses T)\<close>
    using bnb.rtranclp_dpll\<^sub>W_bnb_clauses[OF star] tot by auto
  show ?case
    using cdcl_bnb_still_model[OF st 1 _ _ dist cons 3] IH
      cdcl_bnb_larger_still_larger[OF st]
      order.trans by blast
qed

lemma simple_clss_entailed_by_too_heavy_in_conflicting:
   \<open>C \<in># mset_set (simple_clss (atms_of_mm (clauses S))) \<Longrightarrow>
    too_heavy_clauses (clauses S) (weight S) \<Turnstile>pm
     (C) \<Longrightarrow> C \<in># bnb.conflicting_clss S\<close>
  by (auto simp: conflicting_clauses_def bnb.conflicting_clss_def)

lemma can_always_improve:
  assumes
    ent: \<open>trail S \<Turnstile>asm clauses S\<close> and
    total: \<open>total_over_m (lits_of_l (trail S)) (set_mset (clauses S))\<close> and
    n_s: \<open>(\<forall>C \<in># bnb.conflicting_clss S. \<not> trail S \<Turnstile>as CNot C)\<close> and
    all_struct: \<open>dpll\<^sub>W_all_inv (bnb.abs_state S)\<close>
   shows \<open>Ex (bnb.dpll\<^sub>W_bound S)\<close>
proof -
  have H: \<open>(lit_of `# mset (trail S)) \<in># mset_set (simple_clss (atms_of_mm (clauses S)))\<close>
    \<open>(lit_of `# mset (trail S)) \<in> simple_clss (atms_of_mm (clauses S))\<close>
    \<open>no_dup (trail S)\<close>
    apply (subst finite_set_mset_mset_set[OF simple_clss_finite])
    using all_struct by (auto simp: simple_clss_def
        dpll\<^sub>W_all_inv_def atms_of_def lits_of_def image_image clauses_def
      dest: no_dup_not_tautology no_dup_distinct)
  moreover have \<open>trail S \<Turnstile>as CNot (pNeg (lit_of `# mset (trail S)))\<close>
    by (auto simp: pNeg_def true_annots_true_cls_def_iff_negation_in_model lits_of_def)

  ultimately have le: \<open>Found (\<rho> (lit_of `# mset (trail S))) < \<rho>' (weight S)\<close>
    using n_s total not_entailed_too_heavy_clauses_ge[of \<open>lit_of `# mset (trail S)\<close> \<open>clauses S\<close> \<open>weight S\<close>]
     simple_clss_entailed_by_too_heavy_in_conflicting[of \<open>pNeg (lit_of `# mset (trail S))\<close> S]
    by (cases \<open>\<not> too_heavy_clauses (clauses S) (weight S) \<Turnstile>pm
       pNeg (lit_of `# mset (trail S))\<close>)
     (auto simp:  lits_of_def
         conflicting_clauses_def clauses_def negate_ann_lits_pNeg_lit_of image_iff
         simple_clss_finite subset_iff
       dest: bspec[of _ _ \<open>(lit_of `# mset (trail S))\<close>] dest: total_over_m_atms_incl
          true_clss_cls_in too_heavy_clauses_contains_itself
          dest!: multi_member_split)
  have tr: \<open>trail S \<Turnstile>asm clauses S\<close>
    using ent by (auto simp: clauses_def)
  have tot': \<open>total_over_m (lits_of_l (trail S)) (set_mset (clauses S))\<close>
    using total all_struct by (auto simp: total_over_m_def total_over_set_def)
  have M': \<open>\<rho> (lit_of `# mset M') = \<rho> (lit_of `# mset (trail S))\<close>
    if \<open>total_over_m (lits_of_l M') (set_mset (clauses S))\<close> and
      incl: \<open>mset (trail S) \<subseteq># mset M'\<close> and
      \<open>lit_of `# mset M' \<in> simple_clss (atms_of_mm (clauses S))\<close>
      for M'
    proof -
      have [simp]: \<open>lits_of_l M' = set_mset (lit_of `# mset M')\<close>
        by (auto simp: lits_of_def)
      obtain A where A: \<open>mset M' = A + mset (trail S)\<close>
        using incl by (auto simp: mset_subset_eq_exists_conv)
      have M': \<open>lits_of_l M' = lit_of ` set_mset A \<union> lits_of_l (trail S)\<close>
        unfolding lits_of_def
        by (metis A image_Un set_mset_mset set_mset_union)
      have \<open>mset M' = mset (trail S)\<close>
        using that tot' total unfolding A total_over_m_alt_def
          apply (case_tac A)
        apply (auto simp: A simple_clss_def distinct_mset_add M' image_Un
            tautology_union mset_inter_empty_set_mset atms_of_def atms_of_s_def
            atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set image_image
            tautology_add_mset)
          by (metis (no_types, lifting) atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set
          lits_of_def subsetCE)
      then show ?thesis
        using total by auto
    qed
  have \<open>bnb.is_improving (trail S) (trail S) S\<close>
    if \<open>Found (\<rho> (lit_of `# mset (trail S))) < \<rho>' (weight S)\<close>
    using that total H tr tot' M' unfolding is_improving_int_def lits_of_def
    by fast
  then show ?thesis
    using bnb.dpll\<^sub>W_bound.intros[of \<open>trail S\<close> _ S \<open>update_weight_information (trail S) S\<close>] total H le
    by fast
qed


lemma no_step_dpll\<^sub>W_bnb_conflict:
  assumes
    ns: \<open>no_step bnb.dpll\<^sub>W_bnb S\<close> and
    invs: \<open>dpll\<^sub>W_all_inv (bnb.abs_state S)\<close>
  shows \<open>\<exists>C \<in># clauses S + bnb.conflicting_clss S. trail S \<Turnstile>as CNot C\<close> (is ?A) and
      \<open>count_decided (trail S) = 0\<close> and
     \<open>unsatisfiable (set_mset (clauses S + bnb.conflicting_clss S))\<close>
  apply (rule bnb.no_step_dpll\<^sub>W_bnb_conflict[OF _ assms])
  subgoal using can_always_improve by blast
  apply (rule bnb.no_step_dpll\<^sub>W_bnb_conflict[OF _ assms])
  subgoal using can_always_improve by blast
  apply (rule bnb.no_step_dpll\<^sub>W_bnb_conflict[OF _ assms])
  subgoal using can_always_improve by blast
  done

lemma full_cdcl_bnb_stgy_larger_or_equal_weight:
  assumes
    st: \<open>full bnb.dpll\<^sub>W_bnb S T\<close> and
    all_struct: \<open>dpll\<^sub>W_all_inv (bnb.abs_state S)\<close> and
    ent: \<open>(set_mset I \<Turnstile>sm clauses S \<and> set_mset I \<Turnstile>sm bnb.conflicting_clss S) \<or> Found (\<rho> I) \<ge> \<rho>' (weight S)\<close> and
    dist: \<open>distinct_mset I\<close> and
    cons: \<open>consistent_interp (set_mset I)\<close> and
    tot: \<open>atms_of I = atms_of_mm (clauses S)\<close>
  shows
    \<open>Found (\<rho> I) \<ge> \<rho>' (weight T)\<close> and
    \<open>unsatisfiable (set_mset (clauses T + bnb.conflicting_clss T))\<close>
proof -
  have ns: \<open>no_step bnb.dpll\<^sub>W_bnb T\<close> and
    st: \<open>bnb.dpll\<^sub>W_bnb\<^sup>*\<^sup>* S T\<close>
    using st unfolding full_def by (auto intro: )
  have struct_T: \<open>dpll\<^sub>W_all_inv (bnb.abs_state T)\<close>
    using bnb.rtranclp_dpll\<^sub>W_bnb_abs_state_all_inv[OF st all_struct]  .

  have atms_eq: \<open>atms_of I \<union> atms_of_mm (bnb.conflicting_clss T) = atms_of_mm (clauses T)\<close>
    using atms_of_mm_conflicting_clss_incl_init_clauses[of T]
      bnb.rtranclp_dpll\<^sub>W_bnb_clauses[OF st] tot
    by auto

  show \<open>unsatisfiable (set_mset (clauses T + bnb.conflicting_clss T))\<close>
    using no_step_dpll\<^sub>W_bnb_conflict[of T] ns struct_T
    by fast
  then have \<open>\<not>set_mset I \<Turnstile>sm clauses T + bnb.conflicting_clss T\<close>
    using dist cons by auto
  then have \<open>False\<close> if \<open>Found (\<rho> I) < \<rho>' (weight T)\<close>
    using ent that rtranclp_cdcl_bnb_still_model[OF st assms(2-)]
      bnb.rtranclp_dpll\<^sub>W_bnb_clauses[OF st]
    apply simp
    using leD by blast

  then show \<open>Found (\<rho> I) \<ge> \<rho>' (weight T)\<close>
    by force
qed


(*TODO:
full_cdcl_bnb_stgy_larger_or_equal_weight
full_cdcl_bnb_stgy_no_conflicting_clause_from_init_state
*)

end

end
