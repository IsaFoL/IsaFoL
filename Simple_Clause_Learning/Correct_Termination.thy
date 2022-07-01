theory Correct_Termination
  imports Simple_Clause_Learning
begin

context scl begin

lemma not_satisfiable_if_sound_state_conflict_bottom:
  assumes sound_S: "sound_state N \<beta> S" and conflict_S: "state_conflict S = Some ({#}, \<gamma>)"
  shows "\<not> satisfiable (grounding_of_clss N)"
proof -
  from sound_S conflict_S have "N \<TTurnstile>\<G>e {{#}}"
    unfolding sound_state_def state_conflict_def by auto
  thus ?thesis by simp
qed

lemma propagate_if_conflict_follows_decide:
  assumes
    fin_N: "finite N" and fin_learned: "finite (state_learned S\<^sub>0)" and
    trail_lt_\<beta>: "\<forall>L \<in> fst ` set (state_trail S\<^sub>2). atm_of L \<prec>\<^sub>B \<beta>" and
    no_conf: "\<nexists>S\<^sub>1. conflict N \<beta> S\<^sub>0 S\<^sub>1" and deci: "decide N \<beta> S\<^sub>0 S\<^sub>2" and conf: "conflict N \<beta> S\<^sub>2 S\<^sub>3"
  shows "\<exists>S\<^sub>4. propagate N \<beta> S\<^sub>0 S\<^sub>4"
proof -
  from deci obtain L \<gamma> \<Gamma> U where
    S\<^sub>0_def: "S\<^sub>0 = (\<Gamma>, U, None)" and
    S\<^sub>2_def: "S\<^sub>2 = (trail_decide \<Gamma> (L \<cdot>l \<gamma>), U, None)" and
    "L \<in> \<Union> (set_mset ` N)" and
    "is_ground_lit (L \<cdot>l \<gamma>)" and
    "\<not> trail_defined_lit \<Gamma> (L \<cdot>l \<gamma>)" and
    "atm_of L \<cdot>a \<gamma> \<prec>\<^sub>B \<beta>"
    by (elim decide.cases) blast
  
  from conf S\<^sub>2_def obtain D D' \<sigma> where
    S\<^sub>3_def: "S\<^sub>3 = (trail_decide \<Gamma> (L \<cdot>l \<gamma>), U, Some (D', \<sigma>))" and
    D_in: "D \<in> N \<union> U" and
    D'_def: "D' = rename_clause (N \<union> U \<union> clss_of_trail (trail_decide \<Gamma> (L \<cdot>l \<gamma>))) D" and
    dom_\<sigma>_subset:"subst_domain \<sigma> \<subseteq> vars_cls D'" and
    ground_D'_\<sigma>: "is_ground_cls (D' \<cdot> \<sigma>)" and
    tr_\<Gamma>_L_false_D': "trail_false_cls (trail_decide \<Gamma> (L \<cdot>l \<gamma>)) (D' \<cdot> \<sigma>)"
    by (elim conflict.cases) blast

  define \<rho> :: "'v \<Rightarrow> ('f, 'v) Term.term" where
    "\<rho> = renaming_wrt (N \<union> U \<union> clss_of_trail \<Gamma>)"

  have ren_\<rho>: "is_renaming \<rho>"
    unfolding \<rho>_def
    by (metis S\<^sub>0_def fin_N fin_learned finite_UnI finite_clss_of_trail is_renaming_renaming_wrt
        state_learned_simp)

  have is_renaming_wrt_N_U_\<Gamma>_L: "is_renaming (renaming_wrt (N \<union> U \<union> clss_of_trail (trail_decide \<Gamma> (L \<cdot>l \<gamma>))))"
    by (metis S\<^sub>0_def fin_N fin_learned finite_UnI finite_clss_of_trail is_renaming_renaming_wrt
        state_learned_simp)

  from D'_def ground_D'_\<sigma> tr_\<Gamma>_L_false_D' obtain \<sigma>' where
    "is_ground_cls (D \<cdot> \<sigma>')" and "trail_false_cls ((L \<cdot>l \<gamma>, None) # \<Gamma>) (D \<cdot> \<sigma>')"
    unfolding trail_decide_def by (metis rename_clause_def subst_cls_comp_subst)
  moreover hence "\<not> trail_false_cls \<Gamma> (D \<cdot> \<sigma>')"
    using not_trail_false_ground_cls_if_no_conflict[OF fin_N fin_learned no_conf]
    using D_in by (simp add: S\<^sub>0_def)
  ultimately have "- (L \<cdot>l \<gamma>) \<in># D \<cdot> \<sigma>'"
    using subtrail_falseI by metis
  then obtain D'' L' where D_def: "D = add_mset L' D''" and "- (L \<cdot>l \<gamma>) = L' \<cdot>l \<sigma>'"
    by (meson Melem_subst_cls multi_member_split)

  have 1: "D'' \<cdot> \<rho> + {#L' \<cdot>l \<rho>#} = rename_clause (N \<union> U \<union> clss_of_trail \<Gamma>) D"
    unfolding D_def rename_clause_def
    by (simp add: \<rho>_def)

  have "inj \<rho>"
    unfolding \<rho>_def
    apply (rule inj_Var_renaming)
    using fin_N fin_learned
    by (simp add: S\<^sub>0_def)

  define \<sigma>'' where
    "\<sigma>'' = adapt_subst_to_renaming \<rho> \<sigma>'"

  define \<sigma>''' where
    "\<sigma>''' = restrict_subst (vars_cls (D'' \<cdot> \<rho>) \<union> vars_lit (L' \<cdot>l \<rho>)) \<sigma>''"

  have 2: "subst_domain \<sigma>''' \<subseteq> vars_cls (D'' \<cdot> \<rho>) \<union> vars_lit (L' \<cdot>l \<rho>)"
    by (simp add: \<sigma>'''_def subst_domain_restrict_subst)

  have "D \<cdot> \<sigma>' = D \<cdot> \<rho> \<cdot> \<sigma>''"
    unfolding \<sigma>''_def
  proof (rule subst_renaming_subst_adapted[symmetric])
    show "is_renaming \<rho>"
      unfolding \<rho>_def
      by (metis S\<^sub>0_def fin_N fin_learned finite_UnI finite_clss_of_trail is_renaming_renaming_wrt
          state_learned_simp)
  next
    show "vars_cls D \<subseteq> subst_domain \<sigma>'"
      using \<open>is_ground_cls (D \<cdot> \<sigma>')\<close>
      by (auto intro!: vars_cls_subset_subst_domain_if_grounding)
  qed
  hence "D \<cdot> \<sigma>' = D \<cdot> \<rho> \<cdot> \<sigma>'''"
    unfolding \<sigma>'''_def
    by (metis "1" \<rho>_def rename_clause_def subst_cls_restrict_subst_idem sup_bot.right_neutral
        sup_ge1 vars_cls_add_mset vars_cls_empty vars_cls_plus_iff)
  hence 3: "is_ground_cls ((D'' \<cdot> \<rho> + {#L' \<cdot>l \<rho>#}) \<cdot> \<sigma>''')"
    using 1[unfolded rename_clause_def, folded \<rho>_def, symmetric]
    using \<open>is_ground_cls (D \<cdot> \<sigma>')\<close>
    by presburger

  have not_false_if_grounding:
    "is_ground_cls (add_mset (L' \<cdot>l \<rho>) (D'' \<cdot> \<rho>) \<cdot> \<sigma>) \<Longrightarrow>
      \<not> trail_false_cls \<Gamma> (add_mset (L' \<cdot>l \<rho>) (D'' \<cdot> \<rho>) \<cdot> \<sigma>)" for \<sigma>
    using not_trail_false_ground_cls_if_no_conflict[OF fin_N fin_learned no_conf, unfolded S\<^sub>0_def,
        of "add_mset L' D''" "\<rho> \<odot> \<sigma>", simplified]
    using D_def D_in by auto

  have "L' \<cdot>l \<rho> \<cdot>l \<sigma>''' = L' \<cdot>l \<rho> \<cdot>l \<sigma>''"
    unfolding \<sigma>'''_def
    by (meson inf_sup_ord(4) subst_lit_restrict_subst_idem)

  have "D'' \<cdot> \<rho> \<cdot> \<sigma>''' = D'' \<cdot> \<rho> \<cdot> \<sigma>''"
    unfolding \<sigma>'''_def
    by (meson inf_sup_ord subst_cls_restrict_subst_idem)

  have "{#K \<in># D'' \<cdot> \<rho>. K \<cdot>l \<sigma>''' \<noteq> L' \<cdot>l \<rho> \<cdot>l \<sigma>'''#} =
    {#K \<in># D''. K \<cdot>l \<rho> \<cdot>l \<sigma>''' \<noteq> L' \<cdot>l \<rho> \<cdot>l \<sigma>'''#} \<cdot> \<rho>"
    unfolding subst_cls_def[of D'']
    unfolding image_mset_filter_mset_swap[symmetric]
    unfolding subst_cls_def[symmetric]
    by (rule refl)

  have "{#K \<in># D''. K \<cdot>l \<rho> \<cdot>l \<sigma>''' \<noteq> L' \<cdot>l \<rho> \<cdot>l \<sigma>''#} =
    {#K \<in># D''. K \<cdot>l \<rho> \<cdot>l \<sigma>'' \<noteq> L' \<cdot>l \<rho> \<cdot>l \<sigma>''#}"
  proof (rule filter_mset_cong0)
    fix K assume "K \<in># D''"
    hence "vars_lit K \<subseteq> vars_cls D''"
      using multi_member_split by fastforce
    hence "vars_lit (K \<cdot>l \<rho>) \<subseteq> vars_cls (D'' \<cdot> \<rho>)"
      by (rule vars_lit_subst_subset_vars_cls_substI)
    hence *: "vars_lit (K \<cdot>l \<rho>) \<subseteq> vars_cls (D'' \<cdot> \<rho>) \<union> vars_lit (L' \<cdot>l \<rho>)"
      by blast

    show "(K \<cdot>l \<rho> \<cdot>l \<sigma>''' \<noteq> L' \<cdot>l \<rho> \<cdot>l \<sigma>'') = (K \<cdot>l \<rho> \<cdot>l \<sigma>'' \<noteq> L' \<cdot>l \<rho> \<cdot>l \<sigma>'')"
      unfolding \<sigma>'''_def
      unfolding subst_lit_restrict_subst_idem[OF *]
      by (rule refl)
  qed

  have "{#K \<in># D'' \<cdot> \<rho>. K \<cdot>l \<sigma>''' \<noteq> L' \<cdot>l \<rho> \<cdot>l \<sigma>'''#} \<cdot> \<sigma>''' =
    {#K \<in># D''. K \<cdot>l \<rho> \<cdot>l \<sigma>'' \<noteq> L' \<cdot>l \<rho> \<cdot>l \<sigma>''#} \<cdot> \<rho> \<cdot> \<sigma>''"
    unfolding \<open>{#K \<in># D'' \<cdot> \<rho>. K \<cdot>l \<sigma>''' \<noteq> L' \<cdot>l \<rho> \<cdot>l \<sigma>'''#} = {#K \<in># D''. K \<cdot>l \<rho> \<cdot>l \<sigma>''' \<noteq> L' \<cdot>l \<rho> \<cdot>l \<sigma>'''#} \<cdot> \<rho>\<close>
    unfolding \<open>L' \<cdot>l \<rho> \<cdot>l \<sigma>''' = L' \<cdot>l \<rho> \<cdot>l \<sigma>''\<close>
    unfolding \<open>{#K \<in># D''. K \<cdot>l \<rho> \<cdot>l \<sigma>''' \<noteq> L' \<cdot>l \<rho> \<cdot>l \<sigma>''#} = {#K \<in># D''. K \<cdot>l \<rho> \<cdot>l \<sigma>'' \<noteq> L' \<cdot>l \<rho> \<cdot>l \<sigma>''#}\<close>
    unfolding \<sigma>'''_def
  proof (rule subst_cls_restrict_subst_idem)
    have "vars_cls ({#K \<in># D''. K \<cdot>l \<rho> \<cdot>l \<sigma>'' \<noteq> L' \<cdot>l \<rho> \<cdot>l \<sigma>''#} \<cdot> \<rho>) \<subseteq> vars_cls (D'' \<cdot> \<rho>)"
      by (metis multiset_filter_subset subset_mset.le_iff_add subst_cls_mono_mset sup_ge1
          vars_cls_plus_iff)
    thus "vars_cls ({#K \<in># D''. K \<cdot>l \<rho> \<cdot>l \<sigma>'' \<noteq> L' \<cdot>l \<rho> \<cdot>l \<sigma>''#} \<cdot> \<rho>) \<subseteq> vars_cls (D'' \<cdot> \<rho>) \<union>
      vars_lit (L' \<cdot>l \<rho>) "
      by fast
  qed

  have "vars_cls D \<subseteq> subst_domain \<sigma>'"
    by (rule \<open>is_ground_cls (D \<cdot> \<sigma>')\<close>[THEN vars_cls_subset_subst_domain_if_grounding])

  have "vars_cls D'' \<subseteq> subst_domain \<sigma>'" "vars_lit L' \<subseteq> subst_domain \<sigma>'"
    using \<open>is_ground_cls (D \<cdot> \<sigma>')\<close>[THEN vars_cls_subset_subst_domain_if_grounding]
    unfolding D_def
    by simp_all

  have "{#K \<in># D''. K \<cdot>l \<rho> \<cdot>l \<sigma>'' \<noteq> L' \<cdot>l \<sigma>'#} \<subseteq># D''"
    by simp
  hence "vars_cls {#K \<in># D''. K \<cdot>l \<rho> \<cdot>l \<sigma>'' \<noteq> L' \<cdot>l \<sigma>'#} \<subseteq> vars_cls D''"
    by (metis multiset_partition sup_ge1 vars_cls_plus_iff)
  with \<open>vars_cls D'' \<subseteq> subst_domain \<sigma>'\<close> have
    "vars_cls {#K \<in># D''. K \<cdot>l \<rho> \<cdot>l \<sigma>'' \<noteq> L' \<cdot>l \<sigma>'#} \<subseteq> subst_domain \<sigma>'"
    by fast

  have 4: "trail_false_cls \<Gamma> ({#K \<in># D'' \<cdot> \<rho>. K \<cdot>l \<sigma>''' \<noteq> L' \<cdot>l \<rho> \<cdot>l \<sigma>'''#} \<cdot> \<sigma>''')"
    using \<open>trail_false_cls ((L \<cdot>l \<gamma>, None) # \<Gamma>) (D \<cdot> \<sigma>')\<close>[
        unfolded \<open>D \<cdot> \<sigma>' = D \<cdot> \<rho> \<cdot> \<sigma>'''\<close> 1[unfolded rename_clause_def, folded \<rho>_def, symmetric],
        simplified]
    using not_false_if_grounding[of \<sigma>''', simplified, OF 3[simplified]]
    unfolding \<open>{#K \<in># D'' \<cdot> \<rho>. K \<cdot>l \<sigma>''' \<noteq> L' \<cdot>l \<rho> \<cdot>l \<sigma>'''#} \<cdot> \<sigma>''' =
       {#K \<in># D''. K \<cdot>l \<rho> \<cdot>l \<sigma>''  \<noteq> L' \<cdot>l \<rho> \<cdot>l \<sigma>''#} \<cdot> \<rho> \<cdot> \<sigma>''\<close>
    unfolding \<open>L' \<cdot>l \<rho> \<cdot>l \<sigma>''' = L' \<cdot>l \<rho> \<cdot>l \<sigma>''\<close> \<open>D'' \<cdot> \<rho> \<cdot> \<sigma>''' = D'' \<cdot> \<rho> \<cdot> \<sigma>''\<close>
    unfolding subst_lit_renaming_subst_adapted[OF ren_\<rho> \<open>vars_lit L' \<subseteq> subst_domain \<sigma>'\<close>, folded \<sigma>''_def]
    unfolding subst_renaming_subst_adapted[OF ren_\<rho> \<open>vars_cls D'' \<subseteq> subst_domain \<sigma>'\<close>, folded \<sigma>''_def]
    unfolding subst_renaming_subst_adapted[OF ren_\<rho>
        \<open>vars_cls {#K \<in># D''. K \<cdot>l \<rho> \<cdot>l \<sigma>'' \<noteq> L' \<cdot>l \<sigma>'#} \<subseteq> subst_domain \<sigma>'\<close>, folded \<sigma>''_def]
    unfolding \<open>- (L \<cdot>l \<gamma>) = L' \<cdot>l \<sigma>'\<close>[symmetric]
    unfolding trail_false_cls_def trail_false_lit_def list.set image_insert prod.sel
    unfolding subst_cls_def ball_image_mset_iff ball_filter_mset_iff
    by (smt (verit, ccfv_threshold) \<open>vars_cls D'' \<subseteq> subst_domain \<sigma>'\<close> \<rho>_def \<sigma>''_def
        add_mset_add_single clss_of_trail_trail_decide image_insert insert_DiffM insert_iff
        is_renaming_wrt_N_U_\<Gamma>_L le_sup_iff mk_disjoint_insert multiset.set_map
        subst_lit_renaming_subst_adapted uminus_lit_swap union_iff vars_cls_add_mset)

  have 5: "\<not> trail_defined_lit \<Gamma> (L' \<cdot>l \<rho> \<cdot>l \<sigma>''')"
    unfolding \<open>L' \<cdot>l \<rho> \<cdot>l \<sigma>''' = L' \<cdot>l \<rho> \<cdot>l \<sigma>''\<close>
    unfolding subst_lit_renaming_subst_adapted[OF ren_\<rho> \<open>vars_lit L' \<subseteq> subst_domain \<sigma>'\<close>, folded \<sigma>''_def]
    unfolding \<open>- (L \<cdot>l \<gamma>) = L' \<cdot>l \<sigma>'\<close>[symmetric]
    using \<open>\<not> trail_defined_lit \<Gamma> (L \<cdot>l \<gamma>)\<close>
    by (metis trail_defined_lit_iff_defined_uminus)

  obtain xs where "mset xs = add_mset (L' \<cdot>l \<rho>) {#K \<in># D'' \<cdot> \<rho>. K \<cdot>l \<sigma>''' = L' \<cdot>l \<rho> \<cdot>l \<sigma>'''#}"
    using ex_mset by auto
  hence set_xs_conv:
    "set xs = set_mset (add_mset (L' \<cdot>l \<rho>) {#K \<in># D'' \<cdot> \<rho>. K \<cdot>l \<sigma>''' = L' \<cdot>l \<rho> \<cdot>l \<sigma>'''#})"
    by (metis set_mset_mset)

  have "unifiers (set (pairs (map atm_of xs))) \<noteq> {}"
  proof (rule not_empty_if_mem)
    show "\<sigma>''' \<in> unifiers (set (pairs (map atm_of xs)))"
      unfolding unifiers_def mem_Collect_eq
      unfolding set_pairs list.set_map set_xs_conv
      unfolding subst_cls_def[of D'']
      unfolding image_mset_filter_mset_swap[symmetric]
      unfolding subst_cls_def[symmetric]
      unfolding split_paired_Ball_Sigma prod.sel
      unfolding set_mset_add_mset_insert image_insert
      unfolding subst_cls_def set_image_mset set_mset_filter
      by (smt (verit, ccfv_SIG) image_iff insert_iff mem_Collect_eq subst_atm_of_eqI)
  qed

  then obtain ys where
    unify_pairs: "unify (pairs (map atm_of xs)) [] = Some ys"
    using ex_unify_if_unifiers_not_empty[OF _ refl]
    by blast

  define \<mu> where
    "\<mu> = subst_of ys"

  have 6: "is_mimgu \<mu>
    {atm_of ` set_mset (add_mset (L' \<cdot>l \<rho>) {#K \<in># D'' \<cdot> \<rho>. K \<cdot>l \<sigma>''' = L' \<cdot>l \<rho> \<cdot>l \<sigma>'''#})}"
  proof (intro is_mimgu_if_mgu_sets[unfolded mgu_sets_def] exI conjI)
    show "set (map set [(map atm_of xs)]) = {atm_of ` set_mset
      (add_mset (L' \<cdot>l \<rho>) {#K \<in># D'' \<cdot> \<rho>. K \<cdot>l \<sigma>''' = L' \<cdot>l \<rho> \<cdot>l \<sigma>'''#})}"
      using set_xs_conv by auto
  next
    show "map_option subst_of (unify (concat (map pairs [map atm_of xs])) []) = Some \<mu>"
      by (simp add: unify_pairs \<mu>_def)
  qed

  have 7: "\<forall>K\<in>#add_mset (L' \<cdot>l \<rho>) (D'' \<cdot> \<rho>) \<cdot> \<sigma>'''. atm_of K \<prec>\<^sub>B \<beta>"
  proof (rule ballI)
    from trail_lt_\<beta> have trail_lt_\<beta>': "\<forall>K \<in> fst ` set (trail_decide \<Gamma> (L \<cdot>l \<gamma>)). atm_of K \<prec>\<^sub>B \<beta>"
      by (simp add: S\<^sub>2_def)
    
    fix K assume "K\<in>#add_mset (L' \<cdot>l \<rho>) (D'' \<cdot> \<rho>) \<cdot> \<sigma>'''"

    hence "K = L' \<cdot>l \<rho> \<cdot>l \<sigma>''' \<or> K \<in># {#K \<in># D'' \<cdot> \<rho> \<cdot> \<sigma>'''. K \<noteq> L' \<cdot>l \<rho> \<cdot>l \<sigma>'''#}"
      by (induction D'') auto
    thus "atm_of K \<prec>\<^sub>B \<beta>"
    proof (rule disjE)
      assume "K = L' \<cdot>l \<rho> \<cdot>l \<sigma>'''"
      thus ?thesis
        using trail_lt_\<beta>'
        by (metis D_def \<open>D \<cdot> \<sigma>' = D \<cdot> \<rho> \<cdot> \<sigma>'''\<close> \<open>K \<in># add_mset (L' \<cdot>l \<rho>) (D'' \<cdot> \<rho>) \<cdot> \<sigma>'''\<close>
            \<open>trail_false_cls ((L \<cdot>l \<gamma>, None) # \<Gamma>) (D \<cdot> \<sigma>')\<close> atm_of_eq_uminus_if_lit_eq
            subst_cls_add_mset trail_decide_def trail_false_cls_def trail_false_lit_def)
    next
      assume "K \<in># {#K \<in># D'' \<cdot> \<rho> \<cdot> \<sigma>'''. K \<noteq> L' \<cdot>l \<rho> \<cdot>l \<sigma>'''#}"
      hence "K \<in># {#K \<in># D'' \<cdot> \<rho>. K \<cdot>l \<sigma>''' \<noteq> L' \<cdot>l \<rho> \<cdot>l \<sigma>'''#} \<cdot> \<sigma>'''"
        by auto
      hence "trail_false_lit \<Gamma> K"
        using 4 by (simp add: trail_false_cls_def)
      hence "- K \<in> fst ` set \<Gamma>"
        by (simp add: trail_false_lit_def)
      thus ?thesis
        using trail_lt_\<beta>'[rule_format, of "- K"]
        by (simp add: trail_decide_def)
    qed
  qed

  show ?thesis
    using propagateI[OF D_in 1 2 3 refl refl 4 5 6 refl 7]
    unfolding S\<^sub>0_def by blast
qed

definition trail_propagated_wf where
  "trail_propagated_wf \<Gamma> \<longleftrightarrow> (\<forall>(L\<^sub>\<gamma>, n) \<in> set \<Gamma>.
    case n of
      None \<Rightarrow> True
    | Some (_, L, \<gamma>) \<Rightarrow> L\<^sub>\<gamma> = L \<cdot>l \<gamma>)"

lemma trail_propagated_wf_if_sound: "sound_trail N U \<Gamma> \<Longrightarrow> trail_propagated_wf \<Gamma>"
proof (induction \<Gamma> rule: sound_trail.induct)
  case Nil
  then show ?case
    by (simp add: trail_propagated_wf_def)
next
  case (Cons \<Gamma> L u)
  then show ?case
    by (cases u) (auto simp add: trail_propagated_wf_def)
qed

definition trail_minimal_subst_domains where
  "trail_minimal_subst_domains \<Gamma> \<longleftrightarrow> (\<forall>(_, n) \<in> set \<Gamma>.
    case n of
      None \<Rightarrow> True
    | Some (C, L, \<gamma>) \<Rightarrow> subst_domain \<gamma> \<subseteq> vars_cls (add_mset L C))"

lemma trail_minimal_subst_domains_if_sound: "sound_trail N U \<Gamma> \<Longrightarrow> trail_minimal_subst_domains \<Gamma>"
proof (induction \<Gamma> rule: sound_trail.induct)
  case Nil
  then show ?case
    by (simp add: trail_minimal_subst_domains_def)
next
  case (Cons \<Gamma> L u)
  then show ?case
    by (cases u) (auto simp add: trail_minimal_subst_domains_def)
qed

definition trail_groundings where
  "trail_groundings \<Gamma> \<longleftrightarrow> (\<forall>(_, n) \<in> set \<Gamma>.
    case n of
      None \<Rightarrow> True
    | Some (C, L, \<gamma>) \<Rightarrow> is_ground_cls (add_mset L C \<cdot> \<gamma>))"

lemma trail_groundings_if_sound: "sound_trail N U \<Gamma> \<Longrightarrow> trail_groundings \<Gamma>"
proof (induction \<Gamma> rule: sound_trail.induct)
  case Nil
  then show ?case
    by (simp add: trail_groundings_def)
next
  case (Cons \<Gamma> L u)
  then show ?case
    by (cases u) (auto simp add: trail_groundings_def)
qed

definition conflict_minimal_subst_domain where
  "conflict_minimal_subst_domain u \<longleftrightarrow>
    (case u of None \<Rightarrow> True | Some (C, \<gamma>) \<Rightarrow> subst_domain \<gamma> \<subseteq> vars_cls C)"

lemma
  assumes
    fin_N: "finite N" and fin_learned_S: "finite (state_learned S)" and
    disj_N: "disjoint_vars_set N" and
    regular_run: "(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S" and
    no_more_regular_step: "\<nexists>S'. regular_scl N \<beta> S S'"
  shows "\<not> satisfiable (grounding_of_clss N) \<and> (\<exists>\<gamma>. state_conflict S = Some ({#}, \<gamma>)) \<or>
    satisfiable {C \<in> grounding_of_clss N. \<forall>L \<in># C. atm_of L \<prec>\<^sub>B \<beta>} \<and>
      trail_true_clss (state_trail S) {C \<in> grounding_of_clss N. \<forall>L \<in># C. atm_of L \<prec>\<^sub>B \<beta>}"
proof -
  from regular_run have scl_run: "(scl N \<beta>)\<^sup>*\<^sup>* initial_state S"
  proof (rule mono_rtranclp[rule_format, rotated])
    show "\<And>a b. regular_scl N \<beta> a b \<Longrightarrow> scl N \<beta> a b"
      by (rule scl_if_reasonable[OF reasonable_if_regular])
  qed
  hence mempty_not_in_learned_S: "{#} \<notin> state_learned S"
    by (induction S rule: rtranclp_induct) (simp_all add: scl_mempty_not_in_sate_learned)

  obtain \<Gamma> U u where S_def: "S = (\<Gamma>, U, u)"
    using prod_cases3 by blast

  have sound_S: "sound_state N \<beta> S"
    using regular_run_sound_state[OF regular_run] sound_initial_state[OF fin_N disj_N] by blast
  hence sound_\<Gamma>: "sound_trail N U \<Gamma>"
    by (simp add: S_def sound_state_def)

  from no_more_regular_step have no_new_conflict: "\<nexists>S'. conflict N \<beta> S S'"
    using regular_scl_def by blast

  from no_more_regular_step have no_new_propagate: "\<nexists>S'. propagate N \<beta> S S'"
    by (meson decide_well_defined(1) local.scl_def reasonable_scl_def regular_scl_def)

  from no_more_regular_step have
    no_reasonable_decide: "(\<nexists>S'. decide N \<beta> S S') \<or> (\<exists>S' S''. decide N \<beta> S S' \<and> conflict N \<beta> S' S'')"
    using local.scl_def reasonable_scl_def regular_scl_def by meson

  from sound_\<Gamma> have trail_propagate_wf: "trail_propagated_wf (state_trail S)"
    by (simp add: S_def trail_propagated_wf_if_sound)
  from sound_\<Gamma> have trail_min_subst_dom: "trail_minimal_subst_domains (state_trail S)"
    by (simp add: S_def trail_minimal_subst_domains_if_sound)
  from sound_\<Gamma> have trail_groundings: "trail_groundings (state_trail S)"
    by (simp add: S_def trail_groundings_if_sound)
  from sound_\<Gamma> have trail_consistent: "trail_consistent (state_trail S)"
    by (simp add: S_def trail_consistent_if_sound)

  show ?thesis
  proof (cases u)
    case u_def: None
    hence "state_conflict S = None"
      by (simp add: S_def)

    show ?thesis
      using no_reasonable_decide
    proof (elim disjE exE conjE)
      assume no_new_decide: "\<nexists>S'. decide N \<beta> S S'"

      have tr_true: "trail_true_clss \<Gamma> {C \<in> grounding_of_clss N. \<forall>L \<in># C. atm_of L \<prec>\<^sub>B \<beta>}"
        unfolding trail_true_clss_def
      proof (rule ballI, unfold mem_Collect_eq, erule conjE)
        fix C assume C_in: "C \<in> grounding_of_clss N" and C_lt_\<beta>: "\<forall>L \<in># C. atm_of L \<prec>\<^sub>B \<beta>"

        from C_in have "is_ground_cls C"
          by (rule grounding_ground)

        from C_in obtain C' \<gamma> where C'_in: "C' \<in> N" and C_def: "C = C' \<cdot> \<gamma>"
          using grounding_of_clss_def grounding_of_cls_def
          by (smt (verit, del_insts) UN_iff mem_Collect_eq)

        from no_new_decide have \<Gamma>_defined_C: "trail_defined_cls \<Gamma> C"
        proof (rule contrapos_np)
          assume "\<not> trail_defined_cls \<Gamma> C"
          then obtain L where L_in: "L \<in># C" and "\<not> trail_defined_lit \<Gamma> L"
            using trail_defined_cls_def by blast
          then obtain L' where L'_in: "L' \<in># C'" and "L = L' \<cdot>l \<gamma>"
            using C_def Melem_subst_cls by blast

          have "decide N \<beta> (\<Gamma>, U, None) (trail_decide \<Gamma> (L' \<cdot>l \<gamma>), U, None)"
          proof (rule decideI)
            show "L' \<in> \<Union> (set_mset ` N)"
              using C'_in L'_in by blast
          next
            show "is_ground_lit (L' \<cdot>l \<gamma>)"
              using L_in \<open>L = L' \<cdot>l \<gamma>\<close> \<open>is_ground_cls C\<close> is_ground_cls_def by blast
          next
            show "\<not> trail_defined_lit \<Gamma> (L' \<cdot>l \<gamma>)"
              using \<open>L = L' \<cdot>l \<gamma>\<close> \<open>\<not> trail_defined_lit \<Gamma> L\<close> by blast
          next
            show "atm_of L' \<cdot>a \<gamma> \<prec>\<^sub>B \<beta>"
              using \<open>L = L' \<cdot>l \<gamma>\<close> C_lt_\<beta> L_in by fastforce
          qed
          thus "\<exists>S'. decide N \<beta> S S'"
            by (auto simp add: S_def u_def)
        qed

        show "trail_true_cls \<Gamma> C"
          using \<Gamma>_defined_C[THEN trail_true_or_false_cls_if_defined]
        proof (elim disjE)
          show "trail_true_cls \<Gamma> C \<Longrightarrow> trail_true_cls \<Gamma> C"
            by assumption
        next
          assume "trail_false_cls \<Gamma> C"

          define C'' where
            "C'' = rename_clause (N \<union> U \<union> clss_of_trail \<Gamma>) C'"
          define \<rho> :: "'v \<Rightarrow> ('f, 'v) term" where
            "\<rho> = renaming_wrt (N \<union> U \<union> clss_of_trail \<Gamma>)"
          define \<gamma>' where
            "\<gamma>' = adapt_subst_to_renaming \<rho> \<gamma>"

          have C''_conv: "C'' = C' \<cdot> \<rho>"
            by (simp add: C''_def rename_clause_def \<rho>_def)

          have C''_restricted_\<gamma>': "C'' \<cdot> restrict_subst (vars_cls C'') \<gamma>' = C' \<cdot> \<gamma>"
            unfolding subst_cls_restrict_subst_idem[OF subset_refl] C''_conv \<gamma>'_def
          proof (rule subst_renaming_subst_adapted)
            show "is_renaming \<rho>"
              unfolding \<rho>_def
              by (metis S_def fin_N fin_learned_S finite_Un finite_clss_of_trail
                  is_renaming_renaming_wrt state_learned_simp)
          next
            show "vars_cls C' \<subseteq> subst_domain \<gamma>"
              using C_def C_in grounding_ground vars_cls_subset_subst_domain_if_grounding by blast
          qed
          
          have "conflict N \<beta> (\<Gamma>, U, None) (\<Gamma>, U, Some (C'', restrict_subst (vars_cls C'') \<gamma>'))"
          proof (rule conflictI)
            show "C' \<in> N \<union> U"
              using C'_in by simp
          next
            show "is_ground_cls (C'' \<cdot> restrict_subst (vars_cls C'') \<gamma>')"
              unfolding C''_restricted_\<gamma>'
              using C_def C_in grounding_ground by blast
          next
            show "trail_false_cls \<Gamma> (C'' \<cdot> restrict_subst (vars_cls C'') \<gamma>')"
              unfolding C''_restricted_\<gamma>'
              using C_def \<open>trail_false_cls \<Gamma> C\<close> by blast
          qed (simp_all add: C''_def subst_domain_restrict_subst)
          with no_new_conflict have False
            by (simp add: S_def u_def)
          thus "trail_true_cls \<Gamma> C" ..
        qed
      qed
      moreover have "satisfiable {C \<in> grounding_of_clss N. \<forall>L \<in># C. atm_of L \<prec>\<^sub>B \<beta>}"
        unfolding true_clss_def
      proof (intro exI ballI, unfold mem_Collect_eq, elim conjE)
        fix C
        have "trail_consistent \<Gamma>"
          using S_def trail_consistent by auto
        show "C \<in> grounding_of_clss N \<Longrightarrow> \<forall>L \<in># C. atm_of L \<prec>\<^sub>B \<beta> \<Longrightarrow> trail_interp \<Gamma> \<TTurnstile> C"
          using tr_true[unfolded S_def, simplified]
          using trail_interp_cls_if_trail_true[OF \<open>trail_consistent \<Gamma>\<close>]
          by (simp add: trail_true_clss_def)
      qed
      ultimately show ?thesis
        by (simp add: S_def)
    next
      fix S' S''
      assume deci: "decide N \<beta> S S'" and conf: "conflict N \<beta> S' S''"
      moreover have "\<forall>L\<in>fst ` set (state_trail S'). atm_of L \<prec>\<^sub>B \<beta>"
        by (rule decide_sound_state[OF deci sound_S, THEN trail_lt_if_sound_state])
      ultimately have "\<exists>S\<^sub>4. propagate N \<beta> S S\<^sub>4"
        using propagate_if_conflict_follows_decide[OF fin_N fin_learned_S _ no_new_conflict]
        by simp
      with no_new_propagate have False
        by blast
      thus ?thesis ..
    qed
  next
    case (Some Cl)
    then obtain C \<gamma> where u_def: "u = Some (C, \<gamma>)" by force

    from sound_S have disj_vars_conflict: "\<forall>D \<in> N \<union> U \<union> clss_of_trail \<Gamma>. disjoint_vars C D"
      by (simp add: S_def u_def sound_state_def)

    from sound_S have domain_\<gamma>: "subst_domain \<gamma> \<subseteq> vars_cls C"
      by (simp add: S_def u_def sound_state_def)

    from sound_S have \<Gamma>_false_C_\<gamma>: "trail_false_cls \<Gamma> (C \<cdot> \<gamma>)"
      by (simp add: S_def u_def sound_state_def)

    show ?thesis
    proof (cases "C = {#}")
      case True
      hence "\<not> satisfiable (grounding_of_clss N) \<and> (\<exists>\<gamma>. state_conflict S = Some ({#}, \<gamma>))"
        using S_def u_def not_satisfiable_if_sound_state_conflict_bottom[OF sound_S] by simp
      thus ?thesis by simp
    next
      case C_not_empty: False
      show ?thesis
      proof (cases \<Gamma>)
        case Nil
        with \<Gamma>_false_C_\<gamma> have False
          using C_not_empty by simp
        thus ?thesis ..
      next
        case (Cons Ln \<Gamma>')
        then obtain L n where \<Gamma>_def: "\<Gamma> = (L, n) # \<Gamma>'"
          by fastforce

        from regular_run have mempty_not_in_N: "{#} \<notin> N"
          using C_not_empty mempty_not_in_initial_clauses_if_regular_run_reaches_non_empty_conflict
          unfolding S_def state_conflict_simp u_def option.inject
          by simp

        show ?thesis
        proof (cases "- L \<in># C \<cdot> \<gamma>")
          case True \<comment> \<open>Literal cannot be skipped\<close>
          then obtain C' K where C_def: "C = C' + {#K#}" and K_\<gamma>: "K \<cdot>l \<gamma> = - L"
            by (metis Melem_subst_cls add.right_neutral multi_member_split
                union_mset_add_mset_right)
          hence L_eq_uminus_K_\<gamma>: "L = - (K \<cdot>l \<gamma>)"
            by simp

          show ?thesis
          proof (cases n)
            case None \<comment> \<open>Conflict clause can be backtracked\<close>
            hence \<Gamma>_def: "\<Gamma> = trail_decide \<Gamma>' (- (K \<cdot>l \<gamma>))"
              by (simp add: \<Gamma>_def L_eq_uminus_K_\<gamma> trail_decide_def)

            from \<Gamma>_def have \<Gamma>_def': "\<Gamma> = trail_decide (\<Gamma>' @ []) (- (K \<cdot>l \<gamma>))"
              by auto

            have no_new_new_conflict: "\<nexists>S'. conflict N \<beta> ([], insert (add_mset K C') U, None) S'"
              apply simp
              apply (intro allI notI)
              apply (erule conflict.cases)
              apply (simp add: )
              using mempty_not_in_N mempty_not_in_learned_S[unfolded S_def, simplified]
              by (metis C_def C_not_empty add_mset_add_single insertE not_trail_false_Nil(2)
                  rename_clause_def subst_cls_empty_iff)

            have "backtrack N \<beta> (\<Gamma>, U, Some (C' + {#K#}, \<gamma>)) ([], insert (add_mset K C') U, None)"
              by (rule backtrackI[OF \<Gamma>_def' no_new_new_conflict])

            with no_more_regular_step have False
              unfolding regular_scl_def reasonable_scl_def scl_def
              unfolding S_def[unfolded u_def C_def, symmetric]
              using backtrack_well_defined(2) by blast
            thus ?thesis ..
          next
            case Some \<comment> \<open>Literal can be resolved\<close>
            then obtain D L' \<sigma> where n_def: "n = Some (D, L', \<sigma>)"
              by (metis prod_cases3)
            with trail_propagate_wf have L_def: "L = L' \<cdot>l \<sigma>"
              by (simp add: \<Gamma>_def S_def trail_propagated_wf_def)
            hence 1: "\<Gamma> = trail_propagate \<Gamma>' L' D \<sigma> "
              using \<Gamma>_def n_def
              by (simp add: trail_propagate_def)

            have domain_\<sigma>: "subst_domain \<sigma> \<subseteq> vars_cls (add_mset L' D)"
              using trail_min_subst_dom
              by (simp add: S_def trail_minimal_subst_domains_def 1 trail_propagate_def)
            have ground_L'_D_\<sigma>: "is_ground_cls (add_mset L' D \<cdot> \<sigma>)"
              using trail_groundings
              by (simp add: S_def trail_groundings_def 1 trail_propagate_def)

            define \<rho> :: "'v \<Rightarrow> ('f, 'v) Term.term" where
              "\<rho> = renaming_wrt (N \<union> U \<union> clss_of_trail \<Gamma> \<union> {C' + {#K#}})"

            have *: "vars_cls (add_mset L' D) \<inter> vars_cls (add_mset K C') = {}"
              using disj_vars_conflict[unfolded C_def 1]
              by (simp add: disjoint_vars_iff_inter_empty inf.commute)

            have 2: "L' \<cdot>l \<sigma> = - (K \<cdot>l \<gamma>)"
              using K_\<gamma> L_def by fastforce
            hence "atm_of L' \<cdot>a \<sigma> = atm_of K \<cdot>a \<gamma>"
              by (metis atm_of_subst_lit atm_of_uminus)
            hence "atm_of L' \<cdot>a (\<sigma> \<odot> \<gamma>) = atm_of K \<cdot>a (\<sigma> \<odot> \<gamma>)"
              unfolding subst_subst_compose
            proof (rule subst_subst_eq_subst_subst_if_subst_eq_substI(1))
              show "vars_lit L' \<inter> subst_domain \<gamma> = {}"
                using * domain_\<gamma> disj_vars_conflict
                by (auto simp: C_def)
            next
              show "vars_lit K \<inter> subst_domain \<sigma> = {}"
                using * domain_\<sigma> disj_vars_conflict by auto
            next
              have "range_vars \<sigma> = {}"
                by (rule range_vars_eq_empty_if_is_ground[OF ground_L'_D_\<sigma> domain_\<sigma>])
              thus "range_vars \<sigma> \<inter> subst_domain \<gamma> = {}"
                by simp
            qed
            then obtain \<mu> where "Unification.mgu (atm_of L') (atm_of K) = Some \<mu>"
              using ex_mgu_if_subst_eq_subst by blast
            hence 3: "is_mimgu \<mu> {{atm_of L', atm_of K}}"
              by (rule is_mimgu_if_mgu_eq_Some)

            have "resolve N \<beta> (\<Gamma>, U, Some (C' + {#K#}, \<gamma>)) (\<Gamma>, U, Some ((C' + D) \<cdot> \<mu> \<cdot> \<rho>,
              restrict_subst (vars_cls ((C' + D) \<cdot> \<mu> \<cdot> \<rho>)) (inv_renaming' \<rho> \<odot> \<gamma> \<odot> \<sigma>)))"
              by (rule resolveI[OF 1 \<rho>_def 2 3])
            with no_more_regular_step have False
              unfolding regular_scl_def reasonable_scl_def scl_def
              using S_def \<Gamma>_def C_def decide_well_defined(5) u_def by blast
            thus ?thesis ..
          qed
        next
          case False \<comment> \<open>Literal can be skipped\<close>
          hence "skip N \<beta> ((L, n) # \<Gamma>', U, Some (C, \<gamma>)) (\<Gamma>', U, Some (C, \<gamma>))"
            by (rule skipI[of L C \<gamma> N \<beta> n \<Gamma>' U, OF _ C_not_empty])
          with no_more_regular_step have False
            by (metis S_def \<Gamma>_def local.scl_def reasonable_scl_def regular_scl_def
                skip_well_defined(2) u_def)
          thus ?thesis ..
        qed
      qed
    qed
  qed
qed

end

end