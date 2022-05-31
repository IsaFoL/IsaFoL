theory Correct_Termination
  imports Simple_Clause_Learning
begin

context scl begin

(* lemma assumes "(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S" and "conflict N \<beta> S S'"
  shows "\<exists>C \<gamma>. state_conflict S' = Some (C, \<gamma>) \<and>
    (trail_level_cls (state_trail S) (C \<cdot> \<gamma>) = trail_level (state_trail S))"
  using \<open>conflict N S S'\<close>
proof (cases N S S' rule: conflict.cases)
  case (conflictI D U D' \<Gamma> \<gamma>)
  show ?thesis
  proof (intro exI conjI)
    show "state_conflict S' = Some (D', \<gamma>)"
      using conflictI by simp
  next
    show "trail_level_cls (state_trail S) (D' \<cdot> \<gamma>) = trail_level (state_trail S)"
    proof (cases "D' \<cdot> \<gamma>")
      case empty
      hence "D' = {#}"
        using subst_cls_empty_iff by blast
      hence "D = {#}"
        by (simp add: local.conflictI(4) rename_clause_def)
      hence "{#} \<in> N \<union> U" 
        using local.conflictI(3) by force
      then show ?thesis
    oops

lemma
  assumes "\<forall>C \<in> N. C \<noteq> {#}" and "(regular_scl N)\<^sup>*\<^sup>* initial_state S" and "conflict N S S'"
  shows "\<exists>\<Gamma> L C \<gamma>. state_trail S = trail_propagate \<Gamma> L C \<gamma>"
  using assms(2,3)
proof (induction S rule: rtranclp_induct)
  case base
  then obtain D D'  \<sigma> where
       "D \<in> N" and "D' = rename_clause N D" and "trail_false_cls [] (D' \<cdot> \<sigma>)"
    by (auto elim: conflict.cases)

  from \<open>\<forall>C \<in> N. C \<noteq> {#}\<close> and \<open>D \<in> N\<close> have "D \<noteq> {#}"
    by simp
  hence "D' \<cdot> \<sigma> \<noteq> {#}"
    by (simp add: \<open>D' = rename_clause N D\<close> rename_clause_def)
  hence "\<not> trail_false_cls [] (D' \<cdot> \<sigma>)"
    by (rule not_trail_false_Nil(2))
  with \<open>trail_false_cls [] (D' \<cdot> \<sigma>)\<close> have False
    by simp
  thus ?case ..
next
  case (step S S'')
  from step.hyps have "regular_scl N S S''" by simp
  with \<open>conflict N S'' S'\<close> have "\<not> conflict N S S''" and "reasonable_scl N S S''"
    unfolding HOL.atomize_conj
    by (smt (verit, best) conflict.cases option.distinct(1) prod.inject reasonable_if_regular)
  hence "scl N S S''" and "decide N S S'' \<longrightarrow> \<not> (\<exists>S'''. conflict N S'' S''')"
    by (simp_all add: reasonable_scl_def)

  from \<open>scl N S S''\<close> show ?case
    unfolding scl_def
  proof (elim disjE)
    assume "propagate N S S''"
    thus ?thesis
      by (elim propagate.cases) auto
  next
    assume "decide N S S''"
    with \<open>conflict N S'' S'\<close> have False
      using \<open>decide N S S'' \<longrightarrow> \<not> (\<exists>S'''. conflict N S'' S''')\<close> by fast
    thus ?thesis ..
  next
    assume "conflict N S S''"
    with \<open>\<not> conflict N S S''\<close> have False ..
    thus ?thesis ..
  next
    assume "skip N S S''"
    with \<open>conflict N S'' S'\<close> have False
      by (elim skip.cases conflict.cases) simp
    thus ?thesis ..
  next
    assume "factorize N S S''"
    with \<open>conflict N S'' S'\<close> have False
      by (elim factorize.cases conflict.cases) simp
    thus ?thesis ..
  next
    assume "resolve N S S''"
    with \<open>conflict N S'' S'\<close> have False
      by (elim resolve.cases conflict.cases) simp
    thus ?thesis ..
  next
    assume "backtrack N S S''"
    then have False
      apply (elim backtrack.cases)
      oops

lemma
  assumes "(regular_scl N)\<^sup>*\<^sup>* initial_state S" and "conflict N S S'"
  shows "\<exists>S''. (\<lambda>S S'. skip N S S' \<or> factorize N S S')\<^sup>*\<^sup>* S' S'' \<and> resolve N S S'"
proof -  
  oops

lemma
  assumes sound: "sound_state N (\<Gamma>, U, Some (C' + {#L#}, \<gamma>))"
  shows
    "(\<exists>S'. skip N (\<Gamma>, U, Some (C' + {#L#}, \<gamma>)) S') \<or>
    (\<exists>S'. factorize N (\<Gamma>, U, Some (C' + {#L#}, \<gamma>)) S') \<or>
    (\<exists>S'. resolve N (\<Gamma>, U, Some (C' + {#L#}, \<gamma>)) S') \<or>
    (\<exists>S'. backtrack N (\<Gamma>, U, Some (C' + {#L#}, \<gamma>)) S')"
proof (cases \<Gamma>)
  case Nil
  from sound have "trail_false_cls \<Gamma> ((C' + {#L#}) \<cdot> \<gamma>)"
    by (simp add: sound_state_def)
  hence "trail_false_lit \<Gamma> (L \<cdot>l \<gamma>)"
    by (simp add: trail_false_cls_def)
  hence False
    unfolding trail_false_lit_def Nil by simp
  thus ?thesis
    by simp
next
  case (Cons Ln \<Gamma>')
  then obtain L n where Ln_def: "Ln = (L, n)" by force
  show ?thesis
  proof (cases n)
    case None
    show ?thesis
      unfolding Cons Ln_def None
      apply (simp add: skip.simps trail_propagate_def resolve.simps)
      unfolding backtrack.simps
      apply (simp add: is_decision_lit_def)
  oops

lemma ball_trail_defined_lit_if:
  assumes
    no_conflict: "state_conflict S = None" and
    no_decide: "\<nexists>S'. decide N S S'"
  shows "\<forall>C \<in> N. \<forall>L \<in># C. \<forall>\<gamma>. is_ground_lit (L \<cdot>l \<gamma>) \<longrightarrow> trail_defined_lit (state_trail S) (L \<cdot>l \<gamma>)"
proof (intro ballI allI impI)
  fix C L \<gamma>
  assume "C \<in> N" "L \<in># C" "is_ground_lit (L \<cdot>l \<gamma>)"

  from no_conflict obtain \<Gamma> U where S_def: "S = (\<Gamma>, U, None)"
    by (metis prod_cases3 state_conflict_simp)

  show "trail_defined_lit (state_trail S) (L \<cdot>l \<gamma>)"
    using no_decide
  proof (rule contrapos_np)
    assume assm: "\<not> trail_defined_lit (state_trail S) (L \<cdot>l \<gamma>)"
    show "\<exists>S'. decide N S S'"
      using decideI[OF \<open>is_ground_lit (L \<cdot>l \<gamma>)\<close> assm]
      unfolding S_def state_trail_simp
      by fastforce
  qed
qed

lemma set_removeAll_mset: "set_mset (removeAll_mset x M) = set_mset M - {x}"
  by simp

lemma trail_true_lit_Cons_iff: "trail_true_lit ((L, u) # \<Gamma>) K \<longleftrightarrow> L = K \<or> trail_true_lit \<Gamma> K"
  by (auto simp: trail_true_lit_def)

lemma trail_true_cls_Cons_iff: "trail_true_cls ((L, u) # \<Gamma>) C \<longleftrightarrow> L \<in># C \<or> trail_true_cls \<Gamma> C"
  by (auto simp: trail_true_cls_def trail_true_lit_Cons_iff)

lemma trail_interp_clss_if_sound_and_trail_true:
  assumes "sound_trail N U \<Gamma>" and "trail_true_clss \<Gamma> CC"
  shows "trail_interp \<Gamma> \<TTurnstile>s CC"
  using \<open>trail_true_clss \<Gamma> CC\<close> trail_interp_cls_if_sound_and_trail_true[OF \<open>sound_trail N U \<Gamma>\<close>]
  by (simp add: trail_true_clss_def true_clss_def)
 *)

lemma not_satisfiable_if_sound_state_conflict_bottom:
  assumes sound_S: "sound_state N S" and conflict_S: "state_conflict S = Some ({#}, \<gamma>)"
  shows "\<not> satisfiable (grounding_of_clss N)"
proof -
  from sound_S conflict_S have "N \<TTurnstile>\<G>e {{#}}"
    unfolding sound_state_def state_conflict_def by auto
  thus ?thesis by simp
qed

definition adapt_subst_to_renaming where
  "adapt_subst_to_renaming \<rho> \<sigma> x =
    (if x \<in> the_Var ` \<rho> ` subst_domain \<sigma> then
      \<sigma> (the_inv \<rho> (Var x))
    else
      Var x)"

lemma subst_lit_renaming_subst_adapted:
  assumes ren_\<rho>: "is_renaming \<rho>" and vars_L: "vars_lit L \<subseteq> subst_domain \<sigma>"
  shows "L \<cdot>l \<rho> \<cdot>l adapt_subst_to_renaming \<rho> \<sigma> = L \<cdot>l \<sigma>"
  unfolding subst_lit_comp_subst[symmetric]
proof (intro same_on_vars_lit ballI)
  fix x assume "x \<in> vars_lit L"
  with vars_L have x_in: "x \<in> subst_domain \<sigma>"
    by blast

  obtain x' where \<rho>_x: "\<rho> x = Var x'"
    using ren_\<rho>[unfolded is_renaming_iff]
    by (meson is_Var_def)
  with x_in have x'_in: "x' \<in> the_Var ` \<rho> ` subst_domain \<sigma>"
    by (metis image_eqI term.sel(1))

  have "(\<rho> \<odot> adapt_subst_to_renaming \<rho> \<sigma>) x = \<rho> x \<cdot>a adapt_subst_to_renaming \<rho> \<sigma>"
    by (simp add: subst_compose_def)
  also have "... = adapt_subst_to_renaming \<rho> \<sigma> x'"
    using \<rho>_x by simp
  also have "... = \<sigma> (the_inv \<rho> (Var x'))"
    by (simp add: adapt_subst_to_renaming_def if_P[OF x'_in])
  also have "... = \<sigma> (the_inv \<rho> (\<rho> x))"
    by (simp add: \<rho>_x)
  also have "... = \<sigma> x"
    using ren_\<rho>[unfolded is_renaming_iff]
    by (simp add: the_inv_f_f)
  finally show "(\<rho> \<odot> adapt_subst_to_renaming \<rho> \<sigma>) x = \<sigma> x"
    by simp
qed

lemma subst_renaming_subst_adapted:
  assumes ren_\<rho>: "is_renaming \<rho>" and vars_D: "vars_cls D \<subseteq> subst_domain \<sigma>"
  shows "D \<cdot> \<rho> \<cdot> adapt_subst_to_renaming \<rho> \<sigma> = D \<cdot> \<sigma>"
  unfolding subst_cls_comp_subst[symmetric]
proof (intro same_on_lits_clause ballI)
  fix L assume "L \<in># D"
  with vars_D have "vars_lit L \<subseteq> subst_domain \<sigma>"
    by (auto dest!: multi_member_split)
  thus "L \<cdot>l (\<rho> \<odot> adapt_subst_to_renaming \<rho> \<sigma>) = L \<cdot>l \<sigma>"
    unfolding subst_lit_comp_subst
    by (rule subst_lit_renaming_subst_adapted[OF ren_\<rho>])
qed

lemma vars_cls_subset_subst_domain_if_grounding:
  assumes "is_ground_cls (C \<cdot> \<sigma>)"
  shows "vars_cls C \<subseteq> subst_domain \<sigma>"
proof (rule Set.subsetI)
  fix x assume "x \<in> vars_cls C"
  thus "x \<in> subst_domain \<sigma>"
    unfolding subst_domain_def mem_Collect_eq
    by (metis assms empty_iff is_ground_atm_iff_vars_empty is_ground_cls_is_ground_on_var
        term.set_intros(3))
qed

lemma vars_lit_subst_subset_vars_cls_substI[intro]:
  "vars_lit L \<subseteq> vars_cls C \<Longrightarrow> vars_lit (L \<cdot>l \<sigma>) \<subseteq> vars_cls (C \<cdot> \<sigma>)"
  by (metis subset_Un_eq subst_cls_add_mset vars_cls_add_mset vars_subst_cls_eq)

lemma ball_image_mset: "(\<forall>x \<in># image_mset f M. P x) \<longleftrightarrow> (\<forall>x \<in># M. P (f x))"
  by blast

lemma ball_filter_mset: "(\<forall>x \<in># filter_mset P M. Q x) \<longleftrightarrow> (\<forall>x \<in># M. P x \<longrightarrow> Q x)"
  by fastforce

lemma set_list_of_mset[simp]: "set (list_of_mset M) = set_mset M"
  by (rule set_mset_mset[of "list_of_mset _", unfolded mset_list_of_mset, symmetric])

lemma ex_unify_if_unifiers_not_empty:
  "unifiers es \<noteq> {} \<Longrightarrow> set xs = es \<Longrightarrow> \<exists>ys. unify xs [] = Some ys"
  using unify_complete by auto

lemma not_empty_if_mem: "x \<in> X \<Longrightarrow> X \<noteq> {}"
  by blast

lemma propagate_if_conflict_follows_decide:
  assumes
    fin_N: "finite N" and fin_learned: "finite (state_learned S\<^sub>0)" and
    no_conf: "\<nexists>S\<^sub>1. conflict N \<beta> S\<^sub>0 S\<^sub>1" and deci: "decide N \<beta> S\<^sub>0 S\<^sub>2" and conf: "conflict N \<beta> S\<^sub>2 S\<^sub>3"
  shows "\<exists>S\<^sub>4. propagate N \<beta> S\<^sub>0 S\<^sub>4"
proof -
  from deci obtain L \<gamma> \<Gamma> U where
    S\<^sub>0_def: "S\<^sub>0 = (\<Gamma>, U, None)" and
    S\<^sub>2_def: "S\<^sub>2 = (trail_decide \<Gamma> (L \<cdot>l \<gamma>), U, None)" and
    "L \<in> \<Union> (set_mset ` N)" and
    "is_ground_lit (L \<cdot>l \<gamma>)" and
    "\<not> trail_defined_lit \<Gamma> (L \<cdot>l \<gamma>)"
    by (elim decide.cases) blast
  with conf obtain D D' \<sigma> where
    S\<^sub>3_def: "S\<^sub>3 = (trail_decide \<Gamma> (L \<cdot>l \<gamma>), U, Some (D', \<sigma>))" and
    D_in: "D \<in> N \<union> U" and
    D'_def: "D' = rename_clause (N \<union> U \<union> clss_of_trail (trail_decide \<Gamma> (L \<cdot>l \<gamma>))) D" and
    "subst_domain \<sigma> \<subseteq> vars_cls D'" and
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

  from D_in D'_def ground_D'_\<sigma> tr_\<Gamma>_L_false_D' obtain \<sigma>' where
    "is_ground_cls (D \<cdot> \<sigma>')" and "trail_false_cls ((L \<cdot>l \<gamma>, None) # \<Gamma>) (D \<cdot> \<sigma>')"
    unfolding trail_decide_def by (metis rename_clause_def subst_cls_comp_subst)
  moreover have
    nex_false_grounding: "\<nexists>\<sigma>. is_ground_cls (D \<cdot> \<sigma>) \<and> trail_false_cls \<Gamma> (D \<cdot> \<sigma>)"
    unfolding not_ex de_Morgan_conj
  proof (rule allI)
    fix \<delta>
    from no_conf[simplified, rule_format, of \<Gamma> U "Some (D', restrict_subst (vars_cls D')
      (adapt_subst_to_renaming (renaming_wrt (N \<union> U \<union> clss_of_trail (trail_decide \<Gamma> (L \<cdot>l \<gamma>))))
        (restrict_subst (vars_cls D) \<delta>)))"]
    show "\<not> is_ground_cls (D \<cdot> \<delta>) \<or> \<not> trail_false_cls \<Gamma> (D \<cdot> \<delta>)"
      apply (simp add: D'_def rename_clause_def conflict.simps S\<^sub>0_def subst_cls_restrict_subst_idem subst_domain_restrict_subst)
      using subst_renaming_subst_adapted[OF is_renaming_wrt_N_U_\<Gamma>_L, of D "restrict_subst (vars_cls D) \<delta>"]
      by (smt (verit) D'_def S\<^sub>0_def S\<^sub>3_def
          \<open>\<And>thesis. (\<And>D D' \<sigma>. \<lbrakk>S\<^sub>3 = (trail_decide \<Gamma> (L \<cdot>l \<gamma>), U, Some (D', \<sigma>)); D \<in> N \<union> U; D' = rename_clause (N \<union> U \<union> clss_of_trail (trail_decide \<Gamma> (L \<cdot>l \<gamma>))) D; subst_domain \<sigma> \<subseteq> vars_cls D'; is_ground_cls (D' \<cdot> \<sigma>); trail_false_cls (trail_decide \<Gamma> (L \<cdot>l \<gamma>)) (D' \<cdot> \<sigma>)\<rbrakk> \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close>
          \<open>\<not> conflict N \<beta> S\<^sub>0 (\<Gamma>, U, Some (D', restrict_subst (vars_cls D') (adapt_subst_to_renaming (renaming_wrt (N \<union> U \<union> clss_of_trail (trail_decide \<Gamma> (L \<cdot>l \<gamma>)))) (restrict_subst (vars_cls D) \<delta>))))\<close>
          clss_of_trail_trail_decide conflict.intros equalityD1 option.inject prod.simps(1)
          rename_clause_def vars_cls_subset_subst_domain_if_grounding subst_cls_restrict_subst_idem
          subst_domain_restrict_subst)
  qed
  ultimately have "- (L \<cdot>l \<gamma>) \<in># D \<cdot> \<sigma>'"
    using subtrail_falseI by blast
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
    using nex_false_grounding[simplified, rule_format, of "\<rho> \<odot> _", simplified]
    unfolding 1[unfolded rename_clause_def, folded \<rho>_def, symmetric]
    by simp

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
    unfolding subst_cls_def ball_image_mset ball_filter_mset
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

  let ?xs =
    "map atm_of (list_of_mset (add_mset (L' \<cdot>l \<rho>) {#K \<in># D'' \<cdot> \<rho>. K \<cdot>l \<sigma>''' = L' \<cdot>l \<rho> \<cdot>l \<sigma>'''#}))"

  have "unifiers (set (pairs ?xs)) \<noteq> {}"
  proof (rule not_empty_if_mem)
    show "\<sigma>''' \<in> unifiers (set (pairs ?xs))"
      unfolding subst_cls_def[of D'']
      unfolding image_mset_filter_mset_swap[symmetric]
      unfolding subst_cls_def[symmetric]
      unfolding unifiers_def mem_Collect_eq
      unfolding set_pairs list.set_map set_list_of_mset
      unfolding split_paired_Ball_Sigma prod.sel
      unfolding set_mset_add_mset_insert image_insert
      unfolding subst_cls_def set_image_mset set_mset_filter
      by (smt (verit, ccfv_SIG) image_iff insert_iff mem_Collect_eq subst_atm_of_eqI)
  qed

  then obtain ys where
    unify_pairs: "unify (pairs ?xs) [] = Some ys"
    using ex_unify_if_unifiers_not_empty[OF _ refl]
    by blast

  define \<mu> where
    "\<mu> = subst_of ys"

  have 6: "is_mimgu \<mu>
    {atm_of ` set_mset (add_mset (L' \<cdot>l \<rho>) {#K \<in># D'' \<cdot> \<rho>. K \<cdot>l \<sigma>''' = L' \<cdot>l \<rho> \<cdot>l \<sigma>'''#})}"
  proof (intro is_mimgu_if_mgu_sets[unfolded mgu_sets_def] exI conjI)
    show "set (map set [?xs]) = {atm_of ` set_mset
      (add_mset (L' \<cdot>l \<rho>) {#K \<in># D'' \<cdot> \<rho>. K \<cdot>l \<sigma>''' = L' \<cdot>l \<rho> \<cdot>l \<sigma>'''#})}"
      by simp
  next
    show "map_option subst_of (unify (concat (map pairs
      [map atm_of (list_of_mset (add_mset (L' \<cdot>l \<rho>) {#K \<in># D'' \<cdot> \<rho>. K \<cdot>l \<sigma>''' = L' \<cdot>l \<rho> \<cdot>l \<sigma>'''#}))]))
      []) = Some \<mu>"
      by (simp add: unify_pairs \<mu>_def)
  qed

  have 7: "\<forall>K\<in>#add_mset (L' \<cdot>l \<rho>) (D'' \<cdot> \<rho>) \<cdot> \<sigma>'''. K \<prec>\<^sub>B \<beta>"
    sorry

  show ?thesis
    using propagateI[OF D_in 1 2 3 refl refl 4 5 6 refl 7]
    unfolding S\<^sub>0_def by blast
qed

lemma ex_mgu_if_subst_eq_subst:
  assumes "t \<cdot>a \<sigma> = u \<cdot>a \<sigma>"
  shows "\<exists>\<mu>. Unification.mgu t u = Some \<mu>"
proof -
  from assms have "unifiers {(t, u)} \<noteq> {}"
    unfolding unifiers_def by auto
  then obtain xs where unify: "unify [(t, u)] [] = Some xs"
    using ex_unify_if_unifiers_not_empty[of "{(t, u)}" "[(t, u)]"]
    by auto

  show ?thesis
  proof (rule exI)
    show "Unification.mgu t u = Some (subst_of xs)"
      using unify
      by (simp add: Unification.mgu.simps)
  qed
qed

lemma range_vars_eq_empty_if_is_ground:
  "is_ground_cls (C \<cdot> \<gamma>) \<Longrightarrow> subst_domain \<gamma> \<subseteq> vars_cls C \<Longrightarrow> range_vars \<gamma> = {}"
  unfolding range_vars_def UNION_empty_conv subst_range.simps is_ground_cls_iff_vars_empty
  by (metis (no_types, opaque_lifting) dual_order.eq_iff imageE is_ground_atm_iff_vars_empty
      is_ground_cls_iff_vars_empty is_ground_cls_is_ground_on_var
      vars_cls_subset_subst_domain_if_grounding)

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

definition conflict_grounding where
  "conflict_grounding u \<longleftrightarrow> (case u of None \<Rightarrow> True | Some (C, \<gamma>) \<Rightarrow> is_ground_cls (C \<cdot> \<gamma>))"

lemma "sound_state N S \<Longrightarrow> conflict_grounding (state_conflict S)"
  by (cases "state_conflict S") (auto simp add: sound_state_def conflict_grounding_def)

definition conflict_minimal_subst_domain where
  "conflict_minimal_subst_domain u \<longleftrightarrow>
    (case u of None \<Rightarrow> True | Some (C, \<gamma>) \<Rightarrow> subst_domain \<gamma> \<subseteq> vars_cls C)"

lemma conflict_if_mempty_in_initial_clauses_and_no_conflict:
  assumes "{#} \<in> N" and "state_conflict S = None"
  shows "conflict N \<beta> S (state_trail S, state_learned S, Some ({#}, Var))"
proof -
  from assms(2) obtain \<Gamma> U where S_def: "S = (\<Gamma>, U, None)"
    by (metis snd_conv state_conflict_def surj_pair)

  show ?thesis
    unfolding S_def state_trail_simp state_learned_simp
  proof (rule conflictI[of "{#}" N _ _ _ Var])
    from assms(1) show "{#} \<in> N \<union> U"
      by simp
  qed simp_all
qed

lemma conflict_initial_state_if_mempty_in_intial_clauses:
  "{#} \<in> N \<Longrightarrow> conflict N \<beta> initial_state ([], {}, Some ({#}, Var))"
  using conflict_if_mempty_in_initial_clauses_and_no_conflict by auto

lemma conflict_initial_state_only_with_mempty:
  assumes "conflict N \<beta> initial_state S"
  shows "S = ([], {}, Some ({#}, Var))"
  using assms(1)
proof (cases rule: conflict.cases)
  case (conflictI D D' \<sigma>)

  from \<open>trail_false_cls [] (D' \<cdot> \<sigma>)\<close> have "D' \<cdot> \<sigma> = {#}"
    using not_trail_false_Nil(2) by blast
  hence "D' = {#}"
    by simp
  moreover with \<open>subst_domain \<sigma> \<subseteq> vars_cls D'\<close> have "\<sigma> = Var"
    using subst_ident_if_not_in_domain by fastforce
  ultimately show ?thesis
    using \<open>S = ([], {}, Some (D', \<sigma>))\<close> by simp
qed

lemma no_more_step_if_conflict_mempty:
  assumes "state_conflict S = Some ({#}, \<gamma>)"
  shows "\<not> (\<exists>S'. scl N \<beta> S S')"
  apply (rule notI)
  unfolding scl_def
  apply (insert assms)
  by (elim exE disjE propagate.cases decide.cases conflict.cases skip.cases factorize.cases
      resolve.cases backtrack.cases) simp_all
  

lemma mempty_not_in_initial_clauses_if_regular_run_reaches_non_empty_conflict:
  assumes "(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S" and "state_conflict S = Some (C, \<gamma>)" and "C \<noteq> {#}"
  shows "{#} \<notin> N"
proof (rule notI)
  from assms(2) have "initial_state \<noteq> S" by fastforce
  then obtain S' where
    reg_scl_init_S': "regular_scl N \<beta> initial_state S'" and "(regular_scl N \<beta>)\<^sup>*\<^sup>* S' S"
    by (metis assms(1) converse_rtranclpE)

  assume "{#} \<in> N"
  hence "conflict N \<beta> initial_state ([], {}, Some ({#}, Var))"
    by (rule conflict_initial_state_if_mempty_in_intial_clauses)
  hence conf_init: "regular_scl N \<beta> initial_state ([], {}, Some ({#}, Var))"
    using regular_scl_def by blast
  hence S'_def: "S' = ([], {}, Some ({#}, Var))"
    using reg_scl_init_S'
    unfolding regular_scl_def
    using \<open>conflict N \<beta> initial_state ([], {}, Some ({#}, Var))\<close>
      conflict_initial_state_only_with_mempty
    by blast

  have "\<nexists>S'. scl N \<beta> ([], {}, Some ({#}, Var)) S'"
    by (rule no_more_step_if_conflict_mempty) simp
  hence "\<nexists>S'. regular_scl N \<beta> ([], {}, Some ({#}, Var)) S'"
    using scl_if_reasonable[OF reasonable_if_regular] by blast
  hence "S = S'"
    using \<open>(regular_scl N \<beta>)\<^sup>*\<^sup>* S' S\<close> unfolding S'_def
    by (metis converse_rtranclpE)
  with assms(2,3) show False by (simp add: S'_def)
qed

lemma
  assumes
    fin_N: "finite N" and fin_learned_S: "finite (state_learned S)" and
    disj_N: "disjoint_vars_set N" and
    (* conflict_min_subst_dom: "conflict_minimal_subst_domain (state_conflict S)" and *)
    sound_S: "sound_state N S" and
    (* sound_trail_S: "sound_trail N (state_learned S) (state_trail S)" and *)
    regular_run: "(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S" and
    no_more_regular_step: "\<nexists>S'. regular_scl N \<beta> S S'"
  shows "\<not> satisfiable (grounding_of_clss N) \<and> (\<exists>\<gamma>. state_conflict S = Some ({#}, \<gamma>)) \<or>
    satisfiable {C \<in> grounding_of_clss N. multp (\<prec>\<^sub>B) C {#\<beta>#}} \<and>
      trail_true_clss (state_trail S) {C \<in> grounding_of_clss N. multp (\<prec>\<^sub>B) C {#\<beta>#}}"
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

  from sound_S have sound_\<Gamma>: "sound_trail N U \<Gamma>"
    by (simp add: S_def sound_state_def)

  have sound_S: "sound_state N S"
    using regular_run_sound_state[OF regular_run] sound_initial_state[OF fin_N disj_N] by blast

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

      have tr_true: "trail_true_clss \<Gamma> {C \<in> grounding_of_clss N. multp (\<prec>\<^sub>B) C {#\<beta>#}}"
        unfolding trail_true_clss_def
      proof (rule ballI, unfold mem_Collect_eq, erule conjE)
        fix C assume C_in: "C \<in> grounding_of_clss N" and C_lt_\<beta>: "multp (\<prec>\<^sub>B) C {#\<beta>#}"

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
            show "L' \<cdot>l \<gamma> \<prec>\<^sub>B \<beta>"
              unfolding \<open>L = L' \<cdot>l \<gamma>\<close>[symmetric]
              by (rule multp_singleton_rightD[OF C_lt_\<beta> transp_less_B L_in])
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
      moreover have "satisfiable {C \<in> grounding_of_clss N. multp (\<prec>\<^sub>B) C {#\<beta>#}}"
        unfolding true_clss_def
      proof (intro exI ballI, unfold mem_Collect_eq, elim conjE)
        fix C
        have "trail_consistent \<Gamma>"
          using S_def trail_consistent by auto
        show "C \<in> grounding_of_clss N \<Longrightarrow> multp (\<prec>\<^sub>B) C {#\<beta>#} \<Longrightarrow> trail_interp \<Gamma> \<TTurnstile> C"
          using tr_true[unfolded S_def, simplified]
          using trail_interp_cls_if_trail_true[OF \<open>trail_consistent \<Gamma>\<close>]
          by (simp add: trail_true_clss_def)
      qed
      ultimately show ?thesis
        by (simp add: S_def)
    next
      fix S' S''
      assume "decide N \<beta> S S'" and "conflict N \<beta> S' S''"
      hence "\<exists>S\<^sub>4. propagate N \<beta> S S\<^sub>4"
        by (rule propagate_if_conflict_follows_decide[OF fin_N fin_learned_S no_new_conflict])
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