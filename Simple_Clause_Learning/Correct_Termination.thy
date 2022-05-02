theory Correct_Termination
  imports Simple_Clause_Learning
begin

context scl begin


lemma assumes "(regular_scl N)\<^sup>*\<^sup>* initial_state S" and "conflict N S S'"
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

lemma not_satisfiable_if_sound_state_conflict_bottom:
  assumes sound_S: "sound_state N S" and conflict_S: "state_conflict S = Some ({#}, \<gamma>)"
  shows "\<not> satisfiable (grounding_of_clss N)"
proof -
  from sound_S conflict_S have "N \<TTurnstile>\<G>e {{#}}"
    unfolding sound_state_def state_conflict_def by auto
  thus ?thesis by simp
qed

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

lemma trail_defined_lit_iff: "trail_defined_lit \<Gamma> L \<longleftrightarrow> atm_of L \<in> atm_of ` fst ` set \<Gamma>"
  by (simp add: atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set trail_defined_lit_def)

lemma "trail_interp \<Gamma> \<subseteq> atm_of ` fst ` set \<Gamma>"
  by (smt (verit, best) UN_iff image_iff insert_iff literal.case_eq_if singletonD subsetI trail_interp_def)

lemma set_filter_insert_conv:
  "{x \<in> insert y S. P x} = (if P y then insert y else id) {x \<in> S. P x}"
  by auto

lemma trail_interp_conv: "trail_interp \<Gamma> = atm_of ` {L \<in> fst ` set \<Gamma>. is_pos L}"
proof (induction \<Gamma>)
  case Nil
  show ?case by (simp add: trail_interp_def)
next
  case (Cons Ln \<Gamma>)
  then show ?case
    unfolding list.set image_insert set_filter_insert_conv trail_interp_Cons'
    by (simp add: literal.case_eq_if)
qed

lemma not_in_trail_interp_if_not_in_trail: "t \<notin> atm_of ` fst ` set \<Gamma> \<Longrightarrow> t \<notin> trail_interp \<Gamma>"
  by (metis (no_types, lifting) atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set
      literal.sel(2) mem_Collect_eq trail_interp_conv)

lemma trail_interp_lit_if_sound_and_trail_true:
  shows "sound_trail N U \<Gamma> \<Longrightarrow> trail_true_lit \<Gamma> L \<Longrightarrow> trail_interp \<Gamma> \<TTurnstile>l L"
proof (induction \<Gamma> rule: sound_trail.induct)
  case Nil
  thus ?case
    by (simp add: trail_true_lit_def)
next
  case (Cons \<Gamma> K u)
  show ?case
  proof (cases "L = K \<or> L = - K")
    case True
    then show ?thesis 
    proof (elim disjE)
      assume "L = K"
      thus ?thesis
      proof (cases L; cases K)
        fix t\<^sub>L t\<^sub>K
        from \<open>L = K\<close> show "L = Pos t\<^sub>L \<Longrightarrow> K = Pos t\<^sub>K \<Longrightarrow> ?thesis"
          by (simp add: trail_interp_def)
      next
        fix t\<^sub>L t\<^sub>K
        from \<open>L = K\<close> show "L = Neg t\<^sub>L \<Longrightarrow> K = Neg t\<^sub>K \<Longrightarrow> ?thesis"
          using Cons.hyps
          by (simp add: trail_defined_lit_iff trail_interp_Cons'
              not_in_trail_interp_if_not_in_trail)
      qed simp_all
    next
      assume "L = - K"
      then show ?thesis
      proof (cases L; cases K)
        fix t\<^sub>L t\<^sub>K
        from \<open>L = - K\<close> show "L = Pos t\<^sub>L \<Longrightarrow> K = Neg t\<^sub>K \<Longrightarrow> ?thesis"
          unfolding trail_interp_Cons'
          using Cons.hyps(1) Cons.prems
          by (metis (no_types, lifting) image_insert insertE list.simps(15) literal.distinct(1)
              prod.sel(1) trail_defined_lit_def trail_true_lit_def)
      next
        fix t\<^sub>L t\<^sub>K
        from \<open>L = - K\<close> show "L = Neg t\<^sub>L \<Longrightarrow> K = Pos t\<^sub>K \<Longrightarrow> ?thesis"
          unfolding trail_interp_Cons'
          using Cons.hyps(1) Cons.prems
          by (metis (no_types, lifting) image_insert insertE list.simps(15) literal.distinct(1)
              prod.sel(1) trail_defined_lit_def trail_true_lit_def)
      qed simp_all
    qed
  next
    case False
    with Cons.prems have "trail_true_lit \<Gamma> L"
      by (simp add: trail_true_lit_def)
    with Cons.IH have "trail_interp \<Gamma> \<TTurnstile>l L"
      by simp
    with False show ?thesis
      by (cases L; cases K) (simp_all add: trail_interp_def del: true_lit_iff)
  qed
qed

lemma trail_interp_cls_if_sound_and_trail_true:
  assumes "sound_trail N U \<Gamma>" and "trail_true_cls \<Gamma> C"
  shows "trail_interp \<Gamma> \<TTurnstile> C"
proof -
  from \<open>trail_true_cls \<Gamma> C\<close> obtain L where "L \<in># C" and "trail_true_lit \<Gamma> L"
    by (auto simp: trail_true_cls_def)
  show ?thesis
    unfolding true_cls_def
  proof (rule bexI[OF _ \<open>L \<in># C\<close>])
    show "trail_interp \<Gamma> \<TTurnstile>l L"
      by (rule trail_interp_lit_if_sound_and_trail_true[OF \<open>sound_trail N U \<Gamma>\<close> \<open>trail_true_lit \<Gamma> L\<close>])
  qed
qed

lemma set_removeAll_mset: "set_mset (removeAll_mset x M) = set_mset M - {x}"
  by simp

lemma trail_true_lit_Cons_iff: "trail_true_lit ((L, u) # \<Gamma>) K \<longleftrightarrow> L = K \<or> trail_true_lit \<Gamma> K"
  by (auto simp: trail_true_lit_def)

lemma trail_true_cls_Cons_iff: "trail_true_cls ((L, u) # \<Gamma>) C \<longleftrightarrow> L \<in># C \<or> trail_true_cls \<Gamma> C"
  by (auto simp: trail_true_cls_def trail_true_lit_Cons_iff)

lemma trail_true_cls_iff_trail_interp_entails:
  assumes "sound_trail N U \<Gamma>" "\<forall>L \<in># C. trail_defined_lit \<Gamma> L"
  shows "trail_true_cls \<Gamma> C \<longleftrightarrow> trail_interp \<Gamma> \<TTurnstile> C"
proof (rule iffI)
  assume "trail_true_cls \<Gamma> C"
  thus "trail_interp \<Gamma> \<TTurnstile> C"
    using assms(1) trail_interp_cls_if_sound_and_trail_true by blast
next
  assume "trail_interp \<Gamma> \<TTurnstile> C"
  then obtain L where "L \<in># C" and "trail_interp \<Gamma> \<TTurnstile>l L"
    by (auto simp: true_cls_def)
  show "trail_true_cls \<Gamma> C"
  proof (cases L)
    case (Pos t)
    hence "t \<in> trail_interp \<Gamma>"
      using \<open>trail_interp \<Gamma> \<TTurnstile>l L\<close> by simp
    then show ?thesis
      unfolding trail_true_cls_def
      using \<open>L \<in># C\<close> Pos
      by (metis assms(1) assms(2) trail_defined_lit_def trail_interp_lit_if_sound_and_trail_true
          trail_true_lit_def true_lit_simps(2) uminus_Pos)
  next
    case (Neg t)
    then show ?thesis
      by (metis \<open>L \<in># C\<close> \<open>trail_interp \<Gamma> \<TTurnstile>l L\<close> assms(1) assms(2) trail_defined_lit_def
          trail_interp_lit_if_sound_and_trail_true trail_true_cls_def trail_true_lit_def
          true_lit_simps(1) true_lit_simps(2) uminus_Neg)
  qed
qed

lemma trail_interp_clss_if_sound_and_trail_true:
  assumes "sound_trail N U \<Gamma>" and "trail_true_clss \<Gamma> CC"
  shows "trail_interp \<Gamma> \<TTurnstile>s CC"
  using \<open>trail_true_clss \<Gamma> CC\<close> trail_interp_cls_if_sound_and_trail_true[OF \<open>sound_trail N U \<Gamma>\<close>]
  by (simp add: trail_true_clss_def true_clss_def)

lemma
  assumes
    fin_N: "finite N" and disj_N: "disjoint_vars_set N" and
    regular_run: "(regular_scl N)\<^sup>*\<^sup>* initial_state S" and
    no_more_regular_step: "\<nexists>S'. regular_scl N S S'"
  shows "\<not> satisfiable (grounding_of_clss N) \<and> (\<exists>\<gamma>. state_conflict S = Some ({#}, \<gamma>)) \<or>
  (\<exists>\<gamma>. trail_true_clss (state_trail S) (N \<cdot>cs \<gamma>))"
proof -
  obtain \<Gamma> U u where S_def: "S = (\<Gamma>, U, u)"
    using prod_cases3 by blast

  have sound_S: "sound_state N S"
    using regular_run_sound_state[OF regular_run] sound_initial_state[OF fin_N disj_N] by blast

  from no_more_regular_step have no_new_conflict: "\<nexists>S'. conflict N S S'"
    using regular_scl_def by blast

  from no_more_regular_step have no_propagate: "\<nexists>S'. propagate N S S'"
    by (meson decide_well_defined(1) local.scl_def reasonable_scl_def regular_scl_def)

  from no_more_regular_step have
    no_reasonable_decide: "(\<nexists>S'. decide N S S') \<or> (\<exists>S' S''. decide N S S' \<and> conflict N S' S'')"
    using local.scl_def reasonable_scl_def regular_scl_def by blast

  show ?thesis
  proof (cases u)
    case None
    hence "state_conflict S = None"
      by (simp add: S_def)
    
    have ball_N_not_empty: "\<forall>C \<in> N. C \<noteq> {#}" sorry

    have "satisfiable (grounding_of_clss N)"
      using trail_interp_clss_if_sound_and_trail_true[OF ]
      (* using sound_S[unfolded S_def None] *)
      apply (rule exI[where x = "trail_interp \<Gamma>"])
      unfolding true_clss_def true_cls_def grounding_of_clss_def grounding_of_cls_def
      unfolding imp_ex ball_UN ball_simps
            
      unfolding sound_state_def
      sorry
    moreover have "\<exists>\<gamma>. trail_true_clss \<Gamma> (N \<cdot>cs \<gamma>)"
      using no_more_regular_step
      unfolding S_def[unfolded None]
      unfolding regular_scl_def
      sorry
    ultimately show ?thesis
      unfolding S_def[unfolded None] state_trail_def state_conflict_def prod.sel
      by simp
  next
    case (Some Cl)
    then obtain C \<gamma> where u_def: "u = Some (C, \<gamma>)" by force
    show ?thesis
    proof (cases "C = {#}")
      case True
      hence "\<not> satisfiable (grounding_of_clss N) \<and> (\<exists>\<gamma>. state_conflict S = Some ({#}, \<gamma>))"
        using S_def u_def not_satisfiable_if_sound_state_conflict_bottom[OF sound_S] by simp
      thus ?thesis by simp
    next
      case False
      then obtain L C' where C_def: "C = C' + {#L#}"
        by (metis add_mset_add_single multi_nonempty_split)

      from no_more_regular_step have "\<nexists>S'. (reasonable_scl N)\<^sup>+\<^sup>+ (\<Gamma>, U, Some (C' + {#L#}, \<gamma>)) S'"
        unfolding S_def u_def C_def
        unfolding regular_scl_def
        sorry

      then have False
        unfolding reasonable_scl_def
        sorry

      then show ?thesis by simp
    qed
  qed
  oops

end

end