theory Non_Redundancy
  imports
    Simple_Clause_Learning
    Trail_Induced_Ordering
    Initial_Literals_Generalize_Learned_Literals
begin

context scl begin

section \<open>Reasonable Steps\<close>

definition reasonable_scl where
  "reasonable_scl N \<beta> S S' \<longleftrightarrow>
    scl N \<beta> S S' \<and> (decide N \<beta> S S' \<longrightarrow> \<not>(\<exists>S''. conflict N \<beta> S' S''))"

lemma scl_if_reasonable: "reasonable_scl N \<beta> S S' \<Longrightarrow> scl N \<beta> S S'"
  unfolding reasonable_scl_def scl_def by simp

lemma reasonable_scl_sound_state:
  "reasonable_scl N \<beta> S S' \<Longrightarrow> sound_state N \<beta> S \<Longrightarrow> sound_state N \<beta> S'"
  using scl_preserves_sound_state reasonable_scl_def by blast

lemma reasonable_run_sound_state:
  "(reasonable_scl N \<beta>)\<^sup>*\<^sup>* S S' \<Longrightarrow> sound_state N \<beta> S \<Longrightarrow> sound_state N \<beta> S'"
  by (smt (verit, best) reasonable_scl_sound_state rtranclp_induct)


subsection \<open>Invariants\<close>


subsubsection \<open>No Conflict After Decide\<close>

inductive no_conflict_after_decide for N \<beta> U where
  Nil[simp]: "no_conflict_after_decide N \<beta> U []" |
  Cons: "(is_decision_lit Ln \<longrightarrow> (\<nexists>S'. conflict N \<beta> (Ln # \<Gamma>, U, None) S')) \<Longrightarrow>
    no_conflict_after_decide N \<beta> U \<Gamma> \<Longrightarrow> no_conflict_after_decide N \<beta> U (Ln # \<Gamma>)"

definition no_conflict_after_decide' where
  "no_conflict_after_decide' N \<beta> S = no_conflict_after_decide N \<beta> (state_learned S) (state_trail S)"

lemma no_conflict_after_decide'_initial_state[simp]: "no_conflict_after_decide' N \<beta> initial_state"
  by (simp add: no_conflict_after_decide'_def no_conflict_after_decide.Nil)

lemma propagate_preserves_no_conflict_after_decide':
  assumes "propagate N \<beta> S S'" and "no_conflict_after_decide' N \<beta> S"
  shows "no_conflict_after_decide' N \<beta> S'"
  using assms
  by (auto simp: no_conflict_after_decide'_def trail_propagate_def is_decision_lit_def
      elim!: propagate.cases intro!: no_conflict_after_decide.Cons)

lemma decide_preserves_no_conflict_after_decide':
  assumes "decide N \<beta> S S'" and "\<nexists>S''. conflict N \<beta> S' S''" and "no_conflict_after_decide' N \<beta> S"
  shows "no_conflict_after_decide' N \<beta> S'"
  using assms
  by (auto simp: no_conflict_after_decide'_def trail_decide_def is_decision_lit_def
      elim!: decide.cases intro!: no_conflict_after_decide.Cons)

lemma conflict_preserves_no_conflict_after_decide':
  assumes "conflict N \<beta> S S'" and "no_conflict_after_decide' N \<beta> S"
  shows "no_conflict_after_decide' N \<beta> S'"
  using assms
  by (auto simp: no_conflict_after_decide'_def elim: conflict.cases)

lemma skip_preserves_no_conflict_after_decide':
  assumes "skip N \<beta> S S'" and "no_conflict_after_decide' N \<beta> S"
  shows "no_conflict_after_decide' N \<beta> S'"
  using assms
  by (auto simp: no_conflict_after_decide'_def
      elim!: skip.cases elim: no_conflict_after_decide.cases)

lemma factorize_preserves_no_conflict_after_decide':
  assumes "factorize N \<beta> S S'" and "no_conflict_after_decide' N \<beta> S"
  shows "no_conflict_after_decide' N \<beta> S'"
  using assms
  by (auto simp: no_conflict_after_decide'_def elim: factorize.cases)

lemma resolve_preserves_no_conflict_after_decide':
  assumes "resolve N \<beta> S S'" and "no_conflict_after_decide' N \<beta> S"
  shows "no_conflict_after_decide' N \<beta> S'"
  using assms
  by (auto simp: no_conflict_after_decide'_def elim: resolve.cases)

lemma learning_clause_without_conflict_preserves_nex_conflict:
  fixes N :: "('f, 'v) Term.term clause fset"
  assumes "\<nexists>\<gamma>. is_ground_cls (C \<cdot> \<gamma>) \<and> trail_false_cls \<Gamma> (C \<cdot> \<gamma>)"
  shows "\<nexists>S'. conflict N \<beta> (\<Gamma>, U, None) S' \<Longrightarrow> \<nexists>S'. conflict N \<beta> (\<Gamma>, finsert C U, None) S'"
proof (elim contrapos_nn exE)
  fix S'
  assume "conflict N \<beta> (\<Gamma>, finsert C U, None :: ('f, 'v) closure option) S'"
  then show "\<exists>S'. conflict N \<beta> (\<Gamma>, U, None) S'"
  proof (cases N \<beta> "(\<Gamma>, finsert C U, None :: ('f, 'v) closure option)" S' rule: conflict.cases)
    case (conflictI D \<gamma>)
    then show ?thesis
      using assms conflict.intros by blast
  qed
qed

lemma backtrack_preserves_no_conflict_after_decide':
  assumes step: "backtrack N \<beta> S S'" and invar: "no_conflict_after_decide' N \<beta> S"
  shows "no_conflict_after_decide' N \<beta> S'"
  using step
proof (cases N \<beta> S S' rule: backtrack.cases)
  case (backtrackI \<Gamma> \<Gamma>' \<Gamma>'' L \<sigma> D U)
  have "no_conflict_after_decide N \<beta> U (\<Gamma>' @ \<Gamma>'')"
    using invar
    unfolding backtrackI(1,2,3) no_conflict_after_decide'_def
    by (auto simp: trail_decide_def elim: no_conflict_after_decide.cases)
  hence "no_conflict_after_decide N \<beta> U \<Gamma>''"
    by (induction \<Gamma>') (auto elim: no_conflict_after_decide.cases)
  hence "no_conflict_after_decide N \<beta> (finsert (add_mset L D) U) \<Gamma>''"
    using backtrackI(4)
  proof (induction \<Gamma>'')
    case Nil
    show ?case
      by (auto intro: no_conflict_after_decide.Nil)
  next
    case (Cons Ln \<Gamma>'')
    hence "\<nexists>\<gamma>. is_ground_cls (add_mset L D \<cdot> \<gamma>) \<and> trail_false_cls (Ln # \<Gamma>'') (add_mset L D \<cdot> \<gamma>)"
      by metis
    hence "\<nexists>\<gamma>. is_ground_cls (add_mset L D \<cdot> \<gamma>) \<and> trail_false_cls \<Gamma>'' (add_mset L D \<cdot> \<gamma>)"
      by (metis (no_types, opaque_lifting) image_insert insert_iff list.set(2) trail_false_cls_def
          trail_false_lit_def)
    hence 1: "no_conflict_after_decide N \<beta> (finsert (add_mset L D) U) \<Gamma>''"
      by (rule Cons.IH)

    show ?case
    proof (intro no_conflict_after_decide.Cons impI)
      assume "is_decision_lit Ln"
      with Cons.hyps have "\<nexists>S'. conflict N \<beta> (Ln # \<Gamma>'', U, None) S'"
        by simp
      then show "\<nexists>S'. conflict N \<beta> (Ln # \<Gamma>'', finsert (add_mset L D) U, None) S'"
        using learning_clause_without_conflict_preserves_nex_conflict
        using \<open>\<nexists>\<gamma>. is_ground_cls (add_mset L D \<cdot> \<gamma>) \<and> trail_false_cls (Ln # \<Gamma>'') (add_mset L D \<cdot> \<gamma>)\<close>
        by blast
    next
      show "no_conflict_after_decide N \<beta> (finsert (add_mset L D) U) \<Gamma>''"
        using 1 .
    qed
  qed
  thus ?thesis
    unfolding backtrackI(1,2) no_conflict_after_decide'_def by simp
qed

lemma reasonable_scl_preserves_no_conflict_after_decide':
  assumes "reasonable_scl N \<beta> S S'" and "no_conflict_after_decide' N \<beta> S"
  shows "no_conflict_after_decide' N \<beta> S'"
  using assms unfolding reasonable_scl_def scl_def
  using propagate_preserves_no_conflict_after_decide' decide_preserves_no_conflict_after_decide'
    conflict_preserves_no_conflict_after_decide' skip_preserves_no_conflict_after_decide'
    factorize_preserves_no_conflict_after_decide' resolve_preserves_no_conflict_after_decide'
    backtrack_preserves_no_conflict_after_decide'
  by metis


subsection \<open>Miscellaneous Lemmas\<close>

lemma before_reasonable_conflict:
  assumes conf: "conflict N \<beta> S1 S2" and
    invars: "learned_nonempty S1" "trail_propagated_or_decided' N \<beta> S1"
      "no_conflict_after_decide' N \<beta> S1"
  shows "{#} |\<in>| N \<or> (\<exists>S0. propagate N \<beta> S0 S1)"
  using before_conflict[OF conf invars(1,2)]
proof (elim disjE exE)
  fix S0 assume "decide N \<beta> S0 S1"
  hence False
  proof (cases N \<beta> S0 S1 rule: decide.cases)
    case (decideI L \<gamma> \<Gamma> U)
    with invars(3) have "no_conflict_after_decide N \<beta> U (trail_decide \<Gamma> (L \<cdot>l \<gamma>))"
      by (simp add: no_conflict_after_decide'_def)
    hence "\<nexists>S'. conflict N \<beta> (trail_decide \<Gamma> (L \<cdot>l \<gamma>), U, None) S'"
      by (rule no_conflict_after_decide.cases) (simp_all add: trail_decide_def is_decision_lit_def)
    then show ?thesis
      using conf unfolding decideI(1,2) by metis
  qed
  thus ?thesis ..
qed auto


section \<open>Regular Steps\<close>

definition regular_scl where
  "regular_scl N \<beta> S S' \<longleftrightarrow>
    conflict N \<beta> S S' \<or> \<not> (\<exists>S''. conflict N \<beta> S S'') \<and> reasonable_scl N \<beta> S S'"

lemma regular_scl_if_conflict[simp]: "conflict N \<beta> S S' \<Longrightarrow> regular_scl N \<beta> S S'"
  by (simp add: regular_scl_def)

lemma regular_scl_if_skip[simp]: "skip N \<beta> S S' \<Longrightarrow> regular_scl N \<beta> S S'"
  by (auto simp: regular_scl_def reasonable_scl_def scl_def elim: conflict.cases skip.cases)

lemma regular_scl_if_factorize[simp]: "factorize N \<beta> S S' \<Longrightarrow> regular_scl N \<beta> S S'"
  by (auto simp: regular_scl_def reasonable_scl_def scl_def elim: conflict.cases factorize.cases)

lemma regular_scl_if_resolve[simp]: "resolve N \<beta> S S' \<Longrightarrow> regular_scl N \<beta> S S'"
  by (auto simp: regular_scl_def reasonable_scl_def scl_def elim: conflict.cases resolve.cases)

lemma regular_scl_if_backtrack[simp]: "backtrack N \<beta> S S' \<Longrightarrow> regular_scl N \<beta> S S'"
  by (smt (verit) backtrack.cases decide_well_defined(6) option.discI regular_scl_def conflict.simps
      reasonable_scl_def scl_def state_conflict_simp)

lemma reasonable_if_regular:
  "regular_scl N \<beta> S S' \<Longrightarrow> reasonable_scl N \<beta> S S'"
  unfolding regular_scl_def
proof (elim disjE conjE)
  assume "conflict N \<beta> S S'"
  hence "scl N \<beta> S S'"
    by (simp add: scl_def)
  moreover have "decide N \<beta> S S' \<longrightarrow> \<not>(\<exists>S''. conflict N \<beta> S' S'')"
    by (smt (verit, best) \<open>conflict N \<beta> S S'\<close> conflict.cases option.distinct(1) snd_conv)
  ultimately show "reasonable_scl N \<beta> S S'"
    by (simp add: reasonable_scl_def)
next
  assume "\<not> (\<exists>S''. conflict N \<beta> S S'')" and "reasonable_scl N \<beta> S S'"
  thus ?thesis by simp
qed

lemma regular_scl_sound_state: "regular_scl N \<beta> S S' \<Longrightarrow> sound_state N \<beta> S \<Longrightarrow> sound_state N \<beta> S'"
  by (rule reasonable_scl_sound_state[OF reasonable_if_regular])

lemma regular_run_sound_state:
  "(regular_scl N \<beta>)\<^sup>*\<^sup>* S S' \<Longrightarrow> sound_state N \<beta> S \<Longrightarrow> sound_state N \<beta> S'"
  by (smt (verit, best) regular_scl_sound_state rtranclp_induct)


subsection \<open>Invariants\<close>


subsubsection \<open>Almost No Conflict With Trail\<close>

inductive no_conflict_with_trail for N \<beta> U where
  Nil: "(\<nexists>S'. conflict N \<beta> ([], U, None) S') \<Longrightarrow> no_conflict_with_trail N \<beta> U []" |
  Cons: "(\<nexists>S'. conflict N \<beta> (Ln # \<Gamma>, U, None) S') \<Longrightarrow>
    no_conflict_with_trail N \<beta> U \<Gamma> \<Longrightarrow> no_conflict_with_trail N \<beta> U (Ln # \<Gamma>)"

lemma nex_conflict_if_no_conflict_with_trail:
  assumes "no_conflict_with_trail N \<beta> U \<Gamma>"
  shows "\<nexists>S'. conflict N \<beta> (\<Gamma>, U, None) S'"
  using assms by (auto elim: no_conflict_with_trail.cases)

lemma nex_conflict_if_no_conflict_with_trail':
  assumes "no_conflict_with_trail N \<beta> U \<Gamma>"
  shows "\<nexists>S'. conflict N \<beta> ([], U, None) S'"
  using assms
  by (induction \<Gamma> rule: no_conflict_with_trail.induct) simp_all

lemma no_conflict_after_decide_if_no_conflict_with_trail:
  "no_conflict_with_trail N \<beta> U \<Gamma> \<Longrightarrow> no_conflict_after_decide N \<beta> U \<Gamma>"
  by (induction \<Gamma> rule: no_conflict_with_trail.induct)
    (simp_all add: no_conflict_after_decide.Cons)

lemma not_trail_false_cls_if_no_conflict_with_trail:
  "no_conflict_with_trail N \<beta> U \<Gamma> \<Longrightarrow> D |\<in>| N |\<union>| U \<Longrightarrow> D \<noteq> {#} \<Longrightarrow> is_ground_cls (D \<cdot> \<gamma>) \<Longrightarrow>
    subst_domain \<gamma> \<subseteq> vars_cls D \<Longrightarrow> \<not> trail_false_cls \<Gamma> (D \<cdot> \<gamma>)"
proof (induction \<Gamma> rule: no_conflict_with_trail.induct)
  case Nil
  thus ?case by simp
next
  case (Cons Ln \<Gamma>)
  hence "\<not> trail_false_cls (Ln # \<Gamma>) (D \<cdot> \<gamma>)"
    by (metis fst_conv scl.not_trail_false_ground_cls_if_no_conflict scl_axioms state_conflict_simp
        state_learned_simp state_trail_def)
  thus ?case
    by simp
qed

definition almost_no_conflict_with_trail where
  "almost_no_conflict_with_trail N \<beta> S \<longleftrightarrow>
    {#} |\<in>| N \<and> state_trail S = [] \<or>
    no_conflict_with_trail N \<beta> (state_learned S)
      (case state_trail S of [] \<Rightarrow> [] | Ln # \<Gamma> \<Rightarrow> if is_decision_lit Ln then Ln # \<Gamma> else \<Gamma>)"

lemma nex_conflict_if_no_conflict_with_trail'':
  assumes no_conf: "state_conflict S = None" and "{#} |\<notin>| N" and "learned_nonempty S"
    "no_conflict_with_trail N \<beta> (state_learned S) (state_trail S)"
  shows "\<nexists>S'. conflict N \<beta> S S'"
proof -
  from no_conf obtain \<Gamma> U where S_def: "S = (\<Gamma>, U, None)"
    by (metis state_simp)

  from \<open>learned_nonempty S\<close> have "{#} |\<notin>| U"
    by (simp add: S_def learned_nonempty_def)

  show ?thesis
    using assms(4)
    unfolding S_def state_proj_simp
  proof (cases N \<beta> U \<Gamma> rule: no_conflict_with_trail.cases)
    case Nil
    then show "\<nexists>S'. conflict N \<beta> (\<Gamma>, U, None) S'"
      using \<open>{#} |\<notin>| N\<close> \<open>{#} |\<notin>| U\<close>
      by (auto simp: trail_false_cls_def elim: conflict.cases)
  next
    case (Cons Ln \<Gamma>')
    then show "\<nexists>S'. conflict N \<beta> (\<Gamma>, U, None) S'"
      by (auto intro: no_conflict_tail_trail)
  qed
qed

lemma no_conflict_with_trail_if_nex_conflict:
  assumes no_conf: "\<nexists>S'. conflict N \<beta> S S'" "state_conflict S = None"
  shows "no_conflict_with_trail N \<beta> (state_learned S) (state_trail S)"
proof -
  from no_conf(2) obtain \<Gamma> U where S_def: "S = (\<Gamma>, U, None)"
    by (metis state_simp)

  show ?thesis
    using no_conf(1)
    unfolding S_def state_proj_simp
  proof (induction \<Gamma>)
    case Nil
    thus ?case by (simp add: no_conflict_with_trail.Nil)
  next
    case (Cons Ln \<Gamma>)
    have "\<nexists>a. conflict N \<beta> (\<Gamma>, U, None) a"
      by (rule no_conflict_tail_trail[OF Cons.prems])
    hence "no_conflict_with_trail N \<beta> U \<Gamma>"
      by (rule Cons.IH)
    then show ?case
      using Cons.prems
      by (auto intro: no_conflict_with_trail.Cons)
  qed
qed

lemma almost_no_conflict_with_trail_if_no_conflict_with_trail:
  "no_conflict_with_trail N \<beta> U \<Gamma> \<Longrightarrow> almost_no_conflict_with_trail N \<beta> (\<Gamma>, U, Cl)"
  by (cases \<Gamma>) (auto simp: almost_no_conflict_with_trail_def elim: no_conflict_with_trail.cases)

lemma almost_no_conflict_with_trail_initial_state[simp]:
  "almost_no_conflict_with_trail N \<beta> initial_state"
  by (cases "{#} |\<in>| N") (auto simp: almost_no_conflict_with_trail_def trail_false_cls_def
      elim!: conflict.cases intro: no_conflict_with_trail.Nil)

lemma propagate_preserves_almost_no_conflict_with_trail:
  assumes step: "propagate N \<beta> S S'" and reg_step: "regular_scl N \<beta> S S'"
  shows "almost_no_conflict_with_trail N \<beta> S'"
  using reg_step[unfolded regular_scl_def]
proof (elim disjE conjE)
  assume "conflict N \<beta> S S'"
  with step have False
    using conflict_well_defined by blast
  thus ?thesis ..
next
  assume no_conf: "\<nexists>S'. conflict N \<beta> S S'" and "reasonable_scl N \<beta> S S'"
  from step show ?thesis
  proof (cases N \<beta> S S' rule: propagate.cases)
    case step_hyps: (propagateI C U L C' \<gamma> C\<^sub>0 C\<^sub>1 \<Gamma> \<mu> \<gamma>')
    have "no_conflict_with_trail N \<beta> U \<Gamma>"
      by (rule no_conflict_with_trail_if_nex_conflict[OF no_conf,
            unfolded step_hyps state_proj_simp, OF refl])
    thus ?thesis
      unfolding step_hyps(1,2)
      by (simp add: almost_no_conflict_with_trail_def trail_propagate_def is_decision_lit_def)
  qed
qed

lemma decide_preserves_almost_no_conflict_with_trail:
  assumes step: "decide N \<beta> S S'" and reg_step: "regular_scl N \<beta> S S'"
  shows "almost_no_conflict_with_trail N \<beta> S'"
proof -
  from reg_step have res_step: "reasonable_scl N \<beta> S S'"
    by (rule reasonable_if_regular)

  from step obtain \<Gamma> U where S'_def: "S' = (\<Gamma>, U, None)"
    by (auto elim: decide.cases)

  have "no_conflict_with_trail N \<beta> (state_learned S') (state_trail S')"
  proof (rule no_conflict_with_trail_if_nex_conflict)
    show "\<nexists>S''. conflict N \<beta> S' S''"
      using step res_step[unfolded reasonable_scl_def] by argo
  next
    show "state_conflict S' = None"
      by (simp add: S'_def)
  qed
  thus ?thesis
    unfolding S'_def
    by (simp add: almost_no_conflict_with_trail_if_no_conflict_with_trail)
qed

lemma almost_no_conflict_with_trail_conflict_not_relevant:
  "almost_no_conflict_with_trail N \<beta> (\<Gamma>, U, Cl1) \<longleftrightarrow>
   almost_no_conflict_with_trail N \<beta> (\<Gamma>, U, Cl2)"
  by (simp add: almost_no_conflict_with_trail_def)

lemma conflict_preserves_almost_no_conflict_with_trail:
  assumes step: "conflict N \<beta> S S'" and invar: "almost_no_conflict_with_trail N \<beta> S"
  shows "almost_no_conflict_with_trail N \<beta> S'"
proof -
  from step obtain \<Gamma> U Cl where "S = (\<Gamma>, U, None)" and "S' = (\<Gamma>, U, Some Cl)"
    by (auto elim: conflict.cases)
  with invar show ?thesis
    using almost_no_conflict_with_trail_conflict_not_relevant by metis
qed

lemma skip_preserves_almost_no_conflict_with_trail:
  assumes step: "skip N \<beta> S S'" and invar: "almost_no_conflict_with_trail N \<beta> S"
  shows "almost_no_conflict_with_trail N \<beta> S'"
  using step
proof (cases N \<beta> S S' rule: skip.cases)
  case step_hyps: (skipI L D \<sigma> n \<Gamma> U)
  have "no_conflict_with_trail N \<beta> U (if is_decision_lit (L, n) then (L, n) # \<Gamma> else \<Gamma>)"
    using invar unfolding step_hyps(1,2) by (simp add: almost_no_conflict_with_trail_def)
  hence "no_conflict_with_trail N \<beta> U \<Gamma>"
    by (cases "is_decision_lit (L, n)") (auto elim: no_conflict_with_trail.cases)
  then show ?thesis
    unfolding step_hyps(1,2)
    by (rule almost_no_conflict_with_trail_if_no_conflict_with_trail)
qed

lemma factorize_preserves_almost_no_conflict_with_trail:
  assumes step: "factorize N \<beta> S S'" and invar: "almost_no_conflict_with_trail N \<beta> S"
  shows "almost_no_conflict_with_trail N \<beta> S'"
proof -
  from step obtain \<Gamma> U Cl1 Cl2 where "S = (\<Gamma>, U, Some Cl1)" and "S' = (\<Gamma>, U, Some Cl2)"
    by (auto elim: factorize.cases)
  with invar show ?thesis
    using almost_no_conflict_with_trail_conflict_not_relevant by metis
qed

lemma resolve_preserves_almost_no_conflict_with_trail:
  assumes step: "resolve N \<beta> S S'" and invar: "almost_no_conflict_with_trail N \<beta> S"
  shows "almost_no_conflict_with_trail N \<beta> S'"
proof -
  from step obtain \<Gamma> U Cl1 Cl2 where "S = (\<Gamma>, U, Some Cl1)" and "S' = (\<Gamma>, U, Some Cl2)"
    by (auto elim: resolve.cases)
  with invar show ?thesis
    using almost_no_conflict_with_trail_conflict_not_relevant by metis
qed

lemma backtrack_preserves_almost_no_conflict_with_trail:
  assumes step: "backtrack N \<beta> S S'" and invar: "almost_no_conflict_with_trail N \<beta> S"
  shows "almost_no_conflict_with_trail N \<beta> S'"
  using step
proof (cases N \<beta> S S' rule: backtrack.cases)
  case step_hyps: (backtrackI \<Gamma> \<Gamma>' \<Gamma>'' L \<sigma> D U)
  from invar have "no_conflict_with_trail N \<beta> U ((- (L \<cdot>l \<sigma>), None) # \<Gamma>' @ \<Gamma>'')"
    by (simp add: step_hyps almost_no_conflict_with_trail_def trail_decide_def is_decision_lit_def)
  hence "no_conflict_with_trail N \<beta> U (\<Gamma>' @ \<Gamma>'')"
    by (auto elim: no_conflict_with_trail.cases)
  hence "no_conflict_with_trail N \<beta> U \<Gamma>''"
    by (induction \<Gamma>') (auto elim: no_conflict_with_trail.cases)
  then have "no_conflict_with_trail N \<beta> (finsert (add_mset L D) U) \<Gamma>''"
    by (metis learning_clause_without_conflict_preserves_nex_conflict
        nex_conflict_if_no_conflict_with_trail no_conflict_with_trail_if_nex_conflict
        state_conflict_simp state_learned_simp state_trail_simp step_hyps(4))
  thus ?thesis
    unfolding step_hyps(1,2)
    by (rule almost_no_conflict_with_trail_if_no_conflict_with_trail)
qed

lemma regular_scl_preserves_almost_no_conflict_with_trail:
  assumes "regular_scl N \<beta> S S'" and "almost_no_conflict_with_trail N \<beta> S"
  shows "almost_no_conflict_with_trail N \<beta> S'"
  using assms
  using propagate_preserves_almost_no_conflict_with_trail decide_preserves_almost_no_conflict_with_trail
    conflict_preserves_almost_no_conflict_with_trail skip_preserves_almost_no_conflict_with_trail
    factorize_preserves_almost_no_conflict_with_trail resolve_preserves_almost_no_conflict_with_trail
    backtrack_preserves_almost_no_conflict_with_trail
  by (metis scl_def reasonable_if_regular scl_if_reasonable)


subsubsection \<open>Backtrack Follows Regular Conflict Resolution\<close>


lemma before_conflict_in_regular_run:
  assumes
    reg_run: "(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S1" and
    conf: "conflict N \<beta> S1 S2" and
    "{#} |\<notin>| N"
  shows "\<exists>S0. (regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S0 \<and> regular_scl N \<beta> S0 S1 \<and> (propagate N \<beta> S0 S1)"
proof -
  from reg_run conf show ?thesis
  proof (induction S1 arbitrary: S2 rule: rtranclp_induct)
    case base
    with \<open>{#} |\<notin>| N\<close> have False
      by (meson fempty_iff funion_iff mempty_in_iff_ex_conflict)
    thus ?case ..
  next
    case (step S0 S1)
    from step.hyps(1) have "learned_nonempty S0"
      by (induction S0 rule: rtranclp_induct)
        (simp_all add: scl_preserves_learned_nonempty[OF scl_if_reasonable[OF
              reasonable_if_regular]])
    with step.hyps(2) have "learned_nonempty S1"
      by (simp add: scl_preserves_learned_nonempty[OF scl_if_reasonable[OF reasonable_if_regular]])

    from step.hyps(1) have "trail_propagated_or_decided' N \<beta> S0"
      by (induction S0 rule: rtranclp_induct)
        (simp_all add: scl_preserves_trail_propagated_or_decided[OF scl_if_reasonable[OF
              reasonable_if_regular]])
    with step.hyps(2) have "trail_propagated_or_decided' N \<beta> S1"
      by (simp add: scl_preserves_trail_propagated_or_decided[OF scl_if_reasonable[OF
              reasonable_if_regular]])

    from step.hyps(1) have "almost_no_conflict_with_trail N \<beta> S0"
      by (induction S0 rule: rtranclp_induct)
        (simp_all add: regular_scl_preserves_almost_no_conflict_with_trail)
    with step.hyps(2) have "almost_no_conflict_with_trail N \<beta> S1"
      by (simp add: regular_scl_preserves_almost_no_conflict_with_trail)

    show ?case
    proof (intro exI conjI)
      show "(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S0"
        using step.hyps by simp
    next
      show "regular_scl N \<beta> S0 S1"
        using step.hyps by simp
    next
      from step.prems obtain \<Gamma> U C \<gamma> where
        S1_def: "S1 = (\<Gamma>, U, None)" and
        S2_def: "S2 = (\<Gamma>, U, Some (C, \<gamma>))" and
        C_in: "C |\<in>| N |\<union>| U" and
        dom_\<gamma>: "subst_domain \<gamma> \<subseteq> vars_cls C" and
        ground_conf: "is_ground_cls (C \<cdot> \<gamma>)" and
        tr_false_conf: "trail_false_cls \<Gamma> (C \<cdot> \<gamma>)"
        unfolding conflict.simps by auto
      with step.hyps have "\<not> conflict N \<beta> S0 S1" and "reasonable_scl N \<beta> S0 S1"
        unfolding regular_scl_def by (simp_all add: conflict.simps)
      with step.prems have "scl N \<beta> S0 S1" and "\<not> decide N \<beta> S0 S1"
        unfolding reasonable_scl_def by blast+
      moreover from step.prems have "\<not> backtrack N \<beta> S0 S1"
      proof (cases \<Gamma>)
        case Nil
        then show ?thesis
        using \<open>{#} |\<notin>| N\<close> \<open>almost_no_conflict_with_trail N \<beta> S1\<close> step.prems
        by (auto simp: S1_def almost_no_conflict_with_trail_def elim: no_conflict_with_trail.cases)
      next
        case (Cons Ln \<Gamma>')
        have "C \<noteq> {#}"
          using \<open>{#} |\<notin>| N\<close>
          by (metis C_in S1_def \<open>learned_nonempty S1\<close> funionE learned_nonempty_def state_proj_simp(2))

        from Cons have "\<not> is_decision_lit Ln"
          using \<open>\<not> decide N \<beta> S0 S1\<close>[unfolded S1_def]
          by (metis (mono_tags, lifting) S1_def \<open>almost_no_conflict_with_trail N \<beta> S1\<close>
              almost_no_conflict_with_trail_def list.discI list.simps(5)
              nex_conflict_if_no_conflict_with_trail state_learned_simp state_trail_simp step.prems)
        with \<open>{#} |\<notin>| N\<close> have "no_conflict_with_trail N \<beta> U \<Gamma>'"
          using \<open>almost_no_conflict_with_trail N \<beta> S1\<close>
          by (simp add: Cons S1_def almost_no_conflict_with_trail_def)
        with Cons show ?thesis
          unfolding S1_def
          using \<open>{#} |\<notin>| N\<close>
          by (smt (verit) S2_def \<open>almost_no_conflict_with_trail N \<beta> S0\<close> \<open>learned_nonempty S1\<close>
              almost_no_conflict_with_trail_def backtrack.simps conflict.cases finsert_iff funionE
              funion_finsert_right learned_nonempty_def list.case(2) list.sel(3) list.simps(3)
              no_conflict_with_trail.simps not_trail_false_cls_if_no_conflict_with_trail
              state_learned_simp state_trail_simp step.prems suffixI trail_decide_def
              trail_false_cls_if_trail_false_suffix)
      qed
      ultimately show "propagate N \<beta> S0 S1"
        by (simp add: scl_def S1_def skip.simps conflict.simps factorize.simps resolve.simps)
    qed
  qed
qed

definition regular_conflict_resolution where
  "regular_conflict_resolution N \<beta> S \<longleftrightarrow> {#} |\<notin>| N \<longrightarrow>
    (case state_conflict S of
      None \<Rightarrow> (regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S |
      Some _ \<Rightarrow> (\<exists>S0 S1 S2 S3. (regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S0 \<and>
        propagate N \<beta> S0 S1 \<and> regular_scl N \<beta> S0 S1 \<and>
        conflict N \<beta> S1 S2 \<and> regular_scl N \<beta> S1 S2 \<and>
        (factorize N \<beta>)\<^sup>*\<^sup>* S2 S3 \<and> (regular_scl N \<beta>)\<^sup>*\<^sup>* S2 S3 \<and>
        (S3 = S \<or> (\<exists>S4. resolve N \<beta> S3 S4 \<and> (skip N \<beta> \<squnion> factorize N \<beta> \<squnion> resolve N \<beta>)\<^sup>*\<^sup>* S4 S))))"

lemma regular_conflict_resolution_initial_state[simp]:
  "regular_conflict_resolution N \<beta> initial_state"
  by (simp add: regular_conflict_resolution_def)

lemma propagate_preserves_regular_conflict_resolution:
  assumes step: "propagate N \<beta> S S'" and reg_step: "regular_scl N \<beta> S S'" and
    invar: "regular_conflict_resolution N \<beta> S"
  shows "regular_conflict_resolution N \<beta> S'"
proof -
  from step have "state_conflict S = None" and "state_conflict S' = None"
    by (auto elim: propagate.cases)

  show ?thesis
    unfolding regular_conflict_resolution_def \<open>state_conflict S' = None\<close>
    unfolding option.case
  proof (rule impI)
    assume "{#} |\<notin>| N"
    with invar have "(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S"
      unfolding regular_conflict_resolution_def \<open>state_conflict S = None\<close> by simp
    thus "(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S'"
      using reg_step by (rule rtranclp.rtrancl_into_rtrancl)
  qed
qed

lemma decide_preserves_regular_conflict_resolution:
  assumes step: "decide N \<beta> S S'" and reg_step: "regular_scl N \<beta> S S'" and
    invar: "regular_conflict_resolution N \<beta> S"
  shows "regular_conflict_resolution N \<beta> S'"
proof -
  from step have "state_conflict S = None" and "state_conflict S' = None"
    by (auto elim: decide.cases)

  show ?thesis
    unfolding regular_conflict_resolution_def \<open>state_conflict S' = None\<close>
    unfolding option.case
  proof (rule impI)
    assume "{#} |\<notin>| N"
    with invar have "(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S"
      unfolding regular_conflict_resolution_def \<open>state_conflict S = None\<close> by simp
    thus "(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S'"
      using reg_step by (rule rtranclp.rtrancl_into_rtrancl)
  qed
qed

lemma conflict_preserves_regular_conflict_resolution:
  assumes step: "conflict N \<beta> S S'" and reg_step: "regular_scl N \<beta> S S'" and
    invar: "regular_conflict_resolution N \<beta> S"
  shows "regular_conflict_resolution N \<beta> S'"
proof -
  from step obtain C \<gamma> where "state_conflict S = None" and "state_conflict S' = Some (C, \<gamma>)"
    by (auto elim!: conflict.cases)

  show ?thesis
    unfolding regular_conflict_resolution_def \<open>state_conflict S' = Some (C, \<gamma>)\<close>
    unfolding option.cases
  proof (rule impI)
    assume "{#} |\<notin>| N"
    with invar have reg_run: "(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S"
      unfolding regular_conflict_resolution_def \<open>state_conflict S = None\<close> by simp

    from \<open>{#} |\<notin>| N\<close> obtain S0 where
      "(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S0" "propagate N \<beta> S0 S" "regular_scl N \<beta> S0 S"
      using before_conflict_in_regular_run[OF reg_run step] by metis

    with step show "\<exists>S0 S1 S2 S3. (regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S0 \<and>
      propagate N \<beta> S0 S1 \<and> regular_scl N \<beta> S0 S1 \<and>
      conflict N \<beta> S1 S2 \<and> regular_scl N \<beta> S1 S2 \<and>
      (factorize N \<beta>)\<^sup>*\<^sup>* S2 S3 \<and> (regular_scl N \<beta>)\<^sup>*\<^sup>* S2 S3 \<and>
      (S3 = S' \<or> (\<exists>S4. resolve N \<beta> S3 S4 \<and> (skip N \<beta> \<squnion> factorize N \<beta> \<squnion> resolve N \<beta>)\<^sup>*\<^sup>* S4 S'))"
      using regular_scl_if_conflict
      by blast
  qed
qed

lemma
  assumes "almost_no_conflict_with_trail N \<beta> S" and "{#} |\<notin>| N"
  shows "no_conflict_after_decide' N \<beta> S"
proof -
  obtain U \<Gamma> Cl where S_def: "S = (\<Gamma>, U, Cl)"
    by (metis state_simp)

  show ?thesis
  proof (cases \<Gamma>)
    case Nil
    thus ?thesis
      by (simp add: S_def no_conflict_after_decide'_def)
  next
    case (Cons Ln \<Gamma>')
    with assms have no_conf_with_trail:
      "no_conflict_with_trail N \<beta> U (if is_decision_lit Ln then Ln # \<Gamma>' else \<Gamma>')"
      by (simp add: S_def almost_no_conflict_with_trail_def)

    show ?thesis
      using no_conf_with_trail
      by (cases "is_decision_lit Ln")
        (simp_all add: S_def Cons no_conflict_after_decide'_def no_conflict_after_decide.Cons
          no_conflict_after_decide_if_no_conflict_with_trail)
  qed
qed

lemma mempty_not_in_learned_if_almost_no_conflict_with_trail:
  "almost_no_conflict_with_trail N \<beta> S \<Longrightarrow> {#} |\<notin>| N \<Longrightarrow> {#} |\<notin>| state_learned S"
  unfolding almost_no_conflict_with_trail_def
  using nex_conflict_if_no_conflict_with_trail'[folded mempty_in_iff_ex_conflict]
  by simp

lemma skip_preserves_regular_conflict_resolution:
  assumes step: "skip N \<beta> S S'" and reg_step: "regular_scl N \<beta> S S'" and
    invar: "regular_conflict_resolution N \<beta> S"
  shows "regular_conflict_resolution N \<beta> S'"
proof -
  from step obtain C \<gamma> where
    "state_conflict S = Some (C, \<gamma>)" and "state_conflict S' = Some (C, \<gamma>)"
    by (auto elim!: skip.cases)

  show ?thesis
    unfolding regular_conflict_resolution_def \<open>state_conflict S' = Some (C, \<gamma>)\<close>
    unfolding option.cases
  proof (intro impI)
    assume "{#} |\<notin>| N"
    with invar obtain S0 S1 S2 S3 where
      reg_run: "(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S0" and
      propa: "propagate N \<beta> S0 S1" "regular_scl N \<beta> S0 S1" and
      confl: "conflict N \<beta> S1 S2" "regular_scl N \<beta> S1 S2" and
      facto: "(factorize N \<beta>)\<^sup>*\<^sup>* S2 S3" "(regular_scl N \<beta>)\<^sup>*\<^sup>* S2 S3" and
      maybe_reso: "S3 = S \<or> (\<exists>S4. resolve N \<beta> S3 S4 \<and> (skip N \<beta> \<squnion> factorize N \<beta> \<squnion> resolve N \<beta>)\<^sup>*\<^sup>* S4 S)"
      unfolding regular_conflict_resolution_def \<open>state_conflict S = Some (C, \<gamma>)\<close>
      unfolding option.cases
      by metis

    from reg_run have "(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S1"
      using \<open>regular_scl N \<beta> S0 S1\<close> by simp
    hence "(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S2"
      using \<open>regular_scl N \<beta> S1 S2\<close> by simp
    hence "(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S3"
      using \<open>(regular_scl N \<beta>)\<^sup>*\<^sup>* S2 S3\<close> by simp

    from \<open>(factorize N \<beta>)\<^sup>*\<^sup>* S2 S3\<close> have "state_trail S3 = state_trail S2"
      by (induction S3 rule: rtranclp_induct) (auto elim: factorize.cases)
    also from \<open>conflict N \<beta> S1 S2\<close> have "\<dots> = state_trail S1"
      by (auto elim: conflict.cases)
    finally have "state_trail S3 = state_trail S1"
      by assumption

    from \<open>(factorize N \<beta>)\<^sup>*\<^sup>* S2 S3\<close> have "state_learned S3 = state_learned S2"
    proof (induction S3 rule: rtranclp_induct)
      case base
      show ?case by simp
    next
      case (step y z)
      thus ?case
        by (elim factorize.cases) simp
    qed
    also from \<open>conflict N \<beta> S1 S2\<close> have "\<dots> = state_learned S1"
      by (auto elim: conflict.cases)
    finally have "state_learned S3 = state_learned S1"
      by assumption

    from \<open>propagate N \<beta> S0 S1\<close> have "state_learned S1 = state_learned S0"
      by (auto elim: propagate.cases)

    from \<open>propagate N \<beta> S0 S1\<close> obtain L C \<gamma> where
      "state_trail S1 = trail_propagate (state_trail S0) L C \<gamma>"
      by (auto elim: propagate.cases)

    from \<open>(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S3\<close> have "almost_no_conflict_with_trail N \<beta> S3"
      using regular_scl_preserves_almost_no_conflict_with_trail
      by (induction S3 rule: rtranclp_induct) simp_all

    show "\<exists>S0 S1 S2 S3. (regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S0 \<and>
      propagate N \<beta> S0 S1 \<and> regular_scl N \<beta> S0 S1 \<and>
      conflict N \<beta> S1 S2 \<and> regular_scl N \<beta> S1 S2 \<and>
      (factorize N \<beta>)\<^sup>*\<^sup>* S2 S3 \<and> (regular_scl N \<beta>)\<^sup>*\<^sup>* S2 S3 \<and>
      (S3 = S' \<or> (\<exists>S4. resolve N \<beta> S3 S4 \<and> (skip N \<beta> \<squnion> factorize N \<beta> \<squnion> resolve N \<beta>)\<^sup>*\<^sup>* S4 S'))"
      using reg_run propa confl facto
    proof (intro impI exI conjI)
      show "S3 = S' \<or> (\<exists>S4. resolve N \<beta> S3 S4 \<and> (skip N \<beta> \<squnion> factorize N \<beta> \<squnion> resolve N \<beta>)\<^sup>*\<^sup>* S4 S')"
        using maybe_reso
      proof (elim disjE exE conjE)
        fix S4 assume "resolve N \<beta> S3 S4" and "(skip N \<beta> \<squnion> factorize N \<beta> \<squnion> resolve N \<beta>)\<^sup>*\<^sup>* S4 S"
        with step have "\<exists>S4. resolve N \<beta> S3 S4 \<and> (skip N \<beta> \<squnion> factorize N \<beta> \<squnion> resolve N \<beta>)\<^sup>*\<^sup>* S4 S'"
          by (meson rtranclp.rtrancl_into_rtrancl sup2CI)
        thus ?thesis ..
      next
        assume "S3 = S"
        with \<open>almost_no_conflict_with_trail N \<beta> S3\<close> \<open>{#} |\<notin>| N\<close>
        have no_conf_with_trail: "no_conflict_with_trail N \<beta> (state_learned S)
          (case state_trail S of [] \<Rightarrow> [] | Ln # \<Gamma> \<Rightarrow> if is_decision_lit Ln then Ln # \<Gamma> else \<Gamma>)"
          by (simp add: almost_no_conflict_with_trail_def)
        hence "{#} |\<notin>| state_learned S"
          using nex_conflict_if_no_conflict_with_trail'[folded mempty_in_iff_ex_conflict]
          by simp

        from no_conf_with_trail
        have no_conf_with_trail': "no_conflict_with_trail N \<beta> (state_learned S1) (state_trail S0)"
          using \<open>S3 = S\<close> \<open>state_trail S3 = state_trail S1\<close>
            \<open>state_learned S3 = state_learned S1\<close>
            \<open>state_trail S1 = trail_propagate (state_trail S0) L C \<gamma>\<close>
          by (simp add: trail_propagate_def is_decision_lit_def)

        have "\<exists>D \<gamma>\<^sub>D. state_conflict S2 = Some (D, \<gamma>\<^sub>D) \<and> - (L \<cdot>l \<gamma>) \<in># D \<cdot> \<gamma>\<^sub>D"
          using \<open>conflict N \<beta> S1 S2\<close>
        proof (cases N \<beta> S1 S2 rule: conflict.cases)
          case (conflictI D U \<gamma>\<^sub>D \<Gamma>)
          hence "trail_false_cls (trail_propagate (state_trail S0) L C \<gamma>) (D \<cdot> \<gamma>\<^sub>D)"
            using \<open>state_trail S1 = trail_propagate (state_trail S0) L C \<gamma>\<close>
            by simp

          moreover from no_conf_with_trail' have "\<not> trail_false_cls (state_trail S0) (D \<cdot> \<gamma>\<^sub>D)"
            unfolding \<open>state_learned S1 = state_learned S0\<close>
          proof (rule not_trail_false_cls_if_no_conflict_with_trail)
            show "D |\<in>| N |\<union>| state_learned S0"
              using \<open>state_learned S1 = state_learned S0\<close> local.conflictI(1) local.conflictI(3)
              by fastforce
          next
            have "{#} |\<notin>| U"
              using \<open>{#} |\<notin>| state_learned S\<close> \<open>S3 = S\<close> \<open>state_learned S3 = state_learned S1\<close>
              unfolding conflictI(1,2)
              by simp
            thus "D \<noteq> {#}"
              using \<open>{#} |\<notin>| N\<close> \<open>D |\<in>| N |\<union>| U\<close>
              by auto
          next
            show "is_ground_cls (D \<cdot> \<gamma>\<^sub>D)"
              by (rule \<open>is_ground_cls (D \<cdot> \<gamma>\<^sub>D)\<close>)
          next
            show "subst_domain \<gamma>\<^sub>D \<subseteq> vars_cls D"
              by (rule \<open>subst_domain \<gamma>\<^sub>D \<subseteq> vars_cls D\<close>)
          qed

          ultimately have "- (L \<cdot>l \<gamma>) \<in># D \<cdot> \<gamma>\<^sub>D"
            by (metis subtrail_falseI trail_propagate_def)

          moreover have "state_conflict S2 = Some (D, \<gamma>\<^sub>D)"
            unfolding conflictI(1,2) by simp

          ultimately show ?thesis
            by metis
        qed
        then obtain D \<gamma>\<^sub>D where "state_conflict S2 = Some (D, \<gamma>\<^sub>D)" and "- (L \<cdot>l \<gamma>) \<in># D \<cdot> \<gamma>\<^sub>D"
          by metis

        with \<open>(factorize N \<beta>)\<^sup>*\<^sup>* S2 S3\<close>
        have "\<exists>D' \<gamma>\<^sub>D'. state_conflict S3 = Some (D', \<gamma>\<^sub>D') \<and> - (L \<cdot>l \<gamma>) \<in># D' \<cdot> \<gamma>\<^sub>D'"
        proof (induction S3 arbitrary: rule: rtranclp_induct)
          case base
          thus ?case by simp
        next
          case (step y z)
          then obtain D' \<gamma>\<^sub>D' where "state_conflict y = Some (D', \<gamma>\<^sub>D')" and "- (L \<cdot>l \<gamma>) \<in># D' \<cdot> \<gamma>\<^sub>D'"
            by auto
          then show ?case
            using step.hyps(2)
            by (metis conflict_set_after_factorization)
        qed
        with step have False
          using \<open>state_trail S3 = state_trail S1\<close>
          unfolding \<open>S3 = S\<close> \<open>state_trail S1 = trail_propagate (state_trail S0) L C \<gamma>\<close>
          by (auto simp add: trail_propagate_def elim!: skip.cases)
        thus ?thesis ..
      qed
    qed
  qed
qed

lemma factorize_preserves_regular_conflict_resolution:
  assumes step: "factorize N \<beta> S S'" and reg_step: "regular_scl N \<beta> S S'" and
    invar: "regular_conflict_resolution N \<beta> S"
  shows "regular_conflict_resolution N \<beta> S'"
proof -
  from step obtain C \<gamma> C' \<gamma>' where
    "state_conflict S = Some (C, \<gamma>)" and "state_conflict S' = Some (C', \<gamma>')"
    by (auto elim!: factorize.cases)

  show ?thesis
    unfolding regular_conflict_resolution_def \<open>state_conflict S' = Some (C', \<gamma>')\<close>
    unfolding option.cases
  proof (intro impI)
    assume "{#} |\<notin>| N"
    with invar obtain S0 S1 S2 S3 where
      reg_run: "(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S0" and
      propa: "propagate N \<beta> S0 S1" "regular_scl N \<beta> S0 S1" and
      confl: "conflict N \<beta> S1 S2" "regular_scl N \<beta> S1 S2" and
      facto: "(factorize N \<beta>)\<^sup>*\<^sup>* S2 S3" "(regular_scl N \<beta>)\<^sup>*\<^sup>* S2 S3" and
      maybe_reso: "S3 = S \<or> (\<exists>S4. resolve N \<beta> S3 S4 \<and> (skip N \<beta> \<squnion> factorize N \<beta> \<squnion> resolve N \<beta>)\<^sup>*\<^sup>* S4 S)"
      unfolding regular_conflict_resolution_def \<open>state_conflict S = Some (C, \<gamma>)\<close>
      unfolding option.cases
      by metis

    show "\<exists>S0 S1 S2 S3. (regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S0 \<and>
      propagate N \<beta> S0 S1 \<and> regular_scl N \<beta> S0 S1 \<and>
      conflict N \<beta> S1 S2 \<and> regular_scl N \<beta> S1 S2 \<and>
      (factorize N \<beta>)\<^sup>*\<^sup>* S2 S3 \<and> (regular_scl N \<beta>)\<^sup>*\<^sup>* S2 S3 \<and>
      (S3 = S' \<or> (\<exists>S4. resolve N \<beta> S3 S4 \<and> (skip N \<beta> \<squnion> factorize N \<beta> \<squnion> resolve N \<beta>)\<^sup>*\<^sup>* S4 S'))"
      using maybe_reso
    proof (elim disjE exE conjE)
      assume "S3 = S"
      show ?thesis
        using reg_run propa confl
      proof (intro exI conjI)
        show "(factorize N \<beta>)\<^sup>*\<^sup>* S2 S'"
          using \<open>(factorize N \<beta>)\<^sup>*\<^sup>* S2 S3\<close> step
          by (simp add: \<open>S3 = S\<close>)
      next
        show "(regular_scl N \<beta>)\<^sup>*\<^sup>* S2 S'"
          using \<open>(regular_scl N \<beta>)\<^sup>*\<^sup>* S2 S3\<close> reg_step
          by (simp add: \<open>S3 = S\<close>)
      next
        show "S' = S' \<or> (\<exists>S4. resolve N \<beta> S' S4 \<and> (skip N \<beta> \<squnion> factorize N \<beta> \<squnion> resolve N \<beta>)\<^sup>*\<^sup>* S4 S')"
          by simp
      qed
    next
      fix S4 assume hyps: "resolve N \<beta> S3 S4" "(skip N \<beta> \<squnion> factorize N \<beta> \<squnion> resolve N \<beta>)\<^sup>*\<^sup>* S4 S"
      show ?thesis
        using reg_run propa confl facto
      proof (intro exI conjI)
        show "S3 = S' \<or> (\<exists>S4. resolve N \<beta> S3 S4 \<and> (skip N \<beta> \<squnion> factorize N \<beta> \<squnion> resolve N \<beta>)\<^sup>*\<^sup>* S4 S')"
          using hyps step
          by (meson rtranclp.rtrancl_into_rtrancl sup2CI)
      qed
    qed
  qed
qed

lemma resolve_preserves_regular_conflict_resolution:
  assumes step: "resolve N \<beta> S S'" and reg_step: "regular_scl N \<beta> S S'" and
    invar: "regular_conflict_resolution N \<beta> S"
  shows "regular_conflict_resolution N \<beta> S'"
proof -
  from step obtain C \<gamma> C' \<gamma>' where
    "state_conflict S = Some (C, \<gamma>)" and "state_conflict S' = Some (C', \<gamma>')"
    by (auto elim!: resolve.cases)

  show ?thesis
    unfolding regular_conflict_resolution_def \<open>state_conflict S' = Some (C', \<gamma>')\<close>
    unfolding option.cases
  proof (intro impI)
    from step have "state_conflict S \<noteq> None"
      by (auto elim: resolve.cases)

    assume "{#} |\<notin>| N"
    with invar obtain S0 S1 S2 S3 where
      reg_run: "(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S0" and
      "propagate N \<beta> S0 S1" "regular_scl N \<beta> S0 S1" and
      "conflict N \<beta> S1 S2" "regular_scl N \<beta> S1 S2" and
      "(factorize N \<beta>)\<^sup>*\<^sup>* S2 S3" "(regular_scl N \<beta>)\<^sup>*\<^sup>* S2 S3" and
      maybe_reso: "S3 = S \<or> (\<exists>S4. resolve N \<beta> S3 S4 \<and> (skip N \<beta> \<squnion> factorize N \<beta> \<squnion> resolve N \<beta>)\<^sup>*\<^sup>* S4 S)"
      unfolding regular_conflict_resolution_def \<open>state_conflict S = Some (C, \<gamma>)\<close>
      unfolding option.cases
      by metis

    then show "\<exists>S0 S1 S2 S3. (regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S0 \<and>
      propagate N \<beta> S0 S1 \<and> regular_scl N \<beta> S0 S1 \<and>
      conflict N \<beta> S1 S2 \<and> regular_scl N \<beta> S1 S2 \<and>
      (factorize N \<beta>)\<^sup>*\<^sup>* S2 S3 \<and> (regular_scl N \<beta>)\<^sup>*\<^sup>* S2 S3 \<and>
      (S3 = S' \<or> (\<exists>S4. resolve N \<beta> S3 S4 \<and> (skip N \<beta> \<squnion> factorize N \<beta> \<squnion> resolve N \<beta>)\<^sup>*\<^sup>* S4 S'))"
    proof (intro exI conjI)
      show "S3 = S' \<or> (\<exists>S4. resolve N \<beta> S3 S4 \<and> (skip N \<beta> \<squnion> factorize N \<beta> \<squnion> resolve N \<beta>)\<^sup>*\<^sup>* S4 S')"
        using maybe_reso step
        by (metis (no_types, opaque_lifting) rtranclp.rtrancl_into_rtrancl rtranclp.rtrancl_refl
            sup2I2)
    qed
  qed
qed

lemma backtrack_preserves_regular_conflict_resolution:
  assumes step: "backtrack N \<beta> S S'" and reg_step: "regular_scl N \<beta> S S'" and
    invar: "regular_conflict_resolution N \<beta> S"
  shows "regular_conflict_resolution N \<beta> S'"
proof -
  from step obtain C \<gamma> where
    "state_conflict S = Some (C, \<gamma>)" and "state_conflict S' = None"
    by (auto elim!: backtrack.cases)

  show ?thesis
    unfolding regular_conflict_resolution_def \<open>state_conflict S' = None\<close>
    unfolding option.case
  proof (rule impI)
    assume "{#} |\<notin>| N"
    with invar obtain S0 S1 S2 S3 where
      reg_run: "(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S0" and
      propa: "propagate N \<beta> S0 S1" "regular_scl N \<beta> S0 S1" and
      confl: "conflict N \<beta> S1 S2" "regular_scl N \<beta> S1 S2" and
      facto: "(factorize N \<beta>)\<^sup>*\<^sup>* S2 S3" "(regular_scl N \<beta>)\<^sup>*\<^sup>* S2 S3" and
      maybe_reso: "S3 = S \<or> (\<exists>S4. resolve N \<beta> S3 S4 \<and> (skip N \<beta> \<squnion> factorize N \<beta> \<squnion> resolve N \<beta>)\<^sup>*\<^sup>* S4 S)"
      unfolding regular_conflict_resolution_def \<open>state_conflict S = Some (C, \<gamma>)\<close>
      unfolding option.cases
      by metis

    from reg_run propa(2) confl(2) facto(2) have reg_run_S3: "(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S3"
      by simp

    show "(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S'"
      using maybe_reso
    proof (elim disjE exE conjE)
      show "S3 = S \<Longrightarrow> (regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S'"
        using reg_run_S3 reg_step by simp
    next
      fix S4 assume hyps: "resolve N \<beta> S3 S4" "(skip N \<beta> \<squnion> factorize N \<beta> \<squnion> resolve N \<beta>)\<^sup>*\<^sup>* S4 S"
      have "(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S4"
        using reg_run_S3 regular_scl_if_resolve[OF hyps(1)]
        by (rule rtranclp.rtrancl_into_rtrancl)
      also have "(regular_scl N \<beta>)\<^sup>*\<^sup>* S4 S"
        using hyps(2)
        by (rule mono_rtranclp[rule_format, rotated]) auto
      also have "(regular_scl N \<beta>)\<^sup>*\<^sup>* S S'"
        using reg_step by simp
      finally show "(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S'"
        by assumption
    qed
  qed
qed

lemma regular_scl_preserves_regular_conflict_resolution:
  assumes reg_step: "regular_scl N \<beta> S S'" and
    invars: "regular_conflict_resolution N \<beta> S"
  shows "regular_conflict_resolution N \<beta> S'"
  using assms
  using propagate_preserves_regular_conflict_resolution decide_preserves_regular_conflict_resolution
    conflict_preserves_regular_conflict_resolution skip_preserves_regular_conflict_resolution
    factorize_preserves_regular_conflict_resolution resolve_preserves_regular_conflict_resolution
    backtrack_preserves_regular_conflict_resolution
  by (metis regular_scl_def reasonable_scl_def scl_def)

subsection \<open>Miscellaneous Lemmas\<close>

lemma mempty_not_in_initial_clauses_if_non_empty_regular_conflict:
  assumes "state_conflict S = Some (C, \<gamma>)" and "C \<noteq> {#}" and
    invars: "almost_no_conflict_with_trail N \<beta> S" "sound_state N \<beta> S"
  shows "{#} |\<notin>| N"
proof -
  from assms(1) obtain \<Gamma> U where S_def: "S = (\<Gamma>, U, Some (C, \<gamma>))"
    by (metis state_simp)

  from assms(2) obtain L C' where C_def: "C = add_mset L C'"
    using multi_nonempty_split by metis

  from invars(2) have "trail_false_cls \<Gamma> (C \<cdot> \<gamma>)"
    by (simp add: S_def sound_state_def)
  then obtain Ln \<Gamma>' where "\<Gamma> = Ln # \<Gamma>'"
    by (metis assms(2) neq_Nil_conv not_trail_false_Nil(2) subst_cls_empty_iff)
  with invars(1) have "no_conflict_with_trail N \<beta> U (if is_decision_lit Ln then Ln # \<Gamma>' else \<Gamma>')"
    by (simp add: S_def almost_no_conflict_with_trail_def)
  hence "\<nexists>S'. conflict N \<beta> ([], U, None) S'"
    by (rule nex_conflict_if_no_conflict_with_trail')
  hence "{#} |\<notin>| N |\<union>| U"
    unfolding mempty_in_iff_ex_conflict[symmetric] by assumption
  thus ?thesis
    by simp
qed

lemma mempty_not_in_initial_clauses_if_regular_run_reaches_non_empty_conflict:
  assumes "(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S" and "state_conflict S = Some (C, \<gamma>)" and "C \<noteq> {#}"
  shows "{#} |\<notin>| N"
proof (rule notI)
  from assms(2) have "initial_state \<noteq> S" by fastforce
  then obtain S' where
    reg_scl_init_S': "regular_scl N \<beta> initial_state S'" and "(regular_scl N \<beta>)\<^sup>*\<^sup>* S' S"
    by (metis assms(1) converse_rtranclpE)

  assume "{#} |\<in>| N"
  hence "conflict N \<beta> initial_state ([], {||}, Some ({#}, Var))"
    by (rule conflict_initial_state_if_mempty_in_intial_clauses)
  hence conf_init: "regular_scl N \<beta> initial_state ([], {||}, Some ({#}, Var))"
    using regular_scl_def by blast
  hence S'_def: "S' = ([], {||}, Some ({#}, Var))"
    using reg_scl_init_S'
    unfolding regular_scl_def
    using \<open>conflict N \<beta> initial_state ([], {||}, Some ({#}, Var))\<close>
      conflict_initial_state_only_with_mempty
    by blast

  have "\<nexists>S'. scl N \<beta> ([], {||}, Some ({#}, Var)) S'"
    using no_more_step_if_conflict_mempty by simp
  hence "\<nexists>S'. regular_scl N \<beta> ([], {||}, Some ({#}, Var)) S'"
    using scl_if_reasonable[OF reasonable_if_regular] by blast
  hence "S = S'"
    using \<open>(regular_scl N \<beta>)\<^sup>*\<^sup>* S' S\<close> unfolding S'_def
    by (metis converse_rtranclpE)
  with assms(2,3) show False by (simp add: S'_def)
qed

lemma before_regular_backtrack:
  assumes
    backt: "backtrack N \<beta> S S'" and
    invars: "sound_state N \<beta> S" "almost_no_conflict_with_trail N \<beta> S"
      "regular_conflict_resolution N \<beta> S"
  shows "\<exists>S0 S1 S2 S3 S4. (regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S0 \<and>
    propagate N \<beta> S0 S1 \<and> regular_scl N \<beta> S0 S1 \<and>
    conflict N \<beta> S1 S2 \<and> (factorize N \<beta>)\<^sup>*\<^sup>* S2 S3 \<and> resolve N \<beta> S3 S4 \<and>
    (skip N \<beta> \<squnion> factorize N \<beta> \<squnion> resolve N \<beta>)\<^sup>*\<^sup>* S4 S"
proof -
  from backt obtain L C \<gamma> where conflict_S: "state_conflict S = Some (add_mset L C, \<gamma>)"
    by (auto elim: backtrack.cases)
  
  have "{#} |\<notin>| N"
  proof (rule mempty_not_in_initial_clauses_if_non_empty_regular_conflict)
    show "state_conflict S = Some (add_mset L C, \<gamma>)"
      by (rule \<open>state_conflict S = Some (add_mset L C, \<gamma>)\<close>)
  next
    show "add_mset L C \<noteq> {#}"
      by simp
  next
    show "almost_no_conflict_with_trail N \<beta> S"
      by (rule \<open>almost_no_conflict_with_trail N \<beta> S\<close>)
  next
    show "sound_state N \<beta> S"
      by (rule \<open>sound_state N \<beta> S\<close>)
  qed

  then obtain S0 S1 S2 S3 where
    reg_run: "(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S0" and
    propa: "propagate N \<beta> S0 S1" "regular_scl N \<beta> S0 S1" and
    confl: "conflict N \<beta> S1 S2" and
    fact: "(factorize N \<beta>)\<^sup>*\<^sup>* S2 S3" and
    maybe_resolution: "S3 = S \<or>
      (\<exists>S4. resolve N \<beta> S3 S4 \<and> (skip N \<beta> \<squnion> factorize N \<beta> \<squnion> resolve N \<beta>)\<^sup>*\<^sup>* S4 S)"
    using \<open>regular_conflict_resolution N \<beta> S\<close> \<open>state_conflict S = Some (add_mset L C, \<gamma>)\<close>
    unfolding regular_conflict_resolution_def conflict_S option.case
    by metis

  have "S3 \<noteq> S"
  proof (rule notI)
    from \<open>(factorize N \<beta>)\<^sup>*\<^sup>* S2 S3\<close> have "state_trail S3 = state_trail S2"
      by (induction S3 rule: rtranclp_induct) (auto elim: factorize.cases)
    also from \<open>conflict N \<beta> S1 S2\<close> have "\<dots> = state_trail S1"
      by (auto elim: conflict.cases)
    finally have "state_trail S3 = state_trail S1"
      by assumption
    from \<open>propagate N \<beta> S0 S1\<close> obtain L C \<gamma> where
      "state_trail S1 = trail_propagate (state_trail S0) L C \<gamma>"
      by (auto elim: propagate.cases)

    from \<open>(factorize N \<beta>)\<^sup>*\<^sup>* S2 S3\<close> have "state_learned S3 = state_learned S2"
    proof (induction S3 rule: rtranclp_induct)
      case base
      show ?case by simp
    next
      case (step y z)
      thus ?case
        by (elim factorize.cases) simp
    qed
    also from \<open>conflict N \<beta> S1 S2\<close> have "\<dots> = state_learned S1"
      by (auto elim: conflict.cases)
    finally have "state_learned S3 = state_learned S1"
      by assumption

    from \<open>propagate N \<beta> S0 S1\<close> have "state_learned S1 = state_learned S0"
      by (auto elim: propagate.cases)

    assume "S3 = S"
    hence no_conf_with_trail: "no_conflict_with_trail N \<beta> (state_learned S0) (state_trail S0)"
      using \<open>almost_no_conflict_with_trail N \<beta> S\<close> \<open>{#} |\<notin>| N\<close>
        \<open>state_trail S1 = trail_propagate (state_trail S0) L C \<gamma>\<close> \<open>state_trail S3 = state_trail S1\<close>
        \<open>state_learned S3 = state_learned S1\<close> \<open>state_learned S1 = state_learned S0\<close>
      by (simp add: almost_no_conflict_with_trail_def trail_propagate_def is_decision_lit_def)
    hence "{#} |\<notin>| state_learned S0"
      using nex_conflict_if_no_conflict_with_trail'[folded mempty_in_iff_ex_conflict] by simp

    have "\<exists>D \<gamma>\<^sub>D. state_conflict S2 = Some (D, \<gamma>\<^sub>D) \<and> - (L \<cdot>l \<gamma>) \<in># D \<cdot> \<gamma>\<^sub>D"
      using \<open>conflict N \<beta> S1 S2\<close>
    proof (cases N \<beta> S1 S2 rule: conflict.cases)
      case (conflictI D U \<gamma>\<^sub>D \<Gamma>)
      hence "trail_false_cls (trail_propagate (state_trail S0) L C \<gamma>) (D \<cdot> \<gamma>\<^sub>D)"
        using \<open>state_trail S1 = trail_propagate (state_trail S0) L C \<gamma>\<close>
        by simp

      moreover from no_conf_with_trail have "\<not> trail_false_cls (state_trail S0) (D \<cdot> \<gamma>\<^sub>D)"
      proof (rule not_trail_false_cls_if_no_conflict_with_trail)
        show "D |\<in>| N |\<union>| state_learned S0"
          using \<open>state_learned S1 = state_learned S0\<close> local.conflictI(1) local.conflictI(3)
          by fastforce
      next
        have "{#} |\<notin>| U"
          using \<open>{#} |\<notin>| state_learned S0\<close> \<open>S3 = S\<close> \<open>state_learned S3 = state_learned S1\<close>
            \<open>state_learned S1 = state_learned S0\<close>
          unfolding conflictI(1,2)
          by simp
        thus "D \<noteq> {#}"
          using \<open>{#} |\<notin>| N\<close> \<open>D |\<in>| N |\<union>| U\<close>
          by auto
      next
        show "is_ground_cls (D \<cdot> \<gamma>\<^sub>D)"
          by (rule \<open>is_ground_cls (D \<cdot> \<gamma>\<^sub>D)\<close>)
      next
        show "subst_domain \<gamma>\<^sub>D \<subseteq> vars_cls D"
          by (rule \<open>subst_domain \<gamma>\<^sub>D \<subseteq> vars_cls D\<close>)
      qed

      ultimately have "- (L \<cdot>l \<gamma>) \<in># D \<cdot> \<gamma>\<^sub>D"
        by (metis subtrail_falseI trail_propagate_def)

      moreover have "state_conflict S2 = Some (D, \<gamma>\<^sub>D)"
        unfolding conflictI(1,2) by simp

      ultimately show ?thesis
        by metis
    qed
    then obtain D \<gamma>\<^sub>D where "state_conflict S2 = Some (D, \<gamma>\<^sub>D)" and "- (L \<cdot>l \<gamma>) \<in># D \<cdot> \<gamma>\<^sub>D"
      by metis
    with \<open>(factorize N \<beta>)\<^sup>*\<^sup>* S2 S3\<close>
    have "\<exists>D' \<gamma>\<^sub>D'. state_conflict S3 = Some (D', \<gamma>\<^sub>D') \<and> - (L \<cdot>l \<gamma>) \<in># D' \<cdot> \<gamma>\<^sub>D'"
    proof (induction S3 arbitrary: rule: rtranclp_induct)
      case base
      thus ?case by simp
    next
      case (step y z)
      then obtain D' \<gamma>\<^sub>D' where "state_conflict y = Some (D', \<gamma>\<^sub>D')" and "- (L \<cdot>l \<gamma>) \<in># D' \<cdot> \<gamma>\<^sub>D'"
        by auto
      then show ?case
        using step.hyps(2)
        by (metis conflict_set_after_factorization)
    qed
    with backt \<open>S3 = S\<close> show False
      using \<open>state_trail S3 = state_trail S1\<close>
      unfolding \<open>S3 = S\<close> \<open>state_trail S1 = trail_propagate (state_trail S0) L C \<gamma>\<close>
      by (auto simp add: trail_decide_def trail_propagate_def elim!: backtrack.cases)
  qed
  with maybe_resolution obtain S4 where
    "resolve N \<beta> S3 S4" and "(skip N \<beta> \<squnion> factorize N \<beta> \<squnion> resolve N \<beta>)\<^sup>*\<^sup>* S4 S"
    by metis
  show ?thesis
  proof (intro exI conjI)
    show "(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S0"
      by (rule \<open>(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S0\<close>)
  next
    show "propagate N \<beta> S0 S1"
      by (rule \<open>propagate N \<beta> S0 S1\<close>)
  next
    show "regular_scl N \<beta> S0 S1"
      by (rule propa(2))
  next
    show "conflict N \<beta> S1 S2"
      by (rule \<open>conflict N \<beta> S1 S2\<close>)
  next
    show "(factorize N \<beta>)\<^sup>*\<^sup>* S2 S3"
      by (rule \<open>(factorize N \<beta>)\<^sup>*\<^sup>* S2 S3\<close>)
  next
    show "resolve N \<beta> S3 S4"
      by (rule \<open>resolve N \<beta> S3 S4\<close>)
  next
    show "(skip N \<beta> \<squnion> factorize N \<beta> \<squnion> resolve N \<beta>)\<^sup>*\<^sup>* S4 S"
      by (rule \<open>(skip N \<beta> \<squnion> factorize N \<beta> \<squnion> resolve N \<beta>)\<^sup>*\<^sup>* S4 S\<close>)
  qed
qed


section \<open>Resolve in Regular Runs\<close>

lemma resolve_if_conflict_follows_propagate:
  assumes
    no_conf: "\<nexists>S\<^sub>1. conflict N \<beta> S\<^sub>0 S\<^sub>1" and
    propa: "propagate N \<beta> S\<^sub>0 S\<^sub>1" and
    conf: "conflict N \<beta> S\<^sub>1 S\<^sub>2"
  shows "\<exists>S\<^sub>3. resolve N \<beta> S\<^sub>2 S\<^sub>3"
  using propa
proof (cases N \<beta> S\<^sub>0 S\<^sub>1 rule: propagate.cases)
  case (propagateI C U L C' \<gamma> C\<^sub>0 C\<^sub>1 \<Gamma> \<mu> \<gamma>')
  hence S\<^sub>0_def: "S\<^sub>0 = (\<Gamma>, U, None)"
    by simp

  from conf obtain \<gamma>\<^sub>D D where
    S\<^sub>2_def: "S\<^sub>2 = (trail_propagate \<Gamma> (L \<cdot>l \<mu>) (C\<^sub>0 \<cdot> \<mu>) \<gamma>', U, Some (D, \<gamma>\<^sub>D))" and
    D_in: "D |\<in>| N |\<union>| U" and
    dom_\<gamma>\<^sub>D: "subst_domain \<gamma>\<^sub>D \<subseteq> vars_cls D" and
    gr_D_\<gamma>\<^sub>D: "is_ground_cls (D \<cdot> \<gamma>\<^sub>D)" and
    tr_false_\<Gamma>_L_\<mu>: "trail_false_cls (trail_propagate \<Gamma> (L \<cdot>l \<mu>) (C\<^sub>0 \<cdot> \<mu>) \<gamma>') (D \<cdot> \<gamma>\<^sub>D)"
    by (elim conflict.cases) (unfold propagateI(1,2), blast)

  from no_conf have "\<not> trail_false_cls \<Gamma> (D \<cdot> \<gamma>\<^sub>D)"
    using gr_D_\<gamma>\<^sub>D D_in not_trail_false_ground_cls_if_no_conflict[of N \<beta> _ D \<gamma>\<^sub>D]
    using S\<^sub>0_def by force
  with tr_false_\<Gamma>_L_\<mu> have "- (L \<cdot>l \<mu> \<cdot>l \<gamma>') \<in># D \<cdot> \<gamma>\<^sub>D"
    unfolding trail_propagate_def by (metis subtrail_falseI)
  then obtain D' L' where D_def: "D = add_mset L' D'" and "- (L \<cdot>l \<mu> \<cdot>l \<gamma>') = L' \<cdot>l \<gamma>\<^sub>D"
    by (meson Melem_subst_cls multi_member_split)
  hence 1: "L \<cdot>l \<mu> \<cdot>l \<gamma>' = - (L' \<cdot>l \<gamma>\<^sub>D)"
    by (metis uminus_of_uminus_id)

  define \<rho> where
    "\<rho> = renaming_wrt {add_mset L C\<^sub>0 \<cdot> \<mu>}"

  have "is_renaming \<rho>"
    by (metis \<rho>_def finite.emptyI finite.insertI is_renaming_renaming_wrt)
  hence "\<forall>x. is_Var (\<rho> x)" and "inj \<rho>"
    by (simp_all add: is_renaming_iff)

  have vars_subst_cls_\<rho>_disjoint: "\<And>C. vars_cls (C \<cdot> \<rho>) \<inter> vars_cls (add_mset L C\<^sub>0 \<cdot> \<mu>) = {}"
    by (smt (verit, best) Int_Un_distrib UN_Un Union_image_insert \<rho>_def finite.emptyI finite_UN
        finite_insert finite_vars_cls sup_bot.right_neutral vars_cls_subst_renaming_disj)

  have "\<exists>\<mu>'. Unification.mgu (atm_of L \<cdot>a \<mu>) (atm_of L' \<cdot>a \<rho>) = Some \<mu>'"
  proof (rule ex_mgu_if_subst_eq_subst_and_disj_vars)
    have "vars_lit L' \<subseteq> subst_domain \<gamma>\<^sub>D"
      using gr_D_\<gamma>\<^sub>D[unfolded D_def]
      by (simp add: vars_lit_subset_subst_domain_if_grounding is_ground_cls_imp_is_ground_lit)
    hence "atm_of L' \<cdot>a \<rho> \<cdot>a rename_subst_domain \<rho> \<gamma>\<^sub>D = atm_of L' \<cdot>a \<gamma>\<^sub>D"
      by (rule renaming_cancels_rename_subst_domain[OF \<open>\<forall>x. is_Var (\<rho> x)\<close> \<open>inj \<rho>\<close>])
    then show "atm_of L \<cdot>a \<mu> \<cdot>a \<gamma>' = atm_of L' \<cdot>a \<rho> \<cdot>a rename_subst_domain \<rho> \<gamma>\<^sub>D"
      using 1 by (metis atm_of_subst_lit atm_of_uminus)
  next
    show "vars_term (atm_of L \<cdot>a \<mu>) \<inter> vars_term (atm_of L' \<cdot>a \<rho>) = {}"
      using vars_subst_cls_\<rho>_disjoint[of "{#L'#}"] by auto
  qed
  then obtain \<mu>' where mimgu_\<mu>': "is_mimgu \<mu>' {{atm_of (L \<cdot>l \<mu>), atm_of L' \<cdot>a \<rho>}}"
    using is_mimgu_if_mgu_eq_Some by auto

  let ?\<Gamma>prop = "trail_propagate \<Gamma> (L \<cdot>l \<mu>) (C\<^sub>0 \<cdot> \<mu>) \<gamma>'"
  let ?\<gamma>reso = "restrict_subst_domain (vars_cls ((D' \<cdot> \<rho> + C\<^sub>0 \<cdot> \<mu>) \<cdot> \<mu>')) (rename_subst_domain \<rho> \<gamma>\<^sub>D \<odot> \<gamma>')"

  have "resolve N \<beta>
   (?\<Gamma>prop, U, Some (add_mset L' D', \<gamma>\<^sub>D))
   (?\<Gamma>prop, U, Some ((D' \<cdot> \<rho> + C\<^sub>0 \<cdot> \<mu>) \<cdot> \<mu>', ?\<gamma>reso))"
  proof (rule resolveI[OF refl])
    show "L \<cdot>l \<mu> \<cdot>l \<gamma>' = - (L' \<cdot>l \<gamma>\<^sub>D)"
      by (rule 1)
  next
    show "is_renaming \<rho>"
      by (metis \<rho>_def finite.emptyI finite.insertI is_renaming_renaming_wrt)
  next
    show "vars_cls (add_mset L' D' \<cdot> \<rho>) \<inter> vars_cls (add_mset (L \<cdot>l \<mu>) (C\<^sub>0 \<cdot> \<mu>)) = {}"
      using vars_subst_cls_\<rho>_disjoint[of "add_mset L' D'"] by simp
  next
    show "is_mimgu \<mu>' {{atm_of (L \<cdot>l \<mu>), atm_of L' \<cdot>a \<rho>}}"
      by (rule mimgu_\<mu>')
  qed
  thus ?thesis
    unfolding S\<^sub>2_def D_def by metis
qed

lemma factorize_preserves_resolvability:
  assumes reso: "resolve N \<beta> S\<^sub>1 S\<^sub>2" and fact: "factorize N \<beta> S\<^sub>1 S\<^sub>3" and
    invar: "minimal_ground_closures S\<^sub>1"
  shows "\<exists>S\<^sub>4. resolve N \<beta> S\<^sub>3 S\<^sub>4"
  using reso
proof (cases N \<beta> S\<^sub>1 S\<^sub>2 rule: resolve.cases)
  case (resolveI \<Gamma> \<Gamma>' L C \<delta> L' \<sigma> \<rho> D \<mu> U)

  from fact obtain K K' \<mu>\<^sub>K \<sigma>' DD where
    S\<^sub>1_def: "S\<^sub>1 = (\<Gamma>, U, Some (add_mset K' (add_mset K DD), \<sigma>))" and
    S\<^sub>3_def: "S\<^sub>3 = (\<Gamma>, U, Some (add_mset K DD \<cdot> \<mu>\<^sub>K, \<sigma>'))" and
    "K \<cdot>l \<sigma> = K' \<cdot>l \<sigma>" and
    mimgu_\<mu>\<^sub>K: "is_mimgu \<mu>\<^sub>K {{atm_of K, atm_of K'}}" and
    \<sigma>'_def: "\<sigma>' = restrict_subst_domain (vars_cls (add_mset K DD \<cdot> \<mu>\<^sub>K)) \<sigma>"
    by (auto simp: \<open>S\<^sub>1 = (\<Gamma>, U, Some (add_mset L' D, \<sigma>))\<close> elim: factorize.cases)

  from invar have
    dom_\<sigma>: "subst_domain \<sigma> \<subseteq> vars_cls (add_mset L' D)" and
    ground_conf_\<sigma>: "is_ground_cls (add_mset L' D \<cdot> \<sigma>)"
    unfolding resolveI(1,2)
    by (simp_all add: minimal_ground_closures_def)

  have "add_mset L' D = add_mset K' (add_mset K DD)"
    using resolveI(1) S\<^sub>1_def by simp

  from mimgu_\<mu>\<^sub>K have "\<sigma> = \<mu>\<^sub>K \<odot> \<sigma>"
    using \<open>K \<cdot>l \<sigma> = K' \<cdot>l \<sigma>\<close>
    by (auto simp add: is_mimgu_def is_imgu_def is_unifiers_def is_unifier_alt
        intro!: subst_atm_of_eqI)

  have L_\<mu>\<^sub>K_\<sigma>'_simp: "L \<cdot>l \<mu>\<^sub>K \<cdot>l \<sigma>' = L \<cdot>l \<mu>\<^sub>K \<cdot>l \<sigma>" if L_in: "L \<in># add_mset K DD" for L
    unfolding \<sigma>'_def
    using L_in
    by (metis insert_DiffM subst_lit_restrict_subst_domain sup_ge1 vars_cls_add_mset
        vars_lit_subst_subset_vars_cls_substI)

  have "L' \<cdot>l \<mu>\<^sub>K \<in># add_mset K DD \<cdot> \<mu>\<^sub>K"
  proof (cases "L' = K \<or> L' = K'")
    case True
    moreover have "K \<cdot>l \<mu>\<^sub>K = K' \<cdot>l \<mu>\<^sub>K"
      using mimgu_\<mu>\<^sub>K[unfolded is_mimgu_def, THEN conjunct1, unfolded is_imgu_def, THEN conjunct1,
          unfolded is_unifiers_def, simplified]
      by (metis (no_types, opaque_lifting) \<open>K \<cdot>l \<sigma> = K' \<cdot>l \<sigma>\<close> atm_of_subst_lit finite.emptyI
          finite.insertI insertCI is_unifier_subst_atm_eqI literal.expand subst_lit_is_neg)
    ultimately have "L' \<cdot>l \<mu>\<^sub>K = K \<cdot>l \<mu>\<^sub>K"
      by presburger
    thus ?thesis
      by simp
  next
    case False
    hence "L' \<in># DD"
      by (metis \<open>add_mset L' D = add_mset K' (add_mset K DD)\<close> insert_iff set_mset_add_mset_insert)
    thus ?thesis
      by auto
  qed
  then obtain DDD where "add_mset K DD \<cdot> \<mu>\<^sub>K = add_mset L' DDD \<cdot> \<mu>\<^sub>K"
    by (smt (verit, best) Melem_subst_cls mset_add subst_cls_add_mset)

  define \<rho>\<rho> where
    "\<rho>\<rho> = renaming_wrt {add_mset L C}"

  have ren_\<rho>\<rho>: "is_renaming \<rho>\<rho>"
    by (metis \<rho>\<rho>_def finite.emptyI finite.insertI is_renaming_renaming_wrt)

  have vars_subst_cls_\<rho>\<rho>_disjoint: "\<And>D. vars_cls (D \<cdot> \<rho>\<rho>) \<inter> vars_cls (add_mset L C) = {}"
    by (simp add: \<rho>\<rho>_def vars_cls_subst_renaming_disj)

  have "L \<cdot>l \<delta> = - (L' \<cdot>l \<mu>\<^sub>K \<cdot>l \<sigma>')"
  proof -
    have "L' \<cdot>l \<mu>\<^sub>K \<cdot>l \<sigma>' = L' \<cdot>l \<mu>\<^sub>K \<cdot>l \<sigma>"
      using L_\<mu>\<^sub>K_\<sigma>'_simp
      by (metis Melem_subst_cls \<open>L' \<cdot>l \<mu>\<^sub>K \<in># add_mset K DD \<cdot> \<mu>\<^sub>K\<close>)
    also have "... = L' \<cdot>l \<sigma>"
      using \<open>\<sigma> = \<mu>\<^sub>K \<odot> \<sigma>\<close>
      by (metis subst_lit_comp_subst)
    finally show ?thesis
      using resolveI by simp
  qed

  obtain \<mu>\<mu> where mimgu_\<mu>\<mu>: "is_mimgu \<mu>\<mu> {{atm_of L, atm_of (L' \<cdot>l \<mu>\<^sub>K) \<cdot>a \<rho>\<rho>}}"
  proof -
    assume "\<And>\<mu>\<mu>. is_mimgu \<mu>\<mu> {{atm_of L, atm_of (L' \<cdot>l \<mu>\<^sub>K) \<cdot>a \<rho>\<rho>}} \<Longrightarrow> thesis"
    moreover have "\<exists>\<mu>. Unification.mgu (atm_of L) (atm_of L' \<cdot>a \<mu>\<^sub>K \<cdot>a \<rho>\<rho>) = Some \<mu>"
    proof (rule ex_mgu_if_subst_eq_subst_and_disj_vars)
      have "is_ground_atm (atm_of L' \<cdot>a \<mu>\<^sub>K \<cdot>a \<sigma>')"
        using \<open>L \<cdot>l \<delta> = - (L' \<cdot>l \<mu>\<^sub>K \<cdot>l \<sigma>')\<close> \<open>L \<cdot>l \<delta> = - (L' \<cdot>l \<sigma>)\<close>
        using ground_conf_\<sigma> is_ground_lit_def local.resolveI(4) by force
      hence "vars_term (atm_of L' \<cdot>a \<mu>\<^sub>K) \<subseteq> subst_domain \<sigma>'"
        by (rule vars_atm_subset_subst_domain_if_grounding)
      hence "atm_of L' \<cdot>a \<mu>\<^sub>K \<cdot>a \<rho>\<rho> \<cdot>a rename_subst_domain \<rho>\<rho> \<sigma>' = atm_of L' \<cdot>a \<mu>\<^sub>K \<cdot>a \<sigma>'"
        using ren_\<rho>\<rho>
        by (simp add: renaming_cancels_rename_subst_domain is_renaming_iff)
      thus "atm_of L \<cdot>a \<delta> = atm_of L' \<cdot>a \<mu>\<^sub>K \<cdot>a \<rho>\<rho> \<cdot>a rename_subst_domain \<rho>\<rho> \<sigma>'"
        using \<open>L \<cdot>l \<delta> = - (L' \<cdot>l \<mu>\<^sub>K \<cdot>l \<sigma>')\<close>
        by (metis atm_of_subst_lit atm_of_uminus)
    next
      show "vars_lit L \<inter> vars_term (atm_of L' \<cdot>a \<mu>\<^sub>K \<cdot>a \<rho>\<rho>) = {}"
        using vars_subst_cls_\<rho>\<rho>_disjoint[of "{#L' \<cdot>l \<mu>\<^sub>K#}"] by auto
    qed
    ultimately show ?thesis
      using is_mimgu_if_mgu_eq_Some by auto
  qed

  show ?thesis
    unfolding S\<^sub>3_def \<open>add_mset K DD \<cdot> \<mu>\<^sub>K = add_mset L' DDD \<cdot> \<mu>\<^sub>K\<close>
    using resolve.resolveI[OF \<open>\<Gamma> = trail_propagate \<Gamma>' L C \<delta>\<close> \<open>L \<cdot>l \<delta> = - (L' \<cdot>l \<mu>\<^sub>K \<cdot>l \<sigma>')\<close> ren_\<rho>\<rho>
        vars_subst_cls_\<rho>\<rho>_disjoint mimgu_\<mu>\<mu>, of N \<beta> U "DDD \<cdot> \<mu>\<^sub>K"]
    by auto
qed

text \<open>The following lemma corresponds to Lemma 7 in the paper.\<close>

lemma no_backtrack_after_conflict_if:
  assumes conf: "conflict N \<beta> S1 S2" and trail_S2: "state_trail S1 = trail_propagate \<Gamma> L C \<gamma>"
  shows "\<nexists>S4. backtrack N \<beta> S2 S4"
proof -
  from trail_S2 conf have "state_trail S2 = trail_propagate \<Gamma> L C \<gamma>"
    unfolding conflict.simps by auto
  then show ?thesis
    unfolding backtrack.simps trail_propagate_def trail_decide_def
    by auto
qed

lemma skip_state_trail: "skip N \<beta> S S' \<Longrightarrow> suffix (state_trail S') (state_trail S)"
  by (auto simp: suffix_def elim: skip.cases)

lemma factorize_state_trail: "factorize N \<beta> S S' \<Longrightarrow> state_trail S' = state_trail S"
  by (auto elim: factorize.cases)

lemma resolve_state_trail: "resolve N \<beta> S S' \<Longrightarrow> state_trail S' = state_trail S"
  by (auto elim: resolve.cases)

lemma mempty_not_in_initial_clauses_if_run_leads_to_trail:
  assumes
    reg_run: "(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S1" and
    trail_lit: "state_trail S1 = Lc # \<Gamma>"
  shows "{#} |\<notin>| N"
proof (rule notI)
  assume "{#} |\<in>| N"
  hence "conflict N \<beta> initial_state ([], {||}, Some ({#}, Var))"
    by (rule conflict_initial_state_if_mempty_in_intial_clauses)
  moreover hence "\<nexists>S'. local.scl N \<beta> ([], {||}, Some ({#}, Var)) S'"
    using no_more_step_if_conflict_mempty by simp
  ultimately show False
    using trail_lit
    by (metis (no_types, opaque_lifting) conflict_initial_state_only_with_mempty converse_rtranclpE
        list.discI prod.sel(1) reasonable_if_regular reg_run regular_scl_def scl_if_reasonable
        state_trail_def)
qed

(*
after conflict, one can apply factorize arbitrarily often,
but resolve must be applied at least once.

Prove this lemma!
conflict in reg run \<Longrightarrow> ALL following runs have the following shape:
  factorize* then resolve then (skip or factorize or resolve)*
*)

lemma conflict_with_literal_gets_resolved:
  assumes
    trail_lit: "state_trail S1 = Lc # \<Gamma>" and
    conf: "conflict N \<beta> S1 S2" and
    resolution: "(skip N \<beta> \<squnion> factorize N \<beta> \<squnion> resolve N \<beta>)\<^sup>*\<^sup>* S2 Sn" and
    backtrack: "\<exists>Sn'. backtrack N \<beta> Sn Sn'" and
    mempty_not_in_init_clss: "{#} |\<notin>| N" and
    invars: "learned_nonempty S1" "trail_propagated_or_decided' N \<beta> S1" "no_conflict_after_decide' N \<beta> S1"
  shows "\<not> is_decision_lit Lc \<and> strict_suffix (state_trail Sn) (state_trail S1)"
proof -
  obtain S0 where propa: "propagate N \<beta> S0 S1"
    using mempty_not_in_init_clss before_reasonable_conflict[OF conf \<open>learned_nonempty S1\<close>
        \<open>trail_propagated_or_decided' N \<beta> S1\<close> \<open>no_conflict_after_decide' N \<beta> S1\<close>] by metis

  from trail_lit propa have "\<not> is_decision_lit Lc"
    by (auto simp: trail_propagate_def is_decision_lit_def elim!: propagate.cases)

  show ?thesis
  proof (rule conjI)
    show "\<not> is_decision_lit Lc"
      by (rule \<open>\<not> is_decision_lit Lc\<close>)
  next
    show "strict_suffix (state_trail Sn) (state_trail S1)"
      unfolding strict_suffix_def
    proof (rule conjI)
      from conf have "state_trail S2 = state_trail S1"
        by (auto elim: conflict.cases)
      moreover from resolution have "suffix (state_trail Sn) (state_trail S2)"
      proof (induction Sn rule: rtranclp_induct)
        case base
        thus ?case
          by simp
      next
        case (step y z)
        from step.hyps(2) have "suffix (state_trail z) (state_trail y)"
          by (auto simp: suffix_def factorize_state_trail resolve_state_trail
              dest: skip_state_trail)
        with step.IH show ?case
          by (auto simp: suffix_def)
      qed
      ultimately show "suffix (state_trail Sn) (state_trail S1)"
        by simp
    next
      from backtrack \<open>\<not> is_decision_lit Lc\<close> show "state_trail Sn \<noteq> state_trail S1"
        unfolding trail_lit
        by (auto simp: trail_decide_def is_decision_lit_def elim!: backtrack.cases)
    qed
  qed
qed


section \<open>Clause Redundancy\<close>

definition ground_redundant where
  "ground_redundant lt N C \<longleftrightarrow>
    is_ground_clss N \<and> is_ground_cls C \<and> {D \<in> N. lt\<^sup>=\<^sup>= D C} \<TTurnstile>e {C}"

definition redundant where
  "redundant lt N C \<longleftrightarrow>
    (\<forall>C' \<in> grounding_of_cls C. ground_redundant lt (grounding_of_clss N) C')"

lemma ground_redundant_mono_strong:
  "ground_redundant R N C \<Longrightarrow> (\<And>x. x \<in> N \<Longrightarrow> x \<noteq> C \<Longrightarrow> R x C \<Longrightarrow> S x C) \<Longrightarrow> ground_redundant S N C"
  unfolding ground_redundant_def
  apply (simp add: true_clss_def)
  by blast

lemma redundant_mono_strong:
  "redundant R N C \<Longrightarrow>
    (\<And>x y. x \<in> grounding_of_clss N \<Longrightarrow> y \<in> grounding_of_cls C \<Longrightarrow> x \<noteq> y \<Longrightarrow> R x y \<Longrightarrow> S x y) \<Longrightarrow>
  redundant S N C"
  by (auto simp: redundant_def
      intro: ground_redundant_mono_strong[of R "grounding_of_clss N" _ S])

lemma redundant_multp_if_redundant_strict_subset:
  "redundant (\<subset>#) N C \<Longrightarrow> redundant (multp (trail_less_ex lt Ls)) N C"
  by (auto intro: subset_implies_multp elim!: redundant_mono_strong)

lemma redundant_multp_if_redundant_subset:
  "redundant (\<subseteq>#) N C \<Longrightarrow> redundant (multp (trail_less_ex lt Ls)) N C"
  by (auto intro: subset_implies_multp elim!: redundant_mono_strong)

lemma not_bex_subset_mset_if_not_ground_redundant:
  assumes "is_ground_cls C" and "is_ground_clss N"
  shows "\<not> ground_redundant (\<subset>#) N C \<Longrightarrow> \<not> (\<exists>D \<in> N. D \<subseteq># C)"
  using assms unfolding ground_redundant_def
  apply (simp add: true_cls_def true_clss_def)
  apply (elim exE conjE)
  apply (rule ballI)
  subgoal premises prems for I D
    using prems(3)[rule_format, of D] prems(1,2,4-)
    apply simp
    by (meson mset_subset_eqD subset_mset.nless_le)
  done


section \<open>Trail-Induced Ordering\<close>

subsection \<open>Miscellaneous Lemmas\<close>

lemma pairwise_distinct_if_trail_consistent:
  fixes \<Gamma>
  defines "Ls \<equiv> (map fst \<Gamma>)"
  shows "trail_consistent \<Gamma> \<Longrightarrow>
    \<forall>i < length Ls. \<forall>j < length Ls. i \<noteq> j \<longrightarrow> Ls ! i \<noteq> Ls ! j \<and> Ls ! i \<noteq> - (Ls ! j)"
  unfolding Ls_def
proof (induction \<Gamma> rule: trail_consistent.induct)
  case Nil
  show ?case by simp
next
  case (Cons \<Gamma> L u)
  from Cons.hyps have L_distinct:
    "\<forall>x < length (map fst \<Gamma>). map fst \<Gamma> ! x \<noteq> L"
    "\<forall>x < length (map fst \<Gamma>). map fst \<Gamma> ! x \<noteq> - L"
    unfolding trail_defined_lit_def de_Morgan_disj
    unfolding image_set in_set_conv_nth not_ex de_Morgan_conj disj_not1
    by simp_all
  show ?case
    unfolding list.map prod.sel
  proof (intro allI impI)
    fix i j :: nat
    assume i_lt: "i < length (L # map fst \<Gamma>)" and j_lt: "j < length (L # map fst \<Gamma>)" and "i \<noteq> j"
    show
      "(L # map fst \<Gamma>) ! i \<noteq> (L # map fst \<Gamma>) ! j \<and>
       (L # map fst \<Gamma>) ! i \<noteq> - (L # map fst \<Gamma>) ! j"
    proof (cases i)
      case 0
      thus ?thesis
        using L_distinct \<open>i \<noteq> j\<close> \<open>j < length (L # map fst \<Gamma>)\<close>
        using gr0_conv_Suc by auto
    next
      case (Suc k)
      then show ?thesis
        apply simp
        using i_lt j_lt \<open>i \<noteq> j\<close> L_distinct Cons.IH[rule_format]
        using less_Suc_eq_0_disj by force
    qed
  qed
qed


subsection \<open>Strict Partial Order\<close>

lemma irreflp_trail_less_if_trail_consistant:
  "trail_consistent \<Gamma> \<Longrightarrow> irreflp (trail_less (map fst \<Gamma>))"
  using irreflp_trail_less[OF
      Clausal_Logic.uminus_not_id'
      Clausal_Logic.uminus_of_uminus_id
      pairwise_distinct_if_trail_consistent]
  by assumption

lemma transp_trail_less_if_trail_consistant:
  "trail_consistent \<Gamma> \<Longrightarrow> transp (trail_less (map fst \<Gamma>))"
  using transp_trail_less[OF
      Clausal_Logic.uminus_not_id'
      Clausal_Logic.uminus_of_uminus_id
      pairwise_distinct_if_trail_consistent]
  by assumption

lemma asymp_trail_less_if_trail_consistant:
  "trail_consistent \<Gamma> \<Longrightarrow> asymp (trail_less (map fst \<Gamma>))"
  using asymp_trail_less[OF
      Clausal_Logic.uminus_not_id'
      Clausal_Logic.uminus_of_uminus_id
      pairwise_distinct_if_trail_consistent]
  by assumption


subsection \<open>Extension on All Literals\<close>

lemma transp_trail_less_ex_if_trail_consistant:
  "trail_consistent \<Gamma> \<Longrightarrow> transp lt \<Longrightarrow> transp (trail_less_ex lt (map fst \<Gamma>))"
  using transp_trail_less_ex[OF
      Clausal_Logic.uminus_not_id'
      Clausal_Logic.uminus_of_uminus_id
      pairwise_distinct_if_trail_consistent]
  by assumption

lemma asymp_trail_less_ex_if_trail_consistant:
  "trail_consistent \<Gamma> \<Longrightarrow> asymp lt \<Longrightarrow> asymp (trail_less_ex lt (map fst \<Gamma>))"
  using asymp_trail_less_ex[OF
      Clausal_Logic.uminus_not_id'
      Clausal_Logic.uminus_of_uminus_id
      pairwise_distinct_if_trail_consistent]
  by assumption


subsection \<open>Properties\<close>

lemma trail_defined_if_trail_less_ex:
  "trail_less_ex lt (map fst \<Gamma>) L K \<Longrightarrow> trail_defined_lit \<Gamma> K \<Longrightarrow> trail_defined_lit \<Gamma> L"
  by (metis (no_types, opaque_lifting) list.set_map trail_defined_lit_def trail_less_ex_def)

lemma trail_defined_cls_if_lt_defined:
  assumes consistent_\<Gamma>: "trail_consistent \<Gamma>" and
    transp_lt: "transp lt" and
    C_lt_D: "multp (trail_less_ex lt (map fst \<Gamma>)) C D" and
    tr_def_D: "trail_defined_cls \<Gamma> D"
  shows "trail_defined_cls \<Gamma> C"
proof -
  have transp_tr_lt_ex: "transp (trail_less_ex lt (map fst \<Gamma>))"
    by (rule transp_trail_less_ex_if_trail_consistant[OF consistent_\<Gamma> transp_lt])

  from multp_implies_one_step[OF transp_tr_lt_ex C_lt_D]
  obtain I J K where D_def: "D = I + J" and C_def: "C = I + K" and "J \<noteq> {#}" and
    *: "\<forall>k\<in>#K. \<exists>x\<in>#J. trail_less_ex lt (map fst \<Gamma>) k x"
    by auto

  show ?thesis
    unfolding trail_defined_cls_def
  proof (rule ballI)
    fix L assume L_in: "L \<in># C"
    show "trail_defined_lit \<Gamma> L"
    proof (cases "L \<in># I")
      case True
      then show ?thesis
        using tr_def_D D_def
        by (simp add: trail_defined_cls_def)
    next
      case False
      with C_def L_in have "L \<in># K" by fastforce
      then obtain L' where L'_in: "L'\<in>#J" and "trail_less_ex lt (map fst \<Gamma>) L L'"
        using * by blast
      moreover have "trail_defined_lit \<Gamma> L'"
        using tr_def_D D_def L'_in
        by (simp add: trail_defined_cls_def)
      ultimately show ?thesis
        by (auto intro: trail_defined_if_trail_less_ex)
    qed
  qed
qed


section \<open>Learned Clauses in Regular Runs\<close>

lemma regular_run_if_skip_factorize_resolve_run:
  assumes "(skip N \<beta> \<squnion> factorize N \<beta> \<squnion> resolve N \<beta>)\<^sup>*\<^sup>* S S'"
  shows "(regular_scl N \<beta>)\<^sup>*\<^sup>* S S'"
  using assms
proof (induction S' rule: rtranclp_induct)
  case base
  show ?case by simp
next
  case (step S' S'')
  from step.hyps(2) have "scl N \<beta> S' S''"
    unfolding scl_def by blast
  with step.hyps(2) have "reasonable_scl N \<beta> S' S''"
    using reasonable_scl_def decide_well_defined(4) decide_well_defined(5) skip_well_defined(2)
    by blast
  moreover from step.hyps(2) have "\<not> Ex (conflict N \<beta> S')"
    apply simp
    by (smt (verit, best) conflict.cases factorize.simps option.distinct(1) resolve.simps skip.simps
        state_conflict_simp)
  ultimately have "regular_scl N \<beta> S' S''"
    by (simp add: regular_scl_def)
  with step.IH show ?case
    by simp
qed

lemma not_trail_true_and_false_lit:
  "trail_consistent \<Gamma> \<Longrightarrow> \<not> (trail_true_lit \<Gamma> L \<and> trail_false_lit \<Gamma> L)"
  apply (simp add: trail_true_lit_def trail_false_lit_def)
  by (metis (no_types, lifting) in_set_conv_nth list.set_map pairwise_distinct_if_trail_consistent
      uminus_not_id')

lemma not_trail_true_and_false_cls:
  "trail_consistent \<Gamma> \<Longrightarrow> \<not> (trail_true_cls \<Gamma> C \<and> trail_false_cls \<Gamma> C)"
  using not_trail_true_and_false_lit
  by (metis trail_false_cls_def trail_true_cls_def)

theorem learned_clauses_in_regular_runs_invars:
  assumes
    sound_S0: "sound_state N \<beta> S0" and
    invars: "learned_nonempty S0" "trail_propagated_or_decided' N \<beta> S0"
      "no_conflict_after_decide' N \<beta> S0" "almost_no_conflict_with_trail N \<beta> S0"
      "trail_lits_consistent S0" and
    conflict: "conflict N \<beta> S0 S1" and
    resolution: "(skip N \<beta> \<squnion> factorize N \<beta> \<squnion> resolve N \<beta>)\<^sup>+\<^sup>+ S1 Sn" and
    backtrack: "backtrack N \<beta> Sn Sn'" and
    "transp lt"
  defines
    "trail_ord \<equiv> multp (trail_less_ex lt (map fst (state_trail S1)))" and
    "U \<equiv> state_learned S1"
  shows "(\<exists>C \<gamma>. state_conflict Sn = Some (C, \<gamma>) \<and>
      C \<cdot> \<gamma> \<notin> grounding_of_clss (fset N \<union> fset U) \<and>
      set_mset (C \<cdot> \<gamma>) \<notin> set_mset ` grounding_of_clss (fset N \<union> fset U) \<and>
      \<not> redundant trail_ord (fset N \<union> fset U) C)"
proof -
  from conflict have "almost_no_conflict_with_trail N \<beta> S1"
    using \<open>almost_no_conflict_with_trail N \<beta> S0\<close>
    by (rule conflict_preserves_almost_no_conflict_with_trail)

  from conflict obtain C1 \<gamma>1 where conflict_S1: "state_conflict S1 = Some (C1, \<gamma>1)"
    by (smt (verit, best) conflict.simps state_conflict_simp)
  with backtrack obtain Cn \<gamma>n where conflict_Sn: "state_conflict Sn = Some (Cn, \<gamma>n)" and "Cn \<noteq> {#}"
    by (auto elim: backtrack.cases)
  with resolution conflict_S1 have "C1 \<noteq> {#}"
  proof (induction Sn arbitrary: C1 \<gamma>1 Cn \<gamma>n rule: tranclp_induct)
    case (base y)
    then show ?case
      by (auto elim: skip.cases factorize.cases resolve.cases)
  next
    case (step y z)
    from step.prems step.hyps obtain Cy \<gamma>y where
      conf_y: "state_conflict y = Some (Cy, \<gamma>y)" and "Cy \<noteq> {#}"
      by (auto elim: skip.cases factorize.cases resolve.cases)
    show ?case
      using step.IH[OF _ conf_y \<open>Cy \<noteq> {#}\<close>] step.prems
      by simp
  qed

  from conflict sound_S0 have sound_S1: "sound_state N \<beta> S1"
    by (simp add: conflict_sound_state)
  with resolution have sound_Sn: "sound_state N \<beta> Sn"
    by (induction rule: tranclp_induct)
      (auto intro: skip_sound_state factorize_sound_state resolve_sound_state)

  from conflict_Sn sound_Sn have "fset N \<TTurnstile>\<G>e {Cn}" and
    trail_Sn_false_Cn_\<gamma>n: "trail_false_cls (state_trail Sn) (Cn \<cdot> \<gamma>n)"
    by (auto simp add: sound_state_def)

  from conflict_S1 sound_S1 have trail_S1_false_C1_\<gamma>1: "trail_false_cls (state_trail S1) (C1 \<cdot> \<gamma>1)"
    by (auto simp add: sound_state_def)

  from resolution have "suffix (state_trail Sn) (state_trail S1) \<and>
    (\<exists>Cn \<gamma>n. state_conflict Sn = Some (Cn, \<gamma>n) \<and> trail_false_cls (state_trail S1) (Cn \<cdot> \<gamma>n))"
  proof (induction Sn rule: tranclp_induct)
    case (base S2)
    thus ?case
    proof (elim sup2E)
      assume "skip N \<beta> S1 S2"
      thus ?thesis
        using conflict_S1 skip.simps suffix_ConsI trail_S1_false_C1_\<gamma>1 by fastforce
    next
      assume "factorize N \<beta> S1 S2"
      moreover with sound_S1 have "sound_state N \<beta> S2"
        by (auto intro: factorize_sound_state)
      ultimately show ?thesis
        by (cases N \<beta> S1 S2 rule: factorize.cases) (simp add: sound_state_def)
    next
      assume "resolve N \<beta> S1 S2"
      moreover with sound_S1 have "sound_state N \<beta> S2"
        by (auto intro: resolve_sound_state)
      ultimately show ?thesis
        by (cases N \<beta> S1 S2 rule: resolve.cases) (simp add: sound_state_def)
    qed
  next
    case (step Sm Sm')
    from step.hyps(2) have "suffix (state_trail Sm') (state_trail Sm)"
      by (auto elim!: skip.cases factorize.cases resolve.cases intro: suffix_ConsI)
    with step.IH have "suffix (state_trail Sm') (state_trail S1)"
      by force

    from step.hyps(1) sound_S1 have sound_Sm: "sound_state N \<beta> Sm"
      by (induction rule: tranclp_induct)
        (auto intro: skip_sound_state factorize_sound_state resolve_sound_state)

    from step.IH obtain Cm \<gamma>m where
      conflict_Sm: "state_conflict Sm = Some (Cm, \<gamma>m)" and
      trail_false_Cm_\<gamma>m: "trail_false_cls (state_trail S1) (Cm \<cdot> \<gamma>m)"
      using step.prems step.hyps(2) \<open>suffix (state_trail Sm') (state_trail Sm)\<close>
        \<open>suffix (state_trail Sm') (state_trail S1)\<close>
      unfolding suffix_def
      by auto

    from step.hyps(2) show ?case
    proof (elim sup2E)
      assume "skip N \<beta> Sm Sm'"
      thus ?thesis
        using \<open>suffix (state_trail Sm') (state_trail S1)\<close>
        using conflict_Sm skip.simps trail_false_Cm_\<gamma>m by auto
    next
      assume "factorize N \<beta> Sm Sm'"
      thus ?thesis
      proof (cases N \<beta> Sm Sm' rule: factorize.cases)
        case (factorizeI L \<gamma> L' \<mu> \<gamma>' D \<Gamma> U)
        with conflict_Sm have Cm_def: "Cm = add_mset L' (add_mset L D)" and \<gamma>m_def: "\<gamma>m = \<gamma>"
          by simp_all
        with factorizeI(3,4) have "trail_false_cls (state_trail S1) ((D + {#L#}) \<cdot> \<mu> \<cdot> \<gamma>)"
          apply -
          apply (rule trail_false_cls_subst_mgu_before_grounding[of _ _ L L'])
          using trail_false_Cm_\<gamma>m apply simp
           apply auto
          by (smt (verit, best) atm_of_subst_lit finite.emptyI finite.insertI insertE is_unifier_alt
              is_unifiers_def singletonD)
        with factorizeI(5) have "trail_false_cls (state_trail S1) ((D + {#L#}) \<cdot> \<mu> \<cdot> \<gamma>')"
          using subst_cls_restrict_subst_domain
          by (metis add_mset_add_single order_refl)
        with factorizeI(2) show ?thesis
          using \<open>suffix (state_trail Sm') (state_trail S1)\<close>
          by (metis add_mset_add_single state_conflict_simp)
      qed
    next
      assume "resolve N \<beta> Sm Sm'"
      thus ?thesis
      proof (cases N \<beta> Sm Sm' rule: resolve.cases)
        case (resolveI \<Gamma> \<Gamma>' L C \<delta> L' \<sigma> \<rho> D \<mu> U)
        have "is_renaming (renaming_wrt (fset (N |\<union>| U |\<union>| clss_of_trail \<Gamma> |\<union>| {|D + {#L'#}|})))"
          apply (rule is_renaming_renaming_wrt)
          using resolveI
          by (smt (verit, best) finite_fset sound_Sm sound_state_def state_learned_simp)
        with resolveI have ren_\<rho>: "is_renaming \<rho>"
          by simp

        from resolveI conflict_Sm have Cm_def: "Cm = D + {#L'#}" and \<gamma>m_def: "\<gamma>m = \<sigma>"
          by simp_all
        hence tr_false_L'_D_\<sigma>: "trail_false_cls (state_trail S1) (add_mset L' D \<cdot> \<sigma>)"
          using trail_false_Cm_\<gamma>m by simp

        from resolveI sound_Sm have
          ground_conf_\<sigma>: "is_ground_cls (add_mset L' D \<cdot> \<sigma>)" and
          dom_\<sigma>: "subst_domain \<sigma> \<subseteq> vars_cls (add_mset L' D)" and
          "sound_trail N \<Gamma>" and
          "minimal_ground_closures Sm"
          unfolding sound_state_def by (simp_all add: minimal_ground_closures_def)

        have "atm_of L \<cdot>a rename_subst_domain \<rho> \<sigma> \<cdot>a \<delta> =
          atm_of L' \<cdot>a \<rho> \<cdot>a rename_subst_domain \<rho> \<sigma> \<cdot>a \<delta>"
        proof -
          from ren_\<rho> have "\<forall>x. is_Var (\<rho> x)" and "inj \<rho>"
            by (simp_all add: is_renaming_iff)

          have "atm_of L \<cdot>a rename_subst_domain \<rho> \<sigma> = atm_of L"
          proof (rule subst_apply_term_ident)
            have "subst_domain (rename_subst_domain \<rho> \<sigma>) \<subseteq> the_Var ` \<rho> ` subst_domain \<sigma>"
              using subst_domain_rename_subst_domain_subset[OF \<open>\<forall>x. is_Var (\<rho> x)\<close>] by simp
            also have "\<dots> \<subseteq> the_Var ` \<rho> ` vars_cls (add_mset L' D)"
              using dom_\<sigma> by auto
            also have "\<dots> = (\<Union>x \<in> vars_cls (add_mset L' D). vars_term (\<rho> x))"
              using image_the_Var_image_subst_renaming_eq[OF \<open>\<forall>x. is_Var (\<rho> x)\<close>] by simp
            also have "\<dots> = vars_cls (add_mset L' D \<cdot> \<rho>)"
              using vars_subst_cls_eq by metis
            finally show "vars_lit L \<inter> subst_domain (rename_subst_domain \<rho> \<sigma>) = {}"
              using \<open>vars_cls (add_mset L' D \<cdot> \<rho>) \<inter> vars_cls (add_mset L C) = {}\<close>
              by auto
          qed
          moreover have "atm_of L' \<cdot>a \<rho> \<cdot>a rename_subst_domain \<rho> \<sigma> = atm_of L' \<cdot>a \<sigma>"
            using vars_cls_subset_subst_domain_if_grounding[OF ground_conf_\<sigma>]
            by (simp add: renaming_cancels_rename_subst_domain[OF \<open>\<forall>x. is_Var (\<rho> x)\<close> \<open>inj \<rho>\<close>])
          moreover have "atm_of L' \<cdot>a \<sigma> \<cdot>a \<delta> = atm_of L' \<cdot>a \<sigma>"
          proof (rule subst_apply_term_ident)
            show "vars_term (atm_of L' \<cdot>a \<sigma>) \<inter> subst_domain \<delta> = {}"
              using ground_conf_\<sigma>[unfolded is_ground_cls_iff_vars_empty]
              by simp
          qed
          ultimately show ?thesis
            using \<open>L \<cdot>l \<delta> = - (L' \<cdot>l \<sigma>)\<close>
            by (metis atm_of_subst_lit atm_of_uminus)
        qed
        hence "is_unifier (rename_subst_domain \<rho> \<sigma> \<odot> \<delta>) {atm_of L, atm_of L' \<cdot>a \<rho>}"
          by (simp add: is_unifier_alt)
        hence "\<mu> \<odot> (rename_subst_domain \<rho> \<sigma> \<odot> \<delta>) = rename_subst_domain \<rho> \<sigma> \<odot> \<delta>"
          using \<open>is_mimgu \<mu> {{atm_of L, atm_of L' \<cdot>a \<rho>}}\<close>
          by (auto simp add: is_mimgu_def is_imgu_def is_unifiers_def)

        have "trail_false_cls (state_trail S1) ((D \<cdot> \<rho> + C) \<cdot> rename_subst_domain \<rho> \<sigma> \<cdot> \<delta>)"
        proof (rule trail_false_plusI)
          show "trail_false_cls \<Gamma>' (C \<cdot> \<delta>)" 
            using resolveI \<open>sound_trail N \<Gamma>\<close>
            by (auto simp: trail_propagate_def elim: sound_trail.cases)
        next
          show "trail_false_cls (state_trail S1) (add_mset L' D \<cdot> \<sigma>)"
            using tr_false_L'_D_\<sigma> .
        next
          show "suffix \<Gamma>' (state_trail S1)"
            using resolveI \<open>suffix (state_trail Sm') (state_trail S1)\<close>
            by (metis (no_types, lifting) state_trail_simp suffix_order.trans
                suffix_trail_propagate)
        next
          show "subst_domain \<sigma> \<subseteq> vars_cls (add_mset L' D)"
            using dom_\<sigma> .
        next
          show "is_ground_cls (add_mset L' D \<cdot> \<sigma>)"
            using ground_conf_\<sigma> .
        next
          show "is_renaming \<rho>"
            using ren_\<rho> .
        next
          show "vars_cls (add_mset L' D \<cdot> \<rho>) \<inter> vars_cls C = {}"
            using resolveI by auto
        qed
        hence "trail_false_cls (state_trail S1) ((D \<cdot> \<rho> + C) \<cdot> \<mu> \<cdot> (rename_subst_domain \<rho> \<sigma> \<odot> \<delta>))"
          using \<open>\<mu> \<odot> (rename_subst_domain \<rho> \<sigma> \<odot> \<delta>) = rename_subst_domain \<rho> \<sigma> \<odot> \<delta>\<close>
          by (metis subst_cls_comp_subst)
        hence "trail_false_cls (state_trail S1) ((D \<cdot> \<rho> + C) \<cdot> \<mu> \<cdot>
          restrict_subst_domain (vars_cls ((D \<cdot> \<rho> + C) \<cdot> \<mu>)) (rename_subst_domain \<rho> \<sigma> \<odot> \<delta>))"
          by (simp add: subst_cls_restrict_subst_domain)
        then show ?thesis
          using \<open>suffix (state_trail Sm') (state_trail S1)\<close>
          using resolveI(1,2) by simp
      qed
    qed
  qed

  with conflict_Sn have
    "suffix (state_trail Sn) (state_trail S1)" and
    tr_false_S1_Cn_\<gamma>n: "trail_false_cls (state_trail S1) (Cn \<cdot> \<gamma>n)"
    by auto

  from sound_Sn conflict_Sn have Cn_\<gamma>n_in: "Cn \<cdot> \<gamma>n \<in> grounding_of_cls Cn"
    unfolding sound_state_def minimal_ground_closures_def
    using grounding_of_cls_ground grounding_of_subst_cls_subset
    by fastforce

  from sound_S1 have sound_trail_S1: "sound_trail N (state_trail S1)"
    by (auto simp add: sound_state_def)
  
  have tr_consistent_S1: "trail_consistent (state_trail S1)"
    using conflict_preserves_trail_lits_consistent[OF conflict \<open>trail_lits_consistent S0\<close>]
    by (simp add: trail_lits_consistent_def)

  have "\<forall>L\<in>#Cn \<cdot> \<gamma>n. trail_defined_lit (state_trail S1) L"
    using tr_false_S1_Cn_\<gamma>n trail_defined_lit_iff_true_or_false trail_false_cls_def by blast
  hence "trail_interp (state_trail S1) \<TTurnstile> Cn \<cdot> \<gamma>n \<longleftrightarrow> trail_true_cls (state_trail S1) (Cn \<cdot> \<gamma>n)"
    using tr_consistent_S1 trail_true_cls_iff_trail_interp_entails by auto
  hence not_trail_S1_entails_Cn_\<gamma>n: "\<not> trail_interp (state_trail S1) \<TTurnstile>s {Cn \<cdot> \<gamma>n}"
    using tr_false_S1_Cn_\<gamma>n not_trail_true_and_false_cls[OF tr_consistent_S1] by auto

  have "trail_defined_cls (state_trail S1) (Cn \<cdot> \<gamma>n)"
    using \<open>\<forall>L\<in>#Cn \<cdot> \<gamma>n. trail_defined_lit (state_trail S1) L\<close> trail_defined_cls_def by blast

  have "{#} |\<notin>| N"
    by (rule mempty_not_in_initial_clauses_if_non_empty_regular_conflict[OF conflict_S1 \<open>C1 \<noteq> {#}\<close>
          \<open>almost_no_conflict_with_trail N \<beta> S1\<close> sound_S1])
  then obtain S where "propagate N \<beta> S S0"
    using before_reasonable_conflict[OF conflict \<open>learned_nonempty S0\<close>
        \<open>trail_propagated_or_decided' N \<beta> S0\<close> \<open>no_conflict_after_decide' N \<beta> S0\<close>]
    by auto

  have "state_learned S = state_learned S0"
    using \<open>propagate N \<beta> S S0\<close> by (auto simp add: propagate.simps)
  also from conflict have "... = state_learned S1"
    by (auto simp add: conflict.simps)
  finally have "state_learned S = state_learned S1"
    by assumption

  have "state_conflict S = None"
    using \<open>propagate N \<beta> S S0\<close> by (auto simp add: propagate.simps)

  from conflict have "state_trail S1 = state_trail S0"
    by (smt (verit) conflict.cases state_trail_simp)

  obtain L C \<gamma> where trail_S0_eq: "state_trail S0 = trail_propagate (state_trail S) L C \<gamma>"
    using \<open>propagate N \<beta> S S0\<close> unfolding propagate.simps by auto

  with backtrack have "strict_suffix (state_trail Sn) (state_trail S0)"
    using conflict_with_literal_gets_resolved[OF _ conflict resolution[THEN tranclp_into_rtranclp] _
        \<open>{#} |\<notin>| N\<close> \<open>learned_nonempty S0\<close> \<open>trail_propagated_or_decided' N \<beta> S0\<close>
        \<open>no_conflict_after_decide' N \<beta> S0\<close>]
    by (metis (no_types, lifting) trail_propagate_def)
  hence "suffix (state_trail Sn) (state_trail S)"
    unfolding trail_S0_eq trail_propagate_def
    by (metis suffix_Cons suffix_order.le_less suffix_order.less_irrefl)

  moreover have "\<not> trail_defined_lit (state_trail S) (L \<cdot>l \<gamma>)"
  proof -
    have  "trail_consistent (state_trail S0)"
      using \<open>state_trail S1 = state_trail S0\<close> \<open>trail_consistent (state_trail S1)\<close> by simp
    thus ?thesis
      by (smt (verit, best) Pair_inject list.distinct(1) list.inject trail_S0_eq
          trail_consistent.cases trail_propagate_def)
  qed

  ultimately have "\<not> trail_defined_lit (state_trail Sn) (L \<cdot>l \<gamma>)"
    by (metis trail_defined_lit_def trail_false_lit_def trail_false_lit_if_trail_false_suffix
        uminus_of_uminus_id)

  moreover have "trail_false_cls (state_trail Sn) (Cn \<cdot> \<gamma>n)"
    using sound_Sn conflict_Sn by (auto simp add: sound_state_def)

  ultimately have "L \<cdot>l \<gamma> \<notin># Cn \<cdot> \<gamma>n \<and> - (L \<cdot>l \<gamma>) \<notin># Cn \<cdot> \<gamma>n"
    unfolding trail_false_cls_def trail_false_lit_def trail_defined_lit_def
    by (metis uminus_of_uminus_id)

  have no_conf_at_S: "\<nexists>S'. conflict N \<beta> S S'"
  proof (rule nex_conflict_if_no_conflict_with_trail'')
    show "state_conflict S = None"
      using \<open>propagate N \<beta> S S0\<close> by (auto elim: propagate.cases)
  next
    show "{#} |\<notin>| N"
      by (rule \<open>{#} |\<notin>| N\<close>)
  next
    show "learned_nonempty S"
      using \<open>learned_nonempty S0\<close> \<open>state_learned S = state_learned S0\<close>
      by (simp add: learned_nonempty_def)
  next
    show "no_conflict_with_trail N \<beta> (state_learned S) (state_trail S)"
      using \<open>almost_no_conflict_with_trail N \<beta> S0\<close>
      using \<open>propagate N \<beta> S S0\<close>
      by (auto simp: almost_no_conflict_with_trail_def \<open>state_learned S = state_learned S0\<close>
          trail_propagate_def is_decision_lit_def elim!: propagate.cases)
  qed

  have conf_at_S_if: "\<exists>S'. conflict N \<beta> S S'"
    if D_in: "D \<in> grounding_of_clss (fset N \<union> fset U)" and
      tr_false_D: "trail_false_cls (state_trail S) D"
    for D
    using ex_conflict_if_trail_false_cls[OF tr_false_D D_in]
    unfolding U_def \<open>state_learned S = state_learned S1\<close>[symmetric]
      \<open>state_conflict S = None\<close>[symmetric]
    by simp

  have not_gr_red_Cn_\<gamma>n:
    "\<not> ground_redundant trail_ord (grounding_of_clss (fset N \<union> fset U)) (Cn \<cdot> \<gamma>n)"
  proof (rule notI)
    define gnds_le_Cn_\<gamma>n where
      "gnds_le_Cn_\<gamma>n = {D \<in> grounding_of_clss (fset N \<union> fset U). trail_ord\<^sup>=\<^sup>= D (Cn \<cdot> \<gamma>n)}"

    assume "ground_redundant trail_ord (grounding_of_clss (fset N \<union> fset U)) (Cn \<cdot> \<gamma>n)"
    hence "gnds_le_Cn_\<gamma>n \<TTurnstile>e {Cn \<cdot> \<gamma>n}"
      unfolding ground_redundant_def gnds_le_Cn_\<gamma>n_def by simp
    hence "\<not> trail_interp (state_trail S1) \<TTurnstile>s gnds_le_Cn_\<gamma>n"
      using not_trail_S1_entails_Cn_\<gamma>n by auto
    then obtain D where D_in: "D \<in> gnds_le_Cn_\<gamma>n" and "\<not> trail_interp (state_trail S1) \<TTurnstile> D"
      by (auto simp: true_clss_def)

    from D_in have
      D_in: "D \<in> grounding_of_clss (fset N \<union> fset U)" and
      D_le_Cn_\<gamma>n: "trail_ord\<^sup>=\<^sup>= D (Cn \<cdot> \<gamma>n)"
      unfolding gnds_le_Cn_\<gamma>n_def by simp_all

    from D_le_Cn_\<gamma>n have "trail_defined_cls (state_trail S1) D"
      unfolding Lattices.sup_apply Boolean_Algebras.sup_bool_def
    proof (elim disjE)
      assume multp_D_Cn_\<gamma>n: "trail_ord D (Cn \<cdot> \<gamma>n)"
      show "trail_defined_cls (state_trail S1) D"
        using tr_consistent_S1 multp_D_Cn_\<gamma>n
          \<open>trail_defined_cls (state_trail S1) (Cn \<cdot> \<gamma>n)\<close> \<open>transp lt\<close>
        by (auto simp add: trail_ord_def intro: trail_defined_cls_if_lt_defined)
    next
      assume "D = Cn \<cdot> \<gamma>n"
      then show "trail_defined_cls (state_trail S1) D"
        using \<open>trail_defined_cls (state_trail S1) (Cn \<cdot> \<gamma>n)\<close> by simp
    qed
    hence "trail_false_cls (state_trail S1) D"
      using \<open>\<not> trail_interp (state_trail S1) \<TTurnstile> D\<close>
      using \<open>trail_consistent (state_trail S1)\<close> trail_interp_cls_if_trail_true
        trail_true_or_false_cls_if_defined by blast

    from D_le_Cn_\<gamma>n have "L \<cdot>l \<gamma> \<notin># D \<and> - (L \<cdot>l \<gamma>) \<notin># D"
    proof (rule sup2E)
      show "D = Cn \<cdot> \<gamma>n \<Longrightarrow> ?thesis"
        using \<open>L \<cdot>l \<gamma> \<notin># Cn \<cdot> \<gamma>n \<and> - (L \<cdot>l \<gamma>) \<notin># Cn \<cdot> \<gamma>n\<close> by argo
    next
      assume "trail_ord D (Cn \<cdot> \<gamma>n)"
      hence D_lt_Cn_\<gamma>n': "multp (trail_less (map fst (state_trail S1))) D (Cn \<cdot> \<gamma>n)"
        unfolding trail_ord_def
      proof (rule multp_mono_strong)
        from \<open>transp lt\<close> show "transp (trail_less_ex lt (map fst (state_trail S1)))"
          by (rule transp_trail_less_ex_if_trail_consistant[OF tr_consistent_S1])
      next
        show "\<And>x y. x \<in># D \<Longrightarrow> y \<in># Cn \<cdot> \<gamma>n \<Longrightarrow> trail_less_ex lt (map fst (state_trail S1)) x y \<Longrightarrow>
           trail_less (map fst (state_trail S1)) x y"
          using \<open>\<forall>L\<in>#Cn \<cdot> \<gamma>n. trail_defined_lit (state_trail S1) L\<close>
          by (metis (no_types, opaque_lifting) image_set trail_defined_lit_def trail_less_ex_def)
      qed

      have "\<forall>K\<in>#Cn \<cdot> \<gamma>n. - K \<in> fst ` set (state_trail S1)"
        by (rule \<open>trail_false_cls (state_trail S1) (Cn \<cdot> \<gamma>n)\<close>[unfolded trail_false_cls_def
              trail_false_lit_def])
      hence "\<forall>K\<in>#Cn \<cdot> \<gamma>n. - K \<in> insert (L \<cdot>l \<gamma>) (fst ` set (state_trail S))"
        unfolding \<open>state_trail S1 = state_trail S0\<close>
          \<open>state_trail S0 = trail_propagate (state_trail S) L C \<gamma>\<close>
          trail_propagate_def list.set image_insert prod.sel
        by simp
      hence *: "\<forall>K\<in>#Cn \<cdot> \<gamma>n. - K \<in> fst ` set (state_trail S)"
        by (metis \<open>L \<cdot>l \<gamma> \<notin># Cn \<cdot> \<gamma>n \<and> - (L \<cdot>l \<gamma>) \<notin># Cn \<cdot> \<gamma>n\<close> insert_iff uminus_lit_swap)
      have **: "\<forall>K \<in># Cn \<cdot> \<gamma>n. trail_less (map fst (state_trail S1)) K (L \<cdot>l \<gamma>)"
        unfolding \<open>state_trail S1 = state_trail S0\<close>
          \<open>state_trail S0 = trail_propagate (state_trail S) L C \<gamma>\<close>
          trail_propagate_def prod.sel list.map
      proof (rule ballI)
        fix K assume "K \<in># Cn \<cdot> \<gamma>n"
        have "trail_less_comp_id (L \<cdot>l \<gamma> # map fst (state_trail S)) K (L \<cdot>l \<gamma>)"
          unfolding trail_less_comp_id_def
          using *[rule_format, OF \<open>K \<in># Cn \<cdot> \<gamma>n\<close>]
          by (smt (verit, best) image_set in_set_conv_nth length_Cons less_Suc_eq_0_disj nth_Cons'
              nth_Cons_Suc uminus_lit_swap)
        thus "trail_less (L \<cdot>l \<gamma> # map fst (state_trail S)) K (L \<cdot>l \<gamma>)"
          by (simp add: trail_less_def)
      qed
      
      moreover have "trail_less (map fst (state_trail S1)) (L \<cdot>l \<gamma>) (- (L \<cdot>l \<gamma>))"
        unfolding \<open>state_trail S1 = state_trail S0\<close>
          \<open>state_trail S0 = trail_propagate (state_trail S) L C \<gamma>\<close>
          trail_propagate_def list.map prod.sel
        by (rule trail_less_comp_rightI) simp

      ultimately have ***: "\<forall>K \<in># Cn \<cdot> \<gamma>n. trail_less (map fst (state_trail S1)) K (- (L \<cdot>l \<gamma>))"
        using transp_trail_less_if_trail_consistant[OF tr_consistent_S1, THEN transpD] by blast

      have "\<not> (L \<cdot>l \<gamma> \<in># D \<or> - (L \<cdot>l \<gamma>) \<in># D)"
      proof (rule notI)
        obtain I J K where
          "Cn \<cdot> \<gamma>n = I + J" and D_def: "D = I + K" and "J \<noteq> {#}" and
          "\<forall>k\<in>#K. \<exists>x\<in>#J. trail_less (map fst (state_trail S1)) k x"
          using multp_implies_one_step[OF transp_trail_less_if_trail_consistant[OF tr_consistent_S1]
              D_lt_Cn_\<gamma>n']
          by auto
        assume "L \<cdot>l \<gamma> \<in># D \<or> - (L \<cdot>l \<gamma>) \<in># D"
        then show False
          unfolding D_def Multiset.union_iff
        proof (elim disjE)
          show "L \<cdot>l \<gamma> \<in># I \<Longrightarrow> False"
            using \<open>L \<cdot>l \<gamma> \<notin># Cn \<cdot> \<gamma>n \<and> - (L \<cdot>l \<gamma>) \<notin># Cn \<cdot> \<gamma>n\<close> \<open>Cn \<cdot> \<gamma>n = I + J\<close> by simp
        next
          show "- (L \<cdot>l \<gamma>) \<in># I \<Longrightarrow> False"
            using \<open>L \<cdot>l \<gamma> \<notin># Cn \<cdot> \<gamma>n \<and> - (L \<cdot>l \<gamma>) \<notin># Cn \<cdot> \<gamma>n\<close> \<open>Cn \<cdot> \<gamma>n = I + J\<close> by simp
        next
          show "L \<cdot>l \<gamma> \<in># K \<Longrightarrow> False"
            using \<open>L \<cdot>l \<gamma> \<notin># Cn \<cdot> \<gamma>n \<and> - (L \<cdot>l \<gamma>) \<notin># Cn \<cdot> \<gamma>n\<close>[THEN conjunct1]
              **[unfolded \<open>Cn \<cdot> \<gamma>n = I + J\<close>] \<open>\<forall>k\<in>#K. \<exists>x\<in>#J. trail_less (map fst (state_trail S1)) k x\<close>
            by (metis (no_types, lifting) D_def Un_insert_right
                \<open>\<not> trail_interp (state_trail S1) \<TTurnstile> D\<close>
                \<open>state_trail S0 = trail_propagate (state_trail S) L C \<gamma>\<close>
                \<open>state_trail S1 = state_trail S0\<close> \<open>trail_consistent (state_trail S1)\<close> image_insert
                insert_iff list.set(2) mk_disjoint_insert prod.sel(1) set_mset_union
                trail_interp_cls_if_trail_true trail_propagate_def trail_true_cls_def
                trail_true_lit_def)
        next
          assume "- (L \<cdot>l \<gamma>) \<in># K"
          then obtain j where
            j_in: "j \<in># J" and
            uminus_L_\<gamma>_lt_j: "trail_less (map fst (state_trail S1)) (- (L \<cdot>l \<gamma>)) j"
            using \<open>\<forall>k\<in>#K. \<exists>x\<in>#J. trail_less (map fst (state_trail S1)) k x\<close> by auto

          from j_in have
            "trail_less (map fst (state_trail S1)) j (- (L \<cdot>l \<gamma>))"
            using *** by (auto simp: \<open>Cn \<cdot> \<gamma>n = I + J\<close>)
          with uminus_L_\<gamma>_lt_j show "False"
            using asymp_trail_less_if_trail_consistant[OF tr_consistent_S1, THEN asympD]
            by blast
        qed
      qed
      thus ?thesis by simp
    qed
    hence "trail_false_cls (state_trail S) D"
      using D_in \<open>trail_false_cls (state_trail S1) D\<close>
      unfolding \<open>state_trail S1 = state_trail S0\<close>
        \<open>state_trail S0 = trail_propagate (state_trail S) L C \<gamma>\<close>
      by (simp add: trail_propagate_def subtrail_falseI)
    thus False
      using no_conf_at_S conf_at_S_if[OF D_in] by metis
  qed
  hence "\<not> redundant trail_ord (fset N \<union> fset U) Cn"
    unfolding redundant_def
    using Cn_\<gamma>n_in by auto

  moreover have "Cn \<cdot> \<gamma>n \<notin> grounding_of_clss (fset N \<union> fset U)"
  proof -
    have "is_ground_cls (Cn \<cdot> \<gamma>n)"
      using Cn_\<gamma>n_in is_ground_cls_if_in_grounding_of_cls by blast

    moreover have "is_ground_clss (grounding_of_clss (fset N \<union> fset U))"
      by simp

    ultimately have "\<not> ({D \<in> grounding_of_clss (fset N \<union> fset U). trail_ord\<^sup>=\<^sup>= D (Cn \<cdot> \<gamma>n)} \<TTurnstile>e {Cn \<cdot> \<gamma>n})"
      using not_gr_red_Cn_\<gamma>n
      by (simp add: ground_redundant_def)
    thus ?thesis
      by (auto simp add: true_clss_def)
  qed

  moreover have "set_mset (Cn \<cdot> \<gamma>n) \<notin> set_mset ` grounding_of_clss (fset N \<union> fset U)"
  proof (rule notI)
    assume "set_mset (Cn \<cdot> \<gamma>n) \<in> set_mset ` grounding_of_clss (fset N \<union> fset U)"
    then obtain D where
      D_in: "D \<in> grounding_of_clss (fset N \<union> fset U)" and
      set_mset_eq_D_Cn_\<gamma>n: "set_mset D = set_mset (Cn \<cdot> \<gamma>n)"
      by (auto simp add: image_iff)

    have "\<not> trail_interp (state_trail S1) \<TTurnstile> D"
      unfolding true_cls_iff_set_mset_eq[OF set_mset_eq_D_Cn_\<gamma>n]
      using not_trail_S1_entails_Cn_\<gamma>n
      by simp

    have "trail_defined_cls (state_trail S1) D"
      using \<open>\<forall>L\<in>#Cn \<cdot> \<gamma>n. trail_defined_lit (state_trail S1) L\<close>
      unfolding set_mset_eq_D_Cn_\<gamma>n[symmetric]
      by (simp add: trail_defined_cls_def)
    hence "trail_false_cls (state_trail S1) D"
      using \<open>\<not> trail_interp (state_trail S1) \<TTurnstile> D\<close>
      using tr_consistent_S1 trail_interp_cls_if_trail_true trail_true_or_false_cls_if_defined
      by blast

    have "L \<cdot>l \<gamma> \<notin># D \<and> - (L \<cdot>l \<gamma>) \<notin># D"
      using \<open>L \<cdot>l \<gamma> \<notin># Cn \<cdot> \<gamma>n \<and> - (L \<cdot>l \<gamma>) \<notin># Cn \<cdot> \<gamma>n\<close>
      unfolding set_mset_eq_D_Cn_\<gamma>n[symmetric]
      by assumption
    hence "trail_false_cls (state_trail S) D"
      using D_in \<open>trail_false_cls (state_trail S1) D\<close>
      unfolding \<open>state_trail S1 = state_trail S0\<close>
        \<open>state_trail S0 = trail_propagate (state_trail S) L C \<gamma>\<close>
      by (simp add: trail_propagate_def subtrail_falseI)
    thus False
      using no_conf_at_S conf_at_S_if[OF D_in] by metis
  qed

  ultimately show ?thesis
    using conflict_Sn by simp
qed

theorem learned_clauses_in_regular_runs:
  assumes
    regular_run: "(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S0" and
    conflict: "conflict N \<beta> S0 S1" and
    resolution: "(skip N \<beta> \<squnion> factorize N \<beta> \<squnion> resolve N \<beta>)\<^sup>+\<^sup>+ S1 Sn" and
    backtrack: "backtrack N \<beta> Sn Sn'" and
    "transp lt"
  defines
    "trail_ord \<equiv> multp (trail_less_ex lt (map fst (state_trail S1)))" and
    "U \<equiv> state_learned S1"
  shows "(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state Sn' \<and>
    (\<exists>C \<gamma>. state_conflict Sn = Some (C, \<gamma>) \<and>
      C \<cdot> \<gamma> \<notin> grounding_of_clss (fset N \<union> fset U) \<and>
      set_mset (C \<cdot> \<gamma>) \<notin> set_mset ` grounding_of_clss (fset N \<union> fset U) \<and>
      \<not> redundant trail_ord (fset N \<union> fset U) C)"
proof -
  have "sound_state N \<beta> initial_state"
    by (rule sound_initial_state)
  with regular_run have sound_S0: "sound_state N \<beta> S0"
    by (rule regular_run_sound_state)

  from regular_run have "learned_nonempty S0"
    by (induction S0 rule: rtranclp_induct)
      (auto intro: scl_preserves_learned_nonempty reasonable_if_regular scl_if_reasonable)

  from regular_run have "trail_propagated_or_decided' N \<beta> S0"
    by (induction S0 rule: rtranclp_induct)
      (auto intro: scl_preserves_trail_propagated_or_decided
        reasonable_if_regular scl_if_reasonable)

  from regular_run have "no_conflict_after_decide' N \<beta> S0"
    by (induction S0 rule: rtranclp_induct)
      (auto intro: reasonable_scl_preserves_no_conflict_after_decide' reasonable_if_regular)

  from regular_run have "almost_no_conflict_with_trail N \<beta> S0"
    by (induction S0 rule: rtranclp_induct)
     (simp_all add: regular_scl_preserves_almost_no_conflict_with_trail)

  from regular_run have "trail_lits_consistent S0"
    by (induction S0 rule: rtranclp_induct)
      (auto intro: scl_preserves_trail_lits_consistent reasonable_if_regular scl_if_reasonable)

  from regular_run conflict have "(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S1"
    by (meson regular_scl_def rtranclp.simps)
  also from resolution have reg_run_S1_Sn: "(regular_scl N \<beta>)\<^sup>*\<^sup>* ... Sn"
    using regular_run_if_skip_factorize_resolve_run tranclp_into_rtranclp by metis
  also have "(regular_scl N \<beta>)\<^sup>*\<^sup>* ... Sn'"
  proof (rule r_into_rtranclp)
    from backtrack have "scl N \<beta> Sn Sn'"
      by (simp add: scl_def)
    with backtrack have "reasonable_scl N \<beta> Sn Sn'"
      using reasonable_scl_def decide_well_defined(6) by blast
    with backtrack show "regular_scl N \<beta> Sn Sn'"
      unfolding regular_scl_def
      by (smt (verit) conflict.simps option.simps(3) backtrack.cases state_conflict_simp)
  qed
  finally have "(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state Sn'" by assumption
  thus ?thesis
    using learned_clauses_in_regular_runs_invars[OF sound_S0 \<open>learned_nonempty S0\<close>
        \<open>trail_propagated_or_decided' N \<beta> S0\<close>
        \<open>no_conflict_after_decide' N \<beta> S0\<close> \<open>almost_no_conflict_with_trail N \<beta> S0\<close>
        \<open>trail_lits_consistent S0\<close>
        conflict resolution backtrack \<open>transp lt\<close>, folded trail_ord_def U_def]
    by argo
qed

corollary learned_clauses_in_regular_runs_static_order:
  assumes
    regular_run: "(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S0" and
    conflict: "conflict N \<beta> S0 S1" and
    resolution: "(skip N \<beta> \<squnion> factorize N \<beta> \<squnion> resolve N \<beta>)\<^sup>+\<^sup>+ S1 Sn" and
    backtrack: "backtrack N \<beta> Sn Sn'" and
    "transp lt"
  defines
    "trail_ord \<equiv> multp (trail_less_ex lt (map fst (state_trail S1)))" and
    "U \<equiv> state_learned S1"
  shows "(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state Sn' \<and>
    (\<exists>C \<gamma>. state_conflict Sn = Some (C, \<gamma>) \<and> \<not> redundant (\<subset>#) (fset N \<union> fset U) C)"
  using learned_clauses_in_regular_runs[OF assms(1-5)]
  using U_def redundant_multp_if_redundant_strict_subset by blast

end

end