theory Alternative_Backtracking_Function
  imports Simple_Clause_Learning
begin

primrec bt where
  "bt [] n = ([], 0)" |
  "bt (Ln # \<Gamma>) n =
    (let (\<Gamma>', n') = bt \<Gamma> n in
     if \<Gamma> = \<Gamma>' then
       (\<Gamma>', n')
     
     if is_decision_lit Ln then
       if n' < n then
         (Ln # \<Gamma>', Suc n')
       else
         (\<Gamma>', n')
     else if n' \<le> n then
       (Ln # \<Gamma>', n')
     else
       (\<Gamma>', n'))"

value [simp] "bt [(w, Some ({#}, w, Var)), (z, None), (y, Some ({#}, y, Var)), (x, None)] 0"

lemma bt_level_inv: "bt \<Gamma> level = (\<Gamma>', level') \<Longrightarrow> trail_level \<Gamma>' = level'"
proof (induction \<Gamma> arbitrary: \<Gamma>' level')
  case Nil
  then show ?case by simp
next
  case (Cons Ln \<Gamma>)
  obtain \<Gamma>'' level'' where "bt \<Gamma> level = (\<Gamma>'', level'')"
    by fastforce
  with Cons.prems show ?case
    apply simp
    by (smt (verit, best) Cons.IH Pair_inject id_apply trail_level.simps(2))
qed

abbreviation trail_backtrack where
  "trail_backtrack \<Gamma> level \<equiv> fst (bt \<Gamma> level)"

lemma trail_level_trail_backtrack_le[simp]: "trail_level (trail_backtrack \<Gamma> level) \<le> level"
proof (induction \<Gamma>)
  case Nil
  show ?case
    by simp
next
  case (Cons Ln \<Gamma>)
  thus ?case
    by (smt (verit) Pair_inject Suc_le_eq bt.simps(2) bt_level_inv prod.case_eq_if prod.collapse)
qed

lemma trail_backtrack_ident: "trail_level \<Gamma> < level \<Longrightarrow> trail_backtrack \<Gamma> level = \<Gamma>"
proof (induction \<Gamma>)
  case Nil
  show ?case by simp
next
  case (Cons Ln \<Gamma>)
  then show ?case
    apply simp
    by (smt (verit, del_insts) Pair_inject Suc_le_lessD bt_level_inv case_prod_conv id_apply
        le_eq_less_or_eq prod.collapse)
qed

lemma trail_backtrack_identD: "trail_backtrack \<Gamma> level = \<Gamma> \<Longrightarrow> trail_level \<Gamma> \<le> level"
  apply (induction \<Gamma>)
   apply simp
  apply simp
  apply auto
   apply (smt (verit, ccfv_SIG) bt_level_inv case_prod_conv fst_conv less_Suc_eq_le not_less_eq
      prod.collapse trail_level.simps(2) trail_level_trail_backtrack_le)
  by (smt (verit, del_insts) bt_level_inv fst_conv list.inject prod.collapse split_beta
      trail_level_trail_backtrack_le)

lemma bt_level_inv2: "bt \<Gamma> level = (\<Gamma>', level') \<Longrightarrow> if level < level' then \<Gamma> = \<Gamma>' else suffix \<Gamma>' \<Gamma>"
proof (induction \<Gamma> arbitrary: \<Gamma>' level')
  case Nil
  thus ?case by simp
next
  case (Cons Ln \<Gamma>)
  obtain \<Gamma>'' level'' where "bt \<Gamma> level = (\<Gamma>'', level'')"
    by fastforce

  hence "level'' \<le> level"
    using trail_level_trail_backtrack_le[of \<Gamma> level] bt_level_inv[of \<Gamma> level] by auto

  with Cons.prems show ?case
    apply (simp add: \<open>bt \<Gamma> level = (\<Gamma>'', level'')\<close>)
    apply (cases "is_decision_lit Ln"; simp)
    using Cons.IH[OF \<open>bt \<Gamma> level = (\<Gamma>'', level'')\<close>]
     apply (cases "level = level''"; simp)
      apply (simp add: suffix_Cons)
    unfolding suffix_def
     defer
    apply simp

    
    using trail_level_trail_backtrack_le[of \<Gamma> level]
    using bt_level_inv[OF \<open>bt \<Gamma> level = (\<Gamma>'', level'')\<close>]
    apply simp
    apply (cases "is_decision_lit Ln"; simp)
    subgoal apply (cases "level = level''"; simp) sorry
    subgoal
      apply simp
    
    
    sorry
qed

lemma trail_backtrack_suffix: "suffix (trail_backtrack \<Gamma> level) \<Gamma>"
proof (induction \<Gamma>)
  case Nil
  show ?case by simp
next
  case (Cons Ln \<Gamma>)
  obtain \<Gamma>'' level'' where "bt \<Gamma> level = (\<Gamma>'', level'')"
    by fastforce
  with Cons show ?case
    apply (cases "is_decision_lit Ln")
     apply (simp_all add: suffix_ConsI)
    unfolding suffix_def
qed
  oops

lemma (in scl)
  assumes sound_\<Gamma>: "sound_trail N U \<Gamma>"
  shows "level < trail_level_lit \<Gamma> L \<Longrightarrow> \<not> trail_defined_lit (fst (bt \<Gamma> level)) L"
  using sound_\<Gamma>
proof (induction \<Gamma> rule: sound_trail.induct)
  case Nil
  then show ?case by simp
next
  case (Cons \<Gamma> K u)
  obtain \<Gamma>' m where "bt \<Gamma> level = (\<Gamma>', m)" by force
  with Cons.hyps(1) Cons.prems show ?case
    apply simp
    apply (rule conjI)
    oops

end