theory Non_Redundancy
  imports
    Simple_Clause_Learning
    Trail_Induced_Ordering
begin

context scl begin

section \<open>Resolve in Regular Runs\<close>

lemma before_regular_conflict:
  assumes
    fin: "finite N" and
    reg_run: "(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S1" and
    conf: "conflict N \<beta> S1 S2"
  shows "S1 = initial_state \<and> {#} \<in> N \<or>
    (\<exists>S0. (regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S0 \<and> regular_scl N \<beta> S0 S1 \<and>
    (propagate N \<beta> S0 S1))"
  (is "?lhs \<or> ?rhs")
  using reg_run conf
proof (induction rule: rtranclp_induct)
  case base
  hence "{#} \<in> N"
    by (smt (verit, ccfv_threshold) fin finite_UnI finite_clss_of_trail is_ground_cls_rename_clause
        not_trail_false_Nil(2) rename_clause_ident_if_ground conflict.simps state_learned_simp
        state_trail_simp subst_cls_empty_iff sup_bot.right_neutral)
  thus ?case
    by simp
next
  case (step S0 S1)
  show ?case
  proof (rule disjI2, intro exI conjI)
    show "(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S0"
      using step.hyps by simp
  next
    show "regular_scl N \<beta> S0 S1"
      using step.hyps by simp
  next
    from step.prems obtain \<Gamma> U C \<gamma> where
      S1_def: "S1 = (\<Gamma>, U, None)" and
      S2_def: "S2 = (\<Gamma>, U, Some (C, \<gamma>))"
      unfolding conflict.simps by auto
    with step.hyps have "\<not> conflict N \<beta> S0 S1" and "reasonable_scl N \<beta> S0 S1"
      unfolding regular_scl_def by (simp_all add: conflict.simps)
    with step.prems have "scl N \<beta> S0 S1" and "\<not> decide N \<beta> S0 S1"
      unfolding reasonable_scl_def by blast+
    moreover from step.prems have "\<not> backtrack N \<beta> S0 S1"
      unfolding backtrack.simps by blast
    ultimately show "propagate N \<beta> S0 S1"
      by (simp add: scl_def S1_def skip.simps conflict.simps factorize.simps resolve.simps)
  qed
qed

lemma resolve_if_conflict_follows_propagate:
  assumes
    fin: "finite N" "finite (state_learned S\<^sub>0)" and
    no_conf: "\<nexists>S\<^sub>1. conflict N \<beta> S\<^sub>0 S\<^sub>1" and
    propa: "propagate N \<beta> S\<^sub>0 S\<^sub>1" and
    conf: "conflict N \<beta> S\<^sub>1 S\<^sub>2"
  shows "\<exists>S\<^sub>3. resolve N \<beta> S\<^sub>2 S\<^sub>3"
  using propa
proof (cases N \<beta> S\<^sub>0 S\<^sub>1 rule: propagate.cases)
  case (propagateI C U C' L \<Gamma> \<gamma> C\<^sub>0 C\<^sub>1 \<mu> \<gamma>')
  hence S\<^sub>0_def: "S\<^sub>0 = (\<Gamma>, U, None)"
    by simp

  from conf obtain D' \<sigma> D where
    S\<^sub>2_def: "S\<^sub>2 = (trail_propagate \<Gamma> (L \<cdot>l \<mu>) (C\<^sub>0 \<cdot> \<mu>) \<gamma>', U, Some (D', \<sigma>))" and
    D_in: "D \<in> N \<union> U" and
    D'_def: "D' = D \<cdot> renaming_wrt (insert (add_mset L C\<^sub>0 \<cdot> \<mu>) (N \<union> U \<union> clss_of_trail \<Gamma>))" and
    "subst_domain \<sigma> \<subseteq> vars_cls D'" and
    gr_D'_\<sigma>: "is_ground_cls (D' \<cdot> \<sigma>)" and
    tr_false_\<Gamma>_L_\<mu>: "trail_false_cls (trail_propagate \<Gamma> (L \<cdot>l \<mu>) (C\<^sub>0 \<cdot> \<mu>) \<gamma>') (D' \<cdot> \<sigma>)"
    unfolding propagateI
    by (auto simp: rename_clause_def elim: conflict.cases)

  define \<rho> :: "'v \<Rightarrow> ('f, 'v) Term.term" where
    "\<rho> = renaming_wrt (insert (add_mset L C\<^sub>0 \<cdot> \<mu>) (N \<union> U \<union> clss_of_trail \<Gamma>))"

  from no_conf have "\<not> trail_false_cls \<Gamma> (D' \<cdot> \<sigma>)"
    using gr_D'_\<sigma> D_in not_trail_false_ground_cls_if_no_conflict[OF fin, of \<beta> D "\<rho> \<odot> \<sigma>"]
    unfolding D'_def \<rho>_def[symmetric]
    by (simp add: S\<^sub>0_def)
  with tr_false_\<Gamma>_L_\<mu> have "- (L \<cdot>l \<mu> \<cdot>l \<gamma>') \<in># D' \<cdot> \<sigma>"
    using trail_propagate_def subtrail_falseI by metis
  then obtain D'' L' where D'_def': "D' = add_mset L' D''" and "- (L \<cdot>l \<mu> \<cdot>l \<gamma>') = L' \<cdot>l \<sigma>"
    by (meson Melem_subst_cls multi_member_split)
  hence 1: "L \<cdot>l \<mu> \<cdot>l \<gamma>' = - (L' \<cdot>l \<sigma>)"
    by (metis uminus_of_uminus_id)
  hence "atm_of L \<cdot>a \<mu> \<cdot>a \<gamma>' = atm_of L' \<cdot>a \<sigma>"
    by (metis atm_of_subst_lit atm_of_uminus)
  hence "\<exists>\<mu>'. Unification.mgu (atm_of L \<cdot>a \<mu>) (atm_of L') = Some \<mu>'"
  proof (rule ex_mgu_if_subst_eq_subst_and_disj_vars)
    have fin': "finite (\<Union> (vars_cls ` insert (add_mset L C\<^sub>0 \<cdot> \<mu>) (N \<union> U \<union> clss_of_trail \<Gamma>)))"
      using S\<^sub>0_def fin(1) fin(2) by auto
    show "vars_term (atm_of L \<cdot>a \<mu>) \<inter> vars_lit L' = {}"
      using D'_def[unfolded D'_def']
      using renaming_correct[OF fin']
      by (smt (verit, best) UN_I Un_iff atm_of_subst_lit disjoint_iff fin' insertCI
          subst_cls_add_mset vars_cls_add_mset vars_cls_subst_renaming_disj)
  next
    have "is_ground_lit (L \<cdot>l \<mu> \<cdot>l \<gamma>')"
      using is_ground_cls_imp_is_ground_lit[OF \<open>- (L \<cdot>l \<mu> \<cdot>l \<gamma>') \<in># D' \<cdot> \<sigma>\<close> gr_D'_\<sigma>]
      by (simp add: is_ground_lit_iff_vars_empty)
    hence "(\<Union>x\<in>vars_term (atm_of L \<cdot>a \<mu>). if \<gamma>' x = Var x then {} else vars_term (\<gamma>' x)) = {}"
      unfolding atm_of_subst_lit[symmetric]
      using is_ground_lit_is_ground_on_var[unfolded is_ground_atm_iff_vars_empty]
      by force
    then show "(\<Union>x\<in>vars_term (atm_of L \<cdot>a \<mu>). if \<gamma>' x = Var x then {} else vars_term (\<gamma>' x)) \<inter>
      {x \<in> vars_lit L'. \<sigma> x \<noteq> Var x} = {}"
      by simp
  qed
  then obtain \<mu>' where 2: "is_mimgu \<mu>' {{atm_of (L \<cdot>l \<mu>), atm_of L'}}"
    using is_mimgu_if_mgu_eq_Some by auto

  show ?thesis
    using resolveI[of _ \<Gamma> "L \<cdot>l \<mu>" "C\<^sub>0 \<cdot> \<mu>" \<gamma>' _ N U D'', OF refl refl 1 2]
    unfolding S\<^sub>2_def D'_def'
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

lemma conflict_with_literal_gets_resolved:
  defines "res_scl \<equiv> \<lambda>N \<beta> S S'. skip N \<beta> S S' \<or> factorize N \<beta> S S' \<or> resolve N \<beta> S S'"
  assumes
    fin_N: "finite N" and disj_vars_N: "disjoint_vars_set N" and
    reg_run: "(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S1" and
    trail_lit: "state_trail S1 = Lc # \<Gamma>" and
    conf: "conflict N \<beta> S1 S2" and
    resolution: "(res_scl N \<beta>)\<^sup>*\<^sup>* S2 Sn" and
    backtrack: "\<exists>Sn'. backtrack N \<beta> Sn Sn'"
  shows "\<not> is_decision_lit Lc \<and> strict_suffix (state_trail Sn) (state_trail S1)"
proof -
  from trail_lit obtain S0 where
    reg_run': "(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S0" and
    reg_step: "regular_scl N \<beta> S0 S1" and
    propa: "propagate N \<beta> S0 S1"
    using trail_lit before_regular_conflict[OF fin_N reg_run conf] by force

  have fin_learned_S0: "finite (state_learned S0)"
    by (smt (verit, best) disj_vars_N fin_N reg_run' regular_run_sound_state sound_initial_state
        sound_state_def state_learned_simp)

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
          by (auto simp: res_scl_def suffix_def factorize_state_trail resolve_state_trail
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
  "ground_redundant lt N C \<longleftrightarrow> is_ground_clss N \<and> is_ground_cls C \<and> {D \<in> N. lt\<^sup>=\<^sup>= D C} \<TTurnstile>e {C}"

definition redundant where
  "redundant lt N C \<longleftrightarrow> (\<forall>C' \<in> grounding_of_cls C. ground_redundant lt (grounding_of_clss N) C')"

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

lemma
  assumes "\<exists>C \<in> N. \<exists>\<sigma>. C \<cdot> \<sigma> \<subseteq># D"
  shows "\<exists>C \<in> {C \<in> N. multp (trail_less_ex lt Ls) C D}. \<exists>\<sigma>. C \<cdot> \<sigma> \<subseteq># D"
  oops


section \<open>Trail-Induced Ordering\<close>

subsection \<open>Miscellaneous Lemmas\<close>

lemma pairwise_distinct_if_sound_trail:
  fixes \<Gamma>
  defines "Ls \<equiv> (map fst \<Gamma>)"
  shows "sound_trail N U \<Gamma> \<Longrightarrow>
    \<forall>i < length Ls. \<forall>j < length Ls. i \<noteq> j \<longrightarrow> Ls ! i \<noteq> Ls ! j \<and> Ls ! i \<noteq> - (Ls ! j)"
  unfolding Ls_def
proof (induction \<Gamma> rule: sound_trail.induct)
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

lemma irreflp_trail_less_if_sound: "sound_trail N U \<Gamma> \<Longrightarrow> irreflp (trail_less (map fst \<Gamma>))"
  using irreflp_trail_less[OF
      Clausal_Logic.uminus_not_id'
      Clausal_Logic.uminus_of_uminus_id
      pairwise_distinct_if_sound_trail]
  by assumption

lemma transp_trail_less_if_sound: "sound_trail N U \<Gamma> \<Longrightarrow> transp (trail_less (map fst \<Gamma>))"
  using transp_trail_less[OF
      Clausal_Logic.uminus_not_id'
      Clausal_Logic.uminus_of_uminus_id
      pairwise_distinct_if_sound_trail]
  by assumption

lemma asymp_trail_less_if_sound: "sound_trail N U \<Gamma> \<Longrightarrow> asymp (trail_less (map fst \<Gamma>))"
  using asymp_trail_less[OF
      Clausal_Logic.uminus_not_id'
      Clausal_Logic.uminus_of_uminus_id
      pairwise_distinct_if_sound_trail]
  by assumption


subsection \<open>Extension on All Literals\<close>

lemma transp_trail_less_ex_if_sound: "sound_trail N U \<Gamma> \<Longrightarrow> transp lt \<Longrightarrow> transp (trail_less_ex lt (map fst \<Gamma>))"
  using transp_trail_less_ex[OF
      Clausal_Logic.uminus_not_id'
      Clausal_Logic.uminus_of_uminus_id
      pairwise_distinct_if_sound_trail]
  by assumption

lemma asymp_trail_less_ex_if_sound:
  "sound_trail N U \<Gamma> \<Longrightarrow> asymp lt \<Longrightarrow> asymp (trail_less_ex lt (map fst \<Gamma>))"
  using asymp_trail_less_ex[OF
      Clausal_Logic.uminus_not_id'
      Clausal_Logic.uminus_of_uminus_id
      pairwise_distinct_if_sound_trail]
  by assumption


subsection \<open>Properties\<close>

lemma trail_defined_if_trail_less_ex:
  "trail_less_ex lt (map fst \<Gamma>) L K \<Longrightarrow> trail_defined_lit \<Gamma> K \<Longrightarrow> trail_defined_lit \<Gamma> L"
  by (metis (no_types, opaque_lifting) list.set_map trail_defined_lit_def trail_less_ex_def)

lemma trail_defined_cls_if_lt_defined:
  assumes sound_\<Gamma>: "sound_trail N U \<Gamma>" and
    transp_lt: "transp lt" and
    C_lt_D: "multp (trail_less_ex lt (map fst \<Gamma>)) C D" and
    tr_def_D: "trail_defined_cls \<Gamma> D"
  shows "trail_defined_cls \<Gamma> C"
proof -
  have transp_tr_lt_ex: "transp (trail_less_ex lt (map fst \<Gamma>))"
    by (rule transp_trail_less_ex_if_sound[OF sound_\<Gamma> transp_lt])

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
  assumes "(\<lambda>S S'. skip N \<beta> S S' \<or> factorize N \<beta> S S' \<or> resolve N \<beta> S S')\<^sup>*\<^sup>* S S'"
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
    by (smt (verit) conflict.cases factorize.simps option.simps(3) prod.simps(1) resolve.simps
        skip.simps)
  ultimately have "regular_scl N \<beta> S' S''"
    by (simp add: regular_scl_def)
  with step.IH show ?case
    by simp
qed

lemma not_trail_true_and_false_lit:
  "sound_trail N U \<Gamma> \<Longrightarrow> \<not> (trail_true_lit \<Gamma> L \<and> trail_false_lit \<Gamma> L)"
  apply (simp add: trail_true_lit_def trail_false_lit_def)
  by (metis (no_types, lifting) in_set_conv_nth list.set_map pairwise_distinct_if_sound_trail
      uminus_not_id')

lemma not_trail_true_and_false_cls: "sound_trail N U \<Gamma> \<Longrightarrow> \<not> (trail_true_cls \<Gamma> C \<and> trail_false_cls \<Gamma> C)"
  using not_trail_true_and_false_lit
  by (metis trail_false_cls_def trail_true_cls_def)

lemma
  assumes
    fin_N: "finite N" and disj_vars_N: "disjoint_vars_set N" and
    regular_run: "(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S0" and
    conflict: "conflict N \<beta> S0 S1" and
    resolution: "(\<lambda>S S'. skip N \<beta> S S' \<or> factorize N \<beta> S S' \<or> resolve N \<beta> S S')\<^sup>+\<^sup>+ S1 Sn" and
    backtrack: "backtrack N \<beta> Sn Sn'" and
    "transp lt" (* and
    total_on_ground_lt: "totalp_on {L. is_ground_lit L} lt" *)
  shows "(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state Sn' \<and>
    (\<exists>C \<gamma>. state_conflict Sn = Some (C, \<gamma>) \<and>
      \<not> redundant (multp (trail_less_ex lt (map fst (state_trail S1)))) (N \<union> state_learned S1) C)"
proof -
  from regular_run conflict have reg_run_init_S1: "(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S1"
    by (meson regular_scl_def rtranclp.simps)
  also from resolution have reg_run_S1_Sn: "(regular_scl N \<beta>)\<^sup>*\<^sup>* ... Sn"
    using regular_run_if_skip_factorize_resolve_run tranclp_into_rtranclp by fast
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

  from conflict obtain C1 \<gamma>1 where conflict_S1: "state_conflict S1 = Some (C1, \<gamma>1)"
    by (smt (verit, best) conflict.simps state_conflict_simp)
  with backtrack obtain Cn \<gamma>n where conflict_Sn: "state_conflict Sn = Some (Cn, \<gamma>n)"
    by (smt (verit) backtrack.simps state_conflict_simp)

  from fin_N disj_vars_N have "sound_state N \<beta> initial_state"
    by (rule sound_initial_state)
  with regular_run have sound_S0: "sound_state N \<beta> S0"
    by (simp add: regular_run_sound_state)
  with conflict have sound_S1: "sound_state N \<beta> S1"
    by (simp add: conflict_sound_state)
  with resolution have sound_Sn: "sound_state N \<beta> Sn"
    by (induction rule: tranclp_induct)
      (auto intro: skip_sound_state factorize_sound_state resolve_sound_state)

  from conflict_Sn sound_Sn have "N \<TTurnstile>\<G>e {Cn}" and
    trail_Sn_false_Cn_\<gamma>n: "trail_false_cls (state_trail Sn) (Cn \<cdot> \<gamma>n)"
    by (auto simp add: sound_state_def)

  from conflict_S1 sound_S1 have trail_S1_false_C1_\<gamma>1: "trail_false_cls (state_trail S1) (C1 \<cdot> \<gamma>1)"
    by (auto simp add: sound_state_def)

  from resolution have "suffix (state_trail Sn) (state_trail S1) \<and>
    (\<exists>Cn \<gamma>n. state_conflict Sn = Some (Cn, \<gamma>n) \<and> trail_false_cls (state_trail S1) (Cn \<cdot> \<gamma>n))"
  proof (induction Sn rule: tranclp_induct)
    case (base S2)
    thus ?case
    proof (elim disjE)
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
      by (smt (verit) factorize.simps prod.sel(1) resolve.simps skip.simps state_trail_def
          suffix_ConsI suffix_order.eq_iff)
    with step.IH have "suffix (state_trail Sm') (state_trail S1)"
      by force

    from step.hyps(1) sound_S1 have sound_Sm: "sound_state N \<beta> Sm"
      by (induction rule: tranclp_induct)
        (auto intro: skip_sound_state factorize_sound_state resolve_sound_state)

    from step.IH obtain Cm \<gamma>m where
      conflict_Sm: "state_conflict Sm = Some (Cm, \<gamma>m)" and
      trail_false_Cm_\<gamma>m: "trail_false_cls (state_trail S1) (Cm \<cdot> \<gamma>m)"
      using step.prems step.hyps(2) \<open>suffix (state_trail Sm') (state_trail Sm)\<close>
      by auto

    from step.hyps(2) show ?case
    proof (elim disjE)
      assume "skip N \<beta> Sm Sm'"
      thus ?thesis
        using \<open>suffix (state_trail Sm') (state_trail S1)\<close>
        using conflict_Sm skip.simps trail_false_Cm_\<gamma>m by auto
    next
      assume "factorize N \<beta> Sm Sm'"
      thus ?thesis
      proof (cases N \<beta> Sm Sm' rule: factorize.cases)
        case (factorizeI L \<sigma> L' \<mu> \<sigma>' D \<Gamma> U)
        with conflict_Sm have Cm_def: "Cm = D + {#L, L'#}" and \<gamma>m_def: "\<gamma>m = \<sigma>"
          by simp_all
        with factorizeI(3,4) have "trail_false_cls (state_trail S1) ((D + {#L#}) \<cdot> \<mu> \<cdot> \<sigma>)"
          apply -
          apply (rule trail_false_cls_subst_mgu_before_grounding[of _ _ L L'])
          using trail_false_Cm_\<gamma>m apply simp
           apply auto
          by (smt (verit, best) atm_of_subst_lit finite.emptyI finite.insertI insertE is_unifier_alt
              is_unifiers_def singletonD)
        with factorizeI(5) have "trail_false_cls (state_trail S1) ((D + {#L#}) \<cdot> \<mu> \<cdot> \<sigma>')"
          by (metis subsetI subst_cls_restrict_subst_idem)
        with factorizeI(2) show ?thesis
          using \<open>suffix (state_trail Sm') (state_trail S1)\<close>
          using state_conflict_simp by blast
      qed
    next
      assume "resolve N \<beta> Sm Sm'"
      thus ?thesis
      proof (cases N \<beta> Sm Sm' rule: resolve.cases)
        case (resolveI \<Gamma> \<Gamma>' L C \<delta> \<rho> U D L' \<sigma> \<mu>)
        have "is_renaming (renaming_wrt (N \<union> U \<union> clss_of_trail \<Gamma> \<union> {D + {#L'#}}))"
          apply (rule is_renaming_renaming_wrt)
          using resolveI
          by (smt (verit, best) finite.emptyI finite.insertI finite_UnI finite_clss_of_trail
              sound_Sm sound_state_def state_learned_simp)
        with resolveI have is_renaming_\<rho>: "is_renaming \<rho>"
          by simp

        from resolveI conflict_Sm have Cm_def: "Cm = D + {#L'#}" and \<gamma>m_def: "\<gamma>m = \<sigma>"
          by simp_all
        hence tr_false_D_L'_\<sigma>: "trail_false_cls (state_trail S1) ((D + {#L'#}) \<cdot> \<sigma>)"
          using trail_false_Cm_\<gamma>m by simp

        from resolveI sound_Sm have
          "disjoint_vars_set (N \<union> U \<union> clss_of_trail \<Gamma>)" and
          disj_N_U_\<Gamma>_D_L': "\<forall>C \<in> N \<union> U \<union> clss_of_trail \<Gamma>. disjoint_vars (D + {#L'#}) C" and
          "is_ground_cls ((D + {#L'#}) \<cdot> \<sigma>)" and
          dom_\<sigma>: "subst_domain \<sigma> \<subseteq> vars_cls (D + {#L'#})" and
          "sound_trail N U \<Gamma>"
          unfolding sound_state_def by simp_all

        have "vars_cls (D + {#L'#}) \<inter> vars_cls (C + {#L#}) = {}"
          apply(rule disj_N_U_\<Gamma>_D_L'[unfolded disjoint_vars_iff_inter_empty,
                rule_format, of "C + {#L#}"])
          by (simp add: resolveI(3))

        from resolveI have "atm_of (L \<cdot>l \<delta>) = atm_of (L' \<cdot>l \<sigma>)" by simp
        hence "(atm_of L) \<cdot>a \<delta> = (atm_of L') \<cdot>a \<sigma>" by simp

        have \<sigma>_\<delta>_in_unif: "\<sigma> \<odot> \<delta> \<in> unifiers {(atm_of L, atm_of L')}"
        proof (rule subst_comp_in_unifiersI')
          show "atm_of L \<cdot>a \<delta> = atm_of L' \<cdot>a \<sigma>"
            using resolveI by (metis atm_of_eq_uminus_if_lit_eq atm_of_subst_lit)
        next
          show "vars_lit L \<inter> subst_domain \<sigma> = {}"
            using dom_\<sigma> \<open>vars_cls (D + {#L'#}) \<inter> vars_cls (C + {#L#}) = {}\<close> by fastforce
        next
          have "subst_domain \<delta> \<subseteq> vars_cls C \<union> vars_lit L"
            using \<open>sound_trail N U \<Gamma>\<close>
            unfolding sound_trail.simps[of N U \<Gamma>]
            unfolding resolveI(3)
            by (simp add: trail_propagate_def)
          then show "vars_lit L' \<inter> subst_domain \<delta> = {}"
            using \<open>vars_cls (D + {#L'#}) \<inter> vars_cls (C + {#L#}) = {}\<close> by auto
        next
          have "range_vars \<sigma> = {}"
            unfolding range_vars_def UNION_empty_conv subst_range.simps
            using dom_\<sigma> \<open>is_ground_cls ((D + {#L'#}) \<cdot> \<sigma>)\<close> is_ground_cls_is_ground_on_var
              is_ground_atm_iff_vars_empty
            by fast
          thus "range_vars \<sigma> \<inter> subst_domain \<delta> = {}"
            by simp
        qed

        from resolveI \<open>sound_trail N U \<Gamma>\<close> have "trail_false_cls \<Gamma>' (C \<cdot> \<delta>)"
          by (auto simp: trail_propagate_def elim: sound_trail.cases)

        from resolveI have "suffix \<Gamma>' (state_trail S1)"
          using \<open>suffix (state_trail Sm') (state_trail S1)\<close>
          by (metis (no_types, lifting) state_trail_simp suffix_order.trans suffix_trail_propagate)

        have "trail_false_cls (state_trail S1) ((D + C) \<cdot> \<mu> \<cdot> \<sigma> \<cdot> \<delta>)"
        proof (rule trail_false_cls_plus_subst_mgu_before_groundings[
              of "state_trail S1" D L' \<sigma> _ C \<delta> L \<mu>, OF tr_false_D_L'_\<sigma> \<open>trail_false_cls \<Gamma>' (C \<cdot> \<delta>)\<close>
                \<open>suffix \<Gamma>' (state_trail S1)\<close> \<open>is_ground_cls ((D + {#L'#}) \<cdot> \<sigma>)\<close>
                \<open>vars_cls (D + {#L'#}) \<inter> vars_cls (C + {#L#}) = {}\<close>
                \<open>subst_domain \<sigma> \<subseteq> vars_cls (D + {#L'#})\<close>])
          from resolveI show "is_imgu \<mu> {{atm_of L, atm_of L'}}"
            by auto
        next
          have "\<forall>A \<in> {atm_of L, atm_of L'}. \<forall>B \<in> {atm_of L, atm_of L'}. A \<cdot>a (\<sigma> \<odot> \<delta>) = B \<cdot>a (\<sigma> \<odot> \<delta>)"
            using \<sigma>_\<delta>_in_unif by fastforce
          hence "is_unifier (\<sigma> \<odot> \<delta>) {atm_of L, atm_of L'}"
            using is_unifier_alt[of "{atm_of L, atm_of L'}" "\<sigma> \<odot> \<delta>"]
            by blast
          thus "is_unifiers (\<sigma> \<odot> \<delta>) {{atm_of L, atm_of L'}}"
            using is_unifiers_def by blast
        qed
        then have "trail_false_cls (state_trail S1) ((D + C) \<cdot> \<mu> \<cdot> \<rho> \<cdot>
          restrict_subst (vars_cls ((D + C) \<cdot> \<mu> \<cdot> \<rho>)) (inv_renaming' \<rho> \<odot> \<sigma> \<odot> \<delta>))"
          unfolding subst_cls_restrict_subst_idem[OF subset_refl]
          unfolding subst_cls_comp_subst subst_cls_renaming_inv_renaming_idem[OF is_renaming_\<rho>]
          by assumption
        then show ?thesis
          using \<open>suffix (state_trail Sm') (state_trail S1)\<close>
          using resolveI by simp
      qed
    qed
  qed

  then obtain Cn \<gamma>n where
    "suffix (state_trail Sn) (state_trail S1)" and
    conflict_Sn: "state_conflict Sn = Some (Cn, \<gamma>n)" and
    "trail_false_cls (state_trail S1) (Cn \<cdot> \<gamma>n)"
    by auto

  have "\<not> redundant (multp (trail_less_ex lt (map fst (state_trail S1)))) (N \<union> state_learned S1) Cn"
  proof (rule notI)
    assume "redundant (multp (trail_less_ex lt (map fst (state_trail S1)))) (N \<union> state_learned S1) Cn"
    moreover from sound_Sn conflict_Sn have "Cn \<cdot> \<gamma>n \<in> grounding_of_cls Cn"
      unfolding sound_state_def
      using grounding_of_cls_ground grounding_of_subst_cls_subset 
      by fastforce
    ultimately have gr_red_Cn_\<gamma>n: "ground_redundant
      (multp (trail_less_ex lt (map fst (state_trail S1))))
      (grounding_of_clss (N \<union> state_learned S1)) (Cn \<cdot> \<gamma>n)"
      by (simp add: redundant_def)

    define S where
      "S = {D \<in> grounding_of_clss (N \<union> state_learned S1).
        (multp (trail_less_ex lt (map fst (state_trail S1))))\<^sup>=\<^sup>= D (Cn \<cdot> \<gamma>n)}"

    from gr_red_Cn_\<gamma>n have "S \<TTurnstile>e {Cn \<cdot> \<gamma>n}"
      unfolding ground_redundant_def S_def by simp

    from sound_S1 have sound_trail_S1: "sound_trail N (state_learned S1) (state_trail S1)"
      by (auto simp add: sound_state_def)
    hence "trail_consistent (state_trail S1)"
      by (rule trail_consistent_if_sound)

    moreover have "\<forall>L\<in>#Cn \<cdot> \<gamma>n. trail_defined_lit (state_trail S1) L"
      using \<open>trail_false_cls (state_trail S1) (Cn \<cdot> \<gamma>n)\<close> trail_defined_lit_iff_true_or_false
        trail_false_cls_def by blast

    ultimately have "trail_interp (state_trail S1) \<TTurnstile> Cn \<cdot> \<gamma>n \<longleftrightarrow>
      trail_true_cls (state_trail S1) (Cn \<cdot> \<gamma>n)"
      using trail_true_cls_iff_trail_interp_entails by auto
    hence "\<not> trail_interp (state_trail S1) \<TTurnstile>s {Cn \<cdot> \<gamma>n}"
      using \<open>trail_false_cls (state_trail S1) (Cn \<cdot> \<gamma>n)\<close>
      using not_trail_true_and_false_cls[OF sound_trail_S1]
      by auto
    hence "\<not> trail_interp (state_trail S1) \<TTurnstile>s S"
      using \<open>S \<TTurnstile>e {Cn \<cdot> \<gamma>n}\<close>[rule_format, of "trail_interp (state_trail S1)"]
      by argo
    then obtain D where D_in: "D \<in> S" and "\<not> trail_interp (state_trail S1) \<TTurnstile> D"
      by (auto simp: true_clss_def)

    have "trail_defined_cls (state_trail S1) (Cn \<cdot> \<gamma>n)"
      using \<open>\<forall>L\<in>#Cn \<cdot> \<gamma>n. trail_defined_lit (state_trail S1) L\<close> trail_defined_cls_def by blast

    from \<open>D \<in> S\<close> have
      D_in: "D \<in> grounding_of_clss (N \<union> state_learned S1)" and
      D_le_Cn_\<gamma>n: "(multp (trail_less_ex lt (map fst (state_trail S1))))\<^sup>=\<^sup>= D (Cn \<cdot> \<gamma>n)"
      unfolding S_def by simp_all
    hence "trail_defined_cls (state_trail S1) D"
      unfolding Lattices.sup_apply Boolean_Algebras.sup_bool_def
    proof (elim disjE)
      assume multp_D_Cn_\<gamma>n: "multp (trail_less_ex lt (map fst (state_trail S1))) D (Cn \<cdot> \<gamma>n)"
      show "trail_defined_cls (state_trail S1) D"
        using \<open>sound_trail N (state_learned S1) (state_trail S1)\<close> multp_D_Cn_\<gamma>n
          \<open>trail_defined_cls (state_trail S1) (Cn \<cdot> \<gamma>n)\<close> \<open>transp lt\<close>
        by (auto intro: trail_defined_cls_if_lt_defined)
    next
      assume "D = Cn \<cdot> \<gamma>n"
      then show "trail_defined_cls (state_trail S1) D"
        using \<open>trail_defined_cls (state_trail S1) (Cn \<cdot> \<gamma>n)\<close> by simp
    qed
    then have "trail_false_cls (state_trail S1) D"
      using \<open>\<not> trail_interp (state_trail S1) \<TTurnstile> D\<close>
      using \<open>trail_consistent (state_trail S1)\<close> trail_interp_cls_if_trail_true
        trail_true_or_false_cls_if_defined by blast


    have "trail_false_cls (state_trail S1) D"
      apply (rule trail_false_cls_iff_not_trail_interp_entails[THEN iffD2,
          OF trail_consistent_if_sound[OF sound_trail_S1] _
            \<open>\<not> trail_interp (state_trail S1) \<TTurnstile> D\<close>])
      using \<open>trail_defined_cls (state_trail S1) D\<close> trail_defined_cls_def by blast

    from backtrack have "C1 \<noteq> {#}"
      using reg_run_S1_Sn conflict_S1 no_more_step_if_conflict_mempty
      by (metis converse_rtranclpE scl_def reasonable_if_regular reg_run_S1_Sn scl_if_reasonable)
    hence "{#} \<notin> N"
      using mempty_not_in_initial_clauses_if_regular_run_reaches_non_empty_conflict
      using \<open>(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S1\<close> conflict_S1 by blast
    then obtain S where
      "(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state S" and "regular_scl N \<beta> S S0" and "propagate N \<beta> S S0"
      using before_regular_conflict[OF fin_N regular_run conflict] by auto

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
    (* hence "(\<exists>Sn. resolve N \<beta> S1 Sn)"
      using resolve_before_conflict_with_propagated_literal[OF fin_N disj_vars_N
          regular_run conflict]
      by (simp add: trail_propagate_def) *)

    with backtrack have "strict_suffix (state_trail Sn) (state_trail S0)"
      using conflict_with_literal_gets_resolved[OF fin_N disj_vars_N regular_run _ conflict]
        resolution
      by (metis (no_types, lifting) trail_propagate_def tranclp_into_rtranclp)
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

    from D_le_Cn_\<gamma>n have "L \<cdot>l \<gamma> \<notin># D \<and> - (L \<cdot>l \<gamma>) \<notin># D"
    proof (rule sup2E)
      show "D = Cn \<cdot> \<gamma>n \<Longrightarrow> ?thesis"
        using \<open>L \<cdot>l \<gamma> \<notin># Cn \<cdot> \<gamma>n \<and> - (L \<cdot>l \<gamma>) \<notin># Cn \<cdot> \<gamma>n\<close> by argo
    next
      assume "multp (trail_less_ex lt (map fst (state_trail S1))) D (Cn \<cdot> \<gamma>n)"
      hence D_lt_Cn_\<gamma>n': "multp (trail_less (map fst (state_trail S1))) D (Cn \<cdot> \<gamma>n)"
      proof (rule multp_mono_strong)
        from \<open>transp lt\<close> show "transp (trail_less_ex lt (map fst (state_trail S1)))"
          by (rule transp_trail_less_ex_if_sound[OF
                \<open>sound_trail N (state_learned S1) (state_trail S1)\<close>])
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
        using transp_trail_less_if_sound[OF sound_trail_S1, THEN transpD] by blast

      have "\<not> (L \<cdot>l \<gamma> \<in># D \<or> - (L \<cdot>l \<gamma>) \<in># D)"
      proof (rule notI)
        obtain I J K where
          "Cn \<cdot> \<gamma>n = I + J" and D_def: "D = I + K" and "J \<noteq> {#}" and
          "\<forall>k\<in>#K. \<exists>x\<in>#J. trail_less (map fst (state_trail S1)) k x"
          using multp_implies_one_step[OF transp_trail_less_if_sound[OF sound_trail_S1] D_lt_Cn_\<gamma>n']
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
            using asymp_trail_less_if_sound[OF sound_trail_S1, THEN asympD]
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
    
    have "\<exists>S'. conflict N \<beta> S S'"
    proof -
      have fin_learned_S1: "finite (state_learned S1)"
        by (smt (verit, best) sound_state_def sound_S1 state_learned_simp)
      show ?thesis
        using ex_conflict_if_trail_false_cls[OF fin_N fin_learned_S1
            \<open>trail_false_cls (state_trail S) D\<close> D_in]
        unfolding \<open>state_learned S = state_learned S1\<close>[symmetric]
          \<open>state_conflict S = None\<close>[symmetric]
        by simp
    qed
    thus False
      using \<open>regular_scl N \<beta> S S0\<close> \<open>propagate N \<beta> S S0\<close>
      using conflict_well_defined(1) regular_scl_def by blast
  qed

  with conflict_Sn show ?thesis
    using \<open>(regular_scl N \<beta>)\<^sup>*\<^sup>* initial_state Sn'\<close>
    by simp
qed

end

end