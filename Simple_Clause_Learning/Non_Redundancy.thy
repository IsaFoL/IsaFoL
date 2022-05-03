theory Non_Redundancy
  imports
    Simple_Clause_Learning
    Trail_Induced_Ordering
begin

context scl begin


section \<open>Clause Redundancy\<close>

definition ground_redundant where
  "ground_redundant lt N C \<longleftrightarrow> is_ground_clss N \<and> is_ground_cls C \<and> {D \<in> N. lt\<^sup>=\<^sup>= D C} \<TTurnstile>e {C}"

definition redundant where
  "redundant lt N C \<longleftrightarrow> (\<forall>C' \<in> grounding_of_cls C. ground_redundant lt (grounding_of_clss N) C')"


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
    total_on_lt: "Restricted_Predicates.total_on lt (set_mset C \<union> set_mset D)" and
    C_lt_D: "multp (trail_less_ex lt (map fst \<Gamma>)) C D" and
    tr_def_D: "trail_defined_cls \<Gamma> D"
  shows "trail_defined_cls \<Gamma> C"
proof -
  have transp_on: "transp_on (trail_less_ex lt (map fst \<Gamma>)) S" for S
    using transp_trail_less_ex_if_sound[OF sound_\<Gamma> transp_lt]
    by (metis transpD transp_onI)

  have tot_on_C_D:
    "Restricted_Predicates.total_on (trail_less_ex lt (map fst \<Gamma>)) (set_mset C \<union> set_mset D)"
    using total_on_trail_less_ex[OF Clausal_Logic.uminus_of_uminus_id total_on_lt]
    by assumption

  show ?thesis
    using total_on_unionD[
        OF tot_on_C_D,
        THEN multiset_is_empty_or_bex_greatest_element_if_trans_and_total[OF transp_on]]
  proof (elim disjE)
    assume
      "\<exists>x\<in>#C. \<forall>y\<in>#C. x \<noteq> y \<longrightarrow> trail_less_ex lt (map fst \<Gamma>) y x"
      "D = {#}"
    thus "trail_defined_cls \<Gamma> C"
      using C_lt_D multp_implies_one_step sound_\<Gamma> transp_lt transp_trail_less_ex_if_sound
      by blast
  next
    assume
      "\<exists>x\<in>#C. \<forall>y\<in>#C. x \<noteq> y \<longrightarrow> trail_less_ex lt (map fst \<Gamma>) y x"
      "\<exists>x\<in>#D. \<forall>y\<in>#D. x \<noteq> y \<longrightarrow> trail_less_ex lt (map fst \<Gamma>) y x"
    show "trail_defined_cls \<Gamma> C"
      using tr_def_D trail_defined_if_trail_less_ex
      by (smt (verit, ccfv_threshold) C_lt_D multp_implies_one_step sound_\<Gamma> trail_defined_cls_def
          transp_lt transp_trail_less_ex_if_sound union_iff)
  qed (simp_all add: trail_defined_cls_def)
qed

section \<open>Learned Clauses in Regular Runs\<close>

term multp
term "multp (trail_less_ex lt (map fst \<Gamma>))"
term "redundant (multp (trail_less_ex lt (map fst \<Gamma>)))"

term "regular_scl N initial_state"

thm regular_scl_def
thm ground_redundant_def redundant_def

lemma
  assumes "sound_state N S" and "conflict N S S'"
  shows "redundant (multp (trail_less_ex lt (map fst (state_trail S))))
    (N \<union> state_learned S) (fst (the (state_conflict S')))"
proof -
  from \<open>conflict N S S'\<close> obtain \<Gamma> U C \<gamma> where
    S_def: "S = (\<Gamma>, U, None)" and S'_def: "S' = (\<Gamma>, U, Some (C, \<gamma>))"
    by (smt (verit) conflict.simps)

  from \<open>conflict N S S'\<close> obtain C' where
    "C' \<in> N \<union> U" and
    "C = rename_clause (N \<union> U \<union> clss_of_trail \<Gamma>) C'" and
    "subst_domain \<gamma> \<subseteq> vars_cls C" and
    "is_ground_cls (C \<cdot> \<gamma>)" and
    "trail_false_cls \<Gamma> (C \<cdot> \<gamma>)"
    by (auto simp: S_def S'_def elim!: conflict.cases)

  then show ?thesis
    using assms(1)
    apply (simp add: S_def S'_def sound_state_def redundant_def ground_redundant_def
        grounding_of_cls_rename_clause is_ground_cls_if_in_grounding_of_cls)
    by (smt (verit, best) UN_I \<open>C' \<in> N \<union> U\<close> grounding_of_clss_def mem_Collect_eq true_clss_def)
qed

lemma assumes "asymp lt" and "transp lt" and "sound_state N S" and "resolve N S S'"
  shows "\<not> redundant (multp (trail_less_ex lt (map fst (state_trail S))))
    (N \<union> state_learned S) (fst (the (state_conflict S')))"
proof (rule notI)
  from \<open>resolve N S S'\<close> \<open>sound_state N S\<close> have "sound_state N S'"
    by (rule resolve_sound_state)

  from \<open>resolve N S S'\<close> obtain \<Gamma> \<Gamma>' L C \<delta> D \<sigma> \<rho> U L' \<mu> where
    S_def: "S = (\<Gamma>, U, Some (D + {#L'#}, \<sigma>))" and
    S'_def: "S' = (\<Gamma>, U, Some ((D + C) \<cdot> \<mu> \<cdot> \<rho>,
      restrict_subst (vars_cls ((D + C) \<cdot> \<mu> \<cdot> \<rho>)) (inv_renaming' \<rho> \<odot> \<sigma> \<odot> \<delta>)))" and
    "\<Gamma> = trail_propagate \<Gamma>' L C \<delta>" and
    "\<rho> = renaming_wrt (N \<union> U \<union> clss_of_trail \<Gamma> \<union> {D + {#L'#}})" and
    "L \<cdot>l \<delta> = - (L' \<cdot>l \<sigma>)" and
    "Unification.mgu (atm_of L) (atm_of L') = Some \<mu>"
    by (cases N S S' rule: resolve.cases) simp_all

  define \<gamma> where "\<gamma> = restrict_subst (vars_cls ((D + C) \<cdot> \<mu> \<cdot> \<rho>)) (inv_renaming' \<rho> \<odot> \<sigma> \<odot> \<delta>)"
  define lt' where "lt' = multp (trail_less_ex lt (map fst \<Gamma>))"

  from \<open>sound_state N S'\<close> have "sound_trail N U \<Gamma>" and "trail_false_cls \<Gamma> ((D + C) \<cdot> \<mu> \<cdot> \<rho> \<cdot> \<gamma>)"
    by (simp_all add: sound_state_def S'_def \<gamma>_def)

  assume "redundant (multp (trail_less_ex lt (map fst (state_trail S))))
    (N \<union> state_learned S) (fst (the (state_conflict S')))"
  hence "redundant lt' (N \<union> U) ((D + C) \<cdot> \<mu> \<cdot> \<rho>)"
    by (simp add: S_def S'_def lt'_def)
  moreover from \<open>sound_state N S'\<close> have "is_ground_cls ((D + C) \<cdot> \<mu> \<cdot> \<rho> \<cdot> \<gamma>)"
    unfolding S'_def sound_state_def \<gamma>_def by simp
  ultimately have "ground_redundant lt' (grounding_of_clss (N \<union> U)) ((D + C) \<cdot> \<mu> \<cdot> \<rho> \<cdot> \<gamma>)"
    unfolding redundant_def
    by (metis grounding_of_cls_ground insert_subset subst_cls_eq_grounding_of_cls_subset_eq)
  hence gr_entails_gr:
    "{E \<in> grounding_of_clss (N \<union> U). lt'\<^sup>=\<^sup>= E ((D + C) \<cdot> \<mu> \<cdot> \<rho> \<cdot> \<gamma>)} \<TTurnstile>e {(D + C) \<cdot> \<mu> \<cdot> \<rho> \<cdot> \<gamma>}"
    by (simp add: ground_redundant_def)

  have "E \<in> {E \<in> grounding_of_clss (N \<union> U). lt'\<^sup>=\<^sup>= E ((D + C) \<cdot> \<mu> \<cdot> \<rho> \<cdot> \<gamma>)} \<Longrightarrow>
    trail_defined_lit \<Gamma> L" if "L \<in># E" for E L
    unfolding mem_Collect_eq Lattices.sup_apply sup_bool_def
  proof (elim conjE disjE)
    note trans = transp_trail_less_ex_if_sound[OF \<open>sound_trail N U \<Gamma>\<close> \<open>transp lt\<close>]

    assume "E \<in> grounding_of_clss (N \<union> U)" and "lt' E ((D + C) \<cdot> \<mu> \<cdot> \<rho> \<cdot> \<gamma>)"
    then show ?thesis
      using multiset_is_empty_or_bex_greatest_element_if_trans_and_total[OF ]
      using total_on_trail_less_ex
      sorry

    (* hence "multp\<^sub>H\<^sub>O (trail_less_ex lt (map fst \<Gamma>)) E ((D + C) \<cdot> \<mu> \<cdot> \<rho> \<cdot> \<gamma>)"
      unfolding lt'_def
      using transp_trail_less_ex_if_sound[OF \<open>sound_trail N U \<Gamma>\<close> \<open>transp lt\<close>]
      using asymp_trail_less_ex_if_sound[OF \<open>sound_trail N U \<Gamma>\<close> \<open>asymp lt\<close>]
      by (simp add: multp_eq_multp\<^sub>H\<^sub>O)
    then show ?thesis
      unfolding multp\<^sub>H\<^sub>O_def
      using \<open>trail_false_cls \<Gamma> ((D + C) \<cdot> \<mu> \<cdot> \<rho> \<cdot> \<gamma>)\<close>[unfolded trail_false_cls_def]
      using \<open>L \<in># E\<close>
      sorry *)
  next
    assume "E \<in> grounding_of_clss (N \<union> U)" and "E = (D + C) \<cdot> \<mu> \<cdot> \<rho> \<cdot> \<gamma>"
    with that and \<open>trail_false_cls \<Gamma> ((D + C) \<cdot> \<mu> \<cdot> \<rho> \<cdot> \<gamma>)\<close> show ?thesis
      using trail_defined_lit_iff_true_or_false trail_false_cls_def by blast
  qed

  obtain E where
    "E \<in> {E \<in> grounding_of_clss (N \<union> U). lt'\<^sup>=\<^sup>= E ((D + C) \<cdot> \<mu> \<cdot> \<rho> \<cdot> \<gamma>)} \<and> trail_false_cls \<Gamma> E"
    sorry

  then show False
    using \<open>trail_false_cls \<Gamma> ((D + C) \<cdot> \<mu> \<cdot> \<rho> \<cdot> \<gamma>)\<close>
    using gr_entails_gr[rule_format, of "trail_interp \<Gamma>"] contrapos_pp
    apply (simp add: \<open>is_ground_cls ((D + C) \<cdot> \<mu> \<cdot> \<rho> \<cdot> \<gamma>)\<close>)
    oops

lemma regular_run_if_skip_factorize_resolve_run:
  assumes "(\<lambda>S S'. skip N S S' \<or> factorize N S S' \<or> resolve N S S')\<^sup>*\<^sup>* S S'"
  shows "(regular_scl N)\<^sup>*\<^sup>* S S'"
  using assms
  by (smt (verit, ccfv_SIG) decide_well_defined(4) decide_well_defined(5) local.scl_def
      mono_rtranclp reasonable_scl_def regular_scl_def skip_well_defined(2))

lemma trail_false_conflict_after_skip:
  assumes
    conflict_S: "state_conflict S = Some (C, \<gamma>)" and
    false_C_\<gamma>: "trail_false_cls (state_trail S) (C \<cdot> \<gamma>)" and
    "skip N S S'"
  shows "state_conflict S' = Some (C, \<gamma>) \<and> trail_false_cls (state_trail S) (C \<cdot> \<gamma>)"
  using \<open>skip N S S'\<close>
proof (cases N S S' rule: skip.cases)
  case (skipI L \<delta> D \<sigma> \<Gamma> C U)
  then show ?thesis
    using conflict_S false_C_\<gamma>
    by (auto elim!: trail_false_cls_ConsD simp add: sound_state_def trail_propagate_def)
qed

lemma strict_suffix_trail_if_skip: "skip N S S' \<Longrightarrow> strict_suffix (state_trail S') (state_trail S)"
  by (auto simp: skip.simps strict_suffix_def suffix_def trail_propagate_def)

lemma eq_trail_if_factorize: "factorize N S S' \<Longrightarrow> state_trail S' = state_trail S"
  by (auto simp: factorize.simps)

lemma eq_trail_if_resolve: "resolve N S S' \<Longrightarrow> state_trail S' = state_trail S"
  by (auto simp: resolve.simps)

lemma not_trail_true_and_false_lit:
  "sound_trail N U \<Gamma> \<Longrightarrow> \<not> (trail_true_lit \<Gamma> L \<and> trail_false_lit \<Gamma> L)"
  apply (simp add: trail_true_lit_def trail_false_lit_def)
  by (metis (no_types, lifting) in_set_conv_nth list.set_map pairwise_distinct_if_sound_trail
      uminus_not_id')

lemma not_trail_true_and_false_cls: "sound_trail N U \<Gamma> \<Longrightarrow> \<not> (trail_true_cls \<Gamma> C \<and> trail_false_cls \<Gamma> C)"
  using not_trail_true_and_false_lit
  by (metis trail_false_cls_def trail_true_cls_def)

lemma conflict_if_mempty_in_clause_set:
  assumes "{#} \<in> N" and "state_conflict S1 = None"
  shows "\<exists>S2. conflict N S1 S2 \<and> state_conflict S2 = Some ({#}, Var)"
proof -
  from \<open>state_conflict S1 = None\<close> obtain \<Gamma> U where S1_def: "S1 = (\<Gamma>, U, None)"
    by (metis prod.collapse state_conflict_def)

  show ?thesis
  proof (intro exI conjI)
    from \<open>{#} \<in> N\<close> show "conflict N S1 (\<Gamma>, U, Some ({#}, Var))"
      by (auto simp: S1_def conflict.simps)
  next
    show "state_conflict (\<Gamma>, U, Some ({#}, Var)) = Some ({#}, Var)"
      by simp
  qed
qed

definition trail_no_conflict where
  "trail_no_conflict N \<Gamma> \<longleftrightarrow> (\<nexists>C \<gamma>. C \<in> N \<and> trail_false_cls \<Gamma> (C \<cdot> \<gamma>))"

lemma "trail_no_conflict (N \<union> U) \<Gamma> \<Longrightarrow> \<nexists>C \<gamma>. conflict N (\<Gamma>, U, None) (\<Gamma>, U, Some (C, \<gamma>))"
  apply (rule notI)
  apply (elim exE conflict.cases)
  unfolding trail_no_conflict_def
  by (metis Pair_inject rename_clause_def subst_cls_comp_subst)

lemma trail_no_conflict_union_iff:
  "trail_no_conflict (N1 \<union> N2) \<Gamma> \<longleftrightarrow> trail_no_conflict N1 \<Gamma> \<and> trail_no_conflict N2 \<Gamma>"
  unfolding trail_no_conflict_def by blast

lemma trail_no_conflict_initial_state:
  assumes "{#} \<notin> N"
  shows "trail_no_conflict (N \<union> state_learned initial_state) (state_trail initial_state)"
  unfolding trail_no_conflict_def
  apply simp
  by (metis assms not_trail_false_Nil(2) subst_cls_empty_iff)

definition trail_almost_no_conflict where
  "trail_almost_no_conflict N \<Gamma> \<longleftrightarrow> trail_no_conflict N (trail_backtrack \<Gamma> (trail_level \<Gamma>))"

lemma trail_false_cls_if_suffix_and_false:
  "suffix \<Gamma> \<Gamma>' \<Longrightarrow> trail_false_cls \<Gamma> C \<Longrightarrow> trail_false_cls \<Gamma>' C"
  unfolding trail_false_cls_def suffix_def
  by (elim exE) (auto simp add: trail_false_lit_def)

lemma trail_no_conflict_suffixI:
  "suffix \<Gamma> \<Gamma>' \<Longrightarrow> trail_no_conflict N \<Gamma>' \<Longrightarrow> trail_no_conflict N \<Gamma>"
  unfolding trail_no_conflict_def
  apply (erule contrapos_nn)
  apply (elim exE)
  using trail_false_cls_if_suffix_and_false by blast

lemma trail_almost_no_conflict_if_trail_no_conflict:
  "trail_no_conflict N \<Gamma> \<Longrightarrow> trail_almost_no_conflict N \<Gamma>"
  unfolding trail_almost_no_conflict_def trail_no_conflict_def
  using trail_backtrack_suffix[of \<Gamma>, THEN trail_false_cls_if_suffix_and_false]
  by (elim contrapos_nn) blast

lemma
  assumes suff: "suffix \<Gamma>' \<Gamma>" and "trail_almost_no_conflict N \<Gamma>"
  shows "trail_almost_no_conflict N \<Gamma>'"
proof -
  from suff have "suffix (trail_backtrack \<Gamma>' (trail_level \<Gamma>')) \<Gamma>"
    using trail_backtrack_suffix[of \<Gamma>']
    using suffix_order.order_trans by blast
  then show ?thesis
    unfolding trail_almost_no_conflict_def
    using trail_no_conflict_suffixI trail_almost_no_conflict_if_trail_no_conflict
    oops

(*
Mathias:
  The (case u of Some (C, \<gamma>) \<Rightarrow> ...) is not necessary.
  At a backtrack rule, one literal is undefined in the trail, which implies that it cannot be a
  conflicting clause.
Martin:
  This is correct for \<gamma>, but there could be a conflict with another grounding.
*)
definition regular_state where
  "regular_state N S \<longleftrightarrow> sound_state N S \<and>
    (\<exists>\<Gamma> U u. S = (\<Gamma>, U, u) \<and> trail_almost_no_conflict (N \<union> U) \<Gamma>)"

lemma conflict_preserves_trail_almost_no_conflict:
  assumes "conflict N S1 S2" and "trail_almost_no_conflict (N \<union> state_learned S1) (state_trail S1)"
  shows "trail_almost_no_conflict (N \<union> state_learned S2) (state_trail S2)"
  using assms by (auto simp: conflict.simps)

lemma conflict_regular_state:
  assumes step: "conflict N S1 S2" and "regular_state N S1"
  shows "regular_state N S2"
  using step
proof (cases N S1 S2 rule: conflict.cases)
  case (conflictI D U D' \<Gamma> \<sigma>)
  with \<open>regular_state N S1\<close> have
    sound_S1: "sound_state N S1" and
    tr_almost_no_conf: "trail_almost_no_conflict (N \<union> U) \<Gamma>"
    by (simp_all add: regular_state_def)

  show ?thesis
    unfolding regular_state_def
  proof (intro conjI exI)
    show "sound_state N S2"
      by (rule conflict_sound_state[OF step sound_S1])
  next
    show "S2 = (\<Gamma>, U, Some (D', \<sigma>))"
      using conflictI by simp
  next
    show "trail_almost_no_conflict (N \<union> U) \<Gamma>"
      by (rule tr_almost_no_conf)
  qed
qed

lemma propagate_preserves_trail_almost_no_conflict:
  assumes "propagate N S1 S2" and "trail_almost_no_conflict (N \<union> state_learned S1) (state_trail S1)"
  shows "trail_almost_no_conflict (N \<union> state_learned S2) (state_trail S2)"
  using assms by (auto simp add: propagate.simps trail_almost_no_conflict_def)

lemma propagate_regular_state:
  assumes step: "propagate N S1 S2" and "regular_state N S1"
  shows "regular_state N S2"
  using step
proof (cases N S1 S2 rule: propagate.cases)
  case (propagateI C U C'' L \<Gamma> \<gamma>)
  with \<open>regular_state N S1\<close> have
    sound_S1: "sound_state N S1" and
    tr_almost_no_conf: "trail_almost_no_conflict (N \<union> U) \<Gamma>"
    by (simp_all add: regular_state_def)
  show ?thesis
    unfolding regular_state_def
  proof (intro conjI exI)
    show "sound_state N S2"
      by (rule propagate_sound_state[OF step sound_S1])
  next
    show "S2 = (trail_propagate \<Gamma> L C'' \<gamma>, U, None)"
      using propagateI by simp
  next
    show "trail_almost_no_conflict (N \<union> U) (trail_propagate \<Gamma> L C'' \<gamma>)"
      using tr_almost_no_conf
      by (simp add: trail_almost_no_conflict_def)
  qed
qed

lemma skip_regular_state:
  assumes step: "skip N S1 S2" and "regular_state N S1"
  shows "regular_state N S2"
  using step
proof (cases N S1 S2 rule: skip.cases)
  case (skipI L \<delta> D \<sigma> \<Gamma> C U)
  with \<open>regular_state N S1\<close> have
    sound_S1: "sound_state N S1" and
    tr_almost_no_conf: "trail_almost_no_conflict (N \<union> U) (trail_propagate \<Gamma> L C \<delta>)"
    by (simp_all add: regular_state_def)
  show ?thesis
    unfolding regular_state_def
  proof (intro conjI exI)
    show "sound_state N S2"
      by (rule skip_sound_state[OF step sound_S1])
  next
    show "S2 = (\<Gamma>, U, Some (D, \<sigma>))"
      using skipI by simp
  next
    show "trail_almost_no_conflict (N \<union> U) \<Gamma>"
      using tr_almost_no_conf
      by (simp add: trail_almost_no_conflict_def)
  qed
qed

lemma factorize_regular_state:
  assumes step: "factorize N S1 S2" and "regular_state N S1"
  shows "regular_state N S2"
  using step
proof (cases N S1 S2 rule: factorize.cases)
  case (factorizeI L \<sigma> L' \<mu> \<sigma>' D \<Gamma> U)
  with \<open>regular_state N S1\<close> have
    sound_S1: "sound_state N S1" and
    tr_almost_no_conf: "trail_almost_no_conflict (N \<union> U) \<Gamma>"
    by (simp_all add: regular_state_def)
  show ?thesis
    unfolding regular_state_def
  proof (intro conjI exI)
    show "sound_state N S2"
      by (rule factorize_sound_state[OF step sound_S1])
  next
    show "S2 = (\<Gamma>, U, Some ((D + {#L#}) \<cdot> \<mu>, \<sigma>'))"
      using factorizeI by simp
  next
    show "trail_almost_no_conflict (N \<union> U) \<Gamma>"
      by (rule tr_almost_no_conf)
  qed
qed

lemma resolve_regular_state:
  fixes N :: "('f, 'v) term clause set"
  assumes step: "resolve N S1 S2" and "regular_state N S1"
  shows "regular_state N S2"
  using step
proof (cases N S1 S2 rule: resolve.cases)
  case (resolveI \<Gamma> \<Gamma>' L C \<delta> D \<sigma> \<rho> U L' \<mu>)
  with \<open>regular_state N S1\<close> have
    sound_S1: "sound_state N S1" and
    tr_almost_no_conf: "trail_almost_no_conflict (N \<union> U) \<Gamma>"
    by (simp_all add: regular_state_def)

  let ?\<gamma> = "restrict_subst (vars_cls ((D + C) \<cdot> \<mu> \<cdot> \<rho>)) (inv_renaming' \<rho> \<odot> \<sigma> \<odot> \<delta>)"

  show ?thesis
    unfolding regular_state_def
  proof (intro conjI exI)
    show "sound_state N S2"
      by (rule resolve_sound_state[OF step sound_S1])
  next
    show "S2 = (\<Gamma>, U, Some ((D + C) \<cdot> \<mu> \<cdot> \<rho>, ?\<gamma>))"
      using resolveI by simp
  next
    from sound_S1 have "sound_trail N U \<Gamma>"
      using resolveI by (simp add: sound_state_def)
    then obtain CC :: "('f, 'v) term clause" and \<rho>\<^sub>C\<^sub>C :: "('f, 'v) subst" where
      CC_in: "CC \<in> N \<union> U" and
      "is_renaming \<rho>\<^sub>C\<^sub>C" and
      "add_mset L C = CC \<cdot> \<rho>\<^sub>C\<^sub>C"
      using resolveI unfolding sound_trail.simps[of N U \<Gamma>]
      by (auto simp: trail_propagate_def)

    show "trail_almost_no_conflict (N \<union> U) \<Gamma>"
      by (rule tr_almost_no_conf)
  qed
qed

lemma trail_backtrack_decide_Suc_level[simp]:
  "trail_backtrack (trail_decide \<Gamma> L) (Suc (trail_level \<Gamma>)) = trail_decide \<Gamma> L"
  by (smt (verit, best) id_def n_not_Suc_n trail_backtrack.simps(2) trail_decide_def
      trail_level.simps(2) trail_level_decide)

lemma finite_Union_iff: "finite (\<Union> S) \<longleftrightarrow> finite S \<and> (\<forall>s \<in> S. finite s)"
  by (meson Union_upper finite_Union finite_UnionD finite_subset)

lemma trail_no_conflict_if_not_conflict_and_sound:
  fixes N :: "('f, 'v) term clause set"
  assumes "sound_state N S1"
  shows "(\<nexists>S2. conflict N S1 S2) \<Longrightarrow> state_conflict S1 = None \<Longrightarrow>
    trail_no_conflict (N \<union> state_learned S1) (state_trail S1)"
proof (erule contrapos_np)
  assume "state_conflict S1 = None"
  then obtain \<Gamma> :: "('f, 'v) trail" and U :: "('f, 'v) term clause set" where
    S1_def: "S1 = (\<Gamma>, U, None)"
    by (metis prod.collapse state_conflict_def)
  with \<open>sound_state N S1\<close> have "finite N" and "finite U"
    unfolding sound_state_def by simp_all

  assume "\<not> trail_no_conflict (N \<union> state_learned S1) (state_trail S1)"
  then obtain C :: "('f, 'v) term clause" and \<gamma> :: "('f, 'v) subst" where
    "C \<in> N \<union> U" and "trail_false_cls \<Gamma> (C \<cdot> \<gamma>)"
    by (auto simp: S1_def trail_no_conflict_def)

  define \<rho>_vars :: "'v \<Rightarrow> 'v" where
    "\<rho>_vars = renaming_vars (\<Union> (vars_cls ` (N \<union> U \<union> clss_of_trail \<Gamma>)))"

  have "inj \<rho>_vars"
    unfolding \<rho>_vars_def
  proof (rule inj_renaming)
    show "finite (\<Union> (vars_cls ` (N \<union> U \<union> clss_of_trail \<Gamma>)))"
      using \<open>finite N\<close> \<open>finite U\<close> by simp
  qed

  define C' :: "('f, 'v) term clause" where
    "C' = C \<cdot> (Var \<circ> \<rho>_vars)"
  define \<gamma>' :: "('f, 'v) subst" where
    "\<gamma>' = (\<lambda>x. if x \<in> \<rho>_vars ` vars_cls C then \<gamma> (the_inv \<rho>_vars x) else Var x)"

  have "C \<cdot> ((Var \<circ> \<rho>_vars) \<odot> \<gamma>') = C \<cdot> \<gamma>"
    by (rule same_on_vars_clause) (simp add: subst_compose_def \<gamma>'_def \<open>inj \<rho>_vars\<close> the_inv_f_f)
  hence "C' \<cdot> \<gamma>' = C \<cdot> \<gamma>"
    unfolding C'_def by simp

  show "\<exists>S2. conflict N S1 S2"
  proof (rule exI)
    show "conflict N S1 (\<Gamma>, U, Some (C', \<gamma>'))"
      unfolding S1_def
    proof (rule conflictI)
      show "C \<in> N \<union> U"
        by (rule \<open>C \<in> N \<union> U\<close>)
    next
      show "C' = rename_clause (N \<union> U \<union> clss_of_trail \<Gamma>) C"
        unfolding C'_def rename_clause_def \<rho>_vars_def by (rule refl)
    next
      have "renaming_vars (\<Union>(vars_cls ` (N \<union> U \<union> clss_of_trail \<Gamma>))) x \<noteq> x" for x
        by (simp add: \<open>finite N\<close> \<open>finite U\<close> renaming_all)
      hence "renaming_wrt (N \<union> U \<union> clss_of_trail \<Gamma>) x \<noteq> Var x" for x
        by simp
      hence "subst_domain (Var \<circ> \<rho>_vars) = UNIV"
        unfolding \<rho>_vars_def subst_domain_def by simp
      hence "vars_cls (C \<cdot> (Var \<circ> \<rho>_vars)) = \<rho>_vars ` vars_cls C"
        unfolding vars_subst_cls_eq by auto
      thus "subst_domain \<gamma>' \<subseteq> vars_cls C'"
        unfolding \<gamma>'_def C'_def by (smt (verit, best) mem_Collect_eq subsetI subst_domain_def)
    next
      from \<open>sound_state N S1\<close> have "sound_trail N U \<Gamma>"
        unfolding sound_state_def S1_def by simp
      hence "\<forall>L \<in> fst ` set \<Gamma>. is_ground_lit L"
        by (rule ball_ground_lit_if_sound_trail)
      hence "is_ground_cls (C \<cdot> \<gamma>)"
        unfolding is_ground_cls_def
        apply (intro allI impI)
        apply (drule \<open>trail_false_cls \<Gamma> (C \<cdot> \<gamma>)\<close>[unfolded trail_false_cls_def, rule_format])
        unfolding trail_false_lit_def is_ground_lit_def
        by (metis atm_of_uminus)
      thus "is_ground_cls (C' \<cdot> \<gamma>')"
        using \<open>C' \<cdot> \<gamma>' = C \<cdot> \<gamma>\<close> by simp
    next
      show "trail_false_cls \<Gamma> (C' \<cdot> \<gamma>')"
        using \<open>trail_false_cls \<Gamma> (C \<cdot> \<gamma>)\<close> \<open>C' \<cdot> \<gamma>' = C \<cdot> \<gamma>\<close> by simp
    qed
  qed
qed



lemma decide_regular_state:
  assumes step: "decide N S1 S2" and no_conflict: "\<nexists>S3. conflict N S2 S3" and "regular_state N S1"
  shows "regular_state N S2"
  using step
proof (cases N S1 S2 rule: decide.cases)
  case (decideI L \<Gamma> U)
  with \<open>regular_state N S1\<close> have
    sound_S1: "sound_state N S1" and
    tr_almost_no_conf: "trail_almost_no_conflict (N \<union> U) \<Gamma>"
    by (simp_all add: regular_state_def)

  have sound_S2: "sound_state N S2"
      by (rule decide_sound_state[OF step sound_S1])

  show ?thesis
    unfolding regular_state_def
  proof (intro conjI exI)
    show "sound_state N S2"
      by (rule sound_S2)
  next
    show "S2 = (trail_decide \<Gamma> L, U, None)"
      using decideI by simp
  next
    have "trail_no_conflict (N \<union> state_learned S2) (state_trail S2)"
      by (rule trail_no_conflict_if_not_conflict_and_sound[OF sound_S2 no_conflict])
        (use decideI in simp)
    thus "trail_almost_no_conflict (N \<union> U) (trail_decide \<Gamma> L)"
      using decideI by (simp add: trail_almost_no_conflict_if_trail_no_conflict)
  qed
qed

lemma trail_backtrack_0[simp]: "trail_backtrack \<Gamma> 0 = []"
  by (induction \<Gamma>) simp_all

lemma suffix_trail_backtrack_backtrack_if_le:
  "m \<le> n \<Longrightarrow> n \<le> trail_level \<Gamma> \<Longrightarrow> suffix (trail_backtrack \<Gamma> m) (trail_backtrack \<Gamma> n)"
  unfolding suffix_def
proof (induction \<Gamma> arbitrary: m n)
  case Nil
  show ?case by simp
next
  case (Cons Ln \<Gamma>)
  thus ?case
    by (smt (verit, del_insts) id_apply le_antisym not_less_eq_eq suffix_def
        trail_backtrack.simps(2) trail_backtrack_suffix trail_level.simps(2))
qed

lemma trail_no_conflict_backtrack_if_no_conflict_backtrack_le:
  assumes "m \<le> n" and "n \<le> trail_level \<Gamma>"
  shows "trail_no_conflict N (trail_backtrack \<Gamma> n) \<Longrightarrow> trail_no_conflict N (trail_backtrack \<Gamma> m)"
  unfolding trail_no_conflict_def
  using suffix_trail_backtrack_backtrack_if_le[OF assms, THEN trail_false_cls_if_suffix_and_false]
  by blast

lemma not_trail_false_cls_if_not_trail_defined_lit:
  "\<not> trail_defined_lit \<Gamma> L \<Longrightarrow> L \<in># C \<Longrightarrow> \<not> trail_false_cls \<Gamma> C"
  using trail_defined_lit_iff_true_or_false trail_false_cls_def by blast

lemma "0 < trail_level_lit \<Gamma> L \<Longrightarrow> \<exists>n < length \<Gamma>. fst (\<Gamma> ! n) = L \<or> fst (\<Gamma> ! n) = - L"
proof (induction \<Gamma>)
  case Nil
  then show ?case by simp
next
  case (Cons Ln \<Gamma>)
  show ?case
  proof (cases "fst Ln = L \<or> fst Ln = - L")
    case True
    thus ?thesis by auto
  next
    case False
    with Cons show ?thesis by auto
  qed
qed

lemma backtrack_regular_state:
  assumes step: "backtrack N S1 S2" and regular_S1: "regular_state N S1"
  shows "regular_state N S2"
  using step
proof (cases N S1 S2 rule: backtrack.cases)
  case (backtrackI \<Gamma> D \<sigma> L U)
  with regular_S1 have
    sound_S1: "sound_state N S1" and
    tr_almost_no_conf: "trail_almost_no_conflict (N \<union> U) \<Gamma>"
    by (simp_all add: regular_state_def)

  have sound_S2: "sound_state N S2"
    by (rule backtrack_sound_state[OF step sound_S1])

  show ?thesis
    unfolding regular_state_def
  proof (intro conjI exI)
    show "sound_state N S2"
      by (rule sound_S2)
  next
    show "S2 = (trail_backtrack \<Gamma> (trail_level_cls \<Gamma> (D \<cdot> \<sigma>)), U \<union> {D + {#L#}}, None)"
      using backtrackI by simp
  next
    have "trail_no_conflict (N \<union> U) (trail_backtrack \<Gamma> (trail_level_cls \<Gamma> (D \<cdot> \<sigma>)))"
    proof (rule trail_no_conflict_backtrack_if_no_conflict_backtrack_le)
      show "trail_no_conflict (N \<union> U) (trail_backtrack \<Gamma> (trail_level \<Gamma>))"
        by (rule tr_almost_no_conf[unfolded trail_almost_no_conflict_def])
    next
      show "trail_level_cls \<Gamma> (D \<cdot> \<sigma>) \<le> trail_level \<Gamma>"
        by (rule trail_level_cls_le)
    next
      show "trail_level \<Gamma> \<le> trail_level \<Gamma>"
        by (rule Nat.le_refl)
    qed
    moreover have "trail_no_conflict {D + {#L#}} (trail_backtrack \<Gamma> (trail_level_cls \<Gamma> (D \<cdot> \<sigma>)))"
    proof -
      from sound_S1 have sound_\<Gamma>: "sound_trail N U \<Gamma>"
        using backtrackI by (simp add: sound_state_def)
      hence "\<not> trail_defined_lit (trail_backtrack \<Gamma> (trail_level_cls \<Gamma> (D \<cdot> \<sigma>))) (L \<cdot>l \<sigma>)"
        by (rule not_trail_defined_lit_backtrack_if_level_lit_gt_level_backtrack)
          (use backtrackI in simp_all)
      then show ?thesis
        unfolding trail_no_conflict_def
        apply simp
        using not_trail_false_cls_if_not_trail_defined_lit
        sorry
    qed
    ultimately show "trail_almost_no_conflict (N \<union> (U \<union> {D + {#L#}}))
      (trail_backtrack \<Gamma> (trail_level_cls \<Gamma> (D \<cdot> \<sigma>)))"
      using trail_almost_no_conflict_if_trail_no_conflict trail_no_conflict_union_iff
      by metis
  qed
qed

lemma regular_scl_preserves_regularity:
  assumes
    regular_step: "regular_scl N S1 S2" and
    regular_S1: "regular_state N S1"
  shows "regular_state N S2"
  using regular_step unfolding regular_scl_def
proof (elim disjE conjE)
  show "conflict N S1 S2 \<Longrightarrow> ?thesis"
    by (rule conflict_regular_state[OF _ regular_S1])
next
  from regular_S1 have
    sound_S1: "sound_state N S1" and
    almost_no_conf_S1: "trail_almost_no_conflict (N \<union> state_learned S1) (state_trail S1)"
    unfolding regular_state_def by auto
  from regular_step sound_S1 have sound_S2: "sound_state N S2"
    by (rule regular_scl_sound_state)

  assume "\<not> conflict N S1 S2" and "reasonable_scl N S1 S2"
  thus ?thesis
    unfolding reasonable_scl_def scl_def
  proof (elim disjE conjE)
    show "propagate N S1 S2 \<Longrightarrow> ?thesis"
      by (rule propagate_regular_state[OF _ regular_S1])
  next
    assume "decide N S1 S2" and "decide N S1 S2 \<longrightarrow> \<not> Ex (conflict N S2)"
    thus ?thesis
      using decide_regular_state[OF _ _ regular_S1] by simp
  next
    assume "\<not> conflict N S1 S2" and "conflict N S1 S2"
    hence False by simp
    thus ?thesis ..
  next
    show "skip N S1 S2 \<Longrightarrow> ?thesis"
      by (rule skip_regular_state[OF _ regular_S1])
  next
    show "factorize N S1 S2 \<Longrightarrow> ?thesis"
      by (rule factorize_regular_state[OF _ regular_S1])
  next
    show "resolve N S1 S2 \<Longrightarrow> ?thesis"
      by (rule resolve_regular_state[OF _ regular_S1])
  next
    show "backtrack N S1 S2 \<Longrightarrow> ?thesis"
      (* This depends on a sorry! *)
      by (rule backtrack_regular_state[OF _ regular_S1])
  qed
qed

(* lemma propagate_or_backtrack_before_regular_conflict:
  assumes
    fin_N: "finite N" and disj_vars_N: "disjoint_vars_set N" and
    regular_run: "(regular_scl N)\<^sup>*\<^sup>* initial_state S0" and
    regular_step: "regular_scl N S0 S1" and
    conflict: "conflict N S1 S2"
  shows "propagate N S0 S1 \<or> backtrack N S0 S1"
proof -
  from conflict obtain \<Gamma> U C \<gamma> where
    S1_def: "S1 = (\<Gamma>, U, None)" and
    S2_def: "S2 = (\<Gamma>, U, Some (C, \<gamma>))"
    unfolding conflict.simps by auto

  with regular_step have "\<not> conflict N S0 S1" and "reasonable_scl N S0 S1"
    unfolding regular_scl_def by (simp_all add: conflict.simps)

  with conflict have "scl N S0 S1" and "\<not> decide N S0 S1"
    unfolding reasonable_scl_def by blast+

  thus ?thesis
    unfolding scl_def
    by (simp add: S1_def skip.simps conflict.simps factorize.simps resolve.simps)
qed *)

lemma
  assumes
    fin_N: "finite N" and disj_vars_N: "disjoint_vars_set N" and
    regular_run: "(regular_scl N)\<^sup>*\<^sup>* initial_state S1" and
    conflict: "conflict N S1 S2"
  shows "S1 = initial_state \<and> {#} \<in> N \<or>
    (\<exists>S0. (regular_scl N)\<^sup>*\<^sup>* initial_state S0 \<and> (propagate N S0 S1 \<or> backtrack N S0 S1))"
  (is "?lhs \<or> ?rhs")
  using regular_run conflict
proof (induction rule: rtranclp_induct)
  case base
  hence "{#} \<in> N"
    apply (cases rule: conflict.cases)
    apply simp
    by (metis ex_inv_rename_clause fin_N not_trail_false_Nil(2) subst_cls_empty_iff)
  thus ?case
    by simp
next
  case (step S0 S1)

  from step.prems obtain \<Gamma> U C \<gamma> where
    S1_def: "S1 = (\<Gamma>, U, None)" and
    S2_def: "S2 = (\<Gamma>, U, Some (C, \<gamma>))"
    unfolding conflict.simps by auto
  with step.hyps have "\<not> conflict N S0 S1" and "reasonable_scl N S0 S1"
    unfolding regular_scl_def by (simp_all add: conflict.simps)
  with step.prems have "scl N S0 S1" and "\<not> decide N S0 S1"
    unfolding reasonable_scl_def by blast+
  with step.hyps(1) show ?case
    apply - apply (rule disjI2)
    unfolding scl_def
    apply (simp add: S1_def skip.simps conflict.simps factorize.simps resolve.simps)
    by (metis prod_cases3)
qed
  

lemma
  assumes
    fin_N: "finite N" and disj_vars_N: "disjoint_vars_set N" and
    regular_run: "(regular_scl N)\<^sup>*\<^sup>* initial_state S0" and
    conflict: "conflict N S0 S1" and
    resolution: "(\<lambda>S S'. skip N S S' \<or> factorize N S S' \<or> resolve N S S')\<^sup>+\<^sup>+ S1 Sn" and
    backtrack: "backtrack N Sn Sn'" and
    "transp lt" and
    total_on_ground_lt: "Restricted_Predicates.total_on lt {L. is_ground_lit L}"
  shows "(regular_scl N)\<^sup>*\<^sup>* initial_state Sn' \<and>
    (\<exists>C \<gamma>. state_conflict Sn = Some (C, \<gamma>) \<and>
      \<not> redundant (multp (trail_less_ex lt (map fst (state_trail S1)))) (N \<union> U) C)"
proof -
  from regular_run conflict have "(regular_scl N)\<^sup>*\<^sup>* initial_state S1"
    by (meson regular_scl_def rtranclp.simps)
  also from resolution have "(regular_scl N)\<^sup>*\<^sup>* ... Sn"
    using regular_run_if_skip_factorize_resolve_run tranclp_into_rtranclp by fast
  also from backtrack have "(regular_scl N)\<^sup>*\<^sup>* ... Sn'"
    by (auto simp add: scl_def reasonable_scl_def regular_scl_def backtrack_well_defined)
  finally have "(regular_scl N)\<^sup>*\<^sup>* initial_state Sn'" by assumption

  from conflict obtain C1 \<gamma>1 where conflict_S1: "state_conflict S1 = Some (C1, \<gamma>1)"
    by (smt (verit, best) conflict.simps state_conflict_simp)
  then obtain Cn \<gamma>n where conflict_Sn: "state_conflict Sn = Some (Cn, \<gamma>n)"
    by (smt (verit) backtrack.simps backtrack state_conflict_simp)

  from fin_N disj_vars_N have "sound_state N initial_state"
    by (rule sound_initial_state)
  with regular_run have "sound_state N S0"
    by (simp add: regular_run_sound_state)
  with conflict have sound_S1: "sound_state N S1"
    by (simp add: conflict_sound_state)
  with resolution have sound_Sn: "sound_state N Sn"
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
      assume "skip N S1 S2"
      thus ?thesis
        using trail_false_conflict_after_skip[OF conflict_S1 trail_S1_false_C1_\<gamma>1]
        by (smt (verit) skip.simps state_trail_simp suffix_trail_propagate)
    next
      assume "factorize N S1 S2"
      moreover with sound_S1 have "sound_state N S2"
        by (auto intro: factorize_sound_state)
      ultimately show ?thesis
        by (cases N S1 S2 rule: factorize.cases) (simp add: sound_state_def)
    next
      assume "resolve N S1 S2"
      moreover with sound_S1 have "sound_state N S2"
        by (auto intro: resolve_sound_state)
      ultimately show ?thesis
        by (cases N S1 S2 rule: resolve.cases) (simp add: sound_state_def)
    qed
  next
    case (step Sm Sm')
    from step.hyps(2) have "suffix (state_trail Sm') (state_trail Sm)"
      by (auto dest: strict_suffix_trail_if_skip eq_trail_if_factorize eq_trail_if_resolve)
    with step.IH have "suffix (state_trail Sm') (state_trail S1)"
      by force

    from step.hyps(1) sound_S1 have sound_Sm: "sound_state N Sm"
      by (induction rule: tranclp_induct)
        (auto intro: skip_sound_state factorize_sound_state resolve_sound_state)

    from step.IH obtain Cm \<gamma>m where
      conflict_Sm: "state_conflict Sm = Some (Cm, \<gamma>m)" and
      trail_false_Cm_\<gamma>m: "trail_false_cls (state_trail S1) (Cm \<cdot> \<gamma>m)"
      using step.prems step.hyps(2) \<open>suffix (state_trail Sm') (state_trail Sm)\<close>
      by auto

    from step.hyps(2) show ?case
    proof (elim disjE)
      assume "skip N Sm Sm'"
      thus ?thesis
        using \<open>suffix (state_trail Sm') (state_trail S1)\<close>
        using trail_false_conflict_after_skip trail_false_Cm_\<gamma>m conflict_Sm
        by (smt (verit) skip.cases state_conflict_simp)
    next
      assume "factorize N Sm Sm'"
      thus ?thesis
      proof (cases N Sm Sm' rule: factorize.cases)
        case (factorizeI L \<sigma> L' \<mu> \<sigma>' D \<Gamma> U)
        with conflict_Sm have Cm_def: "Cm = D + {#L, L'#}" and \<gamma>m_def: "\<gamma>m = \<sigma>"
          by simp_all
        with factorizeI(3,4) have "trail_false_cls (state_trail S1) ((D + {#L#}) \<cdot> \<mu> \<cdot> \<sigma>)"
          using trail_false_Cm_\<gamma>m trail_false_cls_subst_mgu_before_grounding
          by (smt (verit, best) CollectI mgu_sound prod.sel singletonD atm_of_subst_lit
              unifiers_def)
        with factorizeI(5) have "trail_false_cls (state_trail S1) ((D + {#L#}) \<cdot> \<mu> \<cdot> \<sigma>')"
          by (metis subsetI subst_cls_restrict_subst_idem)
        with factorizeI(2) show ?thesis
          using \<open>suffix (state_trail Sm') (state_trail S1)\<close>
          using state_conflict_simp by blast
      qed
    next
      assume "resolve N Sm Sm'"
      thus ?thesis
      proof (cases N Sm Sm' rule: resolve.cases)
        case (resolveI \<Gamma> \<Gamma>' L C \<delta> D \<sigma> \<rho> U L' \<mu>)
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

        from resolveI(6) have "atm_of (L \<cdot>l \<delta>) = atm_of (L' \<cdot>l \<sigma>)" by simp
        hence "(atm_of L) \<cdot>a \<delta> = (atm_of L') \<cdot>a \<sigma>" by simp

        have \<sigma>_\<delta>_in_unif: "\<sigma> \<odot> \<delta> \<in> unifiers {(atm_of L, atm_of L')}"
        proof (rule subst_comp_in_unifiersI')
          show "atm_of L \<cdot>a \<delta> = atm_of L' \<cdot>a \<sigma>"
            using resolveI(6) by (metis atm_of_eq_uminus_if_lit_eq atm_of_subst_lit)
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
          using trail_false_cls_plus_subst_mgu_before_groundings[
              of "state_trail S1" D L' \<sigma> _ C \<delta> L \<mu>, OF tr_false_D_L'_\<sigma> \<open>trail_false_cls \<Gamma>' (C \<cdot> \<delta>)\<close>
                \<open>suffix \<Gamma>' (state_trail S1)\<close>
                \<open>is_ground_cls ((D + {#L'#}) \<cdot> \<sigma>)\<close>
                \<open>vars_cls (D + {#L'#}) \<inter> vars_cls (C + {#L#}) = {}\<close>
                \<open>subst_domain \<sigma> \<subseteq> vars_cls (D + {#L'#})\<close>
                mgu_sound[OF resolveI(7)] \<sigma>_\<delta>_in_unif]
          by assumption
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

  moreover have "\<not> redundant (multp (trail_less_ex lt (map fst (state_trail S1)))) (N \<union> U) Cn"
  proof (rule notI)
    assume "redundant (multp (trail_less_ex lt (map fst (state_trail S1)))) (N \<union> U) Cn"
    moreover from sound_Sn conflict_Sn have "Cn \<cdot> \<gamma>n \<in> grounding_of_cls Cn"
      unfolding sound_state_def
      using grounding_of_cls_ground grounding_of_subst_cls_subset 
      by fastforce
    ultimately have gr_red_Cn_\<gamma>n: "ground_redundant
      (multp (trail_less_ex lt (map fst (state_trail S1))))
      (grounding_of_clss (N \<union> U)) (Cn \<cdot> \<gamma>n)"
      by (simp add: redundant_def)

    define S where
      "S = {D \<in> grounding_of_clss (N \<union> U).
        (multp (trail_less_ex lt (map fst (state_trail S1))))\<^sup>=\<^sup>= D (Cn \<cdot> \<gamma>n)}"

    from gr_red_Cn_\<gamma>n have "S \<TTurnstile>e {Cn \<cdot> \<gamma>n}"
      unfolding ground_redundant_def S_def by simp

    from sound_S1 have "sound_trail N (state_learned S1) (state_trail S1)"
      by (auto simp add: sound_state_def)

    have "\<forall>L\<in>#Cn \<cdot> \<gamma>n. trail_defined_lit (state_trail S1) L"
      using \<open>trail_false_cls (state_trail S1) (Cn \<cdot> \<gamma>n)\<close> trail_defined_lit_iff_true_or_false
        trail_false_cls_def by blast

    have "\<not> trail_interp (state_trail S1) \<TTurnstile>s {Cn \<cdot> \<gamma>n}"
      apply (rule notI)
      using \<open>trail_false_cls (state_trail S1) (Cn \<cdot> \<gamma>n)\<close>
      apply simp
      unfolding trail_true_cls_iff_trail_interp_entails[OF
          \<open>sound_trail N (state_learned S1) (state_trail S1)\<close>
          \<open>\<forall>L\<in>#Cn \<cdot> \<gamma>n. trail_defined_lit (state_trail S1) L\<close>, symmetric]
      using not_trail_true_and_false_cls[OF \<open>sound_trail N (state_learned S1) (state_trail S1)\<close>]
      by simp

    hence "\<not> trail_interp (state_trail S1) \<TTurnstile>s S"
      using \<open>S \<TTurnstile>e {Cn \<cdot> \<gamma>n}\<close>[rule_format, of "trail_interp (state_trail S1)"]
      by argo

    then obtain D where "D \<in> S" and "\<not> trail_interp (state_trail S1) \<TTurnstile> D"
      by (auto simp: true_clss_def)

    moreover have "trail_defined_cls (state_trail S1) D"
    proof -
      have "trail_defined_cls (state_trail S1) (Cn \<cdot> \<gamma>n)"
        using \<open>\<forall>L\<in>#Cn \<cdot> \<gamma>n. trail_defined_lit (state_trail S1) L\<close> trail_defined_cls_def by blast

      from \<open>D \<in> S\<close> have
        D_in: "D \<in> grounding_of_clss (N \<union> U)" and
        "(multp (trail_less_ex lt (map fst (state_trail S1))))\<^sup>=\<^sup>= D (Cn \<cdot> \<gamma>n)"
        unfolding S_def by simp_all
      then show "trail_defined_cls (state_trail S1) D"
        unfolding Lattices.sup_apply Boolean_Algebras.sup_bool_def
      proof (elim disjE)
        assume multp_D_Cn_\<gamma>n: "multp (trail_less_ex lt (map fst (state_trail S1))) D (Cn \<cdot> \<gamma>n)"
        show "trail_defined_cls (state_trail S1) D"
        proof (rule trail_defined_cls_if_lt_defined)
          show "sound_trail N (state_learned S1) (state_trail S1)"
            by (rule \<open>sound_trail N (state_learned S1) (state_trail S1)\<close>)
        next
          show "multp (trail_less_ex lt (map fst (state_trail S1))) D (Cn \<cdot> \<gamma>n)"
            by (rule multp_D_Cn_\<gamma>n)
        next
          show "trail_defined_cls (state_trail S1) (Cn \<cdot> \<gamma>n)"
            by (rule \<open>trail_defined_cls (state_trail S1) (Cn \<cdot> \<gamma>n)\<close>)
        next
          show "transp lt"
            by (rule \<open>transp lt\<close>)
        next
          have "is_ground_cls D"
            using D_in by (simp add: grounding_ground)
          moreover have "is_ground_cls (Cn \<cdot> \<gamma>n)"
            using \<open>Cn \<cdot> \<gamma>n \<in> grounding_of_cls Cn\<close> is_ground_cls_if_in_grounding_of_cls by blast
          ultimately have "set_mset D \<union> set_mset (Cn \<cdot> \<gamma>n) \<subseteq> {L. is_ground_lit L}"
            using is_ground_cls_imp_is_ground_lit by auto
          thus "Restricted_Predicates.total_on lt (set_mset D \<union> set_mset (Cn \<cdot> \<gamma>n))"
            using total_on_ground_lt
            by (metis le_iff_sup total_on_unionD1)
        qed
      next
        assume "D = Cn \<cdot> \<gamma>n"
        then show "trail_defined_cls (state_trail S1) D"
          using \<open>trail_defined_cls (state_trail S1) (Cn \<cdot> \<gamma>n)\<close> by simp
      qed    
    qed

    then have "trail_false_cls (state_trail S1) D"
      using \<open>\<not> trail_interp (state_trail S1) \<TTurnstile> D\<close>
      by (meson \<open>sound_trail N (state_learned S1) (state_trail S1)\<close> trail_defined_cls_def
          trail_defined_lit_iff_true_or_false trail_false_cls_def
          trail_interp_cls_if_sound_and_trail_true trail_true_cls_def)

    obtain L C \<gamma> where "state_trail S1 = trail_propagate (state_trail S0) L C \<gamma>"
      using regular_run
      using propagate_or_backtrack_before_regular_conflict[OF fin_N  disj_vars_N _ _ conflict]
      sorry

    thus False
      sorry
  qed

  ultimately show ?thesis
    using \<open>(regular_scl N)\<^sup>*\<^sup>* initial_state Sn'\<close>
    by simp
  oops

end

end