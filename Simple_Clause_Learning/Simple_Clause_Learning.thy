theory Simple_Clause_Learning
  imports
    Main
    "HOL-Library.FSet"
    Saturation_Framework.Calculus
    Saturation_Framework_Extensions.Clausal_Calculus
    Ordered_Resolution_Prover.Clausal_Logic
    Ordered_Resolution_Prover.Abstract_Substitution
    Ordered_Resolution_Prover.Herbrand_Interpretation
    First_Order_Terms.Unification
    First_Order_Terms.Subsumption
    Abstract_Renaming_Apart
    Relation_Extra
begin

sledgehammer_params

section \<open>Extra Lemmas\<close>


subsection \<open>Set_Extra\<close>

lemma not_in_iff: "L \<notin> xs \<longleftrightarrow> (\<forall>y\<in>xs. L \<noteq> y)"
  by auto

lemma disjoint_iff': "A \<inter> B = {} \<longleftrightarrow> (\<forall>a \<in> A. a \<notin> B) \<and> (\<forall>b \<in> B. b \<notin> A)"
  by blast

lemma set_filter_insert_conv:
  "{x \<in> insert y S. P x} = (if P y then insert y else id) {x \<in> S. P x}"
  by auto

lemma not_empty_if_mem: "x \<in> X \<Longrightarrow> X \<noteq> {}"
  by blast


subsection \<open>Finite_Set_Extra\<close>

lemma finite_induct' [case_names empty singleton insert_insert, induct set: finite]:
  \<comment> \<open>Discharging \<open>x \<notin> F\<close> entails extra work.\<close>
  assumes "finite F"
  assumes "P {}"
    and singleton: "\<And>x. P {x}"
    and insert_insert: "\<And>x y F. finite F \<Longrightarrow> x \<noteq> y \<Longrightarrow> x \<notin> F \<Longrightarrow> y \<notin> F \<Longrightarrow> P (insert y F) \<Longrightarrow> P (insert x (insert y F))"
  shows "P F"
  using \<open>finite F\<close>
proof induct
  show "P {}" by fact
next
  fix x F
  assume F: "finite F" and P: "P F"
  thus "P (insert x F)"
  proof (induction F rule: finite.induct)
    case emptyI
    show ?case by (rule singleton)
  next
    case (insertI F y)
    show ?case
    proof (cases "x = y")
      case True
      then show ?thesis
        by (simp add: insertI.prems)
    next
      case x_neq_y: False
      show ?thesis
      proof (cases "x \<in> F \<or> y \<in> F")
        case True
        then show ?thesis
          by (metis insertCI insertI.IH insertI.prems insert_absorb)
      next
        case False
        show ?thesis
        proof (rule insert_insert)
          show "finite F" using insertI by simp
        next
          show "x \<noteq> y" by (rule x_neq_y)
        next
          show "x \<notin> F" using False by simp
        next
          show "y \<notin> F" using False by simp
        next
          show "P (insert y F)"
            by (simp add: insertI.prems)
        qed
      qed
    qed
  qed
qed


subsection \<open>Product_Type_Extra\<close>

lemma insert_Times: "insert a A \<times> B = Pair a ` B \<union> A \<times> B"
  by blast

lemma Times_insert: "A \<times> insert b B = (\<lambda>x. (x, b)) ` A \<union> A \<times> B"
  by blast

lemma insert_Times_insert':
  "insert a A \<times> insert b B = insert (a, b) ((Pair a ` B) \<union> ((\<lambda>x. (x, b)) ` A) \<union> (A \<times> B))"
  (is "?lhs = ?rhs")
  unfolding insert_Times_insert by auto


subsection \<open>List_Extra\<close>

lemma lt_lengthD:
  assumes i_lt_xs: "i < length xs"
  shows "\<exists>xs1 xi xs2. xs = xs1 @ xi # xs2 \<and> length xs1 = i"
  using assms
  by (metis Cons_nth_drop_Suc add_diff_cancel_left' add_diff_cancel_right'
      canonically_ordered_monoid_add_class.lessE id_take_nth_drop length_append length_drop)

lemma lt_lt_lengthD:
  assumes i_lt_xs: "i < length xs" and j_lt_xs: "j < length xs" and
    i_lt_j: "i < j"
  shows "\<exists>xs1 xi xs2 xj xs3. xs = xs1 @ xi # xs2 @ xj # xs3 \<and> length xs1 = i \<and>
    length (xs1 @ xi # xs2) = j"
proof -
  from i_lt_xs obtain xs1 xi xs' where "xs = xs1 @ xi # xs'" and "length xs1 = i"
    using lt_lengthD by blast
  with j_lt_xs obtain xs2 xj xs3 where "xs = xs1 @ xi # xs2 @ xj # xs3" and "length (xs1 @ xi # xs2) = j"
    using lt_lengthD
    by (smt (verit, del_insts) append.assoc append_Cons append_eq_append_conv i_lt_j list.inject)
  thus ?thesis
    using \<open>length xs1 = i\<close> by blast
qed


subsection \<open>Sublist_Extra\<close>

lemma not_mem_strict_suffix:
  shows "strict_suffix xs (y # ys) \<Longrightarrow> y \<notin> set ys \<Longrightarrow> y \<notin> set xs"
  unfolding strict_suffix_def suffix_def
  by (metis Cons_eq_append_conv Un_iff set_append)

lemma not_mem_strict_suffix':
  shows "strict_suffix xs (y # ys) \<Longrightarrow> f y \<notin> f ` set ys \<Longrightarrow> f y \<notin> f ` set xs"
  using not_mem_strict_suffix[of "map f xs" "f y" "map f ys", unfolded list.set_map]
  using map_mono_strict_suffix[of _ "_ # _", unfolded list.map]
  by fast


subsection \<open>Multiset_Extra\<close>

lemma multp\<^sub>D\<^sub>M_implies_one_step:
  "multp\<^sub>D\<^sub>M R M N \<Longrightarrow> \<exists>I J K. N = I + J \<and> M = I + K \<and> J \<noteq> {#} \<and> (\<forall>k\<in>#K. \<exists>x\<in>#J. R k x)"
  unfolding multp\<^sub>D\<^sub>M_def
  by (metis subset_mset.le_imp_diff_is_add)

lemma multp\<^sub>H\<^sub>O_implies_one_step:
  "multp\<^sub>H\<^sub>O R M N \<Longrightarrow> \<exists>I J K. N = I + J \<and> M = I + K \<and> J \<noteq> {#} \<and> (\<forall>k\<in>#K. \<exists>x\<in>#J. R k x)"
  by (metis multp\<^sub>D\<^sub>M_implies_one_step multp\<^sub>H\<^sub>O_imp_multp\<^sub>D\<^sub>M)

lemma multp\<^sub>D\<^sub>M_mono_strong:
  "multp\<^sub>D\<^sub>M R M1 M2 \<Longrightarrow> (\<And>x y. x \<in># M1 \<Longrightarrow> y \<in># M2 \<Longrightarrow> R x y \<Longrightarrow> S x y) \<Longrightarrow> multp\<^sub>D\<^sub>M S M1 M2"
  unfolding multp\<^sub>D\<^sub>M_def
  by (metis add_diff_cancel_left' in_diffD subset_mset.diff_add)

lemma multp\<^sub>H\<^sub>O_mono_strong:
  "multp\<^sub>H\<^sub>O R M1 M2 \<Longrightarrow> (\<And>x y. x \<in># M1 \<Longrightarrow> y \<in># M2 \<Longrightarrow> R x y \<Longrightarrow> S x y) \<Longrightarrow> multp\<^sub>H\<^sub>O S M1 M2"
  unfolding multp\<^sub>H\<^sub>O_def
  by (metis count_inI less_zeroE)

lemma strict_subset_implies_multp\<^sub>D\<^sub>M: "A \<subset># B \<Longrightarrow> multp\<^sub>D\<^sub>M r A B"
  unfolding multp\<^sub>D\<^sub>M_def
  by (metis add.right_neutral add_diff_cancel_right' empty_iff mset_subset_eq_add_right
      set_mset_empty subset_mset.lessE)

lemma strict_subset_implies_multp\<^sub>H\<^sub>O: "A \<subset># B \<Longrightarrow> multp\<^sub>H\<^sub>O r A B"
  unfolding multp\<^sub>H\<^sub>O_def
  by (simp add: leD mset_subset_eq_count)

lemma Multiset_Bex_plus_iff: "(\<exists>x \<in># (M1 + M2). P x) \<longleftrightarrow> (\<exists>x \<in># M1. P x) \<or> (\<exists>x \<in># M2. P x)"
  by auto

lemma multp_singleton_rightD:
  assumes "multp R M {#x#}" and "transp R"
  shows "y \<in># M \<Longrightarrow> R y x"
  using multp_implies_one_step[OF \<open>transp R\<close> \<open>multp R M {#x#}\<close>]
  by (metis add_cancel_left_left set_mset_single single_is_union singletonD)


subsubsection \<open>Calculus_Extra\<close>

lemma (in consequence_relation) entails_one_formula: "N \<Turnstile> U \<Longrightarrow> D \<in> U \<Longrightarrow> N \<Turnstile> {D}"
  using entail_set_all_formulas by blast


subsection \<open>Abstract_Substitution_Extra\<close>

lemma (in substitution_ops) subst_atm_of_eqI:
  "L \<cdot>l \<sigma>\<^sub>L = K \<cdot>l \<sigma>\<^sub>K \<Longrightarrow> atm_of L \<cdot>a \<sigma>\<^sub>L = atm_of K \<cdot>a \<sigma>\<^sub>K"
  by (cases L; cases K) (simp_all add: subst_lit_def)

lemma (in substitution_ops) subst_atm_of_eq_compI:
  "L \<cdot>l \<sigma> = - (L' \<cdot>l \<sigma>) \<Longrightarrow> atm_of L \<cdot>a \<sigma> = atm_of L' \<cdot>a \<sigma>"
  by (cases L; cases L') (simp_all add: uminus_literal_def subst_lit_def)

lemma (in substitution_ops) set_mset_subst_cls_conv: "set_mset (C \<cdot> \<sigma>) = (\<lambda>L. L \<cdot>l \<sigma>) ` set_mset C"
  by (simp add: subst_cls_def)


subsection \<open>Clausal_Calculus_Extra\<close>


subsubsection \<open>Clausal_Calculus Only\<close>

lemma true_cls_iff_set_mset_eq: "set_mset C = set_mset D \<Longrightarrow> I \<TTurnstile> C \<longleftrightarrow> I \<TTurnstile> D"
  by (simp add: true_cls_def)

lemma true_clss_if_set_mset_eq: "(\<forall>D \<in> \<D>. \<exists>C \<in> \<C>. set_mset D = set_mset C) \<Longrightarrow> I \<TTurnstile>s \<C> \<Longrightarrow> I \<TTurnstile>s \<D>"
  using true_cls_iff_set_mset_eq by (metis true_clss_def)

lemma entails_clss_insert: "N \<TTurnstile>e insert C U \<longleftrightarrow> N \<TTurnstile>e {C} \<and> N \<TTurnstile>e U"
  by auto

lemma Collect_lits_from_atms_conv: "{L. P (atm_of L)} = (\<Union>x \<in> {x. P x}. {Pos x, Neg x})"
  (is "?lhs = ?rhs")
proof (rule Set.equalityI; rule Set.subsetI)
  fix L
  show "L \<in> ?lhs \<Longrightarrow> L \<in> ?rhs"
    by (cases L) simp_all
next
  fix L
  show "L \<in> ?rhs \<Longrightarrow> L \<in> ?lhs"
    by auto
qed


subsubsection \<open>Clausal_Calculus and Abstract_Substitution\<close>

lemma (in substitution) is_ground_lit_Pos[simp]: "is_ground_atm atm \<Longrightarrow> is_ground_lit (Pos atm)"
  by (simp add: is_ground_lit_def)

lemma (in substitution) is_ground_lit_Neg[simp]: "is_ground_atm atm \<Longrightarrow> is_ground_lit (Neg atm)"
  by (simp add: is_ground_lit_def)


subsection \<open>First_Order_Terms Extra\<close>


subsubsection \<open>First_Order_Terms Only\<close>

lemma atm_of_eq_uminus_if_lit_eq: "L = - K \<Longrightarrow> atm_of L = atm_of K"
  by (cases L; cases K) simp_all

lemma subst_subst_eq_subst_subst_if_subst_eq_substI:
  assumes "t \<cdot> \<sigma> = u \<cdot> \<delta>" and
    t_inter_\<delta>_empty: "vars_term t \<inter> subst_domain \<delta> = {}" and
    u_inter_\<sigma>_empty: "vars_term u \<inter> subst_domain \<sigma> = {}"
  shows
    "range_vars \<sigma> \<inter> subst_domain \<delta> = {} \<Longrightarrow> t \<cdot> \<sigma> \<cdot> \<delta> = u \<cdot> \<sigma> \<cdot> \<delta>"
    "range_vars \<delta> \<inter> subst_domain \<sigma> = {} \<Longrightarrow> t \<cdot> \<delta> \<cdot> \<sigma> = u \<cdot> \<delta> \<cdot> \<sigma>"
proof -
  from u_inter_\<sigma>_empty have "u \<cdot> \<sigma> \<cdot> \<delta> = u \<cdot> \<delta>"
    by (simp add: subst_apply_term_ident)
  with \<open>t \<cdot> \<sigma> = u \<cdot> \<delta>\<close> show "range_vars \<sigma> \<inter> subst_domain \<delta> = {} \<Longrightarrow> t \<cdot> \<sigma> \<cdot> \<delta> = u \<cdot> \<sigma> \<cdot> \<delta>"
    unfolding subst_apply_term_subst_apply_term_eq_subst_apply_term_lhs[OF _ t_inter_\<delta>_empty]
    by simp

  from t_inter_\<delta>_empty have "t \<cdot> \<delta> \<cdot> \<sigma> = t \<cdot> \<sigma>"
    by (simp add: subst_apply_term_ident)
  with \<open>t \<cdot> \<sigma> = u \<cdot> \<delta>\<close> show "range_vars \<delta> \<inter> subst_domain \<sigma> = {} \<Longrightarrow> t \<cdot> \<delta> \<cdot> \<sigma> = u \<cdot> \<delta> \<cdot> \<sigma>"
    unfolding subst_apply_term_subst_apply_term_eq_subst_apply_term_lhs[OF _ u_inter_\<sigma>_empty]
    by simp
qed

lemma subst_compose_in_unifiersI:
  assumes "t \<cdot> \<sigma> = u \<cdot> \<delta>" and
    "vars_term t \<inter> subst_domain \<delta> = {}" and
    "vars_term u \<inter> subst_domain \<sigma> = {}"
  shows
    "range_vars \<sigma> \<inter> subst_domain \<delta> = {} \<Longrightarrow> \<sigma> \<circ>\<^sub>s \<delta> \<in> unifiers {(t, u)}"
    "range_vars \<delta> \<inter> subst_domain \<sigma> = {} \<Longrightarrow> \<delta> \<circ>\<^sub>s \<sigma> \<in> unifiers {(t, u)}"
  using subst_subst_eq_subst_subst_if_subst_eq_substI(1)[OF assms]
  using subst_subst_eq_subst_subst_if_subst_eq_substI(2)[OF assms]
  by (simp_all add: unifiers_def)

lemma subst_ident_if_not_in_domain: "x \<notin> subst_domain \<mu> \<Longrightarrow> \<mu> x = Var x"
  by (simp add: subst_domain_def)

(* lemma fixes \<upsilon> :: "'a \<Rightarrow> ('b, 'a) Term.term" assumes "\<upsilon> \<in> unifiers E" shows "\<exists>\<mu>. is_mgu \<mu> E"
  unfolding is_mgu_def
proof (rule ccontr)
  assume "\<nexists>\<mu>. \<mu> \<in> unifiers E \<and> (\<forall>\<tau>\<in>unifiers E. \<exists>\<gamma>. \<tau> = \<mu> \<circ>\<^sub>s \<gamma>)"
  fix epred5_5 :: "('b, 'a) Term.term set \<Rightarrow> ('a \<Rightarrow> ('b, 'a) Term.term) \<Rightarrow> ('b, 'a) Term.term set \<Rightarrow> ('a \<Rightarrow> ('b, 'a) Term.term) \<Rightarrow>  ('b, 'a) Term.term set \<Rightarrow> bool"
  have "\<And>(X1 :: 'a \<Rightarrow> ('b, 'a) Term.term) (X2 :: ('b, 'a) Term.term set)
    (X3 :: 'a \<Rightarrow> ('b, 'a) Term.term)  (X4 :: ('b, 'a) Term.term set) (X5 :: ('b, 'a) Term.term set).
    epred5_5 X5 X3 X4 X1 X2 \<longleftrightarrow> \<not> (X3 \<in> X4 \<longrightarrow> True)"
(* thf(c_0_5, plain,
![X1:a > term_b_a, X2:set_a_term_b_a, X3:a > term_b_a, X4:set_a_term_b_a, X5:set_a_term_b_a]:
  (((epred5_5 @ X5 @ X3 @ X4 @ X1 @ X2)<=>
  (~(member_a_term_b_a @ X3 @ X4)=>
    (((insert_a_term_b_a @ X1 @ X2)=(insert_a_term_b_a @ X3 @ X4))<=>
      ((((X1)!=(X3))|(((X2)=(X4))))&
        (((X1)=(X3))|((~((((X2)=(insert_a_term_b_a @ X3 @ X5))&
          (~(member_a_term_b_a @ X3 @ X5)&
          (((X4)=(insert_a_term_b_a @ X1 @ X5))&~(member_a_term_b_a @ X1 @ X5)))))
          |(?[X5:set_a_term_b_a]:($true)))&
      ((((X2)=(insert_a_term_b_a @ X3 @ X5))&
      (~(member_a_term_b_a @ X3 @ X5)&
        (((X4)=(insert_a_term_b_a @ X1 @ X5))&~(member_a_term_b_a @ X1 @ X5))))|
        (?[X5:set_a_term_b_a]:($false)))))))))), introduced(definition)). *)
  show False
  using insert_eq_iff mk_disjoint_insert subst_monoid_mult.mult.right_neutral
  (* sledgehammer [e, slices = 1, dont_minimize, isar_proof, compress = 1, timeout = 30, preplay_timeout = 10, overlord] (insert_eq_iff mk_disjoint_insert subst_monoid_mult.mult.right_neutral) *)
  (* by (metis insert_eq_iff mk_disjoint_insert subst_monoid_mult.mult.right_neutral) *)
  using ex_in_conv insertI1 insert_absorb insert_commute insert_eq_iff insert_iff
    insert_not_empty is_mgu_def mk_disjoint_insert subst_monoid_mult.mult.right_neutral
  (* by (smt (verit) ex_in_conv insertI1 insert_absorb insert_commute insert_eq_iff insert_iff
      insert_not_empty is_mgu_def mk_disjoint_insert subst_monoid_mult.mult.right_neutral) *) *)

lemma "is_renaming (Var(x := Var x'))"
proof (unfold is_renaming_def, intro conjI allI)
  fix y show "is_Var ((Var(x := Var x')) y)"
    by simp
next
  show "inj_on (Var(x := Var x')) (subst_domain (Var(x := Var x')))"
    apply (rule inj_onI)
    apply (simp add: subst_domain_def)
    by presburger
qed

lemma ex_mgu_if_subst_eq_subst_and_disj_vars:
  fixes t u :: "('f, 'v) Term.term" and \<sigma>\<^sub>t \<sigma>\<^sub>u :: "('f, 'v) subst"
  assumes "t \<cdot> \<sigma>\<^sub>t = u \<cdot> \<sigma>\<^sub>u" and "vars_term t \<inter> vars_term u = {}"
  shows "\<exists>\<mu> :: ('f, 'v) subst. Unification.mgu t u = Some \<mu>"
proof -
  from assms obtain \<sigma> :: "('f, 'v) subst" where "t \<cdot> \<sigma> = u \<cdot> \<sigma>"
    using vars_term_disjoint_imp_unifier by metis
  thus ?thesis
    using ex_mgu_if_subst_apply_term_eq_subst_apply_term
    by metis
qed

(* corollary
  fixes \<mu> :: "('f, 'v) subst" and E :: "('f, 'v) equations" and Evars :: "'v set"
  assumes imgu_\<mu>: "is_imgu \<mu> E" and fin_E: "finite E"
  defines "Evars \<equiv> (\<Union>e \<in> E. vars_term (fst e) \<union> vars_term (snd e))"
  shows "(\<Union>x \<in> -Evars. vars_term (\<mu> x)) \<subseteq> -Evars"
  using imgu_subst_domain_subset[OF assms(1,2), folded Evars_def] *)
(*   by (smt (verit, del_insts) ComplD SUP_le_iff Term.term.simps(17) compl_le_swap1
      subset_Compl_singleton subset_eq subst_ident_if_not_in_domain) *)

lemma restrict_subst_domain_subst_composition:
  fixes \<sigma>\<^sub>A \<sigma>\<^sub>B A B
  assumes
    distinct_domains: "A \<inter> B = {}" and
    distinct_range: "\<forall>x \<in> A. vars_term (\<sigma>\<^sub>A x) \<inter> subst_domain \<sigma>\<^sub>B = {}"
  defines "\<sigma> \<equiv> restrict_subst_domain A \<sigma>\<^sub>A \<circ>\<^sub>s \<sigma>\<^sub>B"
  shows "x \<in> A \<Longrightarrow> \<sigma> x = \<sigma>\<^sub>A x" "x \<in> B \<Longrightarrow> \<sigma> x = \<sigma>\<^sub>B x"
proof -
  assume "x \<in> A"
  hence "restrict_subst_domain A \<sigma>\<^sub>A x = \<sigma>\<^sub>A x"
    by (simp add: restrict_subst_domain_def)
  moreover have "\<sigma>\<^sub>A x \<cdot> \<sigma>\<^sub>B = \<sigma>\<^sub>A x"
    using distinct_range
    by (simp add: \<open>x \<in> A\<close> subst_apply_term_ident)
  ultimately show "\<sigma> x = \<sigma>\<^sub>A x"
    by (simp add: \<sigma>_def subst_compose_def)
next
  assume "x \<in> B"
  hence "restrict_subst_domain A \<sigma>\<^sub>A x = Var x"
    using distinct_domains
    by (metis Int_iff empty_iff restrict_subst_domain_def)
  then show "\<sigma> x = \<sigma>\<^sub>B x"
    by (simp add: \<sigma>_def subst_compose_def)
qed

lemma merge_substs_on_disjoint_domains:
  fixes \<sigma>\<^sub>A \<sigma>\<^sub>B A B
  assumes distinct_domains: "A \<inter> B = {}"
  defines "\<sigma> \<equiv> (\<lambda>x. if x \<in> A then \<sigma>\<^sub>A x else if x \<in> B then \<sigma>\<^sub>B x else Var x)"
  shows
    "x \<in> A \<Longrightarrow> \<sigma> x = \<sigma>\<^sub>A x"
    "x \<in> B \<Longrightarrow> \<sigma> x = \<sigma>\<^sub>B x"
    "x \<notin> A \<union> B \<Longrightarrow> \<sigma> x = Var x"
proof -
  show "x \<in> A \<Longrightarrow> \<sigma> x = \<sigma>\<^sub>A x"
    by (simp add: \<sigma>_def)
next
  assume "x \<in> B"
  moreover hence "x \<notin> A"
    using distinct_domains by auto
  ultimately show "\<sigma> x = \<sigma>\<^sub>B x"
    by (simp add: \<sigma>_def)
next
  show "x \<notin> A \<union> B \<Longrightarrow> \<sigma> x = Var x"
    by (simp add: \<sigma>_def)
qed

definition is_grounding_merge where
  "is_grounding_merge \<gamma> A \<gamma>\<^sub>A B \<gamma>\<^sub>B \<longleftrightarrow>
    A \<inter> B = {} \<longrightarrow> (\<forall>x \<in> A. vars_term (\<gamma>\<^sub>A x) = {}) \<longrightarrow> (\<forall>x \<in> B. vars_term (\<gamma>\<^sub>B x) = {}) \<longrightarrow>
    (\<forall>x \<in> A. \<gamma> x = \<gamma>\<^sub>A x) \<and> (\<forall>x \<in> B. \<gamma> x = \<gamma>\<^sub>B x)"

lemma is_grounding_merge_if_mem_then_else[simp]:
  fixes \<gamma>\<^sub>A \<gamma>\<^sub>B A B
  defines "\<gamma> \<equiv> (\<lambda>x. if x \<in> A then \<gamma>\<^sub>A x else \<gamma>\<^sub>B x)"
  shows "is_grounding_merge \<gamma> A \<gamma>\<^sub>A B \<gamma>\<^sub>B"
  unfolding is_grounding_merge_def
  by (auto simp: \<gamma>_def)

lemma is_grounding_merge_restrict_subst_domain_comp[simp]:
  fixes \<gamma>\<^sub>A \<gamma>\<^sub>B A B
  defines "\<gamma> \<equiv> restrict_subst_domain A \<gamma>\<^sub>A \<circ>\<^sub>s \<gamma>\<^sub>B"
  shows "is_grounding_merge \<gamma> A \<gamma>\<^sub>A B \<gamma>\<^sub>B"
  unfolding is_grounding_merge_def
proof (intro impI)
  assume disjoint: "A \<inter> B = {}" and
    ball_A_ground: "\<forall>x\<in>A. vars_term (\<gamma>\<^sub>A x) = {}" and
    ball_B_ground: "\<forall>x\<in>B. vars_term (\<gamma>\<^sub>B x) = {}"

  from ball_A_ground have "\<forall>x\<in>A. vars_term (\<gamma>\<^sub>A x) \<inter> subst_domain \<gamma>\<^sub>B = {}"
    by simp
  thus "(\<forall>x\<in>A. \<gamma> x = \<gamma>\<^sub>A x) \<and> (\<forall>x\<in>B. \<gamma> x = \<gamma>\<^sub>B x)"
    using restrict_subst_domain_subst_composition[OF disjoint, of \<gamma>\<^sub>A \<gamma>\<^sub>B]
    by (simp_all add: \<gamma>_def)
qed
  

subsubsection \<open>First_Order_Terms And Abstract_Substitution\<close>

no_notation subst_apply_term (infixl "\<cdot>" 67)
no_notation subst_compose (infixl "\<circ>\<^sub>s" 75)

global_interpretation substitution_ops subst_apply_term Var subst_compose .

notation subst_atm_abbrev (infixl "\<cdot>a" 67)
notation subst_atm_list (infixl "\<cdot>al" 67)
notation subst_lit (infixl "\<cdot>l" 67)
notation subst_cls (infixl "\<cdot>" 67)
notation subst_clss (infixl "\<cdot>cs" 67)
notation subst_cls_list (infixl "\<cdot>cl" 67)
notation subst_cls_lists (infixl "\<cdot>\<cdot>cl" 67)
notation comp_subst_abbrev (infixl "\<odot>" 67)

abbreviation vars_lit :: "('f, 'v) Term.term literal \<Rightarrow> 'v set" where
  "vars_lit L \<equiv> vars_term (atm_of L)"

definition vars_cls :: "('f, 'v) term clause \<Rightarrow> 'v set" where
  "vars_cls C = Union (set_mset (image_mset vars_lit C))"

definition vars_clss :: "('f, 'v) term clause set \<Rightarrow> 'v set" where
  "vars_clss N = (\<Union>C \<in> N. vars_cls C)"

lemma vars_clss_empty[simp]: "vars_clss {} = {}"
  by (simp add: vars_clss_def)

lemma vars_clss_insert[simp]: "vars_clss (insert C N) = vars_cls C \<union> vars_clss N"
  by (simp add: vars_clss_def)

lemma vars_clss_union[simp]: "vars_clss (CC \<union> DD) = vars_clss CC \<union> vars_clss DD"
  by (simp add: vars_clss_def)

lemma vars_cls_empty[simp]: "vars_cls {#} = {}"
  unfolding vars_cls_def by simp

lemma finite_vars_cls[simp]: "finite (vars_cls C)"
  unfolding vars_cls_def by simp

lemma vars_cls_plus_iff: "vars_cls (C + D) = vars_cls C \<union> vars_cls D"
  unfolding vars_cls_def by simp

lemma vars_cls_subset_vars_cls_if_subset_mset: "C \<subseteq># D \<Longrightarrow> vars_cls C \<subseteq> vars_cls D"
  by (auto simp add: vars_cls_def)

lemma is_ground_atm_iff_vars_empty: "is_ground_atm t \<longleftrightarrow> vars_term t = {}"
  by (metis (mono_tags, opaque_lifting) equals0D equals0I is_ground_atm_def subst_apply_term_empty
      subst_def subst_simps(1) term.distinct(1) term_subst_eq term_subst_eq_rev)

lemma is_ground_lit_iff_vars_empty: "is_ground_lit L \<longleftrightarrow> vars_lit L = {}"
  by (simp add: is_ground_atm_iff_vars_empty is_ground_lit_def)

lemma is_ground_cls_iff_vars_empty: "is_ground_cls C \<longleftrightarrow> vars_cls C = {}"
  by (auto simp: is_ground_cls_def is_ground_lit_iff_vars_empty vars_cls_def)

lemma is_ground_atm_is_ground_on_var:
  assumes "is_ground_atm (A \<cdot>a \<sigma>)" and "v \<in> vars_term A"
  shows "is_ground_atm (\<sigma> v)"
using assms proof (induction A)
  case (Var x)
  then show ?case by auto
next
  case (Fun f ts)
  then show ?case unfolding is_ground_atm_def
    by auto
qed

lemma is_ground_lit_is_ground_on_var:
  assumes ground_lit: "is_ground_lit (subst_lit L \<sigma>)" and v_in_L: "v \<in> vars_lit L"
  shows "is_ground_atm (\<sigma> v)"
proof -
  let ?A = "atm_of L"
  from v_in_L have A_p: "v \<in> vars_term ?A"
    by auto
  then have "is_ground_atm (?A \<cdot>a \<sigma>)"
    using ground_lit unfolding is_ground_lit_def by auto
  then show ?thesis
    using A_p is_ground_atm_is_ground_on_var by metis
qed

lemma is_ground_cls_is_ground_on_var:
  assumes
    ground_clause: "is_ground_cls (subst_cls C \<sigma>)" and
    v_in_C: "v \<in> vars_cls C"
  shows "is_ground_atm (\<sigma> v)"
proof -
  from v_in_C obtain L where L_p: "L \<in># C" "v \<in> vars_lit L"
    unfolding vars_cls_def by auto
  then have "is_ground_lit (subst_lit L \<sigma>)"
    using ground_clause unfolding is_ground_cls_def subst_cls_def by auto
  then show ?thesis
    using L_p is_ground_lit_is_ground_on_var by metis
qed


lemma vars_atm_subset_subst_domain_if_grounding:
  assumes "is_ground_atm (t \<cdot>a \<gamma>)"
  shows "vars_term t \<subseteq> subst_domain \<gamma>"
  using assms
  by (metis empty_iff is_ground_atm_iff_vars_empty is_ground_atm_is_ground_on_var subsetI
      subst_ident_if_not_in_domain term.set_intros(3))

lemma vars_lit_subset_subst_domain_if_grounding:
  assumes "is_ground_lit (L \<cdot>l \<gamma>)"
  shows "vars_lit L \<subseteq> subst_domain \<gamma>"
  using assms vars_atm_subset_subst_domain_if_grounding
  by (metis atm_of_subst_lit is_ground_lit_def)

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

lemma same_on_vars_lit:
  assumes "\<forall>v \<in> vars_lit L. \<sigma> v = \<tau> v"
  shows "subst_lit L \<sigma> = subst_lit L \<tau>"
  using assms
proof (induction L)
  case (Pos x)
  then have "\<forall>v \<in> vars_term x. \<sigma> v = \<tau> v \<Longrightarrow> subst_atm_abbrev x \<sigma> = subst_atm_abbrev x \<tau>"
    using term_subst_eq by metis+
  then show ?case
    unfolding subst_lit_def using Pos by auto
next
  case (Neg x)
  then have "\<forall>v \<in> vars_term x. \<sigma> v = \<tau> v \<Longrightarrow> subst_atm_abbrev x \<sigma> = subst_atm_abbrev x \<tau>"
    using term_subst_eq by metis+
  then show ?case
    unfolding subst_lit_def using Neg by auto
qed

lemma same_on_vars_clause:
  assumes "\<forall>v \<in> vars_cls S. \<sigma> v = \<tau> v"
  shows "subst_cls S \<sigma> = subst_cls S \<tau>"
  by (smt assms image_eqI image_mset_cong2 mem_simps(9) same_on_vars_lit set_image_mset
      subst_cls_def vars_cls_def)

lemma same_on_lits_clause:
  assumes "\<forall>L \<in># C. subst_lit L \<sigma> = subst_lit L \<tau>"
  shows "subst_cls C \<sigma> = subst_cls C \<tau>"
  using assms unfolding subst_cls_def
  by simp

global_interpretation substitution "(\<cdot>a)" "Var :: _ \<Rightarrow> ('f, 'v) term" "(\<odot>)"
proof unfold_locales
  show "\<And>A. A \<cdot>a Var = A"
    by auto
next
  show "\<And>A \<tau> \<sigma>. A \<cdot>a (\<tau> \<odot> \<sigma>) = A \<cdot>a \<tau> \<cdot>a \<sigma>"
    by auto
next
  show "\<And>\<sigma> \<tau>. (\<And>A. A \<cdot>a \<sigma> = A \<cdot>a \<tau>) \<Longrightarrow> \<sigma> = \<tau>"
    by (simp add: subst_term_eqI)
next
  fix C :: "('f, 'v) term clause" and \<sigma> :: "('f, 'v) subst"
  assume "is_ground_cls (subst_cls C \<sigma>)"
  hence ground_atms_\<sigma>: "\<And>v. v \<in> vars_cls C \<Longrightarrow> is_ground_atm (\<sigma> v)"
    by (meson is_ground_cls_is_ground_on_var)

  define some_ground_trm :: "('f, 'v) term" where "some_ground_trm = (Fun undefined [])"
  have ground_trm: "is_ground_atm some_ground_trm"
    unfolding is_ground_atm_def some_ground_trm_def by auto
  define \<tau> where "\<tau> = (\<lambda>v. if v \<in> vars_cls C then \<sigma> v else some_ground_trm)"
  then have \<tau>_\<sigma>: "\<forall>v \<in> vars_cls C. \<sigma> v = \<tau> v"
    unfolding \<tau>_def by auto

  have all_ground_\<tau>: "is_ground_atm (\<tau> v)" for v
  proof (cases "v \<in> vars_cls C")
    case True
    then show ?thesis
      using ground_atms_\<sigma> \<tau>_\<sigma> by auto
  next
    case False
    then show ?thesis
      unfolding \<tau>_def using ground_trm by auto
  qed
  have "is_ground_subst \<tau>"
    unfolding is_ground_subst_def
  proof
    fix A
    show "is_ground_atm (A \<cdot>a \<tau>)"
    proof (induction A)
      case (Var v)
      thus ?case using all_ground_\<tau> by auto
    next
      case (Fun f As)
      thus ?case using all_ground_\<tau> by (simp add: is_ground_atm_def)
    qed
  qed
  moreover with \<tau>_\<sigma> have "C \<cdot> \<sigma> = C \<cdot> \<tau>"
    using same_on_vars_clause by auto
  ultimately show "\<exists>\<tau>. is_ground_subst \<tau> \<and> C \<cdot> \<tau> = C \<cdot> \<sigma>"
    by auto
next
  show "wfP (strictly_generalizes_atm :: ('f, 'v) term \<Rightarrow> _ \<Rightarrow> _)"
    unfolding wfP_def
    by (rule wf_subset[OF wf_subsumes])
      (auto simp: strictly_generalizes_atm_def generalizes_atm_def term_subsumable.subsumes_def
        subsumeseq_term.simps)
qed

lemma vars_subst_lit_eq_vars_subst_atm: "vars_lit (L \<cdot>l \<sigma>) = vars_term (atm_of L \<cdot>a \<sigma>)"
  by (cases L) simp_all

lemma vars_subst_lit_eq:
  "vars_lit (L \<cdot>l \<sigma>) = (\<Union>x \<in> vars_lit L. vars_term (\<sigma> x))"
  using vars_term_subst_apply_term by (metis atm_of_subst_lit)

lemma vars_subst_cls_eq:
  "vars_cls (C \<cdot> \<sigma>) = (\<Union>x \<in> vars_cls C. vars_term (\<sigma> x))"
  by (simp add: vars_cls_def multiset.set_map UN_UN_flatten subst_cls_def
      vars_subst_lit_eq[symmetric])

lemma vars_subst_lit_subset: "vars_lit (L \<cdot>l \<sigma>) \<subseteq> vars_lit L - subst_domain \<sigma> \<union> range_vars \<sigma>"
  using vars_term_subst_apply_term_subset[of "atm_of L"] by simp

lemma vars_subst_cls_subset: "vars_cls (C \<cdot> \<sigma>) \<subseteq> vars_cls C - subst_domain \<sigma> \<union> range_vars \<sigma>"
  unfolding vars_cls_def subst_cls_def
  apply simp
  using vars_subst_lit_subset
  by fastforce

lemma vars_subst_cls_subset_weak: "vars_cls (C \<cdot> \<sigma>) \<subseteq> vars_cls C \<union> range_vars \<sigma>"
  unfolding vars_cls_def subst_cls_def
  apply simp
  using vars_subst_lit_subset
  by fastforce

lemma vars_cls_plus[simp]: "vars_cls (C + D) = vars_cls C \<union> vars_cls D"
  unfolding vars_cls_def by simp

lemma vars_cls_add_mset[simp]: "vars_cls (add_mset L C) = vars_lit L \<union> vars_cls C"
  by (simp add: vars_cls_def)

lemma UN_vars_term_atm_of_cls[simp]: "(\<Union>T\<in>{atm_of ` set_mset C}. \<Union> (vars_term ` T)) = vars_cls C"
  by (induction C) simp_all

lemma vars_lit_subst_subset_vars_cls_substI[intro]:
  "vars_lit L \<subseteq> vars_cls C \<Longrightarrow> vars_lit (L \<cdot>l \<sigma>) \<subseteq> vars_cls (C \<cdot> \<sigma>)"
  by (metis subset_Un_eq subst_cls_add_mset vars_cls_add_mset vars_subst_cls_eq)

lemma vars_subst_cls_subset_vars_cls_subst:
  "vars_cls C \<subseteq> vars_cls D \<Longrightarrow> vars_cls (C \<cdot> \<sigma>) \<subseteq> vars_cls (D \<cdot> \<sigma>)"
  by (metis subset_Un_eq subst_cls_union vars_cls_plus_iff vars_subst_cls_eq)

lemma vars_cls_subst_subset:
  assumes range_vars_\<eta>: "range_vars \<eta> \<subseteq> vars_lit L \<union> vars_lit L'"
  shows "vars_cls (add_mset L D \<cdot> \<eta>) \<subseteq> vars_cls (add_mset L' (add_mset L D))"
proof -
  have "vars_cls ((add_mset L D) \<cdot> \<eta>) \<subseteq> vars_cls (add_mset L D) - subst_domain \<eta> \<union> range_vars \<eta>"
    by (rule vars_subst_cls_subset[of "add_mset L D" \<eta>])
  also have "... \<subseteq> vars_cls (add_mset L D) - (vars_lit L \<union> vars_lit L') \<union> vars_lit L \<union> vars_lit L'"
    using range_vars_\<eta> by blast
  also have "... \<subseteq> vars_cls (add_mset L D) \<union> vars_lit L' \<union> vars_lit L"
    by auto
  also have "... \<subseteq> vars_cls D \<union> vars_lit L' \<union> vars_lit L"
    by auto
  also have "... \<subseteq> vars_cls (add_mset L' (add_mset L D))"
    by auto
  finally show ?thesis
    by assumption
qed

definition disjoint_vars where
  "disjoint_vars C D \<longleftrightarrow> vars_cls C \<inter> vars_cls D = {}"

lemma disjoint_vars_iff_inter_empty: "disjoint_vars C D \<longleftrightarrow> vars_cls C \<inter> vars_cls D = {}"
  by (rule disjoint_vars_def)

hide_fact disjoint_vars_def

lemma disjoint_vars_sym: "disjoint_vars C D \<longleftrightarrow> disjoint_vars D C"
  unfolding disjoint_vars_iff_inter_empty by blast

lemma disjoint_vars_plus_iff: "disjoint_vars (C + D) E \<longleftrightarrow> disjoint_vars C E \<and> disjoint_vars D E"
  unfolding disjoint_vars_iff_inter_empty vars_cls_plus_iff
  by (simp add: Int_Un_distrib2)

lemma disjoint_vars_subset_mset: "disjoint_vars C D \<Longrightarrow> E \<subseteq># C \<Longrightarrow> disjoint_vars E D"
  by (metis disjoint_vars_plus_iff subset_mset.diff_add)

lemma disjoint_vars_subst_clsI:
  "disjoint_vars C D \<Longrightarrow> range_vars \<sigma> \<inter> vars_cls D = {} \<Longrightarrow> disjoint_vars (C \<cdot> \<sigma>) D"
  unfolding disjoint_vars_iff_inter_empty
  unfolding vars_subst_cls_eq
  by (smt (verit, best) Diff_subset Un_iff disjoint_iff image_cong subsetD vars_subst_cls_eq
      vars_subst_cls_subset)

lemma is_renaming_iff: "is_renaming \<rho> \<longleftrightarrow> (\<forall>x. is_Var (\<rho> x)) \<and> inj \<rho>"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof (rule iffI)
  show "?lhs \<Longrightarrow> ?rhs"
    unfolding is_renaming_def
    apply safe
     apply (metis subst_apply_eq_Var subst_compose term.disc(1))
    by (metis injI subst_compose_def term.sel(1))
next
  show "?rhs \<Longrightarrow> ?lhs"
    by (auto simp: is_renaming_def intro: ex_inverse_of_renaming)
qed

lemma subst_cls_idem_if_disj_vars: "subst_domain \<sigma> \<inter> vars_cls C = {} \<Longrightarrow> C \<cdot> \<sigma> = C"
  by (metis (mono_tags, lifting) Int_iff empty_iff mem_Collect_eq same_on_vars_clause
      subst_cls_id_subst subst_domain_def)

lemma subst_lit_idem_if_disj_vars: "subst_domain \<sigma> \<inter> vars_lit L = {} \<Longrightarrow> L \<cdot>l \<sigma> = L"
  by (rule subst_cls_idem_if_disj_vars[of _ "{#L#}", simplified])

lemma subst_lit_restrict_subst_domain: "vars_lit L \<subseteq> V \<Longrightarrow> L \<cdot>l restrict_subst_domain V \<sigma> = L \<cdot>l \<sigma>"
  by (simp add: restrict_subst_domain_def same_on_vars_lit subsetD)

lemma subst_cls_restrict_subst_domain: "vars_cls C \<subseteq> V \<Longrightarrow> C \<cdot> restrict_subst_domain V \<sigma> = C \<cdot> \<sigma>"
  by (simp add: restrict_subst_domain_def same_on_vars_clause subsetD)

lemma subst_clss_insert[simp]: "insert C U \<cdot>cs \<eta> = insert (C \<cdot> \<eta>) (U \<cdot>cs \<eta>)"
  by (simp add: subst_clss_def)

lemma valid_grounding_of_renaming:
  assumes "is_renaming \<rho>"
  shows "I \<TTurnstile>s grounding_of_cls (C \<cdot> \<rho>) \<longleftrightarrow> I \<TTurnstile>s grounding_of_cls C"
proof -
  have "grounding_of_cls (C \<cdot> \<rho>) = grounding_of_cls C"
    by (rule grounding_of_subst_cls_renaming_ident[OF \<open>is_renaming \<rho>\<close>])
  thus ?thesis
    by simp
qed

lemma is_unifier_iff_mem_unifiers_Times:
  assumes fin_AA: "finite AA"
  shows "is_unifier \<upsilon> AA \<longleftrightarrow> \<upsilon> \<in> unifiers (AA \<times> AA)"
proof (rule iffI)
  assume unif_\<upsilon>_AA: "is_unifier \<upsilon> AA"
  show "\<upsilon> \<in> unifiers (AA \<times> AA)"
  unfolding unifiers_def mem_Collect_eq
  proof (rule ballI)
    have "card (AA \<cdot>\<^sub>s\<^sub>e\<^sub>t \<upsilon>) \<le> 1"
      by (rule unif_\<upsilon>_AA[unfolded is_unifier_def subst_atms_def])
  
    fix p assume "p \<in> AA \<times> AA"
    then obtain a b where p_def: "p = (a, b)" and "a \<in> AA" and "b \<in> AA"
      by auto
    hence "card (AA \<cdot>\<^sub>s\<^sub>e\<^sub>t \<upsilon>) = 1"
      using fin_AA \<open>card (AA \<cdot>\<^sub>s\<^sub>e\<^sub>t \<upsilon>) \<le> 1\<close> antisym_conv2 by fastforce
  
    hence "a \<cdot>a \<upsilon> = b \<cdot>a \<upsilon>"
      using \<open>a \<in> AA\<close> \<open>b \<in> AA\<close> fin_AA is_unifier_subst_atm_eqI unif_\<upsilon>_AA by blast
    thus "fst p \<cdot>a \<upsilon> = snd p \<cdot>a \<upsilon>"
      by (simp add: p_def)
  qed
next
  assume unif_\<upsilon>_AA: "\<upsilon> \<in> unifiers (AA \<times> AA)"
  show "is_unifier \<upsilon> AA"
    using fin_AA unif_\<upsilon>_AA
  proof (induction AA arbitrary: \<upsilon> rule: finite_induct)
    case empty
    then show ?case
      by (simp add: is_unifier_def)
  next
    case (insert a AA)
    from insert.prems have
      \<upsilon>_in: "\<upsilon> \<in> unifiers ((insert (a, a) (Pair a ` AA) \<union> (\<lambda>x. (x, a)) ` AA) \<union> AA \<times> AA)"
      unfolding insert_Times_insert'[of a AA a AA] by simp
    then show ?case
      by (smt (verit, del_insts) Set.set_insert Un_insert_left finite.insertI fst_conv image_insert
          insert.hyps(1) insert_compr is_unifier_alt mem_Collect_eq snd_conv unifiers_def)
  qed
qed

lemma is_mgu_singleton_iff_Unifiers_is_mgu_Times:
  assumes fin: "finite AA"
  shows "is_mgu \<upsilon> {AA} \<longleftrightarrow> Unifiers.is_mgu \<upsilon> (AA \<times> AA)"
  by (auto simp: is_mgu_def Unifiers.is_mgu_def is_unifiers_def
      is_unifier_iff_mem_unifiers_Times[OF fin])

lemma is_imgu_singleton_iff_Unifiers_is_imgu_Times:
  assumes fin: "finite AA"
  shows "is_imgu \<upsilon> {AA} \<longleftrightarrow> Unifiers.is_imgu \<upsilon> (AA \<times> AA)"
  by (auto simp: is_imgu_def Unifiers.is_imgu_def is_unifiers_def
      is_unifier_iff_mem_unifiers_Times[OF fin])


lemma unifiers_without_refl: "unifiers E = unifiers {e \<in> E. fst e \<noteq> snd e}"
  (is "?lhs = ?rhs")
  unfolding unifiers_def by fastforce

lemma subst_lit_renaming_subst_adapted:
  assumes ren_\<rho>: "is_renaming \<rho>" and vars_L: "vars_lit L \<subseteq> subst_domain \<sigma>"
  shows "L \<cdot>l \<rho> \<cdot>l rename_subst_domain \<rho> \<sigma> = L \<cdot>l \<sigma>"
proof -
  from ren_\<rho> have is_var_\<rho>: "\<forall>x. is_Var (\<rho> x)" and "inj \<rho>"
    by (simp_all add: is_renaming_iff)

  show ?thesis
    using vars_L renaming_cancels_rename_subst_domain[OF is_var_\<rho> \<open>inj \<rho>\<close>]
    by (cases L) (simp_all add: subst_lit_def)
qed

lemma subst_renaming_subst_adapted:
  assumes ren_\<rho>: "is_renaming \<rho>" and vars_D: "vars_cls D \<subseteq> subst_domain \<sigma>"
  shows "D \<cdot> \<rho> \<cdot> rename_subst_domain \<rho> \<sigma> = D \<cdot> \<sigma>"
  unfolding subst_cls_comp_subst[symmetric]
proof (intro same_on_lits_clause ballI)
  fix L assume "L \<in># D"
  with vars_D have "vars_lit L \<subseteq> subst_domain \<sigma>"
    by (auto dest!: multi_member_split)
  thus "L \<cdot>l (\<rho> \<odot> rename_subst_domain \<rho> \<sigma>) = L \<cdot>l \<sigma>"
    unfolding subst_lit_comp_subst
    by (rule subst_lit_renaming_subst_adapted[OF ren_\<rho>])
qed

lemma subst_domain_rename_subst_domain_subset':
  assumes is_var_\<rho>: "\<forall>x. is_Var (\<rho> x)"
  shows "subst_domain (rename_subst_domain \<rho> \<sigma>) \<subseteq> (\<Union>x \<in> subst_domain \<sigma>. vars_term (\<rho> x))"
proof (rule subset_trans)
  show "subst_domain (rename_subst_domain \<rho> \<sigma>) \<subseteq> the_Var ` \<rho> ` subst_domain \<sigma>"
    by (rule subst_domain_rename_subst_domain_subset[OF is_var_\<rho>])
next
  show "the_Var ` \<rho> ` subst_domain \<sigma> \<subseteq> (\<Union>x\<in>subst_domain \<sigma>. vars_term (\<rho> x))"
    unfolding image_the_Var_image_subst_renaming_eq[OF is_var_\<rho>] by simp
qed

lemma range_vars_eq_empty_if_is_ground:
  "is_ground_cls (C \<cdot> \<gamma>) \<Longrightarrow> subst_domain \<gamma> \<subseteq> vars_cls C \<Longrightarrow> range_vars \<gamma> = {}"
  unfolding range_vars_def UNION_empty_conv subst_range.simps is_ground_cls_iff_vars_empty
  by (metis (no_types, opaque_lifting) dual_order.eq_iff imageE is_ground_atm_iff_vars_empty
      is_ground_cls_iff_vars_empty is_ground_cls_is_ground_on_var
      vars_cls_subset_subst_domain_if_grounding)


subsubsection \<open>Minimal, Idempotent Most General Unifier\<close>

lemma is_imgu_if_mgu_eq_Some:
  assumes mgu: "Unification.mgu t u = Some \<mu>"
  shows "is_imgu \<mu> {{t, u}}"
proof -
  have "unifiers ({t, u} \<times> {t, u}) = unifiers {(t, u)}"
    by (auto simp: unifiers_def)
  hence  "Unifiers.is_imgu \<mu> ({t, u} \<times> {t, u})"
    using mgu_sound[OF mgu]
    by (simp add: Unifiers.is_imgu_def)
  thus ?thesis
    by (simp add: is_imgu_singleton_iff_Unifiers_is_imgu_Times)
qed

primrec pairs where
  "pairs [] = []" |
  "pairs (x # xs) = (x, x) # map (Pair x) xs @ map (\<lambda>y. (y, x)) xs @ pairs xs"

lemma "set (pairs [a, b, c, d]) =
  {(a, a), (a, b), (a, c), (a, d),
   (b, a), (b, b), (b, c), (b, d),
   (c, a), (c, b), (c, c), (c, d),
   (d, a), (d, b), (d, c), (d, d)}"
  by auto

lemma set_pairs: "set (pairs xs) = set xs \<times> set xs"
  by (induction xs) auto

text \<open>Reflexive and symmetric pairs are not necessary to computing the MGU, but it makes the set of
the resulting list equivalent to @{term "{(x, y). x \<in> xs \<and> y \<in> ys}"}, which is necessary for the
following properties.\<close>

lemma pair_in_set_pairs: "a \<in> set as \<Longrightarrow> b \<in> set as \<Longrightarrow> (a, b) \<in> set (pairs as)"
  by (induction as) auto

lemma fst_pair_in_set_if_pair_in_pairs: "p \<in> set (pairs as) \<Longrightarrow> fst p \<in> set as"
  by (induction as) auto

lemma snd_pair_in_set_if_pair_in_pairs: "p \<in> set (pairs as) \<Longrightarrow> snd p \<in> set as"
  by (induction as) auto

lemma vars_mset_mset_pairs:
  "vars_mset (mset (pairs as)) = (\<Union>b \<in> set as. \<Union>a \<in> set as. vars_term a \<union> vars_term b)"
  by (induction as) (auto simp: vars_mset_def)

definition mgu_sets where
  "mgu_sets \<mu> AAA \<longleftrightarrow> (\<exists>ass. set (map set ass) = AAA \<and>
    map_option subst_of (unify (concat (map pairs ass)) []) = Some \<mu>)"

lemma is_imgu_if_mgu_sets:
  assumes mgu_AAA: "mgu_sets \<mu> AAA"
  shows "is_imgu \<mu> AAA"
proof -
  from mgu_AAA obtain ass xs where
    AAA_def: "AAA = set (map set ass)" and
    unify: "unify (concat (map pairs ass)) [] = Some xs" and
    "subst_of xs = \<mu>"
    unfolding mgu_sets_def by auto
  hence "Unifiers.is_imgu \<mu> (set (concat (map pairs ass)))"
    using unify_sound[OF unify] by simp
  moreover have "unifiers (set (concat (map pairs ass))) = {\<upsilon>. is_unifiers \<upsilon> AAA}"
    unfolding AAA_def
  proof (rule Set.equalityI; rule Set.subsetI; unfold mem_Collect_eq)
    fix x assume x_in: "x \<in> unifiers (set (concat (map pairs ass)))"
    show "is_unifiers x (set (map set ass))"
      unfolding is_unifiers_def
    proof (rule ballI)
      fix As assume "As \<in> set (map set ass)"
      hence "finite As" by auto

      from \<open>As \<in> set (map set ass)\<close> obtain as where
        as_in: "as \<in> set ass" and As_def: "As = set as"
        by auto

      show "is_unifier x As"
        unfolding is_unifier_alt[OF \<open>finite As\<close>]
      proof (intro ballI)
        fix A B assume "A \<in> As" "B \<in> As"
        hence "\<exists>xs \<in> set ass. (A, B) \<in> set (pairs xs)"
          using as_in by (auto simp: As_def intro: pair_in_set_pairs)
        thus "A \<cdot>a x = B \<cdot>a x"
          using x_in[unfolded unifiers_def mem_Collect_eq, rule_format, of "(A, B)", simplified]
          by simp
      qed
    qed
  next
    fix x assume is_unifs_x: "is_unifiers x (set (map set ass))"
    show "x \<in> unifiers (set (concat (map pairs ass)))"
      unfolding unifiers_def mem_Collect_eq
    proof (rule ballI)
      fix p assume "p \<in> set (concat (map pairs ass))"
      then obtain as where "as \<in> set ass" and p_in: "p \<in> set (pairs as)"
        by auto
      hence is_unif_x: "is_unifier x (set as)"
        using is_unifs_x[unfolded is_unifiers_def] by simp
      moreover have "fst p \<in> set as"
        by (rule p_in[THEN fst_pair_in_set_if_pair_in_pairs])
      moreover have "snd p \<in> set as"
        by (rule p_in[THEN snd_pair_in_set_if_pair_in_pairs])
      ultimately show "fst p \<cdot>a x = snd p \<cdot>a x"
        unfolding is_unifier_alt[of "set as", simplified]
        by blast
    qed
  qed
  ultimately show "is_imgu \<mu> AAA"
    unfolding Unifiers.is_imgu_def is_imgu_def by simp
qed


subsubsection \<open>Renaming Extra\<close>

context renaming_apart begin

lemma inj_Var_comp_renaming: "finite V \<Longrightarrow> inj (Var \<circ> renaming V)"
  using inj_compose inj_renaming by (metis inj_def term.inject(1))

lemma is_renaming_Var_comp_renaming: "finite V \<Longrightarrow> Term.is_renaming (Var \<circ> renaming V)"
  unfolding Term.is_renaming_def
  using inj_Var_comp_renaming by (metis comp_apply inj_on_subset term.disc(1) top_greatest)

lemma vars_term_subst_term_Var_comp_renaming_disj:
  assumes fin_V: "finite V"
  shows "vars_term (t \<cdot>a (Var \<circ> renaming V)) \<inter> V = {}"
  using is_renaming_Var_comp_renaming[OF fin_V] renaming_correct[OF fin_V]
  by (induction t) auto

lemma vars_term_subst_term_Var_comp_renaming_disj':
  assumes fin_V: "finite V1" and sub: "V2 \<subseteq> V1"
  shows "vars_term (t \<cdot>a (Var \<circ> renaming V1)) \<inter> V2 = {}"
  by (meson disjoint_iff fin_V sub subsetD vars_term_subst_term_Var_comp_renaming_disj)

lemma vars_lit_subst_renaming_disj:
  assumes fin_V: "finite V"
  shows "vars_lit (L \<cdot>l (Var \<circ> renaming V)) \<inter> V = {}"
  using vars_term_subst_term_Var_comp_renaming_disj[OF fin_V] by auto

lemma vars_cls_subst_renaming_disj:
  assumes fin_V: "finite V"
  shows "vars_cls (C \<cdot> (Var \<circ> renaming V)) \<inter> V = {}"
  unfolding vars_cls_def
  apply simp
  using vars_lit_subst_renaming_disj[OF fin_V]
  by (smt (verit, best) UN_iff UN_simps(10) disjoint_iff multiset.set_map subst_cls_def)

abbreviation renaming_wrt :: "('f, _) Term.term clause set \<Rightarrow> _ \<Rightarrow> ('f, _) Term.term" where
  "renaming_wrt N \<equiv> Var \<circ> renaming (vars_clss N)"

lemma is_renaming_renaming_wrt: "finite N \<Longrightarrow> is_renaming (renaming_wrt N)"
  by (simp add: inj_Var_comp_renaming is_renaming_iff vars_clss_def)

lemma ex_renaming_to_disjoint_vars:
  fixes C :: "('f, 'a) Term.term clause" and N :: "('f, 'a) Term.term clause set"
  assumes fin: "finite N"
  shows "\<exists>\<rho>. is_renaming \<rho> \<and> vars_cls (C \<cdot> \<rho>) \<inter> vars_clss N = {}"
proof (intro exI conjI)
  show "Simple_Clause_Learning.is_renaming (renaming_wrt N)"
    using fin is_renaming_renaming_wrt by metis
next
  show "vars_cls (C \<cdot> renaming_wrt N) \<inter> vars_clss N = {}"
    by (simp add: fin vars_cls_subst_renaming_disj vars_clss_def)
qed

end


section \<open>SCL State\<close>

type_synonym ('f, 'v) closure = "('f, 'v) term clause \<times> ('f, 'v) subst"
type_synonym ('f, 'v) closure_with_lit =
  "('f, 'v) term clause \<times> ('f, 'v) term literal \<times> ('f, 'v) subst"
type_synonym ('f, 'v) trail = "(('f, 'v) term literal \<times> ('f, 'v) closure_with_lit option) list"
type_synonym ('f, 'v) state =
  "('f, 'v) trail \<times> ('f, 'v) term clause fset \<times> ('f, 'v) closure option"

text \<open>Note that, in contrast to Bromberger, Schwarz, and Weidenbach, the level is not part of the
state. It would be redundant because it can always be computed from the trail.\<close>

abbreviation initial_state :: "('f, 'v) state" where
  "initial_state \<equiv> ([], {||}, None)"

definition state_trail :: "('f, 'v) state \<Rightarrow> ('f, 'v) trail" where
  "state_trail S = fst S"

lemma state_trail_simp[simp]: "state_trail (\<Gamma>, U, u) = \<Gamma>"
  by (simp add: state_trail_def)

definition state_learned :: "('f, 'v) state \<Rightarrow> ('f, 'v) term clause fset" where
  "state_learned S = fst (snd S)"

lemma state_learned_simp[simp]: "state_learned (\<Gamma>, U, u) = U"
  by (simp add: state_learned_def)

definition state_conflict :: "('f, 'v) state \<Rightarrow> ('f, 'v) closure option" where
  "state_conflict S = snd (snd S)"

lemma state_conflict_simp[simp]: "state_conflict (\<Gamma>, U, u) = u"
  by (simp add: state_conflict_def)

lemmas state_proj_simp = state_trail_simp state_learned_simp state_conflict_simp

lemma state_simp[simp]: "(state_trail S, state_learned S, state_conflict S) = S"
  by (simp add: state_conflict_def state_learned_def state_trail_def)

fun clss_of_trail_lit where
  "clss_of_trail_lit (_, None) = {||}" |
  "clss_of_trail_lit (_, Some (C, L, _)) = {|add_mset L C|}"

primrec clss_of_trail :: "('f, 'v) trail \<Rightarrow> ('f, 'v) term clause fset" where
  "clss_of_trail [] = {||}" |
  "clss_of_trail (Ln # \<Gamma>) = clss_of_trail_lit Ln |\<union>| clss_of_trail \<Gamma>"

hide_fact clss_of_trail_def

lemma clss_of_trail_append: "clss_of_trail (\<Gamma>\<^sub>0 @ \<Gamma>\<^sub>1) = clss_of_trail \<Gamma>\<^sub>0 |\<union>| clss_of_trail \<Gamma>\<^sub>1"
  by (induction \<Gamma>\<^sub>0) (simp_all add: funion_assoc)

fun clss_of_closure where
  "clss_of_closure None = {||}" |
  "clss_of_closure (Some (C, _)) = {|C|}"


definition propagate_lit where
  "propagate_lit L C \<gamma> = (L \<cdot>l \<gamma>, Some (C, L, \<gamma>))"

abbreviation trail_propagate ::
  "('f, 'v) trail \<Rightarrow> ('f, 'v) term literal \<Rightarrow> ('f, 'v) term clause \<Rightarrow> ('f, 'v) subst \<Rightarrow>
    ('f, 'v) trail" where
  "trail_propagate \<Gamma> L C \<gamma> \<equiv> propagate_lit L C \<gamma> # \<Gamma>"

lemma suffix_trail_propagate[simp]: "suffix \<Gamma> (trail_propagate \<Gamma> L C \<delta>)"
  unfolding suffix_def propagate_lit_def
  by simp

lemma clss_of_trail_trail_propagate[simp]:
  "clss_of_trail (trail_propagate \<Gamma> L C \<gamma>) = finsert (add_mset L C) (clss_of_trail \<Gamma>)"
  unfolding propagate_lit_def by simp

definition decide_lit where
  "decide_lit L = (L, None)"

abbreviation trail_decide :: "('f, 'v) trail \<Rightarrow> ('f, 'v) term literal \<Rightarrow> ('f, 'v) trail" where
  "trail_decide \<Gamma> L \<equiv> decide_lit L # \<Gamma>"

lemma clss_of_trail_trail_decide[simp]:
  "clss_of_trail (trail_decide \<Gamma> L) = clss_of_trail \<Gamma>"
  by (simp add: decide_lit_def)

definition is_decision_lit
  :: "('f, 'v) term literal \<times> ('f, 'v) closure_with_lit option \<Rightarrow> bool" where
  "is_decision_lit Ln \<longleftrightarrow> snd Ln = None"

definition trail_interp :: "('f, 'v) trail \<Rightarrow> ('f, 'v) term interp" where
  "trail_interp \<Gamma> = \<Union>((\<lambda>L. case L of Pos A \<Rightarrow> {A} | Neg A \<Rightarrow> {}) ` fst ` set \<Gamma>)"

lemma "trail_interp \<Gamma> = (\<Union>Ln \<in> set \<Gamma>. case fst Ln of Pos t \<Rightarrow> {t} | Neg t \<Rightarrow> {})"
  unfolding trail_interp_def by simp

definition trail_true_lit :: "('f, 'v) trail \<Rightarrow> ('f, 'v) term literal \<Rightarrow> bool" where
  "trail_true_lit \<Gamma> L \<longleftrightarrow> L \<in> fst ` set \<Gamma>"

definition trail_false_lit :: "('f, 'v) trail \<Rightarrow> ('f, 'v) term literal \<Rightarrow> bool" where
  "trail_false_lit \<Gamma> L \<longleftrightarrow> - L \<in> fst ` set \<Gamma>"

definition trail_true_cls :: "('f, 'v) trail \<Rightarrow> ('f, 'v) term clause \<Rightarrow> bool" where
  "trail_true_cls \<Gamma> C \<longleftrightarrow> (\<exists>L \<in># C. trail_true_lit \<Gamma> L)"

definition trail_false_cls :: "('f, 'v) trail \<Rightarrow> ('f, 'v) term clause \<Rightarrow> bool" where
  "trail_false_cls \<Gamma> C \<longleftrightarrow> (\<forall>L \<in># C. trail_false_lit \<Gamma> L)"

definition trail_true_clss :: "('f, 'v) trail \<Rightarrow> ('f, 'v) term clause set \<Rightarrow> bool" where
  "trail_true_clss \<Gamma> N \<longleftrightarrow> (\<forall>C \<in> N. trail_true_cls \<Gamma> C)"

definition trail_defined_lit :: "('f, 'v) trail \<Rightarrow> ('f, 'v) term literal \<Rightarrow> bool" where
  "trail_defined_lit \<Gamma> L \<longleftrightarrow> (L \<in> fst ` set \<Gamma> \<or> - L \<in> fst ` set \<Gamma>)"

definition trail_defined_cls :: "('f, 'v) trail \<Rightarrow> ('f, 'v) term clause \<Rightarrow> bool" where
  "trail_defined_cls \<Gamma> C \<longleftrightarrow> (\<forall>L \<in># C. trail_defined_lit \<Gamma> L)"

lemma trail_defined_lit_iff_true_or_false:
  "trail_defined_lit \<Gamma> L \<longleftrightarrow> trail_true_lit \<Gamma> L \<or> trail_false_lit \<Gamma> L"
  unfolding trail_defined_lit_def trail_false_lit_def trail_true_lit_def by (rule refl)

lemma trail_true_or_false_cls_if_defined:
  "trail_defined_cls \<Gamma> C \<Longrightarrow> trail_true_cls \<Gamma> C \<or> trail_false_cls \<Gamma> C"
  unfolding trail_defined_cls_def trail_false_cls_def trail_true_cls_def
  unfolding trail_defined_lit_iff_true_or_false
  by blast

lemma trail_false_cls_mempty[simp]: "trail_false_cls \<Gamma> {#}"
  by (simp add: trail_false_cls_def)

lemma trail_false_cls_add_mset:
  "trail_false_cls \<Gamma> (add_mset L C) \<longleftrightarrow> trail_false_lit \<Gamma> L \<and> trail_false_cls \<Gamma> C"
  by (auto simp: trail_false_cls_def)

lemma trail_false_cls_plus:
  "trail_false_cls \<Gamma> (C + D) \<longleftrightarrow> trail_false_cls \<Gamma> C \<and> trail_false_cls \<Gamma> D"
  by (auto simp: trail_false_cls_def)

lemma not_trail_true_Nil[simp]:
  "\<not> trail_true_lit [] L"
  "\<not> trail_true_cls [] C"
  "N \<noteq> {} \<Longrightarrow> \<not> trail_true_clss [] N"
  by (simp_all add: trail_true_lit_def trail_true_cls_def trail_true_clss_def)

lemma not_trail_false_Nil[simp]:
  "\<not> trail_false_lit [] L"
  "trail_false_cls [] C \<longleftrightarrow> C = {#}"
  by (simp_all add: trail_false_lit_def trail_false_cls_def)

lemma not_trail_defined_lit_Nil[simp]: "\<not> trail_defined_lit [] L"
  by (simp add: trail_defined_lit_iff_true_or_false)

lemma trail_false_lit_if_trail_false_suffix:
  "suffix \<Gamma>' \<Gamma> \<Longrightarrow> trail_false_lit \<Gamma>' K \<Longrightarrow> trail_false_lit \<Gamma> K"
  by (meson image_mono set_mono_suffix subsetD trail_false_lit_def)

lemma trail_false_cls_if_trail_false_suffix:
  "suffix \<Gamma>' \<Gamma> \<Longrightarrow> trail_false_cls \<Gamma>' C \<Longrightarrow> trail_false_cls \<Gamma> C"
  using trail_false_cls_def trail_false_lit_if_trail_false_suffix by metis

lemma trail_interp_Cons: "trail_interp (Ln # \<Gamma>) = trail_interp [Ln] \<union> trail_interp \<Gamma>"
  unfolding trail_interp_def by simp

lemma trail_interp_Cons': "trail_interp (Ln # \<Gamma>) = (case fst Ln of Pos A \<Rightarrow> {A} | Neg A \<Rightarrow> {}) \<union> trail_interp \<Gamma>"
  unfolding trail_interp_def by simp

lemma true_lit_thick_unionD: "(I1 \<union> I2) \<TTurnstile>l L \<Longrightarrow> I1 \<TTurnstile>l L \<or> I2 \<TTurnstile>l L"
  by auto

lemma subtrail_falseI:
  assumes tr_false: "trail_false_cls ((L, Cl) # \<Gamma>) C" and L_not_in: "-L \<notin># C"
  shows "trail_false_cls \<Gamma> C"
  unfolding trail_false_cls_def
proof (rule ballI)
  fix M
  assume M_in: "M \<in># C"

  from M_in L_not_in have M_neq_L: "M \<noteq> -L" by auto

  from M_in tr_false have tr_false_lit_M: "trail_false_lit ((L, Cl) # \<Gamma>) M"
    unfolding trail_false_cls_def by simp
  thus "trail_false_lit \<Gamma> M"
    unfolding trail_false_lit_def
    using M_neq_L
    by (cases L; cases M) (simp_all add: trail_interp_def trail_false_lit_def)
qed

lemma trail_false_cls_ignores_duplicates:
  "set_mset C = set_mset D \<Longrightarrow> trail_false_cls \<Gamma> C \<longleftrightarrow> trail_false_cls \<Gamma> D"
  by (simp add: trail_false_cls_def)

lemma ball_trail_propagate_is_ground_lit:
  assumes "\<forall>x\<in>set \<Gamma>. is_ground_lit (fst x)" and "is_ground_lit (L \<cdot>l \<sigma>)"
  shows "\<forall>x\<in>set (trail_propagate \<Gamma> L C \<sigma>). is_ground_lit (fst x)"
  unfolding propagate_lit_def
  using assms by simp

lemma ball_trail_decide_is_ground_lit:
  assumes "\<forall>x\<in>set \<Gamma>. is_ground_lit (fst x)" and "is_ground_lit L"
  shows "\<forall>x\<in>set (trail_decide \<Gamma> L). is_ground_lit (fst x)"
  using assms
  by (simp add: decide_lit_def)

lemma trail_false_cls_subst_mgu_before_grounding:
  assumes tr_false_cls: "trail_false_cls \<Gamma> ((D + {#L, L'#}) \<cdot> \<sigma>)" and
    imgu_\<mu>: "is_imgu \<mu> {{atm_of L, atm_of L'}}" and
    unif_\<sigma>: "is_unifiers \<sigma> {{atm_of L, atm_of L'}}"
  shows "trail_false_cls \<Gamma> ((D + {#L#}) \<cdot> \<mu> \<cdot> \<sigma>)"
  unfolding trail_false_cls_def
proof (rule ballI)
  fix K
  assume "K \<in># (D + {#L#}) \<cdot> \<mu> \<cdot> \<sigma>"
  hence "K \<in># D \<cdot> \<mu> \<cdot> \<sigma> \<or> K = L  \<cdot>l \<mu> \<cdot>l \<sigma>" by force
  thus "trail_false_lit \<Gamma> K"
  proof (elim disjE)
    show "K \<in># D \<cdot> \<mu> \<cdot> \<sigma> \<Longrightarrow> trail_false_lit \<Gamma> K"
      using imgu_\<mu> unif_\<sigma>
      by (metis is_imgu_def subst_cls_comp_subst subst_cls_union tr_false_cls trail_false_cls_def
          union_iff)
  next
    have "L \<cdot>l \<mu> \<cdot>l \<sigma> = L \<cdot>l \<sigma>"
      using imgu_\<mu> unif_\<sigma> by (metis is_imgu_def subst_lit_comp_subst)
    thus "K = L \<cdot>l \<mu> \<cdot>l \<sigma> \<Longrightarrow> trail_false_lit \<Gamma> K"
      by (auto intro: tr_false_cls[unfolded trail_false_cls_def, rule_format])
  qed
qed

lemma trail_defined_lit_iff_defined_uminus: "trail_defined_lit \<Gamma> L \<longleftrightarrow> trail_defined_lit \<Gamma> (-L)"
  by (auto simp add: trail_defined_lit_def)

lemma trail_defined_lit_iff: "trail_defined_lit \<Gamma> L \<longleftrightarrow> atm_of L \<in> atm_of ` fst ` set \<Gamma>"
  by (simp add: atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set trail_defined_lit_def)

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

inductive trail_consistent where
  Nil[simp]: "trail_consistent []" |
  Cons: "\<not> trail_defined_lit \<Gamma> L \<Longrightarrow> trail_consistent \<Gamma> \<Longrightarrow> trail_consistent ((L, u) # \<Gamma>)"

lemma trail_consistent_appendD: "trail_consistent (\<Gamma> @ \<Gamma>') \<Longrightarrow> trail_consistent \<Gamma>'"
  by (induction \<Gamma>) (auto elim: trail_consistent.cases)

lemma trail_consistent_if_suffix:
  "trail_consistent \<Gamma> \<Longrightarrow> suffix \<Gamma>' \<Gamma> \<Longrightarrow> trail_consistent \<Gamma>'"
  by (auto simp: suffix_def intro: trail_consistent_appendD)

lemma trail_interp_lit_if_trail_true:
  shows "trail_consistent \<Gamma> \<Longrightarrow> trail_true_lit \<Gamma> L \<Longrightarrow> trail_interp \<Gamma> \<TTurnstile>l L"
proof (induction \<Gamma> rule: trail_consistent.induct)
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
          using Cons.hyps(1)
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

lemma trail_interp_cls_if_trail_true:
  assumes "trail_consistent \<Gamma>" and "trail_true_cls \<Gamma> C"
  shows "trail_interp \<Gamma> \<TTurnstile> C"
proof -
  from \<open>trail_true_cls \<Gamma> C\<close> obtain L where "L \<in># C" and "trail_true_lit \<Gamma> L"
    by (auto simp: trail_true_cls_def)
  show ?thesis
    unfolding true_cls_def
  proof (rule bexI[OF _ \<open>L \<in># C\<close>])
    show "trail_interp \<Gamma> \<TTurnstile>l L"
      by (rule trail_interp_lit_if_trail_true[OF \<open>trail_consistent \<Gamma>\<close> \<open>trail_true_lit \<Gamma> L\<close>])
  qed
qed

lemma trail_true_cls_iff_trail_interp_entails:
  assumes "trail_consistent \<Gamma>" "\<forall>L \<in># C. trail_defined_lit \<Gamma> L"
  shows "trail_true_cls \<Gamma> C \<longleftrightarrow> trail_interp \<Gamma> \<TTurnstile> C"
proof (rule iffI)
  assume "trail_true_cls \<Gamma> C"
  thus "trail_interp \<Gamma> \<TTurnstile> C"
    using assms(1) trail_interp_cls_if_trail_true by fast
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
      by (metis assms(1) assms(2) trail_defined_lit_def trail_interp_lit_if_trail_true
          trail_true_lit_def true_lit_simps(2) uminus_Pos)
  next
    case (Neg t)
    then show ?thesis
      by (metis \<open>L \<in># C\<close> \<open>trail_interp \<Gamma> \<TTurnstile>l L\<close> assms(1) assms(2) trail_defined_lit_def
          trail_interp_lit_if_trail_true trail_true_cls_def trail_true_lit_def true_lit_simps(1,2)
          uminus_Neg)
  qed
qed

lemma trail_false_cls_iff_not_trail_interp_entails:
  assumes "trail_consistent \<Gamma>" "\<forall>L \<in># C. trail_defined_lit \<Gamma> L"
  shows "trail_false_cls \<Gamma> C \<longleftrightarrow> \<not> trail_interp \<Gamma> \<TTurnstile> C"
proof (rule iffI)
  show "trail_false_cls \<Gamma> C \<Longrightarrow> \<not> trail_interp \<Gamma> \<TTurnstile> C"
    by (metis (mono_tags, opaque_lifting) assms(1) trail_false_cls_def trail_false_lit_def
        trail_interp_lit_if_trail_true trail_true_lit_def true_cls_def true_lit_iff
        true_lit_simps(1) true_lit_simps(2) uminus_Neg uminus_Pos)
next
  show "\<not> trail_interp \<Gamma> \<TTurnstile> C \<Longrightarrow> trail_false_cls \<Gamma> C"
    using assms(1) assms(2) trail_defined_cls_def trail_interp_cls_if_trail_true
      trail_true_or_false_cls_if_defined by blast
qed

inductive trail_closures_false where
  Nil[simp]: "trail_closures_false []" |
  Cons:
    "(case u of None \<Rightarrow> True | Some (D, _, \<gamma>) \<Rightarrow> trail_false_cls \<Gamma> (D \<cdot> \<gamma>)) \<Longrightarrow>
    trail_closures_false \<Gamma> \<Longrightarrow> trail_closures_false ((L, u) # \<Gamma>)"

lemma trail_closures_false_ConsD: "trail_closures_false (Ln # \<Gamma>) \<Longrightarrow> trail_closures_false \<Gamma>"
  by (auto elim: trail_closures_false.cases)

lemma trail_closures_false_appendD: "trail_closures_false (\<Gamma> @ \<Gamma>') \<Longrightarrow> trail_closures_false \<Gamma>'"
  by (induction \<Gamma>) (auto elim: trail_closures_false.cases)

lemma is_ground_lit_if_true_in_ground_trail:
  assumes "\<forall>L \<in> fst ` set \<Gamma>. is_ground_lit L"
  shows "trail_true_lit \<Gamma> L \<Longrightarrow> is_ground_lit L"
  using assms by (metis trail_true_lit_def)

lemma is_ground_lit_if_false_in_ground_trail:
  assumes "\<forall>L \<in> fst ` set \<Gamma>. is_ground_lit L"
  shows "trail_false_lit \<Gamma> L \<Longrightarrow> is_ground_lit L"
  using assms by (metis trail_false_lit_def atm_of_uminus is_ground_lit_def)

lemma is_ground_lit_if_defined_in_ground_trail:
  assumes "\<forall>L \<in> fst ` set \<Gamma>. is_ground_lit L"
  shows "trail_defined_lit \<Gamma> L \<Longrightarrow> is_ground_lit L"
  using assms is_ground_lit_if_true_in_ground_trail is_ground_lit_if_false_in_ground_trail
  unfolding trail_defined_lit_iff_true_or_false
  by fast

lemma is_ground_cls_if_false_in_ground_trail:
  assumes "\<forall>L \<in> fst ` set \<Gamma>. is_ground_lit L"
  shows "trail_false_cls \<Gamma> C \<Longrightarrow> is_ground_cls C"
  unfolding trail_false_cls_def is_ground_cls_def
  using assms by (auto intro: is_ground_lit_if_false_in_ground_trail)


section \<open>SCL Calculus\<close>

locale scl = renaming_apart renaming_vars
  for renaming_vars :: "'v set \<Rightarrow> 'v \<Rightarrow> 'v" +
  fixes less_B :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool" (infix "\<prec>\<^sub>B" 50)
  assumes
    finite_less_B: "\<And>\<beta>. finite {x. x \<prec>\<^sub>B \<beta>}"
begin


subsection \<open>Lemmas About @{term less_B}\<close>

lemma lits_less_B_conv: "{L. atm_of L \<prec>\<^sub>B \<beta>} = (\<Union>x\<in>{x. x \<prec>\<^sub>B \<beta>}. {Pos x, Neg x})"
  by (rule Collect_lits_from_atms_conv)

lemma lits_eq_conv: "{L. atm_of L = \<beta>} = {Pos \<beta>, Neg \<beta>}"
  by (rule Collect_lits_from_atms_conv[of "\<lambda>x. x = \<beta>", simplified])

lemma lits_less_eq_B_conv:
  "{L. atm_of L \<prec>\<^sub>B \<beta> \<or> atm_of L = \<beta>} = insert (Pos \<beta>) (insert (Neg \<beta>) {L. atm_of L \<prec>\<^sub>B \<beta>})"
  unfolding Collect_disj_eq lits_eq_conv by simp

lemma finite_lits_less_B: "finite {L. atm_of L \<prec>\<^sub>B \<beta>}"
  unfolding lits_less_B_conv
proof (rule finite_UN_I)
  show "finite {x. x \<prec>\<^sub>B \<beta>}"
    by (rule finite_less_B)
next
  show "\<And>x. x \<in> {x. x \<prec>\<^sub>B \<beta>} \<Longrightarrow> finite {Pos x, Neg x}"
    by simp
qed

lemma finite_lits_less_eq_B: "finite {L. atm_of L \<prec>\<^sub>B \<beta> \<or> atm_of L = \<beta>}"
  using finite_lits_less_B by (simp add: lits_less_eq_B_conv)

lemma Collect_ball_eq_Pow_Collect: "{X. \<forall>x \<in> X. P x} = Pow {x. P x}"
  by blast

lemma finite_lit_clss_nodup_less_B: "finite {C. \<forall>L \<in># C. atm_of L \<prec>\<^sub>B \<beta> \<and> count C L = 1}"
proof -
  have 1: "(\<forall>L \<in># C. P L \<and> count C L = 1) \<longleftrightarrow> (\<exists>C'. C = mset_set C' \<and> finite C' \<and> (\<forall>L \<in> C'. P L))"
    for C P
    by (smt (verit) count_eq_zero_iff count_mset_set' finite_set_mset finite_set_mset_mset_set
        multiset_eqI)

  have 2: "finite {C'. \<forall>L\<in>C'. atm_of L \<prec>\<^sub>B \<beta>}"
    unfolding Collect_ball_eq_Pow_Collect finite_Pow_iff
    by (rule finite_lits_less_B)

  show ?thesis
    unfolding 1
    unfolding setcompr_eq_image
    apply (rule finite_imageI)
    using 2 by simp
qed


subsection \<open>Rules\<close>

inductive propagate :: "('f, 'v) term clause fset \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) state \<Rightarrow>
  ('f, 'v) state \<Rightarrow> bool" for N \<beta> where
  propagateI: "C |\<in>| N |\<union>| U \<Longrightarrow> C = add_mset L C' \<Longrightarrow> is_ground_cls (C \<cdot> \<gamma>) \<Longrightarrow>
    \<forall>K \<in># C \<cdot> \<gamma>. atm_of K \<prec>\<^sub>B \<beta> \<Longrightarrow>
    C\<^sub>0 = {#K \<in># C'. K \<cdot>l \<gamma> \<noteq> L \<cdot>l \<gamma>#} \<Longrightarrow> C\<^sub>1 = {#K \<in># C'. K \<cdot>l \<gamma> = L \<cdot>l \<gamma>#} \<Longrightarrow>
    trail_false_cls \<Gamma> (C\<^sub>0 \<cdot> \<gamma>) \<Longrightarrow> \<not> trail_defined_lit \<Gamma> (L \<cdot>l \<gamma>) \<Longrightarrow>
    is_imgu \<mu> {atm_of ` set_mset (add_mset L C\<^sub>1)} \<Longrightarrow>
    propagate N \<beta> (\<Gamma>, U, None) (trail_propagate \<Gamma> (L \<cdot>l \<mu>) (C\<^sub>0 \<cdot> \<mu>) \<gamma>, U, None)"

lemma "C |\<in>| N |\<union>| U \<Longrightarrow> C = add_mset L C' \<Longrightarrow> is_ground_cls (C \<cdot> \<gamma>) \<Longrightarrow>
    \<forall>K \<in># C. atm_of (K \<cdot>l \<gamma>) \<prec>\<^sub>B \<beta> \<Longrightarrow>
    C\<^sub>0 = {#K \<in># C'. K \<cdot>l \<gamma> \<noteq> L \<cdot>l \<gamma>#} \<Longrightarrow> C\<^sub>1 = {#K \<in># C'. K \<cdot>l \<gamma> = L \<cdot>l \<gamma>#} \<Longrightarrow>
    trail_false_cls \<Gamma> (C\<^sub>0 \<cdot> \<gamma>) \<Longrightarrow> \<not> trail_defined_lit \<Gamma> (L \<cdot>l \<gamma>) \<Longrightarrow>
    is_imgu \<mu> {atm_of ` set_mset (add_mset L C\<^sub>1)} \<Longrightarrow>
    propagate N \<beta> (\<Gamma>, U, None) (trail_propagate \<Gamma> (L \<cdot>l \<mu>) (C\<^sub>0 \<cdot> \<mu>) \<gamma>, U, None)"
  by (auto intro!: propagateI)

(* Whatch out for equality! *)

inductive decide :: "('f, 'v) term clause fset \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) state \<Rightarrow>
  ('f, 'v) state \<Rightarrow> bool" for N \<beta> where
  decideI: "L \<in> \<Union>(set_mset ` fset N) \<Longrightarrow> is_ground_lit (L \<cdot>l \<gamma>) \<Longrightarrow>
    \<not> trail_defined_lit \<Gamma> (L \<cdot>l \<gamma>) \<Longrightarrow> atm_of L \<cdot>a \<gamma> \<prec>\<^sub>B \<beta> \<Longrightarrow>
    decide N \<beta> (\<Gamma>, U, None) (trail_decide \<Gamma> (L \<cdot>l \<gamma>), U, None)"

lemma "add_mset L C |\<in>| N \<Longrightarrow> is_ground_lit (L \<cdot>l \<gamma>) \<Longrightarrow>
    \<not> trail_defined_lit \<Gamma> (L \<cdot>l \<gamma>) \<Longrightarrow> atm_of L \<cdot>a \<gamma> \<prec>\<^sub>B \<beta> \<Longrightarrow>
    decide N \<beta> (\<Gamma>, U, None) (trail_decide \<Gamma> (L \<cdot>l \<gamma>), U, None)"
  by (auto simp: fmember_iff_member_fset intro!: decideI)

inductive conflict :: "('f, 'v) term clause fset \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) state \<Rightarrow>
  ('f, 'v) state \<Rightarrow> bool" for N \<beta> where
  conflictI: "D |\<in>| N |\<union>| U \<Longrightarrow> is_ground_cls (D \<cdot> \<gamma>) \<Longrightarrow> trail_false_cls \<Gamma> (D \<cdot> \<gamma>) \<Longrightarrow>
    conflict N \<beta> (\<Gamma>, U, None) (\<Gamma>, U, Some (D, \<gamma>))"

inductive skip :: "('f, 'v) term clause fset \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) state \<Rightarrow>
  ('f, 'v) state \<Rightarrow> bool" for N \<beta> where
  skipI: "-L \<notin># D \<cdot> \<sigma> \<Longrightarrow>
    skip N \<beta> ((L, n) # \<Gamma>, U, Some (D, \<sigma>)) (\<Gamma>, U, Some (D, \<sigma>))"

inductive factorize :: "('f, 'v) term clause fset \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) state \<Rightarrow>
  ('f, 'v) state \<Rightarrow> bool" for N \<beta> where
  factorizeI: "L \<cdot>l \<gamma> = L' \<cdot>l \<gamma> \<Longrightarrow> is_imgu \<mu> {{atm_of L, atm_of L'}} \<Longrightarrow>
    factorize N \<beta> (\<Gamma>, U, Some (add_mset L' (add_mset L D), \<gamma>)) (\<Gamma>, U, Some (add_mset L D \<cdot> \<mu>, \<gamma>))"

inductive resolve :: "('f, 'v) term clause fset \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) state \<Rightarrow>
  ('f, 'v) state \<Rightarrow> bool" for N \<beta> where
  resolveI: "\<Gamma> = trail_propagate \<Gamma>' K D \<gamma>\<^sub>D \<Longrightarrow> K \<cdot>l \<gamma>\<^sub>D = -(L \<cdot>l \<gamma>\<^sub>C) \<Longrightarrow>
    is_renaming \<rho>\<^sub>C \<Longrightarrow> is_renaming \<rho>\<^sub>D \<Longrightarrow>
    vars_cls (add_mset L C \<cdot> \<rho>\<^sub>C) \<inter> vars_cls (add_mset K D \<cdot> \<rho>\<^sub>D) = {} \<Longrightarrow>
    is_imgu \<mu> {{atm_of L \<cdot>a \<rho>\<^sub>C, atm_of K \<cdot>a \<rho>\<^sub>D}} \<Longrightarrow>
    is_grounding_merge \<gamma>
      (vars_cls (add_mset L C \<cdot> \<rho>\<^sub>C)) (rename_subst_domain \<rho>\<^sub>C \<gamma>\<^sub>C)
      (vars_cls (add_mset K D \<cdot> \<rho>\<^sub>D)) (rename_subst_domain \<rho>\<^sub>D \<gamma>\<^sub>D) \<Longrightarrow>
    resolve N \<beta> (\<Gamma>, U, Some (add_mset L C, \<gamma>\<^sub>C)) (\<Gamma>, U, Some ((C \<cdot> \<rho>\<^sub>C + D \<cdot> \<rho>\<^sub>D) \<cdot> \<mu>, \<gamma>))"

(* Think about showing that the more specific rule from the paper is an instance of this generic rule. *)

inductive backtrack :: "('f, 'v) term clause fset \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) state \<Rightarrow>
  ('f, 'v) state \<Rightarrow> bool" for N \<beta> where
  backtrackI: "\<Gamma> = trail_decide (\<Gamma>' @ \<Gamma>'') K \<Longrightarrow> K = - (L \<cdot>l \<sigma>) \<Longrightarrow>
    \<nexists>\<gamma>. is_ground_cls (add_mset L D \<cdot> \<gamma>) \<and> trail_false_cls \<Gamma>'' (add_mset L D \<cdot> \<gamma>) \<Longrightarrow>
    backtrack N \<beta> (\<Gamma>, U, Some (add_mset L D, \<sigma>)) (\<Gamma>'', finsert (add_mset L D) U, None)"

definition scl :: "('f, 'v) term clause fset \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) state \<Rightarrow>
  ('f, 'v) state \<Rightarrow> bool" where
  "scl N \<beta> S S' \<longleftrightarrow> propagate N \<beta> S S' \<or> decide N \<beta> S S' \<or> conflict N \<beta> S S' \<or> skip N \<beta> S S' \<or>
    factorize N \<beta> S S' \<or> resolve N \<beta> S S' \<or> backtrack N \<beta> S S'"

text \<open>Note that, in contrast to Fiori and Weidenbach (CADE 2019), the set @{term N} of initial
clauses and the ground atom @{term \<beta>} are parameters of the relation instead of being repeated twice
in the states. This is to highlight the fact that they are constant.\<close>


subsection \<open>Well-Defined\<close>

lemma propagate_well_defined:
  assumes "propagate N \<beta> S S'"
  shows
    "\<not> decide N \<beta> S S'"
    "\<not> conflict N \<beta> S S'"
    "\<not> skip N \<beta> S S'"
    "\<not> factorize N \<beta> S S'"
    "\<not> resolve N \<beta> S S'"
    "\<not> backtrack N \<beta> S S'"
  using assms
  by (auto elim!: propagate.cases decide.cases conflict.cases skip.cases factorize.cases
          resolve.cases backtrack.cases
        simp: decide_lit_def propagate_lit_def)

lemma decide_well_defined:
  assumes "decide N \<beta> S S'"
  shows
    "\<not> propagate N \<beta> S S'"
    "\<not> conflict N \<beta> S S'"
    "\<not> skip N \<beta> S S'"
    "\<not> factorize N \<beta> S S'"
    "\<not> resolve N \<beta> S S'"
    "\<not> backtrack N \<beta> S S'"
  using assms
  by (auto elim!: propagate.cases decide.cases conflict.cases skip.cases factorize.cases
          resolve.cases backtrack.cases
        simp: decide_lit_def propagate_lit_def)

lemma conflict_well_defined:
  assumes "conflict N \<beta> S S'"
  shows
    "\<not> propagate N \<beta> S S'"
    "\<not> decide N \<beta> S S'"
    "\<not> skip N \<beta> S S'"
    "\<not> factorize N \<beta> S S'"
    "\<not> resolve N \<beta> S S'"
    "\<not> backtrack N \<beta> S S'"
  using assms
  by (auto elim!: propagate.cases decide.cases conflict.cases skip.cases factorize.cases
          resolve.cases backtrack.cases
        simp: decide_lit_def propagate_lit_def)

lemma skip_well_defined:
  assumes "skip N \<beta> S S'"
  shows
    "\<not> propagate N \<beta> S S'"
    "\<not> decide N \<beta> S S'"
    "\<not> conflict N \<beta> S S'"
    "\<not> factorize N \<beta> S S'"
    "\<not> resolve N \<beta> S S'"
    "\<not> backtrack N \<beta> S S'"
  using assms
  by (auto elim!: propagate.cases decide.cases conflict.cases skip.cases factorize.cases
          resolve.cases backtrack.cases
        simp: decide_lit_def propagate_lit_def)

lemma factorize_well_defined:
  assumes "factorize N \<beta> S S'"
  shows
    "\<not> propagate N \<beta> S S'"
    "\<not> decide N \<beta> S S'"
    "\<not> conflict N \<beta> S S'"
    "\<not> skip N \<beta> S S'"
    (* "\<not> resolve N \<beta> S S'" *)
    "\<not> backtrack N \<beta> S S'"
  using assms
  by (auto elim!: propagate.cases decide.cases conflict.cases skip.cases factorize.cases
          resolve.cases backtrack.cases
        simp: decide_lit_def propagate_lit_def)

lemma resolve_well_defined:
  assumes "resolve N \<beta> S S'"
  shows
    "\<not> propagate N \<beta> S S'"
    "\<not> decide N \<beta> S S'"
    "\<not> conflict N \<beta> S S'"
    "\<not> skip N \<beta> S S'"
    (* "\<not> factorize N \<beta> S S'" *)
    "\<not> backtrack N \<beta> S S'"
  using assms
  by (auto elim!: propagate.cases decide.cases conflict.cases skip.cases factorize.cases
          resolve.cases backtrack.cases
        simp: decide_lit_def propagate_lit_def)

lemma backtrack_well_defined:
  assumes "backtrack N \<beta> S S'"
  shows
    "\<not> propagate N \<beta> S S'"
    "\<not> decide N \<beta> S S'"
    "\<not> conflict N \<beta> S S'"
    "\<not> skip N \<beta> S S'"
    "\<not> factorize N \<beta> S S'"
    "\<not> resolve N \<beta> S S'"
  using assms
  by (auto elim!: propagate.cases decide.cases conflict.cases skip.cases factorize.cases
          resolve.cases backtrack.cases
        simp: decide_lit_def propagate_lit_def)


subsection \<open>Miscellaneous Lemmas\<close>

lemma conflict_set_after_factorization:
  assumes fact: "factorize N \<beta> S S'" and conflict_S: "state_conflict S = Some (C, \<gamma>)"
  shows "\<exists>C' \<gamma>'. state_conflict S' = Some (C', \<gamma>') \<and> set_mset (C \<cdot> \<gamma>) = set_mset (C' \<cdot> \<gamma>')"
  using fact
proof (cases N \<beta> S S' rule: factorize.cases)
  case (factorizeI L \<gamma> L' \<mu> \<Gamma> U D)

  from \<open>L \<cdot>l \<gamma> = L' \<cdot>l \<gamma>\<close> have "is_unifier \<gamma> {atm_of L, atm_of L'}"
    by (auto intro!: is_unifier_alt[THEN iffD2] intro: subst_atm_of_eqI)
  hence "\<mu> \<odot> \<gamma> = \<gamma>"
    using \<open>is_imgu \<mu> {{atm_of L, atm_of L'}}\<close>
    by (simp add: is_imgu_def is_unifiers_def)

  have "L \<cdot>l \<mu> \<cdot>l \<gamma> = L \<cdot>l \<gamma>"
    using \<open>\<mu> \<odot> \<gamma> = \<gamma>\<close>
    by (metis subst_lit_comp_subst)

  moreover have "D \<cdot> \<mu> \<cdot> \<gamma> = D \<cdot> \<gamma>"
    using \<open>\<mu> \<odot> \<gamma> = \<gamma>\<close>
    by (metis subst_cls_comp_subst)

  ultimately show ?thesis
    using conflict_S[symmetric]
    unfolding factorizeI(1,2)
    by (simp add: \<open>L \<cdot>l \<gamma> = L' \<cdot>l \<gamma>\<close>)
qed

lemma not_trail_false_ground_cls_if_no_conflict:
  assumes
    no_conf: "\<nexists>S'. conflict N \<beta> S S'" and
    could_conf: "state_conflict S = None" and
    C_in: "C |\<in>| N |\<union>| state_learned S" and
    gr_C_\<gamma>: "is_ground_cls (C \<cdot> \<gamma>)"
  shows "\<not> trail_false_cls (state_trail S) (C \<cdot> \<gamma>)"
proof (rule notI)
  assume tr_false: "trail_false_cls (state_trail S) (C \<cdot> \<gamma>)"

  from could_conf obtain \<Gamma> U where S_def: "S = (\<Gamma>, U, None)"
    by (metis prod_cases3 state_conflict_simp)

  have "conflict N \<beta> (\<Gamma>, U, None) (\<Gamma>, U,
    Some (C, restrict_subst_domain (vars_cls C) \<gamma>))"
  proof (rule conflictI)
    show "C |\<in>| N |\<union>| U"
      using C_in by (simp add: S_def)
  next
    show "is_ground_cls (C \<cdot> restrict_subst_domain (vars_cls C) \<gamma>)"
      using gr_C_\<gamma> by (simp add: subst_cls_restrict_subst_domain)
  next
    show "trail_false_cls \<Gamma> (C \<cdot> restrict_subst_domain (vars_cls C) \<gamma>)"
      using tr_false by (simp add: S_def subst_cls_restrict_subst_domain)
  qed
  with no_conf show False
    by (simp add: S_def)
qed

lemma scl_mempty_not_in_sate_learned:
  "scl N \<beta> S S' \<Longrightarrow> {#} |\<notin>| state_learned S \<Longrightarrow> {#} |\<notin>| state_learned S'"
  unfolding scl_def
  by (elim disjE propagate.cases decide.cases conflict.cases skip.cases factorize.cases
      resolve.cases backtrack.cases) simp_all

lemma conflict_if_mempty_in_initial_clauses_and_no_conflict:
  assumes "{#} |\<in>| N" and "state_conflict S = None"
  shows "conflict N \<beta> S (state_trail S, state_learned S, Some ({#}, Var))"
proof -
  from assms(2) obtain \<Gamma> U where S_def: "S = (\<Gamma>, U, None)"
    by (metis snd_conv state_conflict_def surj_pair)

  show ?thesis
    unfolding S_def state_trail_simp state_learned_simp
  proof (rule conflictI[of "{#}" N _  Var _ _, unfolded subst_cls_empty])
    from assms(1) show "{#} |\<in>| N |\<union>| U"
      by simp
  qed simp_all
qed

lemma conflict_initial_state_if_mempty_in_intial_clauses:
  "{#} |\<in>| N \<Longrightarrow> conflict N \<beta> initial_state ([], {||}, Some ({#}, Var))"
  using conflict_if_mempty_in_initial_clauses_and_no_conflict by auto

lemma conflict_empty_trail:
  assumes conf: "conflict N \<beta> S S'" and empty_trail: "state_trail S = []"
  shows "{#} |\<in>| N |\<union>| state_learned S"
  using conf
proof (cases N \<beta> S S' rule: conflict.cases)
  case (conflictI D U \<gamma> \<Gamma>)
  from empty_trail have "\<Gamma> = []"
    unfolding conflictI(1,2) by simp
  with \<open>trail_false_cls \<Gamma> (D \<cdot> \<gamma>)\<close> have "D = {#}"
    using not_trail_false_Nil(2) subst_cls_empty_iff by blast
  with \<open>D |\<in>| N |\<union>| U\<close> show ?thesis
    unfolding conflictI(1,2) by simp
qed

lemma conflict_empty_trail':
  assumes "{#} |\<in>| N |\<union>| U"
  shows "\<exists>S'. conflict N \<beta> ([], U, None) S'"
  by (metis assms is_ground_cls_empty not_trail_false_ground_cls_if_no_conflict state_conflict_simp
      state_learned_simp subst_cls_empty trail_false_cls_mempty)

lemma mempty_in_iff_ex_conflict: "{#} |\<in>| N |\<union>| U \<longleftrightarrow> (\<exists>S'. conflict N \<beta> ([], U, None) S')"
  by (metis conflict_empty_trail conflict_empty_trail' state_learned_simp state_trail_simp)

lemma conflict_initial_state_only_with_mempty:
  assumes "conflict N \<beta> initial_state S"
  shows "\<exists>\<gamma>. S = ([], {||}, Some ({#}, \<gamma>))"
  using assms(1)
proof (cases rule: conflict.cases)
  case (conflictI D \<gamma>)

  from \<open>trail_false_cls [] (D \<cdot> \<gamma>)\<close> have "D \<cdot> \<gamma> = {#}"
    using not_trail_false_Nil(2) by blast
  hence "D = {#}"
    by simp
  thus ?thesis
    using \<open>S = ([], {||}, Some (D, \<gamma>))\<close> by simp
qed

lemma no_more_step_if_conflict_mempty:
  assumes "state_trail S = []" "state_conflict S = Some ({#}, \<gamma>)"
  shows "\<nexists>S'. scl N \<beta> S S'"
  apply (rule notI)
  unfolding scl_def
  apply (insert assms)
  by (elim exE disjE propagate.cases decide.cases conflict.cases skip.cases factorize.cases
      resolve.cases backtrack.cases) simp_all

lemma ex_conflict_if_trail_false_cls:
  assumes tr_false_\<Gamma>_D: "trail_false_cls \<Gamma> D" and D_in: "D \<in> grounding_of_clss (fset N \<union> fset U)"
  shows "\<exists>S'. conflict N \<beta> (\<Gamma>, U, None) S'"
proof -
  from D_in obtain D' \<gamma>' where
    D'_in: "D' |\<in>| N |\<union>| U" and D_def: "D = D' \<cdot> \<gamma>'" and gr_D_\<gamma>: "is_ground_cls (D' \<cdot> \<gamma>')"
    unfolding grounding_of_clss_def grounding_of_cls_def
    by (smt (verit, ccfv_threshold) D_in UN_iff grounding_ground mem_Collect_eq notin_fset
        union_fset)

  define \<gamma> where
    "\<gamma> \<equiv> restrict_subst_domain (vars_cls D') \<gamma>'"

  have "conflict N \<beta> (\<Gamma>, U, None) (\<Gamma>, U, Some (D', \<gamma>))"
  proof (rule conflictI[OF D'_in])
    show "is_ground_cls (D' \<cdot> \<gamma>)"
      using gr_D_\<gamma> by (simp add: \<gamma>_def subst_cls_restrict_subst_domain)
  next
    show "trail_false_cls \<Gamma> (D' \<cdot> \<gamma>)"
      using tr_false_\<Gamma>_D by (simp add: D_def \<gamma>_def subst_cls_restrict_subst_domain)
  qed
  thus ?thesis
    by auto
qed

lemma no_conflict_tail_trail:
  assumes "\<nexists>S. conflict N \<beta> (Ln # \<Gamma>, U, None) S"
  shows "\<nexists>S. conflict N \<beta> (\<Gamma>, U, None) S"
proof (rule notI, erule exE)
  fix S assume "conflict N \<beta> (\<Gamma>, U, None) S"
  hence "\<exists>S. conflict N \<beta> (Ln # \<Gamma>, U, None) S"
  proof (cases N \<beta> _ S rule: conflict.cases)
    case (conflictI D \<gamma>)
    have "conflict N \<beta> (Ln # \<Gamma>, U, None) (Ln # \<Gamma>, U, Some (D, \<gamma>))"
    proof (rule conflict.conflictI)
      show "D |\<in>| N |\<union>| U"
        by (rule conflictI)
    next
      show "is_ground_cls (D \<cdot> \<gamma>)"
        by (rule conflictI)
    next
      show "trail_false_cls (Ln # \<Gamma>) (D \<cdot> \<gamma>)"
        using \<open>trail_false_cls \<Gamma> (D \<cdot> \<gamma>)\<close>
        by (simp add: trail_false_cls_def trail_false_lit_def)
    qed
    thus ?thesis
      by metis
  qed
  with assms show False
    by argo
qed

lemma subst_domain_rename_subst_domain_subset_vars_cls_subst_cls:
  assumes "\<forall>x. is_Var (\<rho>\<^sub>C x)" and
    dom_\<gamma>\<^sub>C: "subst_domain \<gamma>\<^sub>C \<subseteq> vars_cls (add_mset L C)"
  shows "subst_domain (rename_subst_domain \<rho>\<^sub>C \<gamma>\<^sub>C) \<subseteq> vars_cls (add_mset L C \<cdot> \<rho>\<^sub>C)"
proof -
  have "subst_domain (rename_subst_domain \<rho>\<^sub>C \<gamma>\<^sub>C) \<subseteq> the_Var ` \<rho>\<^sub>C ` subst_domain \<gamma>\<^sub>C"
    using subst_domain_rename_subst_domain_subset[OF \<open>\<forall>x. is_Var (\<rho>\<^sub>C x)\<close>] by simp
  also have "\<dots> \<subseteq> the_Var ` \<rho>\<^sub>C ` vars_cls (add_mset L C)"
    using dom_\<gamma>\<^sub>C by auto
  also have "\<dots> = (\<Union>x \<in> vars_cls (add_mset L C). vars_term (\<rho>\<^sub>C x))"
    using image_the_Var_image_subst_renaming_eq[OF \<open>\<forall>x. is_Var (\<rho>\<^sub>C x)\<close>] by simp
  also have "\<dots> = vars_cls (add_mset L C \<cdot> \<rho>\<^sub>C)"
    using vars_subst_cls_eq by metis
  finally show dom_ren_dom_\<rho>\<^sub>C_\<gamma>\<^sub>C:
    "subst_domain (rename_subst_domain \<rho>\<^sub>C \<gamma>\<^sub>C) \<subseteq> vars_cls (add_mset L C \<cdot> \<rho>\<^sub>C)"
    by assumption
qed

lemma renamed_comp_renamed_simp:
  fixes \<gamma>\<^sub>C \<gamma>\<^sub>D
  assumes
    "K \<cdot>l \<gamma>\<^sub>D = - (L \<cdot>l \<gamma>\<^sub>C)" and
    ground_conf: "is_ground_cls (add_mset L C \<cdot> \<gamma>\<^sub>C)" and
    ground_prop: "is_ground_cls (add_mset K D \<cdot> \<gamma>\<^sub>D)" and
    dom_\<gamma>\<^sub>D: "subst_domain \<gamma>\<^sub>D \<subseteq> vars_cls (add_mset K D)" and
    ren_\<rho>\<^sub>C: "is_renaming \<rho>\<^sub>C" and
    ren_\<rho>\<^sub>D: "is_renaming \<rho>\<^sub>D" and
    disjoint_vars: "vars_cls (add_mset L C \<cdot> \<rho>\<^sub>C) \<inter> vars_cls (add_mset K D \<cdot> \<rho>\<^sub>D) = {}"
  defines "\<gamma> \<equiv> rename_subst_domain \<rho>\<^sub>D \<gamma>\<^sub>D \<odot> rename_subst_domain \<rho>\<^sub>C \<gamma>\<^sub>C"
  shows
    subst_renamed_comp_renamed_simp:
      "L \<cdot>l \<rho>\<^sub>C \<cdot>l \<gamma> = L \<cdot>l \<gamma>\<^sub>C" "C \<cdot> \<rho>\<^sub>C \<cdot> \<gamma> = C \<cdot> \<gamma>\<^sub>C"
      "K \<cdot>l \<rho>\<^sub>D \<cdot>l \<gamma> = K \<cdot>l \<gamma>\<^sub>D" "D \<cdot> \<rho>\<^sub>D \<cdot> \<gamma> = D \<cdot> \<gamma>\<^sub>D" and
    imgu_comp_renamed_comp_renamed_simp:
      "is_imgu \<mu> {{atm_of L \<cdot>a \<rho>\<^sub>C, atm_of K \<cdot>a \<rho>\<^sub>D}} \<Longrightarrow> \<mu> \<odot> \<gamma> = \<gamma>"
proof -
  have subst_adapt_\<rho>\<^sub>D_\<gamma>\<^sub>D:
    "subst_domain (rename_subst_domain \<rho>\<^sub>D \<gamma>\<^sub>D) \<inter> vars_cls (add_mset L C \<cdot> \<rho>\<^sub>C) = {}"
    using disjoint_vars ren_\<rho>\<^sub>D dom_\<gamma>\<^sub>D
      subst_domain_rename_subst_domain_subset_vars_cls_subst_cls
    by (metis Int_commute Orderings.order_eq_iff ground_prop is_renaming_iff
        subst_renaming_subst_adapted vars_cls_subset_subst_domain_if_grounding)

  show "C \<cdot> \<rho>\<^sub>C \<cdot> \<gamma> = C \<cdot> \<gamma>\<^sub>C"
  proof -
    have "C \<cdot> \<rho>\<^sub>C \<cdot> rename_subst_domain \<rho>\<^sub>C \<gamma>\<^sub>C = C \<cdot> \<gamma>\<^sub>C"
    proof (rule subst_renaming_subst_adapted[OF ren_\<rho>\<^sub>C])
      show "vars_cls C \<subseteq> subst_domain \<gamma>\<^sub>C"
        using vars_cls_subset_subst_domain_if_grounding[OF ground_conf] by simp
    qed
    moreover have "C \<cdot> \<rho>\<^sub>C \<cdot> rename_subst_domain \<rho>\<^sub>D \<gamma>\<^sub>D = C \<cdot> \<rho>\<^sub>C"
    proof (rule subst_cls_idem_if_disj_vars)
      show "subst_domain (rename_subst_domain \<rho>\<^sub>D \<gamma>\<^sub>D) \<inter> vars_cls (C \<cdot> \<rho>\<^sub>C) = {}"
        using subst_adapt_\<rho>\<^sub>D_\<gamma>\<^sub>D by auto
    qed
    ultimately show ?thesis
      unfolding \<gamma>_def by simp
  qed

  show "D \<cdot> \<rho>\<^sub>D \<cdot> \<gamma> = D \<cdot> \<gamma>\<^sub>D"
  proof -
    have "D \<cdot> \<rho>\<^sub>D \<cdot> rename_subst_domain \<rho>\<^sub>D \<gamma>\<^sub>D = D \<cdot> \<gamma>\<^sub>D"
    proof (rule subst_renaming_subst_adapted[OF ren_\<rho>\<^sub>D])
      show "vars_cls D \<subseteq> subst_domain \<gamma>\<^sub>D"
        using vars_cls_subset_subst_domain_if_grounding[OF ground_prop] by simp
    qed
    moreover have "D \<cdot> \<gamma>\<^sub>D \<cdot> rename_subst_domain \<rho>\<^sub>C \<gamma>\<^sub>C = D \<cdot> \<gamma>\<^sub>D"
        using ground_prop by simp
    ultimately show ?thesis
      unfolding \<gamma>_def by simp
  qed

  show "L \<cdot>l \<rho>\<^sub>C \<cdot>l \<gamma> = L \<cdot>l \<gamma>\<^sub>C"
  proof -
    have "L \<cdot>l \<rho>\<^sub>C \<cdot>l rename_subst_domain \<rho>\<^sub>C \<gamma>\<^sub>C = L \<cdot>l \<gamma>\<^sub>C"
    proof (rule subst_lit_renaming_subst_adapted[OF ren_\<rho>\<^sub>C])
      show "vars_lit L \<subseteq> subst_domain \<gamma>\<^sub>C"
        using ground_conf
        by (simp add: vars_lit_subset_subst_domain_if_grounding)
    qed
    moreover have "L \<cdot>l \<rho>\<^sub>C \<cdot>l rename_subst_domain \<rho>\<^sub>D \<gamma>\<^sub>D = L \<cdot>l \<rho>\<^sub>C"
    proof (rule subst_lit_idem_if_disj_vars)
      show "subst_domain (rename_subst_domain \<rho>\<^sub>D \<gamma>\<^sub>D) \<inter> vars_lit (L \<cdot>l \<rho>\<^sub>C) = {}"
        using subst_adapt_\<rho>\<^sub>D_\<gamma>\<^sub>D by auto
    qed
    ultimately show ?thesis
      unfolding \<gamma>_def
      by (simp add: literal.expand)
  qed

  moreover show "K \<cdot>l \<rho>\<^sub>D \<cdot>l \<gamma> = K \<cdot>l \<gamma>\<^sub>D"
  proof -
    have "\<And>\<sigma>. K \<cdot>l \<gamma>\<^sub>D \<cdot>l \<sigma> = K \<cdot>l \<gamma>\<^sub>D"
      using ground_prop by (simp add: is_ground_lit_def)
    moreover have "K \<cdot>l \<rho>\<^sub>D \<cdot>l rename_subst_domain \<rho>\<^sub>D \<gamma>\<^sub>D = K \<cdot>l \<gamma>\<^sub>D"
    proof (rule subst_lit_renaming_subst_adapted[OF ren_\<rho>\<^sub>D])
      show "vars_lit K \<subseteq> subst_domain \<gamma>\<^sub>D"
        using ground_prop
        by (simp add: vars_lit_subset_subst_domain_if_grounding)
    qed
    ultimately show ?thesis
      unfolding \<gamma>_def
      by (simp add: literal.expand)
  qed
  ultimately have "atm_of L \<cdot>a \<rho>\<^sub>C \<cdot>a \<gamma> = atm_of K \<cdot>a \<rho>\<^sub>D \<cdot>a \<gamma>"
    using \<open>K \<cdot>l \<gamma>\<^sub>D = - (L \<cdot>l \<gamma>\<^sub>C)\<close>
    by (metis atm_of_subst_lit atm_of_uminus)
  hence "is_unifiers \<gamma> {{atm_of L \<cdot>a \<rho>\<^sub>C, atm_of K \<cdot>a \<rho>\<^sub>D}}"
    by (simp add: is_unifiers_def is_unifier_alt)

  moreover assume imgu_\<mu>: "is_imgu \<mu> {{atm_of L \<cdot>a \<rho>\<^sub>C, atm_of K \<cdot>a \<rho>\<^sub>D}}"

  ultimately show  "\<mu> \<odot> \<gamma> = \<gamma>"
    by (auto simp: is_imgu_def)
qed


section \<open>Invariants\<close>


subsection \<open>Initial Literals Generalize Learned, Trail, and Conflict Literals\<close>

definition clss_lits_generalize_clss_lits where
  "clss_lits_generalize_clss_lits N U \<longleftrightarrow>
    (\<forall>L \<in> \<Union> (set_mset ` U). \<exists>K \<in> \<Union>(set_mset ` N). generalizes_lit K L)"

lemma clss_lits_generalize_clss_lits_if_superset[simp]:
  assumes "N2 \<subseteq> N1"
  shows "clss_lits_generalize_clss_lits N1 N2"
proof (unfold clss_lits_generalize_clss_lits_def, rule ballI)
  fix L
  assume L_in: "L \<in> \<Union> (set_mset ` N2)"
  show "\<exists>K \<in> \<Union> (set_mset ` N1). generalizes_lit K L"
    unfolding generalizes_lit_def
  proof (intro bexI exI conjI)
    show "L \<in> \<Union> (set_mset ` N1)"
      using L_in \<open>N2 \<subseteq> N1\<close> by blast
  next
    show "L \<cdot>l Var = L"
      by simp
  qed
qed

lemma clss_lits_generalize_clss_lits_subset:
  "clss_lits_generalize_clss_lits N U1 \<Longrightarrow> U2 \<subseteq> U1 \<Longrightarrow> clss_lits_generalize_clss_lits N U2"
  unfolding clss_lits_generalize_clss_lits_def by blast

lemma clss_lits_generalize_clss_lits_insert:
  "clss_lits_generalize_clss_lits N (insert C U) \<longleftrightarrow>
    (\<forall>L \<in># C. \<exists>K \<in> \<Union>(set_mset ` N). generalizes_lit K L) \<and> clss_lits_generalize_clss_lits N U"
  unfolding clss_lits_generalize_clss_lits_def by blast

lemma clss_lits_generalize_clss_lits_trans:
  assumes
    "clss_lits_generalize_clss_lits N1 N2" and
    "clss_lits_generalize_clss_lits N2 N3"
  shows "clss_lits_generalize_clss_lits N1 N3"
proof (unfold clss_lits_generalize_clss_lits_def, rule ballI)
  fix L3
  assume "L3 \<in> \<Union> (set_mset ` N3)"
  then obtain L2 \<sigma>2 where "L2 \<in> \<Union> (set_mset ` N2)" and "L2 \<cdot>l \<sigma>2 = L3"
    using assms(2)[unfolded clss_lits_generalize_clss_lits_def] generalizes_lit_def by meson
  then obtain L1 \<sigma>1 where "L1 \<in> \<Union> (set_mset ` N1)" and "L1 \<cdot>l \<sigma>1 = L2"
    using assms(1)[unfolded clss_lits_generalize_clss_lits_def] generalizes_lit_def by meson
  
  thus "\<exists>K \<in> \<Union> (set_mset ` N1). generalizes_lit K L3"
    unfolding generalizes_lit_def
  proof (intro bexI exI conjI)
    show "L1 \<cdot>l (\<sigma>1 \<odot> \<sigma>2) = L3"
      by (simp add: \<open>L1 \<cdot>l \<sigma>1 = L2\<close> \<open>L2 \<cdot>l \<sigma>2 = L3\<close>)
  qed simp_all
qed

lemma clss_lits_generalize_clss_lits_subst_clss:
  assumes "clss_lits_generalize_clss_lits N1 N2"
  shows "clss_lits_generalize_clss_lits N1 ((\<lambda>C. C \<cdot> \<sigma>) ` N2)"
  unfolding clss_lits_generalize_clss_lits_def
proof (rule ballI)
  fix L assume "L \<in> \<Union> (set_mset ` (\<lambda>C. C \<cdot> \<sigma>) ` N2)"
  then obtain L\<^sub>2 where "L\<^sub>2 \<in> \<Union> (set_mset ` N2)" and L_def: "L = L\<^sub>2 \<cdot>l \<sigma>" by auto
  then obtain L\<^sub>1 \<sigma>\<^sub>1 where L\<^sub>1_in: "L\<^sub>1 \<in> \<Union> (set_mset ` N1)" and L\<^sub>2_def: "L\<^sub>2 = L\<^sub>1 \<cdot>l \<sigma>\<^sub>1"
    using assms[unfolded clss_lits_generalize_clss_lits_def]
    unfolding generalizes_lit_def by metis

  show "\<exists>K \<in> \<Union> (set_mset ` N1). generalizes_lit K L"
    unfolding generalizes_lit_def
  proof (intro bexI exI)
    show "L\<^sub>1 \<in> \<Union> (set_mset ` N1)"
      by (rule L\<^sub>1_in)
  next
    show "L\<^sub>1 \<cdot>l (\<sigma>\<^sub>1 \<odot> \<sigma>) = L"
      unfolding L_def L\<^sub>2_def by simp
  qed
qed

lemma clss_lits_generalize_clss_lits_singleton_subst_cls:
  "clss_lits_generalize_clss_lits N {C} \<Longrightarrow> clss_lits_generalize_clss_lits N {C \<cdot> \<sigma>}"
  by (rule clss_lits_generalize_clss_lits_subst_clss[of N "{C}" \<sigma>, simplified])

lemma clss_lits_generalize_clss_lits_subst_cls:
  assumes "clss_lits_generalize_clss_lits N {add_mset L1 (add_mset L2 C)}"
  shows "clss_lits_generalize_clss_lits N {add_mset (L1 \<cdot>l \<sigma>) (C \<cdot> \<sigma>)}"
proof (rule clss_lits_generalize_clss_lits_trans)
  show "clss_lits_generalize_clss_lits N {add_mset L1 (add_mset L2 C) \<cdot> \<sigma>}"
    by (rule clss_lits_generalize_clss_lits_singleton_subst_cls[of N _ \<sigma>, OF assms])
next
  show "clss_lits_generalize_clss_lits {add_mset L1 (add_mset L2 C) \<cdot> \<sigma>}
    {add_mset (L1 \<cdot>l \<sigma>) (C \<cdot> \<sigma>)}"
    apply (simp add: clss_lits_generalize_clss_lits_def generalizes_lit_def)
    using subst_lit_id_subst by blast
qed

definition initial_lits_generalize_learned_trail_conflict where
  "initial_lits_generalize_learned_trail_conflict N S \<longleftrightarrow> clss_lits_generalize_clss_lits (fset N)
    (fset (state_learned S |\<union>| clss_of_trail (state_trail S) |\<union>|
      (case state_conflict S of None \<Rightarrow> {||} | Some (C, _) \<Rightarrow> {|C|})))"

lemma initial_lits_generalize_learned_trail_conflict_initial_state[simp]:
  "initial_lits_generalize_learned_trail_conflict N initial_state"
  unfolding initial_lits_generalize_learned_trail_conflict_def by simp

lemma propagate_preserves_initial_lits_generalize_learned_trail_conflict:
  "propagate N \<beta> S S' \<Longrightarrow> initial_lits_generalize_learned_trail_conflict N S \<Longrightarrow>
    initial_lits_generalize_learned_trail_conflict N S'"
proof (induction S S' rule: propagate.induct)
  case (propagateI C U L C' \<gamma> C\<^sub>0 C\<^sub>1 \<Gamma> \<mu>)

  from propagateI.prems have
    N_generalize: "clss_lits_generalize_clss_lits (fset N) (fset (U |\<union>| clss_of_trail \<Gamma>))"
    unfolding initial_lits_generalize_learned_trail_conflict_def by simp_all

  from propagateI.hyps have
    C_in: "C |\<in>| N |\<union>| U" and
    C_def: "C = add_mset L C'" and
    C\<^sub>0_def: "C\<^sub>0 = {#K \<in># C'. K \<cdot>l \<gamma> \<noteq> L \<cdot>l \<gamma>#}" by simp_all

  have "clss_lits_generalize_clss_lits (fset N)
    (insert (add_mset L C\<^sub>0 \<cdot> \<mu>) (fset (U |\<union>| clss_of_trail \<Gamma>)))"
    unfolding clss_lits_generalize_clss_lits_insert
  proof (rule conjI)
    show "\<forall>L \<in># add_mset L C\<^sub>0 \<cdot> \<mu>. \<exists>K\<in>\<Union> (set_mset ` fset N). generalizes_lit K L"
    proof (rule ballI)
      fix K assume "K \<in># add_mset L C\<^sub>0 \<cdot> \<mu>"
      hence "K = L \<cdot>l \<mu> \<or> (\<exists>M. M \<in># C\<^sub>0 \<and> K = M \<cdot>l \<mu>)"
        by auto
      then obtain K' where K'_in: "K' \<in># C" and K_def: "K = K' \<cdot>l \<mu>"
        using C\<^sub>0_def C_def by auto
      
      obtain D L\<^sub>D where "D |\<in>| N" and "L\<^sub>D \<in># D" and "generalizes_lit L\<^sub>D K'"
        using K'_in C_in N_generalize[unfolded clss_lits_generalize_clss_lits_def]
        by (metis (mono_tags, opaque_lifting) UN_iff funion_iff generalizes_lit_refl notin_fset)

      show "\<exists>K'\<in>\<Union> (set_mset ` fset N). generalizes_lit K' K"
      proof (rule bexI)
        show "generalizes_lit L\<^sub>D K"
          using \<open>generalizes_lit L\<^sub>D K'\<close> 
          by (metis generalizes_lit_def K_def subst_lit_comp_subst)
      next
        show \<open>L\<^sub>D \<in> \<Union> (set_mset ` fset N)\<close>
          using \<open>D |\<in>| N\<close> \<open>L\<^sub>D \<in># D\<close>
          by (meson UN_I notin_fset)
      qed
    qed
  next
    show "clss_lits_generalize_clss_lits (fset N) (fset (U |\<union>| clss_of_trail \<Gamma>))"
      by (rule N_generalize)
  qed
  thus ?case
    by (simp add: initial_lits_generalize_learned_trail_conflict_def propagate_lit_def)
qed

lemma decide_preserves_initial_lits_generalize_learned_trail_conflict:
  "decide N \<beta> S S' \<Longrightarrow> initial_lits_generalize_learned_trail_conflict N S \<Longrightarrow>
    initial_lits_generalize_learned_trail_conflict N S'"
proof (induction S S' rule: decide.induct)
  case (decideI L \<Gamma> U)
  thus ?case
    by (simp add: decide_lit_def initial_lits_generalize_learned_trail_conflict_def)
qed

lemma conflict_preserves_initial_lits_generalize_learned_trail_conflict:
  assumes "conflict N \<beta> S S'" and "initial_lits_generalize_learned_trail_conflict N S"
  shows "initial_lits_generalize_learned_trail_conflict N S'"
  using assms(1)
proof (cases N \<beta> S S' rule: conflict.cases)
  case (conflictI D U \<gamma> \<Gamma>)
  from assms(2) have "clss_lits_generalize_clss_lits (fset N) (fset (U |\<union>| clss_of_trail \<Gamma>))"
    unfolding conflictI(1) by (simp add: initial_lits_generalize_learned_trail_conflict_def)
  hence ball_U_\<Gamma>_generalize:
    "\<And>L. L \<in> \<Union> (set_mset ` fset (U |\<union>| clss_of_trail \<Gamma>)) \<Longrightarrow>
      \<exists>K \<in> \<Union> (set_mset ` fset N). generalizes_lit K L"
    unfolding clss_lits_generalize_clss_lits_def by blast

  have "clss_lits_generalize_clss_lits (fset N) (insert D (fset (U |\<union>| clss_of_trail \<Gamma>)))"
    unfolding clss_lits_generalize_clss_lits_def
  proof (rule ballI)
    fix L assume "L \<in> \<Union> (set_mset ` insert D (fset (U |\<union>| clss_of_trail \<Gamma>)))"
    hence "L \<in> set_mset D \<or> L \<in> \<Union> (set_mset ` (fset (U |\<union>| clss_of_trail \<Gamma>)))"
      by simp
    thus "\<exists>K \<in> \<Union> (set_mset ` fset N). generalizes_lit K L"
    proof (elim disjE)
      assume L_in: "L \<in># D"
      show "?thesis"
        using \<open>D |\<in>| N |\<union>| U\<close>[unfolded funion_iff]
      proof (elim disjE)
        show "D |\<in>| N \<Longrightarrow> ?thesis"
          using L_in
          by (meson UN_I generalizes_lit_refl notin_fset)
      next
        assume "D |\<in>| U"
        hence "\<exists>K \<in> \<Union> (set_mset ` fset N). generalizes_lit K L"
          using ball_U_\<Gamma>_generalize[of L] L_in
          using mk_disjoint_finsert by fastforce
        thus ?thesis
          by metis
      qed
    next
      show "L \<in> \<Union> (set_mset ` fset (U |\<union>| clss_of_trail \<Gamma>)) \<Longrightarrow> ?thesis"
        using ball_U_\<Gamma>_generalize by simp
    qed
  qed
  then show ?thesis
    using assms(2)
    unfolding conflictI(1,2)
    by (simp add: initial_lits_generalize_learned_trail_conflict_def)
qed

lemma skip_preserves_initial_lits_generalize_learned_trail_conflict:
  "skip N \<beta> S S' \<Longrightarrow> initial_lits_generalize_learned_trail_conflict N S \<Longrightarrow>
    initial_lits_generalize_learned_trail_conflict N S'"
proof (induction S S' rule: skip.induct)
  case (skipI L D \<sigma> Cl \<Gamma> U)
  then show ?case
    unfolding initial_lits_generalize_learned_trail_conflict_def
    unfolding state_learned_simp state_conflict_simp state_trail_simp option.case prod.case
    by (auto elim: clss_lits_generalize_clss_lits_subset)
qed

lemma factorize_preserves_initial_lits_generalize_learned_trail_conflict:
  "factorize N \<beta> S S' \<Longrightarrow> initial_lits_generalize_learned_trail_conflict N S \<Longrightarrow>
    initial_lits_generalize_learned_trail_conflict N S'"
proof (induction S S' rule: factorize.induct)
  case (factorizeI L \<gamma> L' \<mu> \<Gamma> U D)
  moreover have "clss_lits_generalize_clss_lits (fset N) {add_mset (L \<cdot>l \<mu>) (D \<cdot> \<mu>)}"
    using factorizeI
    unfolding initial_lits_generalize_learned_trail_conflict_def
    apply (simp add: clss_lits_generalize_clss_lits_insert generalizes_lit_def)
    by (smt (verit, best) Melem_subst_cls subst_lit_comp_subst)
  ultimately show ?case
    unfolding initial_lits_generalize_learned_trail_conflict_def
    apply simp
    using clss_lits_generalize_clss_lits_insert by blast
qed

lemma resolve_preserves_initial_lits_generalize_learned_trail_conflict:
  "resolve N \<beta> S S' \<Longrightarrow> initial_lits_generalize_learned_trail_conflict N S \<Longrightarrow>
    initial_lits_generalize_learned_trail_conflict N S'"
proof (induction S S' rule: resolve.induct)
  case (resolveI \<Gamma> \<Gamma>' K D \<delta>\<^sub>D L \<delta>\<^sub>C \<rho>\<^sub>C \<rho>\<^sub>D C \<mu> \<gamma> U)
  moreover have "clss_lits_generalize_clss_lits (fset N) {(C \<cdot> \<rho>\<^sub>C + D \<cdot> \<rho>\<^sub>D) \<cdot> \<mu>}"
  proof -
    from resolveI.prems have
      N_lits_sup: "clss_lits_generalize_clss_lits (fset N)
        (fset (U |\<union>| clss_of_trail \<Gamma> |\<union>| {|add_mset L C|}))"
      unfolding initial_lits_generalize_learned_trail_conflict_def by simp

    have "clss_lits_generalize_clss_lits (fset N) {C \<cdot> \<rho>\<^sub>C \<cdot> \<mu>}"
    proof -
      from N_lits_sup have "clss_lits_generalize_clss_lits (fset N) {add_mset L C}"
        by (simp add: clss_lits_generalize_clss_lits_insert)
      hence "clss_lits_generalize_clss_lits (fset N) {C}"
        by (simp add: clss_lits_generalize_clss_lits_def)
      thus ?thesis
        by (auto intro: clss_lits_generalize_clss_lits_singleton_subst_cls)
    qed
    moreover have "clss_lits_generalize_clss_lits (fset N) {D \<cdot> \<rho>\<^sub>D \<cdot> \<mu>}"
    proof -
      from N_lits_sup have "clss_lits_generalize_clss_lits (fset N) (fset (clss_of_trail \<Gamma>))"
        by (rule clss_lits_generalize_clss_lits_subset) auto
      hence "clss_lits_generalize_clss_lits (fset N) {add_mset K D}"
        unfolding resolveI.hyps
        by (simp add: clss_lits_generalize_clss_lits_insert propagate_lit_def)
      hence "clss_lits_generalize_clss_lits (fset N) {D}"
        by (simp add: clss_lits_generalize_clss_lits_def)
      thus ?thesis
        by (auto intro: clss_lits_generalize_clss_lits_singleton_subst_cls)
    qed
    ultimately show ?thesis
      by (auto simp add: clss_lits_generalize_clss_lits_def)
  qed
  ultimately show ?case
    unfolding initial_lits_generalize_learned_trail_conflict_def
    unfolding state_trail_simp state_learned_simp state_conflict_simp
    unfolding option.case prod.case
    by (metis clss_lits_generalize_clss_lits_insert finsert.rep_eq funion_finsert_right)
qed

lemma backtrack_preserves_initial_lits_generalize_learned_trail_conflict:
  "backtrack N \<beta> S S' \<Longrightarrow> initial_lits_generalize_learned_trail_conflict N S \<Longrightarrow>
    initial_lits_generalize_learned_trail_conflict N S'"
proof (induction S S' rule: backtrack.induct)
  case (backtrackI \<Gamma> \<Gamma>' \<Gamma>'' L \<sigma> D U)
  then show ?case
    unfolding initial_lits_generalize_learned_trail_conflict_def
    apply (simp add: clss_of_trail_append)
    apply (erule clss_lits_generalize_clss_lits_subset)
    by blast
qed

lemma scl_preserves_initial_lits_generalize_learned_trail_conflict:
  assumes "scl N \<beta> S S'" and "initial_lits_generalize_learned_trail_conflict N S"
  shows "initial_lits_generalize_learned_trail_conflict N S'"
  using assms unfolding scl_def
  using propagate_preserves_initial_lits_generalize_learned_trail_conflict
    decide_preserves_initial_lits_generalize_learned_trail_conflict
    conflict_preserves_initial_lits_generalize_learned_trail_conflict
    skip_preserves_initial_lits_generalize_learned_trail_conflict
    factorize_preserves_initial_lits_generalize_learned_trail_conflict
    resolve_preserves_initial_lits_generalize_learned_trail_conflict
    backtrack_preserves_initial_lits_generalize_learned_trail_conflict
  by metis


subsection \<open>Trail Literals Come From Clauses\<close>

definition trail_lits_from_clauses where
  "trail_lits_from_clauses N S \<longleftrightarrow>
    (\<forall>L \<in> fst ` set (state_trail S).
      \<exists>L' \<in> \<Union>(set_mset ` (fset N \<union> fset (state_learned S))). generalizes_lit L' L)"

lemma trail_lits_from_clauses_initial_state[simp]: "trail_lits_from_clauses N initial_state"
  by (simp add: trail_lits_from_clauses_def)

lemma propagate_preserves_trail_lits_from_clauses:
  assumes "propagate N \<beta> S S'" and "trail_lits_from_clauses N S"
  shows "trail_lits_from_clauses N S'"
  using assms(1)
proof (cases N \<beta> S S' rule: propagate.cases)
  case (propagateI C U L C' \<gamma> C\<^sub>0 C\<^sub>1 \<Gamma> \<mu>)

  have "\<exists>L'\<in> \<Union> (fset (set_mset |`| (N |\<union>| U))). generalizes_lit L' (L \<cdot>l \<mu> \<cdot>l \<gamma>)"
  proof (rule bexI[of _ L])
    show "L \<in> \<Union> (fset (set_mset |`| (N |\<union>| U)))"
      using \<open>C |\<in>| N |\<union>| U\<close> \<open>C = add_mset L C'\<close>
      by (meson Union_iff fimage_eqI notin_fset union_single_eq_member)
  next
    show "generalizes_lit L (L \<cdot>l \<mu> \<cdot>l \<gamma>)"
      unfolding generalizes_lit_def by (metis subst_lit_comp_subst)
  qed

  moreover have "\<forall>L \<in> fst ` set \<Gamma>. \<exists>L' \<in> \<Union> (fset (set_mset |`| (N |\<union>| U))). generalizes_lit L' L"
    using assms(2) unfolding propagateI by (simp add: trail_lits_from_clauses_def)

  ultimately show ?thesis
    unfolding propagateI(2) by (simp add: trail_lits_from_clauses_def propagate_lit_def)
qed

lemma decide_preserves_trail_lits_from_clauses:
  assumes "decide N \<beta> S S'" and "trail_lits_from_clauses N S"
  shows "trail_lits_from_clauses N S'"
  using assms(1)
proof (cases N \<beta> S S' rule: decide.cases)
  case (decideI L \<gamma> \<Gamma> U)

  hence "\<exists>L'\<in>\<Union> (fset (set_mset |`| (N |\<union>| U))). generalizes_lit L' (L \<cdot>l \<gamma>)"
    by (auto simp: generalizes_lit_def)

  moreover have "\<forall>L \<in> fst ` set \<Gamma>. \<exists>L' \<in> \<Union> (fset (set_mset |`| (N |\<union>| U))). generalizes_lit L' L"
    using assms(2) unfolding decideI by (simp add: trail_lits_from_clauses_def)

  ultimately show ?thesis
    unfolding decideI by (simp add: trail_lits_from_clauses_def decide_lit_def)
qed

lemma conflict_preserves_trail_lits_from_clauses:
  assumes "conflict N \<beta> S S'" and "trail_lits_from_clauses N S"
  shows "trail_lits_from_clauses N S'"
  using assms(1)
proof (cases N \<beta> S S' rule: conflict.cases)
  case (conflictI D U \<gamma> \<Gamma>)
  thus ?thesis
    using assms(2) by (simp add: trail_lits_from_clauses_def)
qed

lemma skip_preserves_trail_lits_from_clauses:
  assumes "skip N \<beta> S S'" and "trail_lits_from_clauses N S"
  shows "trail_lits_from_clauses N S'"
  using assms(1)
proof (cases N \<beta> S S' rule: skip.cases)
  case (skipI L D \<sigma> n \<Gamma> U)
  thus ?thesis
    using assms(2) by (simp add: trail_lits_from_clauses_def)
qed

lemma factorize_preserves_trail_lits_from_clauses:
  assumes "factorize N \<beta> S S'" and "trail_lits_from_clauses N S"
  shows "trail_lits_from_clauses N S'"
  using assms(1)
proof (cases N \<beta> S S' rule: factorize.cases)
  case (factorizeI L \<gamma> L' \<mu> \<Gamma> U D)
  thus ?thesis
    using assms(2) by (simp add: trail_lits_from_clauses_def)
qed

lemma resolve_preserves_trail_lits_from_clauses:
  assumes "resolve N \<beta> S S'" and "trail_lits_from_clauses N S"
  shows "trail_lits_from_clauses N S'"
  using assms(1)
proof (cases N \<beta> S S' rule: resolve.cases)
  case (resolveI \<Gamma> \<Gamma>' L C \<delta> \<rho> U D L' \<sigma> \<mu>)
  thus ?thesis
    using assms(2) by (simp add: trail_lits_from_clauses_def)
qed

lemma backtrack_preserves_trail_lits_from_clauses:
  assumes "backtrack N \<beta> S S'" and "trail_lits_from_clauses N S"
  shows "trail_lits_from_clauses N S'"
  using assms(1)
proof (cases N \<beta> S S' rule: backtrack.cases)
  case (backtrackI \<Gamma> \<Gamma>' \<Gamma>'' K L \<sigma> D U)
  hence "suffix \<Gamma>'' \<Gamma>"
    by (simp add: suffixI decide_lit_def)
  hence "set \<Gamma>'' \<subseteq> set \<Gamma>"
    by (simp add: set_mono_suffix)

  moreover have "\<forall>L \<in> fst ` set \<Gamma>. \<exists>L' \<in> \<Union> (fset (set_mset |`| (N |\<union>| U))). generalizes_lit L' L"
    using assms(2) unfolding backtrackI by (simp add: trail_lits_from_clauses_def)

  ultimately have "\<forall>L \<in> fst ` set \<Gamma>''. \<exists>L' \<in> \<Union> (fset (set_mset |`| (N |\<union>| U))). generalizes_lit L' L"
    by fast
  thus ?thesis
    unfolding trail_lits_from_clauses_def backtrackI(1,2) state_trail_simp state_learned_simp
    by auto
qed

lemma scl_preserves_trail_lits_from_clauses:
  assumes "scl N \<beta> S S'" and "trail_lits_from_clauses N S"
  shows "trail_lits_from_clauses N S'"
  using assms unfolding scl_def
  using propagate_preserves_trail_lits_from_clauses decide_preserves_trail_lits_from_clauses
    conflict_preserves_trail_lits_from_clauses skip_preserves_trail_lits_from_clauses
    factorize_preserves_trail_lits_from_clauses resolve_preserves_trail_lits_from_clauses
    backtrack_preserves_trail_lits_from_clauses
  by metis


subsection \<open>Trail Literals Come From Initial Clauses\<close>

definition trail_lits_from_init_clauses where
  "trail_lits_from_init_clauses N S \<longleftrightarrow>
    (\<forall>L \<in> fst ` set (state_trail S). \<exists>L' \<in> \<Union>(set_mset ` fset N). generalizes_lit L' L)"

lemma trail_lits_from_init_clausesI:
  assumes "trail_lits_from_clauses N S" and "initial_lits_generalize_learned_trail_conflict N S"
  shows "trail_lits_from_init_clauses N S"
  unfolding trail_lits_from_init_clauses_def
proof (rule ballI)
  fix L assume "L \<in> fst ` set (state_trail S)"
  with assms(1) obtain L' where
    "L' \<in> \<Union> (set_mset ` (fset N \<union> fset (state_learned S))) \<and> generalizes_lit L' L"
    unfolding trail_lits_from_clauses_def by metis
  hence "(\<exists>x\<in>fset N. L' \<in># x) \<or> (\<exists>x \<in> fset (state_learned S). L' \<in># x)" and "generalizes_lit L' L"
    by simp_all
  thus "\<exists>L'\<in>\<Union> (set_mset ` fset N). generalizes_lit L' L"
  proof (elim disjE bexE)
    fix C assume "C \<in> fset N"
    thus "L' \<in># C \<Longrightarrow> ?thesis"
      using \<open>generalizes_lit L' L\<close> by auto
  next
    fix C assume "C \<in> fset (state_learned S)" and "L' \<in># C"
    with assms(2) have "\<exists>K\<in>\<Union> (set_mset ` fset N). generalizes_lit K L'"
      unfolding initial_lits_generalize_learned_trail_conflict_def
        clss_lits_generalize_clss_lits_def
      by auto
    thus "?thesis"
      using \<open>generalizes_lit L' L\<close> by (metis generalizes_lit_def subst_lit_comp_subst)
  qed
qed


subsection \<open>Trail Literals Are Ground\<close>

definition trail_lits_ground where
  "trail_lits_ground S \<longleftrightarrow> (\<forall>L \<in> fst ` set (state_trail S). is_ground_lit L)"

lemma trail_lits_ground_initial_state[simp]: "trail_lits_ground initial_state"
  by (simp add: trail_lits_ground_def)

lemma propagate_preserves_trail_lits_ground:
  assumes "propagate N \<beta> S S'" and "trail_lits_ground S"
  shows "trail_lits_ground S'"
  using assms(1)
proof (cases N \<beta> S S' rule: propagate.cases)
  case (propagateI C U L C' \<gamma> C\<^sub>0 C\<^sub>1 \<Gamma> \<mu>)
  hence "is_ground_lit (L \<cdot>l \<gamma>)"
    by (meson Melem_subst_cls is_ground_cls_def mset_subset_eqD mset_subset_eq_add_right
        union_single_eq_member)

  moreover have "\<forall>\<tau>. is_unifiers \<tau> {atm_of ` set_mset (add_mset L C\<^sub>1)} \<longrightarrow> \<tau> = \<mu> \<odot> \<tau>"
    using \<open>is_imgu \<mu> {atm_of ` set_mset (add_mset L C\<^sub>1)}\<close>
    by (simp add: is_imgu_def)

  moreover have "is_unifiers \<gamma> {atm_of ` set_mset (add_mset L C\<^sub>1)}"
    by (auto simp: is_unifiers_def is_unifier_alt \<open>C\<^sub>1 = {#K \<in># C'. K \<cdot>l \<gamma> = L \<cdot>l \<gamma>#}\<close>
        intro: subst_atm_of_eqI)

  ultimately have "is_ground_lit (L \<cdot>l \<mu> \<cdot>l \<gamma>)"
    by (metis subst_lit_comp_subst)

  moreover have "\<forall>L \<in> fst ` set \<Gamma>. is_ground_lit L"
    using \<open>trail_lits_ground S\<close> by (simp add: propagateI(1) trail_lits_ground_def)

  ultimately show ?thesis
    by (simp add: propagateI(2) trail_lits_ground_def propagate_lit_def)
qed

lemma decide_preserves_trail_lits_ground:
  assumes "decide N \<beta> S S'" and "trail_lits_ground S"
  shows "trail_lits_ground S'"
  using assms(1)
proof (cases N \<beta> S S' rule: decide.cases)
  case (decideI L \<gamma> \<Gamma> U)
  hence "is_ground_lit (L \<cdot>l \<gamma>)"
    by metis

  moreover have "\<forall>L \<in> fst ` set \<Gamma>. is_ground_lit L"
    using assms(2) by (simp add: decideI(1) trail_lits_ground_def)

  ultimately show ?thesis
    by (simp add: decideI(2) trail_lits_ground_def decide_lit_def)
qed

lemma conflict_preserves_trail_lits_ground:
  assumes "conflict N \<beta> S S'" and "trail_lits_ground S"
  shows "trail_lits_ground S'"
  using assms by (auto simp: trail_lits_ground_def elim!: conflict.cases)

lemma skip_preserves_trail_lits_ground:
  assumes "skip N \<beta> S S'" and "trail_lits_ground S"
  shows "trail_lits_ground S'"
  using assms by (auto simp: trail_lits_ground_def elim!: skip.cases)

lemma factorize_preserves_trail_lits_ground:
  assumes "factorize N \<beta> S S'" and "trail_lits_ground S"
  shows "trail_lits_ground S'"
  using assms by (auto simp: trail_lits_ground_def elim!: factorize.cases)

lemma resolve_preserves_trail_lits_ground:
  assumes "resolve N \<beta> S S'" and "trail_lits_ground S"
  shows "trail_lits_ground S'"
  using assms by (auto simp: trail_lits_ground_def elim!: resolve.cases)

lemma backtrack_preserves_trail_lits_ground:
  assumes "backtrack N \<beta> S S'" and "trail_lits_ground S"
  shows "trail_lits_ground S'"
  using assms by (auto simp: trail_lits_ground_def decide_lit_def elim!: backtrack.cases)

lemma scl_preserves_trail_lits_ground:
  assumes "scl N \<beta> S S'" and "trail_lits_ground S"
  shows "trail_lits_ground S'"
  using assms unfolding scl_def
  using propagate_preserves_trail_lits_ground decide_preserves_trail_lits_ground
    conflict_preserves_trail_lits_ground skip_preserves_trail_lits_ground
    factorize_preserves_trail_lits_ground resolve_preserves_trail_lits_ground
    backtrack_preserves_trail_lits_ground
  by metis


subsection \<open>Trail Literals Are Defined Only Once\<close>

definition trail_lits_consistent where
  "trail_lits_consistent S \<longleftrightarrow> trail_consistent (state_trail S)"

lemma trail_lits_consistent_initial_state[simp]: "trail_lits_consistent initial_state"
  by (simp add: trail_lits_consistent_def)

lemma propagate_preserves_trail_lits_consistent:
  assumes "propagate N \<beta> S S'" and invar: "trail_lits_consistent S"
  shows "trail_lits_consistent S'"
  using assms(1)
proof (cases N \<beta> S S' rule: propagate.cases)
  case (propagateI C U L C' \<gamma> C\<^sub>0 C\<^sub>1 \<Gamma> \<mu>)
  
  have  "L \<cdot>l \<mu> \<cdot>l \<gamma> = L \<cdot>l \<gamma>"
  proof -
    have "is_unifiers \<gamma> {atm_of ` set_mset (add_mset L C\<^sub>1)}"
      by (smt (verit, del_insts) finite_imageI finite_set_mset image_iff insert_iff is_unifier_alt
          is_unifiers_def local.propagateI(8) mem_Collect_eq set_mset_add_mset_insert
          set_mset_filter singletonD subst_atm_of_eqI)
    hence "\<gamma> = \<mu> \<odot> \<gamma>"
      using \<open>is_imgu \<mu> {atm_of ` set_mset (add_mset L C\<^sub>1)}\<close>
      by (simp add: is_imgu_def)
    thus ?thesis
      by (metis subst_lit_comp_subst)
  qed
  hence "\<not> trail_defined_lit \<Gamma> (L \<cdot>l \<mu> \<cdot>l \<gamma>)"
    using \<open>\<not> trail_defined_lit \<Gamma> (L \<cdot>l \<gamma>)\<close> by metis
  
  moreover from invar have "trail_consistent \<Gamma>"
    by (simp add: propagateI(1) trail_lits_consistent_def)

  ultimately show ?thesis
    by (auto simp: propagateI(2) propagate_lit_def trail_lits_consistent_def
        intro: trail_consistent.Cons)
qed

lemma decide_preserves_trail_lits_consistent:
  assumes "decide N \<beta> S S'" and invar: "trail_lits_consistent S"
  shows "trail_lits_consistent S'"
  using assms
  by (auto simp: trail_lits_consistent_def decide_lit_def elim!: decide.cases
      intro: trail_consistent.Cons)

lemma conflict_preserves_trail_lits_consistent:
  assumes "conflict N \<beta> S S'" and invar: "trail_lits_consistent S"
  shows "trail_lits_consistent S'"
  using assms
  by (auto simp: trail_lits_consistent_def elim: conflict.cases)

lemma skip_preserves_trail_lits_consistent:
  assumes "skip N \<beta> S S'" and invar: "trail_lits_consistent S"
  shows "trail_lits_consistent S'"
  using assms
  by (auto simp: trail_lits_consistent_def elim!: skip.cases elim: trail_consistent.cases)

lemma factorize_preserves_trail_lits_consistent:
  assumes "factorize N \<beta> S S'" and invar: "trail_lits_consistent S"
  shows "trail_lits_consistent S'"
  using assms
  by (auto simp: trail_lits_consistent_def elim: factorize.cases)

lemma resolve_preserves_trail_lits_consistent:
  assumes "resolve N \<beta> S S'" and invar: "trail_lits_consistent S"
  shows "trail_lits_consistent S'"
  using assms
  by (auto simp: trail_lits_consistent_def elim: resolve.cases)

lemma backtrack_preserves_trail_lits_consistent:
  assumes "backtrack N \<beta> S S'" and invar: "trail_lits_consistent S"
  shows "trail_lits_consistent S'"
  using assms
  by (auto simp: trail_lits_consistent_def decide_lit_def elim!: backtrack.cases
      elim!: trail_consistent_if_suffix intro: suffixI)

lemma scl_preserves_trail_lits_consistent:
  assumes "scl N \<beta> S S'" and "trail_lits_consistent S"
  shows "trail_lits_consistent S'"
  using assms unfolding scl_def
  using propagate_preserves_trail_lits_consistent decide_preserves_trail_lits_consistent
    conflict_preserves_trail_lits_consistent skip_preserves_trail_lits_consistent
    factorize_preserves_trail_lits_consistent resolve_preserves_trail_lits_consistent
    backtrack_preserves_trail_lits_consistent
  by metis


subsection \<open>Trail Closures Are False In Subtrails\<close>

definition trail_closures_false' where
  "trail_closures_false' S \<longleftrightarrow> trail_closures_false (state_trail S)"

lemma trail_closures_false'_initial_state[simp]: "trail_closures_false' initial_state"
  by (simp add: trail_closures_false'_def)

lemma propagate_preserves_trail_closures_false':
  assumes step: "propagate N \<beta> S S'" and invar: "trail_closures_false' S"
  shows "trail_closures_false' S'"
  using step
proof (cases N \<beta> S S' rule: propagate.cases)
  case step_hyps: (propagateI C U L C' \<gamma> C\<^sub>0 C\<^sub>1 \<Gamma> \<mu>)
  have "is_unifier \<gamma> (atm_of ` set_mset (add_mset L C\<^sub>1))"
    unfolding step_hyps
    by (auto simp add: is_unifier_alt intro: subst_atm_of_eqI)
  hence "\<mu> \<odot> \<gamma> = \<gamma>"
    using \<open>is_imgu \<mu> {atm_of ` set_mset (add_mset L C\<^sub>1)}\<close>
    by (simp add: is_imgu_def is_unifiers_def)
  hence "trail_false_cls \<Gamma> (C\<^sub>0 \<cdot> \<mu> \<cdot> \<gamma>)"
    using \<open>trail_false_cls \<Gamma> (C\<^sub>0 \<cdot> \<gamma>)\<close>
    by (metis subst_cls_comp_subst)
  with invar show ?thesis
    unfolding step_hyps(1,2)
    by (simp add: trail_closures_false'_def propagate_lit_def trail_closures_false.Cons)
qed

lemma decide_preserves_trail_closures_false':
  assumes step: "decide N \<beta> S S'" and invar: "trail_closures_false' S"
  shows "trail_closures_false' S'"
  using step
proof (cases N \<beta> S S' rule: decide.cases)
  case step_hyps: (decideI L \<gamma> \<Gamma> U)
  with invar show ?thesis
    by (simp add: trail_closures_false'_def decide_lit_def trail_closures_false.Cons)
qed

lemma conflict_preserves_trail_closures_false':
  assumes step: "conflict N \<beta> S S'" and invar: "trail_closures_false' S"
  shows "trail_closures_false' S'"
  using step
proof (cases N \<beta> S S' rule: conflict.cases)
  case (conflictI D U \<gamma> \<Gamma>)
  with invar show ?thesis
    by (simp add: trail_closures_false'_def)
qed

lemma skip_preserves_trail_closures_false':
  assumes step: "skip N \<beta> S S'" and invar: "trail_closures_false' S"
  shows "trail_closures_false' S'"
  using step
proof (cases N \<beta> S S' rule: skip.cases)
  case (skipI L D \<sigma> n \<Gamma> U)
  with invar show ?thesis
    by (simp add: trail_closures_false'_def trail_closures_false_ConsD)
qed

lemma factorize_preserves_trail_closures_false':
  assumes step: "factorize N \<beta> S S'" and invar: "trail_closures_false' S"
  shows "trail_closures_false' S'"
  using step
proof (cases N \<beta> S S' rule: factorize.cases)
  case (factorizeI L \<gamma> L' \<mu> \<Gamma> U D)
  with invar show ?thesis
    by (simp add: trail_closures_false'_def)
qed

lemma resolve_preserves_trail_closures_false':
  assumes step: "resolve N \<beta> S S'" and invar: "trail_closures_false' S"
  shows "trail_closures_false' S'"
  using step
proof (cases N \<beta> S S' rule: resolve.cases)
  case (resolveI \<Gamma> \<Gamma>' K D \<gamma>\<^sub>D L \<gamma>\<^sub>C \<rho>\<^sub>C \<rho>\<^sub>D C \<mu> \<gamma> U)
  with invar show ?thesis
    by (simp add: trail_closures_false'_def)
qed

lemma backtrack_preserves_trail_closures_false':
  assumes step: "backtrack N \<beta> S S'" and invar: "trail_closures_false' S"
  shows "trail_closures_false' S'"
  using step
proof (cases N \<beta> S S' rule: backtrack.cases)
  case (backtrackI \<Gamma> \<Gamma>' \<Gamma>'' K L \<sigma> D U)
  with invar show ?thesis
    by (auto simp add: trail_closures_false'_def
        intro: trail_closures_false_ConsD trail_closures_false_appendD)
qed

lemma scl_preserves_trail_closures_false':
  assumes "scl N \<beta> S S'" and "trail_closures_false' S"
  shows "trail_closures_false' S'"
  using assms unfolding scl_def
  using propagate_preserves_trail_closures_false' decide_preserves_trail_closures_false'
    conflict_preserves_trail_closures_false' skip_preserves_trail_closures_false'
    factorize_preserves_trail_closures_false' resolve_preserves_trail_closures_false'
    backtrack_preserves_trail_closures_false'
  by metis


subsection \<open>Trail Literals Were Propagated or Decided\<close>

inductive trail_propagated_or_decided for N \<beta> U where
  Nil[simp]: "trail_propagated_or_decided N \<beta> U []" |
  Propagate: "
    C |\<in>| N |\<union>| U \<Longrightarrow>
    C = add_mset L C' \<Longrightarrow>
    is_ground_cls (C \<cdot> \<gamma>) \<Longrightarrow>
    \<forall>K\<in>#C \<cdot> \<gamma>. atm_of K \<prec>\<^sub>B \<beta> \<Longrightarrow>
    C\<^sub>0 = {#K \<in># C'. K \<cdot>l \<gamma> \<noteq> L \<cdot>l \<gamma>#} \<Longrightarrow>
    C\<^sub>1 = {#K \<in># C'. K \<cdot>l \<gamma> = L \<cdot>l \<gamma>#} \<Longrightarrow>
    trail_false_cls \<Gamma> (C\<^sub>0 \<cdot> \<gamma>) \<Longrightarrow>
    \<not> trail_defined_lit \<Gamma> (L \<cdot>l \<gamma>) \<Longrightarrow>
    is_imgu \<mu> {atm_of ` set_mset (add_mset L C\<^sub>1)} \<Longrightarrow>
    trail_propagated_or_decided N \<beta> U \<Gamma> \<Longrightarrow>
    trail_propagated_or_decided N \<beta> U (trail_propagate \<Gamma> (L \<cdot>l \<mu>) (C\<^sub>0 \<cdot> \<mu>) \<gamma>)" |
  Decide: "
    L \<in> \<Union> (set_mset ` fset N) \<Longrightarrow>
    is_ground_lit (L \<cdot>l \<gamma>) \<Longrightarrow>
    \<not> trail_defined_lit \<Gamma> (L \<cdot>l \<gamma>) \<Longrightarrow>
    atm_of L \<cdot>a \<gamma> \<prec>\<^sub>B \<beta> \<Longrightarrow>
    trail_propagated_or_decided N \<beta> U \<Gamma> \<Longrightarrow>
    trail_propagated_or_decided N \<beta> U (trail_decide \<Gamma> (L \<cdot>l \<gamma>))"

lemma trail_propagate_or_decide_suffixI:
  assumes "trail_propagated_or_decided N \<beta> U ys" and "suffix xs ys"
  shows "trail_propagated_or_decided N \<beta> U xs"
  using assms
proof (induction ys arbitrary: xs rule: trail_propagated_or_decided.induct)
  case Nil
  hence "xs = []"
    by simp
  thus ?case
    by simp
next
  case (Propagate C L C' \<gamma> C\<^sub>0 C\<^sub>1 \<Gamma> \<mu>)
  from Propagate.prems obtain zs where
    tr_prop_eq: "trail_propagate \<Gamma> (L \<cdot>l \<mu>) (C\<^sub>0 \<cdot> \<mu>) \<gamma> = zs @ xs"
    by (auto simp: suffix_def)
  show ?case
  proof (cases zs)
    case Nil
    with tr_prop_eq have "xs = trail_propagate \<Gamma> (L \<cdot>l \<mu>) (C\<^sub>0 \<cdot> \<mu>) \<gamma>"
      by simp
    then show ?thesis
      by (simp add: trail_propagated_or_decided.Propagate[OF Propagate.hyps])
  next
    case (Cons Ln \<Gamma>')
    with tr_prop_eq have "suffix xs \<Gamma>"
      by (simp add: suffix_def propagate_lit_def)
    thus ?thesis
      by (rule Propagate.IH)
  qed
next
  case (Decide L \<gamma> \<Gamma>)
  from Decide.prems obtain zs where
    tr_deci_eq: "trail_decide \<Gamma> (L \<cdot>l \<gamma>) = zs @ xs"
    by (auto simp: suffix_def)
  show ?case
  proof (cases zs)
    case Nil
    with tr_deci_eq have "xs = trail_decide \<Gamma> (L \<cdot>l \<gamma>)"
      by simp
    then show ?thesis
      by (simp add: trail_propagated_or_decided.Decide[OF Decide.hyps])
  next
    case (Cons Ln \<Gamma>')
    with tr_deci_eq have "suffix xs \<Gamma>"
      by (simp add: suffix_def decide_lit_def)
    thus ?thesis
      by (rule Decide.IH)
  qed
qed

definition trail_propagated_or_decided' where
  "trail_propagated_or_decided' N \<beta> S =
    trail_propagated_or_decided N \<beta> (state_learned S) (state_trail S)"

lemma trail_propagated_or_decided_learned_finsert:
  assumes "trail_propagated_or_decided N \<beta> U \<Gamma>"
  shows "trail_propagated_or_decided N \<beta> (finsert C U) \<Gamma>"
  using assms
proof (induction \<Gamma> rule: trail_propagated_or_decided.induct)
  case Nil
  show ?case by (simp add: trail_propagated_or_decided.Nil)
next
  case (Propagate D L D' \<gamma> D\<^sub>0 D\<^sub>1 \<Gamma> \<mu>)
  
  from Propagate.hyps have D_in: "D |\<in>| N |\<union>| finsert C U"
    by simp

  have IH: "trail_propagated_or_decided N \<beta> (finsert C U) \<Gamma>"
    by (rule Propagate.IH)

  show ?case
    using trail_propagated_or_decided.Propagate[OF D_in Propagate.hyps(2,3,4,5,6,7,8,9) IH] .
next
  case (Decide L \<gamma> \<Gamma>)
  then show ?case
    by (simp add: trail_propagated_or_decided.Decide)
qed

lemma trail_propagated_or_decided_trail_append:
  assumes "trail_propagated_or_decided N \<beta> U (\<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2)"
  shows "trail_propagated_or_decided N \<beta> U \<Gamma>\<^sub>2"
  using assms
proof (induction "\<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2" arbitrary: \<Gamma>\<^sub>1 \<Gamma>\<^sub>2 rule: trail_propagated_or_decided.induct)
  case Nil
  thus ?case
    by simp
next
  case (Propagate C L C' \<gamma> C\<^sub>0 C\<^sub>1 \<Gamma> \<mu>)
  hence tr_prop_eq_\<Gamma>\<^sub>1_\<Gamma>\<^sub>2:
    "\<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2 = trail_propagate \<Gamma> (L \<cdot>l \<mu>) (C\<^sub>0 \<cdot> \<mu>) \<gamma>"
    by simp
  thus ?case
    unfolding propagate_lit_def append_eq_Cons_conv
  proof (elim disjE conjE exE)
    assume "\<Gamma>\<^sub>1 = []" and \<Gamma>\<^sub>2_def: "\<Gamma>\<^sub>2 = (L \<cdot>l \<mu> \<cdot>l \<gamma>, Some (C\<^sub>0 \<cdot> \<mu>, L \<cdot>l \<mu>, \<gamma>)) # \<Gamma>"
    show ?thesis
      unfolding \<Gamma>\<^sub>2_def
      by (rule trail_propagated_or_decided.Propagate[unfolded propagate_lit_def];
          rule Propagate.hyps)
  next
    fix \<Gamma>\<^sub>1'
    assume "\<Gamma>\<^sub>1 = (L \<cdot>l \<mu> \<cdot>l \<gamma>, Some (C\<^sub>0 \<cdot> \<mu>, L \<cdot>l \<mu>, \<gamma>)) # \<Gamma>\<^sub>1'" and "\<Gamma>\<^sub>1' @ \<Gamma>\<^sub>2 = \<Gamma>"
    thus ?thesis
      using Propagate.hyps by blast
  qed
next
  case (Decide L \<gamma> \<Gamma>)
  hence "\<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2 = trail_decide \<Gamma> (L \<cdot>l \<gamma>)"
    by simp
  thus ?case
    unfolding decide_lit_def append_eq_Cons_conv
  proof (elim disjE conjE exE)
    assume "\<Gamma>\<^sub>1 = []" and \<Gamma>\<^sub>2_def: "\<Gamma>\<^sub>2 = (L \<cdot>l \<gamma>, None) # \<Gamma>"
    show ?thesis
      unfolding \<Gamma>\<^sub>2_def
      by (rule trail_propagated_or_decided.Decide[unfolded decide_lit_def]; rule Decide.hyps)
  next
    fix \<Gamma>\<^sub>1' assume "\<Gamma>\<^sub>1 = (L \<cdot>l \<gamma>, None) # \<Gamma>\<^sub>1'" and "\<Gamma>\<^sub>1' @ \<Gamma>\<^sub>2 = \<Gamma>"
    then show ?thesis
      using Decide.hyps by blast
  qed
qed

lemma trail_propagated_or_decided_initial_state[simp]:
  "trail_propagated_or_decided' N \<beta> initial_state"
  by (auto simp: trail_propagated_or_decided'_def intro: trail_propagated_or_decided.Nil)

lemma propagate_preserves_trail_propagated_or_decided:
  assumes "propagate N \<beta> S S'" and "trail_propagated_or_decided' N \<beta> S"
  shows "trail_propagated_or_decided' N \<beta> S'"
  using assms(1)
proof (cases N \<beta> S S' rule: propagate.cases)
  case (propagateI C U L C' \<gamma> C\<^sub>0 C\<^sub>1 \<Gamma> \<mu>)

  from propagateI(1) assms(2) have IH: "trail_propagated_or_decided N \<beta> U \<Gamma>"
    by (simp add: trail_propagated_or_decided'_def)

  show ?thesis
    unfolding propagateI(2)
    apply (simp add: trail_propagated_or_decided'_def)
    by (rule trail_propagated_or_decided.Propagate[rotated -1, OF IH])
      (rule propagateI)+
qed

lemma decide_preserves_trail_propagated_or_decided:
  assumes "decide N \<beta> S S'" and "trail_propagated_or_decided' N \<beta> S"
  shows "trail_propagated_or_decided' N \<beta> S'"
  using assms(1)
proof (cases N \<beta> S S' rule: decide.cases)
  case (decideI L \<gamma> \<Gamma> U)

  from decideI(1) assms(2) have IH: "trail_propagated_or_decided N \<beta> U \<Gamma>"
    by (simp add: trail_propagated_or_decided'_def)
  show ?thesis
    unfolding decideI(2)
    apply (simp add: trail_propagated_or_decided'_def)
    by (rule trail_propagated_or_decided.Decide[rotated -1, OF IH])
      (rule decideI)+
qed

lemma conflict_preserves_trail_propagated_or_decided:
  assumes "conflict N \<beta> S S'" and invar: "trail_propagated_or_decided' N \<beta> S"
  shows "trail_propagated_or_decided' N \<beta> S'"
  using assms by (auto simp: trail_propagated_or_decided'_def elim: conflict.cases)

lemma skip_preserves_trail_propagated_or_decided:
  assumes "skip N \<beta> S S'" and invar: "trail_propagated_or_decided' N \<beta> S"
  shows "trail_propagated_or_decided' N \<beta> S'"
  using assms(1)
proof (cases N \<beta> S S' rule: skip.cases)
  case (skipI L D \<sigma> n \<Gamma> U)

  from invar have "trail_propagated_or_decided N \<beta> U ((L, n) # \<Gamma>)"
    unfolding skipI(1) by (simp add: trail_propagated_or_decided'_def)
  hence "trail_propagated_or_decided N \<beta> U \<Gamma>"
    by (cases N \<beta> U "(L, n) # \<Gamma>" rule: trail_propagated_or_decided.cases)
      (simp_all add: propagate_lit_def decide_lit_def)
  thus ?thesis
    unfolding skipI(2) by (simp add: trail_propagated_or_decided'_def)
qed

lemma factorize_preserves_trail_propagated_or_decided:
  assumes "factorize N \<beta> S S'" and invar: "trail_propagated_or_decided' N \<beta> S"
  shows "trail_propagated_or_decided' N \<beta> S'"
  using assms by (auto simp: trail_propagated_or_decided'_def elim: factorize.cases)

lemma resolve_preserves_trail_propagated_or_decided:
  assumes "resolve N \<beta> S S'" and invar: "trail_propagated_or_decided' N \<beta> S"
  shows "trail_propagated_or_decided' N \<beta> S'"
  using assms by (auto simp: trail_propagated_or_decided'_def elim: resolve.cases) 

lemma backtrack_preserves_trail_propagated_or_decided:
  assumes "backtrack N \<beta> S S'" and invar: "trail_propagated_or_decided' N \<beta> S"
  shows "trail_propagated_or_decided' N \<beta> S'"
  using assms(1)
proof (cases N \<beta> S S' rule: backtrack.cases)
  case (backtrackI \<Gamma> \<Gamma>' \<Gamma>'' K L \<sigma> D U)

  have "trail_propagated_or_decided N \<beta> (finsert (add_mset L D) U) \<Gamma>''"
  proof (rule trail_propagated_or_decided_learned_finsert)
    from invar have "trail_propagated_or_decided N \<beta> U (trail_decide (\<Gamma>' @ \<Gamma>'') (- (L \<cdot>l \<sigma>)))"
      unfolding backtrackI by (simp add: trail_propagated_or_decided'_def)
    then show "trail_propagated_or_decided N \<beta> U \<Gamma>''"
      by (induction "(trail_decide (\<Gamma>' @ \<Gamma>'') (- (L \<cdot>l \<sigma>)))"
          rule: trail_propagated_or_decided.induct)
        (simp_all add: decide_lit_def propagate_lit_def
          trail_propagated_or_decided_trail_append)
  qed
  thus ?thesis
    unfolding backtrackI by (simp add: trail_propagated_or_decided'_def)
qed

lemma scl_preserves_trail_propagated_or_decided:
  assumes "scl N \<beta> S S'" and "trail_propagated_or_decided' N \<beta> S"
  shows "trail_propagated_or_decided' N \<beta> S'"
  using assms unfolding scl_def
  using propagate_preserves_trail_propagated_or_decided decide_preserves_trail_propagated_or_decided
    conflict_preserves_trail_propagated_or_decided skip_preserves_trail_propagated_or_decided
    factorize_preserves_trail_propagated_or_decided resolve_preserves_trail_propagated_or_decided
    backtrack_preserves_trail_propagated_or_decided
  by metis


subsection \<open>Trail Atoms Are Less Than \<beta>\<close>

definition trail_atoms_lt where
  "trail_atoms_lt \<beta> S \<longleftrightarrow> (\<forall>atm \<in> atm_of ` fst ` set (state_trail S). atm \<prec>\<^sub>B \<beta>)"

lemma ball_trail_lt_initial_state[simp]: "trail_atoms_lt \<beta> initial_state"
  by (simp add: trail_atoms_lt_def)

lemma propagate_preserves_trail_atoms_lt:
  assumes "propagate N \<beta> S S'" and "trail_atoms_lt \<beta> S"
  shows "trail_atoms_lt \<beta> S'"
  using assms(1)
proof (cases N \<beta> S S' rule: propagate.cases)
  case (propagateI C U L C' \<gamma> C\<^sub>0 C\<^sub>1 \<Gamma> \<mu>)
  hence "is_ground_lit (L \<cdot>l \<gamma>)"
    by (meson Melem_subst_cls is_ground_cls_def mset_subset_eqD mset_subset_eq_add_right
        union_single_eq_member)

  moreover have "\<forall>\<tau>. is_unifiers \<tau> {atm_of ` set_mset (add_mset L C\<^sub>1)} \<longrightarrow> \<tau> = \<mu> \<odot> \<tau>"
    using \<open>is_imgu \<mu> {atm_of ` set_mset (add_mset L C\<^sub>1)}\<close>
    by (simp add: is_imgu_def)

  moreover have "is_unifiers \<gamma> {atm_of ` set_mset (add_mset L C\<^sub>1)}"
    by (auto simp: is_unifiers_def is_unifier_alt \<open>C\<^sub>1 = {#K \<in># C'. K \<cdot>l \<gamma> = L \<cdot>l \<gamma>#}\<close>
        intro: subst_atm_of_eqI)

  ultimately have "is_ground_lit (L \<cdot>l \<mu> \<cdot>l \<gamma>)"
    by (metis subst_lit_comp_subst)

  have "atm_of L \<cdot>a \<mu> \<cdot>a \<gamma> = atm_of L \<cdot>a \<gamma>"
  proof -
    from propagateI have "is_unifiers \<gamma> {atm_of ` set_mset (add_mset L C\<^sub>1)}"
      by (auto simp: is_unifiers_def is_unifier_alt intro: subst_atm_of_eqI)
    with propagateI have "\<gamma> = \<mu> \<odot> \<gamma>"
      by (simp add: is_imgu_def)
    thus ?thesis
      by (metis subst_atm_comp_subst)
  qed

  moreover from propagateI have "atm_of L \<cdot>a \<gamma> \<prec>\<^sub>B \<beta>"
    by (metis add_mset_add_single atm_of_subst_lit subst_cls_single subst_cls_union
        union_single_eq_member)

  ultimately have "atm_of L \<cdot>a \<mu> \<cdot>a \<gamma> \<prec>\<^sub>B \<beta>"
    by simp
  with \<open>trail_atoms_lt \<beta> S\<close> show ?thesis
    by (simp add: trail_atoms_lt_def propagateI(1,2) propagate_lit_def)
qed

lemma decide_preserves_trail_atoms_lt:
  assumes "decide N \<beta> S S'" and "trail_atoms_lt \<beta> S"
  shows "trail_atoms_lt \<beta> S'"
  using assms by (auto simp: trail_atoms_lt_def decide_lit_def elim!: decide.cases)

lemma conflict_preserves_trail_atoms_lt:
  assumes "conflict N \<beta> S S'" and "trail_atoms_lt \<beta> S"
  shows "trail_atoms_lt \<beta> S'"
  using assms by (auto simp: trail_atoms_lt_def elim!: conflict.cases)

lemma skip_preserves_trail_atoms_lt:
  assumes "skip N \<beta> S S'" and "trail_atoms_lt \<beta> S"
  shows "trail_atoms_lt \<beta> S'"
  using assms by (auto simp: trail_atoms_lt_def elim!: skip.cases)

lemma factorize_preserves_trail_atoms_lt:
  assumes "factorize N \<beta> S S'" and "trail_atoms_lt \<beta> S"
  shows "trail_atoms_lt \<beta> S'"
  using assms by (auto simp: trail_atoms_lt_def elim!: factorize.cases)

lemma resolve_preserves_trail_atoms_lt:
  assumes "resolve N \<beta> S S'" and "trail_atoms_lt \<beta> S"
  shows "trail_atoms_lt \<beta> S'"
  using assms by (auto simp: trail_atoms_lt_def elim!: resolve.cases)

lemma backtrack_preserves_trail_atoms_lt:
  assumes "backtrack N \<beta> S S'" and "trail_atoms_lt \<beta> S"
  shows "trail_atoms_lt \<beta> S'"
  using assms by (auto simp: trail_atoms_lt_def decide_lit_def elim!: backtrack.cases)

lemma scl_preserves_trail_atoms_lt:
  assumes "scl N \<beta> S S'" and "trail_atoms_lt \<beta> S"
  shows "trail_atoms_lt \<beta> S'"
  using assms unfolding scl_def
  using propagate_preserves_trail_atoms_lt decide_preserves_trail_atoms_lt
    conflict_preserves_trail_atoms_lt skip_preserves_trail_atoms_lt
    factorize_preserves_trail_atoms_lt resolve_preserves_trail_atoms_lt
    backtrack_preserves_trail_atoms_lt
  by metis


subsection \<open>Trail Resolved Literals Have Unique Polarity\<close>

definition trail_resolved_lits_pol where
  "trail_resolved_lits_pol S \<longleftrightarrow>
  (\<forall>Ln \<in> set (state_trail S). \<forall>C L \<gamma>. snd Ln = Some (C, L, \<gamma>) \<longrightarrow> -(L \<cdot>l \<gamma>) \<notin># C \<cdot> \<gamma>)"

lemma trail_resolved_lits_pol_initial_state[simp]: "trail_resolved_lits_pol initial_state"
  by (simp add: trail_resolved_lits_pol_def)

lemma propagate_preserves_trail_resolved_lits_pol:
  assumes step: "propagate N \<beta> S S'" and invar: "trail_resolved_lits_pol S"
  shows "trail_resolved_lits_pol S'"
  using step
proof (cases N \<beta> S S' rule: propagate.cases)
  case (propagateI C U L C' \<gamma> C\<^sub>0 C\<^sub>1 \<Gamma> \<mu>)
  have "is_unifiers \<gamma> {atm_of ` set_mset (add_mset L C\<^sub>1)}"
    unfolding \<open>C\<^sub>1 = {#K \<in># C'. K \<cdot>l \<gamma> = L \<cdot>l \<gamma>#}\<close>
    by (auto simp add: is_unifiers_def is_unifier_alt intro: subst_atm_of_eqI)
  hence "\<mu> \<odot> \<gamma> = \<gamma>"
    using \<open>is_imgu \<mu> {atm_of ` set_mset (add_mset L C\<^sub>1)}\<close>
    by (simp add: is_imgu_def)
  hence "L \<cdot>l \<mu> \<cdot>l \<gamma> = L \<cdot>l \<gamma>" and "C\<^sub>0 \<cdot> \<mu> \<cdot> \<gamma> = C\<^sub>0 \<cdot> \<gamma>"
    by (simp_all del: subst_lit_comp_subst subst_cls_comp_subst
        add: subst_lit_comp_subst[symmetric] subst_cls_comp_subst[symmetric])
  hence "- (L \<cdot>l \<mu> \<cdot>l \<gamma>) \<notin># C\<^sub>0 \<cdot> \<mu> \<cdot> \<gamma>"
    using \<open>C\<^sub>0 = {#K \<in># C'. K \<cdot>l \<gamma> \<noteq> L \<cdot>l \<gamma>#}\<close> \<open>\<not> trail_defined_lit \<Gamma> (L \<cdot>l \<gamma>)\<close>
      \<open>trail_false_cls \<Gamma> (C\<^sub>0 \<cdot> \<gamma>)\<close>
    by (metis trail_defined_lit_iff_defined_uminus trail_defined_lit_iff_true_or_false
        trail_false_cls_def)

  moreover from invar have "\<forall>Ln \<in> set \<Gamma>. \<forall>C L \<gamma>. snd Ln = Some (C, L, \<gamma>) \<longrightarrow> - (L \<cdot>l \<gamma>) \<notin># C \<cdot> \<gamma>"
    unfolding propagateI(1,2) trail_resolved_lits_pol_def
    by simp
  
  ultimately show ?thesis
    unfolding propagateI(1,2)
    unfolding trail_resolved_lits_pol_def propagate_lit_def state_proj_simp list.set
    by fastforce
qed

lemma decide_preserves_trail_resolved_lits_pol:
  assumes step: "decide N \<beta> S S'" and invar: "trail_resolved_lits_pol S"
  shows "trail_resolved_lits_pol S'"
  using assms
  by (auto simp: trail_resolved_lits_pol_def decide_lit_def elim: decide.cases)

lemma conflict_preserves_trail_resolved_lits_pol:
  assumes step: "conflict N \<beta> S S'" and invar: "trail_resolved_lits_pol S"
  shows "trail_resolved_lits_pol S'"
  using assms
  by (auto simp: trail_resolved_lits_pol_def elim: conflict.cases)

lemma skip_preserves_trail_resolved_lits_pol:
  assumes step: "skip N \<beta> S S'" and invar: "trail_resolved_lits_pol S"
  shows "trail_resolved_lits_pol S'"
  using assms
  by (auto simp: trail_resolved_lits_pol_def elim: skip.cases)

lemma factorize_preserves_trail_resolved_lits_pol:
  assumes step: "factorize N \<beta> S S'" and invar: "trail_resolved_lits_pol S"
  shows "trail_resolved_lits_pol S'"
  using assms
  by (auto simp: trail_resolved_lits_pol_def elim: factorize.cases)

lemma resolve_preserves_trail_resolved_lits_pol:
  assumes step: "resolve N \<beta> S S'" and invar: "trail_resolved_lits_pol S"
  shows "trail_resolved_lits_pol S'"
  using assms
  by (auto simp: trail_resolved_lits_pol_def propagate_lit_def elim!: resolve.cases)

lemma backtrack_preserves_trail_resolved_lits_pol:
  assumes step: "backtrack N \<beta> S S'" and invar: "trail_resolved_lits_pol S"
  shows "trail_resolved_lits_pol S'"
  using assms
  by (auto simp: trail_resolved_lits_pol_def decide_lit_def ball_Un elim: backtrack.cases)

lemma scl_preserves_trail_resolved_lits_pol:
  assumes "scl N \<beta> S S'" and "trail_resolved_lits_pol S"
  shows "trail_resolved_lits_pol S'"
  using assms unfolding scl_def
  using propagate_preserves_trail_resolved_lits_pol decide_preserves_trail_resolved_lits_pol
    conflict_preserves_trail_resolved_lits_pol skip_preserves_trail_resolved_lits_pol
    factorize_preserves_trail_resolved_lits_pol resolve_preserves_trail_resolved_lits_pol
    backtrack_preserves_trail_resolved_lits_pol
  by metis


subsection \<open>Trail And Conflict Closures Are Ground\<close>

definition ground_closures where
  "ground_closures S \<longleftrightarrow>
    (\<forall>Ln \<in> set (state_trail S). \<forall>C L \<gamma>. snd Ln = Some (C, L, \<gamma>) \<longrightarrow> is_ground_cls (add_mset L C \<cdot> \<gamma>)) \<and>
    (\<forall>C \<gamma>. state_conflict S = Some (C, \<gamma>) \<longrightarrow> is_ground_cls (C \<cdot> \<gamma>))"

lemma ground_closures_initial_state[simp]: "ground_closures initial_state"
  by (simp add: ground_closures_def)

lemma propagate_preserves_ground_closures:
  assumes step: "propagate N \<beta> S S'" and invar: "ground_closures S"
  shows "ground_closures S'"
  using step
proof (cases N \<beta> S S' rule: propagate.cases)
  case (propagateI C U L C' \<gamma> C\<^sub>0 C\<^sub>1 \<Gamma> \<mu>)

  have C_def: "C = add_mset L (C\<^sub>0 + C\<^sub>1)"
    using propagateI(3-) by auto

  have "is_unifiers \<gamma> {atm_of ` set_mset (add_mset L C\<^sub>1)}"
    unfolding \<open>C\<^sub>1 = {#K \<in># C'. K \<cdot>l \<gamma> = L \<cdot>l \<gamma>#}\<close>
    by (auto simp add: is_unifiers_def is_unifier_alt intro: subst_atm_of_eqI)
  hence "\<mu> \<odot> \<gamma> = \<gamma>"
    using \<open>is_imgu \<mu> {atm_of ` set_mset (add_mset L C\<^sub>1)}\<close>
    by (simp add: is_imgu_def)
  hence "L \<cdot>l \<mu> \<cdot>l \<gamma> = L \<cdot>l \<gamma>" and "C\<^sub>0 \<cdot> \<mu> \<cdot> \<gamma> = C\<^sub>0 \<cdot> \<gamma>"
    by (simp_all del: subst_lit_comp_subst subst_cls_comp_subst
        add: subst_lit_comp_subst[symmetric] subst_cls_comp_subst[symmetric])
  hence "is_ground_cls (add_mset L C\<^sub>0 \<cdot> \<mu> \<cdot> \<gamma>)"
    using \<open>is_ground_cls (C \<cdot> \<gamma>)\<close>
    by (simp add: C_def)
  thus ?thesis
    using invar
    unfolding propagateI(1,2)
    by (simp add: ground_closures_def propagate_lit_def)
qed

lemma decide_preserves_ground_closures:
  assumes step: "decide N \<beta> S S'" and invar: "ground_closures S"
  shows "ground_closures S'"
  using assms
  by (cases N \<beta> S S' rule: decide.cases) (simp add: ground_closures_def decide_lit_def)

lemma conflict_preserves_ground_closures:
  assumes step: "conflict N \<beta> S S'" and invar: "ground_closures S"
  shows "ground_closures S'"
  using step
proof (cases N \<beta> S S' rule: conflict.cases)
  case (conflictI D U \<gamma> \<Gamma>)
  thus ?thesis
    using invar
    unfolding conflictI(1,2)
    by (simp add: ground_closures_def)
qed

lemma skip_preserves_ground_closures:
  assumes step: "skip N \<beta> S S'" and invar: "ground_closures S"
  shows "ground_closures S'"
  using assms
  by (cases N \<beta> S S' rule: skip.cases) (simp add: ground_closures_def)

lemma factorize_preserves_ground_closures:
  assumes step: "factorize N \<beta> S S'" and invar: "ground_closures S"
  shows "ground_closures S'"
  using step
proof (cases N \<beta> S S' rule: factorize.cases)
  case (factorizeI L \<gamma> L' \<mu> \<Gamma> U D)
  have "is_unifier \<gamma> {atm_of L, atm_of L'}"
    using \<open>L \<cdot>l \<gamma> = L' \<cdot>l \<gamma>\<close>[THEN subst_atm_of_eqI]
    by (simp add: is_unifier_alt)
  hence "\<mu> \<odot> \<gamma> = \<gamma>"
    using \<open>is_imgu \<mu> {{atm_of L, atm_of L'}}\<close>
    by (simp add: is_imgu_def is_unifiers_def)

  have "add_mset L D \<cdot> \<mu> \<cdot> \<gamma> = add_mset L D \<cdot> \<gamma>"
    using \<open>\<mu> \<odot> \<gamma> = \<gamma>\<close>
    by (metis subst_cls_comp_subst)
  hence "is_ground_cls (add_mset L D \<cdot> \<mu> \<cdot> \<gamma>)"
    using factorizeI(3-) invar
    unfolding factorizeI(1,2)
    by (simp add: ground_closures_def)
  thus ?thesis
    using invar
    unfolding factorizeI(1,2)
    by (simp add: ground_closures_def)
qed

lemma merge_of_renamed_groundings:
  assumes
    ren_\<rho>\<^sub>C: "is_renaming \<rho>\<^sub>C" and
    ren_\<rho>\<^sub>D: "is_renaming \<rho>\<^sub>D" and
    disjoint_vars: "vars_cls (C \<cdot> \<rho>\<^sub>C) \<inter> vars_cls (D \<cdot> \<rho>\<^sub>D) = {}" and
    ground_conf: "is_ground_cls (C \<cdot> \<gamma>\<^sub>C)" and
    ground_prop: "is_ground_cls (D \<cdot> \<gamma>\<^sub>D)" and
    merge_\<gamma>: "is_grounding_merge \<gamma>
      (vars_cls (C \<cdot> \<rho>\<^sub>C)) (rename_subst_domain \<rho>\<^sub>C \<gamma>\<^sub>C)
      (vars_cls (D \<cdot> \<rho>\<^sub>D)) (rename_subst_domain \<rho>\<^sub>D \<gamma>\<^sub>D)"
  shows
    "\<forall>L \<in># C. L \<cdot>l \<rho>\<^sub>C \<cdot>l \<gamma> = L \<cdot>l \<gamma>\<^sub>C"
    "\<forall>K \<in># D. K \<cdot>l \<rho>\<^sub>D \<cdot>l \<gamma> = K \<cdot>l \<gamma>\<^sub>D"
proof -
  have "\<forall>x\<in>vars_cls (C \<cdot> \<rho>\<^sub>C). vars_term (rename_subst_domain \<rho>\<^sub>C \<gamma>\<^sub>C x) = {}"
    using ground_conf ren_\<rho>\<^sub>C
    by (metis is_ground_atm_iff_vars_empty is_ground_cls_is_ground_on_var
        subst_renaming_subst_adapted vars_cls_subset_subst_domain_if_grounding)

  moreover have "\<forall>x\<in>vars_cls (D \<cdot> \<rho>\<^sub>D). vars_term (rename_subst_domain \<rho>\<^sub>D \<gamma>\<^sub>D x) = {}"
    using ground_prop ren_\<rho>\<^sub>D
    by (metis is_ground_atm_iff_vars_empty is_ground_cls_is_ground_on_var
        subst_renaming_subst_adapted vars_cls_subset_subst_domain_if_grounding)

  ultimately have
    ball_C_\<rho>\<^sub>C_apply_\<gamma>: "\<forall>x\<in>vars_cls (C \<cdot> \<rho>\<^sub>C). \<gamma> x = rename_subst_domain \<rho>\<^sub>C \<gamma>\<^sub>C x" and
    ball_D_\<rho>\<^sub>D_apply_\<gamma>: "\<forall>x\<in>vars_cls (D \<cdot> \<rho>\<^sub>D). \<gamma> x = rename_subst_domain \<rho>\<^sub>D \<gamma>\<^sub>D x"
    using disjoint_vars merge_\<gamma>
    unfolding is_grounding_merge_def
    by simp_all

  show "\<forall>L \<in># C. L \<cdot>l \<rho>\<^sub>C \<cdot>l \<gamma> = L \<cdot>l \<gamma>\<^sub>C"
  proof (rule ballI)
    fix L assume L_in: "L \<in># C"
    show "L \<cdot>l \<rho>\<^sub>C \<cdot>l \<gamma> = L \<cdot>l \<gamma>\<^sub>C"
      unfolding subst_lit_comp_subst[symmetric]
    proof (intro same_on_vars_lit ballI)
      fix x assume "x \<in> vars_lit L"
      moreover obtain x' where "\<rho>\<^sub>C x = Var x'"
        using ren_\<rho>\<^sub>C
        by (meson is_Var_def is_renaming_iff)
      ultimately have "x' \<in> vars_lit (L \<cdot>l \<rho>\<^sub>C)"
        using vars_subst_lit_eq by fastforce
      hence "\<gamma> x' = rename_subst_domain \<rho>\<^sub>C \<gamma>\<^sub>C x'"
        using ball_C_\<rho>\<^sub>C_apply_\<gamma> L_in multi_member_split by force
      thus "(\<rho>\<^sub>C \<odot> \<gamma>) x = \<gamma>\<^sub>C x"
        apply (simp add: subst_compose_def \<open>\<rho>\<^sub>C x = Var x'\<close>)
        by (metis (no_types, opaque_lifting) L_in Un_iff \<open>\<rho>\<^sub>C x = Var x'\<close> \<open>x \<in> vars_lit L\<close>
            ground_conf image_eqI insert_DiffM is_renaming_iff ren_\<rho>\<^sub>C rename_subst_domain_def
            subsetD the_inv_f_f vars_cls_add_mset vars_cls_subset_subst_domain_if_grounding)
    qed
  qed

  show "\<forall>K \<in># D. K \<cdot>l \<rho>\<^sub>D \<cdot>l \<gamma> = K \<cdot>l \<gamma>\<^sub>D"
  proof (rule ballI)
    fix K assume K_in: "K \<in># D"
    show "K \<cdot>l \<rho>\<^sub>D \<cdot>l \<gamma> = K \<cdot>l \<gamma>\<^sub>D"
      unfolding subst_lit_comp_subst[symmetric]
    proof (intro same_on_vars_lit ballI)
      fix x assume "x \<in> vars_lit K"
      moreover obtain x' where "\<rho>\<^sub>D x = Var x'"
        using ren_\<rho>\<^sub>D
        by (meson is_Var_def is_renaming_iff)
      ultimately have "x' \<in> vars_lit (K \<cdot>l \<rho>\<^sub>D)"
        using vars_subst_lit_eq by fastforce
      hence "\<gamma> x' = rename_subst_domain \<rho>\<^sub>D \<gamma>\<^sub>D x'"
        using ball_D_\<rho>\<^sub>D_apply_\<gamma> K_in multi_member_split by force
      thus "(\<rho>\<^sub>D \<odot> \<gamma>) x = \<gamma>\<^sub>D x"
        apply (simp add: subst_compose_def \<open>\<rho>\<^sub>D x = Var x'\<close>)
        by (metis (no_types, opaque_lifting) K_in UnI1 \<open>\<rho>\<^sub>D x = Var x'\<close> \<open>x \<in> vars_lit K\<close>
            ground_prop image_eqI is_renaming_iff multi_member_split ren_\<rho>\<^sub>D rename_subst_domain_def
            subset_iff the_inv_f_f vars_cls_add_mset vars_cls_subset_subst_domain_if_grounding)
    qed
  qed
qed

lemma resolve_preserves_ground_closures:
  assumes step: "resolve N \<beta> S S'" and invar: "ground_closures S"
  shows "ground_closures S'"
  using step
proof (cases N \<beta> S S' rule: resolve.cases)
  case (resolveI \<Gamma> \<Gamma>' K D \<gamma>\<^sub>D L \<gamma>\<^sub>C \<rho>\<^sub>C \<rho>\<^sub>D C \<mu> \<gamma> U) 
  hence
    ren_\<rho>\<^sub>C: "is_renaming \<rho>\<^sub>C" and
    ren_\<rho>\<^sub>D: "is_renaming \<rho>\<^sub>D" and
    disjoint_vars: "vars_cls (add_mset L C \<cdot> \<rho>\<^sub>C) \<inter> vars_cls (add_mset K D \<cdot> \<rho>\<^sub>D) = {}" and
    merge_\<gamma>: "is_grounding_merge \<gamma>
      (vars_cls (add_mset L C \<cdot> \<rho>\<^sub>C)) (rename_subst_domain \<rho>\<^sub>C \<gamma>\<^sub>C)
      (vars_cls (add_mset K D \<cdot> \<rho>\<^sub>D)) (rename_subst_domain \<rho>\<^sub>D \<gamma>\<^sub>D)"
    by simp_all
  hence "\<forall>x. is_Var (\<rho>\<^sub>C x)" and "inj \<rho>\<^sub>C" and "\<forall>x. is_Var (\<rho>\<^sub>D x)" and "inj \<rho>\<^sub>D"
    by (simp_all add: is_renaming_iff)

  from invar have
    ground_conf: "is_ground_cls (add_mset L C \<cdot> \<gamma>\<^sub>C)" and
    ground_prop: "is_ground_cls (add_mset K D \<cdot> \<gamma>\<^sub>D)" and
    min_ground_clo_\<Gamma>: "\<forall>Ln \<in> set  \<Gamma>. \<forall>C L \<gamma>. snd Ln = Some (C, L, \<gamma>) \<longrightarrow> is_ground_cls (add_mset L C \<cdot> \<gamma>)"
    unfolding resolveI(1,2) \<open>\<Gamma> = trail_propagate \<Gamma>' K D \<gamma>\<^sub>D\<close>
    by (simp_all add: propagate_lit_def ground_closures_def)
  hence
    "\<forall>L\<in>#add_mset L C. L \<cdot>l \<rho>\<^sub>C \<cdot>l \<gamma> = L \<cdot>l \<gamma>\<^sub>C"
    "\<forall>K\<in>#add_mset K D. K \<cdot>l \<rho>\<^sub>D \<cdot>l \<gamma> = K \<cdot>l \<gamma>\<^sub>D"
    using merge_of_renamed_groundings[OF ren_\<rho>\<^sub>C ren_\<rho>\<^sub>D disjoint_vars _ _ merge_\<gamma>] by simp_all

  have "atm_of L \<cdot>a \<rho>\<^sub>C \<cdot>a \<gamma> = atm_of K \<cdot>a \<rho>\<^sub>D \<cdot>a \<gamma>"
    using \<open>K \<cdot>l \<gamma>\<^sub>D = - (L \<cdot>l \<gamma>\<^sub>C)\<close>
      \<open>\<forall>L\<in>#add_mset L C. L \<cdot>l \<rho>\<^sub>C \<cdot>l \<gamma> = L \<cdot>l \<gamma>\<^sub>C\<close>[rule_format, of L, simplified]
      \<open>\<forall>K\<in>#add_mset K D. K \<cdot>l \<rho>\<^sub>D \<cdot>l \<gamma> = K \<cdot>l \<gamma>\<^sub>D\<close>[rule_format, of K, simplified]
    by (metis atm_of_eq_uminus_if_lit_eq atm_of_subst_lit)
  hence "is_unifiers \<gamma> {{atm_of L \<cdot>a \<rho>\<^sub>C, atm_of K \<cdot>a \<rho>\<^sub>D}}"
    by (simp add: is_unifiers_def is_unifier_alt)
  hence "\<mu> \<odot> \<gamma> = \<gamma>"
    using \<open>is_imgu \<mu> {{atm_of L \<cdot>a \<rho>\<^sub>C, atm_of K \<cdot>a \<rho>\<^sub>D}}\<close>
    by (auto simp: is_imgu_def)
  hence "C \<cdot> \<rho>\<^sub>C \<cdot> \<mu> \<cdot> \<gamma> = C \<cdot> \<gamma>\<^sub>C" and "D \<cdot> \<rho>\<^sub>D \<cdot> \<mu> \<cdot> \<gamma> = D \<cdot> \<gamma>\<^sub>D"
    using \<open>\<forall>L\<in>#add_mset L C. L \<cdot>l \<rho>\<^sub>C \<cdot>l \<gamma> = L \<cdot>l \<gamma>\<^sub>C\<close> \<open>\<forall>K\<in>#add_mset K D. K \<cdot>l \<rho>\<^sub>D \<cdot>l \<gamma> = K \<cdot>l \<gamma>\<^sub>D\<close>
    by (metis insert_iff same_on_lits_clause set_mset_add_mset_insert subst_cls_comp_subst
        subst_lit_comp_subst)+
  hence "(C \<cdot> \<rho>\<^sub>C + D \<cdot> \<rho>\<^sub>D) \<cdot> \<mu> \<cdot> \<gamma> = C \<cdot> \<gamma>\<^sub>C + D \<cdot> \<gamma>\<^sub>D"
    by (metis subst_cls_comp_subst subst_cls_union)
  thus ?thesis
    using ground_conf ground_prop min_ground_clo_\<Gamma>
    unfolding resolveI
    by (simp add: ground_closures_def)
qed

lemma backtrack_preserves_ground_closures:
  assumes step: "backtrack N \<beta> S S'" and invar: "ground_closures S"
  shows "ground_closures S'"
  using assms
  by (cases N \<beta> S S' rule: backtrack.cases)
    (simp add: ground_closures_def decide_lit_def ball_Un)

lemma scl_preserves_ground_closures:
  assumes "scl N \<beta> S S'" and "ground_closures S"
  shows "ground_closures S'"
  using assms unfolding scl_def
  using propagate_preserves_ground_closures decide_preserves_ground_closures
    conflict_preserves_ground_closures skip_preserves_ground_closures
    factorize_preserves_ground_closures resolve_preserves_ground_closures
    backtrack_preserves_ground_closures
  by metis

subsection \<open>Trail And Conflict Closures Are Ground And False\<close>

definition ground_false_closures where
  "ground_false_closures S \<longleftrightarrow> ground_closures S \<and>
    trail_closures_false (state_trail S) \<and>
    (\<forall>C \<gamma>. state_conflict S = Some (C, \<gamma>) \<longrightarrow> trail_false_cls (state_trail S) (C \<cdot> \<gamma>))"

lemma ground_false_closures_initial_state[simp]: "ground_false_closures initial_state"
  by (simp add: ground_false_closures_def)

lemma propagate_preserves_ground_false_closures:
  assumes step: "propagate N \<beta> S S'" and invar: "ground_false_closures S"
  shows "ground_false_closures S'"
  using step
proof (cases N \<beta> S S' rule: propagate.cases)
  case step_hyps: (propagateI C U L C' \<gamma> C\<^sub>0 C\<^sub>1 \<Gamma> \<mu>)

  have "ground_closures S'"
    using invar propagate_preserves_ground_closures[OF step]
    by (metis ground_false_closures_def)

  moreover have "trail_closures_false (state_trail S')"
    using invar propagate_preserves_trail_closures_false'[OF step]
    by (metis ground_false_closures_def trail_closures_false'_def)

  moreover have "\<forall>C \<gamma>. state_conflict S' = Some (C, \<gamma>) \<longrightarrow> trail_false_cls (state_trail S') (C \<cdot> \<gamma>)"
    unfolding step_hyps(1,2) by simp

  ultimately show ?thesis
    unfolding ground_false_closures_def by metis
qed

lemma decide_preserves_ground_false_closures:
  assumes step: "decide N \<beta> S S'" and invar: "ground_false_closures S"
  shows "ground_false_closures S'"
  using step
proof (cases N \<beta> S S' rule: decide.cases)
  case step_hyps: (decideI L \<gamma> \<Gamma> U)

  have "ground_closures S'"
    using invar decide_preserves_ground_closures[OF step]
    by (metis ground_false_closures_def)

  moreover have "trail_closures_false (state_trail S')"
    using invar decide_preserves_trail_closures_false'[OF step]
    by (metis ground_false_closures_def trail_closures_false'_def)

  moreover have "\<forall>C \<gamma>. state_conflict S' = Some (C, \<gamma>) \<longrightarrow> trail_false_cls (state_trail S') (C \<cdot> \<gamma>)"
    unfolding step_hyps(1,2) by simp

  ultimately show ?thesis
    unfolding ground_false_closures_def by metis
qed

lemma conflict_preserves_ground_false_closures:
  assumes step: "conflict N \<beta> S S'" and invar: "ground_false_closures S"
  shows "ground_false_closures S'"
  using step
proof (cases N \<beta> S S' rule: conflict.cases)
  case step_hyps: (conflictI D U \<gamma> \<Gamma>)

  have "ground_closures S'"
    using invar conflict_preserves_ground_closures[OF step]
    by (metis ground_false_closures_def)

  moreover have "trail_closures_false (state_trail S')"
    using invar conflict_preserves_trail_closures_false'[OF step]
    by (metis ground_false_closures_def trail_closures_false'_def)

  moreover have "\<forall>C \<gamma>. state_conflict S' = Some (C, \<gamma>) \<longrightarrow> trail_false_cls (state_trail S') (C \<cdot> \<gamma>)"
    unfolding step_hyps(1,2)
    using step_hyps(3-) by simp

  ultimately show ?thesis
    unfolding ground_false_closures_def by metis
qed

lemma skip_preserves_ground_false_closures:
  assumes step: "skip N \<beta> S S'" and invar: "ground_false_closures S"
  shows "ground_false_closures S'"
  using step
proof (cases N \<beta> S S' rule: skip.cases)
  case step_hyps: (skipI L D \<sigma> n \<Gamma> U)

  have "ground_closures S'"
    using invar skip_preserves_ground_closures[OF step]
    by (metis ground_false_closures_def)

  moreover have "trail_closures_false (state_trail S')"
    using invar skip_preserves_trail_closures_false'[OF step]
    by (metis ground_false_closures_def trail_closures_false'_def)

  moreover have "\<forall>C \<gamma>. state_conflict S' = Some (C, \<gamma>) \<longrightarrow> trail_false_cls (state_trail S') (C \<cdot> \<gamma>)"
    using invar
    unfolding step_hyps(1,2)
    using \<open>- L \<notin># D \<cdot> \<sigma>\<close>
    by (auto simp add: ground_false_closures_def elim!: subtrail_falseI)

  ultimately show ?thesis
    unfolding ground_false_closures_def by metis
qed

lemma factorize_preserves_ground_false_closures:
  assumes step: "factorize N \<beta> S S'" and invar: "ground_false_closures S"
  shows "ground_false_closures S'"
  using step
proof (cases N \<beta> S S' rule: factorize.cases)
  case step_hyps: (factorizeI L \<gamma> L' \<mu> \<Gamma> U D)

  have "ground_closures S'"
    using invar factorize_preserves_ground_closures[OF step]
    by (metis ground_false_closures_def)

  moreover have "trail_closures_false (state_trail S')"
    using invar factorize_preserves_trail_closures_false'[OF step]
    by (metis ground_false_closures_def trail_closures_false'_def)

  moreover have "\<forall>C \<gamma>. state_conflict S' = Some (C, \<gamma>) \<longrightarrow> trail_false_cls (state_trail S') (C \<cdot> \<gamma>)"
    using invar conflict_set_after_factorization[OF step]
    unfolding step_hyps(1,2) ground_false_closures_def
    by (auto simp del: set_mset_add_mset_insert dest: trail_false_cls_ignores_duplicates)

  ultimately show ?thesis
    unfolding ground_false_closures_def by metis
qed

lemma resolve_preserves_ground_false_closures:
  assumes step: "resolve N \<beta> S S'" and invar: "ground_false_closures S"
  shows "ground_false_closures S'"
  using step
proof (cases N \<beta> S S' rule: resolve.cases)
  case step_hyps: (resolveI \<Gamma> \<Gamma>' K D \<gamma>\<^sub>D L \<gamma>\<^sub>C \<rho>\<^sub>C \<rho>\<^sub>D C \<mu> \<gamma> U)
  hence \<Gamma>_def: "\<Gamma> = trail_propagate \<Gamma>' K D \<gamma>\<^sub>D"
    by simp

  have "ground_closures S"
    using invar
    by (metis ground_false_closures_def)
  hence "ground_closures S'"
    using resolve_preserves_ground_closures[OF step]
    by metis

  moreover have "trail_closures_false (state_trail S')"
    using invar resolve_preserves_trail_closures_false'[OF step]
    by (metis ground_false_closures_def trail_closures_false'_def)

  moreover have "\<forall>C \<gamma>. state_conflict S' = Some (C, \<gamma>) \<longrightarrow> trail_false_cls (state_trail S') (C \<cdot> \<gamma>)"
  proof -
    from \<open>ground_closures S\<close> have
      ground_conf: "is_ground_cls (add_mset L C \<cdot> \<gamma>\<^sub>C)" and
      ground_prop: "is_ground_cls (add_mset K D \<cdot> \<gamma>\<^sub>D)"
      unfolding step_hyps(1,2)
      by (simp_all add: ground_closures_def \<Gamma>_def propagate_lit_def)
    hence
      "\<forall>L\<in>#add_mset L C. L \<cdot>l \<rho>\<^sub>C \<cdot>l \<gamma> = L \<cdot>l \<gamma>\<^sub>C"
      "\<forall>K\<in>#add_mset K D. K \<cdot>l \<rho>\<^sub>D \<cdot>l \<gamma> = K \<cdot>l \<gamma>\<^sub>D"
      using merge_of_renamed_groundings step_hyps(3-)
      by metis+

    have "atm_of L \<cdot>a \<rho>\<^sub>C \<cdot>a \<gamma> = atm_of K \<cdot>a \<rho>\<^sub>D \<cdot>a \<gamma>"
      using \<open>K \<cdot>l \<gamma>\<^sub>D = - (L \<cdot>l \<gamma>\<^sub>C)\<close>
        \<open>\<forall>L\<in>#add_mset L C. L \<cdot>l \<rho>\<^sub>C \<cdot>l \<gamma> = L \<cdot>l \<gamma>\<^sub>C\<close>[rule_format, of L, simplified]
        \<open>\<forall>K\<in>#add_mset K D. K \<cdot>l \<rho>\<^sub>D \<cdot>l \<gamma> = K \<cdot>l \<gamma>\<^sub>D\<close>[rule_format, of K, simplified]
      by (metis atm_of_eq_uminus_if_lit_eq atm_of_subst_lit)
    hence "is_unifiers \<gamma> {{atm_of L \<cdot>a \<rho>\<^sub>C, atm_of K \<cdot>a \<rho>\<^sub>D}}"
      by (simp add: is_unifiers_def is_unifier_alt)
    hence "\<mu> \<odot> \<gamma> = \<gamma>"
      using \<open>is_imgu \<mu> {{atm_of L \<cdot>a \<rho>\<^sub>C, atm_of K \<cdot>a \<rho>\<^sub>D}}\<close>
      by (auto simp: is_imgu_def)
    hence "C \<cdot> \<rho>\<^sub>C \<cdot> \<mu> \<cdot> \<gamma> = C \<cdot> \<gamma>\<^sub>C" and "D \<cdot> \<rho>\<^sub>D \<cdot> \<mu> \<cdot> \<gamma> = D \<cdot> \<gamma>\<^sub>D"
      using \<open>\<forall>L\<in>#add_mset L C. L \<cdot>l \<rho>\<^sub>C \<cdot>l \<gamma> = L \<cdot>l \<gamma>\<^sub>C\<close> \<open>\<forall>K\<in>#add_mset K D. K \<cdot>l \<rho>\<^sub>D \<cdot>l \<gamma> = K \<cdot>l \<gamma>\<^sub>D\<close>
      by (metis insert_iff same_on_lits_clause set_mset_add_mset_insert subst_cls_comp_subst
          subst_lit_comp_subst)+

    moreover have "trail_false_cls \<Gamma> (C \<cdot> \<gamma>\<^sub>C)"
      using invar
      unfolding step_hyps(1,2)
      by (simp add: ground_false_closures_def trail_false_cls_add_mset)

    moreover have "trail_false_cls \<Gamma> (D \<cdot> \<gamma>\<^sub>D)"
    proof (rule trail_false_cls_if_trail_false_suffix)
      show "suffix \<Gamma>' \<Gamma>"
        unfolding \<open>\<Gamma> = trail_propagate \<Gamma>' K D \<gamma>\<^sub>D\<close>
        by (simp add: suffix_def)
    next
      show "trail_false_cls \<Gamma>' (D \<cdot> \<gamma>\<^sub>D)"
        using invar
        unfolding step_hyps(1,2) \<open>\<Gamma> = trail_propagate \<Gamma>' K D \<gamma>\<^sub>D\<close>
        by (auto simp: ground_false_closures_def propagate_lit_def elim: trail_closures_false.cases)
    qed

    ultimately show ?thesis
      unfolding step_hyps(1,2)
      by (simp add: trail_false_cls_plus)
  qed

  ultimately show ?thesis
    unfolding ground_false_closures_def by metis
qed

lemma backtrack_preserves_ground_false_closures:
  assumes step: "backtrack N \<beta> S S'" and invar: "ground_false_closures S"
  shows "ground_false_closures S'"
  using step
proof (cases N \<beta> S S' rule: backtrack.cases)
  case step_hyps: (backtrackI \<Gamma> \<Gamma>' \<Gamma>'' K L \<sigma> D U)

  have "ground_closures S'"
    using invar backtrack_preserves_ground_closures[OF step]
    by (metis ground_false_closures_def)

  moreover have "trail_closures_false (state_trail S')"
    using invar backtrack_preserves_trail_closures_false'[OF step]
    by (metis ground_false_closures_def trail_closures_false'_def)

  moreover have "\<forall>C \<gamma>. state_conflict S' = Some (C, \<gamma>) \<longrightarrow> trail_false_cls (state_trail S') (C \<cdot> \<gamma>)"
    unfolding step_hyps(1,2) by simp

  ultimately show ?thesis
    unfolding ground_false_closures_def by metis
qed

lemma scl_preserves_ground_false_closures:
  assumes "scl N \<beta> S S'" and "ground_false_closures S"
  shows "ground_false_closures S'"
  using assms unfolding scl_def
  using propagate_preserves_ground_false_closures decide_preserves_ground_false_closures
    conflict_preserves_ground_false_closures skip_preserves_ground_false_closures
    factorize_preserves_ground_false_closures resolve_preserves_ground_false_closures
    backtrack_preserves_ground_false_closures
  by metis


subsection \<open>Learned Clauses Are Non-empty\<close>

definition learned_nonempty where
  "learned_nonempty S \<longleftrightarrow> {#} |\<notin>| state_learned S"

lemma learned_nonempty_initial_state[simp]: "learned_nonempty initial_state"
  by (simp add: learned_nonempty_def)

lemma propagate_preserves_learned_nonempty:
  assumes "propagate N \<beta> S S'" and "learned_nonempty S"
  shows "learned_nonempty S'"
  using assms by (cases rule: propagate.cases) (simp add: learned_nonempty_def)

lemma decide_preserves_learned_nonempty:
  assumes "decide N \<beta> S S'" and "learned_nonempty S"
  shows "learned_nonempty S'"
  using assms by (cases rule: decide.cases) (simp add: learned_nonempty_def)

lemma conflict_preserves_learned_nonempty:
  assumes "conflict N \<beta> S S'" and "learned_nonempty S"
  shows "learned_nonempty S'"
  using assms by (cases rule: conflict.cases) (simp add: learned_nonempty_def)

lemma skip_preserves_learned_nonempty:
  assumes "skip N \<beta> S S'" and "learned_nonempty S"
  shows "learned_nonempty S'"
  using assms by (cases rule: skip.cases) (simp add: learned_nonempty_def)

lemma factorize_preserves_learned_nonempty:
  assumes "factorize N \<beta> S S'" and "learned_nonempty S"
  shows "learned_nonempty S'"
  using assms by (cases rule: factorize.cases) (simp add: learned_nonempty_def)

lemma resolve_preserves_learned_nonempty:
  assumes "resolve N \<beta> S S'" and "learned_nonempty S"
  shows "learned_nonempty S'"
  using assms by (cases rule: resolve.cases) (simp add: learned_nonempty_def)

lemma backtrack_preserves_learned_nonempty:
  assumes "backtrack N \<beta> S S'" and "learned_nonempty S"
  shows "learned_nonempty S'"
  using assms by (cases rule: backtrack.cases) (simp add: learned_nonempty_def)

lemma scl_preserves_learned_nonempty:
  assumes "scl N \<beta> S S'" and "learned_nonempty S"
  shows "learned_nonempty S'"
  using assms unfolding scl_def
  using propagate_preserves_learned_nonempty decide_preserves_learned_nonempty
    conflict_preserves_learned_nonempty skip_preserves_learned_nonempty
    factorize_preserves_learned_nonempty resolve_preserves_learned_nonempty
    backtrack_preserves_learned_nonempty
  by metis


subsection \<open>Backtrack Follows Conflict Resolution\<close>

definition conflict_resolution where
  "conflict_resolution N \<beta> S \<longleftrightarrow> (state_conflict S \<noteq> None \<longrightarrow>
    (\<exists>S0 S1. conflict N \<beta> S0 S1 \<and> (skip N \<beta> \<squnion> factorize N \<beta> \<squnion> resolve N \<beta>)\<^sup>*\<^sup>* S1 S))"

lemma conflict_resolution_initial_state[simp]: "conflict_resolution N \<beta> initial_state"
  by (simp add: conflict_resolution_def)

lemma propagate_preserves_conflict_resolution:
  assumes step: "propagate N \<beta> S S'"
  shows "conflict_resolution N \<beta> S'"
  using step by (auto simp: conflict_resolution_def elim: propagate.cases)

lemma decide_preserves_conflict_resolution:
  assumes step: "decide N \<beta> S S'"
  shows "conflict_resolution N \<beta> S'"
  using step by (auto simp: conflict_resolution_def elim: decide.cases)

lemma conflict_preserves_conflict_resolution:
  assumes step: "conflict N \<beta> S S'"
  shows "conflict_resolution N \<beta> S'"
  using step unfolding conflict_resolution_def by blast

lemma skip_preserves_conflict_resolution:
  assumes step: "skip N \<beta> S S'" and invar: "conflict_resolution N \<beta> S"
  shows "conflict_resolution N \<beta> S'"
  using step
proof -
  from step have "state_conflict S \<noteq> None"
    by (auto elim: skip.cases)
  with invar obtain S0 S1 where
    "conflict N \<beta> S0 S1" and "(skip N \<beta> \<squnion> factorize N \<beta> \<squnion> resolve N \<beta>)\<^sup>*\<^sup>* S1 S"
    by (auto simp: conflict_resolution_def)
  show ?thesis
    unfolding conflict_resolution_def
  proof (intro impI exI conjI)
    show "conflict N \<beta> S0 S1"
      by (rule \<open>conflict N \<beta> S0 S1\<close>)
  next
    show "(skip N \<beta> \<squnion> factorize N \<beta> \<squnion> resolve N \<beta>)\<^sup>*\<^sup>* S1 S'"
      using \<open>(skip N \<beta> \<squnion> factorize N \<beta> \<squnion> resolve N \<beta>)\<^sup>*\<^sup>* S1 S\<close> step
      by (metis (no_types, opaque_lifting) rtranclp.rtrancl_into_rtrancl sup2CI)
  qed
qed

lemma factorize_preserves_conflict_resolution:
  assumes step: "factorize N \<beta> S S'" and invar: "conflict_resolution N \<beta> S"
  shows "conflict_resolution N \<beta> S'"
  using step
proof -
  from step have "state_conflict S \<noteq> None"
    by (auto elim: factorize.cases)
  with invar obtain S0 S1 where
    "conflict N \<beta> S0 S1" and "(skip N \<beta> \<squnion> factorize N \<beta> \<squnion> resolve N \<beta>)\<^sup>*\<^sup>* S1 S"
    by (auto simp: conflict_resolution_def)
  show ?thesis
    unfolding conflict_resolution_def
  proof (intro impI exI conjI)
    show "conflict N \<beta> S0 S1"
      by (rule \<open>conflict N \<beta> S0 S1\<close>)
  next
    show "(skip N \<beta> \<squnion> factorize N \<beta> \<squnion> resolve N \<beta>)\<^sup>*\<^sup>* S1 S'"
      using \<open>(skip N \<beta> \<squnion> factorize N \<beta> \<squnion> resolve N \<beta>)\<^sup>*\<^sup>* S1 S\<close> step
      by (metis (no_types, opaque_lifting) rtranclp.rtrancl_into_rtrancl sup2CI)
  qed
qed

lemma resolve_preserves_conflict_resolution:
  assumes step: "resolve N \<beta> S S'" and invar: "conflict_resolution N \<beta> S"
  shows "conflict_resolution N \<beta> S'"
  using step
proof -
  from step have "state_conflict S \<noteq> None"
    by (auto elim: resolve.cases)
  with invar obtain S0 S1 where
    "conflict N \<beta> S0 S1" and "(skip N \<beta> \<squnion> factorize N \<beta> \<squnion> resolve N \<beta>)\<^sup>*\<^sup>* S1 S"
    by (auto simp: conflict_resolution_def)
  show ?thesis
    unfolding conflict_resolution_def
  proof (intro impI exI conjI)
    show "conflict N \<beta> S0 S1"
      by (rule \<open>conflict N \<beta> S0 S1\<close>)
  next
    show "(skip N \<beta> \<squnion> factorize N \<beta> \<squnion> resolve N \<beta>)\<^sup>*\<^sup>* S1 S'"
      using \<open>(skip N \<beta> \<squnion> factorize N \<beta> \<squnion> resolve N \<beta>)\<^sup>*\<^sup>* S1 S\<close> step
      by (metis (no_types, opaque_lifting) rtranclp.rtrancl_into_rtrancl sup2CI)
  qed
qed

lemma backtrack_preserves_conflict_resolution:
  assumes step: "backtrack N \<beta> S S'"
  shows "conflict_resolution N \<beta> S'"
  using step by (auto simp: conflict_resolution_def elim: backtrack.cases)

lemma scl_preserves_conflict_resolution:
  assumes "scl N \<beta> S S'" and "conflict_resolution N \<beta> S"
  shows "conflict_resolution N \<beta> S'"
  using assms unfolding scl_def
  using propagate_preserves_conflict_resolution decide_preserves_conflict_resolution
    conflict_preserves_conflict_resolution skip_preserves_conflict_resolution
    factorize_preserves_conflict_resolution resolve_preserves_conflict_resolution
    backtrack_preserves_conflict_resolution
  by metis


subsection \<open>Miscellaneous Lemmas\<close>

lemma before_conflict:
  assumes "conflict N \<beta> S1 S2" and
    invars: "learned_nonempty S1" "trail_propagated_or_decided' N \<beta> S1"
  shows "{#} |\<in>| N \<or> (\<exists>S0. propagate N \<beta> S0 S1) \<or> (\<exists>S0. decide N \<beta> S0 S1)"
  using assms
proof (cases N \<beta> S1 S2 rule: conflict.cases)
  case (conflictI D U \<gamma> \<Gamma>)
  with invars(2) have "trail_propagated_or_decided N \<beta> U \<Gamma>"
    by (simp add: trail_propagated_or_decided'_def)
  thus ?thesis
  proof (cases N \<beta> U \<Gamma> rule: trail_propagated_or_decided.cases)
    case Nil
    hence "D \<cdot> \<gamma> = {#}"
      using \<open>trail_false_cls \<Gamma> (D \<cdot> \<gamma>)\<close> not_trail_false_Nil(2) by blast
    hence "D = {#}"
      by (simp add: local.conflictI(4))
    moreover from invars(1) have "{#} |\<notin>| U"
      by (simp add: conflictI(1) learned_nonempty_def)
    ultimately have "{#} |\<in>| N"
      using \<open>D |\<in>| N |\<union>| U\<close> by simp
    thus ?thesis by simp
  next
    case (Propagate C L C' \<gamma>\<^sub>C C\<^sub>0 C\<^sub>1 \<Gamma>' \<mu>)
    hence "\<exists>S0. propagate N \<beta> S0 S1"
      unfolding conflictI(1)
      using propagateI by blast
    thus ?thesis by simp
  next
    case (Decide L \<gamma>\<^sub>L \<Gamma>')
    hence "\<exists>S0. decide N \<beta> S0 S1"
      unfolding conflictI(1)
      using decideI by blast
    thus ?thesis by simp
  qed
qed

lemma before_backtrack:
  assumes backt: "backtrack N \<beta> Sn Sm" and
    invar: "conflict_resolution N \<beta> Sn"
  shows "\<exists>S0 S1. conflict N \<beta> S0 S1 \<and> (skip N \<beta> \<squnion> factorize N \<beta> \<squnion> resolve N \<beta>)\<^sup>*\<^sup>* S1 Sn"
  using backt
proof (cases N \<beta> Sn Sm rule: backtrack.cases)
  case (backtrackI \<Gamma> \<Gamma>' \<Gamma>'' L \<sigma> D U)
  thus ?thesis
    using invar by (simp add: conflict_resolution_def)
qed

lemma ball_less_B_if_trail_false_and_trail_atoms_lt:
  "trail_false_cls (state_trail S) C \<Longrightarrow> trail_atoms_lt \<beta> S \<Longrightarrow> \<forall>L \<in># C. atm_of L \<prec>\<^sub>B \<beta>"
  unfolding trail_atoms_lt_def
  by (meson atm_of_in_atm_of_set_iff_in_set_or_uminus_in_set trail_false_cls_def
      trail_false_lit_def)


section \<open>Soundness\<close>


subsection \<open>Sound Trail\<close>

abbreviation entails_\<G> (infix "\<TTurnstile>\<G>e" 50) where
  "entails_\<G> N U \<equiv> grounding_of_clss N \<TTurnstile>e grounding_of_clss U"

definition sound_trail where
  "sound_trail N \<Gamma> \<longleftrightarrow>
    (\<forall>Ln \<in> set \<Gamma>. \<forall>D K \<gamma>. snd Ln = Some (D, K, \<gamma>) \<longrightarrow> fset N \<TTurnstile>\<G>e {add_mset K D})"

lemma sound_trail_Nil[simp]: "sound_trail N []"
  by (simp add: sound_trail_def)

lemma entails_\<G>_mono: "N \<TTurnstile>\<G>e U \<Longrightarrow> N \<subseteq> NN \<Longrightarrow> NN \<TTurnstile>\<G>e U"
  by (meson grounding_of_clss_mono true_clss_mono)

lemma sound_trail_supersetI: "sound_trail N \<Gamma> \<Longrightarrow> N |\<subseteq>| NN \<Longrightarrow> sound_trail NN \<Gamma>"
  unfolding sound_trail_def
  by (meson entails_\<G>_mono less_eq_fset.rep_eq)

lemma sound_trail_ConsD: "sound_trail N (Ln # \<Gamma>) \<Longrightarrow> sound_trail N \<Gamma>"
  by (simp add: sound_trail_def)

lemma sound_trail_appendD: "sound_trail N (\<Gamma> @ \<Gamma>') \<Longrightarrow> sound_trail N \<Gamma>'"
  by (induction \<Gamma>) (auto intro: sound_trail_ConsD)

lemma sound_trail_propagate:
  assumes
    sound_\<Gamma>: "sound_trail N \<Gamma>" and
    N_entails_C_L: "fset N \<TTurnstile>\<G>e {C + {#L#}}"
  shows "sound_trail N (trail_propagate \<Gamma> L C \<sigma>)"
  using assms
  by (simp add: sound_trail_def propagate_lit_def)

lemma sound_trail_decide:
  "sound_trail N \<Gamma> \<Longrightarrow> sound_trail N (trail_decide \<Gamma> L)"
  by (simp add: sound_trail_def decide_lit_def)


subsection \<open>Sound State\<close>

definition sound_state :: "('f, 'v) term clause fset \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) state \<Rightarrow> bool" where
  "sound_state N \<beta> S \<longleftrightarrow>
    (\<exists>\<Gamma> U u. S = (\<Gamma>, U, u) \<and> sound_trail N \<Gamma> \<and> fset N \<TTurnstile>\<G>e fset U \<and>
    (case u of None \<Rightarrow> True | Some (C, \<gamma>) \<Rightarrow> fset N \<TTurnstile>\<G>e {C}))"


subsection \<open>Initial State Is Sound\<close>

lemma sound_initial_state[simp]: "sound_state N \<beta> initial_state"
  by (simp add: sound_state_def trail_atoms_lt_def)


subsection \<open>SCL Rules Preserve Soundness\<close>

lemma mem_vars_cls_subst_clsD: "x' \<in> vars_cls (C \<cdot> \<rho>) \<Longrightarrow> \<exists>x\<in>vars_cls C. x' \<in> vars_term (\<rho> x)"
  unfolding vars_subst_cls_eq
  using subst_domain_def by force

lemma propagate_preserves_sound_state:
  assumes step: "propagate N \<beta> S S'" and sound: "sound_state N \<beta> S"
  shows "sound_state N \<beta> S'"
  using assms(1)
proof (cases N \<beta> S S' rule: propagate.cases)
  case (propagateI C U L C' \<gamma> C\<^sub>0 C\<^sub>1 \<Gamma> \<mu>)
  hence
    S_def: "S = (\<Gamma>, U, None)" and
    S'_def: "S' = (trail_propagate \<Gamma> (L \<cdot>l \<mu>) (C\<^sub>0 \<cdot> \<mu>) \<gamma>, U, None)" and
    C_in: "C |\<in>| N |\<union>| U" and
    C_def: "C = add_mset L C'" and
    gr_C_\<gamma>: "is_ground_cls (C \<cdot> \<gamma>)" and
    C\<^sub>0_def: "C\<^sub>0 = {#K \<in># C'. K \<cdot>l \<gamma> \<noteq> L \<cdot>l \<gamma>#}" and
    C\<^sub>1_def: "C\<^sub>1 = {#K \<in># C'. K \<cdot>l \<gamma> = L \<cdot>l \<gamma>#}" and
    \<Gamma>_false_C\<^sub>0_\<gamma>: "trail_false_cls \<Gamma> (C\<^sub>0 \<cdot> \<gamma>)" and
    undef_\<Gamma>_L_\<gamma>: "\<not> trail_defined_lit \<Gamma> (L \<cdot>l \<gamma>)" and
    imgu_\<mu>: "is_imgu \<mu> {atm_of ` set_mset (add_mset L C\<^sub>1)}"
    by simp_all

  from sound have
    sound_\<Gamma>: "sound_trail N \<Gamma>" and
    N_entails_U: "fset N \<TTurnstile>\<G>e fset U"
    unfolding sound_state_def S_def by auto

  have vars_C\<^sub>0: "vars_cls C\<^sub>0 \<subseteq> vars_cls C'"
    apply (simp add: C\<^sub>0_def)
    by (metis multiset_partition order_refl sup.coboundedI1 vars_cls_plus_iff)

  have vars_C\<^sub>1: "vars_cls C\<^sub>1 \<subseteq> vars_cls C'"
    apply (simp add: C\<^sub>1_def)
    by (metis multiset_partition order_refl sup.coboundedI1 vars_cls_plus_iff)

  have fin_atm_C\<^sub>1: "finite (atm_of ` (set_mset C\<^sub>1))"
    by blast
  hence "is_unifier \<gamma> (atm_of ` (set_mset (add_mset L C\<^sub>1)))"
    by (auto simp add: is_unifier_alt C\<^sub>1_def intro: subst_atm_of_eqI)
  hence \<mu>_\<gamma>_simp: "\<mu> \<odot> \<gamma> = \<gamma>"
    using imgu_\<mu>[unfolded is_imgu_def, THEN conjunct2]
    using is_unifiers_def by fastforce

  have "L \<cdot>l \<mu> \<cdot>l \<gamma> = L \<cdot>l \<gamma>"
    using \<mu>_\<gamma>_simp by (metis subst_lit_comp_subst)

  have "C\<^sub>0 \<cdot> \<mu> \<cdot> \<gamma> = C\<^sub>0 \<cdot> \<gamma>"
    using \<mu>_\<gamma>_simp by (metis subst_cls_comp_subst)

  have "sound_trail N (trail_propagate \<Gamma> (L \<cdot>l \<mu>) (C\<^sub>0 \<cdot> \<mu>) \<gamma>)"
  proof (rule sound_trail_propagate)
    show "sound_trail N \<Gamma>"
      by (rule sound_\<Gamma>)
  next
    from C_in N_entails_U have "fset N \<TTurnstile>\<G>e {C}"
      by (metis (no_types, opaque_lifting) empty_subsetI funion_iff grounding_of_clss_mono
          insert_subset notin_fset true_clss_mono)
    hence "fset N \<TTurnstile>\<G>e {add_mset L (C\<^sub>0 + C\<^sub>1)}"
      by (simp add: C_def C\<^sub>0_def C\<^sub>1_def)
    hence "fset N \<TTurnstile>\<G>e {add_mset L (C\<^sub>0 + C\<^sub>1) \<cdot> \<mu>}"
      by (metis (no_types, opaque_lifting) grounding_of_clss_singleton
          subst_cls_eq_grounding_of_cls_subset_eq true_clss_mono)
    hence "fset N \<TTurnstile>\<G>e {add_mset L C\<^sub>0 \<cdot> \<mu>}"
    proof (rule entails_trans)
      have "\<exists>C\<in>grounding_of_clss {(C\<^sub>0 + C\<^sub>1 + {#L#}) \<cdot> \<mu>}. set_mset D = set_mset C"
        if D_in: "D \<in> grounding_of_clss {(C\<^sub>0 + {#L#}) \<cdot> \<mu>}" for I D
      proof-
        from D_in obtain \<sigma> where
          D_def: "D = add_mset L C\<^sub>0 \<cdot> \<mu> \<cdot> \<sigma>" and gr_\<sigma>: "is_ground_subst \<sigma>"
          by (auto simp: grounding_of_cls_def)
        show ?thesis
        proof (rule bexI)
          from imgu_\<mu> have "is_unifier \<mu> (atm_of ` set_mset (add_mset L C\<^sub>1))"
            by (simp add: is_imgu_def is_unifiers_def)
          hence "\<forall>A\<in>atm_of ` set_mset (add_mset L C\<^sub>1). \<forall>B\<in>atm_of ` set_mset (add_mset L C\<^sub>1).
            A \<cdot>a \<mu> = B \<cdot>a \<mu>"
            using is_unifier_alt
            by (metis (mono_tags, opaque_lifting) finite_imageI finite_set_mset)
          hence "\<forall>A\<in>atm_of ` set_mset C\<^sub>1. A \<cdot>a \<mu> = atm_of L \<cdot>a \<mu>"
            by (metis image_insert insert_iff set_mset_add_mset_insert)
          hence "\<forall>A\<in>set_mset C\<^sub>1. A \<cdot>l \<mu> = L \<cdot>l \<mu>"
            unfolding C\<^sub>1_def
            by (metis (mono_tags, lifting) atm_of_subst_lit image_eqI literal.expand mem_Collect_eq
                set_mset_filter subst_lit_is_neg)
          hence "set_mset ((add_mset L C\<^sub>1) \<cdot> \<mu>) = {L \<cdot>l \<mu>}"
            by auto
          hence "set_mset ((C\<^sub>0 + C\<^sub>1 + {#L#}) \<cdot> \<mu>) = set_mset ((C\<^sub>0 + {#L#}) \<cdot> \<mu>)"
            by auto
          thus "set_mset D = set_mset ((C\<^sub>0 + C\<^sub>1 + {#L#}) \<cdot> \<mu> \<cdot> \<sigma>)"
            unfolding D_def set_mset_subst_cls_conv[of _ \<sigma>]
            by simp
        next
          show "(C\<^sub>0 + C\<^sub>1 + {#L#}) \<cdot> \<mu> \<cdot> \<sigma> \<in> grounding_of_clss {(C\<^sub>0 + C\<^sub>1 + {#L#}) \<cdot> \<mu>}"
            using gr_\<sigma> by (auto simp: grounding_of_cls_def)
        qed
      qed
      then show "{add_mset L (C\<^sub>0 + C\<^sub>1) \<cdot> \<mu>} \<TTurnstile>\<G>e {add_mset L C\<^sub>0 \<cdot> \<mu>}"
        by (auto elim: true_clss_if_set_mset_eq[rotated])
    qed
    thus "fset N \<TTurnstile>\<G>e {C\<^sub>0 \<cdot> \<mu> + {#L \<cdot>l \<mu>#}}"
      by (metis (no_types, opaque_lifting) add_mset_add_single grounding_of_clss_singleton
          subst_cls_add_mset)
  qed
  thus ?thesis
    unfolding S'_def sound_state_def
    using N_entails_U by simp
qed

lemma decide_preserves_sound_state:
  assumes step: "decide N \<beta> S S'" and sound: "sound_state N \<beta> S"
  shows "sound_state N \<beta> S'"
  using assms(1)
proof (cases N \<beta> S S' rule: decide.cases)
  case (decideI L \<gamma> \<Gamma> U)
  from decideI(1) sound have
    sound_\<Gamma>: "sound_trail N \<Gamma>" and
    N_entails_U: "fset N \<TTurnstile>\<G>e fset U"
    unfolding sound_state_def by auto

  moreover have "sound_trail N (trail_decide \<Gamma> (L \<cdot>l \<gamma>))"
    by (simp add: local.decideI(4) local.decideI(5) sound_\<Gamma> sound_trail_decide)

  ultimately show ?thesis
    unfolding decideI sound_state_def by simp
qed

lemma conflict_preserves_sound_state:
  assumes step: "conflict N \<beta> S S'" and sound: "sound_state N \<beta> S"
  shows "sound_state N \<beta> S'"
  using assms(1)
proof (cases N \<beta> S S' rule: conflict.cases)
  case (conflictI D U \<gamma> \<Gamma>)
  hence D_in: "D |\<in>| N |\<union>| U" by simp
  
  from conflictI(1) sound have
    sound_\<Gamma>: "sound_trail N \<Gamma>" and
    N_entails_U: "fset N \<TTurnstile>\<G>e fset U"
    unfolding sound_state_def by auto

  have N_entails_D': "fset N \<TTurnstile>\<G>e {D}"
  proof (intro allI impI)
    fix I
    assume valid_N: "I \<TTurnstile>s grounding_of_clss (fset N)"
    then show "I \<TTurnstile>s grounding_of_clss {D}"
      using D_in
      unfolding grounding_of_clss_singleton
      by (metis (mono_tags, opaque_lifting) N_entails_U UN_I funion_iff grounding_of_clss_def
          notin_fset true_clss_def)
  qed
  thus ?thesis
    unfolding conflictI(1,2) sound_state_def
    using sound_\<Gamma> N_entails_U by simp
qed

lemma skip_preserves_sound_state:
  assumes step: "skip N \<beta> S S'" and sound: "sound_state N \<beta> S"
  shows "sound_state N \<beta> S'"
  using step
proof (cases N \<beta> S S' rule: skip.cases)
  case (skipI L D \<sigma> Cl \<Gamma> U)
  thus ?thesis
    using sound
    by (auto simp: sound_state_def trail_atoms_lt_def
        intro: sound_trail_ConsD elim!: subtrail_falseI)
qed

lemma factorize_preserves_sound_state:
  assumes step: "factorize N \<beta> S S'" and sound: "sound_state N \<beta> S"
  shows "sound_state N \<beta> S'"
  using assms(1)
proof (cases N \<beta> S S' rule: factorize.cases)
  case (factorizeI L \<gamma> L' \<mu> \<Gamma> U D)

  from factorizeI(1) sound have
    sound_\<Gamma>: "sound_trail N \<Gamma>" and
    N_entails_U: "fset N \<TTurnstile>\<G>e fset U" and
    N_entails_D_L_L': "fset N \<TTurnstile>\<G>e {D + {#L, L'#}}"
    unfolding sound_state_def by (simp_all add: add_mset_commute)

  from factorizeI have
    imgu_\<mu>: "is_imgu \<mu> {{atm_of L, atm_of L'}}"
    by simp
  from factorizeI have L_eq_L'_\<gamma>: "L \<cdot>l \<gamma> = L' \<cdot>l \<gamma>" by simp

  from L_eq_L'_\<gamma> have unif_\<gamma>: "is_unifier \<gamma> {atm_of L, atm_of L'}"
    by (auto simp: is_unifier_alt intro: subst_atm_of_eqI)
  hence unifs_\<gamma>: "is_unifiers \<gamma> {{atm_of L, atm_of L'}}"
    by (simp add: is_unifiers_def)

  from imgu_\<mu> have "is_unifier \<mu> {atm_of L, atm_of L'}"
    by (auto simp add: is_unifiers_def dest: is_imgu_is_mgu[THEN is_mgu_is_unifiers])
  hence L_eq_L'_\<mu>: "L \<cdot>l \<mu> = L' \<cdot>l \<mu>"
    apply (simp add: is_unifier_alt)
    by (metis L_eq_L'_\<gamma> atm_of_subst_lit literal.expand subst_lit_is_neg)

  have "fset N \<TTurnstile>\<G>e {(D + {#L#}) \<cdot> \<mu>}"
  proof (rule entails_trans)
    show "fset N \<TTurnstile>\<G>e {D + {#L, L'#}}"
      by (rule N_entails_D_L_L')
  next
    have *: "{(D + {#L, L'#}) \<cdot> \<mu>} = {D \<cdot> \<mu> + {#L \<cdot>l \<mu>, L \<cdot>l \<mu>#}}"
      by (simp add: L_eq_L'_\<mu>)

    have "{D + {#L, L'#}} \<TTurnstile>\<G>e {(D + {#L, L'#}) \<cdot> \<mu>}"
      using subst_cls_eq_grounding_of_cls_subset_eq true_clss_mono
      by (metis (mono_tags, lifting) grounding_of_clss_singleton)

    moreover have "{(D + {#L, L'#}) \<cdot> \<mu>} \<TTurnstile>\<G>e {(D + {#L#}) \<cdot> \<mu>}"
      apply (intro allI impI)
      by (erule true_clss_if_set_mset_eq[rotated]) (auto simp add: L_eq_L'_\<mu> grounding_of_cls_def)

    ultimately show "{D + {#L, L'#}} \<TTurnstile>\<G>e {(D + {#L#}) \<cdot> \<mu>}"
      by simp
  qed
  thus ?thesis
    unfolding factorizeI sound_state_def
    using sound_\<Gamma> N_entails_U by simp
qed

lemma resolve_preserves_sound_state:
  assumes step: "resolve N \<beta> S S'" and sound: "sound_state N \<beta> S"
  shows "sound_state N \<beta> S'"
  using assms(1)
proof (cases N \<beta> S S' rule: resolve.cases)
  case (resolveI \<Gamma> \<Gamma>' K D \<gamma>\<^sub>D L \<gamma>\<^sub>C \<rho>\<^sub>C \<rho>\<^sub>D C \<mu> \<gamma> U)
  hence
    \<Gamma>_def: "\<Gamma> = trail_propagate \<Gamma>' K D \<gamma>\<^sub>D" and
    imgu_\<mu>: "is_imgu \<mu> {{atm_of L \<cdot>a \<rho>\<^sub>C, atm_of K \<cdot>a \<rho>\<^sub>D}}"
    by simp_all

  from sound have
    sound_\<Gamma>: "sound_trail N \<Gamma>" and
    N_entails_U: "fset N \<TTurnstile>\<G>e fset U" and
    N_entails_conf: "fset N \<TTurnstile>\<G>e {add_mset L C}"
    unfolding resolveI(1,2) sound_state_def by simp_all

  from sound_\<Gamma> have
    N_entails_prop: "fset N \<TTurnstile>\<G>e {add_mset K D}"
    unfolding sound_trail_def \<Gamma>_def
    by (simp add: propagate_lit_def)

  moreover have "fset N \<TTurnstile>\<G>e {(C \<cdot> \<rho>\<^sub>C + D \<cdot> \<rho>\<^sub>D) \<cdot> \<mu>}"
  proof -
    have *: "fset N \<TTurnstile>\<G>e {add_mset L C \<cdot> \<rho>\<^sub>C \<cdot> \<mu>}"
      using N_entails_conf
      by (metis (no_types, opaque_lifting) grounding_of_clss_singleton grounding_of_subst_cls_subset
          true_clss_mono)

    have **: "fset N \<TTurnstile>\<G>e {add_mset K D \<cdot> \<rho>\<^sub>D \<cdot> \<mu>}"
      using N_entails_prop
      by (metis (no_types, opaque_lifting) grounding_of_clss_singleton grounding_of_subst_cls_subset
          true_clss_mono)

    show "fset N \<TTurnstile>\<G>e {(C \<cdot> \<rho>\<^sub>C + D \<cdot> \<rho>\<^sub>D) \<cdot> \<mu>}"
      unfolding true_clss_def
    proof (intro allI impI ballI)
      fix I E
      assume I_entails: "\<forall>E \<in> grounding_of_clss (fset N). I \<TTurnstile> E" and
        E_in: "E \<in> grounding_of_clss {(C \<cdot> \<rho>\<^sub>C + D \<cdot> \<rho>\<^sub>D) \<cdot> \<mu>}"
      then obtain \<gamma>\<^sub>E where
        E_def: "E = (C \<cdot> \<rho>\<^sub>C + D \<cdot> \<rho>\<^sub>D) \<cdot> \<mu> \<cdot> \<gamma>\<^sub>E" and gr_\<gamma>\<^sub>E: "is_ground_subst \<gamma>\<^sub>E"
        unfolding grounding_of_clss_def grounding_of_cls_def by auto

      have "I \<TTurnstile>l L \<cdot>l \<rho>\<^sub>C \<cdot>l \<mu> \<cdot>l \<gamma>\<^sub>E \<or> (\<exists>x \<in># C \<cdot> \<rho>\<^sub>C \<cdot> \<mu> \<cdot> \<gamma>\<^sub>E. I \<TTurnstile>l x)"
      proof -
        have "add_mset L C \<cdot> \<rho>\<^sub>C \<cdot> \<mu> \<cdot> \<gamma>\<^sub>E \<in> grounding_of_clss {add_mset L C \<cdot> \<rho>\<^sub>C \<cdot> \<mu>}"
          using gr_\<gamma>\<^sub>E unfolding grounding_of_clss_def grounding_of_cls_def by auto
        hence "\<exists>K \<in># add_mset L C \<cdot> \<rho>\<^sub>C \<cdot> \<mu> \<cdot> \<gamma>\<^sub>E. I \<TTurnstile>l K"
          using *[rule_format, unfolded true_clss_def, OF I_entails]
          by (metis true_cls_def)
        thus ?thesis
          by simp
      qed

      moreover have "I \<TTurnstile>l K \<cdot>l \<rho>\<^sub>D \<cdot>l \<mu> \<cdot>l \<gamma>\<^sub>E \<or> (\<exists>x \<in># D \<cdot> \<rho>\<^sub>D \<cdot> \<mu> \<cdot> \<gamma>\<^sub>E. I \<TTurnstile>l x)"
      proof -
        have "add_mset K D \<cdot> \<rho>\<^sub>D \<cdot> \<mu> \<cdot> \<gamma>\<^sub>E \<in> grounding_of_clss {add_mset K D \<cdot> \<rho>\<^sub>D \<cdot> \<mu>}"
          using gr_\<gamma>\<^sub>E unfolding grounding_of_clss_def grounding_of_cls_def by auto
        hence "\<exists>K \<in># add_mset K D \<cdot> \<rho>\<^sub>D \<cdot> \<mu> \<cdot> \<gamma>\<^sub>E. I \<TTurnstile>l K"
          using **[rule_format, unfolded true_clss_def, OF I_entails]
          by (metis true_cls_def)
        thus ?thesis
          by simp
      qed

      ultimately show "I \<TTurnstile> E"
      proof (elim disjE)
        assume "I \<TTurnstile>l L \<cdot>l \<rho>\<^sub>C \<cdot>l \<mu> \<cdot>l \<gamma>\<^sub>E" and "I \<TTurnstile>l K \<cdot>l \<rho>\<^sub>D \<cdot>l \<mu> \<cdot>l \<gamma>\<^sub>E"
        moreover have "atm_of L \<cdot>a \<rho>\<^sub>C \<cdot>a \<mu> = atm_of K \<cdot>a \<rho>\<^sub>D \<cdot>a \<mu>"
          using imgu_\<mu>[unfolded is_imgu_def]
          by (meson finite.emptyI finite.insertI insertCI is_unifier_alt is_unifiers_def)
        ultimately have False
          using \<open>K \<cdot>l \<gamma>\<^sub>D = - (L \<cdot>l \<gamma>\<^sub>C)\<close>
          by (cases L; cases K; simp add: uminus_literal_def subst_lit_def)
        thus ?thesis ..
      qed (auto simp: E_def)
    qed
  qed

  moreover have "sound_trail N (trail_propagate \<Gamma>' K D \<gamma>\<^sub>D)"
    using \<Gamma>_def sound_\<Gamma> by blast

  ultimately show ?thesis
    unfolding resolveI sound_state_def
    using N_entails_U by simp
qed

lemma backtrack_preserves_sound_state:
  assumes step: "backtrack N \<beta> S S'" and sound: "sound_state N \<beta> S"
  shows "sound_state N \<beta> S'"
  using assms(1)
proof (cases N \<beta> S S' rule: backtrack.cases)
  case (backtrackI \<Gamma> \<Gamma>' \<Gamma>'' K L \<sigma> D U)
  from backtrackI(1) sound have
    sound_\<Gamma>: "sound_trail N \<Gamma>" and
    N_entails_U: "fset N \<TTurnstile>\<G>e fset U" and
    N_entails_D_L_L': "fset N \<TTurnstile>\<G>e {D + {#L#}}"
    unfolding sound_state_def by simp_all

  from backtrackI have \<Gamma>_def: "\<Gamma> = trail_decide (\<Gamma>' @ \<Gamma>'') (- (L \<cdot>l \<sigma>))" by simp

  moreover have "sound_trail N \<Gamma>''"
  proof -
    from sound_\<Gamma> have "sound_trail N \<Gamma>"
      by (rule sound_trail_supersetI) auto
    then show ?thesis
      by (auto simp: \<Gamma>_def decide_lit_def intro: sound_trail_ConsD sound_trail_appendD)
  qed

  moreover have "fset N \<TTurnstile>\<G>e (fset U \<union> {D + {#L#}})"
    using N_entails_U N_entails_D_L_L' by (metis UN_Un grounding_of_clss_def true_clss_union)

  ultimately show ?thesis
    unfolding backtrackI sound_state_def by simp
qed

theorem scl_preserves_sound_state:
  fixes N :: "('f, 'v) Term.term clause fset"
  shows "scl N \<beta> S S' \<Longrightarrow> sound_state N \<beta> S \<Longrightarrow> sound_state N \<beta> S'"
  unfolding scl_def
  using propagate_preserves_sound_state decide_preserves_sound_state conflict_preserves_sound_state skip_preserves_sound_state
    factorize_preserves_sound_state resolve_preserves_sound_state backtrack_preserves_sound_state
  by metis


section \<open>Strategies\<close>

definition reasonable_scl where
  "reasonable_scl N \<beta> S S' \<longleftrightarrow>
    scl N \<beta> S S' \<and> (decide N \<beta> S S' \<longrightarrow> \<not>(\<exists>S''. conflict N \<beta> S' S''))"

lemma scl_if_reasonable: "reasonable_scl N \<beta> S S' \<Longrightarrow> scl N \<beta> S S'"
  unfolding reasonable_scl_def scl_def by simp

definition regular_scl where
  "regular_scl N \<beta> S S' \<longleftrightarrow>
    conflict N \<beta> S S' \<or> \<not> (\<exists>S''. conflict N \<beta> S S'') \<and> reasonable_scl N \<beta> S S'"

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

lemma scl_if_regular:
  "regular_scl N \<beta> S S' \<Longrightarrow> scl N \<beta> S S'"
  using scl_if_reasonable reasonable_if_regular by simp

text \<open>The following specification of @{const regular_scl} is better for the paper as it highlights
that it is a restriction of @{const reasonable_scl}.\<close>

lemma "regular_scl N \<beta> S S' \<longleftrightarrow> reasonable_scl N \<beta> S S' \<and>
  ((\<exists>S''. conflict N \<beta> S S'') \<longrightarrow> conflict N \<beta> S S')"
  (is "?lhs = ?rhs")
proof (rule iffI)
  assume ?lhs
  thus ?rhs
    unfolding regular_scl_def
  proof (elim disjE conjE)
    assume conf: "conflict N \<beta> S S'"
    show ?rhs
    proof (rule conjI)
      from conf have "\<not> decide N \<beta> S S'"
        by (simp add: conflict_well_defined(2))
      with conf show "reasonable_scl N \<beta> S S'"
        unfolding reasonable_scl_def scl_def by simp
    next
      show "(\<exists>S''. conflict N \<beta> S S'') \<longrightarrow> conflict N \<beta> S S'"
        using conf by simp
    qed
  next
    assume "\<not> (\<exists>S''. conflict N \<beta> S S'')" and "reasonable_scl N \<beta> S S'"
    thus ?rhs
      by simp
  qed
next
  assume ?rhs
  thus ?lhs
  proof (cases "\<exists>S''. conflict N \<beta> S S''")
    case True
    with \<open>?rhs\<close> have "conflict N \<beta> S S'"
      by blast
    then show ?thesis
      unfolding regular_scl_def
      by simp
  next
    case False
    then show ?thesis
      unfolding regular_scl_def
      using \<open>?rhs\<close> by simp
  qed
qed

definition ex_conflict where
  "ex_conflict C \<Gamma> \<longleftrightarrow> (\<exists>\<gamma>. is_ground_cls (C \<cdot> \<gamma>) \<and> trail_false_cls \<Gamma> (C \<cdot> \<gamma>))"

definition is_shortest_backtrack where
  "is_shortest_backtrack C \<Gamma> \<Gamma>\<^sub>0 \<longleftrightarrow> C \<noteq> {#} \<longrightarrow> suffix \<Gamma>\<^sub>0 \<Gamma> \<and> \<not> ex_conflict C \<Gamma>\<^sub>0 \<and>
    (\<forall>Kn. suffix (Kn # \<Gamma>\<^sub>0) \<Gamma> \<longrightarrow> ex_conflict C (Kn # \<Gamma>\<^sub>0))"

definition shortest_backtrack_strategy where
  "shortest_backtrack_strategy R N \<beta> S S' \<longleftrightarrow> R N \<beta> S S' \<and> (backtrack N \<beta> S S' \<longrightarrow>
    is_shortest_backtrack (fst (the (state_conflict S))) (state_trail S) (state_trail S'))"

lemma regular_scl_if_shortest_backtrack_strategy:
  "shortest_backtrack_strategy regular_scl N \<beta> S S' \<Longrightarrow> regular_scl N \<beta> S S'"
  by (simp add: shortest_backtrack_strategy_def)

primrec shortest_backtrack where
  "shortest_backtrack C [] = []" |
  "shortest_backtrack C (Ln # \<Gamma>) =
    (if ex_conflict C (Ln # \<Gamma>) then
      shortest_backtrack C \<Gamma>
    else
      Ln # \<Gamma>)"

lemma suffix_shortest_backtrack: "suffix (shortest_backtrack C \<Gamma>) \<Gamma>"
  by (induction \<Gamma>) (simp_all add: suffix_Cons)

lemma ex_conflict_shortest_backtrack: "ex_conflict C (shortest_backtrack C \<Gamma>) \<longleftrightarrow> C = {#}"
  by (induction \<Gamma>) (auto simp add: ex_conflict_def)

lemma is_shortest_backtrack_shortest_backtrack:
  "C \<noteq> {#} \<Longrightarrow> is_shortest_backtrack C \<Gamma> (shortest_backtrack C \<Gamma>)"
proof (induction \<Gamma>)
  case Nil
  then show ?case
    by (simp add: is_shortest_backtrack_def ex_conflict_def)
next
  case (Cons Kn \<Gamma>)
  then show ?case
    apply (simp del: )
    apply (rule conjI)
     apply (simp add: is_shortest_backtrack_def suffix_Cons)
    by (meson is_shortest_backtrack_def not_Cons_self2 suffix_ConsD suffix_appendD
        suffix_order.dual_order.antisym suffix_order.dual_order.refl)
qed

end

end