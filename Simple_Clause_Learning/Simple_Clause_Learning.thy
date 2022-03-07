theory Simple_Clause_Learning
  imports
    Main
    Saturation_Framework.Calculus
    Saturation_Framework_Extensions.Clausal_Calculus
    Ordered_Resolution_Prover.Clausal_Logic
    Ordered_Resolution_Prover.Abstract_Substitution
    Ordered_Resolution_Prover.Herbrand_Interpretation
    First_Order_Terms.Unification
    First_Order_Terms.Subsumption
    (* Functional_Ordered_Resolution_Prover.IsaFoR_Term *)
    Abstract_Renaming_Apart
begin


section \<open>List_Extra\<close>

primrec find_map where
  "find_map f [] = None" |
  "find_map f (x # xs) = (case f x of None \<Rightarrow> find_map f xs | Some y \<Rightarrow> Some y)"

lemma find_map_conv: "find_map f xs = Option.bind (find (\<lambda>x. f x \<noteq> None) xs) f"
  by (induction xs) auto


section \<open>Multiset_Extra\<close>

lemma Multiset_Bex_plus_iff: "(\<exists>x \<in># (M1 + M2). P x) \<longleftrightarrow> (\<exists>x \<in># M1. P x) \<or> (\<exists>x \<in># M2. P x)"
  by auto


section \<open>Calculus_Extra\<close>

lemma (in consequence_relation) entails_one_formula: "N \<Turnstile> U \<Longrightarrow> D \<in> U \<Longrightarrow> N \<Turnstile> {D}"
  using entail_set_all_formulas by blast


section \<open>Clausal_Calculus_Extra\<close>

lemma true_cls_iff_set_mset_eq: "set_mset C = set_mset D \<Longrightarrow> I \<TTurnstile> C \<longleftrightarrow> I \<TTurnstile> D"
  by (simp add: true_cls_def)

lemma true_clss_if_set_mset_eq: "(\<forall>D \<in> \<D>. \<exists>C \<in> \<C>. set_mset D = set_mset C) \<Longrightarrow> I \<TTurnstile>s \<C> \<Longrightarrow> I \<TTurnstile>s \<D>"
  using true_cls_iff_set_mset_eq by (metis true_clss_def)


section \<open>Abstract_Substitution_Extra\<close>

lemma (in substitution_ops) grounding_of_clss_empty[simp]: "grounding_of_clss {} = {}"
  by (simp add: grounding_of_clss_def)

lemma (in substitution_ops) grounding_of_clss_singleton[simp]:
  "grounding_of_clss {C} = grounding_of_cls C"
  by (simp add: grounding_of_clss_def)

lemma (in substitution_ops) subst_atm_of_eqI:
  "L \<cdot>l \<sigma> = L' \<cdot>l \<sigma> \<Longrightarrow> atm_of L \<cdot>a \<sigma> = atm_of L' \<cdot>a \<sigma>"
  by (cases L; cases L') (simp_all add: subst_lit_def)

lemma (in substitution_ops) subst_atm_of_eq_compI:
  "L \<cdot>l \<sigma> = - (L' \<cdot>l \<sigma>) \<Longrightarrow> atm_of L \<cdot>a \<sigma> = atm_of L' \<cdot>a \<sigma>"
  by (cases L; cases L') (simp_all add: uminus_literal_def subst_lit_def)


section \<open>First_Order_Terms Extra\<close>

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

lemma vars_cls_empty[simp]: "vars_cls {#} = {}"
  unfolding vars_cls_def by simp

lemma finite_vars_cls[simp]: "finite (vars_cls C)"
  unfolding vars_cls_def by simp

lemma vars_cls_plus_iff: "vars_cls (C + D) = vars_cls C \<union> vars_cls D"
  unfolding vars_cls_def by simp

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

definition disjoint_vars_set where
  "disjoint_vars_set N \<longleftrightarrow> (\<forall>C \<in> N. \<forall>D \<in> N. C \<noteq> D \<longrightarrow> disjoint_vars C D)"

lemma disjoint_vars_set_substetI[intro]: "disjoint_vars_set N \<Longrightarrow> M \<subseteq> N \<Longrightarrow> disjoint_vars_set M"
  unfolding disjoint_vars_set_def by auto

lemma inv_renaming_sound:
  assumes is_var_\<sigma>: "\<And>x. is_Var (\<sigma> x)" and inj_\<sigma>: "inj \<sigma>"
  shows "\<sigma> \<odot> (Var \<circ> (inv (the_Var \<circ> \<sigma>))) = Var"
proof -
  define \<sigma>' where "\<sigma>' = the_Var \<circ> \<sigma>"
  have \<sigma>_def: "\<sigma> = Var \<circ> \<sigma>'"
    unfolding \<sigma>'_def using is_var_\<sigma> by auto

  from is_var_\<sigma> inj_\<sigma> have "inj \<sigma>'"
    unfolding inj_on_def \<sigma>_def comp_def by fast
  hence "inv \<sigma>' \<circ> \<sigma>' = id"
    using inv_o_cancel[of \<sigma>'] by simp
  hence "Var \<circ> (inv \<sigma>' \<circ> \<sigma>') = Var"
    by simp
  hence "\<forall>x. (Var \<circ> (inv \<sigma>' \<circ> \<sigma>')) x = Var x"
    by metis
  hence "\<forall>x. ((Var \<circ> \<sigma>') \<odot> (Var \<circ> (inv \<sigma>'))) x = Var x"
    unfolding subst_compose_def by auto
  thus "\<sigma> \<odot> (Var \<circ> (inv \<sigma>')) = Var"
    using \<sigma>_def by auto
qed

lemma ex_inv_subst:
  assumes is_var_\<sigma>: "\<And>x. is_Var (\<sigma> x)" and inj_\<sigma>: "inj \<sigma>"
  shows "\<exists>\<tau>. \<sigma> \<odot> \<tau> = Var"
  using inv_renaming_sound[OF assms] by blast

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
    by (auto simp: is_renaming_def intro: ex_inv_subst)
qed

lemma mgu_subst_range_vars:
  assumes "Unification.mgu s t = Some \<sigma>"
  shows "range_vars \<sigma> \<subseteq> vars_term s \<union> vars_term t"
proof -
  obtain xs where *: "unify [(s, t)] [] = Some xs" and [simp]: "subst_of xs = \<sigma>"
    using assms by (simp split: option.splits)
  from unify_Some_UNIF [OF *] obtain ss
    where "compose ss = \<sigma>" and "UNIF ss {#(s, t)#} {#}" by auto
  with UNIF_range_vars_subset [of ss "{#(s, t)#}" "{#}"]
  show ?thesis using vars_mset_singleton by force
qed

lemma vars_subst_term: "vars_term (t \<cdot>a \<sigma>) \<subseteq> vars_term t - subst_domain \<sigma> \<union> range_vars \<sigma>"
proof (induction t)
  case (Var x)
  show ?case
    apply (simp add: range_vars_def subst_domain_def)
    by (smt (verit, best) SUP_upper Term.term.simps(17) empty_Diff insert_Diff_if le_supI1
        mem_Collect_eq sup_bot_left sup_ge2)
next
  case (Fun f xs)
  thus ?case by auto
qed

lemma vars_subst_lit: "vars_lit (L \<cdot>l \<sigma>) \<subseteq> vars_lit L - subst_domain \<sigma> \<union> range_vars \<sigma>"
  using vars_subst_term[of "atm_of L"] by simp

lemma vars_subst_cls: "vars_cls (C \<cdot> \<sigma>) \<subseteq> vars_cls C - subst_domain \<sigma> \<union> range_vars \<sigma>"
  unfolding vars_cls_def subst_cls_def
  apply simp
  using vars_subst_lit
  by fastforce

lemma vars_cls_plus[simp]: "vars_cls (C + D) = vars_cls C \<union> vars_cls D"
  unfolding vars_cls_def by simp

lemma vars_cls_add_mset[simp]: "vars_cls (add_mset L C) = vars_lit L \<union> vars_cls C"
  by (simp add: vars_cls_def)

lemma vars_cls_subst_mgu_subset:
  assumes mgu_L_L': "Unification.mgu (atm_of L) (atm_of L') = Some \<eta>"
  shows "vars_cls ((D + {#L#}) \<cdot> \<eta>) \<subseteq> vars_cls (D + {#L, L'#})"
proof -
  have "vars_cls ((D + {#L#}) \<cdot> \<eta>) \<subseteq> vars_cls (D + {#L#}) - subst_domain \<eta> \<union> range_vars \<eta>"
    by (rule vars_subst_cls[of "(D + {#L#})" \<eta>])
  also have "... \<subseteq> vars_cls (D + {#L#}) - (vars_lit L \<union> vars_lit L') \<union> vars_lit L \<union> vars_lit L'"
    using mgu_subst_range_vars[OF mgu_L_L'] mgu_subst_domain[OF mgu_L_L'] by blast
  also have "... \<subseteq> vars_cls (D + {#L#}) \<union> vars_lit L \<union> vars_lit L'"
    by fast
  also have "... \<subseteq> vars_cls D \<union> vars_lit L \<union> vars_lit L'"
    unfolding vars_cls_plus unfolding vars_cls_def by simp
  also have "... \<subseteq> vars_cls (D + {#L, L'#})"
    by auto
  finally show ?thesis
    by assumption
qed

lemma disjoint_vars_set_mgu:
  assumes
    disj_N_D_L_L': "disjoint_vars_set N" and
    D_L_L'_in: "D + {#L, L'#} \<in> N" and
    mgu_L_L': "Unification.mgu (atm_of L) (atm_of L') = Some \<eta>"
  shows "disjoint_vars_set (N - {D + {#L, L'#}} \<union> {(D + {#L#}) \<cdot> \<eta>})"
proof -
  have vars_D_L_\<eta>_subset: "vars_cls ((D + {#L#}) \<cdot> \<eta>) \<subseteq> vars_cls (D + {#L, L'#})"
    by (rule vars_cls_subst_mgu_subset[OF mgu_L_L'])

  have disj_D_L_\<eta>: "disjoint_vars ((D + {#L#}) \<cdot> \<eta>) C" if C_in: "C \<in> N - {D + {#L, L'#}}" for C
  proof -
    from C_in have "C \<noteq> D + {#L, L'#}" by force
    hence "disjoint_vars C (D + {#L, L'#})"
        by (meson D_L_L'_in DiffD1 \<open>C \<in> N - {D + {#L, L'#}}\<close> disj_N_D_L_L' disjoint_vars_set_def)
    thus ?thesis
      unfolding disjoint_vars_iff_inter_empty
      using vars_D_L_\<eta>_subset by blast
  qed

  show ?thesis
    unfolding disjoint_vars_set_def
  proof (intro ballI impI)
    fix C E
    assume
      C_D_in:
        "C \<in> N - {D + {#L, L'#}} \<union> {(D + {#L#}) \<cdot> \<eta>}"
        "E \<in> N - {D + {#L, L'#}} \<union> {(D + {#L#}) \<cdot> \<eta>}" and
      C_neq_E: "C \<noteq> E"

    from C_D_in[unfolded Un_iff] show "disjoint_vars C E"
    proof (elim disjE)
      assume "C \<in> N - {D + {#L, L'#}}" and "E \<in> N - {D + {#L, L'#}}"
      thus "disjoint_vars C E" by (meson C_neq_E DiffE disj_N_D_L_L' disjoint_vars_set_def)
    next
      assume "C \<in> {(D + {#L#}) \<cdot> \<eta>}" and "E \<in> {(D + {#L#}) \<cdot> \<eta>}"
      with \<open>C \<noteq> E\<close> have False by blast
      thus "disjoint_vars C E" by (rule FalseE)
    next
      assume C_in: "C \<in> N - {D + {#L, L'#}}" and E_in: "E \<in> {(D + {#L#}) \<cdot> \<eta>}"
      thus ?thesis using disj_D_L_\<eta> disjoint_vars_sym by blast
    next
      assume C_in: "C \<in> {(D + {#L#}) \<cdot> \<eta>}" and E_in: "E \<in> N - {D + {#L, L'#}}"
      thus ?thesis using disj_D_L_\<eta> by blast
    qed
  qed
qed

lemma disjoint_vars_set_minus_empty_vars:
  assumes "vars_cls C = {}"
  shows "disjoint_vars_set (N - {C}) \<longleftrightarrow> disjoint_vars_set N"
  using assms unfolding disjoint_vars_set_def disjoint_vars_iff_inter_empty by blast

lemma subst_term_eq_if_mgu:
  assumes mgu_t_u: "Unification.mgu t u = Some \<mu>"
  shows "t \<cdot>a \<mu> = u \<cdot>a \<mu>"
  using mgu_sound[OF mgu_t_u]
  unfolding Unifiers.is_imgu_def unifiers_def mem_Collect_eq
  by simp

lemma grounding_of_subst_cls_subset:
  shows "grounding_of_cls (C \<cdot> \<mu>) \<subseteq> grounding_of_cls C"
    (is "?lhs \<subseteq> ?rhs")
proof (rule subsetI)
  fix D
  assume "D \<in> ?lhs"
  then obtain \<gamma> where D_def: "D = C \<cdot> \<mu> \<cdot> \<gamma>" and gr_\<gamma>: "is_ground_subst \<gamma>"
    unfolding grounding_of_cls_def mem_Collect_eq by auto

  show "D \<in> ?rhs"
    unfolding grounding_of_cls_def mem_Collect_eq
    unfolding D_def
    using is_ground_comp_subst[OF gr_\<gamma>, of \<mu>]
    by force
qed

lemma subst_cls_idem_if_disj_vars: "subst_domain \<sigma> \<inter> vars_cls C = {} \<Longrightarrow> C \<cdot> \<sigma> = C"
  by (metis (mono_tags, lifting) Int_iff empty_iff mem_Collect_eq same_on_vars_clause
      subst_cls_id_subst subst_domain_def)

lemma subst_lit_idem_if_disj_vars: "subst_domain \<sigma> \<inter> vars_lit L = {} \<Longrightarrow> L \<cdot>l \<sigma> = L"
  by (rule subst_cls_idem_if_disj_vars[of _ "{#L#}", simplified])


subsubsection \<open>Renaming Extra\<close>

context renaming_apart begin

lemma inj_Var_renaming: "finite V \<Longrightarrow> inj (Var \<circ> renaming V)"
  using inj_compose inj_renaming by (metis inj_def term.inject(1))

lemma is_renaming_Var_comp_renaming: "finite V \<Longrightarrow> Term.is_renaming (Var \<circ> renaming V)"
  unfolding Term.is_renaming_def
  using inj_Var_renaming by (metis comp_apply inj_on_subset term.disc(1) top_greatest)

lemma vars_term_subst_term_Var_comp_renaming_disj:
  assumes fin_V: "finite V"
  shows "vars_term (t \<cdot>a (Var \<circ> renaming V)) \<inter> V = {}"
  using is_renaming_Var_comp_renaming[OF fin_V] renaming_correct[OF fin_V]
  by (induction t) auto

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

abbreviation renaming_wrt where
  "renaming_wrt N \<equiv> Var \<circ> renaming (\<Union> (vars_cls ` N))"

definition inv_renaming where
  "inv_renaming \<rho> \<equiv> Var \<circ> inv (the_Var \<circ> \<rho>)"

lemma inv_renaming_sound: "is_renaming \<rho> \<Longrightarrow> \<rho> \<odot> inv_renaming \<rho> = Var"
  unfolding is_renaming_iff inv_renaming_def
  by (auto intro: inv_renaming_sound)

lemma subst_cls_renaming_inv_renaming_idem: "is_renaming \<rho> \<Longrightarrow> C \<cdot> \<rho> \<cdot> inv_renaming \<rho> = C"
  using inv_renaming_sound
  by (metis subst_cls_comp_subst subst_cls_id_subst)

lemma is_renaming_renaming_wrt: "finite N \<Longrightarrow> is_renaming (renaming_wrt N)"
  by (simp add: inj_Var_renaming is_renaming_iff)

definition rename_clause ::
  "('f, 'a) term clause set \<Rightarrow> ('f, 'a) term clause \<Rightarrow> ('f, 'a) term clause" where
  "rename_clause N C = C \<cdot> renaming_wrt N"

lemma disjoint_vars_set_insert_rename_clause:
  assumes fin_N: "finite N" and disj_N: "disjoint_vars_set N"
  shows "disjoint_vars_set (insert (rename_clause N C) N)"
  unfolding disjoint_vars_set_def
proof (intro ballI impI)
  fix D E
  assume D_in: "D \<in> insert (rename_clause N C) N" and E_in: "E \<in> insert (rename_clause N C) N" and
    D_neq_E: "D \<noteq> E"
  from fin_N have fin_vars_N: "finite (\<Union> (vars_cls ` N))" by simp
  show "disjoint_vars D E"
    using D_in E_in D_neq_E
    apply simp
    apply safe
    unfolding rename_clause_def disjoint_vars_iff_inter_empty
    using vars_cls_subst_renaming_disj[OF fin_vars_N]
    using disj_N[unfolded disjoint_vars_set_def disjoint_vars_iff_inter_empty, rule_format]
    by auto
qed

lemma ex_inv_rename_clause: "finite N \<Longrightarrow> \<exists>\<rho>. rename_clause N C \<cdot> \<rho> = C"
  unfolding rename_clause_def
  using ex_inv_subst[OF _ inj_Var_renaming]
  by (metis comp_apply finite_UN finite_vars_cls subst_cls_comp_subst subst_cls_id_subst
      term.disc(1))

lemma grounding_of_cls_rename_clause:
  "finite N \<Longrightarrow> grounding_of_cls (rename_clause N C) = grounding_of_cls C"
  unfolding grounding_of_cls_def
  apply (rule Set.equalityI; rule subsetI)
   apply (metis (no_types) grounding_of_cls_def rename_clause_def subsetD
      subst_cls_eq_grounding_of_cls_subset_eq)
  using ex_inv_rename_clause
  by (smt (verit, ccfv_threshold) Collect_mono_iff grounding_of_cls_def mem_Collect_eq
      subst_cls_eq_grounding_of_cls_subset_eq)

end


section \<open>SCL State\<close>

type_synonym ('f, 'v) closure = "('f, 'v) term clause \<times> ('f, 'v) subst"
type_synonym ('f, 'v) closure_with_lit =
  "('f, 'v) term clause \<times> ('f, 'v) term literal \<times> ('f, 'v) subst"
type_synonym ('f, 'v) trail = "(('f, 'v) term literal \<times> ('f, 'v) closure_with_lit option) list"
type_synonym ('f, 'v) state =
  "('f, 'v) trail \<times> ('f, 'v) term clause set \<times> nat \<times> ('f, 'v) closure option"

definition clss_of_trail :: "('f, 'v) trail \<Rightarrow> ('f, 'v) term clause set" where
  "clss_of_trail \<Gamma> = (\<Union>Ln \<in> set \<Gamma>. case snd Ln of None \<Rightarrow> {} | Some (C, L, _) \<Rightarrow> {C + {#L#}})"

lemma clss_of_trail_Nil[simp]: "clss_of_trail [] = {}"
  by (simp add: clss_of_trail_def)

lemma clss_of_trail_Cons: "clss_of_trail (Ln # \<Gamma>) = clss_of_trail [Ln] \<union> clss_of_trail \<Gamma>"
  by (simp add: clss_of_trail_def)

lemma finite_clss_of_trail[simp]: "finite (clss_of_trail \<Gamma>)"
  unfolding clss_of_trail_def
proof (induction \<Gamma>)
  case Nil
  show ?case by simp
next
  case (Cons Ln \<Gamma>)
  then show ?case by (simp add: option.case_eq_if prod.case_eq_if)
qed

definition trail_propagate ::
  "('f, 'v) trail \<Rightarrow> ('f, 'v) term literal \<Rightarrow> ('f, 'v) closure_with_lit \<Rightarrow> ('f, 'v) trail" where
  "trail_propagate \<Gamma> L Cl = (L, Some Cl) # \<Gamma>"

lemma clss_of_trail_trail_propagate[simp]:
  "clss_of_trail (trail_propagate \<Gamma> (L \<cdot>l \<gamma>) (C, L, \<gamma>)) = clss_of_trail \<Gamma> \<union> {C + {#L#}}"
  unfolding trail_propagate_def clss_of_trail_def by simp

definition trail_decide :: "('f, 'v) trail \<Rightarrow> ('f, 'v) term literal \<Rightarrow> ('f, 'v) trail" where
  "trail_decide \<Gamma> L = (L, None) # \<Gamma>"

lemma clss_of_trail_trail_decide[simp]:
  "clss_of_trail (trail_decide \<Gamma> L) = clss_of_trail \<Gamma>"
  unfolding trail_decide_def clss_of_trail_def by simp

definition is_decision_lit
  :: "('f, 'v) term literal \<times> ('f, 'v) closure_with_lit option \<Rightarrow> bool" where
  "is_decision_lit Ln \<longleftrightarrow> snd Ln = None"

primrec trail_level :: "('f, 'v) trail \<Rightarrow> nat" where
  "trail_level [] = 0" |
  "trail_level (Ln # \<Gamma>) = (if is_decision_lit Ln then Suc else id) (trail_level \<Gamma>)"

primrec trail_level_lit :: "('f, 'v) trail \<Rightarrow> ('f, 'v) term literal \<Rightarrow> nat" where
  "trail_level_lit [] _ = 0" |
  "trail_level_lit (Ln # \<Gamma>) L =
    (if fst Ln = L \<or> fst Ln = -L then trail_level (Ln # \<Gamma>) else trail_level_lit \<Gamma> L)"

definition trail_level_cls :: "('f, 'v) trail \<Rightarrow> ('f, 'v) term clause \<Rightarrow> nat" where
  "trail_level_cls \<Gamma> C = Max_mset {#trail_level_lit \<Gamma> L. L \<in># C#}"

primrec trail_backtrack :: "('f, 'v) trail \<Rightarrow> nat \<Rightarrow> ('f, 'v) trail" where
  "trail_backtrack [] _ = []" |
  "trail_backtrack (Lc # \<Gamma>) level =
    (if is_decision_lit Lc \<and> trail_level (Lc # \<Gamma>) = level then
      Lc # \<Gamma>
    else
      trail_backtrack \<Gamma> level)"

lemma trail_backtrack_inv: "trail_level \<Gamma> < level \<Longrightarrow> trail_backtrack \<Gamma> level = []"
proof (induction \<Gamma>)
  case Nil
  thus ?case by simp
next
  case (Cons Lc \<Gamma>)
  thus ?case
    by (metis (mono_tags, lifting) trail_backtrack.simps(2) trail_level.simps(2) not_less_eq
        not_less_iff_gr_or_eq of_nat_eq_id of_nat_id)
qed

lemma trail_backtrack_suffix: "suffix (trail_backtrack \<Gamma> level) \<Gamma>"
proof (induction \<Gamma>)
  case Nil
  thus ?case by simp
next
  case (Cons Lc \<Gamma>)
  thus ?case
    by (cases "is_decision_lit Lc") (simp_all add: suffix_ConsI)
qed

lemma clss_of_trail_trail_decide_subset:
  "clss_of_trail (trail_backtrack \<Gamma> n) \<subseteq> clss_of_trail \<Gamma>"
  unfolding trail_decide_def clss_of_trail_def
  by (simp add: SUP_subset_mono set_mono_suffix trail_backtrack_suffix)

lemma ball_set_trail_backtrackI: "\<forall>x \<in> set \<Gamma>. P x \<Longrightarrow> \<forall>x \<in> set (trail_backtrack \<Gamma> level). P x"
  by (meson set_mono_suffix subset_eq trail_backtrack_suffix)

lemma trail_backtrack_hd:
  "trail_backtrack \<Gamma> level = [] \<or> is_decision_lit (hd (trail_backtrack \<Gamma> level))"
  by (induction \<Gamma>) simp_all

lemma trail_backtrack_level:
  "trail_level (trail_backtrack \<Gamma> level) = 0 \<or> trail_level (trail_backtrack \<Gamma> level) = level"
  by (induction \<Gamma>) simp_all

definition trail_interp :: "('f, 'v) trail \<Rightarrow> ('f, 'v) term interp" where
  "trail_interp \<Gamma> = \<Union>((\<lambda>L. case L of Pos A \<Rightarrow> {A} | Neg A \<Rightarrow> {}) ` fst ` set \<Gamma>)"

definition trail_true_lit :: "('f, 'v) trail \<Rightarrow> ('f, 'v) term literal \<Rightarrow> bool" where
  "trail_true_lit \<Gamma> L \<longleftrightarrow> trail_interp \<Gamma> \<TTurnstile>l L"

definition trail_false_lit :: "('f, 'v) trail \<Rightarrow> ('f, 'v) term literal \<Rightarrow> bool" where
  "trail_false_lit \<Gamma> L \<longleftrightarrow> trail_interp \<Gamma> \<TTurnstile>l -L"

definition trail_true_cls :: "('f, 'v) trail \<Rightarrow> ('f, 'v) term clause \<Rightarrow> bool" where
  "trail_true_cls \<Gamma> C \<longleftrightarrow> (\<exists>L \<in># C. trail_true_lit \<Gamma> L)"

definition trail_false_cls :: "('f, 'v) trail \<Rightarrow> ('f, 'v) term clause \<Rightarrow> bool" where
  "trail_false_cls \<Gamma> C \<longleftrightarrow> (\<forall>L \<in># C. trail_false_lit \<Gamma> L)"

definition trail_defined_lit :: "('f, 'v) trail \<Rightarrow> ('f, 'v) term literal \<Rightarrow> bool" where
  "trail_defined_lit \<Gamma> L \<longleftrightarrow> (trail_true_lit \<Gamma> L \<or> trail_false_lit \<Gamma> L)"

lemma ball_trail_backtrackI:
  assumes "\<forall>x \<in> set \<Gamma>. P (fst x)"
  shows "\<forall>x \<in> set (trail_backtrack \<Gamma> i). P (fst x)"
  using assms trail_backtrack_suffix[THEN set_mono_suffix]
  by blast

lemma trail_interp_Cons: "trail_interp (Ln # \<Gamma>) = trail_interp [Ln] \<union> trail_interp \<Gamma>"
  unfolding trail_interp_def by simp

lemma trail_interp_Cons': "trail_interp (Ln # \<Gamma>) = (case fst Ln of Pos A \<Rightarrow> {A} | Neg A \<Rightarrow> {}) \<union> trail_interp \<Gamma>"
  unfolding trail_interp_def by simp

lemma true_lit_thick_unionD: "(I1 \<union> I2) \<TTurnstile>l L \<Longrightarrow> I1 \<TTurnstile>l L \<or> I2 \<TTurnstile>l L"
  by auto

lemma trail_false_cls_ConsD:
  assumes tr_false: "trail_false_cls ((L, Some Cl) # \<Gamma>) C" and L_not_in: "-L \<notin># C"
  shows "trail_false_cls \<Gamma> C"
  unfolding trail_false_cls_def
proof (rule ballI)
  fix M
  assume M_in: "M \<in># C"

  from M_in L_not_in have M_neq_L: "M \<noteq> -L" by auto

  from M_in tr_false have tr_false_lit_M: "trail_false_lit ((L, Some Cl) # \<Gamma>) M"
    unfolding trail_false_cls_def by simp
  hence "trail_interp ((L, Some Cl) # \<Gamma>) \<TTurnstile>l - M"
    unfolding trail_false_lit_def by simp
  thus "trail_false_lit \<Gamma> M"
    unfolding trail_false_lit_def
    using M_neq_L
    by (cases L; cases M) (simp_all add: trail_interp_def trail_false_lit_def)
qed


section \<open>SCL Calculus\<close>

locale scl = renaming_apart renaming_vars
  for renaming_vars :: "'v set \<Rightarrow> 'v \<Rightarrow> 'v"
begin

inductive scl :: "('f, 'v) term clause set \<Rightarrow> ('f, 'v) state => ('f, 'v) state \<Rightarrow> bool" for N where
  propagate: "C \<in> N \<union> U \<Longrightarrow> C' = rename_clause (N \<union> U \<union> clss_of_trail \<Gamma>) C \<Longrightarrow> C' = C'' + {#L#} \<Longrightarrow>
    is_ground_cls ((C'' + {#L#}) \<cdot> \<sigma>) \<Longrightarrow> trail_false_cls \<Gamma> (C'' \<cdot> \<sigma>) \<Longrightarrow>
    \<not> trail_defined_lit \<Gamma> (L \<cdot>l \<sigma>) \<Longrightarrow>
    scl N (\<Gamma>, U, k, None) (trail_propagate \<Gamma> (L \<cdot>l \<sigma>) (C'', L, \<sigma>), U, k, None)" |

  decide: "is_ground_lit L \<Longrightarrow> \<not> trail_defined_lit \<Gamma> L \<Longrightarrow>
    scl N (\<Gamma>, U, k, None) (trail_decide \<Gamma> L, U, Suc k, None)" |

  conflict: "D \<in> N \<union> U \<Longrightarrow> D' = rename_clause (N \<union> U \<union> clss_of_trail \<Gamma>) D \<Longrightarrow>
    is_ground_cls (D' \<cdot> \<sigma>) \<Longrightarrow> trail_false_cls \<Gamma> (D' \<cdot> \<sigma>) \<Longrightarrow>
    scl N (\<Gamma>, U, k, None) (\<Gamma>, U, Suc k, Some (D', \<sigma>))" |

  skip: "-(L \<cdot>l \<delta>) \<notin># D \<cdot> \<sigma> \<Longrightarrow>
    scl N (trail_propagate \<Gamma> (L \<cdot>l \<delta>) (C, L, \<delta>), U, k, Some (D, \<sigma>)) (\<Gamma>, U, k, Some (D, \<sigma>))" |

  factorize: "L \<cdot>l \<sigma> = L' \<cdot>l \<sigma> \<Longrightarrow> Unification.mgu (atm_of L) (atm_of L') = Some \<mu> \<Longrightarrow>
    scl N (\<Gamma>, U, k, Some (D + {#L,L'#}, \<sigma>)) (\<Gamma>, U, k, Some ((D + {#L#}) \<cdot> \<mu>, \<sigma>))" |

  resolve: "\<Gamma> = trail_propagate \<Gamma>' (L \<cdot>l \<delta>) (C, L, \<delta>) \<Longrightarrow> trail_level_cls \<Gamma> (D \<cdot> \<sigma>) = k \<Longrightarrow>
    \<rho> = renaming_wrt (N \<union> U \<union> clss_of_trail \<Gamma> \<union> {D + {#L'#}}) \<Longrightarrow>
    (L \<cdot>l \<delta>) = -(L' \<cdot>l \<sigma>) \<Longrightarrow> Unification.mgu (atm_of L) (atm_of L') = Some \<mu> \<Longrightarrow>
    scl N (\<Gamma>, U, k, Some (D + {#L'#}, \<sigma>)) (\<Gamma>, U, k, Some ((D + C) \<cdot> \<mu> \<cdot> \<rho>, inv_renaming \<rho> \<odot> \<sigma> \<odot> \<delta>))" |

  backtrack: "trail_level_lit \<Gamma> (L \<cdot>l \<sigma>) = k \<Longrightarrow> trail_level_cls \<Gamma> (D \<cdot> \<sigma>) = i \<Longrightarrow>
    scl N (\<Gamma>, U, k, Some (D + {#L#}, \<sigma>)) (trail_backtrack \<Gamma> i, U \<union> {D + {#L#}}, k, None)"

text \<open>Note that, in contrast to Fiori and Weidenbach (CADE 2019), the set of clauses @{term N} is a
parameter of the relation instead of being repeated twice in the state. This is to highlight the
fact that it is a constant.\<close>


section \<open>Soundness\<close>

inductive sound_trail for N U where
  Nil[simp]: "sound_trail N U []" |
  Cons: "\<not> trail_defined_lit \<Gamma> L \<Longrightarrow>
    (case u of
      None \<Rightarrow> True |
      Some (C, L', \<gamma>) \<Rightarrow> L = L' \<cdot>l \<gamma> \<and> is_ground_cls ((C + {#L'#}) \<cdot> \<gamma>) \<and> trail_false_cls \<Gamma> (C \<cdot> \<gamma>) \<and>
        (\<exists>D \<in> N \<union> U. \<exists>\<rho>. is_renaming \<rho> \<and> C + {#L'#} = D \<cdot> \<rho>)) \<Longrightarrow>
    sound_trail N U \<Gamma> \<Longrightarrow> sound_trail N U ((L, u) # \<Gamma>)"

lemma sound_trail_supersetI: "sound_trail N U \<Gamma> \<Longrightarrow> N \<subseteq> NN \<Longrightarrow> U \<subseteq> UU \<Longrightarrow> sound_trail NN UU \<Gamma>"
proof (induction \<Gamma> rule: sound_trail.induct)
  case Nil
  thus ?case by simp
next
  case (Cons \<Gamma> L u)
  show ?case
  proof (rule sound_trail.Cons)
    from Cons.hyps show "\<not> trail_defined_lit \<Gamma> L" by simp
  next
    from Cons.prems show "sound_trail NN UU \<Gamma>"
      by (rule Cons.IH)
  next
    show
      "case u of
        None \<Rightarrow> True
      | Some (C, L', \<gamma>) \<Rightarrow>
        L = L' \<cdot>l \<gamma> \<and> is_ground_cls ((C + {#L'#}) \<cdot> \<gamma>) \<and> trail_false_cls \<Gamma> (C \<cdot> \<gamma>) \<and>
        (\<exists>D \<in> NN \<union> UU. \<exists>\<rho>. is_renaming \<rho> \<and> C + {#L'#} = D \<cdot> \<rho>)"
    proof (cases u)
      case None
      thus ?thesis by simp
    next
      case (Some Cl)
      from Cons.hyps Some obtain C L' \<gamma> where
        Cl_def: "Cl = (C, L', \<gamma>)" and
        L_def: "L = L' \<cdot>l \<gamma>" and
        gr_L_L'_\<gamma>: "is_ground_cls ((C + {#L'#}) \<cdot> \<gamma>)" and
        tr_false: "trail_false_cls \<Gamma> (C \<cdot> \<gamma>)" and
        C_renaing: "\<exists>D \<in> N \<union> U. \<exists>\<rho>. is_renaming \<rho> \<and> C + {#L'#} = D \<cdot> \<rho>"
        by fastforce

      show ?thesis
        unfolding Some Cl_def option.case prod.case
      proof (intro conjI)
        show "L = L' \<cdot>l \<gamma>" by (rule L_def)
      next
        show "is_ground_cls ((C + {#L'#}) \<cdot> \<gamma>)" by (rule gr_L_L'_\<gamma>)
      next
        show "trail_false_cls \<Gamma> (C \<cdot> \<gamma>)" by (rule tr_false)
      next
        show "\<exists>D\<in>NN \<union> UU. \<exists>\<rho>. is_renaming \<rho> \<and> C + {#L'#} = D \<cdot> \<rho>"
          using Cons.prems C_renaing by fast
      qed
    qed
  qed
qed

lemma sound_trail_backtrackI: "sound_trail N U \<Gamma> \<Longrightarrow> sound_trail N U (trail_backtrack \<Gamma> level)"
  by (induction \<Gamma> rule: sound_trail.induct) (auto intro: sound_trail.intros)

lemma sound_trail_propagate:
  assumes
    sound_\<Gamma>: "sound_trail N U \<Gamma>" and
    not_tr_def_\<Gamma>_L_\<sigma>: "\<not> trail_defined_lit \<Gamma> (L \<cdot>l \<sigma>)" and
    gr_C_L_\<sigma>: "is_ground_cls ((C + {#L#}) \<cdot> \<sigma>)" and
    tr_false_\<Gamma>_C_\<sigma>: "trail_false_cls \<Gamma> (C \<cdot> \<sigma>)" and
    ex_renaming: "\<exists>D\<in>N \<union> U. \<exists>\<rho>. is_renaming \<rho> \<and> C + {#L#} = D \<cdot> \<rho>"
  shows "sound_trail N U (trail_propagate \<Gamma> (L \<cdot>l \<sigma>) (C, L, \<sigma>))"
  unfolding trail_propagate_def
proof (rule sound_trail.Cons; (unfold option.case prod.case)?)
  show "\<not> trail_defined_lit \<Gamma> (L \<cdot>l \<sigma>)"
    by (rule not_tr_def_\<Gamma>_L_\<sigma>)
next
  show "sound_trail N U \<Gamma>"
    by (rule sound_\<Gamma>)
next
  show "L \<cdot>l \<sigma> = L \<cdot>l \<sigma> \<and> is_ground_cls ((C + {#L#}) \<cdot> \<sigma>) \<and> trail_false_cls \<Gamma> (C \<cdot> \<sigma>) \<and>
    (\<exists>D\<in>N \<union> U. \<exists>\<rho>. is_renaming \<rho> \<and> C + {#L#} = D \<cdot> \<rho>)"
    using gr_C_L_\<sigma> tr_false_\<Gamma>_C_\<sigma> ex_renaming by auto
qed

lemma sound_trail_decide:
  "sound_trail N U \<Gamma> \<Longrightarrow> \<not> trail_defined_lit \<Gamma> L \<Longrightarrow> sound_trail N U (trail_decide \<Gamma> L)"
  unfolding trail_decide_def
  by (auto intro: sound_trail.Cons)

text \<open>In contrast to Fiori and Weidenbach (CADE 2019), I lifting the entailments @{term \<open>N \<TTurnstile>e U\<close>}
and @{term \<open>N \<TTurnstile>e {C}\<close>} from ground to non-ground with a ground substitution @{term \<eta>};
the conjunction becomes an implication.\<close>

abbreviation entails_\<G> (infix "\<TTurnstile>\<G>e" 50) where
  "entails_\<G> N U \<equiv> grounding_of_clss N \<TTurnstile>e grounding_of_clss U"

definition sound_state :: "('f, 'v) Term.term clause set \<Rightarrow> ('f, 'v) state \<Rightarrow> bool" where
  "sound_state N S \<longleftrightarrow> (\<exists>\<Gamma> U k u.
    S = (\<Gamma>, U, k, u) \<and>
    finite N \<and> finite U \<and>
    disjoint_vars_set (N \<union> U \<union> clss_of_trail \<Gamma>) \<and>
    (case u of None \<Rightarrow> True | Some (C, _) \<Rightarrow> \<forall>D \<in> N \<union> U  \<union> clss_of_trail \<Gamma>. disjoint_vars C D) \<and>
    (\<forall>L \<in> fst ` set \<Gamma>. is_ground_lit L) \<and>
    sound_trail N U \<Gamma> \<and>
    N \<TTurnstile>\<G>e U \<and>
    (case u of None \<Rightarrow> True
    | Some (C, \<gamma>) \<Rightarrow> is_ground_cls (C \<cdot> \<gamma>) \<and> trail_false_cls \<Gamma> (C \<cdot> \<gamma>) \<and> N \<TTurnstile>\<G>e {C}))"

abbreviation initial_state :: "('f, 'v) state" where
  "initial_state \<equiv> ([], {}, 0, None)"

lemma sound_initial_state[simp]: "finite N \<Longrightarrow> disjoint_vars_set N \<Longrightarrow> sound_state N initial_state"
  by (simp add: sound_state_def)

lemma ball_trail_propagate_is_ground_lit:
  assumes "\<forall>x\<in>set \<Gamma>. is_ground_lit (fst x)" and "is_ground_lit (L \<cdot>l \<sigma>)"
  shows "\<forall>x\<in>set (trail_propagate \<Gamma> (L \<cdot>l \<sigma>) (C, L, \<sigma>)). is_ground_lit (fst x)"
  unfolding trail_propagate_def
  using assms
  by simp

lemma ball_trail_decide_is_ground_lit:
  assumes "\<forall>x\<in>set \<Gamma>. is_ground_lit (fst x)" and "is_ground_lit L"
  shows "\<forall>x\<in>set (trail_decide \<Gamma> L). is_ground_lit (fst x)"
  unfolding trail_decide_def
  using assms
  by simp

lemma entails_clss_insert: "N \<TTurnstile>e insert C U \<longleftrightarrow> N \<TTurnstile>e {C} \<and> N \<TTurnstile>e U"
  by auto

lemma subst_clss_insert[simp]: "insert C U \<cdot>cs \<eta> = insert (C \<cdot> \<eta>) (U \<cdot>cs \<eta>)"
  by (simp add: subst_clss_def)

lemma ball_singleton: "(\<forall>x \<in> {y}. P x) \<longleftrightarrow> P y" by simp

lemma valid_grounding_of_renaming:
  assumes "is_renaming \<rho>"
  shows "I \<TTurnstile>s grounding_of_cls (C \<cdot> \<rho>) \<longleftrightarrow> I \<TTurnstile>s grounding_of_cls C"
proof -
  have "grounding_of_cls (C \<cdot> \<rho>) = grounding_of_cls C" (is "?lhs = ?rhs")
    by (metis (no_types, lifting) assms subset_antisym subst_cls_comp_subst
        subst_cls_eq_grounding_of_cls_subset_eq subst_cls_id_subst substitution_ops.is_renaming_def)
  thus ?thesis
    by simp
qed

theorem scl_sound_state: "scl N S S' \<Longrightarrow> sound_state N S \<Longrightarrow> sound_state N S'"
proof (induction S S' rule: scl.induct)
  case (propagate C U C' \<Gamma> C'' L \<gamma> k)
  from propagate.prems have
    fin: "finite N" "finite U" and
    disj_N_U_\<Gamma>: "disjoint_vars_set (N \<union> U \<union> clss_of_trail \<Gamma>)" and
    ball_\<Gamma>_ground: "\<forall>L \<in> set \<Gamma>. is_ground_lit (fst L)" and
    sound_\<Gamma>: "sound_trail N U \<Gamma>" and
    N_entails_U: "N \<TTurnstile>\<G>e U"
    unfolding sound_state_def by auto

  from propagate.hyps have
    C_in: "C \<in> N \<union> U" and
    rename_C: "C'' + {#L#} = rename_clause (N \<union> U \<union> clss_of_trail \<Gamma>) C" and
    gr_C''_L_\<gamma>: "is_ground_cls ((C'' + {#L#}) \<cdot> \<gamma>)"
    by simp_all

  have "disjoint_vars_set (N \<union> U \<union> clss_of_trail (trail_propagate \<Gamma> (L \<cdot>l \<gamma>) (C'', L, \<gamma>)))"
    using fin disj_N_U_\<Gamma> C_in rename_C
    by (auto intro: disjoint_vars_set_insert_rename_clause)

  moreover have "\<forall>x\<in>set (trail_propagate \<Gamma> (L \<cdot>l \<gamma>) (C'', L, \<gamma>)). is_ground_lit (fst x)"
  proof (rule ball_trail_propagate_is_ground_lit)
    show "\<forall>x\<in>set \<Gamma>. is_ground_lit (fst x)"
      by (rule ball_\<Gamma>_ground)
  next
    show "is_ground_lit (L \<cdot>l \<gamma>)"
      by (rule gr_C''_L_\<gamma>[unfolded is_ground_cls_def, rule_format]) simp
  qed

  moreover have "sound_trail N U (trail_propagate \<Gamma> (L \<cdot>l \<gamma>) (C'', L, \<gamma>))"
  proof (rule sound_trail_propagate)
    show "\<exists>D\<in>N \<union> U. \<exists>\<rho>. Simple_Clause_Learning.is_renaming \<rho> \<and> C'' + {#L#} = D \<cdot> \<rho>"
      unfolding rename_C unfolding rename_clause_def
      using fin C_in by (metis finite_UnI finite_clss_of_trail is_renaming_renaming_wrt)
  qed (use propagate.hyps sound_\<Gamma> in simp_all)

  ultimately show ?case
    unfolding sound_state_def
    using fin N_entails_U
    by simp
next
  case (decide L \<Gamma> U k)
  from decide.prems have
    fin: "finite N" "finite U" and
    disj_N_U_\<Gamma>: "disjoint_vars_set (N \<union> U \<union> clss_of_trail \<Gamma>)" and
    ball_\<Gamma>_ground: "\<forall>L \<in> set \<Gamma>. is_ground_lit (fst L)" and
    sound_\<Gamma>: "sound_trail N U \<Gamma>" and
    N_entails_U: "N \<TTurnstile>\<G>e U"
    unfolding sound_state_def by auto
  with decide.hyps show ?case
    unfolding sound_state_def
    using ball_trail_decide_is_ground_lit[of \<Gamma> L]
    by (auto intro: sound_trail_decide)
next
  case (conflict D U D' \<Gamma> \<sigma> k)
  from conflict.prems have
    fin_N: "finite N" and
    fin_U: "finite U" and
    disj_N_U: "disjoint_vars_set (N \<union> U \<union> clss_of_trail \<Gamma>)" and
    ball_\<Gamma>_ground: "\<forall>L \<in> set \<Gamma>. is_ground_lit (fst L)" and
    sound_\<Gamma>: "sound_trail N U \<Gamma>" and
    N_entails_U: "N \<TTurnstile>\<G>e U"
    unfolding sound_state_def by auto

  from conflict.hyps have D_in: "D \<in> N \<union> U" by simp
  from conflict.hyps have D'_def: "D' = rename_clause (N \<union> U \<union> clss_of_trail \<Gamma>) D" by simp
  from conflict.hyps have tr_false_D': "trail_false_cls \<Gamma> (D' \<cdot> \<sigma>)" by simp

  from fin_N fin_U have fin_N_U: "finite (N \<union> U)" by simp
  with disj_N_U D'_def have disj_N_U_D': "\<forall>C \<in> N \<union> U \<union> clss_of_trail \<Gamma>. disjoint_vars D' C"
    using disjoint_vars_set_insert_rename_clause
    by (smt (verit) UN_I Un_iff disjoint_iff disjoint_vars_iff_inter_empty finite_UN finite_UnI
        finite_clss_of_trail finite_vars_cls rename_clause_def vars_cls_subst_renaming_disj)

  from conflict.hyps have "is_ground_cls (D' \<cdot> \<sigma>)" by simp

  moreover have N_entails_D': "N \<TTurnstile>\<G>e {D'}"
  proof (intro allI impI)
    fix I
    assume valid_N: "I \<TTurnstile>s grounding_of_clss N"
    moreover have "grounding_of_cls D' = grounding_of_cls D"
      unfolding D'_def
      using grounding_of_cls_rename_clause fin_N_U
      by (metis finite_UnI finite_clss_of_trail)
    ultimately show "I \<TTurnstile>s grounding_of_clss {D'}"
      using D_in
      by (metis (mono_tags, lifting) N_entails_U UN_I UnE grounding_of_clss_def
          grounding_of_clss_singleton true_clss_def)
  qed

  ultimately show ?case
    unfolding sound_state_def
    using fin_N fin_U disj_N_U disj_N_U_D' ball_\<Gamma>_ground sound_\<Gamma> N_entails_U tr_false_D' N_entails_D'
    by simp
next
  case (skip L \<delta> D \<sigma> \<Gamma> C U k)
  from skip show ?case
    unfolding sound_state_def
    by (auto simp: trail_propagate_def clss_of_trail_Cons[of _ \<Gamma>]
        elim: sound_trail.cases dest!: trail_false_cls_ConsD)
next
  case (factorize L \<sigma> L' \<mu> \<Gamma> U k D)
  from factorize.prems have
    fin_N: "finite N" and fin_U: "finite U" and
    disj_N_U: "disjoint_vars_set (N \<union> U \<union> clss_of_trail \<Gamma>)" and
    disj_N_U_D_L_L': "\<forall>C \<in> N \<union> U \<union> clss_of_trail \<Gamma>. disjoint_vars (D + {#L, L'#}) C" and
    ball_\<Gamma>_ground:"\<forall>L \<in> set \<Gamma>. is_ground_lit (fst L)" and
    sound_\<Gamma>: "sound_trail N U \<Gamma>" and
    N_entails_U: "N \<TTurnstile>\<G>e U" and
    gr_D_L_L'_\<sigma>: "is_ground_cls ((D + {#L, L'#}) \<cdot> \<sigma>)" and
    tr_false_cls: "trail_false_cls \<Gamma> ((D + {#L, L'#}) \<cdot> \<sigma>)" and
    N_entails_D_L_L': "N \<TTurnstile>\<G>e {D + {#L, L'#}}"
    unfolding sound_state_def by simp_all

  from factorize.hyps have mgu_L_L': "Unification.mgu (atm_of L) (atm_of L') = Some \<mu>" by simp
  from factorize.hyps have L_eq_L'_\<sigma>: "L \<cdot>l \<sigma> = L' \<cdot>l \<sigma>" by simp

  hence \<sigma>_unif: "\<sigma> \<in> Unifiers.unifiers {(atm_of L, atm_of L')}"
    unfolding Unifiers.unifiers_def by (auto intro: subst_atm_of_eqI)

  have is_imgu_\<mu>_full:
    "Unifiers.is_imgu \<mu> (insert (atm_of L, atm_of L') ((\<lambda>t. (t, t)) ` atm_of ` set_mset D))"
    sorry

  have \<sigma>_unif_full:
    "\<sigma> \<in> unifiers (insert (atm_of L, atm_of L') ((\<lambda>t. (t, t)) ` atm_of ` set_mset D))"
    unfolding unifiers_def mem_Collect_eq
    using L_eq_L'_\<sigma> by (auto intro: subst_atm_of_eqI)

  from mgu_L_L' have L_eq_L'_\<mu>: "L \<cdot>l \<mu> = L' \<cdot>l \<mu>"
    using subst_term_eq_if_mgu
    by (metis (mono_tags, lifting) L_eq_L'_\<sigma> atm_of_subst_lit literal.expand subst_lit_is_neg)

  have "disjoint_vars ((D + {#L#}) \<cdot> \<mu>) C" if C_in: "C \<in> N \<union> U \<union> clss_of_trail \<Gamma>" for C
    using disj_N_U_D_L_L'[rule_format, OF C_in]
    unfolding _disjoint_vars_iff_inter_empty
    using vars_cls_subst_mgu_subset[OF mgu_L_L'] 
    by fast

  moreover have "is_ground_cls ((D + {#L#}) \<cdot> \<mu> \<cdot> \<sigma>)"
    using gr_D_L_L'_\<sigma>
    by (metis (no_types, lifting) Unifiers.is_imgu_def \<sigma>_unif_full add_mset_add_single
        is_ground_cls_union is_imgu_\<mu>_full subst_cls_comp_subst subst_cls_union)

  moreover have "trail_false_cls \<Gamma> ((D + {#L#}) \<cdot> \<mu> \<cdot> \<sigma>)"
    unfolding trail_false_cls_def
  proof (rule ballI)
    fix K
    assume "K \<in># (D + {#L#}) \<cdot> \<mu> \<cdot> \<sigma>"
    hence "K \<in># D \<cdot> \<mu> \<cdot> \<sigma> \<or> K = L  \<cdot>l \<mu> \<cdot>l \<sigma>" by force
    thus "trail_false_lit \<Gamma> K"
    proof (elim disjE)
      show "K \<in># D \<cdot> \<mu> \<cdot> \<sigma> \<Longrightarrow> trail_false_lit \<Gamma> K"
        apply (rule tr_false_cls[unfolded trail_false_cls_def, rule_format])
        using is_imgu_\<mu>_full \<sigma>_unif_full
        by (metis (no_types, lifting) Unifiers.is_imgu_def subst_cls_comp_subst subst_cls_union
            union_iff)
    next
      have "L \<cdot>l \<mu> \<cdot>l \<sigma> = L \<cdot>l \<sigma>"
        using mgu_sound[OF mgu_L_L'] \<sigma>_unif
        unfolding Unifiers.is_imgu_def
        by (metis subst_lit_comp_subst)
      thus "K = L \<cdot>l \<mu> \<cdot>l \<sigma> \<Longrightarrow> trail_false_lit \<Gamma> K"
        by (auto intro: tr_false_cls[unfolded trail_false_cls_def, rule_format])
    qed
  qed

  moreover have "N \<TTurnstile>\<G>e {(D + {#L#}) \<cdot> \<mu>}"
  proof (rule entails_trans)
    show "N \<TTurnstile>\<G>e {D + {#L, L'#}}"
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

  ultimately show ?case
    unfolding sound_state_def
    using fin_N fin_U disj_N_U ball_\<Gamma>_ground sound_\<Gamma> N_entails_U
    by simp
next
  case (resolve \<Gamma> \<Gamma>' L \<delta> C D \<sigma> k \<rho> U L' \<mu>)
  from resolve.prems have
    fin: "finite N" "finite U" and
    disj_N_U: "disjoint_vars_set (N \<union> U \<union> clss_of_trail \<Gamma>)" and
    disj_N_U_\<Gamma>_D_L_L': "\<forall>C \<in> N \<union> U \<union> clss_of_trail \<Gamma>. disjoint_vars (D + {#L'#}) C" and
    ball_\<Gamma>_ground:"\<forall>L \<in> set \<Gamma>. is_ground_lit (fst L)" and
    sound_\<Gamma>: "sound_trail N U \<Gamma>" and
    N_entails_U: "N \<TTurnstile>\<G>e U" and
    gr_D_L'_\<sigma>: "is_ground_cls ((D + {#L'#}) \<cdot> \<sigma>)" and
    tr_false_cls: "trail_false_cls \<Gamma> ((D + {#L'#}) \<cdot> \<sigma>)" and
    N_entails_D_L': "N \<TTurnstile>\<G>e {D + {#L'#}}"
    unfolding sound_state_def by simp_all

  from resolve.hyps have L_eq_comp_L': "L \<cdot>l \<delta> = - (L' \<cdot>l \<sigma>)" by simp
  from resolve.hyps have mgu_L_\<rho>_L': "Unification.mgu (atm_of L) (atm_of L') = Some \<mu>" by simp
  from resolve.hyps have \<Gamma>_def: "\<Gamma> = trail_propagate \<Gamma>' (L \<cdot>l \<delta>) (C, L, \<delta>)" by simp
  from resolve.hyps fin have is_renaming_\<rho>: "is_renaming \<rho>"
    using is_renaming_renaming_wrt
    by (metis finite.emptyI finite.insertI finite_UnI finite_clss_of_trail)

  from sound_\<Gamma> \<Gamma>_def have tr_undef_\<Gamma>'_L_\<delta>: "\<not> trail_defined_lit \<Gamma>' (L \<cdot>l \<delta>)"
    by (auto simp: trail_propagate_def elim: sound_trail.cases)

  have
    dom_\<sigma>: "subst_domain \<sigma> \<subseteq> vars_cls (D + {#L'#})" and
    dom_\<delta>: "subst_domain \<delta> \<subseteq> vars_cls (C + {#L#})"
    sorry

  have vars_D_L'_vars_C_L_disj: "vars_cls (D + {#L'#}) \<inter> vars_cls (C + {#L#}) = {}"
    apply(rule disj_N_U_\<Gamma>_D_L_L'[unfolded disjoint_vars_iff_inter_empty,
          rule_format, of "C + {#L#}"])
    by (simp add: \<Gamma>_def)

  from sound_\<Gamma> have
    gr_C_L_\<delta>: "is_ground_cls ((C + {#L#}) \<cdot> \<delta>)" and
    tr_false_cls_C: "trail_false_cls \<Gamma>' (C \<cdot> \<delta>)" and
    ex_renamed_in_N_U: "\<exists>CC \<in> N \<union> U. \<exists>\<rho>. is_renaming \<rho> \<and> C + {#L#} = CC \<cdot> \<rho>"
    unfolding \<Gamma>_def trail_propagate_def
    by (auto elim: sound_trail.cases)

  have is_imgu_\<mu>_full:
    "Unifiers.is_imgu \<mu> (insert (atm_of L, atm_of L') ((\<lambda>t. (t, t)) ` atm_of ` set_mset (C + D)))"
    sorry

  from L_eq_comp_L' have "L \<cdot>l \<sigma> \<cdot>l \<delta> = - (L' \<cdot>l \<sigma> \<cdot>l \<delta>)"
    using dom_\<sigma> dom_\<delta>
    using subst_lit_idem_if_disj_vars[of \<sigma> L]
    by (smt (verit) Un_Int_eq(4) add_mset_eq_single gr_D_L'_\<sigma> inf.commute inf.orderE inf_bot_right
        inf_sup_aci(2) is_ground_cls_union is_ground_subst_cls subst_cls_single subst_cls_union
        sup_bot.right_neutral vars_D_L'_vars_C_L_disj vars_cls_add_mset vars_cls_empty
        vars_cls_plus_iff)
    
  hence \<sigma>_\<delta>_in_unif:"\<sigma> \<odot> \<delta> \<in> unifiers
    (insert (atm_of L, atm_of L') ((\<lambda>t. (t, t)) ` atm_of ` set_mset (C + D)))"
    unfolding unifiers_def mem_Collect_eq
    by (auto intro: subst_atm_of_eq_compI[of _ "\<sigma> \<odot> \<delta>", simplified])

  have "disjoint_vars ((D + C) \<cdot> \<mu> \<cdot> \<rho>) E" if E_in: "E \<in> N \<union> U \<union> clss_of_trail \<Gamma>" for E
  proof - 
    have
      inter_D_E: "vars_cls D \<inter> vars_cls E = {}" and
      inter_L'_E: "vars_cls {#L'#} \<inter> vars_cls E = {}"
        using disj_N_U_\<Gamma>_D_L_L'[rule_format, OF E_in]
        unfolding disjoint_vars_plus_iff
        unfolding disjoint_vars_iff_inter_empty
        by simp_all

    have inter_L_\<rho>_E: "vars_term (atm_of L \<cdot>a \<rho>) \<inter> vars_cls E = {}"
        by (smt (verit, ccfv_threshold) E_in UN_I UN_Un Un_empty disjoint_iff fin finite.intros
            finite_UN finite_UnI finite_clss_of_trail finite_vars_cls inf_sup_distrib1
            vars_lit_subst_renaming_disj resolve.hyps(3) atm_of_subst_lit)

    show ?thesis
      unfolding subst_cls_union disjoint_vars_plus_iff
    proof (rule conjI)
      show "disjoint_vars (D \<cdot> \<mu> \<cdot> \<rho>) E"
        unfolding disjoint_vars_iff_inter_empty
        by (smt (verit) E_in UN_I Un_iff disjoint_iff fin finite.intros finite_UN finite_UnI
            finite_clss_of_trail finite_vars_cls vars_cls_subst_renaming_disj resolve.hyps(3))
    next
      show "disjoint_vars (C \<cdot> \<mu> \<cdot> \<rho>) E"
        unfolding disjoint_vars_iff_inter_empty
        by (smt (verit) E_in UN_I Un_iff disjoint_iff fin finite.intros finite_UN finite_UnI
            finite_clss_of_trail finite_vars_cls vars_cls_subst_renaming_disj resolve.hyps(3))
    qed
  qed

  moreover have "is_ground_cls (D \<cdot> \<mu> \<cdot> \<rho> \<cdot> inv_renaming \<rho> \<cdot> \<sigma> \<cdot> \<delta> + C \<cdot> \<mu> \<cdot> \<rho> \<cdot> inv_renaming \<rho> \<cdot> \<sigma> \<cdot> \<delta>)"
    unfolding subst_cls_renaming_inv_renaming_idem[OF is_renaming_\<rho>] is_ground_cls_union
  proof (rule conjI)
    from gr_D_L'_\<sigma> have "is_ground_cls ((D + {#L'#}) \<cdot> \<sigma> \<cdot> \<delta>)"
      by (metis is_ground_subst_cls)
    hence "is_ground_cls ((D + {#L'#}) \<cdot> \<mu> \<cdot> \<sigma> \<cdot> \<delta>)"
      by (metis (no_types, lifting) Unifiers.is_imgu_def \<sigma>_\<delta>_in_unif is_imgu_\<mu>_full
          subst_cls_comp_subst)
    thus "is_ground_cls (D \<cdot> \<mu> \<cdot> \<sigma> \<cdot> \<delta>)"
      by (metis is_ground_cls_union subst_cls_union)
  next
    from gr_C_L_\<delta> have "is_ground_cls ((C + {#L#}) \<cdot> \<sigma> \<cdot> \<delta>)"
      using subst_cls_idem_if_disj_vars[of \<sigma> C]
      using dom_\<sigma> vars_D_L'_vars_C_L_disj
      by (smt (verit, best) Int_assoc inf.orderE inf_bot_right subst_cls_idem_if_disj_vars)
    hence "is_ground_cls ((C + {#L#}) \<cdot> \<mu> \<cdot> \<sigma> \<cdot> \<delta>)"
      by (metis (no_types, lifting) Unifiers.is_imgu_def \<sigma>_\<delta>_in_unif is_imgu_\<mu>_full
          subst_cls_comp_subst)
    thus "is_ground_cls (C \<cdot> \<mu> \<cdot> \<sigma> \<cdot> \<delta>)"
      by (metis is_ground_cls_union subst_cls_union)
  qed

  moreover have "trail_false_cls \<Gamma>
    (D \<cdot> \<mu> \<cdot> \<rho> \<cdot> inv_renaming \<rho> \<cdot> \<sigma> \<cdot> \<delta> + C \<cdot> \<mu> \<cdot> \<rho> \<cdot> inv_renaming \<rho> \<cdot> \<sigma> \<cdot> \<delta>)"
    unfolding subst_cls_renaming_inv_renaming_idem[OF is_renaming_\<rho>]
    unfolding trail_false_cls_def
  proof (rule ballI)
    fix K
    assume "K \<in># D \<cdot> \<mu> \<cdot> \<sigma> \<cdot> \<delta> + C \<cdot> \<mu> \<cdot> \<sigma> \<cdot> \<delta>"
    thus "trail_false_lit \<Gamma> K"
      unfolding union_iff
    proof (elim disjE)
      assume K_in: "K \<in># D \<cdot> \<mu> \<cdot> \<sigma> \<cdot> \<delta>"
      hence "K \<in># D \<cdot> \<sigma> \<cdot> \<delta>"
        using is_imgu_\<mu>_full[unfolded Unifiers.is_imgu_def, THEN conjunct2, rule_format,
            OF \<sigma>_\<delta>_in_unif]
        by (metis subst_cls_comp_subst)
      hence "K \<in># D \<cdot> \<sigma>"
        using gr_D_L'_\<sigma> is_ground_subst_cls by (metis is_ground_cls_union subst_cls_union)
      then show ?thesis
        by (auto intro!: tr_false_cls[unfolded trail_false_cls_def, rule_format])
    next
      have tr_false_cls_C: "trail_false_cls \<Gamma>' (C \<cdot> \<delta>)"
        using sound_\<Gamma>
        unfolding sound_trail.simps[of _ _ \<Gamma>]
        unfolding \<Gamma>_def trail_propagate_def
        by simp

      assume "K \<in># C \<cdot> \<mu> \<cdot> \<sigma> \<cdot> \<delta>"
      hence "K \<in># C \<cdot> \<sigma> \<cdot> \<delta>"
        using is_imgu_\<mu>_full[unfolded Unifiers.is_imgu_def, THEN conjunct2, rule_format,
            OF \<sigma>_\<delta>_in_unif]
        by (metis subst_cls_comp_subst)
      have "K \<in># C \<cdot> \<delta>"
      proof -
        have "subst_domain \<sigma> \<inter> vars_cls C = {}"
          using dom_\<sigma> vars_D_L'_vars_C_L_disj
          by auto
        thus ?thesis
          using \<open>K \<in># C \<cdot> \<sigma> \<cdot> \<delta>\<close> subst_cls_idem_if_disj_vars[of \<sigma> C] by simp
      qed
      hence tr_false_\<Gamma>'_K:"trail_false_lit \<Gamma>' K"
        using tr_false_cls_C[unfolded trail_false_cls_def, rule_format, of K] by simp
      show ?thesis
      proof (cases "L \<cdot>l \<delta>")
        case L_Pos: (Pos t)
        show ?thesis
        proof (cases K)
          case K_Pos: (Pos u)
          then show ?thesis
            using L_Pos tr_false_\<Gamma>'_K tr_undef_\<Gamma>'_L_\<delta>
            unfolding \<Gamma>_def trail_false_lit_def trail_propagate_def trail_defined_lit_def
              trail_true_lit_def trail_interp_Cons'
            by simp
        next
          case (Neg u)
          then show ?thesis
            using L_Pos tr_false_\<Gamma>'_K
            unfolding \<Gamma>_def trail_false_lit_def trail_propagate_def
            unfolding trail_interp_Cons' prod.sel
            by simp
        qed
      next
        case (Neg t)
        then show ?thesis
          using tr_false_\<Gamma>'_K
          unfolding \<Gamma>_def trail_false_lit_def trail_propagate_def
          unfolding trail_interp_Cons' prod.sel
          by simp
      qed
    qed
  qed

  moreover have "N \<TTurnstile>\<G>e {(D + C) \<cdot> \<mu> \<cdot> \<rho>}"
  proof -
    from ex_renamed_in_N_U obtain CC' \<rho>\<^sub>C\<^sub>C where
      CC'_in: "CC' \<in> N \<union> U" and ren_\<rho>\<^sub>C\<^sub>C: "is_renaming \<rho>\<^sub>C\<^sub>C" and CC'_conv: "C + {#L#} = CC' \<cdot> \<rho>\<^sub>C\<^sub>C"
      by auto

    have "N \<TTurnstile>\<G>e {CC'}"
      using CC'_in
      by (metis (no_types, opaque_lifting) N_entails_U UnE emptyE grounding_of_clss_mono
          insert_subset subset_eq true_clss_mono)
    hence "N \<TTurnstile>\<G>e {CC' \<cdot> \<rho>\<^sub>C\<^sub>C}"
      using ren_\<rho>\<^sub>C\<^sub>C by (metis valid_grounding_of_renaming grounding_of_clss_singleton)
    hence "N \<TTurnstile>\<G>e {C + {#L#}}"
      using CC'_conv by simp
    hence *: "N \<TTurnstile>\<G>e {(C + {#L#}) \<cdot> \<mu>}"
      using grounding_of_subst_cls_subset
      by (metis (no_types, lifting) grounding_of_clss_singleton true_clss_mono)

    have **: "N \<TTurnstile>\<G>e {(D + {#L'#}) \<cdot> \<mu>}"
      using N_entails_D_L' grounding_of_subst_cls_subset
      by (metis (no_types, lifting) grounding_of_clss_singleton true_clss_mono)

    have "N \<TTurnstile>\<G>e {(D + C) \<cdot> \<mu>}"
      unfolding true_clss_def
    proof (intro allI impI ballI)
      fix I E
      assume I_entails: "\<forall>E \<in> grounding_of_clss N. I \<TTurnstile> E" and
        E_in: "E \<in> grounding_of_clss {(D + C) \<cdot> \<mu>}"

      from E_in have E_in': "E \<in> grounding_of_cls ((D + C) \<cdot> \<mu>)"
        unfolding grounding_of_clss_def by simp
      then obtain \<gamma> where E_def: "E = (D + C) \<cdot> \<mu> \<cdot> \<gamma>" and gr_\<gamma>: "is_ground_subst \<gamma>"
        unfolding grounding_of_cls_def by auto

      have "(D + {#L'#}) \<cdot> \<mu> \<cdot> \<gamma> \<in> grounding_of_clss {(D + {#L'#}) \<cdot> \<mu>}"
        using gr_\<gamma> unfolding grounding_of_clss_def grounding_of_cls_def by auto
      hence AA: "\<exists>K \<in># (D + {#L'#}) \<cdot> \<mu> \<cdot> \<gamma>. I \<TTurnstile>l K"
        using **[rule_format, unfolded true_clss_def, OF I_entails]
        by (metis true_cls_def)

      have "(C + {#L#}) \<cdot> \<mu> \<cdot> \<gamma> \<in> grounding_of_clss {(C + {#L#}) \<cdot> \<mu>}"
        using gr_\<gamma> unfolding grounding_of_clss_def grounding_of_cls_def by auto
      hence BB: "\<exists>K \<in># (C + {#L#}) \<cdot> \<mu> \<cdot> \<gamma>. I \<TTurnstile>l K"
        using *[rule_format, unfolded true_clss_def, OF I_entails]
        by (metis true_cls_def)

      show "I \<TTurnstile> E"
        unfolding E_def true_cls_def
        using AA[unfolded subst_cls_union Multiset_Bex_plus_iff]
        using BB[unfolded subst_cls_union Multiset_Bex_plus_iff]
        unfolding subst_cls_union Multiset_Bex_plus_iff
      proof (elim disjE)
        assume "\<exists>K \<in># {#L'#} \<cdot> \<mu> \<cdot> \<gamma>. I \<TTurnstile>l K" and "\<exists>K \<in># {#L#} \<cdot> \<mu> \<cdot> \<gamma>. I \<TTurnstile>l K"
        hence False
          using L_eq_comp_L'
          using subst_term_eq_if_mgu[OF mgu_L_\<rho>_L']
          by (cases L; cases L'; simp add: uminus_literal_def subst_lit_def)
        thus "(\<exists>K \<in># D \<cdot> \<mu> \<cdot> \<gamma>. I \<TTurnstile>l K) \<or> (\<exists>K \<in># C \<cdot> \<mu> \<cdot> \<gamma>. I \<TTurnstile>l K)"
          by simp
      qed simp_all
    qed
    thus ?thesis
      by (metis (no_types, lifting) grounding_of_clss_singleton grounding_of_subst_cls_subset
          true_clss_mono)
  qed

  ultimately show ?case
    unfolding sound_state_def
    using fin disj_N_U ball_\<Gamma>_ground sound_\<Gamma> N_entails_U
    by simp
next
  case (backtrack \<Gamma> L \<sigma> k D i U)
  from backtrack.prems have
    fin: "finite N" "finite U" and
    disj_N_U: "disjoint_vars_set (N \<union> U \<union> clss_of_trail \<Gamma>)" and
    disj_N_U_\<Gamma>_D_L_L': "\<forall>C \<in> N \<union> U \<union> clss_of_trail \<Gamma>. disjoint_vars (D + {#L#}) C" and
    ball_\<Gamma>_ground:"\<forall>L \<in> set \<Gamma>. is_ground_lit (fst L)" and
    sound_\<Gamma>: "sound_trail N U \<Gamma>" and
    N_entails_U: "N \<TTurnstile>\<G>e U" and
    gr_D_L_\<sigma>: "is_ground_cls ((D + {#L#}) \<cdot> \<sigma>)" and
    tr_false_cls: "trail_false_cls \<Gamma> ((D + {#L#}) \<cdot> \<sigma>)" and
    N_entails_D_L_L': "N \<TTurnstile>\<G>e {D + {#L#}}"
    unfolding sound_state_def by simp_all

  have "disjoint_vars_set (N \<union> U \<union> clss_of_trail (trail_backtrack \<Gamma> i) \<union> {D + {#L#}})"
    unfolding disjoint_vars_set_def
  proof (intro ballI impI)
    fix C E
    assume
      C_in: "C \<in> N \<union> U \<union> clss_of_trail (trail_backtrack \<Gamma> i) \<union> {D + {#L#}}" and
      E_in: "E \<in> N \<union> U \<union> clss_of_trail (trail_backtrack \<Gamma> i) \<union> {D + {#L#}}" and
      C_neq_E: "C \<noteq> E"
    from C_in have C_in': "C \<in> N \<union> U \<union> clss_of_trail \<Gamma> \<or> C = D + {#L#}"
      using clss_of_trail_trail_decide_subset by blast
    from E_in have E_in': "E \<in> N \<union> U \<union> clss_of_trail \<Gamma> \<or> E = D + {#L#}"
      using clss_of_trail_trail_decide_subset by blast
    
    from C_in' E_in' C_neq_E show "disjoint_vars C E"
      using disj_N_U[unfolded disjoint_vars_set_def, rule_format]
      using disj_N_U_\<Gamma>_D_L_L' disjoint_vars_sym by blast
  qed

  moreover have "\<forall>L \<in> set (trail_backtrack \<Gamma> i). is_ground_lit (fst L)"
    by (rule ball_set_trail_backtrackI[OF ball_\<Gamma>_ground])

  moreover have "sound_trail N (insert (add_mset L D) U) (trail_backtrack \<Gamma> i)"
    using backtrack
    by (auto simp: sound_state_def intro: sound_trail_backtrackI sound_trail_supersetI)

  moreover have "N \<TTurnstile>\<G>e (U \<union> {D + {#L#}})"
    using N_entails_U N_entails_D_L_L' by (metis UN_Un grounding_of_clss_def true_clss_union)

  ultimately show ?case
    unfolding sound_state_def
    using fin by simp
qed

end

end